Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_LE_1_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_CLAUSES_spec.
Require Import INT_POS_spec.
Require Import LEFT_OR_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1005477_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367770_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
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
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
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
Require Import thm19158_spec.
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
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm2318495_spec.
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
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3888988_spec.
Require Import thm3892933_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem4108828 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) (h1 : (@HAS_SIZE _100044 s n) = (term0 _100044 s n)) : (@HAS_SIZE _100044 s n) = (term0 _100044 s n).
Proof. exact (h1). Qed.
Lemma lem4108829 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) (h1 : (@HAS_SIZE _100044 s n) = (term0 _100044 s n)) : (term0 _100044 s n) = (@HAS_SIZE _100044 s n).
Proof. exact (SYM (@lem4108828 _100044 s n h1)). Qed.
Lemma lem4108830 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) (h1 : (term0 _100044 s n) = (@HAS_SIZE _100044 s n)) : (term0 _100044 s n) = (@HAS_SIZE _100044 s n).
Proof. exact (h1). Qed.
Lemma lem4108831 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) (h1 : (term0 _100044 s n) = (@HAS_SIZE _100044 s n)) : (@HAS_SIZE _100044 s n) = (term0 _100044 s n).
Proof. exact (SYM (@lem4108830 _100044 s n h1)). Qed.
Lemma lem4108832 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term0 _100044 s n)) = ((term0 _100044 s n) = (@HAS_SIZE _100044 s n)).
Proof. exact (prop_ext (fun h1 : (@HAS_SIZE _100044 s n) = (term0 _100044 s n) => @lem4108829 _100044 s n h1) (fun h1 : (term0 _100044 s n) = (@HAS_SIZE _100044 s n) => @lem4108831 _100044 s n h1)). Qed.
Lemma lem4108833 {_100044 : Type'} (s : _100044 -> Prop) : (term1 _100044 s) = (term2 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem4108832 _100044 s n)). Qed.
Lemma lem4108834 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4108835 {_100044 : Type'} (s : _100044 -> Prop) : (term3 _100044 s) = (term4 _100044 s).
Proof. exact (MK_COMB (@lem4108834) (@lem4108833 _100044 s)). Qed.
Lemma lem4108836 {_100044 : Type'} : (term5 _100044) = (term6 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem4108835 _100044 s)). Qed.
Lemma lem4108837 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem4108838 {_100044 : Type'} : (term7 _100044) = (term8 _100044).
Proof. exact (MK_COMB (@lem4108837 _100044) (@lem4108836 _100044)). Qed.
Lemma lem4108839 {_100044 : Type'} : term8 _100044.
Proof. exact (EQ_MP (@lem4108838 _100044) (@lem3863773 _100044)). Qed.
Lemma lem4108840 {_100044 : Type'} (s : _100044 -> Prop) : term9 _100044 s.
Proof. exact (@lem4108839 _100044 s). Qed.
Lemma lem4108841 {_100044 : Type'} (s : _100044 -> Prop) : (term9 _100044 s) = (term4 _100044 s).
Proof. exact (eq_refl (term9 _100044 s)). Qed.
Lemma lem4108842 {_100044 : Type'} (s : _100044 -> Prop) : term4 _100044 s.
Proof. exact (EQ_MP (@lem4108841 _100044 s) (@lem4108840 _100044 s)). Qed.
Lemma lem4108843 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term10 _100044 s n.
Proof. exact (@lem4108842 _100044 s n). Qed.
Lemma lem4108844 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term10 _100044 s n) = ((term0 _100044 s n) = (@HAS_SIZE _100044 s n)).
Proof. exact (eq_refl (term10 _100044 s n)). Qed.
Lemma lem4108846 (p : Prop) : term11 p.
Proof. exact (@lem1001 p). Qed.
Lemma lem4108847 (p : Prop) : (term11 p) = (term12 p).
Proof. exact (eq_refl (term11 p)). Qed.
Lemma lem4108848 (p : Prop) : term12 p.
Proof. exact (EQ_MP (@lem4108847 p) (@lem4108846 p)). Qed.
Lemma lem4108849 (p : Prop) (q : Prop) : term13 p q.
Proof. exact (@lem4108848 p q). Qed.
Lemma lem4108850 (q : Prop) (p : Prop) : (term13 p q) = (term14 q p).
Proof. exact (eq_refl (term13 p q)). Qed.
Lemma lem4108851 (q : Prop) (p : Prop) : term14 q p.
Proof. exact (EQ_MP (@lem4108850 q p) (@lem4108849 p q)). Qed.
Lemma lem4108852 (q : Prop) (p : Prop) (r : Prop) : term15 q p r.
Proof. exact (@lem4108851 q p r). Qed.
Lemma lem4108853 (q : Prop) (p : Prop) (r : Prop) : (term15 q p r) = ((term16 p q r) = (term17 q p r)).
Proof. exact (eq_refl (term15 q p r)). Qed.
Lemma lem4108884 (c : nat) : (term18 c) = (term19 c).
Proof. exact (@lem17160 (c = (NUMERAL 0)) (c = term20)). Qed.
Lemma lem4108889 (c : nat) : (term21 c) = (term21 c).
Proof. exact (eq_refl (term21 c)). Qed.
Lemma lem4108890 (c : nat) : (term22 c) = (term23 c).
Proof. exact (MK_COMB (@lem4108889 c) (@lem4108884 c)). Qed.
Lemma lem4108895 (c : nat) : (term24 c) = (term24 c).
Proof. exact (eq_refl (term24 c)). Qed.
Lemma lem4108896 (c : nat) : (term25 c) = (term26 c).
Proof. exact (MK_COMB (@lem4108895 c) (@lem4108890 c)). Qed.
Lemma lem4108897 (c : nat) : ((term27 c) = (term28 c)) = (term25 c).
Proof. exact (@lem17500 (term27 c) (term28 c)). Qed.
Lemma lem4108979 (c : nat) : ((term27 c) = (term28 c)) = (term26 c).
Proof. exact (TRANS (@lem4108897 c) (@lem4108896 c)). Qed.
Lemma lem4108981 (m : nat) (n : nat) : (Peano.le m n) = (term29 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4108982 (c : nat) : (term27 c) = (term30 c).
Proof. exact (@lem4108981 c term20). Qed.
Lemma lem4108983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4108984 (c : nat) : (term31 c) = (term32 c).
Proof. exact (MK_COMB (@lem4108983) (@lem4108982 c)). Qed.
Lemma lem4108986 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem4108987 (c : nat) : (c = (NUMERAL 0)) = ((int_of_num c) = term33).
Proof. exact (@lem4108986 c (NUMERAL 0)). Qed.
Lemma lem4108990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4108991 (c : nat) : (term34 c) = (term35 c).
Proof. exact (MK_COMB (@lem4108990) (@lem4108987 c)). Qed.
Lemma lem4108993 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem4108994 (c : nat) : (c = term20) = ((int_of_num c) = term36).
Proof. exact (@lem4108993 c term20). Qed.
Lemma lem4108997 (c : nat) : (term28 c) = (term37 c).
Proof. exact (MK_COMB (@lem4108991 c) (@lem4108994 c)). Qed.
Lemma lem4108998 (c : nat) : (term38 c) = (term39 c).
Proof. exact (MK_COMB (@lem4108984 c) (@lem4108997 c)). Qed.
Lemma lem4108999 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4109000 (c : nat) : (term24 c) = (term40 c).
Proof. exact (MK_COMB (@lem4108999) (@lem4108998 c)). Qed.
Lemma lem4109002 (m : nat) (n : nat) : (Peano.le m n) = (term29 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4109003 (c : nat) : (term27 c) = (term30 c).
Proof. exact (@lem4109002 c term20). Qed.
Lemma lem4109004 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4109005 (c : nat) : (term41 c) = (term42 c).
Proof. exact (MK_COMB (@lem4109004) (@lem4109003 c)). Qed.
Lemma lem4109006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4109007 (c : nat) : (term21 c) = (term43 c).
Proof. exact (MK_COMB (@lem4109006) (@lem4109005 c)). Qed.
Lemma lem4109009 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem4109010 (c : nat) : (c = (NUMERAL 0)) = ((int_of_num c) = term33).
Proof. exact (@lem4109009 c (NUMERAL 0)). Qed.
Lemma lem4109013 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4109014 (c : nat) : (term44 c) = (term45 c).
Proof. exact (MK_COMB (@lem4109013) (@lem4109010 c)). Qed.
Lemma lem4109015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4109016 (c : nat) : (term46 c) = (term47 c).
Proof. exact (MK_COMB (@lem4109015) (@lem4109014 c)). Qed.
Lemma lem4109018 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem4109019 (c : nat) : (c = term20) = ((int_of_num c) = term36).
Proof. exact (@lem4109018 c term20). Qed.
Lemma lem4109022 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4109023 (c : nat) : (term48 c) = (term49 c).
Proof. exact (MK_COMB (@lem4109022) (@lem4109019 c)). Qed.
Lemma lem4109024 (c : nat) : (term19 c) = (term50 c).
Proof. exact (MK_COMB (@lem4109016 c) (@lem4109023 c)). Qed.
Lemma lem4109025 (c : nat) : (term23 c) = (term51 c).
Proof. exact (MK_COMB (@lem4109007 c) (@lem4109024 c)). Qed.
Lemma lem4109026 (c : nat) : (term26 c) = (term52 c).
Proof. exact (MK_COMB (@lem4109000 c) (@lem4109025 c)). Qed.
Lemma lem4109027 (c : nat) : ((term27 c) = (term28 c)) = (term52 c).
Proof. exact (TRANS (@lem4108979 c) (@lem4109026 c)). Qed.
Lemma lem4109028 (c : nat) : term53 c.
Proof. exact (@lem2307535 c). Qed.
Lemma lem4109029 (c : nat) : (term53 c) = (term54 c).
Proof. exact (eq_refl (term53 c)). Qed.
Lemma lem4109030 (c : nat) : term54 c.
Proof. exact (EQ_MP (@lem4109029 c) (@lem4109028 c)). Qed.
Lemma lem4109031 (_48296 : int) : (term55 _48296) = (term56 _48296).
Proof. exact (@lem2318604 (term56 _48296)). Qed.
Lemma lem4109057 (_48296 : int) : (term57 _48296) = (term58 _48296).
Proof. exact (@lem17160 (_48296 = term33) (_48296 = term36)). Qed.
Lemma lem4109059 (_48296 : int) : (term59 _48296) = (term59 _48296).
Proof. exact (eq_refl (term59 _48296)). Qed.
Lemma lem4109060 (_48296 : int) : (term60 _48296) = (term61 _48296).
Proof. exact (MK_COMB (@lem4109059 _48296) (@lem4109057 _48296)). Qed.
Lemma lem4109061 (_48296 : int) : (term62 _48296) = (term60 _48296).
Proof. exact (@lem17045 (term63 _48296) (term64 _48296)). Qed.
Lemma lem4109062 (_48296 : int) : (term62 _48296) = (term61 _48296).
Proof. exact (TRANS (@lem4109061 _48296) (@lem4109060 _48296)). Qed.
Lemma lem4109065 (_48296 : int) : (term65 _48296) = (term63 _48296).
Proof. exact (@lem16933 (term63 _48296)). Qed.
Lemma lem4109068 (_48296 : int) : (term66 _48296) = (_48296 = term33).
Proof. exact (@lem16933 (_48296 = term33)). Qed.
Lemma lem4109071 (_48296 : int) : (term67 _48296) = (_48296 = term36).
Proof. exact (@lem16933 (_48296 = term36)). Qed.
Lemma lem4109072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4109073 (_48296 : int) : (term68 _48296) = (term69 _48296).
Proof. exact (MK_COMB (@lem4109072) (@lem4109068 _48296)). Qed.
Lemma lem4109074 (_48296 : int) : (term70 _48296) = (term64 _48296).
Proof. exact (MK_COMB (@lem4109073 _48296) (@lem4109071 _48296)). Qed.
Lemma lem4109075 (_48296 : int) : (term71 _48296) = (term70 _48296).
Proof. exact (@lem17045 (term72 _48296) (term73 _48296)). Qed.
Lemma lem4109076 (_48296 : int) : (term71 _48296) = (term64 _48296).
Proof. exact (TRANS (@lem4109075 _48296) (@lem4109074 _48296)). Qed.
Lemma lem4109077 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4109078 (_48296 : int) : (term74 _48296) = (term75 _48296).
Proof. exact (MK_COMB (@lem4109077) (@lem4109065 _48296)). Qed.
Lemma lem4109079 (_48296 : int) : (term76 _48296) = (term77 _48296).
Proof. exact (MK_COMB (@lem4109078 _48296) (@lem4109076 _48296)). Qed.
Lemma lem4109080 (_48296 : int) : (term78 _48296) = (term76 _48296).
Proof. exact (@lem17045 (term79 _48296) (term58 _48296)). Qed.
Lemma lem4109081 (_48296 : int) : (term78 _48296) = (term77 _48296).
Proof. exact (TRANS (@lem4109080 _48296) (@lem4109079 _48296)). Qed.
Lemma lem4109082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4109083 (_48296 : int) : (term80 _48296) = (term81 _48296).
Proof. exact (MK_COMB (@lem4109082) (@lem4109062 _48296)). Qed.
Lemma lem4109084 (_48296 : int) : (term82 _48296) = (term83 _48296).
Proof. exact (MK_COMB (@lem4109083 _48296) (@lem4109081 _48296)). Qed.
Lemma lem4109085 (_48296 : int) : (term84 _48296) = (term82 _48296).
Proof. exact (@lem17160 (term85 _48296) (term86 _48296)). Qed.
Lemma lem4109086 (_48296 : int) : (term84 _48296) = (term83 _48296).
Proof. exact (TRANS (@lem4109085 _48296) (@lem4109084 _48296)). Qed.
Lemma lem4109088 (_48296 : int) : (term87 _48296) = (term87 _48296).
Proof. exact (eq_refl (term87 _48296)). Qed.
Lemma lem4109089 (_48296 : int) : (term88 _48296) = (term89 _48296).
Proof. exact (MK_COMB (@lem4109088 _48296) (@lem4109086 _48296)). Qed.
Lemma lem4109090 (_48296 : int) : (term90 _48296) = (term88 _48296).
Proof. exact (@lem17362 (term91 _48296) (term92 _48296)). Qed.
Lemma lem4109124 (_48296 : int) : (term90 _48296) = (term89 _48296).
Proof. exact (TRANS (@lem4109090 _48296) (@lem4109089 _48296)). Qed.
Lemma lem4109127 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4109128 (_48296 : int) : (term91 _48296) = (term94 _48296).
Proof. exact (@lem4109127 term33 _48296). Qed.
Lemma lem4109130 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109131 : term96 = term97.
Proof. exact (@lem4109130 (NUMERAL 0)). Qed.
Lemma lem4109132 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4109133 : term98 = term99.
Proof. exact (MK_COMB (@lem4109132) (@lem4109131)). Qed.
Lemma lem4109134 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4109135 (_48296 : int) : (term94 _48296) = (term100 _48296).
Proof. exact (MK_COMB (@lem4109133) (@lem4109134 _48296)). Qed.
Lemma lem4109137 (_48296 : int) : (term91 _48296) = (term100 _48296).
Proof. exact (TRANS (@lem4109128 _48296) (@lem4109135 _48296)). Qed.
Lemma lem4109139 (y : int) (x : int) : (term101 x y) = (term102 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem4109140 (_48296 : int) : (term79 _48296) = (term103 _48296).
Proof. exact (@lem4109139 term36 _48296). Qed.
Lemma lem4109142 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4109143 (_48296 : int) : (term103 _48296) = (term104 _48296).
Proof. exact (@lem4109142 term105 _48296). Qed.
Lemma lem4109145 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4109146 : term108 = term109.
Proof. exact (@lem4109145 term36 term36). Qed.
Lemma lem4109148 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109149 : term110 = term111.
Proof. exact (@lem4109148 term20). Qed.
Lemma lem4109150 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4109151 : term112 = term113.
Proof. exact (MK_COMB (@lem4109150) (@lem4109149)). Qed.
Lemma lem4109153 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109154 : term110 = term111.
Proof. exact (@lem4109153 term20). Qed.
Lemma lem4109155 : term109 = term114.
Proof. exact (MK_COMB (@lem4109151) (@lem4109154)). Qed.
Lemma lem4109156 : term108 = term114.
Proof. exact (TRANS (@lem4109146) (@lem4109155)). Qed.
Lemma lem4109157 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4109158 : term115 = term116.
Proof. exact (MK_COMB (@lem4109157) (@lem4109156)). Qed.
Lemma lem4109159 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4109160 (_48296 : int) : (term104 _48296) = (term117 _48296).
Proof. exact (MK_COMB (@lem4109158) (@lem4109159 _48296)). Qed.
Lemma lem4109161 (_48296 : int) : (term103 _48296) = (term117 _48296).
Proof. exact (TRANS (@lem4109143 _48296) (@lem4109160 _48296)). Qed.
Lemma lem4109162 (_48296 : int) : (term79 _48296) = (term117 _48296).
Proof. exact (TRANS (@lem4109140 _48296) (@lem4109161 _48296)). Qed.
Lemma lem4109164 (y : int) (x : int) : (term118 x y) = (term119 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem4109165 (_48296 : int) : (term72 _48296) = (term120 _48296).
Proof. exact (@lem4109164 term33 _48296). Qed.
Lemma lem4109167 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4109168 (_48296 : int) : (term121 _48296) = (term122 _48296).
Proof. exact (@lem4109167 (term123 _48296) term33). Qed.
Lemma lem4109170 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4109171 (_48296 : int) : (term124 _48296) = (term125 _48296).
Proof. exact (@lem4109170 _48296 term36). Qed.
Lemma lem4109173 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109174 : term110 = term111.
Proof. exact (@lem4109173 term20). Qed.
Lemma lem4109175 (_48296 : int) : (term126 _48296) = (term126 _48296).
Proof. exact (eq_refl (term126 _48296)). Qed.
Lemma lem4109176 (_48296 : int) : (term125 _48296) = (term127 _48296).
Proof. exact (MK_COMB (@lem4109175 _48296) (@lem4109174)). Qed.
Lemma lem4109177 (_48296 : int) : (term124 _48296) = (term127 _48296).
Proof. exact (TRANS (@lem4109171 _48296) (@lem4109176 _48296)). Qed.
Lemma lem4109178 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4109179 (_48296 : int) : (term128 _48296) = (term129 _48296).
Proof. exact (MK_COMB (@lem4109178) (@lem4109177 _48296)). Qed.
Lemma lem4109181 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109182 : term96 = term97.
Proof. exact (@lem4109181 (NUMERAL 0)). Qed.
Lemma lem4109183 (_48296 : int) : (term122 _48296) = (term130 _48296).
Proof. exact (MK_COMB (@lem4109179 _48296) (@lem4109182)). Qed.
Lemma lem4109184 (_48296 : int) : (term121 _48296) = (term130 _48296).
Proof. exact (TRANS (@lem4109168 _48296) (@lem4109183 _48296)). Qed.
Lemma lem4109185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4109186 (_48296 : int) : (term131 _48296) = (term132 _48296).
Proof. exact (MK_COMB (@lem4109185) (@lem4109184 _48296)). Qed.
Lemma lem4109188 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4109189 (_48296 : int) : (term133 _48296) = (term134 _48296).
Proof. exact (@lem4109188 term135 _48296). Qed.
Lemma lem4109191 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4109192 : term136 = term137.
Proof. exact (@lem4109191 term33 term36). Qed.
Lemma lem4109194 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109195 : term96 = term97.
Proof. exact (@lem4109194 (NUMERAL 0)). Qed.
Lemma lem4109196 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4109197 : term138 = term139.
Proof. exact (MK_COMB (@lem4109196) (@lem4109195)). Qed.
Lemma lem4109199 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109200 : term110 = term111.
Proof. exact (@lem4109199 term20). Qed.
Lemma lem4109201 : term137 = term140.
Proof. exact (MK_COMB (@lem4109197) (@lem4109200)). Qed.
Lemma lem4109202 : term136 = term140.
Proof. exact (TRANS (@lem4109192) (@lem4109201)). Qed.
Lemma lem4109203 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4109204 : term141 = term142.
Proof. exact (MK_COMB (@lem4109203) (@lem4109202)). Qed.
Lemma lem4109205 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4109206 (_48296 : int) : (term134 _48296) = (term143 _48296).
Proof. exact (MK_COMB (@lem4109204) (@lem4109205 _48296)). Qed.
Lemma lem4109207 (_48296 : int) : (term133 _48296) = (term143 _48296).
Proof. exact (TRANS (@lem4109189 _48296) (@lem4109206 _48296)). Qed.
Lemma lem4109208 (_48296 : int) : (term120 _48296) = (term144 _48296).
Proof. exact (MK_COMB (@lem4109186 _48296) (@lem4109207 _48296)). Qed.
Lemma lem4109209 (_48296 : int) : (term72 _48296) = (term144 _48296).
Proof. exact (TRANS (@lem4109165 _48296) (@lem4109208 _48296)). Qed.
Lemma lem4109211 (y : int) (x : int) : (term118 x y) = (term119 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem4109212 (_48296 : int) : (term73 _48296) = (term145 _48296).
Proof. exact (@lem4109211 term36 _48296). Qed.
Lemma lem4109214 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4109215 (_48296 : int) : (term146 _48296) = (term147 _48296).
Proof. exact (@lem4109214 (term123 _48296) term36). Qed.
Lemma lem4109217 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4109218 (_48296 : int) : (term124 _48296) = (term125 _48296).
Proof. exact (@lem4109217 _48296 term36). Qed.
Lemma lem4109220 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109221 : term110 = term111.
Proof. exact (@lem4109220 term20). Qed.
Lemma lem4109222 (_48296 : int) : (term126 _48296) = (term126 _48296).
Proof. exact (eq_refl (term126 _48296)). Qed.
Lemma lem4109223 (_48296 : int) : (term125 _48296) = (term127 _48296).
Proof. exact (MK_COMB (@lem4109222 _48296) (@lem4109221)). Qed.
Lemma lem4109224 (_48296 : int) : (term124 _48296) = (term127 _48296).
Proof. exact (TRANS (@lem4109218 _48296) (@lem4109223 _48296)). Qed.
Lemma lem4109225 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4109226 (_48296 : int) : (term128 _48296) = (term129 _48296).
Proof. exact (MK_COMB (@lem4109225) (@lem4109224 _48296)). Qed.
Lemma lem4109228 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109229 : term110 = term111.
Proof. exact (@lem4109228 term20). Qed.
Lemma lem4109230 (_48296 : int) : (term147 _48296) = (term148 _48296).
Proof. exact (MK_COMB (@lem4109226 _48296) (@lem4109229)). Qed.
Lemma lem4109231 (_48296 : int) : (term146 _48296) = (term148 _48296).
Proof. exact (TRANS (@lem4109215 _48296) (@lem4109230 _48296)). Qed.
Lemma lem4109232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4109233 (_48296 : int) : (term149 _48296) = (term150 _48296).
Proof. exact (MK_COMB (@lem4109232) (@lem4109231 _48296)). Qed.
Lemma lem4109235 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4109236 (_48296 : int) : (term103 _48296) = (term104 _48296).
Proof. exact (@lem4109235 term105 _48296). Qed.
Lemma lem4109238 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4109239 : term108 = term109.
Proof. exact (@lem4109238 term36 term36). Qed.
Lemma lem4109241 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109242 : term110 = term111.
Proof. exact (@lem4109241 term20). Qed.
Lemma lem4109243 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4109244 : term112 = term113.
Proof. exact (MK_COMB (@lem4109243) (@lem4109242)). Qed.
Lemma lem4109246 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109247 : term110 = term111.
Proof. exact (@lem4109246 term20). Qed.
Lemma lem4109248 : term109 = term114.
Proof. exact (MK_COMB (@lem4109244) (@lem4109247)). Qed.
Lemma lem4109249 : term108 = term114.
Proof. exact (TRANS (@lem4109239) (@lem4109248)). Qed.
Lemma lem4109250 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4109251 : term115 = term116.
Proof. exact (MK_COMB (@lem4109250) (@lem4109249)). Qed.
Lemma lem4109252 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4109253 (_48296 : int) : (term104 _48296) = (term117 _48296).
Proof. exact (MK_COMB (@lem4109251) (@lem4109252 _48296)). Qed.
Lemma lem4109254 (_48296 : int) : (term103 _48296) = (term117 _48296).
Proof. exact (TRANS (@lem4109236 _48296) (@lem4109253 _48296)). Qed.
Lemma lem4109255 (_48296 : int) : (term145 _48296) = (term151 _48296).
Proof. exact (MK_COMB (@lem4109233 _48296) (@lem4109254 _48296)). Qed.
Lemma lem4109256 (_48296 : int) : (term73 _48296) = (term151 _48296).
Proof. exact (TRANS (@lem4109212 _48296) (@lem4109255 _48296)). Qed.
Lemma lem4109257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4109258 (_48296 : int) : (term152 _48296) = (term153 _48296).
Proof. exact (MK_COMB (@lem4109257) (@lem4109209 _48296)). Qed.
Lemma lem4109259 (_48296 : int) : (term58 _48296) = (term154 _48296).
Proof. exact (MK_COMB (@lem4109258 _48296) (@lem4109256 _48296)). Qed.
Lemma lem4109260 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4109261 (_48296 : int) : (term59 _48296) = (term155 _48296).
Proof. exact (MK_COMB (@lem4109260) (@lem4109162 _48296)). Qed.
Lemma lem4109262 (_48296 : int) : (term61 _48296) = (term156 _48296).
Proof. exact (MK_COMB (@lem4109261 _48296) (@lem4109259 _48296)). Qed.
Lemma lem4109265 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4109266 (_48296 : int) : (term63 _48296) = (term157 _48296).
Proof. exact (@lem4109265 _48296 term36). Qed.
Lemma lem4109268 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109269 : term110 = term111.
Proof. exact (@lem4109268 term20). Qed.
Lemma lem4109270 (_48296 : int) : (term158 _48296) = (term158 _48296).
Proof. exact (eq_refl (term158 _48296)). Qed.
Lemma lem4109271 (_48296 : int) : (term157 _48296) = (term159 _48296).
Proof. exact (MK_COMB (@lem4109270 _48296) (@lem4109269)). Qed.
Lemma lem4109273 (_48296 : int) : (term63 _48296) = (term159 _48296).
Proof. exact (TRANS (@lem4109266 _48296) (@lem4109271 _48296)). Qed.
Lemma lem4109276 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem4109277 (_48296 : int) : (_48296 = term33) = ((real_of_int _48296) = term96).
Proof. exact (@lem4109276 _48296 term33). Qed.
Lemma lem4109281 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109282 : term96 = term97.
Proof. exact (@lem4109281 (NUMERAL 0)). Qed.
Lemma lem4109283 (_48296 : int) : (term160 _48296) = (term160 _48296).
Proof. exact (eq_refl (term160 _48296)). Qed.
Lemma lem4109284 (_48296 : int) : ((real_of_int _48296) = term96) = ((real_of_int _48296) = term97).
Proof. exact (MK_COMB (@lem4109283 _48296) (@lem4109282)). Qed.
Lemma lem4109286 (_48296 : int) : (_48296 = term33) = ((real_of_int _48296) = term97).
Proof. exact (TRANS (@lem4109277 _48296) (@lem4109284 _48296)). Qed.
Lemma lem4109289 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem4109290 (_48296 : int) : (_48296 = term36) = ((real_of_int _48296) = term110).
Proof. exact (@lem4109289 _48296 term36). Qed.
Lemma lem4109294 (n : nat) : (term95 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4109295 : term110 = term111.
Proof. exact (@lem4109294 term20). Qed.
Lemma lem4109296 (_48296 : int) : (term160 _48296) = (term160 _48296).
Proof. exact (eq_refl (term160 _48296)). Qed.
Lemma lem4109297 (_48296 : int) : ((real_of_int _48296) = term110) = ((real_of_int _48296) = term111).
Proof. exact (MK_COMB (@lem4109296 _48296) (@lem4109295)). Qed.
Lemma lem4109299 (_48296 : int) : (_48296 = term36) = ((real_of_int _48296) = term111).
Proof. exact (TRANS (@lem4109290 _48296) (@lem4109297 _48296)). Qed.
Lemma lem4109300 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4109301 (_48296 : int) : (term69 _48296) = (term161 _48296).
Proof. exact (MK_COMB (@lem4109300) (@lem4109286 _48296)). Qed.
Lemma lem4109302 (_48296 : int) : (term64 _48296) = (term162 _48296).
Proof. exact (MK_COMB (@lem4109301 _48296) (@lem4109299 _48296)). Qed.
Lemma lem4109303 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4109304 (_48296 : int) : (term75 _48296) = (term163 _48296).
Proof. exact (MK_COMB (@lem4109303) (@lem4109273 _48296)). Qed.
Lemma lem4109305 (_48296 : int) : (term77 _48296) = (term164 _48296).
Proof. exact (MK_COMB (@lem4109304 _48296) (@lem4109302 _48296)). Qed.
Lemma lem4109306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4109307 (_48296 : int) : (term81 _48296) = (term165 _48296).
Proof. exact (MK_COMB (@lem4109306) (@lem4109262 _48296)). Qed.
Lemma lem4109308 (_48296 : int) : (term83 _48296) = (term166 _48296).
Proof. exact (MK_COMB (@lem4109307 _48296) (@lem4109305 _48296)). Qed.
Lemma lem4109309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4109310 (_48296 : int) : (term87 _48296) = (term167 _48296).
Proof. exact (MK_COMB (@lem4109309) (@lem4109137 _48296)). Qed.
Lemma lem4109311 (_48296 : int) : (term89 _48296) = (term168 _48296).
Proof. exact (MK_COMB (@lem4109310 _48296) (@lem4109308 _48296)). Qed.
Lemma lem4109312 (_48296 : int) : (term90 _48296) = (term168 _48296).
Proof. exact (TRANS (@lem4109124 _48296) (@lem4109311 _48296)). Qed.
Lemma lem4109316 (t : Prop) : (term169 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4109402 (_48296 : int) : (term170 _48296) = (term168 _48296).
Proof. exact (@lem4109316 (term168 _48296)). Qed.
Lemma lem4109403 (_48296 : int) : (term100 _48296) = (term171 _48296).
Proof. exact (@lem1988287 (real_of_int _48296) term97). Qed.
Lemma lem4109409 (_48296 : int) : (term172 _48296) = (term173 _48296).
Proof. exact (@lem1982792 (real_of_int _48296) term97). Qed.
Lemma lem4109411 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4109412 : term97 = term175.
Proof. exact (@lem4109411 (NUMERAL 0)). Qed.
Lemma lem4109414 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4109415 : term178 = term179.
Proof. exact (@lem4109414 term20). Qed.
Lemma lem4109416 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4109417 : term180 = term181.
Proof. exact (MK_COMB (@lem4109416) (@lem4109415)). Qed.
Lemma lem4109418 : term182 = term183.
Proof. exact (MK_COMB (@lem4109417) (@lem4109412)). Qed.
Lemma lem4109419 : term183 = term184.
Proof. exact (@lem1981613 term178 term97 term111 term111). Qed.
Lemma lem4109421 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109422 : term187 = term188.
Proof. exact (@lem4109421 term20 term20). Qed.
Lemma lem4109423 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109424 : term190 = term20.
Proof. exact (EQ_MP (@lem4109423) (@lem940073)). Qed.
Lemma lem4109425 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109426 : term188 = term111.
Proof. exact (MK_COMB (@lem4109425) (@lem4109424)). Qed.
Lemma lem4109427 : term187 = term111.
Proof. exact (TRANS (@lem4109422) (@lem4109426)). Qed.
Lemma lem4109429 (x : nat) : (term191 x) = term97.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem4109430 : term182 = term97.
Proof. exact (@lem4109429 term20). Qed.
Lemma lem4109431 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4109432 : term192 = term193.
Proof. exact (MK_COMB (@lem4109431) (@lem4109430)). Qed.
Lemma lem4109433 : term184 = term175.
Proof. exact (MK_COMB (@lem4109432) (@lem4109427)). Qed.
Lemma lem4109434 : term183 = term175.
Proof. exact (TRANS (@lem4109419) (@lem4109433)). Qed.
Lemma lem4109435 : term182 = term175.
Proof. exact (TRANS (@lem4109418) (@lem4109434)). Qed.
Lemma lem4109437 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4109438 : term175 = term97.
Proof. exact (@lem4109437 term97). Qed.
Lemma lem4109439 : term182 = term97.
Proof. exact (TRANS (@lem4109435) (@lem4109438)). Qed.
Lemma lem4109440 (_48296 : int) : (term126 _48296) = (term126 _48296).
Proof. exact (eq_refl (term126 _48296)). Qed.
Lemma lem4109441 (_48296 : int) : (term173 _48296) = (term195 _48296).
Proof. exact (MK_COMB (@lem4109440 _48296) (@lem4109439)). Qed.
Lemma lem4109442 (_48296 : int) : (term195 _48296) = (real_of_int _48296).
Proof. exact (@lem1982723 (real_of_int _48296)). Qed.
Lemma lem4109443 (_48296 : int) : (term173 _48296) = (real_of_int _48296).
Proof. exact (TRANS (@lem4109441 _48296) (@lem4109442 _48296)). Qed.
Lemma lem4109445 (_48296 : int) : (term172 _48296) = (real_of_int _48296).
Proof. exact (TRANS (@lem4109409 _48296) (@lem4109443 _48296)). Qed.
Lemma lem4109446 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4109447 (_48296 : int) : (term196 _48296) = (term197 _48296).
Proof. exact (MK_COMB (@lem4109446) (@lem4109445 _48296)). Qed.
Lemma lem4109448 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4109449 (_48296 : int) : (term171 _48296) = (term198 _48296).
Proof. exact (MK_COMB (@lem4109447 _48296) (@lem4109448)). Qed.
Lemma lem4109450 (_48296 : int) : (term100 _48296) = (term198 _48296).
Proof. exact (TRANS (@lem4109403 _48296) (@lem4109449 _48296)). Qed.
Lemma lem4109451 (_48296 : int) : (term117 _48296) = (term199 _48296).
Proof. exact (@lem1988287 (real_of_int _48296) term114). Qed.
Lemma lem4109458 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4109459 : term111 = term200.
Proof. exact (@lem4109458 term20). Qed.
Lemma lem4109461 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4109462 : term111 = term200.
Proof. exact (@lem4109461 term20). Qed.
Lemma lem4109463 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4109464 : term113 = term201.
Proof. exact (MK_COMB (@lem4109463) (@lem4109462)). Qed.
Lemma lem4109465 : term114 = term202.
Proof. exact (MK_COMB (@lem4109464) (@lem4109459)). Qed.
Lemma lem4109466 : term203.
Proof. exact (@lem1981473 term111 term111 term111 term111 term204 term111). Qed.
Lemma lem4109468 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4109469 : term206 = term207.
Proof. exact (@lem4109468 (NUMERAL 0) term20). Qed.
Lemma lem4109470 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4109471 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4109472 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4109471 h1) (fun h1 : term207 = True => @lem4109470)). Qed.
Lemma lem4109473 : term207 = True.
Proof. exact (EQ_MP (@lem4109472) (@lem4109470)). Qed.
Lemma lem4109474 : term206 = True.
Proof. exact (TRANS (@lem4109469) (@lem4109473)). Qed.
Lemma lem4109475 : True = term206.
Proof. exact (SYM (@lem4109474)). Qed.
Lemma lem4109476 : term206.
Proof. exact (EQ_MP (@lem4109475) (@lem0)). Qed.
Lemma lem4109477 : term209.
Proof. exact (@lem4109466 (@lem4109476)). Qed.
Lemma lem4109479 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4109480 : term206 = term207.
Proof. exact (@lem4109479 (NUMERAL 0) term20). Qed.
Lemma lem4109481 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4109482 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4109483 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4109482 h1) (fun h1 : term207 = True => @lem4109481)). Qed.
Lemma lem4109484 : term207 = True.
Proof. exact (EQ_MP (@lem4109483) (@lem4109481)). Qed.
Lemma lem4109485 : term206 = True.
Proof. exact (TRANS (@lem4109480) (@lem4109484)). Qed.
Lemma lem4109486 : True = term206.
Proof. exact (SYM (@lem4109485)). Qed.
Lemma lem4109487 : term206.
Proof. exact (EQ_MP (@lem4109486) (@lem0)). Qed.
Lemma lem4109488 : term210.
Proof. exact (@lem4109477 (@lem4109487)). Qed.
Lemma lem4109490 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4109491 : term206 = term207.
Proof. exact (@lem4109490 (NUMERAL 0) term20). Qed.
Lemma lem4109492 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4109493 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4109494 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4109493 h1) (fun h1 : term207 = True => @lem4109492)). Qed.
Lemma lem4109495 : term207 = True.
Proof. exact (EQ_MP (@lem4109494) (@lem4109492)). Qed.
Lemma lem4109496 : term206 = True.
Proof. exact (TRANS (@lem4109491) (@lem4109495)). Qed.
Lemma lem4109497 : True = term206.
Proof. exact (SYM (@lem4109496)). Qed.
Lemma lem4109498 : term206.
Proof. exact (EQ_MP (@lem4109497) (@lem0)). Qed.
Lemma lem4109499 : term211.
Proof. exact (@lem4109488 (@lem4109498)). Qed.
Lemma lem4109501 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109502 : term187 = term188.
Proof. exact (@lem4109501 term20 term20). Qed.
Lemma lem4109503 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109504 : term190 = term20.
Proof. exact (EQ_MP (@lem4109503) (@lem940073)). Qed.
Lemma lem4109505 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109506 : term188 = term111.
Proof. exact (MK_COMB (@lem4109505) (@lem4109504)). Qed.
Lemma lem4109507 : term187 = term111.
Proof. exact (TRANS (@lem4109502) (@lem4109506)). Qed.
Lemma lem4109509 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109510 : term187 = term188.
Proof. exact (@lem4109509 term20 term20). Qed.
Lemma lem4109511 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109512 : term190 = term20.
Proof. exact (EQ_MP (@lem4109511) (@lem940073)). Qed.
Lemma lem4109513 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109514 : term188 = term111.
Proof. exact (MK_COMB (@lem4109513) (@lem4109512)). Qed.
Lemma lem4109515 : term187 = term111.
Proof. exact (TRANS (@lem4109510) (@lem4109514)). Qed.
Lemma lem4109516 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4109517 : term212 = term113.
Proof. exact (MK_COMB (@lem4109516) (@lem4109515)). Qed.
Lemma lem4109518 : term213 = term114.
Proof. exact (MK_COMB (@lem4109517) (@lem4109507)). Qed.
Lemma lem4109519 : term114 = term214.
Proof. exact (@lem1367770 term20 term20). Qed.
Lemma lem4109520 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem4109521 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem4109522 : term217 = term218.
Proof. exact (EQ_MP (@lem4109521) (@lem4109520)). Qed.
Lemma lem4109523 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109524 : term214 = term204.
Proof. exact (MK_COMB (@lem4109523) (@lem4109522)). Qed.
Lemma lem4109525 : term114 = term204.
Proof. exact (TRANS (@lem4109519) (@lem4109524)). Qed.
Lemma lem4109526 : term213 = term204.
Proof. exact (TRANS (@lem4109518) (@lem4109525)). Qed.
Lemma lem4109527 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4109528 : term219 = term220.
Proof. exact (MK_COMB (@lem4109527) (@lem4109526)). Qed.
Lemma lem4109529 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4109530 : term221 = term222.
Proof. exact (MK_COMB (@lem4109528) (@lem4109529)). Qed.
Lemma lem4109532 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109533 : term222 = term223.
Proof. exact (@lem4109532 term218 term20). Qed.
Lemma lem4109534 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4109535 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4109536 : term225 = term218.
Proof. exact (EQ_MP (@lem4109535) (@lem4109534)). Qed.
Lemma lem4109537 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109538 : term223 = term204.
Proof. exact (MK_COMB (@lem4109537) (@lem4109536)). Qed.
Lemma lem4109539 : term222 = term204.
Proof. exact (TRANS (@lem4109533) (@lem4109538)). Qed.
Lemma lem4109540 : term221 = term204.
Proof. exact (TRANS (@lem4109530) (@lem4109539)). Qed.
Lemma lem4109542 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109543 : term187 = term188.
Proof. exact (@lem4109542 term20 term20). Qed.
Lemma lem4109544 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109545 : term190 = term20.
Proof. exact (EQ_MP (@lem4109544) (@lem940073)). Qed.
Lemma lem4109546 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109547 : term188 = term111.
Proof. exact (MK_COMB (@lem4109546) (@lem4109545)). Qed.
Lemma lem4109548 : term187 = term111.
Proof. exact (TRANS (@lem4109543) (@lem4109547)). Qed.
Lemma lem4109549 : term220 = term220.
Proof. exact (eq_refl term220). Qed.
Lemma lem4109550 : term226 = term222.
Proof. exact (MK_COMB (@lem4109549) (@lem4109548)). Qed.
Lemma lem4109552 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109553 : term222 = term223.
Proof. exact (@lem4109552 term218 term20). Qed.
Lemma lem4109554 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4109555 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4109556 : term225 = term218.
Proof. exact (EQ_MP (@lem4109555) (@lem4109554)). Qed.
Lemma lem4109557 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109558 : term223 = term204.
Proof. exact (MK_COMB (@lem4109557) (@lem4109556)). Qed.
Lemma lem4109559 : term222 = term204.
Proof. exact (TRANS (@lem4109553) (@lem4109558)). Qed.
Lemma lem4109560 : term226 = term204.
Proof. exact (TRANS (@lem4109550) (@lem4109559)). Qed.
Lemma lem4109561 : term204 = term226.
Proof. exact (SYM (@lem4109560)). Qed.
Lemma lem4109562 : term221 = term226.
Proof. exact (TRANS (@lem4109540) (@lem4109561)). Qed.
Lemma lem4109563 : term202 = term227.
Proof. exact (@lem4109499 (@lem4109562)). Qed.
Lemma lem4109564 : term114 = term227.
Proof. exact (TRANS (@lem4109465) (@lem4109563)). Qed.
Lemma lem4109566 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4109567 : term227 = term204.
Proof. exact (@lem4109566 term204). Qed.
Lemma lem4109569 : term114 = term204.
Proof. exact (TRANS (@lem4109564) (@lem4109567)). Qed.
Lemma lem4109572 (_48296 : int) : (term228 _48296) = (term228 _48296).
Proof. exact (eq_refl (term228 _48296)). Qed.
Lemma lem4109573 (_48296 : int) : (term229 _48296) = (term230 _48296).
Proof. exact (MK_COMB (@lem4109572 _48296) (@lem4109569)). Qed.
Lemma lem4109574 (_48296 : int) : (term230 _48296) = (term231 _48296).
Proof. exact (@lem1982792 (real_of_int _48296) term204). Qed.
Lemma lem4109576 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4109577 : term204 = term227.
Proof. exact (@lem4109576 term218). Qed.
Lemma lem4109579 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4109580 : term178 = term179.
Proof. exact (@lem4109579 term20). Qed.
Lemma lem4109581 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4109582 : term180 = term181.
Proof. exact (MK_COMB (@lem4109581) (@lem4109580)). Qed.
Lemma lem4109583 : term232 = term233.
Proof. exact (MK_COMB (@lem4109582) (@lem4109577)). Qed.
Lemma lem4109584 : term233 = term234.
Proof. exact (@lem1981613 term178 term204 term111 term111). Qed.
Lemma lem4109586 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109587 : term187 = term188.
Proof. exact (@lem4109586 term20 term20). Qed.
Lemma lem4109588 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109589 : term190 = term20.
Proof. exact (EQ_MP (@lem4109588) (@lem940073)). Qed.
Lemma lem4109590 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109591 : term188 = term111.
Proof. exact (MK_COMB (@lem4109590) (@lem4109589)). Qed.
Lemma lem4109592 : term187 = term111.
Proof. exact (TRANS (@lem4109587) (@lem4109591)). Qed.
Lemma lem4109594 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4109595 : term232 = term237.
Proof. exact (@lem4109594 term20 term218). Qed.
Lemma lem4109596 : term238 = term216.
Proof. exact (@lem996238 term216). Qed.
Lemma lem4109597 : (term238 = term216) = (term239 = term218).
Proof. exact (@lem1007663 (BIT1 0) term216 term216). Qed.
Lemma lem4109598 : term239 = term218.
Proof. exact (EQ_MP (@lem4109597) (@lem4109596)). Qed.
Lemma lem4109599 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109600 : term240 = term204.
Proof. exact (MK_COMB (@lem4109599) (@lem4109598)). Qed.
Lemma lem4109601 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4109602 : term237 = term241.
Proof. exact (MK_COMB (@lem4109601) (@lem4109600)). Qed.
Lemma lem4109603 : term232 = term241.
Proof. exact (TRANS (@lem4109595) (@lem4109602)). Qed.
Lemma lem4109604 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4109605 : term242 = term243.
Proof. exact (MK_COMB (@lem4109604) (@lem4109603)). Qed.
Lemma lem4109606 : term234 = term244.
Proof. exact (MK_COMB (@lem4109605) (@lem4109592)). Qed.
Lemma lem4109607 : term233 = term244.
Proof. exact (TRANS (@lem4109584) (@lem4109606)). Qed.
Lemma lem4109608 : term232 = term244.
Proof. exact (TRANS (@lem4109583) (@lem4109607)). Qed.
Lemma lem4109610 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4109611 : term244 = term241.
Proof. exact (@lem4109610 term241). Qed.
Lemma lem4109612 : term232 = term241.
Proof. exact (TRANS (@lem4109608) (@lem4109611)). Qed.
Lemma lem4109613 (_48296 : int) : (term126 _48296) = (term126 _48296).
Proof. exact (eq_refl (term126 _48296)). Qed.
Lemma lem4109616 (_48296 : int) : (term231 _48296) = (term245 _48296).
Proof. exact (MK_COMB (@lem4109613 _48296) (@lem4109612)). Qed.
Lemma lem4109617 (_48296 : int) : (term230 _48296) = (term245 _48296).
Proof. exact (TRANS (@lem4109574 _48296) (@lem4109616 _48296)). Qed.
Lemma lem4109618 (_48296 : int) : (term229 _48296) = (term245 _48296).
Proof. exact (TRANS (@lem4109573 _48296) (@lem4109617 _48296)). Qed.
Lemma lem4109619 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4109620 (_48296 : int) : (term246 _48296) = (term247 _48296).
Proof. exact (MK_COMB (@lem4109619) (@lem4109618 _48296)). Qed.
Lemma lem4109621 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4109622 (_48296 : int) : (term199 _48296) = (term248 _48296).
Proof. exact (MK_COMB (@lem4109620 _48296) (@lem4109621)). Qed.
Lemma lem4109623 (_48296 : int) : (term117 _48296) = (term248 _48296).
Proof. exact (TRANS (@lem4109451 _48296) (@lem4109622 _48296)). Qed.
Lemma lem4109624 (_48296 : int) : (term130 _48296) = (term249 _48296).
Proof. exact (@lem1988287 term97 (term127 _48296)). Qed.
Lemma lem4109636 (_48296 : int) : (term250 _48296) = (term251 _48296).
Proof. exact (@lem1982792 term97 (term127 _48296)). Qed.
Lemma lem4109637 (_48296 : int) : (term252 _48296) = (term253 _48296).
Proof. exact (@lem1982781 (real_of_int _48296) term178 term111). Qed.
Lemma lem4109639 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4109640 : term111 = term200.
Proof. exact (@lem4109639 term20). Qed.
Lemma lem4109642 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4109643 : term178 = term179.
Proof. exact (@lem4109642 term20). Qed.
Lemma lem4109644 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4109645 : term180 = term181.
Proof. exact (MK_COMB (@lem4109644) (@lem4109643)). Qed.
Lemma lem4109646 : term254 = term255.
Proof. exact (MK_COMB (@lem4109645) (@lem4109640)). Qed.
Lemma lem4109647 : term255 = term256.
Proof. exact (@lem1981613 term178 term111 term111 term111). Qed.
Lemma lem4109649 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109650 : term187 = term188.
Proof. exact (@lem4109649 term20 term20). Qed.
Lemma lem4109651 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109652 : term190 = term20.
Proof. exact (EQ_MP (@lem4109651) (@lem940073)). Qed.
Lemma lem4109653 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109654 : term188 = term111.
Proof. exact (MK_COMB (@lem4109653) (@lem4109652)). Qed.
Lemma lem4109655 : term187 = term111.
Proof. exact (TRANS (@lem4109650) (@lem4109654)). Qed.
Lemma lem4109657 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4109658 : term254 = term257.
Proof. exact (@lem4109657 term20 term20). Qed.
Lemma lem4109659 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109660 : term190 = term20.
Proof. exact (EQ_MP (@lem4109659) (@lem940073)). Qed.
Lemma lem4109661 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109662 : term188 = term111.
Proof. exact (MK_COMB (@lem4109661) (@lem4109660)). Qed.
Lemma lem4109663 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4109664 : term257 = term178.
Proof. exact (MK_COMB (@lem4109663) (@lem4109662)). Qed.
Lemma lem4109665 : term254 = term178.
Proof. exact (TRANS (@lem4109658) (@lem4109664)). Qed.
Lemma lem4109666 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4109667 : term258 = term259.
Proof. exact (MK_COMB (@lem4109666) (@lem4109665)). Qed.
Lemma lem4109668 : term256 = term179.
Proof. exact (MK_COMB (@lem4109667) (@lem4109655)). Qed.
Lemma lem4109669 : term255 = term179.
Proof. exact (TRANS (@lem4109647) (@lem4109668)). Qed.
Lemma lem4109670 : term254 = term179.
Proof. exact (TRANS (@lem4109646) (@lem4109669)). Qed.
Lemma lem4109672 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4109673 : term179 = term178.
Proof. exact (@lem4109672 term178). Qed.
Lemma lem4109674 : term254 = term178.
Proof. exact (TRANS (@lem4109670) (@lem4109673)). Qed.
Lemma lem4109677 (_48296 : int) : (term260 _48296) = (term260 _48296).
Proof. exact (eq_refl (term260 _48296)). Qed.
Lemma lem4109678 (_48296 : int) : (term253 _48296) = (term261 _48296).
Proof. exact (MK_COMB (@lem4109677 _48296) (@lem4109674)). Qed.
Lemma lem4109679 (_48296 : int) : (term252 _48296) = (term261 _48296).
Proof. exact (TRANS (@lem4109637 _48296) (@lem4109678 _48296)). Qed.
Lemma lem4109680 : term139 = term139.
Proof. exact (eq_refl term139). Qed.
Lemma lem4109681 (_48296 : int) : (term251 _48296) = (term262 _48296).
Proof. exact (MK_COMB (@lem4109680) (@lem4109679 _48296)). Qed.
Lemma lem4109682 (_48296 : int) : (term262 _48296) = (term261 _48296).
Proof. exact (@lem1982721 (term261 _48296)). Qed.
Lemma lem4109683 (_48296 : int) : (term251 _48296) = (term261 _48296).
Proof. exact (TRANS (@lem4109681 _48296) (@lem4109682 _48296)). Qed.
Lemma lem4109685 (_48296 : int) : (term250 _48296) = (term261 _48296).
Proof. exact (TRANS (@lem4109636 _48296) (@lem4109683 _48296)). Qed.
Lemma lem4109686 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4109687 (_48296 : int) : (term263 _48296) = (term264 _48296).
Proof. exact (MK_COMB (@lem4109686) (@lem4109685 _48296)). Qed.
Lemma lem4109688 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4109689 (_48296 : int) : (term249 _48296) = (term265 _48296).
Proof. exact (MK_COMB (@lem4109687 _48296) (@lem4109688)). Qed.
Lemma lem4109690 (_48296 : int) : (term130 _48296) = (term265 _48296).
Proof. exact (TRANS (@lem4109624 _48296) (@lem4109689 _48296)). Qed.
Lemma lem4109691 (_48296 : int) : (term143 _48296) = (term266 _48296).
Proof. exact (@lem1988287 (real_of_int _48296) term140). Qed.
Lemma lem4109698 : term140 = term111.
Proof. exact (@lem1982721 term111). Qed.
Lemma lem4109701 (_48296 : int) : (term228 _48296) = (term228 _48296).
Proof. exact (eq_refl (term228 _48296)). Qed.
Lemma lem4109702 (_48296 : int) : (term267 _48296) = (term268 _48296).
Proof. exact (MK_COMB (@lem4109701 _48296) (@lem4109698)). Qed.
Lemma lem4109703 (_48296 : int) : (term268 _48296) = (term269 _48296).
Proof. exact (@lem1982792 (real_of_int _48296) term111). Qed.
Lemma lem4109705 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4109706 : term111 = term200.
Proof. exact (@lem4109705 term20). Qed.
Lemma lem4109708 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4109709 : term178 = term179.
Proof. exact (@lem4109708 term20). Qed.
Lemma lem4109710 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4109711 : term180 = term181.
Proof. exact (MK_COMB (@lem4109710) (@lem4109709)). Qed.
Lemma lem4109712 : term254 = term255.
Proof. exact (MK_COMB (@lem4109711) (@lem4109706)). Qed.
Lemma lem4109713 : term255 = term256.
Proof. exact (@lem1981613 term178 term111 term111 term111). Qed.
Lemma lem4109715 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109716 : term187 = term188.
Proof. exact (@lem4109715 term20 term20). Qed.
Lemma lem4109717 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109718 : term190 = term20.
Proof. exact (EQ_MP (@lem4109717) (@lem940073)). Qed.
Lemma lem4109719 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109720 : term188 = term111.
Proof. exact (MK_COMB (@lem4109719) (@lem4109718)). Qed.
Lemma lem4109721 : term187 = term111.
Proof. exact (TRANS (@lem4109716) (@lem4109720)). Qed.
Lemma lem4109723 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4109724 : term254 = term257.
Proof. exact (@lem4109723 term20 term20). Qed.
Lemma lem4109725 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109726 : term190 = term20.
Proof. exact (EQ_MP (@lem4109725) (@lem940073)). Qed.
Lemma lem4109727 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109728 : term188 = term111.
Proof. exact (MK_COMB (@lem4109727) (@lem4109726)). Qed.
Lemma lem4109729 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4109730 : term257 = term178.
Proof. exact (MK_COMB (@lem4109729) (@lem4109728)). Qed.
Lemma lem4109731 : term254 = term178.
Proof. exact (TRANS (@lem4109724) (@lem4109730)). Qed.
Lemma lem4109732 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4109733 : term258 = term259.
Proof. exact (MK_COMB (@lem4109732) (@lem4109731)). Qed.
Lemma lem4109734 : term256 = term179.
Proof. exact (MK_COMB (@lem4109733) (@lem4109721)). Qed.
Lemma lem4109735 : term255 = term179.
Proof. exact (TRANS (@lem4109713) (@lem4109734)). Qed.
Lemma lem4109736 : term254 = term179.
Proof. exact (TRANS (@lem4109712) (@lem4109735)). Qed.
Lemma lem4109738 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4109739 : term179 = term178.
Proof. exact (@lem4109738 term178). Qed.
Lemma lem4109740 : term254 = term178.
Proof. exact (TRANS (@lem4109736) (@lem4109739)). Qed.
Lemma lem4109741 (_48296 : int) : (term126 _48296) = (term126 _48296).
Proof. exact (eq_refl (term126 _48296)). Qed.
Lemma lem4109744 (_48296 : int) : (term269 _48296) = (term270 _48296).
Proof. exact (MK_COMB (@lem4109741 _48296) (@lem4109740)). Qed.
Lemma lem4109745 (_48296 : int) : (term268 _48296) = (term270 _48296).
Proof. exact (TRANS (@lem4109703 _48296) (@lem4109744 _48296)). Qed.
Lemma lem4109746 (_48296 : int) : (term267 _48296) = (term270 _48296).
Proof. exact (TRANS (@lem4109702 _48296) (@lem4109745 _48296)). Qed.
Lemma lem4109747 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4109748 (_48296 : int) : (term271 _48296) = (term272 _48296).
Proof. exact (MK_COMB (@lem4109747) (@lem4109746 _48296)). Qed.
Lemma lem4109749 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4109750 (_48296 : int) : (term266 _48296) = (term273 _48296).
Proof. exact (MK_COMB (@lem4109748 _48296) (@lem4109749)). Qed.
Lemma lem4109751 (_48296 : int) : (term143 _48296) = (term273 _48296).
Proof. exact (TRANS (@lem4109691 _48296) (@lem4109750 _48296)). Qed.
Lemma lem4109752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4109753 (_48296 : int) : (term132 _48296) = (term274 _48296).
Proof. exact (MK_COMB (@lem4109752) (@lem4109690 _48296)). Qed.
Lemma lem4109754 (_48296 : int) : (term144 _48296) = (term275 _48296).
Proof. exact (MK_COMB (@lem4109753 _48296) (@lem4109751 _48296)). Qed.
Lemma lem4109755 (_48296 : int) : (term148 _48296) = (term276 _48296).
Proof. exact (@lem1988287 term111 (term127 _48296)). Qed.
Lemma lem4109767 (_48296 : int) : (term277 _48296) = (term278 _48296).
Proof. exact (@lem1982792 term111 (term127 _48296)). Qed.
Lemma lem4109768 (_48296 : int) : (term252 _48296) = (term253 _48296).
Proof. exact (@lem1982781 (real_of_int _48296) term178 term111). Qed.
Lemma lem4109770 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4109771 : term111 = term200.
Proof. exact (@lem4109770 term20). Qed.
Lemma lem4109773 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4109774 : term178 = term179.
Proof. exact (@lem4109773 term20). Qed.
Lemma lem4109775 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4109776 : term180 = term181.
Proof. exact (MK_COMB (@lem4109775) (@lem4109774)). Qed.
Lemma lem4109777 : term254 = term255.
Proof. exact (MK_COMB (@lem4109776) (@lem4109771)). Qed.
Lemma lem4109778 : term255 = term256.
Proof. exact (@lem1981613 term178 term111 term111 term111). Qed.
Lemma lem4109780 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109781 : term187 = term188.
Proof. exact (@lem4109780 term20 term20). Qed.
Lemma lem4109782 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109783 : term190 = term20.
Proof. exact (EQ_MP (@lem4109782) (@lem940073)). Qed.
Lemma lem4109784 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109785 : term188 = term111.
Proof. exact (MK_COMB (@lem4109784) (@lem4109783)). Qed.
Lemma lem4109786 : term187 = term111.
Proof. exact (TRANS (@lem4109781) (@lem4109785)). Qed.
Lemma lem4109788 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4109789 : term254 = term257.
Proof. exact (@lem4109788 term20 term20). Qed.
Lemma lem4109790 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109791 : term190 = term20.
Proof. exact (EQ_MP (@lem4109790) (@lem940073)). Qed.
Lemma lem4109792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109793 : term188 = term111.
Proof. exact (MK_COMB (@lem4109792) (@lem4109791)). Qed.
Lemma lem4109794 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4109795 : term257 = term178.
Proof. exact (MK_COMB (@lem4109794) (@lem4109793)). Qed.
Lemma lem4109796 : term254 = term178.
Proof. exact (TRANS (@lem4109789) (@lem4109795)). Qed.
Lemma lem4109797 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4109798 : term258 = term259.
Proof. exact (MK_COMB (@lem4109797) (@lem4109796)). Qed.
Lemma lem4109799 : term256 = term179.
Proof. exact (MK_COMB (@lem4109798) (@lem4109786)). Qed.
Lemma lem4109800 : term255 = term179.
Proof. exact (TRANS (@lem4109778) (@lem4109799)). Qed.
Lemma lem4109801 : term254 = term179.
Proof. exact (TRANS (@lem4109777) (@lem4109800)). Qed.
Lemma lem4109803 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4109804 : term179 = term178.
Proof. exact (@lem4109803 term178). Qed.
Lemma lem4109805 : term254 = term178.
Proof. exact (TRANS (@lem4109801) (@lem4109804)). Qed.
Lemma lem4109808 (_48296 : int) : (term260 _48296) = (term260 _48296).
Proof. exact (eq_refl (term260 _48296)). Qed.
Lemma lem4109809 (_48296 : int) : (term253 _48296) = (term261 _48296).
Proof. exact (MK_COMB (@lem4109808 _48296) (@lem4109805)). Qed.
Lemma lem4109810 (_48296 : int) : (term252 _48296) = (term261 _48296).
Proof. exact (TRANS (@lem4109768 _48296) (@lem4109809 _48296)). Qed.
Lemma lem4109811 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem4109812 (_48296 : int) : (term278 _48296) = (term279 _48296).
Proof. exact (MK_COMB (@lem4109811) (@lem4109810 _48296)). Qed.
Lemma lem4109813 (_48296 : int) : (term279 _48296) = (term280 _48296).
Proof. exact (@lem1982757 (term281 _48296) term111 term178). Qed.
Lemma lem4109815 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4109816 : term178 = term179.
Proof. exact (@lem4109815 term20). Qed.
Lemma lem4109818 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4109819 : term111 = term200.
Proof. exact (@lem4109818 term20). Qed.
Lemma lem4109820 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4109821 : term113 = term201.
Proof. exact (MK_COMB (@lem4109820) (@lem4109819)). Qed.
Lemma lem4109822 : term282 = term283.
Proof. exact (MK_COMB (@lem4109821) (@lem4109816)). Qed.
Lemma lem4109823 : term284.
Proof. exact (@lem1981473 term111 term111 term178 term111 term97 term111). Qed.
Lemma lem4109825 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4109826 : term206 = term207.
Proof. exact (@lem4109825 (NUMERAL 0) term20). Qed.
Lemma lem4109827 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4109828 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4109829 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4109828 h1) (fun h1 : term207 = True => @lem4109827)). Qed.
Lemma lem4109830 : term207 = True.
Proof. exact (EQ_MP (@lem4109829) (@lem4109827)). Qed.
Lemma lem4109831 : term206 = True.
Proof. exact (TRANS (@lem4109826) (@lem4109830)). Qed.
Lemma lem4109832 : True = term206.
Proof. exact (SYM (@lem4109831)). Qed.
Lemma lem4109833 : term206.
Proof. exact (EQ_MP (@lem4109832) (@lem0)). Qed.
Lemma lem4109834 : term285.
Proof. exact (@lem4109823 (@lem4109833)). Qed.
Lemma lem4109836 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4109837 : term206 = term207.
Proof. exact (@lem4109836 (NUMERAL 0) term20). Qed.
Lemma lem4109838 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4109839 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4109840 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4109839 h1) (fun h1 : term207 = True => @lem4109838)). Qed.
Lemma lem4109841 : term207 = True.
Proof. exact (EQ_MP (@lem4109840) (@lem4109838)). Qed.
Lemma lem4109842 : term206 = True.
Proof. exact (TRANS (@lem4109837) (@lem4109841)). Qed.
Lemma lem4109843 : True = term206.
Proof. exact (SYM (@lem4109842)). Qed.
Lemma lem4109844 : term206.
Proof. exact (EQ_MP (@lem4109843) (@lem0)). Qed.
Lemma lem4109845 : term286.
Proof. exact (@lem4109834 (@lem4109844)). Qed.
Lemma lem4109847 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4109848 : term206 = term207.
Proof. exact (@lem4109847 (NUMERAL 0) term20). Qed.
Lemma lem4109849 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4109850 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4109851 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4109850 h1) (fun h1 : term207 = True => @lem4109849)). Qed.
Lemma lem4109852 : term207 = True.
Proof. exact (EQ_MP (@lem4109851) (@lem4109849)). Qed.
Lemma lem4109853 : term206 = True.
Proof. exact (TRANS (@lem4109848) (@lem4109852)). Qed.
Lemma lem4109854 : True = term206.
Proof. exact (SYM (@lem4109853)). Qed.
Lemma lem4109855 : term206.
Proof. exact (EQ_MP (@lem4109854) (@lem0)). Qed.
Lemma lem4109856 : term287.
Proof. exact (@lem4109845 (@lem4109855)). Qed.
Lemma lem4109858 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4109859 : term254 = term257.
Proof. exact (@lem4109858 term20 term20). Qed.
Lemma lem4109860 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109861 : term190 = term20.
Proof. exact (EQ_MP (@lem4109860) (@lem940073)). Qed.
Lemma lem4109862 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109863 : term188 = term111.
Proof. exact (MK_COMB (@lem4109862) (@lem4109861)). Qed.
Lemma lem4109864 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4109865 : term257 = term178.
Proof. exact (MK_COMB (@lem4109864) (@lem4109863)). Qed.
Lemma lem4109866 : term254 = term178.
Proof. exact (TRANS (@lem4109859) (@lem4109865)). Qed.
Lemma lem4109868 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109869 : term187 = term188.
Proof. exact (@lem4109868 term20 term20). Qed.
Lemma lem4109870 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109871 : term190 = term20.
Proof. exact (EQ_MP (@lem4109870) (@lem940073)). Qed.
Lemma lem4109872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109873 : term188 = term111.
Proof. exact (MK_COMB (@lem4109872) (@lem4109871)). Qed.
Lemma lem4109874 : term187 = term111.
Proof. exact (TRANS (@lem4109869) (@lem4109873)). Qed.
Lemma lem4109875 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4109876 : term212 = term113.
Proof. exact (MK_COMB (@lem4109875) (@lem4109874)). Qed.
Lemma lem4109877 : term288 = term282.
Proof. exact (MK_COMB (@lem4109876) (@lem4109866)). Qed.
Lemma lem4109879 (m : nat) : (term289 m) = term97.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem4109880 : term282 = term97.
Proof. exact (@lem4109879 term20). Qed.
Lemma lem4109881 : term288 = term97.
Proof. exact (TRANS (@lem4109877) (@lem4109880)). Qed.
Lemma lem4109882 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4109883 : term290 = term291.
Proof. exact (MK_COMB (@lem4109882) (@lem4109881)). Qed.
Lemma lem4109884 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4109885 : term292 = term293.
Proof. exact (MK_COMB (@lem4109883) (@lem4109884)). Qed.
Lemma lem4109887 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4109888 : term293 = term97.
Proof. exact (@lem4109887 term20). Qed.
Lemma lem4109889 : term292 = term97.
Proof. exact (TRANS (@lem4109885) (@lem4109888)). Qed.
Lemma lem4109891 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109892 : term187 = term188.
Proof. exact (@lem4109891 term20 term20). Qed.
Lemma lem4109893 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109894 : term190 = term20.
Proof. exact (EQ_MP (@lem4109893) (@lem940073)). Qed.
Lemma lem4109895 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109896 : term188 = term111.
Proof. exact (MK_COMB (@lem4109895) (@lem4109894)). Qed.
Lemma lem4109897 : term187 = term111.
Proof. exact (TRANS (@lem4109892) (@lem4109896)). Qed.
Lemma lem4109898 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4109899 : term295 = term293.
Proof. exact (MK_COMB (@lem4109898) (@lem4109897)). Qed.
Lemma lem4109901 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4109902 : term293 = term97.
Proof. exact (@lem4109901 term20). Qed.
Lemma lem4109903 : term295 = term97.
Proof. exact (TRANS (@lem4109899) (@lem4109902)). Qed.
Lemma lem4109904 : term97 = term295.
Proof. exact (SYM (@lem4109903)). Qed.
Lemma lem4109905 : term292 = term295.
Proof. exact (TRANS (@lem4109889) (@lem4109904)). Qed.
Lemma lem4109906 : term283 = term175.
Proof. exact (@lem4109856 (@lem4109905)). Qed.
Lemma lem4109907 : term282 = term175.
Proof. exact (TRANS (@lem4109822) (@lem4109906)). Qed.
Lemma lem4109909 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4109910 : term175 = term97.
Proof. exact (@lem4109909 term97). Qed.
Lemma lem4109911 : term282 = term97.
Proof. exact (TRANS (@lem4109907) (@lem4109910)). Qed.
Lemma lem4109912 (_48296 : int) : (term260 _48296) = (term260 _48296).
Proof. exact (eq_refl (term260 _48296)). Qed.
Lemma lem4109913 (_48296 : int) : (term280 _48296) = (term296 _48296).
Proof. exact (MK_COMB (@lem4109912 _48296) (@lem4109911)). Qed.
Lemma lem4109914 (_48296 : int) : (term279 _48296) = (term296 _48296).
Proof. exact (TRANS (@lem4109813 _48296) (@lem4109913 _48296)). Qed.
Lemma lem4109915 (_48296 : int) : (term296 _48296) = (term281 _48296).
Proof. exact (@lem1982723 (term281 _48296)). Qed.
Lemma lem4109916 (_48296 : int) : (term279 _48296) = (term281 _48296).
Proof. exact (TRANS (@lem4109914 _48296) (@lem4109915 _48296)). Qed.
Lemma lem4109917 (_48296 : int) : (term278 _48296) = (term281 _48296).
Proof. exact (TRANS (@lem4109812 _48296) (@lem4109916 _48296)). Qed.
Lemma lem4109919 (_48296 : int) : (term277 _48296) = (term281 _48296).
Proof. exact (TRANS (@lem4109767 _48296) (@lem4109917 _48296)). Qed.
Lemma lem4109920 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4109921 (_48296 : int) : (term297 _48296) = (term298 _48296).
Proof. exact (MK_COMB (@lem4109920) (@lem4109919 _48296)). Qed.
Lemma lem4109922 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4109923 (_48296 : int) : (term276 _48296) = (term299 _48296).
Proof. exact (MK_COMB (@lem4109921 _48296) (@lem4109922)). Qed.
Lemma lem4109924 (_48296 : int) : (term148 _48296) = (term299 _48296).
Proof. exact (TRANS (@lem4109755 _48296) (@lem4109923 _48296)). Qed.
Lemma lem4109925 (_48296 : int) : (term117 _48296) = (term199 _48296).
Proof. exact (@lem1988287 (real_of_int _48296) term114). Qed.
Lemma lem4109932 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4109933 : term111 = term200.
Proof. exact (@lem4109932 term20). Qed.
Lemma lem4109935 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4109936 : term111 = term200.
Proof. exact (@lem4109935 term20). Qed.
Lemma lem4109937 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4109938 : term113 = term201.
Proof. exact (MK_COMB (@lem4109937) (@lem4109936)). Qed.
Lemma lem4109939 : term114 = term202.
Proof. exact (MK_COMB (@lem4109938) (@lem4109933)). Qed.
Lemma lem4109940 : term203.
Proof. exact (@lem1981473 term111 term111 term111 term111 term204 term111). Qed.
Lemma lem4109942 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4109943 : term206 = term207.
Proof. exact (@lem4109942 (NUMERAL 0) term20). Qed.
Lemma lem4109944 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4109945 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4109946 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4109945 h1) (fun h1 : term207 = True => @lem4109944)). Qed.
Lemma lem4109947 : term207 = True.
Proof. exact (EQ_MP (@lem4109946) (@lem4109944)). Qed.
Lemma lem4109948 : term206 = True.
Proof. exact (TRANS (@lem4109943) (@lem4109947)). Qed.
Lemma lem4109949 : True = term206.
Proof. exact (SYM (@lem4109948)). Qed.
Lemma lem4109950 : term206.
Proof. exact (EQ_MP (@lem4109949) (@lem0)). Qed.
Lemma lem4109951 : term209.
Proof. exact (@lem4109940 (@lem4109950)). Qed.
Lemma lem4109953 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4109954 : term206 = term207.
Proof. exact (@lem4109953 (NUMERAL 0) term20). Qed.
Lemma lem4109955 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4109956 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4109957 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4109956 h1) (fun h1 : term207 = True => @lem4109955)). Qed.
Lemma lem4109958 : term207 = True.
Proof. exact (EQ_MP (@lem4109957) (@lem4109955)). Qed.
Lemma lem4109959 : term206 = True.
Proof. exact (TRANS (@lem4109954) (@lem4109958)). Qed.
Lemma lem4109960 : True = term206.
Proof. exact (SYM (@lem4109959)). Qed.
Lemma lem4109961 : term206.
Proof. exact (EQ_MP (@lem4109960) (@lem0)). Qed.
Lemma lem4109962 : term210.
Proof. exact (@lem4109951 (@lem4109961)). Qed.
Lemma lem4109964 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4109965 : term206 = term207.
Proof. exact (@lem4109964 (NUMERAL 0) term20). Qed.
Lemma lem4109966 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4109967 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4109968 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4109967 h1) (fun h1 : term207 = True => @lem4109966)). Qed.
Lemma lem4109969 : term207 = True.
Proof. exact (EQ_MP (@lem4109968) (@lem4109966)). Qed.
Lemma lem4109970 : term206 = True.
Proof. exact (TRANS (@lem4109965) (@lem4109969)). Qed.
Lemma lem4109971 : True = term206.
Proof. exact (SYM (@lem4109970)). Qed.
Lemma lem4109972 : term206.
Proof. exact (EQ_MP (@lem4109971) (@lem0)). Qed.
Lemma lem4109973 : term211.
Proof. exact (@lem4109962 (@lem4109972)). Qed.
Lemma lem4109975 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109976 : term187 = term188.
Proof. exact (@lem4109975 term20 term20). Qed.
Lemma lem4109977 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109978 : term190 = term20.
Proof. exact (EQ_MP (@lem4109977) (@lem940073)). Qed.
Lemma lem4109979 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109980 : term188 = term111.
Proof. exact (MK_COMB (@lem4109979) (@lem4109978)). Qed.
Lemma lem4109981 : term187 = term111.
Proof. exact (TRANS (@lem4109976) (@lem4109980)). Qed.
Lemma lem4109983 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4109984 : term187 = term188.
Proof. exact (@lem4109983 term20 term20). Qed.
Lemma lem4109985 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4109986 : term190 = term20.
Proof. exact (EQ_MP (@lem4109985) (@lem940073)). Qed.
Lemma lem4109987 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109988 : term188 = term111.
Proof. exact (MK_COMB (@lem4109987) (@lem4109986)). Qed.
Lemma lem4109989 : term187 = term111.
Proof. exact (TRANS (@lem4109984) (@lem4109988)). Qed.
Lemma lem4109990 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4109991 : term212 = term113.
Proof. exact (MK_COMB (@lem4109990) (@lem4109989)). Qed.
Lemma lem4109992 : term213 = term114.
Proof. exact (MK_COMB (@lem4109991) (@lem4109981)). Qed.
Lemma lem4109993 : term114 = term214.
Proof. exact (@lem1367770 term20 term20). Qed.
Lemma lem4109994 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem4109995 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem4109996 : term217 = term218.
Proof. exact (EQ_MP (@lem4109995) (@lem4109994)). Qed.
Lemma lem4109997 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4109998 : term214 = term204.
Proof. exact (MK_COMB (@lem4109997) (@lem4109996)). Qed.
Lemma lem4109999 : term114 = term204.
Proof. exact (TRANS (@lem4109993) (@lem4109998)). Qed.
Lemma lem4110000 : term213 = term204.
Proof. exact (TRANS (@lem4109992) (@lem4109999)). Qed.
Lemma lem4110001 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4110002 : term219 = term220.
Proof. exact (MK_COMB (@lem4110001) (@lem4110000)). Qed.
Lemma lem4110003 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4110004 : term221 = term222.
Proof. exact (MK_COMB (@lem4110002) (@lem4110003)). Qed.
Lemma lem4110006 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4110007 : term222 = term223.
Proof. exact (@lem4110006 term218 term20). Qed.
Lemma lem4110008 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4110009 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4110010 : term225 = term218.
Proof. exact (EQ_MP (@lem4110009) (@lem4110008)). Qed.
Lemma lem4110011 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110012 : term223 = term204.
Proof. exact (MK_COMB (@lem4110011) (@lem4110010)). Qed.
Lemma lem4110013 : term222 = term204.
Proof. exact (TRANS (@lem4110007) (@lem4110012)). Qed.
Lemma lem4110014 : term221 = term204.
Proof. exact (TRANS (@lem4110004) (@lem4110013)). Qed.
Lemma lem4110016 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4110017 : term187 = term188.
Proof. exact (@lem4110016 term20 term20). Qed.
Lemma lem4110018 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110019 : term190 = term20.
Proof. exact (EQ_MP (@lem4110018) (@lem940073)). Qed.
Lemma lem4110020 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110021 : term188 = term111.
Proof. exact (MK_COMB (@lem4110020) (@lem4110019)). Qed.
Lemma lem4110022 : term187 = term111.
Proof. exact (TRANS (@lem4110017) (@lem4110021)). Qed.
Lemma lem4110023 : term220 = term220.
Proof. exact (eq_refl term220). Qed.
Lemma lem4110024 : term226 = term222.
Proof. exact (MK_COMB (@lem4110023) (@lem4110022)). Qed.
Lemma lem4110026 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4110027 : term222 = term223.
Proof. exact (@lem4110026 term218 term20). Qed.
Lemma lem4110028 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4110029 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4110030 : term225 = term218.
Proof. exact (EQ_MP (@lem4110029) (@lem4110028)). Qed.
Lemma lem4110031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110032 : term223 = term204.
Proof. exact (MK_COMB (@lem4110031) (@lem4110030)). Qed.
Lemma lem4110033 : term222 = term204.
Proof. exact (TRANS (@lem4110027) (@lem4110032)). Qed.
Lemma lem4110034 : term226 = term204.
Proof. exact (TRANS (@lem4110024) (@lem4110033)). Qed.
Lemma lem4110035 : term204 = term226.
Proof. exact (SYM (@lem4110034)). Qed.
Lemma lem4110036 : term221 = term226.
Proof. exact (TRANS (@lem4110014) (@lem4110035)). Qed.
Lemma lem4110037 : term202 = term227.
Proof. exact (@lem4109973 (@lem4110036)). Qed.
Lemma lem4110038 : term114 = term227.
Proof. exact (TRANS (@lem4109939) (@lem4110037)). Qed.
Lemma lem4110040 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4110041 : term227 = term204.
Proof. exact (@lem4110040 term204). Qed.
Lemma lem4110043 : term114 = term204.
Proof. exact (TRANS (@lem4110038) (@lem4110041)). Qed.
Lemma lem4110046 (_48296 : int) : (term228 _48296) = (term228 _48296).
Proof. exact (eq_refl (term228 _48296)). Qed.
Lemma lem4110047 (_48296 : int) : (term229 _48296) = (term230 _48296).
Proof. exact (MK_COMB (@lem4110046 _48296) (@lem4110043)). Qed.
Lemma lem4110048 (_48296 : int) : (term230 _48296) = (term231 _48296).
Proof. exact (@lem1982792 (real_of_int _48296) term204). Qed.
Lemma lem4110050 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4110051 : term204 = term227.
Proof. exact (@lem4110050 term218). Qed.
Lemma lem4110053 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4110054 : term178 = term179.
Proof. exact (@lem4110053 term20). Qed.
Lemma lem4110055 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4110056 : term180 = term181.
Proof. exact (MK_COMB (@lem4110055) (@lem4110054)). Qed.
Lemma lem4110057 : term232 = term233.
Proof. exact (MK_COMB (@lem4110056) (@lem4110051)). Qed.
Lemma lem4110058 : term233 = term234.
Proof. exact (@lem1981613 term178 term204 term111 term111). Qed.
Lemma lem4110060 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4110061 : term187 = term188.
Proof. exact (@lem4110060 term20 term20). Qed.
Lemma lem4110062 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110063 : term190 = term20.
Proof. exact (EQ_MP (@lem4110062) (@lem940073)). Qed.
Lemma lem4110064 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110065 : term188 = term111.
Proof. exact (MK_COMB (@lem4110064) (@lem4110063)). Qed.
Lemma lem4110066 : term187 = term111.
Proof. exact (TRANS (@lem4110061) (@lem4110065)). Qed.
Lemma lem4110068 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4110069 : term232 = term237.
Proof. exact (@lem4110068 term20 term218). Qed.
Lemma lem4110070 : term238 = term216.
Proof. exact (@lem996238 term216). Qed.
Lemma lem4110071 : (term238 = term216) = (term239 = term218).
Proof. exact (@lem1007663 (BIT1 0) term216 term216). Qed.
Lemma lem4110072 : term239 = term218.
Proof. exact (EQ_MP (@lem4110071) (@lem4110070)). Qed.
Lemma lem4110073 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110074 : term240 = term204.
Proof. exact (MK_COMB (@lem4110073) (@lem4110072)). Qed.
Lemma lem4110075 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4110076 : term237 = term241.
Proof. exact (MK_COMB (@lem4110075) (@lem4110074)). Qed.
Lemma lem4110077 : term232 = term241.
Proof. exact (TRANS (@lem4110069) (@lem4110076)). Qed.
Lemma lem4110078 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4110079 : term242 = term243.
Proof. exact (MK_COMB (@lem4110078) (@lem4110077)). Qed.
Lemma lem4110080 : term234 = term244.
Proof. exact (MK_COMB (@lem4110079) (@lem4110066)). Qed.
Lemma lem4110081 : term233 = term244.
Proof. exact (TRANS (@lem4110058) (@lem4110080)). Qed.
Lemma lem4110082 : term232 = term244.
Proof. exact (TRANS (@lem4110057) (@lem4110081)). Qed.
Lemma lem4110084 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4110085 : term244 = term241.
Proof. exact (@lem4110084 term241). Qed.
Lemma lem4110086 : term232 = term241.
Proof. exact (TRANS (@lem4110082) (@lem4110085)). Qed.
Lemma lem4110087 (_48296 : int) : (term126 _48296) = (term126 _48296).
Proof. exact (eq_refl (term126 _48296)). Qed.
Lemma lem4110090 (_48296 : int) : (term231 _48296) = (term245 _48296).
Proof. exact (MK_COMB (@lem4110087 _48296) (@lem4110086)). Qed.
Lemma lem4110091 (_48296 : int) : (term230 _48296) = (term245 _48296).
Proof. exact (TRANS (@lem4110048 _48296) (@lem4110090 _48296)). Qed.
Lemma lem4110092 (_48296 : int) : (term229 _48296) = (term245 _48296).
Proof. exact (TRANS (@lem4110047 _48296) (@lem4110091 _48296)). Qed.
Lemma lem4110093 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4110094 (_48296 : int) : (term246 _48296) = (term247 _48296).
Proof. exact (MK_COMB (@lem4110093) (@lem4110092 _48296)). Qed.
Lemma lem4110095 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4110096 (_48296 : int) : (term199 _48296) = (term248 _48296).
Proof. exact (MK_COMB (@lem4110094 _48296) (@lem4110095)). Qed.
Lemma lem4110097 (_48296 : int) : (term117 _48296) = (term248 _48296).
Proof. exact (TRANS (@lem4109925 _48296) (@lem4110096 _48296)). Qed.
Lemma lem4110098 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110099 (_48296 : int) : (term150 _48296) = (term300 _48296).
Proof. exact (MK_COMB (@lem4110098) (@lem4109924 _48296)). Qed.
Lemma lem4110100 (_48296 : int) : (term151 _48296) = (term301 _48296).
Proof. exact (MK_COMB (@lem4110099 _48296) (@lem4110097 _48296)). Qed.
Lemma lem4110101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4110102 (_48296 : int) : (term153 _48296) = (term302 _48296).
Proof. exact (MK_COMB (@lem4110101) (@lem4109754 _48296)). Qed.
Lemma lem4110103 (_48296 : int) : (term154 _48296) = (term303 _48296).
Proof. exact (MK_COMB (@lem4110102 _48296) (@lem4110100 _48296)). Qed.
Lemma lem4110104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110105 (_48296 : int) : (term155 _48296) = (term304 _48296).
Proof. exact (MK_COMB (@lem4110104) (@lem4109623 _48296)). Qed.
Lemma lem4110106 (_48296 : int) : (term156 _48296) = (term305 _48296).
Proof. exact (MK_COMB (@lem4110105 _48296) (@lem4110103 _48296)). Qed.
Lemma lem4110107 (_48296 : int) : (term159 _48296) = (term306 _48296).
Proof. exact (@lem1988287 term111 (real_of_int _48296)). Qed.
Lemma lem4110113 (_48296 : int) : (term307 _48296) = (term308 _48296).
Proof. exact (@lem1982792 term111 (real_of_int _48296)). Qed.
Lemma lem4110118 (_48296 : int) : (term308 _48296) = (term309 _48296).
Proof. exact (@lem1982761 (term281 _48296) term111). Qed.
Lemma lem4110120 (_48296 : int) : (term307 _48296) = (term309 _48296).
Proof. exact (TRANS (@lem4110113 _48296) (@lem4110118 _48296)). Qed.
Lemma lem4110121 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4110122 (_48296 : int) : (term310 _48296) = (term311 _48296).
Proof. exact (MK_COMB (@lem4110121) (@lem4110120 _48296)). Qed.
Lemma lem4110123 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4110124 (_48296 : int) : (term306 _48296) = (term312 _48296).
Proof. exact (MK_COMB (@lem4110122 _48296) (@lem4110123)). Qed.
Lemma lem4110125 (_48296 : int) : (term159 _48296) = (term312 _48296).
Proof. exact (TRANS (@lem4110107 _48296) (@lem4110124 _48296)). Qed.
Lemma lem4110126 (_48296 : int) : ((real_of_int _48296) = term97) = ((term172 _48296) = term97).
Proof. exact (@lem1988293 (real_of_int _48296) term97). Qed.
Lemma lem4110132 (_48296 : int) : (term172 _48296) = (term173 _48296).
Proof. exact (@lem1982792 (real_of_int _48296) term97). Qed.
Lemma lem4110134 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4110135 : term97 = term175.
Proof. exact (@lem4110134 (NUMERAL 0)). Qed.
Lemma lem4110137 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4110138 : term178 = term179.
Proof. exact (@lem4110137 term20). Qed.
Lemma lem4110139 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4110140 : term180 = term181.
Proof. exact (MK_COMB (@lem4110139) (@lem4110138)). Qed.
Lemma lem4110141 : term182 = term183.
Proof. exact (MK_COMB (@lem4110140) (@lem4110135)). Qed.
Lemma lem4110142 : term183 = term184.
Proof. exact (@lem1981613 term178 term97 term111 term111). Qed.
Lemma lem4110144 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4110145 : term187 = term188.
Proof. exact (@lem4110144 term20 term20). Qed.
Lemma lem4110146 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110147 : term190 = term20.
Proof. exact (EQ_MP (@lem4110146) (@lem940073)). Qed.
Lemma lem4110148 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110149 : term188 = term111.
Proof. exact (MK_COMB (@lem4110148) (@lem4110147)). Qed.
Lemma lem4110150 : term187 = term111.
Proof. exact (TRANS (@lem4110145) (@lem4110149)). Qed.
Lemma lem4110152 (x : nat) : (term191 x) = term97.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem4110153 : term182 = term97.
Proof. exact (@lem4110152 term20). Qed.
Lemma lem4110154 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4110155 : term192 = term193.
Proof. exact (MK_COMB (@lem4110154) (@lem4110153)). Qed.
Lemma lem4110156 : term184 = term175.
Proof. exact (MK_COMB (@lem4110155) (@lem4110150)). Qed.
Lemma lem4110157 : term183 = term175.
Proof. exact (TRANS (@lem4110142) (@lem4110156)). Qed.
Lemma lem4110158 : term182 = term175.
Proof. exact (TRANS (@lem4110141) (@lem4110157)). Qed.
Lemma lem4110160 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4110161 : term175 = term97.
Proof. exact (@lem4110160 term97). Qed.
Lemma lem4110162 : term182 = term97.
Proof. exact (TRANS (@lem4110158) (@lem4110161)). Qed.
Lemma lem4110163 (_48296 : int) : (term126 _48296) = (term126 _48296).
Proof. exact (eq_refl (term126 _48296)). Qed.
Lemma lem4110164 (_48296 : int) : (term173 _48296) = (term195 _48296).
Proof. exact (MK_COMB (@lem4110163 _48296) (@lem4110162)). Qed.
Lemma lem4110165 (_48296 : int) : (term195 _48296) = (real_of_int _48296).
Proof. exact (@lem1982723 (real_of_int _48296)). Qed.
Lemma lem4110166 (_48296 : int) : (term173 _48296) = (real_of_int _48296).
Proof. exact (TRANS (@lem4110164 _48296) (@lem4110165 _48296)). Qed.
Lemma lem4110168 (_48296 : int) : (term172 _48296) = (real_of_int _48296).
Proof. exact (TRANS (@lem4110132 _48296) (@lem4110166 _48296)). Qed.
Lemma lem4110169 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem4110170 (_48296 : int) : (term313 _48296) = (term160 _48296).
Proof. exact (MK_COMB (@lem4110169) (@lem4110168 _48296)). Qed.
Lemma lem4110171 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4110172 (_48296 : int) : ((term172 _48296) = term97) = ((real_of_int _48296) = term97).
Proof. exact (MK_COMB (@lem4110170 _48296) (@lem4110171)). Qed.
Lemma lem4110173 (_48296 : int) : ((real_of_int _48296) = term97) = ((real_of_int _48296) = term97).
Proof. exact (TRANS (@lem4110126 _48296) (@lem4110172 _48296)). Qed.
Lemma lem4110174 (_48296 : int) : ((real_of_int _48296) = term111) = ((term268 _48296) = term97).
Proof. exact (@lem1988293 (real_of_int _48296) term111). Qed.
Lemma lem4110180 (_48296 : int) : (term268 _48296) = (term269 _48296).
Proof. exact (@lem1982792 (real_of_int _48296) term111). Qed.
Lemma lem4110182 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4110183 : term111 = term200.
Proof. exact (@lem4110182 term20). Qed.
Lemma lem4110185 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4110186 : term178 = term179.
Proof. exact (@lem4110185 term20). Qed.
Lemma lem4110187 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4110188 : term180 = term181.
Proof. exact (MK_COMB (@lem4110187) (@lem4110186)). Qed.
Lemma lem4110189 : term254 = term255.
Proof. exact (MK_COMB (@lem4110188) (@lem4110183)). Qed.
Lemma lem4110190 : term255 = term256.
Proof. exact (@lem1981613 term178 term111 term111 term111). Qed.
Lemma lem4110192 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4110193 : term187 = term188.
Proof. exact (@lem4110192 term20 term20). Qed.
Lemma lem4110194 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110195 : term190 = term20.
Proof. exact (EQ_MP (@lem4110194) (@lem940073)). Qed.
Lemma lem4110196 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110197 : term188 = term111.
Proof. exact (MK_COMB (@lem4110196) (@lem4110195)). Qed.
Lemma lem4110198 : term187 = term111.
Proof. exact (TRANS (@lem4110193) (@lem4110197)). Qed.
Lemma lem4110200 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4110201 : term254 = term257.
Proof. exact (@lem4110200 term20 term20). Qed.
Lemma lem4110202 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110203 : term190 = term20.
Proof. exact (EQ_MP (@lem4110202) (@lem940073)). Qed.
Lemma lem4110204 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110205 : term188 = term111.
Proof. exact (MK_COMB (@lem4110204) (@lem4110203)). Qed.
Lemma lem4110206 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4110207 : term257 = term178.
Proof. exact (MK_COMB (@lem4110206) (@lem4110205)). Qed.
Lemma lem4110208 : term254 = term178.
Proof. exact (TRANS (@lem4110201) (@lem4110207)). Qed.
Lemma lem4110209 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4110210 : term258 = term259.
Proof. exact (MK_COMB (@lem4110209) (@lem4110208)). Qed.
Lemma lem4110211 : term256 = term179.
Proof. exact (MK_COMB (@lem4110210) (@lem4110198)). Qed.
Lemma lem4110212 : term255 = term179.
Proof. exact (TRANS (@lem4110190) (@lem4110211)). Qed.
Lemma lem4110213 : term254 = term179.
Proof. exact (TRANS (@lem4110189) (@lem4110212)). Qed.
Lemma lem4110215 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4110216 : term179 = term178.
Proof. exact (@lem4110215 term178). Qed.
Lemma lem4110217 : term254 = term178.
Proof. exact (TRANS (@lem4110213) (@lem4110216)). Qed.
Lemma lem4110218 (_48296 : int) : (term126 _48296) = (term126 _48296).
Proof. exact (eq_refl (term126 _48296)). Qed.
Lemma lem4110221 (_48296 : int) : (term269 _48296) = (term270 _48296).
Proof. exact (MK_COMB (@lem4110218 _48296) (@lem4110217)). Qed.
Lemma lem4110223 (_48296 : int) : (term268 _48296) = (term270 _48296).
Proof. exact (TRANS (@lem4110180 _48296) (@lem4110221 _48296)). Qed.
Lemma lem4110224 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem4110225 (_48296 : int) : (term314 _48296) = (term315 _48296).
Proof. exact (MK_COMB (@lem4110224) (@lem4110223 _48296)). Qed.
Lemma lem4110226 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4110227 (_48296 : int) : ((term268 _48296) = term97) = ((term270 _48296) = term97).
Proof. exact (MK_COMB (@lem4110225 _48296) (@lem4110226)). Qed.
Lemma lem4110228 (_48296 : int) : ((real_of_int _48296) = term111) = ((term270 _48296) = term97).
Proof. exact (TRANS (@lem4110174 _48296) (@lem4110227 _48296)). Qed.
Lemma lem4110229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110230 (_48296 : int) : (term161 _48296) = (term161 _48296).
Proof. exact (MK_COMB (@lem4110229) (@lem4110173 _48296)). Qed.
Lemma lem4110231 (_48296 : int) : (term162 _48296) = (term316 _48296).
Proof. exact (MK_COMB (@lem4110230 _48296) (@lem4110228 _48296)). Qed.
Lemma lem4110232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110233 (_48296 : int) : (term163 _48296) = (term317 _48296).
Proof. exact (MK_COMB (@lem4110232) (@lem4110125 _48296)). Qed.
Lemma lem4110234 (_48296 : int) : (term164 _48296) = (term318 _48296).
Proof. exact (MK_COMB (@lem4110233 _48296) (@lem4110231 _48296)). Qed.
Lemma lem4110235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4110236 (_48296 : int) : (term165 _48296) = (term319 _48296).
Proof. exact (MK_COMB (@lem4110235) (@lem4110106 _48296)). Qed.
Lemma lem4110237 (_48296 : int) : (term166 _48296) = (term320 _48296).
Proof. exact (MK_COMB (@lem4110236 _48296) (@lem4110234 _48296)). Qed.
Lemma lem4110238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4110239 (_48296 : int) : (term167 _48296) = (term321 _48296).
Proof. exact (MK_COMB (@lem4110238) (@lem4109450 _48296)). Qed.
Lemma lem4110240 (_48296 : int) : (term168 _48296) = (term322 _48296).
Proof. exact (MK_COMB (@lem4110239 _48296) (@lem4110237 _48296)). Qed.
Lemma lem4110247 (_48296 : int) : (term170 _48296) = (term322 _48296).
Proof. exact (TRANS (@lem4109402 _48296) (@lem4110240 _48296)). Qed.
Lemma lem4110256 (_48296 : int) : (term318 _48296) = (term318 _48296).
Proof. exact (eq_refl (term318 _48296)). Qed.
Lemma lem4110270 (_48296 : int) : (term303 _48296) = (term323 _48296).
Proof. exact (@lem19158 (term299 _48296) (term275 _48296) (term248 _48296)). Qed.
Lemma lem4110277 (_48296 : int) : (term324 _48296) = (term325 _48296).
Proof. exact (@lem19367 (term265 _48296) (term273 _48296) (term248 _48296)). Qed.
Lemma lem4110284 (_48296 : int) : (term326 _48296) = (term327 _48296).
Proof. exact (@lem19367 (term265 _48296) (term273 _48296) (term299 _48296)). Qed.
Lemma lem4110285 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110286 (_48296 : int) : (term328 _48296) = (term329 _48296).
Proof. exact (MK_COMB (@lem4110285) (@lem4110284 _48296)). Qed.
Lemma lem4110287 (_48296 : int) : (term323 _48296) = (term330 _48296).
Proof. exact (MK_COMB (@lem4110286 _48296) (@lem4110277 _48296)). Qed.
Lemma lem4110289 (_48296 : int) : (term303 _48296) = (term330 _48296).
Proof. exact (TRANS (@lem4110270 _48296) (@lem4110287 _48296)). Qed.
Lemma lem4110292 (_48296 : int) : (term304 _48296) = (term304 _48296).
Proof. exact (eq_refl (term304 _48296)). Qed.
Lemma lem4110293 (_48296 : int) : (term305 _48296) = (term331 _48296).
Proof. exact (MK_COMB (@lem4110292 _48296) (@lem4110289 _48296)). Qed.
Lemma lem4110294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4110295 (_48296 : int) : (term319 _48296) = (term332 _48296).
Proof. exact (MK_COMB (@lem4110294) (@lem4110293 _48296)). Qed.
Lemma lem4110296 (_48296 : int) : (term320 _48296) = (term333 _48296).
Proof. exact (MK_COMB (@lem4110295 _48296) (@lem4110256 _48296)). Qed.
Lemma lem4110297 (_48296 : int) : (term333 _48296) = (term334 _48296).
Proof. exact (@lem19158 (term312 _48296) (term331 _48296) (term316 _48296)). Qed.
Lemma lem4110298 (_48296 : int) : (term335 _48296) = (term336 _48296).
Proof. exact (@lem19158 ((real_of_int _48296) = term97) (term331 _48296) ((term270 _48296) = term97)). Qed.
Lemma lem4110299 (_48296 : int) : (term337 _48296) = (term338 _48296).
Proof. exact (@lem19367 (term248 _48296) (term330 _48296) ((term270 _48296) = term97)). Qed.
Lemma lem4110300 (_48296 : int) : (term339 _48296) = (term340 _48296).
Proof. exact (@lem19367 (term327 _48296) (term325 _48296) ((term270 _48296) = term97)). Qed.
Lemma lem4110307 (_48296 : int) : (term341 _48296) = (term342 _48296).
Proof. exact (@lem19367 (term343 _48296) (term344 _48296) ((term270 _48296) = term97)). Qed.
Lemma lem4110314 (_48296 : int) : (term345 _48296) = (term346 _48296).
Proof. exact (@lem19367 (term347 _48296) (term348 _48296) ((term270 _48296) = term97)). Qed.
Lemma lem4110315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110316 (_48296 : int) : (term349 _48296) = (term350 _48296).
Proof. exact (MK_COMB (@lem4110315) (@lem4110314 _48296)). Qed.
Lemma lem4110317 (_48296 : int) : (term340 _48296) = (term351 _48296).
Proof. exact (MK_COMB (@lem4110316 _48296) (@lem4110307 _48296)). Qed.
Lemma lem4110318 (_48296 : int) : (term339 _48296) = (term351 _48296).
Proof. exact (TRANS (@lem4110300 _48296) (@lem4110317 _48296)). Qed.
Lemma lem4110321 (_48296 : int) : (term352 _48296) = (term352 _48296).
Proof. exact (eq_refl (term352 _48296)). Qed.
Lemma lem4110322 (_48296 : int) : (term338 _48296) = (term353 _48296).
Proof. exact (MK_COMB (@lem4110321 _48296) (@lem4110318 _48296)). Qed.
Lemma lem4110323 (_48296 : int) : (term337 _48296) = (term353 _48296).
Proof. exact (TRANS (@lem4110299 _48296) (@lem4110322 _48296)). Qed.
Lemma lem4110324 (_48296 : int) : (term354 _48296) = (term355 _48296).
Proof. exact (@lem19367 (term248 _48296) (term330 _48296) ((real_of_int _48296) = term97)). Qed.
Lemma lem4110325 (_48296 : int) : (term356 _48296) = (term357 _48296).
Proof. exact (@lem19367 (term327 _48296) (term325 _48296) ((real_of_int _48296) = term97)). Qed.
Lemma lem4110332 (_48296 : int) : (term358 _48296) = (term359 _48296).
Proof. exact (@lem19367 (term343 _48296) (term344 _48296) ((real_of_int _48296) = term97)). Qed.
Lemma lem4110339 (_48296 : int) : (term360 _48296) = (term361 _48296).
Proof. exact (@lem19367 (term347 _48296) (term348 _48296) ((real_of_int _48296) = term97)). Qed.
Lemma lem4110340 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110341 (_48296 : int) : (term362 _48296) = (term363 _48296).
Proof. exact (MK_COMB (@lem4110340) (@lem4110339 _48296)). Qed.
Lemma lem4110342 (_48296 : int) : (term357 _48296) = (term364 _48296).
Proof. exact (MK_COMB (@lem4110341 _48296) (@lem4110332 _48296)). Qed.
Lemma lem4110343 (_48296 : int) : (term356 _48296) = (term364 _48296).
Proof. exact (TRANS (@lem4110325 _48296) (@lem4110342 _48296)). Qed.
Lemma lem4110346 (_48296 : int) : (term365 _48296) = (term365 _48296).
Proof. exact (eq_refl (term365 _48296)). Qed.
Lemma lem4110347 (_48296 : int) : (term355 _48296) = (term366 _48296).
Proof. exact (MK_COMB (@lem4110346 _48296) (@lem4110343 _48296)). Qed.
Lemma lem4110348 (_48296 : int) : (term354 _48296) = (term366 _48296).
Proof. exact (TRANS (@lem4110324 _48296) (@lem4110347 _48296)). Qed.
Lemma lem4110349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110350 (_48296 : int) : (term367 _48296) = (term368 _48296).
Proof. exact (MK_COMB (@lem4110349) (@lem4110348 _48296)). Qed.
Lemma lem4110351 (_48296 : int) : (term336 _48296) = (term369 _48296).
Proof. exact (MK_COMB (@lem4110350 _48296) (@lem4110323 _48296)). Qed.
Lemma lem4110352 (_48296 : int) : (term335 _48296) = (term369 _48296).
Proof. exact (TRANS (@lem4110298 _48296) (@lem4110351 _48296)). Qed.
Lemma lem4110353 (_48296 : int) : (term370 _48296) = (term371 _48296).
Proof. exact (@lem19367 (term248 _48296) (term330 _48296) (term312 _48296)). Qed.
Lemma lem4110354 (_48296 : int) : (term372 _48296) = (term373 _48296).
Proof. exact (@lem19367 (term327 _48296) (term325 _48296) (term312 _48296)). Qed.
Lemma lem4110361 (_48296 : int) : (term374 _48296) = (term375 _48296).
Proof. exact (@lem19367 (term343 _48296) (term344 _48296) (term312 _48296)). Qed.
Lemma lem4110368 (_48296 : int) : (term376 _48296) = (term377 _48296).
Proof. exact (@lem19367 (term347 _48296) (term348 _48296) (term312 _48296)). Qed.
Lemma lem4110369 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110370 (_48296 : int) : (term378 _48296) = (term379 _48296).
Proof. exact (MK_COMB (@lem4110369) (@lem4110368 _48296)). Qed.
Lemma lem4110371 (_48296 : int) : (term373 _48296) = (term380 _48296).
Proof. exact (MK_COMB (@lem4110370 _48296) (@lem4110361 _48296)). Qed.
Lemma lem4110372 (_48296 : int) : (term372 _48296) = (term380 _48296).
Proof. exact (TRANS (@lem4110354 _48296) (@lem4110371 _48296)). Qed.
Lemma lem4110375 (_48296 : int) : (term381 _48296) = (term381 _48296).
Proof. exact (eq_refl (term381 _48296)). Qed.
Lemma lem4110376 (_48296 : int) : (term371 _48296) = (term382 _48296).
Proof. exact (MK_COMB (@lem4110375 _48296) (@lem4110372 _48296)). Qed.
Lemma lem4110377 (_48296 : int) : (term370 _48296) = (term382 _48296).
Proof. exact (TRANS (@lem4110353 _48296) (@lem4110376 _48296)). Qed.
Lemma lem4110378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110379 (_48296 : int) : (term383 _48296) = (term384 _48296).
Proof. exact (MK_COMB (@lem4110378) (@lem4110377 _48296)). Qed.
Lemma lem4110380 (_48296 : int) : (term334 _48296) = (term385 _48296).
Proof. exact (MK_COMB (@lem4110379 _48296) (@lem4110352 _48296)). Qed.
Lemma lem4110381 (_48296 : int) : (term333 _48296) = (term385 _48296).
Proof. exact (TRANS (@lem4110297 _48296) (@lem4110380 _48296)). Qed.
Lemma lem4110382 (_48296 : int) : (term320 _48296) = (term385 _48296).
Proof. exact (TRANS (@lem4110296 _48296) (@lem4110381 _48296)). Qed.
Lemma lem4110385 (_48296 : int) : (term321 _48296) = (term321 _48296).
Proof. exact (eq_refl (term321 _48296)). Qed.
Lemma lem4110386 (_48296 : int) : (term322 _48296) = (term386 _48296).
Proof. exact (MK_COMB (@lem4110385 _48296) (@lem4110382 _48296)). Qed.
Lemma lem4110387 (_48296 : int) : (term386 _48296) = (term387 _48296).
Proof. exact (@lem19158 (term382 _48296) (term198 _48296) (term369 _48296)). Qed.
Lemma lem4110388 (_48296 : int) : (term388 _48296) = (term389 _48296).
Proof. exact (@lem19158 (term366 _48296) (term198 _48296) (term353 _48296)). Qed.
Lemma lem4110389 (_48296 : int) : (term390 _48296) = (term391 _48296).
Proof. exact (@lem19158 (term392 _48296) (term198 _48296) (term351 _48296)). Qed.
Lemma lem4110390 (_48296 : int) : (term393 _48296) = (term394 _48296).
Proof. exact (@lem19158 (term346 _48296) (term198 _48296) (term342 _48296)). Qed.
Lemma lem4110397 (_48296 : int) : (term395 _48296) = (term396 _48296).
Proof. exact (@lem19158 (term397 _48296) (term198 _48296) (term398 _48296)). Qed.
Lemma lem4110404 (_48296 : int) : (term399 _48296) = (term400 _48296).
Proof. exact (@lem19158 (term401 _48296) (term198 _48296) (term402 _48296)). Qed.
Lemma lem4110405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110406 (_48296 : int) : (term403 _48296) = (term404 _48296).
Proof. exact (MK_COMB (@lem4110405) (@lem4110404 _48296)). Qed.
Lemma lem4110407 (_48296 : int) : (term394 _48296) = (term405 _48296).
Proof. exact (MK_COMB (@lem4110406 _48296) (@lem4110397 _48296)). Qed.
Lemma lem4110408 (_48296 : int) : (term393 _48296) = (term405 _48296).
Proof. exact (TRANS (@lem4110390 _48296) (@lem4110407 _48296)). Qed.
Lemma lem4110411 (_48296 : int) : (term406 _48296) = (term406 _48296).
Proof. exact (eq_refl (term406 _48296)). Qed.
Lemma lem4110412 (_48296 : int) : (term391 _48296) = (term407 _48296).
Proof. exact (MK_COMB (@lem4110411 _48296) (@lem4110408 _48296)). Qed.
Lemma lem4110413 (_48296 : int) : (term390 _48296) = (term407 _48296).
Proof. exact (TRANS (@lem4110389 _48296) (@lem4110412 _48296)). Qed.
Lemma lem4110414 (_48296 : int) : (term408 _48296) = (term409 _48296).
Proof. exact (@lem19158 (term410 _48296) (term198 _48296) (term364 _48296)). Qed.
Lemma lem4110415 (_48296 : int) : (term411 _48296) = (term412 _48296).
Proof. exact (@lem19158 (term361 _48296) (term198 _48296) (term359 _48296)). Qed.
Lemma lem4110422 (_48296 : int) : (term413 _48296) = (term414 _48296).
Proof. exact (@lem19158 (term415 _48296) (term198 _48296) (term416 _48296)). Qed.
Lemma lem4110429 (_48296 : int) : (term417 _48296) = (term418 _48296).
Proof. exact (@lem19158 (term419 _48296) (term198 _48296) (term420 _48296)). Qed.
Lemma lem4110430 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110431 (_48296 : int) : (term421 _48296) = (term422 _48296).
Proof. exact (MK_COMB (@lem4110430) (@lem4110429 _48296)). Qed.
Lemma lem4110432 (_48296 : int) : (term412 _48296) = (term423 _48296).
Proof. exact (MK_COMB (@lem4110431 _48296) (@lem4110422 _48296)). Qed.
Lemma lem4110433 (_48296 : int) : (term411 _48296) = (term423 _48296).
Proof. exact (TRANS (@lem4110415 _48296) (@lem4110432 _48296)). Qed.
Lemma lem4110436 (_48296 : int) : (term424 _48296) = (term424 _48296).
Proof. exact (eq_refl (term424 _48296)). Qed.
Lemma lem4110437 (_48296 : int) : (term409 _48296) = (term425 _48296).
Proof. exact (MK_COMB (@lem4110436 _48296) (@lem4110433 _48296)). Qed.
Lemma lem4110438 (_48296 : int) : (term408 _48296) = (term425 _48296).
Proof. exact (TRANS (@lem4110414 _48296) (@lem4110437 _48296)). Qed.
Lemma lem4110439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110440 (_48296 : int) : (term426 _48296) = (term427 _48296).
Proof. exact (MK_COMB (@lem4110439) (@lem4110438 _48296)). Qed.
Lemma lem4110441 (_48296 : int) : (term389 _48296) = (term428 _48296).
Proof. exact (MK_COMB (@lem4110440 _48296) (@lem4110413 _48296)). Qed.
Lemma lem4110442 (_48296 : int) : (term388 _48296) = (term428 _48296).
Proof. exact (TRANS (@lem4110388 _48296) (@lem4110441 _48296)). Qed.
Lemma lem4110443 (_48296 : int) : (term429 _48296) = (term430 _48296).
Proof. exact (@lem19158 (term431 _48296) (term198 _48296) (term380 _48296)). Qed.
Lemma lem4110444 (_48296 : int) : (term432 _48296) = (term433 _48296).
Proof. exact (@lem19158 (term377 _48296) (term198 _48296) (term375 _48296)). Qed.
Lemma lem4110451 (_48296 : int) : (term434 _48296) = (term435 _48296).
Proof. exact (@lem19158 (term436 _48296) (term198 _48296) (term437 _48296)). Qed.
Lemma lem4110458 (_48296 : int) : (term438 _48296) = (term439 _48296).
Proof. exact (@lem19158 (term440 _48296) (term198 _48296) (term441 _48296)). Qed.
Lemma lem4110459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110460 (_48296 : int) : (term442 _48296) = (term443 _48296).
Proof. exact (MK_COMB (@lem4110459) (@lem4110458 _48296)). Qed.
Lemma lem4110461 (_48296 : int) : (term433 _48296) = (term444 _48296).
Proof. exact (MK_COMB (@lem4110460 _48296) (@lem4110451 _48296)). Qed.
Lemma lem4110462 (_48296 : int) : (term432 _48296) = (term444 _48296).
Proof. exact (TRANS (@lem4110444 _48296) (@lem4110461 _48296)). Qed.
Lemma lem4110465 (_48296 : int) : (term445 _48296) = (term445 _48296).
Proof. exact (eq_refl (term445 _48296)). Qed.
Lemma lem4110466 (_48296 : int) : (term430 _48296) = (term446 _48296).
Proof. exact (MK_COMB (@lem4110465 _48296) (@lem4110462 _48296)). Qed.
Lemma lem4110467 (_48296 : int) : (term429 _48296) = (term446 _48296).
Proof. exact (TRANS (@lem4110443 _48296) (@lem4110466 _48296)). Qed.
Lemma lem4110468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4110469 (_48296 : int) : (term447 _48296) = (term448 _48296).
Proof. exact (MK_COMB (@lem4110468) (@lem4110467 _48296)). Qed.
Lemma lem4110470 (_48296 : int) : (term387 _48296) = (term449 _48296).
Proof. exact (MK_COMB (@lem4110469 _48296) (@lem4110442 _48296)). Qed.
Lemma lem4110471 (_48296 : int) : (term386 _48296) = (term449 _48296).
Proof. exact (TRANS (@lem4110387 _48296) (@lem4110470 _48296)). Qed.
Lemma lem4110472 (_48296 : int) : (term322 _48296) = (term449 _48296).
Proof. exact (TRANS (@lem4110386 _48296) (@lem4110471 _48296)). Qed.
Lemma lem4110473 (_48296 : int) : (term170 _48296) = (term449 _48296).
Proof. exact (TRANS (@lem4110247 _48296) (@lem4110472 _48296)). Qed.
Lemma lem4110561 (_48296 : int) (h1 : term449 _48296) : term449 _48296.
Proof. exact (h1). Qed.
Lemma lem4110562 (_48296 : int) (h1 : term446 _48296) : term446 _48296.
Proof. exact (h1). Qed.
Lemma lem4110563 (_48296 : int) (h1 : term450 _48296) : term450 _48296.
Proof. exact (h1). Qed.
Lemma lem4110564 (_48296 : int) (h1 : term450 _48296) : term431 _48296.
Proof. exact (proj2 (@lem4110563 _48296 h1)). Qed.
Lemma lem4110566 (_48296 : int) (h1 : term450 _48296) : term312 _48296.
Proof. exact (proj2 (@lem4110564 _48296 h1)). Qed.
Lemma lem4110567 (_48296 : int) (h1 : term450 _48296) : term248 _48296.
Proof. exact (proj1 (@lem4110564 _48296 h1)). Qed.
Lemma lem4110569 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4110570 : term451 = term206.
Proof. exact (@lem4110569 term97 term111). Qed.
Lemma lem4110572 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4110573 : term111 = term200.
Proof. exact (@lem4110572 term20). Qed.
Lemma lem4110575 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4110576 : term97 = term175.
Proof. exact (@lem4110575 (NUMERAL 0)). Qed.
Lemma lem4110577 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4110578 : term452 = term453.
Proof. exact (MK_COMB (@lem4110577) (@lem4110576)). Qed.
Lemma lem4110579 : term206 = term454.
Proof. exact (MK_COMB (@lem4110578) (@lem4110573)). Qed.
Lemma lem4110580 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4110582 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110583 : term206 = term207.
Proof. exact (@lem4110582 (NUMERAL 0) term20). Qed.
Lemma lem4110584 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110585 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110586 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110585 h1) (fun h1 : term207 = True => @lem4110584)). Qed.
Lemma lem4110587 : term207 = True.
Proof. exact (EQ_MP (@lem4110586) (@lem4110584)). Qed.
Lemma lem4110588 : term206 = True.
Proof. exact (TRANS (@lem4110583) (@lem4110587)). Qed.
Lemma lem4110589 : True = term206.
Proof. exact (SYM (@lem4110588)). Qed.
Lemma lem4110590 : term206.
Proof. exact (EQ_MP (@lem4110589) (@lem0)). Qed.
Lemma lem4110591 : term456.
Proof. exact (@lem4110580 (@lem4110590)). Qed.
Lemma lem4110593 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110594 : term206 = term207.
Proof. exact (@lem4110593 (NUMERAL 0) term20). Qed.
Lemma lem4110595 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110596 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110597 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110596 h1) (fun h1 : term207 = True => @lem4110595)). Qed.
Lemma lem4110598 : term207 = True.
Proof. exact (EQ_MP (@lem4110597) (@lem4110595)). Qed.
Lemma lem4110599 : term206 = True.
Proof. exact (TRANS (@lem4110594) (@lem4110598)). Qed.
Lemma lem4110600 : True = term206.
Proof. exact (SYM (@lem4110599)). Qed.
Lemma lem4110601 : term206.
Proof. exact (EQ_MP (@lem4110600) (@lem0)). Qed.
Lemma lem4110602 : term454 = term457.
Proof. exact (@lem4110591 (@lem4110601)). Qed.
Lemma lem4110604 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4110605 : term187 = term188.
Proof. exact (@lem4110604 term20 term20). Qed.
Lemma lem4110606 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110607 : term190 = term20.
Proof. exact (EQ_MP (@lem4110606) (@lem940073)). Qed.
Lemma lem4110608 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110609 : term188 = term111.
Proof. exact (MK_COMB (@lem4110608) (@lem4110607)). Qed.
Lemma lem4110610 : term187 = term111.
Proof. exact (TRANS (@lem4110605) (@lem4110609)). Qed.
Lemma lem4110612 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4110613 : term293 = term97.
Proof. exact (@lem4110612 term20). Qed.
Lemma lem4110614 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4110615 : term458 = term452.
Proof. exact (MK_COMB (@lem4110614) (@lem4110613)). Qed.
Lemma lem4110616 : term457 = term206.
Proof. exact (MK_COMB (@lem4110615) (@lem4110610)). Qed.
Lemma lem4110618 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110619 : term206 = term207.
Proof. exact (@lem4110618 (NUMERAL 0) term20). Qed.
Lemma lem4110620 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110621 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110622 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110621 h1) (fun h1 : term207 = True => @lem4110620)). Qed.
Lemma lem4110623 : term207 = True.
Proof. exact (EQ_MP (@lem4110622) (@lem4110620)). Qed.
Lemma lem4110624 : term206 = True.
Proof. exact (TRANS (@lem4110619) (@lem4110623)). Qed.
Lemma lem4110625 : term457 = True.
Proof. exact (TRANS (@lem4110616) (@lem4110624)). Qed.
Lemma lem4110626 : term454 = True.
Proof. exact (TRANS (@lem4110602) (@lem4110625)). Qed.
Lemma lem4110627 : term206 = True.
Proof. exact (TRANS (@lem4110579) (@lem4110626)). Qed.
Lemma lem4110628 : term451 = True.
Proof. exact (TRANS (@lem4110570) (@lem4110627)). Qed.
Lemma lem4110629 : True = term451.
Proof. exact (SYM (@lem4110628)). Qed.
Lemma lem4110630 : term451.
Proof. exact (EQ_MP (@lem4110629) (@lem0)). Qed.
Lemma lem4110631 (_48296 : int) (h1 : term450 _48296) : term459 _48296.
Proof. exact (conj (@lem4110630) (@lem4110567 _48296 h1)). Qed.
Lemma lem4110633 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4110634 (_48296 : int) : term461 _48296.
Proof. exact (@lem4110633 term111 (term245 _48296)). Qed.
Lemma lem4110635 (_48296 : int) (h1 : term450 _48296) : term462 _48296.
Proof. exact (@lem4110634 _48296 (@lem4110631 _48296 h1)). Qed.
Lemma lem4110636 (_48296 : int) : (term463 _48296) = (term245 _48296).
Proof. exact (@lem1982733 (term245 _48296)). Qed.
Lemma lem4110637 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4110638 (_48296 : int) : (term464 _48296) = (term247 _48296).
Proof. exact (MK_COMB (@lem4110637) (@lem4110636 _48296)). Qed.
Lemma lem4110639 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4110640 (_48296 : int) : (term462 _48296) = (term248 _48296).
Proof. exact (MK_COMB (@lem4110638 _48296) (@lem4110639)). Qed.
Lemma lem4110641 (_48296 : int) (h1 : term450 _48296) : term248 _48296.
Proof. exact (EQ_MP (@lem4110640 _48296) (@lem4110635 _48296 h1)). Qed.
Lemma lem4110643 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4110644 : term451 = term206.
Proof. exact (@lem4110643 term97 term111). Qed.
Lemma lem4110646 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4110647 : term111 = term200.
Proof. exact (@lem4110646 term20). Qed.
Lemma lem4110649 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4110650 : term97 = term175.
Proof. exact (@lem4110649 (NUMERAL 0)). Qed.
Lemma lem4110651 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4110652 : term452 = term453.
Proof. exact (MK_COMB (@lem4110651) (@lem4110650)). Qed.
Lemma lem4110653 : term206 = term454.
Proof. exact (MK_COMB (@lem4110652) (@lem4110647)). Qed.
Lemma lem4110654 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4110656 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110657 : term206 = term207.
Proof. exact (@lem4110656 (NUMERAL 0) term20). Qed.
Lemma lem4110658 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110659 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110660 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110659 h1) (fun h1 : term207 = True => @lem4110658)). Qed.
Lemma lem4110661 : term207 = True.
Proof. exact (EQ_MP (@lem4110660) (@lem4110658)). Qed.
Lemma lem4110662 : term206 = True.
Proof. exact (TRANS (@lem4110657) (@lem4110661)). Qed.
Lemma lem4110663 : True = term206.
Proof. exact (SYM (@lem4110662)). Qed.
Lemma lem4110664 : term206.
Proof. exact (EQ_MP (@lem4110663) (@lem0)). Qed.
Lemma lem4110665 : term456.
Proof. exact (@lem4110654 (@lem4110664)). Qed.
Lemma lem4110667 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110668 : term206 = term207.
Proof. exact (@lem4110667 (NUMERAL 0) term20). Qed.
Lemma lem4110669 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110670 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110671 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110670 h1) (fun h1 : term207 = True => @lem4110669)). Qed.
Lemma lem4110672 : term207 = True.
Proof. exact (EQ_MP (@lem4110671) (@lem4110669)). Qed.
Lemma lem4110673 : term206 = True.
Proof. exact (TRANS (@lem4110668) (@lem4110672)). Qed.
Lemma lem4110674 : True = term206.
Proof. exact (SYM (@lem4110673)). Qed.
Lemma lem4110675 : term206.
Proof. exact (EQ_MP (@lem4110674) (@lem0)). Qed.
Lemma lem4110676 : term454 = term457.
Proof. exact (@lem4110665 (@lem4110675)). Qed.
Lemma lem4110678 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4110679 : term187 = term188.
Proof. exact (@lem4110678 term20 term20). Qed.
Lemma lem4110680 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110681 : term190 = term20.
Proof. exact (EQ_MP (@lem4110680) (@lem940073)). Qed.
Lemma lem4110682 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110683 : term188 = term111.
Proof. exact (MK_COMB (@lem4110682) (@lem4110681)). Qed.
Lemma lem4110684 : term187 = term111.
Proof. exact (TRANS (@lem4110679) (@lem4110683)). Qed.
Lemma lem4110686 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4110687 : term293 = term97.
Proof. exact (@lem4110686 term20). Qed.
Lemma lem4110688 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4110689 : term458 = term452.
Proof. exact (MK_COMB (@lem4110688) (@lem4110687)). Qed.
Lemma lem4110690 : term457 = term206.
Proof. exact (MK_COMB (@lem4110689) (@lem4110684)). Qed.
Lemma lem4110692 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110693 : term206 = term207.
Proof. exact (@lem4110692 (NUMERAL 0) term20). Qed.
Lemma lem4110694 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110695 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110696 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110695 h1) (fun h1 : term207 = True => @lem4110694)). Qed.
Lemma lem4110697 : term207 = True.
Proof. exact (EQ_MP (@lem4110696) (@lem4110694)). Qed.
Lemma lem4110698 : term206 = True.
Proof. exact (TRANS (@lem4110693) (@lem4110697)). Qed.
Lemma lem4110699 : term457 = True.
Proof. exact (TRANS (@lem4110690) (@lem4110698)). Qed.
Lemma lem4110700 : term454 = True.
Proof. exact (TRANS (@lem4110676) (@lem4110699)). Qed.
Lemma lem4110701 : term206 = True.
Proof. exact (TRANS (@lem4110653) (@lem4110700)). Qed.
Lemma lem4110702 : term451 = True.
Proof. exact (TRANS (@lem4110644) (@lem4110701)). Qed.
Lemma lem4110703 : True = term451.
Proof. exact (SYM (@lem4110702)). Qed.
Lemma lem4110704 : term451.
Proof. exact (EQ_MP (@lem4110703) (@lem0)). Qed.
Lemma lem4110705 (_48296 : int) (h1 : term450 _48296) : term465 _48296.
Proof. exact (conj (@lem4110704) (@lem4110566 _48296 h1)). Qed.
Lemma lem4110707 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4110708 (_48296 : int) : term466 _48296.
Proof. exact (@lem4110707 term111 (term309 _48296)). Qed.
Lemma lem4110709 (_48296 : int) (h1 : term450 _48296) : term467 _48296.
Proof. exact (@lem4110708 _48296 (@lem4110705 _48296 h1)). Qed.
Lemma lem4110710 (_48296 : int) : (term468 _48296) = (term309 _48296).
Proof. exact (@lem1982733 (term309 _48296)). Qed.
Lemma lem4110711 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4110712 (_48296 : int) : (term469 _48296) = (term311 _48296).
Proof. exact (MK_COMB (@lem4110711) (@lem4110710 _48296)). Qed.
Lemma lem4110713 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4110714 (_48296 : int) : (term467 _48296) = (term312 _48296).
Proof. exact (MK_COMB (@lem4110712 _48296) (@lem4110713)). Qed.
Lemma lem4110715 (_48296 : int) (h1 : term450 _48296) : term312 _48296.
Proof. exact (EQ_MP (@lem4110714 _48296) (@lem4110709 _48296 h1)). Qed.
Lemma lem4110716 (_48296 : int) (h1 : term450 _48296) : term470 _48296.
Proof. exact (conj (@lem4110715 _48296 h1) (@lem4110641 _48296 h1)). Qed.
Lemma lem4110718 (x : real) (y : real) : term471 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem4110719 (_48296 : int) : term472 _48296.
Proof. exact (@lem4110718 (term309 _48296) (term245 _48296)). Qed.
Lemma lem4110720 (_48296 : int) (h1 : term450 _48296) : term473 _48296.
Proof. exact (@lem4110719 _48296 (@lem4110716 _48296 h1)). Qed.
Lemma lem4110721 (_48296 : int) : (term474 _48296) = (term475 _48296).
Proof. exact (@lem1982753 (term281 _48296) (real_of_int _48296) term111 term241). Qed.
Lemma lem4110722 (_48296 : int) : (term476 _48296) = (term477 _48296).
Proof. exact (@lem1982713 term178 (real_of_int _48296)). Qed.
Lemma lem4110724 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4110725 : term111 = term200.
Proof. exact (@lem4110724 term20). Qed.
Lemma lem4110727 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4110728 : term178 = term179.
Proof. exact (@lem4110727 term20). Qed.
Lemma lem4110729 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4110730 : term478 = term479.
Proof. exact (MK_COMB (@lem4110729) (@lem4110728)). Qed.
Lemma lem4110731 : term480 = term481.
Proof. exact (MK_COMB (@lem4110730) (@lem4110725)). Qed.
Lemma lem4110732 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4110734 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110735 : term206 = term207.
Proof. exact (@lem4110734 (NUMERAL 0) term20). Qed.
Lemma lem4110736 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110737 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110738 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110737 h1) (fun h1 : term207 = True => @lem4110736)). Qed.
Lemma lem4110739 : term207 = True.
Proof. exact (EQ_MP (@lem4110738) (@lem4110736)). Qed.
Lemma lem4110740 : term206 = True.
Proof. exact (TRANS (@lem4110735) (@lem4110739)). Qed.
Lemma lem4110741 : True = term206.
Proof. exact (SYM (@lem4110740)). Qed.
Lemma lem4110742 : term206.
Proof. exact (EQ_MP (@lem4110741) (@lem0)). Qed.
Lemma lem4110743 : term483.
Proof. exact (@lem4110732 (@lem4110742)). Qed.
Lemma lem4110745 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110746 : term206 = term207.
Proof. exact (@lem4110745 (NUMERAL 0) term20). Qed.
Lemma lem4110747 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110748 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110749 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110748 h1) (fun h1 : term207 = True => @lem4110747)). Qed.
Lemma lem4110750 : term207 = True.
Proof. exact (EQ_MP (@lem4110749) (@lem4110747)). Qed.
Lemma lem4110751 : term206 = True.
Proof. exact (TRANS (@lem4110746) (@lem4110750)). Qed.
Lemma lem4110752 : True = term206.
Proof. exact (SYM (@lem4110751)). Qed.
Lemma lem4110753 : term206.
Proof. exact (EQ_MP (@lem4110752) (@lem0)). Qed.
Lemma lem4110754 : term484.
Proof. exact (@lem4110743 (@lem4110753)). Qed.
Lemma lem4110756 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110757 : term206 = term207.
Proof. exact (@lem4110756 (NUMERAL 0) term20). Qed.
Lemma lem4110758 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110759 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110760 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110759 h1) (fun h1 : term207 = True => @lem4110758)). Qed.
Lemma lem4110761 : term207 = True.
Proof. exact (EQ_MP (@lem4110760) (@lem4110758)). Qed.
Lemma lem4110762 : term206 = True.
Proof. exact (TRANS (@lem4110757) (@lem4110761)). Qed.
Lemma lem4110763 : True = term206.
Proof. exact (SYM (@lem4110762)). Qed.
Lemma lem4110764 : term206.
Proof. exact (EQ_MP (@lem4110763) (@lem0)). Qed.
Lemma lem4110765 : term485.
Proof. exact (@lem4110754 (@lem4110764)). Qed.
Lemma lem4110767 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4110768 : term187 = term188.
Proof. exact (@lem4110767 term20 term20). Qed.
Lemma lem4110769 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110770 : term190 = term20.
Proof. exact (EQ_MP (@lem4110769) (@lem940073)). Qed.
Lemma lem4110771 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110772 : term188 = term111.
Proof. exact (MK_COMB (@lem4110771) (@lem4110770)). Qed.
Lemma lem4110773 : term187 = term111.
Proof. exact (TRANS (@lem4110768) (@lem4110772)). Qed.
Lemma lem4110775 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4110776 : term254 = term257.
Proof. exact (@lem4110775 term20 term20). Qed.
Lemma lem4110777 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110778 : term190 = term20.
Proof. exact (EQ_MP (@lem4110777) (@lem940073)). Qed.
Lemma lem4110779 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110780 : term188 = term111.
Proof. exact (MK_COMB (@lem4110779) (@lem4110778)). Qed.
Lemma lem4110781 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4110782 : term257 = term178.
Proof. exact (MK_COMB (@lem4110781) (@lem4110780)). Qed.
Lemma lem4110783 : term254 = term178.
Proof. exact (TRANS (@lem4110776) (@lem4110782)). Qed.
Lemma lem4110784 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4110785 : term486 = term478.
Proof. exact (MK_COMB (@lem4110784) (@lem4110783)). Qed.
Lemma lem4110786 : term487 = term480.
Proof. exact (MK_COMB (@lem4110785) (@lem4110773)). Qed.
Lemma lem4110788 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4110789 : term480 = term97.
Proof. exact (@lem4110788 term20). Qed.
Lemma lem4110790 : term487 = term97.
Proof. exact (TRANS (@lem4110786) (@lem4110789)). Qed.
Lemma lem4110791 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4110792 : term489 = term291.
Proof. exact (MK_COMB (@lem4110791) (@lem4110790)). Qed.
Lemma lem4110793 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4110794 : term490 = term293.
Proof. exact (MK_COMB (@lem4110792) (@lem4110793)). Qed.
Lemma lem4110796 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4110797 : term293 = term97.
Proof. exact (@lem4110796 term20). Qed.
Lemma lem4110798 : term490 = term97.
Proof. exact (TRANS (@lem4110794) (@lem4110797)). Qed.
Lemma lem4110800 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4110801 : term187 = term188.
Proof. exact (@lem4110800 term20 term20). Qed.
Lemma lem4110802 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110803 : term190 = term20.
Proof. exact (EQ_MP (@lem4110802) (@lem940073)). Qed.
Lemma lem4110804 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110805 : term188 = term111.
Proof. exact (MK_COMB (@lem4110804) (@lem4110803)). Qed.
Lemma lem4110806 : term187 = term111.
Proof. exact (TRANS (@lem4110801) (@lem4110805)). Qed.
Lemma lem4110807 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4110808 : term295 = term293.
Proof. exact (MK_COMB (@lem4110807) (@lem4110806)). Qed.
Lemma lem4110810 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4110811 : term293 = term97.
Proof. exact (@lem4110810 term20). Qed.
Lemma lem4110812 : term295 = term97.
Proof. exact (TRANS (@lem4110808) (@lem4110811)). Qed.
Lemma lem4110813 : term97 = term295.
Proof. exact (SYM (@lem4110812)). Qed.
Lemma lem4110814 : term490 = term295.
Proof. exact (TRANS (@lem4110798) (@lem4110813)). Qed.
Lemma lem4110815 : term481 = term175.
Proof. exact (@lem4110765 (@lem4110814)). Qed.
Lemma lem4110816 : term480 = term175.
Proof. exact (TRANS (@lem4110731) (@lem4110815)). Qed.
Lemma lem4110818 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4110819 : term175 = term97.
Proof. exact (@lem4110818 term97). Qed.
Lemma lem4110820 : term480 = term97.
Proof. exact (TRANS (@lem4110816) (@lem4110819)). Qed.
Lemma lem4110821 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4110822 : term491 = term291.
Proof. exact (MK_COMB (@lem4110821) (@lem4110820)). Qed.
Lemma lem4110823 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4110824 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4110822) (@lem4110823 _48296)). Qed.
Lemma lem4110825 (_48296 : int) : (term476 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4110722 _48296) (@lem4110824 _48296)). Qed.
Lemma lem4110826 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4110827 (_48296 : int) : (term476 _48296) = term97.
Proof. exact (TRANS (@lem4110825 _48296) (@lem4110826 _48296)). Qed.
Lemma lem4110828 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4110829 (_48296 : int) : (term493 _48296) = term139.
Proof. exact (MK_COMB (@lem4110828) (@lem4110827 _48296)). Qed.
Lemma lem4110831 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4110832 : term241 = term244.
Proof. exact (@lem4110831 term218). Qed.
Lemma lem4110834 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4110835 : term111 = term200.
Proof. exact (@lem4110834 term20). Qed.
Lemma lem4110836 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4110837 : term113 = term201.
Proof. exact (MK_COMB (@lem4110836) (@lem4110835)). Qed.
Lemma lem4110838 : term494 = term495.
Proof. exact (MK_COMB (@lem4110837) (@lem4110832)). Qed.
Lemma lem4110839 : term496.
Proof. exact (@lem1981473 term111 term111 term241 term111 term178 term111). Qed.
Lemma lem4110841 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110842 : term206 = term207.
Proof. exact (@lem4110841 (NUMERAL 0) term20). Qed.
Lemma lem4110843 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110844 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110845 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110844 h1) (fun h1 : term207 = True => @lem4110843)). Qed.
Lemma lem4110846 : term207 = True.
Proof. exact (EQ_MP (@lem4110845) (@lem4110843)). Qed.
Lemma lem4110847 : term206 = True.
Proof. exact (TRANS (@lem4110842) (@lem4110846)). Qed.
Lemma lem4110848 : True = term206.
Proof. exact (SYM (@lem4110847)). Qed.
Lemma lem4110849 : term206.
Proof. exact (EQ_MP (@lem4110848) (@lem0)). Qed.
Lemma lem4110850 : term497.
Proof. exact (@lem4110839 (@lem4110849)). Qed.
Lemma lem4110852 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110853 : term206 = term207.
Proof. exact (@lem4110852 (NUMERAL 0) term20). Qed.
Lemma lem4110854 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110855 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110856 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110855 h1) (fun h1 : term207 = True => @lem4110854)). Qed.
Lemma lem4110857 : term207 = True.
Proof. exact (EQ_MP (@lem4110856) (@lem4110854)). Qed.
Lemma lem4110858 : term206 = True.
Proof. exact (TRANS (@lem4110853) (@lem4110857)). Qed.
Lemma lem4110859 : True = term206.
Proof. exact (SYM (@lem4110858)). Qed.
Lemma lem4110860 : term206.
Proof. exact (EQ_MP (@lem4110859) (@lem0)). Qed.
Lemma lem4110861 : term498.
Proof. exact (@lem4110850 (@lem4110860)). Qed.
Lemma lem4110863 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110864 : term206 = term207.
Proof. exact (@lem4110863 (NUMERAL 0) term20). Qed.
Lemma lem4110865 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110866 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110867 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110866 h1) (fun h1 : term207 = True => @lem4110865)). Qed.
Lemma lem4110868 : term207 = True.
Proof. exact (EQ_MP (@lem4110867) (@lem4110865)). Qed.
Lemma lem4110869 : term206 = True.
Proof. exact (TRANS (@lem4110864) (@lem4110868)). Qed.
Lemma lem4110870 : True = term206.
Proof. exact (SYM (@lem4110869)). Qed.
Lemma lem4110871 : term206.
Proof. exact (EQ_MP (@lem4110870) (@lem0)). Qed.
Lemma lem4110872 : term499.
Proof. exact (@lem4110861 (@lem4110871)). Qed.
Lemma lem4110874 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4110875 : term500 = term501.
Proof. exact (@lem4110874 term218 term20). Qed.
Lemma lem4110876 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4110877 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4110878 : term225 = term218.
Proof. exact (EQ_MP (@lem4110877) (@lem4110876)). Qed.
Lemma lem4110879 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110880 : term223 = term204.
Proof. exact (MK_COMB (@lem4110879) (@lem4110878)). Qed.
Lemma lem4110881 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4110882 : term501 = term241.
Proof. exact (MK_COMB (@lem4110881) (@lem4110880)). Qed.
Lemma lem4110883 : term500 = term241.
Proof. exact (TRANS (@lem4110875) (@lem4110882)). Qed.
Lemma lem4110885 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4110886 : term187 = term188.
Proof. exact (@lem4110885 term20 term20). Qed.
Lemma lem4110887 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110888 : term190 = term20.
Proof. exact (EQ_MP (@lem4110887) (@lem940073)). Qed.
Lemma lem4110889 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110890 : term188 = term111.
Proof. exact (MK_COMB (@lem4110889) (@lem4110888)). Qed.
Lemma lem4110891 : term187 = term111.
Proof. exact (TRANS (@lem4110886) (@lem4110890)). Qed.
Lemma lem4110892 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4110893 : term212 = term113.
Proof. exact (MK_COMB (@lem4110892) (@lem4110891)). Qed.
Lemma lem4110894 : term502 = term494.
Proof. exact (MK_COMB (@lem4110893) (@lem4110883)). Qed.
Lemma lem4110897 : term503 = term178.
Proof. exact (@lem1367771 term20 term20). Qed.
Lemma lem4110898 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem4110899 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem4110900 : term217 = term218.
Proof. exact (EQ_MP (@lem4110899) (@lem4110898)). Qed.
Lemma lem4110901 : term218 = term217.
Proof. exact (SYM (@lem4110900)). Qed.
Lemma lem4110902 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110903 : term204 = term214.
Proof. exact (MK_COMB (@lem4110902) (@lem4110901)). Qed.
Lemma lem4110904 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4110905 : term241 = term504.
Proof. exact (MK_COMB (@lem4110904) (@lem4110903)). Qed.
Lemma lem4110906 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem4110907 : term494 = term503.
Proof. exact (MK_COMB (@lem4110906) (@lem4110905)). Qed.
Lemma lem4110908 : term494 = term178.
Proof. exact (TRANS (@lem4110907) (@lem4110897)). Qed.
Lemma lem4110909 : term502 = term178.
Proof. exact (TRANS (@lem4110894) (@lem4110908)). Qed.
Lemma lem4110910 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4110911 : term505 = term180.
Proof. exact (MK_COMB (@lem4110910) (@lem4110909)). Qed.
Lemma lem4110912 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4110913 : term506 = term254.
Proof. exact (MK_COMB (@lem4110911) (@lem4110912)). Qed.
Lemma lem4110915 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4110916 : term254 = term257.
Proof. exact (@lem4110915 term20 term20). Qed.
Lemma lem4110917 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110918 : term190 = term20.
Proof. exact (EQ_MP (@lem4110917) (@lem940073)). Qed.
Lemma lem4110919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110920 : term188 = term111.
Proof. exact (MK_COMB (@lem4110919) (@lem4110918)). Qed.
Lemma lem4110921 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4110922 : term257 = term178.
Proof. exact (MK_COMB (@lem4110921) (@lem4110920)). Qed.
Lemma lem4110923 : term254 = term178.
Proof. exact (TRANS (@lem4110916) (@lem4110922)). Qed.
Lemma lem4110924 : term506 = term178.
Proof. exact (TRANS (@lem4110913) (@lem4110923)). Qed.
Lemma lem4110926 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4110927 : term187 = term188.
Proof. exact (@lem4110926 term20 term20). Qed.
Lemma lem4110928 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110929 : term190 = term20.
Proof. exact (EQ_MP (@lem4110928) (@lem940073)). Qed.
Lemma lem4110930 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110931 : term188 = term111.
Proof. exact (MK_COMB (@lem4110930) (@lem4110929)). Qed.
Lemma lem4110932 : term187 = term111.
Proof. exact (TRANS (@lem4110927) (@lem4110931)). Qed.
Lemma lem4110933 : term180 = term180.
Proof. exact (eq_refl term180). Qed.
Lemma lem4110934 : term507 = term254.
Proof. exact (MK_COMB (@lem4110933) (@lem4110932)). Qed.
Lemma lem4110936 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4110937 : term254 = term257.
Proof. exact (@lem4110936 term20 term20). Qed.
Lemma lem4110938 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4110939 : term190 = term20.
Proof. exact (EQ_MP (@lem4110938) (@lem940073)). Qed.
Lemma lem4110940 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4110941 : term188 = term111.
Proof. exact (MK_COMB (@lem4110940) (@lem4110939)). Qed.
Lemma lem4110942 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4110943 : term257 = term178.
Proof. exact (MK_COMB (@lem4110942) (@lem4110941)). Qed.
Lemma lem4110944 : term254 = term178.
Proof. exact (TRANS (@lem4110937) (@lem4110943)). Qed.
Lemma lem4110945 : term507 = term178.
Proof. exact (TRANS (@lem4110934) (@lem4110944)). Qed.
Lemma lem4110946 : term178 = term507.
Proof. exact (SYM (@lem4110945)). Qed.
Lemma lem4110947 : term506 = term507.
Proof. exact (TRANS (@lem4110924) (@lem4110946)). Qed.
Lemma lem4110948 : term495 = term179.
Proof. exact (@lem4110872 (@lem4110947)). Qed.
Lemma lem4110949 : term494 = term179.
Proof. exact (TRANS (@lem4110838) (@lem4110948)). Qed.
Lemma lem4110951 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4110952 : term179 = term178.
Proof. exact (@lem4110951 term178). Qed.
Lemma lem4110953 : term494 = term178.
Proof. exact (TRANS (@lem4110949) (@lem4110952)). Qed.
Lemma lem4110954 (_48296 : int) : (term475 _48296) = term508.
Proof. exact (MK_COMB (@lem4110829 _48296) (@lem4110953)). Qed.
Lemma lem4110955 (_48296 : int) : (term474 _48296) = term508.
Proof. exact (TRANS (@lem4110721 _48296) (@lem4110954 _48296)). Qed.
Lemma lem4110956 : term508 = term178.
Proof. exact (@lem1982721 term178). Qed.
Lemma lem4110957 (_48296 : int) : (term474 _48296) = term178.
Proof. exact (TRANS (@lem4110955 _48296) (@lem4110956)). Qed.
Lemma lem4110958 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4110959 (_48296 : int) : (term509 _48296) = term510.
Proof. exact (MK_COMB (@lem4110958) (@lem4110957 _48296)). Qed.
Lemma lem4110960 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4110961 (_48296 : int) : (term473 _48296) = term511.
Proof. exact (MK_COMB (@lem4110959 _48296) (@lem4110960)). Qed.
Lemma lem4110962 (_48296 : int) (h1 : term450 _48296) : term511.
Proof. exact (EQ_MP (@lem4110961 _48296) (@lem4110720 _48296 h1)). Qed.
Lemma lem4110964 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4110965 : term511 = term512.
Proof. exact (@lem4110964 term97 term178). Qed.
Lemma lem4110967 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4110968 : term178 = term179.
Proof. exact (@lem4110967 term20). Qed.
Lemma lem4110970 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4110971 : term97 = term175.
Proof. exact (@lem4110970 (NUMERAL 0)). Qed.
Lemma lem4110972 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4110973 : term99 = term513.
Proof. exact (MK_COMB (@lem4110972) (@lem4110971)). Qed.
Lemma lem4110974 : term512 = term514.
Proof. exact (MK_COMB (@lem4110973) (@lem4110968)). Qed.
Lemma lem4110975 : term515.
Proof. exact (@lem1980026 term97 term111 term178 term111). Qed.
Lemma lem4110977 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110978 : term206 = term207.
Proof. exact (@lem4110977 (NUMERAL 0) term20). Qed.
Lemma lem4110979 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110980 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110981 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110980 h1) (fun h1 : term207 = True => @lem4110979)). Qed.
Lemma lem4110982 : term207 = True.
Proof. exact (EQ_MP (@lem4110981) (@lem4110979)). Qed.
Lemma lem4110983 : term206 = True.
Proof. exact (TRANS (@lem4110978) (@lem4110982)). Qed.
Lemma lem4110984 : True = term206.
Proof. exact (SYM (@lem4110983)). Qed.
Lemma lem4110985 : term206.
Proof. exact (EQ_MP (@lem4110984) (@lem0)). Qed.
Lemma lem4110986 : term516.
Proof. exact (@lem4110975 (@lem4110985)). Qed.
Lemma lem4110988 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4110989 : term206 = term207.
Proof. exact (@lem4110988 (NUMERAL 0) term20). Qed.
Lemma lem4110990 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4110991 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4110992 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4110991 h1) (fun h1 : term207 = True => @lem4110990)). Qed.
Lemma lem4110993 : term207 = True.
Proof. exact (EQ_MP (@lem4110992) (@lem4110990)). Qed.
Lemma lem4110994 : term206 = True.
Proof. exact (TRANS (@lem4110989) (@lem4110993)). Qed.
Lemma lem4110995 : True = term206.
Proof. exact (SYM (@lem4110994)). Qed.
Lemma lem4110996 : term206.
Proof. exact (EQ_MP (@lem4110995) (@lem0)). Qed.
Lemma lem4110997 : term514 = term517.
Proof. exact (@lem4110986 (@lem4110996)). Qed.
Lemma lem4110999 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4111000 : term254 = term257.
Proof. exact (@lem4110999 term20 term20). Qed.
Lemma lem4111001 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111002 : term190 = term20.
Proof. exact (EQ_MP (@lem4111001) (@lem940073)). Qed.
Lemma lem4111003 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111004 : term188 = term111.
Proof. exact (MK_COMB (@lem4111003) (@lem4111002)). Qed.
Lemma lem4111005 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4111006 : term257 = term178.
Proof. exact (MK_COMB (@lem4111005) (@lem4111004)). Qed.
Lemma lem4111007 : term254 = term178.
Proof. exact (TRANS (@lem4111000) (@lem4111006)). Qed.
Lemma lem4111009 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111010 : term293 = term97.
Proof. exact (@lem4111009 term20). Qed.
Lemma lem4111011 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4111012 : term518 = term99.
Proof. exact (MK_COMB (@lem4111011) (@lem4111010)). Qed.
Lemma lem4111013 : term517 = term512.
Proof. exact (MK_COMB (@lem4111012) (@lem4111007)). Qed.
Lemma lem4111015 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4111016 : term512 = term521.
Proof. exact (@lem4111015 (NUMERAL 0) term20). Qed.
Lemma lem4111017 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111018 (h1 : term208 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4111019 : (term208 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111018 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem4111017)). Qed.
Lemma lem4111020 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4111019) (@lem4111017)). Qed.
Lemma lem4111021 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4111022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4111023 : term522 = (and True).
Proof. exact (MK_COMB (@lem4111022) (@lem4111021)). Qed.
Lemma lem4111024 : term521 = (True /\ False).
Proof. exact (MK_COMB (@lem4111023) (@lem4111020)). Qed.
Lemma lem4111026 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4111027 : term521 = False.
Proof. exact (TRANS (@lem4111024) (@lem4111026)). Qed.
Lemma lem4111028 : term512 = False.
Proof. exact (TRANS (@lem4111016) (@lem4111027)). Qed.
Lemma lem4111029 : term517 = False.
Proof. exact (TRANS (@lem4111013) (@lem4111028)). Qed.
Lemma lem4111030 : term514 = False.
Proof. exact (TRANS (@lem4110997) (@lem4111029)). Qed.
Lemma lem4111031 : term512 = False.
Proof. exact (TRANS (@lem4110974) (@lem4111030)). Qed.
Lemma lem4111032 : term511 = False.
Proof. exact (TRANS (@lem4110965) (@lem4111031)). Qed.
Lemma lem4111033 (_48296 : int) (h1 : term450 _48296) : False.
Proof. exact (EQ_MP (@lem4111032) (@lem4110962 _48296 h1)). Qed.
Lemma lem4111034 (_48296 : int) (h1 : term444 _48296) : term444 _48296.
Proof. exact (h1). Qed.
Lemma lem4111035 (_48296 : int) (h1 : term439 _48296) : term439 _48296.
Proof. exact (h1). Qed.
Lemma lem4111036 (_48296 : int) (h1 : term523 _48296) : term523 _48296.
Proof. exact (h1). Qed.
Lemma lem4111037 (_48296 : int) (h1 : term523 _48296) : term440 _48296.
Proof. exact (proj2 (@lem4111036 _48296 h1)). Qed.
Lemma lem4111038 (_48296 : int) (h1 : term523 _48296) : term198 _48296.
Proof. exact (proj1 (@lem4111036 _48296 h1)). Qed.
Lemma lem4111040 (_48296 : int) (h1 : term523 _48296) : term347 _48296.
Proof. exact (proj1 (@lem4111037 _48296 h1)). Qed.
Lemma lem4111042 (_48296 : int) (h1 : term523 _48296) : term265 _48296.
Proof. exact (proj1 (@lem4111040 _48296 h1)). Qed.
Lemma lem4111044 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4111045 : term451 = term206.
Proof. exact (@lem4111044 term97 term111). Qed.
Lemma lem4111047 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111048 : term111 = term200.
Proof. exact (@lem4111047 term20). Qed.
Lemma lem4111050 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111051 : term97 = term175.
Proof. exact (@lem4111050 (NUMERAL 0)). Qed.
Lemma lem4111052 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4111053 : term452 = term453.
Proof. exact (MK_COMB (@lem4111052) (@lem4111051)). Qed.
Lemma lem4111054 : term206 = term454.
Proof. exact (MK_COMB (@lem4111053) (@lem4111048)). Qed.
Lemma lem4111055 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4111057 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111058 : term206 = term207.
Proof. exact (@lem4111057 (NUMERAL 0) term20). Qed.
Lemma lem4111059 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111060 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111061 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111060 h1) (fun h1 : term207 = True => @lem4111059)). Qed.
Lemma lem4111062 : term207 = True.
Proof. exact (EQ_MP (@lem4111061) (@lem4111059)). Qed.
Lemma lem4111063 : term206 = True.
Proof. exact (TRANS (@lem4111058) (@lem4111062)). Qed.
Lemma lem4111064 : True = term206.
Proof. exact (SYM (@lem4111063)). Qed.
Lemma lem4111065 : term206.
Proof. exact (EQ_MP (@lem4111064) (@lem0)). Qed.
Lemma lem4111066 : term456.
Proof. exact (@lem4111055 (@lem4111065)). Qed.
Lemma lem4111068 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111069 : term206 = term207.
Proof. exact (@lem4111068 (NUMERAL 0) term20). Qed.
Lemma lem4111070 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111071 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111072 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111071 h1) (fun h1 : term207 = True => @lem4111070)). Qed.
Lemma lem4111073 : term207 = True.
Proof. exact (EQ_MP (@lem4111072) (@lem4111070)). Qed.
Lemma lem4111074 : term206 = True.
Proof. exact (TRANS (@lem4111069) (@lem4111073)). Qed.
Lemma lem4111075 : True = term206.
Proof. exact (SYM (@lem4111074)). Qed.
Lemma lem4111076 : term206.
Proof. exact (EQ_MP (@lem4111075) (@lem0)). Qed.
Lemma lem4111077 : term454 = term457.
Proof. exact (@lem4111066 (@lem4111076)). Qed.
Lemma lem4111079 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4111080 : term187 = term188.
Proof. exact (@lem4111079 term20 term20). Qed.
Lemma lem4111081 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111082 : term190 = term20.
Proof. exact (EQ_MP (@lem4111081) (@lem940073)). Qed.
Lemma lem4111083 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111084 : term188 = term111.
Proof. exact (MK_COMB (@lem4111083) (@lem4111082)). Qed.
Lemma lem4111085 : term187 = term111.
Proof. exact (TRANS (@lem4111080) (@lem4111084)). Qed.
Lemma lem4111087 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111088 : term293 = term97.
Proof. exact (@lem4111087 term20). Qed.
Lemma lem4111089 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4111090 : term458 = term452.
Proof. exact (MK_COMB (@lem4111089) (@lem4111088)). Qed.
Lemma lem4111091 : term457 = term206.
Proof. exact (MK_COMB (@lem4111090) (@lem4111085)). Qed.
Lemma lem4111093 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111094 : term206 = term207.
Proof. exact (@lem4111093 (NUMERAL 0) term20). Qed.
Lemma lem4111095 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111096 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111097 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111096 h1) (fun h1 : term207 = True => @lem4111095)). Qed.
Lemma lem4111098 : term207 = True.
Proof. exact (EQ_MP (@lem4111097) (@lem4111095)). Qed.
Lemma lem4111099 : term206 = True.
Proof. exact (TRANS (@lem4111094) (@lem4111098)). Qed.
Lemma lem4111100 : term457 = True.
Proof. exact (TRANS (@lem4111091) (@lem4111099)). Qed.
Lemma lem4111101 : term454 = True.
Proof. exact (TRANS (@lem4111077) (@lem4111100)). Qed.
Lemma lem4111102 : term206 = True.
Proof. exact (TRANS (@lem4111054) (@lem4111101)). Qed.
Lemma lem4111103 : term451 = True.
Proof. exact (TRANS (@lem4111045) (@lem4111102)). Qed.
Lemma lem4111104 : True = term451.
Proof. exact (SYM (@lem4111103)). Qed.
Lemma lem4111105 : term451.
Proof. exact (EQ_MP (@lem4111104) (@lem0)). Qed.
Lemma lem4111106 (_48296 : int) (h1 : term523 _48296) : term524 _48296.
Proof. exact (conj (@lem4111105) (@lem4111038 _48296 h1)). Qed.
Lemma lem4111108 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4111109 (_48296 : int) : term525 _48296.
Proof. exact (@lem4111108 term111 (real_of_int _48296)). Qed.
Lemma lem4111110 (_48296 : int) (h1 : term523 _48296) : term526 _48296.
Proof. exact (@lem4111109 _48296 (@lem4111106 _48296 h1)). Qed.
Lemma lem4111111 (_48296 : int) : (term527 _48296) = (real_of_int _48296).
Proof. exact (@lem1982733 (real_of_int _48296)). Qed.
Lemma lem4111112 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4111113 (_48296 : int) : (term528 _48296) = (term197 _48296).
Proof. exact (MK_COMB (@lem4111112) (@lem4111111 _48296)). Qed.
Lemma lem4111114 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4111115 (_48296 : int) : (term526 _48296) = (term198 _48296).
Proof. exact (MK_COMB (@lem4111113 _48296) (@lem4111114)). Qed.
Lemma lem4111116 (_48296 : int) (h1 : term523 _48296) : term198 _48296.
Proof. exact (EQ_MP (@lem4111115 _48296) (@lem4111110 _48296 h1)). Qed.
Lemma lem4111118 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4111119 : term451 = term206.
Proof. exact (@lem4111118 term97 term111). Qed.
Lemma lem4111121 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111122 : term111 = term200.
Proof. exact (@lem4111121 term20). Qed.
Lemma lem4111124 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111125 : term97 = term175.
Proof. exact (@lem4111124 (NUMERAL 0)). Qed.
Lemma lem4111126 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4111127 : term452 = term453.
Proof. exact (MK_COMB (@lem4111126) (@lem4111125)). Qed.
Lemma lem4111128 : term206 = term454.
Proof. exact (MK_COMB (@lem4111127) (@lem4111122)). Qed.
Lemma lem4111129 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4111131 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111132 : term206 = term207.
Proof. exact (@lem4111131 (NUMERAL 0) term20). Qed.
Lemma lem4111133 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111134 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111135 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111134 h1) (fun h1 : term207 = True => @lem4111133)). Qed.
Lemma lem4111136 : term207 = True.
Proof. exact (EQ_MP (@lem4111135) (@lem4111133)). Qed.
Lemma lem4111137 : term206 = True.
Proof. exact (TRANS (@lem4111132) (@lem4111136)). Qed.
Lemma lem4111138 : True = term206.
Proof. exact (SYM (@lem4111137)). Qed.
Lemma lem4111139 : term206.
Proof. exact (EQ_MP (@lem4111138) (@lem0)). Qed.
Lemma lem4111140 : term456.
Proof. exact (@lem4111129 (@lem4111139)). Qed.
Lemma lem4111142 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111143 : term206 = term207.
Proof. exact (@lem4111142 (NUMERAL 0) term20). Qed.
Lemma lem4111144 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111145 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111146 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111145 h1) (fun h1 : term207 = True => @lem4111144)). Qed.
Lemma lem4111147 : term207 = True.
Proof. exact (EQ_MP (@lem4111146) (@lem4111144)). Qed.
Lemma lem4111148 : term206 = True.
Proof. exact (TRANS (@lem4111143) (@lem4111147)). Qed.
Lemma lem4111149 : True = term206.
Proof. exact (SYM (@lem4111148)). Qed.
Lemma lem4111150 : term206.
Proof. exact (EQ_MP (@lem4111149) (@lem0)). Qed.
Lemma lem4111151 : term454 = term457.
Proof. exact (@lem4111140 (@lem4111150)). Qed.
Lemma lem4111153 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4111154 : term187 = term188.
Proof. exact (@lem4111153 term20 term20). Qed.
Lemma lem4111155 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111156 : term190 = term20.
Proof. exact (EQ_MP (@lem4111155) (@lem940073)). Qed.
Lemma lem4111157 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111158 : term188 = term111.
Proof. exact (MK_COMB (@lem4111157) (@lem4111156)). Qed.
Lemma lem4111159 : term187 = term111.
Proof. exact (TRANS (@lem4111154) (@lem4111158)). Qed.
Lemma lem4111161 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111162 : term293 = term97.
Proof. exact (@lem4111161 term20). Qed.
Lemma lem4111163 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4111164 : term458 = term452.
Proof. exact (MK_COMB (@lem4111163) (@lem4111162)). Qed.
Lemma lem4111165 : term457 = term206.
Proof. exact (MK_COMB (@lem4111164) (@lem4111159)). Qed.
Lemma lem4111167 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111168 : term206 = term207.
Proof. exact (@lem4111167 (NUMERAL 0) term20). Qed.
Lemma lem4111169 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111170 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111171 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111170 h1) (fun h1 : term207 = True => @lem4111169)). Qed.
Lemma lem4111172 : term207 = True.
Proof. exact (EQ_MP (@lem4111171) (@lem4111169)). Qed.
Lemma lem4111173 : term206 = True.
Proof. exact (TRANS (@lem4111168) (@lem4111172)). Qed.
Lemma lem4111174 : term457 = True.
Proof. exact (TRANS (@lem4111165) (@lem4111173)). Qed.
Lemma lem4111175 : term454 = True.
Proof. exact (TRANS (@lem4111151) (@lem4111174)). Qed.
Lemma lem4111176 : term206 = True.
Proof. exact (TRANS (@lem4111128) (@lem4111175)). Qed.
Lemma lem4111177 : term451 = True.
Proof. exact (TRANS (@lem4111119) (@lem4111176)). Qed.
Lemma lem4111178 : True = term451.
Proof. exact (SYM (@lem4111177)). Qed.
Lemma lem4111179 : term451.
Proof. exact (EQ_MP (@lem4111178) (@lem0)). Qed.
Lemma lem4111180 (_48296 : int) (h1 : term523 _48296) : term529 _48296.
Proof. exact (conj (@lem4111179) (@lem4111042 _48296 h1)). Qed.
Lemma lem4111182 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4111183 (_48296 : int) : term530 _48296.
Proof. exact (@lem4111182 term111 (term261 _48296)). Qed.
Lemma lem4111184 (_48296 : int) (h1 : term523 _48296) : term531 _48296.
Proof. exact (@lem4111183 _48296 (@lem4111180 _48296 h1)). Qed.
Lemma lem4111185 (_48296 : int) : (term532 _48296) = (term261 _48296).
Proof. exact (@lem1982733 (term261 _48296)). Qed.
Lemma lem4111186 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4111187 (_48296 : int) : (term533 _48296) = (term264 _48296).
Proof. exact (MK_COMB (@lem4111186) (@lem4111185 _48296)). Qed.
Lemma lem4111188 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4111189 (_48296 : int) : (term531 _48296) = (term265 _48296).
Proof. exact (MK_COMB (@lem4111187 _48296) (@lem4111188)). Qed.
Lemma lem4111190 (_48296 : int) (h1 : term523 _48296) : term265 _48296.
Proof. exact (EQ_MP (@lem4111189 _48296) (@lem4111184 _48296 h1)). Qed.
Lemma lem4111191 (_48296 : int) (h1 : term523 _48296) : term534 _48296.
Proof. exact (conj (@lem4111190 _48296 h1) (@lem4111116 _48296 h1)). Qed.
Lemma lem4111193 (x : real) (y : real) : term471 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem4111194 (_48296 : int) : term535 _48296.
Proof. exact (@lem4111193 (term261 _48296) (real_of_int _48296)). Qed.
Lemma lem4111195 (_48296 : int) (h1 : term523 _48296) : term536 _48296.
Proof. exact (@lem4111194 _48296 (@lem4111191 _48296 h1)). Qed.
Lemma lem4111196 (_48296 : int) : (term537 _48296) = (term538 _48296).
Proof. exact (@lem1982759 (term281 _48296) (real_of_int _48296) term178). Qed.
Lemma lem4111197 (_48296 : int) : (term476 _48296) = (term477 _48296).
Proof. exact (@lem1982713 term178 (real_of_int _48296)). Qed.
Lemma lem4111199 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111200 : term111 = term200.
Proof. exact (@lem4111199 term20). Qed.
Lemma lem4111202 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4111203 : term178 = term179.
Proof. exact (@lem4111202 term20). Qed.
Lemma lem4111204 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4111205 : term478 = term479.
Proof. exact (MK_COMB (@lem4111204) (@lem4111203)). Qed.
Lemma lem4111206 : term480 = term481.
Proof. exact (MK_COMB (@lem4111205) (@lem4111200)). Qed.
Lemma lem4111207 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4111209 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111210 : term206 = term207.
Proof. exact (@lem4111209 (NUMERAL 0) term20). Qed.
Lemma lem4111211 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111212 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111213 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111212 h1) (fun h1 : term207 = True => @lem4111211)). Qed.
Lemma lem4111214 : term207 = True.
Proof. exact (EQ_MP (@lem4111213) (@lem4111211)). Qed.
Lemma lem4111215 : term206 = True.
Proof. exact (TRANS (@lem4111210) (@lem4111214)). Qed.
Lemma lem4111216 : True = term206.
Proof. exact (SYM (@lem4111215)). Qed.
Lemma lem4111217 : term206.
Proof. exact (EQ_MP (@lem4111216) (@lem0)). Qed.
Lemma lem4111218 : term483.
Proof. exact (@lem4111207 (@lem4111217)). Qed.
Lemma lem4111220 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111221 : term206 = term207.
Proof. exact (@lem4111220 (NUMERAL 0) term20). Qed.
Lemma lem4111222 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111223 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111224 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111223 h1) (fun h1 : term207 = True => @lem4111222)). Qed.
Lemma lem4111225 : term207 = True.
Proof. exact (EQ_MP (@lem4111224) (@lem4111222)). Qed.
Lemma lem4111226 : term206 = True.
Proof. exact (TRANS (@lem4111221) (@lem4111225)). Qed.
Lemma lem4111227 : True = term206.
Proof. exact (SYM (@lem4111226)). Qed.
Lemma lem4111228 : term206.
Proof. exact (EQ_MP (@lem4111227) (@lem0)). Qed.
Lemma lem4111229 : term484.
Proof. exact (@lem4111218 (@lem4111228)). Qed.
Lemma lem4111231 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111232 : term206 = term207.
Proof. exact (@lem4111231 (NUMERAL 0) term20). Qed.
Lemma lem4111233 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111234 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111235 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111234 h1) (fun h1 : term207 = True => @lem4111233)). Qed.
Lemma lem4111236 : term207 = True.
Proof. exact (EQ_MP (@lem4111235) (@lem4111233)). Qed.
Lemma lem4111237 : term206 = True.
Proof. exact (TRANS (@lem4111232) (@lem4111236)). Qed.
Lemma lem4111238 : True = term206.
Proof. exact (SYM (@lem4111237)). Qed.
Lemma lem4111239 : term206.
Proof. exact (EQ_MP (@lem4111238) (@lem0)). Qed.
Lemma lem4111240 : term485.
Proof. exact (@lem4111229 (@lem4111239)). Qed.
Lemma lem4111242 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4111243 : term187 = term188.
Proof. exact (@lem4111242 term20 term20). Qed.
Lemma lem4111244 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111245 : term190 = term20.
Proof. exact (EQ_MP (@lem4111244) (@lem940073)). Qed.
Lemma lem4111246 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111247 : term188 = term111.
Proof. exact (MK_COMB (@lem4111246) (@lem4111245)). Qed.
Lemma lem4111248 : term187 = term111.
Proof. exact (TRANS (@lem4111243) (@lem4111247)). Qed.
Lemma lem4111250 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4111251 : term254 = term257.
Proof. exact (@lem4111250 term20 term20). Qed.
Lemma lem4111252 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111253 : term190 = term20.
Proof. exact (EQ_MP (@lem4111252) (@lem940073)). Qed.
Lemma lem4111254 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111255 : term188 = term111.
Proof. exact (MK_COMB (@lem4111254) (@lem4111253)). Qed.
Lemma lem4111256 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4111257 : term257 = term178.
Proof. exact (MK_COMB (@lem4111256) (@lem4111255)). Qed.
Lemma lem4111258 : term254 = term178.
Proof. exact (TRANS (@lem4111251) (@lem4111257)). Qed.
Lemma lem4111259 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4111260 : term486 = term478.
Proof. exact (MK_COMB (@lem4111259) (@lem4111258)). Qed.
Lemma lem4111261 : term487 = term480.
Proof. exact (MK_COMB (@lem4111260) (@lem4111248)). Qed.
Lemma lem4111263 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4111264 : term480 = term97.
Proof. exact (@lem4111263 term20). Qed.
Lemma lem4111265 : term487 = term97.
Proof. exact (TRANS (@lem4111261) (@lem4111264)). Qed.
Lemma lem4111266 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4111267 : term489 = term291.
Proof. exact (MK_COMB (@lem4111266) (@lem4111265)). Qed.
Lemma lem4111268 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4111269 : term490 = term293.
Proof. exact (MK_COMB (@lem4111267) (@lem4111268)). Qed.
Lemma lem4111271 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111272 : term293 = term97.
Proof. exact (@lem4111271 term20). Qed.
Lemma lem4111273 : term490 = term97.
Proof. exact (TRANS (@lem4111269) (@lem4111272)). Qed.
Lemma lem4111275 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4111276 : term187 = term188.
Proof. exact (@lem4111275 term20 term20). Qed.
Lemma lem4111277 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111278 : term190 = term20.
Proof. exact (EQ_MP (@lem4111277) (@lem940073)). Qed.
Lemma lem4111279 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111280 : term188 = term111.
Proof. exact (MK_COMB (@lem4111279) (@lem4111278)). Qed.
Lemma lem4111281 : term187 = term111.
Proof. exact (TRANS (@lem4111276) (@lem4111280)). Qed.
Lemma lem4111282 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4111283 : term295 = term293.
Proof. exact (MK_COMB (@lem4111282) (@lem4111281)). Qed.
Lemma lem4111285 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111286 : term293 = term97.
Proof. exact (@lem4111285 term20). Qed.
Lemma lem4111287 : term295 = term97.
Proof. exact (TRANS (@lem4111283) (@lem4111286)). Qed.
Lemma lem4111288 : term97 = term295.
Proof. exact (SYM (@lem4111287)). Qed.
Lemma lem4111289 : term490 = term295.
Proof. exact (TRANS (@lem4111273) (@lem4111288)). Qed.
Lemma lem4111290 : term481 = term175.
Proof. exact (@lem4111240 (@lem4111289)). Qed.
Lemma lem4111291 : term480 = term175.
Proof. exact (TRANS (@lem4111206) (@lem4111290)). Qed.
Lemma lem4111293 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4111294 : term175 = term97.
Proof. exact (@lem4111293 term97). Qed.
Lemma lem4111295 : term480 = term97.
Proof. exact (TRANS (@lem4111291) (@lem4111294)). Qed.
Lemma lem4111296 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4111297 : term491 = term291.
Proof. exact (MK_COMB (@lem4111296) (@lem4111295)). Qed.
Lemma lem4111298 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4111299 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4111297) (@lem4111298 _48296)). Qed.
Lemma lem4111300 (_48296 : int) : (term476 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4111197 _48296) (@lem4111299 _48296)). Qed.
Lemma lem4111301 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4111302 (_48296 : int) : (term476 _48296) = term97.
Proof. exact (TRANS (@lem4111300 _48296) (@lem4111301 _48296)). Qed.
Lemma lem4111303 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4111304 (_48296 : int) : (term493 _48296) = term139.
Proof. exact (MK_COMB (@lem4111303) (@lem4111302 _48296)). Qed.
Lemma lem4111305 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem4111306 (_48296 : int) : (term538 _48296) = term508.
Proof. exact (MK_COMB (@lem4111304 _48296) (@lem4111305)). Qed.
Lemma lem4111307 (_48296 : int) : (term537 _48296) = term508.
Proof. exact (TRANS (@lem4111196 _48296) (@lem4111306 _48296)). Qed.
Lemma lem4111308 : term508 = term178.
Proof. exact (@lem1982721 term178). Qed.
Lemma lem4111309 (_48296 : int) : (term537 _48296) = term178.
Proof. exact (TRANS (@lem4111307 _48296) (@lem4111308)). Qed.
Lemma lem4111310 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4111311 (_48296 : int) : (term539 _48296) = term510.
Proof. exact (MK_COMB (@lem4111310) (@lem4111309 _48296)). Qed.
Lemma lem4111312 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4111313 (_48296 : int) : (term536 _48296) = term511.
Proof. exact (MK_COMB (@lem4111311 _48296) (@lem4111312)). Qed.
Lemma lem4111314 (_48296 : int) (h1 : term523 _48296) : term511.
Proof. exact (EQ_MP (@lem4111313 _48296) (@lem4111195 _48296 h1)). Qed.
Lemma lem4111316 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4111317 : term511 = term512.
Proof. exact (@lem4111316 term97 term178). Qed.
Lemma lem4111319 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4111320 : term178 = term179.
Proof. exact (@lem4111319 term20). Qed.
Lemma lem4111322 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111323 : term97 = term175.
Proof. exact (@lem4111322 (NUMERAL 0)). Qed.
Lemma lem4111324 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4111325 : term99 = term513.
Proof. exact (MK_COMB (@lem4111324) (@lem4111323)). Qed.
Lemma lem4111326 : term512 = term514.
Proof. exact (MK_COMB (@lem4111325) (@lem4111320)). Qed.
Lemma lem4111327 : term515.
Proof. exact (@lem1980026 term97 term111 term178 term111). Qed.
Lemma lem4111329 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111330 : term206 = term207.
Proof. exact (@lem4111329 (NUMERAL 0) term20). Qed.
Lemma lem4111331 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111332 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111333 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111332 h1) (fun h1 : term207 = True => @lem4111331)). Qed.
Lemma lem4111334 : term207 = True.
Proof. exact (EQ_MP (@lem4111333) (@lem4111331)). Qed.
Lemma lem4111335 : term206 = True.
Proof. exact (TRANS (@lem4111330) (@lem4111334)). Qed.
Lemma lem4111336 : True = term206.
Proof. exact (SYM (@lem4111335)). Qed.
Lemma lem4111337 : term206.
Proof. exact (EQ_MP (@lem4111336) (@lem0)). Qed.
Lemma lem4111338 : term516.
Proof. exact (@lem4111327 (@lem4111337)). Qed.
Lemma lem4111340 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111341 : term206 = term207.
Proof. exact (@lem4111340 (NUMERAL 0) term20). Qed.
Lemma lem4111342 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111343 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111344 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111343 h1) (fun h1 : term207 = True => @lem4111342)). Qed.
Lemma lem4111345 : term207 = True.
Proof. exact (EQ_MP (@lem4111344) (@lem4111342)). Qed.
Lemma lem4111346 : term206 = True.
Proof. exact (TRANS (@lem4111341) (@lem4111345)). Qed.
Lemma lem4111347 : True = term206.
Proof. exact (SYM (@lem4111346)). Qed.
Lemma lem4111348 : term206.
Proof. exact (EQ_MP (@lem4111347) (@lem0)). Qed.
Lemma lem4111349 : term514 = term517.
Proof. exact (@lem4111338 (@lem4111348)). Qed.
Lemma lem4111351 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4111352 : term254 = term257.
Proof. exact (@lem4111351 term20 term20). Qed.
Lemma lem4111353 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111354 : term190 = term20.
Proof. exact (EQ_MP (@lem4111353) (@lem940073)). Qed.
Lemma lem4111355 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111356 : term188 = term111.
Proof. exact (MK_COMB (@lem4111355) (@lem4111354)). Qed.
Lemma lem4111357 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4111358 : term257 = term178.
Proof. exact (MK_COMB (@lem4111357) (@lem4111356)). Qed.
Lemma lem4111359 : term254 = term178.
Proof. exact (TRANS (@lem4111352) (@lem4111358)). Qed.
Lemma lem4111361 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111362 : term293 = term97.
Proof. exact (@lem4111361 term20). Qed.
Lemma lem4111363 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4111364 : term518 = term99.
Proof. exact (MK_COMB (@lem4111363) (@lem4111362)). Qed.
Lemma lem4111365 : term517 = term512.
Proof. exact (MK_COMB (@lem4111364) (@lem4111359)). Qed.
Lemma lem4111367 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4111368 : term512 = term521.
Proof. exact (@lem4111367 (NUMERAL 0) term20). Qed.
Lemma lem4111369 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111370 (h1 : term208 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4111371 : (term208 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111370 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem4111369)). Qed.
Lemma lem4111372 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4111371) (@lem4111369)). Qed.
Lemma lem4111373 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4111374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4111375 : term522 = (and True).
Proof. exact (MK_COMB (@lem4111374) (@lem4111373)). Qed.
Lemma lem4111376 : term521 = (True /\ False).
Proof. exact (MK_COMB (@lem4111375) (@lem4111372)). Qed.
Lemma lem4111378 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4111379 : term521 = False.
Proof. exact (TRANS (@lem4111376) (@lem4111378)). Qed.
Lemma lem4111380 : term512 = False.
Proof. exact (TRANS (@lem4111368) (@lem4111379)). Qed.
Lemma lem4111381 : term517 = False.
Proof. exact (TRANS (@lem4111365) (@lem4111380)). Qed.
Lemma lem4111382 : term514 = False.
Proof. exact (TRANS (@lem4111349) (@lem4111381)). Qed.
Lemma lem4111383 : term512 = False.
Proof. exact (TRANS (@lem4111326) (@lem4111382)). Qed.
Lemma lem4111384 : term511 = False.
Proof. exact (TRANS (@lem4111317) (@lem4111383)). Qed.
Lemma lem4111385 (_48296 : int) (h1 : term523 _48296) : False.
Proof. exact (EQ_MP (@lem4111384) (@lem4111314 _48296 h1)). Qed.
Lemma lem4111386 (_48296 : int) (h1 : term540 _48296) : term540 _48296.
Proof. exact (h1). Qed.
Lemma lem4111387 (_48296 : int) (h1 : term540 _48296) : term441 _48296.
Proof. exact (proj2 (@lem4111386 _48296 h1)). Qed.
Lemma lem4111390 (_48296 : int) (h1 : term540 _48296) : term348 _48296.
Proof. exact (proj1 (@lem4111387 _48296 h1)). Qed.
Lemma lem4111391 (_48296 : int) (h1 : term540 _48296) : term299 _48296.
Proof. exact (proj2 (@lem4111390 _48296 h1)). Qed.
Lemma lem4111392 (_48296 : int) (h1 : term540 _48296) : term273 _48296.
Proof. exact (proj1 (@lem4111390 _48296 h1)). Qed.
Lemma lem4111394 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4111395 : term451 = term206.
Proof. exact (@lem4111394 term97 term111). Qed.
Lemma lem4111397 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111398 : term111 = term200.
Proof. exact (@lem4111397 term20). Qed.
Lemma lem4111400 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111401 : term97 = term175.
Proof. exact (@lem4111400 (NUMERAL 0)). Qed.
Lemma lem4111402 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4111403 : term452 = term453.
Proof. exact (MK_COMB (@lem4111402) (@lem4111401)). Qed.
Lemma lem4111404 : term206 = term454.
Proof. exact (MK_COMB (@lem4111403) (@lem4111398)). Qed.
Lemma lem4111405 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4111407 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111408 : term206 = term207.
Proof. exact (@lem4111407 (NUMERAL 0) term20). Qed.
Lemma lem4111409 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111410 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111411 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111410 h1) (fun h1 : term207 = True => @lem4111409)). Qed.
Lemma lem4111412 : term207 = True.
Proof. exact (EQ_MP (@lem4111411) (@lem4111409)). Qed.
Lemma lem4111413 : term206 = True.
Proof. exact (TRANS (@lem4111408) (@lem4111412)). Qed.
Lemma lem4111414 : True = term206.
Proof. exact (SYM (@lem4111413)). Qed.
Lemma lem4111415 : term206.
Proof. exact (EQ_MP (@lem4111414) (@lem0)). Qed.
Lemma lem4111416 : term456.
Proof. exact (@lem4111405 (@lem4111415)). Qed.
Lemma lem4111418 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111419 : term206 = term207.
Proof. exact (@lem4111418 (NUMERAL 0) term20). Qed.
Lemma lem4111420 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111421 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111422 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111421 h1) (fun h1 : term207 = True => @lem4111420)). Qed.
Lemma lem4111423 : term207 = True.
Proof. exact (EQ_MP (@lem4111422) (@lem4111420)). Qed.
Lemma lem4111424 : term206 = True.
Proof. exact (TRANS (@lem4111419) (@lem4111423)). Qed.
Lemma lem4111425 : True = term206.
Proof. exact (SYM (@lem4111424)). Qed.
Lemma lem4111426 : term206.
Proof. exact (EQ_MP (@lem4111425) (@lem0)). Qed.
Lemma lem4111427 : term454 = term457.
Proof. exact (@lem4111416 (@lem4111426)). Qed.
Lemma lem4111429 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4111430 : term187 = term188.
Proof. exact (@lem4111429 term20 term20). Qed.
Lemma lem4111431 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111432 : term190 = term20.
Proof. exact (EQ_MP (@lem4111431) (@lem940073)). Qed.
Lemma lem4111433 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111434 : term188 = term111.
Proof. exact (MK_COMB (@lem4111433) (@lem4111432)). Qed.
Lemma lem4111435 : term187 = term111.
Proof. exact (TRANS (@lem4111430) (@lem4111434)). Qed.
Lemma lem4111437 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111438 : term293 = term97.
Proof. exact (@lem4111437 term20). Qed.
Lemma lem4111439 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4111440 : term458 = term452.
Proof. exact (MK_COMB (@lem4111439) (@lem4111438)). Qed.
Lemma lem4111441 : term457 = term206.
Proof. exact (MK_COMB (@lem4111440) (@lem4111435)). Qed.
Lemma lem4111443 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111444 : term206 = term207.
Proof. exact (@lem4111443 (NUMERAL 0) term20). Qed.
Lemma lem4111445 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111446 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111447 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111446 h1) (fun h1 : term207 = True => @lem4111445)). Qed.
Lemma lem4111448 : term207 = True.
Proof. exact (EQ_MP (@lem4111447) (@lem4111445)). Qed.
Lemma lem4111449 : term206 = True.
Proof. exact (TRANS (@lem4111444) (@lem4111448)). Qed.
Lemma lem4111450 : term457 = True.
Proof. exact (TRANS (@lem4111441) (@lem4111449)). Qed.
Lemma lem4111451 : term454 = True.
Proof. exact (TRANS (@lem4111427) (@lem4111450)). Qed.
Lemma lem4111452 : term206 = True.
Proof. exact (TRANS (@lem4111404) (@lem4111451)). Qed.
Lemma lem4111453 : term451 = True.
Proof. exact (TRANS (@lem4111395) (@lem4111452)). Qed.
Lemma lem4111454 : True = term451.
Proof. exact (SYM (@lem4111453)). Qed.
Lemma lem4111455 : term451.
Proof. exact (EQ_MP (@lem4111454) (@lem0)). Qed.
Lemma lem4111456 (_48296 : int) (h1 : term540 _48296) : term541 _48296.
Proof. exact (conj (@lem4111455) (@lem4111392 _48296 h1)). Qed.
Lemma lem4111458 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4111459 (_48296 : int) : term542 _48296.
Proof. exact (@lem4111458 term111 (term270 _48296)). Qed.
Lemma lem4111460 (_48296 : int) (h1 : term540 _48296) : term543 _48296.
Proof. exact (@lem4111459 _48296 (@lem4111456 _48296 h1)). Qed.
Lemma lem4111461 (_48296 : int) : (term544 _48296) = (term270 _48296).
Proof. exact (@lem1982733 (term270 _48296)). Qed.
Lemma lem4111462 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4111463 (_48296 : int) : (term545 _48296) = (term272 _48296).
Proof. exact (MK_COMB (@lem4111462) (@lem4111461 _48296)). Qed.
Lemma lem4111464 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4111465 (_48296 : int) : (term543 _48296) = (term273 _48296).
Proof. exact (MK_COMB (@lem4111463 _48296) (@lem4111464)). Qed.
Lemma lem4111466 (_48296 : int) (h1 : term540 _48296) : term273 _48296.
Proof. exact (EQ_MP (@lem4111465 _48296) (@lem4111460 _48296 h1)). Qed.
Lemma lem4111468 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4111469 : term451 = term206.
Proof. exact (@lem4111468 term97 term111). Qed.
Lemma lem4111471 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111472 : term111 = term200.
Proof. exact (@lem4111471 term20). Qed.
Lemma lem4111474 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111475 : term97 = term175.
Proof. exact (@lem4111474 (NUMERAL 0)). Qed.
Lemma lem4111476 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4111477 : term452 = term453.
Proof. exact (MK_COMB (@lem4111476) (@lem4111475)). Qed.
Lemma lem4111478 : term206 = term454.
Proof. exact (MK_COMB (@lem4111477) (@lem4111472)). Qed.
Lemma lem4111479 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4111481 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111482 : term206 = term207.
Proof. exact (@lem4111481 (NUMERAL 0) term20). Qed.
Lemma lem4111483 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111484 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111485 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111484 h1) (fun h1 : term207 = True => @lem4111483)). Qed.
Lemma lem4111486 : term207 = True.
Proof. exact (EQ_MP (@lem4111485) (@lem4111483)). Qed.
Lemma lem4111487 : term206 = True.
Proof. exact (TRANS (@lem4111482) (@lem4111486)). Qed.
Lemma lem4111488 : True = term206.
Proof. exact (SYM (@lem4111487)). Qed.
Lemma lem4111489 : term206.
Proof. exact (EQ_MP (@lem4111488) (@lem0)). Qed.
Lemma lem4111490 : term456.
Proof. exact (@lem4111479 (@lem4111489)). Qed.
Lemma lem4111492 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111493 : term206 = term207.
Proof. exact (@lem4111492 (NUMERAL 0) term20). Qed.
Lemma lem4111494 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111495 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111496 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111495 h1) (fun h1 : term207 = True => @lem4111494)). Qed.
Lemma lem4111497 : term207 = True.
Proof. exact (EQ_MP (@lem4111496) (@lem4111494)). Qed.
Lemma lem4111498 : term206 = True.
Proof. exact (TRANS (@lem4111493) (@lem4111497)). Qed.
Lemma lem4111499 : True = term206.
Proof. exact (SYM (@lem4111498)). Qed.
Lemma lem4111500 : term206.
Proof. exact (EQ_MP (@lem4111499) (@lem0)). Qed.
Lemma lem4111501 : term454 = term457.
Proof. exact (@lem4111490 (@lem4111500)). Qed.
Lemma lem4111503 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4111504 : term187 = term188.
Proof. exact (@lem4111503 term20 term20). Qed.
Lemma lem4111505 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111506 : term190 = term20.
Proof. exact (EQ_MP (@lem4111505) (@lem940073)). Qed.
Lemma lem4111507 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111508 : term188 = term111.
Proof. exact (MK_COMB (@lem4111507) (@lem4111506)). Qed.
Lemma lem4111509 : term187 = term111.
Proof. exact (TRANS (@lem4111504) (@lem4111508)). Qed.
Lemma lem4111511 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111512 : term293 = term97.
Proof. exact (@lem4111511 term20). Qed.
Lemma lem4111513 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4111514 : term458 = term452.
Proof. exact (MK_COMB (@lem4111513) (@lem4111512)). Qed.
Lemma lem4111515 : term457 = term206.
Proof. exact (MK_COMB (@lem4111514) (@lem4111509)). Qed.
Lemma lem4111517 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111518 : term206 = term207.
Proof. exact (@lem4111517 (NUMERAL 0) term20). Qed.
Lemma lem4111519 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111520 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111521 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111520 h1) (fun h1 : term207 = True => @lem4111519)). Qed.
Lemma lem4111522 : term207 = True.
Proof. exact (EQ_MP (@lem4111521) (@lem4111519)). Qed.
Lemma lem4111523 : term206 = True.
Proof. exact (TRANS (@lem4111518) (@lem4111522)). Qed.
Lemma lem4111524 : term457 = True.
Proof. exact (TRANS (@lem4111515) (@lem4111523)). Qed.
Lemma lem4111525 : term454 = True.
Proof. exact (TRANS (@lem4111501) (@lem4111524)). Qed.
Lemma lem4111526 : term206 = True.
Proof. exact (TRANS (@lem4111478) (@lem4111525)). Qed.
Lemma lem4111527 : term451 = True.
Proof. exact (TRANS (@lem4111469) (@lem4111526)). Qed.
Lemma lem4111528 : True = term451.
Proof. exact (SYM (@lem4111527)). Qed.
Lemma lem4111529 : term451.
Proof. exact (EQ_MP (@lem4111528) (@lem0)). Qed.
Lemma lem4111530 (_48296 : int) (h1 : term540 _48296) : term546 _48296.
Proof. exact (conj (@lem4111529) (@lem4111391 _48296 h1)). Qed.
Lemma lem4111532 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4111533 (_48296 : int) : term547 _48296.
Proof. exact (@lem4111532 term111 (term281 _48296)). Qed.
Lemma lem4111534 (_48296 : int) (h1 : term540 _48296) : term548 _48296.
Proof. exact (@lem4111533 _48296 (@lem4111530 _48296 h1)). Qed.
Lemma lem4111535 (_48296 : int) : (term549 _48296) = (term281 _48296).
Proof. exact (@lem1982733 (term281 _48296)). Qed.
Lemma lem4111536 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4111537 (_48296 : int) : (term550 _48296) = (term298 _48296).
Proof. exact (MK_COMB (@lem4111536) (@lem4111535 _48296)). Qed.
Lemma lem4111538 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4111539 (_48296 : int) : (term548 _48296) = (term299 _48296).
Proof. exact (MK_COMB (@lem4111537 _48296) (@lem4111538)). Qed.
Lemma lem4111540 (_48296 : int) (h1 : term540 _48296) : term299 _48296.
Proof. exact (EQ_MP (@lem4111539 _48296) (@lem4111534 _48296 h1)). Qed.
Lemma lem4111541 (_48296 : int) (h1 : term540 _48296) : term551 _48296.
Proof. exact (conj (@lem4111540 _48296 h1) (@lem4111466 _48296 h1)). Qed.
Lemma lem4111543 (x : real) (y : real) : term471 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem4111544 (_48296 : int) : term552 _48296.
Proof. exact (@lem4111543 (term281 _48296) (term270 _48296)). Qed.
Lemma lem4111545 (_48296 : int) (h1 : term540 _48296) : term553 _48296.
Proof. exact (@lem4111544 _48296 (@lem4111541 _48296 h1)). Qed.
Lemma lem4111546 (_48296 : int) : (term554 _48296) = (term538 _48296).
Proof. exact (@lem1982763 (term281 _48296) (real_of_int _48296) term178). Qed.
Lemma lem4111547 (_48296 : int) : (term476 _48296) = (term477 _48296).
Proof. exact (@lem1982713 term178 (real_of_int _48296)). Qed.
Lemma lem4111549 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111550 : term111 = term200.
Proof. exact (@lem4111549 term20). Qed.
Lemma lem4111552 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4111553 : term178 = term179.
Proof. exact (@lem4111552 term20). Qed.
Lemma lem4111554 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4111555 : term478 = term479.
Proof. exact (MK_COMB (@lem4111554) (@lem4111553)). Qed.
Lemma lem4111556 : term480 = term481.
Proof. exact (MK_COMB (@lem4111555) (@lem4111550)). Qed.
Lemma lem4111557 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4111559 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111560 : term206 = term207.
Proof. exact (@lem4111559 (NUMERAL 0) term20). Qed.
Lemma lem4111561 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111562 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111563 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111562 h1) (fun h1 : term207 = True => @lem4111561)). Qed.
Lemma lem4111564 : term207 = True.
Proof. exact (EQ_MP (@lem4111563) (@lem4111561)). Qed.
Lemma lem4111565 : term206 = True.
Proof. exact (TRANS (@lem4111560) (@lem4111564)). Qed.
Lemma lem4111566 : True = term206.
Proof. exact (SYM (@lem4111565)). Qed.
Lemma lem4111567 : term206.
Proof. exact (EQ_MP (@lem4111566) (@lem0)). Qed.
Lemma lem4111568 : term483.
Proof. exact (@lem4111557 (@lem4111567)). Qed.
Lemma lem4111570 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111571 : term206 = term207.
Proof. exact (@lem4111570 (NUMERAL 0) term20). Qed.
Lemma lem4111572 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111573 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111574 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111573 h1) (fun h1 : term207 = True => @lem4111572)). Qed.
Lemma lem4111575 : term207 = True.
Proof. exact (EQ_MP (@lem4111574) (@lem4111572)). Qed.
Lemma lem4111576 : term206 = True.
Proof. exact (TRANS (@lem4111571) (@lem4111575)). Qed.
Lemma lem4111577 : True = term206.
Proof. exact (SYM (@lem4111576)). Qed.
Lemma lem4111578 : term206.
Proof. exact (EQ_MP (@lem4111577) (@lem0)). Qed.
Lemma lem4111579 : term484.
Proof. exact (@lem4111568 (@lem4111578)). Qed.
Lemma lem4111581 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111582 : term206 = term207.
Proof. exact (@lem4111581 (NUMERAL 0) term20). Qed.
Lemma lem4111583 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111584 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111585 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111584 h1) (fun h1 : term207 = True => @lem4111583)). Qed.
Lemma lem4111586 : term207 = True.
Proof. exact (EQ_MP (@lem4111585) (@lem4111583)). Qed.
Lemma lem4111587 : term206 = True.
Proof. exact (TRANS (@lem4111582) (@lem4111586)). Qed.
Lemma lem4111588 : True = term206.
Proof. exact (SYM (@lem4111587)). Qed.
Lemma lem4111589 : term206.
Proof. exact (EQ_MP (@lem4111588) (@lem0)). Qed.
Lemma lem4111590 : term485.
Proof. exact (@lem4111579 (@lem4111589)). Qed.
Lemma lem4111592 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4111593 : term187 = term188.
Proof. exact (@lem4111592 term20 term20). Qed.
Lemma lem4111594 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111595 : term190 = term20.
Proof. exact (EQ_MP (@lem4111594) (@lem940073)). Qed.
Lemma lem4111596 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111597 : term188 = term111.
Proof. exact (MK_COMB (@lem4111596) (@lem4111595)). Qed.
Lemma lem4111598 : term187 = term111.
Proof. exact (TRANS (@lem4111593) (@lem4111597)). Qed.
Lemma lem4111600 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4111601 : term254 = term257.
Proof. exact (@lem4111600 term20 term20). Qed.
Lemma lem4111602 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111603 : term190 = term20.
Proof. exact (EQ_MP (@lem4111602) (@lem940073)). Qed.
Lemma lem4111604 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111605 : term188 = term111.
Proof. exact (MK_COMB (@lem4111604) (@lem4111603)). Qed.
Lemma lem4111606 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4111607 : term257 = term178.
Proof. exact (MK_COMB (@lem4111606) (@lem4111605)). Qed.
Lemma lem4111608 : term254 = term178.
Proof. exact (TRANS (@lem4111601) (@lem4111607)). Qed.
Lemma lem4111609 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4111610 : term486 = term478.
Proof. exact (MK_COMB (@lem4111609) (@lem4111608)). Qed.
Lemma lem4111611 : term487 = term480.
Proof. exact (MK_COMB (@lem4111610) (@lem4111598)). Qed.
Lemma lem4111613 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4111614 : term480 = term97.
Proof. exact (@lem4111613 term20). Qed.
Lemma lem4111615 : term487 = term97.
Proof. exact (TRANS (@lem4111611) (@lem4111614)). Qed.
Lemma lem4111616 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4111617 : term489 = term291.
Proof. exact (MK_COMB (@lem4111616) (@lem4111615)). Qed.
Lemma lem4111618 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4111619 : term490 = term293.
Proof. exact (MK_COMB (@lem4111617) (@lem4111618)). Qed.
Lemma lem4111621 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111622 : term293 = term97.
Proof. exact (@lem4111621 term20). Qed.
Lemma lem4111623 : term490 = term97.
Proof. exact (TRANS (@lem4111619) (@lem4111622)). Qed.
Lemma lem4111625 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4111626 : term187 = term188.
Proof. exact (@lem4111625 term20 term20). Qed.
Lemma lem4111627 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111628 : term190 = term20.
Proof. exact (EQ_MP (@lem4111627) (@lem940073)). Qed.
Lemma lem4111629 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111630 : term188 = term111.
Proof. exact (MK_COMB (@lem4111629) (@lem4111628)). Qed.
Lemma lem4111631 : term187 = term111.
Proof. exact (TRANS (@lem4111626) (@lem4111630)). Qed.
Lemma lem4111632 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4111633 : term295 = term293.
Proof. exact (MK_COMB (@lem4111632) (@lem4111631)). Qed.
Lemma lem4111635 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111636 : term293 = term97.
Proof. exact (@lem4111635 term20). Qed.
Lemma lem4111637 : term295 = term97.
Proof. exact (TRANS (@lem4111633) (@lem4111636)). Qed.
Lemma lem4111638 : term97 = term295.
Proof. exact (SYM (@lem4111637)). Qed.
Lemma lem4111639 : term490 = term295.
Proof. exact (TRANS (@lem4111623) (@lem4111638)). Qed.
Lemma lem4111640 : term481 = term175.
Proof. exact (@lem4111590 (@lem4111639)). Qed.
Lemma lem4111641 : term480 = term175.
Proof. exact (TRANS (@lem4111556) (@lem4111640)). Qed.
Lemma lem4111643 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4111644 : term175 = term97.
Proof. exact (@lem4111643 term97). Qed.
Lemma lem4111645 : term480 = term97.
Proof. exact (TRANS (@lem4111641) (@lem4111644)). Qed.
Lemma lem4111646 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4111647 : term491 = term291.
Proof. exact (MK_COMB (@lem4111646) (@lem4111645)). Qed.
Lemma lem4111648 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4111649 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4111647) (@lem4111648 _48296)). Qed.
Lemma lem4111650 (_48296 : int) : (term476 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4111547 _48296) (@lem4111649 _48296)). Qed.
Lemma lem4111651 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4111652 (_48296 : int) : (term476 _48296) = term97.
Proof. exact (TRANS (@lem4111650 _48296) (@lem4111651 _48296)). Qed.
Lemma lem4111653 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4111654 (_48296 : int) : (term493 _48296) = term139.
Proof. exact (MK_COMB (@lem4111653) (@lem4111652 _48296)). Qed.
Lemma lem4111655 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem4111656 (_48296 : int) : (term538 _48296) = term508.
Proof. exact (MK_COMB (@lem4111654 _48296) (@lem4111655)). Qed.
Lemma lem4111657 (_48296 : int) : (term554 _48296) = term508.
Proof. exact (TRANS (@lem4111546 _48296) (@lem4111656 _48296)). Qed.
Lemma lem4111658 : term508 = term178.
Proof. exact (@lem1982721 term178). Qed.
Lemma lem4111659 (_48296 : int) : (term554 _48296) = term178.
Proof. exact (TRANS (@lem4111657 _48296) (@lem4111658)). Qed.
Lemma lem4111660 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4111661 (_48296 : int) : (term555 _48296) = term510.
Proof. exact (MK_COMB (@lem4111660) (@lem4111659 _48296)). Qed.
Lemma lem4111662 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4111663 (_48296 : int) : (term553 _48296) = term511.
Proof. exact (MK_COMB (@lem4111661 _48296) (@lem4111662)). Qed.
Lemma lem4111664 (_48296 : int) (h1 : term540 _48296) : term511.
Proof. exact (EQ_MP (@lem4111663 _48296) (@lem4111545 _48296 h1)). Qed.
Lemma lem4111666 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4111667 : term511 = term512.
Proof. exact (@lem4111666 term97 term178). Qed.
Lemma lem4111669 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4111670 : term178 = term179.
Proof. exact (@lem4111669 term20). Qed.
Lemma lem4111672 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111673 : term97 = term175.
Proof. exact (@lem4111672 (NUMERAL 0)). Qed.
Lemma lem4111674 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4111675 : term99 = term513.
Proof. exact (MK_COMB (@lem4111674) (@lem4111673)). Qed.
Lemma lem4111676 : term512 = term514.
Proof. exact (MK_COMB (@lem4111675) (@lem4111670)). Qed.
Lemma lem4111677 : term515.
Proof. exact (@lem1980026 term97 term111 term178 term111). Qed.
Lemma lem4111679 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111680 : term206 = term207.
Proof. exact (@lem4111679 (NUMERAL 0) term20). Qed.
Lemma lem4111681 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111682 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111683 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111682 h1) (fun h1 : term207 = True => @lem4111681)). Qed.
Lemma lem4111684 : term207 = True.
Proof. exact (EQ_MP (@lem4111683) (@lem4111681)). Qed.
Lemma lem4111685 : term206 = True.
Proof. exact (TRANS (@lem4111680) (@lem4111684)). Qed.
Lemma lem4111686 : True = term206.
Proof. exact (SYM (@lem4111685)). Qed.
Lemma lem4111687 : term206.
Proof. exact (EQ_MP (@lem4111686) (@lem0)). Qed.
Lemma lem4111688 : term516.
Proof. exact (@lem4111677 (@lem4111687)). Qed.
Lemma lem4111690 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111691 : term206 = term207.
Proof. exact (@lem4111690 (NUMERAL 0) term20). Qed.
Lemma lem4111692 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111693 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111694 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111693 h1) (fun h1 : term207 = True => @lem4111692)). Qed.
Lemma lem4111695 : term207 = True.
Proof. exact (EQ_MP (@lem4111694) (@lem4111692)). Qed.
Lemma lem4111696 : term206 = True.
Proof. exact (TRANS (@lem4111691) (@lem4111695)). Qed.
Lemma lem4111697 : True = term206.
Proof. exact (SYM (@lem4111696)). Qed.
Lemma lem4111698 : term206.
Proof. exact (EQ_MP (@lem4111697) (@lem0)). Qed.
Lemma lem4111699 : term514 = term517.
Proof. exact (@lem4111688 (@lem4111698)). Qed.
Lemma lem4111701 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4111702 : term254 = term257.
Proof. exact (@lem4111701 term20 term20). Qed.
Lemma lem4111703 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111704 : term190 = term20.
Proof. exact (EQ_MP (@lem4111703) (@lem940073)). Qed.
Lemma lem4111705 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111706 : term188 = term111.
Proof. exact (MK_COMB (@lem4111705) (@lem4111704)). Qed.
Lemma lem4111707 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4111708 : term257 = term178.
Proof. exact (MK_COMB (@lem4111707) (@lem4111706)). Qed.
Lemma lem4111709 : term254 = term178.
Proof. exact (TRANS (@lem4111702) (@lem4111708)). Qed.
Lemma lem4111711 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111712 : term293 = term97.
Proof. exact (@lem4111711 term20). Qed.
Lemma lem4111713 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4111714 : term518 = term99.
Proof. exact (MK_COMB (@lem4111713) (@lem4111712)). Qed.
Lemma lem4111715 : term517 = term512.
Proof. exact (MK_COMB (@lem4111714) (@lem4111709)). Qed.
Lemma lem4111717 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4111718 : term512 = term521.
Proof. exact (@lem4111717 (NUMERAL 0) term20). Qed.
Lemma lem4111719 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111720 (h1 : term208 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4111721 : (term208 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111720 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem4111719)). Qed.
Lemma lem4111722 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4111721) (@lem4111719)). Qed.
Lemma lem4111723 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4111724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4111725 : term522 = (and True).
Proof. exact (MK_COMB (@lem4111724) (@lem4111723)). Qed.
Lemma lem4111726 : term521 = (True /\ False).
Proof. exact (MK_COMB (@lem4111725) (@lem4111722)). Qed.
Lemma lem4111728 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4111729 : term521 = False.
Proof. exact (TRANS (@lem4111726) (@lem4111728)). Qed.
Lemma lem4111730 : term512 = False.
Proof. exact (TRANS (@lem4111718) (@lem4111729)). Qed.
Lemma lem4111731 : term517 = False.
Proof. exact (TRANS (@lem4111715) (@lem4111730)). Qed.
Lemma lem4111732 : term514 = False.
Proof. exact (TRANS (@lem4111699) (@lem4111731)). Qed.
Lemma lem4111733 : term512 = False.
Proof. exact (TRANS (@lem4111676) (@lem4111732)). Qed.
Lemma lem4111734 : term511 = False.
Proof. exact (TRANS (@lem4111667) (@lem4111733)). Qed.
Lemma lem4111735 (_48296 : int) (h1 : term540 _48296) : False.
Proof. exact (EQ_MP (@lem4111734) (@lem4111664 _48296 h1)). Qed.
Lemma lem4111736 (_48296 : int) (h1 : term439 _48296) : False.
Proof. exact (or_elim (@lem4111035 _48296 h1) (fun h0 : term523 _48296 => @lem4111385 _48296 h0) (fun h0 : term540 _48296 => @lem4111735 _48296 h0)). Qed.
Lemma lem4111737 (_48296 : int) (h1 : term435 _48296) : term435 _48296.
Proof. exact (h1). Qed.
Lemma lem4111738 (_48296 : int) (h1 : term556 _48296) : term556 _48296.
Proof. exact (h1). Qed.
Lemma lem4111739 (_48296 : int) (h1 : term556 _48296) : term436 _48296.
Proof. exact (proj2 (@lem4111738 _48296 h1)). Qed.
Lemma lem4111741 (_48296 : int) (h1 : term556 _48296) : term312 _48296.
Proof. exact (proj2 (@lem4111739 _48296 h1)). Qed.
Lemma lem4111742 (_48296 : int) (h1 : term556 _48296) : term343 _48296.
Proof. exact (proj1 (@lem4111739 _48296 h1)). Qed.
Lemma lem4111743 (_48296 : int) (h1 : term556 _48296) : term248 _48296.
Proof. exact (proj2 (@lem4111742 _48296 h1)). Qed.
Lemma lem4111746 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4111747 : term451 = term206.
Proof. exact (@lem4111746 term97 term111). Qed.
Lemma lem4111749 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111750 : term111 = term200.
Proof. exact (@lem4111749 term20). Qed.
Lemma lem4111752 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111753 : term97 = term175.
Proof. exact (@lem4111752 (NUMERAL 0)). Qed.
Lemma lem4111754 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4111755 : term452 = term453.
Proof. exact (MK_COMB (@lem4111754) (@lem4111753)). Qed.
Lemma lem4111756 : term206 = term454.
Proof. exact (MK_COMB (@lem4111755) (@lem4111750)). Qed.
Lemma lem4111757 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4111759 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111760 : term206 = term207.
Proof. exact (@lem4111759 (NUMERAL 0) term20). Qed.
Lemma lem4111761 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111762 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111763 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111762 h1) (fun h1 : term207 = True => @lem4111761)). Qed.
Lemma lem4111764 : term207 = True.
Proof. exact (EQ_MP (@lem4111763) (@lem4111761)). Qed.
Lemma lem4111765 : term206 = True.
Proof. exact (TRANS (@lem4111760) (@lem4111764)). Qed.
Lemma lem4111766 : True = term206.
Proof. exact (SYM (@lem4111765)). Qed.
Lemma lem4111767 : term206.
Proof. exact (EQ_MP (@lem4111766) (@lem0)). Qed.
Lemma lem4111768 : term456.
Proof. exact (@lem4111757 (@lem4111767)). Qed.
Lemma lem4111770 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111771 : term206 = term207.
Proof. exact (@lem4111770 (NUMERAL 0) term20). Qed.
Lemma lem4111772 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111773 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111774 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111773 h1) (fun h1 : term207 = True => @lem4111772)). Qed.
Lemma lem4111775 : term207 = True.
Proof. exact (EQ_MP (@lem4111774) (@lem4111772)). Qed.
Lemma lem4111776 : term206 = True.
Proof. exact (TRANS (@lem4111771) (@lem4111775)). Qed.
Lemma lem4111777 : True = term206.
Proof. exact (SYM (@lem4111776)). Qed.
Lemma lem4111778 : term206.
Proof. exact (EQ_MP (@lem4111777) (@lem0)). Qed.
Lemma lem4111779 : term454 = term457.
Proof. exact (@lem4111768 (@lem4111778)). Qed.
Lemma lem4111781 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4111782 : term187 = term188.
Proof. exact (@lem4111781 term20 term20). Qed.
Lemma lem4111783 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111784 : term190 = term20.
Proof. exact (EQ_MP (@lem4111783) (@lem940073)). Qed.
Lemma lem4111785 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111786 : term188 = term111.
Proof. exact (MK_COMB (@lem4111785) (@lem4111784)). Qed.
Lemma lem4111787 : term187 = term111.
Proof. exact (TRANS (@lem4111782) (@lem4111786)). Qed.
Lemma lem4111789 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111790 : term293 = term97.
Proof. exact (@lem4111789 term20). Qed.
Lemma lem4111791 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4111792 : term458 = term452.
Proof. exact (MK_COMB (@lem4111791) (@lem4111790)). Qed.
Lemma lem4111793 : term457 = term206.
Proof. exact (MK_COMB (@lem4111792) (@lem4111787)). Qed.
Lemma lem4111795 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111796 : term206 = term207.
Proof. exact (@lem4111795 (NUMERAL 0) term20). Qed.
Lemma lem4111797 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111798 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111799 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111798 h1) (fun h1 : term207 = True => @lem4111797)). Qed.
Lemma lem4111800 : term207 = True.
Proof. exact (EQ_MP (@lem4111799) (@lem4111797)). Qed.
Lemma lem4111801 : term206 = True.
Proof. exact (TRANS (@lem4111796) (@lem4111800)). Qed.
Lemma lem4111802 : term457 = True.
Proof. exact (TRANS (@lem4111793) (@lem4111801)). Qed.
Lemma lem4111803 : term454 = True.
Proof. exact (TRANS (@lem4111779) (@lem4111802)). Qed.
Lemma lem4111804 : term206 = True.
Proof. exact (TRANS (@lem4111756) (@lem4111803)). Qed.
Lemma lem4111805 : term451 = True.
Proof. exact (TRANS (@lem4111747) (@lem4111804)). Qed.
Lemma lem4111806 : True = term451.
Proof. exact (SYM (@lem4111805)). Qed.
Lemma lem4111807 : term451.
Proof. exact (EQ_MP (@lem4111806) (@lem0)). Qed.
Lemma lem4111808 (_48296 : int) (h1 : term556 _48296) : term459 _48296.
Proof. exact (conj (@lem4111807) (@lem4111743 _48296 h1)). Qed.
Lemma lem4111810 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4111811 (_48296 : int) : term461 _48296.
Proof. exact (@lem4111810 term111 (term245 _48296)). Qed.
Lemma lem4111812 (_48296 : int) (h1 : term556 _48296) : term462 _48296.
Proof. exact (@lem4111811 _48296 (@lem4111808 _48296 h1)). Qed.
Lemma lem4111813 (_48296 : int) : (term463 _48296) = (term245 _48296).
Proof. exact (@lem1982733 (term245 _48296)). Qed.
Lemma lem4111814 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4111815 (_48296 : int) : (term464 _48296) = (term247 _48296).
Proof. exact (MK_COMB (@lem4111814) (@lem4111813 _48296)). Qed.
Lemma lem4111816 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4111817 (_48296 : int) : (term462 _48296) = (term248 _48296).
Proof. exact (MK_COMB (@lem4111815 _48296) (@lem4111816)). Qed.
Lemma lem4111818 (_48296 : int) (h1 : term556 _48296) : term248 _48296.
Proof. exact (EQ_MP (@lem4111817 _48296) (@lem4111812 _48296 h1)). Qed.
Lemma lem4111820 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4111821 : term451 = term206.
Proof. exact (@lem4111820 term97 term111). Qed.
Lemma lem4111823 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111824 : term111 = term200.
Proof. exact (@lem4111823 term20). Qed.
Lemma lem4111826 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111827 : term97 = term175.
Proof. exact (@lem4111826 (NUMERAL 0)). Qed.
Lemma lem4111828 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4111829 : term452 = term453.
Proof. exact (MK_COMB (@lem4111828) (@lem4111827)). Qed.
Lemma lem4111830 : term206 = term454.
Proof. exact (MK_COMB (@lem4111829) (@lem4111824)). Qed.
Lemma lem4111831 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4111833 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111834 : term206 = term207.
Proof. exact (@lem4111833 (NUMERAL 0) term20). Qed.
Lemma lem4111835 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111836 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111837 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111836 h1) (fun h1 : term207 = True => @lem4111835)). Qed.
Lemma lem4111838 : term207 = True.
Proof. exact (EQ_MP (@lem4111837) (@lem4111835)). Qed.
Lemma lem4111839 : term206 = True.
Proof. exact (TRANS (@lem4111834) (@lem4111838)). Qed.
Lemma lem4111840 : True = term206.
Proof. exact (SYM (@lem4111839)). Qed.
Lemma lem4111841 : term206.
Proof. exact (EQ_MP (@lem4111840) (@lem0)). Qed.
Lemma lem4111842 : term456.
Proof. exact (@lem4111831 (@lem4111841)). Qed.
Lemma lem4111844 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111845 : term206 = term207.
Proof. exact (@lem4111844 (NUMERAL 0) term20). Qed.
Lemma lem4111846 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111847 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111848 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111847 h1) (fun h1 : term207 = True => @lem4111846)). Qed.
Lemma lem4111849 : term207 = True.
Proof. exact (EQ_MP (@lem4111848) (@lem4111846)). Qed.
Lemma lem4111850 : term206 = True.
Proof. exact (TRANS (@lem4111845) (@lem4111849)). Qed.
Lemma lem4111851 : True = term206.
Proof. exact (SYM (@lem4111850)). Qed.
Lemma lem4111852 : term206.
Proof. exact (EQ_MP (@lem4111851) (@lem0)). Qed.
Lemma lem4111853 : term454 = term457.
Proof. exact (@lem4111842 (@lem4111852)). Qed.
Lemma lem4111855 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4111856 : term187 = term188.
Proof. exact (@lem4111855 term20 term20). Qed.
Lemma lem4111857 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111858 : term190 = term20.
Proof. exact (EQ_MP (@lem4111857) (@lem940073)). Qed.
Lemma lem4111859 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111860 : term188 = term111.
Proof. exact (MK_COMB (@lem4111859) (@lem4111858)). Qed.
Lemma lem4111861 : term187 = term111.
Proof. exact (TRANS (@lem4111856) (@lem4111860)). Qed.
Lemma lem4111863 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111864 : term293 = term97.
Proof. exact (@lem4111863 term20). Qed.
Lemma lem4111865 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4111866 : term458 = term452.
Proof. exact (MK_COMB (@lem4111865) (@lem4111864)). Qed.
Lemma lem4111867 : term457 = term206.
Proof. exact (MK_COMB (@lem4111866) (@lem4111861)). Qed.
Lemma lem4111869 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111870 : term206 = term207.
Proof. exact (@lem4111869 (NUMERAL 0) term20). Qed.
Lemma lem4111871 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111872 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111873 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111872 h1) (fun h1 : term207 = True => @lem4111871)). Qed.
Lemma lem4111874 : term207 = True.
Proof. exact (EQ_MP (@lem4111873) (@lem4111871)). Qed.
Lemma lem4111875 : term206 = True.
Proof. exact (TRANS (@lem4111870) (@lem4111874)). Qed.
Lemma lem4111876 : term457 = True.
Proof. exact (TRANS (@lem4111867) (@lem4111875)). Qed.
Lemma lem4111877 : term454 = True.
Proof. exact (TRANS (@lem4111853) (@lem4111876)). Qed.
Lemma lem4111878 : term206 = True.
Proof. exact (TRANS (@lem4111830) (@lem4111877)). Qed.
Lemma lem4111879 : term451 = True.
Proof. exact (TRANS (@lem4111821) (@lem4111878)). Qed.
Lemma lem4111880 : True = term451.
Proof. exact (SYM (@lem4111879)). Qed.
Lemma lem4111881 : term451.
Proof. exact (EQ_MP (@lem4111880) (@lem0)). Qed.
Lemma lem4111882 (_48296 : int) (h1 : term556 _48296) : term465 _48296.
Proof. exact (conj (@lem4111881) (@lem4111741 _48296 h1)). Qed.
Lemma lem4111884 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4111885 (_48296 : int) : term466 _48296.
Proof. exact (@lem4111884 term111 (term309 _48296)). Qed.
Lemma lem4111886 (_48296 : int) (h1 : term556 _48296) : term467 _48296.
Proof. exact (@lem4111885 _48296 (@lem4111882 _48296 h1)). Qed.
Lemma lem4111887 (_48296 : int) : (term468 _48296) = (term309 _48296).
Proof. exact (@lem1982733 (term309 _48296)). Qed.
Lemma lem4111888 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4111889 (_48296 : int) : (term469 _48296) = (term311 _48296).
Proof. exact (MK_COMB (@lem4111888) (@lem4111887 _48296)). Qed.
Lemma lem4111890 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4111891 (_48296 : int) : (term467 _48296) = (term312 _48296).
Proof. exact (MK_COMB (@lem4111889 _48296) (@lem4111890)). Qed.
Lemma lem4111892 (_48296 : int) (h1 : term556 _48296) : term312 _48296.
Proof. exact (EQ_MP (@lem4111891 _48296) (@lem4111886 _48296 h1)). Qed.
Lemma lem4111893 (_48296 : int) (h1 : term556 _48296) : term470 _48296.
Proof. exact (conj (@lem4111892 _48296 h1) (@lem4111818 _48296 h1)). Qed.
Lemma lem4111895 (x : real) (y : real) : term471 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem4111896 (_48296 : int) : term472 _48296.
Proof. exact (@lem4111895 (term309 _48296) (term245 _48296)). Qed.
Lemma lem4111897 (_48296 : int) (h1 : term556 _48296) : term473 _48296.
Proof. exact (@lem4111896 _48296 (@lem4111893 _48296 h1)). Qed.
Lemma lem4111898 (_48296 : int) : (term474 _48296) = (term475 _48296).
Proof. exact (@lem1982753 (term281 _48296) (real_of_int _48296) term111 term241). Qed.
Lemma lem4111899 (_48296 : int) : (term476 _48296) = (term477 _48296).
Proof. exact (@lem1982713 term178 (real_of_int _48296)). Qed.
Lemma lem4111901 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4111902 : term111 = term200.
Proof. exact (@lem4111901 term20). Qed.
Lemma lem4111904 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4111905 : term178 = term179.
Proof. exact (@lem4111904 term20). Qed.
Lemma lem4111906 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4111907 : term478 = term479.
Proof. exact (MK_COMB (@lem4111906) (@lem4111905)). Qed.
Lemma lem4111908 : term480 = term481.
Proof. exact (MK_COMB (@lem4111907) (@lem4111902)). Qed.
Lemma lem4111909 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4111911 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111912 : term206 = term207.
Proof. exact (@lem4111911 (NUMERAL 0) term20). Qed.
Lemma lem4111913 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111914 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111915 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111914 h1) (fun h1 : term207 = True => @lem4111913)). Qed.
Lemma lem4111916 : term207 = True.
Proof. exact (EQ_MP (@lem4111915) (@lem4111913)). Qed.
Lemma lem4111917 : term206 = True.
Proof. exact (TRANS (@lem4111912) (@lem4111916)). Qed.
Lemma lem4111918 : True = term206.
Proof. exact (SYM (@lem4111917)). Qed.
Lemma lem4111919 : term206.
Proof. exact (EQ_MP (@lem4111918) (@lem0)). Qed.
Lemma lem4111920 : term483.
Proof. exact (@lem4111909 (@lem4111919)). Qed.
Lemma lem4111922 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111923 : term206 = term207.
Proof. exact (@lem4111922 (NUMERAL 0) term20). Qed.
Lemma lem4111924 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111925 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111926 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111925 h1) (fun h1 : term207 = True => @lem4111924)). Qed.
Lemma lem4111927 : term207 = True.
Proof. exact (EQ_MP (@lem4111926) (@lem4111924)). Qed.
Lemma lem4111928 : term206 = True.
Proof. exact (TRANS (@lem4111923) (@lem4111927)). Qed.
Lemma lem4111929 : True = term206.
Proof. exact (SYM (@lem4111928)). Qed.
Lemma lem4111930 : term206.
Proof. exact (EQ_MP (@lem4111929) (@lem0)). Qed.
Lemma lem4111931 : term484.
Proof. exact (@lem4111920 (@lem4111930)). Qed.
Lemma lem4111933 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4111934 : term206 = term207.
Proof. exact (@lem4111933 (NUMERAL 0) term20). Qed.
Lemma lem4111935 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4111936 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4111937 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4111936 h1) (fun h1 : term207 = True => @lem4111935)). Qed.
Lemma lem4111938 : term207 = True.
Proof. exact (EQ_MP (@lem4111937) (@lem4111935)). Qed.
Lemma lem4111939 : term206 = True.
Proof. exact (TRANS (@lem4111934) (@lem4111938)). Qed.
Lemma lem4111940 : True = term206.
Proof. exact (SYM (@lem4111939)). Qed.
Lemma lem4111941 : term206.
Proof. exact (EQ_MP (@lem4111940) (@lem0)). Qed.
Lemma lem4111942 : term485.
Proof. exact (@lem4111931 (@lem4111941)). Qed.
Lemma lem4111944 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4111945 : term187 = term188.
Proof. exact (@lem4111944 term20 term20). Qed.
Lemma lem4111946 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111947 : term190 = term20.
Proof. exact (EQ_MP (@lem4111946) (@lem940073)). Qed.
Lemma lem4111948 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111949 : term188 = term111.
Proof. exact (MK_COMB (@lem4111948) (@lem4111947)). Qed.
Lemma lem4111950 : term187 = term111.
Proof. exact (TRANS (@lem4111945) (@lem4111949)). Qed.
Lemma lem4111952 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4111953 : term254 = term257.
Proof. exact (@lem4111952 term20 term20). Qed.
Lemma lem4111954 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111955 : term190 = term20.
Proof. exact (EQ_MP (@lem4111954) (@lem940073)). Qed.
Lemma lem4111956 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111957 : term188 = term111.
Proof. exact (MK_COMB (@lem4111956) (@lem4111955)). Qed.
Lemma lem4111958 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4111959 : term257 = term178.
Proof. exact (MK_COMB (@lem4111958) (@lem4111957)). Qed.
Lemma lem4111960 : term254 = term178.
Proof. exact (TRANS (@lem4111953) (@lem4111959)). Qed.
Lemma lem4111961 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4111962 : term486 = term478.
Proof. exact (MK_COMB (@lem4111961) (@lem4111960)). Qed.
Lemma lem4111963 : term487 = term480.
Proof. exact (MK_COMB (@lem4111962) (@lem4111950)). Qed.
Lemma lem4111965 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4111966 : term480 = term97.
Proof. exact (@lem4111965 term20). Qed.
Lemma lem4111967 : term487 = term97.
Proof. exact (TRANS (@lem4111963) (@lem4111966)). Qed.
Lemma lem4111968 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4111969 : term489 = term291.
Proof. exact (MK_COMB (@lem4111968) (@lem4111967)). Qed.
Lemma lem4111970 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4111971 : term490 = term293.
Proof. exact (MK_COMB (@lem4111969) (@lem4111970)). Qed.
Lemma lem4111973 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111974 : term293 = term97.
Proof. exact (@lem4111973 term20). Qed.
Lemma lem4111975 : term490 = term97.
Proof. exact (TRANS (@lem4111971) (@lem4111974)). Qed.
Lemma lem4111977 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4111978 : term187 = term188.
Proof. exact (@lem4111977 term20 term20). Qed.
Lemma lem4111979 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4111980 : term190 = term20.
Proof. exact (EQ_MP (@lem4111979) (@lem940073)). Qed.
Lemma lem4111981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4111982 : term188 = term111.
Proof. exact (MK_COMB (@lem4111981) (@lem4111980)). Qed.
Lemma lem4111983 : term187 = term111.
Proof. exact (TRANS (@lem4111978) (@lem4111982)). Qed.
Lemma lem4111984 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4111985 : term295 = term293.
Proof. exact (MK_COMB (@lem4111984) (@lem4111983)). Qed.
Lemma lem4111987 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4111988 : term293 = term97.
Proof. exact (@lem4111987 term20). Qed.
Lemma lem4111989 : term295 = term97.
Proof. exact (TRANS (@lem4111985) (@lem4111988)). Qed.
Lemma lem4111990 : term97 = term295.
Proof. exact (SYM (@lem4111989)). Qed.
Lemma lem4111991 : term490 = term295.
Proof. exact (TRANS (@lem4111975) (@lem4111990)). Qed.
Lemma lem4111992 : term481 = term175.
Proof. exact (@lem4111942 (@lem4111991)). Qed.
Lemma lem4111993 : term480 = term175.
Proof. exact (TRANS (@lem4111908) (@lem4111992)). Qed.
Lemma lem4111995 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4111996 : term175 = term97.
Proof. exact (@lem4111995 term97). Qed.
Lemma lem4111997 : term480 = term97.
Proof. exact (TRANS (@lem4111993) (@lem4111996)). Qed.
Lemma lem4111998 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4111999 : term491 = term291.
Proof. exact (MK_COMB (@lem4111998) (@lem4111997)). Qed.
Lemma lem4112000 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4112001 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4111999) (@lem4112000 _48296)). Qed.
Lemma lem4112002 (_48296 : int) : (term476 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4111899 _48296) (@lem4112001 _48296)). Qed.
Lemma lem4112003 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4112004 (_48296 : int) : (term476 _48296) = term97.
Proof. exact (TRANS (@lem4112002 _48296) (@lem4112003 _48296)). Qed.
Lemma lem4112005 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4112006 (_48296 : int) : (term493 _48296) = term139.
Proof. exact (MK_COMB (@lem4112005) (@lem4112004 _48296)). Qed.
Lemma lem4112008 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4112009 : term241 = term244.
Proof. exact (@lem4112008 term218). Qed.
Lemma lem4112011 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112012 : term111 = term200.
Proof. exact (@lem4112011 term20). Qed.
Lemma lem4112013 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4112014 : term113 = term201.
Proof. exact (MK_COMB (@lem4112013) (@lem4112012)). Qed.
Lemma lem4112015 : term494 = term495.
Proof. exact (MK_COMB (@lem4112014) (@lem4112009)). Qed.
Lemma lem4112016 : term496.
Proof. exact (@lem1981473 term111 term111 term241 term111 term178 term111). Qed.
Lemma lem4112018 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112019 : term206 = term207.
Proof. exact (@lem4112018 (NUMERAL 0) term20). Qed.
Lemma lem4112020 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112021 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112022 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112021 h1) (fun h1 : term207 = True => @lem4112020)). Qed.
Lemma lem4112023 : term207 = True.
Proof. exact (EQ_MP (@lem4112022) (@lem4112020)). Qed.
Lemma lem4112024 : term206 = True.
Proof. exact (TRANS (@lem4112019) (@lem4112023)). Qed.
Lemma lem4112025 : True = term206.
Proof. exact (SYM (@lem4112024)). Qed.
Lemma lem4112026 : term206.
Proof. exact (EQ_MP (@lem4112025) (@lem0)). Qed.
Lemma lem4112027 : term497.
Proof. exact (@lem4112016 (@lem4112026)). Qed.
Lemma lem4112029 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112030 : term206 = term207.
Proof. exact (@lem4112029 (NUMERAL 0) term20). Qed.
Lemma lem4112031 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112032 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112033 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112032 h1) (fun h1 : term207 = True => @lem4112031)). Qed.
Lemma lem4112034 : term207 = True.
Proof. exact (EQ_MP (@lem4112033) (@lem4112031)). Qed.
Lemma lem4112035 : term206 = True.
Proof. exact (TRANS (@lem4112030) (@lem4112034)). Qed.
Lemma lem4112036 : True = term206.
Proof. exact (SYM (@lem4112035)). Qed.
Lemma lem4112037 : term206.
Proof. exact (EQ_MP (@lem4112036) (@lem0)). Qed.
Lemma lem4112038 : term498.
Proof. exact (@lem4112027 (@lem4112037)). Qed.
Lemma lem4112040 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112041 : term206 = term207.
Proof. exact (@lem4112040 (NUMERAL 0) term20). Qed.
Lemma lem4112042 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112043 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112044 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112043 h1) (fun h1 : term207 = True => @lem4112042)). Qed.
Lemma lem4112045 : term207 = True.
Proof. exact (EQ_MP (@lem4112044) (@lem4112042)). Qed.
Lemma lem4112046 : term206 = True.
Proof. exact (TRANS (@lem4112041) (@lem4112045)). Qed.
Lemma lem4112047 : True = term206.
Proof. exact (SYM (@lem4112046)). Qed.
Lemma lem4112048 : term206.
Proof. exact (EQ_MP (@lem4112047) (@lem0)). Qed.
Lemma lem4112049 : term499.
Proof. exact (@lem4112038 (@lem4112048)). Qed.
Lemma lem4112051 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4112052 : term500 = term501.
Proof. exact (@lem4112051 term218 term20). Qed.
Lemma lem4112053 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4112054 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4112055 : term225 = term218.
Proof. exact (EQ_MP (@lem4112054) (@lem4112053)). Qed.
Lemma lem4112056 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112057 : term223 = term204.
Proof. exact (MK_COMB (@lem4112056) (@lem4112055)). Qed.
Lemma lem4112058 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112059 : term501 = term241.
Proof. exact (MK_COMB (@lem4112058) (@lem4112057)). Qed.
Lemma lem4112060 : term500 = term241.
Proof. exact (TRANS (@lem4112052) (@lem4112059)). Qed.
Lemma lem4112062 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4112063 : term187 = term188.
Proof. exact (@lem4112062 term20 term20). Qed.
Lemma lem4112064 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112065 : term190 = term20.
Proof. exact (EQ_MP (@lem4112064) (@lem940073)). Qed.
Lemma lem4112066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112067 : term188 = term111.
Proof. exact (MK_COMB (@lem4112066) (@lem4112065)). Qed.
Lemma lem4112068 : term187 = term111.
Proof. exact (TRANS (@lem4112063) (@lem4112067)). Qed.
Lemma lem4112069 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4112070 : term212 = term113.
Proof. exact (MK_COMB (@lem4112069) (@lem4112068)). Qed.
Lemma lem4112071 : term502 = term494.
Proof. exact (MK_COMB (@lem4112070) (@lem4112060)). Qed.
Lemma lem4112074 : term503 = term178.
Proof. exact (@lem1367771 term20 term20). Qed.
Lemma lem4112075 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem4112076 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem4112077 : term217 = term218.
Proof. exact (EQ_MP (@lem4112076) (@lem4112075)). Qed.
Lemma lem4112078 : term218 = term217.
Proof. exact (SYM (@lem4112077)). Qed.
Lemma lem4112079 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112080 : term204 = term214.
Proof. exact (MK_COMB (@lem4112079) (@lem4112078)). Qed.
Lemma lem4112081 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112082 : term241 = term504.
Proof. exact (MK_COMB (@lem4112081) (@lem4112080)). Qed.
Lemma lem4112083 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem4112084 : term494 = term503.
Proof. exact (MK_COMB (@lem4112083) (@lem4112082)). Qed.
Lemma lem4112085 : term494 = term178.
Proof. exact (TRANS (@lem4112084) (@lem4112074)). Qed.
Lemma lem4112086 : term502 = term178.
Proof. exact (TRANS (@lem4112071) (@lem4112085)). Qed.
Lemma lem4112087 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4112088 : term505 = term180.
Proof. exact (MK_COMB (@lem4112087) (@lem4112086)). Qed.
Lemma lem4112089 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4112090 : term506 = term254.
Proof. exact (MK_COMB (@lem4112088) (@lem4112089)). Qed.
Lemma lem4112092 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4112093 : term254 = term257.
Proof. exact (@lem4112092 term20 term20). Qed.
Lemma lem4112094 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112095 : term190 = term20.
Proof. exact (EQ_MP (@lem4112094) (@lem940073)). Qed.
Lemma lem4112096 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112097 : term188 = term111.
Proof. exact (MK_COMB (@lem4112096) (@lem4112095)). Qed.
Lemma lem4112098 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112099 : term257 = term178.
Proof. exact (MK_COMB (@lem4112098) (@lem4112097)). Qed.
Lemma lem4112100 : term254 = term178.
Proof. exact (TRANS (@lem4112093) (@lem4112099)). Qed.
Lemma lem4112101 : term506 = term178.
Proof. exact (TRANS (@lem4112090) (@lem4112100)). Qed.
Lemma lem4112103 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4112104 : term187 = term188.
Proof. exact (@lem4112103 term20 term20). Qed.
Lemma lem4112105 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112106 : term190 = term20.
Proof. exact (EQ_MP (@lem4112105) (@lem940073)). Qed.
Lemma lem4112107 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112108 : term188 = term111.
Proof. exact (MK_COMB (@lem4112107) (@lem4112106)). Qed.
Lemma lem4112109 : term187 = term111.
Proof. exact (TRANS (@lem4112104) (@lem4112108)). Qed.
Lemma lem4112110 : term180 = term180.
Proof. exact (eq_refl term180). Qed.
Lemma lem4112111 : term507 = term254.
Proof. exact (MK_COMB (@lem4112110) (@lem4112109)). Qed.
Lemma lem4112113 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4112114 : term254 = term257.
Proof. exact (@lem4112113 term20 term20). Qed.
Lemma lem4112115 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112116 : term190 = term20.
Proof. exact (EQ_MP (@lem4112115) (@lem940073)). Qed.
Lemma lem4112117 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112118 : term188 = term111.
Proof. exact (MK_COMB (@lem4112117) (@lem4112116)). Qed.
Lemma lem4112119 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112120 : term257 = term178.
Proof. exact (MK_COMB (@lem4112119) (@lem4112118)). Qed.
Lemma lem4112121 : term254 = term178.
Proof. exact (TRANS (@lem4112114) (@lem4112120)). Qed.
Lemma lem4112122 : term507 = term178.
Proof. exact (TRANS (@lem4112111) (@lem4112121)). Qed.
Lemma lem4112123 : term178 = term507.
Proof. exact (SYM (@lem4112122)). Qed.
Lemma lem4112124 : term506 = term507.
Proof. exact (TRANS (@lem4112101) (@lem4112123)). Qed.
Lemma lem4112125 : term495 = term179.
Proof. exact (@lem4112049 (@lem4112124)). Qed.
Lemma lem4112126 : term494 = term179.
Proof. exact (TRANS (@lem4112015) (@lem4112125)). Qed.
Lemma lem4112128 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4112129 : term179 = term178.
Proof. exact (@lem4112128 term178). Qed.
Lemma lem4112130 : term494 = term178.
Proof. exact (TRANS (@lem4112126) (@lem4112129)). Qed.
Lemma lem4112131 (_48296 : int) : (term475 _48296) = term508.
Proof. exact (MK_COMB (@lem4112006 _48296) (@lem4112130)). Qed.
Lemma lem4112132 (_48296 : int) : (term474 _48296) = term508.
Proof. exact (TRANS (@lem4111898 _48296) (@lem4112131 _48296)). Qed.
Lemma lem4112133 : term508 = term178.
Proof. exact (@lem1982721 term178). Qed.
Lemma lem4112134 (_48296 : int) : (term474 _48296) = term178.
Proof. exact (TRANS (@lem4112132 _48296) (@lem4112133)). Qed.
Lemma lem4112135 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4112136 (_48296 : int) : (term509 _48296) = term510.
Proof. exact (MK_COMB (@lem4112135) (@lem4112134 _48296)). Qed.
Lemma lem4112137 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4112138 (_48296 : int) : (term473 _48296) = term511.
Proof. exact (MK_COMB (@lem4112136 _48296) (@lem4112137)). Qed.
Lemma lem4112139 (_48296 : int) (h1 : term556 _48296) : term511.
Proof. exact (EQ_MP (@lem4112138 _48296) (@lem4111897 _48296 h1)). Qed.
Lemma lem4112141 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4112142 : term511 = term512.
Proof. exact (@lem4112141 term97 term178). Qed.
Lemma lem4112144 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4112145 : term178 = term179.
Proof. exact (@lem4112144 term20). Qed.
Lemma lem4112147 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112148 : term97 = term175.
Proof. exact (@lem4112147 (NUMERAL 0)). Qed.
Lemma lem4112149 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4112150 : term99 = term513.
Proof. exact (MK_COMB (@lem4112149) (@lem4112148)). Qed.
Lemma lem4112151 : term512 = term514.
Proof. exact (MK_COMB (@lem4112150) (@lem4112145)). Qed.
Lemma lem4112152 : term515.
Proof. exact (@lem1980026 term97 term111 term178 term111). Qed.
Lemma lem4112154 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112155 : term206 = term207.
Proof. exact (@lem4112154 (NUMERAL 0) term20). Qed.
Lemma lem4112156 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112157 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112158 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112157 h1) (fun h1 : term207 = True => @lem4112156)). Qed.
Lemma lem4112159 : term207 = True.
Proof. exact (EQ_MP (@lem4112158) (@lem4112156)). Qed.
Lemma lem4112160 : term206 = True.
Proof. exact (TRANS (@lem4112155) (@lem4112159)). Qed.
Lemma lem4112161 : True = term206.
Proof. exact (SYM (@lem4112160)). Qed.
Lemma lem4112162 : term206.
Proof. exact (EQ_MP (@lem4112161) (@lem0)). Qed.
Lemma lem4112163 : term516.
Proof. exact (@lem4112152 (@lem4112162)). Qed.
Lemma lem4112165 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112166 : term206 = term207.
Proof. exact (@lem4112165 (NUMERAL 0) term20). Qed.
Lemma lem4112167 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112168 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112169 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112168 h1) (fun h1 : term207 = True => @lem4112167)). Qed.
Lemma lem4112170 : term207 = True.
Proof. exact (EQ_MP (@lem4112169) (@lem4112167)). Qed.
Lemma lem4112171 : term206 = True.
Proof. exact (TRANS (@lem4112166) (@lem4112170)). Qed.
Lemma lem4112172 : True = term206.
Proof. exact (SYM (@lem4112171)). Qed.
Lemma lem4112173 : term206.
Proof. exact (EQ_MP (@lem4112172) (@lem0)). Qed.
Lemma lem4112174 : term514 = term517.
Proof. exact (@lem4112163 (@lem4112173)). Qed.
Lemma lem4112176 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4112177 : term254 = term257.
Proof. exact (@lem4112176 term20 term20). Qed.
Lemma lem4112178 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112179 : term190 = term20.
Proof. exact (EQ_MP (@lem4112178) (@lem940073)). Qed.
Lemma lem4112180 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112181 : term188 = term111.
Proof. exact (MK_COMB (@lem4112180) (@lem4112179)). Qed.
Lemma lem4112182 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112183 : term257 = term178.
Proof. exact (MK_COMB (@lem4112182) (@lem4112181)). Qed.
Lemma lem4112184 : term254 = term178.
Proof. exact (TRANS (@lem4112177) (@lem4112183)). Qed.
Lemma lem4112186 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4112187 : term293 = term97.
Proof. exact (@lem4112186 term20). Qed.
Lemma lem4112188 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4112189 : term518 = term99.
Proof. exact (MK_COMB (@lem4112188) (@lem4112187)). Qed.
Lemma lem4112190 : term517 = term512.
Proof. exact (MK_COMB (@lem4112189) (@lem4112184)). Qed.
Lemma lem4112192 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4112193 : term512 = term521.
Proof. exact (@lem4112192 (NUMERAL 0) term20). Qed.
Lemma lem4112194 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112195 (h1 : term208 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4112196 : (term208 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112195 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem4112194)). Qed.
Lemma lem4112197 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4112196) (@lem4112194)). Qed.
Lemma lem4112198 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4112199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4112200 : term522 = (and True).
Proof. exact (MK_COMB (@lem4112199) (@lem4112198)). Qed.
Lemma lem4112201 : term521 = (True /\ False).
Proof. exact (MK_COMB (@lem4112200) (@lem4112197)). Qed.
Lemma lem4112203 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4112204 : term521 = False.
Proof. exact (TRANS (@lem4112201) (@lem4112203)). Qed.
Lemma lem4112205 : term512 = False.
Proof. exact (TRANS (@lem4112193) (@lem4112204)). Qed.
Lemma lem4112206 : term517 = False.
Proof. exact (TRANS (@lem4112190) (@lem4112205)). Qed.
Lemma lem4112207 : term514 = False.
Proof. exact (TRANS (@lem4112174) (@lem4112206)). Qed.
Lemma lem4112208 : term512 = False.
Proof. exact (TRANS (@lem4112151) (@lem4112207)). Qed.
Lemma lem4112209 : term511 = False.
Proof. exact (TRANS (@lem4112142) (@lem4112208)). Qed.
Lemma lem4112210 (_48296 : int) (h1 : term556 _48296) : False.
Proof. exact (EQ_MP (@lem4112209) (@lem4112139 _48296 h1)). Qed.
Lemma lem4112211 (_48296 : int) (h1 : term557 _48296) : term557 _48296.
Proof. exact (h1). Qed.
Lemma lem4112212 (_48296 : int) (h1 : term557 _48296) : term437 _48296.
Proof. exact (proj2 (@lem4112211 _48296 h1)). Qed.
Lemma lem4112214 (_48296 : int) (h1 : term557 _48296) : term312 _48296.
Proof. exact (proj2 (@lem4112212 _48296 h1)). Qed.
Lemma lem4112215 (_48296 : int) (h1 : term557 _48296) : term344 _48296.
Proof. exact (proj1 (@lem4112212 _48296 h1)). Qed.
Lemma lem4112216 (_48296 : int) (h1 : term557 _48296) : term248 _48296.
Proof. exact (proj2 (@lem4112215 _48296 h1)). Qed.
Lemma lem4112219 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4112220 : term451 = term206.
Proof. exact (@lem4112219 term97 term111). Qed.
Lemma lem4112222 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112223 : term111 = term200.
Proof. exact (@lem4112222 term20). Qed.
Lemma lem4112225 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112226 : term97 = term175.
Proof. exact (@lem4112225 (NUMERAL 0)). Qed.
Lemma lem4112227 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4112228 : term452 = term453.
Proof. exact (MK_COMB (@lem4112227) (@lem4112226)). Qed.
Lemma lem4112229 : term206 = term454.
Proof. exact (MK_COMB (@lem4112228) (@lem4112223)). Qed.
Lemma lem4112230 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4112232 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112233 : term206 = term207.
Proof. exact (@lem4112232 (NUMERAL 0) term20). Qed.
Lemma lem4112234 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112235 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112236 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112235 h1) (fun h1 : term207 = True => @lem4112234)). Qed.
Lemma lem4112237 : term207 = True.
Proof. exact (EQ_MP (@lem4112236) (@lem4112234)). Qed.
Lemma lem4112238 : term206 = True.
Proof. exact (TRANS (@lem4112233) (@lem4112237)). Qed.
Lemma lem4112239 : True = term206.
Proof. exact (SYM (@lem4112238)). Qed.
Lemma lem4112240 : term206.
Proof. exact (EQ_MP (@lem4112239) (@lem0)). Qed.
Lemma lem4112241 : term456.
Proof. exact (@lem4112230 (@lem4112240)). Qed.
Lemma lem4112243 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112244 : term206 = term207.
Proof. exact (@lem4112243 (NUMERAL 0) term20). Qed.
Lemma lem4112245 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112246 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112247 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112246 h1) (fun h1 : term207 = True => @lem4112245)). Qed.
Lemma lem4112248 : term207 = True.
Proof. exact (EQ_MP (@lem4112247) (@lem4112245)). Qed.
Lemma lem4112249 : term206 = True.
Proof. exact (TRANS (@lem4112244) (@lem4112248)). Qed.
Lemma lem4112250 : True = term206.
Proof. exact (SYM (@lem4112249)). Qed.
Lemma lem4112251 : term206.
Proof. exact (EQ_MP (@lem4112250) (@lem0)). Qed.
Lemma lem4112252 : term454 = term457.
Proof. exact (@lem4112241 (@lem4112251)). Qed.
Lemma lem4112254 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4112255 : term187 = term188.
Proof. exact (@lem4112254 term20 term20). Qed.
Lemma lem4112256 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112257 : term190 = term20.
Proof. exact (EQ_MP (@lem4112256) (@lem940073)). Qed.
Lemma lem4112258 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112259 : term188 = term111.
Proof. exact (MK_COMB (@lem4112258) (@lem4112257)). Qed.
Lemma lem4112260 : term187 = term111.
Proof. exact (TRANS (@lem4112255) (@lem4112259)). Qed.
Lemma lem4112262 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4112263 : term293 = term97.
Proof. exact (@lem4112262 term20). Qed.
Lemma lem4112264 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4112265 : term458 = term452.
Proof. exact (MK_COMB (@lem4112264) (@lem4112263)). Qed.
Lemma lem4112266 : term457 = term206.
Proof. exact (MK_COMB (@lem4112265) (@lem4112260)). Qed.
Lemma lem4112268 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112269 : term206 = term207.
Proof. exact (@lem4112268 (NUMERAL 0) term20). Qed.
Lemma lem4112270 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112271 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112272 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112271 h1) (fun h1 : term207 = True => @lem4112270)). Qed.
Lemma lem4112273 : term207 = True.
Proof. exact (EQ_MP (@lem4112272) (@lem4112270)). Qed.
Lemma lem4112274 : term206 = True.
Proof. exact (TRANS (@lem4112269) (@lem4112273)). Qed.
Lemma lem4112275 : term457 = True.
Proof. exact (TRANS (@lem4112266) (@lem4112274)). Qed.
Lemma lem4112276 : term454 = True.
Proof. exact (TRANS (@lem4112252) (@lem4112275)). Qed.
Lemma lem4112277 : term206 = True.
Proof. exact (TRANS (@lem4112229) (@lem4112276)). Qed.
Lemma lem4112278 : term451 = True.
Proof. exact (TRANS (@lem4112220) (@lem4112277)). Qed.
Lemma lem4112279 : True = term451.
Proof. exact (SYM (@lem4112278)). Qed.
Lemma lem4112280 : term451.
Proof. exact (EQ_MP (@lem4112279) (@lem0)). Qed.
Lemma lem4112281 (_48296 : int) (h1 : term557 _48296) : term459 _48296.
Proof. exact (conj (@lem4112280) (@lem4112216 _48296 h1)). Qed.
Lemma lem4112283 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4112284 (_48296 : int) : term461 _48296.
Proof. exact (@lem4112283 term111 (term245 _48296)). Qed.
Lemma lem4112285 (_48296 : int) (h1 : term557 _48296) : term462 _48296.
Proof. exact (@lem4112284 _48296 (@lem4112281 _48296 h1)). Qed.
Lemma lem4112286 (_48296 : int) : (term463 _48296) = (term245 _48296).
Proof. exact (@lem1982733 (term245 _48296)). Qed.
Lemma lem4112287 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4112288 (_48296 : int) : (term464 _48296) = (term247 _48296).
Proof. exact (MK_COMB (@lem4112287) (@lem4112286 _48296)). Qed.
Lemma lem4112289 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4112290 (_48296 : int) : (term462 _48296) = (term248 _48296).
Proof. exact (MK_COMB (@lem4112288 _48296) (@lem4112289)). Qed.
Lemma lem4112291 (_48296 : int) (h1 : term557 _48296) : term248 _48296.
Proof. exact (EQ_MP (@lem4112290 _48296) (@lem4112285 _48296 h1)). Qed.
Lemma lem4112293 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4112294 : term451 = term206.
Proof. exact (@lem4112293 term97 term111). Qed.
Lemma lem4112296 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112297 : term111 = term200.
Proof. exact (@lem4112296 term20). Qed.
Lemma lem4112299 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112300 : term97 = term175.
Proof. exact (@lem4112299 (NUMERAL 0)). Qed.
Lemma lem4112301 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4112302 : term452 = term453.
Proof. exact (MK_COMB (@lem4112301) (@lem4112300)). Qed.
Lemma lem4112303 : term206 = term454.
Proof. exact (MK_COMB (@lem4112302) (@lem4112297)). Qed.
Lemma lem4112304 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4112306 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112307 : term206 = term207.
Proof. exact (@lem4112306 (NUMERAL 0) term20). Qed.
Lemma lem4112308 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112309 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112310 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112309 h1) (fun h1 : term207 = True => @lem4112308)). Qed.
Lemma lem4112311 : term207 = True.
Proof. exact (EQ_MP (@lem4112310) (@lem4112308)). Qed.
Lemma lem4112312 : term206 = True.
Proof. exact (TRANS (@lem4112307) (@lem4112311)). Qed.
Lemma lem4112313 : True = term206.
Proof. exact (SYM (@lem4112312)). Qed.
Lemma lem4112314 : term206.
Proof. exact (EQ_MP (@lem4112313) (@lem0)). Qed.
Lemma lem4112315 : term456.
Proof. exact (@lem4112304 (@lem4112314)). Qed.
Lemma lem4112317 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112318 : term206 = term207.
Proof. exact (@lem4112317 (NUMERAL 0) term20). Qed.
Lemma lem4112319 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112320 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112321 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112320 h1) (fun h1 : term207 = True => @lem4112319)). Qed.
Lemma lem4112322 : term207 = True.
Proof. exact (EQ_MP (@lem4112321) (@lem4112319)). Qed.
Lemma lem4112323 : term206 = True.
Proof. exact (TRANS (@lem4112318) (@lem4112322)). Qed.
Lemma lem4112324 : True = term206.
Proof. exact (SYM (@lem4112323)). Qed.
Lemma lem4112325 : term206.
Proof. exact (EQ_MP (@lem4112324) (@lem0)). Qed.
Lemma lem4112326 : term454 = term457.
Proof. exact (@lem4112315 (@lem4112325)). Qed.
Lemma lem4112328 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4112329 : term187 = term188.
Proof. exact (@lem4112328 term20 term20). Qed.
Lemma lem4112330 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112331 : term190 = term20.
Proof. exact (EQ_MP (@lem4112330) (@lem940073)). Qed.
Lemma lem4112332 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112333 : term188 = term111.
Proof. exact (MK_COMB (@lem4112332) (@lem4112331)). Qed.
Lemma lem4112334 : term187 = term111.
Proof. exact (TRANS (@lem4112329) (@lem4112333)). Qed.
Lemma lem4112336 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4112337 : term293 = term97.
Proof. exact (@lem4112336 term20). Qed.
Lemma lem4112338 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4112339 : term458 = term452.
Proof. exact (MK_COMB (@lem4112338) (@lem4112337)). Qed.
Lemma lem4112340 : term457 = term206.
Proof. exact (MK_COMB (@lem4112339) (@lem4112334)). Qed.
Lemma lem4112342 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112343 : term206 = term207.
Proof. exact (@lem4112342 (NUMERAL 0) term20). Qed.
Lemma lem4112344 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112345 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112346 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112345 h1) (fun h1 : term207 = True => @lem4112344)). Qed.
Lemma lem4112347 : term207 = True.
Proof. exact (EQ_MP (@lem4112346) (@lem4112344)). Qed.
Lemma lem4112348 : term206 = True.
Proof. exact (TRANS (@lem4112343) (@lem4112347)). Qed.
Lemma lem4112349 : term457 = True.
Proof. exact (TRANS (@lem4112340) (@lem4112348)). Qed.
Lemma lem4112350 : term454 = True.
Proof. exact (TRANS (@lem4112326) (@lem4112349)). Qed.
Lemma lem4112351 : term206 = True.
Proof. exact (TRANS (@lem4112303) (@lem4112350)). Qed.
Lemma lem4112352 : term451 = True.
Proof. exact (TRANS (@lem4112294) (@lem4112351)). Qed.
Lemma lem4112353 : True = term451.
Proof. exact (SYM (@lem4112352)). Qed.
Lemma lem4112354 : term451.
Proof. exact (EQ_MP (@lem4112353) (@lem0)). Qed.
Lemma lem4112355 (_48296 : int) (h1 : term557 _48296) : term465 _48296.
Proof. exact (conj (@lem4112354) (@lem4112214 _48296 h1)). Qed.
Lemma lem4112357 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4112358 (_48296 : int) : term466 _48296.
Proof. exact (@lem4112357 term111 (term309 _48296)). Qed.
Lemma lem4112359 (_48296 : int) (h1 : term557 _48296) : term467 _48296.
Proof. exact (@lem4112358 _48296 (@lem4112355 _48296 h1)). Qed.
Lemma lem4112360 (_48296 : int) : (term468 _48296) = (term309 _48296).
Proof. exact (@lem1982733 (term309 _48296)). Qed.
Lemma lem4112361 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4112362 (_48296 : int) : (term469 _48296) = (term311 _48296).
Proof. exact (MK_COMB (@lem4112361) (@lem4112360 _48296)). Qed.
Lemma lem4112363 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4112364 (_48296 : int) : (term467 _48296) = (term312 _48296).
Proof. exact (MK_COMB (@lem4112362 _48296) (@lem4112363)). Qed.
Lemma lem4112365 (_48296 : int) (h1 : term557 _48296) : term312 _48296.
Proof. exact (EQ_MP (@lem4112364 _48296) (@lem4112359 _48296 h1)). Qed.
Lemma lem4112366 (_48296 : int) (h1 : term557 _48296) : term470 _48296.
Proof. exact (conj (@lem4112365 _48296 h1) (@lem4112291 _48296 h1)). Qed.
Lemma lem4112368 (x : real) (y : real) : term471 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem4112369 (_48296 : int) : term472 _48296.
Proof. exact (@lem4112368 (term309 _48296) (term245 _48296)). Qed.
Lemma lem4112370 (_48296 : int) (h1 : term557 _48296) : term473 _48296.
Proof. exact (@lem4112369 _48296 (@lem4112366 _48296 h1)). Qed.
Lemma lem4112371 (_48296 : int) : (term474 _48296) = (term475 _48296).
Proof. exact (@lem1982753 (term281 _48296) (real_of_int _48296) term111 term241). Qed.
Lemma lem4112372 (_48296 : int) : (term476 _48296) = (term477 _48296).
Proof. exact (@lem1982713 term178 (real_of_int _48296)). Qed.
Lemma lem4112374 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112375 : term111 = term200.
Proof. exact (@lem4112374 term20). Qed.
Lemma lem4112377 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4112378 : term178 = term179.
Proof. exact (@lem4112377 term20). Qed.
Lemma lem4112379 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4112380 : term478 = term479.
Proof. exact (MK_COMB (@lem4112379) (@lem4112378)). Qed.
Lemma lem4112381 : term480 = term481.
Proof. exact (MK_COMB (@lem4112380) (@lem4112375)). Qed.
Lemma lem4112382 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4112384 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112385 : term206 = term207.
Proof. exact (@lem4112384 (NUMERAL 0) term20). Qed.
Lemma lem4112386 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112387 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112388 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112387 h1) (fun h1 : term207 = True => @lem4112386)). Qed.
Lemma lem4112389 : term207 = True.
Proof. exact (EQ_MP (@lem4112388) (@lem4112386)). Qed.
Lemma lem4112390 : term206 = True.
Proof. exact (TRANS (@lem4112385) (@lem4112389)). Qed.
Lemma lem4112391 : True = term206.
Proof. exact (SYM (@lem4112390)). Qed.
Lemma lem4112392 : term206.
Proof. exact (EQ_MP (@lem4112391) (@lem0)). Qed.
Lemma lem4112393 : term483.
Proof. exact (@lem4112382 (@lem4112392)). Qed.
Lemma lem4112395 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112396 : term206 = term207.
Proof. exact (@lem4112395 (NUMERAL 0) term20). Qed.
Lemma lem4112397 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112398 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112399 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112398 h1) (fun h1 : term207 = True => @lem4112397)). Qed.
Lemma lem4112400 : term207 = True.
Proof. exact (EQ_MP (@lem4112399) (@lem4112397)). Qed.
Lemma lem4112401 : term206 = True.
Proof. exact (TRANS (@lem4112396) (@lem4112400)). Qed.
Lemma lem4112402 : True = term206.
Proof. exact (SYM (@lem4112401)). Qed.
Lemma lem4112403 : term206.
Proof. exact (EQ_MP (@lem4112402) (@lem0)). Qed.
Lemma lem4112404 : term484.
Proof. exact (@lem4112393 (@lem4112403)). Qed.
Lemma lem4112406 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112407 : term206 = term207.
Proof. exact (@lem4112406 (NUMERAL 0) term20). Qed.
Lemma lem4112408 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112409 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112410 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112409 h1) (fun h1 : term207 = True => @lem4112408)). Qed.
Lemma lem4112411 : term207 = True.
Proof. exact (EQ_MP (@lem4112410) (@lem4112408)). Qed.
Lemma lem4112412 : term206 = True.
Proof. exact (TRANS (@lem4112407) (@lem4112411)). Qed.
Lemma lem4112413 : True = term206.
Proof. exact (SYM (@lem4112412)). Qed.
Lemma lem4112414 : term206.
Proof. exact (EQ_MP (@lem4112413) (@lem0)). Qed.
Lemma lem4112415 : term485.
Proof. exact (@lem4112404 (@lem4112414)). Qed.
Lemma lem4112417 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4112418 : term187 = term188.
Proof. exact (@lem4112417 term20 term20). Qed.
Lemma lem4112419 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112420 : term190 = term20.
Proof. exact (EQ_MP (@lem4112419) (@lem940073)). Qed.
Lemma lem4112421 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112422 : term188 = term111.
Proof. exact (MK_COMB (@lem4112421) (@lem4112420)). Qed.
Lemma lem4112423 : term187 = term111.
Proof. exact (TRANS (@lem4112418) (@lem4112422)). Qed.
Lemma lem4112425 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4112426 : term254 = term257.
Proof. exact (@lem4112425 term20 term20). Qed.
Lemma lem4112427 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112428 : term190 = term20.
Proof. exact (EQ_MP (@lem4112427) (@lem940073)). Qed.
Lemma lem4112429 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112430 : term188 = term111.
Proof. exact (MK_COMB (@lem4112429) (@lem4112428)). Qed.
Lemma lem4112431 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112432 : term257 = term178.
Proof. exact (MK_COMB (@lem4112431) (@lem4112430)). Qed.
Lemma lem4112433 : term254 = term178.
Proof. exact (TRANS (@lem4112426) (@lem4112432)). Qed.
Lemma lem4112434 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4112435 : term486 = term478.
Proof. exact (MK_COMB (@lem4112434) (@lem4112433)). Qed.
Lemma lem4112436 : term487 = term480.
Proof. exact (MK_COMB (@lem4112435) (@lem4112423)). Qed.
Lemma lem4112438 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4112439 : term480 = term97.
Proof. exact (@lem4112438 term20). Qed.
Lemma lem4112440 : term487 = term97.
Proof. exact (TRANS (@lem4112436) (@lem4112439)). Qed.
Lemma lem4112441 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4112442 : term489 = term291.
Proof. exact (MK_COMB (@lem4112441) (@lem4112440)). Qed.
Lemma lem4112443 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4112444 : term490 = term293.
Proof. exact (MK_COMB (@lem4112442) (@lem4112443)). Qed.
Lemma lem4112446 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4112447 : term293 = term97.
Proof. exact (@lem4112446 term20). Qed.
Lemma lem4112448 : term490 = term97.
Proof. exact (TRANS (@lem4112444) (@lem4112447)). Qed.
Lemma lem4112450 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4112451 : term187 = term188.
Proof. exact (@lem4112450 term20 term20). Qed.
Lemma lem4112452 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112453 : term190 = term20.
Proof. exact (EQ_MP (@lem4112452) (@lem940073)). Qed.
Lemma lem4112454 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112455 : term188 = term111.
Proof. exact (MK_COMB (@lem4112454) (@lem4112453)). Qed.
Lemma lem4112456 : term187 = term111.
Proof. exact (TRANS (@lem4112451) (@lem4112455)). Qed.
Lemma lem4112457 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4112458 : term295 = term293.
Proof. exact (MK_COMB (@lem4112457) (@lem4112456)). Qed.
Lemma lem4112460 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4112461 : term293 = term97.
Proof. exact (@lem4112460 term20). Qed.
Lemma lem4112462 : term295 = term97.
Proof. exact (TRANS (@lem4112458) (@lem4112461)). Qed.
Lemma lem4112463 : term97 = term295.
Proof. exact (SYM (@lem4112462)). Qed.
Lemma lem4112464 : term490 = term295.
Proof. exact (TRANS (@lem4112448) (@lem4112463)). Qed.
Lemma lem4112465 : term481 = term175.
Proof. exact (@lem4112415 (@lem4112464)). Qed.
Lemma lem4112466 : term480 = term175.
Proof. exact (TRANS (@lem4112381) (@lem4112465)). Qed.
Lemma lem4112468 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4112469 : term175 = term97.
Proof. exact (@lem4112468 term97). Qed.
Lemma lem4112470 : term480 = term97.
Proof. exact (TRANS (@lem4112466) (@lem4112469)). Qed.
Lemma lem4112471 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4112472 : term491 = term291.
Proof. exact (MK_COMB (@lem4112471) (@lem4112470)). Qed.
Lemma lem4112473 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4112474 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4112472) (@lem4112473 _48296)). Qed.
Lemma lem4112475 (_48296 : int) : (term476 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4112372 _48296) (@lem4112474 _48296)). Qed.
Lemma lem4112476 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4112477 (_48296 : int) : (term476 _48296) = term97.
Proof. exact (TRANS (@lem4112475 _48296) (@lem4112476 _48296)). Qed.
Lemma lem4112478 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4112479 (_48296 : int) : (term493 _48296) = term139.
Proof. exact (MK_COMB (@lem4112478) (@lem4112477 _48296)). Qed.
Lemma lem4112481 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4112482 : term241 = term244.
Proof. exact (@lem4112481 term218). Qed.
Lemma lem4112484 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112485 : term111 = term200.
Proof. exact (@lem4112484 term20). Qed.
Lemma lem4112486 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4112487 : term113 = term201.
Proof. exact (MK_COMB (@lem4112486) (@lem4112485)). Qed.
Lemma lem4112488 : term494 = term495.
Proof. exact (MK_COMB (@lem4112487) (@lem4112482)). Qed.
Lemma lem4112489 : term496.
Proof. exact (@lem1981473 term111 term111 term241 term111 term178 term111). Qed.
Lemma lem4112491 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112492 : term206 = term207.
Proof. exact (@lem4112491 (NUMERAL 0) term20). Qed.
Lemma lem4112493 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112494 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112495 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112494 h1) (fun h1 : term207 = True => @lem4112493)). Qed.
Lemma lem4112496 : term207 = True.
Proof. exact (EQ_MP (@lem4112495) (@lem4112493)). Qed.
Lemma lem4112497 : term206 = True.
Proof. exact (TRANS (@lem4112492) (@lem4112496)). Qed.
Lemma lem4112498 : True = term206.
Proof. exact (SYM (@lem4112497)). Qed.
Lemma lem4112499 : term206.
Proof. exact (EQ_MP (@lem4112498) (@lem0)). Qed.
Lemma lem4112500 : term497.
Proof. exact (@lem4112489 (@lem4112499)). Qed.
Lemma lem4112502 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112503 : term206 = term207.
Proof. exact (@lem4112502 (NUMERAL 0) term20). Qed.
Lemma lem4112504 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112505 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112506 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112505 h1) (fun h1 : term207 = True => @lem4112504)). Qed.
Lemma lem4112507 : term207 = True.
Proof. exact (EQ_MP (@lem4112506) (@lem4112504)). Qed.
Lemma lem4112508 : term206 = True.
Proof. exact (TRANS (@lem4112503) (@lem4112507)). Qed.
Lemma lem4112509 : True = term206.
Proof. exact (SYM (@lem4112508)). Qed.
Lemma lem4112510 : term206.
Proof. exact (EQ_MP (@lem4112509) (@lem0)). Qed.
Lemma lem4112511 : term498.
Proof. exact (@lem4112500 (@lem4112510)). Qed.
Lemma lem4112513 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112514 : term206 = term207.
Proof. exact (@lem4112513 (NUMERAL 0) term20). Qed.
Lemma lem4112515 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112516 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112517 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112516 h1) (fun h1 : term207 = True => @lem4112515)). Qed.
Lemma lem4112518 : term207 = True.
Proof. exact (EQ_MP (@lem4112517) (@lem4112515)). Qed.
Lemma lem4112519 : term206 = True.
Proof. exact (TRANS (@lem4112514) (@lem4112518)). Qed.
Lemma lem4112520 : True = term206.
Proof. exact (SYM (@lem4112519)). Qed.
Lemma lem4112521 : term206.
Proof. exact (EQ_MP (@lem4112520) (@lem0)). Qed.
Lemma lem4112522 : term499.
Proof. exact (@lem4112511 (@lem4112521)). Qed.
Lemma lem4112524 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4112525 : term500 = term501.
Proof. exact (@lem4112524 term218 term20). Qed.
Lemma lem4112526 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4112527 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4112528 : term225 = term218.
Proof. exact (EQ_MP (@lem4112527) (@lem4112526)). Qed.
Lemma lem4112529 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112530 : term223 = term204.
Proof. exact (MK_COMB (@lem4112529) (@lem4112528)). Qed.
Lemma lem4112531 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112532 : term501 = term241.
Proof. exact (MK_COMB (@lem4112531) (@lem4112530)). Qed.
Lemma lem4112533 : term500 = term241.
Proof. exact (TRANS (@lem4112525) (@lem4112532)). Qed.
Lemma lem4112535 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4112536 : term187 = term188.
Proof. exact (@lem4112535 term20 term20). Qed.
Lemma lem4112537 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112538 : term190 = term20.
Proof. exact (EQ_MP (@lem4112537) (@lem940073)). Qed.
Lemma lem4112539 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112540 : term188 = term111.
Proof. exact (MK_COMB (@lem4112539) (@lem4112538)). Qed.
Lemma lem4112541 : term187 = term111.
Proof. exact (TRANS (@lem4112536) (@lem4112540)). Qed.
Lemma lem4112542 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4112543 : term212 = term113.
Proof. exact (MK_COMB (@lem4112542) (@lem4112541)). Qed.
Lemma lem4112544 : term502 = term494.
Proof. exact (MK_COMB (@lem4112543) (@lem4112533)). Qed.
Lemma lem4112547 : term503 = term178.
Proof. exact (@lem1367771 term20 term20). Qed.
Lemma lem4112548 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem4112549 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem4112550 : term217 = term218.
Proof. exact (EQ_MP (@lem4112549) (@lem4112548)). Qed.
Lemma lem4112551 : term218 = term217.
Proof. exact (SYM (@lem4112550)). Qed.
Lemma lem4112552 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112553 : term204 = term214.
Proof. exact (MK_COMB (@lem4112552) (@lem4112551)). Qed.
Lemma lem4112554 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112555 : term241 = term504.
Proof. exact (MK_COMB (@lem4112554) (@lem4112553)). Qed.
Lemma lem4112556 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem4112557 : term494 = term503.
Proof. exact (MK_COMB (@lem4112556) (@lem4112555)). Qed.
Lemma lem4112558 : term494 = term178.
Proof. exact (TRANS (@lem4112557) (@lem4112547)). Qed.
Lemma lem4112559 : term502 = term178.
Proof. exact (TRANS (@lem4112544) (@lem4112558)). Qed.
Lemma lem4112560 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4112561 : term505 = term180.
Proof. exact (MK_COMB (@lem4112560) (@lem4112559)). Qed.
Lemma lem4112562 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4112563 : term506 = term254.
Proof. exact (MK_COMB (@lem4112561) (@lem4112562)). Qed.
Lemma lem4112565 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4112566 : term254 = term257.
Proof. exact (@lem4112565 term20 term20). Qed.
Lemma lem4112567 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112568 : term190 = term20.
Proof. exact (EQ_MP (@lem4112567) (@lem940073)). Qed.
Lemma lem4112569 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112570 : term188 = term111.
Proof. exact (MK_COMB (@lem4112569) (@lem4112568)). Qed.
Lemma lem4112571 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112572 : term257 = term178.
Proof. exact (MK_COMB (@lem4112571) (@lem4112570)). Qed.
Lemma lem4112573 : term254 = term178.
Proof. exact (TRANS (@lem4112566) (@lem4112572)). Qed.
Lemma lem4112574 : term506 = term178.
Proof. exact (TRANS (@lem4112563) (@lem4112573)). Qed.
Lemma lem4112576 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4112577 : term187 = term188.
Proof. exact (@lem4112576 term20 term20). Qed.
Lemma lem4112578 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112579 : term190 = term20.
Proof. exact (EQ_MP (@lem4112578) (@lem940073)). Qed.
Lemma lem4112580 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112581 : term188 = term111.
Proof. exact (MK_COMB (@lem4112580) (@lem4112579)). Qed.
Lemma lem4112582 : term187 = term111.
Proof. exact (TRANS (@lem4112577) (@lem4112581)). Qed.
Lemma lem4112583 : term180 = term180.
Proof. exact (eq_refl term180). Qed.
Lemma lem4112584 : term507 = term254.
Proof. exact (MK_COMB (@lem4112583) (@lem4112582)). Qed.
Lemma lem4112586 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4112587 : term254 = term257.
Proof. exact (@lem4112586 term20 term20). Qed.
Lemma lem4112588 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112589 : term190 = term20.
Proof. exact (EQ_MP (@lem4112588) (@lem940073)). Qed.
Lemma lem4112590 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112591 : term188 = term111.
Proof. exact (MK_COMB (@lem4112590) (@lem4112589)). Qed.
Lemma lem4112592 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112593 : term257 = term178.
Proof. exact (MK_COMB (@lem4112592) (@lem4112591)). Qed.
Lemma lem4112594 : term254 = term178.
Proof. exact (TRANS (@lem4112587) (@lem4112593)). Qed.
Lemma lem4112595 : term507 = term178.
Proof. exact (TRANS (@lem4112584) (@lem4112594)). Qed.
Lemma lem4112596 : term178 = term507.
Proof. exact (SYM (@lem4112595)). Qed.
Lemma lem4112597 : term506 = term507.
Proof. exact (TRANS (@lem4112574) (@lem4112596)). Qed.
Lemma lem4112598 : term495 = term179.
Proof. exact (@lem4112522 (@lem4112597)). Qed.
Lemma lem4112599 : term494 = term179.
Proof. exact (TRANS (@lem4112488) (@lem4112598)). Qed.
Lemma lem4112601 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4112602 : term179 = term178.
Proof. exact (@lem4112601 term178). Qed.
Lemma lem4112603 : term494 = term178.
Proof. exact (TRANS (@lem4112599) (@lem4112602)). Qed.
Lemma lem4112604 (_48296 : int) : (term475 _48296) = term508.
Proof. exact (MK_COMB (@lem4112479 _48296) (@lem4112603)). Qed.
Lemma lem4112605 (_48296 : int) : (term474 _48296) = term508.
Proof. exact (TRANS (@lem4112371 _48296) (@lem4112604 _48296)). Qed.
Lemma lem4112606 : term508 = term178.
Proof. exact (@lem1982721 term178). Qed.
Lemma lem4112607 (_48296 : int) : (term474 _48296) = term178.
Proof. exact (TRANS (@lem4112605 _48296) (@lem4112606)). Qed.
Lemma lem4112608 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4112609 (_48296 : int) : (term509 _48296) = term510.
Proof. exact (MK_COMB (@lem4112608) (@lem4112607 _48296)). Qed.
Lemma lem4112610 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4112611 (_48296 : int) : (term473 _48296) = term511.
Proof. exact (MK_COMB (@lem4112609 _48296) (@lem4112610)). Qed.
Lemma lem4112612 (_48296 : int) (h1 : term557 _48296) : term511.
Proof. exact (EQ_MP (@lem4112611 _48296) (@lem4112370 _48296 h1)). Qed.
Lemma lem4112614 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4112615 : term511 = term512.
Proof. exact (@lem4112614 term97 term178). Qed.
Lemma lem4112617 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4112618 : term178 = term179.
Proof. exact (@lem4112617 term20). Qed.
Lemma lem4112620 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112621 : term97 = term175.
Proof. exact (@lem4112620 (NUMERAL 0)). Qed.
Lemma lem4112622 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4112623 : term99 = term513.
Proof. exact (MK_COMB (@lem4112622) (@lem4112621)). Qed.
Lemma lem4112624 : term512 = term514.
Proof. exact (MK_COMB (@lem4112623) (@lem4112618)). Qed.
Lemma lem4112625 : term515.
Proof. exact (@lem1980026 term97 term111 term178 term111). Qed.
Lemma lem4112627 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112628 : term206 = term207.
Proof. exact (@lem4112627 (NUMERAL 0) term20). Qed.
Lemma lem4112629 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112630 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112631 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112630 h1) (fun h1 : term207 = True => @lem4112629)). Qed.
Lemma lem4112632 : term207 = True.
Proof. exact (EQ_MP (@lem4112631) (@lem4112629)). Qed.
Lemma lem4112633 : term206 = True.
Proof. exact (TRANS (@lem4112628) (@lem4112632)). Qed.
Lemma lem4112634 : True = term206.
Proof. exact (SYM (@lem4112633)). Qed.
Lemma lem4112635 : term206.
Proof. exact (EQ_MP (@lem4112634) (@lem0)). Qed.
Lemma lem4112636 : term516.
Proof. exact (@lem4112625 (@lem4112635)). Qed.
Lemma lem4112638 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112639 : term206 = term207.
Proof. exact (@lem4112638 (NUMERAL 0) term20). Qed.
Lemma lem4112640 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112641 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112642 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112641 h1) (fun h1 : term207 = True => @lem4112640)). Qed.
Lemma lem4112643 : term207 = True.
Proof. exact (EQ_MP (@lem4112642) (@lem4112640)). Qed.
Lemma lem4112644 : term206 = True.
Proof. exact (TRANS (@lem4112639) (@lem4112643)). Qed.
Lemma lem4112645 : True = term206.
Proof. exact (SYM (@lem4112644)). Qed.
Lemma lem4112646 : term206.
Proof. exact (EQ_MP (@lem4112645) (@lem0)). Qed.
Lemma lem4112647 : term514 = term517.
Proof. exact (@lem4112636 (@lem4112646)). Qed.
Lemma lem4112649 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4112650 : term254 = term257.
Proof. exact (@lem4112649 term20 term20). Qed.
Lemma lem4112651 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112652 : term190 = term20.
Proof. exact (EQ_MP (@lem4112651) (@lem940073)). Qed.
Lemma lem4112653 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112654 : term188 = term111.
Proof. exact (MK_COMB (@lem4112653) (@lem4112652)). Qed.
Lemma lem4112655 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112656 : term257 = term178.
Proof. exact (MK_COMB (@lem4112655) (@lem4112654)). Qed.
Lemma lem4112657 : term254 = term178.
Proof. exact (TRANS (@lem4112650) (@lem4112656)). Qed.
Lemma lem4112659 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4112660 : term293 = term97.
Proof. exact (@lem4112659 term20). Qed.
Lemma lem4112661 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4112662 : term518 = term99.
Proof. exact (MK_COMB (@lem4112661) (@lem4112660)). Qed.
Lemma lem4112663 : term517 = term512.
Proof. exact (MK_COMB (@lem4112662) (@lem4112657)). Qed.
Lemma lem4112665 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4112666 : term512 = term521.
Proof. exact (@lem4112665 (NUMERAL 0) term20). Qed.
Lemma lem4112667 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112668 (h1 : term208 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4112669 : (term208 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112668 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem4112667)). Qed.
Lemma lem4112670 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4112669) (@lem4112667)). Qed.
Lemma lem4112671 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4112672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4112673 : term522 = (and True).
Proof. exact (MK_COMB (@lem4112672) (@lem4112671)). Qed.
Lemma lem4112674 : term521 = (True /\ False).
Proof. exact (MK_COMB (@lem4112673) (@lem4112670)). Qed.
Lemma lem4112676 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4112677 : term521 = False.
Proof. exact (TRANS (@lem4112674) (@lem4112676)). Qed.
Lemma lem4112678 : term512 = False.
Proof. exact (TRANS (@lem4112666) (@lem4112677)). Qed.
Lemma lem4112679 : term517 = False.
Proof. exact (TRANS (@lem4112663) (@lem4112678)). Qed.
Lemma lem4112680 : term514 = False.
Proof. exact (TRANS (@lem4112647) (@lem4112679)). Qed.
Lemma lem4112681 : term512 = False.
Proof. exact (TRANS (@lem4112624) (@lem4112680)). Qed.
Lemma lem4112682 : term511 = False.
Proof. exact (TRANS (@lem4112615) (@lem4112681)). Qed.
Lemma lem4112683 (_48296 : int) (h1 : term557 _48296) : False.
Proof. exact (EQ_MP (@lem4112682) (@lem4112612 _48296 h1)). Qed.
Lemma lem4112684 (_48296 : int) (h1 : term435 _48296) : False.
Proof. exact (or_elim (@lem4111737 _48296 h1) (fun h0 : term556 _48296 => @lem4112210 _48296 h0) (fun h0 : term557 _48296 => @lem4112683 _48296 h0)). Qed.
Lemma lem4112685 (_48296 : int) (h1 : term444 _48296) : False.
Proof. exact (or_elim (@lem4111034 _48296 h1) (fun h0 : term439 _48296 => @lem4111736 _48296 h0) (fun h0 : term435 _48296 => @lem4112684 _48296 h0)). Qed.
Lemma lem4112686 (_48296 : int) (h1 : term446 _48296) : False.
Proof. exact (or_elim (@lem4110562 _48296 h1) (fun h0 : term450 _48296 => @lem4111033 _48296 h0) (fun h0 : term444 _48296 => @lem4112685 _48296 h0)). Qed.
Lemma lem4112687 (_48296 : int) (h1 : term428 _48296) : term428 _48296.
Proof. exact (h1). Qed.
Lemma lem4112688 (_48296 : int) (h1 : term425 _48296) : term425 _48296.
Proof. exact (h1). Qed.
Lemma lem4112689 (_48296 : int) (h1 : term558 _48296) : term558 _48296.
Proof. exact (h1). Qed.
Lemma lem4112690 (_48296 : int) (h1 : term558 _48296) : term410 _48296.
Proof. exact (proj2 (@lem4112689 _48296 h1)). Qed.
Lemma lem4112692 (_48296 : int) (h1 : term558 _48296) : (real_of_int _48296) = term97.
Proof. exact (proj2 (@lem4112690 _48296 h1)). Qed.
Lemma lem4112693 (_48296 : int) (h1 : term558 _48296) : term248 _48296.
Proof. exact (proj1 (@lem4112690 _48296 h1)). Qed.
Lemma lem4112695 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4112696 : term451 = term206.
Proof. exact (@lem4112695 term97 term111). Qed.
Lemma lem4112698 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112699 : term111 = term200.
Proof. exact (@lem4112698 term20). Qed.
Lemma lem4112701 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112702 : term97 = term175.
Proof. exact (@lem4112701 (NUMERAL 0)). Qed.
Lemma lem4112703 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4112704 : term452 = term453.
Proof. exact (MK_COMB (@lem4112703) (@lem4112702)). Qed.
Lemma lem4112705 : term206 = term454.
Proof. exact (MK_COMB (@lem4112704) (@lem4112699)). Qed.
Lemma lem4112706 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4112708 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112709 : term206 = term207.
Proof. exact (@lem4112708 (NUMERAL 0) term20). Qed.
Lemma lem4112710 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112711 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112712 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112711 h1) (fun h1 : term207 = True => @lem4112710)). Qed.
Lemma lem4112713 : term207 = True.
Proof. exact (EQ_MP (@lem4112712) (@lem4112710)). Qed.
Lemma lem4112714 : term206 = True.
Proof. exact (TRANS (@lem4112709) (@lem4112713)). Qed.
Lemma lem4112715 : True = term206.
Proof. exact (SYM (@lem4112714)). Qed.
Lemma lem4112716 : term206.
Proof. exact (EQ_MP (@lem4112715) (@lem0)). Qed.
Lemma lem4112717 : term456.
Proof. exact (@lem4112706 (@lem4112716)). Qed.
Lemma lem4112719 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112720 : term206 = term207.
Proof. exact (@lem4112719 (NUMERAL 0) term20). Qed.
Lemma lem4112721 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112722 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112723 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112722 h1) (fun h1 : term207 = True => @lem4112721)). Qed.
Lemma lem4112724 : term207 = True.
Proof. exact (EQ_MP (@lem4112723) (@lem4112721)). Qed.
Lemma lem4112725 : term206 = True.
Proof. exact (TRANS (@lem4112720) (@lem4112724)). Qed.
Lemma lem4112726 : True = term206.
Proof. exact (SYM (@lem4112725)). Qed.
Lemma lem4112727 : term206.
Proof. exact (EQ_MP (@lem4112726) (@lem0)). Qed.
Lemma lem4112728 : term454 = term457.
Proof. exact (@lem4112717 (@lem4112727)). Qed.
Lemma lem4112730 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4112731 : term187 = term188.
Proof. exact (@lem4112730 term20 term20). Qed.
Lemma lem4112732 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112733 : term190 = term20.
Proof. exact (EQ_MP (@lem4112732) (@lem940073)). Qed.
Lemma lem4112734 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112735 : term188 = term111.
Proof. exact (MK_COMB (@lem4112734) (@lem4112733)). Qed.
Lemma lem4112736 : term187 = term111.
Proof. exact (TRANS (@lem4112731) (@lem4112735)). Qed.
Lemma lem4112738 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4112739 : term293 = term97.
Proof. exact (@lem4112738 term20). Qed.
Lemma lem4112740 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4112741 : term458 = term452.
Proof. exact (MK_COMB (@lem4112740) (@lem4112739)). Qed.
Lemma lem4112742 : term457 = term206.
Proof. exact (MK_COMB (@lem4112741) (@lem4112736)). Qed.
Lemma lem4112744 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112745 : term206 = term207.
Proof. exact (@lem4112744 (NUMERAL 0) term20). Qed.
Lemma lem4112746 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112747 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112748 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112747 h1) (fun h1 : term207 = True => @lem4112746)). Qed.
Lemma lem4112749 : term207 = True.
Proof. exact (EQ_MP (@lem4112748) (@lem4112746)). Qed.
Lemma lem4112750 : term206 = True.
Proof. exact (TRANS (@lem4112745) (@lem4112749)). Qed.
Lemma lem4112751 : term457 = True.
Proof. exact (TRANS (@lem4112742) (@lem4112750)). Qed.
Lemma lem4112752 : term454 = True.
Proof. exact (TRANS (@lem4112728) (@lem4112751)). Qed.
Lemma lem4112753 : term206 = True.
Proof. exact (TRANS (@lem4112705) (@lem4112752)). Qed.
Lemma lem4112754 : term451 = True.
Proof. exact (TRANS (@lem4112696) (@lem4112753)). Qed.
Lemma lem4112755 : True = term451.
Proof. exact (SYM (@lem4112754)). Qed.
Lemma lem4112756 : term451.
Proof. exact (EQ_MP (@lem4112755) (@lem0)). Qed.
Lemma lem4112757 (_48296 : int) (h1 : term558 _48296) : term459 _48296.
Proof. exact (conj (@lem4112756) (@lem4112693 _48296 h1)). Qed.
Lemma lem4112759 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4112760 (_48296 : int) : term461 _48296.
Proof. exact (@lem4112759 term111 (term245 _48296)). Qed.
Lemma lem4112761 (_48296 : int) (h1 : term558 _48296) : term462 _48296.
Proof. exact (@lem4112760 _48296 (@lem4112757 _48296 h1)). Qed.
Lemma lem4112762 (_48296 : int) : (term463 _48296) = (term245 _48296).
Proof. exact (@lem1982733 (term245 _48296)). Qed.
Lemma lem4112763 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4112764 (_48296 : int) : (term464 _48296) = (term247 _48296).
Proof. exact (MK_COMB (@lem4112763) (@lem4112762 _48296)). Qed.
Lemma lem4112765 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4112766 (_48296 : int) : (term462 _48296) = (term248 _48296).
Proof. exact (MK_COMB (@lem4112764 _48296) (@lem4112765)). Qed.
Lemma lem4112767 (_48296 : int) (h1 : term558 _48296) : term248 _48296.
Proof. exact (EQ_MP (@lem4112766 _48296) (@lem4112761 _48296 h1)). Qed.
Lemma lem4112769 (y : real) : term559 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem4112770 (_48296 : int) : term560 _48296.
Proof. exact (@lem4112769 (real_of_int _48296)). Qed.
Lemma lem4112771 (_48296 : int) (h1 : term558 _48296) : term561 _48296.
Proof. exact (@lem4112770 _48296 (@lem4112692 _48296 h1)). Qed.
Lemma lem4112772 (_48296 : int) (h1 : term558 _48296) : term562 _48296.
Proof. exact (@lem4112771 _48296 h1 term178). Qed.
Lemma lem4112773 (_48296 : int) : (term562 _48296) = ((term281 _48296) = term97).
Proof. exact (eq_refl (term562 _48296)). Qed.
Lemma lem4112780 (_48296 : int) (h1 : term558 _48296) : (term281 _48296) = term97.
Proof. exact (EQ_MP (@lem4112773 _48296) (@lem4112772 _48296 h1)). Qed.
Lemma lem4112781 (_48296 : int) (h1 : term558 _48296) : term563 _48296.
Proof. exact (conj (@lem4112780 _48296 h1) (@lem4112767 _48296 h1)). Qed.
Lemma lem4112783 (x : real) (y : real) : term564 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem4112784 (_48296 : int) : term565 _48296.
Proof. exact (@lem4112783 (term281 _48296) (term245 _48296)). Qed.
Lemma lem4112785 (_48296 : int) (h1 : term558 _48296) : term566 _48296.
Proof. exact (@lem4112784 _48296 (@lem4112781 _48296 h1)). Qed.
Lemma lem4112786 (_48296 : int) : (term567 _48296) = (term568 _48296).
Proof. exact (@lem1982763 (term281 _48296) (real_of_int _48296) term241). Qed.
Lemma lem4112787 (_48296 : int) : (term476 _48296) = (term477 _48296).
Proof. exact (@lem1982713 term178 (real_of_int _48296)). Qed.
Lemma lem4112789 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112790 : term111 = term200.
Proof. exact (@lem4112789 term20). Qed.
Lemma lem4112792 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4112793 : term178 = term179.
Proof. exact (@lem4112792 term20). Qed.
Lemma lem4112794 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4112795 : term478 = term479.
Proof. exact (MK_COMB (@lem4112794) (@lem4112793)). Qed.
Lemma lem4112796 : term480 = term481.
Proof. exact (MK_COMB (@lem4112795) (@lem4112790)). Qed.
Lemma lem4112797 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4112799 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112800 : term206 = term207.
Proof. exact (@lem4112799 (NUMERAL 0) term20). Qed.
Lemma lem4112801 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112802 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112803 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112802 h1) (fun h1 : term207 = True => @lem4112801)). Qed.
Lemma lem4112804 : term207 = True.
Proof. exact (EQ_MP (@lem4112803) (@lem4112801)). Qed.
Lemma lem4112805 : term206 = True.
Proof. exact (TRANS (@lem4112800) (@lem4112804)). Qed.
Lemma lem4112806 : True = term206.
Proof. exact (SYM (@lem4112805)). Qed.
Lemma lem4112807 : term206.
Proof. exact (EQ_MP (@lem4112806) (@lem0)). Qed.
Lemma lem4112808 : term483.
Proof. exact (@lem4112797 (@lem4112807)). Qed.
Lemma lem4112810 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112811 : term206 = term207.
Proof. exact (@lem4112810 (NUMERAL 0) term20). Qed.
Lemma lem4112812 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112813 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112814 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112813 h1) (fun h1 : term207 = True => @lem4112812)). Qed.
Lemma lem4112815 : term207 = True.
Proof. exact (EQ_MP (@lem4112814) (@lem4112812)). Qed.
Lemma lem4112816 : term206 = True.
Proof. exact (TRANS (@lem4112811) (@lem4112815)). Qed.
Lemma lem4112817 : True = term206.
Proof. exact (SYM (@lem4112816)). Qed.
Lemma lem4112818 : term206.
Proof. exact (EQ_MP (@lem4112817) (@lem0)). Qed.
Lemma lem4112819 : term484.
Proof. exact (@lem4112808 (@lem4112818)). Qed.
Lemma lem4112821 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112822 : term206 = term207.
Proof. exact (@lem4112821 (NUMERAL 0) term20). Qed.
Lemma lem4112823 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112824 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112825 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112824 h1) (fun h1 : term207 = True => @lem4112823)). Qed.
Lemma lem4112826 : term207 = True.
Proof. exact (EQ_MP (@lem4112825) (@lem4112823)). Qed.
Lemma lem4112827 : term206 = True.
Proof. exact (TRANS (@lem4112822) (@lem4112826)). Qed.
Lemma lem4112828 : True = term206.
Proof. exact (SYM (@lem4112827)). Qed.
Lemma lem4112829 : term206.
Proof. exact (EQ_MP (@lem4112828) (@lem0)). Qed.
Lemma lem4112830 : term485.
Proof. exact (@lem4112819 (@lem4112829)). Qed.
Lemma lem4112832 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4112833 : term187 = term188.
Proof. exact (@lem4112832 term20 term20). Qed.
Lemma lem4112834 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112835 : term190 = term20.
Proof. exact (EQ_MP (@lem4112834) (@lem940073)). Qed.
Lemma lem4112836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112837 : term188 = term111.
Proof. exact (MK_COMB (@lem4112836) (@lem4112835)). Qed.
Lemma lem4112838 : term187 = term111.
Proof. exact (TRANS (@lem4112833) (@lem4112837)). Qed.
Lemma lem4112840 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4112841 : term254 = term257.
Proof. exact (@lem4112840 term20 term20). Qed.
Lemma lem4112842 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112843 : term190 = term20.
Proof. exact (EQ_MP (@lem4112842) (@lem940073)). Qed.
Lemma lem4112844 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112845 : term188 = term111.
Proof. exact (MK_COMB (@lem4112844) (@lem4112843)). Qed.
Lemma lem4112846 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112847 : term257 = term178.
Proof. exact (MK_COMB (@lem4112846) (@lem4112845)). Qed.
Lemma lem4112848 : term254 = term178.
Proof. exact (TRANS (@lem4112841) (@lem4112847)). Qed.
Lemma lem4112849 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4112850 : term486 = term478.
Proof. exact (MK_COMB (@lem4112849) (@lem4112848)). Qed.
Lemma lem4112851 : term487 = term480.
Proof. exact (MK_COMB (@lem4112850) (@lem4112838)). Qed.
Lemma lem4112853 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4112854 : term480 = term97.
Proof. exact (@lem4112853 term20). Qed.
Lemma lem4112855 : term487 = term97.
Proof. exact (TRANS (@lem4112851) (@lem4112854)). Qed.
Lemma lem4112856 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4112857 : term489 = term291.
Proof. exact (MK_COMB (@lem4112856) (@lem4112855)). Qed.
Lemma lem4112858 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4112859 : term490 = term293.
Proof. exact (MK_COMB (@lem4112857) (@lem4112858)). Qed.
Lemma lem4112861 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4112862 : term293 = term97.
Proof. exact (@lem4112861 term20). Qed.
Lemma lem4112863 : term490 = term97.
Proof. exact (TRANS (@lem4112859) (@lem4112862)). Qed.
Lemma lem4112865 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4112866 : term187 = term188.
Proof. exact (@lem4112865 term20 term20). Qed.
Lemma lem4112867 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4112868 : term190 = term20.
Proof. exact (EQ_MP (@lem4112867) (@lem940073)). Qed.
Lemma lem4112869 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112870 : term188 = term111.
Proof. exact (MK_COMB (@lem4112869) (@lem4112868)). Qed.
Lemma lem4112871 : term187 = term111.
Proof. exact (TRANS (@lem4112866) (@lem4112870)). Qed.
Lemma lem4112872 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4112873 : term295 = term293.
Proof. exact (MK_COMB (@lem4112872) (@lem4112871)). Qed.
Lemma lem4112875 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4112876 : term293 = term97.
Proof. exact (@lem4112875 term20). Qed.
Lemma lem4112877 : term295 = term97.
Proof. exact (TRANS (@lem4112873) (@lem4112876)). Qed.
Lemma lem4112878 : term97 = term295.
Proof. exact (SYM (@lem4112877)). Qed.
Lemma lem4112879 : term490 = term295.
Proof. exact (TRANS (@lem4112863) (@lem4112878)). Qed.
Lemma lem4112880 : term481 = term175.
Proof. exact (@lem4112830 (@lem4112879)). Qed.
Lemma lem4112881 : term480 = term175.
Proof. exact (TRANS (@lem4112796) (@lem4112880)). Qed.
Lemma lem4112883 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4112884 : term175 = term97.
Proof. exact (@lem4112883 term97). Qed.
Lemma lem4112885 : term480 = term97.
Proof. exact (TRANS (@lem4112881) (@lem4112884)). Qed.
Lemma lem4112886 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4112887 : term491 = term291.
Proof. exact (MK_COMB (@lem4112886) (@lem4112885)). Qed.
Lemma lem4112888 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4112889 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4112887) (@lem4112888 _48296)). Qed.
Lemma lem4112890 (_48296 : int) : (term476 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4112787 _48296) (@lem4112889 _48296)). Qed.
Lemma lem4112891 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4112892 (_48296 : int) : (term476 _48296) = term97.
Proof. exact (TRANS (@lem4112890 _48296) (@lem4112891 _48296)). Qed.
Lemma lem4112893 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4112894 (_48296 : int) : (term493 _48296) = term139.
Proof. exact (MK_COMB (@lem4112893) (@lem4112892 _48296)). Qed.
Lemma lem4112895 : term241 = term241.
Proof. exact (eq_refl term241). Qed.
Lemma lem4112896 (_48296 : int) : (term568 _48296) = term569.
Proof. exact (MK_COMB (@lem4112894 _48296) (@lem4112895)). Qed.
Lemma lem4112897 (_48296 : int) : (term567 _48296) = term569.
Proof. exact (TRANS (@lem4112786 _48296) (@lem4112896 _48296)). Qed.
Lemma lem4112898 : term569 = term241.
Proof. exact (@lem1982721 term241). Qed.
Lemma lem4112899 (_48296 : int) : (term567 _48296) = term241.
Proof. exact (TRANS (@lem4112897 _48296) (@lem4112898)). Qed.
Lemma lem4112900 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4112901 (_48296 : int) : (term570 _48296) = term571.
Proof. exact (MK_COMB (@lem4112900) (@lem4112899 _48296)). Qed.
Lemma lem4112902 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4112903 (_48296 : int) : (term566 _48296) = term572.
Proof. exact (MK_COMB (@lem4112901 _48296) (@lem4112902)). Qed.
Lemma lem4112904 (_48296 : int) (h1 : term558 _48296) : term572.
Proof. exact (EQ_MP (@lem4112903 _48296) (@lem4112785 _48296 h1)). Qed.
Lemma lem4112906 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4112907 : term572 = term573.
Proof. exact (@lem4112906 term97 term241). Qed.
Lemma lem4112909 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4112910 : term241 = term244.
Proof. exact (@lem4112909 term218). Qed.
Lemma lem4112912 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112913 : term97 = term175.
Proof. exact (@lem4112912 (NUMERAL 0)). Qed.
Lemma lem4112914 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4112915 : term99 = term513.
Proof. exact (MK_COMB (@lem4112914) (@lem4112913)). Qed.
Lemma lem4112916 : term573 = term574.
Proof. exact (MK_COMB (@lem4112915) (@lem4112910)). Qed.
Lemma lem4112917 : term575.
Proof. exact (@lem1980026 term97 term111 term241 term111). Qed.
Lemma lem4112919 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112920 : term206 = term207.
Proof. exact (@lem4112919 (NUMERAL 0) term20). Qed.
Lemma lem4112921 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112922 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112923 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112922 h1) (fun h1 : term207 = True => @lem4112921)). Qed.
Lemma lem4112924 : term207 = True.
Proof. exact (EQ_MP (@lem4112923) (@lem4112921)). Qed.
Lemma lem4112925 : term206 = True.
Proof. exact (TRANS (@lem4112920) (@lem4112924)). Qed.
Lemma lem4112926 : True = term206.
Proof. exact (SYM (@lem4112925)). Qed.
Lemma lem4112927 : term206.
Proof. exact (EQ_MP (@lem4112926) (@lem0)). Qed.
Lemma lem4112928 : term576.
Proof. exact (@lem4112917 (@lem4112927)). Qed.
Lemma lem4112930 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4112931 : term206 = term207.
Proof. exact (@lem4112930 (NUMERAL 0) term20). Qed.
Lemma lem4112932 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4112933 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4112934 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4112933 h1) (fun h1 : term207 = True => @lem4112932)). Qed.
Lemma lem4112935 : term207 = True.
Proof. exact (EQ_MP (@lem4112934) (@lem4112932)). Qed.
Lemma lem4112936 : term206 = True.
Proof. exact (TRANS (@lem4112931) (@lem4112935)). Qed.
Lemma lem4112937 : True = term206.
Proof. exact (SYM (@lem4112936)). Qed.
Lemma lem4112938 : term206.
Proof. exact (EQ_MP (@lem4112937) (@lem0)). Qed.
Lemma lem4112939 : term574 = term577.
Proof. exact (@lem4112928 (@lem4112938)). Qed.
Lemma lem4112941 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4112942 : term500 = term501.
Proof. exact (@lem4112941 term218 term20). Qed.
Lemma lem4112943 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4112944 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4112945 : term225 = term218.
Proof. exact (EQ_MP (@lem4112944) (@lem4112943)). Qed.
Lemma lem4112946 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4112947 : term223 = term204.
Proof. exact (MK_COMB (@lem4112946) (@lem4112945)). Qed.
Lemma lem4112948 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4112949 : term501 = term241.
Proof. exact (MK_COMB (@lem4112948) (@lem4112947)). Qed.
Lemma lem4112950 : term500 = term241.
Proof. exact (TRANS (@lem4112942) (@lem4112949)). Qed.
Lemma lem4112952 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4112953 : term293 = term97.
Proof. exact (@lem4112952 term20). Qed.
Lemma lem4112954 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4112955 : term518 = term99.
Proof. exact (MK_COMB (@lem4112954) (@lem4112953)). Qed.
Lemma lem4112956 : term577 = term573.
Proof. exact (MK_COMB (@lem4112955) (@lem4112950)). Qed.
Lemma lem4112958 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4112959 : term573 = term578.
Proof. exact (@lem4112958 (NUMERAL 0) term218). Qed.
Lemma lem4112960 : term579 = term216.
Proof. exact (@lem912803). Qed.
Lemma lem4112961 (h1 : term579 = term216) : (term218 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term216 h1). Qed.
Lemma lem4112962 : (term579 = term216) = ((term218 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term579 = term216 => @lem4112961 h1) (fun h1 : (term218 = (NUMERAL 0)) = False => @lem4112960)). Qed.
Lemma lem4112963 : (term218 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4112962) (@lem4112960)). Qed.
Lemma lem4112964 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4112965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4112966 : term522 = (and True).
Proof. exact (MK_COMB (@lem4112965) (@lem4112964)). Qed.
Lemma lem4112967 : term578 = (True /\ False).
Proof. exact (MK_COMB (@lem4112966) (@lem4112963)). Qed.
Lemma lem4112969 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4112970 : term578 = False.
Proof. exact (TRANS (@lem4112967) (@lem4112969)). Qed.
Lemma lem4112971 : term573 = False.
Proof. exact (TRANS (@lem4112959) (@lem4112970)). Qed.
Lemma lem4112972 : term577 = False.
Proof. exact (TRANS (@lem4112956) (@lem4112971)). Qed.
Lemma lem4112973 : term574 = False.
Proof. exact (TRANS (@lem4112939) (@lem4112972)). Qed.
Lemma lem4112974 : term573 = False.
Proof. exact (TRANS (@lem4112916) (@lem4112973)). Qed.
Lemma lem4112975 : term572 = False.
Proof. exact (TRANS (@lem4112907) (@lem4112974)). Qed.
Lemma lem4112976 (_48296 : int) (h1 : term558 _48296) : False.
Proof. exact (EQ_MP (@lem4112975) (@lem4112904 _48296 h1)). Qed.
Lemma lem4112977 (_48296 : int) (h1 : term423 _48296) : term423 _48296.
Proof. exact (h1). Qed.
Lemma lem4112978 (_48296 : int) (h1 : term418 _48296) : term418 _48296.
Proof. exact (h1). Qed.
Lemma lem4112979 (_48296 : int) (h1 : term580 _48296) : term580 _48296.
Proof. exact (h1). Qed.
Lemma lem4112980 (_48296 : int) (h1 : term580 _48296) : term419 _48296.
Proof. exact (proj2 (@lem4112979 _48296 h1)). Qed.
Lemma lem4112982 (_48296 : int) (h1 : term580 _48296) : (real_of_int _48296) = term97.
Proof. exact (proj2 (@lem4112980 _48296 h1)). Qed.
Lemma lem4112983 (_48296 : int) (h1 : term580 _48296) : term347 _48296.
Proof. exact (proj1 (@lem4112980 _48296 h1)). Qed.
Lemma lem4112985 (_48296 : int) (h1 : term580 _48296) : term265 _48296.
Proof. exact (proj1 (@lem4112983 _48296 h1)). Qed.
Lemma lem4112987 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4112988 : term451 = term206.
Proof. exact (@lem4112987 term97 term111). Qed.
Lemma lem4112990 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112991 : term111 = term200.
Proof. exact (@lem4112990 term20). Qed.
Lemma lem4112993 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4112994 : term97 = term175.
Proof. exact (@lem4112993 (NUMERAL 0)). Qed.
Lemma lem4112995 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4112996 : term452 = term453.
Proof. exact (MK_COMB (@lem4112995) (@lem4112994)). Qed.
Lemma lem4112997 : term206 = term454.
Proof. exact (MK_COMB (@lem4112996) (@lem4112991)). Qed.
Lemma lem4112998 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4113000 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113001 : term206 = term207.
Proof. exact (@lem4113000 (NUMERAL 0) term20). Qed.
Lemma lem4113002 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113003 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113004 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113003 h1) (fun h1 : term207 = True => @lem4113002)). Qed.
Lemma lem4113005 : term207 = True.
Proof. exact (EQ_MP (@lem4113004) (@lem4113002)). Qed.
Lemma lem4113006 : term206 = True.
Proof. exact (TRANS (@lem4113001) (@lem4113005)). Qed.
Lemma lem4113007 : True = term206.
Proof. exact (SYM (@lem4113006)). Qed.
Lemma lem4113008 : term206.
Proof. exact (EQ_MP (@lem4113007) (@lem0)). Qed.
Lemma lem4113009 : term456.
Proof. exact (@lem4112998 (@lem4113008)). Qed.
Lemma lem4113011 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113012 : term206 = term207.
Proof. exact (@lem4113011 (NUMERAL 0) term20). Qed.
Lemma lem4113013 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113014 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113015 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113014 h1) (fun h1 : term207 = True => @lem4113013)). Qed.
Lemma lem4113016 : term207 = True.
Proof. exact (EQ_MP (@lem4113015) (@lem4113013)). Qed.
Lemma lem4113017 : term206 = True.
Proof. exact (TRANS (@lem4113012) (@lem4113016)). Qed.
Lemma lem4113018 : True = term206.
Proof. exact (SYM (@lem4113017)). Qed.
Lemma lem4113019 : term206.
Proof. exact (EQ_MP (@lem4113018) (@lem0)). Qed.
Lemma lem4113020 : term454 = term457.
Proof. exact (@lem4113009 (@lem4113019)). Qed.
Lemma lem4113022 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4113023 : term187 = term188.
Proof. exact (@lem4113022 term20 term20). Qed.
Lemma lem4113024 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113025 : term190 = term20.
Proof. exact (EQ_MP (@lem4113024) (@lem940073)). Qed.
Lemma lem4113026 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113027 : term188 = term111.
Proof. exact (MK_COMB (@lem4113026) (@lem4113025)). Qed.
Lemma lem4113028 : term187 = term111.
Proof. exact (TRANS (@lem4113023) (@lem4113027)). Qed.
Lemma lem4113030 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113031 : term293 = term97.
Proof. exact (@lem4113030 term20). Qed.
Lemma lem4113032 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4113033 : term458 = term452.
Proof. exact (MK_COMB (@lem4113032) (@lem4113031)). Qed.
Lemma lem4113034 : term457 = term206.
Proof. exact (MK_COMB (@lem4113033) (@lem4113028)). Qed.
Lemma lem4113036 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113037 : term206 = term207.
Proof. exact (@lem4113036 (NUMERAL 0) term20). Qed.
Lemma lem4113038 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113039 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113040 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113039 h1) (fun h1 : term207 = True => @lem4113038)). Qed.
Lemma lem4113041 : term207 = True.
Proof. exact (EQ_MP (@lem4113040) (@lem4113038)). Qed.
Lemma lem4113042 : term206 = True.
Proof. exact (TRANS (@lem4113037) (@lem4113041)). Qed.
Lemma lem4113043 : term457 = True.
Proof. exact (TRANS (@lem4113034) (@lem4113042)). Qed.
Lemma lem4113044 : term454 = True.
Proof. exact (TRANS (@lem4113020) (@lem4113043)). Qed.
Lemma lem4113045 : term206 = True.
Proof. exact (TRANS (@lem4112997) (@lem4113044)). Qed.
Lemma lem4113046 : term451 = True.
Proof. exact (TRANS (@lem4112988) (@lem4113045)). Qed.
Lemma lem4113047 : True = term451.
Proof. exact (SYM (@lem4113046)). Qed.
Lemma lem4113048 : term451.
Proof. exact (EQ_MP (@lem4113047) (@lem0)). Qed.
Lemma lem4113049 (_48296 : int) (h1 : term580 _48296) : term529 _48296.
Proof. exact (conj (@lem4113048) (@lem4112985 _48296 h1)). Qed.
Lemma lem4113051 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4113052 (_48296 : int) : term530 _48296.
Proof. exact (@lem4113051 term111 (term261 _48296)). Qed.
Lemma lem4113053 (_48296 : int) (h1 : term580 _48296) : term531 _48296.
Proof. exact (@lem4113052 _48296 (@lem4113049 _48296 h1)). Qed.
Lemma lem4113054 (_48296 : int) : (term532 _48296) = (term261 _48296).
Proof. exact (@lem1982733 (term261 _48296)). Qed.
Lemma lem4113055 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4113056 (_48296 : int) : (term533 _48296) = (term264 _48296).
Proof. exact (MK_COMB (@lem4113055) (@lem4113054 _48296)). Qed.
Lemma lem4113057 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4113058 (_48296 : int) : (term531 _48296) = (term265 _48296).
Proof. exact (MK_COMB (@lem4113056 _48296) (@lem4113057)). Qed.
Lemma lem4113059 (_48296 : int) (h1 : term580 _48296) : term265 _48296.
Proof. exact (EQ_MP (@lem4113058 _48296) (@lem4113053 _48296 h1)). Qed.
Lemma lem4113061 (y : real) : term559 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem4113062 (_48296 : int) : term560 _48296.
Proof. exact (@lem4113061 (real_of_int _48296)). Qed.
Lemma lem4113063 (_48296 : int) (h1 : term580 _48296) : term561 _48296.
Proof. exact (@lem4113062 _48296 (@lem4112982 _48296 h1)). Qed.
Lemma lem4113064 (_48296 : int) (h1 : term580 _48296) : term581 _48296.
Proof. exact (@lem4113063 _48296 h1 term111). Qed.
Lemma lem4113065 (_48296 : int) : (term581 _48296) = ((term527 _48296) = term97).
Proof. exact (eq_refl (term581 _48296)). Qed.
Lemma lem4113066 (_48296 : int) (h1 : term580 _48296) : (term527 _48296) = term97.
Proof. exact (EQ_MP (@lem4113065 _48296) (@lem4113064 _48296 h1)). Qed.
Lemma lem4113067 (_48296 : int) : (term527 _48296) = (real_of_int _48296).
Proof. exact (@lem1982733 (real_of_int _48296)). Qed.
Lemma lem4113068 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem4113069 (_48296 : int) : (term582 _48296) = (term160 _48296).
Proof. exact (MK_COMB (@lem4113068) (@lem4113067 _48296)). Qed.
Lemma lem4113070 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4113071 (_48296 : int) : ((term527 _48296) = term97) = ((real_of_int _48296) = term97).
Proof. exact (MK_COMB (@lem4113069 _48296) (@lem4113070)). Qed.
Lemma lem4113072 (_48296 : int) (h1 : term580 _48296) : (real_of_int _48296) = term97.
Proof. exact (EQ_MP (@lem4113071 _48296) (@lem4113066 _48296 h1)). Qed.
Lemma lem4113073 (_48296 : int) (h1 : term580 _48296) : term583 _48296.
Proof. exact (conj (@lem4113072 _48296 h1) (@lem4113059 _48296 h1)). Qed.
Lemma lem4113075 (x : real) (y : real) : term564 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem4113076 (_48296 : int) : term584 _48296.
Proof. exact (@lem4113075 (real_of_int _48296) (term261 _48296)). Qed.
Lemma lem4113077 (_48296 : int) (h1 : term580 _48296) : term585 _48296.
Proof. exact (@lem4113076 _48296 (@lem4113073 _48296 h1)). Qed.
Lemma lem4113078 (_48296 : int) : (term586 _48296) = (term587 _48296).
Proof. exact (@lem1982763 (real_of_int _48296) (term281 _48296) term178). Qed.
Lemma lem4113079 (_48296 : int) : (term588 _48296) = (term477 _48296).
Proof. exact (@lem1982715 term178 (real_of_int _48296)). Qed.
Lemma lem4113081 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113082 : term111 = term200.
Proof. exact (@lem4113081 term20). Qed.
Lemma lem4113084 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4113085 : term178 = term179.
Proof. exact (@lem4113084 term20). Qed.
Lemma lem4113086 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4113087 : term478 = term479.
Proof. exact (MK_COMB (@lem4113086) (@lem4113085)). Qed.
Lemma lem4113088 : term480 = term481.
Proof. exact (MK_COMB (@lem4113087) (@lem4113082)). Qed.
Lemma lem4113089 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4113091 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113092 : term206 = term207.
Proof. exact (@lem4113091 (NUMERAL 0) term20). Qed.
Lemma lem4113093 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113094 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113095 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113094 h1) (fun h1 : term207 = True => @lem4113093)). Qed.
Lemma lem4113096 : term207 = True.
Proof. exact (EQ_MP (@lem4113095) (@lem4113093)). Qed.
Lemma lem4113097 : term206 = True.
Proof. exact (TRANS (@lem4113092) (@lem4113096)). Qed.
Lemma lem4113098 : True = term206.
Proof. exact (SYM (@lem4113097)). Qed.
Lemma lem4113099 : term206.
Proof. exact (EQ_MP (@lem4113098) (@lem0)). Qed.
Lemma lem4113100 : term483.
Proof. exact (@lem4113089 (@lem4113099)). Qed.
Lemma lem4113102 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113103 : term206 = term207.
Proof. exact (@lem4113102 (NUMERAL 0) term20). Qed.
Lemma lem4113104 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113105 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113106 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113105 h1) (fun h1 : term207 = True => @lem4113104)). Qed.
Lemma lem4113107 : term207 = True.
Proof. exact (EQ_MP (@lem4113106) (@lem4113104)). Qed.
Lemma lem4113108 : term206 = True.
Proof. exact (TRANS (@lem4113103) (@lem4113107)). Qed.
Lemma lem4113109 : True = term206.
Proof. exact (SYM (@lem4113108)). Qed.
Lemma lem4113110 : term206.
Proof. exact (EQ_MP (@lem4113109) (@lem0)). Qed.
Lemma lem4113111 : term484.
Proof. exact (@lem4113100 (@lem4113110)). Qed.
Lemma lem4113113 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113114 : term206 = term207.
Proof. exact (@lem4113113 (NUMERAL 0) term20). Qed.
Lemma lem4113115 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113116 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113117 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113116 h1) (fun h1 : term207 = True => @lem4113115)). Qed.
Lemma lem4113118 : term207 = True.
Proof. exact (EQ_MP (@lem4113117) (@lem4113115)). Qed.
Lemma lem4113119 : term206 = True.
Proof. exact (TRANS (@lem4113114) (@lem4113118)). Qed.
Lemma lem4113120 : True = term206.
Proof. exact (SYM (@lem4113119)). Qed.
Lemma lem4113121 : term206.
Proof. exact (EQ_MP (@lem4113120) (@lem0)). Qed.
Lemma lem4113122 : term485.
Proof. exact (@lem4113111 (@lem4113121)). Qed.
Lemma lem4113124 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4113125 : term187 = term188.
Proof. exact (@lem4113124 term20 term20). Qed.
Lemma lem4113126 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113127 : term190 = term20.
Proof. exact (EQ_MP (@lem4113126) (@lem940073)). Qed.
Lemma lem4113128 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113129 : term188 = term111.
Proof. exact (MK_COMB (@lem4113128) (@lem4113127)). Qed.
Lemma lem4113130 : term187 = term111.
Proof. exact (TRANS (@lem4113125) (@lem4113129)). Qed.
Lemma lem4113132 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4113133 : term254 = term257.
Proof. exact (@lem4113132 term20 term20). Qed.
Lemma lem4113134 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113135 : term190 = term20.
Proof. exact (EQ_MP (@lem4113134) (@lem940073)). Qed.
Lemma lem4113136 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113137 : term188 = term111.
Proof. exact (MK_COMB (@lem4113136) (@lem4113135)). Qed.
Lemma lem4113138 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4113139 : term257 = term178.
Proof. exact (MK_COMB (@lem4113138) (@lem4113137)). Qed.
Lemma lem4113140 : term254 = term178.
Proof. exact (TRANS (@lem4113133) (@lem4113139)). Qed.
Lemma lem4113141 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4113142 : term486 = term478.
Proof. exact (MK_COMB (@lem4113141) (@lem4113140)). Qed.
Lemma lem4113143 : term487 = term480.
Proof. exact (MK_COMB (@lem4113142) (@lem4113130)). Qed.
Lemma lem4113145 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4113146 : term480 = term97.
Proof. exact (@lem4113145 term20). Qed.
Lemma lem4113147 : term487 = term97.
Proof. exact (TRANS (@lem4113143) (@lem4113146)). Qed.
Lemma lem4113148 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4113149 : term489 = term291.
Proof. exact (MK_COMB (@lem4113148) (@lem4113147)). Qed.
Lemma lem4113150 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4113151 : term490 = term293.
Proof. exact (MK_COMB (@lem4113149) (@lem4113150)). Qed.
Lemma lem4113153 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113154 : term293 = term97.
Proof. exact (@lem4113153 term20). Qed.
Lemma lem4113155 : term490 = term97.
Proof. exact (TRANS (@lem4113151) (@lem4113154)). Qed.
Lemma lem4113157 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4113158 : term187 = term188.
Proof. exact (@lem4113157 term20 term20). Qed.
Lemma lem4113159 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113160 : term190 = term20.
Proof. exact (EQ_MP (@lem4113159) (@lem940073)). Qed.
Lemma lem4113161 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113162 : term188 = term111.
Proof. exact (MK_COMB (@lem4113161) (@lem4113160)). Qed.
Lemma lem4113163 : term187 = term111.
Proof. exact (TRANS (@lem4113158) (@lem4113162)). Qed.
Lemma lem4113164 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4113165 : term295 = term293.
Proof. exact (MK_COMB (@lem4113164) (@lem4113163)). Qed.
Lemma lem4113167 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113168 : term293 = term97.
Proof. exact (@lem4113167 term20). Qed.
Lemma lem4113169 : term295 = term97.
Proof. exact (TRANS (@lem4113165) (@lem4113168)). Qed.
Lemma lem4113170 : term97 = term295.
Proof. exact (SYM (@lem4113169)). Qed.
Lemma lem4113171 : term490 = term295.
Proof. exact (TRANS (@lem4113155) (@lem4113170)). Qed.
Lemma lem4113172 : term481 = term175.
Proof. exact (@lem4113122 (@lem4113171)). Qed.
Lemma lem4113173 : term480 = term175.
Proof. exact (TRANS (@lem4113088) (@lem4113172)). Qed.
Lemma lem4113175 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4113176 : term175 = term97.
Proof. exact (@lem4113175 term97). Qed.
Lemma lem4113177 : term480 = term97.
Proof. exact (TRANS (@lem4113173) (@lem4113176)). Qed.
Lemma lem4113178 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4113179 : term491 = term291.
Proof. exact (MK_COMB (@lem4113178) (@lem4113177)). Qed.
Lemma lem4113180 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4113181 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4113179) (@lem4113180 _48296)). Qed.
Lemma lem4113182 (_48296 : int) : (term588 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4113079 _48296) (@lem4113181 _48296)). Qed.
Lemma lem4113183 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4113184 (_48296 : int) : (term588 _48296) = term97.
Proof. exact (TRANS (@lem4113182 _48296) (@lem4113183 _48296)). Qed.
Lemma lem4113185 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4113186 (_48296 : int) : (term589 _48296) = term139.
Proof. exact (MK_COMB (@lem4113185) (@lem4113184 _48296)). Qed.
Lemma lem4113187 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem4113188 (_48296 : int) : (term587 _48296) = term508.
Proof. exact (MK_COMB (@lem4113186 _48296) (@lem4113187)). Qed.
Lemma lem4113189 (_48296 : int) : (term586 _48296) = term508.
Proof. exact (TRANS (@lem4113078 _48296) (@lem4113188 _48296)). Qed.
Lemma lem4113190 : term508 = term178.
Proof. exact (@lem1982721 term178). Qed.
Lemma lem4113191 (_48296 : int) : (term586 _48296) = term178.
Proof. exact (TRANS (@lem4113189 _48296) (@lem4113190)). Qed.
Lemma lem4113192 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4113193 (_48296 : int) : (term590 _48296) = term510.
Proof. exact (MK_COMB (@lem4113192) (@lem4113191 _48296)). Qed.
Lemma lem4113194 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4113195 (_48296 : int) : (term585 _48296) = term511.
Proof. exact (MK_COMB (@lem4113193 _48296) (@lem4113194)). Qed.
Lemma lem4113196 (_48296 : int) (h1 : term580 _48296) : term511.
Proof. exact (EQ_MP (@lem4113195 _48296) (@lem4113077 _48296 h1)). Qed.
Lemma lem4113198 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4113199 : term511 = term512.
Proof. exact (@lem4113198 term97 term178). Qed.
Lemma lem4113201 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4113202 : term178 = term179.
Proof. exact (@lem4113201 term20). Qed.
Lemma lem4113204 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113205 : term97 = term175.
Proof. exact (@lem4113204 (NUMERAL 0)). Qed.
Lemma lem4113206 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4113207 : term99 = term513.
Proof. exact (MK_COMB (@lem4113206) (@lem4113205)). Qed.
Lemma lem4113208 : term512 = term514.
Proof. exact (MK_COMB (@lem4113207) (@lem4113202)). Qed.
Lemma lem4113209 : term515.
Proof. exact (@lem1980026 term97 term111 term178 term111). Qed.
Lemma lem4113211 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113212 : term206 = term207.
Proof. exact (@lem4113211 (NUMERAL 0) term20). Qed.
Lemma lem4113213 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113214 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113215 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113214 h1) (fun h1 : term207 = True => @lem4113213)). Qed.
Lemma lem4113216 : term207 = True.
Proof. exact (EQ_MP (@lem4113215) (@lem4113213)). Qed.
Lemma lem4113217 : term206 = True.
Proof. exact (TRANS (@lem4113212) (@lem4113216)). Qed.
Lemma lem4113218 : True = term206.
Proof. exact (SYM (@lem4113217)). Qed.
Lemma lem4113219 : term206.
Proof. exact (EQ_MP (@lem4113218) (@lem0)). Qed.
Lemma lem4113220 : term516.
Proof. exact (@lem4113209 (@lem4113219)). Qed.
Lemma lem4113222 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113223 : term206 = term207.
Proof. exact (@lem4113222 (NUMERAL 0) term20). Qed.
Lemma lem4113224 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113225 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113226 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113225 h1) (fun h1 : term207 = True => @lem4113224)). Qed.
Lemma lem4113227 : term207 = True.
Proof. exact (EQ_MP (@lem4113226) (@lem4113224)). Qed.
Lemma lem4113228 : term206 = True.
Proof. exact (TRANS (@lem4113223) (@lem4113227)). Qed.
Lemma lem4113229 : True = term206.
Proof. exact (SYM (@lem4113228)). Qed.
Lemma lem4113230 : term206.
Proof. exact (EQ_MP (@lem4113229) (@lem0)). Qed.
Lemma lem4113231 : term514 = term517.
Proof. exact (@lem4113220 (@lem4113230)). Qed.
Lemma lem4113233 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4113234 : term254 = term257.
Proof. exact (@lem4113233 term20 term20). Qed.
Lemma lem4113235 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113236 : term190 = term20.
Proof. exact (EQ_MP (@lem4113235) (@lem940073)). Qed.
Lemma lem4113237 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113238 : term188 = term111.
Proof. exact (MK_COMB (@lem4113237) (@lem4113236)). Qed.
Lemma lem4113239 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4113240 : term257 = term178.
Proof. exact (MK_COMB (@lem4113239) (@lem4113238)). Qed.
Lemma lem4113241 : term254 = term178.
Proof. exact (TRANS (@lem4113234) (@lem4113240)). Qed.
Lemma lem4113243 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113244 : term293 = term97.
Proof. exact (@lem4113243 term20). Qed.
Lemma lem4113245 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4113246 : term518 = term99.
Proof. exact (MK_COMB (@lem4113245) (@lem4113244)). Qed.
Lemma lem4113247 : term517 = term512.
Proof. exact (MK_COMB (@lem4113246) (@lem4113241)). Qed.
Lemma lem4113249 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4113250 : term512 = term521.
Proof. exact (@lem4113249 (NUMERAL 0) term20). Qed.
Lemma lem4113251 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113252 (h1 : term208 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4113253 : (term208 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113252 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem4113251)). Qed.
Lemma lem4113254 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4113253) (@lem4113251)). Qed.
Lemma lem4113255 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4113256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4113257 : term522 = (and True).
Proof. exact (MK_COMB (@lem4113256) (@lem4113255)). Qed.
Lemma lem4113258 : term521 = (True /\ False).
Proof. exact (MK_COMB (@lem4113257) (@lem4113254)). Qed.
Lemma lem4113260 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4113261 : term521 = False.
Proof. exact (TRANS (@lem4113258) (@lem4113260)). Qed.
Lemma lem4113262 : term512 = False.
Proof. exact (TRANS (@lem4113250) (@lem4113261)). Qed.
Lemma lem4113263 : term517 = False.
Proof. exact (TRANS (@lem4113247) (@lem4113262)). Qed.
Lemma lem4113264 : term514 = False.
Proof. exact (TRANS (@lem4113231) (@lem4113263)). Qed.
Lemma lem4113265 : term512 = False.
Proof. exact (TRANS (@lem4113208) (@lem4113264)). Qed.
Lemma lem4113266 : term511 = False.
Proof. exact (TRANS (@lem4113199) (@lem4113265)). Qed.
Lemma lem4113267 (_48296 : int) (h1 : term580 _48296) : False.
Proof. exact (EQ_MP (@lem4113266) (@lem4113196 _48296 h1)). Qed.
Lemma lem4113268 (_48296 : int) (h1 : term591 _48296) : term591 _48296.
Proof. exact (h1). Qed.
Lemma lem4113269 (_48296 : int) (h1 : term591 _48296) : term420 _48296.
Proof. exact (proj2 (@lem4113268 _48296 h1)). Qed.
Lemma lem4113271 (_48296 : int) (h1 : term591 _48296) : (real_of_int _48296) = term97.
Proof. exact (proj2 (@lem4113269 _48296 h1)). Qed.
Lemma lem4113272 (_48296 : int) (h1 : term591 _48296) : term348 _48296.
Proof. exact (proj1 (@lem4113269 _48296 h1)). Qed.
Lemma lem4113274 (_48296 : int) (h1 : term591 _48296) : term273 _48296.
Proof. exact (proj1 (@lem4113272 _48296 h1)). Qed.
Lemma lem4113276 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4113277 : term451 = term206.
Proof. exact (@lem4113276 term97 term111). Qed.
Lemma lem4113279 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113280 : term111 = term200.
Proof. exact (@lem4113279 term20). Qed.
Lemma lem4113282 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113283 : term97 = term175.
Proof. exact (@lem4113282 (NUMERAL 0)). Qed.
Lemma lem4113284 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4113285 : term452 = term453.
Proof. exact (MK_COMB (@lem4113284) (@lem4113283)). Qed.
Lemma lem4113286 : term206 = term454.
Proof. exact (MK_COMB (@lem4113285) (@lem4113280)). Qed.
Lemma lem4113287 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4113289 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113290 : term206 = term207.
Proof. exact (@lem4113289 (NUMERAL 0) term20). Qed.
Lemma lem4113291 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113292 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113293 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113292 h1) (fun h1 : term207 = True => @lem4113291)). Qed.
Lemma lem4113294 : term207 = True.
Proof. exact (EQ_MP (@lem4113293) (@lem4113291)). Qed.
Lemma lem4113295 : term206 = True.
Proof. exact (TRANS (@lem4113290) (@lem4113294)). Qed.
Lemma lem4113296 : True = term206.
Proof. exact (SYM (@lem4113295)). Qed.
Lemma lem4113297 : term206.
Proof. exact (EQ_MP (@lem4113296) (@lem0)). Qed.
Lemma lem4113298 : term456.
Proof. exact (@lem4113287 (@lem4113297)). Qed.
Lemma lem4113300 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113301 : term206 = term207.
Proof. exact (@lem4113300 (NUMERAL 0) term20). Qed.
Lemma lem4113302 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113303 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113304 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113303 h1) (fun h1 : term207 = True => @lem4113302)). Qed.
Lemma lem4113305 : term207 = True.
Proof. exact (EQ_MP (@lem4113304) (@lem4113302)). Qed.
Lemma lem4113306 : term206 = True.
Proof. exact (TRANS (@lem4113301) (@lem4113305)). Qed.
Lemma lem4113307 : True = term206.
Proof. exact (SYM (@lem4113306)). Qed.
Lemma lem4113308 : term206.
Proof. exact (EQ_MP (@lem4113307) (@lem0)). Qed.
Lemma lem4113309 : term454 = term457.
Proof. exact (@lem4113298 (@lem4113308)). Qed.
Lemma lem4113311 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4113312 : term187 = term188.
Proof. exact (@lem4113311 term20 term20). Qed.
Lemma lem4113313 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113314 : term190 = term20.
Proof. exact (EQ_MP (@lem4113313) (@lem940073)). Qed.
Lemma lem4113315 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113316 : term188 = term111.
Proof. exact (MK_COMB (@lem4113315) (@lem4113314)). Qed.
Lemma lem4113317 : term187 = term111.
Proof. exact (TRANS (@lem4113312) (@lem4113316)). Qed.
Lemma lem4113319 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113320 : term293 = term97.
Proof. exact (@lem4113319 term20). Qed.
Lemma lem4113321 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4113322 : term458 = term452.
Proof. exact (MK_COMB (@lem4113321) (@lem4113320)). Qed.
Lemma lem4113323 : term457 = term206.
Proof. exact (MK_COMB (@lem4113322) (@lem4113317)). Qed.
Lemma lem4113325 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113326 : term206 = term207.
Proof. exact (@lem4113325 (NUMERAL 0) term20). Qed.
Lemma lem4113327 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113328 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113329 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113328 h1) (fun h1 : term207 = True => @lem4113327)). Qed.
Lemma lem4113330 : term207 = True.
Proof. exact (EQ_MP (@lem4113329) (@lem4113327)). Qed.
Lemma lem4113331 : term206 = True.
Proof. exact (TRANS (@lem4113326) (@lem4113330)). Qed.
Lemma lem4113332 : term457 = True.
Proof. exact (TRANS (@lem4113323) (@lem4113331)). Qed.
Lemma lem4113333 : term454 = True.
Proof. exact (TRANS (@lem4113309) (@lem4113332)). Qed.
Lemma lem4113334 : term206 = True.
Proof. exact (TRANS (@lem4113286) (@lem4113333)). Qed.
Lemma lem4113335 : term451 = True.
Proof. exact (TRANS (@lem4113277) (@lem4113334)). Qed.
Lemma lem4113336 : True = term451.
Proof. exact (SYM (@lem4113335)). Qed.
Lemma lem4113337 : term451.
Proof. exact (EQ_MP (@lem4113336) (@lem0)). Qed.
Lemma lem4113338 (_48296 : int) (h1 : term591 _48296) : term541 _48296.
Proof. exact (conj (@lem4113337) (@lem4113274 _48296 h1)). Qed.
Lemma lem4113340 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4113341 (_48296 : int) : term542 _48296.
Proof. exact (@lem4113340 term111 (term270 _48296)). Qed.
Lemma lem4113342 (_48296 : int) (h1 : term591 _48296) : term543 _48296.
Proof. exact (@lem4113341 _48296 (@lem4113338 _48296 h1)). Qed.
Lemma lem4113343 (_48296 : int) : (term544 _48296) = (term270 _48296).
Proof. exact (@lem1982733 (term270 _48296)). Qed.
Lemma lem4113344 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4113345 (_48296 : int) : (term545 _48296) = (term272 _48296).
Proof. exact (MK_COMB (@lem4113344) (@lem4113343 _48296)). Qed.
Lemma lem4113346 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4113347 (_48296 : int) : (term543 _48296) = (term273 _48296).
Proof. exact (MK_COMB (@lem4113345 _48296) (@lem4113346)). Qed.
Lemma lem4113348 (_48296 : int) (h1 : term591 _48296) : term273 _48296.
Proof. exact (EQ_MP (@lem4113347 _48296) (@lem4113342 _48296 h1)). Qed.
Lemma lem4113350 (y : real) : term559 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem4113351 (_48296 : int) : term560 _48296.
Proof. exact (@lem4113350 (real_of_int _48296)). Qed.
Lemma lem4113352 (_48296 : int) (h1 : term591 _48296) : term561 _48296.
Proof. exact (@lem4113351 _48296 (@lem4113271 _48296 h1)). Qed.
Lemma lem4113353 (_48296 : int) (h1 : term591 _48296) : term562 _48296.
Proof. exact (@lem4113352 _48296 h1 term178). Qed.
Lemma lem4113354 (_48296 : int) : (term562 _48296) = ((term281 _48296) = term97).
Proof. exact (eq_refl (term562 _48296)). Qed.
Lemma lem4113361 (_48296 : int) (h1 : term591 _48296) : (term281 _48296) = term97.
Proof. exact (EQ_MP (@lem4113354 _48296) (@lem4113353 _48296 h1)). Qed.
Lemma lem4113362 (_48296 : int) (h1 : term591 _48296) : term592 _48296.
Proof. exact (conj (@lem4113361 _48296 h1) (@lem4113348 _48296 h1)). Qed.
Lemma lem4113364 (x : real) (y : real) : term564 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem4113365 (_48296 : int) : term593 _48296.
Proof. exact (@lem4113364 (term281 _48296) (term270 _48296)). Qed.
Lemma lem4113366 (_48296 : int) (h1 : term591 _48296) : term553 _48296.
Proof. exact (@lem4113365 _48296 (@lem4113362 _48296 h1)). Qed.
Lemma lem4113367 (_48296 : int) : (term554 _48296) = (term538 _48296).
Proof. exact (@lem1982763 (term281 _48296) (real_of_int _48296) term178). Qed.
Lemma lem4113368 (_48296 : int) : (term476 _48296) = (term477 _48296).
Proof. exact (@lem1982713 term178 (real_of_int _48296)). Qed.
Lemma lem4113370 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113371 : term111 = term200.
Proof. exact (@lem4113370 term20). Qed.
Lemma lem4113373 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4113374 : term178 = term179.
Proof. exact (@lem4113373 term20). Qed.
Lemma lem4113375 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4113376 : term478 = term479.
Proof. exact (MK_COMB (@lem4113375) (@lem4113374)). Qed.
Lemma lem4113377 : term480 = term481.
Proof. exact (MK_COMB (@lem4113376) (@lem4113371)). Qed.
Lemma lem4113378 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4113380 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113381 : term206 = term207.
Proof. exact (@lem4113380 (NUMERAL 0) term20). Qed.
Lemma lem4113382 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113383 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113384 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113383 h1) (fun h1 : term207 = True => @lem4113382)). Qed.
Lemma lem4113385 : term207 = True.
Proof. exact (EQ_MP (@lem4113384) (@lem4113382)). Qed.
Lemma lem4113386 : term206 = True.
Proof. exact (TRANS (@lem4113381) (@lem4113385)). Qed.
Lemma lem4113387 : True = term206.
Proof. exact (SYM (@lem4113386)). Qed.
Lemma lem4113388 : term206.
Proof. exact (EQ_MP (@lem4113387) (@lem0)). Qed.
Lemma lem4113389 : term483.
Proof. exact (@lem4113378 (@lem4113388)). Qed.
Lemma lem4113391 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113392 : term206 = term207.
Proof. exact (@lem4113391 (NUMERAL 0) term20). Qed.
Lemma lem4113393 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113394 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113395 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113394 h1) (fun h1 : term207 = True => @lem4113393)). Qed.
Lemma lem4113396 : term207 = True.
Proof. exact (EQ_MP (@lem4113395) (@lem4113393)). Qed.
Lemma lem4113397 : term206 = True.
Proof. exact (TRANS (@lem4113392) (@lem4113396)). Qed.
Lemma lem4113398 : True = term206.
Proof. exact (SYM (@lem4113397)). Qed.
Lemma lem4113399 : term206.
Proof. exact (EQ_MP (@lem4113398) (@lem0)). Qed.
Lemma lem4113400 : term484.
Proof. exact (@lem4113389 (@lem4113399)). Qed.
Lemma lem4113402 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113403 : term206 = term207.
Proof. exact (@lem4113402 (NUMERAL 0) term20). Qed.
Lemma lem4113404 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113405 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113406 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113405 h1) (fun h1 : term207 = True => @lem4113404)). Qed.
Lemma lem4113407 : term207 = True.
Proof. exact (EQ_MP (@lem4113406) (@lem4113404)). Qed.
Lemma lem4113408 : term206 = True.
Proof. exact (TRANS (@lem4113403) (@lem4113407)). Qed.
Lemma lem4113409 : True = term206.
Proof. exact (SYM (@lem4113408)). Qed.
Lemma lem4113410 : term206.
Proof. exact (EQ_MP (@lem4113409) (@lem0)). Qed.
Lemma lem4113411 : term485.
Proof. exact (@lem4113400 (@lem4113410)). Qed.
Lemma lem4113413 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4113414 : term187 = term188.
Proof. exact (@lem4113413 term20 term20). Qed.
Lemma lem4113415 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113416 : term190 = term20.
Proof. exact (EQ_MP (@lem4113415) (@lem940073)). Qed.
Lemma lem4113417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113418 : term188 = term111.
Proof. exact (MK_COMB (@lem4113417) (@lem4113416)). Qed.
Lemma lem4113419 : term187 = term111.
Proof. exact (TRANS (@lem4113414) (@lem4113418)). Qed.
Lemma lem4113421 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4113422 : term254 = term257.
Proof. exact (@lem4113421 term20 term20). Qed.
Lemma lem4113423 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113424 : term190 = term20.
Proof. exact (EQ_MP (@lem4113423) (@lem940073)). Qed.
Lemma lem4113425 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113426 : term188 = term111.
Proof. exact (MK_COMB (@lem4113425) (@lem4113424)). Qed.
Lemma lem4113427 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4113428 : term257 = term178.
Proof. exact (MK_COMB (@lem4113427) (@lem4113426)). Qed.
Lemma lem4113429 : term254 = term178.
Proof. exact (TRANS (@lem4113422) (@lem4113428)). Qed.
Lemma lem4113430 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4113431 : term486 = term478.
Proof. exact (MK_COMB (@lem4113430) (@lem4113429)). Qed.
Lemma lem4113432 : term487 = term480.
Proof. exact (MK_COMB (@lem4113431) (@lem4113419)). Qed.
Lemma lem4113434 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4113435 : term480 = term97.
Proof. exact (@lem4113434 term20). Qed.
Lemma lem4113436 : term487 = term97.
Proof. exact (TRANS (@lem4113432) (@lem4113435)). Qed.
Lemma lem4113437 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4113438 : term489 = term291.
Proof. exact (MK_COMB (@lem4113437) (@lem4113436)). Qed.
Lemma lem4113439 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4113440 : term490 = term293.
Proof. exact (MK_COMB (@lem4113438) (@lem4113439)). Qed.
Lemma lem4113442 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113443 : term293 = term97.
Proof. exact (@lem4113442 term20). Qed.
Lemma lem4113444 : term490 = term97.
Proof. exact (TRANS (@lem4113440) (@lem4113443)). Qed.
Lemma lem4113446 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4113447 : term187 = term188.
Proof. exact (@lem4113446 term20 term20). Qed.
Lemma lem4113448 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113449 : term190 = term20.
Proof. exact (EQ_MP (@lem4113448) (@lem940073)). Qed.
Lemma lem4113450 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113451 : term188 = term111.
Proof. exact (MK_COMB (@lem4113450) (@lem4113449)). Qed.
Lemma lem4113452 : term187 = term111.
Proof. exact (TRANS (@lem4113447) (@lem4113451)). Qed.
Lemma lem4113453 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4113454 : term295 = term293.
Proof. exact (MK_COMB (@lem4113453) (@lem4113452)). Qed.
Lemma lem4113456 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113457 : term293 = term97.
Proof. exact (@lem4113456 term20). Qed.
Lemma lem4113458 : term295 = term97.
Proof. exact (TRANS (@lem4113454) (@lem4113457)). Qed.
Lemma lem4113459 : term97 = term295.
Proof. exact (SYM (@lem4113458)). Qed.
Lemma lem4113460 : term490 = term295.
Proof. exact (TRANS (@lem4113444) (@lem4113459)). Qed.
Lemma lem4113461 : term481 = term175.
Proof. exact (@lem4113411 (@lem4113460)). Qed.
Lemma lem4113462 : term480 = term175.
Proof. exact (TRANS (@lem4113377) (@lem4113461)). Qed.
Lemma lem4113464 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4113465 : term175 = term97.
Proof. exact (@lem4113464 term97). Qed.
Lemma lem4113466 : term480 = term97.
Proof. exact (TRANS (@lem4113462) (@lem4113465)). Qed.
Lemma lem4113467 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4113468 : term491 = term291.
Proof. exact (MK_COMB (@lem4113467) (@lem4113466)). Qed.
Lemma lem4113469 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4113470 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4113468) (@lem4113469 _48296)). Qed.
Lemma lem4113471 (_48296 : int) : (term476 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4113368 _48296) (@lem4113470 _48296)). Qed.
Lemma lem4113472 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4113473 (_48296 : int) : (term476 _48296) = term97.
Proof. exact (TRANS (@lem4113471 _48296) (@lem4113472 _48296)). Qed.
Lemma lem4113474 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4113475 (_48296 : int) : (term493 _48296) = term139.
Proof. exact (MK_COMB (@lem4113474) (@lem4113473 _48296)). Qed.
Lemma lem4113476 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem4113477 (_48296 : int) : (term538 _48296) = term508.
Proof. exact (MK_COMB (@lem4113475 _48296) (@lem4113476)). Qed.
Lemma lem4113478 (_48296 : int) : (term554 _48296) = term508.
Proof. exact (TRANS (@lem4113367 _48296) (@lem4113477 _48296)). Qed.
Lemma lem4113479 : term508 = term178.
Proof. exact (@lem1982721 term178). Qed.
Lemma lem4113480 (_48296 : int) : (term554 _48296) = term178.
Proof. exact (TRANS (@lem4113478 _48296) (@lem4113479)). Qed.
Lemma lem4113481 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4113482 (_48296 : int) : (term555 _48296) = term510.
Proof. exact (MK_COMB (@lem4113481) (@lem4113480 _48296)). Qed.
Lemma lem4113483 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4113484 (_48296 : int) : (term553 _48296) = term511.
Proof. exact (MK_COMB (@lem4113482 _48296) (@lem4113483)). Qed.
Lemma lem4113485 (_48296 : int) (h1 : term591 _48296) : term511.
Proof. exact (EQ_MP (@lem4113484 _48296) (@lem4113366 _48296 h1)). Qed.
Lemma lem4113487 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4113488 : term511 = term512.
Proof. exact (@lem4113487 term97 term178). Qed.
Lemma lem4113490 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4113491 : term178 = term179.
Proof. exact (@lem4113490 term20). Qed.
Lemma lem4113493 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113494 : term97 = term175.
Proof. exact (@lem4113493 (NUMERAL 0)). Qed.
Lemma lem4113495 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4113496 : term99 = term513.
Proof. exact (MK_COMB (@lem4113495) (@lem4113494)). Qed.
Lemma lem4113497 : term512 = term514.
Proof. exact (MK_COMB (@lem4113496) (@lem4113491)). Qed.
Lemma lem4113498 : term515.
Proof. exact (@lem1980026 term97 term111 term178 term111). Qed.
Lemma lem4113500 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113501 : term206 = term207.
Proof. exact (@lem4113500 (NUMERAL 0) term20). Qed.
Lemma lem4113502 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113503 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113504 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113503 h1) (fun h1 : term207 = True => @lem4113502)). Qed.
Lemma lem4113505 : term207 = True.
Proof. exact (EQ_MP (@lem4113504) (@lem4113502)). Qed.
Lemma lem4113506 : term206 = True.
Proof. exact (TRANS (@lem4113501) (@lem4113505)). Qed.
Lemma lem4113507 : True = term206.
Proof. exact (SYM (@lem4113506)). Qed.
Lemma lem4113508 : term206.
Proof. exact (EQ_MP (@lem4113507) (@lem0)). Qed.
Lemma lem4113509 : term516.
Proof. exact (@lem4113498 (@lem4113508)). Qed.
Lemma lem4113511 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113512 : term206 = term207.
Proof. exact (@lem4113511 (NUMERAL 0) term20). Qed.
Lemma lem4113513 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113514 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113515 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113514 h1) (fun h1 : term207 = True => @lem4113513)). Qed.
Lemma lem4113516 : term207 = True.
Proof. exact (EQ_MP (@lem4113515) (@lem4113513)). Qed.
Lemma lem4113517 : term206 = True.
Proof. exact (TRANS (@lem4113512) (@lem4113516)). Qed.
Lemma lem4113518 : True = term206.
Proof. exact (SYM (@lem4113517)). Qed.
Lemma lem4113519 : term206.
Proof. exact (EQ_MP (@lem4113518) (@lem0)). Qed.
Lemma lem4113520 : term514 = term517.
Proof. exact (@lem4113509 (@lem4113519)). Qed.
Lemma lem4113522 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4113523 : term254 = term257.
Proof. exact (@lem4113522 term20 term20). Qed.
Lemma lem4113524 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113525 : term190 = term20.
Proof. exact (EQ_MP (@lem4113524) (@lem940073)). Qed.
Lemma lem4113526 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113527 : term188 = term111.
Proof. exact (MK_COMB (@lem4113526) (@lem4113525)). Qed.
Lemma lem4113528 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4113529 : term257 = term178.
Proof. exact (MK_COMB (@lem4113528) (@lem4113527)). Qed.
Lemma lem4113530 : term254 = term178.
Proof. exact (TRANS (@lem4113523) (@lem4113529)). Qed.
Lemma lem4113532 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113533 : term293 = term97.
Proof. exact (@lem4113532 term20). Qed.
Lemma lem4113534 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4113535 : term518 = term99.
Proof. exact (MK_COMB (@lem4113534) (@lem4113533)). Qed.
Lemma lem4113536 : term517 = term512.
Proof. exact (MK_COMB (@lem4113535) (@lem4113530)). Qed.
Lemma lem4113538 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4113539 : term512 = term521.
Proof. exact (@lem4113538 (NUMERAL 0) term20). Qed.
Lemma lem4113540 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113541 (h1 : term208 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4113542 : (term208 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113541 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem4113540)). Qed.
Lemma lem4113543 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4113542) (@lem4113540)). Qed.
Lemma lem4113544 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4113545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4113546 : term522 = (and True).
Proof. exact (MK_COMB (@lem4113545) (@lem4113544)). Qed.
Lemma lem4113547 : term521 = (True /\ False).
Proof. exact (MK_COMB (@lem4113546) (@lem4113543)). Qed.
Lemma lem4113549 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4113550 : term521 = False.
Proof. exact (TRANS (@lem4113547) (@lem4113549)). Qed.
Lemma lem4113551 : term512 = False.
Proof. exact (TRANS (@lem4113539) (@lem4113550)). Qed.
Lemma lem4113552 : term517 = False.
Proof. exact (TRANS (@lem4113536) (@lem4113551)). Qed.
Lemma lem4113553 : term514 = False.
Proof. exact (TRANS (@lem4113520) (@lem4113552)). Qed.
Lemma lem4113554 : term512 = False.
Proof. exact (TRANS (@lem4113497) (@lem4113553)). Qed.
Lemma lem4113555 : term511 = False.
Proof. exact (TRANS (@lem4113488) (@lem4113554)). Qed.
Lemma lem4113556 (_48296 : int) (h1 : term591 _48296) : False.
Proof. exact (EQ_MP (@lem4113555) (@lem4113485 _48296 h1)). Qed.
Lemma lem4113557 (_48296 : int) (h1 : term418 _48296) : False.
Proof. exact (or_elim (@lem4112978 _48296 h1) (fun h0 : term580 _48296 => @lem4113267 _48296 h0) (fun h0 : term591 _48296 => @lem4113556 _48296 h0)). Qed.
Lemma lem4113558 (_48296 : int) (h1 : term414 _48296) : term414 _48296.
Proof. exact (h1). Qed.
Lemma lem4113559 (_48296 : int) (h1 : term594 _48296) : term594 _48296.
Proof. exact (h1). Qed.
Lemma lem4113560 (_48296 : int) (h1 : term594 _48296) : term415 _48296.
Proof. exact (proj2 (@lem4113559 _48296 h1)). Qed.
Lemma lem4113562 (_48296 : int) (h1 : term594 _48296) : (real_of_int _48296) = term97.
Proof. exact (proj2 (@lem4113560 _48296 h1)). Qed.
Lemma lem4113563 (_48296 : int) (h1 : term594 _48296) : term343 _48296.
Proof. exact (proj1 (@lem4113560 _48296 h1)). Qed.
Lemma lem4113564 (_48296 : int) (h1 : term594 _48296) : term248 _48296.
Proof. exact (proj2 (@lem4113563 _48296 h1)). Qed.
Lemma lem4113567 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4113568 : term451 = term206.
Proof. exact (@lem4113567 term97 term111). Qed.
Lemma lem4113570 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113571 : term111 = term200.
Proof. exact (@lem4113570 term20). Qed.
Lemma lem4113573 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113574 : term97 = term175.
Proof. exact (@lem4113573 (NUMERAL 0)). Qed.
Lemma lem4113575 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4113576 : term452 = term453.
Proof. exact (MK_COMB (@lem4113575) (@lem4113574)). Qed.
Lemma lem4113577 : term206 = term454.
Proof. exact (MK_COMB (@lem4113576) (@lem4113571)). Qed.
Lemma lem4113578 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4113580 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113581 : term206 = term207.
Proof. exact (@lem4113580 (NUMERAL 0) term20). Qed.
Lemma lem4113582 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113583 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113584 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113583 h1) (fun h1 : term207 = True => @lem4113582)). Qed.
Lemma lem4113585 : term207 = True.
Proof. exact (EQ_MP (@lem4113584) (@lem4113582)). Qed.
Lemma lem4113586 : term206 = True.
Proof. exact (TRANS (@lem4113581) (@lem4113585)). Qed.
Lemma lem4113587 : True = term206.
Proof. exact (SYM (@lem4113586)). Qed.
Lemma lem4113588 : term206.
Proof. exact (EQ_MP (@lem4113587) (@lem0)). Qed.
Lemma lem4113589 : term456.
Proof. exact (@lem4113578 (@lem4113588)). Qed.
Lemma lem4113591 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113592 : term206 = term207.
Proof. exact (@lem4113591 (NUMERAL 0) term20). Qed.
Lemma lem4113593 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113594 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113595 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113594 h1) (fun h1 : term207 = True => @lem4113593)). Qed.
Lemma lem4113596 : term207 = True.
Proof. exact (EQ_MP (@lem4113595) (@lem4113593)). Qed.
Lemma lem4113597 : term206 = True.
Proof. exact (TRANS (@lem4113592) (@lem4113596)). Qed.
Lemma lem4113598 : True = term206.
Proof. exact (SYM (@lem4113597)). Qed.
Lemma lem4113599 : term206.
Proof. exact (EQ_MP (@lem4113598) (@lem0)). Qed.
Lemma lem4113600 : term454 = term457.
Proof. exact (@lem4113589 (@lem4113599)). Qed.
Lemma lem4113602 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4113603 : term187 = term188.
Proof. exact (@lem4113602 term20 term20). Qed.
Lemma lem4113604 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113605 : term190 = term20.
Proof. exact (EQ_MP (@lem4113604) (@lem940073)). Qed.
Lemma lem4113606 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113607 : term188 = term111.
Proof. exact (MK_COMB (@lem4113606) (@lem4113605)). Qed.
Lemma lem4113608 : term187 = term111.
Proof. exact (TRANS (@lem4113603) (@lem4113607)). Qed.
Lemma lem4113610 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113611 : term293 = term97.
Proof. exact (@lem4113610 term20). Qed.
Lemma lem4113612 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4113613 : term458 = term452.
Proof. exact (MK_COMB (@lem4113612) (@lem4113611)). Qed.
Lemma lem4113614 : term457 = term206.
Proof. exact (MK_COMB (@lem4113613) (@lem4113608)). Qed.
Lemma lem4113616 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113617 : term206 = term207.
Proof. exact (@lem4113616 (NUMERAL 0) term20). Qed.
Lemma lem4113618 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113619 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113620 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113619 h1) (fun h1 : term207 = True => @lem4113618)). Qed.
Lemma lem4113621 : term207 = True.
Proof. exact (EQ_MP (@lem4113620) (@lem4113618)). Qed.
Lemma lem4113622 : term206 = True.
Proof. exact (TRANS (@lem4113617) (@lem4113621)). Qed.
Lemma lem4113623 : term457 = True.
Proof. exact (TRANS (@lem4113614) (@lem4113622)). Qed.
Lemma lem4113624 : term454 = True.
Proof. exact (TRANS (@lem4113600) (@lem4113623)). Qed.
Lemma lem4113625 : term206 = True.
Proof. exact (TRANS (@lem4113577) (@lem4113624)). Qed.
Lemma lem4113626 : term451 = True.
Proof. exact (TRANS (@lem4113568) (@lem4113625)). Qed.
Lemma lem4113627 : True = term451.
Proof. exact (SYM (@lem4113626)). Qed.
Lemma lem4113628 : term451.
Proof. exact (EQ_MP (@lem4113627) (@lem0)). Qed.
Lemma lem4113629 (_48296 : int) (h1 : term594 _48296) : term459 _48296.
Proof. exact (conj (@lem4113628) (@lem4113564 _48296 h1)). Qed.
Lemma lem4113631 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4113632 (_48296 : int) : term461 _48296.
Proof. exact (@lem4113631 term111 (term245 _48296)). Qed.
Lemma lem4113633 (_48296 : int) (h1 : term594 _48296) : term462 _48296.
Proof. exact (@lem4113632 _48296 (@lem4113629 _48296 h1)). Qed.
Lemma lem4113634 (_48296 : int) : (term463 _48296) = (term245 _48296).
Proof. exact (@lem1982733 (term245 _48296)). Qed.
Lemma lem4113635 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4113636 (_48296 : int) : (term464 _48296) = (term247 _48296).
Proof. exact (MK_COMB (@lem4113635) (@lem4113634 _48296)). Qed.
Lemma lem4113637 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4113638 (_48296 : int) : (term462 _48296) = (term248 _48296).
Proof. exact (MK_COMB (@lem4113636 _48296) (@lem4113637)). Qed.
Lemma lem4113639 (_48296 : int) (h1 : term594 _48296) : term248 _48296.
Proof. exact (EQ_MP (@lem4113638 _48296) (@lem4113633 _48296 h1)). Qed.
Lemma lem4113641 (y : real) : term559 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem4113642 (_48296 : int) : term560 _48296.
Proof. exact (@lem4113641 (real_of_int _48296)). Qed.
Lemma lem4113643 (_48296 : int) (h1 : term594 _48296) : term561 _48296.
Proof. exact (@lem4113642 _48296 (@lem4113562 _48296 h1)). Qed.
Lemma lem4113644 (_48296 : int) (h1 : term594 _48296) : term562 _48296.
Proof. exact (@lem4113643 _48296 h1 term178). Qed.
Lemma lem4113645 (_48296 : int) : (term562 _48296) = ((term281 _48296) = term97).
Proof. exact (eq_refl (term562 _48296)). Qed.
Lemma lem4113652 (_48296 : int) (h1 : term594 _48296) : (term281 _48296) = term97.
Proof. exact (EQ_MP (@lem4113645 _48296) (@lem4113644 _48296 h1)). Qed.
Lemma lem4113653 (_48296 : int) (h1 : term594 _48296) : term563 _48296.
Proof. exact (conj (@lem4113652 _48296 h1) (@lem4113639 _48296 h1)). Qed.
Lemma lem4113655 (x : real) (y : real) : term564 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem4113656 (_48296 : int) : term565 _48296.
Proof. exact (@lem4113655 (term281 _48296) (term245 _48296)). Qed.
Lemma lem4113657 (_48296 : int) (h1 : term594 _48296) : term566 _48296.
Proof. exact (@lem4113656 _48296 (@lem4113653 _48296 h1)). Qed.
Lemma lem4113658 (_48296 : int) : (term567 _48296) = (term568 _48296).
Proof. exact (@lem1982763 (term281 _48296) (real_of_int _48296) term241). Qed.
Lemma lem4113659 (_48296 : int) : (term476 _48296) = (term477 _48296).
Proof. exact (@lem1982713 term178 (real_of_int _48296)). Qed.
Lemma lem4113661 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113662 : term111 = term200.
Proof. exact (@lem4113661 term20). Qed.
Lemma lem4113664 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4113665 : term178 = term179.
Proof. exact (@lem4113664 term20). Qed.
Lemma lem4113666 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4113667 : term478 = term479.
Proof. exact (MK_COMB (@lem4113666) (@lem4113665)). Qed.
Lemma lem4113668 : term480 = term481.
Proof. exact (MK_COMB (@lem4113667) (@lem4113662)). Qed.
Lemma lem4113669 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4113671 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113672 : term206 = term207.
Proof. exact (@lem4113671 (NUMERAL 0) term20). Qed.
Lemma lem4113673 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113674 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113675 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113674 h1) (fun h1 : term207 = True => @lem4113673)). Qed.
Lemma lem4113676 : term207 = True.
Proof. exact (EQ_MP (@lem4113675) (@lem4113673)). Qed.
Lemma lem4113677 : term206 = True.
Proof. exact (TRANS (@lem4113672) (@lem4113676)). Qed.
Lemma lem4113678 : True = term206.
Proof. exact (SYM (@lem4113677)). Qed.
Lemma lem4113679 : term206.
Proof. exact (EQ_MP (@lem4113678) (@lem0)). Qed.
Lemma lem4113680 : term483.
Proof. exact (@lem4113669 (@lem4113679)). Qed.
Lemma lem4113682 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113683 : term206 = term207.
Proof. exact (@lem4113682 (NUMERAL 0) term20). Qed.
Lemma lem4113684 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113685 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113686 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113685 h1) (fun h1 : term207 = True => @lem4113684)). Qed.
Lemma lem4113687 : term207 = True.
Proof. exact (EQ_MP (@lem4113686) (@lem4113684)). Qed.
Lemma lem4113688 : term206 = True.
Proof. exact (TRANS (@lem4113683) (@lem4113687)). Qed.
Lemma lem4113689 : True = term206.
Proof. exact (SYM (@lem4113688)). Qed.
Lemma lem4113690 : term206.
Proof. exact (EQ_MP (@lem4113689) (@lem0)). Qed.
Lemma lem4113691 : term484.
Proof. exact (@lem4113680 (@lem4113690)). Qed.
Lemma lem4113693 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113694 : term206 = term207.
Proof. exact (@lem4113693 (NUMERAL 0) term20). Qed.
Lemma lem4113695 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113696 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113697 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113696 h1) (fun h1 : term207 = True => @lem4113695)). Qed.
Lemma lem4113698 : term207 = True.
Proof. exact (EQ_MP (@lem4113697) (@lem4113695)). Qed.
Lemma lem4113699 : term206 = True.
Proof. exact (TRANS (@lem4113694) (@lem4113698)). Qed.
Lemma lem4113700 : True = term206.
Proof. exact (SYM (@lem4113699)). Qed.
Lemma lem4113701 : term206.
Proof. exact (EQ_MP (@lem4113700) (@lem0)). Qed.
Lemma lem4113702 : term485.
Proof. exact (@lem4113691 (@lem4113701)). Qed.
Lemma lem4113704 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4113705 : term187 = term188.
Proof. exact (@lem4113704 term20 term20). Qed.
Lemma lem4113706 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113707 : term190 = term20.
Proof. exact (EQ_MP (@lem4113706) (@lem940073)). Qed.
Lemma lem4113708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113709 : term188 = term111.
Proof. exact (MK_COMB (@lem4113708) (@lem4113707)). Qed.
Lemma lem4113710 : term187 = term111.
Proof. exact (TRANS (@lem4113705) (@lem4113709)). Qed.
Lemma lem4113712 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4113713 : term254 = term257.
Proof. exact (@lem4113712 term20 term20). Qed.
Lemma lem4113714 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113715 : term190 = term20.
Proof. exact (EQ_MP (@lem4113714) (@lem940073)). Qed.
Lemma lem4113716 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113717 : term188 = term111.
Proof. exact (MK_COMB (@lem4113716) (@lem4113715)). Qed.
Lemma lem4113718 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4113719 : term257 = term178.
Proof. exact (MK_COMB (@lem4113718) (@lem4113717)). Qed.
Lemma lem4113720 : term254 = term178.
Proof. exact (TRANS (@lem4113713) (@lem4113719)). Qed.
Lemma lem4113721 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4113722 : term486 = term478.
Proof. exact (MK_COMB (@lem4113721) (@lem4113720)). Qed.
Lemma lem4113723 : term487 = term480.
Proof. exact (MK_COMB (@lem4113722) (@lem4113710)). Qed.
Lemma lem4113725 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4113726 : term480 = term97.
Proof. exact (@lem4113725 term20). Qed.
Lemma lem4113727 : term487 = term97.
Proof. exact (TRANS (@lem4113723) (@lem4113726)). Qed.
Lemma lem4113728 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4113729 : term489 = term291.
Proof. exact (MK_COMB (@lem4113728) (@lem4113727)). Qed.
Lemma lem4113730 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4113731 : term490 = term293.
Proof. exact (MK_COMB (@lem4113729) (@lem4113730)). Qed.
Lemma lem4113733 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113734 : term293 = term97.
Proof. exact (@lem4113733 term20). Qed.
Lemma lem4113735 : term490 = term97.
Proof. exact (TRANS (@lem4113731) (@lem4113734)). Qed.
Lemma lem4113737 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4113738 : term187 = term188.
Proof. exact (@lem4113737 term20 term20). Qed.
Lemma lem4113739 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113740 : term190 = term20.
Proof. exact (EQ_MP (@lem4113739) (@lem940073)). Qed.
Lemma lem4113741 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113742 : term188 = term111.
Proof. exact (MK_COMB (@lem4113741) (@lem4113740)). Qed.
Lemma lem4113743 : term187 = term111.
Proof. exact (TRANS (@lem4113738) (@lem4113742)). Qed.
Lemma lem4113744 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4113745 : term295 = term293.
Proof. exact (MK_COMB (@lem4113744) (@lem4113743)). Qed.
Lemma lem4113747 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113748 : term293 = term97.
Proof. exact (@lem4113747 term20). Qed.
Lemma lem4113749 : term295 = term97.
Proof. exact (TRANS (@lem4113745) (@lem4113748)). Qed.
Lemma lem4113750 : term97 = term295.
Proof. exact (SYM (@lem4113749)). Qed.
Lemma lem4113751 : term490 = term295.
Proof. exact (TRANS (@lem4113735) (@lem4113750)). Qed.
Lemma lem4113752 : term481 = term175.
Proof. exact (@lem4113702 (@lem4113751)). Qed.
Lemma lem4113753 : term480 = term175.
Proof. exact (TRANS (@lem4113668) (@lem4113752)). Qed.
Lemma lem4113755 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4113756 : term175 = term97.
Proof. exact (@lem4113755 term97). Qed.
Lemma lem4113757 : term480 = term97.
Proof. exact (TRANS (@lem4113753) (@lem4113756)). Qed.
Lemma lem4113758 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4113759 : term491 = term291.
Proof. exact (MK_COMB (@lem4113758) (@lem4113757)). Qed.
Lemma lem4113760 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4113761 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4113759) (@lem4113760 _48296)). Qed.
Lemma lem4113762 (_48296 : int) : (term476 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4113659 _48296) (@lem4113761 _48296)). Qed.
Lemma lem4113763 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4113764 (_48296 : int) : (term476 _48296) = term97.
Proof. exact (TRANS (@lem4113762 _48296) (@lem4113763 _48296)). Qed.
Lemma lem4113765 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4113766 (_48296 : int) : (term493 _48296) = term139.
Proof. exact (MK_COMB (@lem4113765) (@lem4113764 _48296)). Qed.
Lemma lem4113767 : term241 = term241.
Proof. exact (eq_refl term241). Qed.
Lemma lem4113768 (_48296 : int) : (term568 _48296) = term569.
Proof. exact (MK_COMB (@lem4113766 _48296) (@lem4113767)). Qed.
Lemma lem4113769 (_48296 : int) : (term567 _48296) = term569.
Proof. exact (TRANS (@lem4113658 _48296) (@lem4113768 _48296)). Qed.
Lemma lem4113770 : term569 = term241.
Proof. exact (@lem1982721 term241). Qed.
Lemma lem4113771 (_48296 : int) : (term567 _48296) = term241.
Proof. exact (TRANS (@lem4113769 _48296) (@lem4113770)). Qed.
Lemma lem4113772 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4113773 (_48296 : int) : (term570 _48296) = term571.
Proof. exact (MK_COMB (@lem4113772) (@lem4113771 _48296)). Qed.
Lemma lem4113774 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4113775 (_48296 : int) : (term566 _48296) = term572.
Proof. exact (MK_COMB (@lem4113773 _48296) (@lem4113774)). Qed.
Lemma lem4113776 (_48296 : int) (h1 : term594 _48296) : term572.
Proof. exact (EQ_MP (@lem4113775 _48296) (@lem4113657 _48296 h1)). Qed.
Lemma lem4113778 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4113779 : term572 = term573.
Proof. exact (@lem4113778 term97 term241). Qed.
Lemma lem4113781 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4113782 : term241 = term244.
Proof. exact (@lem4113781 term218). Qed.
Lemma lem4113784 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113785 : term97 = term175.
Proof. exact (@lem4113784 (NUMERAL 0)). Qed.
Lemma lem4113786 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4113787 : term99 = term513.
Proof. exact (MK_COMB (@lem4113786) (@lem4113785)). Qed.
Lemma lem4113788 : term573 = term574.
Proof. exact (MK_COMB (@lem4113787) (@lem4113782)). Qed.
Lemma lem4113789 : term575.
Proof. exact (@lem1980026 term97 term111 term241 term111). Qed.
Lemma lem4113791 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113792 : term206 = term207.
Proof. exact (@lem4113791 (NUMERAL 0) term20). Qed.
Lemma lem4113793 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113794 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113795 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113794 h1) (fun h1 : term207 = True => @lem4113793)). Qed.
Lemma lem4113796 : term207 = True.
Proof. exact (EQ_MP (@lem4113795) (@lem4113793)). Qed.
Lemma lem4113797 : term206 = True.
Proof. exact (TRANS (@lem4113792) (@lem4113796)). Qed.
Lemma lem4113798 : True = term206.
Proof. exact (SYM (@lem4113797)). Qed.
Lemma lem4113799 : term206.
Proof. exact (EQ_MP (@lem4113798) (@lem0)). Qed.
Lemma lem4113800 : term576.
Proof. exact (@lem4113789 (@lem4113799)). Qed.
Lemma lem4113802 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113803 : term206 = term207.
Proof. exact (@lem4113802 (NUMERAL 0) term20). Qed.
Lemma lem4113804 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113805 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113806 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113805 h1) (fun h1 : term207 = True => @lem4113804)). Qed.
Lemma lem4113807 : term207 = True.
Proof. exact (EQ_MP (@lem4113806) (@lem4113804)). Qed.
Lemma lem4113808 : term206 = True.
Proof. exact (TRANS (@lem4113803) (@lem4113807)). Qed.
Lemma lem4113809 : True = term206.
Proof. exact (SYM (@lem4113808)). Qed.
Lemma lem4113810 : term206.
Proof. exact (EQ_MP (@lem4113809) (@lem0)). Qed.
Lemma lem4113811 : term574 = term577.
Proof. exact (@lem4113800 (@lem4113810)). Qed.
Lemma lem4113813 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4113814 : term500 = term501.
Proof. exact (@lem4113813 term218 term20). Qed.
Lemma lem4113815 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4113816 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4113817 : term225 = term218.
Proof. exact (EQ_MP (@lem4113816) (@lem4113815)). Qed.
Lemma lem4113818 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113819 : term223 = term204.
Proof. exact (MK_COMB (@lem4113818) (@lem4113817)). Qed.
Lemma lem4113820 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4113821 : term501 = term241.
Proof. exact (MK_COMB (@lem4113820) (@lem4113819)). Qed.
Lemma lem4113822 : term500 = term241.
Proof. exact (TRANS (@lem4113814) (@lem4113821)). Qed.
Lemma lem4113824 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113825 : term293 = term97.
Proof. exact (@lem4113824 term20). Qed.
Lemma lem4113826 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4113827 : term518 = term99.
Proof. exact (MK_COMB (@lem4113826) (@lem4113825)). Qed.
Lemma lem4113828 : term577 = term573.
Proof. exact (MK_COMB (@lem4113827) (@lem4113822)). Qed.
Lemma lem4113830 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4113831 : term573 = term578.
Proof. exact (@lem4113830 (NUMERAL 0) term218). Qed.
Lemma lem4113832 : term579 = term216.
Proof. exact (@lem912803). Qed.
Lemma lem4113833 (h1 : term579 = term216) : (term218 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term216 h1). Qed.
Lemma lem4113834 : (term579 = term216) = ((term218 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term579 = term216 => @lem4113833 h1) (fun h1 : (term218 = (NUMERAL 0)) = False => @lem4113832)). Qed.
Lemma lem4113835 : (term218 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4113834) (@lem4113832)). Qed.
Lemma lem4113836 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4113837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4113838 : term522 = (and True).
Proof. exact (MK_COMB (@lem4113837) (@lem4113836)). Qed.
Lemma lem4113839 : term578 = (True /\ False).
Proof. exact (MK_COMB (@lem4113838) (@lem4113835)). Qed.
Lemma lem4113841 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4113842 : term578 = False.
Proof. exact (TRANS (@lem4113839) (@lem4113841)). Qed.
Lemma lem4113843 : term573 = False.
Proof. exact (TRANS (@lem4113831) (@lem4113842)). Qed.
Lemma lem4113844 : term577 = False.
Proof. exact (TRANS (@lem4113828) (@lem4113843)). Qed.
Lemma lem4113845 : term574 = False.
Proof. exact (TRANS (@lem4113811) (@lem4113844)). Qed.
Lemma lem4113846 : term573 = False.
Proof. exact (TRANS (@lem4113788) (@lem4113845)). Qed.
Lemma lem4113847 : term572 = False.
Proof. exact (TRANS (@lem4113779) (@lem4113846)). Qed.
Lemma lem4113848 (_48296 : int) (h1 : term594 _48296) : False.
Proof. exact (EQ_MP (@lem4113847) (@lem4113776 _48296 h1)). Qed.
Lemma lem4113849 (_48296 : int) (h1 : term595 _48296) : term595 _48296.
Proof. exact (h1). Qed.
Lemma lem4113850 (_48296 : int) (h1 : term595 _48296) : term416 _48296.
Proof. exact (proj2 (@lem4113849 _48296 h1)). Qed.
Lemma lem4113852 (_48296 : int) (h1 : term595 _48296) : (real_of_int _48296) = term97.
Proof. exact (proj2 (@lem4113850 _48296 h1)). Qed.
Lemma lem4113853 (_48296 : int) (h1 : term595 _48296) : term344 _48296.
Proof. exact (proj1 (@lem4113850 _48296 h1)). Qed.
Lemma lem4113854 (_48296 : int) (h1 : term595 _48296) : term248 _48296.
Proof. exact (proj2 (@lem4113853 _48296 h1)). Qed.
Lemma lem4113857 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4113858 : term451 = term206.
Proof. exact (@lem4113857 term97 term111). Qed.
Lemma lem4113860 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113861 : term111 = term200.
Proof. exact (@lem4113860 term20). Qed.
Lemma lem4113863 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113864 : term97 = term175.
Proof. exact (@lem4113863 (NUMERAL 0)). Qed.
Lemma lem4113865 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4113866 : term452 = term453.
Proof. exact (MK_COMB (@lem4113865) (@lem4113864)). Qed.
Lemma lem4113867 : term206 = term454.
Proof. exact (MK_COMB (@lem4113866) (@lem4113861)). Qed.
Lemma lem4113868 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4113870 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113871 : term206 = term207.
Proof. exact (@lem4113870 (NUMERAL 0) term20). Qed.
Lemma lem4113872 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113873 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113874 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113873 h1) (fun h1 : term207 = True => @lem4113872)). Qed.
Lemma lem4113875 : term207 = True.
Proof. exact (EQ_MP (@lem4113874) (@lem4113872)). Qed.
Lemma lem4113876 : term206 = True.
Proof. exact (TRANS (@lem4113871) (@lem4113875)). Qed.
Lemma lem4113877 : True = term206.
Proof. exact (SYM (@lem4113876)). Qed.
Lemma lem4113878 : term206.
Proof. exact (EQ_MP (@lem4113877) (@lem0)). Qed.
Lemma lem4113879 : term456.
Proof. exact (@lem4113868 (@lem4113878)). Qed.
Lemma lem4113881 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113882 : term206 = term207.
Proof. exact (@lem4113881 (NUMERAL 0) term20). Qed.
Lemma lem4113883 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113884 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113885 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113884 h1) (fun h1 : term207 = True => @lem4113883)). Qed.
Lemma lem4113886 : term207 = True.
Proof. exact (EQ_MP (@lem4113885) (@lem4113883)). Qed.
Lemma lem4113887 : term206 = True.
Proof. exact (TRANS (@lem4113882) (@lem4113886)). Qed.
Lemma lem4113888 : True = term206.
Proof. exact (SYM (@lem4113887)). Qed.
Lemma lem4113889 : term206.
Proof. exact (EQ_MP (@lem4113888) (@lem0)). Qed.
Lemma lem4113890 : term454 = term457.
Proof. exact (@lem4113879 (@lem4113889)). Qed.
Lemma lem4113892 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4113893 : term187 = term188.
Proof. exact (@lem4113892 term20 term20). Qed.
Lemma lem4113894 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113895 : term190 = term20.
Proof. exact (EQ_MP (@lem4113894) (@lem940073)). Qed.
Lemma lem4113896 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113897 : term188 = term111.
Proof. exact (MK_COMB (@lem4113896) (@lem4113895)). Qed.
Lemma lem4113898 : term187 = term111.
Proof. exact (TRANS (@lem4113893) (@lem4113897)). Qed.
Lemma lem4113900 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4113901 : term293 = term97.
Proof. exact (@lem4113900 term20). Qed.
Lemma lem4113902 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4113903 : term458 = term452.
Proof. exact (MK_COMB (@lem4113902) (@lem4113901)). Qed.
Lemma lem4113904 : term457 = term206.
Proof. exact (MK_COMB (@lem4113903) (@lem4113898)). Qed.
Lemma lem4113906 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113907 : term206 = term207.
Proof. exact (@lem4113906 (NUMERAL 0) term20). Qed.
Lemma lem4113908 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113909 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113910 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113909 h1) (fun h1 : term207 = True => @lem4113908)). Qed.
Lemma lem4113911 : term207 = True.
Proof. exact (EQ_MP (@lem4113910) (@lem4113908)). Qed.
Lemma lem4113912 : term206 = True.
Proof. exact (TRANS (@lem4113907) (@lem4113911)). Qed.
Lemma lem4113913 : term457 = True.
Proof. exact (TRANS (@lem4113904) (@lem4113912)). Qed.
Lemma lem4113914 : term454 = True.
Proof. exact (TRANS (@lem4113890) (@lem4113913)). Qed.
Lemma lem4113915 : term206 = True.
Proof. exact (TRANS (@lem4113867) (@lem4113914)). Qed.
Lemma lem4113916 : term451 = True.
Proof. exact (TRANS (@lem4113858) (@lem4113915)). Qed.
Lemma lem4113917 : True = term451.
Proof. exact (SYM (@lem4113916)). Qed.
Lemma lem4113918 : term451.
Proof. exact (EQ_MP (@lem4113917) (@lem0)). Qed.
Lemma lem4113919 (_48296 : int) (h1 : term595 _48296) : term459 _48296.
Proof. exact (conj (@lem4113918) (@lem4113854 _48296 h1)). Qed.
Lemma lem4113921 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4113922 (_48296 : int) : term461 _48296.
Proof. exact (@lem4113921 term111 (term245 _48296)). Qed.
Lemma lem4113923 (_48296 : int) (h1 : term595 _48296) : term462 _48296.
Proof. exact (@lem4113922 _48296 (@lem4113919 _48296 h1)). Qed.
Lemma lem4113924 (_48296 : int) : (term463 _48296) = (term245 _48296).
Proof. exact (@lem1982733 (term245 _48296)). Qed.
Lemma lem4113925 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4113926 (_48296 : int) : (term464 _48296) = (term247 _48296).
Proof. exact (MK_COMB (@lem4113925) (@lem4113924 _48296)). Qed.
Lemma lem4113927 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4113928 (_48296 : int) : (term462 _48296) = (term248 _48296).
Proof. exact (MK_COMB (@lem4113926 _48296) (@lem4113927)). Qed.
Lemma lem4113929 (_48296 : int) (h1 : term595 _48296) : term248 _48296.
Proof. exact (EQ_MP (@lem4113928 _48296) (@lem4113923 _48296 h1)). Qed.
Lemma lem4113931 (y : real) : term559 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem4113932 (_48296 : int) : term560 _48296.
Proof. exact (@lem4113931 (real_of_int _48296)). Qed.
Lemma lem4113933 (_48296 : int) (h1 : term595 _48296) : term561 _48296.
Proof. exact (@lem4113932 _48296 (@lem4113852 _48296 h1)). Qed.
Lemma lem4113934 (_48296 : int) (h1 : term595 _48296) : term562 _48296.
Proof. exact (@lem4113933 _48296 h1 term178). Qed.
Lemma lem4113935 (_48296 : int) : (term562 _48296) = ((term281 _48296) = term97).
Proof. exact (eq_refl (term562 _48296)). Qed.
Lemma lem4113942 (_48296 : int) (h1 : term595 _48296) : (term281 _48296) = term97.
Proof. exact (EQ_MP (@lem4113935 _48296) (@lem4113934 _48296 h1)). Qed.
Lemma lem4113943 (_48296 : int) (h1 : term595 _48296) : term563 _48296.
Proof. exact (conj (@lem4113942 _48296 h1) (@lem4113929 _48296 h1)). Qed.
Lemma lem4113945 (x : real) (y : real) : term564 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem4113946 (_48296 : int) : term565 _48296.
Proof. exact (@lem4113945 (term281 _48296) (term245 _48296)). Qed.
Lemma lem4113947 (_48296 : int) (h1 : term595 _48296) : term566 _48296.
Proof. exact (@lem4113946 _48296 (@lem4113943 _48296 h1)). Qed.
Lemma lem4113948 (_48296 : int) : (term567 _48296) = (term568 _48296).
Proof. exact (@lem1982763 (term281 _48296) (real_of_int _48296) term241). Qed.
Lemma lem4113949 (_48296 : int) : (term476 _48296) = (term477 _48296).
Proof. exact (@lem1982713 term178 (real_of_int _48296)). Qed.
Lemma lem4113951 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4113952 : term111 = term200.
Proof. exact (@lem4113951 term20). Qed.
Lemma lem4113954 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4113955 : term178 = term179.
Proof. exact (@lem4113954 term20). Qed.
Lemma lem4113956 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4113957 : term478 = term479.
Proof. exact (MK_COMB (@lem4113956) (@lem4113955)). Qed.
Lemma lem4113958 : term480 = term481.
Proof. exact (MK_COMB (@lem4113957) (@lem4113952)). Qed.
Lemma lem4113959 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4113961 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113962 : term206 = term207.
Proof. exact (@lem4113961 (NUMERAL 0) term20). Qed.
Lemma lem4113963 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113964 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113965 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113964 h1) (fun h1 : term207 = True => @lem4113963)). Qed.
Lemma lem4113966 : term207 = True.
Proof. exact (EQ_MP (@lem4113965) (@lem4113963)). Qed.
Lemma lem4113967 : term206 = True.
Proof. exact (TRANS (@lem4113962) (@lem4113966)). Qed.
Lemma lem4113968 : True = term206.
Proof. exact (SYM (@lem4113967)). Qed.
Lemma lem4113969 : term206.
Proof. exact (EQ_MP (@lem4113968) (@lem0)). Qed.
Lemma lem4113970 : term483.
Proof. exact (@lem4113959 (@lem4113969)). Qed.
Lemma lem4113972 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113973 : term206 = term207.
Proof. exact (@lem4113972 (NUMERAL 0) term20). Qed.
Lemma lem4113974 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113975 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113976 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113975 h1) (fun h1 : term207 = True => @lem4113974)). Qed.
Lemma lem4113977 : term207 = True.
Proof. exact (EQ_MP (@lem4113976) (@lem4113974)). Qed.
Lemma lem4113978 : term206 = True.
Proof. exact (TRANS (@lem4113973) (@lem4113977)). Qed.
Lemma lem4113979 : True = term206.
Proof. exact (SYM (@lem4113978)). Qed.
Lemma lem4113980 : term206.
Proof. exact (EQ_MP (@lem4113979) (@lem0)). Qed.
Lemma lem4113981 : term484.
Proof. exact (@lem4113970 (@lem4113980)). Qed.
Lemma lem4113983 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4113984 : term206 = term207.
Proof. exact (@lem4113983 (NUMERAL 0) term20). Qed.
Lemma lem4113985 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4113986 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4113987 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4113986 h1) (fun h1 : term207 = True => @lem4113985)). Qed.
Lemma lem4113988 : term207 = True.
Proof. exact (EQ_MP (@lem4113987) (@lem4113985)). Qed.
Lemma lem4113989 : term206 = True.
Proof. exact (TRANS (@lem4113984) (@lem4113988)). Qed.
Lemma lem4113990 : True = term206.
Proof. exact (SYM (@lem4113989)). Qed.
Lemma lem4113991 : term206.
Proof. exact (EQ_MP (@lem4113990) (@lem0)). Qed.
Lemma lem4113992 : term485.
Proof. exact (@lem4113981 (@lem4113991)). Qed.
Lemma lem4113994 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4113995 : term187 = term188.
Proof. exact (@lem4113994 term20 term20). Qed.
Lemma lem4113996 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4113997 : term190 = term20.
Proof. exact (EQ_MP (@lem4113996) (@lem940073)). Qed.
Lemma lem4113998 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4113999 : term188 = term111.
Proof. exact (MK_COMB (@lem4113998) (@lem4113997)). Qed.
Lemma lem4114000 : term187 = term111.
Proof. exact (TRANS (@lem4113995) (@lem4113999)). Qed.
Lemma lem4114002 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4114003 : term254 = term257.
Proof. exact (@lem4114002 term20 term20). Qed.
Lemma lem4114004 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114005 : term190 = term20.
Proof. exact (EQ_MP (@lem4114004) (@lem940073)). Qed.
Lemma lem4114006 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114007 : term188 = term111.
Proof. exact (MK_COMB (@lem4114006) (@lem4114005)). Qed.
Lemma lem4114008 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4114009 : term257 = term178.
Proof. exact (MK_COMB (@lem4114008) (@lem4114007)). Qed.
Lemma lem4114010 : term254 = term178.
Proof. exact (TRANS (@lem4114003) (@lem4114009)). Qed.
Lemma lem4114011 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4114012 : term486 = term478.
Proof. exact (MK_COMB (@lem4114011) (@lem4114010)). Qed.
Lemma lem4114013 : term487 = term480.
Proof. exact (MK_COMB (@lem4114012) (@lem4114000)). Qed.
Lemma lem4114015 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4114016 : term480 = term97.
Proof. exact (@lem4114015 term20). Qed.
Lemma lem4114017 : term487 = term97.
Proof. exact (TRANS (@lem4114013) (@lem4114016)). Qed.
Lemma lem4114018 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4114019 : term489 = term291.
Proof. exact (MK_COMB (@lem4114018) (@lem4114017)). Qed.
Lemma lem4114020 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4114021 : term490 = term293.
Proof. exact (MK_COMB (@lem4114019) (@lem4114020)). Qed.
Lemma lem4114023 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4114024 : term293 = term97.
Proof. exact (@lem4114023 term20). Qed.
Lemma lem4114025 : term490 = term97.
Proof. exact (TRANS (@lem4114021) (@lem4114024)). Qed.
Lemma lem4114027 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4114028 : term187 = term188.
Proof. exact (@lem4114027 term20 term20). Qed.
Lemma lem4114029 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114030 : term190 = term20.
Proof. exact (EQ_MP (@lem4114029) (@lem940073)). Qed.
Lemma lem4114031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114032 : term188 = term111.
Proof. exact (MK_COMB (@lem4114031) (@lem4114030)). Qed.
Lemma lem4114033 : term187 = term111.
Proof. exact (TRANS (@lem4114028) (@lem4114032)). Qed.
Lemma lem4114034 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4114035 : term295 = term293.
Proof. exact (MK_COMB (@lem4114034) (@lem4114033)). Qed.
Lemma lem4114037 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4114038 : term293 = term97.
Proof. exact (@lem4114037 term20). Qed.
Lemma lem4114039 : term295 = term97.
Proof. exact (TRANS (@lem4114035) (@lem4114038)). Qed.
Lemma lem4114040 : term97 = term295.
Proof. exact (SYM (@lem4114039)). Qed.
Lemma lem4114041 : term490 = term295.
Proof. exact (TRANS (@lem4114025) (@lem4114040)). Qed.
Lemma lem4114042 : term481 = term175.
Proof. exact (@lem4113992 (@lem4114041)). Qed.
Lemma lem4114043 : term480 = term175.
Proof. exact (TRANS (@lem4113958) (@lem4114042)). Qed.
Lemma lem4114045 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4114046 : term175 = term97.
Proof. exact (@lem4114045 term97). Qed.
Lemma lem4114047 : term480 = term97.
Proof. exact (TRANS (@lem4114043) (@lem4114046)). Qed.
Lemma lem4114048 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4114049 : term491 = term291.
Proof. exact (MK_COMB (@lem4114048) (@lem4114047)). Qed.
Lemma lem4114050 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4114051 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4114049) (@lem4114050 _48296)). Qed.
Lemma lem4114052 (_48296 : int) : (term476 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4113949 _48296) (@lem4114051 _48296)). Qed.
Lemma lem4114053 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4114054 (_48296 : int) : (term476 _48296) = term97.
Proof. exact (TRANS (@lem4114052 _48296) (@lem4114053 _48296)). Qed.
Lemma lem4114055 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4114056 (_48296 : int) : (term493 _48296) = term139.
Proof. exact (MK_COMB (@lem4114055) (@lem4114054 _48296)). Qed.
Lemma lem4114057 : term241 = term241.
Proof. exact (eq_refl term241). Qed.
Lemma lem4114058 (_48296 : int) : (term568 _48296) = term569.
Proof. exact (MK_COMB (@lem4114056 _48296) (@lem4114057)). Qed.
Lemma lem4114059 (_48296 : int) : (term567 _48296) = term569.
Proof. exact (TRANS (@lem4113948 _48296) (@lem4114058 _48296)). Qed.
Lemma lem4114060 : term569 = term241.
Proof. exact (@lem1982721 term241). Qed.
Lemma lem4114061 (_48296 : int) : (term567 _48296) = term241.
Proof. exact (TRANS (@lem4114059 _48296) (@lem4114060)). Qed.
Lemma lem4114062 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4114063 (_48296 : int) : (term570 _48296) = term571.
Proof. exact (MK_COMB (@lem4114062) (@lem4114061 _48296)). Qed.
Lemma lem4114064 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4114065 (_48296 : int) : (term566 _48296) = term572.
Proof. exact (MK_COMB (@lem4114063 _48296) (@lem4114064)). Qed.
Lemma lem4114066 (_48296 : int) (h1 : term595 _48296) : term572.
Proof. exact (EQ_MP (@lem4114065 _48296) (@lem4113947 _48296 h1)). Qed.
Lemma lem4114068 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4114069 : term572 = term573.
Proof. exact (@lem4114068 term97 term241). Qed.
Lemma lem4114071 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4114072 : term241 = term244.
Proof. exact (@lem4114071 term218). Qed.
Lemma lem4114074 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114075 : term97 = term175.
Proof. exact (@lem4114074 (NUMERAL 0)). Qed.
Lemma lem4114076 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4114077 : term99 = term513.
Proof. exact (MK_COMB (@lem4114076) (@lem4114075)). Qed.
Lemma lem4114078 : term573 = term574.
Proof. exact (MK_COMB (@lem4114077) (@lem4114072)). Qed.
Lemma lem4114079 : term575.
Proof. exact (@lem1980026 term97 term111 term241 term111). Qed.
Lemma lem4114081 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114082 : term206 = term207.
Proof. exact (@lem4114081 (NUMERAL 0) term20). Qed.
Lemma lem4114083 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114084 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114085 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114084 h1) (fun h1 : term207 = True => @lem4114083)). Qed.
Lemma lem4114086 : term207 = True.
Proof. exact (EQ_MP (@lem4114085) (@lem4114083)). Qed.
Lemma lem4114087 : term206 = True.
Proof. exact (TRANS (@lem4114082) (@lem4114086)). Qed.
Lemma lem4114088 : True = term206.
Proof. exact (SYM (@lem4114087)). Qed.
Lemma lem4114089 : term206.
Proof. exact (EQ_MP (@lem4114088) (@lem0)). Qed.
Lemma lem4114090 : term576.
Proof. exact (@lem4114079 (@lem4114089)). Qed.
Lemma lem4114092 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114093 : term206 = term207.
Proof. exact (@lem4114092 (NUMERAL 0) term20). Qed.
Lemma lem4114094 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114095 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114096 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114095 h1) (fun h1 : term207 = True => @lem4114094)). Qed.
Lemma lem4114097 : term207 = True.
Proof. exact (EQ_MP (@lem4114096) (@lem4114094)). Qed.
Lemma lem4114098 : term206 = True.
Proof. exact (TRANS (@lem4114093) (@lem4114097)). Qed.
Lemma lem4114099 : True = term206.
Proof. exact (SYM (@lem4114098)). Qed.
Lemma lem4114100 : term206.
Proof. exact (EQ_MP (@lem4114099) (@lem0)). Qed.
Lemma lem4114101 : term574 = term577.
Proof. exact (@lem4114090 (@lem4114100)). Qed.
Lemma lem4114103 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4114104 : term500 = term501.
Proof. exact (@lem4114103 term218 term20). Qed.
Lemma lem4114105 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4114106 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4114107 : term225 = term218.
Proof. exact (EQ_MP (@lem4114106) (@lem4114105)). Qed.
Lemma lem4114108 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114109 : term223 = term204.
Proof. exact (MK_COMB (@lem4114108) (@lem4114107)). Qed.
Lemma lem4114110 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4114111 : term501 = term241.
Proof. exact (MK_COMB (@lem4114110) (@lem4114109)). Qed.
Lemma lem4114112 : term500 = term241.
Proof. exact (TRANS (@lem4114104) (@lem4114111)). Qed.
Lemma lem4114114 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4114115 : term293 = term97.
Proof. exact (@lem4114114 term20). Qed.
Lemma lem4114116 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4114117 : term518 = term99.
Proof. exact (MK_COMB (@lem4114116) (@lem4114115)). Qed.
Lemma lem4114118 : term577 = term573.
Proof. exact (MK_COMB (@lem4114117) (@lem4114112)). Qed.
Lemma lem4114120 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4114121 : term573 = term578.
Proof. exact (@lem4114120 (NUMERAL 0) term218). Qed.
Lemma lem4114122 : term579 = term216.
Proof. exact (@lem912803). Qed.
Lemma lem4114123 (h1 : term579 = term216) : (term218 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term216 h1). Qed.
Lemma lem4114124 : (term579 = term216) = ((term218 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term579 = term216 => @lem4114123 h1) (fun h1 : (term218 = (NUMERAL 0)) = False => @lem4114122)). Qed.
Lemma lem4114125 : (term218 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4114124) (@lem4114122)). Qed.
Lemma lem4114126 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4114127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4114128 : term522 = (and True).
Proof. exact (MK_COMB (@lem4114127) (@lem4114126)). Qed.
Lemma lem4114129 : term578 = (True /\ False).
Proof. exact (MK_COMB (@lem4114128) (@lem4114125)). Qed.
Lemma lem4114131 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4114132 : term578 = False.
Proof. exact (TRANS (@lem4114129) (@lem4114131)). Qed.
Lemma lem4114133 : term573 = False.
Proof. exact (TRANS (@lem4114121) (@lem4114132)). Qed.
Lemma lem4114134 : term577 = False.
Proof. exact (TRANS (@lem4114118) (@lem4114133)). Qed.
Lemma lem4114135 : term574 = False.
Proof. exact (TRANS (@lem4114101) (@lem4114134)). Qed.
Lemma lem4114136 : term573 = False.
Proof. exact (TRANS (@lem4114078) (@lem4114135)). Qed.
Lemma lem4114137 : term572 = False.
Proof. exact (TRANS (@lem4114069) (@lem4114136)). Qed.
Lemma lem4114138 (_48296 : int) (h1 : term595 _48296) : False.
Proof. exact (EQ_MP (@lem4114137) (@lem4114066 _48296 h1)). Qed.
Lemma lem4114139 (_48296 : int) (h1 : term414 _48296) : False.
Proof. exact (or_elim (@lem4113558 _48296 h1) (fun h0 : term594 _48296 => @lem4113848 _48296 h0) (fun h0 : term595 _48296 => @lem4114138 _48296 h0)). Qed.
Lemma lem4114140 (_48296 : int) (h1 : term423 _48296) : False.
Proof. exact (or_elim (@lem4112977 _48296 h1) (fun h0 : term418 _48296 => @lem4113557 _48296 h0) (fun h0 : term414 _48296 => @lem4114139 _48296 h0)). Qed.
Lemma lem4114141 (_48296 : int) (h1 : term425 _48296) : False.
Proof. exact (or_elim (@lem4112688 _48296 h1) (fun h0 : term558 _48296 => @lem4112976 _48296 h0) (fun h0 : term423 _48296 => @lem4114140 _48296 h0)). Qed.
Lemma lem4114142 (_48296 : int) (h1 : term407 _48296) : term407 _48296.
Proof. exact (h1). Qed.
Lemma lem4114143 (_48296 : int) (h1 : term596 _48296) : term596 _48296.
Proof. exact (h1). Qed.
Lemma lem4114144 (_48296 : int) (h1 : term596 _48296) : term392 _48296.
Proof. exact (proj2 (@lem4114143 _48296 h1)). Qed.
Lemma lem4114146 (_48296 : int) (h1 : term596 _48296) : (term270 _48296) = term97.
Proof. exact (proj2 (@lem4114144 _48296 h1)). Qed.
Lemma lem4114147 (_48296 : int) (h1 : term596 _48296) : term248 _48296.
Proof. exact (proj1 (@lem4114144 _48296 h1)). Qed.
Lemma lem4114149 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4114150 : term451 = term206.
Proof. exact (@lem4114149 term97 term111). Qed.
Lemma lem4114152 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114153 : term111 = term200.
Proof. exact (@lem4114152 term20). Qed.
Lemma lem4114155 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114156 : term97 = term175.
Proof. exact (@lem4114155 (NUMERAL 0)). Qed.
Lemma lem4114157 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4114158 : term452 = term453.
Proof. exact (MK_COMB (@lem4114157) (@lem4114156)). Qed.
Lemma lem4114159 : term206 = term454.
Proof. exact (MK_COMB (@lem4114158) (@lem4114153)). Qed.
Lemma lem4114160 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4114162 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114163 : term206 = term207.
Proof. exact (@lem4114162 (NUMERAL 0) term20). Qed.
Lemma lem4114164 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114165 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114166 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114165 h1) (fun h1 : term207 = True => @lem4114164)). Qed.
Lemma lem4114167 : term207 = True.
Proof. exact (EQ_MP (@lem4114166) (@lem4114164)). Qed.
Lemma lem4114168 : term206 = True.
Proof. exact (TRANS (@lem4114163) (@lem4114167)). Qed.
Lemma lem4114169 : True = term206.
Proof. exact (SYM (@lem4114168)). Qed.
Lemma lem4114170 : term206.
Proof. exact (EQ_MP (@lem4114169) (@lem0)). Qed.
Lemma lem4114171 : term456.
Proof. exact (@lem4114160 (@lem4114170)). Qed.
Lemma lem4114173 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114174 : term206 = term207.
Proof. exact (@lem4114173 (NUMERAL 0) term20). Qed.
Lemma lem4114175 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114176 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114177 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114176 h1) (fun h1 : term207 = True => @lem4114175)). Qed.
Lemma lem4114178 : term207 = True.
Proof. exact (EQ_MP (@lem4114177) (@lem4114175)). Qed.
Lemma lem4114179 : term206 = True.
Proof. exact (TRANS (@lem4114174) (@lem4114178)). Qed.
Lemma lem4114180 : True = term206.
Proof. exact (SYM (@lem4114179)). Qed.
Lemma lem4114181 : term206.
Proof. exact (EQ_MP (@lem4114180) (@lem0)). Qed.
Lemma lem4114182 : term454 = term457.
Proof. exact (@lem4114171 (@lem4114181)). Qed.
Lemma lem4114184 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4114185 : term187 = term188.
Proof. exact (@lem4114184 term20 term20). Qed.
Lemma lem4114186 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114187 : term190 = term20.
Proof. exact (EQ_MP (@lem4114186) (@lem940073)). Qed.
Lemma lem4114188 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114189 : term188 = term111.
Proof. exact (MK_COMB (@lem4114188) (@lem4114187)). Qed.
Lemma lem4114190 : term187 = term111.
Proof. exact (TRANS (@lem4114185) (@lem4114189)). Qed.
Lemma lem4114192 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4114193 : term293 = term97.
Proof. exact (@lem4114192 term20). Qed.
Lemma lem4114194 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4114195 : term458 = term452.
Proof. exact (MK_COMB (@lem4114194) (@lem4114193)). Qed.
Lemma lem4114196 : term457 = term206.
Proof. exact (MK_COMB (@lem4114195) (@lem4114190)). Qed.
Lemma lem4114198 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114199 : term206 = term207.
Proof. exact (@lem4114198 (NUMERAL 0) term20). Qed.
Lemma lem4114200 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114201 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114202 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114201 h1) (fun h1 : term207 = True => @lem4114200)). Qed.
Lemma lem4114203 : term207 = True.
Proof. exact (EQ_MP (@lem4114202) (@lem4114200)). Qed.
Lemma lem4114204 : term206 = True.
Proof. exact (TRANS (@lem4114199) (@lem4114203)). Qed.
Lemma lem4114205 : term457 = True.
Proof. exact (TRANS (@lem4114196) (@lem4114204)). Qed.
Lemma lem4114206 : term454 = True.
Proof. exact (TRANS (@lem4114182) (@lem4114205)). Qed.
Lemma lem4114207 : term206 = True.
Proof. exact (TRANS (@lem4114159) (@lem4114206)). Qed.
Lemma lem4114208 : term451 = True.
Proof. exact (TRANS (@lem4114150) (@lem4114207)). Qed.
Lemma lem4114209 : True = term451.
Proof. exact (SYM (@lem4114208)). Qed.
Lemma lem4114210 : term451.
Proof. exact (EQ_MP (@lem4114209) (@lem0)). Qed.
Lemma lem4114211 (_48296 : int) (h1 : term596 _48296) : term459 _48296.
Proof. exact (conj (@lem4114210) (@lem4114147 _48296 h1)). Qed.
Lemma lem4114213 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4114214 (_48296 : int) : term461 _48296.
Proof. exact (@lem4114213 term111 (term245 _48296)). Qed.
Lemma lem4114215 (_48296 : int) (h1 : term596 _48296) : term462 _48296.
Proof. exact (@lem4114214 _48296 (@lem4114211 _48296 h1)). Qed.
Lemma lem4114216 (_48296 : int) : (term463 _48296) = (term245 _48296).
Proof. exact (@lem1982733 (term245 _48296)). Qed.
Lemma lem4114217 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4114218 (_48296 : int) : (term464 _48296) = (term247 _48296).
Proof. exact (MK_COMB (@lem4114217) (@lem4114216 _48296)). Qed.
Lemma lem4114219 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4114220 (_48296 : int) : (term462 _48296) = (term248 _48296).
Proof. exact (MK_COMB (@lem4114218 _48296) (@lem4114219)). Qed.
Lemma lem4114221 (_48296 : int) (h1 : term596 _48296) : term248 _48296.
Proof. exact (EQ_MP (@lem4114220 _48296) (@lem4114215 _48296 h1)). Qed.
Lemma lem4114223 (y : real) : term559 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem4114224 (_48296 : int) : term597 _48296.
Proof. exact (@lem4114223 (term270 _48296)). Qed.
Lemma lem4114225 (_48296 : int) (h1 : term596 _48296) : term598 _48296.
Proof. exact (@lem4114224 _48296 (@lem4114146 _48296 h1)). Qed.
Lemma lem4114226 (_48296 : int) (h1 : term596 _48296) : term599 _48296.
Proof. exact (@lem4114225 _48296 h1 term178). Qed.
Lemma lem4114227 (_48296 : int) : (term599 _48296) = ((term600 _48296) = term97).
Proof. exact (eq_refl (term599 _48296)). Qed.
Lemma lem4114228 (_48296 : int) (h1 : term596 _48296) : (term600 _48296) = term97.
Proof. exact (EQ_MP (@lem4114227 _48296) (@lem4114226 _48296 h1)). Qed.
Lemma lem4114229 (_48296 : int) : (term600 _48296) = (term601 _48296).
Proof. exact (@lem1982781 (real_of_int _48296) term178 term178). Qed.
Lemma lem4114231 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4114232 : term178 = term179.
Proof. exact (@lem4114231 term20). Qed.
Lemma lem4114234 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4114235 : term178 = term179.
Proof. exact (@lem4114234 term20). Qed.
Lemma lem4114236 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4114237 : term180 = term181.
Proof. exact (MK_COMB (@lem4114236) (@lem4114235)). Qed.
Lemma lem4114238 : term602 = term603.
Proof. exact (MK_COMB (@lem4114237) (@lem4114232)). Qed.
Lemma lem4114239 : term603 = term604.
Proof. exact (@lem1981613 term178 term178 term111 term111). Qed.
Lemma lem4114241 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4114242 : term187 = term188.
Proof. exact (@lem4114241 term20 term20). Qed.
Lemma lem4114243 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114244 : term190 = term20.
Proof. exact (EQ_MP (@lem4114243) (@lem940073)). Qed.
Lemma lem4114245 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114246 : term188 = term111.
Proof. exact (MK_COMB (@lem4114245) (@lem4114244)). Qed.
Lemma lem4114247 : term187 = term111.
Proof. exact (TRANS (@lem4114242) (@lem4114246)). Qed.
Lemma lem4114249 (m : nat) (n : nat) : (term605 m n) = (term186 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem4114250 : term602 = term188.
Proof. exact (@lem4114249 term20 term20). Qed.
Lemma lem4114251 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114252 : term190 = term20.
Proof. exact (EQ_MP (@lem4114251) (@lem940073)). Qed.
Lemma lem4114253 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114254 : term188 = term111.
Proof. exact (MK_COMB (@lem4114253) (@lem4114252)). Qed.
Lemma lem4114255 : term602 = term111.
Proof. exact (TRANS (@lem4114250) (@lem4114254)). Qed.
Lemma lem4114256 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4114257 : term606 = term607.
Proof. exact (MK_COMB (@lem4114256) (@lem4114255)). Qed.
Lemma lem4114258 : term604 = term200.
Proof. exact (MK_COMB (@lem4114257) (@lem4114247)). Qed.
Lemma lem4114259 : term603 = term200.
Proof. exact (TRANS (@lem4114239) (@lem4114258)). Qed.
Lemma lem4114260 : term602 = term200.
Proof. exact (TRANS (@lem4114238) (@lem4114259)). Qed.
Lemma lem4114262 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4114263 : term200 = term111.
Proof. exact (@lem4114262 term111). Qed.
Lemma lem4114264 : term602 = term111.
Proof. exact (TRANS (@lem4114260) (@lem4114263)). Qed.
Lemma lem4114267 (_48296 : int) : (term260 _48296) = (term260 _48296).
Proof. exact (eq_refl (term260 _48296)). Qed.
Lemma lem4114268 (_48296 : int) : (term601 _48296) = (term309 _48296).
Proof. exact (MK_COMB (@lem4114267 _48296) (@lem4114264)). Qed.
Lemma lem4114269 (_48296 : int) : (term600 _48296) = (term309 _48296).
Proof. exact (TRANS (@lem4114229 _48296) (@lem4114268 _48296)). Qed.
Lemma lem4114270 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem4114271 (_48296 : int) : (term608 _48296) = (term609 _48296).
Proof. exact (MK_COMB (@lem4114270) (@lem4114269 _48296)). Qed.
Lemma lem4114272 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4114273 (_48296 : int) : ((term600 _48296) = term97) = ((term309 _48296) = term97).
Proof. exact (MK_COMB (@lem4114271 _48296) (@lem4114272)). Qed.
Lemma lem4114274 (_48296 : int) (h1 : term596 _48296) : (term309 _48296) = term97.
Proof. exact (EQ_MP (@lem4114273 _48296) (@lem4114228 _48296 h1)). Qed.
Lemma lem4114275 (_48296 : int) (h1 : term596 _48296) : term610 _48296.
Proof. exact (conj (@lem4114274 _48296 h1) (@lem4114221 _48296 h1)). Qed.
Lemma lem4114277 (x : real) (y : real) : term564 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem4114278 (_48296 : int) : term611 _48296.
Proof. exact (@lem4114277 (term309 _48296) (term245 _48296)). Qed.
Lemma lem4114279 (_48296 : int) (h1 : term596 _48296) : term473 _48296.
Proof. exact (@lem4114278 _48296 (@lem4114275 _48296 h1)). Qed.
Lemma lem4114280 (_48296 : int) : (term474 _48296) = (term475 _48296).
Proof. exact (@lem1982753 (term281 _48296) (real_of_int _48296) term111 term241). Qed.
Lemma lem4114281 (_48296 : int) : (term476 _48296) = (term477 _48296).
Proof. exact (@lem1982713 term178 (real_of_int _48296)). Qed.
Lemma lem4114283 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114284 : term111 = term200.
Proof. exact (@lem4114283 term20). Qed.
Lemma lem4114286 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4114287 : term178 = term179.
Proof. exact (@lem4114286 term20). Qed.
Lemma lem4114288 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4114289 : term478 = term479.
Proof. exact (MK_COMB (@lem4114288) (@lem4114287)). Qed.
Lemma lem4114290 : term480 = term481.
Proof. exact (MK_COMB (@lem4114289) (@lem4114284)). Qed.
Lemma lem4114291 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4114293 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114294 : term206 = term207.
Proof. exact (@lem4114293 (NUMERAL 0) term20). Qed.
Lemma lem4114295 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114296 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114297 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114296 h1) (fun h1 : term207 = True => @lem4114295)). Qed.
Lemma lem4114298 : term207 = True.
Proof. exact (EQ_MP (@lem4114297) (@lem4114295)). Qed.
Lemma lem4114299 : term206 = True.
Proof. exact (TRANS (@lem4114294) (@lem4114298)). Qed.
Lemma lem4114300 : True = term206.
Proof. exact (SYM (@lem4114299)). Qed.
Lemma lem4114301 : term206.
Proof. exact (EQ_MP (@lem4114300) (@lem0)). Qed.
Lemma lem4114302 : term483.
Proof. exact (@lem4114291 (@lem4114301)). Qed.
Lemma lem4114304 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114305 : term206 = term207.
Proof. exact (@lem4114304 (NUMERAL 0) term20). Qed.
Lemma lem4114306 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114307 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114308 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114307 h1) (fun h1 : term207 = True => @lem4114306)). Qed.
Lemma lem4114309 : term207 = True.
Proof. exact (EQ_MP (@lem4114308) (@lem4114306)). Qed.
Lemma lem4114310 : term206 = True.
Proof. exact (TRANS (@lem4114305) (@lem4114309)). Qed.
Lemma lem4114311 : True = term206.
Proof. exact (SYM (@lem4114310)). Qed.
Lemma lem4114312 : term206.
Proof. exact (EQ_MP (@lem4114311) (@lem0)). Qed.
Lemma lem4114313 : term484.
Proof. exact (@lem4114302 (@lem4114312)). Qed.
Lemma lem4114315 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114316 : term206 = term207.
Proof. exact (@lem4114315 (NUMERAL 0) term20). Qed.
Lemma lem4114317 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114318 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114319 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114318 h1) (fun h1 : term207 = True => @lem4114317)). Qed.
Lemma lem4114320 : term207 = True.
Proof. exact (EQ_MP (@lem4114319) (@lem4114317)). Qed.
Lemma lem4114321 : term206 = True.
Proof. exact (TRANS (@lem4114316) (@lem4114320)). Qed.
Lemma lem4114322 : True = term206.
Proof. exact (SYM (@lem4114321)). Qed.
Lemma lem4114323 : term206.
Proof. exact (EQ_MP (@lem4114322) (@lem0)). Qed.
Lemma lem4114324 : term485.
Proof. exact (@lem4114313 (@lem4114323)). Qed.
Lemma lem4114326 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4114327 : term187 = term188.
Proof. exact (@lem4114326 term20 term20). Qed.
Lemma lem4114328 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114329 : term190 = term20.
Proof. exact (EQ_MP (@lem4114328) (@lem940073)). Qed.
Lemma lem4114330 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114331 : term188 = term111.
Proof. exact (MK_COMB (@lem4114330) (@lem4114329)). Qed.
Lemma lem4114332 : term187 = term111.
Proof. exact (TRANS (@lem4114327) (@lem4114331)). Qed.
Lemma lem4114334 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4114335 : term254 = term257.
Proof. exact (@lem4114334 term20 term20). Qed.
Lemma lem4114336 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114337 : term190 = term20.
Proof. exact (EQ_MP (@lem4114336) (@lem940073)). Qed.
Lemma lem4114338 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114339 : term188 = term111.
Proof. exact (MK_COMB (@lem4114338) (@lem4114337)). Qed.
Lemma lem4114340 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4114341 : term257 = term178.
Proof. exact (MK_COMB (@lem4114340) (@lem4114339)). Qed.
Lemma lem4114342 : term254 = term178.
Proof. exact (TRANS (@lem4114335) (@lem4114341)). Qed.
Lemma lem4114343 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4114344 : term486 = term478.
Proof. exact (MK_COMB (@lem4114343) (@lem4114342)). Qed.
Lemma lem4114345 : term487 = term480.
Proof. exact (MK_COMB (@lem4114344) (@lem4114332)). Qed.
Lemma lem4114347 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4114348 : term480 = term97.
Proof. exact (@lem4114347 term20). Qed.
Lemma lem4114349 : term487 = term97.
Proof. exact (TRANS (@lem4114345) (@lem4114348)). Qed.
Lemma lem4114350 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4114351 : term489 = term291.
Proof. exact (MK_COMB (@lem4114350) (@lem4114349)). Qed.
Lemma lem4114352 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4114353 : term490 = term293.
Proof. exact (MK_COMB (@lem4114351) (@lem4114352)). Qed.
Lemma lem4114355 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4114356 : term293 = term97.
Proof. exact (@lem4114355 term20). Qed.
Lemma lem4114357 : term490 = term97.
Proof. exact (TRANS (@lem4114353) (@lem4114356)). Qed.
Lemma lem4114359 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4114360 : term187 = term188.
Proof. exact (@lem4114359 term20 term20). Qed.
Lemma lem4114361 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114362 : term190 = term20.
Proof. exact (EQ_MP (@lem4114361) (@lem940073)). Qed.
Lemma lem4114363 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114364 : term188 = term111.
Proof. exact (MK_COMB (@lem4114363) (@lem4114362)). Qed.
Lemma lem4114365 : term187 = term111.
Proof. exact (TRANS (@lem4114360) (@lem4114364)). Qed.
Lemma lem4114366 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4114367 : term295 = term293.
Proof. exact (MK_COMB (@lem4114366) (@lem4114365)). Qed.
Lemma lem4114369 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4114370 : term293 = term97.
Proof. exact (@lem4114369 term20). Qed.
Lemma lem4114371 : term295 = term97.
Proof. exact (TRANS (@lem4114367) (@lem4114370)). Qed.
Lemma lem4114372 : term97 = term295.
Proof. exact (SYM (@lem4114371)). Qed.
Lemma lem4114373 : term490 = term295.
Proof. exact (TRANS (@lem4114357) (@lem4114372)). Qed.
Lemma lem4114374 : term481 = term175.
Proof. exact (@lem4114324 (@lem4114373)). Qed.
Lemma lem4114375 : term480 = term175.
Proof. exact (TRANS (@lem4114290) (@lem4114374)). Qed.
Lemma lem4114377 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4114378 : term175 = term97.
Proof. exact (@lem4114377 term97). Qed.
Lemma lem4114379 : term480 = term97.
Proof. exact (TRANS (@lem4114375) (@lem4114378)). Qed.
Lemma lem4114380 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4114381 : term491 = term291.
Proof. exact (MK_COMB (@lem4114380) (@lem4114379)). Qed.
Lemma lem4114382 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4114383 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4114381) (@lem4114382 _48296)). Qed.
Lemma lem4114384 (_48296 : int) : (term476 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4114281 _48296) (@lem4114383 _48296)). Qed.
Lemma lem4114385 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4114386 (_48296 : int) : (term476 _48296) = term97.
Proof. exact (TRANS (@lem4114384 _48296) (@lem4114385 _48296)). Qed.
Lemma lem4114387 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4114388 (_48296 : int) : (term493 _48296) = term139.
Proof. exact (MK_COMB (@lem4114387) (@lem4114386 _48296)). Qed.
Lemma lem4114390 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4114391 : term241 = term244.
Proof. exact (@lem4114390 term218). Qed.
Lemma lem4114393 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114394 : term111 = term200.
Proof. exact (@lem4114393 term20). Qed.
Lemma lem4114395 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4114396 : term113 = term201.
Proof. exact (MK_COMB (@lem4114395) (@lem4114394)). Qed.
Lemma lem4114397 : term494 = term495.
Proof. exact (MK_COMB (@lem4114396) (@lem4114391)). Qed.
Lemma lem4114398 : term496.
Proof. exact (@lem1981473 term111 term111 term241 term111 term178 term111). Qed.
Lemma lem4114400 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114401 : term206 = term207.
Proof. exact (@lem4114400 (NUMERAL 0) term20). Qed.
Lemma lem4114402 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114403 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114404 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114403 h1) (fun h1 : term207 = True => @lem4114402)). Qed.
Lemma lem4114405 : term207 = True.
Proof. exact (EQ_MP (@lem4114404) (@lem4114402)). Qed.
Lemma lem4114406 : term206 = True.
Proof. exact (TRANS (@lem4114401) (@lem4114405)). Qed.
Lemma lem4114407 : True = term206.
Proof. exact (SYM (@lem4114406)). Qed.
Lemma lem4114408 : term206.
Proof. exact (EQ_MP (@lem4114407) (@lem0)). Qed.
Lemma lem4114409 : term497.
Proof. exact (@lem4114398 (@lem4114408)). Qed.
Lemma lem4114411 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114412 : term206 = term207.
Proof. exact (@lem4114411 (NUMERAL 0) term20). Qed.
Lemma lem4114413 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114414 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114415 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114414 h1) (fun h1 : term207 = True => @lem4114413)). Qed.
Lemma lem4114416 : term207 = True.
Proof. exact (EQ_MP (@lem4114415) (@lem4114413)). Qed.
Lemma lem4114417 : term206 = True.
Proof. exact (TRANS (@lem4114412) (@lem4114416)). Qed.
Lemma lem4114418 : True = term206.
Proof. exact (SYM (@lem4114417)). Qed.
Lemma lem4114419 : term206.
Proof. exact (EQ_MP (@lem4114418) (@lem0)). Qed.
Lemma lem4114420 : term498.
Proof. exact (@lem4114409 (@lem4114419)). Qed.
Lemma lem4114422 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114423 : term206 = term207.
Proof. exact (@lem4114422 (NUMERAL 0) term20). Qed.
Lemma lem4114424 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114425 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114426 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114425 h1) (fun h1 : term207 = True => @lem4114424)). Qed.
Lemma lem4114427 : term207 = True.
Proof. exact (EQ_MP (@lem4114426) (@lem4114424)). Qed.
Lemma lem4114428 : term206 = True.
Proof. exact (TRANS (@lem4114423) (@lem4114427)). Qed.
Lemma lem4114429 : True = term206.
Proof. exact (SYM (@lem4114428)). Qed.
Lemma lem4114430 : term206.
Proof. exact (EQ_MP (@lem4114429) (@lem0)). Qed.
Lemma lem4114431 : term499.
Proof. exact (@lem4114420 (@lem4114430)). Qed.
Lemma lem4114433 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4114434 : term500 = term501.
Proof. exact (@lem4114433 term218 term20). Qed.
Lemma lem4114435 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4114436 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4114437 : term225 = term218.
Proof. exact (EQ_MP (@lem4114436) (@lem4114435)). Qed.
Lemma lem4114438 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114439 : term223 = term204.
Proof. exact (MK_COMB (@lem4114438) (@lem4114437)). Qed.
Lemma lem4114440 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4114441 : term501 = term241.
Proof. exact (MK_COMB (@lem4114440) (@lem4114439)). Qed.
Lemma lem4114442 : term500 = term241.
Proof. exact (TRANS (@lem4114434) (@lem4114441)). Qed.
Lemma lem4114444 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4114445 : term187 = term188.
Proof. exact (@lem4114444 term20 term20). Qed.
Lemma lem4114446 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114447 : term190 = term20.
Proof. exact (EQ_MP (@lem4114446) (@lem940073)). Qed.
Lemma lem4114448 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114449 : term188 = term111.
Proof. exact (MK_COMB (@lem4114448) (@lem4114447)). Qed.
Lemma lem4114450 : term187 = term111.
Proof. exact (TRANS (@lem4114445) (@lem4114449)). Qed.
Lemma lem4114451 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4114452 : term212 = term113.
Proof. exact (MK_COMB (@lem4114451) (@lem4114450)). Qed.
Lemma lem4114453 : term502 = term494.
Proof. exact (MK_COMB (@lem4114452) (@lem4114442)). Qed.
Lemma lem4114456 : term503 = term178.
Proof. exact (@lem1367771 term20 term20). Qed.
Lemma lem4114457 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem4114458 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem4114459 : term217 = term218.
Proof. exact (EQ_MP (@lem4114458) (@lem4114457)). Qed.
Lemma lem4114460 : term218 = term217.
Proof. exact (SYM (@lem4114459)). Qed.
Lemma lem4114461 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114462 : term204 = term214.
Proof. exact (MK_COMB (@lem4114461) (@lem4114460)). Qed.
Lemma lem4114463 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4114464 : term241 = term504.
Proof. exact (MK_COMB (@lem4114463) (@lem4114462)). Qed.
Lemma lem4114465 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem4114466 : term494 = term503.
Proof. exact (MK_COMB (@lem4114465) (@lem4114464)). Qed.
Lemma lem4114467 : term494 = term178.
Proof. exact (TRANS (@lem4114466) (@lem4114456)). Qed.
Lemma lem4114468 : term502 = term178.
Proof. exact (TRANS (@lem4114453) (@lem4114467)). Qed.
Lemma lem4114469 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4114470 : term505 = term180.
Proof. exact (MK_COMB (@lem4114469) (@lem4114468)). Qed.
Lemma lem4114471 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4114472 : term506 = term254.
Proof. exact (MK_COMB (@lem4114470) (@lem4114471)). Qed.
Lemma lem4114474 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4114475 : term254 = term257.
Proof. exact (@lem4114474 term20 term20). Qed.
Lemma lem4114476 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114477 : term190 = term20.
Proof. exact (EQ_MP (@lem4114476) (@lem940073)). Qed.
Lemma lem4114478 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114479 : term188 = term111.
Proof. exact (MK_COMB (@lem4114478) (@lem4114477)). Qed.
Lemma lem4114480 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4114481 : term257 = term178.
Proof. exact (MK_COMB (@lem4114480) (@lem4114479)). Qed.
Lemma lem4114482 : term254 = term178.
Proof. exact (TRANS (@lem4114475) (@lem4114481)). Qed.
Lemma lem4114483 : term506 = term178.
Proof. exact (TRANS (@lem4114472) (@lem4114482)). Qed.
Lemma lem4114485 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4114486 : term187 = term188.
Proof. exact (@lem4114485 term20 term20). Qed.
Lemma lem4114487 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114488 : term190 = term20.
Proof. exact (EQ_MP (@lem4114487) (@lem940073)). Qed.
Lemma lem4114489 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114490 : term188 = term111.
Proof. exact (MK_COMB (@lem4114489) (@lem4114488)). Qed.
Lemma lem4114491 : term187 = term111.
Proof. exact (TRANS (@lem4114486) (@lem4114490)). Qed.
Lemma lem4114492 : term180 = term180.
Proof. exact (eq_refl term180). Qed.
Lemma lem4114493 : term507 = term254.
Proof. exact (MK_COMB (@lem4114492) (@lem4114491)). Qed.
Lemma lem4114495 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4114496 : term254 = term257.
Proof. exact (@lem4114495 term20 term20). Qed.
Lemma lem4114497 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114498 : term190 = term20.
Proof. exact (EQ_MP (@lem4114497) (@lem940073)). Qed.
Lemma lem4114499 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114500 : term188 = term111.
Proof. exact (MK_COMB (@lem4114499) (@lem4114498)). Qed.
Lemma lem4114501 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4114502 : term257 = term178.
Proof. exact (MK_COMB (@lem4114501) (@lem4114500)). Qed.
Lemma lem4114503 : term254 = term178.
Proof. exact (TRANS (@lem4114496) (@lem4114502)). Qed.
Lemma lem4114504 : term507 = term178.
Proof. exact (TRANS (@lem4114493) (@lem4114503)). Qed.
Lemma lem4114505 : term178 = term507.
Proof. exact (SYM (@lem4114504)). Qed.
Lemma lem4114506 : term506 = term507.
Proof. exact (TRANS (@lem4114483) (@lem4114505)). Qed.
Lemma lem4114507 : term495 = term179.
Proof. exact (@lem4114431 (@lem4114506)). Qed.
Lemma lem4114508 : term494 = term179.
Proof. exact (TRANS (@lem4114397) (@lem4114507)). Qed.
Lemma lem4114510 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4114511 : term179 = term178.
Proof. exact (@lem4114510 term178). Qed.
Lemma lem4114512 : term494 = term178.
Proof. exact (TRANS (@lem4114508) (@lem4114511)). Qed.
Lemma lem4114513 (_48296 : int) : (term475 _48296) = term508.
Proof. exact (MK_COMB (@lem4114388 _48296) (@lem4114512)). Qed.
Lemma lem4114514 (_48296 : int) : (term474 _48296) = term508.
Proof. exact (TRANS (@lem4114280 _48296) (@lem4114513 _48296)). Qed.
Lemma lem4114515 : term508 = term178.
Proof. exact (@lem1982721 term178). Qed.
Lemma lem4114516 (_48296 : int) : (term474 _48296) = term178.
Proof. exact (TRANS (@lem4114514 _48296) (@lem4114515)). Qed.
Lemma lem4114517 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4114518 (_48296 : int) : (term509 _48296) = term510.
Proof. exact (MK_COMB (@lem4114517) (@lem4114516 _48296)). Qed.
Lemma lem4114519 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4114520 (_48296 : int) : (term473 _48296) = term511.
Proof. exact (MK_COMB (@lem4114518 _48296) (@lem4114519)). Qed.
Lemma lem4114521 (_48296 : int) (h1 : term596 _48296) : term511.
Proof. exact (EQ_MP (@lem4114520 _48296) (@lem4114279 _48296 h1)). Qed.
Lemma lem4114523 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4114524 : term511 = term512.
Proof. exact (@lem4114523 term97 term178). Qed.
Lemma lem4114526 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4114527 : term178 = term179.
Proof. exact (@lem4114526 term20). Qed.
Lemma lem4114529 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114530 : term97 = term175.
Proof. exact (@lem4114529 (NUMERAL 0)). Qed.
Lemma lem4114531 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4114532 : term99 = term513.
Proof. exact (MK_COMB (@lem4114531) (@lem4114530)). Qed.
Lemma lem4114533 : term512 = term514.
Proof. exact (MK_COMB (@lem4114532) (@lem4114527)). Qed.
Lemma lem4114534 : term515.
Proof. exact (@lem1980026 term97 term111 term178 term111). Qed.
Lemma lem4114536 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114537 : term206 = term207.
Proof. exact (@lem4114536 (NUMERAL 0) term20). Qed.
Lemma lem4114538 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114539 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114540 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114539 h1) (fun h1 : term207 = True => @lem4114538)). Qed.
Lemma lem4114541 : term207 = True.
Proof. exact (EQ_MP (@lem4114540) (@lem4114538)). Qed.
Lemma lem4114542 : term206 = True.
Proof. exact (TRANS (@lem4114537) (@lem4114541)). Qed.
Lemma lem4114543 : True = term206.
Proof. exact (SYM (@lem4114542)). Qed.
Lemma lem4114544 : term206.
Proof. exact (EQ_MP (@lem4114543) (@lem0)). Qed.
Lemma lem4114545 : term516.
Proof. exact (@lem4114534 (@lem4114544)). Qed.
Lemma lem4114547 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114548 : term206 = term207.
Proof. exact (@lem4114547 (NUMERAL 0) term20). Qed.
Lemma lem4114549 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114550 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114551 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114550 h1) (fun h1 : term207 = True => @lem4114549)). Qed.
Lemma lem4114552 : term207 = True.
Proof. exact (EQ_MP (@lem4114551) (@lem4114549)). Qed.
Lemma lem4114553 : term206 = True.
Proof. exact (TRANS (@lem4114548) (@lem4114552)). Qed.
Lemma lem4114554 : True = term206.
Proof. exact (SYM (@lem4114553)). Qed.
Lemma lem4114555 : term206.
Proof. exact (EQ_MP (@lem4114554) (@lem0)). Qed.
Lemma lem4114556 : term514 = term517.
Proof. exact (@lem4114545 (@lem4114555)). Qed.
Lemma lem4114558 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4114559 : term254 = term257.
Proof. exact (@lem4114558 term20 term20). Qed.
Lemma lem4114560 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114561 : term190 = term20.
Proof. exact (EQ_MP (@lem4114560) (@lem940073)). Qed.
Lemma lem4114562 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114563 : term188 = term111.
Proof. exact (MK_COMB (@lem4114562) (@lem4114561)). Qed.
Lemma lem4114564 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4114565 : term257 = term178.
Proof. exact (MK_COMB (@lem4114564) (@lem4114563)). Qed.
Lemma lem4114566 : term254 = term178.
Proof. exact (TRANS (@lem4114559) (@lem4114565)). Qed.
Lemma lem4114568 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4114569 : term293 = term97.
Proof. exact (@lem4114568 term20). Qed.
Lemma lem4114570 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4114571 : term518 = term99.
Proof. exact (MK_COMB (@lem4114570) (@lem4114569)). Qed.
Lemma lem4114572 : term517 = term512.
Proof. exact (MK_COMB (@lem4114571) (@lem4114566)). Qed.
Lemma lem4114574 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4114575 : term512 = term521.
Proof. exact (@lem4114574 (NUMERAL 0) term20). Qed.
Lemma lem4114576 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114577 (h1 : term208 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4114578 : (term208 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114577 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem4114576)). Qed.
Lemma lem4114579 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4114578) (@lem4114576)). Qed.
Lemma lem4114580 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4114581 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4114582 : term522 = (and True).
Proof. exact (MK_COMB (@lem4114581) (@lem4114580)). Qed.
Lemma lem4114583 : term521 = (True /\ False).
Proof. exact (MK_COMB (@lem4114582) (@lem4114579)). Qed.
Lemma lem4114585 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4114586 : term521 = False.
Proof. exact (TRANS (@lem4114583) (@lem4114585)). Qed.
Lemma lem4114587 : term512 = False.
Proof. exact (TRANS (@lem4114575) (@lem4114586)). Qed.
Lemma lem4114588 : term517 = False.
Proof. exact (TRANS (@lem4114572) (@lem4114587)). Qed.
Lemma lem4114589 : term514 = False.
Proof. exact (TRANS (@lem4114556) (@lem4114588)). Qed.
Lemma lem4114590 : term512 = False.
Proof. exact (TRANS (@lem4114533) (@lem4114589)). Qed.
Lemma lem4114591 : term511 = False.
Proof. exact (TRANS (@lem4114524) (@lem4114590)). Qed.
Lemma lem4114592 (_48296 : int) (h1 : term596 _48296) : False.
Proof. exact (EQ_MP (@lem4114591) (@lem4114521 _48296 h1)). Qed.
Lemma lem4114593 (_48296 : int) (h1 : term405 _48296) : term405 _48296.
Proof. exact (h1). Qed.
Lemma lem4114594 (_48296 : int) (h1 : term400 _48296) : term400 _48296.
Proof. exact (h1). Qed.
Lemma lem4114595 (_48296 : int) (h1 : term612 _48296) : term612 _48296.
Proof. exact (h1). Qed.
Lemma lem4114596 (_48296 : int) (h1 : term612 _48296) : term401 _48296.
Proof. exact (proj2 (@lem4114595 _48296 h1)). Qed.
Lemma lem4114598 (_48296 : int) (h1 : term612 _48296) : (term270 _48296) = term97.
Proof. exact (proj2 (@lem4114596 _48296 h1)). Qed.
Lemma lem4114599 (_48296 : int) (h1 : term612 _48296) : term347 _48296.
Proof. exact (proj1 (@lem4114596 _48296 h1)). Qed.
Lemma lem4114600 (_48296 : int) (h1 : term612 _48296) : term299 _48296.
Proof. exact (proj2 (@lem4114599 _48296 h1)). Qed.
Lemma lem4114603 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4114604 : term451 = term206.
Proof. exact (@lem4114603 term97 term111). Qed.
Lemma lem4114606 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114607 : term111 = term200.
Proof. exact (@lem4114606 term20). Qed.
Lemma lem4114609 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114610 : term97 = term175.
Proof. exact (@lem4114609 (NUMERAL 0)). Qed.
Lemma lem4114611 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4114612 : term452 = term453.
Proof. exact (MK_COMB (@lem4114611) (@lem4114610)). Qed.
Lemma lem4114613 : term206 = term454.
Proof. exact (MK_COMB (@lem4114612) (@lem4114607)). Qed.
Lemma lem4114614 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4114616 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114617 : term206 = term207.
Proof. exact (@lem4114616 (NUMERAL 0) term20). Qed.
Lemma lem4114618 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114619 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114620 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114619 h1) (fun h1 : term207 = True => @lem4114618)). Qed.
Lemma lem4114621 : term207 = True.
Proof. exact (EQ_MP (@lem4114620) (@lem4114618)). Qed.
Lemma lem4114622 : term206 = True.
Proof. exact (TRANS (@lem4114617) (@lem4114621)). Qed.
Lemma lem4114623 : True = term206.
Proof. exact (SYM (@lem4114622)). Qed.
Lemma lem4114624 : term206.
Proof. exact (EQ_MP (@lem4114623) (@lem0)). Qed.
Lemma lem4114625 : term456.
Proof. exact (@lem4114614 (@lem4114624)). Qed.
Lemma lem4114627 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114628 : term206 = term207.
Proof. exact (@lem4114627 (NUMERAL 0) term20). Qed.
Lemma lem4114629 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114630 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114631 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114630 h1) (fun h1 : term207 = True => @lem4114629)). Qed.
Lemma lem4114632 : term207 = True.
Proof. exact (EQ_MP (@lem4114631) (@lem4114629)). Qed.
Lemma lem4114633 : term206 = True.
Proof. exact (TRANS (@lem4114628) (@lem4114632)). Qed.
Lemma lem4114634 : True = term206.
Proof. exact (SYM (@lem4114633)). Qed.
Lemma lem4114635 : term206.
Proof. exact (EQ_MP (@lem4114634) (@lem0)). Qed.
Lemma lem4114636 : term454 = term457.
Proof. exact (@lem4114625 (@lem4114635)). Qed.
Lemma lem4114638 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4114639 : term187 = term188.
Proof. exact (@lem4114638 term20 term20). Qed.
Lemma lem4114640 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114641 : term190 = term20.
Proof. exact (EQ_MP (@lem4114640) (@lem940073)). Qed.
Lemma lem4114642 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114643 : term188 = term111.
Proof. exact (MK_COMB (@lem4114642) (@lem4114641)). Qed.
Lemma lem4114644 : term187 = term111.
Proof. exact (TRANS (@lem4114639) (@lem4114643)). Qed.
Lemma lem4114646 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4114647 : term293 = term97.
Proof. exact (@lem4114646 term20). Qed.
Lemma lem4114648 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4114649 : term458 = term452.
Proof. exact (MK_COMB (@lem4114648) (@lem4114647)). Qed.
Lemma lem4114650 : term457 = term206.
Proof. exact (MK_COMB (@lem4114649) (@lem4114644)). Qed.
Lemma lem4114652 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114653 : term206 = term207.
Proof. exact (@lem4114652 (NUMERAL 0) term20). Qed.
Lemma lem4114654 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114655 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114656 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114655 h1) (fun h1 : term207 = True => @lem4114654)). Qed.
Lemma lem4114657 : term207 = True.
Proof. exact (EQ_MP (@lem4114656) (@lem4114654)). Qed.
Lemma lem4114658 : term206 = True.
Proof. exact (TRANS (@lem4114653) (@lem4114657)). Qed.
Lemma lem4114659 : term457 = True.
Proof. exact (TRANS (@lem4114650) (@lem4114658)). Qed.
Lemma lem4114660 : term454 = True.
Proof. exact (TRANS (@lem4114636) (@lem4114659)). Qed.
Lemma lem4114661 : term206 = True.
Proof. exact (TRANS (@lem4114613) (@lem4114660)). Qed.
Lemma lem4114662 : term451 = True.
Proof. exact (TRANS (@lem4114604) (@lem4114661)). Qed.
Lemma lem4114663 : True = term451.
Proof. exact (SYM (@lem4114662)). Qed.
Lemma lem4114664 : term451.
Proof. exact (EQ_MP (@lem4114663) (@lem0)). Qed.
Lemma lem4114665 (_48296 : int) (h1 : term612 _48296) : term546 _48296.
Proof. exact (conj (@lem4114664) (@lem4114600 _48296 h1)). Qed.
Lemma lem4114667 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4114668 (_48296 : int) : term547 _48296.
Proof. exact (@lem4114667 term111 (term281 _48296)). Qed.
Lemma lem4114669 (_48296 : int) (h1 : term612 _48296) : term548 _48296.
Proof. exact (@lem4114668 _48296 (@lem4114665 _48296 h1)). Qed.
Lemma lem4114670 (_48296 : int) : (term549 _48296) = (term281 _48296).
Proof. exact (@lem1982733 (term281 _48296)). Qed.
Lemma lem4114671 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4114672 (_48296 : int) : (term550 _48296) = (term298 _48296).
Proof. exact (MK_COMB (@lem4114671) (@lem4114670 _48296)). Qed.
Lemma lem4114673 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4114674 (_48296 : int) : (term548 _48296) = (term299 _48296).
Proof. exact (MK_COMB (@lem4114672 _48296) (@lem4114673)). Qed.
Lemma lem4114675 (_48296 : int) (h1 : term612 _48296) : term299 _48296.
Proof. exact (EQ_MP (@lem4114674 _48296) (@lem4114669 _48296 h1)). Qed.
Lemma lem4114677 (y : real) : term559 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem4114678 (_48296 : int) : term597 _48296.
Proof. exact (@lem4114677 (term270 _48296)). Qed.
Lemma lem4114679 (_48296 : int) (h1 : term612 _48296) : term598 _48296.
Proof. exact (@lem4114678 _48296 (@lem4114598 _48296 h1)). Qed.
Lemma lem4114680 (_48296 : int) (h1 : term612 _48296) : term613 _48296.
Proof. exact (@lem4114679 _48296 h1 term111). Qed.
Lemma lem4114681 (_48296 : int) : (term613 _48296) = ((term544 _48296) = term97).
Proof. exact (eq_refl (term613 _48296)). Qed.
Lemma lem4114682 (_48296 : int) (h1 : term612 _48296) : (term544 _48296) = term97.
Proof. exact (EQ_MP (@lem4114681 _48296) (@lem4114680 _48296 h1)). Qed.
Lemma lem4114683 (_48296 : int) : (term544 _48296) = (term270 _48296).
Proof. exact (@lem1982733 (term270 _48296)). Qed.
Lemma lem4114684 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem4114685 (_48296 : int) : (term614 _48296) = (term315 _48296).
Proof. exact (MK_COMB (@lem4114684) (@lem4114683 _48296)). Qed.
Lemma lem4114686 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4114687 (_48296 : int) : ((term544 _48296) = term97) = ((term270 _48296) = term97).
Proof. exact (MK_COMB (@lem4114685 _48296) (@lem4114686)). Qed.
Lemma lem4114688 (_48296 : int) (h1 : term612 _48296) : (term270 _48296) = term97.
Proof. exact (EQ_MP (@lem4114687 _48296) (@lem4114682 _48296 h1)). Qed.
Lemma lem4114689 (_48296 : int) (h1 : term612 _48296) : term615 _48296.
Proof. exact (conj (@lem4114688 _48296 h1) (@lem4114675 _48296 h1)). Qed.
Lemma lem4114691 (x : real) (y : real) : term564 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem4114692 (_48296 : int) : term616 _48296.
Proof. exact (@lem4114691 (term270 _48296) (term281 _48296)). Qed.
Lemma lem4114693 (_48296 : int) (h1 : term612 _48296) : term617 _48296.
Proof. exact (@lem4114692 _48296 (@lem4114689 _48296 h1)). Qed.
Lemma lem4114694 (_48296 : int) : (term618 _48296) = (term587 _48296).
Proof. exact (@lem1982759 (real_of_int _48296) (term281 _48296) term178). Qed.
Lemma lem4114695 (_48296 : int) : (term588 _48296) = (term477 _48296).
Proof. exact (@lem1982715 term178 (real_of_int _48296)). Qed.
Lemma lem4114697 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114698 : term111 = term200.
Proof. exact (@lem4114697 term20). Qed.
Lemma lem4114700 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4114701 : term178 = term179.
Proof. exact (@lem4114700 term20). Qed.
Lemma lem4114702 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4114703 : term478 = term479.
Proof. exact (MK_COMB (@lem4114702) (@lem4114701)). Qed.
Lemma lem4114704 : term480 = term481.
Proof. exact (MK_COMB (@lem4114703) (@lem4114698)). Qed.
Lemma lem4114705 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4114707 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114708 : term206 = term207.
Proof. exact (@lem4114707 (NUMERAL 0) term20). Qed.
Lemma lem4114709 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114710 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114711 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114710 h1) (fun h1 : term207 = True => @lem4114709)). Qed.
Lemma lem4114712 : term207 = True.
Proof. exact (EQ_MP (@lem4114711) (@lem4114709)). Qed.
Lemma lem4114713 : term206 = True.
Proof. exact (TRANS (@lem4114708) (@lem4114712)). Qed.
Lemma lem4114714 : True = term206.
Proof. exact (SYM (@lem4114713)). Qed.
Lemma lem4114715 : term206.
Proof. exact (EQ_MP (@lem4114714) (@lem0)). Qed.
Lemma lem4114716 : term483.
Proof. exact (@lem4114705 (@lem4114715)). Qed.
Lemma lem4114718 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114719 : term206 = term207.
Proof. exact (@lem4114718 (NUMERAL 0) term20). Qed.
Lemma lem4114720 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114721 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114722 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114721 h1) (fun h1 : term207 = True => @lem4114720)). Qed.
Lemma lem4114723 : term207 = True.
Proof. exact (EQ_MP (@lem4114722) (@lem4114720)). Qed.
Lemma lem4114724 : term206 = True.
Proof. exact (TRANS (@lem4114719) (@lem4114723)). Qed.
Lemma lem4114725 : True = term206.
Proof. exact (SYM (@lem4114724)). Qed.
Lemma lem4114726 : term206.
Proof. exact (EQ_MP (@lem4114725) (@lem0)). Qed.
Lemma lem4114727 : term484.
Proof. exact (@lem4114716 (@lem4114726)). Qed.
Lemma lem4114729 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114730 : term206 = term207.
Proof. exact (@lem4114729 (NUMERAL 0) term20). Qed.
Lemma lem4114731 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114732 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114733 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114732 h1) (fun h1 : term207 = True => @lem4114731)). Qed.
Lemma lem4114734 : term207 = True.
Proof. exact (EQ_MP (@lem4114733) (@lem4114731)). Qed.
Lemma lem4114735 : term206 = True.
Proof. exact (TRANS (@lem4114730) (@lem4114734)). Qed.
Lemma lem4114736 : True = term206.
Proof. exact (SYM (@lem4114735)). Qed.
Lemma lem4114737 : term206.
Proof. exact (EQ_MP (@lem4114736) (@lem0)). Qed.
Lemma lem4114738 : term485.
Proof. exact (@lem4114727 (@lem4114737)). Qed.
Lemma lem4114740 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4114741 : term187 = term188.
Proof. exact (@lem4114740 term20 term20). Qed.
Lemma lem4114742 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114743 : term190 = term20.
Proof. exact (EQ_MP (@lem4114742) (@lem940073)). Qed.
Lemma lem4114744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114745 : term188 = term111.
Proof. exact (MK_COMB (@lem4114744) (@lem4114743)). Qed.
Lemma lem4114746 : term187 = term111.
Proof. exact (TRANS (@lem4114741) (@lem4114745)). Qed.
Lemma lem4114748 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4114749 : term254 = term257.
Proof. exact (@lem4114748 term20 term20). Qed.
Lemma lem4114750 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114751 : term190 = term20.
Proof. exact (EQ_MP (@lem4114750) (@lem940073)). Qed.
Lemma lem4114752 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114753 : term188 = term111.
Proof. exact (MK_COMB (@lem4114752) (@lem4114751)). Qed.
Lemma lem4114754 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4114755 : term257 = term178.
Proof. exact (MK_COMB (@lem4114754) (@lem4114753)). Qed.
Lemma lem4114756 : term254 = term178.
Proof. exact (TRANS (@lem4114749) (@lem4114755)). Qed.
Lemma lem4114757 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4114758 : term486 = term478.
Proof. exact (MK_COMB (@lem4114757) (@lem4114756)). Qed.
Lemma lem4114759 : term487 = term480.
Proof. exact (MK_COMB (@lem4114758) (@lem4114746)). Qed.
Lemma lem4114761 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4114762 : term480 = term97.
Proof. exact (@lem4114761 term20). Qed.
Lemma lem4114763 : term487 = term97.
Proof. exact (TRANS (@lem4114759) (@lem4114762)). Qed.
Lemma lem4114764 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4114765 : term489 = term291.
Proof. exact (MK_COMB (@lem4114764) (@lem4114763)). Qed.
Lemma lem4114766 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4114767 : term490 = term293.
Proof. exact (MK_COMB (@lem4114765) (@lem4114766)). Qed.
Lemma lem4114769 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4114770 : term293 = term97.
Proof. exact (@lem4114769 term20). Qed.
Lemma lem4114771 : term490 = term97.
Proof. exact (TRANS (@lem4114767) (@lem4114770)). Qed.
Lemma lem4114773 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4114774 : term187 = term188.
Proof. exact (@lem4114773 term20 term20). Qed.
Lemma lem4114775 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114776 : term190 = term20.
Proof. exact (EQ_MP (@lem4114775) (@lem940073)). Qed.
Lemma lem4114777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114778 : term188 = term111.
Proof. exact (MK_COMB (@lem4114777) (@lem4114776)). Qed.
Lemma lem4114779 : term187 = term111.
Proof. exact (TRANS (@lem4114774) (@lem4114778)). Qed.
Lemma lem4114780 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4114781 : term295 = term293.
Proof. exact (MK_COMB (@lem4114780) (@lem4114779)). Qed.
Lemma lem4114783 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4114784 : term293 = term97.
Proof. exact (@lem4114783 term20). Qed.
Lemma lem4114785 : term295 = term97.
Proof. exact (TRANS (@lem4114781) (@lem4114784)). Qed.
Lemma lem4114786 : term97 = term295.
Proof. exact (SYM (@lem4114785)). Qed.
Lemma lem4114787 : term490 = term295.
Proof. exact (TRANS (@lem4114771) (@lem4114786)). Qed.
Lemma lem4114788 : term481 = term175.
Proof. exact (@lem4114738 (@lem4114787)). Qed.
Lemma lem4114789 : term480 = term175.
Proof. exact (TRANS (@lem4114704) (@lem4114788)). Qed.
Lemma lem4114791 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4114792 : term175 = term97.
Proof. exact (@lem4114791 term97). Qed.
Lemma lem4114793 : term480 = term97.
Proof. exact (TRANS (@lem4114789) (@lem4114792)). Qed.
Lemma lem4114794 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4114795 : term491 = term291.
Proof. exact (MK_COMB (@lem4114794) (@lem4114793)). Qed.
Lemma lem4114796 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4114797 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4114795) (@lem4114796 _48296)). Qed.
Lemma lem4114798 (_48296 : int) : (term588 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4114695 _48296) (@lem4114797 _48296)). Qed.
Lemma lem4114799 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4114800 (_48296 : int) : (term588 _48296) = term97.
Proof. exact (TRANS (@lem4114798 _48296) (@lem4114799 _48296)). Qed.
Lemma lem4114801 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4114802 (_48296 : int) : (term589 _48296) = term139.
Proof. exact (MK_COMB (@lem4114801) (@lem4114800 _48296)). Qed.
Lemma lem4114803 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem4114804 (_48296 : int) : (term587 _48296) = term508.
Proof. exact (MK_COMB (@lem4114802 _48296) (@lem4114803)). Qed.
Lemma lem4114805 (_48296 : int) : (term618 _48296) = term508.
Proof. exact (TRANS (@lem4114694 _48296) (@lem4114804 _48296)). Qed.
Lemma lem4114806 : term508 = term178.
Proof. exact (@lem1982721 term178). Qed.
Lemma lem4114807 (_48296 : int) : (term618 _48296) = term178.
Proof. exact (TRANS (@lem4114805 _48296) (@lem4114806)). Qed.
Lemma lem4114808 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4114809 (_48296 : int) : (term619 _48296) = term510.
Proof. exact (MK_COMB (@lem4114808) (@lem4114807 _48296)). Qed.
Lemma lem4114810 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4114811 (_48296 : int) : (term617 _48296) = term511.
Proof. exact (MK_COMB (@lem4114809 _48296) (@lem4114810)). Qed.
Lemma lem4114812 (_48296 : int) (h1 : term612 _48296) : term511.
Proof. exact (EQ_MP (@lem4114811 _48296) (@lem4114693 _48296 h1)). Qed.
Lemma lem4114814 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4114815 : term511 = term512.
Proof. exact (@lem4114814 term97 term178). Qed.
Lemma lem4114817 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4114818 : term178 = term179.
Proof. exact (@lem4114817 term20). Qed.
Lemma lem4114820 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114821 : term97 = term175.
Proof. exact (@lem4114820 (NUMERAL 0)). Qed.
Lemma lem4114822 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4114823 : term99 = term513.
Proof. exact (MK_COMB (@lem4114822) (@lem4114821)). Qed.
Lemma lem4114824 : term512 = term514.
Proof. exact (MK_COMB (@lem4114823) (@lem4114818)). Qed.
Lemma lem4114825 : term515.
Proof. exact (@lem1980026 term97 term111 term178 term111). Qed.
Lemma lem4114827 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114828 : term206 = term207.
Proof. exact (@lem4114827 (NUMERAL 0) term20). Qed.
Lemma lem4114829 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114830 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114831 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114830 h1) (fun h1 : term207 = True => @lem4114829)). Qed.
Lemma lem4114832 : term207 = True.
Proof. exact (EQ_MP (@lem4114831) (@lem4114829)). Qed.
Lemma lem4114833 : term206 = True.
Proof. exact (TRANS (@lem4114828) (@lem4114832)). Qed.
Lemma lem4114834 : True = term206.
Proof. exact (SYM (@lem4114833)). Qed.
Lemma lem4114835 : term206.
Proof. exact (EQ_MP (@lem4114834) (@lem0)). Qed.
Lemma lem4114836 : term516.
Proof. exact (@lem4114825 (@lem4114835)). Qed.
Lemma lem4114838 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114839 : term206 = term207.
Proof. exact (@lem4114838 (NUMERAL 0) term20). Qed.
Lemma lem4114840 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114841 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114842 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114841 h1) (fun h1 : term207 = True => @lem4114840)). Qed.
Lemma lem4114843 : term207 = True.
Proof. exact (EQ_MP (@lem4114842) (@lem4114840)). Qed.
Lemma lem4114844 : term206 = True.
Proof. exact (TRANS (@lem4114839) (@lem4114843)). Qed.
Lemma lem4114845 : True = term206.
Proof. exact (SYM (@lem4114844)). Qed.
Lemma lem4114846 : term206.
Proof. exact (EQ_MP (@lem4114845) (@lem0)). Qed.
Lemma lem4114847 : term514 = term517.
Proof. exact (@lem4114836 (@lem4114846)). Qed.
Lemma lem4114849 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4114850 : term254 = term257.
Proof. exact (@lem4114849 term20 term20). Qed.
Lemma lem4114851 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114852 : term190 = term20.
Proof. exact (EQ_MP (@lem4114851) (@lem940073)). Qed.
Lemma lem4114853 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114854 : term188 = term111.
Proof. exact (MK_COMB (@lem4114853) (@lem4114852)). Qed.
Lemma lem4114855 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4114856 : term257 = term178.
Proof. exact (MK_COMB (@lem4114855) (@lem4114854)). Qed.
Lemma lem4114857 : term254 = term178.
Proof. exact (TRANS (@lem4114850) (@lem4114856)). Qed.
Lemma lem4114859 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4114860 : term293 = term97.
Proof. exact (@lem4114859 term20). Qed.
Lemma lem4114861 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4114862 : term518 = term99.
Proof. exact (MK_COMB (@lem4114861) (@lem4114860)). Qed.
Lemma lem4114863 : term517 = term512.
Proof. exact (MK_COMB (@lem4114862) (@lem4114857)). Qed.
Lemma lem4114865 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4114866 : term512 = term521.
Proof. exact (@lem4114865 (NUMERAL 0) term20). Qed.
Lemma lem4114867 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114868 (h1 : term208 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4114869 : (term208 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114868 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem4114867)). Qed.
Lemma lem4114870 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4114869) (@lem4114867)). Qed.
Lemma lem4114871 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4114872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4114873 : term522 = (and True).
Proof. exact (MK_COMB (@lem4114872) (@lem4114871)). Qed.
Lemma lem4114874 : term521 = (True /\ False).
Proof. exact (MK_COMB (@lem4114873) (@lem4114870)). Qed.
Lemma lem4114876 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4114877 : term521 = False.
Proof. exact (TRANS (@lem4114874) (@lem4114876)). Qed.
Lemma lem4114878 : term512 = False.
Proof. exact (TRANS (@lem4114866) (@lem4114877)). Qed.
Lemma lem4114879 : term517 = False.
Proof. exact (TRANS (@lem4114863) (@lem4114878)). Qed.
Lemma lem4114880 : term514 = False.
Proof. exact (TRANS (@lem4114847) (@lem4114879)). Qed.
Lemma lem4114881 : term512 = False.
Proof. exact (TRANS (@lem4114824) (@lem4114880)). Qed.
Lemma lem4114882 : term511 = False.
Proof. exact (TRANS (@lem4114815) (@lem4114881)). Qed.
Lemma lem4114883 (_48296 : int) (h1 : term612 _48296) : False.
Proof. exact (EQ_MP (@lem4114882) (@lem4114812 _48296 h1)). Qed.
Lemma lem4114884 (_48296 : int) (h1 : term620 _48296) : term620 _48296.
Proof. exact (h1). Qed.
Lemma lem4114885 (_48296 : int) (h1 : term620 _48296) : term402 _48296.
Proof. exact (proj2 (@lem4114884 _48296 h1)). Qed.
Lemma lem4114887 (_48296 : int) (h1 : term620 _48296) : (term270 _48296) = term97.
Proof. exact (proj2 (@lem4114885 _48296 h1)). Qed.
Lemma lem4114888 (_48296 : int) (h1 : term620 _48296) : term348 _48296.
Proof. exact (proj1 (@lem4114885 _48296 h1)). Qed.
Lemma lem4114889 (_48296 : int) (h1 : term620 _48296) : term299 _48296.
Proof. exact (proj2 (@lem4114888 _48296 h1)). Qed.
Lemma lem4114892 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4114893 : term451 = term206.
Proof. exact (@lem4114892 term97 term111). Qed.
Lemma lem4114895 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114896 : term111 = term200.
Proof. exact (@lem4114895 term20). Qed.
Lemma lem4114898 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114899 : term97 = term175.
Proof. exact (@lem4114898 (NUMERAL 0)). Qed.
Lemma lem4114900 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4114901 : term452 = term453.
Proof. exact (MK_COMB (@lem4114900) (@lem4114899)). Qed.
Lemma lem4114902 : term206 = term454.
Proof. exact (MK_COMB (@lem4114901) (@lem4114896)). Qed.
Lemma lem4114903 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4114905 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114906 : term206 = term207.
Proof. exact (@lem4114905 (NUMERAL 0) term20). Qed.
Lemma lem4114907 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114908 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114909 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114908 h1) (fun h1 : term207 = True => @lem4114907)). Qed.
Lemma lem4114910 : term207 = True.
Proof. exact (EQ_MP (@lem4114909) (@lem4114907)). Qed.
Lemma lem4114911 : term206 = True.
Proof. exact (TRANS (@lem4114906) (@lem4114910)). Qed.
Lemma lem4114912 : True = term206.
Proof. exact (SYM (@lem4114911)). Qed.
Lemma lem4114913 : term206.
Proof. exact (EQ_MP (@lem4114912) (@lem0)). Qed.
Lemma lem4114914 : term456.
Proof. exact (@lem4114903 (@lem4114913)). Qed.
Lemma lem4114916 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114917 : term206 = term207.
Proof. exact (@lem4114916 (NUMERAL 0) term20). Qed.
Lemma lem4114918 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114919 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114920 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114919 h1) (fun h1 : term207 = True => @lem4114918)). Qed.
Lemma lem4114921 : term207 = True.
Proof. exact (EQ_MP (@lem4114920) (@lem4114918)). Qed.
Lemma lem4114922 : term206 = True.
Proof. exact (TRANS (@lem4114917) (@lem4114921)). Qed.
Lemma lem4114923 : True = term206.
Proof. exact (SYM (@lem4114922)). Qed.
Lemma lem4114924 : term206.
Proof. exact (EQ_MP (@lem4114923) (@lem0)). Qed.
Lemma lem4114925 : term454 = term457.
Proof. exact (@lem4114914 (@lem4114924)). Qed.
Lemma lem4114927 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4114928 : term187 = term188.
Proof. exact (@lem4114927 term20 term20). Qed.
Lemma lem4114929 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4114930 : term190 = term20.
Proof. exact (EQ_MP (@lem4114929) (@lem940073)). Qed.
Lemma lem4114931 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4114932 : term188 = term111.
Proof. exact (MK_COMB (@lem4114931) (@lem4114930)). Qed.
Lemma lem4114933 : term187 = term111.
Proof. exact (TRANS (@lem4114928) (@lem4114932)). Qed.
Lemma lem4114935 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4114936 : term293 = term97.
Proof. exact (@lem4114935 term20). Qed.
Lemma lem4114937 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4114938 : term458 = term452.
Proof. exact (MK_COMB (@lem4114937) (@lem4114936)). Qed.
Lemma lem4114939 : term457 = term206.
Proof. exact (MK_COMB (@lem4114938) (@lem4114933)). Qed.
Lemma lem4114941 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114942 : term206 = term207.
Proof. exact (@lem4114941 (NUMERAL 0) term20). Qed.
Lemma lem4114943 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114944 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4114945 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114944 h1) (fun h1 : term207 = True => @lem4114943)). Qed.
Lemma lem4114946 : term207 = True.
Proof. exact (EQ_MP (@lem4114945) (@lem4114943)). Qed.
Lemma lem4114947 : term206 = True.
Proof. exact (TRANS (@lem4114942) (@lem4114946)). Qed.
Lemma lem4114948 : term457 = True.
Proof. exact (TRANS (@lem4114939) (@lem4114947)). Qed.
Lemma lem4114949 : term454 = True.
Proof. exact (TRANS (@lem4114925) (@lem4114948)). Qed.
Lemma lem4114950 : term206 = True.
Proof. exact (TRANS (@lem4114902) (@lem4114949)). Qed.
Lemma lem4114951 : term451 = True.
Proof. exact (TRANS (@lem4114893) (@lem4114950)). Qed.
Lemma lem4114952 : True = term451.
Proof. exact (SYM (@lem4114951)). Qed.
Lemma lem4114953 : term451.
Proof. exact (EQ_MP (@lem4114952) (@lem0)). Qed.
Lemma lem4114954 (_48296 : int) (h1 : term620 _48296) : term546 _48296.
Proof. exact (conj (@lem4114953) (@lem4114889 _48296 h1)). Qed.
Lemma lem4114956 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4114957 (_48296 : int) : term547 _48296.
Proof. exact (@lem4114956 term111 (term281 _48296)). Qed.
Lemma lem4114958 (_48296 : int) (h1 : term620 _48296) : term548 _48296.
Proof. exact (@lem4114957 _48296 (@lem4114954 _48296 h1)). Qed.
Lemma lem4114959 (_48296 : int) : (term549 _48296) = (term281 _48296).
Proof. exact (@lem1982733 (term281 _48296)). Qed.
Lemma lem4114960 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4114961 (_48296 : int) : (term550 _48296) = (term298 _48296).
Proof. exact (MK_COMB (@lem4114960) (@lem4114959 _48296)). Qed.
Lemma lem4114962 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4114963 (_48296 : int) : (term548 _48296) = (term299 _48296).
Proof. exact (MK_COMB (@lem4114961 _48296) (@lem4114962)). Qed.
Lemma lem4114964 (_48296 : int) (h1 : term620 _48296) : term299 _48296.
Proof. exact (EQ_MP (@lem4114963 _48296) (@lem4114958 _48296 h1)). Qed.
Lemma lem4114966 (y : real) : term559 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem4114967 (_48296 : int) : term597 _48296.
Proof. exact (@lem4114966 (term270 _48296)). Qed.
Lemma lem4114968 (_48296 : int) (h1 : term620 _48296) : term598 _48296.
Proof. exact (@lem4114967 _48296 (@lem4114887 _48296 h1)). Qed.
Lemma lem4114969 (_48296 : int) (h1 : term620 _48296) : term613 _48296.
Proof. exact (@lem4114968 _48296 h1 term111). Qed.
Lemma lem4114970 (_48296 : int) : (term613 _48296) = ((term544 _48296) = term97).
Proof. exact (eq_refl (term613 _48296)). Qed.
Lemma lem4114971 (_48296 : int) (h1 : term620 _48296) : (term544 _48296) = term97.
Proof. exact (EQ_MP (@lem4114970 _48296) (@lem4114969 _48296 h1)). Qed.
Lemma lem4114972 (_48296 : int) : (term544 _48296) = (term270 _48296).
Proof. exact (@lem1982733 (term270 _48296)). Qed.
Lemma lem4114973 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem4114974 (_48296 : int) : (term614 _48296) = (term315 _48296).
Proof. exact (MK_COMB (@lem4114973) (@lem4114972 _48296)). Qed.
Lemma lem4114975 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4114976 (_48296 : int) : ((term544 _48296) = term97) = ((term270 _48296) = term97).
Proof. exact (MK_COMB (@lem4114974 _48296) (@lem4114975)). Qed.
Lemma lem4114977 (_48296 : int) (h1 : term620 _48296) : (term270 _48296) = term97.
Proof. exact (EQ_MP (@lem4114976 _48296) (@lem4114971 _48296 h1)). Qed.
Lemma lem4114978 (_48296 : int) (h1 : term620 _48296) : term615 _48296.
Proof. exact (conj (@lem4114977 _48296 h1) (@lem4114964 _48296 h1)). Qed.
Lemma lem4114980 (x : real) (y : real) : term564 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem4114981 (_48296 : int) : term616 _48296.
Proof. exact (@lem4114980 (term270 _48296) (term281 _48296)). Qed.
Lemma lem4114982 (_48296 : int) (h1 : term620 _48296) : term617 _48296.
Proof. exact (@lem4114981 _48296 (@lem4114978 _48296 h1)). Qed.
Lemma lem4114983 (_48296 : int) : (term618 _48296) = (term587 _48296).
Proof. exact (@lem1982759 (real_of_int _48296) (term281 _48296) term178). Qed.
Lemma lem4114984 (_48296 : int) : (term588 _48296) = (term477 _48296).
Proof. exact (@lem1982715 term178 (real_of_int _48296)). Qed.
Lemma lem4114986 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4114987 : term111 = term200.
Proof. exact (@lem4114986 term20). Qed.
Lemma lem4114989 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4114990 : term178 = term179.
Proof. exact (@lem4114989 term20). Qed.
Lemma lem4114991 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4114992 : term478 = term479.
Proof. exact (MK_COMB (@lem4114991) (@lem4114990)). Qed.
Lemma lem4114993 : term480 = term481.
Proof. exact (MK_COMB (@lem4114992) (@lem4114987)). Qed.
Lemma lem4114994 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4114996 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4114997 : term206 = term207.
Proof. exact (@lem4114996 (NUMERAL 0) term20). Qed.
Lemma lem4114998 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4114999 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115000 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4114999 h1) (fun h1 : term207 = True => @lem4114998)). Qed.
Lemma lem4115001 : term207 = True.
Proof. exact (EQ_MP (@lem4115000) (@lem4114998)). Qed.
Lemma lem4115002 : term206 = True.
Proof. exact (TRANS (@lem4114997) (@lem4115001)). Qed.
Lemma lem4115003 : True = term206.
Proof. exact (SYM (@lem4115002)). Qed.
Lemma lem4115004 : term206.
Proof. exact (EQ_MP (@lem4115003) (@lem0)). Qed.
Lemma lem4115005 : term483.
Proof. exact (@lem4114994 (@lem4115004)). Qed.
Lemma lem4115007 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115008 : term206 = term207.
Proof. exact (@lem4115007 (NUMERAL 0) term20). Qed.
Lemma lem4115009 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115010 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115011 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115010 h1) (fun h1 : term207 = True => @lem4115009)). Qed.
Lemma lem4115012 : term207 = True.
Proof. exact (EQ_MP (@lem4115011) (@lem4115009)). Qed.
Lemma lem4115013 : term206 = True.
Proof. exact (TRANS (@lem4115008) (@lem4115012)). Qed.
Lemma lem4115014 : True = term206.
Proof. exact (SYM (@lem4115013)). Qed.
Lemma lem4115015 : term206.
Proof. exact (EQ_MP (@lem4115014) (@lem0)). Qed.
Lemma lem4115016 : term484.
Proof. exact (@lem4115005 (@lem4115015)). Qed.
Lemma lem4115018 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115019 : term206 = term207.
Proof. exact (@lem4115018 (NUMERAL 0) term20). Qed.
Lemma lem4115020 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115021 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115022 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115021 h1) (fun h1 : term207 = True => @lem4115020)). Qed.
Lemma lem4115023 : term207 = True.
Proof. exact (EQ_MP (@lem4115022) (@lem4115020)). Qed.
Lemma lem4115024 : term206 = True.
Proof. exact (TRANS (@lem4115019) (@lem4115023)). Qed.
Lemma lem4115025 : True = term206.
Proof. exact (SYM (@lem4115024)). Qed.
Lemma lem4115026 : term206.
Proof. exact (EQ_MP (@lem4115025) (@lem0)). Qed.
Lemma lem4115027 : term485.
Proof. exact (@lem4115016 (@lem4115026)). Qed.
Lemma lem4115029 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115030 : term187 = term188.
Proof. exact (@lem4115029 term20 term20). Qed.
Lemma lem4115031 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115032 : term190 = term20.
Proof. exact (EQ_MP (@lem4115031) (@lem940073)). Qed.
Lemma lem4115033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115034 : term188 = term111.
Proof. exact (MK_COMB (@lem4115033) (@lem4115032)). Qed.
Lemma lem4115035 : term187 = term111.
Proof. exact (TRANS (@lem4115030) (@lem4115034)). Qed.
Lemma lem4115037 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4115038 : term254 = term257.
Proof. exact (@lem4115037 term20 term20). Qed.
Lemma lem4115039 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115040 : term190 = term20.
Proof. exact (EQ_MP (@lem4115039) (@lem940073)). Qed.
Lemma lem4115041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115042 : term188 = term111.
Proof. exact (MK_COMB (@lem4115041) (@lem4115040)). Qed.
Lemma lem4115043 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115044 : term257 = term178.
Proof. exact (MK_COMB (@lem4115043) (@lem4115042)). Qed.
Lemma lem4115045 : term254 = term178.
Proof. exact (TRANS (@lem4115038) (@lem4115044)). Qed.
Lemma lem4115046 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4115047 : term486 = term478.
Proof. exact (MK_COMB (@lem4115046) (@lem4115045)). Qed.
Lemma lem4115048 : term487 = term480.
Proof. exact (MK_COMB (@lem4115047) (@lem4115035)). Qed.
Lemma lem4115050 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4115051 : term480 = term97.
Proof. exact (@lem4115050 term20). Qed.
Lemma lem4115052 : term487 = term97.
Proof. exact (TRANS (@lem4115048) (@lem4115051)). Qed.
Lemma lem4115053 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4115054 : term489 = term291.
Proof. exact (MK_COMB (@lem4115053) (@lem4115052)). Qed.
Lemma lem4115055 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4115056 : term490 = term293.
Proof. exact (MK_COMB (@lem4115054) (@lem4115055)). Qed.
Lemma lem4115058 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4115059 : term293 = term97.
Proof. exact (@lem4115058 term20). Qed.
Lemma lem4115060 : term490 = term97.
Proof. exact (TRANS (@lem4115056) (@lem4115059)). Qed.
Lemma lem4115062 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115063 : term187 = term188.
Proof. exact (@lem4115062 term20 term20). Qed.
Lemma lem4115064 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115065 : term190 = term20.
Proof. exact (EQ_MP (@lem4115064) (@lem940073)). Qed.
Lemma lem4115066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115067 : term188 = term111.
Proof. exact (MK_COMB (@lem4115066) (@lem4115065)). Qed.
Lemma lem4115068 : term187 = term111.
Proof. exact (TRANS (@lem4115063) (@lem4115067)). Qed.
Lemma lem4115069 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4115070 : term295 = term293.
Proof. exact (MK_COMB (@lem4115069) (@lem4115068)). Qed.
Lemma lem4115072 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4115073 : term293 = term97.
Proof. exact (@lem4115072 term20). Qed.
Lemma lem4115074 : term295 = term97.
Proof. exact (TRANS (@lem4115070) (@lem4115073)). Qed.
Lemma lem4115075 : term97 = term295.
Proof. exact (SYM (@lem4115074)). Qed.
Lemma lem4115076 : term490 = term295.
Proof. exact (TRANS (@lem4115060) (@lem4115075)). Qed.
Lemma lem4115077 : term481 = term175.
Proof. exact (@lem4115027 (@lem4115076)). Qed.
Lemma lem4115078 : term480 = term175.
Proof. exact (TRANS (@lem4114993) (@lem4115077)). Qed.
Lemma lem4115080 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4115081 : term175 = term97.
Proof. exact (@lem4115080 term97). Qed.
Lemma lem4115082 : term480 = term97.
Proof. exact (TRANS (@lem4115078) (@lem4115081)). Qed.
Lemma lem4115083 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4115084 : term491 = term291.
Proof. exact (MK_COMB (@lem4115083) (@lem4115082)). Qed.
Lemma lem4115085 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4115086 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4115084) (@lem4115085 _48296)). Qed.
Lemma lem4115087 (_48296 : int) : (term588 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4114984 _48296) (@lem4115086 _48296)). Qed.
Lemma lem4115088 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4115089 (_48296 : int) : (term588 _48296) = term97.
Proof. exact (TRANS (@lem4115087 _48296) (@lem4115088 _48296)). Qed.
Lemma lem4115090 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4115091 (_48296 : int) : (term589 _48296) = term139.
Proof. exact (MK_COMB (@lem4115090) (@lem4115089 _48296)). Qed.
Lemma lem4115092 : term178 = term178.
Proof. exact (eq_refl term178). Qed.
Lemma lem4115093 (_48296 : int) : (term587 _48296) = term508.
Proof. exact (MK_COMB (@lem4115091 _48296) (@lem4115092)). Qed.
Lemma lem4115094 (_48296 : int) : (term618 _48296) = term508.
Proof. exact (TRANS (@lem4114983 _48296) (@lem4115093 _48296)). Qed.
Lemma lem4115095 : term508 = term178.
Proof. exact (@lem1982721 term178). Qed.
Lemma lem4115096 (_48296 : int) : (term618 _48296) = term178.
Proof. exact (TRANS (@lem4115094 _48296) (@lem4115095)). Qed.
Lemma lem4115097 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4115098 (_48296 : int) : (term619 _48296) = term510.
Proof. exact (MK_COMB (@lem4115097) (@lem4115096 _48296)). Qed.
Lemma lem4115099 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4115100 (_48296 : int) : (term617 _48296) = term511.
Proof. exact (MK_COMB (@lem4115098 _48296) (@lem4115099)). Qed.
Lemma lem4115101 (_48296 : int) (h1 : term620 _48296) : term511.
Proof. exact (EQ_MP (@lem4115100 _48296) (@lem4114982 _48296 h1)). Qed.
Lemma lem4115103 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4115104 : term511 = term512.
Proof. exact (@lem4115103 term97 term178). Qed.
Lemma lem4115106 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4115107 : term178 = term179.
Proof. exact (@lem4115106 term20). Qed.
Lemma lem4115109 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4115110 : term97 = term175.
Proof. exact (@lem4115109 (NUMERAL 0)). Qed.
Lemma lem4115111 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4115112 : term99 = term513.
Proof. exact (MK_COMB (@lem4115111) (@lem4115110)). Qed.
Lemma lem4115113 : term512 = term514.
Proof. exact (MK_COMB (@lem4115112) (@lem4115107)). Qed.
Lemma lem4115114 : term515.
Proof. exact (@lem1980026 term97 term111 term178 term111). Qed.
Lemma lem4115116 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115117 : term206 = term207.
Proof. exact (@lem4115116 (NUMERAL 0) term20). Qed.
Lemma lem4115118 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115119 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115120 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115119 h1) (fun h1 : term207 = True => @lem4115118)). Qed.
Lemma lem4115121 : term207 = True.
Proof. exact (EQ_MP (@lem4115120) (@lem4115118)). Qed.
Lemma lem4115122 : term206 = True.
Proof. exact (TRANS (@lem4115117) (@lem4115121)). Qed.
Lemma lem4115123 : True = term206.
Proof. exact (SYM (@lem4115122)). Qed.
Lemma lem4115124 : term206.
Proof. exact (EQ_MP (@lem4115123) (@lem0)). Qed.
Lemma lem4115125 : term516.
Proof. exact (@lem4115114 (@lem4115124)). Qed.
Lemma lem4115127 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115128 : term206 = term207.
Proof. exact (@lem4115127 (NUMERAL 0) term20). Qed.
Lemma lem4115129 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115130 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115131 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115130 h1) (fun h1 : term207 = True => @lem4115129)). Qed.
Lemma lem4115132 : term207 = True.
Proof. exact (EQ_MP (@lem4115131) (@lem4115129)). Qed.
Lemma lem4115133 : term206 = True.
Proof. exact (TRANS (@lem4115128) (@lem4115132)). Qed.
Lemma lem4115134 : True = term206.
Proof. exact (SYM (@lem4115133)). Qed.
Lemma lem4115135 : term206.
Proof. exact (EQ_MP (@lem4115134) (@lem0)). Qed.
Lemma lem4115136 : term514 = term517.
Proof. exact (@lem4115125 (@lem4115135)). Qed.
Lemma lem4115138 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4115139 : term254 = term257.
Proof. exact (@lem4115138 term20 term20). Qed.
Lemma lem4115140 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115141 : term190 = term20.
Proof. exact (EQ_MP (@lem4115140) (@lem940073)). Qed.
Lemma lem4115142 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115143 : term188 = term111.
Proof. exact (MK_COMB (@lem4115142) (@lem4115141)). Qed.
Lemma lem4115144 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115145 : term257 = term178.
Proof. exact (MK_COMB (@lem4115144) (@lem4115143)). Qed.
Lemma lem4115146 : term254 = term178.
Proof. exact (TRANS (@lem4115139) (@lem4115145)). Qed.
Lemma lem4115148 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4115149 : term293 = term97.
Proof. exact (@lem4115148 term20). Qed.
Lemma lem4115150 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4115151 : term518 = term99.
Proof. exact (MK_COMB (@lem4115150) (@lem4115149)). Qed.
Lemma lem4115152 : term517 = term512.
Proof. exact (MK_COMB (@lem4115151) (@lem4115146)). Qed.
Lemma lem4115154 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4115155 : term512 = term521.
Proof. exact (@lem4115154 (NUMERAL 0) term20). Qed.
Lemma lem4115156 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115157 (h1 : term208 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4115158 : (term208 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115157 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem4115156)). Qed.
Lemma lem4115159 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4115158) (@lem4115156)). Qed.
Lemma lem4115160 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4115161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4115162 : term522 = (and True).
Proof. exact (MK_COMB (@lem4115161) (@lem4115160)). Qed.
Lemma lem4115163 : term521 = (True /\ False).
Proof. exact (MK_COMB (@lem4115162) (@lem4115159)). Qed.
Lemma lem4115165 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4115166 : term521 = False.
Proof. exact (TRANS (@lem4115163) (@lem4115165)). Qed.
Lemma lem4115167 : term512 = False.
Proof. exact (TRANS (@lem4115155) (@lem4115166)). Qed.
Lemma lem4115168 : term517 = False.
Proof. exact (TRANS (@lem4115152) (@lem4115167)). Qed.
Lemma lem4115169 : term514 = False.
Proof. exact (TRANS (@lem4115136) (@lem4115168)). Qed.
Lemma lem4115170 : term512 = False.
Proof. exact (TRANS (@lem4115113) (@lem4115169)). Qed.
Lemma lem4115171 : term511 = False.
Proof. exact (TRANS (@lem4115104) (@lem4115170)). Qed.
Lemma lem4115172 (_48296 : int) (h1 : term620 _48296) : False.
Proof. exact (EQ_MP (@lem4115171) (@lem4115101 _48296 h1)). Qed.
Lemma lem4115173 (_48296 : int) (h1 : term400 _48296) : False.
Proof. exact (or_elim (@lem4114594 _48296 h1) (fun h0 : term612 _48296 => @lem4114883 _48296 h0) (fun h0 : term620 _48296 => @lem4115172 _48296 h0)). Qed.
Lemma lem4115174 (_48296 : int) (h1 : term396 _48296) : term396 _48296.
Proof. exact (h1). Qed.
Lemma lem4115175 (_48296 : int) (h1 : term621 _48296) : term621 _48296.
Proof. exact (h1). Qed.
Lemma lem4115176 (_48296 : int) (h1 : term621 _48296) : term397 _48296.
Proof. exact (proj2 (@lem4115175 _48296 h1)). Qed.
Lemma lem4115178 (_48296 : int) (h1 : term621 _48296) : (term270 _48296) = term97.
Proof. exact (proj2 (@lem4115176 _48296 h1)). Qed.
Lemma lem4115179 (_48296 : int) (h1 : term621 _48296) : term343 _48296.
Proof. exact (proj1 (@lem4115176 _48296 h1)). Qed.
Lemma lem4115180 (_48296 : int) (h1 : term621 _48296) : term248 _48296.
Proof. exact (proj2 (@lem4115179 _48296 h1)). Qed.
Lemma lem4115183 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4115184 : term451 = term206.
Proof. exact (@lem4115183 term97 term111). Qed.
Lemma lem4115186 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4115187 : term111 = term200.
Proof. exact (@lem4115186 term20). Qed.
Lemma lem4115189 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4115190 : term97 = term175.
Proof. exact (@lem4115189 (NUMERAL 0)). Qed.
Lemma lem4115191 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4115192 : term452 = term453.
Proof. exact (MK_COMB (@lem4115191) (@lem4115190)). Qed.
Lemma lem4115193 : term206 = term454.
Proof. exact (MK_COMB (@lem4115192) (@lem4115187)). Qed.
Lemma lem4115194 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4115196 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115197 : term206 = term207.
Proof. exact (@lem4115196 (NUMERAL 0) term20). Qed.
Lemma lem4115198 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115199 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115200 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115199 h1) (fun h1 : term207 = True => @lem4115198)). Qed.
Lemma lem4115201 : term207 = True.
Proof. exact (EQ_MP (@lem4115200) (@lem4115198)). Qed.
Lemma lem4115202 : term206 = True.
Proof. exact (TRANS (@lem4115197) (@lem4115201)). Qed.
Lemma lem4115203 : True = term206.
Proof. exact (SYM (@lem4115202)). Qed.
Lemma lem4115204 : term206.
Proof. exact (EQ_MP (@lem4115203) (@lem0)). Qed.
Lemma lem4115205 : term456.
Proof. exact (@lem4115194 (@lem4115204)). Qed.
Lemma lem4115207 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115208 : term206 = term207.
Proof. exact (@lem4115207 (NUMERAL 0) term20). Qed.
Lemma lem4115209 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115210 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115211 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115210 h1) (fun h1 : term207 = True => @lem4115209)). Qed.
Lemma lem4115212 : term207 = True.
Proof. exact (EQ_MP (@lem4115211) (@lem4115209)). Qed.
Lemma lem4115213 : term206 = True.
Proof. exact (TRANS (@lem4115208) (@lem4115212)). Qed.
Lemma lem4115214 : True = term206.
Proof. exact (SYM (@lem4115213)). Qed.
Lemma lem4115215 : term206.
Proof. exact (EQ_MP (@lem4115214) (@lem0)). Qed.
Lemma lem4115216 : term454 = term457.
Proof. exact (@lem4115205 (@lem4115215)). Qed.
Lemma lem4115218 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115219 : term187 = term188.
Proof. exact (@lem4115218 term20 term20). Qed.
Lemma lem4115220 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115221 : term190 = term20.
Proof. exact (EQ_MP (@lem4115220) (@lem940073)). Qed.
Lemma lem4115222 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115223 : term188 = term111.
Proof. exact (MK_COMB (@lem4115222) (@lem4115221)). Qed.
Lemma lem4115224 : term187 = term111.
Proof. exact (TRANS (@lem4115219) (@lem4115223)). Qed.
Lemma lem4115226 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4115227 : term293 = term97.
Proof. exact (@lem4115226 term20). Qed.
Lemma lem4115228 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4115229 : term458 = term452.
Proof. exact (MK_COMB (@lem4115228) (@lem4115227)). Qed.
Lemma lem4115230 : term457 = term206.
Proof. exact (MK_COMB (@lem4115229) (@lem4115224)). Qed.
Lemma lem4115232 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115233 : term206 = term207.
Proof. exact (@lem4115232 (NUMERAL 0) term20). Qed.
Lemma lem4115234 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115235 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115236 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115235 h1) (fun h1 : term207 = True => @lem4115234)). Qed.
Lemma lem4115237 : term207 = True.
Proof. exact (EQ_MP (@lem4115236) (@lem4115234)). Qed.
Lemma lem4115238 : term206 = True.
Proof. exact (TRANS (@lem4115233) (@lem4115237)). Qed.
Lemma lem4115239 : term457 = True.
Proof. exact (TRANS (@lem4115230) (@lem4115238)). Qed.
Lemma lem4115240 : term454 = True.
Proof. exact (TRANS (@lem4115216) (@lem4115239)). Qed.
Lemma lem4115241 : term206 = True.
Proof. exact (TRANS (@lem4115193) (@lem4115240)). Qed.
Lemma lem4115242 : term451 = True.
Proof. exact (TRANS (@lem4115184) (@lem4115241)). Qed.
Lemma lem4115243 : True = term451.
Proof. exact (SYM (@lem4115242)). Qed.
Lemma lem4115244 : term451.
Proof. exact (EQ_MP (@lem4115243) (@lem0)). Qed.
Lemma lem4115245 (_48296 : int) (h1 : term621 _48296) : term459 _48296.
Proof. exact (conj (@lem4115244) (@lem4115180 _48296 h1)). Qed.
Lemma lem4115247 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4115248 (_48296 : int) : term461 _48296.
Proof. exact (@lem4115247 term111 (term245 _48296)). Qed.
Lemma lem4115249 (_48296 : int) (h1 : term621 _48296) : term462 _48296.
Proof. exact (@lem4115248 _48296 (@lem4115245 _48296 h1)). Qed.
Lemma lem4115250 (_48296 : int) : (term463 _48296) = (term245 _48296).
Proof. exact (@lem1982733 (term245 _48296)). Qed.
Lemma lem4115251 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4115252 (_48296 : int) : (term464 _48296) = (term247 _48296).
Proof. exact (MK_COMB (@lem4115251) (@lem4115250 _48296)). Qed.
Lemma lem4115253 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4115254 (_48296 : int) : (term462 _48296) = (term248 _48296).
Proof. exact (MK_COMB (@lem4115252 _48296) (@lem4115253)). Qed.
Lemma lem4115255 (_48296 : int) (h1 : term621 _48296) : term248 _48296.
Proof. exact (EQ_MP (@lem4115254 _48296) (@lem4115249 _48296 h1)). Qed.
Lemma lem4115257 (y : real) : term559 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem4115258 (_48296 : int) : term597 _48296.
Proof. exact (@lem4115257 (term270 _48296)). Qed.
Lemma lem4115259 (_48296 : int) (h1 : term621 _48296) : term598 _48296.
Proof. exact (@lem4115258 _48296 (@lem4115178 _48296 h1)). Qed.
Lemma lem4115260 (_48296 : int) (h1 : term621 _48296) : term599 _48296.
Proof. exact (@lem4115259 _48296 h1 term178). Qed.
Lemma lem4115261 (_48296 : int) : (term599 _48296) = ((term600 _48296) = term97).
Proof. exact (eq_refl (term599 _48296)). Qed.
Lemma lem4115262 (_48296 : int) (h1 : term621 _48296) : (term600 _48296) = term97.
Proof. exact (EQ_MP (@lem4115261 _48296) (@lem4115260 _48296 h1)). Qed.
Lemma lem4115263 (_48296 : int) : (term600 _48296) = (term601 _48296).
Proof. exact (@lem1982781 (real_of_int _48296) term178 term178). Qed.
Lemma lem4115265 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4115266 : term178 = term179.
Proof. exact (@lem4115265 term20). Qed.
Lemma lem4115268 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4115269 : term178 = term179.
Proof. exact (@lem4115268 term20). Qed.
Lemma lem4115270 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4115271 : term180 = term181.
Proof. exact (MK_COMB (@lem4115270) (@lem4115269)). Qed.
Lemma lem4115272 : term602 = term603.
Proof. exact (MK_COMB (@lem4115271) (@lem4115266)). Qed.
Lemma lem4115273 : term603 = term604.
Proof. exact (@lem1981613 term178 term178 term111 term111). Qed.
Lemma lem4115275 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115276 : term187 = term188.
Proof. exact (@lem4115275 term20 term20). Qed.
Lemma lem4115277 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115278 : term190 = term20.
Proof. exact (EQ_MP (@lem4115277) (@lem940073)). Qed.
Lemma lem4115279 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115280 : term188 = term111.
Proof. exact (MK_COMB (@lem4115279) (@lem4115278)). Qed.
Lemma lem4115281 : term187 = term111.
Proof. exact (TRANS (@lem4115276) (@lem4115280)). Qed.
Lemma lem4115283 (m : nat) (n : nat) : (term605 m n) = (term186 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem4115284 : term602 = term188.
Proof. exact (@lem4115283 term20 term20). Qed.
Lemma lem4115285 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115286 : term190 = term20.
Proof. exact (EQ_MP (@lem4115285) (@lem940073)). Qed.
Lemma lem4115287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115288 : term188 = term111.
Proof. exact (MK_COMB (@lem4115287) (@lem4115286)). Qed.
Lemma lem4115289 : term602 = term111.
Proof. exact (TRANS (@lem4115284) (@lem4115288)). Qed.
Lemma lem4115290 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4115291 : term606 = term607.
Proof. exact (MK_COMB (@lem4115290) (@lem4115289)). Qed.
Lemma lem4115292 : term604 = term200.
Proof. exact (MK_COMB (@lem4115291) (@lem4115281)). Qed.
Lemma lem4115293 : term603 = term200.
Proof. exact (TRANS (@lem4115273) (@lem4115292)). Qed.
Lemma lem4115294 : term602 = term200.
Proof. exact (TRANS (@lem4115272) (@lem4115293)). Qed.
Lemma lem4115296 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4115297 : term200 = term111.
Proof. exact (@lem4115296 term111). Qed.
Lemma lem4115298 : term602 = term111.
Proof. exact (TRANS (@lem4115294) (@lem4115297)). Qed.
Lemma lem4115301 (_48296 : int) : (term260 _48296) = (term260 _48296).
Proof. exact (eq_refl (term260 _48296)). Qed.
Lemma lem4115302 (_48296 : int) : (term601 _48296) = (term309 _48296).
Proof. exact (MK_COMB (@lem4115301 _48296) (@lem4115298)). Qed.
Lemma lem4115303 (_48296 : int) : (term600 _48296) = (term309 _48296).
Proof. exact (TRANS (@lem4115263 _48296) (@lem4115302 _48296)). Qed.
Lemma lem4115304 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem4115305 (_48296 : int) : (term608 _48296) = (term609 _48296).
Proof. exact (MK_COMB (@lem4115304) (@lem4115303 _48296)). Qed.
Lemma lem4115306 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4115307 (_48296 : int) : ((term600 _48296) = term97) = ((term309 _48296) = term97).
Proof. exact (MK_COMB (@lem4115305 _48296) (@lem4115306)). Qed.
Lemma lem4115308 (_48296 : int) (h1 : term621 _48296) : (term309 _48296) = term97.
Proof. exact (EQ_MP (@lem4115307 _48296) (@lem4115262 _48296 h1)). Qed.
Lemma lem4115309 (_48296 : int) (h1 : term621 _48296) : term610 _48296.
Proof. exact (conj (@lem4115308 _48296 h1) (@lem4115255 _48296 h1)). Qed.
Lemma lem4115311 (x : real) (y : real) : term564 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem4115312 (_48296 : int) : term611 _48296.
Proof. exact (@lem4115311 (term309 _48296) (term245 _48296)). Qed.
Lemma lem4115313 (_48296 : int) (h1 : term621 _48296) : term473 _48296.
Proof. exact (@lem4115312 _48296 (@lem4115309 _48296 h1)). Qed.
Lemma lem4115314 (_48296 : int) : (term474 _48296) = (term475 _48296).
Proof. exact (@lem1982753 (term281 _48296) (real_of_int _48296) term111 term241). Qed.
Lemma lem4115315 (_48296 : int) : (term476 _48296) = (term477 _48296).
Proof. exact (@lem1982713 term178 (real_of_int _48296)). Qed.
Lemma lem4115317 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4115318 : term111 = term200.
Proof. exact (@lem4115317 term20). Qed.
Lemma lem4115320 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4115321 : term178 = term179.
Proof. exact (@lem4115320 term20). Qed.
Lemma lem4115322 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4115323 : term478 = term479.
Proof. exact (MK_COMB (@lem4115322) (@lem4115321)). Qed.
Lemma lem4115324 : term480 = term481.
Proof. exact (MK_COMB (@lem4115323) (@lem4115318)). Qed.
Lemma lem4115325 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4115327 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115328 : term206 = term207.
Proof. exact (@lem4115327 (NUMERAL 0) term20). Qed.
Lemma lem4115329 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115330 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115331 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115330 h1) (fun h1 : term207 = True => @lem4115329)). Qed.
Lemma lem4115332 : term207 = True.
Proof. exact (EQ_MP (@lem4115331) (@lem4115329)). Qed.
Lemma lem4115333 : term206 = True.
Proof. exact (TRANS (@lem4115328) (@lem4115332)). Qed.
Lemma lem4115334 : True = term206.
Proof. exact (SYM (@lem4115333)). Qed.
Lemma lem4115335 : term206.
Proof. exact (EQ_MP (@lem4115334) (@lem0)). Qed.
Lemma lem4115336 : term483.
Proof. exact (@lem4115325 (@lem4115335)). Qed.
Lemma lem4115338 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115339 : term206 = term207.
Proof. exact (@lem4115338 (NUMERAL 0) term20). Qed.
Lemma lem4115340 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115341 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115342 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115341 h1) (fun h1 : term207 = True => @lem4115340)). Qed.
Lemma lem4115343 : term207 = True.
Proof. exact (EQ_MP (@lem4115342) (@lem4115340)). Qed.
Lemma lem4115344 : term206 = True.
Proof. exact (TRANS (@lem4115339) (@lem4115343)). Qed.
Lemma lem4115345 : True = term206.
Proof. exact (SYM (@lem4115344)). Qed.
Lemma lem4115346 : term206.
Proof. exact (EQ_MP (@lem4115345) (@lem0)). Qed.
Lemma lem4115347 : term484.
Proof. exact (@lem4115336 (@lem4115346)). Qed.
Lemma lem4115349 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115350 : term206 = term207.
Proof. exact (@lem4115349 (NUMERAL 0) term20). Qed.
Lemma lem4115351 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115352 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115353 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115352 h1) (fun h1 : term207 = True => @lem4115351)). Qed.
Lemma lem4115354 : term207 = True.
Proof. exact (EQ_MP (@lem4115353) (@lem4115351)). Qed.
Lemma lem4115355 : term206 = True.
Proof. exact (TRANS (@lem4115350) (@lem4115354)). Qed.
Lemma lem4115356 : True = term206.
Proof. exact (SYM (@lem4115355)). Qed.
Lemma lem4115357 : term206.
Proof. exact (EQ_MP (@lem4115356) (@lem0)). Qed.
Lemma lem4115358 : term485.
Proof. exact (@lem4115347 (@lem4115357)). Qed.
Lemma lem4115360 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115361 : term187 = term188.
Proof. exact (@lem4115360 term20 term20). Qed.
Lemma lem4115362 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115363 : term190 = term20.
Proof. exact (EQ_MP (@lem4115362) (@lem940073)). Qed.
Lemma lem4115364 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115365 : term188 = term111.
Proof. exact (MK_COMB (@lem4115364) (@lem4115363)). Qed.
Lemma lem4115366 : term187 = term111.
Proof. exact (TRANS (@lem4115361) (@lem4115365)). Qed.
Lemma lem4115368 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4115369 : term254 = term257.
Proof. exact (@lem4115368 term20 term20). Qed.
Lemma lem4115370 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115371 : term190 = term20.
Proof. exact (EQ_MP (@lem4115370) (@lem940073)). Qed.
Lemma lem4115372 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115373 : term188 = term111.
Proof. exact (MK_COMB (@lem4115372) (@lem4115371)). Qed.
Lemma lem4115374 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115375 : term257 = term178.
Proof. exact (MK_COMB (@lem4115374) (@lem4115373)). Qed.
Lemma lem4115376 : term254 = term178.
Proof. exact (TRANS (@lem4115369) (@lem4115375)). Qed.
Lemma lem4115377 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4115378 : term486 = term478.
Proof. exact (MK_COMB (@lem4115377) (@lem4115376)). Qed.
Lemma lem4115379 : term487 = term480.
Proof. exact (MK_COMB (@lem4115378) (@lem4115366)). Qed.
Lemma lem4115381 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4115382 : term480 = term97.
Proof. exact (@lem4115381 term20). Qed.
Lemma lem4115383 : term487 = term97.
Proof. exact (TRANS (@lem4115379) (@lem4115382)). Qed.
Lemma lem4115384 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4115385 : term489 = term291.
Proof. exact (MK_COMB (@lem4115384) (@lem4115383)). Qed.
Lemma lem4115386 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4115387 : term490 = term293.
Proof. exact (MK_COMB (@lem4115385) (@lem4115386)). Qed.
Lemma lem4115389 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4115390 : term293 = term97.
Proof. exact (@lem4115389 term20). Qed.
Lemma lem4115391 : term490 = term97.
Proof. exact (TRANS (@lem4115387) (@lem4115390)). Qed.
Lemma lem4115393 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115394 : term187 = term188.
Proof. exact (@lem4115393 term20 term20). Qed.
Lemma lem4115395 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115396 : term190 = term20.
Proof. exact (EQ_MP (@lem4115395) (@lem940073)). Qed.
Lemma lem4115397 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115398 : term188 = term111.
Proof. exact (MK_COMB (@lem4115397) (@lem4115396)). Qed.
Lemma lem4115399 : term187 = term111.
Proof. exact (TRANS (@lem4115394) (@lem4115398)). Qed.
Lemma lem4115400 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4115401 : term295 = term293.
Proof. exact (MK_COMB (@lem4115400) (@lem4115399)). Qed.
Lemma lem4115403 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4115404 : term293 = term97.
Proof. exact (@lem4115403 term20). Qed.
Lemma lem4115405 : term295 = term97.
Proof. exact (TRANS (@lem4115401) (@lem4115404)). Qed.
Lemma lem4115406 : term97 = term295.
Proof. exact (SYM (@lem4115405)). Qed.
Lemma lem4115407 : term490 = term295.
Proof. exact (TRANS (@lem4115391) (@lem4115406)). Qed.
Lemma lem4115408 : term481 = term175.
Proof. exact (@lem4115358 (@lem4115407)). Qed.
Lemma lem4115409 : term480 = term175.
Proof. exact (TRANS (@lem4115324) (@lem4115408)). Qed.
Lemma lem4115411 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4115412 : term175 = term97.
Proof. exact (@lem4115411 term97). Qed.
Lemma lem4115413 : term480 = term97.
Proof. exact (TRANS (@lem4115409) (@lem4115412)). Qed.
Lemma lem4115414 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4115415 : term491 = term291.
Proof. exact (MK_COMB (@lem4115414) (@lem4115413)). Qed.
Lemma lem4115416 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4115417 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4115415) (@lem4115416 _48296)). Qed.
Lemma lem4115418 (_48296 : int) : (term476 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4115315 _48296) (@lem4115417 _48296)). Qed.
Lemma lem4115419 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4115420 (_48296 : int) : (term476 _48296) = term97.
Proof. exact (TRANS (@lem4115418 _48296) (@lem4115419 _48296)). Qed.
Lemma lem4115421 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4115422 (_48296 : int) : (term493 _48296) = term139.
Proof. exact (MK_COMB (@lem4115421) (@lem4115420 _48296)). Qed.
Lemma lem4115424 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4115425 : term241 = term244.
Proof. exact (@lem4115424 term218). Qed.
Lemma lem4115427 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4115428 : term111 = term200.
Proof. exact (@lem4115427 term20). Qed.
Lemma lem4115429 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4115430 : term113 = term201.
Proof. exact (MK_COMB (@lem4115429) (@lem4115428)). Qed.
Lemma lem4115431 : term494 = term495.
Proof. exact (MK_COMB (@lem4115430) (@lem4115425)). Qed.
Lemma lem4115432 : term496.
Proof. exact (@lem1981473 term111 term111 term241 term111 term178 term111). Qed.
Lemma lem4115434 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115435 : term206 = term207.
Proof. exact (@lem4115434 (NUMERAL 0) term20). Qed.
Lemma lem4115436 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115437 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115438 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115437 h1) (fun h1 : term207 = True => @lem4115436)). Qed.
Lemma lem4115439 : term207 = True.
Proof. exact (EQ_MP (@lem4115438) (@lem4115436)). Qed.
Lemma lem4115440 : term206 = True.
Proof. exact (TRANS (@lem4115435) (@lem4115439)). Qed.
Lemma lem4115441 : True = term206.
Proof. exact (SYM (@lem4115440)). Qed.
Lemma lem4115442 : term206.
Proof. exact (EQ_MP (@lem4115441) (@lem0)). Qed.
Lemma lem4115443 : term497.
Proof. exact (@lem4115432 (@lem4115442)). Qed.
Lemma lem4115445 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115446 : term206 = term207.
Proof. exact (@lem4115445 (NUMERAL 0) term20). Qed.
Lemma lem4115447 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115448 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115449 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115448 h1) (fun h1 : term207 = True => @lem4115447)). Qed.
Lemma lem4115450 : term207 = True.
Proof. exact (EQ_MP (@lem4115449) (@lem4115447)). Qed.
Lemma lem4115451 : term206 = True.
Proof. exact (TRANS (@lem4115446) (@lem4115450)). Qed.
Lemma lem4115452 : True = term206.
Proof. exact (SYM (@lem4115451)). Qed.
Lemma lem4115453 : term206.
Proof. exact (EQ_MP (@lem4115452) (@lem0)). Qed.
Lemma lem4115454 : term498.
Proof. exact (@lem4115443 (@lem4115453)). Qed.
Lemma lem4115456 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115457 : term206 = term207.
Proof. exact (@lem4115456 (NUMERAL 0) term20). Qed.
Lemma lem4115458 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115459 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115460 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115459 h1) (fun h1 : term207 = True => @lem4115458)). Qed.
Lemma lem4115461 : term207 = True.
Proof. exact (EQ_MP (@lem4115460) (@lem4115458)). Qed.
Lemma lem4115462 : term206 = True.
Proof. exact (TRANS (@lem4115457) (@lem4115461)). Qed.
Lemma lem4115463 : True = term206.
Proof. exact (SYM (@lem4115462)). Qed.
Lemma lem4115464 : term206.
Proof. exact (EQ_MP (@lem4115463) (@lem0)). Qed.
Lemma lem4115465 : term499.
Proof. exact (@lem4115454 (@lem4115464)). Qed.
Lemma lem4115467 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4115468 : term500 = term501.
Proof. exact (@lem4115467 term218 term20). Qed.
Lemma lem4115469 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4115470 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4115471 : term225 = term218.
Proof. exact (EQ_MP (@lem4115470) (@lem4115469)). Qed.
Lemma lem4115472 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115473 : term223 = term204.
Proof. exact (MK_COMB (@lem4115472) (@lem4115471)). Qed.
Lemma lem4115474 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115475 : term501 = term241.
Proof. exact (MK_COMB (@lem4115474) (@lem4115473)). Qed.
Lemma lem4115476 : term500 = term241.
Proof. exact (TRANS (@lem4115468) (@lem4115475)). Qed.
Lemma lem4115478 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115479 : term187 = term188.
Proof. exact (@lem4115478 term20 term20). Qed.
Lemma lem4115480 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115481 : term190 = term20.
Proof. exact (EQ_MP (@lem4115480) (@lem940073)). Qed.
Lemma lem4115482 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115483 : term188 = term111.
Proof. exact (MK_COMB (@lem4115482) (@lem4115481)). Qed.
Lemma lem4115484 : term187 = term111.
Proof. exact (TRANS (@lem4115479) (@lem4115483)). Qed.
Lemma lem4115485 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4115486 : term212 = term113.
Proof. exact (MK_COMB (@lem4115485) (@lem4115484)). Qed.
Lemma lem4115487 : term502 = term494.
Proof. exact (MK_COMB (@lem4115486) (@lem4115476)). Qed.
Lemma lem4115490 : term503 = term178.
Proof. exact (@lem1367771 term20 term20). Qed.
Lemma lem4115491 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem4115492 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem4115493 : term217 = term218.
Proof. exact (EQ_MP (@lem4115492) (@lem4115491)). Qed.
Lemma lem4115494 : term218 = term217.
Proof. exact (SYM (@lem4115493)). Qed.
Lemma lem4115495 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115496 : term204 = term214.
Proof. exact (MK_COMB (@lem4115495) (@lem4115494)). Qed.
Lemma lem4115497 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115498 : term241 = term504.
Proof. exact (MK_COMB (@lem4115497) (@lem4115496)). Qed.
Lemma lem4115499 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem4115500 : term494 = term503.
Proof. exact (MK_COMB (@lem4115499) (@lem4115498)). Qed.
Lemma lem4115501 : term494 = term178.
Proof. exact (TRANS (@lem4115500) (@lem4115490)). Qed.
Lemma lem4115502 : term502 = term178.
Proof. exact (TRANS (@lem4115487) (@lem4115501)). Qed.
Lemma lem4115503 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4115504 : term505 = term180.
Proof. exact (MK_COMB (@lem4115503) (@lem4115502)). Qed.
Lemma lem4115505 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4115506 : term506 = term254.
Proof. exact (MK_COMB (@lem4115504) (@lem4115505)). Qed.
Lemma lem4115508 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4115509 : term254 = term257.
Proof. exact (@lem4115508 term20 term20). Qed.
Lemma lem4115510 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115511 : term190 = term20.
Proof. exact (EQ_MP (@lem4115510) (@lem940073)). Qed.
Lemma lem4115512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115513 : term188 = term111.
Proof. exact (MK_COMB (@lem4115512) (@lem4115511)). Qed.
Lemma lem4115514 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115515 : term257 = term178.
Proof. exact (MK_COMB (@lem4115514) (@lem4115513)). Qed.
Lemma lem4115516 : term254 = term178.
Proof. exact (TRANS (@lem4115509) (@lem4115515)). Qed.
Lemma lem4115517 : term506 = term178.
Proof. exact (TRANS (@lem4115506) (@lem4115516)). Qed.
Lemma lem4115519 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115520 : term187 = term188.
Proof. exact (@lem4115519 term20 term20). Qed.
Lemma lem4115521 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115522 : term190 = term20.
Proof. exact (EQ_MP (@lem4115521) (@lem940073)). Qed.
Lemma lem4115523 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115524 : term188 = term111.
Proof. exact (MK_COMB (@lem4115523) (@lem4115522)). Qed.
Lemma lem4115525 : term187 = term111.
Proof. exact (TRANS (@lem4115520) (@lem4115524)). Qed.
Lemma lem4115526 : term180 = term180.
Proof. exact (eq_refl term180). Qed.
Lemma lem4115527 : term507 = term254.
Proof. exact (MK_COMB (@lem4115526) (@lem4115525)). Qed.
Lemma lem4115529 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4115530 : term254 = term257.
Proof. exact (@lem4115529 term20 term20). Qed.
Lemma lem4115531 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115532 : term190 = term20.
Proof. exact (EQ_MP (@lem4115531) (@lem940073)). Qed.
Lemma lem4115533 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115534 : term188 = term111.
Proof. exact (MK_COMB (@lem4115533) (@lem4115532)). Qed.
Lemma lem4115535 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115536 : term257 = term178.
Proof. exact (MK_COMB (@lem4115535) (@lem4115534)). Qed.
Lemma lem4115537 : term254 = term178.
Proof. exact (TRANS (@lem4115530) (@lem4115536)). Qed.
Lemma lem4115538 : term507 = term178.
Proof. exact (TRANS (@lem4115527) (@lem4115537)). Qed.
Lemma lem4115539 : term178 = term507.
Proof. exact (SYM (@lem4115538)). Qed.
Lemma lem4115540 : term506 = term507.
Proof. exact (TRANS (@lem4115517) (@lem4115539)). Qed.
Lemma lem4115541 : term495 = term179.
Proof. exact (@lem4115465 (@lem4115540)). Qed.
Lemma lem4115542 : term494 = term179.
Proof. exact (TRANS (@lem4115431) (@lem4115541)). Qed.
Lemma lem4115544 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4115545 : term179 = term178.
Proof. exact (@lem4115544 term178). Qed.
Lemma lem4115546 : term494 = term178.
Proof. exact (TRANS (@lem4115542) (@lem4115545)). Qed.
Lemma lem4115547 (_48296 : int) : (term475 _48296) = term508.
Proof. exact (MK_COMB (@lem4115422 _48296) (@lem4115546)). Qed.
Lemma lem4115548 (_48296 : int) : (term474 _48296) = term508.
Proof. exact (TRANS (@lem4115314 _48296) (@lem4115547 _48296)). Qed.
Lemma lem4115549 : term508 = term178.
Proof. exact (@lem1982721 term178). Qed.
Lemma lem4115550 (_48296 : int) : (term474 _48296) = term178.
Proof. exact (TRANS (@lem4115548 _48296) (@lem4115549)). Qed.
Lemma lem4115551 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4115552 (_48296 : int) : (term509 _48296) = term510.
Proof. exact (MK_COMB (@lem4115551) (@lem4115550 _48296)). Qed.
Lemma lem4115553 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4115554 (_48296 : int) : (term473 _48296) = term511.
Proof. exact (MK_COMB (@lem4115552 _48296) (@lem4115553)). Qed.
Lemma lem4115555 (_48296 : int) (h1 : term621 _48296) : term511.
Proof. exact (EQ_MP (@lem4115554 _48296) (@lem4115313 _48296 h1)). Qed.
Lemma lem4115557 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4115558 : term511 = term512.
Proof. exact (@lem4115557 term97 term178). Qed.
Lemma lem4115560 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4115561 : term178 = term179.
Proof. exact (@lem4115560 term20). Qed.
Lemma lem4115563 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4115564 : term97 = term175.
Proof. exact (@lem4115563 (NUMERAL 0)). Qed.
Lemma lem4115565 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4115566 : term99 = term513.
Proof. exact (MK_COMB (@lem4115565) (@lem4115564)). Qed.
Lemma lem4115567 : term512 = term514.
Proof. exact (MK_COMB (@lem4115566) (@lem4115561)). Qed.
Lemma lem4115568 : term515.
Proof. exact (@lem1980026 term97 term111 term178 term111). Qed.
Lemma lem4115570 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115571 : term206 = term207.
Proof. exact (@lem4115570 (NUMERAL 0) term20). Qed.
Lemma lem4115572 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115573 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115574 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115573 h1) (fun h1 : term207 = True => @lem4115572)). Qed.
Lemma lem4115575 : term207 = True.
Proof. exact (EQ_MP (@lem4115574) (@lem4115572)). Qed.
Lemma lem4115576 : term206 = True.
Proof. exact (TRANS (@lem4115571) (@lem4115575)). Qed.
Lemma lem4115577 : True = term206.
Proof. exact (SYM (@lem4115576)). Qed.
Lemma lem4115578 : term206.
Proof. exact (EQ_MP (@lem4115577) (@lem0)). Qed.
Lemma lem4115579 : term516.
Proof. exact (@lem4115568 (@lem4115578)). Qed.
Lemma lem4115581 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115582 : term206 = term207.
Proof. exact (@lem4115581 (NUMERAL 0) term20). Qed.
Lemma lem4115583 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115584 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115585 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115584 h1) (fun h1 : term207 = True => @lem4115583)). Qed.
Lemma lem4115586 : term207 = True.
Proof. exact (EQ_MP (@lem4115585) (@lem4115583)). Qed.
Lemma lem4115587 : term206 = True.
Proof. exact (TRANS (@lem4115582) (@lem4115586)). Qed.
Lemma lem4115588 : True = term206.
Proof. exact (SYM (@lem4115587)). Qed.
Lemma lem4115589 : term206.
Proof. exact (EQ_MP (@lem4115588) (@lem0)). Qed.
Lemma lem4115590 : term514 = term517.
Proof. exact (@lem4115579 (@lem4115589)). Qed.
Lemma lem4115592 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4115593 : term254 = term257.
Proof. exact (@lem4115592 term20 term20). Qed.
Lemma lem4115594 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115595 : term190 = term20.
Proof. exact (EQ_MP (@lem4115594) (@lem940073)). Qed.
Lemma lem4115596 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115597 : term188 = term111.
Proof. exact (MK_COMB (@lem4115596) (@lem4115595)). Qed.
Lemma lem4115598 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115599 : term257 = term178.
Proof. exact (MK_COMB (@lem4115598) (@lem4115597)). Qed.
Lemma lem4115600 : term254 = term178.
Proof. exact (TRANS (@lem4115593) (@lem4115599)). Qed.
Lemma lem4115602 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4115603 : term293 = term97.
Proof. exact (@lem4115602 term20). Qed.
Lemma lem4115604 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4115605 : term518 = term99.
Proof. exact (MK_COMB (@lem4115604) (@lem4115603)). Qed.
Lemma lem4115606 : term517 = term512.
Proof. exact (MK_COMB (@lem4115605) (@lem4115600)). Qed.
Lemma lem4115608 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4115609 : term512 = term521.
Proof. exact (@lem4115608 (NUMERAL 0) term20). Qed.
Lemma lem4115610 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115611 (h1 : term208 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4115612 : (term208 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115611 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem4115610)). Qed.
Lemma lem4115613 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4115612) (@lem4115610)). Qed.
Lemma lem4115614 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4115615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4115616 : term522 = (and True).
Proof. exact (MK_COMB (@lem4115615) (@lem4115614)). Qed.
Lemma lem4115617 : term521 = (True /\ False).
Proof. exact (MK_COMB (@lem4115616) (@lem4115613)). Qed.
Lemma lem4115619 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4115620 : term521 = False.
Proof. exact (TRANS (@lem4115617) (@lem4115619)). Qed.
Lemma lem4115621 : term512 = False.
Proof. exact (TRANS (@lem4115609) (@lem4115620)). Qed.
Lemma lem4115622 : term517 = False.
Proof. exact (TRANS (@lem4115606) (@lem4115621)). Qed.
Lemma lem4115623 : term514 = False.
Proof. exact (TRANS (@lem4115590) (@lem4115622)). Qed.
Lemma lem4115624 : term512 = False.
Proof. exact (TRANS (@lem4115567) (@lem4115623)). Qed.
Lemma lem4115625 : term511 = False.
Proof. exact (TRANS (@lem4115558) (@lem4115624)). Qed.
Lemma lem4115626 (_48296 : int) (h1 : term621 _48296) : False.
Proof. exact (EQ_MP (@lem4115625) (@lem4115555 _48296 h1)). Qed.
Lemma lem4115627 (_48296 : int) (h1 : term622 _48296) : term622 _48296.
Proof. exact (h1). Qed.
Lemma lem4115628 (_48296 : int) (h1 : term622 _48296) : term398 _48296.
Proof. exact (proj2 (@lem4115627 _48296 h1)). Qed.
Lemma lem4115630 (_48296 : int) (h1 : term622 _48296) : (term270 _48296) = term97.
Proof. exact (proj2 (@lem4115628 _48296 h1)). Qed.
Lemma lem4115631 (_48296 : int) (h1 : term622 _48296) : term344 _48296.
Proof. exact (proj1 (@lem4115628 _48296 h1)). Qed.
Lemma lem4115632 (_48296 : int) (h1 : term622 _48296) : term248 _48296.
Proof. exact (proj2 (@lem4115631 _48296 h1)). Qed.
Lemma lem4115635 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4115636 : term451 = term206.
Proof. exact (@lem4115635 term97 term111). Qed.
Lemma lem4115638 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4115639 : term111 = term200.
Proof. exact (@lem4115638 term20). Qed.
Lemma lem4115641 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4115642 : term97 = term175.
Proof. exact (@lem4115641 (NUMERAL 0)). Qed.
Lemma lem4115643 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4115644 : term452 = term453.
Proof. exact (MK_COMB (@lem4115643) (@lem4115642)). Qed.
Lemma lem4115645 : term206 = term454.
Proof. exact (MK_COMB (@lem4115644) (@lem4115639)). Qed.
Lemma lem4115646 : term455.
Proof. exact (@lem1980255 term97 term111 term111 term111). Qed.
Lemma lem4115648 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115649 : term206 = term207.
Proof. exact (@lem4115648 (NUMERAL 0) term20). Qed.
Lemma lem4115650 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115651 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115652 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115651 h1) (fun h1 : term207 = True => @lem4115650)). Qed.
Lemma lem4115653 : term207 = True.
Proof. exact (EQ_MP (@lem4115652) (@lem4115650)). Qed.
Lemma lem4115654 : term206 = True.
Proof. exact (TRANS (@lem4115649) (@lem4115653)). Qed.
Lemma lem4115655 : True = term206.
Proof. exact (SYM (@lem4115654)). Qed.
Lemma lem4115656 : term206.
Proof. exact (EQ_MP (@lem4115655) (@lem0)). Qed.
Lemma lem4115657 : term456.
Proof. exact (@lem4115646 (@lem4115656)). Qed.
Lemma lem4115659 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115660 : term206 = term207.
Proof. exact (@lem4115659 (NUMERAL 0) term20). Qed.
Lemma lem4115661 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115662 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115663 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115662 h1) (fun h1 : term207 = True => @lem4115661)). Qed.
Lemma lem4115664 : term207 = True.
Proof. exact (EQ_MP (@lem4115663) (@lem4115661)). Qed.
Lemma lem4115665 : term206 = True.
Proof. exact (TRANS (@lem4115660) (@lem4115664)). Qed.
Lemma lem4115666 : True = term206.
Proof. exact (SYM (@lem4115665)). Qed.
Lemma lem4115667 : term206.
Proof. exact (EQ_MP (@lem4115666) (@lem0)). Qed.
Lemma lem4115668 : term454 = term457.
Proof. exact (@lem4115657 (@lem4115667)). Qed.
Lemma lem4115670 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115671 : term187 = term188.
Proof. exact (@lem4115670 term20 term20). Qed.
Lemma lem4115672 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115673 : term190 = term20.
Proof. exact (EQ_MP (@lem4115672) (@lem940073)). Qed.
Lemma lem4115674 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115675 : term188 = term111.
Proof. exact (MK_COMB (@lem4115674) (@lem4115673)). Qed.
Lemma lem4115676 : term187 = term111.
Proof. exact (TRANS (@lem4115671) (@lem4115675)). Qed.
Lemma lem4115678 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4115679 : term293 = term97.
Proof. exact (@lem4115678 term20). Qed.
Lemma lem4115680 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4115681 : term458 = term452.
Proof. exact (MK_COMB (@lem4115680) (@lem4115679)). Qed.
Lemma lem4115682 : term457 = term206.
Proof. exact (MK_COMB (@lem4115681) (@lem4115676)). Qed.
Lemma lem4115684 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115685 : term206 = term207.
Proof. exact (@lem4115684 (NUMERAL 0) term20). Qed.
Lemma lem4115686 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115687 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115688 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115687 h1) (fun h1 : term207 = True => @lem4115686)). Qed.
Lemma lem4115689 : term207 = True.
Proof. exact (EQ_MP (@lem4115688) (@lem4115686)). Qed.
Lemma lem4115690 : term206 = True.
Proof. exact (TRANS (@lem4115685) (@lem4115689)). Qed.
Lemma lem4115691 : term457 = True.
Proof. exact (TRANS (@lem4115682) (@lem4115690)). Qed.
Lemma lem4115692 : term454 = True.
Proof. exact (TRANS (@lem4115668) (@lem4115691)). Qed.
Lemma lem4115693 : term206 = True.
Proof. exact (TRANS (@lem4115645) (@lem4115692)). Qed.
Lemma lem4115694 : term451 = True.
Proof. exact (TRANS (@lem4115636) (@lem4115693)). Qed.
Lemma lem4115695 : True = term451.
Proof. exact (SYM (@lem4115694)). Qed.
Lemma lem4115696 : term451.
Proof. exact (EQ_MP (@lem4115695) (@lem0)). Qed.
Lemma lem4115697 (_48296 : int) (h1 : term622 _48296) : term459 _48296.
Proof. exact (conj (@lem4115696) (@lem4115632 _48296 h1)). Qed.
Lemma lem4115699 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4115700 (_48296 : int) : term461 _48296.
Proof. exact (@lem4115699 term111 (term245 _48296)). Qed.
Lemma lem4115701 (_48296 : int) (h1 : term622 _48296) : term462 _48296.
Proof. exact (@lem4115700 _48296 (@lem4115697 _48296 h1)). Qed.
Lemma lem4115702 (_48296 : int) : (term463 _48296) = (term245 _48296).
Proof. exact (@lem1982733 (term245 _48296)). Qed.
Lemma lem4115703 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4115704 (_48296 : int) : (term464 _48296) = (term247 _48296).
Proof. exact (MK_COMB (@lem4115703) (@lem4115702 _48296)). Qed.
Lemma lem4115705 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4115706 (_48296 : int) : (term462 _48296) = (term248 _48296).
Proof. exact (MK_COMB (@lem4115704 _48296) (@lem4115705)). Qed.
Lemma lem4115707 (_48296 : int) (h1 : term622 _48296) : term248 _48296.
Proof. exact (EQ_MP (@lem4115706 _48296) (@lem4115701 _48296 h1)). Qed.
Lemma lem4115709 (y : real) : term559 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem4115710 (_48296 : int) : term597 _48296.
Proof. exact (@lem4115709 (term270 _48296)). Qed.
Lemma lem4115711 (_48296 : int) (h1 : term622 _48296) : term598 _48296.
Proof. exact (@lem4115710 _48296 (@lem4115630 _48296 h1)). Qed.
Lemma lem4115712 (_48296 : int) (h1 : term622 _48296) : term599 _48296.
Proof. exact (@lem4115711 _48296 h1 term178). Qed.
Lemma lem4115713 (_48296 : int) : (term599 _48296) = ((term600 _48296) = term97).
Proof. exact (eq_refl (term599 _48296)). Qed.
Lemma lem4115714 (_48296 : int) (h1 : term622 _48296) : (term600 _48296) = term97.
Proof. exact (EQ_MP (@lem4115713 _48296) (@lem4115712 _48296 h1)). Qed.
Lemma lem4115715 (_48296 : int) : (term600 _48296) = (term601 _48296).
Proof. exact (@lem1982781 (real_of_int _48296) term178 term178). Qed.
Lemma lem4115717 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4115718 : term178 = term179.
Proof. exact (@lem4115717 term20). Qed.
Lemma lem4115720 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4115721 : term178 = term179.
Proof. exact (@lem4115720 term20). Qed.
Lemma lem4115722 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4115723 : term180 = term181.
Proof. exact (MK_COMB (@lem4115722) (@lem4115721)). Qed.
Lemma lem4115724 : term602 = term603.
Proof. exact (MK_COMB (@lem4115723) (@lem4115718)). Qed.
Lemma lem4115725 : term603 = term604.
Proof. exact (@lem1981613 term178 term178 term111 term111). Qed.
Lemma lem4115727 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115728 : term187 = term188.
Proof. exact (@lem4115727 term20 term20). Qed.
Lemma lem4115729 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115730 : term190 = term20.
Proof. exact (EQ_MP (@lem4115729) (@lem940073)). Qed.
Lemma lem4115731 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115732 : term188 = term111.
Proof. exact (MK_COMB (@lem4115731) (@lem4115730)). Qed.
Lemma lem4115733 : term187 = term111.
Proof. exact (TRANS (@lem4115728) (@lem4115732)). Qed.
Lemma lem4115735 (m : nat) (n : nat) : (term605 m n) = (term186 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem4115736 : term602 = term188.
Proof. exact (@lem4115735 term20 term20). Qed.
Lemma lem4115737 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115738 : term190 = term20.
Proof. exact (EQ_MP (@lem4115737) (@lem940073)). Qed.
Lemma lem4115739 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115740 : term188 = term111.
Proof. exact (MK_COMB (@lem4115739) (@lem4115738)). Qed.
Lemma lem4115741 : term602 = term111.
Proof. exact (TRANS (@lem4115736) (@lem4115740)). Qed.
Lemma lem4115742 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4115743 : term606 = term607.
Proof. exact (MK_COMB (@lem4115742) (@lem4115741)). Qed.
Lemma lem4115744 : term604 = term200.
Proof. exact (MK_COMB (@lem4115743) (@lem4115733)). Qed.
Lemma lem4115745 : term603 = term200.
Proof. exact (TRANS (@lem4115725) (@lem4115744)). Qed.
Lemma lem4115746 : term602 = term200.
Proof. exact (TRANS (@lem4115724) (@lem4115745)). Qed.
Lemma lem4115748 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4115749 : term200 = term111.
Proof. exact (@lem4115748 term111). Qed.
Lemma lem4115750 : term602 = term111.
Proof. exact (TRANS (@lem4115746) (@lem4115749)). Qed.
Lemma lem4115753 (_48296 : int) : (term260 _48296) = (term260 _48296).
Proof. exact (eq_refl (term260 _48296)). Qed.
Lemma lem4115754 (_48296 : int) : (term601 _48296) = (term309 _48296).
Proof. exact (MK_COMB (@lem4115753 _48296) (@lem4115750)). Qed.
Lemma lem4115755 (_48296 : int) : (term600 _48296) = (term309 _48296).
Proof. exact (TRANS (@lem4115715 _48296) (@lem4115754 _48296)). Qed.
Lemma lem4115756 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem4115757 (_48296 : int) : (term608 _48296) = (term609 _48296).
Proof. exact (MK_COMB (@lem4115756) (@lem4115755 _48296)). Qed.
Lemma lem4115758 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4115759 (_48296 : int) : ((term600 _48296) = term97) = ((term309 _48296) = term97).
Proof. exact (MK_COMB (@lem4115757 _48296) (@lem4115758)). Qed.
Lemma lem4115760 (_48296 : int) (h1 : term622 _48296) : (term309 _48296) = term97.
Proof. exact (EQ_MP (@lem4115759 _48296) (@lem4115714 _48296 h1)). Qed.
Lemma lem4115761 (_48296 : int) (h1 : term622 _48296) : term610 _48296.
Proof. exact (conj (@lem4115760 _48296 h1) (@lem4115707 _48296 h1)). Qed.
Lemma lem4115763 (x : real) (y : real) : term564 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem4115764 (_48296 : int) : term611 _48296.
Proof. exact (@lem4115763 (term309 _48296) (term245 _48296)). Qed.
Lemma lem4115765 (_48296 : int) (h1 : term622 _48296) : term473 _48296.
Proof. exact (@lem4115764 _48296 (@lem4115761 _48296 h1)). Qed.
Lemma lem4115766 (_48296 : int) : (term474 _48296) = (term475 _48296).
Proof. exact (@lem1982753 (term281 _48296) (real_of_int _48296) term111 term241). Qed.
Lemma lem4115767 (_48296 : int) : (term476 _48296) = (term477 _48296).
Proof. exact (@lem1982713 term178 (real_of_int _48296)). Qed.
Lemma lem4115769 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4115770 : term111 = term200.
Proof. exact (@lem4115769 term20). Qed.
Lemma lem4115772 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4115773 : term178 = term179.
Proof. exact (@lem4115772 term20). Qed.
Lemma lem4115774 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4115775 : term478 = term479.
Proof. exact (MK_COMB (@lem4115774) (@lem4115773)). Qed.
Lemma lem4115776 : term480 = term481.
Proof. exact (MK_COMB (@lem4115775) (@lem4115770)). Qed.
Lemma lem4115777 : term482.
Proof. exact (@lem1981473 term178 term111 term111 term111 term97 term111). Qed.
Lemma lem4115779 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115780 : term206 = term207.
Proof. exact (@lem4115779 (NUMERAL 0) term20). Qed.
Lemma lem4115781 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115782 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115783 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115782 h1) (fun h1 : term207 = True => @lem4115781)). Qed.
Lemma lem4115784 : term207 = True.
Proof. exact (EQ_MP (@lem4115783) (@lem4115781)). Qed.
Lemma lem4115785 : term206 = True.
Proof. exact (TRANS (@lem4115780) (@lem4115784)). Qed.
Lemma lem4115786 : True = term206.
Proof. exact (SYM (@lem4115785)). Qed.
Lemma lem4115787 : term206.
Proof. exact (EQ_MP (@lem4115786) (@lem0)). Qed.
Lemma lem4115788 : term483.
Proof. exact (@lem4115777 (@lem4115787)). Qed.
Lemma lem4115790 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115791 : term206 = term207.
Proof. exact (@lem4115790 (NUMERAL 0) term20). Qed.
Lemma lem4115792 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115793 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115794 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115793 h1) (fun h1 : term207 = True => @lem4115792)). Qed.
Lemma lem4115795 : term207 = True.
Proof. exact (EQ_MP (@lem4115794) (@lem4115792)). Qed.
Lemma lem4115796 : term206 = True.
Proof. exact (TRANS (@lem4115791) (@lem4115795)). Qed.
Lemma lem4115797 : True = term206.
Proof. exact (SYM (@lem4115796)). Qed.
Lemma lem4115798 : term206.
Proof. exact (EQ_MP (@lem4115797) (@lem0)). Qed.
Lemma lem4115799 : term484.
Proof. exact (@lem4115788 (@lem4115798)). Qed.
Lemma lem4115801 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115802 : term206 = term207.
Proof. exact (@lem4115801 (NUMERAL 0) term20). Qed.
Lemma lem4115803 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115804 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115805 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115804 h1) (fun h1 : term207 = True => @lem4115803)). Qed.
Lemma lem4115806 : term207 = True.
Proof. exact (EQ_MP (@lem4115805) (@lem4115803)). Qed.
Lemma lem4115807 : term206 = True.
Proof. exact (TRANS (@lem4115802) (@lem4115806)). Qed.
Lemma lem4115808 : True = term206.
Proof. exact (SYM (@lem4115807)). Qed.
Lemma lem4115809 : term206.
Proof. exact (EQ_MP (@lem4115808) (@lem0)). Qed.
Lemma lem4115810 : term485.
Proof. exact (@lem4115799 (@lem4115809)). Qed.
Lemma lem4115812 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115813 : term187 = term188.
Proof. exact (@lem4115812 term20 term20). Qed.
Lemma lem4115814 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115815 : term190 = term20.
Proof. exact (EQ_MP (@lem4115814) (@lem940073)). Qed.
Lemma lem4115816 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115817 : term188 = term111.
Proof. exact (MK_COMB (@lem4115816) (@lem4115815)). Qed.
Lemma lem4115818 : term187 = term111.
Proof. exact (TRANS (@lem4115813) (@lem4115817)). Qed.
Lemma lem4115820 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4115821 : term254 = term257.
Proof. exact (@lem4115820 term20 term20). Qed.
Lemma lem4115822 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115823 : term190 = term20.
Proof. exact (EQ_MP (@lem4115822) (@lem940073)). Qed.
Lemma lem4115824 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115825 : term188 = term111.
Proof. exact (MK_COMB (@lem4115824) (@lem4115823)). Qed.
Lemma lem4115826 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115827 : term257 = term178.
Proof. exact (MK_COMB (@lem4115826) (@lem4115825)). Qed.
Lemma lem4115828 : term254 = term178.
Proof. exact (TRANS (@lem4115821) (@lem4115827)). Qed.
Lemma lem4115829 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4115830 : term486 = term478.
Proof. exact (MK_COMB (@lem4115829) (@lem4115828)). Qed.
Lemma lem4115831 : term487 = term480.
Proof. exact (MK_COMB (@lem4115830) (@lem4115818)). Qed.
Lemma lem4115833 (m : nat) : (term488 m) = term97.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4115834 : term480 = term97.
Proof. exact (@lem4115833 term20). Qed.
Lemma lem4115835 : term487 = term97.
Proof. exact (TRANS (@lem4115831) (@lem4115834)). Qed.
Lemma lem4115836 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4115837 : term489 = term291.
Proof. exact (MK_COMB (@lem4115836) (@lem4115835)). Qed.
Lemma lem4115838 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4115839 : term490 = term293.
Proof. exact (MK_COMB (@lem4115837) (@lem4115838)). Qed.
Lemma lem4115841 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4115842 : term293 = term97.
Proof. exact (@lem4115841 term20). Qed.
Lemma lem4115843 : term490 = term97.
Proof. exact (TRANS (@lem4115839) (@lem4115842)). Qed.
Lemma lem4115845 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115846 : term187 = term188.
Proof. exact (@lem4115845 term20 term20). Qed.
Lemma lem4115847 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115848 : term190 = term20.
Proof. exact (EQ_MP (@lem4115847) (@lem940073)). Qed.
Lemma lem4115849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115850 : term188 = term111.
Proof. exact (MK_COMB (@lem4115849) (@lem4115848)). Qed.
Lemma lem4115851 : term187 = term111.
Proof. exact (TRANS (@lem4115846) (@lem4115850)). Qed.
Lemma lem4115852 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4115853 : term295 = term293.
Proof. exact (MK_COMB (@lem4115852) (@lem4115851)). Qed.
Lemma lem4115855 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4115856 : term293 = term97.
Proof. exact (@lem4115855 term20). Qed.
Lemma lem4115857 : term295 = term97.
Proof. exact (TRANS (@lem4115853) (@lem4115856)). Qed.
Lemma lem4115858 : term97 = term295.
Proof. exact (SYM (@lem4115857)). Qed.
Lemma lem4115859 : term490 = term295.
Proof. exact (TRANS (@lem4115843) (@lem4115858)). Qed.
Lemma lem4115860 : term481 = term175.
Proof. exact (@lem4115810 (@lem4115859)). Qed.
Lemma lem4115861 : term480 = term175.
Proof. exact (TRANS (@lem4115776) (@lem4115860)). Qed.
Lemma lem4115863 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4115864 : term175 = term97.
Proof. exact (@lem4115863 term97). Qed.
Lemma lem4115865 : term480 = term97.
Proof. exact (TRANS (@lem4115861) (@lem4115864)). Qed.
Lemma lem4115866 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4115867 : term491 = term291.
Proof. exact (MK_COMB (@lem4115866) (@lem4115865)). Qed.
Lemma lem4115868 (_48296 : int) : (real_of_int _48296) = (real_of_int _48296).
Proof. exact (eq_refl (real_of_int _48296)). Qed.
Lemma lem4115869 (_48296 : int) : (term477 _48296) = (term492 _48296).
Proof. exact (MK_COMB (@lem4115867) (@lem4115868 _48296)). Qed.
Lemma lem4115870 (_48296 : int) : (term476 _48296) = (term492 _48296).
Proof. exact (TRANS (@lem4115767 _48296) (@lem4115869 _48296)). Qed.
Lemma lem4115871 (_48296 : int) : (term492 _48296) = term97.
Proof. exact (@lem1982719 (real_of_int _48296)). Qed.
Lemma lem4115872 (_48296 : int) : (term476 _48296) = term97.
Proof. exact (TRANS (@lem4115870 _48296) (@lem4115871 _48296)). Qed.
Lemma lem4115873 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4115874 (_48296 : int) : (term493 _48296) = term139.
Proof. exact (MK_COMB (@lem4115873) (@lem4115872 _48296)). Qed.
Lemma lem4115876 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4115877 : term241 = term244.
Proof. exact (@lem4115876 term218). Qed.
Lemma lem4115879 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4115880 : term111 = term200.
Proof. exact (@lem4115879 term20). Qed.
Lemma lem4115881 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4115882 : term113 = term201.
Proof. exact (MK_COMB (@lem4115881) (@lem4115880)). Qed.
Lemma lem4115883 : term494 = term495.
Proof. exact (MK_COMB (@lem4115882) (@lem4115877)). Qed.
Lemma lem4115884 : term496.
Proof. exact (@lem1981473 term111 term111 term241 term111 term178 term111). Qed.
Lemma lem4115886 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115887 : term206 = term207.
Proof. exact (@lem4115886 (NUMERAL 0) term20). Qed.
Lemma lem4115888 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115889 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115890 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115889 h1) (fun h1 : term207 = True => @lem4115888)). Qed.
Lemma lem4115891 : term207 = True.
Proof. exact (EQ_MP (@lem4115890) (@lem4115888)). Qed.
Lemma lem4115892 : term206 = True.
Proof. exact (TRANS (@lem4115887) (@lem4115891)). Qed.
Lemma lem4115893 : True = term206.
Proof. exact (SYM (@lem4115892)). Qed.
Lemma lem4115894 : term206.
Proof. exact (EQ_MP (@lem4115893) (@lem0)). Qed.
Lemma lem4115895 : term497.
Proof. exact (@lem4115884 (@lem4115894)). Qed.
Lemma lem4115897 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115898 : term206 = term207.
Proof. exact (@lem4115897 (NUMERAL 0) term20). Qed.
Lemma lem4115899 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115900 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115901 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115900 h1) (fun h1 : term207 = True => @lem4115899)). Qed.
Lemma lem4115902 : term207 = True.
Proof. exact (EQ_MP (@lem4115901) (@lem4115899)). Qed.
Lemma lem4115903 : term206 = True.
Proof. exact (TRANS (@lem4115898) (@lem4115902)). Qed.
Lemma lem4115904 : True = term206.
Proof. exact (SYM (@lem4115903)). Qed.
Lemma lem4115905 : term206.
Proof. exact (EQ_MP (@lem4115904) (@lem0)). Qed.
Lemma lem4115906 : term498.
Proof. exact (@lem4115895 (@lem4115905)). Qed.
Lemma lem4115908 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4115909 : term206 = term207.
Proof. exact (@lem4115908 (NUMERAL 0) term20). Qed.
Lemma lem4115910 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4115911 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4115912 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4115911 h1) (fun h1 : term207 = True => @lem4115910)). Qed.
Lemma lem4115913 : term207 = True.
Proof. exact (EQ_MP (@lem4115912) (@lem4115910)). Qed.
Lemma lem4115914 : term206 = True.
Proof. exact (TRANS (@lem4115909) (@lem4115913)). Qed.
Lemma lem4115915 : True = term206.
Proof. exact (SYM (@lem4115914)). Qed.
Lemma lem4115916 : term206.
Proof. exact (EQ_MP (@lem4115915) (@lem0)). Qed.
Lemma lem4115917 : term499.
Proof. exact (@lem4115906 (@lem4115916)). Qed.
Lemma lem4115919 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4115920 : term500 = term501.
Proof. exact (@lem4115919 term218 term20). Qed.
Lemma lem4115921 : term224 = term216.
Proof. exact (@lem996237 term216). Qed.
Lemma lem4115922 : (term224 = term216) = (term225 = term218).
Proof. exact (@lem1007663 term216 (BIT1 0) term216). Qed.
Lemma lem4115923 : term225 = term218.
Proof. exact (EQ_MP (@lem4115922) (@lem4115921)). Qed.
Lemma lem4115924 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115925 : term223 = term204.
Proof. exact (MK_COMB (@lem4115924) (@lem4115923)). Qed.
Lemma lem4115926 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115927 : term501 = term241.
Proof. exact (MK_COMB (@lem4115926) (@lem4115925)). Qed.
Lemma lem4115928 : term500 = term241.
Proof. exact (TRANS (@lem4115920) (@lem4115927)). Qed.
Lemma lem4115930 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115931 : term187 = term188.
Proof. exact (@lem4115930 term20 term20). Qed.
Lemma lem4115932 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115933 : term190 = term20.
Proof. exact (EQ_MP (@lem4115932) (@lem940073)). Qed.
Lemma lem4115934 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115935 : term188 = term111.
Proof. exact (MK_COMB (@lem4115934) (@lem4115933)). Qed.
Lemma lem4115936 : term187 = term111.
Proof. exact (TRANS (@lem4115931) (@lem4115935)). Qed.
Lemma lem4115937 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4115938 : term212 = term113.
Proof. exact (MK_COMB (@lem4115937) (@lem4115936)). Qed.
Lemma lem4115939 : term502 = term494.
Proof. exact (MK_COMB (@lem4115938) (@lem4115928)). Qed.
Lemma lem4115942 : term503 = term178.
Proof. exact (@lem1367771 term20 term20). Qed.
Lemma lem4115943 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem4115944 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem4115945 : term217 = term218.
Proof. exact (EQ_MP (@lem4115944) (@lem4115943)). Qed.
Lemma lem4115946 : term218 = term217.
Proof. exact (SYM (@lem4115945)). Qed.
Lemma lem4115947 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115948 : term204 = term214.
Proof. exact (MK_COMB (@lem4115947) (@lem4115946)). Qed.
Lemma lem4115949 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115950 : term241 = term504.
Proof. exact (MK_COMB (@lem4115949) (@lem4115948)). Qed.
Lemma lem4115951 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem4115952 : term494 = term503.
Proof. exact (MK_COMB (@lem4115951) (@lem4115950)). Qed.
Lemma lem4115953 : term494 = term178.
Proof. exact (TRANS (@lem4115952) (@lem4115942)). Qed.
Lemma lem4115954 : term502 = term178.
Proof. exact (TRANS (@lem4115939) (@lem4115953)). Qed.
Lemma lem4115955 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4115956 : term505 = term180.
Proof. exact (MK_COMB (@lem4115955) (@lem4115954)). Qed.
Lemma lem4115957 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem4115958 : term506 = term254.
Proof. exact (MK_COMB (@lem4115956) (@lem4115957)). Qed.
Lemma lem4115960 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4115961 : term254 = term257.
Proof. exact (@lem4115960 term20 term20). Qed.
Lemma lem4115962 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115963 : term190 = term20.
Proof. exact (EQ_MP (@lem4115962) (@lem940073)). Qed.
Lemma lem4115964 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115965 : term188 = term111.
Proof. exact (MK_COMB (@lem4115964) (@lem4115963)). Qed.
Lemma lem4115966 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115967 : term257 = term178.
Proof. exact (MK_COMB (@lem4115966) (@lem4115965)). Qed.
Lemma lem4115968 : term254 = term178.
Proof. exact (TRANS (@lem4115961) (@lem4115967)). Qed.
Lemma lem4115969 : term506 = term178.
Proof. exact (TRANS (@lem4115958) (@lem4115968)). Qed.
Lemma lem4115971 (m : nat) (n : nat) : (term185 m n) = (term186 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4115972 : term187 = term188.
Proof. exact (@lem4115971 term20 term20). Qed.
Lemma lem4115973 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115974 : term190 = term20.
Proof. exact (EQ_MP (@lem4115973) (@lem940073)). Qed.
Lemma lem4115975 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115976 : term188 = term111.
Proof. exact (MK_COMB (@lem4115975) (@lem4115974)). Qed.
Lemma lem4115977 : term187 = term111.
Proof. exact (TRANS (@lem4115972) (@lem4115976)). Qed.
Lemma lem4115978 : term180 = term180.
Proof. exact (eq_refl term180). Qed.
Lemma lem4115979 : term507 = term254.
Proof. exact (MK_COMB (@lem4115978) (@lem4115977)). Qed.
Lemma lem4115981 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4115982 : term254 = term257.
Proof. exact (@lem4115981 term20 term20). Qed.
Lemma lem4115983 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4115984 : term190 = term20.
Proof. exact (EQ_MP (@lem4115983) (@lem940073)). Qed.
Lemma lem4115985 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4115986 : term188 = term111.
Proof. exact (MK_COMB (@lem4115985) (@lem4115984)). Qed.
Lemma lem4115987 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4115988 : term257 = term178.
Proof. exact (MK_COMB (@lem4115987) (@lem4115986)). Qed.
Lemma lem4115989 : term254 = term178.
Proof. exact (TRANS (@lem4115982) (@lem4115988)). Qed.
Lemma lem4115990 : term507 = term178.
Proof. exact (TRANS (@lem4115979) (@lem4115989)). Qed.
Lemma lem4115991 : term178 = term507.
Proof. exact (SYM (@lem4115990)). Qed.
Lemma lem4115992 : term506 = term507.
Proof. exact (TRANS (@lem4115969) (@lem4115991)). Qed.
Lemma lem4115993 : term495 = term179.
Proof. exact (@lem4115917 (@lem4115992)). Qed.
Lemma lem4115994 : term494 = term179.
Proof. exact (TRANS (@lem4115883) (@lem4115993)). Qed.
Lemma lem4115996 (x : real) : (term194 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4115997 : term179 = term178.
Proof. exact (@lem4115996 term178). Qed.
Lemma lem4115998 : term494 = term178.
Proof. exact (TRANS (@lem4115994) (@lem4115997)). Qed.
Lemma lem4115999 (_48296 : int) : (term475 _48296) = term508.
Proof. exact (MK_COMB (@lem4115874 _48296) (@lem4115998)). Qed.
Lemma lem4116000 (_48296 : int) : (term474 _48296) = term508.
Proof. exact (TRANS (@lem4115766 _48296) (@lem4115999 _48296)). Qed.
Lemma lem4116001 : term508 = term178.
Proof. exact (@lem1982721 term178). Qed.
Lemma lem4116002 (_48296 : int) : (term474 _48296) = term178.
Proof. exact (TRANS (@lem4116000 _48296) (@lem4116001)). Qed.
Lemma lem4116003 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4116004 (_48296 : int) : (term509 _48296) = term510.
Proof. exact (MK_COMB (@lem4116003) (@lem4116002 _48296)). Qed.
Lemma lem4116005 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem4116006 (_48296 : int) : (term473 _48296) = term511.
Proof. exact (MK_COMB (@lem4116004 _48296) (@lem4116005)). Qed.
Lemma lem4116007 (_48296 : int) (h1 : term622 _48296) : term511.
Proof. exact (EQ_MP (@lem4116006 _48296) (@lem4115765 _48296 h1)). Qed.
Lemma lem4116009 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4116010 : term511 = term512.
Proof. exact (@lem4116009 term97 term178). Qed.
Lemma lem4116012 (x : nat) : (term176 x) = (term177 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4116013 : term178 = term179.
Proof. exact (@lem4116012 term20). Qed.
Lemma lem4116015 (x : nat) : (real_of_num x) = (term174 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4116016 : term97 = term175.
Proof. exact (@lem4116015 (NUMERAL 0)). Qed.
Lemma lem4116017 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4116018 : term99 = term513.
Proof. exact (MK_COMB (@lem4116017) (@lem4116016)). Qed.
Lemma lem4116019 : term512 = term514.
Proof. exact (MK_COMB (@lem4116018) (@lem4116013)). Qed.
Lemma lem4116020 : term515.
Proof. exact (@lem1980026 term97 term111 term178 term111). Qed.
Lemma lem4116022 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4116023 : term206 = term207.
Proof. exact (@lem4116022 (NUMERAL 0) term20). Qed.
Lemma lem4116024 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4116025 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4116026 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4116025 h1) (fun h1 : term207 = True => @lem4116024)). Qed.
Lemma lem4116027 : term207 = True.
Proof. exact (EQ_MP (@lem4116026) (@lem4116024)). Qed.
Lemma lem4116028 : term206 = True.
Proof. exact (TRANS (@lem4116023) (@lem4116027)). Qed.
Lemma lem4116029 : True = term206.
Proof. exact (SYM (@lem4116028)). Qed.
Lemma lem4116030 : term206.
Proof. exact (EQ_MP (@lem4116029) (@lem0)). Qed.
Lemma lem4116031 : term516.
Proof. exact (@lem4116020 (@lem4116030)). Qed.
Lemma lem4116033 (m : nat) (n : nat) : (term205 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4116034 : term206 = term207.
Proof. exact (@lem4116033 (NUMERAL 0) term20). Qed.
Lemma lem4116035 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4116036 (h1 : term208 = (BIT1 0)) : term207 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4116037 : (term208 = (BIT1 0)) = (term207 = True).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4116036 h1) (fun h1 : term207 = True => @lem4116035)). Qed.
Lemma lem4116038 : term207 = True.
Proof. exact (EQ_MP (@lem4116037) (@lem4116035)). Qed.
Lemma lem4116039 : term206 = True.
Proof. exact (TRANS (@lem4116034) (@lem4116038)). Qed.
Lemma lem4116040 : True = term206.
Proof. exact (SYM (@lem4116039)). Qed.
Lemma lem4116041 : term206.
Proof. exact (EQ_MP (@lem4116040) (@lem0)). Qed.
Lemma lem4116042 : term514 = term517.
Proof. exact (@lem4116031 (@lem4116041)). Qed.
Lemma lem4116044 (m : nat) (n : nat) : (term235 m n) = (term236 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4116045 : term254 = term257.
Proof. exact (@lem4116044 term20 term20). Qed.
Lemma lem4116046 : (term189 = (BIT1 0)) = (term190 = term20).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4116047 : term190 = term20.
Proof. exact (EQ_MP (@lem4116046) (@lem940073)). Qed.
Lemma lem4116048 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4116049 : term188 = term111.
Proof. exact (MK_COMB (@lem4116048) (@lem4116047)). Qed.
Lemma lem4116050 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4116051 : term257 = term178.
Proof. exact (MK_COMB (@lem4116050) (@lem4116049)). Qed.
Lemma lem4116052 : term254 = term178.
Proof. exact (TRANS (@lem4116045) (@lem4116051)). Qed.
Lemma lem4116054 (x : nat) : (term294 x) = term97.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4116055 : term293 = term97.
Proof. exact (@lem4116054 term20). Qed.
Lemma lem4116056 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4116057 : term518 = term99.
Proof. exact (MK_COMB (@lem4116056) (@lem4116055)). Qed.
Lemma lem4116058 : term517 = term512.
Proof. exact (MK_COMB (@lem4116057) (@lem4116052)). Qed.
Lemma lem4116060 (m : nat) (n : nat) : (term519 m n) = (term520 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4116061 : term512 = term521.
Proof. exact (@lem4116060 (NUMERAL 0) term20). Qed.
Lemma lem4116062 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4116063 (h1 : term208 = (BIT1 0)) : (term20 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4116064 : (term208 = (BIT1 0)) = ((term20 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term208 = (BIT1 0) => @lem4116063 h1) (fun h1 : (term20 = (NUMERAL 0)) = False => @lem4116062)). Qed.
Lemma lem4116065 : (term20 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4116064) (@lem4116062)). Qed.
Lemma lem4116066 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4116067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4116068 : term522 = (and True).
Proof. exact (MK_COMB (@lem4116067) (@lem4116066)). Qed.
Lemma lem4116069 : term521 = (True /\ False).
Proof. exact (MK_COMB (@lem4116068) (@lem4116065)). Qed.
Lemma lem4116071 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4116072 : term521 = False.
Proof. exact (TRANS (@lem4116069) (@lem4116071)). Qed.
Lemma lem4116073 : term512 = False.
Proof. exact (TRANS (@lem4116061) (@lem4116072)). Qed.
Lemma lem4116074 : term517 = False.
Proof. exact (TRANS (@lem4116058) (@lem4116073)). Qed.
Lemma lem4116075 : term514 = False.
Proof. exact (TRANS (@lem4116042) (@lem4116074)). Qed.
Lemma lem4116076 : term512 = False.
Proof. exact (TRANS (@lem4116019) (@lem4116075)). Qed.
Lemma lem4116077 : term511 = False.
Proof. exact (TRANS (@lem4116010) (@lem4116076)). Qed.
Lemma lem4116078 (_48296 : int) (h1 : term622 _48296) : False.
Proof. exact (EQ_MP (@lem4116077) (@lem4116007 _48296 h1)). Qed.
Lemma lem4116079 (_48296 : int) (h1 : term396 _48296) : False.
Proof. exact (or_elim (@lem4115174 _48296 h1) (fun h0 : term621 _48296 => @lem4115626 _48296 h0) (fun h0 : term622 _48296 => @lem4116078 _48296 h0)). Qed.
Lemma lem4116080 (_48296 : int) (h1 : term405 _48296) : False.
Proof. exact (or_elim (@lem4114593 _48296 h1) (fun h0 : term400 _48296 => @lem4115173 _48296 h0) (fun h0 : term396 _48296 => @lem4116079 _48296 h0)). Qed.
Lemma lem4116081 (_48296 : int) (h1 : term407 _48296) : False.
Proof. exact (or_elim (@lem4114142 _48296 h1) (fun h0 : term596 _48296 => @lem4114592 _48296 h0) (fun h0 : term405 _48296 => @lem4116080 _48296 h0)). Qed.
Lemma lem4116082 (_48296 : int) (h1 : term428 _48296) : False.
Proof. exact (or_elim (@lem4112687 _48296 h1) (fun h0 : term425 _48296 => @lem4114141 _48296 h0) (fun h0 : term407 _48296 => @lem4116081 _48296 h0)). Qed.
Lemma lem4116083 (_48296 : int) (h1 : term449 _48296) : False.
Proof. exact (or_elim (@lem4110561 _48296 h1) (fun h0 : term446 _48296 => @lem4112686 _48296 h0) (fun h0 : term428 _48296 => @lem4116082 _48296 h0)). Qed.
Lemma lem4116085 (_48296 : int) (h1 : term449 _48296) : term449 _48296.
Proof. exact (h1). Qed.
Lemma lem4116086 (_48296 : int) (h1 : term449 _48296) : (term449 _48296) = False.
Proof. exact (prop_ext (fun h2 : term449 _48296 => @lem4116083 _48296 h1) (fun h2 : False => @lem4116085 _48296 h1)). Qed.
Lemma lem4116087 (_48296 : int) (h1 : term449 _48296) : False.
Proof. exact (EQ_MP (@lem4116086 _48296 h1) (@lem4116085 _48296 h1)). Qed.
Lemma lem4116088 (_48296 : int) (h1 : term170 _48296) : term170 _48296.
Proof. exact (h1). Qed.
Lemma lem4116089 (_48296 : int) (h1 : term170 _48296) : term449 _48296.
Proof. exact (EQ_MP (@lem4110473 _48296) (@lem4116088 _48296 h1)). Qed.
Lemma lem4116090 (_48296 : int) (h1 : term170 _48296) : (term449 _48296) = False.
Proof. exact (prop_ext (fun h2 : term449 _48296 => @lem4116087 _48296 h2) (fun h2 : False => @lem4116089 _48296 h1)). Qed.
Lemma lem4116091 (_48296 : int) (h1 : term170 _48296) : False.
Proof. exact (EQ_MP (@lem4116090 _48296 h1) (@lem4116089 _48296 h1)). Qed.
Lemma lem4116092 (_48296 : int) : term623 _48296.
Proof. exact (fun h0 : term170 _48296 => @lem4116091 _48296 h0). Qed.
Lemma lem4116093 (_48296 : int) : term624 _48296.
Proof. exact (@lem1386578 (term625 _48296)). Qed.
Lemma lem4116096 (_48296 : int) : term625 _48296.
Proof. exact (@lem4116093 _48296 (@lem4116092 _48296)). Qed.
Lemma lem4116097 (_48296 : int) : (term168 _48296) = (term90 _48296).
Proof. exact (SYM (@lem4109312 _48296)). Qed.
Lemma lem4116098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4116099 (_48296 : int) : (term625 _48296) = (term55 _48296).
Proof. exact (MK_COMB (@lem4116098) (@lem4116097 _48296)). Qed.
Lemma lem4116100 (_48296 : int) : term55 _48296.
Proof. exact (EQ_MP (@lem4116099 _48296) (@lem4116096 _48296)). Qed.
Lemma lem4116101 (_48296 : int) : term56 _48296.
Proof. exact (EQ_MP (@lem4109031 _48296) (@lem4116100 _48296)). Qed.
Lemma lem4116102 (c : nat) : term626 c.
Proof. exact (@lem4116101 (int_of_num c)). Qed.
Lemma lem4116103 (c : nat) : term52 c.
Proof. exact (@lem4116102 c (@lem4109030 c)). Qed.
Lemma lem4116104 (c : nat) : (term52 c) = ((term27 c) = (term28 c)).
Proof. exact (SYM (@lem4109027 c)). Qed.
Lemma lem4116111 (c : nat) : (term27 c) = (term28 c).
Proof. exact (EQ_MP (@lem4116104 c) (@lem4116103 c)). Qed.
Lemma lem4116112 {A : Type'} (s : A -> Prop) : (term627 A s) = (term628 A s).
Proof. exact (@lem4116111 (@CARD A s)). Qed.
Lemma lem4116119 {A : Type'} (s : A -> Prop) : (term629 A s) = (term629 A s).
Proof. exact (eq_refl (term629 A s)). Qed.
Lemma lem4116120 {A : Type'} (s : A -> Prop) : (term630 A s) = (term631 A s).
Proof. exact (MK_COMB (@lem4116119 A s) (@lem4116112 A s)). Qed.
Lemma lem4116123 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4116124 {A : Type'} (s : A -> Prop) : (term632 A s) = (term633 A s).
Proof. exact (MK_COMB (@lem4116123) (@lem4116120 A s)). Qed.
Lemma lem4116129 {A : Type'} (s : A -> Prop) : (term634 A s) = (term634 A s).
Proof. exact (eq_refl (term634 A s)). Qed.
Lemma lem4116130 {A : Type'} (s : A -> Prop) : ((term630 A s) = (term634 A s)) = ((term631 A s) = (term634 A s)).
Proof. exact (MK_COMB (@lem4116124 A s) (@lem4116129 A s)). Qed.
Lemma lem4116133 {A : Type'} (s : A -> Prop) : ((term631 A s) = (term634 A s)) = ((term630 A s) = (term634 A s)).
Proof. exact (SYM (@lem4116130 A s)). Qed.
Lemma lem4116137 (q : Prop) (p : Prop) (r : Prop) : (term16 p q r) = (term17 q p r).
Proof. exact (EQ_MP (@lem4108853 q p r) (@lem4108852 q p r)). Qed.
Lemma lem4116138 {A : Type'} (s : A -> Prop) : (term631 A s) = (term635 A s).
Proof. exact (@lem4116137 ((@CARD A s) = (NUMERAL 0)) (@FINITE A s) ((@CARD A s) = term20)). Qed.
Lemma lem4116142 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term0 _100044 s n) = (@HAS_SIZE _100044 s n).
Proof. exact (EQ_MP (@lem4108844 _100044 s n) (@lem4108843 _100044 s n)). Qed.
Lemma lem4116143 {A : Type'} (s : A -> Prop) (n : nat) : (term0 A s n) = (@HAS_SIZE A s n).
Proof. exact (@lem4116142 A s n). Qed.
Lemma lem4116144 {A : Type'} (s : A -> Prop) : (term636 A s) = (term637 A s).
Proof. exact (@lem4116143 A s (NUMERAL 0)). Qed.
Lemma lem4116145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4116146 {A : Type'} (s : A -> Prop) : (term638 A s) = (term639 A s).
Proof. exact (MK_COMB (@lem4116145) (@lem4116144 A s)). Qed.
Lemma lem4116148 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term0 _100044 s n) = (@HAS_SIZE _100044 s n).
Proof. exact (EQ_MP (@lem4108844 _100044 s n) (@lem4108843 _100044 s n)). Qed.
Lemma lem4116149 {A : Type'} (s : A -> Prop) (n : nat) : (term0 A s n) = (@HAS_SIZE A s n).
Proof. exact (@lem4116148 A s n). Qed.
Lemma lem4116150 {A : Type'} (s : A -> Prop) : (term640 A s) = (term641 A s).
Proof. exact (@lem4116149 A s term20). Qed.
Lemma lem4116151 {A : Type'} (s : A -> Prop) : (term635 A s) = (term642 A s).
Proof. exact (MK_COMB (@lem4116146 A s) (@lem4116150 A s)). Qed.
Lemma lem4116154 {A : Type'} (s : A -> Prop) : (term631 A s) = (term642 A s).
Proof. exact (TRANS (@lem4116138 A s) (@lem4116151 A s)). Qed.
Lemma lem4116155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4116156 {A : Type'} (s : A -> Prop) : (term633 A s) = (term643 A s).
Proof. exact (MK_COMB (@lem4116155) (@lem4116154 A s)). Qed.
Lemma lem4116161 {A : Type'} (s : A -> Prop) : (term634 A s) = (term634 A s).
Proof. exact (eq_refl (term634 A s)). Qed.
Lemma lem4116162 {A : Type'} (s : A -> Prop) : ((term631 A s) = (term634 A s)) = ((term642 A s) = (term634 A s)).
Proof. exact (MK_COMB (@lem4116156 A s) (@lem4116161 A s)). Qed.
Lemma lem4116165 {A : Type'} (s : A -> Prop) : ((term642 A s) = (term634 A s)) = ((term631 A s) = (term634 A s)).
Proof. exact (SYM (@lem4116162 A s)). Qed.
Lemma lem4116167 {_100499 : Type'} (s : _100499 -> Prop) : (term637 _100499 s) = (s = (@EMPTY _100499)).
Proof. exact (proj1 (@lem3887954 _100499 (@el nat) s)). Qed.
Lemma lem4116168 {A : Type'} (s : A -> Prop) : (term637 A s) = (s = (@EMPTY A)).
Proof. exact (@lem4116167 A s). Qed.
Lemma lem4116169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4116170 {A : Type'} (s : A -> Prop) : (term639 A s) = (term644 A s).
Proof. exact (MK_COMB (@lem4116169) (@lem4116168 A s)). Qed.
Lemma lem4116171 : term208 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4116172 : (term208 = (BIT1 0)) = (term645 = term20).
Proof. exact (@lem1005477 0 (BIT1 0)). Qed.
Lemma lem4116173 : term645 = term20.
Proof. exact (EQ_MP (@lem4116172) (@lem4116171)). Qed.
Lemma lem4116174 : term20 = term645.
Proof. exact (SYM (@lem4116173)). Qed.
Lemma lem4116175 {A : Type'} (s : A -> Prop) : (@HAS_SIZE A s) = (@HAS_SIZE A s).
Proof. exact (eq_refl (@HAS_SIZE A s)). Qed.
Lemma lem4116176 {A : Type'} (s : A -> Prop) : (term641 A s) = (term646 A s).
Proof. exact (MK_COMB (@lem4116175 A s) (@lem4116174)). Qed.
Lemma lem4116178 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term647 _100499 s n) = (term648 _100499 n s).
Proof. exact (proj2 (@lem3887954 _100499 n s)). Qed.
Lemma lem4116179 {A : Type'} (n : nat) (s : A -> Prop) : (term647 A s n) = (term648 A n s).
Proof. exact (@lem4116178 A n s). Qed.
Lemma lem4116180 {A : Type'} (s : A -> Prop) : (term646 A s) = (term649 A s).
Proof. exact (@lem4116179 A (NUMERAL 0) s). Qed.
Lemma lem4116181 {A : Type'} (s : A -> Prop) : (term641 A s) = (term649 A s).
Proof. exact (TRANS (@lem4116176 A s) (@lem4116180 A s)). Qed.
Lemma lem4116183 {_100607 : Type'} (P : type686 _100607) : (term650 _100607 P) = (P (@EMPTY _100607)).
Proof. exact (proj1 (@lem3892933 _100607 (@el nat) P)). Qed.
Lemma lem4116184 {A : Type'} (P : type686 A) : (term650 A P) = (P (@EMPTY A)).
Proof. exact (@lem4116183 A P). Qed.
Lemma lem4116185 {A : Type'} (s : A -> Prop) (a : A) : (term651 A s a) = (term652 A s a).
Proof. exact (@lem4116184 A (term653 A s a)). Qed.
Lemma lem4116186 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term654 A s a t) = (term655 A s a t).
Proof. exact (eq_refl (term654 A s a t)). Qed.
Lemma lem4116187 {A : Type'} (t : A -> Prop) : (term656 A t) = (term656 A t).
Proof. exact (eq_refl (term656 A t)). Qed.
Lemma lem4116188 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term657 A s a t) = (term658 A s a t).
Proof. exact (MK_COMB (@lem4116187 A t) (@lem4116186 A s a t)). Qed.
Lemma lem4116189 {A : Type'} (s : A -> Prop) (a : A) : (term659 A s a) = (term660 A s a).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4116188 A s a t)). Qed.
Lemma lem4116190 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4116191 {A : Type'} (s : A -> Prop) (a : A) : (term651 A s a) = (term661 A s a).
Proof. exact (MK_COMB (@lem4116190 A) (@lem4116189 A s a)). Qed.
Lemma lem4116192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4116193 {A : Type'} (s : A -> Prop) (a : A) : (term662 A s a) = (term663 A s a).
Proof. exact (MK_COMB (@lem4116192) (@lem4116191 A s a)). Qed.
Lemma lem4116194 {A : Type'} (s : A -> Prop) (a : A) : (term652 A s a) = (term664 A s a).
Proof. exact (eq_refl (term652 A s a)). Qed.
Lemma lem4116195 {A : Type'} (s : A -> Prop) (a : A) : ((term651 A s a) = (term652 A s a)) = ((term661 A s a) = (term664 A s a)).
Proof. exact (MK_COMB (@lem4116193 A s a) (@lem4116194 A s a)). Qed.
Lemma lem4116196 {A : Type'} (s : A -> Prop) (a : A) : (term661 A s a) = (term664 A s a).
Proof. exact (EQ_MP (@lem4116195 A s a) (@lem4116185 A s a)). Qed.
Lemma lem4116197 {A : Type'} (s : A -> Prop) : (term665 A s) = (term666 A s).
Proof. exact (fun_ext (fun a : A => @lem4116196 A s a)). Qed.
Lemma lem4116198 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116199 {A : Type'} (s : A -> Prop) : (term649 A s) = (term667 A s).
Proof. exact (MK_COMB (@lem4116198 A) (@lem4116197 A s)). Qed.
Lemma lem4116200 {A : Type'} (s : A -> Prop) : (term641 A s) = (term667 A s).
Proof. exact (TRANS (@lem4116181 A s) (@lem4116199 A s)). Qed.
Lemma lem4116202 {_100554 : Type'} (a : _100554) (P : Prop) : (term668 _100554 a P) = P.
Proof. exact (proj1 (@lem3888988 _100554 (@el _100554) a (@el (_100554 -> Prop)) P)). Qed.
Lemma lem4116203 {A : Type'} (a : A) (P : Prop) : (term668 A a P) = P.
Proof. exact (@lem4116202 A a P). Qed.
Lemma lem4116206 {A : Type'} (s : A -> Prop) (a : A) : (term664 A s a) = (s = (@INSERT A a (@EMPTY A))).
Proof. exact (@lem4116203 A a (s = (@INSERT A a (@EMPTY A)))). Qed.
Lemma lem4116207 {A : Type'} (s : A -> Prop) : (term666 A s) = (term669 A s).
Proof. exact (fun_ext (fun a : A => @lem4116206 A s a)). Qed.
Lemma lem4116208 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116209 {A : Type'} (s : A -> Prop) : (term667 A s) = (term670 A s).
Proof. exact (MK_COMB (@lem4116208 A) (@lem4116207 A s)). Qed.
Lemma lem4116210 {A : Type'} (s : A -> Prop) : (term641 A s) = (term670 A s).
Proof. exact (TRANS (@lem4116200 A s) (@lem4116209 A s)). Qed.
Lemma lem4116211 {A : Type'} (s : A -> Prop) : (term642 A s) = (term671 A s).
Proof. exact (MK_COMB (@lem4116170 A s) (@lem4116210 A s)). Qed.
Lemma lem4116212 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4116213 {A : Type'} (s : A -> Prop) : (term643 A s) = (term672 A s).
Proof. exact (MK_COMB (@lem4116212) (@lem4116211 A s)). Qed.
Lemma lem4116214 {A : Type'} (s : A -> Prop) : (term634 A s) = (term634 A s).
Proof. exact (eq_refl (term634 A s)). Qed.
Lemma lem4116215 {A : Type'} (s : A -> Prop) : ((term642 A s) = (term634 A s)) = ((term671 A s) = (term634 A s)).
Proof. exact (MK_COMB (@lem4116213 A s) (@lem4116214 A s)). Qed.
Lemma lem4116216 {A : Type'} (s : A -> Prop) : ((term671 A s) = (term634 A s)) = ((term642 A s) = (term634 A s)).
Proof. exact (SYM (@lem4116215 A s)). Qed.
Lemma lem4116226 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term673 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4116227 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term673 A s t).
Proof. exact (@lem4116226 A s t). Qed.
Lemma lem4116228 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term674 A s).
Proof. exact (@lem4116227 A s (@EMPTY A)). Qed.
Lemma lem4116237 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4116238 {A : Type'} (s : A -> Prop) : (term644 A s) = (term675 A s).
Proof. exact (MK_COMB (@lem4116237) (@lem4116228 A s)). Qed.
Lemma lem4116246 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term673 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4116247 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term673 A s t).
Proof. exact (@lem4116246 A s t). Qed.
Lemma lem4116248 {A : Type'} (s : A -> Prop) (a : A) : (s = (@INSERT A a (@EMPTY A))) = (term676 A s a).
Proof. exact (@lem4116247 A s (@INSERT A a (@EMPTY A))). Qed.
Lemma lem4116257 {A : Type'} (s : A -> Prop) : (term669 A s) = (term677 A s).
Proof. exact (fun_ext (fun a : A => @lem4116248 A s a)). Qed.
Lemma lem4116258 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116259 {A : Type'} (s : A -> Prop) : (term670 A s) = (term678 A s).
Proof. exact (MK_COMB (@lem4116258 A) (@lem4116257 A s)). Qed.
Lemma lem4116264 {A : Type'} (s : A -> Prop) : (term671 A s) = (term679 A s).
Proof. exact (MK_COMB (@lem4116238 A s) (@lem4116259 A s)). Qed.
Lemma lem4116267 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4116268 {A : Type'} (s : A -> Prop) : (term672 A s) = (term680 A s).
Proof. exact (MK_COMB (@lem4116267) (@lem4116264 A s)). Qed.
Lemma lem4116274 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term681 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4116275 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term681 A s t).
Proof. exact (@lem4116274 A s t). Qed.
Lemma lem4116276 {A : Type'} (s : A -> Prop) (a : A) : (term682 A s a) = (term683 A s a).
Proof. exact (@lem4116275 A s (@INSERT A a (@EMPTY A))). Qed.
Lemma lem4116283 {A : Type'} (s : A -> Prop) : (term684 A s) = (term685 A s).
Proof. exact (fun_ext (fun a : A => @lem4116276 A s a)). Qed.
Lemma lem4116284 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116285 {A : Type'} (s : A -> Prop) : (term634 A s) = (term686 A s).
Proof. exact (MK_COMB (@lem4116284 A) (@lem4116283 A s)). Qed.
Lemma lem4116290 {A : Type'} (s : A -> Prop) : ((term671 A s) = (term634 A s)) = ((term679 A s) = (term686 A s)).
Proof. exact (MK_COMB (@lem4116268 A s) (@lem4116285 A s)). Qed.
Lemma lem4116295 {A : Type'} (s : A -> Prop) : ((term679 A s) = (term686 A s)) = ((term671 A s) = (term634 A s)).
Proof. exact (SYM (@lem4116290 A s)). Qed.
Lemma lem4116307 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4116308 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4116307 A P x). Qed.
Lemma lem4116309 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4116308 A s x). Qed.
Lemma lem4116310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4116311 {A : Type'} (s : A -> Prop) (x : A) : (term687 A x s) = (term688 A s x).
Proof. exact (MK_COMB (@lem4116310) (@lem4116309 A s x)). Qed.
Lemma lem4116313 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4116314 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4116313 A x). Qed.
Lemma lem4116315 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = ((s x) = False).
Proof. exact (MK_COMB (@lem4116311 A s x) (@lem4116314 A x)). Qed.
Lemma lem4116317 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4116318 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = False) = (term689 A s x).
Proof. exact (@lem4116317 (s x)). Qed.
Lemma lem4116319 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@EMPTY A))) = (term689 A s x).
Proof. exact (TRANS (@lem4116315 A s x) (@lem4116318 A s x)). Qed.
Lemma lem4116320 {A : Type'} (s : A -> Prop) : (term690 A s) = (term691 A s).
Proof. exact (fun_ext (fun x : A => @lem4116319 A s x)). Qed.
Lemma lem4116321 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116322 {A : Type'} (s : A -> Prop) : (term674 A s) = (term692 A s).
Proof. exact (MK_COMB (@lem4116321 A) (@lem4116320 A s)). Qed.
Lemma lem4116327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4116328 {A : Type'} (s : A -> Prop) : (term675 A s) = (term693 A s).
Proof. exact (MK_COMB (@lem4116327) (@lem4116322 A s)). Qed.
Lemma lem4116340 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4116341 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4116340 A P x). Qed.
Lemma lem4116342 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4116341 A s x). Qed.
Lemma lem4116343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4116344 {A : Type'} (s : A -> Prop) (x : A) : (term687 A x s) = (term688 A s x).
Proof. exact (MK_COMB (@lem4116343) (@lem4116342 A s x)). Qed.
Lemma lem4116346 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term694 A x y s) = (term695 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4116347 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term694 A x y s) = (term695 A y x s).
Proof. exact (@lem4116346 A y x s). Qed.
Lemma lem4116348 {A : Type'} (a : A) (x : A) : (term696 A x a) = (term697 A a x).
Proof. exact (@lem4116347 A a x (@EMPTY A)). Qed.
Lemma lem4116354 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4116355 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4116354 A x). Qed.
Lemma lem4116356 {A : Type'} (x : A) (a : A) : (term698 A x a) = (term698 A x a).
Proof. exact (eq_refl (term698 A x a)). Qed.
Lemma lem4116357 {A : Type'} (x : A) (a : A) : (term697 A a x) = (term699 A x a).
Proof. exact (MK_COMB (@lem4116356 A x a) (@lem4116355 A x)). Qed.
Lemma lem4116359 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4116360 {A : Type'} (x : A) (a : A) : (term699 A x a) = (x = a).
Proof. exact (@lem4116359 (x = a)). Qed.
Lemma lem4116363 {A : Type'} (x : A) (a : A) : (term697 A a x) = (x = a).
Proof. exact (TRANS (@lem4116357 A x a) (@lem4116360 A x a)). Qed.
Lemma lem4116364 {A : Type'} (x : A) (a : A) : (term696 A x a) = (x = a).
Proof. exact (TRANS (@lem4116348 A a x) (@lem4116363 A x a)). Qed.
Lemma lem4116365 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((@IN A x s) = (term696 A x a)) = ((s x) = (x = a)).
Proof. exact (MK_COMB (@lem4116344 A s x) (@lem4116364 A x a)). Qed.
Lemma lem4116368 {A : Type'} (s : A -> Prop) (a : A) : (term700 A s a) = (term701 A s a).
Proof. exact (fun_ext (fun x : A => @lem4116365 A s x a)). Qed.
Lemma lem4116369 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116370 {A : Type'} (s : A -> Prop) (a : A) : (term676 A s a) = (term702 A s a).
Proof. exact (MK_COMB (@lem4116369 A) (@lem4116368 A s a)). Qed.
Lemma lem4116375 {A : Type'} (s : A -> Prop) : (term677 A s) = (term703 A s).
Proof. exact (fun_ext (fun a : A => @lem4116370 A s a)). Qed.
Lemma lem4116376 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116377 {A : Type'} (s : A -> Prop) : (term678 A s) = (term704 A s).
Proof. exact (MK_COMB (@lem4116376 A) (@lem4116375 A s)). Qed.
Lemma lem4116382 {A : Type'} (s : A -> Prop) : (term679 A s) = (term705 A s).
Proof. exact (MK_COMB (@lem4116328 A s) (@lem4116377 A s)). Qed.
Lemma lem4116385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4116386 {A : Type'} (s : A -> Prop) : (term680 A s) = (term706 A s).
Proof. exact (MK_COMB (@lem4116385) (@lem4116382 A s)). Qed.
Lemma lem4116398 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4116399 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4116398 A P x). Qed.
Lemma lem4116400 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4116399 A s x). Qed.
Lemma lem4116401 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4116402 {A : Type'} (s : A -> Prop) (x : A) : (term707 A x s) = (term708 A s x).
Proof. exact (MK_COMB (@lem4116401) (@lem4116400 A s x)). Qed.
Lemma lem4116404 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term694 A x y s) = (term695 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem4116405 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term694 A x y s) = (term695 A y x s).
Proof. exact (@lem4116404 A y x s). Qed.
Lemma lem4116406 {A : Type'} (a : A) (x : A) : (term696 A x a) = (term697 A a x).
Proof. exact (@lem4116405 A a x (@EMPTY A)). Qed.
Lemma lem4116412 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4116413 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4116412 A x). Qed.
Lemma lem4116414 {A : Type'} (x : A) (a : A) : (term698 A x a) = (term698 A x a).
Proof. exact (eq_refl (term698 A x a)). Qed.
Lemma lem4116415 {A : Type'} (x : A) (a : A) : (term697 A a x) = (term699 A x a).
Proof. exact (MK_COMB (@lem4116414 A x a) (@lem4116413 A x)). Qed.
Lemma lem4116417 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4116418 {A : Type'} (x : A) (a : A) : (term699 A x a) = (x = a).
Proof. exact (@lem4116417 (x = a)). Qed.
Lemma lem4116421 {A : Type'} (x : A) (a : A) : (term697 A a x) = (x = a).
Proof. exact (TRANS (@lem4116415 A x a) (@lem4116418 A x a)). Qed.
Lemma lem4116422 {A : Type'} (x : A) (a : A) : (term696 A x a) = (x = a).
Proof. exact (TRANS (@lem4116406 A a x) (@lem4116421 A x a)). Qed.
Lemma lem4116423 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term709 A s x a) = (term710 A s x a).
Proof. exact (MK_COMB (@lem4116402 A s x) (@lem4116422 A x a)). Qed.
Lemma lem4116426 {A : Type'} (s : A -> Prop) (a : A) : (term711 A s a) = (term712 A s a).
Proof. exact (fun_ext (fun x : A => @lem4116423 A s x a)). Qed.
Lemma lem4116427 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116428 {A : Type'} (s : A -> Prop) (a : A) : (term683 A s a) = (term713 A s a).
Proof. exact (MK_COMB (@lem4116427 A) (@lem4116426 A s a)). Qed.
Lemma lem4116433 {A : Type'} (s : A -> Prop) : (term685 A s) = (term714 A s).
Proof. exact (fun_ext (fun a : A => @lem4116428 A s a)). Qed.
Lemma lem4116434 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116435 {A : Type'} (s : A -> Prop) : (term686 A s) = (term715 A s).
Proof. exact (MK_COMB (@lem4116434 A) (@lem4116433 A s)). Qed.
Lemma lem4116440 {A : Type'} (s : A -> Prop) : ((term679 A s) = (term686 A s)) = ((term705 A s) = (term715 A s)).
Proof. exact (MK_COMB (@lem4116386 A s) (@lem4116435 A s)). Qed.
Lemma lem4116443 {A : Type'} (s : A -> Prop) : ((term705 A s) = (term715 A s)) = ((term679 A s) = (term686 A s)).
Proof. exact (SYM (@lem4116440 A s)). Qed.
Lemma lem4116445 (p : Prop) : p = (term716 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4116446 {A : Type'} (s : A -> Prop) : ((term705 A s) = (term715 A s)) = (term717 A s).
Proof. exact (@lem4116445 ((term705 A s) = (term715 A s))). Qed.
Lemma lem4116447 {A : Type'} (s : A -> Prop) : (term717 A s) = ((term705 A s) = (term715 A s)).
Proof. exact (SYM (@lem4116446 A s)). Qed.
Lemma lem4116448 {A : Type'} (s : A -> Prop) (h1 : term718 A s) : term718 A s.
Proof. exact (h1). Qed.
Lemma lem4116451 {A : Type'} (s : A -> Prop) (h1 : term717 A s) : term717 A s.
Proof. exact (h1). Qed.
Lemma lem4116452 {A : Type'} (s : A -> Prop) : term719 A s.
Proof. exact (fun h0 : term717 A s => @lem4116451 A s h0). Qed.
Lemma lem4116453 {A : Type'} (s : A -> Prop) (h1 : term719 A s) : term719 A s.
Proof. exact (h1). Qed.
Lemma lem4116454 {A : Type'} (s : A -> Prop) (h1 : term717 A s) : term717 A s.
Proof. exact (h1). Qed.
Lemma lem4116455 {A : Type'} (s : A -> Prop) (h1 : term717 A s) (h2 : term719 A s) : term717 A s.
Proof. exact (@lem4116453 A s h2 (@lem4116454 A s h1)). Qed.
Lemma lem4116456 {A : Type'} (s : A -> Prop) (h1 : term717 A s) : term720 A s.
Proof. exact (fun h0 : term719 A s => @lem4116455 A s h1 h0). Qed.
Lemma lem4116457 {A : Type'} (s : A -> Prop) (h1 : term719 A s) : term719 A s.
Proof. exact (h1). Qed.
Lemma lem4116458 {A : Type'} (s : A -> Prop) (h1 : term717 A s) (h2 : term719 A s) : term717 A s.
Proof. exact (@lem4116456 A s h1 (@lem4116457 A s h2)). Qed.
Lemma lem4116459 {A : Type'} (s : A -> Prop) (h1 : term719 A s) : term719 A s.
Proof. exact (fun h0 : term717 A s => @lem4116458 A s h0 h1). Qed.
Lemma lem4116460 {A : Type'} (s : A -> Prop) : term721 A s.
Proof. exact (fun h0 : term719 A s => @lem4116459 A s h0). Qed.
Lemma lem4116463 {A : Type'} (s : A -> Prop) : term719 A s.
Proof. exact (@lem4116460 A s (@lem4116452 A s)). Qed.
Lemma lem4116464 {A : Type'} (s : A -> Prop) : term719 A s.
Proof. exact (@lem4116463 A s). Qed.
Lemma lem4116470 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4116471 {A : Type'} (s : A -> Prop) : (term717 A s) = (term722 A s).
Proof. exact (@lem4116470 (term718 A s)). Qed.
Lemma lem4116473 (t : Prop) : (term169 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4116474 {A : Type'} (s : A -> Prop) : (term722 A s) = ((term705 A s) = (term715 A s)).
Proof. exact (@lem4116473 ((term705 A s) = (term715 A s))). Qed.
Lemma lem4116475 {A : Type'} (s : A -> Prop) : (term717 A s) = ((term705 A s) = (term715 A s)).
Proof. exact (TRANS (@lem4116471 A s) (@lem4116474 A s)). Qed.
Lemma lem4116500 {A : Type'} : (term723 A) = (term724 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4116475 A s)). Qed.
Lemma lem4116501 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4116510 {A : Type'} : (term725 A) = (term726 A).
Proof. exact (MK_COMB (@lem4116501 A) (@lem4116500 A)). Qed.
Lemma lem4116515 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term710 A s x a) = (term710 A s x a).
Proof. exact (eq_refl (term710 A s x a)). Qed.
Lemma lem4116516 {A : Type'} (s : A -> Prop) (a : A) : (term712 A s a) = (term712 A s a).
Proof. exact (fun_ext (fun x : A => @lem4116515 A s x a)). Qed.
Lemma lem4116517 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116518 {A : Type'} (s : A -> Prop) (a : A) : (term713 A s a) = (term713 A s a).
Proof. exact (MK_COMB (@lem4116517 A) (@lem4116516 A s a)). Qed.
Lemma lem4116519 {A : Type'} (s : A -> Prop) : (term714 A s) = (term714 A s).
Proof. exact (fun_ext (fun a : A => @lem4116518 A s a)). Qed.
Lemma lem4116520 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116521 {A : Type'} (s : A -> Prop) : (term715 A s) = (term715 A s).
Proof. exact (MK_COMB (@lem4116520 A) (@lem4116519 A s)). Qed.
Lemma lem4116526 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((s x) = (x = a)) = ((s x) = (x = a)).
Proof. exact (eq_refl ((s x) = (x = a))). Qed.
Lemma lem4116527 {A : Type'} (s : A -> Prop) (a : A) : (term701 A s a) = (term701 A s a).
Proof. exact (fun_ext (fun x : A => @lem4116526 A s x a)). Qed.
Lemma lem4116528 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116529 {A : Type'} (s : A -> Prop) (a : A) : (term702 A s a) = (term702 A s a).
Proof. exact (MK_COMB (@lem4116528 A) (@lem4116527 A s a)). Qed.
Lemma lem4116530 {A : Type'} (s : A -> Prop) : (term703 A s) = (term703 A s).
Proof. exact (fun_ext (fun a : A => @lem4116529 A s a)). Qed.
Lemma lem4116531 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116532 {A : Type'} (s : A -> Prop) : (term704 A s) = (term704 A s).
Proof. exact (MK_COMB (@lem4116531 A) (@lem4116530 A s)). Qed.
Lemma lem4116535 {A : Type'} (s : A -> Prop) (x : A) : (term689 A s x) = (term689 A s x).
Proof. exact (eq_refl (term689 A s x)). Qed.
Lemma lem4116536 {A : Type'} (s : A -> Prop) : (term691 A s) = (term691 A s).
Proof. exact (fun_ext (fun x : A => @lem4116535 A s x)). Qed.
Lemma lem4116537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116538 {A : Type'} (s : A -> Prop) : (term692 A s) = (term692 A s).
Proof. exact (MK_COMB (@lem4116537 A) (@lem4116536 A s)). Qed.
Lemma lem4116539 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4116540 {A : Type'} (s : A -> Prop) : (term693 A s) = (term693 A s).
Proof. exact (MK_COMB (@lem4116539) (@lem4116538 A s)). Qed.
Lemma lem4116541 {A : Type'} (s : A -> Prop) : (term705 A s) = (term705 A s).
Proof. exact (MK_COMB (@lem4116540 A s) (@lem4116532 A s)). Qed.
Lemma lem4116542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4116543 {A : Type'} (s : A -> Prop) : (term706 A s) = (term706 A s).
Proof. exact (MK_COMB (@lem4116542) (@lem4116541 A s)). Qed.
Lemma lem4116544 {A : Type'} (s : A -> Prop) : ((term705 A s) = (term715 A s)) = ((term705 A s) = (term715 A s)).
Proof. exact (MK_COMB (@lem4116543 A s) (@lem4116521 A s)). Qed.
Lemma lem4116545 {A : Type'} : (term724 A) = (term724 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4116544 A s)). Qed.
Lemma lem4116546 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4116547 {A : Type'} : (term726 A) = (term726 A).
Proof. exact (MK_COMB (@lem4116546 A) (@lem4116545 A)). Qed.
Lemma lem4116590 {A : Type'} : (term725 A) = (term726 A).
Proof. exact (TRANS (@lem4116510 A) (@lem4116547 A)). Qed.
Lemma lem4116591 {A : Type'} : (term726 A) = (term725 A).
Proof. exact (SYM (@lem4116590 A)). Qed.
Lemma lem4116593 (p : Prop) : p = (term716 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4116594 {A : Type'} (s : A -> Prop) : ((term705 A s) = (term715 A s)) = (term717 A s).
Proof. exact (@lem4116593 ((term705 A s) = (term715 A s))). Qed.
Lemma lem4116595 {A : Type'} (s : A -> Prop) : (term717 A s) = ((term705 A s) = (term715 A s)).
Proof. exact (SYM (@lem4116594 A s)). Qed.
Lemma lem4116596 {A : Type'} (s : A -> Prop) (h1 : term718 A s) : term718 A s.
Proof. exact (h1). Qed.
Lemma lem4116597 {A : Type'} (s : A -> Prop) (x : A) : (term689 A s x) = (term689 A s x).
Proof. exact (eq_refl (term689 A s x)). Qed.
Lemma lem4116600 {A : Type'} (s : A -> Prop) (x : A) : (term727 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem4116601 {A : Type'} (P : A -> Prop) : (term728 A P) = (term729 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4116602 {A : Type'} (s : A -> Prop) : (term730 A s) = (term731 A s).
Proof. exact (@lem4116601 A (term691 A s)). Qed.
Lemma lem4116603 {A : Type'} (s : A -> Prop) (x : A) : (term732 A s x) = (term689 A s x).
Proof. exact (eq_refl (term732 A s x)). Qed.
Lemma lem4116604 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4116605 {A : Type'} (s : A -> Prop) (x : A) : (term733 A s x) = (term727 A s x).
Proof. exact (MK_COMB (@lem4116604) (@lem4116603 A s x)). Qed.
Lemma lem4116606 {A : Type'} (s : A -> Prop) (x : A) : (term733 A s x) = (s x).
Proof. exact (TRANS (@lem4116605 A s x) (@lem4116600 A s x)). Qed.
Lemma lem4116607 {A : Type'} (s : A -> Prop) : (term734 A s) = (term735 A s).
Proof. exact (fun_ext (fun x : A => @lem4116606 A s x)). Qed.
Lemma lem4116608 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116609 {A : Type'} (s : A -> Prop) : (term731 A s) = (term736 A s).
Proof. exact (MK_COMB (@lem4116608 A) (@lem4116607 A s)). Qed.
Lemma lem4116610 {A : Type'} (s : A -> Prop) : (term730 A s) = (term736 A s).
Proof. exact (TRANS (@lem4116602 A s) (@lem4116609 A s)). Qed.
Lemma lem4116611 {A : Type'} (s : A -> Prop) : (term691 A s) = (term691 A s).
Proof. exact (fun_ext (fun x : A => @lem4116597 A s x)). Qed.
Lemma lem4116612 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116613 {A : Type'} (s : A -> Prop) : (term692 A s) = (term692 A s).
Proof. exact (MK_COMB (@lem4116612 A) (@lem4116611 A s)). Qed.
Lemma lem4116628 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term737 A s x a) = (term738 A s x a).
Proof. exact (@lem17930 (s x) (x = a)). Qed.
Lemma lem4116639 {A : Type'} (s : A -> Prop) (x : A) (a : A) : ((s x) = (x = a)) = (term739 A s x a).
Proof. exact (@lem17784 (s x) (x = a)). Qed.
Lemma lem4116640 {A : Type'} (P : A -> Prop) : (term728 A P) = (term729 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4116641 {A : Type'} (s : A -> Prop) (a : A) : (term740 A s a) = (term741 A s a).
Proof. exact (@lem4116640 A (term701 A s a)). Qed.
Lemma lem4116642 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term742 A s a x) = ((s x) = (x = a)).
Proof. exact (eq_refl (term742 A s a x)). Qed.
Lemma lem4116643 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4116644 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term743 A s a x) = (term737 A s x a).
Proof. exact (MK_COMB (@lem4116643) (@lem4116642 A s x a)). Qed.
Lemma lem4116645 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term743 A s a x) = (term738 A s x a).
Proof. exact (TRANS (@lem4116644 A s x a) (@lem4116628 A s x a)). Qed.
Lemma lem4116646 {A : Type'} (s : A -> Prop) (a : A) : (term744 A s a) = (term745 A s a).
Proof. exact (fun_ext (fun x : A => @lem4116645 A s x a)). Qed.
Lemma lem4116647 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116648 {A : Type'} (s : A -> Prop) (a : A) : (term741 A s a) = (term746 A s a).
Proof. exact (MK_COMB (@lem4116647 A) (@lem4116646 A s a)). Qed.
Lemma lem4116649 {A : Type'} (s : A -> Prop) (a : A) : (term740 A s a) = (term746 A s a).
Proof. exact (TRANS (@lem4116641 A s a) (@lem4116648 A s a)). Qed.
Lemma lem4116650 {A : Type'} (s : A -> Prop) (a : A) : (term701 A s a) = (term747 A s a).
Proof. exact (fun_ext (fun x : A => @lem4116639 A s x a)). Qed.
Lemma lem4116651 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116652 {A : Type'} (s : A -> Prop) (a : A) : (term702 A s a) = (term748 A s a).
Proof. exact (MK_COMB (@lem4116651 A) (@lem4116650 A s a)). Qed.
Lemma lem4116653 {A : Type'} (P : A -> Prop) : (term749 A P) = (term692 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4116654 {A : Type'} (s : A -> Prop) : (term750 A s) = (term751 A s).
Proof. exact (@lem4116653 A (term703 A s)). Qed.
Lemma lem4116655 {A : Type'} (s : A -> Prop) (a : A) : (term752 A s a) = (term702 A s a).
Proof. exact (eq_refl (term752 A s a)). Qed.
Lemma lem4116656 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4116657 {A : Type'} (s : A -> Prop) (a : A) : (term753 A s a) = (term740 A s a).
Proof. exact (MK_COMB (@lem4116656) (@lem4116655 A s a)). Qed.
Lemma lem4116658 {A : Type'} (s : A -> Prop) (a : A) : (term753 A s a) = (term746 A s a).
Proof. exact (TRANS (@lem4116657 A s a) (@lem4116649 A s a)). Qed.
Lemma lem4116659 {A : Type'} (s : A -> Prop) : (term754 A s) = (term755 A s).
Proof. exact (fun_ext (fun a : A => @lem4116658 A s a)). Qed.
Lemma lem4116660 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116661 {A : Type'} (s : A -> Prop) : (term751 A s) = (term756 A s).
Proof. exact (MK_COMB (@lem4116660 A) (@lem4116659 A s)). Qed.
Lemma lem4116662 {A : Type'} (s : A -> Prop) : (term750 A s) = (term756 A s).
Proof. exact (TRANS (@lem4116654 A s) (@lem4116661 A s)). Qed.
Lemma lem4116663 {A : Type'} (s : A -> Prop) : (term703 A s) = (term757 A s).
Proof. exact (fun_ext (fun a : A => @lem4116652 A s a)). Qed.
Lemma lem4116664 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116665 {A : Type'} (s : A -> Prop) : (term704 A s) = (term758 A s).
Proof. exact (MK_COMB (@lem4116664 A) (@lem4116663 A s)). Qed.
Lemma lem4116666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4116667 {A : Type'} (s : A -> Prop) : (term759 A s) = (term760 A s).
Proof. exact (MK_COMB (@lem4116666) (@lem4116610 A s)). Qed.
Lemma lem4116668 {A : Type'} (s : A -> Prop) : (term761 A s) = (term762 A s).
Proof. exact (MK_COMB (@lem4116667 A s) (@lem4116662 A s)). Qed.
Lemma lem4116669 {A : Type'} (s : A -> Prop) : (term763 A s) = (term761 A s).
Proof. exact (@lem17160 (term692 A s) (term704 A s)). Qed.
Lemma lem4116670 {A : Type'} (s : A -> Prop) : (term763 A s) = (term762 A s).
Proof. exact (TRANS (@lem4116669 A s) (@lem4116668 A s)). Qed.
Lemma lem4116671 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4116672 {A : Type'} (s : A -> Prop) : (term693 A s) = (term693 A s).
Proof. exact (MK_COMB (@lem4116671) (@lem4116613 A s)). Qed.
Lemma lem4116673 {A : Type'} (s : A -> Prop) : (term705 A s) = (term764 A s).
Proof. exact (MK_COMB (@lem4116672 A s) (@lem4116665 A s)). Qed.
Lemma lem4116682 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term765 A s x a) = (term766 A s x a).
Proof. exact (@lem17362 (s x) (x = a)). Qed.
Lemma lem4116687 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term710 A s x a) = (term767 A s x a).
Proof. exact (@lem17265 (s x) (x = a)). Qed.
Lemma lem4116688 {A : Type'} (P : A -> Prop) : (term728 A P) = (term729 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4116689 {A : Type'} (s : A -> Prop) (a : A) : (term768 A s a) = (term769 A s a).
Proof. exact (@lem4116688 A (term712 A s a)). Qed.
Lemma lem4116690 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term770 A s a x) = (term710 A s x a).
Proof. exact (eq_refl (term770 A s a x)). Qed.
Lemma lem4116691 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4116692 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term771 A s a x) = (term765 A s x a).
Proof. exact (MK_COMB (@lem4116691) (@lem4116690 A s x a)). Qed.
Lemma lem4116693 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term771 A s a x) = (term766 A s x a).
Proof. exact (TRANS (@lem4116692 A s x a) (@lem4116682 A s x a)). Qed.
Lemma lem4116694 {A : Type'} (s : A -> Prop) (a : A) : (term772 A s a) = (term773 A s a).
Proof. exact (fun_ext (fun x : A => @lem4116693 A s x a)). Qed.
Lemma lem4116695 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116696 {A : Type'} (s : A -> Prop) (a : A) : (term769 A s a) = (term774 A s a).
Proof. exact (MK_COMB (@lem4116695 A) (@lem4116694 A s a)). Qed.
Lemma lem4116697 {A : Type'} (s : A -> Prop) (a : A) : (term768 A s a) = (term774 A s a).
Proof. exact (TRANS (@lem4116689 A s a) (@lem4116696 A s a)). Qed.
Lemma lem4116698 {A : Type'} (s : A -> Prop) (a : A) : (term712 A s a) = (term775 A s a).
Proof. exact (fun_ext (fun x : A => @lem4116687 A s x a)). Qed.
Lemma lem4116699 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116700 {A : Type'} (s : A -> Prop) (a : A) : (term713 A s a) = (term776 A s a).
Proof. exact (MK_COMB (@lem4116699 A) (@lem4116698 A s a)). Qed.
Lemma lem4116701 {A : Type'} (P : A -> Prop) : (term749 A P) = (term692 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4116702 {A : Type'} (s : A -> Prop) : (term777 A s) = (term778 A s).
Proof. exact (@lem4116701 A (term714 A s)). Qed.
Lemma lem4116703 {A : Type'} (s : A -> Prop) (a : A) : (term779 A s a) = (term713 A s a).
Proof. exact (eq_refl (term779 A s a)). Qed.
Lemma lem4116704 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4116705 {A : Type'} (s : A -> Prop) (a : A) : (term780 A s a) = (term768 A s a).
Proof. exact (MK_COMB (@lem4116704) (@lem4116703 A s a)). Qed.
Lemma lem4116706 {A : Type'} (s : A -> Prop) (a : A) : (term780 A s a) = (term774 A s a).
Proof. exact (TRANS (@lem4116705 A s a) (@lem4116697 A s a)). Qed.
Lemma lem4116707 {A : Type'} (s : A -> Prop) : (term781 A s) = (term782 A s).
Proof. exact (fun_ext (fun a : A => @lem4116706 A s a)). Qed.
Lemma lem4116708 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116709 {A : Type'} (s : A -> Prop) : (term778 A s) = (term783 A s).
Proof. exact (MK_COMB (@lem4116708 A) (@lem4116707 A s)). Qed.
Lemma lem4116710 {A : Type'} (s : A -> Prop) : (term777 A s) = (term783 A s).
Proof. exact (TRANS (@lem4116702 A s) (@lem4116709 A s)). Qed.
Lemma lem4116711 {A : Type'} (s : A -> Prop) : (term714 A s) = (term784 A s).
Proof. exact (fun_ext (fun a : A => @lem4116700 A s a)). Qed.
Lemma lem4116712 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116713 {A : Type'} (s : A -> Prop) : (term715 A s) = (term785 A s).
Proof. exact (MK_COMB (@lem4116712 A) (@lem4116711 A s)). Qed.
Lemma lem4116714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4116715 {A : Type'} (s : A -> Prop) : (term786 A s) = (term787 A s).
Proof. exact (MK_COMB (@lem4116714) (@lem4116670 A s)). Qed.
Lemma lem4116716 {A : Type'} (s : A -> Prop) : (term788 A s) = (term789 A s).
Proof. exact (MK_COMB (@lem4116715 A s) (@lem4116713 A s)). Qed.
Lemma lem4116717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4116718 {A : Type'} (s : A -> Prop) : (term790 A s) = (term791 A s).
Proof. exact (MK_COMB (@lem4116717) (@lem4116673 A s)). Qed.
Lemma lem4116719 {A : Type'} (s : A -> Prop) : (term792 A s) = (term793 A s).
Proof. exact (MK_COMB (@lem4116718 A s) (@lem4116710 A s)). Qed.
Lemma lem4116720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4116721 {A : Type'} (s : A -> Prop) : (term794 A s) = (term795 A s).
Proof. exact (MK_COMB (@lem4116720) (@lem4116719 A s)). Qed.
Lemma lem4116722 {A : Type'} (s : A -> Prop) : (term796 A s) = (term797 A s).
Proof. exact (MK_COMB (@lem4116721 A s) (@lem4116716 A s)). Qed.
Lemma lem4116723 {A : Type'} (s : A -> Prop) : (term718 A s) = (term796 A s).
Proof. exact (@lem17646 (term705 A s) (term715 A s)). Qed.
Lemma lem4116724 {A : Type'} (s : A -> Prop) : (term718 A s) = (term797 A s).
Proof. exact (TRANS (@lem4116723 A s) (@lem4116722 A s)). Qed.
Lemma lem4116734 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term798 A P Q) = (term799 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4116735 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term798 A P Q) = (term799 A P Q).
Proof. exact (@lem4116734 A P Q). Qed.
Lemma lem4116736 {A : Type'} (s : A -> Prop) (a : A) : (term800 A s a) = (term801 A s a).
Proof. exact (@lem4116735 A (term802 A s a) (term775 A s a)). Qed.
Lemma lem4116737 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term803 A s a x) = (term804 A s x a).
Proof. exact (eq_refl (term803 A s a x)). Qed.
Lemma lem4116738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4116739 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term805 A s a x) = (term806 A s x a).
Proof. exact (MK_COMB (@lem4116738) (@lem4116737 A s x a)). Qed.
Lemma lem4116740 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term807 A s a x) = (term767 A s x a).
Proof. exact (eq_refl (term807 A s a x)). Qed.
Lemma lem4116741 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term808 A s a x) = (term739 A s x a).
Proof. exact (MK_COMB (@lem4116739 A s x a) (@lem4116740 A s x a)). Qed.
Lemma lem4116742 {A : Type'} (s : A -> Prop) (a : A) : (term809 A s a) = (term747 A s a).
Proof. exact (fun_ext (fun x : A => @lem4116741 A s x a)). Qed.
Lemma lem4116743 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116744 {A : Type'} (s : A -> Prop) (a : A) : (term800 A s a) = (term748 A s a).
Proof. exact (MK_COMB (@lem4116743 A) (@lem4116742 A s a)). Qed.
Lemma lem4116745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4116746 {A : Type'} (s : A -> Prop) (a : A) : (term810 A s a) = (term811 A s a).
Proof. exact (MK_COMB (@lem4116745) (@lem4116744 A s a)). Qed.
Lemma lem4116747 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term803 A s a x) = (term804 A s x a).
Proof. exact (eq_refl (term803 A s a x)). Qed.
Lemma lem4116748 {A : Type'} (s : A -> Prop) (a : A) : (term812 A s a) = (term802 A s a).
Proof. exact (fun_ext (fun x : A => @lem4116747 A s x a)). Qed.
Lemma lem4116749 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116750 {A : Type'} (s : A -> Prop) (a : A) : (term813 A s a) = (term814 A s a).
Proof. exact (MK_COMB (@lem4116749 A) (@lem4116748 A s a)). Qed.
Lemma lem4116751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4116752 {A : Type'} (s : A -> Prop) (a : A) : (term815 A s a) = (term816 A s a).
Proof. exact (MK_COMB (@lem4116751) (@lem4116750 A s a)). Qed.
Lemma lem4116753 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term807 A s a x) = (term767 A s x a).
Proof. exact (eq_refl (term807 A s a x)). Qed.
Lemma lem4116754 {A : Type'} (s : A -> Prop) (a : A) : (term817 A s a) = (term775 A s a).
Proof. exact (fun_ext (fun x : A => @lem4116753 A s x a)). Qed.
Lemma lem4116755 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4116756 {A : Type'} (s : A -> Prop) (a : A) : (term818 A s a) = (term776 A s a).
Proof. exact (MK_COMB (@lem4116755 A) (@lem4116754 A s a)). Qed.
Lemma lem4116757 {A : Type'} (s : A -> Prop) (a : A) : (term801 A s a) = (term819 A s a).
Proof. exact (MK_COMB (@lem4116752 A s a) (@lem4116756 A s a)). Qed.
Lemma lem4116758 {A : Type'} (s : A -> Prop) (a : A) : ((term800 A s a) = (term801 A s a)) = ((term748 A s a) = (term819 A s a)).
Proof. exact (MK_COMB (@lem4116746 A s a) (@lem4116757 A s a)). Qed.
Lemma lem4116759 {A : Type'} (s : A -> Prop) (a : A) : (term748 A s a) = (term819 A s a).
Proof. exact (EQ_MP (@lem4116758 A s a) (@lem4116736 A s a)). Qed.
Lemma lem4116836 {A : Type'} (s : A -> Prop) : (term757 A s) = (term820 A s).
Proof. exact (fun_ext (fun a : A => @lem4116759 A s a)). Qed.
Lemma lem4116837 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4116838 {A : Type'} (s : A -> Prop) : (term758 A s) = (term821 A s).
Proof. exact (MK_COMB (@lem4116837 A) (@lem4116836 A s)). Qed.
Lemma lem4116887 {A : Type'} (s : A -> Prop) : (term693 A s) = (term693 A s).
Proof. exact (eq_refl (term693 A s)). Qed.
Lemma lem4116888 {A : Type'} (s : A -> Prop) : (term764 A s) = (term822 A s).
Proof. exact (MK_COMB (@lem4116887 A s) (@lem4116838 A s)). Qed.
Lemma lem4116889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4116890 {A : Type'} (s : A -> Prop) : (term791 A s) = (term823 A s).
Proof. exact (MK_COMB (@lem4116889) (@lem4116888 A s)). Qed.
Lemma lem4116923 {A : Type'} (s : A -> Prop) : (term783 A s) = (term783 A s).
Proof. exact (eq_refl (term783 A s)). Qed.
Lemma lem4116924 {A : Type'} (s : A -> Prop) : (term793 A s) = (term824 A s).
Proof. exact (MK_COMB (@lem4116890 A s) (@lem4116923 A s)). Qed.
Lemma lem4116925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4116926 {A : Type'} (s : A -> Prop) : (term795 A s) = (term825 A s).
Proof. exact (MK_COMB (@lem4116925) (@lem4116924 A s)). Qed.
Lemma lem4117035 {A : Type'} (s : A -> Prop) : (term789 A s) = (term789 A s).
Proof. exact (eq_refl (term789 A s)). Qed.
Lemma lem4117036 {A : Type'} (s : A -> Prop) : (term797 A s) = (term826 A s).
Proof. exact (MK_COMB (@lem4116926 A s) (@lem4117035 A s)). Qed.
Lemma lem4117038 {A : Type'} (P : Prop) (Q : A -> Prop) : (term827 A P Q) = (term828 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4117039 {A : Type'} (P : Prop) (Q : A -> Prop) : (term827 A P Q) = (term828 A P Q).
Proof. exact (@lem4117038 A P Q). Qed.
Lemma lem4117040 {A : Type'} (s : A -> Prop) : (term829 A s) = (term830 A s).
Proof. exact (@lem4117039 A (term692 A s) (term820 A s)). Qed.
Lemma lem4117041 {A : Type'} (s : A -> Prop) (a : A) : (term831 A s a) = (term819 A s a).
Proof. exact (eq_refl (term831 A s a)). Qed.
Lemma lem4117042 {A : Type'} (s : A -> Prop) : (term832 A s) = (term820 A s).
Proof. exact (fun_ext (fun a : A => @lem4117041 A s a)). Qed.
Lemma lem4117043 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117044 {A : Type'} (s : A -> Prop) : (term833 A s) = (term821 A s).
Proof. exact (MK_COMB (@lem4117043 A) (@lem4117042 A s)). Qed.
Lemma lem4117045 {A : Type'} (s : A -> Prop) : (term693 A s) = (term693 A s).
Proof. exact (eq_refl (term693 A s)). Qed.
Lemma lem4117046 {A : Type'} (s : A -> Prop) : (term829 A s) = (term822 A s).
Proof. exact (MK_COMB (@lem4117045 A s) (@lem4117044 A s)). Qed.
Lemma lem4117047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117048 {A : Type'} (s : A -> Prop) : (term834 A s) = (term835 A s).
Proof. exact (MK_COMB (@lem4117047) (@lem4117046 A s)). Qed.
Lemma lem4117049 {A : Type'} (s : A -> Prop) (a : A) : (term831 A s a) = (term819 A s a).
Proof. exact (eq_refl (term831 A s a)). Qed.
Lemma lem4117050 {A : Type'} (s : A -> Prop) : (term693 A s) = (term693 A s).
Proof. exact (eq_refl (term693 A s)). Qed.
Lemma lem4117051 {A : Type'} (s : A -> Prop) (a : A) : (term836 A s a) = (term837 A s a).
Proof. exact (MK_COMB (@lem4117050 A s) (@lem4117049 A s a)). Qed.
Lemma lem4117052 {A : Type'} (s : A -> Prop) : (term838 A s) = (term839 A s).
Proof. exact (fun_ext (fun a : A => @lem4117051 A s a)). Qed.
Lemma lem4117053 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117054 {A : Type'} (s : A -> Prop) : (term830 A s) = (term840 A s).
Proof. exact (MK_COMB (@lem4117053 A) (@lem4117052 A s)). Qed.
Lemma lem4117055 {A : Type'} (s : A -> Prop) : ((term829 A s) = (term830 A s)) = ((term822 A s) = (term840 A s)).
Proof. exact (MK_COMB (@lem4117048 A s) (@lem4117054 A s)). Qed.
Lemma lem4117056 {A : Type'} (s : A -> Prop) : (term822 A s) = (term840 A s).
Proof. exact (EQ_MP (@lem4117055 A s) (@lem4117040 A s)). Qed.
Lemma lem4117057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4117058 {A : Type'} (s : A -> Prop) : (term823 A s) = (term841 A s).
Proof. exact (MK_COMB (@lem4117057) (@lem4117056 A s)). Qed.
Lemma lem4117060 {A B : Type'} (P : type1413 A B) : (term842 A B P) = (term843 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4117061 {A : Type'} (P : type1402 A) : (term844 A P) = (term845 A P).
Proof. exact (@lem4117060 A A P). Qed.
Lemma lem4117062 {A : Type'} (s : A -> Prop) : (term846 A s) = (term847 A s).
Proof. exact (@lem4117061 A (term848 A s)). Qed.
Lemma lem4117063 {A : Type'} (s : A -> Prop) (a : A) : (term849 A s a) = (term773 A s a).
Proof. exact (eq_refl (term849 A s a)). Qed.
Lemma lem4117064 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4117065 {A : Type'} (s : A -> Prop) (a : A) (x : A) : (term850 A s a x) = (term851 A s a x).
Proof. exact (MK_COMB (@lem4117063 A s a) (@lem4117064 A x)). Qed.
Lemma lem4117066 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term851 A s a x) = (term766 A s x a).
Proof. exact (eq_refl (term851 A s a x)). Qed.
Lemma lem4117067 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term850 A s a x) = (term766 A s x a).
Proof. exact (TRANS (@lem4117065 A s a x) (@lem4117066 A s x a)). Qed.
Lemma lem4117068 {A : Type'} (s : A -> Prop) (a : A) : (term852 A s a) = (term773 A s a).
Proof. exact (fun_ext (fun x : A => @lem4117067 A s x a)). Qed.
Lemma lem4117069 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117070 {A : Type'} (s : A -> Prop) (a : A) : (term853 A s a) = (term774 A s a).
Proof. exact (MK_COMB (@lem4117069 A) (@lem4117068 A s a)). Qed.
Lemma lem4117071 {A : Type'} (s : A -> Prop) : (term854 A s) = (term782 A s).
Proof. exact (fun_ext (fun a : A => @lem4117070 A s a)). Qed.
Lemma lem4117072 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117073 {A : Type'} (s : A -> Prop) : (term846 A s) = (term783 A s).
Proof. exact (MK_COMB (@lem4117072 A) (@lem4117071 A s)). Qed.
Lemma lem4117074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117075 {A : Type'} (s : A -> Prop) : (term855 A s) = (term856 A s).
Proof. exact (MK_COMB (@lem4117074) (@lem4117073 A s)). Qed.
Lemma lem4117076 {A : Type'} (s : A -> Prop) (a : A) : (term849 A s a) = (term773 A s a).
Proof. exact (eq_refl (term849 A s a)). Qed.
Lemma lem4117077 {A : Type'} (x : A -> A) (a : A) : (x a) = (x a).
Proof. exact (eq_refl (x a)). Qed.
Lemma lem4117078 {A : Type'} (s : A -> Prop) (x : A -> A) (a : A) : (term857 A s x a) = (term858 A s x a).
Proof. exact (MK_COMB (@lem4117076 A s a) (@lem4117077 A x a)). Qed.
Lemma lem4117079 {A : Type'} (s : A -> Prop) (x : A -> A) (a : A) : (term858 A s x a) = (term859 A s x a).
Proof. exact (eq_refl (term858 A s x a)). Qed.
Lemma lem4117080 {A : Type'} (s : A -> Prop) (x : A -> A) (a : A) : (term857 A s x a) = (term859 A s x a).
Proof. exact (TRANS (@lem4117078 A s x a) (@lem4117079 A s x a)). Qed.
Lemma lem4117081 {A : Type'} (s : A -> Prop) (x : A -> A) : (term860 A s x) = (term861 A s x).
Proof. exact (fun_ext (fun a : A => @lem4117080 A s x a)). Qed.
Lemma lem4117082 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117083 {A : Type'} (s : A -> Prop) (x : A -> A) : (term862 A s x) = (term863 A s x).
Proof. exact (MK_COMB (@lem4117082 A) (@lem4117081 A s x)). Qed.
Lemma lem4117084 {A : Type'} (s : A -> Prop) : (term864 A s) = (term865 A s).
Proof. exact (fun_ext (fun x : A -> A => @lem4117083 A s x)). Qed.
Lemma lem4117085 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117086 {A : Type'} (s : A -> Prop) : (term847 A s) = (term866 A s).
Proof. exact (MK_COMB (@lem4117085 A) (@lem4117084 A s)). Qed.
Lemma lem4117087 {A : Type'} (s : A -> Prop) : ((term846 A s) = (term847 A s)) = ((term783 A s) = (term866 A s)).
Proof. exact (MK_COMB (@lem4117075 A s) (@lem4117086 A s)). Qed.
Lemma lem4117088 {A : Type'} (s : A -> Prop) : (term783 A s) = (term866 A s).
Proof. exact (EQ_MP (@lem4117087 A s) (@lem4117062 A s)). Qed.
Lemma lem4117089 {A : Type'} (s : A -> Prop) : (term824 A s) = (term867 A s).
Proof. exact (MK_COMB (@lem4117058 A s) (@lem4117088 A s)). Qed.
Lemma lem4117091 {A : Type'} (P : A -> Prop) (Q : Prop) : (term868 A P Q) = (term869 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4117092 {A : Type'} (P : A -> Prop) (Q : Prop) : (term868 A P Q) = (term869 A P Q).
Proof. exact (@lem4117091 A P Q). Qed.
Lemma lem4117093 {A : Type'} (s : A -> Prop) : (term870 A s) = (term871 A s).
Proof. exact (@lem4117092 A (term839 A s) (term866 A s)). Qed.
Lemma lem4117094 {A : Type'} (s : A -> Prop) (a : A) : (term872 A s a) = (term837 A s a).
Proof. exact (eq_refl (term872 A s a)). Qed.
Lemma lem4117095 {A : Type'} (s : A -> Prop) : (term873 A s) = (term839 A s).
Proof. exact (fun_ext (fun a : A => @lem4117094 A s a)). Qed.
Lemma lem4117096 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117097 {A : Type'} (s : A -> Prop) : (term874 A s) = (term840 A s).
Proof. exact (MK_COMB (@lem4117096 A) (@lem4117095 A s)). Qed.
Lemma lem4117098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4117099 {A : Type'} (s : A -> Prop) : (term875 A s) = (term841 A s).
Proof. exact (MK_COMB (@lem4117098) (@lem4117097 A s)). Qed.
Lemma lem4117100 {A : Type'} (s : A -> Prop) : (term866 A s) = (term866 A s).
Proof. exact (eq_refl (term866 A s)). Qed.
Lemma lem4117101 {A : Type'} (s : A -> Prop) : (term870 A s) = (term867 A s).
Proof. exact (MK_COMB (@lem4117099 A s) (@lem4117100 A s)). Qed.
Lemma lem4117102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117103 {A : Type'} (s : A -> Prop) : (term876 A s) = (term877 A s).
Proof. exact (MK_COMB (@lem4117102) (@lem4117101 A s)). Qed.
Lemma lem4117104 {A : Type'} (s : A -> Prop) (a : A) : (term872 A s a) = (term837 A s a).
Proof. exact (eq_refl (term872 A s a)). Qed.
Lemma lem4117105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4117106 {A : Type'} (s : A -> Prop) (a : A) : (term878 A s a) = (term879 A s a).
Proof. exact (MK_COMB (@lem4117105) (@lem4117104 A s a)). Qed.
Lemma lem4117107 {A : Type'} (s : A -> Prop) : (term866 A s) = (term866 A s).
Proof. exact (eq_refl (term866 A s)). Qed.
Lemma lem4117108 {A : Type'} (a : A) (s : A -> Prop) : (term880 A a s) = (term881 A a s).
Proof. exact (MK_COMB (@lem4117106 A s a) (@lem4117107 A s)). Qed.
Lemma lem4117109 {A : Type'} (s : A -> Prop) : (term882 A s) = (term883 A s).
Proof. exact (fun_ext (fun a : A => @lem4117108 A a s)). Qed.
Lemma lem4117110 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117111 {A : Type'} (s : A -> Prop) : (term871 A s) = (term884 A s).
Proof. exact (MK_COMB (@lem4117110 A) (@lem4117109 A s)). Qed.
Lemma lem4117112 {A : Type'} (s : A -> Prop) : ((term870 A s) = (term871 A s)) = ((term867 A s) = (term884 A s)).
Proof. exact (MK_COMB (@lem4117103 A s) (@lem4117111 A s)). Qed.
Lemma lem4117113 {A : Type'} (s : A -> Prop) : (term867 A s) = (term884 A s).
Proof. exact (EQ_MP (@lem4117112 A s) (@lem4117093 A s)). Qed.
Lemma lem4117115 {A : Type'} (P : Prop) (Q : A -> Prop) : (term885 A P Q) = (term886 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4117116 {A : Type'} (P : Prop) (Q : type488 A) : (term887 A P Q) = (term888 A P Q).
Proof. exact (@lem4117115 (A -> A) P Q). Qed.
Lemma lem4117117 {A : Type'} (a : A) (s : A -> Prop) : (term889 A a s) = (term890 A a s).
Proof. exact (@lem4117116 A (term837 A s a) (term865 A s)). Qed.
Lemma lem4117118 {A : Type'} (s : A -> Prop) (x : A -> A) : (term891 A s x) = (term863 A s x).
Proof. exact (eq_refl (term891 A s x)). Qed.
Lemma lem4117119 {A : Type'} (s : A -> Prop) : (term892 A s) = (term865 A s).
Proof. exact (fun_ext (fun x : A -> A => @lem4117118 A s x)). Qed.
Lemma lem4117120 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117121 {A : Type'} (s : A -> Prop) : (term893 A s) = (term866 A s).
Proof. exact (MK_COMB (@lem4117120 A) (@lem4117119 A s)). Qed.
Lemma lem4117122 {A : Type'} (s : A -> Prop) (a : A) : (term879 A s a) = (term879 A s a).
Proof. exact (eq_refl (term879 A s a)). Qed.
Lemma lem4117123 {A : Type'} (a : A) (s : A -> Prop) : (term889 A a s) = (term881 A a s).
Proof. exact (MK_COMB (@lem4117122 A s a) (@lem4117121 A s)). Qed.
Lemma lem4117124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117125 {A : Type'} (a : A) (s : A -> Prop) : (term894 A a s) = (term895 A a s).
Proof. exact (MK_COMB (@lem4117124) (@lem4117123 A a s)). Qed.
Lemma lem4117126 {A : Type'} (s : A -> Prop) (x : A -> A) : (term891 A s x) = (term863 A s x).
Proof. exact (eq_refl (term891 A s x)). Qed.
Lemma lem4117127 {A : Type'} (s : A -> Prop) (a : A) : (term879 A s a) = (term879 A s a).
Proof. exact (eq_refl (term879 A s a)). Qed.
Lemma lem4117128 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) : (term896 A a s x) = (term897 A a s x).
Proof. exact (MK_COMB (@lem4117127 A s a) (@lem4117126 A s x)). Qed.
Lemma lem4117129 {A : Type'} (a : A) (s : A -> Prop) : (term898 A a s) = (term899 A a s).
Proof. exact (fun_ext (fun x : A -> A => @lem4117128 A a s x)). Qed.
Lemma lem4117130 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117131 {A : Type'} (a : A) (s : A -> Prop) : (term890 A a s) = (term900 A a s).
Proof. exact (MK_COMB (@lem4117130 A) (@lem4117129 A a s)). Qed.
Lemma lem4117132 {A : Type'} (a : A) (s : A -> Prop) : ((term889 A a s) = (term890 A a s)) = ((term881 A a s) = (term900 A a s)).
Proof. exact (MK_COMB (@lem4117125 A a s) (@lem4117131 A a s)). Qed.
Lemma lem4117133 {A : Type'} (a : A) (s : A -> Prop) : (term881 A a s) = (term900 A a s).
Proof. exact (EQ_MP (@lem4117132 A a s) (@lem4117117 A a s)). Qed.
Lemma lem4117134 {A : Type'} (s : A -> Prop) : (term883 A s) = (term901 A s).
Proof. exact (fun_ext (fun a : A => @lem4117133 A a s)). Qed.
Lemma lem4117135 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117136 {A : Type'} (s : A -> Prop) : (term884 A s) = (term902 A s).
Proof. exact (MK_COMB (@lem4117135 A) (@lem4117134 A s)). Qed.
Lemma lem4117137 {A : Type'} (s : A -> Prop) : (term867 A s) = (term902 A s).
Proof. exact (TRANS (@lem4117113 A s) (@lem4117136 A s)). Qed.
Lemma lem4117138 {A : Type'} (s : A -> Prop) : (term824 A s) = (term902 A s).
Proof. exact (TRANS (@lem4117089 A s) (@lem4117137 A s)). Qed.
Lemma lem4117139 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4117140 {A : Type'} (s : A -> Prop) : (term825 A s) = (term903 A s).
Proof. exact (MK_COMB (@lem4117139) (@lem4117138 A s)). Qed.
Lemma lem4117142 {A B : Type'} (P : type1413 A B) : (term842 A B P) = (term843 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4117143 {A : Type'} (P : type1402 A) : (term844 A P) = (term845 A P).
Proof. exact (@lem4117142 A A P). Qed.
Lemma lem4117144 {A : Type'} (s : A -> Prop) : (term904 A s) = (term905 A s).
Proof. exact (@lem4117143 A (term906 A s)). Qed.
Lemma lem4117145 {A : Type'} (s : A -> Prop) (a : A) : (term907 A s a) = (term745 A s a).
Proof. exact (eq_refl (term907 A s a)). Qed.
Lemma lem4117146 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4117147 {A : Type'} (s : A -> Prop) (a : A) (x : A) : (term908 A s a x) = (term909 A s a x).
Proof. exact (MK_COMB (@lem4117145 A s a) (@lem4117146 A x)). Qed.
Lemma lem4117148 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term909 A s a x) = (term738 A s x a).
Proof. exact (eq_refl (term909 A s a x)). Qed.
Lemma lem4117149 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term908 A s a x) = (term738 A s x a).
Proof. exact (TRANS (@lem4117147 A s a x) (@lem4117148 A s x a)). Qed.
Lemma lem4117150 {A : Type'} (s : A -> Prop) (a : A) : (term910 A s a) = (term745 A s a).
Proof. exact (fun_ext (fun x : A => @lem4117149 A s x a)). Qed.
Lemma lem4117151 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117152 {A : Type'} (s : A -> Prop) (a : A) : (term911 A s a) = (term746 A s a).
Proof. exact (MK_COMB (@lem4117151 A) (@lem4117150 A s a)). Qed.
Lemma lem4117153 {A : Type'} (s : A -> Prop) : (term912 A s) = (term755 A s).
Proof. exact (fun_ext (fun a : A => @lem4117152 A s a)). Qed.
Lemma lem4117154 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117155 {A : Type'} (s : A -> Prop) : (term904 A s) = (term756 A s).
Proof. exact (MK_COMB (@lem4117154 A) (@lem4117153 A s)). Qed.
Lemma lem4117156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117157 {A : Type'} (s : A -> Prop) : (term913 A s) = (term914 A s).
Proof. exact (MK_COMB (@lem4117156) (@lem4117155 A s)). Qed.
Lemma lem4117158 {A : Type'} (s : A -> Prop) (a : A) : (term907 A s a) = (term745 A s a).
Proof. exact (eq_refl (term907 A s a)). Qed.
Lemma lem4117159 {A : Type'} (x : A -> A) (a : A) : (x a) = (x a).
Proof. exact (eq_refl (x a)). Qed.
Lemma lem4117160 {A : Type'} (s : A -> Prop) (x : A -> A) (a : A) : (term915 A s x a) = (term916 A s x a).
Proof. exact (MK_COMB (@lem4117158 A s a) (@lem4117159 A x a)). Qed.
Lemma lem4117161 {A : Type'} (s : A -> Prop) (x : A -> A) (a : A) : (term916 A s x a) = (term917 A s x a).
Proof. exact (eq_refl (term916 A s x a)). Qed.
Lemma lem4117162 {A : Type'} (s : A -> Prop) (x : A -> A) (a : A) : (term915 A s x a) = (term917 A s x a).
Proof. exact (TRANS (@lem4117160 A s x a) (@lem4117161 A s x a)). Qed.
Lemma lem4117163 {A : Type'} (s : A -> Prop) (x : A -> A) : (term918 A s x) = (term919 A s x).
Proof. exact (fun_ext (fun a : A => @lem4117162 A s x a)). Qed.
Lemma lem4117164 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117165 {A : Type'} (s : A -> Prop) (x : A -> A) : (term920 A s x) = (term921 A s x).
Proof. exact (MK_COMB (@lem4117164 A) (@lem4117163 A s x)). Qed.
Lemma lem4117166 {A : Type'} (s : A -> Prop) : (term922 A s) = (term923 A s).
Proof. exact (fun_ext (fun x : A -> A => @lem4117165 A s x)). Qed.
Lemma lem4117167 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117168 {A : Type'} (s : A -> Prop) : (term905 A s) = (term924 A s).
Proof. exact (MK_COMB (@lem4117167 A) (@lem4117166 A s)). Qed.
Lemma lem4117169 {A : Type'} (s : A -> Prop) : ((term904 A s) = (term905 A s)) = ((term756 A s) = (term924 A s)).
Proof. exact (MK_COMB (@lem4117157 A s) (@lem4117168 A s)). Qed.
Lemma lem4117170 {A : Type'} (s : A -> Prop) : (term756 A s) = (term924 A s).
Proof. exact (EQ_MP (@lem4117169 A s) (@lem4117144 A s)). Qed.
Lemma lem4117171 {A : Type'} (s : A -> Prop) : (term760 A s) = (term760 A s).
Proof. exact (eq_refl (term760 A s)). Qed.
Lemma lem4117172 {A : Type'} (s : A -> Prop) : (term762 A s) = (term925 A s).
Proof. exact (MK_COMB (@lem4117171 A s) (@lem4117170 A s)). Qed.
Lemma lem4117174 {A : Type'} (P : A -> Prop) (Q : Prop) : (term868 A P Q) = (term869 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4117175 {A : Type'} (P : A -> Prop) (Q : Prop) : (term868 A P Q) = (term869 A P Q).
Proof. exact (@lem4117174 A P Q). Qed.
Lemma lem4117176 {A : Type'} (s : A -> Prop) : (term925 A s) = (term926 A s).
Proof. exact (@lem4117175 A s (term924 A s)). Qed.
Lemma lem4117178 {A : Type'} (P : Prop) (Q : A -> Prop) : (term885 A P Q) = (term886 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4117179 {A : Type'} (P : Prop) (Q : type488 A) : (term887 A P Q) = (term888 A P Q).
Proof. exact (@lem4117178 (A -> A) P Q). Qed.
Lemma lem4117180 {A : Type'} (x : A) (s : A -> Prop) : (term927 A x s) = (term928 A x s).
Proof. exact (@lem4117179 A (s x) (term923 A s)). Qed.
Lemma lem4117181 {A : Type'} (s : A -> Prop) (x : A -> A) : (term929 A s x) = (term921 A s x).
Proof. exact (eq_refl (term929 A s x)). Qed.
Lemma lem4117182 {A : Type'} (s : A -> Prop) : (term930 A s) = (term923 A s).
Proof. exact (fun_ext (fun x : A -> A => @lem4117181 A s x)). Qed.
Lemma lem4117183 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117184 {A : Type'} (s : A -> Prop) : (term931 A s) = (term924 A s).
Proof. exact (MK_COMB (@lem4117183 A) (@lem4117182 A s)). Qed.
Lemma lem4117185 {A : Type'} (s : A -> Prop) (x : A) : (term932 A s x) = (term932 A s x).
Proof. exact (eq_refl (term932 A s x)). Qed.
Lemma lem4117186 {A : Type'} (x : A) (s : A -> Prop) : (term927 A x s) = (term933 A x s).
Proof. exact (MK_COMB (@lem4117185 A s x) (@lem4117184 A s)). Qed.
Lemma lem4117187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117188 {A : Type'} (x : A) (s : A -> Prop) : (term934 A x s) = (term935 A x s).
Proof. exact (MK_COMB (@lem4117187) (@lem4117186 A x s)). Qed.
Lemma lem4117189 {A : Type'} (s : A -> Prop) (x : A -> A) : (term929 A s x) = (term921 A s x).
Proof. exact (eq_refl (term929 A s x)). Qed.
Lemma lem4117190 {A : Type'} (s : A -> Prop) (x : A) : (term932 A s x) = (term932 A s x).
Proof. exact (eq_refl (term932 A s x)). Qed.
Lemma lem4117191 {A : Type'} (x : A) (s : A -> Prop) (x' : A -> A) : (term936 A x s x') = (term937 A x s x').
Proof. exact (MK_COMB (@lem4117190 A s x) (@lem4117189 A s x')). Qed.
Lemma lem4117192 {A : Type'} (x : A) (s : A -> Prop) : (term938 A x s) = (term939 A x s).
Proof. exact (fun_ext (fun x' : A -> A => @lem4117191 A x s x')). Qed.
Lemma lem4117193 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117194 {A : Type'} (x : A) (s : A -> Prop) : (term928 A x s) = (term940 A x s).
Proof. exact (MK_COMB (@lem4117193 A) (@lem4117192 A x s)). Qed.
Lemma lem4117195 {A : Type'} (x : A) (s : A -> Prop) : ((term927 A x s) = (term928 A x s)) = ((term933 A x s) = (term940 A x s)).
Proof. exact (MK_COMB (@lem4117188 A x s) (@lem4117194 A x s)). Qed.
Lemma lem4117196 {A : Type'} (x : A) (s : A -> Prop) : (term933 A x s) = (term940 A x s).
Proof. exact (EQ_MP (@lem4117195 A x s) (@lem4117180 A x s)). Qed.
Lemma lem4117197 {A : Type'} (s : A -> Prop) : (term941 A s) = (term942 A s).
Proof. exact (fun_ext (fun x : A => @lem4117196 A x s)). Qed.
Lemma lem4117198 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117199 {A : Type'} (s : A -> Prop) : (term926 A s) = (term943 A s).
Proof. exact (MK_COMB (@lem4117198 A) (@lem4117197 A s)). Qed.
Lemma lem4117200 {A : Type'} (s : A -> Prop) : (term925 A s) = (term943 A s).
Proof. exact (TRANS (@lem4117176 A s) (@lem4117199 A s)). Qed.
Lemma lem4117201 {A : Type'} (s : A -> Prop) : (term762 A s) = (term943 A s).
Proof. exact (TRANS (@lem4117172 A s) (@lem4117200 A s)). Qed.
Lemma lem4117202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4117203 {A : Type'} (s : A -> Prop) : (term787 A s) = (term944 A s).
Proof. exact (MK_COMB (@lem4117202) (@lem4117201 A s)). Qed.
Lemma lem4117204 {A : Type'} (s : A -> Prop) : (term785 A s) = (term785 A s).
Proof. exact (eq_refl (term785 A s)). Qed.
Lemma lem4117205 {A : Type'} (s : A -> Prop) : (term789 A s) = (term945 A s).
Proof. exact (MK_COMB (@lem4117203 A s) (@lem4117204 A s)). Qed.
Lemma lem4117207 {A : Type'} (P : A -> Prop) (Q : Prop) : (term868 A P Q) = (term869 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4117208 {A : Type'} (P : A -> Prop) (Q : Prop) : (term868 A P Q) = (term869 A P Q).
Proof. exact (@lem4117207 A P Q). Qed.
Lemma lem4117209 {A : Type'} (s : A -> Prop) : (term946 A s) = (term947 A s).
Proof. exact (@lem4117208 A (term942 A s) (term785 A s)). Qed.
Lemma lem4117210 {A : Type'} (x : A) (s : A -> Prop) : (term948 A s x) = (term940 A x s).
Proof. exact (eq_refl (term948 A s x)). Qed.
Lemma lem4117211 {A : Type'} (s : A -> Prop) : (term949 A s) = (term942 A s).
Proof. exact (fun_ext (fun x : A => @lem4117210 A x s)). Qed.
Lemma lem4117212 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117213 {A : Type'} (s : A -> Prop) : (term950 A s) = (term943 A s).
Proof. exact (MK_COMB (@lem4117212 A) (@lem4117211 A s)). Qed.
Lemma lem4117214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4117215 {A : Type'} (s : A -> Prop) : (term951 A s) = (term944 A s).
Proof. exact (MK_COMB (@lem4117214) (@lem4117213 A s)). Qed.
Lemma lem4117216 {A : Type'} (s : A -> Prop) : (term785 A s) = (term785 A s).
Proof. exact (eq_refl (term785 A s)). Qed.
Lemma lem4117217 {A : Type'} (s : A -> Prop) : (term946 A s) = (term945 A s).
Proof. exact (MK_COMB (@lem4117215 A s) (@lem4117216 A s)). Qed.
Lemma lem4117218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117219 {A : Type'} (s : A -> Prop) : (term952 A s) = (term953 A s).
Proof. exact (MK_COMB (@lem4117218) (@lem4117217 A s)). Qed.
Lemma lem4117220 {A : Type'} (x : A) (s : A -> Prop) : (term948 A s x) = (term940 A x s).
Proof. exact (eq_refl (term948 A s x)). Qed.
Lemma lem4117221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4117222 {A : Type'} (x : A) (s : A -> Prop) : (term954 A s x) = (term955 A x s).
Proof. exact (MK_COMB (@lem4117221) (@lem4117220 A x s)). Qed.
Lemma lem4117223 {A : Type'} (s : A -> Prop) : (term785 A s) = (term785 A s).
Proof. exact (eq_refl (term785 A s)). Qed.
Lemma lem4117224 {A : Type'} (x : A) (s : A -> Prop) : (term956 A x s) = (term957 A x s).
Proof. exact (MK_COMB (@lem4117222 A x s) (@lem4117223 A s)). Qed.
Lemma lem4117225 {A : Type'} (s : A -> Prop) : (term958 A s) = (term959 A s).
Proof. exact (fun_ext (fun x : A => @lem4117224 A x s)). Qed.
Lemma lem4117226 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117227 {A : Type'} (s : A -> Prop) : (term947 A s) = (term960 A s).
Proof. exact (MK_COMB (@lem4117226 A) (@lem4117225 A s)). Qed.
Lemma lem4117228 {A : Type'} (s : A -> Prop) : ((term946 A s) = (term947 A s)) = ((term945 A s) = (term960 A s)).
Proof. exact (MK_COMB (@lem4117219 A s) (@lem4117227 A s)). Qed.
Lemma lem4117229 {A : Type'} (s : A -> Prop) : (term945 A s) = (term960 A s).
Proof. exact (EQ_MP (@lem4117228 A s) (@lem4117209 A s)). Qed.
Lemma lem4117231 {A : Type'} (P : A -> Prop) (Q : Prop) : (term868 A P Q) = (term869 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4117232 {A : Type'} (P : type488 A) (Q : Prop) : (term961 A P Q) = (term962 A P Q).
Proof. exact (@lem4117231 (A -> A) P Q). Qed.
Lemma lem4117233 {A : Type'} (x : A) (s : A -> Prop) : (term963 A x s) = (term964 A x s).
Proof. exact (@lem4117232 A (term939 A x s) (term785 A s)). Qed.
Lemma lem4117234 {A : Type'} (x : A) (s : A -> Prop) (x' : A -> A) : (term965 A x s x') = (term937 A x s x').
Proof. exact (eq_refl (term965 A x s x')). Qed.
Lemma lem4117235 {A : Type'} (x : A) (s : A -> Prop) : (term966 A x s) = (term939 A x s).
Proof. exact (fun_ext (fun x' : A -> A => @lem4117234 A x s x')). Qed.
Lemma lem4117236 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117237 {A : Type'} (x : A) (s : A -> Prop) : (term967 A x s) = (term940 A x s).
Proof. exact (MK_COMB (@lem4117236 A) (@lem4117235 A x s)). Qed.
Lemma lem4117238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4117239 {A : Type'} (x : A) (s : A -> Prop) : (term968 A x s) = (term955 A x s).
Proof. exact (MK_COMB (@lem4117238) (@lem4117237 A x s)). Qed.
Lemma lem4117240 {A : Type'} (s : A -> Prop) : (term785 A s) = (term785 A s).
Proof. exact (eq_refl (term785 A s)). Qed.
Lemma lem4117241 {A : Type'} (x : A) (s : A -> Prop) : (term963 A x s) = (term957 A x s).
Proof. exact (MK_COMB (@lem4117239 A x s) (@lem4117240 A s)). Qed.
Lemma lem4117242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117243 {A : Type'} (x : A) (s : A -> Prop) : (term969 A x s) = (term970 A x s).
Proof. exact (MK_COMB (@lem4117242) (@lem4117241 A x s)). Qed.
Lemma lem4117244 {A : Type'} (x : A) (s : A -> Prop) (x' : A -> A) : (term965 A x s x') = (term937 A x s x').
Proof. exact (eq_refl (term965 A x s x')). Qed.
Lemma lem4117245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4117246 {A : Type'} (x : A) (s : A -> Prop) (x' : A -> A) : (term971 A x s x') = (term972 A x s x').
Proof. exact (MK_COMB (@lem4117245) (@lem4117244 A x s x')). Qed.
Lemma lem4117247 {A : Type'} (s : A -> Prop) : (term785 A s) = (term785 A s).
Proof. exact (eq_refl (term785 A s)). Qed.
Lemma lem4117248 {A : Type'} (x : A) (x' : A -> A) (s : A -> Prop) : (term973 A x x' s) = (term974 A x x' s).
Proof. exact (MK_COMB (@lem4117246 A x s x') (@lem4117247 A s)). Qed.
Lemma lem4117249 {A : Type'} (x : A) (s : A -> Prop) : (term975 A x s) = (term976 A x s).
Proof. exact (fun_ext (fun x' : A -> A => @lem4117248 A x x' s)). Qed.
Lemma lem4117250 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117251 {A : Type'} (x : A) (s : A -> Prop) : (term964 A x s) = (term977 A x s).
Proof. exact (MK_COMB (@lem4117250 A) (@lem4117249 A x s)). Qed.
Lemma lem4117252 {A : Type'} (x : A) (s : A -> Prop) : ((term963 A x s) = (term964 A x s)) = ((term957 A x s) = (term977 A x s)).
Proof. exact (MK_COMB (@lem4117243 A x s) (@lem4117251 A x s)). Qed.
Lemma lem4117253 {A : Type'} (x : A) (s : A -> Prop) : (term957 A x s) = (term977 A x s).
Proof. exact (EQ_MP (@lem4117252 A x s) (@lem4117233 A x s)). Qed.
Lemma lem4117255 {A : Type'} (P : Prop) (Q : A -> Prop) : (term885 A P Q) = (term886 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4117256 {A : Type'} (P : Prop) (Q : A -> Prop) : (term885 A P Q) = (term886 A P Q).
Proof. exact (@lem4117255 A P Q). Qed.
Lemma lem4117257 {A : Type'} (x : A) (x' : A -> A) (s : A -> Prop) : (term978 A x x' s) = (term979 A x x' s).
Proof. exact (@lem4117256 A (term937 A x s x') (term784 A s)). Qed.
Lemma lem4117258 {A : Type'} (s : A -> Prop) (a : A) : (term980 A s a) = (term776 A s a).
Proof. exact (eq_refl (term980 A s a)). Qed.
Lemma lem4117259 {A : Type'} (s : A -> Prop) : (term981 A s) = (term784 A s).
Proof. exact (fun_ext (fun a : A => @lem4117258 A s a)). Qed.
Lemma lem4117260 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117261 {A : Type'} (s : A -> Prop) : (term982 A s) = (term785 A s).
Proof. exact (MK_COMB (@lem4117260 A) (@lem4117259 A s)). Qed.
Lemma lem4117262 {A : Type'} (x : A) (s : A -> Prop) (x' : A -> A) : (term972 A x s x') = (term972 A x s x').
Proof. exact (eq_refl (term972 A x s x')). Qed.
Lemma lem4117263 {A : Type'} (x : A) (x' : A -> A) (s : A -> Prop) : (term978 A x x' s) = (term974 A x x' s).
Proof. exact (MK_COMB (@lem4117262 A x s x') (@lem4117261 A s)). Qed.
Lemma lem4117264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117265 {A : Type'} (x : A) (x' : A -> A) (s : A -> Prop) : (term983 A x x' s) = (term984 A x x' s).
Proof. exact (MK_COMB (@lem4117264) (@lem4117263 A x x' s)). Qed.
Lemma lem4117266 {A : Type'} (s : A -> Prop) (a : A) : (term980 A s a) = (term776 A s a).
Proof. exact (eq_refl (term980 A s a)). Qed.
Lemma lem4117267 {A : Type'} (x : A) (s : A -> Prop) (x' : A -> A) : (term972 A x s x') = (term972 A x s x').
Proof. exact (eq_refl (term972 A x s x')). Qed.
Lemma lem4117268 {A : Type'} (x : A) (x' : A -> A) (s : A -> Prop) (a : A) : (term985 A x x' s a) = (term986 A x x' s a).
Proof. exact (MK_COMB (@lem4117267 A x s x') (@lem4117266 A s a)). Qed.
Lemma lem4117269 {A : Type'} (x : A) (x' : A -> A) (s : A -> Prop) : (term987 A x x' s) = (term988 A x x' s).
Proof. exact (fun_ext (fun a : A => @lem4117268 A x x' s a)). Qed.
Lemma lem4117270 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117271 {A : Type'} (x : A) (x' : A -> A) (s : A -> Prop) : (term979 A x x' s) = (term989 A x x' s).
Proof. exact (MK_COMB (@lem4117270 A) (@lem4117269 A x x' s)). Qed.
Lemma lem4117272 {A : Type'} (x : A) (x' : A -> A) (s : A -> Prop) : ((term978 A x x' s) = (term979 A x x' s)) = ((term974 A x x' s) = (term989 A x x' s)).
Proof. exact (MK_COMB (@lem4117265 A x x' s) (@lem4117271 A x x' s)). Qed.
Lemma lem4117273 {A : Type'} (x : A) (x' : A -> A) (s : A -> Prop) : (term974 A x x' s) = (term989 A x x' s).
Proof. exact (EQ_MP (@lem4117272 A x x' s) (@lem4117257 A x x' s)). Qed.
Lemma lem4117274 {A : Type'} (x : A) (s : A -> Prop) : (term976 A x s) = (term990 A x s).
Proof. exact (fun_ext (fun x' : A -> A => @lem4117273 A x x' s)). Qed.
Lemma lem4117275 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117276 {A : Type'} (x : A) (s : A -> Prop) : (term977 A x s) = (term991 A x s).
Proof. exact (MK_COMB (@lem4117275 A) (@lem4117274 A x s)). Qed.
Lemma lem4117277 {A : Type'} (x : A) (s : A -> Prop) : (term957 A x s) = (term991 A x s).
Proof. exact (TRANS (@lem4117253 A x s) (@lem4117276 A x s)). Qed.
Lemma lem4117278 {A : Type'} (s : A -> Prop) : (term959 A s) = (term992 A s).
Proof. exact (fun_ext (fun x : A => @lem4117277 A x s)). Qed.
Lemma lem4117279 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117280 {A : Type'} (s : A -> Prop) : (term960 A s) = (term993 A s).
Proof. exact (MK_COMB (@lem4117279 A) (@lem4117278 A s)). Qed.
Lemma lem4117281 {A : Type'} (s : A -> Prop) : (term945 A s) = (term993 A s).
Proof. exact (TRANS (@lem4117229 A s) (@lem4117280 A s)). Qed.
Lemma lem4117282 {A : Type'} (s : A -> Prop) : (term789 A s) = (term993 A s).
Proof. exact (TRANS (@lem4117205 A s) (@lem4117281 A s)). Qed.
Lemma lem4117283 {A : Type'} (s : A -> Prop) : (term826 A s) = (term994 A s).
Proof. exact (MK_COMB (@lem4117140 A s) (@lem4117282 A s)). Qed.
Lemma lem4117285 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term995 A P Q) = (term996 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4117286 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term995 A P Q) = (term996 A P Q).
Proof. exact (@lem4117285 A P Q). Qed.
Lemma lem4117287 {A : Type'} (s : A -> Prop) : (term997 A s) = (term998 A s).
Proof. exact (@lem4117286 A (term901 A s) (term992 A s)). Qed.
Lemma lem4117288 {A : Type'} (a : A) (s : A -> Prop) : (term999 A s a) = (term900 A a s).
Proof. exact (eq_refl (term999 A s a)). Qed.
Lemma lem4117289 {A : Type'} (s : A -> Prop) : (term1000 A s) = (term901 A s).
Proof. exact (fun_ext (fun a : A => @lem4117288 A a s)). Qed.
Lemma lem4117290 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117291 {A : Type'} (s : A -> Prop) : (term1001 A s) = (term902 A s).
Proof. exact (MK_COMB (@lem4117290 A) (@lem4117289 A s)). Qed.
Lemma lem4117292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4117293 {A : Type'} (s : A -> Prop) : (term1002 A s) = (term903 A s).
Proof. exact (MK_COMB (@lem4117292) (@lem4117291 A s)). Qed.
Lemma lem4117294 {A : Type'} (a : A) (s : A -> Prop) : (term1003 A s a) = (term991 A a s).
Proof. exact (eq_refl (term1003 A s a)). Qed.
Lemma lem4117295 {A : Type'} (s : A -> Prop) : (term1004 A s) = (term992 A s).
Proof. exact (fun_ext (fun a : A => @lem4117294 A a s)). Qed.
Lemma lem4117296 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117297 {A : Type'} (s : A -> Prop) : (term1005 A s) = (term993 A s).
Proof. exact (MK_COMB (@lem4117296 A) (@lem4117295 A s)). Qed.
Lemma lem4117298 {A : Type'} (s : A -> Prop) : (term997 A s) = (term994 A s).
Proof. exact (MK_COMB (@lem4117293 A s) (@lem4117297 A s)). Qed.
Lemma lem4117299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117300 {A : Type'} (s : A -> Prop) : (term1006 A s) = (term1007 A s).
Proof. exact (MK_COMB (@lem4117299) (@lem4117298 A s)). Qed.
Lemma lem4117301 {A : Type'} (a : A) (s : A -> Prop) : (term999 A s a) = (term900 A a s).
Proof. exact (eq_refl (term999 A s a)). Qed.
Lemma lem4117302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4117303 {A : Type'} (a : A) (s : A -> Prop) : (term1008 A s a) = (term1009 A a s).
Proof. exact (MK_COMB (@lem4117302) (@lem4117301 A a s)). Qed.
Lemma lem4117304 {A : Type'} (a : A) (s : A -> Prop) : (term1003 A s a) = (term991 A a s).
Proof. exact (eq_refl (term1003 A s a)). Qed.
Lemma lem4117305 {A : Type'} (a : A) (s : A -> Prop) : (term1010 A s a) = (term1011 A a s).
Proof. exact (MK_COMB (@lem4117303 A a s) (@lem4117304 A a s)). Qed.
Lemma lem4117306 {A : Type'} (s : A -> Prop) : (term1012 A s) = (term1013 A s).
Proof. exact (fun_ext (fun a : A => @lem4117305 A a s)). Qed.
Lemma lem4117307 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117308 {A : Type'} (s : A -> Prop) : (term998 A s) = (term1014 A s).
Proof. exact (MK_COMB (@lem4117307 A) (@lem4117306 A s)). Qed.
Lemma lem4117309 {A : Type'} (s : A -> Prop) : ((term997 A s) = (term998 A s)) = ((term994 A s) = (term1014 A s)).
Proof. exact (MK_COMB (@lem4117300 A s) (@lem4117308 A s)). Qed.
Lemma lem4117310 {A : Type'} (s : A -> Prop) : (term994 A s) = (term1014 A s).
Proof. exact (EQ_MP (@lem4117309 A s) (@lem4117287 A s)). Qed.
Lemma lem4117313 {A : Type'} (s : A -> Prop) : (term1015 A s) = (term1015 A s).
Proof. exact (eq_refl (term1015 A s)). Qed.
Lemma lem4117314 {A : Type'} (s : A -> Prop) : (term1015 A s) = ((term994 A s) = (term1014 A s)).
Proof. exact (eq_refl (term1015 A s)). Qed.
Lemma lem4117315 {A : Type'} (s : A -> Prop) : (term1016 A s) = (term1016 A s).
Proof. exact (eq_refl (term1016 A s)). Qed.
Lemma lem4117316 {A : Type'} (s : A -> Prop) : ((term1015 A s) = (term1015 A s)) = ((term1015 A s) = ((term994 A s) = (term1014 A s))).
Proof. exact (MK_COMB (@lem4117315 A s) (@lem4117314 A s)). Qed.
Lemma lem4117317 {A : Type'} (s : A -> Prop) : (term1015 A s) = ((term994 A s) = (term1014 A s)).
Proof. exact (eq_refl (term1015 A s)). Qed.
Lemma lem4117318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117319 {A : Type'} (s : A -> Prop) : (term1016 A s) = (term1017 A s).
Proof. exact (MK_COMB (@lem4117318) (@lem4117317 A s)). Qed.
Lemma lem4117320 {A : Type'} (s : A -> Prop) : ((term994 A s) = (term1014 A s)) = ((term994 A s) = (term1014 A s)).
Proof. exact (eq_refl ((term994 A s) = (term1014 A s))). Qed.
Lemma lem4117321 {A : Type'} (s : A -> Prop) : ((term1015 A s) = ((term994 A s) = (term1014 A s))) = (((term994 A s) = (term1014 A s)) = ((term994 A s) = (term1014 A s))).
Proof. exact (MK_COMB (@lem4117319 A s) (@lem4117320 A s)). Qed.
Lemma lem4117322 {A : Type'} (s : A -> Prop) : ((term1015 A s) = (term1015 A s)) = (((term994 A s) = (term1014 A s)) = ((term994 A s) = (term1014 A s))).
Proof. exact (TRANS (@lem4117316 A s) (@lem4117321 A s)). Qed.
Lemma lem4117323 {A : Type'} (s : A -> Prop) : ((term994 A s) = (term1014 A s)) = ((term994 A s) = (term1014 A s)).
Proof. exact (EQ_MP (@lem4117322 A s) (@lem4117313 A s)). Qed.
Lemma lem4117324 {A : Type'} (s : A -> Prop) : (term994 A s) = (term1014 A s).
Proof. exact (EQ_MP (@lem4117323 A s) (@lem4117310 A s)). Qed.
Lemma lem4117326 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term995 A P Q) = (term996 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4117327 {A : Type'} (P : type488 A) (Q : type488 A) : (term1018 A P Q) = (term1019 A P Q).
Proof. exact (@lem4117326 (A -> A) P Q). Qed.
Lemma lem4117328 {A : Type'} (a : A) (s : A -> Prop) : (term1020 A a s) = (term1021 A a s).
Proof. exact (@lem4117327 A (term899 A a s) (term990 A a s)). Qed.
Lemma lem4117329 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) : (term1022 A a s x) = (term897 A a s x).
Proof. exact (eq_refl (term1022 A a s x)). Qed.
Lemma lem4117330 {A : Type'} (a : A) (s : A -> Prop) : (term1023 A a s) = (term899 A a s).
Proof. exact (fun_ext (fun x : A -> A => @lem4117329 A a s x)). Qed.
Lemma lem4117331 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117332 {A : Type'} (a : A) (s : A -> Prop) : (term1024 A a s) = (term900 A a s).
Proof. exact (MK_COMB (@lem4117331 A) (@lem4117330 A a s)). Qed.
Lemma lem4117333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4117334 {A : Type'} (a : A) (s : A -> Prop) : (term1025 A a s) = (term1009 A a s).
Proof. exact (MK_COMB (@lem4117333) (@lem4117332 A a s)). Qed.
Lemma lem4117335 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) : (term1026 A a s x) = (term989 A a x s).
Proof. exact (eq_refl (term1026 A a s x)). Qed.
Lemma lem4117336 {A : Type'} (a : A) (s : A -> Prop) : (term1027 A a s) = (term990 A a s).
Proof. exact (fun_ext (fun x : A -> A => @lem4117335 A a x s)). Qed.
Lemma lem4117337 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117338 {A : Type'} (a : A) (s : A -> Prop) : (term1028 A a s) = (term991 A a s).
Proof. exact (MK_COMB (@lem4117337 A) (@lem4117336 A a s)). Qed.
Lemma lem4117339 {A : Type'} (a : A) (s : A -> Prop) : (term1020 A a s) = (term1011 A a s).
Proof. exact (MK_COMB (@lem4117334 A a s) (@lem4117338 A a s)). Qed.
Lemma lem4117340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117341 {A : Type'} (a : A) (s : A -> Prop) : (term1029 A a s) = (term1030 A a s).
Proof. exact (MK_COMB (@lem4117340) (@lem4117339 A a s)). Qed.
Lemma lem4117342 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) : (term1022 A a s x) = (term897 A a s x).
Proof. exact (eq_refl (term1022 A a s x)). Qed.
Lemma lem4117343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4117344 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) : (term1031 A a s x) = (term1032 A a s x).
Proof. exact (MK_COMB (@lem4117343) (@lem4117342 A a s x)). Qed.
Lemma lem4117345 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) : (term1026 A a s x) = (term989 A a x s).
Proof. exact (eq_refl (term1026 A a s x)). Qed.
Lemma lem4117346 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) : (term1033 A a s x) = (term1034 A a x s).
Proof. exact (MK_COMB (@lem4117344 A a s x) (@lem4117345 A a x s)). Qed.
Lemma lem4117347 {A : Type'} (a : A) (s : A -> Prop) : (term1035 A a s) = (term1036 A a s).
Proof. exact (fun_ext (fun x : A -> A => @lem4117346 A a x s)). Qed.
Lemma lem4117348 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117349 {A : Type'} (a : A) (s : A -> Prop) : (term1021 A a s) = (term1037 A a s).
Proof. exact (MK_COMB (@lem4117348 A) (@lem4117347 A a s)). Qed.
Lemma lem4117350 {A : Type'} (a : A) (s : A -> Prop) : ((term1020 A a s) = (term1021 A a s)) = ((term1011 A a s) = (term1037 A a s)).
Proof. exact (MK_COMB (@lem4117341 A a s) (@lem4117349 A a s)). Qed.
Lemma lem4117351 {A : Type'} (a : A) (s : A -> Prop) : (term1011 A a s) = (term1037 A a s).
Proof. exact (EQ_MP (@lem4117350 A a s) (@lem4117328 A a s)). Qed.
Lemma lem4117353 {A : Type'} (P : Prop) (Q : A -> Prop) : (term827 A P Q) = (term828 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4117354 {A : Type'} (P : Prop) (Q : A -> Prop) : (term827 A P Q) = (term828 A P Q).
Proof. exact (@lem4117353 A P Q). Qed.
Lemma lem4117355 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) : (term1038 A a x s) = (term1039 A a x s).
Proof. exact (@lem4117354 A (term897 A a s x) (term988 A a x s)). Qed.
Lemma lem4117356 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) : (term1040 A a x s a') = (term986 A a x s a').
Proof. exact (eq_refl (term1040 A a x s a')). Qed.
Lemma lem4117357 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) : (term1041 A a x s) = (term988 A a x s).
Proof. exact (fun_ext (fun a' : A => @lem4117356 A a x s a')). Qed.
Lemma lem4117358 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117359 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) : (term1042 A a x s) = (term989 A a x s).
Proof. exact (MK_COMB (@lem4117358 A) (@lem4117357 A a x s)). Qed.
Lemma lem4117360 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) : (term1032 A a s x) = (term1032 A a s x).
Proof. exact (eq_refl (term1032 A a s x)). Qed.
Lemma lem4117361 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) : (term1038 A a x s) = (term1034 A a x s).
Proof. exact (MK_COMB (@lem4117360 A a s x) (@lem4117359 A a x s)). Qed.
Lemma lem4117362 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117363 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) : (term1043 A a x s) = (term1044 A a x s).
Proof. exact (MK_COMB (@lem4117362) (@lem4117361 A a x s)). Qed.
Lemma lem4117364 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) : (term1040 A a x s a') = (term986 A a x s a').
Proof. exact (eq_refl (term1040 A a x s a')). Qed.
Lemma lem4117365 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) : (term1032 A a s x) = (term1032 A a s x).
Proof. exact (eq_refl (term1032 A a s x)). Qed.
Lemma lem4117366 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) : (term1045 A a x s a') = (term1046 A a x s a').
Proof. exact (MK_COMB (@lem4117365 A a s x) (@lem4117364 A a x s a')). Qed.
Lemma lem4117367 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) : (term1047 A a x s) = (term1048 A a x s).
Proof. exact (fun_ext (fun a' : A => @lem4117366 A a x s a')). Qed.
Lemma lem4117368 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117369 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) : (term1039 A a x s) = (term1049 A a x s).
Proof. exact (MK_COMB (@lem4117368 A) (@lem4117367 A a x s)). Qed.
Lemma lem4117370 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) : ((term1038 A a x s) = (term1039 A a x s)) = ((term1034 A a x s) = (term1049 A a x s)).
Proof. exact (MK_COMB (@lem4117363 A a x s) (@lem4117369 A a x s)). Qed.
Lemma lem4117371 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) : (term1034 A a x s) = (term1049 A a x s).
Proof. exact (EQ_MP (@lem4117370 A a x s) (@lem4117355 A a x s)). Qed.
Lemma lem4117372 {A : Type'} (a : A) (s : A -> Prop) : (term1036 A a s) = (term1050 A a s).
Proof. exact (fun_ext (fun x : A -> A => @lem4117371 A a x s)). Qed.
Lemma lem4117373 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem4117374 {A : Type'} (a : A) (s : A -> Prop) : (term1037 A a s) = (term1051 A a s).
Proof. exact (MK_COMB (@lem4117373 A) (@lem4117372 A a s)). Qed.
Lemma lem4117375 {A : Type'} (a : A) (s : A -> Prop) : (term1011 A a s) = (term1051 A a s).
Proof. exact (TRANS (@lem4117351 A a s) (@lem4117374 A a s)). Qed.
Lemma lem4117376 {A : Type'} (s : A -> Prop) : (term1013 A s) = (term1052 A s).
Proof. exact (fun_ext (fun a : A => @lem4117375 A a s)). Qed.
Lemma lem4117377 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4117378 {A : Type'} (s : A -> Prop) : (term1014 A s) = (term1053 A s).
Proof. exact (MK_COMB (@lem4117377 A) (@lem4117376 A s)). Qed.
Lemma lem4117379 {A : Type'} (s : A -> Prop) : (term994 A s) = (term1053 A s).
Proof. exact (TRANS (@lem4117324 A s) (@lem4117378 A s)). Qed.
Lemma lem4117380 {A : Type'} (s : A -> Prop) : (term826 A s) = (term1053 A s).
Proof. exact (TRANS (@lem4117283 A s) (@lem4117379 A s)). Qed.
Lemma lem4117381 {A : Type'} (s : A -> Prop) : (term797 A s) = (term1053 A s).
Proof. exact (TRANS (@lem4117036 A s) (@lem4117380 A s)). Qed.
Lemma lem4117382 {A : Type'} (s : A -> Prop) : (term718 A s) = (term1053 A s).
Proof. exact (TRANS (@lem4116724 A s) (@lem4117381 A s)). Qed.
Lemma lem4117383 {A : Type'} (s : A -> Prop) (h1 : term718 A s) : term1053 A s.
Proof. exact (EQ_MP (@lem4117382 A s) (@lem4116596 A s h1)). Qed.
Lemma lem4117384 {A : Type'} (a : A) (s : A -> Prop) (h1 : term1051 A a s) : term1051 A a s.
Proof. exact (h1). Qed.
Lemma lem4117385 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (h1 : term1049 A a x s) : term1049 A a x s.
Proof. exact (h1). Qed.
Lemma lem4117386 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1046 A a x s a') : term1046 A a x s a'.
Proof. exact (h1). Qed.
Lemma lem4117399 {A : Type'} (s : A -> Prop) (x : A) (a' : A) : (term767 A s x a') = (term767 A s x a').
Proof. exact (eq_refl (term767 A s x a')). Qed.
Lemma lem4117400 {A : Type'} (s : A -> Prop) (a' : A) : (term775 A s a') = (term775 A s a').
Proof. exact (fun_ext (fun x : A => @lem4117399 A s x a')). Qed.
Lemma lem4117401 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117402 {A : Type'} (s : A -> Prop) (a' : A) : (term776 A s a') = (term776 A s a').
Proof. exact (MK_COMB (@lem4117401 A) (@lem4117400 A s a')). Qed.
Lemma lem4117439 {A : Type'} (s : A -> Prop) (x : A -> A) (a : A) : (term917 A s x a) = (term917 A s x a).
Proof. exact (eq_refl (term917 A s x a)). Qed.
Lemma lem4117440 {A : Type'} (s : A -> Prop) (x : A -> A) : (term919 A s x) = (term919 A s x).
Proof. exact (fun_ext (fun a : A => @lem4117439 A s x a)). Qed.
Lemma lem4117441 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117442 {A : Type'} (s : A -> Prop) (x : A -> A) : (term921 A s x) = (term921 A s x).
Proof. exact (MK_COMB (@lem4117441 A) (@lem4117440 A s x)). Qed.
Lemma lem4117447 {A : Type'} (s : A -> Prop) (a : A) : (term932 A s a) = (term932 A s a).
Proof. exact (eq_refl (term932 A s a)). Qed.
Lemma lem4117448 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) : (term937 A a s x) = (term937 A a s x).
Proof. exact (MK_COMB (@lem4117447 A s a) (@lem4117442 A s x)). Qed.
Lemma lem4117449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4117450 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) : (term972 A a s x) = (term972 A a s x).
Proof. exact (MK_COMB (@lem4117449) (@lem4117448 A a s x)). Qed.
Lemma lem4117451 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) : (term986 A a x s a') = (term986 A a x s a').
Proof. exact (MK_COMB (@lem4117450 A a s x) (@lem4117402 A s a')). Qed.
Lemma lem4117468 {A : Type'} (s : A -> Prop) (x : A -> A) (a : A) : (term859 A s x a) = (term859 A s x a).
Proof. exact (eq_refl (term859 A s x a)). Qed.
Lemma lem4117469 {A : Type'} (s : A -> Prop) (x : A -> A) : (term861 A s x) = (term861 A s x).
Proof. exact (fun_ext (fun a : A => @lem4117468 A s x a)). Qed.
Lemma lem4117470 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117471 {A : Type'} (s : A -> Prop) (x : A -> A) : (term863 A s x) = (term863 A s x).
Proof. exact (MK_COMB (@lem4117470 A) (@lem4117469 A s x)). Qed.
Lemma lem4117484 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term767 A s x a) = (term767 A s x a).
Proof. exact (eq_refl (term767 A s x a)). Qed.
Lemma lem4117485 {A : Type'} (s : A -> Prop) (a : A) : (term775 A s a) = (term775 A s a).
Proof. exact (fun_ext (fun x : A => @lem4117484 A s x a)). Qed.
Lemma lem4117486 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117487 {A : Type'} (s : A -> Prop) (a : A) : (term776 A s a) = (term776 A s a).
Proof. exact (MK_COMB (@lem4117486 A) (@lem4117485 A s a)). Qed.
Lemma lem4117500 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term804 A s x a) = (term804 A s x a).
Proof. exact (eq_refl (term804 A s x a)). Qed.
Lemma lem4117501 {A : Type'} (s : A -> Prop) (a : A) : (term802 A s a) = (term802 A s a).
Proof. exact (fun_ext (fun x : A => @lem4117500 A s x a)). Qed.
Lemma lem4117502 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117503 {A : Type'} (s : A -> Prop) (a : A) : (term814 A s a) = (term814 A s a).
Proof. exact (MK_COMB (@lem4117502 A) (@lem4117501 A s a)). Qed.
Lemma lem4117504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4117505 {A : Type'} (s : A -> Prop) (a : A) : (term816 A s a) = (term816 A s a).
Proof. exact (MK_COMB (@lem4117504) (@lem4117503 A s a)). Qed.
Lemma lem4117506 {A : Type'} (s : A -> Prop) (a : A) : (term819 A s a) = (term819 A s a).
Proof. exact (MK_COMB (@lem4117505 A s a) (@lem4117487 A s a)). Qed.
Lemma lem4117511 {A : Type'} (s : A -> Prop) (x : A) : (term689 A s x) = (term689 A s x).
Proof. exact (eq_refl (term689 A s x)). Qed.
Lemma lem4117512 {A : Type'} (s : A -> Prop) : (term691 A s) = (term691 A s).
Proof. exact (fun_ext (fun x : A => @lem4117511 A s x)). Qed.
Lemma lem4117513 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117514 {A : Type'} (s : A -> Prop) : (term692 A s) = (term692 A s).
Proof. exact (MK_COMB (@lem4117513 A) (@lem4117512 A s)). Qed.
Lemma lem4117515 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4117516 {A : Type'} (s : A -> Prop) : (term693 A s) = (term693 A s).
Proof. exact (MK_COMB (@lem4117515) (@lem4117514 A s)). Qed.
Lemma lem4117517 {A : Type'} (s : A -> Prop) (a : A) : (term837 A s a) = (term837 A s a).
Proof. exact (MK_COMB (@lem4117516 A s) (@lem4117506 A s a)). Qed.
Lemma lem4117518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4117519 {A : Type'} (s : A -> Prop) (a : A) : (term879 A s a) = (term879 A s a).
Proof. exact (MK_COMB (@lem4117518) (@lem4117517 A s a)). Qed.
Lemma lem4117520 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) : (term897 A a s x) = (term897 A a s x).
Proof. exact (MK_COMB (@lem4117519 A s a) (@lem4117471 A s x)). Qed.
Lemma lem4117521 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4117522 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) : (term1032 A a s x) = (term1032 A a s x).
Proof. exact (MK_COMB (@lem4117521) (@lem4117520 A a s x)). Qed.
Lemma lem4117523 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) : (term1046 A a x s a') = (term1046 A a x s a').
Proof. exact (MK_COMB (@lem4117522 A a s x) (@lem4117451 A a x s a')). Qed.
Lemma lem4117524 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1046 A a x s a') : term1046 A a x s a'.
Proof. exact (EQ_MP (@lem4117523 A a x s a') (@lem4117386 A a x s a' h1)). Qed.
Lemma lem4117525 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term897 A a s x.
Proof. exact (h1). Qed.
Lemma lem4117526 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term986 A a x s a'.
Proof. exact (h1). Qed.
Lemma lem4117527 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term863 A s x.
Proof. exact (proj2 (@lem4117525 A a s x h1)). Qed.
Lemma lem4117528 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term837 A s a.
Proof. exact (proj1 (@lem4117525 A a s x h1)). Qed.
Lemma lem4117529 {A : Type'} (s : A -> Prop) (h1 : term692 A s) : term692 A s.
Proof. exact (h1). Qed.
Lemma lem4117530 {A : Type'} (s : A -> Prop) (a : A) (h1 : term819 A s a) : term819 A s a.
Proof. exact (h1). Qed.
Lemma lem4117531 {A : Type'} (s : A -> Prop) (a : A) (h1 : term819 A s a) : term776 A s a.
Proof. exact (proj2 (@lem4117530 A s a h1)). Qed.
Lemma lem4117533 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term776 A s a'.
Proof. exact (proj2 (@lem4117526 A a x s a' h1)). Qed.
Lemma lem4117534 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term937 A a s x.
Proof. exact (proj1 (@lem4117526 A a x s a' h1)). Qed.
Lemma lem4117535 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term921 A s x.
Proof. exact (proj2 (@lem4117534 A a x s a' h1)). Qed.
Lemma lem4117542 {A : Type'} (s : A -> Prop) (x : A -> A) (a : A) : (term859 A s x a) = (term859 A s x a).
Proof. exact (eq_refl (term859 A s x a)). Qed.
Lemma lem4117543 {A : Type'} (s : A -> Prop) (x : A -> A) : (term861 A s x) = (term861 A s x).
Proof. exact (fun_ext (fun a : A => @lem4117542 A s x a)). Qed.
Lemma lem4117544 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117546 {A : Type'} (s : A -> Prop) (x : A -> A) : (term863 A s x) = (term863 A s x).
Proof. exact (MK_COMB (@lem4117544 A) (@lem4117543 A s x)). Qed.
Lemma lem4117547 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term863 A s x.
Proof. exact (EQ_MP (@lem4117546 A s x) (@lem4117527 A a s x h1)). Qed.
Lemma lem4117549 {A : Type'} (s : A -> Prop) (x : A) : (term689 A s x) = (term689 A s x).
Proof. exact (eq_refl (term689 A s x)). Qed.
Lemma lem4117550 {A : Type'} (s : A -> Prop) : (term691 A s) = (term691 A s).
Proof. exact (fun_ext (fun x : A => @lem4117549 A s x)). Qed.
Lemma lem4117551 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117553 {A : Type'} (s : A -> Prop) : (term692 A s) = (term692 A s).
Proof. exact (MK_COMB (@lem4117551 A) (@lem4117550 A s)). Qed.
Lemma lem4117554 {A : Type'} (s : A -> Prop) (h1 : term692 A s) : term692 A s.
Proof. exact (EQ_MP (@lem4117553 A s) (@lem4117529 A s h1)). Qed.
Lemma lem4117560 {A : Type'} (s : A -> Prop) (x : A -> A) (a : A) : (term859 A s x a) = (term859 A s x a).
Proof. exact (eq_refl (term859 A s x a)). Qed.
Lemma lem4117561 {A : Type'} (s : A -> Prop) (x : A -> A) : (term861 A s x) = (term861 A s x).
Proof. exact (fun_ext (fun a : A => @lem4117560 A s x a)). Qed.
Lemma lem4117562 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117564 {A : Type'} (s : A -> Prop) (x : A -> A) : (term863 A s x) = (term863 A s x).
Proof. exact (MK_COMB (@lem4117562 A) (@lem4117561 A s x)). Qed.
Lemma lem4117565 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term863 A s x.
Proof. exact (EQ_MP (@lem4117564 A s x) (@lem4117527 A a s x h1)). Qed.
Lemma lem4117586 {A : Type'} (s : A -> Prop) (x : A) (a : A) : (term767 A s x a) = (term767 A s x a).
Proof. exact (eq_refl (term767 A s x a)). Qed.
Lemma lem4117587 {A : Type'} (s : A -> Prop) (a : A) : (term775 A s a) = (term775 A s a).
Proof. exact (fun_ext (fun x : A => @lem4117586 A s x a)). Qed.
Lemma lem4117588 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117590 {A : Type'} (s : A -> Prop) (a : A) : (term776 A s a) = (term776 A s a).
Proof. exact (MK_COMB (@lem4117588 A) (@lem4117587 A s a)). Qed.
Lemma lem4117591 {A : Type'} (s : A -> Prop) (a : A) (h1 : term819 A s a) : term776 A s a.
Proof. exact (EQ_MP (@lem4117590 A s a) (@lem4117531 A s a h1)). Qed.
Lemma lem4117599 {A : Type'} (s : A -> Prop) (x : A) (a' : A) : (term767 A s x a') = (term767 A s x a').
Proof. exact (eq_refl (term767 A s x a')). Qed.
Lemma lem4117600 {A : Type'} (s : A -> Prop) (a' : A) : (term775 A s a') = (term775 A s a').
Proof. exact (fun_ext (fun x : A => @lem4117599 A s x a')). Qed.
Lemma lem4117601 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117603 {A : Type'} (s : A -> Prop) (a' : A) : (term776 A s a') = (term776 A s a').
Proof. exact (MK_COMB (@lem4117601 A) (@lem4117600 A s a')). Qed.
Lemma lem4117604 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term776 A s a'.
Proof. exact (EQ_MP (@lem4117603 A s a') (@lem4117533 A a x s a' h1)). Qed.
Lemma lem4117626 {A : Type'} (s : A -> Prop) (x : A -> A) (a : A) : (term917 A s x a) = (term917 A s x a).
Proof. exact (eq_refl (term917 A s x a)). Qed.
Lemma lem4117627 {A : Type'} (s : A -> Prop) (x : A -> A) : (term919 A s x) = (term919 A s x).
Proof. exact (fun_ext (fun a : A => @lem4117626 A s x a)). Qed.
Lemma lem4117628 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4117630 {A : Type'} (s : A -> Prop) (x : A -> A) : (term921 A s x) = (term921 A s x).
Proof. exact (MK_COMB (@lem4117628 A) (@lem4117627 A s x)). Qed.
Lemma lem4117631 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term921 A s x.
Proof. exact (EQ_MP (@lem4117630 A s x) (@lem4117535 A a x s a' h1)). Qed.
Lemma lem4117632 {A : Type'} (_48300 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1054 A s x _48300.
Proof. exact (@lem4117547 A a s x h1 _48300). Qed.
Lemma lem4117633 {A : Type'} (s : A -> Prop) (x : A -> A) (_48300 : A) : (term1054 A s x _48300) = (term859 A s x _48300).
Proof. exact (eq_refl (term1054 A s x _48300)). Qed.
Lemma lem4117634 {A : Type'} (_48300 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term859 A s x _48300.
Proof. exact (EQ_MP (@lem4117633 A s x _48300) (@lem4117632 A _48300 a s x h1)). Qed.
Lemma lem4117635 {A : Type'} (_48301 : A) (s : A -> Prop) (h1 : term692 A s) : term732 A s _48301.
Proof. exact (@lem4117554 A s h1 _48301). Qed.
Lemma lem4117636 {A : Type'} (s : A -> Prop) (_48301 : A) : (term732 A s _48301) = (term689 A s _48301).
Proof. exact (eq_refl (term732 A s _48301)). Qed.
Lemma lem4117638 {A : Type'} (_48302 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1054 A s x _48302.
Proof. exact (@lem4117565 A a s x h1 _48302). Qed.
Lemma lem4117639 {A : Type'} (s : A -> Prop) (x : A -> A) (_48302 : A) : (term1054 A s x _48302) = (term859 A s x _48302).
Proof. exact (eq_refl (term1054 A s x _48302)). Qed.
Lemma lem4117640 {A : Type'} (_48302 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term859 A s x _48302.
Proof. exact (EQ_MP (@lem4117639 A s x _48302) (@lem4117638 A _48302 a s x h1)). Qed.
Lemma lem4117644 {A : Type'} (_48304 : A) (s : A -> Prop) (a : A) (h1 : term819 A s a) : term807 A s a _48304.
Proof. exact (@lem4117591 A s a h1 _48304). Qed.
Lemma lem4117645 {A : Type'} (s : A -> Prop) (_48304 : A) (a : A) : (term807 A s a _48304) = (term767 A s _48304 a).
Proof. exact (eq_refl (term807 A s a _48304)). Qed.
Lemma lem4117647 {A : Type'} (_48305 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term807 A s a' _48305.
Proof. exact (@lem4117604 A a x s a' h1 _48305). Qed.
Lemma lem4117648 {A : Type'} (s : A -> Prop) (_48305 : A) (a' : A) : (term807 A s a' _48305) = (term767 A s _48305 a').
Proof. exact (eq_refl (term807 A s a' _48305)). Qed.
Lemma lem4117650 {A : Type'} (_48306 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1055 A s x _48306.
Proof. exact (@lem4117631 A a x s a' h1 _48306). Qed.
Lemma lem4117651 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : (term1055 A s x _48306) = (term917 A s x _48306).
Proof. exact (eq_refl (term1055 A s x _48306)). Qed.
Lemma lem4117652 {A : Type'} (_48306 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term917 A s x _48306.
Proof. exact (EQ_MP (@lem4117651 A s x _48306) (@lem4117650 A _48306 a x s a' h1)). Qed.
Lemma lem4117660 {A : Type'} (_48301 : A) (s : A -> Prop) (h1 : term692 A s) : term689 A s _48301.
Proof. exact (EQ_MP (@lem4117636 A s _48301) (@lem4117635 A _48301 s h1)). Qed.
Lemma lem4117676 {A : Type'} (_48304 : A) (s : A -> Prop) (a : A) (h1 : term819 A s a) : term767 A s _48304 a.
Proof. exact (EQ_MP (@lem4117645 A s _48304 a) (@lem4117644 A _48304 s a h1)). Qed.
Lemma lem4117680 {A : Type'} (_48302 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1056 A x _48302.
Proof. exact (proj2 (@lem4117640 A _48302 a s x h1)). Qed.
Lemma lem4117686 {A : Type'} (_48305 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term767 A s _48305 a'.
Proof. exact (EQ_MP (@lem4117648 A s _48305 a') (@lem4117647 A _48305 a x s a' h1)). Qed.
Lemma lem4117694 {A : Type'} (_48306 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1057 A s x _48306.
Proof. exact (proj1 (@lem4117652 A _48306 a x s a' h1)). Qed.
Lemma lem4117700 {A : Type'} (_48306 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1058 A s x _48306.
Proof. exact (proj2 (@lem4117652 A _48306 a x s a' h1)). Qed.
Lemma lem4117724 {A : Type'} (_48300 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1059 A s x _48300.
Proof. exact (proj1 (@lem4117634 A _48300 a s x h1)). Qed.
Lemma lem4117725 {A : Type'} (_48300 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1059 A s x _48300.
Proof. exact (@lem4117724 A _48300 a s x h1). Qed.
Lemma lem4117726 {A : Type'} (_48311 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1059 A s x _48311.
Proof. exact (@lem4117725 A _48311 a s x h1). Qed.
Lemma lem4117727 {A : Type'} (_48311 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1060 A s x _48311.
Proof. exact (fun h0 : term1061 A s x _48311 => @lem4117726 A _48311 a s x h1). Qed.
Lemma lem4117729 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4117730 {A : Type'} (s : A -> Prop) (x : A -> A) (_48311 : A) : (term1060 A s x _48311) = (term1059 A s x _48311).
Proof. exact (@lem4117729 (term1059 A s x _48311)). Qed.
Lemma lem4117731 {A : Type'} (_48311 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1059 A s x _48311.
Proof. exact (EQ_MP (@lem4117730 A s x _48311) (@lem4117727 A _48311 a s x h1)). Qed.
Lemma lem4117734 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4117736 {A : Type'} (s : A -> Prop) (_48301 : A) : (term689 A s _48301) = (term1063 A s _48301).
Proof. exact (@lem4117734 (s _48301)). Qed.
Lemma lem4117739 {A : Type'} (_48301 : A) (s : A -> Prop) (h1 : term692 A s) : term1063 A s _48301.
Proof. exact (EQ_MP (@lem4117736 A s _48301) (@lem4117660 A _48301 s h1)). Qed.
Lemma lem4117740 {A : Type'} (_48301 : A) (s : A -> Prop) (h1 : term692 A s) : term1063 A s _48301.
Proof. exact (@lem4117739 A _48301 s h1). Qed.
Lemma lem4117741 {A : Type'} (x : A -> A) (_48311 : A) (s : A -> Prop) (h1 : term692 A s) : term1064 A s x _48311.
Proof. exact (@lem4117740 A (x _48311) s h1). Qed.
Lemma lem4117744 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term692 A s) (h2 : term897 A a s x) : False.
Proof. exact (@lem4117741 A x (@el A) s h1 (@lem4117731 A (@el A) a s x h2)). Qed.
Lemma lem4117745 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term692 A s) (h2 : term897 A a s x) : term1065.
Proof. exact (fun h0 : ~ False => @lem4117744 A a s x h1 h2). Qed.
Lemma lem4117747 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4117748 : term1065 = False.
Proof. exact (@lem4117747 False). Qed.
Lemma lem4117749 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term692 A s) (h2 : term897 A a s x) : False.
Proof. exact (EQ_MP (@lem4117748) (@lem4117745 A a s x h1 h2)). Qed.
Lemma lem4117773 {A : Type'} (_48302 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1059 A s x _48302.
Proof. exact (proj1 (@lem4117640 A _48302 a s x h1)). Qed.
Lemma lem4117774 {A : Type'} (_48302 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1059 A s x _48302.
Proof. exact (@lem4117773 A _48302 a s x h1). Qed.
Lemma lem4117775 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1059 A s x a.
Proof. exact (@lem4117774 A a a s x h1). Qed.
Lemma lem4117776 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1060 A s x a.
Proof. exact (fun h0 : term1061 A s x a => @lem4117775 A a s x h1). Qed.
Lemma lem4117778 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4117779 {A : Type'} (s : A -> Prop) (x : A -> A) (a : A) : (term1060 A s x a) = (term1059 A s x a).
Proof. exact (@lem4117778 (term1059 A s x a)). Qed.
Lemma lem4117780 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1059 A s x a.
Proof. exact (EQ_MP (@lem4117779 A s x a) (@lem4117776 A a s x h1)). Qed.
Lemma lem4117786 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4117787 {A : Type'} (a : A) (s : A -> Prop) (_48304 : A) : (term767 A s _48304 a) = (term1066 A a s _48304).
Proof. exact (@lem4117786 (_48304 = a) (term689 A s _48304)). Qed.
Lemma lem4117795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117796 {A : Type'} (a : A) (s : A -> Prop) (_48304 : A) : (term1067 A s _48304 a) = (term1068 A a s _48304).
Proof. exact (MK_COMB (@lem4117795) (@lem4117787 A a s _48304)). Qed.
Lemma lem4117804 {A : Type'} (a : A) (s : A -> Prop) (_48304 : A) : (term1066 A a s _48304) = (term1066 A a s _48304).
Proof. exact (eq_refl (term1066 A a s _48304)). Qed.
Lemma lem4117805 {A : Type'} (a : A) (s : A -> Prop) (_48304 : A) : ((term767 A s _48304 a) = (term1066 A a s _48304)) = ((term1066 A a s _48304) = (term1066 A a s _48304)).
Proof. exact (MK_COMB (@lem4117796 A a s _48304) (@lem4117804 A a s _48304)). Qed.
Lemma lem4117807 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4117808 (x : Prop) : (x = x) = True.
Proof. exact (@lem4117807 Prop x). Qed.
Lemma lem4117809 {A : Type'} (a : A) (s : A -> Prop) (_48304 : A) : ((term1066 A a s _48304) = (term1066 A a s _48304)) = True.
Proof. exact (@lem4117808 (term1066 A a s _48304)). Qed.
Lemma lem4117810 {A : Type'} (a : A) (s : A -> Prop) (_48304 : A) : ((term767 A s _48304 a) = (term1066 A a s _48304)) = True.
Proof. exact (TRANS (@lem4117805 A a s _48304) (@lem4117809 A a s _48304)). Qed.
Lemma lem4117811 {A : Type'} (a : A) (s : A -> Prop) (_48304 : A) : True = ((term767 A s _48304 a) = (term1066 A a s _48304)).
Proof. exact (SYM (@lem4117810 A a s _48304)). Qed.
Lemma lem4117812 {A : Type'} (a : A) (s : A -> Prop) (_48304 : A) : (term767 A s _48304 a) = (term1066 A a s _48304).
Proof. exact (EQ_MP (@lem4117811 A a s _48304) (@lem0)). Qed.
Lemma lem4117813 {A : Type'} (_48304 : A) (s : A -> Prop) (a : A) (h1 : term819 A s a) : term1066 A a s _48304.
Proof. exact (EQ_MP (@lem4117812 A a s _48304) (@lem4117676 A _48304 s a h1)). Qed.
Lemma lem4117815 (b : Prop) (a : Prop) : (a \/ b) = (term1069 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4117816 {A : Type'} (s : A -> Prop) (_48304 : A) (a : A) : (term1066 A a s _48304) = (term1070 A s _48304 a).
Proof. exact (@lem4117815 (term689 A s _48304) (_48304 = a)). Qed.
Lemma lem4117818 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4117819 {A : Type'} (s : A -> Prop) (_48304 : A) : (term727 A s _48304) = (s _48304).
Proof. exact (@lem4117818 (s _48304)). Qed.
Lemma lem4117820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4117821 {A : Type'} (s : A -> Prop) (_48304 : A) : (term1071 A s _48304) = (term708 A s _48304).
Proof. exact (MK_COMB (@lem4117820) (@lem4117819 A s _48304)). Qed.
Lemma lem4117822 {A : Type'} (_48304 : A) (a : A) : (_48304 = a) = (_48304 = a).
Proof. exact (eq_refl (_48304 = a)). Qed.
Lemma lem4117823 {A : Type'} (s : A -> Prop) (_48304 : A) (a : A) : (term1070 A s _48304 a) = (term710 A s _48304 a).
Proof. exact (MK_COMB (@lem4117821 A s _48304) (@lem4117822 A _48304 a)). Qed.
Lemma lem4117824 {A : Type'} (s : A -> Prop) (_48304 : A) (a : A) : (term1066 A a s _48304) = (term710 A s _48304 a).
Proof. exact (TRANS (@lem4117816 A s _48304 a) (@lem4117823 A s _48304 a)). Qed.
Lemma lem4117827 {A : Type'} (_48304 : A) (s : A -> Prop) (a : A) (h1 : term819 A s a) : term710 A s _48304 a.
Proof. exact (EQ_MP (@lem4117824 A s _48304 a) (@lem4117813 A _48304 s a h1)). Qed.
Lemma lem4117828 {A : Type'} (_48304 : A) (s : A -> Prop) (a : A) (h1 : term819 A s a) : term710 A s _48304 a.
Proof. exact (@lem4117827 A _48304 s a h1). Qed.
Lemma lem4117829 {A : Type'} (x : A -> A) (s : A -> Prop) (a : A) (h1 : term819 A s a) : term1072 A s x a.
Proof. exact (@lem4117828 A (x a) s a h1). Qed.
Lemma lem4117832 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term819 A s a) (h2 : term897 A a s x) : (x a) = a.
Proof. exact (@lem4117829 A x s a h1 (@lem4117780 A a s x h2)). Qed.
Lemma lem4117833 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term819 A s a) (h2 : term897 A a s x) : term1073 A x a.
Proof. exact (fun h0 : term1056 A x a => @lem4117832 A a s x h1 h2). Qed.
Lemma lem4117835 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4117836 {A : Type'} (x : A -> A) (a : A) : (term1073 A x a) = ((x a) = a).
Proof. exact (@lem4117835 ((x a) = a)). Qed.
Lemma lem4117837 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term819 A s a) (h2 : term897 A a s x) : (x a) = a.
Proof. exact (EQ_MP (@lem4117836 A x a) (@lem4117833 A a s x h1 h2)). Qed.
Lemma lem4117840 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4117842 {A : Type'} (x : A -> A) (_48302 : A) : (term1056 A x _48302) = (term1074 A x _48302).
Proof. exact (@lem4117840 ((x _48302) = _48302)). Qed.
Lemma lem4117845 {A : Type'} (_48302 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1074 A x _48302.
Proof. exact (EQ_MP (@lem4117842 A x _48302) (@lem4117680 A _48302 a s x h1)). Qed.
Lemma lem4117846 {A : Type'} (_48302 : A) (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1074 A x _48302.
Proof. exact (@lem4117845 A _48302 a s x h1). Qed.
Lemma lem4117847 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : term1074 A x a.
Proof. exact (@lem4117846 A a a s x h1). Qed.
Lemma lem4117850 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term819 A s a) (h2 : term897 A a s x) : False.
Proof. exact (@lem4117847 A a s x h2 (@lem4117837 A a s x h1 h2)). Qed.
Lemma lem4117851 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term819 A s a) (h2 : term897 A a s x) : term1065.
Proof. exact (fun h0 : ~ False => @lem4117850 A a s x h1 h2). Qed.
Lemma lem4117853 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4117854 : term1065 = False.
Proof. exact (@lem4117853 False). Qed.
Lemma lem4117855 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term819 A s a) (h2 : term897 A a s x) : False.
Proof. exact (EQ_MP (@lem4117854) (@lem4117851 A a s x h1 h2)). Qed.
Lemma lem4117856 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4117857 {A : Type'} (_48316 : A) (_48317 : A) (h1 : _48316 = _48317) : _48316 = _48317.
Proof. exact (h1). Qed.
Lemma lem4117858 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) (h1 : _48316 = _48317) : (s _48316) = (s _48317).
Proof. exact (MK_COMB (@lem4117856 A s) (@lem4117857 A _48316 _48317 h1)). Qed.
Lemma lem4117860 (b : Prop) (a : Prop) : term1075 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4117861 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : term1076 A _48317 s _48316.
Proof. exact (@lem4117860 (s _48317) (s _48316)). Qed.
Lemma lem4117862 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) (h1 : _48316 = _48317) : term1077 A _48317 s _48316.
Proof. exact (@lem4117861 A _48317 s _48316 (@lem4117858 A s _48316 _48317 h1)). Qed.
Lemma lem4117863 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : term1078 A _48317 s _48316.
Proof. exact (fun h0 : _48316 = _48317 => @lem4117862 A s _48316 _48317 h0). Qed.
Lemma lem4117865 (a : Prop) (b : Prop) : (a -> b) = (term1079 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4117866 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : (term1078 A _48317 s _48316) = (term1080 A _48317 s _48316).
Proof. exact (@lem4117865 (_48316 = _48317) (term1077 A _48317 s _48316)). Qed.
Lemma lem4117867 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : term1080 A _48317 s _48316.
Proof. exact (EQ_MP (@lem4117866 A _48317 s _48316) (@lem4117863 A _48317 s _48316)). Qed.
Lemma lem4117877 {A : Type'} (x : A) (y : A) (z : A) : term1081 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem4117879 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4117880 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4117879 A x). Qed.
Lemma lem4117881 {A : Type'} (x : A -> A) (a' : A) : (x a') = (x a').
Proof. exact (@lem4117880 A (x a')). Qed.
Lemma lem4117882 {A : Type'} (x : A -> A) (a' : A) : term1082 A x a'.
Proof. exact (fun h0 : term1083 A x a' => @lem4117881 A x a'). Qed.
Lemma lem4117884 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4117885 {A : Type'} (x : A -> A) (a' : A) : (term1082 A x a') = ((x a') = (x a')).
Proof. exact (@lem4117884 ((x a') = (x a'))). Qed.
Lemma lem4117886 {A : Type'} (x : A -> A) (a' : A) : (x a') = (x a').
Proof. exact (EQ_MP (@lem4117885 A x a') (@lem4117882 A x a')). Qed.
Lemma lem4117889 {A : Type'} (s : A -> Prop) (x : A -> A) (a' : A) (h1 : term1061 A s x a') : term1061 A s x a'.
Proof. exact (h1). Qed.
Lemma lem4117890 {A : Type'} (s : A -> Prop) (x : A -> A) (a' : A) (h1 : term1061 A s x a') : term1084 A s x a'.
Proof. exact (fun h0 : term1059 A s x a' => @lem4117889 A s x a' h1). Qed.
Lemma lem4117892 (p : Prop) : (term1085 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4117893 {A : Type'} (s : A -> Prop) (x : A -> A) (a' : A) : (term1084 A s x a') = (term1061 A s x a').
Proof. exact (@lem4117892 (term1059 A s x a')). Qed.
Lemma lem4117894 {A : Type'} (s : A -> Prop) (x : A -> A) (a' : A) (h1 : term1061 A s x a') : term1061 A s x a'.
Proof. exact (EQ_MP (@lem4117893 A s x a') (@lem4117890 A s x a' h1)). Qed.
Lemma lem4117896 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : s a.
Proof. exact (proj1 (@lem4117534 A a x s a' h1)). Qed.
Lemma lem4117897 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1086 A s a.
Proof. exact (fun h0 : term689 A s a => @lem4117896 A a x s a' h1). Qed.
Lemma lem4117899 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4117900 {A : Type'} (s : A -> Prop) (a : A) : (term1086 A s a) = (s a).
Proof. exact (@lem4117899 (s a)). Qed.
Lemma lem4117901 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : s a.
Proof. exact (EQ_MP (@lem4117900 A s a) (@lem4117897 A a x s a' h1)). Qed.
Lemma lem4117907 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4117908 {A : Type'} (a' : A) (s : A -> Prop) (_48305 : A) : (term767 A s _48305 a') = (term1066 A a' s _48305).
Proof. exact (@lem4117907 (_48305 = a') (term689 A s _48305)). Qed.
Lemma lem4117916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4117917 {A : Type'} (a' : A) (s : A -> Prop) (_48305 : A) : (term1067 A s _48305 a') = (term1068 A a' s _48305).
Proof. exact (MK_COMB (@lem4117916) (@lem4117908 A a' s _48305)). Qed.
Lemma lem4117925 {A : Type'} (a' : A) (s : A -> Prop) (_48305 : A) : (term1066 A a' s _48305) = (term1066 A a' s _48305).
Proof. exact (eq_refl (term1066 A a' s _48305)). Qed.
Lemma lem4117926 {A : Type'} (a' : A) (s : A -> Prop) (_48305 : A) : ((term767 A s _48305 a') = (term1066 A a' s _48305)) = ((term1066 A a' s _48305) = (term1066 A a' s _48305)).
Proof. exact (MK_COMB (@lem4117917 A a' s _48305) (@lem4117925 A a' s _48305)). Qed.
Lemma lem4117928 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4117929 (x : Prop) : (x = x) = True.
Proof. exact (@lem4117928 Prop x). Qed.
Lemma lem4117930 {A : Type'} (a' : A) (s : A -> Prop) (_48305 : A) : ((term1066 A a' s _48305) = (term1066 A a' s _48305)) = True.
Proof. exact (@lem4117929 (term1066 A a' s _48305)). Qed.
Lemma lem4117931 {A : Type'} (a' : A) (s : A -> Prop) (_48305 : A) : ((term767 A s _48305 a') = (term1066 A a' s _48305)) = True.
Proof. exact (TRANS (@lem4117926 A a' s _48305) (@lem4117930 A a' s _48305)). Qed.
Lemma lem4117932 {A : Type'} (a' : A) (s : A -> Prop) (_48305 : A) : True = ((term767 A s _48305 a') = (term1066 A a' s _48305)).
Proof. exact (SYM (@lem4117931 A a' s _48305)). Qed.
Lemma lem4117933 {A : Type'} (a' : A) (s : A -> Prop) (_48305 : A) : (term767 A s _48305 a') = (term1066 A a' s _48305).
Proof. exact (EQ_MP (@lem4117932 A a' s _48305) (@lem0)). Qed.
Lemma lem4117934 {A : Type'} (_48305 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1066 A a' s _48305.
Proof. exact (EQ_MP (@lem4117933 A a' s _48305) (@lem4117686 A _48305 a x s a' h1)). Qed.
Lemma lem4117936 (b : Prop) (a : Prop) : (a \/ b) = (term1069 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4117937 {A : Type'} (s : A -> Prop) (_48305 : A) (a' : A) : (term1066 A a' s _48305) = (term1070 A s _48305 a').
Proof. exact (@lem4117936 (term689 A s _48305) (_48305 = a')). Qed.
Lemma lem4117939 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4117940 {A : Type'} (s : A -> Prop) (_48305 : A) : (term727 A s _48305) = (s _48305).
Proof. exact (@lem4117939 (s _48305)). Qed.
Lemma lem4117941 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4117942 {A : Type'} (s : A -> Prop) (_48305 : A) : (term1071 A s _48305) = (term708 A s _48305).
Proof. exact (MK_COMB (@lem4117941) (@lem4117940 A s _48305)). Qed.
Lemma lem4117943 {A : Type'} (_48305 : A) (a' : A) : (_48305 = a') = (_48305 = a').
Proof. exact (eq_refl (_48305 = a')). Qed.
Lemma lem4117944 {A : Type'} (s : A -> Prop) (_48305 : A) (a' : A) : (term1070 A s _48305 a') = (term710 A s _48305 a').
Proof. exact (MK_COMB (@lem4117942 A s _48305) (@lem4117943 A _48305 a')). Qed.
Lemma lem4117945 {A : Type'} (s : A -> Prop) (_48305 : A) (a' : A) : (term1066 A a' s _48305) = (term710 A s _48305 a').
Proof. exact (TRANS (@lem4117937 A s _48305 a') (@lem4117944 A s _48305 a')). Qed.
Lemma lem4117948 {A : Type'} (_48305 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term710 A s _48305 a'.
Proof. exact (EQ_MP (@lem4117945 A s _48305 a') (@lem4117934 A _48305 a x s a' h1)). Qed.
Lemma lem4117949 {A : Type'} (_48305 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term710 A s _48305 a'.
Proof. exact (@lem4117948 A _48305 a x s a' h1). Qed.
Lemma lem4117950 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term710 A s a a'.
Proof. exact (@lem4117949 A a a x s a' h1). Qed.
Lemma lem4117953 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : a = a'.
Proof. exact (@lem4117950 A a x s a' h1 (@lem4117901 A a x s a' h1)). Qed.
Lemma lem4117954 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1087 A a a'.
Proof. exact (fun h0 : term1088 A a a' => @lem4117953 A a x s a' h1). Qed.
Lemma lem4117956 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4117957 {A : Type'} (a : A) (a' : A) : (term1087 A a a') = (a = a').
Proof. exact (@lem4117956 (a = a')). Qed.
Lemma lem4117958 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : a = a'.
Proof. exact (EQ_MP (@lem4117957 A a a') (@lem4117954 A a x s a' h1)). Qed.
Lemma lem4117960 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : s a.
Proof. exact (proj1 (@lem4117534 A a x s a' h1)). Qed.
Lemma lem4117961 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1086 A s a.
Proof. exact (fun h0 : term689 A s a => @lem4117960 A a x s a' h1). Qed.
Lemma lem4117963 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4117964 {A : Type'} (s : A -> Prop) (a : A) : (term1086 A s a) = (s a).
Proof. exact (@lem4117963 (s a)). Qed.
Lemma lem4117965 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : s a.
Proof. exact (EQ_MP (@lem4117964 A s a) (@lem4117961 A a x s a' h1)). Qed.
Lemma lem4117971 (q : Prop) (p : Prop) (r : Prop) : (term1089 p q r) = (term1089 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4117972 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : (term1080 A _48317 s _48316) = (term1090 A _48317 s _48316).
Proof. exact (@lem4117971 (s _48317) (term1088 A _48316 _48317) (term689 A s _48316)). Qed.
Lemma lem4117986 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4117987 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : (term1091 A _48317 s _48316) = (term1092 A s _48316 _48317).
Proof. exact (@lem4117986 (term689 A s _48316) (term1088 A _48316 _48317)). Qed.
Lemma lem4117995 {A : Type'} (s : A -> Prop) (_48317 : A) : (term1093 A s _48317) = (term1093 A s _48317).
Proof. exact (eq_refl (term1093 A s _48317)). Qed.
Lemma lem4117996 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : (term1090 A _48317 s _48316) = (term1094 A s _48316 _48317).
Proof. exact (MK_COMB (@lem4117995 A s _48317) (@lem4117987 A s _48316 _48317)). Qed.
Lemma lem4118007 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : (term1080 A _48317 s _48316) = (term1094 A s _48316 _48317).
Proof. exact (TRANS (@lem4117972 A _48317 s _48316) (@lem4117996 A s _48316 _48317)). Qed.
Lemma lem4118008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4118009 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : (term1095 A _48317 s _48316) = (term1096 A s _48316 _48317).
Proof. exact (MK_COMB (@lem4118008) (@lem4118007 A s _48316 _48317)). Qed.
Lemma lem4118023 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4118024 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : (term1091 A _48317 s _48316) = (term1092 A s _48316 _48317).
Proof. exact (@lem4118023 (term689 A s _48316) (term1088 A _48316 _48317)). Qed.
Lemma lem4118032 {A : Type'} (s : A -> Prop) (_48317 : A) : (term1093 A s _48317) = (term1093 A s _48317).
Proof. exact (eq_refl (term1093 A s _48317)). Qed.
Lemma lem4118033 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : (term1090 A _48317 s _48316) = (term1094 A s _48316 _48317).
Proof. exact (MK_COMB (@lem4118032 A s _48317) (@lem4118024 A s _48316 _48317)). Qed.
Lemma lem4118044 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : ((term1080 A _48317 s _48316) = (term1090 A _48317 s _48316)) = ((term1094 A s _48316 _48317) = (term1094 A s _48316 _48317)).
Proof. exact (MK_COMB (@lem4118009 A s _48316 _48317) (@lem4118033 A s _48316 _48317)). Qed.
Lemma lem4118046 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4118047 (x : Prop) : (x = x) = True.
Proof. exact (@lem4118046 Prop x). Qed.
Lemma lem4118048 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : ((term1094 A s _48316 _48317) = (term1094 A s _48316 _48317)) = True.
Proof. exact (@lem4118047 (term1094 A s _48316 _48317)). Qed.
Lemma lem4118049 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : ((term1080 A _48317 s _48316) = (term1090 A _48317 s _48316)) = True.
Proof. exact (TRANS (@lem4118044 A s _48316 _48317) (@lem4118048 A s _48316 _48317)). Qed.
Lemma lem4118050 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : True = ((term1080 A _48317 s _48316) = (term1090 A _48317 s _48316)).
Proof. exact (SYM (@lem4118049 A _48317 s _48316)). Qed.
Lemma lem4118051 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : (term1080 A _48317 s _48316) = (term1090 A _48317 s _48316).
Proof. exact (EQ_MP (@lem4118050 A _48317 s _48316) (@lem0)). Qed.
Lemma lem4118052 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : term1090 A _48317 s _48316.
Proof. exact (EQ_MP (@lem4118051 A _48317 s _48316) (@lem4117867 A _48317 s _48316)). Qed.
Lemma lem4118054 (b : Prop) (a : Prop) : (a \/ b) = (term1069 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4118055 {A : Type'} (_48316 : A) (s : A -> Prop) (_48317 : A) : (term1090 A _48317 s _48316) = (term1097 A _48316 s _48317).
Proof. exact (@lem4118054 (term1091 A _48317 s _48316) (s _48317)). Qed.
Lemma lem4118057 (a : Prop) (b : Prop) : (term1098 a b) = (term1099 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4118058 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : (term1100 A _48317 s _48316) = (term1101 A _48317 s _48316).
Proof. exact (@lem4118057 (term1088 A _48316 _48317) (term689 A s _48316)). Qed.
Lemma lem4118060 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4118061 {A : Type'} (_48316 : A) (_48317 : A) : (term1102 A _48316 _48317) = (_48316 = _48317).
Proof. exact (@lem4118060 (_48316 = _48317)). Qed.
Lemma lem4118062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4118063 {A : Type'} (_48316 : A) (_48317 : A) : (term1103 A _48316 _48317) = (term1104 A _48316 _48317).
Proof. exact (MK_COMB (@lem4118062) (@lem4118061 A _48316 _48317)). Qed.
Lemma lem4118065 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4118066 {A : Type'} (s : A -> Prop) (_48316 : A) : (term727 A s _48316) = (s _48316).
Proof. exact (@lem4118065 (s _48316)). Qed.
Lemma lem4118067 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : (term1101 A _48317 s _48316) = (term1105 A _48317 s _48316).
Proof. exact (MK_COMB (@lem4118063 A _48316 _48317) (@lem4118066 A s _48316)). Qed.
Lemma lem4118068 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : (term1100 A _48317 s _48316) = (term1105 A _48317 s _48316).
Proof. exact (TRANS (@lem4118058 A _48317 s _48316) (@lem4118067 A _48317 s _48316)). Qed.
Lemma lem4118069 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4118070 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : (term1106 A _48317 s _48316) = (term1107 A _48317 s _48316).
Proof. exact (MK_COMB (@lem4118069) (@lem4118068 A _48317 s _48316)). Qed.
Lemma lem4118071 {A : Type'} (s : A -> Prop) (_48317 : A) : (s _48317) = (s _48317).
Proof. exact (eq_refl (s _48317)). Qed.
Lemma lem4118072 {A : Type'} (_48316 : A) (s : A -> Prop) (_48317 : A) : (term1097 A _48316 s _48317) = (term1108 A _48316 s _48317).
Proof. exact (MK_COMB (@lem4118070 A _48317 s _48316) (@lem4118071 A s _48317)). Qed.
Lemma lem4118073 {A : Type'} (_48316 : A) (s : A -> Prop) (_48317 : A) : (term1090 A _48317 s _48316) = (term1108 A _48316 s _48317).
Proof. exact (TRANS (@lem4118055 A _48316 s _48317) (@lem4118072 A _48316 s _48317)). Qed.
Lemma lem4118075 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1105 A a' s a.
Proof. exact (conj (@lem4117958 A a x s a' h1) (@lem4117965 A a x s a' h1)). Qed.
Lemma lem4118077 {A : Type'} (_48316 : A) (s : A -> Prop) (_48317 : A) : term1108 A _48316 s _48317.
Proof. exact (EQ_MP (@lem4118073 A _48316 s _48317) (@lem4118052 A _48317 s _48316)). Qed.
Lemma lem4118078 {A : Type'} (_48316 : A) (s : A -> Prop) (_48317 : A) : term1108 A _48316 s _48317.
Proof. exact (@lem4118077 A _48316 s _48317). Qed.
Lemma lem4118079 {A : Type'} (a : A) (s : A -> Prop) (a' : A) : term1108 A a s a'.
Proof. exact (@lem4118078 A a s a'). Qed.
Lemma lem4118082 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : s a'.
Proof. exact (@lem4118079 A a s a' (@lem4118075 A a x s a' h1)). Qed.
Lemma lem4118083 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1086 A s a'.
Proof. exact (fun h0 : term689 A s a' => @lem4118082 A a x s a' h1). Qed.
Lemma lem4118085 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4118086 {A : Type'} (s : A -> Prop) (a' : A) : (term1086 A s a') = (s a').
Proof. exact (@lem4118085 (s a')). Qed.
Lemma lem4118087 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : s a'.
Proof. exact (EQ_MP (@lem4118086 A s a') (@lem4118083 A a x s a' h1)). Qed.
Lemma lem4118089 (b : Prop) (a : Prop) : (a \/ b) = (term1069 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4118090 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : (term1080 A _48317 s _48316) = (term1109 A s _48316 _48317).
Proof. exact (@lem4118089 (term1077 A _48317 s _48316) (term1088 A _48316 _48317)). Qed.
Lemma lem4118092 (a : Prop) (b : Prop) : (term1098 a b) = (term1099 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4118093 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : (term1110 A _48317 s _48316) = (term1111 A _48317 s _48316).
Proof. exact (@lem4118092 (s _48317) (term689 A s _48316)). Qed.
Lemma lem4118095 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4118096 {A : Type'} (s : A -> Prop) (_48316 : A) : (term727 A s _48316) = (s _48316).
Proof. exact (@lem4118095 (s _48316)). Qed.
Lemma lem4118097 {A : Type'} (s : A -> Prop) (_48317 : A) : (term1112 A s _48317) = (term1112 A s _48317).
Proof. exact (eq_refl (term1112 A s _48317)). Qed.
Lemma lem4118098 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : (term1111 A _48317 s _48316) = (term1113 A _48317 s _48316).
Proof. exact (MK_COMB (@lem4118097 A s _48317) (@lem4118096 A s _48316)). Qed.
Lemma lem4118099 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : (term1110 A _48317 s _48316) = (term1113 A _48317 s _48316).
Proof. exact (TRANS (@lem4118093 A _48317 s _48316) (@lem4118098 A _48317 s _48316)). Qed.
Lemma lem4118100 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4118101 {A : Type'} (_48317 : A) (s : A -> Prop) (_48316 : A) : (term1114 A _48317 s _48316) = (term1115 A _48317 s _48316).
Proof. exact (MK_COMB (@lem4118100) (@lem4118099 A _48317 s _48316)). Qed.
Lemma lem4118102 {A : Type'} (_48316 : A) (_48317 : A) : (term1088 A _48316 _48317) = (term1088 A _48316 _48317).
Proof. exact (eq_refl (term1088 A _48316 _48317)). Qed.
Lemma lem4118103 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : (term1109 A s _48316 _48317) = (term1116 A s _48316 _48317).
Proof. exact (MK_COMB (@lem4118101 A _48317 s _48316) (@lem4118102 A _48316 _48317)). Qed.
Lemma lem4118104 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : (term1080 A _48317 s _48316) = (term1116 A s _48316 _48317).
Proof. exact (TRANS (@lem4118090 A s _48316 _48317) (@lem4118103 A s _48316 _48317)). Qed.
Lemma lem4118106 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1061 A s x a') (h2 : term986 A a x s a') : term1117 A x s a'.
Proof. exact (conj (@lem4117894 A s x a' h1) (@lem4118087 A a x s a' h2)). Qed.
Lemma lem4118108 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : term1116 A s _48316 _48317.
Proof. exact (EQ_MP (@lem4118104 A s _48316 _48317) (@lem4117867 A _48317 s _48316)). Qed.
Lemma lem4118109 {A : Type'} (s : A -> Prop) (_48316 : A) (_48317 : A) : term1116 A s _48316 _48317.
Proof. exact (@lem4118108 A s _48316 _48317). Qed.
Lemma lem4118110 {A : Type'} (s : A -> Prop) (x : A -> A) (a' : A) : term1118 A s x a'.
Proof. exact (@lem4118109 A s a' (x a')). Qed.
Lemma lem4118113 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1061 A s x a') (h2 : term986 A a x s a') : term1119 A x a'.
Proof. exact (@lem4118110 A s x a' (@lem4118106 A a x s a' h1 h2)). Qed.
Lemma lem4118114 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1061 A s x a') (h2 : term986 A a x s a') : term1120 A x a'.
Proof. exact (fun h0 : a' = (x a') => @lem4118113 A a x s a' h1 h2). Qed.
Lemma lem4118116 (p : Prop) : (term1085 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4118117 {A : Type'} (x : A -> A) (a' : A) : (term1120 A x a') = (term1119 A x a').
Proof. exact (@lem4118116 (a' = (x a'))). Qed.
Lemma lem4118118 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1061 A s x a') (h2 : term986 A a x s a') : term1119 A x a'.
Proof. exact (EQ_MP (@lem4118117 A x a') (@lem4118114 A a x s a' h1 h2)). Qed.
Lemma lem4118120 (b : Prop) (a : Prop) : (a \/ b) = (term1069 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4118121 {A : Type'} (z : A) (x : A) (y : A) : (term1081 A x y z) = (term1121 A z x y).
Proof. exact (@lem4118120 (term1122 A x y z) (term1088 A x y)). Qed.
Lemma lem4118123 (a : Prop) (b : Prop) : (term1098 a b) = (term1099 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4118124 {A : Type'} (x : A) (y : A) (z : A) : (term1123 A x y z) = (term1124 A x y z).
Proof. exact (@lem4118123 (term1088 A x z) (y = z)). Qed.
Lemma lem4118126 (a : Prop) : (term169 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4118127 {A : Type'} (x : A) (z : A) : (term1102 A x z) = (x = z).
Proof. exact (@lem4118126 (x = z)). Qed.
Lemma lem4118128 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4118129 {A : Type'} (x : A) (z : A) : (term1103 A x z) = (term1104 A x z).
Proof. exact (MK_COMB (@lem4118128) (@lem4118127 A x z)). Qed.
Lemma lem4118130 {A : Type'} (y : A) (z : A) : (term1088 A y z) = (term1088 A y z).
Proof. exact (eq_refl (term1088 A y z)). Qed.
Lemma lem4118131 {A : Type'} (x : A) (y : A) (z : A) : (term1124 A x y z) = (term1125 A x y z).
Proof. exact (MK_COMB (@lem4118129 A x z) (@lem4118130 A y z)). Qed.
Lemma lem4118132 {A : Type'} (x : A) (y : A) (z : A) : (term1123 A x y z) = (term1125 A x y z).
Proof. exact (TRANS (@lem4118124 A x y z) (@lem4118131 A x y z)). Qed.
Lemma lem4118133 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4118134 {A : Type'} (x : A) (y : A) (z : A) : (term1126 A x y z) = (term1127 A x y z).
Proof. exact (MK_COMB (@lem4118133) (@lem4118132 A x y z)). Qed.
Lemma lem4118135 {A : Type'} (x : A) (y : A) : (term1088 A x y) = (term1088 A x y).
Proof. exact (eq_refl (term1088 A x y)). Qed.
Lemma lem4118136 {A : Type'} (z : A) (x : A) (y : A) : (term1121 A z x y) = (term1128 A z x y).
Proof. exact (MK_COMB (@lem4118134 A x y z) (@lem4118135 A x y)). Qed.
Lemma lem4118137 {A : Type'} (z : A) (x : A) (y : A) : (term1081 A x y z) = (term1128 A z x y).
Proof. exact (TRANS (@lem4118121 A z x y) (@lem4118136 A z x y)). Qed.
Lemma lem4118139 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1061 A s x a') (h2 : term986 A a x s a') : term1129 A x a'.
Proof. exact (conj (@lem4117886 A x a') (@lem4118118 A a x s a' h1 h2)). Qed.
Lemma lem4118141 {A : Type'} (z : A) (x : A) (y : A) : term1128 A z x y.
Proof. exact (EQ_MP (@lem4118137 A z x y) (@lem4117877 A x y z)). Qed.
Lemma lem4118142 {A : Type'} (z : A) (x : A) (y : A) : term1128 A z x y.
Proof. exact (@lem4118141 A z x y). Qed.
Lemma lem4118143 {A : Type'} (x : A -> A) (a' : A) : term1130 A x a'.
Proof. exact (@lem4118142 A (x a') (x a') a'). Qed.
Lemma lem4118146 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1061 A s x a') (h2 : term986 A a x s a') : term1056 A x a'.
Proof. exact (@lem4118143 A x a' (@lem4118139 A a x s a' h1 h2)). Qed.
Lemma lem4118147 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1061 A s x a') (h2 : term986 A a x s a') : term1131 A x a'.
Proof. exact (fun h0 : (x a') = a' => @lem4118146 A a x s a' h1 h2). Qed.
Lemma lem4118149 (p : Prop) : (term1085 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4118150 {A : Type'} (x : A -> A) (a' : A) : (term1131 A x a') = (term1056 A x a').
Proof. exact (@lem4118149 ((x a') = a')). Qed.
Lemma lem4118151 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1061 A s x a') (h2 : term986 A a x s a') : term1056 A x a'.
Proof. exact (EQ_MP (@lem4118150 A x a') (@lem4118147 A a x s a' h1 h2)). Qed.
Lemma lem4118153 (b : Prop) (a : Prop) : (a \/ b) = (term1069 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4118156 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : (term1057 A s x _48306) = (term1132 A s x _48306).
Proof. exact (@lem4118153 ((x _48306) = _48306) (term1059 A s x _48306)). Qed.
Lemma lem4118159 {A : Type'} (_48306 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1132 A s x _48306.
Proof. exact (EQ_MP (@lem4118156 A s x _48306) (@lem4117694 A _48306 a x s a' h1)). Qed.
Lemma lem4118160 {A : Type'} (_48306 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1132 A s x _48306.
Proof. exact (@lem4118159 A _48306 a x s a' h1). Qed.
Lemma lem4118161 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1132 A s x a'.
Proof. exact (@lem4118160 A a' a x s a' h1). Qed.
Lemma lem4118164 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1061 A s x a') (h2 : term986 A a x s a') : term1059 A s x a'.
Proof. exact (@lem4118161 A a x s a' h2 (@lem4118151 A a x s a' h1 h2)). Qed.
Lemma lem4118165 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1060 A s x a'.
Proof. exact (fun h0 : term1061 A s x a' => @lem4118164 A a x s a' h0 h1). Qed.
Lemma lem4118167 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4118168 {A : Type'} (s : A -> Prop) (x : A -> A) (a' : A) : (term1060 A s x a') = (term1059 A s x a').
Proof. exact (@lem4118167 (term1059 A s x a')). Qed.
Lemma lem4118169 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1059 A s x a'.
Proof. exact (EQ_MP (@lem4118168 A s x a') (@lem4118165 A a x s a' h1)). Qed.
Lemma lem4118172 {A : Type'} (x : A -> A) (a' : A) (h1 : term1056 A x a') : term1056 A x a'.
Proof. exact (h1). Qed.
Lemma lem4118173 {A : Type'} (x : A -> A) (a' : A) (h1 : term1056 A x a') : term1131 A x a'.
Proof. exact (fun h0 : (x a') = a' => @lem4118172 A x a' h1). Qed.
Lemma lem4118175 (p : Prop) : (term1085 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4118176 {A : Type'} (x : A -> A) (a' : A) : (term1131 A x a') = (term1056 A x a').
Proof. exact (@lem4118175 ((x a') = a')). Qed.
Lemma lem4118177 {A : Type'} (x : A -> A) (a' : A) (h1 : term1056 A x a') : term1056 A x a'.
Proof. exact (EQ_MP (@lem4118176 A x a') (@lem4118173 A x a' h1)). Qed.
Lemma lem4118179 (b : Prop) (a : Prop) : (a \/ b) = (term1069 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4118182 {A : Type'} (a' : A) (s : A -> Prop) (_48305 : A) : (term767 A s _48305 a') = (term1133 A a' s _48305).
Proof. exact (@lem4118179 (_48305 = a') (term689 A s _48305)). Qed.
Lemma lem4118185 {A : Type'} (_48305 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1133 A a' s _48305.
Proof. exact (EQ_MP (@lem4118182 A a' s _48305) (@lem4117686 A _48305 a x s a' h1)). Qed.
Lemma lem4118186 {A : Type'} (_48305 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1133 A a' s _48305.
Proof. exact (@lem4118185 A _48305 a x s a' h1). Qed.
Lemma lem4118187 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1134 A s x a'.
Proof. exact (@lem4118186 A (x a') a x s a' h1). Qed.
Lemma lem4118190 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1056 A x a') (h2 : term986 A a x s a') : term1061 A s x a'.
Proof. exact (@lem4118187 A a x s a' h2 (@lem4118177 A x a' h1)). Qed.
Lemma lem4118191 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1056 A x a') (h2 : term986 A a x s a') : term1084 A s x a'.
Proof. exact (fun h0 : term1059 A s x a' => @lem4118190 A a x s a' h1 h2). Qed.
Lemma lem4118193 (p : Prop) : (term1085 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4118194 {A : Type'} (s : A -> Prop) (x : A -> A) (a' : A) : (term1084 A s x a') = (term1061 A s x a').
Proof. exact (@lem4118193 (term1059 A s x a')). Qed.
Lemma lem4118195 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1056 A x a') (h2 : term986 A a x s a') : term1061 A s x a'.
Proof. exact (EQ_MP (@lem4118194 A s x a') (@lem4118191 A a x s a' h1 h2)). Qed.
Lemma lem4118208 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4118209 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : (term1135 A s x _48306) = (term1057 A s x _48306).
Proof. exact (@lem4118208 (term1059 A s x _48306) ((x _48306) = _48306)). Qed.
Lemma lem4118217 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : (term1136 A s x _48306) = (term1136 A s x _48306).
Proof. exact (eq_refl (term1136 A s x _48306)). Qed.
Lemma lem4118218 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : ((term1057 A s x _48306) = (term1135 A s x _48306)) = ((term1057 A s x _48306) = (term1057 A s x _48306)).
Proof. exact (MK_COMB (@lem4118217 A s x _48306) (@lem4118209 A s x _48306)). Qed.
Lemma lem4118220 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4118221 (x : Prop) : (x = x) = True.
Proof. exact (@lem4118220 Prop x). Qed.
Lemma lem4118222 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : ((term1057 A s x _48306) = (term1057 A s x _48306)) = True.
Proof. exact (@lem4118221 (term1057 A s x _48306)). Qed.
Lemma lem4118223 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : ((term1057 A s x _48306) = (term1135 A s x _48306)) = True.
Proof. exact (TRANS (@lem4118218 A s x _48306) (@lem4118222 A s x _48306)). Qed.
Lemma lem4118224 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : True = ((term1057 A s x _48306) = (term1135 A s x _48306)).
Proof. exact (SYM (@lem4118223 A s x _48306)). Qed.
Lemma lem4118225 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : (term1057 A s x _48306) = (term1135 A s x _48306).
Proof. exact (EQ_MP (@lem4118224 A s x _48306) (@lem0)). Qed.
Lemma lem4118226 {A : Type'} (_48306 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1135 A s x _48306.
Proof. exact (EQ_MP (@lem4118225 A s x _48306) (@lem4117694 A _48306 a x s a' h1)). Qed.
Lemma lem4118228 (b : Prop) (a : Prop) : (a \/ b) = (term1069 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4118231 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : (term1135 A s x _48306) = (term1137 A s x _48306).
Proof. exact (@lem4118228 (term1059 A s x _48306) ((x _48306) = _48306)). Qed.
Lemma lem4118234 {A : Type'} (_48306 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1137 A s x _48306.
Proof. exact (EQ_MP (@lem4118231 A s x _48306) (@lem4118226 A _48306 a x s a' h1)). Qed.
Lemma lem4118235 {A : Type'} (_48306 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1137 A s x _48306.
Proof. exact (@lem4118234 A _48306 a x s a' h1). Qed.
Lemma lem4118236 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1137 A s x a'.
Proof. exact (@lem4118235 A a' a x s a' h1). Qed.
Lemma lem4118239 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1056 A x a') (h2 : term986 A a x s a') : (x a') = a'.
Proof. exact (@lem4118236 A a x s a' h2 (@lem4118195 A a x s a' h1 h2)). Qed.
Lemma lem4118240 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1073 A x a'.
Proof. exact (fun h0 : term1056 A x a' => @lem4118239 A a x s a' h0 h1). Qed.
Lemma lem4118242 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4118243 {A : Type'} (x : A -> A) (a' : A) : (term1073 A x a') = ((x a') = a').
Proof. exact (@lem4118242 ((x a') = a')). Qed.
Lemma lem4118244 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : (x a') = a'.
Proof. exact (EQ_MP (@lem4118243 A x a') (@lem4118240 A a x s a' h1)). Qed.
Lemma lem4118246 (a : Prop) (b : Prop) : (term1138 a b) = (term1139 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4118247 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : (term1058 A s x _48306) = (term1140 A s x _48306).
Proof. exact (@lem4118246 (term1059 A s x _48306) ((x _48306) = _48306)). Qed.
Lemma lem4118249 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4118250 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : (term1140 A s x _48306) = (term1141 A s x _48306).
Proof. exact (@lem4118249 (term1142 A s x _48306)). Qed.
Lemma lem4118251 {A : Type'} (s : A -> Prop) (x : A -> A) (_48306 : A) : (term1058 A s x _48306) = (term1141 A s x _48306).
Proof. exact (TRANS (@lem4118247 A s x _48306) (@lem4118250 A s x _48306)). Qed.
Lemma lem4118253 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1142 A s x a'.
Proof. exact (conj (@lem4118169 A a x s a' h1) (@lem4118244 A a x s a' h1)). Qed.
Lemma lem4118255 {A : Type'} (_48306 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1141 A s x _48306.
Proof. exact (EQ_MP (@lem4118251 A s x _48306) (@lem4117700 A _48306 a x s a' h1)). Qed.
Lemma lem4118256 {A : Type'} (_48306 : A) (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1141 A s x _48306.
Proof. exact (@lem4118255 A _48306 a x s a' h1). Qed.
Lemma lem4118257 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1141 A s x a'.
Proof. exact (@lem4118256 A a' a x s a' h1). Qed.
Lemma lem4118260 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : False.
Proof. exact (@lem4118257 A a x s a' h1 (@lem4118253 A a x s a' h1)). Qed.
Lemma lem4118261 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : term1065.
Proof. exact (fun h0 : ~ False => @lem4118260 A a x s a' h1). Qed.
Lemma lem4118263 (p : Prop) : (term1062 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4118264 : term1065 = False.
Proof. exact (@lem4118263 False). Qed.
Lemma lem4118265 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term986 A a x s a') : False.
Proof. exact (EQ_MP (@lem4118264) (@lem4118261 A a x s a' h1)). Qed.
Lemma lem4118266 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term692 A s) (h2 : term897 A a s x) : (term692 A s) = False.
Proof. exact (prop_ext (fun h3 : term692 A s => @lem4117749 A a s x h1 h2) (fun h3 : False => @lem4117554 A s h1)). Qed.
Lemma lem4118267 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term692 A s) (h2 : term897 A a s x) : False.
Proof. exact (EQ_MP (@lem4118266 A a s x h1 h2) (@lem4117554 A s h1)). Qed.
Lemma lem4118268 {A : Type'} (a : A) (s : A -> Prop) (x : A -> A) (h1 : term897 A a s x) : False.
Proof. exact (or_elim (@lem4117528 A a s x h1) (fun h0 : term692 A s => @lem4118267 A a s x h0 h1) (fun h0 : term819 A s a => @lem4117855 A a s x h0 h1)). Qed.
Lemma lem4118269 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1046 A a x s a') : False.
Proof. exact (or_elim (@lem4117524 A a x s a' h1) (fun h0 : term897 A a s x => @lem4118268 A a s x h0) (fun h0 : term986 A a x s a' => @lem4118265 A a x s a' h0)). Qed.
Lemma lem4118270 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1046 A a x s a') : (term1046 A a x s a') = False.
Proof. exact (prop_ext (fun h2 : term1046 A a x s a' => @lem4118269 A a x s a' h1) (fun h2 : False => @lem4117524 A a x s a' h1)). Qed.
Lemma lem4118271 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (a' : A) (h1 : term1046 A a x s a') : False.
Proof. exact (EQ_MP (@lem4118270 A a x s a' h1) (@lem4117524 A a x s a' h1)). Qed.
Lemma lem4118272 {A : Type'} (a : A) (x : A -> A) (s : A -> Prop) (h1 : term1049 A a x s) : False.
Proof. exact (ex_elim (@lem4117385 A a x s h1) (fun a' : A => fun h0 : term1048 A a x s a' => @lem4118271 A a x s a' h0)). Qed.
Lemma lem4118273 {A : Type'} (a : A) (s : A -> Prop) (h1 : term1051 A a s) : False.
Proof. exact (ex_elim (@lem4117384 A a s h1) (fun x : A -> A => fun h0 : term1050 A a s x => @lem4118272 A a x s h0)). Qed.
Lemma lem4118274 {A : Type'} (s : A -> Prop) (h1 : term718 A s) : False.
Proof. exact (ex_elim (@lem4117383 A s h1) (fun a : A => fun h0 : term1052 A s a => @lem4118273 A a s h0)). Qed.
Lemma lem4118275 {A : Type'} (s : A -> Prop) (h1 : term718 A s) : (term718 A s) = False.
Proof. exact (prop_ext (fun h2 : term718 A s => @lem4118274 A s h1) (fun h2 : False => @lem4116596 A s h1)). Qed.
Lemma lem4118276 {A : Type'} (s : A -> Prop) (h1 : term718 A s) : False.
Proof. exact (EQ_MP (@lem4118275 A s h1) (@lem4116596 A s h1)). Qed.
Lemma lem4118277 {A : Type'} (s : A -> Prop) : term717 A s.
Proof. exact (fun h0 : term718 A s => @lem4118276 A s h0). Qed.
Lemma lem4118278 {A : Type'} (s : A -> Prop) : (term705 A s) = (term715 A s).
Proof. exact (EQ_MP (@lem4116595 A s) (@lem4118277 A s)). Qed.
Lemma lem4118283 {A : Type'} : term726 A.
Proof. exact (fun s : A -> Prop => @lem4118278 A s). Qed.
Lemma lem4118284 {A : Type'} : term725 A.
Proof. exact (EQ_MP (@lem4116591 A) (@lem4118283 A)). Qed.
Lemma lem4118285 {A : Type'} (s : A -> Prop) : term1143 A s.
Proof. exact (@lem4118284 A s). Qed.
Lemma lem4118286 {A : Type'} (s : A -> Prop) : (term1143 A s) = (term717 A s).
Proof. exact (eq_refl (term1143 A s)). Qed.
Lemma lem4118287 {A : Type'} (s : A -> Prop) : term717 A s.
Proof. exact (EQ_MP (@lem4118286 A s) (@lem4118285 A s)). Qed.
Lemma lem4118289 {A : Type'} (s : A -> Prop) : term717 A s.
Proof. exact (@lem4116464 A s (@lem4118287 A s)). Qed.
Lemma lem4118290 {A : Type'} (s : A -> Prop) (h1 : term718 A s) : False.
Proof. exact (@lem4118289 A s (@lem4116448 A s h1)). Qed.
Lemma lem4118291 {A : Type'} (s : A -> Prop) (h1 : term718 A s) : (term718 A s) = False.
Proof. exact (prop_ext (fun h2 : term718 A s => @lem4118290 A s h1) (fun h2 : False => @lem4116448 A s h1)). Qed.
Lemma lem4118292 {A : Type'} (s : A -> Prop) (h1 : term718 A s) : False.
Proof. exact (EQ_MP (@lem4118291 A s h1) (@lem4116448 A s h1)). Qed.
Lemma lem4118293 {A : Type'} (s : A -> Prop) : term717 A s.
Proof. exact (fun h0 : term718 A s => @lem4118292 A s h0). Qed.
Lemma lem4118294 {A : Type'} (s : A -> Prop) : (term705 A s) = (term715 A s).
Proof. exact (EQ_MP (@lem4116447 A s) (@lem4118293 A s)). Qed.
Lemma lem4118295 {A : Type'} (s : A -> Prop) : (term679 A s) = (term686 A s).
Proof. exact (EQ_MP (@lem4116443 A s) (@lem4118294 A s)). Qed.
Lemma lem4118296 {A : Type'} (s : A -> Prop) : (term671 A s) = (term634 A s).
Proof. exact (EQ_MP (@lem4116295 A s) (@lem4118295 A s)). Qed.
Lemma lem4118297 {A : Type'} (s : A -> Prop) : (term642 A s) = (term634 A s).
Proof. exact (EQ_MP (@lem4116216 A s) (@lem4118296 A s)). Qed.
Lemma lem4118298 {A : Type'} (s : A -> Prop) : (term631 A s) = (term634 A s).
Proof. exact (EQ_MP (@lem4116165 A s) (@lem4118297 A s)). Qed.
Lemma lem4118299 {A : Type'} (s : A -> Prop) : (term630 A s) = (term634 A s).
Proof. exact (EQ_MP (@lem4116133 A s) (@lem4118298 A s)). Qed.
Lemma lem4118304 {A : Type'} : term1144 A.
Proof. exact (fun s : A -> Prop => @lem4118299 A s). Qed.
