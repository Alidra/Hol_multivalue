Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_SUBSET_EQ_term_abbrevs.
Require Import CARD_UNION_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_0_spec.
Require Import INT_POS_spec.
Require Import thm0_spec.
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
Require Import thm1820_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
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
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem3892953 {A : Type'} (s : A -> Prop) (h1 : (term0 A s) = (s = (@EMPTY A))) : (term0 A s) = (s = (@EMPTY A)).
Proof. exact (h1). Qed.
Lemma lem3892954 {A : Type'} (s : A -> Prop) (h1 : (term0 A s) = (s = (@EMPTY A))) : (s = (@EMPTY A)) = (term0 A s).
Proof. exact (SYM (@lem3892953 A s h1)). Qed.
Lemma lem3892955 {A : Type'} (s : A -> Prop) (h1 : (s = (@EMPTY A)) = (term0 A s)) : (s = (@EMPTY A)) = (term0 A s).
Proof. exact (h1). Qed.
Lemma lem3892956 {A : Type'} (s : A -> Prop) (h1 : (s = (@EMPTY A)) = (term0 A s)) : (term0 A s) = (s = (@EMPTY A)).
Proof. exact (SYM (@lem3892955 A s h1)). Qed.
Lemma lem3892957 {A : Type'} (s : A -> Prop) : ((term0 A s) = (s = (@EMPTY A))) = ((s = (@EMPTY A)) = (term0 A s)).
Proof. exact (prop_ext (fun h1 : (term0 A s) = (s = (@EMPTY A)) => @lem3892954 A s h1) (fun h1 : (s = (@EMPTY A)) = (term0 A s) => @lem3892956 A s h1)). Qed.
Lemma lem3892958 {A : Type'} : (term1 A) = (term2 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3892957 A s)). Qed.
Lemma lem3892959 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3892960 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (MK_COMB (@lem3892959 A) (@lem3892958 A)). Qed.
Lemma lem3892961 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem3892960 A) (@lem3864294 A)). Qed.
Lemma lem3892962 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (@lem3892961 A s). Qed.
Lemma lem3892963 {A : Type'} (s : A -> Prop) : (term5 A s) = ((s = (@EMPTY A)) = (term0 A s)).
Proof. exact (eq_refl (term5 A s)). Qed.
Lemma lem3893063 (a : nat) (b : nat) : ((a = (Nat.add a b)) = (b = (NUMERAL 0))) = (term6 a b).
Proof. exact (@lem17500 (a = (Nat.add a b)) (b = (NUMERAL 0))). Qed.
Lemma lem3893065 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3893066 (a : nat) (b : nat) : (a = (Nat.add a b)) = ((int_of_num a) = (term7 a b)).
Proof. exact (@lem3893065 a (Nat.add a b)). Qed.
Lemma lem3893070 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem3893071 (a : nat) (b : nat) : (term7 a b) = (term8 a b).
Proof. exact (@lem3893070 a b). Qed.
Lemma lem3893072 (a : nat) : (term9 a) = (term9 a).
Proof. exact (eq_refl (term9 a)). Qed.
Lemma lem3893073 (a : nat) (b : nat) : ((int_of_num a) = (term7 a b)) = ((int_of_num a) = (term8 a b)).
Proof. exact (MK_COMB (@lem3893072 a) (@lem3893071 a b)). Qed.
Lemma lem3893074 (a : nat) (b : nat) : (a = (Nat.add a b)) = ((int_of_num a) = (term8 a b)).
Proof. exact (TRANS (@lem3893066 a b) (@lem3893073 a b)). Qed.
Lemma lem3893075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3893076 (a : nat) (b : nat) : (term10 a b) = (term11 a b).
Proof. exact (MK_COMB (@lem3893075) (@lem3893074 a b)). Qed.
Lemma lem3893078 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3893079 (b : nat) : (b = (NUMERAL 0)) = ((int_of_num b) = term12).
Proof. exact (@lem3893078 b (NUMERAL 0)). Qed.
Lemma lem3893082 (a : nat) (b : nat) : (term13 a b) = (term14 a b).
Proof. exact (MK_COMB (@lem3893076 a b) (@lem3893079 b)). Qed.
Lemma lem3893083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3893084 (a : nat) (b : nat) : (term15 a b) = (term16 a b).
Proof. exact (MK_COMB (@lem3893083) (@lem3893082 a b)). Qed.
Lemma lem3893086 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3893087 (a : nat) (b : nat) : (a = (Nat.add a b)) = ((int_of_num a) = (term7 a b)).
Proof. exact (@lem3893086 a (Nat.add a b)). Qed.
Lemma lem3893091 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem3893092 (a : nat) (b : nat) : (term7 a b) = (term8 a b).
Proof. exact (@lem3893091 a b). Qed.
Lemma lem3893093 (a : nat) : (term9 a) = (term9 a).
Proof. exact (eq_refl (term9 a)). Qed.
Lemma lem3893094 (a : nat) (b : nat) : ((int_of_num a) = (term7 a b)) = ((int_of_num a) = (term8 a b)).
Proof. exact (MK_COMB (@lem3893093 a) (@lem3893092 a b)). Qed.
Lemma lem3893095 (a : nat) (b : nat) : (a = (Nat.add a b)) = ((int_of_num a) = (term8 a b)).
Proof. exact (TRANS (@lem3893087 a b) (@lem3893094 a b)). Qed.
Lemma lem3893096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3893097 (a : nat) (b : nat) : (term17 a b) = (term18 a b).
Proof. exact (MK_COMB (@lem3893096) (@lem3893095 a b)). Qed.
Lemma lem3893098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3893099 (a : nat) (b : nat) : (term19 a b) = (term20 a b).
Proof. exact (MK_COMB (@lem3893098) (@lem3893097 a b)). Qed.
Lemma lem3893101 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3893102 (b : nat) : (b = (NUMERAL 0)) = ((int_of_num b) = term12).
Proof. exact (@lem3893101 b (NUMERAL 0)). Qed.
Lemma lem3893105 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3893106 (b : nat) : (term21 b) = (term22 b).
Proof. exact (MK_COMB (@lem3893105) (@lem3893102 b)). Qed.
Lemma lem3893107 (a : nat) (b : nat) : (term23 a b) = (term24 a b).
Proof. exact (MK_COMB (@lem3893099 a b) (@lem3893106 b)). Qed.
Lemma lem3893108 (a : nat) (b : nat) : (term6 a b) = (term25 a b).
Proof. exact (MK_COMB (@lem3893084 a b) (@lem3893107 a b)). Qed.
Lemma lem3893109 (a : nat) (b : nat) : ((a = (Nat.add a b)) = (b = (NUMERAL 0))) = (term25 a b).
Proof. exact (TRANS (@lem3893063 a b) (@lem3893108 a b)). Qed.
Lemma lem3893110 (a : nat) : term26 a.
Proof. exact (@lem2307535 a). Qed.
Lemma lem3893111 (a : nat) : (term26 a) = (term27 a).
Proof. exact (eq_refl (term26 a)). Qed.
Lemma lem3893112 (a : nat) : term27 a.
Proof. exact (EQ_MP (@lem3893111 a) (@lem3893110 a)). Qed.
Lemma lem3893113 (b : nat) : term26 b.
Proof. exact (@lem2307535 b). Qed.
Lemma lem3893114 (b : nat) : (term26 b) = (term27 b).
Proof. exact (eq_refl (term26 b)). Qed.
Lemma lem3893115 (b : nat) : term27 b.
Proof. exact (EQ_MP (@lem3893114 b) (@lem3893113 b)). Qed.
Lemma lem3893116 (_45282 : int) (_45283 : int) : (term28 _45282 _45283) = (term29 _45282 _45283).
Proof. exact (@lem2318604 (term29 _45282 _45283)). Qed.
Lemma lem3893140 (_45282 : int) (_45283 : int) : (term30 _45282 _45283) = (term31 _45282 _45283).
Proof. exact (@lem17045 (_45282 = (int_add _45282 _45283)) (_45283 = term12)). Qed.
Lemma lem3893143 (_45282 : int) (_45283 : int) : (term32 _45282 _45283) = (_45282 = (int_add _45282 _45283)).
Proof. exact (@lem16933 (_45282 = (int_add _45282 _45283))). Qed.
Lemma lem3893146 (_45283 : int) : (term33 _45283) = (_45283 = term12).
Proof. exact (@lem16933 (_45283 = term12)). Qed.
Lemma lem3893147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3893148 (_45282 : int) (_45283 : int) : (term34 _45282 _45283) = (term35 _45282 _45283).
Proof. exact (MK_COMB (@lem3893147) (@lem3893143 _45282 _45283)). Qed.
Lemma lem3893149 (_45282 : int) (_45283 : int) : (term36 _45282 _45283) = (term37 _45282 _45283).
Proof. exact (MK_COMB (@lem3893148 _45282 _45283) (@lem3893146 _45283)). Qed.
Lemma lem3893150 (_45282 : int) (_45283 : int) : (term38 _45282 _45283) = (term36 _45282 _45283).
Proof. exact (@lem17045 (term39 _45282 _45283) (term40 _45283)). Qed.
Lemma lem3893151 (_45282 : int) (_45283 : int) : (term38 _45282 _45283) = (term37 _45282 _45283).
Proof. exact (TRANS (@lem3893150 _45282 _45283) (@lem3893149 _45282 _45283)). Qed.
Lemma lem3893152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3893153 (_45282 : int) (_45283 : int) : (term41 _45282 _45283) = (term42 _45282 _45283).
Proof. exact (MK_COMB (@lem3893152) (@lem3893140 _45282 _45283)). Qed.
Lemma lem3893154 (_45282 : int) (_45283 : int) : (term43 _45282 _45283) = (term44 _45282 _45283).
Proof. exact (MK_COMB (@lem3893153 _45282 _45283) (@lem3893151 _45282 _45283)). Qed.
Lemma lem3893155 (_45282 : int) (_45283 : int) : (term45 _45282 _45283) = (term43 _45282 _45283).
Proof. exact (@lem17160 (term46 _45282 _45283) (term47 _45282 _45283)). Qed.
Lemma lem3893156 (_45282 : int) (_45283 : int) : (term45 _45282 _45283) = (term44 _45282 _45283).
Proof. exact (TRANS (@lem3893155 _45282 _45283) (@lem3893154 _45282 _45283)). Qed.
Lemma lem3893158 (_45283 : int) : (term48 _45283) = (term48 _45283).
Proof. exact (eq_refl (term48 _45283)). Qed.
Lemma lem3893159 (_45282 : int) (_45283 : int) : (term49 _45282 _45283) = (term50 _45282 _45283).
Proof. exact (MK_COMB (@lem3893158 _45283) (@lem3893156 _45282 _45283)). Qed.
Lemma lem3893160 (_45282 : int) (_45283 : int) : (term51 _45282 _45283) = (term49 _45282 _45283).
Proof. exact (@lem17362 (term52 _45283) (term53 _45282 _45283)). Qed.
Lemma lem3893161 (_45282 : int) (_45283 : int) : (term51 _45282 _45283) = (term50 _45282 _45283).
Proof. exact (TRANS (@lem3893160 _45282 _45283) (@lem3893159 _45282 _45283)). Qed.
Lemma lem3893163 (_45282 : int) : (term48 _45282) = (term48 _45282).
Proof. exact (eq_refl (term48 _45282)). Qed.
Lemma lem3893164 (_45282 : int) (_45283 : int) : (term54 _45282 _45283) = (term55 _45282 _45283).
Proof. exact (MK_COMB (@lem3893163 _45282) (@lem3893161 _45282 _45283)). Qed.
Lemma lem3893165 (_45282 : int) (_45283 : int) : (term56 _45282 _45283) = (term54 _45282 _45283).
Proof. exact (@lem17362 (term52 _45282) (term57 _45282 _45283)). Qed.
Lemma lem3893193 (_45282 : int) (_45283 : int) : (term56 _45282 _45283) = (term55 _45282 _45283).
Proof. exact (TRANS (@lem3893165 _45282 _45283) (@lem3893164 _45282 _45283)). Qed.
Lemma lem3893196 (x : int) (y : int) : (int_le x y) = (term58 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3893197 (_45282 : int) : (term52 _45282) = (term59 _45282).
Proof. exact (@lem3893196 term12 _45282). Qed.
Lemma lem3893199 (n : nat) : (term60 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3893200 : term61 = term62.
Proof. exact (@lem3893199 (NUMERAL 0)). Qed.
Lemma lem3893201 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3893202 : term63 = term64.
Proof. exact (MK_COMB (@lem3893201) (@lem3893200)). Qed.
Lemma lem3893203 (_45282 : int) : (real_of_int _45282) = (real_of_int _45282).
Proof. exact (eq_refl (real_of_int _45282)). Qed.
Lemma lem3893204 (_45282 : int) : (term59 _45282) = (term65 _45282).
Proof. exact (MK_COMB (@lem3893202) (@lem3893203 _45282)). Qed.
Lemma lem3893206 (_45282 : int) : (term52 _45282) = (term65 _45282).
Proof. exact (TRANS (@lem3893197 _45282) (@lem3893204 _45282)). Qed.
Lemma lem3893209 (x : int) (y : int) : (int_le x y) = (term58 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3893210 (_45283 : int) : (term52 _45283) = (term59 _45283).
Proof. exact (@lem3893209 term12 _45283). Qed.
Lemma lem3893212 (n : nat) : (term60 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3893213 : term61 = term62.
Proof. exact (@lem3893212 (NUMERAL 0)). Qed.
Lemma lem3893214 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3893215 : term63 = term64.
Proof. exact (MK_COMB (@lem3893214) (@lem3893213)). Qed.
Lemma lem3893216 (_45283 : int) : (real_of_int _45283) = (real_of_int _45283).
Proof. exact (eq_refl (real_of_int _45283)). Qed.
Lemma lem3893217 (_45283 : int) : (term59 _45283) = (term65 _45283).
Proof. exact (MK_COMB (@lem3893215) (@lem3893216 _45283)). Qed.
Lemma lem3893219 (_45283 : int) : (term52 _45283) = (term65 _45283).
Proof. exact (TRANS (@lem3893210 _45283) (@lem3893217 _45283)). Qed.
Lemma lem3893221 (y : int) (x : int) : (term66 x y) = (term67 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem3893222 (_45283 : int) (_45282 : int) : (term39 _45282 _45283) = (term68 _45283 _45282).
Proof. exact (@lem3893221 (int_add _45282 _45283) _45282). Qed.
Lemma lem3893224 (x : int) (y : int) : (int_le x y) = (term58 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3893225 (_45282 : int) (_45283 : int) : (term69 _45282 _45283) = (term70 _45282 _45283).
Proof. exact (@lem3893224 (term71 _45282) (int_add _45282 _45283)). Qed.
Lemma lem3893227 (x : int) (y : int) : (term72 x y) = (term73 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3893228 (_45282 : int) : (term74 _45282) = (term75 _45282).
Proof. exact (@lem3893227 _45282 term76). Qed.
Lemma lem3893230 (n : nat) : (term60 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3893231 : term77 = term78.
Proof. exact (@lem3893230 term79). Qed.
Lemma lem3893232 (_45282 : int) : (term80 _45282) = (term80 _45282).
Proof. exact (eq_refl (term80 _45282)). Qed.
Lemma lem3893233 (_45282 : int) : (term75 _45282) = (term81 _45282).
Proof. exact (MK_COMB (@lem3893232 _45282) (@lem3893231)). Qed.
Lemma lem3893234 (_45282 : int) : (term74 _45282) = (term81 _45282).
Proof. exact (TRANS (@lem3893228 _45282) (@lem3893233 _45282)). Qed.
Lemma lem3893235 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3893236 (_45282 : int) : (term82 _45282) = (term83 _45282).
Proof. exact (MK_COMB (@lem3893235) (@lem3893234 _45282)). Qed.
Lemma lem3893238 (x : int) (y : int) : (term72 x y) = (term73 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3893239 (_45282 : int) (_45283 : int) : (term72 _45282 _45283) = (term73 _45282 _45283).
Proof. exact (@lem3893238 _45282 _45283). Qed.
Lemma lem3893240 (_45282 : int) (_45283 : int) : (term70 _45282 _45283) = (term84 _45282 _45283).
Proof. exact (MK_COMB (@lem3893236 _45282) (@lem3893239 _45282 _45283)). Qed.
Lemma lem3893241 (_45282 : int) (_45283 : int) : (term69 _45282 _45283) = (term84 _45282 _45283).
Proof. exact (TRANS (@lem3893225 _45282 _45283) (@lem3893240 _45282 _45283)). Qed.
Lemma lem3893242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3893243 (_45282 : int) (_45283 : int) : (term85 _45282 _45283) = (term86 _45282 _45283).
Proof. exact (MK_COMB (@lem3893242) (@lem3893241 _45282 _45283)). Qed.
Lemma lem3893245 (x : int) (y : int) : (int_le x y) = (term58 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3893246 (_45283 : int) (_45282 : int) : (term87 _45283 _45282) = (term88 _45283 _45282).
Proof. exact (@lem3893245 (term89 _45282 _45283) _45282). Qed.
Lemma lem3893248 (x : int) (y : int) : (term72 x y) = (term73 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3893249 (_45282 : int) (_45283 : int) : (term90 _45282 _45283) = (term91 _45282 _45283).
Proof. exact (@lem3893248 (int_add _45282 _45283) term76). Qed.
Lemma lem3893251 (x : int) (y : int) : (term72 x y) = (term73 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3893252 (_45282 : int) (_45283 : int) : (term72 _45282 _45283) = (term73 _45282 _45283).
Proof. exact (@lem3893251 _45282 _45283). Qed.
Lemma lem3893253 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3893254 (_45282 : int) (_45283 : int) : (term92 _45282 _45283) = (term93 _45282 _45283).
Proof. exact (MK_COMB (@lem3893253) (@lem3893252 _45282 _45283)). Qed.
Lemma lem3893256 (n : nat) : (term60 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3893257 : term77 = term78.
Proof. exact (@lem3893256 term79). Qed.
Lemma lem3893258 (_45282 : int) (_45283 : int) : (term91 _45282 _45283) = (term94 _45282 _45283).
Proof. exact (MK_COMB (@lem3893254 _45282 _45283) (@lem3893257)). Qed.
Lemma lem3893259 (_45282 : int) (_45283 : int) : (term90 _45282 _45283) = (term94 _45282 _45283).
Proof. exact (TRANS (@lem3893249 _45282 _45283) (@lem3893258 _45282 _45283)). Qed.
Lemma lem3893260 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3893261 (_45282 : int) (_45283 : int) : (term95 _45282 _45283) = (term96 _45282 _45283).
Proof. exact (MK_COMB (@lem3893260) (@lem3893259 _45282 _45283)). Qed.
Lemma lem3893262 (_45282 : int) : (real_of_int _45282) = (real_of_int _45282).
Proof. exact (eq_refl (real_of_int _45282)). Qed.
Lemma lem3893263 (_45283 : int) (_45282 : int) : (term88 _45283 _45282) = (term97 _45283 _45282).
Proof. exact (MK_COMB (@lem3893261 _45282 _45283) (@lem3893262 _45282)). Qed.
Lemma lem3893264 (_45283 : int) (_45282 : int) : (term87 _45283 _45282) = (term97 _45283 _45282).
Proof. exact (TRANS (@lem3893246 _45283 _45282) (@lem3893263 _45283 _45282)). Qed.
Lemma lem3893265 (_45283 : int) (_45282 : int) : (term68 _45283 _45282) = (term98 _45283 _45282).
Proof. exact (MK_COMB (@lem3893243 _45282 _45283) (@lem3893264 _45283 _45282)). Qed.
Lemma lem3893266 (_45283 : int) (_45282 : int) : (term39 _45282 _45283) = (term98 _45283 _45282).
Proof. exact (TRANS (@lem3893222 _45283 _45282) (@lem3893265 _45283 _45282)). Qed.
Lemma lem3893268 (y : int) (x : int) : (term66 x y) = (term67 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem3893269 (_45283 : int) : (term40 _45283) = (term99 _45283).
Proof. exact (@lem3893268 term12 _45283). Qed.
Lemma lem3893271 (x : int) (y : int) : (int_le x y) = (term58 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3893272 (_45283 : int) : (term100 _45283) = (term101 _45283).
Proof. exact (@lem3893271 (term71 _45283) term12). Qed.
Lemma lem3893274 (x : int) (y : int) : (term72 x y) = (term73 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3893275 (_45283 : int) : (term74 _45283) = (term75 _45283).
Proof. exact (@lem3893274 _45283 term76). Qed.
Lemma lem3893277 (n : nat) : (term60 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3893278 : term77 = term78.
Proof. exact (@lem3893277 term79). Qed.
Lemma lem3893279 (_45283 : int) : (term80 _45283) = (term80 _45283).
Proof. exact (eq_refl (term80 _45283)). Qed.
Lemma lem3893280 (_45283 : int) : (term75 _45283) = (term81 _45283).
Proof. exact (MK_COMB (@lem3893279 _45283) (@lem3893278)). Qed.
Lemma lem3893281 (_45283 : int) : (term74 _45283) = (term81 _45283).
Proof. exact (TRANS (@lem3893275 _45283) (@lem3893280 _45283)). Qed.
Lemma lem3893282 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3893283 (_45283 : int) : (term82 _45283) = (term83 _45283).
Proof. exact (MK_COMB (@lem3893282) (@lem3893281 _45283)). Qed.
Lemma lem3893285 (n : nat) : (term60 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3893286 : term61 = term62.
Proof. exact (@lem3893285 (NUMERAL 0)). Qed.
Lemma lem3893287 (_45283 : int) : (term101 _45283) = (term102 _45283).
Proof. exact (MK_COMB (@lem3893283 _45283) (@lem3893286)). Qed.
Lemma lem3893288 (_45283 : int) : (term100 _45283) = (term102 _45283).
Proof. exact (TRANS (@lem3893272 _45283) (@lem3893287 _45283)). Qed.
Lemma lem3893289 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3893290 (_45283 : int) : (term103 _45283) = (term104 _45283).
Proof. exact (MK_COMB (@lem3893289) (@lem3893288 _45283)). Qed.
Lemma lem3893292 (x : int) (y : int) : (int_le x y) = (term58 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3893293 (_45283 : int) : (term105 _45283) = (term106 _45283).
Proof. exact (@lem3893292 term107 _45283). Qed.
Lemma lem3893295 (x : int) (y : int) : (term72 x y) = (term73 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3893296 : term108 = term109.
Proof. exact (@lem3893295 term12 term76). Qed.
Lemma lem3893298 (n : nat) : (term60 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3893299 : term61 = term62.
Proof. exact (@lem3893298 (NUMERAL 0)). Qed.
Lemma lem3893300 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3893301 : term110 = term111.
Proof. exact (MK_COMB (@lem3893300) (@lem3893299)). Qed.
Lemma lem3893303 (n : nat) : (term60 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3893304 : term77 = term78.
Proof. exact (@lem3893303 term79). Qed.
Lemma lem3893305 : term109 = term112.
Proof. exact (MK_COMB (@lem3893301) (@lem3893304)). Qed.
Lemma lem3893306 : term108 = term112.
Proof. exact (TRANS (@lem3893296) (@lem3893305)). Qed.
Lemma lem3893307 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3893308 : term113 = term114.
Proof. exact (MK_COMB (@lem3893307) (@lem3893306)). Qed.
Lemma lem3893309 (_45283 : int) : (real_of_int _45283) = (real_of_int _45283).
Proof. exact (eq_refl (real_of_int _45283)). Qed.
Lemma lem3893310 (_45283 : int) : (term106 _45283) = (term115 _45283).
Proof. exact (MK_COMB (@lem3893308) (@lem3893309 _45283)). Qed.
Lemma lem3893311 (_45283 : int) : (term105 _45283) = (term115 _45283).
Proof. exact (TRANS (@lem3893293 _45283) (@lem3893310 _45283)). Qed.
Lemma lem3893312 (_45283 : int) : (term99 _45283) = (term116 _45283).
Proof. exact (MK_COMB (@lem3893290 _45283) (@lem3893311 _45283)). Qed.
Lemma lem3893313 (_45283 : int) : (term40 _45283) = (term116 _45283).
Proof. exact (TRANS (@lem3893269 _45283) (@lem3893312 _45283)). Qed.
Lemma lem3893314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3893315 (_45283 : int) (_45282 : int) : (term117 _45282 _45283) = (term118 _45283 _45282).
Proof. exact (MK_COMB (@lem3893314) (@lem3893266 _45283 _45282)). Qed.
Lemma lem3893316 (_45282 : int) (_45283 : int) : (term31 _45282 _45283) = (term119 _45282 _45283).
Proof. exact (MK_COMB (@lem3893315 _45283 _45282) (@lem3893313 _45283)). Qed.
Lemma lem3893319 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3893320 (_45282 : int) (_45283 : int) : (_45282 = (int_add _45282 _45283)) = ((real_of_int _45282) = (term72 _45282 _45283)).
Proof. exact (@lem3893319 _45282 (int_add _45282 _45283)). Qed.
Lemma lem3893324 (x : int) (y : int) : (term72 x y) = (term73 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3893325 (_45282 : int) (_45283 : int) : (term72 _45282 _45283) = (term73 _45282 _45283).
Proof. exact (@lem3893324 _45282 _45283). Qed.
Lemma lem3893326 (_45282 : int) : (term120 _45282) = (term120 _45282).
Proof. exact (eq_refl (term120 _45282)). Qed.
Lemma lem3893327 (_45282 : int) (_45283 : int) : ((real_of_int _45282) = (term72 _45282 _45283)) = ((real_of_int _45282) = (term73 _45282 _45283)).
Proof. exact (MK_COMB (@lem3893326 _45282) (@lem3893325 _45282 _45283)). Qed.
Lemma lem3893329 (_45282 : int) (_45283 : int) : (_45282 = (int_add _45282 _45283)) = ((real_of_int _45282) = (term73 _45282 _45283)).
Proof. exact (TRANS (@lem3893320 _45282 _45283) (@lem3893327 _45282 _45283)). Qed.
Lemma lem3893332 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3893333 (_45283 : int) : (_45283 = term12) = ((real_of_int _45283) = term61).
Proof. exact (@lem3893332 _45283 term12). Qed.
Lemma lem3893337 (n : nat) : (term60 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3893338 : term61 = term62.
Proof. exact (@lem3893337 (NUMERAL 0)). Qed.
Lemma lem3893339 (_45283 : int) : (term120 _45283) = (term120 _45283).
Proof. exact (eq_refl (term120 _45283)). Qed.
Lemma lem3893340 (_45283 : int) : ((real_of_int _45283) = term61) = ((real_of_int _45283) = term62).
Proof. exact (MK_COMB (@lem3893339 _45283) (@lem3893338)). Qed.
Lemma lem3893342 (_45283 : int) : (_45283 = term12) = ((real_of_int _45283) = term62).
Proof. exact (TRANS (@lem3893333 _45283) (@lem3893340 _45283)). Qed.
Lemma lem3893343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3893344 (_45282 : int) (_45283 : int) : (term35 _45282 _45283) = (term121 _45282 _45283).
Proof. exact (MK_COMB (@lem3893343) (@lem3893329 _45282 _45283)). Qed.
Lemma lem3893345 (_45282 : int) (_45283 : int) : (term37 _45282 _45283) = (term122 _45282 _45283).
Proof. exact (MK_COMB (@lem3893344 _45282 _45283) (@lem3893342 _45283)). Qed.
Lemma lem3893346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3893347 (_45282 : int) (_45283 : int) : (term42 _45282 _45283) = (term123 _45282 _45283).
Proof. exact (MK_COMB (@lem3893346) (@lem3893316 _45282 _45283)). Qed.
Lemma lem3893348 (_45282 : int) (_45283 : int) : (term44 _45282 _45283) = (term124 _45282 _45283).
Proof. exact (MK_COMB (@lem3893347 _45282 _45283) (@lem3893345 _45282 _45283)). Qed.
Lemma lem3893349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3893350 (_45283 : int) : (term48 _45283) = (term125 _45283).
Proof. exact (MK_COMB (@lem3893349) (@lem3893219 _45283)). Qed.
Lemma lem3893351 (_45282 : int) (_45283 : int) : (term50 _45282 _45283) = (term126 _45282 _45283).
Proof. exact (MK_COMB (@lem3893350 _45283) (@lem3893348 _45282 _45283)). Qed.
Lemma lem3893352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3893353 (_45282 : int) : (term48 _45282) = (term125 _45282).
Proof. exact (MK_COMB (@lem3893352) (@lem3893206 _45282)). Qed.
Lemma lem3893354 (_45282 : int) (_45283 : int) : (term55 _45282 _45283) = (term127 _45282 _45283).
Proof. exact (MK_COMB (@lem3893353 _45282) (@lem3893351 _45282 _45283)). Qed.
Lemma lem3893355 (_45282 : int) (_45283 : int) : (term56 _45282 _45283) = (term127 _45282 _45283).
Proof. exact (TRANS (@lem3893193 _45282 _45283) (@lem3893354 _45282 _45283)). Qed.
Lemma lem3893359 (t : Prop) : (term128 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3893435 (_45282 : int) (_45283 : int) : (term129 _45282 _45283) = (term127 _45282 _45283).
Proof. exact (@lem3893359 (term127 _45282 _45283)). Qed.
Lemma lem3893436 (_45282 : int) : (term65 _45282) = (term130 _45282).
Proof. exact (@lem1988287 (real_of_int _45282) term62). Qed.
Lemma lem3893442 (_45282 : int) : (term131 _45282) = (term132 _45282).
Proof. exact (@lem1982792 (real_of_int _45282) term62). Qed.
Lemma lem3893444 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3893445 : term62 = term134.
Proof. exact (@lem3893444 (NUMERAL 0)). Qed.
Lemma lem3893447 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3893448 : term137 = term138.
Proof. exact (@lem3893447 term79). Qed.
Lemma lem3893449 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3893450 : term139 = term140.
Proof. exact (MK_COMB (@lem3893449) (@lem3893448)). Qed.
Lemma lem3893451 : term141 = term142.
Proof. exact (MK_COMB (@lem3893450) (@lem3893445)). Qed.
Lemma lem3893452 : term142 = term143.
Proof. exact (@lem1981613 term137 term62 term78 term78). Qed.
Lemma lem3893454 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3893455 : term146 = term147.
Proof. exact (@lem3893454 term79 term79). Qed.
Lemma lem3893456 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893457 : term149 = term79.
Proof. exact (EQ_MP (@lem3893456) (@lem940073)). Qed.
Lemma lem3893458 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893459 : term147 = term78.
Proof. exact (MK_COMB (@lem3893458) (@lem3893457)). Qed.
Lemma lem3893460 : term146 = term78.
Proof. exact (TRANS (@lem3893455) (@lem3893459)). Qed.
Lemma lem3893462 (x : nat) : (term150 x) = term62.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3893463 : term141 = term62.
Proof. exact (@lem3893462 term79). Qed.
Lemma lem3893464 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3893465 : term151 = term152.
Proof. exact (MK_COMB (@lem3893464) (@lem3893463)). Qed.
Lemma lem3893466 : term143 = term134.
Proof. exact (MK_COMB (@lem3893465) (@lem3893460)). Qed.
Lemma lem3893467 : term142 = term134.
Proof. exact (TRANS (@lem3893452) (@lem3893466)). Qed.
Lemma lem3893468 : term141 = term134.
Proof. exact (TRANS (@lem3893451) (@lem3893467)). Qed.
Lemma lem3893470 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3893471 : term134 = term62.
Proof. exact (@lem3893470 term62). Qed.
Lemma lem3893472 : term141 = term62.
Proof. exact (TRANS (@lem3893468) (@lem3893471)). Qed.
Lemma lem3893473 (_45282 : int) : (term80 _45282) = (term80 _45282).
Proof. exact (eq_refl (term80 _45282)). Qed.
Lemma lem3893474 (_45282 : int) : (term132 _45282) = (term154 _45282).
Proof. exact (MK_COMB (@lem3893473 _45282) (@lem3893472)). Qed.
Lemma lem3893475 (_45282 : int) : (term154 _45282) = (real_of_int _45282).
Proof. exact (@lem1982723 (real_of_int _45282)). Qed.
Lemma lem3893476 (_45282 : int) : (term132 _45282) = (real_of_int _45282).
Proof. exact (TRANS (@lem3893474 _45282) (@lem3893475 _45282)). Qed.
Lemma lem3893478 (_45282 : int) : (term131 _45282) = (real_of_int _45282).
Proof. exact (TRANS (@lem3893442 _45282) (@lem3893476 _45282)). Qed.
Lemma lem3893479 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3893480 (_45282 : int) : (term155 _45282) = (term156 _45282).
Proof. exact (MK_COMB (@lem3893479) (@lem3893478 _45282)). Qed.
Lemma lem3893481 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3893482 (_45282 : int) : (term130 _45282) = (term157 _45282).
Proof. exact (MK_COMB (@lem3893480 _45282) (@lem3893481)). Qed.
Lemma lem3893483 (_45282 : int) : (term65 _45282) = (term157 _45282).
Proof. exact (TRANS (@lem3893436 _45282) (@lem3893482 _45282)). Qed.
Lemma lem3893484 (_45283 : int) : (term65 _45283) = (term130 _45283).
Proof. exact (@lem1988287 (real_of_int _45283) term62). Qed.
Lemma lem3893490 (_45283 : int) : (term131 _45283) = (term132 _45283).
Proof. exact (@lem1982792 (real_of_int _45283) term62). Qed.
Lemma lem3893492 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3893493 : term62 = term134.
Proof. exact (@lem3893492 (NUMERAL 0)). Qed.
Lemma lem3893495 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3893496 : term137 = term138.
Proof. exact (@lem3893495 term79). Qed.
Lemma lem3893497 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3893498 : term139 = term140.
Proof. exact (MK_COMB (@lem3893497) (@lem3893496)). Qed.
Lemma lem3893499 : term141 = term142.
Proof. exact (MK_COMB (@lem3893498) (@lem3893493)). Qed.
Lemma lem3893500 : term142 = term143.
Proof. exact (@lem1981613 term137 term62 term78 term78). Qed.
Lemma lem3893502 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3893503 : term146 = term147.
Proof. exact (@lem3893502 term79 term79). Qed.
Lemma lem3893504 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893505 : term149 = term79.
Proof. exact (EQ_MP (@lem3893504) (@lem940073)). Qed.
Lemma lem3893506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893507 : term147 = term78.
Proof. exact (MK_COMB (@lem3893506) (@lem3893505)). Qed.
Lemma lem3893508 : term146 = term78.
Proof. exact (TRANS (@lem3893503) (@lem3893507)). Qed.
Lemma lem3893510 (x : nat) : (term150 x) = term62.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3893511 : term141 = term62.
Proof. exact (@lem3893510 term79). Qed.
Lemma lem3893512 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3893513 : term151 = term152.
Proof. exact (MK_COMB (@lem3893512) (@lem3893511)). Qed.
Lemma lem3893514 : term143 = term134.
Proof. exact (MK_COMB (@lem3893513) (@lem3893508)). Qed.
Lemma lem3893515 : term142 = term134.
Proof. exact (TRANS (@lem3893500) (@lem3893514)). Qed.
Lemma lem3893516 : term141 = term134.
Proof. exact (TRANS (@lem3893499) (@lem3893515)). Qed.
Lemma lem3893518 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3893519 : term134 = term62.
Proof. exact (@lem3893518 term62). Qed.
Lemma lem3893520 : term141 = term62.
Proof. exact (TRANS (@lem3893516) (@lem3893519)). Qed.
Lemma lem3893521 (_45283 : int) : (term80 _45283) = (term80 _45283).
Proof. exact (eq_refl (term80 _45283)). Qed.
Lemma lem3893522 (_45283 : int) : (term132 _45283) = (term154 _45283).
Proof. exact (MK_COMB (@lem3893521 _45283) (@lem3893520)). Qed.
Lemma lem3893523 (_45283 : int) : (term154 _45283) = (real_of_int _45283).
Proof. exact (@lem1982723 (real_of_int _45283)). Qed.
Lemma lem3893524 (_45283 : int) : (term132 _45283) = (real_of_int _45283).
Proof. exact (TRANS (@lem3893522 _45283) (@lem3893523 _45283)). Qed.
Lemma lem3893526 (_45283 : int) : (term131 _45283) = (real_of_int _45283).
Proof. exact (TRANS (@lem3893490 _45283) (@lem3893524 _45283)). Qed.
Lemma lem3893527 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3893528 (_45283 : int) : (term155 _45283) = (term156 _45283).
Proof. exact (MK_COMB (@lem3893527) (@lem3893526 _45283)). Qed.
Lemma lem3893529 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3893530 (_45283 : int) : (term130 _45283) = (term157 _45283).
Proof. exact (MK_COMB (@lem3893528 _45283) (@lem3893529)). Qed.
Lemma lem3893531 (_45283 : int) : (term65 _45283) = (term157 _45283).
Proof. exact (TRANS (@lem3893484 _45283) (@lem3893530 _45283)). Qed.
Lemma lem3893532 (_45283 : int) (_45282 : int) : (term84 _45282 _45283) = (term158 _45283 _45282).
Proof. exact (@lem1988287 (term73 _45282 _45283) (term81 _45282)). Qed.
Lemma lem3893550 (_45283 : int) (_45282 : int) : (term159 _45283 _45282) = (term160 _45283 _45282).
Proof. exact (@lem1982792 (term73 _45282 _45283) (term81 _45282)). Qed.
Lemma lem3893551 (_45282 : int) : (term161 _45282) = (term162 _45282).
Proof. exact (@lem1982781 (real_of_int _45282) term137 term78). Qed.
Lemma lem3893553 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3893554 : term78 = term163.
Proof. exact (@lem3893553 term79). Qed.
Lemma lem3893556 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3893557 : term137 = term138.
Proof. exact (@lem3893556 term79). Qed.
Lemma lem3893558 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3893559 : term139 = term140.
Proof. exact (MK_COMB (@lem3893558) (@lem3893557)). Qed.
Lemma lem3893560 : term164 = term165.
Proof. exact (MK_COMB (@lem3893559) (@lem3893554)). Qed.
Lemma lem3893561 : term165 = term166.
Proof. exact (@lem1981613 term137 term78 term78 term78). Qed.
Lemma lem3893563 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3893564 : term146 = term147.
Proof. exact (@lem3893563 term79 term79). Qed.
Lemma lem3893565 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893566 : term149 = term79.
Proof. exact (EQ_MP (@lem3893565) (@lem940073)). Qed.
Lemma lem3893567 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893568 : term147 = term78.
Proof. exact (MK_COMB (@lem3893567) (@lem3893566)). Qed.
Lemma lem3893569 : term146 = term78.
Proof. exact (TRANS (@lem3893564) (@lem3893568)). Qed.
Lemma lem3893571 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3893572 : term164 = term169.
Proof. exact (@lem3893571 term79 term79). Qed.
Lemma lem3893573 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893574 : term149 = term79.
Proof. exact (EQ_MP (@lem3893573) (@lem940073)). Qed.
Lemma lem3893575 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893576 : term147 = term78.
Proof. exact (MK_COMB (@lem3893575) (@lem3893574)). Qed.
Lemma lem3893577 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3893578 : term169 = term137.
Proof. exact (MK_COMB (@lem3893577) (@lem3893576)). Qed.
Lemma lem3893579 : term164 = term137.
Proof. exact (TRANS (@lem3893572) (@lem3893578)). Qed.
Lemma lem3893580 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3893581 : term170 = term171.
Proof. exact (MK_COMB (@lem3893580) (@lem3893579)). Qed.
Lemma lem3893582 : term166 = term138.
Proof. exact (MK_COMB (@lem3893581) (@lem3893569)). Qed.
Lemma lem3893583 : term165 = term138.
Proof. exact (TRANS (@lem3893561) (@lem3893582)). Qed.
Lemma lem3893584 : term164 = term138.
Proof. exact (TRANS (@lem3893560) (@lem3893583)). Qed.
Lemma lem3893586 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3893587 : term138 = term137.
Proof. exact (@lem3893586 term137). Qed.
Lemma lem3893588 : term164 = term137.
Proof. exact (TRANS (@lem3893584) (@lem3893587)). Qed.
Lemma lem3893591 (_45282 : int) : (term172 _45282) = (term172 _45282).
Proof. exact (eq_refl (term172 _45282)). Qed.
Lemma lem3893592 (_45282 : int) : (term162 _45282) = (term173 _45282).
Proof. exact (MK_COMB (@lem3893591 _45282) (@lem3893588)). Qed.
Lemma lem3893593 (_45282 : int) : (term161 _45282) = (term173 _45282).
Proof. exact (TRANS (@lem3893551 _45282) (@lem3893592 _45282)). Qed.
Lemma lem3893594 (_45282 : int) (_45283 : int) : (term93 _45282 _45283) = (term93 _45282 _45283).
Proof. exact (eq_refl (term93 _45282 _45283)). Qed.
Lemma lem3893595 (_45283 : int) (_45282 : int) : (term160 _45283 _45282) = (term174 _45283 _45282).
Proof. exact (MK_COMB (@lem3893594 _45282 _45283) (@lem3893593 _45282)). Qed.
Lemma lem3893596 (_45282 : int) (_45283 : int) : (term174 _45283 _45282) = (term175 _45282 _45283).
Proof. exact (@lem1982753 (real_of_int _45282) (term176 _45282) (real_of_int _45283) term137). Qed.
Lemma lem3893597 (_45282 : int) : (term177 _45282) = (term178 _45282).
Proof. exact (@lem1982715 term137 (real_of_int _45282)). Qed.
Lemma lem3893599 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3893600 : term78 = term163.
Proof. exact (@lem3893599 term79). Qed.
Lemma lem3893602 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3893603 : term137 = term138.
Proof. exact (@lem3893602 term79). Qed.
Lemma lem3893604 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3893605 : term179 = term180.
Proof. exact (MK_COMB (@lem3893604) (@lem3893603)). Qed.
Lemma lem3893606 : term181 = term182.
Proof. exact (MK_COMB (@lem3893605) (@lem3893600)). Qed.
Lemma lem3893607 : term183.
Proof. exact (@lem1981473 term137 term78 term78 term78 term62 term78). Qed.
Lemma lem3893609 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3893610 : term185 = term186.
Proof. exact (@lem3893609 (NUMERAL 0) term79). Qed.
Lemma lem3893611 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3893612 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3893613 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3893612 h1) (fun h1 : term186 = True => @lem3893611)). Qed.
Lemma lem3893614 : term186 = True.
Proof. exact (EQ_MP (@lem3893613) (@lem3893611)). Qed.
Lemma lem3893615 : term185 = True.
Proof. exact (TRANS (@lem3893610) (@lem3893614)). Qed.
Lemma lem3893616 : True = term185.
Proof. exact (SYM (@lem3893615)). Qed.
Lemma lem3893617 : term185.
Proof. exact (EQ_MP (@lem3893616) (@lem0)). Qed.
Lemma lem3893618 : term188.
Proof. exact (@lem3893607 (@lem3893617)). Qed.
Lemma lem3893620 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3893621 : term185 = term186.
Proof. exact (@lem3893620 (NUMERAL 0) term79). Qed.
Lemma lem3893622 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3893623 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3893624 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3893623 h1) (fun h1 : term186 = True => @lem3893622)). Qed.
Lemma lem3893625 : term186 = True.
Proof. exact (EQ_MP (@lem3893624) (@lem3893622)). Qed.
Lemma lem3893626 : term185 = True.
Proof. exact (TRANS (@lem3893621) (@lem3893625)). Qed.
Lemma lem3893627 : True = term185.
Proof. exact (SYM (@lem3893626)). Qed.
Lemma lem3893628 : term185.
Proof. exact (EQ_MP (@lem3893627) (@lem0)). Qed.
Lemma lem3893629 : term189.
Proof. exact (@lem3893618 (@lem3893628)). Qed.
Lemma lem3893631 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3893632 : term185 = term186.
Proof. exact (@lem3893631 (NUMERAL 0) term79). Qed.
Lemma lem3893633 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3893634 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3893635 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3893634 h1) (fun h1 : term186 = True => @lem3893633)). Qed.
Lemma lem3893636 : term186 = True.
Proof. exact (EQ_MP (@lem3893635) (@lem3893633)). Qed.
Lemma lem3893637 : term185 = True.
Proof. exact (TRANS (@lem3893632) (@lem3893636)). Qed.
Lemma lem3893638 : True = term185.
Proof. exact (SYM (@lem3893637)). Qed.
Lemma lem3893639 : term185.
Proof. exact (EQ_MP (@lem3893638) (@lem0)). Qed.
Lemma lem3893640 : term190.
Proof. exact (@lem3893629 (@lem3893639)). Qed.
Lemma lem3893642 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3893643 : term146 = term147.
Proof. exact (@lem3893642 term79 term79). Qed.
Lemma lem3893644 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893645 : term149 = term79.
Proof. exact (EQ_MP (@lem3893644) (@lem940073)). Qed.
Lemma lem3893646 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893647 : term147 = term78.
Proof. exact (MK_COMB (@lem3893646) (@lem3893645)). Qed.
Lemma lem3893648 : term146 = term78.
Proof. exact (TRANS (@lem3893643) (@lem3893647)). Qed.
Lemma lem3893650 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3893651 : term164 = term169.
Proof. exact (@lem3893650 term79 term79). Qed.
Lemma lem3893652 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893653 : term149 = term79.
Proof. exact (EQ_MP (@lem3893652) (@lem940073)). Qed.
Lemma lem3893654 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893655 : term147 = term78.
Proof. exact (MK_COMB (@lem3893654) (@lem3893653)). Qed.
Lemma lem3893656 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3893657 : term169 = term137.
Proof. exact (MK_COMB (@lem3893656) (@lem3893655)). Qed.
Lemma lem3893658 : term164 = term137.
Proof. exact (TRANS (@lem3893651) (@lem3893657)). Qed.
Lemma lem3893659 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3893660 : term191 = term179.
Proof. exact (MK_COMB (@lem3893659) (@lem3893658)). Qed.
Lemma lem3893661 : term192 = term181.
Proof. exact (MK_COMB (@lem3893660) (@lem3893648)). Qed.
Lemma lem3893663 (m : nat) : (term193 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3893664 : term181 = term62.
Proof. exact (@lem3893663 term79). Qed.
Lemma lem3893665 : term192 = term62.
Proof. exact (TRANS (@lem3893661) (@lem3893664)). Qed.
Lemma lem3893666 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3893667 : term194 = term195.
Proof. exact (MK_COMB (@lem3893666) (@lem3893665)). Qed.
Lemma lem3893668 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem3893669 : term196 = term197.
Proof. exact (MK_COMB (@lem3893667) (@lem3893668)). Qed.
Lemma lem3893671 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3893672 : term197 = term62.
Proof. exact (@lem3893671 term79). Qed.
Lemma lem3893673 : term196 = term62.
Proof. exact (TRANS (@lem3893669) (@lem3893672)). Qed.
Lemma lem3893675 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3893676 : term146 = term147.
Proof. exact (@lem3893675 term79 term79). Qed.
Lemma lem3893677 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893678 : term149 = term79.
Proof. exact (EQ_MP (@lem3893677) (@lem940073)). Qed.
Lemma lem3893679 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893680 : term147 = term78.
Proof. exact (MK_COMB (@lem3893679) (@lem3893678)). Qed.
Lemma lem3893681 : term146 = term78.
Proof. exact (TRANS (@lem3893676) (@lem3893680)). Qed.
Lemma lem3893682 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem3893683 : term199 = term197.
Proof. exact (MK_COMB (@lem3893682) (@lem3893681)). Qed.
Lemma lem3893685 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3893686 : term197 = term62.
Proof. exact (@lem3893685 term79). Qed.
Lemma lem3893687 : term199 = term62.
Proof. exact (TRANS (@lem3893683) (@lem3893686)). Qed.
Lemma lem3893688 : term62 = term199.
Proof. exact (SYM (@lem3893687)). Qed.
Lemma lem3893689 : term196 = term199.
Proof. exact (TRANS (@lem3893673) (@lem3893688)). Qed.
Lemma lem3893690 : term182 = term134.
Proof. exact (@lem3893640 (@lem3893689)). Qed.
Lemma lem3893691 : term181 = term134.
Proof. exact (TRANS (@lem3893606) (@lem3893690)). Qed.
Lemma lem3893693 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3893694 : term134 = term62.
Proof. exact (@lem3893693 term62). Qed.
Lemma lem3893695 : term181 = term62.
Proof. exact (TRANS (@lem3893691) (@lem3893694)). Qed.
Lemma lem3893696 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3893697 : term200 = term195.
Proof. exact (MK_COMB (@lem3893696) (@lem3893695)). Qed.
Lemma lem3893698 (_45282 : int) : (real_of_int _45282) = (real_of_int _45282).
Proof. exact (eq_refl (real_of_int _45282)). Qed.
Lemma lem3893699 (_45282 : int) : (term178 _45282) = (term201 _45282).
Proof. exact (MK_COMB (@lem3893697) (@lem3893698 _45282)). Qed.
Lemma lem3893700 (_45282 : int) : (term177 _45282) = (term201 _45282).
Proof. exact (TRANS (@lem3893597 _45282) (@lem3893699 _45282)). Qed.
Lemma lem3893701 (_45282 : int) : (term201 _45282) = term62.
Proof. exact (@lem1982719 (real_of_int _45282)). Qed.
Lemma lem3893702 (_45282 : int) : (term177 _45282) = term62.
Proof. exact (TRANS (@lem3893700 _45282) (@lem3893701 _45282)). Qed.
Lemma lem3893703 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3893704 (_45282 : int) : (term202 _45282) = term111.
Proof. exact (MK_COMB (@lem3893703) (@lem3893702 _45282)). Qed.
Lemma lem3893705 (_45283 : int) : (term203 _45283) = (term203 _45283).
Proof. exact (eq_refl (term203 _45283)). Qed.
Lemma lem3893706 (_45282 : int) (_45283 : int) : (term175 _45282 _45283) = (term204 _45283).
Proof. exact (MK_COMB (@lem3893704 _45282) (@lem3893705 _45283)). Qed.
Lemma lem3893707 (_45282 : int) (_45283 : int) : (term174 _45283 _45282) = (term204 _45283).
Proof. exact (TRANS (@lem3893596 _45282 _45283) (@lem3893706 _45282 _45283)). Qed.
Lemma lem3893708 (_45283 : int) : (term204 _45283) = (term203 _45283).
Proof. exact (@lem1982721 (term203 _45283)). Qed.
Lemma lem3893709 (_45282 : int) (_45283 : int) : (term174 _45283 _45282) = (term203 _45283).
Proof. exact (TRANS (@lem3893707 _45282 _45283) (@lem3893708 _45283)). Qed.
Lemma lem3893710 (_45282 : int) (_45283 : int) : (term160 _45283 _45282) = (term203 _45283).
Proof. exact (TRANS (@lem3893595 _45283 _45282) (@lem3893709 _45282 _45283)). Qed.
Lemma lem3893712 (_45282 : int) (_45283 : int) : (term159 _45283 _45282) = (term203 _45283).
Proof. exact (TRANS (@lem3893550 _45283 _45282) (@lem3893710 _45282 _45283)). Qed.
Lemma lem3893713 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3893714 (_45282 : int) (_45283 : int) : (term205 _45283 _45282) = (term206 _45283).
Proof. exact (MK_COMB (@lem3893713) (@lem3893712 _45282 _45283)). Qed.
Lemma lem3893715 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3893716 (_45282 : int) (_45283 : int) : (term158 _45283 _45282) = (term207 _45283).
Proof. exact (MK_COMB (@lem3893714 _45282 _45283) (@lem3893715)). Qed.
Lemma lem3893717 (_45282 : int) (_45283 : int) : (term84 _45282 _45283) = (term207 _45283).
Proof. exact (TRANS (@lem3893532 _45283 _45282) (@lem3893716 _45282 _45283)). Qed.
Lemma lem3893718 (_45282 : int) (_45283 : int) : (term97 _45283 _45282) = (term208 _45282 _45283).
Proof. exact (@lem1988287 (real_of_int _45282) (term94 _45282 _45283)). Qed.
Lemma lem3893735 (_45282 : int) (_45283 : int) : (term94 _45282 _45283) = (term209 _45282 _45283).
Proof. exact (@lem1982755 (real_of_int _45282) (real_of_int _45283) term78). Qed.
Lemma lem3893738 (_45282 : int) : (term210 _45282) = (term210 _45282).
Proof. exact (eq_refl (term210 _45282)). Qed.
Lemma lem3893739 (_45282 : int) (_45283 : int) : (term211 _45282 _45283) = (term212 _45282 _45283).
Proof. exact (MK_COMB (@lem3893738 _45282) (@lem3893735 _45282 _45283)). Qed.
Lemma lem3893740 (_45282 : int) (_45283 : int) : (term212 _45282 _45283) = (term213 _45282 _45283).
Proof. exact (@lem1982792 (real_of_int _45282) (term209 _45282 _45283)). Qed.
Lemma lem3893741 (_45282 : int) (_45283 : int) : (term214 _45282 _45283) = (term215 _45282 _45283).
Proof. exact (@lem1982781 (real_of_int _45282) term137 (term81 _45283)). Qed.
Lemma lem3893742 (_45283 : int) : (term161 _45283) = (term162 _45283).
Proof. exact (@lem1982781 (real_of_int _45283) term137 term78). Qed.
Lemma lem3893744 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3893745 : term78 = term163.
Proof. exact (@lem3893744 term79). Qed.
Lemma lem3893747 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3893748 : term137 = term138.
Proof. exact (@lem3893747 term79). Qed.
Lemma lem3893749 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3893750 : term139 = term140.
Proof. exact (MK_COMB (@lem3893749) (@lem3893748)). Qed.
Lemma lem3893751 : term164 = term165.
Proof. exact (MK_COMB (@lem3893750) (@lem3893745)). Qed.
Lemma lem3893752 : term165 = term166.
Proof. exact (@lem1981613 term137 term78 term78 term78). Qed.
Lemma lem3893754 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3893755 : term146 = term147.
Proof. exact (@lem3893754 term79 term79). Qed.
Lemma lem3893756 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893757 : term149 = term79.
Proof. exact (EQ_MP (@lem3893756) (@lem940073)). Qed.
Lemma lem3893758 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893759 : term147 = term78.
Proof. exact (MK_COMB (@lem3893758) (@lem3893757)). Qed.
Lemma lem3893760 : term146 = term78.
Proof. exact (TRANS (@lem3893755) (@lem3893759)). Qed.
Lemma lem3893762 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3893763 : term164 = term169.
Proof. exact (@lem3893762 term79 term79). Qed.
Lemma lem3893764 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893765 : term149 = term79.
Proof. exact (EQ_MP (@lem3893764) (@lem940073)). Qed.
Lemma lem3893766 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893767 : term147 = term78.
Proof. exact (MK_COMB (@lem3893766) (@lem3893765)). Qed.
Lemma lem3893768 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3893769 : term169 = term137.
Proof. exact (MK_COMB (@lem3893768) (@lem3893767)). Qed.
Lemma lem3893770 : term164 = term137.
Proof. exact (TRANS (@lem3893763) (@lem3893769)). Qed.
Lemma lem3893771 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3893772 : term170 = term171.
Proof. exact (MK_COMB (@lem3893771) (@lem3893770)). Qed.
Lemma lem3893773 : term166 = term138.
Proof. exact (MK_COMB (@lem3893772) (@lem3893760)). Qed.
Lemma lem3893774 : term165 = term138.
Proof. exact (TRANS (@lem3893752) (@lem3893773)). Qed.
Lemma lem3893775 : term164 = term138.
Proof. exact (TRANS (@lem3893751) (@lem3893774)). Qed.
Lemma lem3893777 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3893778 : term138 = term137.
Proof. exact (@lem3893777 term137). Qed.
Lemma lem3893779 : term164 = term137.
Proof. exact (TRANS (@lem3893775) (@lem3893778)). Qed.
Lemma lem3893782 (_45283 : int) : (term172 _45283) = (term172 _45283).
Proof. exact (eq_refl (term172 _45283)). Qed.
Lemma lem3893783 (_45283 : int) : (term162 _45283) = (term173 _45283).
Proof. exact (MK_COMB (@lem3893782 _45283) (@lem3893779)). Qed.
Lemma lem3893784 (_45283 : int) : (term161 _45283) = (term173 _45283).
Proof. exact (TRANS (@lem3893742 _45283) (@lem3893783 _45283)). Qed.
Lemma lem3893787 (_45282 : int) : (term172 _45282) = (term172 _45282).
Proof. exact (eq_refl (term172 _45282)). Qed.
Lemma lem3893788 (_45282 : int) (_45283 : int) : (term215 _45282 _45283) = (term216 _45282 _45283).
Proof. exact (MK_COMB (@lem3893787 _45282) (@lem3893784 _45283)). Qed.
Lemma lem3893789 (_45282 : int) (_45283 : int) : (term214 _45282 _45283) = (term216 _45282 _45283).
Proof. exact (TRANS (@lem3893741 _45282 _45283) (@lem3893788 _45282 _45283)). Qed.
Lemma lem3893790 (_45282 : int) : (term80 _45282) = (term80 _45282).
Proof. exact (eq_refl (term80 _45282)). Qed.
Lemma lem3893791 (_45282 : int) (_45283 : int) : (term213 _45282 _45283) = (term217 _45282 _45283).
Proof. exact (MK_COMB (@lem3893790 _45282) (@lem3893789 _45282 _45283)). Qed.
Lemma lem3893792 (_45282 : int) (_45283 : int) : (term217 _45282 _45283) = (term218 _45282 _45283).
Proof. exact (@lem1982763 (real_of_int _45282) (term176 _45282) (term173 _45283)). Qed.
Lemma lem3893793 (_45282 : int) : (term177 _45282) = (term178 _45282).
Proof. exact (@lem1982715 term137 (real_of_int _45282)). Qed.
Lemma lem3893795 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3893796 : term78 = term163.
Proof. exact (@lem3893795 term79). Qed.
Lemma lem3893798 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3893799 : term137 = term138.
Proof. exact (@lem3893798 term79). Qed.
Lemma lem3893800 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3893801 : term179 = term180.
Proof. exact (MK_COMB (@lem3893800) (@lem3893799)). Qed.
Lemma lem3893802 : term181 = term182.
Proof. exact (MK_COMB (@lem3893801) (@lem3893796)). Qed.
Lemma lem3893803 : term183.
Proof. exact (@lem1981473 term137 term78 term78 term78 term62 term78). Qed.
Lemma lem3893805 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3893806 : term185 = term186.
Proof. exact (@lem3893805 (NUMERAL 0) term79). Qed.
Lemma lem3893807 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3893808 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3893809 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3893808 h1) (fun h1 : term186 = True => @lem3893807)). Qed.
Lemma lem3893810 : term186 = True.
Proof. exact (EQ_MP (@lem3893809) (@lem3893807)). Qed.
Lemma lem3893811 : term185 = True.
Proof. exact (TRANS (@lem3893806) (@lem3893810)). Qed.
Lemma lem3893812 : True = term185.
Proof. exact (SYM (@lem3893811)). Qed.
Lemma lem3893813 : term185.
Proof. exact (EQ_MP (@lem3893812) (@lem0)). Qed.
Lemma lem3893814 : term188.
Proof. exact (@lem3893803 (@lem3893813)). Qed.
Lemma lem3893816 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3893817 : term185 = term186.
Proof. exact (@lem3893816 (NUMERAL 0) term79). Qed.
Lemma lem3893818 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3893819 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3893820 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3893819 h1) (fun h1 : term186 = True => @lem3893818)). Qed.
Lemma lem3893821 : term186 = True.
Proof. exact (EQ_MP (@lem3893820) (@lem3893818)). Qed.
Lemma lem3893822 : term185 = True.
Proof. exact (TRANS (@lem3893817) (@lem3893821)). Qed.
Lemma lem3893823 : True = term185.
Proof. exact (SYM (@lem3893822)). Qed.
Lemma lem3893824 : term185.
Proof. exact (EQ_MP (@lem3893823) (@lem0)). Qed.
Lemma lem3893825 : term189.
Proof. exact (@lem3893814 (@lem3893824)). Qed.
Lemma lem3893827 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3893828 : term185 = term186.
Proof. exact (@lem3893827 (NUMERAL 0) term79). Qed.
Lemma lem3893829 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3893830 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3893831 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3893830 h1) (fun h1 : term186 = True => @lem3893829)). Qed.
Lemma lem3893832 : term186 = True.
Proof. exact (EQ_MP (@lem3893831) (@lem3893829)). Qed.
Lemma lem3893833 : term185 = True.
Proof. exact (TRANS (@lem3893828) (@lem3893832)). Qed.
Lemma lem3893834 : True = term185.
Proof. exact (SYM (@lem3893833)). Qed.
Lemma lem3893835 : term185.
Proof. exact (EQ_MP (@lem3893834) (@lem0)). Qed.
Lemma lem3893836 : term190.
Proof. exact (@lem3893825 (@lem3893835)). Qed.
Lemma lem3893838 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3893839 : term146 = term147.
Proof. exact (@lem3893838 term79 term79). Qed.
Lemma lem3893840 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893841 : term149 = term79.
Proof. exact (EQ_MP (@lem3893840) (@lem940073)). Qed.
Lemma lem3893842 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893843 : term147 = term78.
Proof. exact (MK_COMB (@lem3893842) (@lem3893841)). Qed.
Lemma lem3893844 : term146 = term78.
Proof. exact (TRANS (@lem3893839) (@lem3893843)). Qed.
Lemma lem3893846 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3893847 : term164 = term169.
Proof. exact (@lem3893846 term79 term79). Qed.
Lemma lem3893848 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893849 : term149 = term79.
Proof. exact (EQ_MP (@lem3893848) (@lem940073)). Qed.
Lemma lem3893850 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893851 : term147 = term78.
Proof. exact (MK_COMB (@lem3893850) (@lem3893849)). Qed.
Lemma lem3893852 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3893853 : term169 = term137.
Proof. exact (MK_COMB (@lem3893852) (@lem3893851)). Qed.
Lemma lem3893854 : term164 = term137.
Proof. exact (TRANS (@lem3893847) (@lem3893853)). Qed.
Lemma lem3893855 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3893856 : term191 = term179.
Proof. exact (MK_COMB (@lem3893855) (@lem3893854)). Qed.
Lemma lem3893857 : term192 = term181.
Proof. exact (MK_COMB (@lem3893856) (@lem3893844)). Qed.
Lemma lem3893859 (m : nat) : (term193 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3893860 : term181 = term62.
Proof. exact (@lem3893859 term79). Qed.
Lemma lem3893861 : term192 = term62.
Proof. exact (TRANS (@lem3893857) (@lem3893860)). Qed.
Lemma lem3893862 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3893863 : term194 = term195.
Proof. exact (MK_COMB (@lem3893862) (@lem3893861)). Qed.
Lemma lem3893864 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem3893865 : term196 = term197.
Proof. exact (MK_COMB (@lem3893863) (@lem3893864)). Qed.
Lemma lem3893867 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3893868 : term197 = term62.
Proof. exact (@lem3893867 term79). Qed.
Lemma lem3893869 : term196 = term62.
Proof. exact (TRANS (@lem3893865) (@lem3893868)). Qed.
Lemma lem3893871 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3893872 : term146 = term147.
Proof. exact (@lem3893871 term79 term79). Qed.
Lemma lem3893873 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893874 : term149 = term79.
Proof. exact (EQ_MP (@lem3893873) (@lem940073)). Qed.
Lemma lem3893875 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893876 : term147 = term78.
Proof. exact (MK_COMB (@lem3893875) (@lem3893874)). Qed.
Lemma lem3893877 : term146 = term78.
Proof. exact (TRANS (@lem3893872) (@lem3893876)). Qed.
Lemma lem3893878 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem3893879 : term199 = term197.
Proof. exact (MK_COMB (@lem3893878) (@lem3893877)). Qed.
Lemma lem3893881 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3893882 : term197 = term62.
Proof. exact (@lem3893881 term79). Qed.
Lemma lem3893883 : term199 = term62.
Proof. exact (TRANS (@lem3893879) (@lem3893882)). Qed.
Lemma lem3893884 : term62 = term199.
Proof. exact (SYM (@lem3893883)). Qed.
Lemma lem3893885 : term196 = term199.
Proof. exact (TRANS (@lem3893869) (@lem3893884)). Qed.
Lemma lem3893886 : term182 = term134.
Proof. exact (@lem3893836 (@lem3893885)). Qed.
Lemma lem3893887 : term181 = term134.
Proof. exact (TRANS (@lem3893802) (@lem3893886)). Qed.
Lemma lem3893889 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3893890 : term134 = term62.
Proof. exact (@lem3893889 term62). Qed.
Lemma lem3893891 : term181 = term62.
Proof. exact (TRANS (@lem3893887) (@lem3893890)). Qed.
Lemma lem3893892 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3893893 : term200 = term195.
Proof. exact (MK_COMB (@lem3893892) (@lem3893891)). Qed.
Lemma lem3893894 (_45282 : int) : (real_of_int _45282) = (real_of_int _45282).
Proof. exact (eq_refl (real_of_int _45282)). Qed.
Lemma lem3893895 (_45282 : int) : (term178 _45282) = (term201 _45282).
Proof. exact (MK_COMB (@lem3893893) (@lem3893894 _45282)). Qed.
Lemma lem3893896 (_45282 : int) : (term177 _45282) = (term201 _45282).
Proof. exact (TRANS (@lem3893793 _45282) (@lem3893895 _45282)). Qed.
Lemma lem3893897 (_45282 : int) : (term201 _45282) = term62.
Proof. exact (@lem1982719 (real_of_int _45282)). Qed.
Lemma lem3893898 (_45282 : int) : (term177 _45282) = term62.
Proof. exact (TRANS (@lem3893896 _45282) (@lem3893897 _45282)). Qed.
Lemma lem3893899 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3893900 (_45282 : int) : (term202 _45282) = term111.
Proof. exact (MK_COMB (@lem3893899) (@lem3893898 _45282)). Qed.
Lemma lem3893901 (_45283 : int) : (term173 _45283) = (term173 _45283).
Proof. exact (eq_refl (term173 _45283)). Qed.
Lemma lem3893902 (_45282 : int) (_45283 : int) : (term218 _45282 _45283) = (term219 _45283).
Proof. exact (MK_COMB (@lem3893900 _45282) (@lem3893901 _45283)). Qed.
Lemma lem3893903 (_45282 : int) (_45283 : int) : (term217 _45282 _45283) = (term219 _45283).
Proof. exact (TRANS (@lem3893792 _45282 _45283) (@lem3893902 _45282 _45283)). Qed.
Lemma lem3893904 (_45283 : int) : (term219 _45283) = (term173 _45283).
Proof. exact (@lem1982721 (term173 _45283)). Qed.
Lemma lem3893905 (_45282 : int) (_45283 : int) : (term217 _45282 _45283) = (term173 _45283).
Proof. exact (TRANS (@lem3893903 _45282 _45283) (@lem3893904 _45283)). Qed.
Lemma lem3893906 (_45282 : int) (_45283 : int) : (term213 _45282 _45283) = (term173 _45283).
Proof. exact (TRANS (@lem3893791 _45282 _45283) (@lem3893905 _45282 _45283)). Qed.
Lemma lem3893907 (_45282 : int) (_45283 : int) : (term212 _45282 _45283) = (term173 _45283).
Proof. exact (TRANS (@lem3893740 _45282 _45283) (@lem3893906 _45282 _45283)). Qed.
Lemma lem3893908 (_45282 : int) (_45283 : int) : (term211 _45282 _45283) = (term173 _45283).
Proof. exact (TRANS (@lem3893739 _45282 _45283) (@lem3893907 _45282 _45283)). Qed.
Lemma lem3893909 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3893910 (_45282 : int) (_45283 : int) : (term220 _45282 _45283) = (term221 _45283).
Proof. exact (MK_COMB (@lem3893909) (@lem3893908 _45282 _45283)). Qed.
Lemma lem3893911 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3893912 (_45282 : int) (_45283 : int) : (term208 _45282 _45283) = (term222 _45283).
Proof. exact (MK_COMB (@lem3893910 _45282 _45283) (@lem3893911)). Qed.
Lemma lem3893913 (_45282 : int) (_45283 : int) : (term97 _45283 _45282) = (term222 _45283).
Proof. exact (TRANS (@lem3893718 _45282 _45283) (@lem3893912 _45282 _45283)). Qed.
Lemma lem3893914 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3893915 (_45282 : int) (_45283 : int) : (term86 _45282 _45283) = (term223 _45283).
Proof. exact (MK_COMB (@lem3893914) (@lem3893717 _45282 _45283)). Qed.
Lemma lem3893916 (_45282 : int) (_45283 : int) : (term98 _45283 _45282) = (term224 _45283).
Proof. exact (MK_COMB (@lem3893915 _45282 _45283) (@lem3893913 _45282 _45283)). Qed.
Lemma lem3893917 (_45283 : int) : (term102 _45283) = (term225 _45283).
Proof. exact (@lem1988287 term62 (term81 _45283)). Qed.
Lemma lem3893929 (_45283 : int) : (term226 _45283) = (term227 _45283).
Proof. exact (@lem1982792 term62 (term81 _45283)). Qed.
Lemma lem3893930 (_45283 : int) : (term161 _45283) = (term162 _45283).
Proof. exact (@lem1982781 (real_of_int _45283) term137 term78). Qed.
Lemma lem3893932 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3893933 : term78 = term163.
Proof. exact (@lem3893932 term79). Qed.
Lemma lem3893935 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3893936 : term137 = term138.
Proof. exact (@lem3893935 term79). Qed.
Lemma lem3893937 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3893938 : term139 = term140.
Proof. exact (MK_COMB (@lem3893937) (@lem3893936)). Qed.
Lemma lem3893939 : term164 = term165.
Proof. exact (MK_COMB (@lem3893938) (@lem3893933)). Qed.
Lemma lem3893940 : term165 = term166.
Proof. exact (@lem1981613 term137 term78 term78 term78). Qed.
Lemma lem3893942 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3893943 : term146 = term147.
Proof. exact (@lem3893942 term79 term79). Qed.
Lemma lem3893944 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893945 : term149 = term79.
Proof. exact (EQ_MP (@lem3893944) (@lem940073)). Qed.
Lemma lem3893946 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893947 : term147 = term78.
Proof. exact (MK_COMB (@lem3893946) (@lem3893945)). Qed.
Lemma lem3893948 : term146 = term78.
Proof. exact (TRANS (@lem3893943) (@lem3893947)). Qed.
Lemma lem3893950 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3893951 : term164 = term169.
Proof. exact (@lem3893950 term79 term79). Qed.
Lemma lem3893952 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3893953 : term149 = term79.
Proof. exact (EQ_MP (@lem3893952) (@lem940073)). Qed.
Lemma lem3893954 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3893955 : term147 = term78.
Proof. exact (MK_COMB (@lem3893954) (@lem3893953)). Qed.
Lemma lem3893956 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3893957 : term169 = term137.
Proof. exact (MK_COMB (@lem3893956) (@lem3893955)). Qed.
Lemma lem3893958 : term164 = term137.
Proof. exact (TRANS (@lem3893951) (@lem3893957)). Qed.
Lemma lem3893959 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3893960 : term170 = term171.
Proof. exact (MK_COMB (@lem3893959) (@lem3893958)). Qed.
Lemma lem3893961 : term166 = term138.
Proof. exact (MK_COMB (@lem3893960) (@lem3893948)). Qed.
Lemma lem3893962 : term165 = term138.
Proof. exact (TRANS (@lem3893940) (@lem3893961)). Qed.
Lemma lem3893963 : term164 = term138.
Proof. exact (TRANS (@lem3893939) (@lem3893962)). Qed.
Lemma lem3893965 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3893966 : term138 = term137.
Proof. exact (@lem3893965 term137). Qed.
Lemma lem3893967 : term164 = term137.
Proof. exact (TRANS (@lem3893963) (@lem3893966)). Qed.
Lemma lem3893970 (_45283 : int) : (term172 _45283) = (term172 _45283).
Proof. exact (eq_refl (term172 _45283)). Qed.
Lemma lem3893971 (_45283 : int) : (term162 _45283) = (term173 _45283).
Proof. exact (MK_COMB (@lem3893970 _45283) (@lem3893967)). Qed.
Lemma lem3893972 (_45283 : int) : (term161 _45283) = (term173 _45283).
Proof. exact (TRANS (@lem3893930 _45283) (@lem3893971 _45283)). Qed.
Lemma lem3893973 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem3893974 (_45283 : int) : (term227 _45283) = (term219 _45283).
Proof. exact (MK_COMB (@lem3893973) (@lem3893972 _45283)). Qed.
Lemma lem3893975 (_45283 : int) : (term219 _45283) = (term173 _45283).
Proof. exact (@lem1982721 (term173 _45283)). Qed.
Lemma lem3893976 (_45283 : int) : (term227 _45283) = (term173 _45283).
Proof. exact (TRANS (@lem3893974 _45283) (@lem3893975 _45283)). Qed.
Lemma lem3893978 (_45283 : int) : (term226 _45283) = (term173 _45283).
Proof. exact (TRANS (@lem3893929 _45283) (@lem3893976 _45283)). Qed.
Lemma lem3893979 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3893980 (_45283 : int) : (term228 _45283) = (term221 _45283).
Proof. exact (MK_COMB (@lem3893979) (@lem3893978 _45283)). Qed.
Lemma lem3893981 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3893982 (_45283 : int) : (term225 _45283) = (term222 _45283).
Proof. exact (MK_COMB (@lem3893980 _45283) (@lem3893981)). Qed.
Lemma lem3893983 (_45283 : int) : (term102 _45283) = (term222 _45283).
Proof. exact (TRANS (@lem3893917 _45283) (@lem3893982 _45283)). Qed.
Lemma lem3893984 (_45283 : int) : (term115 _45283) = (term229 _45283).
Proof. exact (@lem1988287 (real_of_int _45283) term112). Qed.
Lemma lem3893991 : term112 = term78.
Proof. exact (@lem1982721 term78). Qed.
Lemma lem3893994 (_45283 : int) : (term210 _45283) = (term210 _45283).
Proof. exact (eq_refl (term210 _45283)). Qed.
Lemma lem3893995 (_45283 : int) : (term230 _45283) = (term231 _45283).
Proof. exact (MK_COMB (@lem3893994 _45283) (@lem3893991)). Qed.
Lemma lem3893996 (_45283 : int) : (term231 _45283) = (term232 _45283).
Proof. exact (@lem1982792 (real_of_int _45283) term78). Qed.
Lemma lem3893998 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3893999 : term78 = term163.
Proof. exact (@lem3893998 term79). Qed.
Lemma lem3894001 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3894002 : term137 = term138.
Proof. exact (@lem3894001 term79). Qed.
Lemma lem3894003 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3894004 : term139 = term140.
Proof. exact (MK_COMB (@lem3894003) (@lem3894002)). Qed.
Lemma lem3894005 : term164 = term165.
Proof. exact (MK_COMB (@lem3894004) (@lem3893999)). Qed.
Lemma lem3894006 : term165 = term166.
Proof. exact (@lem1981613 term137 term78 term78 term78). Qed.
Lemma lem3894008 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3894009 : term146 = term147.
Proof. exact (@lem3894008 term79 term79). Qed.
Lemma lem3894010 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894011 : term149 = term79.
Proof. exact (EQ_MP (@lem3894010) (@lem940073)). Qed.
Lemma lem3894012 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894013 : term147 = term78.
Proof. exact (MK_COMB (@lem3894012) (@lem3894011)). Qed.
Lemma lem3894014 : term146 = term78.
Proof. exact (TRANS (@lem3894009) (@lem3894013)). Qed.
Lemma lem3894016 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3894017 : term164 = term169.
Proof. exact (@lem3894016 term79 term79). Qed.
Lemma lem3894018 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894019 : term149 = term79.
Proof. exact (EQ_MP (@lem3894018) (@lem940073)). Qed.
Lemma lem3894020 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894021 : term147 = term78.
Proof. exact (MK_COMB (@lem3894020) (@lem3894019)). Qed.
Lemma lem3894022 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3894023 : term169 = term137.
Proof. exact (MK_COMB (@lem3894022) (@lem3894021)). Qed.
Lemma lem3894024 : term164 = term137.
Proof. exact (TRANS (@lem3894017) (@lem3894023)). Qed.
Lemma lem3894025 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3894026 : term170 = term171.
Proof. exact (MK_COMB (@lem3894025) (@lem3894024)). Qed.
Lemma lem3894027 : term166 = term138.
Proof. exact (MK_COMB (@lem3894026) (@lem3894014)). Qed.
Lemma lem3894028 : term165 = term138.
Proof. exact (TRANS (@lem3894006) (@lem3894027)). Qed.
Lemma lem3894029 : term164 = term138.
Proof. exact (TRANS (@lem3894005) (@lem3894028)). Qed.
Lemma lem3894031 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3894032 : term138 = term137.
Proof. exact (@lem3894031 term137). Qed.
Lemma lem3894033 : term164 = term137.
Proof. exact (TRANS (@lem3894029) (@lem3894032)). Qed.
Lemma lem3894034 (_45283 : int) : (term80 _45283) = (term80 _45283).
Proof. exact (eq_refl (term80 _45283)). Qed.
Lemma lem3894037 (_45283 : int) : (term232 _45283) = (term203 _45283).
Proof. exact (MK_COMB (@lem3894034 _45283) (@lem3894033)). Qed.
Lemma lem3894038 (_45283 : int) : (term231 _45283) = (term203 _45283).
Proof. exact (TRANS (@lem3893996 _45283) (@lem3894037 _45283)). Qed.
Lemma lem3894039 (_45283 : int) : (term230 _45283) = (term203 _45283).
Proof. exact (TRANS (@lem3893995 _45283) (@lem3894038 _45283)). Qed.
Lemma lem3894040 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3894041 (_45283 : int) : (term233 _45283) = (term206 _45283).
Proof. exact (MK_COMB (@lem3894040) (@lem3894039 _45283)). Qed.
Lemma lem3894042 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3894043 (_45283 : int) : (term229 _45283) = (term207 _45283).
Proof. exact (MK_COMB (@lem3894041 _45283) (@lem3894042)). Qed.
Lemma lem3894044 (_45283 : int) : (term115 _45283) = (term207 _45283).
Proof. exact (TRANS (@lem3893984 _45283) (@lem3894043 _45283)). Qed.
Lemma lem3894045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3894046 (_45283 : int) : (term104 _45283) = (term234 _45283).
Proof. exact (MK_COMB (@lem3894045) (@lem3893983 _45283)). Qed.
Lemma lem3894047 (_45283 : int) : (term116 _45283) = (term235 _45283).
Proof. exact (MK_COMB (@lem3894046 _45283) (@lem3894044 _45283)). Qed.
Lemma lem3894048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3894049 (_45282 : int) (_45283 : int) : (term118 _45283 _45282) = (term236 _45283).
Proof. exact (MK_COMB (@lem3894048) (@lem3893916 _45282 _45283)). Qed.
Lemma lem3894050 (_45282 : int) (_45283 : int) : (term119 _45282 _45283) = (term237 _45283).
Proof. exact (MK_COMB (@lem3894049 _45282 _45283) (@lem3894047 _45283)). Qed.
Lemma lem3894051 (_45282 : int) (_45283 : int) : ((real_of_int _45282) = (term73 _45282 _45283)) = ((term238 _45282 _45283) = term62).
Proof. exact (@lem1988293 (real_of_int _45282) (term73 _45282 _45283)). Qed.
Lemma lem3894063 (_45282 : int) (_45283 : int) : (term238 _45282 _45283) = (term239 _45282 _45283).
Proof. exact (@lem1982792 (real_of_int _45282) (term73 _45282 _45283)). Qed.
Lemma lem3894070 (_45282 : int) (_45283 : int) : (term240 _45282 _45283) = (term241 _45282 _45283).
Proof. exact (@lem1982781 (real_of_int _45282) term137 (real_of_int _45283)). Qed.
Lemma lem3894071 (_45282 : int) : (term80 _45282) = (term80 _45282).
Proof. exact (eq_refl (term80 _45282)). Qed.
Lemma lem3894072 (_45282 : int) (_45283 : int) : (term239 _45282 _45283) = (term242 _45282 _45283).
Proof. exact (MK_COMB (@lem3894071 _45282) (@lem3894070 _45282 _45283)). Qed.
Lemma lem3894073 (_45282 : int) (_45283 : int) : (term242 _45282 _45283) = (term243 _45282 _45283).
Proof. exact (@lem1982763 (real_of_int _45282) (term176 _45282) (term176 _45283)). Qed.
Lemma lem3894074 (_45282 : int) : (term177 _45282) = (term178 _45282).
Proof. exact (@lem1982715 term137 (real_of_int _45282)). Qed.
Lemma lem3894076 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3894077 : term78 = term163.
Proof. exact (@lem3894076 term79). Qed.
Lemma lem3894079 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3894080 : term137 = term138.
Proof. exact (@lem3894079 term79). Qed.
Lemma lem3894081 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3894082 : term179 = term180.
Proof. exact (MK_COMB (@lem3894081) (@lem3894080)). Qed.
Lemma lem3894083 : term181 = term182.
Proof. exact (MK_COMB (@lem3894082) (@lem3894077)). Qed.
Lemma lem3894084 : term183.
Proof. exact (@lem1981473 term137 term78 term78 term78 term62 term78). Qed.
Lemma lem3894086 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894087 : term185 = term186.
Proof. exact (@lem3894086 (NUMERAL 0) term79). Qed.
Lemma lem3894088 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894089 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894090 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894089 h1) (fun h1 : term186 = True => @lem3894088)). Qed.
Lemma lem3894091 : term186 = True.
Proof. exact (EQ_MP (@lem3894090) (@lem3894088)). Qed.
Lemma lem3894092 : term185 = True.
Proof. exact (TRANS (@lem3894087) (@lem3894091)). Qed.
Lemma lem3894093 : True = term185.
Proof. exact (SYM (@lem3894092)). Qed.
Lemma lem3894094 : term185.
Proof. exact (EQ_MP (@lem3894093) (@lem0)). Qed.
Lemma lem3894095 : term188.
Proof. exact (@lem3894084 (@lem3894094)). Qed.
Lemma lem3894097 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894098 : term185 = term186.
Proof. exact (@lem3894097 (NUMERAL 0) term79). Qed.
Lemma lem3894099 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894100 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894101 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894100 h1) (fun h1 : term186 = True => @lem3894099)). Qed.
Lemma lem3894102 : term186 = True.
Proof. exact (EQ_MP (@lem3894101) (@lem3894099)). Qed.
Lemma lem3894103 : term185 = True.
Proof. exact (TRANS (@lem3894098) (@lem3894102)). Qed.
Lemma lem3894104 : True = term185.
Proof. exact (SYM (@lem3894103)). Qed.
Lemma lem3894105 : term185.
Proof. exact (EQ_MP (@lem3894104) (@lem0)). Qed.
Lemma lem3894106 : term189.
Proof. exact (@lem3894095 (@lem3894105)). Qed.
Lemma lem3894108 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894109 : term185 = term186.
Proof. exact (@lem3894108 (NUMERAL 0) term79). Qed.
Lemma lem3894110 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894111 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894112 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894111 h1) (fun h1 : term186 = True => @lem3894110)). Qed.
Lemma lem3894113 : term186 = True.
Proof. exact (EQ_MP (@lem3894112) (@lem3894110)). Qed.
Lemma lem3894114 : term185 = True.
Proof. exact (TRANS (@lem3894109) (@lem3894113)). Qed.
Lemma lem3894115 : True = term185.
Proof. exact (SYM (@lem3894114)). Qed.
Lemma lem3894116 : term185.
Proof. exact (EQ_MP (@lem3894115) (@lem0)). Qed.
Lemma lem3894117 : term190.
Proof. exact (@lem3894106 (@lem3894116)). Qed.
Lemma lem3894119 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3894120 : term146 = term147.
Proof. exact (@lem3894119 term79 term79). Qed.
Lemma lem3894121 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894122 : term149 = term79.
Proof. exact (EQ_MP (@lem3894121) (@lem940073)). Qed.
Lemma lem3894123 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894124 : term147 = term78.
Proof. exact (MK_COMB (@lem3894123) (@lem3894122)). Qed.
Lemma lem3894125 : term146 = term78.
Proof. exact (TRANS (@lem3894120) (@lem3894124)). Qed.
Lemma lem3894127 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3894128 : term164 = term169.
Proof. exact (@lem3894127 term79 term79). Qed.
Lemma lem3894129 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894130 : term149 = term79.
Proof. exact (EQ_MP (@lem3894129) (@lem940073)). Qed.
Lemma lem3894131 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894132 : term147 = term78.
Proof. exact (MK_COMB (@lem3894131) (@lem3894130)). Qed.
Lemma lem3894133 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3894134 : term169 = term137.
Proof. exact (MK_COMB (@lem3894133) (@lem3894132)). Qed.
Lemma lem3894135 : term164 = term137.
Proof. exact (TRANS (@lem3894128) (@lem3894134)). Qed.
Lemma lem3894136 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3894137 : term191 = term179.
Proof. exact (MK_COMB (@lem3894136) (@lem3894135)). Qed.
Lemma lem3894138 : term192 = term181.
Proof. exact (MK_COMB (@lem3894137) (@lem3894125)). Qed.
Lemma lem3894140 (m : nat) : (term193 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3894141 : term181 = term62.
Proof. exact (@lem3894140 term79). Qed.
Lemma lem3894142 : term192 = term62.
Proof. exact (TRANS (@lem3894138) (@lem3894141)). Qed.
Lemma lem3894143 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3894144 : term194 = term195.
Proof. exact (MK_COMB (@lem3894143) (@lem3894142)). Qed.
Lemma lem3894145 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem3894146 : term196 = term197.
Proof. exact (MK_COMB (@lem3894144) (@lem3894145)). Qed.
Lemma lem3894148 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3894149 : term197 = term62.
Proof. exact (@lem3894148 term79). Qed.
Lemma lem3894150 : term196 = term62.
Proof. exact (TRANS (@lem3894146) (@lem3894149)). Qed.
Lemma lem3894152 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3894153 : term146 = term147.
Proof. exact (@lem3894152 term79 term79). Qed.
Lemma lem3894154 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894155 : term149 = term79.
Proof. exact (EQ_MP (@lem3894154) (@lem940073)). Qed.
Lemma lem3894156 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894157 : term147 = term78.
Proof. exact (MK_COMB (@lem3894156) (@lem3894155)). Qed.
Lemma lem3894158 : term146 = term78.
Proof. exact (TRANS (@lem3894153) (@lem3894157)). Qed.
Lemma lem3894159 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem3894160 : term199 = term197.
Proof. exact (MK_COMB (@lem3894159) (@lem3894158)). Qed.
Lemma lem3894162 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3894163 : term197 = term62.
Proof. exact (@lem3894162 term79). Qed.
Lemma lem3894164 : term199 = term62.
Proof. exact (TRANS (@lem3894160) (@lem3894163)). Qed.
Lemma lem3894165 : term62 = term199.
Proof. exact (SYM (@lem3894164)). Qed.
Lemma lem3894166 : term196 = term199.
Proof. exact (TRANS (@lem3894150) (@lem3894165)). Qed.
Lemma lem3894167 : term182 = term134.
Proof. exact (@lem3894117 (@lem3894166)). Qed.
Lemma lem3894168 : term181 = term134.
Proof. exact (TRANS (@lem3894083) (@lem3894167)). Qed.
Lemma lem3894170 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3894171 : term134 = term62.
Proof. exact (@lem3894170 term62). Qed.
Lemma lem3894172 : term181 = term62.
Proof. exact (TRANS (@lem3894168) (@lem3894171)). Qed.
Lemma lem3894173 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3894174 : term200 = term195.
Proof. exact (MK_COMB (@lem3894173) (@lem3894172)). Qed.
Lemma lem3894175 (_45282 : int) : (real_of_int _45282) = (real_of_int _45282).
Proof. exact (eq_refl (real_of_int _45282)). Qed.
Lemma lem3894176 (_45282 : int) : (term178 _45282) = (term201 _45282).
Proof. exact (MK_COMB (@lem3894174) (@lem3894175 _45282)). Qed.
Lemma lem3894177 (_45282 : int) : (term177 _45282) = (term201 _45282).
Proof. exact (TRANS (@lem3894074 _45282) (@lem3894176 _45282)). Qed.
Lemma lem3894178 (_45282 : int) : (term201 _45282) = term62.
Proof. exact (@lem1982719 (real_of_int _45282)). Qed.
Lemma lem3894179 (_45282 : int) : (term177 _45282) = term62.
Proof. exact (TRANS (@lem3894177 _45282) (@lem3894178 _45282)). Qed.
Lemma lem3894180 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3894181 (_45282 : int) : (term202 _45282) = term111.
Proof. exact (MK_COMB (@lem3894180) (@lem3894179 _45282)). Qed.
Lemma lem3894182 (_45283 : int) : (term176 _45283) = (term176 _45283).
Proof. exact (eq_refl (term176 _45283)). Qed.
Lemma lem3894183 (_45282 : int) (_45283 : int) : (term243 _45282 _45283) = (term244 _45283).
Proof. exact (MK_COMB (@lem3894181 _45282) (@lem3894182 _45283)). Qed.
Lemma lem3894184 (_45282 : int) (_45283 : int) : (term242 _45282 _45283) = (term244 _45283).
Proof. exact (TRANS (@lem3894073 _45282 _45283) (@lem3894183 _45282 _45283)). Qed.
Lemma lem3894185 (_45283 : int) : (term244 _45283) = (term176 _45283).
Proof. exact (@lem1982721 (term176 _45283)). Qed.
Lemma lem3894186 (_45282 : int) (_45283 : int) : (term242 _45282 _45283) = (term176 _45283).
Proof. exact (TRANS (@lem3894184 _45282 _45283) (@lem3894185 _45283)). Qed.
Lemma lem3894187 (_45282 : int) (_45283 : int) : (term239 _45282 _45283) = (term176 _45283).
Proof. exact (TRANS (@lem3894072 _45282 _45283) (@lem3894186 _45282 _45283)). Qed.
Lemma lem3894189 (_45282 : int) (_45283 : int) : (term238 _45282 _45283) = (term176 _45283).
Proof. exact (TRANS (@lem3894063 _45282 _45283) (@lem3894187 _45282 _45283)). Qed.
Lemma lem3894190 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3894191 (_45282 : int) (_45283 : int) : (term245 _45282 _45283) = (term246 _45283).
Proof. exact (MK_COMB (@lem3894190) (@lem3894189 _45282 _45283)). Qed.
Lemma lem3894192 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3894193 (_45282 : int) (_45283 : int) : ((term238 _45282 _45283) = term62) = ((term176 _45283) = term62).
Proof. exact (MK_COMB (@lem3894191 _45282 _45283) (@lem3894192)). Qed.
Lemma lem3894194 (_45282 : int) (_45283 : int) : ((real_of_int _45282) = (term73 _45282 _45283)) = ((term176 _45283) = term62).
Proof. exact (TRANS (@lem3894051 _45282 _45283) (@lem3894193 _45282 _45283)). Qed.
Lemma lem3894195 (_45283 : int) : ((real_of_int _45283) = term62) = ((term131 _45283) = term62).
Proof. exact (@lem1988293 (real_of_int _45283) term62). Qed.
Lemma lem3894201 (_45283 : int) : (term131 _45283) = (term132 _45283).
Proof. exact (@lem1982792 (real_of_int _45283) term62). Qed.
Lemma lem3894203 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3894204 : term62 = term134.
Proof. exact (@lem3894203 (NUMERAL 0)). Qed.
Lemma lem3894206 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3894207 : term137 = term138.
Proof. exact (@lem3894206 term79). Qed.
Lemma lem3894208 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3894209 : term139 = term140.
Proof. exact (MK_COMB (@lem3894208) (@lem3894207)). Qed.
Lemma lem3894210 : term141 = term142.
Proof. exact (MK_COMB (@lem3894209) (@lem3894204)). Qed.
Lemma lem3894211 : term142 = term143.
Proof. exact (@lem1981613 term137 term62 term78 term78). Qed.
Lemma lem3894213 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3894214 : term146 = term147.
Proof. exact (@lem3894213 term79 term79). Qed.
Lemma lem3894215 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894216 : term149 = term79.
Proof. exact (EQ_MP (@lem3894215) (@lem940073)). Qed.
Lemma lem3894217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894218 : term147 = term78.
Proof. exact (MK_COMB (@lem3894217) (@lem3894216)). Qed.
Lemma lem3894219 : term146 = term78.
Proof. exact (TRANS (@lem3894214) (@lem3894218)). Qed.
Lemma lem3894221 (x : nat) : (term150 x) = term62.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3894222 : term141 = term62.
Proof. exact (@lem3894221 term79). Qed.
Lemma lem3894223 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3894224 : term151 = term152.
Proof. exact (MK_COMB (@lem3894223) (@lem3894222)). Qed.
Lemma lem3894225 : term143 = term134.
Proof. exact (MK_COMB (@lem3894224) (@lem3894219)). Qed.
Lemma lem3894226 : term142 = term134.
Proof. exact (TRANS (@lem3894211) (@lem3894225)). Qed.
Lemma lem3894227 : term141 = term134.
Proof. exact (TRANS (@lem3894210) (@lem3894226)). Qed.
Lemma lem3894229 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3894230 : term134 = term62.
Proof. exact (@lem3894229 term62). Qed.
Lemma lem3894231 : term141 = term62.
Proof. exact (TRANS (@lem3894227) (@lem3894230)). Qed.
Lemma lem3894232 (_45283 : int) : (term80 _45283) = (term80 _45283).
Proof. exact (eq_refl (term80 _45283)). Qed.
Lemma lem3894233 (_45283 : int) : (term132 _45283) = (term154 _45283).
Proof. exact (MK_COMB (@lem3894232 _45283) (@lem3894231)). Qed.
Lemma lem3894234 (_45283 : int) : (term154 _45283) = (real_of_int _45283).
Proof. exact (@lem1982723 (real_of_int _45283)). Qed.
Lemma lem3894235 (_45283 : int) : (term132 _45283) = (real_of_int _45283).
Proof. exact (TRANS (@lem3894233 _45283) (@lem3894234 _45283)). Qed.
Lemma lem3894237 (_45283 : int) : (term131 _45283) = (real_of_int _45283).
Proof. exact (TRANS (@lem3894201 _45283) (@lem3894235 _45283)). Qed.
Lemma lem3894238 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3894239 (_45283 : int) : (term247 _45283) = (term120 _45283).
Proof. exact (MK_COMB (@lem3894238) (@lem3894237 _45283)). Qed.
Lemma lem3894240 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3894241 (_45283 : int) : ((term131 _45283) = term62) = ((real_of_int _45283) = term62).
Proof. exact (MK_COMB (@lem3894239 _45283) (@lem3894240)). Qed.
Lemma lem3894242 (_45283 : int) : ((real_of_int _45283) = term62) = ((real_of_int _45283) = term62).
Proof. exact (TRANS (@lem3894195 _45283) (@lem3894241 _45283)). Qed.
Lemma lem3894243 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3894244 (_45282 : int) (_45283 : int) : (term121 _45282 _45283) = (term248 _45283).
Proof. exact (MK_COMB (@lem3894243) (@lem3894194 _45282 _45283)). Qed.
Lemma lem3894245 (_45282 : int) (_45283 : int) : (term122 _45282 _45283) = (term249 _45283).
Proof. exact (MK_COMB (@lem3894244 _45282 _45283) (@lem3894242 _45283)). Qed.
Lemma lem3894246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3894247 (_45282 : int) (_45283 : int) : (term123 _45282 _45283) = (term250 _45283).
Proof. exact (MK_COMB (@lem3894246) (@lem3894050 _45282 _45283)). Qed.
Lemma lem3894248 (_45282 : int) (_45283 : int) : (term124 _45282 _45283) = (term251 _45283).
Proof. exact (MK_COMB (@lem3894247 _45282 _45283) (@lem3894245 _45282 _45283)). Qed.
Lemma lem3894249 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3894250 (_45283 : int) : (term125 _45283) = (term252 _45283).
Proof. exact (MK_COMB (@lem3894249) (@lem3893531 _45283)). Qed.
Lemma lem3894251 (_45282 : int) (_45283 : int) : (term126 _45282 _45283) = (term253 _45283).
Proof. exact (MK_COMB (@lem3894250 _45283) (@lem3894248 _45282 _45283)). Qed.
Lemma lem3894252 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3894253 (_45282 : int) : (term125 _45282) = (term252 _45282).
Proof. exact (MK_COMB (@lem3894252) (@lem3893483 _45282)). Qed.
Lemma lem3894254 (_45282 : int) (_45283 : int) : (term127 _45282 _45283) = (term254 _45282 _45283).
Proof. exact (MK_COMB (@lem3894253 _45282) (@lem3894251 _45282 _45283)). Qed.
Lemma lem3894261 (_45282 : int) (_45283 : int) : (term129 _45282 _45283) = (term254 _45282 _45283).
Proof. exact (TRANS (@lem3893435 _45282 _45283) (@lem3894254 _45282 _45283)). Qed.
Lemma lem3894283 (_45283 : int) : (term251 _45283) = (term255 _45283).
Proof. exact (@lem19158 ((term176 _45283) = term62) (term237 _45283) ((real_of_int _45283) = term62)). Qed.
Lemma lem3894284 (_45283 : int) : (term256 _45283) = (term257 _45283).
Proof. exact (@lem19367 (term224 _45283) (term235 _45283) ((real_of_int _45283) = term62)). Qed.
Lemma lem3894291 (_45283 : int) : (term258 _45283) = (term259 _45283).
Proof. exact (@lem19367 (term222 _45283) (term207 _45283) ((real_of_int _45283) = term62)). Qed.
Lemma lem3894298 (_45283 : int) : (term260 _45283) = (term261 _45283).
Proof. exact (@lem19367 (term207 _45283) (term222 _45283) ((real_of_int _45283) = term62)). Qed.
Lemma lem3894299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3894300 (_45283 : int) : (term262 _45283) = (term263 _45283).
Proof. exact (MK_COMB (@lem3894299) (@lem3894298 _45283)). Qed.
Lemma lem3894301 (_45283 : int) : (term257 _45283) = (term264 _45283).
Proof. exact (MK_COMB (@lem3894300 _45283) (@lem3894291 _45283)). Qed.
Lemma lem3894302 (_45283 : int) : (term256 _45283) = (term264 _45283).
Proof. exact (TRANS (@lem3894284 _45283) (@lem3894301 _45283)). Qed.
Lemma lem3894303 (_45283 : int) : (term265 _45283) = (term266 _45283).
Proof. exact (@lem19367 (term224 _45283) (term235 _45283) ((term176 _45283) = term62)). Qed.
Lemma lem3894310 (_45283 : int) : (term267 _45283) = (term268 _45283).
Proof. exact (@lem19367 (term222 _45283) (term207 _45283) ((term176 _45283) = term62)). Qed.
Lemma lem3894317 (_45283 : int) : (term269 _45283) = (term270 _45283).
Proof. exact (@lem19367 (term207 _45283) (term222 _45283) ((term176 _45283) = term62)). Qed.
Lemma lem3894318 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3894319 (_45283 : int) : (term271 _45283) = (term272 _45283).
Proof. exact (MK_COMB (@lem3894318) (@lem3894317 _45283)). Qed.
Lemma lem3894320 (_45283 : int) : (term266 _45283) = (term273 _45283).
Proof. exact (MK_COMB (@lem3894319 _45283) (@lem3894310 _45283)). Qed.
Lemma lem3894321 (_45283 : int) : (term265 _45283) = (term273 _45283).
Proof. exact (TRANS (@lem3894303 _45283) (@lem3894320 _45283)). Qed.
Lemma lem3894322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3894323 (_45283 : int) : (term274 _45283) = (term275 _45283).
Proof. exact (MK_COMB (@lem3894322) (@lem3894321 _45283)). Qed.
Lemma lem3894324 (_45283 : int) : (term255 _45283) = (term276 _45283).
Proof. exact (MK_COMB (@lem3894323 _45283) (@lem3894302 _45283)). Qed.
Lemma lem3894326 (_45283 : int) : (term251 _45283) = (term276 _45283).
Proof. exact (TRANS (@lem3894283 _45283) (@lem3894324 _45283)). Qed.
Lemma lem3894329 (_45283 : int) : (term252 _45283) = (term252 _45283).
Proof. exact (eq_refl (term252 _45283)). Qed.
Lemma lem3894330 (_45283 : int) : (term253 _45283) = (term277 _45283).
Proof. exact (MK_COMB (@lem3894329 _45283) (@lem3894326 _45283)). Qed.
Lemma lem3894331 (_45283 : int) : (term277 _45283) = (term278 _45283).
Proof. exact (@lem19158 (term273 _45283) (term157 _45283) (term264 _45283)). Qed.
Lemma lem3894332 (_45283 : int) : (term279 _45283) = (term280 _45283).
Proof. exact (@lem19158 (term261 _45283) (term157 _45283) (term259 _45283)). Qed.
Lemma lem3894339 (_45283 : int) : (term281 _45283) = (term282 _45283).
Proof. exact (@lem19158 (term283 _45283) (term157 _45283) (term284 _45283)). Qed.
Lemma lem3894346 (_45283 : int) : (term285 _45283) = (term286 _45283).
Proof. exact (@lem19158 (term284 _45283) (term157 _45283) (term283 _45283)). Qed.
Lemma lem3894347 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3894348 (_45283 : int) : (term287 _45283) = (term288 _45283).
Proof. exact (MK_COMB (@lem3894347) (@lem3894346 _45283)). Qed.
Lemma lem3894349 (_45283 : int) : (term280 _45283) = (term289 _45283).
Proof. exact (MK_COMB (@lem3894348 _45283) (@lem3894339 _45283)). Qed.
Lemma lem3894350 (_45283 : int) : (term279 _45283) = (term289 _45283).
Proof. exact (TRANS (@lem3894332 _45283) (@lem3894349 _45283)). Qed.
Lemma lem3894351 (_45283 : int) : (term290 _45283) = (term291 _45283).
Proof. exact (@lem19158 (term270 _45283) (term157 _45283) (term268 _45283)). Qed.
Lemma lem3894358 (_45283 : int) : (term292 _45283) = (term293 _45283).
Proof. exact (@lem19158 (term294 _45283) (term157 _45283) (term295 _45283)). Qed.
Lemma lem3894365 (_45283 : int) : (term296 _45283) = (term297 _45283).
Proof. exact (@lem19158 (term295 _45283) (term157 _45283) (term294 _45283)). Qed.
Lemma lem3894366 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3894367 (_45283 : int) : (term298 _45283) = (term299 _45283).
Proof. exact (MK_COMB (@lem3894366) (@lem3894365 _45283)). Qed.
Lemma lem3894368 (_45283 : int) : (term291 _45283) = (term300 _45283).
Proof. exact (MK_COMB (@lem3894367 _45283) (@lem3894358 _45283)). Qed.
Lemma lem3894369 (_45283 : int) : (term290 _45283) = (term300 _45283).
Proof. exact (TRANS (@lem3894351 _45283) (@lem3894368 _45283)). Qed.
Lemma lem3894370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3894371 (_45283 : int) : (term301 _45283) = (term302 _45283).
Proof. exact (MK_COMB (@lem3894370) (@lem3894369 _45283)). Qed.
Lemma lem3894372 (_45283 : int) : (term278 _45283) = (term303 _45283).
Proof. exact (MK_COMB (@lem3894371 _45283) (@lem3894350 _45283)). Qed.
Lemma lem3894373 (_45283 : int) : (term277 _45283) = (term303 _45283).
Proof. exact (TRANS (@lem3894331 _45283) (@lem3894372 _45283)). Qed.
Lemma lem3894374 (_45283 : int) : (term253 _45283) = (term303 _45283).
Proof. exact (TRANS (@lem3894330 _45283) (@lem3894373 _45283)). Qed.
Lemma lem3894377 (_45282 : int) : (term252 _45282) = (term252 _45282).
Proof. exact (eq_refl (term252 _45282)). Qed.
Lemma lem3894378 (_45282 : int) (_45283 : int) : (term254 _45282 _45283) = (term304 _45282 _45283).
Proof. exact (MK_COMB (@lem3894377 _45282) (@lem3894374 _45283)). Qed.
Lemma lem3894379 (_45282 : int) (_45283 : int) : (term304 _45282 _45283) = (term305 _45282 _45283).
Proof. exact (@lem19158 (term300 _45283) (term157 _45282) (term289 _45283)). Qed.
Lemma lem3894380 (_45282 : int) (_45283 : int) : (term306 _45282 _45283) = (term307 _45282 _45283).
Proof. exact (@lem19158 (term286 _45283) (term157 _45282) (term282 _45283)). Qed.
Lemma lem3894387 (_45282 : int) (_45283 : int) : (term308 _45282 _45283) = (term309 _45282 _45283).
Proof. exact (@lem19158 (term310 _45283) (term157 _45282) (term311 _45283)). Qed.
Lemma lem3894394 (_45282 : int) (_45283 : int) : (term312 _45282 _45283) = (term313 _45282 _45283).
Proof. exact (@lem19158 (term311 _45283) (term157 _45282) (term310 _45283)). Qed.
Lemma lem3894395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3894396 (_45282 : int) (_45283 : int) : (term314 _45282 _45283) = (term315 _45282 _45283).
Proof. exact (MK_COMB (@lem3894395) (@lem3894394 _45282 _45283)). Qed.
Lemma lem3894397 (_45282 : int) (_45283 : int) : (term307 _45282 _45283) = (term316 _45282 _45283).
Proof. exact (MK_COMB (@lem3894396 _45282 _45283) (@lem3894387 _45282 _45283)). Qed.
Lemma lem3894398 (_45282 : int) (_45283 : int) : (term306 _45282 _45283) = (term316 _45282 _45283).
Proof. exact (TRANS (@lem3894380 _45282 _45283) (@lem3894397 _45282 _45283)). Qed.
Lemma lem3894399 (_45282 : int) (_45283 : int) : (term317 _45282 _45283) = (term318 _45282 _45283).
Proof. exact (@lem19158 (term297 _45283) (term157 _45282) (term293 _45283)). Qed.
Lemma lem3894406 (_45282 : int) (_45283 : int) : (term319 _45282 _45283) = (term320 _45282 _45283).
Proof. exact (@lem19158 (term321 _45283) (term157 _45282) (term322 _45283)). Qed.
Lemma lem3894413 (_45282 : int) (_45283 : int) : (term323 _45282 _45283) = (term324 _45282 _45283).
Proof. exact (@lem19158 (term322 _45283) (term157 _45282) (term321 _45283)). Qed.
Lemma lem3894414 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3894415 (_45282 : int) (_45283 : int) : (term325 _45282 _45283) = (term326 _45282 _45283).
Proof. exact (MK_COMB (@lem3894414) (@lem3894413 _45282 _45283)). Qed.
Lemma lem3894416 (_45282 : int) (_45283 : int) : (term318 _45282 _45283) = (term327 _45282 _45283).
Proof. exact (MK_COMB (@lem3894415 _45282 _45283) (@lem3894406 _45282 _45283)). Qed.
Lemma lem3894417 (_45282 : int) (_45283 : int) : (term317 _45282 _45283) = (term327 _45282 _45283).
Proof. exact (TRANS (@lem3894399 _45282 _45283) (@lem3894416 _45282 _45283)). Qed.
Lemma lem3894418 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3894419 (_45282 : int) (_45283 : int) : (term328 _45282 _45283) = (term329 _45282 _45283).
Proof. exact (MK_COMB (@lem3894418) (@lem3894417 _45282 _45283)). Qed.
Lemma lem3894420 (_45282 : int) (_45283 : int) : (term305 _45282 _45283) = (term330 _45282 _45283).
Proof. exact (MK_COMB (@lem3894419 _45282 _45283) (@lem3894398 _45282 _45283)). Qed.
Lemma lem3894421 (_45282 : int) (_45283 : int) : (term304 _45282 _45283) = (term330 _45282 _45283).
Proof. exact (TRANS (@lem3894379 _45282 _45283) (@lem3894420 _45282 _45283)). Qed.
Lemma lem3894422 (_45282 : int) (_45283 : int) : (term254 _45282 _45283) = (term330 _45282 _45283).
Proof. exact (TRANS (@lem3894378 _45282 _45283) (@lem3894421 _45282 _45283)). Qed.
Lemma lem3894423 (_45282 : int) (_45283 : int) : (term129 _45282 _45283) = (term330 _45282 _45283).
Proof. exact (TRANS (@lem3894261 _45282 _45283) (@lem3894422 _45282 _45283)). Qed.
Lemma lem3894469 (_45282 : int) (_45283 : int) (h1 : term330 _45282 _45283) : term330 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3894470 (_45282 : int) (_45283 : int) (h1 : term327 _45282 _45283) : term327 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3894471 (_45282 : int) (_45283 : int) (h1 : term324 _45282 _45283) : term324 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3894472 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term331 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3894473 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term322 _45283.
Proof. exact (proj2 (@lem3894472 _45282 _45283 h1)). Qed.
Lemma lem3894475 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term295 _45283.
Proof. exact (proj2 (@lem3894473 _45282 _45283 h1)). Qed.
Lemma lem3894477 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : (term176 _45283) = term62.
Proof. exact (proj2 (@lem3894475 _45282 _45283 h1)). Qed.
Lemma lem3894478 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term207 _45283.
Proof. exact (proj1 (@lem3894475 _45282 _45283 h1)). Qed.
Lemma lem3894480 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3894481 : term332 = term185.
Proof. exact (@lem3894480 term62 term78). Qed.
Lemma lem3894483 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3894484 : term78 = term163.
Proof. exact (@lem3894483 term79). Qed.
Lemma lem3894486 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3894487 : term62 = term134.
Proof. exact (@lem3894486 (NUMERAL 0)). Qed.
Lemma lem3894488 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3894489 : term333 = term334.
Proof. exact (MK_COMB (@lem3894488) (@lem3894487)). Qed.
Lemma lem3894490 : term185 = term335.
Proof. exact (MK_COMB (@lem3894489) (@lem3894484)). Qed.
Lemma lem3894491 : term336.
Proof. exact (@lem1980255 term62 term78 term78 term78). Qed.
Lemma lem3894493 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894494 : term185 = term186.
Proof. exact (@lem3894493 (NUMERAL 0) term79). Qed.
Lemma lem3894495 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894496 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894497 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894496 h1) (fun h1 : term186 = True => @lem3894495)). Qed.
Lemma lem3894498 : term186 = True.
Proof. exact (EQ_MP (@lem3894497) (@lem3894495)). Qed.
Lemma lem3894499 : term185 = True.
Proof. exact (TRANS (@lem3894494) (@lem3894498)). Qed.
Lemma lem3894500 : True = term185.
Proof. exact (SYM (@lem3894499)). Qed.
Lemma lem3894501 : term185.
Proof. exact (EQ_MP (@lem3894500) (@lem0)). Qed.
Lemma lem3894502 : term337.
Proof. exact (@lem3894491 (@lem3894501)). Qed.
Lemma lem3894504 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894505 : term185 = term186.
Proof. exact (@lem3894504 (NUMERAL 0) term79). Qed.
Lemma lem3894506 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894507 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894508 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894507 h1) (fun h1 : term186 = True => @lem3894506)). Qed.
Lemma lem3894509 : term186 = True.
Proof. exact (EQ_MP (@lem3894508) (@lem3894506)). Qed.
Lemma lem3894510 : term185 = True.
Proof. exact (TRANS (@lem3894505) (@lem3894509)). Qed.
Lemma lem3894511 : True = term185.
Proof. exact (SYM (@lem3894510)). Qed.
Lemma lem3894512 : term185.
Proof. exact (EQ_MP (@lem3894511) (@lem0)). Qed.
Lemma lem3894513 : term335 = term338.
Proof. exact (@lem3894502 (@lem3894512)). Qed.
Lemma lem3894515 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3894516 : term146 = term147.
Proof. exact (@lem3894515 term79 term79). Qed.
Lemma lem3894517 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894518 : term149 = term79.
Proof. exact (EQ_MP (@lem3894517) (@lem940073)). Qed.
Lemma lem3894519 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894520 : term147 = term78.
Proof. exact (MK_COMB (@lem3894519) (@lem3894518)). Qed.
Lemma lem3894521 : term146 = term78.
Proof. exact (TRANS (@lem3894516) (@lem3894520)). Qed.
Lemma lem3894523 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3894524 : term197 = term62.
Proof. exact (@lem3894523 term79). Qed.
Lemma lem3894525 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3894526 : term339 = term333.
Proof. exact (MK_COMB (@lem3894525) (@lem3894524)). Qed.
Lemma lem3894527 : term338 = term185.
Proof. exact (MK_COMB (@lem3894526) (@lem3894521)). Qed.
Lemma lem3894529 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894530 : term185 = term186.
Proof. exact (@lem3894529 (NUMERAL 0) term79). Qed.
Lemma lem3894531 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894532 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894533 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894532 h1) (fun h1 : term186 = True => @lem3894531)). Qed.
Lemma lem3894534 : term186 = True.
Proof. exact (EQ_MP (@lem3894533) (@lem3894531)). Qed.
Lemma lem3894535 : term185 = True.
Proof. exact (TRANS (@lem3894530) (@lem3894534)). Qed.
Lemma lem3894536 : term338 = True.
Proof. exact (TRANS (@lem3894527) (@lem3894535)). Qed.
Lemma lem3894537 : term335 = True.
Proof. exact (TRANS (@lem3894513) (@lem3894536)). Qed.
Lemma lem3894538 : term185 = True.
Proof. exact (TRANS (@lem3894490) (@lem3894537)). Qed.
Lemma lem3894539 : term332 = True.
Proof. exact (TRANS (@lem3894481) (@lem3894538)). Qed.
Lemma lem3894540 : True = term332.
Proof. exact (SYM (@lem3894539)). Qed.
Lemma lem3894541 : term332.
Proof. exact (EQ_MP (@lem3894540) (@lem0)). Qed.
Lemma lem3894542 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term340 _45283.
Proof. exact (conj (@lem3894541) (@lem3894478 _45282 _45283 h1)). Qed.
Lemma lem3894544 (x : real) (y : real) : term341 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3894545 (_45283 : int) : term342 _45283.
Proof. exact (@lem3894544 term78 (term203 _45283)). Qed.
Lemma lem3894546 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term343 _45283.
Proof. exact (@lem3894545 _45283 (@lem3894542 _45282 _45283 h1)). Qed.
Lemma lem3894547 (_45283 : int) : (term344 _45283) = (term203 _45283).
Proof. exact (@lem1982733 (term203 _45283)). Qed.
Lemma lem3894548 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3894549 (_45283 : int) : (term345 _45283) = (term206 _45283).
Proof. exact (MK_COMB (@lem3894548) (@lem3894547 _45283)). Qed.
Lemma lem3894550 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3894551 (_45283 : int) : (term343 _45283) = (term207 _45283).
Proof. exact (MK_COMB (@lem3894549 _45283) (@lem3894550)). Qed.
Lemma lem3894552 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term207 _45283.
Proof. exact (EQ_MP (@lem3894551 _45283) (@lem3894546 _45282 _45283 h1)). Qed.
Lemma lem3894554 (y : real) : term346 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3894555 (_45283 : int) : term347 _45283.
Proof. exact (@lem3894554 (term176 _45283)). Qed.
Lemma lem3894556 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term348 _45283.
Proof. exact (@lem3894555 _45283 (@lem3894477 _45282 _45283 h1)). Qed.
Lemma lem3894557 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term349 _45283.
Proof. exact (@lem3894556 _45282 _45283 h1 term78). Qed.
Lemma lem3894558 (_45283 : int) : (term349 _45283) = ((term350 _45283) = term62).
Proof. exact (eq_refl (term349 _45283)). Qed.
Lemma lem3894559 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : (term350 _45283) = term62.
Proof. exact (EQ_MP (@lem3894558 _45283) (@lem3894557 _45282 _45283 h1)). Qed.
Lemma lem3894560 (_45283 : int) : (term350 _45283) = (term176 _45283).
Proof. exact (@lem1982733 (term176 _45283)). Qed.
Lemma lem3894561 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3894562 (_45283 : int) : (term351 _45283) = (term246 _45283).
Proof. exact (MK_COMB (@lem3894561) (@lem3894560 _45283)). Qed.
Lemma lem3894563 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3894564 (_45283 : int) : ((term350 _45283) = term62) = ((term176 _45283) = term62).
Proof. exact (MK_COMB (@lem3894562 _45283) (@lem3894563)). Qed.
Lemma lem3894565 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : (term176 _45283) = term62.
Proof. exact (EQ_MP (@lem3894564 _45283) (@lem3894559 _45282 _45283 h1)). Qed.
Lemma lem3894566 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term352 _45283.
Proof. exact (conj (@lem3894565 _45282 _45283 h1) (@lem3894552 _45282 _45283 h1)). Qed.
Lemma lem3894568 (x : real) (y : real) : term353 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3894569 (_45283 : int) : term354 _45283.
Proof. exact (@lem3894568 (term176 _45283) (term203 _45283)). Qed.
Lemma lem3894570 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term355 _45283.
Proof. exact (@lem3894569 _45283 (@lem3894566 _45282 _45283 h1)). Qed.
Lemma lem3894571 (_45283 : int) : (term356 _45283) = (term357 _45283).
Proof. exact (@lem1982763 (term176 _45283) (real_of_int _45283) term137). Qed.
Lemma lem3894572 (_45283 : int) : (term358 _45283) = (term178 _45283).
Proof. exact (@lem1982713 term137 (real_of_int _45283)). Qed.
Lemma lem3894574 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3894575 : term78 = term163.
Proof. exact (@lem3894574 term79). Qed.
Lemma lem3894577 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3894578 : term137 = term138.
Proof. exact (@lem3894577 term79). Qed.
Lemma lem3894579 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3894580 : term179 = term180.
Proof. exact (MK_COMB (@lem3894579) (@lem3894578)). Qed.
Lemma lem3894581 : term181 = term182.
Proof. exact (MK_COMB (@lem3894580) (@lem3894575)). Qed.
Lemma lem3894582 : term183.
Proof. exact (@lem1981473 term137 term78 term78 term78 term62 term78). Qed.
Lemma lem3894584 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894585 : term185 = term186.
Proof. exact (@lem3894584 (NUMERAL 0) term79). Qed.
Lemma lem3894586 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894587 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894588 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894587 h1) (fun h1 : term186 = True => @lem3894586)). Qed.
Lemma lem3894589 : term186 = True.
Proof. exact (EQ_MP (@lem3894588) (@lem3894586)). Qed.
Lemma lem3894590 : term185 = True.
Proof. exact (TRANS (@lem3894585) (@lem3894589)). Qed.
Lemma lem3894591 : True = term185.
Proof. exact (SYM (@lem3894590)). Qed.
Lemma lem3894592 : term185.
Proof. exact (EQ_MP (@lem3894591) (@lem0)). Qed.
Lemma lem3894593 : term188.
Proof. exact (@lem3894582 (@lem3894592)). Qed.
Lemma lem3894595 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894596 : term185 = term186.
Proof. exact (@lem3894595 (NUMERAL 0) term79). Qed.
Lemma lem3894597 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894598 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894599 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894598 h1) (fun h1 : term186 = True => @lem3894597)). Qed.
Lemma lem3894600 : term186 = True.
Proof. exact (EQ_MP (@lem3894599) (@lem3894597)). Qed.
Lemma lem3894601 : term185 = True.
Proof. exact (TRANS (@lem3894596) (@lem3894600)). Qed.
Lemma lem3894602 : True = term185.
Proof. exact (SYM (@lem3894601)). Qed.
Lemma lem3894603 : term185.
Proof. exact (EQ_MP (@lem3894602) (@lem0)). Qed.
Lemma lem3894604 : term189.
Proof. exact (@lem3894593 (@lem3894603)). Qed.
Lemma lem3894606 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894607 : term185 = term186.
Proof. exact (@lem3894606 (NUMERAL 0) term79). Qed.
Lemma lem3894608 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894609 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894610 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894609 h1) (fun h1 : term186 = True => @lem3894608)). Qed.
Lemma lem3894611 : term186 = True.
Proof. exact (EQ_MP (@lem3894610) (@lem3894608)). Qed.
Lemma lem3894612 : term185 = True.
Proof. exact (TRANS (@lem3894607) (@lem3894611)). Qed.
Lemma lem3894613 : True = term185.
Proof. exact (SYM (@lem3894612)). Qed.
Lemma lem3894614 : term185.
Proof. exact (EQ_MP (@lem3894613) (@lem0)). Qed.
Lemma lem3894615 : term190.
Proof. exact (@lem3894604 (@lem3894614)). Qed.
Lemma lem3894617 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3894618 : term146 = term147.
Proof. exact (@lem3894617 term79 term79). Qed.
Lemma lem3894619 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894620 : term149 = term79.
Proof. exact (EQ_MP (@lem3894619) (@lem940073)). Qed.
Lemma lem3894621 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894622 : term147 = term78.
Proof. exact (MK_COMB (@lem3894621) (@lem3894620)). Qed.
Lemma lem3894623 : term146 = term78.
Proof. exact (TRANS (@lem3894618) (@lem3894622)). Qed.
Lemma lem3894625 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3894626 : term164 = term169.
Proof. exact (@lem3894625 term79 term79). Qed.
Lemma lem3894627 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894628 : term149 = term79.
Proof. exact (EQ_MP (@lem3894627) (@lem940073)). Qed.
Lemma lem3894629 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894630 : term147 = term78.
Proof. exact (MK_COMB (@lem3894629) (@lem3894628)). Qed.
Lemma lem3894631 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3894632 : term169 = term137.
Proof. exact (MK_COMB (@lem3894631) (@lem3894630)). Qed.
Lemma lem3894633 : term164 = term137.
Proof. exact (TRANS (@lem3894626) (@lem3894632)). Qed.
Lemma lem3894634 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3894635 : term191 = term179.
Proof. exact (MK_COMB (@lem3894634) (@lem3894633)). Qed.
Lemma lem3894636 : term192 = term181.
Proof. exact (MK_COMB (@lem3894635) (@lem3894623)). Qed.
Lemma lem3894638 (m : nat) : (term193 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3894639 : term181 = term62.
Proof. exact (@lem3894638 term79). Qed.
Lemma lem3894640 : term192 = term62.
Proof. exact (TRANS (@lem3894636) (@lem3894639)). Qed.
Lemma lem3894641 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3894642 : term194 = term195.
Proof. exact (MK_COMB (@lem3894641) (@lem3894640)). Qed.
Lemma lem3894643 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem3894644 : term196 = term197.
Proof. exact (MK_COMB (@lem3894642) (@lem3894643)). Qed.
Lemma lem3894646 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3894647 : term197 = term62.
Proof. exact (@lem3894646 term79). Qed.
Lemma lem3894648 : term196 = term62.
Proof. exact (TRANS (@lem3894644) (@lem3894647)). Qed.
Lemma lem3894650 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3894651 : term146 = term147.
Proof. exact (@lem3894650 term79 term79). Qed.
Lemma lem3894652 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894653 : term149 = term79.
Proof. exact (EQ_MP (@lem3894652) (@lem940073)). Qed.
Lemma lem3894654 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894655 : term147 = term78.
Proof. exact (MK_COMB (@lem3894654) (@lem3894653)). Qed.
Lemma lem3894656 : term146 = term78.
Proof. exact (TRANS (@lem3894651) (@lem3894655)). Qed.
Lemma lem3894657 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem3894658 : term199 = term197.
Proof. exact (MK_COMB (@lem3894657) (@lem3894656)). Qed.
Lemma lem3894660 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3894661 : term197 = term62.
Proof. exact (@lem3894660 term79). Qed.
Lemma lem3894662 : term199 = term62.
Proof. exact (TRANS (@lem3894658) (@lem3894661)). Qed.
Lemma lem3894663 : term62 = term199.
Proof. exact (SYM (@lem3894662)). Qed.
Lemma lem3894664 : term196 = term199.
Proof. exact (TRANS (@lem3894648) (@lem3894663)). Qed.
Lemma lem3894665 : term182 = term134.
Proof. exact (@lem3894615 (@lem3894664)). Qed.
Lemma lem3894666 : term181 = term134.
Proof. exact (TRANS (@lem3894581) (@lem3894665)). Qed.
Lemma lem3894668 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3894669 : term134 = term62.
Proof. exact (@lem3894668 term62). Qed.
Lemma lem3894670 : term181 = term62.
Proof. exact (TRANS (@lem3894666) (@lem3894669)). Qed.
Lemma lem3894671 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3894672 : term200 = term195.
Proof. exact (MK_COMB (@lem3894671) (@lem3894670)). Qed.
Lemma lem3894673 (_45283 : int) : (real_of_int _45283) = (real_of_int _45283).
Proof. exact (eq_refl (real_of_int _45283)). Qed.
Lemma lem3894674 (_45283 : int) : (term178 _45283) = (term201 _45283).
Proof. exact (MK_COMB (@lem3894672) (@lem3894673 _45283)). Qed.
Lemma lem3894675 (_45283 : int) : (term358 _45283) = (term201 _45283).
Proof. exact (TRANS (@lem3894572 _45283) (@lem3894674 _45283)). Qed.
Lemma lem3894676 (_45283 : int) : (term201 _45283) = term62.
Proof. exact (@lem1982719 (real_of_int _45283)). Qed.
Lemma lem3894677 (_45283 : int) : (term358 _45283) = term62.
Proof. exact (TRANS (@lem3894675 _45283) (@lem3894676 _45283)). Qed.
Lemma lem3894678 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3894679 (_45283 : int) : (term359 _45283) = term111.
Proof. exact (MK_COMB (@lem3894678) (@lem3894677 _45283)). Qed.
Lemma lem3894680 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem3894681 (_45283 : int) : (term357 _45283) = term360.
Proof. exact (MK_COMB (@lem3894679 _45283) (@lem3894680)). Qed.
Lemma lem3894682 (_45283 : int) : (term356 _45283) = term360.
Proof. exact (TRANS (@lem3894571 _45283) (@lem3894681 _45283)). Qed.
Lemma lem3894683 : term360 = term137.
Proof. exact (@lem1982721 term137). Qed.
Lemma lem3894684 (_45283 : int) : (term356 _45283) = term137.
Proof. exact (TRANS (@lem3894682 _45283) (@lem3894683)). Qed.
Lemma lem3894685 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3894686 (_45283 : int) : (term361 _45283) = term362.
Proof. exact (MK_COMB (@lem3894685) (@lem3894684 _45283)). Qed.
Lemma lem3894687 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3894688 (_45283 : int) : (term355 _45283) = term363.
Proof. exact (MK_COMB (@lem3894686 _45283) (@lem3894687)). Qed.
Lemma lem3894689 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term363.
Proof. exact (EQ_MP (@lem3894688 _45283) (@lem3894570 _45282 _45283 h1)). Qed.
Lemma lem3894691 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3894692 : term363 = term364.
Proof. exact (@lem3894691 term62 term137). Qed.
Lemma lem3894694 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3894695 : term137 = term138.
Proof. exact (@lem3894694 term79). Qed.
Lemma lem3894697 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3894698 : term62 = term134.
Proof. exact (@lem3894697 (NUMERAL 0)). Qed.
Lemma lem3894699 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3894700 : term64 = term365.
Proof. exact (MK_COMB (@lem3894699) (@lem3894698)). Qed.
Lemma lem3894701 : term364 = term366.
Proof. exact (MK_COMB (@lem3894700) (@lem3894695)). Qed.
Lemma lem3894702 : term367.
Proof. exact (@lem1980026 term62 term78 term137 term78). Qed.
Lemma lem3894704 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894705 : term185 = term186.
Proof. exact (@lem3894704 (NUMERAL 0) term79). Qed.
Lemma lem3894706 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894707 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894708 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894707 h1) (fun h1 : term186 = True => @lem3894706)). Qed.
Lemma lem3894709 : term186 = True.
Proof. exact (EQ_MP (@lem3894708) (@lem3894706)). Qed.
Lemma lem3894710 : term185 = True.
Proof. exact (TRANS (@lem3894705) (@lem3894709)). Qed.
Lemma lem3894711 : True = term185.
Proof. exact (SYM (@lem3894710)). Qed.
Lemma lem3894712 : term185.
Proof. exact (EQ_MP (@lem3894711) (@lem0)). Qed.
Lemma lem3894713 : term368.
Proof. exact (@lem3894702 (@lem3894712)). Qed.
Lemma lem3894715 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894716 : term185 = term186.
Proof. exact (@lem3894715 (NUMERAL 0) term79). Qed.
Lemma lem3894717 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894718 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894719 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894718 h1) (fun h1 : term186 = True => @lem3894717)). Qed.
Lemma lem3894720 : term186 = True.
Proof. exact (EQ_MP (@lem3894719) (@lem3894717)). Qed.
Lemma lem3894721 : term185 = True.
Proof. exact (TRANS (@lem3894716) (@lem3894720)). Qed.
Lemma lem3894722 : True = term185.
Proof. exact (SYM (@lem3894721)). Qed.
Lemma lem3894723 : term185.
Proof. exact (EQ_MP (@lem3894722) (@lem0)). Qed.
Lemma lem3894724 : term366 = term369.
Proof. exact (@lem3894713 (@lem3894723)). Qed.
Lemma lem3894726 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3894727 : term164 = term169.
Proof. exact (@lem3894726 term79 term79). Qed.
Lemma lem3894728 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894729 : term149 = term79.
Proof. exact (EQ_MP (@lem3894728) (@lem940073)). Qed.
Lemma lem3894730 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894731 : term147 = term78.
Proof. exact (MK_COMB (@lem3894730) (@lem3894729)). Qed.
Lemma lem3894732 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3894733 : term169 = term137.
Proof. exact (MK_COMB (@lem3894732) (@lem3894731)). Qed.
Lemma lem3894734 : term164 = term137.
Proof. exact (TRANS (@lem3894727) (@lem3894733)). Qed.
Lemma lem3894736 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3894737 : term197 = term62.
Proof. exact (@lem3894736 term79). Qed.
Lemma lem3894738 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3894739 : term370 = term64.
Proof. exact (MK_COMB (@lem3894738) (@lem3894737)). Qed.
Lemma lem3894740 : term369 = term364.
Proof. exact (MK_COMB (@lem3894739) (@lem3894734)). Qed.
Lemma lem3894742 (m : nat) (n : nat) : (term371 m n) = (term372 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3894743 : term364 = term373.
Proof. exact (@lem3894742 (NUMERAL 0) term79). Qed.
Lemma lem3894744 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894745 (h1 : term187 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3894746 : (term187 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894745 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem3894744)). Qed.
Lemma lem3894747 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3894746) (@lem3894744)). Qed.
Lemma lem3894748 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3894749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3894750 : term374 = (and True).
Proof. exact (MK_COMB (@lem3894749) (@lem3894748)). Qed.
Lemma lem3894751 : term373 = (True /\ False).
Proof. exact (MK_COMB (@lem3894750) (@lem3894747)). Qed.
Lemma lem3894753 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3894754 : term373 = False.
Proof. exact (TRANS (@lem3894751) (@lem3894753)). Qed.
Lemma lem3894755 : term364 = False.
Proof. exact (TRANS (@lem3894743) (@lem3894754)). Qed.
Lemma lem3894756 : term369 = False.
Proof. exact (TRANS (@lem3894740) (@lem3894755)). Qed.
Lemma lem3894757 : term366 = False.
Proof. exact (TRANS (@lem3894724) (@lem3894756)). Qed.
Lemma lem3894758 : term364 = False.
Proof. exact (TRANS (@lem3894701) (@lem3894757)). Qed.
Lemma lem3894759 : term363 = False.
Proof. exact (TRANS (@lem3894692) (@lem3894758)). Qed.
Lemma lem3894760 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : False.
Proof. exact (EQ_MP (@lem3894759) (@lem3894689 _45282 _45283 h1)). Qed.
Lemma lem3894761 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term375 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3894762 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term321 _45283.
Proof. exact (proj2 (@lem3894761 _45282 _45283 h1)). Qed.
Lemma lem3894764 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term294 _45283.
Proof. exact (proj2 (@lem3894762 _45282 _45283 h1)). Qed.
Lemma lem3894766 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : (term176 _45283) = term62.
Proof. exact (proj2 (@lem3894764 _45282 _45283 h1)). Qed.
Lemma lem3894767 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term222 _45283.
Proof. exact (proj1 (@lem3894764 _45282 _45283 h1)). Qed.
Lemma lem3894769 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3894770 : term332 = term185.
Proof. exact (@lem3894769 term62 term78). Qed.
Lemma lem3894772 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3894773 : term78 = term163.
Proof. exact (@lem3894772 term79). Qed.
Lemma lem3894775 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3894776 : term62 = term134.
Proof. exact (@lem3894775 (NUMERAL 0)). Qed.
Lemma lem3894777 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3894778 : term333 = term334.
Proof. exact (MK_COMB (@lem3894777) (@lem3894776)). Qed.
Lemma lem3894779 : term185 = term335.
Proof. exact (MK_COMB (@lem3894778) (@lem3894773)). Qed.
Lemma lem3894780 : term336.
Proof. exact (@lem1980255 term62 term78 term78 term78). Qed.
Lemma lem3894782 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894783 : term185 = term186.
Proof. exact (@lem3894782 (NUMERAL 0) term79). Qed.
Lemma lem3894784 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894785 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894786 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894785 h1) (fun h1 : term186 = True => @lem3894784)). Qed.
Lemma lem3894787 : term186 = True.
Proof. exact (EQ_MP (@lem3894786) (@lem3894784)). Qed.
Lemma lem3894788 : term185 = True.
Proof. exact (TRANS (@lem3894783) (@lem3894787)). Qed.
Lemma lem3894789 : True = term185.
Proof. exact (SYM (@lem3894788)). Qed.
Lemma lem3894790 : term185.
Proof. exact (EQ_MP (@lem3894789) (@lem0)). Qed.
Lemma lem3894791 : term337.
Proof. exact (@lem3894780 (@lem3894790)). Qed.
Lemma lem3894793 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894794 : term185 = term186.
Proof. exact (@lem3894793 (NUMERAL 0) term79). Qed.
Lemma lem3894795 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894796 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894797 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894796 h1) (fun h1 : term186 = True => @lem3894795)). Qed.
Lemma lem3894798 : term186 = True.
Proof. exact (EQ_MP (@lem3894797) (@lem3894795)). Qed.
Lemma lem3894799 : term185 = True.
Proof. exact (TRANS (@lem3894794) (@lem3894798)). Qed.
Lemma lem3894800 : True = term185.
Proof. exact (SYM (@lem3894799)). Qed.
Lemma lem3894801 : term185.
Proof. exact (EQ_MP (@lem3894800) (@lem0)). Qed.
Lemma lem3894802 : term335 = term338.
Proof. exact (@lem3894791 (@lem3894801)). Qed.
Lemma lem3894804 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3894805 : term146 = term147.
Proof. exact (@lem3894804 term79 term79). Qed.
Lemma lem3894806 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894807 : term149 = term79.
Proof. exact (EQ_MP (@lem3894806) (@lem940073)). Qed.
Lemma lem3894808 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894809 : term147 = term78.
Proof. exact (MK_COMB (@lem3894808) (@lem3894807)). Qed.
Lemma lem3894810 : term146 = term78.
Proof. exact (TRANS (@lem3894805) (@lem3894809)). Qed.
Lemma lem3894812 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3894813 : term197 = term62.
Proof. exact (@lem3894812 term79). Qed.
Lemma lem3894814 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3894815 : term339 = term333.
Proof. exact (MK_COMB (@lem3894814) (@lem3894813)). Qed.
Lemma lem3894816 : term338 = term185.
Proof. exact (MK_COMB (@lem3894815) (@lem3894810)). Qed.
Lemma lem3894818 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894819 : term185 = term186.
Proof. exact (@lem3894818 (NUMERAL 0) term79). Qed.
Lemma lem3894820 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894821 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894822 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894821 h1) (fun h1 : term186 = True => @lem3894820)). Qed.
Lemma lem3894823 : term186 = True.
Proof. exact (EQ_MP (@lem3894822) (@lem3894820)). Qed.
Lemma lem3894824 : term185 = True.
Proof. exact (TRANS (@lem3894819) (@lem3894823)). Qed.
Lemma lem3894825 : term338 = True.
Proof. exact (TRANS (@lem3894816) (@lem3894824)). Qed.
Lemma lem3894826 : term335 = True.
Proof. exact (TRANS (@lem3894802) (@lem3894825)). Qed.
Lemma lem3894827 : term185 = True.
Proof. exact (TRANS (@lem3894779) (@lem3894826)). Qed.
Lemma lem3894828 : term332 = True.
Proof. exact (TRANS (@lem3894770) (@lem3894827)). Qed.
Lemma lem3894829 : True = term332.
Proof. exact (SYM (@lem3894828)). Qed.
Lemma lem3894830 : term332.
Proof. exact (EQ_MP (@lem3894829) (@lem0)). Qed.
Lemma lem3894831 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term376 _45283.
Proof. exact (conj (@lem3894830) (@lem3894767 _45282 _45283 h1)). Qed.
Lemma lem3894833 (x : real) (y : real) : term341 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3894834 (_45283 : int) : term377 _45283.
Proof. exact (@lem3894833 term78 (term173 _45283)). Qed.
Lemma lem3894835 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term378 _45283.
Proof. exact (@lem3894834 _45283 (@lem3894831 _45282 _45283 h1)). Qed.
Lemma lem3894836 (_45283 : int) : (term379 _45283) = (term173 _45283).
Proof. exact (@lem1982733 (term173 _45283)). Qed.
Lemma lem3894837 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3894838 (_45283 : int) : (term380 _45283) = (term221 _45283).
Proof. exact (MK_COMB (@lem3894837) (@lem3894836 _45283)). Qed.
Lemma lem3894839 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3894840 (_45283 : int) : (term378 _45283) = (term222 _45283).
Proof. exact (MK_COMB (@lem3894838 _45283) (@lem3894839)). Qed.
Lemma lem3894841 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term222 _45283.
Proof. exact (EQ_MP (@lem3894840 _45283) (@lem3894835 _45282 _45283 h1)). Qed.
Lemma lem3894843 (y : real) : term346 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3894844 (_45283 : int) : term347 _45283.
Proof. exact (@lem3894843 (term176 _45283)). Qed.
Lemma lem3894845 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term348 _45283.
Proof. exact (@lem3894844 _45283 (@lem3894766 _45282 _45283 h1)). Qed.
Lemma lem3894846 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term381 _45283.
Proof. exact (@lem3894845 _45282 _45283 h1 term137). Qed.
Lemma lem3894847 (_45283 : int) : (term381 _45283) = ((term382 _45283) = term62).
Proof. exact (eq_refl (term381 _45283)). Qed.
Lemma lem3894848 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : (term382 _45283) = term62.
Proof. exact (EQ_MP (@lem3894847 _45283) (@lem3894846 _45282 _45283 h1)). Qed.
Lemma lem3894849 (_45283 : int) : (term382 _45283) = (term383 _45283).
Proof. exact (@lem1982749 term137 term137 (real_of_int _45283)). Qed.
Lemma lem3894851 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3894852 : term137 = term138.
Proof. exact (@lem3894851 term79). Qed.
Lemma lem3894854 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3894855 : term137 = term138.
Proof. exact (@lem3894854 term79). Qed.
Lemma lem3894856 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3894857 : term139 = term140.
Proof. exact (MK_COMB (@lem3894856) (@lem3894855)). Qed.
Lemma lem3894858 : term384 = term385.
Proof. exact (MK_COMB (@lem3894857) (@lem3894852)). Qed.
Lemma lem3894859 : term385 = term386.
Proof. exact (@lem1981613 term137 term137 term78 term78). Qed.
Lemma lem3894861 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3894862 : term146 = term147.
Proof. exact (@lem3894861 term79 term79). Qed.
Lemma lem3894863 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894864 : term149 = term79.
Proof. exact (EQ_MP (@lem3894863) (@lem940073)). Qed.
Lemma lem3894865 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894866 : term147 = term78.
Proof. exact (MK_COMB (@lem3894865) (@lem3894864)). Qed.
Lemma lem3894867 : term146 = term78.
Proof. exact (TRANS (@lem3894862) (@lem3894866)). Qed.
Lemma lem3894869 (m : nat) (n : nat) : (term387 m n) = (term145 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3894870 : term384 = term147.
Proof. exact (@lem3894869 term79 term79). Qed.
Lemma lem3894871 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894872 : term149 = term79.
Proof. exact (EQ_MP (@lem3894871) (@lem940073)). Qed.
Lemma lem3894873 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894874 : term147 = term78.
Proof. exact (MK_COMB (@lem3894873) (@lem3894872)). Qed.
Lemma lem3894875 : term384 = term78.
Proof. exact (TRANS (@lem3894870) (@lem3894874)). Qed.
Lemma lem3894876 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3894877 : term388 = term389.
Proof. exact (MK_COMB (@lem3894876) (@lem3894875)). Qed.
Lemma lem3894878 : term386 = term163.
Proof. exact (MK_COMB (@lem3894877) (@lem3894867)). Qed.
Lemma lem3894879 : term385 = term163.
Proof. exact (TRANS (@lem3894859) (@lem3894878)). Qed.
Lemma lem3894880 : term384 = term163.
Proof. exact (TRANS (@lem3894858) (@lem3894879)). Qed.
Lemma lem3894882 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3894883 : term163 = term78.
Proof. exact (@lem3894882 term78). Qed.
Lemma lem3894884 : term384 = term78.
Proof. exact (TRANS (@lem3894880) (@lem3894883)). Qed.
Lemma lem3894885 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3894886 : term390 = term391.
Proof. exact (MK_COMB (@lem3894885) (@lem3894884)). Qed.
Lemma lem3894887 (_45283 : int) : (real_of_int _45283) = (real_of_int _45283).
Proof. exact (eq_refl (real_of_int _45283)). Qed.
Lemma lem3894888 (_45283 : int) : (term383 _45283) = (term392 _45283).
Proof. exact (MK_COMB (@lem3894886) (@lem3894887 _45283)). Qed.
Lemma lem3894889 (_45283 : int) : (term382 _45283) = (term392 _45283).
Proof. exact (TRANS (@lem3894849 _45283) (@lem3894888 _45283)). Qed.
Lemma lem3894890 (_45283 : int) : (term392 _45283) = (real_of_int _45283).
Proof. exact (@lem1982709 (real_of_int _45283)). Qed.
Lemma lem3894891 (_45283 : int) : (term382 _45283) = (real_of_int _45283).
Proof. exact (TRANS (@lem3894889 _45283) (@lem3894890 _45283)). Qed.
Lemma lem3894892 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3894893 (_45283 : int) : (term393 _45283) = (term120 _45283).
Proof. exact (MK_COMB (@lem3894892) (@lem3894891 _45283)). Qed.
Lemma lem3894894 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3894895 (_45283 : int) : ((term382 _45283) = term62) = ((real_of_int _45283) = term62).
Proof. exact (MK_COMB (@lem3894893 _45283) (@lem3894894)). Qed.
Lemma lem3894896 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : (real_of_int _45283) = term62.
Proof. exact (EQ_MP (@lem3894895 _45283) (@lem3894848 _45282 _45283 h1)). Qed.
Lemma lem3894897 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term394 _45283.
Proof. exact (conj (@lem3894896 _45282 _45283 h1) (@lem3894841 _45282 _45283 h1)). Qed.
Lemma lem3894899 (x : real) (y : real) : term353 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3894900 (_45283 : int) : term395 _45283.
Proof. exact (@lem3894899 (real_of_int _45283) (term173 _45283)). Qed.
Lemma lem3894901 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term396 _45283.
Proof. exact (@lem3894900 _45283 (@lem3894897 _45282 _45283 h1)). Qed.
Lemma lem3894902 (_45283 : int) : (term397 _45283) = (term398 _45283).
Proof. exact (@lem1982763 (real_of_int _45283) (term176 _45283) term137). Qed.
Lemma lem3894903 (_45283 : int) : (term177 _45283) = (term178 _45283).
Proof. exact (@lem1982715 term137 (real_of_int _45283)). Qed.
Lemma lem3894905 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3894906 : term78 = term163.
Proof. exact (@lem3894905 term79). Qed.
Lemma lem3894908 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3894909 : term137 = term138.
Proof. exact (@lem3894908 term79). Qed.
Lemma lem3894910 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3894911 : term179 = term180.
Proof. exact (MK_COMB (@lem3894910) (@lem3894909)). Qed.
Lemma lem3894912 : term181 = term182.
Proof. exact (MK_COMB (@lem3894911) (@lem3894906)). Qed.
Lemma lem3894913 : term183.
Proof. exact (@lem1981473 term137 term78 term78 term78 term62 term78). Qed.
Lemma lem3894915 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894916 : term185 = term186.
Proof. exact (@lem3894915 (NUMERAL 0) term79). Qed.
Lemma lem3894917 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894918 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894919 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894918 h1) (fun h1 : term186 = True => @lem3894917)). Qed.
Lemma lem3894920 : term186 = True.
Proof. exact (EQ_MP (@lem3894919) (@lem3894917)). Qed.
Lemma lem3894921 : term185 = True.
Proof. exact (TRANS (@lem3894916) (@lem3894920)). Qed.
Lemma lem3894922 : True = term185.
Proof. exact (SYM (@lem3894921)). Qed.
Lemma lem3894923 : term185.
Proof. exact (EQ_MP (@lem3894922) (@lem0)). Qed.
Lemma lem3894924 : term188.
Proof. exact (@lem3894913 (@lem3894923)). Qed.
Lemma lem3894926 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894927 : term185 = term186.
Proof. exact (@lem3894926 (NUMERAL 0) term79). Qed.
Lemma lem3894928 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894929 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894930 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894929 h1) (fun h1 : term186 = True => @lem3894928)). Qed.
Lemma lem3894931 : term186 = True.
Proof. exact (EQ_MP (@lem3894930) (@lem3894928)). Qed.
Lemma lem3894932 : term185 = True.
Proof. exact (TRANS (@lem3894927) (@lem3894931)). Qed.
Lemma lem3894933 : True = term185.
Proof. exact (SYM (@lem3894932)). Qed.
Lemma lem3894934 : term185.
Proof. exact (EQ_MP (@lem3894933) (@lem0)). Qed.
Lemma lem3894935 : term189.
Proof. exact (@lem3894924 (@lem3894934)). Qed.
Lemma lem3894937 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3894938 : term185 = term186.
Proof. exact (@lem3894937 (NUMERAL 0) term79). Qed.
Lemma lem3894939 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3894940 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3894941 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3894940 h1) (fun h1 : term186 = True => @lem3894939)). Qed.
Lemma lem3894942 : term186 = True.
Proof. exact (EQ_MP (@lem3894941) (@lem3894939)). Qed.
Lemma lem3894943 : term185 = True.
Proof. exact (TRANS (@lem3894938) (@lem3894942)). Qed.
Lemma lem3894944 : True = term185.
Proof. exact (SYM (@lem3894943)). Qed.
Lemma lem3894945 : term185.
Proof. exact (EQ_MP (@lem3894944) (@lem0)). Qed.
Lemma lem3894946 : term190.
Proof. exact (@lem3894935 (@lem3894945)). Qed.
Lemma lem3894948 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3894949 : term146 = term147.
Proof. exact (@lem3894948 term79 term79). Qed.
Lemma lem3894950 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894951 : term149 = term79.
Proof. exact (EQ_MP (@lem3894950) (@lem940073)). Qed.
Lemma lem3894952 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894953 : term147 = term78.
Proof. exact (MK_COMB (@lem3894952) (@lem3894951)). Qed.
Lemma lem3894954 : term146 = term78.
Proof. exact (TRANS (@lem3894949) (@lem3894953)). Qed.
Lemma lem3894956 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3894957 : term164 = term169.
Proof. exact (@lem3894956 term79 term79). Qed.
Lemma lem3894958 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894959 : term149 = term79.
Proof. exact (EQ_MP (@lem3894958) (@lem940073)). Qed.
Lemma lem3894960 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894961 : term147 = term78.
Proof. exact (MK_COMB (@lem3894960) (@lem3894959)). Qed.
Lemma lem3894962 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3894963 : term169 = term137.
Proof. exact (MK_COMB (@lem3894962) (@lem3894961)). Qed.
Lemma lem3894964 : term164 = term137.
Proof. exact (TRANS (@lem3894957) (@lem3894963)). Qed.
Lemma lem3894965 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3894966 : term191 = term179.
Proof. exact (MK_COMB (@lem3894965) (@lem3894964)). Qed.
Lemma lem3894967 : term192 = term181.
Proof. exact (MK_COMB (@lem3894966) (@lem3894954)). Qed.
Lemma lem3894969 (m : nat) : (term193 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3894970 : term181 = term62.
Proof. exact (@lem3894969 term79). Qed.
Lemma lem3894971 : term192 = term62.
Proof. exact (TRANS (@lem3894967) (@lem3894970)). Qed.
Lemma lem3894972 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3894973 : term194 = term195.
Proof. exact (MK_COMB (@lem3894972) (@lem3894971)). Qed.
Lemma lem3894974 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem3894975 : term196 = term197.
Proof. exact (MK_COMB (@lem3894973) (@lem3894974)). Qed.
Lemma lem3894977 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3894978 : term197 = term62.
Proof. exact (@lem3894977 term79). Qed.
Lemma lem3894979 : term196 = term62.
Proof. exact (TRANS (@lem3894975) (@lem3894978)). Qed.
Lemma lem3894981 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3894982 : term146 = term147.
Proof. exact (@lem3894981 term79 term79). Qed.
Lemma lem3894983 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3894984 : term149 = term79.
Proof. exact (EQ_MP (@lem3894983) (@lem940073)). Qed.
Lemma lem3894985 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3894986 : term147 = term78.
Proof. exact (MK_COMB (@lem3894985) (@lem3894984)). Qed.
Lemma lem3894987 : term146 = term78.
Proof. exact (TRANS (@lem3894982) (@lem3894986)). Qed.
Lemma lem3894988 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem3894989 : term199 = term197.
Proof. exact (MK_COMB (@lem3894988) (@lem3894987)). Qed.
Lemma lem3894991 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3894992 : term197 = term62.
Proof. exact (@lem3894991 term79). Qed.
Lemma lem3894993 : term199 = term62.
Proof. exact (TRANS (@lem3894989) (@lem3894992)). Qed.
Lemma lem3894994 : term62 = term199.
Proof. exact (SYM (@lem3894993)). Qed.
Lemma lem3894995 : term196 = term199.
Proof. exact (TRANS (@lem3894979) (@lem3894994)). Qed.
Lemma lem3894996 : term182 = term134.
Proof. exact (@lem3894946 (@lem3894995)). Qed.
Lemma lem3894997 : term181 = term134.
Proof. exact (TRANS (@lem3894912) (@lem3894996)). Qed.
Lemma lem3894999 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3895000 : term134 = term62.
Proof. exact (@lem3894999 term62). Qed.
Lemma lem3895001 : term181 = term62.
Proof. exact (TRANS (@lem3894997) (@lem3895000)). Qed.
Lemma lem3895002 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3895003 : term200 = term195.
Proof. exact (MK_COMB (@lem3895002) (@lem3895001)). Qed.
Lemma lem3895004 (_45283 : int) : (real_of_int _45283) = (real_of_int _45283).
Proof. exact (eq_refl (real_of_int _45283)). Qed.
Lemma lem3895005 (_45283 : int) : (term178 _45283) = (term201 _45283).
Proof. exact (MK_COMB (@lem3895003) (@lem3895004 _45283)). Qed.
Lemma lem3895006 (_45283 : int) : (term177 _45283) = (term201 _45283).
Proof. exact (TRANS (@lem3894903 _45283) (@lem3895005 _45283)). Qed.
Lemma lem3895007 (_45283 : int) : (term201 _45283) = term62.
Proof. exact (@lem1982719 (real_of_int _45283)). Qed.
Lemma lem3895008 (_45283 : int) : (term177 _45283) = term62.
Proof. exact (TRANS (@lem3895006 _45283) (@lem3895007 _45283)). Qed.
Lemma lem3895009 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3895010 (_45283 : int) : (term202 _45283) = term111.
Proof. exact (MK_COMB (@lem3895009) (@lem3895008 _45283)). Qed.
Lemma lem3895011 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem3895012 (_45283 : int) : (term398 _45283) = term360.
Proof. exact (MK_COMB (@lem3895010 _45283) (@lem3895011)). Qed.
Lemma lem3895013 (_45283 : int) : (term397 _45283) = term360.
Proof. exact (TRANS (@lem3894902 _45283) (@lem3895012 _45283)). Qed.
Lemma lem3895014 : term360 = term137.
Proof. exact (@lem1982721 term137). Qed.
Lemma lem3895015 (_45283 : int) : (term397 _45283) = term137.
Proof. exact (TRANS (@lem3895013 _45283) (@lem3895014)). Qed.
Lemma lem3895016 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3895017 (_45283 : int) : (term399 _45283) = term362.
Proof. exact (MK_COMB (@lem3895016) (@lem3895015 _45283)). Qed.
Lemma lem3895018 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3895019 (_45283 : int) : (term396 _45283) = term363.
Proof. exact (MK_COMB (@lem3895017 _45283) (@lem3895018)). Qed.
Lemma lem3895020 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term363.
Proof. exact (EQ_MP (@lem3895019 _45283) (@lem3894901 _45282 _45283 h1)). Qed.
Lemma lem3895022 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3895023 : term363 = term364.
Proof. exact (@lem3895022 term62 term137). Qed.
Lemma lem3895025 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3895026 : term137 = term138.
Proof. exact (@lem3895025 term79). Qed.
Lemma lem3895028 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895029 : term62 = term134.
Proof. exact (@lem3895028 (NUMERAL 0)). Qed.
Lemma lem3895030 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3895031 : term64 = term365.
Proof. exact (MK_COMB (@lem3895030) (@lem3895029)). Qed.
Lemma lem3895032 : term364 = term366.
Proof. exact (MK_COMB (@lem3895031) (@lem3895026)). Qed.
Lemma lem3895033 : term367.
Proof. exact (@lem1980026 term62 term78 term137 term78). Qed.
Lemma lem3895035 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895036 : term185 = term186.
Proof. exact (@lem3895035 (NUMERAL 0) term79). Qed.
Lemma lem3895037 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895038 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895039 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895038 h1) (fun h1 : term186 = True => @lem3895037)). Qed.
Lemma lem3895040 : term186 = True.
Proof. exact (EQ_MP (@lem3895039) (@lem3895037)). Qed.
Lemma lem3895041 : term185 = True.
Proof. exact (TRANS (@lem3895036) (@lem3895040)). Qed.
Lemma lem3895042 : True = term185.
Proof. exact (SYM (@lem3895041)). Qed.
Lemma lem3895043 : term185.
Proof. exact (EQ_MP (@lem3895042) (@lem0)). Qed.
Lemma lem3895044 : term368.
Proof. exact (@lem3895033 (@lem3895043)). Qed.
Lemma lem3895046 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895047 : term185 = term186.
Proof. exact (@lem3895046 (NUMERAL 0) term79). Qed.
Lemma lem3895048 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895049 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895050 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895049 h1) (fun h1 : term186 = True => @lem3895048)). Qed.
Lemma lem3895051 : term186 = True.
Proof. exact (EQ_MP (@lem3895050) (@lem3895048)). Qed.
Lemma lem3895052 : term185 = True.
Proof. exact (TRANS (@lem3895047) (@lem3895051)). Qed.
Lemma lem3895053 : True = term185.
Proof. exact (SYM (@lem3895052)). Qed.
Lemma lem3895054 : term185.
Proof. exact (EQ_MP (@lem3895053) (@lem0)). Qed.
Lemma lem3895055 : term366 = term369.
Proof. exact (@lem3895044 (@lem3895054)). Qed.
Lemma lem3895057 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3895058 : term164 = term169.
Proof. exact (@lem3895057 term79 term79). Qed.
Lemma lem3895059 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895060 : term149 = term79.
Proof. exact (EQ_MP (@lem3895059) (@lem940073)). Qed.
Lemma lem3895061 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895062 : term147 = term78.
Proof. exact (MK_COMB (@lem3895061) (@lem3895060)). Qed.
Lemma lem3895063 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3895064 : term169 = term137.
Proof. exact (MK_COMB (@lem3895063) (@lem3895062)). Qed.
Lemma lem3895065 : term164 = term137.
Proof. exact (TRANS (@lem3895058) (@lem3895064)). Qed.
Lemma lem3895067 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895068 : term197 = term62.
Proof. exact (@lem3895067 term79). Qed.
Lemma lem3895069 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3895070 : term370 = term64.
Proof. exact (MK_COMB (@lem3895069) (@lem3895068)). Qed.
Lemma lem3895071 : term369 = term364.
Proof. exact (MK_COMB (@lem3895070) (@lem3895065)). Qed.
Lemma lem3895073 (m : nat) (n : nat) : (term371 m n) = (term372 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3895074 : term364 = term373.
Proof. exact (@lem3895073 (NUMERAL 0) term79). Qed.
Lemma lem3895075 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895076 (h1 : term187 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3895077 : (term187 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895076 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem3895075)). Qed.
Lemma lem3895078 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3895077) (@lem3895075)). Qed.
Lemma lem3895079 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3895080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3895081 : term374 = (and True).
Proof. exact (MK_COMB (@lem3895080) (@lem3895079)). Qed.
Lemma lem3895082 : term373 = (True /\ False).
Proof. exact (MK_COMB (@lem3895081) (@lem3895078)). Qed.
Lemma lem3895084 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3895085 : term373 = False.
Proof. exact (TRANS (@lem3895082) (@lem3895084)). Qed.
Lemma lem3895086 : term364 = False.
Proof. exact (TRANS (@lem3895074) (@lem3895085)). Qed.
Lemma lem3895087 : term369 = False.
Proof. exact (TRANS (@lem3895071) (@lem3895086)). Qed.
Lemma lem3895088 : term366 = False.
Proof. exact (TRANS (@lem3895055) (@lem3895087)). Qed.
Lemma lem3895089 : term364 = False.
Proof. exact (TRANS (@lem3895032) (@lem3895088)). Qed.
Lemma lem3895090 : term363 = False.
Proof. exact (TRANS (@lem3895023) (@lem3895089)). Qed.
Lemma lem3895091 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : False.
Proof. exact (EQ_MP (@lem3895090) (@lem3895020 _45282 _45283 h1)). Qed.
Lemma lem3895092 (_45282 : int) (_45283 : int) (h1 : term324 _45282 _45283) : False.
Proof. exact (or_elim (@lem3894471 _45282 _45283 h1) (fun h0 : term331 _45282 _45283 => @lem3894760 _45282 _45283 h0) (fun h0 : term375 _45282 _45283 => @lem3895091 _45282 _45283 h0)). Qed.
Lemma lem3895093 (_45282 : int) (_45283 : int) (h1 : term320 _45282 _45283) : term320 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3895094 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term375 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3895095 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term321 _45283.
Proof. exact (proj2 (@lem3895094 _45282 _45283 h1)). Qed.
Lemma lem3895097 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term294 _45283.
Proof. exact (proj2 (@lem3895095 _45282 _45283 h1)). Qed.
Lemma lem3895099 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : (term176 _45283) = term62.
Proof. exact (proj2 (@lem3895097 _45282 _45283 h1)). Qed.
Lemma lem3895100 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term222 _45283.
Proof. exact (proj1 (@lem3895097 _45282 _45283 h1)). Qed.
Lemma lem3895102 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3895103 : term332 = term185.
Proof. exact (@lem3895102 term62 term78). Qed.
Lemma lem3895105 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895106 : term78 = term163.
Proof. exact (@lem3895105 term79). Qed.
Lemma lem3895108 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895109 : term62 = term134.
Proof. exact (@lem3895108 (NUMERAL 0)). Qed.
Lemma lem3895110 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3895111 : term333 = term334.
Proof. exact (MK_COMB (@lem3895110) (@lem3895109)). Qed.
Lemma lem3895112 : term185 = term335.
Proof. exact (MK_COMB (@lem3895111) (@lem3895106)). Qed.
Lemma lem3895113 : term336.
Proof. exact (@lem1980255 term62 term78 term78 term78). Qed.
Lemma lem3895115 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895116 : term185 = term186.
Proof. exact (@lem3895115 (NUMERAL 0) term79). Qed.
Lemma lem3895117 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895118 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895119 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895118 h1) (fun h1 : term186 = True => @lem3895117)). Qed.
Lemma lem3895120 : term186 = True.
Proof. exact (EQ_MP (@lem3895119) (@lem3895117)). Qed.
Lemma lem3895121 : term185 = True.
Proof. exact (TRANS (@lem3895116) (@lem3895120)). Qed.
Lemma lem3895122 : True = term185.
Proof. exact (SYM (@lem3895121)). Qed.
Lemma lem3895123 : term185.
Proof. exact (EQ_MP (@lem3895122) (@lem0)). Qed.
Lemma lem3895124 : term337.
Proof. exact (@lem3895113 (@lem3895123)). Qed.
Lemma lem3895126 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895127 : term185 = term186.
Proof. exact (@lem3895126 (NUMERAL 0) term79). Qed.
Lemma lem3895128 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895129 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895130 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895129 h1) (fun h1 : term186 = True => @lem3895128)). Qed.
Lemma lem3895131 : term186 = True.
Proof. exact (EQ_MP (@lem3895130) (@lem3895128)). Qed.
Lemma lem3895132 : term185 = True.
Proof. exact (TRANS (@lem3895127) (@lem3895131)). Qed.
Lemma lem3895133 : True = term185.
Proof. exact (SYM (@lem3895132)). Qed.
Lemma lem3895134 : term185.
Proof. exact (EQ_MP (@lem3895133) (@lem0)). Qed.
Lemma lem3895135 : term335 = term338.
Proof. exact (@lem3895124 (@lem3895134)). Qed.
Lemma lem3895137 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3895138 : term146 = term147.
Proof. exact (@lem3895137 term79 term79). Qed.
Lemma lem3895139 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895140 : term149 = term79.
Proof. exact (EQ_MP (@lem3895139) (@lem940073)). Qed.
Lemma lem3895141 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895142 : term147 = term78.
Proof. exact (MK_COMB (@lem3895141) (@lem3895140)). Qed.
Lemma lem3895143 : term146 = term78.
Proof. exact (TRANS (@lem3895138) (@lem3895142)). Qed.
Lemma lem3895145 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895146 : term197 = term62.
Proof. exact (@lem3895145 term79). Qed.
Lemma lem3895147 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3895148 : term339 = term333.
Proof. exact (MK_COMB (@lem3895147) (@lem3895146)). Qed.
Lemma lem3895149 : term338 = term185.
Proof. exact (MK_COMB (@lem3895148) (@lem3895143)). Qed.
Lemma lem3895151 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895152 : term185 = term186.
Proof. exact (@lem3895151 (NUMERAL 0) term79). Qed.
Lemma lem3895153 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895154 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895155 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895154 h1) (fun h1 : term186 = True => @lem3895153)). Qed.
Lemma lem3895156 : term186 = True.
Proof. exact (EQ_MP (@lem3895155) (@lem3895153)). Qed.
Lemma lem3895157 : term185 = True.
Proof. exact (TRANS (@lem3895152) (@lem3895156)). Qed.
Lemma lem3895158 : term338 = True.
Proof. exact (TRANS (@lem3895149) (@lem3895157)). Qed.
Lemma lem3895159 : term335 = True.
Proof. exact (TRANS (@lem3895135) (@lem3895158)). Qed.
Lemma lem3895160 : term185 = True.
Proof. exact (TRANS (@lem3895112) (@lem3895159)). Qed.
Lemma lem3895161 : term332 = True.
Proof. exact (TRANS (@lem3895103) (@lem3895160)). Qed.
Lemma lem3895162 : True = term332.
Proof. exact (SYM (@lem3895161)). Qed.
Lemma lem3895163 : term332.
Proof. exact (EQ_MP (@lem3895162) (@lem0)). Qed.
Lemma lem3895164 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term376 _45283.
Proof. exact (conj (@lem3895163) (@lem3895100 _45282 _45283 h1)). Qed.
Lemma lem3895166 (x : real) (y : real) : term341 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3895167 (_45283 : int) : term377 _45283.
Proof. exact (@lem3895166 term78 (term173 _45283)). Qed.
Lemma lem3895168 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term378 _45283.
Proof. exact (@lem3895167 _45283 (@lem3895164 _45282 _45283 h1)). Qed.
Lemma lem3895169 (_45283 : int) : (term379 _45283) = (term173 _45283).
Proof. exact (@lem1982733 (term173 _45283)). Qed.
Lemma lem3895170 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3895171 (_45283 : int) : (term380 _45283) = (term221 _45283).
Proof. exact (MK_COMB (@lem3895170) (@lem3895169 _45283)). Qed.
Lemma lem3895172 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3895173 (_45283 : int) : (term378 _45283) = (term222 _45283).
Proof. exact (MK_COMB (@lem3895171 _45283) (@lem3895172)). Qed.
Lemma lem3895174 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term222 _45283.
Proof. exact (EQ_MP (@lem3895173 _45283) (@lem3895168 _45282 _45283 h1)). Qed.
Lemma lem3895176 (y : real) : term346 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3895177 (_45283 : int) : term347 _45283.
Proof. exact (@lem3895176 (term176 _45283)). Qed.
Lemma lem3895178 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term348 _45283.
Proof. exact (@lem3895177 _45283 (@lem3895099 _45282 _45283 h1)). Qed.
Lemma lem3895179 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term381 _45283.
Proof. exact (@lem3895178 _45282 _45283 h1 term137). Qed.
Lemma lem3895180 (_45283 : int) : (term381 _45283) = ((term382 _45283) = term62).
Proof. exact (eq_refl (term381 _45283)). Qed.
Lemma lem3895181 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : (term382 _45283) = term62.
Proof. exact (EQ_MP (@lem3895180 _45283) (@lem3895179 _45282 _45283 h1)). Qed.
Lemma lem3895182 (_45283 : int) : (term382 _45283) = (term383 _45283).
Proof. exact (@lem1982749 term137 term137 (real_of_int _45283)). Qed.
Lemma lem3895184 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3895185 : term137 = term138.
Proof. exact (@lem3895184 term79). Qed.
Lemma lem3895187 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3895188 : term137 = term138.
Proof. exact (@lem3895187 term79). Qed.
Lemma lem3895189 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3895190 : term139 = term140.
Proof. exact (MK_COMB (@lem3895189) (@lem3895188)). Qed.
Lemma lem3895191 : term384 = term385.
Proof. exact (MK_COMB (@lem3895190) (@lem3895185)). Qed.
Lemma lem3895192 : term385 = term386.
Proof. exact (@lem1981613 term137 term137 term78 term78). Qed.
Lemma lem3895194 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3895195 : term146 = term147.
Proof. exact (@lem3895194 term79 term79). Qed.
Lemma lem3895196 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895197 : term149 = term79.
Proof. exact (EQ_MP (@lem3895196) (@lem940073)). Qed.
Lemma lem3895198 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895199 : term147 = term78.
Proof. exact (MK_COMB (@lem3895198) (@lem3895197)). Qed.
Lemma lem3895200 : term146 = term78.
Proof. exact (TRANS (@lem3895195) (@lem3895199)). Qed.
Lemma lem3895202 (m : nat) (n : nat) : (term387 m n) = (term145 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3895203 : term384 = term147.
Proof. exact (@lem3895202 term79 term79). Qed.
Lemma lem3895204 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895205 : term149 = term79.
Proof. exact (EQ_MP (@lem3895204) (@lem940073)). Qed.
Lemma lem3895206 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895207 : term147 = term78.
Proof. exact (MK_COMB (@lem3895206) (@lem3895205)). Qed.
Lemma lem3895208 : term384 = term78.
Proof. exact (TRANS (@lem3895203) (@lem3895207)). Qed.
Lemma lem3895209 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3895210 : term388 = term389.
Proof. exact (MK_COMB (@lem3895209) (@lem3895208)). Qed.
Lemma lem3895211 : term386 = term163.
Proof. exact (MK_COMB (@lem3895210) (@lem3895200)). Qed.
Lemma lem3895212 : term385 = term163.
Proof. exact (TRANS (@lem3895192) (@lem3895211)). Qed.
Lemma lem3895213 : term384 = term163.
Proof. exact (TRANS (@lem3895191) (@lem3895212)). Qed.
Lemma lem3895215 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3895216 : term163 = term78.
Proof. exact (@lem3895215 term78). Qed.
Lemma lem3895217 : term384 = term78.
Proof. exact (TRANS (@lem3895213) (@lem3895216)). Qed.
Lemma lem3895218 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3895219 : term390 = term391.
Proof. exact (MK_COMB (@lem3895218) (@lem3895217)). Qed.
Lemma lem3895220 (_45283 : int) : (real_of_int _45283) = (real_of_int _45283).
Proof. exact (eq_refl (real_of_int _45283)). Qed.
Lemma lem3895221 (_45283 : int) : (term383 _45283) = (term392 _45283).
Proof. exact (MK_COMB (@lem3895219) (@lem3895220 _45283)). Qed.
Lemma lem3895222 (_45283 : int) : (term382 _45283) = (term392 _45283).
Proof. exact (TRANS (@lem3895182 _45283) (@lem3895221 _45283)). Qed.
Lemma lem3895223 (_45283 : int) : (term392 _45283) = (real_of_int _45283).
Proof. exact (@lem1982709 (real_of_int _45283)). Qed.
Lemma lem3895224 (_45283 : int) : (term382 _45283) = (real_of_int _45283).
Proof. exact (TRANS (@lem3895222 _45283) (@lem3895223 _45283)). Qed.
Lemma lem3895225 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3895226 (_45283 : int) : (term393 _45283) = (term120 _45283).
Proof. exact (MK_COMB (@lem3895225) (@lem3895224 _45283)). Qed.
Lemma lem3895227 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3895228 (_45283 : int) : ((term382 _45283) = term62) = ((real_of_int _45283) = term62).
Proof. exact (MK_COMB (@lem3895226 _45283) (@lem3895227)). Qed.
Lemma lem3895229 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : (real_of_int _45283) = term62.
Proof. exact (EQ_MP (@lem3895228 _45283) (@lem3895181 _45282 _45283 h1)). Qed.
Lemma lem3895230 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term394 _45283.
Proof. exact (conj (@lem3895229 _45282 _45283 h1) (@lem3895174 _45282 _45283 h1)). Qed.
Lemma lem3895232 (x : real) (y : real) : term353 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3895233 (_45283 : int) : term395 _45283.
Proof. exact (@lem3895232 (real_of_int _45283) (term173 _45283)). Qed.
Lemma lem3895234 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term396 _45283.
Proof. exact (@lem3895233 _45283 (@lem3895230 _45282 _45283 h1)). Qed.
Lemma lem3895235 (_45283 : int) : (term397 _45283) = (term398 _45283).
Proof. exact (@lem1982763 (real_of_int _45283) (term176 _45283) term137). Qed.
Lemma lem3895236 (_45283 : int) : (term177 _45283) = (term178 _45283).
Proof. exact (@lem1982715 term137 (real_of_int _45283)). Qed.
Lemma lem3895238 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895239 : term78 = term163.
Proof. exact (@lem3895238 term79). Qed.
Lemma lem3895241 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3895242 : term137 = term138.
Proof. exact (@lem3895241 term79). Qed.
Lemma lem3895243 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3895244 : term179 = term180.
Proof. exact (MK_COMB (@lem3895243) (@lem3895242)). Qed.
Lemma lem3895245 : term181 = term182.
Proof. exact (MK_COMB (@lem3895244) (@lem3895239)). Qed.
Lemma lem3895246 : term183.
Proof. exact (@lem1981473 term137 term78 term78 term78 term62 term78). Qed.
Lemma lem3895248 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895249 : term185 = term186.
Proof. exact (@lem3895248 (NUMERAL 0) term79). Qed.
Lemma lem3895250 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895251 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895252 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895251 h1) (fun h1 : term186 = True => @lem3895250)). Qed.
Lemma lem3895253 : term186 = True.
Proof. exact (EQ_MP (@lem3895252) (@lem3895250)). Qed.
Lemma lem3895254 : term185 = True.
Proof. exact (TRANS (@lem3895249) (@lem3895253)). Qed.
Lemma lem3895255 : True = term185.
Proof. exact (SYM (@lem3895254)). Qed.
Lemma lem3895256 : term185.
Proof. exact (EQ_MP (@lem3895255) (@lem0)). Qed.
Lemma lem3895257 : term188.
Proof. exact (@lem3895246 (@lem3895256)). Qed.
Lemma lem3895259 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895260 : term185 = term186.
Proof. exact (@lem3895259 (NUMERAL 0) term79). Qed.
Lemma lem3895261 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895262 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895263 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895262 h1) (fun h1 : term186 = True => @lem3895261)). Qed.
Lemma lem3895264 : term186 = True.
Proof. exact (EQ_MP (@lem3895263) (@lem3895261)). Qed.
Lemma lem3895265 : term185 = True.
Proof. exact (TRANS (@lem3895260) (@lem3895264)). Qed.
Lemma lem3895266 : True = term185.
Proof. exact (SYM (@lem3895265)). Qed.
Lemma lem3895267 : term185.
Proof. exact (EQ_MP (@lem3895266) (@lem0)). Qed.
Lemma lem3895268 : term189.
Proof. exact (@lem3895257 (@lem3895267)). Qed.
Lemma lem3895270 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895271 : term185 = term186.
Proof. exact (@lem3895270 (NUMERAL 0) term79). Qed.
Lemma lem3895272 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895273 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895274 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895273 h1) (fun h1 : term186 = True => @lem3895272)). Qed.
Lemma lem3895275 : term186 = True.
Proof. exact (EQ_MP (@lem3895274) (@lem3895272)). Qed.
Lemma lem3895276 : term185 = True.
Proof. exact (TRANS (@lem3895271) (@lem3895275)). Qed.
Lemma lem3895277 : True = term185.
Proof. exact (SYM (@lem3895276)). Qed.
Lemma lem3895278 : term185.
Proof. exact (EQ_MP (@lem3895277) (@lem0)). Qed.
Lemma lem3895279 : term190.
Proof. exact (@lem3895268 (@lem3895278)). Qed.
Lemma lem3895281 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3895282 : term146 = term147.
Proof. exact (@lem3895281 term79 term79). Qed.
Lemma lem3895283 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895284 : term149 = term79.
Proof. exact (EQ_MP (@lem3895283) (@lem940073)). Qed.
Lemma lem3895285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895286 : term147 = term78.
Proof. exact (MK_COMB (@lem3895285) (@lem3895284)). Qed.
Lemma lem3895287 : term146 = term78.
Proof. exact (TRANS (@lem3895282) (@lem3895286)). Qed.
Lemma lem3895289 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3895290 : term164 = term169.
Proof. exact (@lem3895289 term79 term79). Qed.
Lemma lem3895291 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895292 : term149 = term79.
Proof. exact (EQ_MP (@lem3895291) (@lem940073)). Qed.
Lemma lem3895293 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895294 : term147 = term78.
Proof. exact (MK_COMB (@lem3895293) (@lem3895292)). Qed.
Lemma lem3895295 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3895296 : term169 = term137.
Proof. exact (MK_COMB (@lem3895295) (@lem3895294)). Qed.
Lemma lem3895297 : term164 = term137.
Proof. exact (TRANS (@lem3895290) (@lem3895296)). Qed.
Lemma lem3895298 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3895299 : term191 = term179.
Proof. exact (MK_COMB (@lem3895298) (@lem3895297)). Qed.
Lemma lem3895300 : term192 = term181.
Proof. exact (MK_COMB (@lem3895299) (@lem3895287)). Qed.
Lemma lem3895302 (m : nat) : (term193 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3895303 : term181 = term62.
Proof. exact (@lem3895302 term79). Qed.
Lemma lem3895304 : term192 = term62.
Proof. exact (TRANS (@lem3895300) (@lem3895303)). Qed.
Lemma lem3895305 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3895306 : term194 = term195.
Proof. exact (MK_COMB (@lem3895305) (@lem3895304)). Qed.
Lemma lem3895307 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem3895308 : term196 = term197.
Proof. exact (MK_COMB (@lem3895306) (@lem3895307)). Qed.
Lemma lem3895310 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895311 : term197 = term62.
Proof. exact (@lem3895310 term79). Qed.
Lemma lem3895312 : term196 = term62.
Proof. exact (TRANS (@lem3895308) (@lem3895311)). Qed.
Lemma lem3895314 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3895315 : term146 = term147.
Proof. exact (@lem3895314 term79 term79). Qed.
Lemma lem3895316 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895317 : term149 = term79.
Proof. exact (EQ_MP (@lem3895316) (@lem940073)). Qed.
Lemma lem3895318 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895319 : term147 = term78.
Proof. exact (MK_COMB (@lem3895318) (@lem3895317)). Qed.
Lemma lem3895320 : term146 = term78.
Proof. exact (TRANS (@lem3895315) (@lem3895319)). Qed.
Lemma lem3895321 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem3895322 : term199 = term197.
Proof. exact (MK_COMB (@lem3895321) (@lem3895320)). Qed.
Lemma lem3895324 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895325 : term197 = term62.
Proof. exact (@lem3895324 term79). Qed.
Lemma lem3895326 : term199 = term62.
Proof. exact (TRANS (@lem3895322) (@lem3895325)). Qed.
Lemma lem3895327 : term62 = term199.
Proof. exact (SYM (@lem3895326)). Qed.
Lemma lem3895328 : term196 = term199.
Proof. exact (TRANS (@lem3895312) (@lem3895327)). Qed.
Lemma lem3895329 : term182 = term134.
Proof. exact (@lem3895279 (@lem3895328)). Qed.
Lemma lem3895330 : term181 = term134.
Proof. exact (TRANS (@lem3895245) (@lem3895329)). Qed.
Lemma lem3895332 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3895333 : term134 = term62.
Proof. exact (@lem3895332 term62). Qed.
Lemma lem3895334 : term181 = term62.
Proof. exact (TRANS (@lem3895330) (@lem3895333)). Qed.
Lemma lem3895335 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3895336 : term200 = term195.
Proof. exact (MK_COMB (@lem3895335) (@lem3895334)). Qed.
Lemma lem3895337 (_45283 : int) : (real_of_int _45283) = (real_of_int _45283).
Proof. exact (eq_refl (real_of_int _45283)). Qed.
Lemma lem3895338 (_45283 : int) : (term178 _45283) = (term201 _45283).
Proof. exact (MK_COMB (@lem3895336) (@lem3895337 _45283)). Qed.
Lemma lem3895339 (_45283 : int) : (term177 _45283) = (term201 _45283).
Proof. exact (TRANS (@lem3895236 _45283) (@lem3895338 _45283)). Qed.
Lemma lem3895340 (_45283 : int) : (term201 _45283) = term62.
Proof. exact (@lem1982719 (real_of_int _45283)). Qed.
Lemma lem3895341 (_45283 : int) : (term177 _45283) = term62.
Proof. exact (TRANS (@lem3895339 _45283) (@lem3895340 _45283)). Qed.
Lemma lem3895342 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3895343 (_45283 : int) : (term202 _45283) = term111.
Proof. exact (MK_COMB (@lem3895342) (@lem3895341 _45283)). Qed.
Lemma lem3895344 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem3895345 (_45283 : int) : (term398 _45283) = term360.
Proof. exact (MK_COMB (@lem3895343 _45283) (@lem3895344)). Qed.
Lemma lem3895346 (_45283 : int) : (term397 _45283) = term360.
Proof. exact (TRANS (@lem3895235 _45283) (@lem3895345 _45283)). Qed.
Lemma lem3895347 : term360 = term137.
Proof. exact (@lem1982721 term137). Qed.
Lemma lem3895348 (_45283 : int) : (term397 _45283) = term137.
Proof. exact (TRANS (@lem3895346 _45283) (@lem3895347)). Qed.
Lemma lem3895349 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3895350 (_45283 : int) : (term399 _45283) = term362.
Proof. exact (MK_COMB (@lem3895349) (@lem3895348 _45283)). Qed.
Lemma lem3895351 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3895352 (_45283 : int) : (term396 _45283) = term363.
Proof. exact (MK_COMB (@lem3895350 _45283) (@lem3895351)). Qed.
Lemma lem3895353 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : term363.
Proof. exact (EQ_MP (@lem3895352 _45283) (@lem3895234 _45282 _45283 h1)). Qed.
Lemma lem3895355 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3895356 : term363 = term364.
Proof. exact (@lem3895355 term62 term137). Qed.
Lemma lem3895358 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3895359 : term137 = term138.
Proof. exact (@lem3895358 term79). Qed.
Lemma lem3895361 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895362 : term62 = term134.
Proof. exact (@lem3895361 (NUMERAL 0)). Qed.
Lemma lem3895363 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3895364 : term64 = term365.
Proof. exact (MK_COMB (@lem3895363) (@lem3895362)). Qed.
Lemma lem3895365 : term364 = term366.
Proof. exact (MK_COMB (@lem3895364) (@lem3895359)). Qed.
Lemma lem3895366 : term367.
Proof. exact (@lem1980026 term62 term78 term137 term78). Qed.
Lemma lem3895368 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895369 : term185 = term186.
Proof. exact (@lem3895368 (NUMERAL 0) term79). Qed.
Lemma lem3895370 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895371 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895372 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895371 h1) (fun h1 : term186 = True => @lem3895370)). Qed.
Lemma lem3895373 : term186 = True.
Proof. exact (EQ_MP (@lem3895372) (@lem3895370)). Qed.
Lemma lem3895374 : term185 = True.
Proof. exact (TRANS (@lem3895369) (@lem3895373)). Qed.
Lemma lem3895375 : True = term185.
Proof. exact (SYM (@lem3895374)). Qed.
Lemma lem3895376 : term185.
Proof. exact (EQ_MP (@lem3895375) (@lem0)). Qed.
Lemma lem3895377 : term368.
Proof. exact (@lem3895366 (@lem3895376)). Qed.
Lemma lem3895379 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895380 : term185 = term186.
Proof. exact (@lem3895379 (NUMERAL 0) term79). Qed.
Lemma lem3895381 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895382 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895383 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895382 h1) (fun h1 : term186 = True => @lem3895381)). Qed.
Lemma lem3895384 : term186 = True.
Proof. exact (EQ_MP (@lem3895383) (@lem3895381)). Qed.
Lemma lem3895385 : term185 = True.
Proof. exact (TRANS (@lem3895380) (@lem3895384)). Qed.
Lemma lem3895386 : True = term185.
Proof. exact (SYM (@lem3895385)). Qed.
Lemma lem3895387 : term185.
Proof. exact (EQ_MP (@lem3895386) (@lem0)). Qed.
Lemma lem3895388 : term366 = term369.
Proof. exact (@lem3895377 (@lem3895387)). Qed.
Lemma lem3895390 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3895391 : term164 = term169.
Proof. exact (@lem3895390 term79 term79). Qed.
Lemma lem3895392 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895393 : term149 = term79.
Proof. exact (EQ_MP (@lem3895392) (@lem940073)). Qed.
Lemma lem3895394 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895395 : term147 = term78.
Proof. exact (MK_COMB (@lem3895394) (@lem3895393)). Qed.
Lemma lem3895396 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3895397 : term169 = term137.
Proof. exact (MK_COMB (@lem3895396) (@lem3895395)). Qed.
Lemma lem3895398 : term164 = term137.
Proof. exact (TRANS (@lem3895391) (@lem3895397)). Qed.
Lemma lem3895400 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895401 : term197 = term62.
Proof. exact (@lem3895400 term79). Qed.
Lemma lem3895402 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3895403 : term370 = term64.
Proof. exact (MK_COMB (@lem3895402) (@lem3895401)). Qed.
Lemma lem3895404 : term369 = term364.
Proof. exact (MK_COMB (@lem3895403) (@lem3895398)). Qed.
Lemma lem3895406 (m : nat) (n : nat) : (term371 m n) = (term372 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3895407 : term364 = term373.
Proof. exact (@lem3895406 (NUMERAL 0) term79). Qed.
Lemma lem3895408 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895409 (h1 : term187 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3895410 : (term187 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895409 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem3895408)). Qed.
Lemma lem3895411 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3895410) (@lem3895408)). Qed.
Lemma lem3895412 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3895413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3895414 : term374 = (and True).
Proof. exact (MK_COMB (@lem3895413) (@lem3895412)). Qed.
Lemma lem3895415 : term373 = (True /\ False).
Proof. exact (MK_COMB (@lem3895414) (@lem3895411)). Qed.
Lemma lem3895417 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3895418 : term373 = False.
Proof. exact (TRANS (@lem3895415) (@lem3895417)). Qed.
Lemma lem3895419 : term364 = False.
Proof. exact (TRANS (@lem3895407) (@lem3895418)). Qed.
Lemma lem3895420 : term369 = False.
Proof. exact (TRANS (@lem3895404) (@lem3895419)). Qed.
Lemma lem3895421 : term366 = False.
Proof. exact (TRANS (@lem3895388) (@lem3895420)). Qed.
Lemma lem3895422 : term364 = False.
Proof. exact (TRANS (@lem3895365) (@lem3895421)). Qed.
Lemma lem3895423 : term363 = False.
Proof. exact (TRANS (@lem3895356) (@lem3895422)). Qed.
Lemma lem3895424 (_45282 : int) (_45283 : int) (h1 : term375 _45282 _45283) : False.
Proof. exact (EQ_MP (@lem3895423) (@lem3895353 _45282 _45283 h1)). Qed.
Lemma lem3895425 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term331 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3895426 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term322 _45283.
Proof. exact (proj2 (@lem3895425 _45282 _45283 h1)). Qed.
Lemma lem3895428 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term295 _45283.
Proof. exact (proj2 (@lem3895426 _45282 _45283 h1)). Qed.
Lemma lem3895430 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : (term176 _45283) = term62.
Proof. exact (proj2 (@lem3895428 _45282 _45283 h1)). Qed.
Lemma lem3895431 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term207 _45283.
Proof. exact (proj1 (@lem3895428 _45282 _45283 h1)). Qed.
Lemma lem3895433 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3895434 : term332 = term185.
Proof. exact (@lem3895433 term62 term78). Qed.
Lemma lem3895436 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895437 : term78 = term163.
Proof. exact (@lem3895436 term79). Qed.
Lemma lem3895439 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895440 : term62 = term134.
Proof. exact (@lem3895439 (NUMERAL 0)). Qed.
Lemma lem3895441 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3895442 : term333 = term334.
Proof. exact (MK_COMB (@lem3895441) (@lem3895440)). Qed.
Lemma lem3895443 : term185 = term335.
Proof. exact (MK_COMB (@lem3895442) (@lem3895437)). Qed.
Lemma lem3895444 : term336.
Proof. exact (@lem1980255 term62 term78 term78 term78). Qed.
Lemma lem3895446 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895447 : term185 = term186.
Proof. exact (@lem3895446 (NUMERAL 0) term79). Qed.
Lemma lem3895448 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895449 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895450 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895449 h1) (fun h1 : term186 = True => @lem3895448)). Qed.
Lemma lem3895451 : term186 = True.
Proof. exact (EQ_MP (@lem3895450) (@lem3895448)). Qed.
Lemma lem3895452 : term185 = True.
Proof. exact (TRANS (@lem3895447) (@lem3895451)). Qed.
Lemma lem3895453 : True = term185.
Proof. exact (SYM (@lem3895452)). Qed.
Lemma lem3895454 : term185.
Proof. exact (EQ_MP (@lem3895453) (@lem0)). Qed.
Lemma lem3895455 : term337.
Proof. exact (@lem3895444 (@lem3895454)). Qed.
Lemma lem3895457 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895458 : term185 = term186.
Proof. exact (@lem3895457 (NUMERAL 0) term79). Qed.
Lemma lem3895459 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895460 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895461 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895460 h1) (fun h1 : term186 = True => @lem3895459)). Qed.
Lemma lem3895462 : term186 = True.
Proof. exact (EQ_MP (@lem3895461) (@lem3895459)). Qed.
Lemma lem3895463 : term185 = True.
Proof. exact (TRANS (@lem3895458) (@lem3895462)). Qed.
Lemma lem3895464 : True = term185.
Proof. exact (SYM (@lem3895463)). Qed.
Lemma lem3895465 : term185.
Proof. exact (EQ_MP (@lem3895464) (@lem0)). Qed.
Lemma lem3895466 : term335 = term338.
Proof. exact (@lem3895455 (@lem3895465)). Qed.
Lemma lem3895468 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3895469 : term146 = term147.
Proof. exact (@lem3895468 term79 term79). Qed.
Lemma lem3895470 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895471 : term149 = term79.
Proof. exact (EQ_MP (@lem3895470) (@lem940073)). Qed.
Lemma lem3895472 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895473 : term147 = term78.
Proof. exact (MK_COMB (@lem3895472) (@lem3895471)). Qed.
Lemma lem3895474 : term146 = term78.
Proof. exact (TRANS (@lem3895469) (@lem3895473)). Qed.
Lemma lem3895476 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895477 : term197 = term62.
Proof. exact (@lem3895476 term79). Qed.
Lemma lem3895478 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3895479 : term339 = term333.
Proof. exact (MK_COMB (@lem3895478) (@lem3895477)). Qed.
Lemma lem3895480 : term338 = term185.
Proof. exact (MK_COMB (@lem3895479) (@lem3895474)). Qed.
Lemma lem3895482 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895483 : term185 = term186.
Proof. exact (@lem3895482 (NUMERAL 0) term79). Qed.
Lemma lem3895484 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895485 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895486 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895485 h1) (fun h1 : term186 = True => @lem3895484)). Qed.
Lemma lem3895487 : term186 = True.
Proof. exact (EQ_MP (@lem3895486) (@lem3895484)). Qed.
Lemma lem3895488 : term185 = True.
Proof. exact (TRANS (@lem3895483) (@lem3895487)). Qed.
Lemma lem3895489 : term338 = True.
Proof. exact (TRANS (@lem3895480) (@lem3895488)). Qed.
Lemma lem3895490 : term335 = True.
Proof. exact (TRANS (@lem3895466) (@lem3895489)). Qed.
Lemma lem3895491 : term185 = True.
Proof. exact (TRANS (@lem3895443) (@lem3895490)). Qed.
Lemma lem3895492 : term332 = True.
Proof. exact (TRANS (@lem3895434) (@lem3895491)). Qed.
Lemma lem3895493 : True = term332.
Proof. exact (SYM (@lem3895492)). Qed.
Lemma lem3895494 : term332.
Proof. exact (EQ_MP (@lem3895493) (@lem0)). Qed.
Lemma lem3895495 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term340 _45283.
Proof. exact (conj (@lem3895494) (@lem3895431 _45282 _45283 h1)). Qed.
Lemma lem3895497 (x : real) (y : real) : term341 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3895498 (_45283 : int) : term342 _45283.
Proof. exact (@lem3895497 term78 (term203 _45283)). Qed.
Lemma lem3895499 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term343 _45283.
Proof. exact (@lem3895498 _45283 (@lem3895495 _45282 _45283 h1)). Qed.
Lemma lem3895500 (_45283 : int) : (term344 _45283) = (term203 _45283).
Proof. exact (@lem1982733 (term203 _45283)). Qed.
Lemma lem3895501 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3895502 (_45283 : int) : (term345 _45283) = (term206 _45283).
Proof. exact (MK_COMB (@lem3895501) (@lem3895500 _45283)). Qed.
Lemma lem3895503 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3895504 (_45283 : int) : (term343 _45283) = (term207 _45283).
Proof. exact (MK_COMB (@lem3895502 _45283) (@lem3895503)). Qed.
Lemma lem3895505 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term207 _45283.
Proof. exact (EQ_MP (@lem3895504 _45283) (@lem3895499 _45282 _45283 h1)). Qed.
Lemma lem3895507 (y : real) : term346 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3895508 (_45283 : int) : term347 _45283.
Proof. exact (@lem3895507 (term176 _45283)). Qed.
Lemma lem3895509 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term348 _45283.
Proof. exact (@lem3895508 _45283 (@lem3895430 _45282 _45283 h1)). Qed.
Lemma lem3895510 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term349 _45283.
Proof. exact (@lem3895509 _45282 _45283 h1 term78). Qed.
Lemma lem3895511 (_45283 : int) : (term349 _45283) = ((term350 _45283) = term62).
Proof. exact (eq_refl (term349 _45283)). Qed.
Lemma lem3895512 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : (term350 _45283) = term62.
Proof. exact (EQ_MP (@lem3895511 _45283) (@lem3895510 _45282 _45283 h1)). Qed.
Lemma lem3895513 (_45283 : int) : (term350 _45283) = (term176 _45283).
Proof. exact (@lem1982733 (term176 _45283)). Qed.
Lemma lem3895514 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3895515 (_45283 : int) : (term351 _45283) = (term246 _45283).
Proof. exact (MK_COMB (@lem3895514) (@lem3895513 _45283)). Qed.
Lemma lem3895516 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3895517 (_45283 : int) : ((term350 _45283) = term62) = ((term176 _45283) = term62).
Proof. exact (MK_COMB (@lem3895515 _45283) (@lem3895516)). Qed.
Lemma lem3895518 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : (term176 _45283) = term62.
Proof. exact (EQ_MP (@lem3895517 _45283) (@lem3895512 _45282 _45283 h1)). Qed.
Lemma lem3895519 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term352 _45283.
Proof. exact (conj (@lem3895518 _45282 _45283 h1) (@lem3895505 _45282 _45283 h1)). Qed.
Lemma lem3895521 (x : real) (y : real) : term353 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3895522 (_45283 : int) : term354 _45283.
Proof. exact (@lem3895521 (term176 _45283) (term203 _45283)). Qed.
Lemma lem3895523 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term355 _45283.
Proof. exact (@lem3895522 _45283 (@lem3895519 _45282 _45283 h1)). Qed.
Lemma lem3895524 (_45283 : int) : (term356 _45283) = (term357 _45283).
Proof. exact (@lem1982763 (term176 _45283) (real_of_int _45283) term137). Qed.
Lemma lem3895525 (_45283 : int) : (term358 _45283) = (term178 _45283).
Proof. exact (@lem1982713 term137 (real_of_int _45283)). Qed.
Lemma lem3895527 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895528 : term78 = term163.
Proof. exact (@lem3895527 term79). Qed.
Lemma lem3895530 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3895531 : term137 = term138.
Proof. exact (@lem3895530 term79). Qed.
Lemma lem3895532 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3895533 : term179 = term180.
Proof. exact (MK_COMB (@lem3895532) (@lem3895531)). Qed.
Lemma lem3895534 : term181 = term182.
Proof. exact (MK_COMB (@lem3895533) (@lem3895528)). Qed.
Lemma lem3895535 : term183.
Proof. exact (@lem1981473 term137 term78 term78 term78 term62 term78). Qed.
Lemma lem3895537 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895538 : term185 = term186.
Proof. exact (@lem3895537 (NUMERAL 0) term79). Qed.
Lemma lem3895539 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895540 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895541 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895540 h1) (fun h1 : term186 = True => @lem3895539)). Qed.
Lemma lem3895542 : term186 = True.
Proof. exact (EQ_MP (@lem3895541) (@lem3895539)). Qed.
Lemma lem3895543 : term185 = True.
Proof. exact (TRANS (@lem3895538) (@lem3895542)). Qed.
Lemma lem3895544 : True = term185.
Proof. exact (SYM (@lem3895543)). Qed.
Lemma lem3895545 : term185.
Proof. exact (EQ_MP (@lem3895544) (@lem0)). Qed.
Lemma lem3895546 : term188.
Proof. exact (@lem3895535 (@lem3895545)). Qed.
Lemma lem3895548 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895549 : term185 = term186.
Proof. exact (@lem3895548 (NUMERAL 0) term79). Qed.
Lemma lem3895550 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895551 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895552 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895551 h1) (fun h1 : term186 = True => @lem3895550)). Qed.
Lemma lem3895553 : term186 = True.
Proof. exact (EQ_MP (@lem3895552) (@lem3895550)). Qed.
Lemma lem3895554 : term185 = True.
Proof. exact (TRANS (@lem3895549) (@lem3895553)). Qed.
Lemma lem3895555 : True = term185.
Proof. exact (SYM (@lem3895554)). Qed.
Lemma lem3895556 : term185.
Proof. exact (EQ_MP (@lem3895555) (@lem0)). Qed.
Lemma lem3895557 : term189.
Proof. exact (@lem3895546 (@lem3895556)). Qed.
Lemma lem3895559 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895560 : term185 = term186.
Proof. exact (@lem3895559 (NUMERAL 0) term79). Qed.
Lemma lem3895561 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895562 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895563 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895562 h1) (fun h1 : term186 = True => @lem3895561)). Qed.
Lemma lem3895564 : term186 = True.
Proof. exact (EQ_MP (@lem3895563) (@lem3895561)). Qed.
Lemma lem3895565 : term185 = True.
Proof. exact (TRANS (@lem3895560) (@lem3895564)). Qed.
Lemma lem3895566 : True = term185.
Proof. exact (SYM (@lem3895565)). Qed.
Lemma lem3895567 : term185.
Proof. exact (EQ_MP (@lem3895566) (@lem0)). Qed.
Lemma lem3895568 : term190.
Proof. exact (@lem3895557 (@lem3895567)). Qed.
Lemma lem3895570 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3895571 : term146 = term147.
Proof. exact (@lem3895570 term79 term79). Qed.
Lemma lem3895572 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895573 : term149 = term79.
Proof. exact (EQ_MP (@lem3895572) (@lem940073)). Qed.
Lemma lem3895574 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895575 : term147 = term78.
Proof. exact (MK_COMB (@lem3895574) (@lem3895573)). Qed.
Lemma lem3895576 : term146 = term78.
Proof. exact (TRANS (@lem3895571) (@lem3895575)). Qed.
Lemma lem3895578 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3895579 : term164 = term169.
Proof. exact (@lem3895578 term79 term79). Qed.
Lemma lem3895580 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895581 : term149 = term79.
Proof. exact (EQ_MP (@lem3895580) (@lem940073)). Qed.
Lemma lem3895582 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895583 : term147 = term78.
Proof. exact (MK_COMB (@lem3895582) (@lem3895581)). Qed.
Lemma lem3895584 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3895585 : term169 = term137.
Proof. exact (MK_COMB (@lem3895584) (@lem3895583)). Qed.
Lemma lem3895586 : term164 = term137.
Proof. exact (TRANS (@lem3895579) (@lem3895585)). Qed.
Lemma lem3895587 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3895588 : term191 = term179.
Proof. exact (MK_COMB (@lem3895587) (@lem3895586)). Qed.
Lemma lem3895589 : term192 = term181.
Proof. exact (MK_COMB (@lem3895588) (@lem3895576)). Qed.
Lemma lem3895591 (m : nat) : (term193 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3895592 : term181 = term62.
Proof. exact (@lem3895591 term79). Qed.
Lemma lem3895593 : term192 = term62.
Proof. exact (TRANS (@lem3895589) (@lem3895592)). Qed.
Lemma lem3895594 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3895595 : term194 = term195.
Proof. exact (MK_COMB (@lem3895594) (@lem3895593)). Qed.
Lemma lem3895596 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem3895597 : term196 = term197.
Proof. exact (MK_COMB (@lem3895595) (@lem3895596)). Qed.
Lemma lem3895599 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895600 : term197 = term62.
Proof. exact (@lem3895599 term79). Qed.
Lemma lem3895601 : term196 = term62.
Proof. exact (TRANS (@lem3895597) (@lem3895600)). Qed.
Lemma lem3895603 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3895604 : term146 = term147.
Proof. exact (@lem3895603 term79 term79). Qed.
Lemma lem3895605 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895606 : term149 = term79.
Proof. exact (EQ_MP (@lem3895605) (@lem940073)). Qed.
Lemma lem3895607 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895608 : term147 = term78.
Proof. exact (MK_COMB (@lem3895607) (@lem3895606)). Qed.
Lemma lem3895609 : term146 = term78.
Proof. exact (TRANS (@lem3895604) (@lem3895608)). Qed.
Lemma lem3895610 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem3895611 : term199 = term197.
Proof. exact (MK_COMB (@lem3895610) (@lem3895609)). Qed.
Lemma lem3895613 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895614 : term197 = term62.
Proof. exact (@lem3895613 term79). Qed.
Lemma lem3895615 : term199 = term62.
Proof. exact (TRANS (@lem3895611) (@lem3895614)). Qed.
Lemma lem3895616 : term62 = term199.
Proof. exact (SYM (@lem3895615)). Qed.
Lemma lem3895617 : term196 = term199.
Proof. exact (TRANS (@lem3895601) (@lem3895616)). Qed.
Lemma lem3895618 : term182 = term134.
Proof. exact (@lem3895568 (@lem3895617)). Qed.
Lemma lem3895619 : term181 = term134.
Proof. exact (TRANS (@lem3895534) (@lem3895618)). Qed.
Lemma lem3895621 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3895622 : term134 = term62.
Proof. exact (@lem3895621 term62). Qed.
Lemma lem3895623 : term181 = term62.
Proof. exact (TRANS (@lem3895619) (@lem3895622)). Qed.
Lemma lem3895624 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3895625 : term200 = term195.
Proof. exact (MK_COMB (@lem3895624) (@lem3895623)). Qed.
Lemma lem3895626 (_45283 : int) : (real_of_int _45283) = (real_of_int _45283).
Proof. exact (eq_refl (real_of_int _45283)). Qed.
Lemma lem3895627 (_45283 : int) : (term178 _45283) = (term201 _45283).
Proof. exact (MK_COMB (@lem3895625) (@lem3895626 _45283)). Qed.
Lemma lem3895628 (_45283 : int) : (term358 _45283) = (term201 _45283).
Proof. exact (TRANS (@lem3895525 _45283) (@lem3895627 _45283)). Qed.
Lemma lem3895629 (_45283 : int) : (term201 _45283) = term62.
Proof. exact (@lem1982719 (real_of_int _45283)). Qed.
Lemma lem3895630 (_45283 : int) : (term358 _45283) = term62.
Proof. exact (TRANS (@lem3895628 _45283) (@lem3895629 _45283)). Qed.
Lemma lem3895631 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3895632 (_45283 : int) : (term359 _45283) = term111.
Proof. exact (MK_COMB (@lem3895631) (@lem3895630 _45283)). Qed.
Lemma lem3895633 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem3895634 (_45283 : int) : (term357 _45283) = term360.
Proof. exact (MK_COMB (@lem3895632 _45283) (@lem3895633)). Qed.
Lemma lem3895635 (_45283 : int) : (term356 _45283) = term360.
Proof. exact (TRANS (@lem3895524 _45283) (@lem3895634 _45283)). Qed.
Lemma lem3895636 : term360 = term137.
Proof. exact (@lem1982721 term137). Qed.
Lemma lem3895637 (_45283 : int) : (term356 _45283) = term137.
Proof. exact (TRANS (@lem3895635 _45283) (@lem3895636)). Qed.
Lemma lem3895638 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3895639 (_45283 : int) : (term361 _45283) = term362.
Proof. exact (MK_COMB (@lem3895638) (@lem3895637 _45283)). Qed.
Lemma lem3895640 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3895641 (_45283 : int) : (term355 _45283) = term363.
Proof. exact (MK_COMB (@lem3895639 _45283) (@lem3895640)). Qed.
Lemma lem3895642 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : term363.
Proof. exact (EQ_MP (@lem3895641 _45283) (@lem3895523 _45282 _45283 h1)). Qed.
Lemma lem3895644 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3895645 : term363 = term364.
Proof. exact (@lem3895644 term62 term137). Qed.
Lemma lem3895647 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3895648 : term137 = term138.
Proof. exact (@lem3895647 term79). Qed.
Lemma lem3895650 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895651 : term62 = term134.
Proof. exact (@lem3895650 (NUMERAL 0)). Qed.
Lemma lem3895652 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3895653 : term64 = term365.
Proof. exact (MK_COMB (@lem3895652) (@lem3895651)). Qed.
Lemma lem3895654 : term364 = term366.
Proof. exact (MK_COMB (@lem3895653) (@lem3895648)). Qed.
Lemma lem3895655 : term367.
Proof. exact (@lem1980026 term62 term78 term137 term78). Qed.
Lemma lem3895657 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895658 : term185 = term186.
Proof. exact (@lem3895657 (NUMERAL 0) term79). Qed.
Lemma lem3895659 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895660 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895661 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895660 h1) (fun h1 : term186 = True => @lem3895659)). Qed.
Lemma lem3895662 : term186 = True.
Proof. exact (EQ_MP (@lem3895661) (@lem3895659)). Qed.
Lemma lem3895663 : term185 = True.
Proof. exact (TRANS (@lem3895658) (@lem3895662)). Qed.
Lemma lem3895664 : True = term185.
Proof. exact (SYM (@lem3895663)). Qed.
Lemma lem3895665 : term185.
Proof. exact (EQ_MP (@lem3895664) (@lem0)). Qed.
Lemma lem3895666 : term368.
Proof. exact (@lem3895655 (@lem3895665)). Qed.
Lemma lem3895668 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895669 : term185 = term186.
Proof. exact (@lem3895668 (NUMERAL 0) term79). Qed.
Lemma lem3895670 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895671 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895672 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895671 h1) (fun h1 : term186 = True => @lem3895670)). Qed.
Lemma lem3895673 : term186 = True.
Proof. exact (EQ_MP (@lem3895672) (@lem3895670)). Qed.
Lemma lem3895674 : term185 = True.
Proof. exact (TRANS (@lem3895669) (@lem3895673)). Qed.
Lemma lem3895675 : True = term185.
Proof. exact (SYM (@lem3895674)). Qed.
Lemma lem3895676 : term185.
Proof. exact (EQ_MP (@lem3895675) (@lem0)). Qed.
Lemma lem3895677 : term366 = term369.
Proof. exact (@lem3895666 (@lem3895676)). Qed.
Lemma lem3895679 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3895680 : term164 = term169.
Proof. exact (@lem3895679 term79 term79). Qed.
Lemma lem3895681 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895682 : term149 = term79.
Proof. exact (EQ_MP (@lem3895681) (@lem940073)). Qed.
Lemma lem3895683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895684 : term147 = term78.
Proof. exact (MK_COMB (@lem3895683) (@lem3895682)). Qed.
Lemma lem3895685 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3895686 : term169 = term137.
Proof. exact (MK_COMB (@lem3895685) (@lem3895684)). Qed.
Lemma lem3895687 : term164 = term137.
Proof. exact (TRANS (@lem3895680) (@lem3895686)). Qed.
Lemma lem3895689 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895690 : term197 = term62.
Proof. exact (@lem3895689 term79). Qed.
Lemma lem3895691 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3895692 : term370 = term64.
Proof. exact (MK_COMB (@lem3895691) (@lem3895690)). Qed.
Lemma lem3895693 : term369 = term364.
Proof. exact (MK_COMB (@lem3895692) (@lem3895687)). Qed.
Lemma lem3895695 (m : nat) (n : nat) : (term371 m n) = (term372 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3895696 : term364 = term373.
Proof. exact (@lem3895695 (NUMERAL 0) term79). Qed.
Lemma lem3895697 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895698 (h1 : term187 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3895699 : (term187 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895698 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem3895697)). Qed.
Lemma lem3895700 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3895699) (@lem3895697)). Qed.
Lemma lem3895701 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3895702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3895703 : term374 = (and True).
Proof. exact (MK_COMB (@lem3895702) (@lem3895701)). Qed.
Lemma lem3895704 : term373 = (True /\ False).
Proof. exact (MK_COMB (@lem3895703) (@lem3895700)). Qed.
Lemma lem3895706 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3895707 : term373 = False.
Proof. exact (TRANS (@lem3895704) (@lem3895706)). Qed.
Lemma lem3895708 : term364 = False.
Proof. exact (TRANS (@lem3895696) (@lem3895707)). Qed.
Lemma lem3895709 : term369 = False.
Proof. exact (TRANS (@lem3895693) (@lem3895708)). Qed.
Lemma lem3895710 : term366 = False.
Proof. exact (TRANS (@lem3895677) (@lem3895709)). Qed.
Lemma lem3895711 : term364 = False.
Proof. exact (TRANS (@lem3895654) (@lem3895710)). Qed.
Lemma lem3895712 : term363 = False.
Proof. exact (TRANS (@lem3895645) (@lem3895711)). Qed.
Lemma lem3895713 (_45282 : int) (_45283 : int) (h1 : term331 _45282 _45283) : False.
Proof. exact (EQ_MP (@lem3895712) (@lem3895642 _45282 _45283 h1)). Qed.
Lemma lem3895714 (_45282 : int) (_45283 : int) (h1 : term320 _45282 _45283) : False.
Proof. exact (or_elim (@lem3895093 _45282 _45283 h1) (fun h0 : term375 _45282 _45283 => @lem3895424 _45282 _45283 h0) (fun h0 : term331 _45282 _45283 => @lem3895713 _45282 _45283 h0)). Qed.
Lemma lem3895715 (_45282 : int) (_45283 : int) (h1 : term327 _45282 _45283) : False.
Proof. exact (or_elim (@lem3894470 _45282 _45283 h1) (fun h0 : term324 _45282 _45283 => @lem3895092 _45282 _45283 h0) (fun h0 : term320 _45282 _45283 => @lem3895714 _45282 _45283 h0)). Qed.
Lemma lem3895716 (_45282 : int) (_45283 : int) (h1 : term316 _45282 _45283) : term316 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3895717 (_45282 : int) (_45283 : int) (h1 : term313 _45282 _45283) : term313 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3895718 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term400 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3895719 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term311 _45283.
Proof. exact (proj2 (@lem3895718 _45282 _45283 h1)). Qed.
Lemma lem3895721 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term284 _45283.
Proof. exact (proj2 (@lem3895719 _45282 _45283 h1)). Qed.
Lemma lem3895723 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : (real_of_int _45283) = term62.
Proof. exact (proj2 (@lem3895721 _45282 _45283 h1)). Qed.
Lemma lem3895724 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term207 _45283.
Proof. exact (proj1 (@lem3895721 _45282 _45283 h1)). Qed.
Lemma lem3895726 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3895727 : term332 = term185.
Proof. exact (@lem3895726 term62 term78). Qed.
Lemma lem3895729 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895730 : term78 = term163.
Proof. exact (@lem3895729 term79). Qed.
Lemma lem3895732 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895733 : term62 = term134.
Proof. exact (@lem3895732 (NUMERAL 0)). Qed.
Lemma lem3895734 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3895735 : term333 = term334.
Proof. exact (MK_COMB (@lem3895734) (@lem3895733)). Qed.
Lemma lem3895736 : term185 = term335.
Proof. exact (MK_COMB (@lem3895735) (@lem3895730)). Qed.
Lemma lem3895737 : term336.
Proof. exact (@lem1980255 term62 term78 term78 term78). Qed.
Lemma lem3895739 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895740 : term185 = term186.
Proof. exact (@lem3895739 (NUMERAL 0) term79). Qed.
Lemma lem3895741 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895742 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895743 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895742 h1) (fun h1 : term186 = True => @lem3895741)). Qed.
Lemma lem3895744 : term186 = True.
Proof. exact (EQ_MP (@lem3895743) (@lem3895741)). Qed.
Lemma lem3895745 : term185 = True.
Proof. exact (TRANS (@lem3895740) (@lem3895744)). Qed.
Lemma lem3895746 : True = term185.
Proof. exact (SYM (@lem3895745)). Qed.
Lemma lem3895747 : term185.
Proof. exact (EQ_MP (@lem3895746) (@lem0)). Qed.
Lemma lem3895748 : term337.
Proof. exact (@lem3895737 (@lem3895747)). Qed.
Lemma lem3895750 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895751 : term185 = term186.
Proof. exact (@lem3895750 (NUMERAL 0) term79). Qed.
Lemma lem3895752 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895753 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895754 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895753 h1) (fun h1 : term186 = True => @lem3895752)). Qed.
Lemma lem3895755 : term186 = True.
Proof. exact (EQ_MP (@lem3895754) (@lem3895752)). Qed.
Lemma lem3895756 : term185 = True.
Proof. exact (TRANS (@lem3895751) (@lem3895755)). Qed.
Lemma lem3895757 : True = term185.
Proof. exact (SYM (@lem3895756)). Qed.
Lemma lem3895758 : term185.
Proof. exact (EQ_MP (@lem3895757) (@lem0)). Qed.
Lemma lem3895759 : term335 = term338.
Proof. exact (@lem3895748 (@lem3895758)). Qed.
Lemma lem3895761 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3895762 : term146 = term147.
Proof. exact (@lem3895761 term79 term79). Qed.
Lemma lem3895763 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895764 : term149 = term79.
Proof. exact (EQ_MP (@lem3895763) (@lem940073)). Qed.
Lemma lem3895765 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895766 : term147 = term78.
Proof. exact (MK_COMB (@lem3895765) (@lem3895764)). Qed.
Lemma lem3895767 : term146 = term78.
Proof. exact (TRANS (@lem3895762) (@lem3895766)). Qed.
Lemma lem3895769 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895770 : term197 = term62.
Proof. exact (@lem3895769 term79). Qed.
Lemma lem3895771 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3895772 : term339 = term333.
Proof. exact (MK_COMB (@lem3895771) (@lem3895770)). Qed.
Lemma lem3895773 : term338 = term185.
Proof. exact (MK_COMB (@lem3895772) (@lem3895767)). Qed.
Lemma lem3895775 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895776 : term185 = term186.
Proof. exact (@lem3895775 (NUMERAL 0) term79). Qed.
Lemma lem3895777 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895778 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895779 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895778 h1) (fun h1 : term186 = True => @lem3895777)). Qed.
Lemma lem3895780 : term186 = True.
Proof. exact (EQ_MP (@lem3895779) (@lem3895777)). Qed.
Lemma lem3895781 : term185 = True.
Proof. exact (TRANS (@lem3895776) (@lem3895780)). Qed.
Lemma lem3895782 : term338 = True.
Proof. exact (TRANS (@lem3895773) (@lem3895781)). Qed.
Lemma lem3895783 : term335 = True.
Proof. exact (TRANS (@lem3895759) (@lem3895782)). Qed.
Lemma lem3895784 : term185 = True.
Proof. exact (TRANS (@lem3895736) (@lem3895783)). Qed.
Lemma lem3895785 : term332 = True.
Proof. exact (TRANS (@lem3895727) (@lem3895784)). Qed.
Lemma lem3895786 : True = term332.
Proof. exact (SYM (@lem3895785)). Qed.
Lemma lem3895787 : term332.
Proof. exact (EQ_MP (@lem3895786) (@lem0)). Qed.
Lemma lem3895788 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term340 _45283.
Proof. exact (conj (@lem3895787) (@lem3895724 _45282 _45283 h1)). Qed.
Lemma lem3895790 (x : real) (y : real) : term341 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3895791 (_45283 : int) : term342 _45283.
Proof. exact (@lem3895790 term78 (term203 _45283)). Qed.
Lemma lem3895792 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term343 _45283.
Proof. exact (@lem3895791 _45283 (@lem3895788 _45282 _45283 h1)). Qed.
Lemma lem3895793 (_45283 : int) : (term344 _45283) = (term203 _45283).
Proof. exact (@lem1982733 (term203 _45283)). Qed.
Lemma lem3895794 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3895795 (_45283 : int) : (term345 _45283) = (term206 _45283).
Proof. exact (MK_COMB (@lem3895794) (@lem3895793 _45283)). Qed.
Lemma lem3895796 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3895797 (_45283 : int) : (term343 _45283) = (term207 _45283).
Proof. exact (MK_COMB (@lem3895795 _45283) (@lem3895796)). Qed.
Lemma lem3895798 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term207 _45283.
Proof. exact (EQ_MP (@lem3895797 _45283) (@lem3895792 _45282 _45283 h1)). Qed.
Lemma lem3895800 (y : real) : term346 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3895801 (_45283 : int) : term401 _45283.
Proof. exact (@lem3895800 (real_of_int _45283)). Qed.
Lemma lem3895802 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term402 _45283.
Proof. exact (@lem3895801 _45283 (@lem3895723 _45282 _45283 h1)). Qed.
Lemma lem3895803 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term403 _45283.
Proof. exact (@lem3895802 _45282 _45283 h1 term137). Qed.
Lemma lem3895804 (_45283 : int) : (term403 _45283) = ((term176 _45283) = term62).
Proof. exact (eq_refl (term403 _45283)). Qed.
Lemma lem3895811 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : (term176 _45283) = term62.
Proof. exact (EQ_MP (@lem3895804 _45283) (@lem3895803 _45282 _45283 h1)). Qed.
Lemma lem3895812 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term352 _45283.
Proof. exact (conj (@lem3895811 _45282 _45283 h1) (@lem3895798 _45282 _45283 h1)). Qed.
Lemma lem3895814 (x : real) (y : real) : term353 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3895815 (_45283 : int) : term354 _45283.
Proof. exact (@lem3895814 (term176 _45283) (term203 _45283)). Qed.
Lemma lem3895816 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term355 _45283.
Proof. exact (@lem3895815 _45283 (@lem3895812 _45282 _45283 h1)). Qed.
Lemma lem3895817 (_45283 : int) : (term356 _45283) = (term357 _45283).
Proof. exact (@lem1982763 (term176 _45283) (real_of_int _45283) term137). Qed.
Lemma lem3895818 (_45283 : int) : (term358 _45283) = (term178 _45283).
Proof. exact (@lem1982713 term137 (real_of_int _45283)). Qed.
Lemma lem3895820 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895821 : term78 = term163.
Proof. exact (@lem3895820 term79). Qed.
Lemma lem3895823 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3895824 : term137 = term138.
Proof. exact (@lem3895823 term79). Qed.
Lemma lem3895825 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3895826 : term179 = term180.
Proof. exact (MK_COMB (@lem3895825) (@lem3895824)). Qed.
Lemma lem3895827 : term181 = term182.
Proof. exact (MK_COMB (@lem3895826) (@lem3895821)). Qed.
Lemma lem3895828 : term183.
Proof. exact (@lem1981473 term137 term78 term78 term78 term62 term78). Qed.
Lemma lem3895830 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895831 : term185 = term186.
Proof. exact (@lem3895830 (NUMERAL 0) term79). Qed.
Lemma lem3895832 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895833 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895834 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895833 h1) (fun h1 : term186 = True => @lem3895832)). Qed.
Lemma lem3895835 : term186 = True.
Proof. exact (EQ_MP (@lem3895834) (@lem3895832)). Qed.
Lemma lem3895836 : term185 = True.
Proof. exact (TRANS (@lem3895831) (@lem3895835)). Qed.
Lemma lem3895837 : True = term185.
Proof. exact (SYM (@lem3895836)). Qed.
Lemma lem3895838 : term185.
Proof. exact (EQ_MP (@lem3895837) (@lem0)). Qed.
Lemma lem3895839 : term188.
Proof. exact (@lem3895828 (@lem3895838)). Qed.
Lemma lem3895841 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895842 : term185 = term186.
Proof. exact (@lem3895841 (NUMERAL 0) term79). Qed.
Lemma lem3895843 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895844 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895845 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895844 h1) (fun h1 : term186 = True => @lem3895843)). Qed.
Lemma lem3895846 : term186 = True.
Proof. exact (EQ_MP (@lem3895845) (@lem3895843)). Qed.
Lemma lem3895847 : term185 = True.
Proof. exact (TRANS (@lem3895842) (@lem3895846)). Qed.
Lemma lem3895848 : True = term185.
Proof. exact (SYM (@lem3895847)). Qed.
Lemma lem3895849 : term185.
Proof. exact (EQ_MP (@lem3895848) (@lem0)). Qed.
Lemma lem3895850 : term189.
Proof. exact (@lem3895839 (@lem3895849)). Qed.
Lemma lem3895852 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895853 : term185 = term186.
Proof. exact (@lem3895852 (NUMERAL 0) term79). Qed.
Lemma lem3895854 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895855 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895856 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895855 h1) (fun h1 : term186 = True => @lem3895854)). Qed.
Lemma lem3895857 : term186 = True.
Proof. exact (EQ_MP (@lem3895856) (@lem3895854)). Qed.
Lemma lem3895858 : term185 = True.
Proof. exact (TRANS (@lem3895853) (@lem3895857)). Qed.
Lemma lem3895859 : True = term185.
Proof. exact (SYM (@lem3895858)). Qed.
Lemma lem3895860 : term185.
Proof. exact (EQ_MP (@lem3895859) (@lem0)). Qed.
Lemma lem3895861 : term190.
Proof. exact (@lem3895850 (@lem3895860)). Qed.
Lemma lem3895863 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3895864 : term146 = term147.
Proof. exact (@lem3895863 term79 term79). Qed.
Lemma lem3895865 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895866 : term149 = term79.
Proof. exact (EQ_MP (@lem3895865) (@lem940073)). Qed.
Lemma lem3895867 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895868 : term147 = term78.
Proof. exact (MK_COMB (@lem3895867) (@lem3895866)). Qed.
Lemma lem3895869 : term146 = term78.
Proof. exact (TRANS (@lem3895864) (@lem3895868)). Qed.
Lemma lem3895871 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3895872 : term164 = term169.
Proof. exact (@lem3895871 term79 term79). Qed.
Lemma lem3895873 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895874 : term149 = term79.
Proof. exact (EQ_MP (@lem3895873) (@lem940073)). Qed.
Lemma lem3895875 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895876 : term147 = term78.
Proof. exact (MK_COMB (@lem3895875) (@lem3895874)). Qed.
Lemma lem3895877 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3895878 : term169 = term137.
Proof. exact (MK_COMB (@lem3895877) (@lem3895876)). Qed.
Lemma lem3895879 : term164 = term137.
Proof. exact (TRANS (@lem3895872) (@lem3895878)). Qed.
Lemma lem3895880 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3895881 : term191 = term179.
Proof. exact (MK_COMB (@lem3895880) (@lem3895879)). Qed.
Lemma lem3895882 : term192 = term181.
Proof. exact (MK_COMB (@lem3895881) (@lem3895869)). Qed.
Lemma lem3895884 (m : nat) : (term193 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3895885 : term181 = term62.
Proof. exact (@lem3895884 term79). Qed.
Lemma lem3895886 : term192 = term62.
Proof. exact (TRANS (@lem3895882) (@lem3895885)). Qed.
Lemma lem3895887 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3895888 : term194 = term195.
Proof. exact (MK_COMB (@lem3895887) (@lem3895886)). Qed.
Lemma lem3895889 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem3895890 : term196 = term197.
Proof. exact (MK_COMB (@lem3895888) (@lem3895889)). Qed.
Lemma lem3895892 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895893 : term197 = term62.
Proof. exact (@lem3895892 term79). Qed.
Lemma lem3895894 : term196 = term62.
Proof. exact (TRANS (@lem3895890) (@lem3895893)). Qed.
Lemma lem3895896 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3895897 : term146 = term147.
Proof. exact (@lem3895896 term79 term79). Qed.
Lemma lem3895898 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895899 : term149 = term79.
Proof. exact (EQ_MP (@lem3895898) (@lem940073)). Qed.
Lemma lem3895900 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895901 : term147 = term78.
Proof. exact (MK_COMB (@lem3895900) (@lem3895899)). Qed.
Lemma lem3895902 : term146 = term78.
Proof. exact (TRANS (@lem3895897) (@lem3895901)). Qed.
Lemma lem3895903 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem3895904 : term199 = term197.
Proof. exact (MK_COMB (@lem3895903) (@lem3895902)). Qed.
Lemma lem3895906 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895907 : term197 = term62.
Proof. exact (@lem3895906 term79). Qed.
Lemma lem3895908 : term199 = term62.
Proof. exact (TRANS (@lem3895904) (@lem3895907)). Qed.
Lemma lem3895909 : term62 = term199.
Proof. exact (SYM (@lem3895908)). Qed.
Lemma lem3895910 : term196 = term199.
Proof. exact (TRANS (@lem3895894) (@lem3895909)). Qed.
Lemma lem3895911 : term182 = term134.
Proof. exact (@lem3895861 (@lem3895910)). Qed.
Lemma lem3895912 : term181 = term134.
Proof. exact (TRANS (@lem3895827) (@lem3895911)). Qed.
Lemma lem3895914 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3895915 : term134 = term62.
Proof. exact (@lem3895914 term62). Qed.
Lemma lem3895916 : term181 = term62.
Proof. exact (TRANS (@lem3895912) (@lem3895915)). Qed.
Lemma lem3895917 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3895918 : term200 = term195.
Proof. exact (MK_COMB (@lem3895917) (@lem3895916)). Qed.
Lemma lem3895919 (_45283 : int) : (real_of_int _45283) = (real_of_int _45283).
Proof. exact (eq_refl (real_of_int _45283)). Qed.
Lemma lem3895920 (_45283 : int) : (term178 _45283) = (term201 _45283).
Proof. exact (MK_COMB (@lem3895918) (@lem3895919 _45283)). Qed.
Lemma lem3895921 (_45283 : int) : (term358 _45283) = (term201 _45283).
Proof. exact (TRANS (@lem3895818 _45283) (@lem3895920 _45283)). Qed.
Lemma lem3895922 (_45283 : int) : (term201 _45283) = term62.
Proof. exact (@lem1982719 (real_of_int _45283)). Qed.
Lemma lem3895923 (_45283 : int) : (term358 _45283) = term62.
Proof. exact (TRANS (@lem3895921 _45283) (@lem3895922 _45283)). Qed.
Lemma lem3895924 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3895925 (_45283 : int) : (term359 _45283) = term111.
Proof. exact (MK_COMB (@lem3895924) (@lem3895923 _45283)). Qed.
Lemma lem3895926 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem3895927 (_45283 : int) : (term357 _45283) = term360.
Proof. exact (MK_COMB (@lem3895925 _45283) (@lem3895926)). Qed.
Lemma lem3895928 (_45283 : int) : (term356 _45283) = term360.
Proof. exact (TRANS (@lem3895817 _45283) (@lem3895927 _45283)). Qed.
Lemma lem3895929 : term360 = term137.
Proof. exact (@lem1982721 term137). Qed.
Lemma lem3895930 (_45283 : int) : (term356 _45283) = term137.
Proof. exact (TRANS (@lem3895928 _45283) (@lem3895929)). Qed.
Lemma lem3895931 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3895932 (_45283 : int) : (term361 _45283) = term362.
Proof. exact (MK_COMB (@lem3895931) (@lem3895930 _45283)). Qed.
Lemma lem3895933 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3895934 (_45283 : int) : (term355 _45283) = term363.
Proof. exact (MK_COMB (@lem3895932 _45283) (@lem3895933)). Qed.
Lemma lem3895935 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term363.
Proof. exact (EQ_MP (@lem3895934 _45283) (@lem3895816 _45282 _45283 h1)). Qed.
Lemma lem3895937 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3895938 : term363 = term364.
Proof. exact (@lem3895937 term62 term137). Qed.
Lemma lem3895940 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3895941 : term137 = term138.
Proof. exact (@lem3895940 term79). Qed.
Lemma lem3895943 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3895944 : term62 = term134.
Proof. exact (@lem3895943 (NUMERAL 0)). Qed.
Lemma lem3895945 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3895946 : term64 = term365.
Proof. exact (MK_COMB (@lem3895945) (@lem3895944)). Qed.
Lemma lem3895947 : term364 = term366.
Proof. exact (MK_COMB (@lem3895946) (@lem3895941)). Qed.
Lemma lem3895948 : term367.
Proof. exact (@lem1980026 term62 term78 term137 term78). Qed.
Lemma lem3895950 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895951 : term185 = term186.
Proof. exact (@lem3895950 (NUMERAL 0) term79). Qed.
Lemma lem3895952 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895953 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895954 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895953 h1) (fun h1 : term186 = True => @lem3895952)). Qed.
Lemma lem3895955 : term186 = True.
Proof. exact (EQ_MP (@lem3895954) (@lem3895952)). Qed.
Lemma lem3895956 : term185 = True.
Proof. exact (TRANS (@lem3895951) (@lem3895955)). Qed.
Lemma lem3895957 : True = term185.
Proof. exact (SYM (@lem3895956)). Qed.
Lemma lem3895958 : term185.
Proof. exact (EQ_MP (@lem3895957) (@lem0)). Qed.
Lemma lem3895959 : term368.
Proof. exact (@lem3895948 (@lem3895958)). Qed.
Lemma lem3895961 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3895962 : term185 = term186.
Proof. exact (@lem3895961 (NUMERAL 0) term79). Qed.
Lemma lem3895963 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895964 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3895965 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895964 h1) (fun h1 : term186 = True => @lem3895963)). Qed.
Lemma lem3895966 : term186 = True.
Proof. exact (EQ_MP (@lem3895965) (@lem3895963)). Qed.
Lemma lem3895967 : term185 = True.
Proof. exact (TRANS (@lem3895962) (@lem3895966)). Qed.
Lemma lem3895968 : True = term185.
Proof. exact (SYM (@lem3895967)). Qed.
Lemma lem3895969 : term185.
Proof. exact (EQ_MP (@lem3895968) (@lem0)). Qed.
Lemma lem3895970 : term366 = term369.
Proof. exact (@lem3895959 (@lem3895969)). Qed.
Lemma lem3895972 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3895973 : term164 = term169.
Proof. exact (@lem3895972 term79 term79). Qed.
Lemma lem3895974 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3895975 : term149 = term79.
Proof. exact (EQ_MP (@lem3895974) (@lem940073)). Qed.
Lemma lem3895976 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3895977 : term147 = term78.
Proof. exact (MK_COMB (@lem3895976) (@lem3895975)). Qed.
Lemma lem3895978 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3895979 : term169 = term137.
Proof. exact (MK_COMB (@lem3895978) (@lem3895977)). Qed.
Lemma lem3895980 : term164 = term137.
Proof. exact (TRANS (@lem3895973) (@lem3895979)). Qed.
Lemma lem3895982 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3895983 : term197 = term62.
Proof. exact (@lem3895982 term79). Qed.
Lemma lem3895984 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3895985 : term370 = term64.
Proof. exact (MK_COMB (@lem3895984) (@lem3895983)). Qed.
Lemma lem3895986 : term369 = term364.
Proof. exact (MK_COMB (@lem3895985) (@lem3895980)). Qed.
Lemma lem3895988 (m : nat) (n : nat) : (term371 m n) = (term372 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3895989 : term364 = term373.
Proof. exact (@lem3895988 (NUMERAL 0) term79). Qed.
Lemma lem3895990 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3895991 (h1 : term187 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3895992 : (term187 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3895991 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem3895990)). Qed.
Lemma lem3895993 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3895992) (@lem3895990)). Qed.
Lemma lem3895994 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3895995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3895996 : term374 = (and True).
Proof. exact (MK_COMB (@lem3895995) (@lem3895994)). Qed.
Lemma lem3895997 : term373 = (True /\ False).
Proof. exact (MK_COMB (@lem3895996) (@lem3895993)). Qed.
Lemma lem3895999 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3896000 : term373 = False.
Proof. exact (TRANS (@lem3895997) (@lem3895999)). Qed.
Lemma lem3896001 : term364 = False.
Proof. exact (TRANS (@lem3895989) (@lem3896000)). Qed.
Lemma lem3896002 : term369 = False.
Proof. exact (TRANS (@lem3895986) (@lem3896001)). Qed.
Lemma lem3896003 : term366 = False.
Proof. exact (TRANS (@lem3895970) (@lem3896002)). Qed.
Lemma lem3896004 : term364 = False.
Proof. exact (TRANS (@lem3895947) (@lem3896003)). Qed.
Lemma lem3896005 : term363 = False.
Proof. exact (TRANS (@lem3895938) (@lem3896004)). Qed.
Lemma lem3896006 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : False.
Proof. exact (EQ_MP (@lem3896005) (@lem3895935 _45282 _45283 h1)). Qed.
Lemma lem3896007 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term404 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3896008 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term310 _45283.
Proof. exact (proj2 (@lem3896007 _45282 _45283 h1)). Qed.
Lemma lem3896010 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term283 _45283.
Proof. exact (proj2 (@lem3896008 _45282 _45283 h1)). Qed.
Lemma lem3896012 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : (real_of_int _45283) = term62.
Proof. exact (proj2 (@lem3896010 _45282 _45283 h1)). Qed.
Lemma lem3896013 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term222 _45283.
Proof. exact (proj1 (@lem3896010 _45282 _45283 h1)). Qed.
Lemma lem3896015 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3896016 : term332 = term185.
Proof. exact (@lem3896015 term62 term78). Qed.
Lemma lem3896018 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3896019 : term78 = term163.
Proof. exact (@lem3896018 term79). Qed.
Lemma lem3896021 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3896022 : term62 = term134.
Proof. exact (@lem3896021 (NUMERAL 0)). Qed.
Lemma lem3896023 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3896024 : term333 = term334.
Proof. exact (MK_COMB (@lem3896023) (@lem3896022)). Qed.
Lemma lem3896025 : term185 = term335.
Proof. exact (MK_COMB (@lem3896024) (@lem3896019)). Qed.
Lemma lem3896026 : term336.
Proof. exact (@lem1980255 term62 term78 term78 term78). Qed.
Lemma lem3896028 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896029 : term185 = term186.
Proof. exact (@lem3896028 (NUMERAL 0) term79). Qed.
Lemma lem3896030 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896031 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896032 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896031 h1) (fun h1 : term186 = True => @lem3896030)). Qed.
Lemma lem3896033 : term186 = True.
Proof. exact (EQ_MP (@lem3896032) (@lem3896030)). Qed.
Lemma lem3896034 : term185 = True.
Proof. exact (TRANS (@lem3896029) (@lem3896033)). Qed.
Lemma lem3896035 : True = term185.
Proof. exact (SYM (@lem3896034)). Qed.
Lemma lem3896036 : term185.
Proof. exact (EQ_MP (@lem3896035) (@lem0)). Qed.
Lemma lem3896037 : term337.
Proof. exact (@lem3896026 (@lem3896036)). Qed.
Lemma lem3896039 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896040 : term185 = term186.
Proof. exact (@lem3896039 (NUMERAL 0) term79). Qed.
Lemma lem3896041 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896042 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896043 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896042 h1) (fun h1 : term186 = True => @lem3896041)). Qed.
Lemma lem3896044 : term186 = True.
Proof. exact (EQ_MP (@lem3896043) (@lem3896041)). Qed.
Lemma lem3896045 : term185 = True.
Proof. exact (TRANS (@lem3896040) (@lem3896044)). Qed.
Lemma lem3896046 : True = term185.
Proof. exact (SYM (@lem3896045)). Qed.
Lemma lem3896047 : term185.
Proof. exact (EQ_MP (@lem3896046) (@lem0)). Qed.
Lemma lem3896048 : term335 = term338.
Proof. exact (@lem3896037 (@lem3896047)). Qed.
Lemma lem3896050 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3896051 : term146 = term147.
Proof. exact (@lem3896050 term79 term79). Qed.
Lemma lem3896052 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896053 : term149 = term79.
Proof. exact (EQ_MP (@lem3896052) (@lem940073)). Qed.
Lemma lem3896054 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896055 : term147 = term78.
Proof. exact (MK_COMB (@lem3896054) (@lem3896053)). Qed.
Lemma lem3896056 : term146 = term78.
Proof. exact (TRANS (@lem3896051) (@lem3896055)). Qed.
Lemma lem3896058 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3896059 : term197 = term62.
Proof. exact (@lem3896058 term79). Qed.
Lemma lem3896060 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3896061 : term339 = term333.
Proof. exact (MK_COMB (@lem3896060) (@lem3896059)). Qed.
Lemma lem3896062 : term338 = term185.
Proof. exact (MK_COMB (@lem3896061) (@lem3896056)). Qed.
Lemma lem3896064 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896065 : term185 = term186.
Proof. exact (@lem3896064 (NUMERAL 0) term79). Qed.
Lemma lem3896066 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896067 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896068 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896067 h1) (fun h1 : term186 = True => @lem3896066)). Qed.
Lemma lem3896069 : term186 = True.
Proof. exact (EQ_MP (@lem3896068) (@lem3896066)). Qed.
Lemma lem3896070 : term185 = True.
Proof. exact (TRANS (@lem3896065) (@lem3896069)). Qed.
Lemma lem3896071 : term338 = True.
Proof. exact (TRANS (@lem3896062) (@lem3896070)). Qed.
Lemma lem3896072 : term335 = True.
Proof. exact (TRANS (@lem3896048) (@lem3896071)). Qed.
Lemma lem3896073 : term185 = True.
Proof. exact (TRANS (@lem3896025) (@lem3896072)). Qed.
Lemma lem3896074 : term332 = True.
Proof. exact (TRANS (@lem3896016) (@lem3896073)). Qed.
Lemma lem3896075 : True = term332.
Proof. exact (SYM (@lem3896074)). Qed.
Lemma lem3896076 : term332.
Proof. exact (EQ_MP (@lem3896075) (@lem0)). Qed.
Lemma lem3896077 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term376 _45283.
Proof. exact (conj (@lem3896076) (@lem3896013 _45282 _45283 h1)). Qed.
Lemma lem3896079 (x : real) (y : real) : term341 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3896080 (_45283 : int) : term377 _45283.
Proof. exact (@lem3896079 term78 (term173 _45283)). Qed.
Lemma lem3896081 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term378 _45283.
Proof. exact (@lem3896080 _45283 (@lem3896077 _45282 _45283 h1)). Qed.
Lemma lem3896082 (_45283 : int) : (term379 _45283) = (term173 _45283).
Proof. exact (@lem1982733 (term173 _45283)). Qed.
Lemma lem3896083 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3896084 (_45283 : int) : (term380 _45283) = (term221 _45283).
Proof. exact (MK_COMB (@lem3896083) (@lem3896082 _45283)). Qed.
Lemma lem3896085 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3896086 (_45283 : int) : (term378 _45283) = (term222 _45283).
Proof. exact (MK_COMB (@lem3896084 _45283) (@lem3896085)). Qed.
Lemma lem3896087 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term222 _45283.
Proof. exact (EQ_MP (@lem3896086 _45283) (@lem3896081 _45282 _45283 h1)). Qed.
Lemma lem3896089 (y : real) : term346 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3896090 (_45283 : int) : term401 _45283.
Proof. exact (@lem3896089 (real_of_int _45283)). Qed.
Lemma lem3896091 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term402 _45283.
Proof. exact (@lem3896090 _45283 (@lem3896012 _45282 _45283 h1)). Qed.
Lemma lem3896092 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term405 _45283.
Proof. exact (@lem3896091 _45282 _45283 h1 term78). Qed.
Lemma lem3896093 (_45283 : int) : (term405 _45283) = ((term392 _45283) = term62).
Proof. exact (eq_refl (term405 _45283)). Qed.
Lemma lem3896094 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : (term392 _45283) = term62.
Proof. exact (EQ_MP (@lem3896093 _45283) (@lem3896092 _45282 _45283 h1)). Qed.
Lemma lem3896095 (_45283 : int) : (term392 _45283) = (real_of_int _45283).
Proof. exact (@lem1982733 (real_of_int _45283)). Qed.
Lemma lem3896096 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3896097 (_45283 : int) : (term406 _45283) = (term120 _45283).
Proof. exact (MK_COMB (@lem3896096) (@lem3896095 _45283)). Qed.
Lemma lem3896098 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3896099 (_45283 : int) : ((term392 _45283) = term62) = ((real_of_int _45283) = term62).
Proof. exact (MK_COMB (@lem3896097 _45283) (@lem3896098)). Qed.
Lemma lem3896100 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : (real_of_int _45283) = term62.
Proof. exact (EQ_MP (@lem3896099 _45283) (@lem3896094 _45282 _45283 h1)). Qed.
Lemma lem3896101 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term394 _45283.
Proof. exact (conj (@lem3896100 _45282 _45283 h1) (@lem3896087 _45282 _45283 h1)). Qed.
Lemma lem3896103 (x : real) (y : real) : term353 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3896104 (_45283 : int) : term395 _45283.
Proof. exact (@lem3896103 (real_of_int _45283) (term173 _45283)). Qed.
Lemma lem3896105 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term396 _45283.
Proof. exact (@lem3896104 _45283 (@lem3896101 _45282 _45283 h1)). Qed.
Lemma lem3896106 (_45283 : int) : (term397 _45283) = (term398 _45283).
Proof. exact (@lem1982763 (real_of_int _45283) (term176 _45283) term137). Qed.
Lemma lem3896107 (_45283 : int) : (term177 _45283) = (term178 _45283).
Proof. exact (@lem1982715 term137 (real_of_int _45283)). Qed.
Lemma lem3896109 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3896110 : term78 = term163.
Proof. exact (@lem3896109 term79). Qed.
Lemma lem3896112 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3896113 : term137 = term138.
Proof. exact (@lem3896112 term79). Qed.
Lemma lem3896114 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3896115 : term179 = term180.
Proof. exact (MK_COMB (@lem3896114) (@lem3896113)). Qed.
Lemma lem3896116 : term181 = term182.
Proof. exact (MK_COMB (@lem3896115) (@lem3896110)). Qed.
Lemma lem3896117 : term183.
Proof. exact (@lem1981473 term137 term78 term78 term78 term62 term78). Qed.
Lemma lem3896119 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896120 : term185 = term186.
Proof. exact (@lem3896119 (NUMERAL 0) term79). Qed.
Lemma lem3896121 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896122 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896123 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896122 h1) (fun h1 : term186 = True => @lem3896121)). Qed.
Lemma lem3896124 : term186 = True.
Proof. exact (EQ_MP (@lem3896123) (@lem3896121)). Qed.
Lemma lem3896125 : term185 = True.
Proof. exact (TRANS (@lem3896120) (@lem3896124)). Qed.
Lemma lem3896126 : True = term185.
Proof. exact (SYM (@lem3896125)). Qed.
Lemma lem3896127 : term185.
Proof. exact (EQ_MP (@lem3896126) (@lem0)). Qed.
Lemma lem3896128 : term188.
Proof. exact (@lem3896117 (@lem3896127)). Qed.
Lemma lem3896130 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896131 : term185 = term186.
Proof. exact (@lem3896130 (NUMERAL 0) term79). Qed.
Lemma lem3896132 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896133 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896134 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896133 h1) (fun h1 : term186 = True => @lem3896132)). Qed.
Lemma lem3896135 : term186 = True.
Proof. exact (EQ_MP (@lem3896134) (@lem3896132)). Qed.
Lemma lem3896136 : term185 = True.
Proof. exact (TRANS (@lem3896131) (@lem3896135)). Qed.
Lemma lem3896137 : True = term185.
Proof. exact (SYM (@lem3896136)). Qed.
Lemma lem3896138 : term185.
Proof. exact (EQ_MP (@lem3896137) (@lem0)). Qed.
Lemma lem3896139 : term189.
Proof. exact (@lem3896128 (@lem3896138)). Qed.
Lemma lem3896141 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896142 : term185 = term186.
Proof. exact (@lem3896141 (NUMERAL 0) term79). Qed.
Lemma lem3896143 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896144 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896145 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896144 h1) (fun h1 : term186 = True => @lem3896143)). Qed.
Lemma lem3896146 : term186 = True.
Proof. exact (EQ_MP (@lem3896145) (@lem3896143)). Qed.
Lemma lem3896147 : term185 = True.
Proof. exact (TRANS (@lem3896142) (@lem3896146)). Qed.
Lemma lem3896148 : True = term185.
Proof. exact (SYM (@lem3896147)). Qed.
Lemma lem3896149 : term185.
Proof. exact (EQ_MP (@lem3896148) (@lem0)). Qed.
Lemma lem3896150 : term190.
Proof. exact (@lem3896139 (@lem3896149)). Qed.
Lemma lem3896152 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3896153 : term146 = term147.
Proof. exact (@lem3896152 term79 term79). Qed.
Lemma lem3896154 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896155 : term149 = term79.
Proof. exact (EQ_MP (@lem3896154) (@lem940073)). Qed.
Lemma lem3896156 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896157 : term147 = term78.
Proof. exact (MK_COMB (@lem3896156) (@lem3896155)). Qed.
Lemma lem3896158 : term146 = term78.
Proof. exact (TRANS (@lem3896153) (@lem3896157)). Qed.
Lemma lem3896160 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3896161 : term164 = term169.
Proof. exact (@lem3896160 term79 term79). Qed.
Lemma lem3896162 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896163 : term149 = term79.
Proof. exact (EQ_MP (@lem3896162) (@lem940073)). Qed.
Lemma lem3896164 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896165 : term147 = term78.
Proof. exact (MK_COMB (@lem3896164) (@lem3896163)). Qed.
Lemma lem3896166 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3896167 : term169 = term137.
Proof. exact (MK_COMB (@lem3896166) (@lem3896165)). Qed.
Lemma lem3896168 : term164 = term137.
Proof. exact (TRANS (@lem3896161) (@lem3896167)). Qed.
Lemma lem3896169 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3896170 : term191 = term179.
Proof. exact (MK_COMB (@lem3896169) (@lem3896168)). Qed.
Lemma lem3896171 : term192 = term181.
Proof. exact (MK_COMB (@lem3896170) (@lem3896158)). Qed.
Lemma lem3896173 (m : nat) : (term193 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3896174 : term181 = term62.
Proof. exact (@lem3896173 term79). Qed.
Lemma lem3896175 : term192 = term62.
Proof. exact (TRANS (@lem3896171) (@lem3896174)). Qed.
Lemma lem3896176 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3896177 : term194 = term195.
Proof. exact (MK_COMB (@lem3896176) (@lem3896175)). Qed.
Lemma lem3896178 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem3896179 : term196 = term197.
Proof. exact (MK_COMB (@lem3896177) (@lem3896178)). Qed.
Lemma lem3896181 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3896182 : term197 = term62.
Proof. exact (@lem3896181 term79). Qed.
Lemma lem3896183 : term196 = term62.
Proof. exact (TRANS (@lem3896179) (@lem3896182)). Qed.
Lemma lem3896185 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3896186 : term146 = term147.
Proof. exact (@lem3896185 term79 term79). Qed.
Lemma lem3896187 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896188 : term149 = term79.
Proof. exact (EQ_MP (@lem3896187) (@lem940073)). Qed.
Lemma lem3896189 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896190 : term147 = term78.
Proof. exact (MK_COMB (@lem3896189) (@lem3896188)). Qed.
Lemma lem3896191 : term146 = term78.
Proof. exact (TRANS (@lem3896186) (@lem3896190)). Qed.
Lemma lem3896192 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem3896193 : term199 = term197.
Proof. exact (MK_COMB (@lem3896192) (@lem3896191)). Qed.
Lemma lem3896195 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3896196 : term197 = term62.
Proof. exact (@lem3896195 term79). Qed.
Lemma lem3896197 : term199 = term62.
Proof. exact (TRANS (@lem3896193) (@lem3896196)). Qed.
Lemma lem3896198 : term62 = term199.
Proof. exact (SYM (@lem3896197)). Qed.
Lemma lem3896199 : term196 = term199.
Proof. exact (TRANS (@lem3896183) (@lem3896198)). Qed.
Lemma lem3896200 : term182 = term134.
Proof. exact (@lem3896150 (@lem3896199)). Qed.
Lemma lem3896201 : term181 = term134.
Proof. exact (TRANS (@lem3896116) (@lem3896200)). Qed.
Lemma lem3896203 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3896204 : term134 = term62.
Proof. exact (@lem3896203 term62). Qed.
Lemma lem3896205 : term181 = term62.
Proof. exact (TRANS (@lem3896201) (@lem3896204)). Qed.
Lemma lem3896206 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3896207 : term200 = term195.
Proof. exact (MK_COMB (@lem3896206) (@lem3896205)). Qed.
Lemma lem3896208 (_45283 : int) : (real_of_int _45283) = (real_of_int _45283).
Proof. exact (eq_refl (real_of_int _45283)). Qed.
Lemma lem3896209 (_45283 : int) : (term178 _45283) = (term201 _45283).
Proof. exact (MK_COMB (@lem3896207) (@lem3896208 _45283)). Qed.
Lemma lem3896210 (_45283 : int) : (term177 _45283) = (term201 _45283).
Proof. exact (TRANS (@lem3896107 _45283) (@lem3896209 _45283)). Qed.
Lemma lem3896211 (_45283 : int) : (term201 _45283) = term62.
Proof. exact (@lem1982719 (real_of_int _45283)). Qed.
Lemma lem3896212 (_45283 : int) : (term177 _45283) = term62.
Proof. exact (TRANS (@lem3896210 _45283) (@lem3896211 _45283)). Qed.
Lemma lem3896213 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3896214 (_45283 : int) : (term202 _45283) = term111.
Proof. exact (MK_COMB (@lem3896213) (@lem3896212 _45283)). Qed.
Lemma lem3896215 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem3896216 (_45283 : int) : (term398 _45283) = term360.
Proof. exact (MK_COMB (@lem3896214 _45283) (@lem3896215)). Qed.
Lemma lem3896217 (_45283 : int) : (term397 _45283) = term360.
Proof. exact (TRANS (@lem3896106 _45283) (@lem3896216 _45283)). Qed.
Lemma lem3896218 : term360 = term137.
Proof. exact (@lem1982721 term137). Qed.
Lemma lem3896219 (_45283 : int) : (term397 _45283) = term137.
Proof. exact (TRANS (@lem3896217 _45283) (@lem3896218)). Qed.
Lemma lem3896220 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3896221 (_45283 : int) : (term399 _45283) = term362.
Proof. exact (MK_COMB (@lem3896220) (@lem3896219 _45283)). Qed.
Lemma lem3896222 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3896223 (_45283 : int) : (term396 _45283) = term363.
Proof. exact (MK_COMB (@lem3896221 _45283) (@lem3896222)). Qed.
Lemma lem3896224 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term363.
Proof. exact (EQ_MP (@lem3896223 _45283) (@lem3896105 _45282 _45283 h1)). Qed.
Lemma lem3896226 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3896227 : term363 = term364.
Proof. exact (@lem3896226 term62 term137). Qed.
Lemma lem3896229 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3896230 : term137 = term138.
Proof. exact (@lem3896229 term79). Qed.
Lemma lem3896232 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3896233 : term62 = term134.
Proof. exact (@lem3896232 (NUMERAL 0)). Qed.
Lemma lem3896234 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3896235 : term64 = term365.
Proof. exact (MK_COMB (@lem3896234) (@lem3896233)). Qed.
Lemma lem3896236 : term364 = term366.
Proof. exact (MK_COMB (@lem3896235) (@lem3896230)). Qed.
Lemma lem3896237 : term367.
Proof. exact (@lem1980026 term62 term78 term137 term78). Qed.
Lemma lem3896239 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896240 : term185 = term186.
Proof. exact (@lem3896239 (NUMERAL 0) term79). Qed.
Lemma lem3896241 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896242 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896243 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896242 h1) (fun h1 : term186 = True => @lem3896241)). Qed.
Lemma lem3896244 : term186 = True.
Proof. exact (EQ_MP (@lem3896243) (@lem3896241)). Qed.
Lemma lem3896245 : term185 = True.
Proof. exact (TRANS (@lem3896240) (@lem3896244)). Qed.
Lemma lem3896246 : True = term185.
Proof. exact (SYM (@lem3896245)). Qed.
Lemma lem3896247 : term185.
Proof. exact (EQ_MP (@lem3896246) (@lem0)). Qed.
Lemma lem3896248 : term368.
Proof. exact (@lem3896237 (@lem3896247)). Qed.
Lemma lem3896250 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896251 : term185 = term186.
Proof. exact (@lem3896250 (NUMERAL 0) term79). Qed.
Lemma lem3896252 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896253 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896254 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896253 h1) (fun h1 : term186 = True => @lem3896252)). Qed.
Lemma lem3896255 : term186 = True.
Proof. exact (EQ_MP (@lem3896254) (@lem3896252)). Qed.
Lemma lem3896256 : term185 = True.
Proof. exact (TRANS (@lem3896251) (@lem3896255)). Qed.
Lemma lem3896257 : True = term185.
Proof. exact (SYM (@lem3896256)). Qed.
Lemma lem3896258 : term185.
Proof. exact (EQ_MP (@lem3896257) (@lem0)). Qed.
Lemma lem3896259 : term366 = term369.
Proof. exact (@lem3896248 (@lem3896258)). Qed.
Lemma lem3896261 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3896262 : term164 = term169.
Proof. exact (@lem3896261 term79 term79). Qed.
Lemma lem3896263 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896264 : term149 = term79.
Proof. exact (EQ_MP (@lem3896263) (@lem940073)). Qed.
Lemma lem3896265 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896266 : term147 = term78.
Proof. exact (MK_COMB (@lem3896265) (@lem3896264)). Qed.
Lemma lem3896267 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3896268 : term169 = term137.
Proof. exact (MK_COMB (@lem3896267) (@lem3896266)). Qed.
Lemma lem3896269 : term164 = term137.
Proof. exact (TRANS (@lem3896262) (@lem3896268)). Qed.
Lemma lem3896271 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3896272 : term197 = term62.
Proof. exact (@lem3896271 term79). Qed.
Lemma lem3896273 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3896274 : term370 = term64.
Proof. exact (MK_COMB (@lem3896273) (@lem3896272)). Qed.
Lemma lem3896275 : term369 = term364.
Proof. exact (MK_COMB (@lem3896274) (@lem3896269)). Qed.
Lemma lem3896277 (m : nat) (n : nat) : (term371 m n) = (term372 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3896278 : term364 = term373.
Proof. exact (@lem3896277 (NUMERAL 0) term79). Qed.
Lemma lem3896279 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896280 (h1 : term187 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3896281 : (term187 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896280 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem3896279)). Qed.
Lemma lem3896282 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3896281) (@lem3896279)). Qed.
Lemma lem3896283 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3896284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3896285 : term374 = (and True).
Proof. exact (MK_COMB (@lem3896284) (@lem3896283)). Qed.
Lemma lem3896286 : term373 = (True /\ False).
Proof. exact (MK_COMB (@lem3896285) (@lem3896282)). Qed.
Lemma lem3896288 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3896289 : term373 = False.
Proof. exact (TRANS (@lem3896286) (@lem3896288)). Qed.
Lemma lem3896290 : term364 = False.
Proof. exact (TRANS (@lem3896278) (@lem3896289)). Qed.
Lemma lem3896291 : term369 = False.
Proof. exact (TRANS (@lem3896275) (@lem3896290)). Qed.
Lemma lem3896292 : term366 = False.
Proof. exact (TRANS (@lem3896259) (@lem3896291)). Qed.
Lemma lem3896293 : term364 = False.
Proof. exact (TRANS (@lem3896236) (@lem3896292)). Qed.
Lemma lem3896294 : term363 = False.
Proof. exact (TRANS (@lem3896227) (@lem3896293)). Qed.
Lemma lem3896295 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : False.
Proof. exact (EQ_MP (@lem3896294) (@lem3896224 _45282 _45283 h1)). Qed.
Lemma lem3896296 (_45282 : int) (_45283 : int) (h1 : term313 _45282 _45283) : False.
Proof. exact (or_elim (@lem3895717 _45282 _45283 h1) (fun h0 : term400 _45282 _45283 => @lem3896006 _45282 _45283 h0) (fun h0 : term404 _45282 _45283 => @lem3896295 _45282 _45283 h0)). Qed.
Lemma lem3896297 (_45282 : int) (_45283 : int) (h1 : term309 _45282 _45283) : term309 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3896298 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term404 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3896299 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term310 _45283.
Proof. exact (proj2 (@lem3896298 _45282 _45283 h1)). Qed.
Lemma lem3896301 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term283 _45283.
Proof. exact (proj2 (@lem3896299 _45282 _45283 h1)). Qed.
Lemma lem3896303 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : (real_of_int _45283) = term62.
Proof. exact (proj2 (@lem3896301 _45282 _45283 h1)). Qed.
Lemma lem3896304 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term222 _45283.
Proof. exact (proj1 (@lem3896301 _45282 _45283 h1)). Qed.
Lemma lem3896306 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3896307 : term332 = term185.
Proof. exact (@lem3896306 term62 term78). Qed.
Lemma lem3896309 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3896310 : term78 = term163.
Proof. exact (@lem3896309 term79). Qed.
Lemma lem3896312 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3896313 : term62 = term134.
Proof. exact (@lem3896312 (NUMERAL 0)). Qed.
Lemma lem3896314 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3896315 : term333 = term334.
Proof. exact (MK_COMB (@lem3896314) (@lem3896313)). Qed.
Lemma lem3896316 : term185 = term335.
Proof. exact (MK_COMB (@lem3896315) (@lem3896310)). Qed.
Lemma lem3896317 : term336.
Proof. exact (@lem1980255 term62 term78 term78 term78). Qed.
Lemma lem3896319 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896320 : term185 = term186.
Proof. exact (@lem3896319 (NUMERAL 0) term79). Qed.
Lemma lem3896321 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896322 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896323 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896322 h1) (fun h1 : term186 = True => @lem3896321)). Qed.
Lemma lem3896324 : term186 = True.
Proof. exact (EQ_MP (@lem3896323) (@lem3896321)). Qed.
Lemma lem3896325 : term185 = True.
Proof. exact (TRANS (@lem3896320) (@lem3896324)). Qed.
Lemma lem3896326 : True = term185.
Proof. exact (SYM (@lem3896325)). Qed.
Lemma lem3896327 : term185.
Proof. exact (EQ_MP (@lem3896326) (@lem0)). Qed.
Lemma lem3896328 : term337.
Proof. exact (@lem3896317 (@lem3896327)). Qed.
Lemma lem3896330 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896331 : term185 = term186.
Proof. exact (@lem3896330 (NUMERAL 0) term79). Qed.
Lemma lem3896332 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896333 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896334 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896333 h1) (fun h1 : term186 = True => @lem3896332)). Qed.
Lemma lem3896335 : term186 = True.
Proof. exact (EQ_MP (@lem3896334) (@lem3896332)). Qed.
Lemma lem3896336 : term185 = True.
Proof. exact (TRANS (@lem3896331) (@lem3896335)). Qed.
Lemma lem3896337 : True = term185.
Proof. exact (SYM (@lem3896336)). Qed.
Lemma lem3896338 : term185.
Proof. exact (EQ_MP (@lem3896337) (@lem0)). Qed.
Lemma lem3896339 : term335 = term338.
Proof. exact (@lem3896328 (@lem3896338)). Qed.
Lemma lem3896341 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3896342 : term146 = term147.
Proof. exact (@lem3896341 term79 term79). Qed.
Lemma lem3896343 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896344 : term149 = term79.
Proof. exact (EQ_MP (@lem3896343) (@lem940073)). Qed.
Lemma lem3896345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896346 : term147 = term78.
Proof. exact (MK_COMB (@lem3896345) (@lem3896344)). Qed.
Lemma lem3896347 : term146 = term78.
Proof. exact (TRANS (@lem3896342) (@lem3896346)). Qed.
Lemma lem3896349 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3896350 : term197 = term62.
Proof. exact (@lem3896349 term79). Qed.
Lemma lem3896351 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3896352 : term339 = term333.
Proof. exact (MK_COMB (@lem3896351) (@lem3896350)). Qed.
Lemma lem3896353 : term338 = term185.
Proof. exact (MK_COMB (@lem3896352) (@lem3896347)). Qed.
Lemma lem3896355 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896356 : term185 = term186.
Proof. exact (@lem3896355 (NUMERAL 0) term79). Qed.
Lemma lem3896357 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896358 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896359 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896358 h1) (fun h1 : term186 = True => @lem3896357)). Qed.
Lemma lem3896360 : term186 = True.
Proof. exact (EQ_MP (@lem3896359) (@lem3896357)). Qed.
Lemma lem3896361 : term185 = True.
Proof. exact (TRANS (@lem3896356) (@lem3896360)). Qed.
Lemma lem3896362 : term338 = True.
Proof. exact (TRANS (@lem3896353) (@lem3896361)). Qed.
Lemma lem3896363 : term335 = True.
Proof. exact (TRANS (@lem3896339) (@lem3896362)). Qed.
Lemma lem3896364 : term185 = True.
Proof. exact (TRANS (@lem3896316) (@lem3896363)). Qed.
Lemma lem3896365 : term332 = True.
Proof. exact (TRANS (@lem3896307) (@lem3896364)). Qed.
Lemma lem3896366 : True = term332.
Proof. exact (SYM (@lem3896365)). Qed.
Lemma lem3896367 : term332.
Proof. exact (EQ_MP (@lem3896366) (@lem0)). Qed.
Lemma lem3896368 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term376 _45283.
Proof. exact (conj (@lem3896367) (@lem3896304 _45282 _45283 h1)). Qed.
Lemma lem3896370 (x : real) (y : real) : term341 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3896371 (_45283 : int) : term377 _45283.
Proof. exact (@lem3896370 term78 (term173 _45283)). Qed.
Lemma lem3896372 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term378 _45283.
Proof. exact (@lem3896371 _45283 (@lem3896368 _45282 _45283 h1)). Qed.
Lemma lem3896373 (_45283 : int) : (term379 _45283) = (term173 _45283).
Proof. exact (@lem1982733 (term173 _45283)). Qed.
Lemma lem3896374 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3896375 (_45283 : int) : (term380 _45283) = (term221 _45283).
Proof. exact (MK_COMB (@lem3896374) (@lem3896373 _45283)). Qed.
Lemma lem3896376 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3896377 (_45283 : int) : (term378 _45283) = (term222 _45283).
Proof. exact (MK_COMB (@lem3896375 _45283) (@lem3896376)). Qed.
Lemma lem3896378 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term222 _45283.
Proof. exact (EQ_MP (@lem3896377 _45283) (@lem3896372 _45282 _45283 h1)). Qed.
Lemma lem3896380 (y : real) : term346 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3896381 (_45283 : int) : term401 _45283.
Proof. exact (@lem3896380 (real_of_int _45283)). Qed.
Lemma lem3896382 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term402 _45283.
Proof. exact (@lem3896381 _45283 (@lem3896303 _45282 _45283 h1)). Qed.
Lemma lem3896383 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term405 _45283.
Proof. exact (@lem3896382 _45282 _45283 h1 term78). Qed.
Lemma lem3896384 (_45283 : int) : (term405 _45283) = ((term392 _45283) = term62).
Proof. exact (eq_refl (term405 _45283)). Qed.
Lemma lem3896385 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : (term392 _45283) = term62.
Proof. exact (EQ_MP (@lem3896384 _45283) (@lem3896383 _45282 _45283 h1)). Qed.
Lemma lem3896386 (_45283 : int) : (term392 _45283) = (real_of_int _45283).
Proof. exact (@lem1982733 (real_of_int _45283)). Qed.
Lemma lem3896387 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3896388 (_45283 : int) : (term406 _45283) = (term120 _45283).
Proof. exact (MK_COMB (@lem3896387) (@lem3896386 _45283)). Qed.
Lemma lem3896389 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3896390 (_45283 : int) : ((term392 _45283) = term62) = ((real_of_int _45283) = term62).
Proof. exact (MK_COMB (@lem3896388 _45283) (@lem3896389)). Qed.
Lemma lem3896391 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : (real_of_int _45283) = term62.
Proof. exact (EQ_MP (@lem3896390 _45283) (@lem3896385 _45282 _45283 h1)). Qed.
Lemma lem3896392 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term394 _45283.
Proof. exact (conj (@lem3896391 _45282 _45283 h1) (@lem3896378 _45282 _45283 h1)). Qed.
Lemma lem3896394 (x : real) (y : real) : term353 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3896395 (_45283 : int) : term395 _45283.
Proof. exact (@lem3896394 (real_of_int _45283) (term173 _45283)). Qed.
Lemma lem3896396 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term396 _45283.
Proof. exact (@lem3896395 _45283 (@lem3896392 _45282 _45283 h1)). Qed.
Lemma lem3896397 (_45283 : int) : (term397 _45283) = (term398 _45283).
Proof. exact (@lem1982763 (real_of_int _45283) (term176 _45283) term137). Qed.
Lemma lem3896398 (_45283 : int) : (term177 _45283) = (term178 _45283).
Proof. exact (@lem1982715 term137 (real_of_int _45283)). Qed.
Lemma lem3896400 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3896401 : term78 = term163.
Proof. exact (@lem3896400 term79). Qed.
Lemma lem3896403 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3896404 : term137 = term138.
Proof. exact (@lem3896403 term79). Qed.
Lemma lem3896405 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3896406 : term179 = term180.
Proof. exact (MK_COMB (@lem3896405) (@lem3896404)). Qed.
Lemma lem3896407 : term181 = term182.
Proof. exact (MK_COMB (@lem3896406) (@lem3896401)). Qed.
Lemma lem3896408 : term183.
Proof. exact (@lem1981473 term137 term78 term78 term78 term62 term78). Qed.
Lemma lem3896410 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896411 : term185 = term186.
Proof. exact (@lem3896410 (NUMERAL 0) term79). Qed.
Lemma lem3896412 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896413 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896414 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896413 h1) (fun h1 : term186 = True => @lem3896412)). Qed.
Lemma lem3896415 : term186 = True.
Proof. exact (EQ_MP (@lem3896414) (@lem3896412)). Qed.
Lemma lem3896416 : term185 = True.
Proof. exact (TRANS (@lem3896411) (@lem3896415)). Qed.
Lemma lem3896417 : True = term185.
Proof. exact (SYM (@lem3896416)). Qed.
Lemma lem3896418 : term185.
Proof. exact (EQ_MP (@lem3896417) (@lem0)). Qed.
Lemma lem3896419 : term188.
Proof. exact (@lem3896408 (@lem3896418)). Qed.
Lemma lem3896421 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896422 : term185 = term186.
Proof. exact (@lem3896421 (NUMERAL 0) term79). Qed.
Lemma lem3896423 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896424 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896425 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896424 h1) (fun h1 : term186 = True => @lem3896423)). Qed.
Lemma lem3896426 : term186 = True.
Proof. exact (EQ_MP (@lem3896425) (@lem3896423)). Qed.
Lemma lem3896427 : term185 = True.
Proof. exact (TRANS (@lem3896422) (@lem3896426)). Qed.
Lemma lem3896428 : True = term185.
Proof. exact (SYM (@lem3896427)). Qed.
Lemma lem3896429 : term185.
Proof. exact (EQ_MP (@lem3896428) (@lem0)). Qed.
Lemma lem3896430 : term189.
Proof. exact (@lem3896419 (@lem3896429)). Qed.
Lemma lem3896432 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896433 : term185 = term186.
Proof. exact (@lem3896432 (NUMERAL 0) term79). Qed.
Lemma lem3896434 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896435 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896436 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896435 h1) (fun h1 : term186 = True => @lem3896434)). Qed.
Lemma lem3896437 : term186 = True.
Proof. exact (EQ_MP (@lem3896436) (@lem3896434)). Qed.
Lemma lem3896438 : term185 = True.
Proof. exact (TRANS (@lem3896433) (@lem3896437)). Qed.
Lemma lem3896439 : True = term185.
Proof. exact (SYM (@lem3896438)). Qed.
Lemma lem3896440 : term185.
Proof. exact (EQ_MP (@lem3896439) (@lem0)). Qed.
Lemma lem3896441 : term190.
Proof. exact (@lem3896430 (@lem3896440)). Qed.
Lemma lem3896443 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3896444 : term146 = term147.
Proof. exact (@lem3896443 term79 term79). Qed.
Lemma lem3896445 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896446 : term149 = term79.
Proof. exact (EQ_MP (@lem3896445) (@lem940073)). Qed.
Lemma lem3896447 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896448 : term147 = term78.
Proof. exact (MK_COMB (@lem3896447) (@lem3896446)). Qed.
Lemma lem3896449 : term146 = term78.
Proof. exact (TRANS (@lem3896444) (@lem3896448)). Qed.
Lemma lem3896451 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3896452 : term164 = term169.
Proof. exact (@lem3896451 term79 term79). Qed.
Lemma lem3896453 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896454 : term149 = term79.
Proof. exact (EQ_MP (@lem3896453) (@lem940073)). Qed.
Lemma lem3896455 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896456 : term147 = term78.
Proof. exact (MK_COMB (@lem3896455) (@lem3896454)). Qed.
Lemma lem3896457 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3896458 : term169 = term137.
Proof. exact (MK_COMB (@lem3896457) (@lem3896456)). Qed.
Lemma lem3896459 : term164 = term137.
Proof. exact (TRANS (@lem3896452) (@lem3896458)). Qed.
Lemma lem3896460 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3896461 : term191 = term179.
Proof. exact (MK_COMB (@lem3896460) (@lem3896459)). Qed.
Lemma lem3896462 : term192 = term181.
Proof. exact (MK_COMB (@lem3896461) (@lem3896449)). Qed.
Lemma lem3896464 (m : nat) : (term193 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3896465 : term181 = term62.
Proof. exact (@lem3896464 term79). Qed.
Lemma lem3896466 : term192 = term62.
Proof. exact (TRANS (@lem3896462) (@lem3896465)). Qed.
Lemma lem3896467 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3896468 : term194 = term195.
Proof. exact (MK_COMB (@lem3896467) (@lem3896466)). Qed.
Lemma lem3896469 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem3896470 : term196 = term197.
Proof. exact (MK_COMB (@lem3896468) (@lem3896469)). Qed.
Lemma lem3896472 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3896473 : term197 = term62.
Proof. exact (@lem3896472 term79). Qed.
Lemma lem3896474 : term196 = term62.
Proof. exact (TRANS (@lem3896470) (@lem3896473)). Qed.
Lemma lem3896476 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3896477 : term146 = term147.
Proof. exact (@lem3896476 term79 term79). Qed.
Lemma lem3896478 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896479 : term149 = term79.
Proof. exact (EQ_MP (@lem3896478) (@lem940073)). Qed.
Lemma lem3896480 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896481 : term147 = term78.
Proof. exact (MK_COMB (@lem3896480) (@lem3896479)). Qed.
Lemma lem3896482 : term146 = term78.
Proof. exact (TRANS (@lem3896477) (@lem3896481)). Qed.
Lemma lem3896483 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem3896484 : term199 = term197.
Proof. exact (MK_COMB (@lem3896483) (@lem3896482)). Qed.
Lemma lem3896486 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3896487 : term197 = term62.
Proof. exact (@lem3896486 term79). Qed.
Lemma lem3896488 : term199 = term62.
Proof. exact (TRANS (@lem3896484) (@lem3896487)). Qed.
Lemma lem3896489 : term62 = term199.
Proof. exact (SYM (@lem3896488)). Qed.
Lemma lem3896490 : term196 = term199.
Proof. exact (TRANS (@lem3896474) (@lem3896489)). Qed.
Lemma lem3896491 : term182 = term134.
Proof. exact (@lem3896441 (@lem3896490)). Qed.
Lemma lem3896492 : term181 = term134.
Proof. exact (TRANS (@lem3896407) (@lem3896491)). Qed.
Lemma lem3896494 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3896495 : term134 = term62.
Proof. exact (@lem3896494 term62). Qed.
Lemma lem3896496 : term181 = term62.
Proof. exact (TRANS (@lem3896492) (@lem3896495)). Qed.
Lemma lem3896497 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3896498 : term200 = term195.
Proof. exact (MK_COMB (@lem3896497) (@lem3896496)). Qed.
Lemma lem3896499 (_45283 : int) : (real_of_int _45283) = (real_of_int _45283).
Proof. exact (eq_refl (real_of_int _45283)). Qed.
Lemma lem3896500 (_45283 : int) : (term178 _45283) = (term201 _45283).
Proof. exact (MK_COMB (@lem3896498) (@lem3896499 _45283)). Qed.
Lemma lem3896501 (_45283 : int) : (term177 _45283) = (term201 _45283).
Proof. exact (TRANS (@lem3896398 _45283) (@lem3896500 _45283)). Qed.
Lemma lem3896502 (_45283 : int) : (term201 _45283) = term62.
Proof. exact (@lem1982719 (real_of_int _45283)). Qed.
Lemma lem3896503 (_45283 : int) : (term177 _45283) = term62.
Proof. exact (TRANS (@lem3896501 _45283) (@lem3896502 _45283)). Qed.
Lemma lem3896504 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3896505 (_45283 : int) : (term202 _45283) = term111.
Proof. exact (MK_COMB (@lem3896504) (@lem3896503 _45283)). Qed.
Lemma lem3896506 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem3896507 (_45283 : int) : (term398 _45283) = term360.
Proof. exact (MK_COMB (@lem3896505 _45283) (@lem3896506)). Qed.
Lemma lem3896508 (_45283 : int) : (term397 _45283) = term360.
Proof. exact (TRANS (@lem3896397 _45283) (@lem3896507 _45283)). Qed.
Lemma lem3896509 : term360 = term137.
Proof. exact (@lem1982721 term137). Qed.
Lemma lem3896510 (_45283 : int) : (term397 _45283) = term137.
Proof. exact (TRANS (@lem3896508 _45283) (@lem3896509)). Qed.
Lemma lem3896511 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3896512 (_45283 : int) : (term399 _45283) = term362.
Proof. exact (MK_COMB (@lem3896511) (@lem3896510 _45283)). Qed.
Lemma lem3896513 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3896514 (_45283 : int) : (term396 _45283) = term363.
Proof. exact (MK_COMB (@lem3896512 _45283) (@lem3896513)). Qed.
Lemma lem3896515 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : term363.
Proof. exact (EQ_MP (@lem3896514 _45283) (@lem3896396 _45282 _45283 h1)). Qed.
Lemma lem3896517 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3896518 : term363 = term364.
Proof. exact (@lem3896517 term62 term137). Qed.
Lemma lem3896520 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3896521 : term137 = term138.
Proof. exact (@lem3896520 term79). Qed.
Lemma lem3896523 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3896524 : term62 = term134.
Proof. exact (@lem3896523 (NUMERAL 0)). Qed.
Lemma lem3896525 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3896526 : term64 = term365.
Proof. exact (MK_COMB (@lem3896525) (@lem3896524)). Qed.
Lemma lem3896527 : term364 = term366.
Proof. exact (MK_COMB (@lem3896526) (@lem3896521)). Qed.
Lemma lem3896528 : term367.
Proof. exact (@lem1980026 term62 term78 term137 term78). Qed.
Lemma lem3896530 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896531 : term185 = term186.
Proof. exact (@lem3896530 (NUMERAL 0) term79). Qed.
Lemma lem3896532 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896533 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896534 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896533 h1) (fun h1 : term186 = True => @lem3896532)). Qed.
Lemma lem3896535 : term186 = True.
Proof. exact (EQ_MP (@lem3896534) (@lem3896532)). Qed.
Lemma lem3896536 : term185 = True.
Proof. exact (TRANS (@lem3896531) (@lem3896535)). Qed.
Lemma lem3896537 : True = term185.
Proof. exact (SYM (@lem3896536)). Qed.
Lemma lem3896538 : term185.
Proof. exact (EQ_MP (@lem3896537) (@lem0)). Qed.
Lemma lem3896539 : term368.
Proof. exact (@lem3896528 (@lem3896538)). Qed.
Lemma lem3896541 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896542 : term185 = term186.
Proof. exact (@lem3896541 (NUMERAL 0) term79). Qed.
Lemma lem3896543 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896544 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896545 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896544 h1) (fun h1 : term186 = True => @lem3896543)). Qed.
Lemma lem3896546 : term186 = True.
Proof. exact (EQ_MP (@lem3896545) (@lem3896543)). Qed.
Lemma lem3896547 : term185 = True.
Proof. exact (TRANS (@lem3896542) (@lem3896546)). Qed.
Lemma lem3896548 : True = term185.
Proof. exact (SYM (@lem3896547)). Qed.
Lemma lem3896549 : term185.
Proof. exact (EQ_MP (@lem3896548) (@lem0)). Qed.
Lemma lem3896550 : term366 = term369.
Proof. exact (@lem3896539 (@lem3896549)). Qed.
Lemma lem3896552 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3896553 : term164 = term169.
Proof. exact (@lem3896552 term79 term79). Qed.
Lemma lem3896554 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896555 : term149 = term79.
Proof. exact (EQ_MP (@lem3896554) (@lem940073)). Qed.
Lemma lem3896556 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896557 : term147 = term78.
Proof. exact (MK_COMB (@lem3896556) (@lem3896555)). Qed.
Lemma lem3896558 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3896559 : term169 = term137.
Proof. exact (MK_COMB (@lem3896558) (@lem3896557)). Qed.
Lemma lem3896560 : term164 = term137.
Proof. exact (TRANS (@lem3896553) (@lem3896559)). Qed.
Lemma lem3896562 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3896563 : term197 = term62.
Proof. exact (@lem3896562 term79). Qed.
Lemma lem3896564 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3896565 : term370 = term64.
Proof. exact (MK_COMB (@lem3896564) (@lem3896563)). Qed.
Lemma lem3896566 : term369 = term364.
Proof. exact (MK_COMB (@lem3896565) (@lem3896560)). Qed.
Lemma lem3896568 (m : nat) (n : nat) : (term371 m n) = (term372 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3896569 : term364 = term373.
Proof. exact (@lem3896568 (NUMERAL 0) term79). Qed.
Lemma lem3896570 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896571 (h1 : term187 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3896572 : (term187 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896571 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem3896570)). Qed.
Lemma lem3896573 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3896572) (@lem3896570)). Qed.
Lemma lem3896574 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3896575 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3896576 : term374 = (and True).
Proof. exact (MK_COMB (@lem3896575) (@lem3896574)). Qed.
Lemma lem3896577 : term373 = (True /\ False).
Proof. exact (MK_COMB (@lem3896576) (@lem3896573)). Qed.
Lemma lem3896579 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3896580 : term373 = False.
Proof. exact (TRANS (@lem3896577) (@lem3896579)). Qed.
Lemma lem3896581 : term364 = False.
Proof. exact (TRANS (@lem3896569) (@lem3896580)). Qed.
Lemma lem3896582 : term369 = False.
Proof. exact (TRANS (@lem3896566) (@lem3896581)). Qed.
Lemma lem3896583 : term366 = False.
Proof. exact (TRANS (@lem3896550) (@lem3896582)). Qed.
Lemma lem3896584 : term364 = False.
Proof. exact (TRANS (@lem3896527) (@lem3896583)). Qed.
Lemma lem3896585 : term363 = False.
Proof. exact (TRANS (@lem3896518) (@lem3896584)). Qed.
Lemma lem3896586 (_45282 : int) (_45283 : int) (h1 : term404 _45282 _45283) : False.
Proof. exact (EQ_MP (@lem3896585) (@lem3896515 _45282 _45283 h1)). Qed.
Lemma lem3896587 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term400 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3896588 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term311 _45283.
Proof. exact (proj2 (@lem3896587 _45282 _45283 h1)). Qed.
Lemma lem3896590 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term284 _45283.
Proof. exact (proj2 (@lem3896588 _45282 _45283 h1)). Qed.
Lemma lem3896592 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : (real_of_int _45283) = term62.
Proof. exact (proj2 (@lem3896590 _45282 _45283 h1)). Qed.
Lemma lem3896593 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term207 _45283.
Proof. exact (proj1 (@lem3896590 _45282 _45283 h1)). Qed.
Lemma lem3896595 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3896596 : term332 = term185.
Proof. exact (@lem3896595 term62 term78). Qed.
Lemma lem3896598 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3896599 : term78 = term163.
Proof. exact (@lem3896598 term79). Qed.
Lemma lem3896601 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3896602 : term62 = term134.
Proof. exact (@lem3896601 (NUMERAL 0)). Qed.
Lemma lem3896603 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3896604 : term333 = term334.
Proof. exact (MK_COMB (@lem3896603) (@lem3896602)). Qed.
Lemma lem3896605 : term185 = term335.
Proof. exact (MK_COMB (@lem3896604) (@lem3896599)). Qed.
Lemma lem3896606 : term336.
Proof. exact (@lem1980255 term62 term78 term78 term78). Qed.
Lemma lem3896608 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896609 : term185 = term186.
Proof. exact (@lem3896608 (NUMERAL 0) term79). Qed.
Lemma lem3896610 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896611 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896612 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896611 h1) (fun h1 : term186 = True => @lem3896610)). Qed.
Lemma lem3896613 : term186 = True.
Proof. exact (EQ_MP (@lem3896612) (@lem3896610)). Qed.
Lemma lem3896614 : term185 = True.
Proof. exact (TRANS (@lem3896609) (@lem3896613)). Qed.
Lemma lem3896615 : True = term185.
Proof. exact (SYM (@lem3896614)). Qed.
Lemma lem3896616 : term185.
Proof. exact (EQ_MP (@lem3896615) (@lem0)). Qed.
Lemma lem3896617 : term337.
Proof. exact (@lem3896606 (@lem3896616)). Qed.
Lemma lem3896619 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896620 : term185 = term186.
Proof. exact (@lem3896619 (NUMERAL 0) term79). Qed.
Lemma lem3896621 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896622 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896623 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896622 h1) (fun h1 : term186 = True => @lem3896621)). Qed.
Lemma lem3896624 : term186 = True.
Proof. exact (EQ_MP (@lem3896623) (@lem3896621)). Qed.
Lemma lem3896625 : term185 = True.
Proof. exact (TRANS (@lem3896620) (@lem3896624)). Qed.
Lemma lem3896626 : True = term185.
Proof. exact (SYM (@lem3896625)). Qed.
Lemma lem3896627 : term185.
Proof. exact (EQ_MP (@lem3896626) (@lem0)). Qed.
Lemma lem3896628 : term335 = term338.
Proof. exact (@lem3896617 (@lem3896627)). Qed.
Lemma lem3896630 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3896631 : term146 = term147.
Proof. exact (@lem3896630 term79 term79). Qed.
Lemma lem3896632 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896633 : term149 = term79.
Proof. exact (EQ_MP (@lem3896632) (@lem940073)). Qed.
Lemma lem3896634 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896635 : term147 = term78.
Proof. exact (MK_COMB (@lem3896634) (@lem3896633)). Qed.
Lemma lem3896636 : term146 = term78.
Proof. exact (TRANS (@lem3896631) (@lem3896635)). Qed.
Lemma lem3896638 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3896639 : term197 = term62.
Proof. exact (@lem3896638 term79). Qed.
Lemma lem3896640 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3896641 : term339 = term333.
Proof. exact (MK_COMB (@lem3896640) (@lem3896639)). Qed.
Lemma lem3896642 : term338 = term185.
Proof. exact (MK_COMB (@lem3896641) (@lem3896636)). Qed.
Lemma lem3896644 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896645 : term185 = term186.
Proof. exact (@lem3896644 (NUMERAL 0) term79). Qed.
Lemma lem3896646 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896647 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896648 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896647 h1) (fun h1 : term186 = True => @lem3896646)). Qed.
Lemma lem3896649 : term186 = True.
Proof. exact (EQ_MP (@lem3896648) (@lem3896646)). Qed.
Lemma lem3896650 : term185 = True.
Proof. exact (TRANS (@lem3896645) (@lem3896649)). Qed.
Lemma lem3896651 : term338 = True.
Proof. exact (TRANS (@lem3896642) (@lem3896650)). Qed.
Lemma lem3896652 : term335 = True.
Proof. exact (TRANS (@lem3896628) (@lem3896651)). Qed.
Lemma lem3896653 : term185 = True.
Proof. exact (TRANS (@lem3896605) (@lem3896652)). Qed.
Lemma lem3896654 : term332 = True.
Proof. exact (TRANS (@lem3896596) (@lem3896653)). Qed.
Lemma lem3896655 : True = term332.
Proof. exact (SYM (@lem3896654)). Qed.
Lemma lem3896656 : term332.
Proof. exact (EQ_MP (@lem3896655) (@lem0)). Qed.
Lemma lem3896657 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term340 _45283.
Proof. exact (conj (@lem3896656) (@lem3896593 _45282 _45283 h1)). Qed.
Lemma lem3896659 (x : real) (y : real) : term341 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3896660 (_45283 : int) : term342 _45283.
Proof. exact (@lem3896659 term78 (term203 _45283)). Qed.
Lemma lem3896661 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term343 _45283.
Proof. exact (@lem3896660 _45283 (@lem3896657 _45282 _45283 h1)). Qed.
Lemma lem3896662 (_45283 : int) : (term344 _45283) = (term203 _45283).
Proof. exact (@lem1982733 (term203 _45283)). Qed.
Lemma lem3896663 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3896664 (_45283 : int) : (term345 _45283) = (term206 _45283).
Proof. exact (MK_COMB (@lem3896663) (@lem3896662 _45283)). Qed.
Lemma lem3896665 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3896666 (_45283 : int) : (term343 _45283) = (term207 _45283).
Proof. exact (MK_COMB (@lem3896664 _45283) (@lem3896665)). Qed.
Lemma lem3896667 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term207 _45283.
Proof. exact (EQ_MP (@lem3896666 _45283) (@lem3896661 _45282 _45283 h1)). Qed.
Lemma lem3896669 (y : real) : term346 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3896670 (_45283 : int) : term401 _45283.
Proof. exact (@lem3896669 (real_of_int _45283)). Qed.
Lemma lem3896671 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term402 _45283.
Proof. exact (@lem3896670 _45283 (@lem3896592 _45282 _45283 h1)). Qed.
Lemma lem3896672 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term403 _45283.
Proof. exact (@lem3896671 _45282 _45283 h1 term137). Qed.
Lemma lem3896673 (_45283 : int) : (term403 _45283) = ((term176 _45283) = term62).
Proof. exact (eq_refl (term403 _45283)). Qed.
Lemma lem3896680 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : (term176 _45283) = term62.
Proof. exact (EQ_MP (@lem3896673 _45283) (@lem3896672 _45282 _45283 h1)). Qed.
Lemma lem3896681 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term352 _45283.
Proof. exact (conj (@lem3896680 _45282 _45283 h1) (@lem3896667 _45282 _45283 h1)). Qed.
Lemma lem3896683 (x : real) (y : real) : term353 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3896684 (_45283 : int) : term354 _45283.
Proof. exact (@lem3896683 (term176 _45283) (term203 _45283)). Qed.
Lemma lem3896685 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term355 _45283.
Proof. exact (@lem3896684 _45283 (@lem3896681 _45282 _45283 h1)). Qed.
Lemma lem3896686 (_45283 : int) : (term356 _45283) = (term357 _45283).
Proof. exact (@lem1982763 (term176 _45283) (real_of_int _45283) term137). Qed.
Lemma lem3896687 (_45283 : int) : (term358 _45283) = (term178 _45283).
Proof. exact (@lem1982713 term137 (real_of_int _45283)). Qed.
Lemma lem3896689 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3896690 : term78 = term163.
Proof. exact (@lem3896689 term79). Qed.
Lemma lem3896692 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3896693 : term137 = term138.
Proof. exact (@lem3896692 term79). Qed.
Lemma lem3896694 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3896695 : term179 = term180.
Proof. exact (MK_COMB (@lem3896694) (@lem3896693)). Qed.
Lemma lem3896696 : term181 = term182.
Proof. exact (MK_COMB (@lem3896695) (@lem3896690)). Qed.
Lemma lem3896697 : term183.
Proof. exact (@lem1981473 term137 term78 term78 term78 term62 term78). Qed.
Lemma lem3896699 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896700 : term185 = term186.
Proof. exact (@lem3896699 (NUMERAL 0) term79). Qed.
Lemma lem3896701 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896702 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896703 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896702 h1) (fun h1 : term186 = True => @lem3896701)). Qed.
Lemma lem3896704 : term186 = True.
Proof. exact (EQ_MP (@lem3896703) (@lem3896701)). Qed.
Lemma lem3896705 : term185 = True.
Proof. exact (TRANS (@lem3896700) (@lem3896704)). Qed.
Lemma lem3896706 : True = term185.
Proof. exact (SYM (@lem3896705)). Qed.
Lemma lem3896707 : term185.
Proof. exact (EQ_MP (@lem3896706) (@lem0)). Qed.
Lemma lem3896708 : term188.
Proof. exact (@lem3896697 (@lem3896707)). Qed.
Lemma lem3896710 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896711 : term185 = term186.
Proof. exact (@lem3896710 (NUMERAL 0) term79). Qed.
Lemma lem3896712 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896713 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896714 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896713 h1) (fun h1 : term186 = True => @lem3896712)). Qed.
Lemma lem3896715 : term186 = True.
Proof. exact (EQ_MP (@lem3896714) (@lem3896712)). Qed.
Lemma lem3896716 : term185 = True.
Proof. exact (TRANS (@lem3896711) (@lem3896715)). Qed.
Lemma lem3896717 : True = term185.
Proof. exact (SYM (@lem3896716)). Qed.
Lemma lem3896718 : term185.
Proof. exact (EQ_MP (@lem3896717) (@lem0)). Qed.
Lemma lem3896719 : term189.
Proof. exact (@lem3896708 (@lem3896718)). Qed.
Lemma lem3896721 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896722 : term185 = term186.
Proof. exact (@lem3896721 (NUMERAL 0) term79). Qed.
Lemma lem3896723 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896724 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896725 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896724 h1) (fun h1 : term186 = True => @lem3896723)). Qed.
Lemma lem3896726 : term186 = True.
Proof. exact (EQ_MP (@lem3896725) (@lem3896723)). Qed.
Lemma lem3896727 : term185 = True.
Proof. exact (TRANS (@lem3896722) (@lem3896726)). Qed.
Lemma lem3896728 : True = term185.
Proof. exact (SYM (@lem3896727)). Qed.
Lemma lem3896729 : term185.
Proof. exact (EQ_MP (@lem3896728) (@lem0)). Qed.
Lemma lem3896730 : term190.
Proof. exact (@lem3896719 (@lem3896729)). Qed.
Lemma lem3896732 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3896733 : term146 = term147.
Proof. exact (@lem3896732 term79 term79). Qed.
Lemma lem3896734 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896735 : term149 = term79.
Proof. exact (EQ_MP (@lem3896734) (@lem940073)). Qed.
Lemma lem3896736 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896737 : term147 = term78.
Proof. exact (MK_COMB (@lem3896736) (@lem3896735)). Qed.
Lemma lem3896738 : term146 = term78.
Proof. exact (TRANS (@lem3896733) (@lem3896737)). Qed.
Lemma lem3896740 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3896741 : term164 = term169.
Proof. exact (@lem3896740 term79 term79). Qed.
Lemma lem3896742 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896743 : term149 = term79.
Proof. exact (EQ_MP (@lem3896742) (@lem940073)). Qed.
Lemma lem3896744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896745 : term147 = term78.
Proof. exact (MK_COMB (@lem3896744) (@lem3896743)). Qed.
Lemma lem3896746 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3896747 : term169 = term137.
Proof. exact (MK_COMB (@lem3896746) (@lem3896745)). Qed.
Lemma lem3896748 : term164 = term137.
Proof. exact (TRANS (@lem3896741) (@lem3896747)). Qed.
Lemma lem3896749 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3896750 : term191 = term179.
Proof. exact (MK_COMB (@lem3896749) (@lem3896748)). Qed.
Lemma lem3896751 : term192 = term181.
Proof. exact (MK_COMB (@lem3896750) (@lem3896738)). Qed.
Lemma lem3896753 (m : nat) : (term193 m) = term62.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3896754 : term181 = term62.
Proof. exact (@lem3896753 term79). Qed.
Lemma lem3896755 : term192 = term62.
Proof. exact (TRANS (@lem3896751) (@lem3896754)). Qed.
Lemma lem3896756 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3896757 : term194 = term195.
Proof. exact (MK_COMB (@lem3896756) (@lem3896755)). Qed.
Lemma lem3896758 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem3896759 : term196 = term197.
Proof. exact (MK_COMB (@lem3896757) (@lem3896758)). Qed.
Lemma lem3896761 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3896762 : term197 = term62.
Proof. exact (@lem3896761 term79). Qed.
Lemma lem3896763 : term196 = term62.
Proof. exact (TRANS (@lem3896759) (@lem3896762)). Qed.
Lemma lem3896765 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3896766 : term146 = term147.
Proof. exact (@lem3896765 term79 term79). Qed.
Lemma lem3896767 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896768 : term149 = term79.
Proof. exact (EQ_MP (@lem3896767) (@lem940073)). Qed.
Lemma lem3896769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896770 : term147 = term78.
Proof. exact (MK_COMB (@lem3896769) (@lem3896768)). Qed.
Lemma lem3896771 : term146 = term78.
Proof. exact (TRANS (@lem3896766) (@lem3896770)). Qed.
Lemma lem3896772 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem3896773 : term199 = term197.
Proof. exact (MK_COMB (@lem3896772) (@lem3896771)). Qed.
Lemma lem3896775 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3896776 : term197 = term62.
Proof. exact (@lem3896775 term79). Qed.
Lemma lem3896777 : term199 = term62.
Proof. exact (TRANS (@lem3896773) (@lem3896776)). Qed.
Lemma lem3896778 : term62 = term199.
Proof. exact (SYM (@lem3896777)). Qed.
Lemma lem3896779 : term196 = term199.
Proof. exact (TRANS (@lem3896763) (@lem3896778)). Qed.
Lemma lem3896780 : term182 = term134.
Proof. exact (@lem3896730 (@lem3896779)). Qed.
Lemma lem3896781 : term181 = term134.
Proof. exact (TRANS (@lem3896696) (@lem3896780)). Qed.
Lemma lem3896783 (x : real) : (term153 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3896784 : term134 = term62.
Proof. exact (@lem3896783 term62). Qed.
Lemma lem3896785 : term181 = term62.
Proof. exact (TRANS (@lem3896781) (@lem3896784)). Qed.
Lemma lem3896786 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3896787 : term200 = term195.
Proof. exact (MK_COMB (@lem3896786) (@lem3896785)). Qed.
Lemma lem3896788 (_45283 : int) : (real_of_int _45283) = (real_of_int _45283).
Proof. exact (eq_refl (real_of_int _45283)). Qed.
Lemma lem3896789 (_45283 : int) : (term178 _45283) = (term201 _45283).
Proof. exact (MK_COMB (@lem3896787) (@lem3896788 _45283)). Qed.
Lemma lem3896790 (_45283 : int) : (term358 _45283) = (term201 _45283).
Proof. exact (TRANS (@lem3896687 _45283) (@lem3896789 _45283)). Qed.
Lemma lem3896791 (_45283 : int) : (term201 _45283) = term62.
Proof. exact (@lem1982719 (real_of_int _45283)). Qed.
Lemma lem3896792 (_45283 : int) : (term358 _45283) = term62.
Proof. exact (TRANS (@lem3896790 _45283) (@lem3896791 _45283)). Qed.
Lemma lem3896793 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3896794 (_45283 : int) : (term359 _45283) = term111.
Proof. exact (MK_COMB (@lem3896793) (@lem3896792 _45283)). Qed.
Lemma lem3896795 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem3896796 (_45283 : int) : (term357 _45283) = term360.
Proof. exact (MK_COMB (@lem3896794 _45283) (@lem3896795)). Qed.
Lemma lem3896797 (_45283 : int) : (term356 _45283) = term360.
Proof. exact (TRANS (@lem3896686 _45283) (@lem3896796 _45283)). Qed.
Lemma lem3896798 : term360 = term137.
Proof. exact (@lem1982721 term137). Qed.
Lemma lem3896799 (_45283 : int) : (term356 _45283) = term137.
Proof. exact (TRANS (@lem3896797 _45283) (@lem3896798)). Qed.
Lemma lem3896800 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3896801 (_45283 : int) : (term361 _45283) = term362.
Proof. exact (MK_COMB (@lem3896800) (@lem3896799 _45283)). Qed.
Lemma lem3896802 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem3896803 (_45283 : int) : (term355 _45283) = term363.
Proof. exact (MK_COMB (@lem3896801 _45283) (@lem3896802)). Qed.
Lemma lem3896804 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : term363.
Proof. exact (EQ_MP (@lem3896803 _45283) (@lem3896685 _45282 _45283 h1)). Qed.
Lemma lem3896806 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3896807 : term363 = term364.
Proof. exact (@lem3896806 term62 term137). Qed.
Lemma lem3896809 (x : nat) : (term135 x) = (term136 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3896810 : term137 = term138.
Proof. exact (@lem3896809 term79). Qed.
Lemma lem3896812 (x : nat) : (real_of_num x) = (term133 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3896813 : term62 = term134.
Proof. exact (@lem3896812 (NUMERAL 0)). Qed.
Lemma lem3896814 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3896815 : term64 = term365.
Proof. exact (MK_COMB (@lem3896814) (@lem3896813)). Qed.
Lemma lem3896816 : term364 = term366.
Proof. exact (MK_COMB (@lem3896815) (@lem3896810)). Qed.
Lemma lem3896817 : term367.
Proof. exact (@lem1980026 term62 term78 term137 term78). Qed.
Lemma lem3896819 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896820 : term185 = term186.
Proof. exact (@lem3896819 (NUMERAL 0) term79). Qed.
Lemma lem3896821 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896822 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896823 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896822 h1) (fun h1 : term186 = True => @lem3896821)). Qed.
Lemma lem3896824 : term186 = True.
Proof. exact (EQ_MP (@lem3896823) (@lem3896821)). Qed.
Lemma lem3896825 : term185 = True.
Proof. exact (TRANS (@lem3896820) (@lem3896824)). Qed.
Lemma lem3896826 : True = term185.
Proof. exact (SYM (@lem3896825)). Qed.
Lemma lem3896827 : term185.
Proof. exact (EQ_MP (@lem3896826) (@lem0)). Qed.
Lemma lem3896828 : term368.
Proof. exact (@lem3896817 (@lem3896827)). Qed.
Lemma lem3896830 (m : nat) (n : nat) : (term184 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3896831 : term185 = term186.
Proof. exact (@lem3896830 (NUMERAL 0) term79). Qed.
Lemma lem3896832 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896833 (h1 : term187 = (BIT1 0)) : term186 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3896834 : (term187 = (BIT1 0)) = (term186 = True).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896833 h1) (fun h1 : term186 = True => @lem3896832)). Qed.
Lemma lem3896835 : term186 = True.
Proof. exact (EQ_MP (@lem3896834) (@lem3896832)). Qed.
Lemma lem3896836 : term185 = True.
Proof. exact (TRANS (@lem3896831) (@lem3896835)). Qed.
Lemma lem3896837 : True = term185.
Proof. exact (SYM (@lem3896836)). Qed.
Lemma lem3896838 : term185.
Proof. exact (EQ_MP (@lem3896837) (@lem0)). Qed.
Lemma lem3896839 : term366 = term369.
Proof. exact (@lem3896828 (@lem3896838)). Qed.
Lemma lem3896841 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3896842 : term164 = term169.
Proof. exact (@lem3896841 term79 term79). Qed.
Lemma lem3896843 : (term148 = (BIT1 0)) = (term149 = term79).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3896844 : term149 = term79.
Proof. exact (EQ_MP (@lem3896843) (@lem940073)). Qed.
Lemma lem3896845 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3896846 : term147 = term78.
Proof. exact (MK_COMB (@lem3896845) (@lem3896844)). Qed.
Lemma lem3896847 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3896848 : term169 = term137.
Proof. exact (MK_COMB (@lem3896847) (@lem3896846)). Qed.
Lemma lem3896849 : term164 = term137.
Proof. exact (TRANS (@lem3896842) (@lem3896848)). Qed.
Lemma lem3896851 (x : nat) : (term198 x) = term62.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3896852 : term197 = term62.
Proof. exact (@lem3896851 term79). Qed.
Lemma lem3896853 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3896854 : term370 = term64.
Proof. exact (MK_COMB (@lem3896853) (@lem3896852)). Qed.
Lemma lem3896855 : term369 = term364.
Proof. exact (MK_COMB (@lem3896854) (@lem3896849)). Qed.
Lemma lem3896857 (m : nat) (n : nat) : (term371 m n) = (term372 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3896858 : term364 = term373.
Proof. exact (@lem3896857 (NUMERAL 0) term79). Qed.
Lemma lem3896859 : term187 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3896860 (h1 : term187 = (BIT1 0)) : (term79 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3896861 : (term187 = (BIT1 0)) = ((term79 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term187 = (BIT1 0) => @lem3896860 h1) (fun h1 : (term79 = (NUMERAL 0)) = False => @lem3896859)). Qed.
Lemma lem3896862 : (term79 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3896861) (@lem3896859)). Qed.
Lemma lem3896863 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3896864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3896865 : term374 = (and True).
Proof. exact (MK_COMB (@lem3896864) (@lem3896863)). Qed.
Lemma lem3896866 : term373 = (True /\ False).
Proof. exact (MK_COMB (@lem3896865) (@lem3896862)). Qed.
Lemma lem3896868 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3896869 : term373 = False.
Proof. exact (TRANS (@lem3896866) (@lem3896868)). Qed.
Lemma lem3896870 : term364 = False.
Proof. exact (TRANS (@lem3896858) (@lem3896869)). Qed.
Lemma lem3896871 : term369 = False.
Proof. exact (TRANS (@lem3896855) (@lem3896870)). Qed.
Lemma lem3896872 : term366 = False.
Proof. exact (TRANS (@lem3896839) (@lem3896871)). Qed.
Lemma lem3896873 : term364 = False.
Proof. exact (TRANS (@lem3896816) (@lem3896872)). Qed.
Lemma lem3896874 : term363 = False.
Proof. exact (TRANS (@lem3896807) (@lem3896873)). Qed.
Lemma lem3896875 (_45282 : int) (_45283 : int) (h1 : term400 _45282 _45283) : False.
Proof. exact (EQ_MP (@lem3896874) (@lem3896804 _45282 _45283 h1)). Qed.
Lemma lem3896876 (_45282 : int) (_45283 : int) (h1 : term309 _45282 _45283) : False.
Proof. exact (or_elim (@lem3896297 _45282 _45283 h1) (fun h0 : term404 _45282 _45283 => @lem3896586 _45282 _45283 h0) (fun h0 : term400 _45282 _45283 => @lem3896875 _45282 _45283 h0)). Qed.
Lemma lem3896877 (_45282 : int) (_45283 : int) (h1 : term316 _45282 _45283) : False.
Proof. exact (or_elim (@lem3895716 _45282 _45283 h1) (fun h0 : term313 _45282 _45283 => @lem3896296 _45282 _45283 h0) (fun h0 : term309 _45282 _45283 => @lem3896876 _45282 _45283 h0)). Qed.
Lemma lem3896878 (_45282 : int) (_45283 : int) (h1 : term330 _45282 _45283) : False.
Proof. exact (or_elim (@lem3894469 _45282 _45283 h1) (fun h0 : term327 _45282 _45283 => @lem3895715 _45282 _45283 h0) (fun h0 : term316 _45282 _45283 => @lem3896877 _45282 _45283 h0)). Qed.
Lemma lem3896880 (_45282 : int) (_45283 : int) (h1 : term330 _45282 _45283) : term330 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3896881 (_45282 : int) (_45283 : int) (h1 : term330 _45282 _45283) : (term330 _45282 _45283) = False.
Proof. exact (prop_ext (fun h2 : term330 _45282 _45283 => @lem3896878 _45282 _45283 h1) (fun h2 : False => @lem3896880 _45282 _45283 h1)). Qed.
Lemma lem3896882 (_45282 : int) (_45283 : int) (h1 : term330 _45282 _45283) : False.
Proof. exact (EQ_MP (@lem3896881 _45282 _45283 h1) (@lem3896880 _45282 _45283 h1)). Qed.
Lemma lem3896883 (_45282 : int) (_45283 : int) (h1 : term129 _45282 _45283) : term129 _45282 _45283.
Proof. exact (h1). Qed.
Lemma lem3896884 (_45282 : int) (_45283 : int) (h1 : term129 _45282 _45283) : term330 _45282 _45283.
Proof. exact (EQ_MP (@lem3894423 _45282 _45283) (@lem3896883 _45282 _45283 h1)). Qed.
Lemma lem3896885 (_45282 : int) (_45283 : int) (h1 : term129 _45282 _45283) : (term330 _45282 _45283) = False.
Proof. exact (prop_ext (fun h2 : term330 _45282 _45283 => @lem3896882 _45282 _45283 h2) (fun h2 : False => @lem3896884 _45282 _45283 h1)). Qed.
Lemma lem3896886 (_45282 : int) (_45283 : int) (h1 : term129 _45282 _45283) : False.
Proof. exact (EQ_MP (@lem3896885 _45282 _45283 h1) (@lem3896884 _45282 _45283 h1)). Qed.
Lemma lem3896887 (_45282 : int) (_45283 : int) : term407 _45282 _45283.
Proof. exact (fun h0 : term129 _45282 _45283 => @lem3896886 _45282 _45283 h0). Qed.
Lemma lem3896888 (_45282 : int) (_45283 : int) : term408 _45282 _45283.
Proof. exact (@lem1386578 (term409 _45282 _45283)). Qed.
Lemma lem3896891 (_45282 : int) (_45283 : int) : term409 _45282 _45283.
Proof. exact (@lem3896888 _45282 _45283 (@lem3896887 _45282 _45283)). Qed.
Lemma lem3896892 (_45282 : int) (_45283 : int) : (term127 _45282 _45283) = (term56 _45282 _45283).
Proof. exact (SYM (@lem3893355 _45282 _45283)). Qed.
Lemma lem3896893 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3896894 (_45282 : int) (_45283 : int) : (term409 _45282 _45283) = (term28 _45282 _45283).
Proof. exact (MK_COMB (@lem3896893) (@lem3896892 _45282 _45283)). Qed.
Lemma lem3896895 (_45282 : int) (_45283 : int) : term28 _45282 _45283.
Proof. exact (EQ_MP (@lem3896894 _45282 _45283) (@lem3896891 _45282 _45283)). Qed.
Lemma lem3896896 (_45282 : int) (_45283 : int) : term29 _45282 _45283.
Proof. exact (EQ_MP (@lem3893116 _45282 _45283) (@lem3896895 _45282 _45283)). Qed.
Lemma lem3896897 (a : nat) (b : nat) : term410 a b.
Proof. exact (@lem3896896 (int_of_num a) (int_of_num b)). Qed.
Lemma lem3896898 (a : nat) (b : nat) : term411 a b.
Proof. exact (@lem3896897 a b (@lem3893112 a)). Qed.
Lemma lem3896899 (a : nat) (b : nat) : term25 a b.
Proof. exact (@lem3896898 a b (@lem3893115 b)). Qed.
Lemma lem3896900 (a : nat) (b : nat) : (term25 a b) = ((a = (Nat.add a b)) = (b = (NUMERAL 0))).
Proof. exact (SYM (@lem3893109 a b)). Qed.
Lemma lem3896932 {A : Type'} (h1 : term412 A) : term412 A.
Proof. exact (h1). Qed.
Lemma lem3896933 {A : Type'} (s : A -> Prop) (h1 : term412 A) : term413 A s.
Proof. exact (@lem3896932 A h1 s). Qed.
Lemma lem3896934 {A : Type'} (s : A -> Prop) : (term413 A s) = (term414 A s).
Proof. exact (eq_refl (term413 A s)). Qed.
Lemma lem3896935 {A : Type'} (s : A -> Prop) (h1 : term412 A) : term414 A s.
Proof. exact (EQ_MP (@lem3896934 A s) (@lem3896933 A s h1)). Qed.
Lemma lem3896936 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term412 A) : term415 A s t.
Proof. exact (@lem3896935 A s h1 t). Qed.
Lemma lem3896937 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term415 A s t) = (term416 A t s).
Proof. exact (eq_refl (term415 A s t)). Qed.
Lemma lem3896938 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term412 A) : term416 A t s.
Proof. exact (EQ_MP (@lem3896937 A t s) (@lem3896936 A s t h1)). Qed.
Lemma lem3896939 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term417 A s t) : term417 A s t.
Proof. exact (h1). Qed.
Lemma lem3896940 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term412 A) (h2 : term417 A s t) : @FINITE A s.
Proof. exact (@lem3896938 A t s h1 (@lem3896939 A s t h2)). Qed.
Lemma lem3896941 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term417 A s t) : term418 A s.
Proof. exact (fun h0 : term412 A => @lem3896940 A s t h0 h1). Qed.
Lemma lem3896942 {A : Type'} (s : A -> Prop) (h1 : term419 A s) : term419 A s.
Proof. exact (h1). Qed.
Lemma lem3896943 {A : Type'} (s : A -> Prop) (h1 : term419 A s) : term418 A s.
Proof. exact (ex_elim (@lem3896942 A s h1) (fun t : A -> Prop => fun h0 : term420 A s t => @lem3896941 A s t h0)). Qed.
Lemma lem3896944 {A : Type'} (h1 : term412 A) : term412 A.
Proof. exact (h1). Qed.
Lemma lem3896945 {A : Type'} (s : A -> Prop) (h1 : term412 A) (h2 : term419 A s) : @FINITE A s.
Proof. exact (@lem3896943 A s h2 (@lem3896944 A h1)). Qed.
Lemma lem3896946 {A : Type'} (s : A -> Prop) (h1 : term412 A) : term421 A s.
Proof. exact (fun h0 : term419 A s => @lem3896945 A s h1 h0). Qed.
Lemma lem3896947 {A : Type'} (h1 : term412 A) : term422 A.
Proof. exact (fun s : A -> Prop => @lem3896946 A s h1). Qed.
Lemma lem3896948 {A : Type'} : term423 A.
Proof. exact (fun h0 : term412 A => @lem3896947 A h0). Qed.
Lemma lem3896949 {A : Type'} : term422 A.
Proof. exact (@lem3896948 A (@lem3599924 A)). Qed.
Lemma lem3896950 {A : Type'} (s : A -> Prop) : term424 A s.
Proof. exact (@lem3896949 A s). Qed.
Lemma lem3896951 {A : Type'} (s : A -> Prop) : (term424 A s) = (term421 A s).
Proof. exact (eq_refl (term424 A s)). Qed.
Lemma lem3896953 (t1 : Prop) : term425 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3896954 (t1 : Prop) : (term425 t1) = (term426 t1).
Proof. exact (eq_refl (term425 t1)). Qed.
Lemma lem3896955 (t1 : Prop) : term426 t1.
Proof. exact (EQ_MP (@lem3896954 t1) (@lem3896953 t1)). Qed.
Lemma lem3896956 (t1 : Prop) (t2 : Prop) : term427 t1 t2.
Proof. exact (@lem3896955 t1 t2). Qed.
Lemma lem3896957 (t1 : Prop) (t2 : Prop) : (term427 t1 t2) = (term428 t1 t2).
Proof. exact (eq_refl (term427 t1 t2)). Qed.
Lemma lem3896958 (t1 : Prop) (t2 : Prop) : term428 t1 t2.
Proof. exact (EQ_MP (@lem3896957 t1 t2) (@lem3896956 t1 t2)). Qed.
Lemma lem3896959 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term429 t1 t2 t3.
Proof. exact (@lem3896958 t1 t2 t3). Qed.
Lemma lem3896960 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term429 t1 t2 t3) = ((term430 t1 t2 t3) = (term431 t1 t2 t3)).
Proof. exact (eq_refl (term429 t1 t2 t3)). Qed.
Lemma lem3896961 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term430 t1 t2 t3) = (term431 t1 t2 t3).
Proof. exact (EQ_MP (@lem3896960 t1 t2 t3) (@lem3896959 t1 t2 t3)). Qed.
Lemma lem3896962 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term431 t1 t2 t3) = (term430 t1 t2 t3).
Proof. exact (SYM (@lem3896961 t1 t2 t3)). Qed.
Lemma lem3896963 {A : Type'} (a : A -> Prop) : term432 A a.
Proof. exact (@lem3843862 A a). Qed.
Lemma lem3896964 {A : Type'} (a : A -> Prop) : (term432 A a) = (term433 A a).
Proof. exact (eq_refl (term432 A a)). Qed.
Lemma lem3896965 {A : Type'} (a : A -> Prop) : term433 A a.
Proof. exact (EQ_MP (@lem3896964 A a) (@lem3896963 A a)). Qed.
Lemma lem3896966 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term434 A b a.
Proof. exact (@lem3896965 A a (@DIFF A b a)). Qed.
Lemma lem3896967 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term434 A b a) = (term435 A b a).
Proof. exact (eq_refl (term434 A b a)). Qed.
Lemma lem3896968 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term435 A b a.
Proof. exact (EQ_MP (@lem3896967 A b a) (@lem3896966 A b a)). Qed.
Lemma lem3896969 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term436 A a b) : term436 A a b.
Proof. exact (h1). Qed.
Lemma lem3896970 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term437 A a b) : term437 A a b.
Proof. exact (h1). Qed.
Lemma lem3896971 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3896972 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (@CARD A a) = (@CARD A b)) : (@CARD A a) = (@CARD A b).
Proof. exact (h1). Qed.
Lemma lem3896973 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : @SUBSET A a b.
Proof. exact (h1). Qed.
Lemma lem3896974 {A : Type'} (a : A -> Prop) (h1 : @FINITE A a) : @FINITE A a.
Proof. exact (h1). Qed.
Lemma lem3896976 (p : Prop) : p = (term438 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3896977 {A : Type'} (a : A -> Prop) : (@FINITE A a) = (term439 A a).
Proof. exact (@lem3896976 (@FINITE A a)). Qed.
Lemma lem3896978 {A : Type'} (a : A -> Prop) : (term439 A a) = (@FINITE A a).
Proof. exact (SYM (@lem3896977 A a)). Qed.
Lemma lem3896979 {A : Type'} (a : A -> Prop) (h1 : term440 A a) : term440 A a.
Proof. exact (h1). Qed.
Lemma lem3896980 {A : Type'} : term412 A.
Proof. exact (@lem3599924 A). Qed.
Lemma lem3896984 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term441 A b a) : term441 A b a.
Proof. exact (h1). Qed.
Lemma lem3896985 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term442 A b a.
Proof. exact (fun h0 : term441 A b a => @lem3896984 A b a h0). Qed.
Lemma lem3896986 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term442 A b a) : term442 A b a.
Proof. exact (h1). Qed.
Lemma lem3896987 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term441 A b a) : term441 A b a.
Proof. exact (h1). Qed.
Lemma lem3896988 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term441 A b a) (h2 : term442 A b a) : term441 A b a.
Proof. exact (@lem3896986 A b a h2 (@lem3896987 A b a h1)). Qed.
Lemma lem3896989 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term441 A b a) : term443 A b a.
Proof. exact (fun h0 : term442 A b a => @lem3896988 A b a h1 h0). Qed.
Lemma lem3896990 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term442 A b a) : term442 A b a.
Proof. exact (h1). Qed.
Lemma lem3896991 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term441 A b a) (h2 : term442 A b a) : term441 A b a.
Proof. exact (@lem3896989 A b a h1 (@lem3896990 A b a h2)). Qed.
Lemma lem3896992 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term442 A b a) : term442 A b a.
Proof. exact (fun h0 : term441 A b a => @lem3896991 A b a h0 h1). Qed.
Lemma lem3896993 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term444 A b a.
Proof. exact (fun h0 : term442 A b a => @lem3896992 A b a h0). Qed.
Lemma lem3896996 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term442 A b a.
Proof. exact (@lem3896993 A b a (@lem3896985 A b a)). Qed.
Lemma lem3896997 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term442 A b a.
Proof. exact (@lem3896996 A b a). Qed.
Lemma lem3897015 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3897016 {A : Type'} : (term445 A) = (term446 A).
Proof. exact (@lem3897015 (term412 A)). Qed.
Lemma lem3897029 {A : Type'} (a : A -> Prop) : (term447 A a) = (term447 A a).
Proof. exact (eq_refl (term447 A a)). Qed.
Lemma lem3897030 {A : Type'} (a : A -> Prop) : (term448 A a) = (term449 A a).
Proof. exact (MK_COMB (@lem3897029 A a) (@lem3897016 A)). Qed.
Lemma lem3897033 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term450 A a b) = (term450 A a b).
Proof. exact (eq_refl (term450 A a b)). Qed.
Lemma lem3897034 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term451 A b a) = (term452 A b a).
Proof. exact (MK_COMB (@lem3897033 A a b) (@lem3897030 A a)). Qed.
Lemma lem3897037 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term453 A a b) = (term453 A a b).
Proof. exact (eq_refl (term453 A a b)). Qed.
Lemma lem3897038 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term454 A b a) = (term455 A b a).
Proof. exact (MK_COMB (@lem3897037 A a b) (@lem3897034 A b a)). Qed.
Lemma lem3897041 {A : Type'} (b : A -> Prop) : (term456 A b) = (term456 A b).
Proof. exact (eq_refl (term456 A b)). Qed.
Lemma lem3897042 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term441 A b a) = (term457 A b a).
Proof. exact (MK_COMB (@lem3897041 A b) (@lem3897038 A b a)). Qed.
Lemma lem3897045 {A : Type'} (a : A -> Prop) : (term458 A a) = (term459 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3897042 A b a)). Qed.
Lemma lem3897046 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897047 {A : Type'} (a : A -> Prop) : (term460 A a) = (term461 A a).
Proof. exact (MK_COMB (@lem3897046 A) (@lem3897045 A a)). Qed.
Lemma lem3897052 {A : Type'} : (term462 A) = (term463 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3897047 A a)). Qed.
Lemma lem3897053 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897062 {A : Type'} : (term464 A) = (term465 A).
Proof. exact (MK_COMB (@lem3897053 A) (@lem3897052 A)). Qed.
Lemma lem3897071 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term416 A t s) = (term416 A t s).
Proof. exact (eq_refl (term416 A t s)). Qed.
Lemma lem3897072 {A : Type'} (s : A -> Prop) : (term466 A s) = (term466 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3897071 A t s)). Qed.
Lemma lem3897073 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897074 {A : Type'} (s : A -> Prop) : (term414 A s) = (term414 A s).
Proof. exact (MK_COMB (@lem3897073 A) (@lem3897072 A s)). Qed.
Lemma lem3897075 {A : Type'} : (term467 A) = (term467 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3897074 A s)). Qed.
Lemma lem3897076 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897077 {A : Type'} : (term412 A) = (term412 A).
Proof. exact (MK_COMB (@lem3897076 A) (@lem3897075 A)). Qed.
Lemma lem3897078 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3897079 {A : Type'} : (term446 A) = (term446 A).
Proof. exact (MK_COMB (@lem3897078) (@lem3897077 A)). Qed.
Lemma lem3897084 {A : Type'} (a : A -> Prop) : (term447 A a) = (term447 A a).
Proof. exact (eq_refl (term447 A a)). Qed.
Lemma lem3897085 {A : Type'} (a : A -> Prop) : (term449 A a) = (term449 A a).
Proof. exact (MK_COMB (@lem3897084 A a) (@lem3897079 A)). Qed.
Lemma lem3897088 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term450 A a b) = (term450 A a b).
Proof. exact (eq_refl (term450 A a b)). Qed.
Lemma lem3897089 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term452 A b a) = (term452 A b a).
Proof. exact (MK_COMB (@lem3897088 A a b) (@lem3897085 A a)). Qed.
Lemma lem3897092 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term453 A a b) = (term453 A a b).
Proof. exact (eq_refl (term453 A a b)). Qed.
Lemma lem3897093 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term455 A b a) = (term455 A b a).
Proof. exact (MK_COMB (@lem3897092 A a b) (@lem3897089 A b a)). Qed.
Lemma lem3897096 {A : Type'} (b : A -> Prop) : (term456 A b) = (term456 A b).
Proof. exact (eq_refl (term456 A b)). Qed.
Lemma lem3897097 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term457 A b a) = (term457 A b a).
Proof. exact (MK_COMB (@lem3897096 A b) (@lem3897093 A b a)). Qed.
Lemma lem3897098 {A : Type'} (a : A -> Prop) : (term459 A a) = (term459 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3897097 A b a)). Qed.
Lemma lem3897099 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897100 {A : Type'} (a : A -> Prop) : (term461 A a) = (term461 A a).
Proof. exact (MK_COMB (@lem3897099 A) (@lem3897098 A a)). Qed.
Lemma lem3897101 {A : Type'} : (term463 A) = (term463 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3897100 A a)). Qed.
Lemma lem3897102 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897103 {A : Type'} : (term465 A) = (term465 A).
Proof. exact (MK_COMB (@lem3897102 A) (@lem3897101 A)). Qed.
Lemma lem3897142 {A : Type'} : (term464 A) = (term465 A).
Proof. exact (TRANS (@lem3897062 A) (@lem3897103 A)). Qed.
Lemma lem3897143 {A : Type'} : (term465 A) = (term464 A).
Proof. exact (SYM (@lem3897142 A)). Qed.
Lemma lem3897148 {A : Type'} (h1 : term412 A) : term412 A.
Proof. exact (h1). Qed.
Lemma lem3897154 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3897160 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : @SUBSET A a b.
Proof. exact (h1). Qed.
Lemma lem3897172 {A : Type'} (a : A -> Prop) (h1 : term440 A a) : term440 A a.
Proof. exact (h1). Qed.
Lemma lem3897179 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term468 A s t) = (term469 A s t).
Proof. exact (@lem17045 (@FINITE A t) (@SUBSET A s t)). Qed.
Lemma lem3897180 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3897181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3897182 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term470 A s t) = (term471 A s t).
Proof. exact (MK_COMB (@lem3897181) (@lem3897179 A s t)). Qed.
Lemma lem3897183 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term472 A t s) = (term473 A t s).
Proof. exact (MK_COMB (@lem3897182 A s t) (@lem3897180 A s)). Qed.
Lemma lem3897184 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term416 A t s) = (term472 A t s).
Proof. exact (@lem17265 (term417 A s t) (@FINITE A s)). Qed.
Lemma lem3897185 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term416 A t s) = (term473 A t s).
Proof. exact (TRANS (@lem3897184 A t s) (@lem3897183 A t s)). Qed.
Lemma lem3897186 {A : Type'} (s : A -> Prop) : (term466 A s) = (term474 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3897185 A t s)). Qed.
Lemma lem3897187 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897188 {A : Type'} (s : A -> Prop) : (term414 A s) = (term475 A s).
Proof. exact (MK_COMB (@lem3897187 A) (@lem3897186 A s)). Qed.
Lemma lem3897189 {A : Type'} : (term467 A) = (term476 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3897188 A s)). Qed.
Lemma lem3897190 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897191 {A : Type'} : (term412 A) = (term477 A).
Proof. exact (MK_COMB (@lem3897190 A) (@lem3897189 A)). Qed.
Lemma lem3897217 {A : Type'} (P : A -> Prop) (Q : Prop) : (term478 A P Q) = (term479 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem3897218 {A : Type'} (P : type686 A) (Q : Prop) : (term480 A P Q) = (term481 A P Q).
Proof. exact (@lem3897217 (A -> Prop) P Q). Qed.
Lemma lem3897219 {A : Type'} (s : A -> Prop) : (term482 A s) = (term483 A s).
Proof. exact (@lem3897218 A (term484 A s) (@FINITE A s)). Qed.
Lemma lem3897220 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term485 A s t) = (term469 A s t).
Proof. exact (eq_refl (term485 A s t)). Qed.
Lemma lem3897221 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3897222 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term486 A s t) = (term471 A s t).
Proof. exact (MK_COMB (@lem3897221) (@lem3897220 A s t)). Qed.
Lemma lem3897223 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3897224 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term487 A t s) = (term473 A t s).
Proof. exact (MK_COMB (@lem3897222 A s t) (@lem3897223 A s)). Qed.
Lemma lem3897225 {A : Type'} (s : A -> Prop) : (term488 A s) = (term474 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3897224 A t s)). Qed.
Lemma lem3897226 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897227 {A : Type'} (s : A -> Prop) : (term482 A s) = (term475 A s).
Proof. exact (MK_COMB (@lem3897226 A) (@lem3897225 A s)). Qed.
Lemma lem3897228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3897229 {A : Type'} (s : A -> Prop) : (term489 A s) = (term490 A s).
Proof. exact (MK_COMB (@lem3897228) (@lem3897227 A s)). Qed.
Lemma lem3897230 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term485 A s t) = (term469 A s t).
Proof. exact (eq_refl (term485 A s t)). Qed.
Lemma lem3897231 {A : Type'} (s : A -> Prop) : (term491 A s) = (term484 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3897230 A s t)). Qed.
Lemma lem3897232 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897233 {A : Type'} (s : A -> Prop) : (term492 A s) = (term493 A s).
Proof. exact (MK_COMB (@lem3897232 A) (@lem3897231 A s)). Qed.
Lemma lem3897234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3897235 {A : Type'} (s : A -> Prop) : (term494 A s) = (term495 A s).
Proof. exact (MK_COMB (@lem3897234) (@lem3897233 A s)). Qed.
Lemma lem3897236 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3897237 {A : Type'} (s : A -> Prop) : (term483 A s) = (term496 A s).
Proof. exact (MK_COMB (@lem3897235 A s) (@lem3897236 A s)). Qed.
Lemma lem3897238 {A : Type'} (s : A -> Prop) : ((term482 A s) = (term483 A s)) = ((term475 A s) = (term496 A s)).
Proof. exact (MK_COMB (@lem3897229 A s) (@lem3897237 A s)). Qed.
Lemma lem3897239 {A : Type'} (s : A -> Prop) : (term475 A s) = (term496 A s).
Proof. exact (EQ_MP (@lem3897238 A s) (@lem3897219 A s)). Qed.
Lemma lem3897288 {A : Type'} : (term476 A) = (term497 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3897239 A s)). Qed.
Lemma lem3897289 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897324 {A : Type'} : (term477 A) = (term498 A).
Proof. exact (MK_COMB (@lem3897289 A) (@lem3897288 A)). Qed.
Lemma lem3897325 {A : Type'} : (term412 A) = (term498 A).
Proof. exact (TRANS (@lem3897191 A) (@lem3897324 A)). Qed.
Lemma lem3897326 {A : Type'} (h1 : term412 A) : term498 A.
Proof. exact (EQ_MP (@lem3897325 A) (@lem3897148 A h1)). Qed.
Lemma lem3897330 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3897336 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : @SUBSET A a b.
Proof. exact (h1). Qed.
Lemma lem3897352 {A : Type'} (a : A -> Prop) (h1 : term440 A a) : term440 A a.
Proof. exact (h1). Qed.
Lemma lem3897355 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3897370 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term469 A s t) = (term469 A s t).
Proof. exact (eq_refl (term469 A s t)). Qed.
Lemma lem3897371 {A : Type'} (s : A -> Prop) : (term484 A s) = (term484 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3897370 A s t)). Qed.
Lemma lem3897372 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897373 {A : Type'} (s : A -> Prop) : (term493 A s) = (term493 A s).
Proof. exact (MK_COMB (@lem3897372 A) (@lem3897371 A s)). Qed.
Lemma lem3897374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3897375 {A : Type'} (s : A -> Prop) : (term495 A s) = (term495 A s).
Proof. exact (MK_COMB (@lem3897374) (@lem3897373 A s)). Qed.
Lemma lem3897376 {A : Type'} (s : A -> Prop) : (term496 A s) = (term496 A s).
Proof. exact (MK_COMB (@lem3897375 A s) (@lem3897355 A s)). Qed.
Lemma lem3897377 {A : Type'} : (term497 A) = (term497 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3897376 A s)). Qed.
Lemma lem3897378 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897379 {A : Type'} : (term498 A) = (term498 A).
Proof. exact (MK_COMB (@lem3897378 A) (@lem3897377 A)). Qed.
Lemma lem3897380 {A : Type'} (h1 : term412 A) : term498 A.
Proof. exact (EQ_MP (@lem3897379 A) (@lem3897326 A h1)). Qed.
Lemma lem3897384 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3897388 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : @SUBSET A a b.
Proof. exact (h1). Qed.
Lemma lem3897396 {A : Type'} (a : A -> Prop) (h1 : term440 A a) : term440 A a.
Proof. exact (h1). Qed.
Lemma lem3897398 {A : Type'} (P : A -> Prop) (Q : Prop) : (term479 A P Q) = (term478 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3897399 {A : Type'} (P : type686 A) (Q : Prop) : (term481 A P Q) = (term480 A P Q).
Proof. exact (@lem3897398 (A -> Prop) P Q). Qed.
Lemma lem3897400 {A : Type'} (s : A -> Prop) : (term483 A s) = (term482 A s).
Proof. exact (@lem3897399 A (term484 A s) (@FINITE A s)). Qed.
Lemma lem3897401 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term485 A s t) = (term469 A s t).
Proof. exact (eq_refl (term485 A s t)). Qed.
Lemma lem3897402 {A : Type'} (s : A -> Prop) : (term491 A s) = (term484 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3897401 A s t)). Qed.
Lemma lem3897403 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897404 {A : Type'} (s : A -> Prop) : (term492 A s) = (term493 A s).
Proof. exact (MK_COMB (@lem3897403 A) (@lem3897402 A s)). Qed.
Lemma lem3897405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3897406 {A : Type'} (s : A -> Prop) : (term494 A s) = (term495 A s).
Proof. exact (MK_COMB (@lem3897405) (@lem3897404 A s)). Qed.
Lemma lem3897407 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3897408 {A : Type'} (s : A -> Prop) : (term483 A s) = (term496 A s).
Proof. exact (MK_COMB (@lem3897406 A s) (@lem3897407 A s)). Qed.
Lemma lem3897409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3897410 {A : Type'} (s : A -> Prop) : (term499 A s) = (term500 A s).
Proof. exact (MK_COMB (@lem3897409) (@lem3897408 A s)). Qed.
Lemma lem3897411 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term485 A s t) = (term469 A s t).
Proof. exact (eq_refl (term485 A s t)). Qed.
Lemma lem3897412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3897413 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term486 A s t) = (term471 A s t).
Proof. exact (MK_COMB (@lem3897412) (@lem3897411 A s t)). Qed.
Lemma lem3897414 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3897415 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term487 A t s) = (term473 A t s).
Proof. exact (MK_COMB (@lem3897413 A s t) (@lem3897414 A s)). Qed.
Lemma lem3897416 {A : Type'} (s : A -> Prop) : (term488 A s) = (term474 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3897415 A t s)). Qed.
Lemma lem3897417 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897418 {A : Type'} (s : A -> Prop) : (term482 A s) = (term475 A s).
Proof. exact (MK_COMB (@lem3897417 A) (@lem3897416 A s)). Qed.
Lemma lem3897419 {A : Type'} (s : A -> Prop) : ((term483 A s) = (term482 A s)) = ((term496 A s) = (term475 A s)).
Proof. exact (MK_COMB (@lem3897410 A s) (@lem3897418 A s)). Qed.
Lemma lem3897420 {A : Type'} (s : A -> Prop) : (term496 A s) = (term475 A s).
Proof. exact (EQ_MP (@lem3897419 A s) (@lem3897400 A s)). Qed.
Lemma lem3897421 {A : Type'} : (term497 A) = (term476 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3897420 A s)). Qed.
Lemma lem3897422 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897423 {A : Type'} : (term498 A) = (term477 A).
Proof. exact (MK_COMB (@lem3897422 A) (@lem3897421 A)). Qed.
Lemma lem3897436 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term473 A t s) = (term473 A t s).
Proof. exact (eq_refl (term473 A t s)). Qed.
Lemma lem3897437 {A : Type'} (s : A -> Prop) : (term474 A s) = (term474 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3897436 A t s)). Qed.
Lemma lem3897438 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897439 {A : Type'} (s : A -> Prop) : (term475 A s) = (term475 A s).
Proof. exact (MK_COMB (@lem3897438 A) (@lem3897437 A s)). Qed.
Lemma lem3897440 {A : Type'} : (term476 A) = (term476 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3897439 A s)). Qed.
Lemma lem3897441 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897442 {A : Type'} : (term477 A) = (term477 A).
Proof. exact (MK_COMB (@lem3897441 A) (@lem3897440 A)). Qed.
Lemma lem3897443 {A : Type'} : (term498 A) = (term477 A).
Proof. exact (TRANS (@lem3897423 A) (@lem3897442 A)). Qed.
Lemma lem3897444 {A : Type'} (h1 : term412 A) : term477 A.
Proof. exact (EQ_MP (@lem3897443 A) (@lem3897380 A h1)). Qed.
Lemma lem3897445 {A : Type'} (_45286 : A -> Prop) (h1 : term412 A) : term501 A _45286.
Proof. exact (@lem3897444 A h1 _45286). Qed.
Lemma lem3897446 {A : Type'} (_45286 : A -> Prop) : (term501 A _45286) = (term475 A _45286).
Proof. exact (eq_refl (term501 A _45286)). Qed.
Lemma lem3897447 {A : Type'} (_45286 : A -> Prop) (h1 : term412 A) : term475 A _45286.
Proof. exact (EQ_MP (@lem3897446 A _45286) (@lem3897445 A _45286 h1)). Qed.
Lemma lem3897448 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) (h1 : term412 A) : term502 A _45286 _45287.
Proof. exact (@lem3897447 A _45286 h1 _45287). Qed.
Lemma lem3897449 {A : Type'} (_45287 : A -> Prop) (_45286 : A -> Prop) : (term502 A _45286 _45287) = (term473 A _45287 _45286).
Proof. exact (eq_refl (term502 A _45286 _45287)). Qed.
Lemma lem3897450 {A : Type'} (_45287 : A -> Prop) (_45286 : A -> Prop) (h1 : term412 A) : term473 A _45287 _45286.
Proof. exact (EQ_MP (@lem3897449 A _45287 _45286) (@lem3897448 A _45286 _45287 h1)). Qed.
Lemma lem3897452 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3897454 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : @SUBSET A a b.
Proof. exact (h1). Qed.
Lemma lem3897458 {A : Type'} (a : A -> Prop) (h1 : term440 A a) : term440 A a.
Proof. exact (h1). Qed.
Lemma lem3897469 {A : Type'} (_45287 : A -> Prop) (_45286 : A -> Prop) : (term473 A _45287 _45286) = (term503 A _45287 _45286).
Proof. exact (@lem3896962 (term440 A _45287) (term504 A _45286 _45287) (@FINITE A _45286)). Qed.
Lemma lem3897470 {A : Type'} (_45287 : A -> Prop) (_45286 : A -> Prop) (h1 : term412 A) : term503 A _45287 _45286.
Proof. exact (EQ_MP (@lem3897469 A _45287 _45286) (@lem3897450 A _45287 _45286 h1)). Qed.
Lemma lem3897515 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3897516 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : term505 A b.
Proof. exact (fun h0 : term440 A b => @lem3897515 A b h1). Qed.
Lemma lem3897518 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3897519 {A : Type'} (b : A -> Prop) : (term505 A b) = (@FINITE A b).
Proof. exact (@lem3897518 (@FINITE A b)). Qed.
Lemma lem3897520 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (EQ_MP (@lem3897519 A b) (@lem3897516 A b h1)). Qed.
Lemma lem3897522 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : @SUBSET A a b.
Proof. exact (h1). Qed.
Lemma lem3897523 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : term507 A a b.
Proof. exact (fun h0 : term504 A a b => @lem3897522 A a b h1). Qed.
Lemma lem3897525 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3897526 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term507 A a b) = (@SUBSET A a b).
Proof. exact (@lem3897525 (@SUBSET A a b)). Qed.
Lemma lem3897527 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : @SUBSET A a b.
Proof. exact (EQ_MP (@lem3897526 A a b) (@lem3897523 A a b h1)). Qed.
Lemma lem3897543 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3897544 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : (term508 A _45287 _45286) = (term509 A _45286 _45287).
Proof. exact (@lem3897543 (@FINITE A _45286) (term504 A _45286 _45287)). Qed.
Lemma lem3897550 {A : Type'} (_45287 : A -> Prop) : (term510 A _45287) = (term510 A _45287).
Proof. exact (eq_refl (term510 A _45287)). Qed.
Lemma lem3897551 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : (term503 A _45287 _45286) = (term511 A _45286 _45287).
Proof. exact (MK_COMB (@lem3897550 A _45287) (@lem3897544 A _45286 _45287)). Qed.
Lemma lem3897555 (q : Prop) (p : Prop) (r : Prop) : (term430 p q r) = (term430 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3897556 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : (term511 A _45286 _45287) = (term512 A _45286 _45287).
Proof. exact (@lem3897555 (@FINITE A _45286) (term440 A _45287) (term504 A _45286 _45287)). Qed.
Lemma lem3897572 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : (term503 A _45287 _45286) = (term512 A _45286 _45287).
Proof. exact (TRANS (@lem3897551 A _45286 _45287) (@lem3897556 A _45286 _45287)). Qed.
Lemma lem3897573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3897574 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : (term513 A _45287 _45286) = (term514 A _45286 _45287).
Proof. exact (MK_COMB (@lem3897573) (@lem3897572 A _45286 _45287)). Qed.
Lemma lem3897590 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : (term512 A _45286 _45287) = (term512 A _45286 _45287).
Proof. exact (eq_refl (term512 A _45286 _45287)). Qed.
Lemma lem3897591 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : ((term503 A _45287 _45286) = (term512 A _45286 _45287)) = ((term512 A _45286 _45287) = (term512 A _45286 _45287)).
Proof. exact (MK_COMB (@lem3897574 A _45286 _45287) (@lem3897590 A _45286 _45287)). Qed.
Lemma lem3897593 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3897594 (x : Prop) : (x = x) = True.
Proof. exact (@lem3897593 Prop x). Qed.
Lemma lem3897595 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : ((term512 A _45286 _45287) = (term512 A _45286 _45287)) = True.
Proof. exact (@lem3897594 (term512 A _45286 _45287)). Qed.
Lemma lem3897596 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : ((term503 A _45287 _45286) = (term512 A _45286 _45287)) = True.
Proof. exact (TRANS (@lem3897591 A _45286 _45287) (@lem3897595 A _45286 _45287)). Qed.
Lemma lem3897597 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : True = ((term503 A _45287 _45286) = (term512 A _45286 _45287)).
Proof. exact (SYM (@lem3897596 A _45286 _45287)). Qed.
Lemma lem3897598 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : (term503 A _45287 _45286) = (term512 A _45286 _45287).
Proof. exact (EQ_MP (@lem3897597 A _45286 _45287) (@lem0)). Qed.
Lemma lem3897599 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) (h1 : term412 A) : term512 A _45286 _45287.
Proof. exact (EQ_MP (@lem3897598 A _45286 _45287) (@lem3897470 A _45287 _45286 h1)). Qed.
Lemma lem3897601 (b : Prop) (a : Prop) : (a \/ b) = (term515 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3897602 {A : Type'} (_45287 : A -> Prop) (_45286 : A -> Prop) : (term512 A _45286 _45287) = (term516 A _45287 _45286).
Proof. exact (@lem3897601 (term469 A _45286 _45287) (@FINITE A _45286)). Qed.
Lemma lem3897604 (a : Prop) (b : Prop) : (term517 a b) = (term518 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3897605 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : (term519 A _45286 _45287) = (term520 A _45286 _45287).
Proof. exact (@lem3897604 (term440 A _45287) (term504 A _45286 _45287)). Qed.
Lemma lem3897607 (a : Prop) : (term128 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3897608 {A : Type'} (_45287 : A -> Prop) : (term521 A _45287) = (@FINITE A _45287).
Proof. exact (@lem3897607 (@FINITE A _45287)). Qed.
Lemma lem3897609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3897610 {A : Type'} (_45287 : A -> Prop) : (term522 A _45287) = (term523 A _45287).
Proof. exact (MK_COMB (@lem3897609) (@lem3897608 A _45287)). Qed.
Lemma lem3897612 (a : Prop) : (term128 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3897613 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : (term524 A _45286 _45287) = (@SUBSET A _45286 _45287).
Proof. exact (@lem3897612 (@SUBSET A _45286 _45287)). Qed.
Lemma lem3897614 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : (term520 A _45286 _45287) = (term417 A _45286 _45287).
Proof. exact (MK_COMB (@lem3897610 A _45287) (@lem3897613 A _45286 _45287)). Qed.
Lemma lem3897615 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : (term519 A _45286 _45287) = (term417 A _45286 _45287).
Proof. exact (TRANS (@lem3897605 A _45286 _45287) (@lem3897614 A _45286 _45287)). Qed.
Lemma lem3897616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3897617 {A : Type'} (_45286 : A -> Prop) (_45287 : A -> Prop) : (term525 A _45286 _45287) = (term526 A _45286 _45287).
Proof. exact (MK_COMB (@lem3897616) (@lem3897615 A _45286 _45287)). Qed.
Lemma lem3897618 {A : Type'} (_45286 : A -> Prop) : (@FINITE A _45286) = (@FINITE A _45286).
Proof. exact (eq_refl (@FINITE A _45286)). Qed.
Lemma lem3897619 {A : Type'} (_45287 : A -> Prop) (_45286 : A -> Prop) : (term516 A _45287 _45286) = (term416 A _45287 _45286).
Proof. exact (MK_COMB (@lem3897617 A _45286 _45287) (@lem3897618 A _45286)). Qed.
Lemma lem3897620 {A : Type'} (_45287 : A -> Prop) (_45286 : A -> Prop) : (term512 A _45286 _45287) = (term416 A _45287 _45286).
Proof. exact (TRANS (@lem3897602 A _45287 _45286) (@lem3897619 A _45287 _45286)). Qed.
Lemma lem3897622 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : term417 A a b.
Proof. exact (conj (@lem3897520 A b h1) (@lem3897527 A a b h2)). Qed.
Lemma lem3897624 {A : Type'} (_45287 : A -> Prop) (_45286 : A -> Prop) (h1 : term412 A) : term416 A _45287 _45286.
Proof. exact (EQ_MP (@lem3897620 A _45287 _45286) (@lem3897599 A _45286 _45287 h1)). Qed.
Lemma lem3897625 {A : Type'} (_45287 : A -> Prop) (_45286 : A -> Prop) (h1 : term412 A) : term416 A _45287 _45286.
Proof. exact (@lem3897624 A _45287 _45286 h1). Qed.
Lemma lem3897626 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term412 A) : term416 A b a.
Proof. exact (@lem3897625 A b a h1). Qed.
Lemma lem3897629 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : @SUBSET A a b) : @FINITE A a.
Proof. exact (@lem3897626 A b a h1 (@lem3897622 A a b h2 h3)). Qed.
Lemma lem3897630 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : @SUBSET A a b) : term505 A a.
Proof. exact (fun h0 : term440 A a => @lem3897629 A a b h1 h2 h3). Qed.
Lemma lem3897632 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3897633 {A : Type'} (a : A -> Prop) : (term505 A a) = (@FINITE A a).
Proof. exact (@lem3897632 (@FINITE A a)). Qed.
Lemma lem3897634 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : @SUBSET A a b) : @FINITE A a.
Proof. exact (EQ_MP (@lem3897633 A a) (@lem3897630 A a b h1 h2 h3)). Qed.
Lemma lem3897637 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3897639 {A : Type'} (a : A -> Prop) : (term440 A a) = (term527 A a).
Proof. exact (@lem3897637 (@FINITE A a)). Qed.
Lemma lem3897642 {A : Type'} (a : A -> Prop) (h1 : term440 A a) : term527 A a.
Proof. exact (EQ_MP (@lem3897639 A a) (@lem3897458 A a h1)). Qed.
Lemma lem3897645 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (@lem3897642 A a h3 (@lem3897634 A a b h1 h2 h4)). Qed.
Lemma lem3897646 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : term528.
Proof. exact (fun h0 : ~ False => @lem3897645 A a b h1 h2 h3 h4). Qed.
Lemma lem3897648 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3897649 : term528 = False.
Proof. exact (@lem3897648 False). Qed.
Lemma lem3897650 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897649) (@lem3897646 A a b h1 h2 h3 h4)). Qed.
Lemma lem3897651 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (term440 A a) = False.
Proof. exact (prop_ext (fun h5 : term440 A a => @lem3897650 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897458 A a h3)). Qed.
Lemma lem3897652 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897651 A a b h1 h2 h3 h4) (@lem3897458 A a h3)). Qed.
Lemma lem3897653 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (@SUBSET A a b) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A a b => @lem3897652 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897454 A a b h4)). Qed.
Lemma lem3897654 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897653 A a b h1 h2 h3 h4) (@lem3897454 A a b h4)). Qed.
Lemma lem3897655 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (@FINITE A b) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A b => @lem3897654 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897452 A b h2)). Qed.
Lemma lem3897656 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897655 A a b h1 h2 h3 h4) (@lem3897452 A b h2)). Qed.
Lemma lem3897657 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (term440 A a) = False.
Proof. exact (prop_ext (fun h5 : term440 A a => @lem3897656 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897396 A a h3)). Qed.
Lemma lem3897658 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897657 A a b h1 h2 h3 h4) (@lem3897396 A a h3)). Qed.
Lemma lem3897659 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (@SUBSET A a b) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A a b => @lem3897658 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897388 A a b h4)). Qed.
Lemma lem3897660 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897659 A a b h1 h2 h3 h4) (@lem3897388 A a b h4)). Qed.
Lemma lem3897661 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (@FINITE A b) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A b => @lem3897660 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897384 A b h2)). Qed.
Lemma lem3897662 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897661 A a b h1 h2 h3 h4) (@lem3897384 A b h2)). Qed.
Lemma lem3897663 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (term440 A a) = False.
Proof. exact (prop_ext (fun h5 : term440 A a => @lem3897662 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897396 A a h3)). Qed.
Lemma lem3897664 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897663 A a b h1 h2 h3 h4) (@lem3897396 A a h3)). Qed.
Lemma lem3897665 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (@SUBSET A a b) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A a b => @lem3897664 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897388 A a b h4)). Qed.
Lemma lem3897666 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897665 A a b h1 h2 h3 h4) (@lem3897388 A a b h4)). Qed.
Lemma lem3897667 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (@FINITE A b) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A b => @lem3897666 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897384 A b h2)). Qed.
Lemma lem3897668 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897667 A a b h1 h2 h3 h4) (@lem3897384 A b h2)). Qed.
Lemma lem3897669 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (term440 A a) = False.
Proof. exact (prop_ext (fun h5 : term440 A a => @lem3897668 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897352 A a h3)). Qed.
Lemma lem3897670 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897669 A a b h1 h2 h3 h4) (@lem3897352 A a h3)). Qed.
Lemma lem3897671 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (@SUBSET A a b) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A a b => @lem3897670 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897336 A a b h4)). Qed.
Lemma lem3897672 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897671 A a b h1 h2 h3 h4) (@lem3897336 A a b h4)). Qed.
Lemma lem3897673 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (@FINITE A b) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A b => @lem3897672 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897330 A b h2)). Qed.
Lemma lem3897674 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897673 A a b h1 h2 h3 h4) (@lem3897330 A b h2)). Qed.
Lemma lem3897675 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (term440 A a) = False.
Proof. exact (prop_ext (fun h5 : term440 A a => @lem3897674 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897172 A a h3)). Qed.
Lemma lem3897676 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897675 A a b h1 h2 h3 h4) (@lem3897172 A a h3)). Qed.
Lemma lem3897677 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (@SUBSET A a b) = False.
Proof. exact (prop_ext (fun h5 : @SUBSET A a b => @lem3897676 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897160 A a b h4)). Qed.
Lemma lem3897678 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897677 A a b h1 h2 h3 h4) (@lem3897160 A a b h4)). Qed.
Lemma lem3897679 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : (@FINITE A b) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A b => @lem3897678 A a b h1 h2 h3 h4) (fun h5 : False => @lem3897154 A b h2)). Qed.
Lemma lem3897680 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term412 A) (h2 : @FINITE A b) (h3 : term440 A a) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897679 A a b h1 h2 h3 h4) (@lem3897154 A b h2)). Qed.
Lemma lem3897681 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term440 A a) (h3 : @SUBSET A a b) : term445 A.
Proof. exact (fun h0 : term412 A => @lem3897680 A a b h0 h1 h2 h3). Qed.
Lemma lem3897682 {A : Type'} : (term445 A) = (term446 A).
Proof. exact (@lem69 (term412 A)). Qed.
Lemma lem3897683 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term440 A a) (h3 : @SUBSET A a b) : term446 A.
Proof. exact (EQ_MP (@lem3897682 A) (@lem3897681 A a b h1 h2 h3)). Qed.
Lemma lem3897684 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : term449 A a.
Proof. exact (fun h0 : term440 A a => @lem3897683 A a b h1 h0 h2). Qed.
Lemma lem3897685 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : term452 A b a.
Proof. exact (fun h0 : (@CARD A a) = (@CARD A b) => @lem3897684 A a b h1 h2). Qed.
Lemma lem3897686 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : term455 A b a.
Proof. exact (fun h0 : @SUBSET A a b => @lem3897685 A a b h1 h0). Qed.
Lemma lem3897687 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term457 A b a.
Proof. exact (fun h0 : @FINITE A b => @lem3897686 A a b h0). Qed.
Lemma lem3897692 {A : Type'} (a : A -> Prop) : term461 A a.
Proof. exact (fun b : A -> Prop => @lem3897687 A b a). Qed.
Lemma lem3897697 {A : Type'} : term465 A.
Proof. exact (fun a : A -> Prop => @lem3897692 A a). Qed.
Lemma lem3897698 {A : Type'} : term464 A.
Proof. exact (EQ_MP (@lem3897143 A) (@lem3897697 A)). Qed.
Lemma lem3897699 {A : Type'} (a : A -> Prop) : term529 A a.
Proof. exact (@lem3897698 A a). Qed.
Lemma lem3897700 {A : Type'} (a : A -> Prop) : (term529 A a) = (term460 A a).
Proof. exact (eq_refl (term529 A a)). Qed.
Lemma lem3897701 {A : Type'} (a : A -> Prop) : term460 A a.
Proof. exact (EQ_MP (@lem3897700 A a) (@lem3897699 A a)). Qed.
Lemma lem3897702 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term530 A a b.
Proof. exact (@lem3897701 A a b). Qed.
Lemma lem3897703 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term530 A a b) = (term441 A b a).
Proof. exact (eq_refl (term530 A a b)). Qed.
Lemma lem3897704 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term441 A b a.
Proof. exact (EQ_MP (@lem3897703 A b a) (@lem3897702 A a b)). Qed.
Lemma lem3897706 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term441 A b a.
Proof. exact (@lem3896997 A b a (@lem3897704 A b a)). Qed.
Lemma lem3897707 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : term454 A b a.
Proof. exact (@lem3897706 A b a (@lem3896971 A b h1)). Qed.
Lemma lem3897708 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @SUBSET A a b) : term451 A b a.
Proof. exact (@lem3897707 A a b h1 (@lem3896973 A a b h2)). Qed.
Lemma lem3897709 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : (@CARD A a) = (@CARD A b)) (h3 : @SUBSET A a b) : term448 A a.
Proof. exact (@lem3897708 A a b h1 h3 (@lem3896972 A a b h2)). Qed.
Lemma lem3897710 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term440 A a) (h3 : (@CARD A a) = (@CARD A b)) (h4 : @SUBSET A a b) : term445 A.
Proof. exact (@lem3897709 A a b h1 h3 h4 (@lem3896979 A a h2)). Qed.
Lemma lem3897711 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term440 A a) (h3 : (@CARD A a) = (@CARD A b)) (h4 : @SUBSET A a b) : False.
Proof. exact (@lem3897710 A a b h1 h2 h3 h4 (@lem3896980 A)). Qed.
Lemma lem3897712 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term440 A a) (h3 : (@CARD A a) = (@CARD A b)) (h4 : @SUBSET A a b) : (term440 A a) = False.
Proof. exact (prop_ext (fun h5 : term440 A a => @lem3897711 A a b h1 h2 h3 h4) (fun h5 : False => @lem3896979 A a h2)). Qed.
Lemma lem3897713 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term440 A a) (h3 : (@CARD A a) = (@CARD A b)) (h4 : @SUBSET A a b) : False.
Proof. exact (EQ_MP (@lem3897712 A a b h1 h2 h3 h4) (@lem3896979 A a h2)). Qed.
Lemma lem3897714 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : (@CARD A a) = (@CARD A b)) (h3 : @SUBSET A a b) : term439 A a.
Proof. exact (fun h0 : term440 A a => @lem3897713 A a b h1 h0 h2 h3). Qed.
Lemma lem3897715 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : (@CARD A a) = (@CARD A b)) (h3 : @SUBSET A a b) : @FINITE A a.
Proof. exact (EQ_MP (@lem3896978 A a) (@lem3897714 A a b h1 h2 h3)). Qed.
Lemma lem3897716 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) : term531 A b a.
Proof. exact (h1). Qed.
Lemma lem3897718 {A : Type'} (s : A -> Prop) : term421 A s.
Proof. exact (EQ_MP (@lem3896951 A s) (@lem3896950 A s)). Qed.
Lemma lem3897719 {A : Type'} (s : A -> Prop) : term421 A s.
Proof. exact (@lem3897718 A s). Qed.
Lemma lem3897720 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term532 A b a.
Proof. exact (@lem3897719 A (@DIFF A b a)). Qed.
Lemma lem3897721 {A : Type'} (b : A -> Prop) : (@FINITE A b) = ((@FINITE A b) = True).
Proof. exact (@lem7 (@FINITE A b)). Qed.
Lemma lem3897730 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : (@FINITE A b) = True.
Proof. exact (EQ_MP (@lem3897721 A b) (@lem3896971 A b h1)). Qed.
Lemma lem3897731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3897732 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : (term523 A b) = (and True).
Proof. exact (MK_COMB (@lem3897731) (@lem3897730 A b h1)). Qed.
Lemma lem3897733 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term533 A a b) = (term533 A a b).
Proof. exact (eq_refl (term533 A a b)). Qed.
Lemma lem3897734 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : (term534 A a b) = (term535 A a b).
Proof. exact (MK_COMB (@lem3897732 A b h1) (@lem3897733 A a b)). Qed.
Lemma lem3897736 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3897737 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term535 A a b) = (term533 A a b).
Proof. exact (@lem3897736 (term533 A a b)). Qed.
Lemma lem3897738 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : (term534 A a b) = (term533 A a b).
Proof. exact (TRANS (@lem3897734 A a b h1) (@lem3897737 A a b)). Qed.
Lemma lem3897739 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : (term533 A a b) = (term534 A a b).
Proof. exact (SYM (@lem3897738 A a b h1)). Qed.
Lemma lem3897741 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term536 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3897742 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term536 A s t).
Proof. exact (@lem3897741 A s t). Qed.
Lemma lem3897743 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term533 A a b) = (term537 A a b).
Proof. exact (@lem3897742 A (@DIFF A b a) b). Qed.
Lemma lem3897750 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term537 A a b) = (term533 A a b).
Proof. exact (SYM (@lem3897743 A a b)). Qed.
Lemma lem3897758 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term538 A x s t) = (term539 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3897759 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term538 A x s t) = (term539 A s x t).
Proof. exact (@lem3897758 A s x t). Qed.
Lemma lem3897760 {A : Type'} (b : A -> Prop) (x : A) (a : A -> Prop) : (term538 A x b a) = (term539 A b x a).
Proof. exact (@lem3897759 A b x a). Qed.
Lemma lem3897764 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3897765 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3897764 A P x). Qed.
Lemma lem3897766 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3897765 A b x). Qed.
Lemma lem3897767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3897768 {A : Type'} (b : A -> Prop) (x : A) : (term540 A x b) = (term541 A b x).
Proof. exact (MK_COMB (@lem3897767) (@lem3897766 A b x)). Qed.
Lemma lem3897770 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3897771 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3897770 A P x). Qed.
Lemma lem3897772 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3897771 A a x). Qed.
Lemma lem3897773 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3897774 {A : Type'} (a : A -> Prop) (x : A) : (term542 A x a) = (term543 A a x).
Proof. exact (MK_COMB (@lem3897773) (@lem3897772 A a x)). Qed.
Lemma lem3897775 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term539 A b x a) = (term544 A b a x).
Proof. exact (MK_COMB (@lem3897768 A b x) (@lem3897774 A a x)). Qed.
Lemma lem3897778 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term538 A x b a) = (term544 A b a x).
Proof. exact (TRANS (@lem3897760 A b x a) (@lem3897775 A b a x)). Qed.
Lemma lem3897779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3897780 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term545 A x b a) = (term546 A b a x).
Proof. exact (MK_COMB (@lem3897779) (@lem3897778 A b a x)). Qed.
Lemma lem3897782 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3897783 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3897782 A P x). Qed.
Lemma lem3897784 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3897783 A b x). Qed.
Lemma lem3897785 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term547 A a x b) = (term548 A a b x).
Proof. exact (MK_COMB (@lem3897780 A b a x) (@lem3897784 A b x)). Qed.
Lemma lem3897788 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term549 A a b) = (term550 A a b).
Proof. exact (fun_ext (fun x : A => @lem3897785 A a b x)). Qed.
Lemma lem3897789 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3897790 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term537 A a b) = (term551 A a b).
Proof. exact (MK_COMB (@lem3897789 A) (@lem3897788 A a b)). Qed.
Lemma lem3897795 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term551 A a b) = (term537 A a b).
Proof. exact (SYM (@lem3897790 A a b)). Qed.
Lemma lem3897797 (p : Prop) : p = (term438 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3897798 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term551 A a b) = (term552 A a b).
Proof. exact (@lem3897797 (term551 A a b)). Qed.
Lemma lem3897799 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term552 A a b) = (term551 A a b).
Proof. exact (SYM (@lem3897798 A a b)). Qed.
Lemma lem3897800 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term553 A a b) : term553 A a b.
Proof. exact (h1). Qed.
Lemma lem3897803 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term552 A a b) : term552 A a b.
Proof. exact (h1). Qed.
Lemma lem3897804 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term554 A a b.
Proof. exact (fun h0 : term552 A a b => @lem3897803 A a b h0). Qed.
Lemma lem3897805 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term554 A a b) : term554 A a b.
Proof. exact (h1). Qed.
Lemma lem3897806 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term552 A a b) : term552 A a b.
Proof. exact (h1). Qed.
Lemma lem3897807 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term552 A a b) (h2 : term554 A a b) : term552 A a b.
Proof. exact (@lem3897805 A a b h2 (@lem3897806 A a b h1)). Qed.
Lemma lem3897808 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term552 A a b) : term555 A a b.
Proof. exact (fun h0 : term554 A a b => @lem3897807 A a b h1 h0). Qed.
Lemma lem3897809 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term554 A a b) : term554 A a b.
Proof. exact (h1). Qed.
Lemma lem3897810 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term552 A a b) (h2 : term554 A a b) : term552 A a b.
Proof. exact (@lem3897808 A a b h1 (@lem3897809 A a b h2)). Qed.
Lemma lem3897811 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term554 A a b) : term554 A a b.
Proof. exact (fun h0 : term552 A a b => @lem3897810 A a b h0 h1). Qed.
Lemma lem3897812 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term556 A a b.
Proof. exact (fun h0 : term554 A a b => @lem3897811 A a b h0). Qed.
Lemma lem3897815 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term554 A a b.
Proof. exact (@lem3897812 A a b (@lem3897804 A a b)). Qed.
Lemma lem3897816 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term554 A a b.
Proof. exact (@lem3897815 A a b). Qed.
Lemma lem3897826 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3897827 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term552 A a b) = (term557 A a b).
Proof. exact (@lem3897826 (term553 A a b)). Qed.
Lemma lem3897829 (t : Prop) : (term128 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3897830 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term557 A a b) = (term551 A a b).
Proof. exact (@lem3897829 (term551 A a b)). Qed.
Lemma lem3897835 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term552 A a b) = (term551 A a b).
Proof. exact (TRANS (@lem3897827 A a b) (@lem3897830 A a b)). Qed.
Lemma lem3897840 {A : Type'} (b : A -> Prop) : (term558 A b) = (term559 A b).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3897835 A a b)). Qed.
Lemma lem3897841 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897842 {A : Type'} (b : A -> Prop) : (term560 A b) = (term561 A b).
Proof. exact (MK_COMB (@lem3897841 A) (@lem3897840 A b)). Qed.
Lemma lem3897847 {A : Type'} : (term562 A) = (term563 A).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3897842 A b)). Qed.
Lemma lem3897848 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897857 {A : Type'} : (term564 A) = (term565 A).
Proof. exact (MK_COMB (@lem3897848 A) (@lem3897847 A)). Qed.
Lemma lem3897868 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term548 A a b x) = (term548 A a b x).
Proof. exact (eq_refl (term548 A a b x)). Qed.
Lemma lem3897869 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term550 A a b) = (term550 A a b).
Proof. exact (fun_ext (fun x : A => @lem3897868 A a b x)). Qed.
Lemma lem3897870 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3897871 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term551 A a b) = (term551 A a b).
Proof. exact (MK_COMB (@lem3897870 A) (@lem3897869 A a b)). Qed.
Lemma lem3897872 {A : Type'} (b : A -> Prop) : (term559 A b) = (term559 A b).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3897871 A a b)). Qed.
Lemma lem3897873 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897874 {A : Type'} (b : A -> Prop) : (term561 A b) = (term561 A b).
Proof. exact (MK_COMB (@lem3897873 A) (@lem3897872 A b)). Qed.
Lemma lem3897875 {A : Type'} : (term563 A) = (term563 A).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3897874 A b)). Qed.
Lemma lem3897876 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3897877 {A : Type'} : (term565 A) = (term565 A).
Proof. exact (MK_COMB (@lem3897876 A) (@lem3897875 A)). Qed.
Lemma lem3897902 {A : Type'} : (term564 A) = (term565 A).
Proof. exact (TRANS (@lem3897857 A) (@lem3897877 A)). Qed.
Lemma lem3897903 {A : Type'} : (term565 A) = (term564 A).
Proof. exact (SYM (@lem3897902 A)). Qed.
Lemma lem3897906 (p : Prop) : p = (term438 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3897907 {A : Type'} (b : A -> Prop) (x : A) : (b x) = (term566 A b x).
Proof. exact (@lem3897906 (b x)). Qed.
Lemma lem3897908 {A : Type'} (b : A -> Prop) (x : A) : (term566 A b x) = (b x).
Proof. exact (SYM (@lem3897907 A b x)). Qed.
Lemma lem3897909 {A : Type'} (b : A -> Prop) (x : A) (h1 : term543 A b x) : term543 A b x.
Proof. exact (h1). Qed.
Lemma lem3897919 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term544 A b a x) : term544 A b a x.
Proof. exact (h1). Qed.
Lemma lem3897925 {A : Type'} (b : A -> Prop) (x : A) (h1 : term543 A b x) : term543 A b x.
Proof. exact (h1). Qed.
Lemma lem3897937 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term544 A b a x) : term544 A b a x.
Proof. exact (h1). Qed.
Lemma lem3897943 {A : Type'} (b : A -> Prop) (x : A) (h1 : term543 A b x) : term543 A b x.
Proof. exact (h1). Qed.
Lemma lem3897949 {A : Type'} (b : A -> Prop) (x : A) (h1 : term543 A b x) : term543 A b x.
Proof. exact (h1). Qed.
Lemma lem3897959 {A : Type'} (b : A -> Prop) (x : A) (h1 : term543 A b x) : term543 A b x.
Proof. exact (h1). Qed.
Lemma lem3897965 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term544 A b a x) : b x.
Proof. exact (proj1 (@lem3897937 A b a x h1)). Qed.
Lemma lem3897966 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term544 A b a x) : term567 A b x.
Proof. exact (fun h0 : term543 A b x => @lem3897965 A b a x h1). Qed.
Lemma lem3897968 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3897969 {A : Type'} (b : A -> Prop) (x : A) : (term567 A b x) = (b x).
Proof. exact (@lem3897968 (b x)). Qed.
Lemma lem3897970 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term544 A b a x) : b x.
Proof. exact (EQ_MP (@lem3897969 A b x) (@lem3897966 A b a x h1)). Qed.
Lemma lem3897973 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3897975 {A : Type'} (b : A -> Prop) (x : A) : (term543 A b x) = (term568 A b x).
Proof. exact (@lem3897973 (b x)). Qed.
Lemma lem3897978 {A : Type'} (b : A -> Prop) (x : A) (h1 : term543 A b x) : term568 A b x.
Proof. exact (EQ_MP (@lem3897975 A b x) (@lem3897959 A b x h1)). Qed.
Lemma lem3897981 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : False.
Proof. exact (@lem3897978 A b x h1 (@lem3897970 A b a x h2)). Qed.
Lemma lem3897982 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : term528.
Proof. exact (fun h0 : ~ False => @lem3897981 A b a x h1 h2). Qed.
Lemma lem3897984 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3897985 : term528 = False.
Proof. exact (@lem3897984 False). Qed.
Lemma lem3897986 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : False.
Proof. exact (EQ_MP (@lem3897985) (@lem3897982 A b a x h1 h2)). Qed.
Lemma lem3897987 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : (term543 A b x) = False.
Proof. exact (prop_ext (fun h3 : term543 A b x => @lem3897986 A b a x h1 h2) (fun h3 : False => @lem3897959 A b x h1)). Qed.
Lemma lem3897988 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : False.
Proof. exact (EQ_MP (@lem3897987 A b a x h1 h2) (@lem3897959 A b x h1)). Qed.
Lemma lem3897989 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : (term543 A b x) = False.
Proof. exact (prop_ext (fun h3 : term543 A b x => @lem3897988 A b a x h1 h2) (fun h3 : False => @lem3897949 A b x h1)). Qed.
Lemma lem3897990 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : False.
Proof. exact (EQ_MP (@lem3897989 A b a x h1 h2) (@lem3897949 A b x h1)). Qed.
Lemma lem3897991 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : (term543 A b x) = False.
Proof. exact (prop_ext (fun h3 : term543 A b x => @lem3897990 A b a x h1 h2) (fun h3 : False => @lem3897949 A b x h1)). Qed.
Lemma lem3897992 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : False.
Proof. exact (EQ_MP (@lem3897991 A b a x h1 h2) (@lem3897949 A b x h1)). Qed.
Lemma lem3897993 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : (term543 A b x) = False.
Proof. exact (prop_ext (fun h3 : term543 A b x => @lem3897992 A b a x h1 h2) (fun h3 : False => @lem3897943 A b x h1)). Qed.
Lemma lem3897994 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : False.
Proof. exact (EQ_MP (@lem3897993 A b a x h1 h2) (@lem3897943 A b x h1)). Qed.
Lemma lem3897995 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : (term544 A b a x) = False.
Proof. exact (prop_ext (fun h3 : term544 A b a x => @lem3897994 A b a x h1 h2) (fun h3 : False => @lem3897937 A b a x h2)). Qed.
Lemma lem3897996 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : False.
Proof. exact (EQ_MP (@lem3897995 A b a x h1 h2) (@lem3897937 A b a x h2)). Qed.
Lemma lem3897997 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : (term543 A b x) = False.
Proof. exact (prop_ext (fun h3 : term543 A b x => @lem3897996 A b a x h1 h2) (fun h3 : False => @lem3897925 A b x h1)). Qed.
Lemma lem3897998 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : False.
Proof. exact (EQ_MP (@lem3897997 A b a x h1 h2) (@lem3897925 A b x h1)). Qed.
Lemma lem3897999 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : (term544 A b a x) = False.
Proof. exact (prop_ext (fun h3 : term544 A b a x => @lem3897998 A b a x h1 h2) (fun h3 : False => @lem3897919 A b a x h2)). Qed.
Lemma lem3898000 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : False.
Proof. exact (EQ_MP (@lem3897999 A b a x h1 h2) (@lem3897919 A b a x h2)). Qed.
Lemma lem3898001 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : (term543 A b x) = False.
Proof. exact (prop_ext (fun h3 : term543 A b x => @lem3898000 A b a x h1 h2) (fun h3 : False => @lem3897909 A b x h1)). Qed.
Lemma lem3898002 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term544 A b a x) : False.
Proof. exact (EQ_MP (@lem3898001 A b a x h1 h2) (@lem3897909 A b x h1)). Qed.
Lemma lem3898003 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term544 A b a x) : term566 A b x.
Proof. exact (fun h0 : term543 A b x => @lem3898002 A b a x h0 h1). Qed.
Lemma lem3898004 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term544 A b a x) : b x.
Proof. exact (EQ_MP (@lem3897908 A b x) (@lem3898003 A b a x h1)). Qed.
Lemma lem3898005 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : term548 A a b x.
Proof. exact (fun h0 : term544 A b a x => @lem3898004 A b a x h0). Qed.
Lemma lem3898010 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term551 A a b.
Proof. exact (fun x : A => @lem3898005 A a b x). Qed.
Lemma lem3898015 {A : Type'} (b : A -> Prop) : term561 A b.
Proof. exact (fun a : A -> Prop => @lem3898010 A a b). Qed.
Lemma lem3898020 {A : Type'} : term565 A.
Proof. exact (fun b : A -> Prop => @lem3898015 A b). Qed.
Lemma lem3898021 {A : Type'} : term564 A.
Proof. exact (EQ_MP (@lem3897903 A) (@lem3898020 A)). Qed.
Lemma lem3898022 {A : Type'} (b : A -> Prop) : term569 A b.
Proof. exact (@lem3898021 A b). Qed.
Lemma lem3898023 {A : Type'} (b : A -> Prop) : (term569 A b) = (term560 A b).
Proof. exact (eq_refl (term569 A b)). Qed.
Lemma lem3898024 {A : Type'} (b : A -> Prop) : term560 A b.
Proof. exact (EQ_MP (@lem3898023 A b) (@lem3898022 A b)). Qed.
Lemma lem3898025 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term570 A b a.
Proof. exact (@lem3898024 A b a). Qed.
Lemma lem3898026 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term570 A b a) = (term552 A a b).
Proof. exact (eq_refl (term570 A b a)). Qed.
Lemma lem3898027 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term552 A a b.
Proof. exact (EQ_MP (@lem3898026 A a b) (@lem3898025 A b a)). Qed.
Lemma lem3898029 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term552 A a b.
Proof. exact (@lem3897816 A a b (@lem3898027 A a b)). Qed.
Lemma lem3898030 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term553 A a b) : False.
Proof. exact (@lem3898029 A a b (@lem3897800 A a b h1)). Qed.
Lemma lem3898031 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term553 A a b) : (term553 A a b) = False.
Proof. exact (prop_ext (fun h2 : term553 A a b => @lem3898030 A a b h1) (fun h2 : False => @lem3897800 A a b h1)). Qed.
Lemma lem3898032 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term553 A a b) : False.
Proof. exact (EQ_MP (@lem3898031 A a b h1) (@lem3897800 A a b h1)). Qed.
Lemma lem3898033 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term552 A a b.
Proof. exact (fun h0 : term553 A a b => @lem3898032 A a b h0). Qed.
Lemma lem3898034 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term551 A a b.
Proof. exact (EQ_MP (@lem3897799 A a b) (@lem3898033 A a b)). Qed.
Lemma lem3898035 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term537 A a b.
Proof. exact (EQ_MP (@lem3897795 A a b) (@lem3898034 A a b)). Qed.
Lemma lem3898036 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term533 A a b.
Proof. exact (EQ_MP (@lem3897750 A a b) (@lem3898035 A a b)). Qed.
Lemma lem3898037 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : term534 A a b.
Proof. exact (EQ_MP (@lem3897739 A a b h1) (@lem3898036 A a b)). Qed.
Lemma lem3898038 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : term571 A b a.
Proof. exact (ex_intro (term572 A b a) b (@lem3898037 A a b h1)). Qed.
Lemma lem3898039 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : term531 A b a.
Proof. exact (@lem3897720 A b a (@lem3898038 A a b h1)). Qed.
Lemma lem3898040 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term573 A b a) = (@EMPTY A)) : (term573 A b a) = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3898044 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term574 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3898045 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term574 A s t).
Proof. exact (@lem3898044 A s t). Qed.
Lemma lem3898046 {A : Type'} (b : A -> Prop) (a : A -> Prop) : ((term573 A b a) = (@EMPTY A)) = (term575 A b a).
Proof. exact (@lem3898045 A (term573 A b a) (@EMPTY A)). Qed.
Lemma lem3898055 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term575 A b a) = ((term573 A b a) = (@EMPTY A)).
Proof. exact (SYM (@lem3898046 A b a)). Qed.
Lemma lem3898063 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term576 A x s t) = (term577 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3898064 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term576 A x s t) = (term577 A s x t).
Proof. exact (@lem3898063 A s x t). Qed.
Lemma lem3898065 {A : Type'} (x : A) (b : A -> Prop) (a : A -> Prop) : (term578 A x b a) = (term579 A x b a).
Proof. exact (@lem3898064 A a x (@DIFF A b a)). Qed.
Lemma lem3898069 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3898070 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3898069 A P x). Qed.
Lemma lem3898071 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3898070 A a x). Qed.
Lemma lem3898072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3898073 {A : Type'} (a : A -> Prop) (x : A) : (term540 A x a) = (term541 A a x).
Proof. exact (MK_COMB (@lem3898072) (@lem3898071 A a x)). Qed.
Lemma lem3898075 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term538 A x s t) = (term539 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3898076 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term538 A x s t) = (term539 A s x t).
Proof. exact (@lem3898075 A s x t). Qed.
Lemma lem3898077 {A : Type'} (b : A -> Prop) (x : A) (a : A -> Prop) : (term538 A x b a) = (term539 A b x a).
Proof. exact (@lem3898076 A b x a). Qed.
Lemma lem3898081 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3898082 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3898081 A P x). Qed.
Lemma lem3898083 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3898082 A b x). Qed.
Lemma lem3898084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3898085 {A : Type'} (b : A -> Prop) (x : A) : (term540 A x b) = (term541 A b x).
Proof. exact (MK_COMB (@lem3898084) (@lem3898083 A b x)). Qed.
Lemma lem3898087 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3898088 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3898087 A P x). Qed.
Lemma lem3898089 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3898088 A a x). Qed.
Lemma lem3898090 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3898091 {A : Type'} (a : A -> Prop) (x : A) : (term542 A x a) = (term543 A a x).
Proof. exact (MK_COMB (@lem3898090) (@lem3898089 A a x)). Qed.
Lemma lem3898092 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term539 A b x a) = (term544 A b a x).
Proof. exact (MK_COMB (@lem3898085 A b x) (@lem3898091 A a x)). Qed.
Lemma lem3898095 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term538 A x b a) = (term544 A b a x).
Proof. exact (TRANS (@lem3898077 A b x a) (@lem3898092 A b a x)). Qed.
Lemma lem3898096 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term579 A x b a) = (term580 A b a x).
Proof. exact (MK_COMB (@lem3898073 A a x) (@lem3898095 A b a x)). Qed.
Lemma lem3898099 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term578 A x b a) = (term580 A b a x).
Proof. exact (TRANS (@lem3898065 A x b a) (@lem3898096 A b a x)). Qed.
Lemma lem3898100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3898101 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term581 A x b a) = (term582 A b a x).
Proof. exact (MK_COMB (@lem3898100) (@lem3898099 A b a x)). Qed.
Lemma lem3898103 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3898104 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3898103 A x). Qed.
Lemma lem3898105 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : ((term578 A x b a) = (@IN A x (@EMPTY A))) = ((term580 A b a x) = False).
Proof. exact (MK_COMB (@lem3898101 A b a x) (@lem3898104 A x)). Qed.
Lemma lem3898107 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3898108 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : ((term580 A b a x) = False) = (term583 A b a x).
Proof. exact (@lem3898107 (term580 A b a x)). Qed.
Lemma lem3898113 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : ((term578 A x b a) = (@IN A x (@EMPTY A))) = (term583 A b a x).
Proof. exact (TRANS (@lem3898105 A b a x) (@lem3898108 A b a x)). Qed.
Lemma lem3898114 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term584 A b a) = (term585 A b a).
Proof. exact (fun_ext (fun x : A => @lem3898113 A b a x)). Qed.
Lemma lem3898115 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3898116 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term575 A b a) = (term586 A b a).
Proof. exact (MK_COMB (@lem3898115 A) (@lem3898114 A b a)). Qed.
Lemma lem3898121 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term586 A b a) = (term575 A b a).
Proof. exact (SYM (@lem3898116 A b a)). Qed.
Lemma lem3898123 (p : Prop) : p = (term438 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3898124 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term586 A b a) = (term587 A b a).
Proof. exact (@lem3898123 (term586 A b a)). Qed.
Lemma lem3898125 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term587 A b a) = (term586 A b a).
Proof. exact (SYM (@lem3898124 A b a)). Qed.
Lemma lem3898126 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term588 A b a) : term588 A b a.
Proof. exact (h1). Qed.
Lemma lem3898129 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term587 A b a) : term587 A b a.
Proof. exact (h1). Qed.
Lemma lem3898130 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term589 A b a.
Proof. exact (fun h0 : term587 A b a => @lem3898129 A b a h0). Qed.
Lemma lem3898131 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term589 A b a) : term589 A b a.
Proof. exact (h1). Qed.
Lemma lem3898132 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term587 A b a) : term587 A b a.
Proof. exact (h1). Qed.
Lemma lem3898133 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term587 A b a) (h2 : term589 A b a) : term587 A b a.
Proof. exact (@lem3898131 A b a h2 (@lem3898132 A b a h1)). Qed.
Lemma lem3898134 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term587 A b a) : term590 A b a.
Proof. exact (fun h0 : term589 A b a => @lem3898133 A b a h1 h0). Qed.
Lemma lem3898135 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term589 A b a) : term589 A b a.
Proof. exact (h1). Qed.
Lemma lem3898136 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term587 A b a) (h2 : term589 A b a) : term587 A b a.
Proof. exact (@lem3898134 A b a h1 (@lem3898135 A b a h2)). Qed.
Lemma lem3898137 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term589 A b a) : term589 A b a.
Proof. exact (fun h0 : term587 A b a => @lem3898136 A b a h0 h1). Qed.
Lemma lem3898138 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term591 A b a.
Proof. exact (fun h0 : term589 A b a => @lem3898137 A b a h0). Qed.
Lemma lem3898141 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term589 A b a.
Proof. exact (@lem3898138 A b a (@lem3898130 A b a)). Qed.
Lemma lem3898142 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term589 A b a.
Proof. exact (@lem3898141 A b a). Qed.
Lemma lem3898152 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3898153 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term587 A b a) = (term592 A b a).
Proof. exact (@lem3898152 (term588 A b a)). Qed.
Lemma lem3898155 (t : Prop) : (term128 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3898156 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term592 A b a) = (term586 A b a).
Proof. exact (@lem3898155 (term586 A b a)). Qed.
Lemma lem3898161 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term587 A b a) = (term586 A b a).
Proof. exact (TRANS (@lem3898153 A b a) (@lem3898156 A b a)). Qed.
Lemma lem3898166 {A : Type'} (a : A -> Prop) : (term593 A a) = (term594 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3898161 A b a)). Qed.
Lemma lem3898167 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3898168 {A : Type'} (a : A -> Prop) : (term595 A a) = (term596 A a).
Proof. exact (MK_COMB (@lem3898167 A) (@lem3898166 A a)). Qed.
Lemma lem3898173 {A : Type'} : (term597 A) = (term598 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3898168 A a)). Qed.
Lemma lem3898174 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3898183 {A : Type'} : (term599 A) = (term600 A).
Proof. exact (MK_COMB (@lem3898174 A) (@lem3898173 A)). Qed.
Lemma lem3898196 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term583 A b a x) = (term583 A b a x).
Proof. exact (eq_refl (term583 A b a x)). Qed.
Lemma lem3898197 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term585 A b a) = (term585 A b a).
Proof. exact (fun_ext (fun x : A => @lem3898196 A b a x)). Qed.
Lemma lem3898198 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3898199 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term586 A b a) = (term586 A b a).
Proof. exact (MK_COMB (@lem3898198 A) (@lem3898197 A b a)). Qed.
Lemma lem3898200 {A : Type'} (a : A -> Prop) : (term594 A a) = (term594 A a).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3898199 A b a)). Qed.
Lemma lem3898201 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3898202 {A : Type'} (a : A -> Prop) : (term596 A a) = (term596 A a).
Proof. exact (MK_COMB (@lem3898201 A) (@lem3898200 A a)). Qed.
Lemma lem3898203 {A : Type'} : (term598 A) = (term598 A).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3898202 A a)). Qed.
Lemma lem3898204 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3898205 {A : Type'} : (term600 A) = (term600 A).
Proof. exact (MK_COMB (@lem3898204 A) (@lem3898203 A)). Qed.
Lemma lem3898230 {A : Type'} : (term599 A) = (term600 A).
Proof. exact (TRANS (@lem3898183 A) (@lem3898205 A)). Qed.
Lemma lem3898231 {A : Type'} : (term600 A) = (term599 A).
Proof. exact (SYM (@lem3898230 A)). Qed.
Lemma lem3898246 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : term580 A b a x.
Proof. exact (h1). Qed.
Lemma lem3898264 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : term580 A b a x.
Proof. exact (h1). Qed.
Lemma lem3898265 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : term544 A b a x.
Proof. exact (proj2 (@lem3898264 A b a x h1)). Qed.
Lemma lem3898286 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : term543 A a x.
Proof. exact (proj2 (@lem3898265 A b a x h1)). Qed.
Lemma lem3898288 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : a x.
Proof. exact (proj1 (@lem3898264 A b a x h1)). Qed.
Lemma lem3898289 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : term567 A a x.
Proof. exact (fun h0 : term543 A a x => @lem3898288 A b a x h1). Qed.
Lemma lem3898291 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3898292 {A : Type'} (a : A -> Prop) (x : A) : (term567 A a x) = (a x).
Proof. exact (@lem3898291 (a x)). Qed.
Lemma lem3898293 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : a x.
Proof. exact (EQ_MP (@lem3898292 A a x) (@lem3898289 A b a x h1)). Qed.
Lemma lem3898296 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3898298 {A : Type'} (a : A -> Prop) (x : A) : (term543 A a x) = (term568 A a x).
Proof. exact (@lem3898296 (a x)). Qed.
Lemma lem3898301 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : term568 A a x.
Proof. exact (EQ_MP (@lem3898298 A a x) (@lem3898286 A b a x h1)). Qed.
Lemma lem3898304 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : False.
Proof. exact (@lem3898301 A b a x h1 (@lem3898293 A b a x h1)). Qed.
Lemma lem3898305 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : term528.
Proof. exact (fun h0 : ~ False => @lem3898304 A b a x h1). Qed.
Lemma lem3898307 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3898308 : term528 = False.
Proof. exact (@lem3898307 False). Qed.
Lemma lem3898309 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : False.
Proof. exact (EQ_MP (@lem3898308) (@lem3898305 A b a x h1)). Qed.
Lemma lem3898310 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : (term580 A b a x) = False.
Proof. exact (prop_ext (fun h2 : term580 A b a x => @lem3898309 A b a x h1) (fun h2 : False => @lem3898264 A b a x h1)). Qed.
Lemma lem3898311 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : False.
Proof. exact (EQ_MP (@lem3898310 A b a x h1) (@lem3898264 A b a x h1)). Qed.
Lemma lem3898312 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : (term580 A b a x) = False.
Proof. exact (prop_ext (fun h2 : term580 A b a x => @lem3898311 A b a x h1) (fun h2 : False => @lem3898246 A b a x h1)). Qed.
Lemma lem3898313 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term580 A b a x) : False.
Proof. exact (EQ_MP (@lem3898312 A b a x h1) (@lem3898246 A b a x h1)). Qed.
Lemma lem3898314 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : term601 A b a x.
Proof. exact (fun h0 : term580 A b a x => @lem3898313 A b a x h0). Qed.
Lemma lem3898315 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term601 A b a x) = (term583 A b a x).
Proof. exact (@lem69 (term580 A b a x)). Qed.
Lemma lem3898316 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : term583 A b a x.
Proof. exact (EQ_MP (@lem3898315 A b a x) (@lem3898314 A b a x)). Qed.
Lemma lem3898321 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term586 A b a.
Proof. exact (fun x : A => @lem3898316 A b a x). Qed.
Lemma lem3898326 {A : Type'} (a : A -> Prop) : term596 A a.
Proof. exact (fun b : A -> Prop => @lem3898321 A b a). Qed.
Lemma lem3898331 {A : Type'} : term600 A.
Proof. exact (fun a : A -> Prop => @lem3898326 A a). Qed.
Lemma lem3898332 {A : Type'} : term599 A.
Proof. exact (EQ_MP (@lem3898231 A) (@lem3898331 A)). Qed.
Lemma lem3898333 {A : Type'} (a : A -> Prop) : term602 A a.
Proof. exact (@lem3898332 A a). Qed.
Lemma lem3898334 {A : Type'} (a : A -> Prop) : (term602 A a) = (term595 A a).
Proof. exact (eq_refl (term602 A a)). Qed.
Lemma lem3898335 {A : Type'} (a : A -> Prop) : term595 A a.
Proof. exact (EQ_MP (@lem3898334 A a) (@lem3898333 A a)). Qed.
Lemma lem3898336 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term603 A a b.
Proof. exact (@lem3898335 A a b). Qed.
Lemma lem3898337 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term603 A a b) = (term587 A b a).
Proof. exact (eq_refl (term603 A a b)). Qed.
Lemma lem3898338 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term587 A b a.
Proof. exact (EQ_MP (@lem3898337 A b a) (@lem3898336 A a b)). Qed.
Lemma lem3898340 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term587 A b a.
Proof. exact (@lem3898142 A b a (@lem3898338 A b a)). Qed.
Lemma lem3898341 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term588 A b a) : False.
Proof. exact (@lem3898340 A b a (@lem3898126 A b a h1)). Qed.
Lemma lem3898342 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term588 A b a) : (term588 A b a) = False.
Proof. exact (prop_ext (fun h2 : term588 A b a => @lem3898341 A b a h1) (fun h2 : False => @lem3898126 A b a h1)). Qed.
Lemma lem3898343 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term588 A b a) : False.
Proof. exact (EQ_MP (@lem3898342 A b a h1) (@lem3898126 A b a h1)). Qed.
Lemma lem3898344 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term587 A b a.
Proof. exact (fun h0 : term588 A b a => @lem3898343 A b a h0). Qed.
Lemma lem3898345 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term586 A b a.
Proof. exact (EQ_MP (@lem3898125 A b a) (@lem3898344 A b a)). Qed.
Lemma lem3898346 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term575 A b a.
Proof. exact (EQ_MP (@lem3898121 A b a) (@lem3898345 A b a)). Qed.
Lemma lem3898347 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term573 A b a) = (@EMPTY A).
Proof. exact (EQ_MP (@lem3898055 A b a) (@lem3898346 A b a)). Qed.
Lemma lem3898352 {A : Type'} (a : A -> Prop) : (@FINITE A a) = ((@FINITE A a) = True).
Proof. exact (@lem7 (@FINITE A a)). Qed.
Lemma lem3898354 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term531 A b a) = ((term531 A b a) = True).
Proof. exact (@lem7 (term531 A b a)). Qed.
Lemma lem3898363 {A : Type'} (a : A -> Prop) (h1 : @FINITE A a) : (@FINITE A a) = True.
Proof. exact (EQ_MP (@lem3898352 A a) (@lem3896974 A a h1)). Qed.
Lemma lem3898364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3898365 {A : Type'} (a : A -> Prop) (h1 : @FINITE A a) : (term523 A a) = (and True).
Proof. exact (MK_COMB (@lem3898364) (@lem3898363 A a h1)). Qed.
Lemma lem3898369 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) : (term531 A b a) = True.
Proof. exact (EQ_MP (@lem3898354 A b a) (@lem3897716 A b a h1)). Qed.
Lemma lem3898370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3898371 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) : (term604 A b a) = (and True).
Proof. exact (MK_COMB (@lem3898370) (@lem3898369 A b a h1)). Qed.
Lemma lem3898375 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term573 A b a) = (@EMPTY A)) : (term573 A b a) = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3898376 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3898377 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term573 A b a) = (@EMPTY A)) : (term605 A b a) = (@eq (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem3898376 A) (@lem3898375 A b a h1)). Qed.
Lemma lem3898378 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem3898379 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term573 A b a) = (@EMPTY A)) : ((term573 A b a) = (@EMPTY A)) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem3898377 A b a h1) (@lem3898378 A)). Qed.
Lemma lem3898381 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3898382 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3898381 (A -> Prop) x). Qed.
Lemma lem3898383 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem3898382 A (@EMPTY A)). Qed.
Lemma lem3898384 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term573 A b a) = (@EMPTY A)) : ((term573 A b a) = (@EMPTY A)) = True.
Proof. exact (TRANS (@lem3898379 A b a h1) (@lem3898383 A)). Qed.
Lemma lem3898385 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) (h2 : (term573 A b a) = (@EMPTY A)) : (term606 A b a) = (True /\ True).
Proof. exact (MK_COMB (@lem3898371 A b a h1) (@lem3898384 A b a h2)). Qed.
Lemma lem3898387 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3898388 : (True /\ True) = True.
Proof. exact (@lem3898387 True). Qed.
Lemma lem3898389 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) (h2 : (term573 A b a) = (@EMPTY A)) : (term606 A b a) = True.
Proof. exact (TRANS (@lem3898385 A b a h1 h2) (@lem3898388)). Qed.
Lemma lem3898390 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (term573 A b a) = (@EMPTY A)) : (term607 A b a) = (True /\ True).
Proof. exact (MK_COMB (@lem3898365 A a h1) (@lem3898389 A b a h2 h3)). Qed.
Lemma lem3898392 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3898393 : (True /\ True) = True.
Proof. exact (@lem3898392 True). Qed.
Lemma lem3898394 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (term573 A b a) = (@EMPTY A)) : (term607 A b a) = True.
Proof. exact (TRANS (@lem3898390 A b a h1 h2 h3) (@lem3898393)). Qed.
Lemma lem3898395 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3898396 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (term573 A b a) = (@EMPTY A)) : (term608 A b a) = (imp True).
Proof. exact (MK_COMB (@lem3898395) (@lem3898394 A b a h1 h2 h3)). Qed.
Lemma lem3898400 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (@CARD A a) = (@CARD A b)) : (@CARD A a) = (@CARD A b).
Proof. exact (h1). Qed.
Lemma lem3898401 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem3898402 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (@CARD A a) = (@CARD A b)) : (term609 A a) = (term609 A b).
Proof. exact (MK_COMB (@lem3898401) (@lem3898400 A a b h1)). Qed.
Lemma lem3898403 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term610 A b a) = (term610 A b a).
Proof. exact (eq_refl (term610 A b a)). Qed.
Lemma lem3898404 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (@CARD A a) = (@CARD A b)) : (term611 A b a) = (term612 A b a).
Proof. exact (MK_COMB (@lem3898402 A a b h1) (@lem3898403 A b a)). Qed.
Lemma lem3898405 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term613 A b a) = (term613 A b a).
Proof. exact (eq_refl (term613 A b a)). Qed.
Lemma lem3898406 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (@CARD A a) = (@CARD A b)) : ((term614 A b a) = (term611 A b a)) = ((term614 A b a) = (term612 A b a)).
Proof. exact (MK_COMB (@lem3898405 A b a) (@lem3898404 A a b h1)). Qed.
Lemma lem3898409 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (term573 A b a) = (@EMPTY A)) (h4 : (@CARD A a) = (@CARD A b)) : (term435 A b a) = (term615 A b a).
Proof. exact (MK_COMB (@lem3898396 A b a h1 h2 h3) (@lem3898406 A a b h4)). Qed.
Lemma lem3898411 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3898412 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term615 A b a) = ((term614 A b a) = (term612 A b a)).
Proof. exact (@lem3898411 ((term614 A b a) = (term612 A b a))). Qed.
Lemma lem3898415 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (term573 A b a) = (@EMPTY A)) (h4 : (@CARD A a) = (@CARD A b)) : (term435 A b a) = ((term614 A b a) = (term612 A b a)).
Proof. exact (TRANS (@lem3898409 A a b h1 h2 h3 h4) (@lem3898412 A b a)). Qed.
Lemma lem3898416 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3898417 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (term573 A b a) = (@EMPTY A)) (h4 : (@CARD A a) = (@CARD A b)) : (term616 A b a) = (term617 A b a).
Proof. exact (MK_COMB (@lem3898416) (@lem3898415 A a b h1 h2 h3 h4)). Qed.
Lemma lem3898420 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (a = b) = (a = b).
Proof. exact (eq_refl (a = b)). Qed.
Lemma lem3898421 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (term573 A b a) = (@EMPTY A)) (h4 : (@CARD A a) = (@CARD A b)) : (term618 A a b) = (term619 A a b).
Proof. exact (MK_COMB (@lem3898417 A a b h1 h2 h3 h4) (@lem3898420 A a b)). Qed.
Lemma lem3898426 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (term573 A b a) = (@EMPTY A)) (h4 : (@CARD A a) = (@CARD A b)) : (term619 A a b) = (term618 A a b).
Proof. exact (SYM (@lem3898421 A a b h1 h2 h3 h4)). Qed.
Lemma lem3898427 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (term620 A b a) = b) : (term620 A b a) = b.
Proof. exact (h1). Qed.
Lemma lem3898431 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term536 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3898432 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term536 A s t).
Proof. exact (@lem3898431 A s t). Qed.
Lemma lem3898433 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (@SUBSET A a b) = (term536 A a b).
Proof. exact (@lem3898432 A a b). Qed.
Lemma lem3898440 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3898441 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term453 A a b) = (term621 A a b).
Proof. exact (MK_COMB (@lem3898440) (@lem3898433 A a b)). Qed.
Lemma lem3898445 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term574 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3898446 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term574 A s t).
Proof. exact (@lem3898445 A s t). Qed.
Lemma lem3898447 {A : Type'} (a : A -> Prop) (b : A -> Prop) : ((term620 A b a) = b) = (term622 A a b).
Proof. exact (@lem3898446 A (term620 A b a) b). Qed.
Lemma lem3898456 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term623 A a b) = (term624 A a b).
Proof. exact (MK_COMB (@lem3898441 A a b) (@lem3898447 A a b)). Qed.
Lemma lem3898459 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term624 A a b) = (term623 A a b).
Proof. exact (SYM (@lem3898456 A a b)). Qed.
Lemma lem3898469 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3898470 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3898469 A P x). Qed.
Lemma lem3898471 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3898470 A a x). Qed.
Lemma lem3898472 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3898473 {A : Type'} (a : A -> Prop) (x : A) : (term625 A x a) = (term626 A a x).
Proof. exact (MK_COMB (@lem3898472) (@lem3898471 A a x)). Qed.
Lemma lem3898475 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3898476 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3898475 A P x). Qed.
Lemma lem3898477 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3898476 A b x). Qed.
Lemma lem3898478 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term627 A a x b) = (term628 A a b x).
Proof. exact (MK_COMB (@lem3898473 A a x) (@lem3898477 A b x)). Qed.
Lemma lem3898481 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term629 A a b) = (term630 A a b).
Proof. exact (fun_ext (fun x : A => @lem3898478 A a b x)). Qed.
Lemma lem3898482 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3898483 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term536 A a b) = (term631 A a b).
Proof. exact (MK_COMB (@lem3898482 A) (@lem3898481 A a b)). Qed.
Lemma lem3898488 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3898489 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term621 A a b) = (term632 A a b).
Proof. exact (MK_COMB (@lem3898488) (@lem3898483 A a b)). Qed.
Lemma lem3898497 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term633 A x s t) = (term634 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3898498 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term633 A x s t) = (term634 A s x t).
Proof. exact (@lem3898497 A s x t). Qed.
Lemma lem3898499 {A : Type'} (x : A) (b : A -> Prop) (a : A -> Prop) : (term635 A x b a) = (term636 A x b a).
Proof. exact (@lem3898498 A a x (@DIFF A b a)). Qed.
Lemma lem3898503 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3898504 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3898503 A P x). Qed.
Lemma lem3898505 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3898504 A a x). Qed.
Lemma lem3898506 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3898507 {A : Type'} (a : A -> Prop) (x : A) : (term637 A x a) = (term638 A a x).
Proof. exact (MK_COMB (@lem3898506) (@lem3898505 A a x)). Qed.
Lemma lem3898509 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term538 A x s t) = (term539 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3898510 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term538 A x s t) = (term539 A s x t).
Proof. exact (@lem3898509 A s x t). Qed.
Lemma lem3898511 {A : Type'} (b : A -> Prop) (x : A) (a : A -> Prop) : (term538 A x b a) = (term539 A b x a).
Proof. exact (@lem3898510 A b x a). Qed.
Lemma lem3898515 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3898516 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3898515 A P x). Qed.
Lemma lem3898517 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3898516 A b x). Qed.
Lemma lem3898518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3898519 {A : Type'} (b : A -> Prop) (x : A) : (term540 A x b) = (term541 A b x).
Proof. exact (MK_COMB (@lem3898518) (@lem3898517 A b x)). Qed.
Lemma lem3898521 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3898522 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3898521 A P x). Qed.
Lemma lem3898523 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3898522 A a x). Qed.
Lemma lem3898524 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3898525 {A : Type'} (a : A -> Prop) (x : A) : (term542 A x a) = (term543 A a x).
Proof. exact (MK_COMB (@lem3898524) (@lem3898523 A a x)). Qed.
Lemma lem3898526 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term539 A b x a) = (term544 A b a x).
Proof. exact (MK_COMB (@lem3898519 A b x) (@lem3898525 A a x)). Qed.
Lemma lem3898529 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term538 A x b a) = (term544 A b a x).
Proof. exact (TRANS (@lem3898511 A b x a) (@lem3898526 A b a x)). Qed.
Lemma lem3898530 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term636 A x b a) = (term639 A b a x).
Proof. exact (MK_COMB (@lem3898507 A a x) (@lem3898529 A b a x)). Qed.
Lemma lem3898533 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term635 A x b a) = (term639 A b a x).
Proof. exact (TRANS (@lem3898499 A x b a) (@lem3898530 A b a x)). Qed.
Lemma lem3898534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3898535 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term640 A x b a) = (term641 A b a x).
Proof. exact (MK_COMB (@lem3898534) (@lem3898533 A b a x)). Qed.
Lemma lem3898537 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3898538 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3898537 A P x). Qed.
Lemma lem3898539 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3898538 A b x). Qed.
Lemma lem3898540 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : ((term635 A x b a) = (@IN A x b)) = ((term639 A b a x) = (b x)).
Proof. exact (MK_COMB (@lem3898535 A b a x) (@lem3898539 A b x)). Qed.
Lemma lem3898543 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term642 A a b) = (term643 A a b).
Proof. exact (fun_ext (fun x : A => @lem3898540 A a b x)). Qed.
Lemma lem3898544 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3898545 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term622 A a b) = (term644 A a b).
Proof. exact (MK_COMB (@lem3898544 A) (@lem3898543 A a b)). Qed.
Lemma lem3898550 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term624 A a b) = (term645 A a b).
Proof. exact (MK_COMB (@lem3898489 A a b) (@lem3898545 A a b)). Qed.
Lemma lem3898553 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term645 A a b) = (term624 A a b).
Proof. exact (SYM (@lem3898550 A a b)). Qed.
Lemma lem3898555 (p : Prop) : p = (term438 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3898556 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term645 A a b) = (term646 A a b).
Proof. exact (@lem3898555 (term645 A a b)). Qed.
Lemma lem3898557 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term646 A a b) = (term645 A a b).
Proof. exact (SYM (@lem3898556 A a b)). Qed.
Lemma lem3898558 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term647 A a b) : term647 A a b.
Proof. exact (h1). Qed.
Lemma lem3898561 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term646 A a b) : term646 A a b.
Proof. exact (h1). Qed.
Lemma lem3898562 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term648 A a b.
Proof. exact (fun h0 : term646 A a b => @lem3898561 A a b h0). Qed.
Lemma lem3898563 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term648 A a b) : term648 A a b.
Proof. exact (h1). Qed.
Lemma lem3898564 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term646 A a b) : term646 A a b.
Proof. exact (h1). Qed.
Lemma lem3898565 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term646 A a b) (h2 : term648 A a b) : term646 A a b.
Proof. exact (@lem3898563 A a b h2 (@lem3898564 A a b h1)). Qed.
Lemma lem3898566 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term646 A a b) : term649 A a b.
Proof. exact (fun h0 : term648 A a b => @lem3898565 A a b h1 h0). Qed.
Lemma lem3898567 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term648 A a b) : term648 A a b.
Proof. exact (h1). Qed.
Lemma lem3898568 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term646 A a b) (h2 : term648 A a b) : term646 A a b.
Proof. exact (@lem3898566 A a b h1 (@lem3898567 A a b h2)). Qed.
Lemma lem3898569 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term648 A a b) : term648 A a b.
Proof. exact (fun h0 : term646 A a b => @lem3898568 A a b h0 h1). Qed.
Lemma lem3898570 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term650 A a b.
Proof. exact (fun h0 : term648 A a b => @lem3898569 A a b h0). Qed.
Lemma lem3898573 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term648 A a b.
Proof. exact (@lem3898570 A a b (@lem3898562 A a b)). Qed.
Lemma lem3898574 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term648 A a b.
Proof. exact (@lem3898573 A a b). Qed.
Lemma lem3898584 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3898585 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term646 A a b) = (term651 A a b).
Proof. exact (@lem3898584 (term647 A a b)). Qed.
Lemma lem3898587 (t : Prop) : (term128 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3898588 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term651 A a b) = (term645 A a b).
Proof. exact (@lem3898587 (term645 A a b)). Qed.
Lemma lem3898591 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term646 A a b) = (term645 A a b).
Proof. exact (TRANS (@lem3898585 A a b) (@lem3898588 A a b)). Qed.
Lemma lem3898606 {A : Type'} (b : A -> Prop) : (term652 A b) = (term653 A b).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3898591 A a b)). Qed.
Lemma lem3898607 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3898608 {A : Type'} (b : A -> Prop) : (term654 A b) = (term655 A b).
Proof. exact (MK_COMB (@lem3898607 A) (@lem3898606 A b)). Qed.
Lemma lem3898613 {A : Type'} : (term656 A) = (term657 A).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3898608 A b)). Qed.
Lemma lem3898614 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3898623 {A : Type'} : (term658 A) = (term659 A).
Proof. exact (MK_COMB (@lem3898614 A) (@lem3898613 A)). Qed.
Lemma lem3898638 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : ((term639 A b a x) = (b x)) = ((term639 A b a x) = (b x)).
Proof. exact (eq_refl ((term639 A b a x) = (b x))). Qed.
Lemma lem3898639 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term643 A a b) = (term643 A a b).
Proof. exact (fun_ext (fun x : A => @lem3898638 A a b x)). Qed.
Lemma lem3898640 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3898641 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term644 A a b) = (term644 A a b).
Proof. exact (MK_COMB (@lem3898640 A) (@lem3898639 A a b)). Qed.
Lemma lem3898646 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term628 A a b x) = (term628 A a b x).
Proof. exact (eq_refl (term628 A a b x)). Qed.
Lemma lem3898647 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term630 A a b) = (term630 A a b).
Proof. exact (fun_ext (fun x : A => @lem3898646 A a b x)). Qed.
Lemma lem3898648 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3898649 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term631 A a b) = (term631 A a b).
Proof. exact (MK_COMB (@lem3898648 A) (@lem3898647 A a b)). Qed.
Lemma lem3898650 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3898651 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term632 A a b) = (term632 A a b).
Proof. exact (MK_COMB (@lem3898650) (@lem3898649 A a b)). Qed.
Lemma lem3898652 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term645 A a b) = (term645 A a b).
Proof. exact (MK_COMB (@lem3898651 A a b) (@lem3898641 A a b)). Qed.
Lemma lem3898653 {A : Type'} (b : A -> Prop) : (term653 A b) = (term653 A b).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3898652 A a b)). Qed.
Lemma lem3898654 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3898655 {A : Type'} (b : A -> Prop) : (term655 A b) = (term655 A b).
Proof. exact (MK_COMB (@lem3898654 A) (@lem3898653 A b)). Qed.
Lemma lem3898656 {A : Type'} : (term657 A) = (term657 A).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3898655 A b)). Qed.
Lemma lem3898657 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3898658 {A : Type'} : (term659 A) = (term659 A).
Proof. exact (MK_COMB (@lem3898657 A) (@lem3898656 A)). Qed.
Lemma lem3898693 {A : Type'} : (term658 A) = (term659 A).
Proof. exact (TRANS (@lem3898623 A) (@lem3898658 A)). Qed.
Lemma lem3898694 {A : Type'} : (term659 A) = (term658 A).
Proof. exact (SYM (@lem3898693 A)). Qed.
Lemma lem3898695 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term631 A a b.
Proof. exact (h1). Qed.
Lemma lem3898697 (p : Prop) : p = (term438 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3898698 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : ((term639 A b a x) = (b x)) = (term660 A a b x).
Proof. exact (@lem3898697 ((term639 A b a x) = (b x))). Qed.
Lemma lem3898699 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term660 A a b x) = ((term639 A b a x) = (b x)).
Proof. exact (SYM (@lem3898698 A a b x)). Qed.
Lemma lem3898700 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term661 A a b x) : term661 A a b x.
Proof. exact (h1). Qed.
Lemma lem3898707 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term628 A a b x) = (term662 A a b x).
Proof. exact (@lem17265 (a x) (b x)). Qed.
Lemma lem3898708 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term630 A a b) = (term663 A a b).
Proof. exact (fun_ext (fun x : A => @lem3898707 A a b x)). Qed.
Lemma lem3898709 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3898746 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term631 A a b) = (term664 A a b).
Proof. exact (MK_COMB (@lem3898709 A) (@lem3898708 A a b)). Qed.
Lemma lem3898747 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term664 A a b.
Proof. exact (EQ_MP (@lem3898746 A a b) (@lem3898695 A a b h1)). Qed.
Lemma lem3898755 {A : Type'} (a : A -> Prop) (x : A) : (term665 A a x) = (a x).
Proof. exact (@lem16933 (a x)). Qed.
Lemma lem3898757 {A : Type'} (b : A -> Prop) (x : A) : (term666 A b x) = (term666 A b x).
Proof. exact (eq_refl (term666 A b x)). Qed.
Lemma lem3898758 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term667 A b a x) = (term662 A b a x).
Proof. exact (MK_COMB (@lem3898757 A b x) (@lem3898755 A a x)). Qed.
Lemma lem3898759 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term668 A b a x) = (term667 A b a x).
Proof. exact (@lem17045 (b x) (term543 A a x)). Qed.
Lemma lem3898760 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term668 A b a x) = (term662 A b a x).
Proof. exact (TRANS (@lem3898759 A b a x) (@lem3898758 A b a x)). Qed.
Lemma lem3898765 {A : Type'} (a : A -> Prop) (x : A) : (term669 A a x) = (term669 A a x).
Proof. exact (eq_refl (term669 A a x)). Qed.
Lemma lem3898766 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term670 A b a x) = (term671 A b a x).
Proof. exact (MK_COMB (@lem3898765 A a x) (@lem3898760 A b a x)). Qed.
Lemma lem3898767 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term672 A b a x) = (term670 A b a x).
Proof. exact (@lem17160 (a x) (term544 A b a x)). Qed.
Lemma lem3898768 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term672 A b a x) = (term671 A b a x).
Proof. exact (TRANS (@lem3898767 A b a x) (@lem3898766 A b a x)). Qed.
Lemma lem3898773 {A : Type'} (b : A -> Prop) (x : A) : (b x) = (b x).
Proof. exact (eq_refl (b x)). Qed.
Lemma lem3898774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3898775 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term673 A b a x) = (term674 A b a x).
Proof. exact (MK_COMB (@lem3898774) (@lem3898768 A b a x)). Qed.
Lemma lem3898776 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term675 A a b x) = (term676 A a b x).
Proof. exact (MK_COMB (@lem3898775 A b a x) (@lem3898773 A b x)). Qed.
Lemma lem3898781 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term677 A a b x) = (term677 A a b x).
Proof. exact (eq_refl (term677 A a b x)). Qed.
Lemma lem3898782 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term678 A a b x) = (term679 A a b x).
Proof. exact (MK_COMB (@lem3898781 A a b x) (@lem3898776 A a b x)). Qed.
Lemma lem3898783 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term661 A a b x) = (term678 A a b x).
Proof. exact (@lem17646 (term639 A b a x) (b x)). Qed.
Lemma lem3898788 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term661 A a b x) = (term679 A a b x).
Proof. exact (TRANS (@lem3898783 A a b x) (@lem3898782 A a b x)). Qed.
Lemma lem3898800 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term662 A a b x) = (term662 A a b x).
Proof. exact (eq_refl (term662 A a b x)). Qed.
Lemma lem3898801 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term663 A a b) = (term663 A a b).
Proof. exact (fun_ext (fun x : A => @lem3898800 A a b x)). Qed.
Lemma lem3898802 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3898803 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term664 A a b) = (term664 A a b).
Proof. exact (MK_COMB (@lem3898802 A) (@lem3898801 A a b)). Qed.
Lemma lem3898804 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term664 A a b.
Proof. exact (EQ_MP (@lem3898803 A a b) (@lem3898747 A a b h1)). Qed.
Lemma lem3898858 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term661 A a b x) : term679 A a b x.
Proof. exact (EQ_MP (@lem3898788 A a b x) (@lem3898700 A a b x h1)). Qed.
Lemma lem3898859 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term680 A a b x) : term680 A a b x.
Proof. exact (h1). Qed.
Lemma lem3898860 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term676 A a b x) : term676 A a b x.
Proof. exact (h1). Qed.
Lemma lem3898862 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term680 A a b x) : term639 A b a x.
Proof. exact (proj1 (@lem3898859 A a b x h1)). Qed.
Lemma lem3898864 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term544 A b a x) : term544 A b a x.
Proof. exact (h1). Qed.
Lemma lem3898868 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term676 A a b x) : term671 A b a x.
Proof. exact (proj1 (@lem3898860 A a b x h1)). Qed.
Lemma lem3898869 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term676 A a b x) : term662 A b a x.
Proof. exact (proj2 (@lem3898868 A a b x h1)). Qed.
Lemma lem3898880 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term662 A a b x) = (term662 A a b x).
Proof. exact (eq_refl (term662 A a b x)). Qed.
Lemma lem3898881 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term663 A a b) = (term663 A a b).
Proof. exact (fun_ext (fun x : A => @lem3898880 A a b x)). Qed.
Lemma lem3898882 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3898884 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term664 A a b) = (term664 A a b).
Proof. exact (MK_COMB (@lem3898882 A) (@lem3898881 A a b)). Qed.
Lemma lem3898885 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term664 A a b.
Proof. exact (EQ_MP (@lem3898884 A a b) (@lem3898804 A a b h1)). Qed.
Lemma lem3898893 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3898943 {A : Type'} (b : A -> Prop) (x : A) (h1 : term543 A b x) : term543 A b x.
Proof. exact (h1). Qed.
Lemma lem3898968 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3898969 {A : Type'} (_45296 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term681 A a b _45296.
Proof. exact (@lem3898885 A a b h1 _45296). Qed.
Lemma lem3898970 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45296 : A) : (term681 A a b _45296) = (term662 A a b _45296).
Proof. exact (eq_refl (term681 A a b _45296)). Qed.
Lemma lem3898986 {A : Type'} (_45296 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term662 A a b _45296.
Proof. exact (EQ_MP (@lem3898970 A a b _45296) (@lem3898969 A _45296 a b h1)). Qed.
Lemma lem3898988 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term680 A a b x) : term543 A b x.
Proof. exact (proj2 (@lem3898859 A a b x h1)). Qed.
Lemma lem3898990 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3898998 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term680 A a b x) : term543 A b x.
Proof. exact (proj2 (@lem3898859 A a b x h1)). Qed.
Lemma lem3899014 {A : Type'} (b : A -> Prop) (x : A) (h1 : term543 A b x) : term543 A b x.
Proof. exact (h1). Qed.
Lemma lem3899024 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term676 A a b x) : term543 A a x.
Proof. exact (proj1 (@lem3898868 A a b x h1)). Qed.
Lemma lem3899026 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3899028 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3899029 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : term567 A a x.
Proof. exact (fun h0 : term543 A a x => @lem3899028 A a x h1). Qed.
Lemma lem3899031 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3899032 {A : Type'} (a : A -> Prop) (x : A) : (term567 A a x) = (a x).
Proof. exact (@lem3899031 (a x)). Qed.
Lemma lem3899033 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem3899032 A a x) (@lem3899029 A a x h1)). Qed.
Lemma lem3899039 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3899040 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45296 : A) : (term662 A a b _45296) = (term682 A b a _45296).
Proof. exact (@lem3899039 (b _45296) (term543 A a _45296)). Qed.
Lemma lem3899046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3899047 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45296 : A) : (term683 A a b _45296) = (term684 A b a _45296).
Proof. exact (MK_COMB (@lem3899046) (@lem3899040 A b a _45296)). Qed.
Lemma lem3899053 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45296 : A) : (term682 A b a _45296) = (term682 A b a _45296).
Proof. exact (eq_refl (term682 A b a _45296)). Qed.
Lemma lem3899054 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45296 : A) : ((term662 A a b _45296) = (term682 A b a _45296)) = ((term682 A b a _45296) = (term682 A b a _45296)).
Proof. exact (MK_COMB (@lem3899047 A b a _45296) (@lem3899053 A b a _45296)). Qed.
Lemma lem3899056 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3899057 (x : Prop) : (x = x) = True.
Proof. exact (@lem3899056 Prop x). Qed.
Lemma lem3899058 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45296 : A) : ((term682 A b a _45296) = (term682 A b a _45296)) = True.
Proof. exact (@lem3899057 (term682 A b a _45296)). Qed.
Lemma lem3899059 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45296 : A) : ((term662 A a b _45296) = (term682 A b a _45296)) = True.
Proof. exact (TRANS (@lem3899054 A b a _45296) (@lem3899058 A b a _45296)). Qed.
Lemma lem3899060 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45296 : A) : True = ((term662 A a b _45296) = (term682 A b a _45296)).
Proof. exact (SYM (@lem3899059 A b a _45296)). Qed.
Lemma lem3899061 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45296 : A) : (term662 A a b _45296) = (term682 A b a _45296).
Proof. exact (EQ_MP (@lem3899060 A b a _45296) (@lem0)). Qed.
Lemma lem3899062 {A : Type'} (_45296 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term682 A b a _45296.
Proof. exact (EQ_MP (@lem3899061 A b a _45296) (@lem3898986 A _45296 a b h1)). Qed.
Lemma lem3899064 (b : Prop) (a : Prop) : (a \/ b) = (term515 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3899065 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45296 : A) : (term682 A b a _45296) = (term685 A a b _45296).
Proof. exact (@lem3899064 (term543 A a _45296) (b _45296)). Qed.
Lemma lem3899067 (a : Prop) : (term128 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3899068 {A : Type'} (a : A -> Prop) (_45296 : A) : (term665 A a _45296) = (a _45296).
Proof. exact (@lem3899067 (a _45296)). Qed.
Lemma lem3899069 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3899070 {A : Type'} (a : A -> Prop) (_45296 : A) : (term686 A a _45296) = (term626 A a _45296).
Proof. exact (MK_COMB (@lem3899069) (@lem3899068 A a _45296)). Qed.
Lemma lem3899071 {A : Type'} (b : A -> Prop) (_45296 : A) : (b _45296) = (b _45296).
Proof. exact (eq_refl (b _45296)). Qed.
Lemma lem3899072 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45296 : A) : (term685 A a b _45296) = (term628 A a b _45296).
Proof. exact (MK_COMB (@lem3899070 A a _45296) (@lem3899071 A b _45296)). Qed.
Lemma lem3899073 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45296 : A) : (term682 A b a _45296) = (term628 A a b _45296).
Proof. exact (TRANS (@lem3899065 A a b _45296) (@lem3899072 A a b _45296)). Qed.
Lemma lem3899076 {A : Type'} (_45296 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term628 A a b _45296.
Proof. exact (EQ_MP (@lem3899073 A a b _45296) (@lem3899062 A _45296 a b h1)). Qed.
Lemma lem3899077 {A : Type'} (_45296 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term628 A a b _45296.
Proof. exact (@lem3899076 A _45296 a b h1). Qed.
Lemma lem3899078 {A : Type'} (x : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term628 A a b x.
Proof. exact (@lem3899077 A x a b h1). Qed.
Lemma lem3899081 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : a x) : b x.
Proof. exact (@lem3899078 A x a b h1 (@lem3899033 A a x h2)). Qed.
Lemma lem3899082 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : a x) : term567 A b x.
Proof. exact (fun h0 : term543 A b x => @lem3899081 A b a x h1 h2). Qed.
Lemma lem3899084 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3899085 {A : Type'} (b : A -> Prop) (x : A) : (term567 A b x) = (b x).
Proof. exact (@lem3899084 (b x)). Qed.
Lemma lem3899086 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : a x) : b x.
Proof. exact (EQ_MP (@lem3899085 A b x) (@lem3899082 A b a x h1 h2)). Qed.
Lemma lem3899089 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3899091 {A : Type'} (b : A -> Prop) (x : A) : (term543 A b x) = (term568 A b x).
Proof. exact (@lem3899089 (b x)). Qed.
Lemma lem3899094 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term680 A a b x) : term568 A b x.
Proof. exact (EQ_MP (@lem3899091 A b x) (@lem3898988 A a b x h1)). Qed.
Lemma lem3899097 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : a x) (h3 : term680 A a b x) : False.
Proof. exact (@lem3899094 A a b x h3 (@lem3899086 A b a x h1 h2)). Qed.
Lemma lem3899098 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : a x) (h3 : term680 A a b x) : term528.
Proof. exact (fun h0 : ~ False => @lem3899097 A a b x h1 h2 h3). Qed.
Lemma lem3899100 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3899101 : term528 = False.
Proof. exact (@lem3899100 False). Qed.
Lemma lem3899102 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : a x) (h3 : term680 A a b x) : False.
Proof. exact (EQ_MP (@lem3899101) (@lem3899098 A a b x h1 h2 h3)). Qed.
Lemma lem3899104 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term544 A b a x) : b x.
Proof. exact (proj1 (@lem3898864 A b a x h1)). Qed.
Lemma lem3899105 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term544 A b a x) : term567 A b x.
Proof. exact (fun h0 : term543 A b x => @lem3899104 A b a x h1). Qed.
Lemma lem3899107 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3899108 {A : Type'} (b : A -> Prop) (x : A) : (term567 A b x) = (b x).
Proof. exact (@lem3899107 (b x)). Qed.
Lemma lem3899109 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) (h1 : term544 A b a x) : b x.
Proof. exact (EQ_MP (@lem3899108 A b x) (@lem3899105 A b a x h1)). Qed.
Lemma lem3899112 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3899114 {A : Type'} (b : A -> Prop) (x : A) : (term543 A b x) = (term568 A b x).
Proof. exact (@lem3899112 (b x)). Qed.
Lemma lem3899117 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term680 A a b x) : term568 A b x.
Proof. exact (EQ_MP (@lem3899114 A b x) (@lem3898998 A a b x h1)). Qed.
Lemma lem3899120 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term544 A b a x) (h2 : term680 A a b x) : False.
Proof. exact (@lem3899117 A a b x h2 (@lem3899109 A b a x h1)). Qed.
Lemma lem3899121 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term544 A b a x) (h2 : term680 A a b x) : term528.
Proof. exact (fun h0 : ~ False => @lem3899120 A a b x h1 h2). Qed.
Lemma lem3899123 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3899124 : term528 = False.
Proof. exact (@lem3899123 False). Qed.
Lemma lem3899125 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term544 A b a x) (h2 : term680 A a b x) : False.
Proof. exact (EQ_MP (@lem3899124) (@lem3899121 A a b x h1 h2)). Qed.
Lemma lem3899127 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term676 A a b x) : b x.
Proof. exact (proj2 (@lem3898860 A a b x h1)). Qed.
Lemma lem3899128 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term676 A a b x) : term567 A b x.
Proof. exact (fun h0 : term543 A b x => @lem3899127 A a b x h1). Qed.
Lemma lem3899130 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3899131 {A : Type'} (b : A -> Prop) (x : A) : (term567 A b x) = (b x).
Proof. exact (@lem3899130 (b x)). Qed.
Lemma lem3899132 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term676 A a b x) : b x.
Proof. exact (EQ_MP (@lem3899131 A b x) (@lem3899128 A a b x h1)). Qed.
Lemma lem3899135 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3899137 {A : Type'} (b : A -> Prop) (x : A) : (term543 A b x) = (term568 A b x).
Proof. exact (@lem3899135 (b x)). Qed.
Lemma lem3899140 {A : Type'} (b : A -> Prop) (x : A) (h1 : term543 A b x) : term568 A b x.
Proof. exact (EQ_MP (@lem3899137 A b x) (@lem3899014 A b x h1)). Qed.
Lemma lem3899143 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term676 A a b x) : False.
Proof. exact (@lem3899140 A b x h1 (@lem3899132 A a b x h2)). Qed.
Lemma lem3899144 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term676 A a b x) : term528.
Proof. exact (fun h0 : ~ False => @lem3899143 A a b x h1 h2). Qed.
Lemma lem3899146 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3899147 : term528 = False.
Proof. exact (@lem3899146 False). Qed.
Lemma lem3899148 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term676 A a b x) : False.
Proof. exact (EQ_MP (@lem3899147) (@lem3899144 A a b x h1 h2)). Qed.
Lemma lem3899150 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3899151 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : term567 A a x.
Proof. exact (fun h0 : term543 A a x => @lem3899150 A a x h1). Qed.
Lemma lem3899153 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3899154 {A : Type'} (a : A -> Prop) (x : A) : (term567 A a x) = (a x).
Proof. exact (@lem3899153 (a x)). Qed.
Lemma lem3899155 {A : Type'} (a : A -> Prop) (x : A) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem3899154 A a x) (@lem3899151 A a x h1)). Qed.
Lemma lem3899158 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3899160 {A : Type'} (a : A -> Prop) (x : A) : (term543 A a x) = (term568 A a x).
Proof. exact (@lem3899158 (a x)). Qed.
Lemma lem3899163 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term676 A a b x) : term568 A a x.
Proof. exact (EQ_MP (@lem3899160 A a x) (@lem3899024 A a b x h1)). Qed.
Lemma lem3899166 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : a x) (h2 : term676 A a b x) : False.
Proof. exact (@lem3899163 A a b x h2 (@lem3899155 A a x h1)). Qed.
Lemma lem3899167 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : a x) (h2 : term676 A a b x) : term528.
Proof. exact (fun h0 : ~ False => @lem3899166 A a b x h1 h2). Qed.
Lemma lem3899169 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3899170 : term528 = False.
Proof. exact (@lem3899169 False). Qed.
Lemma lem3899171 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : a x) (h2 : term676 A a b x) : False.
Proof. exact (EQ_MP (@lem3899170) (@lem3899167 A a b x h1 h2)). Qed.
Lemma lem3899172 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : a x) (h2 : term676 A a b x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem3899171 A a b x h1 h2) (fun h3 : False => @lem3899026 A a x h1)). Qed.
Lemma lem3899173 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : a x) (h2 : term676 A a b x) : False.
Proof. exact (EQ_MP (@lem3899172 A a b x h1 h2) (@lem3899026 A a x h1)). Qed.
Lemma lem3899174 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term676 A a b x) : (term543 A b x) = False.
Proof. exact (prop_ext (fun h3 : term543 A b x => @lem3899148 A a b x h1 h2) (fun h3 : False => @lem3899014 A b x h1)). Qed.
Lemma lem3899175 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term676 A a b x) : False.
Proof. exact (EQ_MP (@lem3899174 A a b x h1 h2) (@lem3899014 A b x h1)). Qed.
Lemma lem3899176 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : a x) (h3 : term680 A a b x) : (a x) = False.
Proof. exact (prop_ext (fun h4 : a x => @lem3899102 A a b x h1 h2 h3) (fun h4 : False => @lem3898990 A a x h2)). Qed.
Lemma lem3899177 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : a x) (h3 : term680 A a b x) : False.
Proof. exact (EQ_MP (@lem3899176 A a b x h1 h2 h3) (@lem3898990 A a x h2)). Qed.
Lemma lem3899178 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : a x) (h2 : term676 A a b x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem3899173 A a b x h1 h2) (fun h3 : False => @lem3898968 A a x h1)). Qed.
Lemma lem3899179 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : a x) (h2 : term676 A a b x) : False.
Proof. exact (EQ_MP (@lem3899178 A a b x h1 h2) (@lem3898968 A a x h1)). Qed.
Lemma lem3899180 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term676 A a b x) : (term543 A b x) = False.
Proof. exact (prop_ext (fun h3 : term543 A b x => @lem3899175 A a b x h1 h2) (fun h3 : False => @lem3898943 A b x h1)). Qed.
Lemma lem3899181 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term676 A a b x) : False.
Proof. exact (EQ_MP (@lem3899180 A a b x h1 h2) (@lem3898943 A b x h1)). Qed.
Lemma lem3899182 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : a x) (h3 : term680 A a b x) : (a x) = False.
Proof. exact (prop_ext (fun h4 : a x => @lem3899177 A a b x h1 h2 h3) (fun h4 : False => @lem3898893 A a x h2)). Qed.
Lemma lem3899183 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : a x) (h3 : term680 A a b x) : False.
Proof. exact (EQ_MP (@lem3899182 A a b x h1 h2 h3) (@lem3898893 A a x h2)). Qed.
Lemma lem3899184 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : a x) (h2 : term676 A a b x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem3899179 A a b x h1 h2) (fun h3 : False => @lem3898968 A a x h1)). Qed.
Lemma lem3899185 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : a x) (h2 : term676 A a b x) : False.
Proof. exact (EQ_MP (@lem3899184 A a b x h1 h2) (@lem3898968 A a x h1)). Qed.
Lemma lem3899186 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term676 A a b x) : (term543 A b x) = False.
Proof. exact (prop_ext (fun h3 : term543 A b x => @lem3899181 A a b x h1 h2) (fun h3 : False => @lem3898943 A b x h1)). Qed.
Lemma lem3899187 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term543 A b x) (h2 : term676 A a b x) : False.
Proof. exact (EQ_MP (@lem3899186 A a b x h1 h2) (@lem3898943 A b x h1)). Qed.
Lemma lem3899188 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : a x) (h3 : term680 A a b x) : (a x) = False.
Proof. exact (prop_ext (fun h4 : a x => @lem3899183 A a b x h1 h2 h3) (fun h4 : False => @lem3898893 A a x h2)). Qed.
Lemma lem3899189 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : a x) (h3 : term680 A a b x) : False.
Proof. exact (EQ_MP (@lem3899188 A a b x h1 h2 h3) (@lem3898893 A a x h2)). Qed.
Lemma lem3899190 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term676 A a b x) : False.
Proof. exact (or_elim (@lem3898869 A a b x h1) (fun h0 : term543 A b x => @lem3899187 A a b x h0 h1) (fun h0 : a x => @lem3899185 A a b x h0 h1)). Qed.
Lemma lem3899191 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : term680 A a b x) : False.
Proof. exact (or_elim (@lem3898862 A a b x h2) (fun h0 : a x => @lem3899189 A a b x h1 h0 h2) (fun h0 : term544 A b a x => @lem3899125 A a b x h0 h2)). Qed.
Lemma lem3899192 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : term661 A a b x) : False.
Proof. exact (or_elim (@lem3898858 A a b x h2) (fun h0 : term680 A a b x => @lem3899191 A a b x h1 h0) (fun h0 : term676 A a b x => @lem3899190 A a b x h0)). Qed.
Lemma lem3899193 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : term661 A a b x) : (term661 A a b x) = False.
Proof. exact (prop_ext (fun h3 : term661 A a b x => @lem3899192 A a b x h1 h2) (fun h3 : False => @lem3898700 A a b x h2)). Qed.
Lemma lem3899194 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : term661 A a b x) : False.
Proof. exact (EQ_MP (@lem3899193 A a b x h1 h2) (@lem3898700 A a b x h2)). Qed.
Lemma lem3899195 {A : Type'} (x : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term660 A a b x.
Proof. exact (fun h0 : term661 A a b x => @lem3899194 A a b x h1 h0). Qed.
Lemma lem3899196 {A : Type'} (x : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : (term639 A b a x) = (b x).
Proof. exact (EQ_MP (@lem3898699 A a b x) (@lem3899195 A x a b h1)). Qed.
Lemma lem3899201 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term644 A a b.
Proof. exact (fun x : A => @lem3899196 A x a b h1). Qed.
Lemma lem3899202 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term645 A a b.
Proof. exact (fun h0 : term631 A a b => @lem3899201 A a b h0). Qed.
Lemma lem3899207 {A : Type'} (b : A -> Prop) : term655 A b.
Proof. exact (fun a : A -> Prop => @lem3899202 A a b). Qed.
Lemma lem3899212 {A : Type'} : term659 A.
Proof. exact (fun b : A -> Prop => @lem3899207 A b). Qed.
Lemma lem3899213 {A : Type'} : term658 A.
Proof. exact (EQ_MP (@lem3898694 A) (@lem3899212 A)). Qed.
Lemma lem3899214 {A : Type'} (b : A -> Prop) : term687 A b.
Proof. exact (@lem3899213 A b). Qed.
Lemma lem3899215 {A : Type'} (b : A -> Prop) : (term687 A b) = (term654 A b).
Proof. exact (eq_refl (term687 A b)). Qed.
Lemma lem3899216 {A : Type'} (b : A -> Prop) : term654 A b.
Proof. exact (EQ_MP (@lem3899215 A b) (@lem3899214 A b)). Qed.
Lemma lem3899217 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term688 A b a.
Proof. exact (@lem3899216 A b a). Qed.
Lemma lem3899218 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term688 A b a) = (term646 A a b).
Proof. exact (eq_refl (term688 A b a)). Qed.
Lemma lem3899219 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term646 A a b.
Proof. exact (EQ_MP (@lem3899218 A a b) (@lem3899217 A b a)). Qed.
Lemma lem3899221 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term646 A a b.
Proof. exact (@lem3898574 A a b (@lem3899219 A a b)). Qed.
Lemma lem3899222 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term647 A a b) : False.
Proof. exact (@lem3899221 A a b (@lem3898558 A a b h1)). Qed.
Lemma lem3899223 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term647 A a b) : (term647 A a b) = False.
Proof. exact (prop_ext (fun h2 : term647 A a b => @lem3899222 A a b h1) (fun h2 : False => @lem3898558 A a b h1)). Qed.
Lemma lem3899224 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term647 A a b) : False.
Proof. exact (EQ_MP (@lem3899223 A a b h1) (@lem3898558 A a b h1)). Qed.
Lemma lem3899225 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term646 A a b.
Proof. exact (fun h0 : term647 A a b => @lem3899224 A a b h0). Qed.
Lemma lem3899226 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term645 A a b.
Proof. exact (EQ_MP (@lem3898557 A a b) (@lem3899225 A a b)). Qed.
Lemma lem3899227 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term624 A a b.
Proof. exact (EQ_MP (@lem3898553 A a b) (@lem3899226 A a b)). Qed.
Lemma lem3899228 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term623 A a b.
Proof. exact (EQ_MP (@lem3898459 A a b) (@lem3899227 A a b)). Qed.
Lemma lem3899229 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : (term620 A b a) = b.
Proof. exact (@lem3899228 A a b (@lem3896973 A a b h1)). Qed.
Lemma lem3899245 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (term620 A b a) = b) : (term620 A b a) = b.
Proof. exact (h1). Qed.
Lemma lem3899246 {A : Type'} : (@CARD A) = (@CARD A).
Proof. exact (eq_refl (@CARD A)). Qed.
Lemma lem3899247 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (term620 A b a) = b) : (term614 A b a) = (@CARD A b).
Proof. exact (MK_COMB (@lem3899246 A) (@lem3899245 A a b h1)). Qed.
Lemma lem3899248 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3899249 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (term620 A b a) = b) : (term613 A b a) = (term689 A b).
Proof. exact (MK_COMB (@lem3899248) (@lem3899247 A a b h1)). Qed.
Lemma lem3899250 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term612 A b a) = (term612 A b a).
Proof. exact (eq_refl (term612 A b a)). Qed.
Lemma lem3899251 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (term620 A b a) = b) : ((term614 A b a) = (term612 A b a)) = ((@CARD A b) = (term612 A b a)).
Proof. exact (MK_COMB (@lem3899249 A a b h1) (@lem3899250 A b a)). Qed.
Lemma lem3899254 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3899255 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (term620 A b a) = b) : (term617 A b a) = (term690 A b a).
Proof. exact (MK_COMB (@lem3899254) (@lem3899251 A a b h1)). Qed.
Lemma lem3899258 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (a = b) = (a = b).
Proof. exact (eq_refl (a = b)). Qed.
Lemma lem3899259 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (term620 A b a) = b) : (term619 A a b) = (term691 A a b).
Proof. exact (MK_COMB (@lem3899255 A a b h1) (@lem3899258 A a b)). Qed.
Lemma lem3899264 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (term620 A b a) = b) : (term691 A a b) = (term619 A a b).
Proof. exact (SYM (@lem3899259 A a b h1)). Qed.
Lemma lem3899270 (a : nat) (b : nat) : (a = (Nat.add a b)) = (b = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem3896900 a b) (@lem3896899 a b)). Qed.
Lemma lem3899271 {A : Type'} (b : A -> Prop) (a : A -> Prop) : ((@CARD A b) = (term612 A b a)) = ((term610 A b a) = (NUMERAL 0)).
Proof. exact (@lem3899270 (@CARD A b) (term610 A b a)). Qed.
Lemma lem3899274 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3899275 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term690 A b a) = (term692 A b a).
Proof. exact (MK_COMB (@lem3899274) (@lem3899271 A b a)). Qed.
Lemma lem3899278 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (a = b) = (a = b).
Proof. exact (eq_refl (a = b)). Qed.
Lemma lem3899279 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term691 A a b) = (term693 A a b).
Proof. exact (MK_COMB (@lem3899275 A b a) (@lem3899278 A a b)). Qed.
Lemma lem3899284 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term693 A a b) = (term691 A a b).
Proof. exact (SYM (@lem3899279 A a b)). Qed.
Lemma lem3899286 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (@DIFF A b a) = (@EMPTY A)) : (@DIFF A b a) = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3899288 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term0 A s).
Proof. exact (EQ_MP (@lem3892963 A s) (@lem3892962 A s)). Qed.
Lemma lem3899289 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (term0 A s).
Proof. exact (@lem3899288 A s). Qed.
Lemma lem3899290 {A : Type'} (b : A -> Prop) (a : A -> Prop) : ((@DIFF A b a) = (@EMPTY A)) = (term694 A b a).
Proof. exact (@lem3899289 A (@DIFF A b a)). Qed.
Lemma lem3899291 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term694 A b a) = ((@DIFF A b a) = (@EMPTY A)).
Proof. exact (SYM (@lem3899290 A b a)). Qed.
Lemma lem3899292 {_100044 : Type'} (s : _100044 -> Prop) : term695 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem3899293 {_100044 : Type'} (s : _100044 -> Prop) : (term695 _100044 s) = (term696 _100044 s).
Proof. exact (eq_refl (term695 _100044 s)). Qed.
Lemma lem3899294 {_100044 : Type'} (s : _100044 -> Prop) : term696 _100044 s.
Proof. exact (EQ_MP (@lem3899293 _100044 s) (@lem3899292 _100044 s)). Qed.
Lemma lem3899295 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term697 _100044 s n.
Proof. exact (@lem3899294 _100044 s n). Qed.
Lemma lem3899296 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term697 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term698 _100044 s n)).
Proof. exact (eq_refl (term697 _100044 s n)). Qed.
Lemma lem3899304 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term531 A b a) = ((term531 A b a) = True).
Proof. exact (@lem7 (term531 A b a)). Qed.
Lemma lem3899307 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term698 _100044 s n).
Proof. exact (EQ_MP (@lem3899296 _100044 s n) (@lem3899295 _100044 s n)). Qed.
Lemma lem3899308 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term698 A s n).
Proof. exact (@lem3899307 A s n). Qed.
Lemma lem3899309 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term694 A b a) = (term699 A b a).
Proof. exact (@lem3899308 A (@DIFF A b a) (NUMERAL 0)). Qed.
Lemma lem3899313 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) : (term531 A b a) = True.
Proof. exact (EQ_MP (@lem3899304 A b a) (@lem3897716 A b a h1)). Qed.
Lemma lem3899314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3899315 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) : (term604 A b a) = (and True).
Proof. exact (MK_COMB (@lem3899314) (@lem3899313 A b a h1)). Qed.
Lemma lem3899319 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term610 A b a) = (NUMERAL 0)) : (term610 A b a) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3899320 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3899321 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term610 A b a) = (NUMERAL 0)) : (term700 A b a) = term701.
Proof. exact (MK_COMB (@lem3899320) (@lem3899319 A b a h1)). Qed.
Lemma lem3899322 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem3899323 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term610 A b a) = (NUMERAL 0)) : ((term610 A b a) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem3899321 A b a h1) (@lem3899322)). Qed.
Lemma lem3899325 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3899326 (x : nat) : (x = x) = True.
Proof. exact (@lem3899325 nat x). Qed.
Lemma lem3899327 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem3899326 (NUMERAL 0)). Qed.
Lemma lem3899328 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : (term610 A b a) = (NUMERAL 0)) : ((term610 A b a) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem3899323 A b a h1) (@lem3899327)). Qed.
Lemma lem3899329 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) (h2 : (term610 A b a) = (NUMERAL 0)) : (term699 A b a) = (True /\ True).
Proof. exact (MK_COMB (@lem3899315 A b a h1) (@lem3899328 A b a h2)). Qed.
Lemma lem3899331 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3899332 : (True /\ True) = True.
Proof. exact (@lem3899331 True). Qed.
Lemma lem3899333 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) (h2 : (term610 A b a) = (NUMERAL 0)) : (term699 A b a) = True.
Proof. exact (TRANS (@lem3899329 A b a h1 h2) (@lem3899332)). Qed.
Lemma lem3899334 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) (h2 : (term610 A b a) = (NUMERAL 0)) : (term694 A b a) = True.
Proof. exact (TRANS (@lem3899309 A b a) (@lem3899333 A b a h1 h2)). Qed.
Lemma lem3899335 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) (h2 : (term610 A b a) = (NUMERAL 0)) : True = (term694 A b a).
Proof. exact (SYM (@lem3899334 A b a h1 h2)). Qed.
Lemma lem3899336 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) (h2 : (term610 A b a) = (NUMERAL 0)) : term694 A b a.
Proof. exact (EQ_MP (@lem3899335 A b a h1 h2) (@lem0)). Qed.
Lemma lem3899337 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term531 A b a) (h2 : (term610 A b a) = (NUMERAL 0)) : (@DIFF A b a) = (@EMPTY A).
Proof. exact (EQ_MP (@lem3899291 A b a) (@lem3899336 A b a h1 h2)). Qed.
Lemma lem3899341 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term536 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3899342 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term536 A s t).
Proof. exact (@lem3899341 A s t). Qed.
Lemma lem3899343 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (@SUBSET A a b) = (term536 A a b).
Proof. exact (@lem3899342 A a b). Qed.
Lemma lem3899350 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3899351 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term453 A a b) = (term621 A a b).
Proof. exact (MK_COMB (@lem3899350) (@lem3899343 A a b)). Qed.
Lemma lem3899359 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term574 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3899360 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term574 A s t).
Proof. exact (@lem3899359 A s t). Qed.
Lemma lem3899361 {A : Type'} (b : A -> Prop) (a : A -> Prop) : ((@DIFF A b a) = (@EMPTY A)) = (term702 A b a).
Proof. exact (@lem3899360 A (@DIFF A b a) (@EMPTY A)). Qed.
Lemma lem3899370 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3899371 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term703 A b a) = (term704 A b a).
Proof. exact (MK_COMB (@lem3899370) (@lem3899361 A b a)). Qed.
Lemma lem3899375 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term574 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3899376 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term574 A s t).
Proof. exact (@lem3899375 A s t). Qed.
Lemma lem3899377 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (a = b) = (term574 A a b).
Proof. exact (@lem3899376 A a b). Qed.
Lemma lem3899386 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term705 A a b) = (term706 A a b).
Proof. exact (MK_COMB (@lem3899371 A b a) (@lem3899377 A a b)). Qed.
Lemma lem3899389 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term707 A a b) = (term708 A a b).
Proof. exact (MK_COMB (@lem3899351 A a b) (@lem3899386 A a b)). Qed.
Lemma lem3899392 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term708 A a b) = (term707 A a b).
Proof. exact (SYM (@lem3899389 A a b)). Qed.
Lemma lem3899402 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3899403 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3899402 A P x). Qed.
Lemma lem3899404 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3899403 A a x). Qed.
Lemma lem3899405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3899406 {A : Type'} (a : A -> Prop) (x : A) : (term625 A x a) = (term626 A a x).
Proof. exact (MK_COMB (@lem3899405) (@lem3899404 A a x)). Qed.
Lemma lem3899408 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3899409 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3899408 A P x). Qed.
Lemma lem3899410 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3899409 A b x). Qed.
Lemma lem3899411 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term627 A a x b) = (term628 A a b x).
Proof. exact (MK_COMB (@lem3899406 A a x) (@lem3899410 A b x)). Qed.
Lemma lem3899414 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term629 A a b) = (term630 A a b).
Proof. exact (fun_ext (fun x : A => @lem3899411 A a b x)). Qed.
Lemma lem3899415 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3899416 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term536 A a b) = (term631 A a b).
Proof. exact (MK_COMB (@lem3899415 A) (@lem3899414 A a b)). Qed.
Lemma lem3899421 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3899422 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term621 A a b) = (term632 A a b).
Proof. exact (MK_COMB (@lem3899421) (@lem3899416 A a b)). Qed.
Lemma lem3899432 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term538 A x s t) = (term539 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3899433 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term538 A x s t) = (term539 A s x t).
Proof. exact (@lem3899432 A s x t). Qed.
Lemma lem3899434 {A : Type'} (b : A -> Prop) (x : A) (a : A -> Prop) : (term538 A x b a) = (term539 A b x a).
Proof. exact (@lem3899433 A b x a). Qed.
Lemma lem3899438 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3899439 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3899438 A P x). Qed.
Lemma lem3899440 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3899439 A b x). Qed.
Lemma lem3899441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3899442 {A : Type'} (b : A -> Prop) (x : A) : (term540 A x b) = (term541 A b x).
Proof. exact (MK_COMB (@lem3899441) (@lem3899440 A b x)). Qed.
Lemma lem3899444 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3899445 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3899444 A P x). Qed.
Lemma lem3899446 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3899445 A a x). Qed.
Lemma lem3899447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3899448 {A : Type'} (a : A -> Prop) (x : A) : (term542 A x a) = (term543 A a x).
Proof. exact (MK_COMB (@lem3899447) (@lem3899446 A a x)). Qed.
Lemma lem3899449 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term539 A b x a) = (term544 A b a x).
Proof. exact (MK_COMB (@lem3899442 A b x) (@lem3899448 A a x)). Qed.
Lemma lem3899452 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term538 A x b a) = (term544 A b a x).
Proof. exact (TRANS (@lem3899434 A b x a) (@lem3899449 A b a x)). Qed.
Lemma lem3899453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3899454 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term709 A x b a) = (term710 A b a x).
Proof. exact (MK_COMB (@lem3899453) (@lem3899452 A b a x)). Qed.
Lemma lem3899456 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3899457 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3899456 A x). Qed.
Lemma lem3899458 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : ((term538 A x b a) = (@IN A x (@EMPTY A))) = ((term544 A b a x) = False).
Proof. exact (MK_COMB (@lem3899454 A b a x) (@lem3899457 A x)). Qed.
Lemma lem3899460 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3899461 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : ((term544 A b a x) = False) = (term668 A b a x).
Proof. exact (@lem3899460 (term544 A b a x)). Qed.
Lemma lem3899464 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : ((term538 A x b a) = (@IN A x (@EMPTY A))) = (term668 A b a x).
Proof. exact (TRANS (@lem3899458 A b a x) (@lem3899461 A b a x)). Qed.
Lemma lem3899465 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term711 A b a) = (term712 A b a).
Proof. exact (fun_ext (fun x : A => @lem3899464 A b a x)). Qed.
Lemma lem3899466 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3899467 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term702 A b a) = (term713 A b a).
Proof. exact (MK_COMB (@lem3899466 A) (@lem3899465 A b a)). Qed.
Lemma lem3899472 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3899473 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term704 A b a) = (term714 A b a).
Proof. exact (MK_COMB (@lem3899472) (@lem3899467 A b a)). Qed.
Lemma lem3899481 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3899482 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3899481 A P x). Qed.
Lemma lem3899483 {A : Type'} (a : A -> Prop) (x : A) : (@IN A x a) = (a x).
Proof. exact (@lem3899482 A a x). Qed.
Lemma lem3899484 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3899485 {A : Type'} (a : A -> Prop) (x : A) : (term715 A x a) = (term716 A a x).
Proof. exact (MK_COMB (@lem3899484) (@lem3899483 A a x)). Qed.
Lemma lem3899487 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3899488 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3899487 A P x). Qed.
Lemma lem3899489 {A : Type'} (b : A -> Prop) (x : A) : (@IN A x b) = (b x).
Proof. exact (@lem3899488 A b x). Qed.
Lemma lem3899490 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : ((@IN A x a) = (@IN A x b)) = ((a x) = (b x)).
Proof. exact (MK_COMB (@lem3899485 A a x) (@lem3899489 A b x)). Qed.
Lemma lem3899493 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term717 A a b) = (term718 A a b).
Proof. exact (fun_ext (fun x : A => @lem3899490 A a b x)). Qed.
Lemma lem3899494 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3899495 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term574 A a b) = (term719 A a b).
Proof. exact (MK_COMB (@lem3899494 A) (@lem3899493 A a b)). Qed.
Lemma lem3899500 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term706 A a b) = (term720 A a b).
Proof. exact (MK_COMB (@lem3899473 A b a) (@lem3899495 A a b)). Qed.
Lemma lem3899503 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term708 A a b) = (term721 A a b).
Proof. exact (MK_COMB (@lem3899422 A a b) (@lem3899500 A a b)). Qed.
Lemma lem3899506 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term721 A a b) = (term708 A a b).
Proof. exact (SYM (@lem3899503 A a b)). Qed.
Lemma lem3899508 (p : Prop) : p = (term438 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3899509 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term721 A a b) = (term722 A a b).
Proof. exact (@lem3899508 (term721 A a b)). Qed.
Lemma lem3899510 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term722 A a b) = (term721 A a b).
Proof. exact (SYM (@lem3899509 A a b)). Qed.
Lemma lem3899511 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term723 A a b) : term723 A a b.
Proof. exact (h1). Qed.
Lemma lem3899514 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term722 A a b) : term722 A a b.
Proof. exact (h1). Qed.
Lemma lem3899515 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term724 A a b.
Proof. exact (fun h0 : term722 A a b => @lem3899514 A a b h0). Qed.
Lemma lem3899516 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term724 A a b) : term724 A a b.
Proof. exact (h1). Qed.
Lemma lem3899517 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term722 A a b) : term722 A a b.
Proof. exact (h1). Qed.
Lemma lem3899518 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term722 A a b) (h2 : term724 A a b) : term722 A a b.
Proof. exact (@lem3899516 A a b h2 (@lem3899517 A a b h1)). Qed.
Lemma lem3899519 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term722 A a b) : term725 A a b.
Proof. exact (fun h0 : term724 A a b => @lem3899518 A a b h1 h0). Qed.
Lemma lem3899520 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term724 A a b) : term724 A a b.
Proof. exact (h1). Qed.
Lemma lem3899521 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term722 A a b) (h2 : term724 A a b) : term722 A a b.
Proof. exact (@lem3899519 A a b h1 (@lem3899520 A a b h2)). Qed.
Lemma lem3899522 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term724 A a b) : term724 A a b.
Proof. exact (fun h0 : term722 A a b => @lem3899521 A a b h0 h1). Qed.
Lemma lem3899523 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term726 A a b.
Proof. exact (fun h0 : term724 A a b => @lem3899522 A a b h0). Qed.
Lemma lem3899526 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term724 A a b.
Proof. exact (@lem3899523 A a b (@lem3899515 A a b)). Qed.
Lemma lem3899527 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term724 A a b.
Proof. exact (@lem3899526 A a b). Qed.
Lemma lem3899537 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3899538 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term722 A a b) = (term727 A a b).
Proof. exact (@lem3899537 (term723 A a b)). Qed.
Lemma lem3899540 (t : Prop) : (term128 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3899541 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term727 A a b) = (term721 A a b).
Proof. exact (@lem3899540 (term721 A a b)). Qed.
Lemma lem3899544 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term722 A a b) = (term721 A a b).
Proof. exact (TRANS (@lem3899538 A a b) (@lem3899541 A a b)). Qed.
Lemma lem3899563 {A : Type'} (b : A -> Prop) : (term728 A b) = (term729 A b).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3899544 A a b)). Qed.
Lemma lem3899564 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3899565 {A : Type'} (b : A -> Prop) : (term730 A b) = (term731 A b).
Proof. exact (MK_COMB (@lem3899564 A) (@lem3899563 A b)). Qed.
Lemma lem3899570 {A : Type'} : (term732 A) = (term733 A).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3899565 A b)). Qed.
Lemma lem3899571 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3899580 {A : Type'} : (term734 A) = (term735 A).
Proof. exact (MK_COMB (@lem3899571 A) (@lem3899570 A)). Qed.
Lemma lem3899585 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : ((a x) = (b x)) = ((a x) = (b x)).
Proof. exact (eq_refl ((a x) = (b x))). Qed.
Lemma lem3899586 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term718 A a b) = (term718 A a b).
Proof. exact (fun_ext (fun x : A => @lem3899585 A a b x)). Qed.
Lemma lem3899587 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3899588 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term719 A a b) = (term719 A a b).
Proof. exact (MK_COMB (@lem3899587 A) (@lem3899586 A a b)). Qed.
Lemma lem3899597 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term668 A b a x) = (term668 A b a x).
Proof. exact (eq_refl (term668 A b a x)). Qed.
Lemma lem3899598 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term712 A b a) = (term712 A b a).
Proof. exact (fun_ext (fun x : A => @lem3899597 A b a x)). Qed.
Lemma lem3899599 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3899600 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term713 A b a) = (term713 A b a).
Proof. exact (MK_COMB (@lem3899599 A) (@lem3899598 A b a)). Qed.
Lemma lem3899601 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3899602 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term714 A b a) = (term714 A b a).
Proof. exact (MK_COMB (@lem3899601) (@lem3899600 A b a)). Qed.
Lemma lem3899603 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term720 A a b) = (term720 A a b).
Proof. exact (MK_COMB (@lem3899602 A b a) (@lem3899588 A a b)). Qed.
Lemma lem3899608 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term628 A a b x) = (term628 A a b x).
Proof. exact (eq_refl (term628 A a b x)). Qed.
Lemma lem3899609 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term630 A a b) = (term630 A a b).
Proof. exact (fun_ext (fun x : A => @lem3899608 A a b x)). Qed.
Lemma lem3899610 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3899611 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term631 A a b) = (term631 A a b).
Proof. exact (MK_COMB (@lem3899610 A) (@lem3899609 A a b)). Qed.
Lemma lem3899612 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3899613 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term632 A a b) = (term632 A a b).
Proof. exact (MK_COMB (@lem3899612) (@lem3899611 A a b)). Qed.
Lemma lem3899614 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term721 A a b) = (term721 A a b).
Proof. exact (MK_COMB (@lem3899613 A a b) (@lem3899603 A a b)). Qed.
Lemma lem3899615 {A : Type'} (b : A -> Prop) : (term729 A b) = (term729 A b).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3899614 A a b)). Qed.
Lemma lem3899616 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3899617 {A : Type'} (b : A -> Prop) : (term731 A b) = (term731 A b).
Proof. exact (MK_COMB (@lem3899616 A) (@lem3899615 A b)). Qed.
Lemma lem3899618 {A : Type'} : (term733 A) = (term733 A).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3899617 A b)). Qed.
Lemma lem3899619 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3899620 {A : Type'} : (term735 A) = (term735 A).
Proof. exact (MK_COMB (@lem3899619 A) (@lem3899618 A)). Qed.
Lemma lem3899661 {A : Type'} : (term734 A) = (term735 A).
Proof. exact (TRANS (@lem3899580 A) (@lem3899620 A)). Qed.
Lemma lem3899662 {A : Type'} : (term735 A) = (term734 A).
Proof. exact (SYM (@lem3899661 A)). Qed.
Lemma lem3899663 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term631 A a b.
Proof. exact (h1). Qed.
Lemma lem3899664 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term713 A b a) : term713 A b a.
Proof. exact (h1). Qed.
Lemma lem3899666 (p : Prop) : p = (term438 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3899667 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : ((a x) = (b x)) = (term736 A a b x).
Proof. exact (@lem3899666 ((a x) = (b x))). Qed.
Lemma lem3899668 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term736 A a b x) = ((a x) = (b x)).
Proof. exact (SYM (@lem3899667 A a b x)). Qed.
Lemma lem3899669 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term737 A a b x) : term737 A a b x.
Proof. exact (h1). Qed.
Lemma lem3899676 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term628 A a b x) = (term662 A a b x).
Proof. exact (@lem17265 (a x) (b x)). Qed.
Lemma lem3899677 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term630 A a b) = (term663 A a b).
Proof. exact (fun_ext (fun x : A => @lem3899676 A a b x)). Qed.
Lemma lem3899678 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3899715 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term631 A a b) = (term664 A a b).
Proof. exact (MK_COMB (@lem3899678 A) (@lem3899677 A a b)). Qed.
Lemma lem3899716 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term664 A a b.
Proof. exact (EQ_MP (@lem3899715 A a b) (@lem3899663 A a b h1)). Qed.
Lemma lem3899720 {A : Type'} (a : A -> Prop) (x : A) : (term665 A a x) = (a x).
Proof. exact (@lem16933 (a x)). Qed.
Lemma lem3899722 {A : Type'} (b : A -> Prop) (x : A) : (term666 A b x) = (term666 A b x).
Proof. exact (eq_refl (term666 A b x)). Qed.
Lemma lem3899723 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term667 A b a x) = (term662 A b a x).
Proof. exact (MK_COMB (@lem3899722 A b x) (@lem3899720 A a x)). Qed.
Lemma lem3899724 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term668 A b a x) = (term667 A b a x).
Proof. exact (@lem17045 (b x) (term543 A a x)). Qed.
Lemma lem3899725 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term668 A b a x) = (term662 A b a x).
Proof. exact (TRANS (@lem3899724 A b a x) (@lem3899723 A b a x)). Qed.
Lemma lem3899726 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term712 A b a) = (term663 A b a).
Proof. exact (fun_ext (fun x : A => @lem3899725 A b a x)). Qed.
Lemma lem3899727 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3899764 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term713 A b a) = (term664 A b a).
Proof. exact (MK_COMB (@lem3899727 A) (@lem3899726 A b a)). Qed.
Lemma lem3899765 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term713 A b a) : term664 A b a.
Proof. exact (EQ_MP (@lem3899764 A b a) (@lem3899664 A b a h1)). Qed.
Lemma lem3899784 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term737 A a b x) = (term738 A a b x).
Proof. exact (@lem17646 (a x) (b x)). Qed.
Lemma lem3899796 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term662 A a b x) = (term662 A a b x).
Proof. exact (eq_refl (term662 A a b x)). Qed.
Lemma lem3899797 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term663 A a b) = (term663 A a b).
Proof. exact (fun_ext (fun x : A => @lem3899796 A a b x)). Qed.
Lemma lem3899798 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3899799 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term664 A a b) = (term664 A a b).
Proof. exact (MK_COMB (@lem3899798 A) (@lem3899797 A a b)). Qed.
Lemma lem3899800 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term664 A a b.
Proof. exact (EQ_MP (@lem3899799 A a b) (@lem3899716 A a b h1)). Qed.
Lemma lem3899811 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term662 A b a x) = (term662 A b a x).
Proof. exact (eq_refl (term662 A b a x)). Qed.
Lemma lem3899812 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term663 A b a) = (term663 A b a).
Proof. exact (fun_ext (fun x : A => @lem3899811 A b a x)). Qed.
Lemma lem3899813 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3899814 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term664 A b a) = (term664 A b a).
Proof. exact (MK_COMB (@lem3899813 A) (@lem3899812 A b a)). Qed.
Lemma lem3899815 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term713 A b a) : term664 A b a.
Proof. exact (EQ_MP (@lem3899814 A b a) (@lem3899765 A b a h1)). Qed.
Lemma lem3899841 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term737 A a b x) : term738 A a b x.
Proof. exact (EQ_MP (@lem3899784 A a b x) (@lem3899669 A a b x h1)). Qed.
Lemma lem3899842 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term544 A a b x) : term544 A a b x.
Proof. exact (h1). Qed.
Lemma lem3899843 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term739 A a b x) : term739 A a b x.
Proof. exact (h1). Qed.
Lemma lem3899855 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term662 A a b x) = (term662 A a b x).
Proof. exact (eq_refl (term662 A a b x)). Qed.
Lemma lem3899856 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term663 A a b) = (term663 A a b).
Proof. exact (fun_ext (fun x : A => @lem3899855 A a b x)). Qed.
Lemma lem3899857 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3899859 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term664 A a b) = (term664 A a b).
Proof. exact (MK_COMB (@lem3899857 A) (@lem3899856 A a b)). Qed.
Lemma lem3899860 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term664 A a b.
Proof. exact (EQ_MP (@lem3899859 A a b) (@lem3899800 A a b h1)). Qed.
Lemma lem3899902 {A : Type'} (b : A -> Prop) (a : A -> Prop) (x : A) : (term662 A b a x) = (term662 A b a x).
Proof. exact (eq_refl (term662 A b a x)). Qed.
Lemma lem3899903 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term663 A b a) = (term663 A b a).
Proof. exact (fun_ext (fun x : A => @lem3899902 A b a x)). Qed.
Lemma lem3899904 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3899906 {A : Type'} (b : A -> Prop) (a : A -> Prop) : (term664 A b a) = (term664 A b a).
Proof. exact (MK_COMB (@lem3899904 A) (@lem3899903 A b a)). Qed.
Lemma lem3899907 {A : Type'} (b : A -> Prop) (a : A -> Prop) (h1 : term713 A b a) : term664 A b a.
Proof. exact (EQ_MP (@lem3899906 A b a) (@lem3899815 A b a h1)). Qed.
Lemma lem3899916 {A : Type'} (_45300 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term681 A a b _45300.
Proof. exact (@lem3899860 A a b h1 _45300). Qed.
Lemma lem3899917 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45300 : A) : (term681 A a b _45300) = (term662 A a b _45300).
Proof. exact (eq_refl (term681 A a b _45300)). Qed.
Lemma lem3899925 {A : Type'} (_45303 : A) (b : A -> Prop) (a : A -> Prop) (h1 : term713 A b a) : term681 A b a _45303.
Proof. exact (@lem3899907 A b a h1 _45303). Qed.
Lemma lem3899926 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45303 : A) : (term681 A b a _45303) = (term662 A b a _45303).
Proof. exact (eq_refl (term681 A b a _45303)). Qed.
Lemma lem3899933 {A : Type'} (_45300 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term662 A a b _45300.
Proof. exact (EQ_MP (@lem3899917 A a b _45300) (@lem3899916 A _45300 a b h1)). Qed.
Lemma lem3899943 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term544 A a b x) : term543 A b x.
Proof. exact (proj2 (@lem3899842 A a b x h1)). Qed.
Lemma lem3899955 {A : Type'} (_45303 : A) (b : A -> Prop) (a : A -> Prop) (h1 : term713 A b a) : term662 A b a _45303.
Proof. exact (EQ_MP (@lem3899926 A b a _45303) (@lem3899925 A _45303 b a h1)). Qed.
Lemma lem3899957 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term739 A a b x) : term543 A a x.
Proof. exact (proj1 (@lem3899843 A a b x h1)). Qed.
Lemma lem3899961 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term544 A a b x) : a x.
Proof. exact (proj1 (@lem3899842 A a b x h1)). Qed.
Lemma lem3899962 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term544 A a b x) : term567 A a x.
Proof. exact (fun h0 : term543 A a x => @lem3899961 A a b x h1). Qed.
Lemma lem3899964 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3899965 {A : Type'} (a : A -> Prop) (x : A) : (term567 A a x) = (a x).
Proof. exact (@lem3899964 (a x)). Qed.
Lemma lem3899966 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term544 A a b x) : a x.
Proof. exact (EQ_MP (@lem3899965 A a x) (@lem3899962 A a b x h1)). Qed.
Lemma lem3899972 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3899973 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45300 : A) : (term662 A a b _45300) = (term682 A b a _45300).
Proof. exact (@lem3899972 (b _45300) (term543 A a _45300)). Qed.
Lemma lem3899979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3899980 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45300 : A) : (term683 A a b _45300) = (term684 A b a _45300).
Proof. exact (MK_COMB (@lem3899979) (@lem3899973 A b a _45300)). Qed.
Lemma lem3899986 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45300 : A) : (term682 A b a _45300) = (term682 A b a _45300).
Proof. exact (eq_refl (term682 A b a _45300)). Qed.
Lemma lem3899987 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45300 : A) : ((term662 A a b _45300) = (term682 A b a _45300)) = ((term682 A b a _45300) = (term682 A b a _45300)).
Proof. exact (MK_COMB (@lem3899980 A b a _45300) (@lem3899986 A b a _45300)). Qed.
Lemma lem3899989 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3899990 (x : Prop) : (x = x) = True.
Proof. exact (@lem3899989 Prop x). Qed.
Lemma lem3899991 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45300 : A) : ((term682 A b a _45300) = (term682 A b a _45300)) = True.
Proof. exact (@lem3899990 (term682 A b a _45300)). Qed.
Lemma lem3899992 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45300 : A) : ((term662 A a b _45300) = (term682 A b a _45300)) = True.
Proof. exact (TRANS (@lem3899987 A b a _45300) (@lem3899991 A b a _45300)). Qed.
Lemma lem3899993 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45300 : A) : True = ((term662 A a b _45300) = (term682 A b a _45300)).
Proof. exact (SYM (@lem3899992 A b a _45300)). Qed.
Lemma lem3899994 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45300 : A) : (term662 A a b _45300) = (term682 A b a _45300).
Proof. exact (EQ_MP (@lem3899993 A b a _45300) (@lem0)). Qed.
Lemma lem3899995 {A : Type'} (_45300 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term682 A b a _45300.
Proof. exact (EQ_MP (@lem3899994 A b a _45300) (@lem3899933 A _45300 a b h1)). Qed.
Lemma lem3899997 (b : Prop) (a : Prop) : (a \/ b) = (term515 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3899998 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45300 : A) : (term682 A b a _45300) = (term685 A a b _45300).
Proof. exact (@lem3899997 (term543 A a _45300) (b _45300)). Qed.
Lemma lem3900000 (a : Prop) : (term128 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3900001 {A : Type'} (a : A -> Prop) (_45300 : A) : (term665 A a _45300) = (a _45300).
Proof. exact (@lem3900000 (a _45300)). Qed.
Lemma lem3900002 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3900003 {A : Type'} (a : A -> Prop) (_45300 : A) : (term686 A a _45300) = (term626 A a _45300).
Proof. exact (MK_COMB (@lem3900002) (@lem3900001 A a _45300)). Qed.
Lemma lem3900004 {A : Type'} (b : A -> Prop) (_45300 : A) : (b _45300) = (b _45300).
Proof. exact (eq_refl (b _45300)). Qed.
Lemma lem3900005 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45300 : A) : (term685 A a b _45300) = (term628 A a b _45300).
Proof. exact (MK_COMB (@lem3900003 A a _45300) (@lem3900004 A b _45300)). Qed.
Lemma lem3900006 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45300 : A) : (term682 A b a _45300) = (term628 A a b _45300).
Proof. exact (TRANS (@lem3899998 A a b _45300) (@lem3900005 A a b _45300)). Qed.
Lemma lem3900009 {A : Type'} (_45300 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term628 A a b _45300.
Proof. exact (EQ_MP (@lem3900006 A a b _45300) (@lem3899995 A _45300 a b h1)). Qed.
Lemma lem3900010 {A : Type'} (_45300 : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term628 A a b _45300.
Proof. exact (@lem3900009 A _45300 a b h1). Qed.
Lemma lem3900011 {A : Type'} (x : A) (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term628 A a b x.
Proof. exact (@lem3900010 A x a b h1). Qed.
Lemma lem3900014 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : term544 A a b x) : b x.
Proof. exact (@lem3900011 A x a b h1 (@lem3899966 A a b x h2)). Qed.
Lemma lem3900015 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : term544 A a b x) : term567 A b x.
Proof. exact (fun h0 : term543 A b x => @lem3900014 A a b x h1 h2). Qed.
Lemma lem3900017 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3900018 {A : Type'} (b : A -> Prop) (x : A) : (term567 A b x) = (b x).
Proof. exact (@lem3900017 (b x)). Qed.
Lemma lem3900019 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : term544 A a b x) : b x.
Proof. exact (EQ_MP (@lem3900018 A b x) (@lem3900015 A a b x h1 h2)). Qed.
Lemma lem3900022 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3900024 {A : Type'} (b : A -> Prop) (x : A) : (term543 A b x) = (term568 A b x).
Proof. exact (@lem3900022 (b x)). Qed.
Lemma lem3900027 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term544 A a b x) : term568 A b x.
Proof. exact (EQ_MP (@lem3900024 A b x) (@lem3899943 A a b x h1)). Qed.
Lemma lem3900030 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : term544 A a b x) : False.
Proof. exact (@lem3900027 A a b x h2 (@lem3900019 A a b x h1 h2)). Qed.
Lemma lem3900031 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : term544 A a b x) : term528.
Proof. exact (fun h0 : ~ False => @lem3900030 A a b x h1 h2). Qed.
Lemma lem3900033 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3900034 : term528 = False.
Proof. exact (@lem3900033 False). Qed.
Lemma lem3900035 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term631 A a b) (h2 : term544 A a b x) : False.
Proof. exact (EQ_MP (@lem3900034) (@lem3900031 A a b x h1 h2)). Qed.
Lemma lem3900037 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term739 A a b x) : b x.
Proof. exact (proj2 (@lem3899843 A a b x h1)). Qed.
Lemma lem3900038 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term739 A a b x) : term567 A b x.
Proof. exact (fun h0 : term543 A b x => @lem3900037 A a b x h1). Qed.
Lemma lem3900040 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3900041 {A : Type'} (b : A -> Prop) (x : A) : (term567 A b x) = (b x).
Proof. exact (@lem3900040 (b x)). Qed.
Lemma lem3900042 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term739 A a b x) : b x.
Proof. exact (EQ_MP (@lem3900041 A b x) (@lem3900038 A a b x h1)). Qed.
Lemma lem3900048 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3900049 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45303 : A) : (term662 A b a _45303) = (term682 A a b _45303).
Proof. exact (@lem3900048 (a _45303) (term543 A b _45303)). Qed.
Lemma lem3900055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3900056 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45303 : A) : (term683 A b a _45303) = (term684 A a b _45303).
Proof. exact (MK_COMB (@lem3900055) (@lem3900049 A a b _45303)). Qed.
Lemma lem3900062 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45303 : A) : (term682 A a b _45303) = (term682 A a b _45303).
Proof. exact (eq_refl (term682 A a b _45303)). Qed.
Lemma lem3900063 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45303 : A) : ((term662 A b a _45303) = (term682 A a b _45303)) = ((term682 A a b _45303) = (term682 A a b _45303)).
Proof. exact (MK_COMB (@lem3900056 A a b _45303) (@lem3900062 A a b _45303)). Qed.
Lemma lem3900065 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3900066 (x : Prop) : (x = x) = True.
Proof. exact (@lem3900065 Prop x). Qed.
Lemma lem3900067 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45303 : A) : ((term682 A a b _45303) = (term682 A a b _45303)) = True.
Proof. exact (@lem3900066 (term682 A a b _45303)). Qed.
Lemma lem3900068 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45303 : A) : ((term662 A b a _45303) = (term682 A a b _45303)) = True.
Proof. exact (TRANS (@lem3900063 A a b _45303) (@lem3900067 A a b _45303)). Qed.
Lemma lem3900069 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45303 : A) : True = ((term662 A b a _45303) = (term682 A a b _45303)).
Proof. exact (SYM (@lem3900068 A a b _45303)). Qed.
Lemma lem3900070 {A : Type'} (a : A -> Prop) (b : A -> Prop) (_45303 : A) : (term662 A b a _45303) = (term682 A a b _45303).
Proof. exact (EQ_MP (@lem3900069 A a b _45303) (@lem0)). Qed.
Lemma lem3900071 {A : Type'} (_45303 : A) (b : A -> Prop) (a : A -> Prop) (h1 : term713 A b a) : term682 A a b _45303.
Proof. exact (EQ_MP (@lem3900070 A a b _45303) (@lem3899955 A _45303 b a h1)). Qed.
Lemma lem3900073 (b : Prop) (a : Prop) : (a \/ b) = (term515 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3900074 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45303 : A) : (term682 A a b _45303) = (term685 A b a _45303).
Proof. exact (@lem3900073 (term543 A b _45303) (a _45303)). Qed.
Lemma lem3900076 (a : Prop) : (term128 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3900077 {A : Type'} (b : A -> Prop) (_45303 : A) : (term665 A b _45303) = (b _45303).
Proof. exact (@lem3900076 (b _45303)). Qed.
Lemma lem3900078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3900079 {A : Type'} (b : A -> Prop) (_45303 : A) : (term686 A b _45303) = (term626 A b _45303).
Proof. exact (MK_COMB (@lem3900078) (@lem3900077 A b _45303)). Qed.
Lemma lem3900080 {A : Type'} (a : A -> Prop) (_45303 : A) : (a _45303) = (a _45303).
Proof. exact (eq_refl (a _45303)). Qed.
Lemma lem3900081 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45303 : A) : (term685 A b a _45303) = (term628 A b a _45303).
Proof. exact (MK_COMB (@lem3900079 A b _45303) (@lem3900080 A a _45303)). Qed.
Lemma lem3900082 {A : Type'} (b : A -> Prop) (a : A -> Prop) (_45303 : A) : (term682 A a b _45303) = (term628 A b a _45303).
Proof. exact (TRANS (@lem3900074 A b a _45303) (@lem3900081 A b a _45303)). Qed.
Lemma lem3900085 {A : Type'} (_45303 : A) (b : A -> Prop) (a : A -> Prop) (h1 : term713 A b a) : term628 A b a _45303.
Proof. exact (EQ_MP (@lem3900082 A b a _45303) (@lem3900071 A _45303 b a h1)). Qed.
Lemma lem3900086 {A : Type'} (_45303 : A) (b : A -> Prop) (a : A -> Prop) (h1 : term713 A b a) : term628 A b a _45303.
Proof. exact (@lem3900085 A _45303 b a h1). Qed.
Lemma lem3900087 {A : Type'} (x : A) (b : A -> Prop) (a : A -> Prop) (h1 : term713 A b a) : term628 A b a x.
Proof. exact (@lem3900086 A x b a h1). Qed.
Lemma lem3900090 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term713 A b a) (h2 : term739 A a b x) : a x.
Proof. exact (@lem3900087 A x b a h1 (@lem3900042 A a b x h2)). Qed.
Lemma lem3900091 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term713 A b a) (h2 : term739 A a b x) : term567 A a x.
Proof. exact (fun h0 : term543 A a x => @lem3900090 A a b x h1 h2). Qed.
Lemma lem3900093 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3900094 {A : Type'} (a : A -> Prop) (x : A) : (term567 A a x) = (a x).
Proof. exact (@lem3900093 (a x)). Qed.
Lemma lem3900095 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term713 A b a) (h2 : term739 A a b x) : a x.
Proof. exact (EQ_MP (@lem3900094 A a x) (@lem3900091 A a b x h1 h2)). Qed.
Lemma lem3900098 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3900100 {A : Type'} (a : A -> Prop) (x : A) : (term543 A a x) = (term568 A a x).
Proof. exact (@lem3900098 (a x)). Qed.
Lemma lem3900103 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term739 A a b x) : term568 A a x.
Proof. exact (EQ_MP (@lem3900100 A a x) (@lem3899957 A a b x h1)). Qed.
Lemma lem3900106 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term713 A b a) (h2 : term739 A a b x) : False.
Proof. exact (@lem3900103 A a b x h2 (@lem3900095 A a b x h1 h2)). Qed.
Lemma lem3900107 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term713 A b a) (h2 : term739 A a b x) : term528.
Proof. exact (fun h0 : ~ False => @lem3900106 A a b x h1 h2). Qed.
Lemma lem3900109 (p : Prop) : (term506 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3900110 : term528 = False.
Proof. exact (@lem3900109 False). Qed.
Lemma lem3900111 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term713 A b a) (h2 : term739 A a b x) : False.
Proof. exact (EQ_MP (@lem3900110) (@lem3900107 A a b x h1 h2)). Qed.
Lemma lem3900112 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term713 A b a) (h2 : term631 A a b) (h3 : term737 A a b x) : False.
Proof. exact (or_elim (@lem3899841 A a b x h3) (fun h0 : term544 A a b x => @lem3900035 A a b x h2 h0) (fun h0 : term739 A a b x => @lem3900111 A a b x h1 h0)). Qed.
Lemma lem3900113 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term713 A b a) (h2 : term631 A a b) (h3 : term737 A a b x) : (term737 A a b x) = False.
Proof. exact (prop_ext (fun h4 : term737 A a b x => @lem3900112 A a b x h1 h2 h3) (fun h4 : False => @lem3899669 A a b x h3)). Qed.
Lemma lem3900114 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term713 A b a) (h2 : term631 A a b) (h3 : term737 A a b x) : False.
Proof. exact (EQ_MP (@lem3900113 A a b x h1 h2 h3) (@lem3899669 A a b x h3)). Qed.
Lemma lem3900115 {A : Type'} (x : A) (a : A -> Prop) (b : A -> Prop) (h1 : term713 A b a) (h2 : term631 A a b) : term736 A a b x.
Proof. exact (fun h0 : term737 A a b x => @lem3900114 A a b x h1 h2 h0). Qed.
Lemma lem3900116 {A : Type'} (x : A) (a : A -> Prop) (b : A -> Prop) (h1 : term713 A b a) (h2 : term631 A a b) : (a x) = (b x).
Proof. exact (EQ_MP (@lem3899668 A a b x) (@lem3900115 A x a b h1 h2)). Qed.
Lemma lem3900121 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term713 A b a) (h2 : term631 A a b) : term719 A a b.
Proof. exact (fun x : A => @lem3900116 A x a b h1 h2). Qed.
Lemma lem3900122 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term631 A a b) : term720 A a b.
Proof. exact (fun h0 : term713 A b a => @lem3900121 A a b h0 h1). Qed.
Lemma lem3900123 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term721 A a b.
Proof. exact (fun h0 : term631 A a b => @lem3900122 A a b h0). Qed.
Lemma lem3900128 {A : Type'} (b : A -> Prop) : term731 A b.
Proof. exact (fun a : A -> Prop => @lem3900123 A a b). Qed.
Lemma lem3900133 {A : Type'} : term735 A.
Proof. exact (fun b : A -> Prop => @lem3900128 A b). Qed.
Lemma lem3900134 {A : Type'} : term734 A.
Proof. exact (EQ_MP (@lem3899662 A) (@lem3900133 A)). Qed.
Lemma lem3900135 {A : Type'} (b : A -> Prop) : term740 A b.
Proof. exact (@lem3900134 A b). Qed.
Lemma lem3900136 {A : Type'} (b : A -> Prop) : (term740 A b) = (term730 A b).
Proof. exact (eq_refl (term740 A b)). Qed.
Lemma lem3900137 {A : Type'} (b : A -> Prop) : term730 A b.
Proof. exact (EQ_MP (@lem3900136 A b) (@lem3900135 A b)). Qed.
Lemma lem3900138 {A : Type'} (b : A -> Prop) (a : A -> Prop) : term741 A b a.
Proof. exact (@lem3900137 A b a). Qed.
Lemma lem3900139 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term741 A b a) = (term722 A a b).
Proof. exact (eq_refl (term741 A b a)). Qed.
Lemma lem3900140 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term722 A a b.
Proof. exact (EQ_MP (@lem3900139 A a b) (@lem3900138 A b a)). Qed.
Lemma lem3900142 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term722 A a b.
Proof. exact (@lem3899527 A a b (@lem3900140 A a b)). Qed.
Lemma lem3900143 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term723 A a b) : False.
Proof. exact (@lem3900142 A a b (@lem3899511 A a b h1)). Qed.
Lemma lem3900144 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term723 A a b) : (term723 A a b) = False.
Proof. exact (prop_ext (fun h2 : term723 A a b => @lem3900143 A a b h1) (fun h2 : False => @lem3899511 A a b h1)). Qed.
Lemma lem3900145 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term723 A a b) : False.
Proof. exact (EQ_MP (@lem3900144 A a b h1) (@lem3899511 A a b h1)). Qed.
Lemma lem3900146 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term722 A a b.
Proof. exact (fun h0 : term723 A a b => @lem3900145 A a b h0). Qed.
Lemma lem3900147 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term721 A a b.
Proof. exact (EQ_MP (@lem3899510 A a b) (@lem3900146 A a b)). Qed.
Lemma lem3900148 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term708 A a b.
Proof. exact (EQ_MP (@lem3899506 A a b) (@lem3900147 A a b)). Qed.
Lemma lem3900149 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term707 A a b.
Proof. exact (EQ_MP (@lem3899392 A a b) (@lem3900148 A a b)). Qed.
Lemma lem3900150 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @SUBSET A a b) : term705 A a b.
Proof. exact (@lem3900149 A a b (@lem3896973 A a b h1)). Qed.
Lemma lem3900151 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : (@DIFF A b a) = (@EMPTY A)) (h2 : @SUBSET A a b) : a = b.
Proof. exact (@lem3900150 A a b h2 (@lem3899286 A b a h1)). Qed.
Lemma lem3900152 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term531 A b a) (h2 : (term610 A b a) = (NUMERAL 0)) (h3 : @SUBSET A a b) : ((@DIFF A b a) = (@EMPTY A)) = (a = b).
Proof. exact (prop_ext (fun h4 : (@DIFF A b a) = (@EMPTY A) => @lem3900151 A a b h4 h3) (fun h4 : a = b => @lem3899337 A b a h1 h2)). Qed.
Lemma lem3900153 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term531 A b a) (h2 : (term610 A b a) = (NUMERAL 0)) (h3 : @SUBSET A a b) : a = b.
Proof. exact (EQ_MP (@lem3900152 A a b h1 h2 h3) (@lem3899337 A b a h1 h2)). Qed.
Lemma lem3900154 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term531 A b a) (h2 : @SUBSET A a b) : term693 A a b.
Proof. exact (fun h0 : (term610 A b a) = (NUMERAL 0) => @lem3900153 A a b h1 h0 h2). Qed.
Lemma lem3900155 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term531 A b a) (h2 : @SUBSET A a b) : term691 A a b.
Proof. exact (EQ_MP (@lem3899284 A a b) (@lem3900154 A a b h1 h2)). Qed.
Lemma lem3900156 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term531 A b a) (h2 : (term620 A b a) = b) (h3 : @SUBSET A a b) : term619 A a b.
Proof. exact (EQ_MP (@lem3899264 A a b h2) (@lem3900155 A a b h1 h3)). Qed.
Lemma lem3900157 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term531 A b a) (h2 : (term620 A b a) = b) (h3 : @SUBSET A a b) : ((term620 A b a) = b) = (term619 A a b).
Proof. exact (prop_ext (fun h4 : (term620 A b a) = b => @lem3900156 A a b h1 h2 h3) (fun h4 : term619 A a b => @lem3898427 A a b h2)). Qed.
Lemma lem3900158 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term531 A b a) (h2 : (term620 A b a) = b) (h3 : @SUBSET A a b) : term619 A a b.
Proof. exact (EQ_MP (@lem3900157 A a b h1 h2 h3) (@lem3898427 A a b h2)). Qed.
Lemma lem3900159 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term531 A b a) (h2 : @SUBSET A a b) : ((term620 A b a) = b) = (term619 A a b).
Proof. exact (prop_ext (fun h3 : (term620 A b a) = b => @lem3900158 A a b h1 h3 h2) (fun h3 : term619 A a b => @lem3899229 A a b h2)). Qed.
Lemma lem3900160 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term531 A b a) (h2 : @SUBSET A a b) : term619 A a b.
Proof. exact (EQ_MP (@lem3900159 A a b h1 h2) (@lem3899229 A a b h2)). Qed.
Lemma lem3900161 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (term573 A b a) = (@EMPTY A)) (h4 : (@CARD A a) = (@CARD A b)) (h5 : @SUBSET A a b) : term618 A a b.
Proof. exact (EQ_MP (@lem3898426 A a b h1 h2 h3 h4) (@lem3900160 A a b h2 h5)). Qed.
Lemma lem3900162 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (term573 A b a) = (@EMPTY A)) (h4 : (@CARD A a) = (@CARD A b)) (h5 : @SUBSET A a b) : ((term573 A b a) = (@EMPTY A)) = (term618 A a b).
Proof. exact (prop_ext (fun h6 : (term573 A b a) = (@EMPTY A) => @lem3900161 A a b h1 h2 h3 h4 h5) (fun h6 : term618 A a b => @lem3898040 A b a h3)). Qed.
Lemma lem3900163 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (term573 A b a) = (@EMPTY A)) (h4 : (@CARD A a) = (@CARD A b)) (h5 : @SUBSET A a b) : term618 A a b.
Proof. exact (EQ_MP (@lem3900162 A a b h1 h2 h3 h4 h5) (@lem3898040 A b a h3)). Qed.
Lemma lem3900164 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (@CARD A a) = (@CARD A b)) (h4 : @SUBSET A a b) : ((term573 A b a) = (@EMPTY A)) = (term618 A a b).
Proof. exact (prop_ext (fun h5 : (term573 A b a) = (@EMPTY A) => @lem3900163 A a b h1 h2 h5 h3 h4) (fun h5 : term618 A a b => @lem3898347 A b a)). Qed.
Lemma lem3900165 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (@CARD A a) = (@CARD A b)) (h4 : @SUBSET A a b) : term618 A a b.
Proof. exact (EQ_MP (@lem3900164 A a b h1 h2 h3 h4) (@lem3898347 A b a)). Qed.
Lemma lem3900166 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (@CARD A a) = (@CARD A b)) (h4 : @SUBSET A a b) : (term531 A b a) = (term618 A a b).
Proof. exact (prop_ext (fun h5 : term531 A b a => @lem3900165 A a b h1 h2 h3 h4) (fun h5 : term618 A a b => @lem3897716 A b a h2)). Qed.
Lemma lem3900167 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : term531 A b a) (h3 : (@CARD A a) = (@CARD A b)) (h4 : @SUBSET A a b) : term618 A a b.
Proof. exact (EQ_MP (@lem3900166 A a b h1 h2 h3 h4) (@lem3897716 A b a h2)). Qed.
Lemma lem3900168 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : @FINITE A b) (h3 : (@CARD A a) = (@CARD A b)) (h4 : @SUBSET A a b) : (term531 A b a) = (term618 A a b).
Proof. exact (prop_ext (fun h5 : term531 A b a => @lem3900167 A a b h1 h5 h3 h4) (fun h5 : term618 A a b => @lem3898039 A a b h2)). Qed.
Lemma lem3900169 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : @FINITE A b) (h3 : (@CARD A a) = (@CARD A b)) (h4 : @SUBSET A a b) : term618 A a b.
Proof. exact (EQ_MP (@lem3900168 A a b h1 h2 h3 h4) (@lem3898039 A a b h2)). Qed.
Lemma lem3900170 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : @FINITE A b) (h3 : (@CARD A a) = (@CARD A b)) (h4 : @SUBSET A a b) : (@FINITE A a) = (term618 A a b).
Proof. exact (prop_ext (fun h5 : @FINITE A a => @lem3900169 A a b h1 h2 h3 h4) (fun h5 : term618 A a b => @lem3896974 A a h1)). Qed.
Lemma lem3900171 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A a) (h2 : @FINITE A b) (h3 : (@CARD A a) = (@CARD A b)) (h4 : @SUBSET A a b) : term618 A a b.
Proof. exact (EQ_MP (@lem3900170 A a b h1 h2 h3 h4) (@lem3896974 A a h1)). Qed.
Lemma lem3900172 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : (@CARD A a) = (@CARD A b)) (h3 : @SUBSET A a b) : (@FINITE A a) = (term618 A a b).
Proof. exact (prop_ext (fun h4 : @FINITE A a => @lem3900171 A a b h4 h1 h2 h3) (fun h4 : term618 A a b => @lem3897715 A a b h1 h2 h3)). Qed.
Lemma lem3900173 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : (@CARD A a) = (@CARD A b)) (h3 : @SUBSET A a b) : term618 A a b.
Proof. exact (EQ_MP (@lem3900172 A a b h1 h2 h3) (@lem3897715 A a b h1 h2 h3)). Qed.
Lemma lem3900174 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : (@CARD A a) = (@CARD A b)) (h3 : @SUBSET A a b) : a = b.
Proof. exact (@lem3900173 A a b h1 h2 h3 (@lem3896968 A b a)). Qed.
Lemma lem3900175 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term436 A a b) : term437 A a b.
Proof. exact (proj2 (@lem3896969 A a b h1)). Qed.
Lemma lem3900176 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term436 A a b) : @FINITE A b.
Proof. exact (proj1 (@lem3896969 A a b h1)). Qed.
Lemma lem3900177 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term437 A a b) : (@CARD A a) = (@CARD A b).
Proof. exact (proj2 (@lem3896970 A a b h1)). Qed.
Lemma lem3900178 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term437 A a b) : @SUBSET A a b.
Proof. exact (proj1 (@lem3896970 A a b h1)). Qed.
Lemma lem3900179 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : (@CARD A a) = (@CARD A b)) (h3 : @SUBSET A a b) : ((@CARD A a) = (@CARD A b)) = (a = b).
Proof. exact (prop_ext (fun h4 : (@CARD A a) = (@CARD A b) => @lem3900174 A a b h1 h2 h3) (fun h4 : a = b => @lem3896972 A a b h2)). Qed.
Lemma lem3900180 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : (@CARD A a) = (@CARD A b)) (h3 : @SUBSET A a b) : a = b.
Proof. exact (EQ_MP (@lem3900179 A a b h1 h2 h3) (@lem3896972 A a b h2)). Qed.
Lemma lem3900181 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : (@CARD A a) = (@CARD A b)) (h3 : @SUBSET A a b) : (@SUBSET A a b) = (a = b).
Proof. exact (prop_ext (fun h4 : @SUBSET A a b => @lem3900180 A a b h1 h2 h3) (fun h4 : a = b => @lem3896973 A a b h3)). Qed.
Lemma lem3900182 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : (@CARD A a) = (@CARD A b)) (h3 : @SUBSET A a b) : a = b.
Proof. exact (EQ_MP (@lem3900181 A a b h1 h2 h3) (@lem3896973 A a b h3)). Qed.
Lemma lem3900183 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term437 A a b) (h3 : @SUBSET A a b) : ((@CARD A a) = (@CARD A b)) = (a = b).
Proof. exact (prop_ext (fun h4 : (@CARD A a) = (@CARD A b) => @lem3900182 A a b h1 h4 h3) (fun h4 : a = b => @lem3900177 A a b h2)). Qed.
Lemma lem3900184 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term437 A a b) (h3 : @SUBSET A a b) : a = b.
Proof. exact (EQ_MP (@lem3900183 A a b h1 h2 h3) (@lem3900177 A a b h2)). Qed.
Lemma lem3900185 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term437 A a b) : (@SUBSET A a b) = (a = b).
Proof. exact (prop_ext (fun h3 : @SUBSET A a b => @lem3900184 A a b h1 h2 h3) (fun h3 : a = b => @lem3900178 A a b h2)). Qed.
Lemma lem3900186 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term437 A a b) : a = b.
Proof. exact (EQ_MP (@lem3900185 A a b h1 h2) (@lem3900178 A a b h2)). Qed.
Lemma lem3900187 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term437 A a b) : (@FINITE A b) = (a = b).
Proof. exact (prop_ext (fun h3 : @FINITE A b => @lem3900186 A a b h1 h2) (fun h3 : a = b => @lem3896971 A b h1)). Qed.
Lemma lem3900188 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term437 A a b) : a = b.
Proof. exact (EQ_MP (@lem3900187 A a b h1 h2) (@lem3896971 A b h1)). Qed.
Lemma lem3900189 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term436 A a b) : (term437 A a b) = (a = b).
Proof. exact (prop_ext (fun h3 : term437 A a b => @lem3900188 A a b h1 h3) (fun h3 : a = b => @lem3900175 A a b h2)). Qed.
Lemma lem3900190 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term436 A a b) : a = b.
Proof. exact (EQ_MP (@lem3900189 A a b h1 h2) (@lem3900175 A a b h2)). Qed.
Lemma lem3900191 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term436 A a b) : (@FINITE A b) = (a = b).
Proof. exact (prop_ext (fun h2 : @FINITE A b => @lem3900190 A a b h2 h1) (fun h2 : a = b => @lem3900176 A a b h1)). Qed.
Lemma lem3900192 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term436 A a b) : a = b.
Proof. exact (EQ_MP (@lem3900191 A a b h1) (@lem3900176 A a b h1)). Qed.
Lemma lem3900193 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term742 A a b.
Proof. exact (fun h0 : term436 A a b => @lem3900192 A a b h0). Qed.
Lemma lem3900198 {A : Type'} (a : A -> Prop) : term743 A a.
Proof. exact (fun b : A -> Prop => @lem3900193 A a b). Qed.
Lemma lem3900203 {A : Type'} : term744 A.
Proof. exact (fun a : A -> Prop => @lem3900198 A a). Qed.
