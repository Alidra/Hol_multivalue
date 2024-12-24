Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3073366_term_abbrevs.
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
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17646_spec.
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
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm2406442_spec.
Require Import thm2841544_spec.
Require Import thm2841585_spec.
Require Import thm2841586_spec.
Require Import thm2841591_spec.
Require Import thm2841592_spec.
Require Import thm2841615_spec.
Require Import thm2841616_spec.
Require Import thm2841621_spec.
Require Import thm2841622_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem3070996 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (@lem17646 ((int_of_num m) = (int_of_num n)) ((term2 m) = (term2 n))). Qed.
Lemma lem3071002 (x : nat) : (term2 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem3071003 (m : nat) : (term2 m) = (int_of_num m).
Proof. exact (@lem3071002 m). Qed.
Lemma lem3071004 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3071005 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem3071004) (@lem3071003 m)). Qed.
Lemma lem3071007 (x : nat) : (term2 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem3071008 (n : nat) : (term2 n) = (int_of_num n).
Proof. exact (@lem3071007 n). Qed.
Lemma lem3071009 (m : nat) (n : nat) : ((term2 m) = (term2 n)) = ((int_of_num m) = (int_of_num n)).
Proof. exact (MK_COMB (@lem3071005 m) (@lem3071008 n)). Qed.
Lemma lem3071014 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3071015 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (MK_COMB (@lem3071014) (@lem3071009 m n)). Qed.
Lemma lem3071016 (m : nat) (n : nat) : (term7 m n) = (term7 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem3071017 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem3071016 m n) (@lem3071015 m n)). Qed.
Lemma lem3071020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3071021 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem3071020) (@lem3071017 m n)). Qed.
Lemma lem3071027 (x : nat) : (term2 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem3071028 (m : nat) : (term2 m) = (int_of_num m).
Proof. exact (@lem3071027 m). Qed.
Lemma lem3071029 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3071030 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem3071029) (@lem3071028 m)). Qed.
Lemma lem3071032 (x : nat) : (term2 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem3071033 (n : nat) : (term2 n) = (int_of_num n).
Proof. exact (@lem3071032 n). Qed.
Lemma lem3071034 (m : nat) (n : nat) : ((term2 m) = (term2 n)) = ((int_of_num m) = (int_of_num n)).
Proof. exact (MK_COMB (@lem3071030 m) (@lem3071033 n)). Qed.
Lemma lem3071039 (m : nat) (n : nat) : (term12 m n) = (term12 m n).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem3071040 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem3071039 m n) (@lem3071034 m n)). Qed.
Lemma lem3071043 (m : nat) (n : nat) : (term1 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem3071021 m n) (@lem3071040 m n)). Qed.
Lemma lem3071048 (m : nat) (n : nat) : (term0 m n) = (term15 m n).
Proof. exact (TRANS (@lem3070996 m n) (@lem3071043 m n)). Qed.
Lemma lem3071051 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2841622 x y) (@lem2841621 x y)). Qed.
Lemma lem3071052 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = ((term16 m) = (term16 n)).
Proof. exact (@lem3071051 (int_of_num m) (int_of_num n)). Qed.
Lemma lem3071056 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071057 (m : nat) : (term16 m) = (real_of_num m).
Proof. exact (@lem3071056 m). Qed.
Lemma lem3071058 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3071059 (m : nat) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem3071058) (@lem3071057 m)). Qed.
Lemma lem3071061 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071062 (m : nat) (n : nat) : ((term16 m) = (term16 n)) = ((real_of_num m) = (real_of_num n)).
Proof. exact (MK_COMB (@lem3071059 m) (@lem3071061 n)). Qed.
Lemma lem3071064 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = ((real_of_num m) = (real_of_num n)).
Proof. exact (TRANS (@lem3071052 m n) (@lem3071062 m n)). Qed.
Lemma lem3071066 (y : int) (x : int) : (term19 x y) = (term20 y x).
Proof. exact (proj1 (@lem2841544 x y)). Qed.
Lemma lem3071067 (n : nat) (m : nat) : (term6 m n) = (term21 n m).
Proof. exact (@lem3071066 (int_of_num n) (int_of_num m)). Qed.
Lemma lem3071069 (x : int) (y : int) : (int_le x y) = (term22 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3071070 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (@lem3071069 (term25 m) (int_of_num n)). Qed.
Lemma lem3071072 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3071073 (m : nat) : (term28 m) = (term29 m).
Proof. exact (@lem3071072 (int_of_num m) term30). Qed.
Lemma lem3071075 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071076 (m : nat) : (term16 m) = (real_of_num m).
Proof. exact (@lem3071075 m). Qed.
Lemma lem3071077 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3071078 (m : nat) : (term31 m) = (term32 m).
Proof. exact (MK_COMB (@lem3071077) (@lem3071076 m)). Qed.
Lemma lem3071080 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071081 : term33 = term34.
Proof. exact (@lem3071080 term35). Qed.
Lemma lem3071082 (m : nat) : (term29 m) = (term36 m).
Proof. exact (MK_COMB (@lem3071078 m) (@lem3071081)). Qed.
Lemma lem3071083 (m : nat) : (term28 m) = (term36 m).
Proof. exact (TRANS (@lem3071073 m) (@lem3071082 m)). Qed.
Lemma lem3071084 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3071085 (m : nat) : (term37 m) = (term38 m).
Proof. exact (MK_COMB (@lem3071084) (@lem3071083 m)). Qed.
Lemma lem3071087 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071088 (m : nat) (n : nat) : (term24 m n) = (term39 m n).
Proof. exact (MK_COMB (@lem3071085 m) (@lem3071087 n)). Qed.
Lemma lem3071089 (m : nat) (n : nat) : (term23 m n) = (term39 m n).
Proof. exact (TRANS (@lem3071070 m n) (@lem3071088 m n)). Qed.
Lemma lem3071090 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3071091 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (MK_COMB (@lem3071090) (@lem3071089 m n)). Qed.
Lemma lem3071093 (x : int) (y : int) : (int_le x y) = (term22 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3071094 (n : nat) (m : nat) : (term23 n m) = (term24 n m).
Proof. exact (@lem3071093 (term25 n) (int_of_num m)). Qed.
Lemma lem3071096 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3071097 (n : nat) : (term28 n) = (term29 n).
Proof. exact (@lem3071096 (int_of_num n) term30). Qed.
Lemma lem3071099 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071100 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3071101 (n : nat) : (term31 n) = (term32 n).
Proof. exact (MK_COMB (@lem3071100) (@lem3071099 n)). Qed.
Lemma lem3071103 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071104 : term33 = term34.
Proof. exact (@lem3071103 term35). Qed.
Lemma lem3071105 (n : nat) : (term29 n) = (term36 n).
Proof. exact (MK_COMB (@lem3071101 n) (@lem3071104)). Qed.
Lemma lem3071106 (n : nat) : (term28 n) = (term36 n).
Proof. exact (TRANS (@lem3071097 n) (@lem3071105 n)). Qed.
Lemma lem3071107 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3071108 (n : nat) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem3071107) (@lem3071106 n)). Qed.
Lemma lem3071110 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071111 (m : nat) : (term16 m) = (real_of_num m).
Proof. exact (@lem3071110 m). Qed.
Lemma lem3071112 (n : nat) (m : nat) : (term24 n m) = (term39 n m).
Proof. exact (MK_COMB (@lem3071108 n) (@lem3071111 m)). Qed.
Lemma lem3071113 (n : nat) (m : nat) : (term23 n m) = (term39 n m).
Proof. exact (TRANS (@lem3071094 n m) (@lem3071112 n m)). Qed.
Lemma lem3071114 (n : nat) (m : nat) : (term21 n m) = (term42 n m).
Proof. exact (MK_COMB (@lem3071091 m n) (@lem3071113 n m)). Qed.
Lemma lem3071115 (n : nat) (m : nat) : (term6 m n) = (term42 n m).
Proof. exact (TRANS (@lem3071067 n m) (@lem3071114 n m)). Qed.
Lemma lem3071116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3071117 (m : nat) (n : nat) : (term7 m n) = (term43 m n).
Proof. exact (MK_COMB (@lem3071116) (@lem3071064 m n)). Qed.
Lemma lem3071118 (n : nat) (m : nat) : (term9 m n) = (term44 n m).
Proof. exact (MK_COMB (@lem3071117 m n) (@lem3071115 n m)). Qed.
Lemma lem3071120 (y : int) (x : int) : (term19 x y) = (term20 y x).
Proof. exact (proj1 (@lem2841544 x y)). Qed.
Lemma lem3071121 (n : nat) (m : nat) : (term6 m n) = (term21 n m).
Proof. exact (@lem3071120 (int_of_num n) (int_of_num m)). Qed.
Lemma lem3071123 (x : int) (y : int) : (int_le x y) = (term22 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3071124 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (@lem3071123 (term25 m) (int_of_num n)). Qed.
Lemma lem3071126 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3071127 (m : nat) : (term28 m) = (term29 m).
Proof. exact (@lem3071126 (int_of_num m) term30). Qed.
Lemma lem3071129 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071130 (m : nat) : (term16 m) = (real_of_num m).
Proof. exact (@lem3071129 m). Qed.
Lemma lem3071131 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3071132 (m : nat) : (term31 m) = (term32 m).
Proof. exact (MK_COMB (@lem3071131) (@lem3071130 m)). Qed.
Lemma lem3071134 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071135 : term33 = term34.
Proof. exact (@lem3071134 term35). Qed.
Lemma lem3071136 (m : nat) : (term29 m) = (term36 m).
Proof. exact (MK_COMB (@lem3071132 m) (@lem3071135)). Qed.
Lemma lem3071137 (m : nat) : (term28 m) = (term36 m).
Proof. exact (TRANS (@lem3071127 m) (@lem3071136 m)). Qed.
Lemma lem3071138 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3071139 (m : nat) : (term37 m) = (term38 m).
Proof. exact (MK_COMB (@lem3071138) (@lem3071137 m)). Qed.
Lemma lem3071141 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071142 (m : nat) (n : nat) : (term24 m n) = (term39 m n).
Proof. exact (MK_COMB (@lem3071139 m) (@lem3071141 n)). Qed.
Lemma lem3071143 (m : nat) (n : nat) : (term23 m n) = (term39 m n).
Proof. exact (TRANS (@lem3071124 m n) (@lem3071142 m n)). Qed.
Lemma lem3071144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3071145 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (MK_COMB (@lem3071144) (@lem3071143 m n)). Qed.
Lemma lem3071147 (x : int) (y : int) : (int_le x y) = (term22 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem3071148 (n : nat) (m : nat) : (term23 n m) = (term24 n m).
Proof. exact (@lem3071147 (term25 n) (int_of_num m)). Qed.
Lemma lem3071150 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem3071151 (n : nat) : (term28 n) = (term29 n).
Proof. exact (@lem3071150 (int_of_num n) term30). Qed.
Lemma lem3071153 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071154 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3071155 (n : nat) : (term31 n) = (term32 n).
Proof. exact (MK_COMB (@lem3071154) (@lem3071153 n)). Qed.
Lemma lem3071157 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071158 : term33 = term34.
Proof. exact (@lem3071157 term35). Qed.
Lemma lem3071159 (n : nat) : (term29 n) = (term36 n).
Proof. exact (MK_COMB (@lem3071155 n) (@lem3071158)). Qed.
Lemma lem3071160 (n : nat) : (term28 n) = (term36 n).
Proof. exact (TRANS (@lem3071151 n) (@lem3071159 n)). Qed.
Lemma lem3071161 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3071162 (n : nat) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem3071161) (@lem3071160 n)). Qed.
Lemma lem3071164 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071165 (m : nat) : (term16 m) = (real_of_num m).
Proof. exact (@lem3071164 m). Qed.
Lemma lem3071166 (n : nat) (m : nat) : (term24 n m) = (term39 n m).
Proof. exact (MK_COMB (@lem3071162 n) (@lem3071165 m)). Qed.
Lemma lem3071167 (n : nat) (m : nat) : (term23 n m) = (term39 n m).
Proof. exact (TRANS (@lem3071148 n m) (@lem3071166 n m)). Qed.
Lemma lem3071168 (n : nat) (m : nat) : (term21 n m) = (term42 n m).
Proof. exact (MK_COMB (@lem3071145 m n) (@lem3071167 n m)). Qed.
Lemma lem3071169 (n : nat) (m : nat) : (term6 m n) = (term42 n m).
Proof. exact (TRANS (@lem3071121 n m) (@lem3071168 n m)). Qed.
Lemma lem3071172 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2841622 x y) (@lem2841621 x y)). Qed.
Lemma lem3071173 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = ((term16 m) = (term16 n)).
Proof. exact (@lem3071172 (int_of_num m) (int_of_num n)). Qed.
Lemma lem3071177 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071178 (m : nat) : (term16 m) = (real_of_num m).
Proof. exact (@lem3071177 m). Qed.
Lemma lem3071179 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3071180 (m : nat) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem3071179) (@lem3071178 m)). Qed.
Lemma lem3071182 (n : nat) : (term16 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem3071183 (m : nat) (n : nat) : ((term16 m) = (term16 n)) = ((real_of_num m) = (real_of_num n)).
Proof. exact (MK_COMB (@lem3071180 m) (@lem3071182 n)). Qed.
Lemma lem3071185 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = ((real_of_num m) = (real_of_num n)).
Proof. exact (TRANS (@lem3071173 m n) (@lem3071183 m n)). Qed.
Lemma lem3071186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3071187 (n : nat) (m : nat) : (term12 m n) = (term45 n m).
Proof. exact (MK_COMB (@lem3071186) (@lem3071169 n m)). Qed.
Lemma lem3071188 (m : nat) (n : nat) : (term14 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem3071187 n m) (@lem3071185 m n)). Qed.
Lemma lem3071189 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3071190 (n : nat) (m : nat) : (term11 m n) = (term47 n m).
Proof. exact (MK_COMB (@lem3071189) (@lem3071118 n m)). Qed.
Lemma lem3071191 (m : nat) (n : nat) : (term15 m n) = (term48 m n).
Proof. exact (MK_COMB (@lem3071190 n m) (@lem3071188 m n)). Qed.
Lemma lem3071192 (m : nat) (n : nat) : (term0 m n) = (term48 m n).
Proof. exact (TRANS (@lem3071048 m n) (@lem3071191 m n)). Qed.
Lemma lem3071196 (t : Prop) : (term49 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3071252 (m : nat) (n : nat) : (term50 m n) = (term48 m n).
Proof. exact (@lem3071196 (term48 m n)). Qed.
Lemma lem3071253 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = ((term51 m n) = term52).
Proof. exact (@lem1988293 (real_of_num m) (real_of_num n)). Qed.
Lemma lem3071266 (m : nat) (n : nat) : (term51 m n) = (term53 m n).
Proof. exact (@lem1982792 (real_of_num m) (real_of_num n)). Qed.
Lemma lem3071267 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3071268 (m : nat) (n : nat) : (term54 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem3071267) (@lem3071266 m n)). Qed.
Lemma lem3071269 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3071270 (m : nat) (n : nat) : ((term51 m n) = term52) = ((term53 m n) = term52).
Proof. exact (MK_COMB (@lem3071268 m n) (@lem3071269)). Qed.
Lemma lem3071271 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = ((term53 m n) = term52).
Proof. exact (TRANS (@lem3071253 m n) (@lem3071270 m n)). Qed.
Lemma lem3071272 (n : nat) (m : nat) : (term39 m n) = (term56 n m).
Proof. exact (@lem1988287 (real_of_num n) (term36 m)). Qed.
Lemma lem3071284 (n : nat) (m : nat) : (term57 n m) = (term58 n m).
Proof. exact (@lem1982792 (real_of_num n) (term36 m)). Qed.
Lemma lem3071285 (m : nat) : (term59 m) = (term60 m).
Proof. exact (@lem1982781 (real_of_num m) term61 term34). Qed.
Lemma lem3071287 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3071288 : term34 = term63.
Proof. exact (@lem3071287 term35). Qed.
Lemma lem3071290 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3071291 : term61 = term66.
Proof. exact (@lem3071290 term35). Qed.
Lemma lem3071292 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3071293 : term67 = term68.
Proof. exact (MK_COMB (@lem3071292) (@lem3071291)). Qed.
Lemma lem3071294 : term69 = term70.
Proof. exact (MK_COMB (@lem3071293) (@lem3071288)). Qed.
Lemma lem3071295 : term70 = term71.
Proof. exact (@lem1981613 term61 term34 term34 term34). Qed.
Lemma lem3071297 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3071298 : term74 = term75.
Proof. exact (@lem3071297 term35 term35). Qed.
Lemma lem3071299 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071300 : term77 = term35.
Proof. exact (EQ_MP (@lem3071299) (@lem940073)). Qed.
Lemma lem3071301 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071302 : term75 = term34.
Proof. exact (MK_COMB (@lem3071301) (@lem3071300)). Qed.
Lemma lem3071303 : term74 = term34.
Proof. exact (TRANS (@lem3071298) (@lem3071302)). Qed.
Lemma lem3071305 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3071306 : term69 = term80.
Proof. exact (@lem3071305 term35 term35). Qed.
Lemma lem3071307 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071308 : term77 = term35.
Proof. exact (EQ_MP (@lem3071307) (@lem940073)). Qed.
Lemma lem3071309 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071310 : term75 = term34.
Proof. exact (MK_COMB (@lem3071309) (@lem3071308)). Qed.
Lemma lem3071311 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3071312 : term80 = term61.
Proof. exact (MK_COMB (@lem3071311) (@lem3071310)). Qed.
Lemma lem3071313 : term69 = term61.
Proof. exact (TRANS (@lem3071306) (@lem3071312)). Qed.
Lemma lem3071314 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3071315 : term81 = term82.
Proof. exact (MK_COMB (@lem3071314) (@lem3071313)). Qed.
Lemma lem3071316 : term71 = term66.
Proof. exact (MK_COMB (@lem3071315) (@lem3071303)). Qed.
Lemma lem3071317 : term70 = term66.
Proof. exact (TRANS (@lem3071295) (@lem3071316)). Qed.
Lemma lem3071318 : term69 = term66.
Proof. exact (TRANS (@lem3071294) (@lem3071317)). Qed.
Lemma lem3071320 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3071321 : term66 = term61.
Proof. exact (@lem3071320 term61). Qed.
Lemma lem3071322 : term69 = term61.
Proof. exact (TRANS (@lem3071318) (@lem3071321)). Qed.
Lemma lem3071325 (m : nat) : (term84 m) = (term84 m).
Proof. exact (eq_refl (term84 m)). Qed.
Lemma lem3071326 (m : nat) : (term60 m) = (term85 m).
Proof. exact (MK_COMB (@lem3071325 m) (@lem3071322)). Qed.
Lemma lem3071327 (m : nat) : (term59 m) = (term85 m).
Proof. exact (TRANS (@lem3071285 m) (@lem3071326 m)). Qed.
Lemma lem3071328 (n : nat) : (term32 n) = (term32 n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem3071329 (n : nat) (m : nat) : (term58 n m) = (term86 n m).
Proof. exact (MK_COMB (@lem3071328 n) (@lem3071327 m)). Qed.
Lemma lem3071334 (m : nat) (n : nat) : (term86 n m) = (term87 m n).
Proof. exact (@lem1982757 (term88 m) (real_of_num n) term61). Qed.
Lemma lem3071335 (m : nat) (n : nat) : (term58 n m) = (term87 m n).
Proof. exact (TRANS (@lem3071329 n m) (@lem3071334 m n)). Qed.
Lemma lem3071337 (m : nat) (n : nat) : (term57 n m) = (term87 m n).
Proof. exact (TRANS (@lem3071284 n m) (@lem3071335 m n)). Qed.
Lemma lem3071338 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3071339 (m : nat) (n : nat) : (term89 n m) = (term90 m n).
Proof. exact (MK_COMB (@lem3071338) (@lem3071337 m n)). Qed.
Lemma lem3071340 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3071341 (m : nat) (n : nat) : (term56 n m) = (term91 m n).
Proof. exact (MK_COMB (@lem3071339 m n) (@lem3071340)). Qed.
Lemma lem3071342 (m : nat) (n : nat) : (term39 m n) = (term91 m n).
Proof. exact (TRANS (@lem3071272 n m) (@lem3071341 m n)). Qed.
Lemma lem3071343 (m : nat) (n : nat) : (term39 n m) = (term56 m n).
Proof. exact (@lem1988287 (real_of_num m) (term36 n)). Qed.
Lemma lem3071355 (m : nat) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (@lem1982792 (real_of_num m) (term36 n)). Qed.
Lemma lem3071356 (n : nat) : (term59 n) = (term60 n).
Proof. exact (@lem1982781 (real_of_num n) term61 term34). Qed.
Lemma lem3071358 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3071359 : term34 = term63.
Proof. exact (@lem3071358 term35). Qed.
Lemma lem3071361 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3071362 : term61 = term66.
Proof. exact (@lem3071361 term35). Qed.
Lemma lem3071363 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3071364 : term67 = term68.
Proof. exact (MK_COMB (@lem3071363) (@lem3071362)). Qed.
Lemma lem3071365 : term69 = term70.
Proof. exact (MK_COMB (@lem3071364) (@lem3071359)). Qed.
Lemma lem3071366 : term70 = term71.
Proof. exact (@lem1981613 term61 term34 term34 term34). Qed.
Lemma lem3071368 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3071369 : term74 = term75.
Proof. exact (@lem3071368 term35 term35). Qed.
Lemma lem3071370 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071371 : term77 = term35.
Proof. exact (EQ_MP (@lem3071370) (@lem940073)). Qed.
Lemma lem3071372 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071373 : term75 = term34.
Proof. exact (MK_COMB (@lem3071372) (@lem3071371)). Qed.
Lemma lem3071374 : term74 = term34.
Proof. exact (TRANS (@lem3071369) (@lem3071373)). Qed.
Lemma lem3071376 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3071377 : term69 = term80.
Proof. exact (@lem3071376 term35 term35). Qed.
Lemma lem3071378 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071379 : term77 = term35.
Proof. exact (EQ_MP (@lem3071378) (@lem940073)). Qed.
Lemma lem3071380 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071381 : term75 = term34.
Proof. exact (MK_COMB (@lem3071380) (@lem3071379)). Qed.
Lemma lem3071382 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3071383 : term80 = term61.
Proof. exact (MK_COMB (@lem3071382) (@lem3071381)). Qed.
Lemma lem3071384 : term69 = term61.
Proof. exact (TRANS (@lem3071377) (@lem3071383)). Qed.
Lemma lem3071385 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3071386 : term81 = term82.
Proof. exact (MK_COMB (@lem3071385) (@lem3071384)). Qed.
Lemma lem3071387 : term71 = term66.
Proof. exact (MK_COMB (@lem3071386) (@lem3071374)). Qed.
Lemma lem3071388 : term70 = term66.
Proof. exact (TRANS (@lem3071366) (@lem3071387)). Qed.
Lemma lem3071389 : term69 = term66.
Proof. exact (TRANS (@lem3071365) (@lem3071388)). Qed.
Lemma lem3071391 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3071392 : term66 = term61.
Proof. exact (@lem3071391 term61). Qed.
Lemma lem3071393 : term69 = term61.
Proof. exact (TRANS (@lem3071389) (@lem3071392)). Qed.
Lemma lem3071396 (n : nat) : (term84 n) = (term84 n).
Proof. exact (eq_refl (term84 n)). Qed.
Lemma lem3071397 (n : nat) : (term60 n) = (term85 n).
Proof. exact (MK_COMB (@lem3071396 n) (@lem3071393)). Qed.
Lemma lem3071398 (n : nat) : (term59 n) = (term85 n).
Proof. exact (TRANS (@lem3071356 n) (@lem3071397 n)). Qed.
Lemma lem3071399 (m : nat) : (term32 m) = (term32 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem3071402 (m : nat) (n : nat) : (term58 m n) = (term86 m n).
Proof. exact (MK_COMB (@lem3071399 m) (@lem3071398 n)). Qed.
Lemma lem3071404 (m : nat) (n : nat) : (term57 m n) = (term86 m n).
Proof. exact (TRANS (@lem3071355 m n) (@lem3071402 m n)). Qed.
Lemma lem3071405 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3071406 (m : nat) (n : nat) : (term89 m n) = (term92 m n).
Proof. exact (MK_COMB (@lem3071405) (@lem3071404 m n)). Qed.
Lemma lem3071407 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3071408 (m : nat) (n : nat) : (term56 m n) = (term93 m n).
Proof. exact (MK_COMB (@lem3071406 m n) (@lem3071407)). Qed.
Lemma lem3071409 (m : nat) (n : nat) : (term39 n m) = (term93 m n).
Proof. exact (TRANS (@lem3071343 m n) (@lem3071408 m n)). Qed.
Lemma lem3071410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3071411 (m : nat) (n : nat) : (term41 m n) = (term94 m n).
Proof. exact (MK_COMB (@lem3071410) (@lem3071342 m n)). Qed.
Lemma lem3071412 (m : nat) (n : nat) : (term42 n m) = (term95 m n).
Proof. exact (MK_COMB (@lem3071411 m n) (@lem3071409 m n)). Qed.
Lemma lem3071413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3071414 (m : nat) (n : nat) : (term43 m n) = (term96 m n).
Proof. exact (MK_COMB (@lem3071413) (@lem3071271 m n)). Qed.
Lemma lem3071415 (m : nat) (n : nat) : (term44 n m) = (term97 m n).
Proof. exact (MK_COMB (@lem3071414 m n) (@lem3071412 m n)). Qed.
Lemma lem3071416 (n : nat) (m : nat) : (term39 m n) = (term56 n m).
Proof. exact (@lem1988287 (real_of_num n) (term36 m)). Qed.
Lemma lem3071428 (n : nat) (m : nat) : (term57 n m) = (term58 n m).
Proof. exact (@lem1982792 (real_of_num n) (term36 m)). Qed.
Lemma lem3071429 (m : nat) : (term59 m) = (term60 m).
Proof. exact (@lem1982781 (real_of_num m) term61 term34). Qed.
Lemma lem3071431 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3071432 : term34 = term63.
Proof. exact (@lem3071431 term35). Qed.
Lemma lem3071434 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3071435 : term61 = term66.
Proof. exact (@lem3071434 term35). Qed.
Lemma lem3071436 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3071437 : term67 = term68.
Proof. exact (MK_COMB (@lem3071436) (@lem3071435)). Qed.
Lemma lem3071438 : term69 = term70.
Proof. exact (MK_COMB (@lem3071437) (@lem3071432)). Qed.
Lemma lem3071439 : term70 = term71.
Proof. exact (@lem1981613 term61 term34 term34 term34). Qed.
Lemma lem3071441 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3071442 : term74 = term75.
Proof. exact (@lem3071441 term35 term35). Qed.
Lemma lem3071443 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071444 : term77 = term35.
Proof. exact (EQ_MP (@lem3071443) (@lem940073)). Qed.
Lemma lem3071445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071446 : term75 = term34.
Proof. exact (MK_COMB (@lem3071445) (@lem3071444)). Qed.
Lemma lem3071447 : term74 = term34.
Proof. exact (TRANS (@lem3071442) (@lem3071446)). Qed.
Lemma lem3071449 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3071450 : term69 = term80.
Proof. exact (@lem3071449 term35 term35). Qed.
Lemma lem3071451 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071452 : term77 = term35.
Proof. exact (EQ_MP (@lem3071451) (@lem940073)). Qed.
Lemma lem3071453 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071454 : term75 = term34.
Proof. exact (MK_COMB (@lem3071453) (@lem3071452)). Qed.
Lemma lem3071455 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3071456 : term80 = term61.
Proof. exact (MK_COMB (@lem3071455) (@lem3071454)). Qed.
Lemma lem3071457 : term69 = term61.
Proof. exact (TRANS (@lem3071450) (@lem3071456)). Qed.
Lemma lem3071458 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3071459 : term81 = term82.
Proof. exact (MK_COMB (@lem3071458) (@lem3071457)). Qed.
Lemma lem3071460 : term71 = term66.
Proof. exact (MK_COMB (@lem3071459) (@lem3071447)). Qed.
Lemma lem3071461 : term70 = term66.
Proof. exact (TRANS (@lem3071439) (@lem3071460)). Qed.
Lemma lem3071462 : term69 = term66.
Proof. exact (TRANS (@lem3071438) (@lem3071461)). Qed.
Lemma lem3071464 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3071465 : term66 = term61.
Proof. exact (@lem3071464 term61). Qed.
Lemma lem3071466 : term69 = term61.
Proof. exact (TRANS (@lem3071462) (@lem3071465)). Qed.
Lemma lem3071469 (m : nat) : (term84 m) = (term84 m).
Proof. exact (eq_refl (term84 m)). Qed.
Lemma lem3071470 (m : nat) : (term60 m) = (term85 m).
Proof. exact (MK_COMB (@lem3071469 m) (@lem3071466)). Qed.
Lemma lem3071471 (m : nat) : (term59 m) = (term85 m).
Proof. exact (TRANS (@lem3071429 m) (@lem3071470 m)). Qed.
Lemma lem3071472 (n : nat) : (term32 n) = (term32 n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem3071473 (n : nat) (m : nat) : (term58 n m) = (term86 n m).
Proof. exact (MK_COMB (@lem3071472 n) (@lem3071471 m)). Qed.
Lemma lem3071478 (m : nat) (n : nat) : (term86 n m) = (term87 m n).
Proof. exact (@lem1982757 (term88 m) (real_of_num n) term61). Qed.
Lemma lem3071479 (m : nat) (n : nat) : (term58 n m) = (term87 m n).
Proof. exact (TRANS (@lem3071473 n m) (@lem3071478 m n)). Qed.
Lemma lem3071481 (m : nat) (n : nat) : (term57 n m) = (term87 m n).
Proof. exact (TRANS (@lem3071428 n m) (@lem3071479 m n)). Qed.
Lemma lem3071482 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3071483 (m : nat) (n : nat) : (term89 n m) = (term90 m n).
Proof. exact (MK_COMB (@lem3071482) (@lem3071481 m n)). Qed.
Lemma lem3071484 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3071485 (m : nat) (n : nat) : (term56 n m) = (term91 m n).
Proof. exact (MK_COMB (@lem3071483 m n) (@lem3071484)). Qed.
Lemma lem3071486 (m : nat) (n : nat) : (term39 m n) = (term91 m n).
Proof. exact (TRANS (@lem3071416 n m) (@lem3071485 m n)). Qed.
Lemma lem3071487 (m : nat) (n : nat) : (term39 n m) = (term56 m n).
Proof. exact (@lem1988287 (real_of_num m) (term36 n)). Qed.
Lemma lem3071499 (m : nat) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (@lem1982792 (real_of_num m) (term36 n)). Qed.
Lemma lem3071500 (n : nat) : (term59 n) = (term60 n).
Proof. exact (@lem1982781 (real_of_num n) term61 term34). Qed.
Lemma lem3071502 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3071503 : term34 = term63.
Proof. exact (@lem3071502 term35). Qed.
Lemma lem3071505 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3071506 : term61 = term66.
Proof. exact (@lem3071505 term35). Qed.
Lemma lem3071507 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3071508 : term67 = term68.
Proof. exact (MK_COMB (@lem3071507) (@lem3071506)). Qed.
Lemma lem3071509 : term69 = term70.
Proof. exact (MK_COMB (@lem3071508) (@lem3071503)). Qed.
Lemma lem3071510 : term70 = term71.
Proof. exact (@lem1981613 term61 term34 term34 term34). Qed.
Lemma lem3071512 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3071513 : term74 = term75.
Proof. exact (@lem3071512 term35 term35). Qed.
Lemma lem3071514 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071515 : term77 = term35.
Proof. exact (EQ_MP (@lem3071514) (@lem940073)). Qed.
Lemma lem3071516 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071517 : term75 = term34.
Proof. exact (MK_COMB (@lem3071516) (@lem3071515)). Qed.
Lemma lem3071518 : term74 = term34.
Proof. exact (TRANS (@lem3071513) (@lem3071517)). Qed.
Lemma lem3071520 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3071521 : term69 = term80.
Proof. exact (@lem3071520 term35 term35). Qed.
Lemma lem3071522 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071523 : term77 = term35.
Proof. exact (EQ_MP (@lem3071522) (@lem940073)). Qed.
Lemma lem3071524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071525 : term75 = term34.
Proof. exact (MK_COMB (@lem3071524) (@lem3071523)). Qed.
Lemma lem3071526 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3071527 : term80 = term61.
Proof. exact (MK_COMB (@lem3071526) (@lem3071525)). Qed.
Lemma lem3071528 : term69 = term61.
Proof. exact (TRANS (@lem3071521) (@lem3071527)). Qed.
Lemma lem3071529 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3071530 : term81 = term82.
Proof. exact (MK_COMB (@lem3071529) (@lem3071528)). Qed.
Lemma lem3071531 : term71 = term66.
Proof. exact (MK_COMB (@lem3071530) (@lem3071518)). Qed.
Lemma lem3071532 : term70 = term66.
Proof. exact (TRANS (@lem3071510) (@lem3071531)). Qed.
Lemma lem3071533 : term69 = term66.
Proof. exact (TRANS (@lem3071509) (@lem3071532)). Qed.
Lemma lem3071535 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3071536 : term66 = term61.
Proof. exact (@lem3071535 term61). Qed.
Lemma lem3071537 : term69 = term61.
Proof. exact (TRANS (@lem3071533) (@lem3071536)). Qed.
Lemma lem3071540 (n : nat) : (term84 n) = (term84 n).
Proof. exact (eq_refl (term84 n)). Qed.
Lemma lem3071541 (n : nat) : (term60 n) = (term85 n).
Proof. exact (MK_COMB (@lem3071540 n) (@lem3071537)). Qed.
Lemma lem3071542 (n : nat) : (term59 n) = (term85 n).
Proof. exact (TRANS (@lem3071500 n) (@lem3071541 n)). Qed.
Lemma lem3071543 (m : nat) : (term32 m) = (term32 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem3071546 (m : nat) (n : nat) : (term58 m n) = (term86 m n).
Proof. exact (MK_COMB (@lem3071543 m) (@lem3071542 n)). Qed.
Lemma lem3071548 (m : nat) (n : nat) : (term57 m n) = (term86 m n).
Proof. exact (TRANS (@lem3071499 m n) (@lem3071546 m n)). Qed.
Lemma lem3071549 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3071550 (m : nat) (n : nat) : (term89 m n) = (term92 m n).
Proof. exact (MK_COMB (@lem3071549) (@lem3071548 m n)). Qed.
Lemma lem3071551 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3071552 (m : nat) (n : nat) : (term56 m n) = (term93 m n).
Proof. exact (MK_COMB (@lem3071550 m n) (@lem3071551)). Qed.
Lemma lem3071553 (m : nat) (n : nat) : (term39 n m) = (term93 m n).
Proof. exact (TRANS (@lem3071487 m n) (@lem3071552 m n)). Qed.
Lemma lem3071554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3071555 (m : nat) (n : nat) : (term41 m n) = (term94 m n).
Proof. exact (MK_COMB (@lem3071554) (@lem3071486 m n)). Qed.
Lemma lem3071556 (m : nat) (n : nat) : (term42 n m) = (term95 m n).
Proof. exact (MK_COMB (@lem3071555 m n) (@lem3071553 m n)). Qed.
Lemma lem3071557 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = ((term51 m n) = term52).
Proof. exact (@lem1988293 (real_of_num m) (real_of_num n)). Qed.
Lemma lem3071570 (m : nat) (n : nat) : (term51 m n) = (term53 m n).
Proof. exact (@lem1982792 (real_of_num m) (real_of_num n)). Qed.
Lemma lem3071571 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3071572 (m : nat) (n : nat) : (term54 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem3071571) (@lem3071570 m n)). Qed.
Lemma lem3071573 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3071574 (m : nat) (n : nat) : ((term51 m n) = term52) = ((term53 m n) = term52).
Proof. exact (MK_COMB (@lem3071572 m n) (@lem3071573)). Qed.
Lemma lem3071575 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = ((term53 m n) = term52).
Proof. exact (TRANS (@lem3071557 m n) (@lem3071574 m n)). Qed.
Lemma lem3071576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3071577 (m : nat) (n : nat) : (term45 n m) = (term98 m n).
Proof. exact (MK_COMB (@lem3071576) (@lem3071556 m n)). Qed.
Lemma lem3071578 (m : nat) (n : nat) : (term46 m n) = (term99 m n).
Proof. exact (MK_COMB (@lem3071577 m n) (@lem3071575 m n)). Qed.
Lemma lem3071579 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3071580 (m : nat) (n : nat) : (term47 n m) = (term100 m n).
Proof. exact (MK_COMB (@lem3071579) (@lem3071415 m n)). Qed.
Lemma lem3071581 (m : nat) (n : nat) : (term48 m n) = (term101 m n).
Proof. exact (MK_COMB (@lem3071580 m n) (@lem3071578 m n)). Qed.
Lemma lem3071588 (m : nat) (n : nat) : (term50 m n) = (term101 m n).
Proof. exact (TRANS (@lem3071252 m n) (@lem3071581 m n)). Qed.
Lemma lem3071605 (m : nat) (n : nat) : (term99 m n) = (term102 m n).
Proof. exact (@lem19367 (term91 m n) (term93 m n) ((term53 m n) = term52)). Qed.
Lemma lem3071622 (m : nat) (n : nat) : (term97 m n) = (term103 m n).
Proof. exact (@lem19158 (term91 m n) ((term53 m n) = term52) (term93 m n)). Qed.
Lemma lem3071623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3071624 (m : nat) (n : nat) : (term100 m n) = (term104 m n).
Proof. exact (MK_COMB (@lem3071623) (@lem3071622 m n)). Qed.
Lemma lem3071625 (m : nat) (n : nat) : (term101 m n) = (term105 m n).
Proof. exact (MK_COMB (@lem3071624 m n) (@lem3071605 m n)). Qed.
Lemma lem3071626 (m : nat) (n : nat) : (term50 m n) = (term105 m n).
Proof. exact (TRANS (@lem3071588 m n) (@lem3071625 m n)). Qed.
Lemma lem3071648 (m : nat) (n : nat) (h1 : term105 m n) : term105 m n.
Proof. exact (h1). Qed.
Lemma lem3071649 (m : nat) (n : nat) (h1 : term103 m n) : term103 m n.
Proof. exact (h1). Qed.
Lemma lem3071650 (m : nat) (n : nat) (h1 : term106 m n) : term106 m n.
Proof. exact (h1). Qed.
Lemma lem3071651 (m : nat) (n : nat) (h1 : term106 m n) : term91 m n.
Proof. exact (proj2 (@lem3071650 m n h1)). Qed.
Lemma lem3071652 (m : nat) (n : nat) (h1 : term106 m n) : (term53 m n) = term52.
Proof. exact (proj1 (@lem3071650 m n h1)). Qed.
Lemma lem3071656 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3071657 : term107 = term108.
Proof. exact (@lem3071656 term52 term34). Qed.
Lemma lem3071659 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3071660 : term34 = term63.
Proof. exact (@lem3071659 term35). Qed.
Lemma lem3071662 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3071663 : term52 = term109.
Proof. exact (@lem3071662 (NUMERAL 0)). Qed.
Lemma lem3071664 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3071665 : term110 = term111.
Proof. exact (MK_COMB (@lem3071664) (@lem3071663)). Qed.
Lemma lem3071666 : term108 = term112.
Proof. exact (MK_COMB (@lem3071665) (@lem3071660)). Qed.
Lemma lem3071667 : term113.
Proof. exact (@lem1980255 term52 term34 term34 term34). Qed.
Lemma lem3071669 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3071670 : term108 = term115.
Proof. exact (@lem3071669 (NUMERAL 0) term35). Qed.
Lemma lem3071671 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3071672 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3071673 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3071672 h1) (fun h1 : term115 = True => @lem3071671)). Qed.
Lemma lem3071674 : term115 = True.
Proof. exact (EQ_MP (@lem3071673) (@lem3071671)). Qed.
Lemma lem3071675 : term108 = True.
Proof. exact (TRANS (@lem3071670) (@lem3071674)). Qed.
Lemma lem3071676 : True = term108.
Proof. exact (SYM (@lem3071675)). Qed.
Lemma lem3071677 : term108.
Proof. exact (EQ_MP (@lem3071676) (@lem0)). Qed.
Lemma lem3071678 : term117.
Proof. exact (@lem3071667 (@lem3071677)). Qed.
Lemma lem3071680 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3071681 : term108 = term115.
Proof. exact (@lem3071680 (NUMERAL 0) term35). Qed.
Lemma lem3071682 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3071683 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3071684 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3071683 h1) (fun h1 : term115 = True => @lem3071682)). Qed.
Lemma lem3071685 : term115 = True.
Proof. exact (EQ_MP (@lem3071684) (@lem3071682)). Qed.
Lemma lem3071686 : term108 = True.
Proof. exact (TRANS (@lem3071681) (@lem3071685)). Qed.
Lemma lem3071687 : True = term108.
Proof. exact (SYM (@lem3071686)). Qed.
Lemma lem3071688 : term108.
Proof. exact (EQ_MP (@lem3071687) (@lem0)). Qed.
Lemma lem3071689 : term112 = term118.
Proof. exact (@lem3071678 (@lem3071688)). Qed.
Lemma lem3071691 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3071692 : term74 = term75.
Proof. exact (@lem3071691 term35 term35). Qed.
Lemma lem3071693 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071694 : term77 = term35.
Proof. exact (EQ_MP (@lem3071693) (@lem940073)). Qed.
Lemma lem3071695 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071696 : term75 = term34.
Proof. exact (MK_COMB (@lem3071695) (@lem3071694)). Qed.
Lemma lem3071697 : term74 = term34.
Proof. exact (TRANS (@lem3071692) (@lem3071696)). Qed.
Lemma lem3071699 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3071700 : term120 = term52.
Proof. exact (@lem3071699 term35). Qed.
Lemma lem3071701 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3071702 : term121 = term110.
Proof. exact (MK_COMB (@lem3071701) (@lem3071700)). Qed.
Lemma lem3071703 : term118 = term108.
Proof. exact (MK_COMB (@lem3071702) (@lem3071697)). Qed.
Lemma lem3071705 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3071706 : term108 = term115.
Proof. exact (@lem3071705 (NUMERAL 0) term35). Qed.
Lemma lem3071707 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3071708 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3071709 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3071708 h1) (fun h1 : term115 = True => @lem3071707)). Qed.
Lemma lem3071710 : term115 = True.
Proof. exact (EQ_MP (@lem3071709) (@lem3071707)). Qed.
Lemma lem3071711 : term108 = True.
Proof. exact (TRANS (@lem3071706) (@lem3071710)). Qed.
Lemma lem3071712 : term118 = True.
Proof. exact (TRANS (@lem3071703) (@lem3071711)). Qed.
Lemma lem3071713 : term112 = True.
Proof. exact (TRANS (@lem3071689) (@lem3071712)). Qed.
Lemma lem3071714 : term108 = True.
Proof. exact (TRANS (@lem3071666) (@lem3071713)). Qed.
Lemma lem3071715 : term107 = True.
Proof. exact (TRANS (@lem3071657) (@lem3071714)). Qed.
Lemma lem3071716 : True = term107.
Proof. exact (SYM (@lem3071715)). Qed.
Lemma lem3071717 : term107.
Proof. exact (EQ_MP (@lem3071716) (@lem0)). Qed.
Lemma lem3071718 (m : nat) (n : nat) (h1 : term106 m n) : term122 m n.
Proof. exact (conj (@lem3071717) (@lem3071651 m n h1)). Qed.
Lemma lem3071720 (x : real) (y : real) : term123 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3071721 (m : nat) (n : nat) : term124 m n.
Proof. exact (@lem3071720 term34 (term87 m n)). Qed.
Lemma lem3071722 (m : nat) (n : nat) (h1 : term106 m n) : term125 m n.
Proof. exact (@lem3071721 m n (@lem3071718 m n h1)). Qed.
Lemma lem3071723 (m : nat) (n : nat) : (term126 m n) = (term87 m n).
Proof. exact (@lem1982733 (term87 m n)). Qed.
Lemma lem3071724 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3071725 (m : nat) (n : nat) : (term127 m n) = (term90 m n).
Proof. exact (MK_COMB (@lem3071724) (@lem3071723 m n)). Qed.
Lemma lem3071726 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3071727 (m : nat) (n : nat) : (term125 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem3071725 m n) (@lem3071726)). Qed.
Lemma lem3071728 (m : nat) (n : nat) (h1 : term106 m n) : term91 m n.
Proof. exact (EQ_MP (@lem3071727 m n) (@lem3071722 m n h1)). Qed.
Lemma lem3071730 (y : real) : term128 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3071731 (m : nat) (n : nat) : term129 m n.
Proof. exact (@lem3071730 (term53 m n)). Qed.
Lemma lem3071732 (m : nat) (n : nat) (h1 : term106 m n) : term130 m n.
Proof. exact (@lem3071731 m n (@lem3071652 m n h1)). Qed.
Lemma lem3071733 (m : nat) (n : nat) (h1 : term106 m n) : term131 m n.
Proof. exact (@lem3071732 m n h1 term34). Qed.
Lemma lem3071734 (m : nat) (n : nat) : (term131 m n) = ((term132 m n) = term52).
Proof. exact (eq_refl (term131 m n)). Qed.
Lemma lem3071735 (m : nat) (n : nat) (h1 : term106 m n) : (term132 m n) = term52.
Proof. exact (EQ_MP (@lem3071734 m n) (@lem3071733 m n h1)). Qed.
Lemma lem3071736 (m : nat) (n : nat) : (term132 m n) = (term53 m n).
Proof. exact (@lem1982733 (term53 m n)). Qed.
Lemma lem3071737 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3071738 (m : nat) (n : nat) : (term133 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem3071737) (@lem3071736 m n)). Qed.
Lemma lem3071739 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3071740 (m : nat) (n : nat) : ((term132 m n) = term52) = ((term53 m n) = term52).
Proof. exact (MK_COMB (@lem3071738 m n) (@lem3071739)). Qed.
Lemma lem3071741 (m : nat) (n : nat) (h1 : term106 m n) : (term53 m n) = term52.
Proof. exact (EQ_MP (@lem3071740 m n) (@lem3071735 m n h1)). Qed.
Lemma lem3071742 (m : nat) (n : nat) (h1 : term106 m n) : term106 m n.
Proof. exact (conj (@lem3071741 m n h1) (@lem3071728 m n h1)). Qed.
Lemma lem3071744 (x : real) (y : real) : term134 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3071745 (m : nat) (n : nat) : term135 m n.
Proof. exact (@lem3071744 (term53 m n) (term87 m n)). Qed.
Lemma lem3071746 (m : nat) (n : nat) (h1 : term106 m n) : term136 m n.
Proof. exact (@lem3071745 m n (@lem3071742 m n h1)). Qed.
Lemma lem3071747 (m : nat) (n : nat) : (term137 m n) = (term138 m n).
Proof. exact (@lem1982753 (real_of_num m) (term88 m) (term88 n) (term139 n)). Qed.
Lemma lem3071748 (m : nat) : (term140 m) = (term141 m).
Proof. exact (@lem1982715 term61 (real_of_num m)). Qed.
Lemma lem3071750 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3071751 : term34 = term63.
Proof. exact (@lem3071750 term35). Qed.
Lemma lem3071753 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3071754 : term61 = term66.
Proof. exact (@lem3071753 term35). Qed.
Lemma lem3071755 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3071756 : term142 = term143.
Proof. exact (MK_COMB (@lem3071755) (@lem3071754)). Qed.
Lemma lem3071757 : term144 = term145.
Proof. exact (MK_COMB (@lem3071756) (@lem3071751)). Qed.
Lemma lem3071758 : term146.
Proof. exact (@lem1981473 term61 term34 term34 term34 term52 term34). Qed.
Lemma lem3071760 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3071761 : term108 = term115.
Proof. exact (@lem3071760 (NUMERAL 0) term35). Qed.
Lemma lem3071762 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3071763 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3071764 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3071763 h1) (fun h1 : term115 = True => @lem3071762)). Qed.
Lemma lem3071765 : term115 = True.
Proof. exact (EQ_MP (@lem3071764) (@lem3071762)). Qed.
Lemma lem3071766 : term108 = True.
Proof. exact (TRANS (@lem3071761) (@lem3071765)). Qed.
Lemma lem3071767 : True = term108.
Proof. exact (SYM (@lem3071766)). Qed.
Lemma lem3071768 : term108.
Proof. exact (EQ_MP (@lem3071767) (@lem0)). Qed.
Lemma lem3071769 : term147.
Proof. exact (@lem3071758 (@lem3071768)). Qed.
Lemma lem3071771 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3071772 : term108 = term115.
Proof. exact (@lem3071771 (NUMERAL 0) term35). Qed.
Lemma lem3071773 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3071774 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3071775 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3071774 h1) (fun h1 : term115 = True => @lem3071773)). Qed.
Lemma lem3071776 : term115 = True.
Proof. exact (EQ_MP (@lem3071775) (@lem3071773)). Qed.
Lemma lem3071777 : term108 = True.
Proof. exact (TRANS (@lem3071772) (@lem3071776)). Qed.
Lemma lem3071778 : True = term108.
Proof. exact (SYM (@lem3071777)). Qed.
Lemma lem3071779 : term108.
Proof. exact (EQ_MP (@lem3071778) (@lem0)). Qed.
Lemma lem3071780 : term148.
Proof. exact (@lem3071769 (@lem3071779)). Qed.
Lemma lem3071782 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3071783 : term108 = term115.
Proof. exact (@lem3071782 (NUMERAL 0) term35). Qed.
Lemma lem3071784 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3071785 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3071786 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3071785 h1) (fun h1 : term115 = True => @lem3071784)). Qed.
Lemma lem3071787 : term115 = True.
Proof. exact (EQ_MP (@lem3071786) (@lem3071784)). Qed.
Lemma lem3071788 : term108 = True.
Proof. exact (TRANS (@lem3071783) (@lem3071787)). Qed.
Lemma lem3071789 : True = term108.
Proof. exact (SYM (@lem3071788)). Qed.
Lemma lem3071790 : term108.
Proof. exact (EQ_MP (@lem3071789) (@lem0)). Qed.
Lemma lem3071791 : term149.
Proof. exact (@lem3071780 (@lem3071790)). Qed.
Lemma lem3071793 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3071794 : term74 = term75.
Proof. exact (@lem3071793 term35 term35). Qed.
Lemma lem3071795 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071796 : term77 = term35.
Proof. exact (EQ_MP (@lem3071795) (@lem940073)). Qed.
Lemma lem3071797 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071798 : term75 = term34.
Proof. exact (MK_COMB (@lem3071797) (@lem3071796)). Qed.
Lemma lem3071799 : term74 = term34.
Proof. exact (TRANS (@lem3071794) (@lem3071798)). Qed.
Lemma lem3071801 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3071802 : term69 = term80.
Proof. exact (@lem3071801 term35 term35). Qed.
Lemma lem3071803 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071804 : term77 = term35.
Proof. exact (EQ_MP (@lem3071803) (@lem940073)). Qed.
Lemma lem3071805 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071806 : term75 = term34.
Proof. exact (MK_COMB (@lem3071805) (@lem3071804)). Qed.
Lemma lem3071807 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3071808 : term80 = term61.
Proof. exact (MK_COMB (@lem3071807) (@lem3071806)). Qed.
Lemma lem3071809 : term69 = term61.
Proof. exact (TRANS (@lem3071802) (@lem3071808)). Qed.
Lemma lem3071810 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3071811 : term150 = term142.
Proof. exact (MK_COMB (@lem3071810) (@lem3071809)). Qed.
Lemma lem3071812 : term151 = term144.
Proof. exact (MK_COMB (@lem3071811) (@lem3071799)). Qed.
Lemma lem3071814 (m : nat) : (term152 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3071815 : term144 = term52.
Proof. exact (@lem3071814 term35). Qed.
Lemma lem3071816 : term151 = term52.
Proof. exact (TRANS (@lem3071812) (@lem3071815)). Qed.
Lemma lem3071817 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3071818 : term153 = term154.
Proof. exact (MK_COMB (@lem3071817) (@lem3071816)). Qed.
Lemma lem3071819 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem3071820 : term155 = term120.
Proof. exact (MK_COMB (@lem3071818) (@lem3071819)). Qed.
Lemma lem3071822 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3071823 : term120 = term52.
Proof. exact (@lem3071822 term35). Qed.
Lemma lem3071824 : term155 = term52.
Proof. exact (TRANS (@lem3071820) (@lem3071823)). Qed.
Lemma lem3071826 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3071827 : term74 = term75.
Proof. exact (@lem3071826 term35 term35). Qed.
Lemma lem3071828 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071829 : term77 = term35.
Proof. exact (EQ_MP (@lem3071828) (@lem940073)). Qed.
Lemma lem3071830 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071831 : term75 = term34.
Proof. exact (MK_COMB (@lem3071830) (@lem3071829)). Qed.
Lemma lem3071832 : term74 = term34.
Proof. exact (TRANS (@lem3071827) (@lem3071831)). Qed.
Lemma lem3071833 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem3071834 : term156 = term120.
Proof. exact (MK_COMB (@lem3071833) (@lem3071832)). Qed.
Lemma lem3071836 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3071837 : term120 = term52.
Proof. exact (@lem3071836 term35). Qed.
Lemma lem3071838 : term156 = term52.
Proof. exact (TRANS (@lem3071834) (@lem3071837)). Qed.
Lemma lem3071839 : term52 = term156.
Proof. exact (SYM (@lem3071838)). Qed.
Lemma lem3071840 : term155 = term156.
Proof. exact (TRANS (@lem3071824) (@lem3071839)). Qed.
Lemma lem3071841 : term145 = term109.
Proof. exact (@lem3071791 (@lem3071840)). Qed.
Lemma lem3071842 : term144 = term109.
Proof. exact (TRANS (@lem3071757) (@lem3071841)). Qed.
Lemma lem3071844 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3071845 : term109 = term52.
Proof. exact (@lem3071844 term52). Qed.
Lemma lem3071846 : term144 = term52.
Proof. exact (TRANS (@lem3071842) (@lem3071845)). Qed.
Lemma lem3071847 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3071848 : term157 = term154.
Proof. exact (MK_COMB (@lem3071847) (@lem3071846)). Qed.
Lemma lem3071849 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem3071850 (m : nat) : (term141 m) = (term119 m).
Proof. exact (MK_COMB (@lem3071848) (@lem3071849 m)). Qed.
Lemma lem3071851 (m : nat) : (term140 m) = (term119 m).
Proof. exact (TRANS (@lem3071748 m) (@lem3071850 m)). Qed.
Lemma lem3071852 (m : nat) : (term119 m) = term52.
Proof. exact (@lem1982719 (real_of_num m)). Qed.
Lemma lem3071853 (m : nat) : (term140 m) = term52.
Proof. exact (TRANS (@lem3071851 m) (@lem3071852 m)). Qed.
Lemma lem3071854 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3071855 (m : nat) : (term158 m) = term159.
Proof. exact (MK_COMB (@lem3071854) (@lem3071853 m)). Qed.
Lemma lem3071856 (n : nat) : (term160 n) = (term161 n).
Proof. exact (@lem1982763 (term88 n) (real_of_num n) term61). Qed.
Lemma lem3071857 (n : nat) : (term162 n) = (term141 n).
Proof. exact (@lem1982713 term61 (real_of_num n)). Qed.
Lemma lem3071859 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3071860 : term34 = term63.
Proof. exact (@lem3071859 term35). Qed.
Lemma lem3071862 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3071863 : term61 = term66.
Proof. exact (@lem3071862 term35). Qed.
Lemma lem3071864 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3071865 : term142 = term143.
Proof. exact (MK_COMB (@lem3071864) (@lem3071863)). Qed.
Lemma lem3071866 : term144 = term145.
Proof. exact (MK_COMB (@lem3071865) (@lem3071860)). Qed.
Lemma lem3071867 : term146.
Proof. exact (@lem1981473 term61 term34 term34 term34 term52 term34). Qed.
Lemma lem3071869 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3071870 : term108 = term115.
Proof. exact (@lem3071869 (NUMERAL 0) term35). Qed.
Lemma lem3071871 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3071872 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3071873 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3071872 h1) (fun h1 : term115 = True => @lem3071871)). Qed.
Lemma lem3071874 : term115 = True.
Proof. exact (EQ_MP (@lem3071873) (@lem3071871)). Qed.
Lemma lem3071875 : term108 = True.
Proof. exact (TRANS (@lem3071870) (@lem3071874)). Qed.
Lemma lem3071876 : True = term108.
Proof. exact (SYM (@lem3071875)). Qed.
Lemma lem3071877 : term108.
Proof. exact (EQ_MP (@lem3071876) (@lem0)). Qed.
Lemma lem3071878 : term147.
Proof. exact (@lem3071867 (@lem3071877)). Qed.
Lemma lem3071880 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3071881 : term108 = term115.
Proof. exact (@lem3071880 (NUMERAL 0) term35). Qed.
Lemma lem3071882 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3071883 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3071884 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3071883 h1) (fun h1 : term115 = True => @lem3071882)). Qed.
Lemma lem3071885 : term115 = True.
Proof. exact (EQ_MP (@lem3071884) (@lem3071882)). Qed.
Lemma lem3071886 : term108 = True.
Proof. exact (TRANS (@lem3071881) (@lem3071885)). Qed.
Lemma lem3071887 : True = term108.
Proof. exact (SYM (@lem3071886)). Qed.
Lemma lem3071888 : term108.
Proof. exact (EQ_MP (@lem3071887) (@lem0)). Qed.
Lemma lem3071889 : term148.
Proof. exact (@lem3071878 (@lem3071888)). Qed.
Lemma lem3071891 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3071892 : term108 = term115.
Proof. exact (@lem3071891 (NUMERAL 0) term35). Qed.
Lemma lem3071893 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3071894 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3071895 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3071894 h1) (fun h1 : term115 = True => @lem3071893)). Qed.
Lemma lem3071896 : term115 = True.
Proof. exact (EQ_MP (@lem3071895) (@lem3071893)). Qed.
Lemma lem3071897 : term108 = True.
Proof. exact (TRANS (@lem3071892) (@lem3071896)). Qed.
Lemma lem3071898 : True = term108.
Proof. exact (SYM (@lem3071897)). Qed.
Lemma lem3071899 : term108.
Proof. exact (EQ_MP (@lem3071898) (@lem0)). Qed.
Lemma lem3071900 : term149.
Proof. exact (@lem3071889 (@lem3071899)). Qed.
Lemma lem3071902 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3071903 : term74 = term75.
Proof. exact (@lem3071902 term35 term35). Qed.
Lemma lem3071904 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071905 : term77 = term35.
Proof. exact (EQ_MP (@lem3071904) (@lem940073)). Qed.
Lemma lem3071906 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071907 : term75 = term34.
Proof. exact (MK_COMB (@lem3071906) (@lem3071905)). Qed.
Lemma lem3071908 : term74 = term34.
Proof. exact (TRANS (@lem3071903) (@lem3071907)). Qed.
Lemma lem3071910 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3071911 : term69 = term80.
Proof. exact (@lem3071910 term35 term35). Qed.
Lemma lem3071912 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071913 : term77 = term35.
Proof. exact (EQ_MP (@lem3071912) (@lem940073)). Qed.
Lemma lem3071914 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071915 : term75 = term34.
Proof. exact (MK_COMB (@lem3071914) (@lem3071913)). Qed.
Lemma lem3071916 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3071917 : term80 = term61.
Proof. exact (MK_COMB (@lem3071916) (@lem3071915)). Qed.
Lemma lem3071918 : term69 = term61.
Proof. exact (TRANS (@lem3071911) (@lem3071917)). Qed.
Lemma lem3071919 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3071920 : term150 = term142.
Proof. exact (MK_COMB (@lem3071919) (@lem3071918)). Qed.
Lemma lem3071921 : term151 = term144.
Proof. exact (MK_COMB (@lem3071920) (@lem3071908)). Qed.
Lemma lem3071923 (m : nat) : (term152 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3071924 : term144 = term52.
Proof. exact (@lem3071923 term35). Qed.
Lemma lem3071925 : term151 = term52.
Proof. exact (TRANS (@lem3071921) (@lem3071924)). Qed.
Lemma lem3071926 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3071927 : term153 = term154.
Proof. exact (MK_COMB (@lem3071926) (@lem3071925)). Qed.
Lemma lem3071928 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem3071929 : term155 = term120.
Proof. exact (MK_COMB (@lem3071927) (@lem3071928)). Qed.
Lemma lem3071931 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3071932 : term120 = term52.
Proof. exact (@lem3071931 term35). Qed.
Lemma lem3071933 : term155 = term52.
Proof. exact (TRANS (@lem3071929) (@lem3071932)). Qed.
Lemma lem3071935 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3071936 : term74 = term75.
Proof. exact (@lem3071935 term35 term35). Qed.
Lemma lem3071937 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3071938 : term77 = term35.
Proof. exact (EQ_MP (@lem3071937) (@lem940073)). Qed.
Lemma lem3071939 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3071940 : term75 = term34.
Proof. exact (MK_COMB (@lem3071939) (@lem3071938)). Qed.
Lemma lem3071941 : term74 = term34.
Proof. exact (TRANS (@lem3071936) (@lem3071940)). Qed.
Lemma lem3071942 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem3071943 : term156 = term120.
Proof. exact (MK_COMB (@lem3071942) (@lem3071941)). Qed.
Lemma lem3071945 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3071946 : term120 = term52.
Proof. exact (@lem3071945 term35). Qed.
Lemma lem3071947 : term156 = term52.
Proof. exact (TRANS (@lem3071943) (@lem3071946)). Qed.
Lemma lem3071948 : term52 = term156.
Proof. exact (SYM (@lem3071947)). Qed.
Lemma lem3071949 : term155 = term156.
Proof. exact (TRANS (@lem3071933) (@lem3071948)). Qed.
Lemma lem3071950 : term145 = term109.
Proof. exact (@lem3071900 (@lem3071949)). Qed.
Lemma lem3071951 : term144 = term109.
Proof. exact (TRANS (@lem3071866) (@lem3071950)). Qed.
Lemma lem3071953 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3071954 : term109 = term52.
Proof. exact (@lem3071953 term52). Qed.
Lemma lem3071955 : term144 = term52.
Proof. exact (TRANS (@lem3071951) (@lem3071954)). Qed.
Lemma lem3071956 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3071957 : term157 = term154.
Proof. exact (MK_COMB (@lem3071956) (@lem3071955)). Qed.
Lemma lem3071958 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem3071959 (n : nat) : (term141 n) = (term119 n).
Proof. exact (MK_COMB (@lem3071957) (@lem3071958 n)). Qed.
Lemma lem3071960 (n : nat) : (term162 n) = (term119 n).
Proof. exact (TRANS (@lem3071857 n) (@lem3071959 n)). Qed.
Lemma lem3071961 (n : nat) : (term119 n) = term52.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem3071962 (n : nat) : (term162 n) = term52.
Proof. exact (TRANS (@lem3071960 n) (@lem3071961 n)). Qed.
Lemma lem3071963 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3071964 (n : nat) : (term163 n) = term159.
Proof. exact (MK_COMB (@lem3071963) (@lem3071962 n)). Qed.
Lemma lem3071965 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3071966 (n : nat) : (term161 n) = term164.
Proof. exact (MK_COMB (@lem3071964 n) (@lem3071965)). Qed.
Lemma lem3071967 (n : nat) : (term160 n) = term164.
Proof. exact (TRANS (@lem3071856 n) (@lem3071966 n)). Qed.
Lemma lem3071968 : term164 = term61.
Proof. exact (@lem1982721 term61). Qed.
Lemma lem3071969 (n : nat) : (term160 n) = term61.
Proof. exact (TRANS (@lem3071967 n) (@lem3071968)). Qed.
Lemma lem3071970 (m : nat) (n : nat) : (term138 m n) = term164.
Proof. exact (MK_COMB (@lem3071855 m) (@lem3071969 n)). Qed.
Lemma lem3071971 (m : nat) (n : nat) : (term137 m n) = term164.
Proof. exact (TRANS (@lem3071747 m n) (@lem3071970 m n)). Qed.
Lemma lem3071972 : term164 = term61.
Proof. exact (@lem1982721 term61). Qed.
Lemma lem3071973 (m : nat) (n : nat) : (term137 m n) = term61.
Proof. exact (TRANS (@lem3071971 m n) (@lem3071972)). Qed.
Lemma lem3071974 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3071975 (m : nat) (n : nat) : (term165 m n) = term166.
Proof. exact (MK_COMB (@lem3071974) (@lem3071973 m n)). Qed.
Lemma lem3071976 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3071977 (m : nat) (n : nat) : (term136 m n) = term167.
Proof. exact (MK_COMB (@lem3071975 m n) (@lem3071976)). Qed.
Lemma lem3071978 (m : nat) (n : nat) (h1 : term106 m n) : term167.
Proof. exact (EQ_MP (@lem3071977 m n) (@lem3071746 m n h1)). Qed.
Lemma lem3071980 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3071981 : term167 = term168.
Proof. exact (@lem3071980 term52 term61). Qed.
Lemma lem3071983 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3071984 : term61 = term66.
Proof. exact (@lem3071983 term35). Qed.
Lemma lem3071986 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3071987 : term52 = term109.
Proof. exact (@lem3071986 (NUMERAL 0)). Qed.
Lemma lem3071988 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3071989 : term169 = term170.
Proof. exact (MK_COMB (@lem3071988) (@lem3071987)). Qed.
Lemma lem3071990 : term168 = term171.
Proof. exact (MK_COMB (@lem3071989) (@lem3071984)). Qed.
Lemma lem3071991 : term172.
Proof. exact (@lem1980026 term52 term34 term61 term34). Qed.
Lemma lem3071993 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3071994 : term108 = term115.
Proof. exact (@lem3071993 (NUMERAL 0) term35). Qed.
Lemma lem3071995 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3071996 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3071997 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3071996 h1) (fun h1 : term115 = True => @lem3071995)). Qed.
Lemma lem3071998 : term115 = True.
Proof. exact (EQ_MP (@lem3071997) (@lem3071995)). Qed.
Lemma lem3071999 : term108 = True.
Proof. exact (TRANS (@lem3071994) (@lem3071998)). Qed.
Lemma lem3072000 : True = term108.
Proof. exact (SYM (@lem3071999)). Qed.
Lemma lem3072001 : term108.
Proof. exact (EQ_MP (@lem3072000) (@lem0)). Qed.
Lemma lem3072002 : term173.
Proof. exact (@lem3071991 (@lem3072001)). Qed.
Lemma lem3072004 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072005 : term108 = term115.
Proof. exact (@lem3072004 (NUMERAL 0) term35). Qed.
Lemma lem3072006 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072007 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072008 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072007 h1) (fun h1 : term115 = True => @lem3072006)). Qed.
Lemma lem3072009 : term115 = True.
Proof. exact (EQ_MP (@lem3072008) (@lem3072006)). Qed.
Lemma lem3072010 : term108 = True.
Proof. exact (TRANS (@lem3072005) (@lem3072009)). Qed.
Lemma lem3072011 : True = term108.
Proof. exact (SYM (@lem3072010)). Qed.
Lemma lem3072012 : term108.
Proof. exact (EQ_MP (@lem3072011) (@lem0)). Qed.
Lemma lem3072013 : term171 = term174.
Proof. exact (@lem3072002 (@lem3072012)). Qed.
Lemma lem3072015 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3072016 : term69 = term80.
Proof. exact (@lem3072015 term35 term35). Qed.
Lemma lem3072017 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072018 : term77 = term35.
Proof. exact (EQ_MP (@lem3072017) (@lem940073)). Qed.
Lemma lem3072019 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072020 : term75 = term34.
Proof. exact (MK_COMB (@lem3072019) (@lem3072018)). Qed.
Lemma lem3072021 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3072022 : term80 = term61.
Proof. exact (MK_COMB (@lem3072021) (@lem3072020)). Qed.
Lemma lem3072023 : term69 = term61.
Proof. exact (TRANS (@lem3072016) (@lem3072022)). Qed.
Lemma lem3072025 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072026 : term120 = term52.
Proof. exact (@lem3072025 term35). Qed.
Lemma lem3072027 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3072028 : term175 = term169.
Proof. exact (MK_COMB (@lem3072027) (@lem3072026)). Qed.
Lemma lem3072029 : term174 = term168.
Proof. exact (MK_COMB (@lem3072028) (@lem3072023)). Qed.
Lemma lem3072031 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3072032 : term168 = term178.
Proof. exact (@lem3072031 (NUMERAL 0) term35). Qed.
Lemma lem3072033 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072034 (h1 : term116 = (BIT1 0)) : (term35 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3072035 : (term116 = (BIT1 0)) = ((term35 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072034 h1) (fun h1 : (term35 = (NUMERAL 0)) = False => @lem3072033)). Qed.
Lemma lem3072036 : (term35 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3072035) (@lem3072033)). Qed.
Lemma lem3072037 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3072038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3072039 : term179 = (and True).
Proof. exact (MK_COMB (@lem3072038) (@lem3072037)). Qed.
Lemma lem3072040 : term178 = (True /\ False).
Proof. exact (MK_COMB (@lem3072039) (@lem3072036)). Qed.
Lemma lem3072042 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3072043 : term178 = False.
Proof. exact (TRANS (@lem3072040) (@lem3072042)). Qed.
Lemma lem3072044 : term168 = False.
Proof. exact (TRANS (@lem3072032) (@lem3072043)). Qed.
Lemma lem3072045 : term174 = False.
Proof. exact (TRANS (@lem3072029) (@lem3072044)). Qed.
Lemma lem3072046 : term171 = False.
Proof. exact (TRANS (@lem3072013) (@lem3072045)). Qed.
Lemma lem3072047 : term168 = False.
Proof. exact (TRANS (@lem3071990) (@lem3072046)). Qed.
Lemma lem3072048 : term167 = False.
Proof. exact (TRANS (@lem3071981) (@lem3072047)). Qed.
Lemma lem3072049 (m : nat) (n : nat) (h1 : term106 m n) : False.
Proof. exact (EQ_MP (@lem3072048) (@lem3071978 m n h1)). Qed.
Lemma lem3072050 (m : nat) (n : nat) (h1 : term180 m n) : term180 m n.
Proof. exact (h1). Qed.
Lemma lem3072051 (m : nat) (n : nat) (h1 : term180 m n) : term93 m n.
Proof. exact (proj2 (@lem3072050 m n h1)). Qed.
Lemma lem3072052 (m : nat) (n : nat) (h1 : term180 m n) : (term53 m n) = term52.
Proof. exact (proj1 (@lem3072050 m n h1)). Qed.
Lemma lem3072056 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3072057 : term107 = term108.
Proof. exact (@lem3072056 term52 term34). Qed.
Lemma lem3072059 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3072060 : term34 = term63.
Proof. exact (@lem3072059 term35). Qed.
Lemma lem3072062 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3072063 : term52 = term109.
Proof. exact (@lem3072062 (NUMERAL 0)). Qed.
Lemma lem3072064 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3072065 : term110 = term111.
Proof. exact (MK_COMB (@lem3072064) (@lem3072063)). Qed.
Lemma lem3072066 : term108 = term112.
Proof. exact (MK_COMB (@lem3072065) (@lem3072060)). Qed.
Lemma lem3072067 : term113.
Proof. exact (@lem1980255 term52 term34 term34 term34). Qed.
Lemma lem3072069 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072070 : term108 = term115.
Proof. exact (@lem3072069 (NUMERAL 0) term35). Qed.
Lemma lem3072071 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072072 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072073 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072072 h1) (fun h1 : term115 = True => @lem3072071)). Qed.
Lemma lem3072074 : term115 = True.
Proof. exact (EQ_MP (@lem3072073) (@lem3072071)). Qed.
Lemma lem3072075 : term108 = True.
Proof. exact (TRANS (@lem3072070) (@lem3072074)). Qed.
Lemma lem3072076 : True = term108.
Proof. exact (SYM (@lem3072075)). Qed.
Lemma lem3072077 : term108.
Proof. exact (EQ_MP (@lem3072076) (@lem0)). Qed.
Lemma lem3072078 : term117.
Proof. exact (@lem3072067 (@lem3072077)). Qed.
Lemma lem3072080 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072081 : term108 = term115.
Proof. exact (@lem3072080 (NUMERAL 0) term35). Qed.
Lemma lem3072082 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072083 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072084 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072083 h1) (fun h1 : term115 = True => @lem3072082)). Qed.
Lemma lem3072085 : term115 = True.
Proof. exact (EQ_MP (@lem3072084) (@lem3072082)). Qed.
Lemma lem3072086 : term108 = True.
Proof. exact (TRANS (@lem3072081) (@lem3072085)). Qed.
Lemma lem3072087 : True = term108.
Proof. exact (SYM (@lem3072086)). Qed.
Lemma lem3072088 : term108.
Proof. exact (EQ_MP (@lem3072087) (@lem0)). Qed.
Lemma lem3072089 : term112 = term118.
Proof. exact (@lem3072078 (@lem3072088)). Qed.
Lemma lem3072091 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3072092 : term74 = term75.
Proof. exact (@lem3072091 term35 term35). Qed.
Lemma lem3072093 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072094 : term77 = term35.
Proof. exact (EQ_MP (@lem3072093) (@lem940073)). Qed.
Lemma lem3072095 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072096 : term75 = term34.
Proof. exact (MK_COMB (@lem3072095) (@lem3072094)). Qed.
Lemma lem3072097 : term74 = term34.
Proof. exact (TRANS (@lem3072092) (@lem3072096)). Qed.
Lemma lem3072099 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072100 : term120 = term52.
Proof. exact (@lem3072099 term35). Qed.
Lemma lem3072101 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3072102 : term121 = term110.
Proof. exact (MK_COMB (@lem3072101) (@lem3072100)). Qed.
Lemma lem3072103 : term118 = term108.
Proof. exact (MK_COMB (@lem3072102) (@lem3072097)). Qed.
Lemma lem3072105 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072106 : term108 = term115.
Proof. exact (@lem3072105 (NUMERAL 0) term35). Qed.
Lemma lem3072107 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072108 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072109 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072108 h1) (fun h1 : term115 = True => @lem3072107)). Qed.
Lemma lem3072110 : term115 = True.
Proof. exact (EQ_MP (@lem3072109) (@lem3072107)). Qed.
Lemma lem3072111 : term108 = True.
Proof. exact (TRANS (@lem3072106) (@lem3072110)). Qed.
Lemma lem3072112 : term118 = True.
Proof. exact (TRANS (@lem3072103) (@lem3072111)). Qed.
Lemma lem3072113 : term112 = True.
Proof. exact (TRANS (@lem3072089) (@lem3072112)). Qed.
Lemma lem3072114 : term108 = True.
Proof. exact (TRANS (@lem3072066) (@lem3072113)). Qed.
Lemma lem3072115 : term107 = True.
Proof. exact (TRANS (@lem3072057) (@lem3072114)). Qed.
Lemma lem3072116 : True = term107.
Proof. exact (SYM (@lem3072115)). Qed.
Lemma lem3072117 : term107.
Proof. exact (EQ_MP (@lem3072116) (@lem0)). Qed.
Lemma lem3072118 (m : nat) (n : nat) (h1 : term180 m n) : term181 m n.
Proof. exact (conj (@lem3072117) (@lem3072051 m n h1)). Qed.
Lemma lem3072120 (x : real) (y : real) : term123 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3072121 (m : nat) (n : nat) : term182 m n.
Proof. exact (@lem3072120 term34 (term86 m n)). Qed.
Lemma lem3072122 (m : nat) (n : nat) (h1 : term180 m n) : term183 m n.
Proof. exact (@lem3072121 m n (@lem3072118 m n h1)). Qed.
Lemma lem3072123 (m : nat) (n : nat) : (term184 m n) = (term86 m n).
Proof. exact (@lem1982733 (term86 m n)). Qed.
Lemma lem3072124 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3072125 (m : nat) (n : nat) : (term185 m n) = (term92 m n).
Proof. exact (MK_COMB (@lem3072124) (@lem3072123 m n)). Qed.
Lemma lem3072126 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3072127 (m : nat) (n : nat) : (term183 m n) = (term93 m n).
Proof. exact (MK_COMB (@lem3072125 m n) (@lem3072126)). Qed.
Lemma lem3072128 (m : nat) (n : nat) (h1 : term180 m n) : term93 m n.
Proof. exact (EQ_MP (@lem3072127 m n) (@lem3072122 m n h1)). Qed.
Lemma lem3072130 (y : real) : term128 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3072131 (m : nat) (n : nat) : term129 m n.
Proof. exact (@lem3072130 (term53 m n)). Qed.
Lemma lem3072132 (m : nat) (n : nat) (h1 : term180 m n) : term130 m n.
Proof. exact (@lem3072131 m n (@lem3072052 m n h1)). Qed.
Lemma lem3072133 (m : nat) (n : nat) (h1 : term180 m n) : term186 m n.
Proof. exact (@lem3072132 m n h1 term61). Qed.
Lemma lem3072134 (m : nat) (n : nat) : (term186 m n) = ((term187 m n) = term52).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem3072135 (m : nat) (n : nat) (h1 : term180 m n) : (term187 m n) = term52.
Proof. exact (EQ_MP (@lem3072134 m n) (@lem3072133 m n h1)). Qed.
Lemma lem3072136 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (@lem1982781 (real_of_num m) term61 (term88 n)). Qed.
Lemma lem3072137 (n : nat) : (term189 n) = (term190 n).
Proof. exact (@lem1982749 term61 term61 (real_of_num n)). Qed.
Lemma lem3072139 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3072140 : term61 = term66.
Proof. exact (@lem3072139 term35). Qed.
Lemma lem3072142 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3072143 : term61 = term66.
Proof. exact (@lem3072142 term35). Qed.
Lemma lem3072144 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3072145 : term67 = term68.
Proof. exact (MK_COMB (@lem3072144) (@lem3072143)). Qed.
Lemma lem3072146 : term191 = term192.
Proof. exact (MK_COMB (@lem3072145) (@lem3072140)). Qed.
Lemma lem3072147 : term192 = term193.
Proof. exact (@lem1981613 term61 term61 term34 term34). Qed.
Lemma lem3072149 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3072150 : term74 = term75.
Proof. exact (@lem3072149 term35 term35). Qed.
Lemma lem3072151 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072152 : term77 = term35.
Proof. exact (EQ_MP (@lem3072151) (@lem940073)). Qed.
Lemma lem3072153 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072154 : term75 = term34.
Proof. exact (MK_COMB (@lem3072153) (@lem3072152)). Qed.
Lemma lem3072155 : term74 = term34.
Proof. exact (TRANS (@lem3072150) (@lem3072154)). Qed.
Lemma lem3072157 (m : nat) (n : nat) : (term194 m n) = (term73 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3072158 : term191 = term75.
Proof. exact (@lem3072157 term35 term35). Qed.
Lemma lem3072159 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072160 : term77 = term35.
Proof. exact (EQ_MP (@lem3072159) (@lem940073)). Qed.
Lemma lem3072161 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072162 : term75 = term34.
Proof. exact (MK_COMB (@lem3072161) (@lem3072160)). Qed.
Lemma lem3072163 : term191 = term34.
Proof. exact (TRANS (@lem3072158) (@lem3072162)). Qed.
Lemma lem3072164 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3072165 : term195 = term196.
Proof. exact (MK_COMB (@lem3072164) (@lem3072163)). Qed.
Lemma lem3072166 : term193 = term63.
Proof. exact (MK_COMB (@lem3072165) (@lem3072155)). Qed.
Lemma lem3072167 : term192 = term63.
Proof. exact (TRANS (@lem3072147) (@lem3072166)). Qed.
Lemma lem3072168 : term191 = term63.
Proof. exact (TRANS (@lem3072146) (@lem3072167)). Qed.
Lemma lem3072170 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3072171 : term63 = term34.
Proof. exact (@lem3072170 term34). Qed.
Lemma lem3072172 : term191 = term34.
Proof. exact (TRANS (@lem3072168) (@lem3072171)). Qed.
Lemma lem3072173 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3072174 : term197 = term198.
Proof. exact (MK_COMB (@lem3072173) (@lem3072172)). Qed.
Lemma lem3072175 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem3072176 (n : nat) : (term190 n) = (term199 n).
Proof. exact (MK_COMB (@lem3072174) (@lem3072175 n)). Qed.
Lemma lem3072177 (n : nat) : (term189 n) = (term199 n).
Proof. exact (TRANS (@lem3072137 n) (@lem3072176 n)). Qed.
Lemma lem3072178 (n : nat) : (term199 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem3072179 (n : nat) : (term189 n) = (real_of_num n).
Proof. exact (TRANS (@lem3072177 n) (@lem3072178 n)). Qed.
Lemma lem3072182 (m : nat) : (term84 m) = (term84 m).
Proof. exact (eq_refl (term84 m)). Qed.
Lemma lem3072183 (m : nat) (n : nat) : (term188 m n) = (term200 m n).
Proof. exact (MK_COMB (@lem3072182 m) (@lem3072179 n)). Qed.
Lemma lem3072184 (m : nat) (n : nat) : (term187 m n) = (term200 m n).
Proof. exact (TRANS (@lem3072136 m n) (@lem3072183 m n)). Qed.
Lemma lem3072185 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3072186 (m : nat) (n : nat) : (term201 m n) = (term202 m n).
Proof. exact (MK_COMB (@lem3072185) (@lem3072184 m n)). Qed.
Lemma lem3072187 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3072188 (m : nat) (n : nat) : ((term187 m n) = term52) = ((term200 m n) = term52).
Proof. exact (MK_COMB (@lem3072186 m n) (@lem3072187)). Qed.
Lemma lem3072189 (m : nat) (n : nat) (h1 : term180 m n) : (term200 m n) = term52.
Proof. exact (EQ_MP (@lem3072188 m n) (@lem3072135 m n h1)). Qed.
Lemma lem3072190 (m : nat) (n : nat) (h1 : term180 m n) : term203 m n.
Proof. exact (conj (@lem3072189 m n h1) (@lem3072128 m n h1)). Qed.
Lemma lem3072192 (x : real) (y : real) : term134 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3072193 (m : nat) (n : nat) : term204 m n.
Proof. exact (@lem3072192 (term200 m n) (term86 m n)). Qed.
Lemma lem3072194 (m : nat) (n : nat) (h1 : term180 m n) : term205 m n.
Proof. exact (@lem3072193 m n (@lem3072190 m n h1)). Qed.
Lemma lem3072195 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (@lem1982753 (term88 m) (real_of_num m) (real_of_num n) (term85 n)). Qed.
Lemma lem3072196 (m : nat) : (term162 m) = (term141 m).
Proof. exact (@lem1982713 term61 (real_of_num m)). Qed.
Lemma lem3072198 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3072199 : term34 = term63.
Proof. exact (@lem3072198 term35). Qed.
Lemma lem3072201 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3072202 : term61 = term66.
Proof. exact (@lem3072201 term35). Qed.
Lemma lem3072203 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3072204 : term142 = term143.
Proof. exact (MK_COMB (@lem3072203) (@lem3072202)). Qed.
Lemma lem3072205 : term144 = term145.
Proof. exact (MK_COMB (@lem3072204) (@lem3072199)). Qed.
Lemma lem3072206 : term146.
Proof. exact (@lem1981473 term61 term34 term34 term34 term52 term34). Qed.
Lemma lem3072208 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072209 : term108 = term115.
Proof. exact (@lem3072208 (NUMERAL 0) term35). Qed.
Lemma lem3072210 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072211 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072212 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072211 h1) (fun h1 : term115 = True => @lem3072210)). Qed.
Lemma lem3072213 : term115 = True.
Proof. exact (EQ_MP (@lem3072212) (@lem3072210)). Qed.
Lemma lem3072214 : term108 = True.
Proof. exact (TRANS (@lem3072209) (@lem3072213)). Qed.
Lemma lem3072215 : True = term108.
Proof. exact (SYM (@lem3072214)). Qed.
Lemma lem3072216 : term108.
Proof. exact (EQ_MP (@lem3072215) (@lem0)). Qed.
Lemma lem3072217 : term147.
Proof. exact (@lem3072206 (@lem3072216)). Qed.
Lemma lem3072219 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072220 : term108 = term115.
Proof. exact (@lem3072219 (NUMERAL 0) term35). Qed.
Lemma lem3072221 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072222 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072223 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072222 h1) (fun h1 : term115 = True => @lem3072221)). Qed.
Lemma lem3072224 : term115 = True.
Proof. exact (EQ_MP (@lem3072223) (@lem3072221)). Qed.
Lemma lem3072225 : term108 = True.
Proof. exact (TRANS (@lem3072220) (@lem3072224)). Qed.
Lemma lem3072226 : True = term108.
Proof. exact (SYM (@lem3072225)). Qed.
Lemma lem3072227 : term108.
Proof. exact (EQ_MP (@lem3072226) (@lem0)). Qed.
Lemma lem3072228 : term148.
Proof. exact (@lem3072217 (@lem3072227)). Qed.
Lemma lem3072230 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072231 : term108 = term115.
Proof. exact (@lem3072230 (NUMERAL 0) term35). Qed.
Lemma lem3072232 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072233 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072234 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072233 h1) (fun h1 : term115 = True => @lem3072232)). Qed.
Lemma lem3072235 : term115 = True.
Proof. exact (EQ_MP (@lem3072234) (@lem3072232)). Qed.
Lemma lem3072236 : term108 = True.
Proof. exact (TRANS (@lem3072231) (@lem3072235)). Qed.
Lemma lem3072237 : True = term108.
Proof. exact (SYM (@lem3072236)). Qed.
Lemma lem3072238 : term108.
Proof. exact (EQ_MP (@lem3072237) (@lem0)). Qed.
Lemma lem3072239 : term149.
Proof. exact (@lem3072228 (@lem3072238)). Qed.
Lemma lem3072241 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3072242 : term74 = term75.
Proof. exact (@lem3072241 term35 term35). Qed.
Lemma lem3072243 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072244 : term77 = term35.
Proof. exact (EQ_MP (@lem3072243) (@lem940073)). Qed.
Lemma lem3072245 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072246 : term75 = term34.
Proof. exact (MK_COMB (@lem3072245) (@lem3072244)). Qed.
Lemma lem3072247 : term74 = term34.
Proof. exact (TRANS (@lem3072242) (@lem3072246)). Qed.
Lemma lem3072249 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3072250 : term69 = term80.
Proof. exact (@lem3072249 term35 term35). Qed.
Lemma lem3072251 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072252 : term77 = term35.
Proof. exact (EQ_MP (@lem3072251) (@lem940073)). Qed.
Lemma lem3072253 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072254 : term75 = term34.
Proof. exact (MK_COMB (@lem3072253) (@lem3072252)). Qed.
Lemma lem3072255 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3072256 : term80 = term61.
Proof. exact (MK_COMB (@lem3072255) (@lem3072254)). Qed.
Lemma lem3072257 : term69 = term61.
Proof. exact (TRANS (@lem3072250) (@lem3072256)). Qed.
Lemma lem3072258 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3072259 : term150 = term142.
Proof. exact (MK_COMB (@lem3072258) (@lem3072257)). Qed.
Lemma lem3072260 : term151 = term144.
Proof. exact (MK_COMB (@lem3072259) (@lem3072247)). Qed.
Lemma lem3072262 (m : nat) : (term152 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3072263 : term144 = term52.
Proof. exact (@lem3072262 term35). Qed.
Lemma lem3072264 : term151 = term52.
Proof. exact (TRANS (@lem3072260) (@lem3072263)). Qed.
Lemma lem3072265 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3072266 : term153 = term154.
Proof. exact (MK_COMB (@lem3072265) (@lem3072264)). Qed.
Lemma lem3072267 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem3072268 : term155 = term120.
Proof. exact (MK_COMB (@lem3072266) (@lem3072267)). Qed.
Lemma lem3072270 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072271 : term120 = term52.
Proof. exact (@lem3072270 term35). Qed.
Lemma lem3072272 : term155 = term52.
Proof. exact (TRANS (@lem3072268) (@lem3072271)). Qed.
Lemma lem3072274 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3072275 : term74 = term75.
Proof. exact (@lem3072274 term35 term35). Qed.
Lemma lem3072276 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072277 : term77 = term35.
Proof. exact (EQ_MP (@lem3072276) (@lem940073)). Qed.
Lemma lem3072278 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072279 : term75 = term34.
Proof. exact (MK_COMB (@lem3072278) (@lem3072277)). Qed.
Lemma lem3072280 : term74 = term34.
Proof. exact (TRANS (@lem3072275) (@lem3072279)). Qed.
Lemma lem3072281 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem3072282 : term156 = term120.
Proof. exact (MK_COMB (@lem3072281) (@lem3072280)). Qed.
Lemma lem3072284 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072285 : term120 = term52.
Proof. exact (@lem3072284 term35). Qed.
Lemma lem3072286 : term156 = term52.
Proof. exact (TRANS (@lem3072282) (@lem3072285)). Qed.
Lemma lem3072287 : term52 = term156.
Proof. exact (SYM (@lem3072286)). Qed.
Lemma lem3072288 : term155 = term156.
Proof. exact (TRANS (@lem3072272) (@lem3072287)). Qed.
Lemma lem3072289 : term145 = term109.
Proof. exact (@lem3072239 (@lem3072288)). Qed.
Lemma lem3072290 : term144 = term109.
Proof. exact (TRANS (@lem3072205) (@lem3072289)). Qed.
Lemma lem3072292 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3072293 : term109 = term52.
Proof. exact (@lem3072292 term52). Qed.
Lemma lem3072294 : term144 = term52.
Proof. exact (TRANS (@lem3072290) (@lem3072293)). Qed.
Lemma lem3072295 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3072296 : term157 = term154.
Proof. exact (MK_COMB (@lem3072295) (@lem3072294)). Qed.
Lemma lem3072297 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem3072298 (m : nat) : (term141 m) = (term119 m).
Proof. exact (MK_COMB (@lem3072296) (@lem3072297 m)). Qed.
Lemma lem3072299 (m : nat) : (term162 m) = (term119 m).
Proof. exact (TRANS (@lem3072196 m) (@lem3072298 m)). Qed.
Lemma lem3072300 (m : nat) : (term119 m) = term52.
Proof. exact (@lem1982719 (real_of_num m)). Qed.
Lemma lem3072301 (m : nat) : (term162 m) = term52.
Proof. exact (TRANS (@lem3072299 m) (@lem3072300 m)). Qed.
Lemma lem3072302 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3072303 (m : nat) : (term163 m) = term159.
Proof. exact (MK_COMB (@lem3072302) (@lem3072301 m)). Qed.
Lemma lem3072304 (n : nat) : (term208 n) = (term209 n).
Proof. exact (@lem1982763 (real_of_num n) (term88 n) term61). Qed.
Lemma lem3072305 (n : nat) : (term140 n) = (term141 n).
Proof. exact (@lem1982715 term61 (real_of_num n)). Qed.
Lemma lem3072307 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3072308 : term34 = term63.
Proof. exact (@lem3072307 term35). Qed.
Lemma lem3072310 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3072311 : term61 = term66.
Proof. exact (@lem3072310 term35). Qed.
Lemma lem3072312 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3072313 : term142 = term143.
Proof. exact (MK_COMB (@lem3072312) (@lem3072311)). Qed.
Lemma lem3072314 : term144 = term145.
Proof. exact (MK_COMB (@lem3072313) (@lem3072308)). Qed.
Lemma lem3072315 : term146.
Proof. exact (@lem1981473 term61 term34 term34 term34 term52 term34). Qed.
Lemma lem3072317 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072318 : term108 = term115.
Proof. exact (@lem3072317 (NUMERAL 0) term35). Qed.
Lemma lem3072319 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072320 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072321 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072320 h1) (fun h1 : term115 = True => @lem3072319)). Qed.
Lemma lem3072322 : term115 = True.
Proof. exact (EQ_MP (@lem3072321) (@lem3072319)). Qed.
Lemma lem3072323 : term108 = True.
Proof. exact (TRANS (@lem3072318) (@lem3072322)). Qed.
Lemma lem3072324 : True = term108.
Proof. exact (SYM (@lem3072323)). Qed.
Lemma lem3072325 : term108.
Proof. exact (EQ_MP (@lem3072324) (@lem0)). Qed.
Lemma lem3072326 : term147.
Proof. exact (@lem3072315 (@lem3072325)). Qed.
Lemma lem3072328 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072329 : term108 = term115.
Proof. exact (@lem3072328 (NUMERAL 0) term35). Qed.
Lemma lem3072330 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072331 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072332 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072331 h1) (fun h1 : term115 = True => @lem3072330)). Qed.
Lemma lem3072333 : term115 = True.
Proof. exact (EQ_MP (@lem3072332) (@lem3072330)). Qed.
Lemma lem3072334 : term108 = True.
Proof. exact (TRANS (@lem3072329) (@lem3072333)). Qed.
Lemma lem3072335 : True = term108.
Proof. exact (SYM (@lem3072334)). Qed.
Lemma lem3072336 : term108.
Proof. exact (EQ_MP (@lem3072335) (@lem0)). Qed.
Lemma lem3072337 : term148.
Proof. exact (@lem3072326 (@lem3072336)). Qed.
Lemma lem3072339 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072340 : term108 = term115.
Proof. exact (@lem3072339 (NUMERAL 0) term35). Qed.
Lemma lem3072341 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072342 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072343 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072342 h1) (fun h1 : term115 = True => @lem3072341)). Qed.
Lemma lem3072344 : term115 = True.
Proof. exact (EQ_MP (@lem3072343) (@lem3072341)). Qed.
Lemma lem3072345 : term108 = True.
Proof. exact (TRANS (@lem3072340) (@lem3072344)). Qed.
Lemma lem3072346 : True = term108.
Proof. exact (SYM (@lem3072345)). Qed.
Lemma lem3072347 : term108.
Proof. exact (EQ_MP (@lem3072346) (@lem0)). Qed.
Lemma lem3072348 : term149.
Proof. exact (@lem3072337 (@lem3072347)). Qed.
Lemma lem3072350 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3072351 : term74 = term75.
Proof. exact (@lem3072350 term35 term35). Qed.
Lemma lem3072352 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072353 : term77 = term35.
Proof. exact (EQ_MP (@lem3072352) (@lem940073)). Qed.
Lemma lem3072354 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072355 : term75 = term34.
Proof. exact (MK_COMB (@lem3072354) (@lem3072353)). Qed.
Lemma lem3072356 : term74 = term34.
Proof. exact (TRANS (@lem3072351) (@lem3072355)). Qed.
Lemma lem3072358 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3072359 : term69 = term80.
Proof. exact (@lem3072358 term35 term35). Qed.
Lemma lem3072360 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072361 : term77 = term35.
Proof. exact (EQ_MP (@lem3072360) (@lem940073)). Qed.
Lemma lem3072362 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072363 : term75 = term34.
Proof. exact (MK_COMB (@lem3072362) (@lem3072361)). Qed.
Lemma lem3072364 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3072365 : term80 = term61.
Proof. exact (MK_COMB (@lem3072364) (@lem3072363)). Qed.
Lemma lem3072366 : term69 = term61.
Proof. exact (TRANS (@lem3072359) (@lem3072365)). Qed.
Lemma lem3072367 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3072368 : term150 = term142.
Proof. exact (MK_COMB (@lem3072367) (@lem3072366)). Qed.
Lemma lem3072369 : term151 = term144.
Proof. exact (MK_COMB (@lem3072368) (@lem3072356)). Qed.
Lemma lem3072371 (m : nat) : (term152 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3072372 : term144 = term52.
Proof. exact (@lem3072371 term35). Qed.
Lemma lem3072373 : term151 = term52.
Proof. exact (TRANS (@lem3072369) (@lem3072372)). Qed.
Lemma lem3072374 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3072375 : term153 = term154.
Proof. exact (MK_COMB (@lem3072374) (@lem3072373)). Qed.
Lemma lem3072376 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem3072377 : term155 = term120.
Proof. exact (MK_COMB (@lem3072375) (@lem3072376)). Qed.
Lemma lem3072379 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072380 : term120 = term52.
Proof. exact (@lem3072379 term35). Qed.
Lemma lem3072381 : term155 = term52.
Proof. exact (TRANS (@lem3072377) (@lem3072380)). Qed.
Lemma lem3072383 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3072384 : term74 = term75.
Proof. exact (@lem3072383 term35 term35). Qed.
Lemma lem3072385 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072386 : term77 = term35.
Proof. exact (EQ_MP (@lem3072385) (@lem940073)). Qed.
Lemma lem3072387 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072388 : term75 = term34.
Proof. exact (MK_COMB (@lem3072387) (@lem3072386)). Qed.
Lemma lem3072389 : term74 = term34.
Proof. exact (TRANS (@lem3072384) (@lem3072388)). Qed.
Lemma lem3072390 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem3072391 : term156 = term120.
Proof. exact (MK_COMB (@lem3072390) (@lem3072389)). Qed.
Lemma lem3072393 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072394 : term120 = term52.
Proof. exact (@lem3072393 term35). Qed.
Lemma lem3072395 : term156 = term52.
Proof. exact (TRANS (@lem3072391) (@lem3072394)). Qed.
Lemma lem3072396 : term52 = term156.
Proof. exact (SYM (@lem3072395)). Qed.
Lemma lem3072397 : term155 = term156.
Proof. exact (TRANS (@lem3072381) (@lem3072396)). Qed.
Lemma lem3072398 : term145 = term109.
Proof. exact (@lem3072348 (@lem3072397)). Qed.
Lemma lem3072399 : term144 = term109.
Proof. exact (TRANS (@lem3072314) (@lem3072398)). Qed.
Lemma lem3072401 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3072402 : term109 = term52.
Proof. exact (@lem3072401 term52). Qed.
Lemma lem3072403 : term144 = term52.
Proof. exact (TRANS (@lem3072399) (@lem3072402)). Qed.
Lemma lem3072404 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3072405 : term157 = term154.
Proof. exact (MK_COMB (@lem3072404) (@lem3072403)). Qed.
Lemma lem3072406 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem3072407 (n : nat) : (term141 n) = (term119 n).
Proof. exact (MK_COMB (@lem3072405) (@lem3072406 n)). Qed.
Lemma lem3072408 (n : nat) : (term140 n) = (term119 n).
Proof. exact (TRANS (@lem3072305 n) (@lem3072407 n)). Qed.
Lemma lem3072409 (n : nat) : (term119 n) = term52.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem3072410 (n : nat) : (term140 n) = term52.
Proof. exact (TRANS (@lem3072408 n) (@lem3072409 n)). Qed.
Lemma lem3072411 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3072412 (n : nat) : (term158 n) = term159.
Proof. exact (MK_COMB (@lem3072411) (@lem3072410 n)). Qed.
Lemma lem3072413 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3072414 (n : nat) : (term209 n) = term164.
Proof. exact (MK_COMB (@lem3072412 n) (@lem3072413)). Qed.
Lemma lem3072415 (n : nat) : (term208 n) = term164.
Proof. exact (TRANS (@lem3072304 n) (@lem3072414 n)). Qed.
Lemma lem3072416 : term164 = term61.
Proof. exact (@lem1982721 term61). Qed.
Lemma lem3072417 (n : nat) : (term208 n) = term61.
Proof. exact (TRANS (@lem3072415 n) (@lem3072416)). Qed.
Lemma lem3072418 (m : nat) (n : nat) : (term207 m n) = term164.
Proof. exact (MK_COMB (@lem3072303 m) (@lem3072417 n)). Qed.
Lemma lem3072419 (m : nat) (n : nat) : (term206 m n) = term164.
Proof. exact (TRANS (@lem3072195 m n) (@lem3072418 m n)). Qed.
Lemma lem3072420 : term164 = term61.
Proof. exact (@lem1982721 term61). Qed.
Lemma lem3072421 (m : nat) (n : nat) : (term206 m n) = term61.
Proof. exact (TRANS (@lem3072419 m n) (@lem3072420)). Qed.
Lemma lem3072422 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3072423 (m : nat) (n : nat) : (term210 m n) = term166.
Proof. exact (MK_COMB (@lem3072422) (@lem3072421 m n)). Qed.
Lemma lem3072424 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3072425 (m : nat) (n : nat) : (term205 m n) = term167.
Proof. exact (MK_COMB (@lem3072423 m n) (@lem3072424)). Qed.
Lemma lem3072426 (m : nat) (n : nat) (h1 : term180 m n) : term167.
Proof. exact (EQ_MP (@lem3072425 m n) (@lem3072194 m n h1)). Qed.
Lemma lem3072428 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3072429 : term167 = term168.
Proof. exact (@lem3072428 term52 term61). Qed.
Lemma lem3072431 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3072432 : term61 = term66.
Proof. exact (@lem3072431 term35). Qed.
Lemma lem3072434 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3072435 : term52 = term109.
Proof. exact (@lem3072434 (NUMERAL 0)). Qed.
Lemma lem3072436 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3072437 : term169 = term170.
Proof. exact (MK_COMB (@lem3072436) (@lem3072435)). Qed.
Lemma lem3072438 : term168 = term171.
Proof. exact (MK_COMB (@lem3072437) (@lem3072432)). Qed.
Lemma lem3072439 : term172.
Proof. exact (@lem1980026 term52 term34 term61 term34). Qed.
Lemma lem3072441 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072442 : term108 = term115.
Proof. exact (@lem3072441 (NUMERAL 0) term35). Qed.
Lemma lem3072443 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072444 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072445 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072444 h1) (fun h1 : term115 = True => @lem3072443)). Qed.
Lemma lem3072446 : term115 = True.
Proof. exact (EQ_MP (@lem3072445) (@lem3072443)). Qed.
Lemma lem3072447 : term108 = True.
Proof. exact (TRANS (@lem3072442) (@lem3072446)). Qed.
Lemma lem3072448 : True = term108.
Proof. exact (SYM (@lem3072447)). Qed.
Lemma lem3072449 : term108.
Proof. exact (EQ_MP (@lem3072448) (@lem0)). Qed.
Lemma lem3072450 : term173.
Proof. exact (@lem3072439 (@lem3072449)). Qed.
Lemma lem3072452 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072453 : term108 = term115.
Proof. exact (@lem3072452 (NUMERAL 0) term35). Qed.
Lemma lem3072454 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072455 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072456 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072455 h1) (fun h1 : term115 = True => @lem3072454)). Qed.
Lemma lem3072457 : term115 = True.
Proof. exact (EQ_MP (@lem3072456) (@lem3072454)). Qed.
Lemma lem3072458 : term108 = True.
Proof. exact (TRANS (@lem3072453) (@lem3072457)). Qed.
Lemma lem3072459 : True = term108.
Proof. exact (SYM (@lem3072458)). Qed.
Lemma lem3072460 : term108.
Proof. exact (EQ_MP (@lem3072459) (@lem0)). Qed.
Lemma lem3072461 : term171 = term174.
Proof. exact (@lem3072450 (@lem3072460)). Qed.
Lemma lem3072463 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3072464 : term69 = term80.
Proof. exact (@lem3072463 term35 term35). Qed.
Lemma lem3072465 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072466 : term77 = term35.
Proof. exact (EQ_MP (@lem3072465) (@lem940073)). Qed.
Lemma lem3072467 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072468 : term75 = term34.
Proof. exact (MK_COMB (@lem3072467) (@lem3072466)). Qed.
Lemma lem3072469 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3072470 : term80 = term61.
Proof. exact (MK_COMB (@lem3072469) (@lem3072468)). Qed.
Lemma lem3072471 : term69 = term61.
Proof. exact (TRANS (@lem3072464) (@lem3072470)). Qed.
Lemma lem3072473 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072474 : term120 = term52.
Proof. exact (@lem3072473 term35). Qed.
Lemma lem3072475 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3072476 : term175 = term169.
Proof. exact (MK_COMB (@lem3072475) (@lem3072474)). Qed.
Lemma lem3072477 : term174 = term168.
Proof. exact (MK_COMB (@lem3072476) (@lem3072471)). Qed.
Lemma lem3072479 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3072480 : term168 = term178.
Proof. exact (@lem3072479 (NUMERAL 0) term35). Qed.
Lemma lem3072481 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072482 (h1 : term116 = (BIT1 0)) : (term35 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3072483 : (term116 = (BIT1 0)) = ((term35 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072482 h1) (fun h1 : (term35 = (NUMERAL 0)) = False => @lem3072481)). Qed.
Lemma lem3072484 : (term35 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3072483) (@lem3072481)). Qed.
Lemma lem3072485 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3072486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3072487 : term179 = (and True).
Proof. exact (MK_COMB (@lem3072486) (@lem3072485)). Qed.
Lemma lem3072488 : term178 = (True /\ False).
Proof. exact (MK_COMB (@lem3072487) (@lem3072484)). Qed.
Lemma lem3072490 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3072491 : term178 = False.
Proof. exact (TRANS (@lem3072488) (@lem3072490)). Qed.
Lemma lem3072492 : term168 = False.
Proof. exact (TRANS (@lem3072480) (@lem3072491)). Qed.
Lemma lem3072493 : term174 = False.
Proof. exact (TRANS (@lem3072477) (@lem3072492)). Qed.
Lemma lem3072494 : term171 = False.
Proof. exact (TRANS (@lem3072461) (@lem3072493)). Qed.
Lemma lem3072495 : term168 = False.
Proof. exact (TRANS (@lem3072438) (@lem3072494)). Qed.
Lemma lem3072496 : term167 = False.
Proof. exact (TRANS (@lem3072429) (@lem3072495)). Qed.
Lemma lem3072497 (m : nat) (n : nat) (h1 : term180 m n) : False.
Proof. exact (EQ_MP (@lem3072496) (@lem3072426 m n h1)). Qed.
Lemma lem3072498 (m : nat) (n : nat) (h1 : term103 m n) : False.
Proof. exact (or_elim (@lem3071649 m n h1) (fun h0 : term106 m n => @lem3072049 m n h0) (fun h0 : term180 m n => @lem3072497 m n h0)). Qed.
Lemma lem3072499 (m : nat) (n : nat) (h1 : term102 m n) : term102 m n.
Proof. exact (h1). Qed.
Lemma lem3072500 (m : nat) (n : nat) (h1 : term211 m n) : term211 m n.
Proof. exact (h1). Qed.
Lemma lem3072501 (m : nat) (n : nat) (h1 : term211 m n) : (term53 m n) = term52.
Proof. exact (proj2 (@lem3072500 m n h1)). Qed.
Lemma lem3072502 (m : nat) (n : nat) (h1 : term211 m n) : term91 m n.
Proof. exact (proj1 (@lem3072500 m n h1)). Qed.
Lemma lem3072506 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3072507 : term107 = term108.
Proof. exact (@lem3072506 term52 term34). Qed.
Lemma lem3072509 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3072510 : term34 = term63.
Proof. exact (@lem3072509 term35). Qed.
Lemma lem3072512 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3072513 : term52 = term109.
Proof. exact (@lem3072512 (NUMERAL 0)). Qed.
Lemma lem3072514 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3072515 : term110 = term111.
Proof. exact (MK_COMB (@lem3072514) (@lem3072513)). Qed.
Lemma lem3072516 : term108 = term112.
Proof. exact (MK_COMB (@lem3072515) (@lem3072510)). Qed.
Lemma lem3072517 : term113.
Proof. exact (@lem1980255 term52 term34 term34 term34). Qed.
Lemma lem3072519 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072520 : term108 = term115.
Proof. exact (@lem3072519 (NUMERAL 0) term35). Qed.
Lemma lem3072521 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072522 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072523 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072522 h1) (fun h1 : term115 = True => @lem3072521)). Qed.
Lemma lem3072524 : term115 = True.
Proof. exact (EQ_MP (@lem3072523) (@lem3072521)). Qed.
Lemma lem3072525 : term108 = True.
Proof. exact (TRANS (@lem3072520) (@lem3072524)). Qed.
Lemma lem3072526 : True = term108.
Proof. exact (SYM (@lem3072525)). Qed.
Lemma lem3072527 : term108.
Proof. exact (EQ_MP (@lem3072526) (@lem0)). Qed.
Lemma lem3072528 : term117.
Proof. exact (@lem3072517 (@lem3072527)). Qed.
Lemma lem3072530 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072531 : term108 = term115.
Proof. exact (@lem3072530 (NUMERAL 0) term35). Qed.
Lemma lem3072532 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072533 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072534 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072533 h1) (fun h1 : term115 = True => @lem3072532)). Qed.
Lemma lem3072535 : term115 = True.
Proof. exact (EQ_MP (@lem3072534) (@lem3072532)). Qed.
Lemma lem3072536 : term108 = True.
Proof. exact (TRANS (@lem3072531) (@lem3072535)). Qed.
Lemma lem3072537 : True = term108.
Proof. exact (SYM (@lem3072536)). Qed.
Lemma lem3072538 : term108.
Proof. exact (EQ_MP (@lem3072537) (@lem0)). Qed.
Lemma lem3072539 : term112 = term118.
Proof. exact (@lem3072528 (@lem3072538)). Qed.
Lemma lem3072541 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3072542 : term74 = term75.
Proof. exact (@lem3072541 term35 term35). Qed.
Lemma lem3072543 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072544 : term77 = term35.
Proof. exact (EQ_MP (@lem3072543) (@lem940073)). Qed.
Lemma lem3072545 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072546 : term75 = term34.
Proof. exact (MK_COMB (@lem3072545) (@lem3072544)). Qed.
Lemma lem3072547 : term74 = term34.
Proof. exact (TRANS (@lem3072542) (@lem3072546)). Qed.
Lemma lem3072549 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072550 : term120 = term52.
Proof. exact (@lem3072549 term35). Qed.
Lemma lem3072551 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3072552 : term121 = term110.
Proof. exact (MK_COMB (@lem3072551) (@lem3072550)). Qed.
Lemma lem3072553 : term118 = term108.
Proof. exact (MK_COMB (@lem3072552) (@lem3072547)). Qed.
Lemma lem3072555 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072556 : term108 = term115.
Proof. exact (@lem3072555 (NUMERAL 0) term35). Qed.
Lemma lem3072557 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072558 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072559 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072558 h1) (fun h1 : term115 = True => @lem3072557)). Qed.
Lemma lem3072560 : term115 = True.
Proof. exact (EQ_MP (@lem3072559) (@lem3072557)). Qed.
Lemma lem3072561 : term108 = True.
Proof. exact (TRANS (@lem3072556) (@lem3072560)). Qed.
Lemma lem3072562 : term118 = True.
Proof. exact (TRANS (@lem3072553) (@lem3072561)). Qed.
Lemma lem3072563 : term112 = True.
Proof. exact (TRANS (@lem3072539) (@lem3072562)). Qed.
Lemma lem3072564 : term108 = True.
Proof. exact (TRANS (@lem3072516) (@lem3072563)). Qed.
Lemma lem3072565 : term107 = True.
Proof. exact (TRANS (@lem3072507) (@lem3072564)). Qed.
Lemma lem3072566 : True = term107.
Proof. exact (SYM (@lem3072565)). Qed.
Lemma lem3072567 : term107.
Proof. exact (EQ_MP (@lem3072566) (@lem0)). Qed.
Lemma lem3072568 (m : nat) (n : nat) (h1 : term211 m n) : term122 m n.
Proof. exact (conj (@lem3072567) (@lem3072502 m n h1)). Qed.
Lemma lem3072570 (x : real) (y : real) : term123 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3072571 (m : nat) (n : nat) : term124 m n.
Proof. exact (@lem3072570 term34 (term87 m n)). Qed.
Lemma lem3072572 (m : nat) (n : nat) (h1 : term211 m n) : term125 m n.
Proof. exact (@lem3072571 m n (@lem3072568 m n h1)). Qed.
Lemma lem3072573 (m : nat) (n : nat) : (term126 m n) = (term87 m n).
Proof. exact (@lem1982733 (term87 m n)). Qed.
Lemma lem3072574 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3072575 (m : nat) (n : nat) : (term127 m n) = (term90 m n).
Proof. exact (MK_COMB (@lem3072574) (@lem3072573 m n)). Qed.
Lemma lem3072576 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3072577 (m : nat) (n : nat) : (term125 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem3072575 m n) (@lem3072576)). Qed.
Lemma lem3072578 (m : nat) (n : nat) (h1 : term211 m n) : term91 m n.
Proof. exact (EQ_MP (@lem3072577 m n) (@lem3072572 m n h1)). Qed.
Lemma lem3072580 (y : real) : term128 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3072581 (m : nat) (n : nat) : term129 m n.
Proof. exact (@lem3072580 (term53 m n)). Qed.
Lemma lem3072582 (m : nat) (n : nat) (h1 : term211 m n) : term130 m n.
Proof. exact (@lem3072581 m n (@lem3072501 m n h1)). Qed.
Lemma lem3072583 (m : nat) (n : nat) (h1 : term211 m n) : term131 m n.
Proof. exact (@lem3072582 m n h1 term34). Qed.
Lemma lem3072584 (m : nat) (n : nat) : (term131 m n) = ((term132 m n) = term52).
Proof. exact (eq_refl (term131 m n)). Qed.
Lemma lem3072585 (m : nat) (n : nat) (h1 : term211 m n) : (term132 m n) = term52.
Proof. exact (EQ_MP (@lem3072584 m n) (@lem3072583 m n h1)). Qed.
Lemma lem3072586 (m : nat) (n : nat) : (term132 m n) = (term53 m n).
Proof. exact (@lem1982733 (term53 m n)). Qed.
Lemma lem3072587 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3072588 (m : nat) (n : nat) : (term133 m n) = (term55 m n).
Proof. exact (MK_COMB (@lem3072587) (@lem3072586 m n)). Qed.
Lemma lem3072589 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3072590 (m : nat) (n : nat) : ((term132 m n) = term52) = ((term53 m n) = term52).
Proof. exact (MK_COMB (@lem3072588 m n) (@lem3072589)). Qed.
Lemma lem3072591 (m : nat) (n : nat) (h1 : term211 m n) : (term53 m n) = term52.
Proof. exact (EQ_MP (@lem3072590 m n) (@lem3072585 m n h1)). Qed.
Lemma lem3072592 (m : nat) (n : nat) (h1 : term211 m n) : term106 m n.
Proof. exact (conj (@lem3072591 m n h1) (@lem3072578 m n h1)). Qed.
Lemma lem3072594 (x : real) (y : real) : term134 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3072595 (m : nat) (n : nat) : term135 m n.
Proof. exact (@lem3072594 (term53 m n) (term87 m n)). Qed.
Lemma lem3072596 (m : nat) (n : nat) (h1 : term211 m n) : term136 m n.
Proof. exact (@lem3072595 m n (@lem3072592 m n h1)). Qed.
Lemma lem3072597 (m : nat) (n : nat) : (term137 m n) = (term138 m n).
Proof. exact (@lem1982753 (real_of_num m) (term88 m) (term88 n) (term139 n)). Qed.
Lemma lem3072598 (m : nat) : (term140 m) = (term141 m).
Proof. exact (@lem1982715 term61 (real_of_num m)). Qed.
Lemma lem3072600 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3072601 : term34 = term63.
Proof. exact (@lem3072600 term35). Qed.
Lemma lem3072603 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3072604 : term61 = term66.
Proof. exact (@lem3072603 term35). Qed.
Lemma lem3072605 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3072606 : term142 = term143.
Proof. exact (MK_COMB (@lem3072605) (@lem3072604)). Qed.
Lemma lem3072607 : term144 = term145.
Proof. exact (MK_COMB (@lem3072606) (@lem3072601)). Qed.
Lemma lem3072608 : term146.
Proof. exact (@lem1981473 term61 term34 term34 term34 term52 term34). Qed.
Lemma lem3072610 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072611 : term108 = term115.
Proof. exact (@lem3072610 (NUMERAL 0) term35). Qed.
Lemma lem3072612 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072613 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072614 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072613 h1) (fun h1 : term115 = True => @lem3072612)). Qed.
Lemma lem3072615 : term115 = True.
Proof. exact (EQ_MP (@lem3072614) (@lem3072612)). Qed.
Lemma lem3072616 : term108 = True.
Proof. exact (TRANS (@lem3072611) (@lem3072615)). Qed.
Lemma lem3072617 : True = term108.
Proof. exact (SYM (@lem3072616)). Qed.
Lemma lem3072618 : term108.
Proof. exact (EQ_MP (@lem3072617) (@lem0)). Qed.
Lemma lem3072619 : term147.
Proof. exact (@lem3072608 (@lem3072618)). Qed.
Lemma lem3072621 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072622 : term108 = term115.
Proof. exact (@lem3072621 (NUMERAL 0) term35). Qed.
Lemma lem3072623 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072624 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072625 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072624 h1) (fun h1 : term115 = True => @lem3072623)). Qed.
Lemma lem3072626 : term115 = True.
Proof. exact (EQ_MP (@lem3072625) (@lem3072623)). Qed.
Lemma lem3072627 : term108 = True.
Proof. exact (TRANS (@lem3072622) (@lem3072626)). Qed.
Lemma lem3072628 : True = term108.
Proof. exact (SYM (@lem3072627)). Qed.
Lemma lem3072629 : term108.
Proof. exact (EQ_MP (@lem3072628) (@lem0)). Qed.
Lemma lem3072630 : term148.
Proof. exact (@lem3072619 (@lem3072629)). Qed.
Lemma lem3072632 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072633 : term108 = term115.
Proof. exact (@lem3072632 (NUMERAL 0) term35). Qed.
Lemma lem3072634 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072635 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072636 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072635 h1) (fun h1 : term115 = True => @lem3072634)). Qed.
Lemma lem3072637 : term115 = True.
Proof. exact (EQ_MP (@lem3072636) (@lem3072634)). Qed.
Lemma lem3072638 : term108 = True.
Proof. exact (TRANS (@lem3072633) (@lem3072637)). Qed.
Lemma lem3072639 : True = term108.
Proof. exact (SYM (@lem3072638)). Qed.
Lemma lem3072640 : term108.
Proof. exact (EQ_MP (@lem3072639) (@lem0)). Qed.
Lemma lem3072641 : term149.
Proof. exact (@lem3072630 (@lem3072640)). Qed.
Lemma lem3072643 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3072644 : term74 = term75.
Proof. exact (@lem3072643 term35 term35). Qed.
Lemma lem3072645 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072646 : term77 = term35.
Proof. exact (EQ_MP (@lem3072645) (@lem940073)). Qed.
Lemma lem3072647 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072648 : term75 = term34.
Proof. exact (MK_COMB (@lem3072647) (@lem3072646)). Qed.
Lemma lem3072649 : term74 = term34.
Proof. exact (TRANS (@lem3072644) (@lem3072648)). Qed.
Lemma lem3072651 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3072652 : term69 = term80.
Proof. exact (@lem3072651 term35 term35). Qed.
Lemma lem3072653 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072654 : term77 = term35.
Proof. exact (EQ_MP (@lem3072653) (@lem940073)). Qed.
Lemma lem3072655 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072656 : term75 = term34.
Proof. exact (MK_COMB (@lem3072655) (@lem3072654)). Qed.
Lemma lem3072657 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3072658 : term80 = term61.
Proof. exact (MK_COMB (@lem3072657) (@lem3072656)). Qed.
Lemma lem3072659 : term69 = term61.
Proof. exact (TRANS (@lem3072652) (@lem3072658)). Qed.
Lemma lem3072660 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3072661 : term150 = term142.
Proof. exact (MK_COMB (@lem3072660) (@lem3072659)). Qed.
Lemma lem3072662 : term151 = term144.
Proof. exact (MK_COMB (@lem3072661) (@lem3072649)). Qed.
Lemma lem3072664 (m : nat) : (term152 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3072665 : term144 = term52.
Proof. exact (@lem3072664 term35). Qed.
Lemma lem3072666 : term151 = term52.
Proof. exact (TRANS (@lem3072662) (@lem3072665)). Qed.
Lemma lem3072667 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3072668 : term153 = term154.
Proof. exact (MK_COMB (@lem3072667) (@lem3072666)). Qed.
Lemma lem3072669 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem3072670 : term155 = term120.
Proof. exact (MK_COMB (@lem3072668) (@lem3072669)). Qed.
Lemma lem3072672 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072673 : term120 = term52.
Proof. exact (@lem3072672 term35). Qed.
Lemma lem3072674 : term155 = term52.
Proof. exact (TRANS (@lem3072670) (@lem3072673)). Qed.
Lemma lem3072676 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3072677 : term74 = term75.
Proof. exact (@lem3072676 term35 term35). Qed.
Lemma lem3072678 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072679 : term77 = term35.
Proof. exact (EQ_MP (@lem3072678) (@lem940073)). Qed.
Lemma lem3072680 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072681 : term75 = term34.
Proof. exact (MK_COMB (@lem3072680) (@lem3072679)). Qed.
Lemma lem3072682 : term74 = term34.
Proof. exact (TRANS (@lem3072677) (@lem3072681)). Qed.
Lemma lem3072683 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem3072684 : term156 = term120.
Proof. exact (MK_COMB (@lem3072683) (@lem3072682)). Qed.
Lemma lem3072686 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072687 : term120 = term52.
Proof. exact (@lem3072686 term35). Qed.
Lemma lem3072688 : term156 = term52.
Proof. exact (TRANS (@lem3072684) (@lem3072687)). Qed.
Lemma lem3072689 : term52 = term156.
Proof. exact (SYM (@lem3072688)). Qed.
Lemma lem3072690 : term155 = term156.
Proof. exact (TRANS (@lem3072674) (@lem3072689)). Qed.
Lemma lem3072691 : term145 = term109.
Proof. exact (@lem3072641 (@lem3072690)). Qed.
Lemma lem3072692 : term144 = term109.
Proof. exact (TRANS (@lem3072607) (@lem3072691)). Qed.
Lemma lem3072694 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3072695 : term109 = term52.
Proof. exact (@lem3072694 term52). Qed.
Lemma lem3072696 : term144 = term52.
Proof. exact (TRANS (@lem3072692) (@lem3072695)). Qed.
Lemma lem3072697 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3072698 : term157 = term154.
Proof. exact (MK_COMB (@lem3072697) (@lem3072696)). Qed.
Lemma lem3072699 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem3072700 (m : nat) : (term141 m) = (term119 m).
Proof. exact (MK_COMB (@lem3072698) (@lem3072699 m)). Qed.
Lemma lem3072701 (m : nat) : (term140 m) = (term119 m).
Proof. exact (TRANS (@lem3072598 m) (@lem3072700 m)). Qed.
Lemma lem3072702 (m : nat) : (term119 m) = term52.
Proof. exact (@lem1982719 (real_of_num m)). Qed.
Lemma lem3072703 (m : nat) : (term140 m) = term52.
Proof. exact (TRANS (@lem3072701 m) (@lem3072702 m)). Qed.
Lemma lem3072704 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3072705 (m : nat) : (term158 m) = term159.
Proof. exact (MK_COMB (@lem3072704) (@lem3072703 m)). Qed.
Lemma lem3072706 (n : nat) : (term160 n) = (term161 n).
Proof. exact (@lem1982763 (term88 n) (real_of_num n) term61). Qed.
Lemma lem3072707 (n : nat) : (term162 n) = (term141 n).
Proof. exact (@lem1982713 term61 (real_of_num n)). Qed.
Lemma lem3072709 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3072710 : term34 = term63.
Proof. exact (@lem3072709 term35). Qed.
Lemma lem3072712 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3072713 : term61 = term66.
Proof. exact (@lem3072712 term35). Qed.
Lemma lem3072714 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3072715 : term142 = term143.
Proof. exact (MK_COMB (@lem3072714) (@lem3072713)). Qed.
Lemma lem3072716 : term144 = term145.
Proof. exact (MK_COMB (@lem3072715) (@lem3072710)). Qed.
Lemma lem3072717 : term146.
Proof. exact (@lem1981473 term61 term34 term34 term34 term52 term34). Qed.
Lemma lem3072719 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072720 : term108 = term115.
Proof. exact (@lem3072719 (NUMERAL 0) term35). Qed.
Lemma lem3072721 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072722 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072723 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072722 h1) (fun h1 : term115 = True => @lem3072721)). Qed.
Lemma lem3072724 : term115 = True.
Proof. exact (EQ_MP (@lem3072723) (@lem3072721)). Qed.
Lemma lem3072725 : term108 = True.
Proof. exact (TRANS (@lem3072720) (@lem3072724)). Qed.
Lemma lem3072726 : True = term108.
Proof. exact (SYM (@lem3072725)). Qed.
Lemma lem3072727 : term108.
Proof. exact (EQ_MP (@lem3072726) (@lem0)). Qed.
Lemma lem3072728 : term147.
Proof. exact (@lem3072717 (@lem3072727)). Qed.
Lemma lem3072730 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072731 : term108 = term115.
Proof. exact (@lem3072730 (NUMERAL 0) term35). Qed.
Lemma lem3072732 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072733 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072734 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072733 h1) (fun h1 : term115 = True => @lem3072732)). Qed.
Lemma lem3072735 : term115 = True.
Proof. exact (EQ_MP (@lem3072734) (@lem3072732)). Qed.
Lemma lem3072736 : term108 = True.
Proof. exact (TRANS (@lem3072731) (@lem3072735)). Qed.
Lemma lem3072737 : True = term108.
Proof. exact (SYM (@lem3072736)). Qed.
Lemma lem3072738 : term108.
Proof. exact (EQ_MP (@lem3072737) (@lem0)). Qed.
Lemma lem3072739 : term148.
Proof. exact (@lem3072728 (@lem3072738)). Qed.
Lemma lem3072741 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072742 : term108 = term115.
Proof. exact (@lem3072741 (NUMERAL 0) term35). Qed.
Lemma lem3072743 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072744 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072745 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072744 h1) (fun h1 : term115 = True => @lem3072743)). Qed.
Lemma lem3072746 : term115 = True.
Proof. exact (EQ_MP (@lem3072745) (@lem3072743)). Qed.
Lemma lem3072747 : term108 = True.
Proof. exact (TRANS (@lem3072742) (@lem3072746)). Qed.
Lemma lem3072748 : True = term108.
Proof. exact (SYM (@lem3072747)). Qed.
Lemma lem3072749 : term108.
Proof. exact (EQ_MP (@lem3072748) (@lem0)). Qed.
Lemma lem3072750 : term149.
Proof. exact (@lem3072739 (@lem3072749)). Qed.
Lemma lem3072752 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3072753 : term74 = term75.
Proof. exact (@lem3072752 term35 term35). Qed.
Lemma lem3072754 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072755 : term77 = term35.
Proof. exact (EQ_MP (@lem3072754) (@lem940073)). Qed.
Lemma lem3072756 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072757 : term75 = term34.
Proof. exact (MK_COMB (@lem3072756) (@lem3072755)). Qed.
Lemma lem3072758 : term74 = term34.
Proof. exact (TRANS (@lem3072753) (@lem3072757)). Qed.
Lemma lem3072760 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3072761 : term69 = term80.
Proof. exact (@lem3072760 term35 term35). Qed.
Lemma lem3072762 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072763 : term77 = term35.
Proof. exact (EQ_MP (@lem3072762) (@lem940073)). Qed.
Lemma lem3072764 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072765 : term75 = term34.
Proof. exact (MK_COMB (@lem3072764) (@lem3072763)). Qed.
Lemma lem3072766 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3072767 : term80 = term61.
Proof. exact (MK_COMB (@lem3072766) (@lem3072765)). Qed.
Lemma lem3072768 : term69 = term61.
Proof. exact (TRANS (@lem3072761) (@lem3072767)). Qed.
Lemma lem3072769 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3072770 : term150 = term142.
Proof. exact (MK_COMB (@lem3072769) (@lem3072768)). Qed.
Lemma lem3072771 : term151 = term144.
Proof. exact (MK_COMB (@lem3072770) (@lem3072758)). Qed.
Lemma lem3072773 (m : nat) : (term152 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3072774 : term144 = term52.
Proof. exact (@lem3072773 term35). Qed.
Lemma lem3072775 : term151 = term52.
Proof. exact (TRANS (@lem3072771) (@lem3072774)). Qed.
Lemma lem3072776 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3072777 : term153 = term154.
Proof. exact (MK_COMB (@lem3072776) (@lem3072775)). Qed.
Lemma lem3072778 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem3072779 : term155 = term120.
Proof. exact (MK_COMB (@lem3072777) (@lem3072778)). Qed.
Lemma lem3072781 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072782 : term120 = term52.
Proof. exact (@lem3072781 term35). Qed.
Lemma lem3072783 : term155 = term52.
Proof. exact (TRANS (@lem3072779) (@lem3072782)). Qed.
Lemma lem3072785 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3072786 : term74 = term75.
Proof. exact (@lem3072785 term35 term35). Qed.
Lemma lem3072787 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072788 : term77 = term35.
Proof. exact (EQ_MP (@lem3072787) (@lem940073)). Qed.
Lemma lem3072789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072790 : term75 = term34.
Proof. exact (MK_COMB (@lem3072789) (@lem3072788)). Qed.
Lemma lem3072791 : term74 = term34.
Proof. exact (TRANS (@lem3072786) (@lem3072790)). Qed.
Lemma lem3072792 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem3072793 : term156 = term120.
Proof. exact (MK_COMB (@lem3072792) (@lem3072791)). Qed.
Lemma lem3072795 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072796 : term120 = term52.
Proof. exact (@lem3072795 term35). Qed.
Lemma lem3072797 : term156 = term52.
Proof. exact (TRANS (@lem3072793) (@lem3072796)). Qed.
Lemma lem3072798 : term52 = term156.
Proof. exact (SYM (@lem3072797)). Qed.
Lemma lem3072799 : term155 = term156.
Proof. exact (TRANS (@lem3072783) (@lem3072798)). Qed.
Lemma lem3072800 : term145 = term109.
Proof. exact (@lem3072750 (@lem3072799)). Qed.
Lemma lem3072801 : term144 = term109.
Proof. exact (TRANS (@lem3072716) (@lem3072800)). Qed.
Lemma lem3072803 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3072804 : term109 = term52.
Proof. exact (@lem3072803 term52). Qed.
Lemma lem3072805 : term144 = term52.
Proof. exact (TRANS (@lem3072801) (@lem3072804)). Qed.
Lemma lem3072806 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3072807 : term157 = term154.
Proof. exact (MK_COMB (@lem3072806) (@lem3072805)). Qed.
Lemma lem3072808 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem3072809 (n : nat) : (term141 n) = (term119 n).
Proof. exact (MK_COMB (@lem3072807) (@lem3072808 n)). Qed.
Lemma lem3072810 (n : nat) : (term162 n) = (term119 n).
Proof. exact (TRANS (@lem3072707 n) (@lem3072809 n)). Qed.
Lemma lem3072811 (n : nat) : (term119 n) = term52.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem3072812 (n : nat) : (term162 n) = term52.
Proof. exact (TRANS (@lem3072810 n) (@lem3072811 n)). Qed.
Lemma lem3072813 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3072814 (n : nat) : (term163 n) = term159.
Proof. exact (MK_COMB (@lem3072813) (@lem3072812 n)). Qed.
Lemma lem3072815 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3072816 (n : nat) : (term161 n) = term164.
Proof. exact (MK_COMB (@lem3072814 n) (@lem3072815)). Qed.
Lemma lem3072817 (n : nat) : (term160 n) = term164.
Proof. exact (TRANS (@lem3072706 n) (@lem3072816 n)). Qed.
Lemma lem3072818 : term164 = term61.
Proof. exact (@lem1982721 term61). Qed.
Lemma lem3072819 (n : nat) : (term160 n) = term61.
Proof. exact (TRANS (@lem3072817 n) (@lem3072818)). Qed.
Lemma lem3072820 (m : nat) (n : nat) : (term138 m n) = term164.
Proof. exact (MK_COMB (@lem3072705 m) (@lem3072819 n)). Qed.
Lemma lem3072821 (m : nat) (n : nat) : (term137 m n) = term164.
Proof. exact (TRANS (@lem3072597 m n) (@lem3072820 m n)). Qed.
Lemma lem3072822 : term164 = term61.
Proof. exact (@lem1982721 term61). Qed.
Lemma lem3072823 (m : nat) (n : nat) : (term137 m n) = term61.
Proof. exact (TRANS (@lem3072821 m n) (@lem3072822)). Qed.
Lemma lem3072824 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3072825 (m : nat) (n : nat) : (term165 m n) = term166.
Proof. exact (MK_COMB (@lem3072824) (@lem3072823 m n)). Qed.
Lemma lem3072826 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3072827 (m : nat) (n : nat) : (term136 m n) = term167.
Proof. exact (MK_COMB (@lem3072825 m n) (@lem3072826)). Qed.
Lemma lem3072828 (m : nat) (n : nat) (h1 : term211 m n) : term167.
Proof. exact (EQ_MP (@lem3072827 m n) (@lem3072596 m n h1)). Qed.
Lemma lem3072830 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3072831 : term167 = term168.
Proof. exact (@lem3072830 term52 term61). Qed.
Lemma lem3072833 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3072834 : term61 = term66.
Proof. exact (@lem3072833 term35). Qed.
Lemma lem3072836 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3072837 : term52 = term109.
Proof. exact (@lem3072836 (NUMERAL 0)). Qed.
Lemma lem3072838 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3072839 : term169 = term170.
Proof. exact (MK_COMB (@lem3072838) (@lem3072837)). Qed.
Lemma lem3072840 : term168 = term171.
Proof. exact (MK_COMB (@lem3072839) (@lem3072834)). Qed.
Lemma lem3072841 : term172.
Proof. exact (@lem1980026 term52 term34 term61 term34). Qed.
Lemma lem3072843 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072844 : term108 = term115.
Proof. exact (@lem3072843 (NUMERAL 0) term35). Qed.
Lemma lem3072845 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072846 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072847 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072846 h1) (fun h1 : term115 = True => @lem3072845)). Qed.
Lemma lem3072848 : term115 = True.
Proof. exact (EQ_MP (@lem3072847) (@lem3072845)). Qed.
Lemma lem3072849 : term108 = True.
Proof. exact (TRANS (@lem3072844) (@lem3072848)). Qed.
Lemma lem3072850 : True = term108.
Proof. exact (SYM (@lem3072849)). Qed.
Lemma lem3072851 : term108.
Proof. exact (EQ_MP (@lem3072850) (@lem0)). Qed.
Lemma lem3072852 : term173.
Proof. exact (@lem3072841 (@lem3072851)). Qed.
Lemma lem3072854 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072855 : term108 = term115.
Proof. exact (@lem3072854 (NUMERAL 0) term35). Qed.
Lemma lem3072856 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072857 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072858 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072857 h1) (fun h1 : term115 = True => @lem3072856)). Qed.
Lemma lem3072859 : term115 = True.
Proof. exact (EQ_MP (@lem3072858) (@lem3072856)). Qed.
Lemma lem3072860 : term108 = True.
Proof. exact (TRANS (@lem3072855) (@lem3072859)). Qed.
Lemma lem3072861 : True = term108.
Proof. exact (SYM (@lem3072860)). Qed.
Lemma lem3072862 : term108.
Proof. exact (EQ_MP (@lem3072861) (@lem0)). Qed.
Lemma lem3072863 : term171 = term174.
Proof. exact (@lem3072852 (@lem3072862)). Qed.
Lemma lem3072865 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3072866 : term69 = term80.
Proof. exact (@lem3072865 term35 term35). Qed.
Lemma lem3072867 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072868 : term77 = term35.
Proof. exact (EQ_MP (@lem3072867) (@lem940073)). Qed.
Lemma lem3072869 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072870 : term75 = term34.
Proof. exact (MK_COMB (@lem3072869) (@lem3072868)). Qed.
Lemma lem3072871 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3072872 : term80 = term61.
Proof. exact (MK_COMB (@lem3072871) (@lem3072870)). Qed.
Lemma lem3072873 : term69 = term61.
Proof. exact (TRANS (@lem3072866) (@lem3072872)). Qed.
Lemma lem3072875 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072876 : term120 = term52.
Proof. exact (@lem3072875 term35). Qed.
Lemma lem3072877 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3072878 : term175 = term169.
Proof. exact (MK_COMB (@lem3072877) (@lem3072876)). Qed.
Lemma lem3072879 : term174 = term168.
Proof. exact (MK_COMB (@lem3072878) (@lem3072873)). Qed.
Lemma lem3072881 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3072882 : term168 = term178.
Proof. exact (@lem3072881 (NUMERAL 0) term35). Qed.
Lemma lem3072883 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072884 (h1 : term116 = (BIT1 0)) : (term35 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3072885 : (term116 = (BIT1 0)) = ((term35 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072884 h1) (fun h1 : (term35 = (NUMERAL 0)) = False => @lem3072883)). Qed.
Lemma lem3072886 : (term35 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3072885) (@lem3072883)). Qed.
Lemma lem3072887 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3072888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3072889 : term179 = (and True).
Proof. exact (MK_COMB (@lem3072888) (@lem3072887)). Qed.
Lemma lem3072890 : term178 = (True /\ False).
Proof. exact (MK_COMB (@lem3072889) (@lem3072886)). Qed.
Lemma lem3072892 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3072893 : term178 = False.
Proof. exact (TRANS (@lem3072890) (@lem3072892)). Qed.
Lemma lem3072894 : term168 = False.
Proof. exact (TRANS (@lem3072882) (@lem3072893)). Qed.
Lemma lem3072895 : term174 = False.
Proof. exact (TRANS (@lem3072879) (@lem3072894)). Qed.
Lemma lem3072896 : term171 = False.
Proof. exact (TRANS (@lem3072863) (@lem3072895)). Qed.
Lemma lem3072897 : term168 = False.
Proof. exact (TRANS (@lem3072840) (@lem3072896)). Qed.
Lemma lem3072898 : term167 = False.
Proof. exact (TRANS (@lem3072831) (@lem3072897)). Qed.
Lemma lem3072899 (m : nat) (n : nat) (h1 : term211 m n) : False.
Proof. exact (EQ_MP (@lem3072898) (@lem3072828 m n h1)). Qed.
Lemma lem3072900 (m : nat) (n : nat) (h1 : term212 m n) : term212 m n.
Proof. exact (h1). Qed.
Lemma lem3072901 (m : nat) (n : nat) (h1 : term212 m n) : (term53 m n) = term52.
Proof. exact (proj2 (@lem3072900 m n h1)). Qed.
Lemma lem3072902 (m : nat) (n : nat) (h1 : term212 m n) : term93 m n.
Proof. exact (proj1 (@lem3072900 m n h1)). Qed.
Lemma lem3072906 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3072907 : term107 = term108.
Proof. exact (@lem3072906 term52 term34). Qed.
Lemma lem3072909 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3072910 : term34 = term63.
Proof. exact (@lem3072909 term35). Qed.
Lemma lem3072912 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3072913 : term52 = term109.
Proof. exact (@lem3072912 (NUMERAL 0)). Qed.
Lemma lem3072914 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3072915 : term110 = term111.
Proof. exact (MK_COMB (@lem3072914) (@lem3072913)). Qed.
Lemma lem3072916 : term108 = term112.
Proof. exact (MK_COMB (@lem3072915) (@lem3072910)). Qed.
Lemma lem3072917 : term113.
Proof. exact (@lem1980255 term52 term34 term34 term34). Qed.
Lemma lem3072919 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072920 : term108 = term115.
Proof. exact (@lem3072919 (NUMERAL 0) term35). Qed.
Lemma lem3072921 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072922 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072923 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072922 h1) (fun h1 : term115 = True => @lem3072921)). Qed.
Lemma lem3072924 : term115 = True.
Proof. exact (EQ_MP (@lem3072923) (@lem3072921)). Qed.
Lemma lem3072925 : term108 = True.
Proof. exact (TRANS (@lem3072920) (@lem3072924)). Qed.
Lemma lem3072926 : True = term108.
Proof. exact (SYM (@lem3072925)). Qed.
Lemma lem3072927 : term108.
Proof. exact (EQ_MP (@lem3072926) (@lem0)). Qed.
Lemma lem3072928 : term117.
Proof. exact (@lem3072917 (@lem3072927)). Qed.
Lemma lem3072930 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072931 : term108 = term115.
Proof. exact (@lem3072930 (NUMERAL 0) term35). Qed.
Lemma lem3072932 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072933 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072934 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072933 h1) (fun h1 : term115 = True => @lem3072932)). Qed.
Lemma lem3072935 : term115 = True.
Proof. exact (EQ_MP (@lem3072934) (@lem3072932)). Qed.
Lemma lem3072936 : term108 = True.
Proof. exact (TRANS (@lem3072931) (@lem3072935)). Qed.
Lemma lem3072937 : True = term108.
Proof. exact (SYM (@lem3072936)). Qed.
Lemma lem3072938 : term108.
Proof. exact (EQ_MP (@lem3072937) (@lem0)). Qed.
Lemma lem3072939 : term112 = term118.
Proof. exact (@lem3072928 (@lem3072938)). Qed.
Lemma lem3072941 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3072942 : term74 = term75.
Proof. exact (@lem3072941 term35 term35). Qed.
Lemma lem3072943 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3072944 : term77 = term35.
Proof. exact (EQ_MP (@lem3072943) (@lem940073)). Qed.
Lemma lem3072945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3072946 : term75 = term34.
Proof. exact (MK_COMB (@lem3072945) (@lem3072944)). Qed.
Lemma lem3072947 : term74 = term34.
Proof. exact (TRANS (@lem3072942) (@lem3072946)). Qed.
Lemma lem3072949 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3072950 : term120 = term52.
Proof. exact (@lem3072949 term35). Qed.
Lemma lem3072951 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3072952 : term121 = term110.
Proof. exact (MK_COMB (@lem3072951) (@lem3072950)). Qed.
Lemma lem3072953 : term118 = term108.
Proof. exact (MK_COMB (@lem3072952) (@lem3072947)). Qed.
Lemma lem3072955 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3072956 : term108 = term115.
Proof. exact (@lem3072955 (NUMERAL 0) term35). Qed.
Lemma lem3072957 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3072958 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3072959 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3072958 h1) (fun h1 : term115 = True => @lem3072957)). Qed.
Lemma lem3072960 : term115 = True.
Proof. exact (EQ_MP (@lem3072959) (@lem3072957)). Qed.
Lemma lem3072961 : term108 = True.
Proof. exact (TRANS (@lem3072956) (@lem3072960)). Qed.
Lemma lem3072962 : term118 = True.
Proof. exact (TRANS (@lem3072953) (@lem3072961)). Qed.
Lemma lem3072963 : term112 = True.
Proof. exact (TRANS (@lem3072939) (@lem3072962)). Qed.
Lemma lem3072964 : term108 = True.
Proof. exact (TRANS (@lem3072916) (@lem3072963)). Qed.
Lemma lem3072965 : term107 = True.
Proof. exact (TRANS (@lem3072907) (@lem3072964)). Qed.
Lemma lem3072966 : True = term107.
Proof. exact (SYM (@lem3072965)). Qed.
Lemma lem3072967 : term107.
Proof. exact (EQ_MP (@lem3072966) (@lem0)). Qed.
Lemma lem3072968 (m : nat) (n : nat) (h1 : term212 m n) : term181 m n.
Proof. exact (conj (@lem3072967) (@lem3072902 m n h1)). Qed.
Lemma lem3072970 (x : real) (y : real) : term123 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3072971 (m : nat) (n : nat) : term182 m n.
Proof. exact (@lem3072970 term34 (term86 m n)). Qed.
Lemma lem3072972 (m : nat) (n : nat) (h1 : term212 m n) : term183 m n.
Proof. exact (@lem3072971 m n (@lem3072968 m n h1)). Qed.
Lemma lem3072973 (m : nat) (n : nat) : (term184 m n) = (term86 m n).
Proof. exact (@lem1982733 (term86 m n)). Qed.
Lemma lem3072974 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3072975 (m : nat) (n : nat) : (term185 m n) = (term92 m n).
Proof. exact (MK_COMB (@lem3072974) (@lem3072973 m n)). Qed.
Lemma lem3072976 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3072977 (m : nat) (n : nat) : (term183 m n) = (term93 m n).
Proof. exact (MK_COMB (@lem3072975 m n) (@lem3072976)). Qed.
Lemma lem3072978 (m : nat) (n : nat) (h1 : term212 m n) : term93 m n.
Proof. exact (EQ_MP (@lem3072977 m n) (@lem3072972 m n h1)). Qed.
Lemma lem3072980 (y : real) : term128 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3072981 (m : nat) (n : nat) : term129 m n.
Proof. exact (@lem3072980 (term53 m n)). Qed.
Lemma lem3072982 (m : nat) (n : nat) (h1 : term212 m n) : term130 m n.
Proof. exact (@lem3072981 m n (@lem3072901 m n h1)). Qed.
Lemma lem3072983 (m : nat) (n : nat) (h1 : term212 m n) : term186 m n.
Proof. exact (@lem3072982 m n h1 term61). Qed.
Lemma lem3072984 (m : nat) (n : nat) : (term186 m n) = ((term187 m n) = term52).
Proof. exact (eq_refl (term186 m n)). Qed.
Lemma lem3072985 (m : nat) (n : nat) (h1 : term212 m n) : (term187 m n) = term52.
Proof. exact (EQ_MP (@lem3072984 m n) (@lem3072983 m n h1)). Qed.
Lemma lem3072986 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (@lem1982781 (real_of_num m) term61 (term88 n)). Qed.
Lemma lem3072987 (n : nat) : (term189 n) = (term190 n).
Proof. exact (@lem1982749 term61 term61 (real_of_num n)). Qed.
Lemma lem3072989 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3072990 : term61 = term66.
Proof. exact (@lem3072989 term35). Qed.
Lemma lem3072992 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3072993 : term61 = term66.
Proof. exact (@lem3072992 term35). Qed.
Lemma lem3072994 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3072995 : term67 = term68.
Proof. exact (MK_COMB (@lem3072994) (@lem3072993)). Qed.
Lemma lem3072996 : term191 = term192.
Proof. exact (MK_COMB (@lem3072995) (@lem3072990)). Qed.
Lemma lem3072997 : term192 = term193.
Proof. exact (@lem1981613 term61 term61 term34 term34). Qed.
Lemma lem3072999 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3073000 : term74 = term75.
Proof. exact (@lem3072999 term35 term35). Qed.
Lemma lem3073001 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3073002 : term77 = term35.
Proof. exact (EQ_MP (@lem3073001) (@lem940073)). Qed.
Lemma lem3073003 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3073004 : term75 = term34.
Proof. exact (MK_COMB (@lem3073003) (@lem3073002)). Qed.
Lemma lem3073005 : term74 = term34.
Proof. exact (TRANS (@lem3073000) (@lem3073004)). Qed.
Lemma lem3073007 (m : nat) (n : nat) : (term194 m n) = (term73 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem3073008 : term191 = term75.
Proof. exact (@lem3073007 term35 term35). Qed.
Lemma lem3073009 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3073010 : term77 = term35.
Proof. exact (EQ_MP (@lem3073009) (@lem940073)). Qed.
Lemma lem3073011 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3073012 : term75 = term34.
Proof. exact (MK_COMB (@lem3073011) (@lem3073010)). Qed.
Lemma lem3073013 : term191 = term34.
Proof. exact (TRANS (@lem3073008) (@lem3073012)). Qed.
Lemma lem3073014 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3073015 : term195 = term196.
Proof. exact (MK_COMB (@lem3073014) (@lem3073013)). Qed.
Lemma lem3073016 : term193 = term63.
Proof. exact (MK_COMB (@lem3073015) (@lem3073005)). Qed.
Lemma lem3073017 : term192 = term63.
Proof. exact (TRANS (@lem3072997) (@lem3073016)). Qed.
Lemma lem3073018 : term191 = term63.
Proof. exact (TRANS (@lem3072996) (@lem3073017)). Qed.
Lemma lem3073020 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3073021 : term63 = term34.
Proof. exact (@lem3073020 term34). Qed.
Lemma lem3073022 : term191 = term34.
Proof. exact (TRANS (@lem3073018) (@lem3073021)). Qed.
Lemma lem3073023 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3073024 : term197 = term198.
Proof. exact (MK_COMB (@lem3073023) (@lem3073022)). Qed.
Lemma lem3073025 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem3073026 (n : nat) : (term190 n) = (term199 n).
Proof. exact (MK_COMB (@lem3073024) (@lem3073025 n)). Qed.
Lemma lem3073027 (n : nat) : (term189 n) = (term199 n).
Proof. exact (TRANS (@lem3072987 n) (@lem3073026 n)). Qed.
Lemma lem3073028 (n : nat) : (term199 n) = (real_of_num n).
Proof. exact (@lem1982709 (real_of_num n)). Qed.
Lemma lem3073029 (n : nat) : (term189 n) = (real_of_num n).
Proof. exact (TRANS (@lem3073027 n) (@lem3073028 n)). Qed.
Lemma lem3073032 (m : nat) : (term84 m) = (term84 m).
Proof. exact (eq_refl (term84 m)). Qed.
Lemma lem3073033 (m : nat) (n : nat) : (term188 m n) = (term200 m n).
Proof. exact (MK_COMB (@lem3073032 m) (@lem3073029 n)). Qed.
Lemma lem3073034 (m : nat) (n : nat) : (term187 m n) = (term200 m n).
Proof. exact (TRANS (@lem3072986 m n) (@lem3073033 m n)). Qed.
Lemma lem3073035 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3073036 (m : nat) (n : nat) : (term201 m n) = (term202 m n).
Proof. exact (MK_COMB (@lem3073035) (@lem3073034 m n)). Qed.
Lemma lem3073037 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3073038 (m : nat) (n : nat) : ((term187 m n) = term52) = ((term200 m n) = term52).
Proof. exact (MK_COMB (@lem3073036 m n) (@lem3073037)). Qed.
Lemma lem3073039 (m : nat) (n : nat) (h1 : term212 m n) : (term200 m n) = term52.
Proof. exact (EQ_MP (@lem3073038 m n) (@lem3072985 m n h1)). Qed.
Lemma lem3073040 (m : nat) (n : nat) (h1 : term212 m n) : term203 m n.
Proof. exact (conj (@lem3073039 m n h1) (@lem3072978 m n h1)). Qed.
Lemma lem3073042 (x : real) (y : real) : term134 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3073043 (m : nat) (n : nat) : term204 m n.
Proof. exact (@lem3073042 (term200 m n) (term86 m n)). Qed.
Lemma lem3073044 (m : nat) (n : nat) (h1 : term212 m n) : term205 m n.
Proof. exact (@lem3073043 m n (@lem3073040 m n h1)). Qed.
Lemma lem3073045 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (@lem1982753 (term88 m) (real_of_num m) (real_of_num n) (term85 n)). Qed.
Lemma lem3073046 (m : nat) : (term162 m) = (term141 m).
Proof. exact (@lem1982713 term61 (real_of_num m)). Qed.
Lemma lem3073048 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3073049 : term34 = term63.
Proof. exact (@lem3073048 term35). Qed.
Lemma lem3073051 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3073052 : term61 = term66.
Proof. exact (@lem3073051 term35). Qed.
Lemma lem3073053 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3073054 : term142 = term143.
Proof. exact (MK_COMB (@lem3073053) (@lem3073052)). Qed.
Lemma lem3073055 : term144 = term145.
Proof. exact (MK_COMB (@lem3073054) (@lem3073049)). Qed.
Lemma lem3073056 : term146.
Proof. exact (@lem1981473 term61 term34 term34 term34 term52 term34). Qed.
Lemma lem3073058 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3073059 : term108 = term115.
Proof. exact (@lem3073058 (NUMERAL 0) term35). Qed.
Lemma lem3073060 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3073061 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3073062 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3073061 h1) (fun h1 : term115 = True => @lem3073060)). Qed.
Lemma lem3073063 : term115 = True.
Proof. exact (EQ_MP (@lem3073062) (@lem3073060)). Qed.
Lemma lem3073064 : term108 = True.
Proof. exact (TRANS (@lem3073059) (@lem3073063)). Qed.
Lemma lem3073065 : True = term108.
Proof. exact (SYM (@lem3073064)). Qed.
Lemma lem3073066 : term108.
Proof. exact (EQ_MP (@lem3073065) (@lem0)). Qed.
Lemma lem3073067 : term147.
Proof. exact (@lem3073056 (@lem3073066)). Qed.
Lemma lem3073069 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3073070 : term108 = term115.
Proof. exact (@lem3073069 (NUMERAL 0) term35). Qed.
Lemma lem3073071 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3073072 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3073073 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3073072 h1) (fun h1 : term115 = True => @lem3073071)). Qed.
Lemma lem3073074 : term115 = True.
Proof. exact (EQ_MP (@lem3073073) (@lem3073071)). Qed.
Lemma lem3073075 : term108 = True.
Proof. exact (TRANS (@lem3073070) (@lem3073074)). Qed.
Lemma lem3073076 : True = term108.
Proof. exact (SYM (@lem3073075)). Qed.
Lemma lem3073077 : term108.
Proof. exact (EQ_MP (@lem3073076) (@lem0)). Qed.
Lemma lem3073078 : term148.
Proof. exact (@lem3073067 (@lem3073077)). Qed.
Lemma lem3073080 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3073081 : term108 = term115.
Proof. exact (@lem3073080 (NUMERAL 0) term35). Qed.
Lemma lem3073082 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3073083 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3073084 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3073083 h1) (fun h1 : term115 = True => @lem3073082)). Qed.
Lemma lem3073085 : term115 = True.
Proof. exact (EQ_MP (@lem3073084) (@lem3073082)). Qed.
Lemma lem3073086 : term108 = True.
Proof. exact (TRANS (@lem3073081) (@lem3073085)). Qed.
Lemma lem3073087 : True = term108.
Proof. exact (SYM (@lem3073086)). Qed.
Lemma lem3073088 : term108.
Proof. exact (EQ_MP (@lem3073087) (@lem0)). Qed.
Lemma lem3073089 : term149.
Proof. exact (@lem3073078 (@lem3073088)). Qed.
Lemma lem3073091 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3073092 : term74 = term75.
Proof. exact (@lem3073091 term35 term35). Qed.
Lemma lem3073093 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3073094 : term77 = term35.
Proof. exact (EQ_MP (@lem3073093) (@lem940073)). Qed.
Lemma lem3073095 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3073096 : term75 = term34.
Proof. exact (MK_COMB (@lem3073095) (@lem3073094)). Qed.
Lemma lem3073097 : term74 = term34.
Proof. exact (TRANS (@lem3073092) (@lem3073096)). Qed.
Lemma lem3073099 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3073100 : term69 = term80.
Proof. exact (@lem3073099 term35 term35). Qed.
Lemma lem3073101 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3073102 : term77 = term35.
Proof. exact (EQ_MP (@lem3073101) (@lem940073)). Qed.
Lemma lem3073103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3073104 : term75 = term34.
Proof. exact (MK_COMB (@lem3073103) (@lem3073102)). Qed.
Lemma lem3073105 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3073106 : term80 = term61.
Proof. exact (MK_COMB (@lem3073105) (@lem3073104)). Qed.
Lemma lem3073107 : term69 = term61.
Proof. exact (TRANS (@lem3073100) (@lem3073106)). Qed.
Lemma lem3073108 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3073109 : term150 = term142.
Proof. exact (MK_COMB (@lem3073108) (@lem3073107)). Qed.
Lemma lem3073110 : term151 = term144.
Proof. exact (MK_COMB (@lem3073109) (@lem3073097)). Qed.
Lemma lem3073112 (m : nat) : (term152 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3073113 : term144 = term52.
Proof. exact (@lem3073112 term35). Qed.
Lemma lem3073114 : term151 = term52.
Proof. exact (TRANS (@lem3073110) (@lem3073113)). Qed.
Lemma lem3073115 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3073116 : term153 = term154.
Proof. exact (MK_COMB (@lem3073115) (@lem3073114)). Qed.
Lemma lem3073117 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem3073118 : term155 = term120.
Proof. exact (MK_COMB (@lem3073116) (@lem3073117)). Qed.
Lemma lem3073120 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3073121 : term120 = term52.
Proof. exact (@lem3073120 term35). Qed.
Lemma lem3073122 : term155 = term52.
Proof. exact (TRANS (@lem3073118) (@lem3073121)). Qed.
Lemma lem3073124 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3073125 : term74 = term75.
Proof. exact (@lem3073124 term35 term35). Qed.
Lemma lem3073126 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3073127 : term77 = term35.
Proof. exact (EQ_MP (@lem3073126) (@lem940073)). Qed.
Lemma lem3073128 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3073129 : term75 = term34.
Proof. exact (MK_COMB (@lem3073128) (@lem3073127)). Qed.
Lemma lem3073130 : term74 = term34.
Proof. exact (TRANS (@lem3073125) (@lem3073129)). Qed.
Lemma lem3073131 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem3073132 : term156 = term120.
Proof. exact (MK_COMB (@lem3073131) (@lem3073130)). Qed.
Lemma lem3073134 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3073135 : term120 = term52.
Proof. exact (@lem3073134 term35). Qed.
Lemma lem3073136 : term156 = term52.
Proof. exact (TRANS (@lem3073132) (@lem3073135)). Qed.
Lemma lem3073137 : term52 = term156.
Proof. exact (SYM (@lem3073136)). Qed.
Lemma lem3073138 : term155 = term156.
Proof. exact (TRANS (@lem3073122) (@lem3073137)). Qed.
Lemma lem3073139 : term145 = term109.
Proof. exact (@lem3073089 (@lem3073138)). Qed.
Lemma lem3073140 : term144 = term109.
Proof. exact (TRANS (@lem3073055) (@lem3073139)). Qed.
Lemma lem3073142 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3073143 : term109 = term52.
Proof. exact (@lem3073142 term52). Qed.
Lemma lem3073144 : term144 = term52.
Proof. exact (TRANS (@lem3073140) (@lem3073143)). Qed.
Lemma lem3073145 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3073146 : term157 = term154.
Proof. exact (MK_COMB (@lem3073145) (@lem3073144)). Qed.
Lemma lem3073147 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem3073148 (m : nat) : (term141 m) = (term119 m).
Proof. exact (MK_COMB (@lem3073146) (@lem3073147 m)). Qed.
Lemma lem3073149 (m : nat) : (term162 m) = (term119 m).
Proof. exact (TRANS (@lem3073046 m) (@lem3073148 m)). Qed.
Lemma lem3073150 (m : nat) : (term119 m) = term52.
Proof. exact (@lem1982719 (real_of_num m)). Qed.
Lemma lem3073151 (m : nat) : (term162 m) = term52.
Proof. exact (TRANS (@lem3073149 m) (@lem3073150 m)). Qed.
Lemma lem3073152 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3073153 (m : nat) : (term163 m) = term159.
Proof. exact (MK_COMB (@lem3073152) (@lem3073151 m)). Qed.
Lemma lem3073154 (n : nat) : (term208 n) = (term209 n).
Proof. exact (@lem1982763 (real_of_num n) (term88 n) term61). Qed.
Lemma lem3073155 (n : nat) : (term140 n) = (term141 n).
Proof. exact (@lem1982715 term61 (real_of_num n)). Qed.
Lemma lem3073157 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3073158 : term34 = term63.
Proof. exact (@lem3073157 term35). Qed.
Lemma lem3073160 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3073161 : term61 = term66.
Proof. exact (@lem3073160 term35). Qed.
Lemma lem3073162 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3073163 : term142 = term143.
Proof. exact (MK_COMB (@lem3073162) (@lem3073161)). Qed.
Lemma lem3073164 : term144 = term145.
Proof. exact (MK_COMB (@lem3073163) (@lem3073158)). Qed.
Lemma lem3073165 : term146.
Proof. exact (@lem1981473 term61 term34 term34 term34 term52 term34). Qed.
Lemma lem3073167 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3073168 : term108 = term115.
Proof. exact (@lem3073167 (NUMERAL 0) term35). Qed.
Lemma lem3073169 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3073170 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3073171 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3073170 h1) (fun h1 : term115 = True => @lem3073169)). Qed.
Lemma lem3073172 : term115 = True.
Proof. exact (EQ_MP (@lem3073171) (@lem3073169)). Qed.
Lemma lem3073173 : term108 = True.
Proof. exact (TRANS (@lem3073168) (@lem3073172)). Qed.
Lemma lem3073174 : True = term108.
Proof. exact (SYM (@lem3073173)). Qed.
Lemma lem3073175 : term108.
Proof. exact (EQ_MP (@lem3073174) (@lem0)). Qed.
Lemma lem3073176 : term147.
Proof. exact (@lem3073165 (@lem3073175)). Qed.
Lemma lem3073178 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3073179 : term108 = term115.
Proof. exact (@lem3073178 (NUMERAL 0) term35). Qed.
Lemma lem3073180 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3073181 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3073182 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3073181 h1) (fun h1 : term115 = True => @lem3073180)). Qed.
Lemma lem3073183 : term115 = True.
Proof. exact (EQ_MP (@lem3073182) (@lem3073180)). Qed.
Lemma lem3073184 : term108 = True.
Proof. exact (TRANS (@lem3073179) (@lem3073183)). Qed.
Lemma lem3073185 : True = term108.
Proof. exact (SYM (@lem3073184)). Qed.
Lemma lem3073186 : term108.
Proof. exact (EQ_MP (@lem3073185) (@lem0)). Qed.
Lemma lem3073187 : term148.
Proof. exact (@lem3073176 (@lem3073186)). Qed.
Lemma lem3073189 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3073190 : term108 = term115.
Proof. exact (@lem3073189 (NUMERAL 0) term35). Qed.
Lemma lem3073191 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3073192 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3073193 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3073192 h1) (fun h1 : term115 = True => @lem3073191)). Qed.
Lemma lem3073194 : term115 = True.
Proof. exact (EQ_MP (@lem3073193) (@lem3073191)). Qed.
Lemma lem3073195 : term108 = True.
Proof. exact (TRANS (@lem3073190) (@lem3073194)). Qed.
Lemma lem3073196 : True = term108.
Proof. exact (SYM (@lem3073195)). Qed.
Lemma lem3073197 : term108.
Proof. exact (EQ_MP (@lem3073196) (@lem0)). Qed.
Lemma lem3073198 : term149.
Proof. exact (@lem3073187 (@lem3073197)). Qed.
Lemma lem3073200 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3073201 : term74 = term75.
Proof. exact (@lem3073200 term35 term35). Qed.
Lemma lem3073202 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3073203 : term77 = term35.
Proof. exact (EQ_MP (@lem3073202) (@lem940073)). Qed.
Lemma lem3073204 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3073205 : term75 = term34.
Proof. exact (MK_COMB (@lem3073204) (@lem3073203)). Qed.
Lemma lem3073206 : term74 = term34.
Proof. exact (TRANS (@lem3073201) (@lem3073205)). Qed.
Lemma lem3073208 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3073209 : term69 = term80.
Proof. exact (@lem3073208 term35 term35). Qed.
Lemma lem3073210 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3073211 : term77 = term35.
Proof. exact (EQ_MP (@lem3073210) (@lem940073)). Qed.
Lemma lem3073212 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3073213 : term75 = term34.
Proof. exact (MK_COMB (@lem3073212) (@lem3073211)). Qed.
Lemma lem3073214 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3073215 : term80 = term61.
Proof. exact (MK_COMB (@lem3073214) (@lem3073213)). Qed.
Lemma lem3073216 : term69 = term61.
Proof. exact (TRANS (@lem3073209) (@lem3073215)). Qed.
Lemma lem3073217 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3073218 : term150 = term142.
Proof. exact (MK_COMB (@lem3073217) (@lem3073216)). Qed.
Lemma lem3073219 : term151 = term144.
Proof. exact (MK_COMB (@lem3073218) (@lem3073206)). Qed.
Lemma lem3073221 (m : nat) : (term152 m) = term52.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3073222 : term144 = term52.
Proof. exact (@lem3073221 term35). Qed.
Lemma lem3073223 : term151 = term52.
Proof. exact (TRANS (@lem3073219) (@lem3073222)). Qed.
Lemma lem3073224 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3073225 : term153 = term154.
Proof. exact (MK_COMB (@lem3073224) (@lem3073223)). Qed.
Lemma lem3073226 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem3073227 : term155 = term120.
Proof. exact (MK_COMB (@lem3073225) (@lem3073226)). Qed.
Lemma lem3073229 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3073230 : term120 = term52.
Proof. exact (@lem3073229 term35). Qed.
Lemma lem3073231 : term155 = term52.
Proof. exact (TRANS (@lem3073227) (@lem3073230)). Qed.
Lemma lem3073233 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3073234 : term74 = term75.
Proof. exact (@lem3073233 term35 term35). Qed.
Lemma lem3073235 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3073236 : term77 = term35.
Proof. exact (EQ_MP (@lem3073235) (@lem940073)). Qed.
Lemma lem3073237 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3073238 : term75 = term34.
Proof. exact (MK_COMB (@lem3073237) (@lem3073236)). Qed.
Lemma lem3073239 : term74 = term34.
Proof. exact (TRANS (@lem3073234) (@lem3073238)). Qed.
Lemma lem3073240 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem3073241 : term156 = term120.
Proof. exact (MK_COMB (@lem3073240) (@lem3073239)). Qed.
Lemma lem3073243 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3073244 : term120 = term52.
Proof. exact (@lem3073243 term35). Qed.
Lemma lem3073245 : term156 = term52.
Proof. exact (TRANS (@lem3073241) (@lem3073244)). Qed.
Lemma lem3073246 : term52 = term156.
Proof. exact (SYM (@lem3073245)). Qed.
Lemma lem3073247 : term155 = term156.
Proof. exact (TRANS (@lem3073231) (@lem3073246)). Qed.
Lemma lem3073248 : term145 = term109.
Proof. exact (@lem3073198 (@lem3073247)). Qed.
Lemma lem3073249 : term144 = term109.
Proof. exact (TRANS (@lem3073164) (@lem3073248)). Qed.
Lemma lem3073251 (x : real) : (term83 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3073252 : term109 = term52.
Proof. exact (@lem3073251 term52). Qed.
Lemma lem3073253 : term144 = term52.
Proof. exact (TRANS (@lem3073249) (@lem3073252)). Qed.
Lemma lem3073254 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3073255 : term157 = term154.
Proof. exact (MK_COMB (@lem3073254) (@lem3073253)). Qed.
Lemma lem3073256 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem3073257 (n : nat) : (term141 n) = (term119 n).
Proof. exact (MK_COMB (@lem3073255) (@lem3073256 n)). Qed.
Lemma lem3073258 (n : nat) : (term140 n) = (term119 n).
Proof. exact (TRANS (@lem3073155 n) (@lem3073257 n)). Qed.
Lemma lem3073259 (n : nat) : (term119 n) = term52.
Proof. exact (@lem1982719 (real_of_num n)). Qed.
Lemma lem3073260 (n : nat) : (term140 n) = term52.
Proof. exact (TRANS (@lem3073258 n) (@lem3073259 n)). Qed.
Lemma lem3073261 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3073262 (n : nat) : (term158 n) = term159.
Proof. exact (MK_COMB (@lem3073261) (@lem3073260 n)). Qed.
Lemma lem3073263 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem3073264 (n : nat) : (term209 n) = term164.
Proof. exact (MK_COMB (@lem3073262 n) (@lem3073263)). Qed.
Lemma lem3073265 (n : nat) : (term208 n) = term164.
Proof. exact (TRANS (@lem3073154 n) (@lem3073264 n)). Qed.
Lemma lem3073266 : term164 = term61.
Proof. exact (@lem1982721 term61). Qed.
Lemma lem3073267 (n : nat) : (term208 n) = term61.
Proof. exact (TRANS (@lem3073265 n) (@lem3073266)). Qed.
Lemma lem3073268 (m : nat) (n : nat) : (term207 m n) = term164.
Proof. exact (MK_COMB (@lem3073153 m) (@lem3073267 n)). Qed.
Lemma lem3073269 (m : nat) (n : nat) : (term206 m n) = term164.
Proof. exact (TRANS (@lem3073045 m n) (@lem3073268 m n)). Qed.
Lemma lem3073270 : term164 = term61.
Proof. exact (@lem1982721 term61). Qed.
Lemma lem3073271 (m : nat) (n : nat) : (term206 m n) = term61.
Proof. exact (TRANS (@lem3073269 m n) (@lem3073270)). Qed.
Lemma lem3073272 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3073273 (m : nat) (n : nat) : (term210 m n) = term166.
Proof. exact (MK_COMB (@lem3073272) (@lem3073271 m n)). Qed.
Lemma lem3073274 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem3073275 (m : nat) (n : nat) : (term205 m n) = term167.
Proof. exact (MK_COMB (@lem3073273 m n) (@lem3073274)). Qed.
Lemma lem3073276 (m : nat) (n : nat) (h1 : term212 m n) : term167.
Proof. exact (EQ_MP (@lem3073275 m n) (@lem3073044 m n h1)). Qed.
Lemma lem3073278 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3073279 : term167 = term168.
Proof. exact (@lem3073278 term52 term61). Qed.
Lemma lem3073281 (x : nat) : (term64 x) = (term65 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3073282 : term61 = term66.
Proof. exact (@lem3073281 term35). Qed.
Lemma lem3073284 (x : nat) : (real_of_num x) = (term62 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3073285 : term52 = term109.
Proof. exact (@lem3073284 (NUMERAL 0)). Qed.
Lemma lem3073286 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3073287 : term169 = term170.
Proof. exact (MK_COMB (@lem3073286) (@lem3073285)). Qed.
Lemma lem3073288 : term168 = term171.
Proof. exact (MK_COMB (@lem3073287) (@lem3073282)). Qed.
Lemma lem3073289 : term172.
Proof. exact (@lem1980026 term52 term34 term61 term34). Qed.
Lemma lem3073291 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3073292 : term108 = term115.
Proof. exact (@lem3073291 (NUMERAL 0) term35). Qed.
Lemma lem3073293 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3073294 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3073295 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3073294 h1) (fun h1 : term115 = True => @lem3073293)). Qed.
Lemma lem3073296 : term115 = True.
Proof. exact (EQ_MP (@lem3073295) (@lem3073293)). Qed.
Lemma lem3073297 : term108 = True.
Proof. exact (TRANS (@lem3073292) (@lem3073296)). Qed.
Lemma lem3073298 : True = term108.
Proof. exact (SYM (@lem3073297)). Qed.
Lemma lem3073299 : term108.
Proof. exact (EQ_MP (@lem3073298) (@lem0)). Qed.
Lemma lem3073300 : term173.
Proof. exact (@lem3073289 (@lem3073299)). Qed.
Lemma lem3073302 (m : nat) (n : nat) : (term114 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3073303 : term108 = term115.
Proof. exact (@lem3073302 (NUMERAL 0) term35). Qed.
Lemma lem3073304 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3073305 (h1 : term116 = (BIT1 0)) : term115 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3073306 : (term116 = (BIT1 0)) = (term115 = True).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3073305 h1) (fun h1 : term115 = True => @lem3073304)). Qed.
Lemma lem3073307 : term115 = True.
Proof. exact (EQ_MP (@lem3073306) (@lem3073304)). Qed.
Lemma lem3073308 : term108 = True.
Proof. exact (TRANS (@lem3073303) (@lem3073307)). Qed.
Lemma lem3073309 : True = term108.
Proof. exact (SYM (@lem3073308)). Qed.
Lemma lem3073310 : term108.
Proof. exact (EQ_MP (@lem3073309) (@lem0)). Qed.
Lemma lem3073311 : term171 = term174.
Proof. exact (@lem3073300 (@lem3073310)). Qed.
Lemma lem3073313 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3073314 : term69 = term80.
Proof. exact (@lem3073313 term35 term35). Qed.
Lemma lem3073315 : (term76 = (BIT1 0)) = (term77 = term35).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3073316 : term77 = term35.
Proof. exact (EQ_MP (@lem3073315) (@lem940073)). Qed.
Lemma lem3073317 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3073318 : term75 = term34.
Proof. exact (MK_COMB (@lem3073317) (@lem3073316)). Qed.
Lemma lem3073319 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3073320 : term80 = term61.
Proof. exact (MK_COMB (@lem3073319) (@lem3073318)). Qed.
Lemma lem3073321 : term69 = term61.
Proof. exact (TRANS (@lem3073314) (@lem3073320)). Qed.
Lemma lem3073323 (x : nat) : (term119 x) = term52.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3073324 : term120 = term52.
Proof. exact (@lem3073323 term35). Qed.
Lemma lem3073325 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3073326 : term175 = term169.
Proof. exact (MK_COMB (@lem3073325) (@lem3073324)). Qed.
Lemma lem3073327 : term174 = term168.
Proof. exact (MK_COMB (@lem3073326) (@lem3073321)). Qed.
Lemma lem3073329 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3073330 : term168 = term178.
Proof. exact (@lem3073329 (NUMERAL 0) term35). Qed.
Lemma lem3073331 : term116 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3073332 (h1 : term116 = (BIT1 0)) : (term35 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3073333 : (term116 = (BIT1 0)) = ((term35 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term116 = (BIT1 0) => @lem3073332 h1) (fun h1 : (term35 = (NUMERAL 0)) = False => @lem3073331)). Qed.
Lemma lem3073334 : (term35 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3073333) (@lem3073331)). Qed.
Lemma lem3073335 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3073336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3073337 : term179 = (and True).
Proof. exact (MK_COMB (@lem3073336) (@lem3073335)). Qed.
Lemma lem3073338 : term178 = (True /\ False).
Proof. exact (MK_COMB (@lem3073337) (@lem3073334)). Qed.
Lemma lem3073340 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3073341 : term178 = False.
Proof. exact (TRANS (@lem3073338) (@lem3073340)). Qed.
Lemma lem3073342 : term168 = False.
Proof. exact (TRANS (@lem3073330) (@lem3073341)). Qed.
Lemma lem3073343 : term174 = False.
Proof. exact (TRANS (@lem3073327) (@lem3073342)). Qed.
Lemma lem3073344 : term171 = False.
Proof. exact (TRANS (@lem3073311) (@lem3073343)). Qed.
Lemma lem3073345 : term168 = False.
Proof. exact (TRANS (@lem3073288) (@lem3073344)). Qed.
Lemma lem3073346 : term167 = False.
Proof. exact (TRANS (@lem3073279) (@lem3073345)). Qed.
Lemma lem3073347 (m : nat) (n : nat) (h1 : term212 m n) : False.
Proof. exact (EQ_MP (@lem3073346) (@lem3073276 m n h1)). Qed.
Lemma lem3073348 (m : nat) (n : nat) (h1 : term102 m n) : False.
Proof. exact (or_elim (@lem3072499 m n h1) (fun h0 : term211 m n => @lem3072899 m n h0) (fun h0 : term212 m n => @lem3073347 m n h0)). Qed.
Lemma lem3073349 (m : nat) (n : nat) (h1 : term105 m n) : False.
Proof. exact (or_elim (@lem3071648 m n h1) (fun h0 : term103 m n => @lem3072498 m n h0) (fun h0 : term102 m n => @lem3073348 m n h0)). Qed.
Lemma lem3073351 (m : nat) (n : nat) (h1 : term105 m n) : term105 m n.
Proof. exact (h1). Qed.
Lemma lem3073352 (m : nat) (n : nat) (h1 : term105 m n) : (term105 m n) = False.
Proof. exact (prop_ext (fun h2 : term105 m n => @lem3073349 m n h1) (fun h2 : False => @lem3073351 m n h1)). Qed.
Lemma lem3073353 (m : nat) (n : nat) (h1 : term105 m n) : False.
Proof. exact (EQ_MP (@lem3073352 m n h1) (@lem3073351 m n h1)). Qed.
Lemma lem3073354 (m : nat) (n : nat) (h1 : term50 m n) : term50 m n.
Proof. exact (h1). Qed.
Lemma lem3073355 (m : nat) (n : nat) (h1 : term50 m n) : term105 m n.
Proof. exact (EQ_MP (@lem3071626 m n) (@lem3073354 m n h1)). Qed.
Lemma lem3073356 (m : nat) (n : nat) (h1 : term50 m n) : (term105 m n) = False.
Proof. exact (prop_ext (fun h2 : term105 m n => @lem3073353 m n h2) (fun h2 : False => @lem3073355 m n h1)). Qed.
Lemma lem3073357 (m : nat) (n : nat) (h1 : term50 m n) : False.
Proof. exact (EQ_MP (@lem3073356 m n h1) (@lem3073355 m n h1)). Qed.
Lemma lem3073358 (m : nat) (n : nat) : term213 m n.
Proof. exact (fun h0 : term50 m n => @lem3073357 m n h0). Qed.
Lemma lem3073359 (m : nat) (n : nat) : term214 m n.
Proof. exact (@lem1386578 (term215 m n)). Qed.
Lemma lem3073362 (m : nat) (n : nat) : term215 m n.
Proof. exact (@lem3073359 m n (@lem3073358 m n)). Qed.
Lemma lem3073363 (m : nat) (n : nat) : (term48 m n) = (term0 m n).
Proof. exact (SYM (@lem3071192 m n)). Qed.
Lemma lem3073364 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3073365 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (MK_COMB (@lem3073364) (@lem3073363 m n)). Qed.
Lemma lem3073366 (m : nat) (n : nat) : term216 m n.
Proof. exact (EQ_MP (@lem3073365 m n) (@lem3073362 m n)). Qed.
