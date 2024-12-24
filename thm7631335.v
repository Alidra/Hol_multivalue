Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7631335_term_abbrevs.
Require Import DIMINDEX_GE_1_spec.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import LE_REFL_spec.
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
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1842_spec.
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
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Require Import thm940073_spec.
Lemma lem7630044 (a : nat) (b : nat) : (term0 a b) = (term1 a b).
Proof. exact (@lem17265 (term2 a) (term3 a b)). Qed.
Lemma lem7630046 (m : nat) (n : nat) : (Peano.le m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7630047 (a : nat) : (term2 a) = (term5 a).
Proof. exact (@lem7630046 term6 a). Qed.
Lemma lem7630048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7630049 (a : nat) : (term7 a) = (term8 a).
Proof. exact (MK_COMB (@lem7630048) (@lem7630047 a)). Qed.
Lemma lem7630050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7630051 (a : nat) : (term9 a) = (term10 a).
Proof. exact (MK_COMB (@lem7630050) (@lem7630049 a)). Qed.
Lemma lem7630053 (m : nat) (n : nat) : (Peano.le m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7630054 (a : nat) (b : nat) : (term3 a b) = (term11 a b).
Proof. exact (@lem7630053 term6 (Nat.add a b)). Qed.
Lemma lem7630056 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7630057 (a : nat) (b : nat) : (term12 a b) = (term13 a b).
Proof. exact (@lem7630056 a b). Qed.
Lemma lem7630058 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem7630059 (a : nat) (b : nat) : (term11 a b) = (term15 a b).
Proof. exact (MK_COMB (@lem7630058) (@lem7630057 a b)). Qed.
Lemma lem7630060 (a : nat) (b : nat) : (term3 a b) = (term15 a b).
Proof. exact (TRANS (@lem7630054 a b) (@lem7630059 a b)). Qed.
Lemma lem7630061 (a : nat) (b : nat) : (term1 a b) = (term16 a b).
Proof. exact (MK_COMB (@lem7630051 a) (@lem7630060 a b)). Qed.
Lemma lem7630062 (a : nat) (b : nat) : (term0 a b) = (term16 a b).
Proof. exact (TRANS (@lem7630044 a b) (@lem7630061 a b)). Qed.
Lemma lem7630063 (a : nat) : term17 a.
Proof. exact (@lem2307535 a). Qed.
Lemma lem7630064 (a : nat) : (term17 a) = (term18 a).
Proof. exact (eq_refl (term17 a)). Qed.
Lemma lem7630065 (a : nat) : term18 a.
Proof. exact (EQ_MP (@lem7630064 a) (@lem7630063 a)). Qed.
Lemma lem7630066 (b : nat) : term17 b.
Proof. exact (@lem2307535 b). Qed.
Lemma lem7630067 (b : nat) : (term17 b) = (term18 b).
Proof. exact (eq_refl (term17 b)). Qed.
Lemma lem7630068 (b : nat) : term18 b.
Proof. exact (EQ_MP (@lem7630067 b) (@lem7630066 b)). Qed.
Lemma lem7630069 (_98352 : int) (_98353 : int) : (term19 _98352 _98353) = (term20 _98352 _98353).
Proof. exact (@lem2318604 (term20 _98352 _98353)). Qed.
Lemma lem7630085 (_98352 : int) : (term21 _98352) = (term22 _98352).
Proof. exact (@lem16933 (term22 _98352)). Qed.
Lemma lem7630086 (_98352 : int) (_98353 : int) : (term23 _98352 _98353) = (term23 _98352 _98353).
Proof. exact (eq_refl (term23 _98352 _98353)). Qed.
Lemma lem7630087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7630088 (_98352 : int) : (term24 _98352) = (term25 _98352).
Proof. exact (MK_COMB (@lem7630087) (@lem7630085 _98352)). Qed.
Lemma lem7630089 (_98352 : int) (_98353 : int) : (term26 _98352 _98353) = (term27 _98352 _98353).
Proof. exact (MK_COMB (@lem7630088 _98352) (@lem7630086 _98352 _98353)). Qed.
Lemma lem7630090 (_98352 : int) (_98353 : int) : (term28 _98352 _98353) = (term26 _98352 _98353).
Proof. exact (@lem17160 (term29 _98352) (term30 _98352 _98353)). Qed.
Lemma lem7630091 (_98352 : int) (_98353 : int) : (term28 _98352 _98353) = (term27 _98352 _98353).
Proof. exact (TRANS (@lem7630090 _98352 _98353) (@lem7630089 _98352 _98353)). Qed.
Lemma lem7630093 (_98353 : int) : (term31 _98353) = (term31 _98353).
Proof. exact (eq_refl (term31 _98353)). Qed.
Lemma lem7630094 (_98352 : int) (_98353 : int) : (term32 _98352 _98353) = (term33 _98352 _98353).
Proof. exact (MK_COMB (@lem7630093 _98353) (@lem7630091 _98352 _98353)). Qed.
Lemma lem7630095 (_98352 : int) (_98353 : int) : (term34 _98352 _98353) = (term32 _98352 _98353).
Proof. exact (@lem17362 (term35 _98353) (term36 _98352 _98353)). Qed.
Lemma lem7630096 (_98352 : int) (_98353 : int) : (term34 _98352 _98353) = (term33 _98352 _98353).
Proof. exact (TRANS (@lem7630095 _98352 _98353) (@lem7630094 _98352 _98353)). Qed.
Lemma lem7630098 (_98352 : int) : (term31 _98352) = (term31 _98352).
Proof. exact (eq_refl (term31 _98352)). Qed.
Lemma lem7630099 (_98352 : int) (_98353 : int) : (term37 _98352 _98353) = (term38 _98352 _98353).
Proof. exact (MK_COMB (@lem7630098 _98352) (@lem7630096 _98352 _98353)). Qed.
Lemma lem7630100 (_98352 : int) (_98353 : int) : (term39 _98352 _98353) = (term37 _98352 _98353).
Proof. exact (@lem17362 (term35 _98352) (term40 _98352 _98353)). Qed.
Lemma lem7630118 (_98352 : int) (_98353 : int) : (term39 _98352 _98353) = (term38 _98352 _98353).
Proof. exact (TRANS (@lem7630100 _98352 _98353) (@lem7630099 _98352 _98353)). Qed.
Lemma lem7630121 (x : int) (y : int) : (int_le x y) = (term41 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7630122 (_98352 : int) : (term35 _98352) = (term42 _98352).
Proof. exact (@lem7630121 term43 _98352). Qed.
Lemma lem7630124 (n : nat) : (term44 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7630125 : term45 = term46.
Proof. exact (@lem7630124 (NUMERAL 0)). Qed.
Lemma lem7630126 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7630127 : term47 = term48.
Proof. exact (MK_COMB (@lem7630126) (@lem7630125)). Qed.
Lemma lem7630128 (_98352 : int) : (real_of_int _98352) = (real_of_int _98352).
Proof. exact (eq_refl (real_of_int _98352)). Qed.
Lemma lem7630129 (_98352 : int) : (term42 _98352) = (term49 _98352).
Proof. exact (MK_COMB (@lem7630127) (@lem7630128 _98352)). Qed.
Lemma lem7630131 (_98352 : int) : (term35 _98352) = (term49 _98352).
Proof. exact (TRANS (@lem7630122 _98352) (@lem7630129 _98352)). Qed.
Lemma lem7630134 (x : int) (y : int) : (int_le x y) = (term41 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7630135 (_98353 : int) : (term35 _98353) = (term42 _98353).
Proof. exact (@lem7630134 term43 _98353). Qed.
Lemma lem7630137 (n : nat) : (term44 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7630138 : term45 = term46.
Proof. exact (@lem7630137 (NUMERAL 0)). Qed.
Lemma lem7630139 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7630140 : term47 = term48.
Proof. exact (MK_COMB (@lem7630139) (@lem7630138)). Qed.
Lemma lem7630141 (_98353 : int) : (real_of_int _98353) = (real_of_int _98353).
Proof. exact (eq_refl (real_of_int _98353)). Qed.
Lemma lem7630142 (_98353 : int) : (term42 _98353) = (term49 _98353).
Proof. exact (MK_COMB (@lem7630140) (@lem7630141 _98353)). Qed.
Lemma lem7630144 (_98353 : int) : (term35 _98353) = (term49 _98353).
Proof. exact (TRANS (@lem7630135 _98353) (@lem7630142 _98353)). Qed.
Lemma lem7630147 (x : int) (y : int) : (int_le x y) = (term41 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7630148 (_98352 : int) : (term22 _98352) = (term50 _98352).
Proof. exact (@lem7630147 term51 _98352). Qed.
Lemma lem7630150 (n : nat) : (term44 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7630151 : term52 = term53.
Proof. exact (@lem7630150 term6). Qed.
Lemma lem7630152 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7630153 : term54 = term55.
Proof. exact (MK_COMB (@lem7630152) (@lem7630151)). Qed.
Lemma lem7630154 (_98352 : int) : (real_of_int _98352) = (real_of_int _98352).
Proof. exact (eq_refl (real_of_int _98352)). Qed.
Lemma lem7630155 (_98352 : int) : (term50 _98352) = (term56 _98352).
Proof. exact (MK_COMB (@lem7630153) (@lem7630154 _98352)). Qed.
Lemma lem7630157 (_98352 : int) : (term22 _98352) = (term56 _98352).
Proof. exact (TRANS (@lem7630148 _98352) (@lem7630155 _98352)). Qed.
Lemma lem7630159 (y : int) (x : int) : (term57 x y) = (term58 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7630160 (_98352 : int) (_98353 : int) : (term23 _98352 _98353) = (term59 _98352 _98353).
Proof. exact (@lem7630159 (int_add _98352 _98353) term51). Qed.
Lemma lem7630162 (x : int) (y : int) : (int_le x y) = (term41 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7630163 (_98352 : int) (_98353 : int) : (term59 _98352 _98353) = (term60 _98352 _98353).
Proof. exact (@lem7630162 (term61 _98352 _98353) term51). Qed.
Lemma lem7630165 (x : int) (y : int) : (term62 x y) = (term63 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7630166 (_98352 : int) (_98353 : int) : (term64 _98352 _98353) = (term65 _98352 _98353).
Proof. exact (@lem7630165 (int_add _98352 _98353) term51). Qed.
Lemma lem7630168 (x : int) (y : int) : (term62 x y) = (term63 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7630169 (_98352 : int) (_98353 : int) : (term62 _98352 _98353) = (term63 _98352 _98353).
Proof. exact (@lem7630168 _98352 _98353). Qed.
Lemma lem7630170 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7630171 (_98352 : int) (_98353 : int) : (term66 _98352 _98353) = (term67 _98352 _98353).
Proof. exact (MK_COMB (@lem7630170) (@lem7630169 _98352 _98353)). Qed.
Lemma lem7630173 (n : nat) : (term44 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7630174 : term52 = term53.
Proof. exact (@lem7630173 term6). Qed.
Lemma lem7630175 (_98352 : int) (_98353 : int) : (term65 _98352 _98353) = (term68 _98352 _98353).
Proof. exact (MK_COMB (@lem7630171 _98352 _98353) (@lem7630174)). Qed.
Lemma lem7630176 (_98352 : int) (_98353 : int) : (term64 _98352 _98353) = (term68 _98352 _98353).
Proof. exact (TRANS (@lem7630166 _98352 _98353) (@lem7630175 _98352 _98353)). Qed.
Lemma lem7630177 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7630178 (_98352 : int) (_98353 : int) : (term69 _98352 _98353) = (term70 _98352 _98353).
Proof. exact (MK_COMB (@lem7630177) (@lem7630176 _98352 _98353)). Qed.
Lemma lem7630180 (n : nat) : (term44 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7630181 : term52 = term53.
Proof. exact (@lem7630180 term6). Qed.
Lemma lem7630182 (_98352 : int) (_98353 : int) : (term60 _98352 _98353) = (term71 _98352 _98353).
Proof. exact (MK_COMB (@lem7630178 _98352 _98353) (@lem7630181)). Qed.
Lemma lem7630183 (_98352 : int) (_98353 : int) : (term59 _98352 _98353) = (term71 _98352 _98353).
Proof. exact (TRANS (@lem7630163 _98352 _98353) (@lem7630182 _98352 _98353)). Qed.
Lemma lem7630184 (_98352 : int) (_98353 : int) : (term23 _98352 _98353) = (term71 _98352 _98353).
Proof. exact (TRANS (@lem7630160 _98352 _98353) (@lem7630183 _98352 _98353)). Qed.
Lemma lem7630185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7630186 (_98352 : int) : (term25 _98352) = (term72 _98352).
Proof. exact (MK_COMB (@lem7630185) (@lem7630157 _98352)). Qed.
Lemma lem7630187 (_98352 : int) (_98353 : int) : (term27 _98352 _98353) = (term73 _98352 _98353).
Proof. exact (MK_COMB (@lem7630186 _98352) (@lem7630184 _98352 _98353)). Qed.
Lemma lem7630188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7630189 (_98353 : int) : (term31 _98353) = (term74 _98353).
Proof. exact (MK_COMB (@lem7630188) (@lem7630144 _98353)). Qed.
Lemma lem7630190 (_98352 : int) (_98353 : int) : (term33 _98352 _98353) = (term75 _98352 _98353).
Proof. exact (MK_COMB (@lem7630189 _98353) (@lem7630187 _98352 _98353)). Qed.
Lemma lem7630191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7630192 (_98352 : int) : (term31 _98352) = (term74 _98352).
Proof. exact (MK_COMB (@lem7630191) (@lem7630131 _98352)). Qed.
Lemma lem7630193 (_98352 : int) (_98353 : int) : (term38 _98352 _98353) = (term76 _98352 _98353).
Proof. exact (MK_COMB (@lem7630192 _98352) (@lem7630190 _98352 _98353)). Qed.
Lemma lem7630194 (_98352 : int) (_98353 : int) : (term39 _98352 _98353) = (term76 _98352 _98353).
Proof. exact (TRANS (@lem7630118 _98352 _98353) (@lem7630193 _98352 _98353)). Qed.
Lemma lem7630198 (t : Prop) : (term77 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7630234 (_98352 : int) (_98353 : int) : (term78 _98352 _98353) = (term76 _98352 _98353).
Proof. exact (@lem7630198 (term76 _98352 _98353)). Qed.
Lemma lem7630235 (_98352 : int) : (term49 _98352) = (term79 _98352).
Proof. exact (@lem1988287 (real_of_int _98352) term46). Qed.
Lemma lem7630241 (_98352 : int) : (term80 _98352) = (term81 _98352).
Proof. exact (@lem1982792 (real_of_int _98352) term46). Qed.
Lemma lem7630243 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630244 : term46 = term83.
Proof. exact (@lem7630243 (NUMERAL 0)). Qed.
Lemma lem7630246 (x : nat) : (term84 x) = (term85 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7630247 : term86 = term87.
Proof. exact (@lem7630246 term6). Qed.
Lemma lem7630248 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7630249 : term88 = term89.
Proof. exact (MK_COMB (@lem7630248) (@lem7630247)). Qed.
Lemma lem7630250 : term90 = term91.
Proof. exact (MK_COMB (@lem7630249) (@lem7630244)). Qed.
Lemma lem7630251 : term91 = term92.
Proof. exact (@lem1981613 term86 term46 term53 term53). Qed.
Lemma lem7630253 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7630254 : term95 = term96.
Proof. exact (@lem7630253 term6 term6). Qed.
Lemma lem7630255 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630256 : term98 = term6.
Proof. exact (EQ_MP (@lem7630255) (@lem940073)). Qed.
Lemma lem7630257 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630258 : term96 = term53.
Proof. exact (MK_COMB (@lem7630257) (@lem7630256)). Qed.
Lemma lem7630259 : term95 = term53.
Proof. exact (TRANS (@lem7630254) (@lem7630258)). Qed.
Lemma lem7630261 (x : nat) : (term99 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7630262 : term90 = term46.
Proof. exact (@lem7630261 term6). Qed.
Lemma lem7630263 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7630264 : term100 = term101.
Proof. exact (MK_COMB (@lem7630263) (@lem7630262)). Qed.
Lemma lem7630265 : term92 = term83.
Proof. exact (MK_COMB (@lem7630264) (@lem7630259)). Qed.
Lemma lem7630266 : term91 = term83.
Proof. exact (TRANS (@lem7630251) (@lem7630265)). Qed.
Lemma lem7630267 : term90 = term83.
Proof. exact (TRANS (@lem7630250) (@lem7630266)). Qed.
Lemma lem7630269 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7630270 : term83 = term46.
Proof. exact (@lem7630269 term46). Qed.
Lemma lem7630271 : term90 = term46.
Proof. exact (TRANS (@lem7630267) (@lem7630270)). Qed.
Lemma lem7630272 (_98352 : int) : (term103 _98352) = (term103 _98352).
Proof. exact (eq_refl (term103 _98352)). Qed.
Lemma lem7630273 (_98352 : int) : (term81 _98352) = (term104 _98352).
Proof. exact (MK_COMB (@lem7630272 _98352) (@lem7630271)). Qed.
Lemma lem7630274 (_98352 : int) : (term104 _98352) = (real_of_int _98352).
Proof. exact (@lem1982723 (real_of_int _98352)). Qed.
Lemma lem7630275 (_98352 : int) : (term81 _98352) = (real_of_int _98352).
Proof. exact (TRANS (@lem7630273 _98352) (@lem7630274 _98352)). Qed.
Lemma lem7630277 (_98352 : int) : (term80 _98352) = (real_of_int _98352).
Proof. exact (TRANS (@lem7630241 _98352) (@lem7630275 _98352)). Qed.
Lemma lem7630278 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7630279 (_98352 : int) : (term105 _98352) = (term106 _98352).
Proof. exact (MK_COMB (@lem7630278) (@lem7630277 _98352)). Qed.
Lemma lem7630280 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7630281 (_98352 : int) : (term79 _98352) = (term107 _98352).
Proof. exact (MK_COMB (@lem7630279 _98352) (@lem7630280)). Qed.
Lemma lem7630282 (_98352 : int) : (term49 _98352) = (term107 _98352).
Proof. exact (TRANS (@lem7630235 _98352) (@lem7630281 _98352)). Qed.
Lemma lem7630283 (_98353 : int) : (term49 _98353) = (term79 _98353).
Proof. exact (@lem1988287 (real_of_int _98353) term46). Qed.
Lemma lem7630289 (_98353 : int) : (term80 _98353) = (term81 _98353).
Proof. exact (@lem1982792 (real_of_int _98353) term46). Qed.
Lemma lem7630291 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630292 : term46 = term83.
Proof. exact (@lem7630291 (NUMERAL 0)). Qed.
Lemma lem7630294 (x : nat) : (term84 x) = (term85 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7630295 : term86 = term87.
Proof. exact (@lem7630294 term6). Qed.
Lemma lem7630296 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7630297 : term88 = term89.
Proof. exact (MK_COMB (@lem7630296) (@lem7630295)). Qed.
Lemma lem7630298 : term90 = term91.
Proof. exact (MK_COMB (@lem7630297) (@lem7630292)). Qed.
Lemma lem7630299 : term91 = term92.
Proof. exact (@lem1981613 term86 term46 term53 term53). Qed.
Lemma lem7630301 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7630302 : term95 = term96.
Proof. exact (@lem7630301 term6 term6). Qed.
Lemma lem7630303 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630304 : term98 = term6.
Proof. exact (EQ_MP (@lem7630303) (@lem940073)). Qed.
Lemma lem7630305 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630306 : term96 = term53.
Proof. exact (MK_COMB (@lem7630305) (@lem7630304)). Qed.
Lemma lem7630307 : term95 = term53.
Proof. exact (TRANS (@lem7630302) (@lem7630306)). Qed.
Lemma lem7630309 (x : nat) : (term99 x) = term46.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7630310 : term90 = term46.
Proof. exact (@lem7630309 term6). Qed.
Lemma lem7630311 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7630312 : term100 = term101.
Proof. exact (MK_COMB (@lem7630311) (@lem7630310)). Qed.
Lemma lem7630313 : term92 = term83.
Proof. exact (MK_COMB (@lem7630312) (@lem7630307)). Qed.
Lemma lem7630314 : term91 = term83.
Proof. exact (TRANS (@lem7630299) (@lem7630313)). Qed.
Lemma lem7630315 : term90 = term83.
Proof. exact (TRANS (@lem7630298) (@lem7630314)). Qed.
Lemma lem7630317 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7630318 : term83 = term46.
Proof. exact (@lem7630317 term46). Qed.
Lemma lem7630319 : term90 = term46.
Proof. exact (TRANS (@lem7630315) (@lem7630318)). Qed.
Lemma lem7630320 (_98353 : int) : (term103 _98353) = (term103 _98353).
Proof. exact (eq_refl (term103 _98353)). Qed.
Lemma lem7630321 (_98353 : int) : (term81 _98353) = (term104 _98353).
Proof. exact (MK_COMB (@lem7630320 _98353) (@lem7630319)). Qed.
Lemma lem7630322 (_98353 : int) : (term104 _98353) = (real_of_int _98353).
Proof. exact (@lem1982723 (real_of_int _98353)). Qed.
Lemma lem7630323 (_98353 : int) : (term81 _98353) = (real_of_int _98353).
Proof. exact (TRANS (@lem7630321 _98353) (@lem7630322 _98353)). Qed.
Lemma lem7630325 (_98353 : int) : (term80 _98353) = (real_of_int _98353).
Proof. exact (TRANS (@lem7630289 _98353) (@lem7630323 _98353)). Qed.
Lemma lem7630326 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7630327 (_98353 : int) : (term105 _98353) = (term106 _98353).
Proof. exact (MK_COMB (@lem7630326) (@lem7630325 _98353)). Qed.
Lemma lem7630328 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7630329 (_98353 : int) : (term79 _98353) = (term107 _98353).
Proof. exact (MK_COMB (@lem7630327 _98353) (@lem7630328)). Qed.
Lemma lem7630330 (_98353 : int) : (term49 _98353) = (term107 _98353).
Proof. exact (TRANS (@lem7630283 _98353) (@lem7630329 _98353)). Qed.
Lemma lem7630331 (_98352 : int) : (term56 _98352) = (term108 _98352).
Proof. exact (@lem1988287 (real_of_int _98352) term53). Qed.
Lemma lem7630337 (_98352 : int) : (term109 _98352) = (term110 _98352).
Proof. exact (@lem1982792 (real_of_int _98352) term53). Qed.
Lemma lem7630339 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630340 : term53 = term111.
Proof. exact (@lem7630339 term6). Qed.
Lemma lem7630342 (x : nat) : (term84 x) = (term85 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7630343 : term86 = term87.
Proof. exact (@lem7630342 term6). Qed.
Lemma lem7630344 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7630345 : term88 = term89.
Proof. exact (MK_COMB (@lem7630344) (@lem7630343)). Qed.
Lemma lem7630346 : term112 = term113.
Proof. exact (MK_COMB (@lem7630345) (@lem7630340)). Qed.
Lemma lem7630347 : term113 = term114.
Proof. exact (@lem1981613 term86 term53 term53 term53). Qed.
Lemma lem7630349 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7630350 : term95 = term96.
Proof. exact (@lem7630349 term6 term6). Qed.
Lemma lem7630351 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630352 : term98 = term6.
Proof. exact (EQ_MP (@lem7630351) (@lem940073)). Qed.
Lemma lem7630353 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630354 : term96 = term53.
Proof. exact (MK_COMB (@lem7630353) (@lem7630352)). Qed.
Lemma lem7630355 : term95 = term53.
Proof. exact (TRANS (@lem7630350) (@lem7630354)). Qed.
Lemma lem7630357 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7630358 : term112 = term117.
Proof. exact (@lem7630357 term6 term6). Qed.
Lemma lem7630359 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630360 : term98 = term6.
Proof. exact (EQ_MP (@lem7630359) (@lem940073)). Qed.
Lemma lem7630361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630362 : term96 = term53.
Proof. exact (MK_COMB (@lem7630361) (@lem7630360)). Qed.
Lemma lem7630363 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7630364 : term117 = term86.
Proof. exact (MK_COMB (@lem7630363) (@lem7630362)). Qed.
Lemma lem7630365 : term112 = term86.
Proof. exact (TRANS (@lem7630358) (@lem7630364)). Qed.
Lemma lem7630366 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7630367 : term118 = term119.
Proof. exact (MK_COMB (@lem7630366) (@lem7630365)). Qed.
Lemma lem7630368 : term114 = term87.
Proof. exact (MK_COMB (@lem7630367) (@lem7630355)). Qed.
Lemma lem7630369 : term113 = term87.
Proof. exact (TRANS (@lem7630347) (@lem7630368)). Qed.
Lemma lem7630370 : term112 = term87.
Proof. exact (TRANS (@lem7630346) (@lem7630369)). Qed.
Lemma lem7630372 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7630373 : term87 = term86.
Proof. exact (@lem7630372 term86). Qed.
Lemma lem7630374 : term112 = term86.
Proof. exact (TRANS (@lem7630370) (@lem7630373)). Qed.
Lemma lem7630375 (_98352 : int) : (term103 _98352) = (term103 _98352).
Proof. exact (eq_refl (term103 _98352)). Qed.
Lemma lem7630378 (_98352 : int) : (term110 _98352) = (term120 _98352).
Proof. exact (MK_COMB (@lem7630375 _98352) (@lem7630374)). Qed.
Lemma lem7630380 (_98352 : int) : (term109 _98352) = (term120 _98352).
Proof. exact (TRANS (@lem7630337 _98352) (@lem7630378 _98352)). Qed.
Lemma lem7630381 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7630382 (_98352 : int) : (term121 _98352) = (term122 _98352).
Proof. exact (MK_COMB (@lem7630381) (@lem7630380 _98352)). Qed.
Lemma lem7630383 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7630384 (_98352 : int) : (term108 _98352) = (term123 _98352).
Proof. exact (MK_COMB (@lem7630382 _98352) (@lem7630383)). Qed.
Lemma lem7630385 (_98352 : int) : (term56 _98352) = (term123 _98352).
Proof. exact (TRANS (@lem7630331 _98352) (@lem7630384 _98352)). Qed.
Lemma lem7630386 (_98352 : int) (_98353 : int) : (term71 _98352 _98353) = (term124 _98352 _98353).
Proof. exact (@lem1988287 term53 (term68 _98352 _98353)). Qed.
Lemma lem7630403 (_98352 : int) (_98353 : int) : (term68 _98352 _98353) = (term125 _98352 _98353).
Proof. exact (@lem1982755 (real_of_int _98352) (real_of_int _98353) term53). Qed.
Lemma lem7630406 : term126 = term126.
Proof. exact (eq_refl term126). Qed.
Lemma lem7630407 (_98352 : int) (_98353 : int) : (term127 _98352 _98353) = (term128 _98352 _98353).
Proof. exact (MK_COMB (@lem7630406) (@lem7630403 _98352 _98353)). Qed.
Lemma lem7630408 (_98352 : int) (_98353 : int) : (term128 _98352 _98353) = (term129 _98352 _98353).
Proof. exact (@lem1982792 term53 (term125 _98352 _98353)). Qed.
Lemma lem7630409 (_98352 : int) (_98353 : int) : (term130 _98352 _98353) = (term131 _98352 _98353).
Proof. exact (@lem1982781 (real_of_int _98352) term86 (term132 _98353)). Qed.
Lemma lem7630410 (_98353 : int) : (term133 _98353) = (term134 _98353).
Proof. exact (@lem1982781 (real_of_int _98353) term86 term53). Qed.
Lemma lem7630412 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630413 : term53 = term111.
Proof. exact (@lem7630412 term6). Qed.
Lemma lem7630415 (x : nat) : (term84 x) = (term85 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7630416 : term86 = term87.
Proof. exact (@lem7630415 term6). Qed.
Lemma lem7630417 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7630418 : term88 = term89.
Proof. exact (MK_COMB (@lem7630417) (@lem7630416)). Qed.
Lemma lem7630419 : term112 = term113.
Proof. exact (MK_COMB (@lem7630418) (@lem7630413)). Qed.
Lemma lem7630420 : term113 = term114.
Proof. exact (@lem1981613 term86 term53 term53 term53). Qed.
Lemma lem7630422 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7630423 : term95 = term96.
Proof. exact (@lem7630422 term6 term6). Qed.
Lemma lem7630424 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630425 : term98 = term6.
Proof. exact (EQ_MP (@lem7630424) (@lem940073)). Qed.
Lemma lem7630426 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630427 : term96 = term53.
Proof. exact (MK_COMB (@lem7630426) (@lem7630425)). Qed.
Lemma lem7630428 : term95 = term53.
Proof. exact (TRANS (@lem7630423) (@lem7630427)). Qed.
Lemma lem7630430 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7630431 : term112 = term117.
Proof. exact (@lem7630430 term6 term6). Qed.
Lemma lem7630432 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630433 : term98 = term6.
Proof. exact (EQ_MP (@lem7630432) (@lem940073)). Qed.
Lemma lem7630434 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630435 : term96 = term53.
Proof. exact (MK_COMB (@lem7630434) (@lem7630433)). Qed.
Lemma lem7630436 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7630437 : term117 = term86.
Proof. exact (MK_COMB (@lem7630436) (@lem7630435)). Qed.
Lemma lem7630438 : term112 = term86.
Proof. exact (TRANS (@lem7630431) (@lem7630437)). Qed.
Lemma lem7630439 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7630440 : term118 = term119.
Proof. exact (MK_COMB (@lem7630439) (@lem7630438)). Qed.
Lemma lem7630441 : term114 = term87.
Proof. exact (MK_COMB (@lem7630440) (@lem7630428)). Qed.
Lemma lem7630442 : term113 = term87.
Proof. exact (TRANS (@lem7630420) (@lem7630441)). Qed.
Lemma lem7630443 : term112 = term87.
Proof. exact (TRANS (@lem7630419) (@lem7630442)). Qed.
Lemma lem7630445 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7630446 : term87 = term86.
Proof. exact (@lem7630445 term86). Qed.
Lemma lem7630447 : term112 = term86.
Proof. exact (TRANS (@lem7630443) (@lem7630446)). Qed.
Lemma lem7630450 (_98353 : int) : (term135 _98353) = (term135 _98353).
Proof. exact (eq_refl (term135 _98353)). Qed.
Lemma lem7630451 (_98353 : int) : (term134 _98353) = (term136 _98353).
Proof. exact (MK_COMB (@lem7630450 _98353) (@lem7630447)). Qed.
Lemma lem7630452 (_98353 : int) : (term133 _98353) = (term136 _98353).
Proof. exact (TRANS (@lem7630410 _98353) (@lem7630451 _98353)). Qed.
Lemma lem7630455 (_98352 : int) : (term135 _98352) = (term135 _98352).
Proof. exact (eq_refl (term135 _98352)). Qed.
Lemma lem7630456 (_98352 : int) (_98353 : int) : (term131 _98352 _98353) = (term137 _98352 _98353).
Proof. exact (MK_COMB (@lem7630455 _98352) (@lem7630452 _98353)). Qed.
Lemma lem7630457 (_98352 : int) (_98353 : int) : (term130 _98352 _98353) = (term137 _98352 _98353).
Proof. exact (TRANS (@lem7630409 _98352 _98353) (@lem7630456 _98352 _98353)). Qed.
Lemma lem7630458 : term138 = term138.
Proof. exact (eq_refl term138). Qed.
Lemma lem7630459 (_98352 : int) (_98353 : int) : (term129 _98352 _98353) = (term139 _98352 _98353).
Proof. exact (MK_COMB (@lem7630458) (@lem7630457 _98352 _98353)). Qed.
Lemma lem7630460 (_98352 : int) (_98353 : int) : (term139 _98352 _98353) = (term140 _98352 _98353).
Proof. exact (@lem1982757 (term141 _98352) term53 (term136 _98353)). Qed.
Lemma lem7630461 (_98353 : int) : (term142 _98353) = (term143 _98353).
Proof. exact (@lem1982757 (term141 _98353) term53 term86). Qed.
Lemma lem7630463 (x : nat) : (term84 x) = (term85 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7630464 : term86 = term87.
Proof. exact (@lem7630463 term6). Qed.
Lemma lem7630466 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630467 : term53 = term111.
Proof. exact (@lem7630466 term6). Qed.
Lemma lem7630468 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7630469 : term138 = term144.
Proof. exact (MK_COMB (@lem7630468) (@lem7630467)). Qed.
Lemma lem7630470 : term145 = term146.
Proof. exact (MK_COMB (@lem7630469) (@lem7630464)). Qed.
Lemma lem7630471 : term147.
Proof. exact (@lem1981473 term53 term53 term86 term53 term46 term53). Qed.
Lemma lem7630473 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630474 : term149 = term150.
Proof. exact (@lem7630473 (NUMERAL 0) term6). Qed.
Lemma lem7630475 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630476 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630477 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630476 h1) (fun h1 : term150 = True => @lem7630475)). Qed.
Lemma lem7630478 : term150 = True.
Proof. exact (EQ_MP (@lem7630477) (@lem7630475)). Qed.
Lemma lem7630479 : term149 = True.
Proof. exact (TRANS (@lem7630474) (@lem7630478)). Qed.
Lemma lem7630480 : True = term149.
Proof. exact (SYM (@lem7630479)). Qed.
Lemma lem7630481 : term149.
Proof. exact (EQ_MP (@lem7630480) (@lem0)). Qed.
Lemma lem7630482 : term152.
Proof. exact (@lem7630471 (@lem7630481)). Qed.
Lemma lem7630484 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630485 : term149 = term150.
Proof. exact (@lem7630484 (NUMERAL 0) term6). Qed.
Lemma lem7630486 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630487 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630488 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630487 h1) (fun h1 : term150 = True => @lem7630486)). Qed.
Lemma lem7630489 : term150 = True.
Proof. exact (EQ_MP (@lem7630488) (@lem7630486)). Qed.
Lemma lem7630490 : term149 = True.
Proof. exact (TRANS (@lem7630485) (@lem7630489)). Qed.
Lemma lem7630491 : True = term149.
Proof. exact (SYM (@lem7630490)). Qed.
Lemma lem7630492 : term149.
Proof. exact (EQ_MP (@lem7630491) (@lem0)). Qed.
Lemma lem7630493 : term153.
Proof. exact (@lem7630482 (@lem7630492)). Qed.
Lemma lem7630495 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630496 : term149 = term150.
Proof. exact (@lem7630495 (NUMERAL 0) term6). Qed.
Lemma lem7630497 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630498 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630499 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630498 h1) (fun h1 : term150 = True => @lem7630497)). Qed.
Lemma lem7630500 : term150 = True.
Proof. exact (EQ_MP (@lem7630499) (@lem7630497)). Qed.
Lemma lem7630501 : term149 = True.
Proof. exact (TRANS (@lem7630496) (@lem7630500)). Qed.
Lemma lem7630502 : True = term149.
Proof. exact (SYM (@lem7630501)). Qed.
Lemma lem7630503 : term149.
Proof. exact (EQ_MP (@lem7630502) (@lem0)). Qed.
Lemma lem7630504 : term154.
Proof. exact (@lem7630493 (@lem7630503)). Qed.
Lemma lem7630506 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7630507 : term112 = term117.
Proof. exact (@lem7630506 term6 term6). Qed.
Lemma lem7630508 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630509 : term98 = term6.
Proof. exact (EQ_MP (@lem7630508) (@lem940073)). Qed.
Lemma lem7630510 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630511 : term96 = term53.
Proof. exact (MK_COMB (@lem7630510) (@lem7630509)). Qed.
Lemma lem7630512 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7630513 : term117 = term86.
Proof. exact (MK_COMB (@lem7630512) (@lem7630511)). Qed.
Lemma lem7630514 : term112 = term86.
Proof. exact (TRANS (@lem7630507) (@lem7630513)). Qed.
Lemma lem7630516 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7630517 : term95 = term96.
Proof. exact (@lem7630516 term6 term6). Qed.
Lemma lem7630518 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630519 : term98 = term6.
Proof. exact (EQ_MP (@lem7630518) (@lem940073)). Qed.
Lemma lem7630520 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630521 : term96 = term53.
Proof. exact (MK_COMB (@lem7630520) (@lem7630519)). Qed.
Lemma lem7630522 : term95 = term53.
Proof. exact (TRANS (@lem7630517) (@lem7630521)). Qed.
Lemma lem7630523 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7630524 : term155 = term138.
Proof. exact (MK_COMB (@lem7630523) (@lem7630522)). Qed.
Lemma lem7630525 : term156 = term145.
Proof. exact (MK_COMB (@lem7630524) (@lem7630514)). Qed.
Lemma lem7630527 (m : nat) : (term157 m) = term46.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem7630528 : term145 = term46.
Proof. exact (@lem7630527 term6). Qed.
Lemma lem7630529 : term156 = term46.
Proof. exact (TRANS (@lem7630525) (@lem7630528)). Qed.
Lemma lem7630530 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7630531 : term158 = term159.
Proof. exact (MK_COMB (@lem7630530) (@lem7630529)). Qed.
Lemma lem7630532 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem7630533 : term160 = term161.
Proof. exact (MK_COMB (@lem7630531) (@lem7630532)). Qed.
Lemma lem7630535 (x : nat) : (term162 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7630536 : term161 = term46.
Proof. exact (@lem7630535 term6). Qed.
Lemma lem7630537 : term160 = term46.
Proof. exact (TRANS (@lem7630533) (@lem7630536)). Qed.
Lemma lem7630539 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7630540 : term95 = term96.
Proof. exact (@lem7630539 term6 term6). Qed.
Lemma lem7630541 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630542 : term98 = term6.
Proof. exact (EQ_MP (@lem7630541) (@lem940073)). Qed.
Lemma lem7630543 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630544 : term96 = term53.
Proof. exact (MK_COMB (@lem7630543) (@lem7630542)). Qed.
Lemma lem7630545 : term95 = term53.
Proof. exact (TRANS (@lem7630540) (@lem7630544)). Qed.
Lemma lem7630546 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem7630547 : term163 = term161.
Proof. exact (MK_COMB (@lem7630546) (@lem7630545)). Qed.
Lemma lem7630549 (x : nat) : (term162 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7630550 : term161 = term46.
Proof. exact (@lem7630549 term6). Qed.
Lemma lem7630551 : term163 = term46.
Proof. exact (TRANS (@lem7630547) (@lem7630550)). Qed.
Lemma lem7630552 : term46 = term163.
Proof. exact (SYM (@lem7630551)). Qed.
Lemma lem7630553 : term160 = term163.
Proof. exact (TRANS (@lem7630537) (@lem7630552)). Qed.
Lemma lem7630554 : term146 = term83.
Proof. exact (@lem7630504 (@lem7630553)). Qed.
Lemma lem7630555 : term145 = term83.
Proof. exact (TRANS (@lem7630470) (@lem7630554)). Qed.
Lemma lem7630557 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7630558 : term83 = term46.
Proof. exact (@lem7630557 term46). Qed.
Lemma lem7630559 : term145 = term46.
Proof. exact (TRANS (@lem7630555) (@lem7630558)). Qed.
Lemma lem7630560 (_98353 : int) : (term135 _98353) = (term135 _98353).
Proof. exact (eq_refl (term135 _98353)). Qed.
Lemma lem7630561 (_98353 : int) : (term143 _98353) = (term164 _98353).
Proof. exact (MK_COMB (@lem7630560 _98353) (@lem7630559)). Qed.
Lemma lem7630562 (_98353 : int) : (term142 _98353) = (term164 _98353).
Proof. exact (TRANS (@lem7630461 _98353) (@lem7630561 _98353)). Qed.
Lemma lem7630563 (_98353 : int) : (term164 _98353) = (term141 _98353).
Proof. exact (@lem1982723 (term141 _98353)). Qed.
Lemma lem7630564 (_98353 : int) : (term142 _98353) = (term141 _98353).
Proof. exact (TRANS (@lem7630562 _98353) (@lem7630563 _98353)). Qed.
Lemma lem7630565 (_98352 : int) : (term135 _98352) = (term135 _98352).
Proof. exact (eq_refl (term135 _98352)). Qed.
Lemma lem7630566 (_98352 : int) (_98353 : int) : (term140 _98352 _98353) = (term165 _98352 _98353).
Proof. exact (MK_COMB (@lem7630565 _98352) (@lem7630564 _98353)). Qed.
Lemma lem7630567 (_98352 : int) (_98353 : int) : (term139 _98352 _98353) = (term165 _98352 _98353).
Proof. exact (TRANS (@lem7630460 _98352 _98353) (@lem7630566 _98352 _98353)). Qed.
Lemma lem7630568 (_98352 : int) (_98353 : int) : (term129 _98352 _98353) = (term165 _98352 _98353).
Proof. exact (TRANS (@lem7630459 _98352 _98353) (@lem7630567 _98352 _98353)). Qed.
Lemma lem7630569 (_98352 : int) (_98353 : int) : (term128 _98352 _98353) = (term165 _98352 _98353).
Proof. exact (TRANS (@lem7630408 _98352 _98353) (@lem7630568 _98352 _98353)). Qed.
Lemma lem7630570 (_98352 : int) (_98353 : int) : (term127 _98352 _98353) = (term165 _98352 _98353).
Proof. exact (TRANS (@lem7630407 _98352 _98353) (@lem7630569 _98352 _98353)). Qed.
Lemma lem7630571 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7630572 (_98352 : int) (_98353 : int) : (term166 _98352 _98353) = (term167 _98352 _98353).
Proof. exact (MK_COMB (@lem7630571) (@lem7630570 _98352 _98353)). Qed.
Lemma lem7630573 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7630574 (_98352 : int) (_98353 : int) : (term124 _98352 _98353) = (term168 _98352 _98353).
Proof. exact (MK_COMB (@lem7630572 _98352 _98353) (@lem7630573)). Qed.
Lemma lem7630575 (_98352 : int) (_98353 : int) : (term71 _98352 _98353) = (term168 _98352 _98353).
Proof. exact (TRANS (@lem7630386 _98352 _98353) (@lem7630574 _98352 _98353)). Qed.
Lemma lem7630576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7630577 (_98352 : int) : (term72 _98352) = (term169 _98352).
Proof. exact (MK_COMB (@lem7630576) (@lem7630385 _98352)). Qed.
Lemma lem7630578 (_98352 : int) (_98353 : int) : (term73 _98352 _98353) = (term170 _98352 _98353).
Proof. exact (MK_COMB (@lem7630577 _98352) (@lem7630575 _98352 _98353)). Qed.
Lemma lem7630579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7630580 (_98353 : int) : (term74 _98353) = (term171 _98353).
Proof. exact (MK_COMB (@lem7630579) (@lem7630330 _98353)). Qed.
Lemma lem7630581 (_98352 : int) (_98353 : int) : (term75 _98352 _98353) = (term172 _98352 _98353).
Proof. exact (MK_COMB (@lem7630580 _98353) (@lem7630578 _98352 _98353)). Qed.
Lemma lem7630582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7630583 (_98352 : int) : (term74 _98352) = (term171 _98352).
Proof. exact (MK_COMB (@lem7630582) (@lem7630282 _98352)). Qed.
Lemma lem7630584 (_98352 : int) (_98353 : int) : (term76 _98352 _98353) = (term173 _98352 _98353).
Proof. exact (MK_COMB (@lem7630583 _98352) (@lem7630581 _98352 _98353)). Qed.
Lemma lem7630611 (_98352 : int) (_98353 : int) : (term78 _98352 _98353) = (term173 _98352 _98353).
Proof. exact (TRANS (@lem7630234 _98352 _98353) (@lem7630584 _98352 _98353)). Qed.
Lemma lem7630615 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term173 _98352 _98353.
Proof. exact (h1). Qed.
Lemma lem7630616 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term172 _98352 _98353.
Proof. exact (proj2 (@lem7630615 _98352 _98353 h1)). Qed.
Lemma lem7630618 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term170 _98352 _98353.
Proof. exact (proj2 (@lem7630616 _98352 _98353 h1)). Qed.
Lemma lem7630619 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term107 _98353.
Proof. exact (proj1 (@lem7630616 _98352 _98353 h1)). Qed.
Lemma lem7630620 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term168 _98352 _98353.
Proof. exact (proj2 (@lem7630618 _98352 _98353 h1)). Qed.
Lemma lem7630621 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term123 _98352.
Proof. exact (proj1 (@lem7630618 _98352 _98353 h1)). Qed.
Lemma lem7630623 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7630624 : term174 = term149.
Proof. exact (@lem7630623 term46 term53). Qed.
Lemma lem7630626 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630627 : term53 = term111.
Proof. exact (@lem7630626 term6). Qed.
Lemma lem7630629 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630630 : term46 = term83.
Proof. exact (@lem7630629 (NUMERAL 0)). Qed.
Lemma lem7630631 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7630632 : term175 = term176.
Proof. exact (MK_COMB (@lem7630631) (@lem7630630)). Qed.
Lemma lem7630633 : term149 = term177.
Proof. exact (MK_COMB (@lem7630632) (@lem7630627)). Qed.
Lemma lem7630634 : term178.
Proof. exact (@lem1980255 term46 term53 term53 term53). Qed.
Lemma lem7630636 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630637 : term149 = term150.
Proof. exact (@lem7630636 (NUMERAL 0) term6). Qed.
Lemma lem7630638 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630639 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630640 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630639 h1) (fun h1 : term150 = True => @lem7630638)). Qed.
Lemma lem7630641 : term150 = True.
Proof. exact (EQ_MP (@lem7630640) (@lem7630638)). Qed.
Lemma lem7630642 : term149 = True.
Proof. exact (TRANS (@lem7630637) (@lem7630641)). Qed.
Lemma lem7630643 : True = term149.
Proof. exact (SYM (@lem7630642)). Qed.
Lemma lem7630644 : term149.
Proof. exact (EQ_MP (@lem7630643) (@lem0)). Qed.
Lemma lem7630645 : term179.
Proof. exact (@lem7630634 (@lem7630644)). Qed.
Lemma lem7630647 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630648 : term149 = term150.
Proof. exact (@lem7630647 (NUMERAL 0) term6). Qed.
Lemma lem7630649 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630650 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630651 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630650 h1) (fun h1 : term150 = True => @lem7630649)). Qed.
Lemma lem7630652 : term150 = True.
Proof. exact (EQ_MP (@lem7630651) (@lem7630649)). Qed.
Lemma lem7630653 : term149 = True.
Proof. exact (TRANS (@lem7630648) (@lem7630652)). Qed.
Lemma lem7630654 : True = term149.
Proof. exact (SYM (@lem7630653)). Qed.
Lemma lem7630655 : term149.
Proof. exact (EQ_MP (@lem7630654) (@lem0)). Qed.
Lemma lem7630656 : term177 = term180.
Proof. exact (@lem7630645 (@lem7630655)). Qed.
Lemma lem7630658 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7630659 : term95 = term96.
Proof. exact (@lem7630658 term6 term6). Qed.
Lemma lem7630660 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630661 : term98 = term6.
Proof. exact (EQ_MP (@lem7630660) (@lem940073)). Qed.
Lemma lem7630662 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630663 : term96 = term53.
Proof. exact (MK_COMB (@lem7630662) (@lem7630661)). Qed.
Lemma lem7630664 : term95 = term53.
Proof. exact (TRANS (@lem7630659) (@lem7630663)). Qed.
Lemma lem7630666 (x : nat) : (term162 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7630667 : term161 = term46.
Proof. exact (@lem7630666 term6). Qed.
Lemma lem7630668 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7630669 : term181 = term175.
Proof. exact (MK_COMB (@lem7630668) (@lem7630667)). Qed.
Lemma lem7630670 : term180 = term149.
Proof. exact (MK_COMB (@lem7630669) (@lem7630664)). Qed.
Lemma lem7630672 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630673 : term149 = term150.
Proof. exact (@lem7630672 (NUMERAL 0) term6). Qed.
Lemma lem7630674 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630675 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630676 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630675 h1) (fun h1 : term150 = True => @lem7630674)). Qed.
Lemma lem7630677 : term150 = True.
Proof. exact (EQ_MP (@lem7630676) (@lem7630674)). Qed.
Lemma lem7630678 : term149 = True.
Proof. exact (TRANS (@lem7630673) (@lem7630677)). Qed.
Lemma lem7630679 : term180 = True.
Proof. exact (TRANS (@lem7630670) (@lem7630678)). Qed.
Lemma lem7630680 : term177 = True.
Proof. exact (TRANS (@lem7630656) (@lem7630679)). Qed.
Lemma lem7630681 : term149 = True.
Proof. exact (TRANS (@lem7630633) (@lem7630680)). Qed.
Lemma lem7630682 : term174 = True.
Proof. exact (TRANS (@lem7630624) (@lem7630681)). Qed.
Lemma lem7630683 : True = term174.
Proof. exact (SYM (@lem7630682)). Qed.
Lemma lem7630684 : term174.
Proof. exact (EQ_MP (@lem7630683) (@lem0)). Qed.
Lemma lem7630685 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term182 _98352.
Proof. exact (conj (@lem7630684) (@lem7630621 _98352 _98353 h1)). Qed.
Lemma lem7630687 (x : real) (y : real) : term183 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7630688 (_98352 : int) : term184 _98352.
Proof. exact (@lem7630687 term53 (term120 _98352)). Qed.
Lemma lem7630689 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term185 _98352.
Proof. exact (@lem7630688 _98352 (@lem7630685 _98352 _98353 h1)). Qed.
Lemma lem7630690 (_98352 : int) : (term186 _98352) = (term120 _98352).
Proof. exact (@lem1982733 (term120 _98352)). Qed.
Lemma lem7630691 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7630692 (_98352 : int) : (term187 _98352) = (term122 _98352).
Proof. exact (MK_COMB (@lem7630691) (@lem7630690 _98352)). Qed.
Lemma lem7630693 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7630694 (_98352 : int) : (term185 _98352) = (term123 _98352).
Proof. exact (MK_COMB (@lem7630692 _98352) (@lem7630693)). Qed.
Lemma lem7630695 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term123 _98352.
Proof. exact (EQ_MP (@lem7630694 _98352) (@lem7630689 _98352 _98353 h1)). Qed.
Lemma lem7630697 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7630698 : term174 = term149.
Proof. exact (@lem7630697 term46 term53). Qed.
Lemma lem7630700 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630701 : term53 = term111.
Proof. exact (@lem7630700 term6). Qed.
Lemma lem7630703 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630704 : term46 = term83.
Proof. exact (@lem7630703 (NUMERAL 0)). Qed.
Lemma lem7630705 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7630706 : term175 = term176.
Proof. exact (MK_COMB (@lem7630705) (@lem7630704)). Qed.
Lemma lem7630707 : term149 = term177.
Proof. exact (MK_COMB (@lem7630706) (@lem7630701)). Qed.
Lemma lem7630708 : term178.
Proof. exact (@lem1980255 term46 term53 term53 term53). Qed.
Lemma lem7630710 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630711 : term149 = term150.
Proof. exact (@lem7630710 (NUMERAL 0) term6). Qed.
Lemma lem7630712 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630713 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630714 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630713 h1) (fun h1 : term150 = True => @lem7630712)). Qed.
Lemma lem7630715 : term150 = True.
Proof. exact (EQ_MP (@lem7630714) (@lem7630712)). Qed.
Lemma lem7630716 : term149 = True.
Proof. exact (TRANS (@lem7630711) (@lem7630715)). Qed.
Lemma lem7630717 : True = term149.
Proof. exact (SYM (@lem7630716)). Qed.
Lemma lem7630718 : term149.
Proof. exact (EQ_MP (@lem7630717) (@lem0)). Qed.
Lemma lem7630719 : term179.
Proof. exact (@lem7630708 (@lem7630718)). Qed.
Lemma lem7630721 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630722 : term149 = term150.
Proof. exact (@lem7630721 (NUMERAL 0) term6). Qed.
Lemma lem7630723 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630724 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630725 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630724 h1) (fun h1 : term150 = True => @lem7630723)). Qed.
Lemma lem7630726 : term150 = True.
Proof. exact (EQ_MP (@lem7630725) (@lem7630723)). Qed.
Lemma lem7630727 : term149 = True.
Proof. exact (TRANS (@lem7630722) (@lem7630726)). Qed.
Lemma lem7630728 : True = term149.
Proof. exact (SYM (@lem7630727)). Qed.
Lemma lem7630729 : term149.
Proof. exact (EQ_MP (@lem7630728) (@lem0)). Qed.
Lemma lem7630730 : term177 = term180.
Proof. exact (@lem7630719 (@lem7630729)). Qed.
Lemma lem7630732 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7630733 : term95 = term96.
Proof. exact (@lem7630732 term6 term6). Qed.
Lemma lem7630734 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630735 : term98 = term6.
Proof. exact (EQ_MP (@lem7630734) (@lem940073)). Qed.
Lemma lem7630736 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630737 : term96 = term53.
Proof. exact (MK_COMB (@lem7630736) (@lem7630735)). Qed.
Lemma lem7630738 : term95 = term53.
Proof. exact (TRANS (@lem7630733) (@lem7630737)). Qed.
Lemma lem7630740 (x : nat) : (term162 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7630741 : term161 = term46.
Proof. exact (@lem7630740 term6). Qed.
Lemma lem7630742 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7630743 : term181 = term175.
Proof. exact (MK_COMB (@lem7630742) (@lem7630741)). Qed.
Lemma lem7630744 : term180 = term149.
Proof. exact (MK_COMB (@lem7630743) (@lem7630738)). Qed.
Lemma lem7630746 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630747 : term149 = term150.
Proof. exact (@lem7630746 (NUMERAL 0) term6). Qed.
Lemma lem7630748 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630749 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630750 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630749 h1) (fun h1 : term150 = True => @lem7630748)). Qed.
Lemma lem7630751 : term150 = True.
Proof. exact (EQ_MP (@lem7630750) (@lem7630748)). Qed.
Lemma lem7630752 : term149 = True.
Proof. exact (TRANS (@lem7630747) (@lem7630751)). Qed.
Lemma lem7630753 : term180 = True.
Proof. exact (TRANS (@lem7630744) (@lem7630752)). Qed.
Lemma lem7630754 : term177 = True.
Proof. exact (TRANS (@lem7630730) (@lem7630753)). Qed.
Lemma lem7630755 : term149 = True.
Proof. exact (TRANS (@lem7630707) (@lem7630754)). Qed.
Lemma lem7630756 : term174 = True.
Proof. exact (TRANS (@lem7630698) (@lem7630755)). Qed.
Lemma lem7630757 : True = term174.
Proof. exact (SYM (@lem7630756)). Qed.
Lemma lem7630758 : term174.
Proof. exact (EQ_MP (@lem7630757) (@lem0)). Qed.
Lemma lem7630759 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term188 _98353.
Proof. exact (conj (@lem7630758) (@lem7630619 _98352 _98353 h1)). Qed.
Lemma lem7630761 (x : real) (y : real) : term183 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7630762 (_98353 : int) : term189 _98353.
Proof. exact (@lem7630761 term53 (real_of_int _98353)). Qed.
Lemma lem7630763 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term190 _98353.
Proof. exact (@lem7630762 _98353 (@lem7630759 _98352 _98353 h1)). Qed.
Lemma lem7630764 (_98353 : int) : (term191 _98353) = (real_of_int _98353).
Proof. exact (@lem1982733 (real_of_int _98353)). Qed.
Lemma lem7630765 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7630766 (_98353 : int) : (term192 _98353) = (term106 _98353).
Proof. exact (MK_COMB (@lem7630765) (@lem7630764 _98353)). Qed.
Lemma lem7630767 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7630768 (_98353 : int) : (term190 _98353) = (term107 _98353).
Proof. exact (MK_COMB (@lem7630766 _98353) (@lem7630767)). Qed.
Lemma lem7630769 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term107 _98353.
Proof. exact (EQ_MP (@lem7630768 _98353) (@lem7630763 _98352 _98353 h1)). Qed.
Lemma lem7630771 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7630772 : term174 = term149.
Proof. exact (@lem7630771 term46 term53). Qed.
Lemma lem7630774 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630775 : term53 = term111.
Proof. exact (@lem7630774 term6). Qed.
Lemma lem7630777 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630778 : term46 = term83.
Proof. exact (@lem7630777 (NUMERAL 0)). Qed.
Lemma lem7630779 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7630780 : term175 = term176.
Proof. exact (MK_COMB (@lem7630779) (@lem7630778)). Qed.
Lemma lem7630781 : term149 = term177.
Proof. exact (MK_COMB (@lem7630780) (@lem7630775)). Qed.
Lemma lem7630782 : term178.
Proof. exact (@lem1980255 term46 term53 term53 term53). Qed.
Lemma lem7630784 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630785 : term149 = term150.
Proof. exact (@lem7630784 (NUMERAL 0) term6). Qed.
Lemma lem7630786 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630787 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630788 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630787 h1) (fun h1 : term150 = True => @lem7630786)). Qed.
Lemma lem7630789 : term150 = True.
Proof. exact (EQ_MP (@lem7630788) (@lem7630786)). Qed.
Lemma lem7630790 : term149 = True.
Proof. exact (TRANS (@lem7630785) (@lem7630789)). Qed.
Lemma lem7630791 : True = term149.
Proof. exact (SYM (@lem7630790)). Qed.
Lemma lem7630792 : term149.
Proof. exact (EQ_MP (@lem7630791) (@lem0)). Qed.
Lemma lem7630793 : term179.
Proof. exact (@lem7630782 (@lem7630792)). Qed.
Lemma lem7630795 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630796 : term149 = term150.
Proof. exact (@lem7630795 (NUMERAL 0) term6). Qed.
Lemma lem7630797 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630798 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630799 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630798 h1) (fun h1 : term150 = True => @lem7630797)). Qed.
Lemma lem7630800 : term150 = True.
Proof. exact (EQ_MP (@lem7630799) (@lem7630797)). Qed.
Lemma lem7630801 : term149 = True.
Proof. exact (TRANS (@lem7630796) (@lem7630800)). Qed.
Lemma lem7630802 : True = term149.
Proof. exact (SYM (@lem7630801)). Qed.
Lemma lem7630803 : term149.
Proof. exact (EQ_MP (@lem7630802) (@lem0)). Qed.
Lemma lem7630804 : term177 = term180.
Proof. exact (@lem7630793 (@lem7630803)). Qed.
Lemma lem7630806 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7630807 : term95 = term96.
Proof. exact (@lem7630806 term6 term6). Qed.
Lemma lem7630808 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630809 : term98 = term6.
Proof. exact (EQ_MP (@lem7630808) (@lem940073)). Qed.
Lemma lem7630810 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630811 : term96 = term53.
Proof. exact (MK_COMB (@lem7630810) (@lem7630809)). Qed.
Lemma lem7630812 : term95 = term53.
Proof. exact (TRANS (@lem7630807) (@lem7630811)). Qed.
Lemma lem7630814 (x : nat) : (term162 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7630815 : term161 = term46.
Proof. exact (@lem7630814 term6). Qed.
Lemma lem7630816 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7630817 : term181 = term175.
Proof. exact (MK_COMB (@lem7630816) (@lem7630815)). Qed.
Lemma lem7630818 : term180 = term149.
Proof. exact (MK_COMB (@lem7630817) (@lem7630812)). Qed.
Lemma lem7630820 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630821 : term149 = term150.
Proof. exact (@lem7630820 (NUMERAL 0) term6). Qed.
Lemma lem7630822 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630823 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630824 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630823 h1) (fun h1 : term150 = True => @lem7630822)). Qed.
Lemma lem7630825 : term150 = True.
Proof. exact (EQ_MP (@lem7630824) (@lem7630822)). Qed.
Lemma lem7630826 : term149 = True.
Proof. exact (TRANS (@lem7630821) (@lem7630825)). Qed.
Lemma lem7630827 : term180 = True.
Proof. exact (TRANS (@lem7630818) (@lem7630826)). Qed.
Lemma lem7630828 : term177 = True.
Proof. exact (TRANS (@lem7630804) (@lem7630827)). Qed.
Lemma lem7630829 : term149 = True.
Proof. exact (TRANS (@lem7630781) (@lem7630828)). Qed.
Lemma lem7630830 : term174 = True.
Proof. exact (TRANS (@lem7630772) (@lem7630829)). Qed.
Lemma lem7630831 : True = term174.
Proof. exact (SYM (@lem7630830)). Qed.
Lemma lem7630832 : term174.
Proof. exact (EQ_MP (@lem7630831) (@lem0)). Qed.
Lemma lem7630833 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term193 _98352 _98353.
Proof. exact (conj (@lem7630832) (@lem7630620 _98352 _98353 h1)). Qed.
Lemma lem7630835 (x : real) (y : real) : term183 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7630836 (_98352 : int) (_98353 : int) : term194 _98352 _98353.
Proof. exact (@lem7630835 term53 (term165 _98352 _98353)). Qed.
Lemma lem7630837 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term195 _98352 _98353.
Proof. exact (@lem7630836 _98352 _98353 (@lem7630833 _98352 _98353 h1)). Qed.
Lemma lem7630838 (_98352 : int) (_98353 : int) : (term196 _98352 _98353) = (term165 _98352 _98353).
Proof. exact (@lem1982733 (term165 _98352 _98353)). Qed.
Lemma lem7630839 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7630840 (_98352 : int) (_98353 : int) : (term197 _98352 _98353) = (term167 _98352 _98353).
Proof. exact (MK_COMB (@lem7630839) (@lem7630838 _98352 _98353)). Qed.
Lemma lem7630841 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7630842 (_98352 : int) (_98353 : int) : (term195 _98352 _98353) = (term168 _98352 _98353).
Proof. exact (MK_COMB (@lem7630840 _98352 _98353) (@lem7630841)). Qed.
Lemma lem7630843 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term168 _98352 _98353.
Proof. exact (EQ_MP (@lem7630842 _98352 _98353) (@lem7630837 _98352 _98353 h1)). Qed.
Lemma lem7630844 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term198 _98352 _98353.
Proof. exact (conj (@lem7630843 _98352 _98353 h1) (@lem7630769 _98352 _98353 h1)). Qed.
Lemma lem7630846 (x : real) (y : real) : term199 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7630847 (_98352 : int) (_98353 : int) : term200 _98352 _98353.
Proof. exact (@lem7630846 (term165 _98352 _98353) (real_of_int _98353)). Qed.
Lemma lem7630848 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term201 _98352 _98353.
Proof. exact (@lem7630847 _98352 _98353 (@lem7630844 _98352 _98353 h1)). Qed.
Lemma lem7630849 (_98352 : int) (_98353 : int) : (term202 _98352 _98353) = (term203 _98352 _98353).
Proof. exact (@lem1982755 (term141 _98352) (term141 _98353) (real_of_int _98353)). Qed.
Lemma lem7630850 (_98353 : int) : (term204 _98353) = (term205 _98353).
Proof. exact (@lem1982713 term86 (real_of_int _98353)). Qed.
Lemma lem7630852 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630853 : term53 = term111.
Proof. exact (@lem7630852 term6). Qed.
Lemma lem7630855 (x : nat) : (term84 x) = (term85 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7630856 : term86 = term87.
Proof. exact (@lem7630855 term6). Qed.
Lemma lem7630857 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7630858 : term206 = term207.
Proof. exact (MK_COMB (@lem7630857) (@lem7630856)). Qed.
Lemma lem7630859 : term208 = term209.
Proof. exact (MK_COMB (@lem7630858) (@lem7630853)). Qed.
Lemma lem7630860 : term210.
Proof. exact (@lem1981473 term86 term53 term53 term53 term46 term53). Qed.
Lemma lem7630862 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630863 : term149 = term150.
Proof. exact (@lem7630862 (NUMERAL 0) term6). Qed.
Lemma lem7630864 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630865 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630866 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630865 h1) (fun h1 : term150 = True => @lem7630864)). Qed.
Lemma lem7630867 : term150 = True.
Proof. exact (EQ_MP (@lem7630866) (@lem7630864)). Qed.
Lemma lem7630868 : term149 = True.
Proof. exact (TRANS (@lem7630863) (@lem7630867)). Qed.
Lemma lem7630869 : True = term149.
Proof. exact (SYM (@lem7630868)). Qed.
Lemma lem7630870 : term149.
Proof. exact (EQ_MP (@lem7630869) (@lem0)). Qed.
Lemma lem7630871 : term211.
Proof. exact (@lem7630860 (@lem7630870)). Qed.
Lemma lem7630873 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630874 : term149 = term150.
Proof. exact (@lem7630873 (NUMERAL 0) term6). Qed.
Lemma lem7630875 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630876 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630877 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630876 h1) (fun h1 : term150 = True => @lem7630875)). Qed.
Lemma lem7630878 : term150 = True.
Proof. exact (EQ_MP (@lem7630877) (@lem7630875)). Qed.
Lemma lem7630879 : term149 = True.
Proof. exact (TRANS (@lem7630874) (@lem7630878)). Qed.
Lemma lem7630880 : True = term149.
Proof. exact (SYM (@lem7630879)). Qed.
Lemma lem7630881 : term149.
Proof. exact (EQ_MP (@lem7630880) (@lem0)). Qed.
Lemma lem7630882 : term212.
Proof. exact (@lem7630871 (@lem7630881)). Qed.
Lemma lem7630884 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630885 : term149 = term150.
Proof. exact (@lem7630884 (NUMERAL 0) term6). Qed.
Lemma lem7630886 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630887 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630888 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630887 h1) (fun h1 : term150 = True => @lem7630886)). Qed.
Lemma lem7630889 : term150 = True.
Proof. exact (EQ_MP (@lem7630888) (@lem7630886)). Qed.
Lemma lem7630890 : term149 = True.
Proof. exact (TRANS (@lem7630885) (@lem7630889)). Qed.
Lemma lem7630891 : True = term149.
Proof. exact (SYM (@lem7630890)). Qed.
Lemma lem7630892 : term149.
Proof. exact (EQ_MP (@lem7630891) (@lem0)). Qed.
Lemma lem7630893 : term213.
Proof. exact (@lem7630882 (@lem7630892)). Qed.
Lemma lem7630895 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7630896 : term95 = term96.
Proof. exact (@lem7630895 term6 term6). Qed.
Lemma lem7630897 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630898 : term98 = term6.
Proof. exact (EQ_MP (@lem7630897) (@lem940073)). Qed.
Lemma lem7630899 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630900 : term96 = term53.
Proof. exact (MK_COMB (@lem7630899) (@lem7630898)). Qed.
Lemma lem7630901 : term95 = term53.
Proof. exact (TRANS (@lem7630896) (@lem7630900)). Qed.
Lemma lem7630903 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7630904 : term112 = term117.
Proof. exact (@lem7630903 term6 term6). Qed.
Lemma lem7630905 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630906 : term98 = term6.
Proof. exact (EQ_MP (@lem7630905) (@lem940073)). Qed.
Lemma lem7630907 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630908 : term96 = term53.
Proof. exact (MK_COMB (@lem7630907) (@lem7630906)). Qed.
Lemma lem7630909 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7630910 : term117 = term86.
Proof. exact (MK_COMB (@lem7630909) (@lem7630908)). Qed.
Lemma lem7630911 : term112 = term86.
Proof. exact (TRANS (@lem7630904) (@lem7630910)). Qed.
Lemma lem7630912 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7630913 : term214 = term206.
Proof. exact (MK_COMB (@lem7630912) (@lem7630911)). Qed.
Lemma lem7630914 : term215 = term208.
Proof. exact (MK_COMB (@lem7630913) (@lem7630901)). Qed.
Lemma lem7630916 (m : nat) : (term216 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7630917 : term208 = term46.
Proof. exact (@lem7630916 term6). Qed.
Lemma lem7630918 : term215 = term46.
Proof. exact (TRANS (@lem7630914) (@lem7630917)). Qed.
Lemma lem7630919 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7630920 : term217 = term159.
Proof. exact (MK_COMB (@lem7630919) (@lem7630918)). Qed.
Lemma lem7630921 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem7630922 : term218 = term161.
Proof. exact (MK_COMB (@lem7630920) (@lem7630921)). Qed.
Lemma lem7630924 (x : nat) : (term162 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7630925 : term161 = term46.
Proof. exact (@lem7630924 term6). Qed.
Lemma lem7630926 : term218 = term46.
Proof. exact (TRANS (@lem7630922) (@lem7630925)). Qed.
Lemma lem7630928 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7630929 : term95 = term96.
Proof. exact (@lem7630928 term6 term6). Qed.
Lemma lem7630930 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7630931 : term98 = term6.
Proof. exact (EQ_MP (@lem7630930) (@lem940073)). Qed.
Lemma lem7630932 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7630933 : term96 = term53.
Proof. exact (MK_COMB (@lem7630932) (@lem7630931)). Qed.
Lemma lem7630934 : term95 = term53.
Proof. exact (TRANS (@lem7630929) (@lem7630933)). Qed.
Lemma lem7630935 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem7630936 : term163 = term161.
Proof. exact (MK_COMB (@lem7630935) (@lem7630934)). Qed.
Lemma lem7630938 (x : nat) : (term162 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7630939 : term161 = term46.
Proof. exact (@lem7630938 term6). Qed.
Lemma lem7630940 : term163 = term46.
Proof. exact (TRANS (@lem7630936) (@lem7630939)). Qed.
Lemma lem7630941 : term46 = term163.
Proof. exact (SYM (@lem7630940)). Qed.
Lemma lem7630942 : term218 = term163.
Proof. exact (TRANS (@lem7630926) (@lem7630941)). Qed.
Lemma lem7630943 : term209 = term83.
Proof. exact (@lem7630893 (@lem7630942)). Qed.
Lemma lem7630944 : term208 = term83.
Proof. exact (TRANS (@lem7630859) (@lem7630943)). Qed.
Lemma lem7630946 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7630947 : term83 = term46.
Proof. exact (@lem7630946 term46). Qed.
Lemma lem7630948 : term208 = term46.
Proof. exact (TRANS (@lem7630944) (@lem7630947)). Qed.
Lemma lem7630949 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7630950 : term219 = term159.
Proof. exact (MK_COMB (@lem7630949) (@lem7630948)). Qed.
Lemma lem7630951 (_98353 : int) : (real_of_int _98353) = (real_of_int _98353).
Proof. exact (eq_refl (real_of_int _98353)). Qed.
Lemma lem7630952 (_98353 : int) : (term205 _98353) = (term220 _98353).
Proof. exact (MK_COMB (@lem7630950) (@lem7630951 _98353)). Qed.
Lemma lem7630953 (_98353 : int) : (term204 _98353) = (term220 _98353).
Proof. exact (TRANS (@lem7630850 _98353) (@lem7630952 _98353)). Qed.
Lemma lem7630954 (_98353 : int) : (term220 _98353) = term46.
Proof. exact (@lem1982719 (real_of_int _98353)). Qed.
Lemma lem7630955 (_98353 : int) : (term204 _98353) = term46.
Proof. exact (TRANS (@lem7630953 _98353) (@lem7630954 _98353)). Qed.
Lemma lem7630956 (_98352 : int) : (term135 _98352) = (term135 _98352).
Proof. exact (eq_refl (term135 _98352)). Qed.
Lemma lem7630957 (_98353 : int) (_98352 : int) : (term203 _98352 _98353) = (term164 _98352).
Proof. exact (MK_COMB (@lem7630956 _98352) (@lem7630955 _98353)). Qed.
Lemma lem7630958 (_98353 : int) (_98352 : int) : (term202 _98352 _98353) = (term164 _98352).
Proof. exact (TRANS (@lem7630849 _98352 _98353) (@lem7630957 _98353 _98352)). Qed.
Lemma lem7630959 (_98352 : int) : (term164 _98352) = (term141 _98352).
Proof. exact (@lem1982723 (term141 _98352)). Qed.
Lemma lem7630960 (_98353 : int) (_98352 : int) : (term202 _98352 _98353) = (term141 _98352).
Proof. exact (TRANS (@lem7630958 _98353 _98352) (@lem7630959 _98352)). Qed.
Lemma lem7630961 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7630962 (_98353 : int) (_98352 : int) : (term221 _98352 _98353) = (term222 _98352).
Proof. exact (MK_COMB (@lem7630961) (@lem7630960 _98353 _98352)). Qed.
Lemma lem7630963 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7630964 (_98353 : int) (_98352 : int) : (term201 _98352 _98353) = (term223 _98352).
Proof. exact (MK_COMB (@lem7630962 _98353 _98352) (@lem7630963)). Qed.
Lemma lem7630965 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term223 _98352.
Proof. exact (EQ_MP (@lem7630964 _98353 _98352) (@lem7630848 _98352 _98353 h1)). Qed.
Lemma lem7630967 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7630968 : term174 = term149.
Proof. exact (@lem7630967 term46 term53). Qed.
Lemma lem7630970 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630971 : term53 = term111.
Proof. exact (@lem7630970 term6). Qed.
Lemma lem7630973 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7630974 : term46 = term83.
Proof. exact (@lem7630973 (NUMERAL 0)). Qed.
Lemma lem7630975 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7630976 : term175 = term176.
Proof. exact (MK_COMB (@lem7630975) (@lem7630974)). Qed.
Lemma lem7630977 : term149 = term177.
Proof. exact (MK_COMB (@lem7630976) (@lem7630971)). Qed.
Lemma lem7630978 : term178.
Proof. exact (@lem1980255 term46 term53 term53 term53). Qed.
Lemma lem7630980 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630981 : term149 = term150.
Proof. exact (@lem7630980 (NUMERAL 0) term6). Qed.
Lemma lem7630982 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630983 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630984 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630983 h1) (fun h1 : term150 = True => @lem7630982)). Qed.
Lemma lem7630985 : term150 = True.
Proof. exact (EQ_MP (@lem7630984) (@lem7630982)). Qed.
Lemma lem7630986 : term149 = True.
Proof. exact (TRANS (@lem7630981) (@lem7630985)). Qed.
Lemma lem7630987 : True = term149.
Proof. exact (SYM (@lem7630986)). Qed.
Lemma lem7630988 : term149.
Proof. exact (EQ_MP (@lem7630987) (@lem0)). Qed.
Lemma lem7630989 : term179.
Proof. exact (@lem7630978 (@lem7630988)). Qed.
Lemma lem7630991 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7630992 : term149 = term150.
Proof. exact (@lem7630991 (NUMERAL 0) term6). Qed.
Lemma lem7630993 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7630994 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7630995 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7630994 h1) (fun h1 : term150 = True => @lem7630993)). Qed.
Lemma lem7630996 : term150 = True.
Proof. exact (EQ_MP (@lem7630995) (@lem7630993)). Qed.
Lemma lem7630997 : term149 = True.
Proof. exact (TRANS (@lem7630992) (@lem7630996)). Qed.
Lemma lem7630998 : True = term149.
Proof. exact (SYM (@lem7630997)). Qed.
Lemma lem7630999 : term149.
Proof. exact (EQ_MP (@lem7630998) (@lem0)). Qed.
Lemma lem7631000 : term177 = term180.
Proof. exact (@lem7630989 (@lem7630999)). Qed.
Lemma lem7631002 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7631003 : term95 = term96.
Proof. exact (@lem7631002 term6 term6). Qed.
Lemma lem7631004 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7631005 : term98 = term6.
Proof. exact (EQ_MP (@lem7631004) (@lem940073)). Qed.
Lemma lem7631006 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7631007 : term96 = term53.
Proof. exact (MK_COMB (@lem7631006) (@lem7631005)). Qed.
Lemma lem7631008 : term95 = term53.
Proof. exact (TRANS (@lem7631003) (@lem7631007)). Qed.
Lemma lem7631010 (x : nat) : (term162 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7631011 : term161 = term46.
Proof. exact (@lem7631010 term6). Qed.
Lemma lem7631012 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7631013 : term181 = term175.
Proof. exact (MK_COMB (@lem7631012) (@lem7631011)). Qed.
Lemma lem7631014 : term180 = term149.
Proof. exact (MK_COMB (@lem7631013) (@lem7631008)). Qed.
Lemma lem7631016 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7631017 : term149 = term150.
Proof. exact (@lem7631016 (NUMERAL 0) term6). Qed.
Lemma lem7631018 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7631019 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7631020 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7631019 h1) (fun h1 : term150 = True => @lem7631018)). Qed.
Lemma lem7631021 : term150 = True.
Proof. exact (EQ_MP (@lem7631020) (@lem7631018)). Qed.
Lemma lem7631022 : term149 = True.
Proof. exact (TRANS (@lem7631017) (@lem7631021)). Qed.
Lemma lem7631023 : term180 = True.
Proof. exact (TRANS (@lem7631014) (@lem7631022)). Qed.
Lemma lem7631024 : term177 = True.
Proof. exact (TRANS (@lem7631000) (@lem7631023)). Qed.
Lemma lem7631025 : term149 = True.
Proof. exact (TRANS (@lem7630977) (@lem7631024)). Qed.
Lemma lem7631026 : term174 = True.
Proof. exact (TRANS (@lem7630968) (@lem7631025)). Qed.
Lemma lem7631027 : True = term174.
Proof. exact (SYM (@lem7631026)). Qed.
Lemma lem7631028 : term174.
Proof. exact (EQ_MP (@lem7631027) (@lem0)). Qed.
Lemma lem7631029 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term224 _98352.
Proof. exact (conj (@lem7631028) (@lem7630965 _98352 _98353 h1)). Qed.
Lemma lem7631031 (x : real) (y : real) : term183 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7631032 (_98352 : int) : term225 _98352.
Proof. exact (@lem7631031 term53 (term141 _98352)). Qed.
Lemma lem7631033 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term226 _98352.
Proof. exact (@lem7631032 _98352 (@lem7631029 _98352 _98353 h1)). Qed.
Lemma lem7631034 (_98352 : int) : (term227 _98352) = (term141 _98352).
Proof. exact (@lem1982733 (term141 _98352)). Qed.
Lemma lem7631035 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7631036 (_98352 : int) : (term228 _98352) = (term222 _98352).
Proof. exact (MK_COMB (@lem7631035) (@lem7631034 _98352)). Qed.
Lemma lem7631037 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7631038 (_98352 : int) : (term226 _98352) = (term223 _98352).
Proof. exact (MK_COMB (@lem7631036 _98352) (@lem7631037)). Qed.
Lemma lem7631039 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term223 _98352.
Proof. exact (EQ_MP (@lem7631038 _98352) (@lem7631033 _98352 _98353 h1)). Qed.
Lemma lem7631040 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term229 _98352.
Proof. exact (conj (@lem7631039 _98352 _98353 h1) (@lem7630695 _98352 _98353 h1)). Qed.
Lemma lem7631042 (x : real) (y : real) : term199 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7631043 (_98352 : int) : term230 _98352.
Proof. exact (@lem7631042 (term141 _98352) (term120 _98352)). Qed.
Lemma lem7631044 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term231 _98352.
Proof. exact (@lem7631043 _98352 (@lem7631040 _98352 _98353 h1)). Qed.
Lemma lem7631045 (_98352 : int) : (term232 _98352) = (term233 _98352).
Proof. exact (@lem1982763 (term141 _98352) (real_of_int _98352) term86). Qed.
Lemma lem7631046 (_98352 : int) : (term204 _98352) = (term205 _98352).
Proof. exact (@lem1982713 term86 (real_of_int _98352)). Qed.
Lemma lem7631048 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7631049 : term53 = term111.
Proof. exact (@lem7631048 term6). Qed.
Lemma lem7631051 (x : nat) : (term84 x) = (term85 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7631052 : term86 = term87.
Proof. exact (@lem7631051 term6). Qed.
Lemma lem7631053 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7631054 : term206 = term207.
Proof. exact (MK_COMB (@lem7631053) (@lem7631052)). Qed.
Lemma lem7631055 : term208 = term209.
Proof. exact (MK_COMB (@lem7631054) (@lem7631049)). Qed.
Lemma lem7631056 : term210.
Proof. exact (@lem1981473 term86 term53 term53 term53 term46 term53). Qed.
Lemma lem7631058 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7631059 : term149 = term150.
Proof. exact (@lem7631058 (NUMERAL 0) term6). Qed.
Lemma lem7631060 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7631061 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7631062 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7631061 h1) (fun h1 : term150 = True => @lem7631060)). Qed.
Lemma lem7631063 : term150 = True.
Proof. exact (EQ_MP (@lem7631062) (@lem7631060)). Qed.
Lemma lem7631064 : term149 = True.
Proof. exact (TRANS (@lem7631059) (@lem7631063)). Qed.
Lemma lem7631065 : True = term149.
Proof. exact (SYM (@lem7631064)). Qed.
Lemma lem7631066 : term149.
Proof. exact (EQ_MP (@lem7631065) (@lem0)). Qed.
Lemma lem7631067 : term211.
Proof. exact (@lem7631056 (@lem7631066)). Qed.
Lemma lem7631069 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7631070 : term149 = term150.
Proof. exact (@lem7631069 (NUMERAL 0) term6). Qed.
Lemma lem7631071 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7631072 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7631073 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7631072 h1) (fun h1 : term150 = True => @lem7631071)). Qed.
Lemma lem7631074 : term150 = True.
Proof. exact (EQ_MP (@lem7631073) (@lem7631071)). Qed.
Lemma lem7631075 : term149 = True.
Proof. exact (TRANS (@lem7631070) (@lem7631074)). Qed.
Lemma lem7631076 : True = term149.
Proof. exact (SYM (@lem7631075)). Qed.
Lemma lem7631077 : term149.
Proof. exact (EQ_MP (@lem7631076) (@lem0)). Qed.
Lemma lem7631078 : term212.
Proof. exact (@lem7631067 (@lem7631077)). Qed.
Lemma lem7631080 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7631081 : term149 = term150.
Proof. exact (@lem7631080 (NUMERAL 0) term6). Qed.
Lemma lem7631082 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7631083 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7631084 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7631083 h1) (fun h1 : term150 = True => @lem7631082)). Qed.
Lemma lem7631085 : term150 = True.
Proof. exact (EQ_MP (@lem7631084) (@lem7631082)). Qed.
Lemma lem7631086 : term149 = True.
Proof. exact (TRANS (@lem7631081) (@lem7631085)). Qed.
Lemma lem7631087 : True = term149.
Proof. exact (SYM (@lem7631086)). Qed.
Lemma lem7631088 : term149.
Proof. exact (EQ_MP (@lem7631087) (@lem0)). Qed.
Lemma lem7631089 : term213.
Proof. exact (@lem7631078 (@lem7631088)). Qed.
Lemma lem7631091 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7631092 : term95 = term96.
Proof. exact (@lem7631091 term6 term6). Qed.
Lemma lem7631093 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7631094 : term98 = term6.
Proof. exact (EQ_MP (@lem7631093) (@lem940073)). Qed.
Lemma lem7631095 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7631096 : term96 = term53.
Proof. exact (MK_COMB (@lem7631095) (@lem7631094)). Qed.
Lemma lem7631097 : term95 = term53.
Proof. exact (TRANS (@lem7631092) (@lem7631096)). Qed.
Lemma lem7631099 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7631100 : term112 = term117.
Proof. exact (@lem7631099 term6 term6). Qed.
Lemma lem7631101 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7631102 : term98 = term6.
Proof. exact (EQ_MP (@lem7631101) (@lem940073)). Qed.
Lemma lem7631103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7631104 : term96 = term53.
Proof. exact (MK_COMB (@lem7631103) (@lem7631102)). Qed.
Lemma lem7631105 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7631106 : term117 = term86.
Proof. exact (MK_COMB (@lem7631105) (@lem7631104)). Qed.
Lemma lem7631107 : term112 = term86.
Proof. exact (TRANS (@lem7631100) (@lem7631106)). Qed.
Lemma lem7631108 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7631109 : term214 = term206.
Proof. exact (MK_COMB (@lem7631108) (@lem7631107)). Qed.
Lemma lem7631110 : term215 = term208.
Proof. exact (MK_COMB (@lem7631109) (@lem7631097)). Qed.
Lemma lem7631112 (m : nat) : (term216 m) = term46.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7631113 : term208 = term46.
Proof. exact (@lem7631112 term6). Qed.
Lemma lem7631114 : term215 = term46.
Proof. exact (TRANS (@lem7631110) (@lem7631113)). Qed.
Lemma lem7631115 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7631116 : term217 = term159.
Proof. exact (MK_COMB (@lem7631115) (@lem7631114)). Qed.
Lemma lem7631117 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem7631118 : term218 = term161.
Proof. exact (MK_COMB (@lem7631116) (@lem7631117)). Qed.
Lemma lem7631120 (x : nat) : (term162 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7631121 : term161 = term46.
Proof. exact (@lem7631120 term6). Qed.
Lemma lem7631122 : term218 = term46.
Proof. exact (TRANS (@lem7631118) (@lem7631121)). Qed.
Lemma lem7631124 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7631125 : term95 = term96.
Proof. exact (@lem7631124 term6 term6). Qed.
Lemma lem7631126 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7631127 : term98 = term6.
Proof. exact (EQ_MP (@lem7631126) (@lem940073)). Qed.
Lemma lem7631128 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7631129 : term96 = term53.
Proof. exact (MK_COMB (@lem7631128) (@lem7631127)). Qed.
Lemma lem7631130 : term95 = term53.
Proof. exact (TRANS (@lem7631125) (@lem7631129)). Qed.
Lemma lem7631131 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem7631132 : term163 = term161.
Proof. exact (MK_COMB (@lem7631131) (@lem7631130)). Qed.
Lemma lem7631134 (x : nat) : (term162 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7631135 : term161 = term46.
Proof. exact (@lem7631134 term6). Qed.
Lemma lem7631136 : term163 = term46.
Proof. exact (TRANS (@lem7631132) (@lem7631135)). Qed.
Lemma lem7631137 : term46 = term163.
Proof. exact (SYM (@lem7631136)). Qed.
Lemma lem7631138 : term218 = term163.
Proof. exact (TRANS (@lem7631122) (@lem7631137)). Qed.
Lemma lem7631139 : term209 = term83.
Proof. exact (@lem7631089 (@lem7631138)). Qed.
Lemma lem7631140 : term208 = term83.
Proof. exact (TRANS (@lem7631055) (@lem7631139)). Qed.
Lemma lem7631142 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7631143 : term83 = term46.
Proof. exact (@lem7631142 term46). Qed.
Lemma lem7631144 : term208 = term46.
Proof. exact (TRANS (@lem7631140) (@lem7631143)). Qed.
Lemma lem7631145 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7631146 : term219 = term159.
Proof. exact (MK_COMB (@lem7631145) (@lem7631144)). Qed.
Lemma lem7631147 (_98352 : int) : (real_of_int _98352) = (real_of_int _98352).
Proof. exact (eq_refl (real_of_int _98352)). Qed.
Lemma lem7631148 (_98352 : int) : (term205 _98352) = (term220 _98352).
Proof. exact (MK_COMB (@lem7631146) (@lem7631147 _98352)). Qed.
Lemma lem7631149 (_98352 : int) : (term204 _98352) = (term220 _98352).
Proof. exact (TRANS (@lem7631046 _98352) (@lem7631148 _98352)). Qed.
Lemma lem7631150 (_98352 : int) : (term220 _98352) = term46.
Proof. exact (@lem1982719 (real_of_int _98352)). Qed.
Lemma lem7631151 (_98352 : int) : (term204 _98352) = term46.
Proof. exact (TRANS (@lem7631149 _98352) (@lem7631150 _98352)). Qed.
Lemma lem7631152 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7631153 (_98352 : int) : (term234 _98352) = term235.
Proof. exact (MK_COMB (@lem7631152) (@lem7631151 _98352)). Qed.
Lemma lem7631154 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem7631155 (_98352 : int) : (term233 _98352) = term236.
Proof. exact (MK_COMB (@lem7631153 _98352) (@lem7631154)). Qed.
Lemma lem7631156 (_98352 : int) : (term232 _98352) = term236.
Proof. exact (TRANS (@lem7631045 _98352) (@lem7631155 _98352)). Qed.
Lemma lem7631157 : term236 = term86.
Proof. exact (@lem1982721 term86). Qed.
Lemma lem7631158 (_98352 : int) : (term232 _98352) = term86.
Proof. exact (TRANS (@lem7631156 _98352) (@lem7631157)). Qed.
Lemma lem7631159 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7631160 (_98352 : int) : (term237 _98352) = term238.
Proof. exact (MK_COMB (@lem7631159) (@lem7631158 _98352)). Qed.
Lemma lem7631161 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem7631162 (_98352 : int) : (term231 _98352) = term239.
Proof. exact (MK_COMB (@lem7631160 _98352) (@lem7631161)). Qed.
Lemma lem7631163 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term239.
Proof. exact (EQ_MP (@lem7631162 _98352) (@lem7631044 _98352 _98353 h1)). Qed.
Lemma lem7631165 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7631166 : term239 = term240.
Proof. exact (@lem7631165 term46 term86). Qed.
Lemma lem7631168 (x : nat) : (term84 x) = (term85 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7631169 : term86 = term87.
Proof. exact (@lem7631168 term6). Qed.
Lemma lem7631171 (x : nat) : (real_of_num x) = (term82 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7631172 : term46 = term83.
Proof. exact (@lem7631171 (NUMERAL 0)). Qed.
Lemma lem7631173 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7631174 : term48 = term241.
Proof. exact (MK_COMB (@lem7631173) (@lem7631172)). Qed.
Lemma lem7631175 : term240 = term242.
Proof. exact (MK_COMB (@lem7631174) (@lem7631169)). Qed.
Lemma lem7631176 : term243.
Proof. exact (@lem1980026 term46 term53 term86 term53). Qed.
Lemma lem7631178 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7631179 : term149 = term150.
Proof. exact (@lem7631178 (NUMERAL 0) term6). Qed.
Lemma lem7631180 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7631181 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7631182 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7631181 h1) (fun h1 : term150 = True => @lem7631180)). Qed.
Lemma lem7631183 : term150 = True.
Proof. exact (EQ_MP (@lem7631182) (@lem7631180)). Qed.
Lemma lem7631184 : term149 = True.
Proof. exact (TRANS (@lem7631179) (@lem7631183)). Qed.
Lemma lem7631185 : True = term149.
Proof. exact (SYM (@lem7631184)). Qed.
Lemma lem7631186 : term149.
Proof. exact (EQ_MP (@lem7631185) (@lem0)). Qed.
Lemma lem7631187 : term244.
Proof. exact (@lem7631176 (@lem7631186)). Qed.
Lemma lem7631189 (m : nat) (n : nat) : (term148 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7631190 : term149 = term150.
Proof. exact (@lem7631189 (NUMERAL 0) term6). Qed.
Lemma lem7631191 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7631192 (h1 : term151 = (BIT1 0)) : term150 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7631193 : (term151 = (BIT1 0)) = (term150 = True).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7631192 h1) (fun h1 : term150 = True => @lem7631191)). Qed.
Lemma lem7631194 : term150 = True.
Proof. exact (EQ_MP (@lem7631193) (@lem7631191)). Qed.
Lemma lem7631195 : term149 = True.
Proof. exact (TRANS (@lem7631190) (@lem7631194)). Qed.
Lemma lem7631196 : True = term149.
Proof. exact (SYM (@lem7631195)). Qed.
Lemma lem7631197 : term149.
Proof. exact (EQ_MP (@lem7631196) (@lem0)). Qed.
Lemma lem7631198 : term242 = term245.
Proof. exact (@lem7631187 (@lem7631197)). Qed.
Lemma lem7631200 (m : nat) (n : nat) : (term115 m n) = (term116 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7631201 : term112 = term117.
Proof. exact (@lem7631200 term6 term6). Qed.
Lemma lem7631202 : (term97 = (BIT1 0)) = (term98 = term6).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7631203 : term98 = term6.
Proof. exact (EQ_MP (@lem7631202) (@lem940073)). Qed.
Lemma lem7631204 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7631205 : term96 = term53.
Proof. exact (MK_COMB (@lem7631204) (@lem7631203)). Qed.
Lemma lem7631206 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7631207 : term117 = term86.
Proof. exact (MK_COMB (@lem7631206) (@lem7631205)). Qed.
Lemma lem7631208 : term112 = term86.
Proof. exact (TRANS (@lem7631201) (@lem7631207)). Qed.
Lemma lem7631210 (x : nat) : (term162 x) = term46.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7631211 : term161 = term46.
Proof. exact (@lem7631210 term6). Qed.
Lemma lem7631212 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7631213 : term246 = term48.
Proof. exact (MK_COMB (@lem7631212) (@lem7631211)). Qed.
Lemma lem7631214 : term245 = term240.
Proof. exact (MK_COMB (@lem7631213) (@lem7631208)). Qed.
Lemma lem7631216 (m : nat) (n : nat) : (term247 m n) = (term248 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7631217 : term240 = term249.
Proof. exact (@lem7631216 (NUMERAL 0) term6). Qed.
Lemma lem7631218 : term151 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7631219 (h1 : term151 = (BIT1 0)) : (term6 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7631220 : (term151 = (BIT1 0)) = ((term6 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term151 = (BIT1 0) => @lem7631219 h1) (fun h1 : (term6 = (NUMERAL 0)) = False => @lem7631218)). Qed.
Lemma lem7631221 : (term6 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7631220) (@lem7631218)). Qed.
Lemma lem7631222 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7631223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7631224 : term250 = (and True).
Proof. exact (MK_COMB (@lem7631223) (@lem7631222)). Qed.
Lemma lem7631225 : term249 = (True /\ False).
Proof. exact (MK_COMB (@lem7631224) (@lem7631221)). Qed.
Lemma lem7631227 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7631228 : term249 = False.
Proof. exact (TRANS (@lem7631225) (@lem7631227)). Qed.
Lemma lem7631229 : term240 = False.
Proof. exact (TRANS (@lem7631217) (@lem7631228)). Qed.
Lemma lem7631230 : term245 = False.
Proof. exact (TRANS (@lem7631214) (@lem7631229)). Qed.
Lemma lem7631231 : term242 = False.
Proof. exact (TRANS (@lem7631198) (@lem7631230)). Qed.
Lemma lem7631232 : term240 = False.
Proof. exact (TRANS (@lem7631175) (@lem7631231)). Qed.
Lemma lem7631233 : term239 = False.
Proof. exact (TRANS (@lem7631166) (@lem7631232)). Qed.
Lemma lem7631234 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : False.
Proof. exact (EQ_MP (@lem7631233) (@lem7631163 _98352 _98353 h1)). Qed.
Lemma lem7631236 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : term173 _98352 _98353.
Proof. exact (h1). Qed.
Lemma lem7631237 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : (term173 _98352 _98353) = False.
Proof. exact (prop_ext (fun h2 : term173 _98352 _98353 => @lem7631234 _98352 _98353 h1) (fun h2 : False => @lem7631236 _98352 _98353 h1)). Qed.
Lemma lem7631238 (_98352 : int) (_98353 : int) (h1 : term173 _98352 _98353) : False.
Proof. exact (EQ_MP (@lem7631237 _98352 _98353 h1) (@lem7631236 _98352 _98353 h1)). Qed.
Lemma lem7631239 (_98352 : int) (_98353 : int) (h1 : term78 _98352 _98353) : term78 _98352 _98353.
Proof. exact (h1). Qed.
Lemma lem7631240 (_98352 : int) (_98353 : int) (h1 : term78 _98352 _98353) : term173 _98352 _98353.
Proof. exact (EQ_MP (@lem7630611 _98352 _98353) (@lem7631239 _98352 _98353 h1)). Qed.
Lemma lem7631241 (_98352 : int) (_98353 : int) (h1 : term78 _98352 _98353) : (term173 _98352 _98353) = False.
Proof. exact (prop_ext (fun h2 : term173 _98352 _98353 => @lem7631238 _98352 _98353 h2) (fun h2 : False => @lem7631240 _98352 _98353 h1)). Qed.
Lemma lem7631242 (_98352 : int) (_98353 : int) (h1 : term78 _98352 _98353) : False.
Proof. exact (EQ_MP (@lem7631241 _98352 _98353 h1) (@lem7631240 _98352 _98353 h1)). Qed.
Lemma lem7631243 (_98352 : int) (_98353 : int) : term251 _98352 _98353.
Proof. exact (fun h0 : term78 _98352 _98353 => @lem7631242 _98352 _98353 h0). Qed.
Lemma lem7631244 (_98352 : int) (_98353 : int) : term252 _98352 _98353.
Proof. exact (@lem1386578 (term253 _98352 _98353)). Qed.
Lemma lem7631247 (_98352 : int) (_98353 : int) : term253 _98352 _98353.
Proof. exact (@lem7631244 _98352 _98353 (@lem7631243 _98352 _98353)). Qed.
Lemma lem7631248 (_98352 : int) (_98353 : int) : (term76 _98352 _98353) = (term39 _98352 _98353).
Proof. exact (SYM (@lem7630194 _98352 _98353)). Qed.
Lemma lem7631249 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7631250 (_98352 : int) (_98353 : int) : (term253 _98352 _98353) = (term19 _98352 _98353).
Proof. exact (MK_COMB (@lem7631249) (@lem7631248 _98352 _98353)). Qed.
Lemma lem7631251 (_98352 : int) (_98353 : int) : term19 _98352 _98353.
Proof. exact (EQ_MP (@lem7631250 _98352 _98353) (@lem7631247 _98352 _98353)). Qed.
Lemma lem7631252 (_98352 : int) (_98353 : int) : term20 _98352 _98353.
Proof. exact (EQ_MP (@lem7630069 _98352 _98353) (@lem7631251 _98352 _98353)). Qed.
Lemma lem7631253 (a : nat) (b : nat) : term254 a b.
Proof. exact (@lem7631252 (int_of_num a) (int_of_num b)). Qed.
Lemma lem7631254 (a : nat) (b : nat) : term255 a b.
Proof. exact (@lem7631253 a b (@lem7630065 a)). Qed.
Lemma lem7631255 (a : nat) (b : nat) : term16 a b.
Proof. exact (@lem7631254 a b (@lem7630068 b)). Qed.
Lemma lem7631256 (a : nat) (b : nat) : (term16 a b) = (term0 a b).
Proof. exact (SYM (@lem7630062 a b)). Qed.
Lemma lem7631257 (a : nat) (b : nat) : term0 a b.
Proof. exact (EQ_MP (@lem7631256 a b) (@lem7631255 a b)). Qed.
Lemma lem7631258 (a : nat) (h1 : term2 a) : term2 a.
Proof. exact (h1). Qed.
Lemma lem7631259 (b : nat) (a : nat) (h1 : term2 a) : term3 a b.
Proof. exact (@lem7631257 a b (@lem7631258 a h1)). Qed.
Lemma lem7631260 (a : nat) (b : nat) : (term3 a b) = ((term3 a b) = True).
Proof. exact (@lem7 (term3 a b)). Qed.
Lemma lem7631261 (b : nat) (a : nat) (h1 : term2 a) : (term3 a b) = True.
Proof. exact (EQ_MP (@lem7631260 a b) (@lem7631259 b a h1)). Qed.
Lemma lem7631267 {A : Type'} (s : A -> Prop) : term256 A s.
Proof. exact (@lem7594654 A s). Qed.
Lemma lem7631268 {A : Type'} (s : A -> Prop) : (term256 A s) = (term257 A s).
Proof. exact (eq_refl (term256 A s)). Qed.
Lemma lem7631269 {A : Type'} (s : A -> Prop) : term257 A s.
Proof. exact (EQ_MP (@lem7631268 A s) (@lem7631267 A s)). Qed.
Lemma lem7631270 {A : Type'} (s : A -> Prop) : (term257 A s) = ((term257 A s) = True).
Proof. exact (@lem7 (term257 A s)). Qed.
Lemma lem7631272 (n : nat) : term258 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem7631273 (n : nat) : (term258 n) = (Peano.le n n).
Proof. exact (eq_refl (term258 n)). Qed.
Lemma lem7631274 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem7631273 n) (@lem7631272 n)). Qed.
Lemma lem7631275 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem7631277 (m : nat) : term259 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7631278 (m : nat) : (term259 m) = (term260 m).
Proof. exact (eq_refl (term259 m)). Qed.
Lemma lem7631279 (m : nat) : term260 m.
Proof. exact (EQ_MP (@lem7631278 m) (@lem7631277 m)). Qed.
Lemma lem7631280 (m : nat) (n : nat) : term261 m n.
Proof. exact (@lem7631279 m n). Qed.
Lemma lem7631281 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (eq_refl (term261 m n)). Qed.
Lemma lem7631282 (m : nat) (n : nat) : term262 m n.
Proof. exact (EQ_MP (@lem7631281 m n) (@lem7631280 m n)). Qed.
Lemma lem7631283 (m : nat) (n : nat) (p : nat) : term263 m n p.
Proof. exact (@lem7631282 m n p). Qed.
Lemma lem7631284 (m : nat) (p : nat) (n : nat) : (term263 m n p) = ((term264 p m n) = (term265 m p n)).
Proof. exact (eq_refl (term263 m n p)). Qed.
Lemma lem7631287 (m : nat) (p : nat) (n : nat) : (term264 p m n) = (term265 m p n).
Proof. exact (EQ_MP (@lem7631284 m p n) (@lem7631283 m n p)). Qed.
Lemma lem7631288 {A B : Type'} : (term266 A B) = (term267 A B).
Proof. exact (@lem7631287 term6 term6 (term268 A B)). Qed.
Lemma lem7631292 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem7631275 n) (@lem7631274 n)). Qed.
Lemma lem7631293 : term269 = True.
Proof. exact (@lem7631292 term6). Qed.
Lemma lem7631294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7631295 : term270 = (and True).
Proof. exact (MK_COMB (@lem7631294) (@lem7631293)). Qed.
Lemma lem7631297 (a : nat) (b : nat) : term271 a b.
Proof. exact (fun h0 : term2 a => @lem7631261 b a h0). Qed.
Lemma lem7631298 {A B : Type'} : term272 A B.
Proof. exact (@lem7631297 (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))). Qed.
Lemma lem7631300 {A : Type'} (s : A -> Prop) : (term257 A s) = True.
Proof. exact (EQ_MP (@lem7631270 A s) (@lem7631269 A s)). Qed.
Lemma lem7631301 {A : Type'} (s : A -> Prop) : (term257 A s) = True.
Proof. exact (@lem7631300 A s). Qed.
Lemma lem7631302 {A : Type'} : (term273 A) = True.
Proof. exact (@lem7631301 A (@UNIV A)). Qed.
Lemma lem7631303 {A : Type'} : True = (term273 A).
Proof. exact (SYM (@lem7631302 A)). Qed.
Lemma lem7631304 {A : Type'} : term273 A.
Proof. exact (EQ_MP (@lem7631303 A) (@lem0)). Qed.
Lemma lem7631305 {A B : Type'} : (term274 A B) = True.
Proof. exact (@lem7631298 A B (@lem7631304 A)). Qed.
Lemma lem7631306 {A B : Type'} : (term267 A B) = (True /\ True).
Proof. exact (MK_COMB (@lem7631295) (@lem7631305 A B)). Qed.
Lemma lem7631308 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7631309 : (True /\ True) = True.
Proof. exact (@lem7631308 True). Qed.
Lemma lem7631310 {A B : Type'} : (term267 A B) = True.
Proof. exact (TRANS (@lem7631306 A B) (@lem7631309)). Qed.
Lemma lem7631311 {A B : Type'} : (term266 A B) = True.
Proof. exact (TRANS (@lem7631288 A B) (@lem7631310 A B)). Qed.
Lemma lem7631312 {A B : Type'} : True = (term266 A B).
Proof. exact (SYM (@lem7631311 A B)). Qed.
Lemma lem7631313 {A B : Type'} : term266 A B.
Proof. exact (EQ_MP (@lem7631312 A B) (@lem0)). Qed.
Lemma lem7631314 {A B : Type'} : term275 A B.
Proof. exact (ex_intro (term276 A B) term6 (@lem7631313 A B)). Qed.
Lemma lem7631316 {A : Type'} : (@ex A) = (term277 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem7631317 : (@ex nat) = term278.
Proof. exact (@lem7631316 nat). Qed.
Lemma lem7631318 {A B : Type'} : (term276 A B) = (term276 A B).
Proof. exact (eq_refl (term276 A B)). Qed.
Lemma lem7631319 {A B : Type'} : (term275 A B) = (term279 A B).
Proof. exact (MK_COMB (@lem7631317) (@lem7631318 A B)). Qed.
Lemma lem7631320 {A B : Type'} : (term279 A B) = (term280 A B).
Proof. exact (eq_refl (term279 A B)). Qed.
Lemma lem7631321 {A B : Type'} : (term275 A B) = (term280 A B).
Proof. exact (TRANS (@lem7631319 A B) (@lem7631320 A B)). Qed.
Lemma lem7631322 {A B : Type'} : term280 A B.
Proof. exact (EQ_MP (@lem7631321 A B) (@lem7631314 A B)). Qed.
Lemma lem7631323 {A B : Type'} (a : finite_sum A B) : (term281 A B a) = a.
Proof. exact (@axiom_31 A B a). Qed.
Lemma lem7631324 {A B : Type'} (r : nat) : (term282 A B r) = ((term283 A B r) = r).
Proof. exact (@axiom_32 A B r). Qed.
Lemma lem7631327 {A B : Type'} (r : nat) : (term282 A B r) = (term284 A B r).
Proof. exact (eq_refl (term282 A B r)). Qed.
Lemma lem7631328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7631329 {A B : Type'} (r : nat) : (term285 A B r) = (term286 A B r).
Proof. exact (MK_COMB (@lem7631328) (@lem7631327 A B r)). Qed.
Lemma lem7631330 {A B : Type'} (r : nat) : ((term283 A B r) = r) = ((term283 A B r) = r).
Proof. exact (eq_refl ((term283 A B r) = r)). Qed.
Lemma lem7631331 {A B : Type'} (r : nat) : ((term282 A B r) = ((term283 A B r) = r)) = ((term284 A B r) = ((term283 A B r) = r)).
Proof. exact (MK_COMB (@lem7631329 A B r) (@lem7631330 A B r)). Qed.
Lemma lem7631332 {A B : Type'} (r : nat) : (term284 A B r) = ((term283 A B r) = r).
Proof. exact (EQ_MP (@lem7631331 A B r) (@lem7631324 A B r)). Qed.
Lemma lem7631333 {A B : Type'} : term287 A B.
Proof. exact (fun r : nat => @lem7631332 A B r). Qed.
Lemma lem7631334 {A B : Type'} : term288 A B.
Proof. exact (fun a : finite_sum A B => @lem7631323 A B a). Qed.
Lemma lem7631335 {A B : Type'} : term289 A B.
Proof. exact (conj (@lem7631334 A B) (@lem7631333 A B)). Qed.
