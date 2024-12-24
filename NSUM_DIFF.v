Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_DIFF_term_abbrevs.
Require Import INT_POS_spec.
Require Import ITERATE_DIFF_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032098_spec.
Require Import thm1032781_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1393126_spec.
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm196_spec.
Require Import thm197_spec.
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
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988330_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
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
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem6925120 (x : nat) (y : nat) (z : nat) : (term0 x y z) = (term1 x y z).
Proof. exact (@lem17265 ((Nat.add x z) = y) (x = (Nat.sub y z))). Qed.
Lemma lem6925121 (z : nat) (y : nat) (x : nat) : (term2 x y z) = (term3 z y x).
Proof. exact (@lem1032781 y z (term4 z y x)). Qed.
Lemma lem6925122 (z : nat) (y : nat) (x : nat) (d : nat) : (term5 z y x d) = (term6 z y x d).
Proof. exact (eq_refl (term5 z y x d)). Qed.
Lemma lem6925123 (y : nat) (z : nat) (d : nat) : (term7 y z d) = (term7 y z d).
Proof. exact (eq_refl (term7 y z d)). Qed.
Lemma lem6925124 (z : nat) (y : nat) (x : nat) (d : nat) : (term8 z y x d) = (term9 z y x d).
Proof. exact (MK_COMB (@lem6925123 y z d) (@lem6925122 z y x d)). Qed.
Lemma lem6925125 (z : nat) (y : nat) (x : nat) : (term10 z y x) = (term11 z y x).
Proof. exact (fun_ext (fun d : nat => @lem6925124 z y x d)). Qed.
Lemma lem6925126 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6925127 (z : nat) (y : nat) (x : nat) : (term3 z y x) = (term12 z y x).
Proof. exact (MK_COMB (@lem6925126) (@lem6925125 z y x)). Qed.
Lemma lem6925128 (x : nat) (y : nat) (z : nat) : (term2 x y z) = (term1 x y z).
Proof. exact (eq_refl (term2 x y z)). Qed.
Lemma lem6925129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6925130 (x : nat) (y : nat) (z : nat) : (term13 x y z) = (term14 x y z).
Proof. exact (MK_COMB (@lem6925129) (@lem6925128 x y z)). Qed.
Lemma lem6925131 (z : nat) (y : nat) (x : nat) : ((term2 x y z) = (term3 z y x)) = ((term1 x y z) = (term12 z y x)).
Proof. exact (MK_COMB (@lem6925130 x y z) (@lem6925127 z y x)). Qed.
Lemma lem6925132 (z : nat) (y : nat) (x : nat) : (term1 x y z) = (term12 z y x).
Proof. exact (EQ_MP (@lem6925131 z y x) (@lem6925121 z y x)). Qed.
Lemma lem6925133 (z : nat) (y : nat) (x : nat) (d : nat) : (term9 z y x d) = (term9 z y x d).
Proof. exact (eq_refl (term9 z y x d)). Qed.
Lemma lem6925134 (z : nat) (y : nat) (x : nat) : (term11 z y x) = (term11 z y x).
Proof. exact (fun_ext (fun d : nat => @lem6925133 z y x d)). Qed.
Lemma lem6925135 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6925136 (z : nat) (y : nat) (x : nat) : (term12 z y x) = (term12 z y x).
Proof. exact (MK_COMB (@lem6925135) (@lem6925134 z y x)). Qed.
Lemma lem6925137 (x : nat) (y : nat) (z : nat) : (term14 x y z) = (term14 x y z).
Proof. exact (eq_refl (term14 x y z)). Qed.
Lemma lem6925138 (z : nat) (y : nat) (x : nat) : ((term1 x y z) = (term12 z y x)) = ((term1 x y z) = (term12 z y x)).
Proof. exact (MK_COMB (@lem6925137 x y z) (@lem6925136 z y x)). Qed.
Lemma lem6925139 (z : nat) (y : nat) (x : nat) : (term1 x y z) = (term12 z y x).
Proof. exact (EQ_MP (@lem6925138 z y x) (@lem6925132 z y x)). Qed.
Lemma lem6925166 (z : nat) (y : nat) (x : nat) : (term0 x y z) = (term12 z y x).
Proof. exact (TRANS (@lem6925120 x y z) (@lem6925139 z y x)). Qed.
Lemma lem6925187 (z : nat) (y : nat) (x : nat) (d : nat) : (term6 z y x d) = (term6 z y x d).
Proof. exact (eq_refl (term6 z y x d)). Qed.
Lemma lem6925204 (y : nat) (z : nat) (d : nat) : (term15 y z d) = (term15 y z d).
Proof. exact (eq_refl (term15 y z d)). Qed.
Lemma lem6925211 (d : nat) (z : nat) : (Nat.add z d) = (Nat.add d z).
Proof. exact (@lem1032098 d z). Qed.
Lemma lem6925214 (y : nat) : (@eq nat y) = (@eq nat y).
Proof. exact (eq_refl (@eq nat y)). Qed.
Lemma lem6925215 (y : nat) (d : nat) (z : nat) : (y = (Nat.add z d)) = (y = (Nat.add d z)).
Proof. exact (MK_COMB (@lem6925214 y) (@lem6925211 d z)). Qed.
Lemma lem6925216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6925217 (y : nat) (d : nat) (z : nat) : (term16 y z d) = (term16 y d z).
Proof. exact (MK_COMB (@lem6925216) (@lem6925215 y d z)). Qed.
Lemma lem6925218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925219 (y : nat) (d : nat) (z : nat) : (term17 y z d) = (term17 y d z).
Proof. exact (MK_COMB (@lem6925218) (@lem6925217 y d z)). Qed.
Lemma lem6925220 (y : nat) (z : nat) (d : nat) : (term18 y z d) = (term19 y z d).
Proof. exact (MK_COMB (@lem6925219 y d z) (@lem6925204 y z d)). Qed.
Lemma lem6925221 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6925222 (y : nat) (z : nat) (d : nat) : (term7 y z d) = (term20 y z d).
Proof. exact (MK_COMB (@lem6925221) (@lem6925220 y z d)). Qed.
Lemma lem6925223 (z : nat) (y : nat) (x : nat) (d : nat) : (term9 z y x d) = (term21 z y x d).
Proof. exact (MK_COMB (@lem6925222 y z d) (@lem6925187 z y x d)). Qed.
Lemma lem6925224 (z : nat) (y : nat) (x : nat) : (term11 z y x) = (term22 z y x).
Proof. exact (fun_ext (fun d : nat => @lem6925223 z y x d)). Qed.
Lemma lem6925225 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6925226 (z : nat) (y : nat) (x : nat) : (term12 z y x) = (term23 z y x).
Proof. exact (MK_COMB (@lem6925225) (@lem6925224 z y x)). Qed.
Lemma lem6925229 (z : nat) (y : nat) (x : nat) : (term0 x y z) = (term23 z y x).
Proof. exact (TRANS (@lem6925166 z y x) (@lem6925226 z y x)). Qed.
Lemma lem6925231 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6925232 (y : nat) (d : nat) (z : nat) : (y = (Nat.add d z)) = ((int_of_num y) = (term24 d z)).
Proof. exact (@lem6925231 y (Nat.add d z)). Qed.
Lemma lem6925236 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6925237 (d : nat) (z : nat) : (term24 d z) = (term25 d z).
Proof. exact (@lem6925236 d z). Qed.
Lemma lem6925238 (y : nat) : (term26 y) = (term26 y).
Proof. exact (eq_refl (term26 y)). Qed.
Lemma lem6925239 (y : nat) (d : nat) (z : nat) : ((int_of_num y) = (term24 d z)) = ((int_of_num y) = (term25 d z)).
Proof. exact (MK_COMB (@lem6925238 y) (@lem6925237 d z)). Qed.
Lemma lem6925240 (y : nat) (d : nat) (z : nat) : (y = (Nat.add d z)) = ((int_of_num y) = (term25 d z)).
Proof. exact (TRANS (@lem6925232 y d z) (@lem6925239 y d z)). Qed.
Lemma lem6925241 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6925242 (y : nat) (d : nat) (z : nat) : (term16 y d z) = (term27 y d z).
Proof. exact (MK_COMB (@lem6925241) (@lem6925240 y d z)). Qed.
Lemma lem6925243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925244 (y : nat) (d : nat) (z : nat) : (term17 y d z) = (term28 y d z).
Proof. exact (MK_COMB (@lem6925243) (@lem6925242 y d z)). Qed.
Lemma lem6925246 (m : nat) (n : nat) : (Peano.lt m n) = (term29 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem6925247 (y : nat) (z : nat) : (Peano.lt y z) = (term29 y z).
Proof. exact (@lem6925246 y z). Qed.
Lemma lem6925248 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6925249 (y : nat) (z : nat) : (term30 y z) = (term31 y z).
Proof. exact (MK_COMB (@lem6925248) (@lem6925247 y z)). Qed.
Lemma lem6925250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6925251 (y : nat) (z : nat) : (term32 y z) = (term33 y z).
Proof. exact (MK_COMB (@lem6925250) (@lem6925249 y z)). Qed.
Lemma lem6925253 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6925254 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term34).
Proof. exact (@lem6925253 d (NUMERAL 0)). Qed.
Lemma lem6925257 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6925258 (d : nat) : (term35 d) = (term36 d).
Proof. exact (MK_COMB (@lem6925257) (@lem6925254 d)). Qed.
Lemma lem6925259 (y : nat) (z : nat) (d : nat) : (term15 y z d) = (term37 y z d).
Proof. exact (MK_COMB (@lem6925251 y z) (@lem6925258 d)). Qed.
Lemma lem6925260 (y : nat) (z : nat) (d : nat) : (term19 y z d) = (term38 y z d).
Proof. exact (MK_COMB (@lem6925244 y d z) (@lem6925259 y z d)). Qed.
Lemma lem6925261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6925262 (y : nat) (z : nat) (d : nat) : (term20 y z d) = (term39 y z d).
Proof. exact (MK_COMB (@lem6925261) (@lem6925260 y z d)). Qed.
Lemma lem6925264 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6925265 (x : nat) (z : nat) (y : nat) : ((Nat.add x z) = y) = ((term24 x z) = (int_of_num y)).
Proof. exact (@lem6925264 (Nat.add x z) y). Qed.
Lemma lem6925269 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6925270 (x : nat) (z : nat) : (term24 x z) = (term25 x z).
Proof. exact (@lem6925269 x z). Qed.
Lemma lem6925271 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem6925272 (x : nat) (z : nat) : (term40 x z) = (term41 x z).
Proof. exact (MK_COMB (@lem6925271) (@lem6925270 x z)). Qed.
Lemma lem6925273 (y : nat) : (int_of_num y) = (int_of_num y).
Proof. exact (eq_refl (int_of_num y)). Qed.
Lemma lem6925274 (x : nat) (z : nat) (y : nat) : ((term24 x z) = (int_of_num y)) = ((term25 x z) = (int_of_num y)).
Proof. exact (MK_COMB (@lem6925272 x z) (@lem6925273 y)). Qed.
Lemma lem6925275 (x : nat) (z : nat) (y : nat) : ((Nat.add x z) = y) = ((term25 x z) = (int_of_num y)).
Proof. exact (TRANS (@lem6925265 x z y) (@lem6925274 x z y)). Qed.
Lemma lem6925276 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6925277 (x : nat) (z : nat) (y : nat) : (term42 x z y) = (term43 x z y).
Proof. exact (MK_COMB (@lem6925276) (@lem6925275 x z y)). Qed.
Lemma lem6925278 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6925279 (x : nat) (z : nat) (y : nat) : (term44 x z y) = (term45 x z y).
Proof. exact (MK_COMB (@lem6925278) (@lem6925277 x z y)). Qed.
Lemma lem6925281 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6925282 (x : nat) (d : nat) : (x = d) = ((int_of_num x) = (int_of_num d)).
Proof. exact (@lem6925281 x d). Qed.
Lemma lem6925285 (z : nat) (y : nat) (x : nat) (d : nat) : (term6 z y x d) = (term46 z y x d).
Proof. exact (MK_COMB (@lem6925279 x z y) (@lem6925282 x d)). Qed.
Lemma lem6925286 (z : nat) (y : nat) (x : nat) (d : nat) : (term21 z y x d) = (term47 z y x d).
Proof. exact (MK_COMB (@lem6925262 y z d) (@lem6925285 z y x d)). Qed.
Lemma lem6925287 (z : nat) (y : nat) (x : nat) : (term22 z y x) = (term48 z y x).
Proof. exact (fun_ext (fun d : nat => @lem6925286 z y x d)). Qed.
Lemma lem6925288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6925289 (z : nat) (y : nat) (x : nat) : (term23 z y x) = (term49 z y x).
Proof. exact (MK_COMB (@lem6925288) (@lem6925287 z y x)). Qed.
Lemma lem6925290 (z : nat) (y : nat) (x : nat) : (term0 x y z) = (term49 z y x).
Proof. exact (TRANS (@lem6925229 z y x) (@lem6925289 z y x)). Qed.
Lemma lem6925291 (d : nat) : term50 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem6925292 (d : nat) : (term50 d) = (term51 d).
Proof. exact (eq_refl (term50 d)). Qed.
Lemma lem6925293 (d : nat) : term51 d.
Proof. exact (EQ_MP (@lem6925292 d) (@lem6925291 d)). Qed.
Lemma lem6925294 (x : nat) : term50 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem6925295 (x : nat) : (term50 x) = (term51 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem6925296 (x : nat) : term51 x.
Proof. exact (EQ_MP (@lem6925295 x) (@lem6925294 x)). Qed.
Lemma lem6925297 (y : nat) : term50 y.
Proof. exact (@lem2307535 y). Qed.
Lemma lem6925298 (y : nat) : (term50 y) = (term51 y).
Proof. exact (eq_refl (term50 y)). Qed.
Lemma lem6925299 (y : nat) : term51 y.
Proof. exact (EQ_MP (@lem6925298 y) (@lem6925297 y)). Qed.
Lemma lem6925300 (z : nat) : term50 z.
Proof. exact (@lem2307535 z). Qed.
Lemma lem6925301 (z : nat) : (term50 z) = (term51 z).
Proof. exact (eq_refl (term50 z)). Qed.
Lemma lem6925302 (z : nat) : term51 z.
Proof. exact (EQ_MP (@lem6925301 z) (@lem6925300 z)). Qed.
Lemma lem6925303 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term52 _92403 _92402 _92401 _92400) = (term53 _92403 _92402 _92401 _92400).
Proof. exact (@lem2318604 (term53 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925331 (_92402 : int) (_92400 : int) (_92403 : int) : (term54 _92402 _92400 _92403) = (_92402 = (int_add _92400 _92403)).
Proof. exact (@lem16933 (_92402 = (int_add _92400 _92403))). Qed.
Lemma lem6925334 (_92402 : int) (_92403 : int) : (term55 _92402 _92403) = (int_lt _92402 _92403).
Proof. exact (@lem16933 (int_lt _92402 _92403)). Qed.
Lemma lem6925337 (_92400 : int) : (term56 _92400) = (_92400 = term34).
Proof. exact (@lem16933 (_92400 = term34)). Qed.
Lemma lem6925338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925339 (_92402 : int) (_92403 : int) : (term57 _92402 _92403) = (term58 _92402 _92403).
Proof. exact (MK_COMB (@lem6925338) (@lem6925334 _92402 _92403)). Qed.
Lemma lem6925340 (_92402 : int) (_92403 : int) (_92400 : int) : (term59 _92402 _92403 _92400) = (term60 _92402 _92403 _92400).
Proof. exact (MK_COMB (@lem6925339 _92402 _92403) (@lem6925337 _92400)). Qed.
Lemma lem6925341 (_92402 : int) (_92403 : int) (_92400 : int) : (term61 _92402 _92403 _92400) = (term59 _92402 _92403 _92400).
Proof. exact (@lem17160 (term62 _92402 _92403) (term63 _92400)). Qed.
Lemma lem6925342 (_92402 : int) (_92403 : int) (_92400 : int) : (term61 _92402 _92403 _92400) = (term60 _92402 _92403 _92400).
Proof. exact (TRANS (@lem6925341 _92402 _92403 _92400) (@lem6925340 _92402 _92403 _92400)). Qed.
Lemma lem6925343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6925344 (_92402 : int) (_92400 : int) (_92403 : int) : (term64 _92402 _92400 _92403) = (term65 _92402 _92400 _92403).
Proof. exact (MK_COMB (@lem6925343) (@lem6925331 _92402 _92400 _92403)). Qed.
Lemma lem6925345 (_92402 : int) (_92403 : int) (_92400 : int) : (term66 _92402 _92403 _92400) = (term67 _92402 _92403 _92400).
Proof. exact (MK_COMB (@lem6925344 _92402 _92400 _92403) (@lem6925342 _92402 _92403 _92400)). Qed.
Lemma lem6925346 (_92402 : int) (_92403 : int) (_92400 : int) : (term68 _92402 _92403 _92400) = (term66 _92402 _92403 _92400).
Proof. exact (@lem17045 (term69 _92402 _92400 _92403) (term70 _92402 _92403 _92400)). Qed.
Lemma lem6925347 (_92402 : int) (_92403 : int) (_92400 : int) : (term68 _92402 _92403 _92400) = (term67 _92402 _92403 _92400).
Proof. exact (TRANS (@lem6925346 _92402 _92403 _92400) (@lem6925345 _92402 _92403 _92400)). Qed.
Lemma lem6925350 (_92401 : int) (_92403 : int) (_92402 : int) : (term71 _92401 _92403 _92402) = ((int_add _92401 _92403) = _92402).
Proof. exact (@lem16933 ((int_add _92401 _92403) = _92402)). Qed.
Lemma lem6925351 (_92401 : int) (_92400 : int) : (term72 _92401 _92400) = (term72 _92401 _92400).
Proof. exact (eq_refl (term72 _92401 _92400)). Qed.
Lemma lem6925352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925353 (_92401 : int) (_92403 : int) (_92402 : int) : (term73 _92401 _92403 _92402) = (term74 _92401 _92403 _92402).
Proof. exact (MK_COMB (@lem6925352) (@lem6925350 _92401 _92403 _92402)). Qed.
Lemma lem6925354 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term75 _92403 _92402 _92401 _92400) = (term76 _92403 _92402 _92401 _92400).
Proof. exact (MK_COMB (@lem6925353 _92401 _92403 _92402) (@lem6925351 _92401 _92400)). Qed.
Lemma lem6925355 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term77 _92403 _92402 _92401 _92400) = (term75 _92403 _92402 _92401 _92400).
Proof. exact (@lem17160 (term78 _92401 _92403 _92402) (_92401 = _92400)). Qed.
Lemma lem6925356 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term77 _92403 _92402 _92401 _92400) = (term76 _92403 _92402 _92401 _92400).
Proof. exact (TRANS (@lem6925355 _92403 _92402 _92401 _92400) (@lem6925354 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925358 (_92402 : int) (_92403 : int) (_92400 : int) : (term79 _92402 _92403 _92400) = (term80 _92402 _92403 _92400).
Proof. exact (MK_COMB (@lem6925357) (@lem6925347 _92402 _92403 _92400)). Qed.
Lemma lem6925359 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term81 _92403 _92402 _92401 _92400) = (term82 _92403 _92402 _92401 _92400).
Proof. exact (MK_COMB (@lem6925358 _92402 _92403 _92400) (@lem6925356 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925360 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term83 _92403 _92402 _92401 _92400) = (term81 _92403 _92402 _92401 _92400).
Proof. exact (@lem17160 (term84 _92402 _92403 _92400) (term85 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925361 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term83 _92403 _92402 _92401 _92400) = (term82 _92403 _92402 _92401 _92400).
Proof. exact (TRANS (@lem6925360 _92403 _92402 _92401 _92400) (@lem6925359 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925363 (_92403 : int) : (term86 _92403) = (term86 _92403).
Proof. exact (eq_refl (term86 _92403)). Qed.
Lemma lem6925364 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term87 _92403 _92402 _92401 _92400) = (term88 _92403 _92402 _92401 _92400).
Proof. exact (MK_COMB (@lem6925363 _92403) (@lem6925361 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925365 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term89 _92403 _92402 _92401 _92400) = (term87 _92403 _92402 _92401 _92400).
Proof. exact (@lem17362 (term90 _92403) (term91 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925366 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term89 _92403 _92402 _92401 _92400) = (term88 _92403 _92402 _92401 _92400).
Proof. exact (TRANS (@lem6925365 _92403 _92402 _92401 _92400) (@lem6925364 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925368 (_92402 : int) : (term86 _92402) = (term86 _92402).
Proof. exact (eq_refl (term86 _92402)). Qed.
Lemma lem6925369 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term92 _92403 _92402 _92401 _92400) = (term93 _92403 _92402 _92401 _92400).
Proof. exact (MK_COMB (@lem6925368 _92402) (@lem6925366 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925370 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term94 _92403 _92402 _92401 _92400) = (term92 _92403 _92402 _92401 _92400).
Proof. exact (@lem17362 (term90 _92402) (term95 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925371 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term94 _92403 _92402 _92401 _92400) = (term93 _92403 _92402 _92401 _92400).
Proof. exact (TRANS (@lem6925370 _92403 _92402 _92401 _92400) (@lem6925369 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925373 (_92401 : int) : (term86 _92401) = (term86 _92401).
Proof. exact (eq_refl (term86 _92401)). Qed.
Lemma lem6925374 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term96 _92403 _92402 _92401 _92400) = (term97 _92403 _92402 _92401 _92400).
Proof. exact (MK_COMB (@lem6925373 _92401) (@lem6925371 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925375 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term98 _92403 _92402 _92401 _92400) = (term96 _92403 _92402 _92401 _92400).
Proof. exact (@lem17362 (term90 _92401) (term99 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925376 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term98 _92403 _92402 _92401 _92400) = (term97 _92403 _92402 _92401 _92400).
Proof. exact (TRANS (@lem6925375 _92403 _92402 _92401 _92400) (@lem6925374 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925378 (_92400 : int) : (term86 _92400) = (term86 _92400).
Proof. exact (eq_refl (term86 _92400)). Qed.
Lemma lem6925379 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term100 _92403 _92402 _92401 _92400) = (term101 _92403 _92402 _92401 _92400).
Proof. exact (MK_COMB (@lem6925378 _92400) (@lem6925376 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925380 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term102 _92403 _92402 _92401 _92400) = (term100 _92403 _92402 _92401 _92400).
Proof. exact (@lem17362 (term90 _92400) (term103 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925418 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term102 _92403 _92402 _92401 _92400) = (term101 _92403 _92402 _92401 _92400).
Proof. exact (TRANS (@lem6925380 _92403 _92402 _92401 _92400) (@lem6925379 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6925421 (x : int) (y : int) : (int_le x y) = (term104 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6925422 (_92400 : int) : (term90 _92400) = (term105 _92400).
Proof. exact (@lem6925421 term34 _92400). Qed.
Lemma lem6925424 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6925425 : term107 = term108.
Proof. exact (@lem6925424 (NUMERAL 0)). Qed.
Lemma lem6925426 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6925427 : term109 = term110.
Proof. exact (MK_COMB (@lem6925426) (@lem6925425)). Qed.
Lemma lem6925428 (_92400 : int) : (real_of_int _92400) = (real_of_int _92400).
Proof. exact (eq_refl (real_of_int _92400)). Qed.
Lemma lem6925429 (_92400 : int) : (term105 _92400) = (term111 _92400).
Proof. exact (MK_COMB (@lem6925427) (@lem6925428 _92400)). Qed.
Lemma lem6925431 (_92400 : int) : (term90 _92400) = (term111 _92400).
Proof. exact (TRANS (@lem6925422 _92400) (@lem6925429 _92400)). Qed.
Lemma lem6925434 (x : int) (y : int) : (int_le x y) = (term104 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6925435 (_92401 : int) : (term90 _92401) = (term105 _92401).
Proof. exact (@lem6925434 term34 _92401). Qed.
Lemma lem6925437 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6925438 : term107 = term108.
Proof. exact (@lem6925437 (NUMERAL 0)). Qed.
Lemma lem6925439 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6925440 : term109 = term110.
Proof. exact (MK_COMB (@lem6925439) (@lem6925438)). Qed.
Lemma lem6925441 (_92401 : int) : (real_of_int _92401) = (real_of_int _92401).
Proof. exact (eq_refl (real_of_int _92401)). Qed.
Lemma lem6925442 (_92401 : int) : (term105 _92401) = (term111 _92401).
Proof. exact (MK_COMB (@lem6925440) (@lem6925441 _92401)). Qed.
Lemma lem6925444 (_92401 : int) : (term90 _92401) = (term111 _92401).
Proof. exact (TRANS (@lem6925435 _92401) (@lem6925442 _92401)). Qed.
Lemma lem6925447 (x : int) (y : int) : (int_le x y) = (term104 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6925448 (_92402 : int) : (term90 _92402) = (term105 _92402).
Proof. exact (@lem6925447 term34 _92402). Qed.
Lemma lem6925450 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6925451 : term107 = term108.
Proof. exact (@lem6925450 (NUMERAL 0)). Qed.
Lemma lem6925452 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6925453 : term109 = term110.
Proof. exact (MK_COMB (@lem6925452) (@lem6925451)). Qed.
Lemma lem6925454 (_92402 : int) : (real_of_int _92402) = (real_of_int _92402).
Proof. exact (eq_refl (real_of_int _92402)). Qed.
Lemma lem6925455 (_92402 : int) : (term105 _92402) = (term111 _92402).
Proof. exact (MK_COMB (@lem6925453) (@lem6925454 _92402)). Qed.
Lemma lem6925457 (_92402 : int) : (term90 _92402) = (term111 _92402).
Proof. exact (TRANS (@lem6925448 _92402) (@lem6925455 _92402)). Qed.
Lemma lem6925460 (x : int) (y : int) : (int_le x y) = (term104 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6925461 (_92403 : int) : (term90 _92403) = (term105 _92403).
Proof. exact (@lem6925460 term34 _92403). Qed.
Lemma lem6925463 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6925464 : term107 = term108.
Proof. exact (@lem6925463 (NUMERAL 0)). Qed.
Lemma lem6925465 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6925466 : term109 = term110.
Proof. exact (MK_COMB (@lem6925465) (@lem6925464)). Qed.
Lemma lem6925467 (_92403 : int) : (real_of_int _92403) = (real_of_int _92403).
Proof. exact (eq_refl (real_of_int _92403)). Qed.
Lemma lem6925468 (_92403 : int) : (term105 _92403) = (term111 _92403).
Proof. exact (MK_COMB (@lem6925466) (@lem6925467 _92403)). Qed.
Lemma lem6925470 (_92403 : int) : (term90 _92403) = (term111 _92403).
Proof. exact (TRANS (@lem6925461 _92403) (@lem6925468 _92403)). Qed.
Lemma lem6925473 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem6925474 (_92402 : int) (_92400 : int) (_92403 : int) : (_92402 = (int_add _92400 _92403)) = ((real_of_int _92402) = (term112 _92400 _92403)).
Proof. exact (@lem6925473 _92402 (int_add _92400 _92403)). Qed.
Lemma lem6925478 (x : int) (y : int) : (term112 x y) = (term113 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6925479 (_92400 : int) (_92403 : int) : (term112 _92400 _92403) = (term113 _92400 _92403).
Proof. exact (@lem6925478 _92400 _92403). Qed.
Lemma lem6925480 (_92402 : int) : (term114 _92402) = (term114 _92402).
Proof. exact (eq_refl (term114 _92402)). Qed.
Lemma lem6925481 (_92402 : int) (_92400 : int) (_92403 : int) : ((real_of_int _92402) = (term112 _92400 _92403)) = ((real_of_int _92402) = (term113 _92400 _92403)).
Proof. exact (MK_COMB (@lem6925480 _92402) (@lem6925479 _92400 _92403)). Qed.
Lemma lem6925483 (_92402 : int) (_92400 : int) (_92403 : int) : (_92402 = (int_add _92400 _92403)) = ((real_of_int _92402) = (term113 _92400 _92403)).
Proof. exact (TRANS (@lem6925474 _92402 _92400 _92403) (@lem6925481 _92402 _92400 _92403)). Qed.
Lemma lem6925485 (x : int) (y : int) : (int_lt x y) = (term115 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem6925486 (_92402 : int) (_92403 : int) : (int_lt _92402 _92403) = (term115 _92402 _92403).
Proof. exact (@lem6925485 _92402 _92403). Qed.
Lemma lem6925488 (x : int) (y : int) : (int_le x y) = (term104 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6925489 (_92402 : int) (_92403 : int) : (term115 _92402 _92403) = (term116 _92402 _92403).
Proof. exact (@lem6925488 (term117 _92402) _92403). Qed.
Lemma lem6925491 (x : int) (y : int) : (term112 x y) = (term113 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6925492 (_92402 : int) : (term118 _92402) = (term119 _92402).
Proof. exact (@lem6925491 _92402 term120). Qed.
Lemma lem6925494 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6925495 : term121 = term122.
Proof. exact (@lem6925494 term123). Qed.
Lemma lem6925496 (_92402 : int) : (term124 _92402) = (term124 _92402).
Proof. exact (eq_refl (term124 _92402)). Qed.
Lemma lem6925497 (_92402 : int) : (term119 _92402) = (term125 _92402).
Proof. exact (MK_COMB (@lem6925496 _92402) (@lem6925495)). Qed.
Lemma lem6925498 (_92402 : int) : (term118 _92402) = (term125 _92402).
Proof. exact (TRANS (@lem6925492 _92402) (@lem6925497 _92402)). Qed.
Lemma lem6925499 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6925500 (_92402 : int) : (term126 _92402) = (term127 _92402).
Proof. exact (MK_COMB (@lem6925499) (@lem6925498 _92402)). Qed.
Lemma lem6925501 (_92403 : int) : (real_of_int _92403) = (real_of_int _92403).
Proof. exact (eq_refl (real_of_int _92403)). Qed.
Lemma lem6925502 (_92402 : int) (_92403 : int) : (term116 _92402 _92403) = (term128 _92402 _92403).
Proof. exact (MK_COMB (@lem6925500 _92402) (@lem6925501 _92403)). Qed.
Lemma lem6925503 (_92402 : int) (_92403 : int) : (term115 _92402 _92403) = (term128 _92402 _92403).
Proof. exact (TRANS (@lem6925489 _92402 _92403) (@lem6925502 _92402 _92403)). Qed.
Lemma lem6925504 (_92402 : int) (_92403 : int) : (int_lt _92402 _92403) = (term128 _92402 _92403).
Proof. exact (TRANS (@lem6925486 _92402 _92403) (@lem6925503 _92402 _92403)). Qed.
Lemma lem6925507 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem6925508 (_92400 : int) : (_92400 = term34) = ((real_of_int _92400) = term107).
Proof. exact (@lem6925507 _92400 term34). Qed.
Lemma lem6925512 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6925513 : term107 = term108.
Proof. exact (@lem6925512 (NUMERAL 0)). Qed.
Lemma lem6925514 (_92400 : int) : (term114 _92400) = (term114 _92400).
Proof. exact (eq_refl (term114 _92400)). Qed.
Lemma lem6925515 (_92400 : int) : ((real_of_int _92400) = term107) = ((real_of_int _92400) = term108).
Proof. exact (MK_COMB (@lem6925514 _92400) (@lem6925513)). Qed.
Lemma lem6925517 (_92400 : int) : (_92400 = term34) = ((real_of_int _92400) = term108).
Proof. exact (TRANS (@lem6925508 _92400) (@lem6925515 _92400)). Qed.
Lemma lem6925518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925519 (_92402 : int) (_92403 : int) : (term58 _92402 _92403) = (term129 _92402 _92403).
Proof. exact (MK_COMB (@lem6925518) (@lem6925504 _92402 _92403)). Qed.
Lemma lem6925520 (_92402 : int) (_92403 : int) (_92400 : int) : (term60 _92402 _92403 _92400) = (term130 _92402 _92403 _92400).
Proof. exact (MK_COMB (@lem6925519 _92402 _92403) (@lem6925517 _92400)). Qed.
Lemma lem6925521 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6925522 (_92402 : int) (_92400 : int) (_92403 : int) : (term65 _92402 _92400 _92403) = (term131 _92402 _92400 _92403).
Proof. exact (MK_COMB (@lem6925521) (@lem6925483 _92402 _92400 _92403)). Qed.
Lemma lem6925523 (_92402 : int) (_92403 : int) (_92400 : int) : (term67 _92402 _92403 _92400) = (term132 _92402 _92403 _92400).
Proof. exact (MK_COMB (@lem6925522 _92402 _92400 _92403) (@lem6925520 _92402 _92403 _92400)). Qed.
Lemma lem6925526 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem6925527 (_92401 : int) (_92403 : int) (_92402 : int) : ((int_add _92401 _92403) = _92402) = ((term112 _92401 _92403) = (real_of_int _92402)).
Proof. exact (@lem6925526 (int_add _92401 _92403) _92402). Qed.
Lemma lem6925531 (x : int) (y : int) : (term112 x y) = (term113 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6925532 (_92401 : int) (_92403 : int) : (term112 _92401 _92403) = (term113 _92401 _92403).
Proof. exact (@lem6925531 _92401 _92403). Qed.
Lemma lem6925533 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6925534 (_92401 : int) (_92403 : int) : (term133 _92401 _92403) = (term134 _92401 _92403).
Proof. exact (MK_COMB (@lem6925533) (@lem6925532 _92401 _92403)). Qed.
Lemma lem6925535 (_92402 : int) : (real_of_int _92402) = (real_of_int _92402).
Proof. exact (eq_refl (real_of_int _92402)). Qed.
Lemma lem6925536 (_92401 : int) (_92403 : int) (_92402 : int) : ((term112 _92401 _92403) = (real_of_int _92402)) = ((term113 _92401 _92403) = (real_of_int _92402)).
Proof. exact (MK_COMB (@lem6925534 _92401 _92403) (@lem6925535 _92402)). Qed.
Lemma lem6925538 (_92401 : int) (_92403 : int) (_92402 : int) : ((int_add _92401 _92403) = _92402) = ((term113 _92401 _92403) = (real_of_int _92402)).
Proof. exact (TRANS (@lem6925527 _92401 _92403 _92402) (@lem6925536 _92401 _92403 _92402)). Qed.
Lemma lem6925540 (y : int) (x : int) : (term72 x y) = (term135 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6925541 (_92400 : int) (_92401 : int) : (term72 _92401 _92400) = (term135 _92400 _92401).
Proof. exact (@lem6925540 _92400 _92401). Qed.
Lemma lem6925543 (x : int) (y : int) : (int_le x y) = (term104 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6925544 (_92401 : int) (_92400 : int) : (term115 _92401 _92400) = (term116 _92401 _92400).
Proof. exact (@lem6925543 (term117 _92401) _92400). Qed.
Lemma lem6925546 (x : int) (y : int) : (term112 x y) = (term113 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6925547 (_92401 : int) : (term118 _92401) = (term119 _92401).
Proof. exact (@lem6925546 _92401 term120). Qed.
Lemma lem6925549 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6925550 : term121 = term122.
Proof. exact (@lem6925549 term123). Qed.
Lemma lem6925551 (_92401 : int) : (term124 _92401) = (term124 _92401).
Proof. exact (eq_refl (term124 _92401)). Qed.
Lemma lem6925552 (_92401 : int) : (term119 _92401) = (term125 _92401).
Proof. exact (MK_COMB (@lem6925551 _92401) (@lem6925550)). Qed.
Lemma lem6925553 (_92401 : int) : (term118 _92401) = (term125 _92401).
Proof. exact (TRANS (@lem6925547 _92401) (@lem6925552 _92401)). Qed.
Lemma lem6925554 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6925555 (_92401 : int) : (term126 _92401) = (term127 _92401).
Proof. exact (MK_COMB (@lem6925554) (@lem6925553 _92401)). Qed.
Lemma lem6925556 (_92400 : int) : (real_of_int _92400) = (real_of_int _92400).
Proof. exact (eq_refl (real_of_int _92400)). Qed.
Lemma lem6925557 (_92401 : int) (_92400 : int) : (term116 _92401 _92400) = (term128 _92401 _92400).
Proof. exact (MK_COMB (@lem6925555 _92401) (@lem6925556 _92400)). Qed.
Lemma lem6925558 (_92401 : int) (_92400 : int) : (term115 _92401 _92400) = (term128 _92401 _92400).
Proof. exact (TRANS (@lem6925544 _92401 _92400) (@lem6925557 _92401 _92400)). Qed.
Lemma lem6925559 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6925560 (_92401 : int) (_92400 : int) : (term136 _92401 _92400) = (term137 _92401 _92400).
Proof. exact (MK_COMB (@lem6925559) (@lem6925558 _92401 _92400)). Qed.
Lemma lem6925562 (x : int) (y : int) : (int_le x y) = (term104 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6925563 (_92400 : int) (_92401 : int) : (term115 _92400 _92401) = (term116 _92400 _92401).
Proof. exact (@lem6925562 (term117 _92400) _92401). Qed.
Lemma lem6925565 (x : int) (y : int) : (term112 x y) = (term113 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6925566 (_92400 : int) : (term118 _92400) = (term119 _92400).
Proof. exact (@lem6925565 _92400 term120). Qed.
Lemma lem6925568 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6925569 : term121 = term122.
Proof. exact (@lem6925568 term123). Qed.
Lemma lem6925570 (_92400 : int) : (term124 _92400) = (term124 _92400).
Proof. exact (eq_refl (term124 _92400)). Qed.
Lemma lem6925571 (_92400 : int) : (term119 _92400) = (term125 _92400).
Proof. exact (MK_COMB (@lem6925570 _92400) (@lem6925569)). Qed.
Lemma lem6925572 (_92400 : int) : (term118 _92400) = (term125 _92400).
Proof. exact (TRANS (@lem6925566 _92400) (@lem6925571 _92400)). Qed.
Lemma lem6925573 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6925574 (_92400 : int) : (term126 _92400) = (term127 _92400).
Proof. exact (MK_COMB (@lem6925573) (@lem6925572 _92400)). Qed.
Lemma lem6925575 (_92401 : int) : (real_of_int _92401) = (real_of_int _92401).
Proof. exact (eq_refl (real_of_int _92401)). Qed.
Lemma lem6925576 (_92400 : int) (_92401 : int) : (term116 _92400 _92401) = (term128 _92400 _92401).
Proof. exact (MK_COMB (@lem6925574 _92400) (@lem6925575 _92401)). Qed.
Lemma lem6925577 (_92400 : int) (_92401 : int) : (term115 _92400 _92401) = (term128 _92400 _92401).
Proof. exact (TRANS (@lem6925563 _92400 _92401) (@lem6925576 _92400 _92401)). Qed.
Lemma lem6925578 (_92400 : int) (_92401 : int) : (term135 _92400 _92401) = (term138 _92400 _92401).
Proof. exact (MK_COMB (@lem6925560 _92401 _92400) (@lem6925577 _92400 _92401)). Qed.
Lemma lem6925579 (_92400 : int) (_92401 : int) : (term72 _92401 _92400) = (term138 _92400 _92401).
Proof. exact (TRANS (@lem6925541 _92400 _92401) (@lem6925578 _92400 _92401)). Qed.
Lemma lem6925580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925581 (_92401 : int) (_92403 : int) (_92402 : int) : (term74 _92401 _92403 _92402) = (term139 _92401 _92403 _92402).
Proof. exact (MK_COMB (@lem6925580) (@lem6925538 _92401 _92403 _92402)). Qed.
Lemma lem6925582 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) : (term76 _92403 _92402 _92401 _92400) = (term140 _92403 _92402 _92400 _92401).
Proof. exact (MK_COMB (@lem6925581 _92401 _92403 _92402) (@lem6925579 _92400 _92401)). Qed.
Lemma lem6925583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925584 (_92402 : int) (_92403 : int) (_92400 : int) : (term80 _92402 _92403 _92400) = (term141 _92402 _92403 _92400).
Proof. exact (MK_COMB (@lem6925583) (@lem6925523 _92402 _92403 _92400)). Qed.
Lemma lem6925585 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) : (term82 _92403 _92402 _92401 _92400) = (term142 _92403 _92402 _92400 _92401).
Proof. exact (MK_COMB (@lem6925584 _92402 _92403 _92400) (@lem6925582 _92403 _92402 _92400 _92401)). Qed.
Lemma lem6925586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925587 (_92403 : int) : (term86 _92403) = (term143 _92403).
Proof. exact (MK_COMB (@lem6925586) (@lem6925470 _92403)). Qed.
Lemma lem6925588 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) : (term88 _92403 _92402 _92401 _92400) = (term144 _92403 _92402 _92400 _92401).
Proof. exact (MK_COMB (@lem6925587 _92403) (@lem6925585 _92403 _92402 _92400 _92401)). Qed.
Lemma lem6925589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925590 (_92402 : int) : (term86 _92402) = (term143 _92402).
Proof. exact (MK_COMB (@lem6925589) (@lem6925457 _92402)). Qed.
Lemma lem6925591 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) : (term93 _92403 _92402 _92401 _92400) = (term145 _92403 _92402 _92400 _92401).
Proof. exact (MK_COMB (@lem6925590 _92402) (@lem6925588 _92403 _92402 _92400 _92401)). Qed.
Lemma lem6925592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925593 (_92401 : int) : (term86 _92401) = (term143 _92401).
Proof. exact (MK_COMB (@lem6925592) (@lem6925444 _92401)). Qed.
Lemma lem6925594 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) : (term97 _92403 _92402 _92401 _92400) = (term146 _92403 _92402 _92400 _92401).
Proof. exact (MK_COMB (@lem6925593 _92401) (@lem6925591 _92403 _92402 _92400 _92401)). Qed.
Lemma lem6925595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6925596 (_92400 : int) : (term86 _92400) = (term143 _92400).
Proof. exact (MK_COMB (@lem6925595) (@lem6925431 _92400)). Qed.
Lemma lem6925597 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) : (term101 _92403 _92402 _92401 _92400) = (term147 _92403 _92402 _92400 _92401).
Proof. exact (MK_COMB (@lem6925596 _92400) (@lem6925594 _92403 _92402 _92400 _92401)). Qed.
Lemma lem6925598 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) : (term102 _92403 _92402 _92401 _92400) = (term147 _92403 _92402 _92400 _92401).
Proof. exact (TRANS (@lem6925418 _92403 _92402 _92401 _92400) (@lem6925597 _92403 _92402 _92400 _92401)). Qed.
Lemma lem6925602 (t : Prop) : (term148 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6925698 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) : (term149 _92403 _92402 _92400 _92401) = (term147 _92403 _92402 _92400 _92401).
Proof. exact (@lem6925602 (term147 _92403 _92402 _92400 _92401)). Qed.
Lemma lem6925699 (_92400 : int) : (term111 _92400) = (term150 _92400).
Proof. exact (@lem1988287 (real_of_int _92400) term108). Qed.
Lemma lem6925705 (_92400 : int) : (term151 _92400) = (term152 _92400).
Proof. exact (@lem1982792 (real_of_int _92400) term108). Qed.
Lemma lem6925707 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6925708 : term108 = term154.
Proof. exact (@lem6925707 (NUMERAL 0)). Qed.
Lemma lem6925710 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6925711 : term157 = term158.
Proof. exact (@lem6925710 term123). Qed.
Lemma lem6925712 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6925713 : term159 = term160.
Proof. exact (MK_COMB (@lem6925712) (@lem6925711)). Qed.
Lemma lem6925714 : term161 = term162.
Proof. exact (MK_COMB (@lem6925713) (@lem6925708)). Qed.
Lemma lem6925715 : term162 = term163.
Proof. exact (@lem1981613 term157 term108 term122 term122). Qed.
Lemma lem6925717 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6925718 : term166 = term167.
Proof. exact (@lem6925717 term123 term123). Qed.
Lemma lem6925719 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6925720 : term169 = term123.
Proof. exact (EQ_MP (@lem6925719) (@lem940073)). Qed.
Lemma lem6925721 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6925722 : term167 = term122.
Proof. exact (MK_COMB (@lem6925721) (@lem6925720)). Qed.
Lemma lem6925723 : term166 = term122.
Proof. exact (TRANS (@lem6925718) (@lem6925722)). Qed.
Lemma lem6925725 (x : nat) : (term170 x) = term108.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6925726 : term161 = term108.
Proof. exact (@lem6925725 term123). Qed.
Lemma lem6925727 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6925728 : term171 = term172.
Proof. exact (MK_COMB (@lem6925727) (@lem6925726)). Qed.
Lemma lem6925729 : term163 = term154.
Proof. exact (MK_COMB (@lem6925728) (@lem6925723)). Qed.
Lemma lem6925730 : term162 = term154.
Proof. exact (TRANS (@lem6925715) (@lem6925729)). Qed.
Lemma lem6925731 : term161 = term154.
Proof. exact (TRANS (@lem6925714) (@lem6925730)). Qed.
Lemma lem6925733 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6925734 : term154 = term108.
Proof. exact (@lem6925733 term108). Qed.
Lemma lem6925735 : term161 = term108.
Proof. exact (TRANS (@lem6925731) (@lem6925734)). Qed.
Lemma lem6925736 (_92400 : int) : (term124 _92400) = (term124 _92400).
Proof. exact (eq_refl (term124 _92400)). Qed.
Lemma lem6925737 (_92400 : int) : (term152 _92400) = (term174 _92400).
Proof. exact (MK_COMB (@lem6925736 _92400) (@lem6925735)). Qed.
Lemma lem6925738 (_92400 : int) : (term174 _92400) = (real_of_int _92400).
Proof. exact (@lem1982723 (real_of_int _92400)). Qed.
Lemma lem6925739 (_92400 : int) : (term152 _92400) = (real_of_int _92400).
Proof. exact (TRANS (@lem6925737 _92400) (@lem6925738 _92400)). Qed.
Lemma lem6925741 (_92400 : int) : (term151 _92400) = (real_of_int _92400).
Proof. exact (TRANS (@lem6925705 _92400) (@lem6925739 _92400)). Qed.
Lemma lem6925742 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6925743 (_92400 : int) : (term175 _92400) = (term176 _92400).
Proof. exact (MK_COMB (@lem6925742) (@lem6925741 _92400)). Qed.
Lemma lem6925744 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6925745 (_92400 : int) : (term150 _92400) = (term177 _92400).
Proof. exact (MK_COMB (@lem6925743 _92400) (@lem6925744)). Qed.
Lemma lem6925746 (_92400 : int) : (term111 _92400) = (term177 _92400).
Proof. exact (TRANS (@lem6925699 _92400) (@lem6925745 _92400)). Qed.
Lemma lem6925747 (_92401 : int) : (term111 _92401) = (term150 _92401).
Proof. exact (@lem1988287 (real_of_int _92401) term108). Qed.
Lemma lem6925753 (_92401 : int) : (term151 _92401) = (term152 _92401).
Proof. exact (@lem1982792 (real_of_int _92401) term108). Qed.
Lemma lem6925755 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6925756 : term108 = term154.
Proof. exact (@lem6925755 (NUMERAL 0)). Qed.
Lemma lem6925758 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6925759 : term157 = term158.
Proof. exact (@lem6925758 term123). Qed.
Lemma lem6925760 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6925761 : term159 = term160.
Proof. exact (MK_COMB (@lem6925760) (@lem6925759)). Qed.
Lemma lem6925762 : term161 = term162.
Proof. exact (MK_COMB (@lem6925761) (@lem6925756)). Qed.
Lemma lem6925763 : term162 = term163.
Proof. exact (@lem1981613 term157 term108 term122 term122). Qed.
Lemma lem6925765 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6925766 : term166 = term167.
Proof. exact (@lem6925765 term123 term123). Qed.
Lemma lem6925767 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6925768 : term169 = term123.
Proof. exact (EQ_MP (@lem6925767) (@lem940073)). Qed.
Lemma lem6925769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6925770 : term167 = term122.
Proof. exact (MK_COMB (@lem6925769) (@lem6925768)). Qed.
Lemma lem6925771 : term166 = term122.
Proof. exact (TRANS (@lem6925766) (@lem6925770)). Qed.
Lemma lem6925773 (x : nat) : (term170 x) = term108.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6925774 : term161 = term108.
Proof. exact (@lem6925773 term123). Qed.
Lemma lem6925775 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6925776 : term171 = term172.
Proof. exact (MK_COMB (@lem6925775) (@lem6925774)). Qed.
Lemma lem6925777 : term163 = term154.
Proof. exact (MK_COMB (@lem6925776) (@lem6925771)). Qed.
Lemma lem6925778 : term162 = term154.
Proof. exact (TRANS (@lem6925763) (@lem6925777)). Qed.
Lemma lem6925779 : term161 = term154.
Proof. exact (TRANS (@lem6925762) (@lem6925778)). Qed.
Lemma lem6925781 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6925782 : term154 = term108.
Proof. exact (@lem6925781 term108). Qed.
Lemma lem6925783 : term161 = term108.
Proof. exact (TRANS (@lem6925779) (@lem6925782)). Qed.
Lemma lem6925784 (_92401 : int) : (term124 _92401) = (term124 _92401).
Proof. exact (eq_refl (term124 _92401)). Qed.
Lemma lem6925785 (_92401 : int) : (term152 _92401) = (term174 _92401).
Proof. exact (MK_COMB (@lem6925784 _92401) (@lem6925783)). Qed.
Lemma lem6925786 (_92401 : int) : (term174 _92401) = (real_of_int _92401).
Proof. exact (@lem1982723 (real_of_int _92401)). Qed.
Lemma lem6925787 (_92401 : int) : (term152 _92401) = (real_of_int _92401).
Proof. exact (TRANS (@lem6925785 _92401) (@lem6925786 _92401)). Qed.
Lemma lem6925789 (_92401 : int) : (term151 _92401) = (real_of_int _92401).
Proof. exact (TRANS (@lem6925753 _92401) (@lem6925787 _92401)). Qed.
Lemma lem6925790 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6925791 (_92401 : int) : (term175 _92401) = (term176 _92401).
Proof. exact (MK_COMB (@lem6925790) (@lem6925789 _92401)). Qed.
Lemma lem6925792 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6925793 (_92401 : int) : (term150 _92401) = (term177 _92401).
Proof. exact (MK_COMB (@lem6925791 _92401) (@lem6925792)). Qed.
Lemma lem6925794 (_92401 : int) : (term111 _92401) = (term177 _92401).
Proof. exact (TRANS (@lem6925747 _92401) (@lem6925793 _92401)). Qed.
Lemma lem6925795 (_92402 : int) : (term111 _92402) = (term150 _92402).
Proof. exact (@lem1988287 (real_of_int _92402) term108). Qed.
Lemma lem6925801 (_92402 : int) : (term151 _92402) = (term152 _92402).
Proof. exact (@lem1982792 (real_of_int _92402) term108). Qed.
Lemma lem6925803 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6925804 : term108 = term154.
Proof. exact (@lem6925803 (NUMERAL 0)). Qed.
Lemma lem6925806 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6925807 : term157 = term158.
Proof. exact (@lem6925806 term123). Qed.
Lemma lem6925808 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6925809 : term159 = term160.
Proof. exact (MK_COMB (@lem6925808) (@lem6925807)). Qed.
Lemma lem6925810 : term161 = term162.
Proof. exact (MK_COMB (@lem6925809) (@lem6925804)). Qed.
Lemma lem6925811 : term162 = term163.
Proof. exact (@lem1981613 term157 term108 term122 term122). Qed.
Lemma lem6925813 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6925814 : term166 = term167.
Proof. exact (@lem6925813 term123 term123). Qed.
Lemma lem6925815 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6925816 : term169 = term123.
Proof. exact (EQ_MP (@lem6925815) (@lem940073)). Qed.
Lemma lem6925817 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6925818 : term167 = term122.
Proof. exact (MK_COMB (@lem6925817) (@lem6925816)). Qed.
Lemma lem6925819 : term166 = term122.
Proof. exact (TRANS (@lem6925814) (@lem6925818)). Qed.
Lemma lem6925821 (x : nat) : (term170 x) = term108.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6925822 : term161 = term108.
Proof. exact (@lem6925821 term123). Qed.
Lemma lem6925823 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6925824 : term171 = term172.
Proof. exact (MK_COMB (@lem6925823) (@lem6925822)). Qed.
Lemma lem6925825 : term163 = term154.
Proof. exact (MK_COMB (@lem6925824) (@lem6925819)). Qed.
Lemma lem6925826 : term162 = term154.
Proof. exact (TRANS (@lem6925811) (@lem6925825)). Qed.
Lemma lem6925827 : term161 = term154.
Proof. exact (TRANS (@lem6925810) (@lem6925826)). Qed.
Lemma lem6925829 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6925830 : term154 = term108.
Proof. exact (@lem6925829 term108). Qed.
Lemma lem6925831 : term161 = term108.
Proof. exact (TRANS (@lem6925827) (@lem6925830)). Qed.
Lemma lem6925832 (_92402 : int) : (term124 _92402) = (term124 _92402).
Proof. exact (eq_refl (term124 _92402)). Qed.
Lemma lem6925833 (_92402 : int) : (term152 _92402) = (term174 _92402).
Proof. exact (MK_COMB (@lem6925832 _92402) (@lem6925831)). Qed.
Lemma lem6925834 (_92402 : int) : (term174 _92402) = (real_of_int _92402).
Proof. exact (@lem1982723 (real_of_int _92402)). Qed.
Lemma lem6925835 (_92402 : int) : (term152 _92402) = (real_of_int _92402).
Proof. exact (TRANS (@lem6925833 _92402) (@lem6925834 _92402)). Qed.
Lemma lem6925837 (_92402 : int) : (term151 _92402) = (real_of_int _92402).
Proof. exact (TRANS (@lem6925801 _92402) (@lem6925835 _92402)). Qed.
Lemma lem6925838 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6925839 (_92402 : int) : (term175 _92402) = (term176 _92402).
Proof. exact (MK_COMB (@lem6925838) (@lem6925837 _92402)). Qed.
Lemma lem6925840 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6925841 (_92402 : int) : (term150 _92402) = (term177 _92402).
Proof. exact (MK_COMB (@lem6925839 _92402) (@lem6925840)). Qed.
Lemma lem6925842 (_92402 : int) : (term111 _92402) = (term177 _92402).
Proof. exact (TRANS (@lem6925795 _92402) (@lem6925841 _92402)). Qed.
Lemma lem6925843 (_92403 : int) : (term111 _92403) = (term150 _92403).
Proof. exact (@lem1988287 (real_of_int _92403) term108). Qed.
Lemma lem6925849 (_92403 : int) : (term151 _92403) = (term152 _92403).
Proof. exact (@lem1982792 (real_of_int _92403) term108). Qed.
Lemma lem6925851 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6925852 : term108 = term154.
Proof. exact (@lem6925851 (NUMERAL 0)). Qed.
Lemma lem6925854 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6925855 : term157 = term158.
Proof. exact (@lem6925854 term123). Qed.
Lemma lem6925856 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6925857 : term159 = term160.
Proof. exact (MK_COMB (@lem6925856) (@lem6925855)). Qed.
Lemma lem6925858 : term161 = term162.
Proof. exact (MK_COMB (@lem6925857) (@lem6925852)). Qed.
Lemma lem6925859 : term162 = term163.
Proof. exact (@lem1981613 term157 term108 term122 term122). Qed.
Lemma lem6925861 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6925862 : term166 = term167.
Proof. exact (@lem6925861 term123 term123). Qed.
Lemma lem6925863 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6925864 : term169 = term123.
Proof. exact (EQ_MP (@lem6925863) (@lem940073)). Qed.
Lemma lem6925865 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6925866 : term167 = term122.
Proof. exact (MK_COMB (@lem6925865) (@lem6925864)). Qed.
Lemma lem6925867 : term166 = term122.
Proof. exact (TRANS (@lem6925862) (@lem6925866)). Qed.
Lemma lem6925869 (x : nat) : (term170 x) = term108.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6925870 : term161 = term108.
Proof. exact (@lem6925869 term123). Qed.
Lemma lem6925871 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6925872 : term171 = term172.
Proof. exact (MK_COMB (@lem6925871) (@lem6925870)). Qed.
Lemma lem6925873 : term163 = term154.
Proof. exact (MK_COMB (@lem6925872) (@lem6925867)). Qed.
Lemma lem6925874 : term162 = term154.
Proof. exact (TRANS (@lem6925859) (@lem6925873)). Qed.
Lemma lem6925875 : term161 = term154.
Proof. exact (TRANS (@lem6925858) (@lem6925874)). Qed.
Lemma lem6925877 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6925878 : term154 = term108.
Proof. exact (@lem6925877 term108). Qed.
Lemma lem6925879 : term161 = term108.
Proof. exact (TRANS (@lem6925875) (@lem6925878)). Qed.
Lemma lem6925880 (_92403 : int) : (term124 _92403) = (term124 _92403).
Proof. exact (eq_refl (term124 _92403)). Qed.
Lemma lem6925881 (_92403 : int) : (term152 _92403) = (term174 _92403).
Proof. exact (MK_COMB (@lem6925880 _92403) (@lem6925879)). Qed.
Lemma lem6925882 (_92403 : int) : (term174 _92403) = (real_of_int _92403).
Proof. exact (@lem1982723 (real_of_int _92403)). Qed.
Lemma lem6925883 (_92403 : int) : (term152 _92403) = (real_of_int _92403).
Proof. exact (TRANS (@lem6925881 _92403) (@lem6925882 _92403)). Qed.
Lemma lem6925885 (_92403 : int) : (term151 _92403) = (real_of_int _92403).
Proof. exact (TRANS (@lem6925849 _92403) (@lem6925883 _92403)). Qed.
Lemma lem6925886 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6925887 (_92403 : int) : (term175 _92403) = (term176 _92403).
Proof. exact (MK_COMB (@lem6925886) (@lem6925885 _92403)). Qed.
Lemma lem6925888 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6925889 (_92403 : int) : (term150 _92403) = (term177 _92403).
Proof. exact (MK_COMB (@lem6925887 _92403) (@lem6925888)). Qed.
Lemma lem6925890 (_92403 : int) : (term111 _92403) = (term177 _92403).
Proof. exact (TRANS (@lem6925843 _92403) (@lem6925889 _92403)). Qed.
Lemma lem6925891 (_92402 : int) (_92400 : int) (_92403 : int) : ((real_of_int _92402) = (term113 _92400 _92403)) = ((term178 _92402 _92400 _92403) = term108).
Proof. exact (@lem1988293 (real_of_int _92402) (term113 _92400 _92403)). Qed.
Lemma lem6925903 (_92402 : int) (_92400 : int) (_92403 : int) : (term178 _92402 _92400 _92403) = (term179 _92402 _92400 _92403).
Proof. exact (@lem1982792 (real_of_int _92402) (term113 _92400 _92403)). Qed.
Lemma lem6925910 (_92400 : int) (_92403 : int) : (term180 _92400 _92403) = (term181 _92400 _92403).
Proof. exact (@lem1982781 (real_of_int _92400) term157 (real_of_int _92403)). Qed.
Lemma lem6925911 (_92402 : int) : (term124 _92402) = (term124 _92402).
Proof. exact (eq_refl (term124 _92402)). Qed.
Lemma lem6925912 (_92402 : int) (_92400 : int) (_92403 : int) : (term179 _92402 _92400 _92403) = (term182 _92402 _92400 _92403).
Proof. exact (MK_COMB (@lem6925911 _92402) (@lem6925910 _92400 _92403)). Qed.
Lemma lem6925917 (_92400 : int) (_92402 : int) (_92403 : int) : (term182 _92402 _92400 _92403) = (term183 _92400 _92402 _92403).
Proof. exact (@lem1982757 (term184 _92400) (real_of_int _92402) (term184 _92403)). Qed.
Lemma lem6925918 (_92400 : int) (_92402 : int) (_92403 : int) : (term179 _92402 _92400 _92403) = (term183 _92400 _92402 _92403).
Proof. exact (TRANS (@lem6925912 _92402 _92400 _92403) (@lem6925917 _92400 _92402 _92403)). Qed.
Lemma lem6925920 (_92400 : int) (_92402 : int) (_92403 : int) : (term178 _92402 _92400 _92403) = (term183 _92400 _92402 _92403).
Proof. exact (TRANS (@lem6925903 _92402 _92400 _92403) (@lem6925918 _92400 _92402 _92403)). Qed.
Lemma lem6925921 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6925922 (_92400 : int) (_92402 : int) (_92403 : int) : (term185 _92402 _92400 _92403) = (term186 _92400 _92402 _92403).
Proof. exact (MK_COMB (@lem6925921) (@lem6925920 _92400 _92402 _92403)). Qed.
Lemma lem6925923 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6925924 (_92400 : int) (_92402 : int) (_92403 : int) : ((term178 _92402 _92400 _92403) = term108) = ((term183 _92400 _92402 _92403) = term108).
Proof. exact (MK_COMB (@lem6925922 _92400 _92402 _92403) (@lem6925923)). Qed.
Lemma lem6925925 (_92400 : int) (_92402 : int) (_92403 : int) : ((real_of_int _92402) = (term113 _92400 _92403)) = ((term183 _92400 _92402 _92403) = term108).
Proof. exact (TRANS (@lem6925891 _92402 _92400 _92403) (@lem6925924 _92400 _92402 _92403)). Qed.
Lemma lem6925926 (_92403 : int) (_92402 : int) : (term128 _92402 _92403) = (term187 _92403 _92402).
Proof. exact (@lem1988287 (real_of_int _92403) (term125 _92402)). Qed.
Lemma lem6925938 (_92403 : int) (_92402 : int) : (term188 _92403 _92402) = (term189 _92403 _92402).
Proof. exact (@lem1982792 (real_of_int _92403) (term125 _92402)). Qed.
Lemma lem6925939 (_92402 : int) : (term190 _92402) = (term191 _92402).
Proof. exact (@lem1982781 (real_of_int _92402) term157 term122). Qed.
Lemma lem6925941 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6925942 : term122 = term192.
Proof. exact (@lem6925941 term123). Qed.
Lemma lem6925944 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6925945 : term157 = term158.
Proof. exact (@lem6925944 term123). Qed.
Lemma lem6925946 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6925947 : term159 = term160.
Proof. exact (MK_COMB (@lem6925946) (@lem6925945)). Qed.
Lemma lem6925948 : term193 = term194.
Proof. exact (MK_COMB (@lem6925947) (@lem6925942)). Qed.
Lemma lem6925949 : term194 = term195.
Proof. exact (@lem1981613 term157 term122 term122 term122). Qed.
Lemma lem6925951 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6925952 : term166 = term167.
Proof. exact (@lem6925951 term123 term123). Qed.
Lemma lem6925953 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6925954 : term169 = term123.
Proof. exact (EQ_MP (@lem6925953) (@lem940073)). Qed.
Lemma lem6925955 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6925956 : term167 = term122.
Proof. exact (MK_COMB (@lem6925955) (@lem6925954)). Qed.
Lemma lem6925957 : term166 = term122.
Proof. exact (TRANS (@lem6925952) (@lem6925956)). Qed.
Lemma lem6925959 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6925960 : term193 = term198.
Proof. exact (@lem6925959 term123 term123). Qed.
Lemma lem6925961 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6925962 : term169 = term123.
Proof. exact (EQ_MP (@lem6925961) (@lem940073)). Qed.
Lemma lem6925963 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6925964 : term167 = term122.
Proof. exact (MK_COMB (@lem6925963) (@lem6925962)). Qed.
Lemma lem6925965 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6925966 : term198 = term157.
Proof. exact (MK_COMB (@lem6925965) (@lem6925964)). Qed.
Lemma lem6925967 : term193 = term157.
Proof. exact (TRANS (@lem6925960) (@lem6925966)). Qed.
Lemma lem6925968 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6925969 : term199 = term200.
Proof. exact (MK_COMB (@lem6925968) (@lem6925967)). Qed.
Lemma lem6925970 : term195 = term158.
Proof. exact (MK_COMB (@lem6925969) (@lem6925957)). Qed.
Lemma lem6925971 : term194 = term158.
Proof. exact (TRANS (@lem6925949) (@lem6925970)). Qed.
Lemma lem6925972 : term193 = term158.
Proof. exact (TRANS (@lem6925948) (@lem6925971)). Qed.
Lemma lem6925974 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6925975 : term158 = term157.
Proof. exact (@lem6925974 term157). Qed.
Lemma lem6925976 : term193 = term157.
Proof. exact (TRANS (@lem6925972) (@lem6925975)). Qed.
Lemma lem6925979 (_92402 : int) : (term201 _92402) = (term201 _92402).
Proof. exact (eq_refl (term201 _92402)). Qed.
Lemma lem6925980 (_92402 : int) : (term191 _92402) = (term202 _92402).
Proof. exact (MK_COMB (@lem6925979 _92402) (@lem6925976)). Qed.
Lemma lem6925981 (_92402 : int) : (term190 _92402) = (term202 _92402).
Proof. exact (TRANS (@lem6925939 _92402) (@lem6925980 _92402)). Qed.
Lemma lem6925982 (_92403 : int) : (term124 _92403) = (term124 _92403).
Proof. exact (eq_refl (term124 _92403)). Qed.
Lemma lem6925983 (_92403 : int) (_92402 : int) : (term189 _92403 _92402) = (term203 _92403 _92402).
Proof. exact (MK_COMB (@lem6925982 _92403) (@lem6925981 _92402)). Qed.
Lemma lem6925988 (_92402 : int) (_92403 : int) : (term203 _92403 _92402) = (term204 _92402 _92403).
Proof. exact (@lem1982757 (term184 _92402) (real_of_int _92403) term157). Qed.
Lemma lem6925989 (_92402 : int) (_92403 : int) : (term189 _92403 _92402) = (term204 _92402 _92403).
Proof. exact (TRANS (@lem6925983 _92403 _92402) (@lem6925988 _92402 _92403)). Qed.
Lemma lem6925991 (_92402 : int) (_92403 : int) : (term188 _92403 _92402) = (term204 _92402 _92403).
Proof. exact (TRANS (@lem6925938 _92403 _92402) (@lem6925989 _92402 _92403)). Qed.
Lemma lem6925992 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6925993 (_92402 : int) (_92403 : int) : (term205 _92403 _92402) = (term206 _92402 _92403).
Proof. exact (MK_COMB (@lem6925992) (@lem6925991 _92402 _92403)). Qed.
Lemma lem6925994 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6925995 (_92402 : int) (_92403 : int) : (term187 _92403 _92402) = (term207 _92402 _92403).
Proof. exact (MK_COMB (@lem6925993 _92402 _92403) (@lem6925994)). Qed.
Lemma lem6925996 (_92402 : int) (_92403 : int) : (term128 _92402 _92403) = (term207 _92402 _92403).
Proof. exact (TRANS (@lem6925926 _92403 _92402) (@lem6925995 _92402 _92403)). Qed.
Lemma lem6925997 (_92400 : int) : ((real_of_int _92400) = term108) = ((term151 _92400) = term108).
Proof. exact (@lem1988293 (real_of_int _92400) term108). Qed.
Lemma lem6926003 (_92400 : int) : (term151 _92400) = (term152 _92400).
Proof. exact (@lem1982792 (real_of_int _92400) term108). Qed.
Lemma lem6926005 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6926006 : term108 = term154.
Proof. exact (@lem6926005 (NUMERAL 0)). Qed.
Lemma lem6926008 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6926009 : term157 = term158.
Proof. exact (@lem6926008 term123). Qed.
Lemma lem6926010 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6926011 : term159 = term160.
Proof. exact (MK_COMB (@lem6926010) (@lem6926009)). Qed.
Lemma lem6926012 : term161 = term162.
Proof. exact (MK_COMB (@lem6926011) (@lem6926006)). Qed.
Lemma lem6926013 : term162 = term163.
Proof. exact (@lem1981613 term157 term108 term122 term122). Qed.
Lemma lem6926015 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6926016 : term166 = term167.
Proof. exact (@lem6926015 term123 term123). Qed.
Lemma lem6926017 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926018 : term169 = term123.
Proof. exact (EQ_MP (@lem6926017) (@lem940073)). Qed.
Lemma lem6926019 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926020 : term167 = term122.
Proof. exact (MK_COMB (@lem6926019) (@lem6926018)). Qed.
Lemma lem6926021 : term166 = term122.
Proof. exact (TRANS (@lem6926016) (@lem6926020)). Qed.
Lemma lem6926023 (x : nat) : (term170 x) = term108.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6926024 : term161 = term108.
Proof. exact (@lem6926023 term123). Qed.
Lemma lem6926025 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6926026 : term171 = term172.
Proof. exact (MK_COMB (@lem6926025) (@lem6926024)). Qed.
Lemma lem6926027 : term163 = term154.
Proof. exact (MK_COMB (@lem6926026) (@lem6926021)). Qed.
Lemma lem6926028 : term162 = term154.
Proof. exact (TRANS (@lem6926013) (@lem6926027)). Qed.
Lemma lem6926029 : term161 = term154.
Proof. exact (TRANS (@lem6926012) (@lem6926028)). Qed.
Lemma lem6926031 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6926032 : term154 = term108.
Proof. exact (@lem6926031 term108). Qed.
Lemma lem6926033 : term161 = term108.
Proof. exact (TRANS (@lem6926029) (@lem6926032)). Qed.
Lemma lem6926034 (_92400 : int) : (term124 _92400) = (term124 _92400).
Proof. exact (eq_refl (term124 _92400)). Qed.
Lemma lem6926035 (_92400 : int) : (term152 _92400) = (term174 _92400).
Proof. exact (MK_COMB (@lem6926034 _92400) (@lem6926033)). Qed.
Lemma lem6926036 (_92400 : int) : (term174 _92400) = (real_of_int _92400).
Proof. exact (@lem1982723 (real_of_int _92400)). Qed.
Lemma lem6926037 (_92400 : int) : (term152 _92400) = (real_of_int _92400).
Proof. exact (TRANS (@lem6926035 _92400) (@lem6926036 _92400)). Qed.
Lemma lem6926039 (_92400 : int) : (term151 _92400) = (real_of_int _92400).
Proof. exact (TRANS (@lem6926003 _92400) (@lem6926037 _92400)). Qed.
Lemma lem6926040 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6926041 (_92400 : int) : (term208 _92400) = (term114 _92400).
Proof. exact (MK_COMB (@lem6926040) (@lem6926039 _92400)). Qed.
Lemma lem6926042 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6926043 (_92400 : int) : ((term151 _92400) = term108) = ((real_of_int _92400) = term108).
Proof. exact (MK_COMB (@lem6926041 _92400) (@lem6926042)). Qed.
Lemma lem6926044 (_92400 : int) : ((real_of_int _92400) = term108) = ((real_of_int _92400) = term108).
Proof. exact (TRANS (@lem6925997 _92400) (@lem6926043 _92400)). Qed.
Lemma lem6926045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6926046 (_92402 : int) (_92403 : int) : (term129 _92402 _92403) = (term209 _92402 _92403).
Proof. exact (MK_COMB (@lem6926045) (@lem6925996 _92402 _92403)). Qed.
Lemma lem6926047 (_92402 : int) (_92403 : int) (_92400 : int) : (term130 _92402 _92403 _92400) = (term210 _92402 _92403 _92400).
Proof. exact (MK_COMB (@lem6926046 _92402 _92403) (@lem6926044 _92400)). Qed.
Lemma lem6926048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6926049 (_92400 : int) (_92402 : int) (_92403 : int) : (term131 _92402 _92400 _92403) = (term211 _92400 _92402 _92403).
Proof. exact (MK_COMB (@lem6926048) (@lem6925925 _92400 _92402 _92403)). Qed.
Lemma lem6926050 (_92402 : int) (_92403 : int) (_92400 : int) : (term132 _92402 _92403 _92400) = (term212 _92402 _92403 _92400).
Proof. exact (MK_COMB (@lem6926049 _92400 _92402 _92403) (@lem6926047 _92402 _92403 _92400)). Qed.
Lemma lem6926051 (_92401 : int) (_92403 : int) (_92402 : int) : ((term113 _92401 _92403) = (real_of_int _92402)) = ((term213 _92401 _92403 _92402) = term108).
Proof. exact (@lem1988293 (term113 _92401 _92403) (real_of_int _92402)). Qed.
Lemma lem6926063 (_92401 : int) (_92403 : int) (_92402 : int) : (term213 _92401 _92403 _92402) = (term214 _92401 _92403 _92402).
Proof. exact (@lem1982792 (term113 _92401 _92403) (real_of_int _92402)). Qed.
Lemma lem6926067 (_92401 : int) (_92403 : int) (_92402 : int) : (term214 _92401 _92403 _92402) = (term215 _92401 _92403 _92402).
Proof. exact (@lem1982755 (real_of_int _92401) (real_of_int _92403) (term184 _92402)). Qed.
Lemma lem6926068 (_92402 : int) (_92403 : int) : (term216 _92403 _92402) = (term217 _92402 _92403).
Proof. exact (@lem1982761 (term184 _92402) (real_of_int _92403)). Qed.
Lemma lem6926069 (_92401 : int) : (term124 _92401) = (term124 _92401).
Proof. exact (eq_refl (term124 _92401)). Qed.
Lemma lem6926070 (_92401 : int) (_92402 : int) (_92403 : int) : (term215 _92401 _92403 _92402) = (term218 _92401 _92402 _92403).
Proof. exact (MK_COMB (@lem6926069 _92401) (@lem6926068 _92402 _92403)). Qed.
Lemma lem6926072 (_92401 : int) (_92402 : int) (_92403 : int) : (term214 _92401 _92403 _92402) = (term218 _92401 _92402 _92403).
Proof. exact (TRANS (@lem6926067 _92401 _92403 _92402) (@lem6926070 _92401 _92402 _92403)). Qed.
Lemma lem6926074 (_92401 : int) (_92402 : int) (_92403 : int) : (term213 _92401 _92403 _92402) = (term218 _92401 _92402 _92403).
Proof. exact (TRANS (@lem6926063 _92401 _92403 _92402) (@lem6926072 _92401 _92402 _92403)). Qed.
Lemma lem6926075 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6926076 (_92401 : int) (_92402 : int) (_92403 : int) : (term219 _92401 _92403 _92402) = (term220 _92401 _92402 _92403).
Proof. exact (MK_COMB (@lem6926075) (@lem6926074 _92401 _92402 _92403)). Qed.
Lemma lem6926077 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6926078 (_92401 : int) (_92402 : int) (_92403 : int) : ((term213 _92401 _92403 _92402) = term108) = ((term218 _92401 _92402 _92403) = term108).
Proof. exact (MK_COMB (@lem6926076 _92401 _92402 _92403) (@lem6926077)). Qed.
Lemma lem6926079 (_92401 : int) (_92402 : int) (_92403 : int) : ((term113 _92401 _92403) = (real_of_int _92402)) = ((term218 _92401 _92402 _92403) = term108).
Proof. exact (TRANS (@lem6926051 _92401 _92403 _92402) (@lem6926078 _92401 _92402 _92403)). Qed.
Lemma lem6926080 (_92400 : int) (_92401 : int) : (term128 _92401 _92400) = (term187 _92400 _92401).
Proof. exact (@lem1988287 (real_of_int _92400) (term125 _92401)). Qed.
Lemma lem6926092 (_92400 : int) (_92401 : int) : (term188 _92400 _92401) = (term189 _92400 _92401).
Proof. exact (@lem1982792 (real_of_int _92400) (term125 _92401)). Qed.
Lemma lem6926093 (_92401 : int) : (term190 _92401) = (term191 _92401).
Proof. exact (@lem1982781 (real_of_int _92401) term157 term122). Qed.
Lemma lem6926095 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6926096 : term122 = term192.
Proof. exact (@lem6926095 term123). Qed.
Lemma lem6926098 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6926099 : term157 = term158.
Proof. exact (@lem6926098 term123). Qed.
Lemma lem6926100 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6926101 : term159 = term160.
Proof. exact (MK_COMB (@lem6926100) (@lem6926099)). Qed.
Lemma lem6926102 : term193 = term194.
Proof. exact (MK_COMB (@lem6926101) (@lem6926096)). Qed.
Lemma lem6926103 : term194 = term195.
Proof. exact (@lem1981613 term157 term122 term122 term122). Qed.
Lemma lem6926105 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6926106 : term166 = term167.
Proof. exact (@lem6926105 term123 term123). Qed.
Lemma lem6926107 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926108 : term169 = term123.
Proof. exact (EQ_MP (@lem6926107) (@lem940073)). Qed.
Lemma lem6926109 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926110 : term167 = term122.
Proof. exact (MK_COMB (@lem6926109) (@lem6926108)). Qed.
Lemma lem6926111 : term166 = term122.
Proof. exact (TRANS (@lem6926106) (@lem6926110)). Qed.
Lemma lem6926113 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6926114 : term193 = term198.
Proof. exact (@lem6926113 term123 term123). Qed.
Lemma lem6926115 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926116 : term169 = term123.
Proof. exact (EQ_MP (@lem6926115) (@lem940073)). Qed.
Lemma lem6926117 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926118 : term167 = term122.
Proof. exact (MK_COMB (@lem6926117) (@lem6926116)). Qed.
Lemma lem6926119 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6926120 : term198 = term157.
Proof. exact (MK_COMB (@lem6926119) (@lem6926118)). Qed.
Lemma lem6926121 : term193 = term157.
Proof. exact (TRANS (@lem6926114) (@lem6926120)). Qed.
Lemma lem6926122 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6926123 : term199 = term200.
Proof. exact (MK_COMB (@lem6926122) (@lem6926121)). Qed.
Lemma lem6926124 : term195 = term158.
Proof. exact (MK_COMB (@lem6926123) (@lem6926111)). Qed.
Lemma lem6926125 : term194 = term158.
Proof. exact (TRANS (@lem6926103) (@lem6926124)). Qed.
Lemma lem6926126 : term193 = term158.
Proof. exact (TRANS (@lem6926102) (@lem6926125)). Qed.
Lemma lem6926128 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6926129 : term158 = term157.
Proof. exact (@lem6926128 term157). Qed.
Lemma lem6926130 : term193 = term157.
Proof. exact (TRANS (@lem6926126) (@lem6926129)). Qed.
Lemma lem6926133 (_92401 : int) : (term201 _92401) = (term201 _92401).
Proof. exact (eq_refl (term201 _92401)). Qed.
Lemma lem6926134 (_92401 : int) : (term191 _92401) = (term202 _92401).
Proof. exact (MK_COMB (@lem6926133 _92401) (@lem6926130)). Qed.
Lemma lem6926135 (_92401 : int) : (term190 _92401) = (term202 _92401).
Proof. exact (TRANS (@lem6926093 _92401) (@lem6926134 _92401)). Qed.
Lemma lem6926136 (_92400 : int) : (term124 _92400) = (term124 _92400).
Proof. exact (eq_refl (term124 _92400)). Qed.
Lemma lem6926139 (_92400 : int) (_92401 : int) : (term189 _92400 _92401) = (term203 _92400 _92401).
Proof. exact (MK_COMB (@lem6926136 _92400) (@lem6926135 _92401)). Qed.
Lemma lem6926141 (_92400 : int) (_92401 : int) : (term188 _92400 _92401) = (term203 _92400 _92401).
Proof. exact (TRANS (@lem6926092 _92400 _92401) (@lem6926139 _92400 _92401)). Qed.
Lemma lem6926142 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6926143 (_92400 : int) (_92401 : int) : (term205 _92400 _92401) = (term221 _92400 _92401).
Proof. exact (MK_COMB (@lem6926142) (@lem6926141 _92400 _92401)). Qed.
Lemma lem6926144 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6926145 (_92400 : int) (_92401 : int) : (term187 _92400 _92401) = (term222 _92400 _92401).
Proof. exact (MK_COMB (@lem6926143 _92400 _92401) (@lem6926144)). Qed.
Lemma lem6926146 (_92400 : int) (_92401 : int) : (term128 _92401 _92400) = (term222 _92400 _92401).
Proof. exact (TRANS (@lem6926080 _92400 _92401) (@lem6926145 _92400 _92401)). Qed.
Lemma lem6926147 (_92401 : int) (_92400 : int) : (term128 _92400 _92401) = (term187 _92401 _92400).
Proof. exact (@lem1988287 (real_of_int _92401) (term125 _92400)). Qed.
Lemma lem6926159 (_92401 : int) (_92400 : int) : (term188 _92401 _92400) = (term189 _92401 _92400).
Proof. exact (@lem1982792 (real_of_int _92401) (term125 _92400)). Qed.
Lemma lem6926160 (_92400 : int) : (term190 _92400) = (term191 _92400).
Proof. exact (@lem1982781 (real_of_int _92400) term157 term122). Qed.
Lemma lem6926162 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6926163 : term122 = term192.
Proof. exact (@lem6926162 term123). Qed.
Lemma lem6926165 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6926166 : term157 = term158.
Proof. exact (@lem6926165 term123). Qed.
Lemma lem6926167 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6926168 : term159 = term160.
Proof. exact (MK_COMB (@lem6926167) (@lem6926166)). Qed.
Lemma lem6926169 : term193 = term194.
Proof. exact (MK_COMB (@lem6926168) (@lem6926163)). Qed.
Lemma lem6926170 : term194 = term195.
Proof. exact (@lem1981613 term157 term122 term122 term122). Qed.
Lemma lem6926172 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6926173 : term166 = term167.
Proof. exact (@lem6926172 term123 term123). Qed.
Lemma lem6926174 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926175 : term169 = term123.
Proof. exact (EQ_MP (@lem6926174) (@lem940073)). Qed.
Lemma lem6926176 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926177 : term167 = term122.
Proof. exact (MK_COMB (@lem6926176) (@lem6926175)). Qed.
Lemma lem6926178 : term166 = term122.
Proof. exact (TRANS (@lem6926173) (@lem6926177)). Qed.
Lemma lem6926180 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6926181 : term193 = term198.
Proof. exact (@lem6926180 term123 term123). Qed.
Lemma lem6926182 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926183 : term169 = term123.
Proof. exact (EQ_MP (@lem6926182) (@lem940073)). Qed.
Lemma lem6926184 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926185 : term167 = term122.
Proof. exact (MK_COMB (@lem6926184) (@lem6926183)). Qed.
Lemma lem6926186 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6926187 : term198 = term157.
Proof. exact (MK_COMB (@lem6926186) (@lem6926185)). Qed.
Lemma lem6926188 : term193 = term157.
Proof. exact (TRANS (@lem6926181) (@lem6926187)). Qed.
Lemma lem6926189 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6926190 : term199 = term200.
Proof. exact (MK_COMB (@lem6926189) (@lem6926188)). Qed.
Lemma lem6926191 : term195 = term158.
Proof. exact (MK_COMB (@lem6926190) (@lem6926178)). Qed.
Lemma lem6926192 : term194 = term158.
Proof. exact (TRANS (@lem6926170) (@lem6926191)). Qed.
Lemma lem6926193 : term193 = term158.
Proof. exact (TRANS (@lem6926169) (@lem6926192)). Qed.
Lemma lem6926195 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6926196 : term158 = term157.
Proof. exact (@lem6926195 term157). Qed.
Lemma lem6926197 : term193 = term157.
Proof. exact (TRANS (@lem6926193) (@lem6926196)). Qed.
Lemma lem6926200 (_92400 : int) : (term201 _92400) = (term201 _92400).
Proof. exact (eq_refl (term201 _92400)). Qed.
Lemma lem6926201 (_92400 : int) : (term191 _92400) = (term202 _92400).
Proof. exact (MK_COMB (@lem6926200 _92400) (@lem6926197)). Qed.
Lemma lem6926202 (_92400 : int) : (term190 _92400) = (term202 _92400).
Proof. exact (TRANS (@lem6926160 _92400) (@lem6926201 _92400)). Qed.
Lemma lem6926203 (_92401 : int) : (term124 _92401) = (term124 _92401).
Proof. exact (eq_refl (term124 _92401)). Qed.
Lemma lem6926204 (_92401 : int) (_92400 : int) : (term189 _92401 _92400) = (term203 _92401 _92400).
Proof. exact (MK_COMB (@lem6926203 _92401) (@lem6926202 _92400)). Qed.
Lemma lem6926209 (_92400 : int) (_92401 : int) : (term203 _92401 _92400) = (term204 _92400 _92401).
Proof. exact (@lem1982757 (term184 _92400) (real_of_int _92401) term157). Qed.
Lemma lem6926210 (_92400 : int) (_92401 : int) : (term189 _92401 _92400) = (term204 _92400 _92401).
Proof. exact (TRANS (@lem6926204 _92401 _92400) (@lem6926209 _92400 _92401)). Qed.
Lemma lem6926212 (_92400 : int) (_92401 : int) : (term188 _92401 _92400) = (term204 _92400 _92401).
Proof. exact (TRANS (@lem6926159 _92401 _92400) (@lem6926210 _92400 _92401)). Qed.
Lemma lem6926213 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6926214 (_92400 : int) (_92401 : int) : (term205 _92401 _92400) = (term206 _92400 _92401).
Proof. exact (MK_COMB (@lem6926213) (@lem6926212 _92400 _92401)). Qed.
Lemma lem6926215 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6926216 (_92400 : int) (_92401 : int) : (term187 _92401 _92400) = (term207 _92400 _92401).
Proof. exact (MK_COMB (@lem6926214 _92400 _92401) (@lem6926215)). Qed.
Lemma lem6926217 (_92400 : int) (_92401 : int) : (term128 _92400 _92401) = (term207 _92400 _92401).
Proof. exact (TRANS (@lem6926147 _92401 _92400) (@lem6926216 _92400 _92401)). Qed.
Lemma lem6926218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6926219 (_92400 : int) (_92401 : int) : (term137 _92401 _92400) = (term223 _92400 _92401).
Proof. exact (MK_COMB (@lem6926218) (@lem6926146 _92400 _92401)). Qed.
Lemma lem6926220 (_92400 : int) (_92401 : int) : (term138 _92400 _92401) = (term224 _92400 _92401).
Proof. exact (MK_COMB (@lem6926219 _92400 _92401) (@lem6926217 _92400 _92401)). Qed.
Lemma lem6926221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6926222 (_92401 : int) (_92402 : int) (_92403 : int) : (term139 _92401 _92403 _92402) = (term225 _92401 _92402 _92403).
Proof. exact (MK_COMB (@lem6926221) (@lem6926079 _92401 _92402 _92403)). Qed.
Lemma lem6926223 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term140 _92403 _92402 _92400 _92401) = (term226 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926222 _92401 _92402 _92403) (@lem6926220 _92400 _92401)). Qed.
Lemma lem6926224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6926225 (_92402 : int) (_92403 : int) (_92400 : int) : (term141 _92402 _92403 _92400) = (term227 _92402 _92403 _92400).
Proof. exact (MK_COMB (@lem6926224) (@lem6926050 _92402 _92403 _92400)). Qed.
Lemma lem6926226 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term142 _92403 _92402 _92400 _92401) = (term228 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926225 _92402 _92403 _92400) (@lem6926223 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6926228 (_92403 : int) : (term143 _92403) = (term229 _92403).
Proof. exact (MK_COMB (@lem6926227) (@lem6925890 _92403)). Qed.
Lemma lem6926229 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term144 _92403 _92402 _92400 _92401) = (term230 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926228 _92403) (@lem6926226 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6926231 (_92402 : int) : (term143 _92402) = (term229 _92402).
Proof. exact (MK_COMB (@lem6926230) (@lem6925842 _92402)). Qed.
Lemma lem6926232 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term145 _92403 _92402 _92400 _92401) = (term231 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926231 _92402) (@lem6926229 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6926234 (_92401 : int) : (term143 _92401) = (term229 _92401).
Proof. exact (MK_COMB (@lem6926233) (@lem6925794 _92401)). Qed.
Lemma lem6926235 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term146 _92403 _92402 _92400 _92401) = (term232 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926234 _92401) (@lem6926232 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6926237 (_92400 : int) : (term143 _92400) = (term229 _92400).
Proof. exact (MK_COMB (@lem6926236) (@lem6925746 _92400)). Qed.
Lemma lem6926238 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term147 _92403 _92402 _92400 _92401) = (term233 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926237 _92400) (@lem6926235 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926245 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term149 _92403 _92402 _92400 _92401) = (term233 _92402 _92403 _92400 _92401).
Proof. exact (TRANS (@lem6925698 _92403 _92402 _92400 _92401) (@lem6926238 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926262 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term226 _92402 _92403 _92400 _92401) = (term234 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term222 _92400 _92401) ((term218 _92401 _92402 _92403) = term108) (term207 _92400 _92401)). Qed.
Lemma lem6926275 (_92402 : int) (_92403 : int) (_92400 : int) : (term227 _92402 _92403 _92400) = (term227 _92402 _92403 _92400).
Proof. exact (eq_refl (term227 _92402 _92403 _92400)). Qed.
Lemma lem6926276 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term228 _92402 _92403 _92400 _92401) = (term235 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926275 _92402 _92403 _92400) (@lem6926262 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926277 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term235 _92402 _92403 _92400 _92401) = (term236 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term237 _92402 _92403 _92400 _92401) (term212 _92402 _92403 _92400) (term238 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926284 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term239 _92402 _92403 _92400 _92401) = (term240 _92402 _92403 _92400 _92401).
Proof. exact (@lem19367 ((term183 _92400 _92402 _92403) = term108) (term210 _92402 _92403 _92400) (term238 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926291 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term241 _92402 _92403 _92400 _92401) = (term242 _92402 _92403 _92400 _92401).
Proof. exact (@lem19367 ((term183 _92400 _92402 _92403) = term108) (term210 _92402 _92403 _92400) (term237 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6926293 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term243 _92402 _92403 _92400 _92401) = (term244 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926292) (@lem6926291 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926294 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term236 _92402 _92403 _92400 _92401) = (term245 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926293 _92402 _92403 _92400 _92401) (@lem6926284 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926295 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term235 _92402 _92403 _92400 _92401) = (term245 _92402 _92403 _92400 _92401).
Proof. exact (TRANS (@lem6926277 _92402 _92403 _92400 _92401) (@lem6926294 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926296 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term228 _92402 _92403 _92400 _92401) = (term245 _92402 _92403 _92400 _92401).
Proof. exact (TRANS (@lem6926276 _92402 _92403 _92400 _92401) (@lem6926295 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926299 (_92403 : int) : (term229 _92403) = (term229 _92403).
Proof. exact (eq_refl (term229 _92403)). Qed.
Lemma lem6926300 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term230 _92402 _92403 _92400 _92401) = (term246 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926299 _92403) (@lem6926296 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926301 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term246 _92402 _92403 _92400 _92401) = (term247 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term242 _92402 _92403 _92400 _92401) (term177 _92403) (term240 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926308 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term248 _92402 _92403 _92400 _92401) = (term249 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term250 _92402 _92403 _92400 _92401) (term177 _92403) (term251 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926315 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term252 _92402 _92403 _92400 _92401) = (term253 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term254 _92402 _92403 _92400 _92401) (term177 _92403) (term255 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926316 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6926317 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term256 _92402 _92403 _92400 _92401) = (term257 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926316) (@lem6926315 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926318 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term247 _92402 _92403 _92400 _92401) = (term258 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926317 _92402 _92403 _92400 _92401) (@lem6926308 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926319 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term246 _92402 _92403 _92400 _92401) = (term258 _92402 _92403 _92400 _92401).
Proof. exact (TRANS (@lem6926301 _92402 _92403 _92400 _92401) (@lem6926318 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926320 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term230 _92402 _92403 _92400 _92401) = (term258 _92402 _92403 _92400 _92401).
Proof. exact (TRANS (@lem6926300 _92402 _92403 _92400 _92401) (@lem6926319 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926323 (_92402 : int) : (term229 _92402) = (term229 _92402).
Proof. exact (eq_refl (term229 _92402)). Qed.
Lemma lem6926324 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term231 _92402 _92403 _92400 _92401) = (term259 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926323 _92402) (@lem6926320 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926325 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term259 _92402 _92403 _92400 _92401) = (term260 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term253 _92402 _92403 _92400 _92401) (term177 _92402) (term249 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926332 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term261 _92402 _92403 _92400 _92401) = (term262 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term263 _92402 _92403 _92400 _92401) (term177 _92402) (term264 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926339 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term265 _92402 _92403 _92400 _92401) = (term266 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term267 _92402 _92403 _92400 _92401) (term177 _92402) (term268 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926340 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6926341 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term269 _92402 _92403 _92400 _92401) = (term270 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926340) (@lem6926339 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926342 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term260 _92402 _92403 _92400 _92401) = (term271 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926341 _92402 _92403 _92400 _92401) (@lem6926332 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926343 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term259 _92402 _92403 _92400 _92401) = (term271 _92402 _92403 _92400 _92401).
Proof. exact (TRANS (@lem6926325 _92402 _92403 _92400 _92401) (@lem6926342 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926344 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term231 _92402 _92403 _92400 _92401) = (term271 _92402 _92403 _92400 _92401).
Proof. exact (TRANS (@lem6926324 _92402 _92403 _92400 _92401) (@lem6926343 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926347 (_92401 : int) : (term229 _92401) = (term229 _92401).
Proof. exact (eq_refl (term229 _92401)). Qed.
Lemma lem6926348 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term232 _92402 _92403 _92400 _92401) = (term272 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926347 _92401) (@lem6926344 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926349 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term272 _92402 _92403 _92400 _92401) = (term273 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term266 _92402 _92403 _92400 _92401) (term177 _92401) (term262 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926356 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term274 _92402 _92403 _92400 _92401) = (term275 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term276 _92402 _92403 _92400 _92401) (term177 _92401) (term277 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926363 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term278 _92402 _92403 _92400 _92401) = (term279 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term280 _92402 _92403 _92400 _92401) (term177 _92401) (term281 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6926365 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term282 _92402 _92403 _92400 _92401) = (term283 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926364) (@lem6926363 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926366 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term273 _92402 _92403 _92400 _92401) = (term284 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926365 _92402 _92403 _92400 _92401) (@lem6926356 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926367 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term272 _92402 _92403 _92400 _92401) = (term284 _92402 _92403 _92400 _92401).
Proof. exact (TRANS (@lem6926349 _92402 _92403 _92400 _92401) (@lem6926366 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926368 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term232 _92402 _92403 _92400 _92401) = (term284 _92402 _92403 _92400 _92401).
Proof. exact (TRANS (@lem6926348 _92402 _92403 _92400 _92401) (@lem6926367 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926371 (_92400 : int) : (term229 _92400) = (term229 _92400).
Proof. exact (eq_refl (term229 _92400)). Qed.
Lemma lem6926372 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term233 _92402 _92403 _92400 _92401) = (term285 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926371 _92400) (@lem6926368 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926373 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term285 _92402 _92403 _92400 _92401) = (term286 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term279 _92402 _92403 _92400 _92401) (term177 _92400) (term275 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926380 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term287 _92402 _92403 _92400 _92401) = (term288 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term289 _92402 _92403 _92400 _92401) (term177 _92400) (term290 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926387 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term291 _92402 _92403 _92400 _92401) = (term292 _92402 _92403 _92400 _92401).
Proof. exact (@lem19158 (term293 _92402 _92403 _92400 _92401) (term177 _92400) (term294 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6926389 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term295 _92402 _92403 _92400 _92401) = (term296 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926388) (@lem6926387 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926390 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term286 _92402 _92403 _92400 _92401) = (term297 _92402 _92403 _92400 _92401).
Proof. exact (MK_COMB (@lem6926389 _92402 _92403 _92400 _92401) (@lem6926380 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926391 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term285 _92402 _92403 _92400 _92401) = (term297 _92402 _92403 _92400 _92401).
Proof. exact (TRANS (@lem6926373 _92402 _92403 _92400 _92401) (@lem6926390 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926392 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term233 _92402 _92403 _92400 _92401) = (term297 _92402 _92403 _92400 _92401).
Proof. exact (TRANS (@lem6926372 _92402 _92403 _92400 _92401) (@lem6926391 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926393 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term149 _92403 _92402 _92400 _92401) = (term297 _92402 _92403 _92400 _92401).
Proof. exact (TRANS (@lem6926245 _92402 _92403 _92400 _92401) (@lem6926392 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926415 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term297 _92402 _92403 _92400 _92401) : term297 _92402 _92403 _92400 _92401.
Proof. exact (h1). Qed.
Lemma lem6926416 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term292 _92402 _92403 _92400 _92401) : term292 _92402 _92403 _92400 _92401.
Proof. exact (h1). Qed.
Lemma lem6926417 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term298 _92402 _92403 _92400 _92401.
Proof. exact (h1). Qed.
Lemma lem6926418 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term293 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6926417 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926420 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term280 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6926418 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926422 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term267 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6926420 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926424 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term254 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6926422 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926426 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term237 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6926424 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926427 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : (term183 _92400 _92402 _92403) = term108.
Proof. exact (proj1 (@lem6926424 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926428 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term222 _92400 _92401.
Proof. exact (proj2 (@lem6926426 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926429 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : (term218 _92401 _92402 _92403) = term108.
Proof. exact (proj1 (@lem6926426 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926431 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6926432 : term299 = term300.
Proof. exact (@lem6926431 term108 term122). Qed.
Lemma lem6926434 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6926435 : term122 = term192.
Proof. exact (@lem6926434 term123). Qed.
Lemma lem6926437 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6926438 : term108 = term154.
Proof. exact (@lem6926437 (NUMERAL 0)). Qed.
Lemma lem6926439 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6926440 : term301 = term302.
Proof. exact (MK_COMB (@lem6926439) (@lem6926438)). Qed.
Lemma lem6926441 : term300 = term303.
Proof. exact (MK_COMB (@lem6926440) (@lem6926435)). Qed.
Lemma lem6926442 : term304.
Proof. exact (@lem1980255 term108 term122 term122 term122). Qed.
Lemma lem6926444 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926445 : term300 = term306.
Proof. exact (@lem6926444 (NUMERAL 0) term123). Qed.
Lemma lem6926446 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926447 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926448 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926447 h1) (fun h1 : term306 = True => @lem6926446)). Qed.
Lemma lem6926449 : term306 = True.
Proof. exact (EQ_MP (@lem6926448) (@lem6926446)). Qed.
Lemma lem6926450 : term300 = True.
Proof. exact (TRANS (@lem6926445) (@lem6926449)). Qed.
Lemma lem6926451 : True = term300.
Proof. exact (SYM (@lem6926450)). Qed.
Lemma lem6926452 : term300.
Proof. exact (EQ_MP (@lem6926451) (@lem0)). Qed.
Lemma lem6926453 : term308.
Proof. exact (@lem6926442 (@lem6926452)). Qed.
Lemma lem6926455 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926456 : term300 = term306.
Proof. exact (@lem6926455 (NUMERAL 0) term123). Qed.
Lemma lem6926457 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926458 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926459 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926458 h1) (fun h1 : term306 = True => @lem6926457)). Qed.
Lemma lem6926460 : term306 = True.
Proof. exact (EQ_MP (@lem6926459) (@lem6926457)). Qed.
Lemma lem6926461 : term300 = True.
Proof. exact (TRANS (@lem6926456) (@lem6926460)). Qed.
Lemma lem6926462 : True = term300.
Proof. exact (SYM (@lem6926461)). Qed.
Lemma lem6926463 : term300.
Proof. exact (EQ_MP (@lem6926462) (@lem0)). Qed.
Lemma lem6926464 : term303 = term309.
Proof. exact (@lem6926453 (@lem6926463)). Qed.
Lemma lem6926466 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6926467 : term166 = term167.
Proof. exact (@lem6926466 term123 term123). Qed.
Lemma lem6926468 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926469 : term169 = term123.
Proof. exact (EQ_MP (@lem6926468) (@lem940073)). Qed.
Lemma lem6926470 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926471 : term167 = term122.
Proof. exact (MK_COMB (@lem6926470) (@lem6926469)). Qed.
Lemma lem6926472 : term166 = term122.
Proof. exact (TRANS (@lem6926467) (@lem6926471)). Qed.
Lemma lem6926474 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6926475 : term311 = term108.
Proof. exact (@lem6926474 term123). Qed.
Lemma lem6926476 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6926477 : term312 = term301.
Proof. exact (MK_COMB (@lem6926476) (@lem6926475)). Qed.
Lemma lem6926478 : term309 = term300.
Proof. exact (MK_COMB (@lem6926477) (@lem6926472)). Qed.
Lemma lem6926480 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926481 : term300 = term306.
Proof. exact (@lem6926480 (NUMERAL 0) term123). Qed.
Lemma lem6926482 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926483 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926484 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926483 h1) (fun h1 : term306 = True => @lem6926482)). Qed.
Lemma lem6926485 : term306 = True.
Proof. exact (EQ_MP (@lem6926484) (@lem6926482)). Qed.
Lemma lem6926486 : term300 = True.
Proof. exact (TRANS (@lem6926481) (@lem6926485)). Qed.
Lemma lem6926487 : term309 = True.
Proof. exact (TRANS (@lem6926478) (@lem6926486)). Qed.
Lemma lem6926488 : term303 = True.
Proof. exact (TRANS (@lem6926464) (@lem6926487)). Qed.
Lemma lem6926489 : term300 = True.
Proof. exact (TRANS (@lem6926441) (@lem6926488)). Qed.
Lemma lem6926490 : term299 = True.
Proof. exact (TRANS (@lem6926432) (@lem6926489)). Qed.
Lemma lem6926491 : True = term299.
Proof. exact (SYM (@lem6926490)). Qed.
Lemma lem6926492 : term299.
Proof. exact (EQ_MP (@lem6926491) (@lem0)). Qed.
Lemma lem6926493 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term313 _92400 _92401.
Proof. exact (conj (@lem6926492) (@lem6926428 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926495 (x : real) (y : real) : term314 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6926496 (_92400 : int) (_92401 : int) : term315 _92400 _92401.
Proof. exact (@lem6926495 term122 (term203 _92400 _92401)). Qed.
Lemma lem6926497 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term316 _92400 _92401.
Proof. exact (@lem6926496 _92400 _92401 (@lem6926493 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926498 (_92400 : int) (_92401 : int) : (term317 _92400 _92401) = (term203 _92400 _92401).
Proof. exact (@lem1982733 (term203 _92400 _92401)). Qed.
Lemma lem6926499 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6926500 (_92400 : int) (_92401 : int) : (term318 _92400 _92401) = (term221 _92400 _92401).
Proof. exact (MK_COMB (@lem6926499) (@lem6926498 _92400 _92401)). Qed.
Lemma lem6926501 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6926502 (_92400 : int) (_92401 : int) : (term316 _92400 _92401) = (term222 _92400 _92401).
Proof. exact (MK_COMB (@lem6926500 _92400 _92401) (@lem6926501)). Qed.
Lemma lem6926503 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term222 _92400 _92401.
Proof. exact (EQ_MP (@lem6926502 _92400 _92401) (@lem6926497 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926505 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6926506 : term299 = term300.
Proof. exact (@lem6926505 term108 term122). Qed.
Lemma lem6926508 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6926509 : term122 = term192.
Proof. exact (@lem6926508 term123). Qed.
Lemma lem6926511 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6926512 : term108 = term154.
Proof. exact (@lem6926511 (NUMERAL 0)). Qed.
Lemma lem6926513 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6926514 : term301 = term302.
Proof. exact (MK_COMB (@lem6926513) (@lem6926512)). Qed.
Lemma lem6926515 : term300 = term303.
Proof. exact (MK_COMB (@lem6926514) (@lem6926509)). Qed.
Lemma lem6926516 : term304.
Proof. exact (@lem1980255 term108 term122 term122 term122). Qed.
Lemma lem6926518 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926519 : term300 = term306.
Proof. exact (@lem6926518 (NUMERAL 0) term123). Qed.
Lemma lem6926520 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926521 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926522 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926521 h1) (fun h1 : term306 = True => @lem6926520)). Qed.
Lemma lem6926523 : term306 = True.
Proof. exact (EQ_MP (@lem6926522) (@lem6926520)). Qed.
Lemma lem6926524 : term300 = True.
Proof. exact (TRANS (@lem6926519) (@lem6926523)). Qed.
Lemma lem6926525 : True = term300.
Proof. exact (SYM (@lem6926524)). Qed.
Lemma lem6926526 : term300.
Proof. exact (EQ_MP (@lem6926525) (@lem0)). Qed.
Lemma lem6926527 : term308.
Proof. exact (@lem6926516 (@lem6926526)). Qed.
Lemma lem6926529 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926530 : term300 = term306.
Proof. exact (@lem6926529 (NUMERAL 0) term123). Qed.
Lemma lem6926531 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926532 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926533 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926532 h1) (fun h1 : term306 = True => @lem6926531)). Qed.
Lemma lem6926534 : term306 = True.
Proof. exact (EQ_MP (@lem6926533) (@lem6926531)). Qed.
Lemma lem6926535 : term300 = True.
Proof. exact (TRANS (@lem6926530) (@lem6926534)). Qed.
Lemma lem6926536 : True = term300.
Proof. exact (SYM (@lem6926535)). Qed.
Lemma lem6926537 : term300.
Proof. exact (EQ_MP (@lem6926536) (@lem0)). Qed.
Lemma lem6926538 : term303 = term309.
Proof. exact (@lem6926527 (@lem6926537)). Qed.
Lemma lem6926540 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6926541 : term166 = term167.
Proof. exact (@lem6926540 term123 term123). Qed.
Lemma lem6926542 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926543 : term169 = term123.
Proof. exact (EQ_MP (@lem6926542) (@lem940073)). Qed.
Lemma lem6926544 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926545 : term167 = term122.
Proof. exact (MK_COMB (@lem6926544) (@lem6926543)). Qed.
Lemma lem6926546 : term166 = term122.
Proof. exact (TRANS (@lem6926541) (@lem6926545)). Qed.
Lemma lem6926548 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6926549 : term311 = term108.
Proof. exact (@lem6926548 term123). Qed.
Lemma lem6926550 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6926551 : term312 = term301.
Proof. exact (MK_COMB (@lem6926550) (@lem6926549)). Qed.
Lemma lem6926552 : term309 = term300.
Proof. exact (MK_COMB (@lem6926551) (@lem6926546)). Qed.
Lemma lem6926554 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926555 : term300 = term306.
Proof. exact (@lem6926554 (NUMERAL 0) term123). Qed.
Lemma lem6926556 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926557 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926558 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926557 h1) (fun h1 : term306 = True => @lem6926556)). Qed.
Lemma lem6926559 : term306 = True.
Proof. exact (EQ_MP (@lem6926558) (@lem6926556)). Qed.
Lemma lem6926560 : term300 = True.
Proof. exact (TRANS (@lem6926555) (@lem6926559)). Qed.
Lemma lem6926561 : term309 = True.
Proof. exact (TRANS (@lem6926552) (@lem6926560)). Qed.
Lemma lem6926562 : term303 = True.
Proof. exact (TRANS (@lem6926538) (@lem6926561)). Qed.
Lemma lem6926563 : term300 = True.
Proof. exact (TRANS (@lem6926515) (@lem6926562)). Qed.
Lemma lem6926564 : term299 = True.
Proof. exact (TRANS (@lem6926506) (@lem6926563)). Qed.
Lemma lem6926565 : True = term299.
Proof. exact (SYM (@lem6926564)). Qed.
Lemma lem6926566 : term299.
Proof. exact (EQ_MP (@lem6926565) (@lem0)). Qed.
Lemma lem6926567 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term319 _92400 _92402 _92403.
Proof. exact (conj (@lem6926566) (@lem6926427 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926569 (x : real) (y : real) : term320 x y.
Proof. exact (proj1 (@lem1988330 x y)). Qed.
Lemma lem6926570 (_92400 : int) (_92402 : int) (_92403 : int) : term321 _92400 _92402 _92403.
Proof. exact (@lem6926569 term122 (term183 _92400 _92402 _92403)). Qed.
Lemma lem6926571 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : (term322 _92400 _92402 _92403) = term108.
Proof. exact (@lem6926570 _92400 _92402 _92403 (@lem6926567 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926572 (_92400 : int) (_92402 : int) (_92403 : int) : (term322 _92400 _92402 _92403) = (term183 _92400 _92402 _92403).
Proof. exact (@lem1982733 (term183 _92400 _92402 _92403)). Qed.
Lemma lem6926573 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6926574 (_92400 : int) (_92402 : int) (_92403 : int) : (term323 _92400 _92402 _92403) = (term186 _92400 _92402 _92403).
Proof. exact (MK_COMB (@lem6926573) (@lem6926572 _92400 _92402 _92403)). Qed.
Lemma lem6926575 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6926576 (_92400 : int) (_92402 : int) (_92403 : int) : ((term322 _92400 _92402 _92403) = term108) = ((term183 _92400 _92402 _92403) = term108).
Proof. exact (MK_COMB (@lem6926574 _92400 _92402 _92403) (@lem6926575)). Qed.
Lemma lem6926577 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : (term183 _92400 _92402 _92403) = term108.
Proof. exact (EQ_MP (@lem6926576 _92400 _92402 _92403) (@lem6926571 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926579 (y : real) : term324 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6926580 (_92401 : int) (_92402 : int) (_92403 : int) : term325 _92401 _92402 _92403.
Proof. exact (@lem6926579 (term218 _92401 _92402 _92403)). Qed.
Lemma lem6926581 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term326 _92401 _92402 _92403.
Proof. exact (@lem6926580 _92401 _92402 _92403 (@lem6926429 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926582 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term327 _92401 _92402 _92403.
Proof. exact (@lem6926581 _92402 _92403 _92400 _92401 h1 term122). Qed.
Lemma lem6926583 (_92401 : int) (_92402 : int) (_92403 : int) : (term327 _92401 _92402 _92403) = ((term328 _92401 _92402 _92403) = term108).
Proof. exact (eq_refl (term327 _92401 _92402 _92403)). Qed.
Lemma lem6926584 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : (term328 _92401 _92402 _92403) = term108.
Proof. exact (EQ_MP (@lem6926583 _92401 _92402 _92403) (@lem6926582 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926585 (_92401 : int) (_92402 : int) (_92403 : int) : (term328 _92401 _92402 _92403) = (term218 _92401 _92402 _92403).
Proof. exact (@lem1982733 (term218 _92401 _92402 _92403)). Qed.
Lemma lem6926586 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6926587 (_92401 : int) (_92402 : int) (_92403 : int) : (term329 _92401 _92402 _92403) = (term220 _92401 _92402 _92403).
Proof. exact (MK_COMB (@lem6926586) (@lem6926585 _92401 _92402 _92403)). Qed.
Lemma lem6926588 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6926589 (_92401 : int) (_92402 : int) (_92403 : int) : ((term328 _92401 _92402 _92403) = term108) = ((term218 _92401 _92402 _92403) = term108).
Proof. exact (MK_COMB (@lem6926587 _92401 _92402 _92403) (@lem6926588)). Qed.
Lemma lem6926590 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : (term218 _92401 _92402 _92403) = term108.
Proof. exact (EQ_MP (@lem6926589 _92401 _92402 _92403) (@lem6926584 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926591 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term330 _92401 _92400 _92402 _92403.
Proof. exact (conj (@lem6926590 _92402 _92403 _92400 _92401 h1) (@lem6926577 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926593 (x : real) (y : real) : term331 x y.
Proof. exact (proj1 (@lem1393126 x y)). Qed.
Lemma lem6926594 (_92401 : int) (_92400 : int) (_92402 : int) (_92403 : int) : term332 _92401 _92400 _92402 _92403.
Proof. exact (@lem6926593 (term218 _92401 _92402 _92403) (term183 _92400 _92402 _92403)). Qed.
Lemma lem6926595 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : (term333 _92401 _92400 _92402 _92403) = term108.
Proof. exact (@lem6926594 _92401 _92400 _92402 _92403 (@lem6926591 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926596 (_92400 : int) (_92401 : int) (_92402 : int) (_92403 : int) : (term333 _92401 _92400 _92402 _92403) = (term334 _92400 _92401 _92402 _92403).
Proof. exact (@lem1982757 (term184 _92400) (term218 _92401 _92402 _92403) (term216 _92402 _92403)). Qed.
Lemma lem6926597 (_92401 : int) (_92402 : int) (_92403 : int) : (term335 _92401 _92402 _92403) = (term336 _92401 _92402 _92403).
Proof. exact (@lem1982755 (real_of_int _92401) (term217 _92402 _92403) (term216 _92402 _92403)). Qed.
Lemma lem6926598 (_92402 : int) (_92403 : int) : (term337 _92402 _92403) = (term338 _92402 _92403).
Proof. exact (@lem1982753 (term184 _92402) (real_of_int _92402) (real_of_int _92403) (term184 _92403)). Qed.
Lemma lem6926599 (_92402 : int) : (term339 _92402) = (term340 _92402).
Proof. exact (@lem1982713 term157 (real_of_int _92402)). Qed.
Lemma lem6926601 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6926602 : term122 = term192.
Proof. exact (@lem6926601 term123). Qed.
Lemma lem6926604 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6926605 : term157 = term158.
Proof. exact (@lem6926604 term123). Qed.
Lemma lem6926606 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6926607 : term341 = term342.
Proof. exact (MK_COMB (@lem6926606) (@lem6926605)). Qed.
Lemma lem6926608 : term343 = term344.
Proof. exact (MK_COMB (@lem6926607) (@lem6926602)). Qed.
Lemma lem6926609 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6926611 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926612 : term300 = term306.
Proof. exact (@lem6926611 (NUMERAL 0) term123). Qed.
Lemma lem6926613 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926614 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926615 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926614 h1) (fun h1 : term306 = True => @lem6926613)). Qed.
Lemma lem6926616 : term306 = True.
Proof. exact (EQ_MP (@lem6926615) (@lem6926613)). Qed.
Lemma lem6926617 : term300 = True.
Proof. exact (TRANS (@lem6926612) (@lem6926616)). Qed.
Lemma lem6926618 : True = term300.
Proof. exact (SYM (@lem6926617)). Qed.
Lemma lem6926619 : term300.
Proof. exact (EQ_MP (@lem6926618) (@lem0)). Qed.
Lemma lem6926620 : term346.
Proof. exact (@lem6926609 (@lem6926619)). Qed.
Lemma lem6926622 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926623 : term300 = term306.
Proof. exact (@lem6926622 (NUMERAL 0) term123). Qed.
Lemma lem6926624 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926625 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926626 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926625 h1) (fun h1 : term306 = True => @lem6926624)). Qed.
Lemma lem6926627 : term306 = True.
Proof. exact (EQ_MP (@lem6926626) (@lem6926624)). Qed.
Lemma lem6926628 : term300 = True.
Proof. exact (TRANS (@lem6926623) (@lem6926627)). Qed.
Lemma lem6926629 : True = term300.
Proof. exact (SYM (@lem6926628)). Qed.
Lemma lem6926630 : term300.
Proof. exact (EQ_MP (@lem6926629) (@lem0)). Qed.
Lemma lem6926631 : term347.
Proof. exact (@lem6926620 (@lem6926630)). Qed.
Lemma lem6926633 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926634 : term300 = term306.
Proof. exact (@lem6926633 (NUMERAL 0) term123). Qed.
Lemma lem6926635 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926636 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926637 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926636 h1) (fun h1 : term306 = True => @lem6926635)). Qed.
Lemma lem6926638 : term306 = True.
Proof. exact (EQ_MP (@lem6926637) (@lem6926635)). Qed.
Lemma lem6926639 : term300 = True.
Proof. exact (TRANS (@lem6926634) (@lem6926638)). Qed.
Lemma lem6926640 : True = term300.
Proof. exact (SYM (@lem6926639)). Qed.
Lemma lem6926641 : term300.
Proof. exact (EQ_MP (@lem6926640) (@lem0)). Qed.
Lemma lem6926642 : term348.
Proof. exact (@lem6926631 (@lem6926641)). Qed.
Lemma lem6926644 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6926645 : term166 = term167.
Proof. exact (@lem6926644 term123 term123). Qed.
Lemma lem6926646 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926647 : term169 = term123.
Proof. exact (EQ_MP (@lem6926646) (@lem940073)). Qed.
Lemma lem6926648 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926649 : term167 = term122.
Proof. exact (MK_COMB (@lem6926648) (@lem6926647)). Qed.
Lemma lem6926650 : term166 = term122.
Proof. exact (TRANS (@lem6926645) (@lem6926649)). Qed.
Lemma lem6926652 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6926653 : term193 = term198.
Proof. exact (@lem6926652 term123 term123). Qed.
Lemma lem6926654 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926655 : term169 = term123.
Proof. exact (EQ_MP (@lem6926654) (@lem940073)). Qed.
Lemma lem6926656 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926657 : term167 = term122.
Proof. exact (MK_COMB (@lem6926656) (@lem6926655)). Qed.
Lemma lem6926658 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6926659 : term198 = term157.
Proof. exact (MK_COMB (@lem6926658) (@lem6926657)). Qed.
Lemma lem6926660 : term193 = term157.
Proof. exact (TRANS (@lem6926653) (@lem6926659)). Qed.
Lemma lem6926661 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6926662 : term349 = term341.
Proof. exact (MK_COMB (@lem6926661) (@lem6926660)). Qed.
Lemma lem6926663 : term350 = term343.
Proof. exact (MK_COMB (@lem6926662) (@lem6926650)). Qed.
Lemma lem6926665 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6926666 : term343 = term108.
Proof. exact (@lem6926665 term123). Qed.
Lemma lem6926667 : term350 = term108.
Proof. exact (TRANS (@lem6926663) (@lem6926666)). Qed.
Lemma lem6926668 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6926669 : term352 = term353.
Proof. exact (MK_COMB (@lem6926668) (@lem6926667)). Qed.
Lemma lem6926670 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6926671 : term354 = term311.
Proof. exact (MK_COMB (@lem6926669) (@lem6926670)). Qed.
Lemma lem6926673 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6926674 : term311 = term108.
Proof. exact (@lem6926673 term123). Qed.
Lemma lem6926675 : term354 = term108.
Proof. exact (TRANS (@lem6926671) (@lem6926674)). Qed.
Lemma lem6926677 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6926678 : term166 = term167.
Proof. exact (@lem6926677 term123 term123). Qed.
Lemma lem6926679 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926680 : term169 = term123.
Proof. exact (EQ_MP (@lem6926679) (@lem940073)). Qed.
Lemma lem6926681 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926682 : term167 = term122.
Proof. exact (MK_COMB (@lem6926681) (@lem6926680)). Qed.
Lemma lem6926683 : term166 = term122.
Proof. exact (TRANS (@lem6926678) (@lem6926682)). Qed.
Lemma lem6926684 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6926685 : term355 = term311.
Proof. exact (MK_COMB (@lem6926684) (@lem6926683)). Qed.
Lemma lem6926687 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6926688 : term311 = term108.
Proof. exact (@lem6926687 term123). Qed.
Lemma lem6926689 : term355 = term108.
Proof. exact (TRANS (@lem6926685) (@lem6926688)). Qed.
Lemma lem6926690 : term108 = term355.
Proof. exact (SYM (@lem6926689)). Qed.
Lemma lem6926691 : term354 = term355.
Proof. exact (TRANS (@lem6926675) (@lem6926690)). Qed.
Lemma lem6926692 : term344 = term154.
Proof. exact (@lem6926642 (@lem6926691)). Qed.
Lemma lem6926693 : term343 = term154.
Proof. exact (TRANS (@lem6926608) (@lem6926692)). Qed.
Lemma lem6926695 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6926696 : term154 = term108.
Proof. exact (@lem6926695 term108). Qed.
Lemma lem6926697 : term343 = term108.
Proof. exact (TRANS (@lem6926693) (@lem6926696)). Qed.
Lemma lem6926698 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6926699 : term356 = term353.
Proof. exact (MK_COMB (@lem6926698) (@lem6926697)). Qed.
Lemma lem6926700 (_92402 : int) : (real_of_int _92402) = (real_of_int _92402).
Proof. exact (eq_refl (real_of_int _92402)). Qed.
Lemma lem6926701 (_92402 : int) : (term340 _92402) = (term357 _92402).
Proof. exact (MK_COMB (@lem6926699) (@lem6926700 _92402)). Qed.
Lemma lem6926702 (_92402 : int) : (term339 _92402) = (term357 _92402).
Proof. exact (TRANS (@lem6926599 _92402) (@lem6926701 _92402)). Qed.
Lemma lem6926703 (_92402 : int) : (term357 _92402) = term108.
Proof. exact (@lem1982719 (real_of_int _92402)). Qed.
Lemma lem6926704 (_92402 : int) : (term339 _92402) = term108.
Proof. exact (TRANS (@lem6926702 _92402) (@lem6926703 _92402)). Qed.
Lemma lem6926705 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6926706 (_92402 : int) : (term358 _92402) = term359.
Proof. exact (MK_COMB (@lem6926705) (@lem6926704 _92402)). Qed.
Lemma lem6926707 (_92403 : int) : (term360 _92403) = (term340 _92403).
Proof. exact (@lem1982715 term157 (real_of_int _92403)). Qed.
Lemma lem6926709 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6926710 : term122 = term192.
Proof. exact (@lem6926709 term123). Qed.
Lemma lem6926712 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6926713 : term157 = term158.
Proof. exact (@lem6926712 term123). Qed.
Lemma lem6926714 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6926715 : term341 = term342.
Proof. exact (MK_COMB (@lem6926714) (@lem6926713)). Qed.
Lemma lem6926716 : term343 = term344.
Proof. exact (MK_COMB (@lem6926715) (@lem6926710)). Qed.
Lemma lem6926717 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6926719 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926720 : term300 = term306.
Proof. exact (@lem6926719 (NUMERAL 0) term123). Qed.
Lemma lem6926721 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926722 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926723 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926722 h1) (fun h1 : term306 = True => @lem6926721)). Qed.
Lemma lem6926724 : term306 = True.
Proof. exact (EQ_MP (@lem6926723) (@lem6926721)). Qed.
Lemma lem6926725 : term300 = True.
Proof. exact (TRANS (@lem6926720) (@lem6926724)). Qed.
Lemma lem6926726 : True = term300.
Proof. exact (SYM (@lem6926725)). Qed.
Lemma lem6926727 : term300.
Proof. exact (EQ_MP (@lem6926726) (@lem0)). Qed.
Lemma lem6926728 : term346.
Proof. exact (@lem6926717 (@lem6926727)). Qed.
Lemma lem6926730 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926731 : term300 = term306.
Proof. exact (@lem6926730 (NUMERAL 0) term123). Qed.
Lemma lem6926732 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926733 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926734 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926733 h1) (fun h1 : term306 = True => @lem6926732)). Qed.
Lemma lem6926735 : term306 = True.
Proof. exact (EQ_MP (@lem6926734) (@lem6926732)). Qed.
Lemma lem6926736 : term300 = True.
Proof. exact (TRANS (@lem6926731) (@lem6926735)). Qed.
Lemma lem6926737 : True = term300.
Proof. exact (SYM (@lem6926736)). Qed.
Lemma lem6926738 : term300.
Proof. exact (EQ_MP (@lem6926737) (@lem0)). Qed.
Lemma lem6926739 : term347.
Proof. exact (@lem6926728 (@lem6926738)). Qed.
Lemma lem6926741 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926742 : term300 = term306.
Proof. exact (@lem6926741 (NUMERAL 0) term123). Qed.
Lemma lem6926743 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926744 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926745 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926744 h1) (fun h1 : term306 = True => @lem6926743)). Qed.
Lemma lem6926746 : term306 = True.
Proof. exact (EQ_MP (@lem6926745) (@lem6926743)). Qed.
Lemma lem6926747 : term300 = True.
Proof. exact (TRANS (@lem6926742) (@lem6926746)). Qed.
Lemma lem6926748 : True = term300.
Proof. exact (SYM (@lem6926747)). Qed.
Lemma lem6926749 : term300.
Proof. exact (EQ_MP (@lem6926748) (@lem0)). Qed.
Lemma lem6926750 : term348.
Proof. exact (@lem6926739 (@lem6926749)). Qed.
Lemma lem6926752 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6926753 : term166 = term167.
Proof. exact (@lem6926752 term123 term123). Qed.
Lemma lem6926754 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926755 : term169 = term123.
Proof. exact (EQ_MP (@lem6926754) (@lem940073)). Qed.
Lemma lem6926756 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926757 : term167 = term122.
Proof. exact (MK_COMB (@lem6926756) (@lem6926755)). Qed.
Lemma lem6926758 : term166 = term122.
Proof. exact (TRANS (@lem6926753) (@lem6926757)). Qed.
Lemma lem6926760 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6926761 : term193 = term198.
Proof. exact (@lem6926760 term123 term123). Qed.
Lemma lem6926762 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926763 : term169 = term123.
Proof. exact (EQ_MP (@lem6926762) (@lem940073)). Qed.
Lemma lem6926764 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926765 : term167 = term122.
Proof. exact (MK_COMB (@lem6926764) (@lem6926763)). Qed.
Lemma lem6926766 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6926767 : term198 = term157.
Proof. exact (MK_COMB (@lem6926766) (@lem6926765)). Qed.
Lemma lem6926768 : term193 = term157.
Proof. exact (TRANS (@lem6926761) (@lem6926767)). Qed.
Lemma lem6926769 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6926770 : term349 = term341.
Proof. exact (MK_COMB (@lem6926769) (@lem6926768)). Qed.
Lemma lem6926771 : term350 = term343.
Proof. exact (MK_COMB (@lem6926770) (@lem6926758)). Qed.
Lemma lem6926773 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6926774 : term343 = term108.
Proof. exact (@lem6926773 term123). Qed.
Lemma lem6926775 : term350 = term108.
Proof. exact (TRANS (@lem6926771) (@lem6926774)). Qed.
Lemma lem6926776 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6926777 : term352 = term353.
Proof. exact (MK_COMB (@lem6926776) (@lem6926775)). Qed.
Lemma lem6926778 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6926779 : term354 = term311.
Proof. exact (MK_COMB (@lem6926777) (@lem6926778)). Qed.
Lemma lem6926781 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6926782 : term311 = term108.
Proof. exact (@lem6926781 term123). Qed.
Lemma lem6926783 : term354 = term108.
Proof. exact (TRANS (@lem6926779) (@lem6926782)). Qed.
Lemma lem6926785 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6926786 : term166 = term167.
Proof. exact (@lem6926785 term123 term123). Qed.
Lemma lem6926787 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926788 : term169 = term123.
Proof. exact (EQ_MP (@lem6926787) (@lem940073)). Qed.
Lemma lem6926789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926790 : term167 = term122.
Proof. exact (MK_COMB (@lem6926789) (@lem6926788)). Qed.
Lemma lem6926791 : term166 = term122.
Proof. exact (TRANS (@lem6926786) (@lem6926790)). Qed.
Lemma lem6926792 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6926793 : term355 = term311.
Proof. exact (MK_COMB (@lem6926792) (@lem6926791)). Qed.
Lemma lem6926795 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6926796 : term311 = term108.
Proof. exact (@lem6926795 term123). Qed.
Lemma lem6926797 : term355 = term108.
Proof. exact (TRANS (@lem6926793) (@lem6926796)). Qed.
Lemma lem6926798 : term108 = term355.
Proof. exact (SYM (@lem6926797)). Qed.
Lemma lem6926799 : term354 = term355.
Proof. exact (TRANS (@lem6926783) (@lem6926798)). Qed.
Lemma lem6926800 : term344 = term154.
Proof. exact (@lem6926750 (@lem6926799)). Qed.
Lemma lem6926801 : term343 = term154.
Proof. exact (TRANS (@lem6926716) (@lem6926800)). Qed.
Lemma lem6926803 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6926804 : term154 = term108.
Proof. exact (@lem6926803 term108). Qed.
Lemma lem6926805 : term343 = term108.
Proof. exact (TRANS (@lem6926801) (@lem6926804)). Qed.
Lemma lem6926806 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6926807 : term356 = term353.
Proof. exact (MK_COMB (@lem6926806) (@lem6926805)). Qed.
Lemma lem6926808 (_92403 : int) : (real_of_int _92403) = (real_of_int _92403).
Proof. exact (eq_refl (real_of_int _92403)). Qed.
Lemma lem6926809 (_92403 : int) : (term340 _92403) = (term357 _92403).
Proof. exact (MK_COMB (@lem6926807) (@lem6926808 _92403)). Qed.
Lemma lem6926810 (_92403 : int) : (term360 _92403) = (term357 _92403).
Proof. exact (TRANS (@lem6926707 _92403) (@lem6926809 _92403)). Qed.
Lemma lem6926811 (_92403 : int) : (term357 _92403) = term108.
Proof. exact (@lem1982719 (real_of_int _92403)). Qed.
Lemma lem6926812 (_92403 : int) : (term360 _92403) = term108.
Proof. exact (TRANS (@lem6926810 _92403) (@lem6926811 _92403)). Qed.
Lemma lem6926813 (_92402 : int) (_92403 : int) : (term338 _92402 _92403) = term361.
Proof. exact (MK_COMB (@lem6926706 _92402) (@lem6926812 _92403)). Qed.
Lemma lem6926814 (_92402 : int) (_92403 : int) : (term337 _92402 _92403) = term361.
Proof. exact (TRANS (@lem6926598 _92402 _92403) (@lem6926813 _92402 _92403)). Qed.
Lemma lem6926815 : term361 = term108.
Proof. exact (@lem1982721 term108). Qed.
Lemma lem6926816 (_92402 : int) (_92403 : int) : (term337 _92402 _92403) = term108.
Proof. exact (TRANS (@lem6926814 _92402 _92403) (@lem6926815)). Qed.
Lemma lem6926817 (_92401 : int) : (term124 _92401) = (term124 _92401).
Proof. exact (eq_refl (term124 _92401)). Qed.
Lemma lem6926818 (_92402 : int) (_92403 : int) (_92401 : int) : (term336 _92401 _92402 _92403) = (term174 _92401).
Proof. exact (MK_COMB (@lem6926817 _92401) (@lem6926816 _92402 _92403)). Qed.
Lemma lem6926819 (_92402 : int) (_92403 : int) (_92401 : int) : (term335 _92401 _92402 _92403) = (term174 _92401).
Proof. exact (TRANS (@lem6926597 _92401 _92402 _92403) (@lem6926818 _92402 _92403 _92401)). Qed.
Lemma lem6926820 (_92401 : int) : (term174 _92401) = (real_of_int _92401).
Proof. exact (@lem1982723 (real_of_int _92401)). Qed.
Lemma lem6926821 (_92402 : int) (_92403 : int) (_92401 : int) : (term335 _92401 _92402 _92403) = (real_of_int _92401).
Proof. exact (TRANS (@lem6926819 _92402 _92403 _92401) (@lem6926820 _92401)). Qed.
Lemma lem6926822 (_92400 : int) : (term201 _92400) = (term201 _92400).
Proof. exact (eq_refl (term201 _92400)). Qed.
Lemma lem6926823 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term334 _92400 _92401 _92402 _92403) = (term217 _92400 _92401).
Proof. exact (MK_COMB (@lem6926822 _92400) (@lem6926821 _92402 _92403 _92401)). Qed.
Lemma lem6926824 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term333 _92401 _92400 _92402 _92403) = (term217 _92400 _92401).
Proof. exact (TRANS (@lem6926596 _92400 _92401 _92402 _92403) (@lem6926823 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926825 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6926826 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term362 _92401 _92400 _92402 _92403) = (term363 _92400 _92401).
Proof. exact (MK_COMB (@lem6926825) (@lem6926824 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6926827 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6926828 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : ((term333 _92401 _92400 _92402 _92403) = term108) = ((term217 _92400 _92401) = term108).
Proof. exact (MK_COMB (@lem6926826 _92402 _92403 _92400 _92401) (@lem6926827)). Qed.
Lemma lem6926829 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : (term217 _92400 _92401) = term108.
Proof. exact (EQ_MP (@lem6926828 _92402 _92403 _92400 _92401) (@lem6926595 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926831 (y : real) : term324 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6926832 (_92400 : int) (_92401 : int) : term364 _92400 _92401.
Proof. exact (@lem6926831 (term217 _92400 _92401)). Qed.
Lemma lem6926833 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term365 _92400 _92401.
Proof. exact (@lem6926832 _92400 _92401 (@lem6926829 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926834 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term366 _92400 _92401.
Proof. exact (@lem6926833 _92402 _92403 _92400 _92401 h1 term122). Qed.
Lemma lem6926835 (_92400 : int) (_92401 : int) : (term366 _92400 _92401) = ((term367 _92400 _92401) = term108).
Proof. exact (eq_refl (term366 _92400 _92401)). Qed.
Lemma lem6926836 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : (term367 _92400 _92401) = term108.
Proof. exact (EQ_MP (@lem6926835 _92400 _92401) (@lem6926834 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926837 (_92400 : int) (_92401 : int) : (term367 _92400 _92401) = (term217 _92400 _92401).
Proof. exact (@lem1982733 (term217 _92400 _92401)). Qed.
Lemma lem6926838 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6926839 (_92400 : int) (_92401 : int) : (term368 _92400 _92401) = (term363 _92400 _92401).
Proof. exact (MK_COMB (@lem6926838) (@lem6926837 _92400 _92401)). Qed.
Lemma lem6926840 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6926841 (_92400 : int) (_92401 : int) : ((term367 _92400 _92401) = term108) = ((term217 _92400 _92401) = term108).
Proof. exact (MK_COMB (@lem6926839 _92400 _92401) (@lem6926840)). Qed.
Lemma lem6926842 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : (term217 _92400 _92401) = term108.
Proof. exact (EQ_MP (@lem6926841 _92400 _92401) (@lem6926836 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926843 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term369 _92400 _92401.
Proof. exact (conj (@lem6926842 _92402 _92403 _92400 _92401 h1) (@lem6926503 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926845 (x : real) (y : real) : term370 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6926846 (_92400 : int) (_92401 : int) : term371 _92400 _92401.
Proof. exact (@lem6926845 (term217 _92400 _92401) (term203 _92400 _92401)). Qed.
Lemma lem6926847 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term372 _92400 _92401.
Proof. exact (@lem6926846 _92400 _92401 (@lem6926843 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6926848 (_92400 : int) (_92401 : int) : (term373 _92400 _92401) = (term374 _92400 _92401).
Proof. exact (@lem1982753 (term184 _92400) (real_of_int _92400) (real_of_int _92401) (term202 _92401)). Qed.
Lemma lem6926849 (_92400 : int) : (term339 _92400) = (term340 _92400).
Proof. exact (@lem1982713 term157 (real_of_int _92400)). Qed.
Lemma lem6926851 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6926852 : term122 = term192.
Proof. exact (@lem6926851 term123). Qed.
Lemma lem6926854 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6926855 : term157 = term158.
Proof. exact (@lem6926854 term123). Qed.
Lemma lem6926856 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6926857 : term341 = term342.
Proof. exact (MK_COMB (@lem6926856) (@lem6926855)). Qed.
Lemma lem6926858 : term343 = term344.
Proof. exact (MK_COMB (@lem6926857) (@lem6926852)). Qed.
Lemma lem6926859 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6926861 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926862 : term300 = term306.
Proof. exact (@lem6926861 (NUMERAL 0) term123). Qed.
Lemma lem6926863 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926864 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926865 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926864 h1) (fun h1 : term306 = True => @lem6926863)). Qed.
Lemma lem6926866 : term306 = True.
Proof. exact (EQ_MP (@lem6926865) (@lem6926863)). Qed.
Lemma lem6926867 : term300 = True.
Proof. exact (TRANS (@lem6926862) (@lem6926866)). Qed.
Lemma lem6926868 : True = term300.
Proof. exact (SYM (@lem6926867)). Qed.
Lemma lem6926869 : term300.
Proof. exact (EQ_MP (@lem6926868) (@lem0)). Qed.
Lemma lem6926870 : term346.
Proof. exact (@lem6926859 (@lem6926869)). Qed.
Lemma lem6926872 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926873 : term300 = term306.
Proof. exact (@lem6926872 (NUMERAL 0) term123). Qed.
Lemma lem6926874 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926875 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926876 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926875 h1) (fun h1 : term306 = True => @lem6926874)). Qed.
Lemma lem6926877 : term306 = True.
Proof. exact (EQ_MP (@lem6926876) (@lem6926874)). Qed.
Lemma lem6926878 : term300 = True.
Proof. exact (TRANS (@lem6926873) (@lem6926877)). Qed.
Lemma lem6926879 : True = term300.
Proof. exact (SYM (@lem6926878)). Qed.
Lemma lem6926880 : term300.
Proof. exact (EQ_MP (@lem6926879) (@lem0)). Qed.
Lemma lem6926881 : term347.
Proof. exact (@lem6926870 (@lem6926880)). Qed.
Lemma lem6926883 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926884 : term300 = term306.
Proof. exact (@lem6926883 (NUMERAL 0) term123). Qed.
Lemma lem6926885 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926886 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926887 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926886 h1) (fun h1 : term306 = True => @lem6926885)). Qed.
Lemma lem6926888 : term306 = True.
Proof. exact (EQ_MP (@lem6926887) (@lem6926885)). Qed.
Lemma lem6926889 : term300 = True.
Proof. exact (TRANS (@lem6926884) (@lem6926888)). Qed.
Lemma lem6926890 : True = term300.
Proof. exact (SYM (@lem6926889)). Qed.
Lemma lem6926891 : term300.
Proof. exact (EQ_MP (@lem6926890) (@lem0)). Qed.
Lemma lem6926892 : term348.
Proof. exact (@lem6926881 (@lem6926891)). Qed.
Lemma lem6926894 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6926895 : term166 = term167.
Proof. exact (@lem6926894 term123 term123). Qed.
Lemma lem6926896 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926897 : term169 = term123.
Proof. exact (EQ_MP (@lem6926896) (@lem940073)). Qed.
Lemma lem6926898 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926899 : term167 = term122.
Proof. exact (MK_COMB (@lem6926898) (@lem6926897)). Qed.
Lemma lem6926900 : term166 = term122.
Proof. exact (TRANS (@lem6926895) (@lem6926899)). Qed.
Lemma lem6926902 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6926903 : term193 = term198.
Proof. exact (@lem6926902 term123 term123). Qed.
Lemma lem6926904 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926905 : term169 = term123.
Proof. exact (EQ_MP (@lem6926904) (@lem940073)). Qed.
Lemma lem6926906 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926907 : term167 = term122.
Proof. exact (MK_COMB (@lem6926906) (@lem6926905)). Qed.
Lemma lem6926908 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6926909 : term198 = term157.
Proof. exact (MK_COMB (@lem6926908) (@lem6926907)). Qed.
Lemma lem6926910 : term193 = term157.
Proof. exact (TRANS (@lem6926903) (@lem6926909)). Qed.
Lemma lem6926911 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6926912 : term349 = term341.
Proof. exact (MK_COMB (@lem6926911) (@lem6926910)). Qed.
Lemma lem6926913 : term350 = term343.
Proof. exact (MK_COMB (@lem6926912) (@lem6926900)). Qed.
Lemma lem6926915 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6926916 : term343 = term108.
Proof. exact (@lem6926915 term123). Qed.
Lemma lem6926917 : term350 = term108.
Proof. exact (TRANS (@lem6926913) (@lem6926916)). Qed.
Lemma lem6926918 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6926919 : term352 = term353.
Proof. exact (MK_COMB (@lem6926918) (@lem6926917)). Qed.
Lemma lem6926920 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6926921 : term354 = term311.
Proof. exact (MK_COMB (@lem6926919) (@lem6926920)). Qed.
Lemma lem6926923 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6926924 : term311 = term108.
Proof. exact (@lem6926923 term123). Qed.
Lemma lem6926925 : term354 = term108.
Proof. exact (TRANS (@lem6926921) (@lem6926924)). Qed.
Lemma lem6926927 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6926928 : term166 = term167.
Proof. exact (@lem6926927 term123 term123). Qed.
Lemma lem6926929 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6926930 : term169 = term123.
Proof. exact (EQ_MP (@lem6926929) (@lem940073)). Qed.
Lemma lem6926931 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6926932 : term167 = term122.
Proof. exact (MK_COMB (@lem6926931) (@lem6926930)). Qed.
Lemma lem6926933 : term166 = term122.
Proof. exact (TRANS (@lem6926928) (@lem6926932)). Qed.
Lemma lem6926934 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6926935 : term355 = term311.
Proof. exact (MK_COMB (@lem6926934) (@lem6926933)). Qed.
Lemma lem6926937 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6926938 : term311 = term108.
Proof. exact (@lem6926937 term123). Qed.
Lemma lem6926939 : term355 = term108.
Proof. exact (TRANS (@lem6926935) (@lem6926938)). Qed.
Lemma lem6926940 : term108 = term355.
Proof. exact (SYM (@lem6926939)). Qed.
Lemma lem6926941 : term354 = term355.
Proof. exact (TRANS (@lem6926925) (@lem6926940)). Qed.
Lemma lem6926942 : term344 = term154.
Proof. exact (@lem6926892 (@lem6926941)). Qed.
Lemma lem6926943 : term343 = term154.
Proof. exact (TRANS (@lem6926858) (@lem6926942)). Qed.
Lemma lem6926945 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6926946 : term154 = term108.
Proof. exact (@lem6926945 term108). Qed.
Lemma lem6926947 : term343 = term108.
Proof. exact (TRANS (@lem6926943) (@lem6926946)). Qed.
Lemma lem6926948 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6926949 : term356 = term353.
Proof. exact (MK_COMB (@lem6926948) (@lem6926947)). Qed.
Lemma lem6926950 (_92400 : int) : (real_of_int _92400) = (real_of_int _92400).
Proof. exact (eq_refl (real_of_int _92400)). Qed.
Lemma lem6926951 (_92400 : int) : (term340 _92400) = (term357 _92400).
Proof. exact (MK_COMB (@lem6926949) (@lem6926950 _92400)). Qed.
Lemma lem6926952 (_92400 : int) : (term339 _92400) = (term357 _92400).
Proof. exact (TRANS (@lem6926849 _92400) (@lem6926951 _92400)). Qed.
Lemma lem6926953 (_92400 : int) : (term357 _92400) = term108.
Proof. exact (@lem1982719 (real_of_int _92400)). Qed.
Lemma lem6926954 (_92400 : int) : (term339 _92400) = term108.
Proof. exact (TRANS (@lem6926952 _92400) (@lem6926953 _92400)). Qed.
Lemma lem6926955 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6926956 (_92400 : int) : (term358 _92400) = term359.
Proof. exact (MK_COMB (@lem6926955) (@lem6926954 _92400)). Qed.
Lemma lem6926957 (_92401 : int) : (term375 _92401) = (term376 _92401).
Proof. exact (@lem1982763 (real_of_int _92401) (term184 _92401) term157). Qed.
Lemma lem6926958 (_92401 : int) : (term360 _92401) = (term340 _92401).
Proof. exact (@lem1982715 term157 (real_of_int _92401)). Qed.
Lemma lem6926960 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6926961 : term122 = term192.
Proof. exact (@lem6926960 term123). Qed.
Lemma lem6926963 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6926964 : term157 = term158.
Proof. exact (@lem6926963 term123). Qed.
Lemma lem6926965 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6926966 : term341 = term342.
Proof. exact (MK_COMB (@lem6926965) (@lem6926964)). Qed.
Lemma lem6926967 : term343 = term344.
Proof. exact (MK_COMB (@lem6926966) (@lem6926961)). Qed.
Lemma lem6926968 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6926970 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926971 : term300 = term306.
Proof. exact (@lem6926970 (NUMERAL 0) term123). Qed.
Lemma lem6926972 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926973 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926974 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926973 h1) (fun h1 : term306 = True => @lem6926972)). Qed.
Lemma lem6926975 : term306 = True.
Proof. exact (EQ_MP (@lem6926974) (@lem6926972)). Qed.
Lemma lem6926976 : term300 = True.
Proof. exact (TRANS (@lem6926971) (@lem6926975)). Qed.
Lemma lem6926977 : True = term300.
Proof. exact (SYM (@lem6926976)). Qed.
Lemma lem6926978 : term300.
Proof. exact (EQ_MP (@lem6926977) (@lem0)). Qed.
Lemma lem6926979 : term346.
Proof. exact (@lem6926968 (@lem6926978)). Qed.
Lemma lem6926981 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926982 : term300 = term306.
Proof. exact (@lem6926981 (NUMERAL 0) term123). Qed.
Lemma lem6926983 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926984 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926985 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926984 h1) (fun h1 : term306 = True => @lem6926983)). Qed.
Lemma lem6926986 : term306 = True.
Proof. exact (EQ_MP (@lem6926985) (@lem6926983)). Qed.
Lemma lem6926987 : term300 = True.
Proof. exact (TRANS (@lem6926982) (@lem6926986)). Qed.
Lemma lem6926988 : True = term300.
Proof. exact (SYM (@lem6926987)). Qed.
Lemma lem6926989 : term300.
Proof. exact (EQ_MP (@lem6926988) (@lem0)). Qed.
Lemma lem6926990 : term347.
Proof. exact (@lem6926979 (@lem6926989)). Qed.
Lemma lem6926992 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6926993 : term300 = term306.
Proof. exact (@lem6926992 (NUMERAL 0) term123). Qed.
Lemma lem6926994 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6926995 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6926996 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6926995 h1) (fun h1 : term306 = True => @lem6926994)). Qed.
Lemma lem6926997 : term306 = True.
Proof. exact (EQ_MP (@lem6926996) (@lem6926994)). Qed.
Lemma lem6926998 : term300 = True.
Proof. exact (TRANS (@lem6926993) (@lem6926997)). Qed.
Lemma lem6926999 : True = term300.
Proof. exact (SYM (@lem6926998)). Qed.
Lemma lem6927000 : term300.
Proof. exact (EQ_MP (@lem6926999) (@lem0)). Qed.
Lemma lem6927001 : term348.
Proof. exact (@lem6926990 (@lem6927000)). Qed.
Lemma lem6927003 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927004 : term166 = term167.
Proof. exact (@lem6927003 term123 term123). Qed.
Lemma lem6927005 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927006 : term169 = term123.
Proof. exact (EQ_MP (@lem6927005) (@lem940073)). Qed.
Lemma lem6927007 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927008 : term167 = term122.
Proof. exact (MK_COMB (@lem6927007) (@lem6927006)). Qed.
Lemma lem6927009 : term166 = term122.
Proof. exact (TRANS (@lem6927004) (@lem6927008)). Qed.
Lemma lem6927011 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6927012 : term193 = term198.
Proof. exact (@lem6927011 term123 term123). Qed.
Lemma lem6927013 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927014 : term169 = term123.
Proof. exact (EQ_MP (@lem6927013) (@lem940073)). Qed.
Lemma lem6927015 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927016 : term167 = term122.
Proof. exact (MK_COMB (@lem6927015) (@lem6927014)). Qed.
Lemma lem6927017 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6927018 : term198 = term157.
Proof. exact (MK_COMB (@lem6927017) (@lem6927016)). Qed.
Lemma lem6927019 : term193 = term157.
Proof. exact (TRANS (@lem6927012) (@lem6927018)). Qed.
Lemma lem6927020 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6927021 : term349 = term341.
Proof. exact (MK_COMB (@lem6927020) (@lem6927019)). Qed.
Lemma lem6927022 : term350 = term343.
Proof. exact (MK_COMB (@lem6927021) (@lem6927009)). Qed.
Lemma lem6927024 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6927025 : term343 = term108.
Proof. exact (@lem6927024 term123). Qed.
Lemma lem6927026 : term350 = term108.
Proof. exact (TRANS (@lem6927022) (@lem6927025)). Qed.
Lemma lem6927027 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6927028 : term352 = term353.
Proof. exact (MK_COMB (@lem6927027) (@lem6927026)). Qed.
Lemma lem6927029 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6927030 : term354 = term311.
Proof. exact (MK_COMB (@lem6927028) (@lem6927029)). Qed.
Lemma lem6927032 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927033 : term311 = term108.
Proof. exact (@lem6927032 term123). Qed.
Lemma lem6927034 : term354 = term108.
Proof. exact (TRANS (@lem6927030) (@lem6927033)). Qed.
Lemma lem6927036 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927037 : term166 = term167.
Proof. exact (@lem6927036 term123 term123). Qed.
Lemma lem6927038 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927039 : term169 = term123.
Proof. exact (EQ_MP (@lem6927038) (@lem940073)). Qed.
Lemma lem6927040 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927041 : term167 = term122.
Proof. exact (MK_COMB (@lem6927040) (@lem6927039)). Qed.
Lemma lem6927042 : term166 = term122.
Proof. exact (TRANS (@lem6927037) (@lem6927041)). Qed.
Lemma lem6927043 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6927044 : term355 = term311.
Proof. exact (MK_COMB (@lem6927043) (@lem6927042)). Qed.
Lemma lem6927046 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927047 : term311 = term108.
Proof. exact (@lem6927046 term123). Qed.
Lemma lem6927048 : term355 = term108.
Proof. exact (TRANS (@lem6927044) (@lem6927047)). Qed.
Lemma lem6927049 : term108 = term355.
Proof. exact (SYM (@lem6927048)). Qed.
Lemma lem6927050 : term354 = term355.
Proof. exact (TRANS (@lem6927034) (@lem6927049)). Qed.
Lemma lem6927051 : term344 = term154.
Proof. exact (@lem6927001 (@lem6927050)). Qed.
Lemma lem6927052 : term343 = term154.
Proof. exact (TRANS (@lem6926967) (@lem6927051)). Qed.
Lemma lem6927054 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6927055 : term154 = term108.
Proof. exact (@lem6927054 term108). Qed.
Lemma lem6927056 : term343 = term108.
Proof. exact (TRANS (@lem6927052) (@lem6927055)). Qed.
Lemma lem6927057 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6927058 : term356 = term353.
Proof. exact (MK_COMB (@lem6927057) (@lem6927056)). Qed.
Lemma lem6927059 (_92401 : int) : (real_of_int _92401) = (real_of_int _92401).
Proof. exact (eq_refl (real_of_int _92401)). Qed.
Lemma lem6927060 (_92401 : int) : (term340 _92401) = (term357 _92401).
Proof. exact (MK_COMB (@lem6927058) (@lem6927059 _92401)). Qed.
Lemma lem6927061 (_92401 : int) : (term360 _92401) = (term357 _92401).
Proof. exact (TRANS (@lem6926958 _92401) (@lem6927060 _92401)). Qed.
Lemma lem6927062 (_92401 : int) : (term357 _92401) = term108.
Proof. exact (@lem1982719 (real_of_int _92401)). Qed.
Lemma lem6927063 (_92401 : int) : (term360 _92401) = term108.
Proof. exact (TRANS (@lem6927061 _92401) (@lem6927062 _92401)). Qed.
Lemma lem6927064 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6927065 (_92401 : int) : (term377 _92401) = term359.
Proof. exact (MK_COMB (@lem6927064) (@lem6927063 _92401)). Qed.
Lemma lem6927066 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem6927067 (_92401 : int) : (term376 _92401) = term378.
Proof. exact (MK_COMB (@lem6927065 _92401) (@lem6927066)). Qed.
Lemma lem6927068 (_92401 : int) : (term375 _92401) = term378.
Proof. exact (TRANS (@lem6926957 _92401) (@lem6927067 _92401)). Qed.
Lemma lem6927069 : term378 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem6927070 (_92401 : int) : (term375 _92401) = term157.
Proof. exact (TRANS (@lem6927068 _92401) (@lem6927069)). Qed.
Lemma lem6927071 (_92400 : int) (_92401 : int) : (term374 _92400 _92401) = term378.
Proof. exact (MK_COMB (@lem6926956 _92400) (@lem6927070 _92401)). Qed.
Lemma lem6927072 (_92400 : int) (_92401 : int) : (term373 _92400 _92401) = term378.
Proof. exact (TRANS (@lem6926848 _92400 _92401) (@lem6927071 _92400 _92401)). Qed.
Lemma lem6927073 : term378 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem6927074 (_92400 : int) (_92401 : int) : (term373 _92400 _92401) = term157.
Proof. exact (TRANS (@lem6927072 _92400 _92401) (@lem6927073)). Qed.
Lemma lem6927075 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6927076 (_92400 : int) (_92401 : int) : (term379 _92400 _92401) = term380.
Proof. exact (MK_COMB (@lem6927075) (@lem6927074 _92400 _92401)). Qed.
Lemma lem6927077 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6927078 (_92400 : int) (_92401 : int) : (term372 _92400 _92401) = term381.
Proof. exact (MK_COMB (@lem6927076 _92400 _92401) (@lem6927077)). Qed.
Lemma lem6927079 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : term381.
Proof. exact (EQ_MP (@lem6927078 _92400 _92401) (@lem6926847 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927081 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6927082 : term381 = term382.
Proof. exact (@lem6927081 term108 term157). Qed.
Lemma lem6927084 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6927085 : term157 = term158.
Proof. exact (@lem6927084 term123). Qed.
Lemma lem6927087 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927088 : term108 = term154.
Proof. exact (@lem6927087 (NUMERAL 0)). Qed.
Lemma lem6927089 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6927090 : term110 = term383.
Proof. exact (MK_COMB (@lem6927089) (@lem6927088)). Qed.
Lemma lem6927091 : term382 = term384.
Proof. exact (MK_COMB (@lem6927090) (@lem6927085)). Qed.
Lemma lem6927092 : term385.
Proof. exact (@lem1980026 term108 term122 term157 term122). Qed.
Lemma lem6927094 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927095 : term300 = term306.
Proof. exact (@lem6927094 (NUMERAL 0) term123). Qed.
Lemma lem6927096 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927097 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927098 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927097 h1) (fun h1 : term306 = True => @lem6927096)). Qed.
Lemma lem6927099 : term306 = True.
Proof. exact (EQ_MP (@lem6927098) (@lem6927096)). Qed.
Lemma lem6927100 : term300 = True.
Proof. exact (TRANS (@lem6927095) (@lem6927099)). Qed.
Lemma lem6927101 : True = term300.
Proof. exact (SYM (@lem6927100)). Qed.
Lemma lem6927102 : term300.
Proof. exact (EQ_MP (@lem6927101) (@lem0)). Qed.
Lemma lem6927103 : term386.
Proof. exact (@lem6927092 (@lem6927102)). Qed.
Lemma lem6927105 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927106 : term300 = term306.
Proof. exact (@lem6927105 (NUMERAL 0) term123). Qed.
Lemma lem6927107 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927108 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927109 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927108 h1) (fun h1 : term306 = True => @lem6927107)). Qed.
Lemma lem6927110 : term306 = True.
Proof. exact (EQ_MP (@lem6927109) (@lem6927107)). Qed.
Lemma lem6927111 : term300 = True.
Proof. exact (TRANS (@lem6927106) (@lem6927110)). Qed.
Lemma lem6927112 : True = term300.
Proof. exact (SYM (@lem6927111)). Qed.
Lemma lem6927113 : term300.
Proof. exact (EQ_MP (@lem6927112) (@lem0)). Qed.
Lemma lem6927114 : term384 = term387.
Proof. exact (@lem6927103 (@lem6927113)). Qed.
Lemma lem6927116 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6927117 : term193 = term198.
Proof. exact (@lem6927116 term123 term123). Qed.
Lemma lem6927118 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927119 : term169 = term123.
Proof. exact (EQ_MP (@lem6927118) (@lem940073)). Qed.
Lemma lem6927120 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927121 : term167 = term122.
Proof. exact (MK_COMB (@lem6927120) (@lem6927119)). Qed.
Lemma lem6927122 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6927123 : term198 = term157.
Proof. exact (MK_COMB (@lem6927122) (@lem6927121)). Qed.
Lemma lem6927124 : term193 = term157.
Proof. exact (TRANS (@lem6927117) (@lem6927123)). Qed.
Lemma lem6927126 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927127 : term311 = term108.
Proof. exact (@lem6927126 term123). Qed.
Lemma lem6927128 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6927129 : term388 = term110.
Proof. exact (MK_COMB (@lem6927128) (@lem6927127)). Qed.
Lemma lem6927130 : term387 = term382.
Proof. exact (MK_COMB (@lem6927129) (@lem6927124)). Qed.
Lemma lem6927132 (m : nat) (n : nat) : (term389 m n) = (term390 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6927133 : term382 = term391.
Proof. exact (@lem6927132 (NUMERAL 0) term123). Qed.
Lemma lem6927134 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927135 (h1 : term307 = (BIT1 0)) : (term123 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6927136 : (term307 = (BIT1 0)) = ((term123 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927135 h1) (fun h1 : (term123 = (NUMERAL 0)) = False => @lem6927134)). Qed.
Lemma lem6927137 : (term123 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6927136) (@lem6927134)). Qed.
Lemma lem6927138 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6927139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6927140 : term392 = (and True).
Proof. exact (MK_COMB (@lem6927139) (@lem6927138)). Qed.
Lemma lem6927141 : term391 = (True /\ False).
Proof. exact (MK_COMB (@lem6927140) (@lem6927137)). Qed.
Lemma lem6927143 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6927144 : term391 = False.
Proof. exact (TRANS (@lem6927141) (@lem6927143)). Qed.
Lemma lem6927145 : term382 = False.
Proof. exact (TRANS (@lem6927133) (@lem6927144)). Qed.
Lemma lem6927146 : term387 = False.
Proof. exact (TRANS (@lem6927130) (@lem6927145)). Qed.
Lemma lem6927147 : term384 = False.
Proof. exact (TRANS (@lem6927114) (@lem6927146)). Qed.
Lemma lem6927148 : term382 = False.
Proof. exact (TRANS (@lem6927091) (@lem6927147)). Qed.
Lemma lem6927149 : term381 = False.
Proof. exact (TRANS (@lem6927082) (@lem6927148)). Qed.
Lemma lem6927150 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term298 _92402 _92403 _92400 _92401) : False.
Proof. exact (EQ_MP (@lem6927149) (@lem6927079 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927151 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term393 _92402 _92403 _92400 _92401.
Proof. exact (h1). Qed.
Lemma lem6927152 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term294 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6927151 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927154 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term281 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6927152 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927155 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term177 _92401.
Proof. exact (proj1 (@lem6927152 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927156 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term268 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6927154 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927158 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term255 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6927156 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927160 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term237 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6927158 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927161 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term210 _92402 _92403 _92400.
Proof. exact (proj1 (@lem6927158 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927162 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : (real_of_int _92400) = term108.
Proof. exact (proj2 (@lem6927161 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927164 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term222 _92400 _92401.
Proof. exact (proj2 (@lem6927160 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927167 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6927168 : term299 = term300.
Proof. exact (@lem6927167 term108 term122). Qed.
Lemma lem6927170 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927171 : term122 = term192.
Proof. exact (@lem6927170 term123). Qed.
Lemma lem6927173 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927174 : term108 = term154.
Proof. exact (@lem6927173 (NUMERAL 0)). Qed.
Lemma lem6927175 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6927176 : term301 = term302.
Proof. exact (MK_COMB (@lem6927175) (@lem6927174)). Qed.
Lemma lem6927177 : term300 = term303.
Proof. exact (MK_COMB (@lem6927176) (@lem6927171)). Qed.
Lemma lem6927178 : term304.
Proof. exact (@lem1980255 term108 term122 term122 term122). Qed.
Lemma lem6927180 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927181 : term300 = term306.
Proof. exact (@lem6927180 (NUMERAL 0) term123). Qed.
Lemma lem6927182 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927183 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927184 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927183 h1) (fun h1 : term306 = True => @lem6927182)). Qed.
Lemma lem6927185 : term306 = True.
Proof. exact (EQ_MP (@lem6927184) (@lem6927182)). Qed.
Lemma lem6927186 : term300 = True.
Proof. exact (TRANS (@lem6927181) (@lem6927185)). Qed.
Lemma lem6927187 : True = term300.
Proof. exact (SYM (@lem6927186)). Qed.
Lemma lem6927188 : term300.
Proof. exact (EQ_MP (@lem6927187) (@lem0)). Qed.
Lemma lem6927189 : term308.
Proof. exact (@lem6927178 (@lem6927188)). Qed.
Lemma lem6927191 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927192 : term300 = term306.
Proof. exact (@lem6927191 (NUMERAL 0) term123). Qed.
Lemma lem6927193 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927194 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927195 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927194 h1) (fun h1 : term306 = True => @lem6927193)). Qed.
Lemma lem6927196 : term306 = True.
Proof. exact (EQ_MP (@lem6927195) (@lem6927193)). Qed.
Lemma lem6927197 : term300 = True.
Proof. exact (TRANS (@lem6927192) (@lem6927196)). Qed.
Lemma lem6927198 : True = term300.
Proof. exact (SYM (@lem6927197)). Qed.
Lemma lem6927199 : term300.
Proof. exact (EQ_MP (@lem6927198) (@lem0)). Qed.
Lemma lem6927200 : term303 = term309.
Proof. exact (@lem6927189 (@lem6927199)). Qed.
Lemma lem6927202 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927203 : term166 = term167.
Proof. exact (@lem6927202 term123 term123). Qed.
Lemma lem6927204 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927205 : term169 = term123.
Proof. exact (EQ_MP (@lem6927204) (@lem940073)). Qed.
Lemma lem6927206 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927207 : term167 = term122.
Proof. exact (MK_COMB (@lem6927206) (@lem6927205)). Qed.
Lemma lem6927208 : term166 = term122.
Proof. exact (TRANS (@lem6927203) (@lem6927207)). Qed.
Lemma lem6927210 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927211 : term311 = term108.
Proof. exact (@lem6927210 term123). Qed.
Lemma lem6927212 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6927213 : term312 = term301.
Proof. exact (MK_COMB (@lem6927212) (@lem6927211)). Qed.
Lemma lem6927214 : term309 = term300.
Proof. exact (MK_COMB (@lem6927213) (@lem6927208)). Qed.
Lemma lem6927216 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927217 : term300 = term306.
Proof. exact (@lem6927216 (NUMERAL 0) term123). Qed.
Lemma lem6927218 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927219 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927220 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927219 h1) (fun h1 : term306 = True => @lem6927218)). Qed.
Lemma lem6927221 : term306 = True.
Proof. exact (EQ_MP (@lem6927220) (@lem6927218)). Qed.
Lemma lem6927222 : term300 = True.
Proof. exact (TRANS (@lem6927217) (@lem6927221)). Qed.
Lemma lem6927223 : term309 = True.
Proof. exact (TRANS (@lem6927214) (@lem6927222)). Qed.
Lemma lem6927224 : term303 = True.
Proof. exact (TRANS (@lem6927200) (@lem6927223)). Qed.
Lemma lem6927225 : term300 = True.
Proof. exact (TRANS (@lem6927177) (@lem6927224)). Qed.
Lemma lem6927226 : term299 = True.
Proof. exact (TRANS (@lem6927168) (@lem6927225)). Qed.
Lemma lem6927227 : True = term299.
Proof. exact (SYM (@lem6927226)). Qed.
Lemma lem6927228 : term299.
Proof. exact (EQ_MP (@lem6927227) (@lem0)). Qed.
Lemma lem6927229 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term394 _92401.
Proof. exact (conj (@lem6927228) (@lem6927155 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927231 (x : real) (y : real) : term314 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6927232 (_92401 : int) : term395 _92401.
Proof. exact (@lem6927231 term122 (real_of_int _92401)). Qed.
Lemma lem6927233 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term396 _92401.
Proof. exact (@lem6927232 _92401 (@lem6927229 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927234 (_92401 : int) : (term397 _92401) = (real_of_int _92401).
Proof. exact (@lem1982733 (real_of_int _92401)). Qed.
Lemma lem6927235 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6927236 (_92401 : int) : (term398 _92401) = (term176 _92401).
Proof. exact (MK_COMB (@lem6927235) (@lem6927234 _92401)). Qed.
Lemma lem6927237 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6927238 (_92401 : int) : (term396 _92401) = (term177 _92401).
Proof. exact (MK_COMB (@lem6927236 _92401) (@lem6927237)). Qed.
Lemma lem6927239 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term177 _92401.
Proof. exact (EQ_MP (@lem6927238 _92401) (@lem6927233 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927241 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6927242 : term299 = term300.
Proof. exact (@lem6927241 term108 term122). Qed.
Lemma lem6927244 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927245 : term122 = term192.
Proof. exact (@lem6927244 term123). Qed.
Lemma lem6927247 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927248 : term108 = term154.
Proof. exact (@lem6927247 (NUMERAL 0)). Qed.
Lemma lem6927249 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6927250 : term301 = term302.
Proof. exact (MK_COMB (@lem6927249) (@lem6927248)). Qed.
Lemma lem6927251 : term300 = term303.
Proof. exact (MK_COMB (@lem6927250) (@lem6927245)). Qed.
Lemma lem6927252 : term304.
Proof. exact (@lem1980255 term108 term122 term122 term122). Qed.
Lemma lem6927254 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927255 : term300 = term306.
Proof. exact (@lem6927254 (NUMERAL 0) term123). Qed.
Lemma lem6927256 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927257 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927258 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927257 h1) (fun h1 : term306 = True => @lem6927256)). Qed.
Lemma lem6927259 : term306 = True.
Proof. exact (EQ_MP (@lem6927258) (@lem6927256)). Qed.
Lemma lem6927260 : term300 = True.
Proof. exact (TRANS (@lem6927255) (@lem6927259)). Qed.
Lemma lem6927261 : True = term300.
Proof. exact (SYM (@lem6927260)). Qed.
Lemma lem6927262 : term300.
Proof. exact (EQ_MP (@lem6927261) (@lem0)). Qed.
Lemma lem6927263 : term308.
Proof. exact (@lem6927252 (@lem6927262)). Qed.
Lemma lem6927265 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927266 : term300 = term306.
Proof. exact (@lem6927265 (NUMERAL 0) term123). Qed.
Lemma lem6927267 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927268 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927269 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927268 h1) (fun h1 : term306 = True => @lem6927267)). Qed.
Lemma lem6927270 : term306 = True.
Proof. exact (EQ_MP (@lem6927269) (@lem6927267)). Qed.
Lemma lem6927271 : term300 = True.
Proof. exact (TRANS (@lem6927266) (@lem6927270)). Qed.
Lemma lem6927272 : True = term300.
Proof. exact (SYM (@lem6927271)). Qed.
Lemma lem6927273 : term300.
Proof. exact (EQ_MP (@lem6927272) (@lem0)). Qed.
Lemma lem6927274 : term303 = term309.
Proof. exact (@lem6927263 (@lem6927273)). Qed.
Lemma lem6927276 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927277 : term166 = term167.
Proof. exact (@lem6927276 term123 term123). Qed.
Lemma lem6927278 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927279 : term169 = term123.
Proof. exact (EQ_MP (@lem6927278) (@lem940073)). Qed.
Lemma lem6927280 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927281 : term167 = term122.
Proof. exact (MK_COMB (@lem6927280) (@lem6927279)). Qed.
Lemma lem6927282 : term166 = term122.
Proof. exact (TRANS (@lem6927277) (@lem6927281)). Qed.
Lemma lem6927284 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927285 : term311 = term108.
Proof. exact (@lem6927284 term123). Qed.
Lemma lem6927286 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6927287 : term312 = term301.
Proof. exact (MK_COMB (@lem6927286) (@lem6927285)). Qed.
Lemma lem6927288 : term309 = term300.
Proof. exact (MK_COMB (@lem6927287) (@lem6927282)). Qed.
Lemma lem6927290 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927291 : term300 = term306.
Proof. exact (@lem6927290 (NUMERAL 0) term123). Qed.
Lemma lem6927292 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927293 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927294 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927293 h1) (fun h1 : term306 = True => @lem6927292)). Qed.
Lemma lem6927295 : term306 = True.
Proof. exact (EQ_MP (@lem6927294) (@lem6927292)). Qed.
Lemma lem6927296 : term300 = True.
Proof. exact (TRANS (@lem6927291) (@lem6927295)). Qed.
Lemma lem6927297 : term309 = True.
Proof. exact (TRANS (@lem6927288) (@lem6927296)). Qed.
Lemma lem6927298 : term303 = True.
Proof. exact (TRANS (@lem6927274) (@lem6927297)). Qed.
Lemma lem6927299 : term300 = True.
Proof. exact (TRANS (@lem6927251) (@lem6927298)). Qed.
Lemma lem6927300 : term299 = True.
Proof. exact (TRANS (@lem6927242) (@lem6927299)). Qed.
Lemma lem6927301 : True = term299.
Proof. exact (SYM (@lem6927300)). Qed.
Lemma lem6927302 : term299.
Proof. exact (EQ_MP (@lem6927301) (@lem0)). Qed.
Lemma lem6927303 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term313 _92400 _92401.
Proof. exact (conj (@lem6927302) (@lem6927164 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927305 (x : real) (y : real) : term314 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6927306 (_92400 : int) (_92401 : int) : term315 _92400 _92401.
Proof. exact (@lem6927305 term122 (term203 _92400 _92401)). Qed.
Lemma lem6927307 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term316 _92400 _92401.
Proof. exact (@lem6927306 _92400 _92401 (@lem6927303 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927308 (_92400 : int) (_92401 : int) : (term317 _92400 _92401) = (term203 _92400 _92401).
Proof. exact (@lem1982733 (term203 _92400 _92401)). Qed.
Lemma lem6927309 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6927310 (_92400 : int) (_92401 : int) : (term318 _92400 _92401) = (term221 _92400 _92401).
Proof. exact (MK_COMB (@lem6927309) (@lem6927308 _92400 _92401)). Qed.
Lemma lem6927311 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6927312 (_92400 : int) (_92401 : int) : (term316 _92400 _92401) = (term222 _92400 _92401).
Proof. exact (MK_COMB (@lem6927310 _92400 _92401) (@lem6927311)). Qed.
Lemma lem6927313 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term222 _92400 _92401.
Proof. exact (EQ_MP (@lem6927312 _92400 _92401) (@lem6927307 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927315 (y : real) : term324 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6927316 (_92400 : int) : term399 _92400.
Proof. exact (@lem6927315 (real_of_int _92400)). Qed.
Lemma lem6927317 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term400 _92400.
Proof. exact (@lem6927316 _92400 (@lem6927162 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927318 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term401 _92400.
Proof. exact (@lem6927317 _92402 _92403 _92400 _92401 h1 term157). Qed.
Lemma lem6927319 (_92400 : int) : (term401 _92400) = ((term184 _92400) = term108).
Proof. exact (eq_refl (term401 _92400)). Qed.
Lemma lem6927326 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : (term184 _92400) = term108.
Proof. exact (EQ_MP (@lem6927319 _92400) (@lem6927318 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927327 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term402 _92400 _92401.
Proof. exact (conj (@lem6927326 _92402 _92403 _92400 _92401 h1) (@lem6927313 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927329 (x : real) (y : real) : term370 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6927330 (_92400 : int) (_92401 : int) : term403 _92400 _92401.
Proof. exact (@lem6927329 (term184 _92400) (term203 _92400 _92401)). Qed.
Lemma lem6927331 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term404 _92400 _92401.
Proof. exact (@lem6927330 _92400 _92401 (@lem6927327 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927332 (_92400 : int) (_92401 : int) : (term405 _92400 _92401) = (term406 _92400 _92401).
Proof. exact (@lem1982763 (term184 _92400) (real_of_int _92400) (term202 _92401)). Qed.
Lemma lem6927333 (_92400 : int) : (term339 _92400) = (term340 _92400).
Proof. exact (@lem1982713 term157 (real_of_int _92400)). Qed.
Lemma lem6927335 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927336 : term122 = term192.
Proof. exact (@lem6927335 term123). Qed.
Lemma lem6927338 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6927339 : term157 = term158.
Proof. exact (@lem6927338 term123). Qed.
Lemma lem6927340 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6927341 : term341 = term342.
Proof. exact (MK_COMB (@lem6927340) (@lem6927339)). Qed.
Lemma lem6927342 : term343 = term344.
Proof. exact (MK_COMB (@lem6927341) (@lem6927336)). Qed.
Lemma lem6927343 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6927345 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927346 : term300 = term306.
Proof. exact (@lem6927345 (NUMERAL 0) term123). Qed.
Lemma lem6927347 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927348 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927349 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927348 h1) (fun h1 : term306 = True => @lem6927347)). Qed.
Lemma lem6927350 : term306 = True.
Proof. exact (EQ_MP (@lem6927349) (@lem6927347)). Qed.
Lemma lem6927351 : term300 = True.
Proof. exact (TRANS (@lem6927346) (@lem6927350)). Qed.
Lemma lem6927352 : True = term300.
Proof. exact (SYM (@lem6927351)). Qed.
Lemma lem6927353 : term300.
Proof. exact (EQ_MP (@lem6927352) (@lem0)). Qed.
Lemma lem6927354 : term346.
Proof. exact (@lem6927343 (@lem6927353)). Qed.
Lemma lem6927356 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927357 : term300 = term306.
Proof. exact (@lem6927356 (NUMERAL 0) term123). Qed.
Lemma lem6927358 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927359 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927360 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927359 h1) (fun h1 : term306 = True => @lem6927358)). Qed.
Lemma lem6927361 : term306 = True.
Proof. exact (EQ_MP (@lem6927360) (@lem6927358)). Qed.
Lemma lem6927362 : term300 = True.
Proof. exact (TRANS (@lem6927357) (@lem6927361)). Qed.
Lemma lem6927363 : True = term300.
Proof. exact (SYM (@lem6927362)). Qed.
Lemma lem6927364 : term300.
Proof. exact (EQ_MP (@lem6927363) (@lem0)). Qed.
Lemma lem6927365 : term347.
Proof. exact (@lem6927354 (@lem6927364)). Qed.
Lemma lem6927367 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927368 : term300 = term306.
Proof. exact (@lem6927367 (NUMERAL 0) term123). Qed.
Lemma lem6927369 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927370 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927371 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927370 h1) (fun h1 : term306 = True => @lem6927369)). Qed.
Lemma lem6927372 : term306 = True.
Proof. exact (EQ_MP (@lem6927371) (@lem6927369)). Qed.
Lemma lem6927373 : term300 = True.
Proof. exact (TRANS (@lem6927368) (@lem6927372)). Qed.
Lemma lem6927374 : True = term300.
Proof. exact (SYM (@lem6927373)). Qed.
Lemma lem6927375 : term300.
Proof. exact (EQ_MP (@lem6927374) (@lem0)). Qed.
Lemma lem6927376 : term348.
Proof. exact (@lem6927365 (@lem6927375)). Qed.
Lemma lem6927378 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927379 : term166 = term167.
Proof. exact (@lem6927378 term123 term123). Qed.
Lemma lem6927380 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927381 : term169 = term123.
Proof. exact (EQ_MP (@lem6927380) (@lem940073)). Qed.
Lemma lem6927382 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927383 : term167 = term122.
Proof. exact (MK_COMB (@lem6927382) (@lem6927381)). Qed.
Lemma lem6927384 : term166 = term122.
Proof. exact (TRANS (@lem6927379) (@lem6927383)). Qed.
Lemma lem6927386 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6927387 : term193 = term198.
Proof. exact (@lem6927386 term123 term123). Qed.
Lemma lem6927388 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927389 : term169 = term123.
Proof. exact (EQ_MP (@lem6927388) (@lem940073)). Qed.
Lemma lem6927390 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927391 : term167 = term122.
Proof. exact (MK_COMB (@lem6927390) (@lem6927389)). Qed.
Lemma lem6927392 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6927393 : term198 = term157.
Proof. exact (MK_COMB (@lem6927392) (@lem6927391)). Qed.
Lemma lem6927394 : term193 = term157.
Proof. exact (TRANS (@lem6927387) (@lem6927393)). Qed.
Lemma lem6927395 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6927396 : term349 = term341.
Proof. exact (MK_COMB (@lem6927395) (@lem6927394)). Qed.
Lemma lem6927397 : term350 = term343.
Proof. exact (MK_COMB (@lem6927396) (@lem6927384)). Qed.
Lemma lem6927399 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6927400 : term343 = term108.
Proof. exact (@lem6927399 term123). Qed.
Lemma lem6927401 : term350 = term108.
Proof. exact (TRANS (@lem6927397) (@lem6927400)). Qed.
Lemma lem6927402 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6927403 : term352 = term353.
Proof. exact (MK_COMB (@lem6927402) (@lem6927401)). Qed.
Lemma lem6927404 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6927405 : term354 = term311.
Proof. exact (MK_COMB (@lem6927403) (@lem6927404)). Qed.
Lemma lem6927407 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927408 : term311 = term108.
Proof. exact (@lem6927407 term123). Qed.
Lemma lem6927409 : term354 = term108.
Proof. exact (TRANS (@lem6927405) (@lem6927408)). Qed.
Lemma lem6927411 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927412 : term166 = term167.
Proof. exact (@lem6927411 term123 term123). Qed.
Lemma lem6927413 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927414 : term169 = term123.
Proof. exact (EQ_MP (@lem6927413) (@lem940073)). Qed.
Lemma lem6927415 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927416 : term167 = term122.
Proof. exact (MK_COMB (@lem6927415) (@lem6927414)). Qed.
Lemma lem6927417 : term166 = term122.
Proof. exact (TRANS (@lem6927412) (@lem6927416)). Qed.
Lemma lem6927418 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6927419 : term355 = term311.
Proof. exact (MK_COMB (@lem6927418) (@lem6927417)). Qed.
Lemma lem6927421 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927422 : term311 = term108.
Proof. exact (@lem6927421 term123). Qed.
Lemma lem6927423 : term355 = term108.
Proof. exact (TRANS (@lem6927419) (@lem6927422)). Qed.
Lemma lem6927424 : term108 = term355.
Proof. exact (SYM (@lem6927423)). Qed.
Lemma lem6927425 : term354 = term355.
Proof. exact (TRANS (@lem6927409) (@lem6927424)). Qed.
Lemma lem6927426 : term344 = term154.
Proof. exact (@lem6927376 (@lem6927425)). Qed.
Lemma lem6927427 : term343 = term154.
Proof. exact (TRANS (@lem6927342) (@lem6927426)). Qed.
Lemma lem6927429 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6927430 : term154 = term108.
Proof. exact (@lem6927429 term108). Qed.
Lemma lem6927431 : term343 = term108.
Proof. exact (TRANS (@lem6927427) (@lem6927430)). Qed.
Lemma lem6927432 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6927433 : term356 = term353.
Proof. exact (MK_COMB (@lem6927432) (@lem6927431)). Qed.
Lemma lem6927434 (_92400 : int) : (real_of_int _92400) = (real_of_int _92400).
Proof. exact (eq_refl (real_of_int _92400)). Qed.
Lemma lem6927435 (_92400 : int) : (term340 _92400) = (term357 _92400).
Proof. exact (MK_COMB (@lem6927433) (@lem6927434 _92400)). Qed.
Lemma lem6927436 (_92400 : int) : (term339 _92400) = (term357 _92400).
Proof. exact (TRANS (@lem6927333 _92400) (@lem6927435 _92400)). Qed.
Lemma lem6927437 (_92400 : int) : (term357 _92400) = term108.
Proof. exact (@lem1982719 (real_of_int _92400)). Qed.
Lemma lem6927438 (_92400 : int) : (term339 _92400) = term108.
Proof. exact (TRANS (@lem6927436 _92400) (@lem6927437 _92400)). Qed.
Lemma lem6927439 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6927440 (_92400 : int) : (term358 _92400) = term359.
Proof. exact (MK_COMB (@lem6927439) (@lem6927438 _92400)). Qed.
Lemma lem6927441 (_92401 : int) : (term202 _92401) = (term202 _92401).
Proof. exact (eq_refl (term202 _92401)). Qed.
Lemma lem6927442 (_92400 : int) (_92401 : int) : (term406 _92400 _92401) = (term407 _92401).
Proof. exact (MK_COMB (@lem6927440 _92400) (@lem6927441 _92401)). Qed.
Lemma lem6927443 (_92400 : int) (_92401 : int) : (term405 _92400 _92401) = (term407 _92401).
Proof. exact (TRANS (@lem6927332 _92400 _92401) (@lem6927442 _92400 _92401)). Qed.
Lemma lem6927444 (_92401 : int) : (term407 _92401) = (term202 _92401).
Proof. exact (@lem1982721 (term202 _92401)). Qed.
Lemma lem6927445 (_92400 : int) (_92401 : int) : (term405 _92400 _92401) = (term202 _92401).
Proof. exact (TRANS (@lem6927443 _92400 _92401) (@lem6927444 _92401)). Qed.
Lemma lem6927446 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6927447 (_92400 : int) (_92401 : int) : (term408 _92400 _92401) = (term409 _92401).
Proof. exact (MK_COMB (@lem6927446) (@lem6927445 _92400 _92401)). Qed.
Lemma lem6927448 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6927449 (_92400 : int) (_92401 : int) : (term404 _92400 _92401) = (term410 _92401).
Proof. exact (MK_COMB (@lem6927447 _92400 _92401) (@lem6927448)). Qed.
Lemma lem6927450 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term410 _92401.
Proof. exact (EQ_MP (@lem6927449 _92400 _92401) (@lem6927331 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927452 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6927453 : term299 = term300.
Proof. exact (@lem6927452 term108 term122). Qed.
Lemma lem6927455 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927456 : term122 = term192.
Proof. exact (@lem6927455 term123). Qed.
Lemma lem6927458 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927459 : term108 = term154.
Proof. exact (@lem6927458 (NUMERAL 0)). Qed.
Lemma lem6927460 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6927461 : term301 = term302.
Proof. exact (MK_COMB (@lem6927460) (@lem6927459)). Qed.
Lemma lem6927462 : term300 = term303.
Proof. exact (MK_COMB (@lem6927461) (@lem6927456)). Qed.
Lemma lem6927463 : term304.
Proof. exact (@lem1980255 term108 term122 term122 term122). Qed.
Lemma lem6927465 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927466 : term300 = term306.
Proof. exact (@lem6927465 (NUMERAL 0) term123). Qed.
Lemma lem6927467 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927468 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927469 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927468 h1) (fun h1 : term306 = True => @lem6927467)). Qed.
Lemma lem6927470 : term306 = True.
Proof. exact (EQ_MP (@lem6927469) (@lem6927467)). Qed.
Lemma lem6927471 : term300 = True.
Proof. exact (TRANS (@lem6927466) (@lem6927470)). Qed.
Lemma lem6927472 : True = term300.
Proof. exact (SYM (@lem6927471)). Qed.
Lemma lem6927473 : term300.
Proof. exact (EQ_MP (@lem6927472) (@lem0)). Qed.
Lemma lem6927474 : term308.
Proof. exact (@lem6927463 (@lem6927473)). Qed.
Lemma lem6927476 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927477 : term300 = term306.
Proof. exact (@lem6927476 (NUMERAL 0) term123). Qed.
Lemma lem6927478 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927479 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927480 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927479 h1) (fun h1 : term306 = True => @lem6927478)). Qed.
Lemma lem6927481 : term306 = True.
Proof. exact (EQ_MP (@lem6927480) (@lem6927478)). Qed.
Lemma lem6927482 : term300 = True.
Proof. exact (TRANS (@lem6927477) (@lem6927481)). Qed.
Lemma lem6927483 : True = term300.
Proof. exact (SYM (@lem6927482)). Qed.
Lemma lem6927484 : term300.
Proof. exact (EQ_MP (@lem6927483) (@lem0)). Qed.
Lemma lem6927485 : term303 = term309.
Proof. exact (@lem6927474 (@lem6927484)). Qed.
Lemma lem6927487 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927488 : term166 = term167.
Proof. exact (@lem6927487 term123 term123). Qed.
Lemma lem6927489 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927490 : term169 = term123.
Proof. exact (EQ_MP (@lem6927489) (@lem940073)). Qed.
Lemma lem6927491 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927492 : term167 = term122.
Proof. exact (MK_COMB (@lem6927491) (@lem6927490)). Qed.
Lemma lem6927493 : term166 = term122.
Proof. exact (TRANS (@lem6927488) (@lem6927492)). Qed.
Lemma lem6927495 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927496 : term311 = term108.
Proof. exact (@lem6927495 term123). Qed.
Lemma lem6927497 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6927498 : term312 = term301.
Proof. exact (MK_COMB (@lem6927497) (@lem6927496)). Qed.
Lemma lem6927499 : term309 = term300.
Proof. exact (MK_COMB (@lem6927498) (@lem6927493)). Qed.
Lemma lem6927501 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927502 : term300 = term306.
Proof. exact (@lem6927501 (NUMERAL 0) term123). Qed.
Lemma lem6927503 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927504 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927505 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927504 h1) (fun h1 : term306 = True => @lem6927503)). Qed.
Lemma lem6927506 : term306 = True.
Proof. exact (EQ_MP (@lem6927505) (@lem6927503)). Qed.
Lemma lem6927507 : term300 = True.
Proof. exact (TRANS (@lem6927502) (@lem6927506)). Qed.
Lemma lem6927508 : term309 = True.
Proof. exact (TRANS (@lem6927499) (@lem6927507)). Qed.
Lemma lem6927509 : term303 = True.
Proof. exact (TRANS (@lem6927485) (@lem6927508)). Qed.
Lemma lem6927510 : term300 = True.
Proof. exact (TRANS (@lem6927462) (@lem6927509)). Qed.
Lemma lem6927511 : term299 = True.
Proof. exact (TRANS (@lem6927453) (@lem6927510)). Qed.
Lemma lem6927512 : True = term299.
Proof. exact (SYM (@lem6927511)). Qed.
Lemma lem6927513 : term299.
Proof. exact (EQ_MP (@lem6927512) (@lem0)). Qed.
Lemma lem6927514 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term411 _92401.
Proof. exact (conj (@lem6927513) (@lem6927450 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927516 (x : real) (y : real) : term314 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6927517 (_92401 : int) : term412 _92401.
Proof. exact (@lem6927516 term122 (term202 _92401)). Qed.
Lemma lem6927518 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term413 _92401.
Proof. exact (@lem6927517 _92401 (@lem6927514 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927519 (_92401 : int) : (term414 _92401) = (term202 _92401).
Proof. exact (@lem1982733 (term202 _92401)). Qed.
Lemma lem6927520 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6927521 (_92401 : int) : (term415 _92401) = (term409 _92401).
Proof. exact (MK_COMB (@lem6927520) (@lem6927519 _92401)). Qed.
Lemma lem6927522 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6927523 (_92401 : int) : (term413 _92401) = (term410 _92401).
Proof. exact (MK_COMB (@lem6927521 _92401) (@lem6927522)). Qed.
Lemma lem6927524 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term410 _92401.
Proof. exact (EQ_MP (@lem6927523 _92401) (@lem6927518 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927525 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term416 _92401.
Proof. exact (conj (@lem6927524 _92402 _92403 _92400 _92401 h1) (@lem6927239 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927527 (x : real) (y : real) : term417 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6927528 (_92401 : int) : term418 _92401.
Proof. exact (@lem6927527 (term202 _92401) (real_of_int _92401)). Qed.
Lemma lem6927529 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term419 _92401.
Proof. exact (@lem6927528 _92401 (@lem6927525 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927530 (_92401 : int) : (term420 _92401) = (term421 _92401).
Proof. exact (@lem1982759 (term184 _92401) (real_of_int _92401) term157). Qed.
Lemma lem6927531 (_92401 : int) : (term339 _92401) = (term340 _92401).
Proof. exact (@lem1982713 term157 (real_of_int _92401)). Qed.
Lemma lem6927533 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927534 : term122 = term192.
Proof. exact (@lem6927533 term123). Qed.
Lemma lem6927536 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6927537 : term157 = term158.
Proof. exact (@lem6927536 term123). Qed.
Lemma lem6927538 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6927539 : term341 = term342.
Proof. exact (MK_COMB (@lem6927538) (@lem6927537)). Qed.
Lemma lem6927540 : term343 = term344.
Proof. exact (MK_COMB (@lem6927539) (@lem6927534)). Qed.
Lemma lem6927541 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6927543 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927544 : term300 = term306.
Proof. exact (@lem6927543 (NUMERAL 0) term123). Qed.
Lemma lem6927545 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927546 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927547 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927546 h1) (fun h1 : term306 = True => @lem6927545)). Qed.
Lemma lem6927548 : term306 = True.
Proof. exact (EQ_MP (@lem6927547) (@lem6927545)). Qed.
Lemma lem6927549 : term300 = True.
Proof. exact (TRANS (@lem6927544) (@lem6927548)). Qed.
Lemma lem6927550 : True = term300.
Proof. exact (SYM (@lem6927549)). Qed.
Lemma lem6927551 : term300.
Proof. exact (EQ_MP (@lem6927550) (@lem0)). Qed.
Lemma lem6927552 : term346.
Proof. exact (@lem6927541 (@lem6927551)). Qed.
Lemma lem6927554 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927555 : term300 = term306.
Proof. exact (@lem6927554 (NUMERAL 0) term123). Qed.
Lemma lem6927556 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927557 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927558 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927557 h1) (fun h1 : term306 = True => @lem6927556)). Qed.
Lemma lem6927559 : term306 = True.
Proof. exact (EQ_MP (@lem6927558) (@lem6927556)). Qed.
Lemma lem6927560 : term300 = True.
Proof. exact (TRANS (@lem6927555) (@lem6927559)). Qed.
Lemma lem6927561 : True = term300.
Proof. exact (SYM (@lem6927560)). Qed.
Lemma lem6927562 : term300.
Proof. exact (EQ_MP (@lem6927561) (@lem0)). Qed.
Lemma lem6927563 : term347.
Proof. exact (@lem6927552 (@lem6927562)). Qed.
Lemma lem6927565 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927566 : term300 = term306.
Proof. exact (@lem6927565 (NUMERAL 0) term123). Qed.
Lemma lem6927567 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927568 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927569 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927568 h1) (fun h1 : term306 = True => @lem6927567)). Qed.
Lemma lem6927570 : term306 = True.
Proof. exact (EQ_MP (@lem6927569) (@lem6927567)). Qed.
Lemma lem6927571 : term300 = True.
Proof. exact (TRANS (@lem6927566) (@lem6927570)). Qed.
Lemma lem6927572 : True = term300.
Proof. exact (SYM (@lem6927571)). Qed.
Lemma lem6927573 : term300.
Proof. exact (EQ_MP (@lem6927572) (@lem0)). Qed.
Lemma lem6927574 : term348.
Proof. exact (@lem6927563 (@lem6927573)). Qed.
Lemma lem6927576 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927577 : term166 = term167.
Proof. exact (@lem6927576 term123 term123). Qed.
Lemma lem6927578 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927579 : term169 = term123.
Proof. exact (EQ_MP (@lem6927578) (@lem940073)). Qed.
Lemma lem6927580 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927581 : term167 = term122.
Proof. exact (MK_COMB (@lem6927580) (@lem6927579)). Qed.
Lemma lem6927582 : term166 = term122.
Proof. exact (TRANS (@lem6927577) (@lem6927581)). Qed.
Lemma lem6927584 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6927585 : term193 = term198.
Proof. exact (@lem6927584 term123 term123). Qed.
Lemma lem6927586 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927587 : term169 = term123.
Proof. exact (EQ_MP (@lem6927586) (@lem940073)). Qed.
Lemma lem6927588 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927589 : term167 = term122.
Proof. exact (MK_COMB (@lem6927588) (@lem6927587)). Qed.
Lemma lem6927590 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6927591 : term198 = term157.
Proof. exact (MK_COMB (@lem6927590) (@lem6927589)). Qed.
Lemma lem6927592 : term193 = term157.
Proof. exact (TRANS (@lem6927585) (@lem6927591)). Qed.
Lemma lem6927593 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6927594 : term349 = term341.
Proof. exact (MK_COMB (@lem6927593) (@lem6927592)). Qed.
Lemma lem6927595 : term350 = term343.
Proof. exact (MK_COMB (@lem6927594) (@lem6927582)). Qed.
Lemma lem6927597 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6927598 : term343 = term108.
Proof. exact (@lem6927597 term123). Qed.
Lemma lem6927599 : term350 = term108.
Proof. exact (TRANS (@lem6927595) (@lem6927598)). Qed.
Lemma lem6927600 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6927601 : term352 = term353.
Proof. exact (MK_COMB (@lem6927600) (@lem6927599)). Qed.
Lemma lem6927602 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6927603 : term354 = term311.
Proof. exact (MK_COMB (@lem6927601) (@lem6927602)). Qed.
Lemma lem6927605 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927606 : term311 = term108.
Proof. exact (@lem6927605 term123). Qed.
Lemma lem6927607 : term354 = term108.
Proof. exact (TRANS (@lem6927603) (@lem6927606)). Qed.
Lemma lem6927609 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927610 : term166 = term167.
Proof. exact (@lem6927609 term123 term123). Qed.
Lemma lem6927611 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927612 : term169 = term123.
Proof. exact (EQ_MP (@lem6927611) (@lem940073)). Qed.
Lemma lem6927613 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927614 : term167 = term122.
Proof. exact (MK_COMB (@lem6927613) (@lem6927612)). Qed.
Lemma lem6927615 : term166 = term122.
Proof. exact (TRANS (@lem6927610) (@lem6927614)). Qed.
Lemma lem6927616 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6927617 : term355 = term311.
Proof. exact (MK_COMB (@lem6927616) (@lem6927615)). Qed.
Lemma lem6927619 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927620 : term311 = term108.
Proof. exact (@lem6927619 term123). Qed.
Lemma lem6927621 : term355 = term108.
Proof. exact (TRANS (@lem6927617) (@lem6927620)). Qed.
Lemma lem6927622 : term108 = term355.
Proof. exact (SYM (@lem6927621)). Qed.
Lemma lem6927623 : term354 = term355.
Proof. exact (TRANS (@lem6927607) (@lem6927622)). Qed.
Lemma lem6927624 : term344 = term154.
Proof. exact (@lem6927574 (@lem6927623)). Qed.
Lemma lem6927625 : term343 = term154.
Proof. exact (TRANS (@lem6927540) (@lem6927624)). Qed.
Lemma lem6927627 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6927628 : term154 = term108.
Proof. exact (@lem6927627 term108). Qed.
Lemma lem6927629 : term343 = term108.
Proof. exact (TRANS (@lem6927625) (@lem6927628)). Qed.
Lemma lem6927630 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6927631 : term356 = term353.
Proof. exact (MK_COMB (@lem6927630) (@lem6927629)). Qed.
Lemma lem6927632 (_92401 : int) : (real_of_int _92401) = (real_of_int _92401).
Proof. exact (eq_refl (real_of_int _92401)). Qed.
Lemma lem6927633 (_92401 : int) : (term340 _92401) = (term357 _92401).
Proof. exact (MK_COMB (@lem6927631) (@lem6927632 _92401)). Qed.
Lemma lem6927634 (_92401 : int) : (term339 _92401) = (term357 _92401).
Proof. exact (TRANS (@lem6927531 _92401) (@lem6927633 _92401)). Qed.
Lemma lem6927635 (_92401 : int) : (term357 _92401) = term108.
Proof. exact (@lem1982719 (real_of_int _92401)). Qed.
Lemma lem6927636 (_92401 : int) : (term339 _92401) = term108.
Proof. exact (TRANS (@lem6927634 _92401) (@lem6927635 _92401)). Qed.
Lemma lem6927637 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6927638 (_92401 : int) : (term358 _92401) = term359.
Proof. exact (MK_COMB (@lem6927637) (@lem6927636 _92401)). Qed.
Lemma lem6927639 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem6927640 (_92401 : int) : (term421 _92401) = term378.
Proof. exact (MK_COMB (@lem6927638 _92401) (@lem6927639)). Qed.
Lemma lem6927641 (_92401 : int) : (term420 _92401) = term378.
Proof. exact (TRANS (@lem6927530 _92401) (@lem6927640 _92401)). Qed.
Lemma lem6927642 : term378 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem6927643 (_92401 : int) : (term420 _92401) = term157.
Proof. exact (TRANS (@lem6927641 _92401) (@lem6927642)). Qed.
Lemma lem6927644 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6927645 (_92401 : int) : (term422 _92401) = term380.
Proof. exact (MK_COMB (@lem6927644) (@lem6927643 _92401)). Qed.
Lemma lem6927646 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6927647 (_92401 : int) : (term419 _92401) = term381.
Proof. exact (MK_COMB (@lem6927645 _92401) (@lem6927646)). Qed.
Lemma lem6927648 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : term381.
Proof. exact (EQ_MP (@lem6927647 _92401) (@lem6927529 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927650 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6927651 : term381 = term382.
Proof. exact (@lem6927650 term108 term157). Qed.
Lemma lem6927653 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6927654 : term157 = term158.
Proof. exact (@lem6927653 term123). Qed.
Lemma lem6927656 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927657 : term108 = term154.
Proof. exact (@lem6927656 (NUMERAL 0)). Qed.
Lemma lem6927658 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6927659 : term110 = term383.
Proof. exact (MK_COMB (@lem6927658) (@lem6927657)). Qed.
Lemma lem6927660 : term382 = term384.
Proof. exact (MK_COMB (@lem6927659) (@lem6927654)). Qed.
Lemma lem6927661 : term385.
Proof. exact (@lem1980026 term108 term122 term157 term122). Qed.
Lemma lem6927663 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927664 : term300 = term306.
Proof. exact (@lem6927663 (NUMERAL 0) term123). Qed.
Lemma lem6927665 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927666 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927667 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927666 h1) (fun h1 : term306 = True => @lem6927665)). Qed.
Lemma lem6927668 : term306 = True.
Proof. exact (EQ_MP (@lem6927667) (@lem6927665)). Qed.
Lemma lem6927669 : term300 = True.
Proof. exact (TRANS (@lem6927664) (@lem6927668)). Qed.
Lemma lem6927670 : True = term300.
Proof. exact (SYM (@lem6927669)). Qed.
Lemma lem6927671 : term300.
Proof. exact (EQ_MP (@lem6927670) (@lem0)). Qed.
Lemma lem6927672 : term386.
Proof. exact (@lem6927661 (@lem6927671)). Qed.
Lemma lem6927674 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927675 : term300 = term306.
Proof. exact (@lem6927674 (NUMERAL 0) term123). Qed.
Lemma lem6927676 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927677 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927678 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927677 h1) (fun h1 : term306 = True => @lem6927676)). Qed.
Lemma lem6927679 : term306 = True.
Proof. exact (EQ_MP (@lem6927678) (@lem6927676)). Qed.
Lemma lem6927680 : term300 = True.
Proof. exact (TRANS (@lem6927675) (@lem6927679)). Qed.
Lemma lem6927681 : True = term300.
Proof. exact (SYM (@lem6927680)). Qed.
Lemma lem6927682 : term300.
Proof. exact (EQ_MP (@lem6927681) (@lem0)). Qed.
Lemma lem6927683 : term384 = term387.
Proof. exact (@lem6927672 (@lem6927682)). Qed.
Lemma lem6927685 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6927686 : term193 = term198.
Proof. exact (@lem6927685 term123 term123). Qed.
Lemma lem6927687 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927688 : term169 = term123.
Proof. exact (EQ_MP (@lem6927687) (@lem940073)). Qed.
Lemma lem6927689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927690 : term167 = term122.
Proof. exact (MK_COMB (@lem6927689) (@lem6927688)). Qed.
Lemma lem6927691 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6927692 : term198 = term157.
Proof. exact (MK_COMB (@lem6927691) (@lem6927690)). Qed.
Lemma lem6927693 : term193 = term157.
Proof. exact (TRANS (@lem6927686) (@lem6927692)). Qed.
Lemma lem6927695 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927696 : term311 = term108.
Proof. exact (@lem6927695 term123). Qed.
Lemma lem6927697 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6927698 : term388 = term110.
Proof. exact (MK_COMB (@lem6927697) (@lem6927696)). Qed.
Lemma lem6927699 : term387 = term382.
Proof. exact (MK_COMB (@lem6927698) (@lem6927693)). Qed.
Lemma lem6927701 (m : nat) (n : nat) : (term389 m n) = (term390 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6927702 : term382 = term391.
Proof. exact (@lem6927701 (NUMERAL 0) term123). Qed.
Lemma lem6927703 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927704 (h1 : term307 = (BIT1 0)) : (term123 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6927705 : (term307 = (BIT1 0)) = ((term123 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927704 h1) (fun h1 : (term123 = (NUMERAL 0)) = False => @lem6927703)). Qed.
Lemma lem6927706 : (term123 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6927705) (@lem6927703)). Qed.
Lemma lem6927707 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6927708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6927709 : term392 = (and True).
Proof. exact (MK_COMB (@lem6927708) (@lem6927707)). Qed.
Lemma lem6927710 : term391 = (True /\ False).
Proof. exact (MK_COMB (@lem6927709) (@lem6927706)). Qed.
Lemma lem6927712 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6927713 : term391 = False.
Proof. exact (TRANS (@lem6927710) (@lem6927712)). Qed.
Lemma lem6927714 : term382 = False.
Proof. exact (TRANS (@lem6927702) (@lem6927713)). Qed.
Lemma lem6927715 : term387 = False.
Proof. exact (TRANS (@lem6927699) (@lem6927714)). Qed.
Lemma lem6927716 : term384 = False.
Proof. exact (TRANS (@lem6927683) (@lem6927715)). Qed.
Lemma lem6927717 : term382 = False.
Proof. exact (TRANS (@lem6927660) (@lem6927716)). Qed.
Lemma lem6927718 : term381 = False.
Proof. exact (TRANS (@lem6927651) (@lem6927717)). Qed.
Lemma lem6927719 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term393 _92402 _92403 _92400 _92401) : False.
Proof. exact (EQ_MP (@lem6927718) (@lem6927648 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927720 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term292 _92402 _92403 _92400 _92401) : False.
Proof. exact (or_elim (@lem6926416 _92402 _92403 _92400 _92401 h1) (fun h0 : term298 _92402 _92403 _92400 _92401 => @lem6927150 _92402 _92403 _92400 _92401 h0) (fun h0 : term393 _92402 _92403 _92400 _92401 => @lem6927719 _92402 _92403 _92400 _92401 h0)). Qed.
Lemma lem6927721 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term288 _92402 _92403 _92400 _92401) : term288 _92402 _92403 _92400 _92401.
Proof. exact (h1). Qed.
Lemma lem6927722 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term423 _92402 _92403 _92400 _92401.
Proof. exact (h1). Qed.
Lemma lem6927723 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term289 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6927722 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927725 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term276 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6927723 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927727 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term263 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6927725 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927729 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term250 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6927727 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927731 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term238 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6927729 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927732 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : (term183 _92400 _92402 _92403) = term108.
Proof. exact (proj1 (@lem6927729 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927733 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term207 _92400 _92401.
Proof. exact (proj2 (@lem6927731 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927734 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : (term218 _92401 _92402 _92403) = term108.
Proof. exact (proj1 (@lem6927731 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927736 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6927737 : term299 = term300.
Proof. exact (@lem6927736 term108 term122). Qed.
Lemma lem6927739 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927740 : term122 = term192.
Proof. exact (@lem6927739 term123). Qed.
Lemma lem6927742 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927743 : term108 = term154.
Proof. exact (@lem6927742 (NUMERAL 0)). Qed.
Lemma lem6927744 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6927745 : term301 = term302.
Proof. exact (MK_COMB (@lem6927744) (@lem6927743)). Qed.
Lemma lem6927746 : term300 = term303.
Proof. exact (MK_COMB (@lem6927745) (@lem6927740)). Qed.
Lemma lem6927747 : term304.
Proof. exact (@lem1980255 term108 term122 term122 term122). Qed.
Lemma lem6927749 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927750 : term300 = term306.
Proof. exact (@lem6927749 (NUMERAL 0) term123). Qed.
Lemma lem6927751 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927752 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927753 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927752 h1) (fun h1 : term306 = True => @lem6927751)). Qed.
Lemma lem6927754 : term306 = True.
Proof. exact (EQ_MP (@lem6927753) (@lem6927751)). Qed.
Lemma lem6927755 : term300 = True.
Proof. exact (TRANS (@lem6927750) (@lem6927754)). Qed.
Lemma lem6927756 : True = term300.
Proof. exact (SYM (@lem6927755)). Qed.
Lemma lem6927757 : term300.
Proof. exact (EQ_MP (@lem6927756) (@lem0)). Qed.
Lemma lem6927758 : term308.
Proof. exact (@lem6927747 (@lem6927757)). Qed.
Lemma lem6927760 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927761 : term300 = term306.
Proof. exact (@lem6927760 (NUMERAL 0) term123). Qed.
Lemma lem6927762 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927763 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927764 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927763 h1) (fun h1 : term306 = True => @lem6927762)). Qed.
Lemma lem6927765 : term306 = True.
Proof. exact (EQ_MP (@lem6927764) (@lem6927762)). Qed.
Lemma lem6927766 : term300 = True.
Proof. exact (TRANS (@lem6927761) (@lem6927765)). Qed.
Lemma lem6927767 : True = term300.
Proof. exact (SYM (@lem6927766)). Qed.
Lemma lem6927768 : term300.
Proof. exact (EQ_MP (@lem6927767) (@lem0)). Qed.
Lemma lem6927769 : term303 = term309.
Proof. exact (@lem6927758 (@lem6927768)). Qed.
Lemma lem6927771 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927772 : term166 = term167.
Proof. exact (@lem6927771 term123 term123). Qed.
Lemma lem6927773 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927774 : term169 = term123.
Proof. exact (EQ_MP (@lem6927773) (@lem940073)). Qed.
Lemma lem6927775 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927776 : term167 = term122.
Proof. exact (MK_COMB (@lem6927775) (@lem6927774)). Qed.
Lemma lem6927777 : term166 = term122.
Proof. exact (TRANS (@lem6927772) (@lem6927776)). Qed.
Lemma lem6927779 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927780 : term311 = term108.
Proof. exact (@lem6927779 term123). Qed.
Lemma lem6927781 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6927782 : term312 = term301.
Proof. exact (MK_COMB (@lem6927781) (@lem6927780)). Qed.
Lemma lem6927783 : term309 = term300.
Proof. exact (MK_COMB (@lem6927782) (@lem6927777)). Qed.
Lemma lem6927785 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927786 : term300 = term306.
Proof. exact (@lem6927785 (NUMERAL 0) term123). Qed.
Lemma lem6927787 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927788 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927789 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927788 h1) (fun h1 : term306 = True => @lem6927787)). Qed.
Lemma lem6927790 : term306 = True.
Proof. exact (EQ_MP (@lem6927789) (@lem6927787)). Qed.
Lemma lem6927791 : term300 = True.
Proof. exact (TRANS (@lem6927786) (@lem6927790)). Qed.
Lemma lem6927792 : term309 = True.
Proof. exact (TRANS (@lem6927783) (@lem6927791)). Qed.
Lemma lem6927793 : term303 = True.
Proof. exact (TRANS (@lem6927769) (@lem6927792)). Qed.
Lemma lem6927794 : term300 = True.
Proof. exact (TRANS (@lem6927746) (@lem6927793)). Qed.
Lemma lem6927795 : term299 = True.
Proof. exact (TRANS (@lem6927737) (@lem6927794)). Qed.
Lemma lem6927796 : True = term299.
Proof. exact (SYM (@lem6927795)). Qed.
Lemma lem6927797 : term299.
Proof. exact (EQ_MP (@lem6927796) (@lem0)). Qed.
Lemma lem6927798 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term424 _92400 _92401.
Proof. exact (conj (@lem6927797) (@lem6927733 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927800 (x : real) (y : real) : term314 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6927801 (_92400 : int) (_92401 : int) : term425 _92400 _92401.
Proof. exact (@lem6927800 term122 (term204 _92400 _92401)). Qed.
Lemma lem6927802 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term426 _92400 _92401.
Proof. exact (@lem6927801 _92400 _92401 (@lem6927798 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927803 (_92400 : int) (_92401 : int) : (term427 _92400 _92401) = (term204 _92400 _92401).
Proof. exact (@lem1982733 (term204 _92400 _92401)). Qed.
Lemma lem6927804 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6927805 (_92400 : int) (_92401 : int) : (term428 _92400 _92401) = (term206 _92400 _92401).
Proof. exact (MK_COMB (@lem6927804) (@lem6927803 _92400 _92401)). Qed.
Lemma lem6927806 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6927807 (_92400 : int) (_92401 : int) : (term426 _92400 _92401) = (term207 _92400 _92401).
Proof. exact (MK_COMB (@lem6927805 _92400 _92401) (@lem6927806)). Qed.
Lemma lem6927808 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term207 _92400 _92401.
Proof. exact (EQ_MP (@lem6927807 _92400 _92401) (@lem6927802 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927810 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6927811 : term299 = term300.
Proof. exact (@lem6927810 term108 term122). Qed.
Lemma lem6927813 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927814 : term122 = term192.
Proof. exact (@lem6927813 term123). Qed.
Lemma lem6927816 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927817 : term108 = term154.
Proof. exact (@lem6927816 (NUMERAL 0)). Qed.
Lemma lem6927818 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6927819 : term301 = term302.
Proof. exact (MK_COMB (@lem6927818) (@lem6927817)). Qed.
Lemma lem6927820 : term300 = term303.
Proof. exact (MK_COMB (@lem6927819) (@lem6927814)). Qed.
Lemma lem6927821 : term304.
Proof. exact (@lem1980255 term108 term122 term122 term122). Qed.
Lemma lem6927823 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927824 : term300 = term306.
Proof. exact (@lem6927823 (NUMERAL 0) term123). Qed.
Lemma lem6927825 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927826 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927827 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927826 h1) (fun h1 : term306 = True => @lem6927825)). Qed.
Lemma lem6927828 : term306 = True.
Proof. exact (EQ_MP (@lem6927827) (@lem6927825)). Qed.
Lemma lem6927829 : term300 = True.
Proof. exact (TRANS (@lem6927824) (@lem6927828)). Qed.
Lemma lem6927830 : True = term300.
Proof. exact (SYM (@lem6927829)). Qed.
Lemma lem6927831 : term300.
Proof. exact (EQ_MP (@lem6927830) (@lem0)). Qed.
Lemma lem6927832 : term308.
Proof. exact (@lem6927821 (@lem6927831)). Qed.
Lemma lem6927834 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927835 : term300 = term306.
Proof. exact (@lem6927834 (NUMERAL 0) term123). Qed.
Lemma lem6927836 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927837 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927838 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927837 h1) (fun h1 : term306 = True => @lem6927836)). Qed.
Lemma lem6927839 : term306 = True.
Proof. exact (EQ_MP (@lem6927838) (@lem6927836)). Qed.
Lemma lem6927840 : term300 = True.
Proof. exact (TRANS (@lem6927835) (@lem6927839)). Qed.
Lemma lem6927841 : True = term300.
Proof. exact (SYM (@lem6927840)). Qed.
Lemma lem6927842 : term300.
Proof. exact (EQ_MP (@lem6927841) (@lem0)). Qed.
Lemma lem6927843 : term303 = term309.
Proof. exact (@lem6927832 (@lem6927842)). Qed.
Lemma lem6927845 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927846 : term166 = term167.
Proof. exact (@lem6927845 term123 term123). Qed.
Lemma lem6927847 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927848 : term169 = term123.
Proof. exact (EQ_MP (@lem6927847) (@lem940073)). Qed.
Lemma lem6927849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927850 : term167 = term122.
Proof. exact (MK_COMB (@lem6927849) (@lem6927848)). Qed.
Lemma lem6927851 : term166 = term122.
Proof. exact (TRANS (@lem6927846) (@lem6927850)). Qed.
Lemma lem6927853 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927854 : term311 = term108.
Proof. exact (@lem6927853 term123). Qed.
Lemma lem6927855 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6927856 : term312 = term301.
Proof. exact (MK_COMB (@lem6927855) (@lem6927854)). Qed.
Lemma lem6927857 : term309 = term300.
Proof. exact (MK_COMB (@lem6927856) (@lem6927851)). Qed.
Lemma lem6927859 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927860 : term300 = term306.
Proof. exact (@lem6927859 (NUMERAL 0) term123). Qed.
Lemma lem6927861 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927862 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927863 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927862 h1) (fun h1 : term306 = True => @lem6927861)). Qed.
Lemma lem6927864 : term306 = True.
Proof. exact (EQ_MP (@lem6927863) (@lem6927861)). Qed.
Lemma lem6927865 : term300 = True.
Proof. exact (TRANS (@lem6927860) (@lem6927864)). Qed.
Lemma lem6927866 : term309 = True.
Proof. exact (TRANS (@lem6927857) (@lem6927865)). Qed.
Lemma lem6927867 : term303 = True.
Proof. exact (TRANS (@lem6927843) (@lem6927866)). Qed.
Lemma lem6927868 : term300 = True.
Proof. exact (TRANS (@lem6927820) (@lem6927867)). Qed.
Lemma lem6927869 : term299 = True.
Proof. exact (TRANS (@lem6927811) (@lem6927868)). Qed.
Lemma lem6927870 : True = term299.
Proof. exact (SYM (@lem6927869)). Qed.
Lemma lem6927871 : term299.
Proof. exact (EQ_MP (@lem6927870) (@lem0)). Qed.
Lemma lem6927872 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term319 _92400 _92402 _92403.
Proof. exact (conj (@lem6927871) (@lem6927732 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927874 (x : real) (y : real) : term320 x y.
Proof. exact (proj1 (@lem1988330 x y)). Qed.
Lemma lem6927875 (_92400 : int) (_92402 : int) (_92403 : int) : term321 _92400 _92402 _92403.
Proof. exact (@lem6927874 term122 (term183 _92400 _92402 _92403)). Qed.
Lemma lem6927876 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : (term322 _92400 _92402 _92403) = term108.
Proof. exact (@lem6927875 _92400 _92402 _92403 (@lem6927872 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927877 (_92400 : int) (_92402 : int) (_92403 : int) : (term322 _92400 _92402 _92403) = (term183 _92400 _92402 _92403).
Proof. exact (@lem1982733 (term183 _92400 _92402 _92403)). Qed.
Lemma lem6927878 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6927879 (_92400 : int) (_92402 : int) (_92403 : int) : (term323 _92400 _92402 _92403) = (term186 _92400 _92402 _92403).
Proof. exact (MK_COMB (@lem6927878) (@lem6927877 _92400 _92402 _92403)). Qed.
Lemma lem6927880 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6927881 (_92400 : int) (_92402 : int) (_92403 : int) : ((term322 _92400 _92402 _92403) = term108) = ((term183 _92400 _92402 _92403) = term108).
Proof. exact (MK_COMB (@lem6927879 _92400 _92402 _92403) (@lem6927880)). Qed.
Lemma lem6927882 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : (term183 _92400 _92402 _92403) = term108.
Proof. exact (EQ_MP (@lem6927881 _92400 _92402 _92403) (@lem6927876 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927884 (y : real) : term324 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6927885 (_92401 : int) (_92402 : int) (_92403 : int) : term325 _92401 _92402 _92403.
Proof. exact (@lem6927884 (term218 _92401 _92402 _92403)). Qed.
Lemma lem6927886 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term326 _92401 _92402 _92403.
Proof. exact (@lem6927885 _92401 _92402 _92403 (@lem6927734 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927887 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term327 _92401 _92402 _92403.
Proof. exact (@lem6927886 _92402 _92403 _92400 _92401 h1 term122). Qed.
Lemma lem6927888 (_92401 : int) (_92402 : int) (_92403 : int) : (term327 _92401 _92402 _92403) = ((term328 _92401 _92402 _92403) = term108).
Proof. exact (eq_refl (term327 _92401 _92402 _92403)). Qed.
Lemma lem6927889 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : (term328 _92401 _92402 _92403) = term108.
Proof. exact (EQ_MP (@lem6927888 _92401 _92402 _92403) (@lem6927887 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927890 (_92401 : int) (_92402 : int) (_92403 : int) : (term328 _92401 _92402 _92403) = (term218 _92401 _92402 _92403).
Proof. exact (@lem1982733 (term218 _92401 _92402 _92403)). Qed.
Lemma lem6927891 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6927892 (_92401 : int) (_92402 : int) (_92403 : int) : (term329 _92401 _92402 _92403) = (term220 _92401 _92402 _92403).
Proof. exact (MK_COMB (@lem6927891) (@lem6927890 _92401 _92402 _92403)). Qed.
Lemma lem6927893 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6927894 (_92401 : int) (_92402 : int) (_92403 : int) : ((term328 _92401 _92402 _92403) = term108) = ((term218 _92401 _92402 _92403) = term108).
Proof. exact (MK_COMB (@lem6927892 _92401 _92402 _92403) (@lem6927893)). Qed.
Lemma lem6927895 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : (term218 _92401 _92402 _92403) = term108.
Proof. exact (EQ_MP (@lem6927894 _92401 _92402 _92403) (@lem6927889 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927896 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term330 _92401 _92400 _92402 _92403.
Proof. exact (conj (@lem6927895 _92402 _92403 _92400 _92401 h1) (@lem6927882 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927898 (x : real) (y : real) : term331 x y.
Proof. exact (proj1 (@lem1393126 x y)). Qed.
Lemma lem6927899 (_92401 : int) (_92400 : int) (_92402 : int) (_92403 : int) : term332 _92401 _92400 _92402 _92403.
Proof. exact (@lem6927898 (term218 _92401 _92402 _92403) (term183 _92400 _92402 _92403)). Qed.
Lemma lem6927900 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : (term333 _92401 _92400 _92402 _92403) = term108.
Proof. exact (@lem6927899 _92401 _92400 _92402 _92403 (@lem6927896 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6927901 (_92400 : int) (_92401 : int) (_92402 : int) (_92403 : int) : (term333 _92401 _92400 _92402 _92403) = (term334 _92400 _92401 _92402 _92403).
Proof. exact (@lem1982757 (term184 _92400) (term218 _92401 _92402 _92403) (term216 _92402 _92403)). Qed.
Lemma lem6927902 (_92401 : int) (_92402 : int) (_92403 : int) : (term335 _92401 _92402 _92403) = (term336 _92401 _92402 _92403).
Proof. exact (@lem1982755 (real_of_int _92401) (term217 _92402 _92403) (term216 _92402 _92403)). Qed.
Lemma lem6927903 (_92402 : int) (_92403 : int) : (term337 _92402 _92403) = (term338 _92402 _92403).
Proof. exact (@lem1982753 (term184 _92402) (real_of_int _92402) (real_of_int _92403) (term184 _92403)). Qed.
Lemma lem6927904 (_92402 : int) : (term339 _92402) = (term340 _92402).
Proof. exact (@lem1982713 term157 (real_of_int _92402)). Qed.
Lemma lem6927906 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6927907 : term122 = term192.
Proof. exact (@lem6927906 term123). Qed.
Lemma lem6927909 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6927910 : term157 = term158.
Proof. exact (@lem6927909 term123). Qed.
Lemma lem6927911 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6927912 : term341 = term342.
Proof. exact (MK_COMB (@lem6927911) (@lem6927910)). Qed.
Lemma lem6927913 : term343 = term344.
Proof. exact (MK_COMB (@lem6927912) (@lem6927907)). Qed.
Lemma lem6927914 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6927916 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927917 : term300 = term306.
Proof. exact (@lem6927916 (NUMERAL 0) term123). Qed.
Lemma lem6927918 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927919 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927920 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927919 h1) (fun h1 : term306 = True => @lem6927918)). Qed.
Lemma lem6927921 : term306 = True.
Proof. exact (EQ_MP (@lem6927920) (@lem6927918)). Qed.
Lemma lem6927922 : term300 = True.
Proof. exact (TRANS (@lem6927917) (@lem6927921)). Qed.
Lemma lem6927923 : True = term300.
Proof. exact (SYM (@lem6927922)). Qed.
Lemma lem6927924 : term300.
Proof. exact (EQ_MP (@lem6927923) (@lem0)). Qed.
Lemma lem6927925 : term346.
Proof. exact (@lem6927914 (@lem6927924)). Qed.
Lemma lem6927927 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927928 : term300 = term306.
Proof. exact (@lem6927927 (NUMERAL 0) term123). Qed.
Lemma lem6927929 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927930 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927931 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927930 h1) (fun h1 : term306 = True => @lem6927929)). Qed.
Lemma lem6927932 : term306 = True.
Proof. exact (EQ_MP (@lem6927931) (@lem6927929)). Qed.
Lemma lem6927933 : term300 = True.
Proof. exact (TRANS (@lem6927928) (@lem6927932)). Qed.
Lemma lem6927934 : True = term300.
Proof. exact (SYM (@lem6927933)). Qed.
Lemma lem6927935 : term300.
Proof. exact (EQ_MP (@lem6927934) (@lem0)). Qed.
Lemma lem6927936 : term347.
Proof. exact (@lem6927925 (@lem6927935)). Qed.
Lemma lem6927938 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6927939 : term300 = term306.
Proof. exact (@lem6927938 (NUMERAL 0) term123). Qed.
Lemma lem6927940 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6927941 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6927942 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6927941 h1) (fun h1 : term306 = True => @lem6927940)). Qed.
Lemma lem6927943 : term306 = True.
Proof. exact (EQ_MP (@lem6927942) (@lem6927940)). Qed.
Lemma lem6927944 : term300 = True.
Proof. exact (TRANS (@lem6927939) (@lem6927943)). Qed.
Lemma lem6927945 : True = term300.
Proof. exact (SYM (@lem6927944)). Qed.
Lemma lem6927946 : term300.
Proof. exact (EQ_MP (@lem6927945) (@lem0)). Qed.
Lemma lem6927947 : term348.
Proof. exact (@lem6927936 (@lem6927946)). Qed.
Lemma lem6927949 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927950 : term166 = term167.
Proof. exact (@lem6927949 term123 term123). Qed.
Lemma lem6927951 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927952 : term169 = term123.
Proof. exact (EQ_MP (@lem6927951) (@lem940073)). Qed.
Lemma lem6927953 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927954 : term167 = term122.
Proof. exact (MK_COMB (@lem6927953) (@lem6927952)). Qed.
Lemma lem6927955 : term166 = term122.
Proof. exact (TRANS (@lem6927950) (@lem6927954)). Qed.
Lemma lem6927957 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6927958 : term193 = term198.
Proof. exact (@lem6927957 term123 term123). Qed.
Lemma lem6927959 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927960 : term169 = term123.
Proof. exact (EQ_MP (@lem6927959) (@lem940073)). Qed.
Lemma lem6927961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927962 : term167 = term122.
Proof. exact (MK_COMB (@lem6927961) (@lem6927960)). Qed.
Lemma lem6927963 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6927964 : term198 = term157.
Proof. exact (MK_COMB (@lem6927963) (@lem6927962)). Qed.
Lemma lem6927965 : term193 = term157.
Proof. exact (TRANS (@lem6927958) (@lem6927964)). Qed.
Lemma lem6927966 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6927967 : term349 = term341.
Proof. exact (MK_COMB (@lem6927966) (@lem6927965)). Qed.
Lemma lem6927968 : term350 = term343.
Proof. exact (MK_COMB (@lem6927967) (@lem6927955)). Qed.
Lemma lem6927970 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6927971 : term343 = term108.
Proof. exact (@lem6927970 term123). Qed.
Lemma lem6927972 : term350 = term108.
Proof. exact (TRANS (@lem6927968) (@lem6927971)). Qed.
Lemma lem6927973 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6927974 : term352 = term353.
Proof. exact (MK_COMB (@lem6927973) (@lem6927972)). Qed.
Lemma lem6927975 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6927976 : term354 = term311.
Proof. exact (MK_COMB (@lem6927974) (@lem6927975)). Qed.
Lemma lem6927978 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927979 : term311 = term108.
Proof. exact (@lem6927978 term123). Qed.
Lemma lem6927980 : term354 = term108.
Proof. exact (TRANS (@lem6927976) (@lem6927979)). Qed.
Lemma lem6927982 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6927983 : term166 = term167.
Proof. exact (@lem6927982 term123 term123). Qed.
Lemma lem6927984 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6927985 : term169 = term123.
Proof. exact (EQ_MP (@lem6927984) (@lem940073)). Qed.
Lemma lem6927986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6927987 : term167 = term122.
Proof. exact (MK_COMB (@lem6927986) (@lem6927985)). Qed.
Lemma lem6927988 : term166 = term122.
Proof. exact (TRANS (@lem6927983) (@lem6927987)). Qed.
Lemma lem6927989 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6927990 : term355 = term311.
Proof. exact (MK_COMB (@lem6927989) (@lem6927988)). Qed.
Lemma lem6927992 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6927993 : term311 = term108.
Proof. exact (@lem6927992 term123). Qed.
Lemma lem6927994 : term355 = term108.
Proof. exact (TRANS (@lem6927990) (@lem6927993)). Qed.
Lemma lem6927995 : term108 = term355.
Proof. exact (SYM (@lem6927994)). Qed.
Lemma lem6927996 : term354 = term355.
Proof. exact (TRANS (@lem6927980) (@lem6927995)). Qed.
Lemma lem6927997 : term344 = term154.
Proof. exact (@lem6927947 (@lem6927996)). Qed.
Lemma lem6927998 : term343 = term154.
Proof. exact (TRANS (@lem6927913) (@lem6927997)). Qed.
Lemma lem6928000 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6928001 : term154 = term108.
Proof. exact (@lem6928000 term108). Qed.
Lemma lem6928002 : term343 = term108.
Proof. exact (TRANS (@lem6927998) (@lem6928001)). Qed.
Lemma lem6928003 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928004 : term356 = term353.
Proof. exact (MK_COMB (@lem6928003) (@lem6928002)). Qed.
Lemma lem6928005 (_92402 : int) : (real_of_int _92402) = (real_of_int _92402).
Proof. exact (eq_refl (real_of_int _92402)). Qed.
Lemma lem6928006 (_92402 : int) : (term340 _92402) = (term357 _92402).
Proof. exact (MK_COMB (@lem6928004) (@lem6928005 _92402)). Qed.
Lemma lem6928007 (_92402 : int) : (term339 _92402) = (term357 _92402).
Proof. exact (TRANS (@lem6927904 _92402) (@lem6928006 _92402)). Qed.
Lemma lem6928008 (_92402 : int) : (term357 _92402) = term108.
Proof. exact (@lem1982719 (real_of_int _92402)). Qed.
Lemma lem6928009 (_92402 : int) : (term339 _92402) = term108.
Proof. exact (TRANS (@lem6928007 _92402) (@lem6928008 _92402)). Qed.
Lemma lem6928010 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928011 (_92402 : int) : (term358 _92402) = term359.
Proof. exact (MK_COMB (@lem6928010) (@lem6928009 _92402)). Qed.
Lemma lem6928012 (_92403 : int) : (term360 _92403) = (term340 _92403).
Proof. exact (@lem1982715 term157 (real_of_int _92403)). Qed.
Lemma lem6928014 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6928015 : term122 = term192.
Proof. exact (@lem6928014 term123). Qed.
Lemma lem6928017 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6928018 : term157 = term158.
Proof. exact (@lem6928017 term123). Qed.
Lemma lem6928019 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928020 : term341 = term342.
Proof. exact (MK_COMB (@lem6928019) (@lem6928018)). Qed.
Lemma lem6928021 : term343 = term344.
Proof. exact (MK_COMB (@lem6928020) (@lem6928015)). Qed.
Lemma lem6928022 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6928024 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928025 : term300 = term306.
Proof. exact (@lem6928024 (NUMERAL 0) term123). Qed.
Lemma lem6928026 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928027 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928028 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928027 h1) (fun h1 : term306 = True => @lem6928026)). Qed.
Lemma lem6928029 : term306 = True.
Proof. exact (EQ_MP (@lem6928028) (@lem6928026)). Qed.
Lemma lem6928030 : term300 = True.
Proof. exact (TRANS (@lem6928025) (@lem6928029)). Qed.
Lemma lem6928031 : True = term300.
Proof. exact (SYM (@lem6928030)). Qed.
Lemma lem6928032 : term300.
Proof. exact (EQ_MP (@lem6928031) (@lem0)). Qed.
Lemma lem6928033 : term346.
Proof. exact (@lem6928022 (@lem6928032)). Qed.
Lemma lem6928035 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928036 : term300 = term306.
Proof. exact (@lem6928035 (NUMERAL 0) term123). Qed.
Lemma lem6928037 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928038 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928039 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928038 h1) (fun h1 : term306 = True => @lem6928037)). Qed.
Lemma lem6928040 : term306 = True.
Proof. exact (EQ_MP (@lem6928039) (@lem6928037)). Qed.
Lemma lem6928041 : term300 = True.
Proof. exact (TRANS (@lem6928036) (@lem6928040)). Qed.
Lemma lem6928042 : True = term300.
Proof. exact (SYM (@lem6928041)). Qed.
Lemma lem6928043 : term300.
Proof. exact (EQ_MP (@lem6928042) (@lem0)). Qed.
Lemma lem6928044 : term347.
Proof. exact (@lem6928033 (@lem6928043)). Qed.
Lemma lem6928046 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928047 : term300 = term306.
Proof. exact (@lem6928046 (NUMERAL 0) term123). Qed.
Lemma lem6928048 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928049 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928050 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928049 h1) (fun h1 : term306 = True => @lem6928048)). Qed.
Lemma lem6928051 : term306 = True.
Proof. exact (EQ_MP (@lem6928050) (@lem6928048)). Qed.
Lemma lem6928052 : term300 = True.
Proof. exact (TRANS (@lem6928047) (@lem6928051)). Qed.
Lemma lem6928053 : True = term300.
Proof. exact (SYM (@lem6928052)). Qed.
Lemma lem6928054 : term300.
Proof. exact (EQ_MP (@lem6928053) (@lem0)). Qed.
Lemma lem6928055 : term348.
Proof. exact (@lem6928044 (@lem6928054)). Qed.
Lemma lem6928057 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928058 : term166 = term167.
Proof. exact (@lem6928057 term123 term123). Qed.
Lemma lem6928059 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928060 : term169 = term123.
Proof. exact (EQ_MP (@lem6928059) (@lem940073)). Qed.
Lemma lem6928061 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928062 : term167 = term122.
Proof. exact (MK_COMB (@lem6928061) (@lem6928060)). Qed.
Lemma lem6928063 : term166 = term122.
Proof. exact (TRANS (@lem6928058) (@lem6928062)). Qed.
Lemma lem6928065 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6928066 : term193 = term198.
Proof. exact (@lem6928065 term123 term123). Qed.
Lemma lem6928067 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928068 : term169 = term123.
Proof. exact (EQ_MP (@lem6928067) (@lem940073)). Qed.
Lemma lem6928069 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928070 : term167 = term122.
Proof. exact (MK_COMB (@lem6928069) (@lem6928068)). Qed.
Lemma lem6928071 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6928072 : term198 = term157.
Proof. exact (MK_COMB (@lem6928071) (@lem6928070)). Qed.
Lemma lem6928073 : term193 = term157.
Proof. exact (TRANS (@lem6928066) (@lem6928072)). Qed.
Lemma lem6928074 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928075 : term349 = term341.
Proof. exact (MK_COMB (@lem6928074) (@lem6928073)). Qed.
Lemma lem6928076 : term350 = term343.
Proof. exact (MK_COMB (@lem6928075) (@lem6928063)). Qed.
Lemma lem6928078 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6928079 : term343 = term108.
Proof. exact (@lem6928078 term123). Qed.
Lemma lem6928080 : term350 = term108.
Proof. exact (TRANS (@lem6928076) (@lem6928079)). Qed.
Lemma lem6928081 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928082 : term352 = term353.
Proof. exact (MK_COMB (@lem6928081) (@lem6928080)). Qed.
Lemma lem6928083 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6928084 : term354 = term311.
Proof. exact (MK_COMB (@lem6928082) (@lem6928083)). Qed.
Lemma lem6928086 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6928087 : term311 = term108.
Proof. exact (@lem6928086 term123). Qed.
Lemma lem6928088 : term354 = term108.
Proof. exact (TRANS (@lem6928084) (@lem6928087)). Qed.
Lemma lem6928090 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928091 : term166 = term167.
Proof. exact (@lem6928090 term123 term123). Qed.
Lemma lem6928092 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928093 : term169 = term123.
Proof. exact (EQ_MP (@lem6928092) (@lem940073)). Qed.
Lemma lem6928094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928095 : term167 = term122.
Proof. exact (MK_COMB (@lem6928094) (@lem6928093)). Qed.
Lemma lem6928096 : term166 = term122.
Proof. exact (TRANS (@lem6928091) (@lem6928095)). Qed.
Lemma lem6928097 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6928098 : term355 = term311.
Proof. exact (MK_COMB (@lem6928097) (@lem6928096)). Qed.
Lemma lem6928100 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6928101 : term311 = term108.
Proof. exact (@lem6928100 term123). Qed.
Lemma lem6928102 : term355 = term108.
Proof. exact (TRANS (@lem6928098) (@lem6928101)). Qed.
Lemma lem6928103 : term108 = term355.
Proof. exact (SYM (@lem6928102)). Qed.
Lemma lem6928104 : term354 = term355.
Proof. exact (TRANS (@lem6928088) (@lem6928103)). Qed.
Lemma lem6928105 : term344 = term154.
Proof. exact (@lem6928055 (@lem6928104)). Qed.
Lemma lem6928106 : term343 = term154.
Proof. exact (TRANS (@lem6928021) (@lem6928105)). Qed.
Lemma lem6928108 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6928109 : term154 = term108.
Proof. exact (@lem6928108 term108). Qed.
Lemma lem6928110 : term343 = term108.
Proof. exact (TRANS (@lem6928106) (@lem6928109)). Qed.
Lemma lem6928111 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928112 : term356 = term353.
Proof. exact (MK_COMB (@lem6928111) (@lem6928110)). Qed.
Lemma lem6928113 (_92403 : int) : (real_of_int _92403) = (real_of_int _92403).
Proof. exact (eq_refl (real_of_int _92403)). Qed.
Lemma lem6928114 (_92403 : int) : (term340 _92403) = (term357 _92403).
Proof. exact (MK_COMB (@lem6928112) (@lem6928113 _92403)). Qed.
Lemma lem6928115 (_92403 : int) : (term360 _92403) = (term357 _92403).
Proof. exact (TRANS (@lem6928012 _92403) (@lem6928114 _92403)). Qed.
Lemma lem6928116 (_92403 : int) : (term357 _92403) = term108.
Proof. exact (@lem1982719 (real_of_int _92403)). Qed.
Lemma lem6928117 (_92403 : int) : (term360 _92403) = term108.
Proof. exact (TRANS (@lem6928115 _92403) (@lem6928116 _92403)). Qed.
Lemma lem6928118 (_92402 : int) (_92403 : int) : (term338 _92402 _92403) = term361.
Proof. exact (MK_COMB (@lem6928011 _92402) (@lem6928117 _92403)). Qed.
Lemma lem6928119 (_92402 : int) (_92403 : int) : (term337 _92402 _92403) = term361.
Proof. exact (TRANS (@lem6927903 _92402 _92403) (@lem6928118 _92402 _92403)). Qed.
Lemma lem6928120 : term361 = term108.
Proof. exact (@lem1982721 term108). Qed.
Lemma lem6928121 (_92402 : int) (_92403 : int) : (term337 _92402 _92403) = term108.
Proof. exact (TRANS (@lem6928119 _92402 _92403) (@lem6928120)). Qed.
Lemma lem6928122 (_92401 : int) : (term124 _92401) = (term124 _92401).
Proof. exact (eq_refl (term124 _92401)). Qed.
Lemma lem6928123 (_92402 : int) (_92403 : int) (_92401 : int) : (term336 _92401 _92402 _92403) = (term174 _92401).
Proof. exact (MK_COMB (@lem6928122 _92401) (@lem6928121 _92402 _92403)). Qed.
Lemma lem6928124 (_92402 : int) (_92403 : int) (_92401 : int) : (term335 _92401 _92402 _92403) = (term174 _92401).
Proof. exact (TRANS (@lem6927902 _92401 _92402 _92403) (@lem6928123 _92402 _92403 _92401)). Qed.
Lemma lem6928125 (_92401 : int) : (term174 _92401) = (real_of_int _92401).
Proof. exact (@lem1982723 (real_of_int _92401)). Qed.
Lemma lem6928126 (_92402 : int) (_92403 : int) (_92401 : int) : (term335 _92401 _92402 _92403) = (real_of_int _92401).
Proof. exact (TRANS (@lem6928124 _92402 _92403 _92401) (@lem6928125 _92401)). Qed.
Lemma lem6928127 (_92400 : int) : (term201 _92400) = (term201 _92400).
Proof. exact (eq_refl (term201 _92400)). Qed.
Lemma lem6928128 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term334 _92400 _92401 _92402 _92403) = (term217 _92400 _92401).
Proof. exact (MK_COMB (@lem6928127 _92400) (@lem6928126 _92402 _92403 _92401)). Qed.
Lemma lem6928129 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term333 _92401 _92400 _92402 _92403) = (term217 _92400 _92401).
Proof. exact (TRANS (@lem6927901 _92400 _92401 _92402 _92403) (@lem6928128 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6928130 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6928131 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : (term362 _92401 _92400 _92402 _92403) = (term363 _92400 _92401).
Proof. exact (MK_COMB (@lem6928130) (@lem6928129 _92402 _92403 _92400 _92401)). Qed.
Lemma lem6928132 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6928133 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) : ((term333 _92401 _92400 _92402 _92403) = term108) = ((term217 _92400 _92401) = term108).
Proof. exact (MK_COMB (@lem6928131 _92402 _92403 _92400 _92401) (@lem6928132)). Qed.
Lemma lem6928134 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : (term217 _92400 _92401) = term108.
Proof. exact (EQ_MP (@lem6928133 _92402 _92403 _92400 _92401) (@lem6927900 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928136 (y : real) : term324 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6928137 (_92400 : int) (_92401 : int) : term364 _92400 _92401.
Proof. exact (@lem6928136 (term217 _92400 _92401)). Qed.
Lemma lem6928138 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term365 _92400 _92401.
Proof. exact (@lem6928137 _92400 _92401 (@lem6928134 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928139 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term429 _92400 _92401.
Proof. exact (@lem6928138 _92402 _92403 _92400 _92401 h1 term157). Qed.
Lemma lem6928140 (_92400 : int) (_92401 : int) : (term429 _92400 _92401) = ((term430 _92400 _92401) = term108).
Proof. exact (eq_refl (term429 _92400 _92401)). Qed.
Lemma lem6928141 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : (term430 _92400 _92401) = term108.
Proof. exact (EQ_MP (@lem6928140 _92400 _92401) (@lem6928139 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928142 (_92400 : int) (_92401 : int) : (term430 _92400 _92401) = (term431 _92400 _92401).
Proof. exact (@lem1982781 (term184 _92400) term157 (real_of_int _92401)). Qed.
Lemma lem6928143 (_92401 : int) : (term184 _92401) = (term184 _92401).
Proof. exact (eq_refl (term184 _92401)). Qed.
Lemma lem6928144 (_92400 : int) : (term432 _92400) = (term433 _92400).
Proof. exact (@lem1982749 term157 term157 (real_of_int _92400)). Qed.
Lemma lem6928146 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6928147 : term157 = term158.
Proof. exact (@lem6928146 term123). Qed.
Lemma lem6928149 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6928150 : term157 = term158.
Proof. exact (@lem6928149 term123). Qed.
Lemma lem6928151 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928152 : term159 = term160.
Proof. exact (MK_COMB (@lem6928151) (@lem6928150)). Qed.
Lemma lem6928153 : term434 = term435.
Proof. exact (MK_COMB (@lem6928152) (@lem6928147)). Qed.
Lemma lem6928154 : term435 = term436.
Proof. exact (@lem1981613 term157 term157 term122 term122). Qed.
Lemma lem6928156 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928157 : term166 = term167.
Proof. exact (@lem6928156 term123 term123). Qed.
Lemma lem6928158 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928159 : term169 = term123.
Proof. exact (EQ_MP (@lem6928158) (@lem940073)). Qed.
Lemma lem6928160 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928161 : term167 = term122.
Proof. exact (MK_COMB (@lem6928160) (@lem6928159)). Qed.
Lemma lem6928162 : term166 = term122.
Proof. exact (TRANS (@lem6928157) (@lem6928161)). Qed.
Lemma lem6928164 (m : nat) (n : nat) : (term437 m n) = (term165 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem6928165 : term434 = term167.
Proof. exact (@lem6928164 term123 term123). Qed.
Lemma lem6928166 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928167 : term169 = term123.
Proof. exact (EQ_MP (@lem6928166) (@lem940073)). Qed.
Lemma lem6928168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928169 : term167 = term122.
Proof. exact (MK_COMB (@lem6928168) (@lem6928167)). Qed.
Lemma lem6928170 : term434 = term122.
Proof. exact (TRANS (@lem6928165) (@lem6928169)). Qed.
Lemma lem6928171 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6928172 : term438 = term439.
Proof. exact (MK_COMB (@lem6928171) (@lem6928170)). Qed.
Lemma lem6928173 : term436 = term192.
Proof. exact (MK_COMB (@lem6928172) (@lem6928162)). Qed.
Lemma lem6928174 : term435 = term192.
Proof. exact (TRANS (@lem6928154) (@lem6928173)). Qed.
Lemma lem6928175 : term434 = term192.
Proof. exact (TRANS (@lem6928153) (@lem6928174)). Qed.
Lemma lem6928177 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6928178 : term192 = term122.
Proof. exact (@lem6928177 term122). Qed.
Lemma lem6928179 : term434 = term122.
Proof. exact (TRANS (@lem6928175) (@lem6928178)). Qed.
Lemma lem6928180 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928181 : term440 = term441.
Proof. exact (MK_COMB (@lem6928180) (@lem6928179)). Qed.
Lemma lem6928182 (_92400 : int) : (real_of_int _92400) = (real_of_int _92400).
Proof. exact (eq_refl (real_of_int _92400)). Qed.
Lemma lem6928183 (_92400 : int) : (term433 _92400) = (term397 _92400).
Proof. exact (MK_COMB (@lem6928181) (@lem6928182 _92400)). Qed.
Lemma lem6928184 (_92400 : int) : (term432 _92400) = (term397 _92400).
Proof. exact (TRANS (@lem6928144 _92400) (@lem6928183 _92400)). Qed.
Lemma lem6928185 (_92400 : int) : (term397 _92400) = (real_of_int _92400).
Proof. exact (@lem1982709 (real_of_int _92400)). Qed.
Lemma lem6928186 (_92400 : int) : (term432 _92400) = (real_of_int _92400).
Proof. exact (TRANS (@lem6928184 _92400) (@lem6928185 _92400)). Qed.
Lemma lem6928187 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928188 (_92400 : int) : (term442 _92400) = (term124 _92400).
Proof. exact (MK_COMB (@lem6928187) (@lem6928186 _92400)). Qed.
Lemma lem6928189 (_92400 : int) (_92401 : int) : (term431 _92400 _92401) = (term216 _92400 _92401).
Proof. exact (MK_COMB (@lem6928188 _92400) (@lem6928143 _92401)). Qed.
Lemma lem6928190 (_92400 : int) (_92401 : int) : (term430 _92400 _92401) = (term216 _92400 _92401).
Proof. exact (TRANS (@lem6928142 _92400 _92401) (@lem6928189 _92400 _92401)). Qed.
Lemma lem6928191 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6928192 (_92400 : int) (_92401 : int) : (term443 _92400 _92401) = (term444 _92400 _92401).
Proof. exact (MK_COMB (@lem6928191) (@lem6928190 _92400 _92401)). Qed.
Lemma lem6928193 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6928194 (_92400 : int) (_92401 : int) : ((term430 _92400 _92401) = term108) = ((term216 _92400 _92401) = term108).
Proof. exact (MK_COMB (@lem6928192 _92400 _92401) (@lem6928193)). Qed.
Lemma lem6928195 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : (term216 _92400 _92401) = term108.
Proof. exact (EQ_MP (@lem6928194 _92400 _92401) (@lem6928141 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928196 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term445 _92400 _92401.
Proof. exact (conj (@lem6928195 _92402 _92403 _92400 _92401 h1) (@lem6927808 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928198 (x : real) (y : real) : term370 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6928199 (_92400 : int) (_92401 : int) : term446 _92400 _92401.
Proof. exact (@lem6928198 (term216 _92400 _92401) (term204 _92400 _92401)). Qed.
Lemma lem6928200 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term447 _92400 _92401.
Proof. exact (@lem6928199 _92400 _92401 (@lem6928196 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928201 (_92400 : int) (_92401 : int) : (term448 _92400 _92401) = (term449 _92400 _92401).
Proof. exact (@lem1982753 (real_of_int _92400) (term184 _92400) (term184 _92401) (term450 _92401)). Qed.
Lemma lem6928202 (_92400 : int) : (term360 _92400) = (term340 _92400).
Proof. exact (@lem1982715 term157 (real_of_int _92400)). Qed.
Lemma lem6928204 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6928205 : term122 = term192.
Proof. exact (@lem6928204 term123). Qed.
Lemma lem6928207 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6928208 : term157 = term158.
Proof. exact (@lem6928207 term123). Qed.
Lemma lem6928209 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928210 : term341 = term342.
Proof. exact (MK_COMB (@lem6928209) (@lem6928208)). Qed.
Lemma lem6928211 : term343 = term344.
Proof. exact (MK_COMB (@lem6928210) (@lem6928205)). Qed.
Lemma lem6928212 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6928214 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928215 : term300 = term306.
Proof. exact (@lem6928214 (NUMERAL 0) term123). Qed.
Lemma lem6928216 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928217 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928218 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928217 h1) (fun h1 : term306 = True => @lem6928216)). Qed.
Lemma lem6928219 : term306 = True.
Proof. exact (EQ_MP (@lem6928218) (@lem6928216)). Qed.
Lemma lem6928220 : term300 = True.
Proof. exact (TRANS (@lem6928215) (@lem6928219)). Qed.
Lemma lem6928221 : True = term300.
Proof. exact (SYM (@lem6928220)). Qed.
Lemma lem6928222 : term300.
Proof. exact (EQ_MP (@lem6928221) (@lem0)). Qed.
Lemma lem6928223 : term346.
Proof. exact (@lem6928212 (@lem6928222)). Qed.
Lemma lem6928225 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928226 : term300 = term306.
Proof. exact (@lem6928225 (NUMERAL 0) term123). Qed.
Lemma lem6928227 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928228 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928229 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928228 h1) (fun h1 : term306 = True => @lem6928227)). Qed.
Lemma lem6928230 : term306 = True.
Proof. exact (EQ_MP (@lem6928229) (@lem6928227)). Qed.
Lemma lem6928231 : term300 = True.
Proof. exact (TRANS (@lem6928226) (@lem6928230)). Qed.
Lemma lem6928232 : True = term300.
Proof. exact (SYM (@lem6928231)). Qed.
Lemma lem6928233 : term300.
Proof. exact (EQ_MP (@lem6928232) (@lem0)). Qed.
Lemma lem6928234 : term347.
Proof. exact (@lem6928223 (@lem6928233)). Qed.
Lemma lem6928236 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928237 : term300 = term306.
Proof. exact (@lem6928236 (NUMERAL 0) term123). Qed.
Lemma lem6928238 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928239 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928240 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928239 h1) (fun h1 : term306 = True => @lem6928238)). Qed.
Lemma lem6928241 : term306 = True.
Proof. exact (EQ_MP (@lem6928240) (@lem6928238)). Qed.
Lemma lem6928242 : term300 = True.
Proof. exact (TRANS (@lem6928237) (@lem6928241)). Qed.
Lemma lem6928243 : True = term300.
Proof. exact (SYM (@lem6928242)). Qed.
Lemma lem6928244 : term300.
Proof. exact (EQ_MP (@lem6928243) (@lem0)). Qed.
Lemma lem6928245 : term348.
Proof. exact (@lem6928234 (@lem6928244)). Qed.
Lemma lem6928247 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928248 : term166 = term167.
Proof. exact (@lem6928247 term123 term123). Qed.
Lemma lem6928249 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928250 : term169 = term123.
Proof. exact (EQ_MP (@lem6928249) (@lem940073)). Qed.
Lemma lem6928251 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928252 : term167 = term122.
Proof. exact (MK_COMB (@lem6928251) (@lem6928250)). Qed.
Lemma lem6928253 : term166 = term122.
Proof. exact (TRANS (@lem6928248) (@lem6928252)). Qed.
Lemma lem6928255 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6928256 : term193 = term198.
Proof. exact (@lem6928255 term123 term123). Qed.
Lemma lem6928257 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928258 : term169 = term123.
Proof. exact (EQ_MP (@lem6928257) (@lem940073)). Qed.
Lemma lem6928259 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928260 : term167 = term122.
Proof. exact (MK_COMB (@lem6928259) (@lem6928258)). Qed.
Lemma lem6928261 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6928262 : term198 = term157.
Proof. exact (MK_COMB (@lem6928261) (@lem6928260)). Qed.
Lemma lem6928263 : term193 = term157.
Proof. exact (TRANS (@lem6928256) (@lem6928262)). Qed.
Lemma lem6928264 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928265 : term349 = term341.
Proof. exact (MK_COMB (@lem6928264) (@lem6928263)). Qed.
Lemma lem6928266 : term350 = term343.
Proof. exact (MK_COMB (@lem6928265) (@lem6928253)). Qed.
Lemma lem6928268 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6928269 : term343 = term108.
Proof. exact (@lem6928268 term123). Qed.
Lemma lem6928270 : term350 = term108.
Proof. exact (TRANS (@lem6928266) (@lem6928269)). Qed.
Lemma lem6928271 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928272 : term352 = term353.
Proof. exact (MK_COMB (@lem6928271) (@lem6928270)). Qed.
Lemma lem6928273 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6928274 : term354 = term311.
Proof. exact (MK_COMB (@lem6928272) (@lem6928273)). Qed.
Lemma lem6928276 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6928277 : term311 = term108.
Proof. exact (@lem6928276 term123). Qed.
Lemma lem6928278 : term354 = term108.
Proof. exact (TRANS (@lem6928274) (@lem6928277)). Qed.
Lemma lem6928280 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928281 : term166 = term167.
Proof. exact (@lem6928280 term123 term123). Qed.
Lemma lem6928282 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928283 : term169 = term123.
Proof. exact (EQ_MP (@lem6928282) (@lem940073)). Qed.
Lemma lem6928284 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928285 : term167 = term122.
Proof. exact (MK_COMB (@lem6928284) (@lem6928283)). Qed.
Lemma lem6928286 : term166 = term122.
Proof. exact (TRANS (@lem6928281) (@lem6928285)). Qed.
Lemma lem6928287 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6928288 : term355 = term311.
Proof. exact (MK_COMB (@lem6928287) (@lem6928286)). Qed.
Lemma lem6928290 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6928291 : term311 = term108.
Proof. exact (@lem6928290 term123). Qed.
Lemma lem6928292 : term355 = term108.
Proof. exact (TRANS (@lem6928288) (@lem6928291)). Qed.
Lemma lem6928293 : term108 = term355.
Proof. exact (SYM (@lem6928292)). Qed.
Lemma lem6928294 : term354 = term355.
Proof. exact (TRANS (@lem6928278) (@lem6928293)). Qed.
Lemma lem6928295 : term344 = term154.
Proof. exact (@lem6928245 (@lem6928294)). Qed.
Lemma lem6928296 : term343 = term154.
Proof. exact (TRANS (@lem6928211) (@lem6928295)). Qed.
Lemma lem6928298 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6928299 : term154 = term108.
Proof. exact (@lem6928298 term108). Qed.
Lemma lem6928300 : term343 = term108.
Proof. exact (TRANS (@lem6928296) (@lem6928299)). Qed.
Lemma lem6928301 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928302 : term356 = term353.
Proof. exact (MK_COMB (@lem6928301) (@lem6928300)). Qed.
Lemma lem6928303 (_92400 : int) : (real_of_int _92400) = (real_of_int _92400).
Proof. exact (eq_refl (real_of_int _92400)). Qed.
Lemma lem6928304 (_92400 : int) : (term340 _92400) = (term357 _92400).
Proof. exact (MK_COMB (@lem6928302) (@lem6928303 _92400)). Qed.
Lemma lem6928305 (_92400 : int) : (term360 _92400) = (term357 _92400).
Proof. exact (TRANS (@lem6928202 _92400) (@lem6928304 _92400)). Qed.
Lemma lem6928306 (_92400 : int) : (term357 _92400) = term108.
Proof. exact (@lem1982719 (real_of_int _92400)). Qed.
Lemma lem6928307 (_92400 : int) : (term360 _92400) = term108.
Proof. exact (TRANS (@lem6928305 _92400) (@lem6928306 _92400)). Qed.
Lemma lem6928308 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928309 (_92400 : int) : (term377 _92400) = term359.
Proof. exact (MK_COMB (@lem6928308) (@lem6928307 _92400)). Qed.
Lemma lem6928310 (_92401 : int) : (term451 _92401) = (term421 _92401).
Proof. exact (@lem1982763 (term184 _92401) (real_of_int _92401) term157). Qed.
Lemma lem6928311 (_92401 : int) : (term339 _92401) = (term340 _92401).
Proof. exact (@lem1982713 term157 (real_of_int _92401)). Qed.
Lemma lem6928313 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6928314 : term122 = term192.
Proof. exact (@lem6928313 term123). Qed.
Lemma lem6928316 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6928317 : term157 = term158.
Proof. exact (@lem6928316 term123). Qed.
Lemma lem6928318 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928319 : term341 = term342.
Proof. exact (MK_COMB (@lem6928318) (@lem6928317)). Qed.
Lemma lem6928320 : term343 = term344.
Proof. exact (MK_COMB (@lem6928319) (@lem6928314)). Qed.
Lemma lem6928321 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6928323 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928324 : term300 = term306.
Proof. exact (@lem6928323 (NUMERAL 0) term123). Qed.
Lemma lem6928325 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928326 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928327 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928326 h1) (fun h1 : term306 = True => @lem6928325)). Qed.
Lemma lem6928328 : term306 = True.
Proof. exact (EQ_MP (@lem6928327) (@lem6928325)). Qed.
Lemma lem6928329 : term300 = True.
Proof. exact (TRANS (@lem6928324) (@lem6928328)). Qed.
Lemma lem6928330 : True = term300.
Proof. exact (SYM (@lem6928329)). Qed.
Lemma lem6928331 : term300.
Proof. exact (EQ_MP (@lem6928330) (@lem0)). Qed.
Lemma lem6928332 : term346.
Proof. exact (@lem6928321 (@lem6928331)). Qed.
Lemma lem6928334 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928335 : term300 = term306.
Proof. exact (@lem6928334 (NUMERAL 0) term123). Qed.
Lemma lem6928336 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928337 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928338 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928337 h1) (fun h1 : term306 = True => @lem6928336)). Qed.
Lemma lem6928339 : term306 = True.
Proof. exact (EQ_MP (@lem6928338) (@lem6928336)). Qed.
Lemma lem6928340 : term300 = True.
Proof. exact (TRANS (@lem6928335) (@lem6928339)). Qed.
Lemma lem6928341 : True = term300.
Proof. exact (SYM (@lem6928340)). Qed.
Lemma lem6928342 : term300.
Proof. exact (EQ_MP (@lem6928341) (@lem0)). Qed.
Lemma lem6928343 : term347.
Proof. exact (@lem6928332 (@lem6928342)). Qed.
Lemma lem6928345 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928346 : term300 = term306.
Proof. exact (@lem6928345 (NUMERAL 0) term123). Qed.
Lemma lem6928347 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928348 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928349 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928348 h1) (fun h1 : term306 = True => @lem6928347)). Qed.
Lemma lem6928350 : term306 = True.
Proof. exact (EQ_MP (@lem6928349) (@lem6928347)). Qed.
Lemma lem6928351 : term300 = True.
Proof. exact (TRANS (@lem6928346) (@lem6928350)). Qed.
Lemma lem6928352 : True = term300.
Proof. exact (SYM (@lem6928351)). Qed.
Lemma lem6928353 : term300.
Proof. exact (EQ_MP (@lem6928352) (@lem0)). Qed.
Lemma lem6928354 : term348.
Proof. exact (@lem6928343 (@lem6928353)). Qed.
Lemma lem6928356 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928357 : term166 = term167.
Proof. exact (@lem6928356 term123 term123). Qed.
Lemma lem6928358 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928359 : term169 = term123.
Proof. exact (EQ_MP (@lem6928358) (@lem940073)). Qed.
Lemma lem6928360 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928361 : term167 = term122.
Proof. exact (MK_COMB (@lem6928360) (@lem6928359)). Qed.
Lemma lem6928362 : term166 = term122.
Proof. exact (TRANS (@lem6928357) (@lem6928361)). Qed.
Lemma lem6928364 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6928365 : term193 = term198.
Proof. exact (@lem6928364 term123 term123). Qed.
Lemma lem6928366 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928367 : term169 = term123.
Proof. exact (EQ_MP (@lem6928366) (@lem940073)). Qed.
Lemma lem6928368 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928369 : term167 = term122.
Proof. exact (MK_COMB (@lem6928368) (@lem6928367)). Qed.
Lemma lem6928370 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6928371 : term198 = term157.
Proof. exact (MK_COMB (@lem6928370) (@lem6928369)). Qed.
Lemma lem6928372 : term193 = term157.
Proof. exact (TRANS (@lem6928365) (@lem6928371)). Qed.
Lemma lem6928373 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928374 : term349 = term341.
Proof. exact (MK_COMB (@lem6928373) (@lem6928372)). Qed.
Lemma lem6928375 : term350 = term343.
Proof. exact (MK_COMB (@lem6928374) (@lem6928362)). Qed.
Lemma lem6928377 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6928378 : term343 = term108.
Proof. exact (@lem6928377 term123). Qed.
Lemma lem6928379 : term350 = term108.
Proof. exact (TRANS (@lem6928375) (@lem6928378)). Qed.
Lemma lem6928380 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928381 : term352 = term353.
Proof. exact (MK_COMB (@lem6928380) (@lem6928379)). Qed.
Lemma lem6928382 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6928383 : term354 = term311.
Proof. exact (MK_COMB (@lem6928381) (@lem6928382)). Qed.
Lemma lem6928385 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6928386 : term311 = term108.
Proof. exact (@lem6928385 term123). Qed.
Lemma lem6928387 : term354 = term108.
Proof. exact (TRANS (@lem6928383) (@lem6928386)). Qed.
Lemma lem6928389 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928390 : term166 = term167.
Proof. exact (@lem6928389 term123 term123). Qed.
Lemma lem6928391 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928392 : term169 = term123.
Proof. exact (EQ_MP (@lem6928391) (@lem940073)). Qed.
Lemma lem6928393 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928394 : term167 = term122.
Proof. exact (MK_COMB (@lem6928393) (@lem6928392)). Qed.
Lemma lem6928395 : term166 = term122.
Proof. exact (TRANS (@lem6928390) (@lem6928394)). Qed.
Lemma lem6928396 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6928397 : term355 = term311.
Proof. exact (MK_COMB (@lem6928396) (@lem6928395)). Qed.
Lemma lem6928399 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6928400 : term311 = term108.
Proof. exact (@lem6928399 term123). Qed.
Lemma lem6928401 : term355 = term108.
Proof. exact (TRANS (@lem6928397) (@lem6928400)). Qed.
Lemma lem6928402 : term108 = term355.
Proof. exact (SYM (@lem6928401)). Qed.
Lemma lem6928403 : term354 = term355.
Proof. exact (TRANS (@lem6928387) (@lem6928402)). Qed.
Lemma lem6928404 : term344 = term154.
Proof. exact (@lem6928354 (@lem6928403)). Qed.
Lemma lem6928405 : term343 = term154.
Proof. exact (TRANS (@lem6928320) (@lem6928404)). Qed.
Lemma lem6928407 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6928408 : term154 = term108.
Proof. exact (@lem6928407 term108). Qed.
Lemma lem6928409 : term343 = term108.
Proof. exact (TRANS (@lem6928405) (@lem6928408)). Qed.
Lemma lem6928410 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928411 : term356 = term353.
Proof. exact (MK_COMB (@lem6928410) (@lem6928409)). Qed.
Lemma lem6928412 (_92401 : int) : (real_of_int _92401) = (real_of_int _92401).
Proof. exact (eq_refl (real_of_int _92401)). Qed.
Lemma lem6928413 (_92401 : int) : (term340 _92401) = (term357 _92401).
Proof. exact (MK_COMB (@lem6928411) (@lem6928412 _92401)). Qed.
Lemma lem6928414 (_92401 : int) : (term339 _92401) = (term357 _92401).
Proof. exact (TRANS (@lem6928311 _92401) (@lem6928413 _92401)). Qed.
Lemma lem6928415 (_92401 : int) : (term357 _92401) = term108.
Proof. exact (@lem1982719 (real_of_int _92401)). Qed.
Lemma lem6928416 (_92401 : int) : (term339 _92401) = term108.
Proof. exact (TRANS (@lem6928414 _92401) (@lem6928415 _92401)). Qed.
Lemma lem6928417 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928418 (_92401 : int) : (term358 _92401) = term359.
Proof. exact (MK_COMB (@lem6928417) (@lem6928416 _92401)). Qed.
Lemma lem6928419 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem6928420 (_92401 : int) : (term421 _92401) = term378.
Proof. exact (MK_COMB (@lem6928418 _92401) (@lem6928419)). Qed.
Lemma lem6928421 (_92401 : int) : (term451 _92401) = term378.
Proof. exact (TRANS (@lem6928310 _92401) (@lem6928420 _92401)). Qed.
Lemma lem6928422 : term378 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem6928423 (_92401 : int) : (term451 _92401) = term157.
Proof. exact (TRANS (@lem6928421 _92401) (@lem6928422)). Qed.
Lemma lem6928424 (_92400 : int) (_92401 : int) : (term449 _92400 _92401) = term378.
Proof. exact (MK_COMB (@lem6928309 _92400) (@lem6928423 _92401)). Qed.
Lemma lem6928425 (_92400 : int) (_92401 : int) : (term448 _92400 _92401) = term378.
Proof. exact (TRANS (@lem6928201 _92400 _92401) (@lem6928424 _92400 _92401)). Qed.
Lemma lem6928426 : term378 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem6928427 (_92400 : int) (_92401 : int) : (term448 _92400 _92401) = term157.
Proof. exact (TRANS (@lem6928425 _92400 _92401) (@lem6928426)). Qed.
Lemma lem6928428 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6928429 (_92400 : int) (_92401 : int) : (term452 _92400 _92401) = term380.
Proof. exact (MK_COMB (@lem6928428) (@lem6928427 _92400 _92401)). Qed.
Lemma lem6928430 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6928431 (_92400 : int) (_92401 : int) : (term447 _92400 _92401) = term381.
Proof. exact (MK_COMB (@lem6928429 _92400 _92401) (@lem6928430)). Qed.
Lemma lem6928432 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : term381.
Proof. exact (EQ_MP (@lem6928431 _92400 _92401) (@lem6928200 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928434 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6928435 : term381 = term382.
Proof. exact (@lem6928434 term108 term157). Qed.
Lemma lem6928437 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6928438 : term157 = term158.
Proof. exact (@lem6928437 term123). Qed.
Lemma lem6928440 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6928441 : term108 = term154.
Proof. exact (@lem6928440 (NUMERAL 0)). Qed.
Lemma lem6928442 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6928443 : term110 = term383.
Proof. exact (MK_COMB (@lem6928442) (@lem6928441)). Qed.
Lemma lem6928444 : term382 = term384.
Proof. exact (MK_COMB (@lem6928443) (@lem6928438)). Qed.
Lemma lem6928445 : term385.
Proof. exact (@lem1980026 term108 term122 term157 term122). Qed.
Lemma lem6928447 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928448 : term300 = term306.
Proof. exact (@lem6928447 (NUMERAL 0) term123). Qed.
Lemma lem6928449 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928450 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928451 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928450 h1) (fun h1 : term306 = True => @lem6928449)). Qed.
Lemma lem6928452 : term306 = True.
Proof. exact (EQ_MP (@lem6928451) (@lem6928449)). Qed.
Lemma lem6928453 : term300 = True.
Proof. exact (TRANS (@lem6928448) (@lem6928452)). Qed.
Lemma lem6928454 : True = term300.
Proof. exact (SYM (@lem6928453)). Qed.
Lemma lem6928455 : term300.
Proof. exact (EQ_MP (@lem6928454) (@lem0)). Qed.
Lemma lem6928456 : term386.
Proof. exact (@lem6928445 (@lem6928455)). Qed.
Lemma lem6928458 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928459 : term300 = term306.
Proof. exact (@lem6928458 (NUMERAL 0) term123). Qed.
Lemma lem6928460 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928461 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928462 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928461 h1) (fun h1 : term306 = True => @lem6928460)). Qed.
Lemma lem6928463 : term306 = True.
Proof. exact (EQ_MP (@lem6928462) (@lem6928460)). Qed.
Lemma lem6928464 : term300 = True.
Proof. exact (TRANS (@lem6928459) (@lem6928463)). Qed.
Lemma lem6928465 : True = term300.
Proof. exact (SYM (@lem6928464)). Qed.
Lemma lem6928466 : term300.
Proof. exact (EQ_MP (@lem6928465) (@lem0)). Qed.
Lemma lem6928467 : term384 = term387.
Proof. exact (@lem6928456 (@lem6928466)). Qed.
Lemma lem6928469 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6928470 : term193 = term198.
Proof. exact (@lem6928469 term123 term123). Qed.
Lemma lem6928471 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928472 : term169 = term123.
Proof. exact (EQ_MP (@lem6928471) (@lem940073)). Qed.
Lemma lem6928473 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928474 : term167 = term122.
Proof. exact (MK_COMB (@lem6928473) (@lem6928472)). Qed.
Lemma lem6928475 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6928476 : term198 = term157.
Proof. exact (MK_COMB (@lem6928475) (@lem6928474)). Qed.
Lemma lem6928477 : term193 = term157.
Proof. exact (TRANS (@lem6928470) (@lem6928476)). Qed.
Lemma lem6928479 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6928480 : term311 = term108.
Proof. exact (@lem6928479 term123). Qed.
Lemma lem6928481 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6928482 : term388 = term110.
Proof. exact (MK_COMB (@lem6928481) (@lem6928480)). Qed.
Lemma lem6928483 : term387 = term382.
Proof. exact (MK_COMB (@lem6928482) (@lem6928477)). Qed.
Lemma lem6928485 (m : nat) (n : nat) : (term389 m n) = (term390 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6928486 : term382 = term391.
Proof. exact (@lem6928485 (NUMERAL 0) term123). Qed.
Lemma lem6928487 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928488 (h1 : term307 = (BIT1 0)) : (term123 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6928489 : (term307 = (BIT1 0)) = ((term123 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928488 h1) (fun h1 : (term123 = (NUMERAL 0)) = False => @lem6928487)). Qed.
Lemma lem6928490 : (term123 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6928489) (@lem6928487)). Qed.
Lemma lem6928491 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6928492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6928493 : term392 = (and True).
Proof. exact (MK_COMB (@lem6928492) (@lem6928491)). Qed.
Lemma lem6928494 : term391 = (True /\ False).
Proof. exact (MK_COMB (@lem6928493) (@lem6928490)). Qed.
Lemma lem6928496 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6928497 : term391 = False.
Proof. exact (TRANS (@lem6928494) (@lem6928496)). Qed.
Lemma lem6928498 : term382 = False.
Proof. exact (TRANS (@lem6928486) (@lem6928497)). Qed.
Lemma lem6928499 : term387 = False.
Proof. exact (TRANS (@lem6928483) (@lem6928498)). Qed.
Lemma lem6928500 : term384 = False.
Proof. exact (TRANS (@lem6928467) (@lem6928499)). Qed.
Lemma lem6928501 : term382 = False.
Proof. exact (TRANS (@lem6928444) (@lem6928500)). Qed.
Lemma lem6928502 : term381 = False.
Proof. exact (TRANS (@lem6928435) (@lem6928501)). Qed.
Lemma lem6928503 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term423 _92402 _92403 _92400 _92401) : False.
Proof. exact (EQ_MP (@lem6928502) (@lem6928432 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928504 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term453 _92402 _92403 _92400 _92401.
Proof. exact (h1). Qed.
Lemma lem6928505 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term290 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6928504 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928507 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term277 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6928505 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928509 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term264 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6928507 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928511 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term251 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6928509 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928513 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term238 _92402 _92403 _92400 _92401.
Proof. exact (proj2 (@lem6928511 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928514 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term210 _92402 _92403 _92400.
Proof. exact (proj1 (@lem6928511 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928515 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : (real_of_int _92400) = term108.
Proof. exact (proj2 (@lem6928514 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928516 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term207 _92402 _92403.
Proof. exact (proj1 (@lem6928514 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928517 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term207 _92400 _92401.
Proof. exact (proj2 (@lem6928513 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928518 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : (term218 _92401 _92402 _92403) = term108.
Proof. exact (proj1 (@lem6928513 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928520 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6928521 : term299 = term300.
Proof. exact (@lem6928520 term108 term122). Qed.
Lemma lem6928523 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6928524 : term122 = term192.
Proof. exact (@lem6928523 term123). Qed.
Lemma lem6928526 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6928527 : term108 = term154.
Proof. exact (@lem6928526 (NUMERAL 0)). Qed.
Lemma lem6928528 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6928529 : term301 = term302.
Proof. exact (MK_COMB (@lem6928528) (@lem6928527)). Qed.
Lemma lem6928530 : term300 = term303.
Proof. exact (MK_COMB (@lem6928529) (@lem6928524)). Qed.
Lemma lem6928531 : term304.
Proof. exact (@lem1980255 term108 term122 term122 term122). Qed.
Lemma lem6928533 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928534 : term300 = term306.
Proof. exact (@lem6928533 (NUMERAL 0) term123). Qed.
Lemma lem6928535 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928536 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928537 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928536 h1) (fun h1 : term306 = True => @lem6928535)). Qed.
Lemma lem6928538 : term306 = True.
Proof. exact (EQ_MP (@lem6928537) (@lem6928535)). Qed.
Lemma lem6928539 : term300 = True.
Proof. exact (TRANS (@lem6928534) (@lem6928538)). Qed.
Lemma lem6928540 : True = term300.
Proof. exact (SYM (@lem6928539)). Qed.
Lemma lem6928541 : term300.
Proof. exact (EQ_MP (@lem6928540) (@lem0)). Qed.
Lemma lem6928542 : term308.
Proof. exact (@lem6928531 (@lem6928541)). Qed.
Lemma lem6928544 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928545 : term300 = term306.
Proof. exact (@lem6928544 (NUMERAL 0) term123). Qed.
Lemma lem6928546 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928547 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928548 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928547 h1) (fun h1 : term306 = True => @lem6928546)). Qed.
Lemma lem6928549 : term306 = True.
Proof. exact (EQ_MP (@lem6928548) (@lem6928546)). Qed.
Lemma lem6928550 : term300 = True.
Proof. exact (TRANS (@lem6928545) (@lem6928549)). Qed.
Lemma lem6928551 : True = term300.
Proof. exact (SYM (@lem6928550)). Qed.
Lemma lem6928552 : term300.
Proof. exact (EQ_MP (@lem6928551) (@lem0)). Qed.
Lemma lem6928553 : term303 = term309.
Proof. exact (@lem6928542 (@lem6928552)). Qed.
Lemma lem6928555 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928556 : term166 = term167.
Proof. exact (@lem6928555 term123 term123). Qed.
Lemma lem6928557 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928558 : term169 = term123.
Proof. exact (EQ_MP (@lem6928557) (@lem940073)). Qed.
Lemma lem6928559 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928560 : term167 = term122.
Proof. exact (MK_COMB (@lem6928559) (@lem6928558)). Qed.
Lemma lem6928561 : term166 = term122.
Proof. exact (TRANS (@lem6928556) (@lem6928560)). Qed.
Lemma lem6928563 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6928564 : term311 = term108.
Proof. exact (@lem6928563 term123). Qed.
Lemma lem6928565 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6928566 : term312 = term301.
Proof. exact (MK_COMB (@lem6928565) (@lem6928564)). Qed.
Lemma lem6928567 : term309 = term300.
Proof. exact (MK_COMB (@lem6928566) (@lem6928561)). Qed.
Lemma lem6928569 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928570 : term300 = term306.
Proof. exact (@lem6928569 (NUMERAL 0) term123). Qed.
Lemma lem6928571 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928572 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928573 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928572 h1) (fun h1 : term306 = True => @lem6928571)). Qed.
Lemma lem6928574 : term306 = True.
Proof. exact (EQ_MP (@lem6928573) (@lem6928571)). Qed.
Lemma lem6928575 : term300 = True.
Proof. exact (TRANS (@lem6928570) (@lem6928574)). Qed.
Lemma lem6928576 : term309 = True.
Proof. exact (TRANS (@lem6928567) (@lem6928575)). Qed.
Lemma lem6928577 : term303 = True.
Proof. exact (TRANS (@lem6928553) (@lem6928576)). Qed.
Lemma lem6928578 : term300 = True.
Proof. exact (TRANS (@lem6928530) (@lem6928577)). Qed.
Lemma lem6928579 : term299 = True.
Proof. exact (TRANS (@lem6928521) (@lem6928578)). Qed.
Lemma lem6928580 : True = term299.
Proof. exact (SYM (@lem6928579)). Qed.
Lemma lem6928581 : term299.
Proof. exact (EQ_MP (@lem6928580) (@lem0)). Qed.
Lemma lem6928582 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term424 _92400 _92401.
Proof. exact (conj (@lem6928581) (@lem6928517 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928584 (x : real) (y : real) : term314 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6928585 (_92400 : int) (_92401 : int) : term425 _92400 _92401.
Proof. exact (@lem6928584 term122 (term204 _92400 _92401)). Qed.
Lemma lem6928586 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term426 _92400 _92401.
Proof. exact (@lem6928585 _92400 _92401 (@lem6928582 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928587 (_92400 : int) (_92401 : int) : (term427 _92400 _92401) = (term204 _92400 _92401).
Proof. exact (@lem1982733 (term204 _92400 _92401)). Qed.
Lemma lem6928588 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6928589 (_92400 : int) (_92401 : int) : (term428 _92400 _92401) = (term206 _92400 _92401).
Proof. exact (MK_COMB (@lem6928588) (@lem6928587 _92400 _92401)). Qed.
Lemma lem6928590 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6928591 (_92400 : int) (_92401 : int) : (term426 _92400 _92401) = (term207 _92400 _92401).
Proof. exact (MK_COMB (@lem6928589 _92400 _92401) (@lem6928590)). Qed.
Lemma lem6928592 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term207 _92400 _92401.
Proof. exact (EQ_MP (@lem6928591 _92400 _92401) (@lem6928586 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928594 (y : real) : term324 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6928595 (_92400 : int) : term399 _92400.
Proof. exact (@lem6928594 (real_of_int _92400)). Qed.
Lemma lem6928596 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term400 _92400.
Proof. exact (@lem6928595 _92400 (@lem6928515 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928597 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term454 _92400.
Proof. exact (@lem6928596 _92402 _92403 _92400 _92401 h1 term122). Qed.
Lemma lem6928598 (_92400 : int) : (term454 _92400) = ((term397 _92400) = term108).
Proof. exact (eq_refl (term454 _92400)). Qed.
Lemma lem6928599 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : (term397 _92400) = term108.
Proof. exact (EQ_MP (@lem6928598 _92400) (@lem6928597 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928600 (_92400 : int) : (term397 _92400) = (real_of_int _92400).
Proof. exact (@lem1982733 (real_of_int _92400)). Qed.
Lemma lem6928601 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6928602 (_92400 : int) : (term455 _92400) = (term114 _92400).
Proof. exact (MK_COMB (@lem6928601) (@lem6928600 _92400)). Qed.
Lemma lem6928603 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6928604 (_92400 : int) : ((term397 _92400) = term108) = ((real_of_int _92400) = term108).
Proof. exact (MK_COMB (@lem6928602 _92400) (@lem6928603)). Qed.
Lemma lem6928605 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : (real_of_int _92400) = term108.
Proof. exact (EQ_MP (@lem6928604 _92400) (@lem6928599 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928606 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term456 _92400 _92401.
Proof. exact (conj (@lem6928605 _92402 _92403 _92400 _92401 h1) (@lem6928592 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928608 (x : real) (y : real) : term370 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6928609 (_92400 : int) (_92401 : int) : term457 _92400 _92401.
Proof. exact (@lem6928608 (real_of_int _92400) (term204 _92400 _92401)). Qed.
Lemma lem6928610 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term458 _92400 _92401.
Proof. exact (@lem6928609 _92400 _92401 (@lem6928606 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928611 (_92400 : int) (_92401 : int) : (term459 _92400 _92401) = (term460 _92400 _92401).
Proof. exact (@lem1982763 (real_of_int _92400) (term184 _92400) (term450 _92401)). Qed.
Lemma lem6928612 (_92400 : int) : (term360 _92400) = (term340 _92400).
Proof. exact (@lem1982715 term157 (real_of_int _92400)). Qed.
Lemma lem6928614 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6928615 : term122 = term192.
Proof. exact (@lem6928614 term123). Qed.
Lemma lem6928617 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6928618 : term157 = term158.
Proof. exact (@lem6928617 term123). Qed.
Lemma lem6928619 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928620 : term341 = term342.
Proof. exact (MK_COMB (@lem6928619) (@lem6928618)). Qed.
Lemma lem6928621 : term343 = term344.
Proof. exact (MK_COMB (@lem6928620) (@lem6928615)). Qed.
Lemma lem6928622 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6928624 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928625 : term300 = term306.
Proof. exact (@lem6928624 (NUMERAL 0) term123). Qed.
Lemma lem6928626 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928627 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928628 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928627 h1) (fun h1 : term306 = True => @lem6928626)). Qed.
Lemma lem6928629 : term306 = True.
Proof. exact (EQ_MP (@lem6928628) (@lem6928626)). Qed.
Lemma lem6928630 : term300 = True.
Proof. exact (TRANS (@lem6928625) (@lem6928629)). Qed.
Lemma lem6928631 : True = term300.
Proof. exact (SYM (@lem6928630)). Qed.
Lemma lem6928632 : term300.
Proof. exact (EQ_MP (@lem6928631) (@lem0)). Qed.
Lemma lem6928633 : term346.
Proof. exact (@lem6928622 (@lem6928632)). Qed.
Lemma lem6928635 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928636 : term300 = term306.
Proof. exact (@lem6928635 (NUMERAL 0) term123). Qed.
Lemma lem6928637 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928638 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928639 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928638 h1) (fun h1 : term306 = True => @lem6928637)). Qed.
Lemma lem6928640 : term306 = True.
Proof. exact (EQ_MP (@lem6928639) (@lem6928637)). Qed.
Lemma lem6928641 : term300 = True.
Proof. exact (TRANS (@lem6928636) (@lem6928640)). Qed.
Lemma lem6928642 : True = term300.
Proof. exact (SYM (@lem6928641)). Qed.
Lemma lem6928643 : term300.
Proof. exact (EQ_MP (@lem6928642) (@lem0)). Qed.
Lemma lem6928644 : term347.
Proof. exact (@lem6928633 (@lem6928643)). Qed.
Lemma lem6928646 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928647 : term300 = term306.
Proof. exact (@lem6928646 (NUMERAL 0) term123). Qed.
Lemma lem6928648 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928649 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928650 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928649 h1) (fun h1 : term306 = True => @lem6928648)). Qed.
Lemma lem6928651 : term306 = True.
Proof. exact (EQ_MP (@lem6928650) (@lem6928648)). Qed.
Lemma lem6928652 : term300 = True.
Proof. exact (TRANS (@lem6928647) (@lem6928651)). Qed.
Lemma lem6928653 : True = term300.
Proof. exact (SYM (@lem6928652)). Qed.
Lemma lem6928654 : term300.
Proof. exact (EQ_MP (@lem6928653) (@lem0)). Qed.
Lemma lem6928655 : term348.
Proof. exact (@lem6928644 (@lem6928654)). Qed.
Lemma lem6928657 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928658 : term166 = term167.
Proof. exact (@lem6928657 term123 term123). Qed.
Lemma lem6928659 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928660 : term169 = term123.
Proof. exact (EQ_MP (@lem6928659) (@lem940073)). Qed.
Lemma lem6928661 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928662 : term167 = term122.
Proof. exact (MK_COMB (@lem6928661) (@lem6928660)). Qed.
Lemma lem6928663 : term166 = term122.
Proof. exact (TRANS (@lem6928658) (@lem6928662)). Qed.
Lemma lem6928665 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6928666 : term193 = term198.
Proof. exact (@lem6928665 term123 term123). Qed.
Lemma lem6928667 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928668 : term169 = term123.
Proof. exact (EQ_MP (@lem6928667) (@lem940073)). Qed.
Lemma lem6928669 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928670 : term167 = term122.
Proof. exact (MK_COMB (@lem6928669) (@lem6928668)). Qed.
Lemma lem6928671 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6928672 : term198 = term157.
Proof. exact (MK_COMB (@lem6928671) (@lem6928670)). Qed.
Lemma lem6928673 : term193 = term157.
Proof. exact (TRANS (@lem6928666) (@lem6928672)). Qed.
Lemma lem6928674 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928675 : term349 = term341.
Proof. exact (MK_COMB (@lem6928674) (@lem6928673)). Qed.
Lemma lem6928676 : term350 = term343.
Proof. exact (MK_COMB (@lem6928675) (@lem6928663)). Qed.
Lemma lem6928678 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6928679 : term343 = term108.
Proof. exact (@lem6928678 term123). Qed.
Lemma lem6928680 : term350 = term108.
Proof. exact (TRANS (@lem6928676) (@lem6928679)). Qed.
Lemma lem6928681 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928682 : term352 = term353.
Proof. exact (MK_COMB (@lem6928681) (@lem6928680)). Qed.
Lemma lem6928683 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6928684 : term354 = term311.
Proof. exact (MK_COMB (@lem6928682) (@lem6928683)). Qed.
Lemma lem6928686 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6928687 : term311 = term108.
Proof. exact (@lem6928686 term123). Qed.
Lemma lem6928688 : term354 = term108.
Proof. exact (TRANS (@lem6928684) (@lem6928687)). Qed.
Lemma lem6928690 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928691 : term166 = term167.
Proof. exact (@lem6928690 term123 term123). Qed.
Lemma lem6928692 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928693 : term169 = term123.
Proof. exact (EQ_MP (@lem6928692) (@lem940073)). Qed.
Lemma lem6928694 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928695 : term167 = term122.
Proof. exact (MK_COMB (@lem6928694) (@lem6928693)). Qed.
Lemma lem6928696 : term166 = term122.
Proof. exact (TRANS (@lem6928691) (@lem6928695)). Qed.
Lemma lem6928697 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6928698 : term355 = term311.
Proof. exact (MK_COMB (@lem6928697) (@lem6928696)). Qed.
Lemma lem6928700 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6928701 : term311 = term108.
Proof. exact (@lem6928700 term123). Qed.
Lemma lem6928702 : term355 = term108.
Proof. exact (TRANS (@lem6928698) (@lem6928701)). Qed.
Lemma lem6928703 : term108 = term355.
Proof. exact (SYM (@lem6928702)). Qed.
Lemma lem6928704 : term354 = term355.
Proof. exact (TRANS (@lem6928688) (@lem6928703)). Qed.
Lemma lem6928705 : term344 = term154.
Proof. exact (@lem6928655 (@lem6928704)). Qed.
Lemma lem6928706 : term343 = term154.
Proof. exact (TRANS (@lem6928621) (@lem6928705)). Qed.
Lemma lem6928708 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6928709 : term154 = term108.
Proof. exact (@lem6928708 term108). Qed.
Lemma lem6928710 : term343 = term108.
Proof. exact (TRANS (@lem6928706) (@lem6928709)). Qed.
Lemma lem6928711 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928712 : term356 = term353.
Proof. exact (MK_COMB (@lem6928711) (@lem6928710)). Qed.
Lemma lem6928713 (_92400 : int) : (real_of_int _92400) = (real_of_int _92400).
Proof. exact (eq_refl (real_of_int _92400)). Qed.
Lemma lem6928714 (_92400 : int) : (term340 _92400) = (term357 _92400).
Proof. exact (MK_COMB (@lem6928712) (@lem6928713 _92400)). Qed.
Lemma lem6928715 (_92400 : int) : (term360 _92400) = (term357 _92400).
Proof. exact (TRANS (@lem6928612 _92400) (@lem6928714 _92400)). Qed.
Lemma lem6928716 (_92400 : int) : (term357 _92400) = term108.
Proof. exact (@lem1982719 (real_of_int _92400)). Qed.
Lemma lem6928717 (_92400 : int) : (term360 _92400) = term108.
Proof. exact (TRANS (@lem6928715 _92400) (@lem6928716 _92400)). Qed.
Lemma lem6928718 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928719 (_92400 : int) : (term377 _92400) = term359.
Proof. exact (MK_COMB (@lem6928718) (@lem6928717 _92400)). Qed.
Lemma lem6928720 (_92401 : int) : (term450 _92401) = (term450 _92401).
Proof. exact (eq_refl (term450 _92401)). Qed.
Lemma lem6928721 (_92400 : int) (_92401 : int) : (term460 _92400 _92401) = (term461 _92401).
Proof. exact (MK_COMB (@lem6928719 _92400) (@lem6928720 _92401)). Qed.
Lemma lem6928722 (_92400 : int) (_92401 : int) : (term459 _92400 _92401) = (term461 _92401).
Proof. exact (TRANS (@lem6928611 _92400 _92401) (@lem6928721 _92400 _92401)). Qed.
Lemma lem6928723 (_92401 : int) : (term461 _92401) = (term450 _92401).
Proof. exact (@lem1982721 (term450 _92401)). Qed.
Lemma lem6928724 (_92400 : int) (_92401 : int) : (term459 _92400 _92401) = (term450 _92401).
Proof. exact (TRANS (@lem6928722 _92400 _92401) (@lem6928723 _92401)). Qed.
Lemma lem6928725 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6928726 (_92400 : int) (_92401 : int) : (term462 _92400 _92401) = (term463 _92401).
Proof. exact (MK_COMB (@lem6928725) (@lem6928724 _92400 _92401)). Qed.
Lemma lem6928727 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6928728 (_92400 : int) (_92401 : int) : (term458 _92400 _92401) = (term464 _92401).
Proof. exact (MK_COMB (@lem6928726 _92400 _92401) (@lem6928727)). Qed.
Lemma lem6928729 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term464 _92401.
Proof. exact (EQ_MP (@lem6928728 _92400 _92401) (@lem6928610 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928731 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6928732 : term299 = term300.
Proof. exact (@lem6928731 term108 term122). Qed.
Lemma lem6928734 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6928735 : term122 = term192.
Proof. exact (@lem6928734 term123). Qed.
Lemma lem6928737 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6928738 : term108 = term154.
Proof. exact (@lem6928737 (NUMERAL 0)). Qed.
Lemma lem6928739 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6928740 : term301 = term302.
Proof. exact (MK_COMB (@lem6928739) (@lem6928738)). Qed.
Lemma lem6928741 : term300 = term303.
Proof. exact (MK_COMB (@lem6928740) (@lem6928735)). Qed.
Lemma lem6928742 : term304.
Proof. exact (@lem1980255 term108 term122 term122 term122). Qed.
Lemma lem6928744 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928745 : term300 = term306.
Proof. exact (@lem6928744 (NUMERAL 0) term123). Qed.
Lemma lem6928746 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928747 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928748 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928747 h1) (fun h1 : term306 = True => @lem6928746)). Qed.
Lemma lem6928749 : term306 = True.
Proof. exact (EQ_MP (@lem6928748) (@lem6928746)). Qed.
Lemma lem6928750 : term300 = True.
Proof. exact (TRANS (@lem6928745) (@lem6928749)). Qed.
Lemma lem6928751 : True = term300.
Proof. exact (SYM (@lem6928750)). Qed.
Lemma lem6928752 : term300.
Proof. exact (EQ_MP (@lem6928751) (@lem0)). Qed.
Lemma lem6928753 : term308.
Proof. exact (@lem6928742 (@lem6928752)). Qed.
Lemma lem6928755 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928756 : term300 = term306.
Proof. exact (@lem6928755 (NUMERAL 0) term123). Qed.
Lemma lem6928757 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928758 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928759 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928758 h1) (fun h1 : term306 = True => @lem6928757)). Qed.
Lemma lem6928760 : term306 = True.
Proof. exact (EQ_MP (@lem6928759) (@lem6928757)). Qed.
Lemma lem6928761 : term300 = True.
Proof. exact (TRANS (@lem6928756) (@lem6928760)). Qed.
Lemma lem6928762 : True = term300.
Proof. exact (SYM (@lem6928761)). Qed.
Lemma lem6928763 : term300.
Proof. exact (EQ_MP (@lem6928762) (@lem0)). Qed.
Lemma lem6928764 : term303 = term309.
Proof. exact (@lem6928753 (@lem6928763)). Qed.
Lemma lem6928766 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928767 : term166 = term167.
Proof. exact (@lem6928766 term123 term123). Qed.
Lemma lem6928768 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928769 : term169 = term123.
Proof. exact (EQ_MP (@lem6928768) (@lem940073)). Qed.
Lemma lem6928770 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928771 : term167 = term122.
Proof. exact (MK_COMB (@lem6928770) (@lem6928769)). Qed.
Lemma lem6928772 : term166 = term122.
Proof. exact (TRANS (@lem6928767) (@lem6928771)). Qed.
Lemma lem6928774 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6928775 : term311 = term108.
Proof. exact (@lem6928774 term123). Qed.
Lemma lem6928776 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6928777 : term312 = term301.
Proof. exact (MK_COMB (@lem6928776) (@lem6928775)). Qed.
Lemma lem6928778 : term309 = term300.
Proof. exact (MK_COMB (@lem6928777) (@lem6928772)). Qed.
Lemma lem6928780 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928781 : term300 = term306.
Proof. exact (@lem6928780 (NUMERAL 0) term123). Qed.
Lemma lem6928782 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928783 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928784 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928783 h1) (fun h1 : term306 = True => @lem6928782)). Qed.
Lemma lem6928785 : term306 = True.
Proof. exact (EQ_MP (@lem6928784) (@lem6928782)). Qed.
Lemma lem6928786 : term300 = True.
Proof. exact (TRANS (@lem6928781) (@lem6928785)). Qed.
Lemma lem6928787 : term309 = True.
Proof. exact (TRANS (@lem6928778) (@lem6928786)). Qed.
Lemma lem6928788 : term303 = True.
Proof. exact (TRANS (@lem6928764) (@lem6928787)). Qed.
Lemma lem6928789 : term300 = True.
Proof. exact (TRANS (@lem6928741) (@lem6928788)). Qed.
Lemma lem6928790 : term299 = True.
Proof. exact (TRANS (@lem6928732) (@lem6928789)). Qed.
Lemma lem6928791 : True = term299.
Proof. exact (SYM (@lem6928790)). Qed.
Lemma lem6928792 : term299.
Proof. exact (EQ_MP (@lem6928791) (@lem0)). Qed.
Lemma lem6928793 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term465 _92401.
Proof. exact (conj (@lem6928792) (@lem6928729 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928795 (x : real) (y : real) : term314 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6928796 (_92401 : int) : term466 _92401.
Proof. exact (@lem6928795 term122 (term450 _92401)). Qed.
Lemma lem6928797 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term467 _92401.
Proof. exact (@lem6928796 _92401 (@lem6928793 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928798 (_92401 : int) : (term468 _92401) = (term450 _92401).
Proof. exact (@lem1982733 (term450 _92401)). Qed.
Lemma lem6928799 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6928800 (_92401 : int) : (term469 _92401) = (term463 _92401).
Proof. exact (MK_COMB (@lem6928799) (@lem6928798 _92401)). Qed.
Lemma lem6928801 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6928802 (_92401 : int) : (term467 _92401) = (term464 _92401).
Proof. exact (MK_COMB (@lem6928800 _92401) (@lem6928801)). Qed.
Lemma lem6928803 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term464 _92401.
Proof. exact (EQ_MP (@lem6928802 _92401) (@lem6928797 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928805 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6928806 : term299 = term300.
Proof. exact (@lem6928805 term108 term122). Qed.
Lemma lem6928808 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6928809 : term122 = term192.
Proof. exact (@lem6928808 term123). Qed.
Lemma lem6928811 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6928812 : term108 = term154.
Proof. exact (@lem6928811 (NUMERAL 0)). Qed.
Lemma lem6928813 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6928814 : term301 = term302.
Proof. exact (MK_COMB (@lem6928813) (@lem6928812)). Qed.
Lemma lem6928815 : term300 = term303.
Proof. exact (MK_COMB (@lem6928814) (@lem6928809)). Qed.
Lemma lem6928816 : term304.
Proof. exact (@lem1980255 term108 term122 term122 term122). Qed.
Lemma lem6928818 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928819 : term300 = term306.
Proof. exact (@lem6928818 (NUMERAL 0) term123). Qed.
Lemma lem6928820 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928821 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928822 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928821 h1) (fun h1 : term306 = True => @lem6928820)). Qed.
Lemma lem6928823 : term306 = True.
Proof. exact (EQ_MP (@lem6928822) (@lem6928820)). Qed.
Lemma lem6928824 : term300 = True.
Proof. exact (TRANS (@lem6928819) (@lem6928823)). Qed.
Lemma lem6928825 : True = term300.
Proof. exact (SYM (@lem6928824)). Qed.
Lemma lem6928826 : term300.
Proof. exact (EQ_MP (@lem6928825) (@lem0)). Qed.
Lemma lem6928827 : term308.
Proof. exact (@lem6928816 (@lem6928826)). Qed.
Lemma lem6928829 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928830 : term300 = term306.
Proof. exact (@lem6928829 (NUMERAL 0) term123). Qed.
Lemma lem6928831 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928832 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928833 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928832 h1) (fun h1 : term306 = True => @lem6928831)). Qed.
Lemma lem6928834 : term306 = True.
Proof. exact (EQ_MP (@lem6928833) (@lem6928831)). Qed.
Lemma lem6928835 : term300 = True.
Proof. exact (TRANS (@lem6928830) (@lem6928834)). Qed.
Lemma lem6928836 : True = term300.
Proof. exact (SYM (@lem6928835)). Qed.
Lemma lem6928837 : term300.
Proof. exact (EQ_MP (@lem6928836) (@lem0)). Qed.
Lemma lem6928838 : term303 = term309.
Proof. exact (@lem6928827 (@lem6928837)). Qed.
Lemma lem6928840 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928841 : term166 = term167.
Proof. exact (@lem6928840 term123 term123). Qed.
Lemma lem6928842 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928843 : term169 = term123.
Proof. exact (EQ_MP (@lem6928842) (@lem940073)). Qed.
Lemma lem6928844 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928845 : term167 = term122.
Proof. exact (MK_COMB (@lem6928844) (@lem6928843)). Qed.
Lemma lem6928846 : term166 = term122.
Proof. exact (TRANS (@lem6928841) (@lem6928845)). Qed.
Lemma lem6928848 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6928849 : term311 = term108.
Proof. exact (@lem6928848 term123). Qed.
Lemma lem6928850 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6928851 : term312 = term301.
Proof. exact (MK_COMB (@lem6928850) (@lem6928849)). Qed.
Lemma lem6928852 : term309 = term300.
Proof. exact (MK_COMB (@lem6928851) (@lem6928846)). Qed.
Lemma lem6928854 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928855 : term300 = term306.
Proof. exact (@lem6928854 (NUMERAL 0) term123). Qed.
Lemma lem6928856 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928857 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928858 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928857 h1) (fun h1 : term306 = True => @lem6928856)). Qed.
Lemma lem6928859 : term306 = True.
Proof. exact (EQ_MP (@lem6928858) (@lem6928856)). Qed.
Lemma lem6928860 : term300 = True.
Proof. exact (TRANS (@lem6928855) (@lem6928859)). Qed.
Lemma lem6928861 : term309 = True.
Proof. exact (TRANS (@lem6928852) (@lem6928860)). Qed.
Lemma lem6928862 : term303 = True.
Proof. exact (TRANS (@lem6928838) (@lem6928861)). Qed.
Lemma lem6928863 : term300 = True.
Proof. exact (TRANS (@lem6928815) (@lem6928862)). Qed.
Lemma lem6928864 : term299 = True.
Proof. exact (TRANS (@lem6928806) (@lem6928863)). Qed.
Lemma lem6928865 : True = term299.
Proof. exact (SYM (@lem6928864)). Qed.
Lemma lem6928866 : term299.
Proof. exact (EQ_MP (@lem6928865) (@lem0)). Qed.
Lemma lem6928867 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term424 _92402 _92403.
Proof. exact (conj (@lem6928866) (@lem6928516 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928869 (x : real) (y : real) : term314 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6928870 (_92402 : int) (_92403 : int) : term425 _92402 _92403.
Proof. exact (@lem6928869 term122 (term204 _92402 _92403)). Qed.
Lemma lem6928871 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term426 _92402 _92403.
Proof. exact (@lem6928870 _92402 _92403 (@lem6928867 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928872 (_92402 : int) (_92403 : int) : (term427 _92402 _92403) = (term204 _92402 _92403).
Proof. exact (@lem1982733 (term204 _92402 _92403)). Qed.
Lemma lem6928873 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6928874 (_92402 : int) (_92403 : int) : (term428 _92402 _92403) = (term206 _92402 _92403).
Proof. exact (MK_COMB (@lem6928873) (@lem6928872 _92402 _92403)). Qed.
Lemma lem6928875 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6928876 (_92402 : int) (_92403 : int) : (term426 _92402 _92403) = (term207 _92402 _92403).
Proof. exact (MK_COMB (@lem6928874 _92402 _92403) (@lem6928875)). Qed.
Lemma lem6928877 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term207 _92402 _92403.
Proof. exact (EQ_MP (@lem6928876 _92402 _92403) (@lem6928871 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928879 (y : real) : term324 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6928880 (_92401 : int) (_92402 : int) (_92403 : int) : term325 _92401 _92402 _92403.
Proof. exact (@lem6928879 (term218 _92401 _92402 _92403)). Qed.
Lemma lem6928881 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term326 _92401 _92402 _92403.
Proof. exact (@lem6928880 _92401 _92402 _92403 (@lem6928518 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928882 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term470 _92401 _92402 _92403.
Proof. exact (@lem6928881 _92402 _92403 _92400 _92401 h1 term157). Qed.
Lemma lem6928883 (_92401 : int) (_92402 : int) (_92403 : int) : (term470 _92401 _92402 _92403) = ((term471 _92401 _92402 _92403) = term108).
Proof. exact (eq_refl (term470 _92401 _92402 _92403)). Qed.
Lemma lem6928884 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : (term471 _92401 _92402 _92403) = term108.
Proof. exact (EQ_MP (@lem6928883 _92401 _92402 _92403) (@lem6928882 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928885 (_92401 : int) (_92402 : int) (_92403 : int) : (term471 _92401 _92402 _92403) = (term472 _92401 _92402 _92403).
Proof. exact (@lem1982781 (real_of_int _92401) term157 (term217 _92402 _92403)). Qed.
Lemma lem6928886 (_92402 : int) (_92403 : int) : (term430 _92402 _92403) = (term431 _92402 _92403).
Proof. exact (@lem1982781 (term184 _92402) term157 (real_of_int _92403)). Qed.
Lemma lem6928887 (_92403 : int) : (term184 _92403) = (term184 _92403).
Proof. exact (eq_refl (term184 _92403)). Qed.
Lemma lem6928888 (_92402 : int) : (term432 _92402) = (term433 _92402).
Proof. exact (@lem1982749 term157 term157 (real_of_int _92402)). Qed.
Lemma lem6928890 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6928891 : term157 = term158.
Proof. exact (@lem6928890 term123). Qed.
Lemma lem6928893 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6928894 : term157 = term158.
Proof. exact (@lem6928893 term123). Qed.
Lemma lem6928895 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928896 : term159 = term160.
Proof. exact (MK_COMB (@lem6928895) (@lem6928894)). Qed.
Lemma lem6928897 : term434 = term435.
Proof. exact (MK_COMB (@lem6928896) (@lem6928891)). Qed.
Lemma lem6928898 : term435 = term436.
Proof. exact (@lem1981613 term157 term157 term122 term122). Qed.
Lemma lem6928900 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928901 : term166 = term167.
Proof. exact (@lem6928900 term123 term123). Qed.
Lemma lem6928902 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928903 : term169 = term123.
Proof. exact (EQ_MP (@lem6928902) (@lem940073)). Qed.
Lemma lem6928904 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928905 : term167 = term122.
Proof. exact (MK_COMB (@lem6928904) (@lem6928903)). Qed.
Lemma lem6928906 : term166 = term122.
Proof. exact (TRANS (@lem6928901) (@lem6928905)). Qed.
Lemma lem6928908 (m : nat) (n : nat) : (term437 m n) = (term165 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem6928909 : term434 = term167.
Proof. exact (@lem6928908 term123 term123). Qed.
Lemma lem6928910 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6928911 : term169 = term123.
Proof. exact (EQ_MP (@lem6928910) (@lem940073)). Qed.
Lemma lem6928912 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6928913 : term167 = term122.
Proof. exact (MK_COMB (@lem6928912) (@lem6928911)). Qed.
Lemma lem6928914 : term434 = term122.
Proof. exact (TRANS (@lem6928909) (@lem6928913)). Qed.
Lemma lem6928915 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6928916 : term438 = term439.
Proof. exact (MK_COMB (@lem6928915) (@lem6928914)). Qed.
Lemma lem6928917 : term436 = term192.
Proof. exact (MK_COMB (@lem6928916) (@lem6928906)). Qed.
Lemma lem6928918 : term435 = term192.
Proof. exact (TRANS (@lem6928898) (@lem6928917)). Qed.
Lemma lem6928919 : term434 = term192.
Proof. exact (TRANS (@lem6928897) (@lem6928918)). Qed.
Lemma lem6928921 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6928922 : term192 = term122.
Proof. exact (@lem6928921 term122). Qed.
Lemma lem6928923 : term434 = term122.
Proof. exact (TRANS (@lem6928919) (@lem6928922)). Qed.
Lemma lem6928924 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6928925 : term440 = term441.
Proof. exact (MK_COMB (@lem6928924) (@lem6928923)). Qed.
Lemma lem6928926 (_92402 : int) : (real_of_int _92402) = (real_of_int _92402).
Proof. exact (eq_refl (real_of_int _92402)). Qed.
Lemma lem6928927 (_92402 : int) : (term433 _92402) = (term397 _92402).
Proof. exact (MK_COMB (@lem6928925) (@lem6928926 _92402)). Qed.
Lemma lem6928928 (_92402 : int) : (term432 _92402) = (term397 _92402).
Proof. exact (TRANS (@lem6928888 _92402) (@lem6928927 _92402)). Qed.
Lemma lem6928929 (_92402 : int) : (term397 _92402) = (real_of_int _92402).
Proof. exact (@lem1982709 (real_of_int _92402)). Qed.
Lemma lem6928930 (_92402 : int) : (term432 _92402) = (real_of_int _92402).
Proof. exact (TRANS (@lem6928928 _92402) (@lem6928929 _92402)). Qed.
Lemma lem6928931 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928932 (_92402 : int) : (term442 _92402) = (term124 _92402).
Proof. exact (MK_COMB (@lem6928931) (@lem6928930 _92402)). Qed.
Lemma lem6928933 (_92402 : int) (_92403 : int) : (term431 _92402 _92403) = (term216 _92402 _92403).
Proof. exact (MK_COMB (@lem6928932 _92402) (@lem6928887 _92403)). Qed.
Lemma lem6928934 (_92402 : int) (_92403 : int) : (term430 _92402 _92403) = (term216 _92402 _92403).
Proof. exact (TRANS (@lem6928886 _92402 _92403) (@lem6928933 _92402 _92403)). Qed.
Lemma lem6928937 (_92401 : int) : (term201 _92401) = (term201 _92401).
Proof. exact (eq_refl (term201 _92401)). Qed.
Lemma lem6928938 (_92401 : int) (_92402 : int) (_92403 : int) : (term472 _92401 _92402 _92403) = (term183 _92401 _92402 _92403).
Proof. exact (MK_COMB (@lem6928937 _92401) (@lem6928934 _92402 _92403)). Qed.
Lemma lem6928939 (_92401 : int) (_92402 : int) (_92403 : int) : (term471 _92401 _92402 _92403) = (term183 _92401 _92402 _92403).
Proof. exact (TRANS (@lem6928885 _92401 _92402 _92403) (@lem6928938 _92401 _92402 _92403)). Qed.
Lemma lem6928940 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6928941 (_92401 : int) (_92402 : int) (_92403 : int) : (term473 _92401 _92402 _92403) = (term186 _92401 _92402 _92403).
Proof. exact (MK_COMB (@lem6928940) (@lem6928939 _92401 _92402 _92403)). Qed.
Lemma lem6928942 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6928943 (_92401 : int) (_92402 : int) (_92403 : int) : ((term471 _92401 _92402 _92403) = term108) = ((term183 _92401 _92402 _92403) = term108).
Proof. exact (MK_COMB (@lem6928941 _92401 _92402 _92403) (@lem6928942)). Qed.
Lemma lem6928944 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : (term183 _92401 _92402 _92403) = term108.
Proof. exact (EQ_MP (@lem6928943 _92401 _92402 _92403) (@lem6928884 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928945 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term474 _92401 _92402 _92403.
Proof. exact (conj (@lem6928944 _92402 _92403 _92400 _92401 h1) (@lem6928877 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928947 (x : real) (y : real) : term370 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6928948 (_92401 : int) (_92402 : int) (_92403 : int) : term475 _92401 _92402 _92403.
Proof. exact (@lem6928947 (term183 _92401 _92402 _92403) (term204 _92402 _92403)). Qed.
Lemma lem6928949 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term476 _92401 _92402 _92403.
Proof. exact (@lem6928948 _92401 _92402 _92403 (@lem6928945 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6928950 (_92401 : int) (_92402 : int) (_92403 : int) : (term477 _92401 _92402 _92403) = (term478 _92401 _92402 _92403).
Proof. exact (@lem1982755 (term184 _92401) (term216 _92402 _92403) (term204 _92402 _92403)). Qed.
Lemma lem6928951 (_92402 : int) (_92403 : int) : (term448 _92402 _92403) = (term449 _92402 _92403).
Proof. exact (@lem1982753 (real_of_int _92402) (term184 _92402) (term184 _92403) (term450 _92403)). Qed.
Lemma lem6928952 (_92402 : int) : (term360 _92402) = (term340 _92402).
Proof. exact (@lem1982715 term157 (real_of_int _92402)). Qed.
Lemma lem6928954 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6928955 : term122 = term192.
Proof. exact (@lem6928954 term123). Qed.
Lemma lem6928957 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6928958 : term157 = term158.
Proof. exact (@lem6928957 term123). Qed.
Lemma lem6928959 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6928960 : term341 = term342.
Proof. exact (MK_COMB (@lem6928959) (@lem6928958)). Qed.
Lemma lem6928961 : term343 = term344.
Proof. exact (MK_COMB (@lem6928960) (@lem6928955)). Qed.
Lemma lem6928962 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6928964 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928965 : term300 = term306.
Proof. exact (@lem6928964 (NUMERAL 0) term123). Qed.
Lemma lem6928966 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928967 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928968 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928967 h1) (fun h1 : term306 = True => @lem6928966)). Qed.
Lemma lem6928969 : term306 = True.
Proof. exact (EQ_MP (@lem6928968) (@lem6928966)). Qed.
Lemma lem6928970 : term300 = True.
Proof. exact (TRANS (@lem6928965) (@lem6928969)). Qed.
Lemma lem6928971 : True = term300.
Proof. exact (SYM (@lem6928970)). Qed.
Lemma lem6928972 : term300.
Proof. exact (EQ_MP (@lem6928971) (@lem0)). Qed.
Lemma lem6928973 : term346.
Proof. exact (@lem6928962 (@lem6928972)). Qed.
Lemma lem6928975 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928976 : term300 = term306.
Proof. exact (@lem6928975 (NUMERAL 0) term123). Qed.
Lemma lem6928977 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928978 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928979 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928978 h1) (fun h1 : term306 = True => @lem6928977)). Qed.
Lemma lem6928980 : term306 = True.
Proof. exact (EQ_MP (@lem6928979) (@lem6928977)). Qed.
Lemma lem6928981 : term300 = True.
Proof. exact (TRANS (@lem6928976) (@lem6928980)). Qed.
Lemma lem6928982 : True = term300.
Proof. exact (SYM (@lem6928981)). Qed.
Lemma lem6928983 : term300.
Proof. exact (EQ_MP (@lem6928982) (@lem0)). Qed.
Lemma lem6928984 : term347.
Proof. exact (@lem6928973 (@lem6928983)). Qed.
Lemma lem6928986 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6928987 : term300 = term306.
Proof. exact (@lem6928986 (NUMERAL 0) term123). Qed.
Lemma lem6928988 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6928989 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6928990 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6928989 h1) (fun h1 : term306 = True => @lem6928988)). Qed.
Lemma lem6928991 : term306 = True.
Proof. exact (EQ_MP (@lem6928990) (@lem6928988)). Qed.
Lemma lem6928992 : term300 = True.
Proof. exact (TRANS (@lem6928987) (@lem6928991)). Qed.
Lemma lem6928993 : True = term300.
Proof. exact (SYM (@lem6928992)). Qed.
Lemma lem6928994 : term300.
Proof. exact (EQ_MP (@lem6928993) (@lem0)). Qed.
Lemma lem6928995 : term348.
Proof. exact (@lem6928984 (@lem6928994)). Qed.
Lemma lem6928997 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6928998 : term166 = term167.
Proof. exact (@lem6928997 term123 term123). Qed.
Lemma lem6928999 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929000 : term169 = term123.
Proof. exact (EQ_MP (@lem6928999) (@lem940073)). Qed.
Lemma lem6929001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929002 : term167 = term122.
Proof. exact (MK_COMB (@lem6929001) (@lem6929000)). Qed.
Lemma lem6929003 : term166 = term122.
Proof. exact (TRANS (@lem6928998) (@lem6929002)). Qed.
Lemma lem6929005 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6929006 : term193 = term198.
Proof. exact (@lem6929005 term123 term123). Qed.
Lemma lem6929007 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929008 : term169 = term123.
Proof. exact (EQ_MP (@lem6929007) (@lem940073)). Qed.
Lemma lem6929009 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929010 : term167 = term122.
Proof. exact (MK_COMB (@lem6929009) (@lem6929008)). Qed.
Lemma lem6929011 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6929012 : term198 = term157.
Proof. exact (MK_COMB (@lem6929011) (@lem6929010)). Qed.
Lemma lem6929013 : term193 = term157.
Proof. exact (TRANS (@lem6929006) (@lem6929012)). Qed.
Lemma lem6929014 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6929015 : term349 = term341.
Proof. exact (MK_COMB (@lem6929014) (@lem6929013)). Qed.
Lemma lem6929016 : term350 = term343.
Proof. exact (MK_COMB (@lem6929015) (@lem6929003)). Qed.
Lemma lem6929018 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6929019 : term343 = term108.
Proof. exact (@lem6929018 term123). Qed.
Lemma lem6929020 : term350 = term108.
Proof. exact (TRANS (@lem6929016) (@lem6929019)). Qed.
Lemma lem6929021 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6929022 : term352 = term353.
Proof. exact (MK_COMB (@lem6929021) (@lem6929020)). Qed.
Lemma lem6929023 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6929024 : term354 = term311.
Proof. exact (MK_COMB (@lem6929022) (@lem6929023)). Qed.
Lemma lem6929026 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6929027 : term311 = term108.
Proof. exact (@lem6929026 term123). Qed.
Lemma lem6929028 : term354 = term108.
Proof. exact (TRANS (@lem6929024) (@lem6929027)). Qed.
Lemma lem6929030 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6929031 : term166 = term167.
Proof. exact (@lem6929030 term123 term123). Qed.
Lemma lem6929032 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929033 : term169 = term123.
Proof. exact (EQ_MP (@lem6929032) (@lem940073)). Qed.
Lemma lem6929034 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929035 : term167 = term122.
Proof. exact (MK_COMB (@lem6929034) (@lem6929033)). Qed.
Lemma lem6929036 : term166 = term122.
Proof. exact (TRANS (@lem6929031) (@lem6929035)). Qed.
Lemma lem6929037 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6929038 : term355 = term311.
Proof. exact (MK_COMB (@lem6929037) (@lem6929036)). Qed.
Lemma lem6929040 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6929041 : term311 = term108.
Proof. exact (@lem6929040 term123). Qed.
Lemma lem6929042 : term355 = term108.
Proof. exact (TRANS (@lem6929038) (@lem6929041)). Qed.
Lemma lem6929043 : term108 = term355.
Proof. exact (SYM (@lem6929042)). Qed.
Lemma lem6929044 : term354 = term355.
Proof. exact (TRANS (@lem6929028) (@lem6929043)). Qed.
Lemma lem6929045 : term344 = term154.
Proof. exact (@lem6928995 (@lem6929044)). Qed.
Lemma lem6929046 : term343 = term154.
Proof. exact (TRANS (@lem6928961) (@lem6929045)). Qed.
Lemma lem6929048 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6929049 : term154 = term108.
Proof. exact (@lem6929048 term108). Qed.
Lemma lem6929050 : term343 = term108.
Proof. exact (TRANS (@lem6929046) (@lem6929049)). Qed.
Lemma lem6929051 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6929052 : term356 = term353.
Proof. exact (MK_COMB (@lem6929051) (@lem6929050)). Qed.
Lemma lem6929053 (_92402 : int) : (real_of_int _92402) = (real_of_int _92402).
Proof. exact (eq_refl (real_of_int _92402)). Qed.
Lemma lem6929054 (_92402 : int) : (term340 _92402) = (term357 _92402).
Proof. exact (MK_COMB (@lem6929052) (@lem6929053 _92402)). Qed.
Lemma lem6929055 (_92402 : int) : (term360 _92402) = (term357 _92402).
Proof. exact (TRANS (@lem6928952 _92402) (@lem6929054 _92402)). Qed.
Lemma lem6929056 (_92402 : int) : (term357 _92402) = term108.
Proof. exact (@lem1982719 (real_of_int _92402)). Qed.
Lemma lem6929057 (_92402 : int) : (term360 _92402) = term108.
Proof. exact (TRANS (@lem6929055 _92402) (@lem6929056 _92402)). Qed.
Lemma lem6929058 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6929059 (_92402 : int) : (term377 _92402) = term359.
Proof. exact (MK_COMB (@lem6929058) (@lem6929057 _92402)). Qed.
Lemma lem6929060 (_92403 : int) : (term451 _92403) = (term421 _92403).
Proof. exact (@lem1982763 (term184 _92403) (real_of_int _92403) term157). Qed.
Lemma lem6929061 (_92403 : int) : (term339 _92403) = (term340 _92403).
Proof. exact (@lem1982713 term157 (real_of_int _92403)). Qed.
Lemma lem6929063 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6929064 : term122 = term192.
Proof. exact (@lem6929063 term123). Qed.
Lemma lem6929066 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6929067 : term157 = term158.
Proof. exact (@lem6929066 term123). Qed.
Lemma lem6929068 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6929069 : term341 = term342.
Proof. exact (MK_COMB (@lem6929068) (@lem6929067)). Qed.
Lemma lem6929070 : term343 = term344.
Proof. exact (MK_COMB (@lem6929069) (@lem6929064)). Qed.
Lemma lem6929071 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6929073 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929074 : term300 = term306.
Proof. exact (@lem6929073 (NUMERAL 0) term123). Qed.
Lemma lem6929075 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929076 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929077 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929076 h1) (fun h1 : term306 = True => @lem6929075)). Qed.
Lemma lem6929078 : term306 = True.
Proof. exact (EQ_MP (@lem6929077) (@lem6929075)). Qed.
Lemma lem6929079 : term300 = True.
Proof. exact (TRANS (@lem6929074) (@lem6929078)). Qed.
Lemma lem6929080 : True = term300.
Proof. exact (SYM (@lem6929079)). Qed.
Lemma lem6929081 : term300.
Proof. exact (EQ_MP (@lem6929080) (@lem0)). Qed.
Lemma lem6929082 : term346.
Proof. exact (@lem6929071 (@lem6929081)). Qed.
Lemma lem6929084 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929085 : term300 = term306.
Proof. exact (@lem6929084 (NUMERAL 0) term123). Qed.
Lemma lem6929086 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929087 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929088 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929087 h1) (fun h1 : term306 = True => @lem6929086)). Qed.
Lemma lem6929089 : term306 = True.
Proof. exact (EQ_MP (@lem6929088) (@lem6929086)). Qed.
Lemma lem6929090 : term300 = True.
Proof. exact (TRANS (@lem6929085) (@lem6929089)). Qed.
Lemma lem6929091 : True = term300.
Proof. exact (SYM (@lem6929090)). Qed.
Lemma lem6929092 : term300.
Proof. exact (EQ_MP (@lem6929091) (@lem0)). Qed.
Lemma lem6929093 : term347.
Proof. exact (@lem6929082 (@lem6929092)). Qed.
Lemma lem6929095 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929096 : term300 = term306.
Proof. exact (@lem6929095 (NUMERAL 0) term123). Qed.
Lemma lem6929097 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929098 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929099 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929098 h1) (fun h1 : term306 = True => @lem6929097)). Qed.
Lemma lem6929100 : term306 = True.
Proof. exact (EQ_MP (@lem6929099) (@lem6929097)). Qed.
Lemma lem6929101 : term300 = True.
Proof. exact (TRANS (@lem6929096) (@lem6929100)). Qed.
Lemma lem6929102 : True = term300.
Proof. exact (SYM (@lem6929101)). Qed.
Lemma lem6929103 : term300.
Proof. exact (EQ_MP (@lem6929102) (@lem0)). Qed.
Lemma lem6929104 : term348.
Proof. exact (@lem6929093 (@lem6929103)). Qed.
Lemma lem6929106 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6929107 : term166 = term167.
Proof. exact (@lem6929106 term123 term123). Qed.
Lemma lem6929108 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929109 : term169 = term123.
Proof. exact (EQ_MP (@lem6929108) (@lem940073)). Qed.
Lemma lem6929110 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929111 : term167 = term122.
Proof. exact (MK_COMB (@lem6929110) (@lem6929109)). Qed.
Lemma lem6929112 : term166 = term122.
Proof. exact (TRANS (@lem6929107) (@lem6929111)). Qed.
Lemma lem6929114 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6929115 : term193 = term198.
Proof. exact (@lem6929114 term123 term123). Qed.
Lemma lem6929116 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929117 : term169 = term123.
Proof. exact (EQ_MP (@lem6929116) (@lem940073)). Qed.
Lemma lem6929118 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929119 : term167 = term122.
Proof. exact (MK_COMB (@lem6929118) (@lem6929117)). Qed.
Lemma lem6929120 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6929121 : term198 = term157.
Proof. exact (MK_COMB (@lem6929120) (@lem6929119)). Qed.
Lemma lem6929122 : term193 = term157.
Proof. exact (TRANS (@lem6929115) (@lem6929121)). Qed.
Lemma lem6929123 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6929124 : term349 = term341.
Proof. exact (MK_COMB (@lem6929123) (@lem6929122)). Qed.
Lemma lem6929125 : term350 = term343.
Proof. exact (MK_COMB (@lem6929124) (@lem6929112)). Qed.
Lemma lem6929127 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6929128 : term343 = term108.
Proof. exact (@lem6929127 term123). Qed.
Lemma lem6929129 : term350 = term108.
Proof. exact (TRANS (@lem6929125) (@lem6929128)). Qed.
Lemma lem6929130 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6929131 : term352 = term353.
Proof. exact (MK_COMB (@lem6929130) (@lem6929129)). Qed.
Lemma lem6929132 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6929133 : term354 = term311.
Proof. exact (MK_COMB (@lem6929131) (@lem6929132)). Qed.
Lemma lem6929135 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6929136 : term311 = term108.
Proof. exact (@lem6929135 term123). Qed.
Lemma lem6929137 : term354 = term108.
Proof. exact (TRANS (@lem6929133) (@lem6929136)). Qed.
Lemma lem6929139 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6929140 : term166 = term167.
Proof. exact (@lem6929139 term123 term123). Qed.
Lemma lem6929141 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929142 : term169 = term123.
Proof. exact (EQ_MP (@lem6929141) (@lem940073)). Qed.
Lemma lem6929143 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929144 : term167 = term122.
Proof. exact (MK_COMB (@lem6929143) (@lem6929142)). Qed.
Lemma lem6929145 : term166 = term122.
Proof. exact (TRANS (@lem6929140) (@lem6929144)). Qed.
Lemma lem6929146 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6929147 : term355 = term311.
Proof. exact (MK_COMB (@lem6929146) (@lem6929145)). Qed.
Lemma lem6929149 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6929150 : term311 = term108.
Proof. exact (@lem6929149 term123). Qed.
Lemma lem6929151 : term355 = term108.
Proof. exact (TRANS (@lem6929147) (@lem6929150)). Qed.
Lemma lem6929152 : term108 = term355.
Proof. exact (SYM (@lem6929151)). Qed.
Lemma lem6929153 : term354 = term355.
Proof. exact (TRANS (@lem6929137) (@lem6929152)). Qed.
Lemma lem6929154 : term344 = term154.
Proof. exact (@lem6929104 (@lem6929153)). Qed.
Lemma lem6929155 : term343 = term154.
Proof. exact (TRANS (@lem6929070) (@lem6929154)). Qed.
Lemma lem6929157 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6929158 : term154 = term108.
Proof. exact (@lem6929157 term108). Qed.
Lemma lem6929159 : term343 = term108.
Proof. exact (TRANS (@lem6929155) (@lem6929158)). Qed.
Lemma lem6929160 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6929161 : term356 = term353.
Proof. exact (MK_COMB (@lem6929160) (@lem6929159)). Qed.
Lemma lem6929162 (_92403 : int) : (real_of_int _92403) = (real_of_int _92403).
Proof. exact (eq_refl (real_of_int _92403)). Qed.
Lemma lem6929163 (_92403 : int) : (term340 _92403) = (term357 _92403).
Proof. exact (MK_COMB (@lem6929161) (@lem6929162 _92403)). Qed.
Lemma lem6929164 (_92403 : int) : (term339 _92403) = (term357 _92403).
Proof. exact (TRANS (@lem6929061 _92403) (@lem6929163 _92403)). Qed.
Lemma lem6929165 (_92403 : int) : (term357 _92403) = term108.
Proof. exact (@lem1982719 (real_of_int _92403)). Qed.
Lemma lem6929166 (_92403 : int) : (term339 _92403) = term108.
Proof. exact (TRANS (@lem6929164 _92403) (@lem6929165 _92403)). Qed.
Lemma lem6929167 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6929168 (_92403 : int) : (term358 _92403) = term359.
Proof. exact (MK_COMB (@lem6929167) (@lem6929166 _92403)). Qed.
Lemma lem6929169 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem6929170 (_92403 : int) : (term421 _92403) = term378.
Proof. exact (MK_COMB (@lem6929168 _92403) (@lem6929169)). Qed.
Lemma lem6929171 (_92403 : int) : (term451 _92403) = term378.
Proof. exact (TRANS (@lem6929060 _92403) (@lem6929170 _92403)). Qed.
Lemma lem6929172 : term378 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem6929173 (_92403 : int) : (term451 _92403) = term157.
Proof. exact (TRANS (@lem6929171 _92403) (@lem6929172)). Qed.
Lemma lem6929174 (_92402 : int) (_92403 : int) : (term449 _92402 _92403) = term378.
Proof. exact (MK_COMB (@lem6929059 _92402) (@lem6929173 _92403)). Qed.
Lemma lem6929175 (_92402 : int) (_92403 : int) : (term448 _92402 _92403) = term378.
Proof. exact (TRANS (@lem6928951 _92402 _92403) (@lem6929174 _92402 _92403)). Qed.
Lemma lem6929176 : term378 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem6929177 (_92402 : int) (_92403 : int) : (term448 _92402 _92403) = term157.
Proof. exact (TRANS (@lem6929175 _92402 _92403) (@lem6929176)). Qed.
Lemma lem6929178 (_92401 : int) : (term201 _92401) = (term201 _92401).
Proof. exact (eq_refl (term201 _92401)). Qed.
Lemma lem6929179 (_92402 : int) (_92403 : int) (_92401 : int) : (term478 _92401 _92402 _92403) = (term202 _92401).
Proof. exact (MK_COMB (@lem6929178 _92401) (@lem6929177 _92402 _92403)). Qed.
Lemma lem6929180 (_92402 : int) (_92403 : int) (_92401 : int) : (term477 _92401 _92402 _92403) = (term202 _92401).
Proof. exact (TRANS (@lem6928950 _92401 _92402 _92403) (@lem6929179 _92402 _92403 _92401)). Qed.
Lemma lem6929181 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6929182 (_92402 : int) (_92403 : int) (_92401 : int) : (term479 _92401 _92402 _92403) = (term409 _92401).
Proof. exact (MK_COMB (@lem6929181) (@lem6929180 _92402 _92403 _92401)). Qed.
Lemma lem6929183 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6929184 (_92402 : int) (_92403 : int) (_92401 : int) : (term476 _92401 _92402 _92403) = (term410 _92401).
Proof. exact (MK_COMB (@lem6929182 _92402 _92403 _92401) (@lem6929183)). Qed.
Lemma lem6929185 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term410 _92401.
Proof. exact (EQ_MP (@lem6929184 _92402 _92403 _92401) (@lem6928949 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6929187 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6929188 : term299 = term300.
Proof. exact (@lem6929187 term108 term122). Qed.
Lemma lem6929190 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6929191 : term122 = term192.
Proof. exact (@lem6929190 term123). Qed.
Lemma lem6929193 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6929194 : term108 = term154.
Proof. exact (@lem6929193 (NUMERAL 0)). Qed.
Lemma lem6929195 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6929196 : term301 = term302.
Proof. exact (MK_COMB (@lem6929195) (@lem6929194)). Qed.
Lemma lem6929197 : term300 = term303.
Proof. exact (MK_COMB (@lem6929196) (@lem6929191)). Qed.
Lemma lem6929198 : term304.
Proof. exact (@lem1980255 term108 term122 term122 term122). Qed.
Lemma lem6929200 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929201 : term300 = term306.
Proof. exact (@lem6929200 (NUMERAL 0) term123). Qed.
Lemma lem6929202 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929203 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929204 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929203 h1) (fun h1 : term306 = True => @lem6929202)). Qed.
Lemma lem6929205 : term306 = True.
Proof. exact (EQ_MP (@lem6929204) (@lem6929202)). Qed.
Lemma lem6929206 : term300 = True.
Proof. exact (TRANS (@lem6929201) (@lem6929205)). Qed.
Lemma lem6929207 : True = term300.
Proof. exact (SYM (@lem6929206)). Qed.
Lemma lem6929208 : term300.
Proof. exact (EQ_MP (@lem6929207) (@lem0)). Qed.
Lemma lem6929209 : term308.
Proof. exact (@lem6929198 (@lem6929208)). Qed.
Lemma lem6929211 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929212 : term300 = term306.
Proof. exact (@lem6929211 (NUMERAL 0) term123). Qed.
Lemma lem6929213 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929214 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929215 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929214 h1) (fun h1 : term306 = True => @lem6929213)). Qed.
Lemma lem6929216 : term306 = True.
Proof. exact (EQ_MP (@lem6929215) (@lem6929213)). Qed.
Lemma lem6929217 : term300 = True.
Proof. exact (TRANS (@lem6929212) (@lem6929216)). Qed.
Lemma lem6929218 : True = term300.
Proof. exact (SYM (@lem6929217)). Qed.
Lemma lem6929219 : term300.
Proof. exact (EQ_MP (@lem6929218) (@lem0)). Qed.
Lemma lem6929220 : term303 = term309.
Proof. exact (@lem6929209 (@lem6929219)). Qed.
Lemma lem6929222 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6929223 : term166 = term167.
Proof. exact (@lem6929222 term123 term123). Qed.
Lemma lem6929224 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929225 : term169 = term123.
Proof. exact (EQ_MP (@lem6929224) (@lem940073)). Qed.
Lemma lem6929226 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929227 : term167 = term122.
Proof. exact (MK_COMB (@lem6929226) (@lem6929225)). Qed.
Lemma lem6929228 : term166 = term122.
Proof. exact (TRANS (@lem6929223) (@lem6929227)). Qed.
Lemma lem6929230 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6929231 : term311 = term108.
Proof. exact (@lem6929230 term123). Qed.
Lemma lem6929232 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6929233 : term312 = term301.
Proof. exact (MK_COMB (@lem6929232) (@lem6929231)). Qed.
Lemma lem6929234 : term309 = term300.
Proof. exact (MK_COMB (@lem6929233) (@lem6929228)). Qed.
Lemma lem6929236 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929237 : term300 = term306.
Proof. exact (@lem6929236 (NUMERAL 0) term123). Qed.
Lemma lem6929238 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929239 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929240 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929239 h1) (fun h1 : term306 = True => @lem6929238)). Qed.
Lemma lem6929241 : term306 = True.
Proof. exact (EQ_MP (@lem6929240) (@lem6929238)). Qed.
Lemma lem6929242 : term300 = True.
Proof. exact (TRANS (@lem6929237) (@lem6929241)). Qed.
Lemma lem6929243 : term309 = True.
Proof. exact (TRANS (@lem6929234) (@lem6929242)). Qed.
Lemma lem6929244 : term303 = True.
Proof. exact (TRANS (@lem6929220) (@lem6929243)). Qed.
Lemma lem6929245 : term300 = True.
Proof. exact (TRANS (@lem6929197) (@lem6929244)). Qed.
Lemma lem6929246 : term299 = True.
Proof. exact (TRANS (@lem6929188) (@lem6929245)). Qed.
Lemma lem6929247 : True = term299.
Proof. exact (SYM (@lem6929246)). Qed.
Lemma lem6929248 : term299.
Proof. exact (EQ_MP (@lem6929247) (@lem0)). Qed.
Lemma lem6929249 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term411 _92401.
Proof. exact (conj (@lem6929248) (@lem6929185 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6929251 (x : real) (y : real) : term314 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6929252 (_92401 : int) : term412 _92401.
Proof. exact (@lem6929251 term122 (term202 _92401)). Qed.
Lemma lem6929253 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term413 _92401.
Proof. exact (@lem6929252 _92401 (@lem6929249 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6929254 (_92401 : int) : (term414 _92401) = (term202 _92401).
Proof. exact (@lem1982733 (term202 _92401)). Qed.
Lemma lem6929255 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6929256 (_92401 : int) : (term415 _92401) = (term409 _92401).
Proof. exact (MK_COMB (@lem6929255) (@lem6929254 _92401)). Qed.
Lemma lem6929257 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6929258 (_92401 : int) : (term413 _92401) = (term410 _92401).
Proof. exact (MK_COMB (@lem6929256 _92401) (@lem6929257)). Qed.
Lemma lem6929259 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term410 _92401.
Proof. exact (EQ_MP (@lem6929258 _92401) (@lem6929253 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6929260 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term480 _92401.
Proof. exact (conj (@lem6929259 _92402 _92403 _92400 _92401 h1) (@lem6928803 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6929262 (x : real) (y : real) : term417 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6929263 (_92401 : int) : term481 _92401.
Proof. exact (@lem6929262 (term202 _92401) (term450 _92401)). Qed.
Lemma lem6929264 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term482 _92401.
Proof. exact (@lem6929263 _92401 (@lem6929260 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6929265 (_92401 : int) : (term483 _92401) = (term484 _92401).
Proof. exact (@lem1982753 (term184 _92401) (real_of_int _92401) term157 term157). Qed.
Lemma lem6929266 (_92401 : int) : (term339 _92401) = (term340 _92401).
Proof. exact (@lem1982713 term157 (real_of_int _92401)). Qed.
Lemma lem6929268 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6929269 : term122 = term192.
Proof. exact (@lem6929268 term123). Qed.
Lemma lem6929271 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6929272 : term157 = term158.
Proof. exact (@lem6929271 term123). Qed.
Lemma lem6929273 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6929274 : term341 = term342.
Proof. exact (MK_COMB (@lem6929273) (@lem6929272)). Qed.
Lemma lem6929275 : term343 = term344.
Proof. exact (MK_COMB (@lem6929274) (@lem6929269)). Qed.
Lemma lem6929276 : term345.
Proof. exact (@lem1981473 term157 term122 term122 term122 term108 term122). Qed.
Lemma lem6929278 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929279 : term300 = term306.
Proof. exact (@lem6929278 (NUMERAL 0) term123). Qed.
Lemma lem6929280 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929281 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929282 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929281 h1) (fun h1 : term306 = True => @lem6929280)). Qed.
Lemma lem6929283 : term306 = True.
Proof. exact (EQ_MP (@lem6929282) (@lem6929280)). Qed.
Lemma lem6929284 : term300 = True.
Proof. exact (TRANS (@lem6929279) (@lem6929283)). Qed.
Lemma lem6929285 : True = term300.
Proof. exact (SYM (@lem6929284)). Qed.
Lemma lem6929286 : term300.
Proof. exact (EQ_MP (@lem6929285) (@lem0)). Qed.
Lemma lem6929287 : term346.
Proof. exact (@lem6929276 (@lem6929286)). Qed.
Lemma lem6929289 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929290 : term300 = term306.
Proof. exact (@lem6929289 (NUMERAL 0) term123). Qed.
Lemma lem6929291 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929292 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929293 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929292 h1) (fun h1 : term306 = True => @lem6929291)). Qed.
Lemma lem6929294 : term306 = True.
Proof. exact (EQ_MP (@lem6929293) (@lem6929291)). Qed.
Lemma lem6929295 : term300 = True.
Proof. exact (TRANS (@lem6929290) (@lem6929294)). Qed.
Lemma lem6929296 : True = term300.
Proof. exact (SYM (@lem6929295)). Qed.
Lemma lem6929297 : term300.
Proof. exact (EQ_MP (@lem6929296) (@lem0)). Qed.
Lemma lem6929298 : term347.
Proof. exact (@lem6929287 (@lem6929297)). Qed.
Lemma lem6929300 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929301 : term300 = term306.
Proof. exact (@lem6929300 (NUMERAL 0) term123). Qed.
Lemma lem6929302 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929303 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929304 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929303 h1) (fun h1 : term306 = True => @lem6929302)). Qed.
Lemma lem6929305 : term306 = True.
Proof. exact (EQ_MP (@lem6929304) (@lem6929302)). Qed.
Lemma lem6929306 : term300 = True.
Proof. exact (TRANS (@lem6929301) (@lem6929305)). Qed.
Lemma lem6929307 : True = term300.
Proof. exact (SYM (@lem6929306)). Qed.
Lemma lem6929308 : term300.
Proof. exact (EQ_MP (@lem6929307) (@lem0)). Qed.
Lemma lem6929309 : term348.
Proof. exact (@lem6929298 (@lem6929308)). Qed.
Lemma lem6929311 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6929312 : term166 = term167.
Proof. exact (@lem6929311 term123 term123). Qed.
Lemma lem6929313 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929314 : term169 = term123.
Proof. exact (EQ_MP (@lem6929313) (@lem940073)). Qed.
Lemma lem6929315 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929316 : term167 = term122.
Proof. exact (MK_COMB (@lem6929315) (@lem6929314)). Qed.
Lemma lem6929317 : term166 = term122.
Proof. exact (TRANS (@lem6929312) (@lem6929316)). Qed.
Lemma lem6929319 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6929320 : term193 = term198.
Proof. exact (@lem6929319 term123 term123). Qed.
Lemma lem6929321 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929322 : term169 = term123.
Proof. exact (EQ_MP (@lem6929321) (@lem940073)). Qed.
Lemma lem6929323 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929324 : term167 = term122.
Proof. exact (MK_COMB (@lem6929323) (@lem6929322)). Qed.
Lemma lem6929325 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6929326 : term198 = term157.
Proof. exact (MK_COMB (@lem6929325) (@lem6929324)). Qed.
Lemma lem6929327 : term193 = term157.
Proof. exact (TRANS (@lem6929320) (@lem6929326)). Qed.
Lemma lem6929328 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6929329 : term349 = term341.
Proof. exact (MK_COMB (@lem6929328) (@lem6929327)). Qed.
Lemma lem6929330 : term350 = term343.
Proof. exact (MK_COMB (@lem6929329) (@lem6929317)). Qed.
Lemma lem6929332 (m : nat) : (term351 m) = term108.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6929333 : term343 = term108.
Proof. exact (@lem6929332 term123). Qed.
Lemma lem6929334 : term350 = term108.
Proof. exact (TRANS (@lem6929330) (@lem6929333)). Qed.
Lemma lem6929335 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6929336 : term352 = term353.
Proof. exact (MK_COMB (@lem6929335) (@lem6929334)). Qed.
Lemma lem6929337 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6929338 : term354 = term311.
Proof. exact (MK_COMB (@lem6929336) (@lem6929337)). Qed.
Lemma lem6929340 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6929341 : term311 = term108.
Proof. exact (@lem6929340 term123). Qed.
Lemma lem6929342 : term354 = term108.
Proof. exact (TRANS (@lem6929338) (@lem6929341)). Qed.
Lemma lem6929344 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6929345 : term166 = term167.
Proof. exact (@lem6929344 term123 term123). Qed.
Lemma lem6929346 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929347 : term169 = term123.
Proof. exact (EQ_MP (@lem6929346) (@lem940073)). Qed.
Lemma lem6929348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929349 : term167 = term122.
Proof. exact (MK_COMB (@lem6929348) (@lem6929347)). Qed.
Lemma lem6929350 : term166 = term122.
Proof. exact (TRANS (@lem6929345) (@lem6929349)). Qed.
Lemma lem6929351 : term353 = term353.
Proof. exact (eq_refl term353). Qed.
Lemma lem6929352 : term355 = term311.
Proof. exact (MK_COMB (@lem6929351) (@lem6929350)). Qed.
Lemma lem6929354 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6929355 : term311 = term108.
Proof. exact (@lem6929354 term123). Qed.
Lemma lem6929356 : term355 = term108.
Proof. exact (TRANS (@lem6929352) (@lem6929355)). Qed.
Lemma lem6929357 : term108 = term355.
Proof. exact (SYM (@lem6929356)). Qed.
Lemma lem6929358 : term354 = term355.
Proof. exact (TRANS (@lem6929342) (@lem6929357)). Qed.
Lemma lem6929359 : term344 = term154.
Proof. exact (@lem6929309 (@lem6929358)). Qed.
Lemma lem6929360 : term343 = term154.
Proof. exact (TRANS (@lem6929275) (@lem6929359)). Qed.
Lemma lem6929362 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6929363 : term154 = term108.
Proof. exact (@lem6929362 term108). Qed.
Lemma lem6929364 : term343 = term108.
Proof. exact (TRANS (@lem6929360) (@lem6929363)). Qed.
Lemma lem6929365 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6929366 : term356 = term353.
Proof. exact (MK_COMB (@lem6929365) (@lem6929364)). Qed.
Lemma lem6929367 (_92401 : int) : (real_of_int _92401) = (real_of_int _92401).
Proof. exact (eq_refl (real_of_int _92401)). Qed.
Lemma lem6929368 (_92401 : int) : (term340 _92401) = (term357 _92401).
Proof. exact (MK_COMB (@lem6929366) (@lem6929367 _92401)). Qed.
Lemma lem6929369 (_92401 : int) : (term339 _92401) = (term357 _92401).
Proof. exact (TRANS (@lem6929266 _92401) (@lem6929368 _92401)). Qed.
Lemma lem6929370 (_92401 : int) : (term357 _92401) = term108.
Proof. exact (@lem1982719 (real_of_int _92401)). Qed.
Lemma lem6929371 (_92401 : int) : (term339 _92401) = term108.
Proof. exact (TRANS (@lem6929369 _92401) (@lem6929370 _92401)). Qed.
Lemma lem6929372 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6929373 (_92401 : int) : (term358 _92401) = term359.
Proof. exact (MK_COMB (@lem6929372) (@lem6929371 _92401)). Qed.
Lemma lem6929375 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6929376 : term157 = term158.
Proof. exact (@lem6929375 term123). Qed.
Lemma lem6929378 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6929379 : term157 = term158.
Proof. exact (@lem6929378 term123). Qed.
Lemma lem6929380 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6929381 : term341 = term342.
Proof. exact (MK_COMB (@lem6929380) (@lem6929379)). Qed.
Lemma lem6929382 : term485 = term486.
Proof. exact (MK_COMB (@lem6929381) (@lem6929376)). Qed.
Lemma lem6929383 : term487.
Proof. exact (@lem1981473 term157 term122 term157 term122 term488 term122). Qed.
Lemma lem6929385 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929386 : term300 = term306.
Proof. exact (@lem6929385 (NUMERAL 0) term123). Qed.
Lemma lem6929387 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929388 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929389 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929388 h1) (fun h1 : term306 = True => @lem6929387)). Qed.
Lemma lem6929390 : term306 = True.
Proof. exact (EQ_MP (@lem6929389) (@lem6929387)). Qed.
Lemma lem6929391 : term300 = True.
Proof. exact (TRANS (@lem6929386) (@lem6929390)). Qed.
Lemma lem6929392 : True = term300.
Proof. exact (SYM (@lem6929391)). Qed.
Lemma lem6929393 : term300.
Proof. exact (EQ_MP (@lem6929392) (@lem0)). Qed.
Lemma lem6929394 : term489.
Proof. exact (@lem6929383 (@lem6929393)). Qed.
Lemma lem6929396 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929397 : term300 = term306.
Proof. exact (@lem6929396 (NUMERAL 0) term123). Qed.
Lemma lem6929398 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929399 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929400 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929399 h1) (fun h1 : term306 = True => @lem6929398)). Qed.
Lemma lem6929401 : term306 = True.
Proof. exact (EQ_MP (@lem6929400) (@lem6929398)). Qed.
Lemma lem6929402 : term300 = True.
Proof. exact (TRANS (@lem6929397) (@lem6929401)). Qed.
Lemma lem6929403 : True = term300.
Proof. exact (SYM (@lem6929402)). Qed.
Lemma lem6929404 : term300.
Proof. exact (EQ_MP (@lem6929403) (@lem0)). Qed.
Lemma lem6929405 : term490.
Proof. exact (@lem6929394 (@lem6929404)). Qed.
Lemma lem6929407 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929408 : term300 = term306.
Proof. exact (@lem6929407 (NUMERAL 0) term123). Qed.
Lemma lem6929409 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929410 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929411 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929410 h1) (fun h1 : term306 = True => @lem6929409)). Qed.
Lemma lem6929412 : term306 = True.
Proof. exact (EQ_MP (@lem6929411) (@lem6929409)). Qed.
Lemma lem6929413 : term300 = True.
Proof. exact (TRANS (@lem6929408) (@lem6929412)). Qed.
Lemma lem6929414 : True = term300.
Proof. exact (SYM (@lem6929413)). Qed.
Lemma lem6929415 : term300.
Proof. exact (EQ_MP (@lem6929414) (@lem0)). Qed.
Lemma lem6929416 : term491.
Proof. exact (@lem6929405 (@lem6929415)). Qed.
Lemma lem6929418 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6929419 : term193 = term198.
Proof. exact (@lem6929418 term123 term123). Qed.
Lemma lem6929420 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929421 : term169 = term123.
Proof. exact (EQ_MP (@lem6929420) (@lem940073)). Qed.
Lemma lem6929422 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929423 : term167 = term122.
Proof. exact (MK_COMB (@lem6929422) (@lem6929421)). Qed.
Lemma lem6929424 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6929425 : term198 = term157.
Proof. exact (MK_COMB (@lem6929424) (@lem6929423)). Qed.
Lemma lem6929426 : term193 = term157.
Proof. exact (TRANS (@lem6929419) (@lem6929425)). Qed.
Lemma lem6929428 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6929429 : term193 = term198.
Proof. exact (@lem6929428 term123 term123). Qed.
Lemma lem6929430 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929431 : term169 = term123.
Proof. exact (EQ_MP (@lem6929430) (@lem940073)). Qed.
Lemma lem6929432 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929433 : term167 = term122.
Proof. exact (MK_COMB (@lem6929432) (@lem6929431)). Qed.
Lemma lem6929434 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6929435 : term198 = term157.
Proof. exact (MK_COMB (@lem6929434) (@lem6929433)). Qed.
Lemma lem6929436 : term193 = term157.
Proof. exact (TRANS (@lem6929429) (@lem6929435)). Qed.
Lemma lem6929437 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6929438 : term349 = term341.
Proof. exact (MK_COMB (@lem6929437) (@lem6929436)). Qed.
Lemma lem6929439 : term492 = term485.
Proof. exact (MK_COMB (@lem6929438) (@lem6929426)). Qed.
Lemma lem6929440 : term485 = term493.
Proof. exact (@lem1367763 term123 term123). Qed.
Lemma lem6929441 : term494 = term495.
Proof. exact (@lem706885). Qed.
Lemma lem6929442 : (term494 = term495) = (term496 = term497).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term495). Qed.
Lemma lem6929443 : term496 = term497.
Proof. exact (EQ_MP (@lem6929442) (@lem6929441)). Qed.
Lemma lem6929444 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929445 : term498 = term499.
Proof. exact (MK_COMB (@lem6929444) (@lem6929443)). Qed.
Lemma lem6929446 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6929447 : term493 = term488.
Proof. exact (MK_COMB (@lem6929446) (@lem6929445)). Qed.
Lemma lem6929448 : term485 = term488.
Proof. exact (TRANS (@lem6929440) (@lem6929447)). Qed.
Lemma lem6929449 : term492 = term488.
Proof. exact (TRANS (@lem6929439) (@lem6929448)). Qed.
Lemma lem6929450 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6929451 : term500 = term501.
Proof. exact (MK_COMB (@lem6929450) (@lem6929449)). Qed.
Lemma lem6929452 : term122 = term122.
Proof. exact (eq_refl term122). Qed.
Lemma lem6929453 : term502 = term503.
Proof. exact (MK_COMB (@lem6929451) (@lem6929452)). Qed.
Lemma lem6929455 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6929456 : term503 = term504.
Proof. exact (@lem6929455 term497 term123). Qed.
Lemma lem6929457 : term505 = term495.
Proof. exact (@lem996237 term495). Qed.
Lemma lem6929458 : (term505 = term495) = (term506 = term497).
Proof. exact (@lem1007663 term495 (BIT1 0) term495). Qed.
Lemma lem6929459 : term506 = term497.
Proof. exact (EQ_MP (@lem6929458) (@lem6929457)). Qed.
Lemma lem6929460 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929461 : term507 = term499.
Proof. exact (MK_COMB (@lem6929460) (@lem6929459)). Qed.
Lemma lem6929462 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6929463 : term504 = term488.
Proof. exact (MK_COMB (@lem6929462) (@lem6929461)). Qed.
Lemma lem6929464 : term503 = term488.
Proof. exact (TRANS (@lem6929456) (@lem6929463)). Qed.
Lemma lem6929465 : term502 = term488.
Proof. exact (TRANS (@lem6929453) (@lem6929464)). Qed.
Lemma lem6929467 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6929468 : term166 = term167.
Proof. exact (@lem6929467 term123 term123). Qed.
Lemma lem6929469 : (term168 = (BIT1 0)) = (term169 = term123).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6929470 : term169 = term123.
Proof. exact (EQ_MP (@lem6929469) (@lem940073)). Qed.
Lemma lem6929471 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929472 : term167 = term122.
Proof. exact (MK_COMB (@lem6929471) (@lem6929470)). Qed.
Lemma lem6929473 : term166 = term122.
Proof. exact (TRANS (@lem6929468) (@lem6929472)). Qed.
Lemma lem6929474 : term501 = term501.
Proof. exact (eq_refl term501). Qed.
Lemma lem6929475 : term508 = term503.
Proof. exact (MK_COMB (@lem6929474) (@lem6929473)). Qed.
Lemma lem6929477 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6929478 : term503 = term504.
Proof. exact (@lem6929477 term497 term123). Qed.
Lemma lem6929479 : term505 = term495.
Proof. exact (@lem996237 term495). Qed.
Lemma lem6929480 : (term505 = term495) = (term506 = term497).
Proof. exact (@lem1007663 term495 (BIT1 0) term495). Qed.
Lemma lem6929481 : term506 = term497.
Proof. exact (EQ_MP (@lem6929480) (@lem6929479)). Qed.
Lemma lem6929482 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929483 : term507 = term499.
Proof. exact (MK_COMB (@lem6929482) (@lem6929481)). Qed.
Lemma lem6929484 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6929485 : term504 = term488.
Proof. exact (MK_COMB (@lem6929484) (@lem6929483)). Qed.
Lemma lem6929486 : term503 = term488.
Proof. exact (TRANS (@lem6929478) (@lem6929485)). Qed.
Lemma lem6929487 : term508 = term488.
Proof. exact (TRANS (@lem6929475) (@lem6929486)). Qed.
Lemma lem6929488 : term488 = term508.
Proof. exact (SYM (@lem6929487)). Qed.
Lemma lem6929489 : term502 = term508.
Proof. exact (TRANS (@lem6929465) (@lem6929488)). Qed.
Lemma lem6929490 : term486 = term509.
Proof. exact (@lem6929416 (@lem6929489)). Qed.
Lemma lem6929491 : term485 = term509.
Proof. exact (TRANS (@lem6929382) (@lem6929490)). Qed.
Lemma lem6929493 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6929494 : term509 = term488.
Proof. exact (@lem6929493 term488). Qed.
Lemma lem6929495 : term485 = term488.
Proof. exact (TRANS (@lem6929491) (@lem6929494)). Qed.
Lemma lem6929496 (_92401 : int) : (term484 _92401) = term510.
Proof. exact (MK_COMB (@lem6929373 _92401) (@lem6929495)). Qed.
Lemma lem6929497 (_92401 : int) : (term483 _92401) = term510.
Proof. exact (TRANS (@lem6929265 _92401) (@lem6929496 _92401)). Qed.
Lemma lem6929498 : term510 = term488.
Proof. exact (@lem1982721 term488). Qed.
Lemma lem6929499 (_92401 : int) : (term483 _92401) = term488.
Proof. exact (TRANS (@lem6929497 _92401) (@lem6929498)). Qed.
Lemma lem6929500 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6929501 (_92401 : int) : (term511 _92401) = term512.
Proof. exact (MK_COMB (@lem6929500) (@lem6929499 _92401)). Qed.
Lemma lem6929502 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem6929503 (_92401 : int) : (term482 _92401) = term513.
Proof. exact (MK_COMB (@lem6929501 _92401) (@lem6929502)). Qed.
Lemma lem6929504 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : term513.
Proof. exact (EQ_MP (@lem6929503 _92401) (@lem6929264 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6929506 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6929507 : term513 = term514.
Proof. exact (@lem6929506 term108 term488). Qed.
Lemma lem6929509 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6929510 : term488 = term509.
Proof. exact (@lem6929509 term497). Qed.
Lemma lem6929512 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6929513 : term108 = term154.
Proof. exact (@lem6929512 (NUMERAL 0)). Qed.
Lemma lem6929514 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6929515 : term110 = term383.
Proof. exact (MK_COMB (@lem6929514) (@lem6929513)). Qed.
Lemma lem6929516 : term514 = term515.
Proof. exact (MK_COMB (@lem6929515) (@lem6929510)). Qed.
Lemma lem6929517 : term516.
Proof. exact (@lem1980026 term108 term122 term488 term122). Qed.
Lemma lem6929519 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929520 : term300 = term306.
Proof. exact (@lem6929519 (NUMERAL 0) term123). Qed.
Lemma lem6929521 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929522 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929523 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929522 h1) (fun h1 : term306 = True => @lem6929521)). Qed.
Lemma lem6929524 : term306 = True.
Proof. exact (EQ_MP (@lem6929523) (@lem6929521)). Qed.
Lemma lem6929525 : term300 = True.
Proof. exact (TRANS (@lem6929520) (@lem6929524)). Qed.
Lemma lem6929526 : True = term300.
Proof. exact (SYM (@lem6929525)). Qed.
Lemma lem6929527 : term300.
Proof. exact (EQ_MP (@lem6929526) (@lem0)). Qed.
Lemma lem6929528 : term517.
Proof. exact (@lem6929517 (@lem6929527)). Qed.
Lemma lem6929530 (m : nat) (n : nat) : (term305 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6929531 : term300 = term306.
Proof. exact (@lem6929530 (NUMERAL 0) term123). Qed.
Lemma lem6929532 : term307 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6929533 (h1 : term307 = (BIT1 0)) : term306 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6929534 : (term307 = (BIT1 0)) = (term306 = True).
Proof. exact (prop_ext (fun h1 : term307 = (BIT1 0) => @lem6929533 h1) (fun h1 : term306 = True => @lem6929532)). Qed.
Lemma lem6929535 : term306 = True.
Proof. exact (EQ_MP (@lem6929534) (@lem6929532)). Qed.
Lemma lem6929536 : term300 = True.
Proof. exact (TRANS (@lem6929531) (@lem6929535)). Qed.
Lemma lem6929537 : True = term300.
Proof. exact (SYM (@lem6929536)). Qed.
Lemma lem6929538 : term300.
Proof. exact (EQ_MP (@lem6929537) (@lem0)). Qed.
Lemma lem6929539 : term515 = term518.
Proof. exact (@lem6929528 (@lem6929538)). Qed.
Lemma lem6929541 (m : nat) (n : nat) : (term196 m n) = (term197 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6929542 : term503 = term504.
Proof. exact (@lem6929541 term497 term123). Qed.
Lemma lem6929543 : term505 = term495.
Proof. exact (@lem996237 term495). Qed.
Lemma lem6929544 : (term505 = term495) = (term506 = term497).
Proof. exact (@lem1007663 term495 (BIT1 0) term495). Qed.
Lemma lem6929545 : term506 = term497.
Proof. exact (EQ_MP (@lem6929544) (@lem6929543)). Qed.
Lemma lem6929546 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6929547 : term507 = term499.
Proof. exact (MK_COMB (@lem6929546) (@lem6929545)). Qed.
Lemma lem6929548 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6929549 : term504 = term488.
Proof. exact (MK_COMB (@lem6929548) (@lem6929547)). Qed.
Lemma lem6929550 : term503 = term488.
Proof. exact (TRANS (@lem6929542) (@lem6929549)). Qed.
Lemma lem6929552 (x : nat) : (term310 x) = term108.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6929553 : term311 = term108.
Proof. exact (@lem6929552 term123). Qed.
Lemma lem6929554 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6929555 : term388 = term110.
Proof. exact (MK_COMB (@lem6929554) (@lem6929553)). Qed.
Lemma lem6929556 : term518 = term514.
Proof. exact (MK_COMB (@lem6929555) (@lem6929550)). Qed.
Lemma lem6929558 (m : nat) (n : nat) : (term389 m n) = (term390 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6929559 : term514 = term519.
Proof. exact (@lem6929558 (NUMERAL 0) term497). Qed.
Lemma lem6929560 : term520 = term495.
Proof. exact (@lem912803). Qed.
Lemma lem6929561 (h1 : term520 = term495) : (term497 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term495 h1). Qed.
Lemma lem6929562 : (term520 = term495) = ((term497 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term520 = term495 => @lem6929561 h1) (fun h1 : (term497 = (NUMERAL 0)) = False => @lem6929560)). Qed.
Lemma lem6929563 : (term497 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6929562) (@lem6929560)). Qed.
Lemma lem6929564 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6929565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6929566 : term392 = (and True).
Proof. exact (MK_COMB (@lem6929565) (@lem6929564)). Qed.
Lemma lem6929567 : term519 = (True /\ False).
Proof. exact (MK_COMB (@lem6929566) (@lem6929563)). Qed.
Lemma lem6929569 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6929570 : term519 = False.
Proof. exact (TRANS (@lem6929567) (@lem6929569)). Qed.
Lemma lem6929571 : term514 = False.
Proof. exact (TRANS (@lem6929559) (@lem6929570)). Qed.
Lemma lem6929572 : term518 = False.
Proof. exact (TRANS (@lem6929556) (@lem6929571)). Qed.
Lemma lem6929573 : term515 = False.
Proof. exact (TRANS (@lem6929539) (@lem6929572)). Qed.
Lemma lem6929574 : term514 = False.
Proof. exact (TRANS (@lem6929516) (@lem6929573)). Qed.
Lemma lem6929575 : term513 = False.
Proof. exact (TRANS (@lem6929507) (@lem6929574)). Qed.
Lemma lem6929576 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term453 _92402 _92403 _92400 _92401) : False.
Proof. exact (EQ_MP (@lem6929575) (@lem6929504 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6929577 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term288 _92402 _92403 _92400 _92401) : False.
Proof. exact (or_elim (@lem6927721 _92402 _92403 _92400 _92401 h1) (fun h0 : term423 _92402 _92403 _92400 _92401 => @lem6928503 _92402 _92403 _92400 _92401 h0) (fun h0 : term453 _92402 _92403 _92400 _92401 => @lem6929576 _92402 _92403 _92400 _92401 h0)). Qed.
Lemma lem6929578 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term297 _92402 _92403 _92400 _92401) : False.
Proof. exact (or_elim (@lem6926415 _92402 _92403 _92400 _92401 h1) (fun h0 : term292 _92402 _92403 _92400 _92401 => @lem6927720 _92402 _92403 _92400 _92401 h0) (fun h0 : term288 _92402 _92403 _92400 _92401 => @lem6929577 _92402 _92403 _92400 _92401 h0)). Qed.
Lemma lem6929580 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term297 _92402 _92403 _92400 _92401) : term297 _92402 _92403 _92400 _92401.
Proof. exact (h1). Qed.
Lemma lem6929581 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term297 _92402 _92403 _92400 _92401) : (term297 _92402 _92403 _92400 _92401) = False.
Proof. exact (prop_ext (fun h2 : term297 _92402 _92403 _92400 _92401 => @lem6929578 _92402 _92403 _92400 _92401 h1) (fun h2 : False => @lem6929580 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6929582 (_92402 : int) (_92403 : int) (_92400 : int) (_92401 : int) (h1 : term297 _92402 _92403 _92400 _92401) : False.
Proof. exact (EQ_MP (@lem6929581 _92402 _92403 _92400 _92401 h1) (@lem6929580 _92402 _92403 _92400 _92401 h1)). Qed.
Lemma lem6929583 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) (h1 : term149 _92403 _92402 _92400 _92401) : term149 _92403 _92402 _92400 _92401.
Proof. exact (h1). Qed.
Lemma lem6929584 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) (h1 : term149 _92403 _92402 _92400 _92401) : term297 _92402 _92403 _92400 _92401.
Proof. exact (EQ_MP (@lem6926393 _92402 _92403 _92400 _92401) (@lem6929583 _92403 _92402 _92400 _92401 h1)). Qed.
Lemma lem6929585 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) (h1 : term149 _92403 _92402 _92400 _92401) : (term297 _92402 _92403 _92400 _92401) = False.
Proof. exact (prop_ext (fun h2 : term297 _92402 _92403 _92400 _92401 => @lem6929582 _92402 _92403 _92400 _92401 h2) (fun h2 : False => @lem6929584 _92403 _92402 _92400 _92401 h1)). Qed.
Lemma lem6929586 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) (h1 : term149 _92403 _92402 _92400 _92401) : False.
Proof. exact (EQ_MP (@lem6929585 _92403 _92402 _92400 _92401 h1) (@lem6929584 _92403 _92402 _92400 _92401 h1)). Qed.
Lemma lem6929587 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) : term521 _92403 _92402 _92400 _92401.
Proof. exact (fun h0 : term149 _92403 _92402 _92400 _92401 => @lem6929586 _92403 _92402 _92400 _92401 h0). Qed.
Lemma lem6929588 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) : term522 _92403 _92402 _92400 _92401.
Proof. exact (@lem1386578 (term523 _92403 _92402 _92400 _92401)). Qed.
Lemma lem6929591 (_92403 : int) (_92402 : int) (_92400 : int) (_92401 : int) : term523 _92403 _92402 _92400 _92401.
Proof. exact (@lem6929588 _92403 _92402 _92400 _92401 (@lem6929587 _92403 _92402 _92400 _92401)). Qed.
Lemma lem6929592 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term147 _92403 _92402 _92400 _92401) = (term102 _92403 _92402 _92401 _92400).
Proof. exact (SYM (@lem6925598 _92403 _92402 _92400 _92401)). Qed.
Lemma lem6929593 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6929594 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : (term523 _92403 _92402 _92400 _92401) = (term52 _92403 _92402 _92401 _92400).
Proof. exact (MK_COMB (@lem6929593) (@lem6929592 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6929595 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : term52 _92403 _92402 _92401 _92400.
Proof. exact (EQ_MP (@lem6929594 _92403 _92402 _92401 _92400) (@lem6929591 _92403 _92402 _92400 _92401)). Qed.
Lemma lem6929596 (_92403 : int) (_92402 : int) (_92401 : int) (_92400 : int) : term53 _92403 _92402 _92401 _92400.
Proof. exact (EQ_MP (@lem6925303 _92403 _92402 _92401 _92400) (@lem6929595 _92403 _92402 _92401 _92400)). Qed.
Lemma lem6929597 (z : nat) (y : nat) (x : nat) (d : nat) : term524 z y x d.
Proof. exact (@lem6929596 (int_of_num z) (int_of_num y) (int_of_num x) (int_of_num d)). Qed.
Lemma lem6929598 (z : nat) (y : nat) (x : nat) (d : nat) : term525 z y x d.
Proof. exact (@lem6929597 z y x d (@lem6925293 d)). Qed.
Lemma lem6929599 (z : nat) (y : nat) (x : nat) (d : nat) : term526 z y x d.
Proof. exact (@lem6929598 z y x d (@lem6925296 x)). Qed.
Lemma lem6929600 (z : nat) (y : nat) (x : nat) (d : nat) : term527 z y x d.
Proof. exact (@lem6929599 z y x d (@lem6925299 y)). Qed.
Lemma lem6929601 (z : nat) (y : nat) (x : nat) (d : nat) : term47 z y x d.
Proof. exact (@lem6929600 z y x d (@lem6925302 z)). Qed.
Lemma lem6929602 (z : nat) (y : nat) (x : nat) : term49 z y x.
Proof. exact (fun d : nat => @lem6929601 z y x d). Qed.
Lemma lem6929603 (x : nat) (y : nat) (z : nat) : (term49 z y x) = (term0 x y z).
Proof. exact (SYM (@lem6925290 z y x)). Qed.
Lemma lem6929604 (x : nat) (y : nat) (z : nat) : term0 x y z.
Proof. exact (EQ_MP (@lem6929603 x y z) (@lem6929602 z y x)). Qed.
Lemma lem6929605 (x : nat) (y : nat) (z : nat) (h1 : term0 x y z) : term0 x y z.
Proof. exact (h1). Qed.
Lemma lem6929606 (x : nat) (z : nat) (y : nat) (h1 : (Nat.add x z) = y) : (Nat.add x z) = y.
Proof. exact (h1). Qed.
Lemma lem6929607 (x : nat) (y : nat) (z : nat) (h1 : (Nat.add x z) = y) (h2 : term0 x y z) : x = (Nat.sub y z).
Proof. exact (@lem6929605 x y z h2 (@lem6929606 x z y h1)). Qed.
Lemma lem6929608 (x : nat) (z : nat) (y : nat) (h1 : (Nat.add x z) = y) : term528 x y z.
Proof. exact (fun h0 : term0 x y z => @lem6929607 x y z h1 h0). Qed.
Lemma lem6929609 (x : nat) (y : nat) (z : nat) (h1 : term0 x y z) : term0 x y z.
Proof. exact (h1). Qed.
Lemma lem6929610 (x : nat) (y : nat) (z : nat) (h1 : (Nat.add x z) = y) (h2 : term0 x y z) : x = (Nat.sub y z).
Proof. exact (@lem6929608 x z y h1 (@lem6929609 x y z h2)). Qed.
Lemma lem6929611 (x : nat) (y : nat) (z : nat) (h1 : term0 x y z) : term0 x y z.
Proof. exact (fun h0 : (Nat.add x z) = y => @lem6929610 x y z h0 h1). Qed.
Lemma lem6929612 (x : nat) (y : nat) (z : nat) : term529 x y z.
Proof. exact (fun h0 : term0 x y z => @lem6929611 x y z h0). Qed.
Lemma lem6929614 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : term530 _126606 t s) : term530 _126606 t s.
Proof. exact (h1). Qed.
Lemma lem6929615 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @SUBSET _126606 t s) : @SUBSET _126606 t s.
Proof. exact (h1). Qed.
Lemma lem6929616 {_126606 : Type'} (s : _126606 -> Prop) (h1 : @FINITE _126606 s) : @FINITE _126606 s.
Proof. exact (h1). Qed.
Lemma lem6929618 (x : nat) (y : nat) (z : nat) : term0 x y z.
Proof. exact (@lem6929612 x y z (@lem6929604 x y z)). Qed.
Lemma lem6929619 {_126606 : Type'} (s : _126606 -> Prop) (t : _126606 -> Prop) (f : _126606 -> nat) : term531 _126606 s t f.
Proof. exact (@lem6929618 (term532 _126606 s t f) (@nsum _126606 s f) (@nsum _126606 t f)). Qed.
Lemma lem6929620 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6929622 {_120745 _120749 : Type'} (op : type1400 _120749) : term533 _120745 _120749 op.
Proof. exact (@lem5772504 _120745 _120749 op). Qed.
Lemma lem6929623 {_120745 _120749 : Type'} (op : type1400 _120749) : (term533 _120745 _120749 op) = (term534 _120745 _120749 op).
Proof. exact (eq_refl (term533 _120745 _120749 op)). Qed.
Lemma lem6929624 {_120745 _120749 : Type'} (op : type1400 _120749) : term534 _120745 _120749 op.
Proof. exact (EQ_MP (@lem6929623 _120745 _120749 op) (@lem6929622 _120745 _120749 op)). Qed.
Lemma lem6929625 {_120749 : Type'} (op : type1400 _120749) (h1 : @monoidal _120749 op) : @monoidal _120749 op.
Proof. exact (h1). Qed.
Lemma lem6929626 {_120745 _120749 : Type'} (op : type1400 _120749) (h1 : @monoidal _120749 op) : term535 _120745 _120749 op.
Proof. exact (@lem6929624 _120745 _120749 op (@lem6929625 _120749 op h1)). Qed.
Lemma lem6929627 {_120745 _120749 : Type'} (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term536 _120745 _120749 op f.
Proof. exact (@lem6929626 _120745 _120749 op h1 f). Qed.
Lemma lem6929628 {_120745 _120749 : Type'} (op : type1400 _120749) (f : _120745 -> _120749) : (term536 _120745 _120749 op f) = (term537 _120745 _120749 op f).
Proof. exact (eq_refl (term536 _120745 _120749 op f)). Qed.
Lemma lem6929629 {_120745 _120749 : Type'} (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term537 _120745 _120749 op f.
Proof. exact (EQ_MP (@lem6929628 _120745 _120749 op f) (@lem6929627 _120745 _120749 f op h1)). Qed.
Lemma lem6929630 {_120745 _120749 : Type'} (f : _120745 -> _120749) (s : _120745 -> Prop) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term538 _120745 _120749 op f s.
Proof. exact (@lem6929629 _120745 _120749 f op h1 s). Qed.
Lemma lem6929631 {_120745 _120749 : Type'} (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term538 _120745 _120749 op f s) = (term539 _120745 _120749 op s f).
Proof. exact (eq_refl (term538 _120745 _120749 op f s)). Qed.
Lemma lem6929632 {_120745 _120749 : Type'} (s : _120745 -> Prop) (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term539 _120745 _120749 op s f.
Proof. exact (EQ_MP (@lem6929631 _120745 _120749 op s f) (@lem6929630 _120745 _120749 f s op h1)). Qed.
Lemma lem6929633 {_120745 _120749 : Type'} (s : _120745 -> Prop) (f : _120745 -> _120749) (t : _120745 -> Prop) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term540 _120745 _120749 op s f t.
Proof. exact (@lem6929632 _120745 _120749 s f op h1 t). Qed.
Lemma lem6929634 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term540 _120745 _120749 op s f t) = (term541 _120745 _120749 t op s f).
Proof. exact (eq_refl (term540 _120745 _120749 op s f t)). Qed.
Lemma lem6929635 {_120745 _120749 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term541 _120745 _120749 t op s f.
Proof. exact (EQ_MP (@lem6929634 _120745 _120749 t op s f) (@lem6929633 _120745 _120749 s f t op h1)). Qed.
Lemma lem6929636 {_120745 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) (h1 : term530 _120745 t s) : term530 _120745 t s.
Proof. exact (h1). Qed.
Lemma lem6929637 {_120745 _120749 : Type'} (f : _120745 -> _120749) (op : type1400 _120749) (t : _120745 -> Prop) (s : _120745 -> Prop) (h1 : @monoidal _120749 op) (h2 : term530 _120745 t s) : (term542 _120745 _120749 s op t f) = (@iterate _120749 _120745 op s f).
Proof. exact (@lem6929635 _120745 _120749 t s f op h1 (@lem6929636 _120745 t s h2)). Qed.
Lemma lem6929638 {_120745 _120749 : Type'} (t : _120745 -> Prop) (s : _120745 -> Prop) (f : _120745 -> _120749) (op : type1400 _120749) (h1 : @monoidal _120749 op) : term541 _120745 _120749 t op s f.
Proof. exact (fun h0 : term530 _120745 t s => @lem6929637 _120745 _120749 f op t s h1 h0). Qed.
Lemma lem6929639 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : term543 _120745 _120749 t op s f.
Proof. exact (fun h0 : @monoidal _120749 op => @lem6929638 _120745 _120749 t s f op h0). Qed.
Lemma lem6929641 (p : Prop) (q : Prop) (r : Prop) : (term544 p q r) = (term545 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6929646 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : (term543 _120745 _120749 t op s f) = (term546 _120745 _120749 t op s f).
Proof. exact (@lem6929641 (@monoidal _120749 op) (term530 _120745 t s) ((term542 _120745 _120749 s op t f) = (@iterate _120749 _120745 op s f))). Qed.
Lemma lem6929648 {_126606 : Type'} (s : _126606 -> Prop) : (@FINITE _126606 s) = ((@FINITE _126606 s) = True).
Proof. exact (@lem7 (@FINITE _126606 s)). Qed.
Lemma lem6929650 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) : (@SUBSET _126606 t s) = ((@SUBSET _126606 t s) = True).
Proof. exact (@lem7 (@SUBSET _126606 t s)). Qed.
Lemma lem6929671 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6929672 {_126606 : Type'} : (@nsum _126606) = (@iterate nat _126606 Nat.add).
Proof. exact (@lem6929671 _126606). Qed.
Lemma lem6929689 {_126606 : Type'} (s : _126606 -> Prop) (t : _126606 -> Prop) : (@DIFF _126606 s t) = (@DIFF _126606 s t).
Proof. exact (eq_refl (@DIFF _126606 s t)). Qed.
Lemma lem6929690 {_126606 : Type'} (s : _126606 -> Prop) (t : _126606 -> Prop) : (term547 _126606 s t) = (term548 _126606 s t).
Proof. exact (MK_COMB (@lem6929672 _126606) (@lem6929689 _126606 s t)). Qed.
Lemma lem6929711 {_126606 : Type'} (f : _126606 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6929712 {_126606 : Type'} (s : _126606 -> Prop) (t : _126606 -> Prop) (f : _126606 -> nat) : (term532 _126606 s t f) = (term549 _126606 s t f).
Proof. exact (MK_COMB (@lem6929690 _126606 s t) (@lem6929711 _126606 f)). Qed.
Lemma lem6929735 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6929736 {_126606 : Type'} (s : _126606 -> Prop) (t : _126606 -> Prop) (f : _126606 -> nat) : (term550 _126606 s t f) = (term551 _126606 s t f).
Proof. exact (MK_COMB (@lem6929735) (@lem6929712 _126606 s t f)). Qed.
Lemma lem6929768 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6929769 {_126606 : Type'} : (@nsum _126606) = (@iterate nat _126606 Nat.add).
Proof. exact (@lem6929768 _126606). Qed.
Lemma lem6929778 {_126606 : Type'} (t : _126606 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem6929779 {_126606 : Type'} (t : _126606 -> Prop) : (@nsum _126606 t) = (@iterate nat _126606 Nat.add t).
Proof. exact (MK_COMB (@lem6929769 _126606) (@lem6929778 _126606 t)). Qed.
Lemma lem6929792 {_126606 : Type'} (f : _126606 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6929793 {_126606 : Type'} (t : _126606 -> Prop) (f : _126606 -> nat) : (@nsum _126606 t f) = (@iterate nat _126606 Nat.add t f).
Proof. exact (MK_COMB (@lem6929779 _126606 t) (@lem6929792 _126606 f)). Qed.
Lemma lem6929808 {_126606 : Type'} (s : _126606 -> Prop) (t : _126606 -> Prop) (f : _126606 -> nat) : (term552 _126606 s t f) = (term553 _126606 s t f).
Proof. exact (MK_COMB (@lem6929736 _126606 s t f) (@lem6929793 _126606 t f)). Qed.
Lemma lem6929810 {_120745 _120749 : Type'} (t : _120745 -> Prop) (op : type1400 _120749) (s : _120745 -> Prop) (f : _120745 -> _120749) : term546 _120745 _120749 t op s f.
Proof. exact (EQ_MP (@lem6929646 _120745 _120749 t op s f) (@lem6929639 _120745 _120749 t op s f)). Qed.
Lemma lem6929811 {_126606 : Type'} (t : _126606 -> Prop) (op : type1606) (s : _126606 -> Prop) (f : _126606 -> nat) : term554 _126606 t op s f.
Proof. exact (@lem6929810 _126606 nat t op s f). Qed.
Lemma lem6929812 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) (f : _126606 -> nat) : term555 _126606 t s f.
Proof. exact (@lem6929811 _126606 t Nat.add s f). Qed.
Lemma lem6929822 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6929620) (@lem6924403)). Qed.
Lemma lem6929825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6929826 : term556 = (and True).
Proof. exact (MK_COMB (@lem6929825) (@lem6929822)). Qed.
Lemma lem6929842 {_126606 : Type'} (s : _126606 -> Prop) (h1 : @FINITE _126606 s) : (@FINITE _126606 s) = True.
Proof. exact (EQ_MP (@lem6929648 _126606 s) (@lem6929616 _126606 s h1)). Qed.
Lemma lem6929845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6929846 {_126606 : Type'} (s : _126606 -> Prop) (h1 : @FINITE _126606 s) : (term557 _126606 s) = (and True).
Proof. exact (MK_COMB (@lem6929845) (@lem6929842 _126606 s h1)). Qed.
Lemma lem6929854 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @SUBSET _126606 t s) : (@SUBSET _126606 t s) = True.
Proof. exact (EQ_MP (@lem6929650 _126606 t s) (@lem6929615 _126606 t s h1)). Qed.
Lemma lem6929857 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (term530 _126606 t s) = (True /\ True).
Proof. exact (MK_COMB (@lem6929846 _126606 s h1) (@lem6929854 _126606 t s h2)). Qed.
Lemma lem6929859 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6929860 : (True /\ True) = True.
Proof. exact (@lem6929859 True). Qed.
Lemma lem6929863 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (term530 _126606 t s) = True.
Proof. exact (TRANS (@lem6929857 _126606 t s h1 h2) (@lem6929860)). Qed.
Lemma lem6929864 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (term558 _126606 t s) = (True /\ True).
Proof. exact (MK_COMB (@lem6929826) (@lem6929863 _126606 t s h1 h2)). Qed.
Lemma lem6929866 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6929867 : (True /\ True) = True.
Proof. exact (@lem6929866 True). Qed.
Lemma lem6929870 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (term558 _126606 t s) = True.
Proof. exact (TRANS (@lem6929864 _126606 t s h1 h2) (@lem6929867)). Qed.
Lemma lem6929871 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : True = (term558 _126606 t s).
Proof. exact (SYM (@lem6929870 _126606 t s h1 h2)). Qed.
Lemma lem6929872 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : term558 _126606 t s.
Proof. exact (EQ_MP (@lem6929871 _126606 t s h1 h2) (@lem0)). Qed.
Lemma lem6929873 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (term553 _126606 s t f) = (@iterate nat _126606 Nat.add s f).
Proof. exact (@lem6929812 _126606 t s f (@lem6929872 _126606 t s h1 h2)). Qed.
Lemma lem6929888 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (term552 _126606 s t f) = (@iterate nat _126606 Nat.add s f).
Proof. exact (TRANS (@lem6929808 _126606 s t f) (@lem6929873 _126606 f t s h1 h2)). Qed.
Lemma lem6929889 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6929890 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (term559 _126606 s t f) = (term560 _126606 s f).
Proof. exact (MK_COMB (@lem6929889) (@lem6929888 _126606 f t s h1 h2)). Qed.
Lemma lem6929914 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6929915 {_126606 : Type'} : (@nsum _126606) = (@iterate nat _126606 Nat.add).
Proof. exact (@lem6929914 _126606). Qed.
Lemma lem6929924 {_126606 : Type'} (s : _126606 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6929925 {_126606 : Type'} (s : _126606 -> Prop) : (@nsum _126606 s) = (@iterate nat _126606 Nat.add s).
Proof. exact (MK_COMB (@lem6929915 _126606) (@lem6929924 _126606 s)). Qed.
Lemma lem6929938 {_126606 : Type'} (f : _126606 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6929939 {_126606 : Type'} (s : _126606 -> Prop) (f : _126606 -> nat) : (@nsum _126606 s f) = (@iterate nat _126606 Nat.add s f).
Proof. exact (MK_COMB (@lem6929925 _126606 s) (@lem6929938 _126606 f)). Qed.
Lemma lem6929954 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : ((term552 _126606 s t f) = (@nsum _126606 s f)) = ((@iterate nat _126606 Nat.add s f) = (@iterate nat _126606 Nat.add s f)).
Proof. exact (MK_COMB (@lem6929890 _126606 f t s h1 h2) (@lem6929939 _126606 s f)). Qed.
Lemma lem6929956 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6929957 (x : nat) : (x = x) = True.
Proof. exact (@lem6929956 nat x). Qed.
Lemma lem6929958 {_126606 : Type'} (s : _126606 -> Prop) (f : _126606 -> nat) : ((@iterate nat _126606 Nat.add s f) = (@iterate nat _126606 Nat.add s f)) = True.
Proof. exact (@lem6929957 (@iterate nat _126606 Nat.add s f)). Qed.
Lemma lem6929961 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : ((term552 _126606 s t f) = (@nsum _126606 s f)) = True.
Proof. exact (TRANS (@lem6929954 _126606 f t s h1 h2) (@lem6929958 _126606 s f)). Qed.
Lemma lem6929962 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : True = ((term552 _126606 s t f) = (@nsum _126606 s f)).
Proof. exact (SYM (@lem6929961 _126606 f t s h1 h2)). Qed.
Lemma lem6929963 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (term552 _126606 s t f) = (@nsum _126606 s f).
Proof. exact (EQ_MP (@lem6929962 _126606 f t s h1 h2) (@lem0)). Qed.
Lemma lem6929964 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (term532 _126606 s t f) = (term561 _126606 s t f).
Proof. exact (@lem6929619 _126606 s t f (@lem6929963 _126606 f t s h1 h2)). Qed.
Lemma lem6929965 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : term530 _126606 t s) : @SUBSET _126606 t s.
Proof. exact (proj2 (@lem6929614 _126606 t s h1)). Qed.
Lemma lem6929966 {_126606 : Type'} (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : term530 _126606 t s) : @FINITE _126606 s.
Proof. exact (proj1 (@lem6929614 _126606 t s h1)). Qed.
Lemma lem6929967 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (@SUBSET _126606 t s) = ((term532 _126606 s t f) = (term561 _126606 s t f)).
Proof. exact (prop_ext (fun h3 : @SUBSET _126606 t s => @lem6929964 _126606 f t s h1 h2) (fun h3 : (term532 _126606 s t f) = (term561 _126606 s t f) => @lem6929615 _126606 t s h2)). Qed.
Lemma lem6929968 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (term532 _126606 s t f) = (term561 _126606 s t f).
Proof. exact (EQ_MP (@lem6929967 _126606 f t s h1 h2) (@lem6929615 _126606 t s h2)). Qed.
Lemma lem6929969 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (@FINITE _126606 s) = ((term532 _126606 s t f) = (term561 _126606 s t f)).
Proof. exact (prop_ext (fun h3 : @FINITE _126606 s => @lem6929968 _126606 f t s h1 h2) (fun h3 : (term532 _126606 s t f) = (term561 _126606 s t f) => @lem6929616 _126606 s h1)). Qed.
Lemma lem6929970 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : @SUBSET _126606 t s) : (term532 _126606 s t f) = (term561 _126606 s t f).
Proof. exact (EQ_MP (@lem6929969 _126606 f t s h1 h2) (@lem6929616 _126606 s h1)). Qed.
Lemma lem6929971 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : term530 _126606 t s) : (@SUBSET _126606 t s) = ((term532 _126606 s t f) = (term561 _126606 s t f)).
Proof. exact (prop_ext (fun h3 : @SUBSET _126606 t s => @lem6929970 _126606 f t s h1 h3) (fun h3 : (term532 _126606 s t f) = (term561 _126606 s t f) => @lem6929965 _126606 t s h2)). Qed.
Lemma lem6929972 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : @FINITE _126606 s) (h2 : term530 _126606 t s) : (term532 _126606 s t f) = (term561 _126606 s t f).
Proof. exact (EQ_MP (@lem6929971 _126606 f t s h1 h2) (@lem6929965 _126606 t s h2)). Qed.
Lemma lem6929973 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : term530 _126606 t s) : (@FINITE _126606 s) = ((term532 _126606 s t f) = (term561 _126606 s t f)).
Proof. exact (prop_ext (fun h2 : @FINITE _126606 s => @lem6929972 _126606 f t s h2 h1) (fun h2 : (term532 _126606 s t f) = (term561 _126606 s t f) => @lem6929966 _126606 t s h1)). Qed.
Lemma lem6929974 {_126606 : Type'} (f : _126606 -> nat) (t : _126606 -> Prop) (s : _126606 -> Prop) (h1 : term530 _126606 t s) : (term532 _126606 s t f) = (term561 _126606 s t f).
Proof. exact (EQ_MP (@lem6929973 _126606 f t s h1) (@lem6929966 _126606 t s h1)). Qed.
Lemma lem6929975 {_126606 : Type'} (s : _126606 -> Prop) (t : _126606 -> Prop) (f : _126606 -> nat) : term562 _126606 s t f.
Proof. exact (fun h0 : term530 _126606 t s => @lem6929974 _126606 f t s h0). Qed.
Lemma lem6929980 {_126606 : Type'} (s : _126606 -> Prop) (f : _126606 -> nat) : term563 _126606 s f.
Proof. exact (fun t : _126606 -> Prop => @lem6929975 _126606 s t f). Qed.
Lemma lem6929985 {_126606 : Type'} (f : _126606 -> nat) : term564 _126606 f.
Proof. exact (fun s : _126606 -> Prop => @lem6929980 _126606 s f). Qed.
Lemma lem6929990 {_126606 : Type'} : term565 _126606.
Proof. exact (fun f : _126606 -> nat => @lem6929985 _126606 f). Qed.
