Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5404127_term_abbrevs.
Require Import INT_POS_spec.
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
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5401085 (m : nat) (x : nat) : ((term0 m x) = (x = (NUMERAL 0))) = ((term0 m x) = (x = (NUMERAL 0))).
Proof. exact (eq_refl ((term0 m x) = (x = (NUMERAL 0)))). Qed.
Lemma lem5401086 (m : nat) : (term1 m) = (term1 m).
Proof. exact (fun_ext (fun x : nat => @lem5401085 m x)). Qed.
Lemma lem5401087 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5401088 (m : nat) : (term2 m) = (term2 m).
Proof. exact (MK_COMB (@lem5401087) (@lem5401086 m)). Qed.
Lemma lem5401091 (m : nat) : (term3 m) = (term3 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem5401093 (m : nat) : (term4 m) = (term4 m).
Proof. exact (MK_COMB (@lem5401091 m) (@lem5401088 m)). Qed.
Lemma lem5401103 (m : nat) (x : nat) : (term5 m x) = (term6 m x).
Proof. exact (@lem17045 (Peano.le m x) (term7 x)). Qed.
Lemma lem5401108 (x : nat) : (x = (NUMERAL 0)) = (x = (NUMERAL 0)).
Proof. exact (eq_refl (x = (NUMERAL 0))). Qed.
Lemma lem5401109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5401110 (m : nat) (x : nat) : (term8 m x) = (term9 m x).
Proof. exact (MK_COMB (@lem5401109) (@lem5401103 m x)). Qed.
Lemma lem5401111 (m : nat) (x : nat) : (term10 m x) = (term11 m x).
Proof. exact (MK_COMB (@lem5401110 m x) (@lem5401108 x)). Qed.
Lemma lem5401116 (m : nat) (x : nat) : (term12 m x) = (term12 m x).
Proof. exact (eq_refl (term12 m x)). Qed.
Lemma lem5401117 (m : nat) (x : nat) : (term13 m x) = (term14 m x).
Proof. exact (MK_COMB (@lem5401116 m x) (@lem5401111 m x)). Qed.
Lemma lem5401118 (m : nat) (x : nat) : ((term0 m x) = (x = (NUMERAL 0))) = (term13 m x).
Proof. exact (@lem17784 (term0 m x) (x = (NUMERAL 0))). Qed.
Lemma lem5401119 (m : nat) (x : nat) : ((term0 m x) = (x = (NUMERAL 0))) = (term14 m x).
Proof. exact (TRANS (@lem5401118 m x) (@lem5401117 m x)). Qed.
Lemma lem5401120 (m : nat) : (term1 m) = (term15 m).
Proof. exact (fun_ext (fun x : nat => @lem5401119 m x)). Qed.
Lemma lem5401121 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5401122 (m : nat) : (term2 m) = (term16 m).
Proof. exact (MK_COMB (@lem5401121) (@lem5401120 m)). Qed.
Lemma lem5401124 (m : nat) : (term17 m) = (term17 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem5401125 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem5401124 m) (@lem5401122 m)). Qed.
Lemma lem5401126 (m : nat) : (term4 m) = (term18 m).
Proof. exact (@lem17265 (m = (NUMERAL 0)) (term2 m)). Qed.
Lemma lem5401127 (m : nat) : (term4 m) = (term19 m).
Proof. exact (TRANS (@lem5401126 m) (@lem5401125 m)). Qed.
Lemma lem5401128 (m : nat) : (term4 m) = (term19 m).
Proof. exact (TRANS (@lem5401093 m) (@lem5401127 m)). Qed.
Lemma lem5401129 (m : nat) (x : nat) : (term14 m x) = (term14 m x).
Proof. exact (eq_refl (term14 m x)). Qed.
Lemma lem5401130 (m : nat) : (term15 m) = (term15 m).
Proof. exact (fun_ext (fun x : nat => @lem5401129 m x)). Qed.
Lemma lem5401131 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5401132 (m : nat) : (term16 m) = (term16 m).
Proof. exact (MK_COMB (@lem5401131) (@lem5401130 m)). Qed.
Lemma lem5401135 (m : nat) : (term17 m) = (term17 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem5401136 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem5401135 m) (@lem5401132 m)). Qed.
Lemma lem5401165 (m : nat) : (term4 m) = (term19 m).
Proof. exact (TRANS (@lem5401128 m) (@lem5401136 m)). Qed.
Lemma lem5401216 (m : nat) (x : nat) : (term14 m x) = (term14 m x).
Proof. exact (eq_refl (term14 m x)). Qed.
Lemma lem5401217 (m : nat) : (term15 m) = (term15 m).
Proof. exact (fun_ext (fun x : nat => @lem5401216 m x)). Qed.
Lemma lem5401218 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5401219 (m : nat) : (term16 m) = (term16 m).
Proof. exact (MK_COMB (@lem5401218) (@lem5401217 m)). Qed.
Lemma lem5401228 (m : nat) : (term17 m) = (term17 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem5401229 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem5401228 m) (@lem5401219 m)). Qed.
Lemma lem5401230 (m : nat) : (term4 m) = (term19 m).
Proof. exact (TRANS (@lem5401165 m) (@lem5401229 m)). Qed.
Lemma lem5401232 {A : Type'} (P : Prop) (Q : A -> Prop) : (term20 A P Q) = (term21 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5401233 (P : Prop) (Q : nat -> Prop) : (term22 P Q) = (term23 P Q).
Proof. exact (@lem5401232 nat P Q). Qed.
Lemma lem5401234 (m : nat) : (term24 m) = (term25 m).
Proof. exact (@lem5401233 (term26 m) (term15 m)). Qed.
Lemma lem5401235 (m : nat) (x : nat) : (term27 m x) = (term14 m x).
Proof. exact (eq_refl (term27 m x)). Qed.
Lemma lem5401236 (m : nat) : (term28 m) = (term15 m).
Proof. exact (fun_ext (fun x : nat => @lem5401235 m x)). Qed.
Lemma lem5401237 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5401238 (m : nat) : (term29 m) = (term16 m).
Proof. exact (MK_COMB (@lem5401237) (@lem5401236 m)). Qed.
Lemma lem5401239 (m : nat) : (term17 m) = (term17 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem5401240 (m : nat) : (term24 m) = (term19 m).
Proof. exact (MK_COMB (@lem5401239 m) (@lem5401238 m)). Qed.
Lemma lem5401241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5401242 (m : nat) : (term30 m) = (term31 m).
Proof. exact (MK_COMB (@lem5401241) (@lem5401240 m)). Qed.
Lemma lem5401243 (m : nat) (x : nat) : (term27 m x) = (term14 m x).
Proof. exact (eq_refl (term27 m x)). Qed.
Lemma lem5401244 (m : nat) : (term17 m) = (term17 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem5401245 (m : nat) (x : nat) : (term32 m x) = (term33 m x).
Proof. exact (MK_COMB (@lem5401244 m) (@lem5401243 m x)). Qed.
Lemma lem5401246 (m : nat) : (term34 m) = (term35 m).
Proof. exact (fun_ext (fun x : nat => @lem5401245 m x)). Qed.
Lemma lem5401247 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5401248 (m : nat) : (term25 m) = (term36 m).
Proof. exact (MK_COMB (@lem5401247) (@lem5401246 m)). Qed.
Lemma lem5401249 (m : nat) : ((term24 m) = (term25 m)) = ((term19 m) = (term36 m)).
Proof. exact (MK_COMB (@lem5401242 m) (@lem5401248 m)). Qed.
Lemma lem5401250 (m : nat) : (term19 m) = (term36 m).
Proof. exact (EQ_MP (@lem5401249 m) (@lem5401234 m)). Qed.
Lemma lem5401251 (m : nat) : (term4 m) = (term36 m).
Proof. exact (TRANS (@lem5401230 m) (@lem5401250 m)). Qed.
Lemma lem5401253 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5401254 (m : nat) : (m = (NUMERAL 0)) = ((int_of_num m) = term37).
Proof. exact (@lem5401253 m (NUMERAL 0)). Qed.
Lemma lem5401257 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5401258 (m : nat) : (term26 m) = (term38 m).
Proof. exact (MK_COMB (@lem5401257) (@lem5401254 m)). Qed.
Lemma lem5401259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5401260 (m : nat) : (term17 m) = (term39 m).
Proof. exact (MK_COMB (@lem5401259) (@lem5401258 m)). Qed.
Lemma lem5401262 (m : nat) (n : nat) : (Peano.le m n) = (term40 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5401263 (m : nat) (x : nat) : (Peano.le m x) = (term40 m x).
Proof. exact (@lem5401262 m x). Qed.
Lemma lem5401264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5401265 (m : nat) (x : nat) : (term41 m x) = (term42 m x).
Proof. exact (MK_COMB (@lem5401264) (@lem5401263 m x)). Qed.
Lemma lem5401267 (m : nat) (n : nat) : (Peano.le m n) = (term40 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5401268 (x : nat) : (term7 x) = (term43 x).
Proof. exact (@lem5401267 x (NUMERAL 0)). Qed.
Lemma lem5401269 (m : nat) (x : nat) : (term0 m x) = (term44 m x).
Proof. exact (MK_COMB (@lem5401265 m x) (@lem5401268 x)). Qed.
Lemma lem5401270 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5401271 (m : nat) (x : nat) : (term45 m x) = (term46 m x).
Proof. exact (MK_COMB (@lem5401270) (@lem5401269 m x)). Qed.
Lemma lem5401273 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5401274 (x : nat) : (x = (NUMERAL 0)) = ((int_of_num x) = term37).
Proof. exact (@lem5401273 x (NUMERAL 0)). Qed.
Lemma lem5401277 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5401278 (x : nat) : (term26 x) = (term38 x).
Proof. exact (MK_COMB (@lem5401277) (@lem5401274 x)). Qed.
Lemma lem5401279 (m : nat) (x : nat) : (term47 m x) = (term48 m x).
Proof. exact (MK_COMB (@lem5401271 m x) (@lem5401278 x)). Qed.
Lemma lem5401280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5401281 (m : nat) (x : nat) : (term12 m x) = (term49 m x).
Proof. exact (MK_COMB (@lem5401280) (@lem5401279 m x)). Qed.
Lemma lem5401283 (m : nat) (n : nat) : (Peano.le m n) = (term40 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5401284 (m : nat) (x : nat) : (Peano.le m x) = (term40 m x).
Proof. exact (@lem5401283 m x). Qed.
Lemma lem5401285 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5401286 (m : nat) (x : nat) : (term50 m x) = (term51 m x).
Proof. exact (MK_COMB (@lem5401285) (@lem5401284 m x)). Qed.
Lemma lem5401287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5401288 (m : nat) (x : nat) : (term52 m x) = (term53 m x).
Proof. exact (MK_COMB (@lem5401287) (@lem5401286 m x)). Qed.
Lemma lem5401290 (m : nat) (n : nat) : (Peano.le m n) = (term40 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5401291 (x : nat) : (term7 x) = (term43 x).
Proof. exact (@lem5401290 x (NUMERAL 0)). Qed.
Lemma lem5401292 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5401293 (x : nat) : (term54 x) = (term55 x).
Proof. exact (MK_COMB (@lem5401292) (@lem5401291 x)). Qed.
Lemma lem5401294 (m : nat) (x : nat) : (term6 m x) = (term56 m x).
Proof. exact (MK_COMB (@lem5401288 m x) (@lem5401293 x)). Qed.
Lemma lem5401295 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5401296 (m : nat) (x : nat) : (term9 m x) = (term57 m x).
Proof. exact (MK_COMB (@lem5401295) (@lem5401294 m x)). Qed.
Lemma lem5401298 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5401299 (x : nat) : (x = (NUMERAL 0)) = ((int_of_num x) = term37).
Proof. exact (@lem5401298 x (NUMERAL 0)). Qed.
Lemma lem5401302 (m : nat) (x : nat) : (term11 m x) = (term58 m x).
Proof. exact (MK_COMB (@lem5401296 m x) (@lem5401299 x)). Qed.
Lemma lem5401303 (m : nat) (x : nat) : (term14 m x) = (term59 m x).
Proof. exact (MK_COMB (@lem5401281 m x) (@lem5401302 m x)). Qed.
Lemma lem5401304 (m : nat) (x : nat) : (term33 m x) = (term60 m x).
Proof. exact (MK_COMB (@lem5401260 m) (@lem5401303 m x)). Qed.
Lemma lem5401305 (m : nat) : (term35 m) = (term61 m).
Proof. exact (fun_ext (fun x : nat => @lem5401304 m x)). Qed.
Lemma lem5401306 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5401307 (m : nat) : (term36 m) = (term62 m).
Proof. exact (MK_COMB (@lem5401306) (@lem5401305 m)). Qed.
Lemma lem5401308 (m : nat) : (term4 m) = (term62 m).
Proof. exact (TRANS (@lem5401251 m) (@lem5401307 m)). Qed.
Lemma lem5401309 (m : nat) : term63 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem5401310 (m : nat) : (term63 m) = (term64 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem5401311 (m : nat) : term64 m.
Proof. exact (EQ_MP (@lem5401310 m) (@lem5401309 m)). Qed.
Lemma lem5401312 (x : nat) : term63 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5401313 (x : nat) : (term63 x) = (term64 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem5401314 (x : nat) : term64 x.
Proof. exact (EQ_MP (@lem5401313 x) (@lem5401312 x)). Qed.
Lemma lem5401315 (_69895 : int) (_69896 : int) : (term65 _69895 _69896) = (term66 _69895 _69896).
Proof. exact (@lem2318604 (term66 _69895 _69896)). Qed.
Lemma lem5401341 (_69895 : int) : (term67 _69895) = (_69895 = term37).
Proof. exact (@lem16933 (_69895 = term37)). Qed.
Lemma lem5401348 (_69895 : int) (_69896 : int) : (term68 _69895 _69896) = (term69 _69895 _69896).
Proof. exact (@lem17045 (int_le _69895 _69896) (term70 _69896)). Qed.
Lemma lem5401351 (_69896 : int) : (term67 _69896) = (_69896 = term37).
Proof. exact (@lem16933 (_69896 = term37)). Qed.
Lemma lem5401352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5401353 (_69895 : int) (_69896 : int) : (term71 _69895 _69896) = (term72 _69895 _69896).
Proof. exact (MK_COMB (@lem5401352) (@lem5401348 _69895 _69896)). Qed.
Lemma lem5401354 (_69895 : int) (_69896 : int) : (term73 _69895 _69896) = (term74 _69895 _69896).
Proof. exact (MK_COMB (@lem5401353 _69895 _69896) (@lem5401351 _69896)). Qed.
Lemma lem5401355 (_69895 : int) (_69896 : int) : (term75 _69895 _69896) = (term73 _69895 _69896).
Proof. exact (@lem17160 (term76 _69895 _69896) (term77 _69896)). Qed.
Lemma lem5401356 (_69895 : int) (_69896 : int) : (term75 _69895 _69896) = (term74 _69895 _69896).
Proof. exact (TRANS (@lem5401355 _69895 _69896) (@lem5401354 _69895 _69896)). Qed.
Lemma lem5401359 (_69895 : int) (_69896 : int) : (term78 _69895 _69896) = (int_le _69895 _69896).
Proof. exact (@lem16933 (int_le _69895 _69896)). Qed.
Lemma lem5401362 (_69896 : int) : (term79 _69896) = (term70 _69896).
Proof. exact (@lem16933 (term70 _69896)). Qed.
Lemma lem5401363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5401364 (_69895 : int) (_69896 : int) : (term80 _69895 _69896) = (term81 _69895 _69896).
Proof. exact (MK_COMB (@lem5401363) (@lem5401359 _69895 _69896)). Qed.
Lemma lem5401365 (_69895 : int) (_69896 : int) : (term82 _69895 _69896) = (term76 _69895 _69896).
Proof. exact (MK_COMB (@lem5401364 _69895 _69896) (@lem5401362 _69896)). Qed.
Lemma lem5401366 (_69895 : int) (_69896 : int) : (term83 _69895 _69896) = (term82 _69895 _69896).
Proof. exact (@lem17160 (term84 _69895 _69896) (term85 _69896)). Qed.
Lemma lem5401367 (_69895 : int) (_69896 : int) : (term83 _69895 _69896) = (term76 _69895 _69896).
Proof. exact (TRANS (@lem5401366 _69895 _69896) (@lem5401365 _69895 _69896)). Qed.
Lemma lem5401368 (_69896 : int) : (term77 _69896) = (term77 _69896).
Proof. exact (eq_refl (term77 _69896)). Qed.
Lemma lem5401369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5401370 (_69895 : int) (_69896 : int) : (term86 _69895 _69896) = (term87 _69895 _69896).
Proof. exact (MK_COMB (@lem5401369) (@lem5401367 _69895 _69896)). Qed.
Lemma lem5401371 (_69895 : int) (_69896 : int) : (term88 _69895 _69896) = (term89 _69895 _69896).
Proof. exact (MK_COMB (@lem5401370 _69895 _69896) (@lem5401368 _69896)). Qed.
Lemma lem5401372 (_69895 : int) (_69896 : int) : (term90 _69895 _69896) = (term88 _69895 _69896).
Proof. exact (@lem17160 (term69 _69895 _69896) (_69896 = term37)). Qed.
Lemma lem5401373 (_69895 : int) (_69896 : int) : (term90 _69895 _69896) = (term89 _69895 _69896).
Proof. exact (TRANS (@lem5401372 _69895 _69896) (@lem5401371 _69895 _69896)). Qed.
Lemma lem5401374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5401375 (_69895 : int) (_69896 : int) : (term91 _69895 _69896) = (term92 _69895 _69896).
Proof. exact (MK_COMB (@lem5401374) (@lem5401356 _69895 _69896)). Qed.
Lemma lem5401376 (_69895 : int) (_69896 : int) : (term93 _69895 _69896) = (term94 _69895 _69896).
Proof. exact (MK_COMB (@lem5401375 _69895 _69896) (@lem5401373 _69895 _69896)). Qed.
Lemma lem5401377 (_69895 : int) (_69896 : int) : (term95 _69895 _69896) = (term93 _69895 _69896).
Proof. exact (@lem17045 (term96 _69895 _69896) (term97 _69895 _69896)). Qed.
Lemma lem5401378 (_69895 : int) (_69896 : int) : (term95 _69895 _69896) = (term94 _69895 _69896).
Proof. exact (TRANS (@lem5401377 _69895 _69896) (@lem5401376 _69895 _69896)). Qed.
Lemma lem5401379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5401380 (_69895 : int) : (term98 _69895) = (term99 _69895).
Proof. exact (MK_COMB (@lem5401379) (@lem5401341 _69895)). Qed.
Lemma lem5401381 (_69895 : int) (_69896 : int) : (term100 _69895 _69896) = (term101 _69895 _69896).
Proof. exact (MK_COMB (@lem5401380 _69895) (@lem5401378 _69895 _69896)). Qed.
Lemma lem5401382 (_69895 : int) (_69896 : int) : (term102 _69895 _69896) = (term100 _69895 _69896).
Proof. exact (@lem17160 (term77 _69895) (term103 _69895 _69896)). Qed.
Lemma lem5401383 (_69895 : int) (_69896 : int) : (term102 _69895 _69896) = (term101 _69895 _69896).
Proof. exact (TRANS (@lem5401382 _69895 _69896) (@lem5401381 _69895 _69896)). Qed.
Lemma lem5401385 (_69896 : int) : (term104 _69896) = (term104 _69896).
Proof. exact (eq_refl (term104 _69896)). Qed.
Lemma lem5401386 (_69895 : int) (_69896 : int) : (term105 _69895 _69896) = (term106 _69895 _69896).
Proof. exact (MK_COMB (@lem5401385 _69896) (@lem5401383 _69895 _69896)). Qed.
Lemma lem5401387 (_69895 : int) (_69896 : int) : (term107 _69895 _69896) = (term105 _69895 _69896).
Proof. exact (@lem17362 (term108 _69896) (term109 _69895 _69896)). Qed.
Lemma lem5401388 (_69895 : int) (_69896 : int) : (term107 _69895 _69896) = (term106 _69895 _69896).
Proof. exact (TRANS (@lem5401387 _69895 _69896) (@lem5401386 _69895 _69896)). Qed.
Lemma lem5401390 (_69895 : int) : (term104 _69895) = (term104 _69895).
Proof. exact (eq_refl (term104 _69895)). Qed.
Lemma lem5401391 (_69895 : int) (_69896 : int) : (term110 _69895 _69896) = (term111 _69895 _69896).
Proof. exact (MK_COMB (@lem5401390 _69895) (@lem5401388 _69895 _69896)). Qed.
Lemma lem5401392 (_69895 : int) (_69896 : int) : (term112 _69895 _69896) = (term110 _69895 _69896).
Proof. exact (@lem17362 (term108 _69895) (term113 _69895 _69896)). Qed.
Lemma lem5401434 (_69895 : int) (_69896 : int) : (term112 _69895 _69896) = (term111 _69895 _69896).
Proof. exact (TRANS (@lem5401392 _69895 _69896) (@lem5401391 _69895 _69896)). Qed.
Lemma lem5401437 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5401438 (_69895 : int) : (term108 _69895) = (term115 _69895).
Proof. exact (@lem5401437 term37 _69895). Qed.
Lemma lem5401440 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5401441 : term117 = term118.
Proof. exact (@lem5401440 (NUMERAL 0)). Qed.
Lemma lem5401442 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5401443 : term119 = term120.
Proof. exact (MK_COMB (@lem5401442) (@lem5401441)). Qed.
Lemma lem5401444 (_69895 : int) : (real_of_int _69895) = (real_of_int _69895).
Proof. exact (eq_refl (real_of_int _69895)). Qed.
Lemma lem5401445 (_69895 : int) : (term115 _69895) = (term121 _69895).
Proof. exact (MK_COMB (@lem5401443) (@lem5401444 _69895)). Qed.
Lemma lem5401447 (_69895 : int) : (term108 _69895) = (term121 _69895).
Proof. exact (TRANS (@lem5401438 _69895) (@lem5401445 _69895)). Qed.
Lemma lem5401450 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5401451 (_69896 : int) : (term108 _69896) = (term115 _69896).
Proof. exact (@lem5401450 term37 _69896). Qed.
Lemma lem5401453 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5401454 : term117 = term118.
Proof. exact (@lem5401453 (NUMERAL 0)). Qed.
Lemma lem5401455 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5401456 : term119 = term120.
Proof. exact (MK_COMB (@lem5401455) (@lem5401454)). Qed.
Lemma lem5401457 (_69896 : int) : (real_of_int _69896) = (real_of_int _69896).
Proof. exact (eq_refl (real_of_int _69896)). Qed.
Lemma lem5401458 (_69896 : int) : (term115 _69896) = (term121 _69896).
Proof. exact (MK_COMB (@lem5401456) (@lem5401457 _69896)). Qed.
Lemma lem5401460 (_69896 : int) : (term108 _69896) = (term121 _69896).
Proof. exact (TRANS (@lem5401451 _69896) (@lem5401458 _69896)). Qed.
Lemma lem5401463 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5401464 (_69895 : int) : (_69895 = term37) = ((real_of_int _69895) = term117).
Proof. exact (@lem5401463 _69895 term37). Qed.
Lemma lem5401468 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5401469 : term117 = term118.
Proof. exact (@lem5401468 (NUMERAL 0)). Qed.
Lemma lem5401470 (_69895 : int) : (term122 _69895) = (term122 _69895).
Proof. exact (eq_refl (term122 _69895)). Qed.
Lemma lem5401471 (_69895 : int) : ((real_of_int _69895) = term117) = ((real_of_int _69895) = term118).
Proof. exact (MK_COMB (@lem5401470 _69895) (@lem5401469)). Qed.
Lemma lem5401473 (_69895 : int) : (_69895 = term37) = ((real_of_int _69895) = term118).
Proof. exact (TRANS (@lem5401464 _69895) (@lem5401471 _69895)). Qed.
Lemma lem5401475 (y : int) (x : int) : (term84 x y) = (term123 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5401476 (_69896 : int) (_69895 : int) : (term84 _69895 _69896) = (term123 _69896 _69895).
Proof. exact (@lem5401475 _69896 _69895). Qed.
Lemma lem5401478 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5401479 (_69896 : int) (_69895 : int) : (term123 _69896 _69895) = (term124 _69896 _69895).
Proof. exact (@lem5401478 (term125 _69896) _69895). Qed.
Lemma lem5401481 (x : int) (y : int) : (term126 x y) = (term127 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5401482 (_69896 : int) : (term128 _69896) = (term129 _69896).
Proof. exact (@lem5401481 _69896 term130). Qed.
Lemma lem5401484 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5401485 : term131 = term132.
Proof. exact (@lem5401484 term133). Qed.
Lemma lem5401486 (_69896 : int) : (term134 _69896) = (term134 _69896).
Proof. exact (eq_refl (term134 _69896)). Qed.
Lemma lem5401487 (_69896 : int) : (term129 _69896) = (term135 _69896).
Proof. exact (MK_COMB (@lem5401486 _69896) (@lem5401485)). Qed.
Lemma lem5401488 (_69896 : int) : (term128 _69896) = (term135 _69896).
Proof. exact (TRANS (@lem5401482 _69896) (@lem5401487 _69896)). Qed.
Lemma lem5401489 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5401490 (_69896 : int) : (term136 _69896) = (term137 _69896).
Proof. exact (MK_COMB (@lem5401489) (@lem5401488 _69896)). Qed.
Lemma lem5401491 (_69895 : int) : (real_of_int _69895) = (real_of_int _69895).
Proof. exact (eq_refl (real_of_int _69895)). Qed.
Lemma lem5401492 (_69896 : int) (_69895 : int) : (term124 _69896 _69895) = (term138 _69896 _69895).
Proof. exact (MK_COMB (@lem5401490 _69896) (@lem5401491 _69895)). Qed.
Lemma lem5401493 (_69896 : int) (_69895 : int) : (term123 _69896 _69895) = (term138 _69896 _69895).
Proof. exact (TRANS (@lem5401479 _69896 _69895) (@lem5401492 _69896 _69895)). Qed.
Lemma lem5401494 (_69896 : int) (_69895 : int) : (term84 _69895 _69896) = (term138 _69896 _69895).
Proof. exact (TRANS (@lem5401476 _69896 _69895) (@lem5401493 _69896 _69895)). Qed.
Lemma lem5401496 (y : int) (x : int) : (term84 x y) = (term123 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5401497 (_69896 : int) : (term85 _69896) = (term139 _69896).
Proof. exact (@lem5401496 term37 _69896). Qed.
Lemma lem5401499 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5401500 (_69896 : int) : (term139 _69896) = (term140 _69896).
Proof. exact (@lem5401499 term141 _69896). Qed.
Lemma lem5401502 (x : int) (y : int) : (term126 x y) = (term127 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5401503 : term142 = term143.
Proof. exact (@lem5401502 term37 term130). Qed.
Lemma lem5401505 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5401506 : term117 = term118.
Proof. exact (@lem5401505 (NUMERAL 0)). Qed.
Lemma lem5401507 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5401508 : term144 = term145.
Proof. exact (MK_COMB (@lem5401507) (@lem5401506)). Qed.
Lemma lem5401510 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5401511 : term131 = term132.
Proof. exact (@lem5401510 term133). Qed.
Lemma lem5401512 : term143 = term146.
Proof. exact (MK_COMB (@lem5401508) (@lem5401511)). Qed.
Lemma lem5401513 : term142 = term146.
Proof. exact (TRANS (@lem5401503) (@lem5401512)). Qed.
Lemma lem5401514 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5401515 : term147 = term148.
Proof. exact (MK_COMB (@lem5401514) (@lem5401513)). Qed.
Lemma lem5401516 (_69896 : int) : (real_of_int _69896) = (real_of_int _69896).
Proof. exact (eq_refl (real_of_int _69896)). Qed.
Lemma lem5401517 (_69896 : int) : (term140 _69896) = (term149 _69896).
Proof. exact (MK_COMB (@lem5401515) (@lem5401516 _69896)). Qed.
Lemma lem5401518 (_69896 : int) : (term139 _69896) = (term149 _69896).
Proof. exact (TRANS (@lem5401500 _69896) (@lem5401517 _69896)). Qed.
Lemma lem5401519 (_69896 : int) : (term85 _69896) = (term149 _69896).
Proof. exact (TRANS (@lem5401497 _69896) (@lem5401518 _69896)). Qed.
Lemma lem5401520 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5401521 (_69896 : int) (_69895 : int) : (term150 _69895 _69896) = (term151 _69896 _69895).
Proof. exact (MK_COMB (@lem5401520) (@lem5401494 _69896 _69895)). Qed.
Lemma lem5401522 (_69895 : int) (_69896 : int) : (term69 _69895 _69896) = (term152 _69895 _69896).
Proof. exact (MK_COMB (@lem5401521 _69896 _69895) (@lem5401519 _69896)). Qed.
Lemma lem5401525 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5401526 (_69896 : int) : (_69896 = term37) = ((real_of_int _69896) = term117).
Proof. exact (@lem5401525 _69896 term37). Qed.
Lemma lem5401530 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5401531 : term117 = term118.
Proof. exact (@lem5401530 (NUMERAL 0)). Qed.
Lemma lem5401532 (_69896 : int) : (term122 _69896) = (term122 _69896).
Proof. exact (eq_refl (term122 _69896)). Qed.
Lemma lem5401533 (_69896 : int) : ((real_of_int _69896) = term117) = ((real_of_int _69896) = term118).
Proof. exact (MK_COMB (@lem5401532 _69896) (@lem5401531)). Qed.
Lemma lem5401535 (_69896 : int) : (_69896 = term37) = ((real_of_int _69896) = term118).
Proof. exact (TRANS (@lem5401526 _69896) (@lem5401533 _69896)). Qed.
Lemma lem5401536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5401537 (_69895 : int) (_69896 : int) : (term72 _69895 _69896) = (term153 _69895 _69896).
Proof. exact (MK_COMB (@lem5401536) (@lem5401522 _69895 _69896)). Qed.
Lemma lem5401538 (_69895 : int) (_69896 : int) : (term74 _69895 _69896) = (term154 _69895 _69896).
Proof. exact (MK_COMB (@lem5401537 _69895 _69896) (@lem5401535 _69896)). Qed.
Lemma lem5401541 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5401543 (_69895 : int) (_69896 : int) : (int_le _69895 _69896) = (term114 _69895 _69896).
Proof. exact (@lem5401541 _69895 _69896). Qed.
Lemma lem5401546 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5401547 (_69896 : int) : (term70 _69896) = (term155 _69896).
Proof. exact (@lem5401546 _69896 term37). Qed.
Lemma lem5401549 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5401550 : term117 = term118.
Proof. exact (@lem5401549 (NUMERAL 0)). Qed.
Lemma lem5401551 (_69896 : int) : (term156 _69896) = (term156 _69896).
Proof. exact (eq_refl (term156 _69896)). Qed.
Lemma lem5401552 (_69896 : int) : (term155 _69896) = (term157 _69896).
Proof. exact (MK_COMB (@lem5401551 _69896) (@lem5401550)). Qed.
Lemma lem5401554 (_69896 : int) : (term70 _69896) = (term157 _69896).
Proof. exact (TRANS (@lem5401547 _69896) (@lem5401552 _69896)). Qed.
Lemma lem5401555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5401556 (_69895 : int) (_69896 : int) : (term81 _69895 _69896) = (term158 _69895 _69896).
Proof. exact (MK_COMB (@lem5401555) (@lem5401543 _69895 _69896)). Qed.
Lemma lem5401557 (_69895 : int) (_69896 : int) : (term76 _69895 _69896) = (term159 _69895 _69896).
Proof. exact (MK_COMB (@lem5401556 _69895 _69896) (@lem5401554 _69896)). Qed.
Lemma lem5401559 (y : int) (x : int) : (term160 x y) = (term161 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem5401560 (_69896 : int) : (term77 _69896) = (term162 _69896).
Proof. exact (@lem5401559 term37 _69896). Qed.
Lemma lem5401562 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5401563 (_69896 : int) : (term163 _69896) = (term164 _69896).
Proof. exact (@lem5401562 (term125 _69896) term37). Qed.
Lemma lem5401565 (x : int) (y : int) : (term126 x y) = (term127 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5401566 (_69896 : int) : (term128 _69896) = (term129 _69896).
Proof. exact (@lem5401565 _69896 term130). Qed.
Lemma lem5401568 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5401569 : term131 = term132.
Proof. exact (@lem5401568 term133). Qed.
Lemma lem5401570 (_69896 : int) : (term134 _69896) = (term134 _69896).
Proof. exact (eq_refl (term134 _69896)). Qed.
Lemma lem5401571 (_69896 : int) : (term129 _69896) = (term135 _69896).
Proof. exact (MK_COMB (@lem5401570 _69896) (@lem5401569)). Qed.
Lemma lem5401572 (_69896 : int) : (term128 _69896) = (term135 _69896).
Proof. exact (TRANS (@lem5401566 _69896) (@lem5401571 _69896)). Qed.
Lemma lem5401573 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5401574 (_69896 : int) : (term136 _69896) = (term137 _69896).
Proof. exact (MK_COMB (@lem5401573) (@lem5401572 _69896)). Qed.
Lemma lem5401576 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5401577 : term117 = term118.
Proof. exact (@lem5401576 (NUMERAL 0)). Qed.
Lemma lem5401578 (_69896 : int) : (term164 _69896) = (term165 _69896).
Proof. exact (MK_COMB (@lem5401574 _69896) (@lem5401577)). Qed.
Lemma lem5401579 (_69896 : int) : (term163 _69896) = (term165 _69896).
Proof. exact (TRANS (@lem5401563 _69896) (@lem5401578 _69896)). Qed.
Lemma lem5401580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5401581 (_69896 : int) : (term166 _69896) = (term167 _69896).
Proof. exact (MK_COMB (@lem5401580) (@lem5401579 _69896)). Qed.
Lemma lem5401583 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5401584 (_69896 : int) : (term139 _69896) = (term140 _69896).
Proof. exact (@lem5401583 term141 _69896). Qed.
Lemma lem5401586 (x : int) (y : int) : (term126 x y) = (term127 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5401587 : term142 = term143.
Proof. exact (@lem5401586 term37 term130). Qed.
Lemma lem5401589 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5401590 : term117 = term118.
Proof. exact (@lem5401589 (NUMERAL 0)). Qed.
Lemma lem5401591 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5401592 : term144 = term145.
Proof. exact (MK_COMB (@lem5401591) (@lem5401590)). Qed.
Lemma lem5401594 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5401595 : term131 = term132.
Proof. exact (@lem5401594 term133). Qed.
Lemma lem5401596 : term143 = term146.
Proof. exact (MK_COMB (@lem5401592) (@lem5401595)). Qed.
Lemma lem5401597 : term142 = term146.
Proof. exact (TRANS (@lem5401587) (@lem5401596)). Qed.
Lemma lem5401598 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5401599 : term147 = term148.
Proof. exact (MK_COMB (@lem5401598) (@lem5401597)). Qed.
Lemma lem5401600 (_69896 : int) : (real_of_int _69896) = (real_of_int _69896).
Proof. exact (eq_refl (real_of_int _69896)). Qed.
Lemma lem5401601 (_69896 : int) : (term140 _69896) = (term149 _69896).
Proof. exact (MK_COMB (@lem5401599) (@lem5401600 _69896)). Qed.
Lemma lem5401602 (_69896 : int) : (term139 _69896) = (term149 _69896).
Proof. exact (TRANS (@lem5401584 _69896) (@lem5401601 _69896)). Qed.
Lemma lem5401603 (_69896 : int) : (term162 _69896) = (term168 _69896).
Proof. exact (MK_COMB (@lem5401581 _69896) (@lem5401602 _69896)). Qed.
Lemma lem5401604 (_69896 : int) : (term77 _69896) = (term168 _69896).
Proof. exact (TRANS (@lem5401560 _69896) (@lem5401603 _69896)). Qed.
Lemma lem5401605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5401606 (_69895 : int) (_69896 : int) : (term87 _69895 _69896) = (term169 _69895 _69896).
Proof. exact (MK_COMB (@lem5401605) (@lem5401557 _69895 _69896)). Qed.
Lemma lem5401607 (_69895 : int) (_69896 : int) : (term89 _69895 _69896) = (term170 _69895 _69896).
Proof. exact (MK_COMB (@lem5401606 _69895 _69896) (@lem5401604 _69896)). Qed.
Lemma lem5401608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5401609 (_69895 : int) (_69896 : int) : (term92 _69895 _69896) = (term171 _69895 _69896).
Proof. exact (MK_COMB (@lem5401608) (@lem5401538 _69895 _69896)). Qed.
Lemma lem5401610 (_69895 : int) (_69896 : int) : (term94 _69895 _69896) = (term172 _69895 _69896).
Proof. exact (MK_COMB (@lem5401609 _69895 _69896) (@lem5401607 _69895 _69896)). Qed.
Lemma lem5401611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5401612 (_69895 : int) : (term99 _69895) = (term173 _69895).
Proof. exact (MK_COMB (@lem5401611) (@lem5401473 _69895)). Qed.
Lemma lem5401613 (_69895 : int) (_69896 : int) : (term101 _69895 _69896) = (term174 _69895 _69896).
Proof. exact (MK_COMB (@lem5401612 _69895) (@lem5401610 _69895 _69896)). Qed.
Lemma lem5401614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5401615 (_69896 : int) : (term104 _69896) = (term175 _69896).
Proof. exact (MK_COMB (@lem5401614) (@lem5401460 _69896)). Qed.
Lemma lem5401616 (_69895 : int) (_69896 : int) : (term106 _69895 _69896) = (term176 _69895 _69896).
Proof. exact (MK_COMB (@lem5401615 _69896) (@lem5401613 _69895 _69896)). Qed.
Lemma lem5401617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5401618 (_69895 : int) : (term104 _69895) = (term175 _69895).
Proof. exact (MK_COMB (@lem5401617) (@lem5401447 _69895)). Qed.
Lemma lem5401619 (_69895 : int) (_69896 : int) : (term111 _69895 _69896) = (term177 _69895 _69896).
Proof. exact (MK_COMB (@lem5401618 _69895) (@lem5401616 _69895 _69896)). Qed.
Lemma lem5401620 (_69895 : int) (_69896 : int) : (term112 _69895 _69896) = (term177 _69895 _69896).
Proof. exact (TRANS (@lem5401434 _69895 _69896) (@lem5401619 _69895 _69896)). Qed.
Lemma lem5401624 (t : Prop) : (term178 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5401720 (_69895 : int) (_69896 : int) : (term179 _69895 _69896) = (term177 _69895 _69896).
Proof. exact (@lem5401624 (term177 _69895 _69896)). Qed.
Lemma lem5401721 (_69895 : int) : (term121 _69895) = (term180 _69895).
Proof. exact (@lem1988287 (real_of_int _69895) term118). Qed.
Lemma lem5401727 (_69895 : int) : (term181 _69895) = (term182 _69895).
Proof. exact (@lem1982792 (real_of_int _69895) term118). Qed.
Lemma lem5401729 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5401730 : term118 = term184.
Proof. exact (@lem5401729 (NUMERAL 0)). Qed.
Lemma lem5401732 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5401733 : term187 = term188.
Proof. exact (@lem5401732 term133). Qed.
Lemma lem5401734 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5401735 : term189 = term190.
Proof. exact (MK_COMB (@lem5401734) (@lem5401733)). Qed.
Lemma lem5401736 : term191 = term192.
Proof. exact (MK_COMB (@lem5401735) (@lem5401730)). Qed.
Lemma lem5401737 : term192 = term193.
Proof. exact (@lem1981613 term187 term118 term132 term132). Qed.
Lemma lem5401739 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5401740 : term196 = term197.
Proof. exact (@lem5401739 term133 term133). Qed.
Lemma lem5401741 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5401742 : term199 = term133.
Proof. exact (EQ_MP (@lem5401741) (@lem940073)). Qed.
Lemma lem5401743 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5401744 : term197 = term132.
Proof. exact (MK_COMB (@lem5401743) (@lem5401742)). Qed.
Lemma lem5401745 : term196 = term132.
Proof. exact (TRANS (@lem5401740) (@lem5401744)). Qed.
Lemma lem5401747 (x : nat) : (term200 x) = term118.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5401748 : term191 = term118.
Proof. exact (@lem5401747 term133). Qed.
Lemma lem5401749 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5401750 : term201 = term202.
Proof. exact (MK_COMB (@lem5401749) (@lem5401748)). Qed.
Lemma lem5401751 : term193 = term184.
Proof. exact (MK_COMB (@lem5401750) (@lem5401745)). Qed.
Lemma lem5401752 : term192 = term184.
Proof. exact (TRANS (@lem5401737) (@lem5401751)). Qed.
Lemma lem5401753 : term191 = term184.
Proof. exact (TRANS (@lem5401736) (@lem5401752)). Qed.
Lemma lem5401755 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5401756 : term184 = term118.
Proof. exact (@lem5401755 term118). Qed.
Lemma lem5401757 : term191 = term118.
Proof. exact (TRANS (@lem5401753) (@lem5401756)). Qed.
Lemma lem5401758 (_69895 : int) : (term134 _69895) = (term134 _69895).
Proof. exact (eq_refl (term134 _69895)). Qed.
Lemma lem5401759 (_69895 : int) : (term182 _69895) = (term204 _69895).
Proof. exact (MK_COMB (@lem5401758 _69895) (@lem5401757)). Qed.
Lemma lem5401760 (_69895 : int) : (term204 _69895) = (real_of_int _69895).
Proof. exact (@lem1982723 (real_of_int _69895)). Qed.
Lemma lem5401761 (_69895 : int) : (term182 _69895) = (real_of_int _69895).
Proof. exact (TRANS (@lem5401759 _69895) (@lem5401760 _69895)). Qed.
Lemma lem5401763 (_69895 : int) : (term181 _69895) = (real_of_int _69895).
Proof. exact (TRANS (@lem5401727 _69895) (@lem5401761 _69895)). Qed.
Lemma lem5401764 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5401765 (_69895 : int) : (term205 _69895) = (term206 _69895).
Proof. exact (MK_COMB (@lem5401764) (@lem5401763 _69895)). Qed.
Lemma lem5401766 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5401767 (_69895 : int) : (term180 _69895) = (term207 _69895).
Proof. exact (MK_COMB (@lem5401765 _69895) (@lem5401766)). Qed.
Lemma lem5401768 (_69895 : int) : (term121 _69895) = (term207 _69895).
Proof. exact (TRANS (@lem5401721 _69895) (@lem5401767 _69895)). Qed.
Lemma lem5401769 (_69896 : int) : (term121 _69896) = (term180 _69896).
Proof. exact (@lem1988287 (real_of_int _69896) term118). Qed.
Lemma lem5401775 (_69896 : int) : (term181 _69896) = (term182 _69896).
Proof. exact (@lem1982792 (real_of_int _69896) term118). Qed.
Lemma lem5401777 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5401778 : term118 = term184.
Proof. exact (@lem5401777 (NUMERAL 0)). Qed.
Lemma lem5401780 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5401781 : term187 = term188.
Proof. exact (@lem5401780 term133). Qed.
Lemma lem5401782 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5401783 : term189 = term190.
Proof. exact (MK_COMB (@lem5401782) (@lem5401781)). Qed.
Lemma lem5401784 : term191 = term192.
Proof. exact (MK_COMB (@lem5401783) (@lem5401778)). Qed.
Lemma lem5401785 : term192 = term193.
Proof. exact (@lem1981613 term187 term118 term132 term132). Qed.
Lemma lem5401787 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5401788 : term196 = term197.
Proof. exact (@lem5401787 term133 term133). Qed.
Lemma lem5401789 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5401790 : term199 = term133.
Proof. exact (EQ_MP (@lem5401789) (@lem940073)). Qed.
Lemma lem5401791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5401792 : term197 = term132.
Proof. exact (MK_COMB (@lem5401791) (@lem5401790)). Qed.
Lemma lem5401793 : term196 = term132.
Proof. exact (TRANS (@lem5401788) (@lem5401792)). Qed.
Lemma lem5401795 (x : nat) : (term200 x) = term118.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5401796 : term191 = term118.
Proof. exact (@lem5401795 term133). Qed.
Lemma lem5401797 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5401798 : term201 = term202.
Proof. exact (MK_COMB (@lem5401797) (@lem5401796)). Qed.
Lemma lem5401799 : term193 = term184.
Proof. exact (MK_COMB (@lem5401798) (@lem5401793)). Qed.
Lemma lem5401800 : term192 = term184.
Proof. exact (TRANS (@lem5401785) (@lem5401799)). Qed.
Lemma lem5401801 : term191 = term184.
Proof. exact (TRANS (@lem5401784) (@lem5401800)). Qed.
Lemma lem5401803 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5401804 : term184 = term118.
Proof. exact (@lem5401803 term118). Qed.
Lemma lem5401805 : term191 = term118.
Proof. exact (TRANS (@lem5401801) (@lem5401804)). Qed.
Lemma lem5401806 (_69896 : int) : (term134 _69896) = (term134 _69896).
Proof. exact (eq_refl (term134 _69896)). Qed.
Lemma lem5401807 (_69896 : int) : (term182 _69896) = (term204 _69896).
Proof. exact (MK_COMB (@lem5401806 _69896) (@lem5401805)). Qed.
Lemma lem5401808 (_69896 : int) : (term204 _69896) = (real_of_int _69896).
Proof. exact (@lem1982723 (real_of_int _69896)). Qed.
Lemma lem5401809 (_69896 : int) : (term182 _69896) = (real_of_int _69896).
Proof. exact (TRANS (@lem5401807 _69896) (@lem5401808 _69896)). Qed.
Lemma lem5401811 (_69896 : int) : (term181 _69896) = (real_of_int _69896).
Proof. exact (TRANS (@lem5401775 _69896) (@lem5401809 _69896)). Qed.
Lemma lem5401812 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5401813 (_69896 : int) : (term205 _69896) = (term206 _69896).
Proof. exact (MK_COMB (@lem5401812) (@lem5401811 _69896)). Qed.
Lemma lem5401814 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5401815 (_69896 : int) : (term180 _69896) = (term207 _69896).
Proof. exact (MK_COMB (@lem5401813 _69896) (@lem5401814)). Qed.
Lemma lem5401816 (_69896 : int) : (term121 _69896) = (term207 _69896).
Proof. exact (TRANS (@lem5401769 _69896) (@lem5401815 _69896)). Qed.
Lemma lem5401817 (_69895 : int) : ((real_of_int _69895) = term118) = ((term181 _69895) = term118).
Proof. exact (@lem1988293 (real_of_int _69895) term118). Qed.
Lemma lem5401823 (_69895 : int) : (term181 _69895) = (term182 _69895).
Proof. exact (@lem1982792 (real_of_int _69895) term118). Qed.
Lemma lem5401825 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5401826 : term118 = term184.
Proof. exact (@lem5401825 (NUMERAL 0)). Qed.
Lemma lem5401828 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5401829 : term187 = term188.
Proof. exact (@lem5401828 term133). Qed.
Lemma lem5401830 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5401831 : term189 = term190.
Proof. exact (MK_COMB (@lem5401830) (@lem5401829)). Qed.
Lemma lem5401832 : term191 = term192.
Proof. exact (MK_COMB (@lem5401831) (@lem5401826)). Qed.
Lemma lem5401833 : term192 = term193.
Proof. exact (@lem1981613 term187 term118 term132 term132). Qed.
Lemma lem5401835 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5401836 : term196 = term197.
Proof. exact (@lem5401835 term133 term133). Qed.
Lemma lem5401837 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5401838 : term199 = term133.
Proof. exact (EQ_MP (@lem5401837) (@lem940073)). Qed.
Lemma lem5401839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5401840 : term197 = term132.
Proof. exact (MK_COMB (@lem5401839) (@lem5401838)). Qed.
Lemma lem5401841 : term196 = term132.
Proof. exact (TRANS (@lem5401836) (@lem5401840)). Qed.
Lemma lem5401843 (x : nat) : (term200 x) = term118.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5401844 : term191 = term118.
Proof. exact (@lem5401843 term133). Qed.
Lemma lem5401845 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5401846 : term201 = term202.
Proof. exact (MK_COMB (@lem5401845) (@lem5401844)). Qed.
Lemma lem5401847 : term193 = term184.
Proof. exact (MK_COMB (@lem5401846) (@lem5401841)). Qed.
Lemma lem5401848 : term192 = term184.
Proof. exact (TRANS (@lem5401833) (@lem5401847)). Qed.
Lemma lem5401849 : term191 = term184.
Proof. exact (TRANS (@lem5401832) (@lem5401848)). Qed.
Lemma lem5401851 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5401852 : term184 = term118.
Proof. exact (@lem5401851 term118). Qed.
Lemma lem5401853 : term191 = term118.
Proof. exact (TRANS (@lem5401849) (@lem5401852)). Qed.
Lemma lem5401854 (_69895 : int) : (term134 _69895) = (term134 _69895).
Proof. exact (eq_refl (term134 _69895)). Qed.
Lemma lem5401855 (_69895 : int) : (term182 _69895) = (term204 _69895).
Proof. exact (MK_COMB (@lem5401854 _69895) (@lem5401853)). Qed.
Lemma lem5401856 (_69895 : int) : (term204 _69895) = (real_of_int _69895).
Proof. exact (@lem1982723 (real_of_int _69895)). Qed.
Lemma lem5401857 (_69895 : int) : (term182 _69895) = (real_of_int _69895).
Proof. exact (TRANS (@lem5401855 _69895) (@lem5401856 _69895)). Qed.
Lemma lem5401859 (_69895 : int) : (term181 _69895) = (real_of_int _69895).
Proof. exact (TRANS (@lem5401823 _69895) (@lem5401857 _69895)). Qed.
Lemma lem5401860 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5401861 (_69895 : int) : (term208 _69895) = (term122 _69895).
Proof. exact (MK_COMB (@lem5401860) (@lem5401859 _69895)). Qed.
Lemma lem5401862 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5401863 (_69895 : int) : ((term181 _69895) = term118) = ((real_of_int _69895) = term118).
Proof. exact (MK_COMB (@lem5401861 _69895) (@lem5401862)). Qed.
Lemma lem5401864 (_69895 : int) : ((real_of_int _69895) = term118) = ((real_of_int _69895) = term118).
Proof. exact (TRANS (@lem5401817 _69895) (@lem5401863 _69895)). Qed.
Lemma lem5401865 (_69895 : int) (_69896 : int) : (term138 _69896 _69895) = (term209 _69895 _69896).
Proof. exact (@lem1988287 (real_of_int _69895) (term135 _69896)). Qed.
Lemma lem5401877 (_69895 : int) (_69896 : int) : (term210 _69895 _69896) = (term211 _69895 _69896).
Proof. exact (@lem1982792 (real_of_int _69895) (term135 _69896)). Qed.
Lemma lem5401878 (_69896 : int) : (term212 _69896) = (term213 _69896).
Proof. exact (@lem1982781 (real_of_int _69896) term187 term132). Qed.
Lemma lem5401880 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5401881 : term132 = term214.
Proof. exact (@lem5401880 term133). Qed.
Lemma lem5401883 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5401884 : term187 = term188.
Proof. exact (@lem5401883 term133). Qed.
Lemma lem5401885 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5401886 : term189 = term190.
Proof. exact (MK_COMB (@lem5401885) (@lem5401884)). Qed.
Lemma lem5401887 : term215 = term216.
Proof. exact (MK_COMB (@lem5401886) (@lem5401881)). Qed.
Lemma lem5401888 : term216 = term217.
Proof. exact (@lem1981613 term187 term132 term132 term132). Qed.
Lemma lem5401890 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5401891 : term196 = term197.
Proof. exact (@lem5401890 term133 term133). Qed.
Lemma lem5401892 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5401893 : term199 = term133.
Proof. exact (EQ_MP (@lem5401892) (@lem940073)). Qed.
Lemma lem5401894 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5401895 : term197 = term132.
Proof. exact (MK_COMB (@lem5401894) (@lem5401893)). Qed.
Lemma lem5401896 : term196 = term132.
Proof. exact (TRANS (@lem5401891) (@lem5401895)). Qed.
Lemma lem5401898 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5401899 : term215 = term220.
Proof. exact (@lem5401898 term133 term133). Qed.
Lemma lem5401900 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5401901 : term199 = term133.
Proof. exact (EQ_MP (@lem5401900) (@lem940073)). Qed.
Lemma lem5401902 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5401903 : term197 = term132.
Proof. exact (MK_COMB (@lem5401902) (@lem5401901)). Qed.
Lemma lem5401904 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5401905 : term220 = term187.
Proof. exact (MK_COMB (@lem5401904) (@lem5401903)). Qed.
Lemma lem5401906 : term215 = term187.
Proof. exact (TRANS (@lem5401899) (@lem5401905)). Qed.
Lemma lem5401907 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5401908 : term221 = term222.
Proof. exact (MK_COMB (@lem5401907) (@lem5401906)). Qed.
Lemma lem5401909 : term217 = term188.
Proof. exact (MK_COMB (@lem5401908) (@lem5401896)). Qed.
Lemma lem5401910 : term216 = term188.
Proof. exact (TRANS (@lem5401888) (@lem5401909)). Qed.
Lemma lem5401911 : term215 = term188.
Proof. exact (TRANS (@lem5401887) (@lem5401910)). Qed.
Lemma lem5401913 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5401914 : term188 = term187.
Proof. exact (@lem5401913 term187). Qed.
Lemma lem5401915 : term215 = term187.
Proof. exact (TRANS (@lem5401911) (@lem5401914)). Qed.
Lemma lem5401918 (_69896 : int) : (term223 _69896) = (term223 _69896).
Proof. exact (eq_refl (term223 _69896)). Qed.
Lemma lem5401919 (_69896 : int) : (term213 _69896) = (term224 _69896).
Proof. exact (MK_COMB (@lem5401918 _69896) (@lem5401915)). Qed.
Lemma lem5401920 (_69896 : int) : (term212 _69896) = (term224 _69896).
Proof. exact (TRANS (@lem5401878 _69896) (@lem5401919 _69896)). Qed.
Lemma lem5401921 (_69895 : int) : (term134 _69895) = (term134 _69895).
Proof. exact (eq_refl (term134 _69895)). Qed.
Lemma lem5401924 (_69895 : int) (_69896 : int) : (term211 _69895 _69896) = (term225 _69895 _69896).
Proof. exact (MK_COMB (@lem5401921 _69895) (@lem5401920 _69896)). Qed.
Lemma lem5401926 (_69895 : int) (_69896 : int) : (term210 _69895 _69896) = (term225 _69895 _69896).
Proof. exact (TRANS (@lem5401877 _69895 _69896) (@lem5401924 _69895 _69896)). Qed.
Lemma lem5401927 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5401928 (_69895 : int) (_69896 : int) : (term226 _69895 _69896) = (term227 _69895 _69896).
Proof. exact (MK_COMB (@lem5401927) (@lem5401926 _69895 _69896)). Qed.
Lemma lem5401929 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5401930 (_69895 : int) (_69896 : int) : (term209 _69895 _69896) = (term228 _69895 _69896).
Proof. exact (MK_COMB (@lem5401928 _69895 _69896) (@lem5401929)). Qed.
Lemma lem5401931 (_69895 : int) (_69896 : int) : (term138 _69896 _69895) = (term228 _69895 _69896).
Proof. exact (TRANS (@lem5401865 _69895 _69896) (@lem5401930 _69895 _69896)). Qed.
Lemma lem5401932 (_69896 : int) : (term149 _69896) = (term229 _69896).
Proof. exact (@lem1988287 (real_of_int _69896) term146). Qed.
Lemma lem5401939 : term146 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem5401942 (_69896 : int) : (term230 _69896) = (term230 _69896).
Proof. exact (eq_refl (term230 _69896)). Qed.
Lemma lem5401943 (_69896 : int) : (term231 _69896) = (term232 _69896).
Proof. exact (MK_COMB (@lem5401942 _69896) (@lem5401939)). Qed.
Lemma lem5401944 (_69896 : int) : (term232 _69896) = (term233 _69896).
Proof. exact (@lem1982792 (real_of_int _69896) term132). Qed.
Lemma lem5401946 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5401947 : term132 = term214.
Proof. exact (@lem5401946 term133). Qed.
Lemma lem5401949 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5401950 : term187 = term188.
Proof. exact (@lem5401949 term133). Qed.
Lemma lem5401951 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5401952 : term189 = term190.
Proof. exact (MK_COMB (@lem5401951) (@lem5401950)). Qed.
Lemma lem5401953 : term215 = term216.
Proof. exact (MK_COMB (@lem5401952) (@lem5401947)). Qed.
Lemma lem5401954 : term216 = term217.
Proof. exact (@lem1981613 term187 term132 term132 term132). Qed.
Lemma lem5401956 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5401957 : term196 = term197.
Proof. exact (@lem5401956 term133 term133). Qed.
Lemma lem5401958 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5401959 : term199 = term133.
Proof. exact (EQ_MP (@lem5401958) (@lem940073)). Qed.
Lemma lem5401960 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5401961 : term197 = term132.
Proof. exact (MK_COMB (@lem5401960) (@lem5401959)). Qed.
Lemma lem5401962 : term196 = term132.
Proof. exact (TRANS (@lem5401957) (@lem5401961)). Qed.
Lemma lem5401964 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5401965 : term215 = term220.
Proof. exact (@lem5401964 term133 term133). Qed.
Lemma lem5401966 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5401967 : term199 = term133.
Proof. exact (EQ_MP (@lem5401966) (@lem940073)). Qed.
Lemma lem5401968 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5401969 : term197 = term132.
Proof. exact (MK_COMB (@lem5401968) (@lem5401967)). Qed.
Lemma lem5401970 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5401971 : term220 = term187.
Proof. exact (MK_COMB (@lem5401970) (@lem5401969)). Qed.
Lemma lem5401972 : term215 = term187.
Proof. exact (TRANS (@lem5401965) (@lem5401971)). Qed.
Lemma lem5401973 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5401974 : term221 = term222.
Proof. exact (MK_COMB (@lem5401973) (@lem5401972)). Qed.
Lemma lem5401975 : term217 = term188.
Proof. exact (MK_COMB (@lem5401974) (@lem5401962)). Qed.
Lemma lem5401976 : term216 = term188.
Proof. exact (TRANS (@lem5401954) (@lem5401975)). Qed.
Lemma lem5401977 : term215 = term188.
Proof. exact (TRANS (@lem5401953) (@lem5401976)). Qed.
Lemma lem5401979 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5401980 : term188 = term187.
Proof. exact (@lem5401979 term187). Qed.
Lemma lem5401981 : term215 = term187.
Proof. exact (TRANS (@lem5401977) (@lem5401980)). Qed.
Lemma lem5401982 (_69896 : int) : (term134 _69896) = (term134 _69896).
Proof. exact (eq_refl (term134 _69896)). Qed.
Lemma lem5401985 (_69896 : int) : (term233 _69896) = (term234 _69896).
Proof. exact (MK_COMB (@lem5401982 _69896) (@lem5401981)). Qed.
Lemma lem5401986 (_69896 : int) : (term232 _69896) = (term234 _69896).
Proof. exact (TRANS (@lem5401944 _69896) (@lem5401985 _69896)). Qed.
Lemma lem5401987 (_69896 : int) : (term231 _69896) = (term234 _69896).
Proof. exact (TRANS (@lem5401943 _69896) (@lem5401986 _69896)). Qed.
Lemma lem5401988 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5401989 (_69896 : int) : (term235 _69896) = (term236 _69896).
Proof. exact (MK_COMB (@lem5401988) (@lem5401987 _69896)). Qed.
Lemma lem5401990 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5401991 (_69896 : int) : (term229 _69896) = (term237 _69896).
Proof. exact (MK_COMB (@lem5401989 _69896) (@lem5401990)). Qed.
Lemma lem5401992 (_69896 : int) : (term149 _69896) = (term237 _69896).
Proof. exact (TRANS (@lem5401932 _69896) (@lem5401991 _69896)). Qed.
Lemma lem5401993 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5401994 (_69895 : int) (_69896 : int) : (term151 _69896 _69895) = (term238 _69895 _69896).
Proof. exact (MK_COMB (@lem5401993) (@lem5401931 _69895 _69896)). Qed.
Lemma lem5401995 (_69895 : int) (_69896 : int) : (term152 _69895 _69896) = (term239 _69895 _69896).
Proof. exact (MK_COMB (@lem5401994 _69895 _69896) (@lem5401992 _69896)). Qed.
Lemma lem5401996 (_69896 : int) : ((real_of_int _69896) = term118) = ((term181 _69896) = term118).
Proof. exact (@lem1988293 (real_of_int _69896) term118). Qed.
Lemma lem5402002 (_69896 : int) : (term181 _69896) = (term182 _69896).
Proof. exact (@lem1982792 (real_of_int _69896) term118). Qed.
Lemma lem5402004 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402005 : term118 = term184.
Proof. exact (@lem5402004 (NUMERAL 0)). Qed.
Lemma lem5402007 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5402008 : term187 = term188.
Proof. exact (@lem5402007 term133). Qed.
Lemma lem5402009 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5402010 : term189 = term190.
Proof. exact (MK_COMB (@lem5402009) (@lem5402008)). Qed.
Lemma lem5402011 : term191 = term192.
Proof. exact (MK_COMB (@lem5402010) (@lem5402005)). Qed.
Lemma lem5402012 : term192 = term193.
Proof. exact (@lem1981613 term187 term118 term132 term132). Qed.
Lemma lem5402014 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5402015 : term196 = term197.
Proof. exact (@lem5402014 term133 term133). Qed.
Lemma lem5402016 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402017 : term199 = term133.
Proof. exact (EQ_MP (@lem5402016) (@lem940073)). Qed.
Lemma lem5402018 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402019 : term197 = term132.
Proof. exact (MK_COMB (@lem5402018) (@lem5402017)). Qed.
Lemma lem5402020 : term196 = term132.
Proof. exact (TRANS (@lem5402015) (@lem5402019)). Qed.
Lemma lem5402022 (x : nat) : (term200 x) = term118.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5402023 : term191 = term118.
Proof. exact (@lem5402022 term133). Qed.
Lemma lem5402024 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5402025 : term201 = term202.
Proof. exact (MK_COMB (@lem5402024) (@lem5402023)). Qed.
Lemma lem5402026 : term193 = term184.
Proof. exact (MK_COMB (@lem5402025) (@lem5402020)). Qed.
Lemma lem5402027 : term192 = term184.
Proof. exact (TRANS (@lem5402012) (@lem5402026)). Qed.
Lemma lem5402028 : term191 = term184.
Proof. exact (TRANS (@lem5402011) (@lem5402027)). Qed.
Lemma lem5402030 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5402031 : term184 = term118.
Proof. exact (@lem5402030 term118). Qed.
Lemma lem5402032 : term191 = term118.
Proof. exact (TRANS (@lem5402028) (@lem5402031)). Qed.
Lemma lem5402033 (_69896 : int) : (term134 _69896) = (term134 _69896).
Proof. exact (eq_refl (term134 _69896)). Qed.
Lemma lem5402034 (_69896 : int) : (term182 _69896) = (term204 _69896).
Proof. exact (MK_COMB (@lem5402033 _69896) (@lem5402032)). Qed.
Lemma lem5402035 (_69896 : int) : (term204 _69896) = (real_of_int _69896).
Proof. exact (@lem1982723 (real_of_int _69896)). Qed.
Lemma lem5402036 (_69896 : int) : (term182 _69896) = (real_of_int _69896).
Proof. exact (TRANS (@lem5402034 _69896) (@lem5402035 _69896)). Qed.
Lemma lem5402038 (_69896 : int) : (term181 _69896) = (real_of_int _69896).
Proof. exact (TRANS (@lem5402002 _69896) (@lem5402036 _69896)). Qed.
Lemma lem5402039 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5402040 (_69896 : int) : (term208 _69896) = (term122 _69896).
Proof. exact (MK_COMB (@lem5402039) (@lem5402038 _69896)). Qed.
Lemma lem5402041 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5402042 (_69896 : int) : ((term181 _69896) = term118) = ((real_of_int _69896) = term118).
Proof. exact (MK_COMB (@lem5402040 _69896) (@lem5402041)). Qed.
Lemma lem5402043 (_69896 : int) : ((real_of_int _69896) = term118) = ((real_of_int _69896) = term118).
Proof. exact (TRANS (@lem5401996 _69896) (@lem5402042 _69896)). Qed.
Lemma lem5402044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5402045 (_69895 : int) (_69896 : int) : (term153 _69895 _69896) = (term240 _69895 _69896).
Proof. exact (MK_COMB (@lem5402044) (@lem5401995 _69895 _69896)). Qed.
Lemma lem5402046 (_69895 : int) (_69896 : int) : (term154 _69895 _69896) = (term241 _69895 _69896).
Proof. exact (MK_COMB (@lem5402045 _69895 _69896) (@lem5402043 _69896)). Qed.
Lemma lem5402047 (_69896 : int) (_69895 : int) : (term114 _69895 _69896) = (term242 _69896 _69895).
Proof. exact (@lem1988287 (real_of_int _69896) (real_of_int _69895)). Qed.
Lemma lem5402053 (_69896 : int) (_69895 : int) : (term243 _69896 _69895) = (term244 _69896 _69895).
Proof. exact (@lem1982792 (real_of_int _69896) (real_of_int _69895)). Qed.
Lemma lem5402058 (_69895 : int) (_69896 : int) : (term244 _69896 _69895) = (term245 _69895 _69896).
Proof. exact (@lem1982761 (term246 _69895) (real_of_int _69896)). Qed.
Lemma lem5402060 (_69895 : int) (_69896 : int) : (term243 _69896 _69895) = (term245 _69895 _69896).
Proof. exact (TRANS (@lem5402053 _69896 _69895) (@lem5402058 _69895 _69896)). Qed.
Lemma lem5402061 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5402062 (_69895 : int) (_69896 : int) : (term247 _69896 _69895) = (term248 _69895 _69896).
Proof. exact (MK_COMB (@lem5402061) (@lem5402060 _69895 _69896)). Qed.
Lemma lem5402063 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5402064 (_69895 : int) (_69896 : int) : (term242 _69896 _69895) = (term249 _69895 _69896).
Proof. exact (MK_COMB (@lem5402062 _69895 _69896) (@lem5402063)). Qed.
Lemma lem5402065 (_69895 : int) (_69896 : int) : (term114 _69895 _69896) = (term249 _69895 _69896).
Proof. exact (TRANS (@lem5402047 _69896 _69895) (@lem5402064 _69895 _69896)). Qed.
Lemma lem5402066 (_69896 : int) : (term157 _69896) = (term250 _69896).
Proof. exact (@lem1988287 term118 (real_of_int _69896)). Qed.
Lemma lem5402072 (_69896 : int) : (term251 _69896) = (term252 _69896).
Proof. exact (@lem1982792 term118 (real_of_int _69896)). Qed.
Lemma lem5402077 (_69896 : int) : (term252 _69896) = (term246 _69896).
Proof. exact (@lem1982721 (term246 _69896)). Qed.
Lemma lem5402079 (_69896 : int) : (term251 _69896) = (term246 _69896).
Proof. exact (TRANS (@lem5402072 _69896) (@lem5402077 _69896)). Qed.
Lemma lem5402080 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5402081 (_69896 : int) : (term253 _69896) = (term254 _69896).
Proof. exact (MK_COMB (@lem5402080) (@lem5402079 _69896)). Qed.
Lemma lem5402082 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5402083 (_69896 : int) : (term250 _69896) = (term255 _69896).
Proof. exact (MK_COMB (@lem5402081 _69896) (@lem5402082)). Qed.
Lemma lem5402084 (_69896 : int) : (term157 _69896) = (term255 _69896).
Proof. exact (TRANS (@lem5402066 _69896) (@lem5402083 _69896)). Qed.
Lemma lem5402085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5402086 (_69895 : int) (_69896 : int) : (term158 _69895 _69896) = (term256 _69895 _69896).
Proof. exact (MK_COMB (@lem5402085) (@lem5402065 _69895 _69896)). Qed.
Lemma lem5402087 (_69895 : int) (_69896 : int) : (term159 _69895 _69896) = (term257 _69895 _69896).
Proof. exact (MK_COMB (@lem5402086 _69895 _69896) (@lem5402084 _69896)). Qed.
Lemma lem5402088 (_69896 : int) : (term165 _69896) = (term258 _69896).
Proof. exact (@lem1988287 term118 (term135 _69896)). Qed.
Lemma lem5402100 (_69896 : int) : (term259 _69896) = (term260 _69896).
Proof. exact (@lem1982792 term118 (term135 _69896)). Qed.
Lemma lem5402101 (_69896 : int) : (term212 _69896) = (term213 _69896).
Proof. exact (@lem1982781 (real_of_int _69896) term187 term132). Qed.
Lemma lem5402103 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402104 : term132 = term214.
Proof. exact (@lem5402103 term133). Qed.
Lemma lem5402106 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5402107 : term187 = term188.
Proof. exact (@lem5402106 term133). Qed.
Lemma lem5402108 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5402109 : term189 = term190.
Proof. exact (MK_COMB (@lem5402108) (@lem5402107)). Qed.
Lemma lem5402110 : term215 = term216.
Proof. exact (MK_COMB (@lem5402109) (@lem5402104)). Qed.
Lemma lem5402111 : term216 = term217.
Proof. exact (@lem1981613 term187 term132 term132 term132). Qed.
Lemma lem5402113 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5402114 : term196 = term197.
Proof. exact (@lem5402113 term133 term133). Qed.
Lemma lem5402115 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402116 : term199 = term133.
Proof. exact (EQ_MP (@lem5402115) (@lem940073)). Qed.
Lemma lem5402117 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402118 : term197 = term132.
Proof. exact (MK_COMB (@lem5402117) (@lem5402116)). Qed.
Lemma lem5402119 : term196 = term132.
Proof. exact (TRANS (@lem5402114) (@lem5402118)). Qed.
Lemma lem5402121 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5402122 : term215 = term220.
Proof. exact (@lem5402121 term133 term133). Qed.
Lemma lem5402123 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402124 : term199 = term133.
Proof. exact (EQ_MP (@lem5402123) (@lem940073)). Qed.
Lemma lem5402125 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402126 : term197 = term132.
Proof. exact (MK_COMB (@lem5402125) (@lem5402124)). Qed.
Lemma lem5402127 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5402128 : term220 = term187.
Proof. exact (MK_COMB (@lem5402127) (@lem5402126)). Qed.
Lemma lem5402129 : term215 = term187.
Proof. exact (TRANS (@lem5402122) (@lem5402128)). Qed.
Lemma lem5402130 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5402131 : term221 = term222.
Proof. exact (MK_COMB (@lem5402130) (@lem5402129)). Qed.
Lemma lem5402132 : term217 = term188.
Proof. exact (MK_COMB (@lem5402131) (@lem5402119)). Qed.
Lemma lem5402133 : term216 = term188.
Proof. exact (TRANS (@lem5402111) (@lem5402132)). Qed.
Lemma lem5402134 : term215 = term188.
Proof. exact (TRANS (@lem5402110) (@lem5402133)). Qed.
Lemma lem5402136 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5402137 : term188 = term187.
Proof. exact (@lem5402136 term187). Qed.
Lemma lem5402138 : term215 = term187.
Proof. exact (TRANS (@lem5402134) (@lem5402137)). Qed.
Lemma lem5402141 (_69896 : int) : (term223 _69896) = (term223 _69896).
Proof. exact (eq_refl (term223 _69896)). Qed.
Lemma lem5402142 (_69896 : int) : (term213 _69896) = (term224 _69896).
Proof. exact (MK_COMB (@lem5402141 _69896) (@lem5402138)). Qed.
Lemma lem5402143 (_69896 : int) : (term212 _69896) = (term224 _69896).
Proof. exact (TRANS (@lem5402101 _69896) (@lem5402142 _69896)). Qed.
Lemma lem5402144 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem5402145 (_69896 : int) : (term260 _69896) = (term261 _69896).
Proof. exact (MK_COMB (@lem5402144) (@lem5402143 _69896)). Qed.
Lemma lem5402146 (_69896 : int) : (term261 _69896) = (term224 _69896).
Proof. exact (@lem1982721 (term224 _69896)). Qed.
Lemma lem5402147 (_69896 : int) : (term260 _69896) = (term224 _69896).
Proof. exact (TRANS (@lem5402145 _69896) (@lem5402146 _69896)). Qed.
Lemma lem5402149 (_69896 : int) : (term259 _69896) = (term224 _69896).
Proof. exact (TRANS (@lem5402100 _69896) (@lem5402147 _69896)). Qed.
Lemma lem5402150 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5402151 (_69896 : int) : (term262 _69896) = (term263 _69896).
Proof. exact (MK_COMB (@lem5402150) (@lem5402149 _69896)). Qed.
Lemma lem5402152 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5402153 (_69896 : int) : (term258 _69896) = (term264 _69896).
Proof. exact (MK_COMB (@lem5402151 _69896) (@lem5402152)). Qed.
Lemma lem5402154 (_69896 : int) : (term165 _69896) = (term264 _69896).
Proof. exact (TRANS (@lem5402088 _69896) (@lem5402153 _69896)). Qed.
Lemma lem5402155 (_69896 : int) : (term149 _69896) = (term229 _69896).
Proof. exact (@lem1988287 (real_of_int _69896) term146). Qed.
Lemma lem5402162 : term146 = term132.
Proof. exact (@lem1982721 term132). Qed.
Lemma lem5402165 (_69896 : int) : (term230 _69896) = (term230 _69896).
Proof. exact (eq_refl (term230 _69896)). Qed.
Lemma lem5402166 (_69896 : int) : (term231 _69896) = (term232 _69896).
Proof. exact (MK_COMB (@lem5402165 _69896) (@lem5402162)). Qed.
Lemma lem5402167 (_69896 : int) : (term232 _69896) = (term233 _69896).
Proof. exact (@lem1982792 (real_of_int _69896) term132). Qed.
Lemma lem5402169 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402170 : term132 = term214.
Proof. exact (@lem5402169 term133). Qed.
Lemma lem5402172 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5402173 : term187 = term188.
Proof. exact (@lem5402172 term133). Qed.
Lemma lem5402174 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5402175 : term189 = term190.
Proof. exact (MK_COMB (@lem5402174) (@lem5402173)). Qed.
Lemma lem5402176 : term215 = term216.
Proof. exact (MK_COMB (@lem5402175) (@lem5402170)). Qed.
Lemma lem5402177 : term216 = term217.
Proof. exact (@lem1981613 term187 term132 term132 term132). Qed.
Lemma lem5402179 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5402180 : term196 = term197.
Proof. exact (@lem5402179 term133 term133). Qed.
Lemma lem5402181 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402182 : term199 = term133.
Proof. exact (EQ_MP (@lem5402181) (@lem940073)). Qed.
Lemma lem5402183 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402184 : term197 = term132.
Proof. exact (MK_COMB (@lem5402183) (@lem5402182)). Qed.
Lemma lem5402185 : term196 = term132.
Proof. exact (TRANS (@lem5402180) (@lem5402184)). Qed.
Lemma lem5402187 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5402188 : term215 = term220.
Proof. exact (@lem5402187 term133 term133). Qed.
Lemma lem5402189 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402190 : term199 = term133.
Proof. exact (EQ_MP (@lem5402189) (@lem940073)). Qed.
Lemma lem5402191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402192 : term197 = term132.
Proof. exact (MK_COMB (@lem5402191) (@lem5402190)). Qed.
Lemma lem5402193 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5402194 : term220 = term187.
Proof. exact (MK_COMB (@lem5402193) (@lem5402192)). Qed.
Lemma lem5402195 : term215 = term187.
Proof. exact (TRANS (@lem5402188) (@lem5402194)). Qed.
Lemma lem5402196 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5402197 : term221 = term222.
Proof. exact (MK_COMB (@lem5402196) (@lem5402195)). Qed.
Lemma lem5402198 : term217 = term188.
Proof. exact (MK_COMB (@lem5402197) (@lem5402185)). Qed.
Lemma lem5402199 : term216 = term188.
Proof. exact (TRANS (@lem5402177) (@lem5402198)). Qed.
Lemma lem5402200 : term215 = term188.
Proof. exact (TRANS (@lem5402176) (@lem5402199)). Qed.
Lemma lem5402202 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5402203 : term188 = term187.
Proof. exact (@lem5402202 term187). Qed.
Lemma lem5402204 : term215 = term187.
Proof. exact (TRANS (@lem5402200) (@lem5402203)). Qed.
Lemma lem5402205 (_69896 : int) : (term134 _69896) = (term134 _69896).
Proof. exact (eq_refl (term134 _69896)). Qed.
Lemma lem5402208 (_69896 : int) : (term233 _69896) = (term234 _69896).
Proof. exact (MK_COMB (@lem5402205 _69896) (@lem5402204)). Qed.
Lemma lem5402209 (_69896 : int) : (term232 _69896) = (term234 _69896).
Proof. exact (TRANS (@lem5402167 _69896) (@lem5402208 _69896)). Qed.
Lemma lem5402210 (_69896 : int) : (term231 _69896) = (term234 _69896).
Proof. exact (TRANS (@lem5402166 _69896) (@lem5402209 _69896)). Qed.
Lemma lem5402211 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5402212 (_69896 : int) : (term235 _69896) = (term236 _69896).
Proof. exact (MK_COMB (@lem5402211) (@lem5402210 _69896)). Qed.
Lemma lem5402213 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5402214 (_69896 : int) : (term229 _69896) = (term237 _69896).
Proof. exact (MK_COMB (@lem5402212 _69896) (@lem5402213)). Qed.
Lemma lem5402215 (_69896 : int) : (term149 _69896) = (term237 _69896).
Proof. exact (TRANS (@lem5402155 _69896) (@lem5402214 _69896)). Qed.
Lemma lem5402216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5402217 (_69896 : int) : (term167 _69896) = (term265 _69896).
Proof. exact (MK_COMB (@lem5402216) (@lem5402154 _69896)). Qed.
Lemma lem5402218 (_69896 : int) : (term168 _69896) = (term266 _69896).
Proof. exact (MK_COMB (@lem5402217 _69896) (@lem5402215 _69896)). Qed.
Lemma lem5402219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5402220 (_69895 : int) (_69896 : int) : (term169 _69895 _69896) = (term267 _69895 _69896).
Proof. exact (MK_COMB (@lem5402219) (@lem5402087 _69895 _69896)). Qed.
Lemma lem5402221 (_69895 : int) (_69896 : int) : (term170 _69895 _69896) = (term268 _69895 _69896).
Proof. exact (MK_COMB (@lem5402220 _69895 _69896) (@lem5402218 _69896)). Qed.
Lemma lem5402222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5402223 (_69895 : int) (_69896 : int) : (term171 _69895 _69896) = (term269 _69895 _69896).
Proof. exact (MK_COMB (@lem5402222) (@lem5402046 _69895 _69896)). Qed.
Lemma lem5402224 (_69895 : int) (_69896 : int) : (term172 _69895 _69896) = (term270 _69895 _69896).
Proof. exact (MK_COMB (@lem5402223 _69895 _69896) (@lem5402221 _69895 _69896)). Qed.
Lemma lem5402225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5402226 (_69895 : int) : (term173 _69895) = (term173 _69895).
Proof. exact (MK_COMB (@lem5402225) (@lem5401864 _69895)). Qed.
Lemma lem5402227 (_69895 : int) (_69896 : int) : (term174 _69895 _69896) = (term271 _69895 _69896).
Proof. exact (MK_COMB (@lem5402226 _69895) (@lem5402224 _69895 _69896)). Qed.
Lemma lem5402228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5402229 (_69896 : int) : (term175 _69896) = (term272 _69896).
Proof. exact (MK_COMB (@lem5402228) (@lem5401816 _69896)). Qed.
Lemma lem5402230 (_69895 : int) (_69896 : int) : (term176 _69895 _69896) = (term273 _69895 _69896).
Proof. exact (MK_COMB (@lem5402229 _69896) (@lem5402227 _69895 _69896)). Qed.
Lemma lem5402231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5402232 (_69895 : int) : (term175 _69895) = (term272 _69895).
Proof. exact (MK_COMB (@lem5402231) (@lem5401768 _69895)). Qed.
Lemma lem5402233 (_69895 : int) (_69896 : int) : (term177 _69895 _69896) = (term274 _69895 _69896).
Proof. exact (MK_COMB (@lem5402232 _69895) (@lem5402230 _69895 _69896)). Qed.
Lemma lem5402240 (_69895 : int) (_69896 : int) : (term179 _69895 _69896) = (term274 _69895 _69896).
Proof. exact (TRANS (@lem5401720 _69895 _69896) (@lem5402233 _69895 _69896)). Qed.
Lemma lem5402263 (_69895 : int) (_69896 : int) : (term268 _69895 _69896) = (term275 _69895 _69896).
Proof. exact (@lem19158 (term264 _69896) (term257 _69895 _69896) (term237 _69896)). Qed.
Lemma lem5402280 (_69895 : int) (_69896 : int) : (term241 _69895 _69896) = (term276 _69895 _69896).
Proof. exact (@lem19367 (term228 _69895 _69896) (term237 _69896) ((real_of_int _69896) = term118)). Qed.
Lemma lem5402281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5402282 (_69895 : int) (_69896 : int) : (term269 _69895 _69896) = (term277 _69895 _69896).
Proof. exact (MK_COMB (@lem5402281) (@lem5402280 _69895 _69896)). Qed.
Lemma lem5402283 (_69895 : int) (_69896 : int) : (term270 _69895 _69896) = (term278 _69895 _69896).
Proof. exact (MK_COMB (@lem5402282 _69895 _69896) (@lem5402263 _69895 _69896)). Qed.
Lemma lem5402286 (_69895 : int) : (term173 _69895) = (term173 _69895).
Proof. exact (eq_refl (term173 _69895)). Qed.
Lemma lem5402287 (_69895 : int) (_69896 : int) : (term271 _69895 _69896) = (term279 _69895 _69896).
Proof. exact (MK_COMB (@lem5402286 _69895) (@lem5402283 _69895 _69896)). Qed.
Lemma lem5402288 (_69895 : int) (_69896 : int) : (term279 _69895 _69896) = (term280 _69895 _69896).
Proof. exact (@lem19158 (term276 _69895 _69896) ((real_of_int _69895) = term118) (term275 _69895 _69896)). Qed.
Lemma lem5402295 (_69895 : int) (_69896 : int) : (term281 _69895 _69896) = (term282 _69895 _69896).
Proof. exact (@lem19158 (term283 _69895 _69896) ((real_of_int _69895) = term118) (term284 _69895 _69896)). Qed.
Lemma lem5402302 (_69895 : int) (_69896 : int) : (term285 _69895 _69896) = (term286 _69895 _69896).
Proof. exact (@lem19158 (term287 _69895 _69896) ((real_of_int _69895) = term118) (term288 _69896)). Qed.
Lemma lem5402303 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5402304 (_69895 : int) (_69896 : int) : (term289 _69895 _69896) = (term290 _69895 _69896).
Proof. exact (MK_COMB (@lem5402303) (@lem5402302 _69895 _69896)). Qed.
Lemma lem5402305 (_69895 : int) (_69896 : int) : (term280 _69895 _69896) = (term291 _69895 _69896).
Proof. exact (MK_COMB (@lem5402304 _69895 _69896) (@lem5402295 _69895 _69896)). Qed.
Lemma lem5402306 (_69895 : int) (_69896 : int) : (term279 _69895 _69896) = (term291 _69895 _69896).
Proof. exact (TRANS (@lem5402288 _69895 _69896) (@lem5402305 _69895 _69896)). Qed.
Lemma lem5402307 (_69895 : int) (_69896 : int) : (term271 _69895 _69896) = (term291 _69895 _69896).
Proof. exact (TRANS (@lem5402287 _69895 _69896) (@lem5402306 _69895 _69896)). Qed.
Lemma lem5402310 (_69896 : int) : (term272 _69896) = (term272 _69896).
Proof. exact (eq_refl (term272 _69896)). Qed.
Lemma lem5402311 (_69895 : int) (_69896 : int) : (term273 _69895 _69896) = (term292 _69895 _69896).
Proof. exact (MK_COMB (@lem5402310 _69896) (@lem5402307 _69895 _69896)). Qed.
Lemma lem5402312 (_69895 : int) (_69896 : int) : (term292 _69895 _69896) = (term293 _69895 _69896).
Proof. exact (@lem19158 (term286 _69895 _69896) (term207 _69896) (term282 _69895 _69896)). Qed.
Lemma lem5402319 (_69895 : int) (_69896 : int) : (term294 _69895 _69896) = (term295 _69895 _69896).
Proof. exact (@lem19158 (term296 _69895 _69896) (term207 _69896) (term297 _69895 _69896)). Qed.
Lemma lem5402326 (_69895 : int) (_69896 : int) : (term298 _69895 _69896) = (term299 _69895 _69896).
Proof. exact (@lem19158 (term300 _69895 _69896) (term207 _69896) (term301 _69895 _69896)). Qed.
Lemma lem5402327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5402328 (_69895 : int) (_69896 : int) : (term302 _69895 _69896) = (term303 _69895 _69896).
Proof. exact (MK_COMB (@lem5402327) (@lem5402326 _69895 _69896)). Qed.
Lemma lem5402329 (_69895 : int) (_69896 : int) : (term293 _69895 _69896) = (term304 _69895 _69896).
Proof. exact (MK_COMB (@lem5402328 _69895 _69896) (@lem5402319 _69895 _69896)). Qed.
Lemma lem5402330 (_69895 : int) (_69896 : int) : (term292 _69895 _69896) = (term304 _69895 _69896).
Proof. exact (TRANS (@lem5402312 _69895 _69896) (@lem5402329 _69895 _69896)). Qed.
Lemma lem5402331 (_69895 : int) (_69896 : int) : (term273 _69895 _69896) = (term304 _69895 _69896).
Proof. exact (TRANS (@lem5402311 _69895 _69896) (@lem5402330 _69895 _69896)). Qed.
Lemma lem5402334 (_69895 : int) : (term272 _69895) = (term272 _69895).
Proof. exact (eq_refl (term272 _69895)). Qed.
Lemma lem5402335 (_69895 : int) (_69896 : int) : (term274 _69895 _69896) = (term305 _69895 _69896).
Proof. exact (MK_COMB (@lem5402334 _69895) (@lem5402331 _69895 _69896)). Qed.
Lemma lem5402336 (_69895 : int) (_69896 : int) : (term305 _69895 _69896) = (term306 _69895 _69896).
Proof. exact (@lem19158 (term299 _69895 _69896) (term207 _69895) (term295 _69895 _69896)). Qed.
Lemma lem5402343 (_69895 : int) (_69896 : int) : (term307 _69895 _69896) = (term308 _69895 _69896).
Proof. exact (@lem19158 (term309 _69895 _69896) (term207 _69895) (term310 _69895 _69896)). Qed.
Lemma lem5402350 (_69895 : int) (_69896 : int) : (term311 _69895 _69896) = (term312 _69895 _69896).
Proof. exact (@lem19158 (term313 _69895 _69896) (term207 _69895) (term314 _69895 _69896)). Qed.
Lemma lem5402351 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5402352 (_69895 : int) (_69896 : int) : (term315 _69895 _69896) = (term316 _69895 _69896).
Proof. exact (MK_COMB (@lem5402351) (@lem5402350 _69895 _69896)). Qed.
Lemma lem5402353 (_69895 : int) (_69896 : int) : (term306 _69895 _69896) = (term317 _69895 _69896).
Proof. exact (MK_COMB (@lem5402352 _69895 _69896) (@lem5402343 _69895 _69896)). Qed.
Lemma lem5402354 (_69895 : int) (_69896 : int) : (term305 _69895 _69896) = (term317 _69895 _69896).
Proof. exact (TRANS (@lem5402336 _69895 _69896) (@lem5402353 _69895 _69896)). Qed.
Lemma lem5402355 (_69895 : int) (_69896 : int) : (term274 _69895 _69896) = (term317 _69895 _69896).
Proof. exact (TRANS (@lem5402335 _69895 _69896) (@lem5402354 _69895 _69896)). Qed.
Lemma lem5402356 (_69895 : int) (_69896 : int) : (term179 _69895 _69896) = (term317 _69895 _69896).
Proof. exact (TRANS (@lem5402240 _69895 _69896) (@lem5402355 _69895 _69896)). Qed.
Lemma lem5402378 (_69895 : int) (_69896 : int) (h1 : term317 _69895 _69896) : term317 _69895 _69896.
Proof. exact (h1). Qed.
Lemma lem5402379 (_69895 : int) (_69896 : int) (h1 : term312 _69895 _69896) : term312 _69895 _69896.
Proof. exact (h1). Qed.
Lemma lem5402380 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term318 _69895 _69896.
Proof. exact (h1). Qed.
Lemma lem5402381 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term313 _69895 _69896.
Proof. exact (proj2 (@lem5402380 _69895 _69896 h1)). Qed.
Lemma lem5402383 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term300 _69895 _69896.
Proof. exact (proj2 (@lem5402381 _69895 _69896 h1)). Qed.
Lemma lem5402385 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term287 _69895 _69896.
Proof. exact (proj2 (@lem5402383 _69895 _69896 h1)). Qed.
Lemma lem5402386 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : (real_of_int _69895) = term118.
Proof. exact (proj1 (@lem5402383 _69895 _69896 h1)). Qed.
Lemma lem5402387 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : (real_of_int _69896) = term118.
Proof. exact (proj2 (@lem5402385 _69895 _69896 h1)). Qed.
Lemma lem5402388 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term228 _69895 _69896.
Proof. exact (proj1 (@lem5402385 _69895 _69896 h1)). Qed.
Lemma lem5402390 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5402391 : term319 = term320.
Proof. exact (@lem5402390 term118 term132). Qed.
Lemma lem5402393 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402394 : term132 = term214.
Proof. exact (@lem5402393 term133). Qed.
Lemma lem5402396 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402397 : term118 = term184.
Proof. exact (@lem5402396 (NUMERAL 0)). Qed.
Lemma lem5402398 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5402399 : term321 = term322.
Proof. exact (MK_COMB (@lem5402398) (@lem5402397)). Qed.
Lemma lem5402400 : term320 = term323.
Proof. exact (MK_COMB (@lem5402399) (@lem5402394)). Qed.
Lemma lem5402401 : term324.
Proof. exact (@lem1980255 term118 term132 term132 term132). Qed.
Lemma lem5402403 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402404 : term320 = term326.
Proof. exact (@lem5402403 (NUMERAL 0) term133). Qed.
Lemma lem5402405 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402406 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402407 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402406 h1) (fun h1 : term326 = True => @lem5402405)). Qed.
Lemma lem5402408 : term326 = True.
Proof. exact (EQ_MP (@lem5402407) (@lem5402405)). Qed.
Lemma lem5402409 : term320 = True.
Proof. exact (TRANS (@lem5402404) (@lem5402408)). Qed.
Lemma lem5402410 : True = term320.
Proof. exact (SYM (@lem5402409)). Qed.
Lemma lem5402411 : term320.
Proof. exact (EQ_MP (@lem5402410) (@lem0)). Qed.
Lemma lem5402412 : term328.
Proof. exact (@lem5402401 (@lem5402411)). Qed.
Lemma lem5402414 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402415 : term320 = term326.
Proof. exact (@lem5402414 (NUMERAL 0) term133). Qed.
Lemma lem5402416 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402417 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402418 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402417 h1) (fun h1 : term326 = True => @lem5402416)). Qed.
Lemma lem5402419 : term326 = True.
Proof. exact (EQ_MP (@lem5402418) (@lem5402416)). Qed.
Lemma lem5402420 : term320 = True.
Proof. exact (TRANS (@lem5402415) (@lem5402419)). Qed.
Lemma lem5402421 : True = term320.
Proof. exact (SYM (@lem5402420)). Qed.
Lemma lem5402422 : term320.
Proof. exact (EQ_MP (@lem5402421) (@lem0)). Qed.
Lemma lem5402423 : term323 = term329.
Proof. exact (@lem5402412 (@lem5402422)). Qed.
Lemma lem5402425 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5402426 : term196 = term197.
Proof. exact (@lem5402425 term133 term133). Qed.
Lemma lem5402427 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402428 : term199 = term133.
Proof. exact (EQ_MP (@lem5402427) (@lem940073)). Qed.
Lemma lem5402429 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402430 : term197 = term132.
Proof. exact (MK_COMB (@lem5402429) (@lem5402428)). Qed.
Lemma lem5402431 : term196 = term132.
Proof. exact (TRANS (@lem5402426) (@lem5402430)). Qed.
Lemma lem5402433 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5402434 : term331 = term118.
Proof. exact (@lem5402433 term133). Qed.
Lemma lem5402435 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5402436 : term332 = term321.
Proof. exact (MK_COMB (@lem5402435) (@lem5402434)). Qed.
Lemma lem5402437 : term329 = term320.
Proof. exact (MK_COMB (@lem5402436) (@lem5402431)). Qed.
Lemma lem5402439 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402440 : term320 = term326.
Proof. exact (@lem5402439 (NUMERAL 0) term133). Qed.
Lemma lem5402441 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402442 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402443 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402442 h1) (fun h1 : term326 = True => @lem5402441)). Qed.
Lemma lem5402444 : term326 = True.
Proof. exact (EQ_MP (@lem5402443) (@lem5402441)). Qed.
Lemma lem5402445 : term320 = True.
Proof. exact (TRANS (@lem5402440) (@lem5402444)). Qed.
Lemma lem5402446 : term329 = True.
Proof. exact (TRANS (@lem5402437) (@lem5402445)). Qed.
Lemma lem5402447 : term323 = True.
Proof. exact (TRANS (@lem5402423) (@lem5402446)). Qed.
Lemma lem5402448 : term320 = True.
Proof. exact (TRANS (@lem5402400) (@lem5402447)). Qed.
Lemma lem5402449 : term319 = True.
Proof. exact (TRANS (@lem5402391) (@lem5402448)). Qed.
Lemma lem5402450 : True = term319.
Proof. exact (SYM (@lem5402449)). Qed.
Lemma lem5402451 : term319.
Proof. exact (EQ_MP (@lem5402450) (@lem0)). Qed.
Lemma lem5402452 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term333 _69895 _69896.
Proof. exact (conj (@lem5402451) (@lem5402388 _69895 _69896 h1)). Qed.
Lemma lem5402454 (x : real) (y : real) : term334 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5402455 (_69895 : int) (_69896 : int) : term335 _69895 _69896.
Proof. exact (@lem5402454 term132 (term225 _69895 _69896)). Qed.
Lemma lem5402456 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term336 _69895 _69896.
Proof. exact (@lem5402455 _69895 _69896 (@lem5402452 _69895 _69896 h1)). Qed.
Lemma lem5402457 (_69895 : int) (_69896 : int) : (term337 _69895 _69896) = (term225 _69895 _69896).
Proof. exact (@lem1982733 (term225 _69895 _69896)). Qed.
Lemma lem5402458 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5402459 (_69895 : int) (_69896 : int) : (term338 _69895 _69896) = (term227 _69895 _69896).
Proof. exact (MK_COMB (@lem5402458) (@lem5402457 _69895 _69896)). Qed.
Lemma lem5402460 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5402461 (_69895 : int) (_69896 : int) : (term336 _69895 _69896) = (term228 _69895 _69896).
Proof. exact (MK_COMB (@lem5402459 _69895 _69896) (@lem5402460)). Qed.
Lemma lem5402462 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term228 _69895 _69896.
Proof. exact (EQ_MP (@lem5402461 _69895 _69896) (@lem5402456 _69895 _69896 h1)). Qed.
Lemma lem5402464 (y : real) : term339 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5402465 (_69896 : int) : term340 _69896.
Proof. exact (@lem5402464 (real_of_int _69896)). Qed.
Lemma lem5402466 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term341 _69896.
Proof. exact (@lem5402465 _69896 (@lem5402387 _69895 _69896 h1)). Qed.
Lemma lem5402467 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term342 _69896.
Proof. exact (@lem5402466 _69895 _69896 h1 term132). Qed.
Lemma lem5402468 (_69896 : int) : (term342 _69896) = ((term343 _69896) = term118).
Proof. exact (eq_refl (term342 _69896)). Qed.
Lemma lem5402469 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : (term343 _69896) = term118.
Proof. exact (EQ_MP (@lem5402468 _69896) (@lem5402467 _69895 _69896 h1)). Qed.
Lemma lem5402470 (_69896 : int) : (term343 _69896) = (real_of_int _69896).
Proof. exact (@lem1982733 (real_of_int _69896)). Qed.
Lemma lem5402471 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5402472 (_69896 : int) : (term344 _69896) = (term122 _69896).
Proof. exact (MK_COMB (@lem5402471) (@lem5402470 _69896)). Qed.
Lemma lem5402473 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5402474 (_69896 : int) : ((term343 _69896) = term118) = ((real_of_int _69896) = term118).
Proof. exact (MK_COMB (@lem5402472 _69896) (@lem5402473)). Qed.
Lemma lem5402475 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : (real_of_int _69896) = term118.
Proof. exact (EQ_MP (@lem5402474 _69896) (@lem5402469 _69895 _69896 h1)). Qed.
Lemma lem5402476 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term345 _69895 _69896.
Proof. exact (conj (@lem5402475 _69895 _69896 h1) (@lem5402462 _69895 _69896 h1)). Qed.
Lemma lem5402478 (x : real) (y : real) : term346 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5402479 (_69895 : int) (_69896 : int) : term347 _69895 _69896.
Proof. exact (@lem5402478 (real_of_int _69896) (term225 _69895 _69896)). Qed.
Lemma lem5402480 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term348 _69895 _69896.
Proof. exact (@lem5402479 _69895 _69896 (@lem5402476 _69895 _69896 h1)). Qed.
Lemma lem5402481 (_69895 : int) (_69896 : int) : (term349 _69895 _69896) = (term350 _69895 _69896).
Proof. exact (@lem1982757 (real_of_int _69895) (real_of_int _69896) (term224 _69896)). Qed.
Lemma lem5402482 (_69896 : int) : (term351 _69896) = (term352 _69896).
Proof. exact (@lem1982763 (real_of_int _69896) (term246 _69896) term187). Qed.
Lemma lem5402483 (_69896 : int) : (term353 _69896) = (term354 _69896).
Proof. exact (@lem1982715 term187 (real_of_int _69896)). Qed.
Lemma lem5402485 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402486 : term132 = term214.
Proof. exact (@lem5402485 term133). Qed.
Lemma lem5402488 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5402489 : term187 = term188.
Proof. exact (@lem5402488 term133). Qed.
Lemma lem5402490 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5402491 : term355 = term356.
Proof. exact (MK_COMB (@lem5402490) (@lem5402489)). Qed.
Lemma lem5402492 : term357 = term358.
Proof. exact (MK_COMB (@lem5402491) (@lem5402486)). Qed.
Lemma lem5402493 : term359.
Proof. exact (@lem1981473 term187 term132 term132 term132 term118 term132). Qed.
Lemma lem5402495 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402496 : term320 = term326.
Proof. exact (@lem5402495 (NUMERAL 0) term133). Qed.
Lemma lem5402497 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402498 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402499 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402498 h1) (fun h1 : term326 = True => @lem5402497)). Qed.
Lemma lem5402500 : term326 = True.
Proof. exact (EQ_MP (@lem5402499) (@lem5402497)). Qed.
Lemma lem5402501 : term320 = True.
Proof. exact (TRANS (@lem5402496) (@lem5402500)). Qed.
Lemma lem5402502 : True = term320.
Proof. exact (SYM (@lem5402501)). Qed.
Lemma lem5402503 : term320.
Proof. exact (EQ_MP (@lem5402502) (@lem0)). Qed.
Lemma lem5402504 : term360.
Proof. exact (@lem5402493 (@lem5402503)). Qed.
Lemma lem5402506 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402507 : term320 = term326.
Proof. exact (@lem5402506 (NUMERAL 0) term133). Qed.
Lemma lem5402508 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402509 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402510 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402509 h1) (fun h1 : term326 = True => @lem5402508)). Qed.
Lemma lem5402511 : term326 = True.
Proof. exact (EQ_MP (@lem5402510) (@lem5402508)). Qed.
Lemma lem5402512 : term320 = True.
Proof. exact (TRANS (@lem5402507) (@lem5402511)). Qed.
Lemma lem5402513 : True = term320.
Proof. exact (SYM (@lem5402512)). Qed.
Lemma lem5402514 : term320.
Proof. exact (EQ_MP (@lem5402513) (@lem0)). Qed.
Lemma lem5402515 : term361.
Proof. exact (@lem5402504 (@lem5402514)). Qed.
Lemma lem5402517 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402518 : term320 = term326.
Proof. exact (@lem5402517 (NUMERAL 0) term133). Qed.
Lemma lem5402519 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402520 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402521 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402520 h1) (fun h1 : term326 = True => @lem5402519)). Qed.
Lemma lem5402522 : term326 = True.
Proof. exact (EQ_MP (@lem5402521) (@lem5402519)). Qed.
Lemma lem5402523 : term320 = True.
Proof. exact (TRANS (@lem5402518) (@lem5402522)). Qed.
Lemma lem5402524 : True = term320.
Proof. exact (SYM (@lem5402523)). Qed.
Lemma lem5402525 : term320.
Proof. exact (EQ_MP (@lem5402524) (@lem0)). Qed.
Lemma lem5402526 : term362.
Proof. exact (@lem5402515 (@lem5402525)). Qed.
Lemma lem5402528 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5402529 : term196 = term197.
Proof. exact (@lem5402528 term133 term133). Qed.
Lemma lem5402530 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402531 : term199 = term133.
Proof. exact (EQ_MP (@lem5402530) (@lem940073)). Qed.
Lemma lem5402532 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402533 : term197 = term132.
Proof. exact (MK_COMB (@lem5402532) (@lem5402531)). Qed.
Lemma lem5402534 : term196 = term132.
Proof. exact (TRANS (@lem5402529) (@lem5402533)). Qed.
Lemma lem5402536 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5402537 : term215 = term220.
Proof. exact (@lem5402536 term133 term133). Qed.
Lemma lem5402538 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402539 : term199 = term133.
Proof. exact (EQ_MP (@lem5402538) (@lem940073)). Qed.
Lemma lem5402540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402541 : term197 = term132.
Proof. exact (MK_COMB (@lem5402540) (@lem5402539)). Qed.
Lemma lem5402542 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5402543 : term220 = term187.
Proof. exact (MK_COMB (@lem5402542) (@lem5402541)). Qed.
Lemma lem5402544 : term215 = term187.
Proof. exact (TRANS (@lem5402537) (@lem5402543)). Qed.
Lemma lem5402545 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5402546 : term363 = term355.
Proof. exact (MK_COMB (@lem5402545) (@lem5402544)). Qed.
Lemma lem5402547 : term364 = term357.
Proof. exact (MK_COMB (@lem5402546) (@lem5402534)). Qed.
Lemma lem5402549 (m : nat) : (term365 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5402550 : term357 = term118.
Proof. exact (@lem5402549 term133). Qed.
Lemma lem5402551 : term364 = term118.
Proof. exact (TRANS (@lem5402547) (@lem5402550)). Qed.
Lemma lem5402552 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5402553 : term366 = term367.
Proof. exact (MK_COMB (@lem5402552) (@lem5402551)). Qed.
Lemma lem5402554 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem5402555 : term368 = term331.
Proof. exact (MK_COMB (@lem5402553) (@lem5402554)). Qed.
Lemma lem5402557 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5402558 : term331 = term118.
Proof. exact (@lem5402557 term133). Qed.
Lemma lem5402559 : term368 = term118.
Proof. exact (TRANS (@lem5402555) (@lem5402558)). Qed.
Lemma lem5402561 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5402562 : term196 = term197.
Proof. exact (@lem5402561 term133 term133). Qed.
Lemma lem5402563 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402564 : term199 = term133.
Proof. exact (EQ_MP (@lem5402563) (@lem940073)). Qed.
Lemma lem5402565 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402566 : term197 = term132.
Proof. exact (MK_COMB (@lem5402565) (@lem5402564)). Qed.
Lemma lem5402567 : term196 = term132.
Proof. exact (TRANS (@lem5402562) (@lem5402566)). Qed.
Lemma lem5402568 : term367 = term367.
Proof. exact (eq_refl term367). Qed.
Lemma lem5402569 : term369 = term331.
Proof. exact (MK_COMB (@lem5402568) (@lem5402567)). Qed.
Lemma lem5402571 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5402572 : term331 = term118.
Proof. exact (@lem5402571 term133). Qed.
Lemma lem5402573 : term369 = term118.
Proof. exact (TRANS (@lem5402569) (@lem5402572)). Qed.
Lemma lem5402574 : term118 = term369.
Proof. exact (SYM (@lem5402573)). Qed.
Lemma lem5402575 : term368 = term369.
Proof. exact (TRANS (@lem5402559) (@lem5402574)). Qed.
Lemma lem5402576 : term358 = term184.
Proof. exact (@lem5402526 (@lem5402575)). Qed.
Lemma lem5402577 : term357 = term184.
Proof. exact (TRANS (@lem5402492) (@lem5402576)). Qed.
Lemma lem5402579 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5402580 : term184 = term118.
Proof. exact (@lem5402579 term118). Qed.
Lemma lem5402581 : term357 = term118.
Proof. exact (TRANS (@lem5402577) (@lem5402580)). Qed.
Lemma lem5402582 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5402583 : term370 = term367.
Proof. exact (MK_COMB (@lem5402582) (@lem5402581)). Qed.
Lemma lem5402584 (_69896 : int) : (real_of_int _69896) = (real_of_int _69896).
Proof. exact (eq_refl (real_of_int _69896)). Qed.
Lemma lem5402585 (_69896 : int) : (term354 _69896) = (term371 _69896).
Proof. exact (MK_COMB (@lem5402583) (@lem5402584 _69896)). Qed.
Lemma lem5402586 (_69896 : int) : (term353 _69896) = (term371 _69896).
Proof. exact (TRANS (@lem5402483 _69896) (@lem5402585 _69896)). Qed.
Lemma lem5402587 (_69896 : int) : (term371 _69896) = term118.
Proof. exact (@lem1982719 (real_of_int _69896)). Qed.
Lemma lem5402588 (_69896 : int) : (term353 _69896) = term118.
Proof. exact (TRANS (@lem5402586 _69896) (@lem5402587 _69896)). Qed.
Lemma lem5402589 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5402590 (_69896 : int) : (term372 _69896) = term145.
Proof. exact (MK_COMB (@lem5402589) (@lem5402588 _69896)). Qed.
Lemma lem5402591 : term187 = term187.
Proof. exact (eq_refl term187). Qed.
Lemma lem5402592 (_69896 : int) : (term352 _69896) = term373.
Proof. exact (MK_COMB (@lem5402590 _69896) (@lem5402591)). Qed.
Lemma lem5402593 (_69896 : int) : (term351 _69896) = term373.
Proof. exact (TRANS (@lem5402482 _69896) (@lem5402592 _69896)). Qed.
Lemma lem5402594 : term373 = term187.
Proof. exact (@lem1982721 term187). Qed.
Lemma lem5402595 (_69896 : int) : (term351 _69896) = term187.
Proof. exact (TRANS (@lem5402593 _69896) (@lem5402594)). Qed.
Lemma lem5402596 (_69895 : int) : (term134 _69895) = (term134 _69895).
Proof. exact (eq_refl (term134 _69895)). Qed.
Lemma lem5402597 (_69896 : int) (_69895 : int) : (term350 _69895 _69896) = (term234 _69895).
Proof. exact (MK_COMB (@lem5402596 _69895) (@lem5402595 _69896)). Qed.
Lemma lem5402598 (_69896 : int) (_69895 : int) : (term349 _69895 _69896) = (term234 _69895).
Proof. exact (TRANS (@lem5402481 _69895 _69896) (@lem5402597 _69896 _69895)). Qed.
Lemma lem5402599 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5402600 (_69896 : int) (_69895 : int) : (term374 _69895 _69896) = (term236 _69895).
Proof. exact (MK_COMB (@lem5402599) (@lem5402598 _69896 _69895)). Qed.
Lemma lem5402601 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5402602 (_69896 : int) (_69895 : int) : (term348 _69895 _69896) = (term237 _69895).
Proof. exact (MK_COMB (@lem5402600 _69896 _69895) (@lem5402601)). Qed.
Lemma lem5402603 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term237 _69895.
Proof. exact (EQ_MP (@lem5402602 _69896 _69895) (@lem5402480 _69895 _69896 h1)). Qed.
Lemma lem5402605 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5402606 : term319 = term320.
Proof. exact (@lem5402605 term118 term132). Qed.
Lemma lem5402608 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402609 : term132 = term214.
Proof. exact (@lem5402608 term133). Qed.
Lemma lem5402611 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402612 : term118 = term184.
Proof. exact (@lem5402611 (NUMERAL 0)). Qed.
Lemma lem5402613 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5402614 : term321 = term322.
Proof. exact (MK_COMB (@lem5402613) (@lem5402612)). Qed.
Lemma lem5402615 : term320 = term323.
Proof. exact (MK_COMB (@lem5402614) (@lem5402609)). Qed.
Lemma lem5402616 : term324.
Proof. exact (@lem1980255 term118 term132 term132 term132). Qed.
Lemma lem5402618 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402619 : term320 = term326.
Proof. exact (@lem5402618 (NUMERAL 0) term133). Qed.
Lemma lem5402620 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402621 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402622 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402621 h1) (fun h1 : term326 = True => @lem5402620)). Qed.
Lemma lem5402623 : term326 = True.
Proof. exact (EQ_MP (@lem5402622) (@lem5402620)). Qed.
Lemma lem5402624 : term320 = True.
Proof. exact (TRANS (@lem5402619) (@lem5402623)). Qed.
Lemma lem5402625 : True = term320.
Proof. exact (SYM (@lem5402624)). Qed.
Lemma lem5402626 : term320.
Proof. exact (EQ_MP (@lem5402625) (@lem0)). Qed.
Lemma lem5402627 : term328.
Proof. exact (@lem5402616 (@lem5402626)). Qed.
Lemma lem5402629 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402630 : term320 = term326.
Proof. exact (@lem5402629 (NUMERAL 0) term133). Qed.
Lemma lem5402631 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402632 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402633 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402632 h1) (fun h1 : term326 = True => @lem5402631)). Qed.
Lemma lem5402634 : term326 = True.
Proof. exact (EQ_MP (@lem5402633) (@lem5402631)). Qed.
Lemma lem5402635 : term320 = True.
Proof. exact (TRANS (@lem5402630) (@lem5402634)). Qed.
Lemma lem5402636 : True = term320.
Proof. exact (SYM (@lem5402635)). Qed.
Lemma lem5402637 : term320.
Proof. exact (EQ_MP (@lem5402636) (@lem0)). Qed.
Lemma lem5402638 : term323 = term329.
Proof. exact (@lem5402627 (@lem5402637)). Qed.
Lemma lem5402640 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5402641 : term196 = term197.
Proof. exact (@lem5402640 term133 term133). Qed.
Lemma lem5402642 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402643 : term199 = term133.
Proof. exact (EQ_MP (@lem5402642) (@lem940073)). Qed.
Lemma lem5402644 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402645 : term197 = term132.
Proof. exact (MK_COMB (@lem5402644) (@lem5402643)). Qed.
Lemma lem5402646 : term196 = term132.
Proof. exact (TRANS (@lem5402641) (@lem5402645)). Qed.
Lemma lem5402648 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5402649 : term331 = term118.
Proof. exact (@lem5402648 term133). Qed.
Lemma lem5402650 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5402651 : term332 = term321.
Proof. exact (MK_COMB (@lem5402650) (@lem5402649)). Qed.
Lemma lem5402652 : term329 = term320.
Proof. exact (MK_COMB (@lem5402651) (@lem5402646)). Qed.
Lemma lem5402654 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402655 : term320 = term326.
Proof. exact (@lem5402654 (NUMERAL 0) term133). Qed.
Lemma lem5402656 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402657 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402658 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402657 h1) (fun h1 : term326 = True => @lem5402656)). Qed.
Lemma lem5402659 : term326 = True.
Proof. exact (EQ_MP (@lem5402658) (@lem5402656)). Qed.
Lemma lem5402660 : term320 = True.
Proof. exact (TRANS (@lem5402655) (@lem5402659)). Qed.
Lemma lem5402661 : term329 = True.
Proof. exact (TRANS (@lem5402652) (@lem5402660)). Qed.
Lemma lem5402662 : term323 = True.
Proof. exact (TRANS (@lem5402638) (@lem5402661)). Qed.
Lemma lem5402663 : term320 = True.
Proof. exact (TRANS (@lem5402615) (@lem5402662)). Qed.
Lemma lem5402664 : term319 = True.
Proof. exact (TRANS (@lem5402606) (@lem5402663)). Qed.
Lemma lem5402665 : True = term319.
Proof. exact (SYM (@lem5402664)). Qed.
Lemma lem5402666 : term319.
Proof. exact (EQ_MP (@lem5402665) (@lem0)). Qed.
Lemma lem5402667 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term375 _69895.
Proof. exact (conj (@lem5402666) (@lem5402603 _69895 _69896 h1)). Qed.
Lemma lem5402669 (x : real) (y : real) : term334 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5402670 (_69895 : int) : term376 _69895.
Proof. exact (@lem5402669 term132 (term234 _69895)). Qed.
Lemma lem5402671 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term377 _69895.
Proof. exact (@lem5402670 _69895 (@lem5402667 _69895 _69896 h1)). Qed.
Lemma lem5402672 (_69895 : int) : (term378 _69895) = (term234 _69895).
Proof. exact (@lem1982733 (term234 _69895)). Qed.
Lemma lem5402673 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5402674 (_69895 : int) : (term379 _69895) = (term236 _69895).
Proof. exact (MK_COMB (@lem5402673) (@lem5402672 _69895)). Qed.
Lemma lem5402675 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5402676 (_69895 : int) : (term377 _69895) = (term237 _69895).
Proof. exact (MK_COMB (@lem5402674 _69895) (@lem5402675)). Qed.
Lemma lem5402677 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term237 _69895.
Proof. exact (EQ_MP (@lem5402676 _69895) (@lem5402671 _69895 _69896 h1)). Qed.
Lemma lem5402679 (y : real) : term339 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5402680 (_69895 : int) : term340 _69895.
Proof. exact (@lem5402679 (real_of_int _69895)). Qed.
Lemma lem5402681 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term341 _69895.
Proof. exact (@lem5402680 _69895 (@lem5402386 _69895 _69896 h1)). Qed.
Lemma lem5402682 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term380 _69895.
Proof. exact (@lem5402681 _69895 _69896 h1 term187). Qed.
Lemma lem5402683 (_69895 : int) : (term380 _69895) = ((term246 _69895) = term118).
Proof. exact (eq_refl (term380 _69895)). Qed.
Lemma lem5402690 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : (term246 _69895) = term118.
Proof. exact (EQ_MP (@lem5402683 _69895) (@lem5402682 _69895 _69896 h1)). Qed.
Lemma lem5402691 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term381 _69895.
Proof. exact (conj (@lem5402690 _69895 _69896 h1) (@lem5402677 _69895 _69896 h1)). Qed.
Lemma lem5402693 (x : real) (y : real) : term346 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5402694 (_69895 : int) : term382 _69895.
Proof. exact (@lem5402693 (term246 _69895) (term234 _69895)). Qed.
Lemma lem5402695 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term383 _69895.
Proof. exact (@lem5402694 _69895 (@lem5402691 _69895 _69896 h1)). Qed.
Lemma lem5402696 (_69895 : int) : (term384 _69895) = (term385 _69895).
Proof. exact (@lem1982763 (term246 _69895) (real_of_int _69895) term187). Qed.
Lemma lem5402697 (_69895 : int) : (term386 _69895) = (term354 _69895).
Proof. exact (@lem1982713 term187 (real_of_int _69895)). Qed.
Lemma lem5402699 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402700 : term132 = term214.
Proof. exact (@lem5402699 term133). Qed.
Lemma lem5402702 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5402703 : term187 = term188.
Proof. exact (@lem5402702 term133). Qed.
Lemma lem5402704 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5402705 : term355 = term356.
Proof. exact (MK_COMB (@lem5402704) (@lem5402703)). Qed.
Lemma lem5402706 : term357 = term358.
Proof. exact (MK_COMB (@lem5402705) (@lem5402700)). Qed.
Lemma lem5402707 : term359.
Proof. exact (@lem1981473 term187 term132 term132 term132 term118 term132). Qed.
Lemma lem5402709 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402710 : term320 = term326.
Proof. exact (@lem5402709 (NUMERAL 0) term133). Qed.
Lemma lem5402711 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402712 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402713 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402712 h1) (fun h1 : term326 = True => @lem5402711)). Qed.
Lemma lem5402714 : term326 = True.
Proof. exact (EQ_MP (@lem5402713) (@lem5402711)). Qed.
Lemma lem5402715 : term320 = True.
Proof. exact (TRANS (@lem5402710) (@lem5402714)). Qed.
Lemma lem5402716 : True = term320.
Proof. exact (SYM (@lem5402715)). Qed.
Lemma lem5402717 : term320.
Proof. exact (EQ_MP (@lem5402716) (@lem0)). Qed.
Lemma lem5402718 : term360.
Proof. exact (@lem5402707 (@lem5402717)). Qed.
Lemma lem5402720 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402721 : term320 = term326.
Proof. exact (@lem5402720 (NUMERAL 0) term133). Qed.
Lemma lem5402722 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402723 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402724 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402723 h1) (fun h1 : term326 = True => @lem5402722)). Qed.
Lemma lem5402725 : term326 = True.
Proof. exact (EQ_MP (@lem5402724) (@lem5402722)). Qed.
Lemma lem5402726 : term320 = True.
Proof. exact (TRANS (@lem5402721) (@lem5402725)). Qed.
Lemma lem5402727 : True = term320.
Proof. exact (SYM (@lem5402726)). Qed.
Lemma lem5402728 : term320.
Proof. exact (EQ_MP (@lem5402727) (@lem0)). Qed.
Lemma lem5402729 : term361.
Proof. exact (@lem5402718 (@lem5402728)). Qed.
Lemma lem5402731 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402732 : term320 = term326.
Proof. exact (@lem5402731 (NUMERAL 0) term133). Qed.
Lemma lem5402733 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402734 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402735 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402734 h1) (fun h1 : term326 = True => @lem5402733)). Qed.
Lemma lem5402736 : term326 = True.
Proof. exact (EQ_MP (@lem5402735) (@lem5402733)). Qed.
Lemma lem5402737 : term320 = True.
Proof. exact (TRANS (@lem5402732) (@lem5402736)). Qed.
Lemma lem5402738 : True = term320.
Proof. exact (SYM (@lem5402737)). Qed.
Lemma lem5402739 : term320.
Proof. exact (EQ_MP (@lem5402738) (@lem0)). Qed.
Lemma lem5402740 : term362.
Proof. exact (@lem5402729 (@lem5402739)). Qed.
Lemma lem5402742 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5402743 : term196 = term197.
Proof. exact (@lem5402742 term133 term133). Qed.
Lemma lem5402744 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402745 : term199 = term133.
Proof. exact (EQ_MP (@lem5402744) (@lem940073)). Qed.
Lemma lem5402746 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402747 : term197 = term132.
Proof. exact (MK_COMB (@lem5402746) (@lem5402745)). Qed.
Lemma lem5402748 : term196 = term132.
Proof. exact (TRANS (@lem5402743) (@lem5402747)). Qed.
Lemma lem5402750 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5402751 : term215 = term220.
Proof. exact (@lem5402750 term133 term133). Qed.
Lemma lem5402752 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402753 : term199 = term133.
Proof. exact (EQ_MP (@lem5402752) (@lem940073)). Qed.
Lemma lem5402754 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402755 : term197 = term132.
Proof. exact (MK_COMB (@lem5402754) (@lem5402753)). Qed.
Lemma lem5402756 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5402757 : term220 = term187.
Proof. exact (MK_COMB (@lem5402756) (@lem5402755)). Qed.
Lemma lem5402758 : term215 = term187.
Proof. exact (TRANS (@lem5402751) (@lem5402757)). Qed.
Lemma lem5402759 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5402760 : term363 = term355.
Proof. exact (MK_COMB (@lem5402759) (@lem5402758)). Qed.
Lemma lem5402761 : term364 = term357.
Proof. exact (MK_COMB (@lem5402760) (@lem5402748)). Qed.
Lemma lem5402763 (m : nat) : (term365 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5402764 : term357 = term118.
Proof. exact (@lem5402763 term133). Qed.
Lemma lem5402765 : term364 = term118.
Proof. exact (TRANS (@lem5402761) (@lem5402764)). Qed.
Lemma lem5402766 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5402767 : term366 = term367.
Proof. exact (MK_COMB (@lem5402766) (@lem5402765)). Qed.
Lemma lem5402768 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem5402769 : term368 = term331.
Proof. exact (MK_COMB (@lem5402767) (@lem5402768)). Qed.
Lemma lem5402771 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5402772 : term331 = term118.
Proof. exact (@lem5402771 term133). Qed.
Lemma lem5402773 : term368 = term118.
Proof. exact (TRANS (@lem5402769) (@lem5402772)). Qed.
Lemma lem5402775 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5402776 : term196 = term197.
Proof. exact (@lem5402775 term133 term133). Qed.
Lemma lem5402777 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402778 : term199 = term133.
Proof. exact (EQ_MP (@lem5402777) (@lem940073)). Qed.
Lemma lem5402779 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402780 : term197 = term132.
Proof. exact (MK_COMB (@lem5402779) (@lem5402778)). Qed.
Lemma lem5402781 : term196 = term132.
Proof. exact (TRANS (@lem5402776) (@lem5402780)). Qed.
Lemma lem5402782 : term367 = term367.
Proof. exact (eq_refl term367). Qed.
Lemma lem5402783 : term369 = term331.
Proof. exact (MK_COMB (@lem5402782) (@lem5402781)). Qed.
Lemma lem5402785 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5402786 : term331 = term118.
Proof. exact (@lem5402785 term133). Qed.
Lemma lem5402787 : term369 = term118.
Proof. exact (TRANS (@lem5402783) (@lem5402786)). Qed.
Lemma lem5402788 : term118 = term369.
Proof. exact (SYM (@lem5402787)). Qed.
Lemma lem5402789 : term368 = term369.
Proof. exact (TRANS (@lem5402773) (@lem5402788)). Qed.
Lemma lem5402790 : term358 = term184.
Proof. exact (@lem5402740 (@lem5402789)). Qed.
Lemma lem5402791 : term357 = term184.
Proof. exact (TRANS (@lem5402706) (@lem5402790)). Qed.
Lemma lem5402793 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5402794 : term184 = term118.
Proof. exact (@lem5402793 term118). Qed.
Lemma lem5402795 : term357 = term118.
Proof. exact (TRANS (@lem5402791) (@lem5402794)). Qed.
Lemma lem5402796 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5402797 : term370 = term367.
Proof. exact (MK_COMB (@lem5402796) (@lem5402795)). Qed.
Lemma lem5402798 (_69895 : int) : (real_of_int _69895) = (real_of_int _69895).
Proof. exact (eq_refl (real_of_int _69895)). Qed.
Lemma lem5402799 (_69895 : int) : (term354 _69895) = (term371 _69895).
Proof. exact (MK_COMB (@lem5402797) (@lem5402798 _69895)). Qed.
Lemma lem5402800 (_69895 : int) : (term386 _69895) = (term371 _69895).
Proof. exact (TRANS (@lem5402697 _69895) (@lem5402799 _69895)). Qed.
Lemma lem5402801 (_69895 : int) : (term371 _69895) = term118.
Proof. exact (@lem1982719 (real_of_int _69895)). Qed.
Lemma lem5402802 (_69895 : int) : (term386 _69895) = term118.
Proof. exact (TRANS (@lem5402800 _69895) (@lem5402801 _69895)). Qed.
Lemma lem5402803 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5402804 (_69895 : int) : (term387 _69895) = term145.
Proof. exact (MK_COMB (@lem5402803) (@lem5402802 _69895)). Qed.
Lemma lem5402805 : term187 = term187.
Proof. exact (eq_refl term187). Qed.
Lemma lem5402806 (_69895 : int) : (term385 _69895) = term373.
Proof. exact (MK_COMB (@lem5402804 _69895) (@lem5402805)). Qed.
Lemma lem5402807 (_69895 : int) : (term384 _69895) = term373.
Proof. exact (TRANS (@lem5402696 _69895) (@lem5402806 _69895)). Qed.
Lemma lem5402808 : term373 = term187.
Proof. exact (@lem1982721 term187). Qed.
Lemma lem5402809 (_69895 : int) : (term384 _69895) = term187.
Proof. exact (TRANS (@lem5402807 _69895) (@lem5402808)). Qed.
Lemma lem5402810 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5402811 (_69895 : int) : (term388 _69895) = term389.
Proof. exact (MK_COMB (@lem5402810) (@lem5402809 _69895)). Qed.
Lemma lem5402812 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5402813 (_69895 : int) : (term383 _69895) = term390.
Proof. exact (MK_COMB (@lem5402811 _69895) (@lem5402812)). Qed.
Lemma lem5402814 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : term390.
Proof. exact (EQ_MP (@lem5402813 _69895) (@lem5402695 _69895 _69896 h1)). Qed.
Lemma lem5402816 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5402817 : term390 = term391.
Proof. exact (@lem5402816 term118 term187). Qed.
Lemma lem5402819 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5402820 : term187 = term188.
Proof. exact (@lem5402819 term133). Qed.
Lemma lem5402822 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402823 : term118 = term184.
Proof. exact (@lem5402822 (NUMERAL 0)). Qed.
Lemma lem5402824 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5402825 : term120 = term392.
Proof. exact (MK_COMB (@lem5402824) (@lem5402823)). Qed.
Lemma lem5402826 : term391 = term393.
Proof. exact (MK_COMB (@lem5402825) (@lem5402820)). Qed.
Lemma lem5402827 : term394.
Proof. exact (@lem1980026 term118 term132 term187 term132). Qed.
Lemma lem5402829 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402830 : term320 = term326.
Proof. exact (@lem5402829 (NUMERAL 0) term133). Qed.
Lemma lem5402831 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402832 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402833 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402832 h1) (fun h1 : term326 = True => @lem5402831)). Qed.
Lemma lem5402834 : term326 = True.
Proof. exact (EQ_MP (@lem5402833) (@lem5402831)). Qed.
Lemma lem5402835 : term320 = True.
Proof. exact (TRANS (@lem5402830) (@lem5402834)). Qed.
Lemma lem5402836 : True = term320.
Proof. exact (SYM (@lem5402835)). Qed.
Lemma lem5402837 : term320.
Proof. exact (EQ_MP (@lem5402836) (@lem0)). Qed.
Lemma lem5402838 : term395.
Proof. exact (@lem5402827 (@lem5402837)). Qed.
Lemma lem5402840 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402841 : term320 = term326.
Proof. exact (@lem5402840 (NUMERAL 0) term133). Qed.
Lemma lem5402842 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402843 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402844 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402843 h1) (fun h1 : term326 = True => @lem5402842)). Qed.
Lemma lem5402845 : term326 = True.
Proof. exact (EQ_MP (@lem5402844) (@lem5402842)). Qed.
Lemma lem5402846 : term320 = True.
Proof. exact (TRANS (@lem5402841) (@lem5402845)). Qed.
Lemma lem5402847 : True = term320.
Proof. exact (SYM (@lem5402846)). Qed.
Lemma lem5402848 : term320.
Proof. exact (EQ_MP (@lem5402847) (@lem0)). Qed.
Lemma lem5402849 : term393 = term396.
Proof. exact (@lem5402838 (@lem5402848)). Qed.
Lemma lem5402851 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5402852 : term215 = term220.
Proof. exact (@lem5402851 term133 term133). Qed.
Lemma lem5402853 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402854 : term199 = term133.
Proof. exact (EQ_MP (@lem5402853) (@lem940073)). Qed.
Lemma lem5402855 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402856 : term197 = term132.
Proof. exact (MK_COMB (@lem5402855) (@lem5402854)). Qed.
Lemma lem5402857 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5402858 : term220 = term187.
Proof. exact (MK_COMB (@lem5402857) (@lem5402856)). Qed.
Lemma lem5402859 : term215 = term187.
Proof. exact (TRANS (@lem5402852) (@lem5402858)). Qed.
Lemma lem5402861 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5402862 : term331 = term118.
Proof. exact (@lem5402861 term133). Qed.
Lemma lem5402863 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5402864 : term397 = term120.
Proof. exact (MK_COMB (@lem5402863) (@lem5402862)). Qed.
Lemma lem5402865 : term396 = term391.
Proof. exact (MK_COMB (@lem5402864) (@lem5402859)). Qed.
Lemma lem5402867 (m : nat) (n : nat) : (term398 m n) = (term399 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5402868 : term391 = term400.
Proof. exact (@lem5402867 (NUMERAL 0) term133). Qed.
Lemma lem5402869 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402870 (h1 : term327 = (BIT1 0)) : (term133 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5402871 : (term327 = (BIT1 0)) = ((term133 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402870 h1) (fun h1 : (term133 = (NUMERAL 0)) = False => @lem5402869)). Qed.
Lemma lem5402872 : (term133 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5402871) (@lem5402869)). Qed.
Lemma lem5402873 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5402874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5402875 : term401 = (and True).
Proof. exact (MK_COMB (@lem5402874) (@lem5402873)). Qed.
Lemma lem5402876 : term400 = (True /\ False).
Proof. exact (MK_COMB (@lem5402875) (@lem5402872)). Qed.
Lemma lem5402878 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5402879 : term400 = False.
Proof. exact (TRANS (@lem5402876) (@lem5402878)). Qed.
Lemma lem5402880 : term391 = False.
Proof. exact (TRANS (@lem5402868) (@lem5402879)). Qed.
Lemma lem5402881 : term396 = False.
Proof. exact (TRANS (@lem5402865) (@lem5402880)). Qed.
Lemma lem5402882 : term393 = False.
Proof. exact (TRANS (@lem5402849) (@lem5402881)). Qed.
Lemma lem5402883 : term391 = False.
Proof. exact (TRANS (@lem5402826) (@lem5402882)). Qed.
Lemma lem5402884 : term390 = False.
Proof. exact (TRANS (@lem5402817) (@lem5402883)). Qed.
Lemma lem5402885 (_69895 : int) (_69896 : int) (h1 : term318 _69895 _69896) : False.
Proof. exact (EQ_MP (@lem5402884) (@lem5402814 _69895 _69896 h1)). Qed.
Lemma lem5402886 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term402 _69895 _69896.
Proof. exact (h1). Qed.
Lemma lem5402887 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term314 _69895 _69896.
Proof. exact (proj2 (@lem5402886 _69895 _69896 h1)). Qed.
Lemma lem5402889 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term301 _69895 _69896.
Proof. exact (proj2 (@lem5402887 _69895 _69896 h1)). Qed.
Lemma lem5402891 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term288 _69896.
Proof. exact (proj2 (@lem5402889 _69895 _69896 h1)). Qed.
Lemma lem5402893 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : (real_of_int _69896) = term118.
Proof. exact (proj2 (@lem5402891 _69895 _69896 h1)). Qed.
Lemma lem5402894 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term237 _69896.
Proof. exact (proj1 (@lem5402891 _69895 _69896 h1)). Qed.
Lemma lem5402896 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5402897 : term319 = term320.
Proof. exact (@lem5402896 term118 term132). Qed.
Lemma lem5402899 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402900 : term132 = term214.
Proof. exact (@lem5402899 term133). Qed.
Lemma lem5402902 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402903 : term118 = term184.
Proof. exact (@lem5402902 (NUMERAL 0)). Qed.
Lemma lem5402904 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5402905 : term321 = term322.
Proof. exact (MK_COMB (@lem5402904) (@lem5402903)). Qed.
Lemma lem5402906 : term320 = term323.
Proof. exact (MK_COMB (@lem5402905) (@lem5402900)). Qed.
Lemma lem5402907 : term324.
Proof. exact (@lem1980255 term118 term132 term132 term132). Qed.
Lemma lem5402909 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402910 : term320 = term326.
Proof. exact (@lem5402909 (NUMERAL 0) term133). Qed.
Lemma lem5402911 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402912 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402913 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402912 h1) (fun h1 : term326 = True => @lem5402911)). Qed.
Lemma lem5402914 : term326 = True.
Proof. exact (EQ_MP (@lem5402913) (@lem5402911)). Qed.
Lemma lem5402915 : term320 = True.
Proof. exact (TRANS (@lem5402910) (@lem5402914)). Qed.
Lemma lem5402916 : True = term320.
Proof. exact (SYM (@lem5402915)). Qed.
Lemma lem5402917 : term320.
Proof. exact (EQ_MP (@lem5402916) (@lem0)). Qed.
Lemma lem5402918 : term328.
Proof. exact (@lem5402907 (@lem5402917)). Qed.
Lemma lem5402920 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402921 : term320 = term326.
Proof. exact (@lem5402920 (NUMERAL 0) term133). Qed.
Lemma lem5402922 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402923 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402924 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402923 h1) (fun h1 : term326 = True => @lem5402922)). Qed.
Lemma lem5402925 : term326 = True.
Proof. exact (EQ_MP (@lem5402924) (@lem5402922)). Qed.
Lemma lem5402926 : term320 = True.
Proof. exact (TRANS (@lem5402921) (@lem5402925)). Qed.
Lemma lem5402927 : True = term320.
Proof. exact (SYM (@lem5402926)). Qed.
Lemma lem5402928 : term320.
Proof. exact (EQ_MP (@lem5402927) (@lem0)). Qed.
Lemma lem5402929 : term323 = term329.
Proof. exact (@lem5402918 (@lem5402928)). Qed.
Lemma lem5402931 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5402932 : term196 = term197.
Proof. exact (@lem5402931 term133 term133). Qed.
Lemma lem5402933 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5402934 : term199 = term133.
Proof. exact (EQ_MP (@lem5402933) (@lem940073)). Qed.
Lemma lem5402935 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5402936 : term197 = term132.
Proof. exact (MK_COMB (@lem5402935) (@lem5402934)). Qed.
Lemma lem5402937 : term196 = term132.
Proof. exact (TRANS (@lem5402932) (@lem5402936)). Qed.
Lemma lem5402939 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5402940 : term331 = term118.
Proof. exact (@lem5402939 term133). Qed.
Lemma lem5402941 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5402942 : term332 = term321.
Proof. exact (MK_COMB (@lem5402941) (@lem5402940)). Qed.
Lemma lem5402943 : term329 = term320.
Proof. exact (MK_COMB (@lem5402942) (@lem5402937)). Qed.
Lemma lem5402945 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5402946 : term320 = term326.
Proof. exact (@lem5402945 (NUMERAL 0) term133). Qed.
Lemma lem5402947 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5402948 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5402949 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5402948 h1) (fun h1 : term326 = True => @lem5402947)). Qed.
Lemma lem5402950 : term326 = True.
Proof. exact (EQ_MP (@lem5402949) (@lem5402947)). Qed.
Lemma lem5402951 : term320 = True.
Proof. exact (TRANS (@lem5402946) (@lem5402950)). Qed.
Lemma lem5402952 : term329 = True.
Proof. exact (TRANS (@lem5402943) (@lem5402951)). Qed.
Lemma lem5402953 : term323 = True.
Proof. exact (TRANS (@lem5402929) (@lem5402952)). Qed.
Lemma lem5402954 : term320 = True.
Proof. exact (TRANS (@lem5402906) (@lem5402953)). Qed.
Lemma lem5402955 : term319 = True.
Proof. exact (TRANS (@lem5402897) (@lem5402954)). Qed.
Lemma lem5402956 : True = term319.
Proof. exact (SYM (@lem5402955)). Qed.
Lemma lem5402957 : term319.
Proof. exact (EQ_MP (@lem5402956) (@lem0)). Qed.
Lemma lem5402958 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term375 _69896.
Proof. exact (conj (@lem5402957) (@lem5402894 _69895 _69896 h1)). Qed.
Lemma lem5402960 (x : real) (y : real) : term334 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5402961 (_69896 : int) : term376 _69896.
Proof. exact (@lem5402960 term132 (term234 _69896)). Qed.
Lemma lem5402962 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term377 _69896.
Proof. exact (@lem5402961 _69896 (@lem5402958 _69895 _69896 h1)). Qed.
Lemma lem5402963 (_69896 : int) : (term378 _69896) = (term234 _69896).
Proof. exact (@lem1982733 (term234 _69896)). Qed.
Lemma lem5402964 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5402965 (_69896 : int) : (term379 _69896) = (term236 _69896).
Proof. exact (MK_COMB (@lem5402964) (@lem5402963 _69896)). Qed.
Lemma lem5402966 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5402967 (_69896 : int) : (term377 _69896) = (term237 _69896).
Proof. exact (MK_COMB (@lem5402965 _69896) (@lem5402966)). Qed.
Lemma lem5402968 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term237 _69896.
Proof. exact (EQ_MP (@lem5402967 _69896) (@lem5402962 _69895 _69896 h1)). Qed.
Lemma lem5402970 (y : real) : term339 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5402971 (_69896 : int) : term340 _69896.
Proof. exact (@lem5402970 (real_of_int _69896)). Qed.
Lemma lem5402972 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term341 _69896.
Proof. exact (@lem5402971 _69896 (@lem5402893 _69895 _69896 h1)). Qed.
Lemma lem5402973 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term380 _69896.
Proof. exact (@lem5402972 _69895 _69896 h1 term187). Qed.
Lemma lem5402974 (_69896 : int) : (term380 _69896) = ((term246 _69896) = term118).
Proof. exact (eq_refl (term380 _69896)). Qed.
Lemma lem5402981 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : (term246 _69896) = term118.
Proof. exact (EQ_MP (@lem5402974 _69896) (@lem5402973 _69895 _69896 h1)). Qed.
Lemma lem5402982 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term381 _69896.
Proof. exact (conj (@lem5402981 _69895 _69896 h1) (@lem5402968 _69895 _69896 h1)). Qed.
Lemma lem5402984 (x : real) (y : real) : term346 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5402985 (_69896 : int) : term382 _69896.
Proof. exact (@lem5402984 (term246 _69896) (term234 _69896)). Qed.
Lemma lem5402986 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term383 _69896.
Proof. exact (@lem5402985 _69896 (@lem5402982 _69895 _69896 h1)). Qed.
Lemma lem5402987 (_69896 : int) : (term384 _69896) = (term385 _69896).
Proof. exact (@lem1982763 (term246 _69896) (real_of_int _69896) term187). Qed.
Lemma lem5402988 (_69896 : int) : (term386 _69896) = (term354 _69896).
Proof. exact (@lem1982713 term187 (real_of_int _69896)). Qed.
Lemma lem5402990 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5402991 : term132 = term214.
Proof. exact (@lem5402990 term133). Qed.
Lemma lem5402993 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5402994 : term187 = term188.
Proof. exact (@lem5402993 term133). Qed.
Lemma lem5402995 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5402996 : term355 = term356.
Proof. exact (MK_COMB (@lem5402995) (@lem5402994)). Qed.
Lemma lem5402997 : term357 = term358.
Proof. exact (MK_COMB (@lem5402996) (@lem5402991)). Qed.
Lemma lem5402998 : term359.
Proof. exact (@lem1981473 term187 term132 term132 term132 term118 term132). Qed.
Lemma lem5403000 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403001 : term320 = term326.
Proof. exact (@lem5403000 (NUMERAL 0) term133). Qed.
Lemma lem5403002 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403003 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403004 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403003 h1) (fun h1 : term326 = True => @lem5403002)). Qed.
Lemma lem5403005 : term326 = True.
Proof. exact (EQ_MP (@lem5403004) (@lem5403002)). Qed.
Lemma lem5403006 : term320 = True.
Proof. exact (TRANS (@lem5403001) (@lem5403005)). Qed.
Lemma lem5403007 : True = term320.
Proof. exact (SYM (@lem5403006)). Qed.
Lemma lem5403008 : term320.
Proof. exact (EQ_MP (@lem5403007) (@lem0)). Qed.
Lemma lem5403009 : term360.
Proof. exact (@lem5402998 (@lem5403008)). Qed.
Lemma lem5403011 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403012 : term320 = term326.
Proof. exact (@lem5403011 (NUMERAL 0) term133). Qed.
Lemma lem5403013 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403014 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403015 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403014 h1) (fun h1 : term326 = True => @lem5403013)). Qed.
Lemma lem5403016 : term326 = True.
Proof. exact (EQ_MP (@lem5403015) (@lem5403013)). Qed.
Lemma lem5403017 : term320 = True.
Proof. exact (TRANS (@lem5403012) (@lem5403016)). Qed.
Lemma lem5403018 : True = term320.
Proof. exact (SYM (@lem5403017)). Qed.
Lemma lem5403019 : term320.
Proof. exact (EQ_MP (@lem5403018) (@lem0)). Qed.
Lemma lem5403020 : term361.
Proof. exact (@lem5403009 (@lem5403019)). Qed.
Lemma lem5403022 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403023 : term320 = term326.
Proof. exact (@lem5403022 (NUMERAL 0) term133). Qed.
Lemma lem5403024 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403025 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403026 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403025 h1) (fun h1 : term326 = True => @lem5403024)). Qed.
Lemma lem5403027 : term326 = True.
Proof. exact (EQ_MP (@lem5403026) (@lem5403024)). Qed.
Lemma lem5403028 : term320 = True.
Proof. exact (TRANS (@lem5403023) (@lem5403027)). Qed.
Lemma lem5403029 : True = term320.
Proof. exact (SYM (@lem5403028)). Qed.
Lemma lem5403030 : term320.
Proof. exact (EQ_MP (@lem5403029) (@lem0)). Qed.
Lemma lem5403031 : term362.
Proof. exact (@lem5403020 (@lem5403030)). Qed.
Lemma lem5403033 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403034 : term196 = term197.
Proof. exact (@lem5403033 term133 term133). Qed.
Lemma lem5403035 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403036 : term199 = term133.
Proof. exact (EQ_MP (@lem5403035) (@lem940073)). Qed.
Lemma lem5403037 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403038 : term197 = term132.
Proof. exact (MK_COMB (@lem5403037) (@lem5403036)). Qed.
Lemma lem5403039 : term196 = term132.
Proof. exact (TRANS (@lem5403034) (@lem5403038)). Qed.
Lemma lem5403041 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5403042 : term215 = term220.
Proof. exact (@lem5403041 term133 term133). Qed.
Lemma lem5403043 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403044 : term199 = term133.
Proof. exact (EQ_MP (@lem5403043) (@lem940073)). Qed.
Lemma lem5403045 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403046 : term197 = term132.
Proof. exact (MK_COMB (@lem5403045) (@lem5403044)). Qed.
Lemma lem5403047 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5403048 : term220 = term187.
Proof. exact (MK_COMB (@lem5403047) (@lem5403046)). Qed.
Lemma lem5403049 : term215 = term187.
Proof. exact (TRANS (@lem5403042) (@lem5403048)). Qed.
Lemma lem5403050 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5403051 : term363 = term355.
Proof. exact (MK_COMB (@lem5403050) (@lem5403049)). Qed.
Lemma lem5403052 : term364 = term357.
Proof. exact (MK_COMB (@lem5403051) (@lem5403039)). Qed.
Lemma lem5403054 (m : nat) : (term365 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5403055 : term357 = term118.
Proof. exact (@lem5403054 term133). Qed.
Lemma lem5403056 : term364 = term118.
Proof. exact (TRANS (@lem5403052) (@lem5403055)). Qed.
Lemma lem5403057 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5403058 : term366 = term367.
Proof. exact (MK_COMB (@lem5403057) (@lem5403056)). Qed.
Lemma lem5403059 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem5403060 : term368 = term331.
Proof. exact (MK_COMB (@lem5403058) (@lem5403059)). Qed.
Lemma lem5403062 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403063 : term331 = term118.
Proof. exact (@lem5403062 term133). Qed.
Lemma lem5403064 : term368 = term118.
Proof. exact (TRANS (@lem5403060) (@lem5403063)). Qed.
Lemma lem5403066 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403067 : term196 = term197.
Proof. exact (@lem5403066 term133 term133). Qed.
Lemma lem5403068 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403069 : term199 = term133.
Proof. exact (EQ_MP (@lem5403068) (@lem940073)). Qed.
Lemma lem5403070 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403071 : term197 = term132.
Proof. exact (MK_COMB (@lem5403070) (@lem5403069)). Qed.
Lemma lem5403072 : term196 = term132.
Proof. exact (TRANS (@lem5403067) (@lem5403071)). Qed.
Lemma lem5403073 : term367 = term367.
Proof. exact (eq_refl term367). Qed.
Lemma lem5403074 : term369 = term331.
Proof. exact (MK_COMB (@lem5403073) (@lem5403072)). Qed.
Lemma lem5403076 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403077 : term331 = term118.
Proof. exact (@lem5403076 term133). Qed.
Lemma lem5403078 : term369 = term118.
Proof. exact (TRANS (@lem5403074) (@lem5403077)). Qed.
Lemma lem5403079 : term118 = term369.
Proof. exact (SYM (@lem5403078)). Qed.
Lemma lem5403080 : term368 = term369.
Proof. exact (TRANS (@lem5403064) (@lem5403079)). Qed.
Lemma lem5403081 : term358 = term184.
Proof. exact (@lem5403031 (@lem5403080)). Qed.
Lemma lem5403082 : term357 = term184.
Proof. exact (TRANS (@lem5402997) (@lem5403081)). Qed.
Lemma lem5403084 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5403085 : term184 = term118.
Proof. exact (@lem5403084 term118). Qed.
Lemma lem5403086 : term357 = term118.
Proof. exact (TRANS (@lem5403082) (@lem5403085)). Qed.
Lemma lem5403087 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5403088 : term370 = term367.
Proof. exact (MK_COMB (@lem5403087) (@lem5403086)). Qed.
Lemma lem5403089 (_69896 : int) : (real_of_int _69896) = (real_of_int _69896).
Proof. exact (eq_refl (real_of_int _69896)). Qed.
Lemma lem5403090 (_69896 : int) : (term354 _69896) = (term371 _69896).
Proof. exact (MK_COMB (@lem5403088) (@lem5403089 _69896)). Qed.
Lemma lem5403091 (_69896 : int) : (term386 _69896) = (term371 _69896).
Proof. exact (TRANS (@lem5402988 _69896) (@lem5403090 _69896)). Qed.
Lemma lem5403092 (_69896 : int) : (term371 _69896) = term118.
Proof. exact (@lem1982719 (real_of_int _69896)). Qed.
Lemma lem5403093 (_69896 : int) : (term386 _69896) = term118.
Proof. exact (TRANS (@lem5403091 _69896) (@lem5403092 _69896)). Qed.
Lemma lem5403094 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5403095 (_69896 : int) : (term387 _69896) = term145.
Proof. exact (MK_COMB (@lem5403094) (@lem5403093 _69896)). Qed.
Lemma lem5403096 : term187 = term187.
Proof. exact (eq_refl term187). Qed.
Lemma lem5403097 (_69896 : int) : (term385 _69896) = term373.
Proof. exact (MK_COMB (@lem5403095 _69896) (@lem5403096)). Qed.
Lemma lem5403098 (_69896 : int) : (term384 _69896) = term373.
Proof. exact (TRANS (@lem5402987 _69896) (@lem5403097 _69896)). Qed.
Lemma lem5403099 : term373 = term187.
Proof. exact (@lem1982721 term187). Qed.
Lemma lem5403100 (_69896 : int) : (term384 _69896) = term187.
Proof. exact (TRANS (@lem5403098 _69896) (@lem5403099)). Qed.
Lemma lem5403101 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5403102 (_69896 : int) : (term388 _69896) = term389.
Proof. exact (MK_COMB (@lem5403101) (@lem5403100 _69896)). Qed.
Lemma lem5403103 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5403104 (_69896 : int) : (term383 _69896) = term390.
Proof. exact (MK_COMB (@lem5403102 _69896) (@lem5403103)). Qed.
Lemma lem5403105 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : term390.
Proof. exact (EQ_MP (@lem5403104 _69896) (@lem5402986 _69895 _69896 h1)). Qed.
Lemma lem5403107 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5403108 : term390 = term391.
Proof. exact (@lem5403107 term118 term187). Qed.
Lemma lem5403110 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5403111 : term187 = term188.
Proof. exact (@lem5403110 term133). Qed.
Lemma lem5403113 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403114 : term118 = term184.
Proof. exact (@lem5403113 (NUMERAL 0)). Qed.
Lemma lem5403115 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5403116 : term120 = term392.
Proof. exact (MK_COMB (@lem5403115) (@lem5403114)). Qed.
Lemma lem5403117 : term391 = term393.
Proof. exact (MK_COMB (@lem5403116) (@lem5403111)). Qed.
Lemma lem5403118 : term394.
Proof. exact (@lem1980026 term118 term132 term187 term132). Qed.
Lemma lem5403120 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403121 : term320 = term326.
Proof. exact (@lem5403120 (NUMERAL 0) term133). Qed.
Lemma lem5403122 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403123 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403124 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403123 h1) (fun h1 : term326 = True => @lem5403122)). Qed.
Lemma lem5403125 : term326 = True.
Proof. exact (EQ_MP (@lem5403124) (@lem5403122)). Qed.
Lemma lem5403126 : term320 = True.
Proof. exact (TRANS (@lem5403121) (@lem5403125)). Qed.
Lemma lem5403127 : True = term320.
Proof. exact (SYM (@lem5403126)). Qed.
Lemma lem5403128 : term320.
Proof. exact (EQ_MP (@lem5403127) (@lem0)). Qed.
Lemma lem5403129 : term395.
Proof. exact (@lem5403118 (@lem5403128)). Qed.
Lemma lem5403131 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403132 : term320 = term326.
Proof. exact (@lem5403131 (NUMERAL 0) term133). Qed.
Lemma lem5403133 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403134 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403135 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403134 h1) (fun h1 : term326 = True => @lem5403133)). Qed.
Lemma lem5403136 : term326 = True.
Proof. exact (EQ_MP (@lem5403135) (@lem5403133)). Qed.
Lemma lem5403137 : term320 = True.
Proof. exact (TRANS (@lem5403132) (@lem5403136)). Qed.
Lemma lem5403138 : True = term320.
Proof. exact (SYM (@lem5403137)). Qed.
Lemma lem5403139 : term320.
Proof. exact (EQ_MP (@lem5403138) (@lem0)). Qed.
Lemma lem5403140 : term393 = term396.
Proof. exact (@lem5403129 (@lem5403139)). Qed.
Lemma lem5403142 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5403143 : term215 = term220.
Proof. exact (@lem5403142 term133 term133). Qed.
Lemma lem5403144 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403145 : term199 = term133.
Proof. exact (EQ_MP (@lem5403144) (@lem940073)). Qed.
Lemma lem5403146 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403147 : term197 = term132.
Proof. exact (MK_COMB (@lem5403146) (@lem5403145)). Qed.
Lemma lem5403148 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5403149 : term220 = term187.
Proof. exact (MK_COMB (@lem5403148) (@lem5403147)). Qed.
Lemma lem5403150 : term215 = term187.
Proof. exact (TRANS (@lem5403143) (@lem5403149)). Qed.
Lemma lem5403152 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403153 : term331 = term118.
Proof. exact (@lem5403152 term133). Qed.
Lemma lem5403154 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5403155 : term397 = term120.
Proof. exact (MK_COMB (@lem5403154) (@lem5403153)). Qed.
Lemma lem5403156 : term396 = term391.
Proof. exact (MK_COMB (@lem5403155) (@lem5403150)). Qed.
Lemma lem5403158 (m : nat) (n : nat) : (term398 m n) = (term399 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5403159 : term391 = term400.
Proof. exact (@lem5403158 (NUMERAL 0) term133). Qed.
Lemma lem5403160 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403161 (h1 : term327 = (BIT1 0)) : (term133 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5403162 : (term327 = (BIT1 0)) = ((term133 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403161 h1) (fun h1 : (term133 = (NUMERAL 0)) = False => @lem5403160)). Qed.
Lemma lem5403163 : (term133 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5403162) (@lem5403160)). Qed.
Lemma lem5403164 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5403165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5403166 : term401 = (and True).
Proof. exact (MK_COMB (@lem5403165) (@lem5403164)). Qed.
Lemma lem5403167 : term400 = (True /\ False).
Proof. exact (MK_COMB (@lem5403166) (@lem5403163)). Qed.
Lemma lem5403169 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5403170 : term400 = False.
Proof. exact (TRANS (@lem5403167) (@lem5403169)). Qed.
Lemma lem5403171 : term391 = False.
Proof. exact (TRANS (@lem5403159) (@lem5403170)). Qed.
Lemma lem5403172 : term396 = False.
Proof. exact (TRANS (@lem5403156) (@lem5403171)). Qed.
Lemma lem5403173 : term393 = False.
Proof. exact (TRANS (@lem5403140) (@lem5403172)). Qed.
Lemma lem5403174 : term391 = False.
Proof. exact (TRANS (@lem5403117) (@lem5403173)). Qed.
Lemma lem5403175 : term390 = False.
Proof. exact (TRANS (@lem5403108) (@lem5403174)). Qed.
Lemma lem5403176 (_69895 : int) (_69896 : int) (h1 : term402 _69895 _69896) : False.
Proof. exact (EQ_MP (@lem5403175) (@lem5403105 _69895 _69896 h1)). Qed.
Lemma lem5403177 (_69895 : int) (_69896 : int) (h1 : term312 _69895 _69896) : False.
Proof. exact (or_elim (@lem5402379 _69895 _69896 h1) (fun h0 : term318 _69895 _69896 => @lem5402885 _69895 _69896 h0) (fun h0 : term402 _69895 _69896 => @lem5403176 _69895 _69896 h0)). Qed.
Lemma lem5403178 (_69895 : int) (_69896 : int) (h1 : term308 _69895 _69896) : term308 _69895 _69896.
Proof. exact (h1). Qed.
Lemma lem5403179 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term403 _69895 _69896.
Proof. exact (h1). Qed.
Lemma lem5403180 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term309 _69895 _69896.
Proof. exact (proj2 (@lem5403179 _69895 _69896 h1)). Qed.
Lemma lem5403182 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term296 _69895 _69896.
Proof. exact (proj2 (@lem5403180 _69895 _69896 h1)). Qed.
Lemma lem5403184 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term283 _69895 _69896.
Proof. exact (proj2 (@lem5403182 _69895 _69896 h1)). Qed.
Lemma lem5403185 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : (real_of_int _69895) = term118.
Proof. exact (proj1 (@lem5403182 _69895 _69896 h1)). Qed.
Lemma lem5403186 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term264 _69896.
Proof. exact (proj2 (@lem5403184 _69895 _69896 h1)). Qed.
Lemma lem5403187 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term257 _69895 _69896.
Proof. exact (proj1 (@lem5403184 _69895 _69896 h1)). Qed.
Lemma lem5403189 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term249 _69895 _69896.
Proof. exact (proj1 (@lem5403187 _69895 _69896 h1)). Qed.
Lemma lem5403191 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5403192 : term319 = term320.
Proof. exact (@lem5403191 term118 term132). Qed.
Lemma lem5403194 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403195 : term132 = term214.
Proof. exact (@lem5403194 term133). Qed.
Lemma lem5403197 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403198 : term118 = term184.
Proof. exact (@lem5403197 (NUMERAL 0)). Qed.
Lemma lem5403199 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5403200 : term321 = term322.
Proof. exact (MK_COMB (@lem5403199) (@lem5403198)). Qed.
Lemma lem5403201 : term320 = term323.
Proof. exact (MK_COMB (@lem5403200) (@lem5403195)). Qed.
Lemma lem5403202 : term324.
Proof. exact (@lem1980255 term118 term132 term132 term132). Qed.
Lemma lem5403204 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403205 : term320 = term326.
Proof. exact (@lem5403204 (NUMERAL 0) term133). Qed.
Lemma lem5403206 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403207 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403208 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403207 h1) (fun h1 : term326 = True => @lem5403206)). Qed.
Lemma lem5403209 : term326 = True.
Proof. exact (EQ_MP (@lem5403208) (@lem5403206)). Qed.
Lemma lem5403210 : term320 = True.
Proof. exact (TRANS (@lem5403205) (@lem5403209)). Qed.
Lemma lem5403211 : True = term320.
Proof. exact (SYM (@lem5403210)). Qed.
Lemma lem5403212 : term320.
Proof. exact (EQ_MP (@lem5403211) (@lem0)). Qed.
Lemma lem5403213 : term328.
Proof. exact (@lem5403202 (@lem5403212)). Qed.
Lemma lem5403215 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403216 : term320 = term326.
Proof. exact (@lem5403215 (NUMERAL 0) term133). Qed.
Lemma lem5403217 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403218 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403219 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403218 h1) (fun h1 : term326 = True => @lem5403217)). Qed.
Lemma lem5403220 : term326 = True.
Proof. exact (EQ_MP (@lem5403219) (@lem5403217)). Qed.
Lemma lem5403221 : term320 = True.
Proof. exact (TRANS (@lem5403216) (@lem5403220)). Qed.
Lemma lem5403222 : True = term320.
Proof. exact (SYM (@lem5403221)). Qed.
Lemma lem5403223 : term320.
Proof. exact (EQ_MP (@lem5403222) (@lem0)). Qed.
Lemma lem5403224 : term323 = term329.
Proof. exact (@lem5403213 (@lem5403223)). Qed.
Lemma lem5403226 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403227 : term196 = term197.
Proof. exact (@lem5403226 term133 term133). Qed.
Lemma lem5403228 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403229 : term199 = term133.
Proof. exact (EQ_MP (@lem5403228) (@lem940073)). Qed.
Lemma lem5403230 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403231 : term197 = term132.
Proof. exact (MK_COMB (@lem5403230) (@lem5403229)). Qed.
Lemma lem5403232 : term196 = term132.
Proof. exact (TRANS (@lem5403227) (@lem5403231)). Qed.
Lemma lem5403234 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403235 : term331 = term118.
Proof. exact (@lem5403234 term133). Qed.
Lemma lem5403236 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5403237 : term332 = term321.
Proof. exact (MK_COMB (@lem5403236) (@lem5403235)). Qed.
Lemma lem5403238 : term329 = term320.
Proof. exact (MK_COMB (@lem5403237) (@lem5403232)). Qed.
Lemma lem5403240 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403241 : term320 = term326.
Proof. exact (@lem5403240 (NUMERAL 0) term133). Qed.
Lemma lem5403242 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403243 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403244 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403243 h1) (fun h1 : term326 = True => @lem5403242)). Qed.
Lemma lem5403245 : term326 = True.
Proof. exact (EQ_MP (@lem5403244) (@lem5403242)). Qed.
Lemma lem5403246 : term320 = True.
Proof. exact (TRANS (@lem5403241) (@lem5403245)). Qed.
Lemma lem5403247 : term329 = True.
Proof. exact (TRANS (@lem5403238) (@lem5403246)). Qed.
Lemma lem5403248 : term323 = True.
Proof. exact (TRANS (@lem5403224) (@lem5403247)). Qed.
Lemma lem5403249 : term320 = True.
Proof. exact (TRANS (@lem5403201) (@lem5403248)). Qed.
Lemma lem5403250 : term319 = True.
Proof. exact (TRANS (@lem5403192) (@lem5403249)). Qed.
Lemma lem5403251 : True = term319.
Proof. exact (SYM (@lem5403250)). Qed.
Lemma lem5403252 : term319.
Proof. exact (EQ_MP (@lem5403251) (@lem0)). Qed.
Lemma lem5403253 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term404 _69895 _69896.
Proof. exact (conj (@lem5403252) (@lem5403189 _69895 _69896 h1)). Qed.
Lemma lem5403255 (x : real) (y : real) : term334 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5403256 (_69895 : int) (_69896 : int) : term405 _69895 _69896.
Proof. exact (@lem5403255 term132 (term245 _69895 _69896)). Qed.
Lemma lem5403257 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term406 _69895 _69896.
Proof. exact (@lem5403256 _69895 _69896 (@lem5403253 _69895 _69896 h1)). Qed.
Lemma lem5403258 (_69895 : int) (_69896 : int) : (term407 _69895 _69896) = (term245 _69895 _69896).
Proof. exact (@lem1982733 (term245 _69895 _69896)). Qed.
Lemma lem5403259 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5403260 (_69895 : int) (_69896 : int) : (term408 _69895 _69896) = (term248 _69895 _69896).
Proof. exact (MK_COMB (@lem5403259) (@lem5403258 _69895 _69896)). Qed.
Lemma lem5403261 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5403262 (_69895 : int) (_69896 : int) : (term406 _69895 _69896) = (term249 _69895 _69896).
Proof. exact (MK_COMB (@lem5403260 _69895 _69896) (@lem5403261)). Qed.
Lemma lem5403263 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term249 _69895 _69896.
Proof. exact (EQ_MP (@lem5403262 _69895 _69896) (@lem5403257 _69895 _69896 h1)). Qed.
Lemma lem5403265 (y : real) : term339 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5403266 (_69895 : int) : term340 _69895.
Proof. exact (@lem5403265 (real_of_int _69895)). Qed.
Lemma lem5403267 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term341 _69895.
Proof. exact (@lem5403266 _69895 (@lem5403185 _69895 _69896 h1)). Qed.
Lemma lem5403268 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term342 _69895.
Proof. exact (@lem5403267 _69895 _69896 h1 term132). Qed.
Lemma lem5403269 (_69895 : int) : (term342 _69895) = ((term343 _69895) = term118).
Proof. exact (eq_refl (term342 _69895)). Qed.
Lemma lem5403270 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : (term343 _69895) = term118.
Proof. exact (EQ_MP (@lem5403269 _69895) (@lem5403268 _69895 _69896 h1)). Qed.
Lemma lem5403271 (_69895 : int) : (term343 _69895) = (real_of_int _69895).
Proof. exact (@lem1982733 (real_of_int _69895)). Qed.
Lemma lem5403272 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5403273 (_69895 : int) : (term344 _69895) = (term122 _69895).
Proof. exact (MK_COMB (@lem5403272) (@lem5403271 _69895)). Qed.
Lemma lem5403274 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5403275 (_69895 : int) : ((term343 _69895) = term118) = ((real_of_int _69895) = term118).
Proof. exact (MK_COMB (@lem5403273 _69895) (@lem5403274)). Qed.
Lemma lem5403276 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : (real_of_int _69895) = term118.
Proof. exact (EQ_MP (@lem5403275 _69895) (@lem5403270 _69895 _69896 h1)). Qed.
Lemma lem5403277 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term409 _69895 _69896.
Proof. exact (conj (@lem5403276 _69895 _69896 h1) (@lem5403263 _69895 _69896 h1)). Qed.
Lemma lem5403279 (x : real) (y : real) : term346 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5403280 (_69895 : int) (_69896 : int) : term410 _69895 _69896.
Proof. exact (@lem5403279 (real_of_int _69895) (term245 _69895 _69896)). Qed.
Lemma lem5403281 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term411 _69895 _69896.
Proof. exact (@lem5403280 _69895 _69896 (@lem5403277 _69895 _69896 h1)). Qed.
Lemma lem5403282 (_69895 : int) (_69896 : int) : (term412 _69895 _69896) = (term413 _69895 _69896).
Proof. exact (@lem1982763 (real_of_int _69895) (term246 _69895) (real_of_int _69896)). Qed.
Lemma lem5403283 (_69895 : int) : (term353 _69895) = (term354 _69895).
Proof. exact (@lem1982715 term187 (real_of_int _69895)). Qed.
Lemma lem5403285 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403286 : term132 = term214.
Proof. exact (@lem5403285 term133). Qed.
Lemma lem5403288 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5403289 : term187 = term188.
Proof. exact (@lem5403288 term133). Qed.
Lemma lem5403290 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5403291 : term355 = term356.
Proof. exact (MK_COMB (@lem5403290) (@lem5403289)). Qed.
Lemma lem5403292 : term357 = term358.
Proof. exact (MK_COMB (@lem5403291) (@lem5403286)). Qed.
Lemma lem5403293 : term359.
Proof. exact (@lem1981473 term187 term132 term132 term132 term118 term132). Qed.
Lemma lem5403295 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403296 : term320 = term326.
Proof. exact (@lem5403295 (NUMERAL 0) term133). Qed.
Lemma lem5403297 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403298 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403299 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403298 h1) (fun h1 : term326 = True => @lem5403297)). Qed.
Lemma lem5403300 : term326 = True.
Proof. exact (EQ_MP (@lem5403299) (@lem5403297)). Qed.
Lemma lem5403301 : term320 = True.
Proof. exact (TRANS (@lem5403296) (@lem5403300)). Qed.
Lemma lem5403302 : True = term320.
Proof. exact (SYM (@lem5403301)). Qed.
Lemma lem5403303 : term320.
Proof. exact (EQ_MP (@lem5403302) (@lem0)). Qed.
Lemma lem5403304 : term360.
Proof. exact (@lem5403293 (@lem5403303)). Qed.
Lemma lem5403306 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403307 : term320 = term326.
Proof. exact (@lem5403306 (NUMERAL 0) term133). Qed.
Lemma lem5403308 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403309 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403310 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403309 h1) (fun h1 : term326 = True => @lem5403308)). Qed.
Lemma lem5403311 : term326 = True.
Proof. exact (EQ_MP (@lem5403310) (@lem5403308)). Qed.
Lemma lem5403312 : term320 = True.
Proof. exact (TRANS (@lem5403307) (@lem5403311)). Qed.
Lemma lem5403313 : True = term320.
Proof. exact (SYM (@lem5403312)). Qed.
Lemma lem5403314 : term320.
Proof. exact (EQ_MP (@lem5403313) (@lem0)). Qed.
Lemma lem5403315 : term361.
Proof. exact (@lem5403304 (@lem5403314)). Qed.
Lemma lem5403317 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403318 : term320 = term326.
Proof. exact (@lem5403317 (NUMERAL 0) term133). Qed.
Lemma lem5403319 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403320 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403321 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403320 h1) (fun h1 : term326 = True => @lem5403319)). Qed.
Lemma lem5403322 : term326 = True.
Proof. exact (EQ_MP (@lem5403321) (@lem5403319)). Qed.
Lemma lem5403323 : term320 = True.
Proof. exact (TRANS (@lem5403318) (@lem5403322)). Qed.
Lemma lem5403324 : True = term320.
Proof. exact (SYM (@lem5403323)). Qed.
Lemma lem5403325 : term320.
Proof. exact (EQ_MP (@lem5403324) (@lem0)). Qed.
Lemma lem5403326 : term362.
Proof. exact (@lem5403315 (@lem5403325)). Qed.
Lemma lem5403328 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403329 : term196 = term197.
Proof. exact (@lem5403328 term133 term133). Qed.
Lemma lem5403330 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403331 : term199 = term133.
Proof. exact (EQ_MP (@lem5403330) (@lem940073)). Qed.
Lemma lem5403332 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403333 : term197 = term132.
Proof. exact (MK_COMB (@lem5403332) (@lem5403331)). Qed.
Lemma lem5403334 : term196 = term132.
Proof. exact (TRANS (@lem5403329) (@lem5403333)). Qed.
Lemma lem5403336 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5403337 : term215 = term220.
Proof. exact (@lem5403336 term133 term133). Qed.
Lemma lem5403338 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403339 : term199 = term133.
Proof. exact (EQ_MP (@lem5403338) (@lem940073)). Qed.
Lemma lem5403340 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403341 : term197 = term132.
Proof. exact (MK_COMB (@lem5403340) (@lem5403339)). Qed.
Lemma lem5403342 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5403343 : term220 = term187.
Proof. exact (MK_COMB (@lem5403342) (@lem5403341)). Qed.
Lemma lem5403344 : term215 = term187.
Proof. exact (TRANS (@lem5403337) (@lem5403343)). Qed.
Lemma lem5403345 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5403346 : term363 = term355.
Proof. exact (MK_COMB (@lem5403345) (@lem5403344)). Qed.
Lemma lem5403347 : term364 = term357.
Proof. exact (MK_COMB (@lem5403346) (@lem5403334)). Qed.
Lemma lem5403349 (m : nat) : (term365 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5403350 : term357 = term118.
Proof. exact (@lem5403349 term133). Qed.
Lemma lem5403351 : term364 = term118.
Proof. exact (TRANS (@lem5403347) (@lem5403350)). Qed.
Lemma lem5403352 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5403353 : term366 = term367.
Proof. exact (MK_COMB (@lem5403352) (@lem5403351)). Qed.
Lemma lem5403354 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem5403355 : term368 = term331.
Proof. exact (MK_COMB (@lem5403353) (@lem5403354)). Qed.
Lemma lem5403357 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403358 : term331 = term118.
Proof. exact (@lem5403357 term133). Qed.
Lemma lem5403359 : term368 = term118.
Proof. exact (TRANS (@lem5403355) (@lem5403358)). Qed.
Lemma lem5403361 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403362 : term196 = term197.
Proof. exact (@lem5403361 term133 term133). Qed.
Lemma lem5403363 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403364 : term199 = term133.
Proof. exact (EQ_MP (@lem5403363) (@lem940073)). Qed.
Lemma lem5403365 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403366 : term197 = term132.
Proof. exact (MK_COMB (@lem5403365) (@lem5403364)). Qed.
Lemma lem5403367 : term196 = term132.
Proof. exact (TRANS (@lem5403362) (@lem5403366)). Qed.
Lemma lem5403368 : term367 = term367.
Proof. exact (eq_refl term367). Qed.
Lemma lem5403369 : term369 = term331.
Proof. exact (MK_COMB (@lem5403368) (@lem5403367)). Qed.
Lemma lem5403371 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403372 : term331 = term118.
Proof. exact (@lem5403371 term133). Qed.
Lemma lem5403373 : term369 = term118.
Proof. exact (TRANS (@lem5403369) (@lem5403372)). Qed.
Lemma lem5403374 : term118 = term369.
Proof. exact (SYM (@lem5403373)). Qed.
Lemma lem5403375 : term368 = term369.
Proof. exact (TRANS (@lem5403359) (@lem5403374)). Qed.
Lemma lem5403376 : term358 = term184.
Proof. exact (@lem5403326 (@lem5403375)). Qed.
Lemma lem5403377 : term357 = term184.
Proof. exact (TRANS (@lem5403292) (@lem5403376)). Qed.
Lemma lem5403379 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5403380 : term184 = term118.
Proof. exact (@lem5403379 term118). Qed.
Lemma lem5403381 : term357 = term118.
Proof. exact (TRANS (@lem5403377) (@lem5403380)). Qed.
Lemma lem5403382 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5403383 : term370 = term367.
Proof. exact (MK_COMB (@lem5403382) (@lem5403381)). Qed.
Lemma lem5403384 (_69895 : int) : (real_of_int _69895) = (real_of_int _69895).
Proof. exact (eq_refl (real_of_int _69895)). Qed.
Lemma lem5403385 (_69895 : int) : (term354 _69895) = (term371 _69895).
Proof. exact (MK_COMB (@lem5403383) (@lem5403384 _69895)). Qed.
Lemma lem5403386 (_69895 : int) : (term353 _69895) = (term371 _69895).
Proof. exact (TRANS (@lem5403283 _69895) (@lem5403385 _69895)). Qed.
Lemma lem5403387 (_69895 : int) : (term371 _69895) = term118.
Proof. exact (@lem1982719 (real_of_int _69895)). Qed.
Lemma lem5403388 (_69895 : int) : (term353 _69895) = term118.
Proof. exact (TRANS (@lem5403386 _69895) (@lem5403387 _69895)). Qed.
Lemma lem5403389 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5403390 (_69895 : int) : (term372 _69895) = term145.
Proof. exact (MK_COMB (@lem5403389) (@lem5403388 _69895)). Qed.
Lemma lem5403391 (_69896 : int) : (real_of_int _69896) = (real_of_int _69896).
Proof. exact (eq_refl (real_of_int _69896)). Qed.
Lemma lem5403392 (_69895 : int) (_69896 : int) : (term413 _69895 _69896) = (term414 _69896).
Proof. exact (MK_COMB (@lem5403390 _69895) (@lem5403391 _69896)). Qed.
Lemma lem5403393 (_69895 : int) (_69896 : int) : (term412 _69895 _69896) = (term414 _69896).
Proof. exact (TRANS (@lem5403282 _69895 _69896) (@lem5403392 _69895 _69896)). Qed.
Lemma lem5403394 (_69896 : int) : (term414 _69896) = (real_of_int _69896).
Proof. exact (@lem1982721 (real_of_int _69896)). Qed.
Lemma lem5403395 (_69895 : int) (_69896 : int) : (term412 _69895 _69896) = (real_of_int _69896).
Proof. exact (TRANS (@lem5403393 _69895 _69896) (@lem5403394 _69896)). Qed.
Lemma lem5403396 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5403397 (_69895 : int) (_69896 : int) : (term415 _69895 _69896) = (term206 _69896).
Proof. exact (MK_COMB (@lem5403396) (@lem5403395 _69895 _69896)). Qed.
Lemma lem5403398 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5403399 (_69895 : int) (_69896 : int) : (term411 _69895 _69896) = (term207 _69896).
Proof. exact (MK_COMB (@lem5403397 _69895 _69896) (@lem5403398)). Qed.
Lemma lem5403400 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term207 _69896.
Proof. exact (EQ_MP (@lem5403399 _69895 _69896) (@lem5403281 _69895 _69896 h1)). Qed.
Lemma lem5403402 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5403403 : term319 = term320.
Proof. exact (@lem5403402 term118 term132). Qed.
Lemma lem5403405 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403406 : term132 = term214.
Proof. exact (@lem5403405 term133). Qed.
Lemma lem5403408 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403409 : term118 = term184.
Proof. exact (@lem5403408 (NUMERAL 0)). Qed.
Lemma lem5403410 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5403411 : term321 = term322.
Proof. exact (MK_COMB (@lem5403410) (@lem5403409)). Qed.
Lemma lem5403412 : term320 = term323.
Proof. exact (MK_COMB (@lem5403411) (@lem5403406)). Qed.
Lemma lem5403413 : term324.
Proof. exact (@lem1980255 term118 term132 term132 term132). Qed.
Lemma lem5403415 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403416 : term320 = term326.
Proof. exact (@lem5403415 (NUMERAL 0) term133). Qed.
Lemma lem5403417 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403418 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403419 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403418 h1) (fun h1 : term326 = True => @lem5403417)). Qed.
Lemma lem5403420 : term326 = True.
Proof. exact (EQ_MP (@lem5403419) (@lem5403417)). Qed.
Lemma lem5403421 : term320 = True.
Proof. exact (TRANS (@lem5403416) (@lem5403420)). Qed.
Lemma lem5403422 : True = term320.
Proof. exact (SYM (@lem5403421)). Qed.
Lemma lem5403423 : term320.
Proof. exact (EQ_MP (@lem5403422) (@lem0)). Qed.
Lemma lem5403424 : term328.
Proof. exact (@lem5403413 (@lem5403423)). Qed.
Lemma lem5403426 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403427 : term320 = term326.
Proof. exact (@lem5403426 (NUMERAL 0) term133). Qed.
Lemma lem5403428 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403429 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403430 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403429 h1) (fun h1 : term326 = True => @lem5403428)). Qed.
Lemma lem5403431 : term326 = True.
Proof. exact (EQ_MP (@lem5403430) (@lem5403428)). Qed.
Lemma lem5403432 : term320 = True.
Proof. exact (TRANS (@lem5403427) (@lem5403431)). Qed.
Lemma lem5403433 : True = term320.
Proof. exact (SYM (@lem5403432)). Qed.
Lemma lem5403434 : term320.
Proof. exact (EQ_MP (@lem5403433) (@lem0)). Qed.
Lemma lem5403435 : term323 = term329.
Proof. exact (@lem5403424 (@lem5403434)). Qed.
Lemma lem5403437 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403438 : term196 = term197.
Proof. exact (@lem5403437 term133 term133). Qed.
Lemma lem5403439 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403440 : term199 = term133.
Proof. exact (EQ_MP (@lem5403439) (@lem940073)). Qed.
Lemma lem5403441 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403442 : term197 = term132.
Proof. exact (MK_COMB (@lem5403441) (@lem5403440)). Qed.
Lemma lem5403443 : term196 = term132.
Proof. exact (TRANS (@lem5403438) (@lem5403442)). Qed.
Lemma lem5403445 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403446 : term331 = term118.
Proof. exact (@lem5403445 term133). Qed.
Lemma lem5403447 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5403448 : term332 = term321.
Proof. exact (MK_COMB (@lem5403447) (@lem5403446)). Qed.
Lemma lem5403449 : term329 = term320.
Proof. exact (MK_COMB (@lem5403448) (@lem5403443)). Qed.
Lemma lem5403451 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403452 : term320 = term326.
Proof. exact (@lem5403451 (NUMERAL 0) term133). Qed.
Lemma lem5403453 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403454 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403455 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403454 h1) (fun h1 : term326 = True => @lem5403453)). Qed.
Lemma lem5403456 : term326 = True.
Proof. exact (EQ_MP (@lem5403455) (@lem5403453)). Qed.
Lemma lem5403457 : term320 = True.
Proof. exact (TRANS (@lem5403452) (@lem5403456)). Qed.
Lemma lem5403458 : term329 = True.
Proof. exact (TRANS (@lem5403449) (@lem5403457)). Qed.
Lemma lem5403459 : term323 = True.
Proof. exact (TRANS (@lem5403435) (@lem5403458)). Qed.
Lemma lem5403460 : term320 = True.
Proof. exact (TRANS (@lem5403412) (@lem5403459)). Qed.
Lemma lem5403461 : term319 = True.
Proof. exact (TRANS (@lem5403403) (@lem5403460)). Qed.
Lemma lem5403462 : True = term319.
Proof. exact (SYM (@lem5403461)). Qed.
Lemma lem5403463 : term319.
Proof. exact (EQ_MP (@lem5403462) (@lem0)). Qed.
Lemma lem5403464 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term416 _69896.
Proof. exact (conj (@lem5403463) (@lem5403400 _69895 _69896 h1)). Qed.
Lemma lem5403466 (x : real) (y : real) : term334 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5403467 (_69896 : int) : term417 _69896.
Proof. exact (@lem5403466 term132 (real_of_int _69896)). Qed.
Lemma lem5403468 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term418 _69896.
Proof. exact (@lem5403467 _69896 (@lem5403464 _69895 _69896 h1)). Qed.
Lemma lem5403469 (_69896 : int) : (term343 _69896) = (real_of_int _69896).
Proof. exact (@lem1982733 (real_of_int _69896)). Qed.
Lemma lem5403470 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5403471 (_69896 : int) : (term419 _69896) = (term206 _69896).
Proof. exact (MK_COMB (@lem5403470) (@lem5403469 _69896)). Qed.
Lemma lem5403472 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5403473 (_69896 : int) : (term418 _69896) = (term207 _69896).
Proof. exact (MK_COMB (@lem5403471 _69896) (@lem5403472)). Qed.
Lemma lem5403474 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term207 _69896.
Proof. exact (EQ_MP (@lem5403473 _69896) (@lem5403468 _69895 _69896 h1)). Qed.
Lemma lem5403476 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5403477 : term319 = term320.
Proof. exact (@lem5403476 term118 term132). Qed.
Lemma lem5403479 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403480 : term132 = term214.
Proof. exact (@lem5403479 term133). Qed.
Lemma lem5403482 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403483 : term118 = term184.
Proof. exact (@lem5403482 (NUMERAL 0)). Qed.
Lemma lem5403484 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5403485 : term321 = term322.
Proof. exact (MK_COMB (@lem5403484) (@lem5403483)). Qed.
Lemma lem5403486 : term320 = term323.
Proof. exact (MK_COMB (@lem5403485) (@lem5403480)). Qed.
Lemma lem5403487 : term324.
Proof. exact (@lem1980255 term118 term132 term132 term132). Qed.
Lemma lem5403489 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403490 : term320 = term326.
Proof. exact (@lem5403489 (NUMERAL 0) term133). Qed.
Lemma lem5403491 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403492 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403493 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403492 h1) (fun h1 : term326 = True => @lem5403491)). Qed.
Lemma lem5403494 : term326 = True.
Proof. exact (EQ_MP (@lem5403493) (@lem5403491)). Qed.
Lemma lem5403495 : term320 = True.
Proof. exact (TRANS (@lem5403490) (@lem5403494)). Qed.
Lemma lem5403496 : True = term320.
Proof. exact (SYM (@lem5403495)). Qed.
Lemma lem5403497 : term320.
Proof. exact (EQ_MP (@lem5403496) (@lem0)). Qed.
Lemma lem5403498 : term328.
Proof. exact (@lem5403487 (@lem5403497)). Qed.
Lemma lem5403500 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403501 : term320 = term326.
Proof. exact (@lem5403500 (NUMERAL 0) term133). Qed.
Lemma lem5403502 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403503 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403504 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403503 h1) (fun h1 : term326 = True => @lem5403502)). Qed.
Lemma lem5403505 : term326 = True.
Proof. exact (EQ_MP (@lem5403504) (@lem5403502)). Qed.
Lemma lem5403506 : term320 = True.
Proof. exact (TRANS (@lem5403501) (@lem5403505)). Qed.
Lemma lem5403507 : True = term320.
Proof. exact (SYM (@lem5403506)). Qed.
Lemma lem5403508 : term320.
Proof. exact (EQ_MP (@lem5403507) (@lem0)). Qed.
Lemma lem5403509 : term323 = term329.
Proof. exact (@lem5403498 (@lem5403508)). Qed.
Lemma lem5403511 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403512 : term196 = term197.
Proof. exact (@lem5403511 term133 term133). Qed.
Lemma lem5403513 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403514 : term199 = term133.
Proof. exact (EQ_MP (@lem5403513) (@lem940073)). Qed.
Lemma lem5403515 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403516 : term197 = term132.
Proof. exact (MK_COMB (@lem5403515) (@lem5403514)). Qed.
Lemma lem5403517 : term196 = term132.
Proof. exact (TRANS (@lem5403512) (@lem5403516)). Qed.
Lemma lem5403519 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403520 : term331 = term118.
Proof. exact (@lem5403519 term133). Qed.
Lemma lem5403521 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5403522 : term332 = term321.
Proof. exact (MK_COMB (@lem5403521) (@lem5403520)). Qed.
Lemma lem5403523 : term329 = term320.
Proof. exact (MK_COMB (@lem5403522) (@lem5403517)). Qed.
Lemma lem5403525 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403526 : term320 = term326.
Proof. exact (@lem5403525 (NUMERAL 0) term133). Qed.
Lemma lem5403527 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403528 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403529 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403528 h1) (fun h1 : term326 = True => @lem5403527)). Qed.
Lemma lem5403530 : term326 = True.
Proof. exact (EQ_MP (@lem5403529) (@lem5403527)). Qed.
Lemma lem5403531 : term320 = True.
Proof. exact (TRANS (@lem5403526) (@lem5403530)). Qed.
Lemma lem5403532 : term329 = True.
Proof. exact (TRANS (@lem5403523) (@lem5403531)). Qed.
Lemma lem5403533 : term323 = True.
Proof. exact (TRANS (@lem5403509) (@lem5403532)). Qed.
Lemma lem5403534 : term320 = True.
Proof. exact (TRANS (@lem5403486) (@lem5403533)). Qed.
Lemma lem5403535 : term319 = True.
Proof. exact (TRANS (@lem5403477) (@lem5403534)). Qed.
Lemma lem5403536 : True = term319.
Proof. exact (SYM (@lem5403535)). Qed.
Lemma lem5403537 : term319.
Proof. exact (EQ_MP (@lem5403536) (@lem0)). Qed.
Lemma lem5403538 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term420 _69896.
Proof. exact (conj (@lem5403537) (@lem5403186 _69895 _69896 h1)). Qed.
Lemma lem5403540 (x : real) (y : real) : term334 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5403541 (_69896 : int) : term421 _69896.
Proof. exact (@lem5403540 term132 (term224 _69896)). Qed.
Lemma lem5403542 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term422 _69896.
Proof. exact (@lem5403541 _69896 (@lem5403538 _69895 _69896 h1)). Qed.
Lemma lem5403543 (_69896 : int) : (term423 _69896) = (term224 _69896).
Proof. exact (@lem1982733 (term224 _69896)). Qed.
Lemma lem5403544 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5403545 (_69896 : int) : (term424 _69896) = (term263 _69896).
Proof. exact (MK_COMB (@lem5403544) (@lem5403543 _69896)). Qed.
Lemma lem5403546 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5403547 (_69896 : int) : (term422 _69896) = (term264 _69896).
Proof. exact (MK_COMB (@lem5403545 _69896) (@lem5403546)). Qed.
Lemma lem5403548 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term264 _69896.
Proof. exact (EQ_MP (@lem5403547 _69896) (@lem5403542 _69895 _69896 h1)). Qed.
Lemma lem5403549 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term425 _69896.
Proof. exact (conj (@lem5403548 _69895 _69896 h1) (@lem5403474 _69895 _69896 h1)). Qed.
Lemma lem5403551 (x : real) (y : real) : term426 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5403552 (_69896 : int) : term427 _69896.
Proof. exact (@lem5403551 (term224 _69896) (real_of_int _69896)). Qed.
Lemma lem5403553 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term428 _69896.
Proof. exact (@lem5403552 _69896 (@lem5403549 _69895 _69896 h1)). Qed.
Lemma lem5403554 (_69896 : int) : (term429 _69896) = (term385 _69896).
Proof. exact (@lem1982759 (term246 _69896) (real_of_int _69896) term187). Qed.
Lemma lem5403555 (_69896 : int) : (term386 _69896) = (term354 _69896).
Proof. exact (@lem1982713 term187 (real_of_int _69896)). Qed.
Lemma lem5403557 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403558 : term132 = term214.
Proof. exact (@lem5403557 term133). Qed.
Lemma lem5403560 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5403561 : term187 = term188.
Proof. exact (@lem5403560 term133). Qed.
Lemma lem5403562 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5403563 : term355 = term356.
Proof. exact (MK_COMB (@lem5403562) (@lem5403561)). Qed.
Lemma lem5403564 : term357 = term358.
Proof. exact (MK_COMB (@lem5403563) (@lem5403558)). Qed.
Lemma lem5403565 : term359.
Proof. exact (@lem1981473 term187 term132 term132 term132 term118 term132). Qed.
Lemma lem5403567 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403568 : term320 = term326.
Proof. exact (@lem5403567 (NUMERAL 0) term133). Qed.
Lemma lem5403569 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403570 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403571 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403570 h1) (fun h1 : term326 = True => @lem5403569)). Qed.
Lemma lem5403572 : term326 = True.
Proof. exact (EQ_MP (@lem5403571) (@lem5403569)). Qed.
Lemma lem5403573 : term320 = True.
Proof. exact (TRANS (@lem5403568) (@lem5403572)). Qed.
Lemma lem5403574 : True = term320.
Proof. exact (SYM (@lem5403573)). Qed.
Lemma lem5403575 : term320.
Proof. exact (EQ_MP (@lem5403574) (@lem0)). Qed.
Lemma lem5403576 : term360.
Proof. exact (@lem5403565 (@lem5403575)). Qed.
Lemma lem5403578 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403579 : term320 = term326.
Proof. exact (@lem5403578 (NUMERAL 0) term133). Qed.
Lemma lem5403580 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403581 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403582 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403581 h1) (fun h1 : term326 = True => @lem5403580)). Qed.
Lemma lem5403583 : term326 = True.
Proof. exact (EQ_MP (@lem5403582) (@lem5403580)). Qed.
Lemma lem5403584 : term320 = True.
Proof. exact (TRANS (@lem5403579) (@lem5403583)). Qed.
Lemma lem5403585 : True = term320.
Proof. exact (SYM (@lem5403584)). Qed.
Lemma lem5403586 : term320.
Proof. exact (EQ_MP (@lem5403585) (@lem0)). Qed.
Lemma lem5403587 : term361.
Proof. exact (@lem5403576 (@lem5403586)). Qed.
Lemma lem5403589 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403590 : term320 = term326.
Proof. exact (@lem5403589 (NUMERAL 0) term133). Qed.
Lemma lem5403591 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403592 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403593 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403592 h1) (fun h1 : term326 = True => @lem5403591)). Qed.
Lemma lem5403594 : term326 = True.
Proof. exact (EQ_MP (@lem5403593) (@lem5403591)). Qed.
Lemma lem5403595 : term320 = True.
Proof. exact (TRANS (@lem5403590) (@lem5403594)). Qed.
Lemma lem5403596 : True = term320.
Proof. exact (SYM (@lem5403595)). Qed.
Lemma lem5403597 : term320.
Proof. exact (EQ_MP (@lem5403596) (@lem0)). Qed.
Lemma lem5403598 : term362.
Proof. exact (@lem5403587 (@lem5403597)). Qed.
Lemma lem5403600 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403601 : term196 = term197.
Proof. exact (@lem5403600 term133 term133). Qed.
Lemma lem5403602 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403603 : term199 = term133.
Proof. exact (EQ_MP (@lem5403602) (@lem940073)). Qed.
Lemma lem5403604 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403605 : term197 = term132.
Proof. exact (MK_COMB (@lem5403604) (@lem5403603)). Qed.
Lemma lem5403606 : term196 = term132.
Proof. exact (TRANS (@lem5403601) (@lem5403605)). Qed.
Lemma lem5403608 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5403609 : term215 = term220.
Proof. exact (@lem5403608 term133 term133). Qed.
Lemma lem5403610 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403611 : term199 = term133.
Proof. exact (EQ_MP (@lem5403610) (@lem940073)). Qed.
Lemma lem5403612 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403613 : term197 = term132.
Proof. exact (MK_COMB (@lem5403612) (@lem5403611)). Qed.
Lemma lem5403614 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5403615 : term220 = term187.
Proof. exact (MK_COMB (@lem5403614) (@lem5403613)). Qed.
Lemma lem5403616 : term215 = term187.
Proof. exact (TRANS (@lem5403609) (@lem5403615)). Qed.
Lemma lem5403617 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5403618 : term363 = term355.
Proof. exact (MK_COMB (@lem5403617) (@lem5403616)). Qed.
Lemma lem5403619 : term364 = term357.
Proof. exact (MK_COMB (@lem5403618) (@lem5403606)). Qed.
Lemma lem5403621 (m : nat) : (term365 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5403622 : term357 = term118.
Proof. exact (@lem5403621 term133). Qed.
Lemma lem5403623 : term364 = term118.
Proof. exact (TRANS (@lem5403619) (@lem5403622)). Qed.
Lemma lem5403624 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5403625 : term366 = term367.
Proof. exact (MK_COMB (@lem5403624) (@lem5403623)). Qed.
Lemma lem5403626 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem5403627 : term368 = term331.
Proof. exact (MK_COMB (@lem5403625) (@lem5403626)). Qed.
Lemma lem5403629 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403630 : term331 = term118.
Proof. exact (@lem5403629 term133). Qed.
Lemma lem5403631 : term368 = term118.
Proof. exact (TRANS (@lem5403627) (@lem5403630)). Qed.
Lemma lem5403633 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403634 : term196 = term197.
Proof. exact (@lem5403633 term133 term133). Qed.
Lemma lem5403635 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403636 : term199 = term133.
Proof. exact (EQ_MP (@lem5403635) (@lem940073)). Qed.
Lemma lem5403637 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403638 : term197 = term132.
Proof. exact (MK_COMB (@lem5403637) (@lem5403636)). Qed.
Lemma lem5403639 : term196 = term132.
Proof. exact (TRANS (@lem5403634) (@lem5403638)). Qed.
Lemma lem5403640 : term367 = term367.
Proof. exact (eq_refl term367). Qed.
Lemma lem5403641 : term369 = term331.
Proof. exact (MK_COMB (@lem5403640) (@lem5403639)). Qed.
Lemma lem5403643 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403644 : term331 = term118.
Proof. exact (@lem5403643 term133). Qed.
Lemma lem5403645 : term369 = term118.
Proof. exact (TRANS (@lem5403641) (@lem5403644)). Qed.
Lemma lem5403646 : term118 = term369.
Proof. exact (SYM (@lem5403645)). Qed.
Lemma lem5403647 : term368 = term369.
Proof. exact (TRANS (@lem5403631) (@lem5403646)). Qed.
Lemma lem5403648 : term358 = term184.
Proof. exact (@lem5403598 (@lem5403647)). Qed.
Lemma lem5403649 : term357 = term184.
Proof. exact (TRANS (@lem5403564) (@lem5403648)). Qed.
Lemma lem5403651 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5403652 : term184 = term118.
Proof. exact (@lem5403651 term118). Qed.
Lemma lem5403653 : term357 = term118.
Proof. exact (TRANS (@lem5403649) (@lem5403652)). Qed.
Lemma lem5403654 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5403655 : term370 = term367.
Proof. exact (MK_COMB (@lem5403654) (@lem5403653)). Qed.
Lemma lem5403656 (_69896 : int) : (real_of_int _69896) = (real_of_int _69896).
Proof. exact (eq_refl (real_of_int _69896)). Qed.
Lemma lem5403657 (_69896 : int) : (term354 _69896) = (term371 _69896).
Proof. exact (MK_COMB (@lem5403655) (@lem5403656 _69896)). Qed.
Lemma lem5403658 (_69896 : int) : (term386 _69896) = (term371 _69896).
Proof. exact (TRANS (@lem5403555 _69896) (@lem5403657 _69896)). Qed.
Lemma lem5403659 (_69896 : int) : (term371 _69896) = term118.
Proof. exact (@lem1982719 (real_of_int _69896)). Qed.
Lemma lem5403660 (_69896 : int) : (term386 _69896) = term118.
Proof. exact (TRANS (@lem5403658 _69896) (@lem5403659 _69896)). Qed.
Lemma lem5403661 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5403662 (_69896 : int) : (term387 _69896) = term145.
Proof. exact (MK_COMB (@lem5403661) (@lem5403660 _69896)). Qed.
Lemma lem5403663 : term187 = term187.
Proof. exact (eq_refl term187). Qed.
Lemma lem5403664 (_69896 : int) : (term385 _69896) = term373.
Proof. exact (MK_COMB (@lem5403662 _69896) (@lem5403663)). Qed.
Lemma lem5403665 (_69896 : int) : (term429 _69896) = term373.
Proof. exact (TRANS (@lem5403554 _69896) (@lem5403664 _69896)). Qed.
Lemma lem5403666 : term373 = term187.
Proof. exact (@lem1982721 term187). Qed.
Lemma lem5403667 (_69896 : int) : (term429 _69896) = term187.
Proof. exact (TRANS (@lem5403665 _69896) (@lem5403666)). Qed.
Lemma lem5403668 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5403669 (_69896 : int) : (term430 _69896) = term389.
Proof. exact (MK_COMB (@lem5403668) (@lem5403667 _69896)). Qed.
Lemma lem5403670 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5403671 (_69896 : int) : (term428 _69896) = term390.
Proof. exact (MK_COMB (@lem5403669 _69896) (@lem5403670)). Qed.
Lemma lem5403672 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : term390.
Proof. exact (EQ_MP (@lem5403671 _69896) (@lem5403553 _69895 _69896 h1)). Qed.
Lemma lem5403674 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5403675 : term390 = term391.
Proof. exact (@lem5403674 term118 term187). Qed.
Lemma lem5403677 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5403678 : term187 = term188.
Proof. exact (@lem5403677 term133). Qed.
Lemma lem5403680 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403681 : term118 = term184.
Proof. exact (@lem5403680 (NUMERAL 0)). Qed.
Lemma lem5403682 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5403683 : term120 = term392.
Proof. exact (MK_COMB (@lem5403682) (@lem5403681)). Qed.
Lemma lem5403684 : term391 = term393.
Proof. exact (MK_COMB (@lem5403683) (@lem5403678)). Qed.
Lemma lem5403685 : term394.
Proof. exact (@lem1980026 term118 term132 term187 term132). Qed.
Lemma lem5403687 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403688 : term320 = term326.
Proof. exact (@lem5403687 (NUMERAL 0) term133). Qed.
Lemma lem5403689 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403690 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403691 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403690 h1) (fun h1 : term326 = True => @lem5403689)). Qed.
Lemma lem5403692 : term326 = True.
Proof. exact (EQ_MP (@lem5403691) (@lem5403689)). Qed.
Lemma lem5403693 : term320 = True.
Proof. exact (TRANS (@lem5403688) (@lem5403692)). Qed.
Lemma lem5403694 : True = term320.
Proof. exact (SYM (@lem5403693)). Qed.
Lemma lem5403695 : term320.
Proof. exact (EQ_MP (@lem5403694) (@lem0)). Qed.
Lemma lem5403696 : term395.
Proof. exact (@lem5403685 (@lem5403695)). Qed.
Lemma lem5403698 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403699 : term320 = term326.
Proof. exact (@lem5403698 (NUMERAL 0) term133). Qed.
Lemma lem5403700 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403701 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403702 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403701 h1) (fun h1 : term326 = True => @lem5403700)). Qed.
Lemma lem5403703 : term326 = True.
Proof. exact (EQ_MP (@lem5403702) (@lem5403700)). Qed.
Lemma lem5403704 : term320 = True.
Proof. exact (TRANS (@lem5403699) (@lem5403703)). Qed.
Lemma lem5403705 : True = term320.
Proof. exact (SYM (@lem5403704)). Qed.
Lemma lem5403706 : term320.
Proof. exact (EQ_MP (@lem5403705) (@lem0)). Qed.
Lemma lem5403707 : term393 = term396.
Proof. exact (@lem5403696 (@lem5403706)). Qed.
Lemma lem5403709 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5403710 : term215 = term220.
Proof. exact (@lem5403709 term133 term133). Qed.
Lemma lem5403711 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403712 : term199 = term133.
Proof. exact (EQ_MP (@lem5403711) (@lem940073)). Qed.
Lemma lem5403713 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403714 : term197 = term132.
Proof. exact (MK_COMB (@lem5403713) (@lem5403712)). Qed.
Lemma lem5403715 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5403716 : term220 = term187.
Proof. exact (MK_COMB (@lem5403715) (@lem5403714)). Qed.
Lemma lem5403717 : term215 = term187.
Proof. exact (TRANS (@lem5403710) (@lem5403716)). Qed.
Lemma lem5403719 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403720 : term331 = term118.
Proof. exact (@lem5403719 term133). Qed.
Lemma lem5403721 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5403722 : term397 = term120.
Proof. exact (MK_COMB (@lem5403721) (@lem5403720)). Qed.
Lemma lem5403723 : term396 = term391.
Proof. exact (MK_COMB (@lem5403722) (@lem5403717)). Qed.
Lemma lem5403725 (m : nat) (n : nat) : (term398 m n) = (term399 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5403726 : term391 = term400.
Proof. exact (@lem5403725 (NUMERAL 0) term133). Qed.
Lemma lem5403727 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403728 (h1 : term327 = (BIT1 0)) : (term133 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5403729 : (term327 = (BIT1 0)) = ((term133 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403728 h1) (fun h1 : (term133 = (NUMERAL 0)) = False => @lem5403727)). Qed.
Lemma lem5403730 : (term133 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5403729) (@lem5403727)). Qed.
Lemma lem5403731 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5403732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5403733 : term401 = (and True).
Proof. exact (MK_COMB (@lem5403732) (@lem5403731)). Qed.
Lemma lem5403734 : term400 = (True /\ False).
Proof. exact (MK_COMB (@lem5403733) (@lem5403730)). Qed.
Lemma lem5403736 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5403737 : term400 = False.
Proof. exact (TRANS (@lem5403734) (@lem5403736)). Qed.
Lemma lem5403738 : term391 = False.
Proof. exact (TRANS (@lem5403726) (@lem5403737)). Qed.
Lemma lem5403739 : term396 = False.
Proof. exact (TRANS (@lem5403723) (@lem5403738)). Qed.
Lemma lem5403740 : term393 = False.
Proof. exact (TRANS (@lem5403707) (@lem5403739)). Qed.
Lemma lem5403741 : term391 = False.
Proof. exact (TRANS (@lem5403684) (@lem5403740)). Qed.
Lemma lem5403742 : term390 = False.
Proof. exact (TRANS (@lem5403675) (@lem5403741)). Qed.
Lemma lem5403743 (_69895 : int) (_69896 : int) (h1 : term403 _69895 _69896) : False.
Proof. exact (EQ_MP (@lem5403742) (@lem5403672 _69895 _69896 h1)). Qed.
Lemma lem5403744 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term431 _69895 _69896.
Proof. exact (h1). Qed.
Lemma lem5403745 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term310 _69895 _69896.
Proof. exact (proj2 (@lem5403744 _69895 _69896 h1)). Qed.
Lemma lem5403747 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term297 _69895 _69896.
Proof. exact (proj2 (@lem5403745 _69895 _69896 h1)). Qed.
Lemma lem5403749 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term284 _69895 _69896.
Proof. exact (proj2 (@lem5403747 _69895 _69896 h1)). Qed.
Lemma lem5403751 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term237 _69896.
Proof. exact (proj2 (@lem5403749 _69895 _69896 h1)). Qed.
Lemma lem5403752 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term257 _69895 _69896.
Proof. exact (proj1 (@lem5403749 _69895 _69896 h1)). Qed.
Lemma lem5403753 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term255 _69896.
Proof. exact (proj2 (@lem5403752 _69895 _69896 h1)). Qed.
Lemma lem5403756 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5403757 : term319 = term320.
Proof. exact (@lem5403756 term118 term132). Qed.
Lemma lem5403759 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403760 : term132 = term214.
Proof. exact (@lem5403759 term133). Qed.
Lemma lem5403762 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403763 : term118 = term184.
Proof. exact (@lem5403762 (NUMERAL 0)). Qed.
Lemma lem5403764 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5403765 : term321 = term322.
Proof. exact (MK_COMB (@lem5403764) (@lem5403763)). Qed.
Lemma lem5403766 : term320 = term323.
Proof. exact (MK_COMB (@lem5403765) (@lem5403760)). Qed.
Lemma lem5403767 : term324.
Proof. exact (@lem1980255 term118 term132 term132 term132). Qed.
Lemma lem5403769 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403770 : term320 = term326.
Proof. exact (@lem5403769 (NUMERAL 0) term133). Qed.
Lemma lem5403771 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403772 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403773 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403772 h1) (fun h1 : term326 = True => @lem5403771)). Qed.
Lemma lem5403774 : term326 = True.
Proof. exact (EQ_MP (@lem5403773) (@lem5403771)). Qed.
Lemma lem5403775 : term320 = True.
Proof. exact (TRANS (@lem5403770) (@lem5403774)). Qed.
Lemma lem5403776 : True = term320.
Proof. exact (SYM (@lem5403775)). Qed.
Lemma lem5403777 : term320.
Proof. exact (EQ_MP (@lem5403776) (@lem0)). Qed.
Lemma lem5403778 : term328.
Proof. exact (@lem5403767 (@lem5403777)). Qed.
Lemma lem5403780 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403781 : term320 = term326.
Proof. exact (@lem5403780 (NUMERAL 0) term133). Qed.
Lemma lem5403782 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403783 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403784 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403783 h1) (fun h1 : term326 = True => @lem5403782)). Qed.
Lemma lem5403785 : term326 = True.
Proof. exact (EQ_MP (@lem5403784) (@lem5403782)). Qed.
Lemma lem5403786 : term320 = True.
Proof. exact (TRANS (@lem5403781) (@lem5403785)). Qed.
Lemma lem5403787 : True = term320.
Proof. exact (SYM (@lem5403786)). Qed.
Lemma lem5403788 : term320.
Proof. exact (EQ_MP (@lem5403787) (@lem0)). Qed.
Lemma lem5403789 : term323 = term329.
Proof. exact (@lem5403778 (@lem5403788)). Qed.
Lemma lem5403791 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403792 : term196 = term197.
Proof. exact (@lem5403791 term133 term133). Qed.
Lemma lem5403793 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403794 : term199 = term133.
Proof. exact (EQ_MP (@lem5403793) (@lem940073)). Qed.
Lemma lem5403795 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403796 : term197 = term132.
Proof. exact (MK_COMB (@lem5403795) (@lem5403794)). Qed.
Lemma lem5403797 : term196 = term132.
Proof. exact (TRANS (@lem5403792) (@lem5403796)). Qed.
Lemma lem5403799 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403800 : term331 = term118.
Proof. exact (@lem5403799 term133). Qed.
Lemma lem5403801 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5403802 : term332 = term321.
Proof. exact (MK_COMB (@lem5403801) (@lem5403800)). Qed.
Lemma lem5403803 : term329 = term320.
Proof. exact (MK_COMB (@lem5403802) (@lem5403797)). Qed.
Lemma lem5403805 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403806 : term320 = term326.
Proof. exact (@lem5403805 (NUMERAL 0) term133). Qed.
Lemma lem5403807 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403808 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403809 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403808 h1) (fun h1 : term326 = True => @lem5403807)). Qed.
Lemma lem5403810 : term326 = True.
Proof. exact (EQ_MP (@lem5403809) (@lem5403807)). Qed.
Lemma lem5403811 : term320 = True.
Proof. exact (TRANS (@lem5403806) (@lem5403810)). Qed.
Lemma lem5403812 : term329 = True.
Proof. exact (TRANS (@lem5403803) (@lem5403811)). Qed.
Lemma lem5403813 : term323 = True.
Proof. exact (TRANS (@lem5403789) (@lem5403812)). Qed.
Lemma lem5403814 : term320 = True.
Proof. exact (TRANS (@lem5403766) (@lem5403813)). Qed.
Lemma lem5403815 : term319 = True.
Proof. exact (TRANS (@lem5403757) (@lem5403814)). Qed.
Lemma lem5403816 : True = term319.
Proof. exact (SYM (@lem5403815)). Qed.
Lemma lem5403817 : term319.
Proof. exact (EQ_MP (@lem5403816) (@lem0)). Qed.
Lemma lem5403818 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term375 _69896.
Proof. exact (conj (@lem5403817) (@lem5403751 _69895 _69896 h1)). Qed.
Lemma lem5403820 (x : real) (y : real) : term334 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5403821 (_69896 : int) : term376 _69896.
Proof. exact (@lem5403820 term132 (term234 _69896)). Qed.
Lemma lem5403822 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term377 _69896.
Proof. exact (@lem5403821 _69896 (@lem5403818 _69895 _69896 h1)). Qed.
Lemma lem5403823 (_69896 : int) : (term378 _69896) = (term234 _69896).
Proof. exact (@lem1982733 (term234 _69896)). Qed.
Lemma lem5403824 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5403825 (_69896 : int) : (term379 _69896) = (term236 _69896).
Proof. exact (MK_COMB (@lem5403824) (@lem5403823 _69896)). Qed.
Lemma lem5403826 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5403827 (_69896 : int) : (term377 _69896) = (term237 _69896).
Proof. exact (MK_COMB (@lem5403825 _69896) (@lem5403826)). Qed.
Lemma lem5403828 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term237 _69896.
Proof. exact (EQ_MP (@lem5403827 _69896) (@lem5403822 _69895 _69896 h1)). Qed.
Lemma lem5403830 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5403831 : term319 = term320.
Proof. exact (@lem5403830 term118 term132). Qed.
Lemma lem5403833 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403834 : term132 = term214.
Proof. exact (@lem5403833 term133). Qed.
Lemma lem5403836 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403837 : term118 = term184.
Proof. exact (@lem5403836 (NUMERAL 0)). Qed.
Lemma lem5403838 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5403839 : term321 = term322.
Proof. exact (MK_COMB (@lem5403838) (@lem5403837)). Qed.
Lemma lem5403840 : term320 = term323.
Proof. exact (MK_COMB (@lem5403839) (@lem5403834)). Qed.
Lemma lem5403841 : term324.
Proof. exact (@lem1980255 term118 term132 term132 term132). Qed.
Lemma lem5403843 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403844 : term320 = term326.
Proof. exact (@lem5403843 (NUMERAL 0) term133). Qed.
Lemma lem5403845 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403846 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403847 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403846 h1) (fun h1 : term326 = True => @lem5403845)). Qed.
Lemma lem5403848 : term326 = True.
Proof. exact (EQ_MP (@lem5403847) (@lem5403845)). Qed.
Lemma lem5403849 : term320 = True.
Proof. exact (TRANS (@lem5403844) (@lem5403848)). Qed.
Lemma lem5403850 : True = term320.
Proof. exact (SYM (@lem5403849)). Qed.
Lemma lem5403851 : term320.
Proof. exact (EQ_MP (@lem5403850) (@lem0)). Qed.
Lemma lem5403852 : term328.
Proof. exact (@lem5403841 (@lem5403851)). Qed.
Lemma lem5403854 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403855 : term320 = term326.
Proof. exact (@lem5403854 (NUMERAL 0) term133). Qed.
Lemma lem5403856 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403857 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403858 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403857 h1) (fun h1 : term326 = True => @lem5403856)). Qed.
Lemma lem5403859 : term326 = True.
Proof. exact (EQ_MP (@lem5403858) (@lem5403856)). Qed.
Lemma lem5403860 : term320 = True.
Proof. exact (TRANS (@lem5403855) (@lem5403859)). Qed.
Lemma lem5403861 : True = term320.
Proof. exact (SYM (@lem5403860)). Qed.
Lemma lem5403862 : term320.
Proof. exact (EQ_MP (@lem5403861) (@lem0)). Qed.
Lemma lem5403863 : term323 = term329.
Proof. exact (@lem5403852 (@lem5403862)). Qed.
Lemma lem5403865 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403866 : term196 = term197.
Proof. exact (@lem5403865 term133 term133). Qed.
Lemma lem5403867 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403868 : term199 = term133.
Proof. exact (EQ_MP (@lem5403867) (@lem940073)). Qed.
Lemma lem5403869 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403870 : term197 = term132.
Proof. exact (MK_COMB (@lem5403869) (@lem5403868)). Qed.
Lemma lem5403871 : term196 = term132.
Proof. exact (TRANS (@lem5403866) (@lem5403870)). Qed.
Lemma lem5403873 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403874 : term331 = term118.
Proof. exact (@lem5403873 term133). Qed.
Lemma lem5403875 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5403876 : term332 = term321.
Proof. exact (MK_COMB (@lem5403875) (@lem5403874)). Qed.
Lemma lem5403877 : term329 = term320.
Proof. exact (MK_COMB (@lem5403876) (@lem5403871)). Qed.
Lemma lem5403879 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403880 : term320 = term326.
Proof. exact (@lem5403879 (NUMERAL 0) term133). Qed.
Lemma lem5403881 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403882 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403883 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403882 h1) (fun h1 : term326 = True => @lem5403881)). Qed.
Lemma lem5403884 : term326 = True.
Proof. exact (EQ_MP (@lem5403883) (@lem5403881)). Qed.
Lemma lem5403885 : term320 = True.
Proof. exact (TRANS (@lem5403880) (@lem5403884)). Qed.
Lemma lem5403886 : term329 = True.
Proof. exact (TRANS (@lem5403877) (@lem5403885)). Qed.
Lemma lem5403887 : term323 = True.
Proof. exact (TRANS (@lem5403863) (@lem5403886)). Qed.
Lemma lem5403888 : term320 = True.
Proof. exact (TRANS (@lem5403840) (@lem5403887)). Qed.
Lemma lem5403889 : term319 = True.
Proof. exact (TRANS (@lem5403831) (@lem5403888)). Qed.
Lemma lem5403890 : True = term319.
Proof. exact (SYM (@lem5403889)). Qed.
Lemma lem5403891 : term319.
Proof. exact (EQ_MP (@lem5403890) (@lem0)). Qed.
Lemma lem5403892 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term432 _69896.
Proof. exact (conj (@lem5403891) (@lem5403753 _69895 _69896 h1)). Qed.
Lemma lem5403894 (x : real) (y : real) : term334 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5403895 (_69896 : int) : term433 _69896.
Proof. exact (@lem5403894 term132 (term246 _69896)). Qed.
Lemma lem5403896 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term434 _69896.
Proof. exact (@lem5403895 _69896 (@lem5403892 _69895 _69896 h1)). Qed.
Lemma lem5403897 (_69896 : int) : (term435 _69896) = (term246 _69896).
Proof. exact (@lem1982733 (term246 _69896)). Qed.
Lemma lem5403898 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5403899 (_69896 : int) : (term436 _69896) = (term254 _69896).
Proof. exact (MK_COMB (@lem5403898) (@lem5403897 _69896)). Qed.
Lemma lem5403900 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5403901 (_69896 : int) : (term434 _69896) = (term255 _69896).
Proof. exact (MK_COMB (@lem5403899 _69896) (@lem5403900)). Qed.
Lemma lem5403902 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term255 _69896.
Proof. exact (EQ_MP (@lem5403901 _69896) (@lem5403896 _69895 _69896 h1)). Qed.
Lemma lem5403903 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term437 _69896.
Proof. exact (conj (@lem5403902 _69895 _69896 h1) (@lem5403828 _69895 _69896 h1)). Qed.
Lemma lem5403905 (x : real) (y : real) : term426 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5403906 (_69896 : int) : term438 _69896.
Proof. exact (@lem5403905 (term246 _69896) (term234 _69896)). Qed.
Lemma lem5403907 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term383 _69896.
Proof. exact (@lem5403906 _69896 (@lem5403903 _69895 _69896 h1)). Qed.
Lemma lem5403908 (_69896 : int) : (term384 _69896) = (term385 _69896).
Proof. exact (@lem1982763 (term246 _69896) (real_of_int _69896) term187). Qed.
Lemma lem5403909 (_69896 : int) : (term386 _69896) = (term354 _69896).
Proof. exact (@lem1982713 term187 (real_of_int _69896)). Qed.
Lemma lem5403911 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5403912 : term132 = term214.
Proof. exact (@lem5403911 term133). Qed.
Lemma lem5403914 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5403915 : term187 = term188.
Proof. exact (@lem5403914 term133). Qed.
Lemma lem5403916 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5403917 : term355 = term356.
Proof. exact (MK_COMB (@lem5403916) (@lem5403915)). Qed.
Lemma lem5403918 : term357 = term358.
Proof. exact (MK_COMB (@lem5403917) (@lem5403912)). Qed.
Lemma lem5403919 : term359.
Proof. exact (@lem1981473 term187 term132 term132 term132 term118 term132). Qed.
Lemma lem5403921 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403922 : term320 = term326.
Proof. exact (@lem5403921 (NUMERAL 0) term133). Qed.
Lemma lem5403923 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403924 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403925 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403924 h1) (fun h1 : term326 = True => @lem5403923)). Qed.
Lemma lem5403926 : term326 = True.
Proof. exact (EQ_MP (@lem5403925) (@lem5403923)). Qed.
Lemma lem5403927 : term320 = True.
Proof. exact (TRANS (@lem5403922) (@lem5403926)). Qed.
Lemma lem5403928 : True = term320.
Proof. exact (SYM (@lem5403927)). Qed.
Lemma lem5403929 : term320.
Proof. exact (EQ_MP (@lem5403928) (@lem0)). Qed.
Lemma lem5403930 : term360.
Proof. exact (@lem5403919 (@lem5403929)). Qed.
Lemma lem5403932 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403933 : term320 = term326.
Proof. exact (@lem5403932 (NUMERAL 0) term133). Qed.
Lemma lem5403934 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403935 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403936 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403935 h1) (fun h1 : term326 = True => @lem5403934)). Qed.
Lemma lem5403937 : term326 = True.
Proof. exact (EQ_MP (@lem5403936) (@lem5403934)). Qed.
Lemma lem5403938 : term320 = True.
Proof. exact (TRANS (@lem5403933) (@lem5403937)). Qed.
Lemma lem5403939 : True = term320.
Proof. exact (SYM (@lem5403938)). Qed.
Lemma lem5403940 : term320.
Proof. exact (EQ_MP (@lem5403939) (@lem0)). Qed.
Lemma lem5403941 : term361.
Proof. exact (@lem5403930 (@lem5403940)). Qed.
Lemma lem5403943 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5403944 : term320 = term326.
Proof. exact (@lem5403943 (NUMERAL 0) term133). Qed.
Lemma lem5403945 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5403946 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5403947 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5403946 h1) (fun h1 : term326 = True => @lem5403945)). Qed.
Lemma lem5403948 : term326 = True.
Proof. exact (EQ_MP (@lem5403947) (@lem5403945)). Qed.
Lemma lem5403949 : term320 = True.
Proof. exact (TRANS (@lem5403944) (@lem5403948)). Qed.
Lemma lem5403950 : True = term320.
Proof. exact (SYM (@lem5403949)). Qed.
Lemma lem5403951 : term320.
Proof. exact (EQ_MP (@lem5403950) (@lem0)). Qed.
Lemma lem5403952 : term362.
Proof. exact (@lem5403941 (@lem5403951)). Qed.
Lemma lem5403954 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403955 : term196 = term197.
Proof. exact (@lem5403954 term133 term133). Qed.
Lemma lem5403956 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403957 : term199 = term133.
Proof. exact (EQ_MP (@lem5403956) (@lem940073)). Qed.
Lemma lem5403958 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403959 : term197 = term132.
Proof. exact (MK_COMB (@lem5403958) (@lem5403957)). Qed.
Lemma lem5403960 : term196 = term132.
Proof. exact (TRANS (@lem5403955) (@lem5403959)). Qed.
Lemma lem5403962 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5403963 : term215 = term220.
Proof. exact (@lem5403962 term133 term133). Qed.
Lemma lem5403964 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403965 : term199 = term133.
Proof. exact (EQ_MP (@lem5403964) (@lem940073)). Qed.
Lemma lem5403966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403967 : term197 = term132.
Proof. exact (MK_COMB (@lem5403966) (@lem5403965)). Qed.
Lemma lem5403968 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5403969 : term220 = term187.
Proof. exact (MK_COMB (@lem5403968) (@lem5403967)). Qed.
Lemma lem5403970 : term215 = term187.
Proof. exact (TRANS (@lem5403963) (@lem5403969)). Qed.
Lemma lem5403971 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5403972 : term363 = term355.
Proof. exact (MK_COMB (@lem5403971) (@lem5403970)). Qed.
Lemma lem5403973 : term364 = term357.
Proof. exact (MK_COMB (@lem5403972) (@lem5403960)). Qed.
Lemma lem5403975 (m : nat) : (term365 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5403976 : term357 = term118.
Proof. exact (@lem5403975 term133). Qed.
Lemma lem5403977 : term364 = term118.
Proof. exact (TRANS (@lem5403973) (@lem5403976)). Qed.
Lemma lem5403978 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5403979 : term366 = term367.
Proof. exact (MK_COMB (@lem5403978) (@lem5403977)). Qed.
Lemma lem5403980 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem5403981 : term368 = term331.
Proof. exact (MK_COMB (@lem5403979) (@lem5403980)). Qed.
Lemma lem5403983 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403984 : term331 = term118.
Proof. exact (@lem5403983 term133). Qed.
Lemma lem5403985 : term368 = term118.
Proof. exact (TRANS (@lem5403981) (@lem5403984)). Qed.
Lemma lem5403987 (m : nat) (n : nat) : (term194 m n) = (term195 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5403988 : term196 = term197.
Proof. exact (@lem5403987 term133 term133). Qed.
Lemma lem5403989 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5403990 : term199 = term133.
Proof. exact (EQ_MP (@lem5403989) (@lem940073)). Qed.
Lemma lem5403991 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5403992 : term197 = term132.
Proof. exact (MK_COMB (@lem5403991) (@lem5403990)). Qed.
Lemma lem5403993 : term196 = term132.
Proof. exact (TRANS (@lem5403988) (@lem5403992)). Qed.
Lemma lem5403994 : term367 = term367.
Proof. exact (eq_refl term367). Qed.
Lemma lem5403995 : term369 = term331.
Proof. exact (MK_COMB (@lem5403994) (@lem5403993)). Qed.
Lemma lem5403997 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5403998 : term331 = term118.
Proof. exact (@lem5403997 term133). Qed.
Lemma lem5403999 : term369 = term118.
Proof. exact (TRANS (@lem5403995) (@lem5403998)). Qed.
Lemma lem5404000 : term118 = term369.
Proof. exact (SYM (@lem5403999)). Qed.
Lemma lem5404001 : term368 = term369.
Proof. exact (TRANS (@lem5403985) (@lem5404000)). Qed.
Lemma lem5404002 : term358 = term184.
Proof. exact (@lem5403952 (@lem5404001)). Qed.
Lemma lem5404003 : term357 = term184.
Proof. exact (TRANS (@lem5403918) (@lem5404002)). Qed.
Lemma lem5404005 (x : real) : (term203 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5404006 : term184 = term118.
Proof. exact (@lem5404005 term118). Qed.
Lemma lem5404007 : term357 = term118.
Proof. exact (TRANS (@lem5404003) (@lem5404006)). Qed.
Lemma lem5404008 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5404009 : term370 = term367.
Proof. exact (MK_COMB (@lem5404008) (@lem5404007)). Qed.
Lemma lem5404010 (_69896 : int) : (real_of_int _69896) = (real_of_int _69896).
Proof. exact (eq_refl (real_of_int _69896)). Qed.
Lemma lem5404011 (_69896 : int) : (term354 _69896) = (term371 _69896).
Proof. exact (MK_COMB (@lem5404009) (@lem5404010 _69896)). Qed.
Lemma lem5404012 (_69896 : int) : (term386 _69896) = (term371 _69896).
Proof. exact (TRANS (@lem5403909 _69896) (@lem5404011 _69896)). Qed.
Lemma lem5404013 (_69896 : int) : (term371 _69896) = term118.
Proof. exact (@lem1982719 (real_of_int _69896)). Qed.
Lemma lem5404014 (_69896 : int) : (term386 _69896) = term118.
Proof. exact (TRANS (@lem5404012 _69896) (@lem5404013 _69896)). Qed.
Lemma lem5404015 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5404016 (_69896 : int) : (term387 _69896) = term145.
Proof. exact (MK_COMB (@lem5404015) (@lem5404014 _69896)). Qed.
Lemma lem5404017 : term187 = term187.
Proof. exact (eq_refl term187). Qed.
Lemma lem5404018 (_69896 : int) : (term385 _69896) = term373.
Proof. exact (MK_COMB (@lem5404016 _69896) (@lem5404017)). Qed.
Lemma lem5404019 (_69896 : int) : (term384 _69896) = term373.
Proof. exact (TRANS (@lem5403908 _69896) (@lem5404018 _69896)). Qed.
Lemma lem5404020 : term373 = term187.
Proof. exact (@lem1982721 term187). Qed.
Lemma lem5404021 (_69896 : int) : (term384 _69896) = term187.
Proof. exact (TRANS (@lem5404019 _69896) (@lem5404020)). Qed.
Lemma lem5404022 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5404023 (_69896 : int) : (term388 _69896) = term389.
Proof. exact (MK_COMB (@lem5404022) (@lem5404021 _69896)). Qed.
Lemma lem5404024 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5404025 (_69896 : int) : (term383 _69896) = term390.
Proof. exact (MK_COMB (@lem5404023 _69896) (@lem5404024)). Qed.
Lemma lem5404026 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : term390.
Proof. exact (EQ_MP (@lem5404025 _69896) (@lem5403907 _69895 _69896 h1)). Qed.
Lemma lem5404028 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5404029 : term390 = term391.
Proof. exact (@lem5404028 term118 term187). Qed.
Lemma lem5404031 (x : nat) : (term185 x) = (term186 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5404032 : term187 = term188.
Proof. exact (@lem5404031 term133). Qed.
Lemma lem5404034 (x : nat) : (real_of_num x) = (term183 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5404035 : term118 = term184.
Proof. exact (@lem5404034 (NUMERAL 0)). Qed.
Lemma lem5404036 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5404037 : term120 = term392.
Proof. exact (MK_COMB (@lem5404036) (@lem5404035)). Qed.
Lemma lem5404038 : term391 = term393.
Proof. exact (MK_COMB (@lem5404037) (@lem5404032)). Qed.
Lemma lem5404039 : term394.
Proof. exact (@lem1980026 term118 term132 term187 term132). Qed.
Lemma lem5404041 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5404042 : term320 = term326.
Proof. exact (@lem5404041 (NUMERAL 0) term133). Qed.
Lemma lem5404043 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5404044 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5404045 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5404044 h1) (fun h1 : term326 = True => @lem5404043)). Qed.
Lemma lem5404046 : term326 = True.
Proof. exact (EQ_MP (@lem5404045) (@lem5404043)). Qed.
Lemma lem5404047 : term320 = True.
Proof. exact (TRANS (@lem5404042) (@lem5404046)). Qed.
Lemma lem5404048 : True = term320.
Proof. exact (SYM (@lem5404047)). Qed.
Lemma lem5404049 : term320.
Proof. exact (EQ_MP (@lem5404048) (@lem0)). Qed.
Lemma lem5404050 : term395.
Proof. exact (@lem5404039 (@lem5404049)). Qed.
Lemma lem5404052 (m : nat) (n : nat) : (term325 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5404053 : term320 = term326.
Proof. exact (@lem5404052 (NUMERAL 0) term133). Qed.
Lemma lem5404054 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5404055 (h1 : term327 = (BIT1 0)) : term326 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5404056 : (term327 = (BIT1 0)) = (term326 = True).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5404055 h1) (fun h1 : term326 = True => @lem5404054)). Qed.
Lemma lem5404057 : term326 = True.
Proof. exact (EQ_MP (@lem5404056) (@lem5404054)). Qed.
Lemma lem5404058 : term320 = True.
Proof. exact (TRANS (@lem5404053) (@lem5404057)). Qed.
Lemma lem5404059 : True = term320.
Proof. exact (SYM (@lem5404058)). Qed.
Lemma lem5404060 : term320.
Proof. exact (EQ_MP (@lem5404059) (@lem0)). Qed.
Lemma lem5404061 : term393 = term396.
Proof. exact (@lem5404050 (@lem5404060)). Qed.
Lemma lem5404063 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5404064 : term215 = term220.
Proof. exact (@lem5404063 term133 term133). Qed.
Lemma lem5404065 : (term198 = (BIT1 0)) = (term199 = term133).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5404066 : term199 = term133.
Proof. exact (EQ_MP (@lem5404065) (@lem940073)). Qed.
Lemma lem5404067 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5404068 : term197 = term132.
Proof. exact (MK_COMB (@lem5404067) (@lem5404066)). Qed.
Lemma lem5404069 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5404070 : term220 = term187.
Proof. exact (MK_COMB (@lem5404069) (@lem5404068)). Qed.
Lemma lem5404071 : term215 = term187.
Proof. exact (TRANS (@lem5404064) (@lem5404070)). Qed.
Lemma lem5404073 (x : nat) : (term330 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5404074 : term331 = term118.
Proof. exact (@lem5404073 term133). Qed.
Lemma lem5404075 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5404076 : term397 = term120.
Proof. exact (MK_COMB (@lem5404075) (@lem5404074)). Qed.
Lemma lem5404077 : term396 = term391.
Proof. exact (MK_COMB (@lem5404076) (@lem5404071)). Qed.
Lemma lem5404079 (m : nat) (n : nat) : (term398 m n) = (term399 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5404080 : term391 = term400.
Proof. exact (@lem5404079 (NUMERAL 0) term133). Qed.
Lemma lem5404081 : term327 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5404082 (h1 : term327 = (BIT1 0)) : (term133 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5404083 : (term327 = (BIT1 0)) = ((term133 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term327 = (BIT1 0) => @lem5404082 h1) (fun h1 : (term133 = (NUMERAL 0)) = False => @lem5404081)). Qed.
Lemma lem5404084 : (term133 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5404083) (@lem5404081)). Qed.
Lemma lem5404085 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5404086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5404087 : term401 = (and True).
Proof. exact (MK_COMB (@lem5404086) (@lem5404085)). Qed.
Lemma lem5404088 : term400 = (True /\ False).
Proof. exact (MK_COMB (@lem5404087) (@lem5404084)). Qed.
Lemma lem5404090 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5404091 : term400 = False.
Proof. exact (TRANS (@lem5404088) (@lem5404090)). Qed.
Lemma lem5404092 : term391 = False.
Proof. exact (TRANS (@lem5404080) (@lem5404091)). Qed.
Lemma lem5404093 : term396 = False.
Proof. exact (TRANS (@lem5404077) (@lem5404092)). Qed.
Lemma lem5404094 : term393 = False.
Proof. exact (TRANS (@lem5404061) (@lem5404093)). Qed.
Lemma lem5404095 : term391 = False.
Proof. exact (TRANS (@lem5404038) (@lem5404094)). Qed.
Lemma lem5404096 : term390 = False.
Proof. exact (TRANS (@lem5404029) (@lem5404095)). Qed.
Lemma lem5404097 (_69895 : int) (_69896 : int) (h1 : term431 _69895 _69896) : False.
Proof. exact (EQ_MP (@lem5404096) (@lem5404026 _69895 _69896 h1)). Qed.
Lemma lem5404098 (_69895 : int) (_69896 : int) (h1 : term308 _69895 _69896) : False.
Proof. exact (or_elim (@lem5403178 _69895 _69896 h1) (fun h0 : term403 _69895 _69896 => @lem5403743 _69895 _69896 h0) (fun h0 : term431 _69895 _69896 => @lem5404097 _69895 _69896 h0)). Qed.
Lemma lem5404099 (_69895 : int) (_69896 : int) (h1 : term317 _69895 _69896) : False.
Proof. exact (or_elim (@lem5402378 _69895 _69896 h1) (fun h0 : term312 _69895 _69896 => @lem5403177 _69895 _69896 h0) (fun h0 : term308 _69895 _69896 => @lem5404098 _69895 _69896 h0)). Qed.
Lemma lem5404101 (_69895 : int) (_69896 : int) (h1 : term317 _69895 _69896) : term317 _69895 _69896.
Proof. exact (h1). Qed.
Lemma lem5404102 (_69895 : int) (_69896 : int) (h1 : term317 _69895 _69896) : (term317 _69895 _69896) = False.
Proof. exact (prop_ext (fun h2 : term317 _69895 _69896 => @lem5404099 _69895 _69896 h1) (fun h2 : False => @lem5404101 _69895 _69896 h1)). Qed.
Lemma lem5404103 (_69895 : int) (_69896 : int) (h1 : term317 _69895 _69896) : False.
Proof. exact (EQ_MP (@lem5404102 _69895 _69896 h1) (@lem5404101 _69895 _69896 h1)). Qed.
Lemma lem5404104 (_69895 : int) (_69896 : int) (h1 : term179 _69895 _69896) : term179 _69895 _69896.
Proof. exact (h1). Qed.
Lemma lem5404105 (_69895 : int) (_69896 : int) (h1 : term179 _69895 _69896) : term317 _69895 _69896.
Proof. exact (EQ_MP (@lem5402356 _69895 _69896) (@lem5404104 _69895 _69896 h1)). Qed.
Lemma lem5404106 (_69895 : int) (_69896 : int) (h1 : term179 _69895 _69896) : (term317 _69895 _69896) = False.
Proof. exact (prop_ext (fun h2 : term317 _69895 _69896 => @lem5404103 _69895 _69896 h2) (fun h2 : False => @lem5404105 _69895 _69896 h1)). Qed.
Lemma lem5404107 (_69895 : int) (_69896 : int) (h1 : term179 _69895 _69896) : False.
Proof. exact (EQ_MP (@lem5404106 _69895 _69896 h1) (@lem5404105 _69895 _69896 h1)). Qed.
Lemma lem5404108 (_69895 : int) (_69896 : int) : term439 _69895 _69896.
Proof. exact (fun h0 : term179 _69895 _69896 => @lem5404107 _69895 _69896 h0). Qed.
Lemma lem5404109 (_69895 : int) (_69896 : int) : term440 _69895 _69896.
Proof. exact (@lem1386578 (term441 _69895 _69896)). Qed.
Lemma lem5404112 (_69895 : int) (_69896 : int) : term441 _69895 _69896.
Proof. exact (@lem5404109 _69895 _69896 (@lem5404108 _69895 _69896)). Qed.
Lemma lem5404113 (_69895 : int) (_69896 : int) : (term177 _69895 _69896) = (term112 _69895 _69896).
Proof. exact (SYM (@lem5401620 _69895 _69896)). Qed.
Lemma lem5404114 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5404115 (_69895 : int) (_69896 : int) : (term441 _69895 _69896) = (term65 _69895 _69896).
Proof. exact (MK_COMB (@lem5404114) (@lem5404113 _69895 _69896)). Qed.
Lemma lem5404116 (_69895 : int) (_69896 : int) : term65 _69895 _69896.
Proof. exact (EQ_MP (@lem5404115 _69895 _69896) (@lem5404112 _69895 _69896)). Qed.
Lemma lem5404117 (_69895 : int) (_69896 : int) : term66 _69895 _69896.
Proof. exact (EQ_MP (@lem5401315 _69895 _69896) (@lem5404116 _69895 _69896)). Qed.
Lemma lem5404118 (m : nat) (x : nat) : term442 m x.
Proof. exact (@lem5404117 (int_of_num m) (int_of_num x)). Qed.
Lemma lem5404119 (m : nat) (x : nat) : term443 m x.
Proof. exact (@lem5404118 m x (@lem5401311 m)). Qed.
Lemma lem5404120 (m : nat) (x : nat) : term60 m x.
Proof. exact (@lem5404119 m x (@lem5401314 x)). Qed.
Lemma lem5404121 (m : nat) : term62 m.
Proof. exact (fun x : nat => @lem5404120 m x). Qed.
Lemma lem5404122 (m : nat) : (term62 m) = (term4 m).
Proof. exact (SYM (@lem5401308 m)). Qed.
Lemma lem5404123 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem5404122 m) (@lem5404121 m)). Qed.
Lemma lem5404124 (m : nat) : (term4 m) = ((term4 m) = True).
Proof. exact (@lem7 (term4 m)). Qed.
Lemma lem5404125 (m : nat) : (term4 m) = True.
Proof. exact (EQ_MP (@lem5404124 m) (@lem5404123 m)). Qed.
Lemma lem5404126 (m : nat) : True = (term4 m).
Proof. exact (SYM (@lem5404125 m)). Qed.
Lemma lem5404127 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem5404126 m) (@lem0)). Qed.
