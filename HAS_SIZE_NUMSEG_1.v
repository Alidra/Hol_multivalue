Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_NUMSEG_1_term_abbrevs.
Require Import CARD_NUMSEG_spec.
Require Import FINITE_NUMSEG_spec.
Require Import HAS_SIZE_spec.
Require Import INT_POS_spec.
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
Require Import thm1367770_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm1842_spec.
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
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
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
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem5397153 (m : nat) : term0 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem5397154 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem5397155 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem5397154 m) (@lem5397153 m)). Qed.
Lemma lem5397156 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem5397155 m n). Qed.
Lemma lem5397157 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem5397158 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem5397157 m n) (@lem5397156 m n)). Qed.
Lemma lem5397159 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem5397161 {_100044 : Type'} (s : _100044 -> Prop) : term4 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem5397162 {_100044 : Type'} (s : _100044 -> Prop) : (term4 _100044 s) = (term5 _100044 s).
Proof. exact (eq_refl (term4 _100044 s)). Qed.
Lemma lem5397163 {_100044 : Type'} (s : _100044 -> Prop) : term5 _100044 s.
Proof. exact (EQ_MP (@lem5397162 _100044 s) (@lem5397161 _100044 s)). Qed.
Lemma lem5397164 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term6 _100044 s n.
Proof. exact (@lem5397163 _100044 s n). Qed.
Lemma lem5397165 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term6 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term7 _100044 s n)).
Proof. exact (eq_refl (term6 _100044 s n)). Qed.
Lemma lem5397167 (m : nat) : term8 m.
Proof. exact (@lem5393502 m). Qed.
Lemma lem5397168 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem5397169 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem5397168 m) (@lem5397167 m)). Qed.
Lemma lem5397170 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem5397169 m n). Qed.
Lemma lem5397171 (n : nat) (m : nat) : (term10 m n) = ((term11 m n) = (term12 n m)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem5397178 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term7 _100044 s n).
Proof. exact (EQ_MP (@lem5397165 _100044 s n) (@lem5397164 _100044 s n)). Qed.
Lemma lem5397179 (s : nat -> Prop) (n : nat) : (@HAS_SIZE nat s n) = (term13 s n).
Proof. exact (@lem5397178 nat s n). Qed.
Lemma lem5397180 (n : nat) : (term14 n) = (term15 n).
Proof. exact (@lem5397179 (term16 n) n). Qed.
Lemma lem5397184 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem5397159 m n) (@lem5397158 m n)). Qed.
Lemma lem5397185 (n : nat) : (term17 n) = True.
Proof. exact (@lem5397184 term18 n). Qed.
Lemma lem5397186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5397187 (n : nat) : (term19 n) = (and True).
Proof. exact (MK_COMB (@lem5397186) (@lem5397185 n)). Qed.
Lemma lem5397191 (n : nat) (m : nat) : (term11 m n) = (term12 n m).
Proof. exact (EQ_MP (@lem5397171 n m) (@lem5397170 m n)). Qed.
Lemma lem5397192 (n : nat) : (term20 n) = (term21 n).
Proof. exact (@lem5397191 n term18). Qed.
Lemma lem5397193 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem5397194 (n : nat) : (term22 n) = (term23 n).
Proof. exact (MK_COMB (@lem5397193) (@lem5397192 n)). Qed.
Lemma lem5397195 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem5397196 (n : nat) : ((term20 n) = n) = ((term21 n) = n).
Proof. exact (MK_COMB (@lem5397194 n) (@lem5397195 n)). Qed.
Lemma lem5397199 (n : nat) : (term15 n) = (term24 n).
Proof. exact (MK_COMB (@lem5397187 n) (@lem5397196 n)). Qed.
Lemma lem5397201 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5397202 (n : nat) : (term24 n) = ((term21 n) = n).
Proof. exact (@lem5397201 ((term21 n) = n)). Qed.
Lemma lem5397205 (n : nat) : (term15 n) = ((term21 n) = n).
Proof. exact (TRANS (@lem5397199 n) (@lem5397202 n)). Qed.
Lemma lem5397206 (n : nat) : (term14 n) = ((term21 n) = n).
Proof. exact (TRANS (@lem5397180 n) (@lem5397205 n)). Qed.
Lemma lem5397207 : term25 = term26.
Proof. exact (fun_ext (fun n : nat => @lem5397206 n)). Qed.
Lemma lem5397208 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5397209 : term27 = term28.
Proof. exact (MK_COMB (@lem5397208) (@lem5397207)). Qed.
Lemma lem5397214 : term28 = term27.
Proof. exact (SYM (@lem5397209)). Qed.
Lemma lem5397222 (n : nat) : ((term21 n) = n) = ((term21 n) = n).
Proof. exact (eq_refl ((term21 n) = n)). Qed.
Lemma lem5397223 : term26 = term26.
Proof. exact (fun_ext (fun n : nat => @lem5397222 n)). Qed.
Lemma lem5397224 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5397226 : term28 = term28.
Proof. exact (MK_COMB (@lem5397224) (@lem5397223)). Qed.
Lemma lem5397227 (n : nat) : ((term21 n) = n) = ((term21 n) = n).
Proof. exact (eq_refl ((term21 n) = n)). Qed.
Lemma lem5397228 : term26 = term26.
Proof. exact (fun_ext (fun n : nat => @lem5397227 n)). Qed.
Lemma lem5397229 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5397230 : term28 = term28.
Proof. exact (MK_COMB (@lem5397229) (@lem5397228)). Qed.
Lemma lem5397231 : term28 = term28.
Proof. exact (TRANS (@lem5397226) (@lem5397230)). Qed.
Lemma lem5397232 (n : nat) : (term29 n) = (term30 n).
Proof. exact (@lem1032781 (term31 n) term18 (term32 n)). Qed.
Lemma lem5397233 (d : nat) (n : nat) : (term33 n d) = (d = n).
Proof. exact (eq_refl (term33 n d)). Qed.
Lemma lem5397234 (n : nat) (d : nat) : (term34 n d) = (term34 n d).
Proof. exact (eq_refl (term34 n d)). Qed.
Lemma lem5397235 (d : nat) (n : nat) : (term35 n d) = (term36 d n).
Proof. exact (MK_COMB (@lem5397234 n d) (@lem5397233 d n)). Qed.
Lemma lem5397236 (n : nat) : (term37 n) = (term38 n).
Proof. exact (fun_ext (fun d : nat => @lem5397235 d n)). Qed.
Lemma lem5397237 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5397238 (n : nat) : (term30 n) = (term39 n).
Proof. exact (MK_COMB (@lem5397237) (@lem5397236 n)). Qed.
Lemma lem5397239 (n : nat) : (term29 n) = ((term21 n) = n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem5397240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5397241 (n : nat) : (term40 n) = (term41 n).
Proof. exact (MK_COMB (@lem5397240) (@lem5397239 n)). Qed.
Lemma lem5397242 (n : nat) : ((term29 n) = (term30 n)) = (((term21 n) = n) = (term39 n)).
Proof. exact (MK_COMB (@lem5397241 n) (@lem5397238 n)). Qed.
Lemma lem5397243 (n : nat) : ((term21 n) = n) = (term39 n).
Proof. exact (EQ_MP (@lem5397242 n) (@lem5397232 n)). Qed.
Lemma lem5397244 (d : nat) (n : nat) : (term36 d n) = (term36 d n).
Proof. exact (eq_refl (term36 d n)). Qed.
Lemma lem5397245 (n : nat) : (term38 n) = (term38 n).
Proof. exact (fun_ext (fun d : nat => @lem5397244 d n)). Qed.
Lemma lem5397246 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5397247 (n : nat) : (term39 n) = (term39 n).
Proof. exact (MK_COMB (@lem5397246) (@lem5397245 n)). Qed.
Lemma lem5397248 (n : nat) : (term41 n) = (term41 n).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem5397249 (n : nat) : (((term21 n) = n) = (term39 n)) = (((term21 n) = n) = (term39 n)).
Proof. exact (MK_COMB (@lem5397248 n) (@lem5397247 n)). Qed.
Lemma lem5397250 (n : nat) : ((term21 n) = n) = (term39 n).
Proof. exact (EQ_MP (@lem5397249 n) (@lem5397243 n)). Qed.
Lemma lem5397251 : term26 = term42.
Proof. exact (fun_ext (fun n : nat => @lem5397250 n)). Qed.
Lemma lem5397252 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5397253 : term28 = term43.
Proof. exact (MK_COMB (@lem5397252) (@lem5397251)). Qed.
Lemma lem5397280 : term28 = term43.
Proof. exact (TRANS (@lem5397231) (@lem5397253)). Qed.
Lemma lem5397285 (d : nat) (n : nat) : (d = n) = (d = n).
Proof. exact (eq_refl (d = n)). Qed.
Lemma lem5397308 (n : nat) (d : nat) : (term44 n d) = (term44 n d).
Proof. exact (eq_refl (term44 n d)). Qed.
Lemma lem5397315 (d : nat) : (term45 d) = (term31 d).
Proof. exact (@lem1032098 d term18). Qed.
Lemma lem5397324 (n : nat) : (term46 n) = (term46 n).
Proof. exact (eq_refl (term46 n)). Qed.
Lemma lem5397325 (n : nat) (d : nat) : ((term31 n) = (term45 d)) = ((term31 n) = (term31 d)).
Proof. exact (MK_COMB (@lem5397324 n) (@lem5397315 d)). Qed.
Lemma lem5397326 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5397327 (n : nat) (d : nat) : (term47 n d) = (term48 n d).
Proof. exact (MK_COMB (@lem5397326) (@lem5397325 n d)). Qed.
Lemma lem5397328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5397329 (n : nat) (d : nat) : (term49 n d) = (term50 n d).
Proof. exact (MK_COMB (@lem5397328) (@lem5397327 n d)). Qed.
Lemma lem5397330 (n : nat) (d : nat) : (term51 n d) = (term52 n d).
Proof. exact (MK_COMB (@lem5397329 n d) (@lem5397308 n d)). Qed.
Lemma lem5397331 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5397332 (n : nat) (d : nat) : (term34 n d) = (term53 n d).
Proof. exact (MK_COMB (@lem5397331) (@lem5397330 n d)). Qed.
Lemma lem5397333 (d : nat) (n : nat) : (term36 d n) = (term54 d n).
Proof. exact (MK_COMB (@lem5397332 n d) (@lem5397285 d n)). Qed.
Lemma lem5397334 (n : nat) : (term38 n) = (term55 n).
Proof. exact (fun_ext (fun d : nat => @lem5397333 d n)). Qed.
Lemma lem5397335 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5397336 (n : nat) : (term39 n) = (term56 n).
Proof. exact (MK_COMB (@lem5397335) (@lem5397334 n)). Qed.
Lemma lem5397337 : term42 = term57.
Proof. exact (fun_ext (fun n : nat => @lem5397336 n)). Qed.
Lemma lem5397338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5397339 : term43 = term58.
Proof. exact (MK_COMB (@lem5397338) (@lem5397337)). Qed.
Lemma lem5397342 : term28 = term58.
Proof. exact (TRANS (@lem5397280) (@lem5397339)). Qed.
Lemma lem5397344 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5397345 (n : nat) (d : nat) : ((term31 n) = (term31 d)) = ((term59 n) = (term59 d)).
Proof. exact (@lem5397344 (term31 n) (term31 d)). Qed.
Lemma lem5397349 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5397350 (n : nat) : (term59 n) = (term62 n).
Proof. exact (@lem5397349 n term18). Qed.
Lemma lem5397351 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem5397352 (n : nat) : (term63 n) = (term64 n).
Proof. exact (MK_COMB (@lem5397351) (@lem5397350 n)). Qed.
Lemma lem5397354 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5397355 (d : nat) : (term59 d) = (term62 d).
Proof. exact (@lem5397354 d term18). Qed.
Lemma lem5397356 (n : nat) (d : nat) : ((term59 n) = (term59 d)) = ((term62 n) = (term62 d)).
Proof. exact (MK_COMB (@lem5397352 n) (@lem5397355 d)). Qed.
Lemma lem5397357 (n : nat) (d : nat) : ((term31 n) = (term31 d)) = ((term62 n) = (term62 d)).
Proof. exact (TRANS (@lem5397345 n d) (@lem5397356 n d)). Qed.
Lemma lem5397358 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5397359 (n : nat) (d : nat) : (term48 n d) = (term65 n d).
Proof. exact (MK_COMB (@lem5397358) (@lem5397357 n d)). Qed.
Lemma lem5397360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5397361 (n : nat) (d : nat) : (term50 n d) = (term66 n d).
Proof. exact (MK_COMB (@lem5397360) (@lem5397359 n d)). Qed.
Lemma lem5397363 (m : nat) (n : nat) : (Peano.lt m n) = (term67 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5397364 (n : nat) : (term68 n) = (term69 n).
Proof. exact (@lem5397363 (term31 n) term18). Qed.
Lemma lem5397366 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5397367 (n : nat) : (term59 n) = (term62 n).
Proof. exact (@lem5397366 n term18). Qed.
Lemma lem5397368 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem5397369 (n : nat) : (term70 n) = (term71 n).
Proof. exact (MK_COMB (@lem5397368) (@lem5397367 n)). Qed.
Lemma lem5397370 : term72 = term72.
Proof. exact (eq_refl term72). Qed.
Lemma lem5397371 (n : nat) : (term69 n) = (term73 n).
Proof. exact (MK_COMB (@lem5397369 n) (@lem5397370)). Qed.
Lemma lem5397372 (n : nat) : (term68 n) = (term73 n).
Proof. exact (TRANS (@lem5397364 n) (@lem5397371 n)). Qed.
Lemma lem5397373 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5397374 (n : nat) : (term74 n) = (term75 n).
Proof. exact (MK_COMB (@lem5397373) (@lem5397372 n)). Qed.
Lemma lem5397375 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5397376 (n : nat) : (term76 n) = (term77 n).
Proof. exact (MK_COMB (@lem5397375) (@lem5397374 n)). Qed.
Lemma lem5397378 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5397379 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term78).
Proof. exact (@lem5397378 d (NUMERAL 0)). Qed.
Lemma lem5397382 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5397383 (d : nat) : (term79 d) = (term80 d).
Proof. exact (MK_COMB (@lem5397382) (@lem5397379 d)). Qed.
Lemma lem5397384 (n : nat) (d : nat) : (term44 n d) = (term81 n d).
Proof. exact (MK_COMB (@lem5397376 n) (@lem5397383 d)). Qed.
Lemma lem5397385 (n : nat) (d : nat) : (term52 n d) = (term82 n d).
Proof. exact (MK_COMB (@lem5397361 n d) (@lem5397384 n d)). Qed.
Lemma lem5397386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5397387 (n : nat) (d : nat) : (term53 n d) = (term83 n d).
Proof. exact (MK_COMB (@lem5397386) (@lem5397385 n d)). Qed.
Lemma lem5397389 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5397390 (d : nat) (n : nat) : (d = n) = ((int_of_num d) = (int_of_num n)).
Proof. exact (@lem5397389 d n). Qed.
Lemma lem5397393 (d : nat) (n : nat) : (term54 d n) = (term84 d n).
Proof. exact (MK_COMB (@lem5397387 n d) (@lem5397390 d n)). Qed.
Lemma lem5397394 (n : nat) : (term55 n) = (term85 n).
Proof. exact (fun_ext (fun d : nat => @lem5397393 d n)). Qed.
Lemma lem5397395 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5397396 (n : nat) : (term56 n) = (term86 n).
Proof. exact (MK_COMB (@lem5397395) (@lem5397394 n)). Qed.
Lemma lem5397397 : term57 = term87.
Proof. exact (fun_ext (fun n : nat => @lem5397396 n)). Qed.
Lemma lem5397398 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5397399 : term58 = term88.
Proof. exact (MK_COMB (@lem5397398) (@lem5397397)). Qed.
Lemma lem5397400 : term28 = term88.
Proof. exact (TRANS (@lem5397342) (@lem5397399)). Qed.
Lemma lem5397401 (d : nat) : term89 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem5397402 (d : nat) : (term89 d) = (term90 d).
Proof. exact (eq_refl (term89 d)). Qed.
Lemma lem5397403 (d : nat) : term90 d.
Proof. exact (EQ_MP (@lem5397402 d) (@lem5397401 d)). Qed.
Lemma lem5397404 (n : nat) : term89 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5397405 (n : nat) : (term89 n) = (term90 n).
Proof. exact (eq_refl (term89 n)). Qed.
Lemma lem5397406 (n : nat) : term90 n.
Proof. exact (EQ_MP (@lem5397405 n) (@lem5397404 n)). Qed.
Lemma lem5397407 (_69879 : int) (_69880 : int) : (term91 _69879 _69880) = (term92 _69879 _69880).
Proof. exact (@lem2318604 (term92 _69879 _69880)). Qed.
Lemma lem5397427 (_69880 : int) (_69879 : int) : (term93 _69880 _69879) = ((term94 _69880) = (term94 _69879)).
Proof. exact (@lem16933 ((term94 _69880) = (term94 _69879))). Qed.
Lemma lem5397430 (_69880 : int) : (term95 _69880) = (term96 _69880).
Proof. exact (@lem16933 (term96 _69880)). Qed.
Lemma lem5397433 (_69879 : int) : (term97 _69879) = (_69879 = term78).
Proof. exact (@lem16933 (_69879 = term78)). Qed.
Lemma lem5397434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5397435 (_69880 : int) : (term98 _69880) = (term99 _69880).
Proof. exact (MK_COMB (@lem5397434) (@lem5397430 _69880)). Qed.
Lemma lem5397436 (_69880 : int) (_69879 : int) : (term100 _69880 _69879) = (term101 _69880 _69879).
Proof. exact (MK_COMB (@lem5397435 _69880) (@lem5397433 _69879)). Qed.
Lemma lem5397437 (_69880 : int) (_69879 : int) : (term102 _69880 _69879) = (term100 _69880 _69879).
Proof. exact (@lem17160 (term103 _69880) (term104 _69879)). Qed.
Lemma lem5397438 (_69880 : int) (_69879 : int) : (term102 _69880 _69879) = (term101 _69880 _69879).
Proof. exact (TRANS (@lem5397437 _69880 _69879) (@lem5397436 _69880 _69879)). Qed.
Lemma lem5397439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5397440 (_69880 : int) (_69879 : int) : (term105 _69880 _69879) = (term106 _69880 _69879).
Proof. exact (MK_COMB (@lem5397439) (@lem5397427 _69880 _69879)). Qed.
Lemma lem5397441 (_69880 : int) (_69879 : int) : (term107 _69880 _69879) = (term108 _69880 _69879).
Proof. exact (MK_COMB (@lem5397440 _69880 _69879) (@lem5397438 _69880 _69879)). Qed.
Lemma lem5397442 (_69880 : int) (_69879 : int) : (term109 _69880 _69879) = (term107 _69880 _69879).
Proof. exact (@lem17045 (term110 _69880 _69879) (term111 _69880 _69879)). Qed.
Lemma lem5397443 (_69880 : int) (_69879 : int) : (term109 _69880 _69879) = (term108 _69880 _69879).
Proof. exact (TRANS (@lem5397442 _69880 _69879) (@lem5397441 _69880 _69879)). Qed.
Lemma lem5397444 (_69879 : int) (_69880 : int) : (term112 _69879 _69880) = (term112 _69879 _69880).
Proof. exact (eq_refl (term112 _69879 _69880)). Qed.
Lemma lem5397445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5397446 (_69880 : int) (_69879 : int) : (term113 _69880 _69879) = (term114 _69880 _69879).
Proof. exact (MK_COMB (@lem5397445) (@lem5397443 _69880 _69879)). Qed.
Lemma lem5397447 (_69879 : int) (_69880 : int) : (term115 _69879 _69880) = (term116 _69879 _69880).
Proof. exact (MK_COMB (@lem5397446 _69880 _69879) (@lem5397444 _69879 _69880)). Qed.
Lemma lem5397448 (_69879 : int) (_69880 : int) : (term117 _69879 _69880) = (term115 _69879 _69880).
Proof. exact (@lem17160 (term118 _69880 _69879) (_69879 = _69880)). Qed.
Lemma lem5397449 (_69879 : int) (_69880 : int) : (term117 _69879 _69880) = (term116 _69879 _69880).
Proof. exact (TRANS (@lem5397448 _69879 _69880) (@lem5397447 _69879 _69880)). Qed.
Lemma lem5397451 (_69880 : int) : (term119 _69880) = (term119 _69880).
Proof. exact (eq_refl (term119 _69880)). Qed.
Lemma lem5397452 (_69879 : int) (_69880 : int) : (term120 _69879 _69880) = (term121 _69879 _69880).
Proof. exact (MK_COMB (@lem5397451 _69880) (@lem5397449 _69879 _69880)). Qed.
Lemma lem5397453 (_69879 : int) (_69880 : int) : (term122 _69879 _69880) = (term120 _69879 _69880).
Proof. exact (@lem17362 (term123 _69880) (term124 _69879 _69880)). Qed.
Lemma lem5397454 (_69879 : int) (_69880 : int) : (term122 _69879 _69880) = (term121 _69879 _69880).
Proof. exact (TRANS (@lem5397453 _69879 _69880) (@lem5397452 _69879 _69880)). Qed.
Lemma lem5397456 (_69879 : int) : (term119 _69879) = (term119 _69879).
Proof. exact (eq_refl (term119 _69879)). Qed.
Lemma lem5397457 (_69879 : int) (_69880 : int) : (term125 _69879 _69880) = (term126 _69879 _69880).
Proof. exact (MK_COMB (@lem5397456 _69879) (@lem5397454 _69879 _69880)). Qed.
Lemma lem5397458 (_69879 : int) (_69880 : int) : (term127 _69879 _69880) = (term125 _69879 _69880).
Proof. exact (@lem17362 (term123 _69879) (term128 _69879 _69880)). Qed.
Lemma lem5397484 (_69879 : int) (_69880 : int) : (term127 _69879 _69880) = (term126 _69879 _69880).
Proof. exact (TRANS (@lem5397458 _69879 _69880) (@lem5397457 _69879 _69880)). Qed.
Lemma lem5397487 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5397488 (_69879 : int) : (term123 _69879) = (term130 _69879).
Proof. exact (@lem5397487 term78 _69879). Qed.
Lemma lem5397490 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5397491 : term132 = term133.
Proof. exact (@lem5397490 (NUMERAL 0)). Qed.
Lemma lem5397492 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5397493 : term134 = term135.
Proof. exact (MK_COMB (@lem5397492) (@lem5397491)). Qed.
Lemma lem5397494 (_69879 : int) : (real_of_int _69879) = (real_of_int _69879).
Proof. exact (eq_refl (real_of_int _69879)). Qed.
Lemma lem5397495 (_69879 : int) : (term130 _69879) = (term136 _69879).
Proof. exact (MK_COMB (@lem5397493) (@lem5397494 _69879)). Qed.
Lemma lem5397497 (_69879 : int) : (term123 _69879) = (term136 _69879).
Proof. exact (TRANS (@lem5397488 _69879) (@lem5397495 _69879)). Qed.
Lemma lem5397500 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5397501 (_69880 : int) : (term123 _69880) = (term130 _69880).
Proof. exact (@lem5397500 term78 _69880). Qed.
Lemma lem5397503 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5397504 : term132 = term133.
Proof. exact (@lem5397503 (NUMERAL 0)). Qed.
Lemma lem5397505 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5397506 : term134 = term135.
Proof. exact (MK_COMB (@lem5397505) (@lem5397504)). Qed.
Lemma lem5397507 (_69880 : int) : (real_of_int _69880) = (real_of_int _69880).
Proof. exact (eq_refl (real_of_int _69880)). Qed.
Lemma lem5397508 (_69880 : int) : (term130 _69880) = (term136 _69880).
Proof. exact (MK_COMB (@lem5397506) (@lem5397507 _69880)). Qed.
Lemma lem5397510 (_69880 : int) : (term123 _69880) = (term136 _69880).
Proof. exact (TRANS (@lem5397501 _69880) (@lem5397508 _69880)). Qed.
Lemma lem5397513 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5397514 (_69880 : int) (_69879 : int) : ((term94 _69880) = (term94 _69879)) = ((term137 _69880) = (term137 _69879)).
Proof. exact (@lem5397513 (term94 _69880) (term94 _69879)). Qed.
Lemma lem5397518 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5397519 (_69880 : int) : (term137 _69880) = (term140 _69880).
Proof. exact (@lem5397518 _69880 term72). Qed.
Lemma lem5397521 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5397522 : term141 = term142.
Proof. exact (@lem5397521 term18). Qed.
Lemma lem5397523 (_69880 : int) : (term143 _69880) = (term143 _69880).
Proof. exact (eq_refl (term143 _69880)). Qed.
Lemma lem5397524 (_69880 : int) : (term140 _69880) = (term144 _69880).
Proof. exact (MK_COMB (@lem5397523 _69880) (@lem5397522)). Qed.
Lemma lem5397525 (_69880 : int) : (term137 _69880) = (term144 _69880).
Proof. exact (TRANS (@lem5397519 _69880) (@lem5397524 _69880)). Qed.
Lemma lem5397526 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5397527 (_69880 : int) : (term145 _69880) = (term146 _69880).
Proof. exact (MK_COMB (@lem5397526) (@lem5397525 _69880)). Qed.
Lemma lem5397529 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5397530 (_69879 : int) : (term137 _69879) = (term140 _69879).
Proof. exact (@lem5397529 _69879 term72). Qed.
Lemma lem5397532 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5397533 : term141 = term142.
Proof. exact (@lem5397532 term18). Qed.
Lemma lem5397534 (_69879 : int) : (term143 _69879) = (term143 _69879).
Proof. exact (eq_refl (term143 _69879)). Qed.
Lemma lem5397535 (_69879 : int) : (term140 _69879) = (term144 _69879).
Proof. exact (MK_COMB (@lem5397534 _69879) (@lem5397533)). Qed.
Lemma lem5397536 (_69879 : int) : (term137 _69879) = (term144 _69879).
Proof. exact (TRANS (@lem5397530 _69879) (@lem5397535 _69879)). Qed.
Lemma lem5397537 (_69880 : int) (_69879 : int) : ((term137 _69880) = (term137 _69879)) = ((term144 _69880) = (term144 _69879)).
Proof. exact (MK_COMB (@lem5397527 _69880) (@lem5397536 _69879)). Qed.
Lemma lem5397539 (_69880 : int) (_69879 : int) : ((term94 _69880) = (term94 _69879)) = ((term144 _69880) = (term144 _69879)).
Proof. exact (TRANS (@lem5397514 _69880 _69879) (@lem5397537 _69880 _69879)). Qed.
Lemma lem5397541 (x : int) (y : int) : (int_lt x y) = (term147 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5397542 (_69880 : int) : (term96 _69880) = (term148 _69880).
Proof. exact (@lem5397541 (term94 _69880) term72). Qed.
Lemma lem5397544 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5397545 (_69880 : int) : (term148 _69880) = (term149 _69880).
Proof. exact (@lem5397544 (term150 _69880) term72). Qed.
Lemma lem5397547 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5397548 (_69880 : int) : (term151 _69880) = (term152 _69880).
Proof. exact (@lem5397547 (term94 _69880) term72). Qed.
Lemma lem5397550 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5397551 (_69880 : int) : (term137 _69880) = (term140 _69880).
Proof. exact (@lem5397550 _69880 term72). Qed.
Lemma lem5397553 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5397554 : term141 = term142.
Proof. exact (@lem5397553 term18). Qed.
Lemma lem5397555 (_69880 : int) : (term143 _69880) = (term143 _69880).
Proof. exact (eq_refl (term143 _69880)). Qed.
Lemma lem5397556 (_69880 : int) : (term140 _69880) = (term144 _69880).
Proof. exact (MK_COMB (@lem5397555 _69880) (@lem5397554)). Qed.
Lemma lem5397557 (_69880 : int) : (term137 _69880) = (term144 _69880).
Proof. exact (TRANS (@lem5397551 _69880) (@lem5397556 _69880)). Qed.
Lemma lem5397558 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5397559 (_69880 : int) : (term153 _69880) = (term154 _69880).
Proof. exact (MK_COMB (@lem5397558) (@lem5397557 _69880)). Qed.
Lemma lem5397561 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5397562 : term141 = term142.
Proof. exact (@lem5397561 term18). Qed.
Lemma lem5397563 (_69880 : int) : (term152 _69880) = (term155 _69880).
Proof. exact (MK_COMB (@lem5397559 _69880) (@lem5397562)). Qed.
Lemma lem5397564 (_69880 : int) : (term151 _69880) = (term155 _69880).
Proof. exact (TRANS (@lem5397548 _69880) (@lem5397563 _69880)). Qed.
Lemma lem5397565 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5397566 (_69880 : int) : (term156 _69880) = (term157 _69880).
Proof. exact (MK_COMB (@lem5397565) (@lem5397564 _69880)). Qed.
Lemma lem5397568 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5397569 : term141 = term142.
Proof. exact (@lem5397568 term18). Qed.
Lemma lem5397570 (_69880 : int) : (term149 _69880) = (term158 _69880).
Proof. exact (MK_COMB (@lem5397566 _69880) (@lem5397569)). Qed.
Lemma lem5397571 (_69880 : int) : (term148 _69880) = (term158 _69880).
Proof. exact (TRANS (@lem5397545 _69880) (@lem5397570 _69880)). Qed.
Lemma lem5397572 (_69880 : int) : (term96 _69880) = (term158 _69880).
Proof. exact (TRANS (@lem5397542 _69880) (@lem5397571 _69880)). Qed.
Lemma lem5397575 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5397576 (_69879 : int) : (_69879 = term78) = ((real_of_int _69879) = term132).
Proof. exact (@lem5397575 _69879 term78). Qed.
Lemma lem5397580 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5397581 : term132 = term133.
Proof. exact (@lem5397580 (NUMERAL 0)). Qed.
Lemma lem5397582 (_69879 : int) : (term159 _69879) = (term159 _69879).
Proof. exact (eq_refl (term159 _69879)). Qed.
Lemma lem5397583 (_69879 : int) : ((real_of_int _69879) = term132) = ((real_of_int _69879) = term133).
Proof. exact (MK_COMB (@lem5397582 _69879) (@lem5397581)). Qed.
Lemma lem5397585 (_69879 : int) : (_69879 = term78) = ((real_of_int _69879) = term133).
Proof. exact (TRANS (@lem5397576 _69879) (@lem5397583 _69879)). Qed.
Lemma lem5397586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5397587 (_69880 : int) : (term99 _69880) = (term160 _69880).
Proof. exact (MK_COMB (@lem5397586) (@lem5397572 _69880)). Qed.
Lemma lem5397588 (_69880 : int) (_69879 : int) : (term101 _69880 _69879) = (term161 _69880 _69879).
Proof. exact (MK_COMB (@lem5397587 _69880) (@lem5397585 _69879)). Qed.
Lemma lem5397589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5397590 (_69880 : int) (_69879 : int) : (term106 _69880 _69879) = (term162 _69880 _69879).
Proof. exact (MK_COMB (@lem5397589) (@lem5397539 _69880 _69879)). Qed.
Lemma lem5397591 (_69880 : int) (_69879 : int) : (term108 _69880 _69879) = (term163 _69880 _69879).
Proof. exact (MK_COMB (@lem5397590 _69880 _69879) (@lem5397588 _69880 _69879)). Qed.
Lemma lem5397593 (y : int) (x : int) : (term112 x y) = (term164 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem5397594 (_69880 : int) (_69879 : int) : (term112 _69879 _69880) = (term164 _69880 _69879).
Proof. exact (@lem5397593 _69880 _69879). Qed.
Lemma lem5397596 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5397597 (_69879 : int) (_69880 : int) : (term147 _69879 _69880) = (term165 _69879 _69880).
Proof. exact (@lem5397596 (term94 _69879) _69880). Qed.
Lemma lem5397599 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5397600 (_69879 : int) : (term137 _69879) = (term140 _69879).
Proof. exact (@lem5397599 _69879 term72). Qed.
Lemma lem5397602 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5397603 : term141 = term142.
Proof. exact (@lem5397602 term18). Qed.
Lemma lem5397604 (_69879 : int) : (term143 _69879) = (term143 _69879).
Proof. exact (eq_refl (term143 _69879)). Qed.
Lemma lem5397605 (_69879 : int) : (term140 _69879) = (term144 _69879).
Proof. exact (MK_COMB (@lem5397604 _69879) (@lem5397603)). Qed.
Lemma lem5397606 (_69879 : int) : (term137 _69879) = (term144 _69879).
Proof. exact (TRANS (@lem5397600 _69879) (@lem5397605 _69879)). Qed.
Lemma lem5397607 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5397608 (_69879 : int) : (term166 _69879) = (term167 _69879).
Proof. exact (MK_COMB (@lem5397607) (@lem5397606 _69879)). Qed.
Lemma lem5397609 (_69880 : int) : (real_of_int _69880) = (real_of_int _69880).
Proof. exact (eq_refl (real_of_int _69880)). Qed.
Lemma lem5397610 (_69879 : int) (_69880 : int) : (term165 _69879 _69880) = (term168 _69879 _69880).
Proof. exact (MK_COMB (@lem5397608 _69879) (@lem5397609 _69880)). Qed.
Lemma lem5397611 (_69879 : int) (_69880 : int) : (term147 _69879 _69880) = (term168 _69879 _69880).
Proof. exact (TRANS (@lem5397597 _69879 _69880) (@lem5397610 _69879 _69880)). Qed.
Lemma lem5397612 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5397613 (_69879 : int) (_69880 : int) : (term169 _69879 _69880) = (term170 _69879 _69880).
Proof. exact (MK_COMB (@lem5397612) (@lem5397611 _69879 _69880)). Qed.
Lemma lem5397615 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5397616 (_69880 : int) (_69879 : int) : (term147 _69880 _69879) = (term165 _69880 _69879).
Proof. exact (@lem5397615 (term94 _69880) _69879). Qed.
Lemma lem5397618 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5397619 (_69880 : int) : (term137 _69880) = (term140 _69880).
Proof. exact (@lem5397618 _69880 term72). Qed.
Lemma lem5397621 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5397622 : term141 = term142.
Proof. exact (@lem5397621 term18). Qed.
Lemma lem5397623 (_69880 : int) : (term143 _69880) = (term143 _69880).
Proof. exact (eq_refl (term143 _69880)). Qed.
Lemma lem5397624 (_69880 : int) : (term140 _69880) = (term144 _69880).
Proof. exact (MK_COMB (@lem5397623 _69880) (@lem5397622)). Qed.
Lemma lem5397625 (_69880 : int) : (term137 _69880) = (term144 _69880).
Proof. exact (TRANS (@lem5397619 _69880) (@lem5397624 _69880)). Qed.
Lemma lem5397626 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5397627 (_69880 : int) : (term166 _69880) = (term167 _69880).
Proof. exact (MK_COMB (@lem5397626) (@lem5397625 _69880)). Qed.
Lemma lem5397628 (_69879 : int) : (real_of_int _69879) = (real_of_int _69879).
Proof. exact (eq_refl (real_of_int _69879)). Qed.
Lemma lem5397629 (_69880 : int) (_69879 : int) : (term165 _69880 _69879) = (term168 _69880 _69879).
Proof. exact (MK_COMB (@lem5397627 _69880) (@lem5397628 _69879)). Qed.
Lemma lem5397630 (_69880 : int) (_69879 : int) : (term147 _69880 _69879) = (term168 _69880 _69879).
Proof. exact (TRANS (@lem5397616 _69880 _69879) (@lem5397629 _69880 _69879)). Qed.
Lemma lem5397631 (_69880 : int) (_69879 : int) : (term164 _69880 _69879) = (term171 _69880 _69879).
Proof. exact (MK_COMB (@lem5397613 _69879 _69880) (@lem5397630 _69880 _69879)). Qed.
Lemma lem5397632 (_69880 : int) (_69879 : int) : (term112 _69879 _69880) = (term171 _69880 _69879).
Proof. exact (TRANS (@lem5397594 _69880 _69879) (@lem5397631 _69880 _69879)). Qed.
Lemma lem5397633 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5397634 (_69880 : int) (_69879 : int) : (term114 _69880 _69879) = (term172 _69880 _69879).
Proof. exact (MK_COMB (@lem5397633) (@lem5397591 _69880 _69879)). Qed.
Lemma lem5397635 (_69880 : int) (_69879 : int) : (term116 _69879 _69880) = (term173 _69880 _69879).
Proof. exact (MK_COMB (@lem5397634 _69880 _69879) (@lem5397632 _69880 _69879)). Qed.
Lemma lem5397636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5397637 (_69880 : int) : (term119 _69880) = (term174 _69880).
Proof. exact (MK_COMB (@lem5397636) (@lem5397510 _69880)). Qed.
Lemma lem5397638 (_69880 : int) (_69879 : int) : (term121 _69879 _69880) = (term175 _69880 _69879).
Proof. exact (MK_COMB (@lem5397637 _69880) (@lem5397635 _69880 _69879)). Qed.
Lemma lem5397639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5397640 (_69879 : int) : (term119 _69879) = (term174 _69879).
Proof. exact (MK_COMB (@lem5397639) (@lem5397497 _69879)). Qed.
Lemma lem5397641 (_69880 : int) (_69879 : int) : (term126 _69879 _69880) = (term176 _69880 _69879).
Proof. exact (MK_COMB (@lem5397640 _69879) (@lem5397638 _69880 _69879)). Qed.
Lemma lem5397642 (_69880 : int) (_69879 : int) : (term127 _69879 _69880) = (term176 _69880 _69879).
Proof. exact (TRANS (@lem5397484 _69879 _69880) (@lem5397641 _69880 _69879)). Qed.
Lemma lem5397646 (t : Prop) : (term177 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5397712 (_69880 : int) (_69879 : int) : (term178 _69880 _69879) = (term176 _69880 _69879).
Proof. exact (@lem5397646 (term176 _69880 _69879)). Qed.
Lemma lem5397713 (_69879 : int) : (term136 _69879) = (term179 _69879).
Proof. exact (@lem1988287 (real_of_int _69879) term133). Qed.
Lemma lem5397719 (_69879 : int) : (term180 _69879) = (term181 _69879).
Proof. exact (@lem1982792 (real_of_int _69879) term133). Qed.
Lemma lem5397721 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5397722 : term133 = term183.
Proof. exact (@lem5397721 (NUMERAL 0)). Qed.
Lemma lem5397724 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5397725 : term186 = term187.
Proof. exact (@lem5397724 term18). Qed.
Lemma lem5397726 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5397727 : term188 = term189.
Proof. exact (MK_COMB (@lem5397726) (@lem5397725)). Qed.
Lemma lem5397728 : term190 = term191.
Proof. exact (MK_COMB (@lem5397727) (@lem5397722)). Qed.
Lemma lem5397729 : term191 = term192.
Proof. exact (@lem1981613 term186 term133 term142 term142). Qed.
Lemma lem5397731 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5397732 : term195 = term196.
Proof. exact (@lem5397731 term18 term18). Qed.
Lemma lem5397733 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5397734 : term198 = term18.
Proof. exact (EQ_MP (@lem5397733) (@lem940073)). Qed.
Lemma lem5397735 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5397736 : term196 = term142.
Proof. exact (MK_COMB (@lem5397735) (@lem5397734)). Qed.
Lemma lem5397737 : term195 = term142.
Proof. exact (TRANS (@lem5397732) (@lem5397736)). Qed.
Lemma lem5397739 (x : nat) : (term199 x) = term133.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5397740 : term190 = term133.
Proof. exact (@lem5397739 term18). Qed.
Lemma lem5397741 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5397742 : term200 = term201.
Proof. exact (MK_COMB (@lem5397741) (@lem5397740)). Qed.
Lemma lem5397743 : term192 = term183.
Proof. exact (MK_COMB (@lem5397742) (@lem5397737)). Qed.
Lemma lem5397744 : term191 = term183.
Proof. exact (TRANS (@lem5397729) (@lem5397743)). Qed.
Lemma lem5397745 : term190 = term183.
Proof. exact (TRANS (@lem5397728) (@lem5397744)). Qed.
Lemma lem5397747 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5397748 : term183 = term133.
Proof. exact (@lem5397747 term133). Qed.
Lemma lem5397749 : term190 = term133.
Proof. exact (TRANS (@lem5397745) (@lem5397748)). Qed.
Lemma lem5397750 (_69879 : int) : (term143 _69879) = (term143 _69879).
Proof. exact (eq_refl (term143 _69879)). Qed.
Lemma lem5397751 (_69879 : int) : (term181 _69879) = (term203 _69879).
Proof. exact (MK_COMB (@lem5397750 _69879) (@lem5397749)). Qed.
Lemma lem5397752 (_69879 : int) : (term203 _69879) = (real_of_int _69879).
Proof. exact (@lem1982723 (real_of_int _69879)). Qed.
Lemma lem5397753 (_69879 : int) : (term181 _69879) = (real_of_int _69879).
Proof. exact (TRANS (@lem5397751 _69879) (@lem5397752 _69879)). Qed.
Lemma lem5397755 (_69879 : int) : (term180 _69879) = (real_of_int _69879).
Proof. exact (TRANS (@lem5397719 _69879) (@lem5397753 _69879)). Qed.
Lemma lem5397756 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5397757 (_69879 : int) : (term204 _69879) = (term205 _69879).
Proof. exact (MK_COMB (@lem5397756) (@lem5397755 _69879)). Qed.
Lemma lem5397758 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5397759 (_69879 : int) : (term179 _69879) = (term206 _69879).
Proof. exact (MK_COMB (@lem5397757 _69879) (@lem5397758)). Qed.
Lemma lem5397760 (_69879 : int) : (term136 _69879) = (term206 _69879).
Proof. exact (TRANS (@lem5397713 _69879) (@lem5397759 _69879)). Qed.
Lemma lem5397761 (_69880 : int) : (term136 _69880) = (term179 _69880).
Proof. exact (@lem1988287 (real_of_int _69880) term133). Qed.
Lemma lem5397767 (_69880 : int) : (term180 _69880) = (term181 _69880).
Proof. exact (@lem1982792 (real_of_int _69880) term133). Qed.
Lemma lem5397769 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5397770 : term133 = term183.
Proof. exact (@lem5397769 (NUMERAL 0)). Qed.
Lemma lem5397772 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5397773 : term186 = term187.
Proof. exact (@lem5397772 term18). Qed.
Lemma lem5397774 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5397775 : term188 = term189.
Proof. exact (MK_COMB (@lem5397774) (@lem5397773)). Qed.
Lemma lem5397776 : term190 = term191.
Proof. exact (MK_COMB (@lem5397775) (@lem5397770)). Qed.
Lemma lem5397777 : term191 = term192.
Proof. exact (@lem1981613 term186 term133 term142 term142). Qed.
Lemma lem5397779 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5397780 : term195 = term196.
Proof. exact (@lem5397779 term18 term18). Qed.
Lemma lem5397781 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5397782 : term198 = term18.
Proof. exact (EQ_MP (@lem5397781) (@lem940073)). Qed.
Lemma lem5397783 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5397784 : term196 = term142.
Proof. exact (MK_COMB (@lem5397783) (@lem5397782)). Qed.
Lemma lem5397785 : term195 = term142.
Proof. exact (TRANS (@lem5397780) (@lem5397784)). Qed.
Lemma lem5397787 (x : nat) : (term199 x) = term133.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5397788 : term190 = term133.
Proof. exact (@lem5397787 term18). Qed.
Lemma lem5397789 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5397790 : term200 = term201.
Proof. exact (MK_COMB (@lem5397789) (@lem5397788)). Qed.
Lemma lem5397791 : term192 = term183.
Proof. exact (MK_COMB (@lem5397790) (@lem5397785)). Qed.
Lemma lem5397792 : term191 = term183.
Proof. exact (TRANS (@lem5397777) (@lem5397791)). Qed.
Lemma lem5397793 : term190 = term183.
Proof. exact (TRANS (@lem5397776) (@lem5397792)). Qed.
Lemma lem5397795 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5397796 : term183 = term133.
Proof. exact (@lem5397795 term133). Qed.
Lemma lem5397797 : term190 = term133.
Proof. exact (TRANS (@lem5397793) (@lem5397796)). Qed.
Lemma lem5397798 (_69880 : int) : (term143 _69880) = (term143 _69880).
Proof. exact (eq_refl (term143 _69880)). Qed.
Lemma lem5397799 (_69880 : int) : (term181 _69880) = (term203 _69880).
Proof. exact (MK_COMB (@lem5397798 _69880) (@lem5397797)). Qed.
Lemma lem5397800 (_69880 : int) : (term203 _69880) = (real_of_int _69880).
Proof. exact (@lem1982723 (real_of_int _69880)). Qed.
Lemma lem5397801 (_69880 : int) : (term181 _69880) = (real_of_int _69880).
Proof. exact (TRANS (@lem5397799 _69880) (@lem5397800 _69880)). Qed.
Lemma lem5397803 (_69880 : int) : (term180 _69880) = (real_of_int _69880).
Proof. exact (TRANS (@lem5397767 _69880) (@lem5397801 _69880)). Qed.
Lemma lem5397804 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5397805 (_69880 : int) : (term204 _69880) = (term205 _69880).
Proof. exact (MK_COMB (@lem5397804) (@lem5397803 _69880)). Qed.
Lemma lem5397806 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5397807 (_69880 : int) : (term179 _69880) = (term206 _69880).
Proof. exact (MK_COMB (@lem5397805 _69880) (@lem5397806)). Qed.
Lemma lem5397808 (_69880 : int) : (term136 _69880) = (term206 _69880).
Proof. exact (TRANS (@lem5397761 _69880) (@lem5397807 _69880)). Qed.
Lemma lem5397809 (_69880 : int) (_69879 : int) : ((term144 _69880) = (term144 _69879)) = ((term207 _69880 _69879) = term133).
Proof. exact (@lem1988293 (term144 _69880) (term144 _69879)). Qed.
Lemma lem5397827 (_69880 : int) (_69879 : int) : (term207 _69880 _69879) = (term208 _69880 _69879).
Proof. exact (@lem1982792 (term144 _69880) (term144 _69879)). Qed.
Lemma lem5397828 (_69879 : int) : (term209 _69879) = (term210 _69879).
Proof. exact (@lem1982781 (real_of_int _69879) term186 term142). Qed.
Lemma lem5397830 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5397831 : term142 = term211.
Proof. exact (@lem5397830 term18). Qed.
Lemma lem5397833 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5397834 : term186 = term187.
Proof. exact (@lem5397833 term18). Qed.
Lemma lem5397835 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5397836 : term188 = term189.
Proof. exact (MK_COMB (@lem5397835) (@lem5397834)). Qed.
Lemma lem5397837 : term212 = term213.
Proof. exact (MK_COMB (@lem5397836) (@lem5397831)). Qed.
Lemma lem5397838 : term213 = term214.
Proof. exact (@lem1981613 term186 term142 term142 term142). Qed.
Lemma lem5397840 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5397841 : term195 = term196.
Proof. exact (@lem5397840 term18 term18). Qed.
Lemma lem5397842 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5397843 : term198 = term18.
Proof. exact (EQ_MP (@lem5397842) (@lem940073)). Qed.
Lemma lem5397844 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5397845 : term196 = term142.
Proof. exact (MK_COMB (@lem5397844) (@lem5397843)). Qed.
Lemma lem5397846 : term195 = term142.
Proof. exact (TRANS (@lem5397841) (@lem5397845)). Qed.
Lemma lem5397848 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5397849 : term212 = term217.
Proof. exact (@lem5397848 term18 term18). Qed.
Lemma lem5397850 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5397851 : term198 = term18.
Proof. exact (EQ_MP (@lem5397850) (@lem940073)). Qed.
Lemma lem5397852 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5397853 : term196 = term142.
Proof. exact (MK_COMB (@lem5397852) (@lem5397851)). Qed.
Lemma lem5397854 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5397855 : term217 = term186.
Proof. exact (MK_COMB (@lem5397854) (@lem5397853)). Qed.
Lemma lem5397856 : term212 = term186.
Proof. exact (TRANS (@lem5397849) (@lem5397855)). Qed.
Lemma lem5397857 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5397858 : term218 = term219.
Proof. exact (MK_COMB (@lem5397857) (@lem5397856)). Qed.
Lemma lem5397859 : term214 = term187.
Proof. exact (MK_COMB (@lem5397858) (@lem5397846)). Qed.
Lemma lem5397860 : term213 = term187.
Proof. exact (TRANS (@lem5397838) (@lem5397859)). Qed.
Lemma lem5397861 : term212 = term187.
Proof. exact (TRANS (@lem5397837) (@lem5397860)). Qed.
Lemma lem5397863 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5397864 : term187 = term186.
Proof. exact (@lem5397863 term186). Qed.
Lemma lem5397865 : term212 = term186.
Proof. exact (TRANS (@lem5397861) (@lem5397864)). Qed.
Lemma lem5397868 (_69879 : int) : (term220 _69879) = (term220 _69879).
Proof. exact (eq_refl (term220 _69879)). Qed.
Lemma lem5397869 (_69879 : int) : (term210 _69879) = (term221 _69879).
Proof. exact (MK_COMB (@lem5397868 _69879) (@lem5397865)). Qed.
Lemma lem5397870 (_69879 : int) : (term209 _69879) = (term221 _69879).
Proof. exact (TRANS (@lem5397828 _69879) (@lem5397869 _69879)). Qed.
Lemma lem5397871 (_69880 : int) : (term154 _69880) = (term154 _69880).
Proof. exact (eq_refl (term154 _69880)). Qed.
Lemma lem5397872 (_69880 : int) (_69879 : int) : (term208 _69880 _69879) = (term222 _69880 _69879).
Proof. exact (MK_COMB (@lem5397871 _69880) (@lem5397870 _69879)). Qed.
Lemma lem5397873 (_69879 : int) (_69880 : int) : (term222 _69880 _69879) = (term223 _69879 _69880).
Proof. exact (@lem1982757 (term224 _69879) (term144 _69880) term186). Qed.
Lemma lem5397874 (_69880 : int) : (term225 _69880) = (term226 _69880).
Proof. exact (@lem1982755 (real_of_int _69880) term142 term186). Qed.
Lemma lem5397876 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5397877 : term186 = term187.
Proof. exact (@lem5397876 term18). Qed.
Lemma lem5397879 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5397880 : term142 = term211.
Proof. exact (@lem5397879 term18). Qed.
Lemma lem5397881 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5397882 : term227 = term228.
Proof. exact (MK_COMB (@lem5397881) (@lem5397880)). Qed.
Lemma lem5397883 : term229 = term230.
Proof. exact (MK_COMB (@lem5397882) (@lem5397877)). Qed.
Lemma lem5397884 : term231.
Proof. exact (@lem1981473 term142 term142 term186 term142 term133 term142). Qed.
Lemma lem5397886 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5397887 : term233 = term234.
Proof. exact (@lem5397886 (NUMERAL 0) term18). Qed.
Lemma lem5397888 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5397889 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5397890 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5397889 h1) (fun h1 : term234 = True => @lem5397888)). Qed.
Lemma lem5397891 : term234 = True.
Proof. exact (EQ_MP (@lem5397890) (@lem5397888)). Qed.
Lemma lem5397892 : term233 = True.
Proof. exact (TRANS (@lem5397887) (@lem5397891)). Qed.
Lemma lem5397893 : True = term233.
Proof. exact (SYM (@lem5397892)). Qed.
Lemma lem5397894 : term233.
Proof. exact (EQ_MP (@lem5397893) (@lem0)). Qed.
Lemma lem5397895 : term236.
Proof. exact (@lem5397884 (@lem5397894)). Qed.
Lemma lem5397897 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5397898 : term233 = term234.
Proof. exact (@lem5397897 (NUMERAL 0) term18). Qed.
Lemma lem5397899 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5397900 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5397901 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5397900 h1) (fun h1 : term234 = True => @lem5397899)). Qed.
Lemma lem5397902 : term234 = True.
Proof. exact (EQ_MP (@lem5397901) (@lem5397899)). Qed.
Lemma lem5397903 : term233 = True.
Proof. exact (TRANS (@lem5397898) (@lem5397902)). Qed.
Lemma lem5397904 : True = term233.
Proof. exact (SYM (@lem5397903)). Qed.
Lemma lem5397905 : term233.
Proof. exact (EQ_MP (@lem5397904) (@lem0)). Qed.
Lemma lem5397906 : term237.
Proof. exact (@lem5397895 (@lem5397905)). Qed.
Lemma lem5397908 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5397909 : term233 = term234.
Proof. exact (@lem5397908 (NUMERAL 0) term18). Qed.
Lemma lem5397910 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5397911 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5397912 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5397911 h1) (fun h1 : term234 = True => @lem5397910)). Qed.
Lemma lem5397913 : term234 = True.
Proof. exact (EQ_MP (@lem5397912) (@lem5397910)). Qed.
Lemma lem5397914 : term233 = True.
Proof. exact (TRANS (@lem5397909) (@lem5397913)). Qed.
Lemma lem5397915 : True = term233.
Proof. exact (SYM (@lem5397914)). Qed.
Lemma lem5397916 : term233.
Proof. exact (EQ_MP (@lem5397915) (@lem0)). Qed.
Lemma lem5397917 : term238.
Proof. exact (@lem5397906 (@lem5397916)). Qed.
Lemma lem5397919 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5397920 : term212 = term217.
Proof. exact (@lem5397919 term18 term18). Qed.
Lemma lem5397921 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5397922 : term198 = term18.
Proof. exact (EQ_MP (@lem5397921) (@lem940073)). Qed.
Lemma lem5397923 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5397924 : term196 = term142.
Proof. exact (MK_COMB (@lem5397923) (@lem5397922)). Qed.
Lemma lem5397925 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5397926 : term217 = term186.
Proof. exact (MK_COMB (@lem5397925) (@lem5397924)). Qed.
Lemma lem5397927 : term212 = term186.
Proof. exact (TRANS (@lem5397920) (@lem5397926)). Qed.
Lemma lem5397929 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5397930 : term195 = term196.
Proof. exact (@lem5397929 term18 term18). Qed.
Lemma lem5397931 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5397932 : term198 = term18.
Proof. exact (EQ_MP (@lem5397931) (@lem940073)). Qed.
Lemma lem5397933 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5397934 : term196 = term142.
Proof. exact (MK_COMB (@lem5397933) (@lem5397932)). Qed.
Lemma lem5397935 : term195 = term142.
Proof. exact (TRANS (@lem5397930) (@lem5397934)). Qed.
Lemma lem5397936 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5397937 : term239 = term227.
Proof. exact (MK_COMB (@lem5397936) (@lem5397935)). Qed.
Lemma lem5397938 : term240 = term229.
Proof. exact (MK_COMB (@lem5397937) (@lem5397927)). Qed.
Lemma lem5397940 (m : nat) : (term241 m) = term133.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5397941 : term229 = term133.
Proof. exact (@lem5397940 term18). Qed.
Lemma lem5397942 : term240 = term133.
Proof. exact (TRANS (@lem5397938) (@lem5397941)). Qed.
Lemma lem5397943 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5397944 : term242 = term243.
Proof. exact (MK_COMB (@lem5397943) (@lem5397942)). Qed.
Lemma lem5397945 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem5397946 : term244 = term245.
Proof. exact (MK_COMB (@lem5397944) (@lem5397945)). Qed.
Lemma lem5397948 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5397949 : term245 = term133.
Proof. exact (@lem5397948 term18). Qed.
Lemma lem5397950 : term244 = term133.
Proof. exact (TRANS (@lem5397946) (@lem5397949)). Qed.
Lemma lem5397952 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5397953 : term195 = term196.
Proof. exact (@lem5397952 term18 term18). Qed.
Lemma lem5397954 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5397955 : term198 = term18.
Proof. exact (EQ_MP (@lem5397954) (@lem940073)). Qed.
Lemma lem5397956 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5397957 : term196 = term142.
Proof. exact (MK_COMB (@lem5397956) (@lem5397955)). Qed.
Lemma lem5397958 : term195 = term142.
Proof. exact (TRANS (@lem5397953) (@lem5397957)). Qed.
Lemma lem5397959 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem5397960 : term247 = term245.
Proof. exact (MK_COMB (@lem5397959) (@lem5397958)). Qed.
Lemma lem5397962 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5397963 : term245 = term133.
Proof. exact (@lem5397962 term18). Qed.
Lemma lem5397964 : term247 = term133.
Proof. exact (TRANS (@lem5397960) (@lem5397963)). Qed.
Lemma lem5397965 : term133 = term247.
Proof. exact (SYM (@lem5397964)). Qed.
Lemma lem5397966 : term244 = term247.
Proof. exact (TRANS (@lem5397950) (@lem5397965)). Qed.
Lemma lem5397967 : term230 = term183.
Proof. exact (@lem5397917 (@lem5397966)). Qed.
Lemma lem5397968 : term229 = term183.
Proof. exact (TRANS (@lem5397883) (@lem5397967)). Qed.
Lemma lem5397970 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5397971 : term183 = term133.
Proof. exact (@lem5397970 term133). Qed.
Lemma lem5397972 : term229 = term133.
Proof. exact (TRANS (@lem5397968) (@lem5397971)). Qed.
Lemma lem5397973 (_69880 : int) : (term143 _69880) = (term143 _69880).
Proof. exact (eq_refl (term143 _69880)). Qed.
Lemma lem5397974 (_69880 : int) : (term226 _69880) = (term203 _69880).
Proof. exact (MK_COMB (@lem5397973 _69880) (@lem5397972)). Qed.
Lemma lem5397975 (_69880 : int) : (term225 _69880) = (term203 _69880).
Proof. exact (TRANS (@lem5397874 _69880) (@lem5397974 _69880)). Qed.
Lemma lem5397976 (_69880 : int) : (term203 _69880) = (real_of_int _69880).
Proof. exact (@lem1982723 (real_of_int _69880)). Qed.
Lemma lem5397977 (_69880 : int) : (term225 _69880) = (real_of_int _69880).
Proof. exact (TRANS (@lem5397975 _69880) (@lem5397976 _69880)). Qed.
Lemma lem5397978 (_69879 : int) : (term220 _69879) = (term220 _69879).
Proof. exact (eq_refl (term220 _69879)). Qed.
Lemma lem5397979 (_69879 : int) (_69880 : int) : (term223 _69879 _69880) = (term248 _69879 _69880).
Proof. exact (MK_COMB (@lem5397978 _69879) (@lem5397977 _69880)). Qed.
Lemma lem5397980 (_69879 : int) (_69880 : int) : (term222 _69880 _69879) = (term248 _69879 _69880).
Proof. exact (TRANS (@lem5397873 _69879 _69880) (@lem5397979 _69879 _69880)). Qed.
Lemma lem5397981 (_69879 : int) (_69880 : int) : (term208 _69880 _69879) = (term248 _69879 _69880).
Proof. exact (TRANS (@lem5397872 _69880 _69879) (@lem5397980 _69879 _69880)). Qed.
Lemma lem5397983 (_69879 : int) (_69880 : int) : (term207 _69880 _69879) = (term248 _69879 _69880).
Proof. exact (TRANS (@lem5397827 _69880 _69879) (@lem5397981 _69879 _69880)). Qed.
Lemma lem5397984 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5397985 (_69879 : int) (_69880 : int) : (term249 _69880 _69879) = (term250 _69879 _69880).
Proof. exact (MK_COMB (@lem5397984) (@lem5397983 _69879 _69880)). Qed.
Lemma lem5397986 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5397987 (_69879 : int) (_69880 : int) : ((term207 _69880 _69879) = term133) = ((term248 _69879 _69880) = term133).
Proof. exact (MK_COMB (@lem5397985 _69879 _69880) (@lem5397986)). Qed.
Lemma lem5397988 (_69879 : int) (_69880 : int) : ((term144 _69880) = (term144 _69879)) = ((term248 _69879 _69880) = term133).
Proof. exact (TRANS (@lem5397809 _69880 _69879) (@lem5397987 _69879 _69880)). Qed.
Lemma lem5397989 (_69880 : int) : (term158 _69880) = (term251 _69880).
Proof. exact (@lem1988287 term142 (term155 _69880)). Qed.
Lemma lem5398001 (_69880 : int) : (term155 _69880) = (term252 _69880).
Proof. exact (@lem1982755 (real_of_int _69880) term142 term142). Qed.
Lemma lem5398003 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5398004 : term142 = term211.
Proof. exact (@lem5398003 term18). Qed.
Lemma lem5398006 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5398007 : term142 = term211.
Proof. exact (@lem5398006 term18). Qed.
Lemma lem5398008 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5398009 : term227 = term228.
Proof. exact (MK_COMB (@lem5398008) (@lem5398007)). Qed.
Lemma lem5398010 : term253 = term254.
Proof. exact (MK_COMB (@lem5398009) (@lem5398004)). Qed.
Lemma lem5398011 : term255.
Proof. exact (@lem1981473 term142 term142 term142 term142 term256 term142). Qed.
Lemma lem5398013 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398014 : term233 = term234.
Proof. exact (@lem5398013 (NUMERAL 0) term18). Qed.
Lemma lem5398015 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398016 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398017 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398016 h1) (fun h1 : term234 = True => @lem5398015)). Qed.
Lemma lem5398018 : term234 = True.
Proof. exact (EQ_MP (@lem5398017) (@lem5398015)). Qed.
Lemma lem5398019 : term233 = True.
Proof. exact (TRANS (@lem5398014) (@lem5398018)). Qed.
Lemma lem5398020 : True = term233.
Proof. exact (SYM (@lem5398019)). Qed.
Lemma lem5398021 : term233.
Proof. exact (EQ_MP (@lem5398020) (@lem0)). Qed.
Lemma lem5398022 : term257.
Proof. exact (@lem5398011 (@lem5398021)). Qed.
Lemma lem5398024 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398025 : term233 = term234.
Proof. exact (@lem5398024 (NUMERAL 0) term18). Qed.
Lemma lem5398026 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398027 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398028 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398027 h1) (fun h1 : term234 = True => @lem5398026)). Qed.
Lemma lem5398029 : term234 = True.
Proof. exact (EQ_MP (@lem5398028) (@lem5398026)). Qed.
Lemma lem5398030 : term233 = True.
Proof. exact (TRANS (@lem5398025) (@lem5398029)). Qed.
Lemma lem5398031 : True = term233.
Proof. exact (SYM (@lem5398030)). Qed.
Lemma lem5398032 : term233.
Proof. exact (EQ_MP (@lem5398031) (@lem0)). Qed.
Lemma lem5398033 : term258.
Proof. exact (@lem5398022 (@lem5398032)). Qed.
Lemma lem5398035 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398036 : term233 = term234.
Proof. exact (@lem5398035 (NUMERAL 0) term18). Qed.
Lemma lem5398037 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398038 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398039 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398038 h1) (fun h1 : term234 = True => @lem5398037)). Qed.
Lemma lem5398040 : term234 = True.
Proof. exact (EQ_MP (@lem5398039) (@lem5398037)). Qed.
Lemma lem5398041 : term233 = True.
Proof. exact (TRANS (@lem5398036) (@lem5398040)). Qed.
Lemma lem5398042 : True = term233.
Proof. exact (SYM (@lem5398041)). Qed.
Lemma lem5398043 : term233.
Proof. exact (EQ_MP (@lem5398042) (@lem0)). Qed.
Lemma lem5398044 : term259.
Proof. exact (@lem5398033 (@lem5398043)). Qed.
Lemma lem5398046 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398047 : term195 = term196.
Proof. exact (@lem5398046 term18 term18). Qed.
Lemma lem5398048 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398049 : term198 = term18.
Proof. exact (EQ_MP (@lem5398048) (@lem940073)). Qed.
Lemma lem5398050 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398051 : term196 = term142.
Proof. exact (MK_COMB (@lem5398050) (@lem5398049)). Qed.
Lemma lem5398052 : term195 = term142.
Proof. exact (TRANS (@lem5398047) (@lem5398051)). Qed.
Lemma lem5398054 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398055 : term195 = term196.
Proof. exact (@lem5398054 term18 term18). Qed.
Lemma lem5398056 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398057 : term198 = term18.
Proof. exact (EQ_MP (@lem5398056) (@lem940073)). Qed.
Lemma lem5398058 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398059 : term196 = term142.
Proof. exact (MK_COMB (@lem5398058) (@lem5398057)). Qed.
Lemma lem5398060 : term195 = term142.
Proof. exact (TRANS (@lem5398055) (@lem5398059)). Qed.
Lemma lem5398061 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5398062 : term239 = term227.
Proof. exact (MK_COMB (@lem5398061) (@lem5398060)). Qed.
Lemma lem5398063 : term260 = term253.
Proof. exact (MK_COMB (@lem5398062) (@lem5398052)). Qed.
Lemma lem5398064 : term253 = term261.
Proof. exact (@lem1367770 term18 term18). Qed.
Lemma lem5398065 : term262 = term263.
Proof. exact (@lem706885). Qed.
Lemma lem5398066 : (term262 = term263) = (term264 = term265).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term263). Qed.
Lemma lem5398067 : term264 = term265.
Proof. exact (EQ_MP (@lem5398066) (@lem5398065)). Qed.
Lemma lem5398068 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398069 : term261 = term256.
Proof. exact (MK_COMB (@lem5398068) (@lem5398067)). Qed.
Lemma lem5398070 : term253 = term256.
Proof. exact (TRANS (@lem5398064) (@lem5398069)). Qed.
Lemma lem5398071 : term260 = term256.
Proof. exact (TRANS (@lem5398063) (@lem5398070)). Qed.
Lemma lem5398072 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5398073 : term266 = term267.
Proof. exact (MK_COMB (@lem5398072) (@lem5398071)). Qed.
Lemma lem5398074 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem5398075 : term268 = term269.
Proof. exact (MK_COMB (@lem5398073) (@lem5398074)). Qed.
Lemma lem5398077 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398078 : term269 = term270.
Proof. exact (@lem5398077 term265 term18). Qed.
Lemma lem5398079 : term271 = term263.
Proof. exact (@lem996237 term263). Qed.
Lemma lem5398080 : (term271 = term263) = (term272 = term265).
Proof. exact (@lem1007663 term263 (BIT1 0) term263). Qed.
Lemma lem5398081 : term272 = term265.
Proof. exact (EQ_MP (@lem5398080) (@lem5398079)). Qed.
Lemma lem5398082 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398083 : term270 = term256.
Proof. exact (MK_COMB (@lem5398082) (@lem5398081)). Qed.
Lemma lem5398084 : term269 = term256.
Proof. exact (TRANS (@lem5398078) (@lem5398083)). Qed.
Lemma lem5398085 : term268 = term256.
Proof. exact (TRANS (@lem5398075) (@lem5398084)). Qed.
Lemma lem5398087 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398088 : term195 = term196.
Proof. exact (@lem5398087 term18 term18). Qed.
Lemma lem5398089 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398090 : term198 = term18.
Proof. exact (EQ_MP (@lem5398089) (@lem940073)). Qed.
Lemma lem5398091 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398092 : term196 = term142.
Proof. exact (MK_COMB (@lem5398091) (@lem5398090)). Qed.
Lemma lem5398093 : term195 = term142.
Proof. exact (TRANS (@lem5398088) (@lem5398092)). Qed.
Lemma lem5398094 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem5398095 : term273 = term269.
Proof. exact (MK_COMB (@lem5398094) (@lem5398093)). Qed.
Lemma lem5398097 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398098 : term269 = term270.
Proof. exact (@lem5398097 term265 term18). Qed.
Lemma lem5398099 : term271 = term263.
Proof. exact (@lem996237 term263). Qed.
Lemma lem5398100 : (term271 = term263) = (term272 = term265).
Proof. exact (@lem1007663 term263 (BIT1 0) term263). Qed.
Lemma lem5398101 : term272 = term265.
Proof. exact (EQ_MP (@lem5398100) (@lem5398099)). Qed.
Lemma lem5398102 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398103 : term270 = term256.
Proof. exact (MK_COMB (@lem5398102) (@lem5398101)). Qed.
Lemma lem5398104 : term269 = term256.
Proof. exact (TRANS (@lem5398098) (@lem5398103)). Qed.
Lemma lem5398105 : term273 = term256.
Proof. exact (TRANS (@lem5398095) (@lem5398104)). Qed.
Lemma lem5398106 : term256 = term273.
Proof. exact (SYM (@lem5398105)). Qed.
Lemma lem5398107 : term268 = term273.
Proof. exact (TRANS (@lem5398085) (@lem5398106)). Qed.
Lemma lem5398108 : term254 = term274.
Proof. exact (@lem5398044 (@lem5398107)). Qed.
Lemma lem5398109 : term253 = term274.
Proof. exact (TRANS (@lem5398010) (@lem5398108)). Qed.
Lemma lem5398111 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5398112 : term274 = term256.
Proof. exact (@lem5398111 term256). Qed.
Lemma lem5398113 : term253 = term256.
Proof. exact (TRANS (@lem5398109) (@lem5398112)). Qed.
Lemma lem5398114 (_69880 : int) : (term143 _69880) = (term143 _69880).
Proof. exact (eq_refl (term143 _69880)). Qed.
Lemma lem5398115 (_69880 : int) : (term252 _69880) = (term275 _69880).
Proof. exact (MK_COMB (@lem5398114 _69880) (@lem5398113)). Qed.
Lemma lem5398117 (_69880 : int) : (term155 _69880) = (term275 _69880).
Proof. exact (TRANS (@lem5398001 _69880) (@lem5398115 _69880)). Qed.
Lemma lem5398120 : term276 = term276.
Proof. exact (eq_refl term276). Qed.
Lemma lem5398121 (_69880 : int) : (term277 _69880) = (term278 _69880).
Proof. exact (MK_COMB (@lem5398120) (@lem5398117 _69880)). Qed.
Lemma lem5398122 (_69880 : int) : (term278 _69880) = (term279 _69880).
Proof. exact (@lem1982792 term142 (term275 _69880)). Qed.
Lemma lem5398123 (_69880 : int) : (term280 _69880) = (term281 _69880).
Proof. exact (@lem1982781 (real_of_int _69880) term186 term256). Qed.
Lemma lem5398125 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5398126 : term256 = term274.
Proof. exact (@lem5398125 term265). Qed.
Lemma lem5398128 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5398129 : term186 = term187.
Proof. exact (@lem5398128 term18). Qed.
Lemma lem5398130 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5398131 : term188 = term189.
Proof. exact (MK_COMB (@lem5398130) (@lem5398129)). Qed.
Lemma lem5398132 : term282 = term283.
Proof. exact (MK_COMB (@lem5398131) (@lem5398126)). Qed.
Lemma lem5398133 : term283 = term284.
Proof. exact (@lem1981613 term186 term256 term142 term142). Qed.
Lemma lem5398135 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398136 : term195 = term196.
Proof. exact (@lem5398135 term18 term18). Qed.
Lemma lem5398137 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398138 : term198 = term18.
Proof. exact (EQ_MP (@lem5398137) (@lem940073)). Qed.
Lemma lem5398139 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398140 : term196 = term142.
Proof. exact (MK_COMB (@lem5398139) (@lem5398138)). Qed.
Lemma lem5398141 : term195 = term142.
Proof. exact (TRANS (@lem5398136) (@lem5398140)). Qed.
Lemma lem5398143 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5398144 : term282 = term285.
Proof. exact (@lem5398143 term18 term265). Qed.
Lemma lem5398145 : term286 = term263.
Proof. exact (@lem996238 term263). Qed.
Lemma lem5398146 : (term286 = term263) = (term287 = term265).
Proof. exact (@lem1007663 (BIT1 0) term263 term263). Qed.
Lemma lem5398147 : term287 = term265.
Proof. exact (EQ_MP (@lem5398146) (@lem5398145)). Qed.
Lemma lem5398148 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398149 : term288 = term256.
Proof. exact (MK_COMB (@lem5398148) (@lem5398147)). Qed.
Lemma lem5398150 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5398151 : term285 = term289.
Proof. exact (MK_COMB (@lem5398150) (@lem5398149)). Qed.
Lemma lem5398152 : term282 = term289.
Proof. exact (TRANS (@lem5398144) (@lem5398151)). Qed.
Lemma lem5398153 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5398154 : term290 = term291.
Proof. exact (MK_COMB (@lem5398153) (@lem5398152)). Qed.
Lemma lem5398155 : term284 = term292.
Proof. exact (MK_COMB (@lem5398154) (@lem5398141)). Qed.
Lemma lem5398156 : term283 = term292.
Proof. exact (TRANS (@lem5398133) (@lem5398155)). Qed.
Lemma lem5398157 : term282 = term292.
Proof. exact (TRANS (@lem5398132) (@lem5398156)). Qed.
Lemma lem5398159 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5398160 : term292 = term289.
Proof. exact (@lem5398159 term289). Qed.
Lemma lem5398161 : term282 = term289.
Proof. exact (TRANS (@lem5398157) (@lem5398160)). Qed.
Lemma lem5398164 (_69880 : int) : (term220 _69880) = (term220 _69880).
Proof. exact (eq_refl (term220 _69880)). Qed.
Lemma lem5398165 (_69880 : int) : (term281 _69880) = (term293 _69880).
Proof. exact (MK_COMB (@lem5398164 _69880) (@lem5398161)). Qed.
Lemma lem5398166 (_69880 : int) : (term280 _69880) = (term293 _69880).
Proof. exact (TRANS (@lem5398123 _69880) (@lem5398165 _69880)). Qed.
Lemma lem5398167 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5398168 (_69880 : int) : (term279 _69880) = (term294 _69880).
Proof. exact (MK_COMB (@lem5398167) (@lem5398166 _69880)). Qed.
Lemma lem5398169 (_69880 : int) : (term294 _69880) = (term295 _69880).
Proof. exact (@lem1982757 (term224 _69880) term142 term289). Qed.
Lemma lem5398171 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5398172 : term289 = term292.
Proof. exact (@lem5398171 term265). Qed.
Lemma lem5398174 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5398175 : term142 = term211.
Proof. exact (@lem5398174 term18). Qed.
Lemma lem5398176 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5398177 : term227 = term228.
Proof. exact (MK_COMB (@lem5398176) (@lem5398175)). Qed.
Lemma lem5398178 : term296 = term297.
Proof. exact (MK_COMB (@lem5398177) (@lem5398172)). Qed.
Lemma lem5398179 : term298.
Proof. exact (@lem1981473 term142 term142 term289 term142 term186 term142). Qed.
Lemma lem5398181 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398182 : term233 = term234.
Proof. exact (@lem5398181 (NUMERAL 0) term18). Qed.
Lemma lem5398183 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398184 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398185 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398184 h1) (fun h1 : term234 = True => @lem5398183)). Qed.
Lemma lem5398186 : term234 = True.
Proof. exact (EQ_MP (@lem5398185) (@lem5398183)). Qed.
Lemma lem5398187 : term233 = True.
Proof. exact (TRANS (@lem5398182) (@lem5398186)). Qed.
Lemma lem5398188 : True = term233.
Proof. exact (SYM (@lem5398187)). Qed.
Lemma lem5398189 : term233.
Proof. exact (EQ_MP (@lem5398188) (@lem0)). Qed.
Lemma lem5398190 : term299.
Proof. exact (@lem5398179 (@lem5398189)). Qed.
Lemma lem5398192 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398193 : term233 = term234.
Proof. exact (@lem5398192 (NUMERAL 0) term18). Qed.
Lemma lem5398194 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398195 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398196 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398195 h1) (fun h1 : term234 = True => @lem5398194)). Qed.
Lemma lem5398197 : term234 = True.
Proof. exact (EQ_MP (@lem5398196) (@lem5398194)). Qed.
Lemma lem5398198 : term233 = True.
Proof. exact (TRANS (@lem5398193) (@lem5398197)). Qed.
Lemma lem5398199 : True = term233.
Proof. exact (SYM (@lem5398198)). Qed.
Lemma lem5398200 : term233.
Proof. exact (EQ_MP (@lem5398199) (@lem0)). Qed.
Lemma lem5398201 : term300.
Proof. exact (@lem5398190 (@lem5398200)). Qed.
Lemma lem5398203 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398204 : term233 = term234.
Proof. exact (@lem5398203 (NUMERAL 0) term18). Qed.
Lemma lem5398205 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398206 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398207 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398206 h1) (fun h1 : term234 = True => @lem5398205)). Qed.
Lemma lem5398208 : term234 = True.
Proof. exact (EQ_MP (@lem5398207) (@lem5398205)). Qed.
Lemma lem5398209 : term233 = True.
Proof. exact (TRANS (@lem5398204) (@lem5398208)). Qed.
Lemma lem5398210 : True = term233.
Proof. exact (SYM (@lem5398209)). Qed.
Lemma lem5398211 : term233.
Proof. exact (EQ_MP (@lem5398210) (@lem0)). Qed.
Lemma lem5398212 : term301.
Proof. exact (@lem5398201 (@lem5398211)). Qed.
Lemma lem5398214 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5398215 : term302 = term303.
Proof. exact (@lem5398214 term265 term18). Qed.
Lemma lem5398216 : term271 = term263.
Proof. exact (@lem996237 term263). Qed.
Lemma lem5398217 : (term271 = term263) = (term272 = term265).
Proof. exact (@lem1007663 term263 (BIT1 0) term263). Qed.
Lemma lem5398218 : term272 = term265.
Proof. exact (EQ_MP (@lem5398217) (@lem5398216)). Qed.
Lemma lem5398219 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398220 : term270 = term256.
Proof. exact (MK_COMB (@lem5398219) (@lem5398218)). Qed.
Lemma lem5398221 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5398222 : term303 = term289.
Proof. exact (MK_COMB (@lem5398221) (@lem5398220)). Qed.
Lemma lem5398223 : term302 = term289.
Proof. exact (TRANS (@lem5398215) (@lem5398222)). Qed.
Lemma lem5398225 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398226 : term195 = term196.
Proof. exact (@lem5398225 term18 term18). Qed.
Lemma lem5398227 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398228 : term198 = term18.
Proof. exact (EQ_MP (@lem5398227) (@lem940073)). Qed.
Lemma lem5398229 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398230 : term196 = term142.
Proof. exact (MK_COMB (@lem5398229) (@lem5398228)). Qed.
Lemma lem5398231 : term195 = term142.
Proof. exact (TRANS (@lem5398226) (@lem5398230)). Qed.
Lemma lem5398232 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5398233 : term239 = term227.
Proof. exact (MK_COMB (@lem5398232) (@lem5398231)). Qed.
Lemma lem5398234 : term304 = term296.
Proof. exact (MK_COMB (@lem5398233) (@lem5398223)). Qed.
Lemma lem5398237 : term305 = term186.
Proof. exact (@lem1367771 term18 term18). Qed.
Lemma lem5398238 : term262 = term263.
Proof. exact (@lem706885). Qed.
Lemma lem5398239 : (term262 = term263) = (term264 = term265).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term263). Qed.
Lemma lem5398240 : term264 = term265.
Proof. exact (EQ_MP (@lem5398239) (@lem5398238)). Qed.
Lemma lem5398241 : term265 = term264.
Proof. exact (SYM (@lem5398240)). Qed.
Lemma lem5398242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398243 : term256 = term261.
Proof. exact (MK_COMB (@lem5398242) (@lem5398241)). Qed.
Lemma lem5398244 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5398245 : term289 = term306.
Proof. exact (MK_COMB (@lem5398244) (@lem5398243)). Qed.
Lemma lem5398246 : term227 = term227.
Proof. exact (eq_refl term227). Qed.
Lemma lem5398247 : term296 = term305.
Proof. exact (MK_COMB (@lem5398246) (@lem5398245)). Qed.
Lemma lem5398248 : term296 = term186.
Proof. exact (TRANS (@lem5398247) (@lem5398237)). Qed.
Lemma lem5398249 : term304 = term186.
Proof. exact (TRANS (@lem5398234) (@lem5398248)). Qed.
Lemma lem5398250 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5398251 : term307 = term188.
Proof. exact (MK_COMB (@lem5398250) (@lem5398249)). Qed.
Lemma lem5398252 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem5398253 : term308 = term212.
Proof. exact (MK_COMB (@lem5398251) (@lem5398252)). Qed.
Lemma lem5398255 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5398256 : term212 = term217.
Proof. exact (@lem5398255 term18 term18). Qed.
Lemma lem5398257 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398258 : term198 = term18.
Proof. exact (EQ_MP (@lem5398257) (@lem940073)). Qed.
Lemma lem5398259 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398260 : term196 = term142.
Proof. exact (MK_COMB (@lem5398259) (@lem5398258)). Qed.
Lemma lem5398261 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5398262 : term217 = term186.
Proof. exact (MK_COMB (@lem5398261) (@lem5398260)). Qed.
Lemma lem5398263 : term212 = term186.
Proof. exact (TRANS (@lem5398256) (@lem5398262)). Qed.
Lemma lem5398264 : term308 = term186.
Proof. exact (TRANS (@lem5398253) (@lem5398263)). Qed.
Lemma lem5398266 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398267 : term195 = term196.
Proof. exact (@lem5398266 term18 term18). Qed.
Lemma lem5398268 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398269 : term198 = term18.
Proof. exact (EQ_MP (@lem5398268) (@lem940073)). Qed.
Lemma lem5398270 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398271 : term196 = term142.
Proof. exact (MK_COMB (@lem5398270) (@lem5398269)). Qed.
Lemma lem5398272 : term195 = term142.
Proof. exact (TRANS (@lem5398267) (@lem5398271)). Qed.
Lemma lem5398273 : term188 = term188.
Proof. exact (eq_refl term188). Qed.
Lemma lem5398274 : term309 = term212.
Proof. exact (MK_COMB (@lem5398273) (@lem5398272)). Qed.
Lemma lem5398276 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5398277 : term212 = term217.
Proof. exact (@lem5398276 term18 term18). Qed.
Lemma lem5398278 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398279 : term198 = term18.
Proof. exact (EQ_MP (@lem5398278) (@lem940073)). Qed.
Lemma lem5398280 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398281 : term196 = term142.
Proof. exact (MK_COMB (@lem5398280) (@lem5398279)). Qed.
Lemma lem5398282 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5398283 : term217 = term186.
Proof. exact (MK_COMB (@lem5398282) (@lem5398281)). Qed.
Lemma lem5398284 : term212 = term186.
Proof. exact (TRANS (@lem5398277) (@lem5398283)). Qed.
Lemma lem5398285 : term309 = term186.
Proof. exact (TRANS (@lem5398274) (@lem5398284)). Qed.
Lemma lem5398286 : term186 = term309.
Proof. exact (SYM (@lem5398285)). Qed.
Lemma lem5398287 : term308 = term309.
Proof. exact (TRANS (@lem5398264) (@lem5398286)). Qed.
Lemma lem5398288 : term297 = term187.
Proof. exact (@lem5398212 (@lem5398287)). Qed.
Lemma lem5398289 : term296 = term187.
Proof. exact (TRANS (@lem5398178) (@lem5398288)). Qed.
Lemma lem5398291 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5398292 : term187 = term186.
Proof. exact (@lem5398291 term186). Qed.
Lemma lem5398293 : term296 = term186.
Proof. exact (TRANS (@lem5398289) (@lem5398292)). Qed.
Lemma lem5398294 (_69880 : int) : (term220 _69880) = (term220 _69880).
Proof. exact (eq_refl (term220 _69880)). Qed.
Lemma lem5398295 (_69880 : int) : (term295 _69880) = (term221 _69880).
Proof. exact (MK_COMB (@lem5398294 _69880) (@lem5398293)). Qed.
Lemma lem5398296 (_69880 : int) : (term294 _69880) = (term221 _69880).
Proof. exact (TRANS (@lem5398169 _69880) (@lem5398295 _69880)). Qed.
Lemma lem5398297 (_69880 : int) : (term279 _69880) = (term221 _69880).
Proof. exact (TRANS (@lem5398168 _69880) (@lem5398296 _69880)). Qed.
Lemma lem5398298 (_69880 : int) : (term278 _69880) = (term221 _69880).
Proof. exact (TRANS (@lem5398122 _69880) (@lem5398297 _69880)). Qed.
Lemma lem5398299 (_69880 : int) : (term277 _69880) = (term221 _69880).
Proof. exact (TRANS (@lem5398121 _69880) (@lem5398298 _69880)). Qed.
Lemma lem5398300 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5398301 (_69880 : int) : (term310 _69880) = (term311 _69880).
Proof. exact (MK_COMB (@lem5398300) (@lem5398299 _69880)). Qed.
Lemma lem5398302 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5398303 (_69880 : int) : (term251 _69880) = (term312 _69880).
Proof. exact (MK_COMB (@lem5398301 _69880) (@lem5398302)). Qed.
Lemma lem5398304 (_69880 : int) : (term158 _69880) = (term312 _69880).
Proof. exact (TRANS (@lem5397989 _69880) (@lem5398303 _69880)). Qed.
Lemma lem5398305 (_69879 : int) : ((real_of_int _69879) = term133) = ((term180 _69879) = term133).
Proof. exact (@lem1988293 (real_of_int _69879) term133). Qed.
Lemma lem5398311 (_69879 : int) : (term180 _69879) = (term181 _69879).
Proof. exact (@lem1982792 (real_of_int _69879) term133). Qed.
Lemma lem5398313 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5398314 : term133 = term183.
Proof. exact (@lem5398313 (NUMERAL 0)). Qed.
Lemma lem5398316 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5398317 : term186 = term187.
Proof. exact (@lem5398316 term18). Qed.
Lemma lem5398318 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5398319 : term188 = term189.
Proof. exact (MK_COMB (@lem5398318) (@lem5398317)). Qed.
Lemma lem5398320 : term190 = term191.
Proof. exact (MK_COMB (@lem5398319) (@lem5398314)). Qed.
Lemma lem5398321 : term191 = term192.
Proof. exact (@lem1981613 term186 term133 term142 term142). Qed.
Lemma lem5398323 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398324 : term195 = term196.
Proof. exact (@lem5398323 term18 term18). Qed.
Lemma lem5398325 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398326 : term198 = term18.
Proof. exact (EQ_MP (@lem5398325) (@lem940073)). Qed.
Lemma lem5398327 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398328 : term196 = term142.
Proof. exact (MK_COMB (@lem5398327) (@lem5398326)). Qed.
Lemma lem5398329 : term195 = term142.
Proof. exact (TRANS (@lem5398324) (@lem5398328)). Qed.
Lemma lem5398331 (x : nat) : (term199 x) = term133.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5398332 : term190 = term133.
Proof. exact (@lem5398331 term18). Qed.
Lemma lem5398333 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5398334 : term200 = term201.
Proof. exact (MK_COMB (@lem5398333) (@lem5398332)). Qed.
Lemma lem5398335 : term192 = term183.
Proof. exact (MK_COMB (@lem5398334) (@lem5398329)). Qed.
Lemma lem5398336 : term191 = term183.
Proof. exact (TRANS (@lem5398321) (@lem5398335)). Qed.
Lemma lem5398337 : term190 = term183.
Proof. exact (TRANS (@lem5398320) (@lem5398336)). Qed.
Lemma lem5398339 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5398340 : term183 = term133.
Proof. exact (@lem5398339 term133). Qed.
Lemma lem5398341 : term190 = term133.
Proof. exact (TRANS (@lem5398337) (@lem5398340)). Qed.
Lemma lem5398342 (_69879 : int) : (term143 _69879) = (term143 _69879).
Proof. exact (eq_refl (term143 _69879)). Qed.
Lemma lem5398343 (_69879 : int) : (term181 _69879) = (term203 _69879).
Proof. exact (MK_COMB (@lem5398342 _69879) (@lem5398341)). Qed.
Lemma lem5398344 (_69879 : int) : (term203 _69879) = (real_of_int _69879).
Proof. exact (@lem1982723 (real_of_int _69879)). Qed.
Lemma lem5398345 (_69879 : int) : (term181 _69879) = (real_of_int _69879).
Proof. exact (TRANS (@lem5398343 _69879) (@lem5398344 _69879)). Qed.
Lemma lem5398347 (_69879 : int) : (term180 _69879) = (real_of_int _69879).
Proof. exact (TRANS (@lem5398311 _69879) (@lem5398345 _69879)). Qed.
Lemma lem5398348 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5398349 (_69879 : int) : (term313 _69879) = (term159 _69879).
Proof. exact (MK_COMB (@lem5398348) (@lem5398347 _69879)). Qed.
Lemma lem5398350 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5398351 (_69879 : int) : ((term180 _69879) = term133) = ((real_of_int _69879) = term133).
Proof. exact (MK_COMB (@lem5398349 _69879) (@lem5398350)). Qed.
Lemma lem5398352 (_69879 : int) : ((real_of_int _69879) = term133) = ((real_of_int _69879) = term133).
Proof. exact (TRANS (@lem5398305 _69879) (@lem5398351 _69879)). Qed.
Lemma lem5398353 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5398354 (_69880 : int) : (term160 _69880) = (term314 _69880).
Proof. exact (MK_COMB (@lem5398353) (@lem5398304 _69880)). Qed.
Lemma lem5398355 (_69880 : int) (_69879 : int) : (term161 _69880 _69879) = (term315 _69880 _69879).
Proof. exact (MK_COMB (@lem5398354 _69880) (@lem5398352 _69879)). Qed.
Lemma lem5398356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5398357 (_69879 : int) (_69880 : int) : (term162 _69880 _69879) = (term316 _69879 _69880).
Proof. exact (MK_COMB (@lem5398356) (@lem5397988 _69879 _69880)). Qed.
Lemma lem5398358 (_69880 : int) (_69879 : int) : (term163 _69880 _69879) = (term317 _69880 _69879).
Proof. exact (MK_COMB (@lem5398357 _69879 _69880) (@lem5398355 _69880 _69879)). Qed.
Lemma lem5398359 (_69880 : int) (_69879 : int) : (term168 _69879 _69880) = (term318 _69880 _69879).
Proof. exact (@lem1988287 (real_of_int _69880) (term144 _69879)). Qed.
Lemma lem5398371 (_69880 : int) (_69879 : int) : (term319 _69880 _69879) = (term320 _69880 _69879).
Proof. exact (@lem1982792 (real_of_int _69880) (term144 _69879)). Qed.
Lemma lem5398372 (_69879 : int) : (term209 _69879) = (term210 _69879).
Proof. exact (@lem1982781 (real_of_int _69879) term186 term142). Qed.
Lemma lem5398374 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5398375 : term142 = term211.
Proof. exact (@lem5398374 term18). Qed.
Lemma lem5398377 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5398378 : term186 = term187.
Proof. exact (@lem5398377 term18). Qed.
Lemma lem5398379 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5398380 : term188 = term189.
Proof. exact (MK_COMB (@lem5398379) (@lem5398378)). Qed.
Lemma lem5398381 : term212 = term213.
Proof. exact (MK_COMB (@lem5398380) (@lem5398375)). Qed.
Lemma lem5398382 : term213 = term214.
Proof. exact (@lem1981613 term186 term142 term142 term142). Qed.
Lemma lem5398384 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398385 : term195 = term196.
Proof. exact (@lem5398384 term18 term18). Qed.
Lemma lem5398386 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398387 : term198 = term18.
Proof. exact (EQ_MP (@lem5398386) (@lem940073)). Qed.
Lemma lem5398388 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398389 : term196 = term142.
Proof. exact (MK_COMB (@lem5398388) (@lem5398387)). Qed.
Lemma lem5398390 : term195 = term142.
Proof. exact (TRANS (@lem5398385) (@lem5398389)). Qed.
Lemma lem5398392 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5398393 : term212 = term217.
Proof. exact (@lem5398392 term18 term18). Qed.
Lemma lem5398394 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398395 : term198 = term18.
Proof. exact (EQ_MP (@lem5398394) (@lem940073)). Qed.
Lemma lem5398396 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398397 : term196 = term142.
Proof. exact (MK_COMB (@lem5398396) (@lem5398395)). Qed.
Lemma lem5398398 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5398399 : term217 = term186.
Proof. exact (MK_COMB (@lem5398398) (@lem5398397)). Qed.
Lemma lem5398400 : term212 = term186.
Proof. exact (TRANS (@lem5398393) (@lem5398399)). Qed.
Lemma lem5398401 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5398402 : term218 = term219.
Proof. exact (MK_COMB (@lem5398401) (@lem5398400)). Qed.
Lemma lem5398403 : term214 = term187.
Proof. exact (MK_COMB (@lem5398402) (@lem5398390)). Qed.
Lemma lem5398404 : term213 = term187.
Proof. exact (TRANS (@lem5398382) (@lem5398403)). Qed.
Lemma lem5398405 : term212 = term187.
Proof. exact (TRANS (@lem5398381) (@lem5398404)). Qed.
Lemma lem5398407 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5398408 : term187 = term186.
Proof. exact (@lem5398407 term186). Qed.
Lemma lem5398409 : term212 = term186.
Proof. exact (TRANS (@lem5398405) (@lem5398408)). Qed.
Lemma lem5398412 (_69879 : int) : (term220 _69879) = (term220 _69879).
Proof. exact (eq_refl (term220 _69879)). Qed.
Lemma lem5398413 (_69879 : int) : (term210 _69879) = (term221 _69879).
Proof. exact (MK_COMB (@lem5398412 _69879) (@lem5398409)). Qed.
Lemma lem5398414 (_69879 : int) : (term209 _69879) = (term221 _69879).
Proof. exact (TRANS (@lem5398372 _69879) (@lem5398413 _69879)). Qed.
Lemma lem5398415 (_69880 : int) : (term143 _69880) = (term143 _69880).
Proof. exact (eq_refl (term143 _69880)). Qed.
Lemma lem5398416 (_69880 : int) (_69879 : int) : (term320 _69880 _69879) = (term321 _69880 _69879).
Proof. exact (MK_COMB (@lem5398415 _69880) (@lem5398414 _69879)). Qed.
Lemma lem5398421 (_69879 : int) (_69880 : int) : (term321 _69880 _69879) = (term322 _69879 _69880).
Proof. exact (@lem1982757 (term224 _69879) (real_of_int _69880) term186). Qed.
Lemma lem5398422 (_69879 : int) (_69880 : int) : (term320 _69880 _69879) = (term322 _69879 _69880).
Proof. exact (TRANS (@lem5398416 _69880 _69879) (@lem5398421 _69879 _69880)). Qed.
Lemma lem5398424 (_69879 : int) (_69880 : int) : (term319 _69880 _69879) = (term322 _69879 _69880).
Proof. exact (TRANS (@lem5398371 _69880 _69879) (@lem5398422 _69879 _69880)). Qed.
Lemma lem5398425 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5398426 (_69879 : int) (_69880 : int) : (term323 _69880 _69879) = (term324 _69879 _69880).
Proof. exact (MK_COMB (@lem5398425) (@lem5398424 _69879 _69880)). Qed.
Lemma lem5398427 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5398428 (_69879 : int) (_69880 : int) : (term318 _69880 _69879) = (term325 _69879 _69880).
Proof. exact (MK_COMB (@lem5398426 _69879 _69880) (@lem5398427)). Qed.
Lemma lem5398429 (_69879 : int) (_69880 : int) : (term168 _69879 _69880) = (term325 _69879 _69880).
Proof. exact (TRANS (@lem5398359 _69880 _69879) (@lem5398428 _69879 _69880)). Qed.
Lemma lem5398430 (_69879 : int) (_69880 : int) : (term168 _69880 _69879) = (term318 _69879 _69880).
Proof. exact (@lem1988287 (real_of_int _69879) (term144 _69880)). Qed.
Lemma lem5398442 (_69879 : int) (_69880 : int) : (term319 _69879 _69880) = (term320 _69879 _69880).
Proof. exact (@lem1982792 (real_of_int _69879) (term144 _69880)). Qed.
Lemma lem5398443 (_69880 : int) : (term209 _69880) = (term210 _69880).
Proof. exact (@lem1982781 (real_of_int _69880) term186 term142). Qed.
Lemma lem5398445 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5398446 : term142 = term211.
Proof. exact (@lem5398445 term18). Qed.
Lemma lem5398448 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5398449 : term186 = term187.
Proof. exact (@lem5398448 term18). Qed.
Lemma lem5398450 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5398451 : term188 = term189.
Proof. exact (MK_COMB (@lem5398450) (@lem5398449)). Qed.
Lemma lem5398452 : term212 = term213.
Proof. exact (MK_COMB (@lem5398451) (@lem5398446)). Qed.
Lemma lem5398453 : term213 = term214.
Proof. exact (@lem1981613 term186 term142 term142 term142). Qed.
Lemma lem5398455 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398456 : term195 = term196.
Proof. exact (@lem5398455 term18 term18). Qed.
Lemma lem5398457 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398458 : term198 = term18.
Proof. exact (EQ_MP (@lem5398457) (@lem940073)). Qed.
Lemma lem5398459 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398460 : term196 = term142.
Proof. exact (MK_COMB (@lem5398459) (@lem5398458)). Qed.
Lemma lem5398461 : term195 = term142.
Proof. exact (TRANS (@lem5398456) (@lem5398460)). Qed.
Lemma lem5398463 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5398464 : term212 = term217.
Proof. exact (@lem5398463 term18 term18). Qed.
Lemma lem5398465 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398466 : term198 = term18.
Proof. exact (EQ_MP (@lem5398465) (@lem940073)). Qed.
Lemma lem5398467 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398468 : term196 = term142.
Proof. exact (MK_COMB (@lem5398467) (@lem5398466)). Qed.
Lemma lem5398469 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5398470 : term217 = term186.
Proof. exact (MK_COMB (@lem5398469) (@lem5398468)). Qed.
Lemma lem5398471 : term212 = term186.
Proof. exact (TRANS (@lem5398464) (@lem5398470)). Qed.
Lemma lem5398472 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5398473 : term218 = term219.
Proof. exact (MK_COMB (@lem5398472) (@lem5398471)). Qed.
Lemma lem5398474 : term214 = term187.
Proof. exact (MK_COMB (@lem5398473) (@lem5398461)). Qed.
Lemma lem5398475 : term213 = term187.
Proof. exact (TRANS (@lem5398453) (@lem5398474)). Qed.
Lemma lem5398476 : term212 = term187.
Proof. exact (TRANS (@lem5398452) (@lem5398475)). Qed.
Lemma lem5398478 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5398479 : term187 = term186.
Proof. exact (@lem5398478 term186). Qed.
Lemma lem5398480 : term212 = term186.
Proof. exact (TRANS (@lem5398476) (@lem5398479)). Qed.
Lemma lem5398483 (_69880 : int) : (term220 _69880) = (term220 _69880).
Proof. exact (eq_refl (term220 _69880)). Qed.
Lemma lem5398484 (_69880 : int) : (term210 _69880) = (term221 _69880).
Proof. exact (MK_COMB (@lem5398483 _69880) (@lem5398480)). Qed.
Lemma lem5398485 (_69880 : int) : (term209 _69880) = (term221 _69880).
Proof. exact (TRANS (@lem5398443 _69880) (@lem5398484 _69880)). Qed.
Lemma lem5398486 (_69879 : int) : (term143 _69879) = (term143 _69879).
Proof. exact (eq_refl (term143 _69879)). Qed.
Lemma lem5398489 (_69879 : int) (_69880 : int) : (term320 _69879 _69880) = (term321 _69879 _69880).
Proof. exact (MK_COMB (@lem5398486 _69879) (@lem5398485 _69880)). Qed.
Lemma lem5398491 (_69879 : int) (_69880 : int) : (term319 _69879 _69880) = (term321 _69879 _69880).
Proof. exact (TRANS (@lem5398442 _69879 _69880) (@lem5398489 _69879 _69880)). Qed.
Lemma lem5398492 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5398493 (_69879 : int) (_69880 : int) : (term323 _69879 _69880) = (term326 _69879 _69880).
Proof. exact (MK_COMB (@lem5398492) (@lem5398491 _69879 _69880)). Qed.
Lemma lem5398494 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5398495 (_69879 : int) (_69880 : int) : (term318 _69879 _69880) = (term327 _69879 _69880).
Proof. exact (MK_COMB (@lem5398493 _69879 _69880) (@lem5398494)). Qed.
Lemma lem5398496 (_69879 : int) (_69880 : int) : (term168 _69880 _69879) = (term327 _69879 _69880).
Proof. exact (TRANS (@lem5398430 _69879 _69880) (@lem5398495 _69879 _69880)). Qed.
Lemma lem5398497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5398498 (_69879 : int) (_69880 : int) : (term170 _69879 _69880) = (term328 _69879 _69880).
Proof. exact (MK_COMB (@lem5398497) (@lem5398429 _69879 _69880)). Qed.
Lemma lem5398499 (_69879 : int) (_69880 : int) : (term171 _69880 _69879) = (term329 _69879 _69880).
Proof. exact (MK_COMB (@lem5398498 _69879 _69880) (@lem5398496 _69879 _69880)). Qed.
Lemma lem5398500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5398501 (_69880 : int) (_69879 : int) : (term172 _69880 _69879) = (term330 _69880 _69879).
Proof. exact (MK_COMB (@lem5398500) (@lem5398358 _69880 _69879)). Qed.
Lemma lem5398502 (_69879 : int) (_69880 : int) : (term173 _69880 _69879) = (term331 _69879 _69880).
Proof. exact (MK_COMB (@lem5398501 _69880 _69879) (@lem5398499 _69879 _69880)). Qed.
Lemma lem5398503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5398504 (_69880 : int) : (term174 _69880) = (term332 _69880).
Proof. exact (MK_COMB (@lem5398503) (@lem5397808 _69880)). Qed.
Lemma lem5398505 (_69879 : int) (_69880 : int) : (term175 _69880 _69879) = (term333 _69879 _69880).
Proof. exact (MK_COMB (@lem5398504 _69880) (@lem5398502 _69879 _69880)). Qed.
Lemma lem5398506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5398507 (_69879 : int) : (term174 _69879) = (term332 _69879).
Proof. exact (MK_COMB (@lem5398506) (@lem5397760 _69879)). Qed.
Lemma lem5398508 (_69879 : int) (_69880 : int) : (term176 _69880 _69879) = (term334 _69879 _69880).
Proof. exact (MK_COMB (@lem5398507 _69879) (@lem5398505 _69879 _69880)). Qed.
Lemma lem5398515 (_69879 : int) (_69880 : int) : (term178 _69880 _69879) = (term334 _69879 _69880).
Proof. exact (TRANS (@lem5397712 _69880 _69879) (@lem5398508 _69879 _69880)). Qed.
Lemma lem5398535 (_69879 : int) (_69880 : int) : (term331 _69879 _69880) = (term335 _69879 _69880).
Proof. exact (@lem19158 (term325 _69879 _69880) (term317 _69880 _69879) (term327 _69879 _69880)). Qed.
Lemma lem5398542 (_69879 : int) (_69880 : int) : (term336 _69879 _69880) = (term337 _69879 _69880).
Proof. exact (@lem19367 ((term248 _69879 _69880) = term133) (term315 _69880 _69879) (term327 _69879 _69880)). Qed.
Lemma lem5398549 (_69879 : int) (_69880 : int) : (term338 _69879 _69880) = (term339 _69879 _69880).
Proof. exact (@lem19367 ((term248 _69879 _69880) = term133) (term315 _69880 _69879) (term325 _69879 _69880)). Qed.
Lemma lem5398550 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5398551 (_69879 : int) (_69880 : int) : (term340 _69879 _69880) = (term341 _69879 _69880).
Proof. exact (MK_COMB (@lem5398550) (@lem5398549 _69879 _69880)). Qed.
Lemma lem5398552 (_69879 : int) (_69880 : int) : (term335 _69879 _69880) = (term342 _69879 _69880).
Proof. exact (MK_COMB (@lem5398551 _69879 _69880) (@lem5398542 _69879 _69880)). Qed.
Lemma lem5398554 (_69879 : int) (_69880 : int) : (term331 _69879 _69880) = (term342 _69879 _69880).
Proof. exact (TRANS (@lem5398535 _69879 _69880) (@lem5398552 _69879 _69880)). Qed.
Lemma lem5398557 (_69880 : int) : (term332 _69880) = (term332 _69880).
Proof. exact (eq_refl (term332 _69880)). Qed.
Lemma lem5398558 (_69879 : int) (_69880 : int) : (term333 _69879 _69880) = (term343 _69879 _69880).
Proof. exact (MK_COMB (@lem5398557 _69880) (@lem5398554 _69879 _69880)). Qed.
Lemma lem5398559 (_69879 : int) (_69880 : int) : (term343 _69879 _69880) = (term344 _69879 _69880).
Proof. exact (@lem19158 (term339 _69879 _69880) (term206 _69880) (term337 _69879 _69880)). Qed.
Lemma lem5398566 (_69879 : int) (_69880 : int) : (term345 _69879 _69880) = (term346 _69879 _69880).
Proof. exact (@lem19158 (term347 _69879 _69880) (term206 _69880) (term348 _69879 _69880)). Qed.
Lemma lem5398573 (_69879 : int) (_69880 : int) : (term349 _69879 _69880) = (term350 _69879 _69880).
Proof. exact (@lem19158 (term351 _69879 _69880) (term206 _69880) (term352 _69879 _69880)). Qed.
Lemma lem5398574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5398575 (_69879 : int) (_69880 : int) : (term353 _69879 _69880) = (term354 _69879 _69880).
Proof. exact (MK_COMB (@lem5398574) (@lem5398573 _69879 _69880)). Qed.
Lemma lem5398576 (_69879 : int) (_69880 : int) : (term344 _69879 _69880) = (term355 _69879 _69880).
Proof. exact (MK_COMB (@lem5398575 _69879 _69880) (@lem5398566 _69879 _69880)). Qed.
Lemma lem5398577 (_69879 : int) (_69880 : int) : (term343 _69879 _69880) = (term355 _69879 _69880).
Proof. exact (TRANS (@lem5398559 _69879 _69880) (@lem5398576 _69879 _69880)). Qed.
Lemma lem5398578 (_69879 : int) (_69880 : int) : (term333 _69879 _69880) = (term355 _69879 _69880).
Proof. exact (TRANS (@lem5398558 _69879 _69880) (@lem5398577 _69879 _69880)). Qed.
Lemma lem5398581 (_69879 : int) : (term332 _69879) = (term332 _69879).
Proof. exact (eq_refl (term332 _69879)). Qed.
Lemma lem5398582 (_69879 : int) (_69880 : int) : (term334 _69879 _69880) = (term356 _69879 _69880).
Proof. exact (MK_COMB (@lem5398581 _69879) (@lem5398578 _69879 _69880)). Qed.
Lemma lem5398583 (_69879 : int) (_69880 : int) : (term356 _69879 _69880) = (term357 _69879 _69880).
Proof. exact (@lem19158 (term350 _69879 _69880) (term206 _69879) (term346 _69879 _69880)). Qed.
Lemma lem5398590 (_69879 : int) (_69880 : int) : (term358 _69879 _69880) = (term359 _69879 _69880).
Proof. exact (@lem19158 (term360 _69879 _69880) (term206 _69879) (term361 _69879 _69880)). Qed.
Lemma lem5398597 (_69879 : int) (_69880 : int) : (term362 _69879 _69880) = (term363 _69879 _69880).
Proof. exact (@lem19158 (term364 _69879 _69880) (term206 _69879) (term365 _69879 _69880)). Qed.
Lemma lem5398598 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5398599 (_69879 : int) (_69880 : int) : (term366 _69879 _69880) = (term367 _69879 _69880).
Proof. exact (MK_COMB (@lem5398598) (@lem5398597 _69879 _69880)). Qed.
Lemma lem5398600 (_69879 : int) (_69880 : int) : (term357 _69879 _69880) = (term368 _69879 _69880).
Proof. exact (MK_COMB (@lem5398599 _69879 _69880) (@lem5398590 _69879 _69880)). Qed.
Lemma lem5398601 (_69879 : int) (_69880 : int) : (term356 _69879 _69880) = (term368 _69879 _69880).
Proof. exact (TRANS (@lem5398583 _69879 _69880) (@lem5398600 _69879 _69880)). Qed.
Lemma lem5398602 (_69879 : int) (_69880 : int) : (term334 _69879 _69880) = (term368 _69879 _69880).
Proof. exact (TRANS (@lem5398582 _69879 _69880) (@lem5398601 _69879 _69880)). Qed.
Lemma lem5398603 (_69879 : int) (_69880 : int) : (term178 _69880 _69879) = (term368 _69879 _69880).
Proof. exact (TRANS (@lem5398515 _69879 _69880) (@lem5398602 _69879 _69880)). Qed.
Lemma lem5398625 (_69879 : int) (_69880 : int) (h1 : term368 _69879 _69880) : term368 _69879 _69880.
Proof. exact (h1). Qed.
Lemma lem5398626 (_69879 : int) (_69880 : int) (h1 : term363 _69879 _69880) : term363 _69879 _69880.
Proof. exact (h1). Qed.
Lemma lem5398627 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : term369 _69879 _69880.
Proof. exact (h1). Qed.
Lemma lem5398628 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : term364 _69879 _69880.
Proof. exact (proj2 (@lem5398627 _69879 _69880 h1)). Qed.
Lemma lem5398630 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : term351 _69879 _69880.
Proof. exact (proj2 (@lem5398628 _69879 _69880 h1)). Qed.
Lemma lem5398632 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : term325 _69879 _69880.
Proof. exact (proj2 (@lem5398630 _69879 _69880 h1)). Qed.
Lemma lem5398633 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : (term248 _69879 _69880) = term133.
Proof. exact (proj1 (@lem5398630 _69879 _69880 h1)). Qed.
Lemma lem5398635 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5398636 : term370 = term233.
Proof. exact (@lem5398635 term133 term142). Qed.
Lemma lem5398638 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5398639 : term142 = term211.
Proof. exact (@lem5398638 term18). Qed.
Lemma lem5398641 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5398642 : term133 = term183.
Proof. exact (@lem5398641 (NUMERAL 0)). Qed.
Lemma lem5398643 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5398644 : term371 = term372.
Proof. exact (MK_COMB (@lem5398643) (@lem5398642)). Qed.
Lemma lem5398645 : term233 = term373.
Proof. exact (MK_COMB (@lem5398644) (@lem5398639)). Qed.
Lemma lem5398646 : term374.
Proof. exact (@lem1980255 term133 term142 term142 term142). Qed.
Lemma lem5398648 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398649 : term233 = term234.
Proof. exact (@lem5398648 (NUMERAL 0) term18). Qed.
Lemma lem5398650 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398651 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398652 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398651 h1) (fun h1 : term234 = True => @lem5398650)). Qed.
Lemma lem5398653 : term234 = True.
Proof. exact (EQ_MP (@lem5398652) (@lem5398650)). Qed.
Lemma lem5398654 : term233 = True.
Proof. exact (TRANS (@lem5398649) (@lem5398653)). Qed.
Lemma lem5398655 : True = term233.
Proof. exact (SYM (@lem5398654)). Qed.
Lemma lem5398656 : term233.
Proof. exact (EQ_MP (@lem5398655) (@lem0)). Qed.
Lemma lem5398657 : term375.
Proof. exact (@lem5398646 (@lem5398656)). Qed.
Lemma lem5398659 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398660 : term233 = term234.
Proof. exact (@lem5398659 (NUMERAL 0) term18). Qed.
Lemma lem5398661 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398662 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398663 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398662 h1) (fun h1 : term234 = True => @lem5398661)). Qed.
Lemma lem5398664 : term234 = True.
Proof. exact (EQ_MP (@lem5398663) (@lem5398661)). Qed.
Lemma lem5398665 : term233 = True.
Proof. exact (TRANS (@lem5398660) (@lem5398664)). Qed.
Lemma lem5398666 : True = term233.
Proof. exact (SYM (@lem5398665)). Qed.
Lemma lem5398667 : term233.
Proof. exact (EQ_MP (@lem5398666) (@lem0)). Qed.
Lemma lem5398668 : term373 = term376.
Proof. exact (@lem5398657 (@lem5398667)). Qed.
Lemma lem5398670 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398671 : term195 = term196.
Proof. exact (@lem5398670 term18 term18). Qed.
Lemma lem5398672 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398673 : term198 = term18.
Proof. exact (EQ_MP (@lem5398672) (@lem940073)). Qed.
Lemma lem5398674 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398675 : term196 = term142.
Proof. exact (MK_COMB (@lem5398674) (@lem5398673)). Qed.
Lemma lem5398676 : term195 = term142.
Proof. exact (TRANS (@lem5398671) (@lem5398675)). Qed.
Lemma lem5398678 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5398679 : term245 = term133.
Proof. exact (@lem5398678 term18). Qed.
Lemma lem5398680 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5398681 : term377 = term371.
Proof. exact (MK_COMB (@lem5398680) (@lem5398679)). Qed.
Lemma lem5398682 : term376 = term233.
Proof. exact (MK_COMB (@lem5398681) (@lem5398676)). Qed.
Lemma lem5398684 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398685 : term233 = term234.
Proof. exact (@lem5398684 (NUMERAL 0) term18). Qed.
Lemma lem5398686 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398687 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398688 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398687 h1) (fun h1 : term234 = True => @lem5398686)). Qed.
Lemma lem5398689 : term234 = True.
Proof. exact (EQ_MP (@lem5398688) (@lem5398686)). Qed.
Lemma lem5398690 : term233 = True.
Proof. exact (TRANS (@lem5398685) (@lem5398689)). Qed.
Lemma lem5398691 : term376 = True.
Proof. exact (TRANS (@lem5398682) (@lem5398690)). Qed.
Lemma lem5398692 : term373 = True.
Proof. exact (TRANS (@lem5398668) (@lem5398691)). Qed.
Lemma lem5398693 : term233 = True.
Proof. exact (TRANS (@lem5398645) (@lem5398692)). Qed.
Lemma lem5398694 : term370 = True.
Proof. exact (TRANS (@lem5398636) (@lem5398693)). Qed.
Lemma lem5398695 : True = term370.
Proof. exact (SYM (@lem5398694)). Qed.
Lemma lem5398696 : term370.
Proof. exact (EQ_MP (@lem5398695) (@lem0)). Qed.
Lemma lem5398697 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : term378 _69879 _69880.
Proof. exact (conj (@lem5398696) (@lem5398632 _69879 _69880 h1)). Qed.
Lemma lem5398699 (x : real) (y : real) : term379 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5398700 (_69879 : int) (_69880 : int) : term380 _69879 _69880.
Proof. exact (@lem5398699 term142 (term322 _69879 _69880)). Qed.
Lemma lem5398701 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : term381 _69879 _69880.
Proof. exact (@lem5398700 _69879 _69880 (@lem5398697 _69879 _69880 h1)). Qed.
Lemma lem5398702 (_69879 : int) (_69880 : int) : (term382 _69879 _69880) = (term322 _69879 _69880).
Proof. exact (@lem1982733 (term322 _69879 _69880)). Qed.
Lemma lem5398703 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5398704 (_69879 : int) (_69880 : int) : (term383 _69879 _69880) = (term324 _69879 _69880).
Proof. exact (MK_COMB (@lem5398703) (@lem5398702 _69879 _69880)). Qed.
Lemma lem5398705 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5398706 (_69879 : int) (_69880 : int) : (term381 _69879 _69880) = (term325 _69879 _69880).
Proof. exact (MK_COMB (@lem5398704 _69879 _69880) (@lem5398705)). Qed.
Lemma lem5398707 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : term325 _69879 _69880.
Proof. exact (EQ_MP (@lem5398706 _69879 _69880) (@lem5398701 _69879 _69880 h1)). Qed.
Lemma lem5398709 (y : real) : term384 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5398710 (_69879 : int) (_69880 : int) : term385 _69879 _69880.
Proof. exact (@lem5398709 (term248 _69879 _69880)). Qed.
Lemma lem5398711 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : term386 _69879 _69880.
Proof. exact (@lem5398710 _69879 _69880 (@lem5398633 _69879 _69880 h1)). Qed.
Lemma lem5398712 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : term387 _69879 _69880.
Proof. exact (@lem5398711 _69879 _69880 h1 term186). Qed.
Lemma lem5398713 (_69879 : int) (_69880 : int) : (term387 _69879 _69880) = ((term388 _69879 _69880) = term133).
Proof. exact (eq_refl (term387 _69879 _69880)). Qed.
Lemma lem5398714 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : (term388 _69879 _69880) = term133.
Proof. exact (EQ_MP (@lem5398713 _69879 _69880) (@lem5398712 _69879 _69880 h1)). Qed.
Lemma lem5398715 (_69879 : int) (_69880 : int) : (term388 _69879 _69880) = (term389 _69879 _69880).
Proof. exact (@lem1982781 (term224 _69879) term186 (real_of_int _69880)). Qed.
Lemma lem5398716 (_69880 : int) : (term224 _69880) = (term224 _69880).
Proof. exact (eq_refl (term224 _69880)). Qed.
Lemma lem5398717 (_69879 : int) : (term390 _69879) = (term391 _69879).
Proof. exact (@lem1982749 term186 term186 (real_of_int _69879)). Qed.
Lemma lem5398719 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5398720 : term186 = term187.
Proof. exact (@lem5398719 term18). Qed.
Lemma lem5398722 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5398723 : term186 = term187.
Proof. exact (@lem5398722 term18). Qed.
Lemma lem5398724 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5398725 : term188 = term189.
Proof. exact (MK_COMB (@lem5398724) (@lem5398723)). Qed.
Lemma lem5398726 : term392 = term393.
Proof. exact (MK_COMB (@lem5398725) (@lem5398720)). Qed.
Lemma lem5398727 : term393 = term394.
Proof. exact (@lem1981613 term186 term186 term142 term142). Qed.
Lemma lem5398729 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398730 : term195 = term196.
Proof. exact (@lem5398729 term18 term18). Qed.
Lemma lem5398731 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398732 : term198 = term18.
Proof. exact (EQ_MP (@lem5398731) (@lem940073)). Qed.
Lemma lem5398733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398734 : term196 = term142.
Proof. exact (MK_COMB (@lem5398733) (@lem5398732)). Qed.
Lemma lem5398735 : term195 = term142.
Proof. exact (TRANS (@lem5398730) (@lem5398734)). Qed.
Lemma lem5398737 (m : nat) (n : nat) : (term395 m n) = (term194 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5398738 : term392 = term196.
Proof. exact (@lem5398737 term18 term18). Qed.
Lemma lem5398739 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398740 : term198 = term18.
Proof. exact (EQ_MP (@lem5398739) (@lem940073)). Qed.
Lemma lem5398741 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398742 : term196 = term142.
Proof. exact (MK_COMB (@lem5398741) (@lem5398740)). Qed.
Lemma lem5398743 : term392 = term142.
Proof. exact (TRANS (@lem5398738) (@lem5398742)). Qed.
Lemma lem5398744 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5398745 : term396 = term397.
Proof. exact (MK_COMB (@lem5398744) (@lem5398743)). Qed.
Lemma lem5398746 : term394 = term211.
Proof. exact (MK_COMB (@lem5398745) (@lem5398735)). Qed.
Lemma lem5398747 : term393 = term211.
Proof. exact (TRANS (@lem5398727) (@lem5398746)). Qed.
Lemma lem5398748 : term392 = term211.
Proof. exact (TRANS (@lem5398726) (@lem5398747)). Qed.
Lemma lem5398750 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5398751 : term211 = term142.
Proof. exact (@lem5398750 term142). Qed.
Lemma lem5398752 : term392 = term142.
Proof. exact (TRANS (@lem5398748) (@lem5398751)). Qed.
Lemma lem5398753 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5398754 : term398 = term399.
Proof. exact (MK_COMB (@lem5398753) (@lem5398752)). Qed.
Lemma lem5398755 (_69879 : int) : (real_of_int _69879) = (real_of_int _69879).
Proof. exact (eq_refl (real_of_int _69879)). Qed.
Lemma lem5398756 (_69879 : int) : (term391 _69879) = (term400 _69879).
Proof. exact (MK_COMB (@lem5398754) (@lem5398755 _69879)). Qed.
Lemma lem5398757 (_69879 : int) : (term390 _69879) = (term400 _69879).
Proof. exact (TRANS (@lem5398717 _69879) (@lem5398756 _69879)). Qed.
Lemma lem5398758 (_69879 : int) : (term400 _69879) = (real_of_int _69879).
Proof. exact (@lem1982709 (real_of_int _69879)). Qed.
Lemma lem5398759 (_69879 : int) : (term390 _69879) = (real_of_int _69879).
Proof. exact (TRANS (@lem5398757 _69879) (@lem5398758 _69879)). Qed.
Lemma lem5398760 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5398761 (_69879 : int) : (term401 _69879) = (term143 _69879).
Proof. exact (MK_COMB (@lem5398760) (@lem5398759 _69879)). Qed.
Lemma lem5398762 (_69879 : int) (_69880 : int) : (term389 _69879 _69880) = (term402 _69879 _69880).
Proof. exact (MK_COMB (@lem5398761 _69879) (@lem5398716 _69880)). Qed.
Lemma lem5398763 (_69879 : int) (_69880 : int) : (term388 _69879 _69880) = (term402 _69879 _69880).
Proof. exact (TRANS (@lem5398715 _69879 _69880) (@lem5398762 _69879 _69880)). Qed.
Lemma lem5398764 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5398765 (_69879 : int) (_69880 : int) : (term403 _69879 _69880) = (term404 _69879 _69880).
Proof. exact (MK_COMB (@lem5398764) (@lem5398763 _69879 _69880)). Qed.
Lemma lem5398766 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5398767 (_69879 : int) (_69880 : int) : ((term388 _69879 _69880) = term133) = ((term402 _69879 _69880) = term133).
Proof. exact (MK_COMB (@lem5398765 _69879 _69880) (@lem5398766)). Qed.
Lemma lem5398768 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : (term402 _69879 _69880) = term133.
Proof. exact (EQ_MP (@lem5398767 _69879 _69880) (@lem5398714 _69879 _69880 h1)). Qed.
Lemma lem5398769 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : term405 _69879 _69880.
Proof. exact (conj (@lem5398768 _69879 _69880 h1) (@lem5398707 _69879 _69880 h1)). Qed.
Lemma lem5398771 (x : real) (y : real) : term406 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5398772 (_69879 : int) (_69880 : int) : term407 _69879 _69880.
Proof. exact (@lem5398771 (term402 _69879 _69880) (term322 _69879 _69880)). Qed.
Lemma lem5398773 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : term408 _69879 _69880.
Proof. exact (@lem5398772 _69879 _69880 (@lem5398769 _69879 _69880 h1)). Qed.
Lemma lem5398774 (_69879 : int) (_69880 : int) : (term409 _69879 _69880) = (term410 _69879 _69880).
Proof. exact (@lem1982753 (real_of_int _69879) (term224 _69879) (term224 _69880) (term411 _69880)). Qed.
Lemma lem5398775 (_69879 : int) : (term412 _69879) = (term413 _69879).
Proof. exact (@lem1982715 term186 (real_of_int _69879)). Qed.
Lemma lem5398777 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5398778 : term142 = term211.
Proof. exact (@lem5398777 term18). Qed.
Lemma lem5398780 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5398781 : term186 = term187.
Proof. exact (@lem5398780 term18). Qed.
Lemma lem5398782 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5398783 : term414 = term415.
Proof. exact (MK_COMB (@lem5398782) (@lem5398781)). Qed.
Lemma lem5398784 : term416 = term417.
Proof. exact (MK_COMB (@lem5398783) (@lem5398778)). Qed.
Lemma lem5398785 : term418.
Proof. exact (@lem1981473 term186 term142 term142 term142 term133 term142). Qed.
Lemma lem5398787 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398788 : term233 = term234.
Proof. exact (@lem5398787 (NUMERAL 0) term18). Qed.
Lemma lem5398789 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398790 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398791 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398790 h1) (fun h1 : term234 = True => @lem5398789)). Qed.
Lemma lem5398792 : term234 = True.
Proof. exact (EQ_MP (@lem5398791) (@lem5398789)). Qed.
Lemma lem5398793 : term233 = True.
Proof. exact (TRANS (@lem5398788) (@lem5398792)). Qed.
Lemma lem5398794 : True = term233.
Proof. exact (SYM (@lem5398793)). Qed.
Lemma lem5398795 : term233.
Proof. exact (EQ_MP (@lem5398794) (@lem0)). Qed.
Lemma lem5398796 : term419.
Proof. exact (@lem5398785 (@lem5398795)). Qed.
Lemma lem5398798 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398799 : term233 = term234.
Proof. exact (@lem5398798 (NUMERAL 0) term18). Qed.
Lemma lem5398800 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398801 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398802 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398801 h1) (fun h1 : term234 = True => @lem5398800)). Qed.
Lemma lem5398803 : term234 = True.
Proof. exact (EQ_MP (@lem5398802) (@lem5398800)). Qed.
Lemma lem5398804 : term233 = True.
Proof. exact (TRANS (@lem5398799) (@lem5398803)). Qed.
Lemma lem5398805 : True = term233.
Proof. exact (SYM (@lem5398804)). Qed.
Lemma lem5398806 : term233.
Proof. exact (EQ_MP (@lem5398805) (@lem0)). Qed.
Lemma lem5398807 : term420.
Proof. exact (@lem5398796 (@lem5398806)). Qed.
Lemma lem5398809 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398810 : term233 = term234.
Proof. exact (@lem5398809 (NUMERAL 0) term18). Qed.
Lemma lem5398811 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398812 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398813 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398812 h1) (fun h1 : term234 = True => @lem5398811)). Qed.
Lemma lem5398814 : term234 = True.
Proof. exact (EQ_MP (@lem5398813) (@lem5398811)). Qed.
Lemma lem5398815 : term233 = True.
Proof. exact (TRANS (@lem5398810) (@lem5398814)). Qed.
Lemma lem5398816 : True = term233.
Proof. exact (SYM (@lem5398815)). Qed.
Lemma lem5398817 : term233.
Proof. exact (EQ_MP (@lem5398816) (@lem0)). Qed.
Lemma lem5398818 : term421.
Proof. exact (@lem5398807 (@lem5398817)). Qed.
Lemma lem5398820 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398821 : term195 = term196.
Proof. exact (@lem5398820 term18 term18). Qed.
Lemma lem5398822 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398823 : term198 = term18.
Proof. exact (EQ_MP (@lem5398822) (@lem940073)). Qed.
Lemma lem5398824 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398825 : term196 = term142.
Proof. exact (MK_COMB (@lem5398824) (@lem5398823)). Qed.
Lemma lem5398826 : term195 = term142.
Proof. exact (TRANS (@lem5398821) (@lem5398825)). Qed.
Lemma lem5398828 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5398829 : term212 = term217.
Proof. exact (@lem5398828 term18 term18). Qed.
Lemma lem5398830 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398831 : term198 = term18.
Proof. exact (EQ_MP (@lem5398830) (@lem940073)). Qed.
Lemma lem5398832 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398833 : term196 = term142.
Proof. exact (MK_COMB (@lem5398832) (@lem5398831)). Qed.
Lemma lem5398834 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5398835 : term217 = term186.
Proof. exact (MK_COMB (@lem5398834) (@lem5398833)). Qed.
Lemma lem5398836 : term212 = term186.
Proof. exact (TRANS (@lem5398829) (@lem5398835)). Qed.
Lemma lem5398837 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5398838 : term422 = term414.
Proof. exact (MK_COMB (@lem5398837) (@lem5398836)). Qed.
Lemma lem5398839 : term423 = term416.
Proof. exact (MK_COMB (@lem5398838) (@lem5398826)). Qed.
Lemma lem5398841 (m : nat) : (term424 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5398842 : term416 = term133.
Proof. exact (@lem5398841 term18). Qed.
Lemma lem5398843 : term423 = term133.
Proof. exact (TRANS (@lem5398839) (@lem5398842)). Qed.
Lemma lem5398844 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5398845 : term425 = term243.
Proof. exact (MK_COMB (@lem5398844) (@lem5398843)). Qed.
Lemma lem5398846 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem5398847 : term426 = term245.
Proof. exact (MK_COMB (@lem5398845) (@lem5398846)). Qed.
Lemma lem5398849 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5398850 : term245 = term133.
Proof. exact (@lem5398849 term18). Qed.
Lemma lem5398851 : term426 = term133.
Proof. exact (TRANS (@lem5398847) (@lem5398850)). Qed.
Lemma lem5398853 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398854 : term195 = term196.
Proof. exact (@lem5398853 term18 term18). Qed.
Lemma lem5398855 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398856 : term198 = term18.
Proof. exact (EQ_MP (@lem5398855) (@lem940073)). Qed.
Lemma lem5398857 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398858 : term196 = term142.
Proof. exact (MK_COMB (@lem5398857) (@lem5398856)). Qed.
Lemma lem5398859 : term195 = term142.
Proof. exact (TRANS (@lem5398854) (@lem5398858)). Qed.
Lemma lem5398860 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem5398861 : term247 = term245.
Proof. exact (MK_COMB (@lem5398860) (@lem5398859)). Qed.
Lemma lem5398863 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5398864 : term245 = term133.
Proof. exact (@lem5398863 term18). Qed.
Lemma lem5398865 : term247 = term133.
Proof. exact (TRANS (@lem5398861) (@lem5398864)). Qed.
Lemma lem5398866 : term133 = term247.
Proof. exact (SYM (@lem5398865)). Qed.
Lemma lem5398867 : term426 = term247.
Proof. exact (TRANS (@lem5398851) (@lem5398866)). Qed.
Lemma lem5398868 : term417 = term183.
Proof. exact (@lem5398818 (@lem5398867)). Qed.
Lemma lem5398869 : term416 = term183.
Proof. exact (TRANS (@lem5398784) (@lem5398868)). Qed.
Lemma lem5398871 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5398872 : term183 = term133.
Proof. exact (@lem5398871 term133). Qed.
Lemma lem5398873 : term416 = term133.
Proof. exact (TRANS (@lem5398869) (@lem5398872)). Qed.
Lemma lem5398874 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5398875 : term427 = term243.
Proof. exact (MK_COMB (@lem5398874) (@lem5398873)). Qed.
Lemma lem5398876 (_69879 : int) : (real_of_int _69879) = (real_of_int _69879).
Proof. exact (eq_refl (real_of_int _69879)). Qed.
Lemma lem5398877 (_69879 : int) : (term413 _69879) = (term428 _69879).
Proof. exact (MK_COMB (@lem5398875) (@lem5398876 _69879)). Qed.
Lemma lem5398878 (_69879 : int) : (term412 _69879) = (term428 _69879).
Proof. exact (TRANS (@lem5398775 _69879) (@lem5398877 _69879)). Qed.
Lemma lem5398879 (_69879 : int) : (term428 _69879) = term133.
Proof. exact (@lem1982719 (real_of_int _69879)). Qed.
Lemma lem5398880 (_69879 : int) : (term412 _69879) = term133.
Proof. exact (TRANS (@lem5398878 _69879) (@lem5398879 _69879)). Qed.
Lemma lem5398881 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5398882 (_69879 : int) : (term429 _69879) = term430.
Proof. exact (MK_COMB (@lem5398881) (@lem5398880 _69879)). Qed.
Lemma lem5398883 (_69880 : int) : (term431 _69880) = (term432 _69880).
Proof. exact (@lem1982763 (term224 _69880) (real_of_int _69880) term186). Qed.
Lemma lem5398884 (_69880 : int) : (term433 _69880) = (term413 _69880).
Proof. exact (@lem1982713 term186 (real_of_int _69880)). Qed.
Lemma lem5398886 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5398887 : term142 = term211.
Proof. exact (@lem5398886 term18). Qed.
Lemma lem5398889 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5398890 : term186 = term187.
Proof. exact (@lem5398889 term18). Qed.
Lemma lem5398891 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5398892 : term414 = term415.
Proof. exact (MK_COMB (@lem5398891) (@lem5398890)). Qed.
Lemma lem5398893 : term416 = term417.
Proof. exact (MK_COMB (@lem5398892) (@lem5398887)). Qed.
Lemma lem5398894 : term418.
Proof. exact (@lem1981473 term186 term142 term142 term142 term133 term142). Qed.
Lemma lem5398896 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398897 : term233 = term234.
Proof. exact (@lem5398896 (NUMERAL 0) term18). Qed.
Lemma lem5398898 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398899 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398900 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398899 h1) (fun h1 : term234 = True => @lem5398898)). Qed.
Lemma lem5398901 : term234 = True.
Proof. exact (EQ_MP (@lem5398900) (@lem5398898)). Qed.
Lemma lem5398902 : term233 = True.
Proof. exact (TRANS (@lem5398897) (@lem5398901)). Qed.
Lemma lem5398903 : True = term233.
Proof. exact (SYM (@lem5398902)). Qed.
Lemma lem5398904 : term233.
Proof. exact (EQ_MP (@lem5398903) (@lem0)). Qed.
Lemma lem5398905 : term419.
Proof. exact (@lem5398894 (@lem5398904)). Qed.
Lemma lem5398907 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398908 : term233 = term234.
Proof. exact (@lem5398907 (NUMERAL 0) term18). Qed.
Lemma lem5398909 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398910 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398911 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398910 h1) (fun h1 : term234 = True => @lem5398909)). Qed.
Lemma lem5398912 : term234 = True.
Proof. exact (EQ_MP (@lem5398911) (@lem5398909)). Qed.
Lemma lem5398913 : term233 = True.
Proof. exact (TRANS (@lem5398908) (@lem5398912)). Qed.
Lemma lem5398914 : True = term233.
Proof. exact (SYM (@lem5398913)). Qed.
Lemma lem5398915 : term233.
Proof. exact (EQ_MP (@lem5398914) (@lem0)). Qed.
Lemma lem5398916 : term420.
Proof. exact (@lem5398905 (@lem5398915)). Qed.
Lemma lem5398918 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5398919 : term233 = term234.
Proof. exact (@lem5398918 (NUMERAL 0) term18). Qed.
Lemma lem5398920 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5398921 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5398922 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5398921 h1) (fun h1 : term234 = True => @lem5398920)). Qed.
Lemma lem5398923 : term234 = True.
Proof. exact (EQ_MP (@lem5398922) (@lem5398920)). Qed.
Lemma lem5398924 : term233 = True.
Proof. exact (TRANS (@lem5398919) (@lem5398923)). Qed.
Lemma lem5398925 : True = term233.
Proof. exact (SYM (@lem5398924)). Qed.
Lemma lem5398926 : term233.
Proof. exact (EQ_MP (@lem5398925) (@lem0)). Qed.
Lemma lem5398927 : term421.
Proof. exact (@lem5398916 (@lem5398926)). Qed.
Lemma lem5398929 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398930 : term195 = term196.
Proof. exact (@lem5398929 term18 term18). Qed.
Lemma lem5398931 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398932 : term198 = term18.
Proof. exact (EQ_MP (@lem5398931) (@lem940073)). Qed.
Lemma lem5398933 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398934 : term196 = term142.
Proof. exact (MK_COMB (@lem5398933) (@lem5398932)). Qed.
Lemma lem5398935 : term195 = term142.
Proof. exact (TRANS (@lem5398930) (@lem5398934)). Qed.
Lemma lem5398937 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5398938 : term212 = term217.
Proof. exact (@lem5398937 term18 term18). Qed.
Lemma lem5398939 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398940 : term198 = term18.
Proof. exact (EQ_MP (@lem5398939) (@lem940073)). Qed.
Lemma lem5398941 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398942 : term196 = term142.
Proof. exact (MK_COMB (@lem5398941) (@lem5398940)). Qed.
Lemma lem5398943 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5398944 : term217 = term186.
Proof. exact (MK_COMB (@lem5398943) (@lem5398942)). Qed.
Lemma lem5398945 : term212 = term186.
Proof. exact (TRANS (@lem5398938) (@lem5398944)). Qed.
Lemma lem5398946 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5398947 : term422 = term414.
Proof. exact (MK_COMB (@lem5398946) (@lem5398945)). Qed.
Lemma lem5398948 : term423 = term416.
Proof. exact (MK_COMB (@lem5398947) (@lem5398935)). Qed.
Lemma lem5398950 (m : nat) : (term424 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5398951 : term416 = term133.
Proof. exact (@lem5398950 term18). Qed.
Lemma lem5398952 : term423 = term133.
Proof. exact (TRANS (@lem5398948) (@lem5398951)). Qed.
Lemma lem5398953 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5398954 : term425 = term243.
Proof. exact (MK_COMB (@lem5398953) (@lem5398952)). Qed.
Lemma lem5398955 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem5398956 : term426 = term245.
Proof. exact (MK_COMB (@lem5398954) (@lem5398955)). Qed.
Lemma lem5398958 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5398959 : term245 = term133.
Proof. exact (@lem5398958 term18). Qed.
Lemma lem5398960 : term426 = term133.
Proof. exact (TRANS (@lem5398956) (@lem5398959)). Qed.
Lemma lem5398962 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5398963 : term195 = term196.
Proof. exact (@lem5398962 term18 term18). Qed.
Lemma lem5398964 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5398965 : term198 = term18.
Proof. exact (EQ_MP (@lem5398964) (@lem940073)). Qed.
Lemma lem5398966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5398967 : term196 = term142.
Proof. exact (MK_COMB (@lem5398966) (@lem5398965)). Qed.
Lemma lem5398968 : term195 = term142.
Proof. exact (TRANS (@lem5398963) (@lem5398967)). Qed.
Lemma lem5398969 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem5398970 : term247 = term245.
Proof. exact (MK_COMB (@lem5398969) (@lem5398968)). Qed.
Lemma lem5398972 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5398973 : term245 = term133.
Proof. exact (@lem5398972 term18). Qed.
Lemma lem5398974 : term247 = term133.
Proof. exact (TRANS (@lem5398970) (@lem5398973)). Qed.
Lemma lem5398975 : term133 = term247.
Proof. exact (SYM (@lem5398974)). Qed.
Lemma lem5398976 : term426 = term247.
Proof. exact (TRANS (@lem5398960) (@lem5398975)). Qed.
Lemma lem5398977 : term417 = term183.
Proof. exact (@lem5398927 (@lem5398976)). Qed.
Lemma lem5398978 : term416 = term183.
Proof. exact (TRANS (@lem5398893) (@lem5398977)). Qed.
Lemma lem5398980 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5398981 : term183 = term133.
Proof. exact (@lem5398980 term133). Qed.
Lemma lem5398982 : term416 = term133.
Proof. exact (TRANS (@lem5398978) (@lem5398981)). Qed.
Lemma lem5398983 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5398984 : term427 = term243.
Proof. exact (MK_COMB (@lem5398983) (@lem5398982)). Qed.
Lemma lem5398985 (_69880 : int) : (real_of_int _69880) = (real_of_int _69880).
Proof. exact (eq_refl (real_of_int _69880)). Qed.
Lemma lem5398986 (_69880 : int) : (term413 _69880) = (term428 _69880).
Proof. exact (MK_COMB (@lem5398984) (@lem5398985 _69880)). Qed.
Lemma lem5398987 (_69880 : int) : (term433 _69880) = (term428 _69880).
Proof. exact (TRANS (@lem5398884 _69880) (@lem5398986 _69880)). Qed.
Lemma lem5398988 (_69880 : int) : (term428 _69880) = term133.
Proof. exact (@lem1982719 (real_of_int _69880)). Qed.
Lemma lem5398989 (_69880 : int) : (term433 _69880) = term133.
Proof. exact (TRANS (@lem5398987 _69880) (@lem5398988 _69880)). Qed.
Lemma lem5398990 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5398991 (_69880 : int) : (term434 _69880) = term430.
Proof. exact (MK_COMB (@lem5398990) (@lem5398989 _69880)). Qed.
Lemma lem5398992 : term186 = term186.
Proof. exact (eq_refl term186). Qed.
Lemma lem5398993 (_69880 : int) : (term432 _69880) = term435.
Proof. exact (MK_COMB (@lem5398991 _69880) (@lem5398992)). Qed.
Lemma lem5398994 (_69880 : int) : (term431 _69880) = term435.
Proof. exact (TRANS (@lem5398883 _69880) (@lem5398993 _69880)). Qed.
Lemma lem5398995 : term435 = term186.
Proof. exact (@lem1982721 term186). Qed.
Lemma lem5398996 (_69880 : int) : (term431 _69880) = term186.
Proof. exact (TRANS (@lem5398994 _69880) (@lem5398995)). Qed.
Lemma lem5398997 (_69879 : int) (_69880 : int) : (term410 _69879 _69880) = term435.
Proof. exact (MK_COMB (@lem5398882 _69879) (@lem5398996 _69880)). Qed.
Lemma lem5398998 (_69879 : int) (_69880 : int) : (term409 _69879 _69880) = term435.
Proof. exact (TRANS (@lem5398774 _69879 _69880) (@lem5398997 _69879 _69880)). Qed.
Lemma lem5398999 : term435 = term186.
Proof. exact (@lem1982721 term186). Qed.
Lemma lem5399000 (_69879 : int) (_69880 : int) : (term409 _69879 _69880) = term186.
Proof. exact (TRANS (@lem5398998 _69879 _69880) (@lem5398999)). Qed.
Lemma lem5399001 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5399002 (_69879 : int) (_69880 : int) : (term436 _69879 _69880) = term437.
Proof. exact (MK_COMB (@lem5399001) (@lem5399000 _69879 _69880)). Qed.
Lemma lem5399003 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5399004 (_69879 : int) (_69880 : int) : (term408 _69879 _69880) = term438.
Proof. exact (MK_COMB (@lem5399002 _69879 _69880) (@lem5399003)). Qed.
Lemma lem5399005 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : term438.
Proof. exact (EQ_MP (@lem5399004 _69879 _69880) (@lem5398773 _69879 _69880 h1)). Qed.
Lemma lem5399007 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5399008 : term438 = term439.
Proof. exact (@lem5399007 term133 term186). Qed.
Lemma lem5399010 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5399011 : term186 = term187.
Proof. exact (@lem5399010 term18). Qed.
Lemma lem5399013 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399014 : term133 = term183.
Proof. exact (@lem5399013 (NUMERAL 0)). Qed.
Lemma lem5399015 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5399016 : term135 = term440.
Proof. exact (MK_COMB (@lem5399015) (@lem5399014)). Qed.
Lemma lem5399017 : term439 = term441.
Proof. exact (MK_COMB (@lem5399016) (@lem5399011)). Qed.
Lemma lem5399018 : term442.
Proof. exact (@lem1980026 term133 term142 term186 term142). Qed.
Lemma lem5399020 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399021 : term233 = term234.
Proof. exact (@lem5399020 (NUMERAL 0) term18). Qed.
Lemma lem5399022 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399023 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399024 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399023 h1) (fun h1 : term234 = True => @lem5399022)). Qed.
Lemma lem5399025 : term234 = True.
Proof. exact (EQ_MP (@lem5399024) (@lem5399022)). Qed.
Lemma lem5399026 : term233 = True.
Proof. exact (TRANS (@lem5399021) (@lem5399025)). Qed.
Lemma lem5399027 : True = term233.
Proof. exact (SYM (@lem5399026)). Qed.
Lemma lem5399028 : term233.
Proof. exact (EQ_MP (@lem5399027) (@lem0)). Qed.
Lemma lem5399029 : term443.
Proof. exact (@lem5399018 (@lem5399028)). Qed.
Lemma lem5399031 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399032 : term233 = term234.
Proof. exact (@lem5399031 (NUMERAL 0) term18). Qed.
Lemma lem5399033 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399034 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399035 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399034 h1) (fun h1 : term234 = True => @lem5399033)). Qed.
Lemma lem5399036 : term234 = True.
Proof. exact (EQ_MP (@lem5399035) (@lem5399033)). Qed.
Lemma lem5399037 : term233 = True.
Proof. exact (TRANS (@lem5399032) (@lem5399036)). Qed.
Lemma lem5399038 : True = term233.
Proof. exact (SYM (@lem5399037)). Qed.
Lemma lem5399039 : term233.
Proof. exact (EQ_MP (@lem5399038) (@lem0)). Qed.
Lemma lem5399040 : term441 = term444.
Proof. exact (@lem5399029 (@lem5399039)). Qed.
Lemma lem5399042 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5399043 : term212 = term217.
Proof. exact (@lem5399042 term18 term18). Qed.
Lemma lem5399044 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399045 : term198 = term18.
Proof. exact (EQ_MP (@lem5399044) (@lem940073)). Qed.
Lemma lem5399046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399047 : term196 = term142.
Proof. exact (MK_COMB (@lem5399046) (@lem5399045)). Qed.
Lemma lem5399048 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5399049 : term217 = term186.
Proof. exact (MK_COMB (@lem5399048) (@lem5399047)). Qed.
Lemma lem5399050 : term212 = term186.
Proof. exact (TRANS (@lem5399043) (@lem5399049)). Qed.
Lemma lem5399052 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5399053 : term245 = term133.
Proof. exact (@lem5399052 term18). Qed.
Lemma lem5399054 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5399055 : term445 = term135.
Proof. exact (MK_COMB (@lem5399054) (@lem5399053)). Qed.
Lemma lem5399056 : term444 = term439.
Proof. exact (MK_COMB (@lem5399055) (@lem5399050)). Qed.
Lemma lem5399058 (m : nat) (n : nat) : (term446 m n) = (term447 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5399059 : term439 = term448.
Proof. exact (@lem5399058 (NUMERAL 0) term18). Qed.
Lemma lem5399060 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399061 (h1 : term235 = (BIT1 0)) : (term18 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5399062 : (term235 = (BIT1 0)) = ((term18 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399061 h1) (fun h1 : (term18 = (NUMERAL 0)) = False => @lem5399060)). Qed.
Lemma lem5399063 : (term18 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5399062) (@lem5399060)). Qed.
Lemma lem5399064 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5399065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5399066 : term449 = (and True).
Proof. exact (MK_COMB (@lem5399065) (@lem5399064)). Qed.
Lemma lem5399067 : term448 = (True /\ False).
Proof. exact (MK_COMB (@lem5399066) (@lem5399063)). Qed.
Lemma lem5399069 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5399070 : term448 = False.
Proof. exact (TRANS (@lem5399067) (@lem5399069)). Qed.
Lemma lem5399071 : term439 = False.
Proof. exact (TRANS (@lem5399059) (@lem5399070)). Qed.
Lemma lem5399072 : term444 = False.
Proof. exact (TRANS (@lem5399056) (@lem5399071)). Qed.
Lemma lem5399073 : term441 = False.
Proof. exact (TRANS (@lem5399040) (@lem5399072)). Qed.
Lemma lem5399074 : term439 = False.
Proof. exact (TRANS (@lem5399017) (@lem5399073)). Qed.
Lemma lem5399075 : term438 = False.
Proof. exact (TRANS (@lem5399008) (@lem5399074)). Qed.
Lemma lem5399076 (_69879 : int) (_69880 : int) (h1 : term369 _69879 _69880) : False.
Proof. exact (EQ_MP (@lem5399075) (@lem5399005 _69879 _69880 h1)). Qed.
Lemma lem5399077 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term450 _69879 _69880.
Proof. exact (h1). Qed.
Lemma lem5399078 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term365 _69879 _69880.
Proof. exact (proj2 (@lem5399077 _69879 _69880 h1)). Qed.
Lemma lem5399080 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term352 _69879 _69880.
Proof. exact (proj2 (@lem5399078 _69879 _69880 h1)). Qed.
Lemma lem5399082 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term325 _69879 _69880.
Proof. exact (proj2 (@lem5399080 _69879 _69880 h1)). Qed.
Lemma lem5399083 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term315 _69880 _69879.
Proof. exact (proj1 (@lem5399080 _69879 _69880 h1)). Qed.
Lemma lem5399084 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : (real_of_int _69879) = term133.
Proof. exact (proj2 (@lem5399083 _69879 _69880 h1)). Qed.
Lemma lem5399085 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term312 _69880.
Proof. exact (proj1 (@lem5399083 _69879 _69880 h1)). Qed.
Lemma lem5399087 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5399088 : term370 = term233.
Proof. exact (@lem5399087 term133 term142). Qed.
Lemma lem5399090 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399091 : term142 = term211.
Proof. exact (@lem5399090 term18). Qed.
Lemma lem5399093 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399094 : term133 = term183.
Proof. exact (@lem5399093 (NUMERAL 0)). Qed.
Lemma lem5399095 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5399096 : term371 = term372.
Proof. exact (MK_COMB (@lem5399095) (@lem5399094)). Qed.
Lemma lem5399097 : term233 = term373.
Proof. exact (MK_COMB (@lem5399096) (@lem5399091)). Qed.
Lemma lem5399098 : term374.
Proof. exact (@lem1980255 term133 term142 term142 term142). Qed.
Lemma lem5399100 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399101 : term233 = term234.
Proof. exact (@lem5399100 (NUMERAL 0) term18). Qed.
Lemma lem5399102 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399103 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399104 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399103 h1) (fun h1 : term234 = True => @lem5399102)). Qed.
Lemma lem5399105 : term234 = True.
Proof. exact (EQ_MP (@lem5399104) (@lem5399102)). Qed.
Lemma lem5399106 : term233 = True.
Proof. exact (TRANS (@lem5399101) (@lem5399105)). Qed.
Lemma lem5399107 : True = term233.
Proof. exact (SYM (@lem5399106)). Qed.
Lemma lem5399108 : term233.
Proof. exact (EQ_MP (@lem5399107) (@lem0)). Qed.
Lemma lem5399109 : term375.
Proof. exact (@lem5399098 (@lem5399108)). Qed.
Lemma lem5399111 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399112 : term233 = term234.
Proof. exact (@lem5399111 (NUMERAL 0) term18). Qed.
Lemma lem5399113 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399114 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399115 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399114 h1) (fun h1 : term234 = True => @lem5399113)). Qed.
Lemma lem5399116 : term234 = True.
Proof. exact (EQ_MP (@lem5399115) (@lem5399113)). Qed.
Lemma lem5399117 : term233 = True.
Proof. exact (TRANS (@lem5399112) (@lem5399116)). Qed.
Lemma lem5399118 : True = term233.
Proof. exact (SYM (@lem5399117)). Qed.
Lemma lem5399119 : term233.
Proof. exact (EQ_MP (@lem5399118) (@lem0)). Qed.
Lemma lem5399120 : term373 = term376.
Proof. exact (@lem5399109 (@lem5399119)). Qed.
Lemma lem5399122 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5399123 : term195 = term196.
Proof. exact (@lem5399122 term18 term18). Qed.
Lemma lem5399124 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399125 : term198 = term18.
Proof. exact (EQ_MP (@lem5399124) (@lem940073)). Qed.
Lemma lem5399126 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399127 : term196 = term142.
Proof. exact (MK_COMB (@lem5399126) (@lem5399125)). Qed.
Lemma lem5399128 : term195 = term142.
Proof. exact (TRANS (@lem5399123) (@lem5399127)). Qed.
Lemma lem5399130 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5399131 : term245 = term133.
Proof. exact (@lem5399130 term18). Qed.
Lemma lem5399132 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5399133 : term377 = term371.
Proof. exact (MK_COMB (@lem5399132) (@lem5399131)). Qed.
Lemma lem5399134 : term376 = term233.
Proof. exact (MK_COMB (@lem5399133) (@lem5399128)). Qed.
Lemma lem5399136 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399137 : term233 = term234.
Proof. exact (@lem5399136 (NUMERAL 0) term18). Qed.
Lemma lem5399138 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399139 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399140 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399139 h1) (fun h1 : term234 = True => @lem5399138)). Qed.
Lemma lem5399141 : term234 = True.
Proof. exact (EQ_MP (@lem5399140) (@lem5399138)). Qed.
Lemma lem5399142 : term233 = True.
Proof. exact (TRANS (@lem5399137) (@lem5399141)). Qed.
Lemma lem5399143 : term376 = True.
Proof. exact (TRANS (@lem5399134) (@lem5399142)). Qed.
Lemma lem5399144 : term373 = True.
Proof. exact (TRANS (@lem5399120) (@lem5399143)). Qed.
Lemma lem5399145 : term233 = True.
Proof. exact (TRANS (@lem5399097) (@lem5399144)). Qed.
Lemma lem5399146 : term370 = True.
Proof. exact (TRANS (@lem5399088) (@lem5399145)). Qed.
Lemma lem5399147 : True = term370.
Proof. exact (SYM (@lem5399146)). Qed.
Lemma lem5399148 : term370.
Proof. exact (EQ_MP (@lem5399147) (@lem0)). Qed.
Lemma lem5399149 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term378 _69879 _69880.
Proof. exact (conj (@lem5399148) (@lem5399082 _69879 _69880 h1)). Qed.
Lemma lem5399151 (x : real) (y : real) : term379 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5399152 (_69879 : int) (_69880 : int) : term380 _69879 _69880.
Proof. exact (@lem5399151 term142 (term322 _69879 _69880)). Qed.
Lemma lem5399153 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term381 _69879 _69880.
Proof. exact (@lem5399152 _69879 _69880 (@lem5399149 _69879 _69880 h1)). Qed.
Lemma lem5399154 (_69879 : int) (_69880 : int) : (term382 _69879 _69880) = (term322 _69879 _69880).
Proof. exact (@lem1982733 (term322 _69879 _69880)). Qed.
Lemma lem5399155 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5399156 (_69879 : int) (_69880 : int) : (term383 _69879 _69880) = (term324 _69879 _69880).
Proof. exact (MK_COMB (@lem5399155) (@lem5399154 _69879 _69880)). Qed.
Lemma lem5399157 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5399158 (_69879 : int) (_69880 : int) : (term381 _69879 _69880) = (term325 _69879 _69880).
Proof. exact (MK_COMB (@lem5399156 _69879 _69880) (@lem5399157)). Qed.
Lemma lem5399159 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term325 _69879 _69880.
Proof. exact (EQ_MP (@lem5399158 _69879 _69880) (@lem5399153 _69879 _69880 h1)). Qed.
Lemma lem5399161 (y : real) : term384 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5399162 (_69879 : int) : term451 _69879.
Proof. exact (@lem5399161 (real_of_int _69879)). Qed.
Lemma lem5399163 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term452 _69879.
Proof. exact (@lem5399162 _69879 (@lem5399084 _69879 _69880 h1)). Qed.
Lemma lem5399164 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term453 _69879.
Proof. exact (@lem5399163 _69879 _69880 h1 term142). Qed.
Lemma lem5399165 (_69879 : int) : (term453 _69879) = ((term400 _69879) = term133).
Proof. exact (eq_refl (term453 _69879)). Qed.
Lemma lem5399166 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : (term400 _69879) = term133.
Proof. exact (EQ_MP (@lem5399165 _69879) (@lem5399164 _69879 _69880 h1)). Qed.
Lemma lem5399167 (_69879 : int) : (term400 _69879) = (real_of_int _69879).
Proof. exact (@lem1982733 (real_of_int _69879)). Qed.
Lemma lem5399168 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5399169 (_69879 : int) : (term454 _69879) = (term159 _69879).
Proof. exact (MK_COMB (@lem5399168) (@lem5399167 _69879)). Qed.
Lemma lem5399170 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5399171 (_69879 : int) : ((term400 _69879) = term133) = ((real_of_int _69879) = term133).
Proof. exact (MK_COMB (@lem5399169 _69879) (@lem5399170)). Qed.
Lemma lem5399172 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : (real_of_int _69879) = term133.
Proof. exact (EQ_MP (@lem5399171 _69879) (@lem5399166 _69879 _69880 h1)). Qed.
Lemma lem5399173 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term455 _69879 _69880.
Proof. exact (conj (@lem5399172 _69879 _69880 h1) (@lem5399159 _69879 _69880 h1)). Qed.
Lemma lem5399175 (x : real) (y : real) : term406 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5399176 (_69879 : int) (_69880 : int) : term456 _69879 _69880.
Proof. exact (@lem5399175 (real_of_int _69879) (term322 _69879 _69880)). Qed.
Lemma lem5399177 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term457 _69879 _69880.
Proof. exact (@lem5399176 _69879 _69880 (@lem5399173 _69879 _69880 h1)). Qed.
Lemma lem5399178 (_69879 : int) (_69880 : int) : (term458 _69879 _69880) = (term459 _69879 _69880).
Proof. exact (@lem1982763 (real_of_int _69879) (term224 _69879) (term411 _69880)). Qed.
Lemma lem5399179 (_69879 : int) : (term412 _69879) = (term413 _69879).
Proof. exact (@lem1982715 term186 (real_of_int _69879)). Qed.
Lemma lem5399181 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399182 : term142 = term211.
Proof. exact (@lem5399181 term18). Qed.
Lemma lem5399184 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5399185 : term186 = term187.
Proof. exact (@lem5399184 term18). Qed.
Lemma lem5399186 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5399187 : term414 = term415.
Proof. exact (MK_COMB (@lem5399186) (@lem5399185)). Qed.
Lemma lem5399188 : term416 = term417.
Proof. exact (MK_COMB (@lem5399187) (@lem5399182)). Qed.
Lemma lem5399189 : term418.
Proof. exact (@lem1981473 term186 term142 term142 term142 term133 term142). Qed.
Lemma lem5399191 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399192 : term233 = term234.
Proof. exact (@lem5399191 (NUMERAL 0) term18). Qed.
Lemma lem5399193 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399194 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399195 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399194 h1) (fun h1 : term234 = True => @lem5399193)). Qed.
Lemma lem5399196 : term234 = True.
Proof. exact (EQ_MP (@lem5399195) (@lem5399193)). Qed.
Lemma lem5399197 : term233 = True.
Proof. exact (TRANS (@lem5399192) (@lem5399196)). Qed.
Lemma lem5399198 : True = term233.
Proof. exact (SYM (@lem5399197)). Qed.
Lemma lem5399199 : term233.
Proof. exact (EQ_MP (@lem5399198) (@lem0)). Qed.
Lemma lem5399200 : term419.
Proof. exact (@lem5399189 (@lem5399199)). Qed.
Lemma lem5399202 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399203 : term233 = term234.
Proof. exact (@lem5399202 (NUMERAL 0) term18). Qed.
Lemma lem5399204 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399205 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399206 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399205 h1) (fun h1 : term234 = True => @lem5399204)). Qed.
Lemma lem5399207 : term234 = True.
Proof. exact (EQ_MP (@lem5399206) (@lem5399204)). Qed.
Lemma lem5399208 : term233 = True.
Proof. exact (TRANS (@lem5399203) (@lem5399207)). Qed.
Lemma lem5399209 : True = term233.
Proof. exact (SYM (@lem5399208)). Qed.
Lemma lem5399210 : term233.
Proof. exact (EQ_MP (@lem5399209) (@lem0)). Qed.
Lemma lem5399211 : term420.
Proof. exact (@lem5399200 (@lem5399210)). Qed.
Lemma lem5399213 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399214 : term233 = term234.
Proof. exact (@lem5399213 (NUMERAL 0) term18). Qed.
Lemma lem5399215 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399216 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399217 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399216 h1) (fun h1 : term234 = True => @lem5399215)). Qed.
Lemma lem5399218 : term234 = True.
Proof. exact (EQ_MP (@lem5399217) (@lem5399215)). Qed.
Lemma lem5399219 : term233 = True.
Proof. exact (TRANS (@lem5399214) (@lem5399218)). Qed.
Lemma lem5399220 : True = term233.
Proof. exact (SYM (@lem5399219)). Qed.
Lemma lem5399221 : term233.
Proof. exact (EQ_MP (@lem5399220) (@lem0)). Qed.
Lemma lem5399222 : term421.
Proof. exact (@lem5399211 (@lem5399221)). Qed.
Lemma lem5399224 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5399225 : term195 = term196.
Proof. exact (@lem5399224 term18 term18). Qed.
Lemma lem5399226 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399227 : term198 = term18.
Proof. exact (EQ_MP (@lem5399226) (@lem940073)). Qed.
Lemma lem5399228 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399229 : term196 = term142.
Proof. exact (MK_COMB (@lem5399228) (@lem5399227)). Qed.
Lemma lem5399230 : term195 = term142.
Proof. exact (TRANS (@lem5399225) (@lem5399229)). Qed.
Lemma lem5399232 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5399233 : term212 = term217.
Proof. exact (@lem5399232 term18 term18). Qed.
Lemma lem5399234 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399235 : term198 = term18.
Proof. exact (EQ_MP (@lem5399234) (@lem940073)). Qed.
Lemma lem5399236 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399237 : term196 = term142.
Proof. exact (MK_COMB (@lem5399236) (@lem5399235)). Qed.
Lemma lem5399238 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5399239 : term217 = term186.
Proof. exact (MK_COMB (@lem5399238) (@lem5399237)). Qed.
Lemma lem5399240 : term212 = term186.
Proof. exact (TRANS (@lem5399233) (@lem5399239)). Qed.
Lemma lem5399241 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5399242 : term422 = term414.
Proof. exact (MK_COMB (@lem5399241) (@lem5399240)). Qed.
Lemma lem5399243 : term423 = term416.
Proof. exact (MK_COMB (@lem5399242) (@lem5399230)). Qed.
Lemma lem5399245 (m : nat) : (term424 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5399246 : term416 = term133.
Proof. exact (@lem5399245 term18). Qed.
Lemma lem5399247 : term423 = term133.
Proof. exact (TRANS (@lem5399243) (@lem5399246)). Qed.
Lemma lem5399248 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5399249 : term425 = term243.
Proof. exact (MK_COMB (@lem5399248) (@lem5399247)). Qed.
Lemma lem5399250 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem5399251 : term426 = term245.
Proof. exact (MK_COMB (@lem5399249) (@lem5399250)). Qed.
Lemma lem5399253 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5399254 : term245 = term133.
Proof. exact (@lem5399253 term18). Qed.
Lemma lem5399255 : term426 = term133.
Proof. exact (TRANS (@lem5399251) (@lem5399254)). Qed.
Lemma lem5399257 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5399258 : term195 = term196.
Proof. exact (@lem5399257 term18 term18). Qed.
Lemma lem5399259 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399260 : term198 = term18.
Proof. exact (EQ_MP (@lem5399259) (@lem940073)). Qed.
Lemma lem5399261 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399262 : term196 = term142.
Proof. exact (MK_COMB (@lem5399261) (@lem5399260)). Qed.
Lemma lem5399263 : term195 = term142.
Proof. exact (TRANS (@lem5399258) (@lem5399262)). Qed.
Lemma lem5399264 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem5399265 : term247 = term245.
Proof. exact (MK_COMB (@lem5399264) (@lem5399263)). Qed.
Lemma lem5399267 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5399268 : term245 = term133.
Proof. exact (@lem5399267 term18). Qed.
Lemma lem5399269 : term247 = term133.
Proof. exact (TRANS (@lem5399265) (@lem5399268)). Qed.
Lemma lem5399270 : term133 = term247.
Proof. exact (SYM (@lem5399269)). Qed.
Lemma lem5399271 : term426 = term247.
Proof. exact (TRANS (@lem5399255) (@lem5399270)). Qed.
Lemma lem5399272 : term417 = term183.
Proof. exact (@lem5399222 (@lem5399271)). Qed.
Lemma lem5399273 : term416 = term183.
Proof. exact (TRANS (@lem5399188) (@lem5399272)). Qed.
Lemma lem5399275 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5399276 : term183 = term133.
Proof. exact (@lem5399275 term133). Qed.
Lemma lem5399277 : term416 = term133.
Proof. exact (TRANS (@lem5399273) (@lem5399276)). Qed.
Lemma lem5399278 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5399279 : term427 = term243.
Proof. exact (MK_COMB (@lem5399278) (@lem5399277)). Qed.
Lemma lem5399280 (_69879 : int) : (real_of_int _69879) = (real_of_int _69879).
Proof. exact (eq_refl (real_of_int _69879)). Qed.
Lemma lem5399281 (_69879 : int) : (term413 _69879) = (term428 _69879).
Proof. exact (MK_COMB (@lem5399279) (@lem5399280 _69879)). Qed.
Lemma lem5399282 (_69879 : int) : (term412 _69879) = (term428 _69879).
Proof. exact (TRANS (@lem5399179 _69879) (@lem5399281 _69879)). Qed.
Lemma lem5399283 (_69879 : int) : (term428 _69879) = term133.
Proof. exact (@lem1982719 (real_of_int _69879)). Qed.
Lemma lem5399284 (_69879 : int) : (term412 _69879) = term133.
Proof. exact (TRANS (@lem5399282 _69879) (@lem5399283 _69879)). Qed.
Lemma lem5399285 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5399286 (_69879 : int) : (term429 _69879) = term430.
Proof. exact (MK_COMB (@lem5399285) (@lem5399284 _69879)). Qed.
Lemma lem5399287 (_69880 : int) : (term411 _69880) = (term411 _69880).
Proof. exact (eq_refl (term411 _69880)). Qed.
Lemma lem5399288 (_69879 : int) (_69880 : int) : (term459 _69879 _69880) = (term460 _69880).
Proof. exact (MK_COMB (@lem5399286 _69879) (@lem5399287 _69880)). Qed.
Lemma lem5399289 (_69879 : int) (_69880 : int) : (term458 _69879 _69880) = (term460 _69880).
Proof. exact (TRANS (@lem5399178 _69879 _69880) (@lem5399288 _69879 _69880)). Qed.
Lemma lem5399290 (_69880 : int) : (term460 _69880) = (term411 _69880).
Proof. exact (@lem1982721 (term411 _69880)). Qed.
Lemma lem5399291 (_69879 : int) (_69880 : int) : (term458 _69879 _69880) = (term411 _69880).
Proof. exact (TRANS (@lem5399289 _69879 _69880) (@lem5399290 _69880)). Qed.
Lemma lem5399292 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5399293 (_69879 : int) (_69880 : int) : (term461 _69879 _69880) = (term462 _69880).
Proof. exact (MK_COMB (@lem5399292) (@lem5399291 _69879 _69880)). Qed.
Lemma lem5399294 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5399295 (_69879 : int) (_69880 : int) : (term457 _69879 _69880) = (term463 _69880).
Proof. exact (MK_COMB (@lem5399293 _69879 _69880) (@lem5399294)). Qed.
Lemma lem5399296 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term463 _69880.
Proof. exact (EQ_MP (@lem5399295 _69879 _69880) (@lem5399177 _69879 _69880 h1)). Qed.
Lemma lem5399298 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5399299 : term370 = term233.
Proof. exact (@lem5399298 term133 term142). Qed.
Lemma lem5399301 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399302 : term142 = term211.
Proof. exact (@lem5399301 term18). Qed.
Lemma lem5399304 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399305 : term133 = term183.
Proof. exact (@lem5399304 (NUMERAL 0)). Qed.
Lemma lem5399306 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5399307 : term371 = term372.
Proof. exact (MK_COMB (@lem5399306) (@lem5399305)). Qed.
Lemma lem5399308 : term233 = term373.
Proof. exact (MK_COMB (@lem5399307) (@lem5399302)). Qed.
Lemma lem5399309 : term374.
Proof. exact (@lem1980255 term133 term142 term142 term142). Qed.
Lemma lem5399311 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399312 : term233 = term234.
Proof. exact (@lem5399311 (NUMERAL 0) term18). Qed.
Lemma lem5399313 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399314 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399315 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399314 h1) (fun h1 : term234 = True => @lem5399313)). Qed.
Lemma lem5399316 : term234 = True.
Proof. exact (EQ_MP (@lem5399315) (@lem5399313)). Qed.
Lemma lem5399317 : term233 = True.
Proof. exact (TRANS (@lem5399312) (@lem5399316)). Qed.
Lemma lem5399318 : True = term233.
Proof. exact (SYM (@lem5399317)). Qed.
Lemma lem5399319 : term233.
Proof. exact (EQ_MP (@lem5399318) (@lem0)). Qed.
Lemma lem5399320 : term375.
Proof. exact (@lem5399309 (@lem5399319)). Qed.
Lemma lem5399322 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399323 : term233 = term234.
Proof. exact (@lem5399322 (NUMERAL 0) term18). Qed.
Lemma lem5399324 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399325 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399326 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399325 h1) (fun h1 : term234 = True => @lem5399324)). Qed.
Lemma lem5399327 : term234 = True.
Proof. exact (EQ_MP (@lem5399326) (@lem5399324)). Qed.
Lemma lem5399328 : term233 = True.
Proof. exact (TRANS (@lem5399323) (@lem5399327)). Qed.
Lemma lem5399329 : True = term233.
Proof. exact (SYM (@lem5399328)). Qed.
Lemma lem5399330 : term233.
Proof. exact (EQ_MP (@lem5399329) (@lem0)). Qed.
Lemma lem5399331 : term373 = term376.
Proof. exact (@lem5399320 (@lem5399330)). Qed.
Lemma lem5399333 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5399334 : term195 = term196.
Proof. exact (@lem5399333 term18 term18). Qed.
Lemma lem5399335 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399336 : term198 = term18.
Proof. exact (EQ_MP (@lem5399335) (@lem940073)). Qed.
Lemma lem5399337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399338 : term196 = term142.
Proof. exact (MK_COMB (@lem5399337) (@lem5399336)). Qed.
Lemma lem5399339 : term195 = term142.
Proof. exact (TRANS (@lem5399334) (@lem5399338)). Qed.
Lemma lem5399341 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5399342 : term245 = term133.
Proof. exact (@lem5399341 term18). Qed.
Lemma lem5399343 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5399344 : term377 = term371.
Proof. exact (MK_COMB (@lem5399343) (@lem5399342)). Qed.
Lemma lem5399345 : term376 = term233.
Proof. exact (MK_COMB (@lem5399344) (@lem5399339)). Qed.
Lemma lem5399347 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399348 : term233 = term234.
Proof. exact (@lem5399347 (NUMERAL 0) term18). Qed.
Lemma lem5399349 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399350 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399351 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399350 h1) (fun h1 : term234 = True => @lem5399349)). Qed.
Lemma lem5399352 : term234 = True.
Proof. exact (EQ_MP (@lem5399351) (@lem5399349)). Qed.
Lemma lem5399353 : term233 = True.
Proof. exact (TRANS (@lem5399348) (@lem5399352)). Qed.
Lemma lem5399354 : term376 = True.
Proof. exact (TRANS (@lem5399345) (@lem5399353)). Qed.
Lemma lem5399355 : term373 = True.
Proof. exact (TRANS (@lem5399331) (@lem5399354)). Qed.
Lemma lem5399356 : term233 = True.
Proof. exact (TRANS (@lem5399308) (@lem5399355)). Qed.
Lemma lem5399357 : term370 = True.
Proof. exact (TRANS (@lem5399299) (@lem5399356)). Qed.
Lemma lem5399358 : True = term370.
Proof. exact (SYM (@lem5399357)). Qed.
Lemma lem5399359 : term370.
Proof. exact (EQ_MP (@lem5399358) (@lem0)). Qed.
Lemma lem5399360 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term464 _69880.
Proof. exact (conj (@lem5399359) (@lem5399296 _69879 _69880 h1)). Qed.
Lemma lem5399362 (x : real) (y : real) : term379 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5399363 (_69880 : int) : term465 _69880.
Proof. exact (@lem5399362 term142 (term411 _69880)). Qed.
Lemma lem5399364 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term466 _69880.
Proof. exact (@lem5399363 _69880 (@lem5399360 _69879 _69880 h1)). Qed.
Lemma lem5399365 (_69880 : int) : (term467 _69880) = (term411 _69880).
Proof. exact (@lem1982733 (term411 _69880)). Qed.
Lemma lem5399366 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5399367 (_69880 : int) : (term468 _69880) = (term462 _69880).
Proof. exact (MK_COMB (@lem5399366) (@lem5399365 _69880)). Qed.
Lemma lem5399368 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5399369 (_69880 : int) : (term466 _69880) = (term463 _69880).
Proof. exact (MK_COMB (@lem5399367 _69880) (@lem5399368)). Qed.
Lemma lem5399370 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term463 _69880.
Proof. exact (EQ_MP (@lem5399369 _69880) (@lem5399364 _69879 _69880 h1)). Qed.
Lemma lem5399372 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5399373 : term370 = term233.
Proof. exact (@lem5399372 term133 term142). Qed.
Lemma lem5399375 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399376 : term142 = term211.
Proof. exact (@lem5399375 term18). Qed.
Lemma lem5399378 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399379 : term133 = term183.
Proof. exact (@lem5399378 (NUMERAL 0)). Qed.
Lemma lem5399380 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5399381 : term371 = term372.
Proof. exact (MK_COMB (@lem5399380) (@lem5399379)). Qed.
Lemma lem5399382 : term233 = term373.
Proof. exact (MK_COMB (@lem5399381) (@lem5399376)). Qed.
Lemma lem5399383 : term374.
Proof. exact (@lem1980255 term133 term142 term142 term142). Qed.
Lemma lem5399385 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399386 : term233 = term234.
Proof. exact (@lem5399385 (NUMERAL 0) term18). Qed.
Lemma lem5399387 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399388 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399389 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399388 h1) (fun h1 : term234 = True => @lem5399387)). Qed.
Lemma lem5399390 : term234 = True.
Proof. exact (EQ_MP (@lem5399389) (@lem5399387)). Qed.
Lemma lem5399391 : term233 = True.
Proof. exact (TRANS (@lem5399386) (@lem5399390)). Qed.
Lemma lem5399392 : True = term233.
Proof. exact (SYM (@lem5399391)). Qed.
Lemma lem5399393 : term233.
Proof. exact (EQ_MP (@lem5399392) (@lem0)). Qed.
Lemma lem5399394 : term375.
Proof. exact (@lem5399383 (@lem5399393)). Qed.
Lemma lem5399396 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399397 : term233 = term234.
Proof. exact (@lem5399396 (NUMERAL 0) term18). Qed.
Lemma lem5399398 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399399 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399400 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399399 h1) (fun h1 : term234 = True => @lem5399398)). Qed.
Lemma lem5399401 : term234 = True.
Proof. exact (EQ_MP (@lem5399400) (@lem5399398)). Qed.
Lemma lem5399402 : term233 = True.
Proof. exact (TRANS (@lem5399397) (@lem5399401)). Qed.
Lemma lem5399403 : True = term233.
Proof. exact (SYM (@lem5399402)). Qed.
Lemma lem5399404 : term233.
Proof. exact (EQ_MP (@lem5399403) (@lem0)). Qed.
Lemma lem5399405 : term373 = term376.
Proof. exact (@lem5399394 (@lem5399404)). Qed.
Lemma lem5399407 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5399408 : term195 = term196.
Proof. exact (@lem5399407 term18 term18). Qed.
Lemma lem5399409 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399410 : term198 = term18.
Proof. exact (EQ_MP (@lem5399409) (@lem940073)). Qed.
Lemma lem5399411 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399412 : term196 = term142.
Proof. exact (MK_COMB (@lem5399411) (@lem5399410)). Qed.
Lemma lem5399413 : term195 = term142.
Proof. exact (TRANS (@lem5399408) (@lem5399412)). Qed.
Lemma lem5399415 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5399416 : term245 = term133.
Proof. exact (@lem5399415 term18). Qed.
Lemma lem5399417 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5399418 : term377 = term371.
Proof. exact (MK_COMB (@lem5399417) (@lem5399416)). Qed.
Lemma lem5399419 : term376 = term233.
Proof. exact (MK_COMB (@lem5399418) (@lem5399413)). Qed.
Lemma lem5399421 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399422 : term233 = term234.
Proof. exact (@lem5399421 (NUMERAL 0) term18). Qed.
Lemma lem5399423 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399424 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399425 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399424 h1) (fun h1 : term234 = True => @lem5399423)). Qed.
Lemma lem5399426 : term234 = True.
Proof. exact (EQ_MP (@lem5399425) (@lem5399423)). Qed.
Lemma lem5399427 : term233 = True.
Proof. exact (TRANS (@lem5399422) (@lem5399426)). Qed.
Lemma lem5399428 : term376 = True.
Proof. exact (TRANS (@lem5399419) (@lem5399427)). Qed.
Lemma lem5399429 : term373 = True.
Proof. exact (TRANS (@lem5399405) (@lem5399428)). Qed.
Lemma lem5399430 : term233 = True.
Proof. exact (TRANS (@lem5399382) (@lem5399429)). Qed.
Lemma lem5399431 : term370 = True.
Proof. exact (TRANS (@lem5399373) (@lem5399430)). Qed.
Lemma lem5399432 : True = term370.
Proof. exact (SYM (@lem5399431)). Qed.
Lemma lem5399433 : term370.
Proof. exact (EQ_MP (@lem5399432) (@lem0)). Qed.
Lemma lem5399434 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term469 _69880.
Proof. exact (conj (@lem5399433) (@lem5399085 _69879 _69880 h1)). Qed.
Lemma lem5399436 (x : real) (y : real) : term379 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5399437 (_69880 : int) : term470 _69880.
Proof. exact (@lem5399436 term142 (term221 _69880)). Qed.
Lemma lem5399438 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term471 _69880.
Proof. exact (@lem5399437 _69880 (@lem5399434 _69879 _69880 h1)). Qed.
Lemma lem5399439 (_69880 : int) : (term472 _69880) = (term221 _69880).
Proof. exact (@lem1982733 (term221 _69880)). Qed.
Lemma lem5399440 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5399441 (_69880 : int) : (term473 _69880) = (term311 _69880).
Proof. exact (MK_COMB (@lem5399440) (@lem5399439 _69880)). Qed.
Lemma lem5399442 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5399443 (_69880 : int) : (term471 _69880) = (term312 _69880).
Proof. exact (MK_COMB (@lem5399441 _69880) (@lem5399442)). Qed.
Lemma lem5399444 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term312 _69880.
Proof. exact (EQ_MP (@lem5399443 _69880) (@lem5399438 _69879 _69880 h1)). Qed.
Lemma lem5399445 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term474 _69880.
Proof. exact (conj (@lem5399444 _69879 _69880 h1) (@lem5399370 _69879 _69880 h1)). Qed.
Lemma lem5399447 (x : real) (y : real) : term475 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5399448 (_69880 : int) : term476 _69880.
Proof. exact (@lem5399447 (term221 _69880) (term411 _69880)). Qed.
Lemma lem5399449 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term477 _69880.
Proof. exact (@lem5399448 _69880 (@lem5399445 _69879 _69880 h1)). Qed.
Lemma lem5399450 (_69880 : int) : (term478 _69880) = (term479 _69880).
Proof. exact (@lem1982753 (term224 _69880) (real_of_int _69880) term186 term186). Qed.
Lemma lem5399451 (_69880 : int) : (term433 _69880) = (term413 _69880).
Proof. exact (@lem1982713 term186 (real_of_int _69880)). Qed.
Lemma lem5399453 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399454 : term142 = term211.
Proof. exact (@lem5399453 term18). Qed.
Lemma lem5399456 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5399457 : term186 = term187.
Proof. exact (@lem5399456 term18). Qed.
Lemma lem5399458 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5399459 : term414 = term415.
Proof. exact (MK_COMB (@lem5399458) (@lem5399457)). Qed.
Lemma lem5399460 : term416 = term417.
Proof. exact (MK_COMB (@lem5399459) (@lem5399454)). Qed.
Lemma lem5399461 : term418.
Proof. exact (@lem1981473 term186 term142 term142 term142 term133 term142). Qed.
Lemma lem5399463 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399464 : term233 = term234.
Proof. exact (@lem5399463 (NUMERAL 0) term18). Qed.
Lemma lem5399465 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399466 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399467 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399466 h1) (fun h1 : term234 = True => @lem5399465)). Qed.
Lemma lem5399468 : term234 = True.
Proof. exact (EQ_MP (@lem5399467) (@lem5399465)). Qed.
Lemma lem5399469 : term233 = True.
Proof. exact (TRANS (@lem5399464) (@lem5399468)). Qed.
Lemma lem5399470 : True = term233.
Proof. exact (SYM (@lem5399469)). Qed.
Lemma lem5399471 : term233.
Proof. exact (EQ_MP (@lem5399470) (@lem0)). Qed.
Lemma lem5399472 : term419.
Proof. exact (@lem5399461 (@lem5399471)). Qed.
Lemma lem5399474 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399475 : term233 = term234.
Proof. exact (@lem5399474 (NUMERAL 0) term18). Qed.
Lemma lem5399476 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399477 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399478 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399477 h1) (fun h1 : term234 = True => @lem5399476)). Qed.
Lemma lem5399479 : term234 = True.
Proof. exact (EQ_MP (@lem5399478) (@lem5399476)). Qed.
Lemma lem5399480 : term233 = True.
Proof. exact (TRANS (@lem5399475) (@lem5399479)). Qed.
Lemma lem5399481 : True = term233.
Proof. exact (SYM (@lem5399480)). Qed.
Lemma lem5399482 : term233.
Proof. exact (EQ_MP (@lem5399481) (@lem0)). Qed.
Lemma lem5399483 : term420.
Proof. exact (@lem5399472 (@lem5399482)). Qed.
Lemma lem5399485 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399486 : term233 = term234.
Proof. exact (@lem5399485 (NUMERAL 0) term18). Qed.
Lemma lem5399487 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399488 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399489 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399488 h1) (fun h1 : term234 = True => @lem5399487)). Qed.
Lemma lem5399490 : term234 = True.
Proof. exact (EQ_MP (@lem5399489) (@lem5399487)). Qed.
Lemma lem5399491 : term233 = True.
Proof. exact (TRANS (@lem5399486) (@lem5399490)). Qed.
Lemma lem5399492 : True = term233.
Proof. exact (SYM (@lem5399491)). Qed.
Lemma lem5399493 : term233.
Proof. exact (EQ_MP (@lem5399492) (@lem0)). Qed.
Lemma lem5399494 : term421.
Proof. exact (@lem5399483 (@lem5399493)). Qed.
Lemma lem5399496 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5399497 : term195 = term196.
Proof. exact (@lem5399496 term18 term18). Qed.
Lemma lem5399498 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399499 : term198 = term18.
Proof. exact (EQ_MP (@lem5399498) (@lem940073)). Qed.
Lemma lem5399500 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399501 : term196 = term142.
Proof. exact (MK_COMB (@lem5399500) (@lem5399499)). Qed.
Lemma lem5399502 : term195 = term142.
Proof. exact (TRANS (@lem5399497) (@lem5399501)). Qed.
Lemma lem5399504 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5399505 : term212 = term217.
Proof. exact (@lem5399504 term18 term18). Qed.
Lemma lem5399506 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399507 : term198 = term18.
Proof. exact (EQ_MP (@lem5399506) (@lem940073)). Qed.
Lemma lem5399508 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399509 : term196 = term142.
Proof. exact (MK_COMB (@lem5399508) (@lem5399507)). Qed.
Lemma lem5399510 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5399511 : term217 = term186.
Proof. exact (MK_COMB (@lem5399510) (@lem5399509)). Qed.
Lemma lem5399512 : term212 = term186.
Proof. exact (TRANS (@lem5399505) (@lem5399511)). Qed.
Lemma lem5399513 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5399514 : term422 = term414.
Proof. exact (MK_COMB (@lem5399513) (@lem5399512)). Qed.
Lemma lem5399515 : term423 = term416.
Proof. exact (MK_COMB (@lem5399514) (@lem5399502)). Qed.
Lemma lem5399517 (m : nat) : (term424 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5399518 : term416 = term133.
Proof. exact (@lem5399517 term18). Qed.
Lemma lem5399519 : term423 = term133.
Proof. exact (TRANS (@lem5399515) (@lem5399518)). Qed.
Lemma lem5399520 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5399521 : term425 = term243.
Proof. exact (MK_COMB (@lem5399520) (@lem5399519)). Qed.
Lemma lem5399522 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem5399523 : term426 = term245.
Proof. exact (MK_COMB (@lem5399521) (@lem5399522)). Qed.
Lemma lem5399525 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5399526 : term245 = term133.
Proof. exact (@lem5399525 term18). Qed.
Lemma lem5399527 : term426 = term133.
Proof. exact (TRANS (@lem5399523) (@lem5399526)). Qed.
Lemma lem5399529 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5399530 : term195 = term196.
Proof. exact (@lem5399529 term18 term18). Qed.
Lemma lem5399531 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399532 : term198 = term18.
Proof. exact (EQ_MP (@lem5399531) (@lem940073)). Qed.
Lemma lem5399533 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399534 : term196 = term142.
Proof. exact (MK_COMB (@lem5399533) (@lem5399532)). Qed.
Lemma lem5399535 : term195 = term142.
Proof. exact (TRANS (@lem5399530) (@lem5399534)). Qed.
Lemma lem5399536 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem5399537 : term247 = term245.
Proof. exact (MK_COMB (@lem5399536) (@lem5399535)). Qed.
Lemma lem5399539 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5399540 : term245 = term133.
Proof. exact (@lem5399539 term18). Qed.
Lemma lem5399541 : term247 = term133.
Proof. exact (TRANS (@lem5399537) (@lem5399540)). Qed.
Lemma lem5399542 : term133 = term247.
Proof. exact (SYM (@lem5399541)). Qed.
Lemma lem5399543 : term426 = term247.
Proof. exact (TRANS (@lem5399527) (@lem5399542)). Qed.
Lemma lem5399544 : term417 = term183.
Proof. exact (@lem5399494 (@lem5399543)). Qed.
Lemma lem5399545 : term416 = term183.
Proof. exact (TRANS (@lem5399460) (@lem5399544)). Qed.
Lemma lem5399547 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5399548 : term183 = term133.
Proof. exact (@lem5399547 term133). Qed.
Lemma lem5399549 : term416 = term133.
Proof. exact (TRANS (@lem5399545) (@lem5399548)). Qed.
Lemma lem5399550 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5399551 : term427 = term243.
Proof. exact (MK_COMB (@lem5399550) (@lem5399549)). Qed.
Lemma lem5399552 (_69880 : int) : (real_of_int _69880) = (real_of_int _69880).
Proof. exact (eq_refl (real_of_int _69880)). Qed.
Lemma lem5399553 (_69880 : int) : (term413 _69880) = (term428 _69880).
Proof. exact (MK_COMB (@lem5399551) (@lem5399552 _69880)). Qed.
Lemma lem5399554 (_69880 : int) : (term433 _69880) = (term428 _69880).
Proof. exact (TRANS (@lem5399451 _69880) (@lem5399553 _69880)). Qed.
Lemma lem5399555 (_69880 : int) : (term428 _69880) = term133.
Proof. exact (@lem1982719 (real_of_int _69880)). Qed.
Lemma lem5399556 (_69880 : int) : (term433 _69880) = term133.
Proof. exact (TRANS (@lem5399554 _69880) (@lem5399555 _69880)). Qed.
Lemma lem5399557 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5399558 (_69880 : int) : (term434 _69880) = term430.
Proof. exact (MK_COMB (@lem5399557) (@lem5399556 _69880)). Qed.
Lemma lem5399560 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5399561 : term186 = term187.
Proof. exact (@lem5399560 term18). Qed.
Lemma lem5399563 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5399564 : term186 = term187.
Proof. exact (@lem5399563 term18). Qed.
Lemma lem5399565 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5399566 : term414 = term415.
Proof. exact (MK_COMB (@lem5399565) (@lem5399564)). Qed.
Lemma lem5399567 : term480 = term481.
Proof. exact (MK_COMB (@lem5399566) (@lem5399561)). Qed.
Lemma lem5399568 : term482.
Proof. exact (@lem1981473 term186 term142 term186 term142 term289 term142). Qed.
Lemma lem5399570 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399571 : term233 = term234.
Proof. exact (@lem5399570 (NUMERAL 0) term18). Qed.
Lemma lem5399572 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399573 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399574 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399573 h1) (fun h1 : term234 = True => @lem5399572)). Qed.
Lemma lem5399575 : term234 = True.
Proof. exact (EQ_MP (@lem5399574) (@lem5399572)). Qed.
Lemma lem5399576 : term233 = True.
Proof. exact (TRANS (@lem5399571) (@lem5399575)). Qed.
Lemma lem5399577 : True = term233.
Proof. exact (SYM (@lem5399576)). Qed.
Lemma lem5399578 : term233.
Proof. exact (EQ_MP (@lem5399577) (@lem0)). Qed.
Lemma lem5399579 : term483.
Proof. exact (@lem5399568 (@lem5399578)). Qed.
Lemma lem5399581 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399582 : term233 = term234.
Proof. exact (@lem5399581 (NUMERAL 0) term18). Qed.
Lemma lem5399583 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399584 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399585 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399584 h1) (fun h1 : term234 = True => @lem5399583)). Qed.
Lemma lem5399586 : term234 = True.
Proof. exact (EQ_MP (@lem5399585) (@lem5399583)). Qed.
Lemma lem5399587 : term233 = True.
Proof. exact (TRANS (@lem5399582) (@lem5399586)). Qed.
Lemma lem5399588 : True = term233.
Proof. exact (SYM (@lem5399587)). Qed.
Lemma lem5399589 : term233.
Proof. exact (EQ_MP (@lem5399588) (@lem0)). Qed.
Lemma lem5399590 : term484.
Proof. exact (@lem5399579 (@lem5399589)). Qed.
Lemma lem5399592 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399593 : term233 = term234.
Proof. exact (@lem5399592 (NUMERAL 0) term18). Qed.
Lemma lem5399594 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399595 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399596 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399595 h1) (fun h1 : term234 = True => @lem5399594)). Qed.
Lemma lem5399597 : term234 = True.
Proof. exact (EQ_MP (@lem5399596) (@lem5399594)). Qed.
Lemma lem5399598 : term233 = True.
Proof. exact (TRANS (@lem5399593) (@lem5399597)). Qed.
Lemma lem5399599 : True = term233.
Proof. exact (SYM (@lem5399598)). Qed.
Lemma lem5399600 : term233.
Proof. exact (EQ_MP (@lem5399599) (@lem0)). Qed.
Lemma lem5399601 : term485.
Proof. exact (@lem5399590 (@lem5399600)). Qed.
Lemma lem5399603 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5399604 : term212 = term217.
Proof. exact (@lem5399603 term18 term18). Qed.
Lemma lem5399605 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399606 : term198 = term18.
Proof. exact (EQ_MP (@lem5399605) (@lem940073)). Qed.
Lemma lem5399607 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399608 : term196 = term142.
Proof. exact (MK_COMB (@lem5399607) (@lem5399606)). Qed.
Lemma lem5399609 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5399610 : term217 = term186.
Proof. exact (MK_COMB (@lem5399609) (@lem5399608)). Qed.
Lemma lem5399611 : term212 = term186.
Proof. exact (TRANS (@lem5399604) (@lem5399610)). Qed.
Lemma lem5399613 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5399614 : term212 = term217.
Proof. exact (@lem5399613 term18 term18). Qed.
Lemma lem5399615 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399616 : term198 = term18.
Proof. exact (EQ_MP (@lem5399615) (@lem940073)). Qed.
Lemma lem5399617 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399618 : term196 = term142.
Proof. exact (MK_COMB (@lem5399617) (@lem5399616)). Qed.
Lemma lem5399619 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5399620 : term217 = term186.
Proof. exact (MK_COMB (@lem5399619) (@lem5399618)). Qed.
Lemma lem5399621 : term212 = term186.
Proof. exact (TRANS (@lem5399614) (@lem5399620)). Qed.
Lemma lem5399622 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5399623 : term422 = term414.
Proof. exact (MK_COMB (@lem5399622) (@lem5399621)). Qed.
Lemma lem5399624 : term486 = term480.
Proof. exact (MK_COMB (@lem5399623) (@lem5399611)). Qed.
Lemma lem5399625 : term480 = term306.
Proof. exact (@lem1367763 term18 term18). Qed.
Lemma lem5399626 : term262 = term263.
Proof. exact (@lem706885). Qed.
Lemma lem5399627 : (term262 = term263) = (term264 = term265).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term263). Qed.
Lemma lem5399628 : term264 = term265.
Proof. exact (EQ_MP (@lem5399627) (@lem5399626)). Qed.
Lemma lem5399629 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399630 : term261 = term256.
Proof. exact (MK_COMB (@lem5399629) (@lem5399628)). Qed.
Lemma lem5399631 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5399632 : term306 = term289.
Proof. exact (MK_COMB (@lem5399631) (@lem5399630)). Qed.
Lemma lem5399633 : term480 = term289.
Proof. exact (TRANS (@lem5399625) (@lem5399632)). Qed.
Lemma lem5399634 : term486 = term289.
Proof. exact (TRANS (@lem5399624) (@lem5399633)). Qed.
Lemma lem5399635 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5399636 : term487 = term488.
Proof. exact (MK_COMB (@lem5399635) (@lem5399634)). Qed.
Lemma lem5399637 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem5399638 : term489 = term302.
Proof. exact (MK_COMB (@lem5399636) (@lem5399637)). Qed.
Lemma lem5399640 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5399641 : term302 = term303.
Proof. exact (@lem5399640 term265 term18). Qed.
Lemma lem5399642 : term271 = term263.
Proof. exact (@lem996237 term263). Qed.
Lemma lem5399643 : (term271 = term263) = (term272 = term265).
Proof. exact (@lem1007663 term263 (BIT1 0) term263). Qed.
Lemma lem5399644 : term272 = term265.
Proof. exact (EQ_MP (@lem5399643) (@lem5399642)). Qed.
Lemma lem5399645 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399646 : term270 = term256.
Proof. exact (MK_COMB (@lem5399645) (@lem5399644)). Qed.
Lemma lem5399647 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5399648 : term303 = term289.
Proof. exact (MK_COMB (@lem5399647) (@lem5399646)). Qed.
Lemma lem5399649 : term302 = term289.
Proof. exact (TRANS (@lem5399641) (@lem5399648)). Qed.
Lemma lem5399650 : term489 = term289.
Proof. exact (TRANS (@lem5399638) (@lem5399649)). Qed.
Lemma lem5399652 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5399653 : term195 = term196.
Proof. exact (@lem5399652 term18 term18). Qed.
Lemma lem5399654 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399655 : term198 = term18.
Proof. exact (EQ_MP (@lem5399654) (@lem940073)). Qed.
Lemma lem5399656 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399657 : term196 = term142.
Proof. exact (MK_COMB (@lem5399656) (@lem5399655)). Qed.
Lemma lem5399658 : term195 = term142.
Proof. exact (TRANS (@lem5399653) (@lem5399657)). Qed.
Lemma lem5399659 : term488 = term488.
Proof. exact (eq_refl term488). Qed.
Lemma lem5399660 : term490 = term302.
Proof. exact (MK_COMB (@lem5399659) (@lem5399658)). Qed.
Lemma lem5399662 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5399663 : term302 = term303.
Proof. exact (@lem5399662 term265 term18). Qed.
Lemma lem5399664 : term271 = term263.
Proof. exact (@lem996237 term263). Qed.
Lemma lem5399665 : (term271 = term263) = (term272 = term265).
Proof. exact (@lem1007663 term263 (BIT1 0) term263). Qed.
Lemma lem5399666 : term272 = term265.
Proof. exact (EQ_MP (@lem5399665) (@lem5399664)). Qed.
Lemma lem5399667 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399668 : term270 = term256.
Proof. exact (MK_COMB (@lem5399667) (@lem5399666)). Qed.
Lemma lem5399669 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5399670 : term303 = term289.
Proof. exact (MK_COMB (@lem5399669) (@lem5399668)). Qed.
Lemma lem5399671 : term302 = term289.
Proof. exact (TRANS (@lem5399663) (@lem5399670)). Qed.
Lemma lem5399672 : term490 = term289.
Proof. exact (TRANS (@lem5399660) (@lem5399671)). Qed.
Lemma lem5399673 : term289 = term490.
Proof. exact (SYM (@lem5399672)). Qed.
Lemma lem5399674 : term489 = term490.
Proof. exact (TRANS (@lem5399650) (@lem5399673)). Qed.
Lemma lem5399675 : term481 = term292.
Proof. exact (@lem5399601 (@lem5399674)). Qed.
Lemma lem5399676 : term480 = term292.
Proof. exact (TRANS (@lem5399567) (@lem5399675)). Qed.
Lemma lem5399678 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5399679 : term292 = term289.
Proof. exact (@lem5399678 term289). Qed.
Lemma lem5399680 : term480 = term289.
Proof. exact (TRANS (@lem5399676) (@lem5399679)). Qed.
Lemma lem5399681 (_69880 : int) : (term479 _69880) = term491.
Proof. exact (MK_COMB (@lem5399558 _69880) (@lem5399680)). Qed.
Lemma lem5399682 (_69880 : int) : (term478 _69880) = term491.
Proof. exact (TRANS (@lem5399450 _69880) (@lem5399681 _69880)). Qed.
Lemma lem5399683 : term491 = term289.
Proof. exact (@lem1982721 term289). Qed.
Lemma lem5399684 (_69880 : int) : (term478 _69880) = term289.
Proof. exact (TRANS (@lem5399682 _69880) (@lem5399683)). Qed.
Lemma lem5399685 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5399686 (_69880 : int) : (term492 _69880) = term493.
Proof. exact (MK_COMB (@lem5399685) (@lem5399684 _69880)). Qed.
Lemma lem5399687 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5399688 (_69880 : int) : (term477 _69880) = term494.
Proof. exact (MK_COMB (@lem5399686 _69880) (@lem5399687)). Qed.
Lemma lem5399689 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : term494.
Proof. exact (EQ_MP (@lem5399688 _69880) (@lem5399449 _69879 _69880 h1)). Qed.
Lemma lem5399691 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5399692 : term494 = term495.
Proof. exact (@lem5399691 term133 term289). Qed.
Lemma lem5399694 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5399695 : term289 = term292.
Proof. exact (@lem5399694 term265). Qed.
Lemma lem5399697 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399698 : term133 = term183.
Proof. exact (@lem5399697 (NUMERAL 0)). Qed.
Lemma lem5399699 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5399700 : term135 = term440.
Proof. exact (MK_COMB (@lem5399699) (@lem5399698)). Qed.
Lemma lem5399701 : term495 = term496.
Proof. exact (MK_COMB (@lem5399700) (@lem5399695)). Qed.
Lemma lem5399702 : term497.
Proof. exact (@lem1980026 term133 term142 term289 term142). Qed.
Lemma lem5399704 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399705 : term233 = term234.
Proof. exact (@lem5399704 (NUMERAL 0) term18). Qed.
Lemma lem5399706 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399707 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399708 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399707 h1) (fun h1 : term234 = True => @lem5399706)). Qed.
Lemma lem5399709 : term234 = True.
Proof. exact (EQ_MP (@lem5399708) (@lem5399706)). Qed.
Lemma lem5399710 : term233 = True.
Proof. exact (TRANS (@lem5399705) (@lem5399709)). Qed.
Lemma lem5399711 : True = term233.
Proof. exact (SYM (@lem5399710)). Qed.
Lemma lem5399712 : term233.
Proof. exact (EQ_MP (@lem5399711) (@lem0)). Qed.
Lemma lem5399713 : term498.
Proof. exact (@lem5399702 (@lem5399712)). Qed.
Lemma lem5399715 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399716 : term233 = term234.
Proof. exact (@lem5399715 (NUMERAL 0) term18). Qed.
Lemma lem5399717 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399718 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399719 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399718 h1) (fun h1 : term234 = True => @lem5399717)). Qed.
Lemma lem5399720 : term234 = True.
Proof. exact (EQ_MP (@lem5399719) (@lem5399717)). Qed.
Lemma lem5399721 : term233 = True.
Proof. exact (TRANS (@lem5399716) (@lem5399720)). Qed.
Lemma lem5399722 : True = term233.
Proof. exact (SYM (@lem5399721)). Qed.
Lemma lem5399723 : term233.
Proof. exact (EQ_MP (@lem5399722) (@lem0)). Qed.
Lemma lem5399724 : term496 = term499.
Proof. exact (@lem5399713 (@lem5399723)). Qed.
Lemma lem5399726 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5399727 : term302 = term303.
Proof. exact (@lem5399726 term265 term18). Qed.
Lemma lem5399728 : term271 = term263.
Proof. exact (@lem996237 term263). Qed.
Lemma lem5399729 : (term271 = term263) = (term272 = term265).
Proof. exact (@lem1007663 term263 (BIT1 0) term263). Qed.
Lemma lem5399730 : term272 = term265.
Proof. exact (EQ_MP (@lem5399729) (@lem5399728)). Qed.
Lemma lem5399731 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399732 : term270 = term256.
Proof. exact (MK_COMB (@lem5399731) (@lem5399730)). Qed.
Lemma lem5399733 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5399734 : term303 = term289.
Proof. exact (MK_COMB (@lem5399733) (@lem5399732)). Qed.
Lemma lem5399735 : term302 = term289.
Proof. exact (TRANS (@lem5399727) (@lem5399734)). Qed.
Lemma lem5399737 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5399738 : term245 = term133.
Proof. exact (@lem5399737 term18). Qed.
Lemma lem5399739 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5399740 : term445 = term135.
Proof. exact (MK_COMB (@lem5399739) (@lem5399738)). Qed.
Lemma lem5399741 : term499 = term495.
Proof. exact (MK_COMB (@lem5399740) (@lem5399735)). Qed.
Lemma lem5399743 (m : nat) (n : nat) : (term446 m n) = (term447 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5399744 : term495 = term500.
Proof. exact (@lem5399743 (NUMERAL 0) term265). Qed.
Lemma lem5399745 : term501 = term263.
Proof. exact (@lem912803). Qed.
Lemma lem5399746 (h1 : term501 = term263) : (term265 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term263 h1). Qed.
Lemma lem5399747 : (term501 = term263) = ((term265 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term501 = term263 => @lem5399746 h1) (fun h1 : (term265 = (NUMERAL 0)) = False => @lem5399745)). Qed.
Lemma lem5399748 : (term265 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5399747) (@lem5399745)). Qed.
Lemma lem5399749 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5399750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5399751 : term449 = (and True).
Proof. exact (MK_COMB (@lem5399750) (@lem5399749)). Qed.
Lemma lem5399752 : term500 = (True /\ False).
Proof. exact (MK_COMB (@lem5399751) (@lem5399748)). Qed.
Lemma lem5399754 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5399755 : term500 = False.
Proof. exact (TRANS (@lem5399752) (@lem5399754)). Qed.
Lemma lem5399756 : term495 = False.
Proof. exact (TRANS (@lem5399744) (@lem5399755)). Qed.
Lemma lem5399757 : term499 = False.
Proof. exact (TRANS (@lem5399741) (@lem5399756)). Qed.
Lemma lem5399758 : term496 = False.
Proof. exact (TRANS (@lem5399724) (@lem5399757)). Qed.
Lemma lem5399759 : term495 = False.
Proof. exact (TRANS (@lem5399701) (@lem5399758)). Qed.
Lemma lem5399760 : term494 = False.
Proof. exact (TRANS (@lem5399692) (@lem5399759)). Qed.
Lemma lem5399761 (_69879 : int) (_69880 : int) (h1 : term450 _69879 _69880) : False.
Proof. exact (EQ_MP (@lem5399760) (@lem5399689 _69879 _69880 h1)). Qed.
Lemma lem5399762 (_69879 : int) (_69880 : int) (h1 : term363 _69879 _69880) : False.
Proof. exact (or_elim (@lem5398626 _69879 _69880 h1) (fun h0 : term369 _69879 _69880 => @lem5399076 _69879 _69880 h0) (fun h0 : term450 _69879 _69880 => @lem5399761 _69879 _69880 h0)). Qed.
Lemma lem5399763 (_69879 : int) (_69880 : int) (h1 : term359 _69879 _69880) : term359 _69879 _69880.
Proof. exact (h1). Qed.
Lemma lem5399764 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : term502 _69879 _69880.
Proof. exact (h1). Qed.
Lemma lem5399765 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : term360 _69879 _69880.
Proof. exact (proj2 (@lem5399764 _69879 _69880 h1)). Qed.
Lemma lem5399767 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : term347 _69879 _69880.
Proof. exact (proj2 (@lem5399765 _69879 _69880 h1)). Qed.
Lemma lem5399769 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : term327 _69879 _69880.
Proof. exact (proj2 (@lem5399767 _69879 _69880 h1)). Qed.
Lemma lem5399770 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : (term248 _69879 _69880) = term133.
Proof. exact (proj1 (@lem5399767 _69879 _69880 h1)). Qed.
Lemma lem5399772 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5399773 : term370 = term233.
Proof. exact (@lem5399772 term133 term142). Qed.
Lemma lem5399775 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399776 : term142 = term211.
Proof. exact (@lem5399775 term18). Qed.
Lemma lem5399778 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399779 : term133 = term183.
Proof. exact (@lem5399778 (NUMERAL 0)). Qed.
Lemma lem5399780 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5399781 : term371 = term372.
Proof. exact (MK_COMB (@lem5399780) (@lem5399779)). Qed.
Lemma lem5399782 : term233 = term373.
Proof. exact (MK_COMB (@lem5399781) (@lem5399776)). Qed.
Lemma lem5399783 : term374.
Proof. exact (@lem1980255 term133 term142 term142 term142). Qed.
Lemma lem5399785 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399786 : term233 = term234.
Proof. exact (@lem5399785 (NUMERAL 0) term18). Qed.
Lemma lem5399787 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399788 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399789 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399788 h1) (fun h1 : term234 = True => @lem5399787)). Qed.
Lemma lem5399790 : term234 = True.
Proof. exact (EQ_MP (@lem5399789) (@lem5399787)). Qed.
Lemma lem5399791 : term233 = True.
Proof. exact (TRANS (@lem5399786) (@lem5399790)). Qed.
Lemma lem5399792 : True = term233.
Proof. exact (SYM (@lem5399791)). Qed.
Lemma lem5399793 : term233.
Proof. exact (EQ_MP (@lem5399792) (@lem0)). Qed.
Lemma lem5399794 : term375.
Proof. exact (@lem5399783 (@lem5399793)). Qed.
Lemma lem5399796 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399797 : term233 = term234.
Proof. exact (@lem5399796 (NUMERAL 0) term18). Qed.
Lemma lem5399798 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399799 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399800 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399799 h1) (fun h1 : term234 = True => @lem5399798)). Qed.
Lemma lem5399801 : term234 = True.
Proof. exact (EQ_MP (@lem5399800) (@lem5399798)). Qed.
Lemma lem5399802 : term233 = True.
Proof. exact (TRANS (@lem5399797) (@lem5399801)). Qed.
Lemma lem5399803 : True = term233.
Proof. exact (SYM (@lem5399802)). Qed.
Lemma lem5399804 : term233.
Proof. exact (EQ_MP (@lem5399803) (@lem0)). Qed.
Lemma lem5399805 : term373 = term376.
Proof. exact (@lem5399794 (@lem5399804)). Qed.
Lemma lem5399807 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5399808 : term195 = term196.
Proof. exact (@lem5399807 term18 term18). Qed.
Lemma lem5399809 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399810 : term198 = term18.
Proof. exact (EQ_MP (@lem5399809) (@lem940073)). Qed.
Lemma lem5399811 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399812 : term196 = term142.
Proof. exact (MK_COMB (@lem5399811) (@lem5399810)). Qed.
Lemma lem5399813 : term195 = term142.
Proof. exact (TRANS (@lem5399808) (@lem5399812)). Qed.
Lemma lem5399815 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5399816 : term245 = term133.
Proof. exact (@lem5399815 term18). Qed.
Lemma lem5399817 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5399818 : term377 = term371.
Proof. exact (MK_COMB (@lem5399817) (@lem5399816)). Qed.
Lemma lem5399819 : term376 = term233.
Proof. exact (MK_COMB (@lem5399818) (@lem5399813)). Qed.
Lemma lem5399821 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399822 : term233 = term234.
Proof. exact (@lem5399821 (NUMERAL 0) term18). Qed.
Lemma lem5399823 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399824 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399825 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399824 h1) (fun h1 : term234 = True => @lem5399823)). Qed.
Lemma lem5399826 : term234 = True.
Proof. exact (EQ_MP (@lem5399825) (@lem5399823)). Qed.
Lemma lem5399827 : term233 = True.
Proof. exact (TRANS (@lem5399822) (@lem5399826)). Qed.
Lemma lem5399828 : term376 = True.
Proof. exact (TRANS (@lem5399819) (@lem5399827)). Qed.
Lemma lem5399829 : term373 = True.
Proof. exact (TRANS (@lem5399805) (@lem5399828)). Qed.
Lemma lem5399830 : term233 = True.
Proof. exact (TRANS (@lem5399782) (@lem5399829)). Qed.
Lemma lem5399831 : term370 = True.
Proof. exact (TRANS (@lem5399773) (@lem5399830)). Qed.
Lemma lem5399832 : True = term370.
Proof. exact (SYM (@lem5399831)). Qed.
Lemma lem5399833 : term370.
Proof. exact (EQ_MP (@lem5399832) (@lem0)). Qed.
Lemma lem5399834 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : term503 _69879 _69880.
Proof. exact (conj (@lem5399833) (@lem5399769 _69879 _69880 h1)). Qed.
Lemma lem5399836 (x : real) (y : real) : term379 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5399837 (_69879 : int) (_69880 : int) : term504 _69879 _69880.
Proof. exact (@lem5399836 term142 (term321 _69879 _69880)). Qed.
Lemma lem5399838 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : term505 _69879 _69880.
Proof. exact (@lem5399837 _69879 _69880 (@lem5399834 _69879 _69880 h1)). Qed.
Lemma lem5399839 (_69879 : int) (_69880 : int) : (term506 _69879 _69880) = (term321 _69879 _69880).
Proof. exact (@lem1982733 (term321 _69879 _69880)). Qed.
Lemma lem5399840 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5399841 (_69879 : int) (_69880 : int) : (term507 _69879 _69880) = (term326 _69879 _69880).
Proof. exact (MK_COMB (@lem5399840) (@lem5399839 _69879 _69880)). Qed.
Lemma lem5399842 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5399843 (_69879 : int) (_69880 : int) : (term505 _69879 _69880) = (term327 _69879 _69880).
Proof. exact (MK_COMB (@lem5399841 _69879 _69880) (@lem5399842)). Qed.
Lemma lem5399844 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : term327 _69879 _69880.
Proof. exact (EQ_MP (@lem5399843 _69879 _69880) (@lem5399838 _69879 _69880 h1)). Qed.
Lemma lem5399846 (y : real) : term384 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5399847 (_69879 : int) (_69880 : int) : term385 _69879 _69880.
Proof. exact (@lem5399846 (term248 _69879 _69880)). Qed.
Lemma lem5399848 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : term386 _69879 _69880.
Proof. exact (@lem5399847 _69879 _69880 (@lem5399770 _69879 _69880 h1)). Qed.
Lemma lem5399849 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : term508 _69879 _69880.
Proof. exact (@lem5399848 _69879 _69880 h1 term142). Qed.
Lemma lem5399850 (_69879 : int) (_69880 : int) : (term508 _69879 _69880) = ((term509 _69879 _69880) = term133).
Proof. exact (eq_refl (term508 _69879 _69880)). Qed.
Lemma lem5399851 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : (term509 _69879 _69880) = term133.
Proof. exact (EQ_MP (@lem5399850 _69879 _69880) (@lem5399849 _69879 _69880 h1)). Qed.
Lemma lem5399852 (_69879 : int) (_69880 : int) : (term509 _69879 _69880) = (term248 _69879 _69880).
Proof. exact (@lem1982733 (term248 _69879 _69880)). Qed.
Lemma lem5399853 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5399854 (_69879 : int) (_69880 : int) : (term510 _69879 _69880) = (term250 _69879 _69880).
Proof. exact (MK_COMB (@lem5399853) (@lem5399852 _69879 _69880)). Qed.
Lemma lem5399855 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5399856 (_69879 : int) (_69880 : int) : ((term509 _69879 _69880) = term133) = ((term248 _69879 _69880) = term133).
Proof. exact (MK_COMB (@lem5399854 _69879 _69880) (@lem5399855)). Qed.
Lemma lem5399857 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : (term248 _69879 _69880) = term133.
Proof. exact (EQ_MP (@lem5399856 _69879 _69880) (@lem5399851 _69879 _69880 h1)). Qed.
Lemma lem5399858 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : term347 _69879 _69880.
Proof. exact (conj (@lem5399857 _69879 _69880 h1) (@lem5399844 _69879 _69880 h1)). Qed.
Lemma lem5399860 (x : real) (y : real) : term406 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5399861 (_69879 : int) (_69880 : int) : term511 _69879 _69880.
Proof. exact (@lem5399860 (term248 _69879 _69880) (term321 _69879 _69880)). Qed.
Lemma lem5399862 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : term512 _69879 _69880.
Proof. exact (@lem5399861 _69879 _69880 (@lem5399858 _69879 _69880 h1)). Qed.
Lemma lem5399863 (_69879 : int) (_69880 : int) : (term513 _69879 _69880) = (term514 _69879 _69880).
Proof. exact (@lem1982753 (term224 _69879) (real_of_int _69879) (real_of_int _69880) (term221 _69880)). Qed.
Lemma lem5399864 (_69879 : int) : (term433 _69879) = (term413 _69879).
Proof. exact (@lem1982713 term186 (real_of_int _69879)). Qed.
Lemma lem5399866 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399867 : term142 = term211.
Proof. exact (@lem5399866 term18). Qed.
Lemma lem5399869 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5399870 : term186 = term187.
Proof. exact (@lem5399869 term18). Qed.
Lemma lem5399871 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5399872 : term414 = term415.
Proof. exact (MK_COMB (@lem5399871) (@lem5399870)). Qed.
Lemma lem5399873 : term416 = term417.
Proof. exact (MK_COMB (@lem5399872) (@lem5399867)). Qed.
Lemma lem5399874 : term418.
Proof. exact (@lem1981473 term186 term142 term142 term142 term133 term142). Qed.
Lemma lem5399876 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399877 : term233 = term234.
Proof. exact (@lem5399876 (NUMERAL 0) term18). Qed.
Lemma lem5399878 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399879 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399880 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399879 h1) (fun h1 : term234 = True => @lem5399878)). Qed.
Lemma lem5399881 : term234 = True.
Proof. exact (EQ_MP (@lem5399880) (@lem5399878)). Qed.
Lemma lem5399882 : term233 = True.
Proof. exact (TRANS (@lem5399877) (@lem5399881)). Qed.
Lemma lem5399883 : True = term233.
Proof. exact (SYM (@lem5399882)). Qed.
Lemma lem5399884 : term233.
Proof. exact (EQ_MP (@lem5399883) (@lem0)). Qed.
Lemma lem5399885 : term419.
Proof. exact (@lem5399874 (@lem5399884)). Qed.
Lemma lem5399887 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399888 : term233 = term234.
Proof. exact (@lem5399887 (NUMERAL 0) term18). Qed.
Lemma lem5399889 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399890 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399891 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399890 h1) (fun h1 : term234 = True => @lem5399889)). Qed.
Lemma lem5399892 : term234 = True.
Proof. exact (EQ_MP (@lem5399891) (@lem5399889)). Qed.
Lemma lem5399893 : term233 = True.
Proof. exact (TRANS (@lem5399888) (@lem5399892)). Qed.
Lemma lem5399894 : True = term233.
Proof. exact (SYM (@lem5399893)). Qed.
Lemma lem5399895 : term233.
Proof. exact (EQ_MP (@lem5399894) (@lem0)). Qed.
Lemma lem5399896 : term420.
Proof. exact (@lem5399885 (@lem5399895)). Qed.
Lemma lem5399898 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399899 : term233 = term234.
Proof. exact (@lem5399898 (NUMERAL 0) term18). Qed.
Lemma lem5399900 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399901 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399902 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399901 h1) (fun h1 : term234 = True => @lem5399900)). Qed.
Lemma lem5399903 : term234 = True.
Proof. exact (EQ_MP (@lem5399902) (@lem5399900)). Qed.
Lemma lem5399904 : term233 = True.
Proof. exact (TRANS (@lem5399899) (@lem5399903)). Qed.
Lemma lem5399905 : True = term233.
Proof. exact (SYM (@lem5399904)). Qed.
Lemma lem5399906 : term233.
Proof. exact (EQ_MP (@lem5399905) (@lem0)). Qed.
Lemma lem5399907 : term421.
Proof. exact (@lem5399896 (@lem5399906)). Qed.
Lemma lem5399909 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5399910 : term195 = term196.
Proof. exact (@lem5399909 term18 term18). Qed.
Lemma lem5399911 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399912 : term198 = term18.
Proof. exact (EQ_MP (@lem5399911) (@lem940073)). Qed.
Lemma lem5399913 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399914 : term196 = term142.
Proof. exact (MK_COMB (@lem5399913) (@lem5399912)). Qed.
Lemma lem5399915 : term195 = term142.
Proof. exact (TRANS (@lem5399910) (@lem5399914)). Qed.
Lemma lem5399917 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5399918 : term212 = term217.
Proof. exact (@lem5399917 term18 term18). Qed.
Lemma lem5399919 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399920 : term198 = term18.
Proof. exact (EQ_MP (@lem5399919) (@lem940073)). Qed.
Lemma lem5399921 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399922 : term196 = term142.
Proof. exact (MK_COMB (@lem5399921) (@lem5399920)). Qed.
Lemma lem5399923 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5399924 : term217 = term186.
Proof. exact (MK_COMB (@lem5399923) (@lem5399922)). Qed.
Lemma lem5399925 : term212 = term186.
Proof. exact (TRANS (@lem5399918) (@lem5399924)). Qed.
Lemma lem5399926 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5399927 : term422 = term414.
Proof. exact (MK_COMB (@lem5399926) (@lem5399925)). Qed.
Lemma lem5399928 : term423 = term416.
Proof. exact (MK_COMB (@lem5399927) (@lem5399915)). Qed.
Lemma lem5399930 (m : nat) : (term424 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5399931 : term416 = term133.
Proof. exact (@lem5399930 term18). Qed.
Lemma lem5399932 : term423 = term133.
Proof. exact (TRANS (@lem5399928) (@lem5399931)). Qed.
Lemma lem5399933 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5399934 : term425 = term243.
Proof. exact (MK_COMB (@lem5399933) (@lem5399932)). Qed.
Lemma lem5399935 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem5399936 : term426 = term245.
Proof. exact (MK_COMB (@lem5399934) (@lem5399935)). Qed.
Lemma lem5399938 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5399939 : term245 = term133.
Proof. exact (@lem5399938 term18). Qed.
Lemma lem5399940 : term426 = term133.
Proof. exact (TRANS (@lem5399936) (@lem5399939)). Qed.
Lemma lem5399942 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5399943 : term195 = term196.
Proof. exact (@lem5399942 term18 term18). Qed.
Lemma lem5399944 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5399945 : term198 = term18.
Proof. exact (EQ_MP (@lem5399944) (@lem940073)). Qed.
Lemma lem5399946 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5399947 : term196 = term142.
Proof. exact (MK_COMB (@lem5399946) (@lem5399945)). Qed.
Lemma lem5399948 : term195 = term142.
Proof. exact (TRANS (@lem5399943) (@lem5399947)). Qed.
Lemma lem5399949 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem5399950 : term247 = term245.
Proof. exact (MK_COMB (@lem5399949) (@lem5399948)). Qed.
Lemma lem5399952 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5399953 : term245 = term133.
Proof. exact (@lem5399952 term18). Qed.
Lemma lem5399954 : term247 = term133.
Proof. exact (TRANS (@lem5399950) (@lem5399953)). Qed.
Lemma lem5399955 : term133 = term247.
Proof. exact (SYM (@lem5399954)). Qed.
Lemma lem5399956 : term426 = term247.
Proof. exact (TRANS (@lem5399940) (@lem5399955)). Qed.
Lemma lem5399957 : term417 = term183.
Proof. exact (@lem5399907 (@lem5399956)). Qed.
Lemma lem5399958 : term416 = term183.
Proof. exact (TRANS (@lem5399873) (@lem5399957)). Qed.
Lemma lem5399960 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5399961 : term183 = term133.
Proof. exact (@lem5399960 term133). Qed.
Lemma lem5399962 : term416 = term133.
Proof. exact (TRANS (@lem5399958) (@lem5399961)). Qed.
Lemma lem5399963 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5399964 : term427 = term243.
Proof. exact (MK_COMB (@lem5399963) (@lem5399962)). Qed.
Lemma lem5399965 (_69879 : int) : (real_of_int _69879) = (real_of_int _69879).
Proof. exact (eq_refl (real_of_int _69879)). Qed.
Lemma lem5399966 (_69879 : int) : (term413 _69879) = (term428 _69879).
Proof. exact (MK_COMB (@lem5399964) (@lem5399965 _69879)). Qed.
Lemma lem5399967 (_69879 : int) : (term433 _69879) = (term428 _69879).
Proof. exact (TRANS (@lem5399864 _69879) (@lem5399966 _69879)). Qed.
Lemma lem5399968 (_69879 : int) : (term428 _69879) = term133.
Proof. exact (@lem1982719 (real_of_int _69879)). Qed.
Lemma lem5399969 (_69879 : int) : (term433 _69879) = term133.
Proof. exact (TRANS (@lem5399967 _69879) (@lem5399968 _69879)). Qed.
Lemma lem5399970 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5399971 (_69879 : int) : (term434 _69879) = term430.
Proof. exact (MK_COMB (@lem5399970) (@lem5399969 _69879)). Qed.
Lemma lem5399972 (_69880 : int) : (term515 _69880) = (term516 _69880).
Proof. exact (@lem1982763 (real_of_int _69880) (term224 _69880) term186). Qed.
Lemma lem5399973 (_69880 : int) : (term412 _69880) = (term413 _69880).
Proof. exact (@lem1982715 term186 (real_of_int _69880)). Qed.
Lemma lem5399975 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5399976 : term142 = term211.
Proof. exact (@lem5399975 term18). Qed.
Lemma lem5399978 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5399979 : term186 = term187.
Proof. exact (@lem5399978 term18). Qed.
Lemma lem5399980 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5399981 : term414 = term415.
Proof. exact (MK_COMB (@lem5399980) (@lem5399979)). Qed.
Lemma lem5399982 : term416 = term417.
Proof. exact (MK_COMB (@lem5399981) (@lem5399976)). Qed.
Lemma lem5399983 : term418.
Proof. exact (@lem1981473 term186 term142 term142 term142 term133 term142). Qed.
Lemma lem5399985 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399986 : term233 = term234.
Proof. exact (@lem5399985 (NUMERAL 0) term18). Qed.
Lemma lem5399987 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399988 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5399989 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399988 h1) (fun h1 : term234 = True => @lem5399987)). Qed.
Lemma lem5399990 : term234 = True.
Proof. exact (EQ_MP (@lem5399989) (@lem5399987)). Qed.
Lemma lem5399991 : term233 = True.
Proof. exact (TRANS (@lem5399986) (@lem5399990)). Qed.
Lemma lem5399992 : True = term233.
Proof. exact (SYM (@lem5399991)). Qed.
Lemma lem5399993 : term233.
Proof. exact (EQ_MP (@lem5399992) (@lem0)). Qed.
Lemma lem5399994 : term419.
Proof. exact (@lem5399983 (@lem5399993)). Qed.
Lemma lem5399996 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5399997 : term233 = term234.
Proof. exact (@lem5399996 (NUMERAL 0) term18). Qed.
Lemma lem5399998 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5399999 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400000 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5399999 h1) (fun h1 : term234 = True => @lem5399998)). Qed.
Lemma lem5400001 : term234 = True.
Proof. exact (EQ_MP (@lem5400000) (@lem5399998)). Qed.
Lemma lem5400002 : term233 = True.
Proof. exact (TRANS (@lem5399997) (@lem5400001)). Qed.
Lemma lem5400003 : True = term233.
Proof. exact (SYM (@lem5400002)). Qed.
Lemma lem5400004 : term233.
Proof. exact (EQ_MP (@lem5400003) (@lem0)). Qed.
Lemma lem5400005 : term420.
Proof. exact (@lem5399994 (@lem5400004)). Qed.
Lemma lem5400007 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400008 : term233 = term234.
Proof. exact (@lem5400007 (NUMERAL 0) term18). Qed.
Lemma lem5400009 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400010 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400011 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400010 h1) (fun h1 : term234 = True => @lem5400009)). Qed.
Lemma lem5400012 : term234 = True.
Proof. exact (EQ_MP (@lem5400011) (@lem5400009)). Qed.
Lemma lem5400013 : term233 = True.
Proof. exact (TRANS (@lem5400008) (@lem5400012)). Qed.
Lemma lem5400014 : True = term233.
Proof. exact (SYM (@lem5400013)). Qed.
Lemma lem5400015 : term233.
Proof. exact (EQ_MP (@lem5400014) (@lem0)). Qed.
Lemma lem5400016 : term421.
Proof. exact (@lem5400005 (@lem5400015)). Qed.
Lemma lem5400018 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5400019 : term195 = term196.
Proof. exact (@lem5400018 term18 term18). Qed.
Lemma lem5400020 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400021 : term198 = term18.
Proof. exact (EQ_MP (@lem5400020) (@lem940073)). Qed.
Lemma lem5400022 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400023 : term196 = term142.
Proof. exact (MK_COMB (@lem5400022) (@lem5400021)). Qed.
Lemma lem5400024 : term195 = term142.
Proof. exact (TRANS (@lem5400019) (@lem5400023)). Qed.
Lemma lem5400026 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5400027 : term212 = term217.
Proof. exact (@lem5400026 term18 term18). Qed.
Lemma lem5400028 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400029 : term198 = term18.
Proof. exact (EQ_MP (@lem5400028) (@lem940073)). Qed.
Lemma lem5400030 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400031 : term196 = term142.
Proof. exact (MK_COMB (@lem5400030) (@lem5400029)). Qed.
Lemma lem5400032 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5400033 : term217 = term186.
Proof. exact (MK_COMB (@lem5400032) (@lem5400031)). Qed.
Lemma lem5400034 : term212 = term186.
Proof. exact (TRANS (@lem5400027) (@lem5400033)). Qed.
Lemma lem5400035 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5400036 : term422 = term414.
Proof. exact (MK_COMB (@lem5400035) (@lem5400034)). Qed.
Lemma lem5400037 : term423 = term416.
Proof. exact (MK_COMB (@lem5400036) (@lem5400024)). Qed.
Lemma lem5400039 (m : nat) : (term424 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5400040 : term416 = term133.
Proof. exact (@lem5400039 term18). Qed.
Lemma lem5400041 : term423 = term133.
Proof. exact (TRANS (@lem5400037) (@lem5400040)). Qed.
Lemma lem5400042 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5400043 : term425 = term243.
Proof. exact (MK_COMB (@lem5400042) (@lem5400041)). Qed.
Lemma lem5400044 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem5400045 : term426 = term245.
Proof. exact (MK_COMB (@lem5400043) (@lem5400044)). Qed.
Lemma lem5400047 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5400048 : term245 = term133.
Proof. exact (@lem5400047 term18). Qed.
Lemma lem5400049 : term426 = term133.
Proof. exact (TRANS (@lem5400045) (@lem5400048)). Qed.
Lemma lem5400051 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5400052 : term195 = term196.
Proof. exact (@lem5400051 term18 term18). Qed.
Lemma lem5400053 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400054 : term198 = term18.
Proof. exact (EQ_MP (@lem5400053) (@lem940073)). Qed.
Lemma lem5400055 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400056 : term196 = term142.
Proof. exact (MK_COMB (@lem5400055) (@lem5400054)). Qed.
Lemma lem5400057 : term195 = term142.
Proof. exact (TRANS (@lem5400052) (@lem5400056)). Qed.
Lemma lem5400058 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem5400059 : term247 = term245.
Proof. exact (MK_COMB (@lem5400058) (@lem5400057)). Qed.
Lemma lem5400061 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5400062 : term245 = term133.
Proof. exact (@lem5400061 term18). Qed.
Lemma lem5400063 : term247 = term133.
Proof. exact (TRANS (@lem5400059) (@lem5400062)). Qed.
Lemma lem5400064 : term133 = term247.
Proof. exact (SYM (@lem5400063)). Qed.
Lemma lem5400065 : term426 = term247.
Proof. exact (TRANS (@lem5400049) (@lem5400064)). Qed.
Lemma lem5400066 : term417 = term183.
Proof. exact (@lem5400016 (@lem5400065)). Qed.
Lemma lem5400067 : term416 = term183.
Proof. exact (TRANS (@lem5399982) (@lem5400066)). Qed.
Lemma lem5400069 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5400070 : term183 = term133.
Proof. exact (@lem5400069 term133). Qed.
Lemma lem5400071 : term416 = term133.
Proof. exact (TRANS (@lem5400067) (@lem5400070)). Qed.
Lemma lem5400072 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5400073 : term427 = term243.
Proof. exact (MK_COMB (@lem5400072) (@lem5400071)). Qed.
Lemma lem5400074 (_69880 : int) : (real_of_int _69880) = (real_of_int _69880).
Proof. exact (eq_refl (real_of_int _69880)). Qed.
Lemma lem5400075 (_69880 : int) : (term413 _69880) = (term428 _69880).
Proof. exact (MK_COMB (@lem5400073) (@lem5400074 _69880)). Qed.
Lemma lem5400076 (_69880 : int) : (term412 _69880) = (term428 _69880).
Proof. exact (TRANS (@lem5399973 _69880) (@lem5400075 _69880)). Qed.
Lemma lem5400077 (_69880 : int) : (term428 _69880) = term133.
Proof. exact (@lem1982719 (real_of_int _69880)). Qed.
Lemma lem5400078 (_69880 : int) : (term412 _69880) = term133.
Proof. exact (TRANS (@lem5400076 _69880) (@lem5400077 _69880)). Qed.
Lemma lem5400079 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5400080 (_69880 : int) : (term429 _69880) = term430.
Proof. exact (MK_COMB (@lem5400079) (@lem5400078 _69880)). Qed.
Lemma lem5400081 : term186 = term186.
Proof. exact (eq_refl term186). Qed.
Lemma lem5400082 (_69880 : int) : (term516 _69880) = term435.
Proof. exact (MK_COMB (@lem5400080 _69880) (@lem5400081)). Qed.
Lemma lem5400083 (_69880 : int) : (term515 _69880) = term435.
Proof. exact (TRANS (@lem5399972 _69880) (@lem5400082 _69880)). Qed.
Lemma lem5400084 : term435 = term186.
Proof. exact (@lem1982721 term186). Qed.
Lemma lem5400085 (_69880 : int) : (term515 _69880) = term186.
Proof. exact (TRANS (@lem5400083 _69880) (@lem5400084)). Qed.
Lemma lem5400086 (_69879 : int) (_69880 : int) : (term514 _69879 _69880) = term435.
Proof. exact (MK_COMB (@lem5399971 _69879) (@lem5400085 _69880)). Qed.
Lemma lem5400087 (_69879 : int) (_69880 : int) : (term513 _69879 _69880) = term435.
Proof. exact (TRANS (@lem5399863 _69879 _69880) (@lem5400086 _69879 _69880)). Qed.
Lemma lem5400088 : term435 = term186.
Proof. exact (@lem1982721 term186). Qed.
Lemma lem5400089 (_69879 : int) (_69880 : int) : (term513 _69879 _69880) = term186.
Proof. exact (TRANS (@lem5400087 _69879 _69880) (@lem5400088)). Qed.
Lemma lem5400090 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5400091 (_69879 : int) (_69880 : int) : (term517 _69879 _69880) = term437.
Proof. exact (MK_COMB (@lem5400090) (@lem5400089 _69879 _69880)). Qed.
Lemma lem5400092 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5400093 (_69879 : int) (_69880 : int) : (term512 _69879 _69880) = term438.
Proof. exact (MK_COMB (@lem5400091 _69879 _69880) (@lem5400092)). Qed.
Lemma lem5400094 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : term438.
Proof. exact (EQ_MP (@lem5400093 _69879 _69880) (@lem5399862 _69879 _69880 h1)). Qed.
Lemma lem5400096 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5400097 : term438 = term439.
Proof. exact (@lem5400096 term133 term186). Qed.
Lemma lem5400099 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5400100 : term186 = term187.
Proof. exact (@lem5400099 term18). Qed.
Lemma lem5400102 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5400103 : term133 = term183.
Proof. exact (@lem5400102 (NUMERAL 0)). Qed.
Lemma lem5400104 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5400105 : term135 = term440.
Proof. exact (MK_COMB (@lem5400104) (@lem5400103)). Qed.
Lemma lem5400106 : term439 = term441.
Proof. exact (MK_COMB (@lem5400105) (@lem5400100)). Qed.
Lemma lem5400107 : term442.
Proof. exact (@lem1980026 term133 term142 term186 term142). Qed.
Lemma lem5400109 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400110 : term233 = term234.
Proof. exact (@lem5400109 (NUMERAL 0) term18). Qed.
Lemma lem5400111 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400112 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400113 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400112 h1) (fun h1 : term234 = True => @lem5400111)). Qed.
Lemma lem5400114 : term234 = True.
Proof. exact (EQ_MP (@lem5400113) (@lem5400111)). Qed.
Lemma lem5400115 : term233 = True.
Proof. exact (TRANS (@lem5400110) (@lem5400114)). Qed.
Lemma lem5400116 : True = term233.
Proof. exact (SYM (@lem5400115)). Qed.
Lemma lem5400117 : term233.
Proof. exact (EQ_MP (@lem5400116) (@lem0)). Qed.
Lemma lem5400118 : term443.
Proof. exact (@lem5400107 (@lem5400117)). Qed.
Lemma lem5400120 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400121 : term233 = term234.
Proof. exact (@lem5400120 (NUMERAL 0) term18). Qed.
Lemma lem5400122 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400123 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400124 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400123 h1) (fun h1 : term234 = True => @lem5400122)). Qed.
Lemma lem5400125 : term234 = True.
Proof. exact (EQ_MP (@lem5400124) (@lem5400122)). Qed.
Lemma lem5400126 : term233 = True.
Proof. exact (TRANS (@lem5400121) (@lem5400125)). Qed.
Lemma lem5400127 : True = term233.
Proof. exact (SYM (@lem5400126)). Qed.
Lemma lem5400128 : term233.
Proof. exact (EQ_MP (@lem5400127) (@lem0)). Qed.
Lemma lem5400129 : term441 = term444.
Proof. exact (@lem5400118 (@lem5400128)). Qed.
Lemma lem5400131 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5400132 : term212 = term217.
Proof. exact (@lem5400131 term18 term18). Qed.
Lemma lem5400133 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400134 : term198 = term18.
Proof. exact (EQ_MP (@lem5400133) (@lem940073)). Qed.
Lemma lem5400135 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400136 : term196 = term142.
Proof. exact (MK_COMB (@lem5400135) (@lem5400134)). Qed.
Lemma lem5400137 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5400138 : term217 = term186.
Proof. exact (MK_COMB (@lem5400137) (@lem5400136)). Qed.
Lemma lem5400139 : term212 = term186.
Proof. exact (TRANS (@lem5400132) (@lem5400138)). Qed.
Lemma lem5400141 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5400142 : term245 = term133.
Proof. exact (@lem5400141 term18). Qed.
Lemma lem5400143 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5400144 : term445 = term135.
Proof. exact (MK_COMB (@lem5400143) (@lem5400142)). Qed.
Lemma lem5400145 : term444 = term439.
Proof. exact (MK_COMB (@lem5400144) (@lem5400139)). Qed.
Lemma lem5400147 (m : nat) (n : nat) : (term446 m n) = (term447 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5400148 : term439 = term448.
Proof. exact (@lem5400147 (NUMERAL 0) term18). Qed.
Lemma lem5400149 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400150 (h1 : term235 = (BIT1 0)) : (term18 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5400151 : (term235 = (BIT1 0)) = ((term18 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400150 h1) (fun h1 : (term18 = (NUMERAL 0)) = False => @lem5400149)). Qed.
Lemma lem5400152 : (term18 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5400151) (@lem5400149)). Qed.
Lemma lem5400153 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5400154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5400155 : term449 = (and True).
Proof. exact (MK_COMB (@lem5400154) (@lem5400153)). Qed.
Lemma lem5400156 : term448 = (True /\ False).
Proof. exact (MK_COMB (@lem5400155) (@lem5400152)). Qed.
Lemma lem5400158 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5400159 : term448 = False.
Proof. exact (TRANS (@lem5400156) (@lem5400158)). Qed.
Lemma lem5400160 : term439 = False.
Proof. exact (TRANS (@lem5400148) (@lem5400159)). Qed.
Lemma lem5400161 : term444 = False.
Proof. exact (TRANS (@lem5400145) (@lem5400160)). Qed.
Lemma lem5400162 : term441 = False.
Proof. exact (TRANS (@lem5400129) (@lem5400161)). Qed.
Lemma lem5400163 : term439 = False.
Proof. exact (TRANS (@lem5400106) (@lem5400162)). Qed.
Lemma lem5400164 : term438 = False.
Proof. exact (TRANS (@lem5400097) (@lem5400163)). Qed.
Lemma lem5400165 (_69879 : int) (_69880 : int) (h1 : term502 _69879 _69880) : False.
Proof. exact (EQ_MP (@lem5400164) (@lem5400094 _69879 _69880 h1)). Qed.
Lemma lem5400166 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term518 _69879 _69880.
Proof. exact (h1). Qed.
Lemma lem5400167 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term361 _69879 _69880.
Proof. exact (proj2 (@lem5400166 _69879 _69880 h1)). Qed.
Lemma lem5400169 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term348 _69879 _69880.
Proof. exact (proj2 (@lem5400167 _69879 _69880 h1)). Qed.
Lemma lem5400170 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term206 _69880.
Proof. exact (proj1 (@lem5400167 _69879 _69880 h1)). Qed.
Lemma lem5400171 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term327 _69879 _69880.
Proof. exact (proj2 (@lem5400169 _69879 _69880 h1)). Qed.
Lemma lem5400172 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term315 _69880 _69879.
Proof. exact (proj1 (@lem5400169 _69879 _69880 h1)). Qed.
Lemma lem5400173 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : (real_of_int _69879) = term133.
Proof. exact (proj2 (@lem5400172 _69879 _69880 h1)). Qed.
Lemma lem5400176 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5400177 : term370 = term233.
Proof. exact (@lem5400176 term133 term142). Qed.
Lemma lem5400179 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5400180 : term142 = term211.
Proof. exact (@lem5400179 term18). Qed.
Lemma lem5400182 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5400183 : term133 = term183.
Proof. exact (@lem5400182 (NUMERAL 0)). Qed.
Lemma lem5400184 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5400185 : term371 = term372.
Proof. exact (MK_COMB (@lem5400184) (@lem5400183)). Qed.
Lemma lem5400186 : term233 = term373.
Proof. exact (MK_COMB (@lem5400185) (@lem5400180)). Qed.
Lemma lem5400187 : term374.
Proof. exact (@lem1980255 term133 term142 term142 term142). Qed.
Lemma lem5400189 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400190 : term233 = term234.
Proof. exact (@lem5400189 (NUMERAL 0) term18). Qed.
Lemma lem5400191 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400192 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400193 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400192 h1) (fun h1 : term234 = True => @lem5400191)). Qed.
Lemma lem5400194 : term234 = True.
Proof. exact (EQ_MP (@lem5400193) (@lem5400191)). Qed.
Lemma lem5400195 : term233 = True.
Proof. exact (TRANS (@lem5400190) (@lem5400194)). Qed.
Lemma lem5400196 : True = term233.
Proof. exact (SYM (@lem5400195)). Qed.
Lemma lem5400197 : term233.
Proof. exact (EQ_MP (@lem5400196) (@lem0)). Qed.
Lemma lem5400198 : term375.
Proof. exact (@lem5400187 (@lem5400197)). Qed.
Lemma lem5400200 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400201 : term233 = term234.
Proof. exact (@lem5400200 (NUMERAL 0) term18). Qed.
Lemma lem5400202 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400203 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400204 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400203 h1) (fun h1 : term234 = True => @lem5400202)). Qed.
Lemma lem5400205 : term234 = True.
Proof. exact (EQ_MP (@lem5400204) (@lem5400202)). Qed.
Lemma lem5400206 : term233 = True.
Proof. exact (TRANS (@lem5400201) (@lem5400205)). Qed.
Lemma lem5400207 : True = term233.
Proof. exact (SYM (@lem5400206)). Qed.
Lemma lem5400208 : term233.
Proof. exact (EQ_MP (@lem5400207) (@lem0)). Qed.
Lemma lem5400209 : term373 = term376.
Proof. exact (@lem5400198 (@lem5400208)). Qed.
Lemma lem5400211 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5400212 : term195 = term196.
Proof. exact (@lem5400211 term18 term18). Qed.
Lemma lem5400213 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400214 : term198 = term18.
Proof. exact (EQ_MP (@lem5400213) (@lem940073)). Qed.
Lemma lem5400215 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400216 : term196 = term142.
Proof. exact (MK_COMB (@lem5400215) (@lem5400214)). Qed.
Lemma lem5400217 : term195 = term142.
Proof. exact (TRANS (@lem5400212) (@lem5400216)). Qed.
Lemma lem5400219 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5400220 : term245 = term133.
Proof. exact (@lem5400219 term18). Qed.
Lemma lem5400221 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5400222 : term377 = term371.
Proof. exact (MK_COMB (@lem5400221) (@lem5400220)). Qed.
Lemma lem5400223 : term376 = term233.
Proof. exact (MK_COMB (@lem5400222) (@lem5400217)). Qed.
Lemma lem5400225 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400226 : term233 = term234.
Proof. exact (@lem5400225 (NUMERAL 0) term18). Qed.
Lemma lem5400227 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400228 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400229 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400228 h1) (fun h1 : term234 = True => @lem5400227)). Qed.
Lemma lem5400230 : term234 = True.
Proof. exact (EQ_MP (@lem5400229) (@lem5400227)). Qed.
Lemma lem5400231 : term233 = True.
Proof. exact (TRANS (@lem5400226) (@lem5400230)). Qed.
Lemma lem5400232 : term376 = True.
Proof. exact (TRANS (@lem5400223) (@lem5400231)). Qed.
Lemma lem5400233 : term373 = True.
Proof. exact (TRANS (@lem5400209) (@lem5400232)). Qed.
Lemma lem5400234 : term233 = True.
Proof. exact (TRANS (@lem5400186) (@lem5400233)). Qed.
Lemma lem5400235 : term370 = True.
Proof. exact (TRANS (@lem5400177) (@lem5400234)). Qed.
Lemma lem5400236 : True = term370.
Proof. exact (SYM (@lem5400235)). Qed.
Lemma lem5400237 : term370.
Proof. exact (EQ_MP (@lem5400236) (@lem0)). Qed.
Lemma lem5400238 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term519 _69880.
Proof. exact (conj (@lem5400237) (@lem5400170 _69879 _69880 h1)). Qed.
Lemma lem5400240 (x : real) (y : real) : term379 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5400241 (_69880 : int) : term520 _69880.
Proof. exact (@lem5400240 term142 (real_of_int _69880)). Qed.
Lemma lem5400242 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term521 _69880.
Proof. exact (@lem5400241 _69880 (@lem5400238 _69879 _69880 h1)). Qed.
Lemma lem5400243 (_69880 : int) : (term400 _69880) = (real_of_int _69880).
Proof. exact (@lem1982733 (real_of_int _69880)). Qed.
Lemma lem5400244 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5400245 (_69880 : int) : (term522 _69880) = (term205 _69880).
Proof. exact (MK_COMB (@lem5400244) (@lem5400243 _69880)). Qed.
Lemma lem5400246 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5400247 (_69880 : int) : (term521 _69880) = (term206 _69880).
Proof. exact (MK_COMB (@lem5400245 _69880) (@lem5400246)). Qed.
Lemma lem5400248 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term206 _69880.
Proof. exact (EQ_MP (@lem5400247 _69880) (@lem5400242 _69879 _69880 h1)). Qed.
Lemma lem5400250 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5400251 : term370 = term233.
Proof. exact (@lem5400250 term133 term142). Qed.
Lemma lem5400253 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5400254 : term142 = term211.
Proof. exact (@lem5400253 term18). Qed.
Lemma lem5400256 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5400257 : term133 = term183.
Proof. exact (@lem5400256 (NUMERAL 0)). Qed.
Lemma lem5400258 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5400259 : term371 = term372.
Proof. exact (MK_COMB (@lem5400258) (@lem5400257)). Qed.
Lemma lem5400260 : term233 = term373.
Proof. exact (MK_COMB (@lem5400259) (@lem5400254)). Qed.
Lemma lem5400261 : term374.
Proof. exact (@lem1980255 term133 term142 term142 term142). Qed.
Lemma lem5400263 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400264 : term233 = term234.
Proof. exact (@lem5400263 (NUMERAL 0) term18). Qed.
Lemma lem5400265 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400266 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400267 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400266 h1) (fun h1 : term234 = True => @lem5400265)). Qed.
Lemma lem5400268 : term234 = True.
Proof. exact (EQ_MP (@lem5400267) (@lem5400265)). Qed.
Lemma lem5400269 : term233 = True.
Proof. exact (TRANS (@lem5400264) (@lem5400268)). Qed.
Lemma lem5400270 : True = term233.
Proof. exact (SYM (@lem5400269)). Qed.
Lemma lem5400271 : term233.
Proof. exact (EQ_MP (@lem5400270) (@lem0)). Qed.
Lemma lem5400272 : term375.
Proof. exact (@lem5400261 (@lem5400271)). Qed.
Lemma lem5400274 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400275 : term233 = term234.
Proof. exact (@lem5400274 (NUMERAL 0) term18). Qed.
Lemma lem5400276 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400277 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400278 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400277 h1) (fun h1 : term234 = True => @lem5400276)). Qed.
Lemma lem5400279 : term234 = True.
Proof. exact (EQ_MP (@lem5400278) (@lem5400276)). Qed.
Lemma lem5400280 : term233 = True.
Proof. exact (TRANS (@lem5400275) (@lem5400279)). Qed.
Lemma lem5400281 : True = term233.
Proof. exact (SYM (@lem5400280)). Qed.
Lemma lem5400282 : term233.
Proof. exact (EQ_MP (@lem5400281) (@lem0)). Qed.
Lemma lem5400283 : term373 = term376.
Proof. exact (@lem5400272 (@lem5400282)). Qed.
Lemma lem5400285 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5400286 : term195 = term196.
Proof. exact (@lem5400285 term18 term18). Qed.
Lemma lem5400287 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400288 : term198 = term18.
Proof. exact (EQ_MP (@lem5400287) (@lem940073)). Qed.
Lemma lem5400289 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400290 : term196 = term142.
Proof. exact (MK_COMB (@lem5400289) (@lem5400288)). Qed.
Lemma lem5400291 : term195 = term142.
Proof. exact (TRANS (@lem5400286) (@lem5400290)). Qed.
Lemma lem5400293 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5400294 : term245 = term133.
Proof. exact (@lem5400293 term18). Qed.
Lemma lem5400295 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5400296 : term377 = term371.
Proof. exact (MK_COMB (@lem5400295) (@lem5400294)). Qed.
Lemma lem5400297 : term376 = term233.
Proof. exact (MK_COMB (@lem5400296) (@lem5400291)). Qed.
Lemma lem5400299 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400300 : term233 = term234.
Proof. exact (@lem5400299 (NUMERAL 0) term18). Qed.
Lemma lem5400301 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400302 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400303 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400302 h1) (fun h1 : term234 = True => @lem5400301)). Qed.
Lemma lem5400304 : term234 = True.
Proof. exact (EQ_MP (@lem5400303) (@lem5400301)). Qed.
Lemma lem5400305 : term233 = True.
Proof. exact (TRANS (@lem5400300) (@lem5400304)). Qed.
Lemma lem5400306 : term376 = True.
Proof. exact (TRANS (@lem5400297) (@lem5400305)). Qed.
Lemma lem5400307 : term373 = True.
Proof. exact (TRANS (@lem5400283) (@lem5400306)). Qed.
Lemma lem5400308 : term233 = True.
Proof. exact (TRANS (@lem5400260) (@lem5400307)). Qed.
Lemma lem5400309 : term370 = True.
Proof. exact (TRANS (@lem5400251) (@lem5400308)). Qed.
Lemma lem5400310 : True = term370.
Proof. exact (SYM (@lem5400309)). Qed.
Lemma lem5400311 : term370.
Proof. exact (EQ_MP (@lem5400310) (@lem0)). Qed.
Lemma lem5400312 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term503 _69879 _69880.
Proof. exact (conj (@lem5400311) (@lem5400171 _69879 _69880 h1)). Qed.
Lemma lem5400314 (x : real) (y : real) : term379 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5400315 (_69879 : int) (_69880 : int) : term504 _69879 _69880.
Proof. exact (@lem5400314 term142 (term321 _69879 _69880)). Qed.
Lemma lem5400316 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term505 _69879 _69880.
Proof. exact (@lem5400315 _69879 _69880 (@lem5400312 _69879 _69880 h1)). Qed.
Lemma lem5400317 (_69879 : int) (_69880 : int) : (term506 _69879 _69880) = (term321 _69879 _69880).
Proof. exact (@lem1982733 (term321 _69879 _69880)). Qed.
Lemma lem5400318 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5400319 (_69879 : int) (_69880 : int) : (term507 _69879 _69880) = (term326 _69879 _69880).
Proof. exact (MK_COMB (@lem5400318) (@lem5400317 _69879 _69880)). Qed.
Lemma lem5400320 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5400321 (_69879 : int) (_69880 : int) : (term505 _69879 _69880) = (term327 _69879 _69880).
Proof. exact (MK_COMB (@lem5400319 _69879 _69880) (@lem5400320)). Qed.
Lemma lem5400322 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term327 _69879 _69880.
Proof. exact (EQ_MP (@lem5400321 _69879 _69880) (@lem5400316 _69879 _69880 h1)). Qed.
Lemma lem5400324 (y : real) : term384 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5400325 (_69879 : int) : term451 _69879.
Proof. exact (@lem5400324 (real_of_int _69879)). Qed.
Lemma lem5400326 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term452 _69879.
Proof. exact (@lem5400325 _69879 (@lem5400173 _69879 _69880 h1)). Qed.
Lemma lem5400327 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term523 _69879.
Proof. exact (@lem5400326 _69879 _69880 h1 term186). Qed.
Lemma lem5400328 (_69879 : int) : (term523 _69879) = ((term224 _69879) = term133).
Proof. exact (eq_refl (term523 _69879)). Qed.
Lemma lem5400335 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : (term224 _69879) = term133.
Proof. exact (EQ_MP (@lem5400328 _69879) (@lem5400327 _69879 _69880 h1)). Qed.
Lemma lem5400336 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term524 _69879 _69880.
Proof. exact (conj (@lem5400335 _69879 _69880 h1) (@lem5400322 _69879 _69880 h1)). Qed.
Lemma lem5400338 (x : real) (y : real) : term406 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5400339 (_69879 : int) (_69880 : int) : term525 _69879 _69880.
Proof. exact (@lem5400338 (term224 _69879) (term321 _69879 _69880)). Qed.
Lemma lem5400340 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term526 _69879 _69880.
Proof. exact (@lem5400339 _69879 _69880 (@lem5400336 _69879 _69880 h1)). Qed.
Lemma lem5400341 (_69879 : int) (_69880 : int) : (term527 _69879 _69880) = (term528 _69879 _69880).
Proof. exact (@lem1982763 (term224 _69879) (real_of_int _69879) (term221 _69880)). Qed.
Lemma lem5400342 (_69879 : int) : (term433 _69879) = (term413 _69879).
Proof. exact (@lem1982713 term186 (real_of_int _69879)). Qed.
Lemma lem5400344 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5400345 : term142 = term211.
Proof. exact (@lem5400344 term18). Qed.
Lemma lem5400347 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5400348 : term186 = term187.
Proof. exact (@lem5400347 term18). Qed.
Lemma lem5400349 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5400350 : term414 = term415.
Proof. exact (MK_COMB (@lem5400349) (@lem5400348)). Qed.
Lemma lem5400351 : term416 = term417.
Proof. exact (MK_COMB (@lem5400350) (@lem5400345)). Qed.
Lemma lem5400352 : term418.
Proof. exact (@lem1981473 term186 term142 term142 term142 term133 term142). Qed.
Lemma lem5400354 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400355 : term233 = term234.
Proof. exact (@lem5400354 (NUMERAL 0) term18). Qed.
Lemma lem5400356 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400357 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400358 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400357 h1) (fun h1 : term234 = True => @lem5400356)). Qed.
Lemma lem5400359 : term234 = True.
Proof. exact (EQ_MP (@lem5400358) (@lem5400356)). Qed.
Lemma lem5400360 : term233 = True.
Proof. exact (TRANS (@lem5400355) (@lem5400359)). Qed.
Lemma lem5400361 : True = term233.
Proof. exact (SYM (@lem5400360)). Qed.
Lemma lem5400362 : term233.
Proof. exact (EQ_MP (@lem5400361) (@lem0)). Qed.
Lemma lem5400363 : term419.
Proof. exact (@lem5400352 (@lem5400362)). Qed.
Lemma lem5400365 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400366 : term233 = term234.
Proof. exact (@lem5400365 (NUMERAL 0) term18). Qed.
Lemma lem5400367 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400368 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400369 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400368 h1) (fun h1 : term234 = True => @lem5400367)). Qed.
Lemma lem5400370 : term234 = True.
Proof. exact (EQ_MP (@lem5400369) (@lem5400367)). Qed.
Lemma lem5400371 : term233 = True.
Proof. exact (TRANS (@lem5400366) (@lem5400370)). Qed.
Lemma lem5400372 : True = term233.
Proof. exact (SYM (@lem5400371)). Qed.
Lemma lem5400373 : term233.
Proof. exact (EQ_MP (@lem5400372) (@lem0)). Qed.
Lemma lem5400374 : term420.
Proof. exact (@lem5400363 (@lem5400373)). Qed.
Lemma lem5400376 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400377 : term233 = term234.
Proof. exact (@lem5400376 (NUMERAL 0) term18). Qed.
Lemma lem5400378 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400379 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400380 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400379 h1) (fun h1 : term234 = True => @lem5400378)). Qed.
Lemma lem5400381 : term234 = True.
Proof. exact (EQ_MP (@lem5400380) (@lem5400378)). Qed.
Lemma lem5400382 : term233 = True.
Proof. exact (TRANS (@lem5400377) (@lem5400381)). Qed.
Lemma lem5400383 : True = term233.
Proof. exact (SYM (@lem5400382)). Qed.
Lemma lem5400384 : term233.
Proof. exact (EQ_MP (@lem5400383) (@lem0)). Qed.
Lemma lem5400385 : term421.
Proof. exact (@lem5400374 (@lem5400384)). Qed.
Lemma lem5400387 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5400388 : term195 = term196.
Proof. exact (@lem5400387 term18 term18). Qed.
Lemma lem5400389 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400390 : term198 = term18.
Proof. exact (EQ_MP (@lem5400389) (@lem940073)). Qed.
Lemma lem5400391 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400392 : term196 = term142.
Proof. exact (MK_COMB (@lem5400391) (@lem5400390)). Qed.
Lemma lem5400393 : term195 = term142.
Proof. exact (TRANS (@lem5400388) (@lem5400392)). Qed.
Lemma lem5400395 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5400396 : term212 = term217.
Proof. exact (@lem5400395 term18 term18). Qed.
Lemma lem5400397 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400398 : term198 = term18.
Proof. exact (EQ_MP (@lem5400397) (@lem940073)). Qed.
Lemma lem5400399 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400400 : term196 = term142.
Proof. exact (MK_COMB (@lem5400399) (@lem5400398)). Qed.
Lemma lem5400401 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5400402 : term217 = term186.
Proof. exact (MK_COMB (@lem5400401) (@lem5400400)). Qed.
Lemma lem5400403 : term212 = term186.
Proof. exact (TRANS (@lem5400396) (@lem5400402)). Qed.
Lemma lem5400404 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5400405 : term422 = term414.
Proof. exact (MK_COMB (@lem5400404) (@lem5400403)). Qed.
Lemma lem5400406 : term423 = term416.
Proof. exact (MK_COMB (@lem5400405) (@lem5400393)). Qed.
Lemma lem5400408 (m : nat) : (term424 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5400409 : term416 = term133.
Proof. exact (@lem5400408 term18). Qed.
Lemma lem5400410 : term423 = term133.
Proof. exact (TRANS (@lem5400406) (@lem5400409)). Qed.
Lemma lem5400411 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5400412 : term425 = term243.
Proof. exact (MK_COMB (@lem5400411) (@lem5400410)). Qed.
Lemma lem5400413 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem5400414 : term426 = term245.
Proof. exact (MK_COMB (@lem5400412) (@lem5400413)). Qed.
Lemma lem5400416 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5400417 : term245 = term133.
Proof. exact (@lem5400416 term18). Qed.
Lemma lem5400418 : term426 = term133.
Proof. exact (TRANS (@lem5400414) (@lem5400417)). Qed.
Lemma lem5400420 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5400421 : term195 = term196.
Proof. exact (@lem5400420 term18 term18). Qed.
Lemma lem5400422 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400423 : term198 = term18.
Proof. exact (EQ_MP (@lem5400422) (@lem940073)). Qed.
Lemma lem5400424 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400425 : term196 = term142.
Proof. exact (MK_COMB (@lem5400424) (@lem5400423)). Qed.
Lemma lem5400426 : term195 = term142.
Proof. exact (TRANS (@lem5400421) (@lem5400425)). Qed.
Lemma lem5400427 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem5400428 : term247 = term245.
Proof. exact (MK_COMB (@lem5400427) (@lem5400426)). Qed.
Lemma lem5400430 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5400431 : term245 = term133.
Proof. exact (@lem5400430 term18). Qed.
Lemma lem5400432 : term247 = term133.
Proof. exact (TRANS (@lem5400428) (@lem5400431)). Qed.
Lemma lem5400433 : term133 = term247.
Proof. exact (SYM (@lem5400432)). Qed.
Lemma lem5400434 : term426 = term247.
Proof. exact (TRANS (@lem5400418) (@lem5400433)). Qed.
Lemma lem5400435 : term417 = term183.
Proof. exact (@lem5400385 (@lem5400434)). Qed.
Lemma lem5400436 : term416 = term183.
Proof. exact (TRANS (@lem5400351) (@lem5400435)). Qed.
Lemma lem5400438 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5400439 : term183 = term133.
Proof. exact (@lem5400438 term133). Qed.
Lemma lem5400440 : term416 = term133.
Proof. exact (TRANS (@lem5400436) (@lem5400439)). Qed.
Lemma lem5400441 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5400442 : term427 = term243.
Proof. exact (MK_COMB (@lem5400441) (@lem5400440)). Qed.
Lemma lem5400443 (_69879 : int) : (real_of_int _69879) = (real_of_int _69879).
Proof. exact (eq_refl (real_of_int _69879)). Qed.
Lemma lem5400444 (_69879 : int) : (term413 _69879) = (term428 _69879).
Proof. exact (MK_COMB (@lem5400442) (@lem5400443 _69879)). Qed.
Lemma lem5400445 (_69879 : int) : (term433 _69879) = (term428 _69879).
Proof. exact (TRANS (@lem5400342 _69879) (@lem5400444 _69879)). Qed.
Lemma lem5400446 (_69879 : int) : (term428 _69879) = term133.
Proof. exact (@lem1982719 (real_of_int _69879)). Qed.
Lemma lem5400447 (_69879 : int) : (term433 _69879) = term133.
Proof. exact (TRANS (@lem5400445 _69879) (@lem5400446 _69879)). Qed.
Lemma lem5400448 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5400449 (_69879 : int) : (term434 _69879) = term430.
Proof. exact (MK_COMB (@lem5400448) (@lem5400447 _69879)). Qed.
Lemma lem5400450 (_69880 : int) : (term221 _69880) = (term221 _69880).
Proof. exact (eq_refl (term221 _69880)). Qed.
Lemma lem5400451 (_69879 : int) (_69880 : int) : (term528 _69879 _69880) = (term529 _69880).
Proof. exact (MK_COMB (@lem5400449 _69879) (@lem5400450 _69880)). Qed.
Lemma lem5400452 (_69879 : int) (_69880 : int) : (term527 _69879 _69880) = (term529 _69880).
Proof. exact (TRANS (@lem5400341 _69879 _69880) (@lem5400451 _69879 _69880)). Qed.
Lemma lem5400453 (_69880 : int) : (term529 _69880) = (term221 _69880).
Proof. exact (@lem1982721 (term221 _69880)). Qed.
Lemma lem5400454 (_69879 : int) (_69880 : int) : (term527 _69879 _69880) = (term221 _69880).
Proof. exact (TRANS (@lem5400452 _69879 _69880) (@lem5400453 _69880)). Qed.
Lemma lem5400455 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5400456 (_69879 : int) (_69880 : int) : (term530 _69879 _69880) = (term311 _69880).
Proof. exact (MK_COMB (@lem5400455) (@lem5400454 _69879 _69880)). Qed.
Lemma lem5400457 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5400458 (_69879 : int) (_69880 : int) : (term526 _69879 _69880) = (term312 _69880).
Proof. exact (MK_COMB (@lem5400456 _69879 _69880) (@lem5400457)). Qed.
Lemma lem5400459 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term312 _69880.
Proof. exact (EQ_MP (@lem5400458 _69879 _69880) (@lem5400340 _69879 _69880 h1)). Qed.
Lemma lem5400461 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5400462 : term370 = term233.
Proof. exact (@lem5400461 term133 term142). Qed.
Lemma lem5400464 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5400465 : term142 = term211.
Proof. exact (@lem5400464 term18). Qed.
Lemma lem5400467 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5400468 : term133 = term183.
Proof. exact (@lem5400467 (NUMERAL 0)). Qed.
Lemma lem5400469 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5400470 : term371 = term372.
Proof. exact (MK_COMB (@lem5400469) (@lem5400468)). Qed.
Lemma lem5400471 : term233 = term373.
Proof. exact (MK_COMB (@lem5400470) (@lem5400465)). Qed.
Lemma lem5400472 : term374.
Proof. exact (@lem1980255 term133 term142 term142 term142). Qed.
Lemma lem5400474 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400475 : term233 = term234.
Proof. exact (@lem5400474 (NUMERAL 0) term18). Qed.
Lemma lem5400476 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400477 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400478 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400477 h1) (fun h1 : term234 = True => @lem5400476)). Qed.
Lemma lem5400479 : term234 = True.
Proof. exact (EQ_MP (@lem5400478) (@lem5400476)). Qed.
Lemma lem5400480 : term233 = True.
Proof. exact (TRANS (@lem5400475) (@lem5400479)). Qed.
Lemma lem5400481 : True = term233.
Proof. exact (SYM (@lem5400480)). Qed.
Lemma lem5400482 : term233.
Proof. exact (EQ_MP (@lem5400481) (@lem0)). Qed.
Lemma lem5400483 : term375.
Proof. exact (@lem5400472 (@lem5400482)). Qed.
Lemma lem5400485 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400486 : term233 = term234.
Proof. exact (@lem5400485 (NUMERAL 0) term18). Qed.
Lemma lem5400487 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400488 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400489 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400488 h1) (fun h1 : term234 = True => @lem5400487)). Qed.
Lemma lem5400490 : term234 = True.
Proof. exact (EQ_MP (@lem5400489) (@lem5400487)). Qed.
Lemma lem5400491 : term233 = True.
Proof. exact (TRANS (@lem5400486) (@lem5400490)). Qed.
Lemma lem5400492 : True = term233.
Proof. exact (SYM (@lem5400491)). Qed.
Lemma lem5400493 : term233.
Proof. exact (EQ_MP (@lem5400492) (@lem0)). Qed.
Lemma lem5400494 : term373 = term376.
Proof. exact (@lem5400483 (@lem5400493)). Qed.
Lemma lem5400496 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5400497 : term195 = term196.
Proof. exact (@lem5400496 term18 term18). Qed.
Lemma lem5400498 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400499 : term198 = term18.
Proof. exact (EQ_MP (@lem5400498) (@lem940073)). Qed.
Lemma lem5400500 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400501 : term196 = term142.
Proof. exact (MK_COMB (@lem5400500) (@lem5400499)). Qed.
Lemma lem5400502 : term195 = term142.
Proof. exact (TRANS (@lem5400497) (@lem5400501)). Qed.
Lemma lem5400504 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5400505 : term245 = term133.
Proof. exact (@lem5400504 term18). Qed.
Lemma lem5400506 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5400507 : term377 = term371.
Proof. exact (MK_COMB (@lem5400506) (@lem5400505)). Qed.
Lemma lem5400508 : term376 = term233.
Proof. exact (MK_COMB (@lem5400507) (@lem5400502)). Qed.
Lemma lem5400510 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400511 : term233 = term234.
Proof. exact (@lem5400510 (NUMERAL 0) term18). Qed.
Lemma lem5400512 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400513 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400514 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400513 h1) (fun h1 : term234 = True => @lem5400512)). Qed.
Lemma lem5400515 : term234 = True.
Proof. exact (EQ_MP (@lem5400514) (@lem5400512)). Qed.
Lemma lem5400516 : term233 = True.
Proof. exact (TRANS (@lem5400511) (@lem5400515)). Qed.
Lemma lem5400517 : term376 = True.
Proof. exact (TRANS (@lem5400508) (@lem5400516)). Qed.
Lemma lem5400518 : term373 = True.
Proof. exact (TRANS (@lem5400494) (@lem5400517)). Qed.
Lemma lem5400519 : term233 = True.
Proof. exact (TRANS (@lem5400471) (@lem5400518)). Qed.
Lemma lem5400520 : term370 = True.
Proof. exact (TRANS (@lem5400462) (@lem5400519)). Qed.
Lemma lem5400521 : True = term370.
Proof. exact (SYM (@lem5400520)). Qed.
Lemma lem5400522 : term370.
Proof. exact (EQ_MP (@lem5400521) (@lem0)). Qed.
Lemma lem5400523 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term469 _69880.
Proof. exact (conj (@lem5400522) (@lem5400459 _69879 _69880 h1)). Qed.
Lemma lem5400525 (x : real) (y : real) : term379 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5400526 (_69880 : int) : term470 _69880.
Proof. exact (@lem5400525 term142 (term221 _69880)). Qed.
Lemma lem5400527 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term471 _69880.
Proof. exact (@lem5400526 _69880 (@lem5400523 _69879 _69880 h1)). Qed.
Lemma lem5400528 (_69880 : int) : (term472 _69880) = (term221 _69880).
Proof. exact (@lem1982733 (term221 _69880)). Qed.
Lemma lem5400529 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5400530 (_69880 : int) : (term473 _69880) = (term311 _69880).
Proof. exact (MK_COMB (@lem5400529) (@lem5400528 _69880)). Qed.
Lemma lem5400531 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5400532 (_69880 : int) : (term471 _69880) = (term312 _69880).
Proof. exact (MK_COMB (@lem5400530 _69880) (@lem5400531)). Qed.
Lemma lem5400533 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term312 _69880.
Proof. exact (EQ_MP (@lem5400532 _69880) (@lem5400527 _69879 _69880 h1)). Qed.
Lemma lem5400534 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term531 _69880.
Proof. exact (conj (@lem5400533 _69879 _69880 h1) (@lem5400248 _69879 _69880 h1)). Qed.
Lemma lem5400536 (x : real) (y : real) : term475 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5400537 (_69880 : int) : term532 _69880.
Proof. exact (@lem5400536 (term221 _69880) (real_of_int _69880)). Qed.
Lemma lem5400538 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term533 _69880.
Proof. exact (@lem5400537 _69880 (@lem5400534 _69879 _69880 h1)). Qed.
Lemma lem5400539 (_69880 : int) : (term534 _69880) = (term432 _69880).
Proof. exact (@lem1982759 (term224 _69880) (real_of_int _69880) term186). Qed.
Lemma lem5400540 (_69880 : int) : (term433 _69880) = (term413 _69880).
Proof. exact (@lem1982713 term186 (real_of_int _69880)). Qed.
Lemma lem5400542 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5400543 : term142 = term211.
Proof. exact (@lem5400542 term18). Qed.
Lemma lem5400545 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5400546 : term186 = term187.
Proof. exact (@lem5400545 term18). Qed.
Lemma lem5400547 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5400548 : term414 = term415.
Proof. exact (MK_COMB (@lem5400547) (@lem5400546)). Qed.
Lemma lem5400549 : term416 = term417.
Proof. exact (MK_COMB (@lem5400548) (@lem5400543)). Qed.
Lemma lem5400550 : term418.
Proof. exact (@lem1981473 term186 term142 term142 term142 term133 term142). Qed.
Lemma lem5400552 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400553 : term233 = term234.
Proof. exact (@lem5400552 (NUMERAL 0) term18). Qed.
Lemma lem5400554 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400555 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400556 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400555 h1) (fun h1 : term234 = True => @lem5400554)). Qed.
Lemma lem5400557 : term234 = True.
Proof. exact (EQ_MP (@lem5400556) (@lem5400554)). Qed.
Lemma lem5400558 : term233 = True.
Proof. exact (TRANS (@lem5400553) (@lem5400557)). Qed.
Lemma lem5400559 : True = term233.
Proof. exact (SYM (@lem5400558)). Qed.
Lemma lem5400560 : term233.
Proof. exact (EQ_MP (@lem5400559) (@lem0)). Qed.
Lemma lem5400561 : term419.
Proof. exact (@lem5400550 (@lem5400560)). Qed.
Lemma lem5400563 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400564 : term233 = term234.
Proof. exact (@lem5400563 (NUMERAL 0) term18). Qed.
Lemma lem5400565 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400566 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400567 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400566 h1) (fun h1 : term234 = True => @lem5400565)). Qed.
Lemma lem5400568 : term234 = True.
Proof. exact (EQ_MP (@lem5400567) (@lem5400565)). Qed.
Lemma lem5400569 : term233 = True.
Proof. exact (TRANS (@lem5400564) (@lem5400568)). Qed.
Lemma lem5400570 : True = term233.
Proof. exact (SYM (@lem5400569)). Qed.
Lemma lem5400571 : term233.
Proof. exact (EQ_MP (@lem5400570) (@lem0)). Qed.
Lemma lem5400572 : term420.
Proof. exact (@lem5400561 (@lem5400571)). Qed.
Lemma lem5400574 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400575 : term233 = term234.
Proof. exact (@lem5400574 (NUMERAL 0) term18). Qed.
Lemma lem5400576 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400577 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400578 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400577 h1) (fun h1 : term234 = True => @lem5400576)). Qed.
Lemma lem5400579 : term234 = True.
Proof. exact (EQ_MP (@lem5400578) (@lem5400576)). Qed.
Lemma lem5400580 : term233 = True.
Proof. exact (TRANS (@lem5400575) (@lem5400579)). Qed.
Lemma lem5400581 : True = term233.
Proof. exact (SYM (@lem5400580)). Qed.
Lemma lem5400582 : term233.
Proof. exact (EQ_MP (@lem5400581) (@lem0)). Qed.
Lemma lem5400583 : term421.
Proof. exact (@lem5400572 (@lem5400582)). Qed.
Lemma lem5400585 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5400586 : term195 = term196.
Proof. exact (@lem5400585 term18 term18). Qed.
Lemma lem5400587 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400588 : term198 = term18.
Proof. exact (EQ_MP (@lem5400587) (@lem940073)). Qed.
Lemma lem5400589 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400590 : term196 = term142.
Proof. exact (MK_COMB (@lem5400589) (@lem5400588)). Qed.
Lemma lem5400591 : term195 = term142.
Proof. exact (TRANS (@lem5400586) (@lem5400590)). Qed.
Lemma lem5400593 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5400594 : term212 = term217.
Proof. exact (@lem5400593 term18 term18). Qed.
Lemma lem5400595 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400596 : term198 = term18.
Proof. exact (EQ_MP (@lem5400595) (@lem940073)). Qed.
Lemma lem5400597 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400598 : term196 = term142.
Proof. exact (MK_COMB (@lem5400597) (@lem5400596)). Qed.
Lemma lem5400599 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5400600 : term217 = term186.
Proof. exact (MK_COMB (@lem5400599) (@lem5400598)). Qed.
Lemma lem5400601 : term212 = term186.
Proof. exact (TRANS (@lem5400594) (@lem5400600)). Qed.
Lemma lem5400602 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5400603 : term422 = term414.
Proof. exact (MK_COMB (@lem5400602) (@lem5400601)). Qed.
Lemma lem5400604 : term423 = term416.
Proof. exact (MK_COMB (@lem5400603) (@lem5400591)). Qed.
Lemma lem5400606 (m : nat) : (term424 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5400607 : term416 = term133.
Proof. exact (@lem5400606 term18). Qed.
Lemma lem5400608 : term423 = term133.
Proof. exact (TRANS (@lem5400604) (@lem5400607)). Qed.
Lemma lem5400609 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5400610 : term425 = term243.
Proof. exact (MK_COMB (@lem5400609) (@lem5400608)). Qed.
Lemma lem5400611 : term142 = term142.
Proof. exact (eq_refl term142). Qed.
Lemma lem5400612 : term426 = term245.
Proof. exact (MK_COMB (@lem5400610) (@lem5400611)). Qed.
Lemma lem5400614 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5400615 : term245 = term133.
Proof. exact (@lem5400614 term18). Qed.
Lemma lem5400616 : term426 = term133.
Proof. exact (TRANS (@lem5400612) (@lem5400615)). Qed.
Lemma lem5400618 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5400619 : term195 = term196.
Proof. exact (@lem5400618 term18 term18). Qed.
Lemma lem5400620 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400621 : term198 = term18.
Proof. exact (EQ_MP (@lem5400620) (@lem940073)). Qed.
Lemma lem5400622 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400623 : term196 = term142.
Proof. exact (MK_COMB (@lem5400622) (@lem5400621)). Qed.
Lemma lem5400624 : term195 = term142.
Proof. exact (TRANS (@lem5400619) (@lem5400623)). Qed.
Lemma lem5400625 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem5400626 : term247 = term245.
Proof. exact (MK_COMB (@lem5400625) (@lem5400624)). Qed.
Lemma lem5400628 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5400629 : term245 = term133.
Proof. exact (@lem5400628 term18). Qed.
Lemma lem5400630 : term247 = term133.
Proof. exact (TRANS (@lem5400626) (@lem5400629)). Qed.
Lemma lem5400631 : term133 = term247.
Proof. exact (SYM (@lem5400630)). Qed.
Lemma lem5400632 : term426 = term247.
Proof. exact (TRANS (@lem5400616) (@lem5400631)). Qed.
Lemma lem5400633 : term417 = term183.
Proof. exact (@lem5400583 (@lem5400632)). Qed.
Lemma lem5400634 : term416 = term183.
Proof. exact (TRANS (@lem5400549) (@lem5400633)). Qed.
Lemma lem5400636 (x : real) : (term202 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5400637 : term183 = term133.
Proof. exact (@lem5400636 term133). Qed.
Lemma lem5400638 : term416 = term133.
Proof. exact (TRANS (@lem5400634) (@lem5400637)). Qed.
Lemma lem5400639 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5400640 : term427 = term243.
Proof. exact (MK_COMB (@lem5400639) (@lem5400638)). Qed.
Lemma lem5400641 (_69880 : int) : (real_of_int _69880) = (real_of_int _69880).
Proof. exact (eq_refl (real_of_int _69880)). Qed.
Lemma lem5400642 (_69880 : int) : (term413 _69880) = (term428 _69880).
Proof. exact (MK_COMB (@lem5400640) (@lem5400641 _69880)). Qed.
Lemma lem5400643 (_69880 : int) : (term433 _69880) = (term428 _69880).
Proof. exact (TRANS (@lem5400540 _69880) (@lem5400642 _69880)). Qed.
Lemma lem5400644 (_69880 : int) : (term428 _69880) = term133.
Proof. exact (@lem1982719 (real_of_int _69880)). Qed.
Lemma lem5400645 (_69880 : int) : (term433 _69880) = term133.
Proof. exact (TRANS (@lem5400643 _69880) (@lem5400644 _69880)). Qed.
Lemma lem5400646 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5400647 (_69880 : int) : (term434 _69880) = term430.
Proof. exact (MK_COMB (@lem5400646) (@lem5400645 _69880)). Qed.
Lemma lem5400648 : term186 = term186.
Proof. exact (eq_refl term186). Qed.
Lemma lem5400649 (_69880 : int) : (term432 _69880) = term435.
Proof. exact (MK_COMB (@lem5400647 _69880) (@lem5400648)). Qed.
Lemma lem5400650 (_69880 : int) : (term534 _69880) = term435.
Proof. exact (TRANS (@lem5400539 _69880) (@lem5400649 _69880)). Qed.
Lemma lem5400651 : term435 = term186.
Proof. exact (@lem1982721 term186). Qed.
Lemma lem5400652 (_69880 : int) : (term534 _69880) = term186.
Proof. exact (TRANS (@lem5400650 _69880) (@lem5400651)). Qed.
Lemma lem5400653 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5400654 (_69880 : int) : (term535 _69880) = term437.
Proof. exact (MK_COMB (@lem5400653) (@lem5400652 _69880)). Qed.
Lemma lem5400655 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem5400656 (_69880 : int) : (term533 _69880) = term438.
Proof. exact (MK_COMB (@lem5400654 _69880) (@lem5400655)). Qed.
Lemma lem5400657 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : term438.
Proof. exact (EQ_MP (@lem5400656 _69880) (@lem5400538 _69879 _69880 h1)). Qed.
Lemma lem5400659 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5400660 : term438 = term439.
Proof. exact (@lem5400659 term133 term186). Qed.
Lemma lem5400662 (x : nat) : (term184 x) = (term185 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5400663 : term186 = term187.
Proof. exact (@lem5400662 term18). Qed.
Lemma lem5400665 (x : nat) : (real_of_num x) = (term182 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5400666 : term133 = term183.
Proof. exact (@lem5400665 (NUMERAL 0)). Qed.
Lemma lem5400667 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5400668 : term135 = term440.
Proof. exact (MK_COMB (@lem5400667) (@lem5400666)). Qed.
Lemma lem5400669 : term439 = term441.
Proof. exact (MK_COMB (@lem5400668) (@lem5400663)). Qed.
Lemma lem5400670 : term442.
Proof. exact (@lem1980026 term133 term142 term186 term142). Qed.
Lemma lem5400672 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400673 : term233 = term234.
Proof. exact (@lem5400672 (NUMERAL 0) term18). Qed.
Lemma lem5400674 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400675 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400676 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400675 h1) (fun h1 : term234 = True => @lem5400674)). Qed.
Lemma lem5400677 : term234 = True.
Proof. exact (EQ_MP (@lem5400676) (@lem5400674)). Qed.
Lemma lem5400678 : term233 = True.
Proof. exact (TRANS (@lem5400673) (@lem5400677)). Qed.
Lemma lem5400679 : True = term233.
Proof. exact (SYM (@lem5400678)). Qed.
Lemma lem5400680 : term233.
Proof. exact (EQ_MP (@lem5400679) (@lem0)). Qed.
Lemma lem5400681 : term443.
Proof. exact (@lem5400670 (@lem5400680)). Qed.
Lemma lem5400683 (m : nat) (n : nat) : (term232 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5400684 : term233 = term234.
Proof. exact (@lem5400683 (NUMERAL 0) term18). Qed.
Lemma lem5400685 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400686 (h1 : term235 = (BIT1 0)) : term234 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5400687 : (term235 = (BIT1 0)) = (term234 = True).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400686 h1) (fun h1 : term234 = True => @lem5400685)). Qed.
Lemma lem5400688 : term234 = True.
Proof. exact (EQ_MP (@lem5400687) (@lem5400685)). Qed.
Lemma lem5400689 : term233 = True.
Proof. exact (TRANS (@lem5400684) (@lem5400688)). Qed.
Lemma lem5400690 : True = term233.
Proof. exact (SYM (@lem5400689)). Qed.
Lemma lem5400691 : term233.
Proof. exact (EQ_MP (@lem5400690) (@lem0)). Qed.
Lemma lem5400692 : term441 = term444.
Proof. exact (@lem5400681 (@lem5400691)). Qed.
Lemma lem5400694 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5400695 : term212 = term217.
Proof. exact (@lem5400694 term18 term18). Qed.
Lemma lem5400696 : (term197 = (BIT1 0)) = (term198 = term18).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5400697 : term198 = term18.
Proof. exact (EQ_MP (@lem5400696) (@lem940073)). Qed.
Lemma lem5400698 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5400699 : term196 = term142.
Proof. exact (MK_COMB (@lem5400698) (@lem5400697)). Qed.
Lemma lem5400700 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5400701 : term217 = term186.
Proof. exact (MK_COMB (@lem5400700) (@lem5400699)). Qed.
Lemma lem5400702 : term212 = term186.
Proof. exact (TRANS (@lem5400695) (@lem5400701)). Qed.
Lemma lem5400704 (x : nat) : (term246 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5400705 : term245 = term133.
Proof. exact (@lem5400704 term18). Qed.
Lemma lem5400706 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5400707 : term445 = term135.
Proof. exact (MK_COMB (@lem5400706) (@lem5400705)). Qed.
Lemma lem5400708 : term444 = term439.
Proof. exact (MK_COMB (@lem5400707) (@lem5400702)). Qed.
Lemma lem5400710 (m : nat) (n : nat) : (term446 m n) = (term447 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5400711 : term439 = term448.
Proof. exact (@lem5400710 (NUMERAL 0) term18). Qed.
Lemma lem5400712 : term235 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5400713 (h1 : term235 = (BIT1 0)) : (term18 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5400714 : (term235 = (BIT1 0)) = ((term18 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term235 = (BIT1 0) => @lem5400713 h1) (fun h1 : (term18 = (NUMERAL 0)) = False => @lem5400712)). Qed.
Lemma lem5400715 : (term18 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5400714) (@lem5400712)). Qed.
Lemma lem5400716 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5400717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5400718 : term449 = (and True).
Proof. exact (MK_COMB (@lem5400717) (@lem5400716)). Qed.
Lemma lem5400719 : term448 = (True /\ False).
Proof. exact (MK_COMB (@lem5400718) (@lem5400715)). Qed.
Lemma lem5400721 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5400722 : term448 = False.
Proof. exact (TRANS (@lem5400719) (@lem5400721)). Qed.
Lemma lem5400723 : term439 = False.
Proof. exact (TRANS (@lem5400711) (@lem5400722)). Qed.
Lemma lem5400724 : term444 = False.
Proof. exact (TRANS (@lem5400708) (@lem5400723)). Qed.
Lemma lem5400725 : term441 = False.
Proof. exact (TRANS (@lem5400692) (@lem5400724)). Qed.
Lemma lem5400726 : term439 = False.
Proof. exact (TRANS (@lem5400669) (@lem5400725)). Qed.
Lemma lem5400727 : term438 = False.
Proof. exact (TRANS (@lem5400660) (@lem5400726)). Qed.
Lemma lem5400728 (_69879 : int) (_69880 : int) (h1 : term518 _69879 _69880) : False.
Proof. exact (EQ_MP (@lem5400727) (@lem5400657 _69879 _69880 h1)). Qed.
Lemma lem5400729 (_69879 : int) (_69880 : int) (h1 : term359 _69879 _69880) : False.
Proof. exact (or_elim (@lem5399763 _69879 _69880 h1) (fun h0 : term502 _69879 _69880 => @lem5400165 _69879 _69880 h0) (fun h0 : term518 _69879 _69880 => @lem5400728 _69879 _69880 h0)). Qed.
Lemma lem5400730 (_69879 : int) (_69880 : int) (h1 : term368 _69879 _69880) : False.
Proof. exact (or_elim (@lem5398625 _69879 _69880 h1) (fun h0 : term363 _69879 _69880 => @lem5399762 _69879 _69880 h0) (fun h0 : term359 _69879 _69880 => @lem5400729 _69879 _69880 h0)). Qed.
Lemma lem5400732 (_69879 : int) (_69880 : int) (h1 : term368 _69879 _69880) : term368 _69879 _69880.
Proof. exact (h1). Qed.
Lemma lem5400733 (_69879 : int) (_69880 : int) (h1 : term368 _69879 _69880) : (term368 _69879 _69880) = False.
Proof. exact (prop_ext (fun h2 : term368 _69879 _69880 => @lem5400730 _69879 _69880 h1) (fun h2 : False => @lem5400732 _69879 _69880 h1)). Qed.
Lemma lem5400734 (_69879 : int) (_69880 : int) (h1 : term368 _69879 _69880) : False.
Proof. exact (EQ_MP (@lem5400733 _69879 _69880 h1) (@lem5400732 _69879 _69880 h1)). Qed.
Lemma lem5400735 (_69880 : int) (_69879 : int) (h1 : term178 _69880 _69879) : term178 _69880 _69879.
Proof. exact (h1). Qed.
Lemma lem5400736 (_69880 : int) (_69879 : int) (h1 : term178 _69880 _69879) : term368 _69879 _69880.
Proof. exact (EQ_MP (@lem5398603 _69879 _69880) (@lem5400735 _69880 _69879 h1)). Qed.
Lemma lem5400737 (_69880 : int) (_69879 : int) (h1 : term178 _69880 _69879) : (term368 _69879 _69880) = False.
Proof. exact (prop_ext (fun h2 : term368 _69879 _69880 => @lem5400734 _69879 _69880 h2) (fun h2 : False => @lem5400736 _69880 _69879 h1)). Qed.
Lemma lem5400738 (_69880 : int) (_69879 : int) (h1 : term178 _69880 _69879) : False.
Proof. exact (EQ_MP (@lem5400737 _69880 _69879 h1) (@lem5400736 _69880 _69879 h1)). Qed.
Lemma lem5400739 (_69880 : int) (_69879 : int) : term536 _69880 _69879.
Proof. exact (fun h0 : term178 _69880 _69879 => @lem5400738 _69880 _69879 h0). Qed.
Lemma lem5400740 (_69880 : int) (_69879 : int) : term537 _69880 _69879.
Proof. exact (@lem1386578 (term538 _69880 _69879)). Qed.
Lemma lem5400743 (_69880 : int) (_69879 : int) : term538 _69880 _69879.
Proof. exact (@lem5400740 _69880 _69879 (@lem5400739 _69880 _69879)). Qed.
Lemma lem5400744 (_69879 : int) (_69880 : int) : (term176 _69880 _69879) = (term127 _69879 _69880).
Proof. exact (SYM (@lem5397642 _69880 _69879)). Qed.
Lemma lem5400745 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5400746 (_69879 : int) (_69880 : int) : (term538 _69880 _69879) = (term91 _69879 _69880).
Proof. exact (MK_COMB (@lem5400745) (@lem5400744 _69879 _69880)). Qed.
Lemma lem5400747 (_69879 : int) (_69880 : int) : term91 _69879 _69880.
Proof. exact (EQ_MP (@lem5400746 _69879 _69880) (@lem5400743 _69880 _69879)). Qed.
Lemma lem5400748 (_69879 : int) (_69880 : int) : term92 _69879 _69880.
Proof. exact (EQ_MP (@lem5397407 _69879 _69880) (@lem5400747 _69879 _69880)). Qed.
Lemma lem5400749 (d : nat) (n : nat) : term539 d n.
Proof. exact (@lem5400748 (int_of_num d) (int_of_num n)). Qed.
Lemma lem5400750 (d : nat) (n : nat) : term540 d n.
Proof. exact (@lem5400749 d n (@lem5397403 d)). Qed.
Lemma lem5400751 (d : nat) (n : nat) : term84 d n.
Proof. exact (@lem5400750 d n (@lem5397406 n)). Qed.
Lemma lem5400752 (n : nat) : term86 n.
Proof. exact (fun d : nat => @lem5400751 d n). Qed.
Lemma lem5400753 : term88.
Proof. exact (fun n : nat => @lem5400752 n). Qed.
Lemma lem5400754 : term88 = term28.
Proof. exact (SYM (@lem5397400)). Qed.
Lemma lem5400755 : term28.
Proof. exact (EQ_MP (@lem5400754) (@lem5400753)). Qed.
Lemma lem5400756 : term28 = (term28 = True).
Proof. exact (@lem7 term28). Qed.
Lemma lem5400757 : term28 = True.
Proof. exact (EQ_MP (@lem5400756) (@lem5400755)). Qed.
Lemma lem5400758 : True = term28.
Proof. exact (SYM (@lem5400757)). Qed.
Lemma lem5400759 : term28.
Proof. exact (EQ_MP (@lem5400758) (@lem0)). Qed.
Lemma lem5400760 : term27.
Proof. exact (EQ_MP (@lem5397214) (@lem5400759)). Qed.
