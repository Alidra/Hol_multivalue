Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PASTECART_FST_SND_term_abbrevs.
Require Import CART_EQ_spec.
Require Import INT_POS_spec.
Require Import LAMBDA_BETA_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import fstcart_spec.
Require Import pastecart_spec.
Require Import sndcart_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032098_spec.
Require Import thm1032781_spec.
Require Import thm13473_spec.
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
Require Import thm1396750_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm7640410_spec.
Require Import thm7640437_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem7648213 (i : nat) (a : nat) : (term0 i a) = (Peano.le i a).
Proof. exact (@lem16933 (Peano.le i a)). Qed.
Lemma lem7648214 (a : nat) (i : nat) : ((term1 i a) = i) = ((term1 i a) = i).
Proof. exact (eq_refl ((term1 i a) = i)). Qed.
Lemma lem7648215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7648216 (i : nat) (a : nat) : (term2 i a) = (term3 i a).
Proof. exact (MK_COMB (@lem7648215) (@lem7648213 i a)). Qed.
Lemma lem7648217 (a : nat) (i : nat) : (term4 a i) = (term5 a i).
Proof. exact (MK_COMB (@lem7648216 i a) (@lem7648214 a i)). Qed.
Lemma lem7648218 (a : nat) (i : nat) : (term6 a i) = (term4 a i).
Proof. exact (@lem17265 (term7 i a) ((term1 i a) = i)). Qed.
Lemma lem7648220 (a : nat) (i : nat) : (term6 a i) = (term5 a i).
Proof. exact (TRANS (@lem7648218 a i) (@lem7648217 a i)). Qed.
Lemma lem7648221 (a : nat) (i : nat) : (term8 i a) = (term9 a i).
Proof. exact (@lem1032781 i a (term10 a i)). Qed.
Lemma lem7648222 (d : nat) (a : nat) (i : nat) : (term11 a i d) = (term12 d a i).
Proof. exact (eq_refl (term11 a i d)). Qed.
Lemma lem7648223 (i : nat) (a : nat) (d : nat) : (term13 i a d) = (term13 i a d).
Proof. exact (eq_refl (term13 i a d)). Qed.
Lemma lem7648224 (d : nat) (a : nat) (i : nat) : (term14 a i d) = (term15 d a i).
Proof. exact (MK_COMB (@lem7648223 i a d) (@lem7648222 d a i)). Qed.
Lemma lem7648225 (a : nat) (i : nat) : (term16 a i) = (term17 a i).
Proof. exact (fun_ext (fun d : nat => @lem7648224 d a i)). Qed.
Lemma lem7648226 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7648227 (a : nat) (i : nat) : (term9 a i) = (term18 a i).
Proof. exact (MK_COMB (@lem7648226) (@lem7648225 a i)). Qed.
Lemma lem7648228 (a : nat) (i : nat) : (term8 i a) = (term5 a i).
Proof. exact (eq_refl (term8 i a)). Qed.
Lemma lem7648229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7648230 (a : nat) (i : nat) : (term19 i a) = (term20 a i).
Proof. exact (MK_COMB (@lem7648229) (@lem7648228 a i)). Qed.
Lemma lem7648231 (a : nat) (i : nat) : ((term8 i a) = (term9 a i)) = ((term5 a i) = (term18 a i)).
Proof. exact (MK_COMB (@lem7648230 a i) (@lem7648227 a i)). Qed.
Lemma lem7648232 (a : nat) (i : nat) : (term5 a i) = (term18 a i).
Proof. exact (EQ_MP (@lem7648231 a i) (@lem7648221 a i)). Qed.
Lemma lem7648233 (d : nat) (a : nat) (i : nat) : (term15 d a i) = (term15 d a i).
Proof. exact (eq_refl (term15 d a i)). Qed.
Lemma lem7648234 (a : nat) (i : nat) : (term17 a i) = (term17 a i).
Proof. exact (fun_ext (fun d : nat => @lem7648233 d a i)). Qed.
Lemma lem7648235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7648236 (a : nat) (i : nat) : (term18 a i) = (term18 a i).
Proof. exact (MK_COMB (@lem7648235) (@lem7648234 a i)). Qed.
Lemma lem7648237 (a : nat) (i : nat) : (term20 a i) = (term20 a i).
Proof. exact (eq_refl (term20 a i)). Qed.
Lemma lem7648238 (a : nat) (i : nat) : ((term5 a i) = (term18 a i)) = ((term5 a i) = (term18 a i)).
Proof. exact (MK_COMB (@lem7648237 a i) (@lem7648236 a i)). Qed.
Lemma lem7648239 (a : nat) (i : nat) : (term5 a i) = (term18 a i).
Proof. exact (EQ_MP (@lem7648238 a i) (@lem7648232 a i)). Qed.
Lemma lem7648264 (a : nat) (i : nat) : (term6 a i) = (term18 a i).
Proof. exact (TRANS (@lem7648220 a i) (@lem7648239 a i)). Qed.
Lemma lem7648265 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7648272 (a : nat) (d : nat) : (Nat.add d a) = (Nat.add a d).
Proof. exact (@lem1032098 a d). Qed.
Lemma lem7648273 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7648274 (a : nat) (d : nat) : (term21 d a) = (term21 a d).
Proof. exact (MK_COMB (@lem7648273) (@lem7648272 a d)). Qed.
Lemma lem7648275 (a : nat) (d : nat) (i : nat) : ((Nat.add d a) = i) = ((Nat.add a d) = i).
Proof. exact (MK_COMB (@lem7648274 a d) (@lem7648265 i)). Qed.
Lemma lem7648282 (i : nat) (a : nat) : (term3 i a) = (term3 i a).
Proof. exact (eq_refl (term3 i a)). Qed.
Lemma lem7648283 (a : nat) (d : nat) (i : nat) : (term12 d a i) = (term22 a d i).
Proof. exact (MK_COMB (@lem7648282 i a) (@lem7648275 a d i)). Qed.
Lemma lem7648318 (i : nat) (a : nat) (d : nat) : (term13 i a d) = (term13 i a d).
Proof. exact (eq_refl (term13 i a d)). Qed.
Lemma lem7648319 (a : nat) (d : nat) (i : nat) : (term15 d a i) = (term23 a d i).
Proof. exact (MK_COMB (@lem7648318 i a d) (@lem7648283 a d i)). Qed.
Lemma lem7648320 (a : nat) (i : nat) : (term17 a i) = (term24 a i).
Proof. exact (fun_ext (fun d : nat => @lem7648319 a d i)). Qed.
Lemma lem7648321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7648322 (a : nat) (i : nat) : (term18 a i) = (term25 a i).
Proof. exact (MK_COMB (@lem7648321) (@lem7648320 a i)). Qed.
Lemma lem7648325 (a : nat) (i : nat) : (term6 a i) = (term25 a i).
Proof. exact (TRANS (@lem7648264 a i) (@lem7648322 a i)). Qed.
Lemma lem7648327 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7648328 (i : nat) (a : nat) (d : nat) : (i = (Nat.add a d)) = ((int_of_num i) = (term26 a d)).
Proof. exact (@lem7648327 i (Nat.add a d)). Qed.
Lemma lem7648332 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7648333 (a : nat) (d : nat) : (term26 a d) = (term27 a d).
Proof. exact (@lem7648332 a d). Qed.
Lemma lem7648334 (i : nat) : (term28 i) = (term28 i).
Proof. exact (eq_refl (term28 i)). Qed.
Lemma lem7648335 (i : nat) (a : nat) (d : nat) : ((int_of_num i) = (term26 a d)) = ((int_of_num i) = (term27 a d)).
Proof. exact (MK_COMB (@lem7648334 i) (@lem7648333 a d)). Qed.
Lemma lem7648336 (i : nat) (a : nat) (d : nat) : (i = (Nat.add a d)) = ((int_of_num i) = (term27 a d)).
Proof. exact (TRANS (@lem7648328 i a d) (@lem7648335 i a d)). Qed.
Lemma lem7648337 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7648338 (i : nat) (a : nat) (d : nat) : (term29 i a d) = (term30 i a d).
Proof. exact (MK_COMB (@lem7648337) (@lem7648336 i a d)). Qed.
Lemma lem7648339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7648340 (i : nat) (a : nat) (d : nat) : (term31 i a d) = (term32 i a d).
Proof. exact (MK_COMB (@lem7648339) (@lem7648338 i a d)). Qed.
Lemma lem7648342 (m : nat) (n : nat) : (Peano.lt m n) = (term33 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem7648343 (i : nat) (a : nat) : (Peano.lt i a) = (term33 i a).
Proof. exact (@lem7648342 i a). Qed.
Lemma lem7648344 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7648345 (i : nat) (a : nat) : (term34 i a) = (term35 i a).
Proof. exact (MK_COMB (@lem7648344) (@lem7648343 i a)). Qed.
Lemma lem7648346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7648347 (i : nat) (a : nat) : (term36 i a) = (term37 i a).
Proof. exact (MK_COMB (@lem7648346) (@lem7648345 i a)). Qed.
Lemma lem7648349 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7648350 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term38).
Proof. exact (@lem7648349 d (NUMERAL 0)). Qed.
Lemma lem7648353 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7648354 (d : nat) : (term39 d) = (term40 d).
Proof. exact (MK_COMB (@lem7648353) (@lem7648350 d)). Qed.
Lemma lem7648355 (i : nat) (a : nat) (d : nat) : (term41 i a d) = (term42 i a d).
Proof. exact (MK_COMB (@lem7648347 i a) (@lem7648354 d)). Qed.
Lemma lem7648356 (i : nat) (a : nat) (d : nat) : (term43 i a d) = (term44 i a d).
Proof. exact (MK_COMB (@lem7648340 i a d) (@lem7648355 i a d)). Qed.
Lemma lem7648357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7648358 (i : nat) (a : nat) (d : nat) : (term13 i a d) = (term45 i a d).
Proof. exact (MK_COMB (@lem7648357) (@lem7648356 i a d)). Qed.
Lemma lem7648360 (m : nat) (n : nat) : (Peano.le m n) = (term46 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7648361 (i : nat) (a : nat) : (Peano.le i a) = (term46 i a).
Proof. exact (@lem7648360 i a). Qed.
Lemma lem7648362 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7648363 (i : nat) (a : nat) : (term3 i a) = (term47 i a).
Proof. exact (MK_COMB (@lem7648362) (@lem7648361 i a)). Qed.
Lemma lem7648365 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7648366 (a : nat) (d : nat) (i : nat) : ((Nat.add a d) = i) = ((term26 a d) = (int_of_num i)).
Proof. exact (@lem7648365 (Nat.add a d) i). Qed.
Lemma lem7648370 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7648371 (a : nat) (d : nat) : (term26 a d) = (term27 a d).
Proof. exact (@lem7648370 a d). Qed.
Lemma lem7648372 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem7648373 (a : nat) (d : nat) : (term48 a d) = (term49 a d).
Proof. exact (MK_COMB (@lem7648372) (@lem7648371 a d)). Qed.
Lemma lem7648374 (i : nat) : (int_of_num i) = (int_of_num i).
Proof. exact (eq_refl (int_of_num i)). Qed.
Lemma lem7648375 (a : nat) (d : nat) (i : nat) : ((term26 a d) = (int_of_num i)) = ((term27 a d) = (int_of_num i)).
Proof. exact (MK_COMB (@lem7648373 a d) (@lem7648374 i)). Qed.
Lemma lem7648376 (a : nat) (d : nat) (i : nat) : ((Nat.add a d) = i) = ((term27 a d) = (int_of_num i)).
Proof. exact (TRANS (@lem7648366 a d i) (@lem7648375 a d i)). Qed.
Lemma lem7648377 (a : nat) (d : nat) (i : nat) : (term22 a d i) = (term50 a d i).
Proof. exact (MK_COMB (@lem7648363 i a) (@lem7648376 a d i)). Qed.
Lemma lem7648378 (a : nat) (d : nat) (i : nat) : (term23 a d i) = (term51 a d i).
Proof. exact (MK_COMB (@lem7648358 i a d) (@lem7648377 a d i)). Qed.
Lemma lem7648379 (a : nat) (i : nat) : (term24 a i) = (term52 a i).
Proof. exact (fun_ext (fun d : nat => @lem7648378 a d i)). Qed.
Lemma lem7648380 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7648381 (a : nat) (i : nat) : (term25 a i) = (term53 a i).
Proof. exact (MK_COMB (@lem7648380) (@lem7648379 a i)). Qed.
Lemma lem7648382 (a : nat) (i : nat) : (term6 a i) = (term53 a i).
Proof. exact (TRANS (@lem7648325 a i) (@lem7648381 a i)). Qed.
Lemma lem7648383 (a : nat) : term54 a.
Proof. exact (@lem2307535 a). Qed.
Lemma lem7648384 (a : nat) : (term54 a) = (term55 a).
Proof. exact (eq_refl (term54 a)). Qed.
Lemma lem7648385 (a : nat) : term55 a.
Proof. exact (EQ_MP (@lem7648384 a) (@lem7648383 a)). Qed.
Lemma lem7648386 (d : nat) : term54 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem7648387 (d : nat) : (term54 d) = (term55 d).
Proof. exact (eq_refl (term54 d)). Qed.
Lemma lem7648388 (d : nat) : term55 d.
Proof. exact (EQ_MP (@lem7648387 d) (@lem7648386 d)). Qed.
Lemma lem7648389 (i : nat) : term54 i.
Proof. exact (@lem2307535 i). Qed.
Lemma lem7648390 (i : nat) : (term54 i) = (term55 i).
Proof. exact (eq_refl (term54 i)). Qed.
Lemma lem7648391 (i : nat) : term55 i.
Proof. exact (EQ_MP (@lem7648390 i) (@lem7648389 i)). Qed.
Lemma lem7648392 (_98518 : int) (_98519 : int) (_98520 : int) : (term56 _98518 _98519 _98520) = (term57 _98518 _98519 _98520).
Proof. exact (@lem2318604 (term57 _98518 _98519 _98520)). Qed.
Lemma lem7648417 (_98520 : int) (_98518 : int) (_98519 : int) : (term58 _98520 _98518 _98519) = (_98520 = (int_add _98518 _98519)).
Proof. exact (@lem16933 (_98520 = (int_add _98518 _98519))). Qed.
Lemma lem7648420 (_98520 : int) (_98518 : int) : (term59 _98520 _98518) = (int_lt _98520 _98518).
Proof. exact (@lem16933 (int_lt _98520 _98518)). Qed.
Lemma lem7648423 (_98519 : int) : (term60 _98519) = (_98519 = term38).
Proof. exact (@lem16933 (_98519 = term38)). Qed.
Lemma lem7648424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7648425 (_98520 : int) (_98518 : int) : (term61 _98520 _98518) = (term62 _98520 _98518).
Proof. exact (MK_COMB (@lem7648424) (@lem7648420 _98520 _98518)). Qed.
Lemma lem7648426 (_98520 : int) (_98518 : int) (_98519 : int) : (term63 _98520 _98518 _98519) = (term64 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648425 _98520 _98518) (@lem7648423 _98519)). Qed.
Lemma lem7648427 (_98520 : int) (_98518 : int) (_98519 : int) : (term65 _98520 _98518 _98519) = (term63 _98520 _98518 _98519).
Proof. exact (@lem17160 (term66 _98520 _98518) (term67 _98519)). Qed.
Lemma lem7648428 (_98520 : int) (_98518 : int) (_98519 : int) : (term65 _98520 _98518 _98519) = (term64 _98520 _98518 _98519).
Proof. exact (TRANS (@lem7648427 _98520 _98518 _98519) (@lem7648426 _98520 _98518 _98519)). Qed.
Lemma lem7648429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7648430 (_98520 : int) (_98518 : int) (_98519 : int) : (term68 _98520 _98518 _98519) = (term69 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648429) (@lem7648417 _98520 _98518 _98519)). Qed.
Lemma lem7648431 (_98520 : int) (_98518 : int) (_98519 : int) : (term70 _98520 _98518 _98519) = (term71 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648430 _98520 _98518 _98519) (@lem7648428 _98520 _98518 _98519)). Qed.
Lemma lem7648432 (_98520 : int) (_98518 : int) (_98519 : int) : (term72 _98520 _98518 _98519) = (term70 _98520 _98518 _98519).
Proof. exact (@lem17045 (term73 _98520 _98518 _98519) (term74 _98520 _98518 _98519)). Qed.
Lemma lem7648433 (_98520 : int) (_98518 : int) (_98519 : int) : (term72 _98520 _98518 _98519) = (term71 _98520 _98518 _98519).
Proof. exact (TRANS (@lem7648432 _98520 _98518 _98519) (@lem7648431 _98520 _98518 _98519)). Qed.
Lemma lem7648440 (_98518 : int) (_98519 : int) (_98520 : int) : (term75 _98518 _98519 _98520) = (term76 _98518 _98519 _98520).
Proof. exact (@lem17160 (int_le _98520 _98518) ((int_add _98518 _98519) = _98520)). Qed.
Lemma lem7648441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7648442 (_98520 : int) (_98518 : int) (_98519 : int) : (term77 _98520 _98518 _98519) = (term78 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648441) (@lem7648433 _98520 _98518 _98519)). Qed.
Lemma lem7648443 (_98518 : int) (_98519 : int) (_98520 : int) : (term79 _98518 _98519 _98520) = (term80 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7648442 _98520 _98518 _98519) (@lem7648440 _98518 _98519 _98520)). Qed.
Lemma lem7648444 (_98518 : int) (_98519 : int) (_98520 : int) : (term81 _98518 _98519 _98520) = (term79 _98518 _98519 _98520).
Proof. exact (@lem17160 (term82 _98520 _98518 _98519) (term83 _98518 _98519 _98520)). Qed.
Lemma lem7648445 (_98518 : int) (_98519 : int) (_98520 : int) : (term81 _98518 _98519 _98520) = (term80 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7648444 _98518 _98519 _98520) (@lem7648443 _98518 _98519 _98520)). Qed.
Lemma lem7648447 (_98520 : int) : (term84 _98520) = (term84 _98520).
Proof. exact (eq_refl (term84 _98520)). Qed.
Lemma lem7648448 (_98518 : int) (_98519 : int) (_98520 : int) : (term85 _98518 _98519 _98520) = (term86 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7648447 _98520) (@lem7648445 _98518 _98519 _98520)). Qed.
Lemma lem7648449 (_98518 : int) (_98519 : int) (_98520 : int) : (term87 _98518 _98519 _98520) = (term85 _98518 _98519 _98520).
Proof. exact (@lem17362 (term88 _98520) (term89 _98518 _98519 _98520)). Qed.
Lemma lem7648450 (_98518 : int) (_98519 : int) (_98520 : int) : (term87 _98518 _98519 _98520) = (term86 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7648449 _98518 _98519 _98520) (@lem7648448 _98518 _98519 _98520)). Qed.
Lemma lem7648452 (_98519 : int) : (term84 _98519) = (term84 _98519).
Proof. exact (eq_refl (term84 _98519)). Qed.
Lemma lem7648453 (_98518 : int) (_98519 : int) (_98520 : int) : (term90 _98518 _98519 _98520) = (term91 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7648452 _98519) (@lem7648450 _98518 _98519 _98520)). Qed.
Lemma lem7648454 (_98518 : int) (_98519 : int) (_98520 : int) : (term92 _98518 _98519 _98520) = (term90 _98518 _98519 _98520).
Proof. exact (@lem17362 (term88 _98519) (term93 _98518 _98519 _98520)). Qed.
Lemma lem7648455 (_98518 : int) (_98519 : int) (_98520 : int) : (term92 _98518 _98519 _98520) = (term91 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7648454 _98518 _98519 _98520) (@lem7648453 _98518 _98519 _98520)). Qed.
Lemma lem7648457 (_98518 : int) : (term84 _98518) = (term84 _98518).
Proof. exact (eq_refl (term84 _98518)). Qed.
Lemma lem7648458 (_98518 : int) (_98519 : int) (_98520 : int) : (term94 _98518 _98519 _98520) = (term95 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7648457 _98518) (@lem7648455 _98518 _98519 _98520)). Qed.
Lemma lem7648459 (_98518 : int) (_98519 : int) (_98520 : int) : (term96 _98518 _98519 _98520) = (term94 _98518 _98519 _98520).
Proof. exact (@lem17362 (term88 _98518) (term97 _98518 _98519 _98520)). Qed.
Lemma lem7648495 (_98518 : int) (_98519 : int) (_98520 : int) : (term96 _98518 _98519 _98520) = (term95 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7648459 _98518 _98519 _98520) (@lem7648458 _98518 _98519 _98520)). Qed.
Lemma lem7648498 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7648499 (_98518 : int) : (term88 _98518) = (term99 _98518).
Proof. exact (@lem7648498 term38 _98518). Qed.
Lemma lem7648501 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7648502 : term101 = term102.
Proof. exact (@lem7648501 (NUMERAL 0)). Qed.
Lemma lem7648503 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7648504 : term103 = term104.
Proof. exact (MK_COMB (@lem7648503) (@lem7648502)). Qed.
Lemma lem7648505 (_98518 : int) : (real_of_int _98518) = (real_of_int _98518).
Proof. exact (eq_refl (real_of_int _98518)). Qed.
Lemma lem7648506 (_98518 : int) : (term99 _98518) = (term105 _98518).
Proof. exact (MK_COMB (@lem7648504) (@lem7648505 _98518)). Qed.
Lemma lem7648508 (_98518 : int) : (term88 _98518) = (term105 _98518).
Proof. exact (TRANS (@lem7648499 _98518) (@lem7648506 _98518)). Qed.
Lemma lem7648511 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7648512 (_98519 : int) : (term88 _98519) = (term99 _98519).
Proof. exact (@lem7648511 term38 _98519). Qed.
Lemma lem7648514 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7648515 : term101 = term102.
Proof. exact (@lem7648514 (NUMERAL 0)). Qed.
Lemma lem7648516 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7648517 : term103 = term104.
Proof. exact (MK_COMB (@lem7648516) (@lem7648515)). Qed.
Lemma lem7648518 (_98519 : int) : (real_of_int _98519) = (real_of_int _98519).
Proof. exact (eq_refl (real_of_int _98519)). Qed.
Lemma lem7648519 (_98519 : int) : (term99 _98519) = (term105 _98519).
Proof. exact (MK_COMB (@lem7648517) (@lem7648518 _98519)). Qed.
Lemma lem7648521 (_98519 : int) : (term88 _98519) = (term105 _98519).
Proof. exact (TRANS (@lem7648512 _98519) (@lem7648519 _98519)). Qed.
Lemma lem7648524 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7648525 (_98520 : int) : (term88 _98520) = (term99 _98520).
Proof. exact (@lem7648524 term38 _98520). Qed.
Lemma lem7648527 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7648528 : term101 = term102.
Proof. exact (@lem7648527 (NUMERAL 0)). Qed.
Lemma lem7648529 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7648530 : term103 = term104.
Proof. exact (MK_COMB (@lem7648529) (@lem7648528)). Qed.
Lemma lem7648531 (_98520 : int) : (real_of_int _98520) = (real_of_int _98520).
Proof. exact (eq_refl (real_of_int _98520)). Qed.
Lemma lem7648532 (_98520 : int) : (term99 _98520) = (term105 _98520).
Proof. exact (MK_COMB (@lem7648530) (@lem7648531 _98520)). Qed.
Lemma lem7648534 (_98520 : int) : (term88 _98520) = (term105 _98520).
Proof. exact (TRANS (@lem7648525 _98520) (@lem7648532 _98520)). Qed.
Lemma lem7648537 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem7648538 (_98520 : int) (_98518 : int) (_98519 : int) : (_98520 = (int_add _98518 _98519)) = ((real_of_int _98520) = (term106 _98518 _98519)).
Proof. exact (@lem7648537 _98520 (int_add _98518 _98519)). Qed.
Lemma lem7648542 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7648543 (_98518 : int) (_98519 : int) : (term106 _98518 _98519) = (term107 _98518 _98519).
Proof. exact (@lem7648542 _98518 _98519). Qed.
Lemma lem7648544 (_98520 : int) : (term108 _98520) = (term108 _98520).
Proof. exact (eq_refl (term108 _98520)). Qed.
Lemma lem7648545 (_98520 : int) (_98518 : int) (_98519 : int) : ((real_of_int _98520) = (term106 _98518 _98519)) = ((real_of_int _98520) = (term107 _98518 _98519)).
Proof. exact (MK_COMB (@lem7648544 _98520) (@lem7648543 _98518 _98519)). Qed.
Lemma lem7648547 (_98520 : int) (_98518 : int) (_98519 : int) : (_98520 = (int_add _98518 _98519)) = ((real_of_int _98520) = (term107 _98518 _98519)).
Proof. exact (TRANS (@lem7648538 _98520 _98518 _98519) (@lem7648545 _98520 _98518 _98519)). Qed.
Lemma lem7648549 (x : int) (y : int) : (int_lt x y) = (term109 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem7648550 (_98520 : int) (_98518 : int) : (int_lt _98520 _98518) = (term109 _98520 _98518).
Proof. exact (@lem7648549 _98520 _98518). Qed.
Lemma lem7648552 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7648553 (_98520 : int) (_98518 : int) : (term109 _98520 _98518) = (term110 _98520 _98518).
Proof. exact (@lem7648552 (term111 _98520) _98518). Qed.
Lemma lem7648555 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7648556 (_98520 : int) : (term112 _98520) = (term113 _98520).
Proof. exact (@lem7648555 _98520 term114). Qed.
Lemma lem7648558 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7648559 : term115 = term116.
Proof. exact (@lem7648558 term117). Qed.
Lemma lem7648560 (_98520 : int) : (term118 _98520) = (term118 _98520).
Proof. exact (eq_refl (term118 _98520)). Qed.
Lemma lem7648561 (_98520 : int) : (term113 _98520) = (term119 _98520).
Proof. exact (MK_COMB (@lem7648560 _98520) (@lem7648559)). Qed.
Lemma lem7648562 (_98520 : int) : (term112 _98520) = (term119 _98520).
Proof. exact (TRANS (@lem7648556 _98520) (@lem7648561 _98520)). Qed.
Lemma lem7648563 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7648564 (_98520 : int) : (term120 _98520) = (term121 _98520).
Proof. exact (MK_COMB (@lem7648563) (@lem7648562 _98520)). Qed.
Lemma lem7648565 (_98518 : int) : (real_of_int _98518) = (real_of_int _98518).
Proof. exact (eq_refl (real_of_int _98518)). Qed.
Lemma lem7648566 (_98520 : int) (_98518 : int) : (term110 _98520 _98518) = (term122 _98520 _98518).
Proof. exact (MK_COMB (@lem7648564 _98520) (@lem7648565 _98518)). Qed.
Lemma lem7648567 (_98520 : int) (_98518 : int) : (term109 _98520 _98518) = (term122 _98520 _98518).
Proof. exact (TRANS (@lem7648553 _98520 _98518) (@lem7648566 _98520 _98518)). Qed.
Lemma lem7648568 (_98520 : int) (_98518 : int) : (int_lt _98520 _98518) = (term122 _98520 _98518).
Proof. exact (TRANS (@lem7648550 _98520 _98518) (@lem7648567 _98520 _98518)). Qed.
Lemma lem7648571 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem7648572 (_98519 : int) : (_98519 = term38) = ((real_of_int _98519) = term101).
Proof. exact (@lem7648571 _98519 term38). Qed.
Lemma lem7648576 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7648577 : term101 = term102.
Proof. exact (@lem7648576 (NUMERAL 0)). Qed.
Lemma lem7648578 (_98519 : int) : (term108 _98519) = (term108 _98519).
Proof. exact (eq_refl (term108 _98519)). Qed.
Lemma lem7648579 (_98519 : int) : ((real_of_int _98519) = term101) = ((real_of_int _98519) = term102).
Proof. exact (MK_COMB (@lem7648578 _98519) (@lem7648577)). Qed.
Lemma lem7648581 (_98519 : int) : (_98519 = term38) = ((real_of_int _98519) = term102).
Proof. exact (TRANS (@lem7648572 _98519) (@lem7648579 _98519)). Qed.
Lemma lem7648582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7648583 (_98520 : int) (_98518 : int) : (term62 _98520 _98518) = (term123 _98520 _98518).
Proof. exact (MK_COMB (@lem7648582) (@lem7648568 _98520 _98518)). Qed.
Lemma lem7648584 (_98520 : int) (_98518 : int) (_98519 : int) : (term64 _98520 _98518 _98519) = (term124 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648583 _98520 _98518) (@lem7648581 _98519)). Qed.
Lemma lem7648585 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7648586 (_98520 : int) (_98518 : int) (_98519 : int) : (term69 _98520 _98518 _98519) = (term125 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648585) (@lem7648547 _98520 _98518 _98519)). Qed.
Lemma lem7648587 (_98520 : int) (_98518 : int) (_98519 : int) : (term71 _98520 _98518 _98519) = (term126 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648586 _98520 _98518 _98519) (@lem7648584 _98520 _98518 _98519)). Qed.
Lemma lem7648589 (y : int) (x : int) : (term127 x y) = (term109 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7648590 (_98518 : int) (_98520 : int) : (term127 _98520 _98518) = (term109 _98518 _98520).
Proof. exact (@lem7648589 _98518 _98520). Qed.
Lemma lem7648592 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7648593 (_98518 : int) (_98520 : int) : (term109 _98518 _98520) = (term110 _98518 _98520).
Proof. exact (@lem7648592 (term111 _98518) _98520). Qed.
Lemma lem7648595 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7648596 (_98518 : int) : (term112 _98518) = (term113 _98518).
Proof. exact (@lem7648595 _98518 term114). Qed.
Lemma lem7648598 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7648599 : term115 = term116.
Proof. exact (@lem7648598 term117). Qed.
Lemma lem7648600 (_98518 : int) : (term118 _98518) = (term118 _98518).
Proof. exact (eq_refl (term118 _98518)). Qed.
Lemma lem7648601 (_98518 : int) : (term113 _98518) = (term119 _98518).
Proof. exact (MK_COMB (@lem7648600 _98518) (@lem7648599)). Qed.
Lemma lem7648602 (_98518 : int) : (term112 _98518) = (term119 _98518).
Proof. exact (TRANS (@lem7648596 _98518) (@lem7648601 _98518)). Qed.
Lemma lem7648603 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7648604 (_98518 : int) : (term120 _98518) = (term121 _98518).
Proof. exact (MK_COMB (@lem7648603) (@lem7648602 _98518)). Qed.
Lemma lem7648605 (_98520 : int) : (real_of_int _98520) = (real_of_int _98520).
Proof. exact (eq_refl (real_of_int _98520)). Qed.
Lemma lem7648606 (_98518 : int) (_98520 : int) : (term110 _98518 _98520) = (term122 _98518 _98520).
Proof. exact (MK_COMB (@lem7648604 _98518) (@lem7648605 _98520)). Qed.
Lemma lem7648607 (_98518 : int) (_98520 : int) : (term109 _98518 _98520) = (term122 _98518 _98520).
Proof. exact (TRANS (@lem7648593 _98518 _98520) (@lem7648606 _98518 _98520)). Qed.
Lemma lem7648608 (_98518 : int) (_98520 : int) : (term127 _98520 _98518) = (term122 _98518 _98520).
Proof. exact (TRANS (@lem7648590 _98518 _98520) (@lem7648607 _98518 _98520)). Qed.
Lemma lem7648610 (y : int) (x : int) : (term128 x y) = (term129 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem7648611 (_98520 : int) (_98518 : int) (_98519 : int) : (term130 _98518 _98519 _98520) = (term131 _98520 _98518 _98519).
Proof. exact (@lem7648610 _98520 (int_add _98518 _98519)). Qed.
Lemma lem7648613 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7648614 (_98518 : int) (_98519 : int) (_98520 : int) : (term132 _98518 _98519 _98520) = (term133 _98518 _98519 _98520).
Proof. exact (@lem7648613 (term134 _98518 _98519) _98520). Qed.
Lemma lem7648616 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7648617 (_98518 : int) (_98519 : int) : (term135 _98518 _98519) = (term136 _98518 _98519).
Proof. exact (@lem7648616 (int_add _98518 _98519) term114). Qed.
Lemma lem7648619 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7648620 (_98518 : int) (_98519 : int) : (term106 _98518 _98519) = (term107 _98518 _98519).
Proof. exact (@lem7648619 _98518 _98519). Qed.
Lemma lem7648621 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7648622 (_98518 : int) (_98519 : int) : (term137 _98518 _98519) = (term138 _98518 _98519).
Proof. exact (MK_COMB (@lem7648621) (@lem7648620 _98518 _98519)). Qed.
Lemma lem7648624 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7648625 : term115 = term116.
Proof. exact (@lem7648624 term117). Qed.
Lemma lem7648626 (_98518 : int) (_98519 : int) : (term136 _98518 _98519) = (term139 _98518 _98519).
Proof. exact (MK_COMB (@lem7648622 _98518 _98519) (@lem7648625)). Qed.
Lemma lem7648627 (_98518 : int) (_98519 : int) : (term135 _98518 _98519) = (term139 _98518 _98519).
Proof. exact (TRANS (@lem7648617 _98518 _98519) (@lem7648626 _98518 _98519)). Qed.
Lemma lem7648628 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7648629 (_98518 : int) (_98519 : int) : (term140 _98518 _98519) = (term141 _98518 _98519).
Proof. exact (MK_COMB (@lem7648628) (@lem7648627 _98518 _98519)). Qed.
Lemma lem7648630 (_98520 : int) : (real_of_int _98520) = (real_of_int _98520).
Proof. exact (eq_refl (real_of_int _98520)). Qed.
Lemma lem7648631 (_98518 : int) (_98519 : int) (_98520 : int) : (term133 _98518 _98519 _98520) = (term142 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7648629 _98518 _98519) (@lem7648630 _98520)). Qed.
Lemma lem7648632 (_98518 : int) (_98519 : int) (_98520 : int) : (term132 _98518 _98519 _98520) = (term142 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7648614 _98518 _98519 _98520) (@lem7648631 _98518 _98519 _98520)). Qed.
Lemma lem7648633 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7648634 (_98518 : int) (_98519 : int) (_98520 : int) : (term143 _98518 _98519 _98520) = (term144 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7648633) (@lem7648632 _98518 _98519 _98520)). Qed.
Lemma lem7648636 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7648637 (_98520 : int) (_98518 : int) (_98519 : int) : (term145 _98520 _98518 _98519) = (term146 _98520 _98518 _98519).
Proof. exact (@lem7648636 (term111 _98520) (int_add _98518 _98519)). Qed.
Lemma lem7648639 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7648640 (_98520 : int) : (term112 _98520) = (term113 _98520).
Proof. exact (@lem7648639 _98520 term114). Qed.
Lemma lem7648642 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7648643 : term115 = term116.
Proof. exact (@lem7648642 term117). Qed.
Lemma lem7648644 (_98520 : int) : (term118 _98520) = (term118 _98520).
Proof. exact (eq_refl (term118 _98520)). Qed.
Lemma lem7648645 (_98520 : int) : (term113 _98520) = (term119 _98520).
Proof. exact (MK_COMB (@lem7648644 _98520) (@lem7648643)). Qed.
Lemma lem7648646 (_98520 : int) : (term112 _98520) = (term119 _98520).
Proof. exact (TRANS (@lem7648640 _98520) (@lem7648645 _98520)). Qed.
Lemma lem7648647 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7648648 (_98520 : int) : (term120 _98520) = (term121 _98520).
Proof. exact (MK_COMB (@lem7648647) (@lem7648646 _98520)). Qed.
Lemma lem7648650 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7648651 (_98518 : int) (_98519 : int) : (term106 _98518 _98519) = (term107 _98518 _98519).
Proof. exact (@lem7648650 _98518 _98519). Qed.
Lemma lem7648652 (_98520 : int) (_98518 : int) (_98519 : int) : (term146 _98520 _98518 _98519) = (term147 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648648 _98520) (@lem7648651 _98518 _98519)). Qed.
Lemma lem7648653 (_98520 : int) (_98518 : int) (_98519 : int) : (term145 _98520 _98518 _98519) = (term147 _98520 _98518 _98519).
Proof. exact (TRANS (@lem7648637 _98520 _98518 _98519) (@lem7648652 _98520 _98518 _98519)). Qed.
Lemma lem7648654 (_98520 : int) (_98518 : int) (_98519 : int) : (term131 _98520 _98518 _98519) = (term148 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648634 _98518 _98519 _98520) (@lem7648653 _98520 _98518 _98519)). Qed.
Lemma lem7648655 (_98520 : int) (_98518 : int) (_98519 : int) : (term130 _98518 _98519 _98520) = (term148 _98520 _98518 _98519).
Proof. exact (TRANS (@lem7648611 _98520 _98518 _98519) (@lem7648654 _98520 _98518 _98519)). Qed.
Lemma lem7648656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7648657 (_98518 : int) (_98520 : int) : (term149 _98520 _98518) = (term123 _98518 _98520).
Proof. exact (MK_COMB (@lem7648656) (@lem7648608 _98518 _98520)). Qed.
Lemma lem7648658 (_98520 : int) (_98518 : int) (_98519 : int) : (term76 _98518 _98519 _98520) = (term150 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648657 _98518 _98520) (@lem7648655 _98520 _98518 _98519)). Qed.
Lemma lem7648659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7648660 (_98520 : int) (_98518 : int) (_98519 : int) : (term78 _98520 _98518 _98519) = (term151 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648659) (@lem7648587 _98520 _98518 _98519)). Qed.
Lemma lem7648661 (_98520 : int) (_98518 : int) (_98519 : int) : (term80 _98518 _98519 _98520) = (term152 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648660 _98520 _98518 _98519) (@lem7648658 _98520 _98518 _98519)). Qed.
Lemma lem7648662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7648663 (_98520 : int) : (term84 _98520) = (term153 _98520).
Proof. exact (MK_COMB (@lem7648662) (@lem7648534 _98520)). Qed.
Lemma lem7648664 (_98520 : int) (_98518 : int) (_98519 : int) : (term86 _98518 _98519 _98520) = (term154 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648663 _98520) (@lem7648661 _98520 _98518 _98519)). Qed.
Lemma lem7648665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7648666 (_98519 : int) : (term84 _98519) = (term153 _98519).
Proof. exact (MK_COMB (@lem7648665) (@lem7648521 _98519)). Qed.
Lemma lem7648667 (_98520 : int) (_98518 : int) (_98519 : int) : (term91 _98518 _98519 _98520) = (term155 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648666 _98519) (@lem7648664 _98520 _98518 _98519)). Qed.
Lemma lem7648668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7648669 (_98518 : int) : (term84 _98518) = (term153 _98518).
Proof. exact (MK_COMB (@lem7648668) (@lem7648508 _98518)). Qed.
Lemma lem7648670 (_98520 : int) (_98518 : int) (_98519 : int) : (term95 _98518 _98519 _98520) = (term156 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648669 _98518) (@lem7648667 _98520 _98518 _98519)). Qed.
Lemma lem7648671 (_98520 : int) (_98518 : int) (_98519 : int) : (term96 _98518 _98519 _98520) = (term156 _98520 _98518 _98519).
Proof. exact (TRANS (@lem7648495 _98518 _98519 _98520) (@lem7648670 _98520 _98518 _98519)). Qed.
Lemma lem7648675 (t : Prop) : (term157 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7648761 (_98520 : int) (_98518 : int) (_98519 : int) : (term158 _98520 _98518 _98519) = (term156 _98520 _98518 _98519).
Proof. exact (@lem7648675 (term156 _98520 _98518 _98519)). Qed.
Lemma lem7648762 (_98518 : int) : (term105 _98518) = (term159 _98518).
Proof. exact (@lem1988287 (real_of_int _98518) term102). Qed.
Lemma lem7648768 (_98518 : int) : (term160 _98518) = (term161 _98518).
Proof. exact (@lem1982792 (real_of_int _98518) term102). Qed.
Lemma lem7648770 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7648771 : term102 = term163.
Proof. exact (@lem7648770 (NUMERAL 0)). Qed.
Lemma lem7648773 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7648774 : term166 = term167.
Proof. exact (@lem7648773 term117). Qed.
Lemma lem7648775 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7648776 : term168 = term169.
Proof. exact (MK_COMB (@lem7648775) (@lem7648774)). Qed.
Lemma lem7648777 : term170 = term171.
Proof. exact (MK_COMB (@lem7648776) (@lem7648771)). Qed.
Lemma lem7648778 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7648780 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7648781 : term175 = term176.
Proof. exact (@lem7648780 term117 term117). Qed.
Lemma lem7648782 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7648783 : term178 = term117.
Proof. exact (EQ_MP (@lem7648782) (@lem940073)). Qed.
Lemma lem7648784 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7648785 : term176 = term116.
Proof. exact (MK_COMB (@lem7648784) (@lem7648783)). Qed.
Lemma lem7648786 : term175 = term116.
Proof. exact (TRANS (@lem7648781) (@lem7648785)). Qed.
Lemma lem7648788 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7648789 : term170 = term102.
Proof. exact (@lem7648788 term117). Qed.
Lemma lem7648790 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7648791 : term180 = term181.
Proof. exact (MK_COMB (@lem7648790) (@lem7648789)). Qed.
Lemma lem7648792 : term172 = term163.
Proof. exact (MK_COMB (@lem7648791) (@lem7648786)). Qed.
Lemma lem7648793 : term171 = term163.
Proof. exact (TRANS (@lem7648778) (@lem7648792)). Qed.
Lemma lem7648794 : term170 = term163.
Proof. exact (TRANS (@lem7648777) (@lem7648793)). Qed.
Lemma lem7648796 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7648797 : term163 = term102.
Proof. exact (@lem7648796 term102). Qed.
Lemma lem7648798 : term170 = term102.
Proof. exact (TRANS (@lem7648794) (@lem7648797)). Qed.
Lemma lem7648799 (_98518 : int) : (term118 _98518) = (term118 _98518).
Proof. exact (eq_refl (term118 _98518)). Qed.
Lemma lem7648800 (_98518 : int) : (term161 _98518) = (term183 _98518).
Proof. exact (MK_COMB (@lem7648799 _98518) (@lem7648798)). Qed.
Lemma lem7648801 (_98518 : int) : (term183 _98518) = (real_of_int _98518).
Proof. exact (@lem1982723 (real_of_int _98518)). Qed.
Lemma lem7648802 (_98518 : int) : (term161 _98518) = (real_of_int _98518).
Proof. exact (TRANS (@lem7648800 _98518) (@lem7648801 _98518)). Qed.
Lemma lem7648804 (_98518 : int) : (term160 _98518) = (real_of_int _98518).
Proof. exact (TRANS (@lem7648768 _98518) (@lem7648802 _98518)). Qed.
Lemma lem7648805 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7648806 (_98518 : int) : (term184 _98518) = (term185 _98518).
Proof. exact (MK_COMB (@lem7648805) (@lem7648804 _98518)). Qed.
Lemma lem7648807 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7648808 (_98518 : int) : (term159 _98518) = (term186 _98518).
Proof. exact (MK_COMB (@lem7648806 _98518) (@lem7648807)). Qed.
Lemma lem7648809 (_98518 : int) : (term105 _98518) = (term186 _98518).
Proof. exact (TRANS (@lem7648762 _98518) (@lem7648808 _98518)). Qed.
Lemma lem7648810 (_98519 : int) : (term105 _98519) = (term159 _98519).
Proof. exact (@lem1988287 (real_of_int _98519) term102). Qed.
Lemma lem7648816 (_98519 : int) : (term160 _98519) = (term161 _98519).
Proof. exact (@lem1982792 (real_of_int _98519) term102). Qed.
Lemma lem7648818 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7648819 : term102 = term163.
Proof. exact (@lem7648818 (NUMERAL 0)). Qed.
Lemma lem7648821 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7648822 : term166 = term167.
Proof. exact (@lem7648821 term117). Qed.
Lemma lem7648823 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7648824 : term168 = term169.
Proof. exact (MK_COMB (@lem7648823) (@lem7648822)). Qed.
Lemma lem7648825 : term170 = term171.
Proof. exact (MK_COMB (@lem7648824) (@lem7648819)). Qed.
Lemma lem7648826 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7648828 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7648829 : term175 = term176.
Proof. exact (@lem7648828 term117 term117). Qed.
Lemma lem7648830 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7648831 : term178 = term117.
Proof. exact (EQ_MP (@lem7648830) (@lem940073)). Qed.
Lemma lem7648832 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7648833 : term176 = term116.
Proof. exact (MK_COMB (@lem7648832) (@lem7648831)). Qed.
Lemma lem7648834 : term175 = term116.
Proof. exact (TRANS (@lem7648829) (@lem7648833)). Qed.
Lemma lem7648836 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7648837 : term170 = term102.
Proof. exact (@lem7648836 term117). Qed.
Lemma lem7648838 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7648839 : term180 = term181.
Proof. exact (MK_COMB (@lem7648838) (@lem7648837)). Qed.
Lemma lem7648840 : term172 = term163.
Proof. exact (MK_COMB (@lem7648839) (@lem7648834)). Qed.
Lemma lem7648841 : term171 = term163.
Proof. exact (TRANS (@lem7648826) (@lem7648840)). Qed.
Lemma lem7648842 : term170 = term163.
Proof. exact (TRANS (@lem7648825) (@lem7648841)). Qed.
Lemma lem7648844 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7648845 : term163 = term102.
Proof. exact (@lem7648844 term102). Qed.
Lemma lem7648846 : term170 = term102.
Proof. exact (TRANS (@lem7648842) (@lem7648845)). Qed.
Lemma lem7648847 (_98519 : int) : (term118 _98519) = (term118 _98519).
Proof. exact (eq_refl (term118 _98519)). Qed.
Lemma lem7648848 (_98519 : int) : (term161 _98519) = (term183 _98519).
Proof. exact (MK_COMB (@lem7648847 _98519) (@lem7648846)). Qed.
Lemma lem7648849 (_98519 : int) : (term183 _98519) = (real_of_int _98519).
Proof. exact (@lem1982723 (real_of_int _98519)). Qed.
Lemma lem7648850 (_98519 : int) : (term161 _98519) = (real_of_int _98519).
Proof. exact (TRANS (@lem7648848 _98519) (@lem7648849 _98519)). Qed.
Lemma lem7648852 (_98519 : int) : (term160 _98519) = (real_of_int _98519).
Proof. exact (TRANS (@lem7648816 _98519) (@lem7648850 _98519)). Qed.
Lemma lem7648853 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7648854 (_98519 : int) : (term184 _98519) = (term185 _98519).
Proof. exact (MK_COMB (@lem7648853) (@lem7648852 _98519)). Qed.
Lemma lem7648855 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7648856 (_98519 : int) : (term159 _98519) = (term186 _98519).
Proof. exact (MK_COMB (@lem7648854 _98519) (@lem7648855)). Qed.
Lemma lem7648857 (_98519 : int) : (term105 _98519) = (term186 _98519).
Proof. exact (TRANS (@lem7648810 _98519) (@lem7648856 _98519)). Qed.
Lemma lem7648858 (_98520 : int) : (term105 _98520) = (term159 _98520).
Proof. exact (@lem1988287 (real_of_int _98520) term102). Qed.
Lemma lem7648864 (_98520 : int) : (term160 _98520) = (term161 _98520).
Proof. exact (@lem1982792 (real_of_int _98520) term102). Qed.
Lemma lem7648866 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7648867 : term102 = term163.
Proof. exact (@lem7648866 (NUMERAL 0)). Qed.
Lemma lem7648869 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7648870 : term166 = term167.
Proof. exact (@lem7648869 term117). Qed.
Lemma lem7648871 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7648872 : term168 = term169.
Proof. exact (MK_COMB (@lem7648871) (@lem7648870)). Qed.
Lemma lem7648873 : term170 = term171.
Proof. exact (MK_COMB (@lem7648872) (@lem7648867)). Qed.
Lemma lem7648874 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7648876 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7648877 : term175 = term176.
Proof. exact (@lem7648876 term117 term117). Qed.
Lemma lem7648878 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7648879 : term178 = term117.
Proof. exact (EQ_MP (@lem7648878) (@lem940073)). Qed.
Lemma lem7648880 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7648881 : term176 = term116.
Proof. exact (MK_COMB (@lem7648880) (@lem7648879)). Qed.
Lemma lem7648882 : term175 = term116.
Proof. exact (TRANS (@lem7648877) (@lem7648881)). Qed.
Lemma lem7648884 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7648885 : term170 = term102.
Proof. exact (@lem7648884 term117). Qed.
Lemma lem7648886 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7648887 : term180 = term181.
Proof. exact (MK_COMB (@lem7648886) (@lem7648885)). Qed.
Lemma lem7648888 : term172 = term163.
Proof. exact (MK_COMB (@lem7648887) (@lem7648882)). Qed.
Lemma lem7648889 : term171 = term163.
Proof. exact (TRANS (@lem7648874) (@lem7648888)). Qed.
Lemma lem7648890 : term170 = term163.
Proof. exact (TRANS (@lem7648873) (@lem7648889)). Qed.
Lemma lem7648892 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7648893 : term163 = term102.
Proof. exact (@lem7648892 term102). Qed.
Lemma lem7648894 : term170 = term102.
Proof. exact (TRANS (@lem7648890) (@lem7648893)). Qed.
Lemma lem7648895 (_98520 : int) : (term118 _98520) = (term118 _98520).
Proof. exact (eq_refl (term118 _98520)). Qed.
Lemma lem7648896 (_98520 : int) : (term161 _98520) = (term183 _98520).
Proof. exact (MK_COMB (@lem7648895 _98520) (@lem7648894)). Qed.
Lemma lem7648897 (_98520 : int) : (term183 _98520) = (real_of_int _98520).
Proof. exact (@lem1982723 (real_of_int _98520)). Qed.
Lemma lem7648898 (_98520 : int) : (term161 _98520) = (real_of_int _98520).
Proof. exact (TRANS (@lem7648896 _98520) (@lem7648897 _98520)). Qed.
Lemma lem7648900 (_98520 : int) : (term160 _98520) = (real_of_int _98520).
Proof. exact (TRANS (@lem7648864 _98520) (@lem7648898 _98520)). Qed.
Lemma lem7648901 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7648902 (_98520 : int) : (term184 _98520) = (term185 _98520).
Proof. exact (MK_COMB (@lem7648901) (@lem7648900 _98520)). Qed.
Lemma lem7648903 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7648904 (_98520 : int) : (term159 _98520) = (term186 _98520).
Proof. exact (MK_COMB (@lem7648902 _98520) (@lem7648903)). Qed.
Lemma lem7648905 (_98520 : int) : (term105 _98520) = (term186 _98520).
Proof. exact (TRANS (@lem7648858 _98520) (@lem7648904 _98520)). Qed.
Lemma lem7648906 (_98520 : int) (_98518 : int) (_98519 : int) : ((real_of_int _98520) = (term107 _98518 _98519)) = ((term187 _98520 _98518 _98519) = term102).
Proof. exact (@lem1988293 (real_of_int _98520) (term107 _98518 _98519)). Qed.
Lemma lem7648918 (_98520 : int) (_98518 : int) (_98519 : int) : (term187 _98520 _98518 _98519) = (term188 _98520 _98518 _98519).
Proof. exact (@lem1982792 (real_of_int _98520) (term107 _98518 _98519)). Qed.
Lemma lem7648925 (_98518 : int) (_98519 : int) : (term189 _98518 _98519) = (term190 _98518 _98519).
Proof. exact (@lem1982781 (real_of_int _98518) term166 (real_of_int _98519)). Qed.
Lemma lem7648926 (_98520 : int) : (term118 _98520) = (term118 _98520).
Proof. exact (eq_refl (term118 _98520)). Qed.
Lemma lem7648927 (_98520 : int) (_98518 : int) (_98519 : int) : (term188 _98520 _98518 _98519) = (term191 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7648926 _98520) (@lem7648925 _98518 _98519)). Qed.
Lemma lem7648928 (_98518 : int) (_98520 : int) (_98519 : int) : (term191 _98520 _98518 _98519) = (term192 _98518 _98520 _98519).
Proof. exact (@lem1982757 (term193 _98518) (real_of_int _98520) (term193 _98519)). Qed.
Lemma lem7648929 (_98519 : int) (_98520 : int) : (term194 _98520 _98519) = (term195 _98519 _98520).
Proof. exact (@lem1982761 (term193 _98519) (real_of_int _98520)). Qed.
Lemma lem7648930 (_98518 : int) : (term196 _98518) = (term196 _98518).
Proof. exact (eq_refl (term196 _98518)). Qed.
Lemma lem7648931 (_98518 : int) (_98519 : int) (_98520 : int) : (term192 _98518 _98520 _98519) = (term197 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7648930 _98518) (@lem7648929 _98519 _98520)). Qed.
Lemma lem7648932 (_98518 : int) (_98519 : int) (_98520 : int) : (term191 _98520 _98518 _98519) = (term197 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7648928 _98518 _98520 _98519) (@lem7648931 _98518 _98519 _98520)). Qed.
Lemma lem7648933 (_98518 : int) (_98519 : int) (_98520 : int) : (term188 _98520 _98518 _98519) = (term197 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7648927 _98520 _98518 _98519) (@lem7648932 _98518 _98519 _98520)). Qed.
Lemma lem7648935 (_98518 : int) (_98519 : int) (_98520 : int) : (term187 _98520 _98518 _98519) = (term197 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7648918 _98520 _98518 _98519) (@lem7648933 _98518 _98519 _98520)). Qed.
Lemma lem7648936 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7648937 (_98518 : int) (_98519 : int) (_98520 : int) : (term198 _98520 _98518 _98519) = (term199 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7648936) (@lem7648935 _98518 _98519 _98520)). Qed.
Lemma lem7648938 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7648939 (_98518 : int) (_98519 : int) (_98520 : int) : ((term187 _98520 _98518 _98519) = term102) = ((term197 _98518 _98519 _98520) = term102).
Proof. exact (MK_COMB (@lem7648937 _98518 _98519 _98520) (@lem7648938)). Qed.
Lemma lem7648940 (_98518 : int) (_98519 : int) (_98520 : int) : ((real_of_int _98520) = (term107 _98518 _98519)) = ((term197 _98518 _98519 _98520) = term102).
Proof. exact (TRANS (@lem7648906 _98520 _98518 _98519) (@lem7648939 _98518 _98519 _98520)). Qed.
Lemma lem7648941 (_98518 : int) (_98520 : int) : (term122 _98520 _98518) = (term200 _98518 _98520).
Proof. exact (@lem1988287 (real_of_int _98518) (term119 _98520)). Qed.
Lemma lem7648953 (_98518 : int) (_98520 : int) : (term201 _98518 _98520) = (term202 _98518 _98520).
Proof. exact (@lem1982792 (real_of_int _98518) (term119 _98520)). Qed.
Lemma lem7648954 (_98520 : int) : (term203 _98520) = (term204 _98520).
Proof. exact (@lem1982781 (real_of_int _98520) term166 term116). Qed.
Lemma lem7648956 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7648957 : term116 = term205.
Proof. exact (@lem7648956 term117). Qed.
Lemma lem7648959 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7648960 : term166 = term167.
Proof. exact (@lem7648959 term117). Qed.
Lemma lem7648961 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7648962 : term168 = term169.
Proof. exact (MK_COMB (@lem7648961) (@lem7648960)). Qed.
Lemma lem7648963 : term206 = term207.
Proof. exact (MK_COMB (@lem7648962) (@lem7648957)). Qed.
Lemma lem7648964 : term207 = term208.
Proof. exact (@lem1981613 term166 term116 term116 term116). Qed.
Lemma lem7648966 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7648967 : term175 = term176.
Proof. exact (@lem7648966 term117 term117). Qed.
Lemma lem7648968 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7648969 : term178 = term117.
Proof. exact (EQ_MP (@lem7648968) (@lem940073)). Qed.
Lemma lem7648970 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7648971 : term176 = term116.
Proof. exact (MK_COMB (@lem7648970) (@lem7648969)). Qed.
Lemma lem7648972 : term175 = term116.
Proof. exact (TRANS (@lem7648967) (@lem7648971)). Qed.
Lemma lem7648974 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7648975 : term206 = term211.
Proof. exact (@lem7648974 term117 term117). Qed.
Lemma lem7648976 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7648977 : term178 = term117.
Proof. exact (EQ_MP (@lem7648976) (@lem940073)). Qed.
Lemma lem7648978 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7648979 : term176 = term116.
Proof. exact (MK_COMB (@lem7648978) (@lem7648977)). Qed.
Lemma lem7648980 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7648981 : term211 = term166.
Proof. exact (MK_COMB (@lem7648980) (@lem7648979)). Qed.
Lemma lem7648982 : term206 = term166.
Proof. exact (TRANS (@lem7648975) (@lem7648981)). Qed.
Lemma lem7648983 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7648984 : term212 = term213.
Proof. exact (MK_COMB (@lem7648983) (@lem7648982)). Qed.
Lemma lem7648985 : term208 = term167.
Proof. exact (MK_COMB (@lem7648984) (@lem7648972)). Qed.
Lemma lem7648986 : term207 = term167.
Proof. exact (TRANS (@lem7648964) (@lem7648985)). Qed.
Lemma lem7648987 : term206 = term167.
Proof. exact (TRANS (@lem7648963) (@lem7648986)). Qed.
Lemma lem7648989 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7648990 : term167 = term166.
Proof. exact (@lem7648989 term166). Qed.
Lemma lem7648991 : term206 = term166.
Proof. exact (TRANS (@lem7648987) (@lem7648990)). Qed.
Lemma lem7648994 (_98520 : int) : (term196 _98520) = (term196 _98520).
Proof. exact (eq_refl (term196 _98520)). Qed.
Lemma lem7648995 (_98520 : int) : (term204 _98520) = (term214 _98520).
Proof. exact (MK_COMB (@lem7648994 _98520) (@lem7648991)). Qed.
Lemma lem7648996 (_98520 : int) : (term203 _98520) = (term214 _98520).
Proof. exact (TRANS (@lem7648954 _98520) (@lem7648995 _98520)). Qed.
Lemma lem7648997 (_98518 : int) : (term118 _98518) = (term118 _98518).
Proof. exact (eq_refl (term118 _98518)). Qed.
Lemma lem7649000 (_98518 : int) (_98520 : int) : (term202 _98518 _98520) = (term215 _98518 _98520).
Proof. exact (MK_COMB (@lem7648997 _98518) (@lem7648996 _98520)). Qed.
Lemma lem7649002 (_98518 : int) (_98520 : int) : (term201 _98518 _98520) = (term215 _98518 _98520).
Proof. exact (TRANS (@lem7648953 _98518 _98520) (@lem7649000 _98518 _98520)). Qed.
Lemma lem7649003 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7649004 (_98518 : int) (_98520 : int) : (term216 _98518 _98520) = (term217 _98518 _98520).
Proof. exact (MK_COMB (@lem7649003) (@lem7649002 _98518 _98520)). Qed.
Lemma lem7649005 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7649006 (_98518 : int) (_98520 : int) : (term200 _98518 _98520) = (term218 _98518 _98520).
Proof. exact (MK_COMB (@lem7649004 _98518 _98520) (@lem7649005)). Qed.
Lemma lem7649007 (_98518 : int) (_98520 : int) : (term122 _98520 _98518) = (term218 _98518 _98520).
Proof. exact (TRANS (@lem7648941 _98518 _98520) (@lem7649006 _98518 _98520)). Qed.
Lemma lem7649008 (_98519 : int) : ((real_of_int _98519) = term102) = ((term160 _98519) = term102).
Proof. exact (@lem1988293 (real_of_int _98519) term102). Qed.
Lemma lem7649014 (_98519 : int) : (term160 _98519) = (term161 _98519).
Proof. exact (@lem1982792 (real_of_int _98519) term102). Qed.
Lemma lem7649016 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7649017 : term102 = term163.
Proof. exact (@lem7649016 (NUMERAL 0)). Qed.
Lemma lem7649019 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7649020 : term166 = term167.
Proof. exact (@lem7649019 term117). Qed.
Lemma lem7649021 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649022 : term168 = term169.
Proof. exact (MK_COMB (@lem7649021) (@lem7649020)). Qed.
Lemma lem7649023 : term170 = term171.
Proof. exact (MK_COMB (@lem7649022) (@lem7649017)). Qed.
Lemma lem7649024 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7649026 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649027 : term175 = term176.
Proof. exact (@lem7649026 term117 term117). Qed.
Lemma lem7649028 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649029 : term178 = term117.
Proof. exact (EQ_MP (@lem7649028) (@lem940073)). Qed.
Lemma lem7649030 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649031 : term176 = term116.
Proof. exact (MK_COMB (@lem7649030) (@lem7649029)). Qed.
Lemma lem7649032 : term175 = term116.
Proof. exact (TRANS (@lem7649027) (@lem7649031)). Qed.
Lemma lem7649034 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7649035 : term170 = term102.
Proof. exact (@lem7649034 term117). Qed.
Lemma lem7649036 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7649037 : term180 = term181.
Proof. exact (MK_COMB (@lem7649036) (@lem7649035)). Qed.
Lemma lem7649038 : term172 = term163.
Proof. exact (MK_COMB (@lem7649037) (@lem7649032)). Qed.
Lemma lem7649039 : term171 = term163.
Proof. exact (TRANS (@lem7649024) (@lem7649038)). Qed.
Lemma lem7649040 : term170 = term163.
Proof. exact (TRANS (@lem7649023) (@lem7649039)). Qed.
Lemma lem7649042 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7649043 : term163 = term102.
Proof. exact (@lem7649042 term102). Qed.
Lemma lem7649044 : term170 = term102.
Proof. exact (TRANS (@lem7649040) (@lem7649043)). Qed.
Lemma lem7649045 (_98519 : int) : (term118 _98519) = (term118 _98519).
Proof. exact (eq_refl (term118 _98519)). Qed.
Lemma lem7649046 (_98519 : int) : (term161 _98519) = (term183 _98519).
Proof. exact (MK_COMB (@lem7649045 _98519) (@lem7649044)). Qed.
Lemma lem7649047 (_98519 : int) : (term183 _98519) = (real_of_int _98519).
Proof. exact (@lem1982723 (real_of_int _98519)). Qed.
Lemma lem7649048 (_98519 : int) : (term161 _98519) = (real_of_int _98519).
Proof. exact (TRANS (@lem7649046 _98519) (@lem7649047 _98519)). Qed.
Lemma lem7649050 (_98519 : int) : (term160 _98519) = (real_of_int _98519).
Proof. exact (TRANS (@lem7649014 _98519) (@lem7649048 _98519)). Qed.
Lemma lem7649051 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7649052 (_98519 : int) : (term219 _98519) = (term108 _98519).
Proof. exact (MK_COMB (@lem7649051) (@lem7649050 _98519)). Qed.
Lemma lem7649053 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7649054 (_98519 : int) : ((term160 _98519) = term102) = ((real_of_int _98519) = term102).
Proof. exact (MK_COMB (@lem7649052 _98519) (@lem7649053)). Qed.
Lemma lem7649055 (_98519 : int) : ((real_of_int _98519) = term102) = ((real_of_int _98519) = term102).
Proof. exact (TRANS (@lem7649008 _98519) (@lem7649054 _98519)). Qed.
Lemma lem7649056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7649057 (_98518 : int) (_98520 : int) : (term123 _98520 _98518) = (term220 _98518 _98520).
Proof. exact (MK_COMB (@lem7649056) (@lem7649007 _98518 _98520)). Qed.
Lemma lem7649058 (_98518 : int) (_98520 : int) (_98519 : int) : (term124 _98520 _98518 _98519) = (term221 _98518 _98520 _98519).
Proof. exact (MK_COMB (@lem7649057 _98518 _98520) (@lem7649055 _98519)). Qed.
Lemma lem7649059 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7649060 (_98518 : int) (_98519 : int) (_98520 : int) : (term125 _98520 _98518 _98519) = (term222 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649059) (@lem7648940 _98518 _98519 _98520)). Qed.
Lemma lem7649061 (_98518 : int) (_98520 : int) (_98519 : int) : (term126 _98520 _98518 _98519) = (term223 _98518 _98520 _98519).
Proof. exact (MK_COMB (@lem7649060 _98518 _98519 _98520) (@lem7649058 _98518 _98520 _98519)). Qed.
Lemma lem7649062 (_98520 : int) (_98518 : int) : (term122 _98518 _98520) = (term200 _98520 _98518).
Proof. exact (@lem1988287 (real_of_int _98520) (term119 _98518)). Qed.
Lemma lem7649074 (_98520 : int) (_98518 : int) : (term201 _98520 _98518) = (term202 _98520 _98518).
Proof. exact (@lem1982792 (real_of_int _98520) (term119 _98518)). Qed.
Lemma lem7649075 (_98518 : int) : (term203 _98518) = (term204 _98518).
Proof. exact (@lem1982781 (real_of_int _98518) term166 term116). Qed.
Lemma lem7649077 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7649078 : term116 = term205.
Proof. exact (@lem7649077 term117). Qed.
Lemma lem7649080 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7649081 : term166 = term167.
Proof. exact (@lem7649080 term117). Qed.
Lemma lem7649082 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649083 : term168 = term169.
Proof. exact (MK_COMB (@lem7649082) (@lem7649081)). Qed.
Lemma lem7649084 : term206 = term207.
Proof. exact (MK_COMB (@lem7649083) (@lem7649078)). Qed.
Lemma lem7649085 : term207 = term208.
Proof. exact (@lem1981613 term166 term116 term116 term116). Qed.
Lemma lem7649087 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649088 : term175 = term176.
Proof. exact (@lem7649087 term117 term117). Qed.
Lemma lem7649089 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649090 : term178 = term117.
Proof. exact (EQ_MP (@lem7649089) (@lem940073)). Qed.
Lemma lem7649091 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649092 : term176 = term116.
Proof. exact (MK_COMB (@lem7649091) (@lem7649090)). Qed.
Lemma lem7649093 : term175 = term116.
Proof. exact (TRANS (@lem7649088) (@lem7649092)). Qed.
Lemma lem7649095 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7649096 : term206 = term211.
Proof. exact (@lem7649095 term117 term117). Qed.
Lemma lem7649097 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649098 : term178 = term117.
Proof. exact (EQ_MP (@lem7649097) (@lem940073)). Qed.
Lemma lem7649099 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649100 : term176 = term116.
Proof. exact (MK_COMB (@lem7649099) (@lem7649098)). Qed.
Lemma lem7649101 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7649102 : term211 = term166.
Proof. exact (MK_COMB (@lem7649101) (@lem7649100)). Qed.
Lemma lem7649103 : term206 = term166.
Proof. exact (TRANS (@lem7649096) (@lem7649102)). Qed.
Lemma lem7649104 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7649105 : term212 = term213.
Proof. exact (MK_COMB (@lem7649104) (@lem7649103)). Qed.
Lemma lem7649106 : term208 = term167.
Proof. exact (MK_COMB (@lem7649105) (@lem7649093)). Qed.
Lemma lem7649107 : term207 = term167.
Proof. exact (TRANS (@lem7649085) (@lem7649106)). Qed.
Lemma lem7649108 : term206 = term167.
Proof. exact (TRANS (@lem7649084) (@lem7649107)). Qed.
Lemma lem7649110 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7649111 : term167 = term166.
Proof. exact (@lem7649110 term166). Qed.
Lemma lem7649112 : term206 = term166.
Proof. exact (TRANS (@lem7649108) (@lem7649111)). Qed.
Lemma lem7649115 (_98518 : int) : (term196 _98518) = (term196 _98518).
Proof. exact (eq_refl (term196 _98518)). Qed.
Lemma lem7649116 (_98518 : int) : (term204 _98518) = (term214 _98518).
Proof. exact (MK_COMB (@lem7649115 _98518) (@lem7649112)). Qed.
Lemma lem7649117 (_98518 : int) : (term203 _98518) = (term214 _98518).
Proof. exact (TRANS (@lem7649075 _98518) (@lem7649116 _98518)). Qed.
Lemma lem7649118 (_98520 : int) : (term118 _98520) = (term118 _98520).
Proof. exact (eq_refl (term118 _98520)). Qed.
Lemma lem7649119 (_98520 : int) (_98518 : int) : (term202 _98520 _98518) = (term215 _98520 _98518).
Proof. exact (MK_COMB (@lem7649118 _98520) (@lem7649117 _98518)). Qed.
Lemma lem7649124 (_98518 : int) (_98520 : int) : (term215 _98520 _98518) = (term224 _98518 _98520).
Proof. exact (@lem1982757 (term193 _98518) (real_of_int _98520) term166). Qed.
Lemma lem7649125 (_98518 : int) (_98520 : int) : (term202 _98520 _98518) = (term224 _98518 _98520).
Proof. exact (TRANS (@lem7649119 _98520 _98518) (@lem7649124 _98518 _98520)). Qed.
Lemma lem7649127 (_98518 : int) (_98520 : int) : (term201 _98520 _98518) = (term224 _98518 _98520).
Proof. exact (TRANS (@lem7649074 _98520 _98518) (@lem7649125 _98518 _98520)). Qed.
Lemma lem7649128 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7649129 (_98518 : int) (_98520 : int) : (term216 _98520 _98518) = (term225 _98518 _98520).
Proof. exact (MK_COMB (@lem7649128) (@lem7649127 _98518 _98520)). Qed.
Lemma lem7649130 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7649131 (_98518 : int) (_98520 : int) : (term200 _98520 _98518) = (term226 _98518 _98520).
Proof. exact (MK_COMB (@lem7649129 _98518 _98520) (@lem7649130)). Qed.
Lemma lem7649132 (_98518 : int) (_98520 : int) : (term122 _98518 _98520) = (term226 _98518 _98520).
Proof. exact (TRANS (@lem7649062 _98520 _98518) (@lem7649131 _98518 _98520)). Qed.
Lemma lem7649133 (_98520 : int) (_98518 : int) (_98519 : int) : (term142 _98518 _98519 _98520) = (term227 _98520 _98518 _98519).
Proof. exact (@lem1988287 (real_of_int _98520) (term139 _98518 _98519)). Qed.
Lemma lem7649150 (_98518 : int) (_98519 : int) : (term139 _98518 _98519) = (term228 _98518 _98519).
Proof. exact (@lem1982755 (real_of_int _98518) (real_of_int _98519) term116). Qed.
Lemma lem7649153 (_98520 : int) : (term229 _98520) = (term229 _98520).
Proof. exact (eq_refl (term229 _98520)). Qed.
Lemma lem7649154 (_98520 : int) (_98518 : int) (_98519 : int) : (term230 _98520 _98518 _98519) = (term231 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7649153 _98520) (@lem7649150 _98518 _98519)). Qed.
Lemma lem7649155 (_98520 : int) (_98518 : int) (_98519 : int) : (term231 _98520 _98518 _98519) = (term232 _98520 _98518 _98519).
Proof. exact (@lem1982792 (real_of_int _98520) (term228 _98518 _98519)). Qed.
Lemma lem7649156 (_98518 : int) (_98519 : int) : (term233 _98518 _98519) = (term234 _98518 _98519).
Proof. exact (@lem1982781 (real_of_int _98518) term166 (term119 _98519)). Qed.
Lemma lem7649157 (_98519 : int) : (term203 _98519) = (term204 _98519).
Proof. exact (@lem1982781 (real_of_int _98519) term166 term116). Qed.
Lemma lem7649159 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7649160 : term116 = term205.
Proof. exact (@lem7649159 term117). Qed.
Lemma lem7649162 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7649163 : term166 = term167.
Proof. exact (@lem7649162 term117). Qed.
Lemma lem7649164 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649165 : term168 = term169.
Proof. exact (MK_COMB (@lem7649164) (@lem7649163)). Qed.
Lemma lem7649166 : term206 = term207.
Proof. exact (MK_COMB (@lem7649165) (@lem7649160)). Qed.
Lemma lem7649167 : term207 = term208.
Proof. exact (@lem1981613 term166 term116 term116 term116). Qed.
Lemma lem7649169 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649170 : term175 = term176.
Proof. exact (@lem7649169 term117 term117). Qed.
Lemma lem7649171 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649172 : term178 = term117.
Proof. exact (EQ_MP (@lem7649171) (@lem940073)). Qed.
Lemma lem7649173 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649174 : term176 = term116.
Proof. exact (MK_COMB (@lem7649173) (@lem7649172)). Qed.
Lemma lem7649175 : term175 = term116.
Proof. exact (TRANS (@lem7649170) (@lem7649174)). Qed.
Lemma lem7649177 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7649178 : term206 = term211.
Proof. exact (@lem7649177 term117 term117). Qed.
Lemma lem7649179 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649180 : term178 = term117.
Proof. exact (EQ_MP (@lem7649179) (@lem940073)). Qed.
Lemma lem7649181 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649182 : term176 = term116.
Proof. exact (MK_COMB (@lem7649181) (@lem7649180)). Qed.
Lemma lem7649183 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7649184 : term211 = term166.
Proof. exact (MK_COMB (@lem7649183) (@lem7649182)). Qed.
Lemma lem7649185 : term206 = term166.
Proof. exact (TRANS (@lem7649178) (@lem7649184)). Qed.
Lemma lem7649186 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7649187 : term212 = term213.
Proof. exact (MK_COMB (@lem7649186) (@lem7649185)). Qed.
Lemma lem7649188 : term208 = term167.
Proof. exact (MK_COMB (@lem7649187) (@lem7649175)). Qed.
Lemma lem7649189 : term207 = term167.
Proof. exact (TRANS (@lem7649167) (@lem7649188)). Qed.
Lemma lem7649190 : term206 = term167.
Proof. exact (TRANS (@lem7649166) (@lem7649189)). Qed.
Lemma lem7649192 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7649193 : term167 = term166.
Proof. exact (@lem7649192 term166). Qed.
Lemma lem7649194 : term206 = term166.
Proof. exact (TRANS (@lem7649190) (@lem7649193)). Qed.
Lemma lem7649197 (_98519 : int) : (term196 _98519) = (term196 _98519).
Proof. exact (eq_refl (term196 _98519)). Qed.
Lemma lem7649198 (_98519 : int) : (term204 _98519) = (term214 _98519).
Proof. exact (MK_COMB (@lem7649197 _98519) (@lem7649194)). Qed.
Lemma lem7649199 (_98519 : int) : (term203 _98519) = (term214 _98519).
Proof. exact (TRANS (@lem7649157 _98519) (@lem7649198 _98519)). Qed.
Lemma lem7649202 (_98518 : int) : (term196 _98518) = (term196 _98518).
Proof. exact (eq_refl (term196 _98518)). Qed.
Lemma lem7649203 (_98518 : int) (_98519 : int) : (term234 _98518 _98519) = (term235 _98518 _98519).
Proof. exact (MK_COMB (@lem7649202 _98518) (@lem7649199 _98519)). Qed.
Lemma lem7649204 (_98518 : int) (_98519 : int) : (term233 _98518 _98519) = (term235 _98518 _98519).
Proof. exact (TRANS (@lem7649156 _98518 _98519) (@lem7649203 _98518 _98519)). Qed.
Lemma lem7649205 (_98520 : int) : (term118 _98520) = (term118 _98520).
Proof. exact (eq_refl (term118 _98520)). Qed.
Lemma lem7649206 (_98520 : int) (_98518 : int) (_98519 : int) : (term232 _98520 _98518 _98519) = (term236 _98520 _98518 _98519).
Proof. exact (MK_COMB (@lem7649205 _98520) (@lem7649204 _98518 _98519)). Qed.
Lemma lem7649207 (_98518 : int) (_98520 : int) (_98519 : int) : (term236 _98520 _98518 _98519) = (term237 _98518 _98520 _98519).
Proof. exact (@lem1982757 (term193 _98518) (real_of_int _98520) (term214 _98519)). Qed.
Lemma lem7649212 (_98519 : int) (_98520 : int) : (term215 _98520 _98519) = (term224 _98519 _98520).
Proof. exact (@lem1982757 (term193 _98519) (real_of_int _98520) term166). Qed.
Lemma lem7649213 (_98518 : int) : (term196 _98518) = (term196 _98518).
Proof. exact (eq_refl (term196 _98518)). Qed.
Lemma lem7649214 (_98518 : int) (_98519 : int) (_98520 : int) : (term237 _98518 _98520 _98519) = (term238 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649213 _98518) (@lem7649212 _98519 _98520)). Qed.
Lemma lem7649215 (_98518 : int) (_98519 : int) (_98520 : int) : (term236 _98520 _98518 _98519) = (term238 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649207 _98518 _98520 _98519) (@lem7649214 _98518 _98519 _98520)). Qed.
Lemma lem7649216 (_98518 : int) (_98519 : int) (_98520 : int) : (term232 _98520 _98518 _98519) = (term238 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649206 _98520 _98518 _98519) (@lem7649215 _98518 _98519 _98520)). Qed.
Lemma lem7649217 (_98518 : int) (_98519 : int) (_98520 : int) : (term231 _98520 _98518 _98519) = (term238 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649155 _98520 _98518 _98519) (@lem7649216 _98518 _98519 _98520)). Qed.
Lemma lem7649218 (_98518 : int) (_98519 : int) (_98520 : int) : (term230 _98520 _98518 _98519) = (term238 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649154 _98520 _98518 _98519) (@lem7649217 _98518 _98519 _98520)). Qed.
Lemma lem7649219 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7649220 (_98518 : int) (_98519 : int) (_98520 : int) : (term239 _98520 _98518 _98519) = (term240 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649219) (@lem7649218 _98518 _98519 _98520)). Qed.
Lemma lem7649221 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7649222 (_98518 : int) (_98519 : int) (_98520 : int) : (term227 _98520 _98518 _98519) = (term241 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649220 _98518 _98519 _98520) (@lem7649221)). Qed.
Lemma lem7649223 (_98518 : int) (_98519 : int) (_98520 : int) : (term142 _98518 _98519 _98520) = (term241 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649133 _98520 _98518 _98519) (@lem7649222 _98518 _98519 _98520)). Qed.
Lemma lem7649224 (_98518 : int) (_98519 : int) (_98520 : int) : (term147 _98520 _98518 _98519) = (term242 _98518 _98519 _98520).
Proof. exact (@lem1988287 (term107 _98518 _98519) (term119 _98520)). Qed.
Lemma lem7649242 (_98518 : int) (_98519 : int) (_98520 : int) : (term243 _98518 _98519 _98520) = (term244 _98518 _98519 _98520).
Proof. exact (@lem1982792 (term107 _98518 _98519) (term119 _98520)). Qed.
Lemma lem7649243 (_98520 : int) : (term203 _98520) = (term204 _98520).
Proof. exact (@lem1982781 (real_of_int _98520) term166 term116). Qed.
Lemma lem7649245 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7649246 : term116 = term205.
Proof. exact (@lem7649245 term117). Qed.
Lemma lem7649248 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7649249 : term166 = term167.
Proof. exact (@lem7649248 term117). Qed.
Lemma lem7649250 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649251 : term168 = term169.
Proof. exact (MK_COMB (@lem7649250) (@lem7649249)). Qed.
Lemma lem7649252 : term206 = term207.
Proof. exact (MK_COMB (@lem7649251) (@lem7649246)). Qed.
Lemma lem7649253 : term207 = term208.
Proof. exact (@lem1981613 term166 term116 term116 term116). Qed.
Lemma lem7649255 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649256 : term175 = term176.
Proof. exact (@lem7649255 term117 term117). Qed.
Lemma lem7649257 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649258 : term178 = term117.
Proof. exact (EQ_MP (@lem7649257) (@lem940073)). Qed.
Lemma lem7649259 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649260 : term176 = term116.
Proof. exact (MK_COMB (@lem7649259) (@lem7649258)). Qed.
Lemma lem7649261 : term175 = term116.
Proof. exact (TRANS (@lem7649256) (@lem7649260)). Qed.
Lemma lem7649263 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7649264 : term206 = term211.
Proof. exact (@lem7649263 term117 term117). Qed.
Lemma lem7649265 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649266 : term178 = term117.
Proof. exact (EQ_MP (@lem7649265) (@lem940073)). Qed.
Lemma lem7649267 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649268 : term176 = term116.
Proof. exact (MK_COMB (@lem7649267) (@lem7649266)). Qed.
Lemma lem7649269 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7649270 : term211 = term166.
Proof. exact (MK_COMB (@lem7649269) (@lem7649268)). Qed.
Lemma lem7649271 : term206 = term166.
Proof. exact (TRANS (@lem7649264) (@lem7649270)). Qed.
Lemma lem7649272 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7649273 : term212 = term213.
Proof. exact (MK_COMB (@lem7649272) (@lem7649271)). Qed.
Lemma lem7649274 : term208 = term167.
Proof. exact (MK_COMB (@lem7649273) (@lem7649261)). Qed.
Lemma lem7649275 : term207 = term167.
Proof. exact (TRANS (@lem7649253) (@lem7649274)). Qed.
Lemma lem7649276 : term206 = term167.
Proof. exact (TRANS (@lem7649252) (@lem7649275)). Qed.
Lemma lem7649278 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7649279 : term167 = term166.
Proof. exact (@lem7649278 term166). Qed.
Lemma lem7649280 : term206 = term166.
Proof. exact (TRANS (@lem7649276) (@lem7649279)). Qed.
Lemma lem7649283 (_98520 : int) : (term196 _98520) = (term196 _98520).
Proof. exact (eq_refl (term196 _98520)). Qed.
Lemma lem7649284 (_98520 : int) : (term204 _98520) = (term214 _98520).
Proof. exact (MK_COMB (@lem7649283 _98520) (@lem7649280)). Qed.
Lemma lem7649285 (_98520 : int) : (term203 _98520) = (term214 _98520).
Proof. exact (TRANS (@lem7649243 _98520) (@lem7649284 _98520)). Qed.
Lemma lem7649286 (_98518 : int) (_98519 : int) : (term138 _98518 _98519) = (term138 _98518 _98519).
Proof. exact (eq_refl (term138 _98518 _98519)). Qed.
Lemma lem7649287 (_98518 : int) (_98519 : int) (_98520 : int) : (term244 _98518 _98519 _98520) = (term245 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649286 _98518 _98519) (@lem7649285 _98520)). Qed.
Lemma lem7649292 (_98518 : int) (_98519 : int) (_98520 : int) : (term245 _98518 _98519 _98520) = (term246 _98518 _98519 _98520).
Proof. exact (@lem1982755 (real_of_int _98518) (real_of_int _98519) (term214 _98520)). Qed.
Lemma lem7649293 (_98518 : int) (_98519 : int) (_98520 : int) : (term244 _98518 _98519 _98520) = (term246 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649287 _98518 _98519 _98520) (@lem7649292 _98518 _98519 _98520)). Qed.
Lemma lem7649295 (_98518 : int) (_98519 : int) (_98520 : int) : (term243 _98518 _98519 _98520) = (term246 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649242 _98518 _98519 _98520) (@lem7649293 _98518 _98519 _98520)). Qed.
Lemma lem7649296 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7649297 (_98518 : int) (_98519 : int) (_98520 : int) : (term247 _98518 _98519 _98520) = (term248 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649296) (@lem7649295 _98518 _98519 _98520)). Qed.
Lemma lem7649298 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7649299 (_98518 : int) (_98519 : int) (_98520 : int) : (term242 _98518 _98519 _98520) = (term249 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649297 _98518 _98519 _98520) (@lem7649298)). Qed.
Lemma lem7649300 (_98518 : int) (_98519 : int) (_98520 : int) : (term147 _98520 _98518 _98519) = (term249 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649224 _98518 _98519 _98520) (@lem7649299 _98518 _98519 _98520)). Qed.
Lemma lem7649301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7649302 (_98518 : int) (_98519 : int) (_98520 : int) : (term144 _98518 _98519 _98520) = (term250 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649301) (@lem7649223 _98518 _98519 _98520)). Qed.
Lemma lem7649303 (_98518 : int) (_98519 : int) (_98520 : int) : (term148 _98520 _98518 _98519) = (term251 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649302 _98518 _98519 _98520) (@lem7649300 _98518 _98519 _98520)). Qed.
Lemma lem7649304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7649305 (_98518 : int) (_98520 : int) : (term123 _98518 _98520) = (term252 _98518 _98520).
Proof. exact (MK_COMB (@lem7649304) (@lem7649132 _98518 _98520)). Qed.
Lemma lem7649306 (_98518 : int) (_98519 : int) (_98520 : int) : (term150 _98520 _98518 _98519) = (term253 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649305 _98518 _98520) (@lem7649303 _98518 _98519 _98520)). Qed.
Lemma lem7649307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7649308 (_98518 : int) (_98520 : int) (_98519 : int) : (term151 _98520 _98518 _98519) = (term254 _98518 _98520 _98519).
Proof. exact (MK_COMB (@lem7649307) (@lem7649061 _98518 _98520 _98519)). Qed.
Lemma lem7649309 (_98518 : int) (_98519 : int) (_98520 : int) : (term152 _98520 _98518 _98519) = (term255 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649308 _98518 _98520 _98519) (@lem7649306 _98518 _98519 _98520)). Qed.
Lemma lem7649310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7649311 (_98520 : int) : (term153 _98520) = (term256 _98520).
Proof. exact (MK_COMB (@lem7649310) (@lem7648905 _98520)). Qed.
Lemma lem7649312 (_98518 : int) (_98519 : int) (_98520 : int) : (term154 _98520 _98518 _98519) = (term257 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649311 _98520) (@lem7649309 _98518 _98519 _98520)). Qed.
Lemma lem7649313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7649314 (_98519 : int) : (term153 _98519) = (term256 _98519).
Proof. exact (MK_COMB (@lem7649313) (@lem7648857 _98519)). Qed.
Lemma lem7649315 (_98518 : int) (_98519 : int) (_98520 : int) : (term155 _98520 _98518 _98519) = (term258 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649314 _98519) (@lem7649312 _98518 _98519 _98520)). Qed.
Lemma lem7649316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7649317 (_98518 : int) : (term153 _98518) = (term256 _98518).
Proof. exact (MK_COMB (@lem7649316) (@lem7648809 _98518)). Qed.
Lemma lem7649318 (_98518 : int) (_98519 : int) (_98520 : int) : (term156 _98520 _98518 _98519) = (term259 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649317 _98518) (@lem7649315 _98518 _98519 _98520)). Qed.
Lemma lem7649325 (_98518 : int) (_98519 : int) (_98520 : int) : (term158 _98520 _98518 _98519) = (term259 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7648761 _98520 _98518 _98519) (@lem7649318 _98518 _98519 _98520)). Qed.
Lemma lem7649342 (_98518 : int) (_98519 : int) (_98520 : int) : (term253 _98518 _98519 _98520) = (term260 _98518 _98519 _98520).
Proof. exact (@lem19158 (term241 _98518 _98519 _98520) (term226 _98518 _98520) (term249 _98518 _98519 _98520)). Qed.
Lemma lem7649355 (_98518 : int) (_98520 : int) (_98519 : int) : (term254 _98518 _98520 _98519) = (term254 _98518 _98520 _98519).
Proof. exact (eq_refl (term254 _98518 _98520 _98519)). Qed.
Lemma lem7649356 (_98518 : int) (_98519 : int) (_98520 : int) : (term255 _98518 _98519 _98520) = (term261 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649355 _98518 _98520 _98519) (@lem7649342 _98518 _98519 _98520)). Qed.
Lemma lem7649357 (_98518 : int) (_98519 : int) (_98520 : int) : (term261 _98518 _98519 _98520) = (term262 _98518 _98519 _98520).
Proof. exact (@lem19158 (term263 _98518 _98519 _98520) (term223 _98518 _98520 _98519) (term264 _98518 _98519 _98520)). Qed.
Lemma lem7649364 (_98518 : int) (_98519 : int) (_98520 : int) : (term265 _98518 _98519 _98520) = (term266 _98518 _98519 _98520).
Proof. exact (@lem19367 ((term197 _98518 _98519 _98520) = term102) (term221 _98518 _98520 _98519) (term264 _98518 _98519 _98520)). Qed.
Lemma lem7649371 (_98518 : int) (_98519 : int) (_98520 : int) : (term267 _98518 _98519 _98520) = (term268 _98518 _98519 _98520).
Proof. exact (@lem19367 ((term197 _98518 _98519 _98520) = term102) (term221 _98518 _98520 _98519) (term263 _98518 _98519 _98520)). Qed.
Lemma lem7649372 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7649373 (_98518 : int) (_98519 : int) (_98520 : int) : (term269 _98518 _98519 _98520) = (term270 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649372) (@lem7649371 _98518 _98519 _98520)). Qed.
Lemma lem7649374 (_98518 : int) (_98519 : int) (_98520 : int) : (term262 _98518 _98519 _98520) = (term271 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649373 _98518 _98519 _98520) (@lem7649364 _98518 _98519 _98520)). Qed.
Lemma lem7649375 (_98518 : int) (_98519 : int) (_98520 : int) : (term261 _98518 _98519 _98520) = (term271 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649357 _98518 _98519 _98520) (@lem7649374 _98518 _98519 _98520)). Qed.
Lemma lem7649376 (_98518 : int) (_98519 : int) (_98520 : int) : (term255 _98518 _98519 _98520) = (term271 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649356 _98518 _98519 _98520) (@lem7649375 _98518 _98519 _98520)). Qed.
Lemma lem7649379 (_98520 : int) : (term256 _98520) = (term256 _98520).
Proof. exact (eq_refl (term256 _98520)). Qed.
Lemma lem7649380 (_98518 : int) (_98519 : int) (_98520 : int) : (term257 _98518 _98519 _98520) = (term272 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649379 _98520) (@lem7649376 _98518 _98519 _98520)). Qed.
Lemma lem7649381 (_98518 : int) (_98519 : int) (_98520 : int) : (term272 _98518 _98519 _98520) = (term273 _98518 _98519 _98520).
Proof. exact (@lem19158 (term268 _98518 _98519 _98520) (term186 _98520) (term266 _98518 _98519 _98520)). Qed.
Lemma lem7649388 (_98518 : int) (_98519 : int) (_98520 : int) : (term274 _98518 _98519 _98520) = (term275 _98518 _98519 _98520).
Proof. exact (@lem19158 (term276 _98518 _98519 _98520) (term186 _98520) (term277 _98518 _98519 _98520)). Qed.
Lemma lem7649395 (_98518 : int) (_98519 : int) (_98520 : int) : (term278 _98518 _98519 _98520) = (term279 _98518 _98519 _98520).
Proof. exact (@lem19158 (term280 _98518 _98519 _98520) (term186 _98520) (term281 _98518 _98519 _98520)). Qed.
Lemma lem7649396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7649397 (_98518 : int) (_98519 : int) (_98520 : int) : (term282 _98518 _98519 _98520) = (term283 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649396) (@lem7649395 _98518 _98519 _98520)). Qed.
Lemma lem7649398 (_98518 : int) (_98519 : int) (_98520 : int) : (term273 _98518 _98519 _98520) = (term284 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649397 _98518 _98519 _98520) (@lem7649388 _98518 _98519 _98520)). Qed.
Lemma lem7649399 (_98518 : int) (_98519 : int) (_98520 : int) : (term272 _98518 _98519 _98520) = (term284 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649381 _98518 _98519 _98520) (@lem7649398 _98518 _98519 _98520)). Qed.
Lemma lem7649400 (_98518 : int) (_98519 : int) (_98520 : int) : (term257 _98518 _98519 _98520) = (term284 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649380 _98518 _98519 _98520) (@lem7649399 _98518 _98519 _98520)). Qed.
Lemma lem7649403 (_98519 : int) : (term256 _98519) = (term256 _98519).
Proof. exact (eq_refl (term256 _98519)). Qed.
Lemma lem7649404 (_98518 : int) (_98519 : int) (_98520 : int) : (term258 _98518 _98519 _98520) = (term285 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649403 _98519) (@lem7649400 _98518 _98519 _98520)). Qed.
Lemma lem7649405 (_98518 : int) (_98519 : int) (_98520 : int) : (term285 _98518 _98519 _98520) = (term286 _98518 _98519 _98520).
Proof. exact (@lem19158 (term279 _98518 _98519 _98520) (term186 _98519) (term275 _98518 _98519 _98520)). Qed.
Lemma lem7649412 (_98518 : int) (_98519 : int) (_98520 : int) : (term287 _98518 _98519 _98520) = (term288 _98518 _98519 _98520).
Proof. exact (@lem19158 (term289 _98518 _98519 _98520) (term186 _98519) (term290 _98518 _98519 _98520)). Qed.
Lemma lem7649419 (_98518 : int) (_98519 : int) (_98520 : int) : (term291 _98518 _98519 _98520) = (term292 _98518 _98519 _98520).
Proof. exact (@lem19158 (term293 _98518 _98519 _98520) (term186 _98519) (term294 _98518 _98519 _98520)). Qed.
Lemma lem7649420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7649421 (_98518 : int) (_98519 : int) (_98520 : int) : (term295 _98518 _98519 _98520) = (term296 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649420) (@lem7649419 _98518 _98519 _98520)). Qed.
Lemma lem7649422 (_98518 : int) (_98519 : int) (_98520 : int) : (term286 _98518 _98519 _98520) = (term297 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649421 _98518 _98519 _98520) (@lem7649412 _98518 _98519 _98520)). Qed.
Lemma lem7649423 (_98518 : int) (_98519 : int) (_98520 : int) : (term285 _98518 _98519 _98520) = (term297 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649405 _98518 _98519 _98520) (@lem7649422 _98518 _98519 _98520)). Qed.
Lemma lem7649424 (_98518 : int) (_98519 : int) (_98520 : int) : (term258 _98518 _98519 _98520) = (term297 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649404 _98518 _98519 _98520) (@lem7649423 _98518 _98519 _98520)). Qed.
Lemma lem7649427 (_98518 : int) : (term256 _98518) = (term256 _98518).
Proof. exact (eq_refl (term256 _98518)). Qed.
Lemma lem7649428 (_98518 : int) (_98519 : int) (_98520 : int) : (term259 _98518 _98519 _98520) = (term298 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649427 _98518) (@lem7649424 _98518 _98519 _98520)). Qed.
Lemma lem7649429 (_98518 : int) (_98519 : int) (_98520 : int) : (term298 _98518 _98519 _98520) = (term299 _98518 _98519 _98520).
Proof. exact (@lem19158 (term292 _98518 _98519 _98520) (term186 _98518) (term288 _98518 _98519 _98520)). Qed.
Lemma lem7649436 (_98518 : int) (_98519 : int) (_98520 : int) : (term300 _98518 _98519 _98520) = (term301 _98518 _98519 _98520).
Proof. exact (@lem19158 (term302 _98518 _98519 _98520) (term186 _98518) (term303 _98518 _98519 _98520)). Qed.
Lemma lem7649443 (_98518 : int) (_98519 : int) (_98520 : int) : (term304 _98518 _98519 _98520) = (term305 _98518 _98519 _98520).
Proof. exact (@lem19158 (term306 _98518 _98519 _98520) (term186 _98518) (term307 _98518 _98519 _98520)). Qed.
Lemma lem7649444 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7649445 (_98518 : int) (_98519 : int) (_98520 : int) : (term308 _98518 _98519 _98520) = (term309 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649444) (@lem7649443 _98518 _98519 _98520)). Qed.
Lemma lem7649446 (_98518 : int) (_98519 : int) (_98520 : int) : (term299 _98518 _98519 _98520) = (term310 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649445 _98518 _98519 _98520) (@lem7649436 _98518 _98519 _98520)). Qed.
Lemma lem7649447 (_98518 : int) (_98519 : int) (_98520 : int) : (term298 _98518 _98519 _98520) = (term310 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649429 _98518 _98519 _98520) (@lem7649446 _98518 _98519 _98520)). Qed.
Lemma lem7649448 (_98518 : int) (_98519 : int) (_98520 : int) : (term259 _98518 _98519 _98520) = (term310 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649428 _98518 _98519 _98520) (@lem7649447 _98518 _98519 _98520)). Qed.
Lemma lem7649449 (_98518 : int) (_98519 : int) (_98520 : int) : (term158 _98520 _98518 _98519) = (term310 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649325 _98518 _98519 _98520) (@lem7649448 _98518 _98519 _98520)). Qed.
Lemma lem7649471 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term310 _98518 _98519 _98520) : term310 _98518 _98519 _98520.
Proof. exact (h1). Qed.
Lemma lem7649472 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term305 _98518 _98519 _98520) : term305 _98518 _98519 _98520.
Proof. exact (h1). Qed.
Lemma lem7649473 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term311 _98518 _98519 _98520.
Proof. exact (h1). Qed.
Lemma lem7649474 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term306 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7649473 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649476 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term293 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7649474 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649478 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term280 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7649476 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649480 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term263 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7649478 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649481 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : (term197 _98518 _98519 _98520) = term102.
Proof. exact (proj1 (@lem7649478 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649482 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term241 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7649480 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649485 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7649486 : term312 = term313.
Proof. exact (@lem7649485 term102 term116). Qed.
Lemma lem7649488 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7649489 : term116 = term205.
Proof. exact (@lem7649488 term117). Qed.
Lemma lem7649491 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7649492 : term102 = term163.
Proof. exact (@lem7649491 (NUMERAL 0)). Qed.
Lemma lem7649493 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7649494 : term314 = term315.
Proof. exact (MK_COMB (@lem7649493) (@lem7649492)). Qed.
Lemma lem7649495 : term313 = term316.
Proof. exact (MK_COMB (@lem7649494) (@lem7649489)). Qed.
Lemma lem7649496 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7649498 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7649499 : term313 = term319.
Proof. exact (@lem7649498 (NUMERAL 0) term117). Qed.
Lemma lem7649500 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7649501 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7649502 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7649501 h1) (fun h1 : term319 = True => @lem7649500)). Qed.
Lemma lem7649503 : term319 = True.
Proof. exact (EQ_MP (@lem7649502) (@lem7649500)). Qed.
Lemma lem7649504 : term313 = True.
Proof. exact (TRANS (@lem7649499) (@lem7649503)). Qed.
Lemma lem7649505 : True = term313.
Proof. exact (SYM (@lem7649504)). Qed.
Lemma lem7649506 : term313.
Proof. exact (EQ_MP (@lem7649505) (@lem0)). Qed.
Lemma lem7649507 : term321.
Proof. exact (@lem7649496 (@lem7649506)). Qed.
Lemma lem7649509 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7649510 : term313 = term319.
Proof. exact (@lem7649509 (NUMERAL 0) term117). Qed.
Lemma lem7649511 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7649512 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7649513 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7649512 h1) (fun h1 : term319 = True => @lem7649511)). Qed.
Lemma lem7649514 : term319 = True.
Proof. exact (EQ_MP (@lem7649513) (@lem7649511)). Qed.
Lemma lem7649515 : term313 = True.
Proof. exact (TRANS (@lem7649510) (@lem7649514)). Qed.
Lemma lem7649516 : True = term313.
Proof. exact (SYM (@lem7649515)). Qed.
Lemma lem7649517 : term313.
Proof. exact (EQ_MP (@lem7649516) (@lem0)). Qed.
Lemma lem7649518 : term316 = term322.
Proof. exact (@lem7649507 (@lem7649517)). Qed.
Lemma lem7649520 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649521 : term175 = term176.
Proof. exact (@lem7649520 term117 term117). Qed.
Lemma lem7649522 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649523 : term178 = term117.
Proof. exact (EQ_MP (@lem7649522) (@lem940073)). Qed.
Lemma lem7649524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649525 : term176 = term116.
Proof. exact (MK_COMB (@lem7649524) (@lem7649523)). Qed.
Lemma lem7649526 : term175 = term116.
Proof. exact (TRANS (@lem7649521) (@lem7649525)). Qed.
Lemma lem7649528 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7649529 : term324 = term102.
Proof. exact (@lem7649528 term117). Qed.
Lemma lem7649530 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7649531 : term325 = term314.
Proof. exact (MK_COMB (@lem7649530) (@lem7649529)). Qed.
Lemma lem7649532 : term322 = term313.
Proof. exact (MK_COMB (@lem7649531) (@lem7649526)). Qed.
Lemma lem7649534 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7649535 : term313 = term319.
Proof. exact (@lem7649534 (NUMERAL 0) term117). Qed.
Lemma lem7649536 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7649537 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7649538 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7649537 h1) (fun h1 : term319 = True => @lem7649536)). Qed.
Lemma lem7649539 : term319 = True.
Proof. exact (EQ_MP (@lem7649538) (@lem7649536)). Qed.
Lemma lem7649540 : term313 = True.
Proof. exact (TRANS (@lem7649535) (@lem7649539)). Qed.
Lemma lem7649541 : term322 = True.
Proof. exact (TRANS (@lem7649532) (@lem7649540)). Qed.
Lemma lem7649542 : term316 = True.
Proof. exact (TRANS (@lem7649518) (@lem7649541)). Qed.
Lemma lem7649543 : term313 = True.
Proof. exact (TRANS (@lem7649495) (@lem7649542)). Qed.
Lemma lem7649544 : term312 = True.
Proof. exact (TRANS (@lem7649486) (@lem7649543)). Qed.
Lemma lem7649545 : True = term312.
Proof. exact (SYM (@lem7649544)). Qed.
Lemma lem7649546 : term312.
Proof. exact (EQ_MP (@lem7649545) (@lem0)). Qed.
Lemma lem7649547 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term326 _98518 _98519 _98520.
Proof. exact (conj (@lem7649546) (@lem7649482 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649549 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7649550 (_98518 : int) (_98519 : int) (_98520 : int) : term328 _98518 _98519 _98520.
Proof. exact (@lem7649549 term116 (term238 _98518 _98519 _98520)). Qed.
Lemma lem7649551 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term329 _98518 _98519 _98520.
Proof. exact (@lem7649550 _98518 _98519 _98520 (@lem7649547 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649552 (_98518 : int) (_98519 : int) (_98520 : int) : (term330 _98518 _98519 _98520) = (term238 _98518 _98519 _98520).
Proof. exact (@lem1982733 (term238 _98518 _98519 _98520)). Qed.
Lemma lem7649553 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7649554 (_98518 : int) (_98519 : int) (_98520 : int) : (term331 _98518 _98519 _98520) = (term240 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649553) (@lem7649552 _98518 _98519 _98520)). Qed.
Lemma lem7649555 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7649556 (_98518 : int) (_98519 : int) (_98520 : int) : (term329 _98518 _98519 _98520) = (term241 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649554 _98518 _98519 _98520) (@lem7649555)). Qed.
Lemma lem7649557 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term241 _98518 _98519 _98520.
Proof. exact (EQ_MP (@lem7649556 _98518 _98519 _98520) (@lem7649551 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649559 (y : real) : term332 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7649560 (_98518 : int) (_98519 : int) (_98520 : int) : term333 _98518 _98519 _98520.
Proof. exact (@lem7649559 (term197 _98518 _98519 _98520)). Qed.
Lemma lem7649561 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term334 _98518 _98519 _98520.
Proof. exact (@lem7649560 _98518 _98519 _98520 (@lem7649481 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649562 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term335 _98518 _98519 _98520.
Proof. exact (@lem7649561 _98518 _98519 _98520 h1 term166). Qed.
Lemma lem7649563 (_98518 : int) (_98519 : int) (_98520 : int) : (term335 _98518 _98519 _98520) = ((term336 _98518 _98519 _98520) = term102).
Proof. exact (eq_refl (term335 _98518 _98519 _98520)). Qed.
Lemma lem7649564 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : (term336 _98518 _98519 _98520) = term102.
Proof. exact (EQ_MP (@lem7649563 _98518 _98519 _98520) (@lem7649562 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649565 (_98518 : int) (_98519 : int) (_98520 : int) : (term336 _98518 _98519 _98520) = (term337 _98518 _98519 _98520).
Proof. exact (@lem1982781 (term193 _98518) term166 (term195 _98519 _98520)). Qed.
Lemma lem7649566 (_98519 : int) (_98520 : int) : (term338 _98519 _98520) = (term339 _98519 _98520).
Proof. exact (@lem1982781 (term193 _98519) term166 (real_of_int _98520)). Qed.
Lemma lem7649567 (_98520 : int) : (term193 _98520) = (term193 _98520).
Proof. exact (eq_refl (term193 _98520)). Qed.
Lemma lem7649568 (_98519 : int) : (term340 _98519) = (term341 _98519).
Proof. exact (@lem1982749 term166 term166 (real_of_int _98519)). Qed.
Lemma lem7649570 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7649571 : term166 = term167.
Proof. exact (@lem7649570 term117). Qed.
Lemma lem7649573 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7649574 : term166 = term167.
Proof. exact (@lem7649573 term117). Qed.
Lemma lem7649575 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649576 : term168 = term169.
Proof. exact (MK_COMB (@lem7649575) (@lem7649574)). Qed.
Lemma lem7649577 : term342 = term343.
Proof. exact (MK_COMB (@lem7649576) (@lem7649571)). Qed.
Lemma lem7649578 : term343 = term344.
Proof. exact (@lem1981613 term166 term166 term116 term116). Qed.
Lemma lem7649580 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649581 : term175 = term176.
Proof. exact (@lem7649580 term117 term117). Qed.
Lemma lem7649582 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649583 : term178 = term117.
Proof. exact (EQ_MP (@lem7649582) (@lem940073)). Qed.
Lemma lem7649584 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649585 : term176 = term116.
Proof. exact (MK_COMB (@lem7649584) (@lem7649583)). Qed.
Lemma lem7649586 : term175 = term116.
Proof. exact (TRANS (@lem7649581) (@lem7649585)). Qed.
Lemma lem7649588 (m : nat) (n : nat) : (term345 m n) = (term174 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7649589 : term342 = term176.
Proof. exact (@lem7649588 term117 term117). Qed.
Lemma lem7649590 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649591 : term178 = term117.
Proof. exact (EQ_MP (@lem7649590) (@lem940073)). Qed.
Lemma lem7649592 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649593 : term176 = term116.
Proof. exact (MK_COMB (@lem7649592) (@lem7649591)). Qed.
Lemma lem7649594 : term342 = term116.
Proof. exact (TRANS (@lem7649589) (@lem7649593)). Qed.
Lemma lem7649595 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7649596 : term346 = term347.
Proof. exact (MK_COMB (@lem7649595) (@lem7649594)). Qed.
Lemma lem7649597 : term344 = term205.
Proof. exact (MK_COMB (@lem7649596) (@lem7649586)). Qed.
Lemma lem7649598 : term343 = term205.
Proof. exact (TRANS (@lem7649578) (@lem7649597)). Qed.
Lemma lem7649599 : term342 = term205.
Proof. exact (TRANS (@lem7649577) (@lem7649598)). Qed.
Lemma lem7649601 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7649602 : term205 = term116.
Proof. exact (@lem7649601 term116). Qed.
Lemma lem7649603 : term342 = term116.
Proof. exact (TRANS (@lem7649599) (@lem7649602)). Qed.
Lemma lem7649604 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649605 : term348 = term349.
Proof. exact (MK_COMB (@lem7649604) (@lem7649603)). Qed.
Lemma lem7649606 (_98519 : int) : (real_of_int _98519) = (real_of_int _98519).
Proof. exact (eq_refl (real_of_int _98519)). Qed.
Lemma lem7649607 (_98519 : int) : (term341 _98519) = (term350 _98519).
Proof. exact (MK_COMB (@lem7649605) (@lem7649606 _98519)). Qed.
Lemma lem7649608 (_98519 : int) : (term340 _98519) = (term350 _98519).
Proof. exact (TRANS (@lem7649568 _98519) (@lem7649607 _98519)). Qed.
Lemma lem7649609 (_98519 : int) : (term350 _98519) = (real_of_int _98519).
Proof. exact (@lem1982709 (real_of_int _98519)). Qed.
Lemma lem7649610 (_98519 : int) : (term340 _98519) = (real_of_int _98519).
Proof. exact (TRANS (@lem7649608 _98519) (@lem7649609 _98519)). Qed.
Lemma lem7649611 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7649612 (_98519 : int) : (term351 _98519) = (term118 _98519).
Proof. exact (MK_COMB (@lem7649611) (@lem7649610 _98519)). Qed.
Lemma lem7649613 (_98519 : int) (_98520 : int) : (term339 _98519 _98520) = (term194 _98519 _98520).
Proof. exact (MK_COMB (@lem7649612 _98519) (@lem7649567 _98520)). Qed.
Lemma lem7649614 (_98519 : int) (_98520 : int) : (term338 _98519 _98520) = (term194 _98519 _98520).
Proof. exact (TRANS (@lem7649566 _98519 _98520) (@lem7649613 _98519 _98520)). Qed.
Lemma lem7649615 (_98518 : int) : (term340 _98518) = (term341 _98518).
Proof. exact (@lem1982749 term166 term166 (real_of_int _98518)). Qed.
Lemma lem7649617 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7649618 : term166 = term167.
Proof. exact (@lem7649617 term117). Qed.
Lemma lem7649620 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7649621 : term166 = term167.
Proof. exact (@lem7649620 term117). Qed.
Lemma lem7649622 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649623 : term168 = term169.
Proof. exact (MK_COMB (@lem7649622) (@lem7649621)). Qed.
Lemma lem7649624 : term342 = term343.
Proof. exact (MK_COMB (@lem7649623) (@lem7649618)). Qed.
Lemma lem7649625 : term343 = term344.
Proof. exact (@lem1981613 term166 term166 term116 term116). Qed.
Lemma lem7649627 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649628 : term175 = term176.
Proof. exact (@lem7649627 term117 term117). Qed.
Lemma lem7649629 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649630 : term178 = term117.
Proof. exact (EQ_MP (@lem7649629) (@lem940073)). Qed.
Lemma lem7649631 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649632 : term176 = term116.
Proof. exact (MK_COMB (@lem7649631) (@lem7649630)). Qed.
Lemma lem7649633 : term175 = term116.
Proof. exact (TRANS (@lem7649628) (@lem7649632)). Qed.
Lemma lem7649635 (m : nat) (n : nat) : (term345 m n) = (term174 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7649636 : term342 = term176.
Proof. exact (@lem7649635 term117 term117). Qed.
Lemma lem7649637 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649638 : term178 = term117.
Proof. exact (EQ_MP (@lem7649637) (@lem940073)). Qed.
Lemma lem7649639 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649640 : term176 = term116.
Proof. exact (MK_COMB (@lem7649639) (@lem7649638)). Qed.
Lemma lem7649641 : term342 = term116.
Proof. exact (TRANS (@lem7649636) (@lem7649640)). Qed.
Lemma lem7649642 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7649643 : term346 = term347.
Proof. exact (MK_COMB (@lem7649642) (@lem7649641)). Qed.
Lemma lem7649644 : term344 = term205.
Proof. exact (MK_COMB (@lem7649643) (@lem7649633)). Qed.
Lemma lem7649645 : term343 = term205.
Proof. exact (TRANS (@lem7649625) (@lem7649644)). Qed.
Lemma lem7649646 : term342 = term205.
Proof. exact (TRANS (@lem7649624) (@lem7649645)). Qed.
Lemma lem7649648 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7649649 : term205 = term116.
Proof. exact (@lem7649648 term116). Qed.
Lemma lem7649650 : term342 = term116.
Proof. exact (TRANS (@lem7649646) (@lem7649649)). Qed.
Lemma lem7649651 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649652 : term348 = term349.
Proof. exact (MK_COMB (@lem7649651) (@lem7649650)). Qed.
Lemma lem7649653 (_98518 : int) : (real_of_int _98518) = (real_of_int _98518).
Proof. exact (eq_refl (real_of_int _98518)). Qed.
Lemma lem7649654 (_98518 : int) : (term341 _98518) = (term350 _98518).
Proof. exact (MK_COMB (@lem7649652) (@lem7649653 _98518)). Qed.
Lemma lem7649655 (_98518 : int) : (term340 _98518) = (term350 _98518).
Proof. exact (TRANS (@lem7649615 _98518) (@lem7649654 _98518)). Qed.
Lemma lem7649656 (_98518 : int) : (term350 _98518) = (real_of_int _98518).
Proof. exact (@lem1982709 (real_of_int _98518)). Qed.
Lemma lem7649657 (_98518 : int) : (term340 _98518) = (real_of_int _98518).
Proof. exact (TRANS (@lem7649655 _98518) (@lem7649656 _98518)). Qed.
Lemma lem7649658 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7649659 (_98518 : int) : (term351 _98518) = (term118 _98518).
Proof. exact (MK_COMB (@lem7649658) (@lem7649657 _98518)). Qed.
Lemma lem7649660 (_98518 : int) (_98519 : int) (_98520 : int) : (term337 _98518 _98519 _98520) = (term352 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649659 _98518) (@lem7649614 _98519 _98520)). Qed.
Lemma lem7649661 (_98518 : int) (_98519 : int) (_98520 : int) : (term336 _98518 _98519 _98520) = (term352 _98518 _98519 _98520).
Proof. exact (TRANS (@lem7649565 _98518 _98519 _98520) (@lem7649660 _98518 _98519 _98520)). Qed.
Lemma lem7649662 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7649663 (_98518 : int) (_98519 : int) (_98520 : int) : (term353 _98518 _98519 _98520) = (term354 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7649662) (@lem7649661 _98518 _98519 _98520)). Qed.
Lemma lem7649664 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7649665 (_98518 : int) (_98519 : int) (_98520 : int) : ((term336 _98518 _98519 _98520) = term102) = ((term352 _98518 _98519 _98520) = term102).
Proof. exact (MK_COMB (@lem7649663 _98518 _98519 _98520) (@lem7649664)). Qed.
Lemma lem7649666 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : (term352 _98518 _98519 _98520) = term102.
Proof. exact (EQ_MP (@lem7649665 _98518 _98519 _98520) (@lem7649564 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649667 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term355 _98518 _98519 _98520.
Proof. exact (conj (@lem7649666 _98518 _98519 _98520 h1) (@lem7649557 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649669 (x : real) (y : real) : term356 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem7649670 (_98518 : int) (_98519 : int) (_98520 : int) : term357 _98518 _98519 _98520.
Proof. exact (@lem7649669 (term352 _98518 _98519 _98520) (term238 _98518 _98519 _98520)). Qed.
Lemma lem7649671 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term358 _98518 _98519 _98520.
Proof. exact (@lem7649670 _98518 _98519 _98520 (@lem7649667 _98518 _98519 _98520 h1)). Qed.
Lemma lem7649672 (_98518 : int) (_98519 : int) (_98520 : int) : (term359 _98518 _98519 _98520) = (term360 _98518 _98519 _98520).
Proof. exact (@lem1982753 (real_of_int _98518) (term193 _98518) (term194 _98519 _98520) (term224 _98519 _98520)). Qed.
Lemma lem7649673 (_98518 : int) : (term361 _98518) = (term362 _98518).
Proof. exact (@lem1982715 term166 (real_of_int _98518)). Qed.
Lemma lem7649675 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7649676 : term116 = term205.
Proof. exact (@lem7649675 term117). Qed.
Lemma lem7649678 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7649679 : term166 = term167.
Proof. exact (@lem7649678 term117). Qed.
Lemma lem7649680 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7649681 : term363 = term364.
Proof. exact (MK_COMB (@lem7649680) (@lem7649679)). Qed.
Lemma lem7649682 : term365 = term366.
Proof. exact (MK_COMB (@lem7649681) (@lem7649676)). Qed.
Lemma lem7649683 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7649685 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7649686 : term313 = term319.
Proof. exact (@lem7649685 (NUMERAL 0) term117). Qed.
Lemma lem7649687 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7649688 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7649689 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7649688 h1) (fun h1 : term319 = True => @lem7649687)). Qed.
Lemma lem7649690 : term319 = True.
Proof. exact (EQ_MP (@lem7649689) (@lem7649687)). Qed.
Lemma lem7649691 : term313 = True.
Proof. exact (TRANS (@lem7649686) (@lem7649690)). Qed.
Lemma lem7649692 : True = term313.
Proof. exact (SYM (@lem7649691)). Qed.
Lemma lem7649693 : term313.
Proof. exact (EQ_MP (@lem7649692) (@lem0)). Qed.
Lemma lem7649694 : term368.
Proof. exact (@lem7649683 (@lem7649693)). Qed.
Lemma lem7649696 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7649697 : term313 = term319.
Proof. exact (@lem7649696 (NUMERAL 0) term117). Qed.
Lemma lem7649698 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7649699 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7649700 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7649699 h1) (fun h1 : term319 = True => @lem7649698)). Qed.
Lemma lem7649701 : term319 = True.
Proof. exact (EQ_MP (@lem7649700) (@lem7649698)). Qed.
Lemma lem7649702 : term313 = True.
Proof. exact (TRANS (@lem7649697) (@lem7649701)). Qed.
Lemma lem7649703 : True = term313.
Proof. exact (SYM (@lem7649702)). Qed.
Lemma lem7649704 : term313.
Proof. exact (EQ_MP (@lem7649703) (@lem0)). Qed.
Lemma lem7649705 : term369.
Proof. exact (@lem7649694 (@lem7649704)). Qed.
Lemma lem7649707 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7649708 : term313 = term319.
Proof. exact (@lem7649707 (NUMERAL 0) term117). Qed.
Lemma lem7649709 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7649710 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7649711 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7649710 h1) (fun h1 : term319 = True => @lem7649709)). Qed.
Lemma lem7649712 : term319 = True.
Proof. exact (EQ_MP (@lem7649711) (@lem7649709)). Qed.
Lemma lem7649713 : term313 = True.
Proof. exact (TRANS (@lem7649708) (@lem7649712)). Qed.
Lemma lem7649714 : True = term313.
Proof. exact (SYM (@lem7649713)). Qed.
Lemma lem7649715 : term313.
Proof. exact (EQ_MP (@lem7649714) (@lem0)). Qed.
Lemma lem7649716 : term370.
Proof. exact (@lem7649705 (@lem7649715)). Qed.
Lemma lem7649718 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649719 : term175 = term176.
Proof. exact (@lem7649718 term117 term117). Qed.
Lemma lem7649720 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649721 : term178 = term117.
Proof. exact (EQ_MP (@lem7649720) (@lem940073)). Qed.
Lemma lem7649722 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649723 : term176 = term116.
Proof. exact (MK_COMB (@lem7649722) (@lem7649721)). Qed.
Lemma lem7649724 : term175 = term116.
Proof. exact (TRANS (@lem7649719) (@lem7649723)). Qed.
Lemma lem7649726 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7649727 : term206 = term211.
Proof. exact (@lem7649726 term117 term117). Qed.
Lemma lem7649728 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649729 : term178 = term117.
Proof. exact (EQ_MP (@lem7649728) (@lem940073)). Qed.
Lemma lem7649730 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649731 : term176 = term116.
Proof. exact (MK_COMB (@lem7649730) (@lem7649729)). Qed.
Lemma lem7649732 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7649733 : term211 = term166.
Proof. exact (MK_COMB (@lem7649732) (@lem7649731)). Qed.
Lemma lem7649734 : term206 = term166.
Proof. exact (TRANS (@lem7649727) (@lem7649733)). Qed.
Lemma lem7649735 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7649736 : term371 = term363.
Proof. exact (MK_COMB (@lem7649735) (@lem7649734)). Qed.
Lemma lem7649737 : term372 = term365.
Proof. exact (MK_COMB (@lem7649736) (@lem7649724)). Qed.
Lemma lem7649739 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7649740 : term365 = term102.
Proof. exact (@lem7649739 term117). Qed.
Lemma lem7649741 : term372 = term102.
Proof. exact (TRANS (@lem7649737) (@lem7649740)). Qed.
Lemma lem7649742 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649743 : term374 = term375.
Proof. exact (MK_COMB (@lem7649742) (@lem7649741)). Qed.
Lemma lem7649744 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7649745 : term376 = term324.
Proof. exact (MK_COMB (@lem7649743) (@lem7649744)). Qed.
Lemma lem7649747 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7649748 : term324 = term102.
Proof. exact (@lem7649747 term117). Qed.
Lemma lem7649749 : term376 = term102.
Proof. exact (TRANS (@lem7649745) (@lem7649748)). Qed.
Lemma lem7649751 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649752 : term175 = term176.
Proof. exact (@lem7649751 term117 term117). Qed.
Lemma lem7649753 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649754 : term178 = term117.
Proof. exact (EQ_MP (@lem7649753) (@lem940073)). Qed.
Lemma lem7649755 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649756 : term176 = term116.
Proof. exact (MK_COMB (@lem7649755) (@lem7649754)). Qed.
Lemma lem7649757 : term175 = term116.
Proof. exact (TRANS (@lem7649752) (@lem7649756)). Qed.
Lemma lem7649758 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7649759 : term377 = term324.
Proof. exact (MK_COMB (@lem7649758) (@lem7649757)). Qed.
Lemma lem7649761 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7649762 : term324 = term102.
Proof. exact (@lem7649761 term117). Qed.
Lemma lem7649763 : term377 = term102.
Proof. exact (TRANS (@lem7649759) (@lem7649762)). Qed.
Lemma lem7649764 : term102 = term377.
Proof. exact (SYM (@lem7649763)). Qed.
Lemma lem7649765 : term376 = term377.
Proof. exact (TRANS (@lem7649749) (@lem7649764)). Qed.
Lemma lem7649766 : term366 = term163.
Proof. exact (@lem7649716 (@lem7649765)). Qed.
Lemma lem7649767 : term365 = term163.
Proof. exact (TRANS (@lem7649682) (@lem7649766)). Qed.
Lemma lem7649769 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7649770 : term163 = term102.
Proof. exact (@lem7649769 term102). Qed.
Lemma lem7649771 : term365 = term102.
Proof. exact (TRANS (@lem7649767) (@lem7649770)). Qed.
Lemma lem7649772 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649773 : term378 = term375.
Proof. exact (MK_COMB (@lem7649772) (@lem7649771)). Qed.
Lemma lem7649774 (_98518 : int) : (real_of_int _98518) = (real_of_int _98518).
Proof. exact (eq_refl (real_of_int _98518)). Qed.
Lemma lem7649775 (_98518 : int) : (term362 _98518) = (term379 _98518).
Proof. exact (MK_COMB (@lem7649773) (@lem7649774 _98518)). Qed.
Lemma lem7649776 (_98518 : int) : (term361 _98518) = (term379 _98518).
Proof. exact (TRANS (@lem7649673 _98518) (@lem7649775 _98518)). Qed.
Lemma lem7649777 (_98518 : int) : (term379 _98518) = term102.
Proof. exact (@lem1982719 (real_of_int _98518)). Qed.
Lemma lem7649778 (_98518 : int) : (term361 _98518) = term102.
Proof. exact (TRANS (@lem7649776 _98518) (@lem7649777 _98518)). Qed.
Lemma lem7649779 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7649780 (_98518 : int) : (term380 _98518) = term381.
Proof. exact (MK_COMB (@lem7649779) (@lem7649778 _98518)). Qed.
Lemma lem7649781 (_98519 : int) (_98520 : int) : (term382 _98519 _98520) = (term383 _98519 _98520).
Proof. exact (@lem1982753 (real_of_int _98519) (term193 _98519) (term193 _98520) (term384 _98520)). Qed.
Lemma lem7649782 (_98519 : int) : (term361 _98519) = (term362 _98519).
Proof. exact (@lem1982715 term166 (real_of_int _98519)). Qed.
Lemma lem7649784 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7649785 : term116 = term205.
Proof. exact (@lem7649784 term117). Qed.
Lemma lem7649787 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7649788 : term166 = term167.
Proof. exact (@lem7649787 term117). Qed.
Lemma lem7649789 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7649790 : term363 = term364.
Proof. exact (MK_COMB (@lem7649789) (@lem7649788)). Qed.
Lemma lem7649791 : term365 = term366.
Proof. exact (MK_COMB (@lem7649790) (@lem7649785)). Qed.
Lemma lem7649792 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7649794 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7649795 : term313 = term319.
Proof. exact (@lem7649794 (NUMERAL 0) term117). Qed.
Lemma lem7649796 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7649797 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7649798 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7649797 h1) (fun h1 : term319 = True => @lem7649796)). Qed.
Lemma lem7649799 : term319 = True.
Proof. exact (EQ_MP (@lem7649798) (@lem7649796)). Qed.
Lemma lem7649800 : term313 = True.
Proof. exact (TRANS (@lem7649795) (@lem7649799)). Qed.
Lemma lem7649801 : True = term313.
Proof. exact (SYM (@lem7649800)). Qed.
Lemma lem7649802 : term313.
Proof. exact (EQ_MP (@lem7649801) (@lem0)). Qed.
Lemma lem7649803 : term368.
Proof. exact (@lem7649792 (@lem7649802)). Qed.
Lemma lem7649805 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7649806 : term313 = term319.
Proof. exact (@lem7649805 (NUMERAL 0) term117). Qed.
Lemma lem7649807 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7649808 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7649809 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7649808 h1) (fun h1 : term319 = True => @lem7649807)). Qed.
Lemma lem7649810 : term319 = True.
Proof. exact (EQ_MP (@lem7649809) (@lem7649807)). Qed.
Lemma lem7649811 : term313 = True.
Proof. exact (TRANS (@lem7649806) (@lem7649810)). Qed.
Lemma lem7649812 : True = term313.
Proof. exact (SYM (@lem7649811)). Qed.
Lemma lem7649813 : term313.
Proof. exact (EQ_MP (@lem7649812) (@lem0)). Qed.
Lemma lem7649814 : term369.
Proof. exact (@lem7649803 (@lem7649813)). Qed.
Lemma lem7649816 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7649817 : term313 = term319.
Proof. exact (@lem7649816 (NUMERAL 0) term117). Qed.
Lemma lem7649818 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7649819 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7649820 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7649819 h1) (fun h1 : term319 = True => @lem7649818)). Qed.
Lemma lem7649821 : term319 = True.
Proof. exact (EQ_MP (@lem7649820) (@lem7649818)). Qed.
Lemma lem7649822 : term313 = True.
Proof. exact (TRANS (@lem7649817) (@lem7649821)). Qed.
Lemma lem7649823 : True = term313.
Proof. exact (SYM (@lem7649822)). Qed.
Lemma lem7649824 : term313.
Proof. exact (EQ_MP (@lem7649823) (@lem0)). Qed.
Lemma lem7649825 : term370.
Proof. exact (@lem7649814 (@lem7649824)). Qed.
Lemma lem7649827 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649828 : term175 = term176.
Proof. exact (@lem7649827 term117 term117). Qed.
Lemma lem7649829 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649830 : term178 = term117.
Proof. exact (EQ_MP (@lem7649829) (@lem940073)). Qed.
Lemma lem7649831 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649832 : term176 = term116.
Proof. exact (MK_COMB (@lem7649831) (@lem7649830)). Qed.
Lemma lem7649833 : term175 = term116.
Proof. exact (TRANS (@lem7649828) (@lem7649832)). Qed.
Lemma lem7649835 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7649836 : term206 = term211.
Proof. exact (@lem7649835 term117 term117). Qed.
Lemma lem7649837 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649838 : term178 = term117.
Proof. exact (EQ_MP (@lem7649837) (@lem940073)). Qed.
Lemma lem7649839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649840 : term176 = term116.
Proof. exact (MK_COMB (@lem7649839) (@lem7649838)). Qed.
Lemma lem7649841 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7649842 : term211 = term166.
Proof. exact (MK_COMB (@lem7649841) (@lem7649840)). Qed.
Lemma lem7649843 : term206 = term166.
Proof. exact (TRANS (@lem7649836) (@lem7649842)). Qed.
Lemma lem7649844 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7649845 : term371 = term363.
Proof. exact (MK_COMB (@lem7649844) (@lem7649843)). Qed.
Lemma lem7649846 : term372 = term365.
Proof. exact (MK_COMB (@lem7649845) (@lem7649833)). Qed.
Lemma lem7649848 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7649849 : term365 = term102.
Proof. exact (@lem7649848 term117). Qed.
Lemma lem7649850 : term372 = term102.
Proof. exact (TRANS (@lem7649846) (@lem7649849)). Qed.
Lemma lem7649851 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649852 : term374 = term375.
Proof. exact (MK_COMB (@lem7649851) (@lem7649850)). Qed.
Lemma lem7649853 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7649854 : term376 = term324.
Proof. exact (MK_COMB (@lem7649852) (@lem7649853)). Qed.
Lemma lem7649856 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7649857 : term324 = term102.
Proof. exact (@lem7649856 term117). Qed.
Lemma lem7649858 : term376 = term102.
Proof. exact (TRANS (@lem7649854) (@lem7649857)). Qed.
Lemma lem7649860 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649861 : term175 = term176.
Proof. exact (@lem7649860 term117 term117). Qed.
Lemma lem7649862 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649863 : term178 = term117.
Proof. exact (EQ_MP (@lem7649862) (@lem940073)). Qed.
Lemma lem7649864 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649865 : term176 = term116.
Proof. exact (MK_COMB (@lem7649864) (@lem7649863)). Qed.
Lemma lem7649866 : term175 = term116.
Proof. exact (TRANS (@lem7649861) (@lem7649865)). Qed.
Lemma lem7649867 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7649868 : term377 = term324.
Proof. exact (MK_COMB (@lem7649867) (@lem7649866)). Qed.
Lemma lem7649870 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7649871 : term324 = term102.
Proof. exact (@lem7649870 term117). Qed.
Lemma lem7649872 : term377 = term102.
Proof. exact (TRANS (@lem7649868) (@lem7649871)). Qed.
Lemma lem7649873 : term102 = term377.
Proof. exact (SYM (@lem7649872)). Qed.
Lemma lem7649874 : term376 = term377.
Proof. exact (TRANS (@lem7649858) (@lem7649873)). Qed.
Lemma lem7649875 : term366 = term163.
Proof. exact (@lem7649825 (@lem7649874)). Qed.
Lemma lem7649876 : term365 = term163.
Proof. exact (TRANS (@lem7649791) (@lem7649875)). Qed.
Lemma lem7649878 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7649879 : term163 = term102.
Proof. exact (@lem7649878 term102). Qed.
Lemma lem7649880 : term365 = term102.
Proof. exact (TRANS (@lem7649876) (@lem7649879)). Qed.
Lemma lem7649881 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649882 : term378 = term375.
Proof. exact (MK_COMB (@lem7649881) (@lem7649880)). Qed.
Lemma lem7649883 (_98519 : int) : (real_of_int _98519) = (real_of_int _98519).
Proof. exact (eq_refl (real_of_int _98519)). Qed.
Lemma lem7649884 (_98519 : int) : (term362 _98519) = (term379 _98519).
Proof. exact (MK_COMB (@lem7649882) (@lem7649883 _98519)). Qed.
Lemma lem7649885 (_98519 : int) : (term361 _98519) = (term379 _98519).
Proof. exact (TRANS (@lem7649782 _98519) (@lem7649884 _98519)). Qed.
Lemma lem7649886 (_98519 : int) : (term379 _98519) = term102.
Proof. exact (@lem1982719 (real_of_int _98519)). Qed.
Lemma lem7649887 (_98519 : int) : (term361 _98519) = term102.
Proof. exact (TRANS (@lem7649885 _98519) (@lem7649886 _98519)). Qed.
Lemma lem7649888 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7649889 (_98519 : int) : (term380 _98519) = term381.
Proof. exact (MK_COMB (@lem7649888) (@lem7649887 _98519)). Qed.
Lemma lem7649890 (_98520 : int) : (term385 _98520) = (term386 _98520).
Proof. exact (@lem1982763 (term193 _98520) (real_of_int _98520) term166). Qed.
Lemma lem7649891 (_98520 : int) : (term387 _98520) = (term362 _98520).
Proof. exact (@lem1982713 term166 (real_of_int _98520)). Qed.
Lemma lem7649893 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7649894 : term116 = term205.
Proof. exact (@lem7649893 term117). Qed.
Lemma lem7649896 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7649897 : term166 = term167.
Proof. exact (@lem7649896 term117). Qed.
Lemma lem7649898 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7649899 : term363 = term364.
Proof. exact (MK_COMB (@lem7649898) (@lem7649897)). Qed.
Lemma lem7649900 : term365 = term366.
Proof. exact (MK_COMB (@lem7649899) (@lem7649894)). Qed.
Lemma lem7649901 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7649903 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7649904 : term313 = term319.
Proof. exact (@lem7649903 (NUMERAL 0) term117). Qed.
Lemma lem7649905 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7649906 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7649907 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7649906 h1) (fun h1 : term319 = True => @lem7649905)). Qed.
Lemma lem7649908 : term319 = True.
Proof. exact (EQ_MP (@lem7649907) (@lem7649905)). Qed.
Lemma lem7649909 : term313 = True.
Proof. exact (TRANS (@lem7649904) (@lem7649908)). Qed.
Lemma lem7649910 : True = term313.
Proof. exact (SYM (@lem7649909)). Qed.
Lemma lem7649911 : term313.
Proof. exact (EQ_MP (@lem7649910) (@lem0)). Qed.
Lemma lem7649912 : term368.
Proof. exact (@lem7649901 (@lem7649911)). Qed.
Lemma lem7649914 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7649915 : term313 = term319.
Proof. exact (@lem7649914 (NUMERAL 0) term117). Qed.
Lemma lem7649916 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7649917 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7649918 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7649917 h1) (fun h1 : term319 = True => @lem7649916)). Qed.
Lemma lem7649919 : term319 = True.
Proof. exact (EQ_MP (@lem7649918) (@lem7649916)). Qed.
Lemma lem7649920 : term313 = True.
Proof. exact (TRANS (@lem7649915) (@lem7649919)). Qed.
Lemma lem7649921 : True = term313.
Proof. exact (SYM (@lem7649920)). Qed.
Lemma lem7649922 : term313.
Proof. exact (EQ_MP (@lem7649921) (@lem0)). Qed.
Lemma lem7649923 : term369.
Proof. exact (@lem7649912 (@lem7649922)). Qed.
Lemma lem7649925 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7649926 : term313 = term319.
Proof. exact (@lem7649925 (NUMERAL 0) term117). Qed.
Lemma lem7649927 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7649928 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7649929 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7649928 h1) (fun h1 : term319 = True => @lem7649927)). Qed.
Lemma lem7649930 : term319 = True.
Proof. exact (EQ_MP (@lem7649929) (@lem7649927)). Qed.
Lemma lem7649931 : term313 = True.
Proof. exact (TRANS (@lem7649926) (@lem7649930)). Qed.
Lemma lem7649932 : True = term313.
Proof. exact (SYM (@lem7649931)). Qed.
Lemma lem7649933 : term313.
Proof. exact (EQ_MP (@lem7649932) (@lem0)). Qed.
Lemma lem7649934 : term370.
Proof. exact (@lem7649923 (@lem7649933)). Qed.
Lemma lem7649936 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649937 : term175 = term176.
Proof. exact (@lem7649936 term117 term117). Qed.
Lemma lem7649938 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649939 : term178 = term117.
Proof. exact (EQ_MP (@lem7649938) (@lem940073)). Qed.
Lemma lem7649940 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649941 : term176 = term116.
Proof. exact (MK_COMB (@lem7649940) (@lem7649939)). Qed.
Lemma lem7649942 : term175 = term116.
Proof. exact (TRANS (@lem7649937) (@lem7649941)). Qed.
Lemma lem7649944 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7649945 : term206 = term211.
Proof. exact (@lem7649944 term117 term117). Qed.
Lemma lem7649946 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649947 : term178 = term117.
Proof. exact (EQ_MP (@lem7649946) (@lem940073)). Qed.
Lemma lem7649948 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649949 : term176 = term116.
Proof. exact (MK_COMB (@lem7649948) (@lem7649947)). Qed.
Lemma lem7649950 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7649951 : term211 = term166.
Proof. exact (MK_COMB (@lem7649950) (@lem7649949)). Qed.
Lemma lem7649952 : term206 = term166.
Proof. exact (TRANS (@lem7649945) (@lem7649951)). Qed.
Lemma lem7649953 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7649954 : term371 = term363.
Proof. exact (MK_COMB (@lem7649953) (@lem7649952)). Qed.
Lemma lem7649955 : term372 = term365.
Proof. exact (MK_COMB (@lem7649954) (@lem7649942)). Qed.
Lemma lem7649957 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7649958 : term365 = term102.
Proof. exact (@lem7649957 term117). Qed.
Lemma lem7649959 : term372 = term102.
Proof. exact (TRANS (@lem7649955) (@lem7649958)). Qed.
Lemma lem7649960 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649961 : term374 = term375.
Proof. exact (MK_COMB (@lem7649960) (@lem7649959)). Qed.
Lemma lem7649962 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7649963 : term376 = term324.
Proof. exact (MK_COMB (@lem7649961) (@lem7649962)). Qed.
Lemma lem7649965 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7649966 : term324 = term102.
Proof. exact (@lem7649965 term117). Qed.
Lemma lem7649967 : term376 = term102.
Proof. exact (TRANS (@lem7649963) (@lem7649966)). Qed.
Lemma lem7649969 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7649970 : term175 = term176.
Proof. exact (@lem7649969 term117 term117). Qed.
Lemma lem7649971 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7649972 : term178 = term117.
Proof. exact (EQ_MP (@lem7649971) (@lem940073)). Qed.
Lemma lem7649973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7649974 : term176 = term116.
Proof. exact (MK_COMB (@lem7649973) (@lem7649972)). Qed.
Lemma lem7649975 : term175 = term116.
Proof. exact (TRANS (@lem7649970) (@lem7649974)). Qed.
Lemma lem7649976 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7649977 : term377 = term324.
Proof. exact (MK_COMB (@lem7649976) (@lem7649975)). Qed.
Lemma lem7649979 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7649980 : term324 = term102.
Proof. exact (@lem7649979 term117). Qed.
Lemma lem7649981 : term377 = term102.
Proof. exact (TRANS (@lem7649977) (@lem7649980)). Qed.
Lemma lem7649982 : term102 = term377.
Proof. exact (SYM (@lem7649981)). Qed.
Lemma lem7649983 : term376 = term377.
Proof. exact (TRANS (@lem7649967) (@lem7649982)). Qed.
Lemma lem7649984 : term366 = term163.
Proof. exact (@lem7649934 (@lem7649983)). Qed.
Lemma lem7649985 : term365 = term163.
Proof. exact (TRANS (@lem7649900) (@lem7649984)). Qed.
Lemma lem7649987 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7649988 : term163 = term102.
Proof. exact (@lem7649987 term102). Qed.
Lemma lem7649989 : term365 = term102.
Proof. exact (TRANS (@lem7649985) (@lem7649988)). Qed.
Lemma lem7649990 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7649991 : term378 = term375.
Proof. exact (MK_COMB (@lem7649990) (@lem7649989)). Qed.
Lemma lem7649992 (_98520 : int) : (real_of_int _98520) = (real_of_int _98520).
Proof. exact (eq_refl (real_of_int _98520)). Qed.
Lemma lem7649993 (_98520 : int) : (term362 _98520) = (term379 _98520).
Proof. exact (MK_COMB (@lem7649991) (@lem7649992 _98520)). Qed.
Lemma lem7649994 (_98520 : int) : (term387 _98520) = (term379 _98520).
Proof. exact (TRANS (@lem7649891 _98520) (@lem7649993 _98520)). Qed.
Lemma lem7649995 (_98520 : int) : (term379 _98520) = term102.
Proof. exact (@lem1982719 (real_of_int _98520)). Qed.
Lemma lem7649996 (_98520 : int) : (term387 _98520) = term102.
Proof. exact (TRANS (@lem7649994 _98520) (@lem7649995 _98520)). Qed.
Lemma lem7649997 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7649998 (_98520 : int) : (term388 _98520) = term381.
Proof. exact (MK_COMB (@lem7649997) (@lem7649996 _98520)). Qed.
Lemma lem7649999 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem7650000 (_98520 : int) : (term386 _98520) = term389.
Proof. exact (MK_COMB (@lem7649998 _98520) (@lem7649999)). Qed.
Lemma lem7650001 (_98520 : int) : (term385 _98520) = term389.
Proof. exact (TRANS (@lem7649890 _98520) (@lem7650000 _98520)). Qed.
Lemma lem7650002 : term389 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem7650003 (_98520 : int) : (term385 _98520) = term166.
Proof. exact (TRANS (@lem7650001 _98520) (@lem7650002)). Qed.
Lemma lem7650004 (_98519 : int) (_98520 : int) : (term383 _98519 _98520) = term389.
Proof. exact (MK_COMB (@lem7649889 _98519) (@lem7650003 _98520)). Qed.
Lemma lem7650005 (_98519 : int) (_98520 : int) : (term382 _98519 _98520) = term389.
Proof. exact (TRANS (@lem7649781 _98519 _98520) (@lem7650004 _98519 _98520)). Qed.
Lemma lem7650006 : term389 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem7650007 (_98519 : int) (_98520 : int) : (term382 _98519 _98520) = term166.
Proof. exact (TRANS (@lem7650005 _98519 _98520) (@lem7650006)). Qed.
Lemma lem7650008 (_98518 : int) (_98519 : int) (_98520 : int) : (term360 _98518 _98519 _98520) = term389.
Proof. exact (MK_COMB (@lem7649780 _98518) (@lem7650007 _98519 _98520)). Qed.
Lemma lem7650009 (_98518 : int) (_98519 : int) (_98520 : int) : (term359 _98518 _98519 _98520) = term389.
Proof. exact (TRANS (@lem7649672 _98518 _98519 _98520) (@lem7650008 _98518 _98519 _98520)). Qed.
Lemma lem7650010 : term389 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem7650011 (_98518 : int) (_98519 : int) (_98520 : int) : (term359 _98518 _98519 _98520) = term166.
Proof. exact (TRANS (@lem7650009 _98518 _98519 _98520) (@lem7650010)). Qed.
Lemma lem7650012 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7650013 (_98518 : int) (_98519 : int) (_98520 : int) : (term390 _98518 _98519 _98520) = term391.
Proof. exact (MK_COMB (@lem7650012) (@lem7650011 _98518 _98519 _98520)). Qed.
Lemma lem7650014 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7650015 (_98518 : int) (_98519 : int) (_98520 : int) : (term358 _98518 _98519 _98520) = term392.
Proof. exact (MK_COMB (@lem7650013 _98518 _98519 _98520) (@lem7650014)). Qed.
Lemma lem7650016 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : term392.
Proof. exact (EQ_MP (@lem7650015 _98518 _98519 _98520) (@lem7649671 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650018 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7650019 : term392 = term393.
Proof. exact (@lem7650018 term102 term166). Qed.
Lemma lem7650021 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7650022 : term166 = term167.
Proof. exact (@lem7650021 term117). Qed.
Lemma lem7650024 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650025 : term102 = term163.
Proof. exact (@lem7650024 (NUMERAL 0)). Qed.
Lemma lem7650026 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7650027 : term104 = term394.
Proof. exact (MK_COMB (@lem7650026) (@lem7650025)). Qed.
Lemma lem7650028 : term393 = term395.
Proof. exact (MK_COMB (@lem7650027) (@lem7650022)). Qed.
Lemma lem7650029 : term396.
Proof. exact (@lem1980026 term102 term116 term166 term116). Qed.
Lemma lem7650031 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650032 : term313 = term319.
Proof. exact (@lem7650031 (NUMERAL 0) term117). Qed.
Lemma lem7650033 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650034 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650035 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650034 h1) (fun h1 : term319 = True => @lem7650033)). Qed.
Lemma lem7650036 : term319 = True.
Proof. exact (EQ_MP (@lem7650035) (@lem7650033)). Qed.
Lemma lem7650037 : term313 = True.
Proof. exact (TRANS (@lem7650032) (@lem7650036)). Qed.
Lemma lem7650038 : True = term313.
Proof. exact (SYM (@lem7650037)). Qed.
Lemma lem7650039 : term313.
Proof. exact (EQ_MP (@lem7650038) (@lem0)). Qed.
Lemma lem7650040 : term397.
Proof. exact (@lem7650029 (@lem7650039)). Qed.
Lemma lem7650042 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650043 : term313 = term319.
Proof. exact (@lem7650042 (NUMERAL 0) term117). Qed.
Lemma lem7650044 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650045 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650046 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650045 h1) (fun h1 : term319 = True => @lem7650044)). Qed.
Lemma lem7650047 : term319 = True.
Proof. exact (EQ_MP (@lem7650046) (@lem7650044)). Qed.
Lemma lem7650048 : term313 = True.
Proof. exact (TRANS (@lem7650043) (@lem7650047)). Qed.
Lemma lem7650049 : True = term313.
Proof. exact (SYM (@lem7650048)). Qed.
Lemma lem7650050 : term313.
Proof. exact (EQ_MP (@lem7650049) (@lem0)). Qed.
Lemma lem7650051 : term395 = term398.
Proof. exact (@lem7650040 (@lem7650050)). Qed.
Lemma lem7650053 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7650054 : term206 = term211.
Proof. exact (@lem7650053 term117 term117). Qed.
Lemma lem7650055 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650056 : term178 = term117.
Proof. exact (EQ_MP (@lem7650055) (@lem940073)). Qed.
Lemma lem7650057 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650058 : term176 = term116.
Proof. exact (MK_COMB (@lem7650057) (@lem7650056)). Qed.
Lemma lem7650059 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7650060 : term211 = term166.
Proof. exact (MK_COMB (@lem7650059) (@lem7650058)). Qed.
Lemma lem7650061 : term206 = term166.
Proof. exact (TRANS (@lem7650054) (@lem7650060)). Qed.
Lemma lem7650063 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7650064 : term324 = term102.
Proof. exact (@lem7650063 term117). Qed.
Lemma lem7650065 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7650066 : term399 = term104.
Proof. exact (MK_COMB (@lem7650065) (@lem7650064)). Qed.
Lemma lem7650067 : term398 = term393.
Proof. exact (MK_COMB (@lem7650066) (@lem7650061)). Qed.
Lemma lem7650069 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7650070 : term393 = term402.
Proof. exact (@lem7650069 (NUMERAL 0) term117). Qed.
Lemma lem7650071 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650072 (h1 : term320 = (BIT1 0)) : (term117 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7650073 : (term320 = (BIT1 0)) = ((term117 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650072 h1) (fun h1 : (term117 = (NUMERAL 0)) = False => @lem7650071)). Qed.
Lemma lem7650074 : (term117 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7650073) (@lem7650071)). Qed.
Lemma lem7650075 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7650076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7650077 : term403 = (and True).
Proof. exact (MK_COMB (@lem7650076) (@lem7650075)). Qed.
Lemma lem7650078 : term402 = (True /\ False).
Proof. exact (MK_COMB (@lem7650077) (@lem7650074)). Qed.
Lemma lem7650080 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7650081 : term402 = False.
Proof. exact (TRANS (@lem7650078) (@lem7650080)). Qed.
Lemma lem7650082 : term393 = False.
Proof. exact (TRANS (@lem7650070) (@lem7650081)). Qed.
Lemma lem7650083 : term398 = False.
Proof. exact (TRANS (@lem7650067) (@lem7650082)). Qed.
Lemma lem7650084 : term395 = False.
Proof. exact (TRANS (@lem7650051) (@lem7650083)). Qed.
Lemma lem7650085 : term393 = False.
Proof. exact (TRANS (@lem7650028) (@lem7650084)). Qed.
Lemma lem7650086 : term392 = False.
Proof. exact (TRANS (@lem7650019) (@lem7650085)). Qed.
Lemma lem7650087 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term311 _98518 _98519 _98520) : False.
Proof. exact (EQ_MP (@lem7650086) (@lem7650016 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650088 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term404 _98518 _98519 _98520.
Proof. exact (h1). Qed.
Lemma lem7650089 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term307 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7650088 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650091 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term294 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7650089 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650093 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term281 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7650091 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650095 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term263 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7650093 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650096 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term221 _98518 _98520 _98519.
Proof. exact (proj1 (@lem7650093 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650097 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : (real_of_int _98519) = term102.
Proof. exact (proj2 (@lem7650096 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650098 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term218 _98518 _98520.
Proof. exact (proj1 (@lem7650096 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650099 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term241 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7650095 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650102 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7650103 : term312 = term313.
Proof. exact (@lem7650102 term102 term116). Qed.
Lemma lem7650105 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650106 : term116 = term205.
Proof. exact (@lem7650105 term117). Qed.
Lemma lem7650108 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650109 : term102 = term163.
Proof. exact (@lem7650108 (NUMERAL 0)). Qed.
Lemma lem7650110 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7650111 : term314 = term315.
Proof. exact (MK_COMB (@lem7650110) (@lem7650109)). Qed.
Lemma lem7650112 : term313 = term316.
Proof. exact (MK_COMB (@lem7650111) (@lem7650106)). Qed.
Lemma lem7650113 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7650115 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650116 : term313 = term319.
Proof. exact (@lem7650115 (NUMERAL 0) term117). Qed.
Lemma lem7650117 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650118 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650119 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650118 h1) (fun h1 : term319 = True => @lem7650117)). Qed.
Lemma lem7650120 : term319 = True.
Proof. exact (EQ_MP (@lem7650119) (@lem7650117)). Qed.
Lemma lem7650121 : term313 = True.
Proof. exact (TRANS (@lem7650116) (@lem7650120)). Qed.
Lemma lem7650122 : True = term313.
Proof. exact (SYM (@lem7650121)). Qed.
Lemma lem7650123 : term313.
Proof. exact (EQ_MP (@lem7650122) (@lem0)). Qed.
Lemma lem7650124 : term321.
Proof. exact (@lem7650113 (@lem7650123)). Qed.
Lemma lem7650126 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650127 : term313 = term319.
Proof. exact (@lem7650126 (NUMERAL 0) term117). Qed.
Lemma lem7650128 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650129 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650130 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650129 h1) (fun h1 : term319 = True => @lem7650128)). Qed.
Lemma lem7650131 : term319 = True.
Proof. exact (EQ_MP (@lem7650130) (@lem7650128)). Qed.
Lemma lem7650132 : term313 = True.
Proof. exact (TRANS (@lem7650127) (@lem7650131)). Qed.
Lemma lem7650133 : True = term313.
Proof. exact (SYM (@lem7650132)). Qed.
Lemma lem7650134 : term313.
Proof. exact (EQ_MP (@lem7650133) (@lem0)). Qed.
Lemma lem7650135 : term316 = term322.
Proof. exact (@lem7650124 (@lem7650134)). Qed.
Lemma lem7650137 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7650138 : term175 = term176.
Proof. exact (@lem7650137 term117 term117). Qed.
Lemma lem7650139 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650140 : term178 = term117.
Proof. exact (EQ_MP (@lem7650139) (@lem940073)). Qed.
Lemma lem7650141 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650142 : term176 = term116.
Proof. exact (MK_COMB (@lem7650141) (@lem7650140)). Qed.
Lemma lem7650143 : term175 = term116.
Proof. exact (TRANS (@lem7650138) (@lem7650142)). Qed.
Lemma lem7650145 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7650146 : term324 = term102.
Proof. exact (@lem7650145 term117). Qed.
Lemma lem7650147 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7650148 : term325 = term314.
Proof. exact (MK_COMB (@lem7650147) (@lem7650146)). Qed.
Lemma lem7650149 : term322 = term313.
Proof. exact (MK_COMB (@lem7650148) (@lem7650143)). Qed.
Lemma lem7650151 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650152 : term313 = term319.
Proof. exact (@lem7650151 (NUMERAL 0) term117). Qed.
Lemma lem7650153 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650154 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650155 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650154 h1) (fun h1 : term319 = True => @lem7650153)). Qed.
Lemma lem7650156 : term319 = True.
Proof. exact (EQ_MP (@lem7650155) (@lem7650153)). Qed.
Lemma lem7650157 : term313 = True.
Proof. exact (TRANS (@lem7650152) (@lem7650156)). Qed.
Lemma lem7650158 : term322 = True.
Proof. exact (TRANS (@lem7650149) (@lem7650157)). Qed.
Lemma lem7650159 : term316 = True.
Proof. exact (TRANS (@lem7650135) (@lem7650158)). Qed.
Lemma lem7650160 : term313 = True.
Proof. exact (TRANS (@lem7650112) (@lem7650159)). Qed.
Lemma lem7650161 : term312 = True.
Proof. exact (TRANS (@lem7650103) (@lem7650160)). Qed.
Lemma lem7650162 : True = term312.
Proof. exact (SYM (@lem7650161)). Qed.
Lemma lem7650163 : term312.
Proof. exact (EQ_MP (@lem7650162) (@lem0)). Qed.
Lemma lem7650164 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term326 _98518 _98519 _98520.
Proof. exact (conj (@lem7650163) (@lem7650099 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650166 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7650167 (_98518 : int) (_98519 : int) (_98520 : int) : term328 _98518 _98519 _98520.
Proof. exact (@lem7650166 term116 (term238 _98518 _98519 _98520)). Qed.
Lemma lem7650168 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term329 _98518 _98519 _98520.
Proof. exact (@lem7650167 _98518 _98519 _98520 (@lem7650164 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650169 (_98518 : int) (_98519 : int) (_98520 : int) : (term330 _98518 _98519 _98520) = (term238 _98518 _98519 _98520).
Proof. exact (@lem1982733 (term238 _98518 _98519 _98520)). Qed.
Lemma lem7650170 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7650171 (_98518 : int) (_98519 : int) (_98520 : int) : (term331 _98518 _98519 _98520) = (term240 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7650170) (@lem7650169 _98518 _98519 _98520)). Qed.
Lemma lem7650172 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7650173 (_98518 : int) (_98519 : int) (_98520 : int) : (term329 _98518 _98519 _98520) = (term241 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7650171 _98518 _98519 _98520) (@lem7650172)). Qed.
Lemma lem7650174 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term241 _98518 _98519 _98520.
Proof. exact (EQ_MP (@lem7650173 _98518 _98519 _98520) (@lem7650168 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650176 (y : real) : term332 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7650177 (_98519 : int) : term405 _98519.
Proof. exact (@lem7650176 (real_of_int _98519)). Qed.
Lemma lem7650178 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term406 _98519.
Proof. exact (@lem7650177 _98519 (@lem7650097 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650179 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term407 _98519.
Proof. exact (@lem7650178 _98518 _98519 _98520 h1 term116). Qed.
Lemma lem7650180 (_98519 : int) : (term407 _98519) = ((term350 _98519) = term102).
Proof. exact (eq_refl (term407 _98519)). Qed.
Lemma lem7650181 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : (term350 _98519) = term102.
Proof. exact (EQ_MP (@lem7650180 _98519) (@lem7650179 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650182 (_98519 : int) : (term350 _98519) = (real_of_int _98519).
Proof. exact (@lem1982733 (real_of_int _98519)). Qed.
Lemma lem7650183 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7650184 (_98519 : int) : (term408 _98519) = (term108 _98519).
Proof. exact (MK_COMB (@lem7650183) (@lem7650182 _98519)). Qed.
Lemma lem7650185 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7650186 (_98519 : int) : ((term350 _98519) = term102) = ((real_of_int _98519) = term102).
Proof. exact (MK_COMB (@lem7650184 _98519) (@lem7650185)). Qed.
Lemma lem7650187 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : (real_of_int _98519) = term102.
Proof. exact (EQ_MP (@lem7650186 _98519) (@lem7650181 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650188 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term409 _98518 _98519 _98520.
Proof. exact (conj (@lem7650187 _98518 _98519 _98520 h1) (@lem7650174 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650190 (x : real) (y : real) : term356 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem7650191 (_98518 : int) (_98519 : int) (_98520 : int) : term410 _98518 _98519 _98520.
Proof. exact (@lem7650190 (real_of_int _98519) (term238 _98518 _98519 _98520)). Qed.
Lemma lem7650192 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term411 _98518 _98519 _98520.
Proof. exact (@lem7650191 _98518 _98519 _98520 (@lem7650188 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650193 (_98518 : int) (_98519 : int) (_98520 : int) : (term412 _98518 _98519 _98520) = (term413 _98518 _98519 _98520).
Proof. exact (@lem1982757 (term193 _98518) (real_of_int _98519) (term224 _98519 _98520)). Qed.
Lemma lem7650194 (_98519 : int) (_98520 : int) : (term414 _98519 _98520) = (term415 _98519 _98520).
Proof. exact (@lem1982763 (real_of_int _98519) (term193 _98519) (term384 _98520)). Qed.
Lemma lem7650195 (_98519 : int) : (term361 _98519) = (term362 _98519).
Proof. exact (@lem1982715 term166 (real_of_int _98519)). Qed.
Lemma lem7650197 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650198 : term116 = term205.
Proof. exact (@lem7650197 term117). Qed.
Lemma lem7650200 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7650201 : term166 = term167.
Proof. exact (@lem7650200 term117). Qed.
Lemma lem7650202 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7650203 : term363 = term364.
Proof. exact (MK_COMB (@lem7650202) (@lem7650201)). Qed.
Lemma lem7650204 : term365 = term366.
Proof. exact (MK_COMB (@lem7650203) (@lem7650198)). Qed.
Lemma lem7650205 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7650207 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650208 : term313 = term319.
Proof. exact (@lem7650207 (NUMERAL 0) term117). Qed.
Lemma lem7650209 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650210 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650211 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650210 h1) (fun h1 : term319 = True => @lem7650209)). Qed.
Lemma lem7650212 : term319 = True.
Proof. exact (EQ_MP (@lem7650211) (@lem7650209)). Qed.
Lemma lem7650213 : term313 = True.
Proof. exact (TRANS (@lem7650208) (@lem7650212)). Qed.
Lemma lem7650214 : True = term313.
Proof. exact (SYM (@lem7650213)). Qed.
Lemma lem7650215 : term313.
Proof. exact (EQ_MP (@lem7650214) (@lem0)). Qed.
Lemma lem7650216 : term368.
Proof. exact (@lem7650205 (@lem7650215)). Qed.
Lemma lem7650218 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650219 : term313 = term319.
Proof. exact (@lem7650218 (NUMERAL 0) term117). Qed.
Lemma lem7650220 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650221 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650222 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650221 h1) (fun h1 : term319 = True => @lem7650220)). Qed.
Lemma lem7650223 : term319 = True.
Proof. exact (EQ_MP (@lem7650222) (@lem7650220)). Qed.
Lemma lem7650224 : term313 = True.
Proof. exact (TRANS (@lem7650219) (@lem7650223)). Qed.
Lemma lem7650225 : True = term313.
Proof. exact (SYM (@lem7650224)). Qed.
Lemma lem7650226 : term313.
Proof. exact (EQ_MP (@lem7650225) (@lem0)). Qed.
Lemma lem7650227 : term369.
Proof. exact (@lem7650216 (@lem7650226)). Qed.
Lemma lem7650229 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650230 : term313 = term319.
Proof. exact (@lem7650229 (NUMERAL 0) term117). Qed.
Lemma lem7650231 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650232 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650233 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650232 h1) (fun h1 : term319 = True => @lem7650231)). Qed.
Lemma lem7650234 : term319 = True.
Proof. exact (EQ_MP (@lem7650233) (@lem7650231)). Qed.
Lemma lem7650235 : term313 = True.
Proof. exact (TRANS (@lem7650230) (@lem7650234)). Qed.
Lemma lem7650236 : True = term313.
Proof. exact (SYM (@lem7650235)). Qed.
Lemma lem7650237 : term313.
Proof. exact (EQ_MP (@lem7650236) (@lem0)). Qed.
Lemma lem7650238 : term370.
Proof. exact (@lem7650227 (@lem7650237)). Qed.
Lemma lem7650240 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7650241 : term175 = term176.
Proof. exact (@lem7650240 term117 term117). Qed.
Lemma lem7650242 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650243 : term178 = term117.
Proof. exact (EQ_MP (@lem7650242) (@lem940073)). Qed.
Lemma lem7650244 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650245 : term176 = term116.
Proof. exact (MK_COMB (@lem7650244) (@lem7650243)). Qed.
Lemma lem7650246 : term175 = term116.
Proof. exact (TRANS (@lem7650241) (@lem7650245)). Qed.
Lemma lem7650248 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7650249 : term206 = term211.
Proof. exact (@lem7650248 term117 term117). Qed.
Lemma lem7650250 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650251 : term178 = term117.
Proof. exact (EQ_MP (@lem7650250) (@lem940073)). Qed.
Lemma lem7650252 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650253 : term176 = term116.
Proof. exact (MK_COMB (@lem7650252) (@lem7650251)). Qed.
Lemma lem7650254 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7650255 : term211 = term166.
Proof. exact (MK_COMB (@lem7650254) (@lem7650253)). Qed.
Lemma lem7650256 : term206 = term166.
Proof. exact (TRANS (@lem7650249) (@lem7650255)). Qed.
Lemma lem7650257 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7650258 : term371 = term363.
Proof. exact (MK_COMB (@lem7650257) (@lem7650256)). Qed.
Lemma lem7650259 : term372 = term365.
Proof. exact (MK_COMB (@lem7650258) (@lem7650246)). Qed.
Lemma lem7650261 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7650262 : term365 = term102.
Proof. exact (@lem7650261 term117). Qed.
Lemma lem7650263 : term372 = term102.
Proof. exact (TRANS (@lem7650259) (@lem7650262)). Qed.
Lemma lem7650264 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7650265 : term374 = term375.
Proof. exact (MK_COMB (@lem7650264) (@lem7650263)). Qed.
Lemma lem7650266 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7650267 : term376 = term324.
Proof. exact (MK_COMB (@lem7650265) (@lem7650266)). Qed.
Lemma lem7650269 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7650270 : term324 = term102.
Proof. exact (@lem7650269 term117). Qed.
Lemma lem7650271 : term376 = term102.
Proof. exact (TRANS (@lem7650267) (@lem7650270)). Qed.
Lemma lem7650273 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7650274 : term175 = term176.
Proof. exact (@lem7650273 term117 term117). Qed.
Lemma lem7650275 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650276 : term178 = term117.
Proof. exact (EQ_MP (@lem7650275) (@lem940073)). Qed.
Lemma lem7650277 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650278 : term176 = term116.
Proof. exact (MK_COMB (@lem7650277) (@lem7650276)). Qed.
Lemma lem7650279 : term175 = term116.
Proof. exact (TRANS (@lem7650274) (@lem7650278)). Qed.
Lemma lem7650280 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7650281 : term377 = term324.
Proof. exact (MK_COMB (@lem7650280) (@lem7650279)). Qed.
Lemma lem7650283 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7650284 : term324 = term102.
Proof. exact (@lem7650283 term117). Qed.
Lemma lem7650285 : term377 = term102.
Proof. exact (TRANS (@lem7650281) (@lem7650284)). Qed.
Lemma lem7650286 : term102 = term377.
Proof. exact (SYM (@lem7650285)). Qed.
Lemma lem7650287 : term376 = term377.
Proof. exact (TRANS (@lem7650271) (@lem7650286)). Qed.
Lemma lem7650288 : term366 = term163.
Proof. exact (@lem7650238 (@lem7650287)). Qed.
Lemma lem7650289 : term365 = term163.
Proof. exact (TRANS (@lem7650204) (@lem7650288)). Qed.
Lemma lem7650291 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7650292 : term163 = term102.
Proof. exact (@lem7650291 term102). Qed.
Lemma lem7650293 : term365 = term102.
Proof. exact (TRANS (@lem7650289) (@lem7650292)). Qed.
Lemma lem7650294 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7650295 : term378 = term375.
Proof. exact (MK_COMB (@lem7650294) (@lem7650293)). Qed.
Lemma lem7650296 (_98519 : int) : (real_of_int _98519) = (real_of_int _98519).
Proof. exact (eq_refl (real_of_int _98519)). Qed.
Lemma lem7650297 (_98519 : int) : (term362 _98519) = (term379 _98519).
Proof. exact (MK_COMB (@lem7650295) (@lem7650296 _98519)). Qed.
Lemma lem7650298 (_98519 : int) : (term361 _98519) = (term379 _98519).
Proof. exact (TRANS (@lem7650195 _98519) (@lem7650297 _98519)). Qed.
Lemma lem7650299 (_98519 : int) : (term379 _98519) = term102.
Proof. exact (@lem1982719 (real_of_int _98519)). Qed.
Lemma lem7650300 (_98519 : int) : (term361 _98519) = term102.
Proof. exact (TRANS (@lem7650298 _98519) (@lem7650299 _98519)). Qed.
Lemma lem7650301 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7650302 (_98519 : int) : (term380 _98519) = term381.
Proof. exact (MK_COMB (@lem7650301) (@lem7650300 _98519)). Qed.
Lemma lem7650303 (_98520 : int) : (term384 _98520) = (term384 _98520).
Proof. exact (eq_refl (term384 _98520)). Qed.
Lemma lem7650304 (_98519 : int) (_98520 : int) : (term415 _98519 _98520) = (term416 _98520).
Proof. exact (MK_COMB (@lem7650302 _98519) (@lem7650303 _98520)). Qed.
Lemma lem7650305 (_98519 : int) (_98520 : int) : (term414 _98519 _98520) = (term416 _98520).
Proof. exact (TRANS (@lem7650194 _98519 _98520) (@lem7650304 _98519 _98520)). Qed.
Lemma lem7650306 (_98520 : int) : (term416 _98520) = (term384 _98520).
Proof. exact (@lem1982721 (term384 _98520)). Qed.
Lemma lem7650307 (_98519 : int) (_98520 : int) : (term414 _98519 _98520) = (term384 _98520).
Proof. exact (TRANS (@lem7650305 _98519 _98520) (@lem7650306 _98520)). Qed.
Lemma lem7650308 (_98518 : int) : (term196 _98518) = (term196 _98518).
Proof. exact (eq_refl (term196 _98518)). Qed.
Lemma lem7650309 (_98519 : int) (_98518 : int) (_98520 : int) : (term413 _98518 _98519 _98520) = (term224 _98518 _98520).
Proof. exact (MK_COMB (@lem7650308 _98518) (@lem7650307 _98519 _98520)). Qed.
Lemma lem7650310 (_98519 : int) (_98518 : int) (_98520 : int) : (term412 _98518 _98519 _98520) = (term224 _98518 _98520).
Proof. exact (TRANS (@lem7650193 _98518 _98519 _98520) (@lem7650309 _98519 _98518 _98520)). Qed.
Lemma lem7650311 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7650312 (_98519 : int) (_98518 : int) (_98520 : int) : (term417 _98518 _98519 _98520) = (term225 _98518 _98520).
Proof. exact (MK_COMB (@lem7650311) (@lem7650310 _98519 _98518 _98520)). Qed.
Lemma lem7650313 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7650314 (_98519 : int) (_98518 : int) (_98520 : int) : (term411 _98518 _98519 _98520) = (term226 _98518 _98520).
Proof. exact (MK_COMB (@lem7650312 _98519 _98518 _98520) (@lem7650313)). Qed.
Lemma lem7650315 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term226 _98518 _98520.
Proof. exact (EQ_MP (@lem7650314 _98519 _98518 _98520) (@lem7650192 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650317 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7650318 : term312 = term313.
Proof. exact (@lem7650317 term102 term116). Qed.
Lemma lem7650320 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650321 : term116 = term205.
Proof. exact (@lem7650320 term117). Qed.
Lemma lem7650323 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650324 : term102 = term163.
Proof. exact (@lem7650323 (NUMERAL 0)). Qed.
Lemma lem7650325 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7650326 : term314 = term315.
Proof. exact (MK_COMB (@lem7650325) (@lem7650324)). Qed.
Lemma lem7650327 : term313 = term316.
Proof. exact (MK_COMB (@lem7650326) (@lem7650321)). Qed.
Lemma lem7650328 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7650330 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650331 : term313 = term319.
Proof. exact (@lem7650330 (NUMERAL 0) term117). Qed.
Lemma lem7650332 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650333 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650334 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650333 h1) (fun h1 : term319 = True => @lem7650332)). Qed.
Lemma lem7650335 : term319 = True.
Proof. exact (EQ_MP (@lem7650334) (@lem7650332)). Qed.
Lemma lem7650336 : term313 = True.
Proof. exact (TRANS (@lem7650331) (@lem7650335)). Qed.
Lemma lem7650337 : True = term313.
Proof. exact (SYM (@lem7650336)). Qed.
Lemma lem7650338 : term313.
Proof. exact (EQ_MP (@lem7650337) (@lem0)). Qed.
Lemma lem7650339 : term321.
Proof. exact (@lem7650328 (@lem7650338)). Qed.
Lemma lem7650341 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650342 : term313 = term319.
Proof. exact (@lem7650341 (NUMERAL 0) term117). Qed.
Lemma lem7650343 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650344 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650345 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650344 h1) (fun h1 : term319 = True => @lem7650343)). Qed.
Lemma lem7650346 : term319 = True.
Proof. exact (EQ_MP (@lem7650345) (@lem7650343)). Qed.
Lemma lem7650347 : term313 = True.
Proof. exact (TRANS (@lem7650342) (@lem7650346)). Qed.
Lemma lem7650348 : True = term313.
Proof. exact (SYM (@lem7650347)). Qed.
Lemma lem7650349 : term313.
Proof. exact (EQ_MP (@lem7650348) (@lem0)). Qed.
Lemma lem7650350 : term316 = term322.
Proof. exact (@lem7650339 (@lem7650349)). Qed.
Lemma lem7650352 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7650353 : term175 = term176.
Proof. exact (@lem7650352 term117 term117). Qed.
Lemma lem7650354 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650355 : term178 = term117.
Proof. exact (EQ_MP (@lem7650354) (@lem940073)). Qed.
Lemma lem7650356 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650357 : term176 = term116.
Proof. exact (MK_COMB (@lem7650356) (@lem7650355)). Qed.
Lemma lem7650358 : term175 = term116.
Proof. exact (TRANS (@lem7650353) (@lem7650357)). Qed.
Lemma lem7650360 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7650361 : term324 = term102.
Proof. exact (@lem7650360 term117). Qed.
Lemma lem7650362 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7650363 : term325 = term314.
Proof. exact (MK_COMB (@lem7650362) (@lem7650361)). Qed.
Lemma lem7650364 : term322 = term313.
Proof. exact (MK_COMB (@lem7650363) (@lem7650358)). Qed.
Lemma lem7650366 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650367 : term313 = term319.
Proof. exact (@lem7650366 (NUMERAL 0) term117). Qed.
Lemma lem7650368 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650369 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650370 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650369 h1) (fun h1 : term319 = True => @lem7650368)). Qed.
Lemma lem7650371 : term319 = True.
Proof. exact (EQ_MP (@lem7650370) (@lem7650368)). Qed.
Lemma lem7650372 : term313 = True.
Proof. exact (TRANS (@lem7650367) (@lem7650371)). Qed.
Lemma lem7650373 : term322 = True.
Proof. exact (TRANS (@lem7650364) (@lem7650372)). Qed.
Lemma lem7650374 : term316 = True.
Proof. exact (TRANS (@lem7650350) (@lem7650373)). Qed.
Lemma lem7650375 : term313 = True.
Proof. exact (TRANS (@lem7650327) (@lem7650374)). Qed.
Lemma lem7650376 : term312 = True.
Proof. exact (TRANS (@lem7650318) (@lem7650375)). Qed.
Lemma lem7650377 : True = term312.
Proof. exact (SYM (@lem7650376)). Qed.
Lemma lem7650378 : term312.
Proof. exact (EQ_MP (@lem7650377) (@lem0)). Qed.
Lemma lem7650379 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term418 _98518 _98520.
Proof. exact (conj (@lem7650378) (@lem7650315 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650381 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7650382 (_98518 : int) (_98520 : int) : term419 _98518 _98520.
Proof. exact (@lem7650381 term116 (term224 _98518 _98520)). Qed.
Lemma lem7650383 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term420 _98518 _98520.
Proof. exact (@lem7650382 _98518 _98520 (@lem7650379 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650384 (_98518 : int) (_98520 : int) : (term421 _98518 _98520) = (term224 _98518 _98520).
Proof. exact (@lem1982733 (term224 _98518 _98520)). Qed.
Lemma lem7650385 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7650386 (_98518 : int) (_98520 : int) : (term422 _98518 _98520) = (term225 _98518 _98520).
Proof. exact (MK_COMB (@lem7650385) (@lem7650384 _98518 _98520)). Qed.
Lemma lem7650387 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7650388 (_98518 : int) (_98520 : int) : (term420 _98518 _98520) = (term226 _98518 _98520).
Proof. exact (MK_COMB (@lem7650386 _98518 _98520) (@lem7650387)). Qed.
Lemma lem7650389 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term226 _98518 _98520.
Proof. exact (EQ_MP (@lem7650388 _98518 _98520) (@lem7650383 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650391 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7650392 : term312 = term313.
Proof. exact (@lem7650391 term102 term116). Qed.
Lemma lem7650394 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650395 : term116 = term205.
Proof. exact (@lem7650394 term117). Qed.
Lemma lem7650397 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650398 : term102 = term163.
Proof. exact (@lem7650397 (NUMERAL 0)). Qed.
Lemma lem7650399 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7650400 : term314 = term315.
Proof. exact (MK_COMB (@lem7650399) (@lem7650398)). Qed.
Lemma lem7650401 : term313 = term316.
Proof. exact (MK_COMB (@lem7650400) (@lem7650395)). Qed.
Lemma lem7650402 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7650404 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650405 : term313 = term319.
Proof. exact (@lem7650404 (NUMERAL 0) term117). Qed.
Lemma lem7650406 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650407 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650408 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650407 h1) (fun h1 : term319 = True => @lem7650406)). Qed.
Lemma lem7650409 : term319 = True.
Proof. exact (EQ_MP (@lem7650408) (@lem7650406)). Qed.
Lemma lem7650410 : term313 = True.
Proof. exact (TRANS (@lem7650405) (@lem7650409)). Qed.
Lemma lem7650411 : True = term313.
Proof. exact (SYM (@lem7650410)). Qed.
Lemma lem7650412 : term313.
Proof. exact (EQ_MP (@lem7650411) (@lem0)). Qed.
Lemma lem7650413 : term321.
Proof. exact (@lem7650402 (@lem7650412)). Qed.
Lemma lem7650415 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650416 : term313 = term319.
Proof. exact (@lem7650415 (NUMERAL 0) term117). Qed.
Lemma lem7650417 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650418 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650419 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650418 h1) (fun h1 : term319 = True => @lem7650417)). Qed.
Lemma lem7650420 : term319 = True.
Proof. exact (EQ_MP (@lem7650419) (@lem7650417)). Qed.
Lemma lem7650421 : term313 = True.
Proof. exact (TRANS (@lem7650416) (@lem7650420)). Qed.
Lemma lem7650422 : True = term313.
Proof. exact (SYM (@lem7650421)). Qed.
Lemma lem7650423 : term313.
Proof. exact (EQ_MP (@lem7650422) (@lem0)). Qed.
Lemma lem7650424 : term316 = term322.
Proof. exact (@lem7650413 (@lem7650423)). Qed.
Lemma lem7650426 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7650427 : term175 = term176.
Proof. exact (@lem7650426 term117 term117). Qed.
Lemma lem7650428 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650429 : term178 = term117.
Proof. exact (EQ_MP (@lem7650428) (@lem940073)). Qed.
Lemma lem7650430 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650431 : term176 = term116.
Proof. exact (MK_COMB (@lem7650430) (@lem7650429)). Qed.
Lemma lem7650432 : term175 = term116.
Proof. exact (TRANS (@lem7650427) (@lem7650431)). Qed.
Lemma lem7650434 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7650435 : term324 = term102.
Proof. exact (@lem7650434 term117). Qed.
Lemma lem7650436 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7650437 : term325 = term314.
Proof. exact (MK_COMB (@lem7650436) (@lem7650435)). Qed.
Lemma lem7650438 : term322 = term313.
Proof. exact (MK_COMB (@lem7650437) (@lem7650432)). Qed.
Lemma lem7650440 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650441 : term313 = term319.
Proof. exact (@lem7650440 (NUMERAL 0) term117). Qed.
Lemma lem7650442 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650443 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650444 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650443 h1) (fun h1 : term319 = True => @lem7650442)). Qed.
Lemma lem7650445 : term319 = True.
Proof. exact (EQ_MP (@lem7650444) (@lem7650442)). Qed.
Lemma lem7650446 : term313 = True.
Proof. exact (TRANS (@lem7650441) (@lem7650445)). Qed.
Lemma lem7650447 : term322 = True.
Proof. exact (TRANS (@lem7650438) (@lem7650446)). Qed.
Lemma lem7650448 : term316 = True.
Proof. exact (TRANS (@lem7650424) (@lem7650447)). Qed.
Lemma lem7650449 : term313 = True.
Proof. exact (TRANS (@lem7650401) (@lem7650448)). Qed.
Lemma lem7650450 : term312 = True.
Proof. exact (TRANS (@lem7650392) (@lem7650449)). Qed.
Lemma lem7650451 : True = term312.
Proof. exact (SYM (@lem7650450)). Qed.
Lemma lem7650452 : term312.
Proof. exact (EQ_MP (@lem7650451) (@lem0)). Qed.
Lemma lem7650453 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term423 _98518 _98520.
Proof. exact (conj (@lem7650452) (@lem7650098 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650455 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7650456 (_98518 : int) (_98520 : int) : term424 _98518 _98520.
Proof. exact (@lem7650455 term116 (term215 _98518 _98520)). Qed.
Lemma lem7650457 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term425 _98518 _98520.
Proof. exact (@lem7650456 _98518 _98520 (@lem7650453 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650458 (_98518 : int) (_98520 : int) : (term426 _98518 _98520) = (term215 _98518 _98520).
Proof. exact (@lem1982733 (term215 _98518 _98520)). Qed.
Lemma lem7650459 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7650460 (_98518 : int) (_98520 : int) : (term427 _98518 _98520) = (term217 _98518 _98520).
Proof. exact (MK_COMB (@lem7650459) (@lem7650458 _98518 _98520)). Qed.
Lemma lem7650461 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7650462 (_98518 : int) (_98520 : int) : (term425 _98518 _98520) = (term218 _98518 _98520).
Proof. exact (MK_COMB (@lem7650460 _98518 _98520) (@lem7650461)). Qed.
Lemma lem7650463 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term218 _98518 _98520.
Proof. exact (EQ_MP (@lem7650462 _98518 _98520) (@lem7650457 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650464 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term428 _98518 _98520.
Proof. exact (conj (@lem7650463 _98518 _98519 _98520 h1) (@lem7650389 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650466 (x : real) (y : real) : term429 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7650467 (_98518 : int) (_98520 : int) : term430 _98518 _98520.
Proof. exact (@lem7650466 (term215 _98518 _98520) (term224 _98518 _98520)). Qed.
Lemma lem7650468 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term431 _98518 _98520.
Proof. exact (@lem7650467 _98518 _98520 (@lem7650464 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650469 (_98518 : int) (_98520 : int) : (term432 _98518 _98520) = (term433 _98518 _98520).
Proof. exact (@lem1982753 (real_of_int _98518) (term193 _98518) (term214 _98520) (term384 _98520)). Qed.
Lemma lem7650470 (_98518 : int) : (term361 _98518) = (term362 _98518).
Proof. exact (@lem1982715 term166 (real_of_int _98518)). Qed.
Lemma lem7650472 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650473 : term116 = term205.
Proof. exact (@lem7650472 term117). Qed.
Lemma lem7650475 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7650476 : term166 = term167.
Proof. exact (@lem7650475 term117). Qed.
Lemma lem7650477 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7650478 : term363 = term364.
Proof. exact (MK_COMB (@lem7650477) (@lem7650476)). Qed.
Lemma lem7650479 : term365 = term366.
Proof. exact (MK_COMB (@lem7650478) (@lem7650473)). Qed.
Lemma lem7650480 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7650482 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650483 : term313 = term319.
Proof. exact (@lem7650482 (NUMERAL 0) term117). Qed.
Lemma lem7650484 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650485 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650486 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650485 h1) (fun h1 : term319 = True => @lem7650484)). Qed.
Lemma lem7650487 : term319 = True.
Proof. exact (EQ_MP (@lem7650486) (@lem7650484)). Qed.
Lemma lem7650488 : term313 = True.
Proof. exact (TRANS (@lem7650483) (@lem7650487)). Qed.
Lemma lem7650489 : True = term313.
Proof. exact (SYM (@lem7650488)). Qed.
Lemma lem7650490 : term313.
Proof. exact (EQ_MP (@lem7650489) (@lem0)). Qed.
Lemma lem7650491 : term368.
Proof. exact (@lem7650480 (@lem7650490)). Qed.
Lemma lem7650493 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650494 : term313 = term319.
Proof. exact (@lem7650493 (NUMERAL 0) term117). Qed.
Lemma lem7650495 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650496 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650497 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650496 h1) (fun h1 : term319 = True => @lem7650495)). Qed.
Lemma lem7650498 : term319 = True.
Proof. exact (EQ_MP (@lem7650497) (@lem7650495)). Qed.
Lemma lem7650499 : term313 = True.
Proof. exact (TRANS (@lem7650494) (@lem7650498)). Qed.
Lemma lem7650500 : True = term313.
Proof. exact (SYM (@lem7650499)). Qed.
Lemma lem7650501 : term313.
Proof. exact (EQ_MP (@lem7650500) (@lem0)). Qed.
Lemma lem7650502 : term369.
Proof. exact (@lem7650491 (@lem7650501)). Qed.
Lemma lem7650504 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650505 : term313 = term319.
Proof. exact (@lem7650504 (NUMERAL 0) term117). Qed.
Lemma lem7650506 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650507 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650508 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650507 h1) (fun h1 : term319 = True => @lem7650506)). Qed.
Lemma lem7650509 : term319 = True.
Proof. exact (EQ_MP (@lem7650508) (@lem7650506)). Qed.
Lemma lem7650510 : term313 = True.
Proof. exact (TRANS (@lem7650505) (@lem7650509)). Qed.
Lemma lem7650511 : True = term313.
Proof. exact (SYM (@lem7650510)). Qed.
Lemma lem7650512 : term313.
Proof. exact (EQ_MP (@lem7650511) (@lem0)). Qed.
Lemma lem7650513 : term370.
Proof. exact (@lem7650502 (@lem7650512)). Qed.
Lemma lem7650515 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7650516 : term175 = term176.
Proof. exact (@lem7650515 term117 term117). Qed.
Lemma lem7650517 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650518 : term178 = term117.
Proof. exact (EQ_MP (@lem7650517) (@lem940073)). Qed.
Lemma lem7650519 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650520 : term176 = term116.
Proof. exact (MK_COMB (@lem7650519) (@lem7650518)). Qed.
Lemma lem7650521 : term175 = term116.
Proof. exact (TRANS (@lem7650516) (@lem7650520)). Qed.
Lemma lem7650523 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7650524 : term206 = term211.
Proof. exact (@lem7650523 term117 term117). Qed.
Lemma lem7650525 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650526 : term178 = term117.
Proof. exact (EQ_MP (@lem7650525) (@lem940073)). Qed.
Lemma lem7650527 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650528 : term176 = term116.
Proof. exact (MK_COMB (@lem7650527) (@lem7650526)). Qed.
Lemma lem7650529 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7650530 : term211 = term166.
Proof. exact (MK_COMB (@lem7650529) (@lem7650528)). Qed.
Lemma lem7650531 : term206 = term166.
Proof. exact (TRANS (@lem7650524) (@lem7650530)). Qed.
Lemma lem7650532 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7650533 : term371 = term363.
Proof. exact (MK_COMB (@lem7650532) (@lem7650531)). Qed.
Lemma lem7650534 : term372 = term365.
Proof. exact (MK_COMB (@lem7650533) (@lem7650521)). Qed.
Lemma lem7650536 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7650537 : term365 = term102.
Proof. exact (@lem7650536 term117). Qed.
Lemma lem7650538 : term372 = term102.
Proof. exact (TRANS (@lem7650534) (@lem7650537)). Qed.
Lemma lem7650539 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7650540 : term374 = term375.
Proof. exact (MK_COMB (@lem7650539) (@lem7650538)). Qed.
Lemma lem7650541 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7650542 : term376 = term324.
Proof. exact (MK_COMB (@lem7650540) (@lem7650541)). Qed.
Lemma lem7650544 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7650545 : term324 = term102.
Proof. exact (@lem7650544 term117). Qed.
Lemma lem7650546 : term376 = term102.
Proof. exact (TRANS (@lem7650542) (@lem7650545)). Qed.
Lemma lem7650548 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7650549 : term175 = term176.
Proof. exact (@lem7650548 term117 term117). Qed.
Lemma lem7650550 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650551 : term178 = term117.
Proof. exact (EQ_MP (@lem7650550) (@lem940073)). Qed.
Lemma lem7650552 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650553 : term176 = term116.
Proof. exact (MK_COMB (@lem7650552) (@lem7650551)). Qed.
Lemma lem7650554 : term175 = term116.
Proof. exact (TRANS (@lem7650549) (@lem7650553)). Qed.
Lemma lem7650555 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7650556 : term377 = term324.
Proof. exact (MK_COMB (@lem7650555) (@lem7650554)). Qed.
Lemma lem7650558 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7650559 : term324 = term102.
Proof. exact (@lem7650558 term117). Qed.
Lemma lem7650560 : term377 = term102.
Proof. exact (TRANS (@lem7650556) (@lem7650559)). Qed.
Lemma lem7650561 : term102 = term377.
Proof. exact (SYM (@lem7650560)). Qed.
Lemma lem7650562 : term376 = term377.
Proof. exact (TRANS (@lem7650546) (@lem7650561)). Qed.
Lemma lem7650563 : term366 = term163.
Proof. exact (@lem7650513 (@lem7650562)). Qed.
Lemma lem7650564 : term365 = term163.
Proof. exact (TRANS (@lem7650479) (@lem7650563)). Qed.
Lemma lem7650566 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7650567 : term163 = term102.
Proof. exact (@lem7650566 term102). Qed.
Lemma lem7650568 : term365 = term102.
Proof. exact (TRANS (@lem7650564) (@lem7650567)). Qed.
Lemma lem7650569 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7650570 : term378 = term375.
Proof. exact (MK_COMB (@lem7650569) (@lem7650568)). Qed.
Lemma lem7650571 (_98518 : int) : (real_of_int _98518) = (real_of_int _98518).
Proof. exact (eq_refl (real_of_int _98518)). Qed.
Lemma lem7650572 (_98518 : int) : (term362 _98518) = (term379 _98518).
Proof. exact (MK_COMB (@lem7650570) (@lem7650571 _98518)). Qed.
Lemma lem7650573 (_98518 : int) : (term361 _98518) = (term379 _98518).
Proof. exact (TRANS (@lem7650470 _98518) (@lem7650572 _98518)). Qed.
Lemma lem7650574 (_98518 : int) : (term379 _98518) = term102.
Proof. exact (@lem1982719 (real_of_int _98518)). Qed.
Lemma lem7650575 (_98518 : int) : (term361 _98518) = term102.
Proof. exact (TRANS (@lem7650573 _98518) (@lem7650574 _98518)). Qed.
Lemma lem7650576 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7650577 (_98518 : int) : (term380 _98518) = term381.
Proof. exact (MK_COMB (@lem7650576) (@lem7650575 _98518)). Qed.
Lemma lem7650578 (_98520 : int) : (term434 _98520) = (term435 _98520).
Proof. exact (@lem1982753 (term193 _98520) (real_of_int _98520) term166 term166). Qed.
Lemma lem7650579 (_98520 : int) : (term387 _98520) = (term362 _98520).
Proof. exact (@lem1982713 term166 (real_of_int _98520)). Qed.
Lemma lem7650581 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650582 : term116 = term205.
Proof. exact (@lem7650581 term117). Qed.
Lemma lem7650584 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7650585 : term166 = term167.
Proof. exact (@lem7650584 term117). Qed.
Lemma lem7650586 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7650587 : term363 = term364.
Proof. exact (MK_COMB (@lem7650586) (@lem7650585)). Qed.
Lemma lem7650588 : term365 = term366.
Proof. exact (MK_COMB (@lem7650587) (@lem7650582)). Qed.
Lemma lem7650589 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7650591 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650592 : term313 = term319.
Proof. exact (@lem7650591 (NUMERAL 0) term117). Qed.
Lemma lem7650593 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650594 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650595 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650594 h1) (fun h1 : term319 = True => @lem7650593)). Qed.
Lemma lem7650596 : term319 = True.
Proof. exact (EQ_MP (@lem7650595) (@lem7650593)). Qed.
Lemma lem7650597 : term313 = True.
Proof. exact (TRANS (@lem7650592) (@lem7650596)). Qed.
Lemma lem7650598 : True = term313.
Proof. exact (SYM (@lem7650597)). Qed.
Lemma lem7650599 : term313.
Proof. exact (EQ_MP (@lem7650598) (@lem0)). Qed.
Lemma lem7650600 : term368.
Proof. exact (@lem7650589 (@lem7650599)). Qed.
Lemma lem7650602 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650603 : term313 = term319.
Proof. exact (@lem7650602 (NUMERAL 0) term117). Qed.
Lemma lem7650604 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650605 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650606 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650605 h1) (fun h1 : term319 = True => @lem7650604)). Qed.
Lemma lem7650607 : term319 = True.
Proof. exact (EQ_MP (@lem7650606) (@lem7650604)). Qed.
Lemma lem7650608 : term313 = True.
Proof. exact (TRANS (@lem7650603) (@lem7650607)). Qed.
Lemma lem7650609 : True = term313.
Proof. exact (SYM (@lem7650608)). Qed.
Lemma lem7650610 : term313.
Proof. exact (EQ_MP (@lem7650609) (@lem0)). Qed.
Lemma lem7650611 : term369.
Proof. exact (@lem7650600 (@lem7650610)). Qed.
Lemma lem7650613 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650614 : term313 = term319.
Proof. exact (@lem7650613 (NUMERAL 0) term117). Qed.
Lemma lem7650615 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650616 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650617 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650616 h1) (fun h1 : term319 = True => @lem7650615)). Qed.
Lemma lem7650618 : term319 = True.
Proof. exact (EQ_MP (@lem7650617) (@lem7650615)). Qed.
Lemma lem7650619 : term313 = True.
Proof. exact (TRANS (@lem7650614) (@lem7650618)). Qed.
Lemma lem7650620 : True = term313.
Proof. exact (SYM (@lem7650619)). Qed.
Lemma lem7650621 : term313.
Proof. exact (EQ_MP (@lem7650620) (@lem0)). Qed.
Lemma lem7650622 : term370.
Proof. exact (@lem7650611 (@lem7650621)). Qed.
Lemma lem7650624 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7650625 : term175 = term176.
Proof. exact (@lem7650624 term117 term117). Qed.
Lemma lem7650626 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650627 : term178 = term117.
Proof. exact (EQ_MP (@lem7650626) (@lem940073)). Qed.
Lemma lem7650628 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650629 : term176 = term116.
Proof. exact (MK_COMB (@lem7650628) (@lem7650627)). Qed.
Lemma lem7650630 : term175 = term116.
Proof. exact (TRANS (@lem7650625) (@lem7650629)). Qed.
Lemma lem7650632 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7650633 : term206 = term211.
Proof. exact (@lem7650632 term117 term117). Qed.
Lemma lem7650634 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650635 : term178 = term117.
Proof. exact (EQ_MP (@lem7650634) (@lem940073)). Qed.
Lemma lem7650636 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650637 : term176 = term116.
Proof. exact (MK_COMB (@lem7650636) (@lem7650635)). Qed.
Lemma lem7650638 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7650639 : term211 = term166.
Proof. exact (MK_COMB (@lem7650638) (@lem7650637)). Qed.
Lemma lem7650640 : term206 = term166.
Proof. exact (TRANS (@lem7650633) (@lem7650639)). Qed.
Lemma lem7650641 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7650642 : term371 = term363.
Proof. exact (MK_COMB (@lem7650641) (@lem7650640)). Qed.
Lemma lem7650643 : term372 = term365.
Proof. exact (MK_COMB (@lem7650642) (@lem7650630)). Qed.
Lemma lem7650645 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7650646 : term365 = term102.
Proof. exact (@lem7650645 term117). Qed.
Lemma lem7650647 : term372 = term102.
Proof. exact (TRANS (@lem7650643) (@lem7650646)). Qed.
Lemma lem7650648 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7650649 : term374 = term375.
Proof. exact (MK_COMB (@lem7650648) (@lem7650647)). Qed.
Lemma lem7650650 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7650651 : term376 = term324.
Proof. exact (MK_COMB (@lem7650649) (@lem7650650)). Qed.
Lemma lem7650653 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7650654 : term324 = term102.
Proof. exact (@lem7650653 term117). Qed.
Lemma lem7650655 : term376 = term102.
Proof. exact (TRANS (@lem7650651) (@lem7650654)). Qed.
Lemma lem7650657 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7650658 : term175 = term176.
Proof. exact (@lem7650657 term117 term117). Qed.
Lemma lem7650659 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650660 : term178 = term117.
Proof. exact (EQ_MP (@lem7650659) (@lem940073)). Qed.
Lemma lem7650661 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650662 : term176 = term116.
Proof. exact (MK_COMB (@lem7650661) (@lem7650660)). Qed.
Lemma lem7650663 : term175 = term116.
Proof. exact (TRANS (@lem7650658) (@lem7650662)). Qed.
Lemma lem7650664 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7650665 : term377 = term324.
Proof. exact (MK_COMB (@lem7650664) (@lem7650663)). Qed.
Lemma lem7650667 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7650668 : term324 = term102.
Proof. exact (@lem7650667 term117). Qed.
Lemma lem7650669 : term377 = term102.
Proof. exact (TRANS (@lem7650665) (@lem7650668)). Qed.
Lemma lem7650670 : term102 = term377.
Proof. exact (SYM (@lem7650669)). Qed.
Lemma lem7650671 : term376 = term377.
Proof. exact (TRANS (@lem7650655) (@lem7650670)). Qed.
Lemma lem7650672 : term366 = term163.
Proof. exact (@lem7650622 (@lem7650671)). Qed.
Lemma lem7650673 : term365 = term163.
Proof. exact (TRANS (@lem7650588) (@lem7650672)). Qed.
Lemma lem7650675 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7650676 : term163 = term102.
Proof. exact (@lem7650675 term102). Qed.
Lemma lem7650677 : term365 = term102.
Proof. exact (TRANS (@lem7650673) (@lem7650676)). Qed.
Lemma lem7650678 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7650679 : term378 = term375.
Proof. exact (MK_COMB (@lem7650678) (@lem7650677)). Qed.
Lemma lem7650680 (_98520 : int) : (real_of_int _98520) = (real_of_int _98520).
Proof. exact (eq_refl (real_of_int _98520)). Qed.
Lemma lem7650681 (_98520 : int) : (term362 _98520) = (term379 _98520).
Proof. exact (MK_COMB (@lem7650679) (@lem7650680 _98520)). Qed.
Lemma lem7650682 (_98520 : int) : (term387 _98520) = (term379 _98520).
Proof. exact (TRANS (@lem7650579 _98520) (@lem7650681 _98520)). Qed.
Lemma lem7650683 (_98520 : int) : (term379 _98520) = term102.
Proof. exact (@lem1982719 (real_of_int _98520)). Qed.
Lemma lem7650684 (_98520 : int) : (term387 _98520) = term102.
Proof. exact (TRANS (@lem7650682 _98520) (@lem7650683 _98520)). Qed.
Lemma lem7650685 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7650686 (_98520 : int) : (term388 _98520) = term381.
Proof. exact (MK_COMB (@lem7650685) (@lem7650684 _98520)). Qed.
Lemma lem7650688 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7650689 : term166 = term167.
Proof. exact (@lem7650688 term117). Qed.
Lemma lem7650691 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7650692 : term166 = term167.
Proof. exact (@lem7650691 term117). Qed.
Lemma lem7650693 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7650694 : term363 = term364.
Proof. exact (MK_COMB (@lem7650693) (@lem7650692)). Qed.
Lemma lem7650695 : term436 = term437.
Proof. exact (MK_COMB (@lem7650694) (@lem7650689)). Qed.
Lemma lem7650696 : term438.
Proof. exact (@lem1981473 term166 term116 term166 term116 term439 term116). Qed.
Lemma lem7650698 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650699 : term313 = term319.
Proof. exact (@lem7650698 (NUMERAL 0) term117). Qed.
Lemma lem7650700 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650701 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650702 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650701 h1) (fun h1 : term319 = True => @lem7650700)). Qed.
Lemma lem7650703 : term319 = True.
Proof. exact (EQ_MP (@lem7650702) (@lem7650700)). Qed.
Lemma lem7650704 : term313 = True.
Proof. exact (TRANS (@lem7650699) (@lem7650703)). Qed.
Lemma lem7650705 : True = term313.
Proof. exact (SYM (@lem7650704)). Qed.
Lemma lem7650706 : term313.
Proof. exact (EQ_MP (@lem7650705) (@lem0)). Qed.
Lemma lem7650707 : term440.
Proof. exact (@lem7650696 (@lem7650706)). Qed.
Lemma lem7650709 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650710 : term313 = term319.
Proof. exact (@lem7650709 (NUMERAL 0) term117). Qed.
Lemma lem7650711 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650712 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650713 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650712 h1) (fun h1 : term319 = True => @lem7650711)). Qed.
Lemma lem7650714 : term319 = True.
Proof. exact (EQ_MP (@lem7650713) (@lem7650711)). Qed.
Lemma lem7650715 : term313 = True.
Proof. exact (TRANS (@lem7650710) (@lem7650714)). Qed.
Lemma lem7650716 : True = term313.
Proof. exact (SYM (@lem7650715)). Qed.
Lemma lem7650717 : term313.
Proof. exact (EQ_MP (@lem7650716) (@lem0)). Qed.
Lemma lem7650718 : term441.
Proof. exact (@lem7650707 (@lem7650717)). Qed.
Lemma lem7650720 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650721 : term313 = term319.
Proof. exact (@lem7650720 (NUMERAL 0) term117). Qed.
Lemma lem7650722 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650723 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650724 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650723 h1) (fun h1 : term319 = True => @lem7650722)). Qed.
Lemma lem7650725 : term319 = True.
Proof. exact (EQ_MP (@lem7650724) (@lem7650722)). Qed.
Lemma lem7650726 : term313 = True.
Proof. exact (TRANS (@lem7650721) (@lem7650725)). Qed.
Lemma lem7650727 : True = term313.
Proof. exact (SYM (@lem7650726)). Qed.
Lemma lem7650728 : term313.
Proof. exact (EQ_MP (@lem7650727) (@lem0)). Qed.
Lemma lem7650729 : term442.
Proof. exact (@lem7650718 (@lem7650728)). Qed.
Lemma lem7650731 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7650732 : term206 = term211.
Proof. exact (@lem7650731 term117 term117). Qed.
Lemma lem7650733 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650734 : term178 = term117.
Proof. exact (EQ_MP (@lem7650733) (@lem940073)). Qed.
Lemma lem7650735 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650736 : term176 = term116.
Proof. exact (MK_COMB (@lem7650735) (@lem7650734)). Qed.
Lemma lem7650737 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7650738 : term211 = term166.
Proof. exact (MK_COMB (@lem7650737) (@lem7650736)). Qed.
Lemma lem7650739 : term206 = term166.
Proof. exact (TRANS (@lem7650732) (@lem7650738)). Qed.
Lemma lem7650741 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7650742 : term206 = term211.
Proof. exact (@lem7650741 term117 term117). Qed.
Lemma lem7650743 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650744 : term178 = term117.
Proof. exact (EQ_MP (@lem7650743) (@lem940073)). Qed.
Lemma lem7650745 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650746 : term176 = term116.
Proof. exact (MK_COMB (@lem7650745) (@lem7650744)). Qed.
Lemma lem7650747 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7650748 : term211 = term166.
Proof. exact (MK_COMB (@lem7650747) (@lem7650746)). Qed.
Lemma lem7650749 : term206 = term166.
Proof. exact (TRANS (@lem7650742) (@lem7650748)). Qed.
Lemma lem7650750 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7650751 : term371 = term363.
Proof. exact (MK_COMB (@lem7650750) (@lem7650749)). Qed.
Lemma lem7650752 : term443 = term436.
Proof. exact (MK_COMB (@lem7650751) (@lem7650739)). Qed.
Lemma lem7650753 : term436 = term444.
Proof. exact (@lem1367763 term117 term117). Qed.
Lemma lem7650754 : term445 = term446.
Proof. exact (@lem706885). Qed.
Lemma lem7650755 : (term445 = term446) = (term447 = term448).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term446). Qed.
Lemma lem7650756 : term447 = term448.
Proof. exact (EQ_MP (@lem7650755) (@lem7650754)). Qed.
Lemma lem7650757 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650758 : term449 = term450.
Proof. exact (MK_COMB (@lem7650757) (@lem7650756)). Qed.
Lemma lem7650759 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7650760 : term444 = term439.
Proof. exact (MK_COMB (@lem7650759) (@lem7650758)). Qed.
Lemma lem7650761 : term436 = term439.
Proof. exact (TRANS (@lem7650753) (@lem7650760)). Qed.
Lemma lem7650762 : term443 = term439.
Proof. exact (TRANS (@lem7650752) (@lem7650761)). Qed.
Lemma lem7650763 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7650764 : term451 = term452.
Proof. exact (MK_COMB (@lem7650763) (@lem7650762)). Qed.
Lemma lem7650765 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7650766 : term453 = term454.
Proof. exact (MK_COMB (@lem7650764) (@lem7650765)). Qed.
Lemma lem7650768 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7650769 : term454 = term455.
Proof. exact (@lem7650768 term448 term117). Qed.
Lemma lem7650770 : term456 = term446.
Proof. exact (@lem996237 term446). Qed.
Lemma lem7650771 : (term456 = term446) = (term457 = term448).
Proof. exact (@lem1007663 term446 (BIT1 0) term446). Qed.
Lemma lem7650772 : term457 = term448.
Proof. exact (EQ_MP (@lem7650771) (@lem7650770)). Qed.
Lemma lem7650773 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650774 : term458 = term450.
Proof. exact (MK_COMB (@lem7650773) (@lem7650772)). Qed.
Lemma lem7650775 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7650776 : term455 = term439.
Proof. exact (MK_COMB (@lem7650775) (@lem7650774)). Qed.
Lemma lem7650777 : term454 = term439.
Proof. exact (TRANS (@lem7650769) (@lem7650776)). Qed.
Lemma lem7650778 : term453 = term439.
Proof. exact (TRANS (@lem7650766) (@lem7650777)). Qed.
Lemma lem7650780 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7650781 : term175 = term176.
Proof. exact (@lem7650780 term117 term117). Qed.
Lemma lem7650782 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650783 : term178 = term117.
Proof. exact (EQ_MP (@lem7650782) (@lem940073)). Qed.
Lemma lem7650784 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650785 : term176 = term116.
Proof. exact (MK_COMB (@lem7650784) (@lem7650783)). Qed.
Lemma lem7650786 : term175 = term116.
Proof. exact (TRANS (@lem7650781) (@lem7650785)). Qed.
Lemma lem7650787 : term452 = term452.
Proof. exact (eq_refl term452). Qed.
Lemma lem7650788 : term459 = term454.
Proof. exact (MK_COMB (@lem7650787) (@lem7650786)). Qed.
Lemma lem7650790 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7650791 : term454 = term455.
Proof. exact (@lem7650790 term448 term117). Qed.
Lemma lem7650792 : term456 = term446.
Proof. exact (@lem996237 term446). Qed.
Lemma lem7650793 : (term456 = term446) = (term457 = term448).
Proof. exact (@lem1007663 term446 (BIT1 0) term446). Qed.
Lemma lem7650794 : term457 = term448.
Proof. exact (EQ_MP (@lem7650793) (@lem7650792)). Qed.
Lemma lem7650795 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650796 : term458 = term450.
Proof. exact (MK_COMB (@lem7650795) (@lem7650794)). Qed.
Lemma lem7650797 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7650798 : term455 = term439.
Proof. exact (MK_COMB (@lem7650797) (@lem7650796)). Qed.
Lemma lem7650799 : term454 = term439.
Proof. exact (TRANS (@lem7650791) (@lem7650798)). Qed.
Lemma lem7650800 : term459 = term439.
Proof. exact (TRANS (@lem7650788) (@lem7650799)). Qed.
Lemma lem7650801 : term439 = term459.
Proof. exact (SYM (@lem7650800)). Qed.
Lemma lem7650802 : term453 = term459.
Proof. exact (TRANS (@lem7650778) (@lem7650801)). Qed.
Lemma lem7650803 : term437 = term460.
Proof. exact (@lem7650729 (@lem7650802)). Qed.
Lemma lem7650804 : term436 = term460.
Proof. exact (TRANS (@lem7650695) (@lem7650803)). Qed.
Lemma lem7650806 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7650807 : term460 = term439.
Proof. exact (@lem7650806 term439). Qed.
Lemma lem7650808 : term436 = term439.
Proof. exact (TRANS (@lem7650804) (@lem7650807)). Qed.
Lemma lem7650809 (_98520 : int) : (term435 _98520) = term461.
Proof. exact (MK_COMB (@lem7650686 _98520) (@lem7650808)). Qed.
Lemma lem7650810 (_98520 : int) : (term434 _98520) = term461.
Proof. exact (TRANS (@lem7650578 _98520) (@lem7650809 _98520)). Qed.
Lemma lem7650811 : term461 = term439.
Proof. exact (@lem1982721 term439). Qed.
Lemma lem7650812 (_98520 : int) : (term434 _98520) = term439.
Proof. exact (TRANS (@lem7650810 _98520) (@lem7650811)). Qed.
Lemma lem7650813 (_98518 : int) (_98520 : int) : (term433 _98518 _98520) = term461.
Proof. exact (MK_COMB (@lem7650577 _98518) (@lem7650812 _98520)). Qed.
Lemma lem7650814 (_98518 : int) (_98520 : int) : (term432 _98518 _98520) = term461.
Proof. exact (TRANS (@lem7650469 _98518 _98520) (@lem7650813 _98518 _98520)). Qed.
Lemma lem7650815 : term461 = term439.
Proof. exact (@lem1982721 term439). Qed.
Lemma lem7650816 (_98518 : int) (_98520 : int) : (term432 _98518 _98520) = term439.
Proof. exact (TRANS (@lem7650814 _98518 _98520) (@lem7650815)). Qed.
Lemma lem7650817 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7650818 (_98518 : int) (_98520 : int) : (term462 _98518 _98520) = term463.
Proof. exact (MK_COMB (@lem7650817) (@lem7650816 _98518 _98520)). Qed.
Lemma lem7650819 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7650820 (_98518 : int) (_98520 : int) : (term431 _98518 _98520) = term464.
Proof. exact (MK_COMB (@lem7650818 _98518 _98520) (@lem7650819)). Qed.
Lemma lem7650821 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : term464.
Proof. exact (EQ_MP (@lem7650820 _98518 _98520) (@lem7650468 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650823 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7650824 : term464 = term465.
Proof. exact (@lem7650823 term102 term439). Qed.
Lemma lem7650826 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7650827 : term439 = term460.
Proof. exact (@lem7650826 term448). Qed.
Lemma lem7650829 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650830 : term102 = term163.
Proof. exact (@lem7650829 (NUMERAL 0)). Qed.
Lemma lem7650831 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7650832 : term104 = term394.
Proof. exact (MK_COMB (@lem7650831) (@lem7650830)). Qed.
Lemma lem7650833 : term465 = term466.
Proof. exact (MK_COMB (@lem7650832) (@lem7650827)). Qed.
Lemma lem7650834 : term467.
Proof. exact (@lem1980026 term102 term116 term439 term116). Qed.
Lemma lem7650836 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650837 : term313 = term319.
Proof. exact (@lem7650836 (NUMERAL 0) term117). Qed.
Lemma lem7650838 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650839 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650840 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650839 h1) (fun h1 : term319 = True => @lem7650838)). Qed.
Lemma lem7650841 : term319 = True.
Proof. exact (EQ_MP (@lem7650840) (@lem7650838)). Qed.
Lemma lem7650842 : term313 = True.
Proof. exact (TRANS (@lem7650837) (@lem7650841)). Qed.
Lemma lem7650843 : True = term313.
Proof. exact (SYM (@lem7650842)). Qed.
Lemma lem7650844 : term313.
Proof. exact (EQ_MP (@lem7650843) (@lem0)). Qed.
Lemma lem7650845 : term468.
Proof. exact (@lem7650834 (@lem7650844)). Qed.
Lemma lem7650847 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650848 : term313 = term319.
Proof. exact (@lem7650847 (NUMERAL 0) term117). Qed.
Lemma lem7650849 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650850 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650851 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650850 h1) (fun h1 : term319 = True => @lem7650849)). Qed.
Lemma lem7650852 : term319 = True.
Proof. exact (EQ_MP (@lem7650851) (@lem7650849)). Qed.
Lemma lem7650853 : term313 = True.
Proof. exact (TRANS (@lem7650848) (@lem7650852)). Qed.
Lemma lem7650854 : True = term313.
Proof. exact (SYM (@lem7650853)). Qed.
Lemma lem7650855 : term313.
Proof. exact (EQ_MP (@lem7650854) (@lem0)). Qed.
Lemma lem7650856 : term466 = term469.
Proof. exact (@lem7650845 (@lem7650855)). Qed.
Lemma lem7650858 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7650859 : term454 = term455.
Proof. exact (@lem7650858 term448 term117). Qed.
Lemma lem7650860 : term456 = term446.
Proof. exact (@lem996237 term446). Qed.
Lemma lem7650861 : (term456 = term446) = (term457 = term448).
Proof. exact (@lem1007663 term446 (BIT1 0) term446). Qed.
Lemma lem7650862 : term457 = term448.
Proof. exact (EQ_MP (@lem7650861) (@lem7650860)). Qed.
Lemma lem7650863 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650864 : term458 = term450.
Proof. exact (MK_COMB (@lem7650863) (@lem7650862)). Qed.
Lemma lem7650865 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7650866 : term455 = term439.
Proof. exact (MK_COMB (@lem7650865) (@lem7650864)). Qed.
Lemma lem7650867 : term454 = term439.
Proof. exact (TRANS (@lem7650859) (@lem7650866)). Qed.
Lemma lem7650869 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7650870 : term324 = term102.
Proof. exact (@lem7650869 term117). Qed.
Lemma lem7650871 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7650872 : term399 = term104.
Proof. exact (MK_COMB (@lem7650871) (@lem7650870)). Qed.
Lemma lem7650873 : term469 = term465.
Proof. exact (MK_COMB (@lem7650872) (@lem7650867)). Qed.
Lemma lem7650875 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7650876 : term465 = term470.
Proof. exact (@lem7650875 (NUMERAL 0) term448). Qed.
Lemma lem7650877 : term471 = term446.
Proof. exact (@lem912803). Qed.
Lemma lem7650878 (h1 : term471 = term446) : (term448 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term446 h1). Qed.
Lemma lem7650879 : (term471 = term446) = ((term448 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term471 = term446 => @lem7650878 h1) (fun h1 : (term448 = (NUMERAL 0)) = False => @lem7650877)). Qed.
Lemma lem7650880 : (term448 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7650879) (@lem7650877)). Qed.
Lemma lem7650881 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7650882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7650883 : term403 = (and True).
Proof. exact (MK_COMB (@lem7650882) (@lem7650881)). Qed.
Lemma lem7650884 : term470 = (True /\ False).
Proof. exact (MK_COMB (@lem7650883) (@lem7650880)). Qed.
Lemma lem7650886 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7650887 : term470 = False.
Proof. exact (TRANS (@lem7650884) (@lem7650886)). Qed.
Lemma lem7650888 : term465 = False.
Proof. exact (TRANS (@lem7650876) (@lem7650887)). Qed.
Lemma lem7650889 : term469 = False.
Proof. exact (TRANS (@lem7650873) (@lem7650888)). Qed.
Lemma lem7650890 : term466 = False.
Proof. exact (TRANS (@lem7650856) (@lem7650889)). Qed.
Lemma lem7650891 : term465 = False.
Proof. exact (TRANS (@lem7650833) (@lem7650890)). Qed.
Lemma lem7650892 : term464 = False.
Proof. exact (TRANS (@lem7650824) (@lem7650891)). Qed.
Lemma lem7650893 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term404 _98518 _98519 _98520) : False.
Proof. exact (EQ_MP (@lem7650892) (@lem7650821 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650894 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term305 _98518 _98519 _98520) : False.
Proof. exact (or_elim (@lem7649472 _98518 _98519 _98520 h1) (fun h0 : term311 _98518 _98519 _98520 => @lem7650087 _98518 _98519 _98520 h0) (fun h0 : term404 _98518 _98519 _98520 => @lem7650893 _98518 _98519 _98520 h0)). Qed.
Lemma lem7650895 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term301 _98518 _98519 _98520) : term301 _98518 _98519 _98520.
Proof. exact (h1). Qed.
Lemma lem7650896 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term472 _98518 _98519 _98520.
Proof. exact (h1). Qed.
Lemma lem7650897 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term302 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7650896 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650899 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term289 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7650897 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650901 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term276 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7650899 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650903 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term264 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7650901 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650904 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : (term197 _98518 _98519 _98520) = term102.
Proof. exact (proj1 (@lem7650901 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650905 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term249 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7650903 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650908 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7650909 : term312 = term313.
Proof. exact (@lem7650908 term102 term116). Qed.
Lemma lem7650911 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650912 : term116 = term205.
Proof. exact (@lem7650911 term117). Qed.
Lemma lem7650914 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7650915 : term102 = term163.
Proof. exact (@lem7650914 (NUMERAL 0)). Qed.
Lemma lem7650916 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7650917 : term314 = term315.
Proof. exact (MK_COMB (@lem7650916) (@lem7650915)). Qed.
Lemma lem7650918 : term313 = term316.
Proof. exact (MK_COMB (@lem7650917) (@lem7650912)). Qed.
Lemma lem7650919 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7650921 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650922 : term313 = term319.
Proof. exact (@lem7650921 (NUMERAL 0) term117). Qed.
Lemma lem7650923 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650924 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650925 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650924 h1) (fun h1 : term319 = True => @lem7650923)). Qed.
Lemma lem7650926 : term319 = True.
Proof. exact (EQ_MP (@lem7650925) (@lem7650923)). Qed.
Lemma lem7650927 : term313 = True.
Proof. exact (TRANS (@lem7650922) (@lem7650926)). Qed.
Lemma lem7650928 : True = term313.
Proof. exact (SYM (@lem7650927)). Qed.
Lemma lem7650929 : term313.
Proof. exact (EQ_MP (@lem7650928) (@lem0)). Qed.
Lemma lem7650930 : term321.
Proof. exact (@lem7650919 (@lem7650929)). Qed.
Lemma lem7650932 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650933 : term313 = term319.
Proof. exact (@lem7650932 (NUMERAL 0) term117). Qed.
Lemma lem7650934 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650935 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650936 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650935 h1) (fun h1 : term319 = True => @lem7650934)). Qed.
Lemma lem7650937 : term319 = True.
Proof. exact (EQ_MP (@lem7650936) (@lem7650934)). Qed.
Lemma lem7650938 : term313 = True.
Proof. exact (TRANS (@lem7650933) (@lem7650937)). Qed.
Lemma lem7650939 : True = term313.
Proof. exact (SYM (@lem7650938)). Qed.
Lemma lem7650940 : term313.
Proof. exact (EQ_MP (@lem7650939) (@lem0)). Qed.
Lemma lem7650941 : term316 = term322.
Proof. exact (@lem7650930 (@lem7650940)). Qed.
Lemma lem7650943 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7650944 : term175 = term176.
Proof. exact (@lem7650943 term117 term117). Qed.
Lemma lem7650945 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7650946 : term178 = term117.
Proof. exact (EQ_MP (@lem7650945) (@lem940073)). Qed.
Lemma lem7650947 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7650948 : term176 = term116.
Proof. exact (MK_COMB (@lem7650947) (@lem7650946)). Qed.
Lemma lem7650949 : term175 = term116.
Proof. exact (TRANS (@lem7650944) (@lem7650948)). Qed.
Lemma lem7650951 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7650952 : term324 = term102.
Proof. exact (@lem7650951 term117). Qed.
Lemma lem7650953 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7650954 : term325 = term314.
Proof. exact (MK_COMB (@lem7650953) (@lem7650952)). Qed.
Lemma lem7650955 : term322 = term313.
Proof. exact (MK_COMB (@lem7650954) (@lem7650949)). Qed.
Lemma lem7650957 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7650958 : term313 = term319.
Proof. exact (@lem7650957 (NUMERAL 0) term117). Qed.
Lemma lem7650959 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7650960 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7650961 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7650960 h1) (fun h1 : term319 = True => @lem7650959)). Qed.
Lemma lem7650962 : term319 = True.
Proof. exact (EQ_MP (@lem7650961) (@lem7650959)). Qed.
Lemma lem7650963 : term313 = True.
Proof. exact (TRANS (@lem7650958) (@lem7650962)). Qed.
Lemma lem7650964 : term322 = True.
Proof. exact (TRANS (@lem7650955) (@lem7650963)). Qed.
Lemma lem7650965 : term316 = True.
Proof. exact (TRANS (@lem7650941) (@lem7650964)). Qed.
Lemma lem7650966 : term313 = True.
Proof. exact (TRANS (@lem7650918) (@lem7650965)). Qed.
Lemma lem7650967 : term312 = True.
Proof. exact (TRANS (@lem7650909) (@lem7650966)). Qed.
Lemma lem7650968 : True = term312.
Proof. exact (SYM (@lem7650967)). Qed.
Lemma lem7650969 : term312.
Proof. exact (EQ_MP (@lem7650968) (@lem0)). Qed.
Lemma lem7650970 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term473 _98518 _98519 _98520.
Proof. exact (conj (@lem7650969) (@lem7650905 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650972 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7650973 (_98518 : int) (_98519 : int) (_98520 : int) : term474 _98518 _98519 _98520.
Proof. exact (@lem7650972 term116 (term246 _98518 _98519 _98520)). Qed.
Lemma lem7650974 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term475 _98518 _98519 _98520.
Proof. exact (@lem7650973 _98518 _98519 _98520 (@lem7650970 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650975 (_98518 : int) (_98519 : int) (_98520 : int) : (term476 _98518 _98519 _98520) = (term246 _98518 _98519 _98520).
Proof. exact (@lem1982733 (term246 _98518 _98519 _98520)). Qed.
Lemma lem7650976 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7650977 (_98518 : int) (_98519 : int) (_98520 : int) : (term477 _98518 _98519 _98520) = (term248 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7650976) (@lem7650975 _98518 _98519 _98520)). Qed.
Lemma lem7650978 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7650979 (_98518 : int) (_98519 : int) (_98520 : int) : (term475 _98518 _98519 _98520) = (term249 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7650977 _98518 _98519 _98520) (@lem7650978)). Qed.
Lemma lem7650980 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term249 _98518 _98519 _98520.
Proof. exact (EQ_MP (@lem7650979 _98518 _98519 _98520) (@lem7650974 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650982 (y : real) : term332 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7650983 (_98518 : int) (_98519 : int) (_98520 : int) : term333 _98518 _98519 _98520.
Proof. exact (@lem7650982 (term197 _98518 _98519 _98520)). Qed.
Lemma lem7650984 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term334 _98518 _98519 _98520.
Proof. exact (@lem7650983 _98518 _98519 _98520 (@lem7650904 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650985 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term478 _98518 _98519 _98520.
Proof. exact (@lem7650984 _98518 _98519 _98520 h1 term116). Qed.
Lemma lem7650986 (_98518 : int) (_98519 : int) (_98520 : int) : (term478 _98518 _98519 _98520) = ((term479 _98518 _98519 _98520) = term102).
Proof. exact (eq_refl (term478 _98518 _98519 _98520)). Qed.
Lemma lem7650987 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : (term479 _98518 _98519 _98520) = term102.
Proof. exact (EQ_MP (@lem7650986 _98518 _98519 _98520) (@lem7650985 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650988 (_98518 : int) (_98519 : int) (_98520 : int) : (term479 _98518 _98519 _98520) = (term197 _98518 _98519 _98520).
Proof. exact (@lem1982733 (term197 _98518 _98519 _98520)). Qed.
Lemma lem7650989 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7650990 (_98518 : int) (_98519 : int) (_98520 : int) : (term480 _98518 _98519 _98520) = (term199 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7650989) (@lem7650988 _98518 _98519 _98520)). Qed.
Lemma lem7650991 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7650992 (_98518 : int) (_98519 : int) (_98520 : int) : ((term479 _98518 _98519 _98520) = term102) = ((term197 _98518 _98519 _98520) = term102).
Proof. exact (MK_COMB (@lem7650990 _98518 _98519 _98520) (@lem7650991)). Qed.
Lemma lem7650993 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : (term197 _98518 _98519 _98520) = term102.
Proof. exact (EQ_MP (@lem7650992 _98518 _98519 _98520) (@lem7650987 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650994 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term481 _98518 _98519 _98520.
Proof. exact (conj (@lem7650993 _98518 _98519 _98520 h1) (@lem7650980 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650996 (x : real) (y : real) : term356 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem7650997 (_98518 : int) (_98519 : int) (_98520 : int) : term482 _98518 _98519 _98520.
Proof. exact (@lem7650996 (term197 _98518 _98519 _98520) (term246 _98518 _98519 _98520)). Qed.
Lemma lem7650998 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term483 _98518 _98519 _98520.
Proof. exact (@lem7650997 _98518 _98519 _98520 (@lem7650994 _98518 _98519 _98520 h1)). Qed.
Lemma lem7650999 (_98518 : int) (_98519 : int) (_98520 : int) : (term484 _98518 _98519 _98520) = (term485 _98518 _98519 _98520).
Proof. exact (@lem1982753 (term193 _98518) (real_of_int _98518) (term195 _98519 _98520) (term215 _98519 _98520)). Qed.
Lemma lem7651000 (_98518 : int) : (term387 _98518) = (term362 _98518).
Proof. exact (@lem1982713 term166 (real_of_int _98518)). Qed.
Lemma lem7651002 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651003 : term116 = term205.
Proof. exact (@lem7651002 term117). Qed.
Lemma lem7651005 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7651006 : term166 = term167.
Proof. exact (@lem7651005 term117). Qed.
Lemma lem7651007 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651008 : term363 = term364.
Proof. exact (MK_COMB (@lem7651007) (@lem7651006)). Qed.
Lemma lem7651009 : term365 = term366.
Proof. exact (MK_COMB (@lem7651008) (@lem7651003)). Qed.
Lemma lem7651010 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7651012 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651013 : term313 = term319.
Proof. exact (@lem7651012 (NUMERAL 0) term117). Qed.
Lemma lem7651014 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651015 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651016 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651015 h1) (fun h1 : term319 = True => @lem7651014)). Qed.
Lemma lem7651017 : term319 = True.
Proof. exact (EQ_MP (@lem7651016) (@lem7651014)). Qed.
Lemma lem7651018 : term313 = True.
Proof. exact (TRANS (@lem7651013) (@lem7651017)). Qed.
Lemma lem7651019 : True = term313.
Proof. exact (SYM (@lem7651018)). Qed.
Lemma lem7651020 : term313.
Proof. exact (EQ_MP (@lem7651019) (@lem0)). Qed.
Lemma lem7651021 : term368.
Proof. exact (@lem7651010 (@lem7651020)). Qed.
Lemma lem7651023 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651024 : term313 = term319.
Proof. exact (@lem7651023 (NUMERAL 0) term117). Qed.
Lemma lem7651025 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651026 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651027 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651026 h1) (fun h1 : term319 = True => @lem7651025)). Qed.
Lemma lem7651028 : term319 = True.
Proof. exact (EQ_MP (@lem7651027) (@lem7651025)). Qed.
Lemma lem7651029 : term313 = True.
Proof. exact (TRANS (@lem7651024) (@lem7651028)). Qed.
Lemma lem7651030 : True = term313.
Proof. exact (SYM (@lem7651029)). Qed.
Lemma lem7651031 : term313.
Proof. exact (EQ_MP (@lem7651030) (@lem0)). Qed.
Lemma lem7651032 : term369.
Proof. exact (@lem7651021 (@lem7651031)). Qed.
Lemma lem7651034 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651035 : term313 = term319.
Proof. exact (@lem7651034 (NUMERAL 0) term117). Qed.
Lemma lem7651036 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651037 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651038 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651037 h1) (fun h1 : term319 = True => @lem7651036)). Qed.
Lemma lem7651039 : term319 = True.
Proof. exact (EQ_MP (@lem7651038) (@lem7651036)). Qed.
Lemma lem7651040 : term313 = True.
Proof. exact (TRANS (@lem7651035) (@lem7651039)). Qed.
Lemma lem7651041 : True = term313.
Proof. exact (SYM (@lem7651040)). Qed.
Lemma lem7651042 : term313.
Proof. exact (EQ_MP (@lem7651041) (@lem0)). Qed.
Lemma lem7651043 : term370.
Proof. exact (@lem7651032 (@lem7651042)). Qed.
Lemma lem7651045 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651046 : term175 = term176.
Proof. exact (@lem7651045 term117 term117). Qed.
Lemma lem7651047 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651048 : term178 = term117.
Proof. exact (EQ_MP (@lem7651047) (@lem940073)). Qed.
Lemma lem7651049 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651050 : term176 = term116.
Proof. exact (MK_COMB (@lem7651049) (@lem7651048)). Qed.
Lemma lem7651051 : term175 = term116.
Proof. exact (TRANS (@lem7651046) (@lem7651050)). Qed.
Lemma lem7651053 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7651054 : term206 = term211.
Proof. exact (@lem7651053 term117 term117). Qed.
Lemma lem7651055 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651056 : term178 = term117.
Proof. exact (EQ_MP (@lem7651055) (@lem940073)). Qed.
Lemma lem7651057 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651058 : term176 = term116.
Proof. exact (MK_COMB (@lem7651057) (@lem7651056)). Qed.
Lemma lem7651059 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7651060 : term211 = term166.
Proof. exact (MK_COMB (@lem7651059) (@lem7651058)). Qed.
Lemma lem7651061 : term206 = term166.
Proof. exact (TRANS (@lem7651054) (@lem7651060)). Qed.
Lemma lem7651062 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651063 : term371 = term363.
Proof. exact (MK_COMB (@lem7651062) (@lem7651061)). Qed.
Lemma lem7651064 : term372 = term365.
Proof. exact (MK_COMB (@lem7651063) (@lem7651051)). Qed.
Lemma lem7651066 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7651067 : term365 = term102.
Proof. exact (@lem7651066 term117). Qed.
Lemma lem7651068 : term372 = term102.
Proof. exact (TRANS (@lem7651064) (@lem7651067)). Qed.
Lemma lem7651069 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7651070 : term374 = term375.
Proof. exact (MK_COMB (@lem7651069) (@lem7651068)). Qed.
Lemma lem7651071 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7651072 : term376 = term324.
Proof. exact (MK_COMB (@lem7651070) (@lem7651071)). Qed.
Lemma lem7651074 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651075 : term324 = term102.
Proof. exact (@lem7651074 term117). Qed.
Lemma lem7651076 : term376 = term102.
Proof. exact (TRANS (@lem7651072) (@lem7651075)). Qed.
Lemma lem7651078 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651079 : term175 = term176.
Proof. exact (@lem7651078 term117 term117). Qed.
Lemma lem7651080 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651081 : term178 = term117.
Proof. exact (EQ_MP (@lem7651080) (@lem940073)). Qed.
Lemma lem7651082 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651083 : term176 = term116.
Proof. exact (MK_COMB (@lem7651082) (@lem7651081)). Qed.
Lemma lem7651084 : term175 = term116.
Proof. exact (TRANS (@lem7651079) (@lem7651083)). Qed.
Lemma lem7651085 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7651086 : term377 = term324.
Proof. exact (MK_COMB (@lem7651085) (@lem7651084)). Qed.
Lemma lem7651088 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651089 : term324 = term102.
Proof. exact (@lem7651088 term117). Qed.
Lemma lem7651090 : term377 = term102.
Proof. exact (TRANS (@lem7651086) (@lem7651089)). Qed.
Lemma lem7651091 : term102 = term377.
Proof. exact (SYM (@lem7651090)). Qed.
Lemma lem7651092 : term376 = term377.
Proof. exact (TRANS (@lem7651076) (@lem7651091)). Qed.
Lemma lem7651093 : term366 = term163.
Proof. exact (@lem7651043 (@lem7651092)). Qed.
Lemma lem7651094 : term365 = term163.
Proof. exact (TRANS (@lem7651009) (@lem7651093)). Qed.
Lemma lem7651096 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7651097 : term163 = term102.
Proof. exact (@lem7651096 term102). Qed.
Lemma lem7651098 : term365 = term102.
Proof. exact (TRANS (@lem7651094) (@lem7651097)). Qed.
Lemma lem7651099 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7651100 : term378 = term375.
Proof. exact (MK_COMB (@lem7651099) (@lem7651098)). Qed.
Lemma lem7651101 (_98518 : int) : (real_of_int _98518) = (real_of_int _98518).
Proof. exact (eq_refl (real_of_int _98518)). Qed.
Lemma lem7651102 (_98518 : int) : (term362 _98518) = (term379 _98518).
Proof. exact (MK_COMB (@lem7651100) (@lem7651101 _98518)). Qed.
Lemma lem7651103 (_98518 : int) : (term387 _98518) = (term379 _98518).
Proof. exact (TRANS (@lem7651000 _98518) (@lem7651102 _98518)). Qed.
Lemma lem7651104 (_98518 : int) : (term379 _98518) = term102.
Proof. exact (@lem1982719 (real_of_int _98518)). Qed.
Lemma lem7651105 (_98518 : int) : (term387 _98518) = term102.
Proof. exact (TRANS (@lem7651103 _98518) (@lem7651104 _98518)). Qed.
Lemma lem7651106 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651107 (_98518 : int) : (term388 _98518) = term381.
Proof. exact (MK_COMB (@lem7651106) (@lem7651105 _98518)). Qed.
Lemma lem7651108 (_98519 : int) (_98520 : int) : (term486 _98519 _98520) = (term487 _98519 _98520).
Proof. exact (@lem1982753 (term193 _98519) (real_of_int _98519) (real_of_int _98520) (term214 _98520)). Qed.
Lemma lem7651109 (_98519 : int) : (term387 _98519) = (term362 _98519).
Proof. exact (@lem1982713 term166 (real_of_int _98519)). Qed.
Lemma lem7651111 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651112 : term116 = term205.
Proof. exact (@lem7651111 term117). Qed.
Lemma lem7651114 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7651115 : term166 = term167.
Proof. exact (@lem7651114 term117). Qed.
Lemma lem7651116 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651117 : term363 = term364.
Proof. exact (MK_COMB (@lem7651116) (@lem7651115)). Qed.
Lemma lem7651118 : term365 = term366.
Proof. exact (MK_COMB (@lem7651117) (@lem7651112)). Qed.
Lemma lem7651119 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7651121 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651122 : term313 = term319.
Proof. exact (@lem7651121 (NUMERAL 0) term117). Qed.
Lemma lem7651123 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651124 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651125 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651124 h1) (fun h1 : term319 = True => @lem7651123)). Qed.
Lemma lem7651126 : term319 = True.
Proof. exact (EQ_MP (@lem7651125) (@lem7651123)). Qed.
Lemma lem7651127 : term313 = True.
Proof. exact (TRANS (@lem7651122) (@lem7651126)). Qed.
Lemma lem7651128 : True = term313.
Proof. exact (SYM (@lem7651127)). Qed.
Lemma lem7651129 : term313.
Proof. exact (EQ_MP (@lem7651128) (@lem0)). Qed.
Lemma lem7651130 : term368.
Proof. exact (@lem7651119 (@lem7651129)). Qed.
Lemma lem7651132 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651133 : term313 = term319.
Proof. exact (@lem7651132 (NUMERAL 0) term117). Qed.
Lemma lem7651134 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651135 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651136 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651135 h1) (fun h1 : term319 = True => @lem7651134)). Qed.
Lemma lem7651137 : term319 = True.
Proof. exact (EQ_MP (@lem7651136) (@lem7651134)). Qed.
Lemma lem7651138 : term313 = True.
Proof. exact (TRANS (@lem7651133) (@lem7651137)). Qed.
Lemma lem7651139 : True = term313.
Proof. exact (SYM (@lem7651138)). Qed.
Lemma lem7651140 : term313.
Proof. exact (EQ_MP (@lem7651139) (@lem0)). Qed.
Lemma lem7651141 : term369.
Proof. exact (@lem7651130 (@lem7651140)). Qed.
Lemma lem7651143 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651144 : term313 = term319.
Proof. exact (@lem7651143 (NUMERAL 0) term117). Qed.
Lemma lem7651145 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651146 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651147 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651146 h1) (fun h1 : term319 = True => @lem7651145)). Qed.
Lemma lem7651148 : term319 = True.
Proof. exact (EQ_MP (@lem7651147) (@lem7651145)). Qed.
Lemma lem7651149 : term313 = True.
Proof. exact (TRANS (@lem7651144) (@lem7651148)). Qed.
Lemma lem7651150 : True = term313.
Proof. exact (SYM (@lem7651149)). Qed.
Lemma lem7651151 : term313.
Proof. exact (EQ_MP (@lem7651150) (@lem0)). Qed.
Lemma lem7651152 : term370.
Proof. exact (@lem7651141 (@lem7651151)). Qed.
Lemma lem7651154 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651155 : term175 = term176.
Proof. exact (@lem7651154 term117 term117). Qed.
Lemma lem7651156 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651157 : term178 = term117.
Proof. exact (EQ_MP (@lem7651156) (@lem940073)). Qed.
Lemma lem7651158 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651159 : term176 = term116.
Proof. exact (MK_COMB (@lem7651158) (@lem7651157)). Qed.
Lemma lem7651160 : term175 = term116.
Proof. exact (TRANS (@lem7651155) (@lem7651159)). Qed.
Lemma lem7651162 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7651163 : term206 = term211.
Proof. exact (@lem7651162 term117 term117). Qed.
Lemma lem7651164 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651165 : term178 = term117.
Proof. exact (EQ_MP (@lem7651164) (@lem940073)). Qed.
Lemma lem7651166 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651167 : term176 = term116.
Proof. exact (MK_COMB (@lem7651166) (@lem7651165)). Qed.
Lemma lem7651168 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7651169 : term211 = term166.
Proof. exact (MK_COMB (@lem7651168) (@lem7651167)). Qed.
Lemma lem7651170 : term206 = term166.
Proof. exact (TRANS (@lem7651163) (@lem7651169)). Qed.
Lemma lem7651171 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651172 : term371 = term363.
Proof. exact (MK_COMB (@lem7651171) (@lem7651170)). Qed.
Lemma lem7651173 : term372 = term365.
Proof. exact (MK_COMB (@lem7651172) (@lem7651160)). Qed.
Lemma lem7651175 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7651176 : term365 = term102.
Proof. exact (@lem7651175 term117). Qed.
Lemma lem7651177 : term372 = term102.
Proof. exact (TRANS (@lem7651173) (@lem7651176)). Qed.
Lemma lem7651178 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7651179 : term374 = term375.
Proof. exact (MK_COMB (@lem7651178) (@lem7651177)). Qed.
Lemma lem7651180 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7651181 : term376 = term324.
Proof. exact (MK_COMB (@lem7651179) (@lem7651180)). Qed.
Lemma lem7651183 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651184 : term324 = term102.
Proof. exact (@lem7651183 term117). Qed.
Lemma lem7651185 : term376 = term102.
Proof. exact (TRANS (@lem7651181) (@lem7651184)). Qed.
Lemma lem7651187 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651188 : term175 = term176.
Proof. exact (@lem7651187 term117 term117). Qed.
Lemma lem7651189 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651190 : term178 = term117.
Proof. exact (EQ_MP (@lem7651189) (@lem940073)). Qed.
Lemma lem7651191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651192 : term176 = term116.
Proof. exact (MK_COMB (@lem7651191) (@lem7651190)). Qed.
Lemma lem7651193 : term175 = term116.
Proof. exact (TRANS (@lem7651188) (@lem7651192)). Qed.
Lemma lem7651194 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7651195 : term377 = term324.
Proof. exact (MK_COMB (@lem7651194) (@lem7651193)). Qed.
Lemma lem7651197 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651198 : term324 = term102.
Proof. exact (@lem7651197 term117). Qed.
Lemma lem7651199 : term377 = term102.
Proof. exact (TRANS (@lem7651195) (@lem7651198)). Qed.
Lemma lem7651200 : term102 = term377.
Proof. exact (SYM (@lem7651199)). Qed.
Lemma lem7651201 : term376 = term377.
Proof. exact (TRANS (@lem7651185) (@lem7651200)). Qed.
Lemma lem7651202 : term366 = term163.
Proof. exact (@lem7651152 (@lem7651201)). Qed.
Lemma lem7651203 : term365 = term163.
Proof. exact (TRANS (@lem7651118) (@lem7651202)). Qed.
Lemma lem7651205 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7651206 : term163 = term102.
Proof. exact (@lem7651205 term102). Qed.
Lemma lem7651207 : term365 = term102.
Proof. exact (TRANS (@lem7651203) (@lem7651206)). Qed.
Lemma lem7651208 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7651209 : term378 = term375.
Proof. exact (MK_COMB (@lem7651208) (@lem7651207)). Qed.
Lemma lem7651210 (_98519 : int) : (real_of_int _98519) = (real_of_int _98519).
Proof. exact (eq_refl (real_of_int _98519)). Qed.
Lemma lem7651211 (_98519 : int) : (term362 _98519) = (term379 _98519).
Proof. exact (MK_COMB (@lem7651209) (@lem7651210 _98519)). Qed.
Lemma lem7651212 (_98519 : int) : (term387 _98519) = (term379 _98519).
Proof. exact (TRANS (@lem7651109 _98519) (@lem7651211 _98519)). Qed.
Lemma lem7651213 (_98519 : int) : (term379 _98519) = term102.
Proof. exact (@lem1982719 (real_of_int _98519)). Qed.
Lemma lem7651214 (_98519 : int) : (term387 _98519) = term102.
Proof. exact (TRANS (@lem7651212 _98519) (@lem7651213 _98519)). Qed.
Lemma lem7651215 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651216 (_98519 : int) : (term388 _98519) = term381.
Proof. exact (MK_COMB (@lem7651215) (@lem7651214 _98519)). Qed.
Lemma lem7651217 (_98520 : int) : (term488 _98520) = (term489 _98520).
Proof. exact (@lem1982763 (real_of_int _98520) (term193 _98520) term166). Qed.
Lemma lem7651218 (_98520 : int) : (term361 _98520) = (term362 _98520).
Proof. exact (@lem1982715 term166 (real_of_int _98520)). Qed.
Lemma lem7651220 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651221 : term116 = term205.
Proof. exact (@lem7651220 term117). Qed.
Lemma lem7651223 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7651224 : term166 = term167.
Proof. exact (@lem7651223 term117). Qed.
Lemma lem7651225 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651226 : term363 = term364.
Proof. exact (MK_COMB (@lem7651225) (@lem7651224)). Qed.
Lemma lem7651227 : term365 = term366.
Proof. exact (MK_COMB (@lem7651226) (@lem7651221)). Qed.
Lemma lem7651228 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7651230 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651231 : term313 = term319.
Proof. exact (@lem7651230 (NUMERAL 0) term117). Qed.
Lemma lem7651232 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651233 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651234 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651233 h1) (fun h1 : term319 = True => @lem7651232)). Qed.
Lemma lem7651235 : term319 = True.
Proof. exact (EQ_MP (@lem7651234) (@lem7651232)). Qed.
Lemma lem7651236 : term313 = True.
Proof. exact (TRANS (@lem7651231) (@lem7651235)). Qed.
Lemma lem7651237 : True = term313.
Proof. exact (SYM (@lem7651236)). Qed.
Lemma lem7651238 : term313.
Proof. exact (EQ_MP (@lem7651237) (@lem0)). Qed.
Lemma lem7651239 : term368.
Proof. exact (@lem7651228 (@lem7651238)). Qed.
Lemma lem7651241 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651242 : term313 = term319.
Proof. exact (@lem7651241 (NUMERAL 0) term117). Qed.
Lemma lem7651243 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651244 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651245 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651244 h1) (fun h1 : term319 = True => @lem7651243)). Qed.
Lemma lem7651246 : term319 = True.
Proof. exact (EQ_MP (@lem7651245) (@lem7651243)). Qed.
Lemma lem7651247 : term313 = True.
Proof. exact (TRANS (@lem7651242) (@lem7651246)). Qed.
Lemma lem7651248 : True = term313.
Proof. exact (SYM (@lem7651247)). Qed.
Lemma lem7651249 : term313.
Proof. exact (EQ_MP (@lem7651248) (@lem0)). Qed.
Lemma lem7651250 : term369.
Proof. exact (@lem7651239 (@lem7651249)). Qed.
Lemma lem7651252 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651253 : term313 = term319.
Proof. exact (@lem7651252 (NUMERAL 0) term117). Qed.
Lemma lem7651254 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651255 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651256 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651255 h1) (fun h1 : term319 = True => @lem7651254)). Qed.
Lemma lem7651257 : term319 = True.
Proof. exact (EQ_MP (@lem7651256) (@lem7651254)). Qed.
Lemma lem7651258 : term313 = True.
Proof. exact (TRANS (@lem7651253) (@lem7651257)). Qed.
Lemma lem7651259 : True = term313.
Proof. exact (SYM (@lem7651258)). Qed.
Lemma lem7651260 : term313.
Proof. exact (EQ_MP (@lem7651259) (@lem0)). Qed.
Lemma lem7651261 : term370.
Proof. exact (@lem7651250 (@lem7651260)). Qed.
Lemma lem7651263 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651264 : term175 = term176.
Proof. exact (@lem7651263 term117 term117). Qed.
Lemma lem7651265 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651266 : term178 = term117.
Proof. exact (EQ_MP (@lem7651265) (@lem940073)). Qed.
Lemma lem7651267 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651268 : term176 = term116.
Proof. exact (MK_COMB (@lem7651267) (@lem7651266)). Qed.
Lemma lem7651269 : term175 = term116.
Proof. exact (TRANS (@lem7651264) (@lem7651268)). Qed.
Lemma lem7651271 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7651272 : term206 = term211.
Proof. exact (@lem7651271 term117 term117). Qed.
Lemma lem7651273 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651274 : term178 = term117.
Proof. exact (EQ_MP (@lem7651273) (@lem940073)). Qed.
Lemma lem7651275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651276 : term176 = term116.
Proof. exact (MK_COMB (@lem7651275) (@lem7651274)). Qed.
Lemma lem7651277 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7651278 : term211 = term166.
Proof. exact (MK_COMB (@lem7651277) (@lem7651276)). Qed.
Lemma lem7651279 : term206 = term166.
Proof. exact (TRANS (@lem7651272) (@lem7651278)). Qed.
Lemma lem7651280 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651281 : term371 = term363.
Proof. exact (MK_COMB (@lem7651280) (@lem7651279)). Qed.
Lemma lem7651282 : term372 = term365.
Proof. exact (MK_COMB (@lem7651281) (@lem7651269)). Qed.
Lemma lem7651284 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7651285 : term365 = term102.
Proof. exact (@lem7651284 term117). Qed.
Lemma lem7651286 : term372 = term102.
Proof. exact (TRANS (@lem7651282) (@lem7651285)). Qed.
Lemma lem7651287 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7651288 : term374 = term375.
Proof. exact (MK_COMB (@lem7651287) (@lem7651286)). Qed.
Lemma lem7651289 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7651290 : term376 = term324.
Proof. exact (MK_COMB (@lem7651288) (@lem7651289)). Qed.
Lemma lem7651292 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651293 : term324 = term102.
Proof. exact (@lem7651292 term117). Qed.
Lemma lem7651294 : term376 = term102.
Proof. exact (TRANS (@lem7651290) (@lem7651293)). Qed.
Lemma lem7651296 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651297 : term175 = term176.
Proof. exact (@lem7651296 term117 term117). Qed.
Lemma lem7651298 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651299 : term178 = term117.
Proof. exact (EQ_MP (@lem7651298) (@lem940073)). Qed.
Lemma lem7651300 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651301 : term176 = term116.
Proof. exact (MK_COMB (@lem7651300) (@lem7651299)). Qed.
Lemma lem7651302 : term175 = term116.
Proof. exact (TRANS (@lem7651297) (@lem7651301)). Qed.
Lemma lem7651303 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7651304 : term377 = term324.
Proof. exact (MK_COMB (@lem7651303) (@lem7651302)). Qed.
Lemma lem7651306 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651307 : term324 = term102.
Proof. exact (@lem7651306 term117). Qed.
Lemma lem7651308 : term377 = term102.
Proof. exact (TRANS (@lem7651304) (@lem7651307)). Qed.
Lemma lem7651309 : term102 = term377.
Proof. exact (SYM (@lem7651308)). Qed.
Lemma lem7651310 : term376 = term377.
Proof. exact (TRANS (@lem7651294) (@lem7651309)). Qed.
Lemma lem7651311 : term366 = term163.
Proof. exact (@lem7651261 (@lem7651310)). Qed.
Lemma lem7651312 : term365 = term163.
Proof. exact (TRANS (@lem7651227) (@lem7651311)). Qed.
Lemma lem7651314 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7651315 : term163 = term102.
Proof. exact (@lem7651314 term102). Qed.
Lemma lem7651316 : term365 = term102.
Proof. exact (TRANS (@lem7651312) (@lem7651315)). Qed.
Lemma lem7651317 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7651318 : term378 = term375.
Proof. exact (MK_COMB (@lem7651317) (@lem7651316)). Qed.
Lemma lem7651319 (_98520 : int) : (real_of_int _98520) = (real_of_int _98520).
Proof. exact (eq_refl (real_of_int _98520)). Qed.
Lemma lem7651320 (_98520 : int) : (term362 _98520) = (term379 _98520).
Proof. exact (MK_COMB (@lem7651318) (@lem7651319 _98520)). Qed.
Lemma lem7651321 (_98520 : int) : (term361 _98520) = (term379 _98520).
Proof. exact (TRANS (@lem7651218 _98520) (@lem7651320 _98520)). Qed.
Lemma lem7651322 (_98520 : int) : (term379 _98520) = term102.
Proof. exact (@lem1982719 (real_of_int _98520)). Qed.
Lemma lem7651323 (_98520 : int) : (term361 _98520) = term102.
Proof. exact (TRANS (@lem7651321 _98520) (@lem7651322 _98520)). Qed.
Lemma lem7651324 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651325 (_98520 : int) : (term380 _98520) = term381.
Proof. exact (MK_COMB (@lem7651324) (@lem7651323 _98520)). Qed.
Lemma lem7651326 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem7651327 (_98520 : int) : (term489 _98520) = term389.
Proof. exact (MK_COMB (@lem7651325 _98520) (@lem7651326)). Qed.
Lemma lem7651328 (_98520 : int) : (term488 _98520) = term389.
Proof. exact (TRANS (@lem7651217 _98520) (@lem7651327 _98520)). Qed.
Lemma lem7651329 : term389 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem7651330 (_98520 : int) : (term488 _98520) = term166.
Proof. exact (TRANS (@lem7651328 _98520) (@lem7651329)). Qed.
Lemma lem7651331 (_98519 : int) (_98520 : int) : (term487 _98519 _98520) = term389.
Proof. exact (MK_COMB (@lem7651216 _98519) (@lem7651330 _98520)). Qed.
Lemma lem7651332 (_98519 : int) (_98520 : int) : (term486 _98519 _98520) = term389.
Proof. exact (TRANS (@lem7651108 _98519 _98520) (@lem7651331 _98519 _98520)). Qed.
Lemma lem7651333 : term389 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem7651334 (_98519 : int) (_98520 : int) : (term486 _98519 _98520) = term166.
Proof. exact (TRANS (@lem7651332 _98519 _98520) (@lem7651333)). Qed.
Lemma lem7651335 (_98518 : int) (_98519 : int) (_98520 : int) : (term485 _98518 _98519 _98520) = term389.
Proof. exact (MK_COMB (@lem7651107 _98518) (@lem7651334 _98519 _98520)). Qed.
Lemma lem7651336 (_98518 : int) (_98519 : int) (_98520 : int) : (term484 _98518 _98519 _98520) = term389.
Proof. exact (TRANS (@lem7650999 _98518 _98519 _98520) (@lem7651335 _98518 _98519 _98520)). Qed.
Lemma lem7651337 : term389 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem7651338 (_98518 : int) (_98519 : int) (_98520 : int) : (term484 _98518 _98519 _98520) = term166.
Proof. exact (TRANS (@lem7651336 _98518 _98519 _98520) (@lem7651337)). Qed.
Lemma lem7651339 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7651340 (_98518 : int) (_98519 : int) (_98520 : int) : (term490 _98518 _98519 _98520) = term391.
Proof. exact (MK_COMB (@lem7651339) (@lem7651338 _98518 _98519 _98520)). Qed.
Lemma lem7651341 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7651342 (_98518 : int) (_98519 : int) (_98520 : int) : (term483 _98518 _98519 _98520) = term392.
Proof. exact (MK_COMB (@lem7651340 _98518 _98519 _98520) (@lem7651341)). Qed.
Lemma lem7651343 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : term392.
Proof. exact (EQ_MP (@lem7651342 _98518 _98519 _98520) (@lem7650998 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651345 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7651346 : term392 = term393.
Proof. exact (@lem7651345 term102 term166). Qed.
Lemma lem7651348 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7651349 : term166 = term167.
Proof. exact (@lem7651348 term117). Qed.
Lemma lem7651351 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651352 : term102 = term163.
Proof. exact (@lem7651351 (NUMERAL 0)). Qed.
Lemma lem7651353 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7651354 : term104 = term394.
Proof. exact (MK_COMB (@lem7651353) (@lem7651352)). Qed.
Lemma lem7651355 : term393 = term395.
Proof. exact (MK_COMB (@lem7651354) (@lem7651349)). Qed.
Lemma lem7651356 : term396.
Proof. exact (@lem1980026 term102 term116 term166 term116). Qed.
Lemma lem7651358 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651359 : term313 = term319.
Proof. exact (@lem7651358 (NUMERAL 0) term117). Qed.
Lemma lem7651360 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651361 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651362 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651361 h1) (fun h1 : term319 = True => @lem7651360)). Qed.
Lemma lem7651363 : term319 = True.
Proof. exact (EQ_MP (@lem7651362) (@lem7651360)). Qed.
Lemma lem7651364 : term313 = True.
Proof. exact (TRANS (@lem7651359) (@lem7651363)). Qed.
Lemma lem7651365 : True = term313.
Proof. exact (SYM (@lem7651364)). Qed.
Lemma lem7651366 : term313.
Proof. exact (EQ_MP (@lem7651365) (@lem0)). Qed.
Lemma lem7651367 : term397.
Proof. exact (@lem7651356 (@lem7651366)). Qed.
Lemma lem7651369 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651370 : term313 = term319.
Proof. exact (@lem7651369 (NUMERAL 0) term117). Qed.
Lemma lem7651371 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651372 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651373 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651372 h1) (fun h1 : term319 = True => @lem7651371)). Qed.
Lemma lem7651374 : term319 = True.
Proof. exact (EQ_MP (@lem7651373) (@lem7651371)). Qed.
Lemma lem7651375 : term313 = True.
Proof. exact (TRANS (@lem7651370) (@lem7651374)). Qed.
Lemma lem7651376 : True = term313.
Proof. exact (SYM (@lem7651375)). Qed.
Lemma lem7651377 : term313.
Proof. exact (EQ_MP (@lem7651376) (@lem0)). Qed.
Lemma lem7651378 : term395 = term398.
Proof. exact (@lem7651367 (@lem7651377)). Qed.
Lemma lem7651380 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7651381 : term206 = term211.
Proof. exact (@lem7651380 term117 term117). Qed.
Lemma lem7651382 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651383 : term178 = term117.
Proof. exact (EQ_MP (@lem7651382) (@lem940073)). Qed.
Lemma lem7651384 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651385 : term176 = term116.
Proof. exact (MK_COMB (@lem7651384) (@lem7651383)). Qed.
Lemma lem7651386 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7651387 : term211 = term166.
Proof. exact (MK_COMB (@lem7651386) (@lem7651385)). Qed.
Lemma lem7651388 : term206 = term166.
Proof. exact (TRANS (@lem7651381) (@lem7651387)). Qed.
Lemma lem7651390 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651391 : term324 = term102.
Proof. exact (@lem7651390 term117). Qed.
Lemma lem7651392 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7651393 : term399 = term104.
Proof. exact (MK_COMB (@lem7651392) (@lem7651391)). Qed.
Lemma lem7651394 : term398 = term393.
Proof. exact (MK_COMB (@lem7651393) (@lem7651388)). Qed.
Lemma lem7651396 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7651397 : term393 = term402.
Proof. exact (@lem7651396 (NUMERAL 0) term117). Qed.
Lemma lem7651398 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651399 (h1 : term320 = (BIT1 0)) : (term117 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7651400 : (term320 = (BIT1 0)) = ((term117 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651399 h1) (fun h1 : (term117 = (NUMERAL 0)) = False => @lem7651398)). Qed.
Lemma lem7651401 : (term117 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7651400) (@lem7651398)). Qed.
Lemma lem7651402 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7651403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7651404 : term403 = (and True).
Proof. exact (MK_COMB (@lem7651403) (@lem7651402)). Qed.
Lemma lem7651405 : term402 = (True /\ False).
Proof. exact (MK_COMB (@lem7651404) (@lem7651401)). Qed.
Lemma lem7651407 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7651408 : term402 = False.
Proof. exact (TRANS (@lem7651405) (@lem7651407)). Qed.
Lemma lem7651409 : term393 = False.
Proof. exact (TRANS (@lem7651397) (@lem7651408)). Qed.
Lemma lem7651410 : term398 = False.
Proof. exact (TRANS (@lem7651394) (@lem7651409)). Qed.
Lemma lem7651411 : term395 = False.
Proof. exact (TRANS (@lem7651378) (@lem7651410)). Qed.
Lemma lem7651412 : term393 = False.
Proof. exact (TRANS (@lem7651355) (@lem7651411)). Qed.
Lemma lem7651413 : term392 = False.
Proof. exact (TRANS (@lem7651346) (@lem7651412)). Qed.
Lemma lem7651414 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term472 _98518 _98519 _98520) : False.
Proof. exact (EQ_MP (@lem7651413) (@lem7651343 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651415 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term491 _98518 _98519 _98520.
Proof. exact (h1). Qed.
Lemma lem7651416 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term303 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7651415 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651418 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term290 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7651416 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651420 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term277 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7651418 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651422 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term264 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7651420 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651423 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term221 _98518 _98520 _98519.
Proof. exact (proj1 (@lem7651420 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651424 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : (real_of_int _98519) = term102.
Proof. exact (proj2 (@lem7651423 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651426 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term249 _98518 _98519 _98520.
Proof. exact (proj2 (@lem7651422 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651427 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term226 _98518 _98520.
Proof. exact (proj1 (@lem7651422 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651429 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7651430 : term312 = term313.
Proof. exact (@lem7651429 term102 term116). Qed.
Lemma lem7651432 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651433 : term116 = term205.
Proof. exact (@lem7651432 term117). Qed.
Lemma lem7651435 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651436 : term102 = term163.
Proof. exact (@lem7651435 (NUMERAL 0)). Qed.
Lemma lem7651437 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7651438 : term314 = term315.
Proof. exact (MK_COMB (@lem7651437) (@lem7651436)). Qed.
Lemma lem7651439 : term313 = term316.
Proof. exact (MK_COMB (@lem7651438) (@lem7651433)). Qed.
Lemma lem7651440 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7651442 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651443 : term313 = term319.
Proof. exact (@lem7651442 (NUMERAL 0) term117). Qed.
Lemma lem7651444 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651445 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651446 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651445 h1) (fun h1 : term319 = True => @lem7651444)). Qed.
Lemma lem7651447 : term319 = True.
Proof. exact (EQ_MP (@lem7651446) (@lem7651444)). Qed.
Lemma lem7651448 : term313 = True.
Proof. exact (TRANS (@lem7651443) (@lem7651447)). Qed.
Lemma lem7651449 : True = term313.
Proof. exact (SYM (@lem7651448)). Qed.
Lemma lem7651450 : term313.
Proof. exact (EQ_MP (@lem7651449) (@lem0)). Qed.
Lemma lem7651451 : term321.
Proof. exact (@lem7651440 (@lem7651450)). Qed.
Lemma lem7651453 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651454 : term313 = term319.
Proof. exact (@lem7651453 (NUMERAL 0) term117). Qed.
Lemma lem7651455 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651456 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651457 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651456 h1) (fun h1 : term319 = True => @lem7651455)). Qed.
Lemma lem7651458 : term319 = True.
Proof. exact (EQ_MP (@lem7651457) (@lem7651455)). Qed.
Lemma lem7651459 : term313 = True.
Proof. exact (TRANS (@lem7651454) (@lem7651458)). Qed.
Lemma lem7651460 : True = term313.
Proof. exact (SYM (@lem7651459)). Qed.
Lemma lem7651461 : term313.
Proof. exact (EQ_MP (@lem7651460) (@lem0)). Qed.
Lemma lem7651462 : term316 = term322.
Proof. exact (@lem7651451 (@lem7651461)). Qed.
Lemma lem7651464 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651465 : term175 = term176.
Proof. exact (@lem7651464 term117 term117). Qed.
Lemma lem7651466 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651467 : term178 = term117.
Proof. exact (EQ_MP (@lem7651466) (@lem940073)). Qed.
Lemma lem7651468 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651469 : term176 = term116.
Proof. exact (MK_COMB (@lem7651468) (@lem7651467)). Qed.
Lemma lem7651470 : term175 = term116.
Proof. exact (TRANS (@lem7651465) (@lem7651469)). Qed.
Lemma lem7651472 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651473 : term324 = term102.
Proof. exact (@lem7651472 term117). Qed.
Lemma lem7651474 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7651475 : term325 = term314.
Proof. exact (MK_COMB (@lem7651474) (@lem7651473)). Qed.
Lemma lem7651476 : term322 = term313.
Proof. exact (MK_COMB (@lem7651475) (@lem7651470)). Qed.
Lemma lem7651478 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651479 : term313 = term319.
Proof. exact (@lem7651478 (NUMERAL 0) term117). Qed.
Lemma lem7651480 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651481 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651482 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651481 h1) (fun h1 : term319 = True => @lem7651480)). Qed.
Lemma lem7651483 : term319 = True.
Proof. exact (EQ_MP (@lem7651482) (@lem7651480)). Qed.
Lemma lem7651484 : term313 = True.
Proof. exact (TRANS (@lem7651479) (@lem7651483)). Qed.
Lemma lem7651485 : term322 = True.
Proof. exact (TRANS (@lem7651476) (@lem7651484)). Qed.
Lemma lem7651486 : term316 = True.
Proof. exact (TRANS (@lem7651462) (@lem7651485)). Qed.
Lemma lem7651487 : term313 = True.
Proof. exact (TRANS (@lem7651439) (@lem7651486)). Qed.
Lemma lem7651488 : term312 = True.
Proof. exact (TRANS (@lem7651430) (@lem7651487)). Qed.
Lemma lem7651489 : True = term312.
Proof. exact (SYM (@lem7651488)). Qed.
Lemma lem7651490 : term312.
Proof. exact (EQ_MP (@lem7651489) (@lem0)). Qed.
Lemma lem7651491 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term473 _98518 _98519 _98520.
Proof. exact (conj (@lem7651490) (@lem7651426 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651493 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7651494 (_98518 : int) (_98519 : int) (_98520 : int) : term474 _98518 _98519 _98520.
Proof. exact (@lem7651493 term116 (term246 _98518 _98519 _98520)). Qed.
Lemma lem7651495 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term475 _98518 _98519 _98520.
Proof. exact (@lem7651494 _98518 _98519 _98520 (@lem7651491 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651496 (_98518 : int) (_98519 : int) (_98520 : int) : (term476 _98518 _98519 _98520) = (term246 _98518 _98519 _98520).
Proof. exact (@lem1982733 (term246 _98518 _98519 _98520)). Qed.
Lemma lem7651497 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7651498 (_98518 : int) (_98519 : int) (_98520 : int) : (term477 _98518 _98519 _98520) = (term248 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7651497) (@lem7651496 _98518 _98519 _98520)). Qed.
Lemma lem7651499 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7651500 (_98518 : int) (_98519 : int) (_98520 : int) : (term475 _98518 _98519 _98520) = (term249 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7651498 _98518 _98519 _98520) (@lem7651499)). Qed.
Lemma lem7651501 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term249 _98518 _98519 _98520.
Proof. exact (EQ_MP (@lem7651500 _98518 _98519 _98520) (@lem7651495 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651503 (y : real) : term332 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7651504 (_98519 : int) : term405 _98519.
Proof. exact (@lem7651503 (real_of_int _98519)). Qed.
Lemma lem7651505 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term406 _98519.
Proof. exact (@lem7651504 _98519 (@lem7651424 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651506 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term492 _98519.
Proof. exact (@lem7651505 _98518 _98519 _98520 h1 term166). Qed.
Lemma lem7651507 (_98519 : int) : (term492 _98519) = ((term193 _98519) = term102).
Proof. exact (eq_refl (term492 _98519)). Qed.
Lemma lem7651514 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : (term193 _98519) = term102.
Proof. exact (EQ_MP (@lem7651507 _98519) (@lem7651506 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651515 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term493 _98518 _98519 _98520.
Proof. exact (conj (@lem7651514 _98518 _98519 _98520 h1) (@lem7651501 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651517 (x : real) (y : real) : term356 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem7651518 (_98518 : int) (_98519 : int) (_98520 : int) : term494 _98518 _98519 _98520.
Proof. exact (@lem7651517 (term193 _98519) (term246 _98518 _98519 _98520)). Qed.
Lemma lem7651519 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term495 _98518 _98519 _98520.
Proof. exact (@lem7651518 _98518 _98519 _98520 (@lem7651515 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651520 (_98518 : int) (_98519 : int) (_98520 : int) : (term496 _98518 _98519 _98520) = (term497 _98518 _98519 _98520).
Proof. exact (@lem1982757 (real_of_int _98518) (term193 _98519) (term215 _98519 _98520)). Qed.
Lemma lem7651521 (_98519 : int) (_98520 : int) : (term498 _98519 _98520) = (term499 _98519 _98520).
Proof. exact (@lem1982763 (term193 _98519) (real_of_int _98519) (term214 _98520)). Qed.
Lemma lem7651522 (_98519 : int) : (term387 _98519) = (term362 _98519).
Proof. exact (@lem1982713 term166 (real_of_int _98519)). Qed.
Lemma lem7651524 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651525 : term116 = term205.
Proof. exact (@lem7651524 term117). Qed.
Lemma lem7651527 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7651528 : term166 = term167.
Proof. exact (@lem7651527 term117). Qed.
Lemma lem7651529 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651530 : term363 = term364.
Proof. exact (MK_COMB (@lem7651529) (@lem7651528)). Qed.
Lemma lem7651531 : term365 = term366.
Proof. exact (MK_COMB (@lem7651530) (@lem7651525)). Qed.
Lemma lem7651532 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7651534 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651535 : term313 = term319.
Proof. exact (@lem7651534 (NUMERAL 0) term117). Qed.
Lemma lem7651536 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651537 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651538 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651537 h1) (fun h1 : term319 = True => @lem7651536)). Qed.
Lemma lem7651539 : term319 = True.
Proof. exact (EQ_MP (@lem7651538) (@lem7651536)). Qed.
Lemma lem7651540 : term313 = True.
Proof. exact (TRANS (@lem7651535) (@lem7651539)). Qed.
Lemma lem7651541 : True = term313.
Proof. exact (SYM (@lem7651540)). Qed.
Lemma lem7651542 : term313.
Proof. exact (EQ_MP (@lem7651541) (@lem0)). Qed.
Lemma lem7651543 : term368.
Proof. exact (@lem7651532 (@lem7651542)). Qed.
Lemma lem7651545 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651546 : term313 = term319.
Proof. exact (@lem7651545 (NUMERAL 0) term117). Qed.
Lemma lem7651547 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651548 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651549 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651548 h1) (fun h1 : term319 = True => @lem7651547)). Qed.
Lemma lem7651550 : term319 = True.
Proof. exact (EQ_MP (@lem7651549) (@lem7651547)). Qed.
Lemma lem7651551 : term313 = True.
Proof. exact (TRANS (@lem7651546) (@lem7651550)). Qed.
Lemma lem7651552 : True = term313.
Proof. exact (SYM (@lem7651551)). Qed.
Lemma lem7651553 : term313.
Proof. exact (EQ_MP (@lem7651552) (@lem0)). Qed.
Lemma lem7651554 : term369.
Proof. exact (@lem7651543 (@lem7651553)). Qed.
Lemma lem7651556 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651557 : term313 = term319.
Proof. exact (@lem7651556 (NUMERAL 0) term117). Qed.
Lemma lem7651558 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651559 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651560 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651559 h1) (fun h1 : term319 = True => @lem7651558)). Qed.
Lemma lem7651561 : term319 = True.
Proof. exact (EQ_MP (@lem7651560) (@lem7651558)). Qed.
Lemma lem7651562 : term313 = True.
Proof. exact (TRANS (@lem7651557) (@lem7651561)). Qed.
Lemma lem7651563 : True = term313.
Proof. exact (SYM (@lem7651562)). Qed.
Lemma lem7651564 : term313.
Proof. exact (EQ_MP (@lem7651563) (@lem0)). Qed.
Lemma lem7651565 : term370.
Proof. exact (@lem7651554 (@lem7651564)). Qed.
Lemma lem7651567 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651568 : term175 = term176.
Proof. exact (@lem7651567 term117 term117). Qed.
Lemma lem7651569 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651570 : term178 = term117.
Proof. exact (EQ_MP (@lem7651569) (@lem940073)). Qed.
Lemma lem7651571 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651572 : term176 = term116.
Proof. exact (MK_COMB (@lem7651571) (@lem7651570)). Qed.
Lemma lem7651573 : term175 = term116.
Proof. exact (TRANS (@lem7651568) (@lem7651572)). Qed.
Lemma lem7651575 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7651576 : term206 = term211.
Proof. exact (@lem7651575 term117 term117). Qed.
Lemma lem7651577 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651578 : term178 = term117.
Proof. exact (EQ_MP (@lem7651577) (@lem940073)). Qed.
Lemma lem7651579 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651580 : term176 = term116.
Proof. exact (MK_COMB (@lem7651579) (@lem7651578)). Qed.
Lemma lem7651581 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7651582 : term211 = term166.
Proof. exact (MK_COMB (@lem7651581) (@lem7651580)). Qed.
Lemma lem7651583 : term206 = term166.
Proof. exact (TRANS (@lem7651576) (@lem7651582)). Qed.
Lemma lem7651584 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651585 : term371 = term363.
Proof. exact (MK_COMB (@lem7651584) (@lem7651583)). Qed.
Lemma lem7651586 : term372 = term365.
Proof. exact (MK_COMB (@lem7651585) (@lem7651573)). Qed.
Lemma lem7651588 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7651589 : term365 = term102.
Proof. exact (@lem7651588 term117). Qed.
Lemma lem7651590 : term372 = term102.
Proof. exact (TRANS (@lem7651586) (@lem7651589)). Qed.
Lemma lem7651591 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7651592 : term374 = term375.
Proof. exact (MK_COMB (@lem7651591) (@lem7651590)). Qed.
Lemma lem7651593 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7651594 : term376 = term324.
Proof. exact (MK_COMB (@lem7651592) (@lem7651593)). Qed.
Lemma lem7651596 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651597 : term324 = term102.
Proof. exact (@lem7651596 term117). Qed.
Lemma lem7651598 : term376 = term102.
Proof. exact (TRANS (@lem7651594) (@lem7651597)). Qed.
Lemma lem7651600 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651601 : term175 = term176.
Proof. exact (@lem7651600 term117 term117). Qed.
Lemma lem7651602 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651603 : term178 = term117.
Proof. exact (EQ_MP (@lem7651602) (@lem940073)). Qed.
Lemma lem7651604 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651605 : term176 = term116.
Proof. exact (MK_COMB (@lem7651604) (@lem7651603)). Qed.
Lemma lem7651606 : term175 = term116.
Proof. exact (TRANS (@lem7651601) (@lem7651605)). Qed.
Lemma lem7651607 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7651608 : term377 = term324.
Proof. exact (MK_COMB (@lem7651607) (@lem7651606)). Qed.
Lemma lem7651610 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651611 : term324 = term102.
Proof. exact (@lem7651610 term117). Qed.
Lemma lem7651612 : term377 = term102.
Proof. exact (TRANS (@lem7651608) (@lem7651611)). Qed.
Lemma lem7651613 : term102 = term377.
Proof. exact (SYM (@lem7651612)). Qed.
Lemma lem7651614 : term376 = term377.
Proof. exact (TRANS (@lem7651598) (@lem7651613)). Qed.
Lemma lem7651615 : term366 = term163.
Proof. exact (@lem7651565 (@lem7651614)). Qed.
Lemma lem7651616 : term365 = term163.
Proof. exact (TRANS (@lem7651531) (@lem7651615)). Qed.
Lemma lem7651618 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7651619 : term163 = term102.
Proof. exact (@lem7651618 term102). Qed.
Lemma lem7651620 : term365 = term102.
Proof. exact (TRANS (@lem7651616) (@lem7651619)). Qed.
Lemma lem7651621 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7651622 : term378 = term375.
Proof. exact (MK_COMB (@lem7651621) (@lem7651620)). Qed.
Lemma lem7651623 (_98519 : int) : (real_of_int _98519) = (real_of_int _98519).
Proof. exact (eq_refl (real_of_int _98519)). Qed.
Lemma lem7651624 (_98519 : int) : (term362 _98519) = (term379 _98519).
Proof. exact (MK_COMB (@lem7651622) (@lem7651623 _98519)). Qed.
Lemma lem7651625 (_98519 : int) : (term387 _98519) = (term379 _98519).
Proof. exact (TRANS (@lem7651522 _98519) (@lem7651624 _98519)). Qed.
Lemma lem7651626 (_98519 : int) : (term379 _98519) = term102.
Proof. exact (@lem1982719 (real_of_int _98519)). Qed.
Lemma lem7651627 (_98519 : int) : (term387 _98519) = term102.
Proof. exact (TRANS (@lem7651625 _98519) (@lem7651626 _98519)). Qed.
Lemma lem7651628 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651629 (_98519 : int) : (term388 _98519) = term381.
Proof. exact (MK_COMB (@lem7651628) (@lem7651627 _98519)). Qed.
Lemma lem7651630 (_98520 : int) : (term214 _98520) = (term214 _98520).
Proof. exact (eq_refl (term214 _98520)). Qed.
Lemma lem7651631 (_98519 : int) (_98520 : int) : (term499 _98519 _98520) = (term500 _98520).
Proof. exact (MK_COMB (@lem7651629 _98519) (@lem7651630 _98520)). Qed.
Lemma lem7651632 (_98519 : int) (_98520 : int) : (term498 _98519 _98520) = (term500 _98520).
Proof. exact (TRANS (@lem7651521 _98519 _98520) (@lem7651631 _98519 _98520)). Qed.
Lemma lem7651633 (_98520 : int) : (term500 _98520) = (term214 _98520).
Proof. exact (@lem1982721 (term214 _98520)). Qed.
Lemma lem7651634 (_98519 : int) (_98520 : int) : (term498 _98519 _98520) = (term214 _98520).
Proof. exact (TRANS (@lem7651632 _98519 _98520) (@lem7651633 _98520)). Qed.
Lemma lem7651635 (_98518 : int) : (term118 _98518) = (term118 _98518).
Proof. exact (eq_refl (term118 _98518)). Qed.
Lemma lem7651636 (_98519 : int) (_98518 : int) (_98520 : int) : (term497 _98518 _98519 _98520) = (term215 _98518 _98520).
Proof. exact (MK_COMB (@lem7651635 _98518) (@lem7651634 _98519 _98520)). Qed.
Lemma lem7651637 (_98519 : int) (_98518 : int) (_98520 : int) : (term496 _98518 _98519 _98520) = (term215 _98518 _98520).
Proof. exact (TRANS (@lem7651520 _98518 _98519 _98520) (@lem7651636 _98519 _98518 _98520)). Qed.
Lemma lem7651638 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7651639 (_98519 : int) (_98518 : int) (_98520 : int) : (term501 _98518 _98519 _98520) = (term217 _98518 _98520).
Proof. exact (MK_COMB (@lem7651638) (@lem7651637 _98519 _98518 _98520)). Qed.
Lemma lem7651640 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7651641 (_98519 : int) (_98518 : int) (_98520 : int) : (term495 _98518 _98519 _98520) = (term218 _98518 _98520).
Proof. exact (MK_COMB (@lem7651639 _98519 _98518 _98520) (@lem7651640)). Qed.
Lemma lem7651642 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term218 _98518 _98520.
Proof. exact (EQ_MP (@lem7651641 _98519 _98518 _98520) (@lem7651519 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651644 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7651645 : term312 = term313.
Proof. exact (@lem7651644 term102 term116). Qed.
Lemma lem7651647 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651648 : term116 = term205.
Proof. exact (@lem7651647 term117). Qed.
Lemma lem7651650 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651651 : term102 = term163.
Proof. exact (@lem7651650 (NUMERAL 0)). Qed.
Lemma lem7651652 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7651653 : term314 = term315.
Proof. exact (MK_COMB (@lem7651652) (@lem7651651)). Qed.
Lemma lem7651654 : term313 = term316.
Proof. exact (MK_COMB (@lem7651653) (@lem7651648)). Qed.
Lemma lem7651655 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7651657 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651658 : term313 = term319.
Proof. exact (@lem7651657 (NUMERAL 0) term117). Qed.
Lemma lem7651659 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651660 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651661 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651660 h1) (fun h1 : term319 = True => @lem7651659)). Qed.
Lemma lem7651662 : term319 = True.
Proof. exact (EQ_MP (@lem7651661) (@lem7651659)). Qed.
Lemma lem7651663 : term313 = True.
Proof. exact (TRANS (@lem7651658) (@lem7651662)). Qed.
Lemma lem7651664 : True = term313.
Proof. exact (SYM (@lem7651663)). Qed.
Lemma lem7651665 : term313.
Proof. exact (EQ_MP (@lem7651664) (@lem0)). Qed.
Lemma lem7651666 : term321.
Proof. exact (@lem7651655 (@lem7651665)). Qed.
Lemma lem7651668 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651669 : term313 = term319.
Proof. exact (@lem7651668 (NUMERAL 0) term117). Qed.
Lemma lem7651670 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651671 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651672 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651671 h1) (fun h1 : term319 = True => @lem7651670)). Qed.
Lemma lem7651673 : term319 = True.
Proof. exact (EQ_MP (@lem7651672) (@lem7651670)). Qed.
Lemma lem7651674 : term313 = True.
Proof. exact (TRANS (@lem7651669) (@lem7651673)). Qed.
Lemma lem7651675 : True = term313.
Proof. exact (SYM (@lem7651674)). Qed.
Lemma lem7651676 : term313.
Proof. exact (EQ_MP (@lem7651675) (@lem0)). Qed.
Lemma lem7651677 : term316 = term322.
Proof. exact (@lem7651666 (@lem7651676)). Qed.
Lemma lem7651679 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651680 : term175 = term176.
Proof. exact (@lem7651679 term117 term117). Qed.
Lemma lem7651681 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651682 : term178 = term117.
Proof. exact (EQ_MP (@lem7651681) (@lem940073)). Qed.
Lemma lem7651683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651684 : term176 = term116.
Proof. exact (MK_COMB (@lem7651683) (@lem7651682)). Qed.
Lemma lem7651685 : term175 = term116.
Proof. exact (TRANS (@lem7651680) (@lem7651684)). Qed.
Lemma lem7651687 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651688 : term324 = term102.
Proof. exact (@lem7651687 term117). Qed.
Lemma lem7651689 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7651690 : term325 = term314.
Proof. exact (MK_COMB (@lem7651689) (@lem7651688)). Qed.
Lemma lem7651691 : term322 = term313.
Proof. exact (MK_COMB (@lem7651690) (@lem7651685)). Qed.
Lemma lem7651693 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651694 : term313 = term319.
Proof. exact (@lem7651693 (NUMERAL 0) term117). Qed.
Lemma lem7651695 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651696 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651697 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651696 h1) (fun h1 : term319 = True => @lem7651695)). Qed.
Lemma lem7651698 : term319 = True.
Proof. exact (EQ_MP (@lem7651697) (@lem7651695)). Qed.
Lemma lem7651699 : term313 = True.
Proof. exact (TRANS (@lem7651694) (@lem7651698)). Qed.
Lemma lem7651700 : term322 = True.
Proof. exact (TRANS (@lem7651691) (@lem7651699)). Qed.
Lemma lem7651701 : term316 = True.
Proof. exact (TRANS (@lem7651677) (@lem7651700)). Qed.
Lemma lem7651702 : term313 = True.
Proof. exact (TRANS (@lem7651654) (@lem7651701)). Qed.
Lemma lem7651703 : term312 = True.
Proof. exact (TRANS (@lem7651645) (@lem7651702)). Qed.
Lemma lem7651704 : True = term312.
Proof. exact (SYM (@lem7651703)). Qed.
Lemma lem7651705 : term312.
Proof. exact (EQ_MP (@lem7651704) (@lem0)). Qed.
Lemma lem7651706 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term423 _98518 _98520.
Proof. exact (conj (@lem7651705) (@lem7651642 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651708 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7651709 (_98518 : int) (_98520 : int) : term424 _98518 _98520.
Proof. exact (@lem7651708 term116 (term215 _98518 _98520)). Qed.
Lemma lem7651710 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term425 _98518 _98520.
Proof. exact (@lem7651709 _98518 _98520 (@lem7651706 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651711 (_98518 : int) (_98520 : int) : (term426 _98518 _98520) = (term215 _98518 _98520).
Proof. exact (@lem1982733 (term215 _98518 _98520)). Qed.
Lemma lem7651712 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7651713 (_98518 : int) (_98520 : int) : (term427 _98518 _98520) = (term217 _98518 _98520).
Proof. exact (MK_COMB (@lem7651712) (@lem7651711 _98518 _98520)). Qed.
Lemma lem7651714 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7651715 (_98518 : int) (_98520 : int) : (term425 _98518 _98520) = (term218 _98518 _98520).
Proof. exact (MK_COMB (@lem7651713 _98518 _98520) (@lem7651714)). Qed.
Lemma lem7651716 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term218 _98518 _98520.
Proof. exact (EQ_MP (@lem7651715 _98518 _98520) (@lem7651710 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651718 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7651719 : term312 = term313.
Proof. exact (@lem7651718 term102 term116). Qed.
Lemma lem7651721 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651722 : term116 = term205.
Proof. exact (@lem7651721 term117). Qed.
Lemma lem7651724 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651725 : term102 = term163.
Proof. exact (@lem7651724 (NUMERAL 0)). Qed.
Lemma lem7651726 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7651727 : term314 = term315.
Proof. exact (MK_COMB (@lem7651726) (@lem7651725)). Qed.
Lemma lem7651728 : term313 = term316.
Proof. exact (MK_COMB (@lem7651727) (@lem7651722)). Qed.
Lemma lem7651729 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7651731 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651732 : term313 = term319.
Proof. exact (@lem7651731 (NUMERAL 0) term117). Qed.
Lemma lem7651733 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651734 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651735 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651734 h1) (fun h1 : term319 = True => @lem7651733)). Qed.
Lemma lem7651736 : term319 = True.
Proof. exact (EQ_MP (@lem7651735) (@lem7651733)). Qed.
Lemma lem7651737 : term313 = True.
Proof. exact (TRANS (@lem7651732) (@lem7651736)). Qed.
Lemma lem7651738 : True = term313.
Proof. exact (SYM (@lem7651737)). Qed.
Lemma lem7651739 : term313.
Proof. exact (EQ_MP (@lem7651738) (@lem0)). Qed.
Lemma lem7651740 : term321.
Proof. exact (@lem7651729 (@lem7651739)). Qed.
Lemma lem7651742 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651743 : term313 = term319.
Proof. exact (@lem7651742 (NUMERAL 0) term117). Qed.
Lemma lem7651744 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651745 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651746 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651745 h1) (fun h1 : term319 = True => @lem7651744)). Qed.
Lemma lem7651747 : term319 = True.
Proof. exact (EQ_MP (@lem7651746) (@lem7651744)). Qed.
Lemma lem7651748 : term313 = True.
Proof. exact (TRANS (@lem7651743) (@lem7651747)). Qed.
Lemma lem7651749 : True = term313.
Proof. exact (SYM (@lem7651748)). Qed.
Lemma lem7651750 : term313.
Proof. exact (EQ_MP (@lem7651749) (@lem0)). Qed.
Lemma lem7651751 : term316 = term322.
Proof. exact (@lem7651740 (@lem7651750)). Qed.
Lemma lem7651753 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651754 : term175 = term176.
Proof. exact (@lem7651753 term117 term117). Qed.
Lemma lem7651755 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651756 : term178 = term117.
Proof. exact (EQ_MP (@lem7651755) (@lem940073)). Qed.
Lemma lem7651757 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651758 : term176 = term116.
Proof. exact (MK_COMB (@lem7651757) (@lem7651756)). Qed.
Lemma lem7651759 : term175 = term116.
Proof. exact (TRANS (@lem7651754) (@lem7651758)). Qed.
Lemma lem7651761 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651762 : term324 = term102.
Proof. exact (@lem7651761 term117). Qed.
Lemma lem7651763 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7651764 : term325 = term314.
Proof. exact (MK_COMB (@lem7651763) (@lem7651762)). Qed.
Lemma lem7651765 : term322 = term313.
Proof. exact (MK_COMB (@lem7651764) (@lem7651759)). Qed.
Lemma lem7651767 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651768 : term313 = term319.
Proof. exact (@lem7651767 (NUMERAL 0) term117). Qed.
Lemma lem7651769 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651770 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651771 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651770 h1) (fun h1 : term319 = True => @lem7651769)). Qed.
Lemma lem7651772 : term319 = True.
Proof. exact (EQ_MP (@lem7651771) (@lem7651769)). Qed.
Lemma lem7651773 : term313 = True.
Proof. exact (TRANS (@lem7651768) (@lem7651772)). Qed.
Lemma lem7651774 : term322 = True.
Proof. exact (TRANS (@lem7651765) (@lem7651773)). Qed.
Lemma lem7651775 : term316 = True.
Proof. exact (TRANS (@lem7651751) (@lem7651774)). Qed.
Lemma lem7651776 : term313 = True.
Proof. exact (TRANS (@lem7651728) (@lem7651775)). Qed.
Lemma lem7651777 : term312 = True.
Proof. exact (TRANS (@lem7651719) (@lem7651776)). Qed.
Lemma lem7651778 : True = term312.
Proof. exact (SYM (@lem7651777)). Qed.
Lemma lem7651779 : term312.
Proof. exact (EQ_MP (@lem7651778) (@lem0)). Qed.
Lemma lem7651780 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term418 _98518 _98520.
Proof. exact (conj (@lem7651779) (@lem7651427 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651782 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7651783 (_98518 : int) (_98520 : int) : term419 _98518 _98520.
Proof. exact (@lem7651782 term116 (term224 _98518 _98520)). Qed.
Lemma lem7651784 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term420 _98518 _98520.
Proof. exact (@lem7651783 _98518 _98520 (@lem7651780 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651785 (_98518 : int) (_98520 : int) : (term421 _98518 _98520) = (term224 _98518 _98520).
Proof. exact (@lem1982733 (term224 _98518 _98520)). Qed.
Lemma lem7651786 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7651787 (_98518 : int) (_98520 : int) : (term422 _98518 _98520) = (term225 _98518 _98520).
Proof. exact (MK_COMB (@lem7651786) (@lem7651785 _98518 _98520)). Qed.
Lemma lem7651788 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7651789 (_98518 : int) (_98520 : int) : (term420 _98518 _98520) = (term226 _98518 _98520).
Proof. exact (MK_COMB (@lem7651787 _98518 _98520) (@lem7651788)). Qed.
Lemma lem7651790 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term226 _98518 _98520.
Proof. exact (EQ_MP (@lem7651789 _98518 _98520) (@lem7651784 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651791 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term502 _98518 _98520.
Proof. exact (conj (@lem7651790 _98518 _98519 _98520 h1) (@lem7651716 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651793 (x : real) (y : real) : term429 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7651794 (_98518 : int) (_98520 : int) : term503 _98518 _98520.
Proof. exact (@lem7651793 (term224 _98518 _98520) (term215 _98518 _98520)). Qed.
Lemma lem7651795 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term504 _98518 _98520.
Proof. exact (@lem7651794 _98518 _98520 (@lem7651791 _98518 _98519 _98520 h1)). Qed.
Lemma lem7651796 (_98518 : int) (_98520 : int) : (term505 _98518 _98520) = (term506 _98518 _98520).
Proof. exact (@lem1982753 (term193 _98518) (real_of_int _98518) (term384 _98520) (term214 _98520)). Qed.
Lemma lem7651797 (_98518 : int) : (term387 _98518) = (term362 _98518).
Proof. exact (@lem1982713 term166 (real_of_int _98518)). Qed.
Lemma lem7651799 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651800 : term116 = term205.
Proof. exact (@lem7651799 term117). Qed.
Lemma lem7651802 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7651803 : term166 = term167.
Proof. exact (@lem7651802 term117). Qed.
Lemma lem7651804 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651805 : term363 = term364.
Proof. exact (MK_COMB (@lem7651804) (@lem7651803)). Qed.
Lemma lem7651806 : term365 = term366.
Proof. exact (MK_COMB (@lem7651805) (@lem7651800)). Qed.
Lemma lem7651807 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7651809 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651810 : term313 = term319.
Proof. exact (@lem7651809 (NUMERAL 0) term117). Qed.
Lemma lem7651811 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651812 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651813 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651812 h1) (fun h1 : term319 = True => @lem7651811)). Qed.
Lemma lem7651814 : term319 = True.
Proof. exact (EQ_MP (@lem7651813) (@lem7651811)). Qed.
Lemma lem7651815 : term313 = True.
Proof. exact (TRANS (@lem7651810) (@lem7651814)). Qed.
Lemma lem7651816 : True = term313.
Proof. exact (SYM (@lem7651815)). Qed.
Lemma lem7651817 : term313.
Proof. exact (EQ_MP (@lem7651816) (@lem0)). Qed.
Lemma lem7651818 : term368.
Proof. exact (@lem7651807 (@lem7651817)). Qed.
Lemma lem7651820 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651821 : term313 = term319.
Proof. exact (@lem7651820 (NUMERAL 0) term117). Qed.
Lemma lem7651822 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651823 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651824 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651823 h1) (fun h1 : term319 = True => @lem7651822)). Qed.
Lemma lem7651825 : term319 = True.
Proof. exact (EQ_MP (@lem7651824) (@lem7651822)). Qed.
Lemma lem7651826 : term313 = True.
Proof. exact (TRANS (@lem7651821) (@lem7651825)). Qed.
Lemma lem7651827 : True = term313.
Proof. exact (SYM (@lem7651826)). Qed.
Lemma lem7651828 : term313.
Proof. exact (EQ_MP (@lem7651827) (@lem0)). Qed.
Lemma lem7651829 : term369.
Proof. exact (@lem7651818 (@lem7651828)). Qed.
Lemma lem7651831 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651832 : term313 = term319.
Proof. exact (@lem7651831 (NUMERAL 0) term117). Qed.
Lemma lem7651833 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651834 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651835 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651834 h1) (fun h1 : term319 = True => @lem7651833)). Qed.
Lemma lem7651836 : term319 = True.
Proof. exact (EQ_MP (@lem7651835) (@lem7651833)). Qed.
Lemma lem7651837 : term313 = True.
Proof. exact (TRANS (@lem7651832) (@lem7651836)). Qed.
Lemma lem7651838 : True = term313.
Proof. exact (SYM (@lem7651837)). Qed.
Lemma lem7651839 : term313.
Proof. exact (EQ_MP (@lem7651838) (@lem0)). Qed.
Lemma lem7651840 : term370.
Proof. exact (@lem7651829 (@lem7651839)). Qed.
Lemma lem7651842 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651843 : term175 = term176.
Proof. exact (@lem7651842 term117 term117). Qed.
Lemma lem7651844 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651845 : term178 = term117.
Proof. exact (EQ_MP (@lem7651844) (@lem940073)). Qed.
Lemma lem7651846 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651847 : term176 = term116.
Proof. exact (MK_COMB (@lem7651846) (@lem7651845)). Qed.
Lemma lem7651848 : term175 = term116.
Proof. exact (TRANS (@lem7651843) (@lem7651847)). Qed.
Lemma lem7651850 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7651851 : term206 = term211.
Proof. exact (@lem7651850 term117 term117). Qed.
Lemma lem7651852 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651853 : term178 = term117.
Proof. exact (EQ_MP (@lem7651852) (@lem940073)). Qed.
Lemma lem7651854 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651855 : term176 = term116.
Proof. exact (MK_COMB (@lem7651854) (@lem7651853)). Qed.
Lemma lem7651856 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7651857 : term211 = term166.
Proof. exact (MK_COMB (@lem7651856) (@lem7651855)). Qed.
Lemma lem7651858 : term206 = term166.
Proof. exact (TRANS (@lem7651851) (@lem7651857)). Qed.
Lemma lem7651859 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651860 : term371 = term363.
Proof. exact (MK_COMB (@lem7651859) (@lem7651858)). Qed.
Lemma lem7651861 : term372 = term365.
Proof. exact (MK_COMB (@lem7651860) (@lem7651848)). Qed.
Lemma lem7651863 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7651864 : term365 = term102.
Proof. exact (@lem7651863 term117). Qed.
Lemma lem7651865 : term372 = term102.
Proof. exact (TRANS (@lem7651861) (@lem7651864)). Qed.
Lemma lem7651866 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7651867 : term374 = term375.
Proof. exact (MK_COMB (@lem7651866) (@lem7651865)). Qed.
Lemma lem7651868 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7651869 : term376 = term324.
Proof. exact (MK_COMB (@lem7651867) (@lem7651868)). Qed.
Lemma lem7651871 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651872 : term324 = term102.
Proof. exact (@lem7651871 term117). Qed.
Lemma lem7651873 : term376 = term102.
Proof. exact (TRANS (@lem7651869) (@lem7651872)). Qed.
Lemma lem7651875 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651876 : term175 = term176.
Proof. exact (@lem7651875 term117 term117). Qed.
Lemma lem7651877 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651878 : term178 = term117.
Proof. exact (EQ_MP (@lem7651877) (@lem940073)). Qed.
Lemma lem7651879 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651880 : term176 = term116.
Proof. exact (MK_COMB (@lem7651879) (@lem7651878)). Qed.
Lemma lem7651881 : term175 = term116.
Proof. exact (TRANS (@lem7651876) (@lem7651880)). Qed.
Lemma lem7651882 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7651883 : term377 = term324.
Proof. exact (MK_COMB (@lem7651882) (@lem7651881)). Qed.
Lemma lem7651885 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651886 : term324 = term102.
Proof. exact (@lem7651885 term117). Qed.
Lemma lem7651887 : term377 = term102.
Proof. exact (TRANS (@lem7651883) (@lem7651886)). Qed.
Lemma lem7651888 : term102 = term377.
Proof. exact (SYM (@lem7651887)). Qed.
Lemma lem7651889 : term376 = term377.
Proof. exact (TRANS (@lem7651873) (@lem7651888)). Qed.
Lemma lem7651890 : term366 = term163.
Proof. exact (@lem7651840 (@lem7651889)). Qed.
Lemma lem7651891 : term365 = term163.
Proof. exact (TRANS (@lem7651806) (@lem7651890)). Qed.
Lemma lem7651893 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7651894 : term163 = term102.
Proof. exact (@lem7651893 term102). Qed.
Lemma lem7651895 : term365 = term102.
Proof. exact (TRANS (@lem7651891) (@lem7651894)). Qed.
Lemma lem7651896 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7651897 : term378 = term375.
Proof. exact (MK_COMB (@lem7651896) (@lem7651895)). Qed.
Lemma lem7651898 (_98518 : int) : (real_of_int _98518) = (real_of_int _98518).
Proof. exact (eq_refl (real_of_int _98518)). Qed.
Lemma lem7651899 (_98518 : int) : (term362 _98518) = (term379 _98518).
Proof. exact (MK_COMB (@lem7651897) (@lem7651898 _98518)). Qed.
Lemma lem7651900 (_98518 : int) : (term387 _98518) = (term379 _98518).
Proof. exact (TRANS (@lem7651797 _98518) (@lem7651899 _98518)). Qed.
Lemma lem7651901 (_98518 : int) : (term379 _98518) = term102.
Proof. exact (@lem1982719 (real_of_int _98518)). Qed.
Lemma lem7651902 (_98518 : int) : (term387 _98518) = term102.
Proof. exact (TRANS (@lem7651900 _98518) (@lem7651901 _98518)). Qed.
Lemma lem7651903 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651904 (_98518 : int) : (term388 _98518) = term381.
Proof. exact (MK_COMB (@lem7651903) (@lem7651902 _98518)). Qed.
Lemma lem7651905 (_98520 : int) : (term507 _98520) = (term508 _98520).
Proof. exact (@lem1982753 (real_of_int _98520) (term193 _98520) term166 term166). Qed.
Lemma lem7651906 (_98520 : int) : (term361 _98520) = (term362 _98520).
Proof. exact (@lem1982715 term166 (real_of_int _98520)). Qed.
Lemma lem7651908 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7651909 : term116 = term205.
Proof. exact (@lem7651908 term117). Qed.
Lemma lem7651911 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7651912 : term166 = term167.
Proof. exact (@lem7651911 term117). Qed.
Lemma lem7651913 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651914 : term363 = term364.
Proof. exact (MK_COMB (@lem7651913) (@lem7651912)). Qed.
Lemma lem7651915 : term365 = term366.
Proof. exact (MK_COMB (@lem7651914) (@lem7651909)). Qed.
Lemma lem7651916 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7651918 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651919 : term313 = term319.
Proof. exact (@lem7651918 (NUMERAL 0) term117). Qed.
Lemma lem7651920 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651921 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651922 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651921 h1) (fun h1 : term319 = True => @lem7651920)). Qed.
Lemma lem7651923 : term319 = True.
Proof. exact (EQ_MP (@lem7651922) (@lem7651920)). Qed.
Lemma lem7651924 : term313 = True.
Proof. exact (TRANS (@lem7651919) (@lem7651923)). Qed.
Lemma lem7651925 : True = term313.
Proof. exact (SYM (@lem7651924)). Qed.
Lemma lem7651926 : term313.
Proof. exact (EQ_MP (@lem7651925) (@lem0)). Qed.
Lemma lem7651927 : term368.
Proof. exact (@lem7651916 (@lem7651926)). Qed.
Lemma lem7651929 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651930 : term313 = term319.
Proof. exact (@lem7651929 (NUMERAL 0) term117). Qed.
Lemma lem7651931 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651932 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651933 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651932 h1) (fun h1 : term319 = True => @lem7651931)). Qed.
Lemma lem7651934 : term319 = True.
Proof. exact (EQ_MP (@lem7651933) (@lem7651931)). Qed.
Lemma lem7651935 : term313 = True.
Proof. exact (TRANS (@lem7651930) (@lem7651934)). Qed.
Lemma lem7651936 : True = term313.
Proof. exact (SYM (@lem7651935)). Qed.
Lemma lem7651937 : term313.
Proof. exact (EQ_MP (@lem7651936) (@lem0)). Qed.
Lemma lem7651938 : term369.
Proof. exact (@lem7651927 (@lem7651937)). Qed.
Lemma lem7651940 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7651941 : term313 = term319.
Proof. exact (@lem7651940 (NUMERAL 0) term117). Qed.
Lemma lem7651942 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7651943 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7651944 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7651943 h1) (fun h1 : term319 = True => @lem7651942)). Qed.
Lemma lem7651945 : term319 = True.
Proof. exact (EQ_MP (@lem7651944) (@lem7651942)). Qed.
Lemma lem7651946 : term313 = True.
Proof. exact (TRANS (@lem7651941) (@lem7651945)). Qed.
Lemma lem7651947 : True = term313.
Proof. exact (SYM (@lem7651946)). Qed.
Lemma lem7651948 : term313.
Proof. exact (EQ_MP (@lem7651947) (@lem0)). Qed.
Lemma lem7651949 : term370.
Proof. exact (@lem7651938 (@lem7651948)). Qed.
Lemma lem7651951 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651952 : term175 = term176.
Proof. exact (@lem7651951 term117 term117). Qed.
Lemma lem7651953 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651954 : term178 = term117.
Proof. exact (EQ_MP (@lem7651953) (@lem940073)). Qed.
Lemma lem7651955 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651956 : term176 = term116.
Proof. exact (MK_COMB (@lem7651955) (@lem7651954)). Qed.
Lemma lem7651957 : term175 = term116.
Proof. exact (TRANS (@lem7651952) (@lem7651956)). Qed.
Lemma lem7651959 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7651960 : term206 = term211.
Proof. exact (@lem7651959 term117 term117). Qed.
Lemma lem7651961 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651962 : term178 = term117.
Proof. exact (EQ_MP (@lem7651961) (@lem940073)). Qed.
Lemma lem7651963 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651964 : term176 = term116.
Proof. exact (MK_COMB (@lem7651963) (@lem7651962)). Qed.
Lemma lem7651965 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7651966 : term211 = term166.
Proof. exact (MK_COMB (@lem7651965) (@lem7651964)). Qed.
Lemma lem7651967 : term206 = term166.
Proof. exact (TRANS (@lem7651960) (@lem7651966)). Qed.
Lemma lem7651968 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7651969 : term371 = term363.
Proof. exact (MK_COMB (@lem7651968) (@lem7651967)). Qed.
Lemma lem7651970 : term372 = term365.
Proof. exact (MK_COMB (@lem7651969) (@lem7651957)). Qed.
Lemma lem7651972 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7651973 : term365 = term102.
Proof. exact (@lem7651972 term117). Qed.
Lemma lem7651974 : term372 = term102.
Proof. exact (TRANS (@lem7651970) (@lem7651973)). Qed.
Lemma lem7651975 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7651976 : term374 = term375.
Proof. exact (MK_COMB (@lem7651975) (@lem7651974)). Qed.
Lemma lem7651977 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7651978 : term376 = term324.
Proof. exact (MK_COMB (@lem7651976) (@lem7651977)). Qed.
Lemma lem7651980 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651981 : term324 = term102.
Proof. exact (@lem7651980 term117). Qed.
Lemma lem7651982 : term376 = term102.
Proof. exact (TRANS (@lem7651978) (@lem7651981)). Qed.
Lemma lem7651984 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7651985 : term175 = term176.
Proof. exact (@lem7651984 term117 term117). Qed.
Lemma lem7651986 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7651987 : term178 = term117.
Proof. exact (EQ_MP (@lem7651986) (@lem940073)). Qed.
Lemma lem7651988 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7651989 : term176 = term116.
Proof. exact (MK_COMB (@lem7651988) (@lem7651987)). Qed.
Lemma lem7651990 : term175 = term116.
Proof. exact (TRANS (@lem7651985) (@lem7651989)). Qed.
Lemma lem7651991 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7651992 : term377 = term324.
Proof. exact (MK_COMB (@lem7651991) (@lem7651990)). Qed.
Lemma lem7651994 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7651995 : term324 = term102.
Proof. exact (@lem7651994 term117). Qed.
Lemma lem7651996 : term377 = term102.
Proof. exact (TRANS (@lem7651992) (@lem7651995)). Qed.
Lemma lem7651997 : term102 = term377.
Proof. exact (SYM (@lem7651996)). Qed.
Lemma lem7651998 : term376 = term377.
Proof. exact (TRANS (@lem7651982) (@lem7651997)). Qed.
Lemma lem7651999 : term366 = term163.
Proof. exact (@lem7651949 (@lem7651998)). Qed.
Lemma lem7652000 : term365 = term163.
Proof. exact (TRANS (@lem7651915) (@lem7651999)). Qed.
Lemma lem7652002 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7652003 : term163 = term102.
Proof. exact (@lem7652002 term102). Qed.
Lemma lem7652004 : term365 = term102.
Proof. exact (TRANS (@lem7652000) (@lem7652003)). Qed.
Lemma lem7652005 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7652006 : term378 = term375.
Proof. exact (MK_COMB (@lem7652005) (@lem7652004)). Qed.
Lemma lem7652007 (_98520 : int) : (real_of_int _98520) = (real_of_int _98520).
Proof. exact (eq_refl (real_of_int _98520)). Qed.
Lemma lem7652008 (_98520 : int) : (term362 _98520) = (term379 _98520).
Proof. exact (MK_COMB (@lem7652006) (@lem7652007 _98520)). Qed.
Lemma lem7652009 (_98520 : int) : (term361 _98520) = (term379 _98520).
Proof. exact (TRANS (@lem7651906 _98520) (@lem7652008 _98520)). Qed.
Lemma lem7652010 (_98520 : int) : (term379 _98520) = term102.
Proof. exact (@lem1982719 (real_of_int _98520)). Qed.
Lemma lem7652011 (_98520 : int) : (term361 _98520) = term102.
Proof. exact (TRANS (@lem7652009 _98520) (@lem7652010 _98520)). Qed.
Lemma lem7652012 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7652013 (_98520 : int) : (term380 _98520) = term381.
Proof. exact (MK_COMB (@lem7652012) (@lem7652011 _98520)). Qed.
Lemma lem7652015 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7652016 : term166 = term167.
Proof. exact (@lem7652015 term117). Qed.
Lemma lem7652018 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7652019 : term166 = term167.
Proof. exact (@lem7652018 term117). Qed.
Lemma lem7652020 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7652021 : term363 = term364.
Proof. exact (MK_COMB (@lem7652020) (@lem7652019)). Qed.
Lemma lem7652022 : term436 = term437.
Proof. exact (MK_COMB (@lem7652021) (@lem7652016)). Qed.
Lemma lem7652023 : term438.
Proof. exact (@lem1981473 term166 term116 term166 term116 term439 term116). Qed.
Lemma lem7652025 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7652026 : term313 = term319.
Proof. exact (@lem7652025 (NUMERAL 0) term117). Qed.
Lemma lem7652027 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7652028 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7652029 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7652028 h1) (fun h1 : term319 = True => @lem7652027)). Qed.
Lemma lem7652030 : term319 = True.
Proof. exact (EQ_MP (@lem7652029) (@lem7652027)). Qed.
Lemma lem7652031 : term313 = True.
Proof. exact (TRANS (@lem7652026) (@lem7652030)). Qed.
Lemma lem7652032 : True = term313.
Proof. exact (SYM (@lem7652031)). Qed.
Lemma lem7652033 : term313.
Proof. exact (EQ_MP (@lem7652032) (@lem0)). Qed.
Lemma lem7652034 : term440.
Proof. exact (@lem7652023 (@lem7652033)). Qed.
Lemma lem7652036 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7652037 : term313 = term319.
Proof. exact (@lem7652036 (NUMERAL 0) term117). Qed.
Lemma lem7652038 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7652039 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7652040 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7652039 h1) (fun h1 : term319 = True => @lem7652038)). Qed.
Lemma lem7652041 : term319 = True.
Proof. exact (EQ_MP (@lem7652040) (@lem7652038)). Qed.
Lemma lem7652042 : term313 = True.
Proof. exact (TRANS (@lem7652037) (@lem7652041)). Qed.
Lemma lem7652043 : True = term313.
Proof. exact (SYM (@lem7652042)). Qed.
Lemma lem7652044 : term313.
Proof. exact (EQ_MP (@lem7652043) (@lem0)). Qed.
Lemma lem7652045 : term441.
Proof. exact (@lem7652034 (@lem7652044)). Qed.
Lemma lem7652047 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7652048 : term313 = term319.
Proof. exact (@lem7652047 (NUMERAL 0) term117). Qed.
Lemma lem7652049 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7652050 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7652051 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7652050 h1) (fun h1 : term319 = True => @lem7652049)). Qed.
Lemma lem7652052 : term319 = True.
Proof. exact (EQ_MP (@lem7652051) (@lem7652049)). Qed.
Lemma lem7652053 : term313 = True.
Proof. exact (TRANS (@lem7652048) (@lem7652052)). Qed.
Lemma lem7652054 : True = term313.
Proof. exact (SYM (@lem7652053)). Qed.
Lemma lem7652055 : term313.
Proof. exact (EQ_MP (@lem7652054) (@lem0)). Qed.
Lemma lem7652056 : term442.
Proof. exact (@lem7652045 (@lem7652055)). Qed.
Lemma lem7652058 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7652059 : term206 = term211.
Proof. exact (@lem7652058 term117 term117). Qed.
Lemma lem7652060 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7652061 : term178 = term117.
Proof. exact (EQ_MP (@lem7652060) (@lem940073)). Qed.
Lemma lem7652062 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7652063 : term176 = term116.
Proof. exact (MK_COMB (@lem7652062) (@lem7652061)). Qed.
Lemma lem7652064 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7652065 : term211 = term166.
Proof. exact (MK_COMB (@lem7652064) (@lem7652063)). Qed.
Lemma lem7652066 : term206 = term166.
Proof. exact (TRANS (@lem7652059) (@lem7652065)). Qed.
Lemma lem7652068 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7652069 : term206 = term211.
Proof. exact (@lem7652068 term117 term117). Qed.
Lemma lem7652070 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7652071 : term178 = term117.
Proof. exact (EQ_MP (@lem7652070) (@lem940073)). Qed.
Lemma lem7652072 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7652073 : term176 = term116.
Proof. exact (MK_COMB (@lem7652072) (@lem7652071)). Qed.
Lemma lem7652074 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7652075 : term211 = term166.
Proof. exact (MK_COMB (@lem7652074) (@lem7652073)). Qed.
Lemma lem7652076 : term206 = term166.
Proof. exact (TRANS (@lem7652069) (@lem7652075)). Qed.
Lemma lem7652077 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7652078 : term371 = term363.
Proof. exact (MK_COMB (@lem7652077) (@lem7652076)). Qed.
Lemma lem7652079 : term443 = term436.
Proof. exact (MK_COMB (@lem7652078) (@lem7652066)). Qed.
Lemma lem7652080 : term436 = term444.
Proof. exact (@lem1367763 term117 term117). Qed.
Lemma lem7652081 : term445 = term446.
Proof. exact (@lem706885). Qed.
Lemma lem7652082 : (term445 = term446) = (term447 = term448).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term446). Qed.
Lemma lem7652083 : term447 = term448.
Proof. exact (EQ_MP (@lem7652082) (@lem7652081)). Qed.
Lemma lem7652084 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7652085 : term449 = term450.
Proof. exact (MK_COMB (@lem7652084) (@lem7652083)). Qed.
Lemma lem7652086 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7652087 : term444 = term439.
Proof. exact (MK_COMB (@lem7652086) (@lem7652085)). Qed.
Lemma lem7652088 : term436 = term439.
Proof. exact (TRANS (@lem7652080) (@lem7652087)). Qed.
Lemma lem7652089 : term443 = term439.
Proof. exact (TRANS (@lem7652079) (@lem7652088)). Qed.
Lemma lem7652090 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7652091 : term451 = term452.
Proof. exact (MK_COMB (@lem7652090) (@lem7652089)). Qed.
Lemma lem7652092 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7652093 : term453 = term454.
Proof. exact (MK_COMB (@lem7652091) (@lem7652092)). Qed.
Lemma lem7652095 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7652096 : term454 = term455.
Proof. exact (@lem7652095 term448 term117). Qed.
Lemma lem7652097 : term456 = term446.
Proof. exact (@lem996237 term446). Qed.
Lemma lem7652098 : (term456 = term446) = (term457 = term448).
Proof. exact (@lem1007663 term446 (BIT1 0) term446). Qed.
Lemma lem7652099 : term457 = term448.
Proof. exact (EQ_MP (@lem7652098) (@lem7652097)). Qed.
Lemma lem7652100 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7652101 : term458 = term450.
Proof. exact (MK_COMB (@lem7652100) (@lem7652099)). Qed.
Lemma lem7652102 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7652103 : term455 = term439.
Proof. exact (MK_COMB (@lem7652102) (@lem7652101)). Qed.
Lemma lem7652104 : term454 = term439.
Proof. exact (TRANS (@lem7652096) (@lem7652103)). Qed.
Lemma lem7652105 : term453 = term439.
Proof. exact (TRANS (@lem7652093) (@lem7652104)). Qed.
Lemma lem7652107 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7652108 : term175 = term176.
Proof. exact (@lem7652107 term117 term117). Qed.
Lemma lem7652109 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7652110 : term178 = term117.
Proof. exact (EQ_MP (@lem7652109) (@lem940073)). Qed.
Lemma lem7652111 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7652112 : term176 = term116.
Proof. exact (MK_COMB (@lem7652111) (@lem7652110)). Qed.
Lemma lem7652113 : term175 = term116.
Proof. exact (TRANS (@lem7652108) (@lem7652112)). Qed.
Lemma lem7652114 : term452 = term452.
Proof. exact (eq_refl term452). Qed.
Lemma lem7652115 : term459 = term454.
Proof. exact (MK_COMB (@lem7652114) (@lem7652113)). Qed.
Lemma lem7652117 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7652118 : term454 = term455.
Proof. exact (@lem7652117 term448 term117). Qed.
Lemma lem7652119 : term456 = term446.
Proof. exact (@lem996237 term446). Qed.
Lemma lem7652120 : (term456 = term446) = (term457 = term448).
Proof. exact (@lem1007663 term446 (BIT1 0) term446). Qed.
Lemma lem7652121 : term457 = term448.
Proof. exact (EQ_MP (@lem7652120) (@lem7652119)). Qed.
Lemma lem7652122 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7652123 : term458 = term450.
Proof. exact (MK_COMB (@lem7652122) (@lem7652121)). Qed.
Lemma lem7652124 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7652125 : term455 = term439.
Proof. exact (MK_COMB (@lem7652124) (@lem7652123)). Qed.
Lemma lem7652126 : term454 = term439.
Proof. exact (TRANS (@lem7652118) (@lem7652125)). Qed.
Lemma lem7652127 : term459 = term439.
Proof. exact (TRANS (@lem7652115) (@lem7652126)). Qed.
Lemma lem7652128 : term439 = term459.
Proof. exact (SYM (@lem7652127)). Qed.
Lemma lem7652129 : term453 = term459.
Proof. exact (TRANS (@lem7652105) (@lem7652128)). Qed.
Lemma lem7652130 : term437 = term460.
Proof. exact (@lem7652056 (@lem7652129)). Qed.
Lemma lem7652131 : term436 = term460.
Proof. exact (TRANS (@lem7652022) (@lem7652130)). Qed.
Lemma lem7652133 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7652134 : term460 = term439.
Proof. exact (@lem7652133 term439). Qed.
Lemma lem7652135 : term436 = term439.
Proof. exact (TRANS (@lem7652131) (@lem7652134)). Qed.
Lemma lem7652136 (_98520 : int) : (term508 _98520) = term461.
Proof. exact (MK_COMB (@lem7652013 _98520) (@lem7652135)). Qed.
Lemma lem7652137 (_98520 : int) : (term507 _98520) = term461.
Proof. exact (TRANS (@lem7651905 _98520) (@lem7652136 _98520)). Qed.
Lemma lem7652138 : term461 = term439.
Proof. exact (@lem1982721 term439). Qed.
Lemma lem7652139 (_98520 : int) : (term507 _98520) = term439.
Proof. exact (TRANS (@lem7652137 _98520) (@lem7652138)). Qed.
Lemma lem7652140 (_98518 : int) (_98520 : int) : (term506 _98518 _98520) = term461.
Proof. exact (MK_COMB (@lem7651904 _98518) (@lem7652139 _98520)). Qed.
Lemma lem7652141 (_98518 : int) (_98520 : int) : (term505 _98518 _98520) = term461.
Proof. exact (TRANS (@lem7651796 _98518 _98520) (@lem7652140 _98518 _98520)). Qed.
Lemma lem7652142 : term461 = term439.
Proof. exact (@lem1982721 term439). Qed.
Lemma lem7652143 (_98518 : int) (_98520 : int) : (term505 _98518 _98520) = term439.
Proof. exact (TRANS (@lem7652141 _98518 _98520) (@lem7652142)). Qed.
Lemma lem7652144 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7652145 (_98518 : int) (_98520 : int) : (term509 _98518 _98520) = term463.
Proof. exact (MK_COMB (@lem7652144) (@lem7652143 _98518 _98520)). Qed.
Lemma lem7652146 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7652147 (_98518 : int) (_98520 : int) : (term504 _98518 _98520) = term464.
Proof. exact (MK_COMB (@lem7652145 _98518 _98520) (@lem7652146)). Qed.
Lemma lem7652148 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : term464.
Proof. exact (EQ_MP (@lem7652147 _98518 _98520) (@lem7651795 _98518 _98519 _98520 h1)). Qed.
Lemma lem7652150 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7652151 : term464 = term465.
Proof. exact (@lem7652150 term102 term439). Qed.
Lemma lem7652153 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7652154 : term439 = term460.
Proof. exact (@lem7652153 term448). Qed.
Lemma lem7652156 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7652157 : term102 = term163.
Proof. exact (@lem7652156 (NUMERAL 0)). Qed.
Lemma lem7652158 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7652159 : term104 = term394.
Proof. exact (MK_COMB (@lem7652158) (@lem7652157)). Qed.
Lemma lem7652160 : term465 = term466.
Proof. exact (MK_COMB (@lem7652159) (@lem7652154)). Qed.
Lemma lem7652161 : term467.
Proof. exact (@lem1980026 term102 term116 term439 term116). Qed.
Lemma lem7652163 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7652164 : term313 = term319.
Proof. exact (@lem7652163 (NUMERAL 0) term117). Qed.
Lemma lem7652165 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7652166 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7652167 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7652166 h1) (fun h1 : term319 = True => @lem7652165)). Qed.
Lemma lem7652168 : term319 = True.
Proof. exact (EQ_MP (@lem7652167) (@lem7652165)). Qed.
Lemma lem7652169 : term313 = True.
Proof. exact (TRANS (@lem7652164) (@lem7652168)). Qed.
Lemma lem7652170 : True = term313.
Proof. exact (SYM (@lem7652169)). Qed.
Lemma lem7652171 : term313.
Proof. exact (EQ_MP (@lem7652170) (@lem0)). Qed.
Lemma lem7652172 : term468.
Proof. exact (@lem7652161 (@lem7652171)). Qed.
Lemma lem7652174 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7652175 : term313 = term319.
Proof. exact (@lem7652174 (NUMERAL 0) term117). Qed.
Lemma lem7652176 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7652177 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7652178 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7652177 h1) (fun h1 : term319 = True => @lem7652176)). Qed.
Lemma lem7652179 : term319 = True.
Proof. exact (EQ_MP (@lem7652178) (@lem7652176)). Qed.
Lemma lem7652180 : term313 = True.
Proof. exact (TRANS (@lem7652175) (@lem7652179)). Qed.
Lemma lem7652181 : True = term313.
Proof. exact (SYM (@lem7652180)). Qed.
Lemma lem7652182 : term313.
Proof. exact (EQ_MP (@lem7652181) (@lem0)). Qed.
Lemma lem7652183 : term466 = term469.
Proof. exact (@lem7652172 (@lem7652182)). Qed.
Lemma lem7652185 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7652186 : term454 = term455.
Proof. exact (@lem7652185 term448 term117). Qed.
Lemma lem7652187 : term456 = term446.
Proof. exact (@lem996237 term446). Qed.
Lemma lem7652188 : (term456 = term446) = (term457 = term448).
Proof. exact (@lem1007663 term446 (BIT1 0) term446). Qed.
Lemma lem7652189 : term457 = term448.
Proof. exact (EQ_MP (@lem7652188) (@lem7652187)). Qed.
Lemma lem7652190 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7652191 : term458 = term450.
Proof. exact (MK_COMB (@lem7652190) (@lem7652189)). Qed.
Lemma lem7652192 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7652193 : term455 = term439.
Proof. exact (MK_COMB (@lem7652192) (@lem7652191)). Qed.
Lemma lem7652194 : term454 = term439.
Proof. exact (TRANS (@lem7652186) (@lem7652193)). Qed.
Lemma lem7652196 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7652197 : term324 = term102.
Proof. exact (@lem7652196 term117). Qed.
Lemma lem7652198 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7652199 : term399 = term104.
Proof. exact (MK_COMB (@lem7652198) (@lem7652197)). Qed.
Lemma lem7652200 : term469 = term465.
Proof. exact (MK_COMB (@lem7652199) (@lem7652194)). Qed.
Lemma lem7652202 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7652203 : term465 = term470.
Proof. exact (@lem7652202 (NUMERAL 0) term448). Qed.
Lemma lem7652204 : term471 = term446.
Proof. exact (@lem912803). Qed.
Lemma lem7652205 (h1 : term471 = term446) : (term448 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term446 h1). Qed.
Lemma lem7652206 : (term471 = term446) = ((term448 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term471 = term446 => @lem7652205 h1) (fun h1 : (term448 = (NUMERAL 0)) = False => @lem7652204)). Qed.
Lemma lem7652207 : (term448 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7652206) (@lem7652204)). Qed.
Lemma lem7652208 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7652209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7652210 : term403 = (and True).
Proof. exact (MK_COMB (@lem7652209) (@lem7652208)). Qed.
Lemma lem7652211 : term470 = (True /\ False).
Proof. exact (MK_COMB (@lem7652210) (@lem7652207)). Qed.
Lemma lem7652213 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7652214 : term470 = False.
Proof. exact (TRANS (@lem7652211) (@lem7652213)). Qed.
Lemma lem7652215 : term465 = False.
Proof. exact (TRANS (@lem7652203) (@lem7652214)). Qed.
Lemma lem7652216 : term469 = False.
Proof. exact (TRANS (@lem7652200) (@lem7652215)). Qed.
Lemma lem7652217 : term466 = False.
Proof. exact (TRANS (@lem7652183) (@lem7652216)). Qed.
Lemma lem7652218 : term465 = False.
Proof. exact (TRANS (@lem7652160) (@lem7652217)). Qed.
Lemma lem7652219 : term464 = False.
Proof. exact (TRANS (@lem7652151) (@lem7652218)). Qed.
Lemma lem7652220 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term491 _98518 _98519 _98520) : False.
Proof. exact (EQ_MP (@lem7652219) (@lem7652148 _98518 _98519 _98520 h1)). Qed.
Lemma lem7652221 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term301 _98518 _98519 _98520) : False.
Proof. exact (or_elim (@lem7650895 _98518 _98519 _98520 h1) (fun h0 : term472 _98518 _98519 _98520 => @lem7651414 _98518 _98519 _98520 h0) (fun h0 : term491 _98518 _98519 _98520 => @lem7652220 _98518 _98519 _98520 h0)). Qed.
Lemma lem7652222 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term310 _98518 _98519 _98520) : False.
Proof. exact (or_elim (@lem7649471 _98518 _98519 _98520 h1) (fun h0 : term305 _98518 _98519 _98520 => @lem7650894 _98518 _98519 _98520 h0) (fun h0 : term301 _98518 _98519 _98520 => @lem7652221 _98518 _98519 _98520 h0)). Qed.
Lemma lem7652224 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term310 _98518 _98519 _98520) : term310 _98518 _98519 _98520.
Proof. exact (h1). Qed.
Lemma lem7652225 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term310 _98518 _98519 _98520) : (term310 _98518 _98519 _98520) = False.
Proof. exact (prop_ext (fun h2 : term310 _98518 _98519 _98520 => @lem7652222 _98518 _98519 _98520 h1) (fun h2 : False => @lem7652224 _98518 _98519 _98520 h1)). Qed.
Lemma lem7652226 (_98518 : int) (_98519 : int) (_98520 : int) (h1 : term310 _98518 _98519 _98520) : False.
Proof. exact (EQ_MP (@lem7652225 _98518 _98519 _98520 h1) (@lem7652224 _98518 _98519 _98520 h1)). Qed.
Lemma lem7652227 (_98520 : int) (_98518 : int) (_98519 : int) (h1 : term158 _98520 _98518 _98519) : term158 _98520 _98518 _98519.
Proof. exact (h1). Qed.
Lemma lem7652228 (_98520 : int) (_98518 : int) (_98519 : int) (h1 : term158 _98520 _98518 _98519) : term310 _98518 _98519 _98520.
Proof. exact (EQ_MP (@lem7649449 _98518 _98519 _98520) (@lem7652227 _98520 _98518 _98519 h1)). Qed.
Lemma lem7652229 (_98520 : int) (_98518 : int) (_98519 : int) (h1 : term158 _98520 _98518 _98519) : (term310 _98518 _98519 _98520) = False.
Proof. exact (prop_ext (fun h2 : term310 _98518 _98519 _98520 => @lem7652226 _98518 _98519 _98520 h2) (fun h2 : False => @lem7652228 _98520 _98518 _98519 h1)). Qed.
Lemma lem7652230 (_98520 : int) (_98518 : int) (_98519 : int) (h1 : term158 _98520 _98518 _98519) : False.
Proof. exact (EQ_MP (@lem7652229 _98520 _98518 _98519 h1) (@lem7652228 _98520 _98518 _98519 h1)). Qed.
Lemma lem7652231 (_98520 : int) (_98518 : int) (_98519 : int) : term510 _98520 _98518 _98519.
Proof. exact (fun h0 : term158 _98520 _98518 _98519 => @lem7652230 _98520 _98518 _98519 h0). Qed.
Lemma lem7652232 (_98520 : int) (_98518 : int) (_98519 : int) : term511 _98520 _98518 _98519.
Proof. exact (@lem1386578 (term512 _98520 _98518 _98519)). Qed.
Lemma lem7652235 (_98520 : int) (_98518 : int) (_98519 : int) : term512 _98520 _98518 _98519.
Proof. exact (@lem7652232 _98520 _98518 _98519 (@lem7652231 _98520 _98518 _98519)). Qed.
Lemma lem7652236 (_98518 : int) (_98519 : int) (_98520 : int) : (term156 _98520 _98518 _98519) = (term96 _98518 _98519 _98520).
Proof. exact (SYM (@lem7648671 _98520 _98518 _98519)). Qed.
Lemma lem7652237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7652238 (_98518 : int) (_98519 : int) (_98520 : int) : (term512 _98520 _98518 _98519) = (term56 _98518 _98519 _98520).
Proof. exact (MK_COMB (@lem7652237) (@lem7652236 _98518 _98519 _98520)). Qed.
Lemma lem7652239 (_98518 : int) (_98519 : int) (_98520 : int) : term56 _98518 _98519 _98520.
Proof. exact (EQ_MP (@lem7652238 _98518 _98519 _98520) (@lem7652235 _98520 _98518 _98519)). Qed.
Lemma lem7652240 (_98518 : int) (_98519 : int) (_98520 : int) : term57 _98518 _98519 _98520.
Proof. exact (EQ_MP (@lem7648392 _98518 _98519 _98520) (@lem7652239 _98518 _98519 _98520)). Qed.
Lemma lem7652241 (a : nat) (d : nat) (i : nat) : term513 a d i.
Proof. exact (@lem7652240 (int_of_num a) (int_of_num d) (int_of_num i)). Qed.
Lemma lem7652242 (a : nat) (d : nat) (i : nat) : term514 a d i.
Proof. exact (@lem7652241 a d i (@lem7648385 a)). Qed.
Lemma lem7652243 (a : nat) (d : nat) (i : nat) : term515 a d i.
Proof. exact (@lem7652242 a d i (@lem7648388 d)). Qed.
Lemma lem7652244 (a : nat) (d : nat) (i : nat) : term51 a d i.
Proof. exact (@lem7652243 a d i (@lem7648391 i)). Qed.
Lemma lem7652245 (a : nat) (i : nat) : term53 a i.
Proof. exact (fun d : nat => @lem7652244 a d i). Qed.
Lemma lem7652246 (a : nat) (i : nat) : (term53 a i) = (term6 a i).
Proof. exact (SYM (@lem7648382 a i)). Qed.
Lemma lem7652247 (a : nat) (i : nat) : term6 a i.
Proof. exact (EQ_MP (@lem7652246 a i) (@lem7652245 a i)). Qed.
Lemma lem7652261 (i : nat) (a : nat) : (term0 i a) = (Peano.le i a).
Proof. exact (@lem16933 (Peano.le i a)). Qed.
Lemma lem7652262 (i : nat) (a : nat) : (term516 i a) = (term516 i a).
Proof. exact (eq_refl (term516 i a)). Qed.
Lemma lem7652263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7652264 (i : nat) (a : nat) : (term2 i a) = (term3 i a).
Proof. exact (MK_COMB (@lem7652263) (@lem7652261 i a)). Qed.
Lemma lem7652265 (i : nat) (a : nat) : (term517 i a) = (term518 i a).
Proof. exact (MK_COMB (@lem7652264 i a) (@lem7652262 i a)). Qed.
Lemma lem7652266 (i : nat) (a : nat) : (term519 i a) = (term517 i a).
Proof. exact (@lem17265 (term7 i a) (term516 i a)). Qed.
Lemma lem7652268 (i : nat) (a : nat) : (term519 i a) = (term518 i a).
Proof. exact (TRANS (@lem7652266 i a) (@lem7652265 i a)). Qed.
Lemma lem7652269 (i : nat) (a : nat) : (term520 i a) = (term521 i a).
Proof. exact (@lem1032781 i a (term522 i a)). Qed.
Lemma lem7652270 (i : nat) (a : nat) (d : nat) : (term523 i a d) = (term524 i a d).
Proof. exact (eq_refl (term523 i a d)). Qed.
Lemma lem7652271 (i : nat) (a : nat) (d : nat) : (term13 i a d) = (term13 i a d).
Proof. exact (eq_refl (term13 i a d)). Qed.
Lemma lem7652272 (i : nat) (a : nat) (d : nat) : (term525 i a d) = (term526 i a d).
Proof. exact (MK_COMB (@lem7652271 i a d) (@lem7652270 i a d)). Qed.
Lemma lem7652273 (i : nat) (a : nat) : (term527 i a) = (term528 i a).
Proof. exact (fun_ext (fun d : nat => @lem7652272 i a d)). Qed.
Lemma lem7652274 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7652275 (i : nat) (a : nat) : (term521 i a) = (term529 i a).
Proof. exact (MK_COMB (@lem7652274) (@lem7652273 i a)). Qed.
Lemma lem7652276 (i : nat) (a : nat) : (term520 i a) = (term518 i a).
Proof. exact (eq_refl (term520 i a)). Qed.
Lemma lem7652277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7652278 (i : nat) (a : nat) : (term530 i a) = (term531 i a).
Proof. exact (MK_COMB (@lem7652277) (@lem7652276 i a)). Qed.
Lemma lem7652279 (i : nat) (a : nat) : ((term520 i a) = (term521 i a)) = ((term518 i a) = (term529 i a)).
Proof. exact (MK_COMB (@lem7652278 i a) (@lem7652275 i a)). Qed.
Lemma lem7652280 (i : nat) (a : nat) : (term518 i a) = (term529 i a).
Proof. exact (EQ_MP (@lem7652279 i a) (@lem7652269 i a)). Qed.
Lemma lem7652281 (i : nat) (a : nat) (d : nat) : (term526 i a d) = (term526 i a d).
Proof. exact (eq_refl (term526 i a d)). Qed.
Lemma lem7652282 (i : nat) (a : nat) : (term528 i a) = (term528 i a).
Proof. exact (fun_ext (fun d : nat => @lem7652281 i a d)). Qed.
Lemma lem7652283 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7652284 (i : nat) (a : nat) : (term529 i a) = (term529 i a).
Proof. exact (MK_COMB (@lem7652283) (@lem7652282 i a)). Qed.
Lemma lem7652285 (i : nat) (a : nat) : (term531 i a) = (term531 i a).
Proof. exact (eq_refl (term531 i a)). Qed.
Lemma lem7652286 (i : nat) (a : nat) : ((term518 i a) = (term529 i a)) = ((term518 i a) = (term529 i a)).
Proof. exact (MK_COMB (@lem7652285 i a) (@lem7652284 i a)). Qed.
Lemma lem7652287 (i : nat) (a : nat) : (term518 i a) = (term529 i a).
Proof. exact (EQ_MP (@lem7652286 i a) (@lem7652280 i a)). Qed.
Lemma lem7652310 (i : nat) (a : nat) : (term519 i a) = (term529 i a).
Proof. exact (TRANS (@lem7652268 i a) (@lem7652287 i a)). Qed.
Lemma lem7652359 (i : nat) (a : nat) (d : nat) : (term526 i a d) = (term526 i a d).
Proof. exact (eq_refl (term526 i a d)). Qed.
Lemma lem7652360 (i : nat) (a : nat) : (term528 i a) = (term528 i a).
Proof. exact (fun_ext (fun d : nat => @lem7652359 i a d)). Qed.
Lemma lem7652361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7652362 (i : nat) (a : nat) : (term529 i a) = (term529 i a).
Proof. exact (MK_COMB (@lem7652361) (@lem7652360 i a)). Qed.
Lemma lem7652365 (i : nat) (a : nat) : (term519 i a) = (term529 i a).
Proof. exact (TRANS (@lem7652310 i a) (@lem7652362 i a)). Qed.
Lemma lem7652367 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7652368 (i : nat) (a : nat) (d : nat) : (i = (Nat.add a d)) = ((int_of_num i) = (term26 a d)).
Proof. exact (@lem7652367 i (Nat.add a d)). Qed.
Lemma lem7652372 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7652373 (a : nat) (d : nat) : (term26 a d) = (term27 a d).
Proof. exact (@lem7652372 a d). Qed.
Lemma lem7652374 (i : nat) : (term28 i) = (term28 i).
Proof. exact (eq_refl (term28 i)). Qed.
Lemma lem7652375 (i : nat) (a : nat) (d : nat) : ((int_of_num i) = (term26 a d)) = ((int_of_num i) = (term27 a d)).
Proof. exact (MK_COMB (@lem7652374 i) (@lem7652373 a d)). Qed.
Lemma lem7652376 (i : nat) (a : nat) (d : nat) : (i = (Nat.add a d)) = ((int_of_num i) = (term27 a d)).
Proof. exact (TRANS (@lem7652368 i a d) (@lem7652375 i a d)). Qed.
Lemma lem7652377 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7652378 (i : nat) (a : nat) (d : nat) : (term29 i a d) = (term30 i a d).
Proof. exact (MK_COMB (@lem7652377) (@lem7652376 i a d)). Qed.
Lemma lem7652379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7652380 (i : nat) (a : nat) (d : nat) : (term31 i a d) = (term32 i a d).
Proof. exact (MK_COMB (@lem7652379) (@lem7652378 i a d)). Qed.
Lemma lem7652382 (m : nat) (n : nat) : (Peano.lt m n) = (term33 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem7652383 (i : nat) (a : nat) : (Peano.lt i a) = (term33 i a).
Proof. exact (@lem7652382 i a). Qed.
Lemma lem7652384 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7652385 (i : nat) (a : nat) : (term34 i a) = (term35 i a).
Proof. exact (MK_COMB (@lem7652384) (@lem7652383 i a)). Qed.
Lemma lem7652386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7652387 (i : nat) (a : nat) : (term36 i a) = (term37 i a).
Proof. exact (MK_COMB (@lem7652386) (@lem7652385 i a)). Qed.
Lemma lem7652389 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7652390 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term38).
Proof. exact (@lem7652389 d (NUMERAL 0)). Qed.
Lemma lem7652393 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7652394 (d : nat) : (term39 d) = (term40 d).
Proof. exact (MK_COMB (@lem7652393) (@lem7652390 d)). Qed.
Lemma lem7652395 (i : nat) (a : nat) (d : nat) : (term41 i a d) = (term42 i a d).
Proof. exact (MK_COMB (@lem7652387 i a) (@lem7652394 d)). Qed.
Lemma lem7652396 (i : nat) (a : nat) (d : nat) : (term43 i a d) = (term44 i a d).
Proof. exact (MK_COMB (@lem7652380 i a d) (@lem7652395 i a d)). Qed.
Lemma lem7652397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7652398 (i : nat) (a : nat) (d : nat) : (term13 i a d) = (term45 i a d).
Proof. exact (MK_COMB (@lem7652397) (@lem7652396 i a d)). Qed.
Lemma lem7652400 (m : nat) (n : nat) : (Peano.le m n) = (term46 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7652401 (i : nat) (a : nat) : (Peano.le i a) = (term46 i a).
Proof. exact (@lem7652400 i a). Qed.
Lemma lem7652402 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7652403 (i : nat) (a : nat) : (term3 i a) = (term47 i a).
Proof. exact (MK_COMB (@lem7652402) (@lem7652401 i a)). Qed.
Lemma lem7652405 (m : nat) (n : nat) : (Peano.le m n) = (term46 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7652406 (d : nat) : (term532 d) = (term533 d).
Proof. exact (@lem7652405 term117 d). Qed.
Lemma lem7652407 (i : nat) (a : nat) (d : nat) : (term524 i a d) = (term534 i a d).
Proof. exact (MK_COMB (@lem7652403 i a) (@lem7652406 d)). Qed.
Lemma lem7652408 (i : nat) (a : nat) (d : nat) : (term526 i a d) = (term535 i a d).
Proof. exact (MK_COMB (@lem7652398 i a d) (@lem7652407 i a d)). Qed.
Lemma lem7652409 (i : nat) (a : nat) : (term528 i a) = (term536 i a).
Proof. exact (fun_ext (fun d : nat => @lem7652408 i a d)). Qed.
Lemma lem7652410 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7652411 (i : nat) (a : nat) : (term529 i a) = (term537 i a).
Proof. exact (MK_COMB (@lem7652410) (@lem7652409 i a)). Qed.
Lemma lem7652412 (i : nat) (a : nat) : (term519 i a) = (term537 i a).
Proof. exact (TRANS (@lem7652365 i a) (@lem7652411 i a)). Qed.
Lemma lem7652413 (a : nat) : term54 a.
Proof. exact (@lem2307535 a). Qed.
Lemma lem7652414 (a : nat) : (term54 a) = (term55 a).
Proof. exact (eq_refl (term54 a)). Qed.
Lemma lem7652415 (a : nat) : term55 a.
Proof. exact (EQ_MP (@lem7652414 a) (@lem7652413 a)). Qed.
Lemma lem7652416 (d : nat) : term54 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem7652417 (d : nat) : (term54 d) = (term55 d).
Proof. exact (eq_refl (term54 d)). Qed.
Lemma lem7652418 (d : nat) : term55 d.
Proof. exact (EQ_MP (@lem7652417 d) (@lem7652416 d)). Qed.
Lemma lem7652419 (i : nat) : term54 i.
Proof. exact (@lem2307535 i). Qed.
Lemma lem7652420 (i : nat) : (term54 i) = (term55 i).
Proof. exact (eq_refl (term54 i)). Qed.
Lemma lem7652421 (i : nat) : term55 i.
Proof. exact (EQ_MP (@lem7652420 i) (@lem7652419 i)). Qed.
Lemma lem7652422 (_98528 : int) (_98526 : int) (_98527 : int) : (term538 _98528 _98526 _98527) = (term539 _98528 _98526 _98527).
Proof. exact (@lem2318604 (term539 _98528 _98526 _98527)). Qed.
Lemma lem7652447 (_98528 : int) (_98526 : int) (_98527 : int) : (term58 _98528 _98526 _98527) = (_98528 = (int_add _98526 _98527)).
Proof. exact (@lem16933 (_98528 = (int_add _98526 _98527))). Qed.
Lemma lem7652450 (_98528 : int) (_98526 : int) : (term59 _98528 _98526) = (int_lt _98528 _98526).
Proof. exact (@lem16933 (int_lt _98528 _98526)). Qed.
Lemma lem7652453 (_98527 : int) : (term60 _98527) = (_98527 = term38).
Proof. exact (@lem16933 (_98527 = term38)). Qed.
Lemma lem7652454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7652455 (_98528 : int) (_98526 : int) : (term61 _98528 _98526) = (term62 _98528 _98526).
Proof. exact (MK_COMB (@lem7652454) (@lem7652450 _98528 _98526)). Qed.
Lemma lem7652456 (_98528 : int) (_98526 : int) (_98527 : int) : (term63 _98528 _98526 _98527) = (term64 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652455 _98528 _98526) (@lem7652453 _98527)). Qed.
Lemma lem7652457 (_98528 : int) (_98526 : int) (_98527 : int) : (term65 _98528 _98526 _98527) = (term63 _98528 _98526 _98527).
Proof. exact (@lem17160 (term66 _98528 _98526) (term67 _98527)). Qed.
Lemma lem7652458 (_98528 : int) (_98526 : int) (_98527 : int) : (term65 _98528 _98526 _98527) = (term64 _98528 _98526 _98527).
Proof. exact (TRANS (@lem7652457 _98528 _98526 _98527) (@lem7652456 _98528 _98526 _98527)). Qed.
Lemma lem7652459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7652460 (_98528 : int) (_98526 : int) (_98527 : int) : (term68 _98528 _98526 _98527) = (term69 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652459) (@lem7652447 _98528 _98526 _98527)). Qed.
Lemma lem7652461 (_98528 : int) (_98526 : int) (_98527 : int) : (term70 _98528 _98526 _98527) = (term71 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652460 _98528 _98526 _98527) (@lem7652458 _98528 _98526 _98527)). Qed.
Lemma lem7652462 (_98528 : int) (_98526 : int) (_98527 : int) : (term72 _98528 _98526 _98527) = (term70 _98528 _98526 _98527).
Proof. exact (@lem17045 (term73 _98528 _98526 _98527) (term74 _98528 _98526 _98527)). Qed.
Lemma lem7652463 (_98528 : int) (_98526 : int) (_98527 : int) : (term72 _98528 _98526 _98527) = (term71 _98528 _98526 _98527).
Proof. exact (TRANS (@lem7652462 _98528 _98526 _98527) (@lem7652461 _98528 _98526 _98527)). Qed.
Lemma lem7652470 (_98528 : int) (_98526 : int) (_98527 : int) : (term540 _98528 _98526 _98527) = (term541 _98528 _98526 _98527).
Proof. exact (@lem17160 (int_le _98528 _98526) (term542 _98527)). Qed.
Lemma lem7652471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7652472 (_98528 : int) (_98526 : int) (_98527 : int) : (term77 _98528 _98526 _98527) = (term78 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652471) (@lem7652463 _98528 _98526 _98527)). Qed.
Lemma lem7652473 (_98528 : int) (_98526 : int) (_98527 : int) : (term543 _98528 _98526 _98527) = (term544 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652472 _98528 _98526 _98527) (@lem7652470 _98528 _98526 _98527)). Qed.
Lemma lem7652474 (_98528 : int) (_98526 : int) (_98527 : int) : (term545 _98528 _98526 _98527) = (term543 _98528 _98526 _98527).
Proof. exact (@lem17160 (term82 _98528 _98526 _98527) (term546 _98528 _98526 _98527)). Qed.
Lemma lem7652475 (_98528 : int) (_98526 : int) (_98527 : int) : (term545 _98528 _98526 _98527) = (term544 _98528 _98526 _98527).
Proof. exact (TRANS (@lem7652474 _98528 _98526 _98527) (@lem7652473 _98528 _98526 _98527)). Qed.
Lemma lem7652477 (_98528 : int) : (term84 _98528) = (term84 _98528).
Proof. exact (eq_refl (term84 _98528)). Qed.
Lemma lem7652478 (_98528 : int) (_98526 : int) (_98527 : int) : (term547 _98528 _98526 _98527) = (term548 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652477 _98528) (@lem7652475 _98528 _98526 _98527)). Qed.
Lemma lem7652479 (_98528 : int) (_98526 : int) (_98527 : int) : (term549 _98528 _98526 _98527) = (term547 _98528 _98526 _98527).
Proof. exact (@lem17362 (term88 _98528) (term550 _98528 _98526 _98527)). Qed.
Lemma lem7652480 (_98528 : int) (_98526 : int) (_98527 : int) : (term549 _98528 _98526 _98527) = (term548 _98528 _98526 _98527).
Proof. exact (TRANS (@lem7652479 _98528 _98526 _98527) (@lem7652478 _98528 _98526 _98527)). Qed.
Lemma lem7652482 (_98527 : int) : (term84 _98527) = (term84 _98527).
Proof. exact (eq_refl (term84 _98527)). Qed.
Lemma lem7652483 (_98528 : int) (_98526 : int) (_98527 : int) : (term551 _98528 _98526 _98527) = (term552 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652482 _98527) (@lem7652480 _98528 _98526 _98527)). Qed.
Lemma lem7652484 (_98528 : int) (_98526 : int) (_98527 : int) : (term553 _98528 _98526 _98527) = (term551 _98528 _98526 _98527).
Proof. exact (@lem17362 (term88 _98527) (term554 _98528 _98526 _98527)). Qed.
Lemma lem7652485 (_98528 : int) (_98526 : int) (_98527 : int) : (term553 _98528 _98526 _98527) = (term552 _98528 _98526 _98527).
Proof. exact (TRANS (@lem7652484 _98528 _98526 _98527) (@lem7652483 _98528 _98526 _98527)). Qed.
Lemma lem7652487 (_98526 : int) : (term84 _98526) = (term84 _98526).
Proof. exact (eq_refl (term84 _98526)). Qed.
Lemma lem7652488 (_98528 : int) (_98526 : int) (_98527 : int) : (term555 _98528 _98526 _98527) = (term556 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652487 _98526) (@lem7652485 _98528 _98526 _98527)). Qed.
Lemma lem7652489 (_98528 : int) (_98526 : int) (_98527 : int) : (term557 _98528 _98526 _98527) = (term555 _98528 _98526 _98527).
Proof. exact (@lem17362 (term88 _98526) (term558 _98528 _98526 _98527)). Qed.
Lemma lem7652525 (_98528 : int) (_98526 : int) (_98527 : int) : (term557 _98528 _98526 _98527) = (term556 _98528 _98526 _98527).
Proof. exact (TRANS (@lem7652489 _98528 _98526 _98527) (@lem7652488 _98528 _98526 _98527)). Qed.
Lemma lem7652528 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7652529 (_98526 : int) : (term88 _98526) = (term99 _98526).
Proof. exact (@lem7652528 term38 _98526). Qed.
Lemma lem7652531 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7652532 : term101 = term102.
Proof. exact (@lem7652531 (NUMERAL 0)). Qed.
Lemma lem7652533 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7652534 : term103 = term104.
Proof. exact (MK_COMB (@lem7652533) (@lem7652532)). Qed.
Lemma lem7652535 (_98526 : int) : (real_of_int _98526) = (real_of_int _98526).
Proof. exact (eq_refl (real_of_int _98526)). Qed.
Lemma lem7652536 (_98526 : int) : (term99 _98526) = (term105 _98526).
Proof. exact (MK_COMB (@lem7652534) (@lem7652535 _98526)). Qed.
Lemma lem7652538 (_98526 : int) : (term88 _98526) = (term105 _98526).
Proof. exact (TRANS (@lem7652529 _98526) (@lem7652536 _98526)). Qed.
Lemma lem7652541 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7652542 (_98527 : int) : (term88 _98527) = (term99 _98527).
Proof. exact (@lem7652541 term38 _98527). Qed.
Lemma lem7652544 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7652545 : term101 = term102.
Proof. exact (@lem7652544 (NUMERAL 0)). Qed.
Lemma lem7652546 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7652547 : term103 = term104.
Proof. exact (MK_COMB (@lem7652546) (@lem7652545)). Qed.
Lemma lem7652548 (_98527 : int) : (real_of_int _98527) = (real_of_int _98527).
Proof. exact (eq_refl (real_of_int _98527)). Qed.
Lemma lem7652549 (_98527 : int) : (term99 _98527) = (term105 _98527).
Proof. exact (MK_COMB (@lem7652547) (@lem7652548 _98527)). Qed.
Lemma lem7652551 (_98527 : int) : (term88 _98527) = (term105 _98527).
Proof. exact (TRANS (@lem7652542 _98527) (@lem7652549 _98527)). Qed.
Lemma lem7652554 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7652555 (_98528 : int) : (term88 _98528) = (term99 _98528).
Proof. exact (@lem7652554 term38 _98528). Qed.
Lemma lem7652557 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7652558 : term101 = term102.
Proof. exact (@lem7652557 (NUMERAL 0)). Qed.
Lemma lem7652559 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7652560 : term103 = term104.
Proof. exact (MK_COMB (@lem7652559) (@lem7652558)). Qed.
Lemma lem7652561 (_98528 : int) : (real_of_int _98528) = (real_of_int _98528).
Proof. exact (eq_refl (real_of_int _98528)). Qed.
Lemma lem7652562 (_98528 : int) : (term99 _98528) = (term105 _98528).
Proof. exact (MK_COMB (@lem7652560) (@lem7652561 _98528)). Qed.
Lemma lem7652564 (_98528 : int) : (term88 _98528) = (term105 _98528).
Proof. exact (TRANS (@lem7652555 _98528) (@lem7652562 _98528)). Qed.
Lemma lem7652567 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem7652568 (_98528 : int) (_98526 : int) (_98527 : int) : (_98528 = (int_add _98526 _98527)) = ((real_of_int _98528) = (term106 _98526 _98527)).
Proof. exact (@lem7652567 _98528 (int_add _98526 _98527)). Qed.
Lemma lem7652572 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7652573 (_98526 : int) (_98527 : int) : (term106 _98526 _98527) = (term107 _98526 _98527).
Proof. exact (@lem7652572 _98526 _98527). Qed.
Lemma lem7652574 (_98528 : int) : (term108 _98528) = (term108 _98528).
Proof. exact (eq_refl (term108 _98528)). Qed.
Lemma lem7652575 (_98528 : int) (_98526 : int) (_98527 : int) : ((real_of_int _98528) = (term106 _98526 _98527)) = ((real_of_int _98528) = (term107 _98526 _98527)).
Proof. exact (MK_COMB (@lem7652574 _98528) (@lem7652573 _98526 _98527)). Qed.
Lemma lem7652577 (_98528 : int) (_98526 : int) (_98527 : int) : (_98528 = (int_add _98526 _98527)) = ((real_of_int _98528) = (term107 _98526 _98527)).
Proof. exact (TRANS (@lem7652568 _98528 _98526 _98527) (@lem7652575 _98528 _98526 _98527)). Qed.
Lemma lem7652579 (x : int) (y : int) : (int_lt x y) = (term109 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem7652580 (_98528 : int) (_98526 : int) : (int_lt _98528 _98526) = (term109 _98528 _98526).
Proof. exact (@lem7652579 _98528 _98526). Qed.
Lemma lem7652582 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7652583 (_98528 : int) (_98526 : int) : (term109 _98528 _98526) = (term110 _98528 _98526).
Proof. exact (@lem7652582 (term111 _98528) _98526). Qed.
Lemma lem7652585 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7652586 (_98528 : int) : (term112 _98528) = (term113 _98528).
Proof. exact (@lem7652585 _98528 term114). Qed.
Lemma lem7652588 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7652589 : term115 = term116.
Proof. exact (@lem7652588 term117). Qed.
Lemma lem7652590 (_98528 : int) : (term118 _98528) = (term118 _98528).
Proof. exact (eq_refl (term118 _98528)). Qed.
Lemma lem7652591 (_98528 : int) : (term113 _98528) = (term119 _98528).
Proof. exact (MK_COMB (@lem7652590 _98528) (@lem7652589)). Qed.
Lemma lem7652592 (_98528 : int) : (term112 _98528) = (term119 _98528).
Proof. exact (TRANS (@lem7652586 _98528) (@lem7652591 _98528)). Qed.
Lemma lem7652593 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7652594 (_98528 : int) : (term120 _98528) = (term121 _98528).
Proof. exact (MK_COMB (@lem7652593) (@lem7652592 _98528)). Qed.
Lemma lem7652595 (_98526 : int) : (real_of_int _98526) = (real_of_int _98526).
Proof. exact (eq_refl (real_of_int _98526)). Qed.
Lemma lem7652596 (_98528 : int) (_98526 : int) : (term110 _98528 _98526) = (term122 _98528 _98526).
Proof. exact (MK_COMB (@lem7652594 _98528) (@lem7652595 _98526)). Qed.
Lemma lem7652597 (_98528 : int) (_98526 : int) : (term109 _98528 _98526) = (term122 _98528 _98526).
Proof. exact (TRANS (@lem7652583 _98528 _98526) (@lem7652596 _98528 _98526)). Qed.
Lemma lem7652598 (_98528 : int) (_98526 : int) : (int_lt _98528 _98526) = (term122 _98528 _98526).
Proof. exact (TRANS (@lem7652580 _98528 _98526) (@lem7652597 _98528 _98526)). Qed.
Lemma lem7652601 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem7652602 (_98527 : int) : (_98527 = term38) = ((real_of_int _98527) = term101).
Proof. exact (@lem7652601 _98527 term38). Qed.
Lemma lem7652606 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7652607 : term101 = term102.
Proof. exact (@lem7652606 (NUMERAL 0)). Qed.
Lemma lem7652608 (_98527 : int) : (term108 _98527) = (term108 _98527).
Proof. exact (eq_refl (term108 _98527)). Qed.
Lemma lem7652609 (_98527 : int) : ((real_of_int _98527) = term101) = ((real_of_int _98527) = term102).
Proof. exact (MK_COMB (@lem7652608 _98527) (@lem7652607)). Qed.
Lemma lem7652611 (_98527 : int) : (_98527 = term38) = ((real_of_int _98527) = term102).
Proof. exact (TRANS (@lem7652602 _98527) (@lem7652609 _98527)). Qed.
Lemma lem7652612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7652613 (_98528 : int) (_98526 : int) : (term62 _98528 _98526) = (term123 _98528 _98526).
Proof. exact (MK_COMB (@lem7652612) (@lem7652598 _98528 _98526)). Qed.
Lemma lem7652614 (_98528 : int) (_98526 : int) (_98527 : int) : (term64 _98528 _98526 _98527) = (term124 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652613 _98528 _98526) (@lem7652611 _98527)). Qed.
Lemma lem7652615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7652616 (_98528 : int) (_98526 : int) (_98527 : int) : (term69 _98528 _98526 _98527) = (term125 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652615) (@lem7652577 _98528 _98526 _98527)). Qed.
Lemma lem7652617 (_98528 : int) (_98526 : int) (_98527 : int) : (term71 _98528 _98526 _98527) = (term126 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652616 _98528 _98526 _98527) (@lem7652614 _98528 _98526 _98527)). Qed.
Lemma lem7652619 (y : int) (x : int) : (term127 x y) = (term109 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7652620 (_98526 : int) (_98528 : int) : (term127 _98528 _98526) = (term109 _98526 _98528).
Proof. exact (@lem7652619 _98526 _98528). Qed.
Lemma lem7652622 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7652623 (_98526 : int) (_98528 : int) : (term109 _98526 _98528) = (term110 _98526 _98528).
Proof. exact (@lem7652622 (term111 _98526) _98528). Qed.
Lemma lem7652625 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7652626 (_98526 : int) : (term112 _98526) = (term113 _98526).
Proof. exact (@lem7652625 _98526 term114). Qed.
Lemma lem7652628 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7652629 : term115 = term116.
Proof. exact (@lem7652628 term117). Qed.
Lemma lem7652630 (_98526 : int) : (term118 _98526) = (term118 _98526).
Proof. exact (eq_refl (term118 _98526)). Qed.
Lemma lem7652631 (_98526 : int) : (term113 _98526) = (term119 _98526).
Proof. exact (MK_COMB (@lem7652630 _98526) (@lem7652629)). Qed.
Lemma lem7652632 (_98526 : int) : (term112 _98526) = (term119 _98526).
Proof. exact (TRANS (@lem7652626 _98526) (@lem7652631 _98526)). Qed.
Lemma lem7652633 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7652634 (_98526 : int) : (term120 _98526) = (term121 _98526).
Proof. exact (MK_COMB (@lem7652633) (@lem7652632 _98526)). Qed.
Lemma lem7652635 (_98528 : int) : (real_of_int _98528) = (real_of_int _98528).
Proof. exact (eq_refl (real_of_int _98528)). Qed.
Lemma lem7652636 (_98526 : int) (_98528 : int) : (term110 _98526 _98528) = (term122 _98526 _98528).
Proof. exact (MK_COMB (@lem7652634 _98526) (@lem7652635 _98528)). Qed.
Lemma lem7652637 (_98526 : int) (_98528 : int) : (term109 _98526 _98528) = (term122 _98526 _98528).
Proof. exact (TRANS (@lem7652623 _98526 _98528) (@lem7652636 _98526 _98528)). Qed.
Lemma lem7652638 (_98526 : int) (_98528 : int) : (term127 _98528 _98526) = (term122 _98526 _98528).
Proof. exact (TRANS (@lem7652620 _98526 _98528) (@lem7652637 _98526 _98528)). Qed.
Lemma lem7652640 (y : int) (x : int) : (term127 x y) = (term109 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7652641 (_98527 : int) : (term559 _98527) = (term560 _98527).
Proof. exact (@lem7652640 _98527 term114). Qed.
Lemma lem7652643 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7652644 (_98527 : int) : (term560 _98527) = (term561 _98527).
Proof. exact (@lem7652643 (term111 _98527) term114). Qed.
Lemma lem7652646 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7652647 (_98527 : int) : (term112 _98527) = (term113 _98527).
Proof. exact (@lem7652646 _98527 term114). Qed.
Lemma lem7652649 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7652650 : term115 = term116.
Proof. exact (@lem7652649 term117). Qed.
Lemma lem7652651 (_98527 : int) : (term118 _98527) = (term118 _98527).
Proof. exact (eq_refl (term118 _98527)). Qed.
Lemma lem7652652 (_98527 : int) : (term113 _98527) = (term119 _98527).
Proof. exact (MK_COMB (@lem7652651 _98527) (@lem7652650)). Qed.
Lemma lem7652653 (_98527 : int) : (term112 _98527) = (term119 _98527).
Proof. exact (TRANS (@lem7652647 _98527) (@lem7652652 _98527)). Qed.
Lemma lem7652654 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7652655 (_98527 : int) : (term120 _98527) = (term121 _98527).
Proof. exact (MK_COMB (@lem7652654) (@lem7652653 _98527)). Qed.
Lemma lem7652657 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7652658 : term115 = term116.
Proof. exact (@lem7652657 term117). Qed.
Lemma lem7652659 (_98527 : int) : (term561 _98527) = (term562 _98527).
Proof. exact (MK_COMB (@lem7652655 _98527) (@lem7652658)). Qed.
Lemma lem7652660 (_98527 : int) : (term560 _98527) = (term562 _98527).
Proof. exact (TRANS (@lem7652644 _98527) (@lem7652659 _98527)). Qed.
Lemma lem7652661 (_98527 : int) : (term559 _98527) = (term562 _98527).
Proof. exact (TRANS (@lem7652641 _98527) (@lem7652660 _98527)). Qed.
Lemma lem7652662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7652663 (_98526 : int) (_98528 : int) : (term149 _98528 _98526) = (term123 _98526 _98528).
Proof. exact (MK_COMB (@lem7652662) (@lem7652638 _98526 _98528)). Qed.
Lemma lem7652664 (_98526 : int) (_98528 : int) (_98527 : int) : (term541 _98528 _98526 _98527) = (term563 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7652663 _98526 _98528) (@lem7652661 _98527)). Qed.
Lemma lem7652665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7652666 (_98528 : int) (_98526 : int) (_98527 : int) : (term78 _98528 _98526 _98527) = (term151 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652665) (@lem7652617 _98528 _98526 _98527)). Qed.
Lemma lem7652667 (_98526 : int) (_98528 : int) (_98527 : int) : (term544 _98528 _98526 _98527) = (term564 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7652666 _98528 _98526 _98527) (@lem7652664 _98526 _98528 _98527)). Qed.
Lemma lem7652668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7652669 (_98528 : int) : (term84 _98528) = (term153 _98528).
Proof. exact (MK_COMB (@lem7652668) (@lem7652564 _98528)). Qed.
Lemma lem7652670 (_98526 : int) (_98528 : int) (_98527 : int) : (term548 _98528 _98526 _98527) = (term565 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7652669 _98528) (@lem7652667 _98526 _98528 _98527)). Qed.
Lemma lem7652671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7652672 (_98527 : int) : (term84 _98527) = (term153 _98527).
Proof. exact (MK_COMB (@lem7652671) (@lem7652551 _98527)). Qed.
Lemma lem7652673 (_98526 : int) (_98528 : int) (_98527 : int) : (term552 _98528 _98526 _98527) = (term566 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7652672 _98527) (@lem7652670 _98526 _98528 _98527)). Qed.
Lemma lem7652674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7652675 (_98526 : int) : (term84 _98526) = (term153 _98526).
Proof. exact (MK_COMB (@lem7652674) (@lem7652538 _98526)). Qed.
Lemma lem7652676 (_98526 : int) (_98528 : int) (_98527 : int) : (term556 _98528 _98526 _98527) = (term567 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7652675 _98526) (@lem7652673 _98526 _98528 _98527)). Qed.
Lemma lem7652677 (_98526 : int) (_98528 : int) (_98527 : int) : (term557 _98528 _98526 _98527) = (term567 _98526 _98528 _98527).
Proof. exact (TRANS (@lem7652525 _98528 _98526 _98527) (@lem7652676 _98526 _98528 _98527)). Qed.
Lemma lem7652681 (t : Prop) : (term157 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7652757 (_98526 : int) (_98528 : int) (_98527 : int) : (term568 _98526 _98528 _98527) = (term567 _98526 _98528 _98527).
Proof. exact (@lem7652681 (term567 _98526 _98528 _98527)). Qed.
Lemma lem7652758 (_98526 : int) : (term105 _98526) = (term159 _98526).
Proof. exact (@lem1988287 (real_of_int _98526) term102). Qed.
Lemma lem7652764 (_98526 : int) : (term160 _98526) = (term161 _98526).
Proof. exact (@lem1982792 (real_of_int _98526) term102). Qed.
Lemma lem7652766 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7652767 : term102 = term163.
Proof. exact (@lem7652766 (NUMERAL 0)). Qed.
Lemma lem7652769 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7652770 : term166 = term167.
Proof. exact (@lem7652769 term117). Qed.
Lemma lem7652771 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7652772 : term168 = term169.
Proof. exact (MK_COMB (@lem7652771) (@lem7652770)). Qed.
Lemma lem7652773 : term170 = term171.
Proof. exact (MK_COMB (@lem7652772) (@lem7652767)). Qed.
Lemma lem7652774 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7652776 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7652777 : term175 = term176.
Proof. exact (@lem7652776 term117 term117). Qed.
Lemma lem7652778 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7652779 : term178 = term117.
Proof. exact (EQ_MP (@lem7652778) (@lem940073)). Qed.
Lemma lem7652780 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7652781 : term176 = term116.
Proof. exact (MK_COMB (@lem7652780) (@lem7652779)). Qed.
Lemma lem7652782 : term175 = term116.
Proof. exact (TRANS (@lem7652777) (@lem7652781)). Qed.
Lemma lem7652784 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7652785 : term170 = term102.
Proof. exact (@lem7652784 term117). Qed.
Lemma lem7652786 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7652787 : term180 = term181.
Proof. exact (MK_COMB (@lem7652786) (@lem7652785)). Qed.
Lemma lem7652788 : term172 = term163.
Proof. exact (MK_COMB (@lem7652787) (@lem7652782)). Qed.
Lemma lem7652789 : term171 = term163.
Proof. exact (TRANS (@lem7652774) (@lem7652788)). Qed.
Lemma lem7652790 : term170 = term163.
Proof. exact (TRANS (@lem7652773) (@lem7652789)). Qed.
Lemma lem7652792 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7652793 : term163 = term102.
Proof. exact (@lem7652792 term102). Qed.
Lemma lem7652794 : term170 = term102.
Proof. exact (TRANS (@lem7652790) (@lem7652793)). Qed.
Lemma lem7652795 (_98526 : int) : (term118 _98526) = (term118 _98526).
Proof. exact (eq_refl (term118 _98526)). Qed.
Lemma lem7652796 (_98526 : int) : (term161 _98526) = (term183 _98526).
Proof. exact (MK_COMB (@lem7652795 _98526) (@lem7652794)). Qed.
Lemma lem7652797 (_98526 : int) : (term183 _98526) = (real_of_int _98526).
Proof. exact (@lem1982723 (real_of_int _98526)). Qed.
Lemma lem7652798 (_98526 : int) : (term161 _98526) = (real_of_int _98526).
Proof. exact (TRANS (@lem7652796 _98526) (@lem7652797 _98526)). Qed.
Lemma lem7652800 (_98526 : int) : (term160 _98526) = (real_of_int _98526).
Proof. exact (TRANS (@lem7652764 _98526) (@lem7652798 _98526)). Qed.
Lemma lem7652801 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7652802 (_98526 : int) : (term184 _98526) = (term185 _98526).
Proof. exact (MK_COMB (@lem7652801) (@lem7652800 _98526)). Qed.
Lemma lem7652803 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7652804 (_98526 : int) : (term159 _98526) = (term186 _98526).
Proof. exact (MK_COMB (@lem7652802 _98526) (@lem7652803)). Qed.
Lemma lem7652805 (_98526 : int) : (term105 _98526) = (term186 _98526).
Proof. exact (TRANS (@lem7652758 _98526) (@lem7652804 _98526)). Qed.
Lemma lem7652806 (_98527 : int) : (term105 _98527) = (term159 _98527).
Proof. exact (@lem1988287 (real_of_int _98527) term102). Qed.
Lemma lem7652812 (_98527 : int) : (term160 _98527) = (term161 _98527).
Proof. exact (@lem1982792 (real_of_int _98527) term102). Qed.
Lemma lem7652814 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7652815 : term102 = term163.
Proof. exact (@lem7652814 (NUMERAL 0)). Qed.
Lemma lem7652817 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7652818 : term166 = term167.
Proof. exact (@lem7652817 term117). Qed.
Lemma lem7652819 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7652820 : term168 = term169.
Proof. exact (MK_COMB (@lem7652819) (@lem7652818)). Qed.
Lemma lem7652821 : term170 = term171.
Proof. exact (MK_COMB (@lem7652820) (@lem7652815)). Qed.
Lemma lem7652822 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7652824 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7652825 : term175 = term176.
Proof. exact (@lem7652824 term117 term117). Qed.
Lemma lem7652826 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7652827 : term178 = term117.
Proof. exact (EQ_MP (@lem7652826) (@lem940073)). Qed.
Lemma lem7652828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7652829 : term176 = term116.
Proof. exact (MK_COMB (@lem7652828) (@lem7652827)). Qed.
Lemma lem7652830 : term175 = term116.
Proof. exact (TRANS (@lem7652825) (@lem7652829)). Qed.
Lemma lem7652832 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7652833 : term170 = term102.
Proof. exact (@lem7652832 term117). Qed.
Lemma lem7652834 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7652835 : term180 = term181.
Proof. exact (MK_COMB (@lem7652834) (@lem7652833)). Qed.
Lemma lem7652836 : term172 = term163.
Proof. exact (MK_COMB (@lem7652835) (@lem7652830)). Qed.
Lemma lem7652837 : term171 = term163.
Proof. exact (TRANS (@lem7652822) (@lem7652836)). Qed.
Lemma lem7652838 : term170 = term163.
Proof. exact (TRANS (@lem7652821) (@lem7652837)). Qed.
Lemma lem7652840 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7652841 : term163 = term102.
Proof. exact (@lem7652840 term102). Qed.
Lemma lem7652842 : term170 = term102.
Proof. exact (TRANS (@lem7652838) (@lem7652841)). Qed.
Lemma lem7652843 (_98527 : int) : (term118 _98527) = (term118 _98527).
Proof. exact (eq_refl (term118 _98527)). Qed.
Lemma lem7652844 (_98527 : int) : (term161 _98527) = (term183 _98527).
Proof. exact (MK_COMB (@lem7652843 _98527) (@lem7652842)). Qed.
Lemma lem7652845 (_98527 : int) : (term183 _98527) = (real_of_int _98527).
Proof. exact (@lem1982723 (real_of_int _98527)). Qed.
Lemma lem7652846 (_98527 : int) : (term161 _98527) = (real_of_int _98527).
Proof. exact (TRANS (@lem7652844 _98527) (@lem7652845 _98527)). Qed.
Lemma lem7652848 (_98527 : int) : (term160 _98527) = (real_of_int _98527).
Proof. exact (TRANS (@lem7652812 _98527) (@lem7652846 _98527)). Qed.
Lemma lem7652849 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7652850 (_98527 : int) : (term184 _98527) = (term185 _98527).
Proof. exact (MK_COMB (@lem7652849) (@lem7652848 _98527)). Qed.
Lemma lem7652851 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7652852 (_98527 : int) : (term159 _98527) = (term186 _98527).
Proof. exact (MK_COMB (@lem7652850 _98527) (@lem7652851)). Qed.
Lemma lem7652853 (_98527 : int) : (term105 _98527) = (term186 _98527).
Proof. exact (TRANS (@lem7652806 _98527) (@lem7652852 _98527)). Qed.
Lemma lem7652854 (_98528 : int) : (term105 _98528) = (term159 _98528).
Proof. exact (@lem1988287 (real_of_int _98528) term102). Qed.
Lemma lem7652860 (_98528 : int) : (term160 _98528) = (term161 _98528).
Proof. exact (@lem1982792 (real_of_int _98528) term102). Qed.
Lemma lem7652862 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7652863 : term102 = term163.
Proof. exact (@lem7652862 (NUMERAL 0)). Qed.
Lemma lem7652865 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7652866 : term166 = term167.
Proof. exact (@lem7652865 term117). Qed.
Lemma lem7652867 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7652868 : term168 = term169.
Proof. exact (MK_COMB (@lem7652867) (@lem7652866)). Qed.
Lemma lem7652869 : term170 = term171.
Proof. exact (MK_COMB (@lem7652868) (@lem7652863)). Qed.
Lemma lem7652870 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7652872 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7652873 : term175 = term176.
Proof. exact (@lem7652872 term117 term117). Qed.
Lemma lem7652874 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7652875 : term178 = term117.
Proof. exact (EQ_MP (@lem7652874) (@lem940073)). Qed.
Lemma lem7652876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7652877 : term176 = term116.
Proof. exact (MK_COMB (@lem7652876) (@lem7652875)). Qed.
Lemma lem7652878 : term175 = term116.
Proof. exact (TRANS (@lem7652873) (@lem7652877)). Qed.
Lemma lem7652880 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7652881 : term170 = term102.
Proof. exact (@lem7652880 term117). Qed.
Lemma lem7652882 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7652883 : term180 = term181.
Proof. exact (MK_COMB (@lem7652882) (@lem7652881)). Qed.
Lemma lem7652884 : term172 = term163.
Proof. exact (MK_COMB (@lem7652883) (@lem7652878)). Qed.
Lemma lem7652885 : term171 = term163.
Proof. exact (TRANS (@lem7652870) (@lem7652884)). Qed.
Lemma lem7652886 : term170 = term163.
Proof. exact (TRANS (@lem7652869) (@lem7652885)). Qed.
Lemma lem7652888 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7652889 : term163 = term102.
Proof. exact (@lem7652888 term102). Qed.
Lemma lem7652890 : term170 = term102.
Proof. exact (TRANS (@lem7652886) (@lem7652889)). Qed.
Lemma lem7652891 (_98528 : int) : (term118 _98528) = (term118 _98528).
Proof. exact (eq_refl (term118 _98528)). Qed.
Lemma lem7652892 (_98528 : int) : (term161 _98528) = (term183 _98528).
Proof. exact (MK_COMB (@lem7652891 _98528) (@lem7652890)). Qed.
Lemma lem7652893 (_98528 : int) : (term183 _98528) = (real_of_int _98528).
Proof. exact (@lem1982723 (real_of_int _98528)). Qed.
Lemma lem7652894 (_98528 : int) : (term161 _98528) = (real_of_int _98528).
Proof. exact (TRANS (@lem7652892 _98528) (@lem7652893 _98528)). Qed.
Lemma lem7652896 (_98528 : int) : (term160 _98528) = (real_of_int _98528).
Proof. exact (TRANS (@lem7652860 _98528) (@lem7652894 _98528)). Qed.
Lemma lem7652897 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7652898 (_98528 : int) : (term184 _98528) = (term185 _98528).
Proof. exact (MK_COMB (@lem7652897) (@lem7652896 _98528)). Qed.
Lemma lem7652899 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7652900 (_98528 : int) : (term159 _98528) = (term186 _98528).
Proof. exact (MK_COMB (@lem7652898 _98528) (@lem7652899)). Qed.
Lemma lem7652901 (_98528 : int) : (term105 _98528) = (term186 _98528).
Proof. exact (TRANS (@lem7652854 _98528) (@lem7652900 _98528)). Qed.
Lemma lem7652902 (_98528 : int) (_98526 : int) (_98527 : int) : ((real_of_int _98528) = (term107 _98526 _98527)) = ((term187 _98528 _98526 _98527) = term102).
Proof. exact (@lem1988293 (real_of_int _98528) (term107 _98526 _98527)). Qed.
Lemma lem7652914 (_98528 : int) (_98526 : int) (_98527 : int) : (term187 _98528 _98526 _98527) = (term188 _98528 _98526 _98527).
Proof. exact (@lem1982792 (real_of_int _98528) (term107 _98526 _98527)). Qed.
Lemma lem7652921 (_98526 : int) (_98527 : int) : (term189 _98526 _98527) = (term190 _98526 _98527).
Proof. exact (@lem1982781 (real_of_int _98526) term166 (real_of_int _98527)). Qed.
Lemma lem7652922 (_98528 : int) : (term118 _98528) = (term118 _98528).
Proof. exact (eq_refl (term118 _98528)). Qed.
Lemma lem7652923 (_98528 : int) (_98526 : int) (_98527 : int) : (term188 _98528 _98526 _98527) = (term191 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7652922 _98528) (@lem7652921 _98526 _98527)). Qed.
Lemma lem7652924 (_98526 : int) (_98528 : int) (_98527 : int) : (term191 _98528 _98526 _98527) = (term192 _98526 _98528 _98527).
Proof. exact (@lem1982757 (term193 _98526) (real_of_int _98528) (term193 _98527)). Qed.
Lemma lem7652925 (_98527 : int) (_98528 : int) : (term194 _98528 _98527) = (term195 _98527 _98528).
Proof. exact (@lem1982761 (term193 _98527) (real_of_int _98528)). Qed.
Lemma lem7652926 (_98526 : int) : (term196 _98526) = (term196 _98526).
Proof. exact (eq_refl (term196 _98526)). Qed.
Lemma lem7652927 (_98526 : int) (_98527 : int) (_98528 : int) : (term192 _98526 _98528 _98527) = (term197 _98526 _98527 _98528).
Proof. exact (MK_COMB (@lem7652926 _98526) (@lem7652925 _98527 _98528)). Qed.
Lemma lem7652928 (_98526 : int) (_98527 : int) (_98528 : int) : (term191 _98528 _98526 _98527) = (term197 _98526 _98527 _98528).
Proof. exact (TRANS (@lem7652924 _98526 _98528 _98527) (@lem7652927 _98526 _98527 _98528)). Qed.
Lemma lem7652929 (_98526 : int) (_98527 : int) (_98528 : int) : (term188 _98528 _98526 _98527) = (term197 _98526 _98527 _98528).
Proof. exact (TRANS (@lem7652923 _98528 _98526 _98527) (@lem7652928 _98526 _98527 _98528)). Qed.
Lemma lem7652931 (_98526 : int) (_98527 : int) (_98528 : int) : (term187 _98528 _98526 _98527) = (term197 _98526 _98527 _98528).
Proof. exact (TRANS (@lem7652914 _98528 _98526 _98527) (@lem7652929 _98526 _98527 _98528)). Qed.
Lemma lem7652932 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7652933 (_98526 : int) (_98527 : int) (_98528 : int) : (term198 _98528 _98526 _98527) = (term199 _98526 _98527 _98528).
Proof. exact (MK_COMB (@lem7652932) (@lem7652931 _98526 _98527 _98528)). Qed.
Lemma lem7652934 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7652935 (_98526 : int) (_98527 : int) (_98528 : int) : ((term187 _98528 _98526 _98527) = term102) = ((term197 _98526 _98527 _98528) = term102).
Proof. exact (MK_COMB (@lem7652933 _98526 _98527 _98528) (@lem7652934)). Qed.
Lemma lem7652936 (_98526 : int) (_98527 : int) (_98528 : int) : ((real_of_int _98528) = (term107 _98526 _98527)) = ((term197 _98526 _98527 _98528) = term102).
Proof. exact (TRANS (@lem7652902 _98528 _98526 _98527) (@lem7652935 _98526 _98527 _98528)). Qed.
Lemma lem7652937 (_98526 : int) (_98528 : int) : (term122 _98528 _98526) = (term200 _98526 _98528).
Proof. exact (@lem1988287 (real_of_int _98526) (term119 _98528)). Qed.
Lemma lem7652949 (_98526 : int) (_98528 : int) : (term201 _98526 _98528) = (term202 _98526 _98528).
Proof. exact (@lem1982792 (real_of_int _98526) (term119 _98528)). Qed.
Lemma lem7652950 (_98528 : int) : (term203 _98528) = (term204 _98528).
Proof. exact (@lem1982781 (real_of_int _98528) term166 term116). Qed.
Lemma lem7652952 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7652953 : term116 = term205.
Proof. exact (@lem7652952 term117). Qed.
Lemma lem7652955 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7652956 : term166 = term167.
Proof. exact (@lem7652955 term117). Qed.
Lemma lem7652957 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7652958 : term168 = term169.
Proof. exact (MK_COMB (@lem7652957) (@lem7652956)). Qed.
Lemma lem7652959 : term206 = term207.
Proof. exact (MK_COMB (@lem7652958) (@lem7652953)). Qed.
Lemma lem7652960 : term207 = term208.
Proof. exact (@lem1981613 term166 term116 term116 term116). Qed.
Lemma lem7652962 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7652963 : term175 = term176.
Proof. exact (@lem7652962 term117 term117). Qed.
Lemma lem7652964 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7652965 : term178 = term117.
Proof. exact (EQ_MP (@lem7652964) (@lem940073)). Qed.
Lemma lem7652966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7652967 : term176 = term116.
Proof. exact (MK_COMB (@lem7652966) (@lem7652965)). Qed.
Lemma lem7652968 : term175 = term116.
Proof. exact (TRANS (@lem7652963) (@lem7652967)). Qed.
Lemma lem7652970 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7652971 : term206 = term211.
Proof. exact (@lem7652970 term117 term117). Qed.
Lemma lem7652972 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7652973 : term178 = term117.
Proof. exact (EQ_MP (@lem7652972) (@lem940073)). Qed.
Lemma lem7652974 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7652975 : term176 = term116.
Proof. exact (MK_COMB (@lem7652974) (@lem7652973)). Qed.
Lemma lem7652976 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7652977 : term211 = term166.
Proof. exact (MK_COMB (@lem7652976) (@lem7652975)). Qed.
Lemma lem7652978 : term206 = term166.
Proof. exact (TRANS (@lem7652971) (@lem7652977)). Qed.
Lemma lem7652979 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7652980 : term212 = term213.
Proof. exact (MK_COMB (@lem7652979) (@lem7652978)). Qed.
Lemma lem7652981 : term208 = term167.
Proof. exact (MK_COMB (@lem7652980) (@lem7652968)). Qed.
Lemma lem7652982 : term207 = term167.
Proof. exact (TRANS (@lem7652960) (@lem7652981)). Qed.
Lemma lem7652983 : term206 = term167.
Proof. exact (TRANS (@lem7652959) (@lem7652982)). Qed.
Lemma lem7652985 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7652986 : term167 = term166.
Proof. exact (@lem7652985 term166). Qed.
Lemma lem7652987 : term206 = term166.
Proof. exact (TRANS (@lem7652983) (@lem7652986)). Qed.
Lemma lem7652990 (_98528 : int) : (term196 _98528) = (term196 _98528).
Proof. exact (eq_refl (term196 _98528)). Qed.
Lemma lem7652991 (_98528 : int) : (term204 _98528) = (term214 _98528).
Proof. exact (MK_COMB (@lem7652990 _98528) (@lem7652987)). Qed.
Lemma lem7652992 (_98528 : int) : (term203 _98528) = (term214 _98528).
Proof. exact (TRANS (@lem7652950 _98528) (@lem7652991 _98528)). Qed.
Lemma lem7652993 (_98526 : int) : (term118 _98526) = (term118 _98526).
Proof. exact (eq_refl (term118 _98526)). Qed.
Lemma lem7652996 (_98526 : int) (_98528 : int) : (term202 _98526 _98528) = (term215 _98526 _98528).
Proof. exact (MK_COMB (@lem7652993 _98526) (@lem7652992 _98528)). Qed.
Lemma lem7652998 (_98526 : int) (_98528 : int) : (term201 _98526 _98528) = (term215 _98526 _98528).
Proof. exact (TRANS (@lem7652949 _98526 _98528) (@lem7652996 _98526 _98528)). Qed.
Lemma lem7652999 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7653000 (_98526 : int) (_98528 : int) : (term216 _98526 _98528) = (term217 _98526 _98528).
Proof. exact (MK_COMB (@lem7652999) (@lem7652998 _98526 _98528)). Qed.
Lemma lem7653001 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7653002 (_98526 : int) (_98528 : int) : (term200 _98526 _98528) = (term218 _98526 _98528).
Proof. exact (MK_COMB (@lem7653000 _98526 _98528) (@lem7653001)). Qed.
Lemma lem7653003 (_98526 : int) (_98528 : int) : (term122 _98528 _98526) = (term218 _98526 _98528).
Proof. exact (TRANS (@lem7652937 _98526 _98528) (@lem7653002 _98526 _98528)). Qed.
Lemma lem7653004 (_98527 : int) : ((real_of_int _98527) = term102) = ((term160 _98527) = term102).
Proof. exact (@lem1988293 (real_of_int _98527) term102). Qed.
Lemma lem7653010 (_98527 : int) : (term160 _98527) = (term161 _98527).
Proof. exact (@lem1982792 (real_of_int _98527) term102). Qed.
Lemma lem7653012 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653013 : term102 = term163.
Proof. exact (@lem7653012 (NUMERAL 0)). Qed.
Lemma lem7653015 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7653016 : term166 = term167.
Proof. exact (@lem7653015 term117). Qed.
Lemma lem7653017 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7653018 : term168 = term169.
Proof. exact (MK_COMB (@lem7653017) (@lem7653016)). Qed.
Lemma lem7653019 : term170 = term171.
Proof. exact (MK_COMB (@lem7653018) (@lem7653013)). Qed.
Lemma lem7653020 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7653022 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653023 : term175 = term176.
Proof. exact (@lem7653022 term117 term117). Qed.
Lemma lem7653024 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653025 : term178 = term117.
Proof. exact (EQ_MP (@lem7653024) (@lem940073)). Qed.
Lemma lem7653026 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653027 : term176 = term116.
Proof. exact (MK_COMB (@lem7653026) (@lem7653025)). Qed.
Lemma lem7653028 : term175 = term116.
Proof. exact (TRANS (@lem7653023) (@lem7653027)). Qed.
Lemma lem7653030 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7653031 : term170 = term102.
Proof. exact (@lem7653030 term117). Qed.
Lemma lem7653032 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7653033 : term180 = term181.
Proof. exact (MK_COMB (@lem7653032) (@lem7653031)). Qed.
Lemma lem7653034 : term172 = term163.
Proof. exact (MK_COMB (@lem7653033) (@lem7653028)). Qed.
Lemma lem7653035 : term171 = term163.
Proof. exact (TRANS (@lem7653020) (@lem7653034)). Qed.
Lemma lem7653036 : term170 = term163.
Proof. exact (TRANS (@lem7653019) (@lem7653035)). Qed.
Lemma lem7653038 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7653039 : term163 = term102.
Proof. exact (@lem7653038 term102). Qed.
Lemma lem7653040 : term170 = term102.
Proof. exact (TRANS (@lem7653036) (@lem7653039)). Qed.
Lemma lem7653041 (_98527 : int) : (term118 _98527) = (term118 _98527).
Proof. exact (eq_refl (term118 _98527)). Qed.
Lemma lem7653042 (_98527 : int) : (term161 _98527) = (term183 _98527).
Proof. exact (MK_COMB (@lem7653041 _98527) (@lem7653040)). Qed.
Lemma lem7653043 (_98527 : int) : (term183 _98527) = (real_of_int _98527).
Proof. exact (@lem1982723 (real_of_int _98527)). Qed.
Lemma lem7653044 (_98527 : int) : (term161 _98527) = (real_of_int _98527).
Proof. exact (TRANS (@lem7653042 _98527) (@lem7653043 _98527)). Qed.
Lemma lem7653046 (_98527 : int) : (term160 _98527) = (real_of_int _98527).
Proof. exact (TRANS (@lem7653010 _98527) (@lem7653044 _98527)). Qed.
Lemma lem7653047 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7653048 (_98527 : int) : (term219 _98527) = (term108 _98527).
Proof. exact (MK_COMB (@lem7653047) (@lem7653046 _98527)). Qed.
Lemma lem7653049 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7653050 (_98527 : int) : ((term160 _98527) = term102) = ((real_of_int _98527) = term102).
Proof. exact (MK_COMB (@lem7653048 _98527) (@lem7653049)). Qed.
Lemma lem7653051 (_98527 : int) : ((real_of_int _98527) = term102) = ((real_of_int _98527) = term102).
Proof. exact (TRANS (@lem7653004 _98527) (@lem7653050 _98527)). Qed.
Lemma lem7653052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7653053 (_98526 : int) (_98528 : int) : (term123 _98528 _98526) = (term220 _98526 _98528).
Proof. exact (MK_COMB (@lem7653052) (@lem7653003 _98526 _98528)). Qed.
Lemma lem7653054 (_98526 : int) (_98528 : int) (_98527 : int) : (term124 _98528 _98526 _98527) = (term221 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7653053 _98526 _98528) (@lem7653051 _98527)). Qed.
Lemma lem7653055 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7653056 (_98526 : int) (_98527 : int) (_98528 : int) : (term125 _98528 _98526 _98527) = (term222 _98526 _98527 _98528).
Proof. exact (MK_COMB (@lem7653055) (@lem7652936 _98526 _98527 _98528)). Qed.
Lemma lem7653057 (_98526 : int) (_98528 : int) (_98527 : int) : (term126 _98528 _98526 _98527) = (term223 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7653056 _98526 _98527 _98528) (@lem7653054 _98526 _98528 _98527)). Qed.
Lemma lem7653058 (_98528 : int) (_98526 : int) : (term122 _98526 _98528) = (term200 _98528 _98526).
Proof. exact (@lem1988287 (real_of_int _98528) (term119 _98526)). Qed.
Lemma lem7653070 (_98528 : int) (_98526 : int) : (term201 _98528 _98526) = (term202 _98528 _98526).
Proof. exact (@lem1982792 (real_of_int _98528) (term119 _98526)). Qed.
Lemma lem7653071 (_98526 : int) : (term203 _98526) = (term204 _98526).
Proof. exact (@lem1982781 (real_of_int _98526) term166 term116). Qed.
Lemma lem7653073 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653074 : term116 = term205.
Proof. exact (@lem7653073 term117). Qed.
Lemma lem7653076 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7653077 : term166 = term167.
Proof. exact (@lem7653076 term117). Qed.
Lemma lem7653078 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7653079 : term168 = term169.
Proof. exact (MK_COMB (@lem7653078) (@lem7653077)). Qed.
Lemma lem7653080 : term206 = term207.
Proof. exact (MK_COMB (@lem7653079) (@lem7653074)). Qed.
Lemma lem7653081 : term207 = term208.
Proof. exact (@lem1981613 term166 term116 term116 term116). Qed.
Lemma lem7653083 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653084 : term175 = term176.
Proof. exact (@lem7653083 term117 term117). Qed.
Lemma lem7653085 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653086 : term178 = term117.
Proof. exact (EQ_MP (@lem7653085) (@lem940073)). Qed.
Lemma lem7653087 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653088 : term176 = term116.
Proof. exact (MK_COMB (@lem7653087) (@lem7653086)). Qed.
Lemma lem7653089 : term175 = term116.
Proof. exact (TRANS (@lem7653084) (@lem7653088)). Qed.
Lemma lem7653091 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7653092 : term206 = term211.
Proof. exact (@lem7653091 term117 term117). Qed.
Lemma lem7653093 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653094 : term178 = term117.
Proof. exact (EQ_MP (@lem7653093) (@lem940073)). Qed.
Lemma lem7653095 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653096 : term176 = term116.
Proof. exact (MK_COMB (@lem7653095) (@lem7653094)). Qed.
Lemma lem7653097 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7653098 : term211 = term166.
Proof. exact (MK_COMB (@lem7653097) (@lem7653096)). Qed.
Lemma lem7653099 : term206 = term166.
Proof. exact (TRANS (@lem7653092) (@lem7653098)). Qed.
Lemma lem7653100 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7653101 : term212 = term213.
Proof. exact (MK_COMB (@lem7653100) (@lem7653099)). Qed.
Lemma lem7653102 : term208 = term167.
Proof. exact (MK_COMB (@lem7653101) (@lem7653089)). Qed.
Lemma lem7653103 : term207 = term167.
Proof. exact (TRANS (@lem7653081) (@lem7653102)). Qed.
Lemma lem7653104 : term206 = term167.
Proof. exact (TRANS (@lem7653080) (@lem7653103)). Qed.
Lemma lem7653106 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7653107 : term167 = term166.
Proof. exact (@lem7653106 term166). Qed.
Lemma lem7653108 : term206 = term166.
Proof. exact (TRANS (@lem7653104) (@lem7653107)). Qed.
Lemma lem7653111 (_98526 : int) : (term196 _98526) = (term196 _98526).
Proof. exact (eq_refl (term196 _98526)). Qed.
Lemma lem7653112 (_98526 : int) : (term204 _98526) = (term214 _98526).
Proof. exact (MK_COMB (@lem7653111 _98526) (@lem7653108)). Qed.
Lemma lem7653113 (_98526 : int) : (term203 _98526) = (term214 _98526).
Proof. exact (TRANS (@lem7653071 _98526) (@lem7653112 _98526)). Qed.
Lemma lem7653114 (_98528 : int) : (term118 _98528) = (term118 _98528).
Proof. exact (eq_refl (term118 _98528)). Qed.
Lemma lem7653115 (_98528 : int) (_98526 : int) : (term202 _98528 _98526) = (term215 _98528 _98526).
Proof. exact (MK_COMB (@lem7653114 _98528) (@lem7653113 _98526)). Qed.
Lemma lem7653120 (_98526 : int) (_98528 : int) : (term215 _98528 _98526) = (term224 _98526 _98528).
Proof. exact (@lem1982757 (term193 _98526) (real_of_int _98528) term166). Qed.
Lemma lem7653121 (_98526 : int) (_98528 : int) : (term202 _98528 _98526) = (term224 _98526 _98528).
Proof. exact (TRANS (@lem7653115 _98528 _98526) (@lem7653120 _98526 _98528)). Qed.
Lemma lem7653123 (_98526 : int) (_98528 : int) : (term201 _98528 _98526) = (term224 _98526 _98528).
Proof. exact (TRANS (@lem7653070 _98528 _98526) (@lem7653121 _98526 _98528)). Qed.
Lemma lem7653124 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7653125 (_98526 : int) (_98528 : int) : (term216 _98528 _98526) = (term225 _98526 _98528).
Proof. exact (MK_COMB (@lem7653124) (@lem7653123 _98526 _98528)). Qed.
Lemma lem7653126 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7653127 (_98526 : int) (_98528 : int) : (term200 _98528 _98526) = (term226 _98526 _98528).
Proof. exact (MK_COMB (@lem7653125 _98526 _98528) (@lem7653126)). Qed.
Lemma lem7653128 (_98526 : int) (_98528 : int) : (term122 _98526 _98528) = (term226 _98526 _98528).
Proof. exact (TRANS (@lem7653058 _98528 _98526) (@lem7653127 _98526 _98528)). Qed.
Lemma lem7653129 (_98527 : int) : (term562 _98527) = (term569 _98527).
Proof. exact (@lem1988287 term116 (term119 _98527)). Qed.
Lemma lem7653141 (_98527 : int) : (term570 _98527) = (term571 _98527).
Proof. exact (@lem1982792 term116 (term119 _98527)). Qed.
Lemma lem7653142 (_98527 : int) : (term203 _98527) = (term204 _98527).
Proof. exact (@lem1982781 (real_of_int _98527) term166 term116). Qed.
Lemma lem7653144 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653145 : term116 = term205.
Proof. exact (@lem7653144 term117). Qed.
Lemma lem7653147 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7653148 : term166 = term167.
Proof. exact (@lem7653147 term117). Qed.
Lemma lem7653149 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7653150 : term168 = term169.
Proof. exact (MK_COMB (@lem7653149) (@lem7653148)). Qed.
Lemma lem7653151 : term206 = term207.
Proof. exact (MK_COMB (@lem7653150) (@lem7653145)). Qed.
Lemma lem7653152 : term207 = term208.
Proof. exact (@lem1981613 term166 term116 term116 term116). Qed.
Lemma lem7653154 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653155 : term175 = term176.
Proof. exact (@lem7653154 term117 term117). Qed.
Lemma lem7653156 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653157 : term178 = term117.
Proof. exact (EQ_MP (@lem7653156) (@lem940073)). Qed.
Lemma lem7653158 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653159 : term176 = term116.
Proof. exact (MK_COMB (@lem7653158) (@lem7653157)). Qed.
Lemma lem7653160 : term175 = term116.
Proof. exact (TRANS (@lem7653155) (@lem7653159)). Qed.
Lemma lem7653162 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7653163 : term206 = term211.
Proof. exact (@lem7653162 term117 term117). Qed.
Lemma lem7653164 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653165 : term178 = term117.
Proof. exact (EQ_MP (@lem7653164) (@lem940073)). Qed.
Lemma lem7653166 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653167 : term176 = term116.
Proof. exact (MK_COMB (@lem7653166) (@lem7653165)). Qed.
Lemma lem7653168 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7653169 : term211 = term166.
Proof. exact (MK_COMB (@lem7653168) (@lem7653167)). Qed.
Lemma lem7653170 : term206 = term166.
Proof. exact (TRANS (@lem7653163) (@lem7653169)). Qed.
Lemma lem7653171 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7653172 : term212 = term213.
Proof. exact (MK_COMB (@lem7653171) (@lem7653170)). Qed.
Lemma lem7653173 : term208 = term167.
Proof. exact (MK_COMB (@lem7653172) (@lem7653160)). Qed.
Lemma lem7653174 : term207 = term167.
Proof. exact (TRANS (@lem7653152) (@lem7653173)). Qed.
Lemma lem7653175 : term206 = term167.
Proof. exact (TRANS (@lem7653151) (@lem7653174)). Qed.
Lemma lem7653177 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7653178 : term167 = term166.
Proof. exact (@lem7653177 term166). Qed.
Lemma lem7653179 : term206 = term166.
Proof. exact (TRANS (@lem7653175) (@lem7653178)). Qed.
Lemma lem7653182 (_98527 : int) : (term196 _98527) = (term196 _98527).
Proof. exact (eq_refl (term196 _98527)). Qed.
Lemma lem7653183 (_98527 : int) : (term204 _98527) = (term214 _98527).
Proof. exact (MK_COMB (@lem7653182 _98527) (@lem7653179)). Qed.
Lemma lem7653184 (_98527 : int) : (term203 _98527) = (term214 _98527).
Proof. exact (TRANS (@lem7653142 _98527) (@lem7653183 _98527)). Qed.
Lemma lem7653185 : term572 = term572.
Proof. exact (eq_refl term572). Qed.
Lemma lem7653186 (_98527 : int) : (term571 _98527) = (term573 _98527).
Proof. exact (MK_COMB (@lem7653185) (@lem7653184 _98527)). Qed.
Lemma lem7653187 (_98527 : int) : (term573 _98527) = (term574 _98527).
Proof. exact (@lem1982757 (term193 _98527) term116 term166). Qed.
Lemma lem7653189 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7653190 : term166 = term167.
Proof. exact (@lem7653189 term117). Qed.
Lemma lem7653192 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653193 : term116 = term205.
Proof. exact (@lem7653192 term117). Qed.
Lemma lem7653194 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7653195 : term572 = term575.
Proof. exact (MK_COMB (@lem7653194) (@lem7653193)). Qed.
Lemma lem7653196 : term576 = term577.
Proof. exact (MK_COMB (@lem7653195) (@lem7653190)). Qed.
Lemma lem7653197 : term578.
Proof. exact (@lem1981473 term116 term116 term166 term116 term102 term116). Qed.
Lemma lem7653199 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653200 : term313 = term319.
Proof. exact (@lem7653199 (NUMERAL 0) term117). Qed.
Lemma lem7653201 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653202 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653203 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653202 h1) (fun h1 : term319 = True => @lem7653201)). Qed.
Lemma lem7653204 : term319 = True.
Proof. exact (EQ_MP (@lem7653203) (@lem7653201)). Qed.
Lemma lem7653205 : term313 = True.
Proof. exact (TRANS (@lem7653200) (@lem7653204)). Qed.
Lemma lem7653206 : True = term313.
Proof. exact (SYM (@lem7653205)). Qed.
Lemma lem7653207 : term313.
Proof. exact (EQ_MP (@lem7653206) (@lem0)). Qed.
Lemma lem7653208 : term579.
Proof. exact (@lem7653197 (@lem7653207)). Qed.
Lemma lem7653210 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653211 : term313 = term319.
Proof. exact (@lem7653210 (NUMERAL 0) term117). Qed.
Lemma lem7653212 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653213 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653214 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653213 h1) (fun h1 : term319 = True => @lem7653212)). Qed.
Lemma lem7653215 : term319 = True.
Proof. exact (EQ_MP (@lem7653214) (@lem7653212)). Qed.
Lemma lem7653216 : term313 = True.
Proof. exact (TRANS (@lem7653211) (@lem7653215)). Qed.
Lemma lem7653217 : True = term313.
Proof. exact (SYM (@lem7653216)). Qed.
Lemma lem7653218 : term313.
Proof. exact (EQ_MP (@lem7653217) (@lem0)). Qed.
Lemma lem7653219 : term580.
Proof. exact (@lem7653208 (@lem7653218)). Qed.
Lemma lem7653221 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653222 : term313 = term319.
Proof. exact (@lem7653221 (NUMERAL 0) term117). Qed.
Lemma lem7653223 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653224 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653225 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653224 h1) (fun h1 : term319 = True => @lem7653223)). Qed.
Lemma lem7653226 : term319 = True.
Proof. exact (EQ_MP (@lem7653225) (@lem7653223)). Qed.
Lemma lem7653227 : term313 = True.
Proof. exact (TRANS (@lem7653222) (@lem7653226)). Qed.
Lemma lem7653228 : True = term313.
Proof. exact (SYM (@lem7653227)). Qed.
Lemma lem7653229 : term313.
Proof. exact (EQ_MP (@lem7653228) (@lem0)). Qed.
Lemma lem7653230 : term581.
Proof. exact (@lem7653219 (@lem7653229)). Qed.
Lemma lem7653232 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7653233 : term206 = term211.
Proof. exact (@lem7653232 term117 term117). Qed.
Lemma lem7653234 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653235 : term178 = term117.
Proof. exact (EQ_MP (@lem7653234) (@lem940073)). Qed.
Lemma lem7653236 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653237 : term176 = term116.
Proof. exact (MK_COMB (@lem7653236) (@lem7653235)). Qed.
Lemma lem7653238 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7653239 : term211 = term166.
Proof. exact (MK_COMB (@lem7653238) (@lem7653237)). Qed.
Lemma lem7653240 : term206 = term166.
Proof. exact (TRANS (@lem7653233) (@lem7653239)). Qed.
Lemma lem7653242 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653243 : term175 = term176.
Proof. exact (@lem7653242 term117 term117). Qed.
Lemma lem7653244 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653245 : term178 = term117.
Proof. exact (EQ_MP (@lem7653244) (@lem940073)). Qed.
Lemma lem7653246 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653247 : term176 = term116.
Proof. exact (MK_COMB (@lem7653246) (@lem7653245)). Qed.
Lemma lem7653248 : term175 = term116.
Proof. exact (TRANS (@lem7653243) (@lem7653247)). Qed.
Lemma lem7653249 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7653250 : term582 = term572.
Proof. exact (MK_COMB (@lem7653249) (@lem7653248)). Qed.
Lemma lem7653251 : term583 = term576.
Proof. exact (MK_COMB (@lem7653250) (@lem7653240)). Qed.
Lemma lem7653253 (m : nat) : (term584 m) = term102.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem7653254 : term576 = term102.
Proof. exact (@lem7653253 term117). Qed.
Lemma lem7653255 : term583 = term102.
Proof. exact (TRANS (@lem7653251) (@lem7653254)). Qed.
Lemma lem7653256 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7653257 : term585 = term375.
Proof. exact (MK_COMB (@lem7653256) (@lem7653255)). Qed.
Lemma lem7653258 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7653259 : term586 = term324.
Proof. exact (MK_COMB (@lem7653257) (@lem7653258)). Qed.
Lemma lem7653261 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7653262 : term324 = term102.
Proof. exact (@lem7653261 term117). Qed.
Lemma lem7653263 : term586 = term102.
Proof. exact (TRANS (@lem7653259) (@lem7653262)). Qed.
Lemma lem7653265 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653266 : term175 = term176.
Proof. exact (@lem7653265 term117 term117). Qed.
Lemma lem7653267 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653268 : term178 = term117.
Proof. exact (EQ_MP (@lem7653267) (@lem940073)). Qed.
Lemma lem7653269 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653270 : term176 = term116.
Proof. exact (MK_COMB (@lem7653269) (@lem7653268)). Qed.
Lemma lem7653271 : term175 = term116.
Proof. exact (TRANS (@lem7653266) (@lem7653270)). Qed.
Lemma lem7653272 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7653273 : term377 = term324.
Proof. exact (MK_COMB (@lem7653272) (@lem7653271)). Qed.
Lemma lem7653275 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7653276 : term324 = term102.
Proof. exact (@lem7653275 term117). Qed.
Lemma lem7653277 : term377 = term102.
Proof. exact (TRANS (@lem7653273) (@lem7653276)). Qed.
Lemma lem7653278 : term102 = term377.
Proof. exact (SYM (@lem7653277)). Qed.
Lemma lem7653279 : term586 = term377.
Proof. exact (TRANS (@lem7653263) (@lem7653278)). Qed.
Lemma lem7653280 : term577 = term163.
Proof. exact (@lem7653230 (@lem7653279)). Qed.
Lemma lem7653281 : term576 = term163.
Proof. exact (TRANS (@lem7653196) (@lem7653280)). Qed.
Lemma lem7653283 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7653284 : term163 = term102.
Proof. exact (@lem7653283 term102). Qed.
Lemma lem7653285 : term576 = term102.
Proof. exact (TRANS (@lem7653281) (@lem7653284)). Qed.
Lemma lem7653286 (_98527 : int) : (term196 _98527) = (term196 _98527).
Proof. exact (eq_refl (term196 _98527)). Qed.
Lemma lem7653287 (_98527 : int) : (term574 _98527) = (term587 _98527).
Proof. exact (MK_COMB (@lem7653286 _98527) (@lem7653285)). Qed.
Lemma lem7653288 (_98527 : int) : (term573 _98527) = (term587 _98527).
Proof. exact (TRANS (@lem7653187 _98527) (@lem7653287 _98527)). Qed.
Lemma lem7653289 (_98527 : int) : (term587 _98527) = (term193 _98527).
Proof. exact (@lem1982723 (term193 _98527)). Qed.
Lemma lem7653290 (_98527 : int) : (term573 _98527) = (term193 _98527).
Proof. exact (TRANS (@lem7653288 _98527) (@lem7653289 _98527)). Qed.
Lemma lem7653291 (_98527 : int) : (term571 _98527) = (term193 _98527).
Proof. exact (TRANS (@lem7653186 _98527) (@lem7653290 _98527)). Qed.
Lemma lem7653293 (_98527 : int) : (term570 _98527) = (term193 _98527).
Proof. exact (TRANS (@lem7653141 _98527) (@lem7653291 _98527)). Qed.
Lemma lem7653294 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7653295 (_98527 : int) : (term588 _98527) = (term589 _98527).
Proof. exact (MK_COMB (@lem7653294) (@lem7653293 _98527)). Qed.
Lemma lem7653296 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7653297 (_98527 : int) : (term569 _98527) = (term590 _98527).
Proof. exact (MK_COMB (@lem7653295 _98527) (@lem7653296)). Qed.
Lemma lem7653298 (_98527 : int) : (term562 _98527) = (term590 _98527).
Proof. exact (TRANS (@lem7653129 _98527) (@lem7653297 _98527)). Qed.
Lemma lem7653299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7653300 (_98526 : int) (_98528 : int) : (term123 _98526 _98528) = (term252 _98526 _98528).
Proof. exact (MK_COMB (@lem7653299) (@lem7653128 _98526 _98528)). Qed.
Lemma lem7653301 (_98526 : int) (_98528 : int) (_98527 : int) : (term563 _98526 _98528 _98527) = (term591 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7653300 _98526 _98528) (@lem7653298 _98527)). Qed.
Lemma lem7653302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7653303 (_98526 : int) (_98528 : int) (_98527 : int) : (term151 _98528 _98526 _98527) = (term254 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7653302) (@lem7653057 _98526 _98528 _98527)). Qed.
Lemma lem7653304 (_98526 : int) (_98528 : int) (_98527 : int) : (term564 _98526 _98528 _98527) = (term592 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7653303 _98526 _98528 _98527) (@lem7653301 _98526 _98528 _98527)). Qed.
Lemma lem7653305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7653306 (_98528 : int) : (term153 _98528) = (term256 _98528).
Proof. exact (MK_COMB (@lem7653305) (@lem7652901 _98528)). Qed.
Lemma lem7653307 (_98526 : int) (_98528 : int) (_98527 : int) : (term565 _98526 _98528 _98527) = (term593 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7653306 _98528) (@lem7653304 _98526 _98528 _98527)). Qed.
Lemma lem7653308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7653309 (_98527 : int) : (term153 _98527) = (term256 _98527).
Proof. exact (MK_COMB (@lem7653308) (@lem7652853 _98527)). Qed.
Lemma lem7653310 (_98526 : int) (_98528 : int) (_98527 : int) : (term566 _98526 _98528 _98527) = (term594 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7653309 _98527) (@lem7653307 _98526 _98528 _98527)). Qed.
Lemma lem7653311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7653312 (_98526 : int) : (term153 _98526) = (term256 _98526).
Proof. exact (MK_COMB (@lem7653311) (@lem7652805 _98526)). Qed.
Lemma lem7653313 (_98526 : int) (_98528 : int) (_98527 : int) : (term567 _98526 _98528 _98527) = (term595 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7653312 _98526) (@lem7653310 _98526 _98528 _98527)). Qed.
Lemma lem7653320 (_98526 : int) (_98528 : int) (_98527 : int) : (term568 _98526 _98528 _98527) = (term595 _98526 _98528 _98527).
Proof. exact (TRANS (@lem7652757 _98526 _98528 _98527) (@lem7653313 _98526 _98528 _98527)). Qed.
Lemma lem7653349 (_98526 : int) (_98528 : int) (_98527 : int) : (term592 _98526 _98528 _98527) = (term596 _98526 _98528 _98527).
Proof. exact (@lem19367 ((term197 _98526 _98527 _98528) = term102) (term221 _98526 _98528 _98527) (term591 _98526 _98528 _98527)). Qed.
Lemma lem7653352 (_98528 : int) : (term256 _98528) = (term256 _98528).
Proof. exact (eq_refl (term256 _98528)). Qed.
Lemma lem7653353 (_98526 : int) (_98528 : int) (_98527 : int) : (term593 _98526 _98528 _98527) = (term597 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7653352 _98528) (@lem7653349 _98526 _98528 _98527)). Qed.
Lemma lem7653360 (_98526 : int) (_98528 : int) (_98527 : int) : (term597 _98526 _98528 _98527) = (term598 _98526 _98528 _98527).
Proof. exact (@lem19158 (term599 _98526 _98528 _98527) (term186 _98528) (term600 _98526 _98528 _98527)). Qed.
Lemma lem7653361 (_98526 : int) (_98528 : int) (_98527 : int) : (term593 _98526 _98528 _98527) = (term598 _98526 _98528 _98527).
Proof. exact (TRANS (@lem7653353 _98526 _98528 _98527) (@lem7653360 _98526 _98528 _98527)). Qed.
Lemma lem7653364 (_98527 : int) : (term256 _98527) = (term256 _98527).
Proof. exact (eq_refl (term256 _98527)). Qed.
Lemma lem7653365 (_98526 : int) (_98528 : int) (_98527 : int) : (term594 _98526 _98528 _98527) = (term601 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7653364 _98527) (@lem7653361 _98526 _98528 _98527)). Qed.
Lemma lem7653372 (_98526 : int) (_98528 : int) (_98527 : int) : (term601 _98526 _98528 _98527) = (term602 _98526 _98528 _98527).
Proof. exact (@lem19158 (term603 _98526 _98528 _98527) (term186 _98527) (term604 _98526 _98528 _98527)). Qed.
Lemma lem7653373 (_98526 : int) (_98528 : int) (_98527 : int) : (term594 _98526 _98528 _98527) = (term602 _98526 _98528 _98527).
Proof. exact (TRANS (@lem7653365 _98526 _98528 _98527) (@lem7653372 _98526 _98528 _98527)). Qed.
Lemma lem7653376 (_98526 : int) : (term256 _98526) = (term256 _98526).
Proof. exact (eq_refl (term256 _98526)). Qed.
Lemma lem7653377 (_98526 : int) (_98528 : int) (_98527 : int) : (term595 _98526 _98528 _98527) = (term605 _98526 _98528 _98527).
Proof. exact (MK_COMB (@lem7653376 _98526) (@lem7653373 _98526 _98528 _98527)). Qed.
Lemma lem7653384 (_98526 : int) (_98528 : int) (_98527 : int) : (term605 _98526 _98528 _98527) = (term606 _98526 _98528 _98527).
Proof. exact (@lem19158 (term607 _98526 _98528 _98527) (term186 _98526) (term608 _98526 _98528 _98527)). Qed.
Lemma lem7653385 (_98526 : int) (_98528 : int) (_98527 : int) : (term595 _98526 _98528 _98527) = (term606 _98526 _98528 _98527).
Proof. exact (TRANS (@lem7653377 _98526 _98528 _98527) (@lem7653384 _98526 _98528 _98527)). Qed.
Lemma lem7653386 (_98526 : int) (_98528 : int) (_98527 : int) : (term568 _98526 _98528 _98527) = (term606 _98526 _98528 _98527).
Proof. exact (TRANS (@lem7653320 _98526 _98528 _98527) (@lem7653385 _98526 _98528 _98527)). Qed.
Lemma lem7653396 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term606 _98526 _98528 _98527) : term606 _98526 _98528 _98527.
Proof. exact (h1). Qed.
Lemma lem7653397 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term609 _98526 _98528 _98527.
Proof. exact (h1). Qed.
Lemma lem7653398 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term607 _98526 _98528 _98527.
Proof. exact (proj2 (@lem7653397 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653400 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term603 _98526 _98528 _98527.
Proof. exact (proj2 (@lem7653398 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653402 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term599 _98526 _98528 _98527.
Proof. exact (proj2 (@lem7653400 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653404 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term591 _98526 _98528 _98527.
Proof. exact (proj2 (@lem7653402 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653405 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : (term197 _98526 _98527 _98528) = term102.
Proof. exact (proj1 (@lem7653402 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653406 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term590 _98527.
Proof. exact (proj2 (@lem7653404 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653407 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term226 _98526 _98528.
Proof. exact (proj1 (@lem7653404 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653409 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7653410 : term312 = term313.
Proof. exact (@lem7653409 term102 term116). Qed.
Lemma lem7653412 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653413 : term116 = term205.
Proof. exact (@lem7653412 term117). Qed.
Lemma lem7653415 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653416 : term102 = term163.
Proof. exact (@lem7653415 (NUMERAL 0)). Qed.
Lemma lem7653417 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7653418 : term314 = term315.
Proof. exact (MK_COMB (@lem7653417) (@lem7653416)). Qed.
Lemma lem7653419 : term313 = term316.
Proof. exact (MK_COMB (@lem7653418) (@lem7653413)). Qed.
Lemma lem7653420 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7653422 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653423 : term313 = term319.
Proof. exact (@lem7653422 (NUMERAL 0) term117). Qed.
Lemma lem7653424 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653425 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653426 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653425 h1) (fun h1 : term319 = True => @lem7653424)). Qed.
Lemma lem7653427 : term319 = True.
Proof. exact (EQ_MP (@lem7653426) (@lem7653424)). Qed.
Lemma lem7653428 : term313 = True.
Proof. exact (TRANS (@lem7653423) (@lem7653427)). Qed.
Lemma lem7653429 : True = term313.
Proof. exact (SYM (@lem7653428)). Qed.
Lemma lem7653430 : term313.
Proof. exact (EQ_MP (@lem7653429) (@lem0)). Qed.
Lemma lem7653431 : term321.
Proof. exact (@lem7653420 (@lem7653430)). Qed.
Lemma lem7653433 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653434 : term313 = term319.
Proof. exact (@lem7653433 (NUMERAL 0) term117). Qed.
Lemma lem7653435 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653436 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653437 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653436 h1) (fun h1 : term319 = True => @lem7653435)). Qed.
Lemma lem7653438 : term319 = True.
Proof. exact (EQ_MP (@lem7653437) (@lem7653435)). Qed.
Lemma lem7653439 : term313 = True.
Proof. exact (TRANS (@lem7653434) (@lem7653438)). Qed.
Lemma lem7653440 : True = term313.
Proof. exact (SYM (@lem7653439)). Qed.
Lemma lem7653441 : term313.
Proof. exact (EQ_MP (@lem7653440) (@lem0)). Qed.
Lemma lem7653442 : term316 = term322.
Proof. exact (@lem7653431 (@lem7653441)). Qed.
Lemma lem7653444 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653445 : term175 = term176.
Proof. exact (@lem7653444 term117 term117). Qed.
Lemma lem7653446 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653447 : term178 = term117.
Proof. exact (EQ_MP (@lem7653446) (@lem940073)). Qed.
Lemma lem7653448 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653449 : term176 = term116.
Proof. exact (MK_COMB (@lem7653448) (@lem7653447)). Qed.
Lemma lem7653450 : term175 = term116.
Proof. exact (TRANS (@lem7653445) (@lem7653449)). Qed.
Lemma lem7653452 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7653453 : term324 = term102.
Proof. exact (@lem7653452 term117). Qed.
Lemma lem7653454 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7653455 : term325 = term314.
Proof. exact (MK_COMB (@lem7653454) (@lem7653453)). Qed.
Lemma lem7653456 : term322 = term313.
Proof. exact (MK_COMB (@lem7653455) (@lem7653450)). Qed.
Lemma lem7653458 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653459 : term313 = term319.
Proof. exact (@lem7653458 (NUMERAL 0) term117). Qed.
Lemma lem7653460 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653461 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653462 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653461 h1) (fun h1 : term319 = True => @lem7653460)). Qed.
Lemma lem7653463 : term319 = True.
Proof. exact (EQ_MP (@lem7653462) (@lem7653460)). Qed.
Lemma lem7653464 : term313 = True.
Proof. exact (TRANS (@lem7653459) (@lem7653463)). Qed.
Lemma lem7653465 : term322 = True.
Proof. exact (TRANS (@lem7653456) (@lem7653464)). Qed.
Lemma lem7653466 : term316 = True.
Proof. exact (TRANS (@lem7653442) (@lem7653465)). Qed.
Lemma lem7653467 : term313 = True.
Proof. exact (TRANS (@lem7653419) (@lem7653466)). Qed.
Lemma lem7653468 : term312 = True.
Proof. exact (TRANS (@lem7653410) (@lem7653467)). Qed.
Lemma lem7653469 : True = term312.
Proof. exact (SYM (@lem7653468)). Qed.
Lemma lem7653470 : term312.
Proof. exact (EQ_MP (@lem7653469) (@lem0)). Qed.
Lemma lem7653471 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term418 _98526 _98528.
Proof. exact (conj (@lem7653470) (@lem7653407 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653473 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7653474 (_98526 : int) (_98528 : int) : term419 _98526 _98528.
Proof. exact (@lem7653473 term116 (term224 _98526 _98528)). Qed.
Lemma lem7653475 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term420 _98526 _98528.
Proof. exact (@lem7653474 _98526 _98528 (@lem7653471 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653476 (_98526 : int) (_98528 : int) : (term421 _98526 _98528) = (term224 _98526 _98528).
Proof. exact (@lem1982733 (term224 _98526 _98528)). Qed.
Lemma lem7653477 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7653478 (_98526 : int) (_98528 : int) : (term422 _98526 _98528) = (term225 _98526 _98528).
Proof. exact (MK_COMB (@lem7653477) (@lem7653476 _98526 _98528)). Qed.
Lemma lem7653479 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7653480 (_98526 : int) (_98528 : int) : (term420 _98526 _98528) = (term226 _98526 _98528).
Proof. exact (MK_COMB (@lem7653478 _98526 _98528) (@lem7653479)). Qed.
Lemma lem7653481 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term226 _98526 _98528.
Proof. exact (EQ_MP (@lem7653480 _98526 _98528) (@lem7653475 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653483 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7653484 : term312 = term313.
Proof. exact (@lem7653483 term102 term116). Qed.
Lemma lem7653486 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653487 : term116 = term205.
Proof. exact (@lem7653486 term117). Qed.
Lemma lem7653489 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653490 : term102 = term163.
Proof. exact (@lem7653489 (NUMERAL 0)). Qed.
Lemma lem7653491 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7653492 : term314 = term315.
Proof. exact (MK_COMB (@lem7653491) (@lem7653490)). Qed.
Lemma lem7653493 : term313 = term316.
Proof. exact (MK_COMB (@lem7653492) (@lem7653487)). Qed.
Lemma lem7653494 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7653496 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653497 : term313 = term319.
Proof. exact (@lem7653496 (NUMERAL 0) term117). Qed.
Lemma lem7653498 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653499 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653500 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653499 h1) (fun h1 : term319 = True => @lem7653498)). Qed.
Lemma lem7653501 : term319 = True.
Proof. exact (EQ_MP (@lem7653500) (@lem7653498)). Qed.
Lemma lem7653502 : term313 = True.
Proof. exact (TRANS (@lem7653497) (@lem7653501)). Qed.
Lemma lem7653503 : True = term313.
Proof. exact (SYM (@lem7653502)). Qed.
Lemma lem7653504 : term313.
Proof. exact (EQ_MP (@lem7653503) (@lem0)). Qed.
Lemma lem7653505 : term321.
Proof. exact (@lem7653494 (@lem7653504)). Qed.
Lemma lem7653507 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653508 : term313 = term319.
Proof. exact (@lem7653507 (NUMERAL 0) term117). Qed.
Lemma lem7653509 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653510 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653511 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653510 h1) (fun h1 : term319 = True => @lem7653509)). Qed.
Lemma lem7653512 : term319 = True.
Proof. exact (EQ_MP (@lem7653511) (@lem7653509)). Qed.
Lemma lem7653513 : term313 = True.
Proof. exact (TRANS (@lem7653508) (@lem7653512)). Qed.
Lemma lem7653514 : True = term313.
Proof. exact (SYM (@lem7653513)). Qed.
Lemma lem7653515 : term313.
Proof. exact (EQ_MP (@lem7653514) (@lem0)). Qed.
Lemma lem7653516 : term316 = term322.
Proof. exact (@lem7653505 (@lem7653515)). Qed.
Lemma lem7653518 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653519 : term175 = term176.
Proof. exact (@lem7653518 term117 term117). Qed.
Lemma lem7653520 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653521 : term178 = term117.
Proof. exact (EQ_MP (@lem7653520) (@lem940073)). Qed.
Lemma lem7653522 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653523 : term176 = term116.
Proof. exact (MK_COMB (@lem7653522) (@lem7653521)). Qed.
Lemma lem7653524 : term175 = term116.
Proof. exact (TRANS (@lem7653519) (@lem7653523)). Qed.
Lemma lem7653526 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7653527 : term324 = term102.
Proof. exact (@lem7653526 term117). Qed.
Lemma lem7653528 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7653529 : term325 = term314.
Proof. exact (MK_COMB (@lem7653528) (@lem7653527)). Qed.
Lemma lem7653530 : term322 = term313.
Proof. exact (MK_COMB (@lem7653529) (@lem7653524)). Qed.
Lemma lem7653532 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653533 : term313 = term319.
Proof. exact (@lem7653532 (NUMERAL 0) term117). Qed.
Lemma lem7653534 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653535 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653536 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653535 h1) (fun h1 : term319 = True => @lem7653534)). Qed.
Lemma lem7653537 : term319 = True.
Proof. exact (EQ_MP (@lem7653536) (@lem7653534)). Qed.
Lemma lem7653538 : term313 = True.
Proof. exact (TRANS (@lem7653533) (@lem7653537)). Qed.
Lemma lem7653539 : term322 = True.
Proof. exact (TRANS (@lem7653530) (@lem7653538)). Qed.
Lemma lem7653540 : term316 = True.
Proof. exact (TRANS (@lem7653516) (@lem7653539)). Qed.
Lemma lem7653541 : term313 = True.
Proof. exact (TRANS (@lem7653493) (@lem7653540)). Qed.
Lemma lem7653542 : term312 = True.
Proof. exact (TRANS (@lem7653484) (@lem7653541)). Qed.
Lemma lem7653543 : True = term312.
Proof. exact (SYM (@lem7653542)). Qed.
Lemma lem7653544 : term312.
Proof. exact (EQ_MP (@lem7653543) (@lem0)). Qed.
Lemma lem7653545 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term610 _98527.
Proof. exact (conj (@lem7653544) (@lem7653406 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653547 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7653548 (_98527 : int) : term611 _98527.
Proof. exact (@lem7653547 term116 (term193 _98527)). Qed.
Lemma lem7653549 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term612 _98527.
Proof. exact (@lem7653548 _98527 (@lem7653545 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653550 (_98527 : int) : (term613 _98527) = (term193 _98527).
Proof. exact (@lem1982733 (term193 _98527)). Qed.
Lemma lem7653551 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7653552 (_98527 : int) : (term614 _98527) = (term589 _98527).
Proof. exact (MK_COMB (@lem7653551) (@lem7653550 _98527)). Qed.
Lemma lem7653553 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7653554 (_98527 : int) : (term612 _98527) = (term590 _98527).
Proof. exact (MK_COMB (@lem7653552 _98527) (@lem7653553)). Qed.
Lemma lem7653555 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term590 _98527.
Proof. exact (EQ_MP (@lem7653554 _98527) (@lem7653549 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653557 (y : real) : term332 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7653558 (_98526 : int) (_98527 : int) (_98528 : int) : term333 _98526 _98527 _98528.
Proof. exact (@lem7653557 (term197 _98526 _98527 _98528)). Qed.
Lemma lem7653559 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term334 _98526 _98527 _98528.
Proof. exact (@lem7653558 _98526 _98527 _98528 (@lem7653405 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653560 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term335 _98526 _98527 _98528.
Proof. exact (@lem7653559 _98526 _98528 _98527 h1 term166). Qed.
Lemma lem7653561 (_98526 : int) (_98527 : int) (_98528 : int) : (term335 _98526 _98527 _98528) = ((term336 _98526 _98527 _98528) = term102).
Proof. exact (eq_refl (term335 _98526 _98527 _98528)). Qed.
Lemma lem7653562 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : (term336 _98526 _98527 _98528) = term102.
Proof. exact (EQ_MP (@lem7653561 _98526 _98527 _98528) (@lem7653560 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653563 (_98526 : int) (_98527 : int) (_98528 : int) : (term336 _98526 _98527 _98528) = (term337 _98526 _98527 _98528).
Proof. exact (@lem1982781 (term193 _98526) term166 (term195 _98527 _98528)). Qed.
Lemma lem7653564 (_98527 : int) (_98528 : int) : (term338 _98527 _98528) = (term339 _98527 _98528).
Proof. exact (@lem1982781 (term193 _98527) term166 (real_of_int _98528)). Qed.
Lemma lem7653565 (_98528 : int) : (term193 _98528) = (term193 _98528).
Proof. exact (eq_refl (term193 _98528)). Qed.
Lemma lem7653566 (_98527 : int) : (term340 _98527) = (term341 _98527).
Proof. exact (@lem1982749 term166 term166 (real_of_int _98527)). Qed.
Lemma lem7653568 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7653569 : term166 = term167.
Proof. exact (@lem7653568 term117). Qed.
Lemma lem7653571 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7653572 : term166 = term167.
Proof. exact (@lem7653571 term117). Qed.
Lemma lem7653573 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7653574 : term168 = term169.
Proof. exact (MK_COMB (@lem7653573) (@lem7653572)). Qed.
Lemma lem7653575 : term342 = term343.
Proof. exact (MK_COMB (@lem7653574) (@lem7653569)). Qed.
Lemma lem7653576 : term343 = term344.
Proof. exact (@lem1981613 term166 term166 term116 term116). Qed.
Lemma lem7653578 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653579 : term175 = term176.
Proof. exact (@lem7653578 term117 term117). Qed.
Lemma lem7653580 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653581 : term178 = term117.
Proof. exact (EQ_MP (@lem7653580) (@lem940073)). Qed.
Lemma lem7653582 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653583 : term176 = term116.
Proof. exact (MK_COMB (@lem7653582) (@lem7653581)). Qed.
Lemma lem7653584 : term175 = term116.
Proof. exact (TRANS (@lem7653579) (@lem7653583)). Qed.
Lemma lem7653586 (m : nat) (n : nat) : (term345 m n) = (term174 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7653587 : term342 = term176.
Proof. exact (@lem7653586 term117 term117). Qed.
Lemma lem7653588 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653589 : term178 = term117.
Proof. exact (EQ_MP (@lem7653588) (@lem940073)). Qed.
Lemma lem7653590 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653591 : term176 = term116.
Proof. exact (MK_COMB (@lem7653590) (@lem7653589)). Qed.
Lemma lem7653592 : term342 = term116.
Proof. exact (TRANS (@lem7653587) (@lem7653591)). Qed.
Lemma lem7653593 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7653594 : term346 = term347.
Proof. exact (MK_COMB (@lem7653593) (@lem7653592)). Qed.
Lemma lem7653595 : term344 = term205.
Proof. exact (MK_COMB (@lem7653594) (@lem7653584)). Qed.
Lemma lem7653596 : term343 = term205.
Proof. exact (TRANS (@lem7653576) (@lem7653595)). Qed.
Lemma lem7653597 : term342 = term205.
Proof. exact (TRANS (@lem7653575) (@lem7653596)). Qed.
Lemma lem7653599 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7653600 : term205 = term116.
Proof. exact (@lem7653599 term116). Qed.
Lemma lem7653601 : term342 = term116.
Proof. exact (TRANS (@lem7653597) (@lem7653600)). Qed.
Lemma lem7653602 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7653603 : term348 = term349.
Proof. exact (MK_COMB (@lem7653602) (@lem7653601)). Qed.
Lemma lem7653604 (_98527 : int) : (real_of_int _98527) = (real_of_int _98527).
Proof. exact (eq_refl (real_of_int _98527)). Qed.
Lemma lem7653605 (_98527 : int) : (term341 _98527) = (term350 _98527).
Proof. exact (MK_COMB (@lem7653603) (@lem7653604 _98527)). Qed.
Lemma lem7653606 (_98527 : int) : (term340 _98527) = (term350 _98527).
Proof. exact (TRANS (@lem7653566 _98527) (@lem7653605 _98527)). Qed.
Lemma lem7653607 (_98527 : int) : (term350 _98527) = (real_of_int _98527).
Proof. exact (@lem1982709 (real_of_int _98527)). Qed.
Lemma lem7653608 (_98527 : int) : (term340 _98527) = (real_of_int _98527).
Proof. exact (TRANS (@lem7653606 _98527) (@lem7653607 _98527)). Qed.
Lemma lem7653609 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7653610 (_98527 : int) : (term351 _98527) = (term118 _98527).
Proof. exact (MK_COMB (@lem7653609) (@lem7653608 _98527)). Qed.
Lemma lem7653611 (_98527 : int) (_98528 : int) : (term339 _98527 _98528) = (term194 _98527 _98528).
Proof. exact (MK_COMB (@lem7653610 _98527) (@lem7653565 _98528)). Qed.
Lemma lem7653612 (_98527 : int) (_98528 : int) : (term338 _98527 _98528) = (term194 _98527 _98528).
Proof. exact (TRANS (@lem7653564 _98527 _98528) (@lem7653611 _98527 _98528)). Qed.
Lemma lem7653613 (_98526 : int) : (term340 _98526) = (term341 _98526).
Proof. exact (@lem1982749 term166 term166 (real_of_int _98526)). Qed.
Lemma lem7653615 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7653616 : term166 = term167.
Proof. exact (@lem7653615 term117). Qed.
Lemma lem7653618 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7653619 : term166 = term167.
Proof. exact (@lem7653618 term117). Qed.
Lemma lem7653620 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7653621 : term168 = term169.
Proof. exact (MK_COMB (@lem7653620) (@lem7653619)). Qed.
Lemma lem7653622 : term342 = term343.
Proof. exact (MK_COMB (@lem7653621) (@lem7653616)). Qed.
Lemma lem7653623 : term343 = term344.
Proof. exact (@lem1981613 term166 term166 term116 term116). Qed.
Lemma lem7653625 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653626 : term175 = term176.
Proof. exact (@lem7653625 term117 term117). Qed.
Lemma lem7653627 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653628 : term178 = term117.
Proof. exact (EQ_MP (@lem7653627) (@lem940073)). Qed.
Lemma lem7653629 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653630 : term176 = term116.
Proof. exact (MK_COMB (@lem7653629) (@lem7653628)). Qed.
Lemma lem7653631 : term175 = term116.
Proof. exact (TRANS (@lem7653626) (@lem7653630)). Qed.
Lemma lem7653633 (m : nat) (n : nat) : (term345 m n) = (term174 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem7653634 : term342 = term176.
Proof. exact (@lem7653633 term117 term117). Qed.
Lemma lem7653635 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653636 : term178 = term117.
Proof. exact (EQ_MP (@lem7653635) (@lem940073)). Qed.
Lemma lem7653637 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653638 : term176 = term116.
Proof. exact (MK_COMB (@lem7653637) (@lem7653636)). Qed.
Lemma lem7653639 : term342 = term116.
Proof. exact (TRANS (@lem7653634) (@lem7653638)). Qed.
Lemma lem7653640 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7653641 : term346 = term347.
Proof. exact (MK_COMB (@lem7653640) (@lem7653639)). Qed.
Lemma lem7653642 : term344 = term205.
Proof. exact (MK_COMB (@lem7653641) (@lem7653631)). Qed.
Lemma lem7653643 : term343 = term205.
Proof. exact (TRANS (@lem7653623) (@lem7653642)). Qed.
Lemma lem7653644 : term342 = term205.
Proof. exact (TRANS (@lem7653622) (@lem7653643)). Qed.
Lemma lem7653646 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7653647 : term205 = term116.
Proof. exact (@lem7653646 term116). Qed.
Lemma lem7653648 : term342 = term116.
Proof. exact (TRANS (@lem7653644) (@lem7653647)). Qed.
Lemma lem7653649 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7653650 : term348 = term349.
Proof. exact (MK_COMB (@lem7653649) (@lem7653648)). Qed.
Lemma lem7653651 (_98526 : int) : (real_of_int _98526) = (real_of_int _98526).
Proof. exact (eq_refl (real_of_int _98526)). Qed.
Lemma lem7653652 (_98526 : int) : (term341 _98526) = (term350 _98526).
Proof. exact (MK_COMB (@lem7653650) (@lem7653651 _98526)). Qed.
Lemma lem7653653 (_98526 : int) : (term340 _98526) = (term350 _98526).
Proof. exact (TRANS (@lem7653613 _98526) (@lem7653652 _98526)). Qed.
Lemma lem7653654 (_98526 : int) : (term350 _98526) = (real_of_int _98526).
Proof. exact (@lem1982709 (real_of_int _98526)). Qed.
Lemma lem7653655 (_98526 : int) : (term340 _98526) = (real_of_int _98526).
Proof. exact (TRANS (@lem7653653 _98526) (@lem7653654 _98526)). Qed.
Lemma lem7653656 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7653657 (_98526 : int) : (term351 _98526) = (term118 _98526).
Proof. exact (MK_COMB (@lem7653656) (@lem7653655 _98526)). Qed.
Lemma lem7653658 (_98526 : int) (_98527 : int) (_98528 : int) : (term337 _98526 _98527 _98528) = (term352 _98526 _98527 _98528).
Proof. exact (MK_COMB (@lem7653657 _98526) (@lem7653612 _98527 _98528)). Qed.
Lemma lem7653659 (_98526 : int) (_98527 : int) (_98528 : int) : (term336 _98526 _98527 _98528) = (term352 _98526 _98527 _98528).
Proof. exact (TRANS (@lem7653563 _98526 _98527 _98528) (@lem7653658 _98526 _98527 _98528)). Qed.
Lemma lem7653660 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7653661 (_98526 : int) (_98527 : int) (_98528 : int) : (term353 _98526 _98527 _98528) = (term354 _98526 _98527 _98528).
Proof. exact (MK_COMB (@lem7653660) (@lem7653659 _98526 _98527 _98528)). Qed.
Lemma lem7653662 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7653663 (_98526 : int) (_98527 : int) (_98528 : int) : ((term336 _98526 _98527 _98528) = term102) = ((term352 _98526 _98527 _98528) = term102).
Proof. exact (MK_COMB (@lem7653661 _98526 _98527 _98528) (@lem7653662)). Qed.
Lemma lem7653664 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : (term352 _98526 _98527 _98528) = term102.
Proof. exact (EQ_MP (@lem7653663 _98526 _98527 _98528) (@lem7653562 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653665 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term615 _98526 _98528 _98527.
Proof. exact (conj (@lem7653664 _98526 _98528 _98527 h1) (@lem7653555 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653667 (x : real) (y : real) : term356 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem7653668 (_98526 : int) (_98528 : int) (_98527 : int) : term616 _98526 _98528 _98527.
Proof. exact (@lem7653667 (term352 _98526 _98527 _98528) (term193 _98527)). Qed.
Lemma lem7653669 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term617 _98526 _98528 _98527.
Proof. exact (@lem7653668 _98526 _98528 _98527 (@lem7653665 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653670 (_98526 : int) (_98528 : int) (_98527 : int) : (term618 _98526 _98528 _98527) = (term619 _98526 _98528 _98527).
Proof. exact (@lem1982755 (real_of_int _98526) (term194 _98527 _98528) (term193 _98527)). Qed.
Lemma lem7653671 (_98527 : int) (_98528 : int) : (term620 _98528 _98527) = (term621 _98527 _98528).
Proof. exact (@lem1982759 (real_of_int _98527) (term193 _98527) (term193 _98528)). Qed.
Lemma lem7653672 (_98527 : int) : (term361 _98527) = (term362 _98527).
Proof. exact (@lem1982715 term166 (real_of_int _98527)). Qed.
Lemma lem7653674 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653675 : term116 = term205.
Proof. exact (@lem7653674 term117). Qed.
Lemma lem7653677 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7653678 : term166 = term167.
Proof. exact (@lem7653677 term117). Qed.
Lemma lem7653679 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7653680 : term363 = term364.
Proof. exact (MK_COMB (@lem7653679) (@lem7653678)). Qed.
Lemma lem7653681 : term365 = term366.
Proof. exact (MK_COMB (@lem7653680) (@lem7653675)). Qed.
Lemma lem7653682 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7653684 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653685 : term313 = term319.
Proof. exact (@lem7653684 (NUMERAL 0) term117). Qed.
Lemma lem7653686 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653687 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653688 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653687 h1) (fun h1 : term319 = True => @lem7653686)). Qed.
Lemma lem7653689 : term319 = True.
Proof. exact (EQ_MP (@lem7653688) (@lem7653686)). Qed.
Lemma lem7653690 : term313 = True.
Proof. exact (TRANS (@lem7653685) (@lem7653689)). Qed.
Lemma lem7653691 : True = term313.
Proof. exact (SYM (@lem7653690)). Qed.
Lemma lem7653692 : term313.
Proof. exact (EQ_MP (@lem7653691) (@lem0)). Qed.
Lemma lem7653693 : term368.
Proof. exact (@lem7653682 (@lem7653692)). Qed.
Lemma lem7653695 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653696 : term313 = term319.
Proof. exact (@lem7653695 (NUMERAL 0) term117). Qed.
Lemma lem7653697 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653698 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653699 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653698 h1) (fun h1 : term319 = True => @lem7653697)). Qed.
Lemma lem7653700 : term319 = True.
Proof. exact (EQ_MP (@lem7653699) (@lem7653697)). Qed.
Lemma lem7653701 : term313 = True.
Proof. exact (TRANS (@lem7653696) (@lem7653700)). Qed.
Lemma lem7653702 : True = term313.
Proof. exact (SYM (@lem7653701)). Qed.
Lemma lem7653703 : term313.
Proof. exact (EQ_MP (@lem7653702) (@lem0)). Qed.
Lemma lem7653704 : term369.
Proof. exact (@lem7653693 (@lem7653703)). Qed.
Lemma lem7653706 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653707 : term313 = term319.
Proof. exact (@lem7653706 (NUMERAL 0) term117). Qed.
Lemma lem7653708 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653709 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653710 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653709 h1) (fun h1 : term319 = True => @lem7653708)). Qed.
Lemma lem7653711 : term319 = True.
Proof. exact (EQ_MP (@lem7653710) (@lem7653708)). Qed.
Lemma lem7653712 : term313 = True.
Proof. exact (TRANS (@lem7653707) (@lem7653711)). Qed.
Lemma lem7653713 : True = term313.
Proof. exact (SYM (@lem7653712)). Qed.
Lemma lem7653714 : term313.
Proof. exact (EQ_MP (@lem7653713) (@lem0)). Qed.
Lemma lem7653715 : term370.
Proof. exact (@lem7653704 (@lem7653714)). Qed.
Lemma lem7653717 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653718 : term175 = term176.
Proof. exact (@lem7653717 term117 term117). Qed.
Lemma lem7653719 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653720 : term178 = term117.
Proof. exact (EQ_MP (@lem7653719) (@lem940073)). Qed.
Lemma lem7653721 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653722 : term176 = term116.
Proof. exact (MK_COMB (@lem7653721) (@lem7653720)). Qed.
Lemma lem7653723 : term175 = term116.
Proof. exact (TRANS (@lem7653718) (@lem7653722)). Qed.
Lemma lem7653725 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7653726 : term206 = term211.
Proof. exact (@lem7653725 term117 term117). Qed.
Lemma lem7653727 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653728 : term178 = term117.
Proof. exact (EQ_MP (@lem7653727) (@lem940073)). Qed.
Lemma lem7653729 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653730 : term176 = term116.
Proof. exact (MK_COMB (@lem7653729) (@lem7653728)). Qed.
Lemma lem7653731 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7653732 : term211 = term166.
Proof. exact (MK_COMB (@lem7653731) (@lem7653730)). Qed.
Lemma lem7653733 : term206 = term166.
Proof. exact (TRANS (@lem7653726) (@lem7653732)). Qed.
Lemma lem7653734 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7653735 : term371 = term363.
Proof. exact (MK_COMB (@lem7653734) (@lem7653733)). Qed.
Lemma lem7653736 : term372 = term365.
Proof. exact (MK_COMB (@lem7653735) (@lem7653723)). Qed.
Lemma lem7653738 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7653739 : term365 = term102.
Proof. exact (@lem7653738 term117). Qed.
Lemma lem7653740 : term372 = term102.
Proof. exact (TRANS (@lem7653736) (@lem7653739)). Qed.
Lemma lem7653741 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7653742 : term374 = term375.
Proof. exact (MK_COMB (@lem7653741) (@lem7653740)). Qed.
Lemma lem7653743 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7653744 : term376 = term324.
Proof. exact (MK_COMB (@lem7653742) (@lem7653743)). Qed.
Lemma lem7653746 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7653747 : term324 = term102.
Proof. exact (@lem7653746 term117). Qed.
Lemma lem7653748 : term376 = term102.
Proof. exact (TRANS (@lem7653744) (@lem7653747)). Qed.
Lemma lem7653750 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653751 : term175 = term176.
Proof. exact (@lem7653750 term117 term117). Qed.
Lemma lem7653752 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653753 : term178 = term117.
Proof. exact (EQ_MP (@lem7653752) (@lem940073)). Qed.
Lemma lem7653754 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653755 : term176 = term116.
Proof. exact (MK_COMB (@lem7653754) (@lem7653753)). Qed.
Lemma lem7653756 : term175 = term116.
Proof. exact (TRANS (@lem7653751) (@lem7653755)). Qed.
Lemma lem7653757 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7653758 : term377 = term324.
Proof. exact (MK_COMB (@lem7653757) (@lem7653756)). Qed.
Lemma lem7653760 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7653761 : term324 = term102.
Proof. exact (@lem7653760 term117). Qed.
Lemma lem7653762 : term377 = term102.
Proof. exact (TRANS (@lem7653758) (@lem7653761)). Qed.
Lemma lem7653763 : term102 = term377.
Proof. exact (SYM (@lem7653762)). Qed.
Lemma lem7653764 : term376 = term377.
Proof. exact (TRANS (@lem7653748) (@lem7653763)). Qed.
Lemma lem7653765 : term366 = term163.
Proof. exact (@lem7653715 (@lem7653764)). Qed.
Lemma lem7653766 : term365 = term163.
Proof. exact (TRANS (@lem7653681) (@lem7653765)). Qed.
Lemma lem7653768 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7653769 : term163 = term102.
Proof. exact (@lem7653768 term102). Qed.
Lemma lem7653770 : term365 = term102.
Proof. exact (TRANS (@lem7653766) (@lem7653769)). Qed.
Lemma lem7653771 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7653772 : term378 = term375.
Proof. exact (MK_COMB (@lem7653771) (@lem7653770)). Qed.
Lemma lem7653773 (_98527 : int) : (real_of_int _98527) = (real_of_int _98527).
Proof. exact (eq_refl (real_of_int _98527)). Qed.
Lemma lem7653774 (_98527 : int) : (term362 _98527) = (term379 _98527).
Proof. exact (MK_COMB (@lem7653772) (@lem7653773 _98527)). Qed.
Lemma lem7653775 (_98527 : int) : (term361 _98527) = (term379 _98527).
Proof. exact (TRANS (@lem7653672 _98527) (@lem7653774 _98527)). Qed.
Lemma lem7653776 (_98527 : int) : (term379 _98527) = term102.
Proof. exact (@lem1982719 (real_of_int _98527)). Qed.
Lemma lem7653777 (_98527 : int) : (term361 _98527) = term102.
Proof. exact (TRANS (@lem7653775 _98527) (@lem7653776 _98527)). Qed.
Lemma lem7653778 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7653779 (_98527 : int) : (term380 _98527) = term381.
Proof. exact (MK_COMB (@lem7653778) (@lem7653777 _98527)). Qed.
Lemma lem7653780 (_98528 : int) : (term193 _98528) = (term193 _98528).
Proof. exact (eq_refl (term193 _98528)). Qed.
Lemma lem7653781 (_98527 : int) (_98528 : int) : (term621 _98527 _98528) = (term622 _98528).
Proof. exact (MK_COMB (@lem7653779 _98527) (@lem7653780 _98528)). Qed.
Lemma lem7653782 (_98527 : int) (_98528 : int) : (term620 _98528 _98527) = (term622 _98528).
Proof. exact (TRANS (@lem7653671 _98527 _98528) (@lem7653781 _98527 _98528)). Qed.
Lemma lem7653783 (_98528 : int) : (term622 _98528) = (term193 _98528).
Proof. exact (@lem1982721 (term193 _98528)). Qed.
Lemma lem7653784 (_98527 : int) (_98528 : int) : (term620 _98528 _98527) = (term193 _98528).
Proof. exact (TRANS (@lem7653782 _98527 _98528) (@lem7653783 _98528)). Qed.
Lemma lem7653785 (_98526 : int) : (term118 _98526) = (term118 _98526).
Proof. exact (eq_refl (term118 _98526)). Qed.
Lemma lem7653786 (_98527 : int) (_98526 : int) (_98528 : int) : (term619 _98526 _98528 _98527) = (term194 _98526 _98528).
Proof. exact (MK_COMB (@lem7653785 _98526) (@lem7653784 _98527 _98528)). Qed.
Lemma lem7653787 (_98527 : int) (_98526 : int) (_98528 : int) : (term618 _98526 _98528 _98527) = (term194 _98526 _98528).
Proof. exact (TRANS (@lem7653670 _98526 _98528 _98527) (@lem7653786 _98527 _98526 _98528)). Qed.
Lemma lem7653788 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7653789 (_98527 : int) (_98526 : int) (_98528 : int) : (term623 _98526 _98528 _98527) = (term624 _98526 _98528).
Proof. exact (MK_COMB (@lem7653788) (@lem7653787 _98527 _98526 _98528)). Qed.
Lemma lem7653790 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7653791 (_98527 : int) (_98526 : int) (_98528 : int) : (term617 _98526 _98528 _98527) = (term625 _98526 _98528).
Proof. exact (MK_COMB (@lem7653789 _98527 _98526 _98528) (@lem7653790)). Qed.
Lemma lem7653792 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term625 _98526 _98528.
Proof. exact (EQ_MP (@lem7653791 _98527 _98526 _98528) (@lem7653669 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653794 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7653795 : term312 = term313.
Proof. exact (@lem7653794 term102 term116). Qed.
Lemma lem7653797 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653798 : term116 = term205.
Proof. exact (@lem7653797 term117). Qed.
Lemma lem7653800 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653801 : term102 = term163.
Proof. exact (@lem7653800 (NUMERAL 0)). Qed.
Lemma lem7653802 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7653803 : term314 = term315.
Proof. exact (MK_COMB (@lem7653802) (@lem7653801)). Qed.
Lemma lem7653804 : term313 = term316.
Proof. exact (MK_COMB (@lem7653803) (@lem7653798)). Qed.
Lemma lem7653805 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7653807 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653808 : term313 = term319.
Proof. exact (@lem7653807 (NUMERAL 0) term117). Qed.
Lemma lem7653809 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653810 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653811 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653810 h1) (fun h1 : term319 = True => @lem7653809)). Qed.
Lemma lem7653812 : term319 = True.
Proof. exact (EQ_MP (@lem7653811) (@lem7653809)). Qed.
Lemma lem7653813 : term313 = True.
Proof. exact (TRANS (@lem7653808) (@lem7653812)). Qed.
Lemma lem7653814 : True = term313.
Proof. exact (SYM (@lem7653813)). Qed.
Lemma lem7653815 : term313.
Proof. exact (EQ_MP (@lem7653814) (@lem0)). Qed.
Lemma lem7653816 : term321.
Proof. exact (@lem7653805 (@lem7653815)). Qed.
Lemma lem7653818 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653819 : term313 = term319.
Proof. exact (@lem7653818 (NUMERAL 0) term117). Qed.
Lemma lem7653820 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653821 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653822 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653821 h1) (fun h1 : term319 = True => @lem7653820)). Qed.
Lemma lem7653823 : term319 = True.
Proof. exact (EQ_MP (@lem7653822) (@lem7653820)). Qed.
Lemma lem7653824 : term313 = True.
Proof. exact (TRANS (@lem7653819) (@lem7653823)). Qed.
Lemma lem7653825 : True = term313.
Proof. exact (SYM (@lem7653824)). Qed.
Lemma lem7653826 : term313.
Proof. exact (EQ_MP (@lem7653825) (@lem0)). Qed.
Lemma lem7653827 : term316 = term322.
Proof. exact (@lem7653816 (@lem7653826)). Qed.
Lemma lem7653829 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653830 : term175 = term176.
Proof. exact (@lem7653829 term117 term117). Qed.
Lemma lem7653831 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653832 : term178 = term117.
Proof. exact (EQ_MP (@lem7653831) (@lem940073)). Qed.
Lemma lem7653833 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653834 : term176 = term116.
Proof. exact (MK_COMB (@lem7653833) (@lem7653832)). Qed.
Lemma lem7653835 : term175 = term116.
Proof. exact (TRANS (@lem7653830) (@lem7653834)). Qed.
Lemma lem7653837 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7653838 : term324 = term102.
Proof. exact (@lem7653837 term117). Qed.
Lemma lem7653839 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7653840 : term325 = term314.
Proof. exact (MK_COMB (@lem7653839) (@lem7653838)). Qed.
Lemma lem7653841 : term322 = term313.
Proof. exact (MK_COMB (@lem7653840) (@lem7653835)). Qed.
Lemma lem7653843 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653844 : term313 = term319.
Proof. exact (@lem7653843 (NUMERAL 0) term117). Qed.
Lemma lem7653845 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653846 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653847 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653846 h1) (fun h1 : term319 = True => @lem7653845)). Qed.
Lemma lem7653848 : term319 = True.
Proof. exact (EQ_MP (@lem7653847) (@lem7653845)). Qed.
Lemma lem7653849 : term313 = True.
Proof. exact (TRANS (@lem7653844) (@lem7653848)). Qed.
Lemma lem7653850 : term322 = True.
Proof. exact (TRANS (@lem7653841) (@lem7653849)). Qed.
Lemma lem7653851 : term316 = True.
Proof. exact (TRANS (@lem7653827) (@lem7653850)). Qed.
Lemma lem7653852 : term313 = True.
Proof. exact (TRANS (@lem7653804) (@lem7653851)). Qed.
Lemma lem7653853 : term312 = True.
Proof. exact (TRANS (@lem7653795) (@lem7653852)). Qed.
Lemma lem7653854 : True = term312.
Proof. exact (SYM (@lem7653853)). Qed.
Lemma lem7653855 : term312.
Proof. exact (EQ_MP (@lem7653854) (@lem0)). Qed.
Lemma lem7653856 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term626 _98526 _98528.
Proof. exact (conj (@lem7653855) (@lem7653792 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653858 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7653859 (_98526 : int) (_98528 : int) : term627 _98526 _98528.
Proof. exact (@lem7653858 term116 (term194 _98526 _98528)). Qed.
Lemma lem7653860 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term628 _98526 _98528.
Proof. exact (@lem7653859 _98526 _98528 (@lem7653856 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653861 (_98526 : int) (_98528 : int) : (term629 _98526 _98528) = (term194 _98526 _98528).
Proof. exact (@lem1982733 (term194 _98526 _98528)). Qed.
Lemma lem7653862 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7653863 (_98526 : int) (_98528 : int) : (term630 _98526 _98528) = (term624 _98526 _98528).
Proof. exact (MK_COMB (@lem7653862) (@lem7653861 _98526 _98528)). Qed.
Lemma lem7653864 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7653865 (_98526 : int) (_98528 : int) : (term628 _98526 _98528) = (term625 _98526 _98528).
Proof. exact (MK_COMB (@lem7653863 _98526 _98528) (@lem7653864)). Qed.
Lemma lem7653866 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term625 _98526 _98528.
Proof. exact (EQ_MP (@lem7653865 _98526 _98528) (@lem7653860 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653867 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term631 _98526 _98528.
Proof. exact (conj (@lem7653866 _98526 _98528 _98527 h1) (@lem7653481 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653869 (x : real) (y : real) : term429 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7653870 (_98526 : int) (_98528 : int) : term632 _98526 _98528.
Proof. exact (@lem7653869 (term194 _98526 _98528) (term224 _98526 _98528)). Qed.
Lemma lem7653871 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term633 _98526 _98528.
Proof. exact (@lem7653870 _98526 _98528 (@lem7653867 _98526 _98528 _98527 h1)). Qed.
Lemma lem7653872 (_98526 : int) (_98528 : int) : (term382 _98526 _98528) = (term383 _98526 _98528).
Proof. exact (@lem1982753 (real_of_int _98526) (term193 _98526) (term193 _98528) (term384 _98528)). Qed.
Lemma lem7653873 (_98526 : int) : (term361 _98526) = (term362 _98526).
Proof. exact (@lem1982715 term166 (real_of_int _98526)). Qed.
Lemma lem7653875 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653876 : term116 = term205.
Proof. exact (@lem7653875 term117). Qed.
Lemma lem7653878 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7653879 : term166 = term167.
Proof. exact (@lem7653878 term117). Qed.
Lemma lem7653880 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7653881 : term363 = term364.
Proof. exact (MK_COMB (@lem7653880) (@lem7653879)). Qed.
Lemma lem7653882 : term365 = term366.
Proof. exact (MK_COMB (@lem7653881) (@lem7653876)). Qed.
Lemma lem7653883 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7653885 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653886 : term313 = term319.
Proof. exact (@lem7653885 (NUMERAL 0) term117). Qed.
Lemma lem7653887 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653888 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653889 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653888 h1) (fun h1 : term319 = True => @lem7653887)). Qed.
Lemma lem7653890 : term319 = True.
Proof. exact (EQ_MP (@lem7653889) (@lem7653887)). Qed.
Lemma lem7653891 : term313 = True.
Proof. exact (TRANS (@lem7653886) (@lem7653890)). Qed.
Lemma lem7653892 : True = term313.
Proof. exact (SYM (@lem7653891)). Qed.
Lemma lem7653893 : term313.
Proof. exact (EQ_MP (@lem7653892) (@lem0)). Qed.
Lemma lem7653894 : term368.
Proof. exact (@lem7653883 (@lem7653893)). Qed.
Lemma lem7653896 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653897 : term313 = term319.
Proof. exact (@lem7653896 (NUMERAL 0) term117). Qed.
Lemma lem7653898 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653899 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653900 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653899 h1) (fun h1 : term319 = True => @lem7653898)). Qed.
Lemma lem7653901 : term319 = True.
Proof. exact (EQ_MP (@lem7653900) (@lem7653898)). Qed.
Lemma lem7653902 : term313 = True.
Proof. exact (TRANS (@lem7653897) (@lem7653901)). Qed.
Lemma lem7653903 : True = term313.
Proof. exact (SYM (@lem7653902)). Qed.
Lemma lem7653904 : term313.
Proof. exact (EQ_MP (@lem7653903) (@lem0)). Qed.
Lemma lem7653905 : term369.
Proof. exact (@lem7653894 (@lem7653904)). Qed.
Lemma lem7653907 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653908 : term313 = term319.
Proof. exact (@lem7653907 (NUMERAL 0) term117). Qed.
Lemma lem7653909 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653910 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653911 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653910 h1) (fun h1 : term319 = True => @lem7653909)). Qed.
Lemma lem7653912 : term319 = True.
Proof. exact (EQ_MP (@lem7653911) (@lem7653909)). Qed.
Lemma lem7653913 : term313 = True.
Proof. exact (TRANS (@lem7653908) (@lem7653912)). Qed.
Lemma lem7653914 : True = term313.
Proof. exact (SYM (@lem7653913)). Qed.
Lemma lem7653915 : term313.
Proof. exact (EQ_MP (@lem7653914) (@lem0)). Qed.
Lemma lem7653916 : term370.
Proof. exact (@lem7653905 (@lem7653915)). Qed.
Lemma lem7653918 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653919 : term175 = term176.
Proof. exact (@lem7653918 term117 term117). Qed.
Lemma lem7653920 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653921 : term178 = term117.
Proof. exact (EQ_MP (@lem7653920) (@lem940073)). Qed.
Lemma lem7653922 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653923 : term176 = term116.
Proof. exact (MK_COMB (@lem7653922) (@lem7653921)). Qed.
Lemma lem7653924 : term175 = term116.
Proof. exact (TRANS (@lem7653919) (@lem7653923)). Qed.
Lemma lem7653926 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7653927 : term206 = term211.
Proof. exact (@lem7653926 term117 term117). Qed.
Lemma lem7653928 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653929 : term178 = term117.
Proof. exact (EQ_MP (@lem7653928) (@lem940073)). Qed.
Lemma lem7653930 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653931 : term176 = term116.
Proof. exact (MK_COMB (@lem7653930) (@lem7653929)). Qed.
Lemma lem7653932 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7653933 : term211 = term166.
Proof. exact (MK_COMB (@lem7653932) (@lem7653931)). Qed.
Lemma lem7653934 : term206 = term166.
Proof. exact (TRANS (@lem7653927) (@lem7653933)). Qed.
Lemma lem7653935 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7653936 : term371 = term363.
Proof. exact (MK_COMB (@lem7653935) (@lem7653934)). Qed.
Lemma lem7653937 : term372 = term365.
Proof. exact (MK_COMB (@lem7653936) (@lem7653924)). Qed.
Lemma lem7653939 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7653940 : term365 = term102.
Proof. exact (@lem7653939 term117). Qed.
Lemma lem7653941 : term372 = term102.
Proof. exact (TRANS (@lem7653937) (@lem7653940)). Qed.
Lemma lem7653942 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7653943 : term374 = term375.
Proof. exact (MK_COMB (@lem7653942) (@lem7653941)). Qed.
Lemma lem7653944 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7653945 : term376 = term324.
Proof. exact (MK_COMB (@lem7653943) (@lem7653944)). Qed.
Lemma lem7653947 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7653948 : term324 = term102.
Proof. exact (@lem7653947 term117). Qed.
Lemma lem7653949 : term376 = term102.
Proof. exact (TRANS (@lem7653945) (@lem7653948)). Qed.
Lemma lem7653951 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7653952 : term175 = term176.
Proof. exact (@lem7653951 term117 term117). Qed.
Lemma lem7653953 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7653954 : term178 = term117.
Proof. exact (EQ_MP (@lem7653953) (@lem940073)). Qed.
Lemma lem7653955 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7653956 : term176 = term116.
Proof. exact (MK_COMB (@lem7653955) (@lem7653954)). Qed.
Lemma lem7653957 : term175 = term116.
Proof. exact (TRANS (@lem7653952) (@lem7653956)). Qed.
Lemma lem7653958 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7653959 : term377 = term324.
Proof. exact (MK_COMB (@lem7653958) (@lem7653957)). Qed.
Lemma lem7653961 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7653962 : term324 = term102.
Proof. exact (@lem7653961 term117). Qed.
Lemma lem7653963 : term377 = term102.
Proof. exact (TRANS (@lem7653959) (@lem7653962)). Qed.
Lemma lem7653964 : term102 = term377.
Proof. exact (SYM (@lem7653963)). Qed.
Lemma lem7653965 : term376 = term377.
Proof. exact (TRANS (@lem7653949) (@lem7653964)). Qed.
Lemma lem7653966 : term366 = term163.
Proof. exact (@lem7653916 (@lem7653965)). Qed.
Lemma lem7653967 : term365 = term163.
Proof. exact (TRANS (@lem7653882) (@lem7653966)). Qed.
Lemma lem7653969 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7653970 : term163 = term102.
Proof. exact (@lem7653969 term102). Qed.
Lemma lem7653971 : term365 = term102.
Proof. exact (TRANS (@lem7653967) (@lem7653970)). Qed.
Lemma lem7653972 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7653973 : term378 = term375.
Proof. exact (MK_COMB (@lem7653972) (@lem7653971)). Qed.
Lemma lem7653974 (_98526 : int) : (real_of_int _98526) = (real_of_int _98526).
Proof. exact (eq_refl (real_of_int _98526)). Qed.
Lemma lem7653975 (_98526 : int) : (term362 _98526) = (term379 _98526).
Proof. exact (MK_COMB (@lem7653973) (@lem7653974 _98526)). Qed.
Lemma lem7653976 (_98526 : int) : (term361 _98526) = (term379 _98526).
Proof. exact (TRANS (@lem7653873 _98526) (@lem7653975 _98526)). Qed.
Lemma lem7653977 (_98526 : int) : (term379 _98526) = term102.
Proof. exact (@lem1982719 (real_of_int _98526)). Qed.
Lemma lem7653978 (_98526 : int) : (term361 _98526) = term102.
Proof. exact (TRANS (@lem7653976 _98526) (@lem7653977 _98526)). Qed.
Lemma lem7653979 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7653980 (_98526 : int) : (term380 _98526) = term381.
Proof. exact (MK_COMB (@lem7653979) (@lem7653978 _98526)). Qed.
Lemma lem7653981 (_98528 : int) : (term385 _98528) = (term386 _98528).
Proof. exact (@lem1982763 (term193 _98528) (real_of_int _98528) term166). Qed.
Lemma lem7653982 (_98528 : int) : (term387 _98528) = (term362 _98528).
Proof. exact (@lem1982713 term166 (real_of_int _98528)). Qed.
Lemma lem7653984 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7653985 : term116 = term205.
Proof. exact (@lem7653984 term117). Qed.
Lemma lem7653987 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7653988 : term166 = term167.
Proof. exact (@lem7653987 term117). Qed.
Lemma lem7653989 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7653990 : term363 = term364.
Proof. exact (MK_COMB (@lem7653989) (@lem7653988)). Qed.
Lemma lem7653991 : term365 = term366.
Proof. exact (MK_COMB (@lem7653990) (@lem7653985)). Qed.
Lemma lem7653992 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7653994 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7653995 : term313 = term319.
Proof. exact (@lem7653994 (NUMERAL 0) term117). Qed.
Lemma lem7653996 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7653997 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7653998 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7653997 h1) (fun h1 : term319 = True => @lem7653996)). Qed.
Lemma lem7653999 : term319 = True.
Proof. exact (EQ_MP (@lem7653998) (@lem7653996)). Qed.
Lemma lem7654000 : term313 = True.
Proof. exact (TRANS (@lem7653995) (@lem7653999)). Qed.
Lemma lem7654001 : True = term313.
Proof. exact (SYM (@lem7654000)). Qed.
Lemma lem7654002 : term313.
Proof. exact (EQ_MP (@lem7654001) (@lem0)). Qed.
Lemma lem7654003 : term368.
Proof. exact (@lem7653992 (@lem7654002)). Qed.
Lemma lem7654005 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654006 : term313 = term319.
Proof. exact (@lem7654005 (NUMERAL 0) term117). Qed.
Lemma lem7654007 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654008 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654009 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654008 h1) (fun h1 : term319 = True => @lem7654007)). Qed.
Lemma lem7654010 : term319 = True.
Proof. exact (EQ_MP (@lem7654009) (@lem7654007)). Qed.
Lemma lem7654011 : term313 = True.
Proof. exact (TRANS (@lem7654006) (@lem7654010)). Qed.
Lemma lem7654012 : True = term313.
Proof. exact (SYM (@lem7654011)). Qed.
Lemma lem7654013 : term313.
Proof. exact (EQ_MP (@lem7654012) (@lem0)). Qed.
Lemma lem7654014 : term369.
Proof. exact (@lem7654003 (@lem7654013)). Qed.
Lemma lem7654016 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654017 : term313 = term319.
Proof. exact (@lem7654016 (NUMERAL 0) term117). Qed.
Lemma lem7654018 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654019 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654020 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654019 h1) (fun h1 : term319 = True => @lem7654018)). Qed.
Lemma lem7654021 : term319 = True.
Proof. exact (EQ_MP (@lem7654020) (@lem7654018)). Qed.
Lemma lem7654022 : term313 = True.
Proof. exact (TRANS (@lem7654017) (@lem7654021)). Qed.
Lemma lem7654023 : True = term313.
Proof. exact (SYM (@lem7654022)). Qed.
Lemma lem7654024 : term313.
Proof. exact (EQ_MP (@lem7654023) (@lem0)). Qed.
Lemma lem7654025 : term370.
Proof. exact (@lem7654014 (@lem7654024)). Qed.
Lemma lem7654027 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7654028 : term175 = term176.
Proof. exact (@lem7654027 term117 term117). Qed.
Lemma lem7654029 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654030 : term178 = term117.
Proof. exact (EQ_MP (@lem7654029) (@lem940073)). Qed.
Lemma lem7654031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654032 : term176 = term116.
Proof. exact (MK_COMB (@lem7654031) (@lem7654030)). Qed.
Lemma lem7654033 : term175 = term116.
Proof. exact (TRANS (@lem7654028) (@lem7654032)). Qed.
Lemma lem7654035 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7654036 : term206 = term211.
Proof. exact (@lem7654035 term117 term117). Qed.
Lemma lem7654037 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654038 : term178 = term117.
Proof. exact (EQ_MP (@lem7654037) (@lem940073)). Qed.
Lemma lem7654039 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654040 : term176 = term116.
Proof. exact (MK_COMB (@lem7654039) (@lem7654038)). Qed.
Lemma lem7654041 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7654042 : term211 = term166.
Proof. exact (MK_COMB (@lem7654041) (@lem7654040)). Qed.
Lemma lem7654043 : term206 = term166.
Proof. exact (TRANS (@lem7654036) (@lem7654042)). Qed.
Lemma lem7654044 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7654045 : term371 = term363.
Proof. exact (MK_COMB (@lem7654044) (@lem7654043)). Qed.
Lemma lem7654046 : term372 = term365.
Proof. exact (MK_COMB (@lem7654045) (@lem7654033)). Qed.
Lemma lem7654048 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7654049 : term365 = term102.
Proof. exact (@lem7654048 term117). Qed.
Lemma lem7654050 : term372 = term102.
Proof. exact (TRANS (@lem7654046) (@lem7654049)). Qed.
Lemma lem7654051 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7654052 : term374 = term375.
Proof. exact (MK_COMB (@lem7654051) (@lem7654050)). Qed.
Lemma lem7654053 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7654054 : term376 = term324.
Proof. exact (MK_COMB (@lem7654052) (@lem7654053)). Qed.
Lemma lem7654056 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7654057 : term324 = term102.
Proof. exact (@lem7654056 term117). Qed.
Lemma lem7654058 : term376 = term102.
Proof. exact (TRANS (@lem7654054) (@lem7654057)). Qed.
Lemma lem7654060 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7654061 : term175 = term176.
Proof. exact (@lem7654060 term117 term117). Qed.
Lemma lem7654062 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654063 : term178 = term117.
Proof. exact (EQ_MP (@lem7654062) (@lem940073)). Qed.
Lemma lem7654064 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654065 : term176 = term116.
Proof. exact (MK_COMB (@lem7654064) (@lem7654063)). Qed.
Lemma lem7654066 : term175 = term116.
Proof. exact (TRANS (@lem7654061) (@lem7654065)). Qed.
Lemma lem7654067 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7654068 : term377 = term324.
Proof. exact (MK_COMB (@lem7654067) (@lem7654066)). Qed.
Lemma lem7654070 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7654071 : term324 = term102.
Proof. exact (@lem7654070 term117). Qed.
Lemma lem7654072 : term377 = term102.
Proof. exact (TRANS (@lem7654068) (@lem7654071)). Qed.
Lemma lem7654073 : term102 = term377.
Proof. exact (SYM (@lem7654072)). Qed.
Lemma lem7654074 : term376 = term377.
Proof. exact (TRANS (@lem7654058) (@lem7654073)). Qed.
Lemma lem7654075 : term366 = term163.
Proof. exact (@lem7654025 (@lem7654074)). Qed.
Lemma lem7654076 : term365 = term163.
Proof. exact (TRANS (@lem7653991) (@lem7654075)). Qed.
Lemma lem7654078 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7654079 : term163 = term102.
Proof. exact (@lem7654078 term102). Qed.
Lemma lem7654080 : term365 = term102.
Proof. exact (TRANS (@lem7654076) (@lem7654079)). Qed.
Lemma lem7654081 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7654082 : term378 = term375.
Proof. exact (MK_COMB (@lem7654081) (@lem7654080)). Qed.
Lemma lem7654083 (_98528 : int) : (real_of_int _98528) = (real_of_int _98528).
Proof. exact (eq_refl (real_of_int _98528)). Qed.
Lemma lem7654084 (_98528 : int) : (term362 _98528) = (term379 _98528).
Proof. exact (MK_COMB (@lem7654082) (@lem7654083 _98528)). Qed.
Lemma lem7654085 (_98528 : int) : (term387 _98528) = (term379 _98528).
Proof. exact (TRANS (@lem7653982 _98528) (@lem7654084 _98528)). Qed.
Lemma lem7654086 (_98528 : int) : (term379 _98528) = term102.
Proof. exact (@lem1982719 (real_of_int _98528)). Qed.
Lemma lem7654087 (_98528 : int) : (term387 _98528) = term102.
Proof. exact (TRANS (@lem7654085 _98528) (@lem7654086 _98528)). Qed.
Lemma lem7654088 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7654089 (_98528 : int) : (term388 _98528) = term381.
Proof. exact (MK_COMB (@lem7654088) (@lem7654087 _98528)). Qed.
Lemma lem7654090 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem7654091 (_98528 : int) : (term386 _98528) = term389.
Proof. exact (MK_COMB (@lem7654089 _98528) (@lem7654090)). Qed.
Lemma lem7654092 (_98528 : int) : (term385 _98528) = term389.
Proof. exact (TRANS (@lem7653981 _98528) (@lem7654091 _98528)). Qed.
Lemma lem7654093 : term389 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem7654094 (_98528 : int) : (term385 _98528) = term166.
Proof. exact (TRANS (@lem7654092 _98528) (@lem7654093)). Qed.
Lemma lem7654095 (_98526 : int) (_98528 : int) : (term383 _98526 _98528) = term389.
Proof. exact (MK_COMB (@lem7653980 _98526) (@lem7654094 _98528)). Qed.
Lemma lem7654096 (_98526 : int) (_98528 : int) : (term382 _98526 _98528) = term389.
Proof. exact (TRANS (@lem7653872 _98526 _98528) (@lem7654095 _98526 _98528)). Qed.
Lemma lem7654097 : term389 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem7654098 (_98526 : int) (_98528 : int) : (term382 _98526 _98528) = term166.
Proof. exact (TRANS (@lem7654096 _98526 _98528) (@lem7654097)). Qed.
Lemma lem7654099 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7654100 (_98526 : int) (_98528 : int) : (term634 _98526 _98528) = term391.
Proof. exact (MK_COMB (@lem7654099) (@lem7654098 _98526 _98528)). Qed.
Lemma lem7654101 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7654102 (_98526 : int) (_98528 : int) : (term633 _98526 _98528) = term392.
Proof. exact (MK_COMB (@lem7654100 _98526 _98528) (@lem7654101)). Qed.
Lemma lem7654103 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : term392.
Proof. exact (EQ_MP (@lem7654102 _98526 _98528) (@lem7653871 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654105 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7654106 : term392 = term393.
Proof. exact (@lem7654105 term102 term166). Qed.
Lemma lem7654108 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7654109 : term166 = term167.
Proof. exact (@lem7654108 term117). Qed.
Lemma lem7654111 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7654112 : term102 = term163.
Proof. exact (@lem7654111 (NUMERAL 0)). Qed.
Lemma lem7654113 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7654114 : term104 = term394.
Proof. exact (MK_COMB (@lem7654113) (@lem7654112)). Qed.
Lemma lem7654115 : term393 = term395.
Proof. exact (MK_COMB (@lem7654114) (@lem7654109)). Qed.
Lemma lem7654116 : term396.
Proof. exact (@lem1980026 term102 term116 term166 term116). Qed.
Lemma lem7654118 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654119 : term313 = term319.
Proof. exact (@lem7654118 (NUMERAL 0) term117). Qed.
Lemma lem7654120 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654121 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654122 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654121 h1) (fun h1 : term319 = True => @lem7654120)). Qed.
Lemma lem7654123 : term319 = True.
Proof. exact (EQ_MP (@lem7654122) (@lem7654120)). Qed.
Lemma lem7654124 : term313 = True.
Proof. exact (TRANS (@lem7654119) (@lem7654123)). Qed.
Lemma lem7654125 : True = term313.
Proof. exact (SYM (@lem7654124)). Qed.
Lemma lem7654126 : term313.
Proof. exact (EQ_MP (@lem7654125) (@lem0)). Qed.
Lemma lem7654127 : term397.
Proof. exact (@lem7654116 (@lem7654126)). Qed.
Lemma lem7654129 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654130 : term313 = term319.
Proof. exact (@lem7654129 (NUMERAL 0) term117). Qed.
Lemma lem7654131 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654132 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654133 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654132 h1) (fun h1 : term319 = True => @lem7654131)). Qed.
Lemma lem7654134 : term319 = True.
Proof. exact (EQ_MP (@lem7654133) (@lem7654131)). Qed.
Lemma lem7654135 : term313 = True.
Proof. exact (TRANS (@lem7654130) (@lem7654134)). Qed.
Lemma lem7654136 : True = term313.
Proof. exact (SYM (@lem7654135)). Qed.
Lemma lem7654137 : term313.
Proof. exact (EQ_MP (@lem7654136) (@lem0)). Qed.
Lemma lem7654138 : term395 = term398.
Proof. exact (@lem7654127 (@lem7654137)). Qed.
Lemma lem7654140 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7654141 : term206 = term211.
Proof. exact (@lem7654140 term117 term117). Qed.
Lemma lem7654142 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654143 : term178 = term117.
Proof. exact (EQ_MP (@lem7654142) (@lem940073)). Qed.
Lemma lem7654144 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654145 : term176 = term116.
Proof. exact (MK_COMB (@lem7654144) (@lem7654143)). Qed.
Lemma lem7654146 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7654147 : term211 = term166.
Proof. exact (MK_COMB (@lem7654146) (@lem7654145)). Qed.
Lemma lem7654148 : term206 = term166.
Proof. exact (TRANS (@lem7654141) (@lem7654147)). Qed.
Lemma lem7654150 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7654151 : term324 = term102.
Proof. exact (@lem7654150 term117). Qed.
Lemma lem7654152 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7654153 : term399 = term104.
Proof. exact (MK_COMB (@lem7654152) (@lem7654151)). Qed.
Lemma lem7654154 : term398 = term393.
Proof. exact (MK_COMB (@lem7654153) (@lem7654148)). Qed.
Lemma lem7654156 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7654157 : term393 = term402.
Proof. exact (@lem7654156 (NUMERAL 0) term117). Qed.
Lemma lem7654158 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654159 (h1 : term320 = (BIT1 0)) : (term117 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7654160 : (term320 = (BIT1 0)) = ((term117 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654159 h1) (fun h1 : (term117 = (NUMERAL 0)) = False => @lem7654158)). Qed.
Lemma lem7654161 : (term117 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7654160) (@lem7654158)). Qed.
Lemma lem7654162 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7654163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7654164 : term403 = (and True).
Proof. exact (MK_COMB (@lem7654163) (@lem7654162)). Qed.
Lemma lem7654165 : term402 = (True /\ False).
Proof. exact (MK_COMB (@lem7654164) (@lem7654161)). Qed.
Lemma lem7654167 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7654168 : term402 = False.
Proof. exact (TRANS (@lem7654165) (@lem7654167)). Qed.
Lemma lem7654169 : term393 = False.
Proof. exact (TRANS (@lem7654157) (@lem7654168)). Qed.
Lemma lem7654170 : term398 = False.
Proof. exact (TRANS (@lem7654154) (@lem7654169)). Qed.
Lemma lem7654171 : term395 = False.
Proof. exact (TRANS (@lem7654138) (@lem7654170)). Qed.
Lemma lem7654172 : term393 = False.
Proof. exact (TRANS (@lem7654115) (@lem7654171)). Qed.
Lemma lem7654173 : term392 = False.
Proof. exact (TRANS (@lem7654106) (@lem7654172)). Qed.
Lemma lem7654174 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term609 _98526 _98528 _98527) : False.
Proof. exact (EQ_MP (@lem7654173) (@lem7654103 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654175 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term635 _98526 _98528 _98527.
Proof. exact (h1). Qed.
Lemma lem7654176 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term608 _98526 _98528 _98527.
Proof. exact (proj2 (@lem7654175 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654178 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term604 _98526 _98528 _98527.
Proof. exact (proj2 (@lem7654176 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654180 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term600 _98526 _98528 _98527.
Proof. exact (proj2 (@lem7654178 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654182 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term591 _98526 _98528 _98527.
Proof. exact (proj2 (@lem7654180 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654183 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term221 _98526 _98528 _98527.
Proof. exact (proj1 (@lem7654180 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654185 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term218 _98526 _98528.
Proof. exact (proj1 (@lem7654183 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654187 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term226 _98526 _98528.
Proof. exact (proj1 (@lem7654182 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654189 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7654190 : term312 = term313.
Proof. exact (@lem7654189 term102 term116). Qed.
Lemma lem7654192 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7654193 : term116 = term205.
Proof. exact (@lem7654192 term117). Qed.
Lemma lem7654195 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7654196 : term102 = term163.
Proof. exact (@lem7654195 (NUMERAL 0)). Qed.
Lemma lem7654197 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7654198 : term314 = term315.
Proof. exact (MK_COMB (@lem7654197) (@lem7654196)). Qed.
Lemma lem7654199 : term313 = term316.
Proof. exact (MK_COMB (@lem7654198) (@lem7654193)). Qed.
Lemma lem7654200 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7654202 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654203 : term313 = term319.
Proof. exact (@lem7654202 (NUMERAL 0) term117). Qed.
Lemma lem7654204 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654205 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654206 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654205 h1) (fun h1 : term319 = True => @lem7654204)). Qed.
Lemma lem7654207 : term319 = True.
Proof. exact (EQ_MP (@lem7654206) (@lem7654204)). Qed.
Lemma lem7654208 : term313 = True.
Proof. exact (TRANS (@lem7654203) (@lem7654207)). Qed.
Lemma lem7654209 : True = term313.
Proof. exact (SYM (@lem7654208)). Qed.
Lemma lem7654210 : term313.
Proof. exact (EQ_MP (@lem7654209) (@lem0)). Qed.
Lemma lem7654211 : term321.
Proof. exact (@lem7654200 (@lem7654210)). Qed.
Lemma lem7654213 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654214 : term313 = term319.
Proof. exact (@lem7654213 (NUMERAL 0) term117). Qed.
Lemma lem7654215 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654216 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654217 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654216 h1) (fun h1 : term319 = True => @lem7654215)). Qed.
Lemma lem7654218 : term319 = True.
Proof. exact (EQ_MP (@lem7654217) (@lem7654215)). Qed.
Lemma lem7654219 : term313 = True.
Proof. exact (TRANS (@lem7654214) (@lem7654218)). Qed.
Lemma lem7654220 : True = term313.
Proof. exact (SYM (@lem7654219)). Qed.
Lemma lem7654221 : term313.
Proof. exact (EQ_MP (@lem7654220) (@lem0)). Qed.
Lemma lem7654222 : term316 = term322.
Proof. exact (@lem7654211 (@lem7654221)). Qed.
Lemma lem7654224 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7654225 : term175 = term176.
Proof. exact (@lem7654224 term117 term117). Qed.
Lemma lem7654226 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654227 : term178 = term117.
Proof. exact (EQ_MP (@lem7654226) (@lem940073)). Qed.
Lemma lem7654228 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654229 : term176 = term116.
Proof. exact (MK_COMB (@lem7654228) (@lem7654227)). Qed.
Lemma lem7654230 : term175 = term116.
Proof. exact (TRANS (@lem7654225) (@lem7654229)). Qed.
Lemma lem7654232 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7654233 : term324 = term102.
Proof. exact (@lem7654232 term117). Qed.
Lemma lem7654234 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7654235 : term325 = term314.
Proof. exact (MK_COMB (@lem7654234) (@lem7654233)). Qed.
Lemma lem7654236 : term322 = term313.
Proof. exact (MK_COMB (@lem7654235) (@lem7654230)). Qed.
Lemma lem7654238 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654239 : term313 = term319.
Proof. exact (@lem7654238 (NUMERAL 0) term117). Qed.
Lemma lem7654240 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654241 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654242 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654241 h1) (fun h1 : term319 = True => @lem7654240)). Qed.
Lemma lem7654243 : term319 = True.
Proof. exact (EQ_MP (@lem7654242) (@lem7654240)). Qed.
Lemma lem7654244 : term313 = True.
Proof. exact (TRANS (@lem7654239) (@lem7654243)). Qed.
Lemma lem7654245 : term322 = True.
Proof. exact (TRANS (@lem7654236) (@lem7654244)). Qed.
Lemma lem7654246 : term316 = True.
Proof. exact (TRANS (@lem7654222) (@lem7654245)). Qed.
Lemma lem7654247 : term313 = True.
Proof. exact (TRANS (@lem7654199) (@lem7654246)). Qed.
Lemma lem7654248 : term312 = True.
Proof. exact (TRANS (@lem7654190) (@lem7654247)). Qed.
Lemma lem7654249 : True = term312.
Proof. exact (SYM (@lem7654248)). Qed.
Lemma lem7654250 : term312.
Proof. exact (EQ_MP (@lem7654249) (@lem0)). Qed.
Lemma lem7654251 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term423 _98526 _98528.
Proof. exact (conj (@lem7654250) (@lem7654185 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654253 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7654254 (_98526 : int) (_98528 : int) : term424 _98526 _98528.
Proof. exact (@lem7654253 term116 (term215 _98526 _98528)). Qed.
Lemma lem7654255 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term425 _98526 _98528.
Proof. exact (@lem7654254 _98526 _98528 (@lem7654251 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654256 (_98526 : int) (_98528 : int) : (term426 _98526 _98528) = (term215 _98526 _98528).
Proof. exact (@lem1982733 (term215 _98526 _98528)). Qed.
Lemma lem7654257 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7654258 (_98526 : int) (_98528 : int) : (term427 _98526 _98528) = (term217 _98526 _98528).
Proof. exact (MK_COMB (@lem7654257) (@lem7654256 _98526 _98528)). Qed.
Lemma lem7654259 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7654260 (_98526 : int) (_98528 : int) : (term425 _98526 _98528) = (term218 _98526 _98528).
Proof. exact (MK_COMB (@lem7654258 _98526 _98528) (@lem7654259)). Qed.
Lemma lem7654261 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term218 _98526 _98528.
Proof. exact (EQ_MP (@lem7654260 _98526 _98528) (@lem7654255 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654263 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7654264 : term312 = term313.
Proof. exact (@lem7654263 term102 term116). Qed.
Lemma lem7654266 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7654267 : term116 = term205.
Proof. exact (@lem7654266 term117). Qed.
Lemma lem7654269 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7654270 : term102 = term163.
Proof. exact (@lem7654269 (NUMERAL 0)). Qed.
Lemma lem7654271 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7654272 : term314 = term315.
Proof. exact (MK_COMB (@lem7654271) (@lem7654270)). Qed.
Lemma lem7654273 : term313 = term316.
Proof. exact (MK_COMB (@lem7654272) (@lem7654267)). Qed.
Lemma lem7654274 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7654276 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654277 : term313 = term319.
Proof. exact (@lem7654276 (NUMERAL 0) term117). Qed.
Lemma lem7654278 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654279 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654280 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654279 h1) (fun h1 : term319 = True => @lem7654278)). Qed.
Lemma lem7654281 : term319 = True.
Proof. exact (EQ_MP (@lem7654280) (@lem7654278)). Qed.
Lemma lem7654282 : term313 = True.
Proof. exact (TRANS (@lem7654277) (@lem7654281)). Qed.
Lemma lem7654283 : True = term313.
Proof. exact (SYM (@lem7654282)). Qed.
Lemma lem7654284 : term313.
Proof. exact (EQ_MP (@lem7654283) (@lem0)). Qed.
Lemma lem7654285 : term321.
Proof. exact (@lem7654274 (@lem7654284)). Qed.
Lemma lem7654287 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654288 : term313 = term319.
Proof. exact (@lem7654287 (NUMERAL 0) term117). Qed.
Lemma lem7654289 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654290 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654291 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654290 h1) (fun h1 : term319 = True => @lem7654289)). Qed.
Lemma lem7654292 : term319 = True.
Proof. exact (EQ_MP (@lem7654291) (@lem7654289)). Qed.
Lemma lem7654293 : term313 = True.
Proof. exact (TRANS (@lem7654288) (@lem7654292)). Qed.
Lemma lem7654294 : True = term313.
Proof. exact (SYM (@lem7654293)). Qed.
Lemma lem7654295 : term313.
Proof. exact (EQ_MP (@lem7654294) (@lem0)). Qed.
Lemma lem7654296 : term316 = term322.
Proof. exact (@lem7654285 (@lem7654295)). Qed.
Lemma lem7654298 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7654299 : term175 = term176.
Proof. exact (@lem7654298 term117 term117). Qed.
Lemma lem7654300 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654301 : term178 = term117.
Proof. exact (EQ_MP (@lem7654300) (@lem940073)). Qed.
Lemma lem7654302 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654303 : term176 = term116.
Proof. exact (MK_COMB (@lem7654302) (@lem7654301)). Qed.
Lemma lem7654304 : term175 = term116.
Proof. exact (TRANS (@lem7654299) (@lem7654303)). Qed.
Lemma lem7654306 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7654307 : term324 = term102.
Proof. exact (@lem7654306 term117). Qed.
Lemma lem7654308 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7654309 : term325 = term314.
Proof. exact (MK_COMB (@lem7654308) (@lem7654307)). Qed.
Lemma lem7654310 : term322 = term313.
Proof. exact (MK_COMB (@lem7654309) (@lem7654304)). Qed.
Lemma lem7654312 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654313 : term313 = term319.
Proof. exact (@lem7654312 (NUMERAL 0) term117). Qed.
Lemma lem7654314 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654315 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654316 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654315 h1) (fun h1 : term319 = True => @lem7654314)). Qed.
Lemma lem7654317 : term319 = True.
Proof. exact (EQ_MP (@lem7654316) (@lem7654314)). Qed.
Lemma lem7654318 : term313 = True.
Proof. exact (TRANS (@lem7654313) (@lem7654317)). Qed.
Lemma lem7654319 : term322 = True.
Proof. exact (TRANS (@lem7654310) (@lem7654318)). Qed.
Lemma lem7654320 : term316 = True.
Proof. exact (TRANS (@lem7654296) (@lem7654319)). Qed.
Lemma lem7654321 : term313 = True.
Proof. exact (TRANS (@lem7654273) (@lem7654320)). Qed.
Lemma lem7654322 : term312 = True.
Proof. exact (TRANS (@lem7654264) (@lem7654321)). Qed.
Lemma lem7654323 : True = term312.
Proof. exact (SYM (@lem7654322)). Qed.
Lemma lem7654324 : term312.
Proof. exact (EQ_MP (@lem7654323) (@lem0)). Qed.
Lemma lem7654325 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term418 _98526 _98528.
Proof. exact (conj (@lem7654324) (@lem7654187 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654327 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7654328 (_98526 : int) (_98528 : int) : term419 _98526 _98528.
Proof. exact (@lem7654327 term116 (term224 _98526 _98528)). Qed.
Lemma lem7654329 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term420 _98526 _98528.
Proof. exact (@lem7654328 _98526 _98528 (@lem7654325 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654330 (_98526 : int) (_98528 : int) : (term421 _98526 _98528) = (term224 _98526 _98528).
Proof. exact (@lem1982733 (term224 _98526 _98528)). Qed.
Lemma lem7654331 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7654332 (_98526 : int) (_98528 : int) : (term422 _98526 _98528) = (term225 _98526 _98528).
Proof. exact (MK_COMB (@lem7654331) (@lem7654330 _98526 _98528)). Qed.
Lemma lem7654333 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7654334 (_98526 : int) (_98528 : int) : (term420 _98526 _98528) = (term226 _98526 _98528).
Proof. exact (MK_COMB (@lem7654332 _98526 _98528) (@lem7654333)). Qed.
Lemma lem7654335 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term226 _98526 _98528.
Proof. exact (EQ_MP (@lem7654334 _98526 _98528) (@lem7654329 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654336 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term502 _98526 _98528.
Proof. exact (conj (@lem7654335 _98526 _98528 _98527 h1) (@lem7654261 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654338 (x : real) (y : real) : term429 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7654339 (_98526 : int) (_98528 : int) : term503 _98526 _98528.
Proof. exact (@lem7654338 (term224 _98526 _98528) (term215 _98526 _98528)). Qed.
Lemma lem7654340 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term504 _98526 _98528.
Proof. exact (@lem7654339 _98526 _98528 (@lem7654336 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654341 (_98526 : int) (_98528 : int) : (term505 _98526 _98528) = (term506 _98526 _98528).
Proof. exact (@lem1982753 (term193 _98526) (real_of_int _98526) (term384 _98528) (term214 _98528)). Qed.
Lemma lem7654342 (_98526 : int) : (term387 _98526) = (term362 _98526).
Proof. exact (@lem1982713 term166 (real_of_int _98526)). Qed.
Lemma lem7654344 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7654345 : term116 = term205.
Proof. exact (@lem7654344 term117). Qed.
Lemma lem7654347 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7654348 : term166 = term167.
Proof. exact (@lem7654347 term117). Qed.
Lemma lem7654349 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7654350 : term363 = term364.
Proof. exact (MK_COMB (@lem7654349) (@lem7654348)). Qed.
Lemma lem7654351 : term365 = term366.
Proof. exact (MK_COMB (@lem7654350) (@lem7654345)). Qed.
Lemma lem7654352 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7654354 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654355 : term313 = term319.
Proof. exact (@lem7654354 (NUMERAL 0) term117). Qed.
Lemma lem7654356 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654357 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654358 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654357 h1) (fun h1 : term319 = True => @lem7654356)). Qed.
Lemma lem7654359 : term319 = True.
Proof. exact (EQ_MP (@lem7654358) (@lem7654356)). Qed.
Lemma lem7654360 : term313 = True.
Proof. exact (TRANS (@lem7654355) (@lem7654359)). Qed.
Lemma lem7654361 : True = term313.
Proof. exact (SYM (@lem7654360)). Qed.
Lemma lem7654362 : term313.
Proof. exact (EQ_MP (@lem7654361) (@lem0)). Qed.
Lemma lem7654363 : term368.
Proof. exact (@lem7654352 (@lem7654362)). Qed.
Lemma lem7654365 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654366 : term313 = term319.
Proof. exact (@lem7654365 (NUMERAL 0) term117). Qed.
Lemma lem7654367 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654368 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654369 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654368 h1) (fun h1 : term319 = True => @lem7654367)). Qed.
Lemma lem7654370 : term319 = True.
Proof. exact (EQ_MP (@lem7654369) (@lem7654367)). Qed.
Lemma lem7654371 : term313 = True.
Proof. exact (TRANS (@lem7654366) (@lem7654370)). Qed.
Lemma lem7654372 : True = term313.
Proof. exact (SYM (@lem7654371)). Qed.
Lemma lem7654373 : term313.
Proof. exact (EQ_MP (@lem7654372) (@lem0)). Qed.
Lemma lem7654374 : term369.
Proof. exact (@lem7654363 (@lem7654373)). Qed.
Lemma lem7654376 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654377 : term313 = term319.
Proof. exact (@lem7654376 (NUMERAL 0) term117). Qed.
Lemma lem7654378 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654379 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654380 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654379 h1) (fun h1 : term319 = True => @lem7654378)). Qed.
Lemma lem7654381 : term319 = True.
Proof. exact (EQ_MP (@lem7654380) (@lem7654378)). Qed.
Lemma lem7654382 : term313 = True.
Proof. exact (TRANS (@lem7654377) (@lem7654381)). Qed.
Lemma lem7654383 : True = term313.
Proof. exact (SYM (@lem7654382)). Qed.
Lemma lem7654384 : term313.
Proof. exact (EQ_MP (@lem7654383) (@lem0)). Qed.
Lemma lem7654385 : term370.
Proof. exact (@lem7654374 (@lem7654384)). Qed.
Lemma lem7654387 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7654388 : term175 = term176.
Proof. exact (@lem7654387 term117 term117). Qed.
Lemma lem7654389 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654390 : term178 = term117.
Proof. exact (EQ_MP (@lem7654389) (@lem940073)). Qed.
Lemma lem7654391 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654392 : term176 = term116.
Proof. exact (MK_COMB (@lem7654391) (@lem7654390)). Qed.
Lemma lem7654393 : term175 = term116.
Proof. exact (TRANS (@lem7654388) (@lem7654392)). Qed.
Lemma lem7654395 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7654396 : term206 = term211.
Proof. exact (@lem7654395 term117 term117). Qed.
Lemma lem7654397 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654398 : term178 = term117.
Proof. exact (EQ_MP (@lem7654397) (@lem940073)). Qed.
Lemma lem7654399 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654400 : term176 = term116.
Proof. exact (MK_COMB (@lem7654399) (@lem7654398)). Qed.
Lemma lem7654401 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7654402 : term211 = term166.
Proof. exact (MK_COMB (@lem7654401) (@lem7654400)). Qed.
Lemma lem7654403 : term206 = term166.
Proof. exact (TRANS (@lem7654396) (@lem7654402)). Qed.
Lemma lem7654404 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7654405 : term371 = term363.
Proof. exact (MK_COMB (@lem7654404) (@lem7654403)). Qed.
Lemma lem7654406 : term372 = term365.
Proof. exact (MK_COMB (@lem7654405) (@lem7654393)). Qed.
Lemma lem7654408 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7654409 : term365 = term102.
Proof. exact (@lem7654408 term117). Qed.
Lemma lem7654410 : term372 = term102.
Proof. exact (TRANS (@lem7654406) (@lem7654409)). Qed.
Lemma lem7654411 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7654412 : term374 = term375.
Proof. exact (MK_COMB (@lem7654411) (@lem7654410)). Qed.
Lemma lem7654413 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7654414 : term376 = term324.
Proof. exact (MK_COMB (@lem7654412) (@lem7654413)). Qed.
Lemma lem7654416 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7654417 : term324 = term102.
Proof. exact (@lem7654416 term117). Qed.
Lemma lem7654418 : term376 = term102.
Proof. exact (TRANS (@lem7654414) (@lem7654417)). Qed.
Lemma lem7654420 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7654421 : term175 = term176.
Proof. exact (@lem7654420 term117 term117). Qed.
Lemma lem7654422 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654423 : term178 = term117.
Proof. exact (EQ_MP (@lem7654422) (@lem940073)). Qed.
Lemma lem7654424 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654425 : term176 = term116.
Proof. exact (MK_COMB (@lem7654424) (@lem7654423)). Qed.
Lemma lem7654426 : term175 = term116.
Proof. exact (TRANS (@lem7654421) (@lem7654425)). Qed.
Lemma lem7654427 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7654428 : term377 = term324.
Proof. exact (MK_COMB (@lem7654427) (@lem7654426)). Qed.
Lemma lem7654430 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7654431 : term324 = term102.
Proof. exact (@lem7654430 term117). Qed.
Lemma lem7654432 : term377 = term102.
Proof. exact (TRANS (@lem7654428) (@lem7654431)). Qed.
Lemma lem7654433 : term102 = term377.
Proof. exact (SYM (@lem7654432)). Qed.
Lemma lem7654434 : term376 = term377.
Proof. exact (TRANS (@lem7654418) (@lem7654433)). Qed.
Lemma lem7654435 : term366 = term163.
Proof. exact (@lem7654385 (@lem7654434)). Qed.
Lemma lem7654436 : term365 = term163.
Proof. exact (TRANS (@lem7654351) (@lem7654435)). Qed.
Lemma lem7654438 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7654439 : term163 = term102.
Proof. exact (@lem7654438 term102). Qed.
Lemma lem7654440 : term365 = term102.
Proof. exact (TRANS (@lem7654436) (@lem7654439)). Qed.
Lemma lem7654441 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7654442 : term378 = term375.
Proof. exact (MK_COMB (@lem7654441) (@lem7654440)). Qed.
Lemma lem7654443 (_98526 : int) : (real_of_int _98526) = (real_of_int _98526).
Proof. exact (eq_refl (real_of_int _98526)). Qed.
Lemma lem7654444 (_98526 : int) : (term362 _98526) = (term379 _98526).
Proof. exact (MK_COMB (@lem7654442) (@lem7654443 _98526)). Qed.
Lemma lem7654445 (_98526 : int) : (term387 _98526) = (term379 _98526).
Proof. exact (TRANS (@lem7654342 _98526) (@lem7654444 _98526)). Qed.
Lemma lem7654446 (_98526 : int) : (term379 _98526) = term102.
Proof. exact (@lem1982719 (real_of_int _98526)). Qed.
Lemma lem7654447 (_98526 : int) : (term387 _98526) = term102.
Proof. exact (TRANS (@lem7654445 _98526) (@lem7654446 _98526)). Qed.
Lemma lem7654448 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7654449 (_98526 : int) : (term388 _98526) = term381.
Proof. exact (MK_COMB (@lem7654448) (@lem7654447 _98526)). Qed.
Lemma lem7654450 (_98528 : int) : (term507 _98528) = (term508 _98528).
Proof. exact (@lem1982753 (real_of_int _98528) (term193 _98528) term166 term166). Qed.
Lemma lem7654451 (_98528 : int) : (term361 _98528) = (term362 _98528).
Proof. exact (@lem1982715 term166 (real_of_int _98528)). Qed.
Lemma lem7654453 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7654454 : term116 = term205.
Proof. exact (@lem7654453 term117). Qed.
Lemma lem7654456 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7654457 : term166 = term167.
Proof. exact (@lem7654456 term117). Qed.
Lemma lem7654458 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7654459 : term363 = term364.
Proof. exact (MK_COMB (@lem7654458) (@lem7654457)). Qed.
Lemma lem7654460 : term365 = term366.
Proof. exact (MK_COMB (@lem7654459) (@lem7654454)). Qed.
Lemma lem7654461 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7654463 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654464 : term313 = term319.
Proof. exact (@lem7654463 (NUMERAL 0) term117). Qed.
Lemma lem7654465 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654466 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654467 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654466 h1) (fun h1 : term319 = True => @lem7654465)). Qed.
Lemma lem7654468 : term319 = True.
Proof. exact (EQ_MP (@lem7654467) (@lem7654465)). Qed.
Lemma lem7654469 : term313 = True.
Proof. exact (TRANS (@lem7654464) (@lem7654468)). Qed.
Lemma lem7654470 : True = term313.
Proof. exact (SYM (@lem7654469)). Qed.
Lemma lem7654471 : term313.
Proof. exact (EQ_MP (@lem7654470) (@lem0)). Qed.
Lemma lem7654472 : term368.
Proof. exact (@lem7654461 (@lem7654471)). Qed.
Lemma lem7654474 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654475 : term313 = term319.
Proof. exact (@lem7654474 (NUMERAL 0) term117). Qed.
Lemma lem7654476 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654477 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654478 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654477 h1) (fun h1 : term319 = True => @lem7654476)). Qed.
Lemma lem7654479 : term319 = True.
Proof. exact (EQ_MP (@lem7654478) (@lem7654476)). Qed.
Lemma lem7654480 : term313 = True.
Proof. exact (TRANS (@lem7654475) (@lem7654479)). Qed.
Lemma lem7654481 : True = term313.
Proof. exact (SYM (@lem7654480)). Qed.
Lemma lem7654482 : term313.
Proof. exact (EQ_MP (@lem7654481) (@lem0)). Qed.
Lemma lem7654483 : term369.
Proof. exact (@lem7654472 (@lem7654482)). Qed.
Lemma lem7654485 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654486 : term313 = term319.
Proof. exact (@lem7654485 (NUMERAL 0) term117). Qed.
Lemma lem7654487 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654488 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654489 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654488 h1) (fun h1 : term319 = True => @lem7654487)). Qed.
Lemma lem7654490 : term319 = True.
Proof. exact (EQ_MP (@lem7654489) (@lem7654487)). Qed.
Lemma lem7654491 : term313 = True.
Proof. exact (TRANS (@lem7654486) (@lem7654490)). Qed.
Lemma lem7654492 : True = term313.
Proof. exact (SYM (@lem7654491)). Qed.
Lemma lem7654493 : term313.
Proof. exact (EQ_MP (@lem7654492) (@lem0)). Qed.
Lemma lem7654494 : term370.
Proof. exact (@lem7654483 (@lem7654493)). Qed.
Lemma lem7654496 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7654497 : term175 = term176.
Proof. exact (@lem7654496 term117 term117). Qed.
Lemma lem7654498 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654499 : term178 = term117.
Proof. exact (EQ_MP (@lem7654498) (@lem940073)). Qed.
Lemma lem7654500 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654501 : term176 = term116.
Proof. exact (MK_COMB (@lem7654500) (@lem7654499)). Qed.
Lemma lem7654502 : term175 = term116.
Proof. exact (TRANS (@lem7654497) (@lem7654501)). Qed.
Lemma lem7654504 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7654505 : term206 = term211.
Proof. exact (@lem7654504 term117 term117). Qed.
Lemma lem7654506 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654507 : term178 = term117.
Proof. exact (EQ_MP (@lem7654506) (@lem940073)). Qed.
Lemma lem7654508 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654509 : term176 = term116.
Proof. exact (MK_COMB (@lem7654508) (@lem7654507)). Qed.
Lemma lem7654510 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7654511 : term211 = term166.
Proof. exact (MK_COMB (@lem7654510) (@lem7654509)). Qed.
Lemma lem7654512 : term206 = term166.
Proof. exact (TRANS (@lem7654505) (@lem7654511)). Qed.
Lemma lem7654513 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7654514 : term371 = term363.
Proof. exact (MK_COMB (@lem7654513) (@lem7654512)). Qed.
Lemma lem7654515 : term372 = term365.
Proof. exact (MK_COMB (@lem7654514) (@lem7654502)). Qed.
Lemma lem7654517 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7654518 : term365 = term102.
Proof. exact (@lem7654517 term117). Qed.
Lemma lem7654519 : term372 = term102.
Proof. exact (TRANS (@lem7654515) (@lem7654518)). Qed.
Lemma lem7654520 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7654521 : term374 = term375.
Proof. exact (MK_COMB (@lem7654520) (@lem7654519)). Qed.
Lemma lem7654522 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7654523 : term376 = term324.
Proof. exact (MK_COMB (@lem7654521) (@lem7654522)). Qed.
Lemma lem7654525 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7654526 : term324 = term102.
Proof. exact (@lem7654525 term117). Qed.
Lemma lem7654527 : term376 = term102.
Proof. exact (TRANS (@lem7654523) (@lem7654526)). Qed.
Lemma lem7654529 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7654530 : term175 = term176.
Proof. exact (@lem7654529 term117 term117). Qed.
Lemma lem7654531 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654532 : term178 = term117.
Proof. exact (EQ_MP (@lem7654531) (@lem940073)). Qed.
Lemma lem7654533 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654534 : term176 = term116.
Proof. exact (MK_COMB (@lem7654533) (@lem7654532)). Qed.
Lemma lem7654535 : term175 = term116.
Proof. exact (TRANS (@lem7654530) (@lem7654534)). Qed.
Lemma lem7654536 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7654537 : term377 = term324.
Proof. exact (MK_COMB (@lem7654536) (@lem7654535)). Qed.
Lemma lem7654539 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7654540 : term324 = term102.
Proof. exact (@lem7654539 term117). Qed.
Lemma lem7654541 : term377 = term102.
Proof. exact (TRANS (@lem7654537) (@lem7654540)). Qed.
Lemma lem7654542 : term102 = term377.
Proof. exact (SYM (@lem7654541)). Qed.
Lemma lem7654543 : term376 = term377.
Proof. exact (TRANS (@lem7654527) (@lem7654542)). Qed.
Lemma lem7654544 : term366 = term163.
Proof. exact (@lem7654494 (@lem7654543)). Qed.
Lemma lem7654545 : term365 = term163.
Proof. exact (TRANS (@lem7654460) (@lem7654544)). Qed.
Lemma lem7654547 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7654548 : term163 = term102.
Proof. exact (@lem7654547 term102). Qed.
Lemma lem7654549 : term365 = term102.
Proof. exact (TRANS (@lem7654545) (@lem7654548)). Qed.
Lemma lem7654550 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7654551 : term378 = term375.
Proof. exact (MK_COMB (@lem7654550) (@lem7654549)). Qed.
Lemma lem7654552 (_98528 : int) : (real_of_int _98528) = (real_of_int _98528).
Proof. exact (eq_refl (real_of_int _98528)). Qed.
Lemma lem7654553 (_98528 : int) : (term362 _98528) = (term379 _98528).
Proof. exact (MK_COMB (@lem7654551) (@lem7654552 _98528)). Qed.
Lemma lem7654554 (_98528 : int) : (term361 _98528) = (term379 _98528).
Proof. exact (TRANS (@lem7654451 _98528) (@lem7654553 _98528)). Qed.
Lemma lem7654555 (_98528 : int) : (term379 _98528) = term102.
Proof. exact (@lem1982719 (real_of_int _98528)). Qed.
Lemma lem7654556 (_98528 : int) : (term361 _98528) = term102.
Proof. exact (TRANS (@lem7654554 _98528) (@lem7654555 _98528)). Qed.
Lemma lem7654557 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7654558 (_98528 : int) : (term380 _98528) = term381.
Proof. exact (MK_COMB (@lem7654557) (@lem7654556 _98528)). Qed.
Lemma lem7654560 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7654561 : term166 = term167.
Proof. exact (@lem7654560 term117). Qed.
Lemma lem7654563 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7654564 : term166 = term167.
Proof. exact (@lem7654563 term117). Qed.
Lemma lem7654565 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7654566 : term363 = term364.
Proof. exact (MK_COMB (@lem7654565) (@lem7654564)). Qed.
Lemma lem7654567 : term436 = term437.
Proof. exact (MK_COMB (@lem7654566) (@lem7654561)). Qed.
Lemma lem7654568 : term438.
Proof. exact (@lem1981473 term166 term116 term166 term116 term439 term116). Qed.
Lemma lem7654570 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654571 : term313 = term319.
Proof. exact (@lem7654570 (NUMERAL 0) term117). Qed.
Lemma lem7654572 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654573 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654574 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654573 h1) (fun h1 : term319 = True => @lem7654572)). Qed.
Lemma lem7654575 : term319 = True.
Proof. exact (EQ_MP (@lem7654574) (@lem7654572)). Qed.
Lemma lem7654576 : term313 = True.
Proof. exact (TRANS (@lem7654571) (@lem7654575)). Qed.
Lemma lem7654577 : True = term313.
Proof. exact (SYM (@lem7654576)). Qed.
Lemma lem7654578 : term313.
Proof. exact (EQ_MP (@lem7654577) (@lem0)). Qed.
Lemma lem7654579 : term440.
Proof. exact (@lem7654568 (@lem7654578)). Qed.
Lemma lem7654581 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654582 : term313 = term319.
Proof. exact (@lem7654581 (NUMERAL 0) term117). Qed.
Lemma lem7654583 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654584 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654585 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654584 h1) (fun h1 : term319 = True => @lem7654583)). Qed.
Lemma lem7654586 : term319 = True.
Proof. exact (EQ_MP (@lem7654585) (@lem7654583)). Qed.
Lemma lem7654587 : term313 = True.
Proof. exact (TRANS (@lem7654582) (@lem7654586)). Qed.
Lemma lem7654588 : True = term313.
Proof. exact (SYM (@lem7654587)). Qed.
Lemma lem7654589 : term313.
Proof. exact (EQ_MP (@lem7654588) (@lem0)). Qed.
Lemma lem7654590 : term441.
Proof. exact (@lem7654579 (@lem7654589)). Qed.
Lemma lem7654592 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654593 : term313 = term319.
Proof. exact (@lem7654592 (NUMERAL 0) term117). Qed.
Lemma lem7654594 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654595 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654596 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654595 h1) (fun h1 : term319 = True => @lem7654594)). Qed.
Lemma lem7654597 : term319 = True.
Proof. exact (EQ_MP (@lem7654596) (@lem7654594)). Qed.
Lemma lem7654598 : term313 = True.
Proof. exact (TRANS (@lem7654593) (@lem7654597)). Qed.
Lemma lem7654599 : True = term313.
Proof. exact (SYM (@lem7654598)). Qed.
Lemma lem7654600 : term313.
Proof. exact (EQ_MP (@lem7654599) (@lem0)). Qed.
Lemma lem7654601 : term442.
Proof. exact (@lem7654590 (@lem7654600)). Qed.
Lemma lem7654603 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7654604 : term206 = term211.
Proof. exact (@lem7654603 term117 term117). Qed.
Lemma lem7654605 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654606 : term178 = term117.
Proof. exact (EQ_MP (@lem7654605) (@lem940073)). Qed.
Lemma lem7654607 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654608 : term176 = term116.
Proof. exact (MK_COMB (@lem7654607) (@lem7654606)). Qed.
Lemma lem7654609 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7654610 : term211 = term166.
Proof. exact (MK_COMB (@lem7654609) (@lem7654608)). Qed.
Lemma lem7654611 : term206 = term166.
Proof. exact (TRANS (@lem7654604) (@lem7654610)). Qed.
Lemma lem7654613 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7654614 : term206 = term211.
Proof. exact (@lem7654613 term117 term117). Qed.
Lemma lem7654615 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654616 : term178 = term117.
Proof. exact (EQ_MP (@lem7654615) (@lem940073)). Qed.
Lemma lem7654617 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654618 : term176 = term116.
Proof. exact (MK_COMB (@lem7654617) (@lem7654616)). Qed.
Lemma lem7654619 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7654620 : term211 = term166.
Proof. exact (MK_COMB (@lem7654619) (@lem7654618)). Qed.
Lemma lem7654621 : term206 = term166.
Proof. exact (TRANS (@lem7654614) (@lem7654620)). Qed.
Lemma lem7654622 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7654623 : term371 = term363.
Proof. exact (MK_COMB (@lem7654622) (@lem7654621)). Qed.
Lemma lem7654624 : term443 = term436.
Proof. exact (MK_COMB (@lem7654623) (@lem7654611)). Qed.
Lemma lem7654625 : term436 = term444.
Proof. exact (@lem1367763 term117 term117). Qed.
Lemma lem7654626 : term445 = term446.
Proof. exact (@lem706885). Qed.
Lemma lem7654627 : (term445 = term446) = (term447 = term448).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term446). Qed.
Lemma lem7654628 : term447 = term448.
Proof. exact (EQ_MP (@lem7654627) (@lem7654626)). Qed.
Lemma lem7654629 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654630 : term449 = term450.
Proof. exact (MK_COMB (@lem7654629) (@lem7654628)). Qed.
Lemma lem7654631 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7654632 : term444 = term439.
Proof. exact (MK_COMB (@lem7654631) (@lem7654630)). Qed.
Lemma lem7654633 : term436 = term439.
Proof. exact (TRANS (@lem7654625) (@lem7654632)). Qed.
Lemma lem7654634 : term443 = term439.
Proof. exact (TRANS (@lem7654624) (@lem7654633)). Qed.
Lemma lem7654635 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7654636 : term451 = term452.
Proof. exact (MK_COMB (@lem7654635) (@lem7654634)). Qed.
Lemma lem7654637 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7654638 : term453 = term454.
Proof. exact (MK_COMB (@lem7654636) (@lem7654637)). Qed.
Lemma lem7654640 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7654641 : term454 = term455.
Proof. exact (@lem7654640 term448 term117). Qed.
Lemma lem7654642 : term456 = term446.
Proof. exact (@lem996237 term446). Qed.
Lemma lem7654643 : (term456 = term446) = (term457 = term448).
Proof. exact (@lem1007663 term446 (BIT1 0) term446). Qed.
Lemma lem7654644 : term457 = term448.
Proof. exact (EQ_MP (@lem7654643) (@lem7654642)). Qed.
Lemma lem7654645 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654646 : term458 = term450.
Proof. exact (MK_COMB (@lem7654645) (@lem7654644)). Qed.
Lemma lem7654647 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7654648 : term455 = term439.
Proof. exact (MK_COMB (@lem7654647) (@lem7654646)). Qed.
Lemma lem7654649 : term454 = term439.
Proof. exact (TRANS (@lem7654641) (@lem7654648)). Qed.
Lemma lem7654650 : term453 = term439.
Proof. exact (TRANS (@lem7654638) (@lem7654649)). Qed.
Lemma lem7654652 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7654653 : term175 = term176.
Proof. exact (@lem7654652 term117 term117). Qed.
Lemma lem7654654 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7654655 : term178 = term117.
Proof. exact (EQ_MP (@lem7654654) (@lem940073)). Qed.
Lemma lem7654656 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654657 : term176 = term116.
Proof. exact (MK_COMB (@lem7654656) (@lem7654655)). Qed.
Lemma lem7654658 : term175 = term116.
Proof. exact (TRANS (@lem7654653) (@lem7654657)). Qed.
Lemma lem7654659 : term452 = term452.
Proof. exact (eq_refl term452). Qed.
Lemma lem7654660 : term459 = term454.
Proof. exact (MK_COMB (@lem7654659) (@lem7654658)). Qed.
Lemma lem7654662 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7654663 : term454 = term455.
Proof. exact (@lem7654662 term448 term117). Qed.
Lemma lem7654664 : term456 = term446.
Proof. exact (@lem996237 term446). Qed.
Lemma lem7654665 : (term456 = term446) = (term457 = term448).
Proof. exact (@lem1007663 term446 (BIT1 0) term446). Qed.
Lemma lem7654666 : term457 = term448.
Proof. exact (EQ_MP (@lem7654665) (@lem7654664)). Qed.
Lemma lem7654667 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654668 : term458 = term450.
Proof. exact (MK_COMB (@lem7654667) (@lem7654666)). Qed.
Lemma lem7654669 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7654670 : term455 = term439.
Proof. exact (MK_COMB (@lem7654669) (@lem7654668)). Qed.
Lemma lem7654671 : term454 = term439.
Proof. exact (TRANS (@lem7654663) (@lem7654670)). Qed.
Lemma lem7654672 : term459 = term439.
Proof. exact (TRANS (@lem7654660) (@lem7654671)). Qed.
Lemma lem7654673 : term439 = term459.
Proof. exact (SYM (@lem7654672)). Qed.
Lemma lem7654674 : term453 = term459.
Proof. exact (TRANS (@lem7654650) (@lem7654673)). Qed.
Lemma lem7654675 : term437 = term460.
Proof. exact (@lem7654601 (@lem7654674)). Qed.
Lemma lem7654676 : term436 = term460.
Proof. exact (TRANS (@lem7654567) (@lem7654675)). Qed.
Lemma lem7654678 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7654679 : term460 = term439.
Proof. exact (@lem7654678 term439). Qed.
Lemma lem7654680 : term436 = term439.
Proof. exact (TRANS (@lem7654676) (@lem7654679)). Qed.
Lemma lem7654681 (_98528 : int) : (term508 _98528) = term461.
Proof. exact (MK_COMB (@lem7654558 _98528) (@lem7654680)). Qed.
Lemma lem7654682 (_98528 : int) : (term507 _98528) = term461.
Proof. exact (TRANS (@lem7654450 _98528) (@lem7654681 _98528)). Qed.
Lemma lem7654683 : term461 = term439.
Proof. exact (@lem1982721 term439). Qed.
Lemma lem7654684 (_98528 : int) : (term507 _98528) = term439.
Proof. exact (TRANS (@lem7654682 _98528) (@lem7654683)). Qed.
Lemma lem7654685 (_98526 : int) (_98528 : int) : (term506 _98526 _98528) = term461.
Proof. exact (MK_COMB (@lem7654449 _98526) (@lem7654684 _98528)). Qed.
Lemma lem7654686 (_98526 : int) (_98528 : int) : (term505 _98526 _98528) = term461.
Proof. exact (TRANS (@lem7654341 _98526 _98528) (@lem7654685 _98526 _98528)). Qed.
Lemma lem7654687 : term461 = term439.
Proof. exact (@lem1982721 term439). Qed.
Lemma lem7654688 (_98526 : int) (_98528 : int) : (term505 _98526 _98528) = term439.
Proof. exact (TRANS (@lem7654686 _98526 _98528) (@lem7654687)). Qed.
Lemma lem7654689 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7654690 (_98526 : int) (_98528 : int) : (term509 _98526 _98528) = term463.
Proof. exact (MK_COMB (@lem7654689) (@lem7654688 _98526 _98528)). Qed.
Lemma lem7654691 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7654692 (_98526 : int) (_98528 : int) : (term504 _98526 _98528) = term464.
Proof. exact (MK_COMB (@lem7654690 _98526 _98528) (@lem7654691)). Qed.
Lemma lem7654693 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : term464.
Proof. exact (EQ_MP (@lem7654692 _98526 _98528) (@lem7654340 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654695 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7654696 : term464 = term465.
Proof. exact (@lem7654695 term102 term439). Qed.
Lemma lem7654698 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7654699 : term439 = term460.
Proof. exact (@lem7654698 term448). Qed.
Lemma lem7654701 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7654702 : term102 = term163.
Proof. exact (@lem7654701 (NUMERAL 0)). Qed.
Lemma lem7654703 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7654704 : term104 = term394.
Proof. exact (MK_COMB (@lem7654703) (@lem7654702)). Qed.
Lemma lem7654705 : term465 = term466.
Proof. exact (MK_COMB (@lem7654704) (@lem7654699)). Qed.
Lemma lem7654706 : term467.
Proof. exact (@lem1980026 term102 term116 term439 term116). Qed.
Lemma lem7654708 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654709 : term313 = term319.
Proof. exact (@lem7654708 (NUMERAL 0) term117). Qed.
Lemma lem7654710 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654711 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654712 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654711 h1) (fun h1 : term319 = True => @lem7654710)). Qed.
Lemma lem7654713 : term319 = True.
Proof. exact (EQ_MP (@lem7654712) (@lem7654710)). Qed.
Lemma lem7654714 : term313 = True.
Proof. exact (TRANS (@lem7654709) (@lem7654713)). Qed.
Lemma lem7654715 : True = term313.
Proof. exact (SYM (@lem7654714)). Qed.
Lemma lem7654716 : term313.
Proof. exact (EQ_MP (@lem7654715) (@lem0)). Qed.
Lemma lem7654717 : term468.
Proof. exact (@lem7654706 (@lem7654716)). Qed.
Lemma lem7654719 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7654720 : term313 = term319.
Proof. exact (@lem7654719 (NUMERAL 0) term117). Qed.
Lemma lem7654721 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7654722 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7654723 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7654722 h1) (fun h1 : term319 = True => @lem7654721)). Qed.
Lemma lem7654724 : term319 = True.
Proof. exact (EQ_MP (@lem7654723) (@lem7654721)). Qed.
Lemma lem7654725 : term313 = True.
Proof. exact (TRANS (@lem7654720) (@lem7654724)). Qed.
Lemma lem7654726 : True = term313.
Proof. exact (SYM (@lem7654725)). Qed.
Lemma lem7654727 : term313.
Proof. exact (EQ_MP (@lem7654726) (@lem0)). Qed.
Lemma lem7654728 : term466 = term469.
Proof. exact (@lem7654717 (@lem7654727)). Qed.
Lemma lem7654730 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7654731 : term454 = term455.
Proof. exact (@lem7654730 term448 term117). Qed.
Lemma lem7654732 : term456 = term446.
Proof. exact (@lem996237 term446). Qed.
Lemma lem7654733 : (term456 = term446) = (term457 = term448).
Proof. exact (@lem1007663 term446 (BIT1 0) term446). Qed.
Lemma lem7654734 : term457 = term448.
Proof. exact (EQ_MP (@lem7654733) (@lem7654732)). Qed.
Lemma lem7654735 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7654736 : term458 = term450.
Proof. exact (MK_COMB (@lem7654735) (@lem7654734)). Qed.
Lemma lem7654737 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7654738 : term455 = term439.
Proof. exact (MK_COMB (@lem7654737) (@lem7654736)). Qed.
Lemma lem7654739 : term454 = term439.
Proof. exact (TRANS (@lem7654731) (@lem7654738)). Qed.
Lemma lem7654741 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7654742 : term324 = term102.
Proof. exact (@lem7654741 term117). Qed.
Lemma lem7654743 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7654744 : term399 = term104.
Proof. exact (MK_COMB (@lem7654743) (@lem7654742)). Qed.
Lemma lem7654745 : term469 = term465.
Proof. exact (MK_COMB (@lem7654744) (@lem7654739)). Qed.
Lemma lem7654747 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7654748 : term465 = term470.
Proof. exact (@lem7654747 (NUMERAL 0) term448). Qed.
Lemma lem7654749 : term471 = term446.
Proof. exact (@lem912803). Qed.
Lemma lem7654750 (h1 : term471 = term446) : (term448 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term446 h1). Qed.
Lemma lem7654751 : (term471 = term446) = ((term448 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term471 = term446 => @lem7654750 h1) (fun h1 : (term448 = (NUMERAL 0)) = False => @lem7654749)). Qed.
Lemma lem7654752 : (term448 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7654751) (@lem7654749)). Qed.
Lemma lem7654753 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7654754 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7654755 : term403 = (and True).
Proof. exact (MK_COMB (@lem7654754) (@lem7654753)). Qed.
Lemma lem7654756 : term470 = (True /\ False).
Proof. exact (MK_COMB (@lem7654755) (@lem7654752)). Qed.
Lemma lem7654758 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7654759 : term470 = False.
Proof. exact (TRANS (@lem7654756) (@lem7654758)). Qed.
Lemma lem7654760 : term465 = False.
Proof. exact (TRANS (@lem7654748) (@lem7654759)). Qed.
Lemma lem7654761 : term469 = False.
Proof. exact (TRANS (@lem7654745) (@lem7654760)). Qed.
Lemma lem7654762 : term466 = False.
Proof. exact (TRANS (@lem7654728) (@lem7654761)). Qed.
Lemma lem7654763 : term465 = False.
Proof. exact (TRANS (@lem7654705) (@lem7654762)). Qed.
Lemma lem7654764 : term464 = False.
Proof. exact (TRANS (@lem7654696) (@lem7654763)). Qed.
Lemma lem7654765 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term635 _98526 _98528 _98527) : False.
Proof. exact (EQ_MP (@lem7654764) (@lem7654693 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654766 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term606 _98526 _98528 _98527) : False.
Proof. exact (or_elim (@lem7653396 _98526 _98528 _98527 h1) (fun h0 : term609 _98526 _98528 _98527 => @lem7654174 _98526 _98528 _98527 h0) (fun h0 : term635 _98526 _98528 _98527 => @lem7654765 _98526 _98528 _98527 h0)). Qed.
Lemma lem7654768 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term606 _98526 _98528 _98527) : term606 _98526 _98528 _98527.
Proof. exact (h1). Qed.
Lemma lem7654769 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term606 _98526 _98528 _98527) : (term606 _98526 _98528 _98527) = False.
Proof. exact (prop_ext (fun h2 : term606 _98526 _98528 _98527 => @lem7654766 _98526 _98528 _98527 h1) (fun h2 : False => @lem7654768 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654770 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term606 _98526 _98528 _98527) : False.
Proof. exact (EQ_MP (@lem7654769 _98526 _98528 _98527 h1) (@lem7654768 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654771 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term568 _98526 _98528 _98527) : term568 _98526 _98528 _98527.
Proof. exact (h1). Qed.
Lemma lem7654772 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term568 _98526 _98528 _98527) : term606 _98526 _98528 _98527.
Proof. exact (EQ_MP (@lem7653386 _98526 _98528 _98527) (@lem7654771 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654773 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term568 _98526 _98528 _98527) : (term606 _98526 _98528 _98527) = False.
Proof. exact (prop_ext (fun h2 : term606 _98526 _98528 _98527 => @lem7654770 _98526 _98528 _98527 h2) (fun h2 : False => @lem7654772 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654774 (_98526 : int) (_98528 : int) (_98527 : int) (h1 : term568 _98526 _98528 _98527) : False.
Proof. exact (EQ_MP (@lem7654773 _98526 _98528 _98527 h1) (@lem7654772 _98526 _98528 _98527 h1)). Qed.
Lemma lem7654775 (_98526 : int) (_98528 : int) (_98527 : int) : term636 _98526 _98528 _98527.
Proof. exact (fun h0 : term568 _98526 _98528 _98527 => @lem7654774 _98526 _98528 _98527 h0). Qed.
Lemma lem7654776 (_98526 : int) (_98528 : int) (_98527 : int) : term637 _98526 _98528 _98527.
Proof. exact (@lem1386578 (term638 _98526 _98528 _98527)). Qed.
Lemma lem7654779 (_98526 : int) (_98528 : int) (_98527 : int) : term638 _98526 _98528 _98527.
Proof. exact (@lem7654776 _98526 _98528 _98527 (@lem7654775 _98526 _98528 _98527)). Qed.
Lemma lem7654780 (_98528 : int) (_98526 : int) (_98527 : int) : (term567 _98526 _98528 _98527) = (term557 _98528 _98526 _98527).
Proof. exact (SYM (@lem7652677 _98526 _98528 _98527)). Qed.
Lemma lem7654781 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7654782 (_98528 : int) (_98526 : int) (_98527 : int) : (term638 _98526 _98528 _98527) = (term538 _98528 _98526 _98527).
Proof. exact (MK_COMB (@lem7654781) (@lem7654780 _98528 _98526 _98527)). Qed.
Lemma lem7654783 (_98528 : int) (_98526 : int) (_98527 : int) : term538 _98528 _98526 _98527.
Proof. exact (EQ_MP (@lem7654782 _98528 _98526 _98527) (@lem7654779 _98526 _98528 _98527)). Qed.
Lemma lem7654784 (_98528 : int) (_98526 : int) (_98527 : int) : term539 _98528 _98526 _98527.
Proof. exact (EQ_MP (@lem7652422 _98528 _98526 _98527) (@lem7654783 _98528 _98526 _98527)). Qed.
Lemma lem7654785 (i : nat) (a : nat) (d : nat) : term639 i a d.
Proof. exact (@lem7654784 (int_of_num i) (int_of_num a) (int_of_num d)). Qed.
Lemma lem7654786 (i : nat) (a : nat) (d : nat) : term640 i a d.
Proof. exact (@lem7654785 i a d (@lem7652415 a)). Qed.
Lemma lem7654787 (i : nat) (a : nat) (d : nat) : term641 i a d.
Proof. exact (@lem7654786 i a d (@lem7652418 d)). Qed.
Lemma lem7654788 (i : nat) (a : nat) (d : nat) : term535 i a d.
Proof. exact (@lem7654787 i a d (@lem7652421 i)). Qed.
Lemma lem7654789 (i : nat) (a : nat) : term537 i a.
Proof. exact (fun d : nat => @lem7654788 i a d). Qed.
Lemma lem7654790 (i : nat) (a : nat) : (term537 i a) = (term519 i a).
Proof. exact (SYM (@lem7652412 i a)). Qed.
Lemma lem7654791 (i : nat) (a : nat) : term519 i a.
Proof. exact (EQ_MP (@lem7654790 i a) (@lem7654789 i a)). Qed.
Lemma lem7654808 (i : nat) (a : nat) (b : nat) : (term642 i a b) = (term643 i a b).
Proof. exact (@lem17265 (term644 i a b) (term645 i a b)). Qed.
Lemma lem7654809 (i : nat) (a : nat) (b : nat) : (term646 b i a) = (term647 i a b).
Proof. exact (@lem1032781 i a (term648 i a b)). Qed.
Lemma lem7654810 (i : nat) (a : nat) (d : nat) (b : nat) : (term649 i a b d) = (term650 i a d b).
Proof. exact (eq_refl (term649 i a b d)). Qed.
Lemma lem7654811 (i : nat) (a : nat) (d : nat) : (term13 i a d) = (term13 i a d).
Proof. exact (eq_refl (term13 i a d)). Qed.
Lemma lem7654812 (i : nat) (a : nat) (d : nat) (b : nat) : (term651 i a b d) = (term652 i a d b).
Proof. exact (MK_COMB (@lem7654811 i a d) (@lem7654810 i a d b)). Qed.
Lemma lem7654813 (i : nat) (a : nat) (b : nat) : (term653 i a b) = (term654 i a b).
Proof. exact (fun_ext (fun d : nat => @lem7654812 i a d b)). Qed.
Lemma lem7654814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7654815 (i : nat) (a : nat) (b : nat) : (term647 i a b) = (term655 i a b).
Proof. exact (MK_COMB (@lem7654814) (@lem7654813 i a b)). Qed.
Lemma lem7654816 (i : nat) (a : nat) (b : nat) : (term646 b i a) = (term643 i a b).
Proof. exact (eq_refl (term646 b i a)). Qed.
Lemma lem7654817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7654818 (i : nat) (a : nat) (b : nat) : (term656 b i a) = (term657 i a b).
Proof. exact (MK_COMB (@lem7654817) (@lem7654816 i a b)). Qed.
Lemma lem7654819 (i : nat) (a : nat) (b : nat) : ((term646 b i a) = (term647 i a b)) = ((term643 i a b) = (term655 i a b)).
Proof. exact (MK_COMB (@lem7654818 i a b) (@lem7654815 i a b)). Qed.
Lemma lem7654820 (i : nat) (a : nat) (b : nat) : (term643 i a b) = (term655 i a b).
Proof. exact (EQ_MP (@lem7654819 i a b) (@lem7654809 i a b)). Qed.
Lemma lem7654821 (i : nat) (a : nat) (d : nat) (b : nat) : (term652 i a d b) = (term652 i a d b).
Proof. exact (eq_refl (term652 i a d b)). Qed.
Lemma lem7654822 (i : nat) (a : nat) (b : nat) : (term654 i a b) = (term654 i a b).
Proof. exact (fun_ext (fun d : nat => @lem7654821 i a d b)). Qed.
Lemma lem7654823 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7654824 (i : nat) (a : nat) (b : nat) : (term655 i a b) = (term655 i a b).
Proof. exact (MK_COMB (@lem7654823) (@lem7654822 i a b)). Qed.
Lemma lem7654825 (i : nat) (a : nat) (b : nat) : (term657 i a b) = (term657 i a b).
Proof. exact (eq_refl (term657 i a b)). Qed.
Lemma lem7654826 (i : nat) (a : nat) (b : nat) : ((term643 i a b) = (term655 i a b)) = ((term643 i a b) = (term655 i a b)).
Proof. exact (MK_COMB (@lem7654825 i a b) (@lem7654824 i a b)). Qed.
Lemma lem7654827 (i : nat) (a : nat) (b : nat) : (term643 i a b) = (term655 i a b).
Proof. exact (EQ_MP (@lem7654826 i a b) (@lem7654820 i a b)). Qed.
Lemma lem7654850 (i : nat) (a : nat) (b : nat) : (term642 i a b) = (term655 i a b).
Proof. exact (TRANS (@lem7654808 i a b) (@lem7654827 i a b)). Qed.
Lemma lem7654907 (i : nat) (a : nat) (d : nat) (b : nat) : (term652 i a d b) = (term652 i a d b).
Proof. exact (eq_refl (term652 i a d b)). Qed.
Lemma lem7654908 (i : nat) (a : nat) (b : nat) : (term654 i a b) = (term654 i a b).
Proof. exact (fun_ext (fun d : nat => @lem7654907 i a d b)). Qed.
Lemma lem7654909 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7654910 (i : nat) (a : nat) (b : nat) : (term655 i a b) = (term655 i a b).
Proof. exact (MK_COMB (@lem7654909) (@lem7654908 i a b)). Qed.
Lemma lem7654913 (i : nat) (a : nat) (b : nat) : (term642 i a b) = (term655 i a b).
Proof. exact (TRANS (@lem7654850 i a b) (@lem7654910 i a b)). Qed.
Lemma lem7654915 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7654916 (i : nat) (a : nat) (d : nat) : (i = (Nat.add a d)) = ((int_of_num i) = (term26 a d)).
Proof. exact (@lem7654915 i (Nat.add a d)). Qed.
Lemma lem7654920 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7654921 (a : nat) (d : nat) : (term26 a d) = (term27 a d).
Proof. exact (@lem7654920 a d). Qed.
Lemma lem7654922 (i : nat) : (term28 i) = (term28 i).
Proof. exact (eq_refl (term28 i)). Qed.
Lemma lem7654923 (i : nat) (a : nat) (d : nat) : ((int_of_num i) = (term26 a d)) = ((int_of_num i) = (term27 a d)).
Proof. exact (MK_COMB (@lem7654922 i) (@lem7654921 a d)). Qed.
Lemma lem7654924 (i : nat) (a : nat) (d : nat) : (i = (Nat.add a d)) = ((int_of_num i) = (term27 a d)).
Proof. exact (TRANS (@lem7654916 i a d) (@lem7654923 i a d)). Qed.
Lemma lem7654925 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7654926 (i : nat) (a : nat) (d : nat) : (term29 i a d) = (term30 i a d).
Proof. exact (MK_COMB (@lem7654925) (@lem7654924 i a d)). Qed.
Lemma lem7654927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7654928 (i : nat) (a : nat) (d : nat) : (term31 i a d) = (term32 i a d).
Proof. exact (MK_COMB (@lem7654927) (@lem7654926 i a d)). Qed.
Lemma lem7654930 (m : nat) (n : nat) : (Peano.lt m n) = (term33 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem7654931 (i : nat) (a : nat) : (Peano.lt i a) = (term33 i a).
Proof. exact (@lem7654930 i a). Qed.
Lemma lem7654932 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7654933 (i : nat) (a : nat) : (term34 i a) = (term35 i a).
Proof. exact (MK_COMB (@lem7654932) (@lem7654931 i a)). Qed.
Lemma lem7654934 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7654935 (i : nat) (a : nat) : (term36 i a) = (term37 i a).
Proof. exact (MK_COMB (@lem7654934) (@lem7654933 i a)). Qed.
Lemma lem7654937 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7654938 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term38).
Proof. exact (@lem7654937 d (NUMERAL 0)). Qed.
Lemma lem7654941 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7654942 (d : nat) : (term39 d) = (term40 d).
Proof. exact (MK_COMB (@lem7654941) (@lem7654938 d)). Qed.
Lemma lem7654943 (i : nat) (a : nat) (d : nat) : (term41 i a d) = (term42 i a d).
Proof. exact (MK_COMB (@lem7654935 i a) (@lem7654942 d)). Qed.
Lemma lem7654944 (i : nat) (a : nat) (d : nat) : (term43 i a d) = (term44 i a d).
Proof. exact (MK_COMB (@lem7654928 i a d) (@lem7654943 i a d)). Qed.
Lemma lem7654945 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7654946 (i : nat) (a : nat) (d : nat) : (term13 i a d) = (term45 i a d).
Proof. exact (MK_COMB (@lem7654945) (@lem7654944 i a d)). Qed.
Lemma lem7654948 (m : nat) (n : nat) : (Peano.le m n) = (term46 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7654949 (i : nat) (a : nat) (b : nat) : (term644 i a b) = (term658 i a b).
Proof. exact (@lem7654948 i (Nat.add a b)). Qed.
Lemma lem7654951 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7654952 (a : nat) (b : nat) : (term26 a b) = (term27 a b).
Proof. exact (@lem7654951 a b). Qed.
Lemma lem7654953 (i : nat) : (term659 i) = (term659 i).
Proof. exact (eq_refl (term659 i)). Qed.
Lemma lem7654954 (i : nat) (a : nat) (b : nat) : (term658 i a b) = (term660 i a b).
Proof. exact (MK_COMB (@lem7654953 i) (@lem7654952 a b)). Qed.
Lemma lem7654955 (i : nat) (a : nat) (b : nat) : (term644 i a b) = (term660 i a b).
Proof. exact (TRANS (@lem7654949 i a b) (@lem7654954 i a b)). Qed.
Lemma lem7654956 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7654957 (i : nat) (a : nat) (b : nat) : (term661 i a b) = (term662 i a b).
Proof. exact (MK_COMB (@lem7654956) (@lem7654955 i a b)). Qed.
Lemma lem7654958 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7654959 (i : nat) (a : nat) (b : nat) : (term663 i a b) = (term664 i a b).
Proof. exact (MK_COMB (@lem7654958) (@lem7654957 i a b)). Qed.
Lemma lem7654961 (m : nat) (n : nat) : (Peano.le m n) = (term46 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7654962 (d : nat) (b : nat) : (Peano.le d b) = (term46 d b).
Proof. exact (@lem7654961 d b). Qed.
Lemma lem7654963 (i : nat) (a : nat) (d : nat) (b : nat) : (term650 i a d b) = (term665 i a d b).
Proof. exact (MK_COMB (@lem7654959 i a b) (@lem7654962 d b)). Qed.
Lemma lem7654964 (i : nat) (a : nat) (d : nat) (b : nat) : (term652 i a d b) = (term666 i a d b).
Proof. exact (MK_COMB (@lem7654946 i a d) (@lem7654963 i a d b)). Qed.
Lemma lem7654965 (i : nat) (a : nat) (b : nat) : (term654 i a b) = (term667 i a b).
Proof. exact (fun_ext (fun d : nat => @lem7654964 i a d b)). Qed.
Lemma lem7654966 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7654967 (i : nat) (a : nat) (b : nat) : (term655 i a b) = (term668 i a b).
Proof. exact (MK_COMB (@lem7654966) (@lem7654965 i a b)). Qed.
Lemma lem7654968 (i : nat) (a : nat) (b : nat) : (term642 i a b) = (term668 i a b).
Proof. exact (TRANS (@lem7654913 i a b) (@lem7654967 i a b)). Qed.
Lemma lem7654969 (a : nat) : term54 a.
Proof. exact (@lem2307535 a). Qed.
Lemma lem7654970 (a : nat) : (term54 a) = (term55 a).
Proof. exact (eq_refl (term54 a)). Qed.
Lemma lem7654971 (a : nat) : term55 a.
Proof. exact (EQ_MP (@lem7654970 a) (@lem7654969 a)). Qed.
Lemma lem7654972 (b : nat) : term54 b.
Proof. exact (@lem2307535 b). Qed.
Lemma lem7654973 (b : nat) : (term54 b) = (term55 b).
Proof. exact (eq_refl (term54 b)). Qed.
Lemma lem7654974 (b : nat) : term55 b.
Proof. exact (EQ_MP (@lem7654973 b) (@lem7654972 b)). Qed.
Lemma lem7654975 (d : nat) : term54 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem7654976 (d : nat) : (term54 d) = (term55 d).
Proof. exact (eq_refl (term54 d)). Qed.
Lemma lem7654977 (d : nat) : term55 d.
Proof. exact (EQ_MP (@lem7654976 d) (@lem7654975 d)). Qed.
Lemma lem7654978 (i : nat) : term54 i.
Proof. exact (@lem2307535 i). Qed.
Lemma lem7654979 (i : nat) : (term54 i) = (term55 i).
Proof. exact (eq_refl (term54 i)). Qed.
Lemma lem7654980 (i : nat) : term55 i.
Proof. exact (EQ_MP (@lem7654979 i) (@lem7654978 i)). Qed.
Lemma lem7654981 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term669 _98537 _98534 _98536 _98535) = (term670 _98537 _98534 _98536 _98535).
Proof. exact (@lem2318604 (term670 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655009 (_98537 : int) (_98534 : int) (_98536 : int) : (term58 _98537 _98534 _98536) = (_98537 = (int_add _98534 _98536)).
Proof. exact (@lem16933 (_98537 = (int_add _98534 _98536))). Qed.
Lemma lem7655012 (_98537 : int) (_98534 : int) : (term59 _98537 _98534) = (int_lt _98537 _98534).
Proof. exact (@lem16933 (int_lt _98537 _98534)). Qed.
Lemma lem7655015 (_98536 : int) : (term60 _98536) = (_98536 = term38).
Proof. exact (@lem16933 (_98536 = term38)). Qed.
Lemma lem7655016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655017 (_98537 : int) (_98534 : int) : (term61 _98537 _98534) = (term62 _98537 _98534).
Proof. exact (MK_COMB (@lem7655016) (@lem7655012 _98537 _98534)). Qed.
Lemma lem7655018 (_98537 : int) (_98534 : int) (_98536 : int) : (term63 _98537 _98534 _98536) = (term64 _98537 _98534 _98536).
Proof. exact (MK_COMB (@lem7655017 _98537 _98534) (@lem7655015 _98536)). Qed.
Lemma lem7655019 (_98537 : int) (_98534 : int) (_98536 : int) : (term65 _98537 _98534 _98536) = (term63 _98537 _98534 _98536).
Proof. exact (@lem17160 (term66 _98537 _98534) (term67 _98536)). Qed.
Lemma lem7655020 (_98537 : int) (_98534 : int) (_98536 : int) : (term65 _98537 _98534 _98536) = (term64 _98537 _98534 _98536).
Proof. exact (TRANS (@lem7655019 _98537 _98534 _98536) (@lem7655018 _98537 _98534 _98536)). Qed.
Lemma lem7655021 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7655022 (_98537 : int) (_98534 : int) (_98536 : int) : (term68 _98537 _98534 _98536) = (term69 _98537 _98534 _98536).
Proof. exact (MK_COMB (@lem7655021) (@lem7655009 _98537 _98534 _98536)). Qed.
Lemma lem7655023 (_98537 : int) (_98534 : int) (_98536 : int) : (term70 _98537 _98534 _98536) = (term71 _98537 _98534 _98536).
Proof. exact (MK_COMB (@lem7655022 _98537 _98534 _98536) (@lem7655020 _98537 _98534 _98536)). Qed.
Lemma lem7655024 (_98537 : int) (_98534 : int) (_98536 : int) : (term72 _98537 _98534 _98536) = (term70 _98537 _98534 _98536).
Proof. exact (@lem17045 (term73 _98537 _98534 _98536) (term74 _98537 _98534 _98536)). Qed.
Lemma lem7655025 (_98537 : int) (_98534 : int) (_98536 : int) : (term72 _98537 _98534 _98536) = (term71 _98537 _98534 _98536).
Proof. exact (TRANS (@lem7655024 _98537 _98534 _98536) (@lem7655023 _98537 _98534 _98536)). Qed.
Lemma lem7655028 (_98537 : int) (_98534 : int) (_98535 : int) : (term671 _98537 _98534 _98535) = (term672 _98537 _98534 _98535).
Proof. exact (@lem16933 (term672 _98537 _98534 _98535)). Qed.
Lemma lem7655029 (_98536 : int) (_98535 : int) : (term127 _98536 _98535) = (term127 _98536 _98535).
Proof. exact (eq_refl (term127 _98536 _98535)). Qed.
Lemma lem7655030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655031 (_98537 : int) (_98534 : int) (_98535 : int) : (term673 _98537 _98534 _98535) = (term674 _98537 _98534 _98535).
Proof. exact (MK_COMB (@lem7655030) (@lem7655028 _98537 _98534 _98535)). Qed.
Lemma lem7655032 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term675 _98537 _98534 _98536 _98535) = (term676 _98537 _98534 _98536 _98535).
Proof. exact (MK_COMB (@lem7655031 _98537 _98534 _98535) (@lem7655029 _98536 _98535)). Qed.
Lemma lem7655033 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term677 _98537 _98534 _98536 _98535) = (term675 _98537 _98534 _98536 _98535).
Proof. exact (@lem17160 (term678 _98537 _98534 _98535) (int_le _98536 _98535)). Qed.
Lemma lem7655034 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term677 _98537 _98534 _98536 _98535) = (term676 _98537 _98534 _98536 _98535).
Proof. exact (TRANS (@lem7655033 _98537 _98534 _98536 _98535) (@lem7655032 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655036 (_98537 : int) (_98534 : int) (_98536 : int) : (term77 _98537 _98534 _98536) = (term78 _98537 _98534 _98536).
Proof. exact (MK_COMB (@lem7655035) (@lem7655025 _98537 _98534 _98536)). Qed.
Lemma lem7655037 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term679 _98537 _98534 _98536 _98535) = (term680 _98537 _98534 _98536 _98535).
Proof. exact (MK_COMB (@lem7655036 _98537 _98534 _98536) (@lem7655034 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655038 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term681 _98537 _98534 _98536 _98535) = (term679 _98537 _98534 _98536 _98535).
Proof. exact (@lem17160 (term82 _98537 _98534 _98536) (term682 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655039 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term681 _98537 _98534 _98536 _98535) = (term680 _98537 _98534 _98536 _98535).
Proof. exact (TRANS (@lem7655038 _98537 _98534 _98536 _98535) (@lem7655037 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655041 (_98537 : int) : (term84 _98537) = (term84 _98537).
Proof. exact (eq_refl (term84 _98537)). Qed.
Lemma lem7655042 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term683 _98537 _98534 _98536 _98535) = (term684 _98537 _98534 _98536 _98535).
Proof. exact (MK_COMB (@lem7655041 _98537) (@lem7655039 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655043 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term685 _98537 _98534 _98536 _98535) = (term683 _98537 _98534 _98536 _98535).
Proof. exact (@lem17362 (term88 _98537) (term686 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655044 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term685 _98537 _98534 _98536 _98535) = (term684 _98537 _98534 _98536 _98535).
Proof. exact (TRANS (@lem7655043 _98537 _98534 _98536 _98535) (@lem7655042 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655046 (_98536 : int) : (term84 _98536) = (term84 _98536).
Proof. exact (eq_refl (term84 _98536)). Qed.
Lemma lem7655047 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term687 _98537 _98534 _98536 _98535) = (term688 _98537 _98534 _98536 _98535).
Proof. exact (MK_COMB (@lem7655046 _98536) (@lem7655044 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655048 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term689 _98537 _98534 _98536 _98535) = (term687 _98537 _98534 _98536 _98535).
Proof. exact (@lem17362 (term88 _98536) (term690 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655049 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term689 _98537 _98534 _98536 _98535) = (term688 _98537 _98534 _98536 _98535).
Proof. exact (TRANS (@lem7655048 _98537 _98534 _98536 _98535) (@lem7655047 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655051 (_98535 : int) : (term84 _98535) = (term84 _98535).
Proof. exact (eq_refl (term84 _98535)). Qed.
Lemma lem7655052 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term691 _98537 _98534 _98536 _98535) = (term692 _98537 _98534 _98536 _98535).
Proof. exact (MK_COMB (@lem7655051 _98535) (@lem7655049 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655053 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term693 _98537 _98534 _98536 _98535) = (term691 _98537 _98534 _98536 _98535).
Proof. exact (@lem17362 (term88 _98535) (term694 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655054 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term693 _98537 _98534 _98536 _98535) = (term692 _98537 _98534 _98536 _98535).
Proof. exact (TRANS (@lem7655053 _98537 _98534 _98536 _98535) (@lem7655052 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655056 (_98534 : int) : (term84 _98534) = (term84 _98534).
Proof. exact (eq_refl (term84 _98534)). Qed.
Lemma lem7655057 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term695 _98537 _98534 _98536 _98535) = (term696 _98537 _98534 _98536 _98535).
Proof. exact (MK_COMB (@lem7655056 _98534) (@lem7655054 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655058 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term697 _98537 _98534 _98536 _98535) = (term695 _98537 _98534 _98536 _98535).
Proof. exact (@lem17362 (term88 _98534) (term698 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655096 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term697 _98537 _98534 _98536 _98535) = (term696 _98537 _98534 _98536 _98535).
Proof. exact (TRANS (@lem7655058 _98537 _98534 _98536 _98535) (@lem7655057 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7655099 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7655100 (_98534 : int) : (term88 _98534) = (term99 _98534).
Proof. exact (@lem7655099 term38 _98534). Qed.
Lemma lem7655102 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7655103 : term101 = term102.
Proof. exact (@lem7655102 (NUMERAL 0)). Qed.
Lemma lem7655104 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7655105 : term103 = term104.
Proof. exact (MK_COMB (@lem7655104) (@lem7655103)). Qed.
Lemma lem7655106 (_98534 : int) : (real_of_int _98534) = (real_of_int _98534).
Proof. exact (eq_refl (real_of_int _98534)). Qed.
Lemma lem7655107 (_98534 : int) : (term99 _98534) = (term105 _98534).
Proof. exact (MK_COMB (@lem7655105) (@lem7655106 _98534)). Qed.
Lemma lem7655109 (_98534 : int) : (term88 _98534) = (term105 _98534).
Proof. exact (TRANS (@lem7655100 _98534) (@lem7655107 _98534)). Qed.
Lemma lem7655112 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7655113 (_98535 : int) : (term88 _98535) = (term99 _98535).
Proof. exact (@lem7655112 term38 _98535). Qed.
Lemma lem7655115 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7655116 : term101 = term102.
Proof. exact (@lem7655115 (NUMERAL 0)). Qed.
Lemma lem7655117 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7655118 : term103 = term104.
Proof. exact (MK_COMB (@lem7655117) (@lem7655116)). Qed.
Lemma lem7655119 (_98535 : int) : (real_of_int _98535) = (real_of_int _98535).
Proof. exact (eq_refl (real_of_int _98535)). Qed.
Lemma lem7655120 (_98535 : int) : (term99 _98535) = (term105 _98535).
Proof. exact (MK_COMB (@lem7655118) (@lem7655119 _98535)). Qed.
Lemma lem7655122 (_98535 : int) : (term88 _98535) = (term105 _98535).
Proof. exact (TRANS (@lem7655113 _98535) (@lem7655120 _98535)). Qed.
Lemma lem7655125 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7655126 (_98536 : int) : (term88 _98536) = (term99 _98536).
Proof. exact (@lem7655125 term38 _98536). Qed.
Lemma lem7655128 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7655129 : term101 = term102.
Proof. exact (@lem7655128 (NUMERAL 0)). Qed.
Lemma lem7655130 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7655131 : term103 = term104.
Proof. exact (MK_COMB (@lem7655130) (@lem7655129)). Qed.
Lemma lem7655132 (_98536 : int) : (real_of_int _98536) = (real_of_int _98536).
Proof. exact (eq_refl (real_of_int _98536)). Qed.
Lemma lem7655133 (_98536 : int) : (term99 _98536) = (term105 _98536).
Proof. exact (MK_COMB (@lem7655131) (@lem7655132 _98536)). Qed.
Lemma lem7655135 (_98536 : int) : (term88 _98536) = (term105 _98536).
Proof. exact (TRANS (@lem7655126 _98536) (@lem7655133 _98536)). Qed.
Lemma lem7655138 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7655139 (_98537 : int) : (term88 _98537) = (term99 _98537).
Proof. exact (@lem7655138 term38 _98537). Qed.
Lemma lem7655141 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7655142 : term101 = term102.
Proof. exact (@lem7655141 (NUMERAL 0)). Qed.
Lemma lem7655143 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7655144 : term103 = term104.
Proof. exact (MK_COMB (@lem7655143) (@lem7655142)). Qed.
Lemma lem7655145 (_98537 : int) : (real_of_int _98537) = (real_of_int _98537).
Proof. exact (eq_refl (real_of_int _98537)). Qed.
Lemma lem7655146 (_98537 : int) : (term99 _98537) = (term105 _98537).
Proof. exact (MK_COMB (@lem7655144) (@lem7655145 _98537)). Qed.
Lemma lem7655148 (_98537 : int) : (term88 _98537) = (term105 _98537).
Proof. exact (TRANS (@lem7655139 _98537) (@lem7655146 _98537)). Qed.
Lemma lem7655151 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem7655152 (_98537 : int) (_98534 : int) (_98536 : int) : (_98537 = (int_add _98534 _98536)) = ((real_of_int _98537) = (term106 _98534 _98536)).
Proof. exact (@lem7655151 _98537 (int_add _98534 _98536)). Qed.
Lemma lem7655156 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7655157 (_98534 : int) (_98536 : int) : (term106 _98534 _98536) = (term107 _98534 _98536).
Proof. exact (@lem7655156 _98534 _98536). Qed.
Lemma lem7655158 (_98537 : int) : (term108 _98537) = (term108 _98537).
Proof. exact (eq_refl (term108 _98537)). Qed.
Lemma lem7655159 (_98537 : int) (_98534 : int) (_98536 : int) : ((real_of_int _98537) = (term106 _98534 _98536)) = ((real_of_int _98537) = (term107 _98534 _98536)).
Proof. exact (MK_COMB (@lem7655158 _98537) (@lem7655157 _98534 _98536)). Qed.
Lemma lem7655161 (_98537 : int) (_98534 : int) (_98536 : int) : (_98537 = (int_add _98534 _98536)) = ((real_of_int _98537) = (term107 _98534 _98536)).
Proof. exact (TRANS (@lem7655152 _98537 _98534 _98536) (@lem7655159 _98537 _98534 _98536)). Qed.
Lemma lem7655163 (x : int) (y : int) : (int_lt x y) = (term109 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem7655164 (_98537 : int) (_98534 : int) : (int_lt _98537 _98534) = (term109 _98537 _98534).
Proof. exact (@lem7655163 _98537 _98534). Qed.
Lemma lem7655166 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7655167 (_98537 : int) (_98534 : int) : (term109 _98537 _98534) = (term110 _98537 _98534).
Proof. exact (@lem7655166 (term111 _98537) _98534). Qed.
Lemma lem7655169 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7655170 (_98537 : int) : (term112 _98537) = (term113 _98537).
Proof. exact (@lem7655169 _98537 term114). Qed.
Lemma lem7655172 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7655173 : term115 = term116.
Proof. exact (@lem7655172 term117). Qed.
Lemma lem7655174 (_98537 : int) : (term118 _98537) = (term118 _98537).
Proof. exact (eq_refl (term118 _98537)). Qed.
Lemma lem7655175 (_98537 : int) : (term113 _98537) = (term119 _98537).
Proof. exact (MK_COMB (@lem7655174 _98537) (@lem7655173)). Qed.
Lemma lem7655176 (_98537 : int) : (term112 _98537) = (term119 _98537).
Proof. exact (TRANS (@lem7655170 _98537) (@lem7655175 _98537)). Qed.
Lemma lem7655177 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7655178 (_98537 : int) : (term120 _98537) = (term121 _98537).
Proof. exact (MK_COMB (@lem7655177) (@lem7655176 _98537)). Qed.
Lemma lem7655179 (_98534 : int) : (real_of_int _98534) = (real_of_int _98534).
Proof. exact (eq_refl (real_of_int _98534)). Qed.
Lemma lem7655180 (_98537 : int) (_98534 : int) : (term110 _98537 _98534) = (term122 _98537 _98534).
Proof. exact (MK_COMB (@lem7655178 _98537) (@lem7655179 _98534)). Qed.
Lemma lem7655181 (_98537 : int) (_98534 : int) : (term109 _98537 _98534) = (term122 _98537 _98534).
Proof. exact (TRANS (@lem7655167 _98537 _98534) (@lem7655180 _98537 _98534)). Qed.
Lemma lem7655182 (_98537 : int) (_98534 : int) : (int_lt _98537 _98534) = (term122 _98537 _98534).
Proof. exact (TRANS (@lem7655164 _98537 _98534) (@lem7655181 _98537 _98534)). Qed.
Lemma lem7655185 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem7655186 (_98536 : int) : (_98536 = term38) = ((real_of_int _98536) = term101).
Proof. exact (@lem7655185 _98536 term38). Qed.
Lemma lem7655190 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7655191 : term101 = term102.
Proof. exact (@lem7655190 (NUMERAL 0)). Qed.
Lemma lem7655192 (_98536 : int) : (term108 _98536) = (term108 _98536).
Proof. exact (eq_refl (term108 _98536)). Qed.
Lemma lem7655193 (_98536 : int) : ((real_of_int _98536) = term101) = ((real_of_int _98536) = term102).
Proof. exact (MK_COMB (@lem7655192 _98536) (@lem7655191)). Qed.
Lemma lem7655195 (_98536 : int) : (_98536 = term38) = ((real_of_int _98536) = term102).
Proof. exact (TRANS (@lem7655186 _98536) (@lem7655193 _98536)). Qed.
Lemma lem7655196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655197 (_98537 : int) (_98534 : int) : (term62 _98537 _98534) = (term123 _98537 _98534).
Proof. exact (MK_COMB (@lem7655196) (@lem7655182 _98537 _98534)). Qed.
Lemma lem7655198 (_98537 : int) (_98534 : int) (_98536 : int) : (term64 _98537 _98534 _98536) = (term124 _98537 _98534 _98536).
Proof. exact (MK_COMB (@lem7655197 _98537 _98534) (@lem7655195 _98536)). Qed.
Lemma lem7655199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7655200 (_98537 : int) (_98534 : int) (_98536 : int) : (term69 _98537 _98534 _98536) = (term125 _98537 _98534 _98536).
Proof. exact (MK_COMB (@lem7655199) (@lem7655161 _98537 _98534 _98536)). Qed.
Lemma lem7655201 (_98537 : int) (_98534 : int) (_98536 : int) : (term71 _98537 _98534 _98536) = (term126 _98537 _98534 _98536).
Proof. exact (MK_COMB (@lem7655200 _98537 _98534 _98536) (@lem7655198 _98537 _98534 _98536)). Qed.
Lemma lem7655204 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7655205 (_98537 : int) (_98534 : int) (_98535 : int) : (term672 _98537 _98534 _98535) = (term699 _98537 _98534 _98535).
Proof. exact (@lem7655204 _98537 (int_add _98534 _98535)). Qed.
Lemma lem7655207 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7655208 (_98534 : int) (_98535 : int) : (term106 _98534 _98535) = (term107 _98534 _98535).
Proof. exact (@lem7655207 _98534 _98535). Qed.
Lemma lem7655209 (_98537 : int) : (term700 _98537) = (term700 _98537).
Proof. exact (eq_refl (term700 _98537)). Qed.
Lemma lem7655210 (_98537 : int) (_98534 : int) (_98535 : int) : (term699 _98537 _98534 _98535) = (term701 _98537 _98534 _98535).
Proof. exact (MK_COMB (@lem7655209 _98537) (@lem7655208 _98534 _98535)). Qed.
Lemma lem7655212 (_98537 : int) (_98534 : int) (_98535 : int) : (term672 _98537 _98534 _98535) = (term701 _98537 _98534 _98535).
Proof. exact (TRANS (@lem7655205 _98537 _98534 _98535) (@lem7655210 _98537 _98534 _98535)). Qed.
Lemma lem7655214 (y : int) (x : int) : (term127 x y) = (term109 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7655215 (_98535 : int) (_98536 : int) : (term127 _98536 _98535) = (term109 _98535 _98536).
Proof. exact (@lem7655214 _98535 _98536). Qed.
Lemma lem7655217 (x : int) (y : int) : (int_le x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7655218 (_98535 : int) (_98536 : int) : (term109 _98535 _98536) = (term110 _98535 _98536).
Proof. exact (@lem7655217 (term111 _98535) _98536). Qed.
Lemma lem7655220 (x : int) (y : int) : (term106 x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7655221 (_98535 : int) : (term112 _98535) = (term113 _98535).
Proof. exact (@lem7655220 _98535 term114). Qed.
Lemma lem7655223 (n : nat) : (term100 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7655224 : term115 = term116.
Proof. exact (@lem7655223 term117). Qed.
Lemma lem7655225 (_98535 : int) : (term118 _98535) = (term118 _98535).
Proof. exact (eq_refl (term118 _98535)). Qed.
Lemma lem7655226 (_98535 : int) : (term113 _98535) = (term119 _98535).
Proof. exact (MK_COMB (@lem7655225 _98535) (@lem7655224)). Qed.
Lemma lem7655227 (_98535 : int) : (term112 _98535) = (term119 _98535).
Proof. exact (TRANS (@lem7655221 _98535) (@lem7655226 _98535)). Qed.
Lemma lem7655228 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7655229 (_98535 : int) : (term120 _98535) = (term121 _98535).
Proof. exact (MK_COMB (@lem7655228) (@lem7655227 _98535)). Qed.
Lemma lem7655230 (_98536 : int) : (real_of_int _98536) = (real_of_int _98536).
Proof. exact (eq_refl (real_of_int _98536)). Qed.
Lemma lem7655231 (_98535 : int) (_98536 : int) : (term110 _98535 _98536) = (term122 _98535 _98536).
Proof. exact (MK_COMB (@lem7655229 _98535) (@lem7655230 _98536)). Qed.
Lemma lem7655232 (_98535 : int) (_98536 : int) : (term109 _98535 _98536) = (term122 _98535 _98536).
Proof. exact (TRANS (@lem7655218 _98535 _98536) (@lem7655231 _98535 _98536)). Qed.
Lemma lem7655233 (_98535 : int) (_98536 : int) : (term127 _98536 _98535) = (term122 _98535 _98536).
Proof. exact (TRANS (@lem7655215 _98535 _98536) (@lem7655232 _98535 _98536)). Qed.
Lemma lem7655234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655235 (_98537 : int) (_98534 : int) (_98535 : int) : (term674 _98537 _98534 _98535) = (term702 _98537 _98534 _98535).
Proof. exact (MK_COMB (@lem7655234) (@lem7655212 _98537 _98534 _98535)). Qed.
Lemma lem7655236 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) : (term676 _98537 _98534 _98536 _98535) = (term703 _98537 _98534 _98535 _98536).
Proof. exact (MK_COMB (@lem7655235 _98537 _98534 _98535) (@lem7655233 _98535 _98536)). Qed.
Lemma lem7655237 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655238 (_98537 : int) (_98534 : int) (_98536 : int) : (term78 _98537 _98534 _98536) = (term151 _98537 _98534 _98536).
Proof. exact (MK_COMB (@lem7655237) (@lem7655201 _98537 _98534 _98536)). Qed.
Lemma lem7655239 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) : (term680 _98537 _98534 _98536 _98535) = (term704 _98537 _98534 _98535 _98536).
Proof. exact (MK_COMB (@lem7655238 _98537 _98534 _98536) (@lem7655236 _98537 _98534 _98535 _98536)). Qed.
Lemma lem7655240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655241 (_98537 : int) : (term84 _98537) = (term153 _98537).
Proof. exact (MK_COMB (@lem7655240) (@lem7655148 _98537)). Qed.
Lemma lem7655242 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) : (term684 _98537 _98534 _98536 _98535) = (term705 _98537 _98534 _98535 _98536).
Proof. exact (MK_COMB (@lem7655241 _98537) (@lem7655239 _98537 _98534 _98535 _98536)). Qed.
Lemma lem7655243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655244 (_98536 : int) : (term84 _98536) = (term153 _98536).
Proof. exact (MK_COMB (@lem7655243) (@lem7655135 _98536)). Qed.
Lemma lem7655245 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) : (term688 _98537 _98534 _98536 _98535) = (term706 _98537 _98534 _98535 _98536).
Proof. exact (MK_COMB (@lem7655244 _98536) (@lem7655242 _98537 _98534 _98535 _98536)). Qed.
Lemma lem7655246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655247 (_98535 : int) : (term84 _98535) = (term153 _98535).
Proof. exact (MK_COMB (@lem7655246) (@lem7655122 _98535)). Qed.
Lemma lem7655248 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) : (term692 _98537 _98534 _98536 _98535) = (term707 _98537 _98534 _98535 _98536).
Proof. exact (MK_COMB (@lem7655247 _98535) (@lem7655245 _98537 _98534 _98535 _98536)). Qed.
Lemma lem7655249 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655250 (_98534 : int) : (term84 _98534) = (term153 _98534).
Proof. exact (MK_COMB (@lem7655249) (@lem7655109 _98534)). Qed.
Lemma lem7655251 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) : (term696 _98537 _98534 _98536 _98535) = (term708 _98537 _98534 _98535 _98536).
Proof. exact (MK_COMB (@lem7655250 _98534) (@lem7655248 _98537 _98534 _98535 _98536)). Qed.
Lemma lem7655252 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) : (term697 _98537 _98534 _98536 _98535) = (term708 _98537 _98534 _98535 _98536).
Proof. exact (TRANS (@lem7655096 _98537 _98534 _98536 _98535) (@lem7655251 _98537 _98534 _98535 _98536)). Qed.
Lemma lem7655256 (t : Prop) : (term157 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7655342 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) : (term709 _98537 _98534 _98535 _98536) = (term708 _98537 _98534 _98535 _98536).
Proof. exact (@lem7655256 (term708 _98537 _98534 _98535 _98536)). Qed.
Lemma lem7655343 (_98534 : int) : (term105 _98534) = (term159 _98534).
Proof. exact (@lem1988287 (real_of_int _98534) term102). Qed.
Lemma lem7655349 (_98534 : int) : (term160 _98534) = (term161 _98534).
Proof. exact (@lem1982792 (real_of_int _98534) term102). Qed.
Lemma lem7655351 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7655352 : term102 = term163.
Proof. exact (@lem7655351 (NUMERAL 0)). Qed.
Lemma lem7655354 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7655355 : term166 = term167.
Proof. exact (@lem7655354 term117). Qed.
Lemma lem7655356 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7655357 : term168 = term169.
Proof. exact (MK_COMB (@lem7655356) (@lem7655355)). Qed.
Lemma lem7655358 : term170 = term171.
Proof. exact (MK_COMB (@lem7655357) (@lem7655352)). Qed.
Lemma lem7655359 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7655361 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7655362 : term175 = term176.
Proof. exact (@lem7655361 term117 term117). Qed.
Lemma lem7655363 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7655364 : term178 = term117.
Proof. exact (EQ_MP (@lem7655363) (@lem940073)). Qed.
Lemma lem7655365 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7655366 : term176 = term116.
Proof. exact (MK_COMB (@lem7655365) (@lem7655364)). Qed.
Lemma lem7655367 : term175 = term116.
Proof. exact (TRANS (@lem7655362) (@lem7655366)). Qed.
Lemma lem7655369 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7655370 : term170 = term102.
Proof. exact (@lem7655369 term117). Qed.
Lemma lem7655371 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7655372 : term180 = term181.
Proof. exact (MK_COMB (@lem7655371) (@lem7655370)). Qed.
Lemma lem7655373 : term172 = term163.
Proof. exact (MK_COMB (@lem7655372) (@lem7655367)). Qed.
Lemma lem7655374 : term171 = term163.
Proof. exact (TRANS (@lem7655359) (@lem7655373)). Qed.
Lemma lem7655375 : term170 = term163.
Proof. exact (TRANS (@lem7655358) (@lem7655374)). Qed.
Lemma lem7655377 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7655378 : term163 = term102.
Proof. exact (@lem7655377 term102). Qed.
Lemma lem7655379 : term170 = term102.
Proof. exact (TRANS (@lem7655375) (@lem7655378)). Qed.
Lemma lem7655380 (_98534 : int) : (term118 _98534) = (term118 _98534).
Proof. exact (eq_refl (term118 _98534)). Qed.
Lemma lem7655381 (_98534 : int) : (term161 _98534) = (term183 _98534).
Proof. exact (MK_COMB (@lem7655380 _98534) (@lem7655379)). Qed.
Lemma lem7655382 (_98534 : int) : (term183 _98534) = (real_of_int _98534).
Proof. exact (@lem1982723 (real_of_int _98534)). Qed.
Lemma lem7655383 (_98534 : int) : (term161 _98534) = (real_of_int _98534).
Proof. exact (TRANS (@lem7655381 _98534) (@lem7655382 _98534)). Qed.
Lemma lem7655385 (_98534 : int) : (term160 _98534) = (real_of_int _98534).
Proof. exact (TRANS (@lem7655349 _98534) (@lem7655383 _98534)). Qed.
Lemma lem7655386 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7655387 (_98534 : int) : (term184 _98534) = (term185 _98534).
Proof. exact (MK_COMB (@lem7655386) (@lem7655385 _98534)). Qed.
Lemma lem7655388 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7655389 (_98534 : int) : (term159 _98534) = (term186 _98534).
Proof. exact (MK_COMB (@lem7655387 _98534) (@lem7655388)). Qed.
Lemma lem7655390 (_98534 : int) : (term105 _98534) = (term186 _98534).
Proof. exact (TRANS (@lem7655343 _98534) (@lem7655389 _98534)). Qed.
Lemma lem7655391 (_98535 : int) : (term105 _98535) = (term159 _98535).
Proof. exact (@lem1988287 (real_of_int _98535) term102). Qed.
Lemma lem7655397 (_98535 : int) : (term160 _98535) = (term161 _98535).
Proof. exact (@lem1982792 (real_of_int _98535) term102). Qed.
Lemma lem7655399 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7655400 : term102 = term163.
Proof. exact (@lem7655399 (NUMERAL 0)). Qed.
Lemma lem7655402 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7655403 : term166 = term167.
Proof. exact (@lem7655402 term117). Qed.
Lemma lem7655404 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7655405 : term168 = term169.
Proof. exact (MK_COMB (@lem7655404) (@lem7655403)). Qed.
Lemma lem7655406 : term170 = term171.
Proof. exact (MK_COMB (@lem7655405) (@lem7655400)). Qed.
Lemma lem7655407 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7655409 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7655410 : term175 = term176.
Proof. exact (@lem7655409 term117 term117). Qed.
Lemma lem7655411 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7655412 : term178 = term117.
Proof. exact (EQ_MP (@lem7655411) (@lem940073)). Qed.
Lemma lem7655413 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7655414 : term176 = term116.
Proof. exact (MK_COMB (@lem7655413) (@lem7655412)). Qed.
Lemma lem7655415 : term175 = term116.
Proof. exact (TRANS (@lem7655410) (@lem7655414)). Qed.
Lemma lem7655417 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7655418 : term170 = term102.
Proof. exact (@lem7655417 term117). Qed.
Lemma lem7655419 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7655420 : term180 = term181.
Proof. exact (MK_COMB (@lem7655419) (@lem7655418)). Qed.
Lemma lem7655421 : term172 = term163.
Proof. exact (MK_COMB (@lem7655420) (@lem7655415)). Qed.
Lemma lem7655422 : term171 = term163.
Proof. exact (TRANS (@lem7655407) (@lem7655421)). Qed.
Lemma lem7655423 : term170 = term163.
Proof. exact (TRANS (@lem7655406) (@lem7655422)). Qed.
Lemma lem7655425 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7655426 : term163 = term102.
Proof. exact (@lem7655425 term102). Qed.
Lemma lem7655427 : term170 = term102.
Proof. exact (TRANS (@lem7655423) (@lem7655426)). Qed.
Lemma lem7655428 (_98535 : int) : (term118 _98535) = (term118 _98535).
Proof. exact (eq_refl (term118 _98535)). Qed.
Lemma lem7655429 (_98535 : int) : (term161 _98535) = (term183 _98535).
Proof. exact (MK_COMB (@lem7655428 _98535) (@lem7655427)). Qed.
Lemma lem7655430 (_98535 : int) : (term183 _98535) = (real_of_int _98535).
Proof. exact (@lem1982723 (real_of_int _98535)). Qed.
Lemma lem7655431 (_98535 : int) : (term161 _98535) = (real_of_int _98535).
Proof. exact (TRANS (@lem7655429 _98535) (@lem7655430 _98535)). Qed.
Lemma lem7655433 (_98535 : int) : (term160 _98535) = (real_of_int _98535).
Proof. exact (TRANS (@lem7655397 _98535) (@lem7655431 _98535)). Qed.
Lemma lem7655434 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7655435 (_98535 : int) : (term184 _98535) = (term185 _98535).
Proof. exact (MK_COMB (@lem7655434) (@lem7655433 _98535)). Qed.
Lemma lem7655436 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7655437 (_98535 : int) : (term159 _98535) = (term186 _98535).
Proof. exact (MK_COMB (@lem7655435 _98535) (@lem7655436)). Qed.
Lemma lem7655438 (_98535 : int) : (term105 _98535) = (term186 _98535).
Proof. exact (TRANS (@lem7655391 _98535) (@lem7655437 _98535)). Qed.
Lemma lem7655439 (_98536 : int) : (term105 _98536) = (term159 _98536).
Proof. exact (@lem1988287 (real_of_int _98536) term102). Qed.
Lemma lem7655445 (_98536 : int) : (term160 _98536) = (term161 _98536).
Proof. exact (@lem1982792 (real_of_int _98536) term102). Qed.
Lemma lem7655447 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7655448 : term102 = term163.
Proof. exact (@lem7655447 (NUMERAL 0)). Qed.
Lemma lem7655450 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7655451 : term166 = term167.
Proof. exact (@lem7655450 term117). Qed.
Lemma lem7655452 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7655453 : term168 = term169.
Proof. exact (MK_COMB (@lem7655452) (@lem7655451)). Qed.
Lemma lem7655454 : term170 = term171.
Proof. exact (MK_COMB (@lem7655453) (@lem7655448)). Qed.
Lemma lem7655455 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7655457 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7655458 : term175 = term176.
Proof. exact (@lem7655457 term117 term117). Qed.
Lemma lem7655459 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7655460 : term178 = term117.
Proof. exact (EQ_MP (@lem7655459) (@lem940073)). Qed.
Lemma lem7655461 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7655462 : term176 = term116.
Proof. exact (MK_COMB (@lem7655461) (@lem7655460)). Qed.
Lemma lem7655463 : term175 = term116.
Proof. exact (TRANS (@lem7655458) (@lem7655462)). Qed.
Lemma lem7655465 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7655466 : term170 = term102.
Proof. exact (@lem7655465 term117). Qed.
Lemma lem7655467 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7655468 : term180 = term181.
Proof. exact (MK_COMB (@lem7655467) (@lem7655466)). Qed.
Lemma lem7655469 : term172 = term163.
Proof. exact (MK_COMB (@lem7655468) (@lem7655463)). Qed.
Lemma lem7655470 : term171 = term163.
Proof. exact (TRANS (@lem7655455) (@lem7655469)). Qed.
Lemma lem7655471 : term170 = term163.
Proof. exact (TRANS (@lem7655454) (@lem7655470)). Qed.
Lemma lem7655473 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7655474 : term163 = term102.
Proof. exact (@lem7655473 term102). Qed.
Lemma lem7655475 : term170 = term102.
Proof. exact (TRANS (@lem7655471) (@lem7655474)). Qed.
Lemma lem7655476 (_98536 : int) : (term118 _98536) = (term118 _98536).
Proof. exact (eq_refl (term118 _98536)). Qed.
Lemma lem7655477 (_98536 : int) : (term161 _98536) = (term183 _98536).
Proof. exact (MK_COMB (@lem7655476 _98536) (@lem7655475)). Qed.
Lemma lem7655478 (_98536 : int) : (term183 _98536) = (real_of_int _98536).
Proof. exact (@lem1982723 (real_of_int _98536)). Qed.
Lemma lem7655479 (_98536 : int) : (term161 _98536) = (real_of_int _98536).
Proof. exact (TRANS (@lem7655477 _98536) (@lem7655478 _98536)). Qed.
Lemma lem7655481 (_98536 : int) : (term160 _98536) = (real_of_int _98536).
Proof. exact (TRANS (@lem7655445 _98536) (@lem7655479 _98536)). Qed.
Lemma lem7655482 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7655483 (_98536 : int) : (term184 _98536) = (term185 _98536).
Proof. exact (MK_COMB (@lem7655482) (@lem7655481 _98536)). Qed.
Lemma lem7655484 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7655485 (_98536 : int) : (term159 _98536) = (term186 _98536).
Proof. exact (MK_COMB (@lem7655483 _98536) (@lem7655484)). Qed.
Lemma lem7655486 (_98536 : int) : (term105 _98536) = (term186 _98536).
Proof. exact (TRANS (@lem7655439 _98536) (@lem7655485 _98536)). Qed.
Lemma lem7655487 (_98537 : int) : (term105 _98537) = (term159 _98537).
Proof. exact (@lem1988287 (real_of_int _98537) term102). Qed.
Lemma lem7655493 (_98537 : int) : (term160 _98537) = (term161 _98537).
Proof. exact (@lem1982792 (real_of_int _98537) term102). Qed.
Lemma lem7655495 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7655496 : term102 = term163.
Proof. exact (@lem7655495 (NUMERAL 0)). Qed.
Lemma lem7655498 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7655499 : term166 = term167.
Proof. exact (@lem7655498 term117). Qed.
Lemma lem7655500 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7655501 : term168 = term169.
Proof. exact (MK_COMB (@lem7655500) (@lem7655499)). Qed.
Lemma lem7655502 : term170 = term171.
Proof. exact (MK_COMB (@lem7655501) (@lem7655496)). Qed.
Lemma lem7655503 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7655505 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7655506 : term175 = term176.
Proof. exact (@lem7655505 term117 term117). Qed.
Lemma lem7655507 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7655508 : term178 = term117.
Proof. exact (EQ_MP (@lem7655507) (@lem940073)). Qed.
Lemma lem7655509 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7655510 : term176 = term116.
Proof. exact (MK_COMB (@lem7655509) (@lem7655508)). Qed.
Lemma lem7655511 : term175 = term116.
Proof. exact (TRANS (@lem7655506) (@lem7655510)). Qed.
Lemma lem7655513 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7655514 : term170 = term102.
Proof. exact (@lem7655513 term117). Qed.
Lemma lem7655515 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7655516 : term180 = term181.
Proof. exact (MK_COMB (@lem7655515) (@lem7655514)). Qed.
Lemma lem7655517 : term172 = term163.
Proof. exact (MK_COMB (@lem7655516) (@lem7655511)). Qed.
Lemma lem7655518 : term171 = term163.
Proof. exact (TRANS (@lem7655503) (@lem7655517)). Qed.
Lemma lem7655519 : term170 = term163.
Proof. exact (TRANS (@lem7655502) (@lem7655518)). Qed.
Lemma lem7655521 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7655522 : term163 = term102.
Proof. exact (@lem7655521 term102). Qed.
Lemma lem7655523 : term170 = term102.
Proof. exact (TRANS (@lem7655519) (@lem7655522)). Qed.
Lemma lem7655524 (_98537 : int) : (term118 _98537) = (term118 _98537).
Proof. exact (eq_refl (term118 _98537)). Qed.
Lemma lem7655525 (_98537 : int) : (term161 _98537) = (term183 _98537).
Proof. exact (MK_COMB (@lem7655524 _98537) (@lem7655523)). Qed.
Lemma lem7655526 (_98537 : int) : (term183 _98537) = (real_of_int _98537).
Proof. exact (@lem1982723 (real_of_int _98537)). Qed.
Lemma lem7655527 (_98537 : int) : (term161 _98537) = (real_of_int _98537).
Proof. exact (TRANS (@lem7655525 _98537) (@lem7655526 _98537)). Qed.
Lemma lem7655529 (_98537 : int) : (term160 _98537) = (real_of_int _98537).
Proof. exact (TRANS (@lem7655493 _98537) (@lem7655527 _98537)). Qed.
Lemma lem7655530 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7655531 (_98537 : int) : (term184 _98537) = (term185 _98537).
Proof. exact (MK_COMB (@lem7655530) (@lem7655529 _98537)). Qed.
Lemma lem7655532 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7655533 (_98537 : int) : (term159 _98537) = (term186 _98537).
Proof. exact (MK_COMB (@lem7655531 _98537) (@lem7655532)). Qed.
Lemma lem7655534 (_98537 : int) : (term105 _98537) = (term186 _98537).
Proof. exact (TRANS (@lem7655487 _98537) (@lem7655533 _98537)). Qed.
Lemma lem7655535 (_98537 : int) (_98534 : int) (_98536 : int) : ((real_of_int _98537) = (term107 _98534 _98536)) = ((term187 _98537 _98534 _98536) = term102).
Proof. exact (@lem1988293 (real_of_int _98537) (term107 _98534 _98536)). Qed.
Lemma lem7655547 (_98537 : int) (_98534 : int) (_98536 : int) : (term187 _98537 _98534 _98536) = (term188 _98537 _98534 _98536).
Proof. exact (@lem1982792 (real_of_int _98537) (term107 _98534 _98536)). Qed.
Lemma lem7655554 (_98534 : int) (_98536 : int) : (term189 _98534 _98536) = (term190 _98534 _98536).
Proof. exact (@lem1982781 (real_of_int _98534) term166 (real_of_int _98536)). Qed.
Lemma lem7655555 (_98537 : int) : (term118 _98537) = (term118 _98537).
Proof. exact (eq_refl (term118 _98537)). Qed.
Lemma lem7655556 (_98537 : int) (_98534 : int) (_98536 : int) : (term188 _98537 _98534 _98536) = (term191 _98537 _98534 _98536).
Proof. exact (MK_COMB (@lem7655555 _98537) (@lem7655554 _98534 _98536)). Qed.
Lemma lem7655557 (_98534 : int) (_98537 : int) (_98536 : int) : (term191 _98537 _98534 _98536) = (term192 _98534 _98537 _98536).
Proof. exact (@lem1982757 (term193 _98534) (real_of_int _98537) (term193 _98536)). Qed.
Lemma lem7655558 (_98536 : int) (_98537 : int) : (term194 _98537 _98536) = (term195 _98536 _98537).
Proof. exact (@lem1982761 (term193 _98536) (real_of_int _98537)). Qed.
Lemma lem7655559 (_98534 : int) : (term196 _98534) = (term196 _98534).
Proof. exact (eq_refl (term196 _98534)). Qed.
Lemma lem7655560 (_98534 : int) (_98536 : int) (_98537 : int) : (term192 _98534 _98537 _98536) = (term197 _98534 _98536 _98537).
Proof. exact (MK_COMB (@lem7655559 _98534) (@lem7655558 _98536 _98537)). Qed.
Lemma lem7655561 (_98534 : int) (_98536 : int) (_98537 : int) : (term191 _98537 _98534 _98536) = (term197 _98534 _98536 _98537).
Proof. exact (TRANS (@lem7655557 _98534 _98537 _98536) (@lem7655560 _98534 _98536 _98537)). Qed.
Lemma lem7655562 (_98534 : int) (_98536 : int) (_98537 : int) : (term188 _98537 _98534 _98536) = (term197 _98534 _98536 _98537).
Proof. exact (TRANS (@lem7655556 _98537 _98534 _98536) (@lem7655561 _98534 _98536 _98537)). Qed.
Lemma lem7655564 (_98534 : int) (_98536 : int) (_98537 : int) : (term187 _98537 _98534 _98536) = (term197 _98534 _98536 _98537).
Proof. exact (TRANS (@lem7655547 _98537 _98534 _98536) (@lem7655562 _98534 _98536 _98537)). Qed.
Lemma lem7655565 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7655566 (_98534 : int) (_98536 : int) (_98537 : int) : (term198 _98537 _98534 _98536) = (term199 _98534 _98536 _98537).
Proof. exact (MK_COMB (@lem7655565) (@lem7655564 _98534 _98536 _98537)). Qed.
Lemma lem7655567 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7655568 (_98534 : int) (_98536 : int) (_98537 : int) : ((term187 _98537 _98534 _98536) = term102) = ((term197 _98534 _98536 _98537) = term102).
Proof. exact (MK_COMB (@lem7655566 _98534 _98536 _98537) (@lem7655567)). Qed.
Lemma lem7655569 (_98534 : int) (_98536 : int) (_98537 : int) : ((real_of_int _98537) = (term107 _98534 _98536)) = ((term197 _98534 _98536 _98537) = term102).
Proof. exact (TRANS (@lem7655535 _98537 _98534 _98536) (@lem7655568 _98534 _98536 _98537)). Qed.
Lemma lem7655570 (_98534 : int) (_98537 : int) : (term122 _98537 _98534) = (term200 _98534 _98537).
Proof. exact (@lem1988287 (real_of_int _98534) (term119 _98537)). Qed.
Lemma lem7655582 (_98534 : int) (_98537 : int) : (term201 _98534 _98537) = (term202 _98534 _98537).
Proof. exact (@lem1982792 (real_of_int _98534) (term119 _98537)). Qed.
Lemma lem7655583 (_98537 : int) : (term203 _98537) = (term204 _98537).
Proof. exact (@lem1982781 (real_of_int _98537) term166 term116). Qed.
Lemma lem7655585 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7655586 : term116 = term205.
Proof. exact (@lem7655585 term117). Qed.
Lemma lem7655588 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7655589 : term166 = term167.
Proof. exact (@lem7655588 term117). Qed.
Lemma lem7655590 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7655591 : term168 = term169.
Proof. exact (MK_COMB (@lem7655590) (@lem7655589)). Qed.
Lemma lem7655592 : term206 = term207.
Proof. exact (MK_COMB (@lem7655591) (@lem7655586)). Qed.
Lemma lem7655593 : term207 = term208.
Proof. exact (@lem1981613 term166 term116 term116 term116). Qed.
Lemma lem7655595 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7655596 : term175 = term176.
Proof. exact (@lem7655595 term117 term117). Qed.
Lemma lem7655597 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7655598 : term178 = term117.
Proof. exact (EQ_MP (@lem7655597) (@lem940073)). Qed.
Lemma lem7655599 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7655600 : term176 = term116.
Proof. exact (MK_COMB (@lem7655599) (@lem7655598)). Qed.
Lemma lem7655601 : term175 = term116.
Proof. exact (TRANS (@lem7655596) (@lem7655600)). Qed.
Lemma lem7655603 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7655604 : term206 = term211.
Proof. exact (@lem7655603 term117 term117). Qed.
Lemma lem7655605 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7655606 : term178 = term117.
Proof. exact (EQ_MP (@lem7655605) (@lem940073)). Qed.
Lemma lem7655607 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7655608 : term176 = term116.
Proof. exact (MK_COMB (@lem7655607) (@lem7655606)). Qed.
Lemma lem7655609 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7655610 : term211 = term166.
Proof. exact (MK_COMB (@lem7655609) (@lem7655608)). Qed.
Lemma lem7655611 : term206 = term166.
Proof. exact (TRANS (@lem7655604) (@lem7655610)). Qed.
Lemma lem7655612 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7655613 : term212 = term213.
Proof. exact (MK_COMB (@lem7655612) (@lem7655611)). Qed.
Lemma lem7655614 : term208 = term167.
Proof. exact (MK_COMB (@lem7655613) (@lem7655601)). Qed.
Lemma lem7655615 : term207 = term167.
Proof. exact (TRANS (@lem7655593) (@lem7655614)). Qed.
Lemma lem7655616 : term206 = term167.
Proof. exact (TRANS (@lem7655592) (@lem7655615)). Qed.
Lemma lem7655618 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7655619 : term167 = term166.
Proof. exact (@lem7655618 term166). Qed.
Lemma lem7655620 : term206 = term166.
Proof. exact (TRANS (@lem7655616) (@lem7655619)). Qed.
Lemma lem7655623 (_98537 : int) : (term196 _98537) = (term196 _98537).
Proof. exact (eq_refl (term196 _98537)). Qed.
Lemma lem7655624 (_98537 : int) : (term204 _98537) = (term214 _98537).
Proof. exact (MK_COMB (@lem7655623 _98537) (@lem7655620)). Qed.
Lemma lem7655625 (_98537 : int) : (term203 _98537) = (term214 _98537).
Proof. exact (TRANS (@lem7655583 _98537) (@lem7655624 _98537)). Qed.
Lemma lem7655626 (_98534 : int) : (term118 _98534) = (term118 _98534).
Proof. exact (eq_refl (term118 _98534)). Qed.
Lemma lem7655629 (_98534 : int) (_98537 : int) : (term202 _98534 _98537) = (term215 _98534 _98537).
Proof. exact (MK_COMB (@lem7655626 _98534) (@lem7655625 _98537)). Qed.
Lemma lem7655631 (_98534 : int) (_98537 : int) : (term201 _98534 _98537) = (term215 _98534 _98537).
Proof. exact (TRANS (@lem7655582 _98534 _98537) (@lem7655629 _98534 _98537)). Qed.
Lemma lem7655632 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7655633 (_98534 : int) (_98537 : int) : (term216 _98534 _98537) = (term217 _98534 _98537).
Proof. exact (MK_COMB (@lem7655632) (@lem7655631 _98534 _98537)). Qed.
Lemma lem7655634 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7655635 (_98534 : int) (_98537 : int) : (term200 _98534 _98537) = (term218 _98534 _98537).
Proof. exact (MK_COMB (@lem7655633 _98534 _98537) (@lem7655634)). Qed.
Lemma lem7655636 (_98534 : int) (_98537 : int) : (term122 _98537 _98534) = (term218 _98534 _98537).
Proof. exact (TRANS (@lem7655570 _98534 _98537) (@lem7655635 _98534 _98537)). Qed.
Lemma lem7655637 (_98536 : int) : ((real_of_int _98536) = term102) = ((term160 _98536) = term102).
Proof. exact (@lem1988293 (real_of_int _98536) term102). Qed.
Lemma lem7655643 (_98536 : int) : (term160 _98536) = (term161 _98536).
Proof. exact (@lem1982792 (real_of_int _98536) term102). Qed.
Lemma lem7655645 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7655646 : term102 = term163.
Proof. exact (@lem7655645 (NUMERAL 0)). Qed.
Lemma lem7655648 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7655649 : term166 = term167.
Proof. exact (@lem7655648 term117). Qed.
Lemma lem7655650 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7655651 : term168 = term169.
Proof. exact (MK_COMB (@lem7655650) (@lem7655649)). Qed.
Lemma lem7655652 : term170 = term171.
Proof. exact (MK_COMB (@lem7655651) (@lem7655646)). Qed.
Lemma lem7655653 : term171 = term172.
Proof. exact (@lem1981613 term166 term102 term116 term116). Qed.
Lemma lem7655655 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7655656 : term175 = term176.
Proof. exact (@lem7655655 term117 term117). Qed.
Lemma lem7655657 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7655658 : term178 = term117.
Proof. exact (EQ_MP (@lem7655657) (@lem940073)). Qed.
Lemma lem7655659 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7655660 : term176 = term116.
Proof. exact (MK_COMB (@lem7655659) (@lem7655658)). Qed.
Lemma lem7655661 : term175 = term116.
Proof. exact (TRANS (@lem7655656) (@lem7655660)). Qed.
Lemma lem7655663 (x : nat) : (term179 x) = term102.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7655664 : term170 = term102.
Proof. exact (@lem7655663 term117). Qed.
Lemma lem7655665 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7655666 : term180 = term181.
Proof. exact (MK_COMB (@lem7655665) (@lem7655664)). Qed.
Lemma lem7655667 : term172 = term163.
Proof. exact (MK_COMB (@lem7655666) (@lem7655661)). Qed.
Lemma lem7655668 : term171 = term163.
Proof. exact (TRANS (@lem7655653) (@lem7655667)). Qed.
Lemma lem7655669 : term170 = term163.
Proof. exact (TRANS (@lem7655652) (@lem7655668)). Qed.
Lemma lem7655671 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7655672 : term163 = term102.
Proof. exact (@lem7655671 term102). Qed.
Lemma lem7655673 : term170 = term102.
Proof. exact (TRANS (@lem7655669) (@lem7655672)). Qed.
Lemma lem7655674 (_98536 : int) : (term118 _98536) = (term118 _98536).
Proof. exact (eq_refl (term118 _98536)). Qed.
Lemma lem7655675 (_98536 : int) : (term161 _98536) = (term183 _98536).
Proof. exact (MK_COMB (@lem7655674 _98536) (@lem7655673)). Qed.
Lemma lem7655676 (_98536 : int) : (term183 _98536) = (real_of_int _98536).
Proof. exact (@lem1982723 (real_of_int _98536)). Qed.
Lemma lem7655677 (_98536 : int) : (term161 _98536) = (real_of_int _98536).
Proof. exact (TRANS (@lem7655675 _98536) (@lem7655676 _98536)). Qed.
Lemma lem7655679 (_98536 : int) : (term160 _98536) = (real_of_int _98536).
Proof. exact (TRANS (@lem7655643 _98536) (@lem7655677 _98536)). Qed.
Lemma lem7655680 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7655681 (_98536 : int) : (term219 _98536) = (term108 _98536).
Proof. exact (MK_COMB (@lem7655680) (@lem7655679 _98536)). Qed.
Lemma lem7655682 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7655683 (_98536 : int) : ((term160 _98536) = term102) = ((real_of_int _98536) = term102).
Proof. exact (MK_COMB (@lem7655681 _98536) (@lem7655682)). Qed.
Lemma lem7655684 (_98536 : int) : ((real_of_int _98536) = term102) = ((real_of_int _98536) = term102).
Proof. exact (TRANS (@lem7655637 _98536) (@lem7655683 _98536)). Qed.
Lemma lem7655685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655686 (_98534 : int) (_98537 : int) : (term123 _98537 _98534) = (term220 _98534 _98537).
Proof. exact (MK_COMB (@lem7655685) (@lem7655636 _98534 _98537)). Qed.
Lemma lem7655687 (_98534 : int) (_98537 : int) (_98536 : int) : (term124 _98537 _98534 _98536) = (term221 _98534 _98537 _98536).
Proof. exact (MK_COMB (@lem7655686 _98534 _98537) (@lem7655684 _98536)). Qed.
Lemma lem7655688 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7655689 (_98534 : int) (_98536 : int) (_98537 : int) : (term125 _98537 _98534 _98536) = (term222 _98534 _98536 _98537).
Proof. exact (MK_COMB (@lem7655688) (@lem7655569 _98534 _98536 _98537)). Qed.
Lemma lem7655690 (_98534 : int) (_98537 : int) (_98536 : int) : (term126 _98537 _98534 _98536) = (term223 _98534 _98537 _98536).
Proof. exact (MK_COMB (@lem7655689 _98534 _98536 _98537) (@lem7655687 _98534 _98537 _98536)). Qed.
Lemma lem7655691 (_98534 : int) (_98535 : int) (_98537 : int) : (term701 _98537 _98534 _98535) = (term710 _98534 _98535 _98537).
Proof. exact (@lem1988287 (term107 _98534 _98535) (real_of_int _98537)). Qed.
Lemma lem7655703 (_98534 : int) (_98535 : int) (_98537 : int) : (term711 _98534 _98535 _98537) = (term712 _98534 _98535 _98537).
Proof. exact (@lem1982792 (term107 _98534 _98535) (real_of_int _98537)). Qed.
Lemma lem7655712 (_98534 : int) (_98535 : int) (_98537 : int) : (term712 _98534 _98535 _98537) = (term352 _98534 _98535 _98537).
Proof. exact (@lem1982755 (real_of_int _98534) (real_of_int _98535) (term193 _98537)). Qed.
Lemma lem7655714 (_98534 : int) (_98535 : int) (_98537 : int) : (term711 _98534 _98535 _98537) = (term352 _98534 _98535 _98537).
Proof. exact (TRANS (@lem7655703 _98534 _98535 _98537) (@lem7655712 _98534 _98535 _98537)). Qed.
Lemma lem7655715 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7655716 (_98534 : int) (_98535 : int) (_98537 : int) : (term713 _98534 _98535 _98537) = (term714 _98534 _98535 _98537).
Proof. exact (MK_COMB (@lem7655715) (@lem7655714 _98534 _98535 _98537)). Qed.
Lemma lem7655717 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7655718 (_98534 : int) (_98535 : int) (_98537 : int) : (term710 _98534 _98535 _98537) = (term715 _98534 _98535 _98537).
Proof. exact (MK_COMB (@lem7655716 _98534 _98535 _98537) (@lem7655717)). Qed.
Lemma lem7655719 (_98534 : int) (_98535 : int) (_98537 : int) : (term701 _98537 _98534 _98535) = (term715 _98534 _98535 _98537).
Proof. exact (TRANS (@lem7655691 _98534 _98535 _98537) (@lem7655718 _98534 _98535 _98537)). Qed.
Lemma lem7655720 (_98536 : int) (_98535 : int) : (term122 _98535 _98536) = (term200 _98536 _98535).
Proof. exact (@lem1988287 (real_of_int _98536) (term119 _98535)). Qed.
Lemma lem7655732 (_98536 : int) (_98535 : int) : (term201 _98536 _98535) = (term202 _98536 _98535).
Proof. exact (@lem1982792 (real_of_int _98536) (term119 _98535)). Qed.
Lemma lem7655733 (_98535 : int) : (term203 _98535) = (term204 _98535).
Proof. exact (@lem1982781 (real_of_int _98535) term166 term116). Qed.
Lemma lem7655735 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7655736 : term116 = term205.
Proof. exact (@lem7655735 term117). Qed.
Lemma lem7655738 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7655739 : term166 = term167.
Proof. exact (@lem7655738 term117). Qed.
Lemma lem7655740 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7655741 : term168 = term169.
Proof. exact (MK_COMB (@lem7655740) (@lem7655739)). Qed.
Lemma lem7655742 : term206 = term207.
Proof. exact (MK_COMB (@lem7655741) (@lem7655736)). Qed.
Lemma lem7655743 : term207 = term208.
Proof. exact (@lem1981613 term166 term116 term116 term116). Qed.
Lemma lem7655745 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7655746 : term175 = term176.
Proof. exact (@lem7655745 term117 term117). Qed.
Lemma lem7655747 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7655748 : term178 = term117.
Proof. exact (EQ_MP (@lem7655747) (@lem940073)). Qed.
Lemma lem7655749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7655750 : term176 = term116.
Proof. exact (MK_COMB (@lem7655749) (@lem7655748)). Qed.
Lemma lem7655751 : term175 = term116.
Proof. exact (TRANS (@lem7655746) (@lem7655750)). Qed.
Lemma lem7655753 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7655754 : term206 = term211.
Proof. exact (@lem7655753 term117 term117). Qed.
Lemma lem7655755 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7655756 : term178 = term117.
Proof. exact (EQ_MP (@lem7655755) (@lem940073)). Qed.
Lemma lem7655757 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7655758 : term176 = term116.
Proof. exact (MK_COMB (@lem7655757) (@lem7655756)). Qed.
Lemma lem7655759 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7655760 : term211 = term166.
Proof. exact (MK_COMB (@lem7655759) (@lem7655758)). Qed.
Lemma lem7655761 : term206 = term166.
Proof. exact (TRANS (@lem7655754) (@lem7655760)). Qed.
Lemma lem7655762 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7655763 : term212 = term213.
Proof. exact (MK_COMB (@lem7655762) (@lem7655761)). Qed.
Lemma lem7655764 : term208 = term167.
Proof. exact (MK_COMB (@lem7655763) (@lem7655751)). Qed.
Lemma lem7655765 : term207 = term167.
Proof. exact (TRANS (@lem7655743) (@lem7655764)). Qed.
Lemma lem7655766 : term206 = term167.
Proof. exact (TRANS (@lem7655742) (@lem7655765)). Qed.
Lemma lem7655768 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7655769 : term167 = term166.
Proof. exact (@lem7655768 term166). Qed.
Lemma lem7655770 : term206 = term166.
Proof. exact (TRANS (@lem7655766) (@lem7655769)). Qed.
Lemma lem7655773 (_98535 : int) : (term196 _98535) = (term196 _98535).
Proof. exact (eq_refl (term196 _98535)). Qed.
Lemma lem7655774 (_98535 : int) : (term204 _98535) = (term214 _98535).
Proof. exact (MK_COMB (@lem7655773 _98535) (@lem7655770)). Qed.
Lemma lem7655775 (_98535 : int) : (term203 _98535) = (term214 _98535).
Proof. exact (TRANS (@lem7655733 _98535) (@lem7655774 _98535)). Qed.
Lemma lem7655776 (_98536 : int) : (term118 _98536) = (term118 _98536).
Proof. exact (eq_refl (term118 _98536)). Qed.
Lemma lem7655777 (_98536 : int) (_98535 : int) : (term202 _98536 _98535) = (term215 _98536 _98535).
Proof. exact (MK_COMB (@lem7655776 _98536) (@lem7655775 _98535)). Qed.
Lemma lem7655782 (_98535 : int) (_98536 : int) : (term215 _98536 _98535) = (term224 _98535 _98536).
Proof. exact (@lem1982757 (term193 _98535) (real_of_int _98536) term166). Qed.
Lemma lem7655783 (_98535 : int) (_98536 : int) : (term202 _98536 _98535) = (term224 _98535 _98536).
Proof. exact (TRANS (@lem7655777 _98536 _98535) (@lem7655782 _98535 _98536)). Qed.
Lemma lem7655785 (_98535 : int) (_98536 : int) : (term201 _98536 _98535) = (term224 _98535 _98536).
Proof. exact (TRANS (@lem7655732 _98536 _98535) (@lem7655783 _98535 _98536)). Qed.
Lemma lem7655786 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7655787 (_98535 : int) (_98536 : int) : (term216 _98536 _98535) = (term225 _98535 _98536).
Proof. exact (MK_COMB (@lem7655786) (@lem7655785 _98535 _98536)). Qed.
Lemma lem7655788 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7655789 (_98535 : int) (_98536 : int) : (term200 _98536 _98535) = (term226 _98535 _98536).
Proof. exact (MK_COMB (@lem7655787 _98535 _98536) (@lem7655788)). Qed.
Lemma lem7655790 (_98535 : int) (_98536 : int) : (term122 _98535 _98536) = (term226 _98535 _98536).
Proof. exact (TRANS (@lem7655720 _98536 _98535) (@lem7655789 _98535 _98536)). Qed.
Lemma lem7655791 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655792 (_98534 : int) (_98535 : int) (_98537 : int) : (term702 _98537 _98534 _98535) = (term716 _98534 _98535 _98537).
Proof. exact (MK_COMB (@lem7655791) (@lem7655719 _98534 _98535 _98537)). Qed.
Lemma lem7655793 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term703 _98537 _98534 _98535 _98536) = (term717 _98534 _98537 _98535 _98536).
Proof. exact (MK_COMB (@lem7655792 _98534 _98535 _98537) (@lem7655790 _98535 _98536)). Qed.
Lemma lem7655794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655795 (_98534 : int) (_98537 : int) (_98536 : int) : (term151 _98537 _98534 _98536) = (term254 _98534 _98537 _98536).
Proof. exact (MK_COMB (@lem7655794) (@lem7655690 _98534 _98537 _98536)). Qed.
Lemma lem7655796 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term704 _98537 _98534 _98535 _98536) = (term718 _98534 _98537 _98535 _98536).
Proof. exact (MK_COMB (@lem7655795 _98534 _98537 _98536) (@lem7655793 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655798 (_98537 : int) : (term153 _98537) = (term256 _98537).
Proof. exact (MK_COMB (@lem7655797) (@lem7655534 _98537)). Qed.
Lemma lem7655799 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term705 _98537 _98534 _98535 _98536) = (term719 _98534 _98537 _98535 _98536).
Proof. exact (MK_COMB (@lem7655798 _98537) (@lem7655796 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655801 (_98536 : int) : (term153 _98536) = (term256 _98536).
Proof. exact (MK_COMB (@lem7655800) (@lem7655486 _98536)). Qed.
Lemma lem7655802 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term706 _98537 _98534 _98535 _98536) = (term720 _98534 _98537 _98535 _98536).
Proof. exact (MK_COMB (@lem7655801 _98536) (@lem7655799 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655804 (_98535 : int) : (term153 _98535) = (term256 _98535).
Proof. exact (MK_COMB (@lem7655803) (@lem7655438 _98535)). Qed.
Lemma lem7655805 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term707 _98537 _98534 _98535 _98536) = (term721 _98534 _98537 _98535 _98536).
Proof. exact (MK_COMB (@lem7655804 _98535) (@lem7655802 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7655807 (_98534 : int) : (term153 _98534) = (term256 _98534).
Proof. exact (MK_COMB (@lem7655806) (@lem7655390 _98534)). Qed.
Lemma lem7655808 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term708 _98537 _98534 _98535 _98536) = (term722 _98534 _98537 _98535 _98536).
Proof. exact (MK_COMB (@lem7655807 _98534) (@lem7655805 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655815 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term709 _98537 _98534 _98535 _98536) = (term722 _98534 _98537 _98535 _98536).
Proof. exact (TRANS (@lem7655342 _98537 _98534 _98535 _98536) (@lem7655808 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655844 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term718 _98534 _98537 _98535 _98536) = (term723 _98534 _98537 _98535 _98536).
Proof. exact (@lem19367 ((term197 _98534 _98536 _98537) = term102) (term221 _98534 _98537 _98536) (term717 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655847 (_98537 : int) : (term256 _98537) = (term256 _98537).
Proof. exact (eq_refl (term256 _98537)). Qed.
Lemma lem7655848 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term719 _98534 _98537 _98535 _98536) = (term724 _98534 _98537 _98535 _98536).
Proof. exact (MK_COMB (@lem7655847 _98537) (@lem7655844 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655855 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term724 _98534 _98537 _98535 _98536) = (term725 _98534 _98537 _98535 _98536).
Proof. exact (@lem19158 (term726 _98534 _98537 _98535 _98536) (term186 _98537) (term727 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655856 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term719 _98534 _98537 _98535 _98536) = (term725 _98534 _98537 _98535 _98536).
Proof. exact (TRANS (@lem7655848 _98534 _98537 _98535 _98536) (@lem7655855 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655859 (_98536 : int) : (term256 _98536) = (term256 _98536).
Proof. exact (eq_refl (term256 _98536)). Qed.
Lemma lem7655860 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term720 _98534 _98537 _98535 _98536) = (term728 _98534 _98537 _98535 _98536).
Proof. exact (MK_COMB (@lem7655859 _98536) (@lem7655856 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655867 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term728 _98534 _98537 _98535 _98536) = (term729 _98534 _98537 _98535 _98536).
Proof. exact (@lem19158 (term730 _98534 _98537 _98535 _98536) (term186 _98536) (term731 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655868 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term720 _98534 _98537 _98535 _98536) = (term729 _98534 _98537 _98535 _98536).
Proof. exact (TRANS (@lem7655860 _98534 _98537 _98535 _98536) (@lem7655867 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655871 (_98535 : int) : (term256 _98535) = (term256 _98535).
Proof. exact (eq_refl (term256 _98535)). Qed.
Lemma lem7655872 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term721 _98534 _98537 _98535 _98536) = (term732 _98534 _98537 _98535 _98536).
Proof. exact (MK_COMB (@lem7655871 _98535) (@lem7655868 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655879 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term732 _98534 _98537 _98535 _98536) = (term733 _98534 _98537 _98535 _98536).
Proof. exact (@lem19158 (term734 _98534 _98537 _98535 _98536) (term186 _98535) (term735 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655880 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term721 _98534 _98537 _98535 _98536) = (term733 _98534 _98537 _98535 _98536).
Proof. exact (TRANS (@lem7655872 _98534 _98537 _98535 _98536) (@lem7655879 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655883 (_98534 : int) : (term256 _98534) = (term256 _98534).
Proof. exact (eq_refl (term256 _98534)). Qed.
Lemma lem7655884 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term722 _98534 _98537 _98535 _98536) = (term736 _98534 _98537 _98535 _98536).
Proof. exact (MK_COMB (@lem7655883 _98534) (@lem7655880 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655891 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term736 _98534 _98537 _98535 _98536) = (term737 _98534 _98537 _98535 _98536).
Proof. exact (@lem19158 (term738 _98534 _98537 _98535 _98536) (term186 _98534) (term739 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655892 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term722 _98534 _98537 _98535 _98536) = (term737 _98534 _98537 _98535 _98536).
Proof. exact (TRANS (@lem7655884 _98534 _98537 _98535 _98536) (@lem7655891 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655893 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term709 _98537 _98534 _98535 _98536) = (term737 _98534 _98537 _98535 _98536).
Proof. exact (TRANS (@lem7655815 _98534 _98537 _98535 _98536) (@lem7655892 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7655903 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term737 _98534 _98537 _98535 _98536) : term737 _98534 _98537 _98535 _98536.
Proof. exact (h1). Qed.
Lemma lem7655904 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term740 _98534 _98537 _98535 _98536.
Proof. exact (h1). Qed.
Lemma lem7655905 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term738 _98534 _98537 _98535 _98536.
Proof. exact (proj2 (@lem7655904 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7655907 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term734 _98534 _98537 _98535 _98536.
Proof. exact (proj2 (@lem7655905 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7655909 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term730 _98534 _98537 _98535 _98536.
Proof. exact (proj2 (@lem7655907 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7655911 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term726 _98534 _98537 _98535 _98536.
Proof. exact (proj2 (@lem7655909 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7655913 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term717 _98534 _98537 _98535 _98536.
Proof. exact (proj2 (@lem7655911 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7655914 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : (term197 _98534 _98536 _98537) = term102.
Proof. exact (proj1 (@lem7655911 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7655915 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term226 _98535 _98536.
Proof. exact (proj2 (@lem7655913 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7655916 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term715 _98534 _98535 _98537.
Proof. exact (proj1 (@lem7655913 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7655918 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7655919 : term312 = term313.
Proof. exact (@lem7655918 term102 term116). Qed.
Lemma lem7655921 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7655922 : term116 = term205.
Proof. exact (@lem7655921 term117). Qed.
Lemma lem7655924 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7655925 : term102 = term163.
Proof. exact (@lem7655924 (NUMERAL 0)). Qed.
Lemma lem7655926 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7655927 : term314 = term315.
Proof. exact (MK_COMB (@lem7655926) (@lem7655925)). Qed.
Lemma lem7655928 : term313 = term316.
Proof. exact (MK_COMB (@lem7655927) (@lem7655922)). Qed.
Lemma lem7655929 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7655931 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7655932 : term313 = term319.
Proof. exact (@lem7655931 (NUMERAL 0) term117). Qed.
Lemma lem7655933 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7655934 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7655935 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7655934 h1) (fun h1 : term319 = True => @lem7655933)). Qed.
Lemma lem7655936 : term319 = True.
Proof. exact (EQ_MP (@lem7655935) (@lem7655933)). Qed.
Lemma lem7655937 : term313 = True.
Proof. exact (TRANS (@lem7655932) (@lem7655936)). Qed.
Lemma lem7655938 : True = term313.
Proof. exact (SYM (@lem7655937)). Qed.
Lemma lem7655939 : term313.
Proof. exact (EQ_MP (@lem7655938) (@lem0)). Qed.
Lemma lem7655940 : term321.
Proof. exact (@lem7655929 (@lem7655939)). Qed.
Lemma lem7655942 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7655943 : term313 = term319.
Proof. exact (@lem7655942 (NUMERAL 0) term117). Qed.
Lemma lem7655944 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7655945 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7655946 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7655945 h1) (fun h1 : term319 = True => @lem7655944)). Qed.
Lemma lem7655947 : term319 = True.
Proof. exact (EQ_MP (@lem7655946) (@lem7655944)). Qed.
Lemma lem7655948 : term313 = True.
Proof. exact (TRANS (@lem7655943) (@lem7655947)). Qed.
Lemma lem7655949 : True = term313.
Proof. exact (SYM (@lem7655948)). Qed.
Lemma lem7655950 : term313.
Proof. exact (EQ_MP (@lem7655949) (@lem0)). Qed.
Lemma lem7655951 : term316 = term322.
Proof. exact (@lem7655940 (@lem7655950)). Qed.
Lemma lem7655953 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7655954 : term175 = term176.
Proof. exact (@lem7655953 term117 term117). Qed.
Lemma lem7655955 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7655956 : term178 = term117.
Proof. exact (EQ_MP (@lem7655955) (@lem940073)). Qed.
Lemma lem7655957 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7655958 : term176 = term116.
Proof. exact (MK_COMB (@lem7655957) (@lem7655956)). Qed.
Lemma lem7655959 : term175 = term116.
Proof. exact (TRANS (@lem7655954) (@lem7655958)). Qed.
Lemma lem7655961 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7655962 : term324 = term102.
Proof. exact (@lem7655961 term117). Qed.
Lemma lem7655963 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7655964 : term325 = term314.
Proof. exact (MK_COMB (@lem7655963) (@lem7655962)). Qed.
Lemma lem7655965 : term322 = term313.
Proof. exact (MK_COMB (@lem7655964) (@lem7655959)). Qed.
Lemma lem7655967 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7655968 : term313 = term319.
Proof. exact (@lem7655967 (NUMERAL 0) term117). Qed.
Lemma lem7655969 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7655970 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7655971 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7655970 h1) (fun h1 : term319 = True => @lem7655969)). Qed.
Lemma lem7655972 : term319 = True.
Proof. exact (EQ_MP (@lem7655971) (@lem7655969)). Qed.
Lemma lem7655973 : term313 = True.
Proof. exact (TRANS (@lem7655968) (@lem7655972)). Qed.
Lemma lem7655974 : term322 = True.
Proof. exact (TRANS (@lem7655965) (@lem7655973)). Qed.
Lemma lem7655975 : term316 = True.
Proof. exact (TRANS (@lem7655951) (@lem7655974)). Qed.
Lemma lem7655976 : term313 = True.
Proof. exact (TRANS (@lem7655928) (@lem7655975)). Qed.
Lemma lem7655977 : term312 = True.
Proof. exact (TRANS (@lem7655919) (@lem7655976)). Qed.
Lemma lem7655978 : True = term312.
Proof. exact (SYM (@lem7655977)). Qed.
Lemma lem7655979 : term312.
Proof. exact (EQ_MP (@lem7655978) (@lem0)). Qed.
Lemma lem7655980 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term418 _98535 _98536.
Proof. exact (conj (@lem7655979) (@lem7655915 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7655982 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7655983 (_98535 : int) (_98536 : int) : term419 _98535 _98536.
Proof. exact (@lem7655982 term116 (term224 _98535 _98536)). Qed.
Lemma lem7655984 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term420 _98535 _98536.
Proof. exact (@lem7655983 _98535 _98536 (@lem7655980 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7655985 (_98535 : int) (_98536 : int) : (term421 _98535 _98536) = (term224 _98535 _98536).
Proof. exact (@lem1982733 (term224 _98535 _98536)). Qed.
Lemma lem7655986 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7655987 (_98535 : int) (_98536 : int) : (term422 _98535 _98536) = (term225 _98535 _98536).
Proof. exact (MK_COMB (@lem7655986) (@lem7655985 _98535 _98536)). Qed.
Lemma lem7655988 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7655989 (_98535 : int) (_98536 : int) : (term420 _98535 _98536) = (term226 _98535 _98536).
Proof. exact (MK_COMB (@lem7655987 _98535 _98536) (@lem7655988)). Qed.
Lemma lem7655990 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term226 _98535 _98536.
Proof. exact (EQ_MP (@lem7655989 _98535 _98536) (@lem7655984 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7655992 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7655993 : term312 = term313.
Proof. exact (@lem7655992 term102 term116). Qed.
Lemma lem7655995 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7655996 : term116 = term205.
Proof. exact (@lem7655995 term117). Qed.
Lemma lem7655998 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7655999 : term102 = term163.
Proof. exact (@lem7655998 (NUMERAL 0)). Qed.
Lemma lem7656000 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7656001 : term314 = term315.
Proof. exact (MK_COMB (@lem7656000) (@lem7655999)). Qed.
Lemma lem7656002 : term313 = term316.
Proof. exact (MK_COMB (@lem7656001) (@lem7655996)). Qed.
Lemma lem7656003 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7656005 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656006 : term313 = term319.
Proof. exact (@lem7656005 (NUMERAL 0) term117). Qed.
Lemma lem7656007 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656008 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656009 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656008 h1) (fun h1 : term319 = True => @lem7656007)). Qed.
Lemma lem7656010 : term319 = True.
Proof. exact (EQ_MP (@lem7656009) (@lem7656007)). Qed.
Lemma lem7656011 : term313 = True.
Proof. exact (TRANS (@lem7656006) (@lem7656010)). Qed.
Lemma lem7656012 : True = term313.
Proof. exact (SYM (@lem7656011)). Qed.
Lemma lem7656013 : term313.
Proof. exact (EQ_MP (@lem7656012) (@lem0)). Qed.
Lemma lem7656014 : term321.
Proof. exact (@lem7656003 (@lem7656013)). Qed.
Lemma lem7656016 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656017 : term313 = term319.
Proof. exact (@lem7656016 (NUMERAL 0) term117). Qed.
Lemma lem7656018 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656019 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656020 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656019 h1) (fun h1 : term319 = True => @lem7656018)). Qed.
Lemma lem7656021 : term319 = True.
Proof. exact (EQ_MP (@lem7656020) (@lem7656018)). Qed.
Lemma lem7656022 : term313 = True.
Proof. exact (TRANS (@lem7656017) (@lem7656021)). Qed.
Lemma lem7656023 : True = term313.
Proof. exact (SYM (@lem7656022)). Qed.
Lemma lem7656024 : term313.
Proof. exact (EQ_MP (@lem7656023) (@lem0)). Qed.
Lemma lem7656025 : term316 = term322.
Proof. exact (@lem7656014 (@lem7656024)). Qed.
Lemma lem7656027 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656028 : term175 = term176.
Proof. exact (@lem7656027 term117 term117). Qed.
Lemma lem7656029 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656030 : term178 = term117.
Proof. exact (EQ_MP (@lem7656029) (@lem940073)). Qed.
Lemma lem7656031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656032 : term176 = term116.
Proof. exact (MK_COMB (@lem7656031) (@lem7656030)). Qed.
Lemma lem7656033 : term175 = term116.
Proof. exact (TRANS (@lem7656028) (@lem7656032)). Qed.
Lemma lem7656035 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656036 : term324 = term102.
Proof. exact (@lem7656035 term117). Qed.
Lemma lem7656037 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7656038 : term325 = term314.
Proof. exact (MK_COMB (@lem7656037) (@lem7656036)). Qed.
Lemma lem7656039 : term322 = term313.
Proof. exact (MK_COMB (@lem7656038) (@lem7656033)). Qed.
Lemma lem7656041 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656042 : term313 = term319.
Proof. exact (@lem7656041 (NUMERAL 0) term117). Qed.
Lemma lem7656043 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656044 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656045 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656044 h1) (fun h1 : term319 = True => @lem7656043)). Qed.
Lemma lem7656046 : term319 = True.
Proof. exact (EQ_MP (@lem7656045) (@lem7656043)). Qed.
Lemma lem7656047 : term313 = True.
Proof. exact (TRANS (@lem7656042) (@lem7656046)). Qed.
Lemma lem7656048 : term322 = True.
Proof. exact (TRANS (@lem7656039) (@lem7656047)). Qed.
Lemma lem7656049 : term316 = True.
Proof. exact (TRANS (@lem7656025) (@lem7656048)). Qed.
Lemma lem7656050 : term313 = True.
Proof. exact (TRANS (@lem7656002) (@lem7656049)). Qed.
Lemma lem7656051 : term312 = True.
Proof. exact (TRANS (@lem7655993) (@lem7656050)). Qed.
Lemma lem7656052 : True = term312.
Proof. exact (SYM (@lem7656051)). Qed.
Lemma lem7656053 : term312.
Proof. exact (EQ_MP (@lem7656052) (@lem0)). Qed.
Lemma lem7656054 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term741 _98534 _98535 _98537.
Proof. exact (conj (@lem7656053) (@lem7655916 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656056 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7656057 (_98534 : int) (_98535 : int) (_98537 : int) : term742 _98534 _98535 _98537.
Proof. exact (@lem7656056 term116 (term352 _98534 _98535 _98537)). Qed.
Lemma lem7656058 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term743 _98534 _98535 _98537.
Proof. exact (@lem7656057 _98534 _98535 _98537 (@lem7656054 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656059 (_98534 : int) (_98535 : int) (_98537 : int) : (term744 _98534 _98535 _98537) = (term352 _98534 _98535 _98537).
Proof. exact (@lem1982733 (term352 _98534 _98535 _98537)). Qed.
Lemma lem7656060 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7656061 (_98534 : int) (_98535 : int) (_98537 : int) : (term745 _98534 _98535 _98537) = (term714 _98534 _98535 _98537).
Proof. exact (MK_COMB (@lem7656060) (@lem7656059 _98534 _98535 _98537)). Qed.
Lemma lem7656062 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7656063 (_98534 : int) (_98535 : int) (_98537 : int) : (term743 _98534 _98535 _98537) = (term715 _98534 _98535 _98537).
Proof. exact (MK_COMB (@lem7656061 _98534 _98535 _98537) (@lem7656062)). Qed.
Lemma lem7656064 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term715 _98534 _98535 _98537.
Proof. exact (EQ_MP (@lem7656063 _98534 _98535 _98537) (@lem7656058 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656066 (y : real) : term332 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7656067 (_98534 : int) (_98536 : int) (_98537 : int) : term333 _98534 _98536 _98537.
Proof. exact (@lem7656066 (term197 _98534 _98536 _98537)). Qed.
Lemma lem7656068 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term334 _98534 _98536 _98537.
Proof. exact (@lem7656067 _98534 _98536 _98537 (@lem7655914 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656069 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term478 _98534 _98536 _98537.
Proof. exact (@lem7656068 _98534 _98537 _98535 _98536 h1 term116). Qed.
Lemma lem7656070 (_98534 : int) (_98536 : int) (_98537 : int) : (term478 _98534 _98536 _98537) = ((term479 _98534 _98536 _98537) = term102).
Proof. exact (eq_refl (term478 _98534 _98536 _98537)). Qed.
Lemma lem7656071 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : (term479 _98534 _98536 _98537) = term102.
Proof. exact (EQ_MP (@lem7656070 _98534 _98536 _98537) (@lem7656069 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656072 (_98534 : int) (_98536 : int) (_98537 : int) : (term479 _98534 _98536 _98537) = (term197 _98534 _98536 _98537).
Proof. exact (@lem1982733 (term197 _98534 _98536 _98537)). Qed.
Lemma lem7656073 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7656074 (_98534 : int) (_98536 : int) (_98537 : int) : (term480 _98534 _98536 _98537) = (term199 _98534 _98536 _98537).
Proof. exact (MK_COMB (@lem7656073) (@lem7656072 _98534 _98536 _98537)). Qed.
Lemma lem7656075 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7656076 (_98534 : int) (_98536 : int) (_98537 : int) : ((term479 _98534 _98536 _98537) = term102) = ((term197 _98534 _98536 _98537) = term102).
Proof. exact (MK_COMB (@lem7656074 _98534 _98536 _98537) (@lem7656075)). Qed.
Lemma lem7656077 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : (term197 _98534 _98536 _98537) = term102.
Proof. exact (EQ_MP (@lem7656076 _98534 _98536 _98537) (@lem7656071 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656078 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term746 _98536 _98534 _98535 _98537.
Proof. exact (conj (@lem7656077 _98534 _98537 _98535 _98536 h1) (@lem7656064 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656080 (x : real) (y : real) : term356 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem7656081 (_98536 : int) (_98534 : int) (_98535 : int) (_98537 : int) : term747 _98536 _98534 _98535 _98537.
Proof. exact (@lem7656080 (term197 _98534 _98536 _98537) (term352 _98534 _98535 _98537)). Qed.
Lemma lem7656082 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term748 _98536 _98534 _98535 _98537.
Proof. exact (@lem7656081 _98536 _98534 _98535 _98537 (@lem7656078 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656083 (_98534 : int) (_98536 : int) (_98535 : int) (_98537 : int) : (term749 _98536 _98534 _98535 _98537) = (term750 _98534 _98536 _98535 _98537).
Proof. exact (@lem1982753 (term193 _98534) (real_of_int _98534) (term195 _98536 _98537) (term194 _98535 _98537)). Qed.
Lemma lem7656084 (_98534 : int) : (term387 _98534) = (term362 _98534).
Proof. exact (@lem1982713 term166 (real_of_int _98534)). Qed.
Lemma lem7656086 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7656087 : term116 = term205.
Proof. exact (@lem7656086 term117). Qed.
Lemma lem7656089 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7656090 : term166 = term167.
Proof. exact (@lem7656089 term117). Qed.
Lemma lem7656091 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656092 : term363 = term364.
Proof. exact (MK_COMB (@lem7656091) (@lem7656090)). Qed.
Lemma lem7656093 : term365 = term366.
Proof. exact (MK_COMB (@lem7656092) (@lem7656087)). Qed.
Lemma lem7656094 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7656096 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656097 : term313 = term319.
Proof. exact (@lem7656096 (NUMERAL 0) term117). Qed.
Lemma lem7656098 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656099 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656100 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656099 h1) (fun h1 : term319 = True => @lem7656098)). Qed.
Lemma lem7656101 : term319 = True.
Proof. exact (EQ_MP (@lem7656100) (@lem7656098)). Qed.
Lemma lem7656102 : term313 = True.
Proof. exact (TRANS (@lem7656097) (@lem7656101)). Qed.
Lemma lem7656103 : True = term313.
Proof. exact (SYM (@lem7656102)). Qed.
Lemma lem7656104 : term313.
Proof. exact (EQ_MP (@lem7656103) (@lem0)). Qed.
Lemma lem7656105 : term368.
Proof. exact (@lem7656094 (@lem7656104)). Qed.
Lemma lem7656107 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656108 : term313 = term319.
Proof. exact (@lem7656107 (NUMERAL 0) term117). Qed.
Lemma lem7656109 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656110 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656111 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656110 h1) (fun h1 : term319 = True => @lem7656109)). Qed.
Lemma lem7656112 : term319 = True.
Proof. exact (EQ_MP (@lem7656111) (@lem7656109)). Qed.
Lemma lem7656113 : term313 = True.
Proof. exact (TRANS (@lem7656108) (@lem7656112)). Qed.
Lemma lem7656114 : True = term313.
Proof. exact (SYM (@lem7656113)). Qed.
Lemma lem7656115 : term313.
Proof. exact (EQ_MP (@lem7656114) (@lem0)). Qed.
Lemma lem7656116 : term369.
Proof. exact (@lem7656105 (@lem7656115)). Qed.
Lemma lem7656118 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656119 : term313 = term319.
Proof. exact (@lem7656118 (NUMERAL 0) term117). Qed.
Lemma lem7656120 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656121 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656122 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656121 h1) (fun h1 : term319 = True => @lem7656120)). Qed.
Lemma lem7656123 : term319 = True.
Proof. exact (EQ_MP (@lem7656122) (@lem7656120)). Qed.
Lemma lem7656124 : term313 = True.
Proof. exact (TRANS (@lem7656119) (@lem7656123)). Qed.
Lemma lem7656125 : True = term313.
Proof. exact (SYM (@lem7656124)). Qed.
Lemma lem7656126 : term313.
Proof. exact (EQ_MP (@lem7656125) (@lem0)). Qed.
Lemma lem7656127 : term370.
Proof. exact (@lem7656116 (@lem7656126)). Qed.
Lemma lem7656129 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656130 : term175 = term176.
Proof. exact (@lem7656129 term117 term117). Qed.
Lemma lem7656131 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656132 : term178 = term117.
Proof. exact (EQ_MP (@lem7656131) (@lem940073)). Qed.
Lemma lem7656133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656134 : term176 = term116.
Proof. exact (MK_COMB (@lem7656133) (@lem7656132)). Qed.
Lemma lem7656135 : term175 = term116.
Proof. exact (TRANS (@lem7656130) (@lem7656134)). Qed.
Lemma lem7656137 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7656138 : term206 = term211.
Proof. exact (@lem7656137 term117 term117). Qed.
Lemma lem7656139 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656140 : term178 = term117.
Proof. exact (EQ_MP (@lem7656139) (@lem940073)). Qed.
Lemma lem7656141 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656142 : term176 = term116.
Proof. exact (MK_COMB (@lem7656141) (@lem7656140)). Qed.
Lemma lem7656143 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7656144 : term211 = term166.
Proof. exact (MK_COMB (@lem7656143) (@lem7656142)). Qed.
Lemma lem7656145 : term206 = term166.
Proof. exact (TRANS (@lem7656138) (@lem7656144)). Qed.
Lemma lem7656146 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656147 : term371 = term363.
Proof. exact (MK_COMB (@lem7656146) (@lem7656145)). Qed.
Lemma lem7656148 : term372 = term365.
Proof. exact (MK_COMB (@lem7656147) (@lem7656135)). Qed.
Lemma lem7656150 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7656151 : term365 = term102.
Proof. exact (@lem7656150 term117). Qed.
Lemma lem7656152 : term372 = term102.
Proof. exact (TRANS (@lem7656148) (@lem7656151)). Qed.
Lemma lem7656153 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7656154 : term374 = term375.
Proof. exact (MK_COMB (@lem7656153) (@lem7656152)). Qed.
Lemma lem7656155 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7656156 : term376 = term324.
Proof. exact (MK_COMB (@lem7656154) (@lem7656155)). Qed.
Lemma lem7656158 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656159 : term324 = term102.
Proof. exact (@lem7656158 term117). Qed.
Lemma lem7656160 : term376 = term102.
Proof. exact (TRANS (@lem7656156) (@lem7656159)). Qed.
Lemma lem7656162 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656163 : term175 = term176.
Proof. exact (@lem7656162 term117 term117). Qed.
Lemma lem7656164 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656165 : term178 = term117.
Proof. exact (EQ_MP (@lem7656164) (@lem940073)). Qed.
Lemma lem7656166 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656167 : term176 = term116.
Proof. exact (MK_COMB (@lem7656166) (@lem7656165)). Qed.
Lemma lem7656168 : term175 = term116.
Proof. exact (TRANS (@lem7656163) (@lem7656167)). Qed.
Lemma lem7656169 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7656170 : term377 = term324.
Proof. exact (MK_COMB (@lem7656169) (@lem7656168)). Qed.
Lemma lem7656172 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656173 : term324 = term102.
Proof. exact (@lem7656172 term117). Qed.
Lemma lem7656174 : term377 = term102.
Proof. exact (TRANS (@lem7656170) (@lem7656173)). Qed.
Lemma lem7656175 : term102 = term377.
Proof. exact (SYM (@lem7656174)). Qed.
Lemma lem7656176 : term376 = term377.
Proof. exact (TRANS (@lem7656160) (@lem7656175)). Qed.
Lemma lem7656177 : term366 = term163.
Proof. exact (@lem7656127 (@lem7656176)). Qed.
Lemma lem7656178 : term365 = term163.
Proof. exact (TRANS (@lem7656093) (@lem7656177)). Qed.
Lemma lem7656180 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7656181 : term163 = term102.
Proof. exact (@lem7656180 term102). Qed.
Lemma lem7656182 : term365 = term102.
Proof. exact (TRANS (@lem7656178) (@lem7656181)). Qed.
Lemma lem7656183 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7656184 : term378 = term375.
Proof. exact (MK_COMB (@lem7656183) (@lem7656182)). Qed.
Lemma lem7656185 (_98534 : int) : (real_of_int _98534) = (real_of_int _98534).
Proof. exact (eq_refl (real_of_int _98534)). Qed.
Lemma lem7656186 (_98534 : int) : (term362 _98534) = (term379 _98534).
Proof. exact (MK_COMB (@lem7656184) (@lem7656185 _98534)). Qed.
Lemma lem7656187 (_98534 : int) : (term387 _98534) = (term379 _98534).
Proof. exact (TRANS (@lem7656084 _98534) (@lem7656186 _98534)). Qed.
Lemma lem7656188 (_98534 : int) : (term379 _98534) = term102.
Proof. exact (@lem1982719 (real_of_int _98534)). Qed.
Lemma lem7656189 (_98534 : int) : (term387 _98534) = term102.
Proof. exact (TRANS (@lem7656187 _98534) (@lem7656188 _98534)). Qed.
Lemma lem7656190 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656191 (_98534 : int) : (term388 _98534) = term381.
Proof. exact (MK_COMB (@lem7656190) (@lem7656189 _98534)). Qed.
Lemma lem7656192 (_98535 : int) (_98536 : int) (_98537 : int) : (term751 _98536 _98535 _98537) = (term752 _98535 _98536 _98537).
Proof. exact (@lem1982757 (real_of_int _98535) (term195 _98536 _98537) (term193 _98537)). Qed.
Lemma lem7656193 (_98536 : int) (_98537 : int) : (term753 _98536 _98537) = (term754 _98536 _98537).
Proof. exact (@lem1982755 (term193 _98536) (real_of_int _98537) (term193 _98537)). Qed.
Lemma lem7656194 (_98537 : int) : (term361 _98537) = (term362 _98537).
Proof. exact (@lem1982715 term166 (real_of_int _98537)). Qed.
Lemma lem7656196 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7656197 : term116 = term205.
Proof. exact (@lem7656196 term117). Qed.
Lemma lem7656199 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7656200 : term166 = term167.
Proof. exact (@lem7656199 term117). Qed.
Lemma lem7656201 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656202 : term363 = term364.
Proof. exact (MK_COMB (@lem7656201) (@lem7656200)). Qed.
Lemma lem7656203 : term365 = term366.
Proof. exact (MK_COMB (@lem7656202) (@lem7656197)). Qed.
Lemma lem7656204 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7656206 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656207 : term313 = term319.
Proof. exact (@lem7656206 (NUMERAL 0) term117). Qed.
Lemma lem7656208 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656209 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656210 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656209 h1) (fun h1 : term319 = True => @lem7656208)). Qed.
Lemma lem7656211 : term319 = True.
Proof. exact (EQ_MP (@lem7656210) (@lem7656208)). Qed.
Lemma lem7656212 : term313 = True.
Proof. exact (TRANS (@lem7656207) (@lem7656211)). Qed.
Lemma lem7656213 : True = term313.
Proof. exact (SYM (@lem7656212)). Qed.
Lemma lem7656214 : term313.
Proof. exact (EQ_MP (@lem7656213) (@lem0)). Qed.
Lemma lem7656215 : term368.
Proof. exact (@lem7656204 (@lem7656214)). Qed.
Lemma lem7656217 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656218 : term313 = term319.
Proof. exact (@lem7656217 (NUMERAL 0) term117). Qed.
Lemma lem7656219 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656220 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656221 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656220 h1) (fun h1 : term319 = True => @lem7656219)). Qed.
Lemma lem7656222 : term319 = True.
Proof. exact (EQ_MP (@lem7656221) (@lem7656219)). Qed.
Lemma lem7656223 : term313 = True.
Proof. exact (TRANS (@lem7656218) (@lem7656222)). Qed.
Lemma lem7656224 : True = term313.
Proof. exact (SYM (@lem7656223)). Qed.
Lemma lem7656225 : term313.
Proof. exact (EQ_MP (@lem7656224) (@lem0)). Qed.
Lemma lem7656226 : term369.
Proof. exact (@lem7656215 (@lem7656225)). Qed.
Lemma lem7656228 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656229 : term313 = term319.
Proof. exact (@lem7656228 (NUMERAL 0) term117). Qed.
Lemma lem7656230 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656231 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656232 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656231 h1) (fun h1 : term319 = True => @lem7656230)). Qed.
Lemma lem7656233 : term319 = True.
Proof. exact (EQ_MP (@lem7656232) (@lem7656230)). Qed.
Lemma lem7656234 : term313 = True.
Proof. exact (TRANS (@lem7656229) (@lem7656233)). Qed.
Lemma lem7656235 : True = term313.
Proof. exact (SYM (@lem7656234)). Qed.
Lemma lem7656236 : term313.
Proof. exact (EQ_MP (@lem7656235) (@lem0)). Qed.
Lemma lem7656237 : term370.
Proof. exact (@lem7656226 (@lem7656236)). Qed.
Lemma lem7656239 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656240 : term175 = term176.
Proof. exact (@lem7656239 term117 term117). Qed.
Lemma lem7656241 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656242 : term178 = term117.
Proof. exact (EQ_MP (@lem7656241) (@lem940073)). Qed.
Lemma lem7656243 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656244 : term176 = term116.
Proof. exact (MK_COMB (@lem7656243) (@lem7656242)). Qed.
Lemma lem7656245 : term175 = term116.
Proof. exact (TRANS (@lem7656240) (@lem7656244)). Qed.
Lemma lem7656247 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7656248 : term206 = term211.
Proof. exact (@lem7656247 term117 term117). Qed.
Lemma lem7656249 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656250 : term178 = term117.
Proof. exact (EQ_MP (@lem7656249) (@lem940073)). Qed.
Lemma lem7656251 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656252 : term176 = term116.
Proof. exact (MK_COMB (@lem7656251) (@lem7656250)). Qed.
Lemma lem7656253 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7656254 : term211 = term166.
Proof. exact (MK_COMB (@lem7656253) (@lem7656252)). Qed.
Lemma lem7656255 : term206 = term166.
Proof. exact (TRANS (@lem7656248) (@lem7656254)). Qed.
Lemma lem7656256 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656257 : term371 = term363.
Proof. exact (MK_COMB (@lem7656256) (@lem7656255)). Qed.
Lemma lem7656258 : term372 = term365.
Proof. exact (MK_COMB (@lem7656257) (@lem7656245)). Qed.
Lemma lem7656260 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7656261 : term365 = term102.
Proof. exact (@lem7656260 term117). Qed.
Lemma lem7656262 : term372 = term102.
Proof. exact (TRANS (@lem7656258) (@lem7656261)). Qed.
Lemma lem7656263 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7656264 : term374 = term375.
Proof. exact (MK_COMB (@lem7656263) (@lem7656262)). Qed.
Lemma lem7656265 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7656266 : term376 = term324.
Proof. exact (MK_COMB (@lem7656264) (@lem7656265)). Qed.
Lemma lem7656268 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656269 : term324 = term102.
Proof. exact (@lem7656268 term117). Qed.
Lemma lem7656270 : term376 = term102.
Proof. exact (TRANS (@lem7656266) (@lem7656269)). Qed.
Lemma lem7656272 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656273 : term175 = term176.
Proof. exact (@lem7656272 term117 term117). Qed.
Lemma lem7656274 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656275 : term178 = term117.
Proof. exact (EQ_MP (@lem7656274) (@lem940073)). Qed.
Lemma lem7656276 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656277 : term176 = term116.
Proof. exact (MK_COMB (@lem7656276) (@lem7656275)). Qed.
Lemma lem7656278 : term175 = term116.
Proof. exact (TRANS (@lem7656273) (@lem7656277)). Qed.
Lemma lem7656279 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7656280 : term377 = term324.
Proof. exact (MK_COMB (@lem7656279) (@lem7656278)). Qed.
Lemma lem7656282 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656283 : term324 = term102.
Proof. exact (@lem7656282 term117). Qed.
Lemma lem7656284 : term377 = term102.
Proof. exact (TRANS (@lem7656280) (@lem7656283)). Qed.
Lemma lem7656285 : term102 = term377.
Proof. exact (SYM (@lem7656284)). Qed.
Lemma lem7656286 : term376 = term377.
Proof. exact (TRANS (@lem7656270) (@lem7656285)). Qed.
Lemma lem7656287 : term366 = term163.
Proof. exact (@lem7656237 (@lem7656286)). Qed.
Lemma lem7656288 : term365 = term163.
Proof. exact (TRANS (@lem7656203) (@lem7656287)). Qed.
Lemma lem7656290 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7656291 : term163 = term102.
Proof. exact (@lem7656290 term102). Qed.
Lemma lem7656292 : term365 = term102.
Proof. exact (TRANS (@lem7656288) (@lem7656291)). Qed.
Lemma lem7656293 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7656294 : term378 = term375.
Proof. exact (MK_COMB (@lem7656293) (@lem7656292)). Qed.
Lemma lem7656295 (_98537 : int) : (real_of_int _98537) = (real_of_int _98537).
Proof. exact (eq_refl (real_of_int _98537)). Qed.
Lemma lem7656296 (_98537 : int) : (term362 _98537) = (term379 _98537).
Proof. exact (MK_COMB (@lem7656294) (@lem7656295 _98537)). Qed.
Lemma lem7656297 (_98537 : int) : (term361 _98537) = (term379 _98537).
Proof. exact (TRANS (@lem7656194 _98537) (@lem7656296 _98537)). Qed.
Lemma lem7656298 (_98537 : int) : (term379 _98537) = term102.
Proof. exact (@lem1982719 (real_of_int _98537)). Qed.
Lemma lem7656299 (_98537 : int) : (term361 _98537) = term102.
Proof. exact (TRANS (@lem7656297 _98537) (@lem7656298 _98537)). Qed.
Lemma lem7656300 (_98536 : int) : (term196 _98536) = (term196 _98536).
Proof. exact (eq_refl (term196 _98536)). Qed.
Lemma lem7656301 (_98537 : int) (_98536 : int) : (term754 _98536 _98537) = (term587 _98536).
Proof. exact (MK_COMB (@lem7656300 _98536) (@lem7656299 _98537)). Qed.
Lemma lem7656302 (_98537 : int) (_98536 : int) : (term753 _98536 _98537) = (term587 _98536).
Proof. exact (TRANS (@lem7656193 _98536 _98537) (@lem7656301 _98537 _98536)). Qed.
Lemma lem7656303 (_98536 : int) : (term587 _98536) = (term193 _98536).
Proof. exact (@lem1982723 (term193 _98536)). Qed.
Lemma lem7656304 (_98537 : int) (_98536 : int) : (term753 _98536 _98537) = (term193 _98536).
Proof. exact (TRANS (@lem7656302 _98537 _98536) (@lem7656303 _98536)). Qed.
Lemma lem7656305 (_98535 : int) : (term118 _98535) = (term118 _98535).
Proof. exact (eq_refl (term118 _98535)). Qed.
Lemma lem7656306 (_98537 : int) (_98535 : int) (_98536 : int) : (term752 _98535 _98536 _98537) = (term194 _98535 _98536).
Proof. exact (MK_COMB (@lem7656305 _98535) (@lem7656304 _98537 _98536)). Qed.
Lemma lem7656307 (_98537 : int) (_98535 : int) (_98536 : int) : (term751 _98536 _98535 _98537) = (term194 _98535 _98536).
Proof. exact (TRANS (@lem7656192 _98535 _98536 _98537) (@lem7656306 _98537 _98535 _98536)). Qed.
Lemma lem7656308 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term750 _98534 _98536 _98535 _98537) = (term755 _98535 _98536).
Proof. exact (MK_COMB (@lem7656191 _98534) (@lem7656307 _98537 _98535 _98536)). Qed.
Lemma lem7656309 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term749 _98536 _98534 _98535 _98537) = (term755 _98535 _98536).
Proof. exact (TRANS (@lem7656083 _98534 _98536 _98535 _98537) (@lem7656308 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7656310 (_98535 : int) (_98536 : int) : (term755 _98535 _98536) = (term194 _98535 _98536).
Proof. exact (@lem1982721 (term194 _98535 _98536)). Qed.
Lemma lem7656311 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term749 _98536 _98534 _98535 _98537) = (term194 _98535 _98536).
Proof. exact (TRANS (@lem7656309 _98534 _98537 _98535 _98536) (@lem7656310 _98535 _98536)). Qed.
Lemma lem7656312 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7656313 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term756 _98536 _98534 _98535 _98537) = (term624 _98535 _98536).
Proof. exact (MK_COMB (@lem7656312) (@lem7656311 _98534 _98537 _98535 _98536)). Qed.
Lemma lem7656314 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7656315 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) : (term748 _98536 _98534 _98535 _98537) = (term625 _98535 _98536).
Proof. exact (MK_COMB (@lem7656313 _98534 _98537 _98535 _98536) (@lem7656314)). Qed.
Lemma lem7656316 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term625 _98535 _98536.
Proof. exact (EQ_MP (@lem7656315 _98534 _98537 _98535 _98536) (@lem7656082 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656318 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7656319 : term312 = term313.
Proof. exact (@lem7656318 term102 term116). Qed.
Lemma lem7656321 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7656322 : term116 = term205.
Proof. exact (@lem7656321 term117). Qed.
Lemma lem7656324 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7656325 : term102 = term163.
Proof. exact (@lem7656324 (NUMERAL 0)). Qed.
Lemma lem7656326 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7656327 : term314 = term315.
Proof. exact (MK_COMB (@lem7656326) (@lem7656325)). Qed.
Lemma lem7656328 : term313 = term316.
Proof. exact (MK_COMB (@lem7656327) (@lem7656322)). Qed.
Lemma lem7656329 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7656331 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656332 : term313 = term319.
Proof. exact (@lem7656331 (NUMERAL 0) term117). Qed.
Lemma lem7656333 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656334 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656335 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656334 h1) (fun h1 : term319 = True => @lem7656333)). Qed.
Lemma lem7656336 : term319 = True.
Proof. exact (EQ_MP (@lem7656335) (@lem7656333)). Qed.
Lemma lem7656337 : term313 = True.
Proof. exact (TRANS (@lem7656332) (@lem7656336)). Qed.
Lemma lem7656338 : True = term313.
Proof. exact (SYM (@lem7656337)). Qed.
Lemma lem7656339 : term313.
Proof. exact (EQ_MP (@lem7656338) (@lem0)). Qed.
Lemma lem7656340 : term321.
Proof. exact (@lem7656329 (@lem7656339)). Qed.
Lemma lem7656342 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656343 : term313 = term319.
Proof. exact (@lem7656342 (NUMERAL 0) term117). Qed.
Lemma lem7656344 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656345 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656346 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656345 h1) (fun h1 : term319 = True => @lem7656344)). Qed.
Lemma lem7656347 : term319 = True.
Proof. exact (EQ_MP (@lem7656346) (@lem7656344)). Qed.
Lemma lem7656348 : term313 = True.
Proof. exact (TRANS (@lem7656343) (@lem7656347)). Qed.
Lemma lem7656349 : True = term313.
Proof. exact (SYM (@lem7656348)). Qed.
Lemma lem7656350 : term313.
Proof. exact (EQ_MP (@lem7656349) (@lem0)). Qed.
Lemma lem7656351 : term316 = term322.
Proof. exact (@lem7656340 (@lem7656350)). Qed.
Lemma lem7656353 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656354 : term175 = term176.
Proof. exact (@lem7656353 term117 term117). Qed.
Lemma lem7656355 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656356 : term178 = term117.
Proof. exact (EQ_MP (@lem7656355) (@lem940073)). Qed.
Lemma lem7656357 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656358 : term176 = term116.
Proof. exact (MK_COMB (@lem7656357) (@lem7656356)). Qed.
Lemma lem7656359 : term175 = term116.
Proof. exact (TRANS (@lem7656354) (@lem7656358)). Qed.
Lemma lem7656361 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656362 : term324 = term102.
Proof. exact (@lem7656361 term117). Qed.
Lemma lem7656363 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7656364 : term325 = term314.
Proof. exact (MK_COMB (@lem7656363) (@lem7656362)). Qed.
Lemma lem7656365 : term322 = term313.
Proof. exact (MK_COMB (@lem7656364) (@lem7656359)). Qed.
Lemma lem7656367 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656368 : term313 = term319.
Proof. exact (@lem7656367 (NUMERAL 0) term117). Qed.
Lemma lem7656369 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656370 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656371 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656370 h1) (fun h1 : term319 = True => @lem7656369)). Qed.
Lemma lem7656372 : term319 = True.
Proof. exact (EQ_MP (@lem7656371) (@lem7656369)). Qed.
Lemma lem7656373 : term313 = True.
Proof. exact (TRANS (@lem7656368) (@lem7656372)). Qed.
Lemma lem7656374 : term322 = True.
Proof. exact (TRANS (@lem7656365) (@lem7656373)). Qed.
Lemma lem7656375 : term316 = True.
Proof. exact (TRANS (@lem7656351) (@lem7656374)). Qed.
Lemma lem7656376 : term313 = True.
Proof. exact (TRANS (@lem7656328) (@lem7656375)). Qed.
Lemma lem7656377 : term312 = True.
Proof. exact (TRANS (@lem7656319) (@lem7656376)). Qed.
Lemma lem7656378 : True = term312.
Proof. exact (SYM (@lem7656377)). Qed.
Lemma lem7656379 : term312.
Proof. exact (EQ_MP (@lem7656378) (@lem0)). Qed.
Lemma lem7656380 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term626 _98535 _98536.
Proof. exact (conj (@lem7656379) (@lem7656316 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656382 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7656383 (_98535 : int) (_98536 : int) : term627 _98535 _98536.
Proof. exact (@lem7656382 term116 (term194 _98535 _98536)). Qed.
Lemma lem7656384 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term628 _98535 _98536.
Proof. exact (@lem7656383 _98535 _98536 (@lem7656380 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656385 (_98535 : int) (_98536 : int) : (term629 _98535 _98536) = (term194 _98535 _98536).
Proof. exact (@lem1982733 (term194 _98535 _98536)). Qed.
Lemma lem7656386 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7656387 (_98535 : int) (_98536 : int) : (term630 _98535 _98536) = (term624 _98535 _98536).
Proof. exact (MK_COMB (@lem7656386) (@lem7656385 _98535 _98536)). Qed.
Lemma lem7656388 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7656389 (_98535 : int) (_98536 : int) : (term628 _98535 _98536) = (term625 _98535 _98536).
Proof. exact (MK_COMB (@lem7656387 _98535 _98536) (@lem7656388)). Qed.
Lemma lem7656390 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term625 _98535 _98536.
Proof. exact (EQ_MP (@lem7656389 _98535 _98536) (@lem7656384 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656391 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term631 _98535 _98536.
Proof. exact (conj (@lem7656390 _98534 _98537 _98535 _98536 h1) (@lem7655990 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656393 (x : real) (y : real) : term429 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7656394 (_98535 : int) (_98536 : int) : term632 _98535 _98536.
Proof. exact (@lem7656393 (term194 _98535 _98536) (term224 _98535 _98536)). Qed.
Lemma lem7656395 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term633 _98535 _98536.
Proof. exact (@lem7656394 _98535 _98536 (@lem7656391 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656396 (_98535 : int) (_98536 : int) : (term382 _98535 _98536) = (term383 _98535 _98536).
Proof. exact (@lem1982753 (real_of_int _98535) (term193 _98535) (term193 _98536) (term384 _98536)). Qed.
Lemma lem7656397 (_98535 : int) : (term361 _98535) = (term362 _98535).
Proof. exact (@lem1982715 term166 (real_of_int _98535)). Qed.
Lemma lem7656399 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7656400 : term116 = term205.
Proof. exact (@lem7656399 term117). Qed.
Lemma lem7656402 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7656403 : term166 = term167.
Proof. exact (@lem7656402 term117). Qed.
Lemma lem7656404 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656405 : term363 = term364.
Proof. exact (MK_COMB (@lem7656404) (@lem7656403)). Qed.
Lemma lem7656406 : term365 = term366.
Proof. exact (MK_COMB (@lem7656405) (@lem7656400)). Qed.
Lemma lem7656407 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7656409 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656410 : term313 = term319.
Proof. exact (@lem7656409 (NUMERAL 0) term117). Qed.
Lemma lem7656411 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656412 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656413 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656412 h1) (fun h1 : term319 = True => @lem7656411)). Qed.
Lemma lem7656414 : term319 = True.
Proof. exact (EQ_MP (@lem7656413) (@lem7656411)). Qed.
Lemma lem7656415 : term313 = True.
Proof. exact (TRANS (@lem7656410) (@lem7656414)). Qed.
Lemma lem7656416 : True = term313.
Proof. exact (SYM (@lem7656415)). Qed.
Lemma lem7656417 : term313.
Proof. exact (EQ_MP (@lem7656416) (@lem0)). Qed.
Lemma lem7656418 : term368.
Proof. exact (@lem7656407 (@lem7656417)). Qed.
Lemma lem7656420 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656421 : term313 = term319.
Proof. exact (@lem7656420 (NUMERAL 0) term117). Qed.
Lemma lem7656422 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656423 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656424 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656423 h1) (fun h1 : term319 = True => @lem7656422)). Qed.
Lemma lem7656425 : term319 = True.
Proof. exact (EQ_MP (@lem7656424) (@lem7656422)). Qed.
Lemma lem7656426 : term313 = True.
Proof. exact (TRANS (@lem7656421) (@lem7656425)). Qed.
Lemma lem7656427 : True = term313.
Proof. exact (SYM (@lem7656426)). Qed.
Lemma lem7656428 : term313.
Proof. exact (EQ_MP (@lem7656427) (@lem0)). Qed.
Lemma lem7656429 : term369.
Proof. exact (@lem7656418 (@lem7656428)). Qed.
Lemma lem7656431 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656432 : term313 = term319.
Proof. exact (@lem7656431 (NUMERAL 0) term117). Qed.
Lemma lem7656433 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656434 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656435 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656434 h1) (fun h1 : term319 = True => @lem7656433)). Qed.
Lemma lem7656436 : term319 = True.
Proof. exact (EQ_MP (@lem7656435) (@lem7656433)). Qed.
Lemma lem7656437 : term313 = True.
Proof. exact (TRANS (@lem7656432) (@lem7656436)). Qed.
Lemma lem7656438 : True = term313.
Proof. exact (SYM (@lem7656437)). Qed.
Lemma lem7656439 : term313.
Proof. exact (EQ_MP (@lem7656438) (@lem0)). Qed.
Lemma lem7656440 : term370.
Proof. exact (@lem7656429 (@lem7656439)). Qed.
Lemma lem7656442 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656443 : term175 = term176.
Proof. exact (@lem7656442 term117 term117). Qed.
Lemma lem7656444 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656445 : term178 = term117.
Proof. exact (EQ_MP (@lem7656444) (@lem940073)). Qed.
Lemma lem7656446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656447 : term176 = term116.
Proof. exact (MK_COMB (@lem7656446) (@lem7656445)). Qed.
Lemma lem7656448 : term175 = term116.
Proof. exact (TRANS (@lem7656443) (@lem7656447)). Qed.
Lemma lem7656450 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7656451 : term206 = term211.
Proof. exact (@lem7656450 term117 term117). Qed.
Lemma lem7656452 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656453 : term178 = term117.
Proof. exact (EQ_MP (@lem7656452) (@lem940073)). Qed.
Lemma lem7656454 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656455 : term176 = term116.
Proof. exact (MK_COMB (@lem7656454) (@lem7656453)). Qed.
Lemma lem7656456 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7656457 : term211 = term166.
Proof. exact (MK_COMB (@lem7656456) (@lem7656455)). Qed.
Lemma lem7656458 : term206 = term166.
Proof. exact (TRANS (@lem7656451) (@lem7656457)). Qed.
Lemma lem7656459 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656460 : term371 = term363.
Proof. exact (MK_COMB (@lem7656459) (@lem7656458)). Qed.
Lemma lem7656461 : term372 = term365.
Proof. exact (MK_COMB (@lem7656460) (@lem7656448)). Qed.
Lemma lem7656463 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7656464 : term365 = term102.
Proof. exact (@lem7656463 term117). Qed.
Lemma lem7656465 : term372 = term102.
Proof. exact (TRANS (@lem7656461) (@lem7656464)). Qed.
Lemma lem7656466 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7656467 : term374 = term375.
Proof. exact (MK_COMB (@lem7656466) (@lem7656465)). Qed.
Lemma lem7656468 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7656469 : term376 = term324.
Proof. exact (MK_COMB (@lem7656467) (@lem7656468)). Qed.
Lemma lem7656471 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656472 : term324 = term102.
Proof. exact (@lem7656471 term117). Qed.
Lemma lem7656473 : term376 = term102.
Proof. exact (TRANS (@lem7656469) (@lem7656472)). Qed.
Lemma lem7656475 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656476 : term175 = term176.
Proof. exact (@lem7656475 term117 term117). Qed.
Lemma lem7656477 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656478 : term178 = term117.
Proof. exact (EQ_MP (@lem7656477) (@lem940073)). Qed.
Lemma lem7656479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656480 : term176 = term116.
Proof. exact (MK_COMB (@lem7656479) (@lem7656478)). Qed.
Lemma lem7656481 : term175 = term116.
Proof. exact (TRANS (@lem7656476) (@lem7656480)). Qed.
Lemma lem7656482 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7656483 : term377 = term324.
Proof. exact (MK_COMB (@lem7656482) (@lem7656481)). Qed.
Lemma lem7656485 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656486 : term324 = term102.
Proof. exact (@lem7656485 term117). Qed.
Lemma lem7656487 : term377 = term102.
Proof. exact (TRANS (@lem7656483) (@lem7656486)). Qed.
Lemma lem7656488 : term102 = term377.
Proof. exact (SYM (@lem7656487)). Qed.
Lemma lem7656489 : term376 = term377.
Proof. exact (TRANS (@lem7656473) (@lem7656488)). Qed.
Lemma lem7656490 : term366 = term163.
Proof. exact (@lem7656440 (@lem7656489)). Qed.
Lemma lem7656491 : term365 = term163.
Proof. exact (TRANS (@lem7656406) (@lem7656490)). Qed.
Lemma lem7656493 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7656494 : term163 = term102.
Proof. exact (@lem7656493 term102). Qed.
Lemma lem7656495 : term365 = term102.
Proof. exact (TRANS (@lem7656491) (@lem7656494)). Qed.
Lemma lem7656496 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7656497 : term378 = term375.
Proof. exact (MK_COMB (@lem7656496) (@lem7656495)). Qed.
Lemma lem7656498 (_98535 : int) : (real_of_int _98535) = (real_of_int _98535).
Proof. exact (eq_refl (real_of_int _98535)). Qed.
Lemma lem7656499 (_98535 : int) : (term362 _98535) = (term379 _98535).
Proof. exact (MK_COMB (@lem7656497) (@lem7656498 _98535)). Qed.
Lemma lem7656500 (_98535 : int) : (term361 _98535) = (term379 _98535).
Proof. exact (TRANS (@lem7656397 _98535) (@lem7656499 _98535)). Qed.
Lemma lem7656501 (_98535 : int) : (term379 _98535) = term102.
Proof. exact (@lem1982719 (real_of_int _98535)). Qed.
Lemma lem7656502 (_98535 : int) : (term361 _98535) = term102.
Proof. exact (TRANS (@lem7656500 _98535) (@lem7656501 _98535)). Qed.
Lemma lem7656503 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656504 (_98535 : int) : (term380 _98535) = term381.
Proof. exact (MK_COMB (@lem7656503) (@lem7656502 _98535)). Qed.
Lemma lem7656505 (_98536 : int) : (term385 _98536) = (term386 _98536).
Proof. exact (@lem1982763 (term193 _98536) (real_of_int _98536) term166). Qed.
Lemma lem7656506 (_98536 : int) : (term387 _98536) = (term362 _98536).
Proof. exact (@lem1982713 term166 (real_of_int _98536)). Qed.
Lemma lem7656508 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7656509 : term116 = term205.
Proof. exact (@lem7656508 term117). Qed.
Lemma lem7656511 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7656512 : term166 = term167.
Proof. exact (@lem7656511 term117). Qed.
Lemma lem7656513 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656514 : term363 = term364.
Proof. exact (MK_COMB (@lem7656513) (@lem7656512)). Qed.
Lemma lem7656515 : term365 = term366.
Proof. exact (MK_COMB (@lem7656514) (@lem7656509)). Qed.
Lemma lem7656516 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7656518 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656519 : term313 = term319.
Proof. exact (@lem7656518 (NUMERAL 0) term117). Qed.
Lemma lem7656520 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656521 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656522 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656521 h1) (fun h1 : term319 = True => @lem7656520)). Qed.
Lemma lem7656523 : term319 = True.
Proof. exact (EQ_MP (@lem7656522) (@lem7656520)). Qed.
Lemma lem7656524 : term313 = True.
Proof. exact (TRANS (@lem7656519) (@lem7656523)). Qed.
Lemma lem7656525 : True = term313.
Proof. exact (SYM (@lem7656524)). Qed.
Lemma lem7656526 : term313.
Proof. exact (EQ_MP (@lem7656525) (@lem0)). Qed.
Lemma lem7656527 : term368.
Proof. exact (@lem7656516 (@lem7656526)). Qed.
Lemma lem7656529 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656530 : term313 = term319.
Proof. exact (@lem7656529 (NUMERAL 0) term117). Qed.
Lemma lem7656531 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656532 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656533 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656532 h1) (fun h1 : term319 = True => @lem7656531)). Qed.
Lemma lem7656534 : term319 = True.
Proof. exact (EQ_MP (@lem7656533) (@lem7656531)). Qed.
Lemma lem7656535 : term313 = True.
Proof. exact (TRANS (@lem7656530) (@lem7656534)). Qed.
Lemma lem7656536 : True = term313.
Proof. exact (SYM (@lem7656535)). Qed.
Lemma lem7656537 : term313.
Proof. exact (EQ_MP (@lem7656536) (@lem0)). Qed.
Lemma lem7656538 : term369.
Proof. exact (@lem7656527 (@lem7656537)). Qed.
Lemma lem7656540 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656541 : term313 = term319.
Proof. exact (@lem7656540 (NUMERAL 0) term117). Qed.
Lemma lem7656542 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656543 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656544 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656543 h1) (fun h1 : term319 = True => @lem7656542)). Qed.
Lemma lem7656545 : term319 = True.
Proof. exact (EQ_MP (@lem7656544) (@lem7656542)). Qed.
Lemma lem7656546 : term313 = True.
Proof. exact (TRANS (@lem7656541) (@lem7656545)). Qed.
Lemma lem7656547 : True = term313.
Proof. exact (SYM (@lem7656546)). Qed.
Lemma lem7656548 : term313.
Proof. exact (EQ_MP (@lem7656547) (@lem0)). Qed.
Lemma lem7656549 : term370.
Proof. exact (@lem7656538 (@lem7656548)). Qed.
Lemma lem7656551 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656552 : term175 = term176.
Proof. exact (@lem7656551 term117 term117). Qed.
Lemma lem7656553 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656554 : term178 = term117.
Proof. exact (EQ_MP (@lem7656553) (@lem940073)). Qed.
Lemma lem7656555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656556 : term176 = term116.
Proof. exact (MK_COMB (@lem7656555) (@lem7656554)). Qed.
Lemma lem7656557 : term175 = term116.
Proof. exact (TRANS (@lem7656552) (@lem7656556)). Qed.
Lemma lem7656559 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7656560 : term206 = term211.
Proof. exact (@lem7656559 term117 term117). Qed.
Lemma lem7656561 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656562 : term178 = term117.
Proof. exact (EQ_MP (@lem7656561) (@lem940073)). Qed.
Lemma lem7656563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656564 : term176 = term116.
Proof. exact (MK_COMB (@lem7656563) (@lem7656562)). Qed.
Lemma lem7656565 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7656566 : term211 = term166.
Proof. exact (MK_COMB (@lem7656565) (@lem7656564)). Qed.
Lemma lem7656567 : term206 = term166.
Proof. exact (TRANS (@lem7656560) (@lem7656566)). Qed.
Lemma lem7656568 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656569 : term371 = term363.
Proof. exact (MK_COMB (@lem7656568) (@lem7656567)). Qed.
Lemma lem7656570 : term372 = term365.
Proof. exact (MK_COMB (@lem7656569) (@lem7656557)). Qed.
Lemma lem7656572 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7656573 : term365 = term102.
Proof. exact (@lem7656572 term117). Qed.
Lemma lem7656574 : term372 = term102.
Proof. exact (TRANS (@lem7656570) (@lem7656573)). Qed.
Lemma lem7656575 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7656576 : term374 = term375.
Proof. exact (MK_COMB (@lem7656575) (@lem7656574)). Qed.
Lemma lem7656577 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7656578 : term376 = term324.
Proof. exact (MK_COMB (@lem7656576) (@lem7656577)). Qed.
Lemma lem7656580 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656581 : term324 = term102.
Proof. exact (@lem7656580 term117). Qed.
Lemma lem7656582 : term376 = term102.
Proof. exact (TRANS (@lem7656578) (@lem7656581)). Qed.
Lemma lem7656584 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656585 : term175 = term176.
Proof. exact (@lem7656584 term117 term117). Qed.
Lemma lem7656586 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656587 : term178 = term117.
Proof. exact (EQ_MP (@lem7656586) (@lem940073)). Qed.
Lemma lem7656588 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656589 : term176 = term116.
Proof. exact (MK_COMB (@lem7656588) (@lem7656587)). Qed.
Lemma lem7656590 : term175 = term116.
Proof. exact (TRANS (@lem7656585) (@lem7656589)). Qed.
Lemma lem7656591 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7656592 : term377 = term324.
Proof. exact (MK_COMB (@lem7656591) (@lem7656590)). Qed.
Lemma lem7656594 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656595 : term324 = term102.
Proof. exact (@lem7656594 term117). Qed.
Lemma lem7656596 : term377 = term102.
Proof. exact (TRANS (@lem7656592) (@lem7656595)). Qed.
Lemma lem7656597 : term102 = term377.
Proof. exact (SYM (@lem7656596)). Qed.
Lemma lem7656598 : term376 = term377.
Proof. exact (TRANS (@lem7656582) (@lem7656597)). Qed.
Lemma lem7656599 : term366 = term163.
Proof. exact (@lem7656549 (@lem7656598)). Qed.
Lemma lem7656600 : term365 = term163.
Proof. exact (TRANS (@lem7656515) (@lem7656599)). Qed.
Lemma lem7656602 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7656603 : term163 = term102.
Proof. exact (@lem7656602 term102). Qed.
Lemma lem7656604 : term365 = term102.
Proof. exact (TRANS (@lem7656600) (@lem7656603)). Qed.
Lemma lem7656605 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7656606 : term378 = term375.
Proof. exact (MK_COMB (@lem7656605) (@lem7656604)). Qed.
Lemma lem7656607 (_98536 : int) : (real_of_int _98536) = (real_of_int _98536).
Proof. exact (eq_refl (real_of_int _98536)). Qed.
Lemma lem7656608 (_98536 : int) : (term362 _98536) = (term379 _98536).
Proof. exact (MK_COMB (@lem7656606) (@lem7656607 _98536)). Qed.
Lemma lem7656609 (_98536 : int) : (term387 _98536) = (term379 _98536).
Proof. exact (TRANS (@lem7656506 _98536) (@lem7656608 _98536)). Qed.
Lemma lem7656610 (_98536 : int) : (term379 _98536) = term102.
Proof. exact (@lem1982719 (real_of_int _98536)). Qed.
Lemma lem7656611 (_98536 : int) : (term387 _98536) = term102.
Proof. exact (TRANS (@lem7656609 _98536) (@lem7656610 _98536)). Qed.
Lemma lem7656612 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656613 (_98536 : int) : (term388 _98536) = term381.
Proof. exact (MK_COMB (@lem7656612) (@lem7656611 _98536)). Qed.
Lemma lem7656614 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem7656615 (_98536 : int) : (term386 _98536) = term389.
Proof. exact (MK_COMB (@lem7656613 _98536) (@lem7656614)). Qed.
Lemma lem7656616 (_98536 : int) : (term385 _98536) = term389.
Proof. exact (TRANS (@lem7656505 _98536) (@lem7656615 _98536)). Qed.
Lemma lem7656617 : term389 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem7656618 (_98536 : int) : (term385 _98536) = term166.
Proof. exact (TRANS (@lem7656616 _98536) (@lem7656617)). Qed.
Lemma lem7656619 (_98535 : int) (_98536 : int) : (term383 _98535 _98536) = term389.
Proof. exact (MK_COMB (@lem7656504 _98535) (@lem7656618 _98536)). Qed.
Lemma lem7656620 (_98535 : int) (_98536 : int) : (term382 _98535 _98536) = term389.
Proof. exact (TRANS (@lem7656396 _98535 _98536) (@lem7656619 _98535 _98536)). Qed.
Lemma lem7656621 : term389 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem7656622 (_98535 : int) (_98536 : int) : (term382 _98535 _98536) = term166.
Proof. exact (TRANS (@lem7656620 _98535 _98536) (@lem7656621)). Qed.
Lemma lem7656623 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7656624 (_98535 : int) (_98536 : int) : (term634 _98535 _98536) = term391.
Proof. exact (MK_COMB (@lem7656623) (@lem7656622 _98535 _98536)). Qed.
Lemma lem7656625 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7656626 (_98535 : int) (_98536 : int) : (term633 _98535 _98536) = term392.
Proof. exact (MK_COMB (@lem7656624 _98535 _98536) (@lem7656625)). Qed.
Lemma lem7656627 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : term392.
Proof. exact (EQ_MP (@lem7656626 _98535 _98536) (@lem7656395 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656629 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7656630 : term392 = term393.
Proof. exact (@lem7656629 term102 term166). Qed.
Lemma lem7656632 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7656633 : term166 = term167.
Proof. exact (@lem7656632 term117). Qed.
Lemma lem7656635 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7656636 : term102 = term163.
Proof. exact (@lem7656635 (NUMERAL 0)). Qed.
Lemma lem7656637 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7656638 : term104 = term394.
Proof. exact (MK_COMB (@lem7656637) (@lem7656636)). Qed.
Lemma lem7656639 : term393 = term395.
Proof. exact (MK_COMB (@lem7656638) (@lem7656633)). Qed.
Lemma lem7656640 : term396.
Proof. exact (@lem1980026 term102 term116 term166 term116). Qed.
Lemma lem7656642 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656643 : term313 = term319.
Proof. exact (@lem7656642 (NUMERAL 0) term117). Qed.
Lemma lem7656644 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656645 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656646 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656645 h1) (fun h1 : term319 = True => @lem7656644)). Qed.
Lemma lem7656647 : term319 = True.
Proof. exact (EQ_MP (@lem7656646) (@lem7656644)). Qed.
Lemma lem7656648 : term313 = True.
Proof. exact (TRANS (@lem7656643) (@lem7656647)). Qed.
Lemma lem7656649 : True = term313.
Proof. exact (SYM (@lem7656648)). Qed.
Lemma lem7656650 : term313.
Proof. exact (EQ_MP (@lem7656649) (@lem0)). Qed.
Lemma lem7656651 : term397.
Proof. exact (@lem7656640 (@lem7656650)). Qed.
Lemma lem7656653 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656654 : term313 = term319.
Proof. exact (@lem7656653 (NUMERAL 0) term117). Qed.
Lemma lem7656655 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656656 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656657 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656656 h1) (fun h1 : term319 = True => @lem7656655)). Qed.
Lemma lem7656658 : term319 = True.
Proof. exact (EQ_MP (@lem7656657) (@lem7656655)). Qed.
Lemma lem7656659 : term313 = True.
Proof. exact (TRANS (@lem7656654) (@lem7656658)). Qed.
Lemma lem7656660 : True = term313.
Proof. exact (SYM (@lem7656659)). Qed.
Lemma lem7656661 : term313.
Proof. exact (EQ_MP (@lem7656660) (@lem0)). Qed.
Lemma lem7656662 : term395 = term398.
Proof. exact (@lem7656651 (@lem7656661)). Qed.
Lemma lem7656664 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7656665 : term206 = term211.
Proof. exact (@lem7656664 term117 term117). Qed.
Lemma lem7656666 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656667 : term178 = term117.
Proof. exact (EQ_MP (@lem7656666) (@lem940073)). Qed.
Lemma lem7656668 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656669 : term176 = term116.
Proof. exact (MK_COMB (@lem7656668) (@lem7656667)). Qed.
Lemma lem7656670 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7656671 : term211 = term166.
Proof. exact (MK_COMB (@lem7656670) (@lem7656669)). Qed.
Lemma lem7656672 : term206 = term166.
Proof. exact (TRANS (@lem7656665) (@lem7656671)). Qed.
Lemma lem7656674 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656675 : term324 = term102.
Proof. exact (@lem7656674 term117). Qed.
Lemma lem7656676 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7656677 : term399 = term104.
Proof. exact (MK_COMB (@lem7656676) (@lem7656675)). Qed.
Lemma lem7656678 : term398 = term393.
Proof. exact (MK_COMB (@lem7656677) (@lem7656672)). Qed.
Lemma lem7656680 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7656681 : term393 = term402.
Proof. exact (@lem7656680 (NUMERAL 0) term117). Qed.
Lemma lem7656682 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656683 (h1 : term320 = (BIT1 0)) : (term117 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7656684 : (term320 = (BIT1 0)) = ((term117 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656683 h1) (fun h1 : (term117 = (NUMERAL 0)) = False => @lem7656682)). Qed.
Lemma lem7656685 : (term117 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7656684) (@lem7656682)). Qed.
Lemma lem7656686 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7656687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7656688 : term403 = (and True).
Proof. exact (MK_COMB (@lem7656687) (@lem7656686)). Qed.
Lemma lem7656689 : term402 = (True /\ False).
Proof. exact (MK_COMB (@lem7656688) (@lem7656685)). Qed.
Lemma lem7656691 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7656692 : term402 = False.
Proof. exact (TRANS (@lem7656689) (@lem7656691)). Qed.
Lemma lem7656693 : term393 = False.
Proof. exact (TRANS (@lem7656681) (@lem7656692)). Qed.
Lemma lem7656694 : term398 = False.
Proof. exact (TRANS (@lem7656678) (@lem7656693)). Qed.
Lemma lem7656695 : term395 = False.
Proof. exact (TRANS (@lem7656662) (@lem7656694)). Qed.
Lemma lem7656696 : term393 = False.
Proof. exact (TRANS (@lem7656639) (@lem7656695)). Qed.
Lemma lem7656697 : term392 = False.
Proof. exact (TRANS (@lem7656630) (@lem7656696)). Qed.
Lemma lem7656698 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term740 _98534 _98537 _98535 _98536) : False.
Proof. exact (EQ_MP (@lem7656697) (@lem7656627 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656699 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term757 _98534 _98537 _98535 _98536.
Proof. exact (h1). Qed.
Lemma lem7656700 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term739 _98534 _98537 _98535 _98536.
Proof. exact (proj2 (@lem7656699 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656702 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term735 _98534 _98537 _98535 _98536.
Proof. exact (proj2 (@lem7656700 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656703 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term186 _98535.
Proof. exact (proj1 (@lem7656700 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656704 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term731 _98534 _98537 _98535 _98536.
Proof. exact (proj2 (@lem7656702 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656706 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term727 _98534 _98537 _98535 _98536.
Proof. exact (proj2 (@lem7656704 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656708 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term717 _98534 _98537 _98535 _98536.
Proof. exact (proj2 (@lem7656706 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656709 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term221 _98534 _98537 _98536.
Proof. exact (proj1 (@lem7656706 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656710 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : (real_of_int _98536) = term102.
Proof. exact (proj2 (@lem7656709 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656712 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term226 _98535 _98536.
Proof. exact (proj2 (@lem7656708 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656715 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7656716 : term312 = term313.
Proof. exact (@lem7656715 term102 term116). Qed.
Lemma lem7656718 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7656719 : term116 = term205.
Proof. exact (@lem7656718 term117). Qed.
Lemma lem7656721 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7656722 : term102 = term163.
Proof. exact (@lem7656721 (NUMERAL 0)). Qed.
Lemma lem7656723 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7656724 : term314 = term315.
Proof. exact (MK_COMB (@lem7656723) (@lem7656722)). Qed.
Lemma lem7656725 : term313 = term316.
Proof. exact (MK_COMB (@lem7656724) (@lem7656719)). Qed.
Lemma lem7656726 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7656728 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656729 : term313 = term319.
Proof. exact (@lem7656728 (NUMERAL 0) term117). Qed.
Lemma lem7656730 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656731 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656732 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656731 h1) (fun h1 : term319 = True => @lem7656730)). Qed.
Lemma lem7656733 : term319 = True.
Proof. exact (EQ_MP (@lem7656732) (@lem7656730)). Qed.
Lemma lem7656734 : term313 = True.
Proof. exact (TRANS (@lem7656729) (@lem7656733)). Qed.
Lemma lem7656735 : True = term313.
Proof. exact (SYM (@lem7656734)). Qed.
Lemma lem7656736 : term313.
Proof. exact (EQ_MP (@lem7656735) (@lem0)). Qed.
Lemma lem7656737 : term321.
Proof. exact (@lem7656726 (@lem7656736)). Qed.
Lemma lem7656739 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656740 : term313 = term319.
Proof. exact (@lem7656739 (NUMERAL 0) term117). Qed.
Lemma lem7656741 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656742 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656743 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656742 h1) (fun h1 : term319 = True => @lem7656741)). Qed.
Lemma lem7656744 : term319 = True.
Proof. exact (EQ_MP (@lem7656743) (@lem7656741)). Qed.
Lemma lem7656745 : term313 = True.
Proof. exact (TRANS (@lem7656740) (@lem7656744)). Qed.
Lemma lem7656746 : True = term313.
Proof. exact (SYM (@lem7656745)). Qed.
Lemma lem7656747 : term313.
Proof. exact (EQ_MP (@lem7656746) (@lem0)). Qed.
Lemma lem7656748 : term316 = term322.
Proof. exact (@lem7656737 (@lem7656747)). Qed.
Lemma lem7656750 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656751 : term175 = term176.
Proof. exact (@lem7656750 term117 term117). Qed.
Lemma lem7656752 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656753 : term178 = term117.
Proof. exact (EQ_MP (@lem7656752) (@lem940073)). Qed.
Lemma lem7656754 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656755 : term176 = term116.
Proof. exact (MK_COMB (@lem7656754) (@lem7656753)). Qed.
Lemma lem7656756 : term175 = term116.
Proof. exact (TRANS (@lem7656751) (@lem7656755)). Qed.
Lemma lem7656758 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656759 : term324 = term102.
Proof. exact (@lem7656758 term117). Qed.
Lemma lem7656760 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7656761 : term325 = term314.
Proof. exact (MK_COMB (@lem7656760) (@lem7656759)). Qed.
Lemma lem7656762 : term322 = term313.
Proof. exact (MK_COMB (@lem7656761) (@lem7656756)). Qed.
Lemma lem7656764 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656765 : term313 = term319.
Proof. exact (@lem7656764 (NUMERAL 0) term117). Qed.
Lemma lem7656766 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656767 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656768 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656767 h1) (fun h1 : term319 = True => @lem7656766)). Qed.
Lemma lem7656769 : term319 = True.
Proof. exact (EQ_MP (@lem7656768) (@lem7656766)). Qed.
Lemma lem7656770 : term313 = True.
Proof. exact (TRANS (@lem7656765) (@lem7656769)). Qed.
Lemma lem7656771 : term322 = True.
Proof. exact (TRANS (@lem7656762) (@lem7656770)). Qed.
Lemma lem7656772 : term316 = True.
Proof. exact (TRANS (@lem7656748) (@lem7656771)). Qed.
Lemma lem7656773 : term313 = True.
Proof. exact (TRANS (@lem7656725) (@lem7656772)). Qed.
Lemma lem7656774 : term312 = True.
Proof. exact (TRANS (@lem7656716) (@lem7656773)). Qed.
Lemma lem7656775 : True = term312.
Proof. exact (SYM (@lem7656774)). Qed.
Lemma lem7656776 : term312.
Proof. exact (EQ_MP (@lem7656775) (@lem0)). Qed.
Lemma lem7656777 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term758 _98535.
Proof. exact (conj (@lem7656776) (@lem7656703 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656779 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7656780 (_98535 : int) : term759 _98535.
Proof. exact (@lem7656779 term116 (real_of_int _98535)). Qed.
Lemma lem7656781 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term760 _98535.
Proof. exact (@lem7656780 _98535 (@lem7656777 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656782 (_98535 : int) : (term350 _98535) = (real_of_int _98535).
Proof. exact (@lem1982733 (real_of_int _98535)). Qed.
Lemma lem7656783 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7656784 (_98535 : int) : (term761 _98535) = (term185 _98535).
Proof. exact (MK_COMB (@lem7656783) (@lem7656782 _98535)). Qed.
Lemma lem7656785 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7656786 (_98535 : int) : (term760 _98535) = (term186 _98535).
Proof. exact (MK_COMB (@lem7656784 _98535) (@lem7656785)). Qed.
Lemma lem7656787 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term186 _98535.
Proof. exact (EQ_MP (@lem7656786 _98535) (@lem7656781 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656789 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7656790 : term312 = term313.
Proof. exact (@lem7656789 term102 term116). Qed.
Lemma lem7656792 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7656793 : term116 = term205.
Proof. exact (@lem7656792 term117). Qed.
Lemma lem7656795 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7656796 : term102 = term163.
Proof. exact (@lem7656795 (NUMERAL 0)). Qed.
Lemma lem7656797 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7656798 : term314 = term315.
Proof. exact (MK_COMB (@lem7656797) (@lem7656796)). Qed.
Lemma lem7656799 : term313 = term316.
Proof. exact (MK_COMB (@lem7656798) (@lem7656793)). Qed.
Lemma lem7656800 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7656802 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656803 : term313 = term319.
Proof. exact (@lem7656802 (NUMERAL 0) term117). Qed.
Lemma lem7656804 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656805 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656806 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656805 h1) (fun h1 : term319 = True => @lem7656804)). Qed.
Lemma lem7656807 : term319 = True.
Proof. exact (EQ_MP (@lem7656806) (@lem7656804)). Qed.
Lemma lem7656808 : term313 = True.
Proof. exact (TRANS (@lem7656803) (@lem7656807)). Qed.
Lemma lem7656809 : True = term313.
Proof. exact (SYM (@lem7656808)). Qed.
Lemma lem7656810 : term313.
Proof. exact (EQ_MP (@lem7656809) (@lem0)). Qed.
Lemma lem7656811 : term321.
Proof. exact (@lem7656800 (@lem7656810)). Qed.
Lemma lem7656813 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656814 : term313 = term319.
Proof. exact (@lem7656813 (NUMERAL 0) term117). Qed.
Lemma lem7656815 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656816 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656817 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656816 h1) (fun h1 : term319 = True => @lem7656815)). Qed.
Lemma lem7656818 : term319 = True.
Proof. exact (EQ_MP (@lem7656817) (@lem7656815)). Qed.
Lemma lem7656819 : term313 = True.
Proof. exact (TRANS (@lem7656814) (@lem7656818)). Qed.
Lemma lem7656820 : True = term313.
Proof. exact (SYM (@lem7656819)). Qed.
Lemma lem7656821 : term313.
Proof. exact (EQ_MP (@lem7656820) (@lem0)). Qed.
Lemma lem7656822 : term316 = term322.
Proof. exact (@lem7656811 (@lem7656821)). Qed.
Lemma lem7656824 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656825 : term175 = term176.
Proof. exact (@lem7656824 term117 term117). Qed.
Lemma lem7656826 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656827 : term178 = term117.
Proof. exact (EQ_MP (@lem7656826) (@lem940073)). Qed.
Lemma lem7656828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656829 : term176 = term116.
Proof. exact (MK_COMB (@lem7656828) (@lem7656827)). Qed.
Lemma lem7656830 : term175 = term116.
Proof. exact (TRANS (@lem7656825) (@lem7656829)). Qed.
Lemma lem7656832 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656833 : term324 = term102.
Proof. exact (@lem7656832 term117). Qed.
Lemma lem7656834 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7656835 : term325 = term314.
Proof. exact (MK_COMB (@lem7656834) (@lem7656833)). Qed.
Lemma lem7656836 : term322 = term313.
Proof. exact (MK_COMB (@lem7656835) (@lem7656830)). Qed.
Lemma lem7656838 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656839 : term313 = term319.
Proof. exact (@lem7656838 (NUMERAL 0) term117). Qed.
Lemma lem7656840 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656841 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656842 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656841 h1) (fun h1 : term319 = True => @lem7656840)). Qed.
Lemma lem7656843 : term319 = True.
Proof. exact (EQ_MP (@lem7656842) (@lem7656840)). Qed.
Lemma lem7656844 : term313 = True.
Proof. exact (TRANS (@lem7656839) (@lem7656843)). Qed.
Lemma lem7656845 : term322 = True.
Proof. exact (TRANS (@lem7656836) (@lem7656844)). Qed.
Lemma lem7656846 : term316 = True.
Proof. exact (TRANS (@lem7656822) (@lem7656845)). Qed.
Lemma lem7656847 : term313 = True.
Proof. exact (TRANS (@lem7656799) (@lem7656846)). Qed.
Lemma lem7656848 : term312 = True.
Proof. exact (TRANS (@lem7656790) (@lem7656847)). Qed.
Lemma lem7656849 : True = term312.
Proof. exact (SYM (@lem7656848)). Qed.
Lemma lem7656850 : term312.
Proof. exact (EQ_MP (@lem7656849) (@lem0)). Qed.
Lemma lem7656851 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term418 _98535 _98536.
Proof. exact (conj (@lem7656850) (@lem7656712 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656853 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7656854 (_98535 : int) (_98536 : int) : term419 _98535 _98536.
Proof. exact (@lem7656853 term116 (term224 _98535 _98536)). Qed.
Lemma lem7656855 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term420 _98535 _98536.
Proof. exact (@lem7656854 _98535 _98536 (@lem7656851 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656856 (_98535 : int) (_98536 : int) : (term421 _98535 _98536) = (term224 _98535 _98536).
Proof. exact (@lem1982733 (term224 _98535 _98536)). Qed.
Lemma lem7656857 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7656858 (_98535 : int) (_98536 : int) : (term422 _98535 _98536) = (term225 _98535 _98536).
Proof. exact (MK_COMB (@lem7656857) (@lem7656856 _98535 _98536)). Qed.
Lemma lem7656859 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7656860 (_98535 : int) (_98536 : int) : (term420 _98535 _98536) = (term226 _98535 _98536).
Proof. exact (MK_COMB (@lem7656858 _98535 _98536) (@lem7656859)). Qed.
Lemma lem7656861 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term226 _98535 _98536.
Proof. exact (EQ_MP (@lem7656860 _98535 _98536) (@lem7656855 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656863 (y : real) : term332 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem7656864 (_98536 : int) : term405 _98536.
Proof. exact (@lem7656863 (real_of_int _98536)). Qed.
Lemma lem7656865 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term406 _98536.
Proof. exact (@lem7656864 _98536 (@lem7656710 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656866 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term492 _98536.
Proof. exact (@lem7656865 _98534 _98537 _98535 _98536 h1 term166). Qed.
Lemma lem7656867 (_98536 : int) : (term492 _98536) = ((term193 _98536) = term102).
Proof. exact (eq_refl (term492 _98536)). Qed.
Lemma lem7656874 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : (term193 _98536) = term102.
Proof. exact (EQ_MP (@lem7656867 _98536) (@lem7656866 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656875 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term762 _98535 _98536.
Proof. exact (conj (@lem7656874 _98534 _98537 _98535 _98536 h1) (@lem7656861 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656877 (x : real) (y : real) : term356 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem7656878 (_98535 : int) (_98536 : int) : term763 _98535 _98536.
Proof. exact (@lem7656877 (term193 _98536) (term224 _98535 _98536)). Qed.
Lemma lem7656879 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term764 _98535 _98536.
Proof. exact (@lem7656878 _98535 _98536 (@lem7656875 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7656880 (_98535 : int) (_98536 : int) : (term765 _98535 _98536) = (term766 _98535 _98536).
Proof. exact (@lem1982757 (term193 _98535) (term193 _98536) (term384 _98536)). Qed.
Lemma lem7656881 (_98536 : int) : (term385 _98536) = (term386 _98536).
Proof. exact (@lem1982763 (term193 _98536) (real_of_int _98536) term166). Qed.
Lemma lem7656882 (_98536 : int) : (term387 _98536) = (term362 _98536).
Proof. exact (@lem1982713 term166 (real_of_int _98536)). Qed.
Lemma lem7656884 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7656885 : term116 = term205.
Proof. exact (@lem7656884 term117). Qed.
Lemma lem7656887 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7656888 : term166 = term167.
Proof. exact (@lem7656887 term117). Qed.
Lemma lem7656889 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656890 : term363 = term364.
Proof. exact (MK_COMB (@lem7656889) (@lem7656888)). Qed.
Lemma lem7656891 : term365 = term366.
Proof. exact (MK_COMB (@lem7656890) (@lem7656885)). Qed.
Lemma lem7656892 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7656894 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656895 : term313 = term319.
Proof. exact (@lem7656894 (NUMERAL 0) term117). Qed.
Lemma lem7656896 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656897 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656898 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656897 h1) (fun h1 : term319 = True => @lem7656896)). Qed.
Lemma lem7656899 : term319 = True.
Proof. exact (EQ_MP (@lem7656898) (@lem7656896)). Qed.
Lemma lem7656900 : term313 = True.
Proof. exact (TRANS (@lem7656895) (@lem7656899)). Qed.
Lemma lem7656901 : True = term313.
Proof. exact (SYM (@lem7656900)). Qed.
Lemma lem7656902 : term313.
Proof. exact (EQ_MP (@lem7656901) (@lem0)). Qed.
Lemma lem7656903 : term368.
Proof. exact (@lem7656892 (@lem7656902)). Qed.
Lemma lem7656905 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656906 : term313 = term319.
Proof. exact (@lem7656905 (NUMERAL 0) term117). Qed.
Lemma lem7656907 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656908 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656909 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656908 h1) (fun h1 : term319 = True => @lem7656907)). Qed.
Lemma lem7656910 : term319 = True.
Proof. exact (EQ_MP (@lem7656909) (@lem7656907)). Qed.
Lemma lem7656911 : term313 = True.
Proof. exact (TRANS (@lem7656906) (@lem7656910)). Qed.
Lemma lem7656912 : True = term313.
Proof. exact (SYM (@lem7656911)). Qed.
Lemma lem7656913 : term313.
Proof. exact (EQ_MP (@lem7656912) (@lem0)). Qed.
Lemma lem7656914 : term369.
Proof. exact (@lem7656903 (@lem7656913)). Qed.
Lemma lem7656916 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7656917 : term313 = term319.
Proof. exact (@lem7656916 (NUMERAL 0) term117). Qed.
Lemma lem7656918 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7656919 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7656920 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7656919 h1) (fun h1 : term319 = True => @lem7656918)). Qed.
Lemma lem7656921 : term319 = True.
Proof. exact (EQ_MP (@lem7656920) (@lem7656918)). Qed.
Lemma lem7656922 : term313 = True.
Proof. exact (TRANS (@lem7656917) (@lem7656921)). Qed.
Lemma lem7656923 : True = term313.
Proof. exact (SYM (@lem7656922)). Qed.
Lemma lem7656924 : term313.
Proof. exact (EQ_MP (@lem7656923) (@lem0)). Qed.
Lemma lem7656925 : term370.
Proof. exact (@lem7656914 (@lem7656924)). Qed.
Lemma lem7656927 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656928 : term175 = term176.
Proof. exact (@lem7656927 term117 term117). Qed.
Lemma lem7656929 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656930 : term178 = term117.
Proof. exact (EQ_MP (@lem7656929) (@lem940073)). Qed.
Lemma lem7656931 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656932 : term176 = term116.
Proof. exact (MK_COMB (@lem7656931) (@lem7656930)). Qed.
Lemma lem7656933 : term175 = term116.
Proof. exact (TRANS (@lem7656928) (@lem7656932)). Qed.
Lemma lem7656935 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7656936 : term206 = term211.
Proof. exact (@lem7656935 term117 term117). Qed.
Lemma lem7656937 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656938 : term178 = term117.
Proof. exact (EQ_MP (@lem7656937) (@lem940073)). Qed.
Lemma lem7656939 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656940 : term176 = term116.
Proof. exact (MK_COMB (@lem7656939) (@lem7656938)). Qed.
Lemma lem7656941 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7656942 : term211 = term166.
Proof. exact (MK_COMB (@lem7656941) (@lem7656940)). Qed.
Lemma lem7656943 : term206 = term166.
Proof. exact (TRANS (@lem7656936) (@lem7656942)). Qed.
Lemma lem7656944 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656945 : term371 = term363.
Proof. exact (MK_COMB (@lem7656944) (@lem7656943)). Qed.
Lemma lem7656946 : term372 = term365.
Proof. exact (MK_COMB (@lem7656945) (@lem7656933)). Qed.
Lemma lem7656948 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7656949 : term365 = term102.
Proof. exact (@lem7656948 term117). Qed.
Lemma lem7656950 : term372 = term102.
Proof. exact (TRANS (@lem7656946) (@lem7656949)). Qed.
Lemma lem7656951 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7656952 : term374 = term375.
Proof. exact (MK_COMB (@lem7656951) (@lem7656950)). Qed.
Lemma lem7656953 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7656954 : term376 = term324.
Proof. exact (MK_COMB (@lem7656952) (@lem7656953)). Qed.
Lemma lem7656956 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656957 : term324 = term102.
Proof. exact (@lem7656956 term117). Qed.
Lemma lem7656958 : term376 = term102.
Proof. exact (TRANS (@lem7656954) (@lem7656957)). Qed.
Lemma lem7656960 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7656961 : term175 = term176.
Proof. exact (@lem7656960 term117 term117). Qed.
Lemma lem7656962 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7656963 : term178 = term117.
Proof. exact (EQ_MP (@lem7656962) (@lem940073)). Qed.
Lemma lem7656964 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7656965 : term176 = term116.
Proof. exact (MK_COMB (@lem7656964) (@lem7656963)). Qed.
Lemma lem7656966 : term175 = term116.
Proof. exact (TRANS (@lem7656961) (@lem7656965)). Qed.
Lemma lem7656967 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7656968 : term377 = term324.
Proof. exact (MK_COMB (@lem7656967) (@lem7656966)). Qed.
Lemma lem7656970 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7656971 : term324 = term102.
Proof. exact (@lem7656970 term117). Qed.
Lemma lem7656972 : term377 = term102.
Proof. exact (TRANS (@lem7656968) (@lem7656971)). Qed.
Lemma lem7656973 : term102 = term377.
Proof. exact (SYM (@lem7656972)). Qed.
Lemma lem7656974 : term376 = term377.
Proof. exact (TRANS (@lem7656958) (@lem7656973)). Qed.
Lemma lem7656975 : term366 = term163.
Proof. exact (@lem7656925 (@lem7656974)). Qed.
Lemma lem7656976 : term365 = term163.
Proof. exact (TRANS (@lem7656891) (@lem7656975)). Qed.
Lemma lem7656978 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7656979 : term163 = term102.
Proof. exact (@lem7656978 term102). Qed.
Lemma lem7656980 : term365 = term102.
Proof. exact (TRANS (@lem7656976) (@lem7656979)). Qed.
Lemma lem7656981 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7656982 : term378 = term375.
Proof. exact (MK_COMB (@lem7656981) (@lem7656980)). Qed.
Lemma lem7656983 (_98536 : int) : (real_of_int _98536) = (real_of_int _98536).
Proof. exact (eq_refl (real_of_int _98536)). Qed.
Lemma lem7656984 (_98536 : int) : (term362 _98536) = (term379 _98536).
Proof. exact (MK_COMB (@lem7656982) (@lem7656983 _98536)). Qed.
Lemma lem7656985 (_98536 : int) : (term387 _98536) = (term379 _98536).
Proof. exact (TRANS (@lem7656882 _98536) (@lem7656984 _98536)). Qed.
Lemma lem7656986 (_98536 : int) : (term379 _98536) = term102.
Proof. exact (@lem1982719 (real_of_int _98536)). Qed.
Lemma lem7656987 (_98536 : int) : (term387 _98536) = term102.
Proof. exact (TRANS (@lem7656985 _98536) (@lem7656986 _98536)). Qed.
Lemma lem7656988 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7656989 (_98536 : int) : (term388 _98536) = term381.
Proof. exact (MK_COMB (@lem7656988) (@lem7656987 _98536)). Qed.
Lemma lem7656990 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem7656991 (_98536 : int) : (term386 _98536) = term389.
Proof. exact (MK_COMB (@lem7656989 _98536) (@lem7656990)). Qed.
Lemma lem7656992 (_98536 : int) : (term385 _98536) = term389.
Proof. exact (TRANS (@lem7656881 _98536) (@lem7656991 _98536)). Qed.
Lemma lem7656993 : term389 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem7656994 (_98536 : int) : (term385 _98536) = term166.
Proof. exact (TRANS (@lem7656992 _98536) (@lem7656993)). Qed.
Lemma lem7656995 (_98535 : int) : (term196 _98535) = (term196 _98535).
Proof. exact (eq_refl (term196 _98535)). Qed.
Lemma lem7656996 (_98536 : int) (_98535 : int) : (term766 _98535 _98536) = (term214 _98535).
Proof. exact (MK_COMB (@lem7656995 _98535) (@lem7656994 _98536)). Qed.
Lemma lem7656997 (_98536 : int) (_98535 : int) : (term765 _98535 _98536) = (term214 _98535).
Proof. exact (TRANS (@lem7656880 _98535 _98536) (@lem7656996 _98536 _98535)). Qed.
Lemma lem7656998 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7656999 (_98536 : int) (_98535 : int) : (term767 _98535 _98536) = (term768 _98535).
Proof. exact (MK_COMB (@lem7656998) (@lem7656997 _98536 _98535)). Qed.
Lemma lem7657000 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7657001 (_98536 : int) (_98535 : int) : (term764 _98535 _98536) = (term769 _98535).
Proof. exact (MK_COMB (@lem7656999 _98536 _98535) (@lem7657000)). Qed.
Lemma lem7657002 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term769 _98535.
Proof. exact (EQ_MP (@lem7657001 _98536 _98535) (@lem7656879 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7657004 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7657005 : term312 = term313.
Proof. exact (@lem7657004 term102 term116). Qed.
Lemma lem7657007 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7657008 : term116 = term205.
Proof. exact (@lem7657007 term117). Qed.
Lemma lem7657010 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7657011 : term102 = term163.
Proof. exact (@lem7657010 (NUMERAL 0)). Qed.
Lemma lem7657012 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7657013 : term314 = term315.
Proof. exact (MK_COMB (@lem7657012) (@lem7657011)). Qed.
Lemma lem7657014 : term313 = term316.
Proof. exact (MK_COMB (@lem7657013) (@lem7657008)). Qed.
Lemma lem7657015 : term317.
Proof. exact (@lem1980255 term102 term116 term116 term116). Qed.
Lemma lem7657017 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7657018 : term313 = term319.
Proof. exact (@lem7657017 (NUMERAL 0) term117). Qed.
Lemma lem7657019 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7657020 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7657021 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7657020 h1) (fun h1 : term319 = True => @lem7657019)). Qed.
Lemma lem7657022 : term319 = True.
Proof. exact (EQ_MP (@lem7657021) (@lem7657019)). Qed.
Lemma lem7657023 : term313 = True.
Proof. exact (TRANS (@lem7657018) (@lem7657022)). Qed.
Lemma lem7657024 : True = term313.
Proof. exact (SYM (@lem7657023)). Qed.
Lemma lem7657025 : term313.
Proof. exact (EQ_MP (@lem7657024) (@lem0)). Qed.
Lemma lem7657026 : term321.
Proof. exact (@lem7657015 (@lem7657025)). Qed.
Lemma lem7657028 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7657029 : term313 = term319.
Proof. exact (@lem7657028 (NUMERAL 0) term117). Qed.
Lemma lem7657030 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7657031 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7657032 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7657031 h1) (fun h1 : term319 = True => @lem7657030)). Qed.
Lemma lem7657033 : term319 = True.
Proof. exact (EQ_MP (@lem7657032) (@lem7657030)). Qed.
Lemma lem7657034 : term313 = True.
Proof. exact (TRANS (@lem7657029) (@lem7657033)). Qed.
Lemma lem7657035 : True = term313.
Proof. exact (SYM (@lem7657034)). Qed.
Lemma lem7657036 : term313.
Proof. exact (EQ_MP (@lem7657035) (@lem0)). Qed.
Lemma lem7657037 : term316 = term322.
Proof. exact (@lem7657026 (@lem7657036)). Qed.
Lemma lem7657039 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7657040 : term175 = term176.
Proof. exact (@lem7657039 term117 term117). Qed.
Lemma lem7657041 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7657042 : term178 = term117.
Proof. exact (EQ_MP (@lem7657041) (@lem940073)). Qed.
Lemma lem7657043 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7657044 : term176 = term116.
Proof. exact (MK_COMB (@lem7657043) (@lem7657042)). Qed.
Lemma lem7657045 : term175 = term116.
Proof. exact (TRANS (@lem7657040) (@lem7657044)). Qed.
Lemma lem7657047 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7657048 : term324 = term102.
Proof. exact (@lem7657047 term117). Qed.
Lemma lem7657049 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7657050 : term325 = term314.
Proof. exact (MK_COMB (@lem7657049) (@lem7657048)). Qed.
Lemma lem7657051 : term322 = term313.
Proof. exact (MK_COMB (@lem7657050) (@lem7657045)). Qed.
Lemma lem7657053 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7657054 : term313 = term319.
Proof. exact (@lem7657053 (NUMERAL 0) term117). Qed.
Lemma lem7657055 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7657056 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7657057 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7657056 h1) (fun h1 : term319 = True => @lem7657055)). Qed.
Lemma lem7657058 : term319 = True.
Proof. exact (EQ_MP (@lem7657057) (@lem7657055)). Qed.
Lemma lem7657059 : term313 = True.
Proof. exact (TRANS (@lem7657054) (@lem7657058)). Qed.
Lemma lem7657060 : term322 = True.
Proof. exact (TRANS (@lem7657051) (@lem7657059)). Qed.
Lemma lem7657061 : term316 = True.
Proof. exact (TRANS (@lem7657037) (@lem7657060)). Qed.
Lemma lem7657062 : term313 = True.
Proof. exact (TRANS (@lem7657014) (@lem7657061)). Qed.
Lemma lem7657063 : term312 = True.
Proof. exact (TRANS (@lem7657005) (@lem7657062)). Qed.
Lemma lem7657064 : True = term312.
Proof. exact (SYM (@lem7657063)). Qed.
Lemma lem7657065 : term312.
Proof. exact (EQ_MP (@lem7657064) (@lem0)). Qed.
Lemma lem7657066 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term770 _98535.
Proof. exact (conj (@lem7657065) (@lem7657002 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7657068 (x : real) (y : real) : term327 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7657069 (_98535 : int) : term771 _98535.
Proof. exact (@lem7657068 term116 (term214 _98535)). Qed.
Lemma lem7657070 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term772 _98535.
Proof. exact (@lem7657069 _98535 (@lem7657066 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7657071 (_98535 : int) : (term773 _98535) = (term214 _98535).
Proof. exact (@lem1982733 (term214 _98535)). Qed.
Lemma lem7657072 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7657073 (_98535 : int) : (term774 _98535) = (term768 _98535).
Proof. exact (MK_COMB (@lem7657072) (@lem7657071 _98535)). Qed.
Lemma lem7657074 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7657075 (_98535 : int) : (term772 _98535) = (term769 _98535).
Proof. exact (MK_COMB (@lem7657073 _98535) (@lem7657074)). Qed.
Lemma lem7657076 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term769 _98535.
Proof. exact (EQ_MP (@lem7657075 _98535) (@lem7657070 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7657077 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term775 _98535.
Proof. exact (conj (@lem7657076 _98534 _98537 _98535 _98536 h1) (@lem7656787 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7657079 (x : real) (y : real) : term429 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7657080 (_98535 : int) : term776 _98535.
Proof. exact (@lem7657079 (term214 _98535) (real_of_int _98535)). Qed.
Lemma lem7657081 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term777 _98535.
Proof. exact (@lem7657080 _98535 (@lem7657077 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7657082 (_98535 : int) : (term778 _98535) = (term386 _98535).
Proof. exact (@lem1982759 (term193 _98535) (real_of_int _98535) term166). Qed.
Lemma lem7657083 (_98535 : int) : (term387 _98535) = (term362 _98535).
Proof. exact (@lem1982713 term166 (real_of_int _98535)). Qed.
Lemma lem7657085 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7657086 : term116 = term205.
Proof. exact (@lem7657085 term117). Qed.
Lemma lem7657088 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7657089 : term166 = term167.
Proof. exact (@lem7657088 term117). Qed.
Lemma lem7657090 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7657091 : term363 = term364.
Proof. exact (MK_COMB (@lem7657090) (@lem7657089)). Qed.
Lemma lem7657092 : term365 = term366.
Proof. exact (MK_COMB (@lem7657091) (@lem7657086)). Qed.
Lemma lem7657093 : term367.
Proof. exact (@lem1981473 term166 term116 term116 term116 term102 term116). Qed.
Lemma lem7657095 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7657096 : term313 = term319.
Proof. exact (@lem7657095 (NUMERAL 0) term117). Qed.
Lemma lem7657097 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7657098 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7657099 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7657098 h1) (fun h1 : term319 = True => @lem7657097)). Qed.
Lemma lem7657100 : term319 = True.
Proof. exact (EQ_MP (@lem7657099) (@lem7657097)). Qed.
Lemma lem7657101 : term313 = True.
Proof. exact (TRANS (@lem7657096) (@lem7657100)). Qed.
Lemma lem7657102 : True = term313.
Proof. exact (SYM (@lem7657101)). Qed.
Lemma lem7657103 : term313.
Proof. exact (EQ_MP (@lem7657102) (@lem0)). Qed.
Lemma lem7657104 : term368.
Proof. exact (@lem7657093 (@lem7657103)). Qed.
Lemma lem7657106 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7657107 : term313 = term319.
Proof. exact (@lem7657106 (NUMERAL 0) term117). Qed.
Lemma lem7657108 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7657109 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7657110 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7657109 h1) (fun h1 : term319 = True => @lem7657108)). Qed.
Lemma lem7657111 : term319 = True.
Proof. exact (EQ_MP (@lem7657110) (@lem7657108)). Qed.
Lemma lem7657112 : term313 = True.
Proof. exact (TRANS (@lem7657107) (@lem7657111)). Qed.
Lemma lem7657113 : True = term313.
Proof. exact (SYM (@lem7657112)). Qed.
Lemma lem7657114 : term313.
Proof. exact (EQ_MP (@lem7657113) (@lem0)). Qed.
Lemma lem7657115 : term369.
Proof. exact (@lem7657104 (@lem7657114)). Qed.
Lemma lem7657117 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7657118 : term313 = term319.
Proof. exact (@lem7657117 (NUMERAL 0) term117). Qed.
Lemma lem7657119 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7657120 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7657121 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7657120 h1) (fun h1 : term319 = True => @lem7657119)). Qed.
Lemma lem7657122 : term319 = True.
Proof. exact (EQ_MP (@lem7657121) (@lem7657119)). Qed.
Lemma lem7657123 : term313 = True.
Proof. exact (TRANS (@lem7657118) (@lem7657122)). Qed.
Lemma lem7657124 : True = term313.
Proof. exact (SYM (@lem7657123)). Qed.
Lemma lem7657125 : term313.
Proof. exact (EQ_MP (@lem7657124) (@lem0)). Qed.
Lemma lem7657126 : term370.
Proof. exact (@lem7657115 (@lem7657125)). Qed.
Lemma lem7657128 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7657129 : term175 = term176.
Proof. exact (@lem7657128 term117 term117). Qed.
Lemma lem7657130 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7657131 : term178 = term117.
Proof. exact (EQ_MP (@lem7657130) (@lem940073)). Qed.
Lemma lem7657132 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7657133 : term176 = term116.
Proof. exact (MK_COMB (@lem7657132) (@lem7657131)). Qed.
Lemma lem7657134 : term175 = term116.
Proof. exact (TRANS (@lem7657129) (@lem7657133)). Qed.
Lemma lem7657136 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7657137 : term206 = term211.
Proof. exact (@lem7657136 term117 term117). Qed.
Lemma lem7657138 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7657139 : term178 = term117.
Proof. exact (EQ_MP (@lem7657138) (@lem940073)). Qed.
Lemma lem7657140 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7657141 : term176 = term116.
Proof. exact (MK_COMB (@lem7657140) (@lem7657139)). Qed.
Lemma lem7657142 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7657143 : term211 = term166.
Proof. exact (MK_COMB (@lem7657142) (@lem7657141)). Qed.
Lemma lem7657144 : term206 = term166.
Proof. exact (TRANS (@lem7657137) (@lem7657143)). Qed.
Lemma lem7657145 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7657146 : term371 = term363.
Proof. exact (MK_COMB (@lem7657145) (@lem7657144)). Qed.
Lemma lem7657147 : term372 = term365.
Proof. exact (MK_COMB (@lem7657146) (@lem7657134)). Qed.
Lemma lem7657149 (m : nat) : (term373 m) = term102.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7657150 : term365 = term102.
Proof. exact (@lem7657149 term117). Qed.
Lemma lem7657151 : term372 = term102.
Proof. exact (TRANS (@lem7657147) (@lem7657150)). Qed.
Lemma lem7657152 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7657153 : term374 = term375.
Proof. exact (MK_COMB (@lem7657152) (@lem7657151)). Qed.
Lemma lem7657154 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem7657155 : term376 = term324.
Proof. exact (MK_COMB (@lem7657153) (@lem7657154)). Qed.
Lemma lem7657157 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7657158 : term324 = term102.
Proof. exact (@lem7657157 term117). Qed.
Lemma lem7657159 : term376 = term102.
Proof. exact (TRANS (@lem7657155) (@lem7657158)). Qed.
Lemma lem7657161 (m : nat) (n : nat) : (term173 m n) = (term174 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7657162 : term175 = term176.
Proof. exact (@lem7657161 term117 term117). Qed.
Lemma lem7657163 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7657164 : term178 = term117.
Proof. exact (EQ_MP (@lem7657163) (@lem940073)). Qed.
Lemma lem7657165 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7657166 : term176 = term116.
Proof. exact (MK_COMB (@lem7657165) (@lem7657164)). Qed.
Lemma lem7657167 : term175 = term116.
Proof. exact (TRANS (@lem7657162) (@lem7657166)). Qed.
Lemma lem7657168 : term375 = term375.
Proof. exact (eq_refl term375). Qed.
Lemma lem7657169 : term377 = term324.
Proof. exact (MK_COMB (@lem7657168) (@lem7657167)). Qed.
Lemma lem7657171 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7657172 : term324 = term102.
Proof. exact (@lem7657171 term117). Qed.
Lemma lem7657173 : term377 = term102.
Proof. exact (TRANS (@lem7657169) (@lem7657172)). Qed.
Lemma lem7657174 : term102 = term377.
Proof. exact (SYM (@lem7657173)). Qed.
Lemma lem7657175 : term376 = term377.
Proof. exact (TRANS (@lem7657159) (@lem7657174)). Qed.
Lemma lem7657176 : term366 = term163.
Proof. exact (@lem7657126 (@lem7657175)). Qed.
Lemma lem7657177 : term365 = term163.
Proof. exact (TRANS (@lem7657092) (@lem7657176)). Qed.
Lemma lem7657179 (x : real) : (term182 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7657180 : term163 = term102.
Proof. exact (@lem7657179 term102). Qed.
Lemma lem7657181 : term365 = term102.
Proof. exact (TRANS (@lem7657177) (@lem7657180)). Qed.
Lemma lem7657182 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7657183 : term378 = term375.
Proof. exact (MK_COMB (@lem7657182) (@lem7657181)). Qed.
Lemma lem7657184 (_98535 : int) : (real_of_int _98535) = (real_of_int _98535).
Proof. exact (eq_refl (real_of_int _98535)). Qed.
Lemma lem7657185 (_98535 : int) : (term362 _98535) = (term379 _98535).
Proof. exact (MK_COMB (@lem7657183) (@lem7657184 _98535)). Qed.
Lemma lem7657186 (_98535 : int) : (term387 _98535) = (term379 _98535).
Proof. exact (TRANS (@lem7657083 _98535) (@lem7657185 _98535)). Qed.
Lemma lem7657187 (_98535 : int) : (term379 _98535) = term102.
Proof. exact (@lem1982719 (real_of_int _98535)). Qed.
Lemma lem7657188 (_98535 : int) : (term387 _98535) = term102.
Proof. exact (TRANS (@lem7657186 _98535) (@lem7657187 _98535)). Qed.
Lemma lem7657189 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7657190 (_98535 : int) : (term388 _98535) = term381.
Proof. exact (MK_COMB (@lem7657189) (@lem7657188 _98535)). Qed.
Lemma lem7657191 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem7657192 (_98535 : int) : (term386 _98535) = term389.
Proof. exact (MK_COMB (@lem7657190 _98535) (@lem7657191)). Qed.
Lemma lem7657193 (_98535 : int) : (term778 _98535) = term389.
Proof. exact (TRANS (@lem7657082 _98535) (@lem7657192 _98535)). Qed.
Lemma lem7657194 : term389 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem7657195 (_98535 : int) : (term778 _98535) = term166.
Proof. exact (TRANS (@lem7657193 _98535) (@lem7657194)). Qed.
Lemma lem7657196 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7657197 (_98535 : int) : (term779 _98535) = term391.
Proof. exact (MK_COMB (@lem7657196) (@lem7657195 _98535)). Qed.
Lemma lem7657198 : term102 = term102.
Proof. exact (eq_refl term102). Qed.
Lemma lem7657199 (_98535 : int) : (term777 _98535) = term392.
Proof. exact (MK_COMB (@lem7657197 _98535) (@lem7657198)). Qed.
Lemma lem7657200 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : term392.
Proof. exact (EQ_MP (@lem7657199 _98535) (@lem7657081 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7657202 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7657203 : term392 = term393.
Proof. exact (@lem7657202 term102 term166). Qed.
Lemma lem7657205 (x : nat) : (term164 x) = (term165 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7657206 : term166 = term167.
Proof. exact (@lem7657205 term117). Qed.
Lemma lem7657208 (x : nat) : (real_of_num x) = (term162 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7657209 : term102 = term163.
Proof. exact (@lem7657208 (NUMERAL 0)). Qed.
Lemma lem7657210 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7657211 : term104 = term394.
Proof. exact (MK_COMB (@lem7657210) (@lem7657209)). Qed.
Lemma lem7657212 : term393 = term395.
Proof. exact (MK_COMB (@lem7657211) (@lem7657206)). Qed.
Lemma lem7657213 : term396.
Proof. exact (@lem1980026 term102 term116 term166 term116). Qed.
Lemma lem7657215 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7657216 : term313 = term319.
Proof. exact (@lem7657215 (NUMERAL 0) term117). Qed.
Lemma lem7657217 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7657218 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7657219 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7657218 h1) (fun h1 : term319 = True => @lem7657217)). Qed.
Lemma lem7657220 : term319 = True.
Proof. exact (EQ_MP (@lem7657219) (@lem7657217)). Qed.
Lemma lem7657221 : term313 = True.
Proof. exact (TRANS (@lem7657216) (@lem7657220)). Qed.
Lemma lem7657222 : True = term313.
Proof. exact (SYM (@lem7657221)). Qed.
Lemma lem7657223 : term313.
Proof. exact (EQ_MP (@lem7657222) (@lem0)). Qed.
Lemma lem7657224 : term397.
Proof. exact (@lem7657213 (@lem7657223)). Qed.
Lemma lem7657226 (m : nat) (n : nat) : (term318 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7657227 : term313 = term319.
Proof. exact (@lem7657226 (NUMERAL 0) term117). Qed.
Lemma lem7657228 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7657229 (h1 : term320 = (BIT1 0)) : term319 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7657230 : (term320 = (BIT1 0)) = (term319 = True).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7657229 h1) (fun h1 : term319 = True => @lem7657228)). Qed.
Lemma lem7657231 : term319 = True.
Proof. exact (EQ_MP (@lem7657230) (@lem7657228)). Qed.
Lemma lem7657232 : term313 = True.
Proof. exact (TRANS (@lem7657227) (@lem7657231)). Qed.
Lemma lem7657233 : True = term313.
Proof. exact (SYM (@lem7657232)). Qed.
Lemma lem7657234 : term313.
Proof. exact (EQ_MP (@lem7657233) (@lem0)). Qed.
Lemma lem7657235 : term395 = term398.
Proof. exact (@lem7657224 (@lem7657234)). Qed.
Lemma lem7657237 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7657238 : term206 = term211.
Proof. exact (@lem7657237 term117 term117). Qed.
Lemma lem7657239 : (term177 = (BIT1 0)) = (term178 = term117).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7657240 : term178 = term117.
Proof. exact (EQ_MP (@lem7657239) (@lem940073)). Qed.
Lemma lem7657241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7657242 : term176 = term116.
Proof. exact (MK_COMB (@lem7657241) (@lem7657240)). Qed.
Lemma lem7657243 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7657244 : term211 = term166.
Proof. exact (MK_COMB (@lem7657243) (@lem7657242)). Qed.
Lemma lem7657245 : term206 = term166.
Proof. exact (TRANS (@lem7657238) (@lem7657244)). Qed.
Lemma lem7657247 (x : nat) : (term323 x) = term102.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7657248 : term324 = term102.
Proof. exact (@lem7657247 term117). Qed.
Lemma lem7657249 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7657250 : term399 = term104.
Proof. exact (MK_COMB (@lem7657249) (@lem7657248)). Qed.
Lemma lem7657251 : term398 = term393.
Proof. exact (MK_COMB (@lem7657250) (@lem7657245)). Qed.
Lemma lem7657253 (m : nat) (n : nat) : (term400 m n) = (term401 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7657254 : term393 = term402.
Proof. exact (@lem7657253 (NUMERAL 0) term117). Qed.
Lemma lem7657255 : term320 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7657256 (h1 : term320 = (BIT1 0)) : (term117 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7657257 : (term320 = (BIT1 0)) = ((term117 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term320 = (BIT1 0) => @lem7657256 h1) (fun h1 : (term117 = (NUMERAL 0)) = False => @lem7657255)). Qed.
Lemma lem7657258 : (term117 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7657257) (@lem7657255)). Qed.
Lemma lem7657259 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7657260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7657261 : term403 = (and True).
Proof. exact (MK_COMB (@lem7657260) (@lem7657259)). Qed.
Lemma lem7657262 : term402 = (True /\ False).
Proof. exact (MK_COMB (@lem7657261) (@lem7657258)). Qed.
Lemma lem7657264 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7657265 : term402 = False.
Proof. exact (TRANS (@lem7657262) (@lem7657264)). Qed.
Lemma lem7657266 : term393 = False.
Proof. exact (TRANS (@lem7657254) (@lem7657265)). Qed.
Lemma lem7657267 : term398 = False.
Proof. exact (TRANS (@lem7657251) (@lem7657266)). Qed.
Lemma lem7657268 : term395 = False.
Proof. exact (TRANS (@lem7657235) (@lem7657267)). Qed.
Lemma lem7657269 : term393 = False.
Proof. exact (TRANS (@lem7657212) (@lem7657268)). Qed.
Lemma lem7657270 : term392 = False.
Proof. exact (TRANS (@lem7657203) (@lem7657269)). Qed.
Lemma lem7657271 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term757 _98534 _98537 _98535 _98536) : False.
Proof. exact (EQ_MP (@lem7657270) (@lem7657200 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7657272 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term737 _98534 _98537 _98535 _98536) : False.
Proof. exact (or_elim (@lem7655903 _98534 _98537 _98535 _98536 h1) (fun h0 : term740 _98534 _98537 _98535 _98536 => @lem7656698 _98534 _98537 _98535 _98536 h0) (fun h0 : term757 _98534 _98537 _98535 _98536 => @lem7657271 _98534 _98537 _98535 _98536 h0)). Qed.
Lemma lem7657274 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term737 _98534 _98537 _98535 _98536) : term737 _98534 _98537 _98535 _98536.
Proof. exact (h1). Qed.
Lemma lem7657275 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term737 _98534 _98537 _98535 _98536) : (term737 _98534 _98537 _98535 _98536) = False.
Proof. exact (prop_ext (fun h2 : term737 _98534 _98537 _98535 _98536 => @lem7657272 _98534 _98537 _98535 _98536 h1) (fun h2 : False => @lem7657274 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7657276 (_98534 : int) (_98537 : int) (_98535 : int) (_98536 : int) (h1 : term737 _98534 _98537 _98535 _98536) : False.
Proof. exact (EQ_MP (@lem7657275 _98534 _98537 _98535 _98536 h1) (@lem7657274 _98534 _98537 _98535 _98536 h1)). Qed.
Lemma lem7657277 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) (h1 : term709 _98537 _98534 _98535 _98536) : term709 _98537 _98534 _98535 _98536.
Proof. exact (h1). Qed.
Lemma lem7657278 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) (h1 : term709 _98537 _98534 _98535 _98536) : term737 _98534 _98537 _98535 _98536.
Proof. exact (EQ_MP (@lem7655893 _98534 _98537 _98535 _98536) (@lem7657277 _98537 _98534 _98535 _98536 h1)). Qed.
Lemma lem7657279 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) (h1 : term709 _98537 _98534 _98535 _98536) : (term737 _98534 _98537 _98535 _98536) = False.
Proof. exact (prop_ext (fun h2 : term737 _98534 _98537 _98535 _98536 => @lem7657276 _98534 _98537 _98535 _98536 h2) (fun h2 : False => @lem7657278 _98537 _98534 _98535 _98536 h1)). Qed.
Lemma lem7657280 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) (h1 : term709 _98537 _98534 _98535 _98536) : False.
Proof. exact (EQ_MP (@lem7657279 _98537 _98534 _98535 _98536 h1) (@lem7657278 _98537 _98534 _98535 _98536 h1)). Qed.
Lemma lem7657281 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) : term780 _98537 _98534 _98535 _98536.
Proof. exact (fun h0 : term709 _98537 _98534 _98535 _98536 => @lem7657280 _98537 _98534 _98535 _98536 h0). Qed.
Lemma lem7657282 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) : term781 _98537 _98534 _98535 _98536.
Proof. exact (@lem1386578 (term782 _98537 _98534 _98535 _98536)). Qed.
Lemma lem7657285 (_98537 : int) (_98534 : int) (_98535 : int) (_98536 : int) : term782 _98537 _98534 _98535 _98536.
Proof. exact (@lem7657282 _98537 _98534 _98535 _98536 (@lem7657281 _98537 _98534 _98535 _98536)). Qed.
Lemma lem7657286 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term708 _98537 _98534 _98535 _98536) = (term697 _98537 _98534 _98536 _98535).
Proof. exact (SYM (@lem7655252 _98537 _98534 _98535 _98536)). Qed.
Lemma lem7657287 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7657288 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : (term782 _98537 _98534 _98535 _98536) = (term669 _98537 _98534 _98536 _98535).
Proof. exact (MK_COMB (@lem7657287) (@lem7657286 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7657289 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : term669 _98537 _98534 _98536 _98535.
Proof. exact (EQ_MP (@lem7657288 _98537 _98534 _98536 _98535) (@lem7657285 _98537 _98534 _98535 _98536)). Qed.
Lemma lem7657290 (_98537 : int) (_98534 : int) (_98536 : int) (_98535 : int) : term670 _98537 _98534 _98536 _98535.
Proof. exact (EQ_MP (@lem7654981 _98537 _98534 _98536 _98535) (@lem7657289 _98537 _98534 _98536 _98535)). Qed.
Lemma lem7657291 (i : nat) (a : nat) (d : nat) (b : nat) : term783 i a d b.
Proof. exact (@lem7657290 (int_of_num i) (int_of_num a) (int_of_num d) (int_of_num b)). Qed.
Lemma lem7657292 (i : nat) (a : nat) (d : nat) (b : nat) : term784 i a d b.
Proof. exact (@lem7657291 i a d b (@lem7654971 a)). Qed.
Lemma lem7657293 (i : nat) (a : nat) (d : nat) (b : nat) : term785 i a d b.
Proof. exact (@lem7657292 i a d b (@lem7654974 b)). Qed.
Lemma lem7657294 (i : nat) (a : nat) (d : nat) (b : nat) : term786 i a d b.
Proof. exact (@lem7657293 i a d b (@lem7654977 d)). Qed.
Lemma lem7657295 (i : nat) (a : nat) (d : nat) (b : nat) : term666 i a d b.
Proof. exact (@lem7657294 i a d b (@lem7654980 i)). Qed.
Lemma lem7657296 (i : nat) (a : nat) (b : nat) : term668 i a b.
Proof. exact (fun d : nat => @lem7657295 i a d b). Qed.
Lemma lem7657297 (i : nat) (a : nat) (b : nat) : (term668 i a b) = (term642 i a b).
Proof. exact (SYM (@lem7654968 i a b)). Qed.
Lemma lem7657298 (i : nat) (a : nat) (b : nat) : term642 i a b.
Proof. exact (EQ_MP (@lem7657297 i a b) (@lem7657296 i a b)). Qed.
Lemma lem7657299 {A B : Type'} (g : nat -> A) (i : nat) : term787 A B g i.
Proof. exact (@lem7622314 A B g i). Qed.
Lemma lem7657300 {A B : Type'} (g : nat -> A) (i : nat) : (term787 A B g i) = (term788 A B g i).
Proof. exact (eq_refl (term787 A B g i)). Qed.
Lemma lem7657301 {A B : Type'} (g : nat -> A) (i : nat) : term788 A B g i.
Proof. exact (EQ_MP (@lem7657300 A B g i) (@lem7657299 A B g i)). Qed.
Lemma lem7657302 {B : Type'} (i : nat) (h1 : term789 B i) : term789 B i.
Proof. exact (h1). Qed.
Lemma lem7657303 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term789 B i) : (term790 A B g i) = (g i).
Proof. exact (@lem7657301 A B g i (@lem7657302 B i h1)). Qed.
Lemma lem7657309 {A B : Type'} (x : cart A B) : term791 A B x.
Proof. exact (@lem7617066 A B x). Qed.
Lemma lem7657310 {A B : Type'} (x : cart A B) : (term791 A B x) = (term792 A B x).
Proof. exact (eq_refl (term791 A B x)). Qed.
Lemma lem7657311 {A B : Type'} (x : cart A B) : term792 A B x.
Proof. exact (EQ_MP (@lem7657310 A B x) (@lem7657309 A B x)). Qed.
Lemma lem7657312 {A B : Type'} (x : cart A B) (y : cart A B) : term793 A B x y.
Proof. exact (@lem7657311 A B x y). Qed.
Lemma lem7657313 {A B : Type'} (x : cart A B) (y : cart A B) : (term793 A B x y) = ((x = y) = (term794 A B x y)).
Proof. exact (eq_refl (term793 A B x y)). Qed.
Lemma lem7657315 {A M N : Type'} (f : type2 A M N) : term795 A M N f.
Proof. exact (@lem7635254 A M N f). Qed.
Lemma lem7657316 {A M N : Type'} (f : type2 A M N) : (term795 A M N f) = ((@sndcart A M N f) = (term796 A M N f)).
Proof. exact (eq_refl (term795 A M N f)). Qed.
Lemma lem7657318 {A M N : Type'} (f : type2 A M N) : term797 A M N f.
Proof. exact (@lem7633949 A M N f). Qed.
Lemma lem7657319 {A M N : Type'} (f : type2 A M N) : (term797 A M N f) = ((@fstcart A M N f) = (term798 A M N f)).
Proof. exact (eq_refl (term797 A M N f)). Qed.
Lemma lem7657321 {A M N : Type'} (f : cart A M) : term799 A M N f.
Proof. exact (@lem7632649 A M N f). Qed.
Lemma lem7657322 {A M N : Type'} (f : cart A M) : (term799 A M N f) = (term800 A M N f).
Proof. exact (eq_refl (term799 A M N f)). Qed.
Lemma lem7657323 {A M N : Type'} (f : cart A M) : term800 A M N f.
Proof. exact (EQ_MP (@lem7657322 A M N f) (@lem7657321 A M N f)). Qed.
Lemma lem7657324 {A M N : Type'} (f : cart A M) (g : cart A N) : term801 A M N f g.
Proof. exact (@lem7657323 A M N f g). Qed.
Lemma lem7657325 {A M N : Type'} (f : cart A M) (g : cart A N) : (term801 A M N f g) = ((@pastecart A M N f g) = (term802 A M N f g)).
Proof. exact (eq_refl (term801 A M N f g)). Qed.
Lemma lem7657334 {A B : Type'} (x : cart A B) (y : cart A B) : (x = y) = (term794 A B x y).
Proof. exact (EQ_MP (@lem7657313 A B x y) (@lem7657312 A B x y)). Qed.
Lemma lem7657335 {_140390 _140392 _140395 : Type'} (x : type4 _140390 _140392 _140395) (y : type4 _140390 _140392 _140395) : (x = y) = (term803 _140390 _140392 _140395 x y).
Proof. exact (@lem7657334 _140395 (finite_sum _140392 _140390) x y). Qed.
Lemma lem7657336 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : ((term804 _140390 _140392 _140395 z) = z) = (term805 _140390 _140392 _140395 z).
Proof. exact (@lem7657335 _140390 _140392 _140395 (term804 _140390 _140392 _140395 z) z). Qed.
Lemma lem7657344 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term806 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7657345 (p : Prop) (q : Prop) (p' : Prop) : term807 p q p'.
Proof. exact (fun q' : Prop => @lem7657344 p q p' q'). Qed.
Lemma lem7657346 (p : Prop) (q : Prop) : term808 p q.
Proof. exact (fun p' : Prop => @lem7657345 p q p'). Qed.
Lemma lem7657347 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term809 _140390 _140392 _140395 z i.
Proof. exact (@lem7657346 (term810 _140390 _140392 i) ((term811 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i))). Qed.
Lemma lem7657348 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (p' : Prop) : term812 _140390 _140392 _140395 z i p'.
Proof. exact (@lem7657347 _140390 _140392 _140395 z i p'). Qed.
Lemma lem7657349 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (p' : Prop) : (term812 _140390 _140392 _140395 z i p') = (term813 _140390 _140392 _140395 z i p').
Proof. exact (eq_refl (term812 _140390 _140392 _140395 z i p')). Qed.
Lemma lem7657350 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (p' : Prop) : term813 _140390 _140392 _140395 z i p'.
Proof. exact (EQ_MP (@lem7657349 _140390 _140392 _140395 z i p') (@lem7657348 _140390 _140392 _140395 z i p')). Qed.
Lemma lem7657351 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (p' : Prop) (q' : Prop) : term814 _140390 _140392 _140395 z i p' q'.
Proof. exact (@lem7657350 _140390 _140392 _140395 z i p' q'). Qed.
Lemma lem7657352 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (p' : Prop) (q' : Prop) : (term814 _140390 _140392 _140395 z i p' q') = (term815 _140390 _140392 _140395 z i p' q').
Proof. exact (eq_refl (term814 _140390 _140392 _140395 z i p' q')). Qed.
Lemma lem7657353 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (p' : Prop) (q' : Prop) : term815 _140390 _140392 _140395 z i p' q'.
Proof. exact (EQ_MP (@lem7657352 _140390 _140392 _140395 z i p' q') (@lem7657351 _140390 _140392 _140395 z i p' q')). Qed.
Lemma lem7657356 {_140390 _140392 : Type'} (i : nat) : (term810 _140390 _140392 i) = (term810 _140390 _140392 i).
Proof. exact (eq_refl (term810 _140390 _140392 i)). Qed.
Lemma lem7657357 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (q' : Prop) : term816 _140390 _140392 _140395 z i q'.
Proof. exact (@lem7657353 _140390 _140392 _140395 z i (term810 _140390 _140392 i) q'). Qed.
Lemma lem7657358 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (q' : Prop) : term817 _140390 _140392 _140395 z i q'.
Proof. exact (@lem7657357 _140390 _140392 _140395 z i q' (@lem7657356 _140390 _140392 i)). Qed.
Lemma lem7657359 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) : term810 _140390 _140392 i.
Proof. exact (h1). Qed.
Lemma lem7657360 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) : term818 _140390 _140392 i.
Proof. exact (proj2 (@lem7657359 _140390 _140392 i h1)). Qed.
Lemma lem7657361 {_140390 _140392 : Type'} (i : nat) : (term818 _140390 _140392 i) = ((term818 _140390 _140392 i) = True).
Proof. exact (@lem7 (term818 _140390 _140392 i)). Qed.
Lemma lem7657363 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) : term532 i.
Proof. exact (proj1 (@lem7657359 _140390 _140392 i h1)). Qed.
Lemma lem7657364 (i : nat) : (term532 i) = ((term532 i) = True).
Proof. exact (@lem7 (term532 i)). Qed.
Lemma lem7657371 {A M N : Type'} (f : cart A M) (g : cart A N) : (@pastecart A M N f g) = (term802 A M N f g).
Proof. exact (EQ_MP (@lem7657325 A M N f g) (@lem7657324 A M N f g)). Qed.
Lemma lem7657372 {_140390 _140392 _140395 : Type'} (f : cart _140395 _140392) (g : cart _140395 _140390) : (@pastecart _140395 _140392 _140390 f g) = (term819 _140390 _140392 _140395 f g).
Proof. exact (@lem7657371 _140395 _140392 _140390 f g). Qed.
Lemma lem7657373 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term804 _140390 _140392 _140395 z) = (term820 _140390 _140392 _140395 z).
Proof. exact (@lem7657372 _140390 _140392 _140395 (@fstcart _140395 _140392 _140390 z) (@sndcart _140395 _140392 _140390 z)). Qed.
Lemma lem7657522 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term821 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7657523 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term822 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7657522 _2963 g t e g' t' e'). Qed.
Lemma lem7657524 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term823 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7657523 _2963 g t e g' t'). Qed.
Lemma lem7657525 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term824 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7657524 _2963 g t e g'). Qed.
Lemma lem7657526 {_140395 : Type'} (g : Prop) (t : _140395) (e : _140395) : term824 _140395 g t e.
Proof. exact (@lem7657525 _140395 g t e). Qed.
Lemma lem7657527 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) : term825 _140390 _140392 _140395 z _98542.
Proof. exact (@lem7657526 _140395 (term826 _140392 _98542) (term827 _140390 _140392 _140395 z _98542) (term828 _140390 _140392 _140395 z _98542)). Qed.
Lemma lem7657528 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (g' : Prop) : term829 _140390 _140392 _140395 z _98542 g'.
Proof. exact (@lem7657527 _140390 _140392 _140395 z _98542 g'). Qed.
Lemma lem7657529 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (g' : Prop) : (term829 _140390 _140392 _140395 z _98542 g') = (term830 _140390 _140392 _140395 z _98542 g').
Proof. exact (eq_refl (term829 _140390 _140392 _140395 z _98542 g')). Qed.
Lemma lem7657530 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (g' : Prop) : term830 _140390 _140392 _140395 z _98542 g'.
Proof. exact (EQ_MP (@lem7657529 _140390 _140392 _140395 z _98542 g') (@lem7657528 _140390 _140392 _140395 z _98542 g')). Qed.
Lemma lem7657531 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (g' : Prop) (t' : _140395) : term831 _140390 _140392 _140395 z _98542 g' t'.
Proof. exact (@lem7657530 _140390 _140392 _140395 z _98542 g' t'). Qed.
Lemma lem7657532 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (g' : Prop) (t' : _140395) : (term831 _140390 _140392 _140395 z _98542 g' t') = (term832 _140390 _140392 _140395 z _98542 g' t').
Proof. exact (eq_refl (term831 _140390 _140392 _140395 z _98542 g' t')). Qed.
Lemma lem7657533 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (g' : Prop) (t' : _140395) : term832 _140390 _140392 _140395 z _98542 g' t'.
Proof. exact (EQ_MP (@lem7657532 _140390 _140392 _140395 z _98542 g' t') (@lem7657531 _140390 _140392 _140395 z _98542 g' t')). Qed.
Lemma lem7657534 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (g' : Prop) (t' : _140395) (e' : _140395) : term833 _140390 _140392 _140395 z _98542 g' t' e'.
Proof. exact (@lem7657533 _140390 _140392 _140395 z _98542 g' t' e'). Qed.
Lemma lem7657535 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (g' : Prop) (t' : _140395) (e' : _140395) : (term833 _140390 _140392 _140395 z _98542 g' t' e') = (term834 _140390 _140392 _140395 z _98542 g' t' e').
Proof. exact (eq_refl (term833 _140390 _140392 _140395 z _98542 g' t' e')). Qed.
Lemma lem7657536 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (g' : Prop) (t' : _140395) (e' : _140395) : term834 _140390 _140392 _140395 z _98542 g' t' e'.
Proof. exact (EQ_MP (@lem7657535 _140390 _140392 _140395 z _98542 g' t' e') (@lem7657534 _140390 _140392 _140395 z _98542 g' t' e')). Qed.
Lemma lem7657537 {_140392 : Type'} (_98542 : nat) : (term826 _140392 _98542) = (term826 _140392 _98542).
Proof. exact (eq_refl (term826 _140392 _98542)). Qed.
Lemma lem7657538 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (t' : _140395) (e' : _140395) : term835 _140390 _140392 _140395 z _98542 t' e'.
Proof. exact (@lem7657536 _140390 _140392 _140395 z _98542 (term826 _140392 _98542) t' e'). Qed.
Lemma lem7657539 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (t' : _140395) (e' : _140395) : term836 _140390 _140392 _140395 z _98542 t' e'.
Proof. exact (@lem7657538 _140390 _140392 _140395 z _98542 t' e' (@lem7657537 _140392 _98542)). Qed.
Lemma lem7657544 {A M N : Type'} (f : type2 A M N) : (@fstcart A M N f) = (term798 A M N f).
Proof. exact (EQ_MP (@lem7657319 A M N f) (@lem7657318 A M N f)). Qed.
Lemma lem7657545 {_140390 _140392 _140395 : Type'} (f : type4 _140390 _140392 _140395) : (@fstcart _140395 _140392 _140390 f) = (term837 _140390 _140392 _140395 f).
Proof. exact (@lem7657544 _140395 _140392 _140390 f). Qed.
Lemma lem7657546 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (@fstcart _140395 _140392 _140390 z) = (term837 _140390 _140392 _140395 z).
Proof. exact (@lem7657545 _140390 _140392 _140395 z). Qed.
Lemma lem7657547 {_140392 _140395 : Type'} : (@dollar _140395 _140392) = (@dollar _140395 _140392).
Proof. exact (eq_refl (@dollar _140395 _140392)). Qed.
Lemma lem7657548 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term838 _140390 _140392 _140395 z) = (term839 _140390 _140392 _140395 z).
Proof. exact (MK_COMB (@lem7657547 _140392 _140395) (@lem7657546 _140390 _140392 _140395 z)). Qed.
Lemma lem7657549 (_98542 : nat) : _98542 = _98542.
Proof. exact (eq_refl _98542). Qed.
Lemma lem7657550 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) : (term827 _140390 _140392 _140395 z _98542) = (term840 _140390 _140392 _140395 z _98542).
Proof. exact (MK_COMB (@lem7657548 _140390 _140392 _140395 z) (@lem7657549 _98542)). Qed.
Lemma lem7657566 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) : term841 _140390 _140392 _140395 z _98542.
Proof. exact (fun h0 : term826 _140392 _98542 => @lem7657550 _140390 _140392 _140395 z _98542). Qed.
Lemma lem7657567 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (e' : _140395) : term842 _140390 _140392 _140395 z _98542 e'.
Proof. exact (@lem7657539 _140390 _140392 _140395 z _98542 (term840 _140390 _140392 _140395 z _98542) e'). Qed.
Lemma lem7657568 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) (e' : _140395) : term843 _140390 _140392 _140395 z _98542 e'.
Proof. exact (@lem7657567 _140390 _140392 _140395 z _98542 e' (@lem7657566 _140390 _140392 _140395 z _98542)). Qed.
Lemma lem7657573 {A M N : Type'} (f : type2 A M N) : (@sndcart A M N f) = (term796 A M N f).
Proof. exact (EQ_MP (@lem7657316 A M N f) (@lem7657315 A M N f)). Qed.
Lemma lem7657574 {_140390 _140392 _140395 : Type'} (f : type4 _140390 _140392 _140395) : (@sndcart _140395 _140392 _140390 f) = (term844 _140390 _140392 _140395 f).
Proof. exact (@lem7657573 _140395 _140392 _140390 f). Qed.
Lemma lem7657575 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (@sndcart _140395 _140392 _140390 z) = (term844 _140390 _140392 _140395 z).
Proof. exact (@lem7657574 _140390 _140392 _140395 z). Qed.
Lemma lem7657576 {_140390 _140395 : Type'} : (@dollar _140395 _140390) = (@dollar _140395 _140390).
Proof. exact (eq_refl (@dollar _140395 _140390)). Qed.
Lemma lem7657577 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term845 _140390 _140392 _140395 z) = (term846 _140390 _140392 _140395 z).
Proof. exact (MK_COMB (@lem7657576 _140390 _140395) (@lem7657575 _140390 _140392 _140395 z)). Qed.
Lemma lem7657578 {_140392 : Type'} (_98542 : nat) : (term847 _140392 _98542) = (term847 _140392 _98542).
Proof. exact (eq_refl (term847 _140392 _98542)). Qed.
Lemma lem7657579 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) : (term828 _140390 _140392 _140395 z _98542) = (term848 _140390 _140392 _140395 z _98542).
Proof. exact (MK_COMB (@lem7657577 _140390 _140392 _140395 z) (@lem7657578 _140392 _98542)). Qed.
Lemma lem7657588 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) : term849 _140390 _140392 _140395 z _98542.
Proof. exact (fun h0 : term850 _140392 _98542 => @lem7657579 _140390 _140392 _140395 z _98542). Qed.
Lemma lem7657589 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) : term851 _140390 _140392 _140395 z _98542.
Proof. exact (@lem7657568 _140390 _140392 _140395 z _98542 (term848 _140390 _140392 _140395 z _98542)). Qed.
Lemma lem7657590 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (_98542 : nat) : (term852 _140390 _140392 _140395 z _98542) = (term853 _140390 _140392 _140395 z _98542).
Proof. exact (@lem7657589 _140390 _140392 _140395 z _98542 (@lem7657588 _140390 _140392 _140395 z _98542)). Qed.
Lemma lem7657665 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term854 _140390 _140392 _140395 z) = (term855 _140390 _140392 _140395 z).
Proof. exact (fun_ext (fun _98542 : nat => @lem7657590 _140390 _140392 _140395 z _98542)). Qed.
Lemma lem7657869 {_140390 _140392 _140395 : Type'} : (@lambda _140395 (finite_sum _140392 _140390)) = (@lambda _140395 (finite_sum _140392 _140390)).
Proof. exact (eq_refl (@lambda _140395 (finite_sum _140392 _140390))). Qed.
Lemma lem7657870 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term820 _140390 _140392 _140395 z) = (term856 _140390 _140392 _140395 z).
Proof. exact (MK_COMB (@lem7657869 _140390 _140392 _140395) (@lem7657665 _140390 _140392 _140395 z)). Qed.
Lemma lem7658074 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term804 _140390 _140392 _140395 z) = (term856 _140390 _140392 _140395 z).
Proof. exact (TRANS (@lem7657373 _140390 _140392 _140395 z) (@lem7657870 _140390 _140392 _140395 z)). Qed.
Lemma lem7658075 {_140390 _140392 _140395 : Type'} : (@dollar _140395 (finite_sum _140392 _140390)) = (@dollar _140395 (finite_sum _140392 _140390)).
Proof. exact (eq_refl (@dollar _140395 (finite_sum _140392 _140390))). Qed.
Lemma lem7658076 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term857 _140390 _140392 _140395 z) = (term858 _140390 _140392 _140395 z).
Proof. exact (MK_COMB (@lem7658075 _140390 _140392 _140395) (@lem7658074 _140390 _140392 _140395 z)). Qed.
Lemma lem7658280 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7658281 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term811 _140390 _140392 _140395 z i) = (term859 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7658076 _140390 _140392 _140395 z) (@lem7658280 i)). Qed.
Lemma lem7658283 {A B : Type'} (g : nat -> A) (i : nat) : term788 A B g i.
Proof. exact (fun h0 : term789 B i => @lem7657303 A B g i h0). Qed.
Lemma lem7658284 {_140390 _140392 _140395 : Type'} (g : nat -> _140395) (i : nat) : term860 _140390 _140392 _140395 g i.
Proof. exact (@lem7658283 _140395 (finite_sum _140392 _140390) g i). Qed.
Lemma lem7658285 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term861 _140390 _140392 _140395 z i.
Proof. exact (@lem7658284 _140390 _140392 _140395 (term855 _140390 _140392 _140395 z) i). Qed.
Lemma lem7658289 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) : (term532 i) = True.
Proof. exact (EQ_MP (@lem7657364 i) (@lem7657363 _140390 _140392 i h1)). Qed.
Lemma lem7658290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7658291 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) : (term862 i) = (and True).
Proof. exact (MK_COMB (@lem7658290) (@lem7658289 _140390 _140392 i h1)). Qed.
Lemma lem7658293 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) : (term818 _140390 _140392 i) = True.
Proof. exact (EQ_MP (@lem7657361 _140390 _140392 i) (@lem7657360 _140390 _140392 i h1)). Qed.
Lemma lem7658294 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) : (term810 _140390 _140392 i) = (True /\ True).
Proof. exact (MK_COMB (@lem7658291 _140390 _140392 i h1) (@lem7658293 _140390 _140392 i h1)). Qed.
Lemma lem7658296 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7658297 : (True /\ True) = True.
Proof. exact (@lem7658296 True). Qed.
Lemma lem7658298 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) : (term810 _140390 _140392 i) = True.
Proof. exact (TRANS (@lem7658294 _140390 _140392 i h1) (@lem7658297)). Qed.
Lemma lem7658299 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) : True = (term810 _140390 _140392 i).
Proof. exact (SYM (@lem7658298 _140390 _140392 i h1)). Qed.
Lemma lem7658300 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) : term810 _140390 _140392 i.
Proof. exact (EQ_MP (@lem7658299 _140390 _140392 i h1) (@lem0)). Qed.
Lemma lem7658301 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term810 _140390 _140392 i) : (term859 _140390 _140392 _140395 z i) = (term863 _140390 _140392 _140395 z i).
Proof. exact (@lem7658285 _140390 _140392 _140395 z i (@lem7658300 _140390 _140392 i h1)). Qed.
Lemma lem7658303 {A B : Type'} (f : A -> B) (y : A) : (term864 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7658304 {_140395 : Type'} (f : nat -> _140395) (y : nat) : (term865 _140395 f y) = (f y).
Proof. exact (@lem7658303 nat _140395 f y). Qed.
Lemma lem7658305 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term866 _140390 _140392 _140395 z i) = (term863 _140390 _140392 _140395 z i).
Proof. exact (@lem7658304 _140395 (term855 _140390 _140392 _140395 z) i). Qed.
Lemma lem7658306 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term863 _140390 _140392 _140395 z i) = (term853 _140390 _140392 _140395 z i).
Proof. exact (eq_refl (term863 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658307 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term867 _140390 _140392 _140395 z) = (term855 _140390 _140392 _140395 z).
Proof. exact (fun_ext (fun i : nat => @lem7658306 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658308 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7658309 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term866 _140390 _140392 _140395 z i) = (term863 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7658307 _140390 _140392 _140395 z) (@lem7658308 i)). Qed.
Lemma lem7658310 {_140395 : Type'} : (@eq _140395) = (@eq _140395).
Proof. exact (eq_refl (@eq _140395)). Qed.
Lemma lem7658311 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term868 _140390 _140392 _140395 z i) = (term869 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7658310 _140395) (@lem7658309 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658312 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term863 _140390 _140392 _140395 z i) = (term853 _140390 _140392 _140395 z i).
Proof. exact (eq_refl (term863 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658313 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : ((term866 _140390 _140392 _140395 z i) = (term863 _140390 _140392 _140395 z i)) = ((term863 _140390 _140392 _140395 z i) = (term853 _140390 _140392 _140395 z i)).
Proof. exact (MK_COMB (@lem7658311 _140390 _140392 _140395 z i) (@lem7658312 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658314 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term863 _140390 _140392 _140395 z i) = (term853 _140390 _140392 _140395 z i).
Proof. exact (EQ_MP (@lem7658313 _140390 _140392 _140395 z i) (@lem7658305 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658316 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term821 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7658317 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term822 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7658316 _2963 g t e g' t' e'). Qed.
Lemma lem7658318 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term823 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7658317 _2963 g t e g' t'). Qed.
Lemma lem7658319 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term824 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7658318 _2963 g t e g'). Qed.
Lemma lem7658320 {_140395 : Type'} (g : Prop) (t : _140395) (e : _140395) : term824 _140395 g t e.
Proof. exact (@lem7658319 _140395 g t e). Qed.
Lemma lem7658321 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term870 _140390 _140392 _140395 z i.
Proof. exact (@lem7658320 _140395 (term826 _140392 i) (term840 _140390 _140392 _140395 z i) (term848 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658322 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (g' : Prop) : term871 _140390 _140392 _140395 z i g'.
Proof. exact (@lem7658321 _140390 _140392 _140395 z i g'). Qed.
Lemma lem7658323 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (g' : Prop) : (term871 _140390 _140392 _140395 z i g') = (term872 _140390 _140392 _140395 z i g').
Proof. exact (eq_refl (term871 _140390 _140392 _140395 z i g')). Qed.
Lemma lem7658324 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (g' : Prop) : term872 _140390 _140392 _140395 z i g'.
Proof. exact (EQ_MP (@lem7658323 _140390 _140392 _140395 z i g') (@lem7658322 _140390 _140392 _140395 z i g')). Qed.
Lemma lem7658325 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (g' : Prop) (t' : _140395) : term873 _140390 _140392 _140395 z i g' t'.
Proof. exact (@lem7658324 _140390 _140392 _140395 z i g' t'). Qed.
Lemma lem7658326 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (g' : Prop) (t' : _140395) : (term873 _140390 _140392 _140395 z i g' t') = (term874 _140390 _140392 _140395 z i g' t').
Proof. exact (eq_refl (term873 _140390 _140392 _140395 z i g' t')). Qed.
Lemma lem7658327 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (g' : Prop) (t' : _140395) : term874 _140390 _140392 _140395 z i g' t'.
Proof. exact (EQ_MP (@lem7658326 _140390 _140392 _140395 z i g' t') (@lem7658325 _140390 _140392 _140395 z i g' t')). Qed.
Lemma lem7658328 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (g' : Prop) (t' : _140395) (e' : _140395) : term875 _140390 _140392 _140395 z i g' t' e'.
Proof. exact (@lem7658327 _140390 _140392 _140395 z i g' t' e'). Qed.
Lemma lem7658329 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (g' : Prop) (t' : _140395) (e' : _140395) : (term875 _140390 _140392 _140395 z i g' t' e') = (term876 _140390 _140392 _140395 z i g' t' e').
Proof. exact (eq_refl (term875 _140390 _140392 _140395 z i g' t' e')). Qed.
Lemma lem7658330 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (g' : Prop) (t' : _140395) (e' : _140395) : term876 _140390 _140392 _140395 z i g' t' e'.
Proof. exact (EQ_MP (@lem7658329 _140390 _140392 _140395 z i g' t' e') (@lem7658328 _140390 _140392 _140395 z i g' t' e')). Qed.
Lemma lem7658333 {_140392 : Type'} (i : nat) : (term826 _140392 i) = (term826 _140392 i).
Proof. exact (eq_refl (term826 _140392 i)). Qed.
Lemma lem7658334 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (t' : _140395) (e' : _140395) : term877 _140390 _140392 _140395 z i t' e'.
Proof. exact (@lem7658330 _140390 _140392 _140395 z i (term826 _140392 i) t' e'). Qed.
Lemma lem7658335 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (t' : _140395) (e' : _140395) : term878 _140390 _140392 _140395 z i t' e'.
Proof. exact (@lem7658334 _140390 _140392 _140395 z i t' e' (@lem7658333 _140392 i)). Qed.
Lemma lem7658336 {_140392 : Type'} (i : nat) (h1 : term826 _140392 i) : term826 _140392 i.
Proof. exact (h1). Qed.
Lemma lem7658337 {_140392 : Type'} (i : nat) : (term826 _140392 i) = ((term826 _140392 i) = True).
Proof. exact (@lem7 (term826 _140392 i)). Qed.
Lemma lem7658340 {A B : Type'} (g : nat -> A) (i : nat) : term788 A B g i.
Proof. exact (fun h0 : term789 B i => @lem7657303 A B g i h0). Qed.
Lemma lem7658341 {_140392 _140395 : Type'} (g : nat -> _140395) (i : nat) : term879 _140392 _140395 g i.
Proof. exact (@lem7658340 _140395 _140392 g i). Qed.
Lemma lem7658342 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term880 _140390 _140392 _140395 z i.
Proof. exact (@lem7658341 _140392 _140395 (term881 _140390 _140392 _140395 z) i). Qed.
Lemma lem7658346 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) : (term532 i) = True.
Proof. exact (EQ_MP (@lem7657364 i) (@lem7657363 _140390 _140392 i h1)). Qed.
Lemma lem7658347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7658348 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) : (term862 i) = (and True).
Proof. exact (MK_COMB (@lem7658347) (@lem7658346 _140390 _140392 i h1)). Qed.
Lemma lem7658352 {_140392 : Type'} (i : nat) (h1 : term826 _140392 i) : (term826 _140392 i) = True.
Proof. exact (EQ_MP (@lem7658337 _140392 i) (@lem7658336 _140392 i h1)). Qed.
Lemma lem7658353 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) (h2 : term826 _140392 i) : (term789 _140392 i) = (True /\ True).
Proof. exact (MK_COMB (@lem7658348 _140390 _140392 i h1) (@lem7658352 _140392 i h2)). Qed.
Lemma lem7658355 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7658356 : (True /\ True) = True.
Proof. exact (@lem7658355 True). Qed.
Lemma lem7658357 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) (h2 : term826 _140392 i) : (term789 _140392 i) = True.
Proof. exact (TRANS (@lem7658353 _140390 _140392 i h1 h2) (@lem7658356)). Qed.
Lemma lem7658358 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) (h2 : term826 _140392 i) : True = (term789 _140392 i).
Proof. exact (SYM (@lem7658357 _140390 _140392 i h1 h2)). Qed.
Lemma lem7658359 {_140390 _140392 : Type'} (i : nat) (h1 : term810 _140390 _140392 i) (h2 : term826 _140392 i) : term789 _140392 i.
Proof. exact (EQ_MP (@lem7658358 _140390 _140392 i h1 h2) (@lem0)). Qed.
Lemma lem7658360 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term810 _140390 _140392 i) (h2 : term826 _140392 i) : (term840 _140390 _140392 _140395 z i) = (term882 _140390 _140392 _140395 z i).
Proof. exact (@lem7658342 _140390 _140392 _140395 z i (@lem7658359 _140390 _140392 i h1 h2)). Qed.
Lemma lem7658362 {A B : Type'} (f : A -> B) (y : A) : (term864 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7658363 {_140395 : Type'} (f : nat -> _140395) (y : nat) : (term865 _140395 f y) = (f y).
Proof. exact (@lem7658362 nat _140395 f y). Qed.
Lemma lem7658364 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term883 _140390 _140392 _140395 z i) = (term882 _140390 _140392 _140395 z i).
Proof. exact (@lem7658363 _140395 (term881 _140390 _140392 _140395 z) i). Qed.
Lemma lem7658365 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term882 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i).
Proof. exact (eq_refl (term882 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658366 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term884 _140390 _140392 _140395 z) = (term881 _140390 _140392 _140395 z).
Proof. exact (fun_ext (fun i : nat => @lem7658365 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658367 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7658368 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term883 _140390 _140392 _140395 z i) = (term882 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7658366 _140390 _140392 _140395 z) (@lem7658367 i)). Qed.
Lemma lem7658369 {_140395 : Type'} : (@eq _140395) = (@eq _140395).
Proof. exact (eq_refl (@eq _140395)). Qed.
Lemma lem7658370 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term885 _140390 _140392 _140395 z i) = (term886 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7658369 _140395) (@lem7658368 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658371 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term882 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i).
Proof. exact (eq_refl (term882 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658372 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : ((term883 _140390 _140392 _140395 z i) = (term882 _140390 _140392 _140395 z i)) = ((term882 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i)).
Proof. exact (MK_COMB (@lem7658370 _140390 _140392 _140395 z i) (@lem7658371 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658373 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term882 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i).
Proof. exact (EQ_MP (@lem7658372 _140390 _140392 _140395 z i) (@lem7658364 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658374 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term810 _140390 _140392 i) (h2 : term826 _140392 i) : (term840 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i).
Proof. exact (TRANS (@lem7658360 _140390 _140392 _140395 z i h1 h2) (@lem7658373 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658375 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term810 _140390 _140392 i) : term887 _140390 _140392 _140395 z i.
Proof. exact (fun h0 : term826 _140392 i => @lem7658374 _140390 _140392 _140395 z i h1 h0). Qed.
Lemma lem7658376 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (e' : _140395) : term888 _140390 _140392 _140395 z i e'.
Proof. exact (@lem7658335 _140390 _140392 _140395 z i (@dollar _140395 (finite_sum _140392 _140390) z i) e'). Qed.
Lemma lem7658377 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (e' : _140395) (i : nat) (h1 : term810 _140390 _140392 i) : term889 _140390 _140392 _140395 z i e'.
Proof. exact (@lem7658376 _140390 _140392 _140395 z i e' (@lem7658375 _140390 _140392 _140395 z i h1)). Qed.
Lemma lem7658389 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term848 _140390 _140392 _140395 z i) = (term848 _140390 _140392 _140395 z i).
Proof. exact (eq_refl (term848 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658390 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term890 _140390 _140392 _140395 z i.
Proof. exact (fun h0 : term850 _140392 i => @lem7658389 _140390 _140392 _140395 z i). Qed.
Lemma lem7658391 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term810 _140390 _140392 i) : term891 _140390 _140392 _140395 z i.
Proof. exact (@lem7658377 _140390 _140392 _140395 z (term848 _140390 _140392 _140395 z i) i h1). Qed.
Lemma lem7658392 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term810 _140390 _140392 i) : (term853 _140390 _140392 _140395 z i) = (term892 _140390 _140392 _140395 z i).
Proof. exact (@lem7658391 _140390 _140392 _140395 z i h1 (@lem7658390 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658446 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term810 _140390 _140392 i) : (term863 _140390 _140392 _140395 z i) = (term892 _140390 _140392 _140395 z i).
Proof. exact (TRANS (@lem7658314 _140390 _140392 _140395 z i) (@lem7658392 _140390 _140392 _140395 z i h1)). Qed.
Lemma lem7658447 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term810 _140390 _140392 i) : (term859 _140390 _140392 _140395 z i) = (term892 _140390 _140392 _140395 z i).
Proof. exact (TRANS (@lem7658301 _140390 _140392 _140395 z i h1) (@lem7658446 _140390 _140392 _140395 z i h1)). Qed.
Lemma lem7658448 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term810 _140390 _140392 i) : (term811 _140390 _140392 _140395 z i) = (term892 _140390 _140392 _140395 z i).
Proof. exact (TRANS (@lem7658281 _140390 _140392 _140395 z i) (@lem7658447 _140390 _140392 _140395 z i h1)). Qed.
Lemma lem7658449 {_140395 : Type'} : (@eq _140395) = (@eq _140395).
Proof. exact (eq_refl (@eq _140395)). Qed.
Lemma lem7658450 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term810 _140390 _140392 i) : (term893 _140390 _140392 _140395 z i) = (term894 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7658449 _140395) (@lem7658448 _140390 _140392 _140395 z i h1)). Qed.
Lemma lem7658504 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (@dollar _140395 (finite_sum _140392 _140390) z i) = (@dollar _140395 (finite_sum _140392 _140390) z i).
Proof. exact (eq_refl (@dollar _140395 (finite_sum _140392 _140390) z i)). Qed.
Lemma lem7658505 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term810 _140390 _140392 i) : ((term811 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i)) = ((term892 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i)).
Proof. exact (MK_COMB (@lem7658450 _140390 _140392 _140395 z i h1) (@lem7658504 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658563 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term895 _140390 _140392 _140395 z i.
Proof. exact (fun h0 : term810 _140390 _140392 i => @lem7658505 _140390 _140392 _140395 z i h0). Qed.
Lemma lem7658564 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term896 _140390 _140392 _140395 z i.
Proof. exact (@lem7657358 _140390 _140392 _140395 z i ((term892 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i))). Qed.
Lemma lem7658565 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term897 _140390 _140392 _140395 z i) = (term898 _140390 _140392 _140395 z i).
Proof. exact (@lem7658564 _140390 _140392 _140395 z i (@lem7658563 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658707 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term899 _140390 _140392 _140395 z) = (term900 _140390 _140392 _140395 z).
Proof. exact (fun_ext (fun i : nat => @lem7658565 _140390 _140392 _140395 z i)). Qed.
Lemma lem7658849 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7658850 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term805 _140390 _140392 _140395 z) = (term901 _140390 _140392 _140395 z).
Proof. exact (MK_COMB (@lem7658849) (@lem7658707 _140390 _140392 _140395 z)). Qed.
Lemma lem7658996 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : ((term804 _140390 _140392 _140395 z) = z) = (term901 _140390 _140392 _140395 z).
Proof. exact (TRANS (@lem7657336 _140390 _140392 _140395 z) (@lem7658850 _140390 _140392 _140395 z)). Qed.
Lemma lem7658997 {_140390 _140392 _140395 : Type'} : (term902 _140390 _140392 _140395) = (term903 _140390 _140392 _140395).
Proof. exact (fun_ext (fun z : type4 _140390 _140392 _140395 => @lem7658996 _140390 _140392 _140395 z)). Qed.
Lemma lem7659143 {_140390 _140392 _140395 : Type'} : (@all (cart _140395 (finite_sum _140392 _140390))) = (@all (cart _140395 (finite_sum _140392 _140390))).
Proof. exact (eq_refl (@all (cart _140395 (finite_sum _140392 _140390)))). Qed.
Lemma lem7659144 {_140390 _140392 _140395 : Type'} : (term904 _140390 _140392 _140395) = (term905 _140390 _140392 _140395).
Proof. exact (MK_COMB (@lem7659143 _140390 _140392 _140395) (@lem7658997 _140390 _140392 _140395)). Qed.
Lemma lem7659294 {_140390 _140392 _140395 : Type'} : (term905 _140390 _140392 _140395) = (term904 _140390 _140392 _140395).
Proof. exact (SYM (@lem7659144 _140390 _140392 _140395)). Qed.
Lemma lem7659295 {_140395 : Type'} (_474 : _140395) (_475 : Prop) (_476 : _140395 -> Prop) (_477 : _140395) : (term906 _140395 _476 _475 _474 _477) = (term907 _140395 _474 _475 _476 _477).
Proof. exact (@lem13473 _140395 _474 _475 _476 _477). Qed.
Lemma lem7659296 {_140390 _140392 _140395 : Type'} (_474 : _140395) (_475 : Prop) (z : type4 _140390 _140392 _140395) (i : nat) (_477 : _140395) : (term908 _140390 _140392 _140395 z i _475 _474 _477) = (term909 _140390 _140392 _140395 _474 _475 z i _477).
Proof. exact (@lem7659295 _140395 _474 _475 (term910 _140390 _140392 _140395 z i) _477). Qed.
Lemma lem7659297 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term911 _140390 _140392 _140395 z i) = (term912 _140390 _140392 _140395 z i).
Proof. exact (@lem7659296 _140390 _140392 _140395 (@dollar _140395 (finite_sum _140392 _140390) z i) (term826 _140392 i) z i (term848 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659298 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term913 _140390 _140392 _140395 z i) = (term914 _140390 _140392 _140395 z i).
Proof. exact (eq_refl (term913 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659299 {_140392 : Type'} (i : nat) : (term915 _140392 i) = (term915 _140392 i).
Proof. exact (eq_refl (term915 _140392 i)). Qed.
Lemma lem7659300 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term916 _140390 _140392 _140395 z i) = (term917 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7659299 _140392 i) (@lem7659298 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659301 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term918 _140390 _140392 _140395 z i) = (term919 _140390 _140392 _140395 z i).
Proof. exact (eq_refl (term918 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659302 {_140392 : Type'} (i : nat) : (term920 _140392 i) = (term920 _140392 i).
Proof. exact (eq_refl (term920 _140392 i)). Qed.
Lemma lem7659303 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term921 _140390 _140392 _140395 z i) = (term922 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7659302 _140392 i) (@lem7659301 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7659305 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term923 _140390 _140392 _140395 z i) = (term924 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7659304) (@lem7659303 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659306 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term912 _140390 _140392 _140395 z i) = (term925 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7659305 _140390 _140392 _140395 z i) (@lem7659300 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659307 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term911 _140390 _140392 _140395 z i) = (term898 _140390 _140392 _140395 z i).
Proof. exact (eq_refl (term911 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7659309 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term926 _140390 _140392 _140395 z i) = (term927 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7659308) (@lem7659307 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659310 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : ((term911 _140390 _140392 _140395 z i) = (term912 _140390 _140392 _140395 z i)) = ((term898 _140390 _140392 _140395 z i) = (term925 _140390 _140392 _140395 z i)).
Proof. exact (MK_COMB (@lem7659309 _140390 _140392 _140395 z i) (@lem7659306 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659311 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term898 _140390 _140392 _140395 z i) = (term925 _140390 _140392 _140395 z i).
Proof. exact (EQ_MP (@lem7659310 _140390 _140392 _140395 z i) (@lem7659297 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659312 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term925 _140390 _140392 _140395 z i) = (term898 _140390 _140392 _140395 z i).
Proof. exact (SYM (@lem7659311 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659330 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : term850 _140392 i.
Proof. exact (h1). Qed.
Lemma lem7659357 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7659358 {_140395 : Type'} (x : _140395) : (x = x) = True.
Proof. exact (@lem7659357 _140395 x). Qed.
Lemma lem7659359 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : ((@dollar _140395 (finite_sum _140392 _140390) z i) = (@dollar _140395 (finite_sum _140392 _140390) z i)) = True.
Proof. exact (@lem7659358 _140395 (@dollar _140395 (finite_sum _140392 _140390) z i)). Qed.
Lemma lem7659360 {_140390 _140392 : Type'} (i : nat) : (term928 _140390 _140392 i) = (term928 _140390 _140392 i).
Proof. exact (eq_refl (term928 _140390 _140392 i)). Qed.
Lemma lem7659361 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term919 _140390 _140392 _140395 z i) = (term929 _140390 _140392 i).
Proof. exact (MK_COMB (@lem7659360 _140390 _140392 i) (@lem7659359 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659363 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7659364 {_140390 _140392 : Type'} (i : nat) : (term929 _140390 _140392 i) = True.
Proof. exact (@lem7659363 (term810 _140390 _140392 i)). Qed.
Lemma lem7659365 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term919 _140390 _140392 _140395 z i) = True.
Proof. exact (TRANS (@lem7659361 _140390 _140392 _140395 z i) (@lem7659364 _140390 _140392 i)). Qed.
Lemma lem7659366 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : True = (term919 _140390 _140392 _140395 z i).
Proof. exact (SYM (@lem7659365 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659381 (i : nat) (a : nat) (h1 : term7 i a) : term7 i a.
Proof. exact (h1). Qed.
Lemma lem7659382 (i : nat) (a : nat) (h1 : term7 i a) : (term1 i a) = i.
Proof. exact (@lem7652247 a i (@lem7659381 i a h1)). Qed.
Lemma lem7659388 (i : nat) (a : nat) (h1 : term7 i a) : term7 i a.
Proof. exact (h1). Qed.
Lemma lem7659389 (i : nat) (a : nat) (h1 : term7 i a) : term516 i a.
Proof. exact (@lem7654791 i a (@lem7659388 i a h1)). Qed.
Lemma lem7659390 (i : nat) (a : nat) : (term516 i a) = ((term516 i a) = True).
Proof. exact (@lem7 (term516 i a)). Qed.
Lemma lem7659391 (i : nat) (a : nat) (h1 : term7 i a) : (term516 i a) = True.
Proof. exact (EQ_MP (@lem7659390 i a) (@lem7659389 i a h1)). Qed.
Lemma lem7659397 (i : nat) (a : nat) (b : nat) (h1 : term644 i a b) : term644 i a b.
Proof. exact (h1). Qed.
Lemma lem7659398 (i : nat) (a : nat) (b : nat) (h1 : term644 i a b) : term645 i a b.
Proof. exact (@lem7657298 i a b (@lem7659397 i a b h1)). Qed.
Lemma lem7659399 (i : nat) (a : nat) (b : nat) : (term645 i a b) = ((term645 i a b) = True).
Proof. exact (@lem7 (term645 i a b)). Qed.
Lemma lem7659400 (i : nat) (a : nat) (b : nat) (h1 : term644 i a b) : (term645 i a b) = True.
Proof. exact (EQ_MP (@lem7659399 i a b) (@lem7659398 i a b h1)). Qed.
Lemma lem7659406 {A B : Type'} (g : nat -> A) (i : nat) : term787 A B g i.
Proof. exact (@lem7622314 A B g i). Qed.
Lemma lem7659407 {A B : Type'} (g : nat -> A) (i : nat) : (term787 A B g i) = (term788 A B g i).
Proof. exact (eq_refl (term787 A B g i)). Qed.
Lemma lem7659408 {A B : Type'} (g : nat -> A) (i : nat) : term788 A B g i.
Proof. exact (EQ_MP (@lem7659407 A B g i) (@lem7659406 A B g i)). Qed.
Lemma lem7659409 {B : Type'} (i : nat) (h1 : term789 B i) : term789 B i.
Proof. exact (h1). Qed.
Lemma lem7659410 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term789 B i) : (term790 A B g i) = (g i).
Proof. exact (@lem7659408 A B g i (@lem7659409 B i h1)). Qed.
Lemma lem7659416 {_140392 : Type'} (i : nat) : term930 _140392 i.
Proof. exact (@lem82 (term826 _140392 i)). Qed.
Lemma lem7659421 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term806 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7659422 (p : Prop) (q : Prop) (p' : Prop) : term807 p q p'.
Proof. exact (fun q' : Prop => @lem7659421 p q p' q'). Qed.
Lemma lem7659423 (p : Prop) (q : Prop) : term808 p q.
Proof. exact (fun p' : Prop => @lem7659422 p q p'). Qed.
Lemma lem7659424 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term931 _140390 _140392 _140395 z i.
Proof. exact (@lem7659423 (term810 _140390 _140392 i) ((term848 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i))). Qed.
Lemma lem7659425 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (p' : Prop) : term932 _140390 _140392 _140395 z i p'.
Proof. exact (@lem7659424 _140390 _140392 _140395 z i p'). Qed.
Lemma lem7659426 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (p' : Prop) : (term932 _140390 _140392 _140395 z i p') = (term933 _140390 _140392 _140395 z i p').
Proof. exact (eq_refl (term932 _140390 _140392 _140395 z i p')). Qed.
Lemma lem7659427 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (p' : Prop) : term933 _140390 _140392 _140395 z i p'.
Proof. exact (EQ_MP (@lem7659426 _140390 _140392 _140395 z i p') (@lem7659425 _140390 _140392 _140395 z i p')). Qed.
Lemma lem7659428 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (p' : Prop) (q' : Prop) : term934 _140390 _140392 _140395 z i p' q'.
Proof. exact (@lem7659427 _140390 _140392 _140395 z i p' q'). Qed.
Lemma lem7659429 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (p' : Prop) (q' : Prop) : (term934 _140390 _140392 _140395 z i p' q') = (term935 _140390 _140392 _140395 z i p' q').
Proof. exact (eq_refl (term934 _140390 _140392 _140395 z i p' q')). Qed.
Lemma lem7659430 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (p' : Prop) (q' : Prop) : term935 _140390 _140392 _140395 z i p' q'.
Proof. exact (EQ_MP (@lem7659429 _140390 _140392 _140395 z i p' q') (@lem7659428 _140390 _140392 _140395 z i p' q')). Qed.
Lemma lem7659437 {M N : Type'} : (@dimindex (finite_sum M N) (@UNIV (finite_sum M N))) = (term936 M N).
Proof. exact (EQ_MP (@lem7640410 M N) (@lem7640437 M N)). Qed.
Lemma lem7659438 {_140390 _140392 : Type'} : (@dimindex (finite_sum _140392 _140390) (@UNIV (finite_sum _140392 _140390))) = (term937 _140390 _140392).
Proof. exact (@lem7659437 _140392 _140390). Qed.
Lemma lem7659443 (i : nat) : (Peano.le i) = (Peano.le i).
Proof. exact (eq_refl (Peano.le i)). Qed.
Lemma lem7659444 {_140390 _140392 : Type'} (i : nat) : (term818 _140390 _140392 i) = (term938 _140390 _140392 i).
Proof. exact (MK_COMB (@lem7659443 i) (@lem7659438 _140390 _140392)). Qed.
Lemma lem7659449 (i : nat) : (term862 i) = (term862 i).
Proof. exact (eq_refl (term862 i)). Qed.
Lemma lem7659450 {_140390 _140392 : Type'} (i : nat) : (term810 _140390 _140392 i) = (term939 _140390 _140392 i).
Proof. exact (MK_COMB (@lem7659449 i) (@lem7659444 _140390 _140392 i)). Qed.
Lemma lem7659457 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (q' : Prop) : term940 _140390 _140392 _140395 z i q'.
Proof. exact (@lem7659430 _140390 _140392 _140395 z i (term939 _140390 _140392 i) q'). Qed.
Lemma lem7659458 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (q' : Prop) : term941 _140390 _140392 _140395 z i q'.
Proof. exact (@lem7659457 _140390 _140392 _140395 z i q' (@lem7659450 _140390 _140392 i)). Qed.
Lemma lem7659459 {_140390 _140392 : Type'} (i : nat) (h1 : term939 _140390 _140392 i) : term939 _140390 _140392 i.
Proof. exact (h1). Qed.
Lemma lem7659460 {_140390 _140392 : Type'} (i : nat) (h1 : term939 _140390 _140392 i) : term938 _140390 _140392 i.
Proof. exact (proj2 (@lem7659459 _140390 _140392 i h1)). Qed.
Lemma lem7659461 {_140390 _140392 : Type'} (i : nat) : (term938 _140390 _140392 i) = ((term938 _140390 _140392 i) = True).
Proof. exact (@lem7 (term938 _140390 _140392 i)). Qed.
Lemma lem7659469 {A B : Type'} (g : nat -> A) (i : nat) : term788 A B g i.
Proof. exact (fun h0 : term789 B i => @lem7659410 A B g i h0). Qed.
Lemma lem7659470 {_140390 _140395 : Type'} (g : nat -> _140395) (i : nat) : term879 _140390 _140395 g i.
Proof. exact (@lem7659469 _140395 _140390 g i). Qed.
Lemma lem7659471 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term942 _140390 _140392 _140395 z i.
Proof. exact (@lem7659470 _140390 _140395 (term943 _140390 _140392 _140395 z) (term847 _140392 i)). Qed.
Lemma lem7659475 (i : nat) (a : nat) : term944 i a.
Proof. exact (fun h0 : term7 i a => @lem7659391 i a h0). Qed.
Lemma lem7659476 {_140392 : Type'} (i : nat) : term945 _140392 i.
Proof. exact (@lem7659475 i (@dimindex _140392 (@UNIV _140392))). Qed.
Lemma lem7659478 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : (term826 _140392 i) = False.
Proof. exact (@lem7659416 _140392 i (@lem7659330 _140392 i h1)). Qed.
Lemma lem7659479 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7659480 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : (term850 _140392 i) = (~ False).
Proof. exact (MK_COMB (@lem7659479) (@lem7659478 _140392 i h1)). Qed.
Lemma lem7659482 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7659483 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : (term850 _140392 i) = True.
Proof. exact (TRANS (@lem7659480 _140392 i h1) (@lem7659482)). Qed.
Lemma lem7659484 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : True = (term850 _140392 i).
Proof. exact (SYM (@lem7659483 _140392 i h1)). Qed.
Lemma lem7659485 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : term850 _140392 i.
Proof. exact (EQ_MP (@lem7659484 _140392 i h1) (@lem0)). Qed.
Lemma lem7659486 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : (term946 _140392 i) = True.
Proof. exact (@lem7659476 _140392 i (@lem7659485 _140392 i h1)). Qed.
Lemma lem7659487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7659488 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : (term947 _140392 i) = (and True).
Proof. exact (MK_COMB (@lem7659487) (@lem7659486 _140392 i h1)). Qed.
Lemma lem7659490 (i : nat) (a : nat) (b : nat) : term948 i a b.
Proof. exact (fun h0 : term644 i a b => @lem7659400 i a b h0). Qed.
Lemma lem7659491 {_140390 _140392 : Type'} (i : nat) : term949 _140390 _140392 i.
Proof. exact (@lem7659490 i (@dimindex _140392 (@UNIV _140392)) (@dimindex _140390 (@UNIV _140390))). Qed.
Lemma lem7659493 {_140390 _140392 : Type'} (i : nat) (h1 : term939 _140390 _140392 i) : (term938 _140390 _140392 i) = True.
Proof. exact (EQ_MP (@lem7659461 _140390 _140392 i) (@lem7659460 _140390 _140392 i h1)). Qed.
Lemma lem7659494 {_140390 _140392 : Type'} (i : nat) (h1 : term939 _140390 _140392 i) : True = (term938 _140390 _140392 i).
Proof. exact (SYM (@lem7659493 _140390 _140392 i h1)). Qed.
Lemma lem7659495 {_140390 _140392 : Type'} (i : nat) (h1 : term939 _140390 _140392 i) : term938 _140390 _140392 i.
Proof. exact (EQ_MP (@lem7659494 _140390 _140392 i h1) (@lem0)). Qed.
Lemma lem7659496 {_140390 _140392 : Type'} (i : nat) (h1 : term939 _140390 _140392 i) : (term950 _140390 _140392 i) = True.
Proof. exact (@lem7659491 _140390 _140392 i (@lem7659495 _140390 _140392 i h1)). Qed.
Lemma lem7659497 {_140390 _140392 : Type'} (i : nat) (h1 : term850 _140392 i) (h2 : term939 _140390 _140392 i) : (term951 _140390 _140392 i) = (True /\ True).
Proof. exact (MK_COMB (@lem7659488 _140392 i h1) (@lem7659496 _140390 _140392 i h2)). Qed.
Lemma lem7659499 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7659500 : (True /\ True) = True.
Proof. exact (@lem7659499 True). Qed.
Lemma lem7659501 {_140390 _140392 : Type'} (i : nat) (h1 : term850 _140392 i) (h2 : term939 _140390 _140392 i) : (term951 _140390 _140392 i) = True.
Proof. exact (TRANS (@lem7659497 _140390 _140392 i h1 h2) (@lem7659500)). Qed.
Lemma lem7659502 {_140390 _140392 : Type'} (i : nat) (h1 : term850 _140392 i) (h2 : term939 _140390 _140392 i) : True = (term951 _140390 _140392 i).
Proof. exact (SYM (@lem7659501 _140390 _140392 i h1 h2)). Qed.
Lemma lem7659503 {_140390 _140392 : Type'} (i : nat) (h1 : term850 _140392 i) (h2 : term939 _140390 _140392 i) : term951 _140390 _140392 i.
Proof. exact (EQ_MP (@lem7659502 _140390 _140392 i h1 h2) (@lem0)). Qed.
Lemma lem7659504 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) (h2 : term939 _140390 _140392 i) : (term848 _140390 _140392 _140395 z i) = (term952 _140390 _140392 _140395 z i).
Proof. exact (@lem7659471 _140390 _140392 _140395 z i (@lem7659503 _140390 _140392 i h1 h2)). Qed.
Lemma lem7659506 {A B : Type'} (f : A -> B) (y : A) : (term864 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7659507 {_140395 : Type'} (f : nat -> _140395) (y : nat) : (term865 _140395 f y) = (f y).
Proof. exact (@lem7659506 nat _140395 f y). Qed.
Lemma lem7659508 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term953 _140390 _140392 _140395 z i) = (term952 _140390 _140392 _140395 z i).
Proof. exact (@lem7659507 _140395 (term943 _140390 _140392 _140395 z) (term847 _140392 i)). Qed.
Lemma lem7659509 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term954 _140390 _140392 _140395 z i) = (term955 _140390 _140392 _140395 z i).
Proof. exact (eq_refl (term954 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659510 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (term956 _140390 _140392 _140395 z) = (term943 _140390 _140392 _140395 z).
Proof. exact (fun_ext (fun i : nat => @lem7659509 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659511 {_140392 : Type'} (i : nat) : (term847 _140392 i) = (term847 _140392 i).
Proof. exact (eq_refl (term847 _140392 i)). Qed.
Lemma lem7659512 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term953 _140390 _140392 _140395 z i) = (term952 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7659510 _140390 _140392 _140395 z) (@lem7659511 _140392 i)). Qed.
Lemma lem7659513 {_140395 : Type'} : (@eq _140395) = (@eq _140395).
Proof. exact (eq_refl (@eq _140395)). Qed.
Lemma lem7659514 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term957 _140390 _140392 _140395 z i) = (term958 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7659513 _140395) (@lem7659512 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659515 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term952 _140390 _140392 _140395 z i) = (term959 _140390 _140392 _140395 z i).
Proof. exact (eq_refl (term952 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659516 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : ((term953 _140390 _140392 _140395 z i) = (term952 _140390 _140392 _140395 z i)) = ((term952 _140390 _140392 _140395 z i) = (term959 _140390 _140392 _140395 z i)).
Proof. exact (MK_COMB (@lem7659514 _140390 _140392 _140395 z i) (@lem7659515 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659517 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (term952 _140390 _140392 _140395 z i) = (term959 _140390 _140392 _140395 z i).
Proof. exact (EQ_MP (@lem7659516 _140390 _140392 _140395 z i) (@lem7659508 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659519 (a : nat) (i : nat) : term6 a i.
Proof. exact (fun h0 : term7 i a => @lem7659382 i a h0). Qed.
Lemma lem7659520 {_140392 : Type'} (i : nat) : term960 _140392 i.
Proof. exact (@lem7659519 (@dimindex _140392 (@UNIV _140392)) i). Qed.
Lemma lem7659522 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : (term826 _140392 i) = False.
Proof. exact (@lem7659416 _140392 i (@lem7659330 _140392 i h1)). Qed.
Lemma lem7659523 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7659524 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : (term850 _140392 i) = (~ False).
Proof. exact (MK_COMB (@lem7659523) (@lem7659522 _140392 i h1)). Qed.
Lemma lem7659526 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7659527 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : (term850 _140392 i) = True.
Proof. exact (TRANS (@lem7659524 _140392 i h1) (@lem7659526)). Qed.
Lemma lem7659528 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : True = (term850 _140392 i).
Proof. exact (SYM (@lem7659527 _140392 i h1)). Qed.
Lemma lem7659529 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : term850 _140392 i.
Proof. exact (EQ_MP (@lem7659528 _140392 i h1) (@lem0)). Qed.
Lemma lem7659530 {_140392 : Type'} (i : nat) (h1 : term850 _140392 i) : (term961 _140392 i) = i.
Proof. exact (@lem7659520 _140392 i (@lem7659529 _140392 i h1)). Qed.
Lemma lem7659531 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : (@dollar _140395 (finite_sum _140392 _140390) z) = (@dollar _140395 (finite_sum _140392 _140390) z).
Proof. exact (eq_refl (@dollar _140395 (finite_sum _140392 _140390) z)). Qed.
Lemma lem7659532 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) : (term959 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i).
Proof. exact (MK_COMB (@lem7659531 _140390 _140392 _140395 z) (@lem7659530 _140392 i h1)). Qed.
Lemma lem7659533 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) : (term952 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i).
Proof. exact (TRANS (@lem7659517 _140390 _140392 _140395 z i) (@lem7659532 _140390 _140392 _140395 z i h1)). Qed.
Lemma lem7659534 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) (h2 : term939 _140390 _140392 i) : (term848 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i).
Proof. exact (TRANS (@lem7659504 _140390 _140392 _140395 z i h1 h2) (@lem7659533 _140390 _140392 _140395 z i h1)). Qed.
Lemma lem7659535 {_140395 : Type'} : (@eq _140395) = (@eq _140395).
Proof. exact (eq_refl (@eq _140395)). Qed.
Lemma lem7659536 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) (h2 : term939 _140390 _140392 i) : (term962 _140390 _140392 _140395 z i) = (term963 _140390 _140392 _140395 z i).
Proof. exact (MK_COMB (@lem7659535 _140395) (@lem7659534 _140390 _140392 _140395 z i h1 h2)). Qed.
Lemma lem7659537 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : (@dollar _140395 (finite_sum _140392 _140390) z i) = (@dollar _140395 (finite_sum _140392 _140390) z i).
Proof. exact (eq_refl (@dollar _140395 (finite_sum _140392 _140390) z i)). Qed.
Lemma lem7659538 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) (h2 : term939 _140390 _140392 i) : ((term848 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i)) = ((@dollar _140395 (finite_sum _140392 _140390) z i) = (@dollar _140395 (finite_sum _140392 _140390) z i)).
Proof. exact (MK_COMB (@lem7659536 _140390 _140392 _140395 z i h1 h2) (@lem7659537 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659540 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7659541 {_140395 : Type'} (x : _140395) : (x = x) = True.
Proof. exact (@lem7659540 _140395 x). Qed.
Lemma lem7659542 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : ((@dollar _140395 (finite_sum _140392 _140390) z i) = (@dollar _140395 (finite_sum _140392 _140390) z i)) = True.
Proof. exact (@lem7659541 _140395 (@dollar _140395 (finite_sum _140392 _140390) z i)). Qed.
Lemma lem7659543 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) (h2 : term939 _140390 _140392 i) : ((term848 _140390 _140392 _140395 z i) = (@dollar _140395 (finite_sum _140392 _140390) z i)) = True.
Proof. exact (TRANS (@lem7659538 _140390 _140392 _140395 z i h1 h2) (@lem7659542 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659544 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) : term964 _140390 _140392 _140395 z i.
Proof. exact (fun h0 : term939 _140390 _140392 i => @lem7659543 _140390 _140392 _140395 z i h1 h0). Qed.
Lemma lem7659545 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term965 _140390 _140392 _140395 z i.
Proof. exact (@lem7659458 _140390 _140392 _140395 z i True). Qed.
Lemma lem7659546 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) : (term914 _140390 _140392 _140395 z i) = (term966 _140390 _140392 i).
Proof. exact (@lem7659545 _140390 _140392 _140395 z i (@lem7659544 _140390 _140392 _140395 z i h1)). Qed.
Lemma lem7659548 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7659549 {_140390 _140392 : Type'} (i : nat) : (term966 _140390 _140392 i) = True.
Proof. exact (@lem7659548 (term939 _140390 _140392 i)). Qed.
Lemma lem7659550 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) : (term914 _140390 _140392 _140395 z i) = True.
Proof. exact (TRANS (@lem7659546 _140390 _140392 _140395 z i h1) (@lem7659549 _140390 _140392 i)). Qed.
Lemma lem7659551 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) : True = (term914 _140390 _140392 _140395 z i).
Proof. exact (SYM (@lem7659550 _140390 _140392 _140395 z i h1)). Qed.
Lemma lem7659554 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) : term914 _140390 _140392 _140395 z i.
Proof. exact (EQ_MP (@lem7659551 _140390 _140392 _140395 z i h1) (@lem0)). Qed.
Lemma lem7659555 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) : (term850 _140392 i) = (term914 _140390 _140392 _140395 z i).
Proof. exact (prop_ext (fun h2 : term850 _140392 i => @lem7659554 _140390 _140392 _140395 z i h1) (fun h2 : term914 _140390 _140392 _140395 z i => @lem7659330 _140392 i h1)). Qed.
Lemma lem7659556 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) (h1 : term850 _140392 i) : term914 _140390 _140392 _140395 z i.
Proof. exact (EQ_MP (@lem7659555 _140390 _140392 _140395 z i h1) (@lem7659330 _140392 i h1)). Qed.
Lemma lem7659557 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term917 _140390 _140392 _140395 z i.
Proof. exact (fun h0 : term850 _140392 i => @lem7659556 _140390 _140392 _140395 z i h0). Qed.
Lemma lem7659558 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term919 _140390 _140392 _140395 z i.
Proof. exact (EQ_MP (@lem7659366 _140390 _140392 _140395 z i) (@lem0)). Qed.
Lemma lem7659559 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term922 _140390 _140392 _140395 z i.
Proof. exact (fun h0 : term826 _140392 i => @lem7659558 _140390 _140392 _140395 z i). Qed.
Lemma lem7659560 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term925 _140390 _140392 _140395 z i.
Proof. exact (conj (@lem7659559 _140390 _140392 _140395 z i) (@lem7659557 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659561 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) (i : nat) : term898 _140390 _140392 _140395 z i.
Proof. exact (EQ_MP (@lem7659312 _140390 _140392 _140395 z i) (@lem7659560 _140390 _140392 _140395 z i)). Qed.
Lemma lem7659566 {_140390 _140392 _140395 : Type'} (z : type4 _140390 _140392 _140395) : term901 _140390 _140392 _140395 z.
Proof. exact (fun i : nat => @lem7659561 _140390 _140392 _140395 z i). Qed.
Lemma lem7659571 {_140390 _140392 _140395 : Type'} : term905 _140390 _140392 _140395.
Proof. exact (fun z : type4 _140390 _140392 _140395 => @lem7659566 _140390 _140392 _140395 z). Qed.
Lemma lem7659572 {_140390 _140392 _140395 : Type'} : term904 _140390 _140392 _140395.
Proof. exact (EQ_MP (@lem7659294 _140390 _140392 _140395) (@lem7659571 _140390 _140392 _140395)). Qed.
