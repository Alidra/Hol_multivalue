Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INDUCT_DELETE_term_abbrevs.
Require Import CARD_DELETE_spec.
Require Import CARD_EQ_0_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_DELETE_spec.
Require Import INT_POS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import num_WF_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032098_spec.
Require Import thm1032781_spec.
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
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
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
Require Import thm4211_spec.
Require Import thm510983_spec.
Require Import thm511983_spec.
Require Import thm511998_spec.
Require Import thm512702_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem3855291 (n : nat) : (term0 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem3855293 (n : nat) : (term1 n) = (term1 n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem3855294 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem3855293 n) (@lem3855291 n)). Qed.
Lemma lem3855299 (n : nat) : (term4 n) = (term4 n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem3855300 (n : nat) : (term5 n) = (term6 n).
Proof. exact (MK_COMB (@lem3855299 n) (@lem3855294 n)). Qed.
Lemma lem3855301 (n : nat) : ((term7 n) = (term8 n)) = (term5 n).
Proof. exact (@lem17500 (term7 n) (term8 n)). Qed.
Lemma lem3855303 (n : nat) : ((term7 n) = (term8 n)) = (term6 n).
Proof. exact (TRANS (@lem3855301 n) (@lem3855300 n)). Qed.
Lemma lem3855304 (n : nat) : (term9 n) = (term10 n).
Proof. exact (@lem1032781 n term11 (term12 n)). Qed.
Lemma lem3855305 (d : nat) (n : nat) : (term13 n d) = (term14 d n).
Proof. exact (eq_refl (term13 n d)). Qed.
Lemma lem3855306 (n : nat) (d : nat) : (term15 n d) = (term15 n d).
Proof. exact (eq_refl (term15 n d)). Qed.
Lemma lem3855307 (d : nat) (n : nat) : (term16 n d) = (term17 d n).
Proof. exact (MK_COMB (@lem3855306 n d) (@lem3855305 d n)). Qed.
Lemma lem3855308 (n : nat) : (term18 n) = (term19 n).
Proof. exact (fun_ext (fun d : nat => @lem3855307 d n)). Qed.
Lemma lem3855309 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3855310 (n : nat) : (term10 n) = (term20 n).
Proof. exact (MK_COMB (@lem3855309) (@lem3855308 n)). Qed.
Lemma lem3855311 (n : nat) : (term9 n) = (term6 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem3855312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3855313 (n : nat) : (term21 n) = (term22 n).
Proof. exact (MK_COMB (@lem3855312) (@lem3855311 n)). Qed.
Lemma lem3855314 (n : nat) : ((term9 n) = (term10 n)) = ((term6 n) = (term20 n)).
Proof. exact (MK_COMB (@lem3855313 n) (@lem3855310 n)). Qed.
Lemma lem3855315 (n : nat) : (term6 n) = (term20 n).
Proof. exact (EQ_MP (@lem3855314 n) (@lem3855304 n)). Qed.
Lemma lem3855316 (d : nat) (n : nat) : (term17 d n) = (term17 d n).
Proof. exact (eq_refl (term17 d n)). Qed.
Lemma lem3855317 (n : nat) : (term19 n) = (term19 n).
Proof. exact (fun_ext (fun d : nat => @lem3855316 d n)). Qed.
Lemma lem3855318 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3855319 (n : nat) : (term20 n) = (term20 n).
Proof. exact (MK_COMB (@lem3855318) (@lem3855317 n)). Qed.
Lemma lem3855320 (n : nat) : (term22 n) = (term22 n).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem3855321 (n : nat) : ((term6 n) = (term20 n)) = ((term6 n) = (term20 n)).
Proof. exact (MK_COMB (@lem3855320 n) (@lem3855319 n)). Qed.
Lemma lem3855322 (n : nat) : (term6 n) = (term20 n).
Proof. exact (EQ_MP (@lem3855321 n) (@lem3855315 n)). Qed.
Lemma lem3855353 (n : nat) : ((term7 n) = (term8 n)) = (term20 n).
Proof. exact (TRANS (@lem3855303 n) (@lem3855322 n)). Qed.
Lemma lem3855386 (d : nat) (n : nat) : (term14 d n) = (term14 d n).
Proof. exact (eq_refl (term14 d n)). Qed.
Lemma lem3855403 (n : nat) (d : nat) : (term23 n d) = (term23 n d).
Proof. exact (eq_refl (term23 n d)). Qed.
Lemma lem3855410 (d : nat) : (term24 d) = (term25 d).
Proof. exact (@lem1032098 d term11). Qed.
Lemma lem3855413 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem3855414 (n : nat) (d : nat) : (n = (term24 d)) = (n = (term25 d)).
Proof. exact (MK_COMB (@lem3855413 n) (@lem3855410 d)). Qed.
Lemma lem3855415 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3855416 (n : nat) (d : nat) : (term26 n d) = (term27 n d).
Proof. exact (MK_COMB (@lem3855415) (@lem3855414 n d)). Qed.
Lemma lem3855417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3855418 (n : nat) (d : nat) : (term28 n d) = (term29 n d).
Proof. exact (MK_COMB (@lem3855417) (@lem3855416 n d)). Qed.
Lemma lem3855419 (n : nat) (d : nat) : (term30 n d) = (term31 n d).
Proof. exact (MK_COMB (@lem3855418 n d) (@lem3855403 n d)). Qed.
Lemma lem3855420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3855421 (n : nat) (d : nat) : (term15 n d) = (term32 n d).
Proof. exact (MK_COMB (@lem3855420) (@lem3855419 n d)). Qed.
Lemma lem3855422 (d : nat) (n : nat) : (term17 d n) = (term33 d n).
Proof. exact (MK_COMB (@lem3855421 n d) (@lem3855386 d n)). Qed.
Lemma lem3855423 (n : nat) : (term19 n) = (term34 n).
Proof. exact (fun_ext (fun d : nat => @lem3855422 d n)). Qed.
Lemma lem3855424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3855425 (n : nat) : (term20 n) = (term35 n).
Proof. exact (MK_COMB (@lem3855424) (@lem3855423 n)). Qed.
Lemma lem3855428 (n : nat) : ((term7 n) = (term8 n)) = (term35 n).
Proof. exact (TRANS (@lem3855353 n) (@lem3855425 n)). Qed.
Lemma lem3855430 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3855431 (n : nat) (d : nat) : (n = (term25 d)) = ((int_of_num n) = (term36 d)).
Proof. exact (@lem3855430 n (term25 d)). Qed.
Lemma lem3855435 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem3855436 (d : nat) : (term36 d) = (term39 d).
Proof. exact (@lem3855435 d term11). Qed.
Lemma lem3855437 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem3855438 (n : nat) (d : nat) : ((int_of_num n) = (term36 d)) = ((int_of_num n) = (term39 d)).
Proof. exact (MK_COMB (@lem3855437 n) (@lem3855436 d)). Qed.
Lemma lem3855439 (n : nat) (d : nat) : (n = (term25 d)) = ((int_of_num n) = (term39 d)).
Proof. exact (TRANS (@lem3855431 n d) (@lem3855438 n d)). Qed.
Lemma lem3855440 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3855441 (n : nat) (d : nat) : (term27 n d) = (term41 n d).
Proof. exact (MK_COMB (@lem3855440) (@lem3855439 n d)). Qed.
Lemma lem3855442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3855443 (n : nat) (d : nat) : (term29 n d) = (term42 n d).
Proof. exact (MK_COMB (@lem3855442) (@lem3855441 n d)). Qed.
Lemma lem3855445 (m : nat) (n : nat) : (Peano.lt m n) = (term43 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem3855446 (n : nat) : (term44 n) = (term45 n).
Proof. exact (@lem3855445 n term11). Qed.
Lemma lem3855447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3855448 (n : nat) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem3855447) (@lem3855446 n)). Qed.
Lemma lem3855449 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3855450 (n : nat) : (term48 n) = (term49 n).
Proof. exact (MK_COMB (@lem3855449) (@lem3855448 n)). Qed.
Lemma lem3855452 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3855453 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term50).
Proof. exact (@lem3855452 d (NUMERAL 0)). Qed.
Lemma lem3855456 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3855457 (d : nat) : (term8 d) = (term51 d).
Proof. exact (MK_COMB (@lem3855456) (@lem3855453 d)). Qed.
Lemma lem3855458 (n : nat) (d : nat) : (term23 n d) = (term52 n d).
Proof. exact (MK_COMB (@lem3855450 n) (@lem3855457 d)). Qed.
Lemma lem3855459 (n : nat) (d : nat) : (term31 n d) = (term53 n d).
Proof. exact (MK_COMB (@lem3855443 n d) (@lem3855458 n d)). Qed.
Lemma lem3855460 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3855461 (n : nat) (d : nat) : (term32 n d) = (term54 n d).
Proof. exact (MK_COMB (@lem3855460) (@lem3855459 n d)). Qed.
Lemma lem3855463 (m : nat) (n : nat) : (Peano.lt m n) = (term43 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem3855464 (d : nat) (n : nat) : (Peano.lt d n) = (term43 d n).
Proof. exact (@lem3855463 d n). Qed.
Lemma lem3855465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3855466 (d : nat) (n : nat) : (term55 d n) = (term56 d n).
Proof. exact (MK_COMB (@lem3855465) (@lem3855464 d n)). Qed.
Lemma lem3855468 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3855469 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term50).
Proof. exact (@lem3855468 n (NUMERAL 0)). Qed.
Lemma lem3855472 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3855473 (n : nat) : (term8 n) = (term51 n).
Proof. exact (MK_COMB (@lem3855472) (@lem3855469 n)). Qed.
Lemma lem3855474 (d : nat) (n : nat) : (term57 d n) = (term58 d n).
Proof. exact (MK_COMB (@lem3855466 d n) (@lem3855473 n)). Qed.
Lemma lem3855475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3855476 (d : nat) (n : nat) : (term59 d n) = (term60 d n).
Proof. exact (MK_COMB (@lem3855475) (@lem3855474 d n)). Qed.
Lemma lem3855478 (m : nat) (n : nat) : (Peano.lt m n) = (term43 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem3855479 (d : nat) (n : nat) : (Peano.lt d n) = (term43 d n).
Proof. exact (@lem3855478 d n). Qed.
Lemma lem3855480 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3855481 (d : nat) (n : nat) : (term61 d n) = (term62 d n).
Proof. exact (MK_COMB (@lem3855480) (@lem3855479 d n)). Qed.
Lemma lem3855482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3855483 (d : nat) (n : nat) : (term63 d n) = (term64 d n).
Proof. exact (MK_COMB (@lem3855482) (@lem3855481 d n)). Qed.
Lemma lem3855485 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3855486 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term50).
Proof. exact (@lem3855485 n (NUMERAL 0)). Qed.
Lemma lem3855489 (d : nat) (n : nat) : (term65 d n) = (term66 d n).
Proof. exact (MK_COMB (@lem3855483 d n) (@lem3855486 n)). Qed.
Lemma lem3855490 (d : nat) (n : nat) : (term14 d n) = (term67 d n).
Proof. exact (MK_COMB (@lem3855476 d n) (@lem3855489 d n)). Qed.
Lemma lem3855491 (d : nat) (n : nat) : (term33 d n) = (term68 d n).
Proof. exact (MK_COMB (@lem3855461 n d) (@lem3855490 d n)). Qed.
Lemma lem3855492 (n : nat) : (term34 n) = (term69 n).
Proof. exact (fun_ext (fun d : nat => @lem3855491 d n)). Qed.
Lemma lem3855493 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3855494 (n : nat) : (term35 n) = (term70 n).
Proof. exact (MK_COMB (@lem3855493) (@lem3855492 n)). Qed.
Lemma lem3855495 (n : nat) : ((term7 n) = (term8 n)) = (term70 n).
Proof. exact (TRANS (@lem3855428 n) (@lem3855494 n)). Qed.
Lemma lem3855496 (d : nat) : term71 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem3855497 (d : nat) : (term71 d) = (term72 d).
Proof. exact (eq_refl (term71 d)). Qed.
Lemma lem3855498 (d : nat) : term72 d.
Proof. exact (EQ_MP (@lem3855497 d) (@lem3855496 d)). Qed.
Lemma lem3855499 (n : nat) : term71 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem3855500 (n : nat) : (term71 n) = (term72 n).
Proof. exact (eq_refl (term71 n)). Qed.
Lemma lem3855501 (n : nat) : term72 n.
Proof. exact (EQ_MP (@lem3855500 n) (@lem3855499 n)). Qed.
Lemma lem3855502 (_44749 : int) (_44750 : int) : (term73 _44749 _44750) = (term74 _44749 _44750).
Proof. exact (@lem2318604 (term74 _44749 _44750)). Qed.
Lemma lem3855528 (_44750 : int) (_44749 : int) : (term75 _44750 _44749) = (_44750 = (term76 _44749)).
Proof. exact (@lem16933 (_44750 = (term76 _44749))). Qed.
Lemma lem3855531 (_44750 : int) : (term77 _44750) = (term78 _44750).
Proof. exact (@lem16933 (term78 _44750)). Qed.
Lemma lem3855534 (_44749 : int) : (term79 _44749) = (_44749 = term50).
Proof. exact (@lem16933 (_44749 = term50)). Qed.
Lemma lem3855535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3855536 (_44750 : int) : (term80 _44750) = (term81 _44750).
Proof. exact (MK_COMB (@lem3855535) (@lem3855531 _44750)). Qed.
Lemma lem3855537 (_44750 : int) (_44749 : int) : (term82 _44750 _44749) = (term83 _44750 _44749).
Proof. exact (MK_COMB (@lem3855536 _44750) (@lem3855534 _44749)). Qed.
Lemma lem3855538 (_44750 : int) (_44749 : int) : (term84 _44750 _44749) = (term82 _44750 _44749).
Proof. exact (@lem17160 (term85 _44750) (term86 _44749)). Qed.
Lemma lem3855539 (_44750 : int) (_44749 : int) : (term84 _44750 _44749) = (term83 _44750 _44749).
Proof. exact (TRANS (@lem3855538 _44750 _44749) (@lem3855537 _44750 _44749)). Qed.
Lemma lem3855540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3855541 (_44750 : int) (_44749 : int) : (term87 _44750 _44749) = (term88 _44750 _44749).
Proof. exact (MK_COMB (@lem3855540) (@lem3855528 _44750 _44749)). Qed.
Lemma lem3855542 (_44750 : int) (_44749 : int) : (term89 _44750 _44749) = (term90 _44750 _44749).
Proof. exact (MK_COMB (@lem3855541 _44750 _44749) (@lem3855539 _44750 _44749)). Qed.
Lemma lem3855543 (_44750 : int) (_44749 : int) : (term91 _44750 _44749) = (term89 _44750 _44749).
Proof. exact (@lem17045 (term92 _44750 _44749) (term93 _44750 _44749)). Qed.
Lemma lem3855544 (_44750 : int) (_44749 : int) : (term91 _44750 _44749) = (term90 _44750 _44749).
Proof. exact (TRANS (@lem3855543 _44750 _44749) (@lem3855542 _44750 _44749)). Qed.
Lemma lem3855548 (_44750 : int) : (term79 _44750) = (_44750 = term50).
Proof. exact (@lem16933 (_44750 = term50)). Qed.
Lemma lem3855550 (_44749 : int) (_44750 : int) : (term94 _44749 _44750) = (term94 _44749 _44750).
Proof. exact (eq_refl (term94 _44749 _44750)). Qed.
Lemma lem3855551 (_44749 : int) (_44750 : int) : (term95 _44749 _44750) = (term96 _44749 _44750).
Proof. exact (MK_COMB (@lem3855550 _44749 _44750) (@lem3855548 _44750)). Qed.
Lemma lem3855552 (_44749 : int) (_44750 : int) : (term97 _44749 _44750) = (term95 _44749 _44750).
Proof. exact (@lem17045 (int_lt _44749 _44750) (term86 _44750)). Qed.
Lemma lem3855553 (_44749 : int) (_44750 : int) : (term97 _44749 _44750) = (term96 _44749 _44750).
Proof. exact (TRANS (@lem3855552 _44749 _44750) (@lem3855551 _44749 _44750)). Qed.
Lemma lem3855556 (_44749 : int) (_44750 : int) : (term98 _44749 _44750) = (int_lt _44749 _44750).
Proof. exact (@lem16933 (int_lt _44749 _44750)). Qed.
Lemma lem3855557 (_44750 : int) : (term86 _44750) = (term86 _44750).
Proof. exact (eq_refl (term86 _44750)). Qed.
Lemma lem3855558 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3855559 (_44749 : int) (_44750 : int) : (term99 _44749 _44750) = (term100 _44749 _44750).
Proof. exact (MK_COMB (@lem3855558) (@lem3855556 _44749 _44750)). Qed.
Lemma lem3855560 (_44749 : int) (_44750 : int) : (term101 _44749 _44750) = (term102 _44749 _44750).
Proof. exact (MK_COMB (@lem3855559 _44749 _44750) (@lem3855557 _44750)). Qed.
Lemma lem3855561 (_44749 : int) (_44750 : int) : (term103 _44749 _44750) = (term101 _44749 _44750).
Proof. exact (@lem17045 (term104 _44749 _44750) (_44750 = term50)). Qed.
Lemma lem3855562 (_44749 : int) (_44750 : int) : (term103 _44749 _44750) = (term102 _44749 _44750).
Proof. exact (TRANS (@lem3855561 _44749 _44750) (@lem3855560 _44749 _44750)). Qed.
Lemma lem3855563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3855564 (_44749 : int) (_44750 : int) : (term105 _44749 _44750) = (term106 _44749 _44750).
Proof. exact (MK_COMB (@lem3855563) (@lem3855553 _44749 _44750)). Qed.
Lemma lem3855565 (_44749 : int) (_44750 : int) : (term107 _44749 _44750) = (term108 _44749 _44750).
Proof. exact (MK_COMB (@lem3855564 _44749 _44750) (@lem3855562 _44749 _44750)). Qed.
Lemma lem3855566 (_44749 : int) (_44750 : int) : (term109 _44749 _44750) = (term107 _44749 _44750).
Proof. exact (@lem17160 (term110 _44749 _44750) (term111 _44749 _44750)). Qed.
Lemma lem3855567 (_44749 : int) (_44750 : int) : (term109 _44749 _44750) = (term108 _44749 _44750).
Proof. exact (TRANS (@lem3855566 _44749 _44750) (@lem3855565 _44749 _44750)). Qed.
Lemma lem3855568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3855569 (_44750 : int) (_44749 : int) : (term112 _44750 _44749) = (term113 _44750 _44749).
Proof. exact (MK_COMB (@lem3855568) (@lem3855544 _44750 _44749)). Qed.
Lemma lem3855570 (_44749 : int) (_44750 : int) : (term114 _44749 _44750) = (term115 _44749 _44750).
Proof. exact (MK_COMB (@lem3855569 _44750 _44749) (@lem3855567 _44749 _44750)). Qed.
Lemma lem3855571 (_44749 : int) (_44750 : int) : (term116 _44749 _44750) = (term114 _44749 _44750).
Proof. exact (@lem17160 (term117 _44750 _44749) (term118 _44749 _44750)). Qed.
Lemma lem3855572 (_44749 : int) (_44750 : int) : (term116 _44749 _44750) = (term115 _44749 _44750).
Proof. exact (TRANS (@lem3855571 _44749 _44750) (@lem3855570 _44749 _44750)). Qed.
Lemma lem3855574 (_44750 : int) : (term119 _44750) = (term119 _44750).
Proof. exact (eq_refl (term119 _44750)). Qed.
Lemma lem3855575 (_44749 : int) (_44750 : int) : (term120 _44749 _44750) = (term121 _44749 _44750).
Proof. exact (MK_COMB (@lem3855574 _44750) (@lem3855572 _44749 _44750)). Qed.
Lemma lem3855576 (_44749 : int) (_44750 : int) : (term122 _44749 _44750) = (term120 _44749 _44750).
Proof. exact (@lem17362 (term123 _44750) (term124 _44749 _44750)). Qed.
Lemma lem3855577 (_44749 : int) (_44750 : int) : (term122 _44749 _44750) = (term121 _44749 _44750).
Proof. exact (TRANS (@lem3855576 _44749 _44750) (@lem3855575 _44749 _44750)). Qed.
Lemma lem3855579 (_44749 : int) : (term119 _44749) = (term119 _44749).
Proof. exact (eq_refl (term119 _44749)). Qed.
Lemma lem3855580 (_44749 : int) (_44750 : int) : (term125 _44749 _44750) = (term126 _44749 _44750).
Proof. exact (MK_COMB (@lem3855579 _44749) (@lem3855577 _44749 _44750)). Qed.
Lemma lem3855581 (_44749 : int) (_44750 : int) : (term127 _44749 _44750) = (term125 _44749 _44750).
Proof. exact (@lem17362 (term123 _44749) (term128 _44749 _44750)). Qed.
Lemma lem3855621 (_44749 : int) (_44750 : int) : (term127 _44749 _44750) = (term126 _44749 _44750).
Proof. exact (TRANS (@lem3855581 _44749 _44750) (@lem3855580 _44749 _44750)). Qed.
Lemma lem3855624 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3855625 (_44749 : int) : (term123 _44749) = (term130 _44749).
Proof. exact (@lem3855624 term50 _44749). Qed.
Lemma lem3855627 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3855628 : term132 = term133.
Proof. exact (@lem3855627 (NUMERAL 0)). Qed.
Lemma lem3855629 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3855630 : term134 = term135.
Proof. exact (MK_COMB (@lem3855629) (@lem3855628)). Qed.
Lemma lem3855631 (_44749 : int) : (real_of_int _44749) = (real_of_int _44749).
Proof. exact (eq_refl (real_of_int _44749)). Qed.
Lemma lem3855632 (_44749 : int) : (term130 _44749) = (term136 _44749).
Proof. exact (MK_COMB (@lem3855630) (@lem3855631 _44749)). Qed.
Lemma lem3855634 (_44749 : int) : (term123 _44749) = (term136 _44749).
Proof. exact (TRANS (@lem3855625 _44749) (@lem3855632 _44749)). Qed.
Lemma lem3855637 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3855638 (_44750 : int) : (term123 _44750) = (term130 _44750).
Proof. exact (@lem3855637 term50 _44750). Qed.
Lemma lem3855640 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3855641 : term132 = term133.
Proof. exact (@lem3855640 (NUMERAL 0)). Qed.
Lemma lem3855642 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3855643 : term134 = term135.
Proof. exact (MK_COMB (@lem3855642) (@lem3855641)). Qed.
Lemma lem3855644 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3855645 (_44750 : int) : (term130 _44750) = (term136 _44750).
Proof. exact (MK_COMB (@lem3855643) (@lem3855644 _44750)). Qed.
Lemma lem3855647 (_44750 : int) : (term123 _44750) = (term136 _44750).
Proof. exact (TRANS (@lem3855638 _44750) (@lem3855645 _44750)). Qed.
Lemma lem3855650 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3855651 (_44750 : int) (_44749 : int) : (_44750 = (term76 _44749)) = ((real_of_int _44750) = (term137 _44749)).
Proof. exact (@lem3855650 _44750 (term76 _44749)). Qed.
Lemma lem3855655 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3855656 (_44749 : int) : (term137 _44749) = (term140 _44749).
Proof. exact (@lem3855655 _44749 term141). Qed.
Lemma lem3855658 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3855659 : term142 = term143.
Proof. exact (@lem3855658 term11). Qed.
Lemma lem3855660 (_44749 : int) : (term144 _44749) = (term144 _44749).
Proof. exact (eq_refl (term144 _44749)). Qed.
Lemma lem3855661 (_44749 : int) : (term140 _44749) = (term145 _44749).
Proof. exact (MK_COMB (@lem3855660 _44749) (@lem3855659)). Qed.
Lemma lem3855662 (_44749 : int) : (term137 _44749) = (term145 _44749).
Proof. exact (TRANS (@lem3855656 _44749) (@lem3855661 _44749)). Qed.
Lemma lem3855663 (_44750 : int) : (term146 _44750) = (term146 _44750).
Proof. exact (eq_refl (term146 _44750)). Qed.
Lemma lem3855664 (_44750 : int) (_44749 : int) : ((real_of_int _44750) = (term137 _44749)) = ((real_of_int _44750) = (term145 _44749)).
Proof. exact (MK_COMB (@lem3855663 _44750) (@lem3855662 _44749)). Qed.
Lemma lem3855666 (_44750 : int) (_44749 : int) : (_44750 = (term76 _44749)) = ((real_of_int _44750) = (term145 _44749)).
Proof. exact (TRANS (@lem3855651 _44750 _44749) (@lem3855664 _44750 _44749)). Qed.
Lemma lem3855668 (x : int) (y : int) : (int_lt x y) = (term147 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem3855669 (_44750 : int) : (term78 _44750) = (term148 _44750).
Proof. exact (@lem3855668 _44750 term141). Qed.
Lemma lem3855671 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3855672 (_44750 : int) : (term148 _44750) = (term149 _44750).
Proof. exact (@lem3855671 (term76 _44750) term141). Qed.
Lemma lem3855674 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3855675 (_44750 : int) : (term137 _44750) = (term140 _44750).
Proof. exact (@lem3855674 _44750 term141). Qed.
Lemma lem3855677 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3855678 : term142 = term143.
Proof. exact (@lem3855677 term11). Qed.
Lemma lem3855679 (_44750 : int) : (term144 _44750) = (term144 _44750).
Proof. exact (eq_refl (term144 _44750)). Qed.
Lemma lem3855680 (_44750 : int) : (term140 _44750) = (term145 _44750).
Proof. exact (MK_COMB (@lem3855679 _44750) (@lem3855678)). Qed.
Lemma lem3855681 (_44750 : int) : (term137 _44750) = (term145 _44750).
Proof. exact (TRANS (@lem3855675 _44750) (@lem3855680 _44750)). Qed.
Lemma lem3855682 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3855683 (_44750 : int) : (term150 _44750) = (term151 _44750).
Proof. exact (MK_COMB (@lem3855682) (@lem3855681 _44750)). Qed.
Lemma lem3855685 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3855686 : term142 = term143.
Proof. exact (@lem3855685 term11). Qed.
Lemma lem3855687 (_44750 : int) : (term149 _44750) = (term152 _44750).
Proof. exact (MK_COMB (@lem3855683 _44750) (@lem3855686)). Qed.
Lemma lem3855688 (_44750 : int) : (term148 _44750) = (term152 _44750).
Proof. exact (TRANS (@lem3855672 _44750) (@lem3855687 _44750)). Qed.
Lemma lem3855689 (_44750 : int) : (term78 _44750) = (term152 _44750).
Proof. exact (TRANS (@lem3855669 _44750) (@lem3855688 _44750)). Qed.
Lemma lem3855692 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3855693 (_44749 : int) : (_44749 = term50) = ((real_of_int _44749) = term132).
Proof. exact (@lem3855692 _44749 term50). Qed.
Lemma lem3855697 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3855698 : term132 = term133.
Proof. exact (@lem3855697 (NUMERAL 0)). Qed.
Lemma lem3855699 (_44749 : int) : (term146 _44749) = (term146 _44749).
Proof. exact (eq_refl (term146 _44749)). Qed.
Lemma lem3855700 (_44749 : int) : ((real_of_int _44749) = term132) = ((real_of_int _44749) = term133).
Proof. exact (MK_COMB (@lem3855699 _44749) (@lem3855698)). Qed.
Lemma lem3855702 (_44749 : int) : (_44749 = term50) = ((real_of_int _44749) = term133).
Proof. exact (TRANS (@lem3855693 _44749) (@lem3855700 _44749)). Qed.
Lemma lem3855703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3855704 (_44750 : int) : (term81 _44750) = (term153 _44750).
Proof. exact (MK_COMB (@lem3855703) (@lem3855689 _44750)). Qed.
Lemma lem3855705 (_44750 : int) (_44749 : int) : (term83 _44750 _44749) = (term154 _44750 _44749).
Proof. exact (MK_COMB (@lem3855704 _44750) (@lem3855702 _44749)). Qed.
Lemma lem3855706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3855707 (_44750 : int) (_44749 : int) : (term88 _44750 _44749) = (term155 _44750 _44749).
Proof. exact (MK_COMB (@lem3855706) (@lem3855666 _44750 _44749)). Qed.
Lemma lem3855708 (_44750 : int) (_44749 : int) : (term90 _44750 _44749) = (term156 _44750 _44749).
Proof. exact (MK_COMB (@lem3855707 _44750 _44749) (@lem3855705 _44750 _44749)). Qed.
Lemma lem3855710 (y : int) (x : int) : (term104 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem3855711 (_44750 : int) (_44749 : int) : (term104 _44749 _44750) = (int_le _44750 _44749).
Proof. exact (@lem3855710 _44750 _44749). Qed.
Lemma lem3855713 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3855714 (_44750 : int) (_44749 : int) : (int_le _44750 _44749) = (term129 _44750 _44749).
Proof. exact (@lem3855713 _44750 _44749). Qed.
Lemma lem3855715 (_44750 : int) (_44749 : int) : (term104 _44749 _44750) = (term129 _44750 _44749).
Proof. exact (TRANS (@lem3855711 _44750 _44749) (@lem3855714 _44750 _44749)). Qed.
Lemma lem3855718 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3855719 (_44750 : int) : (_44750 = term50) = ((real_of_int _44750) = term132).
Proof. exact (@lem3855718 _44750 term50). Qed.
Lemma lem3855723 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3855724 : term132 = term133.
Proof. exact (@lem3855723 (NUMERAL 0)). Qed.
Lemma lem3855725 (_44750 : int) : (term146 _44750) = (term146 _44750).
Proof. exact (eq_refl (term146 _44750)). Qed.
Lemma lem3855726 (_44750 : int) : ((real_of_int _44750) = term132) = ((real_of_int _44750) = term133).
Proof. exact (MK_COMB (@lem3855725 _44750) (@lem3855724)). Qed.
Lemma lem3855728 (_44750 : int) : (_44750 = term50) = ((real_of_int _44750) = term133).
Proof. exact (TRANS (@lem3855719 _44750) (@lem3855726 _44750)). Qed.
Lemma lem3855729 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3855730 (_44750 : int) (_44749 : int) : (term94 _44749 _44750) = (term157 _44750 _44749).
Proof. exact (MK_COMB (@lem3855729) (@lem3855715 _44750 _44749)). Qed.
Lemma lem3855731 (_44749 : int) (_44750 : int) : (term96 _44749 _44750) = (term158 _44749 _44750).
Proof. exact (MK_COMB (@lem3855730 _44750 _44749) (@lem3855728 _44750)). Qed.
Lemma lem3855733 (x : int) (y : int) : (int_lt x y) = (term147 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem3855734 (_44749 : int) (_44750 : int) : (int_lt _44749 _44750) = (term147 _44749 _44750).
Proof. exact (@lem3855733 _44749 _44750). Qed.
Lemma lem3855736 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3855737 (_44749 : int) (_44750 : int) : (term147 _44749 _44750) = (term159 _44749 _44750).
Proof. exact (@lem3855736 (term76 _44749) _44750). Qed.
Lemma lem3855739 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3855740 (_44749 : int) : (term137 _44749) = (term140 _44749).
Proof. exact (@lem3855739 _44749 term141). Qed.
Lemma lem3855742 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3855743 : term142 = term143.
Proof. exact (@lem3855742 term11). Qed.
Lemma lem3855744 (_44749 : int) : (term144 _44749) = (term144 _44749).
Proof. exact (eq_refl (term144 _44749)). Qed.
Lemma lem3855745 (_44749 : int) : (term140 _44749) = (term145 _44749).
Proof. exact (MK_COMB (@lem3855744 _44749) (@lem3855743)). Qed.
Lemma lem3855746 (_44749 : int) : (term137 _44749) = (term145 _44749).
Proof. exact (TRANS (@lem3855740 _44749) (@lem3855745 _44749)). Qed.
Lemma lem3855747 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3855748 (_44749 : int) : (term150 _44749) = (term151 _44749).
Proof. exact (MK_COMB (@lem3855747) (@lem3855746 _44749)). Qed.
Lemma lem3855749 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3855750 (_44749 : int) (_44750 : int) : (term159 _44749 _44750) = (term160 _44749 _44750).
Proof. exact (MK_COMB (@lem3855748 _44749) (@lem3855749 _44750)). Qed.
Lemma lem3855751 (_44749 : int) (_44750 : int) : (term147 _44749 _44750) = (term160 _44749 _44750).
Proof. exact (TRANS (@lem3855737 _44749 _44750) (@lem3855750 _44749 _44750)). Qed.
Lemma lem3855752 (_44749 : int) (_44750 : int) : (int_lt _44749 _44750) = (term160 _44749 _44750).
Proof. exact (TRANS (@lem3855734 _44749 _44750) (@lem3855751 _44749 _44750)). Qed.
Lemma lem3855754 (y : int) (x : int) : (term161 x y) = (term162 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem3855755 (_44750 : int) : (term86 _44750) = (term163 _44750).
Proof. exact (@lem3855754 term50 _44750). Qed.
Lemma lem3855757 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3855758 (_44750 : int) : (term164 _44750) = (term165 _44750).
Proof. exact (@lem3855757 (term76 _44750) term50). Qed.
Lemma lem3855760 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3855761 (_44750 : int) : (term137 _44750) = (term140 _44750).
Proof. exact (@lem3855760 _44750 term141). Qed.
Lemma lem3855763 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3855764 : term142 = term143.
Proof. exact (@lem3855763 term11). Qed.
Lemma lem3855765 (_44750 : int) : (term144 _44750) = (term144 _44750).
Proof. exact (eq_refl (term144 _44750)). Qed.
Lemma lem3855766 (_44750 : int) : (term140 _44750) = (term145 _44750).
Proof. exact (MK_COMB (@lem3855765 _44750) (@lem3855764)). Qed.
Lemma lem3855767 (_44750 : int) : (term137 _44750) = (term145 _44750).
Proof. exact (TRANS (@lem3855761 _44750) (@lem3855766 _44750)). Qed.
Lemma lem3855768 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3855769 (_44750 : int) : (term150 _44750) = (term151 _44750).
Proof. exact (MK_COMB (@lem3855768) (@lem3855767 _44750)). Qed.
Lemma lem3855771 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3855772 : term132 = term133.
Proof. exact (@lem3855771 (NUMERAL 0)). Qed.
Lemma lem3855773 (_44750 : int) : (term165 _44750) = (term166 _44750).
Proof. exact (MK_COMB (@lem3855769 _44750) (@lem3855772)). Qed.
Lemma lem3855774 (_44750 : int) : (term164 _44750) = (term166 _44750).
Proof. exact (TRANS (@lem3855758 _44750) (@lem3855773 _44750)). Qed.
Lemma lem3855775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3855776 (_44750 : int) : (term167 _44750) = (term168 _44750).
Proof. exact (MK_COMB (@lem3855775) (@lem3855774 _44750)). Qed.
Lemma lem3855778 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3855779 (_44750 : int) : (term169 _44750) = (term170 _44750).
Proof. exact (@lem3855778 term171 _44750). Qed.
Lemma lem3855781 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3855782 : term172 = term173.
Proof. exact (@lem3855781 term50 term141). Qed.
Lemma lem3855784 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3855785 : term132 = term133.
Proof. exact (@lem3855784 (NUMERAL 0)). Qed.
Lemma lem3855786 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3855787 : term174 = term175.
Proof. exact (MK_COMB (@lem3855786) (@lem3855785)). Qed.
Lemma lem3855789 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3855790 : term142 = term143.
Proof. exact (@lem3855789 term11). Qed.
Lemma lem3855791 : term173 = term176.
Proof. exact (MK_COMB (@lem3855787) (@lem3855790)). Qed.
Lemma lem3855792 : term172 = term176.
Proof. exact (TRANS (@lem3855782) (@lem3855791)). Qed.
Lemma lem3855793 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3855794 : term177 = term178.
Proof. exact (MK_COMB (@lem3855793) (@lem3855792)). Qed.
Lemma lem3855795 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3855796 (_44750 : int) : (term170 _44750) = (term179 _44750).
Proof. exact (MK_COMB (@lem3855794) (@lem3855795 _44750)). Qed.
Lemma lem3855797 (_44750 : int) : (term169 _44750) = (term179 _44750).
Proof. exact (TRANS (@lem3855779 _44750) (@lem3855796 _44750)). Qed.
Lemma lem3855798 (_44750 : int) : (term163 _44750) = (term180 _44750).
Proof. exact (MK_COMB (@lem3855776 _44750) (@lem3855797 _44750)). Qed.
Lemma lem3855799 (_44750 : int) : (term86 _44750) = (term180 _44750).
Proof. exact (TRANS (@lem3855755 _44750) (@lem3855798 _44750)). Qed.
Lemma lem3855800 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3855801 (_44749 : int) (_44750 : int) : (term100 _44749 _44750) = (term181 _44749 _44750).
Proof. exact (MK_COMB (@lem3855800) (@lem3855752 _44749 _44750)). Qed.
Lemma lem3855802 (_44749 : int) (_44750 : int) : (term102 _44749 _44750) = (term182 _44749 _44750).
Proof. exact (MK_COMB (@lem3855801 _44749 _44750) (@lem3855799 _44750)). Qed.
Lemma lem3855803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3855804 (_44749 : int) (_44750 : int) : (term106 _44749 _44750) = (term183 _44749 _44750).
Proof. exact (MK_COMB (@lem3855803) (@lem3855731 _44749 _44750)). Qed.
Lemma lem3855805 (_44749 : int) (_44750 : int) : (term108 _44749 _44750) = (term184 _44749 _44750).
Proof. exact (MK_COMB (@lem3855804 _44749 _44750) (@lem3855802 _44749 _44750)). Qed.
Lemma lem3855806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3855807 (_44750 : int) (_44749 : int) : (term113 _44750 _44749) = (term185 _44750 _44749).
Proof. exact (MK_COMB (@lem3855806) (@lem3855708 _44750 _44749)). Qed.
Lemma lem3855808 (_44749 : int) (_44750 : int) : (term115 _44749 _44750) = (term186 _44749 _44750).
Proof. exact (MK_COMB (@lem3855807 _44750 _44749) (@lem3855805 _44749 _44750)). Qed.
Lemma lem3855809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3855810 (_44750 : int) : (term119 _44750) = (term187 _44750).
Proof. exact (MK_COMB (@lem3855809) (@lem3855647 _44750)). Qed.
Lemma lem3855811 (_44749 : int) (_44750 : int) : (term121 _44749 _44750) = (term188 _44749 _44750).
Proof. exact (MK_COMB (@lem3855810 _44750) (@lem3855808 _44749 _44750)). Qed.
Lemma lem3855812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3855813 (_44749 : int) : (term119 _44749) = (term187 _44749).
Proof. exact (MK_COMB (@lem3855812) (@lem3855634 _44749)). Qed.
Lemma lem3855814 (_44749 : int) (_44750 : int) : (term126 _44749 _44750) = (term189 _44749 _44750).
Proof. exact (MK_COMB (@lem3855813 _44749) (@lem3855811 _44749 _44750)). Qed.
Lemma lem3855815 (_44749 : int) (_44750 : int) : (term127 _44749 _44750) = (term189 _44749 _44750).
Proof. exact (TRANS (@lem3855621 _44749 _44750) (@lem3855814 _44749 _44750)). Qed.
Lemma lem3855819 (t : Prop) : (term190 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3855915 (_44749 : int) (_44750 : int) : (term191 _44749 _44750) = (term189 _44749 _44750).
Proof. exact (@lem3855819 (term189 _44749 _44750)). Qed.
Lemma lem3855916 (_44749 : int) : (term136 _44749) = (term192 _44749).
Proof. exact (@lem1988287 (real_of_int _44749) term133). Qed.
Lemma lem3855922 (_44749 : int) : (term193 _44749) = (term194 _44749).
Proof. exact (@lem1982792 (real_of_int _44749) term133). Qed.
Lemma lem3855924 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3855925 : term133 = term196.
Proof. exact (@lem3855924 (NUMERAL 0)). Qed.
Lemma lem3855927 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3855928 : term199 = term200.
Proof. exact (@lem3855927 term11). Qed.
Lemma lem3855929 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3855930 : term201 = term202.
Proof. exact (MK_COMB (@lem3855929) (@lem3855928)). Qed.
Lemma lem3855931 : term203 = term204.
Proof. exact (MK_COMB (@lem3855930) (@lem3855925)). Qed.
Lemma lem3855932 : term204 = term205.
Proof. exact (@lem1981613 term199 term133 term143 term143). Qed.
Lemma lem3855934 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3855935 : term208 = term209.
Proof. exact (@lem3855934 term11 term11). Qed.
Lemma lem3855936 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3855937 : term211 = term11.
Proof. exact (EQ_MP (@lem3855936) (@lem940073)). Qed.
Lemma lem3855938 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3855939 : term209 = term143.
Proof. exact (MK_COMB (@lem3855938) (@lem3855937)). Qed.
Lemma lem3855940 : term208 = term143.
Proof. exact (TRANS (@lem3855935) (@lem3855939)). Qed.
Lemma lem3855942 (x : nat) : (term212 x) = term133.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3855943 : term203 = term133.
Proof. exact (@lem3855942 term11). Qed.
Lemma lem3855944 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3855945 : term213 = term214.
Proof. exact (MK_COMB (@lem3855944) (@lem3855943)). Qed.
Lemma lem3855946 : term205 = term196.
Proof. exact (MK_COMB (@lem3855945) (@lem3855940)). Qed.
Lemma lem3855947 : term204 = term196.
Proof. exact (TRANS (@lem3855932) (@lem3855946)). Qed.
Lemma lem3855948 : term203 = term196.
Proof. exact (TRANS (@lem3855931) (@lem3855947)). Qed.
Lemma lem3855950 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3855951 : term196 = term133.
Proof. exact (@lem3855950 term133). Qed.
Lemma lem3855952 : term203 = term133.
Proof. exact (TRANS (@lem3855948) (@lem3855951)). Qed.
Lemma lem3855953 (_44749 : int) : (term144 _44749) = (term144 _44749).
Proof. exact (eq_refl (term144 _44749)). Qed.
Lemma lem3855954 (_44749 : int) : (term194 _44749) = (term216 _44749).
Proof. exact (MK_COMB (@lem3855953 _44749) (@lem3855952)). Qed.
Lemma lem3855955 (_44749 : int) : (term216 _44749) = (real_of_int _44749).
Proof. exact (@lem1982723 (real_of_int _44749)). Qed.
Lemma lem3855956 (_44749 : int) : (term194 _44749) = (real_of_int _44749).
Proof. exact (TRANS (@lem3855954 _44749) (@lem3855955 _44749)). Qed.
Lemma lem3855958 (_44749 : int) : (term193 _44749) = (real_of_int _44749).
Proof. exact (TRANS (@lem3855922 _44749) (@lem3855956 _44749)). Qed.
Lemma lem3855959 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3855960 (_44749 : int) : (term217 _44749) = (term218 _44749).
Proof. exact (MK_COMB (@lem3855959) (@lem3855958 _44749)). Qed.
Lemma lem3855961 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3855962 (_44749 : int) : (term192 _44749) = (term219 _44749).
Proof. exact (MK_COMB (@lem3855960 _44749) (@lem3855961)). Qed.
Lemma lem3855963 (_44749 : int) : (term136 _44749) = (term219 _44749).
Proof. exact (TRANS (@lem3855916 _44749) (@lem3855962 _44749)). Qed.
Lemma lem3855964 (_44750 : int) : (term136 _44750) = (term192 _44750).
Proof. exact (@lem1988287 (real_of_int _44750) term133). Qed.
Lemma lem3855970 (_44750 : int) : (term193 _44750) = (term194 _44750).
Proof. exact (@lem1982792 (real_of_int _44750) term133). Qed.
Lemma lem3855972 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3855973 : term133 = term196.
Proof. exact (@lem3855972 (NUMERAL 0)). Qed.
Lemma lem3855975 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3855976 : term199 = term200.
Proof. exact (@lem3855975 term11). Qed.
Lemma lem3855977 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3855978 : term201 = term202.
Proof. exact (MK_COMB (@lem3855977) (@lem3855976)). Qed.
Lemma lem3855979 : term203 = term204.
Proof. exact (MK_COMB (@lem3855978) (@lem3855973)). Qed.
Lemma lem3855980 : term204 = term205.
Proof. exact (@lem1981613 term199 term133 term143 term143). Qed.
Lemma lem3855982 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3855983 : term208 = term209.
Proof. exact (@lem3855982 term11 term11). Qed.
Lemma lem3855984 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3855985 : term211 = term11.
Proof. exact (EQ_MP (@lem3855984) (@lem940073)). Qed.
Lemma lem3855986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3855987 : term209 = term143.
Proof. exact (MK_COMB (@lem3855986) (@lem3855985)). Qed.
Lemma lem3855988 : term208 = term143.
Proof. exact (TRANS (@lem3855983) (@lem3855987)). Qed.
Lemma lem3855990 (x : nat) : (term212 x) = term133.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3855991 : term203 = term133.
Proof. exact (@lem3855990 term11). Qed.
Lemma lem3855992 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3855993 : term213 = term214.
Proof. exact (MK_COMB (@lem3855992) (@lem3855991)). Qed.
Lemma lem3855994 : term205 = term196.
Proof. exact (MK_COMB (@lem3855993) (@lem3855988)). Qed.
Lemma lem3855995 : term204 = term196.
Proof. exact (TRANS (@lem3855980) (@lem3855994)). Qed.
Lemma lem3855996 : term203 = term196.
Proof. exact (TRANS (@lem3855979) (@lem3855995)). Qed.
Lemma lem3855998 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3855999 : term196 = term133.
Proof. exact (@lem3855998 term133). Qed.
Lemma lem3856000 : term203 = term133.
Proof. exact (TRANS (@lem3855996) (@lem3855999)). Qed.
Lemma lem3856001 (_44750 : int) : (term144 _44750) = (term144 _44750).
Proof. exact (eq_refl (term144 _44750)). Qed.
Lemma lem3856002 (_44750 : int) : (term194 _44750) = (term216 _44750).
Proof. exact (MK_COMB (@lem3856001 _44750) (@lem3856000)). Qed.
Lemma lem3856003 (_44750 : int) : (term216 _44750) = (real_of_int _44750).
Proof. exact (@lem1982723 (real_of_int _44750)). Qed.
Lemma lem3856004 (_44750 : int) : (term194 _44750) = (real_of_int _44750).
Proof. exact (TRANS (@lem3856002 _44750) (@lem3856003 _44750)). Qed.
Lemma lem3856006 (_44750 : int) : (term193 _44750) = (real_of_int _44750).
Proof. exact (TRANS (@lem3855970 _44750) (@lem3856004 _44750)). Qed.
Lemma lem3856007 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3856008 (_44750 : int) : (term217 _44750) = (term218 _44750).
Proof. exact (MK_COMB (@lem3856007) (@lem3856006 _44750)). Qed.
Lemma lem3856009 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3856010 (_44750 : int) : (term192 _44750) = (term219 _44750).
Proof. exact (MK_COMB (@lem3856008 _44750) (@lem3856009)). Qed.
Lemma lem3856011 (_44750 : int) : (term136 _44750) = (term219 _44750).
Proof. exact (TRANS (@lem3855964 _44750) (@lem3856010 _44750)). Qed.
Lemma lem3856012 (_44750 : int) (_44749 : int) : ((real_of_int _44750) = (term145 _44749)) = ((term220 _44750 _44749) = term133).
Proof. exact (@lem1988293 (real_of_int _44750) (term145 _44749)). Qed.
Lemma lem3856024 (_44750 : int) (_44749 : int) : (term220 _44750 _44749) = (term221 _44750 _44749).
Proof. exact (@lem1982792 (real_of_int _44750) (term145 _44749)). Qed.
Lemma lem3856025 (_44749 : int) : (term222 _44749) = (term223 _44749).
Proof. exact (@lem1982781 (real_of_int _44749) term199 term143). Qed.
Lemma lem3856027 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3856028 : term143 = term224.
Proof. exact (@lem3856027 term11). Qed.
Lemma lem3856030 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3856031 : term199 = term200.
Proof. exact (@lem3856030 term11). Qed.
Lemma lem3856032 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3856033 : term201 = term202.
Proof. exact (MK_COMB (@lem3856032) (@lem3856031)). Qed.
Lemma lem3856034 : term225 = term226.
Proof. exact (MK_COMB (@lem3856033) (@lem3856028)). Qed.
Lemma lem3856035 : term226 = term227.
Proof. exact (@lem1981613 term199 term143 term143 term143). Qed.
Lemma lem3856037 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3856038 : term208 = term209.
Proof. exact (@lem3856037 term11 term11). Qed.
Lemma lem3856039 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856040 : term211 = term11.
Proof. exact (EQ_MP (@lem3856039) (@lem940073)). Qed.
Lemma lem3856041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856042 : term209 = term143.
Proof. exact (MK_COMB (@lem3856041) (@lem3856040)). Qed.
Lemma lem3856043 : term208 = term143.
Proof. exact (TRANS (@lem3856038) (@lem3856042)). Qed.
Lemma lem3856045 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3856046 : term225 = term230.
Proof. exact (@lem3856045 term11 term11). Qed.
Lemma lem3856047 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856048 : term211 = term11.
Proof. exact (EQ_MP (@lem3856047) (@lem940073)). Qed.
Lemma lem3856049 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856050 : term209 = term143.
Proof. exact (MK_COMB (@lem3856049) (@lem3856048)). Qed.
Lemma lem3856051 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3856052 : term230 = term199.
Proof. exact (MK_COMB (@lem3856051) (@lem3856050)). Qed.
Lemma lem3856053 : term225 = term199.
Proof. exact (TRANS (@lem3856046) (@lem3856052)). Qed.
Lemma lem3856054 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3856055 : term231 = term232.
Proof. exact (MK_COMB (@lem3856054) (@lem3856053)). Qed.
Lemma lem3856056 : term227 = term200.
Proof. exact (MK_COMB (@lem3856055) (@lem3856043)). Qed.
Lemma lem3856057 : term226 = term200.
Proof. exact (TRANS (@lem3856035) (@lem3856056)). Qed.
Lemma lem3856058 : term225 = term200.
Proof. exact (TRANS (@lem3856034) (@lem3856057)). Qed.
Lemma lem3856060 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3856061 : term200 = term199.
Proof. exact (@lem3856060 term199). Qed.
Lemma lem3856062 : term225 = term199.
Proof. exact (TRANS (@lem3856058) (@lem3856061)). Qed.
Lemma lem3856065 (_44749 : int) : (term233 _44749) = (term233 _44749).
Proof. exact (eq_refl (term233 _44749)). Qed.
Lemma lem3856066 (_44749 : int) : (term223 _44749) = (term234 _44749).
Proof. exact (MK_COMB (@lem3856065 _44749) (@lem3856062)). Qed.
Lemma lem3856067 (_44749 : int) : (term222 _44749) = (term234 _44749).
Proof. exact (TRANS (@lem3856025 _44749) (@lem3856066 _44749)). Qed.
Lemma lem3856068 (_44750 : int) : (term144 _44750) = (term144 _44750).
Proof. exact (eq_refl (term144 _44750)). Qed.
Lemma lem3856069 (_44750 : int) (_44749 : int) : (term221 _44750 _44749) = (term235 _44750 _44749).
Proof. exact (MK_COMB (@lem3856068 _44750) (@lem3856067 _44749)). Qed.
Lemma lem3856074 (_44749 : int) (_44750 : int) : (term235 _44750 _44749) = (term236 _44749 _44750).
Proof. exact (@lem1982757 (term237 _44749) (real_of_int _44750) term199). Qed.
Lemma lem3856075 (_44749 : int) (_44750 : int) : (term221 _44750 _44749) = (term236 _44749 _44750).
Proof. exact (TRANS (@lem3856069 _44750 _44749) (@lem3856074 _44749 _44750)). Qed.
Lemma lem3856077 (_44749 : int) (_44750 : int) : (term220 _44750 _44749) = (term236 _44749 _44750).
Proof. exact (TRANS (@lem3856024 _44750 _44749) (@lem3856075 _44749 _44750)). Qed.
Lemma lem3856078 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3856079 (_44749 : int) (_44750 : int) : (term238 _44750 _44749) = (term239 _44749 _44750).
Proof. exact (MK_COMB (@lem3856078) (@lem3856077 _44749 _44750)). Qed.
Lemma lem3856080 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3856081 (_44749 : int) (_44750 : int) : ((term220 _44750 _44749) = term133) = ((term236 _44749 _44750) = term133).
Proof. exact (MK_COMB (@lem3856079 _44749 _44750) (@lem3856080)). Qed.
Lemma lem3856082 (_44749 : int) (_44750 : int) : ((real_of_int _44750) = (term145 _44749)) = ((term236 _44749 _44750) = term133).
Proof. exact (TRANS (@lem3856012 _44750 _44749) (@lem3856081 _44749 _44750)). Qed.
Lemma lem3856083 (_44750 : int) : (term152 _44750) = (term240 _44750).
Proof. exact (@lem1988287 term143 (term145 _44750)). Qed.
Lemma lem3856095 (_44750 : int) : (term241 _44750) = (term242 _44750).
Proof. exact (@lem1982792 term143 (term145 _44750)). Qed.
Lemma lem3856096 (_44750 : int) : (term222 _44750) = (term223 _44750).
Proof. exact (@lem1982781 (real_of_int _44750) term199 term143). Qed.
Lemma lem3856098 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3856099 : term143 = term224.
Proof. exact (@lem3856098 term11). Qed.
Lemma lem3856101 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3856102 : term199 = term200.
Proof. exact (@lem3856101 term11). Qed.
Lemma lem3856103 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3856104 : term201 = term202.
Proof. exact (MK_COMB (@lem3856103) (@lem3856102)). Qed.
Lemma lem3856105 : term225 = term226.
Proof. exact (MK_COMB (@lem3856104) (@lem3856099)). Qed.
Lemma lem3856106 : term226 = term227.
Proof. exact (@lem1981613 term199 term143 term143 term143). Qed.
Lemma lem3856108 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3856109 : term208 = term209.
Proof. exact (@lem3856108 term11 term11). Qed.
Lemma lem3856110 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856111 : term211 = term11.
Proof. exact (EQ_MP (@lem3856110) (@lem940073)). Qed.
Lemma lem3856112 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856113 : term209 = term143.
Proof. exact (MK_COMB (@lem3856112) (@lem3856111)). Qed.
Lemma lem3856114 : term208 = term143.
Proof. exact (TRANS (@lem3856109) (@lem3856113)). Qed.
Lemma lem3856116 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3856117 : term225 = term230.
Proof. exact (@lem3856116 term11 term11). Qed.
Lemma lem3856118 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856119 : term211 = term11.
Proof. exact (EQ_MP (@lem3856118) (@lem940073)). Qed.
Lemma lem3856120 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856121 : term209 = term143.
Proof. exact (MK_COMB (@lem3856120) (@lem3856119)). Qed.
Lemma lem3856122 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3856123 : term230 = term199.
Proof. exact (MK_COMB (@lem3856122) (@lem3856121)). Qed.
Lemma lem3856124 : term225 = term199.
Proof. exact (TRANS (@lem3856117) (@lem3856123)). Qed.
Lemma lem3856125 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3856126 : term231 = term232.
Proof. exact (MK_COMB (@lem3856125) (@lem3856124)). Qed.
Lemma lem3856127 : term227 = term200.
Proof. exact (MK_COMB (@lem3856126) (@lem3856114)). Qed.
Lemma lem3856128 : term226 = term200.
Proof. exact (TRANS (@lem3856106) (@lem3856127)). Qed.
Lemma lem3856129 : term225 = term200.
Proof. exact (TRANS (@lem3856105) (@lem3856128)). Qed.
Lemma lem3856131 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3856132 : term200 = term199.
Proof. exact (@lem3856131 term199). Qed.
Lemma lem3856133 : term225 = term199.
Proof. exact (TRANS (@lem3856129) (@lem3856132)). Qed.
Lemma lem3856136 (_44750 : int) : (term233 _44750) = (term233 _44750).
Proof. exact (eq_refl (term233 _44750)). Qed.
Lemma lem3856137 (_44750 : int) : (term223 _44750) = (term234 _44750).
Proof. exact (MK_COMB (@lem3856136 _44750) (@lem3856133)). Qed.
Lemma lem3856138 (_44750 : int) : (term222 _44750) = (term234 _44750).
Proof. exact (TRANS (@lem3856096 _44750) (@lem3856137 _44750)). Qed.
Lemma lem3856139 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem3856140 (_44750 : int) : (term242 _44750) = (term244 _44750).
Proof. exact (MK_COMB (@lem3856139) (@lem3856138 _44750)). Qed.
Lemma lem3856141 (_44750 : int) : (term244 _44750) = (term245 _44750).
Proof. exact (@lem1982757 (term237 _44750) term143 term199). Qed.
Lemma lem3856143 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3856144 : term199 = term200.
Proof. exact (@lem3856143 term11). Qed.
Lemma lem3856146 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3856147 : term143 = term224.
Proof. exact (@lem3856146 term11). Qed.
Lemma lem3856148 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3856149 : term243 = term246.
Proof. exact (MK_COMB (@lem3856148) (@lem3856147)). Qed.
Lemma lem3856150 : term247 = term248.
Proof. exact (MK_COMB (@lem3856149) (@lem3856144)). Qed.
Lemma lem3856151 : term249.
Proof. exact (@lem1981473 term143 term143 term199 term143 term133 term143). Qed.
Lemma lem3856153 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3856154 : term251 = term252.
Proof. exact (@lem3856153 (NUMERAL 0) term11). Qed.
Lemma lem3856155 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3856156 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3856157 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3856156 h1) (fun h1 : term252 = True => @lem3856155)). Qed.
Lemma lem3856158 : term252 = True.
Proof. exact (EQ_MP (@lem3856157) (@lem3856155)). Qed.
Lemma lem3856159 : term251 = True.
Proof. exact (TRANS (@lem3856154) (@lem3856158)). Qed.
Lemma lem3856160 : True = term251.
Proof. exact (SYM (@lem3856159)). Qed.
Lemma lem3856161 : term251.
Proof. exact (EQ_MP (@lem3856160) (@lem0)). Qed.
Lemma lem3856162 : term254.
Proof. exact (@lem3856151 (@lem3856161)). Qed.
Lemma lem3856164 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3856165 : term251 = term252.
Proof. exact (@lem3856164 (NUMERAL 0) term11). Qed.
Lemma lem3856166 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3856167 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3856168 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3856167 h1) (fun h1 : term252 = True => @lem3856166)). Qed.
Lemma lem3856169 : term252 = True.
Proof. exact (EQ_MP (@lem3856168) (@lem3856166)). Qed.
Lemma lem3856170 : term251 = True.
Proof. exact (TRANS (@lem3856165) (@lem3856169)). Qed.
Lemma lem3856171 : True = term251.
Proof. exact (SYM (@lem3856170)). Qed.
Lemma lem3856172 : term251.
Proof. exact (EQ_MP (@lem3856171) (@lem0)). Qed.
Lemma lem3856173 : term255.
Proof. exact (@lem3856162 (@lem3856172)). Qed.
Lemma lem3856175 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3856176 : term251 = term252.
Proof. exact (@lem3856175 (NUMERAL 0) term11). Qed.
Lemma lem3856177 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3856178 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3856179 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3856178 h1) (fun h1 : term252 = True => @lem3856177)). Qed.
Lemma lem3856180 : term252 = True.
Proof. exact (EQ_MP (@lem3856179) (@lem3856177)). Qed.
Lemma lem3856181 : term251 = True.
Proof. exact (TRANS (@lem3856176) (@lem3856180)). Qed.
Lemma lem3856182 : True = term251.
Proof. exact (SYM (@lem3856181)). Qed.
Lemma lem3856183 : term251.
Proof. exact (EQ_MP (@lem3856182) (@lem0)). Qed.
Lemma lem3856184 : term256.
Proof. exact (@lem3856173 (@lem3856183)). Qed.
Lemma lem3856186 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3856187 : term225 = term230.
Proof. exact (@lem3856186 term11 term11). Qed.
Lemma lem3856188 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856189 : term211 = term11.
Proof. exact (EQ_MP (@lem3856188) (@lem940073)). Qed.
Lemma lem3856190 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856191 : term209 = term143.
Proof. exact (MK_COMB (@lem3856190) (@lem3856189)). Qed.
Lemma lem3856192 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3856193 : term230 = term199.
Proof. exact (MK_COMB (@lem3856192) (@lem3856191)). Qed.
Lemma lem3856194 : term225 = term199.
Proof. exact (TRANS (@lem3856187) (@lem3856193)). Qed.
Lemma lem3856196 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3856197 : term208 = term209.
Proof. exact (@lem3856196 term11 term11). Qed.
Lemma lem3856198 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856199 : term211 = term11.
Proof. exact (EQ_MP (@lem3856198) (@lem940073)). Qed.
Lemma lem3856200 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856201 : term209 = term143.
Proof. exact (MK_COMB (@lem3856200) (@lem3856199)). Qed.
Lemma lem3856202 : term208 = term143.
Proof. exact (TRANS (@lem3856197) (@lem3856201)). Qed.
Lemma lem3856203 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3856204 : term257 = term243.
Proof. exact (MK_COMB (@lem3856203) (@lem3856202)). Qed.
Lemma lem3856205 : term258 = term247.
Proof. exact (MK_COMB (@lem3856204) (@lem3856194)). Qed.
Lemma lem3856207 (m : nat) : (term259 m) = term133.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem3856208 : term247 = term133.
Proof. exact (@lem3856207 term11). Qed.
Lemma lem3856209 : term258 = term133.
Proof. exact (TRANS (@lem3856205) (@lem3856208)). Qed.
Lemma lem3856210 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3856211 : term260 = term261.
Proof. exact (MK_COMB (@lem3856210) (@lem3856209)). Qed.
Lemma lem3856212 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3856213 : term262 = term263.
Proof. exact (MK_COMB (@lem3856211) (@lem3856212)). Qed.
Lemma lem3856215 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3856216 : term263 = term133.
Proof. exact (@lem3856215 term11). Qed.
Lemma lem3856217 : term262 = term133.
Proof. exact (TRANS (@lem3856213) (@lem3856216)). Qed.
Lemma lem3856219 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3856220 : term208 = term209.
Proof. exact (@lem3856219 term11 term11). Qed.
Lemma lem3856221 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856222 : term211 = term11.
Proof. exact (EQ_MP (@lem3856221) (@lem940073)). Qed.
Lemma lem3856223 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856224 : term209 = term143.
Proof. exact (MK_COMB (@lem3856223) (@lem3856222)). Qed.
Lemma lem3856225 : term208 = term143.
Proof. exact (TRANS (@lem3856220) (@lem3856224)). Qed.
Lemma lem3856226 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3856227 : term265 = term263.
Proof. exact (MK_COMB (@lem3856226) (@lem3856225)). Qed.
Lemma lem3856229 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3856230 : term263 = term133.
Proof. exact (@lem3856229 term11). Qed.
Lemma lem3856231 : term265 = term133.
Proof. exact (TRANS (@lem3856227) (@lem3856230)). Qed.
Lemma lem3856232 : term133 = term265.
Proof. exact (SYM (@lem3856231)). Qed.
Lemma lem3856233 : term262 = term265.
Proof. exact (TRANS (@lem3856217) (@lem3856232)). Qed.
Lemma lem3856234 : term248 = term196.
Proof. exact (@lem3856184 (@lem3856233)). Qed.
Lemma lem3856235 : term247 = term196.
Proof. exact (TRANS (@lem3856150) (@lem3856234)). Qed.
Lemma lem3856237 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3856238 : term196 = term133.
Proof. exact (@lem3856237 term133). Qed.
Lemma lem3856239 : term247 = term133.
Proof. exact (TRANS (@lem3856235) (@lem3856238)). Qed.
Lemma lem3856240 (_44750 : int) : (term233 _44750) = (term233 _44750).
Proof. exact (eq_refl (term233 _44750)). Qed.
Lemma lem3856241 (_44750 : int) : (term245 _44750) = (term266 _44750).
Proof. exact (MK_COMB (@lem3856240 _44750) (@lem3856239)). Qed.
Lemma lem3856242 (_44750 : int) : (term244 _44750) = (term266 _44750).
Proof. exact (TRANS (@lem3856141 _44750) (@lem3856241 _44750)). Qed.
Lemma lem3856243 (_44750 : int) : (term266 _44750) = (term237 _44750).
Proof. exact (@lem1982723 (term237 _44750)). Qed.
Lemma lem3856244 (_44750 : int) : (term244 _44750) = (term237 _44750).
Proof. exact (TRANS (@lem3856242 _44750) (@lem3856243 _44750)). Qed.
Lemma lem3856245 (_44750 : int) : (term242 _44750) = (term237 _44750).
Proof. exact (TRANS (@lem3856140 _44750) (@lem3856244 _44750)). Qed.
Lemma lem3856247 (_44750 : int) : (term241 _44750) = (term237 _44750).
Proof. exact (TRANS (@lem3856095 _44750) (@lem3856245 _44750)). Qed.
Lemma lem3856248 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3856249 (_44750 : int) : (term267 _44750) = (term268 _44750).
Proof. exact (MK_COMB (@lem3856248) (@lem3856247 _44750)). Qed.
Lemma lem3856250 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3856251 (_44750 : int) : (term240 _44750) = (term269 _44750).
Proof. exact (MK_COMB (@lem3856249 _44750) (@lem3856250)). Qed.
Lemma lem3856252 (_44750 : int) : (term152 _44750) = (term269 _44750).
Proof. exact (TRANS (@lem3856083 _44750) (@lem3856251 _44750)). Qed.
Lemma lem3856253 (_44749 : int) : ((real_of_int _44749) = term133) = ((term193 _44749) = term133).
Proof. exact (@lem1988293 (real_of_int _44749) term133). Qed.
Lemma lem3856259 (_44749 : int) : (term193 _44749) = (term194 _44749).
Proof. exact (@lem1982792 (real_of_int _44749) term133). Qed.
Lemma lem3856261 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3856262 : term133 = term196.
Proof. exact (@lem3856261 (NUMERAL 0)). Qed.
Lemma lem3856264 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3856265 : term199 = term200.
Proof. exact (@lem3856264 term11). Qed.
Lemma lem3856266 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3856267 : term201 = term202.
Proof. exact (MK_COMB (@lem3856266) (@lem3856265)). Qed.
Lemma lem3856268 : term203 = term204.
Proof. exact (MK_COMB (@lem3856267) (@lem3856262)). Qed.
Lemma lem3856269 : term204 = term205.
Proof. exact (@lem1981613 term199 term133 term143 term143). Qed.
Lemma lem3856271 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3856272 : term208 = term209.
Proof. exact (@lem3856271 term11 term11). Qed.
Lemma lem3856273 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856274 : term211 = term11.
Proof. exact (EQ_MP (@lem3856273) (@lem940073)). Qed.
Lemma lem3856275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856276 : term209 = term143.
Proof. exact (MK_COMB (@lem3856275) (@lem3856274)). Qed.
Lemma lem3856277 : term208 = term143.
Proof. exact (TRANS (@lem3856272) (@lem3856276)). Qed.
Lemma lem3856279 (x : nat) : (term212 x) = term133.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3856280 : term203 = term133.
Proof. exact (@lem3856279 term11). Qed.
Lemma lem3856281 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3856282 : term213 = term214.
Proof. exact (MK_COMB (@lem3856281) (@lem3856280)). Qed.
Lemma lem3856283 : term205 = term196.
Proof. exact (MK_COMB (@lem3856282) (@lem3856277)). Qed.
Lemma lem3856284 : term204 = term196.
Proof. exact (TRANS (@lem3856269) (@lem3856283)). Qed.
Lemma lem3856285 : term203 = term196.
Proof. exact (TRANS (@lem3856268) (@lem3856284)). Qed.
Lemma lem3856287 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3856288 : term196 = term133.
Proof. exact (@lem3856287 term133). Qed.
Lemma lem3856289 : term203 = term133.
Proof. exact (TRANS (@lem3856285) (@lem3856288)). Qed.
Lemma lem3856290 (_44749 : int) : (term144 _44749) = (term144 _44749).
Proof. exact (eq_refl (term144 _44749)). Qed.
Lemma lem3856291 (_44749 : int) : (term194 _44749) = (term216 _44749).
Proof. exact (MK_COMB (@lem3856290 _44749) (@lem3856289)). Qed.
Lemma lem3856292 (_44749 : int) : (term216 _44749) = (real_of_int _44749).
Proof. exact (@lem1982723 (real_of_int _44749)). Qed.
Lemma lem3856293 (_44749 : int) : (term194 _44749) = (real_of_int _44749).
Proof. exact (TRANS (@lem3856291 _44749) (@lem3856292 _44749)). Qed.
Lemma lem3856295 (_44749 : int) : (term193 _44749) = (real_of_int _44749).
Proof. exact (TRANS (@lem3856259 _44749) (@lem3856293 _44749)). Qed.
Lemma lem3856296 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3856297 (_44749 : int) : (term270 _44749) = (term146 _44749).
Proof. exact (MK_COMB (@lem3856296) (@lem3856295 _44749)). Qed.
Lemma lem3856298 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3856299 (_44749 : int) : ((term193 _44749) = term133) = ((real_of_int _44749) = term133).
Proof. exact (MK_COMB (@lem3856297 _44749) (@lem3856298)). Qed.
Lemma lem3856300 (_44749 : int) : ((real_of_int _44749) = term133) = ((real_of_int _44749) = term133).
Proof. exact (TRANS (@lem3856253 _44749) (@lem3856299 _44749)). Qed.
Lemma lem3856301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3856302 (_44750 : int) : (term153 _44750) = (term271 _44750).
Proof. exact (MK_COMB (@lem3856301) (@lem3856252 _44750)). Qed.
Lemma lem3856303 (_44750 : int) (_44749 : int) : (term154 _44750 _44749) = (term272 _44750 _44749).
Proof. exact (MK_COMB (@lem3856302 _44750) (@lem3856300 _44749)). Qed.
Lemma lem3856304 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856305 (_44749 : int) (_44750 : int) : (term155 _44750 _44749) = (term273 _44749 _44750).
Proof. exact (MK_COMB (@lem3856304) (@lem3856082 _44749 _44750)). Qed.
Lemma lem3856306 (_44750 : int) (_44749 : int) : (term156 _44750 _44749) = (term274 _44750 _44749).
Proof. exact (MK_COMB (@lem3856305 _44749 _44750) (@lem3856303 _44750 _44749)). Qed.
Lemma lem3856307 (_44749 : int) (_44750 : int) : (term129 _44750 _44749) = (term275 _44749 _44750).
Proof. exact (@lem1988287 (real_of_int _44749) (real_of_int _44750)). Qed.
Lemma lem3856320 (_44749 : int) (_44750 : int) : (term276 _44749 _44750) = (term277 _44749 _44750).
Proof. exact (@lem1982792 (real_of_int _44749) (real_of_int _44750)). Qed.
Lemma lem3856321 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3856322 (_44749 : int) (_44750 : int) : (term278 _44749 _44750) = (term279 _44749 _44750).
Proof. exact (MK_COMB (@lem3856321) (@lem3856320 _44749 _44750)). Qed.
Lemma lem3856323 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3856324 (_44749 : int) (_44750 : int) : (term275 _44749 _44750) = (term280 _44749 _44750).
Proof. exact (MK_COMB (@lem3856322 _44749 _44750) (@lem3856323)). Qed.
Lemma lem3856325 (_44749 : int) (_44750 : int) : (term129 _44750 _44749) = (term280 _44749 _44750).
Proof. exact (TRANS (@lem3856307 _44749 _44750) (@lem3856324 _44749 _44750)). Qed.
Lemma lem3856326 (_44750 : int) : ((real_of_int _44750) = term133) = ((term193 _44750) = term133).
Proof. exact (@lem1988293 (real_of_int _44750) term133). Qed.
Lemma lem3856332 (_44750 : int) : (term193 _44750) = (term194 _44750).
Proof. exact (@lem1982792 (real_of_int _44750) term133). Qed.
Lemma lem3856334 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3856335 : term133 = term196.
Proof. exact (@lem3856334 (NUMERAL 0)). Qed.
Lemma lem3856337 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3856338 : term199 = term200.
Proof. exact (@lem3856337 term11). Qed.
Lemma lem3856339 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3856340 : term201 = term202.
Proof. exact (MK_COMB (@lem3856339) (@lem3856338)). Qed.
Lemma lem3856341 : term203 = term204.
Proof. exact (MK_COMB (@lem3856340) (@lem3856335)). Qed.
Lemma lem3856342 : term204 = term205.
Proof. exact (@lem1981613 term199 term133 term143 term143). Qed.
Lemma lem3856344 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3856345 : term208 = term209.
Proof. exact (@lem3856344 term11 term11). Qed.
Lemma lem3856346 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856347 : term211 = term11.
Proof. exact (EQ_MP (@lem3856346) (@lem940073)). Qed.
Lemma lem3856348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856349 : term209 = term143.
Proof. exact (MK_COMB (@lem3856348) (@lem3856347)). Qed.
Lemma lem3856350 : term208 = term143.
Proof. exact (TRANS (@lem3856345) (@lem3856349)). Qed.
Lemma lem3856352 (x : nat) : (term212 x) = term133.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3856353 : term203 = term133.
Proof. exact (@lem3856352 term11). Qed.
Lemma lem3856354 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3856355 : term213 = term214.
Proof. exact (MK_COMB (@lem3856354) (@lem3856353)). Qed.
Lemma lem3856356 : term205 = term196.
Proof. exact (MK_COMB (@lem3856355) (@lem3856350)). Qed.
Lemma lem3856357 : term204 = term196.
Proof. exact (TRANS (@lem3856342) (@lem3856356)). Qed.
Lemma lem3856358 : term203 = term196.
Proof. exact (TRANS (@lem3856341) (@lem3856357)). Qed.
Lemma lem3856360 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3856361 : term196 = term133.
Proof. exact (@lem3856360 term133). Qed.
Lemma lem3856362 : term203 = term133.
Proof. exact (TRANS (@lem3856358) (@lem3856361)). Qed.
Lemma lem3856363 (_44750 : int) : (term144 _44750) = (term144 _44750).
Proof. exact (eq_refl (term144 _44750)). Qed.
Lemma lem3856364 (_44750 : int) : (term194 _44750) = (term216 _44750).
Proof. exact (MK_COMB (@lem3856363 _44750) (@lem3856362)). Qed.
Lemma lem3856365 (_44750 : int) : (term216 _44750) = (real_of_int _44750).
Proof. exact (@lem1982723 (real_of_int _44750)). Qed.
Lemma lem3856366 (_44750 : int) : (term194 _44750) = (real_of_int _44750).
Proof. exact (TRANS (@lem3856364 _44750) (@lem3856365 _44750)). Qed.
Lemma lem3856368 (_44750 : int) : (term193 _44750) = (real_of_int _44750).
Proof. exact (TRANS (@lem3856332 _44750) (@lem3856366 _44750)). Qed.
Lemma lem3856369 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3856370 (_44750 : int) : (term270 _44750) = (term146 _44750).
Proof. exact (MK_COMB (@lem3856369) (@lem3856368 _44750)). Qed.
Lemma lem3856371 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3856372 (_44750 : int) : ((term193 _44750) = term133) = ((real_of_int _44750) = term133).
Proof. exact (MK_COMB (@lem3856370 _44750) (@lem3856371)). Qed.
Lemma lem3856373 (_44750 : int) : ((real_of_int _44750) = term133) = ((real_of_int _44750) = term133).
Proof. exact (TRANS (@lem3856326 _44750) (@lem3856372 _44750)). Qed.
Lemma lem3856374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856375 (_44749 : int) (_44750 : int) : (term157 _44750 _44749) = (term281 _44749 _44750).
Proof. exact (MK_COMB (@lem3856374) (@lem3856325 _44749 _44750)). Qed.
Lemma lem3856376 (_44749 : int) (_44750 : int) : (term158 _44749 _44750) = (term282 _44749 _44750).
Proof. exact (MK_COMB (@lem3856375 _44749 _44750) (@lem3856373 _44750)). Qed.
Lemma lem3856377 (_44750 : int) (_44749 : int) : (term160 _44749 _44750) = (term283 _44750 _44749).
Proof. exact (@lem1988287 (real_of_int _44750) (term145 _44749)). Qed.
Lemma lem3856389 (_44750 : int) (_44749 : int) : (term220 _44750 _44749) = (term221 _44750 _44749).
Proof. exact (@lem1982792 (real_of_int _44750) (term145 _44749)). Qed.
Lemma lem3856390 (_44749 : int) : (term222 _44749) = (term223 _44749).
Proof. exact (@lem1982781 (real_of_int _44749) term199 term143). Qed.
Lemma lem3856392 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3856393 : term143 = term224.
Proof. exact (@lem3856392 term11). Qed.
Lemma lem3856395 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3856396 : term199 = term200.
Proof. exact (@lem3856395 term11). Qed.
Lemma lem3856397 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3856398 : term201 = term202.
Proof. exact (MK_COMB (@lem3856397) (@lem3856396)). Qed.
Lemma lem3856399 : term225 = term226.
Proof. exact (MK_COMB (@lem3856398) (@lem3856393)). Qed.
Lemma lem3856400 : term226 = term227.
Proof. exact (@lem1981613 term199 term143 term143 term143). Qed.
Lemma lem3856402 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3856403 : term208 = term209.
Proof. exact (@lem3856402 term11 term11). Qed.
Lemma lem3856404 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856405 : term211 = term11.
Proof. exact (EQ_MP (@lem3856404) (@lem940073)). Qed.
Lemma lem3856406 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856407 : term209 = term143.
Proof. exact (MK_COMB (@lem3856406) (@lem3856405)). Qed.
Lemma lem3856408 : term208 = term143.
Proof. exact (TRANS (@lem3856403) (@lem3856407)). Qed.
Lemma lem3856410 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3856411 : term225 = term230.
Proof. exact (@lem3856410 term11 term11). Qed.
Lemma lem3856412 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856413 : term211 = term11.
Proof. exact (EQ_MP (@lem3856412) (@lem940073)). Qed.
Lemma lem3856414 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856415 : term209 = term143.
Proof. exact (MK_COMB (@lem3856414) (@lem3856413)). Qed.
Lemma lem3856416 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3856417 : term230 = term199.
Proof. exact (MK_COMB (@lem3856416) (@lem3856415)). Qed.
Lemma lem3856418 : term225 = term199.
Proof. exact (TRANS (@lem3856411) (@lem3856417)). Qed.
Lemma lem3856419 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3856420 : term231 = term232.
Proof. exact (MK_COMB (@lem3856419) (@lem3856418)). Qed.
Lemma lem3856421 : term227 = term200.
Proof. exact (MK_COMB (@lem3856420) (@lem3856408)). Qed.
Lemma lem3856422 : term226 = term200.
Proof. exact (TRANS (@lem3856400) (@lem3856421)). Qed.
Lemma lem3856423 : term225 = term200.
Proof. exact (TRANS (@lem3856399) (@lem3856422)). Qed.
Lemma lem3856425 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3856426 : term200 = term199.
Proof. exact (@lem3856425 term199). Qed.
Lemma lem3856427 : term225 = term199.
Proof. exact (TRANS (@lem3856423) (@lem3856426)). Qed.
Lemma lem3856430 (_44749 : int) : (term233 _44749) = (term233 _44749).
Proof. exact (eq_refl (term233 _44749)). Qed.
Lemma lem3856431 (_44749 : int) : (term223 _44749) = (term234 _44749).
Proof. exact (MK_COMB (@lem3856430 _44749) (@lem3856427)). Qed.
Lemma lem3856432 (_44749 : int) : (term222 _44749) = (term234 _44749).
Proof. exact (TRANS (@lem3856390 _44749) (@lem3856431 _44749)). Qed.
Lemma lem3856433 (_44750 : int) : (term144 _44750) = (term144 _44750).
Proof. exact (eq_refl (term144 _44750)). Qed.
Lemma lem3856434 (_44750 : int) (_44749 : int) : (term221 _44750 _44749) = (term235 _44750 _44749).
Proof. exact (MK_COMB (@lem3856433 _44750) (@lem3856432 _44749)). Qed.
Lemma lem3856439 (_44749 : int) (_44750 : int) : (term235 _44750 _44749) = (term236 _44749 _44750).
Proof. exact (@lem1982757 (term237 _44749) (real_of_int _44750) term199). Qed.
Lemma lem3856440 (_44749 : int) (_44750 : int) : (term221 _44750 _44749) = (term236 _44749 _44750).
Proof. exact (TRANS (@lem3856434 _44750 _44749) (@lem3856439 _44749 _44750)). Qed.
Lemma lem3856442 (_44749 : int) (_44750 : int) : (term220 _44750 _44749) = (term236 _44749 _44750).
Proof. exact (TRANS (@lem3856389 _44750 _44749) (@lem3856440 _44749 _44750)). Qed.
Lemma lem3856443 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3856444 (_44749 : int) (_44750 : int) : (term284 _44750 _44749) = (term285 _44749 _44750).
Proof. exact (MK_COMB (@lem3856443) (@lem3856442 _44749 _44750)). Qed.
Lemma lem3856445 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3856446 (_44749 : int) (_44750 : int) : (term283 _44750 _44749) = (term286 _44749 _44750).
Proof. exact (MK_COMB (@lem3856444 _44749 _44750) (@lem3856445)). Qed.
Lemma lem3856447 (_44749 : int) (_44750 : int) : (term160 _44749 _44750) = (term286 _44749 _44750).
Proof. exact (TRANS (@lem3856377 _44750 _44749) (@lem3856446 _44749 _44750)). Qed.
Lemma lem3856448 (_44750 : int) : (term166 _44750) = (term287 _44750).
Proof. exact (@lem1988287 term133 (term145 _44750)). Qed.
Lemma lem3856460 (_44750 : int) : (term288 _44750) = (term289 _44750).
Proof. exact (@lem1982792 term133 (term145 _44750)). Qed.
Lemma lem3856461 (_44750 : int) : (term222 _44750) = (term223 _44750).
Proof. exact (@lem1982781 (real_of_int _44750) term199 term143). Qed.
Lemma lem3856463 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3856464 : term143 = term224.
Proof. exact (@lem3856463 term11). Qed.
Lemma lem3856466 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3856467 : term199 = term200.
Proof. exact (@lem3856466 term11). Qed.
Lemma lem3856468 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3856469 : term201 = term202.
Proof. exact (MK_COMB (@lem3856468) (@lem3856467)). Qed.
Lemma lem3856470 : term225 = term226.
Proof. exact (MK_COMB (@lem3856469) (@lem3856464)). Qed.
Lemma lem3856471 : term226 = term227.
Proof. exact (@lem1981613 term199 term143 term143 term143). Qed.
Lemma lem3856473 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3856474 : term208 = term209.
Proof. exact (@lem3856473 term11 term11). Qed.
Lemma lem3856475 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856476 : term211 = term11.
Proof. exact (EQ_MP (@lem3856475) (@lem940073)). Qed.
Lemma lem3856477 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856478 : term209 = term143.
Proof. exact (MK_COMB (@lem3856477) (@lem3856476)). Qed.
Lemma lem3856479 : term208 = term143.
Proof. exact (TRANS (@lem3856474) (@lem3856478)). Qed.
Lemma lem3856481 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3856482 : term225 = term230.
Proof. exact (@lem3856481 term11 term11). Qed.
Lemma lem3856483 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856484 : term211 = term11.
Proof. exact (EQ_MP (@lem3856483) (@lem940073)). Qed.
Lemma lem3856485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856486 : term209 = term143.
Proof. exact (MK_COMB (@lem3856485) (@lem3856484)). Qed.
Lemma lem3856487 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3856488 : term230 = term199.
Proof. exact (MK_COMB (@lem3856487) (@lem3856486)). Qed.
Lemma lem3856489 : term225 = term199.
Proof. exact (TRANS (@lem3856482) (@lem3856488)). Qed.
Lemma lem3856490 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3856491 : term231 = term232.
Proof. exact (MK_COMB (@lem3856490) (@lem3856489)). Qed.
Lemma lem3856492 : term227 = term200.
Proof. exact (MK_COMB (@lem3856491) (@lem3856479)). Qed.
Lemma lem3856493 : term226 = term200.
Proof. exact (TRANS (@lem3856471) (@lem3856492)). Qed.
Lemma lem3856494 : term225 = term200.
Proof. exact (TRANS (@lem3856470) (@lem3856493)). Qed.
Lemma lem3856496 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3856497 : term200 = term199.
Proof. exact (@lem3856496 term199). Qed.
Lemma lem3856498 : term225 = term199.
Proof. exact (TRANS (@lem3856494) (@lem3856497)). Qed.
Lemma lem3856501 (_44750 : int) : (term233 _44750) = (term233 _44750).
Proof. exact (eq_refl (term233 _44750)). Qed.
Lemma lem3856502 (_44750 : int) : (term223 _44750) = (term234 _44750).
Proof. exact (MK_COMB (@lem3856501 _44750) (@lem3856498)). Qed.
Lemma lem3856503 (_44750 : int) : (term222 _44750) = (term234 _44750).
Proof. exact (TRANS (@lem3856461 _44750) (@lem3856502 _44750)). Qed.
Lemma lem3856504 : term175 = term175.
Proof. exact (eq_refl term175). Qed.
Lemma lem3856505 (_44750 : int) : (term289 _44750) = (term290 _44750).
Proof. exact (MK_COMB (@lem3856504) (@lem3856503 _44750)). Qed.
Lemma lem3856506 (_44750 : int) : (term290 _44750) = (term234 _44750).
Proof. exact (@lem1982721 (term234 _44750)). Qed.
Lemma lem3856507 (_44750 : int) : (term289 _44750) = (term234 _44750).
Proof. exact (TRANS (@lem3856505 _44750) (@lem3856506 _44750)). Qed.
Lemma lem3856509 (_44750 : int) : (term288 _44750) = (term234 _44750).
Proof. exact (TRANS (@lem3856460 _44750) (@lem3856507 _44750)). Qed.
Lemma lem3856510 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3856511 (_44750 : int) : (term291 _44750) = (term292 _44750).
Proof. exact (MK_COMB (@lem3856510) (@lem3856509 _44750)). Qed.
Lemma lem3856512 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3856513 (_44750 : int) : (term287 _44750) = (term293 _44750).
Proof. exact (MK_COMB (@lem3856511 _44750) (@lem3856512)). Qed.
Lemma lem3856514 (_44750 : int) : (term166 _44750) = (term293 _44750).
Proof. exact (TRANS (@lem3856448 _44750) (@lem3856513 _44750)). Qed.
Lemma lem3856515 (_44750 : int) : (term179 _44750) = (term294 _44750).
Proof. exact (@lem1988287 (real_of_int _44750) term176). Qed.
Lemma lem3856522 : term176 = term143.
Proof. exact (@lem1982721 term143). Qed.
Lemma lem3856525 (_44750 : int) : (term295 _44750) = (term295 _44750).
Proof. exact (eq_refl (term295 _44750)). Qed.
Lemma lem3856526 (_44750 : int) : (term296 _44750) = (term297 _44750).
Proof. exact (MK_COMB (@lem3856525 _44750) (@lem3856522)). Qed.
Lemma lem3856527 (_44750 : int) : (term297 _44750) = (term298 _44750).
Proof. exact (@lem1982792 (real_of_int _44750) term143). Qed.
Lemma lem3856529 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3856530 : term143 = term224.
Proof. exact (@lem3856529 term11). Qed.
Lemma lem3856532 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3856533 : term199 = term200.
Proof. exact (@lem3856532 term11). Qed.
Lemma lem3856534 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3856535 : term201 = term202.
Proof. exact (MK_COMB (@lem3856534) (@lem3856533)). Qed.
Lemma lem3856536 : term225 = term226.
Proof. exact (MK_COMB (@lem3856535) (@lem3856530)). Qed.
Lemma lem3856537 : term226 = term227.
Proof. exact (@lem1981613 term199 term143 term143 term143). Qed.
Lemma lem3856539 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3856540 : term208 = term209.
Proof. exact (@lem3856539 term11 term11). Qed.
Lemma lem3856541 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856542 : term211 = term11.
Proof. exact (EQ_MP (@lem3856541) (@lem940073)). Qed.
Lemma lem3856543 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856544 : term209 = term143.
Proof. exact (MK_COMB (@lem3856543) (@lem3856542)). Qed.
Lemma lem3856545 : term208 = term143.
Proof. exact (TRANS (@lem3856540) (@lem3856544)). Qed.
Lemma lem3856547 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3856548 : term225 = term230.
Proof. exact (@lem3856547 term11 term11). Qed.
Lemma lem3856549 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856550 : term211 = term11.
Proof. exact (EQ_MP (@lem3856549) (@lem940073)). Qed.
Lemma lem3856551 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856552 : term209 = term143.
Proof. exact (MK_COMB (@lem3856551) (@lem3856550)). Qed.
Lemma lem3856553 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3856554 : term230 = term199.
Proof. exact (MK_COMB (@lem3856553) (@lem3856552)). Qed.
Lemma lem3856555 : term225 = term199.
Proof. exact (TRANS (@lem3856548) (@lem3856554)). Qed.
Lemma lem3856556 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3856557 : term231 = term232.
Proof. exact (MK_COMB (@lem3856556) (@lem3856555)). Qed.
Lemma lem3856558 : term227 = term200.
Proof. exact (MK_COMB (@lem3856557) (@lem3856545)). Qed.
Lemma lem3856559 : term226 = term200.
Proof. exact (TRANS (@lem3856537) (@lem3856558)). Qed.
Lemma lem3856560 : term225 = term200.
Proof. exact (TRANS (@lem3856536) (@lem3856559)). Qed.
Lemma lem3856562 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3856563 : term200 = term199.
Proof. exact (@lem3856562 term199). Qed.
Lemma lem3856564 : term225 = term199.
Proof. exact (TRANS (@lem3856560) (@lem3856563)). Qed.
Lemma lem3856565 (_44750 : int) : (term144 _44750) = (term144 _44750).
Proof. exact (eq_refl (term144 _44750)). Qed.
Lemma lem3856568 (_44750 : int) : (term298 _44750) = (term299 _44750).
Proof. exact (MK_COMB (@lem3856565 _44750) (@lem3856564)). Qed.
Lemma lem3856569 (_44750 : int) : (term297 _44750) = (term299 _44750).
Proof. exact (TRANS (@lem3856527 _44750) (@lem3856568 _44750)). Qed.
Lemma lem3856570 (_44750 : int) : (term296 _44750) = (term299 _44750).
Proof. exact (TRANS (@lem3856526 _44750) (@lem3856569 _44750)). Qed.
Lemma lem3856571 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3856572 (_44750 : int) : (term300 _44750) = (term301 _44750).
Proof. exact (MK_COMB (@lem3856571) (@lem3856570 _44750)). Qed.
Lemma lem3856573 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3856574 (_44750 : int) : (term294 _44750) = (term302 _44750).
Proof. exact (MK_COMB (@lem3856572 _44750) (@lem3856573)). Qed.
Lemma lem3856575 (_44750 : int) : (term179 _44750) = (term302 _44750).
Proof. exact (TRANS (@lem3856515 _44750) (@lem3856574 _44750)). Qed.
Lemma lem3856576 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856577 (_44750 : int) : (term168 _44750) = (term303 _44750).
Proof. exact (MK_COMB (@lem3856576) (@lem3856514 _44750)). Qed.
Lemma lem3856578 (_44750 : int) : (term180 _44750) = (term304 _44750).
Proof. exact (MK_COMB (@lem3856577 _44750) (@lem3856575 _44750)). Qed.
Lemma lem3856579 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856580 (_44749 : int) (_44750 : int) : (term181 _44749 _44750) = (term305 _44749 _44750).
Proof. exact (MK_COMB (@lem3856579) (@lem3856447 _44749 _44750)). Qed.
Lemma lem3856581 (_44749 : int) (_44750 : int) : (term182 _44749 _44750) = (term306 _44749 _44750).
Proof. exact (MK_COMB (@lem3856580 _44749 _44750) (@lem3856578 _44750)). Qed.
Lemma lem3856582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3856583 (_44749 : int) (_44750 : int) : (term183 _44749 _44750) = (term307 _44749 _44750).
Proof. exact (MK_COMB (@lem3856582) (@lem3856376 _44749 _44750)). Qed.
Lemma lem3856584 (_44749 : int) (_44750 : int) : (term184 _44749 _44750) = (term308 _44749 _44750).
Proof. exact (MK_COMB (@lem3856583 _44749 _44750) (@lem3856581 _44749 _44750)). Qed.
Lemma lem3856585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3856586 (_44750 : int) (_44749 : int) : (term185 _44750 _44749) = (term309 _44750 _44749).
Proof. exact (MK_COMB (@lem3856585) (@lem3856306 _44750 _44749)). Qed.
Lemma lem3856587 (_44749 : int) (_44750 : int) : (term186 _44749 _44750) = (term310 _44749 _44750).
Proof. exact (MK_COMB (@lem3856586 _44750 _44749) (@lem3856584 _44749 _44750)). Qed.
Lemma lem3856588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3856589 (_44750 : int) : (term187 _44750) = (term311 _44750).
Proof. exact (MK_COMB (@lem3856588) (@lem3856011 _44750)). Qed.
Lemma lem3856590 (_44749 : int) (_44750 : int) : (term188 _44749 _44750) = (term312 _44749 _44750).
Proof. exact (MK_COMB (@lem3856589 _44750) (@lem3856587 _44749 _44750)). Qed.
Lemma lem3856591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3856592 (_44749 : int) : (term187 _44749) = (term311 _44749).
Proof. exact (MK_COMB (@lem3856591) (@lem3855963 _44749)). Qed.
Lemma lem3856593 (_44749 : int) (_44750 : int) : (term189 _44749 _44750) = (term313 _44749 _44750).
Proof. exact (MK_COMB (@lem3856592 _44749) (@lem3856590 _44749 _44750)). Qed.
Lemma lem3856600 (_44749 : int) (_44750 : int) : (term191 _44749 _44750) = (term313 _44749 _44750).
Proof. exact (TRANS (@lem3855915 _44749 _44750) (@lem3856593 _44749 _44750)). Qed.
Lemma lem3856618 (_44749 : int) (_44750 : int) : (term308 _44749 _44750) = (term314 _44749 _44750).
Proof. exact (@lem19158 (term286 _44749 _44750) (term282 _44749 _44750) (term304 _44750)). Qed.
Lemma lem3856619 (_44749 : int) (_44750 : int) : (term315 _44749 _44750) = (term316 _44749 _44750).
Proof. exact (@lem19158 (term293 _44750) (term282 _44749 _44750) (term302 _44750)). Qed.
Lemma lem3856626 (_44749 : int) (_44750 : int) : (term317 _44749 _44750) = (term318 _44749 _44750).
Proof. exact (@lem19367 (term280 _44749 _44750) ((real_of_int _44750) = term133) (term302 _44750)). Qed.
Lemma lem3856633 (_44749 : int) (_44750 : int) : (term319 _44749 _44750) = (term320 _44749 _44750).
Proof. exact (@lem19367 (term280 _44749 _44750) ((real_of_int _44750) = term133) (term293 _44750)). Qed.
Lemma lem3856634 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856635 (_44749 : int) (_44750 : int) : (term321 _44749 _44750) = (term322 _44749 _44750).
Proof. exact (MK_COMB (@lem3856634) (@lem3856633 _44749 _44750)). Qed.
Lemma lem3856636 (_44749 : int) (_44750 : int) : (term316 _44749 _44750) = (term323 _44749 _44750).
Proof. exact (MK_COMB (@lem3856635 _44749 _44750) (@lem3856626 _44749 _44750)). Qed.
Lemma lem3856637 (_44749 : int) (_44750 : int) : (term315 _44749 _44750) = (term323 _44749 _44750).
Proof. exact (TRANS (@lem3856619 _44749 _44750) (@lem3856636 _44749 _44750)). Qed.
Lemma lem3856644 (_44749 : int) (_44750 : int) : (term324 _44749 _44750) = (term325 _44749 _44750).
Proof. exact (@lem19367 (term280 _44749 _44750) ((real_of_int _44750) = term133) (term286 _44749 _44750)). Qed.
Lemma lem3856645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856646 (_44749 : int) (_44750 : int) : (term326 _44749 _44750) = (term327 _44749 _44750).
Proof. exact (MK_COMB (@lem3856645) (@lem3856644 _44749 _44750)). Qed.
Lemma lem3856647 (_44749 : int) (_44750 : int) : (term314 _44749 _44750) = (term328 _44749 _44750).
Proof. exact (MK_COMB (@lem3856646 _44749 _44750) (@lem3856637 _44749 _44750)). Qed.
Lemma lem3856649 (_44749 : int) (_44750 : int) : (term308 _44749 _44750) = (term328 _44749 _44750).
Proof. exact (TRANS (@lem3856618 _44749 _44750) (@lem3856647 _44749 _44750)). Qed.
Lemma lem3856662 (_44750 : int) (_44749 : int) : (term309 _44750 _44749) = (term309 _44750 _44749).
Proof. exact (eq_refl (term309 _44750 _44749)). Qed.
Lemma lem3856663 (_44749 : int) (_44750 : int) : (term310 _44749 _44750) = (term329 _44749 _44750).
Proof. exact (MK_COMB (@lem3856662 _44750 _44749) (@lem3856649 _44749 _44750)). Qed.
Lemma lem3856664 (_44749 : int) (_44750 : int) : (term329 _44749 _44750) = (term330 _44749 _44750).
Proof. exact (@lem19158 (term325 _44749 _44750) (term274 _44750 _44749) (term323 _44749 _44750)). Qed.
Lemma lem3856665 (_44749 : int) (_44750 : int) : (term331 _44749 _44750) = (term332 _44749 _44750).
Proof. exact (@lem19158 (term320 _44749 _44750) (term274 _44750 _44749) (term318 _44749 _44750)). Qed.
Lemma lem3856666 (_44749 : int) (_44750 : int) : (term333 _44749 _44750) = (term334 _44749 _44750).
Proof. exact (@lem19158 (term335 _44749 _44750) (term274 _44750 _44749) (term336 _44750)). Qed.
Lemma lem3856673 (_44749 : int) (_44750 : int) : (term337 _44749 _44750) = (term338 _44749 _44750).
Proof. exact (@lem19367 ((term236 _44749 _44750) = term133) (term272 _44750 _44749) (term336 _44750)). Qed.
Lemma lem3856680 (_44749 : int) (_44750 : int) : (term339 _44749 _44750) = (term340 _44749 _44750).
Proof. exact (@lem19367 ((term236 _44749 _44750) = term133) (term272 _44750 _44749) (term335 _44749 _44750)). Qed.
Lemma lem3856681 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856682 (_44749 : int) (_44750 : int) : (term341 _44749 _44750) = (term342 _44749 _44750).
Proof. exact (MK_COMB (@lem3856681) (@lem3856680 _44749 _44750)). Qed.
Lemma lem3856683 (_44749 : int) (_44750 : int) : (term334 _44749 _44750) = (term343 _44749 _44750).
Proof. exact (MK_COMB (@lem3856682 _44749 _44750) (@lem3856673 _44749 _44750)). Qed.
Lemma lem3856684 (_44749 : int) (_44750 : int) : (term333 _44749 _44750) = (term343 _44749 _44750).
Proof. exact (TRANS (@lem3856666 _44749 _44750) (@lem3856683 _44749 _44750)). Qed.
Lemma lem3856685 (_44749 : int) (_44750 : int) : (term344 _44749 _44750) = (term345 _44749 _44750).
Proof. exact (@lem19158 (term346 _44749 _44750) (term274 _44750 _44749) (term347 _44750)). Qed.
Lemma lem3856692 (_44749 : int) (_44750 : int) : (term348 _44749 _44750) = (term349 _44749 _44750).
Proof. exact (@lem19367 ((term236 _44749 _44750) = term133) (term272 _44750 _44749) (term347 _44750)). Qed.
Lemma lem3856699 (_44749 : int) (_44750 : int) : (term350 _44749 _44750) = (term351 _44749 _44750).
Proof. exact (@lem19367 ((term236 _44749 _44750) = term133) (term272 _44750 _44749) (term346 _44749 _44750)). Qed.
Lemma lem3856700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856701 (_44749 : int) (_44750 : int) : (term352 _44749 _44750) = (term353 _44749 _44750).
Proof. exact (MK_COMB (@lem3856700) (@lem3856699 _44749 _44750)). Qed.
Lemma lem3856702 (_44749 : int) (_44750 : int) : (term345 _44749 _44750) = (term354 _44749 _44750).
Proof. exact (MK_COMB (@lem3856701 _44749 _44750) (@lem3856692 _44749 _44750)). Qed.
Lemma lem3856703 (_44749 : int) (_44750 : int) : (term344 _44749 _44750) = (term354 _44749 _44750).
Proof. exact (TRANS (@lem3856685 _44749 _44750) (@lem3856702 _44749 _44750)). Qed.
Lemma lem3856704 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856705 (_44749 : int) (_44750 : int) : (term355 _44749 _44750) = (term356 _44749 _44750).
Proof. exact (MK_COMB (@lem3856704) (@lem3856703 _44749 _44750)). Qed.
Lemma lem3856706 (_44749 : int) (_44750 : int) : (term332 _44749 _44750) = (term357 _44749 _44750).
Proof. exact (MK_COMB (@lem3856705 _44749 _44750) (@lem3856684 _44749 _44750)). Qed.
Lemma lem3856707 (_44749 : int) (_44750 : int) : (term331 _44749 _44750) = (term357 _44749 _44750).
Proof. exact (TRANS (@lem3856665 _44749 _44750) (@lem3856706 _44749 _44750)). Qed.
Lemma lem3856708 (_44749 : int) (_44750 : int) : (term358 _44749 _44750) = (term359 _44749 _44750).
Proof. exact (@lem19158 (term360 _44749 _44750) (term274 _44750 _44749) (term361 _44749 _44750)). Qed.
Lemma lem3856715 (_44749 : int) (_44750 : int) : (term362 _44749 _44750) = (term363 _44749 _44750).
Proof. exact (@lem19367 ((term236 _44749 _44750) = term133) (term272 _44750 _44749) (term361 _44749 _44750)). Qed.
Lemma lem3856722 (_44749 : int) (_44750 : int) : (term364 _44749 _44750) = (term365 _44749 _44750).
Proof. exact (@lem19367 ((term236 _44749 _44750) = term133) (term272 _44750 _44749) (term360 _44749 _44750)). Qed.
Lemma lem3856723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856724 (_44749 : int) (_44750 : int) : (term366 _44749 _44750) = (term367 _44749 _44750).
Proof. exact (MK_COMB (@lem3856723) (@lem3856722 _44749 _44750)). Qed.
Lemma lem3856725 (_44749 : int) (_44750 : int) : (term359 _44749 _44750) = (term368 _44749 _44750).
Proof. exact (MK_COMB (@lem3856724 _44749 _44750) (@lem3856715 _44749 _44750)). Qed.
Lemma lem3856726 (_44749 : int) (_44750 : int) : (term358 _44749 _44750) = (term368 _44749 _44750).
Proof. exact (TRANS (@lem3856708 _44749 _44750) (@lem3856725 _44749 _44750)). Qed.
Lemma lem3856727 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856728 (_44749 : int) (_44750 : int) : (term369 _44749 _44750) = (term370 _44749 _44750).
Proof. exact (MK_COMB (@lem3856727) (@lem3856726 _44749 _44750)). Qed.
Lemma lem3856729 (_44749 : int) (_44750 : int) : (term330 _44749 _44750) = (term371 _44749 _44750).
Proof. exact (MK_COMB (@lem3856728 _44749 _44750) (@lem3856707 _44749 _44750)). Qed.
Lemma lem3856730 (_44749 : int) (_44750 : int) : (term329 _44749 _44750) = (term371 _44749 _44750).
Proof. exact (TRANS (@lem3856664 _44749 _44750) (@lem3856729 _44749 _44750)). Qed.
Lemma lem3856731 (_44749 : int) (_44750 : int) : (term310 _44749 _44750) = (term371 _44749 _44750).
Proof. exact (TRANS (@lem3856663 _44749 _44750) (@lem3856730 _44749 _44750)). Qed.
Lemma lem3856734 (_44750 : int) : (term311 _44750) = (term311 _44750).
Proof. exact (eq_refl (term311 _44750)). Qed.
Lemma lem3856735 (_44749 : int) (_44750 : int) : (term312 _44749 _44750) = (term372 _44749 _44750).
Proof. exact (MK_COMB (@lem3856734 _44750) (@lem3856731 _44749 _44750)). Qed.
Lemma lem3856736 (_44749 : int) (_44750 : int) : (term372 _44749 _44750) = (term373 _44749 _44750).
Proof. exact (@lem19158 (term368 _44749 _44750) (term219 _44750) (term357 _44749 _44750)). Qed.
Lemma lem3856737 (_44749 : int) (_44750 : int) : (term374 _44749 _44750) = (term375 _44749 _44750).
Proof. exact (@lem19158 (term354 _44749 _44750) (term219 _44750) (term343 _44749 _44750)). Qed.
Lemma lem3856738 (_44749 : int) (_44750 : int) : (term376 _44749 _44750) = (term377 _44749 _44750).
Proof. exact (@lem19158 (term340 _44749 _44750) (term219 _44750) (term338 _44749 _44750)). Qed.
Lemma lem3856745 (_44749 : int) (_44750 : int) : (term378 _44749 _44750) = (term379 _44749 _44750).
Proof. exact (@lem19158 (term380 _44749 _44750) (term219 _44750) (term381 _44749 _44750)). Qed.
Lemma lem3856752 (_44749 : int) (_44750 : int) : (term382 _44749 _44750) = (term383 _44749 _44750).
Proof. exact (@lem19158 (term384 _44749 _44750) (term219 _44750) (term385 _44749 _44750)). Qed.
Lemma lem3856753 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856754 (_44749 : int) (_44750 : int) : (term386 _44749 _44750) = (term387 _44749 _44750).
Proof. exact (MK_COMB (@lem3856753) (@lem3856752 _44749 _44750)). Qed.
Lemma lem3856755 (_44749 : int) (_44750 : int) : (term377 _44749 _44750) = (term388 _44749 _44750).
Proof. exact (MK_COMB (@lem3856754 _44749 _44750) (@lem3856745 _44749 _44750)). Qed.
Lemma lem3856756 (_44749 : int) (_44750 : int) : (term376 _44749 _44750) = (term388 _44749 _44750).
Proof. exact (TRANS (@lem3856738 _44749 _44750) (@lem3856755 _44749 _44750)). Qed.
Lemma lem3856757 (_44749 : int) (_44750 : int) : (term389 _44749 _44750) = (term390 _44749 _44750).
Proof. exact (@lem19158 (term351 _44749 _44750) (term219 _44750) (term349 _44749 _44750)). Qed.
Lemma lem3856764 (_44749 : int) (_44750 : int) : (term391 _44749 _44750) = (term392 _44749 _44750).
Proof. exact (@lem19158 (term393 _44749 _44750) (term219 _44750) (term394 _44749 _44750)). Qed.
Lemma lem3856771 (_44749 : int) (_44750 : int) : (term395 _44749 _44750) = (term396 _44749 _44750).
Proof. exact (@lem19158 (term397 _44749 _44750) (term219 _44750) (term398 _44749 _44750)). Qed.
Lemma lem3856772 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856773 (_44749 : int) (_44750 : int) : (term399 _44749 _44750) = (term400 _44749 _44750).
Proof. exact (MK_COMB (@lem3856772) (@lem3856771 _44749 _44750)). Qed.
Lemma lem3856774 (_44749 : int) (_44750 : int) : (term390 _44749 _44750) = (term401 _44749 _44750).
Proof. exact (MK_COMB (@lem3856773 _44749 _44750) (@lem3856764 _44749 _44750)). Qed.
Lemma lem3856775 (_44749 : int) (_44750 : int) : (term389 _44749 _44750) = (term401 _44749 _44750).
Proof. exact (TRANS (@lem3856757 _44749 _44750) (@lem3856774 _44749 _44750)). Qed.
Lemma lem3856776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856777 (_44749 : int) (_44750 : int) : (term402 _44749 _44750) = (term403 _44749 _44750).
Proof. exact (MK_COMB (@lem3856776) (@lem3856775 _44749 _44750)). Qed.
Lemma lem3856778 (_44749 : int) (_44750 : int) : (term375 _44749 _44750) = (term404 _44749 _44750).
Proof. exact (MK_COMB (@lem3856777 _44749 _44750) (@lem3856756 _44749 _44750)). Qed.
Lemma lem3856779 (_44749 : int) (_44750 : int) : (term374 _44749 _44750) = (term404 _44749 _44750).
Proof. exact (TRANS (@lem3856737 _44749 _44750) (@lem3856778 _44749 _44750)). Qed.
Lemma lem3856780 (_44749 : int) (_44750 : int) : (term405 _44749 _44750) = (term406 _44749 _44750).
Proof. exact (@lem19158 (term365 _44749 _44750) (term219 _44750) (term363 _44749 _44750)). Qed.
Lemma lem3856787 (_44749 : int) (_44750 : int) : (term407 _44749 _44750) = (term408 _44749 _44750).
Proof. exact (@lem19158 (term409 _44749 _44750) (term219 _44750) (term410 _44749 _44750)). Qed.
Lemma lem3856794 (_44749 : int) (_44750 : int) : (term411 _44749 _44750) = (term412 _44749 _44750).
Proof. exact (@lem19158 (term413 _44749 _44750) (term219 _44750) (term414 _44749 _44750)). Qed.
Lemma lem3856795 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856796 (_44749 : int) (_44750 : int) : (term415 _44749 _44750) = (term416 _44749 _44750).
Proof. exact (MK_COMB (@lem3856795) (@lem3856794 _44749 _44750)). Qed.
Lemma lem3856797 (_44749 : int) (_44750 : int) : (term406 _44749 _44750) = (term417 _44749 _44750).
Proof. exact (MK_COMB (@lem3856796 _44749 _44750) (@lem3856787 _44749 _44750)). Qed.
Lemma lem3856798 (_44749 : int) (_44750 : int) : (term405 _44749 _44750) = (term417 _44749 _44750).
Proof. exact (TRANS (@lem3856780 _44749 _44750) (@lem3856797 _44749 _44750)). Qed.
Lemma lem3856799 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856800 (_44749 : int) (_44750 : int) : (term418 _44749 _44750) = (term419 _44749 _44750).
Proof. exact (MK_COMB (@lem3856799) (@lem3856798 _44749 _44750)). Qed.
Lemma lem3856801 (_44749 : int) (_44750 : int) : (term373 _44749 _44750) = (term420 _44749 _44750).
Proof. exact (MK_COMB (@lem3856800 _44749 _44750) (@lem3856779 _44749 _44750)). Qed.
Lemma lem3856802 (_44749 : int) (_44750 : int) : (term372 _44749 _44750) = (term420 _44749 _44750).
Proof. exact (TRANS (@lem3856736 _44749 _44750) (@lem3856801 _44749 _44750)). Qed.
Lemma lem3856803 (_44749 : int) (_44750 : int) : (term312 _44749 _44750) = (term420 _44749 _44750).
Proof. exact (TRANS (@lem3856735 _44749 _44750) (@lem3856802 _44749 _44750)). Qed.
Lemma lem3856806 (_44749 : int) : (term311 _44749) = (term311 _44749).
Proof. exact (eq_refl (term311 _44749)). Qed.
Lemma lem3856807 (_44749 : int) (_44750 : int) : (term313 _44749 _44750) = (term421 _44749 _44750).
Proof. exact (MK_COMB (@lem3856806 _44749) (@lem3856803 _44749 _44750)). Qed.
Lemma lem3856808 (_44749 : int) (_44750 : int) : (term421 _44749 _44750) = (term422 _44749 _44750).
Proof. exact (@lem19158 (term417 _44749 _44750) (term219 _44749) (term404 _44749 _44750)). Qed.
Lemma lem3856809 (_44749 : int) (_44750 : int) : (term423 _44749 _44750) = (term424 _44749 _44750).
Proof. exact (@lem19158 (term401 _44749 _44750) (term219 _44749) (term388 _44749 _44750)). Qed.
Lemma lem3856810 (_44749 : int) (_44750 : int) : (term425 _44749 _44750) = (term426 _44749 _44750).
Proof. exact (@lem19158 (term383 _44749 _44750) (term219 _44749) (term379 _44749 _44750)). Qed.
Lemma lem3856817 (_44749 : int) (_44750 : int) : (term427 _44749 _44750) = (term428 _44749 _44750).
Proof. exact (@lem19158 (term429 _44749 _44750) (term219 _44749) (term430 _44749 _44750)). Qed.
Lemma lem3856824 (_44749 : int) (_44750 : int) : (term431 _44749 _44750) = (term432 _44749 _44750).
Proof. exact (@lem19158 (term433 _44749 _44750) (term219 _44749) (term434 _44749 _44750)). Qed.
Lemma lem3856825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856826 (_44749 : int) (_44750 : int) : (term435 _44749 _44750) = (term436 _44749 _44750).
Proof. exact (MK_COMB (@lem3856825) (@lem3856824 _44749 _44750)). Qed.
Lemma lem3856827 (_44749 : int) (_44750 : int) : (term426 _44749 _44750) = (term437 _44749 _44750).
Proof. exact (MK_COMB (@lem3856826 _44749 _44750) (@lem3856817 _44749 _44750)). Qed.
Lemma lem3856828 (_44749 : int) (_44750 : int) : (term425 _44749 _44750) = (term437 _44749 _44750).
Proof. exact (TRANS (@lem3856810 _44749 _44750) (@lem3856827 _44749 _44750)). Qed.
Lemma lem3856829 (_44749 : int) (_44750 : int) : (term438 _44749 _44750) = (term439 _44749 _44750).
Proof. exact (@lem19158 (term396 _44749 _44750) (term219 _44749) (term392 _44749 _44750)). Qed.
Lemma lem3856836 (_44749 : int) (_44750 : int) : (term440 _44749 _44750) = (term441 _44749 _44750).
Proof. exact (@lem19158 (term442 _44749 _44750) (term219 _44749) (term443 _44749 _44750)). Qed.
Lemma lem3856843 (_44749 : int) (_44750 : int) : (term444 _44749 _44750) = (term445 _44749 _44750).
Proof. exact (@lem19158 (term446 _44749 _44750) (term219 _44749) (term447 _44749 _44750)). Qed.
Lemma lem3856844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856845 (_44749 : int) (_44750 : int) : (term448 _44749 _44750) = (term449 _44749 _44750).
Proof. exact (MK_COMB (@lem3856844) (@lem3856843 _44749 _44750)). Qed.
Lemma lem3856846 (_44749 : int) (_44750 : int) : (term439 _44749 _44750) = (term450 _44749 _44750).
Proof. exact (MK_COMB (@lem3856845 _44749 _44750) (@lem3856836 _44749 _44750)). Qed.
Lemma lem3856847 (_44749 : int) (_44750 : int) : (term438 _44749 _44750) = (term450 _44749 _44750).
Proof. exact (TRANS (@lem3856829 _44749 _44750) (@lem3856846 _44749 _44750)). Qed.
Lemma lem3856848 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856849 (_44749 : int) (_44750 : int) : (term451 _44749 _44750) = (term452 _44749 _44750).
Proof. exact (MK_COMB (@lem3856848) (@lem3856847 _44749 _44750)). Qed.
Lemma lem3856850 (_44749 : int) (_44750 : int) : (term424 _44749 _44750) = (term453 _44749 _44750).
Proof. exact (MK_COMB (@lem3856849 _44749 _44750) (@lem3856828 _44749 _44750)). Qed.
Lemma lem3856851 (_44749 : int) (_44750 : int) : (term423 _44749 _44750) = (term453 _44749 _44750).
Proof. exact (TRANS (@lem3856809 _44749 _44750) (@lem3856850 _44749 _44750)). Qed.
Lemma lem3856852 (_44749 : int) (_44750 : int) : (term454 _44749 _44750) = (term455 _44749 _44750).
Proof. exact (@lem19158 (term412 _44749 _44750) (term219 _44749) (term408 _44749 _44750)). Qed.
Lemma lem3856859 (_44749 : int) (_44750 : int) : (term456 _44749 _44750) = (term457 _44749 _44750).
Proof. exact (@lem19158 (term458 _44749 _44750) (term219 _44749) (term459 _44749 _44750)). Qed.
Lemma lem3856866 (_44749 : int) (_44750 : int) : (term460 _44749 _44750) = (term461 _44749 _44750).
Proof. exact (@lem19158 (term462 _44749 _44750) (term219 _44749) (term463 _44749 _44750)). Qed.
Lemma lem3856867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856868 (_44749 : int) (_44750 : int) : (term464 _44749 _44750) = (term465 _44749 _44750).
Proof. exact (MK_COMB (@lem3856867) (@lem3856866 _44749 _44750)). Qed.
Lemma lem3856869 (_44749 : int) (_44750 : int) : (term455 _44749 _44750) = (term466 _44749 _44750).
Proof. exact (MK_COMB (@lem3856868 _44749 _44750) (@lem3856859 _44749 _44750)). Qed.
Lemma lem3856870 (_44749 : int) (_44750 : int) : (term454 _44749 _44750) = (term466 _44749 _44750).
Proof. exact (TRANS (@lem3856852 _44749 _44750) (@lem3856869 _44749 _44750)). Qed.
Lemma lem3856871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3856872 (_44749 : int) (_44750 : int) : (term467 _44749 _44750) = (term468 _44749 _44750).
Proof. exact (MK_COMB (@lem3856871) (@lem3856870 _44749 _44750)). Qed.
Lemma lem3856873 (_44749 : int) (_44750 : int) : (term422 _44749 _44750) = (term469 _44749 _44750).
Proof. exact (MK_COMB (@lem3856872 _44749 _44750) (@lem3856851 _44749 _44750)). Qed.
Lemma lem3856874 (_44749 : int) (_44750 : int) : (term421 _44749 _44750) = (term469 _44749 _44750).
Proof. exact (TRANS (@lem3856808 _44749 _44750) (@lem3856873 _44749 _44750)). Qed.
Lemma lem3856875 (_44749 : int) (_44750 : int) : (term313 _44749 _44750) = (term469 _44749 _44750).
Proof. exact (TRANS (@lem3856807 _44749 _44750) (@lem3856874 _44749 _44750)). Qed.
Lemma lem3856876 (_44749 : int) (_44750 : int) : (term191 _44749 _44750) = (term469 _44749 _44750).
Proof. exact (TRANS (@lem3856600 _44749 _44750) (@lem3856875 _44749 _44750)). Qed.
Lemma lem3856946 (_44749 : int) (_44750 : int) (h1 : term469 _44749 _44750) : term469 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3856947 (_44749 : int) (_44750 : int) (h1 : term466 _44749 _44750) : term466 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3856948 (_44749 : int) (_44750 : int) (h1 : term461 _44749 _44750) : term461 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3856949 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term470 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3856950 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term462 _44749 _44750.
Proof. exact (proj2 (@lem3856949 _44749 _44750 h1)). Qed.
Lemma lem3856952 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term413 _44749 _44750.
Proof. exact (proj2 (@lem3856950 _44749 _44750 h1)). Qed.
Lemma lem3856954 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term360 _44749 _44750.
Proof. exact (proj2 (@lem3856952 _44749 _44750 h1)). Qed.
Lemma lem3856955 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : (term236 _44749 _44750) = term133.
Proof. exact (proj1 (@lem3856952 _44749 _44750 h1)). Qed.
Lemma lem3856957 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term280 _44749 _44750.
Proof. exact (proj1 (@lem3856954 _44749 _44750 h1)). Qed.
Lemma lem3856959 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3856960 : term471 = term251.
Proof. exact (@lem3856959 term133 term143). Qed.
Lemma lem3856962 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3856963 : term143 = term224.
Proof. exact (@lem3856962 term11). Qed.
Lemma lem3856965 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3856966 : term133 = term196.
Proof. exact (@lem3856965 (NUMERAL 0)). Qed.
Lemma lem3856967 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3856968 : term472 = term473.
Proof. exact (MK_COMB (@lem3856967) (@lem3856966)). Qed.
Lemma lem3856969 : term251 = term474.
Proof. exact (MK_COMB (@lem3856968) (@lem3856963)). Qed.
Lemma lem3856970 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3856972 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3856973 : term251 = term252.
Proof. exact (@lem3856972 (NUMERAL 0) term11). Qed.
Lemma lem3856974 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3856975 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3856976 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3856975 h1) (fun h1 : term252 = True => @lem3856974)). Qed.
Lemma lem3856977 : term252 = True.
Proof. exact (EQ_MP (@lem3856976) (@lem3856974)). Qed.
Lemma lem3856978 : term251 = True.
Proof. exact (TRANS (@lem3856973) (@lem3856977)). Qed.
Lemma lem3856979 : True = term251.
Proof. exact (SYM (@lem3856978)). Qed.
Lemma lem3856980 : term251.
Proof. exact (EQ_MP (@lem3856979) (@lem0)). Qed.
Lemma lem3856981 : term476.
Proof. exact (@lem3856970 (@lem3856980)). Qed.
Lemma lem3856983 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3856984 : term251 = term252.
Proof. exact (@lem3856983 (NUMERAL 0) term11). Qed.
Lemma lem3856985 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3856986 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3856987 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3856986 h1) (fun h1 : term252 = True => @lem3856985)). Qed.
Lemma lem3856988 : term252 = True.
Proof. exact (EQ_MP (@lem3856987) (@lem3856985)). Qed.
Lemma lem3856989 : term251 = True.
Proof. exact (TRANS (@lem3856984) (@lem3856988)). Qed.
Lemma lem3856990 : True = term251.
Proof. exact (SYM (@lem3856989)). Qed.
Lemma lem3856991 : term251.
Proof. exact (EQ_MP (@lem3856990) (@lem0)). Qed.
Lemma lem3856992 : term474 = term477.
Proof. exact (@lem3856981 (@lem3856991)). Qed.
Lemma lem3856994 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3856995 : term208 = term209.
Proof. exact (@lem3856994 term11 term11). Qed.
Lemma lem3856996 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3856997 : term211 = term11.
Proof. exact (EQ_MP (@lem3856996) (@lem940073)). Qed.
Lemma lem3856998 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3856999 : term209 = term143.
Proof. exact (MK_COMB (@lem3856998) (@lem3856997)). Qed.
Lemma lem3857000 : term208 = term143.
Proof. exact (TRANS (@lem3856995) (@lem3856999)). Qed.
Lemma lem3857002 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857003 : term263 = term133.
Proof. exact (@lem3857002 term11). Qed.
Lemma lem3857004 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3857005 : term478 = term472.
Proof. exact (MK_COMB (@lem3857004) (@lem3857003)). Qed.
Lemma lem3857006 : term477 = term251.
Proof. exact (MK_COMB (@lem3857005) (@lem3857000)). Qed.
Lemma lem3857008 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857009 : term251 = term252.
Proof. exact (@lem3857008 (NUMERAL 0) term11). Qed.
Lemma lem3857010 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857011 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857012 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857011 h1) (fun h1 : term252 = True => @lem3857010)). Qed.
Lemma lem3857013 : term252 = True.
Proof. exact (EQ_MP (@lem3857012) (@lem3857010)). Qed.
Lemma lem3857014 : term251 = True.
Proof. exact (TRANS (@lem3857009) (@lem3857013)). Qed.
Lemma lem3857015 : term477 = True.
Proof. exact (TRANS (@lem3857006) (@lem3857014)). Qed.
Lemma lem3857016 : term474 = True.
Proof. exact (TRANS (@lem3856992) (@lem3857015)). Qed.
Lemma lem3857017 : term251 = True.
Proof. exact (TRANS (@lem3856969) (@lem3857016)). Qed.
Lemma lem3857018 : term471 = True.
Proof. exact (TRANS (@lem3856960) (@lem3857017)). Qed.
Lemma lem3857019 : True = term471.
Proof. exact (SYM (@lem3857018)). Qed.
Lemma lem3857020 : term471.
Proof. exact (EQ_MP (@lem3857019) (@lem0)). Qed.
Lemma lem3857021 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term479 _44749 _44750.
Proof. exact (conj (@lem3857020) (@lem3856957 _44749 _44750 h1)). Qed.
Lemma lem3857023 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3857024 (_44749 : int) (_44750 : int) : term481 _44749 _44750.
Proof. exact (@lem3857023 term143 (term277 _44749 _44750)). Qed.
Lemma lem3857025 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term482 _44749 _44750.
Proof. exact (@lem3857024 _44749 _44750 (@lem3857021 _44749 _44750 h1)). Qed.
Lemma lem3857026 (_44749 : int) (_44750 : int) : (term483 _44749 _44750) = (term277 _44749 _44750).
Proof. exact (@lem1982733 (term277 _44749 _44750)). Qed.
Lemma lem3857027 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3857028 (_44749 : int) (_44750 : int) : (term484 _44749 _44750) = (term279 _44749 _44750).
Proof. exact (MK_COMB (@lem3857027) (@lem3857026 _44749 _44750)). Qed.
Lemma lem3857029 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3857030 (_44749 : int) (_44750 : int) : (term482 _44749 _44750) = (term280 _44749 _44750).
Proof. exact (MK_COMB (@lem3857028 _44749 _44750) (@lem3857029)). Qed.
Lemma lem3857031 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term280 _44749 _44750.
Proof. exact (EQ_MP (@lem3857030 _44749 _44750) (@lem3857025 _44749 _44750 h1)). Qed.
Lemma lem3857033 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3857034 (_44749 : int) (_44750 : int) : term486 _44749 _44750.
Proof. exact (@lem3857033 (term236 _44749 _44750)). Qed.
Lemma lem3857035 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term487 _44749 _44750.
Proof. exact (@lem3857034 _44749 _44750 (@lem3856955 _44749 _44750 h1)). Qed.
Lemma lem3857036 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term488 _44749 _44750.
Proof. exact (@lem3857035 _44749 _44750 h1 term143). Qed.
Lemma lem3857037 (_44749 : int) (_44750 : int) : (term488 _44749 _44750) = ((term489 _44749 _44750) = term133).
Proof. exact (eq_refl (term488 _44749 _44750)). Qed.
Lemma lem3857038 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : (term489 _44749 _44750) = term133.
Proof. exact (EQ_MP (@lem3857037 _44749 _44750) (@lem3857036 _44749 _44750 h1)). Qed.
Lemma lem3857039 (_44749 : int) (_44750 : int) : (term489 _44749 _44750) = (term236 _44749 _44750).
Proof. exact (@lem1982733 (term236 _44749 _44750)). Qed.
Lemma lem3857040 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3857041 (_44749 : int) (_44750 : int) : (term490 _44749 _44750) = (term239 _44749 _44750).
Proof. exact (MK_COMB (@lem3857040) (@lem3857039 _44749 _44750)). Qed.
Lemma lem3857042 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3857043 (_44749 : int) (_44750 : int) : ((term489 _44749 _44750) = term133) = ((term236 _44749 _44750) = term133).
Proof. exact (MK_COMB (@lem3857041 _44749 _44750) (@lem3857042)). Qed.
Lemma lem3857044 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : (term236 _44749 _44750) = term133.
Proof. exact (EQ_MP (@lem3857043 _44749 _44750) (@lem3857038 _44749 _44750 h1)). Qed.
Lemma lem3857045 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term491 _44749 _44750.
Proof. exact (conj (@lem3857044 _44749 _44750 h1) (@lem3857031 _44749 _44750 h1)). Qed.
Lemma lem3857047 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3857048 (_44749 : int) (_44750 : int) : term493 _44749 _44750.
Proof. exact (@lem3857047 (term236 _44749 _44750) (term277 _44749 _44750)). Qed.
Lemma lem3857049 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term494 _44749 _44750.
Proof. exact (@lem3857048 _44749 _44750 (@lem3857045 _44749 _44750 h1)). Qed.
Lemma lem3857050 (_44749 : int) (_44750 : int) : (term495 _44749 _44750) = (term496 _44749 _44750).
Proof. exact (@lem1982753 (term237 _44749) (real_of_int _44749) (term299 _44750) (term237 _44750)). Qed.
Lemma lem3857051 (_44749 : int) : (term497 _44749) = (term498 _44749).
Proof. exact (@lem1982713 term199 (real_of_int _44749)). Qed.
Lemma lem3857053 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857054 : term143 = term224.
Proof. exact (@lem3857053 term11). Qed.
Lemma lem3857056 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3857057 : term199 = term200.
Proof. exact (@lem3857056 term11). Qed.
Lemma lem3857058 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857059 : term499 = term500.
Proof. exact (MK_COMB (@lem3857058) (@lem3857057)). Qed.
Lemma lem3857060 : term501 = term502.
Proof. exact (MK_COMB (@lem3857059) (@lem3857054)). Qed.
Lemma lem3857061 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3857063 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857064 : term251 = term252.
Proof. exact (@lem3857063 (NUMERAL 0) term11). Qed.
Lemma lem3857065 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857066 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857067 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857066 h1) (fun h1 : term252 = True => @lem3857065)). Qed.
Lemma lem3857068 : term252 = True.
Proof. exact (EQ_MP (@lem3857067) (@lem3857065)). Qed.
Lemma lem3857069 : term251 = True.
Proof. exact (TRANS (@lem3857064) (@lem3857068)). Qed.
Lemma lem3857070 : True = term251.
Proof. exact (SYM (@lem3857069)). Qed.
Lemma lem3857071 : term251.
Proof. exact (EQ_MP (@lem3857070) (@lem0)). Qed.
Lemma lem3857072 : term504.
Proof. exact (@lem3857061 (@lem3857071)). Qed.
Lemma lem3857074 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857075 : term251 = term252.
Proof. exact (@lem3857074 (NUMERAL 0) term11). Qed.
Lemma lem3857076 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857077 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857078 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857077 h1) (fun h1 : term252 = True => @lem3857076)). Qed.
Lemma lem3857079 : term252 = True.
Proof. exact (EQ_MP (@lem3857078) (@lem3857076)). Qed.
Lemma lem3857080 : term251 = True.
Proof. exact (TRANS (@lem3857075) (@lem3857079)). Qed.
Lemma lem3857081 : True = term251.
Proof. exact (SYM (@lem3857080)). Qed.
Lemma lem3857082 : term251.
Proof. exact (EQ_MP (@lem3857081) (@lem0)). Qed.
Lemma lem3857083 : term505.
Proof. exact (@lem3857072 (@lem3857082)). Qed.
Lemma lem3857085 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857086 : term251 = term252.
Proof. exact (@lem3857085 (NUMERAL 0) term11). Qed.
Lemma lem3857087 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857088 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857089 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857088 h1) (fun h1 : term252 = True => @lem3857087)). Qed.
Lemma lem3857090 : term252 = True.
Proof. exact (EQ_MP (@lem3857089) (@lem3857087)). Qed.
Lemma lem3857091 : term251 = True.
Proof. exact (TRANS (@lem3857086) (@lem3857090)). Qed.
Lemma lem3857092 : True = term251.
Proof. exact (SYM (@lem3857091)). Qed.
Lemma lem3857093 : term251.
Proof. exact (EQ_MP (@lem3857092) (@lem0)). Qed.
Lemma lem3857094 : term506.
Proof. exact (@lem3857083 (@lem3857093)). Qed.
Lemma lem3857096 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857097 : term208 = term209.
Proof. exact (@lem3857096 term11 term11). Qed.
Lemma lem3857098 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857099 : term211 = term11.
Proof. exact (EQ_MP (@lem3857098) (@lem940073)). Qed.
Lemma lem3857100 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857101 : term209 = term143.
Proof. exact (MK_COMB (@lem3857100) (@lem3857099)). Qed.
Lemma lem3857102 : term208 = term143.
Proof. exact (TRANS (@lem3857097) (@lem3857101)). Qed.
Lemma lem3857104 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3857105 : term225 = term230.
Proof. exact (@lem3857104 term11 term11). Qed.
Lemma lem3857106 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857107 : term211 = term11.
Proof. exact (EQ_MP (@lem3857106) (@lem940073)). Qed.
Lemma lem3857108 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857109 : term209 = term143.
Proof. exact (MK_COMB (@lem3857108) (@lem3857107)). Qed.
Lemma lem3857110 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3857111 : term230 = term199.
Proof. exact (MK_COMB (@lem3857110) (@lem3857109)). Qed.
Lemma lem3857112 : term225 = term199.
Proof. exact (TRANS (@lem3857105) (@lem3857111)). Qed.
Lemma lem3857113 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857114 : term507 = term499.
Proof. exact (MK_COMB (@lem3857113) (@lem3857112)). Qed.
Lemma lem3857115 : term508 = term501.
Proof. exact (MK_COMB (@lem3857114) (@lem3857102)). Qed.
Lemma lem3857117 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3857118 : term501 = term133.
Proof. exact (@lem3857117 term11). Qed.
Lemma lem3857119 : term508 = term133.
Proof. exact (TRANS (@lem3857115) (@lem3857118)). Qed.
Lemma lem3857120 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3857121 : term510 = term261.
Proof. exact (MK_COMB (@lem3857120) (@lem3857119)). Qed.
Lemma lem3857122 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3857123 : term511 = term263.
Proof. exact (MK_COMB (@lem3857121) (@lem3857122)). Qed.
Lemma lem3857125 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857126 : term263 = term133.
Proof. exact (@lem3857125 term11). Qed.
Lemma lem3857127 : term511 = term133.
Proof. exact (TRANS (@lem3857123) (@lem3857126)). Qed.
Lemma lem3857129 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857130 : term208 = term209.
Proof. exact (@lem3857129 term11 term11). Qed.
Lemma lem3857131 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857132 : term211 = term11.
Proof. exact (EQ_MP (@lem3857131) (@lem940073)). Qed.
Lemma lem3857133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857134 : term209 = term143.
Proof. exact (MK_COMB (@lem3857133) (@lem3857132)). Qed.
Lemma lem3857135 : term208 = term143.
Proof. exact (TRANS (@lem3857130) (@lem3857134)). Qed.
Lemma lem3857136 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3857137 : term265 = term263.
Proof. exact (MK_COMB (@lem3857136) (@lem3857135)). Qed.
Lemma lem3857139 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857140 : term263 = term133.
Proof. exact (@lem3857139 term11). Qed.
Lemma lem3857141 : term265 = term133.
Proof. exact (TRANS (@lem3857137) (@lem3857140)). Qed.
Lemma lem3857142 : term133 = term265.
Proof. exact (SYM (@lem3857141)). Qed.
Lemma lem3857143 : term511 = term265.
Proof. exact (TRANS (@lem3857127) (@lem3857142)). Qed.
Lemma lem3857144 : term502 = term196.
Proof. exact (@lem3857094 (@lem3857143)). Qed.
Lemma lem3857145 : term501 = term196.
Proof. exact (TRANS (@lem3857060) (@lem3857144)). Qed.
Lemma lem3857147 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3857148 : term196 = term133.
Proof. exact (@lem3857147 term133). Qed.
Lemma lem3857149 : term501 = term133.
Proof. exact (TRANS (@lem3857145) (@lem3857148)). Qed.
Lemma lem3857150 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3857151 : term512 = term261.
Proof. exact (MK_COMB (@lem3857150) (@lem3857149)). Qed.
Lemma lem3857152 (_44749 : int) : (real_of_int _44749) = (real_of_int _44749).
Proof. exact (eq_refl (real_of_int _44749)). Qed.
Lemma lem3857153 (_44749 : int) : (term498 _44749) = (term513 _44749).
Proof. exact (MK_COMB (@lem3857151) (@lem3857152 _44749)). Qed.
Lemma lem3857154 (_44749 : int) : (term497 _44749) = (term513 _44749).
Proof. exact (TRANS (@lem3857051 _44749) (@lem3857153 _44749)). Qed.
Lemma lem3857155 (_44749 : int) : (term513 _44749) = term133.
Proof. exact (@lem1982719 (real_of_int _44749)). Qed.
Lemma lem3857156 (_44749 : int) : (term497 _44749) = term133.
Proof. exact (TRANS (@lem3857154 _44749) (@lem3857155 _44749)). Qed.
Lemma lem3857157 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857158 (_44749 : int) : (term514 _44749) = term175.
Proof. exact (MK_COMB (@lem3857157) (@lem3857156 _44749)). Qed.
Lemma lem3857159 (_44750 : int) : (term515 _44750) = (term516 _44750).
Proof. exact (@lem1982759 (real_of_int _44750) (term237 _44750) term199). Qed.
Lemma lem3857160 (_44750 : int) : (term517 _44750) = (term498 _44750).
Proof. exact (@lem1982715 term199 (real_of_int _44750)). Qed.
Lemma lem3857162 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857163 : term143 = term224.
Proof. exact (@lem3857162 term11). Qed.
Lemma lem3857165 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3857166 : term199 = term200.
Proof. exact (@lem3857165 term11). Qed.
Lemma lem3857167 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857168 : term499 = term500.
Proof. exact (MK_COMB (@lem3857167) (@lem3857166)). Qed.
Lemma lem3857169 : term501 = term502.
Proof. exact (MK_COMB (@lem3857168) (@lem3857163)). Qed.
Lemma lem3857170 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3857172 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857173 : term251 = term252.
Proof. exact (@lem3857172 (NUMERAL 0) term11). Qed.
Lemma lem3857174 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857175 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857176 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857175 h1) (fun h1 : term252 = True => @lem3857174)). Qed.
Lemma lem3857177 : term252 = True.
Proof. exact (EQ_MP (@lem3857176) (@lem3857174)). Qed.
Lemma lem3857178 : term251 = True.
Proof. exact (TRANS (@lem3857173) (@lem3857177)). Qed.
Lemma lem3857179 : True = term251.
Proof. exact (SYM (@lem3857178)). Qed.
Lemma lem3857180 : term251.
Proof. exact (EQ_MP (@lem3857179) (@lem0)). Qed.
Lemma lem3857181 : term504.
Proof. exact (@lem3857170 (@lem3857180)). Qed.
Lemma lem3857183 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857184 : term251 = term252.
Proof. exact (@lem3857183 (NUMERAL 0) term11). Qed.
Lemma lem3857185 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857186 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857187 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857186 h1) (fun h1 : term252 = True => @lem3857185)). Qed.
Lemma lem3857188 : term252 = True.
Proof. exact (EQ_MP (@lem3857187) (@lem3857185)). Qed.
Lemma lem3857189 : term251 = True.
Proof. exact (TRANS (@lem3857184) (@lem3857188)). Qed.
Lemma lem3857190 : True = term251.
Proof. exact (SYM (@lem3857189)). Qed.
Lemma lem3857191 : term251.
Proof. exact (EQ_MP (@lem3857190) (@lem0)). Qed.
Lemma lem3857192 : term505.
Proof. exact (@lem3857181 (@lem3857191)). Qed.
Lemma lem3857194 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857195 : term251 = term252.
Proof. exact (@lem3857194 (NUMERAL 0) term11). Qed.
Lemma lem3857196 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857197 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857198 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857197 h1) (fun h1 : term252 = True => @lem3857196)). Qed.
Lemma lem3857199 : term252 = True.
Proof. exact (EQ_MP (@lem3857198) (@lem3857196)). Qed.
Lemma lem3857200 : term251 = True.
Proof. exact (TRANS (@lem3857195) (@lem3857199)). Qed.
Lemma lem3857201 : True = term251.
Proof. exact (SYM (@lem3857200)). Qed.
Lemma lem3857202 : term251.
Proof. exact (EQ_MP (@lem3857201) (@lem0)). Qed.
Lemma lem3857203 : term506.
Proof. exact (@lem3857192 (@lem3857202)). Qed.
Lemma lem3857205 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857206 : term208 = term209.
Proof. exact (@lem3857205 term11 term11). Qed.
Lemma lem3857207 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857208 : term211 = term11.
Proof. exact (EQ_MP (@lem3857207) (@lem940073)). Qed.
Lemma lem3857209 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857210 : term209 = term143.
Proof. exact (MK_COMB (@lem3857209) (@lem3857208)). Qed.
Lemma lem3857211 : term208 = term143.
Proof. exact (TRANS (@lem3857206) (@lem3857210)). Qed.
Lemma lem3857213 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3857214 : term225 = term230.
Proof. exact (@lem3857213 term11 term11). Qed.
Lemma lem3857215 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857216 : term211 = term11.
Proof. exact (EQ_MP (@lem3857215) (@lem940073)). Qed.
Lemma lem3857217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857218 : term209 = term143.
Proof. exact (MK_COMB (@lem3857217) (@lem3857216)). Qed.
Lemma lem3857219 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3857220 : term230 = term199.
Proof. exact (MK_COMB (@lem3857219) (@lem3857218)). Qed.
Lemma lem3857221 : term225 = term199.
Proof. exact (TRANS (@lem3857214) (@lem3857220)). Qed.
Lemma lem3857222 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857223 : term507 = term499.
Proof. exact (MK_COMB (@lem3857222) (@lem3857221)). Qed.
Lemma lem3857224 : term508 = term501.
Proof. exact (MK_COMB (@lem3857223) (@lem3857211)). Qed.
Lemma lem3857226 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3857227 : term501 = term133.
Proof. exact (@lem3857226 term11). Qed.
Lemma lem3857228 : term508 = term133.
Proof. exact (TRANS (@lem3857224) (@lem3857227)). Qed.
Lemma lem3857229 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3857230 : term510 = term261.
Proof. exact (MK_COMB (@lem3857229) (@lem3857228)). Qed.
Lemma lem3857231 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3857232 : term511 = term263.
Proof. exact (MK_COMB (@lem3857230) (@lem3857231)). Qed.
Lemma lem3857234 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857235 : term263 = term133.
Proof. exact (@lem3857234 term11). Qed.
Lemma lem3857236 : term511 = term133.
Proof. exact (TRANS (@lem3857232) (@lem3857235)). Qed.
Lemma lem3857238 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857239 : term208 = term209.
Proof. exact (@lem3857238 term11 term11). Qed.
Lemma lem3857240 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857241 : term211 = term11.
Proof. exact (EQ_MP (@lem3857240) (@lem940073)). Qed.
Lemma lem3857242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857243 : term209 = term143.
Proof. exact (MK_COMB (@lem3857242) (@lem3857241)). Qed.
Lemma lem3857244 : term208 = term143.
Proof. exact (TRANS (@lem3857239) (@lem3857243)). Qed.
Lemma lem3857245 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3857246 : term265 = term263.
Proof. exact (MK_COMB (@lem3857245) (@lem3857244)). Qed.
Lemma lem3857248 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857249 : term263 = term133.
Proof. exact (@lem3857248 term11). Qed.
Lemma lem3857250 : term265 = term133.
Proof. exact (TRANS (@lem3857246) (@lem3857249)). Qed.
Lemma lem3857251 : term133 = term265.
Proof. exact (SYM (@lem3857250)). Qed.
Lemma lem3857252 : term511 = term265.
Proof. exact (TRANS (@lem3857236) (@lem3857251)). Qed.
Lemma lem3857253 : term502 = term196.
Proof. exact (@lem3857203 (@lem3857252)). Qed.
Lemma lem3857254 : term501 = term196.
Proof. exact (TRANS (@lem3857169) (@lem3857253)). Qed.
Lemma lem3857256 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3857257 : term196 = term133.
Proof. exact (@lem3857256 term133). Qed.
Lemma lem3857258 : term501 = term133.
Proof. exact (TRANS (@lem3857254) (@lem3857257)). Qed.
Lemma lem3857259 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3857260 : term512 = term261.
Proof. exact (MK_COMB (@lem3857259) (@lem3857258)). Qed.
Lemma lem3857261 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3857262 (_44750 : int) : (term498 _44750) = (term513 _44750).
Proof. exact (MK_COMB (@lem3857260) (@lem3857261 _44750)). Qed.
Lemma lem3857263 (_44750 : int) : (term517 _44750) = (term513 _44750).
Proof. exact (TRANS (@lem3857160 _44750) (@lem3857262 _44750)). Qed.
Lemma lem3857264 (_44750 : int) : (term513 _44750) = term133.
Proof. exact (@lem1982719 (real_of_int _44750)). Qed.
Lemma lem3857265 (_44750 : int) : (term517 _44750) = term133.
Proof. exact (TRANS (@lem3857263 _44750) (@lem3857264 _44750)). Qed.
Lemma lem3857266 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857267 (_44750 : int) : (term518 _44750) = term175.
Proof. exact (MK_COMB (@lem3857266) (@lem3857265 _44750)). Qed.
Lemma lem3857268 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3857269 (_44750 : int) : (term516 _44750) = term519.
Proof. exact (MK_COMB (@lem3857267 _44750) (@lem3857268)). Qed.
Lemma lem3857270 (_44750 : int) : (term515 _44750) = term519.
Proof. exact (TRANS (@lem3857159 _44750) (@lem3857269 _44750)). Qed.
Lemma lem3857271 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3857272 (_44750 : int) : (term515 _44750) = term199.
Proof. exact (TRANS (@lem3857270 _44750) (@lem3857271)). Qed.
Lemma lem3857273 (_44749 : int) (_44750 : int) : (term496 _44749 _44750) = term519.
Proof. exact (MK_COMB (@lem3857158 _44749) (@lem3857272 _44750)). Qed.
Lemma lem3857274 (_44749 : int) (_44750 : int) : (term495 _44749 _44750) = term519.
Proof. exact (TRANS (@lem3857050 _44749 _44750) (@lem3857273 _44749 _44750)). Qed.
Lemma lem3857275 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3857276 (_44749 : int) (_44750 : int) : (term495 _44749 _44750) = term199.
Proof. exact (TRANS (@lem3857274 _44749 _44750) (@lem3857275)). Qed.
Lemma lem3857277 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3857278 (_44749 : int) (_44750 : int) : (term520 _44749 _44750) = term521.
Proof. exact (MK_COMB (@lem3857277) (@lem3857276 _44749 _44750)). Qed.
Lemma lem3857279 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3857280 (_44749 : int) (_44750 : int) : (term494 _44749 _44750) = term522.
Proof. exact (MK_COMB (@lem3857278 _44749 _44750) (@lem3857279)). Qed.
Lemma lem3857281 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : term522.
Proof. exact (EQ_MP (@lem3857280 _44749 _44750) (@lem3857049 _44749 _44750 h1)). Qed.
Lemma lem3857283 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3857284 : term522 = term523.
Proof. exact (@lem3857283 term133 term199). Qed.
Lemma lem3857286 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3857287 : term199 = term200.
Proof. exact (@lem3857286 term11). Qed.
Lemma lem3857289 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857290 : term133 = term196.
Proof. exact (@lem3857289 (NUMERAL 0)). Qed.
Lemma lem3857291 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3857292 : term135 = term524.
Proof. exact (MK_COMB (@lem3857291) (@lem3857290)). Qed.
Lemma lem3857293 : term523 = term525.
Proof. exact (MK_COMB (@lem3857292) (@lem3857287)). Qed.
Lemma lem3857294 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3857296 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857297 : term251 = term252.
Proof. exact (@lem3857296 (NUMERAL 0) term11). Qed.
Lemma lem3857298 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857299 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857300 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857299 h1) (fun h1 : term252 = True => @lem3857298)). Qed.
Lemma lem3857301 : term252 = True.
Proof. exact (EQ_MP (@lem3857300) (@lem3857298)). Qed.
Lemma lem3857302 : term251 = True.
Proof. exact (TRANS (@lem3857297) (@lem3857301)). Qed.
Lemma lem3857303 : True = term251.
Proof. exact (SYM (@lem3857302)). Qed.
Lemma lem3857304 : term251.
Proof. exact (EQ_MP (@lem3857303) (@lem0)). Qed.
Lemma lem3857305 : term527.
Proof. exact (@lem3857294 (@lem3857304)). Qed.
Lemma lem3857307 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857308 : term251 = term252.
Proof. exact (@lem3857307 (NUMERAL 0) term11). Qed.
Lemma lem3857309 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857310 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857311 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857310 h1) (fun h1 : term252 = True => @lem3857309)). Qed.
Lemma lem3857312 : term252 = True.
Proof. exact (EQ_MP (@lem3857311) (@lem3857309)). Qed.
Lemma lem3857313 : term251 = True.
Proof. exact (TRANS (@lem3857308) (@lem3857312)). Qed.
Lemma lem3857314 : True = term251.
Proof. exact (SYM (@lem3857313)). Qed.
Lemma lem3857315 : term251.
Proof. exact (EQ_MP (@lem3857314) (@lem0)). Qed.
Lemma lem3857316 : term525 = term528.
Proof. exact (@lem3857305 (@lem3857315)). Qed.
Lemma lem3857318 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3857319 : term225 = term230.
Proof. exact (@lem3857318 term11 term11). Qed.
Lemma lem3857320 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857321 : term211 = term11.
Proof. exact (EQ_MP (@lem3857320) (@lem940073)). Qed.
Lemma lem3857322 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857323 : term209 = term143.
Proof. exact (MK_COMB (@lem3857322) (@lem3857321)). Qed.
Lemma lem3857324 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3857325 : term230 = term199.
Proof. exact (MK_COMB (@lem3857324) (@lem3857323)). Qed.
Lemma lem3857326 : term225 = term199.
Proof. exact (TRANS (@lem3857319) (@lem3857325)). Qed.
Lemma lem3857328 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857329 : term263 = term133.
Proof. exact (@lem3857328 term11). Qed.
Lemma lem3857330 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3857331 : term529 = term135.
Proof. exact (MK_COMB (@lem3857330) (@lem3857329)). Qed.
Lemma lem3857332 : term528 = term523.
Proof. exact (MK_COMB (@lem3857331) (@lem3857326)). Qed.
Lemma lem3857334 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3857335 : term523 = term532.
Proof. exact (@lem3857334 (NUMERAL 0) term11). Qed.
Lemma lem3857336 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857337 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3857338 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857337 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3857336)). Qed.
Lemma lem3857339 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3857338) (@lem3857336)). Qed.
Lemma lem3857340 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3857341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3857342 : term533 = (and True).
Proof. exact (MK_COMB (@lem3857341) (@lem3857340)). Qed.
Lemma lem3857343 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3857342) (@lem3857339)). Qed.
Lemma lem3857345 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3857346 : term532 = False.
Proof. exact (TRANS (@lem3857343) (@lem3857345)). Qed.
Lemma lem3857347 : term523 = False.
Proof. exact (TRANS (@lem3857335) (@lem3857346)). Qed.
Lemma lem3857348 : term528 = False.
Proof. exact (TRANS (@lem3857332) (@lem3857347)). Qed.
Lemma lem3857349 : term525 = False.
Proof. exact (TRANS (@lem3857316) (@lem3857348)). Qed.
Lemma lem3857350 : term523 = False.
Proof. exact (TRANS (@lem3857293) (@lem3857349)). Qed.
Lemma lem3857351 : term522 = False.
Proof. exact (TRANS (@lem3857284) (@lem3857350)). Qed.
Lemma lem3857352 (_44749 : int) (_44750 : int) (h1 : term470 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3857351) (@lem3857281 _44749 _44750 h1)). Qed.
Lemma lem3857353 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term534 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3857354 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term463 _44749 _44750.
Proof. exact (proj2 (@lem3857353 _44749 _44750 h1)). Qed.
Lemma lem3857356 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term414 _44749 _44750.
Proof. exact (proj2 (@lem3857354 _44749 _44750 h1)). Qed.
Lemma lem3857358 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term360 _44749 _44750.
Proof. exact (proj2 (@lem3857356 _44749 _44750 h1)). Qed.
Lemma lem3857359 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term272 _44750 _44749.
Proof. exact (proj1 (@lem3857356 _44749 _44750 h1)). Qed.
Lemma lem3857360 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : (real_of_int _44749) = term133.
Proof. exact (proj2 (@lem3857359 _44749 _44750 h1)). Qed.
Lemma lem3857362 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term286 _44749 _44750.
Proof. exact (proj2 (@lem3857358 _44749 _44750 h1)). Qed.
Lemma lem3857363 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term280 _44749 _44750.
Proof. exact (proj1 (@lem3857358 _44749 _44750 h1)). Qed.
Lemma lem3857365 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3857366 : term471 = term251.
Proof. exact (@lem3857365 term133 term143). Qed.
Lemma lem3857368 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857369 : term143 = term224.
Proof. exact (@lem3857368 term11). Qed.
Lemma lem3857371 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857372 : term133 = term196.
Proof. exact (@lem3857371 (NUMERAL 0)). Qed.
Lemma lem3857373 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3857374 : term472 = term473.
Proof. exact (MK_COMB (@lem3857373) (@lem3857372)). Qed.
Lemma lem3857375 : term251 = term474.
Proof. exact (MK_COMB (@lem3857374) (@lem3857369)). Qed.
Lemma lem3857376 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3857378 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857379 : term251 = term252.
Proof. exact (@lem3857378 (NUMERAL 0) term11). Qed.
Lemma lem3857380 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857381 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857382 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857381 h1) (fun h1 : term252 = True => @lem3857380)). Qed.
Lemma lem3857383 : term252 = True.
Proof. exact (EQ_MP (@lem3857382) (@lem3857380)). Qed.
Lemma lem3857384 : term251 = True.
Proof. exact (TRANS (@lem3857379) (@lem3857383)). Qed.
Lemma lem3857385 : True = term251.
Proof. exact (SYM (@lem3857384)). Qed.
Lemma lem3857386 : term251.
Proof. exact (EQ_MP (@lem3857385) (@lem0)). Qed.
Lemma lem3857387 : term476.
Proof. exact (@lem3857376 (@lem3857386)). Qed.
Lemma lem3857389 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857390 : term251 = term252.
Proof. exact (@lem3857389 (NUMERAL 0) term11). Qed.
Lemma lem3857391 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857392 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857393 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857392 h1) (fun h1 : term252 = True => @lem3857391)). Qed.
Lemma lem3857394 : term252 = True.
Proof. exact (EQ_MP (@lem3857393) (@lem3857391)). Qed.
Lemma lem3857395 : term251 = True.
Proof. exact (TRANS (@lem3857390) (@lem3857394)). Qed.
Lemma lem3857396 : True = term251.
Proof. exact (SYM (@lem3857395)). Qed.
Lemma lem3857397 : term251.
Proof. exact (EQ_MP (@lem3857396) (@lem0)). Qed.
Lemma lem3857398 : term474 = term477.
Proof. exact (@lem3857387 (@lem3857397)). Qed.
Lemma lem3857400 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857401 : term208 = term209.
Proof. exact (@lem3857400 term11 term11). Qed.
Lemma lem3857402 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857403 : term211 = term11.
Proof. exact (EQ_MP (@lem3857402) (@lem940073)). Qed.
Lemma lem3857404 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857405 : term209 = term143.
Proof. exact (MK_COMB (@lem3857404) (@lem3857403)). Qed.
Lemma lem3857406 : term208 = term143.
Proof. exact (TRANS (@lem3857401) (@lem3857405)). Qed.
Lemma lem3857408 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857409 : term263 = term133.
Proof. exact (@lem3857408 term11). Qed.
Lemma lem3857410 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3857411 : term478 = term472.
Proof. exact (MK_COMB (@lem3857410) (@lem3857409)). Qed.
Lemma lem3857412 : term477 = term251.
Proof. exact (MK_COMB (@lem3857411) (@lem3857406)). Qed.
Lemma lem3857414 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857415 : term251 = term252.
Proof. exact (@lem3857414 (NUMERAL 0) term11). Qed.
Lemma lem3857416 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857417 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857418 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857417 h1) (fun h1 : term252 = True => @lem3857416)). Qed.
Lemma lem3857419 : term252 = True.
Proof. exact (EQ_MP (@lem3857418) (@lem3857416)). Qed.
Lemma lem3857420 : term251 = True.
Proof. exact (TRANS (@lem3857415) (@lem3857419)). Qed.
Lemma lem3857421 : term477 = True.
Proof. exact (TRANS (@lem3857412) (@lem3857420)). Qed.
Lemma lem3857422 : term474 = True.
Proof. exact (TRANS (@lem3857398) (@lem3857421)). Qed.
Lemma lem3857423 : term251 = True.
Proof. exact (TRANS (@lem3857375) (@lem3857422)). Qed.
Lemma lem3857424 : term471 = True.
Proof. exact (TRANS (@lem3857366) (@lem3857423)). Qed.
Lemma lem3857425 : True = term471.
Proof. exact (SYM (@lem3857424)). Qed.
Lemma lem3857426 : term471.
Proof. exact (EQ_MP (@lem3857425) (@lem0)). Qed.
Lemma lem3857427 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term535 _44749 _44750.
Proof. exact (conj (@lem3857426) (@lem3857362 _44749 _44750 h1)). Qed.
Lemma lem3857429 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3857430 (_44749 : int) (_44750 : int) : term536 _44749 _44750.
Proof. exact (@lem3857429 term143 (term236 _44749 _44750)). Qed.
Lemma lem3857431 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term537 _44749 _44750.
Proof. exact (@lem3857430 _44749 _44750 (@lem3857427 _44749 _44750 h1)). Qed.
Lemma lem3857432 (_44749 : int) (_44750 : int) : (term489 _44749 _44750) = (term236 _44749 _44750).
Proof. exact (@lem1982733 (term236 _44749 _44750)). Qed.
Lemma lem3857433 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3857434 (_44749 : int) (_44750 : int) : (term538 _44749 _44750) = (term285 _44749 _44750).
Proof. exact (MK_COMB (@lem3857433) (@lem3857432 _44749 _44750)). Qed.
Lemma lem3857435 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3857436 (_44749 : int) (_44750 : int) : (term537 _44749 _44750) = (term286 _44749 _44750).
Proof. exact (MK_COMB (@lem3857434 _44749 _44750) (@lem3857435)). Qed.
Lemma lem3857437 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term286 _44749 _44750.
Proof. exact (EQ_MP (@lem3857436 _44749 _44750) (@lem3857431 _44749 _44750 h1)). Qed.
Lemma lem3857439 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3857440 (_44749 : int) : term539 _44749.
Proof. exact (@lem3857439 (real_of_int _44749)). Qed.
Lemma lem3857441 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term540 _44749.
Proof. exact (@lem3857440 _44749 (@lem3857360 _44749 _44750 h1)). Qed.
Lemma lem3857442 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term541 _44749.
Proof. exact (@lem3857441 _44749 _44750 h1 term143). Qed.
Lemma lem3857443 (_44749 : int) : (term541 _44749) = ((term542 _44749) = term133).
Proof. exact (eq_refl (term541 _44749)). Qed.
Lemma lem3857444 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : (term542 _44749) = term133.
Proof. exact (EQ_MP (@lem3857443 _44749) (@lem3857442 _44749 _44750 h1)). Qed.
Lemma lem3857445 (_44749 : int) : (term542 _44749) = (real_of_int _44749).
Proof. exact (@lem1982733 (real_of_int _44749)). Qed.
Lemma lem3857446 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3857447 (_44749 : int) : (term543 _44749) = (term146 _44749).
Proof. exact (MK_COMB (@lem3857446) (@lem3857445 _44749)). Qed.
Lemma lem3857448 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3857449 (_44749 : int) : ((term542 _44749) = term133) = ((real_of_int _44749) = term133).
Proof. exact (MK_COMB (@lem3857447 _44749) (@lem3857448)). Qed.
Lemma lem3857450 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : (real_of_int _44749) = term133.
Proof. exact (EQ_MP (@lem3857449 _44749) (@lem3857444 _44749 _44750 h1)). Qed.
Lemma lem3857451 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term544 _44749 _44750.
Proof. exact (conj (@lem3857450 _44749 _44750 h1) (@lem3857437 _44749 _44750 h1)). Qed.
Lemma lem3857453 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3857454 (_44749 : int) (_44750 : int) : term545 _44749 _44750.
Proof. exact (@lem3857453 (real_of_int _44749) (term236 _44749 _44750)). Qed.
Lemma lem3857455 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term546 _44749 _44750.
Proof. exact (@lem3857454 _44749 _44750 (@lem3857451 _44749 _44750 h1)). Qed.
Lemma lem3857456 (_44749 : int) (_44750 : int) : (term547 _44749 _44750) = (term548 _44749 _44750).
Proof. exact (@lem1982763 (real_of_int _44749) (term237 _44749) (term299 _44750)). Qed.
Lemma lem3857457 (_44749 : int) : (term517 _44749) = (term498 _44749).
Proof. exact (@lem1982715 term199 (real_of_int _44749)). Qed.
Lemma lem3857459 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857460 : term143 = term224.
Proof. exact (@lem3857459 term11). Qed.
Lemma lem3857462 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3857463 : term199 = term200.
Proof. exact (@lem3857462 term11). Qed.
Lemma lem3857464 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857465 : term499 = term500.
Proof. exact (MK_COMB (@lem3857464) (@lem3857463)). Qed.
Lemma lem3857466 : term501 = term502.
Proof. exact (MK_COMB (@lem3857465) (@lem3857460)). Qed.
Lemma lem3857467 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3857469 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857470 : term251 = term252.
Proof. exact (@lem3857469 (NUMERAL 0) term11). Qed.
Lemma lem3857471 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857472 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857473 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857472 h1) (fun h1 : term252 = True => @lem3857471)). Qed.
Lemma lem3857474 : term252 = True.
Proof. exact (EQ_MP (@lem3857473) (@lem3857471)). Qed.
Lemma lem3857475 : term251 = True.
Proof. exact (TRANS (@lem3857470) (@lem3857474)). Qed.
Lemma lem3857476 : True = term251.
Proof. exact (SYM (@lem3857475)). Qed.
Lemma lem3857477 : term251.
Proof. exact (EQ_MP (@lem3857476) (@lem0)). Qed.
Lemma lem3857478 : term504.
Proof. exact (@lem3857467 (@lem3857477)). Qed.
Lemma lem3857480 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857481 : term251 = term252.
Proof. exact (@lem3857480 (NUMERAL 0) term11). Qed.
Lemma lem3857482 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857483 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857484 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857483 h1) (fun h1 : term252 = True => @lem3857482)). Qed.
Lemma lem3857485 : term252 = True.
Proof. exact (EQ_MP (@lem3857484) (@lem3857482)). Qed.
Lemma lem3857486 : term251 = True.
Proof. exact (TRANS (@lem3857481) (@lem3857485)). Qed.
Lemma lem3857487 : True = term251.
Proof. exact (SYM (@lem3857486)). Qed.
Lemma lem3857488 : term251.
Proof. exact (EQ_MP (@lem3857487) (@lem0)). Qed.
Lemma lem3857489 : term505.
Proof. exact (@lem3857478 (@lem3857488)). Qed.
Lemma lem3857491 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857492 : term251 = term252.
Proof. exact (@lem3857491 (NUMERAL 0) term11). Qed.
Lemma lem3857493 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857494 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857495 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857494 h1) (fun h1 : term252 = True => @lem3857493)). Qed.
Lemma lem3857496 : term252 = True.
Proof. exact (EQ_MP (@lem3857495) (@lem3857493)). Qed.
Lemma lem3857497 : term251 = True.
Proof. exact (TRANS (@lem3857492) (@lem3857496)). Qed.
Lemma lem3857498 : True = term251.
Proof. exact (SYM (@lem3857497)). Qed.
Lemma lem3857499 : term251.
Proof. exact (EQ_MP (@lem3857498) (@lem0)). Qed.
Lemma lem3857500 : term506.
Proof. exact (@lem3857489 (@lem3857499)). Qed.
Lemma lem3857502 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857503 : term208 = term209.
Proof. exact (@lem3857502 term11 term11). Qed.
Lemma lem3857504 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857505 : term211 = term11.
Proof. exact (EQ_MP (@lem3857504) (@lem940073)). Qed.
Lemma lem3857506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857507 : term209 = term143.
Proof. exact (MK_COMB (@lem3857506) (@lem3857505)). Qed.
Lemma lem3857508 : term208 = term143.
Proof. exact (TRANS (@lem3857503) (@lem3857507)). Qed.
Lemma lem3857510 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3857511 : term225 = term230.
Proof. exact (@lem3857510 term11 term11). Qed.
Lemma lem3857512 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857513 : term211 = term11.
Proof. exact (EQ_MP (@lem3857512) (@lem940073)). Qed.
Lemma lem3857514 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857515 : term209 = term143.
Proof. exact (MK_COMB (@lem3857514) (@lem3857513)). Qed.
Lemma lem3857516 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3857517 : term230 = term199.
Proof. exact (MK_COMB (@lem3857516) (@lem3857515)). Qed.
Lemma lem3857518 : term225 = term199.
Proof. exact (TRANS (@lem3857511) (@lem3857517)). Qed.
Lemma lem3857519 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857520 : term507 = term499.
Proof. exact (MK_COMB (@lem3857519) (@lem3857518)). Qed.
Lemma lem3857521 : term508 = term501.
Proof. exact (MK_COMB (@lem3857520) (@lem3857508)). Qed.
Lemma lem3857523 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3857524 : term501 = term133.
Proof. exact (@lem3857523 term11). Qed.
Lemma lem3857525 : term508 = term133.
Proof. exact (TRANS (@lem3857521) (@lem3857524)). Qed.
Lemma lem3857526 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3857527 : term510 = term261.
Proof. exact (MK_COMB (@lem3857526) (@lem3857525)). Qed.
Lemma lem3857528 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3857529 : term511 = term263.
Proof. exact (MK_COMB (@lem3857527) (@lem3857528)). Qed.
Lemma lem3857531 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857532 : term263 = term133.
Proof. exact (@lem3857531 term11). Qed.
Lemma lem3857533 : term511 = term133.
Proof. exact (TRANS (@lem3857529) (@lem3857532)). Qed.
Lemma lem3857535 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857536 : term208 = term209.
Proof. exact (@lem3857535 term11 term11). Qed.
Lemma lem3857537 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857538 : term211 = term11.
Proof. exact (EQ_MP (@lem3857537) (@lem940073)). Qed.
Lemma lem3857539 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857540 : term209 = term143.
Proof. exact (MK_COMB (@lem3857539) (@lem3857538)). Qed.
Lemma lem3857541 : term208 = term143.
Proof. exact (TRANS (@lem3857536) (@lem3857540)). Qed.
Lemma lem3857542 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3857543 : term265 = term263.
Proof. exact (MK_COMB (@lem3857542) (@lem3857541)). Qed.
Lemma lem3857545 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857546 : term263 = term133.
Proof. exact (@lem3857545 term11). Qed.
Lemma lem3857547 : term265 = term133.
Proof. exact (TRANS (@lem3857543) (@lem3857546)). Qed.
Lemma lem3857548 : term133 = term265.
Proof. exact (SYM (@lem3857547)). Qed.
Lemma lem3857549 : term511 = term265.
Proof. exact (TRANS (@lem3857533) (@lem3857548)). Qed.
Lemma lem3857550 : term502 = term196.
Proof. exact (@lem3857500 (@lem3857549)). Qed.
Lemma lem3857551 : term501 = term196.
Proof. exact (TRANS (@lem3857466) (@lem3857550)). Qed.
Lemma lem3857553 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3857554 : term196 = term133.
Proof. exact (@lem3857553 term133). Qed.
Lemma lem3857555 : term501 = term133.
Proof. exact (TRANS (@lem3857551) (@lem3857554)). Qed.
Lemma lem3857556 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3857557 : term512 = term261.
Proof. exact (MK_COMB (@lem3857556) (@lem3857555)). Qed.
Lemma lem3857558 (_44749 : int) : (real_of_int _44749) = (real_of_int _44749).
Proof. exact (eq_refl (real_of_int _44749)). Qed.
Lemma lem3857559 (_44749 : int) : (term498 _44749) = (term513 _44749).
Proof. exact (MK_COMB (@lem3857557) (@lem3857558 _44749)). Qed.
Lemma lem3857560 (_44749 : int) : (term517 _44749) = (term513 _44749).
Proof. exact (TRANS (@lem3857457 _44749) (@lem3857559 _44749)). Qed.
Lemma lem3857561 (_44749 : int) : (term513 _44749) = term133.
Proof. exact (@lem1982719 (real_of_int _44749)). Qed.
Lemma lem3857562 (_44749 : int) : (term517 _44749) = term133.
Proof. exact (TRANS (@lem3857560 _44749) (@lem3857561 _44749)). Qed.
Lemma lem3857563 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857564 (_44749 : int) : (term518 _44749) = term175.
Proof. exact (MK_COMB (@lem3857563) (@lem3857562 _44749)). Qed.
Lemma lem3857565 (_44750 : int) : (term299 _44750) = (term299 _44750).
Proof. exact (eq_refl (term299 _44750)). Qed.
Lemma lem3857566 (_44749 : int) (_44750 : int) : (term548 _44749 _44750) = (term549 _44750).
Proof. exact (MK_COMB (@lem3857564 _44749) (@lem3857565 _44750)). Qed.
Lemma lem3857567 (_44749 : int) (_44750 : int) : (term547 _44749 _44750) = (term549 _44750).
Proof. exact (TRANS (@lem3857456 _44749 _44750) (@lem3857566 _44749 _44750)). Qed.
Lemma lem3857568 (_44750 : int) : (term549 _44750) = (term299 _44750).
Proof. exact (@lem1982721 (term299 _44750)). Qed.
Lemma lem3857569 (_44749 : int) (_44750 : int) : (term547 _44749 _44750) = (term299 _44750).
Proof. exact (TRANS (@lem3857567 _44749 _44750) (@lem3857568 _44750)). Qed.
Lemma lem3857570 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3857571 (_44749 : int) (_44750 : int) : (term550 _44749 _44750) = (term301 _44750).
Proof. exact (MK_COMB (@lem3857570) (@lem3857569 _44749 _44750)). Qed.
Lemma lem3857572 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3857573 (_44749 : int) (_44750 : int) : (term546 _44749 _44750) = (term302 _44750).
Proof. exact (MK_COMB (@lem3857571 _44749 _44750) (@lem3857572)). Qed.
Lemma lem3857574 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term302 _44750.
Proof. exact (EQ_MP (@lem3857573 _44749 _44750) (@lem3857455 _44749 _44750 h1)). Qed.
Lemma lem3857576 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3857577 : term471 = term251.
Proof. exact (@lem3857576 term133 term143). Qed.
Lemma lem3857579 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857580 : term143 = term224.
Proof. exact (@lem3857579 term11). Qed.
Lemma lem3857582 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857583 : term133 = term196.
Proof. exact (@lem3857582 (NUMERAL 0)). Qed.
Lemma lem3857584 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3857585 : term472 = term473.
Proof. exact (MK_COMB (@lem3857584) (@lem3857583)). Qed.
Lemma lem3857586 : term251 = term474.
Proof. exact (MK_COMB (@lem3857585) (@lem3857580)). Qed.
Lemma lem3857587 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3857589 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857590 : term251 = term252.
Proof. exact (@lem3857589 (NUMERAL 0) term11). Qed.
Lemma lem3857591 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857592 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857593 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857592 h1) (fun h1 : term252 = True => @lem3857591)). Qed.
Lemma lem3857594 : term252 = True.
Proof. exact (EQ_MP (@lem3857593) (@lem3857591)). Qed.
Lemma lem3857595 : term251 = True.
Proof. exact (TRANS (@lem3857590) (@lem3857594)). Qed.
Lemma lem3857596 : True = term251.
Proof. exact (SYM (@lem3857595)). Qed.
Lemma lem3857597 : term251.
Proof. exact (EQ_MP (@lem3857596) (@lem0)). Qed.
Lemma lem3857598 : term476.
Proof. exact (@lem3857587 (@lem3857597)). Qed.
Lemma lem3857600 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857601 : term251 = term252.
Proof. exact (@lem3857600 (NUMERAL 0) term11). Qed.
Lemma lem3857602 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857603 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857604 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857603 h1) (fun h1 : term252 = True => @lem3857602)). Qed.
Lemma lem3857605 : term252 = True.
Proof. exact (EQ_MP (@lem3857604) (@lem3857602)). Qed.
Lemma lem3857606 : term251 = True.
Proof. exact (TRANS (@lem3857601) (@lem3857605)). Qed.
Lemma lem3857607 : True = term251.
Proof. exact (SYM (@lem3857606)). Qed.
Lemma lem3857608 : term251.
Proof. exact (EQ_MP (@lem3857607) (@lem0)). Qed.
Lemma lem3857609 : term474 = term477.
Proof. exact (@lem3857598 (@lem3857608)). Qed.
Lemma lem3857611 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857612 : term208 = term209.
Proof. exact (@lem3857611 term11 term11). Qed.
Lemma lem3857613 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857614 : term211 = term11.
Proof. exact (EQ_MP (@lem3857613) (@lem940073)). Qed.
Lemma lem3857615 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857616 : term209 = term143.
Proof. exact (MK_COMB (@lem3857615) (@lem3857614)). Qed.
Lemma lem3857617 : term208 = term143.
Proof. exact (TRANS (@lem3857612) (@lem3857616)). Qed.
Lemma lem3857619 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857620 : term263 = term133.
Proof. exact (@lem3857619 term11). Qed.
Lemma lem3857621 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3857622 : term478 = term472.
Proof. exact (MK_COMB (@lem3857621) (@lem3857620)). Qed.
Lemma lem3857623 : term477 = term251.
Proof. exact (MK_COMB (@lem3857622) (@lem3857617)). Qed.
Lemma lem3857625 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857626 : term251 = term252.
Proof. exact (@lem3857625 (NUMERAL 0) term11). Qed.
Lemma lem3857627 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857628 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857629 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857628 h1) (fun h1 : term252 = True => @lem3857627)). Qed.
Lemma lem3857630 : term252 = True.
Proof. exact (EQ_MP (@lem3857629) (@lem3857627)). Qed.
Lemma lem3857631 : term251 = True.
Proof. exact (TRANS (@lem3857626) (@lem3857630)). Qed.
Lemma lem3857632 : term477 = True.
Proof. exact (TRANS (@lem3857623) (@lem3857631)). Qed.
Lemma lem3857633 : term474 = True.
Proof. exact (TRANS (@lem3857609) (@lem3857632)). Qed.
Lemma lem3857634 : term251 = True.
Proof. exact (TRANS (@lem3857586) (@lem3857633)). Qed.
Lemma lem3857635 : term471 = True.
Proof. exact (TRANS (@lem3857577) (@lem3857634)). Qed.
Lemma lem3857636 : True = term471.
Proof. exact (SYM (@lem3857635)). Qed.
Lemma lem3857637 : term471.
Proof. exact (EQ_MP (@lem3857636) (@lem0)). Qed.
Lemma lem3857638 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term551 _44750.
Proof. exact (conj (@lem3857637) (@lem3857574 _44749 _44750 h1)). Qed.
Lemma lem3857640 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3857641 (_44750 : int) : term552 _44750.
Proof. exact (@lem3857640 term143 (term299 _44750)). Qed.
Lemma lem3857642 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term553 _44750.
Proof. exact (@lem3857641 _44750 (@lem3857638 _44749 _44750 h1)). Qed.
Lemma lem3857643 (_44750 : int) : (term554 _44750) = (term299 _44750).
Proof. exact (@lem1982733 (term299 _44750)). Qed.
Lemma lem3857644 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3857645 (_44750 : int) : (term555 _44750) = (term301 _44750).
Proof. exact (MK_COMB (@lem3857644) (@lem3857643 _44750)). Qed.
Lemma lem3857646 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3857647 (_44750 : int) : (term553 _44750) = (term302 _44750).
Proof. exact (MK_COMB (@lem3857645 _44750) (@lem3857646)). Qed.
Lemma lem3857648 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term302 _44750.
Proof. exact (EQ_MP (@lem3857647 _44750) (@lem3857642 _44749 _44750 h1)). Qed.
Lemma lem3857650 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3857651 : term471 = term251.
Proof. exact (@lem3857650 term133 term143). Qed.
Lemma lem3857653 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857654 : term143 = term224.
Proof. exact (@lem3857653 term11). Qed.
Lemma lem3857656 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857657 : term133 = term196.
Proof. exact (@lem3857656 (NUMERAL 0)). Qed.
Lemma lem3857658 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3857659 : term472 = term473.
Proof. exact (MK_COMB (@lem3857658) (@lem3857657)). Qed.
Lemma lem3857660 : term251 = term474.
Proof. exact (MK_COMB (@lem3857659) (@lem3857654)). Qed.
Lemma lem3857661 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3857663 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857664 : term251 = term252.
Proof. exact (@lem3857663 (NUMERAL 0) term11). Qed.
Lemma lem3857665 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857666 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857667 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857666 h1) (fun h1 : term252 = True => @lem3857665)). Qed.
Lemma lem3857668 : term252 = True.
Proof. exact (EQ_MP (@lem3857667) (@lem3857665)). Qed.
Lemma lem3857669 : term251 = True.
Proof. exact (TRANS (@lem3857664) (@lem3857668)). Qed.
Lemma lem3857670 : True = term251.
Proof. exact (SYM (@lem3857669)). Qed.
Lemma lem3857671 : term251.
Proof. exact (EQ_MP (@lem3857670) (@lem0)). Qed.
Lemma lem3857672 : term476.
Proof. exact (@lem3857661 (@lem3857671)). Qed.
Lemma lem3857674 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857675 : term251 = term252.
Proof. exact (@lem3857674 (NUMERAL 0) term11). Qed.
Lemma lem3857676 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857677 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857678 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857677 h1) (fun h1 : term252 = True => @lem3857676)). Qed.
Lemma lem3857679 : term252 = True.
Proof. exact (EQ_MP (@lem3857678) (@lem3857676)). Qed.
Lemma lem3857680 : term251 = True.
Proof. exact (TRANS (@lem3857675) (@lem3857679)). Qed.
Lemma lem3857681 : True = term251.
Proof. exact (SYM (@lem3857680)). Qed.
Lemma lem3857682 : term251.
Proof. exact (EQ_MP (@lem3857681) (@lem0)). Qed.
Lemma lem3857683 : term474 = term477.
Proof. exact (@lem3857672 (@lem3857682)). Qed.
Lemma lem3857685 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857686 : term208 = term209.
Proof. exact (@lem3857685 term11 term11). Qed.
Lemma lem3857687 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857688 : term211 = term11.
Proof. exact (EQ_MP (@lem3857687) (@lem940073)). Qed.
Lemma lem3857689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857690 : term209 = term143.
Proof. exact (MK_COMB (@lem3857689) (@lem3857688)). Qed.
Lemma lem3857691 : term208 = term143.
Proof. exact (TRANS (@lem3857686) (@lem3857690)). Qed.
Lemma lem3857693 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857694 : term263 = term133.
Proof. exact (@lem3857693 term11). Qed.
Lemma lem3857695 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3857696 : term478 = term472.
Proof. exact (MK_COMB (@lem3857695) (@lem3857694)). Qed.
Lemma lem3857697 : term477 = term251.
Proof. exact (MK_COMB (@lem3857696) (@lem3857691)). Qed.
Lemma lem3857699 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857700 : term251 = term252.
Proof. exact (@lem3857699 (NUMERAL 0) term11). Qed.
Lemma lem3857701 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857702 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857703 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857702 h1) (fun h1 : term252 = True => @lem3857701)). Qed.
Lemma lem3857704 : term252 = True.
Proof. exact (EQ_MP (@lem3857703) (@lem3857701)). Qed.
Lemma lem3857705 : term251 = True.
Proof. exact (TRANS (@lem3857700) (@lem3857704)). Qed.
Lemma lem3857706 : term477 = True.
Proof. exact (TRANS (@lem3857697) (@lem3857705)). Qed.
Lemma lem3857707 : term474 = True.
Proof. exact (TRANS (@lem3857683) (@lem3857706)). Qed.
Lemma lem3857708 : term251 = True.
Proof. exact (TRANS (@lem3857660) (@lem3857707)). Qed.
Lemma lem3857709 : term471 = True.
Proof. exact (TRANS (@lem3857651) (@lem3857708)). Qed.
Lemma lem3857710 : True = term471.
Proof. exact (SYM (@lem3857709)). Qed.
Lemma lem3857711 : term471.
Proof. exact (EQ_MP (@lem3857710) (@lem0)). Qed.
Lemma lem3857712 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term479 _44749 _44750.
Proof. exact (conj (@lem3857711) (@lem3857363 _44749 _44750 h1)). Qed.
Lemma lem3857714 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3857715 (_44749 : int) (_44750 : int) : term481 _44749 _44750.
Proof. exact (@lem3857714 term143 (term277 _44749 _44750)). Qed.
Lemma lem3857716 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term482 _44749 _44750.
Proof. exact (@lem3857715 _44749 _44750 (@lem3857712 _44749 _44750 h1)). Qed.
Lemma lem3857717 (_44749 : int) (_44750 : int) : (term483 _44749 _44750) = (term277 _44749 _44750).
Proof. exact (@lem1982733 (term277 _44749 _44750)). Qed.
Lemma lem3857718 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3857719 (_44749 : int) (_44750 : int) : (term484 _44749 _44750) = (term279 _44749 _44750).
Proof. exact (MK_COMB (@lem3857718) (@lem3857717 _44749 _44750)). Qed.
Lemma lem3857720 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3857721 (_44749 : int) (_44750 : int) : (term482 _44749 _44750) = (term280 _44749 _44750).
Proof. exact (MK_COMB (@lem3857719 _44749 _44750) (@lem3857720)). Qed.
Lemma lem3857722 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term280 _44749 _44750.
Proof. exact (EQ_MP (@lem3857721 _44749 _44750) (@lem3857716 _44749 _44750 h1)). Qed.
Lemma lem3857724 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3857725 (_44749 : int) : term539 _44749.
Proof. exact (@lem3857724 (real_of_int _44749)). Qed.
Lemma lem3857726 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term540 _44749.
Proof. exact (@lem3857725 _44749 (@lem3857360 _44749 _44750 h1)). Qed.
Lemma lem3857727 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term556 _44749.
Proof. exact (@lem3857726 _44749 _44750 h1 term199). Qed.
Lemma lem3857728 (_44749 : int) : (term556 _44749) = ((term237 _44749) = term133).
Proof. exact (eq_refl (term556 _44749)). Qed.
Lemma lem3857735 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : (term237 _44749) = term133.
Proof. exact (EQ_MP (@lem3857728 _44749) (@lem3857727 _44749 _44750 h1)). Qed.
Lemma lem3857736 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term557 _44749 _44750.
Proof. exact (conj (@lem3857735 _44749 _44750 h1) (@lem3857722 _44749 _44750 h1)). Qed.
Lemma lem3857738 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3857739 (_44749 : int) (_44750 : int) : term558 _44749 _44750.
Proof. exact (@lem3857738 (term237 _44749) (term277 _44749 _44750)). Qed.
Lemma lem3857740 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term559 _44749 _44750.
Proof. exact (@lem3857739 _44749 _44750 (@lem3857736 _44749 _44750 h1)). Qed.
Lemma lem3857741 (_44749 : int) (_44750 : int) : (term560 _44749 _44750) = (term561 _44749 _44750).
Proof. exact (@lem1982763 (term237 _44749) (real_of_int _44749) (term237 _44750)). Qed.
Lemma lem3857742 (_44749 : int) : (term497 _44749) = (term498 _44749).
Proof. exact (@lem1982713 term199 (real_of_int _44749)). Qed.
Lemma lem3857744 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857745 : term143 = term224.
Proof. exact (@lem3857744 term11). Qed.
Lemma lem3857747 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3857748 : term199 = term200.
Proof. exact (@lem3857747 term11). Qed.
Lemma lem3857749 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857750 : term499 = term500.
Proof. exact (MK_COMB (@lem3857749) (@lem3857748)). Qed.
Lemma lem3857751 : term501 = term502.
Proof. exact (MK_COMB (@lem3857750) (@lem3857745)). Qed.
Lemma lem3857752 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3857754 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857755 : term251 = term252.
Proof. exact (@lem3857754 (NUMERAL 0) term11). Qed.
Lemma lem3857756 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857757 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857758 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857757 h1) (fun h1 : term252 = True => @lem3857756)). Qed.
Lemma lem3857759 : term252 = True.
Proof. exact (EQ_MP (@lem3857758) (@lem3857756)). Qed.
Lemma lem3857760 : term251 = True.
Proof. exact (TRANS (@lem3857755) (@lem3857759)). Qed.
Lemma lem3857761 : True = term251.
Proof. exact (SYM (@lem3857760)). Qed.
Lemma lem3857762 : term251.
Proof. exact (EQ_MP (@lem3857761) (@lem0)). Qed.
Lemma lem3857763 : term504.
Proof. exact (@lem3857752 (@lem3857762)). Qed.
Lemma lem3857765 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857766 : term251 = term252.
Proof. exact (@lem3857765 (NUMERAL 0) term11). Qed.
Lemma lem3857767 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857768 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857769 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857768 h1) (fun h1 : term252 = True => @lem3857767)). Qed.
Lemma lem3857770 : term252 = True.
Proof. exact (EQ_MP (@lem3857769) (@lem3857767)). Qed.
Lemma lem3857771 : term251 = True.
Proof. exact (TRANS (@lem3857766) (@lem3857770)). Qed.
Lemma lem3857772 : True = term251.
Proof. exact (SYM (@lem3857771)). Qed.
Lemma lem3857773 : term251.
Proof. exact (EQ_MP (@lem3857772) (@lem0)). Qed.
Lemma lem3857774 : term505.
Proof. exact (@lem3857763 (@lem3857773)). Qed.
Lemma lem3857776 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857777 : term251 = term252.
Proof. exact (@lem3857776 (NUMERAL 0) term11). Qed.
Lemma lem3857778 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857779 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857780 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857779 h1) (fun h1 : term252 = True => @lem3857778)). Qed.
Lemma lem3857781 : term252 = True.
Proof. exact (EQ_MP (@lem3857780) (@lem3857778)). Qed.
Lemma lem3857782 : term251 = True.
Proof. exact (TRANS (@lem3857777) (@lem3857781)). Qed.
Lemma lem3857783 : True = term251.
Proof. exact (SYM (@lem3857782)). Qed.
Lemma lem3857784 : term251.
Proof. exact (EQ_MP (@lem3857783) (@lem0)). Qed.
Lemma lem3857785 : term506.
Proof. exact (@lem3857774 (@lem3857784)). Qed.
Lemma lem3857787 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857788 : term208 = term209.
Proof. exact (@lem3857787 term11 term11). Qed.
Lemma lem3857789 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857790 : term211 = term11.
Proof. exact (EQ_MP (@lem3857789) (@lem940073)). Qed.
Lemma lem3857791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857792 : term209 = term143.
Proof. exact (MK_COMB (@lem3857791) (@lem3857790)). Qed.
Lemma lem3857793 : term208 = term143.
Proof. exact (TRANS (@lem3857788) (@lem3857792)). Qed.
Lemma lem3857795 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3857796 : term225 = term230.
Proof. exact (@lem3857795 term11 term11). Qed.
Lemma lem3857797 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857798 : term211 = term11.
Proof. exact (EQ_MP (@lem3857797) (@lem940073)). Qed.
Lemma lem3857799 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857800 : term209 = term143.
Proof. exact (MK_COMB (@lem3857799) (@lem3857798)). Qed.
Lemma lem3857801 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3857802 : term230 = term199.
Proof. exact (MK_COMB (@lem3857801) (@lem3857800)). Qed.
Lemma lem3857803 : term225 = term199.
Proof. exact (TRANS (@lem3857796) (@lem3857802)). Qed.
Lemma lem3857804 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857805 : term507 = term499.
Proof. exact (MK_COMB (@lem3857804) (@lem3857803)). Qed.
Lemma lem3857806 : term508 = term501.
Proof. exact (MK_COMB (@lem3857805) (@lem3857793)). Qed.
Lemma lem3857808 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3857809 : term501 = term133.
Proof. exact (@lem3857808 term11). Qed.
Lemma lem3857810 : term508 = term133.
Proof. exact (TRANS (@lem3857806) (@lem3857809)). Qed.
Lemma lem3857811 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3857812 : term510 = term261.
Proof. exact (MK_COMB (@lem3857811) (@lem3857810)). Qed.
Lemma lem3857813 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3857814 : term511 = term263.
Proof. exact (MK_COMB (@lem3857812) (@lem3857813)). Qed.
Lemma lem3857816 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857817 : term263 = term133.
Proof. exact (@lem3857816 term11). Qed.
Lemma lem3857818 : term511 = term133.
Proof. exact (TRANS (@lem3857814) (@lem3857817)). Qed.
Lemma lem3857820 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857821 : term208 = term209.
Proof. exact (@lem3857820 term11 term11). Qed.
Lemma lem3857822 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857823 : term211 = term11.
Proof. exact (EQ_MP (@lem3857822) (@lem940073)). Qed.
Lemma lem3857824 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857825 : term209 = term143.
Proof. exact (MK_COMB (@lem3857824) (@lem3857823)). Qed.
Lemma lem3857826 : term208 = term143.
Proof. exact (TRANS (@lem3857821) (@lem3857825)). Qed.
Lemma lem3857827 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3857828 : term265 = term263.
Proof. exact (MK_COMB (@lem3857827) (@lem3857826)). Qed.
Lemma lem3857830 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857831 : term263 = term133.
Proof. exact (@lem3857830 term11). Qed.
Lemma lem3857832 : term265 = term133.
Proof. exact (TRANS (@lem3857828) (@lem3857831)). Qed.
Lemma lem3857833 : term133 = term265.
Proof. exact (SYM (@lem3857832)). Qed.
Lemma lem3857834 : term511 = term265.
Proof. exact (TRANS (@lem3857818) (@lem3857833)). Qed.
Lemma lem3857835 : term502 = term196.
Proof. exact (@lem3857785 (@lem3857834)). Qed.
Lemma lem3857836 : term501 = term196.
Proof. exact (TRANS (@lem3857751) (@lem3857835)). Qed.
Lemma lem3857838 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3857839 : term196 = term133.
Proof. exact (@lem3857838 term133). Qed.
Lemma lem3857840 : term501 = term133.
Proof. exact (TRANS (@lem3857836) (@lem3857839)). Qed.
Lemma lem3857841 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3857842 : term512 = term261.
Proof. exact (MK_COMB (@lem3857841) (@lem3857840)). Qed.
Lemma lem3857843 (_44749 : int) : (real_of_int _44749) = (real_of_int _44749).
Proof. exact (eq_refl (real_of_int _44749)). Qed.
Lemma lem3857844 (_44749 : int) : (term498 _44749) = (term513 _44749).
Proof. exact (MK_COMB (@lem3857842) (@lem3857843 _44749)). Qed.
Lemma lem3857845 (_44749 : int) : (term497 _44749) = (term513 _44749).
Proof. exact (TRANS (@lem3857742 _44749) (@lem3857844 _44749)). Qed.
Lemma lem3857846 (_44749 : int) : (term513 _44749) = term133.
Proof. exact (@lem1982719 (real_of_int _44749)). Qed.
Lemma lem3857847 (_44749 : int) : (term497 _44749) = term133.
Proof. exact (TRANS (@lem3857845 _44749) (@lem3857846 _44749)). Qed.
Lemma lem3857848 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857849 (_44749 : int) : (term514 _44749) = term175.
Proof. exact (MK_COMB (@lem3857848) (@lem3857847 _44749)). Qed.
Lemma lem3857850 (_44750 : int) : (term237 _44750) = (term237 _44750).
Proof. exact (eq_refl (term237 _44750)). Qed.
Lemma lem3857851 (_44749 : int) (_44750 : int) : (term561 _44749 _44750) = (term562 _44750).
Proof. exact (MK_COMB (@lem3857849 _44749) (@lem3857850 _44750)). Qed.
Lemma lem3857852 (_44749 : int) (_44750 : int) : (term560 _44749 _44750) = (term562 _44750).
Proof. exact (TRANS (@lem3857741 _44749 _44750) (@lem3857851 _44749 _44750)). Qed.
Lemma lem3857853 (_44750 : int) : (term562 _44750) = (term237 _44750).
Proof. exact (@lem1982721 (term237 _44750)). Qed.
Lemma lem3857854 (_44749 : int) (_44750 : int) : (term560 _44749 _44750) = (term237 _44750).
Proof. exact (TRANS (@lem3857852 _44749 _44750) (@lem3857853 _44750)). Qed.
Lemma lem3857855 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3857856 (_44749 : int) (_44750 : int) : (term563 _44749 _44750) = (term268 _44750).
Proof. exact (MK_COMB (@lem3857855) (@lem3857854 _44749 _44750)). Qed.
Lemma lem3857857 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3857858 (_44749 : int) (_44750 : int) : (term559 _44749 _44750) = (term269 _44750).
Proof. exact (MK_COMB (@lem3857856 _44749 _44750) (@lem3857857)). Qed.
Lemma lem3857859 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term269 _44750.
Proof. exact (EQ_MP (@lem3857858 _44749 _44750) (@lem3857740 _44749 _44750 h1)). Qed.
Lemma lem3857861 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3857862 : term471 = term251.
Proof. exact (@lem3857861 term133 term143). Qed.
Lemma lem3857864 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857865 : term143 = term224.
Proof. exact (@lem3857864 term11). Qed.
Lemma lem3857867 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857868 : term133 = term196.
Proof. exact (@lem3857867 (NUMERAL 0)). Qed.
Lemma lem3857869 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3857870 : term472 = term473.
Proof. exact (MK_COMB (@lem3857869) (@lem3857868)). Qed.
Lemma lem3857871 : term251 = term474.
Proof. exact (MK_COMB (@lem3857870) (@lem3857865)). Qed.
Lemma lem3857872 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3857874 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857875 : term251 = term252.
Proof. exact (@lem3857874 (NUMERAL 0) term11). Qed.
Lemma lem3857876 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857877 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857878 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857877 h1) (fun h1 : term252 = True => @lem3857876)). Qed.
Lemma lem3857879 : term252 = True.
Proof. exact (EQ_MP (@lem3857878) (@lem3857876)). Qed.
Lemma lem3857880 : term251 = True.
Proof. exact (TRANS (@lem3857875) (@lem3857879)). Qed.
Lemma lem3857881 : True = term251.
Proof. exact (SYM (@lem3857880)). Qed.
Lemma lem3857882 : term251.
Proof. exact (EQ_MP (@lem3857881) (@lem0)). Qed.
Lemma lem3857883 : term476.
Proof. exact (@lem3857872 (@lem3857882)). Qed.
Lemma lem3857885 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857886 : term251 = term252.
Proof. exact (@lem3857885 (NUMERAL 0) term11). Qed.
Lemma lem3857887 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857888 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857889 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857888 h1) (fun h1 : term252 = True => @lem3857887)). Qed.
Lemma lem3857890 : term252 = True.
Proof. exact (EQ_MP (@lem3857889) (@lem3857887)). Qed.
Lemma lem3857891 : term251 = True.
Proof. exact (TRANS (@lem3857886) (@lem3857890)). Qed.
Lemma lem3857892 : True = term251.
Proof. exact (SYM (@lem3857891)). Qed.
Lemma lem3857893 : term251.
Proof. exact (EQ_MP (@lem3857892) (@lem0)). Qed.
Lemma lem3857894 : term474 = term477.
Proof. exact (@lem3857883 (@lem3857893)). Qed.
Lemma lem3857896 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857897 : term208 = term209.
Proof. exact (@lem3857896 term11 term11). Qed.
Lemma lem3857898 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857899 : term211 = term11.
Proof. exact (EQ_MP (@lem3857898) (@lem940073)). Qed.
Lemma lem3857900 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857901 : term209 = term143.
Proof. exact (MK_COMB (@lem3857900) (@lem3857899)). Qed.
Lemma lem3857902 : term208 = term143.
Proof. exact (TRANS (@lem3857897) (@lem3857901)). Qed.
Lemma lem3857904 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3857905 : term263 = term133.
Proof. exact (@lem3857904 term11). Qed.
Lemma lem3857906 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3857907 : term478 = term472.
Proof. exact (MK_COMB (@lem3857906) (@lem3857905)). Qed.
Lemma lem3857908 : term477 = term251.
Proof. exact (MK_COMB (@lem3857907) (@lem3857902)). Qed.
Lemma lem3857910 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857911 : term251 = term252.
Proof. exact (@lem3857910 (NUMERAL 0) term11). Qed.
Lemma lem3857912 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857913 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857914 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857913 h1) (fun h1 : term252 = True => @lem3857912)). Qed.
Lemma lem3857915 : term252 = True.
Proof. exact (EQ_MP (@lem3857914) (@lem3857912)). Qed.
Lemma lem3857916 : term251 = True.
Proof. exact (TRANS (@lem3857911) (@lem3857915)). Qed.
Lemma lem3857917 : term477 = True.
Proof. exact (TRANS (@lem3857908) (@lem3857916)). Qed.
Lemma lem3857918 : term474 = True.
Proof. exact (TRANS (@lem3857894) (@lem3857917)). Qed.
Lemma lem3857919 : term251 = True.
Proof. exact (TRANS (@lem3857871) (@lem3857918)). Qed.
Lemma lem3857920 : term471 = True.
Proof. exact (TRANS (@lem3857862) (@lem3857919)). Qed.
Lemma lem3857921 : True = term471.
Proof. exact (SYM (@lem3857920)). Qed.
Lemma lem3857922 : term471.
Proof. exact (EQ_MP (@lem3857921) (@lem0)). Qed.
Lemma lem3857923 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term564 _44750.
Proof. exact (conj (@lem3857922) (@lem3857859 _44749 _44750 h1)). Qed.
Lemma lem3857925 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3857926 (_44750 : int) : term565 _44750.
Proof. exact (@lem3857925 term143 (term237 _44750)). Qed.
Lemma lem3857927 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term566 _44750.
Proof. exact (@lem3857926 _44750 (@lem3857923 _44749 _44750 h1)). Qed.
Lemma lem3857928 (_44750 : int) : (term567 _44750) = (term237 _44750).
Proof. exact (@lem1982733 (term237 _44750)). Qed.
Lemma lem3857929 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3857930 (_44750 : int) : (term568 _44750) = (term268 _44750).
Proof. exact (MK_COMB (@lem3857929) (@lem3857928 _44750)). Qed.
Lemma lem3857931 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3857932 (_44750 : int) : (term566 _44750) = (term269 _44750).
Proof. exact (MK_COMB (@lem3857930 _44750) (@lem3857931)). Qed.
Lemma lem3857933 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term269 _44750.
Proof. exact (EQ_MP (@lem3857932 _44750) (@lem3857927 _44749 _44750 h1)). Qed.
Lemma lem3857934 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term569 _44750.
Proof. exact (conj (@lem3857933 _44749 _44750 h1) (@lem3857648 _44749 _44750 h1)). Qed.
Lemma lem3857936 (x : real) (y : real) : term570 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3857937 (_44750 : int) : term571 _44750.
Proof. exact (@lem3857936 (term237 _44750) (term299 _44750)). Qed.
Lemma lem3857938 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term572 _44750.
Proof. exact (@lem3857937 _44750 (@lem3857934 _44749 _44750 h1)). Qed.
Lemma lem3857939 (_44750 : int) : (term573 _44750) = (term574 _44750).
Proof. exact (@lem1982763 (term237 _44750) (real_of_int _44750) term199). Qed.
Lemma lem3857940 (_44750 : int) : (term497 _44750) = (term498 _44750).
Proof. exact (@lem1982713 term199 (real_of_int _44750)). Qed.
Lemma lem3857942 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3857943 : term143 = term224.
Proof. exact (@lem3857942 term11). Qed.
Lemma lem3857945 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3857946 : term199 = term200.
Proof. exact (@lem3857945 term11). Qed.
Lemma lem3857947 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3857948 : term499 = term500.
Proof. exact (MK_COMB (@lem3857947) (@lem3857946)). Qed.
Lemma lem3857949 : term501 = term502.
Proof. exact (MK_COMB (@lem3857948) (@lem3857943)). Qed.
Lemma lem3857950 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3857952 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857953 : term251 = term252.
Proof. exact (@lem3857952 (NUMERAL 0) term11). Qed.
Lemma lem3857954 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857955 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857956 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857955 h1) (fun h1 : term252 = True => @lem3857954)). Qed.
Lemma lem3857957 : term252 = True.
Proof. exact (EQ_MP (@lem3857956) (@lem3857954)). Qed.
Lemma lem3857958 : term251 = True.
Proof. exact (TRANS (@lem3857953) (@lem3857957)). Qed.
Lemma lem3857959 : True = term251.
Proof. exact (SYM (@lem3857958)). Qed.
Lemma lem3857960 : term251.
Proof. exact (EQ_MP (@lem3857959) (@lem0)). Qed.
Lemma lem3857961 : term504.
Proof. exact (@lem3857950 (@lem3857960)). Qed.
Lemma lem3857963 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857964 : term251 = term252.
Proof. exact (@lem3857963 (NUMERAL 0) term11). Qed.
Lemma lem3857965 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857966 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857967 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857966 h1) (fun h1 : term252 = True => @lem3857965)). Qed.
Lemma lem3857968 : term252 = True.
Proof. exact (EQ_MP (@lem3857967) (@lem3857965)). Qed.
Lemma lem3857969 : term251 = True.
Proof. exact (TRANS (@lem3857964) (@lem3857968)). Qed.
Lemma lem3857970 : True = term251.
Proof. exact (SYM (@lem3857969)). Qed.
Lemma lem3857971 : term251.
Proof. exact (EQ_MP (@lem3857970) (@lem0)). Qed.
Lemma lem3857972 : term505.
Proof. exact (@lem3857961 (@lem3857971)). Qed.
Lemma lem3857974 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3857975 : term251 = term252.
Proof. exact (@lem3857974 (NUMERAL 0) term11). Qed.
Lemma lem3857976 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3857977 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3857978 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3857977 h1) (fun h1 : term252 = True => @lem3857976)). Qed.
Lemma lem3857979 : term252 = True.
Proof. exact (EQ_MP (@lem3857978) (@lem3857976)). Qed.
Lemma lem3857980 : term251 = True.
Proof. exact (TRANS (@lem3857975) (@lem3857979)). Qed.
Lemma lem3857981 : True = term251.
Proof. exact (SYM (@lem3857980)). Qed.
Lemma lem3857982 : term251.
Proof. exact (EQ_MP (@lem3857981) (@lem0)). Qed.
Lemma lem3857983 : term506.
Proof. exact (@lem3857972 (@lem3857982)). Qed.
Lemma lem3857985 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3857986 : term208 = term209.
Proof. exact (@lem3857985 term11 term11). Qed.
Lemma lem3857987 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857988 : term211 = term11.
Proof. exact (EQ_MP (@lem3857987) (@lem940073)). Qed.
Lemma lem3857989 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857990 : term209 = term143.
Proof. exact (MK_COMB (@lem3857989) (@lem3857988)). Qed.
Lemma lem3857991 : term208 = term143.
Proof. exact (TRANS (@lem3857986) (@lem3857990)). Qed.
Lemma lem3857993 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3857994 : term225 = term230.
Proof. exact (@lem3857993 term11 term11). Qed.
Lemma lem3857995 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3857996 : term211 = term11.
Proof. exact (EQ_MP (@lem3857995) (@lem940073)). Qed.
Lemma lem3857997 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3857998 : term209 = term143.
Proof. exact (MK_COMB (@lem3857997) (@lem3857996)). Qed.
Lemma lem3857999 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3858000 : term230 = term199.
Proof. exact (MK_COMB (@lem3857999) (@lem3857998)). Qed.
Lemma lem3858001 : term225 = term199.
Proof. exact (TRANS (@lem3857994) (@lem3858000)). Qed.
Lemma lem3858002 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3858003 : term507 = term499.
Proof. exact (MK_COMB (@lem3858002) (@lem3858001)). Qed.
Lemma lem3858004 : term508 = term501.
Proof. exact (MK_COMB (@lem3858003) (@lem3857991)). Qed.
Lemma lem3858006 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3858007 : term501 = term133.
Proof. exact (@lem3858006 term11). Qed.
Lemma lem3858008 : term508 = term133.
Proof. exact (TRANS (@lem3858004) (@lem3858007)). Qed.
Lemma lem3858009 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3858010 : term510 = term261.
Proof. exact (MK_COMB (@lem3858009) (@lem3858008)). Qed.
Lemma lem3858011 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3858012 : term511 = term263.
Proof. exact (MK_COMB (@lem3858010) (@lem3858011)). Qed.
Lemma lem3858014 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858015 : term263 = term133.
Proof. exact (@lem3858014 term11). Qed.
Lemma lem3858016 : term511 = term133.
Proof. exact (TRANS (@lem3858012) (@lem3858015)). Qed.
Lemma lem3858018 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3858019 : term208 = term209.
Proof. exact (@lem3858018 term11 term11). Qed.
Lemma lem3858020 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858021 : term211 = term11.
Proof. exact (EQ_MP (@lem3858020) (@lem940073)). Qed.
Lemma lem3858022 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858023 : term209 = term143.
Proof. exact (MK_COMB (@lem3858022) (@lem3858021)). Qed.
Lemma lem3858024 : term208 = term143.
Proof. exact (TRANS (@lem3858019) (@lem3858023)). Qed.
Lemma lem3858025 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3858026 : term265 = term263.
Proof. exact (MK_COMB (@lem3858025) (@lem3858024)). Qed.
Lemma lem3858028 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858029 : term263 = term133.
Proof. exact (@lem3858028 term11). Qed.
Lemma lem3858030 : term265 = term133.
Proof. exact (TRANS (@lem3858026) (@lem3858029)). Qed.
Lemma lem3858031 : term133 = term265.
Proof. exact (SYM (@lem3858030)). Qed.
Lemma lem3858032 : term511 = term265.
Proof. exact (TRANS (@lem3858016) (@lem3858031)). Qed.
Lemma lem3858033 : term502 = term196.
Proof. exact (@lem3857983 (@lem3858032)). Qed.
Lemma lem3858034 : term501 = term196.
Proof. exact (TRANS (@lem3857949) (@lem3858033)). Qed.
Lemma lem3858036 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3858037 : term196 = term133.
Proof. exact (@lem3858036 term133). Qed.
Lemma lem3858038 : term501 = term133.
Proof. exact (TRANS (@lem3858034) (@lem3858037)). Qed.
Lemma lem3858039 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3858040 : term512 = term261.
Proof. exact (MK_COMB (@lem3858039) (@lem3858038)). Qed.
Lemma lem3858041 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3858042 (_44750 : int) : (term498 _44750) = (term513 _44750).
Proof. exact (MK_COMB (@lem3858040) (@lem3858041 _44750)). Qed.
Lemma lem3858043 (_44750 : int) : (term497 _44750) = (term513 _44750).
Proof. exact (TRANS (@lem3857940 _44750) (@lem3858042 _44750)). Qed.
Lemma lem3858044 (_44750 : int) : (term513 _44750) = term133.
Proof. exact (@lem1982719 (real_of_int _44750)). Qed.
Lemma lem3858045 (_44750 : int) : (term497 _44750) = term133.
Proof. exact (TRANS (@lem3858043 _44750) (@lem3858044 _44750)). Qed.
Lemma lem3858046 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3858047 (_44750 : int) : (term514 _44750) = term175.
Proof. exact (MK_COMB (@lem3858046) (@lem3858045 _44750)). Qed.
Lemma lem3858048 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3858049 (_44750 : int) : (term574 _44750) = term519.
Proof. exact (MK_COMB (@lem3858047 _44750) (@lem3858048)). Qed.
Lemma lem3858050 (_44750 : int) : (term573 _44750) = term519.
Proof. exact (TRANS (@lem3857939 _44750) (@lem3858049 _44750)). Qed.
Lemma lem3858051 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3858052 (_44750 : int) : (term573 _44750) = term199.
Proof. exact (TRANS (@lem3858050 _44750) (@lem3858051)). Qed.
Lemma lem3858053 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3858054 (_44750 : int) : (term575 _44750) = term521.
Proof. exact (MK_COMB (@lem3858053) (@lem3858052 _44750)). Qed.
Lemma lem3858055 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3858056 (_44750 : int) : (term572 _44750) = term522.
Proof. exact (MK_COMB (@lem3858054 _44750) (@lem3858055)). Qed.
Lemma lem3858057 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : term522.
Proof. exact (EQ_MP (@lem3858056 _44750) (@lem3857938 _44749 _44750 h1)). Qed.
Lemma lem3858059 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3858060 : term522 = term523.
Proof. exact (@lem3858059 term133 term199). Qed.
Lemma lem3858062 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3858063 : term199 = term200.
Proof. exact (@lem3858062 term11). Qed.
Lemma lem3858065 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858066 : term133 = term196.
Proof. exact (@lem3858065 (NUMERAL 0)). Qed.
Lemma lem3858067 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3858068 : term135 = term524.
Proof. exact (MK_COMB (@lem3858067) (@lem3858066)). Qed.
Lemma lem3858069 : term523 = term525.
Proof. exact (MK_COMB (@lem3858068) (@lem3858063)). Qed.
Lemma lem3858070 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3858072 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858073 : term251 = term252.
Proof. exact (@lem3858072 (NUMERAL 0) term11). Qed.
Lemma lem3858074 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858075 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858076 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858075 h1) (fun h1 : term252 = True => @lem3858074)). Qed.
Lemma lem3858077 : term252 = True.
Proof. exact (EQ_MP (@lem3858076) (@lem3858074)). Qed.
Lemma lem3858078 : term251 = True.
Proof. exact (TRANS (@lem3858073) (@lem3858077)). Qed.
Lemma lem3858079 : True = term251.
Proof. exact (SYM (@lem3858078)). Qed.
Lemma lem3858080 : term251.
Proof. exact (EQ_MP (@lem3858079) (@lem0)). Qed.
Lemma lem3858081 : term527.
Proof. exact (@lem3858070 (@lem3858080)). Qed.
Lemma lem3858083 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858084 : term251 = term252.
Proof. exact (@lem3858083 (NUMERAL 0) term11). Qed.
Lemma lem3858085 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858086 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858087 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858086 h1) (fun h1 : term252 = True => @lem3858085)). Qed.
Lemma lem3858088 : term252 = True.
Proof. exact (EQ_MP (@lem3858087) (@lem3858085)). Qed.
Lemma lem3858089 : term251 = True.
Proof. exact (TRANS (@lem3858084) (@lem3858088)). Qed.
Lemma lem3858090 : True = term251.
Proof. exact (SYM (@lem3858089)). Qed.
Lemma lem3858091 : term251.
Proof. exact (EQ_MP (@lem3858090) (@lem0)). Qed.
Lemma lem3858092 : term525 = term528.
Proof. exact (@lem3858081 (@lem3858091)). Qed.
Lemma lem3858094 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3858095 : term225 = term230.
Proof. exact (@lem3858094 term11 term11). Qed.
Lemma lem3858096 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858097 : term211 = term11.
Proof. exact (EQ_MP (@lem3858096) (@lem940073)). Qed.
Lemma lem3858098 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858099 : term209 = term143.
Proof. exact (MK_COMB (@lem3858098) (@lem3858097)). Qed.
Lemma lem3858100 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3858101 : term230 = term199.
Proof. exact (MK_COMB (@lem3858100) (@lem3858099)). Qed.
Lemma lem3858102 : term225 = term199.
Proof. exact (TRANS (@lem3858095) (@lem3858101)). Qed.
Lemma lem3858104 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858105 : term263 = term133.
Proof. exact (@lem3858104 term11). Qed.
Lemma lem3858106 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3858107 : term529 = term135.
Proof. exact (MK_COMB (@lem3858106) (@lem3858105)). Qed.
Lemma lem3858108 : term528 = term523.
Proof. exact (MK_COMB (@lem3858107) (@lem3858102)). Qed.
Lemma lem3858110 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3858111 : term523 = term532.
Proof. exact (@lem3858110 (NUMERAL 0) term11). Qed.
Lemma lem3858112 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858113 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3858114 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858113 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3858112)). Qed.
Lemma lem3858115 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3858114) (@lem3858112)). Qed.
Lemma lem3858116 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3858117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3858118 : term533 = (and True).
Proof. exact (MK_COMB (@lem3858117) (@lem3858116)). Qed.
Lemma lem3858119 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3858118) (@lem3858115)). Qed.
Lemma lem3858121 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3858122 : term532 = False.
Proof. exact (TRANS (@lem3858119) (@lem3858121)). Qed.
Lemma lem3858123 : term523 = False.
Proof. exact (TRANS (@lem3858111) (@lem3858122)). Qed.
Lemma lem3858124 : term528 = False.
Proof. exact (TRANS (@lem3858108) (@lem3858123)). Qed.
Lemma lem3858125 : term525 = False.
Proof. exact (TRANS (@lem3858092) (@lem3858124)). Qed.
Lemma lem3858126 : term523 = False.
Proof. exact (TRANS (@lem3858069) (@lem3858125)). Qed.
Lemma lem3858127 : term522 = False.
Proof. exact (TRANS (@lem3858060) (@lem3858126)). Qed.
Lemma lem3858128 (_44749 : int) (_44750 : int) (h1 : term534 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3858127) (@lem3858057 _44749 _44750 h1)). Qed.
Lemma lem3858129 (_44749 : int) (_44750 : int) (h1 : term461 _44749 _44750) : False.
Proof. exact (or_elim (@lem3856948 _44749 _44750 h1) (fun h0 : term470 _44749 _44750 => @lem3857352 _44749 _44750 h0) (fun h0 : term534 _44749 _44750 => @lem3858128 _44749 _44750 h0)). Qed.
Lemma lem3858130 (_44749 : int) (_44750 : int) (h1 : term457 _44749 _44750) : term457 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3858131 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term576 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3858132 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term458 _44749 _44750.
Proof. exact (proj2 (@lem3858131 _44749 _44750 h1)). Qed.
Lemma lem3858133 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term219 _44749.
Proof. exact (proj1 (@lem3858131 _44749 _44750 h1)). Qed.
Lemma lem3858134 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term409 _44749 _44750.
Proof. exact (proj2 (@lem3858132 _44749 _44750 h1)). Qed.
Lemma lem3858136 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term361 _44749 _44750.
Proof. exact (proj2 (@lem3858134 _44749 _44750 h1)). Qed.
Lemma lem3858137 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : (term236 _44749 _44750) = term133.
Proof. exact (proj1 (@lem3858134 _44749 _44750 h1)). Qed.
Lemma lem3858139 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : (real_of_int _44750) = term133.
Proof. exact (proj1 (@lem3858136 _44749 _44750 h1)). Qed.
Lemma lem3858141 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3858142 : term471 = term251.
Proof. exact (@lem3858141 term133 term143). Qed.
Lemma lem3858144 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858145 : term143 = term224.
Proof. exact (@lem3858144 term11). Qed.
Lemma lem3858147 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858148 : term133 = term196.
Proof. exact (@lem3858147 (NUMERAL 0)). Qed.
Lemma lem3858149 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3858150 : term472 = term473.
Proof. exact (MK_COMB (@lem3858149) (@lem3858148)). Qed.
Lemma lem3858151 : term251 = term474.
Proof. exact (MK_COMB (@lem3858150) (@lem3858145)). Qed.
Lemma lem3858152 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3858154 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858155 : term251 = term252.
Proof. exact (@lem3858154 (NUMERAL 0) term11). Qed.
Lemma lem3858156 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858157 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858158 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858157 h1) (fun h1 : term252 = True => @lem3858156)). Qed.
Lemma lem3858159 : term252 = True.
Proof. exact (EQ_MP (@lem3858158) (@lem3858156)). Qed.
Lemma lem3858160 : term251 = True.
Proof. exact (TRANS (@lem3858155) (@lem3858159)). Qed.
Lemma lem3858161 : True = term251.
Proof. exact (SYM (@lem3858160)). Qed.
Lemma lem3858162 : term251.
Proof. exact (EQ_MP (@lem3858161) (@lem0)). Qed.
Lemma lem3858163 : term476.
Proof. exact (@lem3858152 (@lem3858162)). Qed.
Lemma lem3858165 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858166 : term251 = term252.
Proof. exact (@lem3858165 (NUMERAL 0) term11). Qed.
Lemma lem3858167 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858168 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858169 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858168 h1) (fun h1 : term252 = True => @lem3858167)). Qed.
Lemma lem3858170 : term252 = True.
Proof. exact (EQ_MP (@lem3858169) (@lem3858167)). Qed.
Lemma lem3858171 : term251 = True.
Proof. exact (TRANS (@lem3858166) (@lem3858170)). Qed.
Lemma lem3858172 : True = term251.
Proof. exact (SYM (@lem3858171)). Qed.
Lemma lem3858173 : term251.
Proof. exact (EQ_MP (@lem3858172) (@lem0)). Qed.
Lemma lem3858174 : term474 = term477.
Proof. exact (@lem3858163 (@lem3858173)). Qed.
Lemma lem3858176 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3858177 : term208 = term209.
Proof. exact (@lem3858176 term11 term11). Qed.
Lemma lem3858178 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858179 : term211 = term11.
Proof. exact (EQ_MP (@lem3858178) (@lem940073)). Qed.
Lemma lem3858180 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858181 : term209 = term143.
Proof. exact (MK_COMB (@lem3858180) (@lem3858179)). Qed.
Lemma lem3858182 : term208 = term143.
Proof. exact (TRANS (@lem3858177) (@lem3858181)). Qed.
Lemma lem3858184 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858185 : term263 = term133.
Proof. exact (@lem3858184 term11). Qed.
Lemma lem3858186 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3858187 : term478 = term472.
Proof. exact (MK_COMB (@lem3858186) (@lem3858185)). Qed.
Lemma lem3858188 : term477 = term251.
Proof. exact (MK_COMB (@lem3858187) (@lem3858182)). Qed.
Lemma lem3858190 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858191 : term251 = term252.
Proof. exact (@lem3858190 (NUMERAL 0) term11). Qed.
Lemma lem3858192 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858193 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858194 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858193 h1) (fun h1 : term252 = True => @lem3858192)). Qed.
Lemma lem3858195 : term252 = True.
Proof. exact (EQ_MP (@lem3858194) (@lem3858192)). Qed.
Lemma lem3858196 : term251 = True.
Proof. exact (TRANS (@lem3858191) (@lem3858195)). Qed.
Lemma lem3858197 : term477 = True.
Proof. exact (TRANS (@lem3858188) (@lem3858196)). Qed.
Lemma lem3858198 : term474 = True.
Proof. exact (TRANS (@lem3858174) (@lem3858197)). Qed.
Lemma lem3858199 : term251 = True.
Proof. exact (TRANS (@lem3858151) (@lem3858198)). Qed.
Lemma lem3858200 : term471 = True.
Proof. exact (TRANS (@lem3858142) (@lem3858199)). Qed.
Lemma lem3858201 : True = term471.
Proof. exact (SYM (@lem3858200)). Qed.
Lemma lem3858202 : term471.
Proof. exact (EQ_MP (@lem3858201) (@lem0)). Qed.
Lemma lem3858203 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term577 _44749.
Proof. exact (conj (@lem3858202) (@lem3858133 _44749 _44750 h1)). Qed.
Lemma lem3858205 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3858206 (_44749 : int) : term578 _44749.
Proof. exact (@lem3858205 term143 (real_of_int _44749)). Qed.
Lemma lem3858207 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term579 _44749.
Proof. exact (@lem3858206 _44749 (@lem3858203 _44749 _44750 h1)). Qed.
Lemma lem3858208 (_44749 : int) : (term542 _44749) = (real_of_int _44749).
Proof. exact (@lem1982733 (real_of_int _44749)). Qed.
Lemma lem3858209 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3858210 (_44749 : int) : (term580 _44749) = (term218 _44749).
Proof. exact (MK_COMB (@lem3858209) (@lem3858208 _44749)). Qed.
Lemma lem3858211 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3858212 (_44749 : int) : (term579 _44749) = (term219 _44749).
Proof. exact (MK_COMB (@lem3858210 _44749) (@lem3858211)). Qed.
Lemma lem3858213 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term219 _44749.
Proof. exact (EQ_MP (@lem3858212 _44749) (@lem3858207 _44749 _44750 h1)). Qed.
Lemma lem3858215 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3858216 : term471 = term251.
Proof. exact (@lem3858215 term133 term143). Qed.
Lemma lem3858218 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858219 : term143 = term224.
Proof. exact (@lem3858218 term11). Qed.
Lemma lem3858221 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858222 : term133 = term196.
Proof. exact (@lem3858221 (NUMERAL 0)). Qed.
Lemma lem3858223 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3858224 : term472 = term473.
Proof. exact (MK_COMB (@lem3858223) (@lem3858222)). Qed.
Lemma lem3858225 : term251 = term474.
Proof. exact (MK_COMB (@lem3858224) (@lem3858219)). Qed.
Lemma lem3858226 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3858228 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858229 : term251 = term252.
Proof. exact (@lem3858228 (NUMERAL 0) term11). Qed.
Lemma lem3858230 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858231 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858232 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858231 h1) (fun h1 : term252 = True => @lem3858230)). Qed.
Lemma lem3858233 : term252 = True.
Proof. exact (EQ_MP (@lem3858232) (@lem3858230)). Qed.
Lemma lem3858234 : term251 = True.
Proof. exact (TRANS (@lem3858229) (@lem3858233)). Qed.
Lemma lem3858235 : True = term251.
Proof. exact (SYM (@lem3858234)). Qed.
Lemma lem3858236 : term251.
Proof. exact (EQ_MP (@lem3858235) (@lem0)). Qed.
Lemma lem3858237 : term476.
Proof. exact (@lem3858226 (@lem3858236)). Qed.
Lemma lem3858239 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858240 : term251 = term252.
Proof. exact (@lem3858239 (NUMERAL 0) term11). Qed.
Lemma lem3858241 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858242 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858243 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858242 h1) (fun h1 : term252 = True => @lem3858241)). Qed.
Lemma lem3858244 : term252 = True.
Proof. exact (EQ_MP (@lem3858243) (@lem3858241)). Qed.
Lemma lem3858245 : term251 = True.
Proof. exact (TRANS (@lem3858240) (@lem3858244)). Qed.
Lemma lem3858246 : True = term251.
Proof. exact (SYM (@lem3858245)). Qed.
Lemma lem3858247 : term251.
Proof. exact (EQ_MP (@lem3858246) (@lem0)). Qed.
Lemma lem3858248 : term474 = term477.
Proof. exact (@lem3858237 (@lem3858247)). Qed.
Lemma lem3858250 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3858251 : term208 = term209.
Proof. exact (@lem3858250 term11 term11). Qed.
Lemma lem3858252 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858253 : term211 = term11.
Proof. exact (EQ_MP (@lem3858252) (@lem940073)). Qed.
Lemma lem3858254 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858255 : term209 = term143.
Proof. exact (MK_COMB (@lem3858254) (@lem3858253)). Qed.
Lemma lem3858256 : term208 = term143.
Proof. exact (TRANS (@lem3858251) (@lem3858255)). Qed.
Lemma lem3858258 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858259 : term263 = term133.
Proof. exact (@lem3858258 term11). Qed.
Lemma lem3858260 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3858261 : term478 = term472.
Proof. exact (MK_COMB (@lem3858260) (@lem3858259)). Qed.
Lemma lem3858262 : term477 = term251.
Proof. exact (MK_COMB (@lem3858261) (@lem3858256)). Qed.
Lemma lem3858264 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858265 : term251 = term252.
Proof. exact (@lem3858264 (NUMERAL 0) term11). Qed.
Lemma lem3858266 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858267 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858268 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858267 h1) (fun h1 : term252 = True => @lem3858266)). Qed.
Lemma lem3858269 : term252 = True.
Proof. exact (EQ_MP (@lem3858268) (@lem3858266)). Qed.
Lemma lem3858270 : term251 = True.
Proof. exact (TRANS (@lem3858265) (@lem3858269)). Qed.
Lemma lem3858271 : term477 = True.
Proof. exact (TRANS (@lem3858262) (@lem3858270)). Qed.
Lemma lem3858272 : term474 = True.
Proof. exact (TRANS (@lem3858248) (@lem3858271)). Qed.
Lemma lem3858273 : term251 = True.
Proof. exact (TRANS (@lem3858225) (@lem3858272)). Qed.
Lemma lem3858274 : term471 = True.
Proof. exact (TRANS (@lem3858216) (@lem3858273)). Qed.
Lemma lem3858275 : True = term471.
Proof. exact (SYM (@lem3858274)). Qed.
Lemma lem3858276 : term471.
Proof. exact (EQ_MP (@lem3858275) (@lem0)). Qed.
Lemma lem3858277 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term581 _44749 _44750.
Proof. exact (conj (@lem3858276) (@lem3858137 _44749 _44750 h1)). Qed.
Lemma lem3858279 (x : real) (y : real) : term582 x y.
Proof. exact (proj1 (@lem1988330 x y)). Qed.
Lemma lem3858280 (_44749 : int) (_44750 : int) : term583 _44749 _44750.
Proof. exact (@lem3858279 term143 (term236 _44749 _44750)). Qed.
Lemma lem3858281 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : (term489 _44749 _44750) = term133.
Proof. exact (@lem3858280 _44749 _44750 (@lem3858277 _44749 _44750 h1)). Qed.
Lemma lem3858282 (_44749 : int) (_44750 : int) : (term489 _44749 _44750) = (term236 _44749 _44750).
Proof. exact (@lem1982733 (term236 _44749 _44750)). Qed.
Lemma lem3858283 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3858284 (_44749 : int) (_44750 : int) : (term490 _44749 _44750) = (term239 _44749 _44750).
Proof. exact (MK_COMB (@lem3858283) (@lem3858282 _44749 _44750)). Qed.
Lemma lem3858285 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3858286 (_44749 : int) (_44750 : int) : ((term489 _44749 _44750) = term133) = ((term236 _44749 _44750) = term133).
Proof. exact (MK_COMB (@lem3858284 _44749 _44750) (@lem3858285)). Qed.
Lemma lem3858287 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : (term236 _44749 _44750) = term133.
Proof. exact (EQ_MP (@lem3858286 _44749 _44750) (@lem3858281 _44749 _44750 h1)). Qed.
Lemma lem3858289 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3858290 (_44750 : int) : term539 _44750.
Proof. exact (@lem3858289 (real_of_int _44750)). Qed.
Lemma lem3858291 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term540 _44750.
Proof. exact (@lem3858290 _44750 (@lem3858139 _44749 _44750 h1)). Qed.
Lemma lem3858292 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term556 _44750.
Proof. exact (@lem3858291 _44749 _44750 h1 term199). Qed.
Lemma lem3858293 (_44750 : int) : (term556 _44750) = ((term237 _44750) = term133).
Proof. exact (eq_refl (term556 _44750)). Qed.
Lemma lem3858300 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : (term237 _44750) = term133.
Proof. exact (EQ_MP (@lem3858293 _44750) (@lem3858292 _44749 _44750 h1)). Qed.
Lemma lem3858301 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term584 _44749 _44750.
Proof. exact (conj (@lem3858300 _44749 _44750 h1) (@lem3858287 _44749 _44750 h1)). Qed.
Lemma lem3858303 (x : real) (y : real) : term585 x y.
Proof. exact (proj1 (@lem1393126 x y)). Qed.
Lemma lem3858304 (_44749 : int) (_44750 : int) : term586 _44749 _44750.
Proof. exact (@lem3858303 (term237 _44750) (term236 _44749 _44750)). Qed.
Lemma lem3858305 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : (term587 _44749 _44750) = term133.
Proof. exact (@lem3858304 _44749 _44750 (@lem3858301 _44749 _44750 h1)). Qed.
Lemma lem3858306 (_44749 : int) (_44750 : int) : (term587 _44749 _44750) = (term588 _44749 _44750).
Proof. exact (@lem1982757 (term237 _44749) (term237 _44750) (term299 _44750)). Qed.
Lemma lem3858307 (_44750 : int) : (term573 _44750) = (term574 _44750).
Proof. exact (@lem1982763 (term237 _44750) (real_of_int _44750) term199). Qed.
Lemma lem3858308 (_44750 : int) : (term497 _44750) = (term498 _44750).
Proof. exact (@lem1982713 term199 (real_of_int _44750)). Qed.
Lemma lem3858310 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858311 : term143 = term224.
Proof. exact (@lem3858310 term11). Qed.
Lemma lem3858313 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3858314 : term199 = term200.
Proof. exact (@lem3858313 term11). Qed.
Lemma lem3858315 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3858316 : term499 = term500.
Proof. exact (MK_COMB (@lem3858315) (@lem3858314)). Qed.
Lemma lem3858317 : term501 = term502.
Proof. exact (MK_COMB (@lem3858316) (@lem3858311)). Qed.
Lemma lem3858318 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3858320 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858321 : term251 = term252.
Proof. exact (@lem3858320 (NUMERAL 0) term11). Qed.
Lemma lem3858322 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858323 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858324 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858323 h1) (fun h1 : term252 = True => @lem3858322)). Qed.
Lemma lem3858325 : term252 = True.
Proof. exact (EQ_MP (@lem3858324) (@lem3858322)). Qed.
Lemma lem3858326 : term251 = True.
Proof. exact (TRANS (@lem3858321) (@lem3858325)). Qed.
Lemma lem3858327 : True = term251.
Proof. exact (SYM (@lem3858326)). Qed.
Lemma lem3858328 : term251.
Proof. exact (EQ_MP (@lem3858327) (@lem0)). Qed.
Lemma lem3858329 : term504.
Proof. exact (@lem3858318 (@lem3858328)). Qed.
Lemma lem3858331 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858332 : term251 = term252.
Proof. exact (@lem3858331 (NUMERAL 0) term11). Qed.
Lemma lem3858333 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858334 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858335 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858334 h1) (fun h1 : term252 = True => @lem3858333)). Qed.
Lemma lem3858336 : term252 = True.
Proof. exact (EQ_MP (@lem3858335) (@lem3858333)). Qed.
Lemma lem3858337 : term251 = True.
Proof. exact (TRANS (@lem3858332) (@lem3858336)). Qed.
Lemma lem3858338 : True = term251.
Proof. exact (SYM (@lem3858337)). Qed.
Lemma lem3858339 : term251.
Proof. exact (EQ_MP (@lem3858338) (@lem0)). Qed.
Lemma lem3858340 : term505.
Proof. exact (@lem3858329 (@lem3858339)). Qed.
Lemma lem3858342 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858343 : term251 = term252.
Proof. exact (@lem3858342 (NUMERAL 0) term11). Qed.
Lemma lem3858344 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858345 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858346 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858345 h1) (fun h1 : term252 = True => @lem3858344)). Qed.
Lemma lem3858347 : term252 = True.
Proof. exact (EQ_MP (@lem3858346) (@lem3858344)). Qed.
Lemma lem3858348 : term251 = True.
Proof. exact (TRANS (@lem3858343) (@lem3858347)). Qed.
Lemma lem3858349 : True = term251.
Proof. exact (SYM (@lem3858348)). Qed.
Lemma lem3858350 : term251.
Proof. exact (EQ_MP (@lem3858349) (@lem0)). Qed.
Lemma lem3858351 : term506.
Proof. exact (@lem3858340 (@lem3858350)). Qed.
Lemma lem3858353 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3858354 : term208 = term209.
Proof. exact (@lem3858353 term11 term11). Qed.
Lemma lem3858355 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858356 : term211 = term11.
Proof. exact (EQ_MP (@lem3858355) (@lem940073)). Qed.
Lemma lem3858357 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858358 : term209 = term143.
Proof. exact (MK_COMB (@lem3858357) (@lem3858356)). Qed.
Lemma lem3858359 : term208 = term143.
Proof. exact (TRANS (@lem3858354) (@lem3858358)). Qed.
Lemma lem3858361 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3858362 : term225 = term230.
Proof. exact (@lem3858361 term11 term11). Qed.
Lemma lem3858363 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858364 : term211 = term11.
Proof. exact (EQ_MP (@lem3858363) (@lem940073)). Qed.
Lemma lem3858365 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858366 : term209 = term143.
Proof. exact (MK_COMB (@lem3858365) (@lem3858364)). Qed.
Lemma lem3858367 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3858368 : term230 = term199.
Proof. exact (MK_COMB (@lem3858367) (@lem3858366)). Qed.
Lemma lem3858369 : term225 = term199.
Proof. exact (TRANS (@lem3858362) (@lem3858368)). Qed.
Lemma lem3858370 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3858371 : term507 = term499.
Proof. exact (MK_COMB (@lem3858370) (@lem3858369)). Qed.
Lemma lem3858372 : term508 = term501.
Proof. exact (MK_COMB (@lem3858371) (@lem3858359)). Qed.
Lemma lem3858374 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3858375 : term501 = term133.
Proof. exact (@lem3858374 term11). Qed.
Lemma lem3858376 : term508 = term133.
Proof. exact (TRANS (@lem3858372) (@lem3858375)). Qed.
Lemma lem3858377 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3858378 : term510 = term261.
Proof. exact (MK_COMB (@lem3858377) (@lem3858376)). Qed.
Lemma lem3858379 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3858380 : term511 = term263.
Proof. exact (MK_COMB (@lem3858378) (@lem3858379)). Qed.
Lemma lem3858382 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858383 : term263 = term133.
Proof. exact (@lem3858382 term11). Qed.
Lemma lem3858384 : term511 = term133.
Proof. exact (TRANS (@lem3858380) (@lem3858383)). Qed.
Lemma lem3858386 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3858387 : term208 = term209.
Proof. exact (@lem3858386 term11 term11). Qed.
Lemma lem3858388 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858389 : term211 = term11.
Proof. exact (EQ_MP (@lem3858388) (@lem940073)). Qed.
Lemma lem3858390 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858391 : term209 = term143.
Proof. exact (MK_COMB (@lem3858390) (@lem3858389)). Qed.
Lemma lem3858392 : term208 = term143.
Proof. exact (TRANS (@lem3858387) (@lem3858391)). Qed.
Lemma lem3858393 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3858394 : term265 = term263.
Proof. exact (MK_COMB (@lem3858393) (@lem3858392)). Qed.
Lemma lem3858396 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858397 : term263 = term133.
Proof. exact (@lem3858396 term11). Qed.
Lemma lem3858398 : term265 = term133.
Proof. exact (TRANS (@lem3858394) (@lem3858397)). Qed.
Lemma lem3858399 : term133 = term265.
Proof. exact (SYM (@lem3858398)). Qed.
Lemma lem3858400 : term511 = term265.
Proof. exact (TRANS (@lem3858384) (@lem3858399)). Qed.
Lemma lem3858401 : term502 = term196.
Proof. exact (@lem3858351 (@lem3858400)). Qed.
Lemma lem3858402 : term501 = term196.
Proof. exact (TRANS (@lem3858317) (@lem3858401)). Qed.
Lemma lem3858404 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3858405 : term196 = term133.
Proof. exact (@lem3858404 term133). Qed.
Lemma lem3858406 : term501 = term133.
Proof. exact (TRANS (@lem3858402) (@lem3858405)). Qed.
Lemma lem3858407 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3858408 : term512 = term261.
Proof. exact (MK_COMB (@lem3858407) (@lem3858406)). Qed.
Lemma lem3858409 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3858410 (_44750 : int) : (term498 _44750) = (term513 _44750).
Proof. exact (MK_COMB (@lem3858408) (@lem3858409 _44750)). Qed.
Lemma lem3858411 (_44750 : int) : (term497 _44750) = (term513 _44750).
Proof. exact (TRANS (@lem3858308 _44750) (@lem3858410 _44750)). Qed.
Lemma lem3858412 (_44750 : int) : (term513 _44750) = term133.
Proof. exact (@lem1982719 (real_of_int _44750)). Qed.
Lemma lem3858413 (_44750 : int) : (term497 _44750) = term133.
Proof. exact (TRANS (@lem3858411 _44750) (@lem3858412 _44750)). Qed.
Lemma lem3858414 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3858415 (_44750 : int) : (term514 _44750) = term175.
Proof. exact (MK_COMB (@lem3858414) (@lem3858413 _44750)). Qed.
Lemma lem3858416 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3858417 (_44750 : int) : (term574 _44750) = term519.
Proof. exact (MK_COMB (@lem3858415 _44750) (@lem3858416)). Qed.
Lemma lem3858418 (_44750 : int) : (term573 _44750) = term519.
Proof. exact (TRANS (@lem3858307 _44750) (@lem3858417 _44750)). Qed.
Lemma lem3858419 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3858420 (_44750 : int) : (term573 _44750) = term199.
Proof. exact (TRANS (@lem3858418 _44750) (@lem3858419)). Qed.
Lemma lem3858421 (_44749 : int) : (term233 _44749) = (term233 _44749).
Proof. exact (eq_refl (term233 _44749)). Qed.
Lemma lem3858422 (_44750 : int) (_44749 : int) : (term588 _44749 _44750) = (term234 _44749).
Proof. exact (MK_COMB (@lem3858421 _44749) (@lem3858420 _44750)). Qed.
Lemma lem3858423 (_44750 : int) (_44749 : int) : (term587 _44749 _44750) = (term234 _44749).
Proof. exact (TRANS (@lem3858306 _44749 _44750) (@lem3858422 _44750 _44749)). Qed.
Lemma lem3858424 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3858425 (_44750 : int) (_44749 : int) : (term589 _44749 _44750) = (term590 _44749).
Proof. exact (MK_COMB (@lem3858424) (@lem3858423 _44750 _44749)). Qed.
Lemma lem3858426 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3858427 (_44750 : int) (_44749 : int) : ((term587 _44749 _44750) = term133) = ((term234 _44749) = term133).
Proof. exact (MK_COMB (@lem3858425 _44750 _44749) (@lem3858426)). Qed.
Lemma lem3858428 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : (term234 _44749) = term133.
Proof. exact (EQ_MP (@lem3858427 _44750 _44749) (@lem3858305 _44749 _44750 h1)). Qed.
Lemma lem3858430 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3858431 (_44749 : int) : term591 _44749.
Proof. exact (@lem3858430 (term234 _44749)). Qed.
Lemma lem3858432 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term592 _44749.
Proof. exact (@lem3858431 _44749 (@lem3858428 _44749 _44750 h1)). Qed.
Lemma lem3858433 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term593 _44749.
Proof. exact (@lem3858432 _44749 _44750 h1 term143). Qed.
Lemma lem3858434 (_44749 : int) : (term593 _44749) = ((term594 _44749) = term133).
Proof. exact (eq_refl (term593 _44749)). Qed.
Lemma lem3858435 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : (term594 _44749) = term133.
Proof. exact (EQ_MP (@lem3858434 _44749) (@lem3858433 _44749 _44750 h1)). Qed.
Lemma lem3858436 (_44749 : int) : (term594 _44749) = (term234 _44749).
Proof. exact (@lem1982733 (term234 _44749)). Qed.
Lemma lem3858437 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3858438 (_44749 : int) : (term595 _44749) = (term590 _44749).
Proof. exact (MK_COMB (@lem3858437) (@lem3858436 _44749)). Qed.
Lemma lem3858439 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3858440 (_44749 : int) : ((term594 _44749) = term133) = ((term234 _44749) = term133).
Proof. exact (MK_COMB (@lem3858438 _44749) (@lem3858439)). Qed.
Lemma lem3858441 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : (term234 _44749) = term133.
Proof. exact (EQ_MP (@lem3858440 _44749) (@lem3858435 _44749 _44750 h1)). Qed.
Lemma lem3858442 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term596 _44749.
Proof. exact (conj (@lem3858441 _44749 _44750 h1) (@lem3858213 _44749 _44750 h1)). Qed.
Lemma lem3858444 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3858445 (_44749 : int) : term597 _44749.
Proof. exact (@lem3858444 (term234 _44749) (real_of_int _44749)). Qed.
Lemma lem3858446 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term598 _44749.
Proof. exact (@lem3858445 _44749 (@lem3858442 _44749 _44750 h1)). Qed.
Lemma lem3858447 (_44749 : int) : (term599 _44749) = (term574 _44749).
Proof. exact (@lem1982759 (term237 _44749) (real_of_int _44749) term199). Qed.
Lemma lem3858448 (_44749 : int) : (term497 _44749) = (term498 _44749).
Proof. exact (@lem1982713 term199 (real_of_int _44749)). Qed.
Lemma lem3858450 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858451 : term143 = term224.
Proof. exact (@lem3858450 term11). Qed.
Lemma lem3858453 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3858454 : term199 = term200.
Proof. exact (@lem3858453 term11). Qed.
Lemma lem3858455 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3858456 : term499 = term500.
Proof. exact (MK_COMB (@lem3858455) (@lem3858454)). Qed.
Lemma lem3858457 : term501 = term502.
Proof. exact (MK_COMB (@lem3858456) (@lem3858451)). Qed.
Lemma lem3858458 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3858460 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858461 : term251 = term252.
Proof. exact (@lem3858460 (NUMERAL 0) term11). Qed.
Lemma lem3858462 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858463 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858464 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858463 h1) (fun h1 : term252 = True => @lem3858462)). Qed.
Lemma lem3858465 : term252 = True.
Proof. exact (EQ_MP (@lem3858464) (@lem3858462)). Qed.
Lemma lem3858466 : term251 = True.
Proof. exact (TRANS (@lem3858461) (@lem3858465)). Qed.
Lemma lem3858467 : True = term251.
Proof. exact (SYM (@lem3858466)). Qed.
Lemma lem3858468 : term251.
Proof. exact (EQ_MP (@lem3858467) (@lem0)). Qed.
Lemma lem3858469 : term504.
Proof. exact (@lem3858458 (@lem3858468)). Qed.
Lemma lem3858471 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858472 : term251 = term252.
Proof. exact (@lem3858471 (NUMERAL 0) term11). Qed.
Lemma lem3858473 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858474 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858475 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858474 h1) (fun h1 : term252 = True => @lem3858473)). Qed.
Lemma lem3858476 : term252 = True.
Proof. exact (EQ_MP (@lem3858475) (@lem3858473)). Qed.
Lemma lem3858477 : term251 = True.
Proof. exact (TRANS (@lem3858472) (@lem3858476)). Qed.
Lemma lem3858478 : True = term251.
Proof. exact (SYM (@lem3858477)). Qed.
Lemma lem3858479 : term251.
Proof. exact (EQ_MP (@lem3858478) (@lem0)). Qed.
Lemma lem3858480 : term505.
Proof. exact (@lem3858469 (@lem3858479)). Qed.
Lemma lem3858482 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858483 : term251 = term252.
Proof. exact (@lem3858482 (NUMERAL 0) term11). Qed.
Lemma lem3858484 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858485 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858486 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858485 h1) (fun h1 : term252 = True => @lem3858484)). Qed.
Lemma lem3858487 : term252 = True.
Proof. exact (EQ_MP (@lem3858486) (@lem3858484)). Qed.
Lemma lem3858488 : term251 = True.
Proof. exact (TRANS (@lem3858483) (@lem3858487)). Qed.
Lemma lem3858489 : True = term251.
Proof. exact (SYM (@lem3858488)). Qed.
Lemma lem3858490 : term251.
Proof. exact (EQ_MP (@lem3858489) (@lem0)). Qed.
Lemma lem3858491 : term506.
Proof. exact (@lem3858480 (@lem3858490)). Qed.
Lemma lem3858493 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3858494 : term208 = term209.
Proof. exact (@lem3858493 term11 term11). Qed.
Lemma lem3858495 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858496 : term211 = term11.
Proof. exact (EQ_MP (@lem3858495) (@lem940073)). Qed.
Lemma lem3858497 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858498 : term209 = term143.
Proof. exact (MK_COMB (@lem3858497) (@lem3858496)). Qed.
Lemma lem3858499 : term208 = term143.
Proof. exact (TRANS (@lem3858494) (@lem3858498)). Qed.
Lemma lem3858501 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3858502 : term225 = term230.
Proof. exact (@lem3858501 term11 term11). Qed.
Lemma lem3858503 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858504 : term211 = term11.
Proof. exact (EQ_MP (@lem3858503) (@lem940073)). Qed.
Lemma lem3858505 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858506 : term209 = term143.
Proof. exact (MK_COMB (@lem3858505) (@lem3858504)). Qed.
Lemma lem3858507 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3858508 : term230 = term199.
Proof. exact (MK_COMB (@lem3858507) (@lem3858506)). Qed.
Lemma lem3858509 : term225 = term199.
Proof. exact (TRANS (@lem3858502) (@lem3858508)). Qed.
Lemma lem3858510 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3858511 : term507 = term499.
Proof. exact (MK_COMB (@lem3858510) (@lem3858509)). Qed.
Lemma lem3858512 : term508 = term501.
Proof. exact (MK_COMB (@lem3858511) (@lem3858499)). Qed.
Lemma lem3858514 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3858515 : term501 = term133.
Proof. exact (@lem3858514 term11). Qed.
Lemma lem3858516 : term508 = term133.
Proof. exact (TRANS (@lem3858512) (@lem3858515)). Qed.
Lemma lem3858517 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3858518 : term510 = term261.
Proof. exact (MK_COMB (@lem3858517) (@lem3858516)). Qed.
Lemma lem3858519 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3858520 : term511 = term263.
Proof. exact (MK_COMB (@lem3858518) (@lem3858519)). Qed.
Lemma lem3858522 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858523 : term263 = term133.
Proof. exact (@lem3858522 term11). Qed.
Lemma lem3858524 : term511 = term133.
Proof. exact (TRANS (@lem3858520) (@lem3858523)). Qed.
Lemma lem3858526 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3858527 : term208 = term209.
Proof. exact (@lem3858526 term11 term11). Qed.
Lemma lem3858528 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858529 : term211 = term11.
Proof. exact (EQ_MP (@lem3858528) (@lem940073)). Qed.
Lemma lem3858530 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858531 : term209 = term143.
Proof. exact (MK_COMB (@lem3858530) (@lem3858529)). Qed.
Lemma lem3858532 : term208 = term143.
Proof. exact (TRANS (@lem3858527) (@lem3858531)). Qed.
Lemma lem3858533 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3858534 : term265 = term263.
Proof. exact (MK_COMB (@lem3858533) (@lem3858532)). Qed.
Lemma lem3858536 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858537 : term263 = term133.
Proof. exact (@lem3858536 term11). Qed.
Lemma lem3858538 : term265 = term133.
Proof. exact (TRANS (@lem3858534) (@lem3858537)). Qed.
Lemma lem3858539 : term133 = term265.
Proof. exact (SYM (@lem3858538)). Qed.
Lemma lem3858540 : term511 = term265.
Proof. exact (TRANS (@lem3858524) (@lem3858539)). Qed.
Lemma lem3858541 : term502 = term196.
Proof. exact (@lem3858491 (@lem3858540)). Qed.
Lemma lem3858542 : term501 = term196.
Proof. exact (TRANS (@lem3858457) (@lem3858541)). Qed.
Lemma lem3858544 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3858545 : term196 = term133.
Proof. exact (@lem3858544 term133). Qed.
Lemma lem3858546 : term501 = term133.
Proof. exact (TRANS (@lem3858542) (@lem3858545)). Qed.
Lemma lem3858547 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3858548 : term512 = term261.
Proof. exact (MK_COMB (@lem3858547) (@lem3858546)). Qed.
Lemma lem3858549 (_44749 : int) : (real_of_int _44749) = (real_of_int _44749).
Proof. exact (eq_refl (real_of_int _44749)). Qed.
Lemma lem3858550 (_44749 : int) : (term498 _44749) = (term513 _44749).
Proof. exact (MK_COMB (@lem3858548) (@lem3858549 _44749)). Qed.
Lemma lem3858551 (_44749 : int) : (term497 _44749) = (term513 _44749).
Proof. exact (TRANS (@lem3858448 _44749) (@lem3858550 _44749)). Qed.
Lemma lem3858552 (_44749 : int) : (term513 _44749) = term133.
Proof. exact (@lem1982719 (real_of_int _44749)). Qed.
Lemma lem3858553 (_44749 : int) : (term497 _44749) = term133.
Proof. exact (TRANS (@lem3858551 _44749) (@lem3858552 _44749)). Qed.
Lemma lem3858554 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3858555 (_44749 : int) : (term514 _44749) = term175.
Proof. exact (MK_COMB (@lem3858554) (@lem3858553 _44749)). Qed.
Lemma lem3858556 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3858557 (_44749 : int) : (term574 _44749) = term519.
Proof. exact (MK_COMB (@lem3858555 _44749) (@lem3858556)). Qed.
Lemma lem3858558 (_44749 : int) : (term599 _44749) = term519.
Proof. exact (TRANS (@lem3858447 _44749) (@lem3858557 _44749)). Qed.
Lemma lem3858559 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3858560 (_44749 : int) : (term599 _44749) = term199.
Proof. exact (TRANS (@lem3858558 _44749) (@lem3858559)). Qed.
Lemma lem3858561 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3858562 (_44749 : int) : (term600 _44749) = term521.
Proof. exact (MK_COMB (@lem3858561) (@lem3858560 _44749)). Qed.
Lemma lem3858563 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3858564 (_44749 : int) : (term598 _44749) = term522.
Proof. exact (MK_COMB (@lem3858562 _44749) (@lem3858563)). Qed.
Lemma lem3858565 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : term522.
Proof. exact (EQ_MP (@lem3858564 _44749) (@lem3858446 _44749 _44750 h1)). Qed.
Lemma lem3858567 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3858568 : term522 = term523.
Proof. exact (@lem3858567 term133 term199). Qed.
Lemma lem3858570 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3858571 : term199 = term200.
Proof. exact (@lem3858570 term11). Qed.
Lemma lem3858573 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858574 : term133 = term196.
Proof. exact (@lem3858573 (NUMERAL 0)). Qed.
Lemma lem3858575 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3858576 : term135 = term524.
Proof. exact (MK_COMB (@lem3858575) (@lem3858574)). Qed.
Lemma lem3858577 : term523 = term525.
Proof. exact (MK_COMB (@lem3858576) (@lem3858571)). Qed.
Lemma lem3858578 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3858580 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858581 : term251 = term252.
Proof. exact (@lem3858580 (NUMERAL 0) term11). Qed.
Lemma lem3858582 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858583 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858584 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858583 h1) (fun h1 : term252 = True => @lem3858582)). Qed.
Lemma lem3858585 : term252 = True.
Proof. exact (EQ_MP (@lem3858584) (@lem3858582)). Qed.
Lemma lem3858586 : term251 = True.
Proof. exact (TRANS (@lem3858581) (@lem3858585)). Qed.
Lemma lem3858587 : True = term251.
Proof. exact (SYM (@lem3858586)). Qed.
Lemma lem3858588 : term251.
Proof. exact (EQ_MP (@lem3858587) (@lem0)). Qed.
Lemma lem3858589 : term527.
Proof. exact (@lem3858578 (@lem3858588)). Qed.
Lemma lem3858591 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858592 : term251 = term252.
Proof. exact (@lem3858591 (NUMERAL 0) term11). Qed.
Lemma lem3858593 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858594 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858595 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858594 h1) (fun h1 : term252 = True => @lem3858593)). Qed.
Lemma lem3858596 : term252 = True.
Proof. exact (EQ_MP (@lem3858595) (@lem3858593)). Qed.
Lemma lem3858597 : term251 = True.
Proof. exact (TRANS (@lem3858592) (@lem3858596)). Qed.
Lemma lem3858598 : True = term251.
Proof. exact (SYM (@lem3858597)). Qed.
Lemma lem3858599 : term251.
Proof. exact (EQ_MP (@lem3858598) (@lem0)). Qed.
Lemma lem3858600 : term525 = term528.
Proof. exact (@lem3858589 (@lem3858599)). Qed.
Lemma lem3858602 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3858603 : term225 = term230.
Proof. exact (@lem3858602 term11 term11). Qed.
Lemma lem3858604 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858605 : term211 = term11.
Proof. exact (EQ_MP (@lem3858604) (@lem940073)). Qed.
Lemma lem3858606 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858607 : term209 = term143.
Proof. exact (MK_COMB (@lem3858606) (@lem3858605)). Qed.
Lemma lem3858608 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3858609 : term230 = term199.
Proof. exact (MK_COMB (@lem3858608) (@lem3858607)). Qed.
Lemma lem3858610 : term225 = term199.
Proof. exact (TRANS (@lem3858603) (@lem3858609)). Qed.
Lemma lem3858612 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858613 : term263 = term133.
Proof. exact (@lem3858612 term11). Qed.
Lemma lem3858614 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3858615 : term529 = term135.
Proof. exact (MK_COMB (@lem3858614) (@lem3858613)). Qed.
Lemma lem3858616 : term528 = term523.
Proof. exact (MK_COMB (@lem3858615) (@lem3858610)). Qed.
Lemma lem3858618 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3858619 : term523 = term532.
Proof. exact (@lem3858618 (NUMERAL 0) term11). Qed.
Lemma lem3858620 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858621 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3858622 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858621 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3858620)). Qed.
Lemma lem3858623 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3858622) (@lem3858620)). Qed.
Lemma lem3858624 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3858625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3858626 : term533 = (and True).
Proof. exact (MK_COMB (@lem3858625) (@lem3858624)). Qed.
Lemma lem3858627 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3858626) (@lem3858623)). Qed.
Lemma lem3858629 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3858630 : term532 = False.
Proof. exact (TRANS (@lem3858627) (@lem3858629)). Qed.
Lemma lem3858631 : term523 = False.
Proof. exact (TRANS (@lem3858619) (@lem3858630)). Qed.
Lemma lem3858632 : term528 = False.
Proof. exact (TRANS (@lem3858616) (@lem3858631)). Qed.
Lemma lem3858633 : term525 = False.
Proof. exact (TRANS (@lem3858600) (@lem3858632)). Qed.
Lemma lem3858634 : term523 = False.
Proof. exact (TRANS (@lem3858577) (@lem3858633)). Qed.
Lemma lem3858635 : term522 = False.
Proof. exact (TRANS (@lem3858568) (@lem3858634)). Qed.
Lemma lem3858636 (_44749 : int) (_44750 : int) (h1 : term576 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3858635) (@lem3858565 _44749 _44750 h1)). Qed.
Lemma lem3858637 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term601 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3858638 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term459 _44749 _44750.
Proof. exact (proj2 (@lem3858637 _44749 _44750 h1)). Qed.
Lemma lem3858640 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term410 _44749 _44750.
Proof. exact (proj2 (@lem3858638 _44749 _44750 h1)). Qed.
Lemma lem3858642 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term361 _44749 _44750.
Proof. exact (proj2 (@lem3858640 _44749 _44750 h1)). Qed.
Lemma lem3858643 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term272 _44750 _44749.
Proof. exact (proj1 (@lem3858640 _44749 _44750 h1)). Qed.
Lemma lem3858644 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : (real_of_int _44749) = term133.
Proof. exact (proj2 (@lem3858643 _44749 _44750 h1)). Qed.
Lemma lem3858646 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term286 _44749 _44750.
Proof. exact (proj2 (@lem3858642 _44749 _44750 h1)). Qed.
Lemma lem3858647 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : (real_of_int _44750) = term133.
Proof. exact (proj1 (@lem3858642 _44749 _44750 h1)). Qed.
Lemma lem3858649 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3858650 : term471 = term251.
Proof. exact (@lem3858649 term133 term143). Qed.
Lemma lem3858652 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858653 : term143 = term224.
Proof. exact (@lem3858652 term11). Qed.
Lemma lem3858655 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858656 : term133 = term196.
Proof. exact (@lem3858655 (NUMERAL 0)). Qed.
Lemma lem3858657 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3858658 : term472 = term473.
Proof. exact (MK_COMB (@lem3858657) (@lem3858656)). Qed.
Lemma lem3858659 : term251 = term474.
Proof. exact (MK_COMB (@lem3858658) (@lem3858653)). Qed.
Lemma lem3858660 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3858662 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858663 : term251 = term252.
Proof. exact (@lem3858662 (NUMERAL 0) term11). Qed.
Lemma lem3858664 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858665 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858666 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858665 h1) (fun h1 : term252 = True => @lem3858664)). Qed.
Lemma lem3858667 : term252 = True.
Proof. exact (EQ_MP (@lem3858666) (@lem3858664)). Qed.
Lemma lem3858668 : term251 = True.
Proof. exact (TRANS (@lem3858663) (@lem3858667)). Qed.
Lemma lem3858669 : True = term251.
Proof. exact (SYM (@lem3858668)). Qed.
Lemma lem3858670 : term251.
Proof. exact (EQ_MP (@lem3858669) (@lem0)). Qed.
Lemma lem3858671 : term476.
Proof. exact (@lem3858660 (@lem3858670)). Qed.
Lemma lem3858673 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858674 : term251 = term252.
Proof. exact (@lem3858673 (NUMERAL 0) term11). Qed.
Lemma lem3858675 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858676 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858677 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858676 h1) (fun h1 : term252 = True => @lem3858675)). Qed.
Lemma lem3858678 : term252 = True.
Proof. exact (EQ_MP (@lem3858677) (@lem3858675)). Qed.
Lemma lem3858679 : term251 = True.
Proof. exact (TRANS (@lem3858674) (@lem3858678)). Qed.
Lemma lem3858680 : True = term251.
Proof. exact (SYM (@lem3858679)). Qed.
Lemma lem3858681 : term251.
Proof. exact (EQ_MP (@lem3858680) (@lem0)). Qed.
Lemma lem3858682 : term474 = term477.
Proof. exact (@lem3858671 (@lem3858681)). Qed.
Lemma lem3858684 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3858685 : term208 = term209.
Proof. exact (@lem3858684 term11 term11). Qed.
Lemma lem3858686 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858687 : term211 = term11.
Proof. exact (EQ_MP (@lem3858686) (@lem940073)). Qed.
Lemma lem3858688 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858689 : term209 = term143.
Proof. exact (MK_COMB (@lem3858688) (@lem3858687)). Qed.
Lemma lem3858690 : term208 = term143.
Proof. exact (TRANS (@lem3858685) (@lem3858689)). Qed.
Lemma lem3858692 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858693 : term263 = term133.
Proof. exact (@lem3858692 term11). Qed.
Lemma lem3858694 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3858695 : term478 = term472.
Proof. exact (MK_COMB (@lem3858694) (@lem3858693)). Qed.
Lemma lem3858696 : term477 = term251.
Proof. exact (MK_COMB (@lem3858695) (@lem3858690)). Qed.
Lemma lem3858698 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858699 : term251 = term252.
Proof. exact (@lem3858698 (NUMERAL 0) term11). Qed.
Lemma lem3858700 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858701 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858702 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858701 h1) (fun h1 : term252 = True => @lem3858700)). Qed.
Lemma lem3858703 : term252 = True.
Proof. exact (EQ_MP (@lem3858702) (@lem3858700)). Qed.
Lemma lem3858704 : term251 = True.
Proof. exact (TRANS (@lem3858699) (@lem3858703)). Qed.
Lemma lem3858705 : term477 = True.
Proof. exact (TRANS (@lem3858696) (@lem3858704)). Qed.
Lemma lem3858706 : term474 = True.
Proof. exact (TRANS (@lem3858682) (@lem3858705)). Qed.
Lemma lem3858707 : term251 = True.
Proof. exact (TRANS (@lem3858659) (@lem3858706)). Qed.
Lemma lem3858708 : term471 = True.
Proof. exact (TRANS (@lem3858650) (@lem3858707)). Qed.
Lemma lem3858709 : True = term471.
Proof. exact (SYM (@lem3858708)). Qed.
Lemma lem3858710 : term471.
Proof. exact (EQ_MP (@lem3858709) (@lem0)). Qed.
Lemma lem3858711 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term535 _44749 _44750.
Proof. exact (conj (@lem3858710) (@lem3858646 _44749 _44750 h1)). Qed.
Lemma lem3858713 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3858714 (_44749 : int) (_44750 : int) : term536 _44749 _44750.
Proof. exact (@lem3858713 term143 (term236 _44749 _44750)). Qed.
Lemma lem3858715 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term537 _44749 _44750.
Proof. exact (@lem3858714 _44749 _44750 (@lem3858711 _44749 _44750 h1)). Qed.
Lemma lem3858716 (_44749 : int) (_44750 : int) : (term489 _44749 _44750) = (term236 _44749 _44750).
Proof. exact (@lem1982733 (term236 _44749 _44750)). Qed.
Lemma lem3858717 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3858718 (_44749 : int) (_44750 : int) : (term538 _44749 _44750) = (term285 _44749 _44750).
Proof. exact (MK_COMB (@lem3858717) (@lem3858716 _44749 _44750)). Qed.
Lemma lem3858719 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3858720 (_44749 : int) (_44750 : int) : (term537 _44749 _44750) = (term286 _44749 _44750).
Proof. exact (MK_COMB (@lem3858718 _44749 _44750) (@lem3858719)). Qed.
Lemma lem3858721 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term286 _44749 _44750.
Proof. exact (EQ_MP (@lem3858720 _44749 _44750) (@lem3858715 _44749 _44750 h1)). Qed.
Lemma lem3858723 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3858724 (_44750 : int) : term539 _44750.
Proof. exact (@lem3858723 (real_of_int _44750)). Qed.
Lemma lem3858725 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term540 _44750.
Proof. exact (@lem3858724 _44750 (@lem3858647 _44749 _44750 h1)). Qed.
Lemma lem3858726 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term556 _44750.
Proof. exact (@lem3858725 _44749 _44750 h1 term199). Qed.
Lemma lem3858727 (_44750 : int) : (term556 _44750) = ((term237 _44750) = term133).
Proof. exact (eq_refl (term556 _44750)). Qed.
Lemma lem3858734 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : (term237 _44750) = term133.
Proof. exact (EQ_MP (@lem3858727 _44750) (@lem3858726 _44749 _44750 h1)). Qed.
Lemma lem3858735 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term602 _44749 _44750.
Proof. exact (conj (@lem3858734 _44749 _44750 h1) (@lem3858721 _44749 _44750 h1)). Qed.
Lemma lem3858737 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3858738 (_44749 : int) (_44750 : int) : term603 _44749 _44750.
Proof. exact (@lem3858737 (term237 _44750) (term236 _44749 _44750)). Qed.
Lemma lem3858739 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term604 _44749 _44750.
Proof. exact (@lem3858738 _44749 _44750 (@lem3858735 _44749 _44750 h1)). Qed.
Lemma lem3858740 (_44749 : int) (_44750 : int) : (term587 _44749 _44750) = (term588 _44749 _44750).
Proof. exact (@lem1982757 (term237 _44749) (term237 _44750) (term299 _44750)). Qed.
Lemma lem3858741 (_44750 : int) : (term573 _44750) = (term574 _44750).
Proof. exact (@lem1982763 (term237 _44750) (real_of_int _44750) term199). Qed.
Lemma lem3858742 (_44750 : int) : (term497 _44750) = (term498 _44750).
Proof. exact (@lem1982713 term199 (real_of_int _44750)). Qed.
Lemma lem3858744 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858745 : term143 = term224.
Proof. exact (@lem3858744 term11). Qed.
Lemma lem3858747 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3858748 : term199 = term200.
Proof. exact (@lem3858747 term11). Qed.
Lemma lem3858749 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3858750 : term499 = term500.
Proof. exact (MK_COMB (@lem3858749) (@lem3858748)). Qed.
Lemma lem3858751 : term501 = term502.
Proof. exact (MK_COMB (@lem3858750) (@lem3858745)). Qed.
Lemma lem3858752 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3858754 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858755 : term251 = term252.
Proof. exact (@lem3858754 (NUMERAL 0) term11). Qed.
Lemma lem3858756 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858757 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858758 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858757 h1) (fun h1 : term252 = True => @lem3858756)). Qed.
Lemma lem3858759 : term252 = True.
Proof. exact (EQ_MP (@lem3858758) (@lem3858756)). Qed.
Lemma lem3858760 : term251 = True.
Proof. exact (TRANS (@lem3858755) (@lem3858759)). Qed.
Lemma lem3858761 : True = term251.
Proof. exact (SYM (@lem3858760)). Qed.
Lemma lem3858762 : term251.
Proof. exact (EQ_MP (@lem3858761) (@lem0)). Qed.
Lemma lem3858763 : term504.
Proof. exact (@lem3858752 (@lem3858762)). Qed.
Lemma lem3858765 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858766 : term251 = term252.
Proof. exact (@lem3858765 (NUMERAL 0) term11). Qed.
Lemma lem3858767 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858768 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858769 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858768 h1) (fun h1 : term252 = True => @lem3858767)). Qed.
Lemma lem3858770 : term252 = True.
Proof. exact (EQ_MP (@lem3858769) (@lem3858767)). Qed.
Lemma lem3858771 : term251 = True.
Proof. exact (TRANS (@lem3858766) (@lem3858770)). Qed.
Lemma lem3858772 : True = term251.
Proof. exact (SYM (@lem3858771)). Qed.
Lemma lem3858773 : term251.
Proof. exact (EQ_MP (@lem3858772) (@lem0)). Qed.
Lemma lem3858774 : term505.
Proof. exact (@lem3858763 (@lem3858773)). Qed.
Lemma lem3858776 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858777 : term251 = term252.
Proof. exact (@lem3858776 (NUMERAL 0) term11). Qed.
Lemma lem3858778 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858779 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858780 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858779 h1) (fun h1 : term252 = True => @lem3858778)). Qed.
Lemma lem3858781 : term252 = True.
Proof. exact (EQ_MP (@lem3858780) (@lem3858778)). Qed.
Lemma lem3858782 : term251 = True.
Proof. exact (TRANS (@lem3858777) (@lem3858781)). Qed.
Lemma lem3858783 : True = term251.
Proof. exact (SYM (@lem3858782)). Qed.
Lemma lem3858784 : term251.
Proof. exact (EQ_MP (@lem3858783) (@lem0)). Qed.
Lemma lem3858785 : term506.
Proof. exact (@lem3858774 (@lem3858784)). Qed.
Lemma lem3858787 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3858788 : term208 = term209.
Proof. exact (@lem3858787 term11 term11). Qed.
Lemma lem3858789 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858790 : term211 = term11.
Proof. exact (EQ_MP (@lem3858789) (@lem940073)). Qed.
Lemma lem3858791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858792 : term209 = term143.
Proof. exact (MK_COMB (@lem3858791) (@lem3858790)). Qed.
Lemma lem3858793 : term208 = term143.
Proof. exact (TRANS (@lem3858788) (@lem3858792)). Qed.
Lemma lem3858795 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3858796 : term225 = term230.
Proof. exact (@lem3858795 term11 term11). Qed.
Lemma lem3858797 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858798 : term211 = term11.
Proof. exact (EQ_MP (@lem3858797) (@lem940073)). Qed.
Lemma lem3858799 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858800 : term209 = term143.
Proof. exact (MK_COMB (@lem3858799) (@lem3858798)). Qed.
Lemma lem3858801 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3858802 : term230 = term199.
Proof. exact (MK_COMB (@lem3858801) (@lem3858800)). Qed.
Lemma lem3858803 : term225 = term199.
Proof. exact (TRANS (@lem3858796) (@lem3858802)). Qed.
Lemma lem3858804 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3858805 : term507 = term499.
Proof. exact (MK_COMB (@lem3858804) (@lem3858803)). Qed.
Lemma lem3858806 : term508 = term501.
Proof. exact (MK_COMB (@lem3858805) (@lem3858793)). Qed.
Lemma lem3858808 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3858809 : term501 = term133.
Proof. exact (@lem3858808 term11). Qed.
Lemma lem3858810 : term508 = term133.
Proof. exact (TRANS (@lem3858806) (@lem3858809)). Qed.
Lemma lem3858811 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3858812 : term510 = term261.
Proof. exact (MK_COMB (@lem3858811) (@lem3858810)). Qed.
Lemma lem3858813 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3858814 : term511 = term263.
Proof. exact (MK_COMB (@lem3858812) (@lem3858813)). Qed.
Lemma lem3858816 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858817 : term263 = term133.
Proof. exact (@lem3858816 term11). Qed.
Lemma lem3858818 : term511 = term133.
Proof. exact (TRANS (@lem3858814) (@lem3858817)). Qed.
Lemma lem3858820 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3858821 : term208 = term209.
Proof. exact (@lem3858820 term11 term11). Qed.
Lemma lem3858822 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858823 : term211 = term11.
Proof. exact (EQ_MP (@lem3858822) (@lem940073)). Qed.
Lemma lem3858824 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858825 : term209 = term143.
Proof. exact (MK_COMB (@lem3858824) (@lem3858823)). Qed.
Lemma lem3858826 : term208 = term143.
Proof. exact (TRANS (@lem3858821) (@lem3858825)). Qed.
Lemma lem3858827 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3858828 : term265 = term263.
Proof. exact (MK_COMB (@lem3858827) (@lem3858826)). Qed.
Lemma lem3858830 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858831 : term263 = term133.
Proof. exact (@lem3858830 term11). Qed.
Lemma lem3858832 : term265 = term133.
Proof. exact (TRANS (@lem3858828) (@lem3858831)). Qed.
Lemma lem3858833 : term133 = term265.
Proof. exact (SYM (@lem3858832)). Qed.
Lemma lem3858834 : term511 = term265.
Proof. exact (TRANS (@lem3858818) (@lem3858833)). Qed.
Lemma lem3858835 : term502 = term196.
Proof. exact (@lem3858785 (@lem3858834)). Qed.
Lemma lem3858836 : term501 = term196.
Proof. exact (TRANS (@lem3858751) (@lem3858835)). Qed.
Lemma lem3858838 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3858839 : term196 = term133.
Proof. exact (@lem3858838 term133). Qed.
Lemma lem3858840 : term501 = term133.
Proof. exact (TRANS (@lem3858836) (@lem3858839)). Qed.
Lemma lem3858841 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3858842 : term512 = term261.
Proof. exact (MK_COMB (@lem3858841) (@lem3858840)). Qed.
Lemma lem3858843 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3858844 (_44750 : int) : (term498 _44750) = (term513 _44750).
Proof. exact (MK_COMB (@lem3858842) (@lem3858843 _44750)). Qed.
Lemma lem3858845 (_44750 : int) : (term497 _44750) = (term513 _44750).
Proof. exact (TRANS (@lem3858742 _44750) (@lem3858844 _44750)). Qed.
Lemma lem3858846 (_44750 : int) : (term513 _44750) = term133.
Proof. exact (@lem1982719 (real_of_int _44750)). Qed.
Lemma lem3858847 (_44750 : int) : (term497 _44750) = term133.
Proof. exact (TRANS (@lem3858845 _44750) (@lem3858846 _44750)). Qed.
Lemma lem3858848 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3858849 (_44750 : int) : (term514 _44750) = term175.
Proof. exact (MK_COMB (@lem3858848) (@lem3858847 _44750)). Qed.
Lemma lem3858850 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3858851 (_44750 : int) : (term574 _44750) = term519.
Proof. exact (MK_COMB (@lem3858849 _44750) (@lem3858850)). Qed.
Lemma lem3858852 (_44750 : int) : (term573 _44750) = term519.
Proof. exact (TRANS (@lem3858741 _44750) (@lem3858851 _44750)). Qed.
Lemma lem3858853 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3858854 (_44750 : int) : (term573 _44750) = term199.
Proof. exact (TRANS (@lem3858852 _44750) (@lem3858853)). Qed.
Lemma lem3858855 (_44749 : int) : (term233 _44749) = (term233 _44749).
Proof. exact (eq_refl (term233 _44749)). Qed.
Lemma lem3858856 (_44750 : int) (_44749 : int) : (term588 _44749 _44750) = (term234 _44749).
Proof. exact (MK_COMB (@lem3858855 _44749) (@lem3858854 _44750)). Qed.
Lemma lem3858857 (_44750 : int) (_44749 : int) : (term587 _44749 _44750) = (term234 _44749).
Proof. exact (TRANS (@lem3858740 _44749 _44750) (@lem3858856 _44750 _44749)). Qed.
Lemma lem3858858 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3858859 (_44750 : int) (_44749 : int) : (term605 _44749 _44750) = (term292 _44749).
Proof. exact (MK_COMB (@lem3858858) (@lem3858857 _44750 _44749)). Qed.
Lemma lem3858860 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3858861 (_44750 : int) (_44749 : int) : (term604 _44749 _44750) = (term293 _44749).
Proof. exact (MK_COMB (@lem3858859 _44750 _44749) (@lem3858860)). Qed.
Lemma lem3858862 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term293 _44749.
Proof. exact (EQ_MP (@lem3858861 _44750 _44749) (@lem3858739 _44749 _44750 h1)). Qed.
Lemma lem3858864 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3858865 : term471 = term251.
Proof. exact (@lem3858864 term133 term143). Qed.
Lemma lem3858867 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858868 : term143 = term224.
Proof. exact (@lem3858867 term11). Qed.
Lemma lem3858870 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858871 : term133 = term196.
Proof. exact (@lem3858870 (NUMERAL 0)). Qed.
Lemma lem3858872 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3858873 : term472 = term473.
Proof. exact (MK_COMB (@lem3858872) (@lem3858871)). Qed.
Lemma lem3858874 : term251 = term474.
Proof. exact (MK_COMB (@lem3858873) (@lem3858868)). Qed.
Lemma lem3858875 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3858877 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858878 : term251 = term252.
Proof. exact (@lem3858877 (NUMERAL 0) term11). Qed.
Lemma lem3858879 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858880 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858881 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858880 h1) (fun h1 : term252 = True => @lem3858879)). Qed.
Lemma lem3858882 : term252 = True.
Proof. exact (EQ_MP (@lem3858881) (@lem3858879)). Qed.
Lemma lem3858883 : term251 = True.
Proof. exact (TRANS (@lem3858878) (@lem3858882)). Qed.
Lemma lem3858884 : True = term251.
Proof. exact (SYM (@lem3858883)). Qed.
Lemma lem3858885 : term251.
Proof. exact (EQ_MP (@lem3858884) (@lem0)). Qed.
Lemma lem3858886 : term476.
Proof. exact (@lem3858875 (@lem3858885)). Qed.
Lemma lem3858888 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858889 : term251 = term252.
Proof. exact (@lem3858888 (NUMERAL 0) term11). Qed.
Lemma lem3858890 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858891 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858892 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858891 h1) (fun h1 : term252 = True => @lem3858890)). Qed.
Lemma lem3858893 : term252 = True.
Proof. exact (EQ_MP (@lem3858892) (@lem3858890)). Qed.
Lemma lem3858894 : term251 = True.
Proof. exact (TRANS (@lem3858889) (@lem3858893)). Qed.
Lemma lem3858895 : True = term251.
Proof. exact (SYM (@lem3858894)). Qed.
Lemma lem3858896 : term251.
Proof. exact (EQ_MP (@lem3858895) (@lem0)). Qed.
Lemma lem3858897 : term474 = term477.
Proof. exact (@lem3858886 (@lem3858896)). Qed.
Lemma lem3858899 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3858900 : term208 = term209.
Proof. exact (@lem3858899 term11 term11). Qed.
Lemma lem3858901 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3858902 : term211 = term11.
Proof. exact (EQ_MP (@lem3858901) (@lem940073)). Qed.
Lemma lem3858903 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3858904 : term209 = term143.
Proof. exact (MK_COMB (@lem3858903) (@lem3858902)). Qed.
Lemma lem3858905 : term208 = term143.
Proof. exact (TRANS (@lem3858900) (@lem3858904)). Qed.
Lemma lem3858907 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3858908 : term263 = term133.
Proof. exact (@lem3858907 term11). Qed.
Lemma lem3858909 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3858910 : term478 = term472.
Proof. exact (MK_COMB (@lem3858909) (@lem3858908)). Qed.
Lemma lem3858911 : term477 = term251.
Proof. exact (MK_COMB (@lem3858910) (@lem3858905)). Qed.
Lemma lem3858913 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858914 : term251 = term252.
Proof. exact (@lem3858913 (NUMERAL 0) term11). Qed.
Lemma lem3858915 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858916 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858917 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858916 h1) (fun h1 : term252 = True => @lem3858915)). Qed.
Lemma lem3858918 : term252 = True.
Proof. exact (EQ_MP (@lem3858917) (@lem3858915)). Qed.
Lemma lem3858919 : term251 = True.
Proof. exact (TRANS (@lem3858914) (@lem3858918)). Qed.
Lemma lem3858920 : term477 = True.
Proof. exact (TRANS (@lem3858911) (@lem3858919)). Qed.
Lemma lem3858921 : term474 = True.
Proof. exact (TRANS (@lem3858897) (@lem3858920)). Qed.
Lemma lem3858922 : term251 = True.
Proof. exact (TRANS (@lem3858874) (@lem3858921)). Qed.
Lemma lem3858923 : term471 = True.
Proof. exact (TRANS (@lem3858865) (@lem3858922)). Qed.
Lemma lem3858924 : True = term471.
Proof. exact (SYM (@lem3858923)). Qed.
Lemma lem3858925 : term471.
Proof. exact (EQ_MP (@lem3858924) (@lem0)). Qed.
Lemma lem3858926 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term606 _44749.
Proof. exact (conj (@lem3858925) (@lem3858862 _44749 _44750 h1)). Qed.
Lemma lem3858928 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3858929 (_44749 : int) : term607 _44749.
Proof. exact (@lem3858928 term143 (term234 _44749)). Qed.
Lemma lem3858930 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term608 _44749.
Proof. exact (@lem3858929 _44749 (@lem3858926 _44749 _44750 h1)). Qed.
Lemma lem3858931 (_44749 : int) : (term594 _44749) = (term234 _44749).
Proof. exact (@lem1982733 (term234 _44749)). Qed.
Lemma lem3858932 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3858933 (_44749 : int) : (term609 _44749) = (term292 _44749).
Proof. exact (MK_COMB (@lem3858932) (@lem3858931 _44749)). Qed.
Lemma lem3858934 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3858935 (_44749 : int) : (term608 _44749) = (term293 _44749).
Proof. exact (MK_COMB (@lem3858933 _44749) (@lem3858934)). Qed.
Lemma lem3858936 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term293 _44749.
Proof. exact (EQ_MP (@lem3858935 _44749) (@lem3858930 _44749 _44750 h1)). Qed.
Lemma lem3858938 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3858939 (_44749 : int) : term539 _44749.
Proof. exact (@lem3858938 (real_of_int _44749)). Qed.
Lemma lem3858940 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term540 _44749.
Proof. exact (@lem3858939 _44749 (@lem3858644 _44749 _44750 h1)). Qed.
Lemma lem3858941 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term541 _44749.
Proof. exact (@lem3858940 _44749 _44750 h1 term143). Qed.
Lemma lem3858942 (_44749 : int) : (term541 _44749) = ((term542 _44749) = term133).
Proof. exact (eq_refl (term541 _44749)). Qed.
Lemma lem3858943 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : (term542 _44749) = term133.
Proof. exact (EQ_MP (@lem3858942 _44749) (@lem3858941 _44749 _44750 h1)). Qed.
Lemma lem3858944 (_44749 : int) : (term542 _44749) = (real_of_int _44749).
Proof. exact (@lem1982733 (real_of_int _44749)). Qed.
Lemma lem3858945 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3858946 (_44749 : int) : (term543 _44749) = (term146 _44749).
Proof. exact (MK_COMB (@lem3858945) (@lem3858944 _44749)). Qed.
Lemma lem3858947 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3858948 (_44749 : int) : ((term542 _44749) = term133) = ((real_of_int _44749) = term133).
Proof. exact (MK_COMB (@lem3858946 _44749) (@lem3858947)). Qed.
Lemma lem3858949 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : (real_of_int _44749) = term133.
Proof. exact (EQ_MP (@lem3858948 _44749) (@lem3858943 _44749 _44750 h1)). Qed.
Lemma lem3858950 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term347 _44749.
Proof. exact (conj (@lem3858949 _44749 _44750 h1) (@lem3858936 _44749 _44750 h1)). Qed.
Lemma lem3858952 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3858953 (_44749 : int) : term610 _44749.
Proof. exact (@lem3858952 (real_of_int _44749) (term234 _44749)). Qed.
Lemma lem3858954 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term611 _44749.
Proof. exact (@lem3858953 _44749 (@lem3858950 _44749 _44750 h1)). Qed.
Lemma lem3858955 (_44749 : int) : (term612 _44749) = (term516 _44749).
Proof. exact (@lem1982763 (real_of_int _44749) (term237 _44749) term199). Qed.
Lemma lem3858956 (_44749 : int) : (term517 _44749) = (term498 _44749).
Proof. exact (@lem1982715 term199 (real_of_int _44749)). Qed.
Lemma lem3858958 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3858959 : term143 = term224.
Proof. exact (@lem3858958 term11). Qed.
Lemma lem3858961 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3858962 : term199 = term200.
Proof. exact (@lem3858961 term11). Qed.
Lemma lem3858963 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3858964 : term499 = term500.
Proof. exact (MK_COMB (@lem3858963) (@lem3858962)). Qed.
Lemma lem3858965 : term501 = term502.
Proof. exact (MK_COMB (@lem3858964) (@lem3858959)). Qed.
Lemma lem3858966 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3858968 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858969 : term251 = term252.
Proof. exact (@lem3858968 (NUMERAL 0) term11). Qed.
Lemma lem3858970 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858971 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858972 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858971 h1) (fun h1 : term252 = True => @lem3858970)). Qed.
Lemma lem3858973 : term252 = True.
Proof. exact (EQ_MP (@lem3858972) (@lem3858970)). Qed.
Lemma lem3858974 : term251 = True.
Proof. exact (TRANS (@lem3858969) (@lem3858973)). Qed.
Lemma lem3858975 : True = term251.
Proof. exact (SYM (@lem3858974)). Qed.
Lemma lem3858976 : term251.
Proof. exact (EQ_MP (@lem3858975) (@lem0)). Qed.
Lemma lem3858977 : term504.
Proof. exact (@lem3858966 (@lem3858976)). Qed.
Lemma lem3858979 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858980 : term251 = term252.
Proof. exact (@lem3858979 (NUMERAL 0) term11). Qed.
Lemma lem3858981 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858982 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858983 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858982 h1) (fun h1 : term252 = True => @lem3858981)). Qed.
Lemma lem3858984 : term252 = True.
Proof. exact (EQ_MP (@lem3858983) (@lem3858981)). Qed.
Lemma lem3858985 : term251 = True.
Proof. exact (TRANS (@lem3858980) (@lem3858984)). Qed.
Lemma lem3858986 : True = term251.
Proof. exact (SYM (@lem3858985)). Qed.
Lemma lem3858987 : term251.
Proof. exact (EQ_MP (@lem3858986) (@lem0)). Qed.
Lemma lem3858988 : term505.
Proof. exact (@lem3858977 (@lem3858987)). Qed.
Lemma lem3858990 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3858991 : term251 = term252.
Proof. exact (@lem3858990 (NUMERAL 0) term11). Qed.
Lemma lem3858992 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3858993 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3858994 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3858993 h1) (fun h1 : term252 = True => @lem3858992)). Qed.
Lemma lem3858995 : term252 = True.
Proof. exact (EQ_MP (@lem3858994) (@lem3858992)). Qed.
Lemma lem3858996 : term251 = True.
Proof. exact (TRANS (@lem3858991) (@lem3858995)). Qed.
Lemma lem3858997 : True = term251.
Proof. exact (SYM (@lem3858996)). Qed.
Lemma lem3858998 : term251.
Proof. exact (EQ_MP (@lem3858997) (@lem0)). Qed.
Lemma lem3858999 : term506.
Proof. exact (@lem3858988 (@lem3858998)). Qed.
Lemma lem3859001 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3859002 : term208 = term209.
Proof. exact (@lem3859001 term11 term11). Qed.
Lemma lem3859003 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859004 : term211 = term11.
Proof. exact (EQ_MP (@lem3859003) (@lem940073)). Qed.
Lemma lem3859005 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859006 : term209 = term143.
Proof. exact (MK_COMB (@lem3859005) (@lem3859004)). Qed.
Lemma lem3859007 : term208 = term143.
Proof. exact (TRANS (@lem3859002) (@lem3859006)). Qed.
Lemma lem3859009 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3859010 : term225 = term230.
Proof. exact (@lem3859009 term11 term11). Qed.
Lemma lem3859011 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859012 : term211 = term11.
Proof. exact (EQ_MP (@lem3859011) (@lem940073)). Qed.
Lemma lem3859013 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859014 : term209 = term143.
Proof. exact (MK_COMB (@lem3859013) (@lem3859012)). Qed.
Lemma lem3859015 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3859016 : term230 = term199.
Proof. exact (MK_COMB (@lem3859015) (@lem3859014)). Qed.
Lemma lem3859017 : term225 = term199.
Proof. exact (TRANS (@lem3859010) (@lem3859016)). Qed.
Lemma lem3859018 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3859019 : term507 = term499.
Proof. exact (MK_COMB (@lem3859018) (@lem3859017)). Qed.
Lemma lem3859020 : term508 = term501.
Proof. exact (MK_COMB (@lem3859019) (@lem3859007)). Qed.
Lemma lem3859022 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3859023 : term501 = term133.
Proof. exact (@lem3859022 term11). Qed.
Lemma lem3859024 : term508 = term133.
Proof. exact (TRANS (@lem3859020) (@lem3859023)). Qed.
Lemma lem3859025 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3859026 : term510 = term261.
Proof. exact (MK_COMB (@lem3859025) (@lem3859024)). Qed.
Lemma lem3859027 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3859028 : term511 = term263.
Proof. exact (MK_COMB (@lem3859026) (@lem3859027)). Qed.
Lemma lem3859030 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859031 : term263 = term133.
Proof. exact (@lem3859030 term11). Qed.
Lemma lem3859032 : term511 = term133.
Proof. exact (TRANS (@lem3859028) (@lem3859031)). Qed.
Lemma lem3859034 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3859035 : term208 = term209.
Proof. exact (@lem3859034 term11 term11). Qed.
Lemma lem3859036 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859037 : term211 = term11.
Proof. exact (EQ_MP (@lem3859036) (@lem940073)). Qed.
Lemma lem3859038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859039 : term209 = term143.
Proof. exact (MK_COMB (@lem3859038) (@lem3859037)). Qed.
Lemma lem3859040 : term208 = term143.
Proof. exact (TRANS (@lem3859035) (@lem3859039)). Qed.
Lemma lem3859041 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3859042 : term265 = term263.
Proof. exact (MK_COMB (@lem3859041) (@lem3859040)). Qed.
Lemma lem3859044 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859045 : term263 = term133.
Proof. exact (@lem3859044 term11). Qed.
Lemma lem3859046 : term265 = term133.
Proof. exact (TRANS (@lem3859042) (@lem3859045)). Qed.
Lemma lem3859047 : term133 = term265.
Proof. exact (SYM (@lem3859046)). Qed.
Lemma lem3859048 : term511 = term265.
Proof. exact (TRANS (@lem3859032) (@lem3859047)). Qed.
Lemma lem3859049 : term502 = term196.
Proof. exact (@lem3858999 (@lem3859048)). Qed.
Lemma lem3859050 : term501 = term196.
Proof. exact (TRANS (@lem3858965) (@lem3859049)). Qed.
Lemma lem3859052 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3859053 : term196 = term133.
Proof. exact (@lem3859052 term133). Qed.
Lemma lem3859054 : term501 = term133.
Proof. exact (TRANS (@lem3859050) (@lem3859053)). Qed.
Lemma lem3859055 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3859056 : term512 = term261.
Proof. exact (MK_COMB (@lem3859055) (@lem3859054)). Qed.
Lemma lem3859057 (_44749 : int) : (real_of_int _44749) = (real_of_int _44749).
Proof. exact (eq_refl (real_of_int _44749)). Qed.
Lemma lem3859058 (_44749 : int) : (term498 _44749) = (term513 _44749).
Proof. exact (MK_COMB (@lem3859056) (@lem3859057 _44749)). Qed.
Lemma lem3859059 (_44749 : int) : (term517 _44749) = (term513 _44749).
Proof. exact (TRANS (@lem3858956 _44749) (@lem3859058 _44749)). Qed.
Lemma lem3859060 (_44749 : int) : (term513 _44749) = term133.
Proof. exact (@lem1982719 (real_of_int _44749)). Qed.
Lemma lem3859061 (_44749 : int) : (term517 _44749) = term133.
Proof. exact (TRANS (@lem3859059 _44749) (@lem3859060 _44749)). Qed.
Lemma lem3859062 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3859063 (_44749 : int) : (term518 _44749) = term175.
Proof. exact (MK_COMB (@lem3859062) (@lem3859061 _44749)). Qed.
Lemma lem3859064 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3859065 (_44749 : int) : (term516 _44749) = term519.
Proof. exact (MK_COMB (@lem3859063 _44749) (@lem3859064)). Qed.
Lemma lem3859066 (_44749 : int) : (term612 _44749) = term519.
Proof. exact (TRANS (@lem3858955 _44749) (@lem3859065 _44749)). Qed.
Lemma lem3859067 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3859068 (_44749 : int) : (term612 _44749) = term199.
Proof. exact (TRANS (@lem3859066 _44749) (@lem3859067)). Qed.
Lemma lem3859069 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3859070 (_44749 : int) : (term613 _44749) = term521.
Proof. exact (MK_COMB (@lem3859069) (@lem3859068 _44749)). Qed.
Lemma lem3859071 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3859072 (_44749 : int) : (term611 _44749) = term522.
Proof. exact (MK_COMB (@lem3859070 _44749) (@lem3859071)). Qed.
Lemma lem3859073 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : term522.
Proof. exact (EQ_MP (@lem3859072 _44749) (@lem3858954 _44749 _44750 h1)). Qed.
Lemma lem3859075 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3859076 : term522 = term523.
Proof. exact (@lem3859075 term133 term199). Qed.
Lemma lem3859078 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3859079 : term199 = term200.
Proof. exact (@lem3859078 term11). Qed.
Lemma lem3859081 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859082 : term133 = term196.
Proof. exact (@lem3859081 (NUMERAL 0)). Qed.
Lemma lem3859083 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3859084 : term135 = term524.
Proof. exact (MK_COMB (@lem3859083) (@lem3859082)). Qed.
Lemma lem3859085 : term523 = term525.
Proof. exact (MK_COMB (@lem3859084) (@lem3859079)). Qed.
Lemma lem3859086 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3859088 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859089 : term251 = term252.
Proof. exact (@lem3859088 (NUMERAL 0) term11). Qed.
Lemma lem3859090 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859091 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859092 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859091 h1) (fun h1 : term252 = True => @lem3859090)). Qed.
Lemma lem3859093 : term252 = True.
Proof. exact (EQ_MP (@lem3859092) (@lem3859090)). Qed.
Lemma lem3859094 : term251 = True.
Proof. exact (TRANS (@lem3859089) (@lem3859093)). Qed.
Lemma lem3859095 : True = term251.
Proof. exact (SYM (@lem3859094)). Qed.
Lemma lem3859096 : term251.
Proof. exact (EQ_MP (@lem3859095) (@lem0)). Qed.
Lemma lem3859097 : term527.
Proof. exact (@lem3859086 (@lem3859096)). Qed.
Lemma lem3859099 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859100 : term251 = term252.
Proof. exact (@lem3859099 (NUMERAL 0) term11). Qed.
Lemma lem3859101 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859102 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859103 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859102 h1) (fun h1 : term252 = True => @lem3859101)). Qed.
Lemma lem3859104 : term252 = True.
Proof. exact (EQ_MP (@lem3859103) (@lem3859101)). Qed.
Lemma lem3859105 : term251 = True.
Proof. exact (TRANS (@lem3859100) (@lem3859104)). Qed.
Lemma lem3859106 : True = term251.
Proof. exact (SYM (@lem3859105)). Qed.
Lemma lem3859107 : term251.
Proof. exact (EQ_MP (@lem3859106) (@lem0)). Qed.
Lemma lem3859108 : term525 = term528.
Proof. exact (@lem3859097 (@lem3859107)). Qed.
Lemma lem3859110 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3859111 : term225 = term230.
Proof. exact (@lem3859110 term11 term11). Qed.
Lemma lem3859112 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859113 : term211 = term11.
Proof. exact (EQ_MP (@lem3859112) (@lem940073)). Qed.
Lemma lem3859114 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859115 : term209 = term143.
Proof. exact (MK_COMB (@lem3859114) (@lem3859113)). Qed.
Lemma lem3859116 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3859117 : term230 = term199.
Proof. exact (MK_COMB (@lem3859116) (@lem3859115)). Qed.
Lemma lem3859118 : term225 = term199.
Proof. exact (TRANS (@lem3859111) (@lem3859117)). Qed.
Lemma lem3859120 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859121 : term263 = term133.
Proof. exact (@lem3859120 term11). Qed.
Lemma lem3859122 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3859123 : term529 = term135.
Proof. exact (MK_COMB (@lem3859122) (@lem3859121)). Qed.
Lemma lem3859124 : term528 = term523.
Proof. exact (MK_COMB (@lem3859123) (@lem3859118)). Qed.
Lemma lem3859126 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3859127 : term523 = term532.
Proof. exact (@lem3859126 (NUMERAL 0) term11). Qed.
Lemma lem3859128 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859129 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3859130 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859129 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3859128)). Qed.
Lemma lem3859131 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3859130) (@lem3859128)). Qed.
Lemma lem3859132 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3859133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3859134 : term533 = (and True).
Proof. exact (MK_COMB (@lem3859133) (@lem3859132)). Qed.
Lemma lem3859135 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3859134) (@lem3859131)). Qed.
Lemma lem3859137 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3859138 : term532 = False.
Proof. exact (TRANS (@lem3859135) (@lem3859137)). Qed.
Lemma lem3859139 : term523 = False.
Proof. exact (TRANS (@lem3859127) (@lem3859138)). Qed.
Lemma lem3859140 : term528 = False.
Proof. exact (TRANS (@lem3859124) (@lem3859139)). Qed.
Lemma lem3859141 : term525 = False.
Proof. exact (TRANS (@lem3859108) (@lem3859140)). Qed.
Lemma lem3859142 : term523 = False.
Proof. exact (TRANS (@lem3859085) (@lem3859141)). Qed.
Lemma lem3859143 : term522 = False.
Proof. exact (TRANS (@lem3859076) (@lem3859142)). Qed.
Lemma lem3859144 (_44749 : int) (_44750 : int) (h1 : term601 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3859143) (@lem3859073 _44749 _44750 h1)). Qed.
Lemma lem3859145 (_44749 : int) (_44750 : int) (h1 : term457 _44749 _44750) : False.
Proof. exact (or_elim (@lem3858130 _44749 _44750 h1) (fun h0 : term576 _44749 _44750 => @lem3858636 _44749 _44750 h0) (fun h0 : term601 _44749 _44750 => @lem3859144 _44749 _44750 h0)). Qed.
Lemma lem3859146 (_44749 : int) (_44750 : int) (h1 : term466 _44749 _44750) : False.
Proof. exact (or_elim (@lem3856947 _44749 _44750 h1) (fun h0 : term461 _44749 _44750 => @lem3858129 _44749 _44750 h0) (fun h0 : term457 _44749 _44750 => @lem3859145 _44749 _44750 h0)). Qed.
Lemma lem3859147 (_44749 : int) (_44750 : int) (h1 : term453 _44749 _44750) : term453 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3859148 (_44749 : int) (_44750 : int) (h1 : term450 _44749 _44750) : term450 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3859149 (_44749 : int) (_44750 : int) (h1 : term445 _44749 _44750) : term445 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3859150 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term614 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3859151 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term446 _44749 _44750.
Proof. exact (proj2 (@lem3859150 _44749 _44750 h1)). Qed.
Lemma lem3859153 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term397 _44749 _44750.
Proof. exact (proj2 (@lem3859151 _44749 _44750 h1)). Qed.
Lemma lem3859155 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term346 _44749 _44750.
Proof. exact (proj2 (@lem3859153 _44749 _44750 h1)). Qed.
Lemma lem3859156 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : (term236 _44749 _44750) = term133.
Proof. exact (proj1 (@lem3859153 _44749 _44750 h1)). Qed.
Lemma lem3859158 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term280 _44749 _44750.
Proof. exact (proj1 (@lem3859155 _44749 _44750 h1)). Qed.
Lemma lem3859160 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3859161 : term471 = term251.
Proof. exact (@lem3859160 term133 term143). Qed.
Lemma lem3859163 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859164 : term143 = term224.
Proof. exact (@lem3859163 term11). Qed.
Lemma lem3859166 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859167 : term133 = term196.
Proof. exact (@lem3859166 (NUMERAL 0)). Qed.
Lemma lem3859168 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3859169 : term472 = term473.
Proof. exact (MK_COMB (@lem3859168) (@lem3859167)). Qed.
Lemma lem3859170 : term251 = term474.
Proof. exact (MK_COMB (@lem3859169) (@lem3859164)). Qed.
Lemma lem3859171 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3859173 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859174 : term251 = term252.
Proof. exact (@lem3859173 (NUMERAL 0) term11). Qed.
Lemma lem3859175 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859176 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859177 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859176 h1) (fun h1 : term252 = True => @lem3859175)). Qed.
Lemma lem3859178 : term252 = True.
Proof. exact (EQ_MP (@lem3859177) (@lem3859175)). Qed.
Lemma lem3859179 : term251 = True.
Proof. exact (TRANS (@lem3859174) (@lem3859178)). Qed.
Lemma lem3859180 : True = term251.
Proof. exact (SYM (@lem3859179)). Qed.
Lemma lem3859181 : term251.
Proof. exact (EQ_MP (@lem3859180) (@lem0)). Qed.
Lemma lem3859182 : term476.
Proof. exact (@lem3859171 (@lem3859181)). Qed.
Lemma lem3859184 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859185 : term251 = term252.
Proof. exact (@lem3859184 (NUMERAL 0) term11). Qed.
Lemma lem3859186 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859187 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859188 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859187 h1) (fun h1 : term252 = True => @lem3859186)). Qed.
Lemma lem3859189 : term252 = True.
Proof. exact (EQ_MP (@lem3859188) (@lem3859186)). Qed.
Lemma lem3859190 : term251 = True.
Proof. exact (TRANS (@lem3859185) (@lem3859189)). Qed.
Lemma lem3859191 : True = term251.
Proof. exact (SYM (@lem3859190)). Qed.
Lemma lem3859192 : term251.
Proof. exact (EQ_MP (@lem3859191) (@lem0)). Qed.
Lemma lem3859193 : term474 = term477.
Proof. exact (@lem3859182 (@lem3859192)). Qed.
Lemma lem3859195 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3859196 : term208 = term209.
Proof. exact (@lem3859195 term11 term11). Qed.
Lemma lem3859197 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859198 : term211 = term11.
Proof. exact (EQ_MP (@lem3859197) (@lem940073)). Qed.
Lemma lem3859199 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859200 : term209 = term143.
Proof. exact (MK_COMB (@lem3859199) (@lem3859198)). Qed.
Lemma lem3859201 : term208 = term143.
Proof. exact (TRANS (@lem3859196) (@lem3859200)). Qed.
Lemma lem3859203 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859204 : term263 = term133.
Proof. exact (@lem3859203 term11). Qed.
Lemma lem3859205 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3859206 : term478 = term472.
Proof. exact (MK_COMB (@lem3859205) (@lem3859204)). Qed.
Lemma lem3859207 : term477 = term251.
Proof. exact (MK_COMB (@lem3859206) (@lem3859201)). Qed.
Lemma lem3859209 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859210 : term251 = term252.
Proof. exact (@lem3859209 (NUMERAL 0) term11). Qed.
Lemma lem3859211 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859212 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859213 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859212 h1) (fun h1 : term252 = True => @lem3859211)). Qed.
Lemma lem3859214 : term252 = True.
Proof. exact (EQ_MP (@lem3859213) (@lem3859211)). Qed.
Lemma lem3859215 : term251 = True.
Proof. exact (TRANS (@lem3859210) (@lem3859214)). Qed.
Lemma lem3859216 : term477 = True.
Proof. exact (TRANS (@lem3859207) (@lem3859215)). Qed.
Lemma lem3859217 : term474 = True.
Proof. exact (TRANS (@lem3859193) (@lem3859216)). Qed.
Lemma lem3859218 : term251 = True.
Proof. exact (TRANS (@lem3859170) (@lem3859217)). Qed.
Lemma lem3859219 : term471 = True.
Proof. exact (TRANS (@lem3859161) (@lem3859218)). Qed.
Lemma lem3859220 : True = term471.
Proof. exact (SYM (@lem3859219)). Qed.
Lemma lem3859221 : term471.
Proof. exact (EQ_MP (@lem3859220) (@lem0)). Qed.
Lemma lem3859222 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term479 _44749 _44750.
Proof. exact (conj (@lem3859221) (@lem3859158 _44749 _44750 h1)). Qed.
Lemma lem3859224 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3859225 (_44749 : int) (_44750 : int) : term481 _44749 _44750.
Proof. exact (@lem3859224 term143 (term277 _44749 _44750)). Qed.
Lemma lem3859226 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term482 _44749 _44750.
Proof. exact (@lem3859225 _44749 _44750 (@lem3859222 _44749 _44750 h1)). Qed.
Lemma lem3859227 (_44749 : int) (_44750 : int) : (term483 _44749 _44750) = (term277 _44749 _44750).
Proof. exact (@lem1982733 (term277 _44749 _44750)). Qed.
Lemma lem3859228 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3859229 (_44749 : int) (_44750 : int) : (term484 _44749 _44750) = (term279 _44749 _44750).
Proof. exact (MK_COMB (@lem3859228) (@lem3859227 _44749 _44750)). Qed.
Lemma lem3859230 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3859231 (_44749 : int) (_44750 : int) : (term482 _44749 _44750) = (term280 _44749 _44750).
Proof. exact (MK_COMB (@lem3859229 _44749 _44750) (@lem3859230)). Qed.
Lemma lem3859232 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term280 _44749 _44750.
Proof. exact (EQ_MP (@lem3859231 _44749 _44750) (@lem3859226 _44749 _44750 h1)). Qed.
Lemma lem3859234 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3859235 (_44749 : int) (_44750 : int) : term486 _44749 _44750.
Proof. exact (@lem3859234 (term236 _44749 _44750)). Qed.
Lemma lem3859236 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term487 _44749 _44750.
Proof. exact (@lem3859235 _44749 _44750 (@lem3859156 _44749 _44750 h1)). Qed.
Lemma lem3859237 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term488 _44749 _44750.
Proof. exact (@lem3859236 _44749 _44750 h1 term143). Qed.
Lemma lem3859238 (_44749 : int) (_44750 : int) : (term488 _44749 _44750) = ((term489 _44749 _44750) = term133).
Proof. exact (eq_refl (term488 _44749 _44750)). Qed.
Lemma lem3859239 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : (term489 _44749 _44750) = term133.
Proof. exact (EQ_MP (@lem3859238 _44749 _44750) (@lem3859237 _44749 _44750 h1)). Qed.
Lemma lem3859240 (_44749 : int) (_44750 : int) : (term489 _44749 _44750) = (term236 _44749 _44750).
Proof. exact (@lem1982733 (term236 _44749 _44750)). Qed.
Lemma lem3859241 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3859242 (_44749 : int) (_44750 : int) : (term490 _44749 _44750) = (term239 _44749 _44750).
Proof. exact (MK_COMB (@lem3859241) (@lem3859240 _44749 _44750)). Qed.
Lemma lem3859243 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3859244 (_44749 : int) (_44750 : int) : ((term489 _44749 _44750) = term133) = ((term236 _44749 _44750) = term133).
Proof. exact (MK_COMB (@lem3859242 _44749 _44750) (@lem3859243)). Qed.
Lemma lem3859245 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : (term236 _44749 _44750) = term133.
Proof. exact (EQ_MP (@lem3859244 _44749 _44750) (@lem3859239 _44749 _44750 h1)). Qed.
Lemma lem3859246 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term491 _44749 _44750.
Proof. exact (conj (@lem3859245 _44749 _44750 h1) (@lem3859232 _44749 _44750 h1)). Qed.
Lemma lem3859248 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3859249 (_44749 : int) (_44750 : int) : term493 _44749 _44750.
Proof. exact (@lem3859248 (term236 _44749 _44750) (term277 _44749 _44750)). Qed.
Lemma lem3859250 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term494 _44749 _44750.
Proof. exact (@lem3859249 _44749 _44750 (@lem3859246 _44749 _44750 h1)). Qed.
Lemma lem3859251 (_44749 : int) (_44750 : int) : (term495 _44749 _44750) = (term496 _44749 _44750).
Proof. exact (@lem1982753 (term237 _44749) (real_of_int _44749) (term299 _44750) (term237 _44750)). Qed.
Lemma lem3859252 (_44749 : int) : (term497 _44749) = (term498 _44749).
Proof. exact (@lem1982713 term199 (real_of_int _44749)). Qed.
Lemma lem3859254 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859255 : term143 = term224.
Proof. exact (@lem3859254 term11). Qed.
Lemma lem3859257 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3859258 : term199 = term200.
Proof. exact (@lem3859257 term11). Qed.
Lemma lem3859259 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3859260 : term499 = term500.
Proof. exact (MK_COMB (@lem3859259) (@lem3859258)). Qed.
Lemma lem3859261 : term501 = term502.
Proof. exact (MK_COMB (@lem3859260) (@lem3859255)). Qed.
Lemma lem3859262 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3859264 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859265 : term251 = term252.
Proof. exact (@lem3859264 (NUMERAL 0) term11). Qed.
Lemma lem3859266 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859267 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859268 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859267 h1) (fun h1 : term252 = True => @lem3859266)). Qed.
Lemma lem3859269 : term252 = True.
Proof. exact (EQ_MP (@lem3859268) (@lem3859266)). Qed.
Lemma lem3859270 : term251 = True.
Proof. exact (TRANS (@lem3859265) (@lem3859269)). Qed.
Lemma lem3859271 : True = term251.
Proof. exact (SYM (@lem3859270)). Qed.
Lemma lem3859272 : term251.
Proof. exact (EQ_MP (@lem3859271) (@lem0)). Qed.
Lemma lem3859273 : term504.
Proof. exact (@lem3859262 (@lem3859272)). Qed.
Lemma lem3859275 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859276 : term251 = term252.
Proof. exact (@lem3859275 (NUMERAL 0) term11). Qed.
Lemma lem3859277 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859278 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859279 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859278 h1) (fun h1 : term252 = True => @lem3859277)). Qed.
Lemma lem3859280 : term252 = True.
Proof. exact (EQ_MP (@lem3859279) (@lem3859277)). Qed.
Lemma lem3859281 : term251 = True.
Proof. exact (TRANS (@lem3859276) (@lem3859280)). Qed.
Lemma lem3859282 : True = term251.
Proof. exact (SYM (@lem3859281)). Qed.
Lemma lem3859283 : term251.
Proof. exact (EQ_MP (@lem3859282) (@lem0)). Qed.
Lemma lem3859284 : term505.
Proof. exact (@lem3859273 (@lem3859283)). Qed.
Lemma lem3859286 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859287 : term251 = term252.
Proof. exact (@lem3859286 (NUMERAL 0) term11). Qed.
Lemma lem3859288 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859289 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859290 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859289 h1) (fun h1 : term252 = True => @lem3859288)). Qed.
Lemma lem3859291 : term252 = True.
Proof. exact (EQ_MP (@lem3859290) (@lem3859288)). Qed.
Lemma lem3859292 : term251 = True.
Proof. exact (TRANS (@lem3859287) (@lem3859291)). Qed.
Lemma lem3859293 : True = term251.
Proof. exact (SYM (@lem3859292)). Qed.
Lemma lem3859294 : term251.
Proof. exact (EQ_MP (@lem3859293) (@lem0)). Qed.
Lemma lem3859295 : term506.
Proof. exact (@lem3859284 (@lem3859294)). Qed.
Lemma lem3859297 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3859298 : term208 = term209.
Proof. exact (@lem3859297 term11 term11). Qed.
Lemma lem3859299 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859300 : term211 = term11.
Proof. exact (EQ_MP (@lem3859299) (@lem940073)). Qed.
Lemma lem3859301 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859302 : term209 = term143.
Proof. exact (MK_COMB (@lem3859301) (@lem3859300)). Qed.
Lemma lem3859303 : term208 = term143.
Proof. exact (TRANS (@lem3859298) (@lem3859302)). Qed.
Lemma lem3859305 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3859306 : term225 = term230.
Proof. exact (@lem3859305 term11 term11). Qed.
Lemma lem3859307 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859308 : term211 = term11.
Proof. exact (EQ_MP (@lem3859307) (@lem940073)). Qed.
Lemma lem3859309 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859310 : term209 = term143.
Proof. exact (MK_COMB (@lem3859309) (@lem3859308)). Qed.
Lemma lem3859311 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3859312 : term230 = term199.
Proof. exact (MK_COMB (@lem3859311) (@lem3859310)). Qed.
Lemma lem3859313 : term225 = term199.
Proof. exact (TRANS (@lem3859306) (@lem3859312)). Qed.
Lemma lem3859314 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3859315 : term507 = term499.
Proof. exact (MK_COMB (@lem3859314) (@lem3859313)). Qed.
Lemma lem3859316 : term508 = term501.
Proof. exact (MK_COMB (@lem3859315) (@lem3859303)). Qed.
Lemma lem3859318 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3859319 : term501 = term133.
Proof. exact (@lem3859318 term11). Qed.
Lemma lem3859320 : term508 = term133.
Proof. exact (TRANS (@lem3859316) (@lem3859319)). Qed.
Lemma lem3859321 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3859322 : term510 = term261.
Proof. exact (MK_COMB (@lem3859321) (@lem3859320)). Qed.
Lemma lem3859323 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3859324 : term511 = term263.
Proof. exact (MK_COMB (@lem3859322) (@lem3859323)). Qed.
Lemma lem3859326 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859327 : term263 = term133.
Proof. exact (@lem3859326 term11). Qed.
Lemma lem3859328 : term511 = term133.
Proof. exact (TRANS (@lem3859324) (@lem3859327)). Qed.
Lemma lem3859330 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3859331 : term208 = term209.
Proof. exact (@lem3859330 term11 term11). Qed.
Lemma lem3859332 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859333 : term211 = term11.
Proof. exact (EQ_MP (@lem3859332) (@lem940073)). Qed.
Lemma lem3859334 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859335 : term209 = term143.
Proof. exact (MK_COMB (@lem3859334) (@lem3859333)). Qed.
Lemma lem3859336 : term208 = term143.
Proof. exact (TRANS (@lem3859331) (@lem3859335)). Qed.
Lemma lem3859337 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3859338 : term265 = term263.
Proof. exact (MK_COMB (@lem3859337) (@lem3859336)). Qed.
Lemma lem3859340 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859341 : term263 = term133.
Proof. exact (@lem3859340 term11). Qed.
Lemma lem3859342 : term265 = term133.
Proof. exact (TRANS (@lem3859338) (@lem3859341)). Qed.
Lemma lem3859343 : term133 = term265.
Proof. exact (SYM (@lem3859342)). Qed.
Lemma lem3859344 : term511 = term265.
Proof. exact (TRANS (@lem3859328) (@lem3859343)). Qed.
Lemma lem3859345 : term502 = term196.
Proof. exact (@lem3859295 (@lem3859344)). Qed.
Lemma lem3859346 : term501 = term196.
Proof. exact (TRANS (@lem3859261) (@lem3859345)). Qed.
Lemma lem3859348 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3859349 : term196 = term133.
Proof. exact (@lem3859348 term133). Qed.
Lemma lem3859350 : term501 = term133.
Proof. exact (TRANS (@lem3859346) (@lem3859349)). Qed.
Lemma lem3859351 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3859352 : term512 = term261.
Proof. exact (MK_COMB (@lem3859351) (@lem3859350)). Qed.
Lemma lem3859353 (_44749 : int) : (real_of_int _44749) = (real_of_int _44749).
Proof. exact (eq_refl (real_of_int _44749)). Qed.
Lemma lem3859354 (_44749 : int) : (term498 _44749) = (term513 _44749).
Proof. exact (MK_COMB (@lem3859352) (@lem3859353 _44749)). Qed.
Lemma lem3859355 (_44749 : int) : (term497 _44749) = (term513 _44749).
Proof. exact (TRANS (@lem3859252 _44749) (@lem3859354 _44749)). Qed.
Lemma lem3859356 (_44749 : int) : (term513 _44749) = term133.
Proof. exact (@lem1982719 (real_of_int _44749)). Qed.
Lemma lem3859357 (_44749 : int) : (term497 _44749) = term133.
Proof. exact (TRANS (@lem3859355 _44749) (@lem3859356 _44749)). Qed.
Lemma lem3859358 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3859359 (_44749 : int) : (term514 _44749) = term175.
Proof. exact (MK_COMB (@lem3859358) (@lem3859357 _44749)). Qed.
Lemma lem3859360 (_44750 : int) : (term515 _44750) = (term516 _44750).
Proof. exact (@lem1982759 (real_of_int _44750) (term237 _44750) term199). Qed.
Lemma lem3859361 (_44750 : int) : (term517 _44750) = (term498 _44750).
Proof. exact (@lem1982715 term199 (real_of_int _44750)). Qed.
Lemma lem3859363 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859364 : term143 = term224.
Proof. exact (@lem3859363 term11). Qed.
Lemma lem3859366 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3859367 : term199 = term200.
Proof. exact (@lem3859366 term11). Qed.
Lemma lem3859368 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3859369 : term499 = term500.
Proof. exact (MK_COMB (@lem3859368) (@lem3859367)). Qed.
Lemma lem3859370 : term501 = term502.
Proof. exact (MK_COMB (@lem3859369) (@lem3859364)). Qed.
Lemma lem3859371 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3859373 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859374 : term251 = term252.
Proof. exact (@lem3859373 (NUMERAL 0) term11). Qed.
Lemma lem3859375 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859376 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859377 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859376 h1) (fun h1 : term252 = True => @lem3859375)). Qed.
Lemma lem3859378 : term252 = True.
Proof. exact (EQ_MP (@lem3859377) (@lem3859375)). Qed.
Lemma lem3859379 : term251 = True.
Proof. exact (TRANS (@lem3859374) (@lem3859378)). Qed.
Lemma lem3859380 : True = term251.
Proof. exact (SYM (@lem3859379)). Qed.
Lemma lem3859381 : term251.
Proof. exact (EQ_MP (@lem3859380) (@lem0)). Qed.
Lemma lem3859382 : term504.
Proof. exact (@lem3859371 (@lem3859381)). Qed.
Lemma lem3859384 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859385 : term251 = term252.
Proof. exact (@lem3859384 (NUMERAL 0) term11). Qed.
Lemma lem3859386 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859387 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859388 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859387 h1) (fun h1 : term252 = True => @lem3859386)). Qed.
Lemma lem3859389 : term252 = True.
Proof. exact (EQ_MP (@lem3859388) (@lem3859386)). Qed.
Lemma lem3859390 : term251 = True.
Proof. exact (TRANS (@lem3859385) (@lem3859389)). Qed.
Lemma lem3859391 : True = term251.
Proof. exact (SYM (@lem3859390)). Qed.
Lemma lem3859392 : term251.
Proof. exact (EQ_MP (@lem3859391) (@lem0)). Qed.
Lemma lem3859393 : term505.
Proof. exact (@lem3859382 (@lem3859392)). Qed.
Lemma lem3859395 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859396 : term251 = term252.
Proof. exact (@lem3859395 (NUMERAL 0) term11). Qed.
Lemma lem3859397 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859398 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859399 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859398 h1) (fun h1 : term252 = True => @lem3859397)). Qed.
Lemma lem3859400 : term252 = True.
Proof. exact (EQ_MP (@lem3859399) (@lem3859397)). Qed.
Lemma lem3859401 : term251 = True.
Proof. exact (TRANS (@lem3859396) (@lem3859400)). Qed.
Lemma lem3859402 : True = term251.
Proof. exact (SYM (@lem3859401)). Qed.
Lemma lem3859403 : term251.
Proof. exact (EQ_MP (@lem3859402) (@lem0)). Qed.
Lemma lem3859404 : term506.
Proof. exact (@lem3859393 (@lem3859403)). Qed.
Lemma lem3859406 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3859407 : term208 = term209.
Proof. exact (@lem3859406 term11 term11). Qed.
Lemma lem3859408 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859409 : term211 = term11.
Proof. exact (EQ_MP (@lem3859408) (@lem940073)). Qed.
Lemma lem3859410 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859411 : term209 = term143.
Proof. exact (MK_COMB (@lem3859410) (@lem3859409)). Qed.
Lemma lem3859412 : term208 = term143.
Proof. exact (TRANS (@lem3859407) (@lem3859411)). Qed.
Lemma lem3859414 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3859415 : term225 = term230.
Proof. exact (@lem3859414 term11 term11). Qed.
Lemma lem3859416 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859417 : term211 = term11.
Proof. exact (EQ_MP (@lem3859416) (@lem940073)). Qed.
Lemma lem3859418 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859419 : term209 = term143.
Proof. exact (MK_COMB (@lem3859418) (@lem3859417)). Qed.
Lemma lem3859420 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3859421 : term230 = term199.
Proof. exact (MK_COMB (@lem3859420) (@lem3859419)). Qed.
Lemma lem3859422 : term225 = term199.
Proof. exact (TRANS (@lem3859415) (@lem3859421)). Qed.
Lemma lem3859423 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3859424 : term507 = term499.
Proof. exact (MK_COMB (@lem3859423) (@lem3859422)). Qed.
Lemma lem3859425 : term508 = term501.
Proof. exact (MK_COMB (@lem3859424) (@lem3859412)). Qed.
Lemma lem3859427 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3859428 : term501 = term133.
Proof. exact (@lem3859427 term11). Qed.
Lemma lem3859429 : term508 = term133.
Proof. exact (TRANS (@lem3859425) (@lem3859428)). Qed.
Lemma lem3859430 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3859431 : term510 = term261.
Proof. exact (MK_COMB (@lem3859430) (@lem3859429)). Qed.
Lemma lem3859432 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3859433 : term511 = term263.
Proof. exact (MK_COMB (@lem3859431) (@lem3859432)). Qed.
Lemma lem3859435 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859436 : term263 = term133.
Proof. exact (@lem3859435 term11). Qed.
Lemma lem3859437 : term511 = term133.
Proof. exact (TRANS (@lem3859433) (@lem3859436)). Qed.
Lemma lem3859439 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3859440 : term208 = term209.
Proof. exact (@lem3859439 term11 term11). Qed.
Lemma lem3859441 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859442 : term211 = term11.
Proof. exact (EQ_MP (@lem3859441) (@lem940073)). Qed.
Lemma lem3859443 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859444 : term209 = term143.
Proof. exact (MK_COMB (@lem3859443) (@lem3859442)). Qed.
Lemma lem3859445 : term208 = term143.
Proof. exact (TRANS (@lem3859440) (@lem3859444)). Qed.
Lemma lem3859446 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3859447 : term265 = term263.
Proof. exact (MK_COMB (@lem3859446) (@lem3859445)). Qed.
Lemma lem3859449 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859450 : term263 = term133.
Proof. exact (@lem3859449 term11). Qed.
Lemma lem3859451 : term265 = term133.
Proof. exact (TRANS (@lem3859447) (@lem3859450)). Qed.
Lemma lem3859452 : term133 = term265.
Proof. exact (SYM (@lem3859451)). Qed.
Lemma lem3859453 : term511 = term265.
Proof. exact (TRANS (@lem3859437) (@lem3859452)). Qed.
Lemma lem3859454 : term502 = term196.
Proof. exact (@lem3859404 (@lem3859453)). Qed.
Lemma lem3859455 : term501 = term196.
Proof. exact (TRANS (@lem3859370) (@lem3859454)). Qed.
Lemma lem3859457 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3859458 : term196 = term133.
Proof. exact (@lem3859457 term133). Qed.
Lemma lem3859459 : term501 = term133.
Proof. exact (TRANS (@lem3859455) (@lem3859458)). Qed.
Lemma lem3859460 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3859461 : term512 = term261.
Proof. exact (MK_COMB (@lem3859460) (@lem3859459)). Qed.
Lemma lem3859462 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3859463 (_44750 : int) : (term498 _44750) = (term513 _44750).
Proof. exact (MK_COMB (@lem3859461) (@lem3859462 _44750)). Qed.
Lemma lem3859464 (_44750 : int) : (term517 _44750) = (term513 _44750).
Proof. exact (TRANS (@lem3859361 _44750) (@lem3859463 _44750)). Qed.
Lemma lem3859465 (_44750 : int) : (term513 _44750) = term133.
Proof. exact (@lem1982719 (real_of_int _44750)). Qed.
Lemma lem3859466 (_44750 : int) : (term517 _44750) = term133.
Proof. exact (TRANS (@lem3859464 _44750) (@lem3859465 _44750)). Qed.
Lemma lem3859467 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3859468 (_44750 : int) : (term518 _44750) = term175.
Proof. exact (MK_COMB (@lem3859467) (@lem3859466 _44750)). Qed.
Lemma lem3859469 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3859470 (_44750 : int) : (term516 _44750) = term519.
Proof. exact (MK_COMB (@lem3859468 _44750) (@lem3859469)). Qed.
Lemma lem3859471 (_44750 : int) : (term515 _44750) = term519.
Proof. exact (TRANS (@lem3859360 _44750) (@lem3859470 _44750)). Qed.
Lemma lem3859472 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3859473 (_44750 : int) : (term515 _44750) = term199.
Proof. exact (TRANS (@lem3859471 _44750) (@lem3859472)). Qed.
Lemma lem3859474 (_44749 : int) (_44750 : int) : (term496 _44749 _44750) = term519.
Proof. exact (MK_COMB (@lem3859359 _44749) (@lem3859473 _44750)). Qed.
Lemma lem3859475 (_44749 : int) (_44750 : int) : (term495 _44749 _44750) = term519.
Proof. exact (TRANS (@lem3859251 _44749 _44750) (@lem3859474 _44749 _44750)). Qed.
Lemma lem3859476 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3859477 (_44749 : int) (_44750 : int) : (term495 _44749 _44750) = term199.
Proof. exact (TRANS (@lem3859475 _44749 _44750) (@lem3859476)). Qed.
Lemma lem3859478 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3859479 (_44749 : int) (_44750 : int) : (term520 _44749 _44750) = term521.
Proof. exact (MK_COMB (@lem3859478) (@lem3859477 _44749 _44750)). Qed.
Lemma lem3859480 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3859481 (_44749 : int) (_44750 : int) : (term494 _44749 _44750) = term522.
Proof. exact (MK_COMB (@lem3859479 _44749 _44750) (@lem3859480)). Qed.
Lemma lem3859482 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : term522.
Proof. exact (EQ_MP (@lem3859481 _44749 _44750) (@lem3859250 _44749 _44750 h1)). Qed.
Lemma lem3859484 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3859485 : term522 = term523.
Proof. exact (@lem3859484 term133 term199). Qed.
Lemma lem3859487 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3859488 : term199 = term200.
Proof. exact (@lem3859487 term11). Qed.
Lemma lem3859490 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859491 : term133 = term196.
Proof. exact (@lem3859490 (NUMERAL 0)). Qed.
Lemma lem3859492 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3859493 : term135 = term524.
Proof. exact (MK_COMB (@lem3859492) (@lem3859491)). Qed.
Lemma lem3859494 : term523 = term525.
Proof. exact (MK_COMB (@lem3859493) (@lem3859488)). Qed.
Lemma lem3859495 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3859497 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859498 : term251 = term252.
Proof. exact (@lem3859497 (NUMERAL 0) term11). Qed.
Lemma lem3859499 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859500 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859501 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859500 h1) (fun h1 : term252 = True => @lem3859499)). Qed.
Lemma lem3859502 : term252 = True.
Proof. exact (EQ_MP (@lem3859501) (@lem3859499)). Qed.
Lemma lem3859503 : term251 = True.
Proof. exact (TRANS (@lem3859498) (@lem3859502)). Qed.
Lemma lem3859504 : True = term251.
Proof. exact (SYM (@lem3859503)). Qed.
Lemma lem3859505 : term251.
Proof. exact (EQ_MP (@lem3859504) (@lem0)). Qed.
Lemma lem3859506 : term527.
Proof. exact (@lem3859495 (@lem3859505)). Qed.
Lemma lem3859508 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859509 : term251 = term252.
Proof. exact (@lem3859508 (NUMERAL 0) term11). Qed.
Lemma lem3859510 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859511 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859512 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859511 h1) (fun h1 : term252 = True => @lem3859510)). Qed.
Lemma lem3859513 : term252 = True.
Proof. exact (EQ_MP (@lem3859512) (@lem3859510)). Qed.
Lemma lem3859514 : term251 = True.
Proof. exact (TRANS (@lem3859509) (@lem3859513)). Qed.
Lemma lem3859515 : True = term251.
Proof. exact (SYM (@lem3859514)). Qed.
Lemma lem3859516 : term251.
Proof. exact (EQ_MP (@lem3859515) (@lem0)). Qed.
Lemma lem3859517 : term525 = term528.
Proof. exact (@lem3859506 (@lem3859516)). Qed.
Lemma lem3859519 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3859520 : term225 = term230.
Proof. exact (@lem3859519 term11 term11). Qed.
Lemma lem3859521 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859522 : term211 = term11.
Proof. exact (EQ_MP (@lem3859521) (@lem940073)). Qed.
Lemma lem3859523 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859524 : term209 = term143.
Proof. exact (MK_COMB (@lem3859523) (@lem3859522)). Qed.
Lemma lem3859525 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3859526 : term230 = term199.
Proof. exact (MK_COMB (@lem3859525) (@lem3859524)). Qed.
Lemma lem3859527 : term225 = term199.
Proof. exact (TRANS (@lem3859520) (@lem3859526)). Qed.
Lemma lem3859529 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859530 : term263 = term133.
Proof. exact (@lem3859529 term11). Qed.
Lemma lem3859531 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3859532 : term529 = term135.
Proof. exact (MK_COMB (@lem3859531) (@lem3859530)). Qed.
Lemma lem3859533 : term528 = term523.
Proof. exact (MK_COMB (@lem3859532) (@lem3859527)). Qed.
Lemma lem3859535 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3859536 : term523 = term532.
Proof. exact (@lem3859535 (NUMERAL 0) term11). Qed.
Lemma lem3859537 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859538 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3859539 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859538 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3859537)). Qed.
Lemma lem3859540 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3859539) (@lem3859537)). Qed.
Lemma lem3859541 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3859542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3859543 : term533 = (and True).
Proof. exact (MK_COMB (@lem3859542) (@lem3859541)). Qed.
Lemma lem3859544 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3859543) (@lem3859540)). Qed.
Lemma lem3859546 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3859547 : term532 = False.
Proof. exact (TRANS (@lem3859544) (@lem3859546)). Qed.
Lemma lem3859548 : term523 = False.
Proof. exact (TRANS (@lem3859536) (@lem3859547)). Qed.
Lemma lem3859549 : term528 = False.
Proof. exact (TRANS (@lem3859533) (@lem3859548)). Qed.
Lemma lem3859550 : term525 = False.
Proof. exact (TRANS (@lem3859517) (@lem3859549)). Qed.
Lemma lem3859551 : term523 = False.
Proof. exact (TRANS (@lem3859494) (@lem3859550)). Qed.
Lemma lem3859552 : term522 = False.
Proof. exact (TRANS (@lem3859485) (@lem3859551)). Qed.
Lemma lem3859553 (_44749 : int) (_44750 : int) (h1 : term614 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3859552) (@lem3859482 _44749 _44750 h1)). Qed.
Lemma lem3859554 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term615 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3859555 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term447 _44749 _44750.
Proof. exact (proj2 (@lem3859554 _44749 _44750 h1)). Qed.
Lemma lem3859557 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term398 _44749 _44750.
Proof. exact (proj2 (@lem3859555 _44749 _44750 h1)). Qed.
Lemma lem3859558 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term219 _44750.
Proof. exact (proj1 (@lem3859555 _44749 _44750 h1)). Qed.
Lemma lem3859559 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term346 _44749 _44750.
Proof. exact (proj2 (@lem3859557 _44749 _44750 h1)). Qed.
Lemma lem3859563 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term293 _44750.
Proof. exact (proj2 (@lem3859559 _44749 _44750 h1)). Qed.
Lemma lem3859566 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3859567 : term471 = term251.
Proof. exact (@lem3859566 term133 term143). Qed.
Lemma lem3859569 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859570 : term143 = term224.
Proof. exact (@lem3859569 term11). Qed.
Lemma lem3859572 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859573 : term133 = term196.
Proof. exact (@lem3859572 (NUMERAL 0)). Qed.
Lemma lem3859574 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3859575 : term472 = term473.
Proof. exact (MK_COMB (@lem3859574) (@lem3859573)). Qed.
Lemma lem3859576 : term251 = term474.
Proof. exact (MK_COMB (@lem3859575) (@lem3859570)). Qed.
Lemma lem3859577 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3859579 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859580 : term251 = term252.
Proof. exact (@lem3859579 (NUMERAL 0) term11). Qed.
Lemma lem3859581 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859582 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859583 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859582 h1) (fun h1 : term252 = True => @lem3859581)). Qed.
Lemma lem3859584 : term252 = True.
Proof. exact (EQ_MP (@lem3859583) (@lem3859581)). Qed.
Lemma lem3859585 : term251 = True.
Proof. exact (TRANS (@lem3859580) (@lem3859584)). Qed.
Lemma lem3859586 : True = term251.
Proof. exact (SYM (@lem3859585)). Qed.
Lemma lem3859587 : term251.
Proof. exact (EQ_MP (@lem3859586) (@lem0)). Qed.
Lemma lem3859588 : term476.
Proof. exact (@lem3859577 (@lem3859587)). Qed.
Lemma lem3859590 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859591 : term251 = term252.
Proof. exact (@lem3859590 (NUMERAL 0) term11). Qed.
Lemma lem3859592 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859593 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859594 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859593 h1) (fun h1 : term252 = True => @lem3859592)). Qed.
Lemma lem3859595 : term252 = True.
Proof. exact (EQ_MP (@lem3859594) (@lem3859592)). Qed.
Lemma lem3859596 : term251 = True.
Proof. exact (TRANS (@lem3859591) (@lem3859595)). Qed.
Lemma lem3859597 : True = term251.
Proof. exact (SYM (@lem3859596)). Qed.
Lemma lem3859598 : term251.
Proof. exact (EQ_MP (@lem3859597) (@lem0)). Qed.
Lemma lem3859599 : term474 = term477.
Proof. exact (@lem3859588 (@lem3859598)). Qed.
Lemma lem3859601 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3859602 : term208 = term209.
Proof. exact (@lem3859601 term11 term11). Qed.
Lemma lem3859603 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859604 : term211 = term11.
Proof. exact (EQ_MP (@lem3859603) (@lem940073)). Qed.
Lemma lem3859605 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859606 : term209 = term143.
Proof. exact (MK_COMB (@lem3859605) (@lem3859604)). Qed.
Lemma lem3859607 : term208 = term143.
Proof. exact (TRANS (@lem3859602) (@lem3859606)). Qed.
Lemma lem3859609 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859610 : term263 = term133.
Proof. exact (@lem3859609 term11). Qed.
Lemma lem3859611 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3859612 : term478 = term472.
Proof. exact (MK_COMB (@lem3859611) (@lem3859610)). Qed.
Lemma lem3859613 : term477 = term251.
Proof. exact (MK_COMB (@lem3859612) (@lem3859607)). Qed.
Lemma lem3859615 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859616 : term251 = term252.
Proof. exact (@lem3859615 (NUMERAL 0) term11). Qed.
Lemma lem3859617 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859618 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859619 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859618 h1) (fun h1 : term252 = True => @lem3859617)). Qed.
Lemma lem3859620 : term252 = True.
Proof. exact (EQ_MP (@lem3859619) (@lem3859617)). Qed.
Lemma lem3859621 : term251 = True.
Proof. exact (TRANS (@lem3859616) (@lem3859620)). Qed.
Lemma lem3859622 : term477 = True.
Proof. exact (TRANS (@lem3859613) (@lem3859621)). Qed.
Lemma lem3859623 : term474 = True.
Proof. exact (TRANS (@lem3859599) (@lem3859622)). Qed.
Lemma lem3859624 : term251 = True.
Proof. exact (TRANS (@lem3859576) (@lem3859623)). Qed.
Lemma lem3859625 : term471 = True.
Proof. exact (TRANS (@lem3859567) (@lem3859624)). Qed.
Lemma lem3859626 : True = term471.
Proof. exact (SYM (@lem3859625)). Qed.
Lemma lem3859627 : term471.
Proof. exact (EQ_MP (@lem3859626) (@lem0)). Qed.
Lemma lem3859628 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term577 _44750.
Proof. exact (conj (@lem3859627) (@lem3859558 _44749 _44750 h1)). Qed.
Lemma lem3859630 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3859631 (_44750 : int) : term578 _44750.
Proof. exact (@lem3859630 term143 (real_of_int _44750)). Qed.
Lemma lem3859632 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term579 _44750.
Proof. exact (@lem3859631 _44750 (@lem3859628 _44749 _44750 h1)). Qed.
Lemma lem3859633 (_44750 : int) : (term542 _44750) = (real_of_int _44750).
Proof. exact (@lem1982733 (real_of_int _44750)). Qed.
Lemma lem3859634 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3859635 (_44750 : int) : (term580 _44750) = (term218 _44750).
Proof. exact (MK_COMB (@lem3859634) (@lem3859633 _44750)). Qed.
Lemma lem3859636 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3859637 (_44750 : int) : (term579 _44750) = (term219 _44750).
Proof. exact (MK_COMB (@lem3859635 _44750) (@lem3859636)). Qed.
Lemma lem3859638 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term219 _44750.
Proof. exact (EQ_MP (@lem3859637 _44750) (@lem3859632 _44749 _44750 h1)). Qed.
Lemma lem3859640 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3859641 : term471 = term251.
Proof. exact (@lem3859640 term133 term143). Qed.
Lemma lem3859643 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859644 : term143 = term224.
Proof. exact (@lem3859643 term11). Qed.
Lemma lem3859646 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859647 : term133 = term196.
Proof. exact (@lem3859646 (NUMERAL 0)). Qed.
Lemma lem3859648 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3859649 : term472 = term473.
Proof. exact (MK_COMB (@lem3859648) (@lem3859647)). Qed.
Lemma lem3859650 : term251 = term474.
Proof. exact (MK_COMB (@lem3859649) (@lem3859644)). Qed.
Lemma lem3859651 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3859653 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859654 : term251 = term252.
Proof. exact (@lem3859653 (NUMERAL 0) term11). Qed.
Lemma lem3859655 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859656 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859657 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859656 h1) (fun h1 : term252 = True => @lem3859655)). Qed.
Lemma lem3859658 : term252 = True.
Proof. exact (EQ_MP (@lem3859657) (@lem3859655)). Qed.
Lemma lem3859659 : term251 = True.
Proof. exact (TRANS (@lem3859654) (@lem3859658)). Qed.
Lemma lem3859660 : True = term251.
Proof. exact (SYM (@lem3859659)). Qed.
Lemma lem3859661 : term251.
Proof. exact (EQ_MP (@lem3859660) (@lem0)). Qed.
Lemma lem3859662 : term476.
Proof. exact (@lem3859651 (@lem3859661)). Qed.
Lemma lem3859664 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859665 : term251 = term252.
Proof. exact (@lem3859664 (NUMERAL 0) term11). Qed.
Lemma lem3859666 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859667 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859668 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859667 h1) (fun h1 : term252 = True => @lem3859666)). Qed.
Lemma lem3859669 : term252 = True.
Proof. exact (EQ_MP (@lem3859668) (@lem3859666)). Qed.
Lemma lem3859670 : term251 = True.
Proof. exact (TRANS (@lem3859665) (@lem3859669)). Qed.
Lemma lem3859671 : True = term251.
Proof. exact (SYM (@lem3859670)). Qed.
Lemma lem3859672 : term251.
Proof. exact (EQ_MP (@lem3859671) (@lem0)). Qed.
Lemma lem3859673 : term474 = term477.
Proof. exact (@lem3859662 (@lem3859672)). Qed.
Lemma lem3859675 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3859676 : term208 = term209.
Proof. exact (@lem3859675 term11 term11). Qed.
Lemma lem3859677 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859678 : term211 = term11.
Proof. exact (EQ_MP (@lem3859677) (@lem940073)). Qed.
Lemma lem3859679 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859680 : term209 = term143.
Proof. exact (MK_COMB (@lem3859679) (@lem3859678)). Qed.
Lemma lem3859681 : term208 = term143.
Proof. exact (TRANS (@lem3859676) (@lem3859680)). Qed.
Lemma lem3859683 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859684 : term263 = term133.
Proof. exact (@lem3859683 term11). Qed.
Lemma lem3859685 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3859686 : term478 = term472.
Proof. exact (MK_COMB (@lem3859685) (@lem3859684)). Qed.
Lemma lem3859687 : term477 = term251.
Proof. exact (MK_COMB (@lem3859686) (@lem3859681)). Qed.
Lemma lem3859689 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859690 : term251 = term252.
Proof. exact (@lem3859689 (NUMERAL 0) term11). Qed.
Lemma lem3859691 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859692 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859693 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859692 h1) (fun h1 : term252 = True => @lem3859691)). Qed.
Lemma lem3859694 : term252 = True.
Proof. exact (EQ_MP (@lem3859693) (@lem3859691)). Qed.
Lemma lem3859695 : term251 = True.
Proof. exact (TRANS (@lem3859690) (@lem3859694)). Qed.
Lemma lem3859696 : term477 = True.
Proof. exact (TRANS (@lem3859687) (@lem3859695)). Qed.
Lemma lem3859697 : term474 = True.
Proof. exact (TRANS (@lem3859673) (@lem3859696)). Qed.
Lemma lem3859698 : term251 = True.
Proof. exact (TRANS (@lem3859650) (@lem3859697)). Qed.
Lemma lem3859699 : term471 = True.
Proof. exact (TRANS (@lem3859641) (@lem3859698)). Qed.
Lemma lem3859700 : True = term471.
Proof. exact (SYM (@lem3859699)). Qed.
Lemma lem3859701 : term471.
Proof. exact (EQ_MP (@lem3859700) (@lem0)). Qed.
Lemma lem3859702 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term606 _44750.
Proof. exact (conj (@lem3859701) (@lem3859563 _44749 _44750 h1)). Qed.
Lemma lem3859704 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3859705 (_44750 : int) : term607 _44750.
Proof. exact (@lem3859704 term143 (term234 _44750)). Qed.
Lemma lem3859706 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term608 _44750.
Proof. exact (@lem3859705 _44750 (@lem3859702 _44749 _44750 h1)). Qed.
Lemma lem3859707 (_44750 : int) : (term594 _44750) = (term234 _44750).
Proof. exact (@lem1982733 (term234 _44750)). Qed.
Lemma lem3859708 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3859709 (_44750 : int) : (term609 _44750) = (term292 _44750).
Proof. exact (MK_COMB (@lem3859708) (@lem3859707 _44750)). Qed.
Lemma lem3859710 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3859711 (_44750 : int) : (term608 _44750) = (term293 _44750).
Proof. exact (MK_COMB (@lem3859709 _44750) (@lem3859710)). Qed.
Lemma lem3859712 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term293 _44750.
Proof. exact (EQ_MP (@lem3859711 _44750) (@lem3859706 _44749 _44750 h1)). Qed.
Lemma lem3859713 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term616 _44750.
Proof. exact (conj (@lem3859712 _44749 _44750 h1) (@lem3859638 _44749 _44750 h1)). Qed.
Lemma lem3859715 (x : real) (y : real) : term570 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3859716 (_44750 : int) : term617 _44750.
Proof. exact (@lem3859715 (term234 _44750) (real_of_int _44750)). Qed.
Lemma lem3859717 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term598 _44750.
Proof. exact (@lem3859716 _44750 (@lem3859713 _44749 _44750 h1)). Qed.
Lemma lem3859718 (_44750 : int) : (term599 _44750) = (term574 _44750).
Proof. exact (@lem1982759 (term237 _44750) (real_of_int _44750) term199). Qed.
Lemma lem3859719 (_44750 : int) : (term497 _44750) = (term498 _44750).
Proof. exact (@lem1982713 term199 (real_of_int _44750)). Qed.
Lemma lem3859721 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859722 : term143 = term224.
Proof. exact (@lem3859721 term11). Qed.
Lemma lem3859724 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3859725 : term199 = term200.
Proof. exact (@lem3859724 term11). Qed.
Lemma lem3859726 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3859727 : term499 = term500.
Proof. exact (MK_COMB (@lem3859726) (@lem3859725)). Qed.
Lemma lem3859728 : term501 = term502.
Proof. exact (MK_COMB (@lem3859727) (@lem3859722)). Qed.
Lemma lem3859729 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3859731 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859732 : term251 = term252.
Proof. exact (@lem3859731 (NUMERAL 0) term11). Qed.
Lemma lem3859733 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859734 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859735 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859734 h1) (fun h1 : term252 = True => @lem3859733)). Qed.
Lemma lem3859736 : term252 = True.
Proof. exact (EQ_MP (@lem3859735) (@lem3859733)). Qed.
Lemma lem3859737 : term251 = True.
Proof. exact (TRANS (@lem3859732) (@lem3859736)). Qed.
Lemma lem3859738 : True = term251.
Proof. exact (SYM (@lem3859737)). Qed.
Lemma lem3859739 : term251.
Proof. exact (EQ_MP (@lem3859738) (@lem0)). Qed.
Lemma lem3859740 : term504.
Proof. exact (@lem3859729 (@lem3859739)). Qed.
Lemma lem3859742 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859743 : term251 = term252.
Proof. exact (@lem3859742 (NUMERAL 0) term11). Qed.
Lemma lem3859744 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859745 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859746 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859745 h1) (fun h1 : term252 = True => @lem3859744)). Qed.
Lemma lem3859747 : term252 = True.
Proof. exact (EQ_MP (@lem3859746) (@lem3859744)). Qed.
Lemma lem3859748 : term251 = True.
Proof. exact (TRANS (@lem3859743) (@lem3859747)). Qed.
Lemma lem3859749 : True = term251.
Proof. exact (SYM (@lem3859748)). Qed.
Lemma lem3859750 : term251.
Proof. exact (EQ_MP (@lem3859749) (@lem0)). Qed.
Lemma lem3859751 : term505.
Proof. exact (@lem3859740 (@lem3859750)). Qed.
Lemma lem3859753 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859754 : term251 = term252.
Proof. exact (@lem3859753 (NUMERAL 0) term11). Qed.
Lemma lem3859755 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859756 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859757 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859756 h1) (fun h1 : term252 = True => @lem3859755)). Qed.
Lemma lem3859758 : term252 = True.
Proof. exact (EQ_MP (@lem3859757) (@lem3859755)). Qed.
Lemma lem3859759 : term251 = True.
Proof. exact (TRANS (@lem3859754) (@lem3859758)). Qed.
Lemma lem3859760 : True = term251.
Proof. exact (SYM (@lem3859759)). Qed.
Lemma lem3859761 : term251.
Proof. exact (EQ_MP (@lem3859760) (@lem0)). Qed.
Lemma lem3859762 : term506.
Proof. exact (@lem3859751 (@lem3859761)). Qed.
Lemma lem3859764 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3859765 : term208 = term209.
Proof. exact (@lem3859764 term11 term11). Qed.
Lemma lem3859766 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859767 : term211 = term11.
Proof. exact (EQ_MP (@lem3859766) (@lem940073)). Qed.
Lemma lem3859768 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859769 : term209 = term143.
Proof. exact (MK_COMB (@lem3859768) (@lem3859767)). Qed.
Lemma lem3859770 : term208 = term143.
Proof. exact (TRANS (@lem3859765) (@lem3859769)). Qed.
Lemma lem3859772 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3859773 : term225 = term230.
Proof. exact (@lem3859772 term11 term11). Qed.
Lemma lem3859774 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859775 : term211 = term11.
Proof. exact (EQ_MP (@lem3859774) (@lem940073)). Qed.
Lemma lem3859776 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859777 : term209 = term143.
Proof. exact (MK_COMB (@lem3859776) (@lem3859775)). Qed.
Lemma lem3859778 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3859779 : term230 = term199.
Proof. exact (MK_COMB (@lem3859778) (@lem3859777)). Qed.
Lemma lem3859780 : term225 = term199.
Proof. exact (TRANS (@lem3859773) (@lem3859779)). Qed.
Lemma lem3859781 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3859782 : term507 = term499.
Proof. exact (MK_COMB (@lem3859781) (@lem3859780)). Qed.
Lemma lem3859783 : term508 = term501.
Proof. exact (MK_COMB (@lem3859782) (@lem3859770)). Qed.
Lemma lem3859785 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3859786 : term501 = term133.
Proof. exact (@lem3859785 term11). Qed.
Lemma lem3859787 : term508 = term133.
Proof. exact (TRANS (@lem3859783) (@lem3859786)). Qed.
Lemma lem3859788 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3859789 : term510 = term261.
Proof. exact (MK_COMB (@lem3859788) (@lem3859787)). Qed.
Lemma lem3859790 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3859791 : term511 = term263.
Proof. exact (MK_COMB (@lem3859789) (@lem3859790)). Qed.
Lemma lem3859793 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859794 : term263 = term133.
Proof. exact (@lem3859793 term11). Qed.
Lemma lem3859795 : term511 = term133.
Proof. exact (TRANS (@lem3859791) (@lem3859794)). Qed.
Lemma lem3859797 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3859798 : term208 = term209.
Proof. exact (@lem3859797 term11 term11). Qed.
Lemma lem3859799 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859800 : term211 = term11.
Proof. exact (EQ_MP (@lem3859799) (@lem940073)). Qed.
Lemma lem3859801 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859802 : term209 = term143.
Proof. exact (MK_COMB (@lem3859801) (@lem3859800)). Qed.
Lemma lem3859803 : term208 = term143.
Proof. exact (TRANS (@lem3859798) (@lem3859802)). Qed.
Lemma lem3859804 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3859805 : term265 = term263.
Proof. exact (MK_COMB (@lem3859804) (@lem3859803)). Qed.
Lemma lem3859807 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859808 : term263 = term133.
Proof. exact (@lem3859807 term11). Qed.
Lemma lem3859809 : term265 = term133.
Proof. exact (TRANS (@lem3859805) (@lem3859808)). Qed.
Lemma lem3859810 : term133 = term265.
Proof. exact (SYM (@lem3859809)). Qed.
Lemma lem3859811 : term511 = term265.
Proof. exact (TRANS (@lem3859795) (@lem3859810)). Qed.
Lemma lem3859812 : term502 = term196.
Proof. exact (@lem3859762 (@lem3859811)). Qed.
Lemma lem3859813 : term501 = term196.
Proof. exact (TRANS (@lem3859728) (@lem3859812)). Qed.
Lemma lem3859815 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3859816 : term196 = term133.
Proof. exact (@lem3859815 term133). Qed.
Lemma lem3859817 : term501 = term133.
Proof. exact (TRANS (@lem3859813) (@lem3859816)). Qed.
Lemma lem3859818 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3859819 : term512 = term261.
Proof. exact (MK_COMB (@lem3859818) (@lem3859817)). Qed.
Lemma lem3859820 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3859821 (_44750 : int) : (term498 _44750) = (term513 _44750).
Proof. exact (MK_COMB (@lem3859819) (@lem3859820 _44750)). Qed.
Lemma lem3859822 (_44750 : int) : (term497 _44750) = (term513 _44750).
Proof. exact (TRANS (@lem3859719 _44750) (@lem3859821 _44750)). Qed.
Lemma lem3859823 (_44750 : int) : (term513 _44750) = term133.
Proof. exact (@lem1982719 (real_of_int _44750)). Qed.
Lemma lem3859824 (_44750 : int) : (term497 _44750) = term133.
Proof. exact (TRANS (@lem3859822 _44750) (@lem3859823 _44750)). Qed.
Lemma lem3859825 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3859826 (_44750 : int) : (term514 _44750) = term175.
Proof. exact (MK_COMB (@lem3859825) (@lem3859824 _44750)). Qed.
Lemma lem3859827 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3859828 (_44750 : int) : (term574 _44750) = term519.
Proof. exact (MK_COMB (@lem3859826 _44750) (@lem3859827)). Qed.
Lemma lem3859829 (_44750 : int) : (term599 _44750) = term519.
Proof. exact (TRANS (@lem3859718 _44750) (@lem3859828 _44750)). Qed.
Lemma lem3859830 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3859831 (_44750 : int) : (term599 _44750) = term199.
Proof. exact (TRANS (@lem3859829 _44750) (@lem3859830)). Qed.
Lemma lem3859832 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3859833 (_44750 : int) : (term600 _44750) = term521.
Proof. exact (MK_COMB (@lem3859832) (@lem3859831 _44750)). Qed.
Lemma lem3859834 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3859835 (_44750 : int) : (term598 _44750) = term522.
Proof. exact (MK_COMB (@lem3859833 _44750) (@lem3859834)). Qed.
Lemma lem3859836 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : term522.
Proof. exact (EQ_MP (@lem3859835 _44750) (@lem3859717 _44749 _44750 h1)). Qed.
Lemma lem3859838 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3859839 : term522 = term523.
Proof. exact (@lem3859838 term133 term199). Qed.
Lemma lem3859841 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3859842 : term199 = term200.
Proof. exact (@lem3859841 term11). Qed.
Lemma lem3859844 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859845 : term133 = term196.
Proof. exact (@lem3859844 (NUMERAL 0)). Qed.
Lemma lem3859846 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3859847 : term135 = term524.
Proof. exact (MK_COMB (@lem3859846) (@lem3859845)). Qed.
Lemma lem3859848 : term523 = term525.
Proof. exact (MK_COMB (@lem3859847) (@lem3859842)). Qed.
Lemma lem3859849 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3859851 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859852 : term251 = term252.
Proof. exact (@lem3859851 (NUMERAL 0) term11). Qed.
Lemma lem3859853 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859854 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859855 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859854 h1) (fun h1 : term252 = True => @lem3859853)). Qed.
Lemma lem3859856 : term252 = True.
Proof. exact (EQ_MP (@lem3859855) (@lem3859853)). Qed.
Lemma lem3859857 : term251 = True.
Proof. exact (TRANS (@lem3859852) (@lem3859856)). Qed.
Lemma lem3859858 : True = term251.
Proof. exact (SYM (@lem3859857)). Qed.
Lemma lem3859859 : term251.
Proof. exact (EQ_MP (@lem3859858) (@lem0)). Qed.
Lemma lem3859860 : term527.
Proof. exact (@lem3859849 (@lem3859859)). Qed.
Lemma lem3859862 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859863 : term251 = term252.
Proof. exact (@lem3859862 (NUMERAL 0) term11). Qed.
Lemma lem3859864 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859865 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859866 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859865 h1) (fun h1 : term252 = True => @lem3859864)). Qed.
Lemma lem3859867 : term252 = True.
Proof. exact (EQ_MP (@lem3859866) (@lem3859864)). Qed.
Lemma lem3859868 : term251 = True.
Proof. exact (TRANS (@lem3859863) (@lem3859867)). Qed.
Lemma lem3859869 : True = term251.
Proof. exact (SYM (@lem3859868)). Qed.
Lemma lem3859870 : term251.
Proof. exact (EQ_MP (@lem3859869) (@lem0)). Qed.
Lemma lem3859871 : term525 = term528.
Proof. exact (@lem3859860 (@lem3859870)). Qed.
Lemma lem3859873 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3859874 : term225 = term230.
Proof. exact (@lem3859873 term11 term11). Qed.
Lemma lem3859875 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859876 : term211 = term11.
Proof. exact (EQ_MP (@lem3859875) (@lem940073)). Qed.
Lemma lem3859877 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859878 : term209 = term143.
Proof. exact (MK_COMB (@lem3859877) (@lem3859876)). Qed.
Lemma lem3859879 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3859880 : term230 = term199.
Proof. exact (MK_COMB (@lem3859879) (@lem3859878)). Qed.
Lemma lem3859881 : term225 = term199.
Proof. exact (TRANS (@lem3859874) (@lem3859880)). Qed.
Lemma lem3859883 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859884 : term263 = term133.
Proof. exact (@lem3859883 term11). Qed.
Lemma lem3859885 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3859886 : term529 = term135.
Proof. exact (MK_COMB (@lem3859885) (@lem3859884)). Qed.
Lemma lem3859887 : term528 = term523.
Proof. exact (MK_COMB (@lem3859886) (@lem3859881)). Qed.
Lemma lem3859889 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3859890 : term523 = term532.
Proof. exact (@lem3859889 (NUMERAL 0) term11). Qed.
Lemma lem3859891 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859892 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3859893 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859892 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3859891)). Qed.
Lemma lem3859894 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3859893) (@lem3859891)). Qed.
Lemma lem3859895 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3859896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3859897 : term533 = (and True).
Proof. exact (MK_COMB (@lem3859896) (@lem3859895)). Qed.
Lemma lem3859898 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3859897) (@lem3859894)). Qed.
Lemma lem3859900 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3859901 : term532 = False.
Proof. exact (TRANS (@lem3859898) (@lem3859900)). Qed.
Lemma lem3859902 : term523 = False.
Proof. exact (TRANS (@lem3859890) (@lem3859901)). Qed.
Lemma lem3859903 : term528 = False.
Proof. exact (TRANS (@lem3859887) (@lem3859902)). Qed.
Lemma lem3859904 : term525 = False.
Proof. exact (TRANS (@lem3859871) (@lem3859903)). Qed.
Lemma lem3859905 : term523 = False.
Proof. exact (TRANS (@lem3859848) (@lem3859904)). Qed.
Lemma lem3859906 : term522 = False.
Proof. exact (TRANS (@lem3859839) (@lem3859905)). Qed.
Lemma lem3859907 (_44749 : int) (_44750 : int) (h1 : term615 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3859906) (@lem3859836 _44749 _44750 h1)). Qed.
Lemma lem3859908 (_44749 : int) (_44750 : int) (h1 : term445 _44749 _44750) : False.
Proof. exact (or_elim (@lem3859149 _44749 _44750 h1) (fun h0 : term614 _44749 _44750 => @lem3859553 _44749 _44750 h0) (fun h0 : term615 _44749 _44750 => @lem3859907 _44749 _44750 h0)). Qed.
Lemma lem3859909 (_44749 : int) (_44750 : int) (h1 : term441 _44749 _44750) : term441 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3859910 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term618 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3859911 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term442 _44749 _44750.
Proof. exact (proj2 (@lem3859910 _44749 _44750 h1)). Qed.
Lemma lem3859913 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term393 _44749 _44750.
Proof. exact (proj2 (@lem3859911 _44749 _44750 h1)). Qed.
Lemma lem3859915 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term347 _44750.
Proof. exact (proj2 (@lem3859913 _44749 _44750 h1)). Qed.
Lemma lem3859917 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term293 _44750.
Proof. exact (proj2 (@lem3859915 _44749 _44750 h1)). Qed.
Lemma lem3859918 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : (real_of_int _44750) = term133.
Proof. exact (proj1 (@lem3859915 _44749 _44750 h1)). Qed.
Lemma lem3859920 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3859921 : term471 = term251.
Proof. exact (@lem3859920 term133 term143). Qed.
Lemma lem3859923 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859924 : term143 = term224.
Proof. exact (@lem3859923 term11). Qed.
Lemma lem3859926 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3859927 : term133 = term196.
Proof. exact (@lem3859926 (NUMERAL 0)). Qed.
Lemma lem3859928 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3859929 : term472 = term473.
Proof. exact (MK_COMB (@lem3859928) (@lem3859927)). Qed.
Lemma lem3859930 : term251 = term474.
Proof. exact (MK_COMB (@lem3859929) (@lem3859924)). Qed.
Lemma lem3859931 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3859933 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859934 : term251 = term252.
Proof. exact (@lem3859933 (NUMERAL 0) term11). Qed.
Lemma lem3859935 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859936 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859937 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859936 h1) (fun h1 : term252 = True => @lem3859935)). Qed.
Lemma lem3859938 : term252 = True.
Proof. exact (EQ_MP (@lem3859937) (@lem3859935)). Qed.
Lemma lem3859939 : term251 = True.
Proof. exact (TRANS (@lem3859934) (@lem3859938)). Qed.
Lemma lem3859940 : True = term251.
Proof. exact (SYM (@lem3859939)). Qed.
Lemma lem3859941 : term251.
Proof. exact (EQ_MP (@lem3859940) (@lem0)). Qed.
Lemma lem3859942 : term476.
Proof. exact (@lem3859931 (@lem3859941)). Qed.
Lemma lem3859944 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859945 : term251 = term252.
Proof. exact (@lem3859944 (NUMERAL 0) term11). Qed.
Lemma lem3859946 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859947 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859948 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859947 h1) (fun h1 : term252 = True => @lem3859946)). Qed.
Lemma lem3859949 : term252 = True.
Proof. exact (EQ_MP (@lem3859948) (@lem3859946)). Qed.
Lemma lem3859950 : term251 = True.
Proof. exact (TRANS (@lem3859945) (@lem3859949)). Qed.
Lemma lem3859951 : True = term251.
Proof. exact (SYM (@lem3859950)). Qed.
Lemma lem3859952 : term251.
Proof. exact (EQ_MP (@lem3859951) (@lem0)). Qed.
Lemma lem3859953 : term474 = term477.
Proof. exact (@lem3859942 (@lem3859952)). Qed.
Lemma lem3859955 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3859956 : term208 = term209.
Proof. exact (@lem3859955 term11 term11). Qed.
Lemma lem3859957 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3859958 : term211 = term11.
Proof. exact (EQ_MP (@lem3859957) (@lem940073)). Qed.
Lemma lem3859959 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3859960 : term209 = term143.
Proof. exact (MK_COMB (@lem3859959) (@lem3859958)). Qed.
Lemma lem3859961 : term208 = term143.
Proof. exact (TRANS (@lem3859956) (@lem3859960)). Qed.
Lemma lem3859963 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3859964 : term263 = term133.
Proof. exact (@lem3859963 term11). Qed.
Lemma lem3859965 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3859966 : term478 = term472.
Proof. exact (MK_COMB (@lem3859965) (@lem3859964)). Qed.
Lemma lem3859967 : term477 = term251.
Proof. exact (MK_COMB (@lem3859966) (@lem3859961)). Qed.
Lemma lem3859969 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3859970 : term251 = term252.
Proof. exact (@lem3859969 (NUMERAL 0) term11). Qed.
Lemma lem3859971 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3859972 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3859973 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3859972 h1) (fun h1 : term252 = True => @lem3859971)). Qed.
Lemma lem3859974 : term252 = True.
Proof. exact (EQ_MP (@lem3859973) (@lem3859971)). Qed.
Lemma lem3859975 : term251 = True.
Proof. exact (TRANS (@lem3859970) (@lem3859974)). Qed.
Lemma lem3859976 : term477 = True.
Proof. exact (TRANS (@lem3859967) (@lem3859975)). Qed.
Lemma lem3859977 : term474 = True.
Proof. exact (TRANS (@lem3859953) (@lem3859976)). Qed.
Lemma lem3859978 : term251 = True.
Proof. exact (TRANS (@lem3859930) (@lem3859977)). Qed.
Lemma lem3859979 : term471 = True.
Proof. exact (TRANS (@lem3859921) (@lem3859978)). Qed.
Lemma lem3859980 : True = term471.
Proof. exact (SYM (@lem3859979)). Qed.
Lemma lem3859981 : term471.
Proof. exact (EQ_MP (@lem3859980) (@lem0)). Qed.
Lemma lem3859982 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term606 _44750.
Proof. exact (conj (@lem3859981) (@lem3859917 _44749 _44750 h1)). Qed.
Lemma lem3859984 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3859985 (_44750 : int) : term607 _44750.
Proof. exact (@lem3859984 term143 (term234 _44750)). Qed.
Lemma lem3859986 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term608 _44750.
Proof. exact (@lem3859985 _44750 (@lem3859982 _44749 _44750 h1)). Qed.
Lemma lem3859987 (_44750 : int) : (term594 _44750) = (term234 _44750).
Proof. exact (@lem1982733 (term234 _44750)). Qed.
Lemma lem3859988 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3859989 (_44750 : int) : (term609 _44750) = (term292 _44750).
Proof. exact (MK_COMB (@lem3859988) (@lem3859987 _44750)). Qed.
Lemma lem3859990 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3859991 (_44750 : int) : (term608 _44750) = (term293 _44750).
Proof. exact (MK_COMB (@lem3859989 _44750) (@lem3859990)). Qed.
Lemma lem3859992 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term293 _44750.
Proof. exact (EQ_MP (@lem3859991 _44750) (@lem3859986 _44749 _44750 h1)). Qed.
Lemma lem3859994 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3859995 (_44750 : int) : term539 _44750.
Proof. exact (@lem3859994 (real_of_int _44750)). Qed.
Lemma lem3859996 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term540 _44750.
Proof. exact (@lem3859995 _44750 (@lem3859918 _44749 _44750 h1)). Qed.
Lemma lem3859997 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term541 _44750.
Proof. exact (@lem3859996 _44749 _44750 h1 term143). Qed.
Lemma lem3859998 (_44750 : int) : (term541 _44750) = ((term542 _44750) = term133).
Proof. exact (eq_refl (term541 _44750)). Qed.
Lemma lem3859999 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : (term542 _44750) = term133.
Proof. exact (EQ_MP (@lem3859998 _44750) (@lem3859997 _44749 _44750 h1)). Qed.
Lemma lem3860000 (_44750 : int) : (term542 _44750) = (real_of_int _44750).
Proof. exact (@lem1982733 (real_of_int _44750)). Qed.
Lemma lem3860001 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3860002 (_44750 : int) : (term543 _44750) = (term146 _44750).
Proof. exact (MK_COMB (@lem3860001) (@lem3860000 _44750)). Qed.
Lemma lem3860003 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3860004 (_44750 : int) : ((term542 _44750) = term133) = ((real_of_int _44750) = term133).
Proof. exact (MK_COMB (@lem3860002 _44750) (@lem3860003)). Qed.
Lemma lem3860005 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : (real_of_int _44750) = term133.
Proof. exact (EQ_MP (@lem3860004 _44750) (@lem3859999 _44749 _44750 h1)). Qed.
Lemma lem3860006 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term347 _44750.
Proof. exact (conj (@lem3860005 _44749 _44750 h1) (@lem3859992 _44749 _44750 h1)). Qed.
Lemma lem3860008 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3860009 (_44750 : int) : term610 _44750.
Proof. exact (@lem3860008 (real_of_int _44750) (term234 _44750)). Qed.
Lemma lem3860010 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term611 _44750.
Proof. exact (@lem3860009 _44750 (@lem3860006 _44749 _44750 h1)). Qed.
Lemma lem3860011 (_44750 : int) : (term612 _44750) = (term516 _44750).
Proof. exact (@lem1982763 (real_of_int _44750) (term237 _44750) term199). Qed.
Lemma lem3860012 (_44750 : int) : (term517 _44750) = (term498 _44750).
Proof. exact (@lem1982715 term199 (real_of_int _44750)). Qed.
Lemma lem3860014 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860015 : term143 = term224.
Proof. exact (@lem3860014 term11). Qed.
Lemma lem3860017 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3860018 : term199 = term200.
Proof. exact (@lem3860017 term11). Qed.
Lemma lem3860019 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3860020 : term499 = term500.
Proof. exact (MK_COMB (@lem3860019) (@lem3860018)). Qed.
Lemma lem3860021 : term501 = term502.
Proof. exact (MK_COMB (@lem3860020) (@lem3860015)). Qed.
Lemma lem3860022 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3860024 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860025 : term251 = term252.
Proof. exact (@lem3860024 (NUMERAL 0) term11). Qed.
Lemma lem3860026 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860027 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860028 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860027 h1) (fun h1 : term252 = True => @lem3860026)). Qed.
Lemma lem3860029 : term252 = True.
Proof. exact (EQ_MP (@lem3860028) (@lem3860026)). Qed.
Lemma lem3860030 : term251 = True.
Proof. exact (TRANS (@lem3860025) (@lem3860029)). Qed.
Lemma lem3860031 : True = term251.
Proof. exact (SYM (@lem3860030)). Qed.
Lemma lem3860032 : term251.
Proof. exact (EQ_MP (@lem3860031) (@lem0)). Qed.
Lemma lem3860033 : term504.
Proof. exact (@lem3860022 (@lem3860032)). Qed.
Lemma lem3860035 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860036 : term251 = term252.
Proof. exact (@lem3860035 (NUMERAL 0) term11). Qed.
Lemma lem3860037 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860038 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860039 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860038 h1) (fun h1 : term252 = True => @lem3860037)). Qed.
Lemma lem3860040 : term252 = True.
Proof. exact (EQ_MP (@lem3860039) (@lem3860037)). Qed.
Lemma lem3860041 : term251 = True.
Proof. exact (TRANS (@lem3860036) (@lem3860040)). Qed.
Lemma lem3860042 : True = term251.
Proof. exact (SYM (@lem3860041)). Qed.
Lemma lem3860043 : term251.
Proof. exact (EQ_MP (@lem3860042) (@lem0)). Qed.
Lemma lem3860044 : term505.
Proof. exact (@lem3860033 (@lem3860043)). Qed.
Lemma lem3860046 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860047 : term251 = term252.
Proof. exact (@lem3860046 (NUMERAL 0) term11). Qed.
Lemma lem3860048 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860049 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860050 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860049 h1) (fun h1 : term252 = True => @lem3860048)). Qed.
Lemma lem3860051 : term252 = True.
Proof. exact (EQ_MP (@lem3860050) (@lem3860048)). Qed.
Lemma lem3860052 : term251 = True.
Proof. exact (TRANS (@lem3860047) (@lem3860051)). Qed.
Lemma lem3860053 : True = term251.
Proof. exact (SYM (@lem3860052)). Qed.
Lemma lem3860054 : term251.
Proof. exact (EQ_MP (@lem3860053) (@lem0)). Qed.
Lemma lem3860055 : term506.
Proof. exact (@lem3860044 (@lem3860054)). Qed.
Lemma lem3860057 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3860058 : term208 = term209.
Proof. exact (@lem3860057 term11 term11). Qed.
Lemma lem3860059 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860060 : term211 = term11.
Proof. exact (EQ_MP (@lem3860059) (@lem940073)). Qed.
Lemma lem3860061 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860062 : term209 = term143.
Proof. exact (MK_COMB (@lem3860061) (@lem3860060)). Qed.
Lemma lem3860063 : term208 = term143.
Proof. exact (TRANS (@lem3860058) (@lem3860062)). Qed.
Lemma lem3860065 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3860066 : term225 = term230.
Proof. exact (@lem3860065 term11 term11). Qed.
Lemma lem3860067 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860068 : term211 = term11.
Proof. exact (EQ_MP (@lem3860067) (@lem940073)). Qed.
Lemma lem3860069 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860070 : term209 = term143.
Proof. exact (MK_COMB (@lem3860069) (@lem3860068)). Qed.
Lemma lem3860071 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3860072 : term230 = term199.
Proof. exact (MK_COMB (@lem3860071) (@lem3860070)). Qed.
Lemma lem3860073 : term225 = term199.
Proof. exact (TRANS (@lem3860066) (@lem3860072)). Qed.
Lemma lem3860074 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3860075 : term507 = term499.
Proof. exact (MK_COMB (@lem3860074) (@lem3860073)). Qed.
Lemma lem3860076 : term508 = term501.
Proof. exact (MK_COMB (@lem3860075) (@lem3860063)). Qed.
Lemma lem3860078 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3860079 : term501 = term133.
Proof. exact (@lem3860078 term11). Qed.
Lemma lem3860080 : term508 = term133.
Proof. exact (TRANS (@lem3860076) (@lem3860079)). Qed.
Lemma lem3860081 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3860082 : term510 = term261.
Proof. exact (MK_COMB (@lem3860081) (@lem3860080)). Qed.
Lemma lem3860083 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3860084 : term511 = term263.
Proof. exact (MK_COMB (@lem3860082) (@lem3860083)). Qed.
Lemma lem3860086 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860087 : term263 = term133.
Proof. exact (@lem3860086 term11). Qed.
Lemma lem3860088 : term511 = term133.
Proof. exact (TRANS (@lem3860084) (@lem3860087)). Qed.
Lemma lem3860090 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3860091 : term208 = term209.
Proof. exact (@lem3860090 term11 term11). Qed.
Lemma lem3860092 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860093 : term211 = term11.
Proof. exact (EQ_MP (@lem3860092) (@lem940073)). Qed.
Lemma lem3860094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860095 : term209 = term143.
Proof. exact (MK_COMB (@lem3860094) (@lem3860093)). Qed.
Lemma lem3860096 : term208 = term143.
Proof. exact (TRANS (@lem3860091) (@lem3860095)). Qed.
Lemma lem3860097 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3860098 : term265 = term263.
Proof. exact (MK_COMB (@lem3860097) (@lem3860096)). Qed.
Lemma lem3860100 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860101 : term263 = term133.
Proof. exact (@lem3860100 term11). Qed.
Lemma lem3860102 : term265 = term133.
Proof. exact (TRANS (@lem3860098) (@lem3860101)). Qed.
Lemma lem3860103 : term133 = term265.
Proof. exact (SYM (@lem3860102)). Qed.
Lemma lem3860104 : term511 = term265.
Proof. exact (TRANS (@lem3860088) (@lem3860103)). Qed.
Lemma lem3860105 : term502 = term196.
Proof. exact (@lem3860055 (@lem3860104)). Qed.
Lemma lem3860106 : term501 = term196.
Proof. exact (TRANS (@lem3860021) (@lem3860105)). Qed.
Lemma lem3860108 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3860109 : term196 = term133.
Proof. exact (@lem3860108 term133). Qed.
Lemma lem3860110 : term501 = term133.
Proof. exact (TRANS (@lem3860106) (@lem3860109)). Qed.
Lemma lem3860111 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3860112 : term512 = term261.
Proof. exact (MK_COMB (@lem3860111) (@lem3860110)). Qed.
Lemma lem3860113 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3860114 (_44750 : int) : (term498 _44750) = (term513 _44750).
Proof. exact (MK_COMB (@lem3860112) (@lem3860113 _44750)). Qed.
Lemma lem3860115 (_44750 : int) : (term517 _44750) = (term513 _44750).
Proof. exact (TRANS (@lem3860012 _44750) (@lem3860114 _44750)). Qed.
Lemma lem3860116 (_44750 : int) : (term513 _44750) = term133.
Proof. exact (@lem1982719 (real_of_int _44750)). Qed.
Lemma lem3860117 (_44750 : int) : (term517 _44750) = term133.
Proof. exact (TRANS (@lem3860115 _44750) (@lem3860116 _44750)). Qed.
Lemma lem3860118 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3860119 (_44750 : int) : (term518 _44750) = term175.
Proof. exact (MK_COMB (@lem3860118) (@lem3860117 _44750)). Qed.
Lemma lem3860120 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3860121 (_44750 : int) : (term516 _44750) = term519.
Proof. exact (MK_COMB (@lem3860119 _44750) (@lem3860120)). Qed.
Lemma lem3860122 (_44750 : int) : (term612 _44750) = term519.
Proof. exact (TRANS (@lem3860011 _44750) (@lem3860121 _44750)). Qed.
Lemma lem3860123 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3860124 (_44750 : int) : (term612 _44750) = term199.
Proof. exact (TRANS (@lem3860122 _44750) (@lem3860123)). Qed.
Lemma lem3860125 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3860126 (_44750 : int) : (term613 _44750) = term521.
Proof. exact (MK_COMB (@lem3860125) (@lem3860124 _44750)). Qed.
Lemma lem3860127 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3860128 (_44750 : int) : (term611 _44750) = term522.
Proof. exact (MK_COMB (@lem3860126 _44750) (@lem3860127)). Qed.
Lemma lem3860129 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : term522.
Proof. exact (EQ_MP (@lem3860128 _44750) (@lem3860010 _44749 _44750 h1)). Qed.
Lemma lem3860131 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3860132 : term522 = term523.
Proof. exact (@lem3860131 term133 term199). Qed.
Lemma lem3860134 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3860135 : term199 = term200.
Proof. exact (@lem3860134 term11). Qed.
Lemma lem3860137 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860138 : term133 = term196.
Proof. exact (@lem3860137 (NUMERAL 0)). Qed.
Lemma lem3860139 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3860140 : term135 = term524.
Proof. exact (MK_COMB (@lem3860139) (@lem3860138)). Qed.
Lemma lem3860141 : term523 = term525.
Proof. exact (MK_COMB (@lem3860140) (@lem3860135)). Qed.
Lemma lem3860142 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3860144 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860145 : term251 = term252.
Proof. exact (@lem3860144 (NUMERAL 0) term11). Qed.
Lemma lem3860146 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860147 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860148 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860147 h1) (fun h1 : term252 = True => @lem3860146)). Qed.
Lemma lem3860149 : term252 = True.
Proof. exact (EQ_MP (@lem3860148) (@lem3860146)). Qed.
Lemma lem3860150 : term251 = True.
Proof. exact (TRANS (@lem3860145) (@lem3860149)). Qed.
Lemma lem3860151 : True = term251.
Proof. exact (SYM (@lem3860150)). Qed.
Lemma lem3860152 : term251.
Proof. exact (EQ_MP (@lem3860151) (@lem0)). Qed.
Lemma lem3860153 : term527.
Proof. exact (@lem3860142 (@lem3860152)). Qed.
Lemma lem3860155 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860156 : term251 = term252.
Proof. exact (@lem3860155 (NUMERAL 0) term11). Qed.
Lemma lem3860157 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860158 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860159 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860158 h1) (fun h1 : term252 = True => @lem3860157)). Qed.
Lemma lem3860160 : term252 = True.
Proof. exact (EQ_MP (@lem3860159) (@lem3860157)). Qed.
Lemma lem3860161 : term251 = True.
Proof. exact (TRANS (@lem3860156) (@lem3860160)). Qed.
Lemma lem3860162 : True = term251.
Proof. exact (SYM (@lem3860161)). Qed.
Lemma lem3860163 : term251.
Proof. exact (EQ_MP (@lem3860162) (@lem0)). Qed.
Lemma lem3860164 : term525 = term528.
Proof. exact (@lem3860153 (@lem3860163)). Qed.
Lemma lem3860166 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3860167 : term225 = term230.
Proof. exact (@lem3860166 term11 term11). Qed.
Lemma lem3860168 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860169 : term211 = term11.
Proof. exact (EQ_MP (@lem3860168) (@lem940073)). Qed.
Lemma lem3860170 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860171 : term209 = term143.
Proof. exact (MK_COMB (@lem3860170) (@lem3860169)). Qed.
Lemma lem3860172 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3860173 : term230 = term199.
Proof. exact (MK_COMB (@lem3860172) (@lem3860171)). Qed.
Lemma lem3860174 : term225 = term199.
Proof. exact (TRANS (@lem3860167) (@lem3860173)). Qed.
Lemma lem3860176 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860177 : term263 = term133.
Proof. exact (@lem3860176 term11). Qed.
Lemma lem3860178 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3860179 : term529 = term135.
Proof. exact (MK_COMB (@lem3860178) (@lem3860177)). Qed.
Lemma lem3860180 : term528 = term523.
Proof. exact (MK_COMB (@lem3860179) (@lem3860174)). Qed.
Lemma lem3860182 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3860183 : term523 = term532.
Proof. exact (@lem3860182 (NUMERAL 0) term11). Qed.
Lemma lem3860184 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860185 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3860186 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860185 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3860184)). Qed.
Lemma lem3860187 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3860186) (@lem3860184)). Qed.
Lemma lem3860188 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3860189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3860190 : term533 = (and True).
Proof. exact (MK_COMB (@lem3860189) (@lem3860188)). Qed.
Lemma lem3860191 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3860190) (@lem3860187)). Qed.
Lemma lem3860193 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3860194 : term532 = False.
Proof. exact (TRANS (@lem3860191) (@lem3860193)). Qed.
Lemma lem3860195 : term523 = False.
Proof. exact (TRANS (@lem3860183) (@lem3860194)). Qed.
Lemma lem3860196 : term528 = False.
Proof. exact (TRANS (@lem3860180) (@lem3860195)). Qed.
Lemma lem3860197 : term525 = False.
Proof. exact (TRANS (@lem3860164) (@lem3860196)). Qed.
Lemma lem3860198 : term523 = False.
Proof. exact (TRANS (@lem3860141) (@lem3860197)). Qed.
Lemma lem3860199 : term522 = False.
Proof. exact (TRANS (@lem3860132) (@lem3860198)). Qed.
Lemma lem3860200 (_44749 : int) (_44750 : int) (h1 : term618 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3860199) (@lem3860129 _44749 _44750 h1)). Qed.
Lemma lem3860201 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term619 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3860202 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term443 _44749 _44750.
Proof. exact (proj2 (@lem3860201 _44749 _44750 h1)). Qed.
Lemma lem3860204 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term394 _44749 _44750.
Proof. exact (proj2 (@lem3860202 _44749 _44750 h1)). Qed.
Lemma lem3860206 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term347 _44750.
Proof. exact (proj2 (@lem3860204 _44749 _44750 h1)). Qed.
Lemma lem3860210 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term293 _44750.
Proof. exact (proj2 (@lem3860206 _44749 _44750 h1)). Qed.
Lemma lem3860211 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : (real_of_int _44750) = term133.
Proof. exact (proj1 (@lem3860206 _44749 _44750 h1)). Qed.
Lemma lem3860213 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3860214 : term471 = term251.
Proof. exact (@lem3860213 term133 term143). Qed.
Lemma lem3860216 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860217 : term143 = term224.
Proof. exact (@lem3860216 term11). Qed.
Lemma lem3860219 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860220 : term133 = term196.
Proof. exact (@lem3860219 (NUMERAL 0)). Qed.
Lemma lem3860221 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3860222 : term472 = term473.
Proof. exact (MK_COMB (@lem3860221) (@lem3860220)). Qed.
Lemma lem3860223 : term251 = term474.
Proof. exact (MK_COMB (@lem3860222) (@lem3860217)). Qed.
Lemma lem3860224 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3860226 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860227 : term251 = term252.
Proof. exact (@lem3860226 (NUMERAL 0) term11). Qed.
Lemma lem3860228 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860229 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860230 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860229 h1) (fun h1 : term252 = True => @lem3860228)). Qed.
Lemma lem3860231 : term252 = True.
Proof. exact (EQ_MP (@lem3860230) (@lem3860228)). Qed.
Lemma lem3860232 : term251 = True.
Proof. exact (TRANS (@lem3860227) (@lem3860231)). Qed.
Lemma lem3860233 : True = term251.
Proof. exact (SYM (@lem3860232)). Qed.
Lemma lem3860234 : term251.
Proof. exact (EQ_MP (@lem3860233) (@lem0)). Qed.
Lemma lem3860235 : term476.
Proof. exact (@lem3860224 (@lem3860234)). Qed.
Lemma lem3860237 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860238 : term251 = term252.
Proof. exact (@lem3860237 (NUMERAL 0) term11). Qed.
Lemma lem3860239 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860240 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860241 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860240 h1) (fun h1 : term252 = True => @lem3860239)). Qed.
Lemma lem3860242 : term252 = True.
Proof. exact (EQ_MP (@lem3860241) (@lem3860239)). Qed.
Lemma lem3860243 : term251 = True.
Proof. exact (TRANS (@lem3860238) (@lem3860242)). Qed.
Lemma lem3860244 : True = term251.
Proof. exact (SYM (@lem3860243)). Qed.
Lemma lem3860245 : term251.
Proof. exact (EQ_MP (@lem3860244) (@lem0)). Qed.
Lemma lem3860246 : term474 = term477.
Proof. exact (@lem3860235 (@lem3860245)). Qed.
Lemma lem3860248 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3860249 : term208 = term209.
Proof. exact (@lem3860248 term11 term11). Qed.
Lemma lem3860250 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860251 : term211 = term11.
Proof. exact (EQ_MP (@lem3860250) (@lem940073)). Qed.
Lemma lem3860252 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860253 : term209 = term143.
Proof. exact (MK_COMB (@lem3860252) (@lem3860251)). Qed.
Lemma lem3860254 : term208 = term143.
Proof. exact (TRANS (@lem3860249) (@lem3860253)). Qed.
Lemma lem3860256 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860257 : term263 = term133.
Proof. exact (@lem3860256 term11). Qed.
Lemma lem3860258 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3860259 : term478 = term472.
Proof. exact (MK_COMB (@lem3860258) (@lem3860257)). Qed.
Lemma lem3860260 : term477 = term251.
Proof. exact (MK_COMB (@lem3860259) (@lem3860254)). Qed.
Lemma lem3860262 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860263 : term251 = term252.
Proof. exact (@lem3860262 (NUMERAL 0) term11). Qed.
Lemma lem3860264 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860265 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860266 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860265 h1) (fun h1 : term252 = True => @lem3860264)). Qed.
Lemma lem3860267 : term252 = True.
Proof. exact (EQ_MP (@lem3860266) (@lem3860264)). Qed.
Lemma lem3860268 : term251 = True.
Proof. exact (TRANS (@lem3860263) (@lem3860267)). Qed.
Lemma lem3860269 : term477 = True.
Proof. exact (TRANS (@lem3860260) (@lem3860268)). Qed.
Lemma lem3860270 : term474 = True.
Proof. exact (TRANS (@lem3860246) (@lem3860269)). Qed.
Lemma lem3860271 : term251 = True.
Proof. exact (TRANS (@lem3860223) (@lem3860270)). Qed.
Lemma lem3860272 : term471 = True.
Proof. exact (TRANS (@lem3860214) (@lem3860271)). Qed.
Lemma lem3860273 : True = term471.
Proof. exact (SYM (@lem3860272)). Qed.
Lemma lem3860274 : term471.
Proof. exact (EQ_MP (@lem3860273) (@lem0)). Qed.
Lemma lem3860275 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term606 _44750.
Proof. exact (conj (@lem3860274) (@lem3860210 _44749 _44750 h1)). Qed.
Lemma lem3860277 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3860278 (_44750 : int) : term607 _44750.
Proof. exact (@lem3860277 term143 (term234 _44750)). Qed.
Lemma lem3860279 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term608 _44750.
Proof. exact (@lem3860278 _44750 (@lem3860275 _44749 _44750 h1)). Qed.
Lemma lem3860280 (_44750 : int) : (term594 _44750) = (term234 _44750).
Proof. exact (@lem1982733 (term234 _44750)). Qed.
Lemma lem3860281 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3860282 (_44750 : int) : (term609 _44750) = (term292 _44750).
Proof. exact (MK_COMB (@lem3860281) (@lem3860280 _44750)). Qed.
Lemma lem3860283 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3860284 (_44750 : int) : (term608 _44750) = (term293 _44750).
Proof. exact (MK_COMB (@lem3860282 _44750) (@lem3860283)). Qed.
Lemma lem3860285 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term293 _44750.
Proof. exact (EQ_MP (@lem3860284 _44750) (@lem3860279 _44749 _44750 h1)). Qed.
Lemma lem3860287 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3860288 (_44750 : int) : term539 _44750.
Proof. exact (@lem3860287 (real_of_int _44750)). Qed.
Lemma lem3860289 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term540 _44750.
Proof. exact (@lem3860288 _44750 (@lem3860211 _44749 _44750 h1)). Qed.
Lemma lem3860290 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term541 _44750.
Proof. exact (@lem3860289 _44749 _44750 h1 term143). Qed.
Lemma lem3860291 (_44750 : int) : (term541 _44750) = ((term542 _44750) = term133).
Proof. exact (eq_refl (term541 _44750)). Qed.
Lemma lem3860292 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : (term542 _44750) = term133.
Proof. exact (EQ_MP (@lem3860291 _44750) (@lem3860290 _44749 _44750 h1)). Qed.
Lemma lem3860293 (_44750 : int) : (term542 _44750) = (real_of_int _44750).
Proof. exact (@lem1982733 (real_of_int _44750)). Qed.
Lemma lem3860294 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3860295 (_44750 : int) : (term543 _44750) = (term146 _44750).
Proof. exact (MK_COMB (@lem3860294) (@lem3860293 _44750)). Qed.
Lemma lem3860296 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3860297 (_44750 : int) : ((term542 _44750) = term133) = ((real_of_int _44750) = term133).
Proof. exact (MK_COMB (@lem3860295 _44750) (@lem3860296)). Qed.
Lemma lem3860298 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : (real_of_int _44750) = term133.
Proof. exact (EQ_MP (@lem3860297 _44750) (@lem3860292 _44749 _44750 h1)). Qed.
Lemma lem3860299 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term347 _44750.
Proof. exact (conj (@lem3860298 _44749 _44750 h1) (@lem3860285 _44749 _44750 h1)). Qed.
Lemma lem3860301 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3860302 (_44750 : int) : term610 _44750.
Proof. exact (@lem3860301 (real_of_int _44750) (term234 _44750)). Qed.
Lemma lem3860303 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term611 _44750.
Proof. exact (@lem3860302 _44750 (@lem3860299 _44749 _44750 h1)). Qed.
Lemma lem3860304 (_44750 : int) : (term612 _44750) = (term516 _44750).
Proof. exact (@lem1982763 (real_of_int _44750) (term237 _44750) term199). Qed.
Lemma lem3860305 (_44750 : int) : (term517 _44750) = (term498 _44750).
Proof. exact (@lem1982715 term199 (real_of_int _44750)). Qed.
Lemma lem3860307 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860308 : term143 = term224.
Proof. exact (@lem3860307 term11). Qed.
Lemma lem3860310 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3860311 : term199 = term200.
Proof. exact (@lem3860310 term11). Qed.
Lemma lem3860312 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3860313 : term499 = term500.
Proof. exact (MK_COMB (@lem3860312) (@lem3860311)). Qed.
Lemma lem3860314 : term501 = term502.
Proof. exact (MK_COMB (@lem3860313) (@lem3860308)). Qed.
Lemma lem3860315 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3860317 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860318 : term251 = term252.
Proof. exact (@lem3860317 (NUMERAL 0) term11). Qed.
Lemma lem3860319 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860320 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860321 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860320 h1) (fun h1 : term252 = True => @lem3860319)). Qed.
Lemma lem3860322 : term252 = True.
Proof. exact (EQ_MP (@lem3860321) (@lem3860319)). Qed.
Lemma lem3860323 : term251 = True.
Proof. exact (TRANS (@lem3860318) (@lem3860322)). Qed.
Lemma lem3860324 : True = term251.
Proof. exact (SYM (@lem3860323)). Qed.
Lemma lem3860325 : term251.
Proof. exact (EQ_MP (@lem3860324) (@lem0)). Qed.
Lemma lem3860326 : term504.
Proof. exact (@lem3860315 (@lem3860325)). Qed.
Lemma lem3860328 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860329 : term251 = term252.
Proof. exact (@lem3860328 (NUMERAL 0) term11). Qed.
Lemma lem3860330 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860331 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860332 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860331 h1) (fun h1 : term252 = True => @lem3860330)). Qed.
Lemma lem3860333 : term252 = True.
Proof. exact (EQ_MP (@lem3860332) (@lem3860330)). Qed.
Lemma lem3860334 : term251 = True.
Proof. exact (TRANS (@lem3860329) (@lem3860333)). Qed.
Lemma lem3860335 : True = term251.
Proof. exact (SYM (@lem3860334)). Qed.
Lemma lem3860336 : term251.
Proof. exact (EQ_MP (@lem3860335) (@lem0)). Qed.
Lemma lem3860337 : term505.
Proof. exact (@lem3860326 (@lem3860336)). Qed.
Lemma lem3860339 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860340 : term251 = term252.
Proof. exact (@lem3860339 (NUMERAL 0) term11). Qed.
Lemma lem3860341 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860342 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860343 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860342 h1) (fun h1 : term252 = True => @lem3860341)). Qed.
Lemma lem3860344 : term252 = True.
Proof. exact (EQ_MP (@lem3860343) (@lem3860341)). Qed.
Lemma lem3860345 : term251 = True.
Proof. exact (TRANS (@lem3860340) (@lem3860344)). Qed.
Lemma lem3860346 : True = term251.
Proof. exact (SYM (@lem3860345)). Qed.
Lemma lem3860347 : term251.
Proof. exact (EQ_MP (@lem3860346) (@lem0)). Qed.
Lemma lem3860348 : term506.
Proof. exact (@lem3860337 (@lem3860347)). Qed.
Lemma lem3860350 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3860351 : term208 = term209.
Proof. exact (@lem3860350 term11 term11). Qed.
Lemma lem3860352 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860353 : term211 = term11.
Proof. exact (EQ_MP (@lem3860352) (@lem940073)). Qed.
Lemma lem3860354 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860355 : term209 = term143.
Proof. exact (MK_COMB (@lem3860354) (@lem3860353)). Qed.
Lemma lem3860356 : term208 = term143.
Proof. exact (TRANS (@lem3860351) (@lem3860355)). Qed.
Lemma lem3860358 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3860359 : term225 = term230.
Proof. exact (@lem3860358 term11 term11). Qed.
Lemma lem3860360 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860361 : term211 = term11.
Proof. exact (EQ_MP (@lem3860360) (@lem940073)). Qed.
Lemma lem3860362 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860363 : term209 = term143.
Proof. exact (MK_COMB (@lem3860362) (@lem3860361)). Qed.
Lemma lem3860364 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3860365 : term230 = term199.
Proof. exact (MK_COMB (@lem3860364) (@lem3860363)). Qed.
Lemma lem3860366 : term225 = term199.
Proof. exact (TRANS (@lem3860359) (@lem3860365)). Qed.
Lemma lem3860367 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3860368 : term507 = term499.
Proof. exact (MK_COMB (@lem3860367) (@lem3860366)). Qed.
Lemma lem3860369 : term508 = term501.
Proof. exact (MK_COMB (@lem3860368) (@lem3860356)). Qed.
Lemma lem3860371 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3860372 : term501 = term133.
Proof. exact (@lem3860371 term11). Qed.
Lemma lem3860373 : term508 = term133.
Proof. exact (TRANS (@lem3860369) (@lem3860372)). Qed.
Lemma lem3860374 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3860375 : term510 = term261.
Proof. exact (MK_COMB (@lem3860374) (@lem3860373)). Qed.
Lemma lem3860376 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3860377 : term511 = term263.
Proof. exact (MK_COMB (@lem3860375) (@lem3860376)). Qed.
Lemma lem3860379 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860380 : term263 = term133.
Proof. exact (@lem3860379 term11). Qed.
Lemma lem3860381 : term511 = term133.
Proof. exact (TRANS (@lem3860377) (@lem3860380)). Qed.
Lemma lem3860383 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3860384 : term208 = term209.
Proof. exact (@lem3860383 term11 term11). Qed.
Lemma lem3860385 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860386 : term211 = term11.
Proof. exact (EQ_MP (@lem3860385) (@lem940073)). Qed.
Lemma lem3860387 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860388 : term209 = term143.
Proof. exact (MK_COMB (@lem3860387) (@lem3860386)). Qed.
Lemma lem3860389 : term208 = term143.
Proof. exact (TRANS (@lem3860384) (@lem3860388)). Qed.
Lemma lem3860390 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3860391 : term265 = term263.
Proof. exact (MK_COMB (@lem3860390) (@lem3860389)). Qed.
Lemma lem3860393 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860394 : term263 = term133.
Proof. exact (@lem3860393 term11). Qed.
Lemma lem3860395 : term265 = term133.
Proof. exact (TRANS (@lem3860391) (@lem3860394)). Qed.
Lemma lem3860396 : term133 = term265.
Proof. exact (SYM (@lem3860395)). Qed.
Lemma lem3860397 : term511 = term265.
Proof. exact (TRANS (@lem3860381) (@lem3860396)). Qed.
Lemma lem3860398 : term502 = term196.
Proof. exact (@lem3860348 (@lem3860397)). Qed.
Lemma lem3860399 : term501 = term196.
Proof. exact (TRANS (@lem3860314) (@lem3860398)). Qed.
Lemma lem3860401 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3860402 : term196 = term133.
Proof. exact (@lem3860401 term133). Qed.
Lemma lem3860403 : term501 = term133.
Proof. exact (TRANS (@lem3860399) (@lem3860402)). Qed.
Lemma lem3860404 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3860405 : term512 = term261.
Proof. exact (MK_COMB (@lem3860404) (@lem3860403)). Qed.
Lemma lem3860406 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3860407 (_44750 : int) : (term498 _44750) = (term513 _44750).
Proof. exact (MK_COMB (@lem3860405) (@lem3860406 _44750)). Qed.
Lemma lem3860408 (_44750 : int) : (term517 _44750) = (term513 _44750).
Proof. exact (TRANS (@lem3860305 _44750) (@lem3860407 _44750)). Qed.
Lemma lem3860409 (_44750 : int) : (term513 _44750) = term133.
Proof. exact (@lem1982719 (real_of_int _44750)). Qed.
Lemma lem3860410 (_44750 : int) : (term517 _44750) = term133.
Proof. exact (TRANS (@lem3860408 _44750) (@lem3860409 _44750)). Qed.
Lemma lem3860411 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3860412 (_44750 : int) : (term518 _44750) = term175.
Proof. exact (MK_COMB (@lem3860411) (@lem3860410 _44750)). Qed.
Lemma lem3860413 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3860414 (_44750 : int) : (term516 _44750) = term519.
Proof. exact (MK_COMB (@lem3860412 _44750) (@lem3860413)). Qed.
Lemma lem3860415 (_44750 : int) : (term612 _44750) = term519.
Proof. exact (TRANS (@lem3860304 _44750) (@lem3860414 _44750)). Qed.
Lemma lem3860416 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3860417 (_44750 : int) : (term612 _44750) = term199.
Proof. exact (TRANS (@lem3860415 _44750) (@lem3860416)). Qed.
Lemma lem3860418 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3860419 (_44750 : int) : (term613 _44750) = term521.
Proof. exact (MK_COMB (@lem3860418) (@lem3860417 _44750)). Qed.
Lemma lem3860420 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3860421 (_44750 : int) : (term611 _44750) = term522.
Proof. exact (MK_COMB (@lem3860419 _44750) (@lem3860420)). Qed.
Lemma lem3860422 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : term522.
Proof. exact (EQ_MP (@lem3860421 _44750) (@lem3860303 _44749 _44750 h1)). Qed.
Lemma lem3860424 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3860425 : term522 = term523.
Proof. exact (@lem3860424 term133 term199). Qed.
Lemma lem3860427 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3860428 : term199 = term200.
Proof. exact (@lem3860427 term11). Qed.
Lemma lem3860430 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860431 : term133 = term196.
Proof. exact (@lem3860430 (NUMERAL 0)). Qed.
Lemma lem3860432 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3860433 : term135 = term524.
Proof. exact (MK_COMB (@lem3860432) (@lem3860431)). Qed.
Lemma lem3860434 : term523 = term525.
Proof. exact (MK_COMB (@lem3860433) (@lem3860428)). Qed.
Lemma lem3860435 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3860437 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860438 : term251 = term252.
Proof. exact (@lem3860437 (NUMERAL 0) term11). Qed.
Lemma lem3860439 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860440 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860441 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860440 h1) (fun h1 : term252 = True => @lem3860439)). Qed.
Lemma lem3860442 : term252 = True.
Proof. exact (EQ_MP (@lem3860441) (@lem3860439)). Qed.
Lemma lem3860443 : term251 = True.
Proof. exact (TRANS (@lem3860438) (@lem3860442)). Qed.
Lemma lem3860444 : True = term251.
Proof. exact (SYM (@lem3860443)). Qed.
Lemma lem3860445 : term251.
Proof. exact (EQ_MP (@lem3860444) (@lem0)). Qed.
Lemma lem3860446 : term527.
Proof. exact (@lem3860435 (@lem3860445)). Qed.
Lemma lem3860448 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860449 : term251 = term252.
Proof. exact (@lem3860448 (NUMERAL 0) term11). Qed.
Lemma lem3860450 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860451 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860452 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860451 h1) (fun h1 : term252 = True => @lem3860450)). Qed.
Lemma lem3860453 : term252 = True.
Proof. exact (EQ_MP (@lem3860452) (@lem3860450)). Qed.
Lemma lem3860454 : term251 = True.
Proof. exact (TRANS (@lem3860449) (@lem3860453)). Qed.
Lemma lem3860455 : True = term251.
Proof. exact (SYM (@lem3860454)). Qed.
Lemma lem3860456 : term251.
Proof. exact (EQ_MP (@lem3860455) (@lem0)). Qed.
Lemma lem3860457 : term525 = term528.
Proof. exact (@lem3860446 (@lem3860456)). Qed.
Lemma lem3860459 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3860460 : term225 = term230.
Proof. exact (@lem3860459 term11 term11). Qed.
Lemma lem3860461 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860462 : term211 = term11.
Proof. exact (EQ_MP (@lem3860461) (@lem940073)). Qed.
Lemma lem3860463 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860464 : term209 = term143.
Proof. exact (MK_COMB (@lem3860463) (@lem3860462)). Qed.
Lemma lem3860465 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3860466 : term230 = term199.
Proof. exact (MK_COMB (@lem3860465) (@lem3860464)). Qed.
Lemma lem3860467 : term225 = term199.
Proof. exact (TRANS (@lem3860460) (@lem3860466)). Qed.
Lemma lem3860469 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860470 : term263 = term133.
Proof. exact (@lem3860469 term11). Qed.
Lemma lem3860471 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3860472 : term529 = term135.
Proof. exact (MK_COMB (@lem3860471) (@lem3860470)). Qed.
Lemma lem3860473 : term528 = term523.
Proof. exact (MK_COMB (@lem3860472) (@lem3860467)). Qed.
Lemma lem3860475 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3860476 : term523 = term532.
Proof. exact (@lem3860475 (NUMERAL 0) term11). Qed.
Lemma lem3860477 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860478 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3860479 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860478 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3860477)). Qed.
Lemma lem3860480 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3860479) (@lem3860477)). Qed.
Lemma lem3860481 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3860482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3860483 : term533 = (and True).
Proof. exact (MK_COMB (@lem3860482) (@lem3860481)). Qed.
Lemma lem3860484 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3860483) (@lem3860480)). Qed.
Lemma lem3860486 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3860487 : term532 = False.
Proof. exact (TRANS (@lem3860484) (@lem3860486)). Qed.
Lemma lem3860488 : term523 = False.
Proof. exact (TRANS (@lem3860476) (@lem3860487)). Qed.
Lemma lem3860489 : term528 = False.
Proof. exact (TRANS (@lem3860473) (@lem3860488)). Qed.
Lemma lem3860490 : term525 = False.
Proof. exact (TRANS (@lem3860457) (@lem3860489)). Qed.
Lemma lem3860491 : term523 = False.
Proof. exact (TRANS (@lem3860434) (@lem3860490)). Qed.
Lemma lem3860492 : term522 = False.
Proof. exact (TRANS (@lem3860425) (@lem3860491)). Qed.
Lemma lem3860493 (_44749 : int) (_44750 : int) (h1 : term619 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3860492) (@lem3860422 _44749 _44750 h1)). Qed.
Lemma lem3860494 (_44749 : int) (_44750 : int) (h1 : term441 _44749 _44750) : False.
Proof. exact (or_elim (@lem3859909 _44749 _44750 h1) (fun h0 : term618 _44749 _44750 => @lem3860200 _44749 _44750 h0) (fun h0 : term619 _44749 _44750 => @lem3860493 _44749 _44750 h0)). Qed.
Lemma lem3860495 (_44749 : int) (_44750 : int) (h1 : term450 _44749 _44750) : False.
Proof. exact (or_elim (@lem3859148 _44749 _44750 h1) (fun h0 : term445 _44749 _44750 => @lem3859908 _44749 _44750 h0) (fun h0 : term441 _44749 _44750 => @lem3860494 _44749 _44750 h0)). Qed.
Lemma lem3860496 (_44749 : int) (_44750 : int) (h1 : term437 _44749 _44750) : term437 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3860497 (_44749 : int) (_44750 : int) (h1 : term432 _44749 _44750) : term432 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3860498 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term620 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3860499 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term433 _44749 _44750.
Proof. exact (proj2 (@lem3860498 _44749 _44750 h1)). Qed.
Lemma lem3860501 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term384 _44749 _44750.
Proof. exact (proj2 (@lem3860499 _44749 _44750 h1)). Qed.
Lemma lem3860503 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term335 _44749 _44750.
Proof. exact (proj2 (@lem3860501 _44749 _44750 h1)). Qed.
Lemma lem3860504 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : (term236 _44749 _44750) = term133.
Proof. exact (proj1 (@lem3860501 _44749 _44750 h1)). Qed.
Lemma lem3860506 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term280 _44749 _44750.
Proof. exact (proj1 (@lem3860503 _44749 _44750 h1)). Qed.
Lemma lem3860508 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3860509 : term471 = term251.
Proof. exact (@lem3860508 term133 term143). Qed.
Lemma lem3860511 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860512 : term143 = term224.
Proof. exact (@lem3860511 term11). Qed.
Lemma lem3860514 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860515 : term133 = term196.
Proof. exact (@lem3860514 (NUMERAL 0)). Qed.
Lemma lem3860516 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3860517 : term472 = term473.
Proof. exact (MK_COMB (@lem3860516) (@lem3860515)). Qed.
Lemma lem3860518 : term251 = term474.
Proof. exact (MK_COMB (@lem3860517) (@lem3860512)). Qed.
Lemma lem3860519 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3860521 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860522 : term251 = term252.
Proof. exact (@lem3860521 (NUMERAL 0) term11). Qed.
Lemma lem3860523 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860524 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860525 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860524 h1) (fun h1 : term252 = True => @lem3860523)). Qed.
Lemma lem3860526 : term252 = True.
Proof. exact (EQ_MP (@lem3860525) (@lem3860523)). Qed.
Lemma lem3860527 : term251 = True.
Proof. exact (TRANS (@lem3860522) (@lem3860526)). Qed.
Lemma lem3860528 : True = term251.
Proof. exact (SYM (@lem3860527)). Qed.
Lemma lem3860529 : term251.
Proof. exact (EQ_MP (@lem3860528) (@lem0)). Qed.
Lemma lem3860530 : term476.
Proof. exact (@lem3860519 (@lem3860529)). Qed.
Lemma lem3860532 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860533 : term251 = term252.
Proof. exact (@lem3860532 (NUMERAL 0) term11). Qed.
Lemma lem3860534 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860535 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860536 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860535 h1) (fun h1 : term252 = True => @lem3860534)). Qed.
Lemma lem3860537 : term252 = True.
Proof. exact (EQ_MP (@lem3860536) (@lem3860534)). Qed.
Lemma lem3860538 : term251 = True.
Proof. exact (TRANS (@lem3860533) (@lem3860537)). Qed.
Lemma lem3860539 : True = term251.
Proof. exact (SYM (@lem3860538)). Qed.
Lemma lem3860540 : term251.
Proof. exact (EQ_MP (@lem3860539) (@lem0)). Qed.
Lemma lem3860541 : term474 = term477.
Proof. exact (@lem3860530 (@lem3860540)). Qed.
Lemma lem3860543 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3860544 : term208 = term209.
Proof. exact (@lem3860543 term11 term11). Qed.
Lemma lem3860545 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860546 : term211 = term11.
Proof. exact (EQ_MP (@lem3860545) (@lem940073)). Qed.
Lemma lem3860547 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860548 : term209 = term143.
Proof. exact (MK_COMB (@lem3860547) (@lem3860546)). Qed.
Lemma lem3860549 : term208 = term143.
Proof. exact (TRANS (@lem3860544) (@lem3860548)). Qed.
Lemma lem3860551 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860552 : term263 = term133.
Proof. exact (@lem3860551 term11). Qed.
Lemma lem3860553 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3860554 : term478 = term472.
Proof. exact (MK_COMB (@lem3860553) (@lem3860552)). Qed.
Lemma lem3860555 : term477 = term251.
Proof. exact (MK_COMB (@lem3860554) (@lem3860549)). Qed.
Lemma lem3860557 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860558 : term251 = term252.
Proof. exact (@lem3860557 (NUMERAL 0) term11). Qed.
Lemma lem3860559 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860560 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860561 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860560 h1) (fun h1 : term252 = True => @lem3860559)). Qed.
Lemma lem3860562 : term252 = True.
Proof. exact (EQ_MP (@lem3860561) (@lem3860559)). Qed.
Lemma lem3860563 : term251 = True.
Proof. exact (TRANS (@lem3860558) (@lem3860562)). Qed.
Lemma lem3860564 : term477 = True.
Proof. exact (TRANS (@lem3860555) (@lem3860563)). Qed.
Lemma lem3860565 : term474 = True.
Proof. exact (TRANS (@lem3860541) (@lem3860564)). Qed.
Lemma lem3860566 : term251 = True.
Proof. exact (TRANS (@lem3860518) (@lem3860565)). Qed.
Lemma lem3860567 : term471 = True.
Proof. exact (TRANS (@lem3860509) (@lem3860566)). Qed.
Lemma lem3860568 : True = term471.
Proof. exact (SYM (@lem3860567)). Qed.
Lemma lem3860569 : term471.
Proof. exact (EQ_MP (@lem3860568) (@lem0)). Qed.
Lemma lem3860570 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term479 _44749 _44750.
Proof. exact (conj (@lem3860569) (@lem3860506 _44749 _44750 h1)). Qed.
Lemma lem3860572 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3860573 (_44749 : int) (_44750 : int) : term481 _44749 _44750.
Proof. exact (@lem3860572 term143 (term277 _44749 _44750)). Qed.
Lemma lem3860574 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term482 _44749 _44750.
Proof. exact (@lem3860573 _44749 _44750 (@lem3860570 _44749 _44750 h1)). Qed.
Lemma lem3860575 (_44749 : int) (_44750 : int) : (term483 _44749 _44750) = (term277 _44749 _44750).
Proof. exact (@lem1982733 (term277 _44749 _44750)). Qed.
Lemma lem3860576 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3860577 (_44749 : int) (_44750 : int) : (term484 _44749 _44750) = (term279 _44749 _44750).
Proof. exact (MK_COMB (@lem3860576) (@lem3860575 _44749 _44750)). Qed.
Lemma lem3860578 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3860579 (_44749 : int) (_44750 : int) : (term482 _44749 _44750) = (term280 _44749 _44750).
Proof. exact (MK_COMB (@lem3860577 _44749 _44750) (@lem3860578)). Qed.
Lemma lem3860580 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term280 _44749 _44750.
Proof. exact (EQ_MP (@lem3860579 _44749 _44750) (@lem3860574 _44749 _44750 h1)). Qed.
Lemma lem3860582 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3860583 (_44749 : int) (_44750 : int) : term486 _44749 _44750.
Proof. exact (@lem3860582 (term236 _44749 _44750)). Qed.
Lemma lem3860584 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term487 _44749 _44750.
Proof. exact (@lem3860583 _44749 _44750 (@lem3860504 _44749 _44750 h1)). Qed.
Lemma lem3860585 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term488 _44749 _44750.
Proof. exact (@lem3860584 _44749 _44750 h1 term143). Qed.
Lemma lem3860586 (_44749 : int) (_44750 : int) : (term488 _44749 _44750) = ((term489 _44749 _44750) = term133).
Proof. exact (eq_refl (term488 _44749 _44750)). Qed.
Lemma lem3860587 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : (term489 _44749 _44750) = term133.
Proof. exact (EQ_MP (@lem3860586 _44749 _44750) (@lem3860585 _44749 _44750 h1)). Qed.
Lemma lem3860588 (_44749 : int) (_44750 : int) : (term489 _44749 _44750) = (term236 _44749 _44750).
Proof. exact (@lem1982733 (term236 _44749 _44750)). Qed.
Lemma lem3860589 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3860590 (_44749 : int) (_44750 : int) : (term490 _44749 _44750) = (term239 _44749 _44750).
Proof. exact (MK_COMB (@lem3860589) (@lem3860588 _44749 _44750)). Qed.
Lemma lem3860591 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3860592 (_44749 : int) (_44750 : int) : ((term489 _44749 _44750) = term133) = ((term236 _44749 _44750) = term133).
Proof. exact (MK_COMB (@lem3860590 _44749 _44750) (@lem3860591)). Qed.
Lemma lem3860593 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : (term236 _44749 _44750) = term133.
Proof. exact (EQ_MP (@lem3860592 _44749 _44750) (@lem3860587 _44749 _44750 h1)). Qed.
Lemma lem3860594 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term491 _44749 _44750.
Proof. exact (conj (@lem3860593 _44749 _44750 h1) (@lem3860580 _44749 _44750 h1)). Qed.
Lemma lem3860596 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3860597 (_44749 : int) (_44750 : int) : term493 _44749 _44750.
Proof. exact (@lem3860596 (term236 _44749 _44750) (term277 _44749 _44750)). Qed.
Lemma lem3860598 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term494 _44749 _44750.
Proof. exact (@lem3860597 _44749 _44750 (@lem3860594 _44749 _44750 h1)). Qed.
Lemma lem3860599 (_44749 : int) (_44750 : int) : (term495 _44749 _44750) = (term496 _44749 _44750).
Proof. exact (@lem1982753 (term237 _44749) (real_of_int _44749) (term299 _44750) (term237 _44750)). Qed.
Lemma lem3860600 (_44749 : int) : (term497 _44749) = (term498 _44749).
Proof. exact (@lem1982713 term199 (real_of_int _44749)). Qed.
Lemma lem3860602 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860603 : term143 = term224.
Proof. exact (@lem3860602 term11). Qed.
Lemma lem3860605 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3860606 : term199 = term200.
Proof. exact (@lem3860605 term11). Qed.
Lemma lem3860607 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3860608 : term499 = term500.
Proof. exact (MK_COMB (@lem3860607) (@lem3860606)). Qed.
Lemma lem3860609 : term501 = term502.
Proof. exact (MK_COMB (@lem3860608) (@lem3860603)). Qed.
Lemma lem3860610 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3860612 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860613 : term251 = term252.
Proof. exact (@lem3860612 (NUMERAL 0) term11). Qed.
Lemma lem3860614 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860615 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860616 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860615 h1) (fun h1 : term252 = True => @lem3860614)). Qed.
Lemma lem3860617 : term252 = True.
Proof. exact (EQ_MP (@lem3860616) (@lem3860614)). Qed.
Lemma lem3860618 : term251 = True.
Proof. exact (TRANS (@lem3860613) (@lem3860617)). Qed.
Lemma lem3860619 : True = term251.
Proof. exact (SYM (@lem3860618)). Qed.
Lemma lem3860620 : term251.
Proof. exact (EQ_MP (@lem3860619) (@lem0)). Qed.
Lemma lem3860621 : term504.
Proof. exact (@lem3860610 (@lem3860620)). Qed.
Lemma lem3860623 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860624 : term251 = term252.
Proof. exact (@lem3860623 (NUMERAL 0) term11). Qed.
Lemma lem3860625 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860626 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860627 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860626 h1) (fun h1 : term252 = True => @lem3860625)). Qed.
Lemma lem3860628 : term252 = True.
Proof. exact (EQ_MP (@lem3860627) (@lem3860625)). Qed.
Lemma lem3860629 : term251 = True.
Proof. exact (TRANS (@lem3860624) (@lem3860628)). Qed.
Lemma lem3860630 : True = term251.
Proof. exact (SYM (@lem3860629)). Qed.
Lemma lem3860631 : term251.
Proof. exact (EQ_MP (@lem3860630) (@lem0)). Qed.
Lemma lem3860632 : term505.
Proof. exact (@lem3860621 (@lem3860631)). Qed.
Lemma lem3860634 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860635 : term251 = term252.
Proof. exact (@lem3860634 (NUMERAL 0) term11). Qed.
Lemma lem3860636 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860637 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860638 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860637 h1) (fun h1 : term252 = True => @lem3860636)). Qed.
Lemma lem3860639 : term252 = True.
Proof. exact (EQ_MP (@lem3860638) (@lem3860636)). Qed.
Lemma lem3860640 : term251 = True.
Proof. exact (TRANS (@lem3860635) (@lem3860639)). Qed.
Lemma lem3860641 : True = term251.
Proof. exact (SYM (@lem3860640)). Qed.
Lemma lem3860642 : term251.
Proof. exact (EQ_MP (@lem3860641) (@lem0)). Qed.
Lemma lem3860643 : term506.
Proof. exact (@lem3860632 (@lem3860642)). Qed.
Lemma lem3860645 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3860646 : term208 = term209.
Proof. exact (@lem3860645 term11 term11). Qed.
Lemma lem3860647 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860648 : term211 = term11.
Proof. exact (EQ_MP (@lem3860647) (@lem940073)). Qed.
Lemma lem3860649 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860650 : term209 = term143.
Proof. exact (MK_COMB (@lem3860649) (@lem3860648)). Qed.
Lemma lem3860651 : term208 = term143.
Proof. exact (TRANS (@lem3860646) (@lem3860650)). Qed.
Lemma lem3860653 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3860654 : term225 = term230.
Proof. exact (@lem3860653 term11 term11). Qed.
Lemma lem3860655 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860656 : term211 = term11.
Proof. exact (EQ_MP (@lem3860655) (@lem940073)). Qed.
Lemma lem3860657 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860658 : term209 = term143.
Proof. exact (MK_COMB (@lem3860657) (@lem3860656)). Qed.
Lemma lem3860659 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3860660 : term230 = term199.
Proof. exact (MK_COMB (@lem3860659) (@lem3860658)). Qed.
Lemma lem3860661 : term225 = term199.
Proof. exact (TRANS (@lem3860654) (@lem3860660)). Qed.
Lemma lem3860662 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3860663 : term507 = term499.
Proof. exact (MK_COMB (@lem3860662) (@lem3860661)). Qed.
Lemma lem3860664 : term508 = term501.
Proof. exact (MK_COMB (@lem3860663) (@lem3860651)). Qed.
Lemma lem3860666 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3860667 : term501 = term133.
Proof. exact (@lem3860666 term11). Qed.
Lemma lem3860668 : term508 = term133.
Proof. exact (TRANS (@lem3860664) (@lem3860667)). Qed.
Lemma lem3860669 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3860670 : term510 = term261.
Proof. exact (MK_COMB (@lem3860669) (@lem3860668)). Qed.
Lemma lem3860671 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3860672 : term511 = term263.
Proof. exact (MK_COMB (@lem3860670) (@lem3860671)). Qed.
Lemma lem3860674 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860675 : term263 = term133.
Proof. exact (@lem3860674 term11). Qed.
Lemma lem3860676 : term511 = term133.
Proof. exact (TRANS (@lem3860672) (@lem3860675)). Qed.
Lemma lem3860678 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3860679 : term208 = term209.
Proof. exact (@lem3860678 term11 term11). Qed.
Lemma lem3860680 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860681 : term211 = term11.
Proof. exact (EQ_MP (@lem3860680) (@lem940073)). Qed.
Lemma lem3860682 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860683 : term209 = term143.
Proof. exact (MK_COMB (@lem3860682) (@lem3860681)). Qed.
Lemma lem3860684 : term208 = term143.
Proof. exact (TRANS (@lem3860679) (@lem3860683)). Qed.
Lemma lem3860685 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3860686 : term265 = term263.
Proof. exact (MK_COMB (@lem3860685) (@lem3860684)). Qed.
Lemma lem3860688 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860689 : term263 = term133.
Proof. exact (@lem3860688 term11). Qed.
Lemma lem3860690 : term265 = term133.
Proof. exact (TRANS (@lem3860686) (@lem3860689)). Qed.
Lemma lem3860691 : term133 = term265.
Proof. exact (SYM (@lem3860690)). Qed.
Lemma lem3860692 : term511 = term265.
Proof. exact (TRANS (@lem3860676) (@lem3860691)). Qed.
Lemma lem3860693 : term502 = term196.
Proof. exact (@lem3860643 (@lem3860692)). Qed.
Lemma lem3860694 : term501 = term196.
Proof. exact (TRANS (@lem3860609) (@lem3860693)). Qed.
Lemma lem3860696 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3860697 : term196 = term133.
Proof. exact (@lem3860696 term133). Qed.
Lemma lem3860698 : term501 = term133.
Proof. exact (TRANS (@lem3860694) (@lem3860697)). Qed.
Lemma lem3860699 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3860700 : term512 = term261.
Proof. exact (MK_COMB (@lem3860699) (@lem3860698)). Qed.
Lemma lem3860701 (_44749 : int) : (real_of_int _44749) = (real_of_int _44749).
Proof. exact (eq_refl (real_of_int _44749)). Qed.
Lemma lem3860702 (_44749 : int) : (term498 _44749) = (term513 _44749).
Proof. exact (MK_COMB (@lem3860700) (@lem3860701 _44749)). Qed.
Lemma lem3860703 (_44749 : int) : (term497 _44749) = (term513 _44749).
Proof. exact (TRANS (@lem3860600 _44749) (@lem3860702 _44749)). Qed.
Lemma lem3860704 (_44749 : int) : (term513 _44749) = term133.
Proof. exact (@lem1982719 (real_of_int _44749)). Qed.
Lemma lem3860705 (_44749 : int) : (term497 _44749) = term133.
Proof. exact (TRANS (@lem3860703 _44749) (@lem3860704 _44749)). Qed.
Lemma lem3860706 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3860707 (_44749 : int) : (term514 _44749) = term175.
Proof. exact (MK_COMB (@lem3860706) (@lem3860705 _44749)). Qed.
Lemma lem3860708 (_44750 : int) : (term515 _44750) = (term516 _44750).
Proof. exact (@lem1982759 (real_of_int _44750) (term237 _44750) term199). Qed.
Lemma lem3860709 (_44750 : int) : (term517 _44750) = (term498 _44750).
Proof. exact (@lem1982715 term199 (real_of_int _44750)). Qed.
Lemma lem3860711 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860712 : term143 = term224.
Proof. exact (@lem3860711 term11). Qed.
Lemma lem3860714 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3860715 : term199 = term200.
Proof. exact (@lem3860714 term11). Qed.
Lemma lem3860716 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3860717 : term499 = term500.
Proof. exact (MK_COMB (@lem3860716) (@lem3860715)). Qed.
Lemma lem3860718 : term501 = term502.
Proof. exact (MK_COMB (@lem3860717) (@lem3860712)). Qed.
Lemma lem3860719 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3860721 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860722 : term251 = term252.
Proof. exact (@lem3860721 (NUMERAL 0) term11). Qed.
Lemma lem3860723 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860724 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860725 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860724 h1) (fun h1 : term252 = True => @lem3860723)). Qed.
Lemma lem3860726 : term252 = True.
Proof. exact (EQ_MP (@lem3860725) (@lem3860723)). Qed.
Lemma lem3860727 : term251 = True.
Proof. exact (TRANS (@lem3860722) (@lem3860726)). Qed.
Lemma lem3860728 : True = term251.
Proof. exact (SYM (@lem3860727)). Qed.
Lemma lem3860729 : term251.
Proof. exact (EQ_MP (@lem3860728) (@lem0)). Qed.
Lemma lem3860730 : term504.
Proof. exact (@lem3860719 (@lem3860729)). Qed.
Lemma lem3860732 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860733 : term251 = term252.
Proof. exact (@lem3860732 (NUMERAL 0) term11). Qed.
Lemma lem3860734 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860735 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860736 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860735 h1) (fun h1 : term252 = True => @lem3860734)). Qed.
Lemma lem3860737 : term252 = True.
Proof. exact (EQ_MP (@lem3860736) (@lem3860734)). Qed.
Lemma lem3860738 : term251 = True.
Proof. exact (TRANS (@lem3860733) (@lem3860737)). Qed.
Lemma lem3860739 : True = term251.
Proof. exact (SYM (@lem3860738)). Qed.
Lemma lem3860740 : term251.
Proof. exact (EQ_MP (@lem3860739) (@lem0)). Qed.
Lemma lem3860741 : term505.
Proof. exact (@lem3860730 (@lem3860740)). Qed.
Lemma lem3860743 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860744 : term251 = term252.
Proof. exact (@lem3860743 (NUMERAL 0) term11). Qed.
Lemma lem3860745 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860746 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860747 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860746 h1) (fun h1 : term252 = True => @lem3860745)). Qed.
Lemma lem3860748 : term252 = True.
Proof. exact (EQ_MP (@lem3860747) (@lem3860745)). Qed.
Lemma lem3860749 : term251 = True.
Proof. exact (TRANS (@lem3860744) (@lem3860748)). Qed.
Lemma lem3860750 : True = term251.
Proof. exact (SYM (@lem3860749)). Qed.
Lemma lem3860751 : term251.
Proof. exact (EQ_MP (@lem3860750) (@lem0)). Qed.
Lemma lem3860752 : term506.
Proof. exact (@lem3860741 (@lem3860751)). Qed.
Lemma lem3860754 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3860755 : term208 = term209.
Proof. exact (@lem3860754 term11 term11). Qed.
Lemma lem3860756 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860757 : term211 = term11.
Proof. exact (EQ_MP (@lem3860756) (@lem940073)). Qed.
Lemma lem3860758 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860759 : term209 = term143.
Proof. exact (MK_COMB (@lem3860758) (@lem3860757)). Qed.
Lemma lem3860760 : term208 = term143.
Proof. exact (TRANS (@lem3860755) (@lem3860759)). Qed.
Lemma lem3860762 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3860763 : term225 = term230.
Proof. exact (@lem3860762 term11 term11). Qed.
Lemma lem3860764 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860765 : term211 = term11.
Proof. exact (EQ_MP (@lem3860764) (@lem940073)). Qed.
Lemma lem3860766 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860767 : term209 = term143.
Proof. exact (MK_COMB (@lem3860766) (@lem3860765)). Qed.
Lemma lem3860768 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3860769 : term230 = term199.
Proof. exact (MK_COMB (@lem3860768) (@lem3860767)). Qed.
Lemma lem3860770 : term225 = term199.
Proof. exact (TRANS (@lem3860763) (@lem3860769)). Qed.
Lemma lem3860771 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3860772 : term507 = term499.
Proof. exact (MK_COMB (@lem3860771) (@lem3860770)). Qed.
Lemma lem3860773 : term508 = term501.
Proof. exact (MK_COMB (@lem3860772) (@lem3860760)). Qed.
Lemma lem3860775 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3860776 : term501 = term133.
Proof. exact (@lem3860775 term11). Qed.
Lemma lem3860777 : term508 = term133.
Proof. exact (TRANS (@lem3860773) (@lem3860776)). Qed.
Lemma lem3860778 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3860779 : term510 = term261.
Proof. exact (MK_COMB (@lem3860778) (@lem3860777)). Qed.
Lemma lem3860780 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3860781 : term511 = term263.
Proof. exact (MK_COMB (@lem3860779) (@lem3860780)). Qed.
Lemma lem3860783 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860784 : term263 = term133.
Proof. exact (@lem3860783 term11). Qed.
Lemma lem3860785 : term511 = term133.
Proof. exact (TRANS (@lem3860781) (@lem3860784)). Qed.
Lemma lem3860787 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3860788 : term208 = term209.
Proof. exact (@lem3860787 term11 term11). Qed.
Lemma lem3860789 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860790 : term211 = term11.
Proof. exact (EQ_MP (@lem3860789) (@lem940073)). Qed.
Lemma lem3860791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860792 : term209 = term143.
Proof. exact (MK_COMB (@lem3860791) (@lem3860790)). Qed.
Lemma lem3860793 : term208 = term143.
Proof. exact (TRANS (@lem3860788) (@lem3860792)). Qed.
Lemma lem3860794 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3860795 : term265 = term263.
Proof. exact (MK_COMB (@lem3860794) (@lem3860793)). Qed.
Lemma lem3860797 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860798 : term263 = term133.
Proof. exact (@lem3860797 term11). Qed.
Lemma lem3860799 : term265 = term133.
Proof. exact (TRANS (@lem3860795) (@lem3860798)). Qed.
Lemma lem3860800 : term133 = term265.
Proof. exact (SYM (@lem3860799)). Qed.
Lemma lem3860801 : term511 = term265.
Proof. exact (TRANS (@lem3860785) (@lem3860800)). Qed.
Lemma lem3860802 : term502 = term196.
Proof. exact (@lem3860752 (@lem3860801)). Qed.
Lemma lem3860803 : term501 = term196.
Proof. exact (TRANS (@lem3860718) (@lem3860802)). Qed.
Lemma lem3860805 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3860806 : term196 = term133.
Proof. exact (@lem3860805 term133). Qed.
Lemma lem3860807 : term501 = term133.
Proof. exact (TRANS (@lem3860803) (@lem3860806)). Qed.
Lemma lem3860808 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3860809 : term512 = term261.
Proof. exact (MK_COMB (@lem3860808) (@lem3860807)). Qed.
Lemma lem3860810 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3860811 (_44750 : int) : (term498 _44750) = (term513 _44750).
Proof. exact (MK_COMB (@lem3860809) (@lem3860810 _44750)). Qed.
Lemma lem3860812 (_44750 : int) : (term517 _44750) = (term513 _44750).
Proof. exact (TRANS (@lem3860709 _44750) (@lem3860811 _44750)). Qed.
Lemma lem3860813 (_44750 : int) : (term513 _44750) = term133.
Proof. exact (@lem1982719 (real_of_int _44750)). Qed.
Lemma lem3860814 (_44750 : int) : (term517 _44750) = term133.
Proof. exact (TRANS (@lem3860812 _44750) (@lem3860813 _44750)). Qed.
Lemma lem3860815 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3860816 (_44750 : int) : (term518 _44750) = term175.
Proof. exact (MK_COMB (@lem3860815) (@lem3860814 _44750)). Qed.
Lemma lem3860817 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3860818 (_44750 : int) : (term516 _44750) = term519.
Proof. exact (MK_COMB (@lem3860816 _44750) (@lem3860817)). Qed.
Lemma lem3860819 (_44750 : int) : (term515 _44750) = term519.
Proof. exact (TRANS (@lem3860708 _44750) (@lem3860818 _44750)). Qed.
Lemma lem3860820 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3860821 (_44750 : int) : (term515 _44750) = term199.
Proof. exact (TRANS (@lem3860819 _44750) (@lem3860820)). Qed.
Lemma lem3860822 (_44749 : int) (_44750 : int) : (term496 _44749 _44750) = term519.
Proof. exact (MK_COMB (@lem3860707 _44749) (@lem3860821 _44750)). Qed.
Lemma lem3860823 (_44749 : int) (_44750 : int) : (term495 _44749 _44750) = term519.
Proof. exact (TRANS (@lem3860599 _44749 _44750) (@lem3860822 _44749 _44750)). Qed.
Lemma lem3860824 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3860825 (_44749 : int) (_44750 : int) : (term495 _44749 _44750) = term199.
Proof. exact (TRANS (@lem3860823 _44749 _44750) (@lem3860824)). Qed.
Lemma lem3860826 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3860827 (_44749 : int) (_44750 : int) : (term520 _44749 _44750) = term521.
Proof. exact (MK_COMB (@lem3860826) (@lem3860825 _44749 _44750)). Qed.
Lemma lem3860828 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3860829 (_44749 : int) (_44750 : int) : (term494 _44749 _44750) = term522.
Proof. exact (MK_COMB (@lem3860827 _44749 _44750) (@lem3860828)). Qed.
Lemma lem3860830 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : term522.
Proof. exact (EQ_MP (@lem3860829 _44749 _44750) (@lem3860598 _44749 _44750 h1)). Qed.
Lemma lem3860832 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3860833 : term522 = term523.
Proof. exact (@lem3860832 term133 term199). Qed.
Lemma lem3860835 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3860836 : term199 = term200.
Proof. exact (@lem3860835 term11). Qed.
Lemma lem3860838 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860839 : term133 = term196.
Proof. exact (@lem3860838 (NUMERAL 0)). Qed.
Lemma lem3860840 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3860841 : term135 = term524.
Proof. exact (MK_COMB (@lem3860840) (@lem3860839)). Qed.
Lemma lem3860842 : term523 = term525.
Proof. exact (MK_COMB (@lem3860841) (@lem3860836)). Qed.
Lemma lem3860843 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3860845 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860846 : term251 = term252.
Proof. exact (@lem3860845 (NUMERAL 0) term11). Qed.
Lemma lem3860847 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860848 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860849 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860848 h1) (fun h1 : term252 = True => @lem3860847)). Qed.
Lemma lem3860850 : term252 = True.
Proof. exact (EQ_MP (@lem3860849) (@lem3860847)). Qed.
Lemma lem3860851 : term251 = True.
Proof. exact (TRANS (@lem3860846) (@lem3860850)). Qed.
Lemma lem3860852 : True = term251.
Proof. exact (SYM (@lem3860851)). Qed.
Lemma lem3860853 : term251.
Proof. exact (EQ_MP (@lem3860852) (@lem0)). Qed.
Lemma lem3860854 : term527.
Proof. exact (@lem3860843 (@lem3860853)). Qed.
Lemma lem3860856 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860857 : term251 = term252.
Proof. exact (@lem3860856 (NUMERAL 0) term11). Qed.
Lemma lem3860858 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860859 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860860 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860859 h1) (fun h1 : term252 = True => @lem3860858)). Qed.
Lemma lem3860861 : term252 = True.
Proof. exact (EQ_MP (@lem3860860) (@lem3860858)). Qed.
Lemma lem3860862 : term251 = True.
Proof. exact (TRANS (@lem3860857) (@lem3860861)). Qed.
Lemma lem3860863 : True = term251.
Proof. exact (SYM (@lem3860862)). Qed.
Lemma lem3860864 : term251.
Proof. exact (EQ_MP (@lem3860863) (@lem0)). Qed.
Lemma lem3860865 : term525 = term528.
Proof. exact (@lem3860854 (@lem3860864)). Qed.
Lemma lem3860867 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3860868 : term225 = term230.
Proof. exact (@lem3860867 term11 term11). Qed.
Lemma lem3860869 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860870 : term211 = term11.
Proof. exact (EQ_MP (@lem3860869) (@lem940073)). Qed.
Lemma lem3860871 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860872 : term209 = term143.
Proof. exact (MK_COMB (@lem3860871) (@lem3860870)). Qed.
Lemma lem3860873 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3860874 : term230 = term199.
Proof. exact (MK_COMB (@lem3860873) (@lem3860872)). Qed.
Lemma lem3860875 : term225 = term199.
Proof. exact (TRANS (@lem3860868) (@lem3860874)). Qed.
Lemma lem3860877 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860878 : term263 = term133.
Proof. exact (@lem3860877 term11). Qed.
Lemma lem3860879 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3860880 : term529 = term135.
Proof. exact (MK_COMB (@lem3860879) (@lem3860878)). Qed.
Lemma lem3860881 : term528 = term523.
Proof. exact (MK_COMB (@lem3860880) (@lem3860875)). Qed.
Lemma lem3860883 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3860884 : term523 = term532.
Proof. exact (@lem3860883 (NUMERAL 0) term11). Qed.
Lemma lem3860885 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860886 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3860887 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860886 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3860885)). Qed.
Lemma lem3860888 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3860887) (@lem3860885)). Qed.
Lemma lem3860889 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3860890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3860891 : term533 = (and True).
Proof. exact (MK_COMB (@lem3860890) (@lem3860889)). Qed.
Lemma lem3860892 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3860891) (@lem3860888)). Qed.
Lemma lem3860894 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3860895 : term532 = False.
Proof. exact (TRANS (@lem3860892) (@lem3860894)). Qed.
Lemma lem3860896 : term523 = False.
Proof. exact (TRANS (@lem3860884) (@lem3860895)). Qed.
Lemma lem3860897 : term528 = False.
Proof. exact (TRANS (@lem3860881) (@lem3860896)). Qed.
Lemma lem3860898 : term525 = False.
Proof. exact (TRANS (@lem3860865) (@lem3860897)). Qed.
Lemma lem3860899 : term523 = False.
Proof. exact (TRANS (@lem3860842) (@lem3860898)). Qed.
Lemma lem3860900 : term522 = False.
Proof. exact (TRANS (@lem3860833) (@lem3860899)). Qed.
Lemma lem3860901 (_44749 : int) (_44750 : int) (h1 : term620 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3860900) (@lem3860830 _44749 _44750 h1)). Qed.
Lemma lem3860902 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term621 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3860903 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term434 _44749 _44750.
Proof. exact (proj2 (@lem3860902 _44749 _44750 h1)). Qed.
Lemma lem3860905 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term385 _44749 _44750.
Proof. exact (proj2 (@lem3860903 _44749 _44750 h1)). Qed.
Lemma lem3860907 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term335 _44749 _44750.
Proof. exact (proj2 (@lem3860905 _44749 _44750 h1)). Qed.
Lemma lem3860908 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term272 _44750 _44749.
Proof. exact (proj1 (@lem3860905 _44749 _44750 h1)). Qed.
Lemma lem3860909 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : (real_of_int _44749) = term133.
Proof. exact (proj2 (@lem3860908 _44749 _44750 h1)). Qed.
Lemma lem3860911 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term302 _44750.
Proof. exact (proj2 (@lem3860907 _44749 _44750 h1)). Qed.
Lemma lem3860912 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term280 _44749 _44750.
Proof. exact (proj1 (@lem3860907 _44749 _44750 h1)). Qed.
Lemma lem3860914 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3860915 : term471 = term251.
Proof. exact (@lem3860914 term133 term143). Qed.
Lemma lem3860917 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860918 : term143 = term224.
Proof. exact (@lem3860917 term11). Qed.
Lemma lem3860920 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860921 : term133 = term196.
Proof. exact (@lem3860920 (NUMERAL 0)). Qed.
Lemma lem3860922 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3860923 : term472 = term473.
Proof. exact (MK_COMB (@lem3860922) (@lem3860921)). Qed.
Lemma lem3860924 : term251 = term474.
Proof. exact (MK_COMB (@lem3860923) (@lem3860918)). Qed.
Lemma lem3860925 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3860927 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860928 : term251 = term252.
Proof. exact (@lem3860927 (NUMERAL 0) term11). Qed.
Lemma lem3860929 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860930 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860931 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860930 h1) (fun h1 : term252 = True => @lem3860929)). Qed.
Lemma lem3860932 : term252 = True.
Proof. exact (EQ_MP (@lem3860931) (@lem3860929)). Qed.
Lemma lem3860933 : term251 = True.
Proof. exact (TRANS (@lem3860928) (@lem3860932)). Qed.
Lemma lem3860934 : True = term251.
Proof. exact (SYM (@lem3860933)). Qed.
Lemma lem3860935 : term251.
Proof. exact (EQ_MP (@lem3860934) (@lem0)). Qed.
Lemma lem3860936 : term476.
Proof. exact (@lem3860925 (@lem3860935)). Qed.
Lemma lem3860938 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860939 : term251 = term252.
Proof. exact (@lem3860938 (NUMERAL 0) term11). Qed.
Lemma lem3860940 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860941 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860942 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860941 h1) (fun h1 : term252 = True => @lem3860940)). Qed.
Lemma lem3860943 : term252 = True.
Proof. exact (EQ_MP (@lem3860942) (@lem3860940)). Qed.
Lemma lem3860944 : term251 = True.
Proof. exact (TRANS (@lem3860939) (@lem3860943)). Qed.
Lemma lem3860945 : True = term251.
Proof. exact (SYM (@lem3860944)). Qed.
Lemma lem3860946 : term251.
Proof. exact (EQ_MP (@lem3860945) (@lem0)). Qed.
Lemma lem3860947 : term474 = term477.
Proof. exact (@lem3860936 (@lem3860946)). Qed.
Lemma lem3860949 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3860950 : term208 = term209.
Proof. exact (@lem3860949 term11 term11). Qed.
Lemma lem3860951 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3860952 : term211 = term11.
Proof. exact (EQ_MP (@lem3860951) (@lem940073)). Qed.
Lemma lem3860953 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3860954 : term209 = term143.
Proof. exact (MK_COMB (@lem3860953) (@lem3860952)). Qed.
Lemma lem3860955 : term208 = term143.
Proof. exact (TRANS (@lem3860950) (@lem3860954)). Qed.
Lemma lem3860957 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3860958 : term263 = term133.
Proof. exact (@lem3860957 term11). Qed.
Lemma lem3860959 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3860960 : term478 = term472.
Proof. exact (MK_COMB (@lem3860959) (@lem3860958)). Qed.
Lemma lem3860961 : term477 = term251.
Proof. exact (MK_COMB (@lem3860960) (@lem3860955)). Qed.
Lemma lem3860963 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3860964 : term251 = term252.
Proof. exact (@lem3860963 (NUMERAL 0) term11). Qed.
Lemma lem3860965 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3860966 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3860967 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3860966 h1) (fun h1 : term252 = True => @lem3860965)). Qed.
Lemma lem3860968 : term252 = True.
Proof. exact (EQ_MP (@lem3860967) (@lem3860965)). Qed.
Lemma lem3860969 : term251 = True.
Proof. exact (TRANS (@lem3860964) (@lem3860968)). Qed.
Lemma lem3860970 : term477 = True.
Proof. exact (TRANS (@lem3860961) (@lem3860969)). Qed.
Lemma lem3860971 : term474 = True.
Proof. exact (TRANS (@lem3860947) (@lem3860970)). Qed.
Lemma lem3860972 : term251 = True.
Proof. exact (TRANS (@lem3860924) (@lem3860971)). Qed.
Lemma lem3860973 : term471 = True.
Proof. exact (TRANS (@lem3860915) (@lem3860972)). Qed.
Lemma lem3860974 : True = term471.
Proof. exact (SYM (@lem3860973)). Qed.
Lemma lem3860975 : term471.
Proof. exact (EQ_MP (@lem3860974) (@lem0)). Qed.
Lemma lem3860976 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term551 _44750.
Proof. exact (conj (@lem3860975) (@lem3860911 _44749 _44750 h1)). Qed.
Lemma lem3860978 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3860979 (_44750 : int) : term552 _44750.
Proof. exact (@lem3860978 term143 (term299 _44750)). Qed.
Lemma lem3860980 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term553 _44750.
Proof. exact (@lem3860979 _44750 (@lem3860976 _44749 _44750 h1)). Qed.
Lemma lem3860981 (_44750 : int) : (term554 _44750) = (term299 _44750).
Proof. exact (@lem1982733 (term299 _44750)). Qed.
Lemma lem3860982 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3860983 (_44750 : int) : (term555 _44750) = (term301 _44750).
Proof. exact (MK_COMB (@lem3860982) (@lem3860981 _44750)). Qed.
Lemma lem3860984 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3860985 (_44750 : int) : (term553 _44750) = (term302 _44750).
Proof. exact (MK_COMB (@lem3860983 _44750) (@lem3860984)). Qed.
Lemma lem3860986 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term302 _44750.
Proof. exact (EQ_MP (@lem3860985 _44750) (@lem3860980 _44749 _44750 h1)). Qed.
Lemma lem3860988 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3860989 : term471 = term251.
Proof. exact (@lem3860988 term133 term143). Qed.
Lemma lem3860991 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860992 : term143 = term224.
Proof. exact (@lem3860991 term11). Qed.
Lemma lem3860994 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3860995 : term133 = term196.
Proof. exact (@lem3860994 (NUMERAL 0)). Qed.
Lemma lem3860996 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3860997 : term472 = term473.
Proof. exact (MK_COMB (@lem3860996) (@lem3860995)). Qed.
Lemma lem3860998 : term251 = term474.
Proof. exact (MK_COMB (@lem3860997) (@lem3860992)). Qed.
Lemma lem3860999 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3861001 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861002 : term251 = term252.
Proof. exact (@lem3861001 (NUMERAL 0) term11). Qed.
Lemma lem3861003 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861004 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861005 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861004 h1) (fun h1 : term252 = True => @lem3861003)). Qed.
Lemma lem3861006 : term252 = True.
Proof. exact (EQ_MP (@lem3861005) (@lem3861003)). Qed.
Lemma lem3861007 : term251 = True.
Proof. exact (TRANS (@lem3861002) (@lem3861006)). Qed.
Lemma lem3861008 : True = term251.
Proof. exact (SYM (@lem3861007)). Qed.
Lemma lem3861009 : term251.
Proof. exact (EQ_MP (@lem3861008) (@lem0)). Qed.
Lemma lem3861010 : term476.
Proof. exact (@lem3860999 (@lem3861009)). Qed.
Lemma lem3861012 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861013 : term251 = term252.
Proof. exact (@lem3861012 (NUMERAL 0) term11). Qed.
Lemma lem3861014 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861015 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861016 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861015 h1) (fun h1 : term252 = True => @lem3861014)). Qed.
Lemma lem3861017 : term252 = True.
Proof. exact (EQ_MP (@lem3861016) (@lem3861014)). Qed.
Lemma lem3861018 : term251 = True.
Proof. exact (TRANS (@lem3861013) (@lem3861017)). Qed.
Lemma lem3861019 : True = term251.
Proof. exact (SYM (@lem3861018)). Qed.
Lemma lem3861020 : term251.
Proof. exact (EQ_MP (@lem3861019) (@lem0)). Qed.
Lemma lem3861021 : term474 = term477.
Proof. exact (@lem3861010 (@lem3861020)). Qed.
Lemma lem3861023 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3861024 : term208 = term209.
Proof. exact (@lem3861023 term11 term11). Qed.
Lemma lem3861025 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861026 : term211 = term11.
Proof. exact (EQ_MP (@lem3861025) (@lem940073)). Qed.
Lemma lem3861027 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861028 : term209 = term143.
Proof. exact (MK_COMB (@lem3861027) (@lem3861026)). Qed.
Lemma lem3861029 : term208 = term143.
Proof. exact (TRANS (@lem3861024) (@lem3861028)). Qed.
Lemma lem3861031 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861032 : term263 = term133.
Proof. exact (@lem3861031 term11). Qed.
Lemma lem3861033 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3861034 : term478 = term472.
Proof. exact (MK_COMB (@lem3861033) (@lem3861032)). Qed.
Lemma lem3861035 : term477 = term251.
Proof. exact (MK_COMB (@lem3861034) (@lem3861029)). Qed.
Lemma lem3861037 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861038 : term251 = term252.
Proof. exact (@lem3861037 (NUMERAL 0) term11). Qed.
Lemma lem3861039 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861040 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861041 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861040 h1) (fun h1 : term252 = True => @lem3861039)). Qed.
Lemma lem3861042 : term252 = True.
Proof. exact (EQ_MP (@lem3861041) (@lem3861039)). Qed.
Lemma lem3861043 : term251 = True.
Proof. exact (TRANS (@lem3861038) (@lem3861042)). Qed.
Lemma lem3861044 : term477 = True.
Proof. exact (TRANS (@lem3861035) (@lem3861043)). Qed.
Lemma lem3861045 : term474 = True.
Proof. exact (TRANS (@lem3861021) (@lem3861044)). Qed.
Lemma lem3861046 : term251 = True.
Proof. exact (TRANS (@lem3860998) (@lem3861045)). Qed.
Lemma lem3861047 : term471 = True.
Proof. exact (TRANS (@lem3860989) (@lem3861046)). Qed.
Lemma lem3861048 : True = term471.
Proof. exact (SYM (@lem3861047)). Qed.
Lemma lem3861049 : term471.
Proof. exact (EQ_MP (@lem3861048) (@lem0)). Qed.
Lemma lem3861050 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term479 _44749 _44750.
Proof. exact (conj (@lem3861049) (@lem3860912 _44749 _44750 h1)). Qed.
Lemma lem3861052 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3861053 (_44749 : int) (_44750 : int) : term481 _44749 _44750.
Proof. exact (@lem3861052 term143 (term277 _44749 _44750)). Qed.
Lemma lem3861054 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term482 _44749 _44750.
Proof. exact (@lem3861053 _44749 _44750 (@lem3861050 _44749 _44750 h1)). Qed.
Lemma lem3861055 (_44749 : int) (_44750 : int) : (term483 _44749 _44750) = (term277 _44749 _44750).
Proof. exact (@lem1982733 (term277 _44749 _44750)). Qed.
Lemma lem3861056 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3861057 (_44749 : int) (_44750 : int) : (term484 _44749 _44750) = (term279 _44749 _44750).
Proof. exact (MK_COMB (@lem3861056) (@lem3861055 _44749 _44750)). Qed.
Lemma lem3861058 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3861059 (_44749 : int) (_44750 : int) : (term482 _44749 _44750) = (term280 _44749 _44750).
Proof. exact (MK_COMB (@lem3861057 _44749 _44750) (@lem3861058)). Qed.
Lemma lem3861060 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term280 _44749 _44750.
Proof. exact (EQ_MP (@lem3861059 _44749 _44750) (@lem3861054 _44749 _44750 h1)). Qed.
Lemma lem3861062 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3861063 (_44749 : int) : term539 _44749.
Proof. exact (@lem3861062 (real_of_int _44749)). Qed.
Lemma lem3861064 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term540 _44749.
Proof. exact (@lem3861063 _44749 (@lem3860909 _44749 _44750 h1)). Qed.
Lemma lem3861065 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term556 _44749.
Proof. exact (@lem3861064 _44749 _44750 h1 term199). Qed.
Lemma lem3861066 (_44749 : int) : (term556 _44749) = ((term237 _44749) = term133).
Proof. exact (eq_refl (term556 _44749)). Qed.
Lemma lem3861073 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : (term237 _44749) = term133.
Proof. exact (EQ_MP (@lem3861066 _44749) (@lem3861065 _44749 _44750 h1)). Qed.
Lemma lem3861074 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term557 _44749 _44750.
Proof. exact (conj (@lem3861073 _44749 _44750 h1) (@lem3861060 _44749 _44750 h1)). Qed.
Lemma lem3861076 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3861077 (_44749 : int) (_44750 : int) : term558 _44749 _44750.
Proof. exact (@lem3861076 (term237 _44749) (term277 _44749 _44750)). Qed.
Lemma lem3861078 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term559 _44749 _44750.
Proof. exact (@lem3861077 _44749 _44750 (@lem3861074 _44749 _44750 h1)). Qed.
Lemma lem3861079 (_44749 : int) (_44750 : int) : (term560 _44749 _44750) = (term561 _44749 _44750).
Proof. exact (@lem1982763 (term237 _44749) (real_of_int _44749) (term237 _44750)). Qed.
Lemma lem3861080 (_44749 : int) : (term497 _44749) = (term498 _44749).
Proof. exact (@lem1982713 term199 (real_of_int _44749)). Qed.
Lemma lem3861082 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861083 : term143 = term224.
Proof. exact (@lem3861082 term11). Qed.
Lemma lem3861085 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3861086 : term199 = term200.
Proof. exact (@lem3861085 term11). Qed.
Lemma lem3861087 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3861088 : term499 = term500.
Proof. exact (MK_COMB (@lem3861087) (@lem3861086)). Qed.
Lemma lem3861089 : term501 = term502.
Proof. exact (MK_COMB (@lem3861088) (@lem3861083)). Qed.
Lemma lem3861090 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3861092 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861093 : term251 = term252.
Proof. exact (@lem3861092 (NUMERAL 0) term11). Qed.
Lemma lem3861094 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861095 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861096 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861095 h1) (fun h1 : term252 = True => @lem3861094)). Qed.
Lemma lem3861097 : term252 = True.
Proof. exact (EQ_MP (@lem3861096) (@lem3861094)). Qed.
Lemma lem3861098 : term251 = True.
Proof. exact (TRANS (@lem3861093) (@lem3861097)). Qed.
Lemma lem3861099 : True = term251.
Proof. exact (SYM (@lem3861098)). Qed.
Lemma lem3861100 : term251.
Proof. exact (EQ_MP (@lem3861099) (@lem0)). Qed.
Lemma lem3861101 : term504.
Proof. exact (@lem3861090 (@lem3861100)). Qed.
Lemma lem3861103 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861104 : term251 = term252.
Proof. exact (@lem3861103 (NUMERAL 0) term11). Qed.
Lemma lem3861105 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861106 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861107 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861106 h1) (fun h1 : term252 = True => @lem3861105)). Qed.
Lemma lem3861108 : term252 = True.
Proof. exact (EQ_MP (@lem3861107) (@lem3861105)). Qed.
Lemma lem3861109 : term251 = True.
Proof. exact (TRANS (@lem3861104) (@lem3861108)). Qed.
Lemma lem3861110 : True = term251.
Proof. exact (SYM (@lem3861109)). Qed.
Lemma lem3861111 : term251.
Proof. exact (EQ_MP (@lem3861110) (@lem0)). Qed.
Lemma lem3861112 : term505.
Proof. exact (@lem3861101 (@lem3861111)). Qed.
Lemma lem3861114 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861115 : term251 = term252.
Proof. exact (@lem3861114 (NUMERAL 0) term11). Qed.
Lemma lem3861116 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861117 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861118 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861117 h1) (fun h1 : term252 = True => @lem3861116)). Qed.
Lemma lem3861119 : term252 = True.
Proof. exact (EQ_MP (@lem3861118) (@lem3861116)). Qed.
Lemma lem3861120 : term251 = True.
Proof. exact (TRANS (@lem3861115) (@lem3861119)). Qed.
Lemma lem3861121 : True = term251.
Proof. exact (SYM (@lem3861120)). Qed.
Lemma lem3861122 : term251.
Proof. exact (EQ_MP (@lem3861121) (@lem0)). Qed.
Lemma lem3861123 : term506.
Proof. exact (@lem3861112 (@lem3861122)). Qed.
Lemma lem3861125 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3861126 : term208 = term209.
Proof. exact (@lem3861125 term11 term11). Qed.
Lemma lem3861127 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861128 : term211 = term11.
Proof. exact (EQ_MP (@lem3861127) (@lem940073)). Qed.
Lemma lem3861129 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861130 : term209 = term143.
Proof. exact (MK_COMB (@lem3861129) (@lem3861128)). Qed.
Lemma lem3861131 : term208 = term143.
Proof. exact (TRANS (@lem3861126) (@lem3861130)). Qed.
Lemma lem3861133 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3861134 : term225 = term230.
Proof. exact (@lem3861133 term11 term11). Qed.
Lemma lem3861135 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861136 : term211 = term11.
Proof. exact (EQ_MP (@lem3861135) (@lem940073)). Qed.
Lemma lem3861137 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861138 : term209 = term143.
Proof. exact (MK_COMB (@lem3861137) (@lem3861136)). Qed.
Lemma lem3861139 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3861140 : term230 = term199.
Proof. exact (MK_COMB (@lem3861139) (@lem3861138)). Qed.
Lemma lem3861141 : term225 = term199.
Proof. exact (TRANS (@lem3861134) (@lem3861140)). Qed.
Lemma lem3861142 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3861143 : term507 = term499.
Proof. exact (MK_COMB (@lem3861142) (@lem3861141)). Qed.
Lemma lem3861144 : term508 = term501.
Proof. exact (MK_COMB (@lem3861143) (@lem3861131)). Qed.
Lemma lem3861146 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3861147 : term501 = term133.
Proof. exact (@lem3861146 term11). Qed.
Lemma lem3861148 : term508 = term133.
Proof. exact (TRANS (@lem3861144) (@lem3861147)). Qed.
Lemma lem3861149 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3861150 : term510 = term261.
Proof. exact (MK_COMB (@lem3861149) (@lem3861148)). Qed.
Lemma lem3861151 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3861152 : term511 = term263.
Proof. exact (MK_COMB (@lem3861150) (@lem3861151)). Qed.
Lemma lem3861154 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861155 : term263 = term133.
Proof. exact (@lem3861154 term11). Qed.
Lemma lem3861156 : term511 = term133.
Proof. exact (TRANS (@lem3861152) (@lem3861155)). Qed.
Lemma lem3861158 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3861159 : term208 = term209.
Proof. exact (@lem3861158 term11 term11). Qed.
Lemma lem3861160 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861161 : term211 = term11.
Proof. exact (EQ_MP (@lem3861160) (@lem940073)). Qed.
Lemma lem3861162 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861163 : term209 = term143.
Proof. exact (MK_COMB (@lem3861162) (@lem3861161)). Qed.
Lemma lem3861164 : term208 = term143.
Proof. exact (TRANS (@lem3861159) (@lem3861163)). Qed.
Lemma lem3861165 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3861166 : term265 = term263.
Proof. exact (MK_COMB (@lem3861165) (@lem3861164)). Qed.
Lemma lem3861168 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861169 : term263 = term133.
Proof. exact (@lem3861168 term11). Qed.
Lemma lem3861170 : term265 = term133.
Proof. exact (TRANS (@lem3861166) (@lem3861169)). Qed.
Lemma lem3861171 : term133 = term265.
Proof. exact (SYM (@lem3861170)). Qed.
Lemma lem3861172 : term511 = term265.
Proof. exact (TRANS (@lem3861156) (@lem3861171)). Qed.
Lemma lem3861173 : term502 = term196.
Proof. exact (@lem3861123 (@lem3861172)). Qed.
Lemma lem3861174 : term501 = term196.
Proof. exact (TRANS (@lem3861089) (@lem3861173)). Qed.
Lemma lem3861176 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3861177 : term196 = term133.
Proof. exact (@lem3861176 term133). Qed.
Lemma lem3861178 : term501 = term133.
Proof. exact (TRANS (@lem3861174) (@lem3861177)). Qed.
Lemma lem3861179 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3861180 : term512 = term261.
Proof. exact (MK_COMB (@lem3861179) (@lem3861178)). Qed.
Lemma lem3861181 (_44749 : int) : (real_of_int _44749) = (real_of_int _44749).
Proof. exact (eq_refl (real_of_int _44749)). Qed.
Lemma lem3861182 (_44749 : int) : (term498 _44749) = (term513 _44749).
Proof. exact (MK_COMB (@lem3861180) (@lem3861181 _44749)). Qed.
Lemma lem3861183 (_44749 : int) : (term497 _44749) = (term513 _44749).
Proof. exact (TRANS (@lem3861080 _44749) (@lem3861182 _44749)). Qed.
Lemma lem3861184 (_44749 : int) : (term513 _44749) = term133.
Proof. exact (@lem1982719 (real_of_int _44749)). Qed.
Lemma lem3861185 (_44749 : int) : (term497 _44749) = term133.
Proof. exact (TRANS (@lem3861183 _44749) (@lem3861184 _44749)). Qed.
Lemma lem3861186 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3861187 (_44749 : int) : (term514 _44749) = term175.
Proof. exact (MK_COMB (@lem3861186) (@lem3861185 _44749)). Qed.
Lemma lem3861188 (_44750 : int) : (term237 _44750) = (term237 _44750).
Proof. exact (eq_refl (term237 _44750)). Qed.
Lemma lem3861189 (_44749 : int) (_44750 : int) : (term561 _44749 _44750) = (term562 _44750).
Proof. exact (MK_COMB (@lem3861187 _44749) (@lem3861188 _44750)). Qed.
Lemma lem3861190 (_44749 : int) (_44750 : int) : (term560 _44749 _44750) = (term562 _44750).
Proof. exact (TRANS (@lem3861079 _44749 _44750) (@lem3861189 _44749 _44750)). Qed.
Lemma lem3861191 (_44750 : int) : (term562 _44750) = (term237 _44750).
Proof. exact (@lem1982721 (term237 _44750)). Qed.
Lemma lem3861192 (_44749 : int) (_44750 : int) : (term560 _44749 _44750) = (term237 _44750).
Proof. exact (TRANS (@lem3861190 _44749 _44750) (@lem3861191 _44750)). Qed.
Lemma lem3861193 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3861194 (_44749 : int) (_44750 : int) : (term563 _44749 _44750) = (term268 _44750).
Proof. exact (MK_COMB (@lem3861193) (@lem3861192 _44749 _44750)). Qed.
Lemma lem3861195 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3861196 (_44749 : int) (_44750 : int) : (term559 _44749 _44750) = (term269 _44750).
Proof. exact (MK_COMB (@lem3861194 _44749 _44750) (@lem3861195)). Qed.
Lemma lem3861197 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term269 _44750.
Proof. exact (EQ_MP (@lem3861196 _44749 _44750) (@lem3861078 _44749 _44750 h1)). Qed.
Lemma lem3861199 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3861200 : term471 = term251.
Proof. exact (@lem3861199 term133 term143). Qed.
Lemma lem3861202 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861203 : term143 = term224.
Proof. exact (@lem3861202 term11). Qed.
Lemma lem3861205 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861206 : term133 = term196.
Proof. exact (@lem3861205 (NUMERAL 0)). Qed.
Lemma lem3861207 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3861208 : term472 = term473.
Proof. exact (MK_COMB (@lem3861207) (@lem3861206)). Qed.
Lemma lem3861209 : term251 = term474.
Proof. exact (MK_COMB (@lem3861208) (@lem3861203)). Qed.
Lemma lem3861210 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3861212 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861213 : term251 = term252.
Proof. exact (@lem3861212 (NUMERAL 0) term11). Qed.
Lemma lem3861214 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861215 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861216 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861215 h1) (fun h1 : term252 = True => @lem3861214)). Qed.
Lemma lem3861217 : term252 = True.
Proof. exact (EQ_MP (@lem3861216) (@lem3861214)). Qed.
Lemma lem3861218 : term251 = True.
Proof. exact (TRANS (@lem3861213) (@lem3861217)). Qed.
Lemma lem3861219 : True = term251.
Proof. exact (SYM (@lem3861218)). Qed.
Lemma lem3861220 : term251.
Proof. exact (EQ_MP (@lem3861219) (@lem0)). Qed.
Lemma lem3861221 : term476.
Proof. exact (@lem3861210 (@lem3861220)). Qed.
Lemma lem3861223 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861224 : term251 = term252.
Proof. exact (@lem3861223 (NUMERAL 0) term11). Qed.
Lemma lem3861225 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861226 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861227 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861226 h1) (fun h1 : term252 = True => @lem3861225)). Qed.
Lemma lem3861228 : term252 = True.
Proof. exact (EQ_MP (@lem3861227) (@lem3861225)). Qed.
Lemma lem3861229 : term251 = True.
Proof. exact (TRANS (@lem3861224) (@lem3861228)). Qed.
Lemma lem3861230 : True = term251.
Proof. exact (SYM (@lem3861229)). Qed.
Lemma lem3861231 : term251.
Proof. exact (EQ_MP (@lem3861230) (@lem0)). Qed.
Lemma lem3861232 : term474 = term477.
Proof. exact (@lem3861221 (@lem3861231)). Qed.
Lemma lem3861234 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3861235 : term208 = term209.
Proof. exact (@lem3861234 term11 term11). Qed.
Lemma lem3861236 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861237 : term211 = term11.
Proof. exact (EQ_MP (@lem3861236) (@lem940073)). Qed.
Lemma lem3861238 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861239 : term209 = term143.
Proof. exact (MK_COMB (@lem3861238) (@lem3861237)). Qed.
Lemma lem3861240 : term208 = term143.
Proof. exact (TRANS (@lem3861235) (@lem3861239)). Qed.
Lemma lem3861242 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861243 : term263 = term133.
Proof. exact (@lem3861242 term11). Qed.
Lemma lem3861244 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3861245 : term478 = term472.
Proof. exact (MK_COMB (@lem3861244) (@lem3861243)). Qed.
Lemma lem3861246 : term477 = term251.
Proof. exact (MK_COMB (@lem3861245) (@lem3861240)). Qed.
Lemma lem3861248 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861249 : term251 = term252.
Proof. exact (@lem3861248 (NUMERAL 0) term11). Qed.
Lemma lem3861250 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861251 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861252 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861251 h1) (fun h1 : term252 = True => @lem3861250)). Qed.
Lemma lem3861253 : term252 = True.
Proof. exact (EQ_MP (@lem3861252) (@lem3861250)). Qed.
Lemma lem3861254 : term251 = True.
Proof. exact (TRANS (@lem3861249) (@lem3861253)). Qed.
Lemma lem3861255 : term477 = True.
Proof. exact (TRANS (@lem3861246) (@lem3861254)). Qed.
Lemma lem3861256 : term474 = True.
Proof. exact (TRANS (@lem3861232) (@lem3861255)). Qed.
Lemma lem3861257 : term251 = True.
Proof. exact (TRANS (@lem3861209) (@lem3861256)). Qed.
Lemma lem3861258 : term471 = True.
Proof. exact (TRANS (@lem3861200) (@lem3861257)). Qed.
Lemma lem3861259 : True = term471.
Proof. exact (SYM (@lem3861258)). Qed.
Lemma lem3861260 : term471.
Proof. exact (EQ_MP (@lem3861259) (@lem0)). Qed.
Lemma lem3861261 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term564 _44750.
Proof. exact (conj (@lem3861260) (@lem3861197 _44749 _44750 h1)). Qed.
Lemma lem3861263 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3861264 (_44750 : int) : term565 _44750.
Proof. exact (@lem3861263 term143 (term237 _44750)). Qed.
Lemma lem3861265 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term566 _44750.
Proof. exact (@lem3861264 _44750 (@lem3861261 _44749 _44750 h1)). Qed.
Lemma lem3861266 (_44750 : int) : (term567 _44750) = (term237 _44750).
Proof. exact (@lem1982733 (term237 _44750)). Qed.
Lemma lem3861267 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3861268 (_44750 : int) : (term568 _44750) = (term268 _44750).
Proof. exact (MK_COMB (@lem3861267) (@lem3861266 _44750)). Qed.
Lemma lem3861269 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3861270 (_44750 : int) : (term566 _44750) = (term269 _44750).
Proof. exact (MK_COMB (@lem3861268 _44750) (@lem3861269)). Qed.
Lemma lem3861271 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term269 _44750.
Proof. exact (EQ_MP (@lem3861270 _44750) (@lem3861265 _44749 _44750 h1)). Qed.
Lemma lem3861272 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term569 _44750.
Proof. exact (conj (@lem3861271 _44749 _44750 h1) (@lem3860986 _44749 _44750 h1)). Qed.
Lemma lem3861274 (x : real) (y : real) : term570 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3861275 (_44750 : int) : term571 _44750.
Proof. exact (@lem3861274 (term237 _44750) (term299 _44750)). Qed.
Lemma lem3861276 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term572 _44750.
Proof. exact (@lem3861275 _44750 (@lem3861272 _44749 _44750 h1)). Qed.
Lemma lem3861277 (_44750 : int) : (term573 _44750) = (term574 _44750).
Proof. exact (@lem1982763 (term237 _44750) (real_of_int _44750) term199). Qed.
Lemma lem3861278 (_44750 : int) : (term497 _44750) = (term498 _44750).
Proof. exact (@lem1982713 term199 (real_of_int _44750)). Qed.
Lemma lem3861280 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861281 : term143 = term224.
Proof. exact (@lem3861280 term11). Qed.
Lemma lem3861283 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3861284 : term199 = term200.
Proof. exact (@lem3861283 term11). Qed.
Lemma lem3861285 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3861286 : term499 = term500.
Proof. exact (MK_COMB (@lem3861285) (@lem3861284)). Qed.
Lemma lem3861287 : term501 = term502.
Proof. exact (MK_COMB (@lem3861286) (@lem3861281)). Qed.
Lemma lem3861288 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3861290 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861291 : term251 = term252.
Proof. exact (@lem3861290 (NUMERAL 0) term11). Qed.
Lemma lem3861292 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861293 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861294 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861293 h1) (fun h1 : term252 = True => @lem3861292)). Qed.
Lemma lem3861295 : term252 = True.
Proof. exact (EQ_MP (@lem3861294) (@lem3861292)). Qed.
Lemma lem3861296 : term251 = True.
Proof. exact (TRANS (@lem3861291) (@lem3861295)). Qed.
Lemma lem3861297 : True = term251.
Proof. exact (SYM (@lem3861296)). Qed.
Lemma lem3861298 : term251.
Proof. exact (EQ_MP (@lem3861297) (@lem0)). Qed.
Lemma lem3861299 : term504.
Proof. exact (@lem3861288 (@lem3861298)). Qed.
Lemma lem3861301 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861302 : term251 = term252.
Proof. exact (@lem3861301 (NUMERAL 0) term11). Qed.
Lemma lem3861303 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861304 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861305 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861304 h1) (fun h1 : term252 = True => @lem3861303)). Qed.
Lemma lem3861306 : term252 = True.
Proof. exact (EQ_MP (@lem3861305) (@lem3861303)). Qed.
Lemma lem3861307 : term251 = True.
Proof. exact (TRANS (@lem3861302) (@lem3861306)). Qed.
Lemma lem3861308 : True = term251.
Proof. exact (SYM (@lem3861307)). Qed.
Lemma lem3861309 : term251.
Proof. exact (EQ_MP (@lem3861308) (@lem0)). Qed.
Lemma lem3861310 : term505.
Proof. exact (@lem3861299 (@lem3861309)). Qed.
Lemma lem3861312 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861313 : term251 = term252.
Proof. exact (@lem3861312 (NUMERAL 0) term11). Qed.
Lemma lem3861314 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861315 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861316 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861315 h1) (fun h1 : term252 = True => @lem3861314)). Qed.
Lemma lem3861317 : term252 = True.
Proof. exact (EQ_MP (@lem3861316) (@lem3861314)). Qed.
Lemma lem3861318 : term251 = True.
Proof. exact (TRANS (@lem3861313) (@lem3861317)). Qed.
Lemma lem3861319 : True = term251.
Proof. exact (SYM (@lem3861318)). Qed.
Lemma lem3861320 : term251.
Proof. exact (EQ_MP (@lem3861319) (@lem0)). Qed.
Lemma lem3861321 : term506.
Proof. exact (@lem3861310 (@lem3861320)). Qed.
Lemma lem3861323 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3861324 : term208 = term209.
Proof. exact (@lem3861323 term11 term11). Qed.
Lemma lem3861325 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861326 : term211 = term11.
Proof. exact (EQ_MP (@lem3861325) (@lem940073)). Qed.
Lemma lem3861327 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861328 : term209 = term143.
Proof. exact (MK_COMB (@lem3861327) (@lem3861326)). Qed.
Lemma lem3861329 : term208 = term143.
Proof. exact (TRANS (@lem3861324) (@lem3861328)). Qed.
Lemma lem3861331 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3861332 : term225 = term230.
Proof. exact (@lem3861331 term11 term11). Qed.
Lemma lem3861333 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861334 : term211 = term11.
Proof. exact (EQ_MP (@lem3861333) (@lem940073)). Qed.
Lemma lem3861335 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861336 : term209 = term143.
Proof. exact (MK_COMB (@lem3861335) (@lem3861334)). Qed.
Lemma lem3861337 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3861338 : term230 = term199.
Proof. exact (MK_COMB (@lem3861337) (@lem3861336)). Qed.
Lemma lem3861339 : term225 = term199.
Proof. exact (TRANS (@lem3861332) (@lem3861338)). Qed.
Lemma lem3861340 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3861341 : term507 = term499.
Proof. exact (MK_COMB (@lem3861340) (@lem3861339)). Qed.
Lemma lem3861342 : term508 = term501.
Proof. exact (MK_COMB (@lem3861341) (@lem3861329)). Qed.
Lemma lem3861344 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3861345 : term501 = term133.
Proof. exact (@lem3861344 term11). Qed.
Lemma lem3861346 : term508 = term133.
Proof. exact (TRANS (@lem3861342) (@lem3861345)). Qed.
Lemma lem3861347 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3861348 : term510 = term261.
Proof. exact (MK_COMB (@lem3861347) (@lem3861346)). Qed.
Lemma lem3861349 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3861350 : term511 = term263.
Proof. exact (MK_COMB (@lem3861348) (@lem3861349)). Qed.
Lemma lem3861352 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861353 : term263 = term133.
Proof. exact (@lem3861352 term11). Qed.
Lemma lem3861354 : term511 = term133.
Proof. exact (TRANS (@lem3861350) (@lem3861353)). Qed.
Lemma lem3861356 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3861357 : term208 = term209.
Proof. exact (@lem3861356 term11 term11). Qed.
Lemma lem3861358 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861359 : term211 = term11.
Proof. exact (EQ_MP (@lem3861358) (@lem940073)). Qed.
Lemma lem3861360 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861361 : term209 = term143.
Proof. exact (MK_COMB (@lem3861360) (@lem3861359)). Qed.
Lemma lem3861362 : term208 = term143.
Proof. exact (TRANS (@lem3861357) (@lem3861361)). Qed.
Lemma lem3861363 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3861364 : term265 = term263.
Proof. exact (MK_COMB (@lem3861363) (@lem3861362)). Qed.
Lemma lem3861366 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861367 : term263 = term133.
Proof. exact (@lem3861366 term11). Qed.
Lemma lem3861368 : term265 = term133.
Proof. exact (TRANS (@lem3861364) (@lem3861367)). Qed.
Lemma lem3861369 : term133 = term265.
Proof. exact (SYM (@lem3861368)). Qed.
Lemma lem3861370 : term511 = term265.
Proof. exact (TRANS (@lem3861354) (@lem3861369)). Qed.
Lemma lem3861371 : term502 = term196.
Proof. exact (@lem3861321 (@lem3861370)). Qed.
Lemma lem3861372 : term501 = term196.
Proof. exact (TRANS (@lem3861287) (@lem3861371)). Qed.
Lemma lem3861374 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3861375 : term196 = term133.
Proof. exact (@lem3861374 term133). Qed.
Lemma lem3861376 : term501 = term133.
Proof. exact (TRANS (@lem3861372) (@lem3861375)). Qed.
Lemma lem3861377 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3861378 : term512 = term261.
Proof. exact (MK_COMB (@lem3861377) (@lem3861376)). Qed.
Lemma lem3861379 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3861380 (_44750 : int) : (term498 _44750) = (term513 _44750).
Proof. exact (MK_COMB (@lem3861378) (@lem3861379 _44750)). Qed.
Lemma lem3861381 (_44750 : int) : (term497 _44750) = (term513 _44750).
Proof. exact (TRANS (@lem3861278 _44750) (@lem3861380 _44750)). Qed.
Lemma lem3861382 (_44750 : int) : (term513 _44750) = term133.
Proof. exact (@lem1982719 (real_of_int _44750)). Qed.
Lemma lem3861383 (_44750 : int) : (term497 _44750) = term133.
Proof. exact (TRANS (@lem3861381 _44750) (@lem3861382 _44750)). Qed.
Lemma lem3861384 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3861385 (_44750 : int) : (term514 _44750) = term175.
Proof. exact (MK_COMB (@lem3861384) (@lem3861383 _44750)). Qed.
Lemma lem3861386 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3861387 (_44750 : int) : (term574 _44750) = term519.
Proof. exact (MK_COMB (@lem3861385 _44750) (@lem3861386)). Qed.
Lemma lem3861388 (_44750 : int) : (term573 _44750) = term519.
Proof. exact (TRANS (@lem3861277 _44750) (@lem3861387 _44750)). Qed.
Lemma lem3861389 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3861390 (_44750 : int) : (term573 _44750) = term199.
Proof. exact (TRANS (@lem3861388 _44750) (@lem3861389)). Qed.
Lemma lem3861391 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3861392 (_44750 : int) : (term575 _44750) = term521.
Proof. exact (MK_COMB (@lem3861391) (@lem3861390 _44750)). Qed.
Lemma lem3861393 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3861394 (_44750 : int) : (term572 _44750) = term522.
Proof. exact (MK_COMB (@lem3861392 _44750) (@lem3861393)). Qed.
Lemma lem3861395 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : term522.
Proof. exact (EQ_MP (@lem3861394 _44750) (@lem3861276 _44749 _44750 h1)). Qed.
Lemma lem3861397 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3861398 : term522 = term523.
Proof. exact (@lem3861397 term133 term199). Qed.
Lemma lem3861400 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3861401 : term199 = term200.
Proof. exact (@lem3861400 term11). Qed.
Lemma lem3861403 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861404 : term133 = term196.
Proof. exact (@lem3861403 (NUMERAL 0)). Qed.
Lemma lem3861405 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3861406 : term135 = term524.
Proof. exact (MK_COMB (@lem3861405) (@lem3861404)). Qed.
Lemma lem3861407 : term523 = term525.
Proof. exact (MK_COMB (@lem3861406) (@lem3861401)). Qed.
Lemma lem3861408 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3861410 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861411 : term251 = term252.
Proof. exact (@lem3861410 (NUMERAL 0) term11). Qed.
Lemma lem3861412 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861413 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861414 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861413 h1) (fun h1 : term252 = True => @lem3861412)). Qed.
Lemma lem3861415 : term252 = True.
Proof. exact (EQ_MP (@lem3861414) (@lem3861412)). Qed.
Lemma lem3861416 : term251 = True.
Proof. exact (TRANS (@lem3861411) (@lem3861415)). Qed.
Lemma lem3861417 : True = term251.
Proof. exact (SYM (@lem3861416)). Qed.
Lemma lem3861418 : term251.
Proof. exact (EQ_MP (@lem3861417) (@lem0)). Qed.
Lemma lem3861419 : term527.
Proof. exact (@lem3861408 (@lem3861418)). Qed.
Lemma lem3861421 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861422 : term251 = term252.
Proof. exact (@lem3861421 (NUMERAL 0) term11). Qed.
Lemma lem3861423 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861424 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861425 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861424 h1) (fun h1 : term252 = True => @lem3861423)). Qed.
Lemma lem3861426 : term252 = True.
Proof. exact (EQ_MP (@lem3861425) (@lem3861423)). Qed.
Lemma lem3861427 : term251 = True.
Proof. exact (TRANS (@lem3861422) (@lem3861426)). Qed.
Lemma lem3861428 : True = term251.
Proof. exact (SYM (@lem3861427)). Qed.
Lemma lem3861429 : term251.
Proof. exact (EQ_MP (@lem3861428) (@lem0)). Qed.
Lemma lem3861430 : term525 = term528.
Proof. exact (@lem3861419 (@lem3861429)). Qed.
Lemma lem3861432 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3861433 : term225 = term230.
Proof. exact (@lem3861432 term11 term11). Qed.
Lemma lem3861434 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861435 : term211 = term11.
Proof. exact (EQ_MP (@lem3861434) (@lem940073)). Qed.
Lemma lem3861436 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861437 : term209 = term143.
Proof. exact (MK_COMB (@lem3861436) (@lem3861435)). Qed.
Lemma lem3861438 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3861439 : term230 = term199.
Proof. exact (MK_COMB (@lem3861438) (@lem3861437)). Qed.
Lemma lem3861440 : term225 = term199.
Proof. exact (TRANS (@lem3861433) (@lem3861439)). Qed.
Lemma lem3861442 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861443 : term263 = term133.
Proof. exact (@lem3861442 term11). Qed.
Lemma lem3861444 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3861445 : term529 = term135.
Proof. exact (MK_COMB (@lem3861444) (@lem3861443)). Qed.
Lemma lem3861446 : term528 = term523.
Proof. exact (MK_COMB (@lem3861445) (@lem3861440)). Qed.
Lemma lem3861448 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3861449 : term523 = term532.
Proof. exact (@lem3861448 (NUMERAL 0) term11). Qed.
Lemma lem3861450 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861451 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3861452 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861451 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3861450)). Qed.
Lemma lem3861453 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3861452) (@lem3861450)). Qed.
Lemma lem3861454 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3861455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3861456 : term533 = (and True).
Proof. exact (MK_COMB (@lem3861455) (@lem3861454)). Qed.
Lemma lem3861457 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3861456) (@lem3861453)). Qed.
Lemma lem3861459 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3861460 : term532 = False.
Proof. exact (TRANS (@lem3861457) (@lem3861459)). Qed.
Lemma lem3861461 : term523 = False.
Proof. exact (TRANS (@lem3861449) (@lem3861460)). Qed.
Lemma lem3861462 : term528 = False.
Proof. exact (TRANS (@lem3861446) (@lem3861461)). Qed.
Lemma lem3861463 : term525 = False.
Proof. exact (TRANS (@lem3861430) (@lem3861462)). Qed.
Lemma lem3861464 : term523 = False.
Proof. exact (TRANS (@lem3861407) (@lem3861463)). Qed.
Lemma lem3861465 : term522 = False.
Proof. exact (TRANS (@lem3861398) (@lem3861464)). Qed.
Lemma lem3861466 (_44749 : int) (_44750 : int) (h1 : term621 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3861465) (@lem3861395 _44749 _44750 h1)). Qed.
Lemma lem3861467 (_44749 : int) (_44750 : int) (h1 : term432 _44749 _44750) : False.
Proof. exact (or_elim (@lem3860497 _44749 _44750 h1) (fun h0 : term620 _44749 _44750 => @lem3860901 _44749 _44750 h0) (fun h0 : term621 _44749 _44750 => @lem3861466 _44749 _44750 h0)). Qed.
Lemma lem3861468 (_44749 : int) (_44750 : int) (h1 : term428 _44749 _44750) : term428 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3861469 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term622 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3861470 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term429 _44749 _44750.
Proof. exact (proj2 (@lem3861469 _44749 _44750 h1)). Qed.
Lemma lem3861472 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term380 _44749 _44750.
Proof. exact (proj2 (@lem3861470 _44749 _44750 h1)). Qed.
Lemma lem3861474 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term336 _44750.
Proof. exact (proj2 (@lem3861472 _44749 _44750 h1)). Qed.
Lemma lem3861476 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term302 _44750.
Proof. exact (proj2 (@lem3861474 _44749 _44750 h1)). Qed.
Lemma lem3861477 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : (real_of_int _44750) = term133.
Proof. exact (proj1 (@lem3861474 _44749 _44750 h1)). Qed.
Lemma lem3861479 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3861480 : term471 = term251.
Proof. exact (@lem3861479 term133 term143). Qed.
Lemma lem3861482 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861483 : term143 = term224.
Proof. exact (@lem3861482 term11). Qed.
Lemma lem3861485 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861486 : term133 = term196.
Proof. exact (@lem3861485 (NUMERAL 0)). Qed.
Lemma lem3861487 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3861488 : term472 = term473.
Proof. exact (MK_COMB (@lem3861487) (@lem3861486)). Qed.
Lemma lem3861489 : term251 = term474.
Proof. exact (MK_COMB (@lem3861488) (@lem3861483)). Qed.
Lemma lem3861490 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3861492 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861493 : term251 = term252.
Proof. exact (@lem3861492 (NUMERAL 0) term11). Qed.
Lemma lem3861494 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861495 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861496 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861495 h1) (fun h1 : term252 = True => @lem3861494)). Qed.
Lemma lem3861497 : term252 = True.
Proof. exact (EQ_MP (@lem3861496) (@lem3861494)). Qed.
Lemma lem3861498 : term251 = True.
Proof. exact (TRANS (@lem3861493) (@lem3861497)). Qed.
Lemma lem3861499 : True = term251.
Proof. exact (SYM (@lem3861498)). Qed.
Lemma lem3861500 : term251.
Proof. exact (EQ_MP (@lem3861499) (@lem0)). Qed.
Lemma lem3861501 : term476.
Proof. exact (@lem3861490 (@lem3861500)). Qed.
Lemma lem3861503 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861504 : term251 = term252.
Proof. exact (@lem3861503 (NUMERAL 0) term11). Qed.
Lemma lem3861505 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861506 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861507 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861506 h1) (fun h1 : term252 = True => @lem3861505)). Qed.
Lemma lem3861508 : term252 = True.
Proof. exact (EQ_MP (@lem3861507) (@lem3861505)). Qed.
Lemma lem3861509 : term251 = True.
Proof. exact (TRANS (@lem3861504) (@lem3861508)). Qed.
Lemma lem3861510 : True = term251.
Proof. exact (SYM (@lem3861509)). Qed.
Lemma lem3861511 : term251.
Proof. exact (EQ_MP (@lem3861510) (@lem0)). Qed.
Lemma lem3861512 : term474 = term477.
Proof. exact (@lem3861501 (@lem3861511)). Qed.
Lemma lem3861514 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3861515 : term208 = term209.
Proof. exact (@lem3861514 term11 term11). Qed.
Lemma lem3861516 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861517 : term211 = term11.
Proof. exact (EQ_MP (@lem3861516) (@lem940073)). Qed.
Lemma lem3861518 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861519 : term209 = term143.
Proof. exact (MK_COMB (@lem3861518) (@lem3861517)). Qed.
Lemma lem3861520 : term208 = term143.
Proof. exact (TRANS (@lem3861515) (@lem3861519)). Qed.
Lemma lem3861522 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861523 : term263 = term133.
Proof. exact (@lem3861522 term11). Qed.
Lemma lem3861524 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3861525 : term478 = term472.
Proof. exact (MK_COMB (@lem3861524) (@lem3861523)). Qed.
Lemma lem3861526 : term477 = term251.
Proof. exact (MK_COMB (@lem3861525) (@lem3861520)). Qed.
Lemma lem3861528 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861529 : term251 = term252.
Proof. exact (@lem3861528 (NUMERAL 0) term11). Qed.
Lemma lem3861530 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861531 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861532 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861531 h1) (fun h1 : term252 = True => @lem3861530)). Qed.
Lemma lem3861533 : term252 = True.
Proof. exact (EQ_MP (@lem3861532) (@lem3861530)). Qed.
Lemma lem3861534 : term251 = True.
Proof. exact (TRANS (@lem3861529) (@lem3861533)). Qed.
Lemma lem3861535 : term477 = True.
Proof. exact (TRANS (@lem3861526) (@lem3861534)). Qed.
Lemma lem3861536 : term474 = True.
Proof. exact (TRANS (@lem3861512) (@lem3861535)). Qed.
Lemma lem3861537 : term251 = True.
Proof. exact (TRANS (@lem3861489) (@lem3861536)). Qed.
Lemma lem3861538 : term471 = True.
Proof. exact (TRANS (@lem3861480) (@lem3861537)). Qed.
Lemma lem3861539 : True = term471.
Proof. exact (SYM (@lem3861538)). Qed.
Lemma lem3861540 : term471.
Proof. exact (EQ_MP (@lem3861539) (@lem0)). Qed.
Lemma lem3861541 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term551 _44750.
Proof. exact (conj (@lem3861540) (@lem3861476 _44749 _44750 h1)). Qed.
Lemma lem3861543 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3861544 (_44750 : int) : term552 _44750.
Proof. exact (@lem3861543 term143 (term299 _44750)). Qed.
Lemma lem3861545 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term553 _44750.
Proof. exact (@lem3861544 _44750 (@lem3861541 _44749 _44750 h1)). Qed.
Lemma lem3861546 (_44750 : int) : (term554 _44750) = (term299 _44750).
Proof. exact (@lem1982733 (term299 _44750)). Qed.
Lemma lem3861547 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3861548 (_44750 : int) : (term555 _44750) = (term301 _44750).
Proof. exact (MK_COMB (@lem3861547) (@lem3861546 _44750)). Qed.
Lemma lem3861549 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3861550 (_44750 : int) : (term553 _44750) = (term302 _44750).
Proof. exact (MK_COMB (@lem3861548 _44750) (@lem3861549)). Qed.
Lemma lem3861551 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term302 _44750.
Proof. exact (EQ_MP (@lem3861550 _44750) (@lem3861545 _44749 _44750 h1)). Qed.
Lemma lem3861553 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3861554 (_44750 : int) : term539 _44750.
Proof. exact (@lem3861553 (real_of_int _44750)). Qed.
Lemma lem3861555 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term540 _44750.
Proof. exact (@lem3861554 _44750 (@lem3861477 _44749 _44750 h1)). Qed.
Lemma lem3861556 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term556 _44750.
Proof. exact (@lem3861555 _44749 _44750 h1 term199). Qed.
Lemma lem3861557 (_44750 : int) : (term556 _44750) = ((term237 _44750) = term133).
Proof. exact (eq_refl (term556 _44750)). Qed.
Lemma lem3861564 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : (term237 _44750) = term133.
Proof. exact (EQ_MP (@lem3861557 _44750) (@lem3861556 _44749 _44750 h1)). Qed.
Lemma lem3861565 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term623 _44750.
Proof. exact (conj (@lem3861564 _44749 _44750 h1) (@lem3861551 _44749 _44750 h1)). Qed.
Lemma lem3861567 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3861568 (_44750 : int) : term624 _44750.
Proof. exact (@lem3861567 (term237 _44750) (term299 _44750)). Qed.
Lemma lem3861569 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term572 _44750.
Proof. exact (@lem3861568 _44750 (@lem3861565 _44749 _44750 h1)). Qed.
Lemma lem3861570 (_44750 : int) : (term573 _44750) = (term574 _44750).
Proof. exact (@lem1982763 (term237 _44750) (real_of_int _44750) term199). Qed.
Lemma lem3861571 (_44750 : int) : (term497 _44750) = (term498 _44750).
Proof. exact (@lem1982713 term199 (real_of_int _44750)). Qed.
Lemma lem3861573 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861574 : term143 = term224.
Proof. exact (@lem3861573 term11). Qed.
Lemma lem3861576 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3861577 : term199 = term200.
Proof. exact (@lem3861576 term11). Qed.
Lemma lem3861578 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3861579 : term499 = term500.
Proof. exact (MK_COMB (@lem3861578) (@lem3861577)). Qed.
Lemma lem3861580 : term501 = term502.
Proof. exact (MK_COMB (@lem3861579) (@lem3861574)). Qed.
Lemma lem3861581 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3861583 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861584 : term251 = term252.
Proof. exact (@lem3861583 (NUMERAL 0) term11). Qed.
Lemma lem3861585 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861586 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861587 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861586 h1) (fun h1 : term252 = True => @lem3861585)). Qed.
Lemma lem3861588 : term252 = True.
Proof. exact (EQ_MP (@lem3861587) (@lem3861585)). Qed.
Lemma lem3861589 : term251 = True.
Proof. exact (TRANS (@lem3861584) (@lem3861588)). Qed.
Lemma lem3861590 : True = term251.
Proof. exact (SYM (@lem3861589)). Qed.
Lemma lem3861591 : term251.
Proof. exact (EQ_MP (@lem3861590) (@lem0)). Qed.
Lemma lem3861592 : term504.
Proof. exact (@lem3861581 (@lem3861591)). Qed.
Lemma lem3861594 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861595 : term251 = term252.
Proof. exact (@lem3861594 (NUMERAL 0) term11). Qed.
Lemma lem3861596 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861597 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861598 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861597 h1) (fun h1 : term252 = True => @lem3861596)). Qed.
Lemma lem3861599 : term252 = True.
Proof. exact (EQ_MP (@lem3861598) (@lem3861596)). Qed.
Lemma lem3861600 : term251 = True.
Proof. exact (TRANS (@lem3861595) (@lem3861599)). Qed.
Lemma lem3861601 : True = term251.
Proof. exact (SYM (@lem3861600)). Qed.
Lemma lem3861602 : term251.
Proof. exact (EQ_MP (@lem3861601) (@lem0)). Qed.
Lemma lem3861603 : term505.
Proof. exact (@lem3861592 (@lem3861602)). Qed.
Lemma lem3861605 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861606 : term251 = term252.
Proof. exact (@lem3861605 (NUMERAL 0) term11). Qed.
Lemma lem3861607 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861608 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861609 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861608 h1) (fun h1 : term252 = True => @lem3861607)). Qed.
Lemma lem3861610 : term252 = True.
Proof. exact (EQ_MP (@lem3861609) (@lem3861607)). Qed.
Lemma lem3861611 : term251 = True.
Proof. exact (TRANS (@lem3861606) (@lem3861610)). Qed.
Lemma lem3861612 : True = term251.
Proof. exact (SYM (@lem3861611)). Qed.
Lemma lem3861613 : term251.
Proof. exact (EQ_MP (@lem3861612) (@lem0)). Qed.
Lemma lem3861614 : term506.
Proof. exact (@lem3861603 (@lem3861613)). Qed.
Lemma lem3861616 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3861617 : term208 = term209.
Proof. exact (@lem3861616 term11 term11). Qed.
Lemma lem3861618 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861619 : term211 = term11.
Proof. exact (EQ_MP (@lem3861618) (@lem940073)). Qed.
Lemma lem3861620 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861621 : term209 = term143.
Proof. exact (MK_COMB (@lem3861620) (@lem3861619)). Qed.
Lemma lem3861622 : term208 = term143.
Proof. exact (TRANS (@lem3861617) (@lem3861621)). Qed.
Lemma lem3861624 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3861625 : term225 = term230.
Proof. exact (@lem3861624 term11 term11). Qed.
Lemma lem3861626 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861627 : term211 = term11.
Proof. exact (EQ_MP (@lem3861626) (@lem940073)). Qed.
Lemma lem3861628 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861629 : term209 = term143.
Proof. exact (MK_COMB (@lem3861628) (@lem3861627)). Qed.
Lemma lem3861630 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3861631 : term230 = term199.
Proof. exact (MK_COMB (@lem3861630) (@lem3861629)). Qed.
Lemma lem3861632 : term225 = term199.
Proof. exact (TRANS (@lem3861625) (@lem3861631)). Qed.
Lemma lem3861633 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3861634 : term507 = term499.
Proof. exact (MK_COMB (@lem3861633) (@lem3861632)). Qed.
Lemma lem3861635 : term508 = term501.
Proof. exact (MK_COMB (@lem3861634) (@lem3861622)). Qed.
Lemma lem3861637 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3861638 : term501 = term133.
Proof. exact (@lem3861637 term11). Qed.
Lemma lem3861639 : term508 = term133.
Proof. exact (TRANS (@lem3861635) (@lem3861638)). Qed.
Lemma lem3861640 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3861641 : term510 = term261.
Proof. exact (MK_COMB (@lem3861640) (@lem3861639)). Qed.
Lemma lem3861642 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3861643 : term511 = term263.
Proof. exact (MK_COMB (@lem3861641) (@lem3861642)). Qed.
Lemma lem3861645 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861646 : term263 = term133.
Proof. exact (@lem3861645 term11). Qed.
Lemma lem3861647 : term511 = term133.
Proof. exact (TRANS (@lem3861643) (@lem3861646)). Qed.
Lemma lem3861649 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3861650 : term208 = term209.
Proof. exact (@lem3861649 term11 term11). Qed.
Lemma lem3861651 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861652 : term211 = term11.
Proof. exact (EQ_MP (@lem3861651) (@lem940073)). Qed.
Lemma lem3861653 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861654 : term209 = term143.
Proof. exact (MK_COMB (@lem3861653) (@lem3861652)). Qed.
Lemma lem3861655 : term208 = term143.
Proof. exact (TRANS (@lem3861650) (@lem3861654)). Qed.
Lemma lem3861656 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3861657 : term265 = term263.
Proof. exact (MK_COMB (@lem3861656) (@lem3861655)). Qed.
Lemma lem3861659 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861660 : term263 = term133.
Proof. exact (@lem3861659 term11). Qed.
Lemma lem3861661 : term265 = term133.
Proof. exact (TRANS (@lem3861657) (@lem3861660)). Qed.
Lemma lem3861662 : term133 = term265.
Proof. exact (SYM (@lem3861661)). Qed.
Lemma lem3861663 : term511 = term265.
Proof. exact (TRANS (@lem3861647) (@lem3861662)). Qed.
Lemma lem3861664 : term502 = term196.
Proof. exact (@lem3861614 (@lem3861663)). Qed.
Lemma lem3861665 : term501 = term196.
Proof. exact (TRANS (@lem3861580) (@lem3861664)). Qed.
Lemma lem3861667 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3861668 : term196 = term133.
Proof. exact (@lem3861667 term133). Qed.
Lemma lem3861669 : term501 = term133.
Proof. exact (TRANS (@lem3861665) (@lem3861668)). Qed.
Lemma lem3861670 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3861671 : term512 = term261.
Proof. exact (MK_COMB (@lem3861670) (@lem3861669)). Qed.
Lemma lem3861672 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3861673 (_44750 : int) : (term498 _44750) = (term513 _44750).
Proof. exact (MK_COMB (@lem3861671) (@lem3861672 _44750)). Qed.
Lemma lem3861674 (_44750 : int) : (term497 _44750) = (term513 _44750).
Proof. exact (TRANS (@lem3861571 _44750) (@lem3861673 _44750)). Qed.
Lemma lem3861675 (_44750 : int) : (term513 _44750) = term133.
Proof. exact (@lem1982719 (real_of_int _44750)). Qed.
Lemma lem3861676 (_44750 : int) : (term497 _44750) = term133.
Proof. exact (TRANS (@lem3861674 _44750) (@lem3861675 _44750)). Qed.
Lemma lem3861677 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3861678 (_44750 : int) : (term514 _44750) = term175.
Proof. exact (MK_COMB (@lem3861677) (@lem3861676 _44750)). Qed.
Lemma lem3861679 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3861680 (_44750 : int) : (term574 _44750) = term519.
Proof. exact (MK_COMB (@lem3861678 _44750) (@lem3861679)). Qed.
Lemma lem3861681 (_44750 : int) : (term573 _44750) = term519.
Proof. exact (TRANS (@lem3861570 _44750) (@lem3861680 _44750)). Qed.
Lemma lem3861682 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3861683 (_44750 : int) : (term573 _44750) = term199.
Proof. exact (TRANS (@lem3861681 _44750) (@lem3861682)). Qed.
Lemma lem3861684 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3861685 (_44750 : int) : (term575 _44750) = term521.
Proof. exact (MK_COMB (@lem3861684) (@lem3861683 _44750)). Qed.
Lemma lem3861686 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3861687 (_44750 : int) : (term572 _44750) = term522.
Proof. exact (MK_COMB (@lem3861685 _44750) (@lem3861686)). Qed.
Lemma lem3861688 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : term522.
Proof. exact (EQ_MP (@lem3861687 _44750) (@lem3861569 _44749 _44750 h1)). Qed.
Lemma lem3861690 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3861691 : term522 = term523.
Proof. exact (@lem3861690 term133 term199). Qed.
Lemma lem3861693 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3861694 : term199 = term200.
Proof. exact (@lem3861693 term11). Qed.
Lemma lem3861696 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861697 : term133 = term196.
Proof. exact (@lem3861696 (NUMERAL 0)). Qed.
Lemma lem3861698 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3861699 : term135 = term524.
Proof. exact (MK_COMB (@lem3861698) (@lem3861697)). Qed.
Lemma lem3861700 : term523 = term525.
Proof. exact (MK_COMB (@lem3861699) (@lem3861694)). Qed.
Lemma lem3861701 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3861703 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861704 : term251 = term252.
Proof. exact (@lem3861703 (NUMERAL 0) term11). Qed.
Lemma lem3861705 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861706 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861707 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861706 h1) (fun h1 : term252 = True => @lem3861705)). Qed.
Lemma lem3861708 : term252 = True.
Proof. exact (EQ_MP (@lem3861707) (@lem3861705)). Qed.
Lemma lem3861709 : term251 = True.
Proof. exact (TRANS (@lem3861704) (@lem3861708)). Qed.
Lemma lem3861710 : True = term251.
Proof. exact (SYM (@lem3861709)). Qed.
Lemma lem3861711 : term251.
Proof. exact (EQ_MP (@lem3861710) (@lem0)). Qed.
Lemma lem3861712 : term527.
Proof. exact (@lem3861701 (@lem3861711)). Qed.
Lemma lem3861714 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861715 : term251 = term252.
Proof. exact (@lem3861714 (NUMERAL 0) term11). Qed.
Lemma lem3861716 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861717 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861718 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861717 h1) (fun h1 : term252 = True => @lem3861716)). Qed.
Lemma lem3861719 : term252 = True.
Proof. exact (EQ_MP (@lem3861718) (@lem3861716)). Qed.
Lemma lem3861720 : term251 = True.
Proof. exact (TRANS (@lem3861715) (@lem3861719)). Qed.
Lemma lem3861721 : True = term251.
Proof. exact (SYM (@lem3861720)). Qed.
Lemma lem3861722 : term251.
Proof. exact (EQ_MP (@lem3861721) (@lem0)). Qed.
Lemma lem3861723 : term525 = term528.
Proof. exact (@lem3861712 (@lem3861722)). Qed.
Lemma lem3861725 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3861726 : term225 = term230.
Proof. exact (@lem3861725 term11 term11). Qed.
Lemma lem3861727 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861728 : term211 = term11.
Proof. exact (EQ_MP (@lem3861727) (@lem940073)). Qed.
Lemma lem3861729 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861730 : term209 = term143.
Proof. exact (MK_COMB (@lem3861729) (@lem3861728)). Qed.
Lemma lem3861731 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3861732 : term230 = term199.
Proof. exact (MK_COMB (@lem3861731) (@lem3861730)). Qed.
Lemma lem3861733 : term225 = term199.
Proof. exact (TRANS (@lem3861726) (@lem3861732)). Qed.
Lemma lem3861735 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861736 : term263 = term133.
Proof. exact (@lem3861735 term11). Qed.
Lemma lem3861737 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3861738 : term529 = term135.
Proof. exact (MK_COMB (@lem3861737) (@lem3861736)). Qed.
Lemma lem3861739 : term528 = term523.
Proof. exact (MK_COMB (@lem3861738) (@lem3861733)). Qed.
Lemma lem3861741 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3861742 : term523 = term532.
Proof. exact (@lem3861741 (NUMERAL 0) term11). Qed.
Lemma lem3861743 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861744 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3861745 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861744 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3861743)). Qed.
Lemma lem3861746 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3861745) (@lem3861743)). Qed.
Lemma lem3861747 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3861748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3861749 : term533 = (and True).
Proof. exact (MK_COMB (@lem3861748) (@lem3861747)). Qed.
Lemma lem3861750 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3861749) (@lem3861746)). Qed.
Lemma lem3861752 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3861753 : term532 = False.
Proof. exact (TRANS (@lem3861750) (@lem3861752)). Qed.
Lemma lem3861754 : term523 = False.
Proof. exact (TRANS (@lem3861742) (@lem3861753)). Qed.
Lemma lem3861755 : term528 = False.
Proof. exact (TRANS (@lem3861739) (@lem3861754)). Qed.
Lemma lem3861756 : term525 = False.
Proof. exact (TRANS (@lem3861723) (@lem3861755)). Qed.
Lemma lem3861757 : term523 = False.
Proof. exact (TRANS (@lem3861700) (@lem3861756)). Qed.
Lemma lem3861758 : term522 = False.
Proof. exact (TRANS (@lem3861691) (@lem3861757)). Qed.
Lemma lem3861759 (_44749 : int) (_44750 : int) (h1 : term622 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3861758) (@lem3861688 _44749 _44750 h1)). Qed.
Lemma lem3861760 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term625 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3861761 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term430 _44749 _44750.
Proof. exact (proj2 (@lem3861760 _44749 _44750 h1)). Qed.
Lemma lem3861763 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term381 _44749 _44750.
Proof. exact (proj2 (@lem3861761 _44749 _44750 h1)). Qed.
Lemma lem3861765 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term336 _44750.
Proof. exact (proj2 (@lem3861763 _44749 _44750 h1)). Qed.
Lemma lem3861769 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term302 _44750.
Proof. exact (proj2 (@lem3861765 _44749 _44750 h1)). Qed.
Lemma lem3861770 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : (real_of_int _44750) = term133.
Proof. exact (proj1 (@lem3861765 _44749 _44750 h1)). Qed.
Lemma lem3861772 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3861773 : term471 = term251.
Proof. exact (@lem3861772 term133 term143). Qed.
Lemma lem3861775 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861776 : term143 = term224.
Proof. exact (@lem3861775 term11). Qed.
Lemma lem3861778 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861779 : term133 = term196.
Proof. exact (@lem3861778 (NUMERAL 0)). Qed.
Lemma lem3861780 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3861781 : term472 = term473.
Proof. exact (MK_COMB (@lem3861780) (@lem3861779)). Qed.
Lemma lem3861782 : term251 = term474.
Proof. exact (MK_COMB (@lem3861781) (@lem3861776)). Qed.
Lemma lem3861783 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3861785 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861786 : term251 = term252.
Proof. exact (@lem3861785 (NUMERAL 0) term11). Qed.
Lemma lem3861787 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861788 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861789 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861788 h1) (fun h1 : term252 = True => @lem3861787)). Qed.
Lemma lem3861790 : term252 = True.
Proof. exact (EQ_MP (@lem3861789) (@lem3861787)). Qed.
Lemma lem3861791 : term251 = True.
Proof. exact (TRANS (@lem3861786) (@lem3861790)). Qed.
Lemma lem3861792 : True = term251.
Proof. exact (SYM (@lem3861791)). Qed.
Lemma lem3861793 : term251.
Proof. exact (EQ_MP (@lem3861792) (@lem0)). Qed.
Lemma lem3861794 : term476.
Proof. exact (@lem3861783 (@lem3861793)). Qed.
Lemma lem3861796 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861797 : term251 = term252.
Proof. exact (@lem3861796 (NUMERAL 0) term11). Qed.
Lemma lem3861798 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861799 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861800 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861799 h1) (fun h1 : term252 = True => @lem3861798)). Qed.
Lemma lem3861801 : term252 = True.
Proof. exact (EQ_MP (@lem3861800) (@lem3861798)). Qed.
Lemma lem3861802 : term251 = True.
Proof. exact (TRANS (@lem3861797) (@lem3861801)). Qed.
Lemma lem3861803 : True = term251.
Proof. exact (SYM (@lem3861802)). Qed.
Lemma lem3861804 : term251.
Proof. exact (EQ_MP (@lem3861803) (@lem0)). Qed.
Lemma lem3861805 : term474 = term477.
Proof. exact (@lem3861794 (@lem3861804)). Qed.
Lemma lem3861807 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3861808 : term208 = term209.
Proof. exact (@lem3861807 term11 term11). Qed.
Lemma lem3861809 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861810 : term211 = term11.
Proof. exact (EQ_MP (@lem3861809) (@lem940073)). Qed.
Lemma lem3861811 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861812 : term209 = term143.
Proof. exact (MK_COMB (@lem3861811) (@lem3861810)). Qed.
Lemma lem3861813 : term208 = term143.
Proof. exact (TRANS (@lem3861808) (@lem3861812)). Qed.
Lemma lem3861815 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861816 : term263 = term133.
Proof. exact (@lem3861815 term11). Qed.
Lemma lem3861817 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3861818 : term478 = term472.
Proof. exact (MK_COMB (@lem3861817) (@lem3861816)). Qed.
Lemma lem3861819 : term477 = term251.
Proof. exact (MK_COMB (@lem3861818) (@lem3861813)). Qed.
Lemma lem3861821 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861822 : term251 = term252.
Proof. exact (@lem3861821 (NUMERAL 0) term11). Qed.
Lemma lem3861823 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861824 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861825 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861824 h1) (fun h1 : term252 = True => @lem3861823)). Qed.
Lemma lem3861826 : term252 = True.
Proof. exact (EQ_MP (@lem3861825) (@lem3861823)). Qed.
Lemma lem3861827 : term251 = True.
Proof. exact (TRANS (@lem3861822) (@lem3861826)). Qed.
Lemma lem3861828 : term477 = True.
Proof. exact (TRANS (@lem3861819) (@lem3861827)). Qed.
Lemma lem3861829 : term474 = True.
Proof. exact (TRANS (@lem3861805) (@lem3861828)). Qed.
Lemma lem3861830 : term251 = True.
Proof. exact (TRANS (@lem3861782) (@lem3861829)). Qed.
Lemma lem3861831 : term471 = True.
Proof. exact (TRANS (@lem3861773) (@lem3861830)). Qed.
Lemma lem3861832 : True = term471.
Proof. exact (SYM (@lem3861831)). Qed.
Lemma lem3861833 : term471.
Proof. exact (EQ_MP (@lem3861832) (@lem0)). Qed.
Lemma lem3861834 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term551 _44750.
Proof. exact (conj (@lem3861833) (@lem3861769 _44749 _44750 h1)). Qed.
Lemma lem3861836 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3861837 (_44750 : int) : term552 _44750.
Proof. exact (@lem3861836 term143 (term299 _44750)). Qed.
Lemma lem3861838 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term553 _44750.
Proof. exact (@lem3861837 _44750 (@lem3861834 _44749 _44750 h1)). Qed.
Lemma lem3861839 (_44750 : int) : (term554 _44750) = (term299 _44750).
Proof. exact (@lem1982733 (term299 _44750)). Qed.
Lemma lem3861840 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3861841 (_44750 : int) : (term555 _44750) = (term301 _44750).
Proof. exact (MK_COMB (@lem3861840) (@lem3861839 _44750)). Qed.
Lemma lem3861842 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3861843 (_44750 : int) : (term553 _44750) = (term302 _44750).
Proof. exact (MK_COMB (@lem3861841 _44750) (@lem3861842)). Qed.
Lemma lem3861844 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term302 _44750.
Proof. exact (EQ_MP (@lem3861843 _44750) (@lem3861838 _44749 _44750 h1)). Qed.
Lemma lem3861846 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3861847 (_44750 : int) : term539 _44750.
Proof. exact (@lem3861846 (real_of_int _44750)). Qed.
Lemma lem3861848 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term540 _44750.
Proof. exact (@lem3861847 _44750 (@lem3861770 _44749 _44750 h1)). Qed.
Lemma lem3861849 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term556 _44750.
Proof. exact (@lem3861848 _44749 _44750 h1 term199). Qed.
Lemma lem3861850 (_44750 : int) : (term556 _44750) = ((term237 _44750) = term133).
Proof. exact (eq_refl (term556 _44750)). Qed.
Lemma lem3861857 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : (term237 _44750) = term133.
Proof. exact (EQ_MP (@lem3861850 _44750) (@lem3861849 _44749 _44750 h1)). Qed.
Lemma lem3861858 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term623 _44750.
Proof. exact (conj (@lem3861857 _44749 _44750 h1) (@lem3861844 _44749 _44750 h1)). Qed.
Lemma lem3861860 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3861861 (_44750 : int) : term624 _44750.
Proof. exact (@lem3861860 (term237 _44750) (term299 _44750)). Qed.
Lemma lem3861862 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term572 _44750.
Proof. exact (@lem3861861 _44750 (@lem3861858 _44749 _44750 h1)). Qed.
Lemma lem3861863 (_44750 : int) : (term573 _44750) = (term574 _44750).
Proof. exact (@lem1982763 (term237 _44750) (real_of_int _44750) term199). Qed.
Lemma lem3861864 (_44750 : int) : (term497 _44750) = (term498 _44750).
Proof. exact (@lem1982713 term199 (real_of_int _44750)). Qed.
Lemma lem3861866 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861867 : term143 = term224.
Proof. exact (@lem3861866 term11). Qed.
Lemma lem3861869 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3861870 : term199 = term200.
Proof. exact (@lem3861869 term11). Qed.
Lemma lem3861871 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3861872 : term499 = term500.
Proof. exact (MK_COMB (@lem3861871) (@lem3861870)). Qed.
Lemma lem3861873 : term501 = term502.
Proof. exact (MK_COMB (@lem3861872) (@lem3861867)). Qed.
Lemma lem3861874 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3861876 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861877 : term251 = term252.
Proof. exact (@lem3861876 (NUMERAL 0) term11). Qed.
Lemma lem3861878 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861879 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861880 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861879 h1) (fun h1 : term252 = True => @lem3861878)). Qed.
Lemma lem3861881 : term252 = True.
Proof. exact (EQ_MP (@lem3861880) (@lem3861878)). Qed.
Lemma lem3861882 : term251 = True.
Proof. exact (TRANS (@lem3861877) (@lem3861881)). Qed.
Lemma lem3861883 : True = term251.
Proof. exact (SYM (@lem3861882)). Qed.
Lemma lem3861884 : term251.
Proof. exact (EQ_MP (@lem3861883) (@lem0)). Qed.
Lemma lem3861885 : term504.
Proof. exact (@lem3861874 (@lem3861884)). Qed.
Lemma lem3861887 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861888 : term251 = term252.
Proof. exact (@lem3861887 (NUMERAL 0) term11). Qed.
Lemma lem3861889 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861890 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861891 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861890 h1) (fun h1 : term252 = True => @lem3861889)). Qed.
Lemma lem3861892 : term252 = True.
Proof. exact (EQ_MP (@lem3861891) (@lem3861889)). Qed.
Lemma lem3861893 : term251 = True.
Proof. exact (TRANS (@lem3861888) (@lem3861892)). Qed.
Lemma lem3861894 : True = term251.
Proof. exact (SYM (@lem3861893)). Qed.
Lemma lem3861895 : term251.
Proof. exact (EQ_MP (@lem3861894) (@lem0)). Qed.
Lemma lem3861896 : term505.
Proof. exact (@lem3861885 (@lem3861895)). Qed.
Lemma lem3861898 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861899 : term251 = term252.
Proof. exact (@lem3861898 (NUMERAL 0) term11). Qed.
Lemma lem3861900 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861901 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3861902 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861901 h1) (fun h1 : term252 = True => @lem3861900)). Qed.
Lemma lem3861903 : term252 = True.
Proof. exact (EQ_MP (@lem3861902) (@lem3861900)). Qed.
Lemma lem3861904 : term251 = True.
Proof. exact (TRANS (@lem3861899) (@lem3861903)). Qed.
Lemma lem3861905 : True = term251.
Proof. exact (SYM (@lem3861904)). Qed.
Lemma lem3861906 : term251.
Proof. exact (EQ_MP (@lem3861905) (@lem0)). Qed.
Lemma lem3861907 : term506.
Proof. exact (@lem3861896 (@lem3861906)). Qed.
Lemma lem3861909 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3861910 : term208 = term209.
Proof. exact (@lem3861909 term11 term11). Qed.
Lemma lem3861911 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861912 : term211 = term11.
Proof. exact (EQ_MP (@lem3861911) (@lem940073)). Qed.
Lemma lem3861913 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861914 : term209 = term143.
Proof. exact (MK_COMB (@lem3861913) (@lem3861912)). Qed.
Lemma lem3861915 : term208 = term143.
Proof. exact (TRANS (@lem3861910) (@lem3861914)). Qed.
Lemma lem3861917 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3861918 : term225 = term230.
Proof. exact (@lem3861917 term11 term11). Qed.
Lemma lem3861919 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861920 : term211 = term11.
Proof. exact (EQ_MP (@lem3861919) (@lem940073)). Qed.
Lemma lem3861921 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861922 : term209 = term143.
Proof. exact (MK_COMB (@lem3861921) (@lem3861920)). Qed.
Lemma lem3861923 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3861924 : term230 = term199.
Proof. exact (MK_COMB (@lem3861923) (@lem3861922)). Qed.
Lemma lem3861925 : term225 = term199.
Proof. exact (TRANS (@lem3861918) (@lem3861924)). Qed.
Lemma lem3861926 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3861927 : term507 = term499.
Proof. exact (MK_COMB (@lem3861926) (@lem3861925)). Qed.
Lemma lem3861928 : term508 = term501.
Proof. exact (MK_COMB (@lem3861927) (@lem3861915)). Qed.
Lemma lem3861930 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3861931 : term501 = term133.
Proof. exact (@lem3861930 term11). Qed.
Lemma lem3861932 : term508 = term133.
Proof. exact (TRANS (@lem3861928) (@lem3861931)). Qed.
Lemma lem3861933 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3861934 : term510 = term261.
Proof. exact (MK_COMB (@lem3861933) (@lem3861932)). Qed.
Lemma lem3861935 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3861936 : term511 = term263.
Proof. exact (MK_COMB (@lem3861934) (@lem3861935)). Qed.
Lemma lem3861938 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861939 : term263 = term133.
Proof. exact (@lem3861938 term11). Qed.
Lemma lem3861940 : term511 = term133.
Proof. exact (TRANS (@lem3861936) (@lem3861939)). Qed.
Lemma lem3861942 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3861943 : term208 = term209.
Proof. exact (@lem3861942 term11 term11). Qed.
Lemma lem3861944 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3861945 : term211 = term11.
Proof. exact (EQ_MP (@lem3861944) (@lem940073)). Qed.
Lemma lem3861946 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3861947 : term209 = term143.
Proof. exact (MK_COMB (@lem3861946) (@lem3861945)). Qed.
Lemma lem3861948 : term208 = term143.
Proof. exact (TRANS (@lem3861943) (@lem3861947)). Qed.
Lemma lem3861949 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3861950 : term265 = term263.
Proof. exact (MK_COMB (@lem3861949) (@lem3861948)). Qed.
Lemma lem3861952 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3861953 : term263 = term133.
Proof. exact (@lem3861952 term11). Qed.
Lemma lem3861954 : term265 = term133.
Proof. exact (TRANS (@lem3861950) (@lem3861953)). Qed.
Lemma lem3861955 : term133 = term265.
Proof. exact (SYM (@lem3861954)). Qed.
Lemma lem3861956 : term511 = term265.
Proof. exact (TRANS (@lem3861940) (@lem3861955)). Qed.
Lemma lem3861957 : term502 = term196.
Proof. exact (@lem3861907 (@lem3861956)). Qed.
Lemma lem3861958 : term501 = term196.
Proof. exact (TRANS (@lem3861873) (@lem3861957)). Qed.
Lemma lem3861960 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3861961 : term196 = term133.
Proof. exact (@lem3861960 term133). Qed.
Lemma lem3861962 : term501 = term133.
Proof. exact (TRANS (@lem3861958) (@lem3861961)). Qed.
Lemma lem3861963 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3861964 : term512 = term261.
Proof. exact (MK_COMB (@lem3861963) (@lem3861962)). Qed.
Lemma lem3861965 (_44750 : int) : (real_of_int _44750) = (real_of_int _44750).
Proof. exact (eq_refl (real_of_int _44750)). Qed.
Lemma lem3861966 (_44750 : int) : (term498 _44750) = (term513 _44750).
Proof. exact (MK_COMB (@lem3861964) (@lem3861965 _44750)). Qed.
Lemma lem3861967 (_44750 : int) : (term497 _44750) = (term513 _44750).
Proof. exact (TRANS (@lem3861864 _44750) (@lem3861966 _44750)). Qed.
Lemma lem3861968 (_44750 : int) : (term513 _44750) = term133.
Proof. exact (@lem1982719 (real_of_int _44750)). Qed.
Lemma lem3861969 (_44750 : int) : (term497 _44750) = term133.
Proof. exact (TRANS (@lem3861967 _44750) (@lem3861968 _44750)). Qed.
Lemma lem3861970 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3861971 (_44750 : int) : (term514 _44750) = term175.
Proof. exact (MK_COMB (@lem3861970) (@lem3861969 _44750)). Qed.
Lemma lem3861972 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3861973 (_44750 : int) : (term574 _44750) = term519.
Proof. exact (MK_COMB (@lem3861971 _44750) (@lem3861972)). Qed.
Lemma lem3861974 (_44750 : int) : (term573 _44750) = term519.
Proof. exact (TRANS (@lem3861863 _44750) (@lem3861973 _44750)). Qed.
Lemma lem3861975 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3861976 (_44750 : int) : (term573 _44750) = term199.
Proof. exact (TRANS (@lem3861974 _44750) (@lem3861975)). Qed.
Lemma lem3861977 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3861978 (_44750 : int) : (term575 _44750) = term521.
Proof. exact (MK_COMB (@lem3861977) (@lem3861976 _44750)). Qed.
Lemma lem3861979 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3861980 (_44750 : int) : (term572 _44750) = term522.
Proof. exact (MK_COMB (@lem3861978 _44750) (@lem3861979)). Qed.
Lemma lem3861981 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : term522.
Proof. exact (EQ_MP (@lem3861980 _44750) (@lem3861862 _44749 _44750 h1)). Qed.
Lemma lem3861983 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3861984 : term522 = term523.
Proof. exact (@lem3861983 term133 term199). Qed.
Lemma lem3861986 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3861987 : term199 = term200.
Proof. exact (@lem3861986 term11). Qed.
Lemma lem3861989 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3861990 : term133 = term196.
Proof. exact (@lem3861989 (NUMERAL 0)). Qed.
Lemma lem3861991 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3861992 : term135 = term524.
Proof. exact (MK_COMB (@lem3861991) (@lem3861990)). Qed.
Lemma lem3861993 : term523 = term525.
Proof. exact (MK_COMB (@lem3861992) (@lem3861987)). Qed.
Lemma lem3861994 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3861996 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3861997 : term251 = term252.
Proof. exact (@lem3861996 (NUMERAL 0) term11). Qed.
Lemma lem3861998 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3861999 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3862000 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3861999 h1) (fun h1 : term252 = True => @lem3861998)). Qed.
Lemma lem3862001 : term252 = True.
Proof. exact (EQ_MP (@lem3862000) (@lem3861998)). Qed.
Lemma lem3862002 : term251 = True.
Proof. exact (TRANS (@lem3861997) (@lem3862001)). Qed.
Lemma lem3862003 : True = term251.
Proof. exact (SYM (@lem3862002)). Qed.
Lemma lem3862004 : term251.
Proof. exact (EQ_MP (@lem3862003) (@lem0)). Qed.
Lemma lem3862005 : term527.
Proof. exact (@lem3861994 (@lem3862004)). Qed.
Lemma lem3862007 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3862008 : term251 = term252.
Proof. exact (@lem3862007 (NUMERAL 0) term11). Qed.
Lemma lem3862009 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3862010 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3862011 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3862010 h1) (fun h1 : term252 = True => @lem3862009)). Qed.
Lemma lem3862012 : term252 = True.
Proof. exact (EQ_MP (@lem3862011) (@lem3862009)). Qed.
Lemma lem3862013 : term251 = True.
Proof. exact (TRANS (@lem3862008) (@lem3862012)). Qed.
Lemma lem3862014 : True = term251.
Proof. exact (SYM (@lem3862013)). Qed.
Lemma lem3862015 : term251.
Proof. exact (EQ_MP (@lem3862014) (@lem0)). Qed.
Lemma lem3862016 : term525 = term528.
Proof. exact (@lem3862005 (@lem3862015)). Qed.
Lemma lem3862018 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3862019 : term225 = term230.
Proof. exact (@lem3862018 term11 term11). Qed.
Lemma lem3862020 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3862021 : term211 = term11.
Proof. exact (EQ_MP (@lem3862020) (@lem940073)). Qed.
Lemma lem3862022 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3862023 : term209 = term143.
Proof. exact (MK_COMB (@lem3862022) (@lem3862021)). Qed.
Lemma lem3862024 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3862025 : term230 = term199.
Proof. exact (MK_COMB (@lem3862024) (@lem3862023)). Qed.
Lemma lem3862026 : term225 = term199.
Proof. exact (TRANS (@lem3862019) (@lem3862025)). Qed.
Lemma lem3862028 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3862029 : term263 = term133.
Proof. exact (@lem3862028 term11). Qed.
Lemma lem3862030 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3862031 : term529 = term135.
Proof. exact (MK_COMB (@lem3862030) (@lem3862029)). Qed.
Lemma lem3862032 : term528 = term523.
Proof. exact (MK_COMB (@lem3862031) (@lem3862026)). Qed.
Lemma lem3862034 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3862035 : term523 = term532.
Proof. exact (@lem3862034 (NUMERAL 0) term11). Qed.
Lemma lem3862036 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3862037 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3862038 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3862037 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3862036)). Qed.
Lemma lem3862039 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3862038) (@lem3862036)). Qed.
Lemma lem3862040 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3862041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3862042 : term533 = (and True).
Proof. exact (MK_COMB (@lem3862041) (@lem3862040)). Qed.
Lemma lem3862043 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3862042) (@lem3862039)). Qed.
Lemma lem3862045 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3862046 : term532 = False.
Proof. exact (TRANS (@lem3862043) (@lem3862045)). Qed.
Lemma lem3862047 : term523 = False.
Proof. exact (TRANS (@lem3862035) (@lem3862046)). Qed.
Lemma lem3862048 : term528 = False.
Proof. exact (TRANS (@lem3862032) (@lem3862047)). Qed.
Lemma lem3862049 : term525 = False.
Proof. exact (TRANS (@lem3862016) (@lem3862048)). Qed.
Lemma lem3862050 : term523 = False.
Proof. exact (TRANS (@lem3861993) (@lem3862049)). Qed.
Lemma lem3862051 : term522 = False.
Proof. exact (TRANS (@lem3861984) (@lem3862050)). Qed.
Lemma lem3862052 (_44749 : int) (_44750 : int) (h1 : term625 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3862051) (@lem3861981 _44749 _44750 h1)). Qed.
Lemma lem3862053 (_44749 : int) (_44750 : int) (h1 : term428 _44749 _44750) : False.
Proof. exact (or_elim (@lem3861468 _44749 _44750 h1) (fun h0 : term622 _44749 _44750 => @lem3861759 _44749 _44750 h0) (fun h0 : term625 _44749 _44750 => @lem3862052 _44749 _44750 h0)). Qed.
Lemma lem3862054 (_44749 : int) (_44750 : int) (h1 : term437 _44749 _44750) : False.
Proof. exact (or_elim (@lem3860496 _44749 _44750 h1) (fun h0 : term432 _44749 _44750 => @lem3861467 _44749 _44750 h0) (fun h0 : term428 _44749 _44750 => @lem3862053 _44749 _44750 h0)). Qed.
Lemma lem3862055 (_44749 : int) (_44750 : int) (h1 : term453 _44749 _44750) : False.
Proof. exact (or_elim (@lem3859147 _44749 _44750 h1) (fun h0 : term450 _44749 _44750 => @lem3860495 _44749 _44750 h0) (fun h0 : term437 _44749 _44750 => @lem3862054 _44749 _44750 h0)). Qed.
Lemma lem3862056 (_44749 : int) (_44750 : int) (h1 : term469 _44749 _44750) : False.
Proof. exact (or_elim (@lem3856946 _44749 _44750 h1) (fun h0 : term466 _44749 _44750 => @lem3859146 _44749 _44750 h0) (fun h0 : term453 _44749 _44750 => @lem3862055 _44749 _44750 h0)). Qed.
Lemma lem3862058 (_44749 : int) (_44750 : int) (h1 : term469 _44749 _44750) : term469 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3862059 (_44749 : int) (_44750 : int) (h1 : term469 _44749 _44750) : (term469 _44749 _44750) = False.
Proof. exact (prop_ext (fun h2 : term469 _44749 _44750 => @lem3862056 _44749 _44750 h1) (fun h2 : False => @lem3862058 _44749 _44750 h1)). Qed.
Lemma lem3862060 (_44749 : int) (_44750 : int) (h1 : term469 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3862059 _44749 _44750 h1) (@lem3862058 _44749 _44750 h1)). Qed.
Lemma lem3862061 (_44749 : int) (_44750 : int) (h1 : term191 _44749 _44750) : term191 _44749 _44750.
Proof. exact (h1). Qed.
Lemma lem3862062 (_44749 : int) (_44750 : int) (h1 : term191 _44749 _44750) : term469 _44749 _44750.
Proof. exact (EQ_MP (@lem3856876 _44749 _44750) (@lem3862061 _44749 _44750 h1)). Qed.
Lemma lem3862063 (_44749 : int) (_44750 : int) (h1 : term191 _44749 _44750) : (term469 _44749 _44750) = False.
Proof. exact (prop_ext (fun h2 : term469 _44749 _44750 => @lem3862060 _44749 _44750 h2) (fun h2 : False => @lem3862062 _44749 _44750 h1)). Qed.
Lemma lem3862064 (_44749 : int) (_44750 : int) (h1 : term191 _44749 _44750) : False.
Proof. exact (EQ_MP (@lem3862063 _44749 _44750 h1) (@lem3862062 _44749 _44750 h1)). Qed.
Lemma lem3862065 (_44749 : int) (_44750 : int) : term626 _44749 _44750.
Proof. exact (fun h0 : term191 _44749 _44750 => @lem3862064 _44749 _44750 h0). Qed.
Lemma lem3862066 (_44749 : int) (_44750 : int) : term627 _44749 _44750.
Proof. exact (@lem1386578 (term628 _44749 _44750)). Qed.
Lemma lem3862069 (_44749 : int) (_44750 : int) : term628 _44749 _44750.
Proof. exact (@lem3862066 _44749 _44750 (@lem3862065 _44749 _44750)). Qed.
Lemma lem3862070 (_44749 : int) (_44750 : int) : (term189 _44749 _44750) = (term127 _44749 _44750).
Proof. exact (SYM (@lem3855815 _44749 _44750)). Qed.
Lemma lem3862071 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3862072 (_44749 : int) (_44750 : int) : (term628 _44749 _44750) = (term73 _44749 _44750).
Proof. exact (MK_COMB (@lem3862071) (@lem3862070 _44749 _44750)). Qed.
Lemma lem3862073 (_44749 : int) (_44750 : int) : term73 _44749 _44750.
Proof. exact (EQ_MP (@lem3862072 _44749 _44750) (@lem3862069 _44749 _44750)). Qed.
Lemma lem3862074 (_44749 : int) (_44750 : int) : term74 _44749 _44750.
Proof. exact (EQ_MP (@lem3855502 _44749 _44750) (@lem3862073 _44749 _44750)). Qed.
Lemma lem3862075 (d : nat) (n : nat) : term629 d n.
Proof. exact (@lem3862074 (int_of_num d) (int_of_num n)). Qed.
Lemma lem3862076 (d : nat) (n : nat) : term630 d n.
Proof. exact (@lem3862075 d n (@lem3855498 d)). Qed.
Lemma lem3862077 (d : nat) (n : nat) : term68 d n.
Proof. exact (@lem3862076 d n (@lem3855501 n)). Qed.
Lemma lem3862078 (n : nat) : term70 n.
Proof. exact (fun d : nat => @lem3862077 d n). Qed.
Lemma lem3862079 (n : nat) : (term70 n) = ((term7 n) = (term8 n)).
Proof. exact (SYM (@lem3855495 n)). Qed.
Lemma lem3862081 {A : Type'} (s : A -> Prop) : term631 A s.
Proof. exact (@lem9784 (s = (@EMPTY A))). Qed.
Lemma lem3862082 {A : Type'} (s : A -> Prop) : (term631 A s) = (term632 A s).
Proof. exact (eq_refl (term631 A s)). Qed.
Lemma lem3862083 {A : Type'} (s : A -> Prop) : term632 A s.
Proof. exact (EQ_MP (@lem3862082 A s) (@lem3862081 A s)). Qed.
Lemma lem3862085 {A : Type'} (s : A -> Prop) (h1 : term633 A s) : term633 A s.
Proof. exact (h1). Qed.
Lemma lem3862086 {A : Type'} (P : type686 A) (h1 : term634 A P) : term634 A P.
Proof. exact (h1). Qed.
Lemma lem3862087 {A : Type'} (P : type686 A) (h1 : term635 A P) : term635 A P.
Proof. exact (h1). Qed.
Lemma lem3862088 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) : P (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3862089 (P : nat -> Prop) : term636 P.
Proof. exact (@lem115780 P). Qed.
Lemma lem3862090 (P : nat -> Prop) : (term636 P) = (term637 P).
Proof. exact (eq_refl (term636 P)). Qed.
Lemma lem3862093 (P : nat -> Prop) : term637 P.
Proof. exact (EQ_MP (@lem3862090 P) (@lem3862089 P)). Qed.
Lemma lem3862094 {A : Type'} (P : type686 A) : term638 A P.
Proof. exact (@lem3862093 (term639 A P)). Qed.
Lemma lem3862095 {A : Type'} (m : nat) (P : type686 A) : (term640 A P m) = (term641 A m P).
Proof. exact (eq_refl (term640 A P m)). Qed.
Lemma lem3862096 (m : nat) (_44753 : nat) : (term642 m _44753) = (term642 m _44753).
Proof. exact (eq_refl (term642 m _44753)). Qed.
Lemma lem3862097 {A : Type'} (_44753 : nat) (m : nat) (P : type686 A) : (term643 A _44753 P m) = (term644 A _44753 m P).
Proof. exact (MK_COMB (@lem3862096 m _44753) (@lem3862095 A m P)). Qed.
Lemma lem3862098 {A : Type'} (_44753 : nat) (P : type686 A) : (term645 A _44753 P) = (term646 A _44753 P).
Proof. exact (fun_ext (fun m : nat => @lem3862097 A _44753 m P)). Qed.
Lemma lem3862099 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3862100 {A : Type'} (_44753 : nat) (P : type686 A) : (term647 A _44753 P) = (term648 A _44753 P).
Proof. exact (MK_COMB (@lem3862099) (@lem3862098 A _44753 P)). Qed.
Lemma lem3862101 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862102 {A : Type'} (_44753 : nat) (P : type686 A) : (term649 A _44753 P) = (term650 A _44753 P).
Proof. exact (MK_COMB (@lem3862101) (@lem3862100 A _44753 P)). Qed.
Lemma lem3862103 {A : Type'} (_44753 : nat) (P : type686 A) : (term640 A P _44753) = (term641 A _44753 P).
Proof. exact (eq_refl (term640 A P _44753)). Qed.
Lemma lem3862104 {A : Type'} (_44753 : nat) (P : type686 A) : (term651 A P _44753) = (term652 A _44753 P).
Proof. exact (MK_COMB (@lem3862102 A _44753 P) (@lem3862103 A _44753 P)). Qed.
Lemma lem3862105 {A : Type'} (P : type686 A) : (term653 A P) = (term654 A P).
Proof. exact (fun_ext (fun _44753 : nat => @lem3862104 A _44753 P)). Qed.
Lemma lem3862106 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3862107 {A : Type'} (P : type686 A) : (term655 A P) = (term656 A P).
Proof. exact (MK_COMB (@lem3862106) (@lem3862105 A P)). Qed.
Lemma lem3862108 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862109 {A : Type'} (P : type686 A) : (term657 A P) = (term658 A P).
Proof. exact (MK_COMB (@lem3862108) (@lem3862107 A P)). Qed.
Lemma lem3862110 {A : Type'} (_44753 : nat) (P : type686 A) : (term640 A P _44753) = (term641 A _44753 P).
Proof. exact (eq_refl (term640 A P _44753)). Qed.
Lemma lem3862111 {A : Type'} (P : type686 A) : (term659 A P) = (term639 A P).
Proof. exact (fun_ext (fun _44753 : nat => @lem3862110 A _44753 P)). Qed.
Lemma lem3862112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3862113 {A : Type'} (P : type686 A) : (term660 A P) = (term661 A P).
Proof. exact (MK_COMB (@lem3862112) (@lem3862111 A P)). Qed.
Lemma lem3862114 {A : Type'} (P : type686 A) : (term638 A P) = (term662 A P).
Proof. exact (MK_COMB (@lem3862109 A P) (@lem3862113 A P)). Qed.
Lemma lem3862115 {A : Type'} (P : type686 A) : term662 A P.
Proof. exact (EQ_MP (@lem3862114 A P) (@lem3862094 A P)). Qed.
Lemma lem3862116 {A : Type'} (P : type686 A) (h1 : term656 A P) : term656 A P.
Proof. exact (h1). Qed.
Lemma lem3862117 {A : Type'} (P : type686 A) (h1 : term656 A P) : term661 A P.
Proof. exact (@lem3862115 A P (@lem3862116 A P h1)). Qed.
Lemma lem3862118 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem3862119 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term656 A P) : term663 A P s.
Proof. exact (@lem3862117 A P h1 (@CARD A s)). Qed.
Lemma lem3862120 {A : Type'} (s : A -> Prop) (P : type686 A) : (term663 A P s) = (term664 A s P).
Proof. exact (eq_refl (term663 A P s)). Qed.
Lemma lem3862121 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term656 A P) : term664 A s P.
Proof. exact (EQ_MP (@lem3862120 A s P) (@lem3862119 A s P h1)). Qed.
Lemma lem3862122 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term656 A P) : term665 A P s.
Proof. exact (@lem3862121 A s P h1 s). Qed.
Lemma lem3862123 {A : Type'} (P : type686 A) (s : A -> Prop) : (term665 A P s) = (term666 A P s).
Proof. exact (eq_refl (term665 A P s)). Qed.
Lemma lem3862124 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term656 A P) : term666 A P s.
Proof. exact (EQ_MP (@lem3862123 A P s) (@lem3862122 A s P h1)). Qed.
Lemma lem3862125 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term656 A P) : term667 A P s.
Proof. exact (@lem3862124 A s P h1 (@lem3862118 A s)). Qed.
Lemma lem3862126 {A : Type'} (P : type686 A) (s : A -> Prop) : term668 A P s.
Proof. exact (fun h0 : term656 A P => @lem3862125 A s P h0). Qed.
Lemma lem3862128 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term669 _17370 _17371 P Q) = (term670 _17370 _17371 P Q).
Proof. exact (EQ_MP (@lem510983 _17370 _17371 P Q) (@lem511983 _17370 _17371 P Q)). Qed.
Lemma lem3862129 {A : Type'} (P : nat -> Prop) (Q : type1576 A) : (term671 A P Q) = (term672 A P Q).
Proof. exact (@lem3862128 (A -> Prop) nat P Q). Qed.
Lemma lem3862130 {A : Type'} (P : type686 A) : (term673 A P) = (term674 A P).
Proof. exact (@lem3862129 A (term675 A P) (term676 A P)). Qed.
Lemma lem3862131 {A : Type'} (_44753 : nat) (P : type686 A) : (term677 A P _44753) = (term648 A _44753 P).
Proof. exact (eq_refl (term677 A P _44753)). Qed.
Lemma lem3862132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862133 {A : Type'} (_44753 : nat) (P : type686 A) : (term678 A P _44753) = (term650 A _44753 P).
Proof. exact (MK_COMB (@lem3862132) (@lem3862131 A _44753 P)). Qed.
Lemma lem3862134 {A : Type'} (_44753 : nat) (P : type686 A) : (term679 A P _44753) = (term680 A _44753 P).
Proof. exact (eq_refl (term679 A P _44753)). Qed.
Lemma lem3862135 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3862136 {A : Type'} (_44753 : nat) (P : type686 A) (s : A -> Prop) : (term681 A P _44753 s) = (term682 A _44753 P s).
Proof. exact (MK_COMB (@lem3862134 A _44753 P) (@lem3862135 A s)). Qed.
Lemma lem3862137 {A : Type'} (_44753 : nat) (P : type686 A) (s : A -> Prop) : (term682 A _44753 P s) = (term683 A _44753 P s).
Proof. exact (eq_refl (term682 A _44753 P s)). Qed.
Lemma lem3862138 {A : Type'} (_44753 : nat) (P : type686 A) (s : A -> Prop) : (term681 A P _44753 s) = (term683 A _44753 P s).
Proof. exact (TRANS (@lem3862136 A _44753 P s) (@lem3862137 A _44753 P s)). Qed.
Lemma lem3862139 {A : Type'} (_44753 : nat) (P : type686 A) : (term684 A P _44753) = (term680 A _44753 P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3862138 A _44753 P s)). Qed.
Lemma lem3862140 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3862141 {A : Type'} (_44753 : nat) (P : type686 A) : (term685 A P _44753) = (term641 A _44753 P).
Proof. exact (MK_COMB (@lem3862140 A) (@lem3862139 A _44753 P)). Qed.
Lemma lem3862142 {A : Type'} (_44753 : nat) (P : type686 A) : (term686 A P _44753) = (term652 A _44753 P).
Proof. exact (MK_COMB (@lem3862133 A _44753 P) (@lem3862141 A _44753 P)). Qed.
Lemma lem3862143 {A : Type'} (P : type686 A) : (term687 A P) = (term654 A P).
Proof. exact (fun_ext (fun _44753 : nat => @lem3862142 A _44753 P)). Qed.
Lemma lem3862144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3862145 {A : Type'} (P : type686 A) : (term673 A P) = (term656 A P).
Proof. exact (MK_COMB (@lem3862144) (@lem3862143 A P)). Qed.
Lemma lem3862146 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3862147 {A : Type'} (P : type686 A) : (term688 A P) = (term689 A P).
Proof. exact (MK_COMB (@lem3862146) (@lem3862145 A P)). Qed.
Lemma lem3862148 {A : Type'} (_44753 : nat) (P : type686 A) : (term677 A P _44753) = (term648 A _44753 P).
Proof. exact (eq_refl (term677 A P _44753)). Qed.
Lemma lem3862149 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862150 {A : Type'} (_44753 : nat) (P : type686 A) : (term678 A P _44753) = (term650 A _44753 P).
Proof. exact (MK_COMB (@lem3862149) (@lem3862148 A _44753 P)). Qed.
Lemma lem3862151 {A : Type'} (_44753 : nat) (P : type686 A) : (term679 A P _44753) = (term680 A _44753 P).
Proof. exact (eq_refl (term679 A P _44753)). Qed.
Lemma lem3862152 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3862153 {A : Type'} (_44753 : nat) (P : type686 A) (s : A -> Prop) : (term681 A P _44753 s) = (term682 A _44753 P s).
Proof. exact (MK_COMB (@lem3862151 A _44753 P) (@lem3862152 A s)). Qed.
Lemma lem3862154 {A : Type'} (_44753 : nat) (P : type686 A) (s : A -> Prop) : (term682 A _44753 P s) = (term683 A _44753 P s).
Proof. exact (eq_refl (term682 A _44753 P s)). Qed.
Lemma lem3862155 {A : Type'} (_44753 : nat) (P : type686 A) (s : A -> Prop) : (term681 A P _44753 s) = (term683 A _44753 P s).
Proof. exact (TRANS (@lem3862153 A _44753 P s) (@lem3862154 A _44753 P s)). Qed.
Lemma lem3862156 {A : Type'} (_44753 : nat) (P : type686 A) (s : A -> Prop) : (term690 A P _44753 s) = (term691 A _44753 P s).
Proof. exact (MK_COMB (@lem3862150 A _44753 P) (@lem3862155 A _44753 P s)). Qed.
Lemma lem3862157 {A : Type'} (P : type686 A) (s : A -> Prop) : (term692 A P s) = (term693 A P s).
Proof. exact (fun_ext (fun _44753 : nat => @lem3862156 A _44753 P s)). Qed.
Lemma lem3862158 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3862159 {A : Type'} (P : type686 A) (s : A -> Prop) : (term694 A P s) = (term695 A P s).
Proof. exact (MK_COMB (@lem3862158) (@lem3862157 A P s)). Qed.
Lemma lem3862160 {A : Type'} (P : type686 A) : (term696 A P) = (term697 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3862159 A P s)). Qed.
Lemma lem3862161 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3862162 {A : Type'} (P : type686 A) : (term674 A P) = (term698 A P).
Proof. exact (MK_COMB (@lem3862161 A) (@lem3862160 A P)). Qed.
Lemma lem3862163 {A : Type'} (P : type686 A) : ((term673 A P) = (term674 A P)) = ((term656 A P) = (term698 A P)).
Proof. exact (MK_COMB (@lem3862147 A P) (@lem3862162 A P)). Qed.
Lemma lem3862164 {A : Type'} (P : type686 A) : (term656 A P) = (term698 A P).
Proof. exact (EQ_MP (@lem3862163 A P) (@lem3862130 A P)). Qed.
Lemma lem3862166 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : (term699 _17389 P e Q) = (term700 _17389 P e Q).
Proof. exact (EQ_MP (@lem511998 _17389 P e Q) (@lem512702 _17389 P e Q)). Qed.
Lemma lem3862167 (P : nat -> Prop) (e : nat) (Q : Prop) : (term701 P e Q) = (term702 P e Q).
Proof. exact (@lem3862166 nat P e Q). Qed.
Lemma lem3862168 {A : Type'} (P : type686 A) (s : A -> Prop) : (term703 A P s) = (term704 A P s).
Proof. exact (@lem3862167 (term675 A P) (@CARD A s) (term667 A P s)). Qed.
Lemma lem3862169 {A : Type'} (_44753 : nat) (P : type686 A) : (term677 A P _44753) = (term648 A _44753 P).
Proof. exact (eq_refl (term677 A P _44753)). Qed.
Lemma lem3862170 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862171 {A : Type'} (_44753 : nat) (P : type686 A) : (term678 A P _44753) = (term650 A _44753 P).
Proof. exact (MK_COMB (@lem3862170) (@lem3862169 A _44753 P)). Qed.
Lemma lem3862172 {A : Type'} (_44753 : nat) (P : type686 A) (s : A -> Prop) : (term683 A _44753 P s) = (term683 A _44753 P s).
Proof. exact (eq_refl (term683 A _44753 P s)). Qed.
Lemma lem3862173 {A : Type'} (_44753 : nat) (P : type686 A) (s : A -> Prop) : (term705 A _44753 P s) = (term691 A _44753 P s).
Proof. exact (MK_COMB (@lem3862171 A _44753 P) (@lem3862172 A _44753 P s)). Qed.
Lemma lem3862174 {A : Type'} (P : type686 A) (s : A -> Prop) : (term706 A P s) = (term693 A P s).
Proof. exact (fun_ext (fun _44753 : nat => @lem3862173 A _44753 P s)). Qed.
Lemma lem3862175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3862176 {A : Type'} (P : type686 A) (s : A -> Prop) : (term703 A P s) = (term695 A P s).
Proof. exact (MK_COMB (@lem3862175) (@lem3862174 A P s)). Qed.
Lemma lem3862177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3862178 {A : Type'} (P : type686 A) (s : A -> Prop) : (term707 A P s) = (term708 A P s).
Proof. exact (MK_COMB (@lem3862177) (@lem3862176 A P s)). Qed.
Lemma lem3862179 {A : Type'} (s : A -> Prop) (P : type686 A) : (term709 A P s) = (term710 A s P).
Proof. exact (eq_refl (term709 A P s)). Qed.
Lemma lem3862180 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862181 {A : Type'} (s : A -> Prop) (P : type686 A) : (term711 A P s) = (term712 A s P).
Proof. exact (MK_COMB (@lem3862180) (@lem3862179 A s P)). Qed.
Lemma lem3862182 {A : Type'} (P : type686 A) (s : A -> Prop) : (term667 A P s) = (term667 A P s).
Proof. exact (eq_refl (term667 A P s)). Qed.
Lemma lem3862183 {A : Type'} (P : type686 A) (s : A -> Prop) : (term704 A P s) = (term713 A P s).
Proof. exact (MK_COMB (@lem3862181 A s P) (@lem3862182 A P s)). Qed.
Lemma lem3862184 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term703 A P s) = (term704 A P s)) = ((term695 A P s) = (term713 A P s)).
Proof. exact (MK_COMB (@lem3862178 A P s) (@lem3862183 A P s)). Qed.
Lemma lem3862185 {A : Type'} (P : type686 A) (s : A -> Prop) : (term695 A P s) = (term713 A P s).
Proof. exact (EQ_MP (@lem3862184 A P s) (@lem3862168 A P s)). Qed.
Lemma lem3862186 {A : Type'} (P : type686 A) : (term697 A P) = (term714 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3862185 A P s)). Qed.
Lemma lem3862187 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3862188 {A : Type'} (P : type686 A) : (term698 A P) = (term715 A P).
Proof. exact (MK_COMB (@lem3862187 A) (@lem3862186 A P)). Qed.
Lemma lem3862189 {A : Type'} (P : type686 A) : (term656 A P) = (term715 A P).
Proof. exact (TRANS (@lem3862164 A P) (@lem3862188 A P)). Qed.
Lemma lem3862190 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862191 {A : Type'} (P : type686 A) : (term658 A P) = (term716 A P).
Proof. exact (MK_COMB (@lem3862190) (@lem3862189 A P)). Qed.
Lemma lem3862192 {A : Type'} (P : type686 A) (s : A -> Prop) : (term667 A P s) = (term667 A P s).
Proof. exact (eq_refl (term667 A P s)). Qed.
Lemma lem3862193 {A : Type'} (P : type686 A) (s : A -> Prop) : (term668 A P s) = (term717 A P s).
Proof. exact (MK_COMB (@lem3862191 A P) (@lem3862192 A P s)). Qed.
Lemma lem3862194 {A : Type'} (P : type686 A) (s : A -> Prop) : term717 A P s.
Proof. exact (EQ_MP (@lem3862193 A P s) (@lem3862126 A P s)). Qed.
Lemma lem3862195 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term717 A P s) : term717 A P s.
Proof. exact (h1). Qed.
Lemma lem3862196 {A : Type'} (P : type686 A) (h1 : term715 A P) : term715 A P.
Proof. exact (h1). Qed.
Lemma lem3862197 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term715 A P) (h2 : term717 A P s) : term667 A P s.
Proof. exact (@lem3862195 A P s h2 (@lem3862196 A P h1)). Qed.
Lemma lem3862198 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term715 A P) : term718 A P s.
Proof. exact (fun h0 : term717 A P s => @lem3862197 A P s h1 h0). Qed.
Lemma lem3862199 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term717 A P s) : term717 A P s.
Proof. exact (h1). Qed.
Lemma lem3862200 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term715 A P) (h2 : term717 A P s) : term667 A P s.
Proof. exact (@lem3862198 A s P h1 (@lem3862199 A P s h2)). Qed.
Lemma lem3862201 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term717 A P s) : term717 A P s.
Proof. exact (fun h0 : term715 A P => @lem3862200 A P s h0 h1). Qed.
Lemma lem3862202 {A : Type'} (P : type686 A) (s : A -> Prop) : term719 A P s.
Proof. exact (fun h0 : term717 A P s => @lem3862201 A P s h0). Qed.
Lemma lem3862205 {A : Type'} (P : type686 A) (s : A -> Prop) : term717 A P s.
Proof. exact (@lem3862202 A P s (@lem3862194 A P s)). Qed.
Lemma lem3862206 {A : Type'} (P : type686 A) (s : A -> Prop) : term717 A P s.
Proof. exact (@lem3862205 A P s). Qed.
Lemma lem3862208 {_17370 _17371 : Type'} (P : _17371 -> Prop) (Q : type1470 _17370 _17371) : (term669 _17370 _17371 P Q) = (term670 _17370 _17371 P Q).
Proof. exact (EQ_MP (@lem510983 _17370 _17371 P Q) (@lem511983 _17370 _17371 P Q)). Qed.
Lemma lem3862209 {A : Type'} (P : nat -> Prop) (Q : type1576 A) : (term671 A P Q) = (term672 A P Q).
Proof. exact (@lem3862208 (A -> Prop) nat P Q). Qed.
Lemma lem3862210 {A : Type'} (s : A -> Prop) (P : type686 A) : (term720 A s P) = (term721 A s P).
Proof. exact (@lem3862209 A (term722 A s) (term676 A P)). Qed.
Lemma lem3862211 {A : Type'} (m : nat) (s : A -> Prop) : (term723 A s m) = (term724 A m s).
Proof. exact (eq_refl (term723 A s m)). Qed.
Lemma lem3862212 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862213 {A : Type'} (m : nat) (s : A -> Prop) : (term725 A s m) = (term726 A m s).
Proof. exact (MK_COMB (@lem3862212) (@lem3862211 A m s)). Qed.
Lemma lem3862214 {A : Type'} (m : nat) (P : type686 A) : (term679 A P m) = (term680 A m P).
Proof. exact (eq_refl (term679 A P m)). Qed.
Lemma lem3862215 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3862216 {A : Type'} (m : nat) (P : type686 A) (s : A -> Prop) : (term681 A P m s) = (term682 A m P s).
Proof. exact (MK_COMB (@lem3862214 A m P) (@lem3862215 A s)). Qed.
Lemma lem3862217 {A : Type'} (m : nat) (P : type686 A) (s : A -> Prop) : (term682 A m P s) = (term683 A m P s).
Proof. exact (eq_refl (term682 A m P s)). Qed.
Lemma lem3862218 {A : Type'} (m : nat) (P : type686 A) (s : A -> Prop) : (term681 A P m s) = (term683 A m P s).
Proof. exact (TRANS (@lem3862216 A m P s) (@lem3862217 A m P s)). Qed.
Lemma lem3862219 {A : Type'} (m : nat) (P : type686 A) : (term684 A P m) = (term680 A m P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3862218 A m P s)). Qed.
Lemma lem3862220 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3862221 {A : Type'} (m : nat) (P : type686 A) : (term685 A P m) = (term641 A m P).
Proof. exact (MK_COMB (@lem3862220 A) (@lem3862219 A m P)). Qed.
Lemma lem3862222 {A : Type'} (s : A -> Prop) (m : nat) (P : type686 A) : (term727 A s P m) = (term728 A s m P).
Proof. exact (MK_COMB (@lem3862213 A m s) (@lem3862221 A m P)). Qed.
Lemma lem3862223 {A : Type'} (s : A -> Prop) (P : type686 A) : (term729 A s P) = (term730 A s P).
Proof. exact (fun_ext (fun m : nat => @lem3862222 A s m P)). Qed.
Lemma lem3862224 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3862225 {A : Type'} (s : A -> Prop) (P : type686 A) : (term720 A s P) = (term710 A s P).
Proof. exact (MK_COMB (@lem3862224) (@lem3862223 A s P)). Qed.
Lemma lem3862226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3862227 {A : Type'} (s : A -> Prop) (P : type686 A) : (term731 A s P) = (term732 A s P).
Proof. exact (MK_COMB (@lem3862226) (@lem3862225 A s P)). Qed.
Lemma lem3862228 {A : Type'} (m : nat) (s : A -> Prop) : (term723 A s m) = (term724 A m s).
Proof. exact (eq_refl (term723 A s m)). Qed.
Lemma lem3862229 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862230 {A : Type'} (m : nat) (s : A -> Prop) : (term725 A s m) = (term726 A m s).
Proof. exact (MK_COMB (@lem3862229) (@lem3862228 A m s)). Qed.
Lemma lem3862231 {A : Type'} (m : nat) (P : type686 A) : (term679 A P m) = (term680 A m P).
Proof. exact (eq_refl (term679 A P m)). Qed.
Lemma lem3862232 {A : Type'} (s' : A -> Prop) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3862233 {A : Type'} (m : nat) (P : type686 A) (s' : A -> Prop) : (term681 A P m s') = (term682 A m P s').
Proof. exact (MK_COMB (@lem3862231 A m P) (@lem3862232 A s')). Qed.
Lemma lem3862234 {A : Type'} (m : nat) (P : type686 A) (s' : A -> Prop) : (term682 A m P s') = (term683 A m P s').
Proof. exact (eq_refl (term682 A m P s')). Qed.
Lemma lem3862235 {A : Type'} (m : nat) (P : type686 A) (s' : A -> Prop) : (term681 A P m s') = (term683 A m P s').
Proof. exact (TRANS (@lem3862233 A m P s') (@lem3862234 A m P s')). Qed.
Lemma lem3862236 {A : Type'} (s : A -> Prop) (m : nat) (P : type686 A) (s' : A -> Prop) : (term733 A s P m s') = (term734 A s m P s').
Proof. exact (MK_COMB (@lem3862230 A m s) (@lem3862235 A m P s')). Qed.
Lemma lem3862237 {A : Type'} (s : A -> Prop) (P : type686 A) (s' : A -> Prop) : (term735 A s P s') = (term736 A s P s').
Proof. exact (fun_ext (fun m : nat => @lem3862236 A s m P s')). Qed.
Lemma lem3862238 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3862239 {A : Type'} (s : A -> Prop) (P : type686 A) (s' : A -> Prop) : (term737 A s P s') = (term738 A s P s').
Proof. exact (MK_COMB (@lem3862238) (@lem3862237 A s P s')). Qed.
Lemma lem3862240 {A : Type'} (s : A -> Prop) (P : type686 A) : (term739 A s P) = (term740 A s P).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3862239 A s P s')). Qed.
Lemma lem3862241 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3862242 {A : Type'} (s : A -> Prop) (P : type686 A) : (term721 A s P) = (term741 A s P).
Proof. exact (MK_COMB (@lem3862241 A) (@lem3862240 A s P)). Qed.
Lemma lem3862243 {A : Type'} (s : A -> Prop) (P : type686 A) : ((term720 A s P) = (term721 A s P)) = ((term710 A s P) = (term741 A s P)).
Proof. exact (MK_COMB (@lem3862227 A s P) (@lem3862242 A s P)). Qed.
Lemma lem3862244 {A : Type'} (s : A -> Prop) (P : type686 A) : (term710 A s P) = (term741 A s P).
Proof. exact (EQ_MP (@lem3862243 A s P) (@lem3862210 A s P)). Qed.
Lemma lem3862246 {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop) : (term699 _17389 P e Q) = (term700 _17389 P e Q).
Proof. exact (EQ_MP (@lem511998 _17389 P e Q) (@lem512702 _17389 P e Q)). Qed.
Lemma lem3862247 (P : nat -> Prop) (e : nat) (Q : Prop) : (term701 P e Q) = (term702 P e Q).
Proof. exact (@lem3862246 nat P e Q). Qed.
Lemma lem3862248 {A : Type'} (s : A -> Prop) (P : type686 A) (s' : A -> Prop) : (term742 A s P s') = (term743 A s P s').
Proof. exact (@lem3862247 (term722 A s) (@CARD A s') (term667 A P s')). Qed.
Lemma lem3862249 {A : Type'} (m : nat) (s : A -> Prop) : (term723 A s m) = (term724 A m s).
Proof. exact (eq_refl (term723 A s m)). Qed.
Lemma lem3862250 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862251 {A : Type'} (m : nat) (s : A -> Prop) : (term725 A s m) = (term726 A m s).
Proof. exact (MK_COMB (@lem3862250) (@lem3862249 A m s)). Qed.
Lemma lem3862252 {A : Type'} (m : nat) (P : type686 A) (s' : A -> Prop) : (term683 A m P s') = (term683 A m P s').
Proof. exact (eq_refl (term683 A m P s')). Qed.
Lemma lem3862253 {A : Type'} (s : A -> Prop) (m : nat) (P : type686 A) (s' : A -> Prop) : (term744 A s m P s') = (term734 A s m P s').
Proof. exact (MK_COMB (@lem3862251 A m s) (@lem3862252 A m P s')). Qed.
Lemma lem3862254 {A : Type'} (s : A -> Prop) (P : type686 A) (s' : A -> Prop) : (term745 A s P s') = (term736 A s P s').
Proof. exact (fun_ext (fun m : nat => @lem3862253 A s m P s')). Qed.
Lemma lem3862255 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3862256 {A : Type'} (s : A -> Prop) (P : type686 A) (s' : A -> Prop) : (term742 A s P s') = (term738 A s P s').
Proof. exact (MK_COMB (@lem3862255) (@lem3862254 A s P s')). Qed.
Lemma lem3862257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3862258 {A : Type'} (s : A -> Prop) (P : type686 A) (s' : A -> Prop) : (term746 A s P s') = (term747 A s P s').
Proof. exact (MK_COMB (@lem3862257) (@lem3862256 A s P s')). Qed.
Lemma lem3862259 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term748 A s s') = (term749 A s' s).
Proof. exact (eq_refl (term748 A s s')). Qed.
Lemma lem3862260 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862261 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term750 A s s') = (term751 A s' s).
Proof. exact (MK_COMB (@lem3862260) (@lem3862259 A s' s)). Qed.
Lemma lem3862262 {A : Type'} (P : type686 A) (s' : A -> Prop) : (term667 A P s') = (term667 A P s').
Proof. exact (eq_refl (term667 A P s')). Qed.
Lemma lem3862263 {A : Type'} (s : A -> Prop) (P : type686 A) (s' : A -> Prop) : (term743 A s P s') = (term752 A s P s').
Proof. exact (MK_COMB (@lem3862261 A s' s) (@lem3862262 A P s')). Qed.
Lemma lem3862264 {A : Type'} (s : A -> Prop) (P : type686 A) (s' : A -> Prop) : ((term742 A s P s') = (term743 A s P s')) = ((term738 A s P s') = (term752 A s P s')).
Proof. exact (MK_COMB (@lem3862258 A s P s') (@lem3862263 A s P s')). Qed.
Lemma lem3862265 {A : Type'} (s : A -> Prop) (P : type686 A) (s' : A -> Prop) : (term738 A s P s') = (term752 A s P s').
Proof. exact (EQ_MP (@lem3862264 A s P s') (@lem3862248 A s P s')). Qed.
Lemma lem3862266 {A : Type'} (s : A -> Prop) (P : type686 A) : (term740 A s P) = (term753 A s P).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3862265 A s P s')). Qed.
Lemma lem3862267 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3862268 {A : Type'} (s : A -> Prop) (P : type686 A) : (term741 A s P) = (term754 A s P).
Proof. exact (MK_COMB (@lem3862267 A) (@lem3862266 A s P)). Qed.
Lemma lem3862269 {A : Type'} (s : A -> Prop) (P : type686 A) : (term710 A s P) = (term754 A s P).
Proof. exact (TRANS (@lem3862244 A s P) (@lem3862268 A s P)). Qed.
Lemma lem3862270 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862271 {A : Type'} (s : A -> Prop) (P : type686 A) : (term712 A s P) = (term755 A s P).
Proof. exact (MK_COMB (@lem3862270) (@lem3862269 A s P)). Qed.
Lemma lem3862272 {A : Type'} (P : type686 A) (s : A -> Prop) : (term667 A P s) = (term667 A P s).
Proof. exact (eq_refl (term667 A P s)). Qed.
Lemma lem3862273 {A : Type'} (P : type686 A) (s : A -> Prop) : (term713 A P s) = (term756 A P s).
Proof. exact (MK_COMB (@lem3862271 A s P) (@lem3862272 A P s)). Qed.
Lemma lem3862274 {A : Type'} (P : type686 A) (s : A -> Prop) : (term756 A P s) = (term713 A P s).
Proof. exact (SYM (@lem3862273 A P s)). Qed.
Lemma lem3862275 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term754 A s P) : term754 A s P.
Proof. exact (h1). Qed.
Lemma lem3862276 {A : Type'} (P : type686 A) : (P (@EMPTY A)) = ((P (@EMPTY A)) = True).
Proof. exact (@lem7 (P (@EMPTY A))). Qed.
Lemma lem3862291 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3862292 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3862293 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (@FINITE A s) = (@FINITE A (@EMPTY A)).
Proof. exact (MK_COMB (@lem3862292 A) (@lem3862291 A s h1)). Qed.
Lemma lem3862294 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862295 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term757 A s) = (term758 A).
Proof. exact (MK_COMB (@lem3862294) (@lem3862293 A s h1)). Qed.
Lemma lem3862297 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3862298 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3862299 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (P s) = (P (@EMPTY A)).
Proof. exact (MK_COMB (@lem3862298 A P) (@lem3862297 A s h1)). Qed.
Lemma lem3862301 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) : (P (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem3862276 A P) (@lem3862088 A P h1)). Qed.
Lemma lem3862302 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P (@EMPTY A)) (h2 : s = (@EMPTY A)) : (P s) = True.
Proof. exact (TRANS (@lem3862299 A P s h2) (@lem3862301 A P h1)). Qed.
Lemma lem3862303 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P (@EMPTY A)) (h2 : s = (@EMPTY A)) : (term667 A P s) = (term759 A).
Proof. exact (MK_COMB (@lem3862295 A s h2) (@lem3862302 A P s h1 h2)). Qed.
Lemma lem3862305 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3862306 {A : Type'} : (term759 A) = True.
Proof. exact (@lem3862305 (@FINITE A (@EMPTY A))). Qed.
Lemma lem3862307 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P (@EMPTY A)) (h2 : s = (@EMPTY A)) : (term667 A P s) = True.
Proof. exact (TRANS (@lem3862303 A P s h1 h2) (@lem3862306 A)). Qed.
Lemma lem3862308 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P (@EMPTY A)) (h2 : s = (@EMPTY A)) : True = (term667 A P s).
Proof. exact (SYM (@lem3862307 A P s h1 h2)). Qed.
Lemma lem3862309 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : P (@EMPTY A)) (h2 : s = (@EMPTY A)) : term667 A P s.
Proof. exact (EQ_MP (@lem3862308 A P s h1 h2) (@lem0)). Qed.
Lemma lem3862339 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3862340 {A : Type'} (P : type686 A) (h1 : term635 A P) : term635 A P.
Proof. exact (h1). Qed.
Lemma lem3862341 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term635 A P) : term760 A P s.
Proof. exact (@lem3862340 A P h1 s). Qed.
Lemma lem3862342 {A : Type'} (P : type686 A) (s : A -> Prop) : (term760 A P s) = (term761 A P s).
Proof. exact (eq_refl (term760 A P s)). Qed.
Lemma lem3862343 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term635 A P) : term761 A P s.
Proof. exact (EQ_MP (@lem3862342 A P s) (@lem3862341 A s P h1)). Qed.
Lemma lem3862351 {A : Type'} (s : A -> Prop) : term762 A s.
Proof. exact (@lem82 (s = (@EMPTY A))). Qed.
Lemma lem3862364 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3862373 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3862364 A s) (@lem3862339 A s h1)). Qed.
Lemma lem3862374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3862375 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term763 A s) = (and True).
Proof. exact (MK_COMB (@lem3862374) (@lem3862373 A s h1)). Qed.
Lemma lem3862377 {A : Type'} (s : A -> Prop) (h1 : term633 A s) : (s = (@EMPTY A)) = False.
Proof. exact (@lem3862351 A s (@lem3862085 A s h1)). Qed.
Lemma lem3862378 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3862379 {A : Type'} (s : A -> Prop) (h1 : term633 A s) : (term633 A s) = (~ False).
Proof. exact (MK_COMB (@lem3862378) (@lem3862377 A s h1)). Qed.
Lemma lem3862381 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3862382 {A : Type'} (s : A -> Prop) (h1 : term633 A s) : (term633 A s) = True.
Proof. exact (TRANS (@lem3862379 A s h1) (@lem3862381)). Qed.
Lemma lem3862383 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) : (term764 A s) = (True /\ True).
Proof. exact (MK_COMB (@lem3862375 A s h1) (@lem3862382 A s h2)). Qed.
Lemma lem3862385 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3862386 : (True /\ True) = True.
Proof. exact (@lem3862385 True). Qed.
Lemma lem3862387 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) : (term764 A s) = True.
Proof. exact (TRANS (@lem3862383 A s h1 h2) (@lem3862386)). Qed.
Lemma lem3862388 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862389 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) : (term765 A s) = (imp True).
Proof. exact (MK_COMB (@lem3862388) (@lem3862387 A s h1 h2)). Qed.
Lemma lem3862398 {A : Type'} (P : type686 A) (s : A -> Prop) : (term766 A P s) = (term766 A P s).
Proof. exact (eq_refl (term766 A P s)). Qed.
Lemma lem3862399 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) : (term761 A P s) = (term767 A P s).
Proof. exact (MK_COMB (@lem3862389 A s h1 h2) (@lem3862398 A P s)). Qed.
Lemma lem3862401 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3862402 {A : Type'} (P : type686 A) (s : A -> Prop) : (term767 A P s) = (term766 A P s).
Proof. exact (@lem3862401 (term766 A P s)). Qed.
Lemma lem3862411 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) : (term761 A P s) = (term766 A P s).
Proof. exact (TRANS (@lem3862399 A P s h1 h2) (@lem3862402 A P s)). Qed.
Lemma lem3862412 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3862413 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) : (term768 A P s) = (term769 A P s).
Proof. exact (MK_COMB (@lem3862412) (@lem3862411 A P s h1 h2)). Qed.
Lemma lem3862414 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3862415 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) : (term770 A P s) = (term771 A P s).
Proof. exact (MK_COMB (@lem3862413 A P s h1 h2) (@lem3862414 A P s)). Qed.
Lemma lem3862418 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) : (term771 A P s) = (term770 A P s).
Proof. exact (SYM (@lem3862415 A P s h1 h2)). Qed.
Lemma lem3862419 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term766 A P s) : term766 A P s.
Proof. exact (h1). Qed.
Lemma lem3862420 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term772 A x P s) : term772 A x P s.
Proof. exact (h1). Qed.
Lemma lem3862421 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term773 A x P s) : term773 A x P s.
Proof. exact (h1). Qed.
Lemma lem3862422 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term773 A x P s) : term773 A x P s.
Proof. exact (h1). Qed.
Lemma lem3862423 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (h1 : term774 A P s x) : term774 A P s x.
Proof. exact (h1). Qed.
Lemma lem3862424 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term774 A P s x) (h2 : term773 A x P s) : P s.
Proof. exact (@lem3862422 A x P s h2 (@lem3862423 A P s x h1)). Qed.
Lemma lem3862425 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (h1 : term774 A P s x) : term775 A x P s.
Proof. exact (fun h0 : term773 A x P s => @lem3862424 A x P s h1 h0). Qed.
Lemma lem3862426 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term773 A x P s) : term773 A x P s.
Proof. exact (h1). Qed.
Lemma lem3862427 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term774 A P s x) (h2 : term773 A x P s) : P s.
Proof. exact (@lem3862425 A P s x h1 (@lem3862426 A x P s h2)). Qed.
Lemma lem3862428 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term773 A x P s) : term773 A x P s.
Proof. exact (fun h0 : term774 A P s x => @lem3862427 A x P s h0 h1). Qed.
Lemma lem3862429 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) : term776 A x P s.
Proof. exact (fun h0 : term773 A x P s => @lem3862428 A x P s h0). Qed.
Lemma lem3862431 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3862433 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term773 A x P s) : term773 A x P s.
Proof. exact (@lem3862429 A x P s (@lem3862421 A x P s h1)). Qed.
Lemma lem3862434 {A : Type'} (x : A) (s : A -> Prop) (P : type686 A) (h1 : term754 A s P) : term777 A P s x.
Proof. exact (@lem3862275 A s P h1 (@DELETE A s x)). Qed.
Lemma lem3862435 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) : (term777 A P s x) = (term778 A P s x).
Proof. exact (eq_refl (term777 A P s x)). Qed.
Lemma lem3862436 {A : Type'} (x : A) (s : A -> Prop) (P : type686 A) (h1 : term754 A s P) : term778 A P s x.
Proof. exact (EQ_MP (@lem3862435 A P s x) (@lem3862434 A x s P h1)). Qed.
Lemma lem3862437 {_99911 : Type'} (s : _99911 -> Prop) : term779 _99911 s.
Proof. exact (@lem3854502 _99911 s). Qed.
Lemma lem3862438 {_99911 : Type'} (s : _99911 -> Prop) : (term779 _99911 s) = (term780 _99911 s).
Proof. exact (eq_refl (term779 _99911 s)). Qed.
Lemma lem3862439 {_99911 : Type'} (s : _99911 -> Prop) : term780 _99911 s.
Proof. exact (EQ_MP (@lem3862438 _99911 s) (@lem3862437 _99911 s)). Qed.
Lemma lem3862440 {_99911 : Type'} (s : _99911 -> Prop) (h1 : @FINITE _99911 s) : @FINITE _99911 s.
Proof. exact (h1). Qed.
Lemma lem3862441 {_99911 : Type'} (s : _99911 -> Prop) (h1 : @FINITE _99911 s) : ((@CARD _99911 s) = (NUMERAL 0)) = (s = (@EMPTY _99911)).
Proof. exact (@lem3862439 _99911 s (@lem3862440 _99911 s h1)). Qed.
Lemma lem3862447 {A : Type'} (x : A) : term781 A x.
Proof. exact (@lem3845383 A x). Qed.
Lemma lem3862448 {A : Type'} (x : A) : (term781 A x) = (term782 A x).
Proof. exact (eq_refl (term781 A x)). Qed.
Lemma lem3862449 {A : Type'} (x : A) : term782 A x.
Proof. exact (EQ_MP (@lem3862448 A x) (@lem3862447 A x)). Qed.
Lemma lem3862450 {A : Type'} (x : A) (s : A -> Prop) : term783 A x s.
Proof. exact (@lem3862449 A x s). Qed.
Lemma lem3862451 {A : Type'} (x : A) (s : A -> Prop) : (term783 A x s) = (term784 A x s).
Proof. exact (eq_refl (term783 A x s)). Qed.
Lemma lem3862452 {A : Type'} (x : A) (s : A -> Prop) : term784 A x s.
Proof. exact (EQ_MP (@lem3862451 A x s) (@lem3862450 A x s)). Qed.
Lemma lem3862453 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3862454 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term785 A s x) = (term786 A x s).
Proof. exact (@lem3862452 A x s (@lem3862453 A s h1)). Qed.
Lemma lem3862460 {A : Type'} (s : A -> Prop) : term787 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem3862461 {A : Type'} (s : A -> Prop) : (term787 A s) = (term788 A s).
Proof. exact (eq_refl (term787 A s)). Qed.
Lemma lem3862462 {A : Type'} (s : A -> Prop) : term788 A s.
Proof. exact (EQ_MP (@lem3862461 A s) (@lem3862460 A s)). Qed.
Lemma lem3862463 {A : Type'} (s : A -> Prop) (x : A) : term789 A s x.
Proof. exact (@lem3862462 A s x). Qed.
Lemma lem3862464 {A : Type'} (x : A) (s : A -> Prop) : (term789 A s x) = ((term790 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term789 A s x)). Qed.
Lemma lem3862468 {A : Type'} (s : A -> Prop) : term762 A s.
Proof. exact (@lem82 (s = (@EMPTY A))). Qed.
Lemma lem3862481 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3862483 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem3862488 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term791 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3862489 (p : Prop) (q : Prop) (p' : Prop) : term792 p q p'.
Proof. exact (fun q' : Prop => @lem3862488 p q p' q'). Qed.
Lemma lem3862490 (p : Prop) (q : Prop) : term793 p q.
Proof. exact (fun p' : Prop => @lem3862489 p q p'). Qed.
Lemma lem3862491 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) : term794 A P s x.
Proof. exact (@lem3862490 (term778 A P s x) (term774 A P s x)). Qed.
Lemma lem3862492 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) : term795 A P s x p'.
Proof. exact (@lem3862491 A P s x p'). Qed.
Lemma lem3862493 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) : (term795 A P s x p') = (term796 A P s x p').
Proof. exact (eq_refl (term795 A P s x p')). Qed.
Lemma lem3862494 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) : term796 A P s x p'.
Proof. exact (EQ_MP (@lem3862493 A P s x p') (@lem3862492 A P s x p')). Qed.
Lemma lem3862495 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : term797 A P s x p' q'.
Proof. exact (@lem3862494 A P s x p' q'). Qed.
Lemma lem3862496 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : (term797 A P s x p' q') = (term798 A P s x p' q').
Proof. exact (eq_refl (term797 A P s x p' q')). Qed.
Lemma lem3862497 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : term798 A P s x p' q'.
Proof. exact (EQ_MP (@lem3862496 A P s x p' q') (@lem3862495 A P s x p' q')). Qed.
Lemma lem3862501 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term791 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3862502 (p : Prop) (q : Prop) (p' : Prop) : term792 p q p'.
Proof. exact (fun q' : Prop => @lem3862501 p q p' q'). Qed.
Lemma lem3862503 (p : Prop) (q : Prop) : term793 p q.
Proof. exact (fun p' : Prop => @lem3862502 p q p'). Qed.
Lemma lem3862504 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) : term799 A P s x.
Proof. exact (@lem3862503 (term800 A x s) (term801 A P s x)). Qed.
Lemma lem3862505 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) : term802 A P s x p'.
Proof. exact (@lem3862504 A P s x p'). Qed.
Lemma lem3862506 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) : (term802 A P s x p') = (term803 A P s x p').
Proof. exact (eq_refl (term802 A P s x p')). Qed.
Lemma lem3862507 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) : term803 A P s x p'.
Proof. exact (EQ_MP (@lem3862506 A P s x p') (@lem3862505 A P s x p')). Qed.
Lemma lem3862508 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : term804 A P s x p' q'.
Proof. exact (@lem3862507 A P s x p' q'). Qed.
Lemma lem3862509 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : (term804 A P s x p' q') = (term805 A P s x p' q').
Proof. exact (eq_refl (term804 A P s x p' q')). Qed.
Lemma lem3862510 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : term805 A P s x p' q'.
Proof. exact (EQ_MP (@lem3862509 A P s x p' q') (@lem3862508 A P s x p' q')). Qed.
Lemma lem3862512 {A : Type'} (x : A) (s : A -> Prop) : term784 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3862454 A x s h0). Qed.
Lemma lem3862513 {A : Type'} (x : A) (s : A -> Prop) : term784 A x s.
Proof. exact (@lem3862512 A x s). Qed.
Lemma lem3862515 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3862481 A s) (@lem3862339 A s h1)). Qed.
Lemma lem3862516 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem3862515 A s h1)). Qed.
Lemma lem3862517 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3862516 A s h1) (@lem0)). Qed.
Lemma lem3862518 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term785 A s x) = (term786 A x s).
Proof. exact (@lem3862513 A x s (@lem3862517 A s h1)). Qed.
Lemma lem3862520 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term806 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem3862521 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term807 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem3862520 _2963 g t e g' t' e'). Qed.
Lemma lem3862522 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term808 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem3862521 _2963 g t e g' t'). Qed.
Lemma lem3862523 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term809 _2963 g t e.
Proof. exact (fun g' : Prop => @lem3862522 _2963 g t e g'). Qed.
Lemma lem3862524 (g : Prop) (t : nat) (e : nat) : term810 g t e.
Proof. exact (@lem3862523 nat g t e). Qed.
Lemma lem3862525 {A : Type'} (x : A) (s : A -> Prop) : term811 A x s.
Proof. exact (@lem3862524 (@IN A x s) (term812 A s) (@CARD A s)). Qed.
Lemma lem3862526 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : term813 A x s g'.
Proof. exact (@lem3862525 A x s g'). Qed.
Lemma lem3862527 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : (term813 A x s g') = (term814 A x s g').
Proof. exact (eq_refl (term813 A x s g')). Qed.
Lemma lem3862528 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : term814 A x s g'.
Proof. exact (EQ_MP (@lem3862527 A x s g') (@lem3862526 A x s g')). Qed.
Lemma lem3862529 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term815 A x s g' t'.
Proof. exact (@lem3862528 A x s g' t'). Qed.
Lemma lem3862530 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : (term815 A x s g' t') = (term816 A x s g' t').
Proof. exact (eq_refl (term815 A x s g' t')). Qed.
Lemma lem3862531 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term816 A x s g' t'.
Proof. exact (EQ_MP (@lem3862530 A x s g' t') (@lem3862529 A x s g' t')). Qed.
Lemma lem3862532 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term817 A x s g' t' e'.
Proof. exact (@lem3862531 A x s g' t' e'). Qed.
Lemma lem3862533 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term817 A x s g' t' e') = (term818 A x s g' t' e').
Proof. exact (eq_refl (term817 A x s g' t' e')). Qed.
Lemma lem3862534 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term818 A x s g' t' e'.
Proof. exact (EQ_MP (@lem3862533 A x s g' t' e') (@lem3862532 A x s g' t' e')). Qed.
Lemma lem3862536 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem3862483 A x s) (@lem3862431 A x s h1)). Qed.
Lemma lem3862537 {A : Type'} (x : A) (s : A -> Prop) (t' : nat) (e' : nat) : term819 A x s t' e'.
Proof. exact (@lem3862534 A x s True t' e'). Qed.
Lemma lem3862538 {A : Type'} (t' : nat) (e' : nat) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term820 A x s t' e'.
Proof. exact (@lem3862537 A x s t' e' (@lem3862536 A x s h1)). Qed.
Lemma lem3862544 {A : Type'} (s : A -> Prop) : (term812 A s) = (term812 A s).
Proof. exact (eq_refl (term812 A s)). Qed.
Lemma lem3862545 {A : Type'} (s : A -> Prop) : term821 A s.
Proof. exact (fun h0 : True => @lem3862544 A s). Qed.
Lemma lem3862546 {A : Type'} (e' : nat) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term822 A x s e'.
Proof. exact (@lem3862538 A (term812 A s) e' x s h1). Qed.
Lemma lem3862547 {A : Type'} (e' : nat) (x : A) (s : A -> Prop) (h1 : @IN A x s) : term823 A x s e'.
Proof. exact (@lem3862546 A e' x s h1 (@lem3862545 A s)). Qed.
Lemma lem3862551 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem3862552 {A : Type'} (s : A -> Prop) : term824 A s.
Proof. exact (fun h0 : ~ True => @lem3862551 A s). Qed.
Lemma lem3862553 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term825 A x s.
Proof. exact (@lem3862547 A (@CARD A s) x s h1). Qed.
Lemma lem3862554 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term786 A x s) = (term826 A s).
Proof. exact (@lem3862553 A x s h1 (@lem3862552 A s)). Qed.
Lemma lem3862556 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem3862557 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem3862556 nat t2 t1). Qed.
Lemma lem3862558 {A : Type'} (s : A -> Prop) : (term826 A s) = (term812 A s).
Proof. exact (@lem3862557 (@CARD A s) (term812 A s)). Qed.
Lemma lem3862559 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (term786 A x s) = (term812 A s).
Proof. exact (TRANS (@lem3862554 A x s h1) (@lem3862558 A s)). Qed.
Lemma lem3862560 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : (term785 A s x) = (term812 A s).
Proof. exact (TRANS (@lem3862518 A x s h1) (@lem3862559 A x s h2)). Qed.
Lemma lem3862561 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem3862562 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : (term827 A s x) = (term828 A s).
Proof. exact (MK_COMB (@lem3862561) (@lem3862560 A x s h1 h2)). Qed.
Lemma lem3862563 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem3862564 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : @IN A x s) : (term800 A x s) = (term829 A s).
Proof. exact (MK_COMB (@lem3862562 A x s h1 h2) (@lem3862563 A s)). Qed.
Lemma lem3862566 (n : nat) : (term7 n) = (term8 n).
Proof. exact (EQ_MP (@lem3862079 n) (@lem3862078 n)). Qed.
Lemma lem3862567 {A : Type'} (s : A -> Prop) : (term829 A s) = (term830 A s).
Proof. exact (@lem3862566 (@CARD A s)). Qed.
Lemma lem3862569 {_99911 : Type'} (s : _99911 -> Prop) : term780 _99911 s.
Proof. exact (fun h0 : @FINITE _99911 s => @lem3862441 _99911 s h0). Qed.
Lemma lem3862570 {A : Type'} (s : A -> Prop) : term780 A s.
Proof. exact (@lem3862569 A s). Qed.
Lemma lem3862572 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3862481 A s) (@lem3862339 A s h1)). Qed.
Lemma lem3862573 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem3862572 A s h1)). Qed.
Lemma lem3862574 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3862573 A s h1) (@lem0)). Qed.
Lemma lem3862575 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : ((@CARD A s) = (NUMERAL 0)) = (s = (@EMPTY A)).
Proof. exact (@lem3862570 A s (@lem3862574 A s h1)). Qed.
Lemma lem3862577 {A : Type'} (s : A -> Prop) (h1 : term633 A s) : (s = (@EMPTY A)) = False.
Proof. exact (@lem3862468 A s (@lem3862085 A s h1)). Qed.
Lemma lem3862578 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) : ((@CARD A s) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem3862575 A s h1) (@lem3862577 A s h2)). Qed.
Lemma lem3862579 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3862580 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) : (term830 A s) = (~ False).
Proof. exact (MK_COMB (@lem3862579) (@lem3862578 A s h1 h2)). Qed.
Lemma lem3862582 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3862583 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) : (term830 A s) = True.
Proof. exact (TRANS (@lem3862580 A s h1 h2) (@lem3862582)). Qed.
Lemma lem3862584 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) : (term829 A s) = True.
Proof. exact (TRANS (@lem3862567 A s) (@lem3862583 A s h1 h2)). Qed.
Lemma lem3862585 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) (h3 : @IN A x s) : (term800 A x s) = True.
Proof. exact (TRANS (@lem3862564 A x s h1 h3) (@lem3862584 A s h1 h2)). Qed.
Lemma lem3862586 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (q' : Prop) : term831 A P s x q'.
Proof. exact (@lem3862510 A P s x True q'). Qed.
Lemma lem3862587 {A : Type'} (P : type686 A) (q' : Prop) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) (h3 : @IN A x s) : term832 A P s x q'.
Proof. exact (@lem3862586 A P s x q' (@lem3862585 A x s h1 h2 h3)). Qed.
Lemma lem3862596 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term791 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3862597 (p : Prop) (q : Prop) (p' : Prop) : term792 p q p'.
Proof. exact (fun q' : Prop => @lem3862596 p q p' q'). Qed.
Lemma lem3862598 (p : Prop) (q : Prop) : term793 p q.
Proof. exact (fun p' : Prop => @lem3862597 p q p'). Qed.
Lemma lem3862599 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) : term833 A P s x.
Proof. exact (@lem3862598 (term790 A s x) (term774 A P s x)). Qed.
Lemma lem3862600 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) : term834 A P s x p'.
Proof. exact (@lem3862599 A P s x p'). Qed.
Lemma lem3862601 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) : (term834 A P s x p') = (term835 A P s x p').
Proof. exact (eq_refl (term834 A P s x p')). Qed.
Lemma lem3862602 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) : term835 A P s x p'.
Proof. exact (EQ_MP (@lem3862601 A P s x p') (@lem3862600 A P s x p')). Qed.
Lemma lem3862603 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : term836 A P s x p' q'.
Proof. exact (@lem3862602 A P s x p' q'). Qed.
Lemma lem3862604 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : (term836 A P s x p' q') = (term837 A P s x p' q').
Proof. exact (eq_refl (term836 A P s x p' q')). Qed.
Lemma lem3862605 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : term837 A P s x p' q'.
Proof. exact (EQ_MP (@lem3862604 A P s x p' q') (@lem3862603 A P s x p' q')). Qed.
Lemma lem3862607 {A : Type'} (x : A) (s : A -> Prop) : (term790 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3862464 A x s) (@lem3862463 A s x)). Qed.
Lemma lem3862608 {A : Type'} (x : A) (s : A -> Prop) : (term790 A s x) = (@FINITE A s).
Proof. exact (@lem3862607 A x s). Qed.
Lemma lem3862610 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3862481 A s) (@lem3862339 A s h1)). Qed.
Lemma lem3862613 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term790 A s x) = True.
Proof. exact (TRANS (@lem3862608 A x s) (@lem3862610 A s h1)). Qed.
Lemma lem3862614 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (q' : Prop) : term838 A P s x q'.
Proof. exact (@lem3862605 A P s x True q'). Qed.
Lemma lem3862615 {A : Type'} (P : type686 A) (x : A) (q' : Prop) (s : A -> Prop) (h1 : @FINITE A s) : term839 A P s x q'.
Proof. exact (@lem3862614 A P s x q' (@lem3862613 A x s h1)). Qed.
Lemma lem3862621 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) : (term774 A P s x) = (term774 A P s x).
Proof. exact (eq_refl (term774 A P s x)). Qed.
Lemma lem3862622 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) : term840 A P s x.
Proof. exact (fun h0 : True => @lem3862621 A P s x). Qed.
Lemma lem3862623 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term841 A P s x.
Proof. exact (@lem3862615 A P x (term774 A P s x) s h1). Qed.
Lemma lem3862624 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term801 A P s x) = (term842 A P s x).
Proof. exact (@lem3862623 A P x s h1 (@lem3862622 A P s x)). Qed.
Lemma lem3862626 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3862627 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) : (term842 A P s x) = (term774 A P s x).
Proof. exact (@lem3862626 (term774 A P s x)). Qed.
Lemma lem3862628 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term801 A P s x) = (term774 A P s x).
Proof. exact (TRANS (@lem3862624 A P x s h1) (@lem3862627 A P s x)). Qed.
Lemma lem3862629 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term843 A P s x.
Proof. exact (fun h0 : True => @lem3862628 A P x s h1). Qed.
Lemma lem3862630 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) (h3 : @IN A x s) : term844 A P s x.
Proof. exact (@lem3862587 A P (term774 A P s x) x s h1 h2 h3). Qed.
Lemma lem3862631 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) (h3 : @IN A x s) : (term778 A P s x) = (term842 A P s x).
Proof. exact (@lem3862630 A P x s h1 h2 h3 (@lem3862629 A P x s h1)). Qed.
Lemma lem3862633 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3862634 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) : (term842 A P s x) = (term774 A P s x).
Proof. exact (@lem3862633 (term774 A P s x)). Qed.
Lemma lem3862635 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) (h3 : @IN A x s) : (term778 A P s x) = (term774 A P s x).
Proof. exact (TRANS (@lem3862631 A P x s h1 h2 h3) (@lem3862634 A P s x)). Qed.
Lemma lem3862636 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (q' : Prop) : term845 A P s x q'.
Proof. exact (@lem3862497 A P s x (term774 A P s x) q'). Qed.
Lemma lem3862637 {A : Type'} (P : type686 A) (q' : Prop) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) (h3 : @IN A x s) : term846 A P s x q'.
Proof. exact (@lem3862636 A P s x q' (@lem3862635 A P x s h1 h2 h3)). Qed.
Lemma lem3862638 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (h1 : term774 A P s x) : term774 A P s x.
Proof. exact (h1). Qed.
Lemma lem3862639 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) : (term774 A P s x) = ((term774 A P s x) = True).
Proof. exact (@lem7 (term774 A P s x)). Qed.
Lemma lem3862642 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) (h1 : term774 A P s x) : (term774 A P s x) = True.
Proof. exact (EQ_MP (@lem3862639 A P s x) (@lem3862638 A P s x h1)). Qed.
Lemma lem3862643 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) : term847 A P s x.
Proof. exact (fun h0 : term774 A P s x => @lem3862642 A P s x h0). Qed.
Lemma lem3862644 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) (h3 : @IN A x s) : term848 A P s x.
Proof. exact (@lem3862637 A P True x s h1 h2 h3). Qed.
Lemma lem3862645 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) (h3 : @IN A x s) : (term849 A P s x) = (term850 A P s x).
Proof. exact (@lem3862644 A P x s h1 h2 h3 (@lem3862643 A P s x)). Qed.
Lemma lem3862647 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3862648 {A : Type'} (P : type686 A) (s : A -> Prop) (x : A) : (term850 A P s x) = True.
Proof. exact (@lem3862647 (term774 A P s x)). Qed.
Lemma lem3862649 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) (h3 : @IN A x s) : (term849 A P s x) = True.
Proof. exact (TRANS (@lem3862645 A P x s h1 h2 h3) (@lem3862648 A P s x)). Qed.
Lemma lem3862650 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) (h3 : @IN A x s) : True = (term849 A P s x).
Proof. exact (SYM (@lem3862649 A P x s h1 h2 h3)). Qed.
Lemma lem3862651 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term633 A s) (h3 : @IN A x s) : term849 A P s x.
Proof. exact (EQ_MP (@lem3862650 A P x s h1 h2 h3) (@lem0)). Qed.
Lemma lem3862652 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : term754 A s P) (h2 : @FINITE A s) (h3 : term633 A s) (h4 : @IN A x s) : term774 A P s x.
Proof. exact (@lem3862651 A P x s h2 h3 h4 (@lem3862436 A x s P h1)). Qed.
Lemma lem3862653 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term772 A x P s) : term773 A x P s.
Proof. exact (proj2 (@lem3862420 A x P s h1)). Qed.
Lemma lem3862654 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term772 A x P s) : @IN A x s.
Proof. exact (proj1 (@lem3862420 A x P s h1)). Qed.
Lemma lem3862655 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : term754 A s P) (h2 : @FINITE A s) (h3 : term633 A s) (h4 : term773 A x P s) (h5 : @IN A x s) : P s.
Proof. exact (@lem3862433 A x P s h4 (@lem3862652 A P x s h1 h2 h3 h5)). Qed.
Lemma lem3862656 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : term754 A s P) (h2 : @FINITE A s) (h3 : term633 A s) (h4 : term773 A x P s) (h5 : @IN A x s) : (@IN A x s) = (P s).
Proof. exact (prop_ext (fun h6 : @IN A x s => @lem3862655 A P x s h1 h2 h3 h4 h5) (fun h6 : P s => @lem3862431 A x s h5)). Qed.
Lemma lem3862657 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : term754 A s P) (h2 : @FINITE A s) (h3 : term633 A s) (h4 : term773 A x P s) (h5 : @IN A x s) : P s.
Proof. exact (EQ_MP (@lem3862656 A P x s h1 h2 h3 h4 h5) (@lem3862431 A x s h5)). Qed.
Lemma lem3862658 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : term754 A s P) (h2 : @FINITE A s) (h3 : term633 A s) (h4 : term772 A x P s) (h5 : @IN A x s) : (term773 A x P s) = (P s).
Proof. exact (prop_ext (fun h6 : term773 A x P s => @lem3862657 A P x s h1 h2 h3 h6 h5) (fun h6 : P s => @lem3862653 A x P s h4)). Qed.
Lemma lem3862659 {A : Type'} (P : type686 A) (x : A) (s : A -> Prop) (h1 : term754 A s P) (h2 : @FINITE A s) (h3 : term633 A s) (h4 : term772 A x P s) (h5 : @IN A x s) : P s.
Proof. exact (EQ_MP (@lem3862658 A P x s h1 h2 h3 h4 h5) (@lem3862653 A x P s h4)). Qed.
Lemma lem3862660 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term754 A s P) (h2 : @FINITE A s) (h3 : term633 A s) (h4 : term772 A x P s) : (@IN A x s) = (P s).
Proof. exact (prop_ext (fun h5 : @IN A x s => @lem3862659 A P x s h1 h2 h3 h4 h5) (fun h5 : P s => @lem3862654 A x P s h4)). Qed.
Lemma lem3862661 {A : Type'} (x : A) (P : type686 A) (s : A -> Prop) (h1 : term754 A s P) (h2 : @FINITE A s) (h3 : term633 A s) (h4 : term772 A x P s) : P s.
Proof. exact (EQ_MP (@lem3862660 A x P s h1 h2 h3 h4) (@lem3862654 A x P s h4)). Qed.
Lemma lem3862662 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term754 A s P) (h2 : term766 A P s) (h3 : @FINITE A s) (h4 : term633 A s) : P s.
Proof. exact (ex_elim (@lem3862419 A P s h2) (fun x : A => fun h0 : term851 A P s x => @lem3862661 A x P s h1 h3 h4 h0)). Qed.
Lemma lem3862663 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term754 A s P) (h2 : @FINITE A s) (h3 : term633 A s) : term771 A P s.
Proof. exact (fun h0 : term766 A P s => @lem3862662 A P s h1 h0 h2 h3). Qed.
Lemma lem3862664 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term754 A s P) (h2 : @FINITE A s) (h3 : term633 A s) : term770 A P s.
Proof. exact (EQ_MP (@lem3862418 A P s h2 h3) (@lem3862663 A P s h1 h2 h3)). Qed.
Lemma lem3862665 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term635 A P) (h2 : term754 A s P) (h3 : @FINITE A s) (h4 : term633 A s) : P s.
Proof. exact (@lem3862664 A P s h2 h3 h4 (@lem3862343 A s P h1)). Qed.
Lemma lem3862666 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term754 A s P) (h2 : @FINITE A s) (h3 : term633 A s) : term852 A P s.
Proof. exact (fun h0 : term635 A P => @lem3862665 A P s h0 h1 h2 h3). Qed.
Lemma lem3862667 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term635 A P) (h2 : term754 A s P) (h3 : @FINITE A s) (h4 : term633 A s) : P s.
Proof. exact (@lem3862666 A P s h2 h3 h4 (@lem3862087 A P h1)). Qed.
Lemma lem3862669 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term635 A P) (h2 : term754 A s P) (h3 : term633 A s) : term667 A P s.
Proof. exact (fun h0 : @FINITE A s => @lem3862667 A P s h1 h2 h0 h3). Qed.
Lemma lem3862670 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term635 A P) (h2 : term754 A s P) (h3 : P (@EMPTY A)) : term667 A P s.
Proof. exact (or_elim (@lem3862083 A s) (fun h0 : s = (@EMPTY A) => @lem3862309 A P s h3 h0) (fun h0 : term633 A s => @lem3862669 A P s h1 h2 h0)). Qed.
Lemma lem3862671 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term635 A P) (h2 : term754 A s P) (h3 : P (@EMPTY A)) : (term754 A s P) = (term667 A P s).
Proof. exact (prop_ext (fun h4 : term754 A s P => @lem3862670 A s P h1 h2 h3) (fun h4 : term667 A P s => @lem3862275 A s P h2)). Qed.
Lemma lem3862672 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term635 A P) (h2 : term754 A s P) (h3 : P (@EMPTY A)) : term667 A P s.
Proof. exact (EQ_MP (@lem3862671 A s P h1 h2 h3) (@lem3862275 A s P h2)). Qed.
Lemma lem3862673 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term635 A P) (h2 : P (@EMPTY A)) : term756 A P s.
Proof. exact (fun h0 : term754 A s P => @lem3862672 A s P h1 h0 h2). Qed.
Lemma lem3862674 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term635 A P) (h2 : P (@EMPTY A)) : term713 A P s.
Proof. exact (EQ_MP (@lem3862274 A P s) (@lem3862673 A s P h1 h2)). Qed.
Lemma lem3862679 {A : Type'} (P : type686 A) (h1 : term635 A P) (h2 : P (@EMPTY A)) : term715 A P.
Proof. exact (fun s : A -> Prop => @lem3862674 A s P h1 h2). Qed.
Lemma lem3862680 {A : Type'} (s : A -> Prop) (P : type686 A) (h1 : term635 A P) (h2 : P (@EMPTY A)) : term667 A P s.
Proof. exact (@lem3862206 A P s (@lem3862679 A P h1 h2)). Qed.
Lemma lem3862685 {A : Type'} (P : type686 A) (h1 : term635 A P) (h2 : P (@EMPTY A)) : term853 A P.
Proof. exact (fun s : A -> Prop => @lem3862680 A s P h1 h2). Qed.
Lemma lem3862686 {A : Type'} (P : type686 A) (h1 : term634 A P) : term635 A P.
Proof. exact (proj2 (@lem3862086 A P h1)). Qed.
Lemma lem3862687 {A : Type'} (P : type686 A) (h1 : term634 A P) : P (@EMPTY A).
Proof. exact (proj1 (@lem3862086 A P h1)). Qed.
Lemma lem3862688 {A : Type'} (P : type686 A) (h1 : term635 A P) (h2 : P (@EMPTY A)) : (term635 A P) = (term853 A P).
Proof. exact (prop_ext (fun h3 : term635 A P => @lem3862685 A P h1 h2) (fun h3 : term853 A P => @lem3862087 A P h1)). Qed.
Lemma lem3862689 {A : Type'} (P : type686 A) (h1 : term635 A P) (h2 : P (@EMPTY A)) : term853 A P.
Proof. exact (EQ_MP (@lem3862688 A P h1 h2) (@lem3862087 A P h1)). Qed.
Lemma lem3862690 {A : Type'} (P : type686 A) (h1 : term635 A P) (h2 : P (@EMPTY A)) : (P (@EMPTY A)) = (term853 A P).
Proof. exact (prop_ext (fun h3 : P (@EMPTY A) => @lem3862689 A P h1 h2) (fun h3 : term853 A P => @lem3862088 A P h2)). Qed.
Lemma lem3862691 {A : Type'} (P : type686 A) (h1 : term635 A P) (h2 : P (@EMPTY A)) : term853 A P.
Proof. exact (EQ_MP (@lem3862690 A P h1 h2) (@lem3862088 A P h2)). Qed.
Lemma lem3862692 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) (h2 : term634 A P) : (term635 A P) = (term853 A P).
Proof. exact (prop_ext (fun h3 : term635 A P => @lem3862691 A P h3 h1) (fun h3 : term853 A P => @lem3862686 A P h2)). Qed.
Lemma lem3862693 {A : Type'} (P : type686 A) (h1 : P (@EMPTY A)) (h2 : term634 A P) : term853 A P.
Proof. exact (EQ_MP (@lem3862692 A P h1 h2) (@lem3862686 A P h2)). Qed.
Lemma lem3862694 {A : Type'} (P : type686 A) (h1 : term634 A P) : (P (@EMPTY A)) = (term853 A P).
Proof. exact (prop_ext (fun h2 : P (@EMPTY A) => @lem3862693 A P h2 h1) (fun h2 : term853 A P => @lem3862687 A P h1)). Qed.
Lemma lem3862695 {A : Type'} (P : type686 A) (h1 : term634 A P) : term853 A P.
Proof. exact (EQ_MP (@lem3862694 A P h1) (@lem3862687 A P h1)). Qed.
Lemma lem3862696 {A : Type'} (P : type686 A) : term854 A P.
Proof. exact (fun h0 : term634 A P => @lem3862695 A P h0). Qed.
Lemma lem3862701 {A : Type'} : term855 A.
Proof. exact (fun P : type686 A => @lem3862696 A P). Qed.
