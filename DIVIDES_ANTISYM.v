Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVIDES_ANTISYM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DIVIDES_LE_STRONG_spec.
Require Import INT_POS_spec.
Require Import MULT_CLAUSES_spec.
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
Require Import thm18394_spec.
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
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
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
Require Import thm3073436_spec.
Require Import thm3074596_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem3102345 (m : nat) : term0 m.
Proof. exact (@lem3086875 m). Qed.
Lemma lem3102346 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem3102347 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem3102346 m) (@lem3102345 m)). Qed.
Lemma lem3102348 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem3102347 m n). Qed.
Lemma lem3102349 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem3102370 (b : nat) (a : nat) : (num_divides a b) = (term4 b a).
Proof. exact (EQ_MP (@lem3073436 b a) (@lem3074596 b a)). Qed.
Lemma lem3102371 (n : nat) (m : nat) : (num_divides m n) = (term4 n m).
Proof. exact (@lem3102370 n m). Qed.
Lemma lem3102378 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102379 (n : nat) (m : nat) : (term5 m n) = (term6 n m).
Proof. exact (MK_COMB (@lem3102378) (@lem3102371 n m)). Qed.
Lemma lem3102381 (b : nat) (a : nat) : (num_divides a b) = (term4 b a).
Proof. exact (EQ_MP (@lem3073436 b a) (@lem3074596 b a)). Qed.
Lemma lem3102382 (m : nat) (n : nat) : (num_divides n m) = (term4 m n).
Proof. exact (@lem3102381 m n). Qed.
Lemma lem3102389 (m : nat) (n : nat) : (term7 n m) = (term8 m n).
Proof. exact (MK_COMB (@lem3102379 n m) (@lem3102382 m n)). Qed.
Lemma lem3102392 (m : nat) (n : nat) : (term9 m n) = (term9 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem3102393 (m : nat) (n : nat) : (term10 n m) = (term11 m n).
Proof. exact (MK_COMB (@lem3102392 m n) (@lem3102389 m n)). Qed.
Lemma lem3102398 (n : nat) (m : nat) : (term11 m n) = (term10 n m).
Proof. exact (SYM (@lem3102393 m n)). Qed.
Lemma lem3102400 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3102401 (m : nat) (n : nat) : (term11 m n) = (term13 m n).
Proof. exact (@lem3102400 (term11 m n)). Qed.
Lemma lem3102402 (m : nat) (n : nat) : (term13 m n) = (term11 m n).
Proof. exact (SYM (@lem3102401 m n)). Qed.
Lemma lem3102403 (m : nat) (n : nat) (h1 : term14 m n) : term14 m n.
Proof. exact (h1). Qed.
Lemma lem3102406 (m : nat) (n : nat) (h1 : term15 m n) : term15 m n.
Proof. exact (h1). Qed.
Lemma lem3102407 (m : nat) (n : nat) : term16 m n.
Proof. exact (fun h0 : term15 m n => @lem3102406 m n h0). Qed.
Lemma lem3102408 (m : nat) (n : nat) (h1 : term16 m n) : term16 m n.
Proof. exact (h1). Qed.
Lemma lem3102409 (m : nat) (n : nat) (h1 : term15 m n) : term15 m n.
Proof. exact (h1). Qed.
Lemma lem3102410 (m : nat) (n : nat) (h1 : term15 m n) (h2 : term16 m n) : term15 m n.
Proof. exact (@lem3102408 m n h2 (@lem3102409 m n h1)). Qed.
Lemma lem3102411 (m : nat) (n : nat) (h1 : term15 m n) : term17 m n.
Proof. exact (fun h0 : term16 m n => @lem3102410 m n h1 h0). Qed.
Lemma lem3102412 (m : nat) (n : nat) (h1 : term16 m n) : term16 m n.
Proof. exact (h1). Qed.
Lemma lem3102413 (m : nat) (n : nat) (h1 : term15 m n) (h2 : term16 m n) : term15 m n.
Proof. exact (@lem3102411 m n h1 (@lem3102412 m n h2)). Qed.
Lemma lem3102414 (m : nat) (n : nat) (h1 : term16 m n) : term16 m n.
Proof. exact (fun h0 : term15 m n => @lem3102413 m n h0 h1). Qed.
Lemma lem3102415 (m : nat) (n : nat) : term18 m n.
Proof. exact (fun h0 : term16 m n => @lem3102414 m n h0). Qed.
Lemma lem3102418 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem3102415 m n (@lem3102407 m n)). Qed.
Lemma lem3102442 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3102443 : term19 = term20.
Proof. exact (@lem3102442 term21). Qed.
Lemma lem3102486 (m : nat) (n : nat) : (term22 m n) = (term22 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem3102487 (m : nat) (n : nat) : (term15 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem3102486 m n) (@lem3102443)). Qed.
Lemma lem3102490 (n : nat) : (term24 n) = (term25 n).
Proof. exact (fun_ext (fun m : nat => @lem3102487 m n)). Qed.
Lemma lem3102491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102492 (n : nat) : (term26 n) = (term27 n).
Proof. exact (MK_COMB (@lem3102491) (@lem3102490 n)). Qed.
Lemma lem3102497 : term28 = term29.
Proof. exact (fun_ext (fun n : nat => @lem3102492 n)). Qed.
Lemma lem3102498 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102507 : term30 = term31.
Proof. exact (MK_COMB (@lem3102498) (@lem3102497)). Qed.
Lemma lem3102508 (m : nat) (n : nat) : ((term32 m n) = (term33 m n)) = ((term32 m n) = (term33 m n)).
Proof. exact (eq_refl ((term32 m n) = (term33 m n))). Qed.
Lemma lem3102509 (m : nat) : (term34 m) = (term34 m).
Proof. exact (fun_ext (fun n : nat => @lem3102508 m n)). Qed.
Lemma lem3102510 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102511 (m : nat) : (term35 m) = (term35 m).
Proof. exact (MK_COMB (@lem3102510) (@lem3102509 m)). Qed.
Lemma lem3102512 : term36 = term36.
Proof. exact (fun_ext (fun m : nat => @lem3102511 m)). Qed.
Lemma lem3102513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102514 : term37 = term37.
Proof. exact (MK_COMB (@lem3102513) (@lem3102512)). Qed.
Lemma lem3102515 (m : nat) (n : nat) : ((term38 m n) = (term39 m n)) = ((term38 m n) = (term39 m n)).
Proof. exact (eq_refl ((term38 m n) = (term39 m n))). Qed.
Lemma lem3102516 (m : nat) : (term40 m) = (term40 m).
Proof. exact (fun_ext (fun n : nat => @lem3102515 m n)). Qed.
Lemma lem3102517 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102518 (m : nat) : (term41 m) = (term41 m).
Proof. exact (MK_COMB (@lem3102517) (@lem3102516 m)). Qed.
Lemma lem3102519 : term42 = term42.
Proof. exact (fun_ext (fun m : nat => @lem3102518 m)). Qed.
Lemma lem3102520 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102521 : term43 = term43.
Proof. exact (MK_COMB (@lem3102520) (@lem3102519)). Qed.
Lemma lem3102522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102523 : term44 = term44.
Proof. exact (MK_COMB (@lem3102522) (@lem3102521)). Qed.
Lemma lem3102524 : term45 = term45.
Proof. exact (MK_COMB (@lem3102523) (@lem3102514)). Qed.
Lemma lem3102525 (m : nat) : ((term46 m) = m) = ((term46 m) = m).
Proof. exact (eq_refl ((term46 m) = m)). Qed.
Lemma lem3102526 : term47 = term47.
Proof. exact (fun_ext (fun m : nat => @lem3102525 m)). Qed.
Lemma lem3102527 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102528 : term48 = term48.
Proof. exact (MK_COMB (@lem3102527) (@lem3102526)). Qed.
Lemma lem3102529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102530 : term49 = term49.
Proof. exact (MK_COMB (@lem3102529) (@lem3102528)). Qed.
Lemma lem3102531 : term50 = term50.
Proof. exact (MK_COMB (@lem3102530) (@lem3102524)). Qed.
Lemma lem3102532 (n : nat) : ((term51 n) = n) = ((term51 n) = n).
Proof. exact (eq_refl ((term51 n) = n)). Qed.
Lemma lem3102533 : term52 = term52.
Proof. exact (fun_ext (fun n : nat => @lem3102532 n)). Qed.
Lemma lem3102534 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102535 : term53 = term53.
Proof. exact (MK_COMB (@lem3102534) (@lem3102533)). Qed.
Lemma lem3102536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102537 : term54 = term54.
Proof. exact (MK_COMB (@lem3102536) (@lem3102535)). Qed.
Lemma lem3102538 : term55 = term55.
Proof. exact (MK_COMB (@lem3102537) (@lem3102531)). Qed.
Lemma lem3102539 (m : nat) : ((term56 m) = (NUMERAL 0)) = ((term56 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term56 m) = (NUMERAL 0))). Qed.
Lemma lem3102540 : term57 = term57.
Proof. exact (fun_ext (fun m : nat => @lem3102539 m)). Qed.
Lemma lem3102541 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102542 : term58 = term58.
Proof. exact (MK_COMB (@lem3102541) (@lem3102540)). Qed.
Lemma lem3102543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102544 : term59 = term59.
Proof. exact (MK_COMB (@lem3102543) (@lem3102542)). Qed.
Lemma lem3102545 : term60 = term60.
Proof. exact (MK_COMB (@lem3102544) (@lem3102538)). Qed.
Lemma lem3102546 (n : nat) : ((term61 n) = (NUMERAL 0)) = ((term61 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term61 n) = (NUMERAL 0))). Qed.
Lemma lem3102547 : term62 = term62.
Proof. exact (fun_ext (fun n : nat => @lem3102546 n)). Qed.
Lemma lem3102548 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102549 : term63 = term63.
Proof. exact (MK_COMB (@lem3102548) (@lem3102547)). Qed.
Lemma lem3102550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102551 : term64 = term64.
Proof. exact (MK_COMB (@lem3102550) (@lem3102549)). Qed.
Lemma lem3102552 : term21 = term21.
Proof. exact (MK_COMB (@lem3102551) (@lem3102545)). Qed.
Lemma lem3102553 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3102554 : term20 = term20.
Proof. exact (MK_COMB (@lem3102553) (@lem3102552)). Qed.
Lemma lem3102555 (m : nat) (n : nat) (x : nat) : (m = (Nat.mul n x)) = (m = (Nat.mul n x)).
Proof. exact (eq_refl (m = (Nat.mul n x))). Qed.
Lemma lem3102556 (m : nat) (n : nat) : (term65 m n) = (term65 m n).
Proof. exact (fun_ext (fun x : nat => @lem3102555 m n x)). Qed.
Lemma lem3102557 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3102558 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (MK_COMB (@lem3102557) (@lem3102556 m n)). Qed.
Lemma lem3102559 (n : nat) (m : nat) (x : nat) : (n = (Nat.mul m x)) = (n = (Nat.mul m x)).
Proof. exact (eq_refl (n = (Nat.mul m x))). Qed.
Lemma lem3102560 (n : nat) (m : nat) : (term65 n m) = (term65 n m).
Proof. exact (fun_ext (fun x : nat => @lem3102559 n m x)). Qed.
Lemma lem3102561 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3102562 (n : nat) (m : nat) : (term4 n m) = (term4 n m).
Proof. exact (MK_COMB (@lem3102561) (@lem3102560 n m)). Qed.
Lemma lem3102563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102564 (n : nat) (m : nat) : (term6 n m) = (term6 n m).
Proof. exact (MK_COMB (@lem3102563) (@lem3102562 n m)). Qed.
Lemma lem3102565 (m : nat) (n : nat) : (term8 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem3102564 n m) (@lem3102558 m n)). Qed.
Lemma lem3102568 (m : nat) (n : nat) : (term9 m n) = (term9 m n).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem3102569 (m : nat) (n : nat) : (term11 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem3102568 m n) (@lem3102565 m n)). Qed.
Lemma lem3102570 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3102571 (m : nat) (n : nat) : (term14 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem3102570) (@lem3102569 m n)). Qed.
Lemma lem3102572 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3102573 (m : nat) (n : nat) : (term22 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem3102572) (@lem3102571 m n)). Qed.
Lemma lem3102574 (m : nat) (n : nat) : (term23 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem3102573 m n) (@lem3102554)). Qed.
Lemma lem3102575 (n : nat) : (term25 n) = (term25 n).
Proof. exact (fun_ext (fun m : nat => @lem3102574 m n)). Qed.
Lemma lem3102576 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102577 (n : nat) : (term27 n) = (term27 n).
Proof. exact (MK_COMB (@lem3102576) (@lem3102575 n)). Qed.
Lemma lem3102578 : term29 = term29.
Proof. exact (fun_ext (fun n : nat => @lem3102577 n)). Qed.
Lemma lem3102579 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102580 : term31 = term31.
Proof. exact (MK_COMB (@lem3102579) (@lem3102578)). Qed.
Lemma lem3102671 : term30 = term31.
Proof. exact (TRANS (@lem3102507) (@lem3102580)). Qed.
Lemma lem3102672 : term31 = term30.
Proof. exact (SYM (@lem3102671)). Qed.
Lemma lem3102673 (m : nat) (n : nat) (h1 : term14 m n) : term14 m n.
Proof. exact (h1). Qed.
Lemma lem3102674 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem3102677 (P : nat -> Prop) : (term66 P) = (term67 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem3102678 (n : nat) (m : nat) : (term68 n m) = (term69 n m).
Proof. exact (@lem3102677 (term65 n m)). Qed.
Lemma lem3102679 (n : nat) (m : nat) (x : nat) : (term70 n m x) = (n = (Nat.mul m x)).
Proof. exact (eq_refl (term70 n m x)). Qed.
Lemma lem3102680 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3102682 (n : nat) (m : nat) (x : nat) : (term71 n m x) = (term72 n m x).
Proof. exact (MK_COMB (@lem3102680) (@lem3102679 n m x)). Qed.
Lemma lem3102683 (n : nat) (m : nat) : (term73 n m) = (term74 n m).
Proof. exact (fun_ext (fun x : nat => @lem3102682 n m x)). Qed.
Lemma lem3102684 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102685 (n : nat) (m : nat) : (term69 n m) = (term75 n m).
Proof. exact (MK_COMB (@lem3102684) (@lem3102683 n m)). Qed.
Lemma lem3102686 (n : nat) (m : nat) : (term68 n m) = (term75 n m).
Proof. exact (TRANS (@lem3102678 n m) (@lem3102685 n m)). Qed.
Lemma lem3102688 (P : nat -> Prop) : (term66 P) = (term67 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem3102689 (m : nat) (n : nat) : (term68 m n) = (term69 m n).
Proof. exact (@lem3102688 (term65 m n)). Qed.
Lemma lem3102690 (m : nat) (n : nat) (x : nat) : (term70 m n x) = (m = (Nat.mul n x)).
Proof. exact (eq_refl (term70 m n x)). Qed.
Lemma lem3102691 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3102693 (m : nat) (n : nat) (x : nat) : (term71 m n x) = (term72 m n x).
Proof. exact (MK_COMB (@lem3102691) (@lem3102690 m n x)). Qed.
Lemma lem3102694 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (fun_ext (fun x : nat => @lem3102693 m n x)). Qed.
Lemma lem3102695 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102696 (m : nat) (n : nat) : (term69 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem3102695) (@lem3102694 m n)). Qed.
Lemma lem3102697 (m : nat) (n : nat) : (term68 m n) = (term75 m n).
Proof. exact (TRANS (@lem3102689 m n) (@lem3102696 m n)). Qed.
Lemma lem3102698 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3102699 (n : nat) (m : nat) : (term76 n m) = (term77 n m).
Proof. exact (MK_COMB (@lem3102698) (@lem3102686 n m)). Qed.
Lemma lem3102700 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem3102699 n m) (@lem3102697 m n)). Qed.
Lemma lem3102701 (m : nat) (n : nat) : (term80 m n) = (term78 m n).
Proof. exact (@lem17045 (term4 n m) (term4 m n)). Qed.
Lemma lem3102702 (m : nat) (n : nat) : (term80 m n) = (term79 m n).
Proof. exact (TRANS (@lem3102701 m n) (@lem3102700 m n)). Qed.
Lemma lem3102704 (m : nat) (n : nat) : (term81 m n) = (term81 m n).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem3102705 (m : nat) (n : nat) : (term82 m n) = (term83 m n).
Proof. exact (MK_COMB (@lem3102704 m n) (@lem3102702 m n)). Qed.
Lemma lem3102706 (m : nat) (n : nat) : (term14 m n) = (term82 m n).
Proof. exact (@lem17362 (m = n) (term8 m n)). Qed.
Lemma lem3102719 (m : nat) (n : nat) : (term14 m n) = (term83 m n).
Proof. exact (TRANS (@lem3102706 m n) (@lem3102705 m n)). Qed.
Lemma lem3102720 (m : nat) (n : nat) (h1 : term14 m n) : term83 m n.
Proof. exact (EQ_MP (@lem3102719 m n) (@lem3102673 m n h1)). Qed.
Lemma lem3102721 (n : nat) : ((term61 n) = (NUMERAL 0)) = ((term61 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term61 n) = (NUMERAL 0))). Qed.
Lemma lem3102722 : term62 = term62.
Proof. exact (fun_ext (fun n : nat => @lem3102721 n)). Qed.
Lemma lem3102723 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102724 : term63 = term63.
Proof. exact (MK_COMB (@lem3102723) (@lem3102722)). Qed.
Lemma lem3102725 (m : nat) : ((term56 m) = (NUMERAL 0)) = ((term56 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term56 m) = (NUMERAL 0))). Qed.
Lemma lem3102726 : term57 = term57.
Proof. exact (fun_ext (fun m : nat => @lem3102725 m)). Qed.
Lemma lem3102727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102728 : term58 = term58.
Proof. exact (MK_COMB (@lem3102727) (@lem3102726)). Qed.
Lemma lem3102729 (n : nat) : ((term51 n) = n) = ((term51 n) = n).
Proof. exact (eq_refl ((term51 n) = n)). Qed.
Lemma lem3102730 : term52 = term52.
Proof. exact (fun_ext (fun n : nat => @lem3102729 n)). Qed.
Lemma lem3102731 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102732 : term53 = term53.
Proof. exact (MK_COMB (@lem3102731) (@lem3102730)). Qed.
Lemma lem3102733 (m : nat) : ((term46 m) = m) = ((term46 m) = m).
Proof. exact (eq_refl ((term46 m) = m)). Qed.
Lemma lem3102734 : term47 = term47.
Proof. exact (fun_ext (fun m : nat => @lem3102733 m)). Qed.
Lemma lem3102735 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102736 : term48 = term48.
Proof. exact (MK_COMB (@lem3102735) (@lem3102734)). Qed.
Lemma lem3102737 (m : nat) (n : nat) : ((term38 m n) = (term39 m n)) = ((term38 m n) = (term39 m n)).
Proof. exact (eq_refl ((term38 m n) = (term39 m n))). Qed.
Lemma lem3102738 (m : nat) : (term40 m) = (term40 m).
Proof. exact (fun_ext (fun n : nat => @lem3102737 m n)). Qed.
Lemma lem3102739 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102740 (m : nat) : (term41 m) = (term41 m).
Proof. exact (MK_COMB (@lem3102739) (@lem3102738 m)). Qed.
Lemma lem3102741 : term42 = term42.
Proof. exact (fun_ext (fun m : nat => @lem3102740 m)). Qed.
Lemma lem3102742 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102743 : term43 = term43.
Proof. exact (MK_COMB (@lem3102742) (@lem3102741)). Qed.
Lemma lem3102744 (m : nat) (n : nat) : ((term32 m n) = (term33 m n)) = ((term32 m n) = (term33 m n)).
Proof. exact (eq_refl ((term32 m n) = (term33 m n))). Qed.
Lemma lem3102745 (m : nat) : (term34 m) = (term34 m).
Proof. exact (fun_ext (fun n : nat => @lem3102744 m n)). Qed.
Lemma lem3102746 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102747 (m : nat) : (term35 m) = (term35 m).
Proof. exact (MK_COMB (@lem3102746) (@lem3102745 m)). Qed.
Lemma lem3102748 : term36 = term36.
Proof. exact (fun_ext (fun m : nat => @lem3102747 m)). Qed.
Lemma lem3102749 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102750 : term37 = term37.
Proof. exact (MK_COMB (@lem3102749) (@lem3102748)). Qed.
Lemma lem3102751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102752 : term44 = term44.
Proof. exact (MK_COMB (@lem3102751) (@lem3102743)). Qed.
Lemma lem3102753 : term45 = term45.
Proof. exact (MK_COMB (@lem3102752) (@lem3102750)). Qed.
Lemma lem3102754 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102755 : term49 = term49.
Proof. exact (MK_COMB (@lem3102754) (@lem3102736)). Qed.
Lemma lem3102756 : term50 = term50.
Proof. exact (MK_COMB (@lem3102755) (@lem3102753)). Qed.
Lemma lem3102757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102758 : term54 = term54.
Proof. exact (MK_COMB (@lem3102757) (@lem3102732)). Qed.
Lemma lem3102759 : term55 = term55.
Proof. exact (MK_COMB (@lem3102758) (@lem3102756)). Qed.
Lemma lem3102760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102761 : term59 = term59.
Proof. exact (MK_COMB (@lem3102760) (@lem3102728)). Qed.
Lemma lem3102762 : term60 = term60.
Proof. exact (MK_COMB (@lem3102761) (@lem3102759)). Qed.
Lemma lem3102763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102764 : term64 = term64.
Proof. exact (MK_COMB (@lem3102763) (@lem3102724)). Qed.
Lemma lem3102801 : term21 = term21.
Proof. exact (MK_COMB (@lem3102764) (@lem3102762)). Qed.
Lemma lem3102802 (h1 : term21) : term21.
Proof. exact (EQ_MP (@lem3102801) (@lem3102674 h1)). Qed.
Lemma lem3102813 (m : nat) (n : nat) (x : nat) : (term72 m n x) = (term72 m n x).
Proof. exact (eq_refl (term72 m n x)). Qed.
Lemma lem3102814 (m : nat) (n : nat) : (term74 m n) = (term74 m n).
Proof. exact (fun_ext (fun x : nat => @lem3102813 m n x)). Qed.
Lemma lem3102815 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102816 (m : nat) (n : nat) : (term75 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem3102815) (@lem3102814 m n)). Qed.
Lemma lem3102827 (n : nat) (m : nat) (x : nat) : (term72 n m x) = (term72 n m x).
Proof. exact (eq_refl (term72 n m x)). Qed.
Lemma lem3102828 (n : nat) (m : nat) : (term74 n m) = (term74 n m).
Proof. exact (fun_ext (fun x : nat => @lem3102827 n m x)). Qed.
Lemma lem3102829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102830 (n : nat) (m : nat) : (term75 n m) = (term75 n m).
Proof. exact (MK_COMB (@lem3102829) (@lem3102828 n m)). Qed.
Lemma lem3102831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3102832 (n : nat) (m : nat) : (term77 n m) = (term77 n m).
Proof. exact (MK_COMB (@lem3102831) (@lem3102830 n m)). Qed.
Lemma lem3102833 (m : nat) (n : nat) : (term79 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem3102832 n m) (@lem3102816 m n)). Qed.
Lemma lem3102840 (m : nat) (n : nat) : (term81 m n) = (term81 m n).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem3102841 (m : nat) (n : nat) : (term83 m n) = (term83 m n).
Proof. exact (MK_COMB (@lem3102840 m n) (@lem3102833 m n)). Qed.
Lemma lem3102842 (m : nat) (n : nat) (h1 : term14 m n) : term83 m n.
Proof. exact (EQ_MP (@lem3102841 m n) (@lem3102720 m n h1)). Qed.
Lemma lem3102861 (m : nat) (n : nat) : ((term32 m n) = (term33 m n)) = ((term32 m n) = (term33 m n)).
Proof. exact (eq_refl ((term32 m n) = (term33 m n))). Qed.
Lemma lem3102862 (m : nat) : (term34 m) = (term34 m).
Proof. exact (fun_ext (fun n : nat => @lem3102861 m n)). Qed.
Lemma lem3102863 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102864 (m : nat) : (term35 m) = (term35 m).
Proof. exact (MK_COMB (@lem3102863) (@lem3102862 m)). Qed.
Lemma lem3102865 : term36 = term36.
Proof. exact (fun_ext (fun m : nat => @lem3102864 m)). Qed.
Lemma lem3102866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102867 : term37 = term37.
Proof. exact (MK_COMB (@lem3102866) (@lem3102865)). Qed.
Lemma lem3102886 (m : nat) (n : nat) : ((term38 m n) = (term39 m n)) = ((term38 m n) = (term39 m n)).
Proof. exact (eq_refl ((term38 m n) = (term39 m n))). Qed.
Lemma lem3102887 (m : nat) : (term40 m) = (term40 m).
Proof. exact (fun_ext (fun n : nat => @lem3102886 m n)). Qed.
Lemma lem3102888 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102889 (m : nat) : (term41 m) = (term41 m).
Proof. exact (MK_COMB (@lem3102888) (@lem3102887 m)). Qed.
Lemma lem3102890 : term42 = term42.
Proof. exact (fun_ext (fun m : nat => @lem3102889 m)). Qed.
Lemma lem3102891 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102892 : term43 = term43.
Proof. exact (MK_COMB (@lem3102891) (@lem3102890)). Qed.
Lemma lem3102893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102894 : term44 = term44.
Proof. exact (MK_COMB (@lem3102893) (@lem3102892)). Qed.
Lemma lem3102895 : term45 = term45.
Proof. exact (MK_COMB (@lem3102894) (@lem3102867)). Qed.
Lemma lem3102908 (m : nat) : ((term46 m) = m) = ((term46 m) = m).
Proof. exact (eq_refl ((term46 m) = m)). Qed.
Lemma lem3102909 : term47 = term47.
Proof. exact (fun_ext (fun m : nat => @lem3102908 m)). Qed.
Lemma lem3102910 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102911 : term48 = term48.
Proof. exact (MK_COMB (@lem3102910) (@lem3102909)). Qed.
Lemma lem3102912 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102913 : term49 = term49.
Proof. exact (MK_COMB (@lem3102912) (@lem3102911)). Qed.
Lemma lem3102914 : term50 = term50.
Proof. exact (MK_COMB (@lem3102913) (@lem3102895)). Qed.
Lemma lem3102927 (n : nat) : ((term51 n) = n) = ((term51 n) = n).
Proof. exact (eq_refl ((term51 n) = n)). Qed.
Lemma lem3102928 : term52 = term52.
Proof. exact (fun_ext (fun n : nat => @lem3102927 n)). Qed.
Lemma lem3102929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102930 : term53 = term53.
Proof. exact (MK_COMB (@lem3102929) (@lem3102928)). Qed.
Lemma lem3102931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102932 : term54 = term54.
Proof. exact (MK_COMB (@lem3102931) (@lem3102930)). Qed.
Lemma lem3102933 : term55 = term55.
Proof. exact (MK_COMB (@lem3102932) (@lem3102914)). Qed.
Lemma lem3102946 (m : nat) : ((term56 m) = (NUMERAL 0)) = ((term56 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term56 m) = (NUMERAL 0))). Qed.
Lemma lem3102947 : term57 = term57.
Proof. exact (fun_ext (fun m : nat => @lem3102946 m)). Qed.
Lemma lem3102948 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102949 : term58 = term58.
Proof. exact (MK_COMB (@lem3102948) (@lem3102947)). Qed.
Lemma lem3102950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102951 : term59 = term59.
Proof. exact (MK_COMB (@lem3102950) (@lem3102949)). Qed.
Lemma lem3102952 : term60 = term60.
Proof. exact (MK_COMB (@lem3102951) (@lem3102933)). Qed.
Lemma lem3102965 (n : nat) : ((term61 n) = (NUMERAL 0)) = ((term61 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term61 n) = (NUMERAL 0))). Qed.
Lemma lem3102966 : term62 = term62.
Proof. exact (fun_ext (fun n : nat => @lem3102965 n)). Qed.
Lemma lem3102967 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3102968 : term63 = term63.
Proof. exact (MK_COMB (@lem3102967) (@lem3102966)). Qed.
Lemma lem3102969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3102970 : term64 = term64.
Proof. exact (MK_COMB (@lem3102969) (@lem3102968)). Qed.
Lemma lem3102971 : term21 = term21.
Proof. exact (MK_COMB (@lem3102970) (@lem3102952)). Qed.
Lemma lem3102972 (h1 : term21) : term21.
Proof. exact (EQ_MP (@lem3102971) (@lem3102802 h1)). Qed.
Lemma lem3102973 (h1 : term21) : term60.
Proof. exact (proj2 (@lem3102972 h1)). Qed.
Lemma lem3102975 (h1 : term21) : term55.
Proof. exact (proj2 (@lem3102973 h1)). Qed.
Lemma lem3102977 (h1 : term21) : term50.
Proof. exact (proj2 (@lem3102975 h1)). Qed.
Lemma lem3102980 (h1 : term21) : term48.
Proof. exact (proj1 (@lem3102977 h1)). Qed.
Lemma lem3102983 (m : nat) (n : nat) (h1 : term14 m n) : term79 m n.
Proof. exact (proj2 (@lem3102842 m n h1)). Qed.
Lemma lem3102985 (n : nat) (m : nat) (h1 : term75 n m) : term75 n m.
Proof. exact (h1). Qed.
Lemma lem3102986 (m : nat) (n : nat) (h1 : term75 m n) : term75 m n.
Proof. exact (h1). Qed.
Lemma lem3103009 (m : nat) : ((term46 m) = m) = ((term46 m) = m).
Proof. exact (eq_refl ((term46 m) = m)). Qed.
Lemma lem3103010 : term47 = term47.
Proof. exact (fun_ext (fun m : nat => @lem3103009 m)). Qed.
Lemma lem3103011 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3103013 : term48 = term48.
Proof. exact (MK_COMB (@lem3103011) (@lem3103010)). Qed.
Lemma lem3103014 (h1 : term21) : term48.
Proof. exact (EQ_MP (@lem3103013) (@lem3102980 h1)). Qed.
Lemma lem3103040 (n : nat) (m : nat) (x : nat) : (term72 n m x) = (term72 n m x).
Proof. exact (eq_refl (term72 n m x)). Qed.
Lemma lem3103041 (n : nat) (m : nat) : (term74 n m) = (term74 n m).
Proof. exact (fun_ext (fun x : nat => @lem3103040 n m x)). Qed.
Lemma lem3103042 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3103044 (n : nat) (m : nat) : (term75 n m) = (term75 n m).
Proof. exact (MK_COMB (@lem3103042) (@lem3103041 n m)). Qed.
Lemma lem3103045 (n : nat) (m : nat) (h1 : term75 n m) : term75 n m.
Proof. exact (EQ_MP (@lem3103044 n m) (@lem3102985 n m h1)). Qed.
Lemma lem3103068 (m : nat) : ((term46 m) = m) = ((term46 m) = m).
Proof. exact (eq_refl ((term46 m) = m)). Qed.
Lemma lem3103069 : term47 = term47.
Proof. exact (fun_ext (fun m : nat => @lem3103068 m)). Qed.
Lemma lem3103070 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3103072 : term48 = term48.
Proof. exact (MK_COMB (@lem3103070) (@lem3103069)). Qed.
Lemma lem3103073 (h1 : term21) : term48.
Proof. exact (EQ_MP (@lem3103072) (@lem3102980 h1)). Qed.
Lemma lem3103099 (m : nat) (n : nat) (x : nat) : (term72 m n x) = (term72 m n x).
Proof. exact (eq_refl (term72 m n x)). Qed.
Lemma lem3103100 (m : nat) (n : nat) : (term74 m n) = (term74 m n).
Proof. exact (fun_ext (fun x : nat => @lem3103099 m n x)). Qed.
Lemma lem3103101 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3103103 (m : nat) (n : nat) : (term75 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem3103101) (@lem3103100 m n)). Qed.
Lemma lem3103104 (m : nat) (n : nat) (h1 : term75 m n) : term75 m n.
Proof. exact (EQ_MP (@lem3103103 m n) (@lem3102986 m n h1)). Qed.
Lemma lem3103114 (_32156 : nat) (h1 : term21) : term84 _32156.
Proof. exact (@lem3103014 h1 _32156). Qed.
Lemma lem3103115 (_32156 : nat) : (term84 _32156) = ((term46 _32156) = _32156).
Proof. exact (eq_refl (term84 _32156)). Qed.
Lemma lem3103129 (_32161 : nat) (n : nat) (m : nat) (h1 : term75 n m) : term85 n m _32161.
Proof. exact (@lem3103045 n m h1 _32161). Qed.
Lemma lem3103130 (n : nat) (m : nat) (_32161 : nat) : (term85 n m _32161) = (term72 n m _32161).
Proof. exact (eq_refl (term85 n m _32161)). Qed.
Lemma lem3103141 (_32165 : nat) (h1 : term21) : term84 _32165.
Proof. exact (@lem3103073 h1 _32165). Qed.
Lemma lem3103142 (_32165 : nat) : (term84 _32165) = ((term46 _32165) = _32165).
Proof. exact (eq_refl (term84 _32165)). Qed.
Lemma lem3103156 (_32170 : nat) (m : nat) (n : nat) (h1 : term75 m n) : term85 m n _32170.
Proof. exact (@lem3103104 m n h1 _32170). Qed.
Lemma lem3103157 (m : nat) (n : nat) (_32170 : nat) : (term85 m n _32170) = (term72 m n _32170).
Proof. exact (eq_refl (term85 m n _32170)). Qed.
Lemma lem3103172 (m : nat) (n : nat) (h1 : term14 m n) : m = n.
Proof. exact (proj1 (@lem3102842 m n h1)). Qed.
Lemma lem3103174 (_32161 : nat) (n : nat) (m : nat) (h1 : term75 n m) : term72 n m _32161.
Proof. exact (EQ_MP (@lem3103130 n m _32161) (@lem3103129 _32161 n m h1)). Qed.
Lemma lem3103188 (m : nat) (n : nat) (h1 : term14 m n) : m = n.
Proof. exact (proj1 (@lem3102842 m n h1)). Qed.
Lemma lem3103190 (_32170 : nat) (m : nat) (n : nat) (h1 : term75 m n) : term72 m n _32170.
Proof. exact (EQ_MP (@lem3103157 m n _32170) (@lem3103156 _32170 m n h1)). Qed.
Lemma lem3103289 (n : nat) (_32161 : nat) : (term86 n _32161) = (term86 n _32161).
Proof. exact (eq_refl (term86 n _32161)). Qed.
Lemma lem3103290 (_32161 : nat) (m : nat) (n : nat) (h1 : term14 m n) : (term87 n _32161 m) = (term88 _32161 n).
Proof. exact (MK_COMB (@lem3103289 n _32161) (@lem3103172 m n h1)). Qed.
Lemma lem3103291 (n : nat) (_32161 : nat) : (term88 _32161 n) = (term89 n _32161).
Proof. exact (eq_refl (term88 _32161 n)). Qed.
Lemma lem3103292 (n : nat) (_32161 : nat) (m : nat) : (term90 n _32161 m) = (term90 n _32161 m).
Proof. exact (eq_refl (term90 n _32161 m)). Qed.
Lemma lem3103293 (m : nat) (n : nat) (_32161 : nat) : ((term87 n _32161 m) = (term88 _32161 n)) = ((term87 n _32161 m) = (term89 n _32161)).
Proof. exact (MK_COMB (@lem3103292 n _32161 m) (@lem3103291 n _32161)). Qed.
Lemma lem3103294 (n : nat) (m : nat) (_32161 : nat) : (term87 n _32161 m) = (term72 n m _32161).
Proof. exact (eq_refl (term87 n _32161 m)). Qed.
Lemma lem3103295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3103296 (n : nat) (m : nat) (_32161 : nat) : (term90 n _32161 m) = (term91 n m _32161).
Proof. exact (MK_COMB (@lem3103295) (@lem3103294 n m _32161)). Qed.
Lemma lem3103297 (n : nat) (_32161 : nat) : (term89 n _32161) = (term89 n _32161).
Proof. exact (eq_refl (term89 n _32161)). Qed.
Lemma lem3103298 (m : nat) (n : nat) (_32161 : nat) : ((term87 n _32161 m) = (term89 n _32161)) = ((term72 n m _32161) = (term89 n _32161)).
Proof. exact (MK_COMB (@lem3103296 n m _32161) (@lem3103297 n _32161)). Qed.
Lemma lem3103299 (m : nat) (n : nat) (_32161 : nat) : ((term87 n _32161 m) = (term88 _32161 n)) = ((term72 n m _32161) = (term89 n _32161)).
Proof. exact (TRANS (@lem3103293 m n _32161) (@lem3103298 m n _32161)). Qed.
Lemma lem3103300 (_32161 : nat) (m : nat) (n : nat) (h1 : term14 m n) : (term72 n m _32161) = (term89 n _32161).
Proof. exact (EQ_MP (@lem3103299 m n _32161) (@lem3103290 _32161 m n h1)). Qed.
Lemma lem3103301 (_32161 : nat) (m : nat) (n : nat) (h1 : term75 n m) (h2 : term14 m n) : term89 n _32161.
Proof. exact (EQ_MP (@lem3103300 _32161 m n h2) (@lem3103174 _32161 n m h1)). Qed.
Lemma lem3103400 (n : nat) (_32170 : nat) : (term92 n _32170) = (term92 n _32170).
Proof. exact (eq_refl (term92 n _32170)). Qed.
Lemma lem3103401 (_32170 : nat) (m : nat) (n : nat) (h1 : term14 m n) : (term93 n _32170 m) = (term94 _32170 n).
Proof. exact (MK_COMB (@lem3103400 n _32170) (@lem3103188 m n h1)). Qed.
Lemma lem3103402 (n : nat) (_32170 : nat) : (term94 _32170 n) = (term89 n _32170).
Proof. exact (eq_refl (term94 _32170 n)). Qed.
Lemma lem3103403 (n : nat) (_32170 : nat) (m : nat) : (term95 n _32170 m) = (term95 n _32170 m).
Proof. exact (eq_refl (term95 n _32170 m)). Qed.
Lemma lem3103404 (m : nat) (n : nat) (_32170 : nat) : ((term93 n _32170 m) = (term94 _32170 n)) = ((term93 n _32170 m) = (term89 n _32170)).
Proof. exact (MK_COMB (@lem3103403 n _32170 m) (@lem3103402 n _32170)). Qed.
Lemma lem3103405 (m : nat) (n : nat) (_32170 : nat) : (term93 n _32170 m) = (term72 m n _32170).
Proof. exact (eq_refl (term93 n _32170 m)). Qed.
Lemma lem3103406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3103407 (m : nat) (n : nat) (_32170 : nat) : (term95 n _32170 m) = (term91 m n _32170).
Proof. exact (MK_COMB (@lem3103406) (@lem3103405 m n _32170)). Qed.
Lemma lem3103408 (n : nat) (_32170 : nat) : (term89 n _32170) = (term89 n _32170).
Proof. exact (eq_refl (term89 n _32170)). Qed.
Lemma lem3103409 (m : nat) (n : nat) (_32170 : nat) : ((term93 n _32170 m) = (term89 n _32170)) = ((term72 m n _32170) = (term89 n _32170)).
Proof. exact (MK_COMB (@lem3103407 m n _32170) (@lem3103408 n _32170)). Qed.
Lemma lem3103410 (m : nat) (n : nat) (_32170 : nat) : ((term93 n _32170 m) = (term94 _32170 n)) = ((term72 m n _32170) = (term89 n _32170)).
Proof. exact (TRANS (@lem3103404 m n _32170) (@lem3103409 m n _32170)). Qed.
Lemma lem3103411 (_32170 : nat) (m : nat) (n : nat) (h1 : term14 m n) : (term72 m n _32170) = (term89 n _32170).
Proof. exact (EQ_MP (@lem3103410 m n _32170) (@lem3103401 _32170 m n h1)). Qed.
Lemma lem3103412 (_32170 : nat) (m : nat) (n : nat) (h1 : term75 m n) (h2 : term14 m n) : term89 n _32170.
Proof. exact (EQ_MP (@lem3103411 _32170 m n h2) (@lem3103190 _32170 m n h1)). Qed.
Lemma lem3103468 (x : nat) (y : nat) (z : nat) : term96 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem3103470 (_32156 : nat) (h1 : term21) : (term46 _32156) = _32156.
Proof. exact (EQ_MP (@lem3103115 _32156) (@lem3103114 _32156 h1)). Qed.
Lemma lem3103471 (n : nat) (h1 : term21) : (term46 n) = n.
Proof. exact (@lem3103470 n h1). Qed.
Lemma lem3103472 (n : nat) (h1 : term21) : term97 n.
Proof. exact (fun h0 : term98 n => @lem3103471 n h1). Qed.
Lemma lem3103474 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3103475 (n : nat) : (term97 n) = ((term46 n) = n).
Proof. exact (@lem3103474 ((term46 n) = n)). Qed.
Lemma lem3103476 (n : nat) (h1 : term21) : (term46 n) = n.
Proof. exact (EQ_MP (@lem3103475 n) (@lem3103472 n h1)). Qed.
Lemma lem3103478 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem3103479 (n : nat) : (term46 n) = (term46 n).
Proof. exact (@lem3103478 (term46 n)). Qed.
Lemma lem3103480 (n : nat) : term100 n.
Proof. exact (fun h0 : term101 n => @lem3103479 n). Qed.
Lemma lem3103482 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3103483 (n : nat) : (term100 n) = ((term46 n) = (term46 n)).
Proof. exact (@lem3103482 ((term46 n) = (term46 n))). Qed.
Lemma lem3103484 (n : nat) : (term46 n) = (term46 n).
Proof. exact (EQ_MP (@lem3103483 n) (@lem3103480 n)). Qed.
Lemma lem3103502 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3103503 (y : nat) (x : nat) (z : nat) : (term102 x y z) = (term103 y x z).
Proof. exact (@lem3103502 (y = z) (term104 x z)). Qed.
Lemma lem3103513 (x : nat) (y : nat) : (term105 x y) = (term105 x y).
Proof. exact (eq_refl (term105 x y)). Qed.
Lemma lem3103514 (y : nat) (x : nat) (z : nat) : (term96 x y z) = (term106 y x z).
Proof. exact (MK_COMB (@lem3103513 x y) (@lem3103503 y x z)). Qed.
Lemma lem3103518 (q : Prop) (p : Prop) (r : Prop) : (term107 p q r) = (term107 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3103519 (y : nat) (x : nat) (z : nat) : (term106 y x z) = (term108 y x z).
Proof. exact (@lem3103518 (y = z) (term104 x y) (term104 x z)). Qed.
Lemma lem3103541 (y : nat) (x : nat) (z : nat) : (term96 x y z) = (term108 y x z).
Proof. exact (TRANS (@lem3103514 y x z) (@lem3103519 y x z)). Qed.
Lemma lem3103542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3103543 (y : nat) (x : nat) (z : nat) : (term109 x y z) = (term110 y x z).
Proof. exact (MK_COMB (@lem3103542) (@lem3103541 y x z)). Qed.
Lemma lem3103565 (y : nat) (x : nat) (z : nat) : (term108 y x z) = (term108 y x z).
Proof. exact (eq_refl (term108 y x z)). Qed.
Lemma lem3103566 (y : nat) (x : nat) (z : nat) : ((term96 x y z) = (term108 y x z)) = ((term108 y x z) = (term108 y x z)).
Proof. exact (MK_COMB (@lem3103543 y x z) (@lem3103565 y x z)). Qed.
Lemma lem3103568 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3103569 (x : Prop) : (x = x) = True.
Proof. exact (@lem3103568 Prop x). Qed.
Lemma lem3103570 (y : nat) (x : nat) (z : nat) : ((term108 y x z) = (term108 y x z)) = True.
Proof. exact (@lem3103569 (term108 y x z)). Qed.
Lemma lem3103571 (y : nat) (x : nat) (z : nat) : ((term96 x y z) = (term108 y x z)) = True.
Proof. exact (TRANS (@lem3103566 y x z) (@lem3103570 y x z)). Qed.
Lemma lem3103572 (y : nat) (x : nat) (z : nat) : True = ((term96 x y z) = (term108 y x z)).
Proof. exact (SYM (@lem3103571 y x z)). Qed.
Lemma lem3103573 (y : nat) (x : nat) (z : nat) : (term96 x y z) = (term108 y x z).
Proof. exact (EQ_MP (@lem3103572 y x z) (@lem0)). Qed.
Lemma lem3103574 (y : nat) (x : nat) (z : nat) : term108 y x z.
Proof. exact (EQ_MP (@lem3103573 y x z) (@lem3103468 x y z)). Qed.
Lemma lem3103576 (b : Prop) (a : Prop) : (a \/ b) = (term111 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3103577 (x : nat) (y : nat) (z : nat) : (term108 y x z) = (term112 x y z).
Proof. exact (@lem3103576 (term113 y x z) (y = z)). Qed.
Lemma lem3103579 (a : Prop) (b : Prop) : (term114 a b) = (term115 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3103580 (y : nat) (x : nat) (z : nat) : (term116 y x z) = (term117 y x z).
Proof. exact (@lem3103579 (term104 x y) (term104 x z)). Qed.
Lemma lem3103582 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3103583 (x : nat) (y : nat) : (term119 x y) = (x = y).
Proof. exact (@lem3103582 (x = y)). Qed.
Lemma lem3103584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3103585 (x : nat) (y : nat) : (term120 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem3103584) (@lem3103583 x y)). Qed.
Lemma lem3103587 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3103588 (x : nat) (z : nat) : (term119 x z) = (x = z).
Proof. exact (@lem3103587 (x = z)). Qed.
Lemma lem3103589 (y : nat) (x : nat) (z : nat) : (term117 y x z) = (term121 y x z).
Proof. exact (MK_COMB (@lem3103585 x y) (@lem3103588 x z)). Qed.
Lemma lem3103590 (y : nat) (x : nat) (z : nat) : (term116 y x z) = (term121 y x z).
Proof. exact (TRANS (@lem3103580 y x z) (@lem3103589 y x z)). Qed.
Lemma lem3103591 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3103592 (y : nat) (x : nat) (z : nat) : (term122 y x z) = (term123 y x z).
Proof. exact (MK_COMB (@lem3103591) (@lem3103590 y x z)). Qed.
Lemma lem3103593 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3103594 (x : nat) (y : nat) (z : nat) : (term112 x y z) = (term124 x y z).
Proof. exact (MK_COMB (@lem3103592 y x z) (@lem3103593 y z)). Qed.
Lemma lem3103595 (x : nat) (y : nat) (z : nat) : (term108 y x z) = (term124 x y z).
Proof. exact (TRANS (@lem3103577 x y z) (@lem3103594 x y z)). Qed.
Lemma lem3103597 (n : nat) (h1 : term21) : term125 n.
Proof. exact (conj (@lem3103476 n h1) (@lem3103484 n)). Qed.
Lemma lem3103599 (x : nat) (y : nat) (z : nat) : term124 x y z.
Proof. exact (EQ_MP (@lem3103595 x y z) (@lem3103574 y x z)). Qed.
Lemma lem3103600 (n : nat) : term126 n.
Proof. exact (@lem3103599 (term46 n) n (term46 n)). Qed.
Lemma lem3103603 (n : nat) (h1 : term21) : n = (term46 n).
Proof. exact (@lem3103600 n (@lem3103597 n h1)). Qed.
Lemma lem3103604 (n : nat) (h1 : term21) : term127 n.
Proof. exact (fun h0 : term128 n => @lem3103603 n h1). Qed.
Lemma lem3103606 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3103607 (n : nat) : (term127 n) = (n = (term46 n)).
Proof. exact (@lem3103606 (n = (term46 n))). Qed.
Lemma lem3103608 (n : nat) (h1 : term21) : n = (term46 n).
Proof. exact (EQ_MP (@lem3103607 n) (@lem3103604 n h1)). Qed.
Lemma lem3103611 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3103613 (n : nat) (_32161 : nat) : (term89 n _32161) = (term129 n _32161).
Proof. exact (@lem3103611 (n = (Nat.mul n _32161))). Qed.
Lemma lem3103616 (_32161 : nat) (m : nat) (n : nat) (h1 : term75 n m) (h2 : term14 m n) : term129 n _32161.
Proof. exact (EQ_MP (@lem3103613 n _32161) (@lem3103301 _32161 m n h1 h2)). Qed.
Lemma lem3103617 (m : nat) (n : nat) (h1 : term75 n m) (h2 : term14 m n) : term130 n.
Proof. exact (@lem3103616 term131 m n h1 h2). Qed.
Lemma lem3103620 (m : nat) (n : nat) (h1 : term75 n m) (h2 : term14 m n) (h3 : term21) : False.
Proof. exact (@lem3103617 m n h1 h2 (@lem3103608 n h3)). Qed.
Lemma lem3103621 (m : nat) (n : nat) (h1 : term75 n m) (h2 : term14 m n) (h3 : term21) : term132.
Proof. exact (fun h0 : ~ False => @lem3103620 m n h1 h2 h3). Qed.
Lemma lem3103623 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3103624 : term132 = False.
Proof. exact (@lem3103623 False). Qed.
Lemma lem3103681 (x : nat) (y : nat) (z : nat) : term96 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem3103683 (_32165 : nat) (h1 : term21) : (term46 _32165) = _32165.
Proof. exact (EQ_MP (@lem3103142 _32165) (@lem3103141 _32165 h1)). Qed.
Lemma lem3103684 (n : nat) (h1 : term21) : (term46 n) = n.
Proof. exact (@lem3103683 n h1). Qed.
Lemma lem3103685 (n : nat) (h1 : term21) : term97 n.
Proof. exact (fun h0 : term98 n => @lem3103684 n h1). Qed.
Lemma lem3103687 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3103688 (n : nat) : (term97 n) = ((term46 n) = n).
Proof. exact (@lem3103687 ((term46 n) = n)). Qed.
Lemma lem3103689 (n : nat) (h1 : term21) : (term46 n) = n.
Proof. exact (EQ_MP (@lem3103688 n) (@lem3103685 n h1)). Qed.
Lemma lem3103691 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem3103692 (n : nat) : (term46 n) = (term46 n).
Proof. exact (@lem3103691 (term46 n)). Qed.
Lemma lem3103693 (n : nat) : term100 n.
Proof. exact (fun h0 : term101 n => @lem3103692 n). Qed.
Lemma lem3103695 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3103696 (n : nat) : (term100 n) = ((term46 n) = (term46 n)).
Proof. exact (@lem3103695 ((term46 n) = (term46 n))). Qed.
Lemma lem3103697 (n : nat) : (term46 n) = (term46 n).
Proof. exact (EQ_MP (@lem3103696 n) (@lem3103693 n)). Qed.
Lemma lem3103715 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3103716 (y : nat) (x : nat) (z : nat) : (term102 x y z) = (term103 y x z).
Proof. exact (@lem3103715 (y = z) (term104 x z)). Qed.
Lemma lem3103726 (x : nat) (y : nat) : (term105 x y) = (term105 x y).
Proof. exact (eq_refl (term105 x y)). Qed.
Lemma lem3103727 (y : nat) (x : nat) (z : nat) : (term96 x y z) = (term106 y x z).
Proof. exact (MK_COMB (@lem3103726 x y) (@lem3103716 y x z)). Qed.
Lemma lem3103731 (q : Prop) (p : Prop) (r : Prop) : (term107 p q r) = (term107 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3103732 (y : nat) (x : nat) (z : nat) : (term106 y x z) = (term108 y x z).
Proof. exact (@lem3103731 (y = z) (term104 x y) (term104 x z)). Qed.
Lemma lem3103754 (y : nat) (x : nat) (z : nat) : (term96 x y z) = (term108 y x z).
Proof. exact (TRANS (@lem3103727 y x z) (@lem3103732 y x z)). Qed.
Lemma lem3103755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3103756 (y : nat) (x : nat) (z : nat) : (term109 x y z) = (term110 y x z).
Proof. exact (MK_COMB (@lem3103755) (@lem3103754 y x z)). Qed.
Lemma lem3103778 (y : nat) (x : nat) (z : nat) : (term108 y x z) = (term108 y x z).
Proof. exact (eq_refl (term108 y x z)). Qed.
Lemma lem3103779 (y : nat) (x : nat) (z : nat) : ((term96 x y z) = (term108 y x z)) = ((term108 y x z) = (term108 y x z)).
Proof. exact (MK_COMB (@lem3103756 y x z) (@lem3103778 y x z)). Qed.
Lemma lem3103781 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3103782 (x : Prop) : (x = x) = True.
Proof. exact (@lem3103781 Prop x). Qed.
Lemma lem3103783 (y : nat) (x : nat) (z : nat) : ((term108 y x z) = (term108 y x z)) = True.
Proof. exact (@lem3103782 (term108 y x z)). Qed.
Lemma lem3103784 (y : nat) (x : nat) (z : nat) : ((term96 x y z) = (term108 y x z)) = True.
Proof. exact (TRANS (@lem3103779 y x z) (@lem3103783 y x z)). Qed.
Lemma lem3103785 (y : nat) (x : nat) (z : nat) : True = ((term96 x y z) = (term108 y x z)).
Proof. exact (SYM (@lem3103784 y x z)). Qed.
Lemma lem3103786 (y : nat) (x : nat) (z : nat) : (term96 x y z) = (term108 y x z).
Proof. exact (EQ_MP (@lem3103785 y x z) (@lem0)). Qed.
Lemma lem3103787 (y : nat) (x : nat) (z : nat) : term108 y x z.
Proof. exact (EQ_MP (@lem3103786 y x z) (@lem3103681 x y z)). Qed.
Lemma lem3103789 (b : Prop) (a : Prop) : (a \/ b) = (term111 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3103790 (x : nat) (y : nat) (z : nat) : (term108 y x z) = (term112 x y z).
Proof. exact (@lem3103789 (term113 y x z) (y = z)). Qed.
Lemma lem3103792 (a : Prop) (b : Prop) : (term114 a b) = (term115 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3103793 (y : nat) (x : nat) (z : nat) : (term116 y x z) = (term117 y x z).
Proof. exact (@lem3103792 (term104 x y) (term104 x z)). Qed.
Lemma lem3103795 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3103796 (x : nat) (y : nat) : (term119 x y) = (x = y).
Proof. exact (@lem3103795 (x = y)). Qed.
Lemma lem3103797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3103798 (x : nat) (y : nat) : (term120 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem3103797) (@lem3103796 x y)). Qed.
Lemma lem3103800 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3103801 (x : nat) (z : nat) : (term119 x z) = (x = z).
Proof. exact (@lem3103800 (x = z)). Qed.
Lemma lem3103802 (y : nat) (x : nat) (z : nat) : (term117 y x z) = (term121 y x z).
Proof. exact (MK_COMB (@lem3103798 x y) (@lem3103801 x z)). Qed.
Lemma lem3103803 (y : nat) (x : nat) (z : nat) : (term116 y x z) = (term121 y x z).
Proof. exact (TRANS (@lem3103793 y x z) (@lem3103802 y x z)). Qed.
Lemma lem3103804 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3103805 (y : nat) (x : nat) (z : nat) : (term122 y x z) = (term123 y x z).
Proof. exact (MK_COMB (@lem3103804) (@lem3103803 y x z)). Qed.
Lemma lem3103806 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3103807 (x : nat) (y : nat) (z : nat) : (term112 x y z) = (term124 x y z).
Proof. exact (MK_COMB (@lem3103805 y x z) (@lem3103806 y z)). Qed.
Lemma lem3103808 (x : nat) (y : nat) (z : nat) : (term108 y x z) = (term124 x y z).
Proof. exact (TRANS (@lem3103790 x y z) (@lem3103807 x y z)). Qed.
Lemma lem3103810 (n : nat) (h1 : term21) : term125 n.
Proof. exact (conj (@lem3103689 n h1) (@lem3103697 n)). Qed.
Lemma lem3103812 (x : nat) (y : nat) (z : nat) : term124 x y z.
Proof. exact (EQ_MP (@lem3103808 x y z) (@lem3103787 y x z)). Qed.
Lemma lem3103813 (n : nat) : term126 n.
Proof. exact (@lem3103812 (term46 n) n (term46 n)). Qed.
Lemma lem3103816 (n : nat) (h1 : term21) : n = (term46 n).
Proof. exact (@lem3103813 n (@lem3103810 n h1)). Qed.
Lemma lem3103817 (n : nat) (h1 : term21) : term127 n.
Proof. exact (fun h0 : term128 n => @lem3103816 n h1). Qed.
Lemma lem3103819 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3103820 (n : nat) : (term127 n) = (n = (term46 n)).
Proof. exact (@lem3103819 (n = (term46 n))). Qed.
Lemma lem3103821 (n : nat) (h1 : term21) : n = (term46 n).
Proof. exact (EQ_MP (@lem3103820 n) (@lem3103817 n h1)). Qed.
Lemma lem3103824 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3103826 (n : nat) (_32170 : nat) : (term89 n _32170) = (term129 n _32170).
Proof. exact (@lem3103824 (n = (Nat.mul n _32170))). Qed.
Lemma lem3103829 (_32170 : nat) (m : nat) (n : nat) (h1 : term75 m n) (h2 : term14 m n) : term129 n _32170.
Proof. exact (EQ_MP (@lem3103826 n _32170) (@lem3103412 _32170 m n h1 h2)). Qed.
Lemma lem3103830 (m : nat) (n : nat) (h1 : term75 m n) (h2 : term14 m n) : term130 n.
Proof. exact (@lem3103829 term131 m n h1 h2). Qed.
Lemma lem3103833 (m : nat) (n : nat) (h1 : term75 m n) (h2 : term14 m n) (h3 : term21) : False.
Proof. exact (@lem3103830 m n h1 h2 (@lem3103821 n h3)). Qed.
Lemma lem3103834 (m : nat) (n : nat) (h1 : term75 m n) (h2 : term14 m n) (h3 : term21) : term132.
Proof. exact (fun h0 : ~ False => @lem3103833 m n h1 h2 h3). Qed.
Lemma lem3103836 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3103837 : term132 = False.
Proof. exact (@lem3103836 False). Qed.
Lemma lem3103839 (m : nat) (n : nat) (h1 : term75 m n) (h2 : term14 m n) (h3 : term21) : False.
Proof. exact (EQ_MP (@lem3103837) (@lem3103834 m n h1 h2 h3)). Qed.
Lemma lem3103840 (m : nat) (n : nat) (h1 : term75 n m) (h2 : term14 m n) (h3 : term21) : False.
Proof. exact (EQ_MP (@lem3103624) (@lem3103621 m n h1 h2 h3)). Qed.
Lemma lem3103841 (m : nat) (n : nat) (h1 : term75 m n) (h2 : term14 m n) (h3 : term21) : (term75 m n) = False.
Proof. exact (prop_ext (fun h4 : term75 m n => @lem3103839 m n h1 h2 h3) (fun h4 : False => @lem3103104 m n h1)). Qed.
Lemma lem3103842 (m : nat) (n : nat) (h1 : term75 m n) (h2 : term14 m n) (h3 : term21) : False.
Proof. exact (EQ_MP (@lem3103841 m n h1 h2 h3) (@lem3103104 m n h1)). Qed.
Lemma lem3103843 (m : nat) (n : nat) (h1 : term75 n m) (h2 : term14 m n) (h3 : term21) : (term75 n m) = False.
Proof. exact (prop_ext (fun h4 : term75 n m => @lem3103840 m n h1 h2 h3) (fun h4 : False => @lem3103045 n m h1)). Qed.
Lemma lem3103844 (m : nat) (n : nat) (h1 : term75 n m) (h2 : term14 m n) (h3 : term21) : False.
Proof. exact (EQ_MP (@lem3103843 m n h1 h2 h3) (@lem3103045 n m h1)). Qed.
Lemma lem3103845 (m : nat) (n : nat) (h1 : term14 m n) (h2 : term21) : False.
Proof. exact (or_elim (@lem3102983 m n h1) (fun h0 : term75 n m => @lem3103844 m n h0 h1 h2) (fun h0 : term75 m n => @lem3103842 m n h0 h1 h2)). Qed.
Lemma lem3103846 (m : nat) (n : nat) (h1 : term14 m n) (h2 : term21) : term21 = False.
Proof. exact (prop_ext (fun h3 : term21 => @lem3103845 m n h1 h2) (fun h3 : False => @lem3102972 h2)). Qed.
Lemma lem3103847 (m : nat) (n : nat) (h1 : term14 m n) (h2 : term21) : False.
Proof. exact (EQ_MP (@lem3103846 m n h1 h2) (@lem3102972 h2)). Qed.
Lemma lem3103848 (m : nat) (n : nat) (h1 : term14 m n) (h2 : term21) : term21 = False.
Proof. exact (prop_ext (fun h3 : term21 => @lem3103847 m n h1 h2) (fun h3 : False => @lem3102802 h2)). Qed.
Lemma lem3103849 (m : nat) (n : nat) (h1 : term14 m n) (h2 : term21) : False.
Proof. exact (EQ_MP (@lem3103848 m n h1 h2) (@lem3102802 h2)). Qed.
Lemma lem3103850 (m : nat) (n : nat) (h1 : term14 m n) : term19.
Proof. exact (fun h0 : term21 => @lem3103849 m n h1 h0). Qed.
Lemma lem3103851 : term19 = term20.
Proof. exact (@lem69 term21). Qed.
Lemma lem3103852 (m : nat) (n : nat) (h1 : term14 m n) : term20.
Proof. exact (EQ_MP (@lem3103851) (@lem3103850 m n h1)). Qed.
Lemma lem3103853 (m : nat) (n : nat) : term23 m n.
Proof. exact (fun h0 : term14 m n => @lem3103852 m n h0). Qed.
Lemma lem3103858 (n : nat) : term27 n.
Proof. exact (fun m : nat => @lem3103853 m n). Qed.
Lemma lem3103863 : term31.
Proof. exact (fun n : nat => @lem3103858 n). Qed.
Lemma lem3103864 : term30.
Proof. exact (EQ_MP (@lem3102672) (@lem3103863)). Qed.
Lemma lem3103865 (n : nat) : term133 n.
Proof. exact (@lem3103864 n). Qed.
Lemma lem3103866 (n : nat) : (term133 n) = (term26 n).
Proof. exact (eq_refl (term133 n)). Qed.
Lemma lem3103867 (n : nat) : term26 n.
Proof. exact (EQ_MP (@lem3103866 n) (@lem3103865 n)). Qed.
Lemma lem3103868 (n : nat) (m : nat) : term134 n m.
Proof. exact (@lem3103867 n m). Qed.
Lemma lem3103869 (m : nat) (n : nat) : (term134 n m) = (term15 m n).
Proof. exact (eq_refl (term134 n m)). Qed.
Lemma lem3103870 (m : nat) (n : nat) : term15 m n.
Proof. exact (EQ_MP (@lem3103869 m n) (@lem3103868 n m)). Qed.
Lemma lem3103872 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem3102418 m n (@lem3103870 m n)). Qed.
Lemma lem3103873 (m : nat) (n : nat) (h1 : term14 m n) : term19.
Proof. exact (@lem3103872 m n (@lem3102403 m n h1)). Qed.
Lemma lem3103874 (m : nat) (n : nat) (h1 : term14 m n) : False.
Proof. exact (@lem3103873 m n h1 (@lem81645)). Qed.
Lemma lem3103875 (m : nat) (n : nat) (h1 : term14 m n) : (term14 m n) = False.
Proof. exact (prop_ext (fun h2 : term14 m n => @lem3103874 m n h1) (fun h2 : False => @lem3102403 m n h1)). Qed.
Lemma lem3103876 (m : nat) (n : nat) (h1 : term14 m n) : False.
Proof. exact (EQ_MP (@lem3103875 m n h1) (@lem3102403 m n h1)). Qed.
Lemma lem3103877 (m : nat) (n : nat) : term13 m n.
Proof. exact (fun h0 : term14 m n => @lem3103876 m n h0). Qed.
Lemma lem3103878 (m : nat) (n : nat) : term11 m n.
Proof. exact (EQ_MP (@lem3102402 m n) (@lem3103877 m n)). Qed.
Lemma lem3103879 (n : nat) (m : nat) : term10 n m.
Proof. exact (EQ_MP (@lem3102398 n m) (@lem3103878 m n)). Qed.
Lemma lem3103880 (n : nat) (m : nat) (h1 : term7 n m) : term7 n m.
Proof. exact (h1). Qed.
Lemma lem3103881 (n : nat) (m : nat) (h1 : num_divides n m) : num_divides n m.
Proof. exact (h1). Qed.
Lemma lem3103883 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem3102349 m n) (@lem3102348 m n)). Qed.
Lemma lem3103884 (n : nat) (m : nat) : term3 n m.
Proof. exact (@lem3103883 n m). Qed.
Lemma lem3103885 (n : nat) (m : nat) (h1 : num_divides n m) : term135 n m.
Proof. exact (@lem3103884 n m (@lem3103881 n m h1)). Qed.
Lemma lem3103886 (m : nat) (n : nat) (h1 : num_divides m n) : num_divides m n.
Proof. exact (h1). Qed.
Lemma lem3103888 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem3102349 m n) (@lem3102348 m n)). Qed.
Lemma lem3103889 (m : nat) (n : nat) (h1 : num_divides m n) : term135 m n.
Proof. exact (@lem3103888 m n (@lem3103886 m n h1)). Qed.
Lemma lem3103941 (n : nat) (m : nat) : (term136 n m) = (term137 n m).
Proof. exact (@lem17045 (term138 n) (Peano.le n m)). Qed.
Lemma lem3103942 (m : nat) : (term139 m) = (term139 m).
Proof. exact (eq_refl (term139 m)). Qed.
Lemma lem3103943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3103944 (n : nat) (m : nat) : (term140 n m) = (term141 n m).
Proof. exact (MK_COMB (@lem3103943) (@lem3103941 n m)). Qed.
Lemma lem3103945 (n : nat) (m : nat) : (term142 n m) = (term143 n m).
Proof. exact (MK_COMB (@lem3103944 n m) (@lem3103942 m)). Qed.
Lemma lem3103946 (n : nat) (m : nat) : (term144 n m) = (term142 n m).
Proof. exact (@lem17160 (term145 n m) (m = (NUMERAL 0))). Qed.
Lemma lem3103947 (n : nat) (m : nat) : (term144 n m) = (term143 n m).
Proof. exact (TRANS (@lem3103946 n m) (@lem3103945 n m)). Qed.
Lemma lem3103954 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (@lem17045 (term138 m) (Peano.le m n)). Qed.
Lemma lem3103955 (n : nat) : (term139 n) = (term139 n).
Proof. exact (eq_refl (term139 n)). Qed.
Lemma lem3103956 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3103957 (m : nat) (n : nat) : (term140 m n) = (term141 m n).
Proof. exact (MK_COMB (@lem3103956) (@lem3103954 m n)). Qed.
Lemma lem3103958 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (MK_COMB (@lem3103957 m n) (@lem3103955 n)). Qed.
Lemma lem3103959 (m : nat) (n : nat) : (term144 m n) = (term142 m n).
Proof. exact (@lem17160 (term145 m n) (n = (NUMERAL 0))). Qed.
Lemma lem3103960 (m : nat) (n : nat) : (term144 m n) = (term143 m n).
Proof. exact (TRANS (@lem3103959 m n) (@lem3103958 m n)). Qed.
Lemma lem3103961 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem3103962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3103963 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (MK_COMB (@lem3103962) (@lem3103960 m n)). Qed.
Lemma lem3103964 (m : nat) (n : nat) : (term148 m n) = (term149 m n).
Proof. exact (MK_COMB (@lem3103963 m n) (@lem3103961 m n)). Qed.
Lemma lem3103965 (m : nat) (n : nat) : (term150 m n) = (term148 m n).
Proof. exact (@lem17265 (term135 m n) (m = n)). Qed.
Lemma lem3103966 (m : nat) (n : nat) : (term150 m n) = (term149 m n).
Proof. exact (TRANS (@lem3103965 m n) (@lem3103964 m n)). Qed.
Lemma lem3103967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3103968 (n : nat) (m : nat) : (term146 n m) = (term147 n m).
Proof. exact (MK_COMB (@lem3103967) (@lem3103947 n m)). Qed.
Lemma lem3103969 (m : nat) (n : nat) : (term151 m n) = (term152 m n).
Proof. exact (MK_COMB (@lem3103968 n m) (@lem3103966 m n)). Qed.
Lemma lem3103970 (m : nat) (n : nat) : (term153 m n) = (term151 m n).
Proof. exact (@lem17265 (term135 n m) (term150 m n)). Qed.
Lemma lem3104066 (m : nat) (n : nat) : (term153 m n) = (term152 m n).
Proof. exact (TRANS (@lem3103970 m n) (@lem3103969 m n)). Qed.
Lemma lem3104068 (m : nat) (n : nat) : (Peano.le m n) = (term154 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3104069 (n : nat) : (term138 n) = (term155 n).
Proof. exact (@lem3104068 term131 n). Qed.
Lemma lem3104070 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3104071 (n : nat) : (term156 n) = (term157 n).
Proof. exact (MK_COMB (@lem3104070) (@lem3104069 n)). Qed.
Lemma lem3104072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3104073 (n : nat) : (term158 n) = (term159 n).
Proof. exact (MK_COMB (@lem3104072) (@lem3104071 n)). Qed.
Lemma lem3104075 (m : nat) (n : nat) : (Peano.le m n) = (term154 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3104076 (n : nat) (m : nat) : (Peano.le n m) = (term154 n m).
Proof. exact (@lem3104075 n m). Qed.
Lemma lem3104077 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3104078 (n : nat) (m : nat) : (term160 n m) = (term161 n m).
Proof. exact (MK_COMB (@lem3104077) (@lem3104076 n m)). Qed.
Lemma lem3104079 (n : nat) (m : nat) : (term137 n m) = (term162 n m).
Proof. exact (MK_COMB (@lem3104073 n) (@lem3104078 n m)). Qed.
Lemma lem3104080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104081 (n : nat) (m : nat) : (term141 n m) = (term163 n m).
Proof. exact (MK_COMB (@lem3104080) (@lem3104079 n m)). Qed.
Lemma lem3104083 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3104084 (m : nat) : (m = (NUMERAL 0)) = ((int_of_num m) = term164).
Proof. exact (@lem3104083 m (NUMERAL 0)). Qed.
Lemma lem3104087 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3104088 (m : nat) : (term139 m) = (term165 m).
Proof. exact (MK_COMB (@lem3104087) (@lem3104084 m)). Qed.
Lemma lem3104089 (n : nat) (m : nat) : (term143 n m) = (term166 n m).
Proof. exact (MK_COMB (@lem3104081 n m) (@lem3104088 m)). Qed.
Lemma lem3104090 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3104091 (n : nat) (m : nat) : (term147 n m) = (term167 n m).
Proof. exact (MK_COMB (@lem3104090) (@lem3104089 n m)). Qed.
Lemma lem3104093 (m : nat) (n : nat) : (Peano.le m n) = (term154 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3104094 (m : nat) : (term138 m) = (term155 m).
Proof. exact (@lem3104093 term131 m). Qed.
Lemma lem3104095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3104096 (m : nat) : (term156 m) = (term157 m).
Proof. exact (MK_COMB (@lem3104095) (@lem3104094 m)). Qed.
Lemma lem3104097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3104098 (m : nat) : (term158 m) = (term159 m).
Proof. exact (MK_COMB (@lem3104097) (@lem3104096 m)). Qed.
Lemma lem3104100 (m : nat) (n : nat) : (Peano.le m n) = (term154 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem3104101 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3104102 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (MK_COMB (@lem3104101) (@lem3104100 m n)). Qed.
Lemma lem3104103 (m : nat) (n : nat) : (term137 m n) = (term162 m n).
Proof. exact (MK_COMB (@lem3104098 m) (@lem3104102 m n)). Qed.
Lemma lem3104104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104105 (m : nat) (n : nat) : (term141 m n) = (term163 m n).
Proof. exact (MK_COMB (@lem3104104) (@lem3104103 m n)). Qed.
Lemma lem3104107 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3104108 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term164).
Proof. exact (@lem3104107 n (NUMERAL 0)). Qed.
Lemma lem3104111 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3104112 (n : nat) : (term139 n) = (term165 n).
Proof. exact (MK_COMB (@lem3104111) (@lem3104108 n)). Qed.
Lemma lem3104113 (m : nat) (n : nat) : (term143 m n) = (term166 m n).
Proof. exact (MK_COMB (@lem3104105 m n) (@lem3104112 n)). Qed.
Lemma lem3104114 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3104115 (m : nat) (n : nat) : (term147 m n) = (term167 m n).
Proof. exact (MK_COMB (@lem3104114) (@lem3104113 m n)). Qed.
Lemma lem3104117 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3104120 (m : nat) (n : nat) : (term149 m n) = (term168 m n).
Proof. exact (MK_COMB (@lem3104115 m n) (@lem3104117 m n)). Qed.
Lemma lem3104121 (m : nat) (n : nat) : (term152 m n) = (term169 m n).
Proof. exact (MK_COMB (@lem3104091 n m) (@lem3104120 m n)). Qed.
Lemma lem3104122 (m : nat) (n : nat) : (term153 m n) = (term169 m n).
Proof. exact (TRANS (@lem3104066 m n) (@lem3104121 m n)). Qed.
Lemma lem3104123 (m : nat) : term170 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem3104124 (m : nat) : (term170 m) = (term171 m).
Proof. exact (eq_refl (term170 m)). Qed.
Lemma lem3104125 (m : nat) : term171 m.
Proof. exact (EQ_MP (@lem3104124 m) (@lem3104123 m)). Qed.
Lemma lem3104126 (n : nat) : term170 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem3104127 (n : nat) : (term170 n) = (term171 n).
Proof. exact (eq_refl (term170 n)). Qed.
Lemma lem3104128 (n : nat) : term171 n.
Proof. exact (EQ_MP (@lem3104127 n) (@lem3104126 n)). Qed.
Lemma lem3104129 (_32231 : int) (_32232 : int) : (term172 _32231 _32232) = (term173 _32231 _32232).
Proof. exact (@lem2318604 (term173 _32231 _32232)). Qed.
Lemma lem3104155 (_32232 : int) : (term174 _32232) = (term175 _32232).
Proof. exact (@lem16933 (term175 _32232)). Qed.
Lemma lem3104158 (_32232 : int) (_32231 : int) : (term176 _32232 _32231) = (int_le _32232 _32231).
Proof. exact (@lem16933 (int_le _32232 _32231)). Qed.
Lemma lem3104159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104160 (_32232 : int) : (term177 _32232) = (term178 _32232).
Proof. exact (MK_COMB (@lem3104159) (@lem3104155 _32232)). Qed.
Lemma lem3104161 (_32232 : int) (_32231 : int) : (term179 _32232 _32231) = (term180 _32232 _32231).
Proof. exact (MK_COMB (@lem3104160 _32232) (@lem3104158 _32232 _32231)). Qed.
Lemma lem3104162 (_32232 : int) (_32231 : int) : (term181 _32232 _32231) = (term179 _32232 _32231).
Proof. exact (@lem17160 (term182 _32232) (term183 _32232 _32231)). Qed.
Lemma lem3104163 (_32232 : int) (_32231 : int) : (term181 _32232 _32231) = (term180 _32232 _32231).
Proof. exact (TRANS (@lem3104162 _32232 _32231) (@lem3104161 _32232 _32231)). Qed.
Lemma lem3104166 (_32231 : int) : (term184 _32231) = (_32231 = term164).
Proof. exact (@lem16933 (_32231 = term164)). Qed.
Lemma lem3104167 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3104168 (_32232 : int) (_32231 : int) : (term185 _32232 _32231) = (term186 _32232 _32231).
Proof. exact (MK_COMB (@lem3104167) (@lem3104163 _32232 _32231)). Qed.
Lemma lem3104169 (_32232 : int) (_32231 : int) : (term187 _32232 _32231) = (term188 _32232 _32231).
Proof. exact (MK_COMB (@lem3104168 _32232 _32231) (@lem3104166 _32231)). Qed.
Lemma lem3104170 (_32232 : int) (_32231 : int) : (term189 _32232 _32231) = (term187 _32232 _32231).
Proof. exact (@lem17045 (term190 _32232 _32231) (term191 _32231)). Qed.
Lemma lem3104171 (_32232 : int) (_32231 : int) : (term189 _32232 _32231) = (term188 _32232 _32231).
Proof. exact (TRANS (@lem3104170 _32232 _32231) (@lem3104169 _32232 _32231)). Qed.
Lemma lem3104174 (_32231 : int) : (term174 _32231) = (term175 _32231).
Proof. exact (@lem16933 (term175 _32231)). Qed.
Lemma lem3104177 (_32231 : int) (_32232 : int) : (term176 _32231 _32232) = (int_le _32231 _32232).
Proof. exact (@lem16933 (int_le _32231 _32232)). Qed.
Lemma lem3104178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104179 (_32231 : int) : (term177 _32231) = (term178 _32231).
Proof. exact (MK_COMB (@lem3104178) (@lem3104174 _32231)). Qed.
Lemma lem3104180 (_32231 : int) (_32232 : int) : (term179 _32231 _32232) = (term180 _32231 _32232).
Proof. exact (MK_COMB (@lem3104179 _32231) (@lem3104177 _32231 _32232)). Qed.
Lemma lem3104181 (_32231 : int) (_32232 : int) : (term181 _32231 _32232) = (term179 _32231 _32232).
Proof. exact (@lem17160 (term182 _32231) (term183 _32231 _32232)). Qed.
Lemma lem3104182 (_32231 : int) (_32232 : int) : (term181 _32231 _32232) = (term180 _32231 _32232).
Proof. exact (TRANS (@lem3104181 _32231 _32232) (@lem3104180 _32231 _32232)). Qed.
Lemma lem3104185 (_32232 : int) : (term184 _32232) = (_32232 = term164).
Proof. exact (@lem16933 (_32232 = term164)). Qed.
Lemma lem3104186 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3104187 (_32231 : int) (_32232 : int) : (term185 _32231 _32232) = (term186 _32231 _32232).
Proof. exact (MK_COMB (@lem3104186) (@lem3104182 _32231 _32232)). Qed.
Lemma lem3104188 (_32231 : int) (_32232 : int) : (term187 _32231 _32232) = (term188 _32231 _32232).
Proof. exact (MK_COMB (@lem3104187 _32231 _32232) (@lem3104185 _32232)). Qed.
Lemma lem3104189 (_32231 : int) (_32232 : int) : (term189 _32231 _32232) = (term187 _32231 _32232).
Proof. exact (@lem17045 (term190 _32231 _32232) (term191 _32232)). Qed.
Lemma lem3104190 (_32231 : int) (_32232 : int) : (term189 _32231 _32232) = (term188 _32231 _32232).
Proof. exact (TRANS (@lem3104189 _32231 _32232) (@lem3104188 _32231 _32232)). Qed.
Lemma lem3104191 (_32231 : int) (_32232 : int) : (term192 _32231 _32232) = (term192 _32231 _32232).
Proof. exact (eq_refl (term192 _32231 _32232)). Qed.
Lemma lem3104192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104193 (_32231 : int) (_32232 : int) : (term193 _32231 _32232) = (term194 _32231 _32232).
Proof. exact (MK_COMB (@lem3104192) (@lem3104190 _32231 _32232)). Qed.
Lemma lem3104194 (_32231 : int) (_32232 : int) : (term195 _32231 _32232) = (term196 _32231 _32232).
Proof. exact (MK_COMB (@lem3104193 _32231 _32232) (@lem3104191 _32231 _32232)). Qed.
Lemma lem3104195 (_32231 : int) (_32232 : int) : (term197 _32231 _32232) = (term195 _32231 _32232).
Proof. exact (@lem17160 (term198 _32231 _32232) (_32231 = _32232)). Qed.
Lemma lem3104196 (_32231 : int) (_32232 : int) : (term197 _32231 _32232) = (term196 _32231 _32232).
Proof. exact (TRANS (@lem3104195 _32231 _32232) (@lem3104194 _32231 _32232)). Qed.
Lemma lem3104197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104198 (_32232 : int) (_32231 : int) : (term193 _32232 _32231) = (term194 _32232 _32231).
Proof. exact (MK_COMB (@lem3104197) (@lem3104171 _32232 _32231)). Qed.
Lemma lem3104199 (_32231 : int) (_32232 : int) : (term199 _32231 _32232) = (term200 _32231 _32232).
Proof. exact (MK_COMB (@lem3104198 _32232 _32231) (@lem3104196 _32231 _32232)). Qed.
Lemma lem3104200 (_32231 : int) (_32232 : int) : (term201 _32231 _32232) = (term199 _32231 _32232).
Proof. exact (@lem17160 (term198 _32232 _32231) (term202 _32231 _32232)). Qed.
Lemma lem3104201 (_32231 : int) (_32232 : int) : (term201 _32231 _32232) = (term200 _32231 _32232).
Proof. exact (TRANS (@lem3104200 _32231 _32232) (@lem3104199 _32231 _32232)). Qed.
Lemma lem3104203 (_32232 : int) : (term203 _32232) = (term203 _32232).
Proof. exact (eq_refl (term203 _32232)). Qed.
Lemma lem3104204 (_32231 : int) (_32232 : int) : (term204 _32231 _32232) = (term205 _32231 _32232).
Proof. exact (MK_COMB (@lem3104203 _32232) (@lem3104201 _32231 _32232)). Qed.
Lemma lem3104205 (_32231 : int) (_32232 : int) : (term206 _32231 _32232) = (term204 _32231 _32232).
Proof. exact (@lem17362 (term207 _32232) (term208 _32231 _32232)). Qed.
Lemma lem3104206 (_32231 : int) (_32232 : int) : (term206 _32231 _32232) = (term205 _32231 _32232).
Proof. exact (TRANS (@lem3104205 _32231 _32232) (@lem3104204 _32231 _32232)). Qed.
Lemma lem3104208 (_32231 : int) : (term203 _32231) = (term203 _32231).
Proof. exact (eq_refl (term203 _32231)). Qed.
Lemma lem3104209 (_32231 : int) (_32232 : int) : (term209 _32231 _32232) = (term210 _32231 _32232).
Proof. exact (MK_COMB (@lem3104208 _32231) (@lem3104206 _32231 _32232)). Qed.
Lemma lem3104210 (_32231 : int) (_32232 : int) : (term211 _32231 _32232) = (term209 _32231 _32232).
Proof. exact (@lem17362 (term207 _32231) (term212 _32231 _32232)). Qed.
Lemma lem3104248 (_32231 : int) (_32232 : int) : (term211 _32231 _32232) = (term210 _32231 _32232).
Proof. exact (TRANS (@lem3104210 _32231 _32232) (@lem3104209 _32231 _32232)). Qed.
Lemma lem3104251 (x : int) (y : int) : (int_le x y) = (term213 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3104252 (_32231 : int) : (term207 _32231) = (term214 _32231).
Proof. exact (@lem3104251 term164 _32231). Qed.
Lemma lem3104254 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3104255 : term216 = term217.
Proof. exact (@lem3104254 (NUMERAL 0)). Qed.
Lemma lem3104256 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3104257 : term218 = term219.
Proof. exact (MK_COMB (@lem3104256) (@lem3104255)). Qed.
Lemma lem3104258 (_32231 : int) : (real_of_int _32231) = (real_of_int _32231).
Proof. exact (eq_refl (real_of_int _32231)). Qed.
Lemma lem3104259 (_32231 : int) : (term214 _32231) = (term220 _32231).
Proof. exact (MK_COMB (@lem3104257) (@lem3104258 _32231)). Qed.
Lemma lem3104261 (_32231 : int) : (term207 _32231) = (term220 _32231).
Proof. exact (TRANS (@lem3104252 _32231) (@lem3104259 _32231)). Qed.
Lemma lem3104264 (x : int) (y : int) : (int_le x y) = (term213 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3104265 (_32232 : int) : (term207 _32232) = (term214 _32232).
Proof. exact (@lem3104264 term164 _32232). Qed.
Lemma lem3104267 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3104268 : term216 = term217.
Proof. exact (@lem3104267 (NUMERAL 0)). Qed.
Lemma lem3104269 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3104270 : term218 = term219.
Proof. exact (MK_COMB (@lem3104269) (@lem3104268)). Qed.
Lemma lem3104271 (_32232 : int) : (real_of_int _32232) = (real_of_int _32232).
Proof. exact (eq_refl (real_of_int _32232)). Qed.
Lemma lem3104272 (_32232 : int) : (term214 _32232) = (term220 _32232).
Proof. exact (MK_COMB (@lem3104270) (@lem3104271 _32232)). Qed.
Lemma lem3104274 (_32232 : int) : (term207 _32232) = (term220 _32232).
Proof. exact (TRANS (@lem3104265 _32232) (@lem3104272 _32232)). Qed.
Lemma lem3104277 (x : int) (y : int) : (int_le x y) = (term213 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3104278 (_32232 : int) : (term175 _32232) = (term221 _32232).
Proof. exact (@lem3104277 term222 _32232). Qed.
Lemma lem3104280 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3104281 : term223 = term224.
Proof. exact (@lem3104280 term131). Qed.
Lemma lem3104282 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3104283 : term225 = term226.
Proof. exact (MK_COMB (@lem3104282) (@lem3104281)). Qed.
Lemma lem3104284 (_32232 : int) : (real_of_int _32232) = (real_of_int _32232).
Proof. exact (eq_refl (real_of_int _32232)). Qed.
Lemma lem3104285 (_32232 : int) : (term221 _32232) = (term227 _32232).
Proof. exact (MK_COMB (@lem3104283) (@lem3104284 _32232)). Qed.
Lemma lem3104287 (_32232 : int) : (term175 _32232) = (term227 _32232).
Proof. exact (TRANS (@lem3104278 _32232) (@lem3104285 _32232)). Qed.
Lemma lem3104290 (x : int) (y : int) : (int_le x y) = (term213 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3104292 (_32232 : int) (_32231 : int) : (int_le _32232 _32231) = (term213 _32232 _32231).
Proof. exact (@lem3104290 _32232 _32231). Qed.
Lemma lem3104293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104294 (_32232 : int) : (term178 _32232) = (term228 _32232).
Proof. exact (MK_COMB (@lem3104293) (@lem3104287 _32232)). Qed.
Lemma lem3104295 (_32232 : int) (_32231 : int) : (term180 _32232 _32231) = (term229 _32232 _32231).
Proof. exact (MK_COMB (@lem3104294 _32232) (@lem3104292 _32232 _32231)). Qed.
Lemma lem3104298 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3104299 (_32231 : int) : (_32231 = term164) = ((real_of_int _32231) = term216).
Proof. exact (@lem3104298 _32231 term164). Qed.
Lemma lem3104303 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3104304 : term216 = term217.
Proof. exact (@lem3104303 (NUMERAL 0)). Qed.
Lemma lem3104305 (_32231 : int) : (term230 _32231) = (term230 _32231).
Proof. exact (eq_refl (term230 _32231)). Qed.
Lemma lem3104306 (_32231 : int) : ((real_of_int _32231) = term216) = ((real_of_int _32231) = term217).
Proof. exact (MK_COMB (@lem3104305 _32231) (@lem3104304)). Qed.
Lemma lem3104308 (_32231 : int) : (_32231 = term164) = ((real_of_int _32231) = term217).
Proof. exact (TRANS (@lem3104299 _32231) (@lem3104306 _32231)). Qed.
Lemma lem3104309 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3104310 (_32232 : int) (_32231 : int) : (term186 _32232 _32231) = (term231 _32232 _32231).
Proof. exact (MK_COMB (@lem3104309) (@lem3104295 _32232 _32231)). Qed.
Lemma lem3104311 (_32232 : int) (_32231 : int) : (term188 _32232 _32231) = (term232 _32232 _32231).
Proof. exact (MK_COMB (@lem3104310 _32232 _32231) (@lem3104308 _32231)). Qed.
Lemma lem3104314 (x : int) (y : int) : (int_le x y) = (term213 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3104315 (_32231 : int) : (term175 _32231) = (term221 _32231).
Proof. exact (@lem3104314 term222 _32231). Qed.
Lemma lem3104317 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3104318 : term223 = term224.
Proof. exact (@lem3104317 term131). Qed.
Lemma lem3104319 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3104320 : term225 = term226.
Proof. exact (MK_COMB (@lem3104319) (@lem3104318)). Qed.
Lemma lem3104321 (_32231 : int) : (real_of_int _32231) = (real_of_int _32231).
Proof. exact (eq_refl (real_of_int _32231)). Qed.
Lemma lem3104322 (_32231 : int) : (term221 _32231) = (term227 _32231).
Proof. exact (MK_COMB (@lem3104320) (@lem3104321 _32231)). Qed.
Lemma lem3104324 (_32231 : int) : (term175 _32231) = (term227 _32231).
Proof. exact (TRANS (@lem3104315 _32231) (@lem3104322 _32231)). Qed.
Lemma lem3104327 (x : int) (y : int) : (int_le x y) = (term213 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3104329 (_32231 : int) (_32232 : int) : (int_le _32231 _32232) = (term213 _32231 _32232).
Proof. exact (@lem3104327 _32231 _32232). Qed.
Lemma lem3104330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104331 (_32231 : int) : (term178 _32231) = (term228 _32231).
Proof. exact (MK_COMB (@lem3104330) (@lem3104324 _32231)). Qed.
Lemma lem3104332 (_32231 : int) (_32232 : int) : (term180 _32231 _32232) = (term229 _32231 _32232).
Proof. exact (MK_COMB (@lem3104331 _32231) (@lem3104329 _32231 _32232)). Qed.
Lemma lem3104335 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3104336 (_32232 : int) : (_32232 = term164) = ((real_of_int _32232) = term216).
Proof. exact (@lem3104335 _32232 term164). Qed.
Lemma lem3104340 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3104341 : term216 = term217.
Proof. exact (@lem3104340 (NUMERAL 0)). Qed.
Lemma lem3104342 (_32232 : int) : (term230 _32232) = (term230 _32232).
Proof. exact (eq_refl (term230 _32232)). Qed.
Lemma lem3104343 (_32232 : int) : ((real_of_int _32232) = term216) = ((real_of_int _32232) = term217).
Proof. exact (MK_COMB (@lem3104342 _32232) (@lem3104341)). Qed.
Lemma lem3104345 (_32232 : int) : (_32232 = term164) = ((real_of_int _32232) = term217).
Proof. exact (TRANS (@lem3104336 _32232) (@lem3104343 _32232)). Qed.
Lemma lem3104346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3104347 (_32231 : int) (_32232 : int) : (term186 _32231 _32232) = (term231 _32231 _32232).
Proof. exact (MK_COMB (@lem3104346) (@lem3104332 _32231 _32232)). Qed.
Lemma lem3104348 (_32231 : int) (_32232 : int) : (term188 _32231 _32232) = (term232 _32231 _32232).
Proof. exact (MK_COMB (@lem3104347 _32231 _32232) (@lem3104345 _32232)). Qed.
Lemma lem3104350 (y : int) (x : int) : (term192 x y) = (term233 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem3104351 (_32232 : int) (_32231 : int) : (term192 _32231 _32232) = (term233 _32232 _32231).
Proof. exact (@lem3104350 _32232 _32231). Qed.
Lemma lem3104353 (x : int) (y : int) : (int_le x y) = (term213 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3104354 (_32231 : int) (_32232 : int) : (term234 _32231 _32232) = (term235 _32231 _32232).
Proof. exact (@lem3104353 (term236 _32231) _32232). Qed.
Lemma lem3104356 (x : int) (y : int) : (term237 x y) = (term238 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3104357 (_32231 : int) : (term239 _32231) = (term240 _32231).
Proof. exact (@lem3104356 _32231 term222). Qed.
Lemma lem3104359 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3104360 : term223 = term224.
Proof. exact (@lem3104359 term131). Qed.
Lemma lem3104361 (_32231 : int) : (term241 _32231) = (term241 _32231).
Proof. exact (eq_refl (term241 _32231)). Qed.
Lemma lem3104362 (_32231 : int) : (term240 _32231) = (term242 _32231).
Proof. exact (MK_COMB (@lem3104361 _32231) (@lem3104360)). Qed.
Lemma lem3104363 (_32231 : int) : (term239 _32231) = (term242 _32231).
Proof. exact (TRANS (@lem3104357 _32231) (@lem3104362 _32231)). Qed.
Lemma lem3104364 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3104365 (_32231 : int) : (term243 _32231) = (term244 _32231).
Proof. exact (MK_COMB (@lem3104364) (@lem3104363 _32231)). Qed.
Lemma lem3104366 (_32232 : int) : (real_of_int _32232) = (real_of_int _32232).
Proof. exact (eq_refl (real_of_int _32232)). Qed.
Lemma lem3104367 (_32231 : int) (_32232 : int) : (term235 _32231 _32232) = (term245 _32231 _32232).
Proof. exact (MK_COMB (@lem3104365 _32231) (@lem3104366 _32232)). Qed.
Lemma lem3104368 (_32231 : int) (_32232 : int) : (term234 _32231 _32232) = (term245 _32231 _32232).
Proof. exact (TRANS (@lem3104354 _32231 _32232) (@lem3104367 _32231 _32232)). Qed.
Lemma lem3104369 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3104370 (_32231 : int) (_32232 : int) : (term246 _32231 _32232) = (term247 _32231 _32232).
Proof. exact (MK_COMB (@lem3104369) (@lem3104368 _32231 _32232)). Qed.
Lemma lem3104372 (x : int) (y : int) : (int_le x y) = (term213 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3104373 (_32232 : int) (_32231 : int) : (term234 _32232 _32231) = (term235 _32232 _32231).
Proof. exact (@lem3104372 (term236 _32232) _32231). Qed.
Lemma lem3104375 (x : int) (y : int) : (term237 x y) = (term238 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3104376 (_32232 : int) : (term239 _32232) = (term240 _32232).
Proof. exact (@lem3104375 _32232 term222). Qed.
Lemma lem3104378 (n : nat) : (term215 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3104379 : term223 = term224.
Proof. exact (@lem3104378 term131). Qed.
Lemma lem3104380 (_32232 : int) : (term241 _32232) = (term241 _32232).
Proof. exact (eq_refl (term241 _32232)). Qed.
Lemma lem3104381 (_32232 : int) : (term240 _32232) = (term242 _32232).
Proof. exact (MK_COMB (@lem3104380 _32232) (@lem3104379)). Qed.
Lemma lem3104382 (_32232 : int) : (term239 _32232) = (term242 _32232).
Proof. exact (TRANS (@lem3104376 _32232) (@lem3104381 _32232)). Qed.
Lemma lem3104383 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3104384 (_32232 : int) : (term243 _32232) = (term244 _32232).
Proof. exact (MK_COMB (@lem3104383) (@lem3104382 _32232)). Qed.
Lemma lem3104385 (_32231 : int) : (real_of_int _32231) = (real_of_int _32231).
Proof. exact (eq_refl (real_of_int _32231)). Qed.
Lemma lem3104386 (_32232 : int) (_32231 : int) : (term235 _32232 _32231) = (term245 _32232 _32231).
Proof. exact (MK_COMB (@lem3104384 _32232) (@lem3104385 _32231)). Qed.
Lemma lem3104387 (_32232 : int) (_32231 : int) : (term234 _32232 _32231) = (term245 _32232 _32231).
Proof. exact (TRANS (@lem3104373 _32232 _32231) (@lem3104386 _32232 _32231)). Qed.
Lemma lem3104388 (_32232 : int) (_32231 : int) : (term233 _32232 _32231) = (term248 _32232 _32231).
Proof. exact (MK_COMB (@lem3104370 _32231 _32232) (@lem3104387 _32232 _32231)). Qed.
Lemma lem3104389 (_32232 : int) (_32231 : int) : (term192 _32231 _32232) = (term248 _32232 _32231).
Proof. exact (TRANS (@lem3104351 _32232 _32231) (@lem3104388 _32232 _32231)). Qed.
Lemma lem3104390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104391 (_32231 : int) (_32232 : int) : (term194 _32231 _32232) = (term249 _32231 _32232).
Proof. exact (MK_COMB (@lem3104390) (@lem3104348 _32231 _32232)). Qed.
Lemma lem3104392 (_32232 : int) (_32231 : int) : (term196 _32231 _32232) = (term250 _32232 _32231).
Proof. exact (MK_COMB (@lem3104391 _32231 _32232) (@lem3104389 _32232 _32231)). Qed.
Lemma lem3104393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104394 (_32232 : int) (_32231 : int) : (term194 _32232 _32231) = (term249 _32232 _32231).
Proof. exact (MK_COMB (@lem3104393) (@lem3104311 _32232 _32231)). Qed.
Lemma lem3104395 (_32232 : int) (_32231 : int) : (term200 _32231 _32232) = (term251 _32232 _32231).
Proof. exact (MK_COMB (@lem3104394 _32232 _32231) (@lem3104392 _32232 _32231)). Qed.
Lemma lem3104396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104397 (_32232 : int) : (term203 _32232) = (term252 _32232).
Proof. exact (MK_COMB (@lem3104396) (@lem3104274 _32232)). Qed.
Lemma lem3104398 (_32232 : int) (_32231 : int) : (term205 _32231 _32232) = (term253 _32232 _32231).
Proof. exact (MK_COMB (@lem3104397 _32232) (@lem3104395 _32232 _32231)). Qed.
Lemma lem3104399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104400 (_32231 : int) : (term203 _32231) = (term252 _32231).
Proof. exact (MK_COMB (@lem3104399) (@lem3104261 _32231)). Qed.
Lemma lem3104401 (_32232 : int) (_32231 : int) : (term210 _32231 _32232) = (term254 _32232 _32231).
Proof. exact (MK_COMB (@lem3104400 _32231) (@lem3104398 _32232 _32231)). Qed.
Lemma lem3104402 (_32232 : int) (_32231 : int) : (term211 _32231 _32232) = (term254 _32232 _32231).
Proof. exact (TRANS (@lem3104248 _32231 _32232) (@lem3104401 _32232 _32231)). Qed.
Lemma lem3104406 (t : Prop) : (term118 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3104502 (_32232 : int) (_32231 : int) : (term255 _32232 _32231) = (term254 _32232 _32231).
Proof. exact (@lem3104406 (term254 _32232 _32231)). Qed.
Lemma lem3104503 (_32231 : int) : (term220 _32231) = (term256 _32231).
Proof. exact (@lem1988287 (real_of_int _32231) term217). Qed.
Lemma lem3104509 (_32231 : int) : (term257 _32231) = (term258 _32231).
Proof. exact (@lem1982792 (real_of_int _32231) term217). Qed.
Lemma lem3104511 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3104512 : term217 = term260.
Proof. exact (@lem3104511 (NUMERAL 0)). Qed.
Lemma lem3104514 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3104515 : term263 = term264.
Proof. exact (@lem3104514 term131). Qed.
Lemma lem3104516 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3104517 : term265 = term266.
Proof. exact (MK_COMB (@lem3104516) (@lem3104515)). Qed.
Lemma lem3104518 : term267 = term268.
Proof. exact (MK_COMB (@lem3104517) (@lem3104512)). Qed.
Lemma lem3104519 : term268 = term269.
Proof. exact (@lem1981613 term263 term217 term224 term224). Qed.
Lemma lem3104521 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3104522 : term272 = term273.
Proof. exact (@lem3104521 term131 term131). Qed.
Lemma lem3104523 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3104524 : term275 = term131.
Proof. exact (EQ_MP (@lem3104523) (@lem940073)). Qed.
Lemma lem3104525 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3104526 : term273 = term224.
Proof. exact (MK_COMB (@lem3104525) (@lem3104524)). Qed.
Lemma lem3104527 : term272 = term224.
Proof. exact (TRANS (@lem3104522) (@lem3104526)). Qed.
Lemma lem3104529 (x : nat) : (term276 x) = term217.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3104530 : term267 = term217.
Proof. exact (@lem3104529 term131). Qed.
Lemma lem3104531 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3104532 : term277 = term278.
Proof. exact (MK_COMB (@lem3104531) (@lem3104530)). Qed.
Lemma lem3104533 : term269 = term260.
Proof. exact (MK_COMB (@lem3104532) (@lem3104527)). Qed.
Lemma lem3104534 : term268 = term260.
Proof. exact (TRANS (@lem3104519) (@lem3104533)). Qed.
Lemma lem3104535 : term267 = term260.
Proof. exact (TRANS (@lem3104518) (@lem3104534)). Qed.
Lemma lem3104537 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3104538 : term260 = term217.
Proof. exact (@lem3104537 term217). Qed.
Lemma lem3104539 : term267 = term217.
Proof. exact (TRANS (@lem3104535) (@lem3104538)). Qed.
Lemma lem3104540 (_32231 : int) : (term241 _32231) = (term241 _32231).
Proof. exact (eq_refl (term241 _32231)). Qed.
Lemma lem3104541 (_32231 : int) : (term258 _32231) = (term280 _32231).
Proof. exact (MK_COMB (@lem3104540 _32231) (@lem3104539)). Qed.
Lemma lem3104542 (_32231 : int) : (term280 _32231) = (real_of_int _32231).
Proof. exact (@lem1982723 (real_of_int _32231)). Qed.
Lemma lem3104543 (_32231 : int) : (term258 _32231) = (real_of_int _32231).
Proof. exact (TRANS (@lem3104541 _32231) (@lem3104542 _32231)). Qed.
Lemma lem3104545 (_32231 : int) : (term257 _32231) = (real_of_int _32231).
Proof. exact (TRANS (@lem3104509 _32231) (@lem3104543 _32231)). Qed.
Lemma lem3104546 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3104547 (_32231 : int) : (term281 _32231) = (term282 _32231).
Proof. exact (MK_COMB (@lem3104546) (@lem3104545 _32231)). Qed.
Lemma lem3104548 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3104549 (_32231 : int) : (term256 _32231) = (term283 _32231).
Proof. exact (MK_COMB (@lem3104547 _32231) (@lem3104548)). Qed.
Lemma lem3104550 (_32231 : int) : (term220 _32231) = (term283 _32231).
Proof. exact (TRANS (@lem3104503 _32231) (@lem3104549 _32231)). Qed.
Lemma lem3104551 (_32232 : int) : (term220 _32232) = (term256 _32232).
Proof. exact (@lem1988287 (real_of_int _32232) term217). Qed.
Lemma lem3104557 (_32232 : int) : (term257 _32232) = (term258 _32232).
Proof. exact (@lem1982792 (real_of_int _32232) term217). Qed.
Lemma lem3104559 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3104560 : term217 = term260.
Proof. exact (@lem3104559 (NUMERAL 0)). Qed.
Lemma lem3104562 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3104563 : term263 = term264.
Proof. exact (@lem3104562 term131). Qed.
Lemma lem3104564 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3104565 : term265 = term266.
Proof. exact (MK_COMB (@lem3104564) (@lem3104563)). Qed.
Lemma lem3104566 : term267 = term268.
Proof. exact (MK_COMB (@lem3104565) (@lem3104560)). Qed.
Lemma lem3104567 : term268 = term269.
Proof. exact (@lem1981613 term263 term217 term224 term224). Qed.
Lemma lem3104569 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3104570 : term272 = term273.
Proof. exact (@lem3104569 term131 term131). Qed.
Lemma lem3104571 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3104572 : term275 = term131.
Proof. exact (EQ_MP (@lem3104571) (@lem940073)). Qed.
Lemma lem3104573 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3104574 : term273 = term224.
Proof. exact (MK_COMB (@lem3104573) (@lem3104572)). Qed.
Lemma lem3104575 : term272 = term224.
Proof. exact (TRANS (@lem3104570) (@lem3104574)). Qed.
Lemma lem3104577 (x : nat) : (term276 x) = term217.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3104578 : term267 = term217.
Proof. exact (@lem3104577 term131). Qed.
Lemma lem3104579 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3104580 : term277 = term278.
Proof. exact (MK_COMB (@lem3104579) (@lem3104578)). Qed.
Lemma lem3104581 : term269 = term260.
Proof. exact (MK_COMB (@lem3104580) (@lem3104575)). Qed.
Lemma lem3104582 : term268 = term260.
Proof. exact (TRANS (@lem3104567) (@lem3104581)). Qed.
Lemma lem3104583 : term267 = term260.
Proof. exact (TRANS (@lem3104566) (@lem3104582)). Qed.
Lemma lem3104585 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3104586 : term260 = term217.
Proof. exact (@lem3104585 term217). Qed.
Lemma lem3104587 : term267 = term217.
Proof. exact (TRANS (@lem3104583) (@lem3104586)). Qed.
Lemma lem3104588 (_32232 : int) : (term241 _32232) = (term241 _32232).
Proof. exact (eq_refl (term241 _32232)). Qed.
Lemma lem3104589 (_32232 : int) : (term258 _32232) = (term280 _32232).
Proof. exact (MK_COMB (@lem3104588 _32232) (@lem3104587)). Qed.
Lemma lem3104590 (_32232 : int) : (term280 _32232) = (real_of_int _32232).
Proof. exact (@lem1982723 (real_of_int _32232)). Qed.
Lemma lem3104591 (_32232 : int) : (term258 _32232) = (real_of_int _32232).
Proof. exact (TRANS (@lem3104589 _32232) (@lem3104590 _32232)). Qed.
Lemma lem3104593 (_32232 : int) : (term257 _32232) = (real_of_int _32232).
Proof. exact (TRANS (@lem3104557 _32232) (@lem3104591 _32232)). Qed.
Lemma lem3104594 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3104595 (_32232 : int) : (term281 _32232) = (term282 _32232).
Proof. exact (MK_COMB (@lem3104594) (@lem3104593 _32232)). Qed.
Lemma lem3104596 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3104597 (_32232 : int) : (term256 _32232) = (term283 _32232).
Proof. exact (MK_COMB (@lem3104595 _32232) (@lem3104596)). Qed.
Lemma lem3104598 (_32232 : int) : (term220 _32232) = (term283 _32232).
Proof. exact (TRANS (@lem3104551 _32232) (@lem3104597 _32232)). Qed.
Lemma lem3104599 (_32232 : int) : (term227 _32232) = (term284 _32232).
Proof. exact (@lem1988287 (real_of_int _32232) term224). Qed.
Lemma lem3104605 (_32232 : int) : (term285 _32232) = (term286 _32232).
Proof. exact (@lem1982792 (real_of_int _32232) term224). Qed.
Lemma lem3104607 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3104608 : term224 = term287.
Proof. exact (@lem3104607 term131). Qed.
Lemma lem3104610 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3104611 : term263 = term264.
Proof. exact (@lem3104610 term131). Qed.
Lemma lem3104612 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3104613 : term265 = term266.
Proof. exact (MK_COMB (@lem3104612) (@lem3104611)). Qed.
Lemma lem3104614 : term288 = term289.
Proof. exact (MK_COMB (@lem3104613) (@lem3104608)). Qed.
Lemma lem3104615 : term289 = term290.
Proof. exact (@lem1981613 term263 term224 term224 term224). Qed.
Lemma lem3104617 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3104618 : term272 = term273.
Proof. exact (@lem3104617 term131 term131). Qed.
Lemma lem3104619 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3104620 : term275 = term131.
Proof. exact (EQ_MP (@lem3104619) (@lem940073)). Qed.
Lemma lem3104621 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3104622 : term273 = term224.
Proof. exact (MK_COMB (@lem3104621) (@lem3104620)). Qed.
Lemma lem3104623 : term272 = term224.
Proof. exact (TRANS (@lem3104618) (@lem3104622)). Qed.
Lemma lem3104625 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3104626 : term288 = term293.
Proof. exact (@lem3104625 term131 term131). Qed.
Lemma lem3104627 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3104628 : term275 = term131.
Proof. exact (EQ_MP (@lem3104627) (@lem940073)). Qed.
Lemma lem3104629 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3104630 : term273 = term224.
Proof. exact (MK_COMB (@lem3104629) (@lem3104628)). Qed.
Lemma lem3104631 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3104632 : term293 = term263.
Proof. exact (MK_COMB (@lem3104631) (@lem3104630)). Qed.
Lemma lem3104633 : term288 = term263.
Proof. exact (TRANS (@lem3104626) (@lem3104632)). Qed.
Lemma lem3104634 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3104635 : term294 = term295.
Proof. exact (MK_COMB (@lem3104634) (@lem3104633)). Qed.
Lemma lem3104636 : term290 = term264.
Proof. exact (MK_COMB (@lem3104635) (@lem3104623)). Qed.
Lemma lem3104637 : term289 = term264.
Proof. exact (TRANS (@lem3104615) (@lem3104636)). Qed.
Lemma lem3104638 : term288 = term264.
Proof. exact (TRANS (@lem3104614) (@lem3104637)). Qed.
Lemma lem3104640 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3104641 : term264 = term263.
Proof. exact (@lem3104640 term263). Qed.
Lemma lem3104642 : term288 = term263.
Proof. exact (TRANS (@lem3104638) (@lem3104641)). Qed.
Lemma lem3104643 (_32232 : int) : (term241 _32232) = (term241 _32232).
Proof. exact (eq_refl (term241 _32232)). Qed.
Lemma lem3104646 (_32232 : int) : (term286 _32232) = (term296 _32232).
Proof. exact (MK_COMB (@lem3104643 _32232) (@lem3104642)). Qed.
Lemma lem3104648 (_32232 : int) : (term285 _32232) = (term296 _32232).
Proof. exact (TRANS (@lem3104605 _32232) (@lem3104646 _32232)). Qed.
Lemma lem3104649 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3104650 (_32232 : int) : (term297 _32232) = (term298 _32232).
Proof. exact (MK_COMB (@lem3104649) (@lem3104648 _32232)). Qed.
Lemma lem3104651 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3104652 (_32232 : int) : (term284 _32232) = (term299 _32232).
Proof. exact (MK_COMB (@lem3104650 _32232) (@lem3104651)). Qed.
Lemma lem3104653 (_32232 : int) : (term227 _32232) = (term299 _32232).
Proof. exact (TRANS (@lem3104599 _32232) (@lem3104652 _32232)). Qed.
Lemma lem3104654 (_32231 : int) (_32232 : int) : (term213 _32232 _32231) = (term300 _32231 _32232).
Proof. exact (@lem1988287 (real_of_int _32231) (real_of_int _32232)). Qed.
Lemma lem3104667 (_32231 : int) (_32232 : int) : (term301 _32231 _32232) = (term302 _32231 _32232).
Proof. exact (@lem1982792 (real_of_int _32231) (real_of_int _32232)). Qed.
Lemma lem3104668 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3104669 (_32231 : int) (_32232 : int) : (term303 _32231 _32232) = (term304 _32231 _32232).
Proof. exact (MK_COMB (@lem3104668) (@lem3104667 _32231 _32232)). Qed.
Lemma lem3104670 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3104671 (_32231 : int) (_32232 : int) : (term300 _32231 _32232) = (term305 _32231 _32232).
Proof. exact (MK_COMB (@lem3104669 _32231 _32232) (@lem3104670)). Qed.
Lemma lem3104672 (_32231 : int) (_32232 : int) : (term213 _32232 _32231) = (term305 _32231 _32232).
Proof. exact (TRANS (@lem3104654 _32231 _32232) (@lem3104671 _32231 _32232)). Qed.
Lemma lem3104673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104674 (_32232 : int) : (term228 _32232) = (term306 _32232).
Proof. exact (MK_COMB (@lem3104673) (@lem3104653 _32232)). Qed.
Lemma lem3104675 (_32231 : int) (_32232 : int) : (term229 _32232 _32231) = (term307 _32231 _32232).
Proof. exact (MK_COMB (@lem3104674 _32232) (@lem3104672 _32231 _32232)). Qed.
Lemma lem3104676 (_32231 : int) : ((real_of_int _32231) = term217) = ((term257 _32231) = term217).
Proof. exact (@lem1988293 (real_of_int _32231) term217). Qed.
Lemma lem3104682 (_32231 : int) : (term257 _32231) = (term258 _32231).
Proof. exact (@lem1982792 (real_of_int _32231) term217). Qed.
Lemma lem3104684 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3104685 : term217 = term260.
Proof. exact (@lem3104684 (NUMERAL 0)). Qed.
Lemma lem3104687 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3104688 : term263 = term264.
Proof. exact (@lem3104687 term131). Qed.
Lemma lem3104689 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3104690 : term265 = term266.
Proof. exact (MK_COMB (@lem3104689) (@lem3104688)). Qed.
Lemma lem3104691 : term267 = term268.
Proof. exact (MK_COMB (@lem3104690) (@lem3104685)). Qed.
Lemma lem3104692 : term268 = term269.
Proof. exact (@lem1981613 term263 term217 term224 term224). Qed.
Lemma lem3104694 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3104695 : term272 = term273.
Proof. exact (@lem3104694 term131 term131). Qed.
Lemma lem3104696 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3104697 : term275 = term131.
Proof. exact (EQ_MP (@lem3104696) (@lem940073)). Qed.
Lemma lem3104698 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3104699 : term273 = term224.
Proof. exact (MK_COMB (@lem3104698) (@lem3104697)). Qed.
Lemma lem3104700 : term272 = term224.
Proof. exact (TRANS (@lem3104695) (@lem3104699)). Qed.
Lemma lem3104702 (x : nat) : (term276 x) = term217.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3104703 : term267 = term217.
Proof. exact (@lem3104702 term131). Qed.
Lemma lem3104704 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3104705 : term277 = term278.
Proof. exact (MK_COMB (@lem3104704) (@lem3104703)). Qed.
Lemma lem3104706 : term269 = term260.
Proof. exact (MK_COMB (@lem3104705) (@lem3104700)). Qed.
Lemma lem3104707 : term268 = term260.
Proof. exact (TRANS (@lem3104692) (@lem3104706)). Qed.
Lemma lem3104708 : term267 = term260.
Proof. exact (TRANS (@lem3104691) (@lem3104707)). Qed.
Lemma lem3104710 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3104711 : term260 = term217.
Proof. exact (@lem3104710 term217). Qed.
Lemma lem3104712 : term267 = term217.
Proof. exact (TRANS (@lem3104708) (@lem3104711)). Qed.
Lemma lem3104713 (_32231 : int) : (term241 _32231) = (term241 _32231).
Proof. exact (eq_refl (term241 _32231)). Qed.
Lemma lem3104714 (_32231 : int) : (term258 _32231) = (term280 _32231).
Proof. exact (MK_COMB (@lem3104713 _32231) (@lem3104712)). Qed.
Lemma lem3104715 (_32231 : int) : (term280 _32231) = (real_of_int _32231).
Proof. exact (@lem1982723 (real_of_int _32231)). Qed.
Lemma lem3104716 (_32231 : int) : (term258 _32231) = (real_of_int _32231).
Proof. exact (TRANS (@lem3104714 _32231) (@lem3104715 _32231)). Qed.
Lemma lem3104718 (_32231 : int) : (term257 _32231) = (real_of_int _32231).
Proof. exact (TRANS (@lem3104682 _32231) (@lem3104716 _32231)). Qed.
Lemma lem3104719 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3104720 (_32231 : int) : (term308 _32231) = (term230 _32231).
Proof. exact (MK_COMB (@lem3104719) (@lem3104718 _32231)). Qed.
Lemma lem3104721 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3104722 (_32231 : int) : ((term257 _32231) = term217) = ((real_of_int _32231) = term217).
Proof. exact (MK_COMB (@lem3104720 _32231) (@lem3104721)). Qed.
Lemma lem3104723 (_32231 : int) : ((real_of_int _32231) = term217) = ((real_of_int _32231) = term217).
Proof. exact (TRANS (@lem3104676 _32231) (@lem3104722 _32231)). Qed.
Lemma lem3104724 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3104725 (_32231 : int) (_32232 : int) : (term231 _32232 _32231) = (term309 _32231 _32232).
Proof. exact (MK_COMB (@lem3104724) (@lem3104675 _32231 _32232)). Qed.
Lemma lem3104726 (_32232 : int) (_32231 : int) : (term232 _32232 _32231) = (term310 _32232 _32231).
Proof. exact (MK_COMB (@lem3104725 _32231 _32232) (@lem3104723 _32231)). Qed.
Lemma lem3104727 (_32231 : int) : (term227 _32231) = (term284 _32231).
Proof. exact (@lem1988287 (real_of_int _32231) term224). Qed.
Lemma lem3104733 (_32231 : int) : (term285 _32231) = (term286 _32231).
Proof. exact (@lem1982792 (real_of_int _32231) term224). Qed.
Lemma lem3104735 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3104736 : term224 = term287.
Proof. exact (@lem3104735 term131). Qed.
Lemma lem3104738 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3104739 : term263 = term264.
Proof. exact (@lem3104738 term131). Qed.
Lemma lem3104740 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3104741 : term265 = term266.
Proof. exact (MK_COMB (@lem3104740) (@lem3104739)). Qed.
Lemma lem3104742 : term288 = term289.
Proof. exact (MK_COMB (@lem3104741) (@lem3104736)). Qed.
Lemma lem3104743 : term289 = term290.
Proof. exact (@lem1981613 term263 term224 term224 term224). Qed.
Lemma lem3104745 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3104746 : term272 = term273.
Proof. exact (@lem3104745 term131 term131). Qed.
Lemma lem3104747 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3104748 : term275 = term131.
Proof. exact (EQ_MP (@lem3104747) (@lem940073)). Qed.
Lemma lem3104749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3104750 : term273 = term224.
Proof. exact (MK_COMB (@lem3104749) (@lem3104748)). Qed.
Lemma lem3104751 : term272 = term224.
Proof. exact (TRANS (@lem3104746) (@lem3104750)). Qed.
Lemma lem3104753 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3104754 : term288 = term293.
Proof. exact (@lem3104753 term131 term131). Qed.
Lemma lem3104755 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3104756 : term275 = term131.
Proof. exact (EQ_MP (@lem3104755) (@lem940073)). Qed.
Lemma lem3104757 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3104758 : term273 = term224.
Proof. exact (MK_COMB (@lem3104757) (@lem3104756)). Qed.
Lemma lem3104759 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3104760 : term293 = term263.
Proof. exact (MK_COMB (@lem3104759) (@lem3104758)). Qed.
Lemma lem3104761 : term288 = term263.
Proof. exact (TRANS (@lem3104754) (@lem3104760)). Qed.
Lemma lem3104762 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3104763 : term294 = term295.
Proof. exact (MK_COMB (@lem3104762) (@lem3104761)). Qed.
Lemma lem3104764 : term290 = term264.
Proof. exact (MK_COMB (@lem3104763) (@lem3104751)). Qed.
Lemma lem3104765 : term289 = term264.
Proof. exact (TRANS (@lem3104743) (@lem3104764)). Qed.
Lemma lem3104766 : term288 = term264.
Proof. exact (TRANS (@lem3104742) (@lem3104765)). Qed.
Lemma lem3104768 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3104769 : term264 = term263.
Proof. exact (@lem3104768 term263). Qed.
Lemma lem3104770 : term288 = term263.
Proof. exact (TRANS (@lem3104766) (@lem3104769)). Qed.
Lemma lem3104771 (_32231 : int) : (term241 _32231) = (term241 _32231).
Proof. exact (eq_refl (term241 _32231)). Qed.
Lemma lem3104774 (_32231 : int) : (term286 _32231) = (term296 _32231).
Proof. exact (MK_COMB (@lem3104771 _32231) (@lem3104770)). Qed.
Lemma lem3104776 (_32231 : int) : (term285 _32231) = (term296 _32231).
Proof. exact (TRANS (@lem3104733 _32231) (@lem3104774 _32231)). Qed.
Lemma lem3104777 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3104778 (_32231 : int) : (term297 _32231) = (term298 _32231).
Proof. exact (MK_COMB (@lem3104777) (@lem3104776 _32231)). Qed.
Lemma lem3104779 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3104780 (_32231 : int) : (term284 _32231) = (term299 _32231).
Proof. exact (MK_COMB (@lem3104778 _32231) (@lem3104779)). Qed.
Lemma lem3104781 (_32231 : int) : (term227 _32231) = (term299 _32231).
Proof. exact (TRANS (@lem3104727 _32231) (@lem3104780 _32231)). Qed.
Lemma lem3104782 (_32232 : int) (_32231 : int) : (term213 _32231 _32232) = (term300 _32232 _32231).
Proof. exact (@lem1988287 (real_of_int _32232) (real_of_int _32231)). Qed.
Lemma lem3104788 (_32232 : int) (_32231 : int) : (term301 _32232 _32231) = (term302 _32232 _32231).
Proof. exact (@lem1982792 (real_of_int _32232) (real_of_int _32231)). Qed.
Lemma lem3104793 (_32231 : int) (_32232 : int) : (term302 _32232 _32231) = (term311 _32231 _32232).
Proof. exact (@lem1982761 (term312 _32231) (real_of_int _32232)). Qed.
Lemma lem3104795 (_32231 : int) (_32232 : int) : (term301 _32232 _32231) = (term311 _32231 _32232).
Proof. exact (TRANS (@lem3104788 _32232 _32231) (@lem3104793 _32231 _32232)). Qed.
Lemma lem3104796 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3104797 (_32231 : int) (_32232 : int) : (term303 _32232 _32231) = (term313 _32231 _32232).
Proof. exact (MK_COMB (@lem3104796) (@lem3104795 _32231 _32232)). Qed.
Lemma lem3104798 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3104799 (_32231 : int) (_32232 : int) : (term300 _32232 _32231) = (term314 _32231 _32232).
Proof. exact (MK_COMB (@lem3104797 _32231 _32232) (@lem3104798)). Qed.
Lemma lem3104800 (_32231 : int) (_32232 : int) : (term213 _32231 _32232) = (term314 _32231 _32232).
Proof. exact (TRANS (@lem3104782 _32232 _32231) (@lem3104799 _32231 _32232)). Qed.
Lemma lem3104801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104802 (_32231 : int) : (term228 _32231) = (term306 _32231).
Proof. exact (MK_COMB (@lem3104801) (@lem3104781 _32231)). Qed.
Lemma lem3104803 (_32231 : int) (_32232 : int) : (term229 _32231 _32232) = (term315 _32231 _32232).
Proof. exact (MK_COMB (@lem3104802 _32231) (@lem3104800 _32231 _32232)). Qed.
Lemma lem3104804 (_32232 : int) : ((real_of_int _32232) = term217) = ((term257 _32232) = term217).
Proof. exact (@lem1988293 (real_of_int _32232) term217). Qed.
Lemma lem3104810 (_32232 : int) : (term257 _32232) = (term258 _32232).
Proof. exact (@lem1982792 (real_of_int _32232) term217). Qed.
Lemma lem3104812 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3104813 : term217 = term260.
Proof. exact (@lem3104812 (NUMERAL 0)). Qed.
Lemma lem3104815 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3104816 : term263 = term264.
Proof. exact (@lem3104815 term131). Qed.
Lemma lem3104817 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3104818 : term265 = term266.
Proof. exact (MK_COMB (@lem3104817) (@lem3104816)). Qed.
Lemma lem3104819 : term267 = term268.
Proof. exact (MK_COMB (@lem3104818) (@lem3104813)). Qed.
Lemma lem3104820 : term268 = term269.
Proof. exact (@lem1981613 term263 term217 term224 term224). Qed.
Lemma lem3104822 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3104823 : term272 = term273.
Proof. exact (@lem3104822 term131 term131). Qed.
Lemma lem3104824 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3104825 : term275 = term131.
Proof. exact (EQ_MP (@lem3104824) (@lem940073)). Qed.
Lemma lem3104826 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3104827 : term273 = term224.
Proof. exact (MK_COMB (@lem3104826) (@lem3104825)). Qed.
Lemma lem3104828 : term272 = term224.
Proof. exact (TRANS (@lem3104823) (@lem3104827)). Qed.
Lemma lem3104830 (x : nat) : (term276 x) = term217.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3104831 : term267 = term217.
Proof. exact (@lem3104830 term131). Qed.
Lemma lem3104832 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3104833 : term277 = term278.
Proof. exact (MK_COMB (@lem3104832) (@lem3104831)). Qed.
Lemma lem3104834 : term269 = term260.
Proof. exact (MK_COMB (@lem3104833) (@lem3104828)). Qed.
Lemma lem3104835 : term268 = term260.
Proof. exact (TRANS (@lem3104820) (@lem3104834)). Qed.
Lemma lem3104836 : term267 = term260.
Proof. exact (TRANS (@lem3104819) (@lem3104835)). Qed.
Lemma lem3104838 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3104839 : term260 = term217.
Proof. exact (@lem3104838 term217). Qed.
Lemma lem3104840 : term267 = term217.
Proof. exact (TRANS (@lem3104836) (@lem3104839)). Qed.
Lemma lem3104841 (_32232 : int) : (term241 _32232) = (term241 _32232).
Proof. exact (eq_refl (term241 _32232)). Qed.
Lemma lem3104842 (_32232 : int) : (term258 _32232) = (term280 _32232).
Proof. exact (MK_COMB (@lem3104841 _32232) (@lem3104840)). Qed.
Lemma lem3104843 (_32232 : int) : (term280 _32232) = (real_of_int _32232).
Proof. exact (@lem1982723 (real_of_int _32232)). Qed.
Lemma lem3104844 (_32232 : int) : (term258 _32232) = (real_of_int _32232).
Proof. exact (TRANS (@lem3104842 _32232) (@lem3104843 _32232)). Qed.
Lemma lem3104846 (_32232 : int) : (term257 _32232) = (real_of_int _32232).
Proof. exact (TRANS (@lem3104810 _32232) (@lem3104844 _32232)). Qed.
Lemma lem3104847 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3104848 (_32232 : int) : (term308 _32232) = (term230 _32232).
Proof. exact (MK_COMB (@lem3104847) (@lem3104846 _32232)). Qed.
Lemma lem3104849 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3104850 (_32232 : int) : ((term257 _32232) = term217) = ((real_of_int _32232) = term217).
Proof. exact (MK_COMB (@lem3104848 _32232) (@lem3104849)). Qed.
Lemma lem3104851 (_32232 : int) : ((real_of_int _32232) = term217) = ((real_of_int _32232) = term217).
Proof. exact (TRANS (@lem3104804 _32232) (@lem3104850 _32232)). Qed.
Lemma lem3104852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3104853 (_32231 : int) (_32232 : int) : (term231 _32231 _32232) = (term316 _32231 _32232).
Proof. exact (MK_COMB (@lem3104852) (@lem3104803 _32231 _32232)). Qed.
Lemma lem3104854 (_32231 : int) (_32232 : int) : (term232 _32231 _32232) = (term317 _32231 _32232).
Proof. exact (MK_COMB (@lem3104853 _32231 _32232) (@lem3104851 _32232)). Qed.
Lemma lem3104855 (_32232 : int) (_32231 : int) : (term245 _32231 _32232) = (term318 _32232 _32231).
Proof. exact (@lem1988287 (real_of_int _32232) (term242 _32231)). Qed.
Lemma lem3104867 (_32232 : int) (_32231 : int) : (term319 _32232 _32231) = (term320 _32232 _32231).
Proof. exact (@lem1982792 (real_of_int _32232) (term242 _32231)). Qed.
Lemma lem3104868 (_32231 : int) : (term321 _32231) = (term322 _32231).
Proof. exact (@lem1982781 (real_of_int _32231) term263 term224). Qed.
Lemma lem3104870 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3104871 : term224 = term287.
Proof. exact (@lem3104870 term131). Qed.
Lemma lem3104873 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3104874 : term263 = term264.
Proof. exact (@lem3104873 term131). Qed.
Lemma lem3104875 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3104876 : term265 = term266.
Proof. exact (MK_COMB (@lem3104875) (@lem3104874)). Qed.
Lemma lem3104877 : term288 = term289.
Proof. exact (MK_COMB (@lem3104876) (@lem3104871)). Qed.
Lemma lem3104878 : term289 = term290.
Proof. exact (@lem1981613 term263 term224 term224 term224). Qed.
Lemma lem3104880 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3104881 : term272 = term273.
Proof. exact (@lem3104880 term131 term131). Qed.
Lemma lem3104882 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3104883 : term275 = term131.
Proof. exact (EQ_MP (@lem3104882) (@lem940073)). Qed.
Lemma lem3104884 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3104885 : term273 = term224.
Proof. exact (MK_COMB (@lem3104884) (@lem3104883)). Qed.
Lemma lem3104886 : term272 = term224.
Proof. exact (TRANS (@lem3104881) (@lem3104885)). Qed.
Lemma lem3104888 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3104889 : term288 = term293.
Proof. exact (@lem3104888 term131 term131). Qed.
Lemma lem3104890 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3104891 : term275 = term131.
Proof. exact (EQ_MP (@lem3104890) (@lem940073)). Qed.
Lemma lem3104892 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3104893 : term273 = term224.
Proof. exact (MK_COMB (@lem3104892) (@lem3104891)). Qed.
Lemma lem3104894 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3104895 : term293 = term263.
Proof. exact (MK_COMB (@lem3104894) (@lem3104893)). Qed.
Lemma lem3104896 : term288 = term263.
Proof. exact (TRANS (@lem3104889) (@lem3104895)). Qed.
Lemma lem3104897 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3104898 : term294 = term295.
Proof. exact (MK_COMB (@lem3104897) (@lem3104896)). Qed.
Lemma lem3104899 : term290 = term264.
Proof. exact (MK_COMB (@lem3104898) (@lem3104886)). Qed.
Lemma lem3104900 : term289 = term264.
Proof. exact (TRANS (@lem3104878) (@lem3104899)). Qed.
Lemma lem3104901 : term288 = term264.
Proof. exact (TRANS (@lem3104877) (@lem3104900)). Qed.
Lemma lem3104903 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3104904 : term264 = term263.
Proof. exact (@lem3104903 term263). Qed.
Lemma lem3104905 : term288 = term263.
Proof. exact (TRANS (@lem3104901) (@lem3104904)). Qed.
Lemma lem3104908 (_32231 : int) : (term323 _32231) = (term323 _32231).
Proof. exact (eq_refl (term323 _32231)). Qed.
Lemma lem3104909 (_32231 : int) : (term322 _32231) = (term324 _32231).
Proof. exact (MK_COMB (@lem3104908 _32231) (@lem3104905)). Qed.
Lemma lem3104910 (_32231 : int) : (term321 _32231) = (term324 _32231).
Proof. exact (TRANS (@lem3104868 _32231) (@lem3104909 _32231)). Qed.
Lemma lem3104911 (_32232 : int) : (term241 _32232) = (term241 _32232).
Proof. exact (eq_refl (term241 _32232)). Qed.
Lemma lem3104912 (_32232 : int) (_32231 : int) : (term320 _32232 _32231) = (term325 _32232 _32231).
Proof. exact (MK_COMB (@lem3104911 _32232) (@lem3104910 _32231)). Qed.
Lemma lem3104917 (_32231 : int) (_32232 : int) : (term325 _32232 _32231) = (term326 _32231 _32232).
Proof. exact (@lem1982757 (term312 _32231) (real_of_int _32232) term263). Qed.
Lemma lem3104918 (_32231 : int) (_32232 : int) : (term320 _32232 _32231) = (term326 _32231 _32232).
Proof. exact (TRANS (@lem3104912 _32232 _32231) (@lem3104917 _32231 _32232)). Qed.
Lemma lem3104920 (_32231 : int) (_32232 : int) : (term319 _32232 _32231) = (term326 _32231 _32232).
Proof. exact (TRANS (@lem3104867 _32232 _32231) (@lem3104918 _32231 _32232)). Qed.
Lemma lem3104921 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3104922 (_32231 : int) (_32232 : int) : (term327 _32232 _32231) = (term328 _32231 _32232).
Proof. exact (MK_COMB (@lem3104921) (@lem3104920 _32231 _32232)). Qed.
Lemma lem3104923 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3104924 (_32231 : int) (_32232 : int) : (term318 _32232 _32231) = (term329 _32231 _32232).
Proof. exact (MK_COMB (@lem3104922 _32231 _32232) (@lem3104923)). Qed.
Lemma lem3104925 (_32231 : int) (_32232 : int) : (term245 _32231 _32232) = (term329 _32231 _32232).
Proof. exact (TRANS (@lem3104855 _32232 _32231) (@lem3104924 _32231 _32232)). Qed.
Lemma lem3104926 (_32231 : int) (_32232 : int) : (term245 _32232 _32231) = (term318 _32231 _32232).
Proof. exact (@lem1988287 (real_of_int _32231) (term242 _32232)). Qed.
Lemma lem3104938 (_32231 : int) (_32232 : int) : (term319 _32231 _32232) = (term320 _32231 _32232).
Proof. exact (@lem1982792 (real_of_int _32231) (term242 _32232)). Qed.
Lemma lem3104939 (_32232 : int) : (term321 _32232) = (term322 _32232).
Proof. exact (@lem1982781 (real_of_int _32232) term263 term224). Qed.
Lemma lem3104941 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3104942 : term224 = term287.
Proof. exact (@lem3104941 term131). Qed.
Lemma lem3104944 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3104945 : term263 = term264.
Proof. exact (@lem3104944 term131). Qed.
Lemma lem3104946 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3104947 : term265 = term266.
Proof. exact (MK_COMB (@lem3104946) (@lem3104945)). Qed.
Lemma lem3104948 : term288 = term289.
Proof. exact (MK_COMB (@lem3104947) (@lem3104942)). Qed.
Lemma lem3104949 : term289 = term290.
Proof. exact (@lem1981613 term263 term224 term224 term224). Qed.
Lemma lem3104951 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3104952 : term272 = term273.
Proof. exact (@lem3104951 term131 term131). Qed.
Lemma lem3104953 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3104954 : term275 = term131.
Proof. exact (EQ_MP (@lem3104953) (@lem940073)). Qed.
Lemma lem3104955 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3104956 : term273 = term224.
Proof. exact (MK_COMB (@lem3104955) (@lem3104954)). Qed.
Lemma lem3104957 : term272 = term224.
Proof. exact (TRANS (@lem3104952) (@lem3104956)). Qed.
Lemma lem3104959 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3104960 : term288 = term293.
Proof. exact (@lem3104959 term131 term131). Qed.
Lemma lem3104961 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3104962 : term275 = term131.
Proof. exact (EQ_MP (@lem3104961) (@lem940073)). Qed.
Lemma lem3104963 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3104964 : term273 = term224.
Proof. exact (MK_COMB (@lem3104963) (@lem3104962)). Qed.
Lemma lem3104965 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3104966 : term293 = term263.
Proof. exact (MK_COMB (@lem3104965) (@lem3104964)). Qed.
Lemma lem3104967 : term288 = term263.
Proof. exact (TRANS (@lem3104960) (@lem3104966)). Qed.
Lemma lem3104968 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3104969 : term294 = term295.
Proof. exact (MK_COMB (@lem3104968) (@lem3104967)). Qed.
Lemma lem3104970 : term290 = term264.
Proof. exact (MK_COMB (@lem3104969) (@lem3104957)). Qed.
Lemma lem3104971 : term289 = term264.
Proof. exact (TRANS (@lem3104949) (@lem3104970)). Qed.
Lemma lem3104972 : term288 = term264.
Proof. exact (TRANS (@lem3104948) (@lem3104971)). Qed.
Lemma lem3104974 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3104975 : term264 = term263.
Proof. exact (@lem3104974 term263). Qed.
Lemma lem3104976 : term288 = term263.
Proof. exact (TRANS (@lem3104972) (@lem3104975)). Qed.
Lemma lem3104979 (_32232 : int) : (term323 _32232) = (term323 _32232).
Proof. exact (eq_refl (term323 _32232)). Qed.
Lemma lem3104980 (_32232 : int) : (term322 _32232) = (term324 _32232).
Proof. exact (MK_COMB (@lem3104979 _32232) (@lem3104976)). Qed.
Lemma lem3104981 (_32232 : int) : (term321 _32232) = (term324 _32232).
Proof. exact (TRANS (@lem3104939 _32232) (@lem3104980 _32232)). Qed.
Lemma lem3104982 (_32231 : int) : (term241 _32231) = (term241 _32231).
Proof. exact (eq_refl (term241 _32231)). Qed.
Lemma lem3104985 (_32231 : int) (_32232 : int) : (term320 _32231 _32232) = (term325 _32231 _32232).
Proof. exact (MK_COMB (@lem3104982 _32231) (@lem3104981 _32232)). Qed.
Lemma lem3104987 (_32231 : int) (_32232 : int) : (term319 _32231 _32232) = (term325 _32231 _32232).
Proof. exact (TRANS (@lem3104938 _32231 _32232) (@lem3104985 _32231 _32232)). Qed.
Lemma lem3104988 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3104989 (_32231 : int) (_32232 : int) : (term327 _32231 _32232) = (term330 _32231 _32232).
Proof. exact (MK_COMB (@lem3104988) (@lem3104987 _32231 _32232)). Qed.
Lemma lem3104990 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3104991 (_32231 : int) (_32232 : int) : (term318 _32231 _32232) = (term331 _32231 _32232).
Proof. exact (MK_COMB (@lem3104989 _32231 _32232) (@lem3104990)). Qed.
Lemma lem3104992 (_32231 : int) (_32232 : int) : (term245 _32232 _32231) = (term331 _32231 _32232).
Proof. exact (TRANS (@lem3104926 _32231 _32232) (@lem3104991 _32231 _32232)). Qed.
Lemma lem3104993 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3104994 (_32231 : int) (_32232 : int) : (term247 _32231 _32232) = (term332 _32231 _32232).
Proof. exact (MK_COMB (@lem3104993) (@lem3104925 _32231 _32232)). Qed.
Lemma lem3104995 (_32231 : int) (_32232 : int) : (term248 _32232 _32231) = (term333 _32231 _32232).
Proof. exact (MK_COMB (@lem3104994 _32231 _32232) (@lem3104992 _32231 _32232)). Qed.
Lemma lem3104996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3104997 (_32231 : int) (_32232 : int) : (term249 _32231 _32232) = (term334 _32231 _32232).
Proof. exact (MK_COMB (@lem3104996) (@lem3104854 _32231 _32232)). Qed.
Lemma lem3104998 (_32231 : int) (_32232 : int) : (term250 _32232 _32231) = (term335 _32231 _32232).
Proof. exact (MK_COMB (@lem3104997 _32231 _32232) (@lem3104995 _32231 _32232)). Qed.
Lemma lem3104999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3105000 (_32232 : int) (_32231 : int) : (term249 _32232 _32231) = (term336 _32232 _32231).
Proof. exact (MK_COMB (@lem3104999) (@lem3104726 _32232 _32231)). Qed.
Lemma lem3105001 (_32231 : int) (_32232 : int) : (term251 _32232 _32231) = (term337 _32231 _32232).
Proof. exact (MK_COMB (@lem3105000 _32232 _32231) (@lem3104998 _32231 _32232)). Qed.
Lemma lem3105002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3105003 (_32232 : int) : (term252 _32232) = (term338 _32232).
Proof. exact (MK_COMB (@lem3105002) (@lem3104598 _32232)). Qed.
Lemma lem3105004 (_32231 : int) (_32232 : int) : (term253 _32232 _32231) = (term339 _32231 _32232).
Proof. exact (MK_COMB (@lem3105003 _32232) (@lem3105001 _32231 _32232)). Qed.
Lemma lem3105005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3105006 (_32231 : int) : (term252 _32231) = (term338 _32231).
Proof. exact (MK_COMB (@lem3105005) (@lem3104550 _32231)). Qed.
Lemma lem3105007 (_32231 : int) (_32232 : int) : (term254 _32232 _32231) = (term340 _32231 _32232).
Proof. exact (MK_COMB (@lem3105006 _32231) (@lem3105004 _32231 _32232)). Qed.
Lemma lem3105014 (_32231 : int) (_32232 : int) : (term255 _32232 _32231) = (term340 _32231 _32232).
Proof. exact (TRANS (@lem3104502 _32232 _32231) (@lem3105007 _32231 _32232)). Qed.
Lemma lem3105034 (_32231 : int) (_32232 : int) : (term335 _32231 _32232) = (term341 _32231 _32232).
Proof. exact (@lem19158 (term329 _32231 _32232) (term317 _32231 _32232) (term331 _32231 _32232)). Qed.
Lemma lem3105041 (_32231 : int) (_32232 : int) : (term342 _32231 _32232) = (term343 _32231 _32232).
Proof. exact (@lem19367 (term315 _32231 _32232) ((real_of_int _32232) = term217) (term331 _32231 _32232)). Qed.
Lemma lem3105048 (_32231 : int) (_32232 : int) : (term344 _32231 _32232) = (term345 _32231 _32232).
Proof. exact (@lem19367 (term315 _32231 _32232) ((real_of_int _32232) = term217) (term329 _32231 _32232)). Qed.
Lemma lem3105049 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3105050 (_32231 : int) (_32232 : int) : (term346 _32231 _32232) = (term347 _32231 _32232).
Proof. exact (MK_COMB (@lem3105049) (@lem3105048 _32231 _32232)). Qed.
Lemma lem3105051 (_32231 : int) (_32232 : int) : (term341 _32231 _32232) = (term348 _32231 _32232).
Proof. exact (MK_COMB (@lem3105050 _32231 _32232) (@lem3105041 _32231 _32232)). Qed.
Lemma lem3105053 (_32231 : int) (_32232 : int) : (term335 _32231 _32232) = (term348 _32231 _32232).
Proof. exact (TRANS (@lem3105034 _32231 _32232) (@lem3105051 _32231 _32232)). Qed.
Lemma lem3105066 (_32232 : int) (_32231 : int) : (term336 _32232 _32231) = (term336 _32232 _32231).
Proof. exact (eq_refl (term336 _32232 _32231)). Qed.
Lemma lem3105067 (_32231 : int) (_32232 : int) : (term337 _32231 _32232) = (term349 _32231 _32232).
Proof. exact (MK_COMB (@lem3105066 _32232 _32231) (@lem3105053 _32231 _32232)). Qed.
Lemma lem3105068 (_32231 : int) (_32232 : int) : (term349 _32231 _32232) = (term350 _32231 _32232).
Proof. exact (@lem19158 (term345 _32231 _32232) (term310 _32232 _32231) (term343 _32231 _32232)). Qed.
Lemma lem3105069 (_32231 : int) (_32232 : int) : (term351 _32231 _32232) = (term352 _32231 _32232).
Proof. exact (@lem19158 (term353 _32231 _32232) (term310 _32232 _32231) (term354 _32231 _32232)). Qed.
Lemma lem3105076 (_32231 : int) (_32232 : int) : (term355 _32231 _32232) = (term356 _32231 _32232).
Proof. exact (@lem19367 (term307 _32231 _32232) ((real_of_int _32231) = term217) (term354 _32231 _32232)). Qed.
Lemma lem3105083 (_32231 : int) (_32232 : int) : (term357 _32231 _32232) = (term358 _32231 _32232).
Proof. exact (@lem19367 (term307 _32231 _32232) ((real_of_int _32231) = term217) (term353 _32231 _32232)). Qed.
Lemma lem3105084 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3105085 (_32231 : int) (_32232 : int) : (term359 _32231 _32232) = (term360 _32231 _32232).
Proof. exact (MK_COMB (@lem3105084) (@lem3105083 _32231 _32232)). Qed.
Lemma lem3105086 (_32231 : int) (_32232 : int) : (term352 _32231 _32232) = (term361 _32231 _32232).
Proof. exact (MK_COMB (@lem3105085 _32231 _32232) (@lem3105076 _32231 _32232)). Qed.
Lemma lem3105087 (_32231 : int) (_32232 : int) : (term351 _32231 _32232) = (term361 _32231 _32232).
Proof. exact (TRANS (@lem3105069 _32231 _32232) (@lem3105086 _32231 _32232)). Qed.
Lemma lem3105088 (_32231 : int) (_32232 : int) : (term362 _32231 _32232) = (term363 _32231 _32232).
Proof. exact (@lem19158 (term364 _32231 _32232) (term310 _32232 _32231) (term365 _32231 _32232)). Qed.
Lemma lem3105095 (_32231 : int) (_32232 : int) : (term366 _32231 _32232) = (term367 _32231 _32232).
Proof. exact (@lem19367 (term307 _32231 _32232) ((real_of_int _32231) = term217) (term365 _32231 _32232)). Qed.
Lemma lem3105102 (_32231 : int) (_32232 : int) : (term368 _32231 _32232) = (term369 _32231 _32232).
Proof. exact (@lem19367 (term307 _32231 _32232) ((real_of_int _32231) = term217) (term364 _32231 _32232)). Qed.
Lemma lem3105103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3105104 (_32231 : int) (_32232 : int) : (term370 _32231 _32232) = (term371 _32231 _32232).
Proof. exact (MK_COMB (@lem3105103) (@lem3105102 _32231 _32232)). Qed.
Lemma lem3105105 (_32231 : int) (_32232 : int) : (term363 _32231 _32232) = (term372 _32231 _32232).
Proof. exact (MK_COMB (@lem3105104 _32231 _32232) (@lem3105095 _32231 _32232)). Qed.
Lemma lem3105106 (_32231 : int) (_32232 : int) : (term362 _32231 _32232) = (term372 _32231 _32232).
Proof. exact (TRANS (@lem3105088 _32231 _32232) (@lem3105105 _32231 _32232)). Qed.
Lemma lem3105107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3105108 (_32231 : int) (_32232 : int) : (term373 _32231 _32232) = (term374 _32231 _32232).
Proof. exact (MK_COMB (@lem3105107) (@lem3105106 _32231 _32232)). Qed.
Lemma lem3105109 (_32231 : int) (_32232 : int) : (term350 _32231 _32232) = (term375 _32231 _32232).
Proof. exact (MK_COMB (@lem3105108 _32231 _32232) (@lem3105087 _32231 _32232)). Qed.
Lemma lem3105110 (_32231 : int) (_32232 : int) : (term349 _32231 _32232) = (term375 _32231 _32232).
Proof. exact (TRANS (@lem3105068 _32231 _32232) (@lem3105109 _32231 _32232)). Qed.
Lemma lem3105111 (_32231 : int) (_32232 : int) : (term337 _32231 _32232) = (term375 _32231 _32232).
Proof. exact (TRANS (@lem3105067 _32231 _32232) (@lem3105110 _32231 _32232)). Qed.
Lemma lem3105114 (_32232 : int) : (term338 _32232) = (term338 _32232).
Proof. exact (eq_refl (term338 _32232)). Qed.
Lemma lem3105115 (_32231 : int) (_32232 : int) : (term339 _32231 _32232) = (term376 _32231 _32232).
Proof. exact (MK_COMB (@lem3105114 _32232) (@lem3105111 _32231 _32232)). Qed.
Lemma lem3105116 (_32231 : int) (_32232 : int) : (term376 _32231 _32232) = (term377 _32231 _32232).
Proof. exact (@lem19158 (term372 _32231 _32232) (term283 _32232) (term361 _32231 _32232)). Qed.
Lemma lem3105117 (_32231 : int) (_32232 : int) : (term378 _32231 _32232) = (term379 _32231 _32232).
Proof. exact (@lem19158 (term358 _32231 _32232) (term283 _32232) (term356 _32231 _32232)). Qed.
Lemma lem3105124 (_32231 : int) (_32232 : int) : (term380 _32231 _32232) = (term381 _32231 _32232).
Proof. exact (@lem19158 (term382 _32231 _32232) (term283 _32232) (term383 _32231 _32232)). Qed.
Lemma lem3105131 (_32231 : int) (_32232 : int) : (term384 _32231 _32232) = (term385 _32231 _32232).
Proof. exact (@lem19158 (term386 _32231 _32232) (term283 _32232) (term387 _32231 _32232)). Qed.
Lemma lem3105132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3105133 (_32231 : int) (_32232 : int) : (term388 _32231 _32232) = (term389 _32231 _32232).
Proof. exact (MK_COMB (@lem3105132) (@lem3105131 _32231 _32232)). Qed.
Lemma lem3105134 (_32231 : int) (_32232 : int) : (term379 _32231 _32232) = (term390 _32231 _32232).
Proof. exact (MK_COMB (@lem3105133 _32231 _32232) (@lem3105124 _32231 _32232)). Qed.
Lemma lem3105135 (_32231 : int) (_32232 : int) : (term378 _32231 _32232) = (term390 _32231 _32232).
Proof. exact (TRANS (@lem3105117 _32231 _32232) (@lem3105134 _32231 _32232)). Qed.
Lemma lem3105136 (_32231 : int) (_32232 : int) : (term391 _32231 _32232) = (term392 _32231 _32232).
Proof. exact (@lem19158 (term369 _32231 _32232) (term283 _32232) (term367 _32231 _32232)). Qed.
Lemma lem3105143 (_32231 : int) (_32232 : int) : (term393 _32231 _32232) = (term394 _32231 _32232).
Proof. exact (@lem19158 (term395 _32231 _32232) (term283 _32232) (term396 _32231 _32232)). Qed.
Lemma lem3105150 (_32231 : int) (_32232 : int) : (term397 _32231 _32232) = (term398 _32231 _32232).
Proof. exact (@lem19158 (term399 _32231 _32232) (term283 _32232) (term400 _32231 _32232)). Qed.
Lemma lem3105151 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3105152 (_32231 : int) (_32232 : int) : (term401 _32231 _32232) = (term402 _32231 _32232).
Proof. exact (MK_COMB (@lem3105151) (@lem3105150 _32231 _32232)). Qed.
Lemma lem3105153 (_32231 : int) (_32232 : int) : (term392 _32231 _32232) = (term403 _32231 _32232).
Proof. exact (MK_COMB (@lem3105152 _32231 _32232) (@lem3105143 _32231 _32232)). Qed.
Lemma lem3105154 (_32231 : int) (_32232 : int) : (term391 _32231 _32232) = (term403 _32231 _32232).
Proof. exact (TRANS (@lem3105136 _32231 _32232) (@lem3105153 _32231 _32232)). Qed.
Lemma lem3105155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3105156 (_32231 : int) (_32232 : int) : (term404 _32231 _32232) = (term405 _32231 _32232).
Proof. exact (MK_COMB (@lem3105155) (@lem3105154 _32231 _32232)). Qed.
Lemma lem3105157 (_32231 : int) (_32232 : int) : (term377 _32231 _32232) = (term406 _32231 _32232).
Proof. exact (MK_COMB (@lem3105156 _32231 _32232) (@lem3105135 _32231 _32232)). Qed.
Lemma lem3105158 (_32231 : int) (_32232 : int) : (term376 _32231 _32232) = (term406 _32231 _32232).
Proof. exact (TRANS (@lem3105116 _32231 _32232) (@lem3105157 _32231 _32232)). Qed.
Lemma lem3105159 (_32231 : int) (_32232 : int) : (term339 _32231 _32232) = (term406 _32231 _32232).
Proof. exact (TRANS (@lem3105115 _32231 _32232) (@lem3105158 _32231 _32232)). Qed.
Lemma lem3105162 (_32231 : int) : (term338 _32231) = (term338 _32231).
Proof. exact (eq_refl (term338 _32231)). Qed.
Lemma lem3105163 (_32231 : int) (_32232 : int) : (term340 _32231 _32232) = (term407 _32231 _32232).
Proof. exact (MK_COMB (@lem3105162 _32231) (@lem3105159 _32231 _32232)). Qed.
Lemma lem3105164 (_32231 : int) (_32232 : int) : (term407 _32231 _32232) = (term408 _32231 _32232).
Proof. exact (@lem19158 (term403 _32231 _32232) (term283 _32231) (term390 _32231 _32232)). Qed.
Lemma lem3105165 (_32231 : int) (_32232 : int) : (term409 _32231 _32232) = (term410 _32231 _32232).
Proof. exact (@lem19158 (term385 _32231 _32232) (term283 _32231) (term381 _32231 _32232)). Qed.
Lemma lem3105172 (_32231 : int) (_32232 : int) : (term411 _32231 _32232) = (term412 _32231 _32232).
Proof. exact (@lem19158 (term413 _32231 _32232) (term283 _32231) (term414 _32231 _32232)). Qed.
Lemma lem3105179 (_32231 : int) (_32232 : int) : (term415 _32231 _32232) = (term416 _32231 _32232).
Proof. exact (@lem19158 (term417 _32231 _32232) (term283 _32231) (term418 _32231 _32232)). Qed.
Lemma lem3105180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3105181 (_32231 : int) (_32232 : int) : (term419 _32231 _32232) = (term420 _32231 _32232).
Proof. exact (MK_COMB (@lem3105180) (@lem3105179 _32231 _32232)). Qed.
Lemma lem3105182 (_32231 : int) (_32232 : int) : (term410 _32231 _32232) = (term421 _32231 _32232).
Proof. exact (MK_COMB (@lem3105181 _32231 _32232) (@lem3105172 _32231 _32232)). Qed.
Lemma lem3105183 (_32231 : int) (_32232 : int) : (term409 _32231 _32232) = (term421 _32231 _32232).
Proof. exact (TRANS (@lem3105165 _32231 _32232) (@lem3105182 _32231 _32232)). Qed.
Lemma lem3105184 (_32231 : int) (_32232 : int) : (term422 _32231 _32232) = (term423 _32231 _32232).
Proof. exact (@lem19158 (term398 _32231 _32232) (term283 _32231) (term394 _32231 _32232)). Qed.
Lemma lem3105191 (_32231 : int) (_32232 : int) : (term424 _32231 _32232) = (term425 _32231 _32232).
Proof. exact (@lem19158 (term426 _32231 _32232) (term283 _32231) (term427 _32231 _32232)). Qed.
Lemma lem3105198 (_32231 : int) (_32232 : int) : (term428 _32231 _32232) = (term429 _32231 _32232).
Proof. exact (@lem19158 (term430 _32231 _32232) (term283 _32231) (term431 _32231 _32232)). Qed.
Lemma lem3105199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3105200 (_32231 : int) (_32232 : int) : (term432 _32231 _32232) = (term433 _32231 _32232).
Proof. exact (MK_COMB (@lem3105199) (@lem3105198 _32231 _32232)). Qed.
Lemma lem3105201 (_32231 : int) (_32232 : int) : (term423 _32231 _32232) = (term434 _32231 _32232).
Proof. exact (MK_COMB (@lem3105200 _32231 _32232) (@lem3105191 _32231 _32232)). Qed.
Lemma lem3105202 (_32231 : int) (_32232 : int) : (term422 _32231 _32232) = (term434 _32231 _32232).
Proof. exact (TRANS (@lem3105184 _32231 _32232) (@lem3105201 _32231 _32232)). Qed.
Lemma lem3105203 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3105204 (_32231 : int) (_32232 : int) : (term435 _32231 _32232) = (term436 _32231 _32232).
Proof. exact (MK_COMB (@lem3105203) (@lem3105202 _32231 _32232)). Qed.
Lemma lem3105205 (_32231 : int) (_32232 : int) : (term408 _32231 _32232) = (term437 _32231 _32232).
Proof. exact (MK_COMB (@lem3105204 _32231 _32232) (@lem3105183 _32231 _32232)). Qed.
Lemma lem3105206 (_32231 : int) (_32232 : int) : (term407 _32231 _32232) = (term437 _32231 _32232).
Proof. exact (TRANS (@lem3105164 _32231 _32232) (@lem3105205 _32231 _32232)). Qed.
Lemma lem3105207 (_32231 : int) (_32232 : int) : (term340 _32231 _32232) = (term437 _32231 _32232).
Proof. exact (TRANS (@lem3105163 _32231 _32232) (@lem3105206 _32231 _32232)). Qed.
Lemma lem3105208 (_32231 : int) (_32232 : int) : (term255 _32232 _32231) = (term437 _32231 _32232).
Proof. exact (TRANS (@lem3105014 _32231 _32232) (@lem3105207 _32231 _32232)). Qed.
Lemma lem3105254 (_32231 : int) (_32232 : int) (h1 : term437 _32231 _32232) : term437 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3105255 (_32231 : int) (_32232 : int) (h1 : term434 _32231 _32232) : term434 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3105256 (_32231 : int) (_32232 : int) (h1 : term429 _32231 _32232) : term429 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3105257 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term438 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3105258 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term430 _32231 _32232.
Proof. exact (proj2 (@lem3105257 _32231 _32232 h1)). Qed.
Lemma lem3105260 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term399 _32231 _32232.
Proof. exact (proj2 (@lem3105258 _32231 _32232 h1)). Qed.
Lemma lem3105262 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term364 _32231 _32232.
Proof. exact (proj2 (@lem3105260 _32231 _32232 h1)). Qed.
Lemma lem3105263 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term307 _32231 _32232.
Proof. exact (proj1 (@lem3105260 _32231 _32232 h1)). Qed.
Lemma lem3105264 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term305 _32231 _32232.
Proof. exact (proj2 (@lem3105263 _32231 _32232 h1)). Qed.
Lemma lem3105266 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term329 _32231 _32232.
Proof. exact (proj2 (@lem3105262 _32231 _32232 h1)). Qed.
Lemma lem3105271 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3105272 : term439 = term440.
Proof. exact (@lem3105271 term217 term224). Qed.
Lemma lem3105274 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3105275 : term224 = term287.
Proof. exact (@lem3105274 term131). Qed.
Lemma lem3105277 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3105278 : term217 = term260.
Proof. exact (@lem3105277 (NUMERAL 0)). Qed.
Lemma lem3105279 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3105280 : term441 = term442.
Proof. exact (MK_COMB (@lem3105279) (@lem3105278)). Qed.
Lemma lem3105281 : term440 = term443.
Proof. exact (MK_COMB (@lem3105280) (@lem3105275)). Qed.
Lemma lem3105282 : term444.
Proof. exact (@lem1980255 term217 term224 term224 term224). Qed.
Lemma lem3105284 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105285 : term440 = term446.
Proof. exact (@lem3105284 (NUMERAL 0) term131). Qed.
Lemma lem3105286 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105287 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105288 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105287 h1) (fun h1 : term446 = True => @lem3105286)). Qed.
Lemma lem3105289 : term446 = True.
Proof. exact (EQ_MP (@lem3105288) (@lem3105286)). Qed.
Lemma lem3105290 : term440 = True.
Proof. exact (TRANS (@lem3105285) (@lem3105289)). Qed.
Lemma lem3105291 : True = term440.
Proof. exact (SYM (@lem3105290)). Qed.
Lemma lem3105292 : term440.
Proof. exact (EQ_MP (@lem3105291) (@lem0)). Qed.
Lemma lem3105293 : term448.
Proof. exact (@lem3105282 (@lem3105292)). Qed.
Lemma lem3105295 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105296 : term440 = term446.
Proof. exact (@lem3105295 (NUMERAL 0) term131). Qed.
Lemma lem3105297 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105298 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105299 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105298 h1) (fun h1 : term446 = True => @lem3105297)). Qed.
Lemma lem3105300 : term446 = True.
Proof. exact (EQ_MP (@lem3105299) (@lem3105297)). Qed.
Lemma lem3105301 : term440 = True.
Proof. exact (TRANS (@lem3105296) (@lem3105300)). Qed.
Lemma lem3105302 : True = term440.
Proof. exact (SYM (@lem3105301)). Qed.
Lemma lem3105303 : term440.
Proof. exact (EQ_MP (@lem3105302) (@lem0)). Qed.
Lemma lem3105304 : term443 = term449.
Proof. exact (@lem3105293 (@lem3105303)). Qed.
Lemma lem3105306 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3105307 : term272 = term273.
Proof. exact (@lem3105306 term131 term131). Qed.
Lemma lem3105308 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105309 : term275 = term131.
Proof. exact (EQ_MP (@lem3105308) (@lem940073)). Qed.
Lemma lem3105310 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105311 : term273 = term224.
Proof. exact (MK_COMB (@lem3105310) (@lem3105309)). Qed.
Lemma lem3105312 : term272 = term224.
Proof. exact (TRANS (@lem3105307) (@lem3105311)). Qed.
Lemma lem3105314 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3105315 : term451 = term217.
Proof. exact (@lem3105314 term131). Qed.
Lemma lem3105316 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3105317 : term452 = term441.
Proof. exact (MK_COMB (@lem3105316) (@lem3105315)). Qed.
Lemma lem3105318 : term449 = term440.
Proof. exact (MK_COMB (@lem3105317) (@lem3105312)). Qed.
Lemma lem3105320 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105321 : term440 = term446.
Proof. exact (@lem3105320 (NUMERAL 0) term131). Qed.
Lemma lem3105322 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105323 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105324 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105323 h1) (fun h1 : term446 = True => @lem3105322)). Qed.
Lemma lem3105325 : term446 = True.
Proof. exact (EQ_MP (@lem3105324) (@lem3105322)). Qed.
Lemma lem3105326 : term440 = True.
Proof. exact (TRANS (@lem3105321) (@lem3105325)). Qed.
Lemma lem3105327 : term449 = True.
Proof. exact (TRANS (@lem3105318) (@lem3105326)). Qed.
Lemma lem3105328 : term443 = True.
Proof. exact (TRANS (@lem3105304) (@lem3105327)). Qed.
Lemma lem3105329 : term440 = True.
Proof. exact (TRANS (@lem3105281) (@lem3105328)). Qed.
Lemma lem3105330 : term439 = True.
Proof. exact (TRANS (@lem3105272) (@lem3105329)). Qed.
Lemma lem3105331 : True = term439.
Proof. exact (SYM (@lem3105330)). Qed.
Lemma lem3105332 : term439.
Proof. exact (EQ_MP (@lem3105331) (@lem0)). Qed.
Lemma lem3105333 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term453 _32231 _32232.
Proof. exact (conj (@lem3105332) (@lem3105266 _32231 _32232 h1)). Qed.
Lemma lem3105335 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3105336 (_32231 : int) (_32232 : int) : term455 _32231 _32232.
Proof. exact (@lem3105335 term224 (term326 _32231 _32232)). Qed.
Lemma lem3105337 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term456 _32231 _32232.
Proof. exact (@lem3105336 _32231 _32232 (@lem3105333 _32231 _32232 h1)). Qed.
Lemma lem3105338 (_32231 : int) (_32232 : int) : (term457 _32231 _32232) = (term326 _32231 _32232).
Proof. exact (@lem1982733 (term326 _32231 _32232)). Qed.
Lemma lem3105339 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3105340 (_32231 : int) (_32232 : int) : (term458 _32231 _32232) = (term328 _32231 _32232).
Proof. exact (MK_COMB (@lem3105339) (@lem3105338 _32231 _32232)). Qed.
Lemma lem3105341 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3105342 (_32231 : int) (_32232 : int) : (term456 _32231 _32232) = (term329 _32231 _32232).
Proof. exact (MK_COMB (@lem3105340 _32231 _32232) (@lem3105341)). Qed.
Lemma lem3105343 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term329 _32231 _32232.
Proof. exact (EQ_MP (@lem3105342 _32231 _32232) (@lem3105337 _32231 _32232 h1)). Qed.
Lemma lem3105345 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3105346 : term439 = term440.
Proof. exact (@lem3105345 term217 term224). Qed.
Lemma lem3105348 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3105349 : term224 = term287.
Proof. exact (@lem3105348 term131). Qed.
Lemma lem3105351 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3105352 : term217 = term260.
Proof. exact (@lem3105351 (NUMERAL 0)). Qed.
Lemma lem3105353 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3105354 : term441 = term442.
Proof. exact (MK_COMB (@lem3105353) (@lem3105352)). Qed.
Lemma lem3105355 : term440 = term443.
Proof. exact (MK_COMB (@lem3105354) (@lem3105349)). Qed.
Lemma lem3105356 : term444.
Proof. exact (@lem1980255 term217 term224 term224 term224). Qed.
Lemma lem3105358 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105359 : term440 = term446.
Proof. exact (@lem3105358 (NUMERAL 0) term131). Qed.
Lemma lem3105360 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105361 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105362 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105361 h1) (fun h1 : term446 = True => @lem3105360)). Qed.
Lemma lem3105363 : term446 = True.
Proof. exact (EQ_MP (@lem3105362) (@lem3105360)). Qed.
Lemma lem3105364 : term440 = True.
Proof. exact (TRANS (@lem3105359) (@lem3105363)). Qed.
Lemma lem3105365 : True = term440.
Proof. exact (SYM (@lem3105364)). Qed.
Lemma lem3105366 : term440.
Proof. exact (EQ_MP (@lem3105365) (@lem0)). Qed.
Lemma lem3105367 : term448.
Proof. exact (@lem3105356 (@lem3105366)). Qed.
Lemma lem3105369 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105370 : term440 = term446.
Proof. exact (@lem3105369 (NUMERAL 0) term131). Qed.
Lemma lem3105371 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105372 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105373 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105372 h1) (fun h1 : term446 = True => @lem3105371)). Qed.
Lemma lem3105374 : term446 = True.
Proof. exact (EQ_MP (@lem3105373) (@lem3105371)). Qed.
Lemma lem3105375 : term440 = True.
Proof. exact (TRANS (@lem3105370) (@lem3105374)). Qed.
Lemma lem3105376 : True = term440.
Proof. exact (SYM (@lem3105375)). Qed.
Lemma lem3105377 : term440.
Proof. exact (EQ_MP (@lem3105376) (@lem0)). Qed.
Lemma lem3105378 : term443 = term449.
Proof. exact (@lem3105367 (@lem3105377)). Qed.
Lemma lem3105380 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3105381 : term272 = term273.
Proof. exact (@lem3105380 term131 term131). Qed.
Lemma lem3105382 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105383 : term275 = term131.
Proof. exact (EQ_MP (@lem3105382) (@lem940073)). Qed.
Lemma lem3105384 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105385 : term273 = term224.
Proof. exact (MK_COMB (@lem3105384) (@lem3105383)). Qed.
Lemma lem3105386 : term272 = term224.
Proof. exact (TRANS (@lem3105381) (@lem3105385)). Qed.
Lemma lem3105388 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3105389 : term451 = term217.
Proof. exact (@lem3105388 term131). Qed.
Lemma lem3105390 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3105391 : term452 = term441.
Proof. exact (MK_COMB (@lem3105390) (@lem3105389)). Qed.
Lemma lem3105392 : term449 = term440.
Proof. exact (MK_COMB (@lem3105391) (@lem3105386)). Qed.
Lemma lem3105394 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105395 : term440 = term446.
Proof. exact (@lem3105394 (NUMERAL 0) term131). Qed.
Lemma lem3105396 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105397 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105398 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105397 h1) (fun h1 : term446 = True => @lem3105396)). Qed.
Lemma lem3105399 : term446 = True.
Proof. exact (EQ_MP (@lem3105398) (@lem3105396)). Qed.
Lemma lem3105400 : term440 = True.
Proof. exact (TRANS (@lem3105395) (@lem3105399)). Qed.
Lemma lem3105401 : term449 = True.
Proof. exact (TRANS (@lem3105392) (@lem3105400)). Qed.
Lemma lem3105402 : term443 = True.
Proof. exact (TRANS (@lem3105378) (@lem3105401)). Qed.
Lemma lem3105403 : term440 = True.
Proof. exact (TRANS (@lem3105355) (@lem3105402)). Qed.
Lemma lem3105404 : term439 = True.
Proof. exact (TRANS (@lem3105346) (@lem3105403)). Qed.
Lemma lem3105405 : True = term439.
Proof. exact (SYM (@lem3105404)). Qed.
Lemma lem3105406 : term439.
Proof. exact (EQ_MP (@lem3105405) (@lem0)). Qed.
Lemma lem3105407 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term459 _32231 _32232.
Proof. exact (conj (@lem3105406) (@lem3105264 _32231 _32232 h1)). Qed.
Lemma lem3105409 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3105410 (_32231 : int) (_32232 : int) : term460 _32231 _32232.
Proof. exact (@lem3105409 term224 (term302 _32231 _32232)). Qed.
Lemma lem3105411 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term461 _32231 _32232.
Proof. exact (@lem3105410 _32231 _32232 (@lem3105407 _32231 _32232 h1)). Qed.
Lemma lem3105412 (_32231 : int) (_32232 : int) : (term462 _32231 _32232) = (term302 _32231 _32232).
Proof. exact (@lem1982733 (term302 _32231 _32232)). Qed.
Lemma lem3105413 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3105414 (_32231 : int) (_32232 : int) : (term463 _32231 _32232) = (term304 _32231 _32232).
Proof. exact (MK_COMB (@lem3105413) (@lem3105412 _32231 _32232)). Qed.
Lemma lem3105415 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3105416 (_32231 : int) (_32232 : int) : (term461 _32231 _32232) = (term305 _32231 _32232).
Proof. exact (MK_COMB (@lem3105414 _32231 _32232) (@lem3105415)). Qed.
Lemma lem3105417 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term305 _32231 _32232.
Proof. exact (EQ_MP (@lem3105416 _32231 _32232) (@lem3105411 _32231 _32232 h1)). Qed.
Lemma lem3105418 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term464 _32231 _32232.
Proof. exact (conj (@lem3105417 _32231 _32232 h1) (@lem3105343 _32231 _32232 h1)). Qed.
Lemma lem3105420 (x : real) (y : real) : term465 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3105421 (_32231 : int) (_32232 : int) : term466 _32231 _32232.
Proof. exact (@lem3105420 (term302 _32231 _32232) (term326 _32231 _32232)). Qed.
Lemma lem3105422 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term467 _32231 _32232.
Proof. exact (@lem3105421 _32231 _32232 (@lem3105418 _32231 _32232 h1)). Qed.
Lemma lem3105423 (_32231 : int) (_32232 : int) : (term468 _32231 _32232) = (term469 _32231 _32232).
Proof. exact (@lem1982753 (real_of_int _32231) (term312 _32231) (term312 _32232) (term296 _32232)). Qed.
Lemma lem3105424 (_32231 : int) : (term470 _32231) = (term471 _32231).
Proof. exact (@lem1982715 term263 (real_of_int _32231)). Qed.
Lemma lem3105426 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3105427 : term224 = term287.
Proof. exact (@lem3105426 term131). Qed.
Lemma lem3105429 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3105430 : term263 = term264.
Proof. exact (@lem3105429 term131). Qed.
Lemma lem3105431 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3105432 : term472 = term473.
Proof. exact (MK_COMB (@lem3105431) (@lem3105430)). Qed.
Lemma lem3105433 : term474 = term475.
Proof. exact (MK_COMB (@lem3105432) (@lem3105427)). Qed.
Lemma lem3105434 : term476.
Proof. exact (@lem1981473 term263 term224 term224 term224 term217 term224). Qed.
Lemma lem3105436 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105437 : term440 = term446.
Proof. exact (@lem3105436 (NUMERAL 0) term131). Qed.
Lemma lem3105438 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105439 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105440 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105439 h1) (fun h1 : term446 = True => @lem3105438)). Qed.
Lemma lem3105441 : term446 = True.
Proof. exact (EQ_MP (@lem3105440) (@lem3105438)). Qed.
Lemma lem3105442 : term440 = True.
Proof. exact (TRANS (@lem3105437) (@lem3105441)). Qed.
Lemma lem3105443 : True = term440.
Proof. exact (SYM (@lem3105442)). Qed.
Lemma lem3105444 : term440.
Proof. exact (EQ_MP (@lem3105443) (@lem0)). Qed.
Lemma lem3105445 : term477.
Proof. exact (@lem3105434 (@lem3105444)). Qed.
Lemma lem3105447 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105448 : term440 = term446.
Proof. exact (@lem3105447 (NUMERAL 0) term131). Qed.
Lemma lem3105449 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105450 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105451 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105450 h1) (fun h1 : term446 = True => @lem3105449)). Qed.
Lemma lem3105452 : term446 = True.
Proof. exact (EQ_MP (@lem3105451) (@lem3105449)). Qed.
Lemma lem3105453 : term440 = True.
Proof. exact (TRANS (@lem3105448) (@lem3105452)). Qed.
Lemma lem3105454 : True = term440.
Proof. exact (SYM (@lem3105453)). Qed.
Lemma lem3105455 : term440.
Proof. exact (EQ_MP (@lem3105454) (@lem0)). Qed.
Lemma lem3105456 : term478.
Proof. exact (@lem3105445 (@lem3105455)). Qed.
Lemma lem3105458 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105459 : term440 = term446.
Proof. exact (@lem3105458 (NUMERAL 0) term131). Qed.
Lemma lem3105460 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105461 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105462 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105461 h1) (fun h1 : term446 = True => @lem3105460)). Qed.
Lemma lem3105463 : term446 = True.
Proof. exact (EQ_MP (@lem3105462) (@lem3105460)). Qed.
Lemma lem3105464 : term440 = True.
Proof. exact (TRANS (@lem3105459) (@lem3105463)). Qed.
Lemma lem3105465 : True = term440.
Proof. exact (SYM (@lem3105464)). Qed.
Lemma lem3105466 : term440.
Proof. exact (EQ_MP (@lem3105465) (@lem0)). Qed.
Lemma lem3105467 : term479.
Proof. exact (@lem3105456 (@lem3105466)). Qed.
Lemma lem3105469 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3105470 : term272 = term273.
Proof. exact (@lem3105469 term131 term131). Qed.
Lemma lem3105471 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105472 : term275 = term131.
Proof. exact (EQ_MP (@lem3105471) (@lem940073)). Qed.
Lemma lem3105473 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105474 : term273 = term224.
Proof. exact (MK_COMB (@lem3105473) (@lem3105472)). Qed.
Lemma lem3105475 : term272 = term224.
Proof. exact (TRANS (@lem3105470) (@lem3105474)). Qed.
Lemma lem3105477 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3105478 : term288 = term293.
Proof. exact (@lem3105477 term131 term131). Qed.
Lemma lem3105479 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105480 : term275 = term131.
Proof. exact (EQ_MP (@lem3105479) (@lem940073)). Qed.
Lemma lem3105481 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105482 : term273 = term224.
Proof. exact (MK_COMB (@lem3105481) (@lem3105480)). Qed.
Lemma lem3105483 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3105484 : term293 = term263.
Proof. exact (MK_COMB (@lem3105483) (@lem3105482)). Qed.
Lemma lem3105485 : term288 = term263.
Proof. exact (TRANS (@lem3105478) (@lem3105484)). Qed.
Lemma lem3105486 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3105487 : term480 = term472.
Proof. exact (MK_COMB (@lem3105486) (@lem3105485)). Qed.
Lemma lem3105488 : term481 = term474.
Proof. exact (MK_COMB (@lem3105487) (@lem3105475)). Qed.
Lemma lem3105490 (m : nat) : (term482 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3105491 : term474 = term217.
Proof. exact (@lem3105490 term131). Qed.
Lemma lem3105492 : term481 = term217.
Proof. exact (TRANS (@lem3105488) (@lem3105491)). Qed.
Lemma lem3105493 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3105494 : term483 = term484.
Proof. exact (MK_COMB (@lem3105493) (@lem3105492)). Qed.
Lemma lem3105495 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem3105496 : term485 = term451.
Proof. exact (MK_COMB (@lem3105494) (@lem3105495)). Qed.
Lemma lem3105498 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3105499 : term451 = term217.
Proof. exact (@lem3105498 term131). Qed.
Lemma lem3105500 : term485 = term217.
Proof. exact (TRANS (@lem3105496) (@lem3105499)). Qed.
Lemma lem3105502 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3105503 : term272 = term273.
Proof. exact (@lem3105502 term131 term131). Qed.
Lemma lem3105504 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105505 : term275 = term131.
Proof. exact (EQ_MP (@lem3105504) (@lem940073)). Qed.
Lemma lem3105506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105507 : term273 = term224.
Proof. exact (MK_COMB (@lem3105506) (@lem3105505)). Qed.
Lemma lem3105508 : term272 = term224.
Proof. exact (TRANS (@lem3105503) (@lem3105507)). Qed.
Lemma lem3105509 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem3105510 : term486 = term451.
Proof. exact (MK_COMB (@lem3105509) (@lem3105508)). Qed.
Lemma lem3105512 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3105513 : term451 = term217.
Proof. exact (@lem3105512 term131). Qed.
Lemma lem3105514 : term486 = term217.
Proof. exact (TRANS (@lem3105510) (@lem3105513)). Qed.
Lemma lem3105515 : term217 = term486.
Proof. exact (SYM (@lem3105514)). Qed.
Lemma lem3105516 : term485 = term486.
Proof. exact (TRANS (@lem3105500) (@lem3105515)). Qed.
Lemma lem3105517 : term475 = term260.
Proof. exact (@lem3105467 (@lem3105516)). Qed.
Lemma lem3105518 : term474 = term260.
Proof. exact (TRANS (@lem3105433) (@lem3105517)). Qed.
Lemma lem3105520 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3105521 : term260 = term217.
Proof. exact (@lem3105520 term217). Qed.
Lemma lem3105522 : term474 = term217.
Proof. exact (TRANS (@lem3105518) (@lem3105521)). Qed.
Lemma lem3105523 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3105524 : term487 = term484.
Proof. exact (MK_COMB (@lem3105523) (@lem3105522)). Qed.
Lemma lem3105525 (_32231 : int) : (real_of_int _32231) = (real_of_int _32231).
Proof. exact (eq_refl (real_of_int _32231)). Qed.
Lemma lem3105526 (_32231 : int) : (term471 _32231) = (term488 _32231).
Proof. exact (MK_COMB (@lem3105524) (@lem3105525 _32231)). Qed.
Lemma lem3105527 (_32231 : int) : (term470 _32231) = (term488 _32231).
Proof. exact (TRANS (@lem3105424 _32231) (@lem3105526 _32231)). Qed.
Lemma lem3105528 (_32231 : int) : (term488 _32231) = term217.
Proof. exact (@lem1982719 (real_of_int _32231)). Qed.
Lemma lem3105529 (_32231 : int) : (term470 _32231) = term217.
Proof. exact (TRANS (@lem3105527 _32231) (@lem3105528 _32231)). Qed.
Lemma lem3105530 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3105531 (_32231 : int) : (term489 _32231) = term490.
Proof. exact (MK_COMB (@lem3105530) (@lem3105529 _32231)). Qed.
Lemma lem3105532 (_32232 : int) : (term491 _32232) = (term492 _32232).
Proof. exact (@lem1982763 (term312 _32232) (real_of_int _32232) term263). Qed.
Lemma lem3105533 (_32232 : int) : (term493 _32232) = (term471 _32232).
Proof. exact (@lem1982713 term263 (real_of_int _32232)). Qed.
Lemma lem3105535 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3105536 : term224 = term287.
Proof. exact (@lem3105535 term131). Qed.
Lemma lem3105538 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3105539 : term263 = term264.
Proof. exact (@lem3105538 term131). Qed.
Lemma lem3105540 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3105541 : term472 = term473.
Proof. exact (MK_COMB (@lem3105540) (@lem3105539)). Qed.
Lemma lem3105542 : term474 = term475.
Proof. exact (MK_COMB (@lem3105541) (@lem3105536)). Qed.
Lemma lem3105543 : term476.
Proof. exact (@lem1981473 term263 term224 term224 term224 term217 term224). Qed.
Lemma lem3105545 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105546 : term440 = term446.
Proof. exact (@lem3105545 (NUMERAL 0) term131). Qed.
Lemma lem3105547 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105548 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105549 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105548 h1) (fun h1 : term446 = True => @lem3105547)). Qed.
Lemma lem3105550 : term446 = True.
Proof. exact (EQ_MP (@lem3105549) (@lem3105547)). Qed.
Lemma lem3105551 : term440 = True.
Proof. exact (TRANS (@lem3105546) (@lem3105550)). Qed.
Lemma lem3105552 : True = term440.
Proof. exact (SYM (@lem3105551)). Qed.
Lemma lem3105553 : term440.
Proof. exact (EQ_MP (@lem3105552) (@lem0)). Qed.
Lemma lem3105554 : term477.
Proof. exact (@lem3105543 (@lem3105553)). Qed.
Lemma lem3105556 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105557 : term440 = term446.
Proof. exact (@lem3105556 (NUMERAL 0) term131). Qed.
Lemma lem3105558 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105559 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105560 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105559 h1) (fun h1 : term446 = True => @lem3105558)). Qed.
Lemma lem3105561 : term446 = True.
Proof. exact (EQ_MP (@lem3105560) (@lem3105558)). Qed.
Lemma lem3105562 : term440 = True.
Proof. exact (TRANS (@lem3105557) (@lem3105561)). Qed.
Lemma lem3105563 : True = term440.
Proof. exact (SYM (@lem3105562)). Qed.
Lemma lem3105564 : term440.
Proof. exact (EQ_MP (@lem3105563) (@lem0)). Qed.
Lemma lem3105565 : term478.
Proof. exact (@lem3105554 (@lem3105564)). Qed.
Lemma lem3105567 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105568 : term440 = term446.
Proof. exact (@lem3105567 (NUMERAL 0) term131). Qed.
Lemma lem3105569 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105570 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105571 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105570 h1) (fun h1 : term446 = True => @lem3105569)). Qed.
Lemma lem3105572 : term446 = True.
Proof. exact (EQ_MP (@lem3105571) (@lem3105569)). Qed.
Lemma lem3105573 : term440 = True.
Proof. exact (TRANS (@lem3105568) (@lem3105572)). Qed.
Lemma lem3105574 : True = term440.
Proof. exact (SYM (@lem3105573)). Qed.
Lemma lem3105575 : term440.
Proof. exact (EQ_MP (@lem3105574) (@lem0)). Qed.
Lemma lem3105576 : term479.
Proof. exact (@lem3105565 (@lem3105575)). Qed.
Lemma lem3105578 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3105579 : term272 = term273.
Proof. exact (@lem3105578 term131 term131). Qed.
Lemma lem3105580 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105581 : term275 = term131.
Proof. exact (EQ_MP (@lem3105580) (@lem940073)). Qed.
Lemma lem3105582 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105583 : term273 = term224.
Proof. exact (MK_COMB (@lem3105582) (@lem3105581)). Qed.
Lemma lem3105584 : term272 = term224.
Proof. exact (TRANS (@lem3105579) (@lem3105583)). Qed.
Lemma lem3105586 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3105587 : term288 = term293.
Proof. exact (@lem3105586 term131 term131). Qed.
Lemma lem3105588 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105589 : term275 = term131.
Proof. exact (EQ_MP (@lem3105588) (@lem940073)). Qed.
Lemma lem3105590 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105591 : term273 = term224.
Proof. exact (MK_COMB (@lem3105590) (@lem3105589)). Qed.
Lemma lem3105592 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3105593 : term293 = term263.
Proof. exact (MK_COMB (@lem3105592) (@lem3105591)). Qed.
Lemma lem3105594 : term288 = term263.
Proof. exact (TRANS (@lem3105587) (@lem3105593)). Qed.
Lemma lem3105595 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3105596 : term480 = term472.
Proof. exact (MK_COMB (@lem3105595) (@lem3105594)). Qed.
Lemma lem3105597 : term481 = term474.
Proof. exact (MK_COMB (@lem3105596) (@lem3105584)). Qed.
Lemma lem3105599 (m : nat) : (term482 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3105600 : term474 = term217.
Proof. exact (@lem3105599 term131). Qed.
Lemma lem3105601 : term481 = term217.
Proof. exact (TRANS (@lem3105597) (@lem3105600)). Qed.
Lemma lem3105602 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3105603 : term483 = term484.
Proof. exact (MK_COMB (@lem3105602) (@lem3105601)). Qed.
Lemma lem3105604 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem3105605 : term485 = term451.
Proof. exact (MK_COMB (@lem3105603) (@lem3105604)). Qed.
Lemma lem3105607 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3105608 : term451 = term217.
Proof. exact (@lem3105607 term131). Qed.
Lemma lem3105609 : term485 = term217.
Proof. exact (TRANS (@lem3105605) (@lem3105608)). Qed.
Lemma lem3105611 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3105612 : term272 = term273.
Proof. exact (@lem3105611 term131 term131). Qed.
Lemma lem3105613 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105614 : term275 = term131.
Proof. exact (EQ_MP (@lem3105613) (@lem940073)). Qed.
Lemma lem3105615 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105616 : term273 = term224.
Proof. exact (MK_COMB (@lem3105615) (@lem3105614)). Qed.
Lemma lem3105617 : term272 = term224.
Proof. exact (TRANS (@lem3105612) (@lem3105616)). Qed.
Lemma lem3105618 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem3105619 : term486 = term451.
Proof. exact (MK_COMB (@lem3105618) (@lem3105617)). Qed.
Lemma lem3105621 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3105622 : term451 = term217.
Proof. exact (@lem3105621 term131). Qed.
Lemma lem3105623 : term486 = term217.
Proof. exact (TRANS (@lem3105619) (@lem3105622)). Qed.
Lemma lem3105624 : term217 = term486.
Proof. exact (SYM (@lem3105623)). Qed.
Lemma lem3105625 : term485 = term486.
Proof. exact (TRANS (@lem3105609) (@lem3105624)). Qed.
Lemma lem3105626 : term475 = term260.
Proof. exact (@lem3105576 (@lem3105625)). Qed.
Lemma lem3105627 : term474 = term260.
Proof. exact (TRANS (@lem3105542) (@lem3105626)). Qed.
Lemma lem3105629 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3105630 : term260 = term217.
Proof. exact (@lem3105629 term217). Qed.
Lemma lem3105631 : term474 = term217.
Proof. exact (TRANS (@lem3105627) (@lem3105630)). Qed.
Lemma lem3105632 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3105633 : term487 = term484.
Proof. exact (MK_COMB (@lem3105632) (@lem3105631)). Qed.
Lemma lem3105634 (_32232 : int) : (real_of_int _32232) = (real_of_int _32232).
Proof. exact (eq_refl (real_of_int _32232)). Qed.
Lemma lem3105635 (_32232 : int) : (term471 _32232) = (term488 _32232).
Proof. exact (MK_COMB (@lem3105633) (@lem3105634 _32232)). Qed.
Lemma lem3105636 (_32232 : int) : (term493 _32232) = (term488 _32232).
Proof. exact (TRANS (@lem3105533 _32232) (@lem3105635 _32232)). Qed.
Lemma lem3105637 (_32232 : int) : (term488 _32232) = term217.
Proof. exact (@lem1982719 (real_of_int _32232)). Qed.
Lemma lem3105638 (_32232 : int) : (term493 _32232) = term217.
Proof. exact (TRANS (@lem3105636 _32232) (@lem3105637 _32232)). Qed.
Lemma lem3105639 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3105640 (_32232 : int) : (term494 _32232) = term490.
Proof. exact (MK_COMB (@lem3105639) (@lem3105638 _32232)). Qed.
Lemma lem3105641 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem3105642 (_32232 : int) : (term492 _32232) = term495.
Proof. exact (MK_COMB (@lem3105640 _32232) (@lem3105641)). Qed.
Lemma lem3105643 (_32232 : int) : (term491 _32232) = term495.
Proof. exact (TRANS (@lem3105532 _32232) (@lem3105642 _32232)). Qed.
Lemma lem3105644 : term495 = term263.
Proof. exact (@lem1982721 term263). Qed.
Lemma lem3105645 (_32232 : int) : (term491 _32232) = term263.
Proof. exact (TRANS (@lem3105643 _32232) (@lem3105644)). Qed.
Lemma lem3105646 (_32231 : int) (_32232 : int) : (term469 _32231 _32232) = term495.
Proof. exact (MK_COMB (@lem3105531 _32231) (@lem3105645 _32232)). Qed.
Lemma lem3105647 (_32231 : int) (_32232 : int) : (term468 _32231 _32232) = term495.
Proof. exact (TRANS (@lem3105423 _32231 _32232) (@lem3105646 _32231 _32232)). Qed.
Lemma lem3105648 : term495 = term263.
Proof. exact (@lem1982721 term263). Qed.
Lemma lem3105649 (_32231 : int) (_32232 : int) : (term468 _32231 _32232) = term263.
Proof. exact (TRANS (@lem3105647 _32231 _32232) (@lem3105648)). Qed.
Lemma lem3105650 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3105651 (_32231 : int) (_32232 : int) : (term496 _32231 _32232) = term497.
Proof. exact (MK_COMB (@lem3105650) (@lem3105649 _32231 _32232)). Qed.
Lemma lem3105652 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3105653 (_32231 : int) (_32232 : int) : (term467 _32231 _32232) = term498.
Proof. exact (MK_COMB (@lem3105651 _32231 _32232) (@lem3105652)). Qed.
Lemma lem3105654 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : term498.
Proof. exact (EQ_MP (@lem3105653 _32231 _32232) (@lem3105422 _32231 _32232 h1)). Qed.
Lemma lem3105656 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3105657 : term498 = term499.
Proof. exact (@lem3105656 term217 term263). Qed.
Lemma lem3105659 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3105660 : term263 = term264.
Proof. exact (@lem3105659 term131). Qed.
Lemma lem3105662 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3105663 : term217 = term260.
Proof. exact (@lem3105662 (NUMERAL 0)). Qed.
Lemma lem3105664 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3105665 : term219 = term500.
Proof. exact (MK_COMB (@lem3105664) (@lem3105663)). Qed.
Lemma lem3105666 : term499 = term501.
Proof. exact (MK_COMB (@lem3105665) (@lem3105660)). Qed.
Lemma lem3105667 : term502.
Proof. exact (@lem1980026 term217 term224 term263 term224). Qed.
Lemma lem3105669 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105670 : term440 = term446.
Proof. exact (@lem3105669 (NUMERAL 0) term131). Qed.
Lemma lem3105671 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105672 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105673 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105672 h1) (fun h1 : term446 = True => @lem3105671)). Qed.
Lemma lem3105674 : term446 = True.
Proof. exact (EQ_MP (@lem3105673) (@lem3105671)). Qed.
Lemma lem3105675 : term440 = True.
Proof. exact (TRANS (@lem3105670) (@lem3105674)). Qed.
Lemma lem3105676 : True = term440.
Proof. exact (SYM (@lem3105675)). Qed.
Lemma lem3105677 : term440.
Proof. exact (EQ_MP (@lem3105676) (@lem0)). Qed.
Lemma lem3105678 : term503.
Proof. exact (@lem3105667 (@lem3105677)). Qed.
Lemma lem3105680 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105681 : term440 = term446.
Proof. exact (@lem3105680 (NUMERAL 0) term131). Qed.
Lemma lem3105682 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105683 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105684 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105683 h1) (fun h1 : term446 = True => @lem3105682)). Qed.
Lemma lem3105685 : term446 = True.
Proof. exact (EQ_MP (@lem3105684) (@lem3105682)). Qed.
Lemma lem3105686 : term440 = True.
Proof. exact (TRANS (@lem3105681) (@lem3105685)). Qed.
Lemma lem3105687 : True = term440.
Proof. exact (SYM (@lem3105686)). Qed.
Lemma lem3105688 : term440.
Proof. exact (EQ_MP (@lem3105687) (@lem0)). Qed.
Lemma lem3105689 : term501 = term504.
Proof. exact (@lem3105678 (@lem3105688)). Qed.
Lemma lem3105691 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3105692 : term288 = term293.
Proof. exact (@lem3105691 term131 term131). Qed.
Lemma lem3105693 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105694 : term275 = term131.
Proof. exact (EQ_MP (@lem3105693) (@lem940073)). Qed.
Lemma lem3105695 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105696 : term273 = term224.
Proof. exact (MK_COMB (@lem3105695) (@lem3105694)). Qed.
Lemma lem3105697 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3105698 : term293 = term263.
Proof. exact (MK_COMB (@lem3105697) (@lem3105696)). Qed.
Lemma lem3105699 : term288 = term263.
Proof. exact (TRANS (@lem3105692) (@lem3105698)). Qed.
Lemma lem3105701 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3105702 : term451 = term217.
Proof. exact (@lem3105701 term131). Qed.
Lemma lem3105703 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3105704 : term505 = term219.
Proof. exact (MK_COMB (@lem3105703) (@lem3105702)). Qed.
Lemma lem3105705 : term504 = term499.
Proof. exact (MK_COMB (@lem3105704) (@lem3105699)). Qed.
Lemma lem3105707 (m : nat) (n : nat) : (term506 m n) = (term507 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3105708 : term499 = term508.
Proof. exact (@lem3105707 (NUMERAL 0) term131). Qed.
Lemma lem3105709 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105710 (h1 : term447 = (BIT1 0)) : (term131 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3105711 : (term447 = (BIT1 0)) = ((term131 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105710 h1) (fun h1 : (term131 = (NUMERAL 0)) = False => @lem3105709)). Qed.
Lemma lem3105712 : (term131 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3105711) (@lem3105709)). Qed.
Lemma lem3105713 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3105714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3105715 : term509 = (and True).
Proof. exact (MK_COMB (@lem3105714) (@lem3105713)). Qed.
Lemma lem3105716 : term508 = (True /\ False).
Proof. exact (MK_COMB (@lem3105715) (@lem3105712)). Qed.
Lemma lem3105718 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3105719 : term508 = False.
Proof. exact (TRANS (@lem3105716) (@lem3105718)). Qed.
Lemma lem3105720 : term499 = False.
Proof. exact (TRANS (@lem3105708) (@lem3105719)). Qed.
Lemma lem3105721 : term504 = False.
Proof. exact (TRANS (@lem3105705) (@lem3105720)). Qed.
Lemma lem3105722 : term501 = False.
Proof. exact (TRANS (@lem3105689) (@lem3105721)). Qed.
Lemma lem3105723 : term499 = False.
Proof. exact (TRANS (@lem3105666) (@lem3105722)). Qed.
Lemma lem3105724 : term498 = False.
Proof. exact (TRANS (@lem3105657) (@lem3105723)). Qed.
Lemma lem3105725 (_32231 : int) (_32232 : int) (h1 : term438 _32231 _32232) : False.
Proof. exact (EQ_MP (@lem3105724) (@lem3105654 _32231 _32232 h1)). Qed.
Lemma lem3105726 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term510 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3105727 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term431 _32231 _32232.
Proof. exact (proj2 (@lem3105726 _32231 _32232 h1)). Qed.
Lemma lem3105729 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term400 _32231 _32232.
Proof. exact (proj2 (@lem3105727 _32231 _32232 h1)). Qed.
Lemma lem3105731 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term364 _32231 _32232.
Proof. exact (proj2 (@lem3105729 _32231 _32232 h1)). Qed.
Lemma lem3105732 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : (real_of_int _32231) = term217.
Proof. exact (proj1 (@lem3105729 _32231 _32232 h1)). Qed.
Lemma lem3105734 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term315 _32231 _32232.
Proof. exact (proj1 (@lem3105731 _32231 _32232 h1)). Qed.
Lemma lem3105736 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term299 _32231.
Proof. exact (proj1 (@lem3105734 _32231 _32232 h1)). Qed.
Lemma lem3105738 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3105739 : term439 = term440.
Proof. exact (@lem3105738 term217 term224). Qed.
Lemma lem3105741 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3105742 : term224 = term287.
Proof. exact (@lem3105741 term131). Qed.
Lemma lem3105744 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3105745 : term217 = term260.
Proof. exact (@lem3105744 (NUMERAL 0)). Qed.
Lemma lem3105746 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3105747 : term441 = term442.
Proof. exact (MK_COMB (@lem3105746) (@lem3105745)). Qed.
Lemma lem3105748 : term440 = term443.
Proof. exact (MK_COMB (@lem3105747) (@lem3105742)). Qed.
Lemma lem3105749 : term444.
Proof. exact (@lem1980255 term217 term224 term224 term224). Qed.
Lemma lem3105751 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105752 : term440 = term446.
Proof. exact (@lem3105751 (NUMERAL 0) term131). Qed.
Lemma lem3105753 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105754 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105755 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105754 h1) (fun h1 : term446 = True => @lem3105753)). Qed.
Lemma lem3105756 : term446 = True.
Proof. exact (EQ_MP (@lem3105755) (@lem3105753)). Qed.
Lemma lem3105757 : term440 = True.
Proof. exact (TRANS (@lem3105752) (@lem3105756)). Qed.
Lemma lem3105758 : True = term440.
Proof. exact (SYM (@lem3105757)). Qed.
Lemma lem3105759 : term440.
Proof. exact (EQ_MP (@lem3105758) (@lem0)). Qed.
Lemma lem3105760 : term448.
Proof. exact (@lem3105749 (@lem3105759)). Qed.
Lemma lem3105762 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105763 : term440 = term446.
Proof. exact (@lem3105762 (NUMERAL 0) term131). Qed.
Lemma lem3105764 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105765 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105766 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105765 h1) (fun h1 : term446 = True => @lem3105764)). Qed.
Lemma lem3105767 : term446 = True.
Proof. exact (EQ_MP (@lem3105766) (@lem3105764)). Qed.
Lemma lem3105768 : term440 = True.
Proof. exact (TRANS (@lem3105763) (@lem3105767)). Qed.
Lemma lem3105769 : True = term440.
Proof. exact (SYM (@lem3105768)). Qed.
Lemma lem3105770 : term440.
Proof. exact (EQ_MP (@lem3105769) (@lem0)). Qed.
Lemma lem3105771 : term443 = term449.
Proof. exact (@lem3105760 (@lem3105770)). Qed.
Lemma lem3105773 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3105774 : term272 = term273.
Proof. exact (@lem3105773 term131 term131). Qed.
Lemma lem3105775 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105776 : term275 = term131.
Proof. exact (EQ_MP (@lem3105775) (@lem940073)). Qed.
Lemma lem3105777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105778 : term273 = term224.
Proof. exact (MK_COMB (@lem3105777) (@lem3105776)). Qed.
Lemma lem3105779 : term272 = term224.
Proof. exact (TRANS (@lem3105774) (@lem3105778)). Qed.
Lemma lem3105781 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3105782 : term451 = term217.
Proof. exact (@lem3105781 term131). Qed.
Lemma lem3105783 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3105784 : term452 = term441.
Proof. exact (MK_COMB (@lem3105783) (@lem3105782)). Qed.
Lemma lem3105785 : term449 = term440.
Proof. exact (MK_COMB (@lem3105784) (@lem3105779)). Qed.
Lemma lem3105787 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105788 : term440 = term446.
Proof. exact (@lem3105787 (NUMERAL 0) term131). Qed.
Lemma lem3105789 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105790 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105791 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105790 h1) (fun h1 : term446 = True => @lem3105789)). Qed.
Lemma lem3105792 : term446 = True.
Proof. exact (EQ_MP (@lem3105791) (@lem3105789)). Qed.
Lemma lem3105793 : term440 = True.
Proof. exact (TRANS (@lem3105788) (@lem3105792)). Qed.
Lemma lem3105794 : term449 = True.
Proof. exact (TRANS (@lem3105785) (@lem3105793)). Qed.
Lemma lem3105795 : term443 = True.
Proof. exact (TRANS (@lem3105771) (@lem3105794)). Qed.
Lemma lem3105796 : term440 = True.
Proof. exact (TRANS (@lem3105748) (@lem3105795)). Qed.
Lemma lem3105797 : term439 = True.
Proof. exact (TRANS (@lem3105739) (@lem3105796)). Qed.
Lemma lem3105798 : True = term439.
Proof. exact (SYM (@lem3105797)). Qed.
Lemma lem3105799 : term439.
Proof. exact (EQ_MP (@lem3105798) (@lem0)). Qed.
Lemma lem3105800 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term511 _32231.
Proof. exact (conj (@lem3105799) (@lem3105736 _32231 _32232 h1)). Qed.
Lemma lem3105802 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3105803 (_32231 : int) : term512 _32231.
Proof. exact (@lem3105802 term224 (term296 _32231)). Qed.
Lemma lem3105804 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term513 _32231.
Proof. exact (@lem3105803 _32231 (@lem3105800 _32231 _32232 h1)). Qed.
Lemma lem3105805 (_32231 : int) : (term514 _32231) = (term296 _32231).
Proof. exact (@lem1982733 (term296 _32231)). Qed.
Lemma lem3105806 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3105807 (_32231 : int) : (term515 _32231) = (term298 _32231).
Proof. exact (MK_COMB (@lem3105806) (@lem3105805 _32231)). Qed.
Lemma lem3105808 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3105809 (_32231 : int) : (term513 _32231) = (term299 _32231).
Proof. exact (MK_COMB (@lem3105807 _32231) (@lem3105808)). Qed.
Lemma lem3105810 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term299 _32231.
Proof. exact (EQ_MP (@lem3105809 _32231) (@lem3105804 _32231 _32232 h1)). Qed.
Lemma lem3105812 (y : real) : term516 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3105813 (_32231 : int) : term517 _32231.
Proof. exact (@lem3105812 (real_of_int _32231)). Qed.
Lemma lem3105814 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term518 _32231.
Proof. exact (@lem3105813 _32231 (@lem3105732 _32231 _32232 h1)). Qed.
Lemma lem3105815 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term519 _32231.
Proof. exact (@lem3105814 _32231 _32232 h1 term263). Qed.
Lemma lem3105816 (_32231 : int) : (term519 _32231) = ((term312 _32231) = term217).
Proof. exact (eq_refl (term519 _32231)). Qed.
Lemma lem3105823 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : (term312 _32231) = term217.
Proof. exact (EQ_MP (@lem3105816 _32231) (@lem3105815 _32231 _32232 h1)). Qed.
Lemma lem3105824 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term520 _32231.
Proof. exact (conj (@lem3105823 _32231 _32232 h1) (@lem3105810 _32231 _32232 h1)). Qed.
Lemma lem3105826 (x : real) (y : real) : term521 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3105827 (_32231 : int) : term522 _32231.
Proof. exact (@lem3105826 (term312 _32231) (term296 _32231)). Qed.
Lemma lem3105828 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term523 _32231.
Proof. exact (@lem3105827 _32231 (@lem3105824 _32231 _32232 h1)). Qed.
Lemma lem3105829 (_32231 : int) : (term491 _32231) = (term492 _32231).
Proof. exact (@lem1982763 (term312 _32231) (real_of_int _32231) term263). Qed.
Lemma lem3105830 (_32231 : int) : (term493 _32231) = (term471 _32231).
Proof. exact (@lem1982713 term263 (real_of_int _32231)). Qed.
Lemma lem3105832 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3105833 : term224 = term287.
Proof. exact (@lem3105832 term131). Qed.
Lemma lem3105835 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3105836 : term263 = term264.
Proof. exact (@lem3105835 term131). Qed.
Lemma lem3105837 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3105838 : term472 = term473.
Proof. exact (MK_COMB (@lem3105837) (@lem3105836)). Qed.
Lemma lem3105839 : term474 = term475.
Proof. exact (MK_COMB (@lem3105838) (@lem3105833)). Qed.
Lemma lem3105840 : term476.
Proof. exact (@lem1981473 term263 term224 term224 term224 term217 term224). Qed.
Lemma lem3105842 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105843 : term440 = term446.
Proof. exact (@lem3105842 (NUMERAL 0) term131). Qed.
Lemma lem3105844 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105845 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105846 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105845 h1) (fun h1 : term446 = True => @lem3105844)). Qed.
Lemma lem3105847 : term446 = True.
Proof. exact (EQ_MP (@lem3105846) (@lem3105844)). Qed.
Lemma lem3105848 : term440 = True.
Proof. exact (TRANS (@lem3105843) (@lem3105847)). Qed.
Lemma lem3105849 : True = term440.
Proof. exact (SYM (@lem3105848)). Qed.
Lemma lem3105850 : term440.
Proof. exact (EQ_MP (@lem3105849) (@lem0)). Qed.
Lemma lem3105851 : term477.
Proof. exact (@lem3105840 (@lem3105850)). Qed.
Lemma lem3105853 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105854 : term440 = term446.
Proof. exact (@lem3105853 (NUMERAL 0) term131). Qed.
Lemma lem3105855 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105856 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105857 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105856 h1) (fun h1 : term446 = True => @lem3105855)). Qed.
Lemma lem3105858 : term446 = True.
Proof. exact (EQ_MP (@lem3105857) (@lem3105855)). Qed.
Lemma lem3105859 : term440 = True.
Proof. exact (TRANS (@lem3105854) (@lem3105858)). Qed.
Lemma lem3105860 : True = term440.
Proof. exact (SYM (@lem3105859)). Qed.
Lemma lem3105861 : term440.
Proof. exact (EQ_MP (@lem3105860) (@lem0)). Qed.
Lemma lem3105862 : term478.
Proof. exact (@lem3105851 (@lem3105861)). Qed.
Lemma lem3105864 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105865 : term440 = term446.
Proof. exact (@lem3105864 (NUMERAL 0) term131). Qed.
Lemma lem3105866 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105867 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105868 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105867 h1) (fun h1 : term446 = True => @lem3105866)). Qed.
Lemma lem3105869 : term446 = True.
Proof. exact (EQ_MP (@lem3105868) (@lem3105866)). Qed.
Lemma lem3105870 : term440 = True.
Proof. exact (TRANS (@lem3105865) (@lem3105869)). Qed.
Lemma lem3105871 : True = term440.
Proof. exact (SYM (@lem3105870)). Qed.
Lemma lem3105872 : term440.
Proof. exact (EQ_MP (@lem3105871) (@lem0)). Qed.
Lemma lem3105873 : term479.
Proof. exact (@lem3105862 (@lem3105872)). Qed.
Lemma lem3105875 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3105876 : term272 = term273.
Proof. exact (@lem3105875 term131 term131). Qed.
Lemma lem3105877 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105878 : term275 = term131.
Proof. exact (EQ_MP (@lem3105877) (@lem940073)). Qed.
Lemma lem3105879 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105880 : term273 = term224.
Proof. exact (MK_COMB (@lem3105879) (@lem3105878)). Qed.
Lemma lem3105881 : term272 = term224.
Proof. exact (TRANS (@lem3105876) (@lem3105880)). Qed.
Lemma lem3105883 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3105884 : term288 = term293.
Proof. exact (@lem3105883 term131 term131). Qed.
Lemma lem3105885 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105886 : term275 = term131.
Proof. exact (EQ_MP (@lem3105885) (@lem940073)). Qed.
Lemma lem3105887 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105888 : term273 = term224.
Proof. exact (MK_COMB (@lem3105887) (@lem3105886)). Qed.
Lemma lem3105889 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3105890 : term293 = term263.
Proof. exact (MK_COMB (@lem3105889) (@lem3105888)). Qed.
Lemma lem3105891 : term288 = term263.
Proof. exact (TRANS (@lem3105884) (@lem3105890)). Qed.
Lemma lem3105892 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3105893 : term480 = term472.
Proof. exact (MK_COMB (@lem3105892) (@lem3105891)). Qed.
Lemma lem3105894 : term481 = term474.
Proof. exact (MK_COMB (@lem3105893) (@lem3105881)). Qed.
Lemma lem3105896 (m : nat) : (term482 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3105897 : term474 = term217.
Proof. exact (@lem3105896 term131). Qed.
Lemma lem3105898 : term481 = term217.
Proof. exact (TRANS (@lem3105894) (@lem3105897)). Qed.
Lemma lem3105899 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3105900 : term483 = term484.
Proof. exact (MK_COMB (@lem3105899) (@lem3105898)). Qed.
Lemma lem3105901 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem3105902 : term485 = term451.
Proof. exact (MK_COMB (@lem3105900) (@lem3105901)). Qed.
Lemma lem3105904 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3105905 : term451 = term217.
Proof. exact (@lem3105904 term131). Qed.
Lemma lem3105906 : term485 = term217.
Proof. exact (TRANS (@lem3105902) (@lem3105905)). Qed.
Lemma lem3105908 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3105909 : term272 = term273.
Proof. exact (@lem3105908 term131 term131). Qed.
Lemma lem3105910 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105911 : term275 = term131.
Proof. exact (EQ_MP (@lem3105910) (@lem940073)). Qed.
Lemma lem3105912 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105913 : term273 = term224.
Proof. exact (MK_COMB (@lem3105912) (@lem3105911)). Qed.
Lemma lem3105914 : term272 = term224.
Proof. exact (TRANS (@lem3105909) (@lem3105913)). Qed.
Lemma lem3105915 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem3105916 : term486 = term451.
Proof. exact (MK_COMB (@lem3105915) (@lem3105914)). Qed.
Lemma lem3105918 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3105919 : term451 = term217.
Proof. exact (@lem3105918 term131). Qed.
Lemma lem3105920 : term486 = term217.
Proof. exact (TRANS (@lem3105916) (@lem3105919)). Qed.
Lemma lem3105921 : term217 = term486.
Proof. exact (SYM (@lem3105920)). Qed.
Lemma lem3105922 : term485 = term486.
Proof. exact (TRANS (@lem3105906) (@lem3105921)). Qed.
Lemma lem3105923 : term475 = term260.
Proof. exact (@lem3105873 (@lem3105922)). Qed.
Lemma lem3105924 : term474 = term260.
Proof. exact (TRANS (@lem3105839) (@lem3105923)). Qed.
Lemma lem3105926 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3105927 : term260 = term217.
Proof. exact (@lem3105926 term217). Qed.
Lemma lem3105928 : term474 = term217.
Proof. exact (TRANS (@lem3105924) (@lem3105927)). Qed.
Lemma lem3105929 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3105930 : term487 = term484.
Proof. exact (MK_COMB (@lem3105929) (@lem3105928)). Qed.
Lemma lem3105931 (_32231 : int) : (real_of_int _32231) = (real_of_int _32231).
Proof. exact (eq_refl (real_of_int _32231)). Qed.
Lemma lem3105932 (_32231 : int) : (term471 _32231) = (term488 _32231).
Proof. exact (MK_COMB (@lem3105930) (@lem3105931 _32231)). Qed.
Lemma lem3105933 (_32231 : int) : (term493 _32231) = (term488 _32231).
Proof. exact (TRANS (@lem3105830 _32231) (@lem3105932 _32231)). Qed.
Lemma lem3105934 (_32231 : int) : (term488 _32231) = term217.
Proof. exact (@lem1982719 (real_of_int _32231)). Qed.
Lemma lem3105935 (_32231 : int) : (term493 _32231) = term217.
Proof. exact (TRANS (@lem3105933 _32231) (@lem3105934 _32231)). Qed.
Lemma lem3105936 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3105937 (_32231 : int) : (term494 _32231) = term490.
Proof. exact (MK_COMB (@lem3105936) (@lem3105935 _32231)). Qed.
Lemma lem3105938 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem3105939 (_32231 : int) : (term492 _32231) = term495.
Proof. exact (MK_COMB (@lem3105937 _32231) (@lem3105938)). Qed.
Lemma lem3105940 (_32231 : int) : (term491 _32231) = term495.
Proof. exact (TRANS (@lem3105829 _32231) (@lem3105939 _32231)). Qed.
Lemma lem3105941 : term495 = term263.
Proof. exact (@lem1982721 term263). Qed.
Lemma lem3105942 (_32231 : int) : (term491 _32231) = term263.
Proof. exact (TRANS (@lem3105940 _32231) (@lem3105941)). Qed.
Lemma lem3105943 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3105944 (_32231 : int) : (term524 _32231) = term497.
Proof. exact (MK_COMB (@lem3105943) (@lem3105942 _32231)). Qed.
Lemma lem3105945 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3105946 (_32231 : int) : (term523 _32231) = term498.
Proof. exact (MK_COMB (@lem3105944 _32231) (@lem3105945)). Qed.
Lemma lem3105947 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : term498.
Proof. exact (EQ_MP (@lem3105946 _32231) (@lem3105828 _32231 _32232 h1)). Qed.
Lemma lem3105949 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3105950 : term498 = term499.
Proof. exact (@lem3105949 term217 term263). Qed.
Lemma lem3105952 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3105953 : term263 = term264.
Proof. exact (@lem3105952 term131). Qed.
Lemma lem3105955 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3105956 : term217 = term260.
Proof. exact (@lem3105955 (NUMERAL 0)). Qed.
Lemma lem3105957 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3105958 : term219 = term500.
Proof. exact (MK_COMB (@lem3105957) (@lem3105956)). Qed.
Lemma lem3105959 : term499 = term501.
Proof. exact (MK_COMB (@lem3105958) (@lem3105953)). Qed.
Lemma lem3105960 : term502.
Proof. exact (@lem1980026 term217 term224 term263 term224). Qed.
Lemma lem3105962 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105963 : term440 = term446.
Proof. exact (@lem3105962 (NUMERAL 0) term131). Qed.
Lemma lem3105964 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105965 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105966 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105965 h1) (fun h1 : term446 = True => @lem3105964)). Qed.
Lemma lem3105967 : term446 = True.
Proof. exact (EQ_MP (@lem3105966) (@lem3105964)). Qed.
Lemma lem3105968 : term440 = True.
Proof. exact (TRANS (@lem3105963) (@lem3105967)). Qed.
Lemma lem3105969 : True = term440.
Proof. exact (SYM (@lem3105968)). Qed.
Lemma lem3105970 : term440.
Proof. exact (EQ_MP (@lem3105969) (@lem0)). Qed.
Lemma lem3105971 : term503.
Proof. exact (@lem3105960 (@lem3105970)). Qed.
Lemma lem3105973 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3105974 : term440 = term446.
Proof. exact (@lem3105973 (NUMERAL 0) term131). Qed.
Lemma lem3105975 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3105976 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3105977 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3105976 h1) (fun h1 : term446 = True => @lem3105975)). Qed.
Lemma lem3105978 : term446 = True.
Proof. exact (EQ_MP (@lem3105977) (@lem3105975)). Qed.
Lemma lem3105979 : term440 = True.
Proof. exact (TRANS (@lem3105974) (@lem3105978)). Qed.
Lemma lem3105980 : True = term440.
Proof. exact (SYM (@lem3105979)). Qed.
Lemma lem3105981 : term440.
Proof. exact (EQ_MP (@lem3105980) (@lem0)). Qed.
Lemma lem3105982 : term501 = term504.
Proof. exact (@lem3105971 (@lem3105981)). Qed.
Lemma lem3105984 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3105985 : term288 = term293.
Proof. exact (@lem3105984 term131 term131). Qed.
Lemma lem3105986 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3105987 : term275 = term131.
Proof. exact (EQ_MP (@lem3105986) (@lem940073)). Qed.
Lemma lem3105988 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3105989 : term273 = term224.
Proof. exact (MK_COMB (@lem3105988) (@lem3105987)). Qed.
Lemma lem3105990 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3105991 : term293 = term263.
Proof. exact (MK_COMB (@lem3105990) (@lem3105989)). Qed.
Lemma lem3105992 : term288 = term263.
Proof. exact (TRANS (@lem3105985) (@lem3105991)). Qed.
Lemma lem3105994 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3105995 : term451 = term217.
Proof. exact (@lem3105994 term131). Qed.
Lemma lem3105996 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3105997 : term505 = term219.
Proof. exact (MK_COMB (@lem3105996) (@lem3105995)). Qed.
Lemma lem3105998 : term504 = term499.
Proof. exact (MK_COMB (@lem3105997) (@lem3105992)). Qed.
Lemma lem3106000 (m : nat) (n : nat) : (term506 m n) = (term507 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3106001 : term499 = term508.
Proof. exact (@lem3106000 (NUMERAL 0) term131). Qed.
Lemma lem3106002 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106003 (h1 : term447 = (BIT1 0)) : (term131 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3106004 : (term447 = (BIT1 0)) = ((term131 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106003 h1) (fun h1 : (term131 = (NUMERAL 0)) = False => @lem3106002)). Qed.
Lemma lem3106005 : (term131 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3106004) (@lem3106002)). Qed.
Lemma lem3106006 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3106007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3106008 : term509 = (and True).
Proof. exact (MK_COMB (@lem3106007) (@lem3106006)). Qed.
Lemma lem3106009 : term508 = (True /\ False).
Proof. exact (MK_COMB (@lem3106008) (@lem3106005)). Qed.
Lemma lem3106011 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3106012 : term508 = False.
Proof. exact (TRANS (@lem3106009) (@lem3106011)). Qed.
Lemma lem3106013 : term499 = False.
Proof. exact (TRANS (@lem3106001) (@lem3106012)). Qed.
Lemma lem3106014 : term504 = False.
Proof. exact (TRANS (@lem3105998) (@lem3106013)). Qed.
Lemma lem3106015 : term501 = False.
Proof. exact (TRANS (@lem3105982) (@lem3106014)). Qed.
Lemma lem3106016 : term499 = False.
Proof. exact (TRANS (@lem3105959) (@lem3106015)). Qed.
Lemma lem3106017 : term498 = False.
Proof. exact (TRANS (@lem3105950) (@lem3106016)). Qed.
Lemma lem3106018 (_32231 : int) (_32232 : int) (h1 : term510 _32231 _32232) : False.
Proof. exact (EQ_MP (@lem3106017) (@lem3105947 _32231 _32232 h1)). Qed.
Lemma lem3106019 (_32231 : int) (_32232 : int) (h1 : term429 _32231 _32232) : False.
Proof. exact (or_elim (@lem3105256 _32231 _32232 h1) (fun h0 : term438 _32231 _32232 => @lem3105725 _32231 _32232 h0) (fun h0 : term510 _32231 _32232 => @lem3106018 _32231 _32232 h0)). Qed.
Lemma lem3106020 (_32231 : int) (_32232 : int) (h1 : term425 _32231 _32232) : term425 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3106021 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term525 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3106022 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term426 _32231 _32232.
Proof. exact (proj2 (@lem3106021 _32231 _32232 h1)). Qed.
Lemma lem3106024 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term395 _32231 _32232.
Proof. exact (proj2 (@lem3106022 _32231 _32232 h1)). Qed.
Lemma lem3106026 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term365 _32231 _32232.
Proof. exact (proj2 (@lem3106024 _32231 _32232 h1)). Qed.
Lemma lem3106027 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term307 _32231 _32232.
Proof. exact (proj1 (@lem3106024 _32231 _32232 h1)). Qed.
Lemma lem3106029 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term299 _32232.
Proof. exact (proj1 (@lem3106027 _32231 _32232 h1)). Qed.
Lemma lem3106031 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : (real_of_int _32232) = term217.
Proof. exact (proj1 (@lem3106026 _32231 _32232 h1)). Qed.
Lemma lem3106033 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3106034 : term439 = term440.
Proof. exact (@lem3106033 term217 term224). Qed.
Lemma lem3106036 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106037 : term224 = term287.
Proof. exact (@lem3106036 term131). Qed.
Lemma lem3106039 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106040 : term217 = term260.
Proof. exact (@lem3106039 (NUMERAL 0)). Qed.
Lemma lem3106041 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3106042 : term441 = term442.
Proof. exact (MK_COMB (@lem3106041) (@lem3106040)). Qed.
Lemma lem3106043 : term440 = term443.
Proof. exact (MK_COMB (@lem3106042) (@lem3106037)). Qed.
Lemma lem3106044 : term444.
Proof. exact (@lem1980255 term217 term224 term224 term224). Qed.
Lemma lem3106046 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106047 : term440 = term446.
Proof. exact (@lem3106046 (NUMERAL 0) term131). Qed.
Lemma lem3106048 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106049 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106050 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106049 h1) (fun h1 : term446 = True => @lem3106048)). Qed.
Lemma lem3106051 : term446 = True.
Proof. exact (EQ_MP (@lem3106050) (@lem3106048)). Qed.
Lemma lem3106052 : term440 = True.
Proof. exact (TRANS (@lem3106047) (@lem3106051)). Qed.
Lemma lem3106053 : True = term440.
Proof. exact (SYM (@lem3106052)). Qed.
Lemma lem3106054 : term440.
Proof. exact (EQ_MP (@lem3106053) (@lem0)). Qed.
Lemma lem3106055 : term448.
Proof. exact (@lem3106044 (@lem3106054)). Qed.
Lemma lem3106057 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106058 : term440 = term446.
Proof. exact (@lem3106057 (NUMERAL 0) term131). Qed.
Lemma lem3106059 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106060 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106061 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106060 h1) (fun h1 : term446 = True => @lem3106059)). Qed.
Lemma lem3106062 : term446 = True.
Proof. exact (EQ_MP (@lem3106061) (@lem3106059)). Qed.
Lemma lem3106063 : term440 = True.
Proof. exact (TRANS (@lem3106058) (@lem3106062)). Qed.
Lemma lem3106064 : True = term440.
Proof. exact (SYM (@lem3106063)). Qed.
Lemma lem3106065 : term440.
Proof. exact (EQ_MP (@lem3106064) (@lem0)). Qed.
Lemma lem3106066 : term443 = term449.
Proof. exact (@lem3106055 (@lem3106065)). Qed.
Lemma lem3106068 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3106069 : term272 = term273.
Proof. exact (@lem3106068 term131 term131). Qed.
Lemma lem3106070 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106071 : term275 = term131.
Proof. exact (EQ_MP (@lem3106070) (@lem940073)). Qed.
Lemma lem3106072 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106073 : term273 = term224.
Proof. exact (MK_COMB (@lem3106072) (@lem3106071)). Qed.
Lemma lem3106074 : term272 = term224.
Proof. exact (TRANS (@lem3106069) (@lem3106073)). Qed.
Lemma lem3106076 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106077 : term451 = term217.
Proof. exact (@lem3106076 term131). Qed.
Lemma lem3106078 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3106079 : term452 = term441.
Proof. exact (MK_COMB (@lem3106078) (@lem3106077)). Qed.
Lemma lem3106080 : term449 = term440.
Proof. exact (MK_COMB (@lem3106079) (@lem3106074)). Qed.
Lemma lem3106082 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106083 : term440 = term446.
Proof. exact (@lem3106082 (NUMERAL 0) term131). Qed.
Lemma lem3106084 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106085 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106086 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106085 h1) (fun h1 : term446 = True => @lem3106084)). Qed.
Lemma lem3106087 : term446 = True.
Proof. exact (EQ_MP (@lem3106086) (@lem3106084)). Qed.
Lemma lem3106088 : term440 = True.
Proof. exact (TRANS (@lem3106083) (@lem3106087)). Qed.
Lemma lem3106089 : term449 = True.
Proof. exact (TRANS (@lem3106080) (@lem3106088)). Qed.
Lemma lem3106090 : term443 = True.
Proof. exact (TRANS (@lem3106066) (@lem3106089)). Qed.
Lemma lem3106091 : term440 = True.
Proof. exact (TRANS (@lem3106043) (@lem3106090)). Qed.
Lemma lem3106092 : term439 = True.
Proof. exact (TRANS (@lem3106034) (@lem3106091)). Qed.
Lemma lem3106093 : True = term439.
Proof. exact (SYM (@lem3106092)). Qed.
Lemma lem3106094 : term439.
Proof. exact (EQ_MP (@lem3106093) (@lem0)). Qed.
Lemma lem3106095 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term511 _32232.
Proof. exact (conj (@lem3106094) (@lem3106029 _32231 _32232 h1)). Qed.
Lemma lem3106097 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3106098 (_32232 : int) : term512 _32232.
Proof. exact (@lem3106097 term224 (term296 _32232)). Qed.
Lemma lem3106099 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term513 _32232.
Proof. exact (@lem3106098 _32232 (@lem3106095 _32231 _32232 h1)). Qed.
Lemma lem3106100 (_32232 : int) : (term514 _32232) = (term296 _32232).
Proof. exact (@lem1982733 (term296 _32232)). Qed.
Lemma lem3106101 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3106102 (_32232 : int) : (term515 _32232) = (term298 _32232).
Proof. exact (MK_COMB (@lem3106101) (@lem3106100 _32232)). Qed.
Lemma lem3106103 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3106104 (_32232 : int) : (term513 _32232) = (term299 _32232).
Proof. exact (MK_COMB (@lem3106102 _32232) (@lem3106103)). Qed.
Lemma lem3106105 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term299 _32232.
Proof. exact (EQ_MP (@lem3106104 _32232) (@lem3106099 _32231 _32232 h1)). Qed.
Lemma lem3106107 (y : real) : term516 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3106108 (_32232 : int) : term517 _32232.
Proof. exact (@lem3106107 (real_of_int _32232)). Qed.
Lemma lem3106109 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term518 _32232.
Proof. exact (@lem3106108 _32232 (@lem3106031 _32231 _32232 h1)). Qed.
Lemma lem3106110 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term519 _32232.
Proof. exact (@lem3106109 _32231 _32232 h1 term263). Qed.
Lemma lem3106111 (_32232 : int) : (term519 _32232) = ((term312 _32232) = term217).
Proof. exact (eq_refl (term519 _32232)). Qed.
Lemma lem3106118 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : (term312 _32232) = term217.
Proof. exact (EQ_MP (@lem3106111 _32232) (@lem3106110 _32231 _32232 h1)). Qed.
Lemma lem3106119 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term520 _32232.
Proof. exact (conj (@lem3106118 _32231 _32232 h1) (@lem3106105 _32231 _32232 h1)). Qed.
Lemma lem3106121 (x : real) (y : real) : term521 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3106122 (_32232 : int) : term522 _32232.
Proof. exact (@lem3106121 (term312 _32232) (term296 _32232)). Qed.
Lemma lem3106123 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term523 _32232.
Proof. exact (@lem3106122 _32232 (@lem3106119 _32231 _32232 h1)). Qed.
Lemma lem3106124 (_32232 : int) : (term491 _32232) = (term492 _32232).
Proof. exact (@lem1982763 (term312 _32232) (real_of_int _32232) term263). Qed.
Lemma lem3106125 (_32232 : int) : (term493 _32232) = (term471 _32232).
Proof. exact (@lem1982713 term263 (real_of_int _32232)). Qed.
Lemma lem3106127 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106128 : term224 = term287.
Proof. exact (@lem3106127 term131). Qed.
Lemma lem3106130 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3106131 : term263 = term264.
Proof. exact (@lem3106130 term131). Qed.
Lemma lem3106132 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3106133 : term472 = term473.
Proof. exact (MK_COMB (@lem3106132) (@lem3106131)). Qed.
Lemma lem3106134 : term474 = term475.
Proof. exact (MK_COMB (@lem3106133) (@lem3106128)). Qed.
Lemma lem3106135 : term476.
Proof. exact (@lem1981473 term263 term224 term224 term224 term217 term224). Qed.
Lemma lem3106137 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106138 : term440 = term446.
Proof. exact (@lem3106137 (NUMERAL 0) term131). Qed.
Lemma lem3106139 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106140 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106141 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106140 h1) (fun h1 : term446 = True => @lem3106139)). Qed.
Lemma lem3106142 : term446 = True.
Proof. exact (EQ_MP (@lem3106141) (@lem3106139)). Qed.
Lemma lem3106143 : term440 = True.
Proof. exact (TRANS (@lem3106138) (@lem3106142)). Qed.
Lemma lem3106144 : True = term440.
Proof. exact (SYM (@lem3106143)). Qed.
Lemma lem3106145 : term440.
Proof. exact (EQ_MP (@lem3106144) (@lem0)). Qed.
Lemma lem3106146 : term477.
Proof. exact (@lem3106135 (@lem3106145)). Qed.
Lemma lem3106148 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106149 : term440 = term446.
Proof. exact (@lem3106148 (NUMERAL 0) term131). Qed.
Lemma lem3106150 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106151 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106152 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106151 h1) (fun h1 : term446 = True => @lem3106150)). Qed.
Lemma lem3106153 : term446 = True.
Proof. exact (EQ_MP (@lem3106152) (@lem3106150)). Qed.
Lemma lem3106154 : term440 = True.
Proof. exact (TRANS (@lem3106149) (@lem3106153)). Qed.
Lemma lem3106155 : True = term440.
Proof. exact (SYM (@lem3106154)). Qed.
Lemma lem3106156 : term440.
Proof. exact (EQ_MP (@lem3106155) (@lem0)). Qed.
Lemma lem3106157 : term478.
Proof. exact (@lem3106146 (@lem3106156)). Qed.
Lemma lem3106159 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106160 : term440 = term446.
Proof. exact (@lem3106159 (NUMERAL 0) term131). Qed.
Lemma lem3106161 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106162 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106163 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106162 h1) (fun h1 : term446 = True => @lem3106161)). Qed.
Lemma lem3106164 : term446 = True.
Proof. exact (EQ_MP (@lem3106163) (@lem3106161)). Qed.
Lemma lem3106165 : term440 = True.
Proof. exact (TRANS (@lem3106160) (@lem3106164)). Qed.
Lemma lem3106166 : True = term440.
Proof. exact (SYM (@lem3106165)). Qed.
Lemma lem3106167 : term440.
Proof. exact (EQ_MP (@lem3106166) (@lem0)). Qed.
Lemma lem3106168 : term479.
Proof. exact (@lem3106157 (@lem3106167)). Qed.
Lemma lem3106170 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3106171 : term272 = term273.
Proof. exact (@lem3106170 term131 term131). Qed.
Lemma lem3106172 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106173 : term275 = term131.
Proof. exact (EQ_MP (@lem3106172) (@lem940073)). Qed.
Lemma lem3106174 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106175 : term273 = term224.
Proof. exact (MK_COMB (@lem3106174) (@lem3106173)). Qed.
Lemma lem3106176 : term272 = term224.
Proof. exact (TRANS (@lem3106171) (@lem3106175)). Qed.
Lemma lem3106178 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3106179 : term288 = term293.
Proof. exact (@lem3106178 term131 term131). Qed.
Lemma lem3106180 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106181 : term275 = term131.
Proof. exact (EQ_MP (@lem3106180) (@lem940073)). Qed.
Lemma lem3106182 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106183 : term273 = term224.
Proof. exact (MK_COMB (@lem3106182) (@lem3106181)). Qed.
Lemma lem3106184 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3106185 : term293 = term263.
Proof. exact (MK_COMB (@lem3106184) (@lem3106183)). Qed.
Lemma lem3106186 : term288 = term263.
Proof. exact (TRANS (@lem3106179) (@lem3106185)). Qed.
Lemma lem3106187 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3106188 : term480 = term472.
Proof. exact (MK_COMB (@lem3106187) (@lem3106186)). Qed.
Lemma lem3106189 : term481 = term474.
Proof. exact (MK_COMB (@lem3106188) (@lem3106176)). Qed.
Lemma lem3106191 (m : nat) : (term482 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3106192 : term474 = term217.
Proof. exact (@lem3106191 term131). Qed.
Lemma lem3106193 : term481 = term217.
Proof. exact (TRANS (@lem3106189) (@lem3106192)). Qed.
Lemma lem3106194 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3106195 : term483 = term484.
Proof. exact (MK_COMB (@lem3106194) (@lem3106193)). Qed.
Lemma lem3106196 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem3106197 : term485 = term451.
Proof. exact (MK_COMB (@lem3106195) (@lem3106196)). Qed.
Lemma lem3106199 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106200 : term451 = term217.
Proof. exact (@lem3106199 term131). Qed.
Lemma lem3106201 : term485 = term217.
Proof. exact (TRANS (@lem3106197) (@lem3106200)). Qed.
Lemma lem3106203 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3106204 : term272 = term273.
Proof. exact (@lem3106203 term131 term131). Qed.
Lemma lem3106205 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106206 : term275 = term131.
Proof. exact (EQ_MP (@lem3106205) (@lem940073)). Qed.
Lemma lem3106207 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106208 : term273 = term224.
Proof. exact (MK_COMB (@lem3106207) (@lem3106206)). Qed.
Lemma lem3106209 : term272 = term224.
Proof. exact (TRANS (@lem3106204) (@lem3106208)). Qed.
Lemma lem3106210 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem3106211 : term486 = term451.
Proof. exact (MK_COMB (@lem3106210) (@lem3106209)). Qed.
Lemma lem3106213 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106214 : term451 = term217.
Proof. exact (@lem3106213 term131). Qed.
Lemma lem3106215 : term486 = term217.
Proof. exact (TRANS (@lem3106211) (@lem3106214)). Qed.
Lemma lem3106216 : term217 = term486.
Proof. exact (SYM (@lem3106215)). Qed.
Lemma lem3106217 : term485 = term486.
Proof. exact (TRANS (@lem3106201) (@lem3106216)). Qed.
Lemma lem3106218 : term475 = term260.
Proof. exact (@lem3106168 (@lem3106217)). Qed.
Lemma lem3106219 : term474 = term260.
Proof. exact (TRANS (@lem3106134) (@lem3106218)). Qed.
Lemma lem3106221 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3106222 : term260 = term217.
Proof. exact (@lem3106221 term217). Qed.
Lemma lem3106223 : term474 = term217.
Proof. exact (TRANS (@lem3106219) (@lem3106222)). Qed.
Lemma lem3106224 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3106225 : term487 = term484.
Proof. exact (MK_COMB (@lem3106224) (@lem3106223)). Qed.
Lemma lem3106226 (_32232 : int) : (real_of_int _32232) = (real_of_int _32232).
Proof. exact (eq_refl (real_of_int _32232)). Qed.
Lemma lem3106227 (_32232 : int) : (term471 _32232) = (term488 _32232).
Proof. exact (MK_COMB (@lem3106225) (@lem3106226 _32232)). Qed.
Lemma lem3106228 (_32232 : int) : (term493 _32232) = (term488 _32232).
Proof. exact (TRANS (@lem3106125 _32232) (@lem3106227 _32232)). Qed.
Lemma lem3106229 (_32232 : int) : (term488 _32232) = term217.
Proof. exact (@lem1982719 (real_of_int _32232)). Qed.
Lemma lem3106230 (_32232 : int) : (term493 _32232) = term217.
Proof. exact (TRANS (@lem3106228 _32232) (@lem3106229 _32232)). Qed.
Lemma lem3106231 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3106232 (_32232 : int) : (term494 _32232) = term490.
Proof. exact (MK_COMB (@lem3106231) (@lem3106230 _32232)). Qed.
Lemma lem3106233 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem3106234 (_32232 : int) : (term492 _32232) = term495.
Proof. exact (MK_COMB (@lem3106232 _32232) (@lem3106233)). Qed.
Lemma lem3106235 (_32232 : int) : (term491 _32232) = term495.
Proof. exact (TRANS (@lem3106124 _32232) (@lem3106234 _32232)). Qed.
Lemma lem3106236 : term495 = term263.
Proof. exact (@lem1982721 term263). Qed.
Lemma lem3106237 (_32232 : int) : (term491 _32232) = term263.
Proof. exact (TRANS (@lem3106235 _32232) (@lem3106236)). Qed.
Lemma lem3106238 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3106239 (_32232 : int) : (term524 _32232) = term497.
Proof. exact (MK_COMB (@lem3106238) (@lem3106237 _32232)). Qed.
Lemma lem3106240 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3106241 (_32232 : int) : (term523 _32232) = term498.
Proof. exact (MK_COMB (@lem3106239 _32232) (@lem3106240)). Qed.
Lemma lem3106242 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : term498.
Proof. exact (EQ_MP (@lem3106241 _32232) (@lem3106123 _32231 _32232 h1)). Qed.
Lemma lem3106244 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3106245 : term498 = term499.
Proof. exact (@lem3106244 term217 term263). Qed.
Lemma lem3106247 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3106248 : term263 = term264.
Proof. exact (@lem3106247 term131). Qed.
Lemma lem3106250 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106251 : term217 = term260.
Proof. exact (@lem3106250 (NUMERAL 0)). Qed.
Lemma lem3106252 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3106253 : term219 = term500.
Proof. exact (MK_COMB (@lem3106252) (@lem3106251)). Qed.
Lemma lem3106254 : term499 = term501.
Proof. exact (MK_COMB (@lem3106253) (@lem3106248)). Qed.
Lemma lem3106255 : term502.
Proof. exact (@lem1980026 term217 term224 term263 term224). Qed.
Lemma lem3106257 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106258 : term440 = term446.
Proof. exact (@lem3106257 (NUMERAL 0) term131). Qed.
Lemma lem3106259 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106260 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106261 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106260 h1) (fun h1 : term446 = True => @lem3106259)). Qed.
Lemma lem3106262 : term446 = True.
Proof. exact (EQ_MP (@lem3106261) (@lem3106259)). Qed.
Lemma lem3106263 : term440 = True.
Proof. exact (TRANS (@lem3106258) (@lem3106262)). Qed.
Lemma lem3106264 : True = term440.
Proof. exact (SYM (@lem3106263)). Qed.
Lemma lem3106265 : term440.
Proof. exact (EQ_MP (@lem3106264) (@lem0)). Qed.
Lemma lem3106266 : term503.
Proof. exact (@lem3106255 (@lem3106265)). Qed.
Lemma lem3106268 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106269 : term440 = term446.
Proof. exact (@lem3106268 (NUMERAL 0) term131). Qed.
Lemma lem3106270 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106271 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106272 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106271 h1) (fun h1 : term446 = True => @lem3106270)). Qed.
Lemma lem3106273 : term446 = True.
Proof. exact (EQ_MP (@lem3106272) (@lem3106270)). Qed.
Lemma lem3106274 : term440 = True.
Proof. exact (TRANS (@lem3106269) (@lem3106273)). Qed.
Lemma lem3106275 : True = term440.
Proof. exact (SYM (@lem3106274)). Qed.
Lemma lem3106276 : term440.
Proof. exact (EQ_MP (@lem3106275) (@lem0)). Qed.
Lemma lem3106277 : term501 = term504.
Proof. exact (@lem3106266 (@lem3106276)). Qed.
Lemma lem3106279 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3106280 : term288 = term293.
Proof. exact (@lem3106279 term131 term131). Qed.
Lemma lem3106281 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106282 : term275 = term131.
Proof. exact (EQ_MP (@lem3106281) (@lem940073)). Qed.
Lemma lem3106283 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106284 : term273 = term224.
Proof. exact (MK_COMB (@lem3106283) (@lem3106282)). Qed.
Lemma lem3106285 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3106286 : term293 = term263.
Proof. exact (MK_COMB (@lem3106285) (@lem3106284)). Qed.
Lemma lem3106287 : term288 = term263.
Proof. exact (TRANS (@lem3106280) (@lem3106286)). Qed.
Lemma lem3106289 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106290 : term451 = term217.
Proof. exact (@lem3106289 term131). Qed.
Lemma lem3106291 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3106292 : term505 = term219.
Proof. exact (MK_COMB (@lem3106291) (@lem3106290)). Qed.
Lemma lem3106293 : term504 = term499.
Proof. exact (MK_COMB (@lem3106292) (@lem3106287)). Qed.
Lemma lem3106295 (m : nat) (n : nat) : (term506 m n) = (term507 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3106296 : term499 = term508.
Proof. exact (@lem3106295 (NUMERAL 0) term131). Qed.
Lemma lem3106297 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106298 (h1 : term447 = (BIT1 0)) : (term131 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3106299 : (term447 = (BIT1 0)) = ((term131 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106298 h1) (fun h1 : (term131 = (NUMERAL 0)) = False => @lem3106297)). Qed.
Lemma lem3106300 : (term131 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3106299) (@lem3106297)). Qed.
Lemma lem3106301 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3106302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3106303 : term509 = (and True).
Proof. exact (MK_COMB (@lem3106302) (@lem3106301)). Qed.
Lemma lem3106304 : term508 = (True /\ False).
Proof. exact (MK_COMB (@lem3106303) (@lem3106300)). Qed.
Lemma lem3106306 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3106307 : term508 = False.
Proof. exact (TRANS (@lem3106304) (@lem3106306)). Qed.
Lemma lem3106308 : term499 = False.
Proof. exact (TRANS (@lem3106296) (@lem3106307)). Qed.
Lemma lem3106309 : term504 = False.
Proof. exact (TRANS (@lem3106293) (@lem3106308)). Qed.
Lemma lem3106310 : term501 = False.
Proof. exact (TRANS (@lem3106277) (@lem3106309)). Qed.
Lemma lem3106311 : term499 = False.
Proof. exact (TRANS (@lem3106254) (@lem3106310)). Qed.
Lemma lem3106312 : term498 = False.
Proof. exact (TRANS (@lem3106245) (@lem3106311)). Qed.
Lemma lem3106313 (_32231 : int) (_32232 : int) (h1 : term525 _32231 _32232) : False.
Proof. exact (EQ_MP (@lem3106312) (@lem3106242 _32231 _32232 h1)). Qed.
Lemma lem3106314 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term526 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3106315 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term427 _32231 _32232.
Proof. exact (proj2 (@lem3106314 _32231 _32232 h1)). Qed.
Lemma lem3106317 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term396 _32231 _32232.
Proof. exact (proj2 (@lem3106315 _32231 _32232 h1)). Qed.
Lemma lem3106319 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term365 _32231 _32232.
Proof. exact (proj2 (@lem3106317 _32231 _32232 h1)). Qed.
Lemma lem3106320 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : (real_of_int _32231) = term217.
Proof. exact (proj1 (@lem3106317 _32231 _32232 h1)). Qed.
Lemma lem3106321 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term329 _32231 _32232.
Proof. exact (proj2 (@lem3106319 _32231 _32232 h1)). Qed.
Lemma lem3106322 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : (real_of_int _32232) = term217.
Proof. exact (proj1 (@lem3106319 _32231 _32232 h1)). Qed.
Lemma lem3106324 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3106325 : term439 = term440.
Proof. exact (@lem3106324 term217 term224). Qed.
Lemma lem3106327 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106328 : term224 = term287.
Proof. exact (@lem3106327 term131). Qed.
Lemma lem3106330 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106331 : term217 = term260.
Proof. exact (@lem3106330 (NUMERAL 0)). Qed.
Lemma lem3106332 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3106333 : term441 = term442.
Proof. exact (MK_COMB (@lem3106332) (@lem3106331)). Qed.
Lemma lem3106334 : term440 = term443.
Proof. exact (MK_COMB (@lem3106333) (@lem3106328)). Qed.
Lemma lem3106335 : term444.
Proof. exact (@lem1980255 term217 term224 term224 term224). Qed.
Lemma lem3106337 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106338 : term440 = term446.
Proof. exact (@lem3106337 (NUMERAL 0) term131). Qed.
Lemma lem3106339 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106340 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106341 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106340 h1) (fun h1 : term446 = True => @lem3106339)). Qed.
Lemma lem3106342 : term446 = True.
Proof. exact (EQ_MP (@lem3106341) (@lem3106339)). Qed.
Lemma lem3106343 : term440 = True.
Proof. exact (TRANS (@lem3106338) (@lem3106342)). Qed.
Lemma lem3106344 : True = term440.
Proof. exact (SYM (@lem3106343)). Qed.
Lemma lem3106345 : term440.
Proof. exact (EQ_MP (@lem3106344) (@lem0)). Qed.
Lemma lem3106346 : term448.
Proof. exact (@lem3106335 (@lem3106345)). Qed.
Lemma lem3106348 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106349 : term440 = term446.
Proof. exact (@lem3106348 (NUMERAL 0) term131). Qed.
Lemma lem3106350 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106351 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106352 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106351 h1) (fun h1 : term446 = True => @lem3106350)). Qed.
Lemma lem3106353 : term446 = True.
Proof. exact (EQ_MP (@lem3106352) (@lem3106350)). Qed.
Lemma lem3106354 : term440 = True.
Proof. exact (TRANS (@lem3106349) (@lem3106353)). Qed.
Lemma lem3106355 : True = term440.
Proof. exact (SYM (@lem3106354)). Qed.
Lemma lem3106356 : term440.
Proof. exact (EQ_MP (@lem3106355) (@lem0)). Qed.
Lemma lem3106357 : term443 = term449.
Proof. exact (@lem3106346 (@lem3106356)). Qed.
Lemma lem3106359 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3106360 : term272 = term273.
Proof. exact (@lem3106359 term131 term131). Qed.
Lemma lem3106361 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106362 : term275 = term131.
Proof. exact (EQ_MP (@lem3106361) (@lem940073)). Qed.
Lemma lem3106363 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106364 : term273 = term224.
Proof. exact (MK_COMB (@lem3106363) (@lem3106362)). Qed.
Lemma lem3106365 : term272 = term224.
Proof. exact (TRANS (@lem3106360) (@lem3106364)). Qed.
Lemma lem3106367 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106368 : term451 = term217.
Proof. exact (@lem3106367 term131). Qed.
Lemma lem3106369 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3106370 : term452 = term441.
Proof. exact (MK_COMB (@lem3106369) (@lem3106368)). Qed.
Lemma lem3106371 : term449 = term440.
Proof. exact (MK_COMB (@lem3106370) (@lem3106365)). Qed.
Lemma lem3106373 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106374 : term440 = term446.
Proof. exact (@lem3106373 (NUMERAL 0) term131). Qed.
Lemma lem3106375 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106376 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106377 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106376 h1) (fun h1 : term446 = True => @lem3106375)). Qed.
Lemma lem3106378 : term446 = True.
Proof. exact (EQ_MP (@lem3106377) (@lem3106375)). Qed.
Lemma lem3106379 : term440 = True.
Proof. exact (TRANS (@lem3106374) (@lem3106378)). Qed.
Lemma lem3106380 : term449 = True.
Proof. exact (TRANS (@lem3106371) (@lem3106379)). Qed.
Lemma lem3106381 : term443 = True.
Proof. exact (TRANS (@lem3106357) (@lem3106380)). Qed.
Lemma lem3106382 : term440 = True.
Proof. exact (TRANS (@lem3106334) (@lem3106381)). Qed.
Lemma lem3106383 : term439 = True.
Proof. exact (TRANS (@lem3106325) (@lem3106382)). Qed.
Lemma lem3106384 : True = term439.
Proof. exact (SYM (@lem3106383)). Qed.
Lemma lem3106385 : term439.
Proof. exact (EQ_MP (@lem3106384) (@lem0)). Qed.
Lemma lem3106386 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term453 _32231 _32232.
Proof. exact (conj (@lem3106385) (@lem3106321 _32231 _32232 h1)). Qed.
Lemma lem3106388 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3106389 (_32231 : int) (_32232 : int) : term455 _32231 _32232.
Proof. exact (@lem3106388 term224 (term326 _32231 _32232)). Qed.
Lemma lem3106390 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term456 _32231 _32232.
Proof. exact (@lem3106389 _32231 _32232 (@lem3106386 _32231 _32232 h1)). Qed.
Lemma lem3106391 (_32231 : int) (_32232 : int) : (term457 _32231 _32232) = (term326 _32231 _32232).
Proof. exact (@lem1982733 (term326 _32231 _32232)). Qed.
Lemma lem3106392 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3106393 (_32231 : int) (_32232 : int) : (term458 _32231 _32232) = (term328 _32231 _32232).
Proof. exact (MK_COMB (@lem3106392) (@lem3106391 _32231 _32232)). Qed.
Lemma lem3106394 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3106395 (_32231 : int) (_32232 : int) : (term456 _32231 _32232) = (term329 _32231 _32232).
Proof. exact (MK_COMB (@lem3106393 _32231 _32232) (@lem3106394)). Qed.
Lemma lem3106396 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term329 _32231 _32232.
Proof. exact (EQ_MP (@lem3106395 _32231 _32232) (@lem3106390 _32231 _32232 h1)). Qed.
Lemma lem3106398 (y : real) : term516 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3106399 (_32232 : int) : term517 _32232.
Proof. exact (@lem3106398 (real_of_int _32232)). Qed.
Lemma lem3106400 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term518 _32232.
Proof. exact (@lem3106399 _32232 (@lem3106322 _32231 _32232 h1)). Qed.
Lemma lem3106401 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term519 _32232.
Proof. exact (@lem3106400 _32231 _32232 h1 term263). Qed.
Lemma lem3106402 (_32232 : int) : (term519 _32232) = ((term312 _32232) = term217).
Proof. exact (eq_refl (term519 _32232)). Qed.
Lemma lem3106409 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : (term312 _32232) = term217.
Proof. exact (EQ_MP (@lem3106402 _32232) (@lem3106401 _32231 _32232 h1)). Qed.
Lemma lem3106410 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term527 _32231 _32232.
Proof. exact (conj (@lem3106409 _32231 _32232 h1) (@lem3106396 _32231 _32232 h1)). Qed.
Lemma lem3106412 (x : real) (y : real) : term521 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3106413 (_32231 : int) (_32232 : int) : term528 _32231 _32232.
Proof. exact (@lem3106412 (term312 _32232) (term326 _32231 _32232)). Qed.
Lemma lem3106414 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term529 _32231 _32232.
Proof. exact (@lem3106413 _32231 _32232 (@lem3106410 _32231 _32232 h1)). Qed.
Lemma lem3106415 (_32231 : int) (_32232 : int) : (term530 _32231 _32232) = (term531 _32231 _32232).
Proof. exact (@lem1982757 (term312 _32231) (term312 _32232) (term296 _32232)). Qed.
Lemma lem3106416 (_32232 : int) : (term491 _32232) = (term492 _32232).
Proof. exact (@lem1982763 (term312 _32232) (real_of_int _32232) term263). Qed.
Lemma lem3106417 (_32232 : int) : (term493 _32232) = (term471 _32232).
Proof. exact (@lem1982713 term263 (real_of_int _32232)). Qed.
Lemma lem3106419 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106420 : term224 = term287.
Proof. exact (@lem3106419 term131). Qed.
Lemma lem3106422 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3106423 : term263 = term264.
Proof. exact (@lem3106422 term131). Qed.
Lemma lem3106424 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3106425 : term472 = term473.
Proof. exact (MK_COMB (@lem3106424) (@lem3106423)). Qed.
Lemma lem3106426 : term474 = term475.
Proof. exact (MK_COMB (@lem3106425) (@lem3106420)). Qed.
Lemma lem3106427 : term476.
Proof. exact (@lem1981473 term263 term224 term224 term224 term217 term224). Qed.
Lemma lem3106429 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106430 : term440 = term446.
Proof. exact (@lem3106429 (NUMERAL 0) term131). Qed.
Lemma lem3106431 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106432 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106433 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106432 h1) (fun h1 : term446 = True => @lem3106431)). Qed.
Lemma lem3106434 : term446 = True.
Proof. exact (EQ_MP (@lem3106433) (@lem3106431)). Qed.
Lemma lem3106435 : term440 = True.
Proof. exact (TRANS (@lem3106430) (@lem3106434)). Qed.
Lemma lem3106436 : True = term440.
Proof. exact (SYM (@lem3106435)). Qed.
Lemma lem3106437 : term440.
Proof. exact (EQ_MP (@lem3106436) (@lem0)). Qed.
Lemma lem3106438 : term477.
Proof. exact (@lem3106427 (@lem3106437)). Qed.
Lemma lem3106440 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106441 : term440 = term446.
Proof. exact (@lem3106440 (NUMERAL 0) term131). Qed.
Lemma lem3106442 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106443 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106444 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106443 h1) (fun h1 : term446 = True => @lem3106442)). Qed.
Lemma lem3106445 : term446 = True.
Proof. exact (EQ_MP (@lem3106444) (@lem3106442)). Qed.
Lemma lem3106446 : term440 = True.
Proof. exact (TRANS (@lem3106441) (@lem3106445)). Qed.
Lemma lem3106447 : True = term440.
Proof. exact (SYM (@lem3106446)). Qed.
Lemma lem3106448 : term440.
Proof. exact (EQ_MP (@lem3106447) (@lem0)). Qed.
Lemma lem3106449 : term478.
Proof. exact (@lem3106438 (@lem3106448)). Qed.
Lemma lem3106451 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106452 : term440 = term446.
Proof. exact (@lem3106451 (NUMERAL 0) term131). Qed.
Lemma lem3106453 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106454 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106455 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106454 h1) (fun h1 : term446 = True => @lem3106453)). Qed.
Lemma lem3106456 : term446 = True.
Proof. exact (EQ_MP (@lem3106455) (@lem3106453)). Qed.
Lemma lem3106457 : term440 = True.
Proof. exact (TRANS (@lem3106452) (@lem3106456)). Qed.
Lemma lem3106458 : True = term440.
Proof. exact (SYM (@lem3106457)). Qed.
Lemma lem3106459 : term440.
Proof. exact (EQ_MP (@lem3106458) (@lem0)). Qed.
Lemma lem3106460 : term479.
Proof. exact (@lem3106449 (@lem3106459)). Qed.
Lemma lem3106462 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3106463 : term272 = term273.
Proof. exact (@lem3106462 term131 term131). Qed.
Lemma lem3106464 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106465 : term275 = term131.
Proof. exact (EQ_MP (@lem3106464) (@lem940073)). Qed.
Lemma lem3106466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106467 : term273 = term224.
Proof. exact (MK_COMB (@lem3106466) (@lem3106465)). Qed.
Lemma lem3106468 : term272 = term224.
Proof. exact (TRANS (@lem3106463) (@lem3106467)). Qed.
Lemma lem3106470 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3106471 : term288 = term293.
Proof. exact (@lem3106470 term131 term131). Qed.
Lemma lem3106472 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106473 : term275 = term131.
Proof. exact (EQ_MP (@lem3106472) (@lem940073)). Qed.
Lemma lem3106474 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106475 : term273 = term224.
Proof. exact (MK_COMB (@lem3106474) (@lem3106473)). Qed.
Lemma lem3106476 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3106477 : term293 = term263.
Proof. exact (MK_COMB (@lem3106476) (@lem3106475)). Qed.
Lemma lem3106478 : term288 = term263.
Proof. exact (TRANS (@lem3106471) (@lem3106477)). Qed.
Lemma lem3106479 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3106480 : term480 = term472.
Proof. exact (MK_COMB (@lem3106479) (@lem3106478)). Qed.
Lemma lem3106481 : term481 = term474.
Proof. exact (MK_COMB (@lem3106480) (@lem3106468)). Qed.
Lemma lem3106483 (m : nat) : (term482 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3106484 : term474 = term217.
Proof. exact (@lem3106483 term131). Qed.
Lemma lem3106485 : term481 = term217.
Proof. exact (TRANS (@lem3106481) (@lem3106484)). Qed.
Lemma lem3106486 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3106487 : term483 = term484.
Proof. exact (MK_COMB (@lem3106486) (@lem3106485)). Qed.
Lemma lem3106488 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem3106489 : term485 = term451.
Proof. exact (MK_COMB (@lem3106487) (@lem3106488)). Qed.
Lemma lem3106491 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106492 : term451 = term217.
Proof. exact (@lem3106491 term131). Qed.
Lemma lem3106493 : term485 = term217.
Proof. exact (TRANS (@lem3106489) (@lem3106492)). Qed.
Lemma lem3106495 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3106496 : term272 = term273.
Proof. exact (@lem3106495 term131 term131). Qed.
Lemma lem3106497 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106498 : term275 = term131.
Proof. exact (EQ_MP (@lem3106497) (@lem940073)). Qed.
Lemma lem3106499 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106500 : term273 = term224.
Proof. exact (MK_COMB (@lem3106499) (@lem3106498)). Qed.
Lemma lem3106501 : term272 = term224.
Proof. exact (TRANS (@lem3106496) (@lem3106500)). Qed.
Lemma lem3106502 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem3106503 : term486 = term451.
Proof. exact (MK_COMB (@lem3106502) (@lem3106501)). Qed.
Lemma lem3106505 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106506 : term451 = term217.
Proof. exact (@lem3106505 term131). Qed.
Lemma lem3106507 : term486 = term217.
Proof. exact (TRANS (@lem3106503) (@lem3106506)). Qed.
Lemma lem3106508 : term217 = term486.
Proof. exact (SYM (@lem3106507)). Qed.
Lemma lem3106509 : term485 = term486.
Proof. exact (TRANS (@lem3106493) (@lem3106508)). Qed.
Lemma lem3106510 : term475 = term260.
Proof. exact (@lem3106460 (@lem3106509)). Qed.
Lemma lem3106511 : term474 = term260.
Proof. exact (TRANS (@lem3106426) (@lem3106510)). Qed.
Lemma lem3106513 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3106514 : term260 = term217.
Proof. exact (@lem3106513 term217). Qed.
Lemma lem3106515 : term474 = term217.
Proof. exact (TRANS (@lem3106511) (@lem3106514)). Qed.
Lemma lem3106516 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3106517 : term487 = term484.
Proof. exact (MK_COMB (@lem3106516) (@lem3106515)). Qed.
Lemma lem3106518 (_32232 : int) : (real_of_int _32232) = (real_of_int _32232).
Proof. exact (eq_refl (real_of_int _32232)). Qed.
Lemma lem3106519 (_32232 : int) : (term471 _32232) = (term488 _32232).
Proof. exact (MK_COMB (@lem3106517) (@lem3106518 _32232)). Qed.
Lemma lem3106520 (_32232 : int) : (term493 _32232) = (term488 _32232).
Proof. exact (TRANS (@lem3106417 _32232) (@lem3106519 _32232)). Qed.
Lemma lem3106521 (_32232 : int) : (term488 _32232) = term217.
Proof. exact (@lem1982719 (real_of_int _32232)). Qed.
Lemma lem3106522 (_32232 : int) : (term493 _32232) = term217.
Proof. exact (TRANS (@lem3106520 _32232) (@lem3106521 _32232)). Qed.
Lemma lem3106523 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3106524 (_32232 : int) : (term494 _32232) = term490.
Proof. exact (MK_COMB (@lem3106523) (@lem3106522 _32232)). Qed.
Lemma lem3106525 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem3106526 (_32232 : int) : (term492 _32232) = term495.
Proof. exact (MK_COMB (@lem3106524 _32232) (@lem3106525)). Qed.
Lemma lem3106527 (_32232 : int) : (term491 _32232) = term495.
Proof. exact (TRANS (@lem3106416 _32232) (@lem3106526 _32232)). Qed.
Lemma lem3106528 : term495 = term263.
Proof. exact (@lem1982721 term263). Qed.
Lemma lem3106529 (_32232 : int) : (term491 _32232) = term263.
Proof. exact (TRANS (@lem3106527 _32232) (@lem3106528)). Qed.
Lemma lem3106530 (_32231 : int) : (term323 _32231) = (term323 _32231).
Proof. exact (eq_refl (term323 _32231)). Qed.
Lemma lem3106531 (_32232 : int) (_32231 : int) : (term531 _32231 _32232) = (term324 _32231).
Proof. exact (MK_COMB (@lem3106530 _32231) (@lem3106529 _32232)). Qed.
Lemma lem3106532 (_32232 : int) (_32231 : int) : (term530 _32231 _32232) = (term324 _32231).
Proof. exact (TRANS (@lem3106415 _32231 _32232) (@lem3106531 _32232 _32231)). Qed.
Lemma lem3106533 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3106534 (_32232 : int) (_32231 : int) : (term532 _32231 _32232) = (term533 _32231).
Proof. exact (MK_COMB (@lem3106533) (@lem3106532 _32232 _32231)). Qed.
Lemma lem3106535 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3106536 (_32232 : int) (_32231 : int) : (term529 _32231 _32232) = (term534 _32231).
Proof. exact (MK_COMB (@lem3106534 _32232 _32231) (@lem3106535)). Qed.
Lemma lem3106537 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term534 _32231.
Proof. exact (EQ_MP (@lem3106536 _32232 _32231) (@lem3106414 _32231 _32232 h1)). Qed.
Lemma lem3106539 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3106540 : term439 = term440.
Proof. exact (@lem3106539 term217 term224). Qed.
Lemma lem3106542 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106543 : term224 = term287.
Proof. exact (@lem3106542 term131). Qed.
Lemma lem3106545 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106546 : term217 = term260.
Proof. exact (@lem3106545 (NUMERAL 0)). Qed.
Lemma lem3106547 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3106548 : term441 = term442.
Proof. exact (MK_COMB (@lem3106547) (@lem3106546)). Qed.
Lemma lem3106549 : term440 = term443.
Proof. exact (MK_COMB (@lem3106548) (@lem3106543)). Qed.
Lemma lem3106550 : term444.
Proof. exact (@lem1980255 term217 term224 term224 term224). Qed.
Lemma lem3106552 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106553 : term440 = term446.
Proof. exact (@lem3106552 (NUMERAL 0) term131). Qed.
Lemma lem3106554 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106555 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106556 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106555 h1) (fun h1 : term446 = True => @lem3106554)). Qed.
Lemma lem3106557 : term446 = True.
Proof. exact (EQ_MP (@lem3106556) (@lem3106554)). Qed.
Lemma lem3106558 : term440 = True.
Proof. exact (TRANS (@lem3106553) (@lem3106557)). Qed.
Lemma lem3106559 : True = term440.
Proof. exact (SYM (@lem3106558)). Qed.
Lemma lem3106560 : term440.
Proof. exact (EQ_MP (@lem3106559) (@lem0)). Qed.
Lemma lem3106561 : term448.
Proof. exact (@lem3106550 (@lem3106560)). Qed.
Lemma lem3106563 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106564 : term440 = term446.
Proof. exact (@lem3106563 (NUMERAL 0) term131). Qed.
Lemma lem3106565 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106566 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106567 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106566 h1) (fun h1 : term446 = True => @lem3106565)). Qed.
Lemma lem3106568 : term446 = True.
Proof. exact (EQ_MP (@lem3106567) (@lem3106565)). Qed.
Lemma lem3106569 : term440 = True.
Proof. exact (TRANS (@lem3106564) (@lem3106568)). Qed.
Lemma lem3106570 : True = term440.
Proof. exact (SYM (@lem3106569)). Qed.
Lemma lem3106571 : term440.
Proof. exact (EQ_MP (@lem3106570) (@lem0)). Qed.
Lemma lem3106572 : term443 = term449.
Proof. exact (@lem3106561 (@lem3106571)). Qed.
Lemma lem3106574 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3106575 : term272 = term273.
Proof. exact (@lem3106574 term131 term131). Qed.
Lemma lem3106576 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106577 : term275 = term131.
Proof. exact (EQ_MP (@lem3106576) (@lem940073)). Qed.
Lemma lem3106578 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106579 : term273 = term224.
Proof. exact (MK_COMB (@lem3106578) (@lem3106577)). Qed.
Lemma lem3106580 : term272 = term224.
Proof. exact (TRANS (@lem3106575) (@lem3106579)). Qed.
Lemma lem3106582 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106583 : term451 = term217.
Proof. exact (@lem3106582 term131). Qed.
Lemma lem3106584 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3106585 : term452 = term441.
Proof. exact (MK_COMB (@lem3106584) (@lem3106583)). Qed.
Lemma lem3106586 : term449 = term440.
Proof. exact (MK_COMB (@lem3106585) (@lem3106580)). Qed.
Lemma lem3106588 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106589 : term440 = term446.
Proof. exact (@lem3106588 (NUMERAL 0) term131). Qed.
Lemma lem3106590 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106591 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106592 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106591 h1) (fun h1 : term446 = True => @lem3106590)). Qed.
Lemma lem3106593 : term446 = True.
Proof. exact (EQ_MP (@lem3106592) (@lem3106590)). Qed.
Lemma lem3106594 : term440 = True.
Proof. exact (TRANS (@lem3106589) (@lem3106593)). Qed.
Lemma lem3106595 : term449 = True.
Proof. exact (TRANS (@lem3106586) (@lem3106594)). Qed.
Lemma lem3106596 : term443 = True.
Proof. exact (TRANS (@lem3106572) (@lem3106595)). Qed.
Lemma lem3106597 : term440 = True.
Proof. exact (TRANS (@lem3106549) (@lem3106596)). Qed.
Lemma lem3106598 : term439 = True.
Proof. exact (TRANS (@lem3106540) (@lem3106597)). Qed.
Lemma lem3106599 : True = term439.
Proof. exact (SYM (@lem3106598)). Qed.
Lemma lem3106600 : term439.
Proof. exact (EQ_MP (@lem3106599) (@lem0)). Qed.
Lemma lem3106601 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term535 _32231.
Proof. exact (conj (@lem3106600) (@lem3106537 _32231 _32232 h1)). Qed.
Lemma lem3106603 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3106604 (_32231 : int) : term536 _32231.
Proof. exact (@lem3106603 term224 (term324 _32231)). Qed.
Lemma lem3106605 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term537 _32231.
Proof. exact (@lem3106604 _32231 (@lem3106601 _32231 _32232 h1)). Qed.
Lemma lem3106606 (_32231 : int) : (term538 _32231) = (term324 _32231).
Proof. exact (@lem1982733 (term324 _32231)). Qed.
Lemma lem3106607 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3106608 (_32231 : int) : (term539 _32231) = (term533 _32231).
Proof. exact (MK_COMB (@lem3106607) (@lem3106606 _32231)). Qed.
Lemma lem3106609 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3106610 (_32231 : int) : (term537 _32231) = (term534 _32231).
Proof. exact (MK_COMB (@lem3106608 _32231) (@lem3106609)). Qed.
Lemma lem3106611 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term534 _32231.
Proof. exact (EQ_MP (@lem3106610 _32231) (@lem3106605 _32231 _32232 h1)). Qed.
Lemma lem3106613 (y : real) : term516 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3106614 (_32231 : int) : term517 _32231.
Proof. exact (@lem3106613 (real_of_int _32231)). Qed.
Lemma lem3106615 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term518 _32231.
Proof. exact (@lem3106614 _32231 (@lem3106320 _32231 _32232 h1)). Qed.
Lemma lem3106616 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term540 _32231.
Proof. exact (@lem3106615 _32231 _32232 h1 term224). Qed.
Lemma lem3106617 (_32231 : int) : (term540 _32231) = ((term541 _32231) = term217).
Proof. exact (eq_refl (term540 _32231)). Qed.
Lemma lem3106618 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : (term541 _32231) = term217.
Proof. exact (EQ_MP (@lem3106617 _32231) (@lem3106616 _32231 _32232 h1)). Qed.
Lemma lem3106619 (_32231 : int) : (term541 _32231) = (real_of_int _32231).
Proof. exact (@lem1982733 (real_of_int _32231)). Qed.
Lemma lem3106620 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3106621 (_32231 : int) : (term542 _32231) = (term230 _32231).
Proof. exact (MK_COMB (@lem3106620) (@lem3106619 _32231)). Qed.
Lemma lem3106622 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3106623 (_32231 : int) : ((term541 _32231) = term217) = ((real_of_int _32231) = term217).
Proof. exact (MK_COMB (@lem3106621 _32231) (@lem3106622)). Qed.
Lemma lem3106624 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : (real_of_int _32231) = term217.
Proof. exact (EQ_MP (@lem3106623 _32231) (@lem3106618 _32231 _32232 h1)). Qed.
Lemma lem3106625 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term543 _32231.
Proof. exact (conj (@lem3106624 _32231 _32232 h1) (@lem3106611 _32231 _32232 h1)). Qed.
Lemma lem3106627 (x : real) (y : real) : term521 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3106628 (_32231 : int) : term544 _32231.
Proof. exact (@lem3106627 (real_of_int _32231) (term324 _32231)). Qed.
Lemma lem3106629 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term545 _32231.
Proof. exact (@lem3106628 _32231 (@lem3106625 _32231 _32232 h1)). Qed.
Lemma lem3106630 (_32231 : int) : (term546 _32231) = (term547 _32231).
Proof. exact (@lem1982763 (real_of_int _32231) (term312 _32231) term263). Qed.
Lemma lem3106631 (_32231 : int) : (term470 _32231) = (term471 _32231).
Proof. exact (@lem1982715 term263 (real_of_int _32231)). Qed.
Lemma lem3106633 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106634 : term224 = term287.
Proof. exact (@lem3106633 term131). Qed.
Lemma lem3106636 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3106637 : term263 = term264.
Proof. exact (@lem3106636 term131). Qed.
Lemma lem3106638 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3106639 : term472 = term473.
Proof. exact (MK_COMB (@lem3106638) (@lem3106637)). Qed.
Lemma lem3106640 : term474 = term475.
Proof. exact (MK_COMB (@lem3106639) (@lem3106634)). Qed.
Lemma lem3106641 : term476.
Proof. exact (@lem1981473 term263 term224 term224 term224 term217 term224). Qed.
Lemma lem3106643 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106644 : term440 = term446.
Proof. exact (@lem3106643 (NUMERAL 0) term131). Qed.
Lemma lem3106645 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106646 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106647 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106646 h1) (fun h1 : term446 = True => @lem3106645)). Qed.
Lemma lem3106648 : term446 = True.
Proof. exact (EQ_MP (@lem3106647) (@lem3106645)). Qed.
Lemma lem3106649 : term440 = True.
Proof. exact (TRANS (@lem3106644) (@lem3106648)). Qed.
Lemma lem3106650 : True = term440.
Proof. exact (SYM (@lem3106649)). Qed.
Lemma lem3106651 : term440.
Proof. exact (EQ_MP (@lem3106650) (@lem0)). Qed.
Lemma lem3106652 : term477.
Proof. exact (@lem3106641 (@lem3106651)). Qed.
Lemma lem3106654 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106655 : term440 = term446.
Proof. exact (@lem3106654 (NUMERAL 0) term131). Qed.
Lemma lem3106656 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106657 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106658 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106657 h1) (fun h1 : term446 = True => @lem3106656)). Qed.
Lemma lem3106659 : term446 = True.
Proof. exact (EQ_MP (@lem3106658) (@lem3106656)). Qed.
Lemma lem3106660 : term440 = True.
Proof. exact (TRANS (@lem3106655) (@lem3106659)). Qed.
Lemma lem3106661 : True = term440.
Proof. exact (SYM (@lem3106660)). Qed.
Lemma lem3106662 : term440.
Proof. exact (EQ_MP (@lem3106661) (@lem0)). Qed.
Lemma lem3106663 : term478.
Proof. exact (@lem3106652 (@lem3106662)). Qed.
Lemma lem3106665 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106666 : term440 = term446.
Proof. exact (@lem3106665 (NUMERAL 0) term131). Qed.
Lemma lem3106667 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106668 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106669 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106668 h1) (fun h1 : term446 = True => @lem3106667)). Qed.
Lemma lem3106670 : term446 = True.
Proof. exact (EQ_MP (@lem3106669) (@lem3106667)). Qed.
Lemma lem3106671 : term440 = True.
Proof. exact (TRANS (@lem3106666) (@lem3106670)). Qed.
Lemma lem3106672 : True = term440.
Proof. exact (SYM (@lem3106671)). Qed.
Lemma lem3106673 : term440.
Proof. exact (EQ_MP (@lem3106672) (@lem0)). Qed.
Lemma lem3106674 : term479.
Proof. exact (@lem3106663 (@lem3106673)). Qed.
Lemma lem3106676 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3106677 : term272 = term273.
Proof. exact (@lem3106676 term131 term131). Qed.
Lemma lem3106678 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106679 : term275 = term131.
Proof. exact (EQ_MP (@lem3106678) (@lem940073)). Qed.
Lemma lem3106680 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106681 : term273 = term224.
Proof. exact (MK_COMB (@lem3106680) (@lem3106679)). Qed.
Lemma lem3106682 : term272 = term224.
Proof. exact (TRANS (@lem3106677) (@lem3106681)). Qed.
Lemma lem3106684 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3106685 : term288 = term293.
Proof. exact (@lem3106684 term131 term131). Qed.
Lemma lem3106686 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106687 : term275 = term131.
Proof. exact (EQ_MP (@lem3106686) (@lem940073)). Qed.
Lemma lem3106688 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106689 : term273 = term224.
Proof. exact (MK_COMB (@lem3106688) (@lem3106687)). Qed.
Lemma lem3106690 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3106691 : term293 = term263.
Proof. exact (MK_COMB (@lem3106690) (@lem3106689)). Qed.
Lemma lem3106692 : term288 = term263.
Proof. exact (TRANS (@lem3106685) (@lem3106691)). Qed.
Lemma lem3106693 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3106694 : term480 = term472.
Proof. exact (MK_COMB (@lem3106693) (@lem3106692)). Qed.
Lemma lem3106695 : term481 = term474.
Proof. exact (MK_COMB (@lem3106694) (@lem3106682)). Qed.
Lemma lem3106697 (m : nat) : (term482 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3106698 : term474 = term217.
Proof. exact (@lem3106697 term131). Qed.
Lemma lem3106699 : term481 = term217.
Proof. exact (TRANS (@lem3106695) (@lem3106698)). Qed.
Lemma lem3106700 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3106701 : term483 = term484.
Proof. exact (MK_COMB (@lem3106700) (@lem3106699)). Qed.
Lemma lem3106702 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem3106703 : term485 = term451.
Proof. exact (MK_COMB (@lem3106701) (@lem3106702)). Qed.
Lemma lem3106705 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106706 : term451 = term217.
Proof. exact (@lem3106705 term131). Qed.
Lemma lem3106707 : term485 = term217.
Proof. exact (TRANS (@lem3106703) (@lem3106706)). Qed.
Lemma lem3106709 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3106710 : term272 = term273.
Proof. exact (@lem3106709 term131 term131). Qed.
Lemma lem3106711 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106712 : term275 = term131.
Proof. exact (EQ_MP (@lem3106711) (@lem940073)). Qed.
Lemma lem3106713 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106714 : term273 = term224.
Proof. exact (MK_COMB (@lem3106713) (@lem3106712)). Qed.
Lemma lem3106715 : term272 = term224.
Proof. exact (TRANS (@lem3106710) (@lem3106714)). Qed.
Lemma lem3106716 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem3106717 : term486 = term451.
Proof. exact (MK_COMB (@lem3106716) (@lem3106715)). Qed.
Lemma lem3106719 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106720 : term451 = term217.
Proof. exact (@lem3106719 term131). Qed.
Lemma lem3106721 : term486 = term217.
Proof. exact (TRANS (@lem3106717) (@lem3106720)). Qed.
Lemma lem3106722 : term217 = term486.
Proof. exact (SYM (@lem3106721)). Qed.
Lemma lem3106723 : term485 = term486.
Proof. exact (TRANS (@lem3106707) (@lem3106722)). Qed.
Lemma lem3106724 : term475 = term260.
Proof. exact (@lem3106674 (@lem3106723)). Qed.
Lemma lem3106725 : term474 = term260.
Proof. exact (TRANS (@lem3106640) (@lem3106724)). Qed.
Lemma lem3106727 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3106728 : term260 = term217.
Proof. exact (@lem3106727 term217). Qed.
Lemma lem3106729 : term474 = term217.
Proof. exact (TRANS (@lem3106725) (@lem3106728)). Qed.
Lemma lem3106730 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3106731 : term487 = term484.
Proof. exact (MK_COMB (@lem3106730) (@lem3106729)). Qed.
Lemma lem3106732 (_32231 : int) : (real_of_int _32231) = (real_of_int _32231).
Proof. exact (eq_refl (real_of_int _32231)). Qed.
Lemma lem3106733 (_32231 : int) : (term471 _32231) = (term488 _32231).
Proof. exact (MK_COMB (@lem3106731) (@lem3106732 _32231)). Qed.
Lemma lem3106734 (_32231 : int) : (term470 _32231) = (term488 _32231).
Proof. exact (TRANS (@lem3106631 _32231) (@lem3106733 _32231)). Qed.
Lemma lem3106735 (_32231 : int) : (term488 _32231) = term217.
Proof. exact (@lem1982719 (real_of_int _32231)). Qed.
Lemma lem3106736 (_32231 : int) : (term470 _32231) = term217.
Proof. exact (TRANS (@lem3106734 _32231) (@lem3106735 _32231)). Qed.
Lemma lem3106737 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3106738 (_32231 : int) : (term489 _32231) = term490.
Proof. exact (MK_COMB (@lem3106737) (@lem3106736 _32231)). Qed.
Lemma lem3106739 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem3106740 (_32231 : int) : (term547 _32231) = term495.
Proof. exact (MK_COMB (@lem3106738 _32231) (@lem3106739)). Qed.
Lemma lem3106741 (_32231 : int) : (term546 _32231) = term495.
Proof. exact (TRANS (@lem3106630 _32231) (@lem3106740 _32231)). Qed.
Lemma lem3106742 : term495 = term263.
Proof. exact (@lem1982721 term263). Qed.
Lemma lem3106743 (_32231 : int) : (term546 _32231) = term263.
Proof. exact (TRANS (@lem3106741 _32231) (@lem3106742)). Qed.
Lemma lem3106744 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3106745 (_32231 : int) : (term548 _32231) = term497.
Proof. exact (MK_COMB (@lem3106744) (@lem3106743 _32231)). Qed.
Lemma lem3106746 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3106747 (_32231 : int) : (term545 _32231) = term498.
Proof. exact (MK_COMB (@lem3106745 _32231) (@lem3106746)). Qed.
Lemma lem3106748 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : term498.
Proof. exact (EQ_MP (@lem3106747 _32231) (@lem3106629 _32231 _32232 h1)). Qed.
Lemma lem3106750 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3106751 : term498 = term499.
Proof. exact (@lem3106750 term217 term263). Qed.
Lemma lem3106753 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3106754 : term263 = term264.
Proof. exact (@lem3106753 term131). Qed.
Lemma lem3106756 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106757 : term217 = term260.
Proof. exact (@lem3106756 (NUMERAL 0)). Qed.
Lemma lem3106758 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3106759 : term219 = term500.
Proof. exact (MK_COMB (@lem3106758) (@lem3106757)). Qed.
Lemma lem3106760 : term499 = term501.
Proof. exact (MK_COMB (@lem3106759) (@lem3106754)). Qed.
Lemma lem3106761 : term502.
Proof. exact (@lem1980026 term217 term224 term263 term224). Qed.
Lemma lem3106763 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106764 : term440 = term446.
Proof. exact (@lem3106763 (NUMERAL 0) term131). Qed.
Lemma lem3106765 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106766 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106767 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106766 h1) (fun h1 : term446 = True => @lem3106765)). Qed.
Lemma lem3106768 : term446 = True.
Proof. exact (EQ_MP (@lem3106767) (@lem3106765)). Qed.
Lemma lem3106769 : term440 = True.
Proof. exact (TRANS (@lem3106764) (@lem3106768)). Qed.
Lemma lem3106770 : True = term440.
Proof. exact (SYM (@lem3106769)). Qed.
Lemma lem3106771 : term440.
Proof. exact (EQ_MP (@lem3106770) (@lem0)). Qed.
Lemma lem3106772 : term503.
Proof. exact (@lem3106761 (@lem3106771)). Qed.
Lemma lem3106774 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106775 : term440 = term446.
Proof. exact (@lem3106774 (NUMERAL 0) term131). Qed.
Lemma lem3106776 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106777 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106778 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106777 h1) (fun h1 : term446 = True => @lem3106776)). Qed.
Lemma lem3106779 : term446 = True.
Proof. exact (EQ_MP (@lem3106778) (@lem3106776)). Qed.
Lemma lem3106780 : term440 = True.
Proof. exact (TRANS (@lem3106775) (@lem3106779)). Qed.
Lemma lem3106781 : True = term440.
Proof. exact (SYM (@lem3106780)). Qed.
Lemma lem3106782 : term440.
Proof. exact (EQ_MP (@lem3106781) (@lem0)). Qed.
Lemma lem3106783 : term501 = term504.
Proof. exact (@lem3106772 (@lem3106782)). Qed.
Lemma lem3106785 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3106786 : term288 = term293.
Proof. exact (@lem3106785 term131 term131). Qed.
Lemma lem3106787 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106788 : term275 = term131.
Proof. exact (EQ_MP (@lem3106787) (@lem940073)). Qed.
Lemma lem3106789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106790 : term273 = term224.
Proof. exact (MK_COMB (@lem3106789) (@lem3106788)). Qed.
Lemma lem3106791 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3106792 : term293 = term263.
Proof. exact (MK_COMB (@lem3106791) (@lem3106790)). Qed.
Lemma lem3106793 : term288 = term263.
Proof. exact (TRANS (@lem3106786) (@lem3106792)). Qed.
Lemma lem3106795 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106796 : term451 = term217.
Proof. exact (@lem3106795 term131). Qed.
Lemma lem3106797 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3106798 : term505 = term219.
Proof. exact (MK_COMB (@lem3106797) (@lem3106796)). Qed.
Lemma lem3106799 : term504 = term499.
Proof. exact (MK_COMB (@lem3106798) (@lem3106793)). Qed.
Lemma lem3106801 (m : nat) (n : nat) : (term506 m n) = (term507 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3106802 : term499 = term508.
Proof. exact (@lem3106801 (NUMERAL 0) term131). Qed.
Lemma lem3106803 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106804 (h1 : term447 = (BIT1 0)) : (term131 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3106805 : (term447 = (BIT1 0)) = ((term131 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106804 h1) (fun h1 : (term131 = (NUMERAL 0)) = False => @lem3106803)). Qed.
Lemma lem3106806 : (term131 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3106805) (@lem3106803)). Qed.
Lemma lem3106807 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3106808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3106809 : term509 = (and True).
Proof. exact (MK_COMB (@lem3106808) (@lem3106807)). Qed.
Lemma lem3106810 : term508 = (True /\ False).
Proof. exact (MK_COMB (@lem3106809) (@lem3106806)). Qed.
Lemma lem3106812 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3106813 : term508 = False.
Proof. exact (TRANS (@lem3106810) (@lem3106812)). Qed.
Lemma lem3106814 : term499 = False.
Proof. exact (TRANS (@lem3106802) (@lem3106813)). Qed.
Lemma lem3106815 : term504 = False.
Proof. exact (TRANS (@lem3106799) (@lem3106814)). Qed.
Lemma lem3106816 : term501 = False.
Proof. exact (TRANS (@lem3106783) (@lem3106815)). Qed.
Lemma lem3106817 : term499 = False.
Proof. exact (TRANS (@lem3106760) (@lem3106816)). Qed.
Lemma lem3106818 : term498 = False.
Proof. exact (TRANS (@lem3106751) (@lem3106817)). Qed.
Lemma lem3106819 (_32231 : int) (_32232 : int) (h1 : term526 _32231 _32232) : False.
Proof. exact (EQ_MP (@lem3106818) (@lem3106748 _32231 _32232 h1)). Qed.
Lemma lem3106820 (_32231 : int) (_32232 : int) (h1 : term425 _32231 _32232) : False.
Proof. exact (or_elim (@lem3106020 _32231 _32232 h1) (fun h0 : term525 _32231 _32232 => @lem3106313 _32231 _32232 h0) (fun h0 : term526 _32231 _32232 => @lem3106819 _32231 _32232 h0)). Qed.
Lemma lem3106821 (_32231 : int) (_32232 : int) (h1 : term434 _32231 _32232) : False.
Proof. exact (or_elim (@lem3105255 _32231 _32232 h1) (fun h0 : term429 _32231 _32232 => @lem3106019 _32231 _32232 h0) (fun h0 : term425 _32231 _32232 => @lem3106820 _32231 _32232 h0)). Qed.
Lemma lem3106822 (_32231 : int) (_32232 : int) (h1 : term421 _32231 _32232) : term421 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3106823 (_32231 : int) (_32232 : int) (h1 : term416 _32231 _32232) : term416 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3106824 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term549 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3106825 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term417 _32231 _32232.
Proof. exact (proj2 (@lem3106824 _32231 _32232 h1)). Qed.
Lemma lem3106827 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term386 _32231 _32232.
Proof. exact (proj2 (@lem3106825 _32231 _32232 h1)). Qed.
Lemma lem3106829 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term353 _32231 _32232.
Proof. exact (proj2 (@lem3106827 _32231 _32232 h1)). Qed.
Lemma lem3106833 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term331 _32231 _32232.
Proof. exact (proj2 (@lem3106829 _32231 _32232 h1)). Qed.
Lemma lem3106834 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term315 _32231 _32232.
Proof. exact (proj1 (@lem3106829 _32231 _32232 h1)). Qed.
Lemma lem3106835 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term314 _32231 _32232.
Proof. exact (proj2 (@lem3106834 _32231 _32232 h1)). Qed.
Lemma lem3106838 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3106839 : term439 = term440.
Proof. exact (@lem3106838 term217 term224). Qed.
Lemma lem3106841 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106842 : term224 = term287.
Proof. exact (@lem3106841 term131). Qed.
Lemma lem3106844 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106845 : term217 = term260.
Proof. exact (@lem3106844 (NUMERAL 0)). Qed.
Lemma lem3106846 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3106847 : term441 = term442.
Proof. exact (MK_COMB (@lem3106846) (@lem3106845)). Qed.
Lemma lem3106848 : term440 = term443.
Proof. exact (MK_COMB (@lem3106847) (@lem3106842)). Qed.
Lemma lem3106849 : term444.
Proof. exact (@lem1980255 term217 term224 term224 term224). Qed.
Lemma lem3106851 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106852 : term440 = term446.
Proof. exact (@lem3106851 (NUMERAL 0) term131). Qed.
Lemma lem3106853 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106854 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106855 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106854 h1) (fun h1 : term446 = True => @lem3106853)). Qed.
Lemma lem3106856 : term446 = True.
Proof. exact (EQ_MP (@lem3106855) (@lem3106853)). Qed.
Lemma lem3106857 : term440 = True.
Proof. exact (TRANS (@lem3106852) (@lem3106856)). Qed.
Lemma lem3106858 : True = term440.
Proof. exact (SYM (@lem3106857)). Qed.
Lemma lem3106859 : term440.
Proof. exact (EQ_MP (@lem3106858) (@lem0)). Qed.
Lemma lem3106860 : term448.
Proof. exact (@lem3106849 (@lem3106859)). Qed.
Lemma lem3106862 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106863 : term440 = term446.
Proof. exact (@lem3106862 (NUMERAL 0) term131). Qed.
Lemma lem3106864 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106865 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106866 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106865 h1) (fun h1 : term446 = True => @lem3106864)). Qed.
Lemma lem3106867 : term446 = True.
Proof. exact (EQ_MP (@lem3106866) (@lem3106864)). Qed.
Lemma lem3106868 : term440 = True.
Proof. exact (TRANS (@lem3106863) (@lem3106867)). Qed.
Lemma lem3106869 : True = term440.
Proof. exact (SYM (@lem3106868)). Qed.
Lemma lem3106870 : term440.
Proof. exact (EQ_MP (@lem3106869) (@lem0)). Qed.
Lemma lem3106871 : term443 = term449.
Proof. exact (@lem3106860 (@lem3106870)). Qed.
Lemma lem3106873 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3106874 : term272 = term273.
Proof. exact (@lem3106873 term131 term131). Qed.
Lemma lem3106875 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106876 : term275 = term131.
Proof. exact (EQ_MP (@lem3106875) (@lem940073)). Qed.
Lemma lem3106877 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106878 : term273 = term224.
Proof. exact (MK_COMB (@lem3106877) (@lem3106876)). Qed.
Lemma lem3106879 : term272 = term224.
Proof. exact (TRANS (@lem3106874) (@lem3106878)). Qed.
Lemma lem3106881 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106882 : term451 = term217.
Proof. exact (@lem3106881 term131). Qed.
Lemma lem3106883 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3106884 : term452 = term441.
Proof. exact (MK_COMB (@lem3106883) (@lem3106882)). Qed.
Lemma lem3106885 : term449 = term440.
Proof. exact (MK_COMB (@lem3106884) (@lem3106879)). Qed.
Lemma lem3106887 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106888 : term440 = term446.
Proof. exact (@lem3106887 (NUMERAL 0) term131). Qed.
Lemma lem3106889 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106890 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106891 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106890 h1) (fun h1 : term446 = True => @lem3106889)). Qed.
Lemma lem3106892 : term446 = True.
Proof. exact (EQ_MP (@lem3106891) (@lem3106889)). Qed.
Lemma lem3106893 : term440 = True.
Proof. exact (TRANS (@lem3106888) (@lem3106892)). Qed.
Lemma lem3106894 : term449 = True.
Proof. exact (TRANS (@lem3106885) (@lem3106893)). Qed.
Lemma lem3106895 : term443 = True.
Proof. exact (TRANS (@lem3106871) (@lem3106894)). Qed.
Lemma lem3106896 : term440 = True.
Proof. exact (TRANS (@lem3106848) (@lem3106895)). Qed.
Lemma lem3106897 : term439 = True.
Proof. exact (TRANS (@lem3106839) (@lem3106896)). Qed.
Lemma lem3106898 : True = term439.
Proof. exact (SYM (@lem3106897)). Qed.
Lemma lem3106899 : term439.
Proof. exact (EQ_MP (@lem3106898) (@lem0)). Qed.
Lemma lem3106900 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term550 _32231 _32232.
Proof. exact (conj (@lem3106899) (@lem3106833 _32231 _32232 h1)). Qed.
Lemma lem3106902 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3106903 (_32231 : int) (_32232 : int) : term551 _32231 _32232.
Proof. exact (@lem3106902 term224 (term325 _32231 _32232)). Qed.
Lemma lem3106904 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term552 _32231 _32232.
Proof. exact (@lem3106903 _32231 _32232 (@lem3106900 _32231 _32232 h1)). Qed.
Lemma lem3106905 (_32231 : int) (_32232 : int) : (term553 _32231 _32232) = (term325 _32231 _32232).
Proof. exact (@lem1982733 (term325 _32231 _32232)). Qed.
Lemma lem3106906 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3106907 (_32231 : int) (_32232 : int) : (term554 _32231 _32232) = (term330 _32231 _32232).
Proof. exact (MK_COMB (@lem3106906) (@lem3106905 _32231 _32232)). Qed.
Lemma lem3106908 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3106909 (_32231 : int) (_32232 : int) : (term552 _32231 _32232) = (term331 _32231 _32232).
Proof. exact (MK_COMB (@lem3106907 _32231 _32232) (@lem3106908)). Qed.
Lemma lem3106910 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term331 _32231 _32232.
Proof. exact (EQ_MP (@lem3106909 _32231 _32232) (@lem3106904 _32231 _32232 h1)). Qed.
Lemma lem3106912 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3106913 : term439 = term440.
Proof. exact (@lem3106912 term217 term224). Qed.
Lemma lem3106915 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106916 : term224 = term287.
Proof. exact (@lem3106915 term131). Qed.
Lemma lem3106918 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106919 : term217 = term260.
Proof. exact (@lem3106918 (NUMERAL 0)). Qed.
Lemma lem3106920 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3106921 : term441 = term442.
Proof. exact (MK_COMB (@lem3106920) (@lem3106919)). Qed.
Lemma lem3106922 : term440 = term443.
Proof. exact (MK_COMB (@lem3106921) (@lem3106916)). Qed.
Lemma lem3106923 : term444.
Proof. exact (@lem1980255 term217 term224 term224 term224). Qed.
Lemma lem3106925 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106926 : term440 = term446.
Proof. exact (@lem3106925 (NUMERAL 0) term131). Qed.
Lemma lem3106927 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106928 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106929 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106928 h1) (fun h1 : term446 = True => @lem3106927)). Qed.
Lemma lem3106930 : term446 = True.
Proof. exact (EQ_MP (@lem3106929) (@lem3106927)). Qed.
Lemma lem3106931 : term440 = True.
Proof. exact (TRANS (@lem3106926) (@lem3106930)). Qed.
Lemma lem3106932 : True = term440.
Proof. exact (SYM (@lem3106931)). Qed.
Lemma lem3106933 : term440.
Proof. exact (EQ_MP (@lem3106932) (@lem0)). Qed.
Lemma lem3106934 : term448.
Proof. exact (@lem3106923 (@lem3106933)). Qed.
Lemma lem3106936 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106937 : term440 = term446.
Proof. exact (@lem3106936 (NUMERAL 0) term131). Qed.
Lemma lem3106938 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106939 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106940 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106939 h1) (fun h1 : term446 = True => @lem3106938)). Qed.
Lemma lem3106941 : term446 = True.
Proof. exact (EQ_MP (@lem3106940) (@lem3106938)). Qed.
Lemma lem3106942 : term440 = True.
Proof. exact (TRANS (@lem3106937) (@lem3106941)). Qed.
Lemma lem3106943 : True = term440.
Proof. exact (SYM (@lem3106942)). Qed.
Lemma lem3106944 : term440.
Proof. exact (EQ_MP (@lem3106943) (@lem0)). Qed.
Lemma lem3106945 : term443 = term449.
Proof. exact (@lem3106934 (@lem3106944)). Qed.
Lemma lem3106947 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3106948 : term272 = term273.
Proof. exact (@lem3106947 term131 term131). Qed.
Lemma lem3106949 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3106950 : term275 = term131.
Proof. exact (EQ_MP (@lem3106949) (@lem940073)). Qed.
Lemma lem3106951 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3106952 : term273 = term224.
Proof. exact (MK_COMB (@lem3106951) (@lem3106950)). Qed.
Lemma lem3106953 : term272 = term224.
Proof. exact (TRANS (@lem3106948) (@lem3106952)). Qed.
Lemma lem3106955 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3106956 : term451 = term217.
Proof. exact (@lem3106955 term131). Qed.
Lemma lem3106957 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3106958 : term452 = term441.
Proof. exact (MK_COMB (@lem3106957) (@lem3106956)). Qed.
Lemma lem3106959 : term449 = term440.
Proof. exact (MK_COMB (@lem3106958) (@lem3106953)). Qed.
Lemma lem3106961 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3106962 : term440 = term446.
Proof. exact (@lem3106961 (NUMERAL 0) term131). Qed.
Lemma lem3106963 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3106964 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3106965 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3106964 h1) (fun h1 : term446 = True => @lem3106963)). Qed.
Lemma lem3106966 : term446 = True.
Proof. exact (EQ_MP (@lem3106965) (@lem3106963)). Qed.
Lemma lem3106967 : term440 = True.
Proof. exact (TRANS (@lem3106962) (@lem3106966)). Qed.
Lemma lem3106968 : term449 = True.
Proof. exact (TRANS (@lem3106959) (@lem3106967)). Qed.
Lemma lem3106969 : term443 = True.
Proof. exact (TRANS (@lem3106945) (@lem3106968)). Qed.
Lemma lem3106970 : term440 = True.
Proof. exact (TRANS (@lem3106922) (@lem3106969)). Qed.
Lemma lem3106971 : term439 = True.
Proof. exact (TRANS (@lem3106913) (@lem3106970)). Qed.
Lemma lem3106972 : True = term439.
Proof. exact (SYM (@lem3106971)). Qed.
Lemma lem3106973 : term439.
Proof. exact (EQ_MP (@lem3106972) (@lem0)). Qed.
Lemma lem3106974 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term555 _32231 _32232.
Proof. exact (conj (@lem3106973) (@lem3106835 _32231 _32232 h1)). Qed.
Lemma lem3106976 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3106977 (_32231 : int) (_32232 : int) : term556 _32231 _32232.
Proof. exact (@lem3106976 term224 (term311 _32231 _32232)). Qed.
Lemma lem3106978 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term557 _32231 _32232.
Proof. exact (@lem3106977 _32231 _32232 (@lem3106974 _32231 _32232 h1)). Qed.
Lemma lem3106979 (_32231 : int) (_32232 : int) : (term558 _32231 _32232) = (term311 _32231 _32232).
Proof. exact (@lem1982733 (term311 _32231 _32232)). Qed.
Lemma lem3106980 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3106981 (_32231 : int) (_32232 : int) : (term559 _32231 _32232) = (term313 _32231 _32232).
Proof. exact (MK_COMB (@lem3106980) (@lem3106979 _32231 _32232)). Qed.
Lemma lem3106982 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3106983 (_32231 : int) (_32232 : int) : (term557 _32231 _32232) = (term314 _32231 _32232).
Proof. exact (MK_COMB (@lem3106981 _32231 _32232) (@lem3106982)). Qed.
Lemma lem3106984 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term314 _32231 _32232.
Proof. exact (EQ_MP (@lem3106983 _32231 _32232) (@lem3106978 _32231 _32232 h1)). Qed.
Lemma lem3106985 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term560 _32231 _32232.
Proof. exact (conj (@lem3106984 _32231 _32232 h1) (@lem3106910 _32231 _32232 h1)). Qed.
Lemma lem3106987 (x : real) (y : real) : term465 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3106988 (_32231 : int) (_32232 : int) : term561 _32231 _32232.
Proof. exact (@lem3106987 (term311 _32231 _32232) (term325 _32231 _32232)). Qed.
Lemma lem3106989 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term562 _32231 _32232.
Proof. exact (@lem3106988 _32231 _32232 (@lem3106985 _32231 _32232 h1)). Qed.
Lemma lem3106990 (_32231 : int) (_32232 : int) : (term563 _32231 _32232) = (term564 _32231 _32232).
Proof. exact (@lem1982753 (term312 _32231) (real_of_int _32231) (real_of_int _32232) (term324 _32232)). Qed.
Lemma lem3106991 (_32231 : int) : (term493 _32231) = (term471 _32231).
Proof. exact (@lem1982713 term263 (real_of_int _32231)). Qed.
Lemma lem3106993 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3106994 : term224 = term287.
Proof. exact (@lem3106993 term131). Qed.
Lemma lem3106996 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3106997 : term263 = term264.
Proof. exact (@lem3106996 term131). Qed.
Lemma lem3106998 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3106999 : term472 = term473.
Proof. exact (MK_COMB (@lem3106998) (@lem3106997)). Qed.
Lemma lem3107000 : term474 = term475.
Proof. exact (MK_COMB (@lem3106999) (@lem3106994)). Qed.
Lemma lem3107001 : term476.
Proof. exact (@lem1981473 term263 term224 term224 term224 term217 term224). Qed.
Lemma lem3107003 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107004 : term440 = term446.
Proof. exact (@lem3107003 (NUMERAL 0) term131). Qed.
Lemma lem3107005 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107006 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107007 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107006 h1) (fun h1 : term446 = True => @lem3107005)). Qed.
Lemma lem3107008 : term446 = True.
Proof. exact (EQ_MP (@lem3107007) (@lem3107005)). Qed.
Lemma lem3107009 : term440 = True.
Proof. exact (TRANS (@lem3107004) (@lem3107008)). Qed.
Lemma lem3107010 : True = term440.
Proof. exact (SYM (@lem3107009)). Qed.
Lemma lem3107011 : term440.
Proof. exact (EQ_MP (@lem3107010) (@lem0)). Qed.
Lemma lem3107012 : term477.
Proof. exact (@lem3107001 (@lem3107011)). Qed.
Lemma lem3107014 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107015 : term440 = term446.
Proof. exact (@lem3107014 (NUMERAL 0) term131). Qed.
Lemma lem3107016 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107017 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107018 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107017 h1) (fun h1 : term446 = True => @lem3107016)). Qed.
Lemma lem3107019 : term446 = True.
Proof. exact (EQ_MP (@lem3107018) (@lem3107016)). Qed.
Lemma lem3107020 : term440 = True.
Proof. exact (TRANS (@lem3107015) (@lem3107019)). Qed.
Lemma lem3107021 : True = term440.
Proof. exact (SYM (@lem3107020)). Qed.
Lemma lem3107022 : term440.
Proof. exact (EQ_MP (@lem3107021) (@lem0)). Qed.
Lemma lem3107023 : term478.
Proof. exact (@lem3107012 (@lem3107022)). Qed.
Lemma lem3107025 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107026 : term440 = term446.
Proof. exact (@lem3107025 (NUMERAL 0) term131). Qed.
Lemma lem3107027 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107028 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107029 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107028 h1) (fun h1 : term446 = True => @lem3107027)). Qed.
Lemma lem3107030 : term446 = True.
Proof. exact (EQ_MP (@lem3107029) (@lem3107027)). Qed.
Lemma lem3107031 : term440 = True.
Proof. exact (TRANS (@lem3107026) (@lem3107030)). Qed.
Lemma lem3107032 : True = term440.
Proof. exact (SYM (@lem3107031)). Qed.
Lemma lem3107033 : term440.
Proof. exact (EQ_MP (@lem3107032) (@lem0)). Qed.
Lemma lem3107034 : term479.
Proof. exact (@lem3107023 (@lem3107033)). Qed.
Lemma lem3107036 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3107037 : term272 = term273.
Proof. exact (@lem3107036 term131 term131). Qed.
Lemma lem3107038 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107039 : term275 = term131.
Proof. exact (EQ_MP (@lem3107038) (@lem940073)). Qed.
Lemma lem3107040 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107041 : term273 = term224.
Proof. exact (MK_COMB (@lem3107040) (@lem3107039)). Qed.
Lemma lem3107042 : term272 = term224.
Proof. exact (TRANS (@lem3107037) (@lem3107041)). Qed.
Lemma lem3107044 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3107045 : term288 = term293.
Proof. exact (@lem3107044 term131 term131). Qed.
Lemma lem3107046 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107047 : term275 = term131.
Proof. exact (EQ_MP (@lem3107046) (@lem940073)). Qed.
Lemma lem3107048 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107049 : term273 = term224.
Proof. exact (MK_COMB (@lem3107048) (@lem3107047)). Qed.
Lemma lem3107050 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3107051 : term293 = term263.
Proof. exact (MK_COMB (@lem3107050) (@lem3107049)). Qed.
Lemma lem3107052 : term288 = term263.
Proof. exact (TRANS (@lem3107045) (@lem3107051)). Qed.
Lemma lem3107053 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3107054 : term480 = term472.
Proof. exact (MK_COMB (@lem3107053) (@lem3107052)). Qed.
Lemma lem3107055 : term481 = term474.
Proof. exact (MK_COMB (@lem3107054) (@lem3107042)). Qed.
Lemma lem3107057 (m : nat) : (term482 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3107058 : term474 = term217.
Proof. exact (@lem3107057 term131). Qed.
Lemma lem3107059 : term481 = term217.
Proof. exact (TRANS (@lem3107055) (@lem3107058)). Qed.
Lemma lem3107060 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3107061 : term483 = term484.
Proof. exact (MK_COMB (@lem3107060) (@lem3107059)). Qed.
Lemma lem3107062 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem3107063 : term485 = term451.
Proof. exact (MK_COMB (@lem3107061) (@lem3107062)). Qed.
Lemma lem3107065 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107066 : term451 = term217.
Proof. exact (@lem3107065 term131). Qed.
Lemma lem3107067 : term485 = term217.
Proof. exact (TRANS (@lem3107063) (@lem3107066)). Qed.
Lemma lem3107069 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3107070 : term272 = term273.
Proof. exact (@lem3107069 term131 term131). Qed.
Lemma lem3107071 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107072 : term275 = term131.
Proof. exact (EQ_MP (@lem3107071) (@lem940073)). Qed.
Lemma lem3107073 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107074 : term273 = term224.
Proof. exact (MK_COMB (@lem3107073) (@lem3107072)). Qed.
Lemma lem3107075 : term272 = term224.
Proof. exact (TRANS (@lem3107070) (@lem3107074)). Qed.
Lemma lem3107076 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem3107077 : term486 = term451.
Proof. exact (MK_COMB (@lem3107076) (@lem3107075)). Qed.
Lemma lem3107079 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107080 : term451 = term217.
Proof. exact (@lem3107079 term131). Qed.
Lemma lem3107081 : term486 = term217.
Proof. exact (TRANS (@lem3107077) (@lem3107080)). Qed.
Lemma lem3107082 : term217 = term486.
Proof. exact (SYM (@lem3107081)). Qed.
Lemma lem3107083 : term485 = term486.
Proof. exact (TRANS (@lem3107067) (@lem3107082)). Qed.
Lemma lem3107084 : term475 = term260.
Proof. exact (@lem3107034 (@lem3107083)). Qed.
Lemma lem3107085 : term474 = term260.
Proof. exact (TRANS (@lem3107000) (@lem3107084)). Qed.
Lemma lem3107087 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3107088 : term260 = term217.
Proof. exact (@lem3107087 term217). Qed.
Lemma lem3107089 : term474 = term217.
Proof. exact (TRANS (@lem3107085) (@lem3107088)). Qed.
Lemma lem3107090 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3107091 : term487 = term484.
Proof. exact (MK_COMB (@lem3107090) (@lem3107089)). Qed.
Lemma lem3107092 (_32231 : int) : (real_of_int _32231) = (real_of_int _32231).
Proof. exact (eq_refl (real_of_int _32231)). Qed.
Lemma lem3107093 (_32231 : int) : (term471 _32231) = (term488 _32231).
Proof. exact (MK_COMB (@lem3107091) (@lem3107092 _32231)). Qed.
Lemma lem3107094 (_32231 : int) : (term493 _32231) = (term488 _32231).
Proof. exact (TRANS (@lem3106991 _32231) (@lem3107093 _32231)). Qed.
Lemma lem3107095 (_32231 : int) : (term488 _32231) = term217.
Proof. exact (@lem1982719 (real_of_int _32231)). Qed.
Lemma lem3107096 (_32231 : int) : (term493 _32231) = term217.
Proof. exact (TRANS (@lem3107094 _32231) (@lem3107095 _32231)). Qed.
Lemma lem3107097 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3107098 (_32231 : int) : (term494 _32231) = term490.
Proof. exact (MK_COMB (@lem3107097) (@lem3107096 _32231)). Qed.
Lemma lem3107099 (_32232 : int) : (term546 _32232) = (term547 _32232).
Proof. exact (@lem1982763 (real_of_int _32232) (term312 _32232) term263). Qed.
Lemma lem3107100 (_32232 : int) : (term470 _32232) = (term471 _32232).
Proof. exact (@lem1982715 term263 (real_of_int _32232)). Qed.
Lemma lem3107102 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107103 : term224 = term287.
Proof. exact (@lem3107102 term131). Qed.
Lemma lem3107105 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3107106 : term263 = term264.
Proof. exact (@lem3107105 term131). Qed.
Lemma lem3107107 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3107108 : term472 = term473.
Proof. exact (MK_COMB (@lem3107107) (@lem3107106)). Qed.
Lemma lem3107109 : term474 = term475.
Proof. exact (MK_COMB (@lem3107108) (@lem3107103)). Qed.
Lemma lem3107110 : term476.
Proof. exact (@lem1981473 term263 term224 term224 term224 term217 term224). Qed.
Lemma lem3107112 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107113 : term440 = term446.
Proof. exact (@lem3107112 (NUMERAL 0) term131). Qed.
Lemma lem3107114 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107115 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107116 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107115 h1) (fun h1 : term446 = True => @lem3107114)). Qed.
Lemma lem3107117 : term446 = True.
Proof. exact (EQ_MP (@lem3107116) (@lem3107114)). Qed.
Lemma lem3107118 : term440 = True.
Proof. exact (TRANS (@lem3107113) (@lem3107117)). Qed.
Lemma lem3107119 : True = term440.
Proof. exact (SYM (@lem3107118)). Qed.
Lemma lem3107120 : term440.
Proof. exact (EQ_MP (@lem3107119) (@lem0)). Qed.
Lemma lem3107121 : term477.
Proof. exact (@lem3107110 (@lem3107120)). Qed.
Lemma lem3107123 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107124 : term440 = term446.
Proof. exact (@lem3107123 (NUMERAL 0) term131). Qed.
Lemma lem3107125 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107126 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107127 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107126 h1) (fun h1 : term446 = True => @lem3107125)). Qed.
Lemma lem3107128 : term446 = True.
Proof. exact (EQ_MP (@lem3107127) (@lem3107125)). Qed.
Lemma lem3107129 : term440 = True.
Proof. exact (TRANS (@lem3107124) (@lem3107128)). Qed.
Lemma lem3107130 : True = term440.
Proof. exact (SYM (@lem3107129)). Qed.
Lemma lem3107131 : term440.
Proof. exact (EQ_MP (@lem3107130) (@lem0)). Qed.
Lemma lem3107132 : term478.
Proof. exact (@lem3107121 (@lem3107131)). Qed.
Lemma lem3107134 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107135 : term440 = term446.
Proof. exact (@lem3107134 (NUMERAL 0) term131). Qed.
Lemma lem3107136 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107137 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107138 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107137 h1) (fun h1 : term446 = True => @lem3107136)). Qed.
Lemma lem3107139 : term446 = True.
Proof. exact (EQ_MP (@lem3107138) (@lem3107136)). Qed.
Lemma lem3107140 : term440 = True.
Proof. exact (TRANS (@lem3107135) (@lem3107139)). Qed.
Lemma lem3107141 : True = term440.
Proof. exact (SYM (@lem3107140)). Qed.
Lemma lem3107142 : term440.
Proof. exact (EQ_MP (@lem3107141) (@lem0)). Qed.
Lemma lem3107143 : term479.
Proof. exact (@lem3107132 (@lem3107142)). Qed.
Lemma lem3107145 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3107146 : term272 = term273.
Proof. exact (@lem3107145 term131 term131). Qed.
Lemma lem3107147 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107148 : term275 = term131.
Proof. exact (EQ_MP (@lem3107147) (@lem940073)). Qed.
Lemma lem3107149 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107150 : term273 = term224.
Proof. exact (MK_COMB (@lem3107149) (@lem3107148)). Qed.
Lemma lem3107151 : term272 = term224.
Proof. exact (TRANS (@lem3107146) (@lem3107150)). Qed.
Lemma lem3107153 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3107154 : term288 = term293.
Proof. exact (@lem3107153 term131 term131). Qed.
Lemma lem3107155 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107156 : term275 = term131.
Proof. exact (EQ_MP (@lem3107155) (@lem940073)). Qed.
Lemma lem3107157 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107158 : term273 = term224.
Proof. exact (MK_COMB (@lem3107157) (@lem3107156)). Qed.
Lemma lem3107159 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3107160 : term293 = term263.
Proof. exact (MK_COMB (@lem3107159) (@lem3107158)). Qed.
Lemma lem3107161 : term288 = term263.
Proof. exact (TRANS (@lem3107154) (@lem3107160)). Qed.
Lemma lem3107162 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3107163 : term480 = term472.
Proof. exact (MK_COMB (@lem3107162) (@lem3107161)). Qed.
Lemma lem3107164 : term481 = term474.
Proof. exact (MK_COMB (@lem3107163) (@lem3107151)). Qed.
Lemma lem3107166 (m : nat) : (term482 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3107167 : term474 = term217.
Proof. exact (@lem3107166 term131). Qed.
Lemma lem3107168 : term481 = term217.
Proof. exact (TRANS (@lem3107164) (@lem3107167)). Qed.
Lemma lem3107169 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3107170 : term483 = term484.
Proof. exact (MK_COMB (@lem3107169) (@lem3107168)). Qed.
Lemma lem3107171 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem3107172 : term485 = term451.
Proof. exact (MK_COMB (@lem3107170) (@lem3107171)). Qed.
Lemma lem3107174 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107175 : term451 = term217.
Proof. exact (@lem3107174 term131). Qed.
Lemma lem3107176 : term485 = term217.
Proof. exact (TRANS (@lem3107172) (@lem3107175)). Qed.
Lemma lem3107178 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3107179 : term272 = term273.
Proof. exact (@lem3107178 term131 term131). Qed.
Lemma lem3107180 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107181 : term275 = term131.
Proof. exact (EQ_MP (@lem3107180) (@lem940073)). Qed.
Lemma lem3107182 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107183 : term273 = term224.
Proof. exact (MK_COMB (@lem3107182) (@lem3107181)). Qed.
Lemma lem3107184 : term272 = term224.
Proof. exact (TRANS (@lem3107179) (@lem3107183)). Qed.
Lemma lem3107185 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem3107186 : term486 = term451.
Proof. exact (MK_COMB (@lem3107185) (@lem3107184)). Qed.
Lemma lem3107188 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107189 : term451 = term217.
Proof. exact (@lem3107188 term131). Qed.
Lemma lem3107190 : term486 = term217.
Proof. exact (TRANS (@lem3107186) (@lem3107189)). Qed.
Lemma lem3107191 : term217 = term486.
Proof. exact (SYM (@lem3107190)). Qed.
Lemma lem3107192 : term485 = term486.
Proof. exact (TRANS (@lem3107176) (@lem3107191)). Qed.
Lemma lem3107193 : term475 = term260.
Proof. exact (@lem3107143 (@lem3107192)). Qed.
Lemma lem3107194 : term474 = term260.
Proof. exact (TRANS (@lem3107109) (@lem3107193)). Qed.
Lemma lem3107196 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3107197 : term260 = term217.
Proof. exact (@lem3107196 term217). Qed.
Lemma lem3107198 : term474 = term217.
Proof. exact (TRANS (@lem3107194) (@lem3107197)). Qed.
Lemma lem3107199 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3107200 : term487 = term484.
Proof. exact (MK_COMB (@lem3107199) (@lem3107198)). Qed.
Lemma lem3107201 (_32232 : int) : (real_of_int _32232) = (real_of_int _32232).
Proof. exact (eq_refl (real_of_int _32232)). Qed.
Lemma lem3107202 (_32232 : int) : (term471 _32232) = (term488 _32232).
Proof. exact (MK_COMB (@lem3107200) (@lem3107201 _32232)). Qed.
Lemma lem3107203 (_32232 : int) : (term470 _32232) = (term488 _32232).
Proof. exact (TRANS (@lem3107100 _32232) (@lem3107202 _32232)). Qed.
Lemma lem3107204 (_32232 : int) : (term488 _32232) = term217.
Proof. exact (@lem1982719 (real_of_int _32232)). Qed.
Lemma lem3107205 (_32232 : int) : (term470 _32232) = term217.
Proof. exact (TRANS (@lem3107203 _32232) (@lem3107204 _32232)). Qed.
Lemma lem3107206 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3107207 (_32232 : int) : (term489 _32232) = term490.
Proof. exact (MK_COMB (@lem3107206) (@lem3107205 _32232)). Qed.
Lemma lem3107208 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem3107209 (_32232 : int) : (term547 _32232) = term495.
Proof. exact (MK_COMB (@lem3107207 _32232) (@lem3107208)). Qed.
Lemma lem3107210 (_32232 : int) : (term546 _32232) = term495.
Proof. exact (TRANS (@lem3107099 _32232) (@lem3107209 _32232)). Qed.
Lemma lem3107211 : term495 = term263.
Proof. exact (@lem1982721 term263). Qed.
Lemma lem3107212 (_32232 : int) : (term546 _32232) = term263.
Proof. exact (TRANS (@lem3107210 _32232) (@lem3107211)). Qed.
Lemma lem3107213 (_32231 : int) (_32232 : int) : (term564 _32231 _32232) = term495.
Proof. exact (MK_COMB (@lem3107098 _32231) (@lem3107212 _32232)). Qed.
Lemma lem3107214 (_32231 : int) (_32232 : int) : (term563 _32231 _32232) = term495.
Proof. exact (TRANS (@lem3106990 _32231 _32232) (@lem3107213 _32231 _32232)). Qed.
Lemma lem3107215 : term495 = term263.
Proof. exact (@lem1982721 term263). Qed.
Lemma lem3107216 (_32231 : int) (_32232 : int) : (term563 _32231 _32232) = term263.
Proof. exact (TRANS (@lem3107214 _32231 _32232) (@lem3107215)). Qed.
Lemma lem3107217 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3107218 (_32231 : int) (_32232 : int) : (term565 _32231 _32232) = term497.
Proof. exact (MK_COMB (@lem3107217) (@lem3107216 _32231 _32232)). Qed.
Lemma lem3107219 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3107220 (_32231 : int) (_32232 : int) : (term562 _32231 _32232) = term498.
Proof. exact (MK_COMB (@lem3107218 _32231 _32232) (@lem3107219)). Qed.
Lemma lem3107221 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : term498.
Proof. exact (EQ_MP (@lem3107220 _32231 _32232) (@lem3106989 _32231 _32232 h1)). Qed.
Lemma lem3107223 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3107224 : term498 = term499.
Proof. exact (@lem3107223 term217 term263). Qed.
Lemma lem3107226 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3107227 : term263 = term264.
Proof. exact (@lem3107226 term131). Qed.
Lemma lem3107229 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107230 : term217 = term260.
Proof. exact (@lem3107229 (NUMERAL 0)). Qed.
Lemma lem3107231 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3107232 : term219 = term500.
Proof. exact (MK_COMB (@lem3107231) (@lem3107230)). Qed.
Lemma lem3107233 : term499 = term501.
Proof. exact (MK_COMB (@lem3107232) (@lem3107227)). Qed.
Lemma lem3107234 : term502.
Proof. exact (@lem1980026 term217 term224 term263 term224). Qed.
Lemma lem3107236 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107237 : term440 = term446.
Proof. exact (@lem3107236 (NUMERAL 0) term131). Qed.
Lemma lem3107238 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107239 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107240 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107239 h1) (fun h1 : term446 = True => @lem3107238)). Qed.
Lemma lem3107241 : term446 = True.
Proof. exact (EQ_MP (@lem3107240) (@lem3107238)). Qed.
Lemma lem3107242 : term440 = True.
Proof. exact (TRANS (@lem3107237) (@lem3107241)). Qed.
Lemma lem3107243 : True = term440.
Proof. exact (SYM (@lem3107242)). Qed.
Lemma lem3107244 : term440.
Proof. exact (EQ_MP (@lem3107243) (@lem0)). Qed.
Lemma lem3107245 : term503.
Proof. exact (@lem3107234 (@lem3107244)). Qed.
Lemma lem3107247 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107248 : term440 = term446.
Proof. exact (@lem3107247 (NUMERAL 0) term131). Qed.
Lemma lem3107249 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107250 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107251 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107250 h1) (fun h1 : term446 = True => @lem3107249)). Qed.
Lemma lem3107252 : term446 = True.
Proof. exact (EQ_MP (@lem3107251) (@lem3107249)). Qed.
Lemma lem3107253 : term440 = True.
Proof. exact (TRANS (@lem3107248) (@lem3107252)). Qed.
Lemma lem3107254 : True = term440.
Proof. exact (SYM (@lem3107253)). Qed.
Lemma lem3107255 : term440.
Proof. exact (EQ_MP (@lem3107254) (@lem0)). Qed.
Lemma lem3107256 : term501 = term504.
Proof. exact (@lem3107245 (@lem3107255)). Qed.
Lemma lem3107258 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3107259 : term288 = term293.
Proof. exact (@lem3107258 term131 term131). Qed.
Lemma lem3107260 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107261 : term275 = term131.
Proof. exact (EQ_MP (@lem3107260) (@lem940073)). Qed.
Lemma lem3107262 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107263 : term273 = term224.
Proof. exact (MK_COMB (@lem3107262) (@lem3107261)). Qed.
Lemma lem3107264 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3107265 : term293 = term263.
Proof. exact (MK_COMB (@lem3107264) (@lem3107263)). Qed.
Lemma lem3107266 : term288 = term263.
Proof. exact (TRANS (@lem3107259) (@lem3107265)). Qed.
Lemma lem3107268 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107269 : term451 = term217.
Proof. exact (@lem3107268 term131). Qed.
Lemma lem3107270 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3107271 : term505 = term219.
Proof. exact (MK_COMB (@lem3107270) (@lem3107269)). Qed.
Lemma lem3107272 : term504 = term499.
Proof. exact (MK_COMB (@lem3107271) (@lem3107266)). Qed.
Lemma lem3107274 (m : nat) (n : nat) : (term506 m n) = (term507 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3107275 : term499 = term508.
Proof. exact (@lem3107274 (NUMERAL 0) term131). Qed.
Lemma lem3107276 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107277 (h1 : term447 = (BIT1 0)) : (term131 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3107278 : (term447 = (BIT1 0)) = ((term131 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107277 h1) (fun h1 : (term131 = (NUMERAL 0)) = False => @lem3107276)). Qed.
Lemma lem3107279 : (term131 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3107278) (@lem3107276)). Qed.
Lemma lem3107280 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3107281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3107282 : term509 = (and True).
Proof. exact (MK_COMB (@lem3107281) (@lem3107280)). Qed.
Lemma lem3107283 : term508 = (True /\ False).
Proof. exact (MK_COMB (@lem3107282) (@lem3107279)). Qed.
Lemma lem3107285 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3107286 : term508 = False.
Proof. exact (TRANS (@lem3107283) (@lem3107285)). Qed.
Lemma lem3107287 : term499 = False.
Proof. exact (TRANS (@lem3107275) (@lem3107286)). Qed.
Lemma lem3107288 : term504 = False.
Proof. exact (TRANS (@lem3107272) (@lem3107287)). Qed.
Lemma lem3107289 : term501 = False.
Proof. exact (TRANS (@lem3107256) (@lem3107288)). Qed.
Lemma lem3107290 : term499 = False.
Proof. exact (TRANS (@lem3107233) (@lem3107289)). Qed.
Lemma lem3107291 : term498 = False.
Proof. exact (TRANS (@lem3107224) (@lem3107290)). Qed.
Lemma lem3107292 (_32231 : int) (_32232 : int) (h1 : term549 _32231 _32232) : False.
Proof. exact (EQ_MP (@lem3107291) (@lem3107221 _32231 _32232 h1)). Qed.
Lemma lem3107293 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term566 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3107294 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term418 _32231 _32232.
Proof. exact (proj2 (@lem3107293 _32231 _32232 h1)). Qed.
Lemma lem3107296 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term387 _32231 _32232.
Proof. exact (proj2 (@lem3107294 _32231 _32232 h1)). Qed.
Lemma lem3107298 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term353 _32231 _32232.
Proof. exact (proj2 (@lem3107296 _32231 _32232 h1)). Qed.
Lemma lem3107299 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : (real_of_int _32231) = term217.
Proof. exact (proj1 (@lem3107296 _32231 _32232 h1)). Qed.
Lemma lem3107301 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term315 _32231 _32232.
Proof. exact (proj1 (@lem3107298 _32231 _32232 h1)). Qed.
Lemma lem3107303 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term299 _32231.
Proof. exact (proj1 (@lem3107301 _32231 _32232 h1)). Qed.
Lemma lem3107305 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3107306 : term439 = term440.
Proof. exact (@lem3107305 term217 term224). Qed.
Lemma lem3107308 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107309 : term224 = term287.
Proof. exact (@lem3107308 term131). Qed.
Lemma lem3107311 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107312 : term217 = term260.
Proof. exact (@lem3107311 (NUMERAL 0)). Qed.
Lemma lem3107313 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3107314 : term441 = term442.
Proof. exact (MK_COMB (@lem3107313) (@lem3107312)). Qed.
Lemma lem3107315 : term440 = term443.
Proof. exact (MK_COMB (@lem3107314) (@lem3107309)). Qed.
Lemma lem3107316 : term444.
Proof. exact (@lem1980255 term217 term224 term224 term224). Qed.
Lemma lem3107318 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107319 : term440 = term446.
Proof. exact (@lem3107318 (NUMERAL 0) term131). Qed.
Lemma lem3107320 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107321 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107322 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107321 h1) (fun h1 : term446 = True => @lem3107320)). Qed.
Lemma lem3107323 : term446 = True.
Proof. exact (EQ_MP (@lem3107322) (@lem3107320)). Qed.
Lemma lem3107324 : term440 = True.
Proof. exact (TRANS (@lem3107319) (@lem3107323)). Qed.
Lemma lem3107325 : True = term440.
Proof. exact (SYM (@lem3107324)). Qed.
Lemma lem3107326 : term440.
Proof. exact (EQ_MP (@lem3107325) (@lem0)). Qed.
Lemma lem3107327 : term448.
Proof. exact (@lem3107316 (@lem3107326)). Qed.
Lemma lem3107329 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107330 : term440 = term446.
Proof. exact (@lem3107329 (NUMERAL 0) term131). Qed.
Lemma lem3107331 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107332 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107333 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107332 h1) (fun h1 : term446 = True => @lem3107331)). Qed.
Lemma lem3107334 : term446 = True.
Proof. exact (EQ_MP (@lem3107333) (@lem3107331)). Qed.
Lemma lem3107335 : term440 = True.
Proof. exact (TRANS (@lem3107330) (@lem3107334)). Qed.
Lemma lem3107336 : True = term440.
Proof. exact (SYM (@lem3107335)). Qed.
Lemma lem3107337 : term440.
Proof. exact (EQ_MP (@lem3107336) (@lem0)). Qed.
Lemma lem3107338 : term443 = term449.
Proof. exact (@lem3107327 (@lem3107337)). Qed.
Lemma lem3107340 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3107341 : term272 = term273.
Proof. exact (@lem3107340 term131 term131). Qed.
Lemma lem3107342 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107343 : term275 = term131.
Proof. exact (EQ_MP (@lem3107342) (@lem940073)). Qed.
Lemma lem3107344 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107345 : term273 = term224.
Proof. exact (MK_COMB (@lem3107344) (@lem3107343)). Qed.
Lemma lem3107346 : term272 = term224.
Proof. exact (TRANS (@lem3107341) (@lem3107345)). Qed.
Lemma lem3107348 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107349 : term451 = term217.
Proof. exact (@lem3107348 term131). Qed.
Lemma lem3107350 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3107351 : term452 = term441.
Proof. exact (MK_COMB (@lem3107350) (@lem3107349)). Qed.
Lemma lem3107352 : term449 = term440.
Proof. exact (MK_COMB (@lem3107351) (@lem3107346)). Qed.
Lemma lem3107354 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107355 : term440 = term446.
Proof. exact (@lem3107354 (NUMERAL 0) term131). Qed.
Lemma lem3107356 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107357 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107358 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107357 h1) (fun h1 : term446 = True => @lem3107356)). Qed.
Lemma lem3107359 : term446 = True.
Proof. exact (EQ_MP (@lem3107358) (@lem3107356)). Qed.
Lemma lem3107360 : term440 = True.
Proof. exact (TRANS (@lem3107355) (@lem3107359)). Qed.
Lemma lem3107361 : term449 = True.
Proof. exact (TRANS (@lem3107352) (@lem3107360)). Qed.
Lemma lem3107362 : term443 = True.
Proof. exact (TRANS (@lem3107338) (@lem3107361)). Qed.
Lemma lem3107363 : term440 = True.
Proof. exact (TRANS (@lem3107315) (@lem3107362)). Qed.
Lemma lem3107364 : term439 = True.
Proof. exact (TRANS (@lem3107306) (@lem3107363)). Qed.
Lemma lem3107365 : True = term439.
Proof. exact (SYM (@lem3107364)). Qed.
Lemma lem3107366 : term439.
Proof. exact (EQ_MP (@lem3107365) (@lem0)). Qed.
Lemma lem3107367 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term511 _32231.
Proof. exact (conj (@lem3107366) (@lem3107303 _32231 _32232 h1)). Qed.
Lemma lem3107369 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3107370 (_32231 : int) : term512 _32231.
Proof. exact (@lem3107369 term224 (term296 _32231)). Qed.
Lemma lem3107371 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term513 _32231.
Proof. exact (@lem3107370 _32231 (@lem3107367 _32231 _32232 h1)). Qed.
Lemma lem3107372 (_32231 : int) : (term514 _32231) = (term296 _32231).
Proof. exact (@lem1982733 (term296 _32231)). Qed.
Lemma lem3107373 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3107374 (_32231 : int) : (term515 _32231) = (term298 _32231).
Proof. exact (MK_COMB (@lem3107373) (@lem3107372 _32231)). Qed.
Lemma lem3107375 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3107376 (_32231 : int) : (term513 _32231) = (term299 _32231).
Proof. exact (MK_COMB (@lem3107374 _32231) (@lem3107375)). Qed.
Lemma lem3107377 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term299 _32231.
Proof. exact (EQ_MP (@lem3107376 _32231) (@lem3107371 _32231 _32232 h1)). Qed.
Lemma lem3107379 (y : real) : term516 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3107380 (_32231 : int) : term517 _32231.
Proof. exact (@lem3107379 (real_of_int _32231)). Qed.
Lemma lem3107381 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term518 _32231.
Proof. exact (@lem3107380 _32231 (@lem3107299 _32231 _32232 h1)). Qed.
Lemma lem3107382 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term519 _32231.
Proof. exact (@lem3107381 _32231 _32232 h1 term263). Qed.
Lemma lem3107383 (_32231 : int) : (term519 _32231) = ((term312 _32231) = term217).
Proof. exact (eq_refl (term519 _32231)). Qed.
Lemma lem3107390 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : (term312 _32231) = term217.
Proof. exact (EQ_MP (@lem3107383 _32231) (@lem3107382 _32231 _32232 h1)). Qed.
Lemma lem3107391 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term520 _32231.
Proof. exact (conj (@lem3107390 _32231 _32232 h1) (@lem3107377 _32231 _32232 h1)). Qed.
Lemma lem3107393 (x : real) (y : real) : term521 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3107394 (_32231 : int) : term522 _32231.
Proof. exact (@lem3107393 (term312 _32231) (term296 _32231)). Qed.
Lemma lem3107395 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term523 _32231.
Proof. exact (@lem3107394 _32231 (@lem3107391 _32231 _32232 h1)). Qed.
Lemma lem3107396 (_32231 : int) : (term491 _32231) = (term492 _32231).
Proof. exact (@lem1982763 (term312 _32231) (real_of_int _32231) term263). Qed.
Lemma lem3107397 (_32231 : int) : (term493 _32231) = (term471 _32231).
Proof. exact (@lem1982713 term263 (real_of_int _32231)). Qed.
Lemma lem3107399 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107400 : term224 = term287.
Proof. exact (@lem3107399 term131). Qed.
Lemma lem3107402 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3107403 : term263 = term264.
Proof. exact (@lem3107402 term131). Qed.
Lemma lem3107404 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3107405 : term472 = term473.
Proof. exact (MK_COMB (@lem3107404) (@lem3107403)). Qed.
Lemma lem3107406 : term474 = term475.
Proof. exact (MK_COMB (@lem3107405) (@lem3107400)). Qed.
Lemma lem3107407 : term476.
Proof. exact (@lem1981473 term263 term224 term224 term224 term217 term224). Qed.
Lemma lem3107409 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107410 : term440 = term446.
Proof. exact (@lem3107409 (NUMERAL 0) term131). Qed.
Lemma lem3107411 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107412 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107413 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107412 h1) (fun h1 : term446 = True => @lem3107411)). Qed.
Lemma lem3107414 : term446 = True.
Proof. exact (EQ_MP (@lem3107413) (@lem3107411)). Qed.
Lemma lem3107415 : term440 = True.
Proof. exact (TRANS (@lem3107410) (@lem3107414)). Qed.
Lemma lem3107416 : True = term440.
Proof. exact (SYM (@lem3107415)). Qed.
Lemma lem3107417 : term440.
Proof. exact (EQ_MP (@lem3107416) (@lem0)). Qed.
Lemma lem3107418 : term477.
Proof. exact (@lem3107407 (@lem3107417)). Qed.
Lemma lem3107420 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107421 : term440 = term446.
Proof. exact (@lem3107420 (NUMERAL 0) term131). Qed.
Lemma lem3107422 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107423 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107424 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107423 h1) (fun h1 : term446 = True => @lem3107422)). Qed.
Lemma lem3107425 : term446 = True.
Proof. exact (EQ_MP (@lem3107424) (@lem3107422)). Qed.
Lemma lem3107426 : term440 = True.
Proof. exact (TRANS (@lem3107421) (@lem3107425)). Qed.
Lemma lem3107427 : True = term440.
Proof. exact (SYM (@lem3107426)). Qed.
Lemma lem3107428 : term440.
Proof. exact (EQ_MP (@lem3107427) (@lem0)). Qed.
Lemma lem3107429 : term478.
Proof. exact (@lem3107418 (@lem3107428)). Qed.
Lemma lem3107431 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107432 : term440 = term446.
Proof. exact (@lem3107431 (NUMERAL 0) term131). Qed.
Lemma lem3107433 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107434 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107435 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107434 h1) (fun h1 : term446 = True => @lem3107433)). Qed.
Lemma lem3107436 : term446 = True.
Proof. exact (EQ_MP (@lem3107435) (@lem3107433)). Qed.
Lemma lem3107437 : term440 = True.
Proof. exact (TRANS (@lem3107432) (@lem3107436)). Qed.
Lemma lem3107438 : True = term440.
Proof. exact (SYM (@lem3107437)). Qed.
Lemma lem3107439 : term440.
Proof. exact (EQ_MP (@lem3107438) (@lem0)). Qed.
Lemma lem3107440 : term479.
Proof. exact (@lem3107429 (@lem3107439)). Qed.
Lemma lem3107442 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3107443 : term272 = term273.
Proof. exact (@lem3107442 term131 term131). Qed.
Lemma lem3107444 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107445 : term275 = term131.
Proof. exact (EQ_MP (@lem3107444) (@lem940073)). Qed.
Lemma lem3107446 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107447 : term273 = term224.
Proof. exact (MK_COMB (@lem3107446) (@lem3107445)). Qed.
Lemma lem3107448 : term272 = term224.
Proof. exact (TRANS (@lem3107443) (@lem3107447)). Qed.
Lemma lem3107450 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3107451 : term288 = term293.
Proof. exact (@lem3107450 term131 term131). Qed.
Lemma lem3107452 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107453 : term275 = term131.
Proof. exact (EQ_MP (@lem3107452) (@lem940073)). Qed.
Lemma lem3107454 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107455 : term273 = term224.
Proof. exact (MK_COMB (@lem3107454) (@lem3107453)). Qed.
Lemma lem3107456 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3107457 : term293 = term263.
Proof. exact (MK_COMB (@lem3107456) (@lem3107455)). Qed.
Lemma lem3107458 : term288 = term263.
Proof. exact (TRANS (@lem3107451) (@lem3107457)). Qed.
Lemma lem3107459 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3107460 : term480 = term472.
Proof. exact (MK_COMB (@lem3107459) (@lem3107458)). Qed.
Lemma lem3107461 : term481 = term474.
Proof. exact (MK_COMB (@lem3107460) (@lem3107448)). Qed.
Lemma lem3107463 (m : nat) : (term482 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3107464 : term474 = term217.
Proof. exact (@lem3107463 term131). Qed.
Lemma lem3107465 : term481 = term217.
Proof. exact (TRANS (@lem3107461) (@lem3107464)). Qed.
Lemma lem3107466 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3107467 : term483 = term484.
Proof. exact (MK_COMB (@lem3107466) (@lem3107465)). Qed.
Lemma lem3107468 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem3107469 : term485 = term451.
Proof. exact (MK_COMB (@lem3107467) (@lem3107468)). Qed.
Lemma lem3107471 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107472 : term451 = term217.
Proof. exact (@lem3107471 term131). Qed.
Lemma lem3107473 : term485 = term217.
Proof. exact (TRANS (@lem3107469) (@lem3107472)). Qed.
Lemma lem3107475 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3107476 : term272 = term273.
Proof. exact (@lem3107475 term131 term131). Qed.
Lemma lem3107477 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107478 : term275 = term131.
Proof. exact (EQ_MP (@lem3107477) (@lem940073)). Qed.
Lemma lem3107479 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107480 : term273 = term224.
Proof. exact (MK_COMB (@lem3107479) (@lem3107478)). Qed.
Lemma lem3107481 : term272 = term224.
Proof. exact (TRANS (@lem3107476) (@lem3107480)). Qed.
Lemma lem3107482 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem3107483 : term486 = term451.
Proof. exact (MK_COMB (@lem3107482) (@lem3107481)). Qed.
Lemma lem3107485 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107486 : term451 = term217.
Proof. exact (@lem3107485 term131). Qed.
Lemma lem3107487 : term486 = term217.
Proof. exact (TRANS (@lem3107483) (@lem3107486)). Qed.
Lemma lem3107488 : term217 = term486.
Proof. exact (SYM (@lem3107487)). Qed.
Lemma lem3107489 : term485 = term486.
Proof. exact (TRANS (@lem3107473) (@lem3107488)). Qed.
Lemma lem3107490 : term475 = term260.
Proof. exact (@lem3107440 (@lem3107489)). Qed.
Lemma lem3107491 : term474 = term260.
Proof. exact (TRANS (@lem3107406) (@lem3107490)). Qed.
Lemma lem3107493 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3107494 : term260 = term217.
Proof. exact (@lem3107493 term217). Qed.
Lemma lem3107495 : term474 = term217.
Proof. exact (TRANS (@lem3107491) (@lem3107494)). Qed.
Lemma lem3107496 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3107497 : term487 = term484.
Proof. exact (MK_COMB (@lem3107496) (@lem3107495)). Qed.
Lemma lem3107498 (_32231 : int) : (real_of_int _32231) = (real_of_int _32231).
Proof. exact (eq_refl (real_of_int _32231)). Qed.
Lemma lem3107499 (_32231 : int) : (term471 _32231) = (term488 _32231).
Proof. exact (MK_COMB (@lem3107497) (@lem3107498 _32231)). Qed.
Lemma lem3107500 (_32231 : int) : (term493 _32231) = (term488 _32231).
Proof. exact (TRANS (@lem3107397 _32231) (@lem3107499 _32231)). Qed.
Lemma lem3107501 (_32231 : int) : (term488 _32231) = term217.
Proof. exact (@lem1982719 (real_of_int _32231)). Qed.
Lemma lem3107502 (_32231 : int) : (term493 _32231) = term217.
Proof. exact (TRANS (@lem3107500 _32231) (@lem3107501 _32231)). Qed.
Lemma lem3107503 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3107504 (_32231 : int) : (term494 _32231) = term490.
Proof. exact (MK_COMB (@lem3107503) (@lem3107502 _32231)). Qed.
Lemma lem3107505 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem3107506 (_32231 : int) : (term492 _32231) = term495.
Proof. exact (MK_COMB (@lem3107504 _32231) (@lem3107505)). Qed.
Lemma lem3107507 (_32231 : int) : (term491 _32231) = term495.
Proof. exact (TRANS (@lem3107396 _32231) (@lem3107506 _32231)). Qed.
Lemma lem3107508 : term495 = term263.
Proof. exact (@lem1982721 term263). Qed.
Lemma lem3107509 (_32231 : int) : (term491 _32231) = term263.
Proof. exact (TRANS (@lem3107507 _32231) (@lem3107508)). Qed.
Lemma lem3107510 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3107511 (_32231 : int) : (term524 _32231) = term497.
Proof. exact (MK_COMB (@lem3107510) (@lem3107509 _32231)). Qed.
Lemma lem3107512 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3107513 (_32231 : int) : (term523 _32231) = term498.
Proof. exact (MK_COMB (@lem3107511 _32231) (@lem3107512)). Qed.
Lemma lem3107514 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : term498.
Proof. exact (EQ_MP (@lem3107513 _32231) (@lem3107395 _32231 _32232 h1)). Qed.
Lemma lem3107516 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3107517 : term498 = term499.
Proof. exact (@lem3107516 term217 term263). Qed.
Lemma lem3107519 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3107520 : term263 = term264.
Proof. exact (@lem3107519 term131). Qed.
Lemma lem3107522 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107523 : term217 = term260.
Proof. exact (@lem3107522 (NUMERAL 0)). Qed.
Lemma lem3107524 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3107525 : term219 = term500.
Proof. exact (MK_COMB (@lem3107524) (@lem3107523)). Qed.
Lemma lem3107526 : term499 = term501.
Proof. exact (MK_COMB (@lem3107525) (@lem3107520)). Qed.
Lemma lem3107527 : term502.
Proof. exact (@lem1980026 term217 term224 term263 term224). Qed.
Lemma lem3107529 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107530 : term440 = term446.
Proof. exact (@lem3107529 (NUMERAL 0) term131). Qed.
Lemma lem3107531 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107532 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107533 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107532 h1) (fun h1 : term446 = True => @lem3107531)). Qed.
Lemma lem3107534 : term446 = True.
Proof. exact (EQ_MP (@lem3107533) (@lem3107531)). Qed.
Lemma lem3107535 : term440 = True.
Proof. exact (TRANS (@lem3107530) (@lem3107534)). Qed.
Lemma lem3107536 : True = term440.
Proof. exact (SYM (@lem3107535)). Qed.
Lemma lem3107537 : term440.
Proof. exact (EQ_MP (@lem3107536) (@lem0)). Qed.
Lemma lem3107538 : term503.
Proof. exact (@lem3107527 (@lem3107537)). Qed.
Lemma lem3107540 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107541 : term440 = term446.
Proof. exact (@lem3107540 (NUMERAL 0) term131). Qed.
Lemma lem3107542 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107543 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107544 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107543 h1) (fun h1 : term446 = True => @lem3107542)). Qed.
Lemma lem3107545 : term446 = True.
Proof. exact (EQ_MP (@lem3107544) (@lem3107542)). Qed.
Lemma lem3107546 : term440 = True.
Proof. exact (TRANS (@lem3107541) (@lem3107545)). Qed.
Lemma lem3107547 : True = term440.
Proof. exact (SYM (@lem3107546)). Qed.
Lemma lem3107548 : term440.
Proof. exact (EQ_MP (@lem3107547) (@lem0)). Qed.
Lemma lem3107549 : term501 = term504.
Proof. exact (@lem3107538 (@lem3107548)). Qed.
Lemma lem3107551 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3107552 : term288 = term293.
Proof. exact (@lem3107551 term131 term131). Qed.
Lemma lem3107553 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107554 : term275 = term131.
Proof. exact (EQ_MP (@lem3107553) (@lem940073)). Qed.
Lemma lem3107555 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107556 : term273 = term224.
Proof. exact (MK_COMB (@lem3107555) (@lem3107554)). Qed.
Lemma lem3107557 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3107558 : term293 = term263.
Proof. exact (MK_COMB (@lem3107557) (@lem3107556)). Qed.
Lemma lem3107559 : term288 = term263.
Proof. exact (TRANS (@lem3107552) (@lem3107558)). Qed.
Lemma lem3107561 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107562 : term451 = term217.
Proof. exact (@lem3107561 term131). Qed.
Lemma lem3107563 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3107564 : term505 = term219.
Proof. exact (MK_COMB (@lem3107563) (@lem3107562)). Qed.
Lemma lem3107565 : term504 = term499.
Proof. exact (MK_COMB (@lem3107564) (@lem3107559)). Qed.
Lemma lem3107567 (m : nat) (n : nat) : (term506 m n) = (term507 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3107568 : term499 = term508.
Proof. exact (@lem3107567 (NUMERAL 0) term131). Qed.
Lemma lem3107569 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107570 (h1 : term447 = (BIT1 0)) : (term131 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3107571 : (term447 = (BIT1 0)) = ((term131 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107570 h1) (fun h1 : (term131 = (NUMERAL 0)) = False => @lem3107569)). Qed.
Lemma lem3107572 : (term131 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3107571) (@lem3107569)). Qed.
Lemma lem3107573 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3107574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3107575 : term509 = (and True).
Proof. exact (MK_COMB (@lem3107574) (@lem3107573)). Qed.
Lemma lem3107576 : term508 = (True /\ False).
Proof. exact (MK_COMB (@lem3107575) (@lem3107572)). Qed.
Lemma lem3107578 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3107579 : term508 = False.
Proof. exact (TRANS (@lem3107576) (@lem3107578)). Qed.
Lemma lem3107580 : term499 = False.
Proof. exact (TRANS (@lem3107568) (@lem3107579)). Qed.
Lemma lem3107581 : term504 = False.
Proof. exact (TRANS (@lem3107565) (@lem3107580)). Qed.
Lemma lem3107582 : term501 = False.
Proof. exact (TRANS (@lem3107549) (@lem3107581)). Qed.
Lemma lem3107583 : term499 = False.
Proof. exact (TRANS (@lem3107526) (@lem3107582)). Qed.
Lemma lem3107584 : term498 = False.
Proof. exact (TRANS (@lem3107517) (@lem3107583)). Qed.
Lemma lem3107585 (_32231 : int) (_32232 : int) (h1 : term566 _32231 _32232) : False.
Proof. exact (EQ_MP (@lem3107584) (@lem3107514 _32231 _32232 h1)). Qed.
Lemma lem3107586 (_32231 : int) (_32232 : int) (h1 : term416 _32231 _32232) : False.
Proof. exact (or_elim (@lem3106823 _32231 _32232 h1) (fun h0 : term549 _32231 _32232 => @lem3107292 _32231 _32232 h0) (fun h0 : term566 _32231 _32232 => @lem3107585 _32231 _32232 h0)). Qed.
Lemma lem3107587 (_32231 : int) (_32232 : int) (h1 : term412 _32231 _32232) : term412 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3107588 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term567 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3107589 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term413 _32231 _32232.
Proof. exact (proj2 (@lem3107588 _32231 _32232 h1)). Qed.
Lemma lem3107591 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term382 _32231 _32232.
Proof. exact (proj2 (@lem3107589 _32231 _32232 h1)). Qed.
Lemma lem3107593 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term354 _32231 _32232.
Proof. exact (proj2 (@lem3107591 _32231 _32232 h1)). Qed.
Lemma lem3107594 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term307 _32231 _32232.
Proof. exact (proj1 (@lem3107591 _32231 _32232 h1)). Qed.
Lemma lem3107596 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term299 _32232.
Proof. exact (proj1 (@lem3107594 _32231 _32232 h1)). Qed.
Lemma lem3107598 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : (real_of_int _32232) = term217.
Proof. exact (proj1 (@lem3107593 _32231 _32232 h1)). Qed.
Lemma lem3107600 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3107601 : term439 = term440.
Proof. exact (@lem3107600 term217 term224). Qed.
Lemma lem3107603 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107604 : term224 = term287.
Proof. exact (@lem3107603 term131). Qed.
Lemma lem3107606 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107607 : term217 = term260.
Proof. exact (@lem3107606 (NUMERAL 0)). Qed.
Lemma lem3107608 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3107609 : term441 = term442.
Proof. exact (MK_COMB (@lem3107608) (@lem3107607)). Qed.
Lemma lem3107610 : term440 = term443.
Proof. exact (MK_COMB (@lem3107609) (@lem3107604)). Qed.
Lemma lem3107611 : term444.
Proof. exact (@lem1980255 term217 term224 term224 term224). Qed.
Lemma lem3107613 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107614 : term440 = term446.
Proof. exact (@lem3107613 (NUMERAL 0) term131). Qed.
Lemma lem3107615 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107616 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107617 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107616 h1) (fun h1 : term446 = True => @lem3107615)). Qed.
Lemma lem3107618 : term446 = True.
Proof. exact (EQ_MP (@lem3107617) (@lem3107615)). Qed.
Lemma lem3107619 : term440 = True.
Proof. exact (TRANS (@lem3107614) (@lem3107618)). Qed.
Lemma lem3107620 : True = term440.
Proof. exact (SYM (@lem3107619)). Qed.
Lemma lem3107621 : term440.
Proof. exact (EQ_MP (@lem3107620) (@lem0)). Qed.
Lemma lem3107622 : term448.
Proof. exact (@lem3107611 (@lem3107621)). Qed.
Lemma lem3107624 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107625 : term440 = term446.
Proof. exact (@lem3107624 (NUMERAL 0) term131). Qed.
Lemma lem3107626 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107627 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107628 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107627 h1) (fun h1 : term446 = True => @lem3107626)). Qed.
Lemma lem3107629 : term446 = True.
Proof. exact (EQ_MP (@lem3107628) (@lem3107626)). Qed.
Lemma lem3107630 : term440 = True.
Proof. exact (TRANS (@lem3107625) (@lem3107629)). Qed.
Lemma lem3107631 : True = term440.
Proof. exact (SYM (@lem3107630)). Qed.
Lemma lem3107632 : term440.
Proof. exact (EQ_MP (@lem3107631) (@lem0)). Qed.
Lemma lem3107633 : term443 = term449.
Proof. exact (@lem3107622 (@lem3107632)). Qed.
Lemma lem3107635 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3107636 : term272 = term273.
Proof. exact (@lem3107635 term131 term131). Qed.
Lemma lem3107637 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107638 : term275 = term131.
Proof. exact (EQ_MP (@lem3107637) (@lem940073)). Qed.
Lemma lem3107639 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107640 : term273 = term224.
Proof. exact (MK_COMB (@lem3107639) (@lem3107638)). Qed.
Lemma lem3107641 : term272 = term224.
Proof. exact (TRANS (@lem3107636) (@lem3107640)). Qed.
Lemma lem3107643 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107644 : term451 = term217.
Proof. exact (@lem3107643 term131). Qed.
Lemma lem3107645 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3107646 : term452 = term441.
Proof. exact (MK_COMB (@lem3107645) (@lem3107644)). Qed.
Lemma lem3107647 : term449 = term440.
Proof. exact (MK_COMB (@lem3107646) (@lem3107641)). Qed.
Lemma lem3107649 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107650 : term440 = term446.
Proof. exact (@lem3107649 (NUMERAL 0) term131). Qed.
Lemma lem3107651 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107652 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107653 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107652 h1) (fun h1 : term446 = True => @lem3107651)). Qed.
Lemma lem3107654 : term446 = True.
Proof. exact (EQ_MP (@lem3107653) (@lem3107651)). Qed.
Lemma lem3107655 : term440 = True.
Proof. exact (TRANS (@lem3107650) (@lem3107654)). Qed.
Lemma lem3107656 : term449 = True.
Proof. exact (TRANS (@lem3107647) (@lem3107655)). Qed.
Lemma lem3107657 : term443 = True.
Proof. exact (TRANS (@lem3107633) (@lem3107656)). Qed.
Lemma lem3107658 : term440 = True.
Proof. exact (TRANS (@lem3107610) (@lem3107657)). Qed.
Lemma lem3107659 : term439 = True.
Proof. exact (TRANS (@lem3107601) (@lem3107658)). Qed.
Lemma lem3107660 : True = term439.
Proof. exact (SYM (@lem3107659)). Qed.
Lemma lem3107661 : term439.
Proof. exact (EQ_MP (@lem3107660) (@lem0)). Qed.
Lemma lem3107662 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term511 _32232.
Proof. exact (conj (@lem3107661) (@lem3107596 _32231 _32232 h1)). Qed.
Lemma lem3107664 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3107665 (_32232 : int) : term512 _32232.
Proof. exact (@lem3107664 term224 (term296 _32232)). Qed.
Lemma lem3107666 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term513 _32232.
Proof. exact (@lem3107665 _32232 (@lem3107662 _32231 _32232 h1)). Qed.
Lemma lem3107667 (_32232 : int) : (term514 _32232) = (term296 _32232).
Proof. exact (@lem1982733 (term296 _32232)). Qed.
Lemma lem3107668 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3107669 (_32232 : int) : (term515 _32232) = (term298 _32232).
Proof. exact (MK_COMB (@lem3107668) (@lem3107667 _32232)). Qed.
Lemma lem3107670 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3107671 (_32232 : int) : (term513 _32232) = (term299 _32232).
Proof. exact (MK_COMB (@lem3107669 _32232) (@lem3107670)). Qed.
Lemma lem3107672 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term299 _32232.
Proof. exact (EQ_MP (@lem3107671 _32232) (@lem3107666 _32231 _32232 h1)). Qed.
Lemma lem3107674 (y : real) : term516 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3107675 (_32232 : int) : term517 _32232.
Proof. exact (@lem3107674 (real_of_int _32232)). Qed.
Lemma lem3107676 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term518 _32232.
Proof. exact (@lem3107675 _32232 (@lem3107598 _32231 _32232 h1)). Qed.
Lemma lem3107677 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term519 _32232.
Proof. exact (@lem3107676 _32231 _32232 h1 term263). Qed.
Lemma lem3107678 (_32232 : int) : (term519 _32232) = ((term312 _32232) = term217).
Proof. exact (eq_refl (term519 _32232)). Qed.
Lemma lem3107685 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : (term312 _32232) = term217.
Proof. exact (EQ_MP (@lem3107678 _32232) (@lem3107677 _32231 _32232 h1)). Qed.
Lemma lem3107686 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term520 _32232.
Proof. exact (conj (@lem3107685 _32231 _32232 h1) (@lem3107672 _32231 _32232 h1)). Qed.
Lemma lem3107688 (x : real) (y : real) : term521 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3107689 (_32232 : int) : term522 _32232.
Proof. exact (@lem3107688 (term312 _32232) (term296 _32232)). Qed.
Lemma lem3107690 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term523 _32232.
Proof. exact (@lem3107689 _32232 (@lem3107686 _32231 _32232 h1)). Qed.
Lemma lem3107691 (_32232 : int) : (term491 _32232) = (term492 _32232).
Proof. exact (@lem1982763 (term312 _32232) (real_of_int _32232) term263). Qed.
Lemma lem3107692 (_32232 : int) : (term493 _32232) = (term471 _32232).
Proof. exact (@lem1982713 term263 (real_of_int _32232)). Qed.
Lemma lem3107694 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107695 : term224 = term287.
Proof. exact (@lem3107694 term131). Qed.
Lemma lem3107697 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3107698 : term263 = term264.
Proof. exact (@lem3107697 term131). Qed.
Lemma lem3107699 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3107700 : term472 = term473.
Proof. exact (MK_COMB (@lem3107699) (@lem3107698)). Qed.
Lemma lem3107701 : term474 = term475.
Proof. exact (MK_COMB (@lem3107700) (@lem3107695)). Qed.
Lemma lem3107702 : term476.
Proof. exact (@lem1981473 term263 term224 term224 term224 term217 term224). Qed.
Lemma lem3107704 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107705 : term440 = term446.
Proof. exact (@lem3107704 (NUMERAL 0) term131). Qed.
Lemma lem3107706 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107707 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107708 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107707 h1) (fun h1 : term446 = True => @lem3107706)). Qed.
Lemma lem3107709 : term446 = True.
Proof. exact (EQ_MP (@lem3107708) (@lem3107706)). Qed.
Lemma lem3107710 : term440 = True.
Proof. exact (TRANS (@lem3107705) (@lem3107709)). Qed.
Lemma lem3107711 : True = term440.
Proof. exact (SYM (@lem3107710)). Qed.
Lemma lem3107712 : term440.
Proof. exact (EQ_MP (@lem3107711) (@lem0)). Qed.
Lemma lem3107713 : term477.
Proof. exact (@lem3107702 (@lem3107712)). Qed.
Lemma lem3107715 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107716 : term440 = term446.
Proof. exact (@lem3107715 (NUMERAL 0) term131). Qed.
Lemma lem3107717 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107718 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107719 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107718 h1) (fun h1 : term446 = True => @lem3107717)). Qed.
Lemma lem3107720 : term446 = True.
Proof. exact (EQ_MP (@lem3107719) (@lem3107717)). Qed.
Lemma lem3107721 : term440 = True.
Proof. exact (TRANS (@lem3107716) (@lem3107720)). Qed.
Lemma lem3107722 : True = term440.
Proof. exact (SYM (@lem3107721)). Qed.
Lemma lem3107723 : term440.
Proof. exact (EQ_MP (@lem3107722) (@lem0)). Qed.
Lemma lem3107724 : term478.
Proof. exact (@lem3107713 (@lem3107723)). Qed.
Lemma lem3107726 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107727 : term440 = term446.
Proof. exact (@lem3107726 (NUMERAL 0) term131). Qed.
Lemma lem3107728 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107729 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107730 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107729 h1) (fun h1 : term446 = True => @lem3107728)). Qed.
Lemma lem3107731 : term446 = True.
Proof. exact (EQ_MP (@lem3107730) (@lem3107728)). Qed.
Lemma lem3107732 : term440 = True.
Proof. exact (TRANS (@lem3107727) (@lem3107731)). Qed.
Lemma lem3107733 : True = term440.
Proof. exact (SYM (@lem3107732)). Qed.
Lemma lem3107734 : term440.
Proof. exact (EQ_MP (@lem3107733) (@lem0)). Qed.
Lemma lem3107735 : term479.
Proof. exact (@lem3107724 (@lem3107734)). Qed.
Lemma lem3107737 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3107738 : term272 = term273.
Proof. exact (@lem3107737 term131 term131). Qed.
Lemma lem3107739 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107740 : term275 = term131.
Proof. exact (EQ_MP (@lem3107739) (@lem940073)). Qed.
Lemma lem3107741 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107742 : term273 = term224.
Proof. exact (MK_COMB (@lem3107741) (@lem3107740)). Qed.
Lemma lem3107743 : term272 = term224.
Proof. exact (TRANS (@lem3107738) (@lem3107742)). Qed.
Lemma lem3107745 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3107746 : term288 = term293.
Proof. exact (@lem3107745 term131 term131). Qed.
Lemma lem3107747 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107748 : term275 = term131.
Proof. exact (EQ_MP (@lem3107747) (@lem940073)). Qed.
Lemma lem3107749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107750 : term273 = term224.
Proof. exact (MK_COMB (@lem3107749) (@lem3107748)). Qed.
Lemma lem3107751 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3107752 : term293 = term263.
Proof. exact (MK_COMB (@lem3107751) (@lem3107750)). Qed.
Lemma lem3107753 : term288 = term263.
Proof. exact (TRANS (@lem3107746) (@lem3107752)). Qed.
Lemma lem3107754 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3107755 : term480 = term472.
Proof. exact (MK_COMB (@lem3107754) (@lem3107753)). Qed.
Lemma lem3107756 : term481 = term474.
Proof. exact (MK_COMB (@lem3107755) (@lem3107743)). Qed.
Lemma lem3107758 (m : nat) : (term482 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3107759 : term474 = term217.
Proof. exact (@lem3107758 term131). Qed.
Lemma lem3107760 : term481 = term217.
Proof. exact (TRANS (@lem3107756) (@lem3107759)). Qed.
Lemma lem3107761 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3107762 : term483 = term484.
Proof. exact (MK_COMB (@lem3107761) (@lem3107760)). Qed.
Lemma lem3107763 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem3107764 : term485 = term451.
Proof. exact (MK_COMB (@lem3107762) (@lem3107763)). Qed.
Lemma lem3107766 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107767 : term451 = term217.
Proof. exact (@lem3107766 term131). Qed.
Lemma lem3107768 : term485 = term217.
Proof. exact (TRANS (@lem3107764) (@lem3107767)). Qed.
Lemma lem3107770 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3107771 : term272 = term273.
Proof. exact (@lem3107770 term131 term131). Qed.
Lemma lem3107772 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107773 : term275 = term131.
Proof. exact (EQ_MP (@lem3107772) (@lem940073)). Qed.
Lemma lem3107774 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107775 : term273 = term224.
Proof. exact (MK_COMB (@lem3107774) (@lem3107773)). Qed.
Lemma lem3107776 : term272 = term224.
Proof. exact (TRANS (@lem3107771) (@lem3107775)). Qed.
Lemma lem3107777 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem3107778 : term486 = term451.
Proof. exact (MK_COMB (@lem3107777) (@lem3107776)). Qed.
Lemma lem3107780 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107781 : term451 = term217.
Proof. exact (@lem3107780 term131). Qed.
Lemma lem3107782 : term486 = term217.
Proof. exact (TRANS (@lem3107778) (@lem3107781)). Qed.
Lemma lem3107783 : term217 = term486.
Proof. exact (SYM (@lem3107782)). Qed.
Lemma lem3107784 : term485 = term486.
Proof. exact (TRANS (@lem3107768) (@lem3107783)). Qed.
Lemma lem3107785 : term475 = term260.
Proof. exact (@lem3107735 (@lem3107784)). Qed.
Lemma lem3107786 : term474 = term260.
Proof. exact (TRANS (@lem3107701) (@lem3107785)). Qed.
Lemma lem3107788 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3107789 : term260 = term217.
Proof. exact (@lem3107788 term217). Qed.
Lemma lem3107790 : term474 = term217.
Proof. exact (TRANS (@lem3107786) (@lem3107789)). Qed.
Lemma lem3107791 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3107792 : term487 = term484.
Proof. exact (MK_COMB (@lem3107791) (@lem3107790)). Qed.
Lemma lem3107793 (_32232 : int) : (real_of_int _32232) = (real_of_int _32232).
Proof. exact (eq_refl (real_of_int _32232)). Qed.
Lemma lem3107794 (_32232 : int) : (term471 _32232) = (term488 _32232).
Proof. exact (MK_COMB (@lem3107792) (@lem3107793 _32232)). Qed.
Lemma lem3107795 (_32232 : int) : (term493 _32232) = (term488 _32232).
Proof. exact (TRANS (@lem3107692 _32232) (@lem3107794 _32232)). Qed.
Lemma lem3107796 (_32232 : int) : (term488 _32232) = term217.
Proof. exact (@lem1982719 (real_of_int _32232)). Qed.
Lemma lem3107797 (_32232 : int) : (term493 _32232) = term217.
Proof. exact (TRANS (@lem3107795 _32232) (@lem3107796 _32232)). Qed.
Lemma lem3107798 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3107799 (_32232 : int) : (term494 _32232) = term490.
Proof. exact (MK_COMB (@lem3107798) (@lem3107797 _32232)). Qed.
Lemma lem3107800 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem3107801 (_32232 : int) : (term492 _32232) = term495.
Proof. exact (MK_COMB (@lem3107799 _32232) (@lem3107800)). Qed.
Lemma lem3107802 (_32232 : int) : (term491 _32232) = term495.
Proof. exact (TRANS (@lem3107691 _32232) (@lem3107801 _32232)). Qed.
Lemma lem3107803 : term495 = term263.
Proof. exact (@lem1982721 term263). Qed.
Lemma lem3107804 (_32232 : int) : (term491 _32232) = term263.
Proof. exact (TRANS (@lem3107802 _32232) (@lem3107803)). Qed.
Lemma lem3107805 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3107806 (_32232 : int) : (term524 _32232) = term497.
Proof. exact (MK_COMB (@lem3107805) (@lem3107804 _32232)). Qed.
Lemma lem3107807 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3107808 (_32232 : int) : (term523 _32232) = term498.
Proof. exact (MK_COMB (@lem3107806 _32232) (@lem3107807)). Qed.
Lemma lem3107809 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : term498.
Proof. exact (EQ_MP (@lem3107808 _32232) (@lem3107690 _32231 _32232 h1)). Qed.
Lemma lem3107811 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3107812 : term498 = term499.
Proof. exact (@lem3107811 term217 term263). Qed.
Lemma lem3107814 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3107815 : term263 = term264.
Proof. exact (@lem3107814 term131). Qed.
Lemma lem3107817 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107818 : term217 = term260.
Proof. exact (@lem3107817 (NUMERAL 0)). Qed.
Lemma lem3107819 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3107820 : term219 = term500.
Proof. exact (MK_COMB (@lem3107819) (@lem3107818)). Qed.
Lemma lem3107821 : term499 = term501.
Proof. exact (MK_COMB (@lem3107820) (@lem3107815)). Qed.
Lemma lem3107822 : term502.
Proof. exact (@lem1980026 term217 term224 term263 term224). Qed.
Lemma lem3107824 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107825 : term440 = term446.
Proof. exact (@lem3107824 (NUMERAL 0) term131). Qed.
Lemma lem3107826 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107827 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107828 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107827 h1) (fun h1 : term446 = True => @lem3107826)). Qed.
Lemma lem3107829 : term446 = True.
Proof. exact (EQ_MP (@lem3107828) (@lem3107826)). Qed.
Lemma lem3107830 : term440 = True.
Proof. exact (TRANS (@lem3107825) (@lem3107829)). Qed.
Lemma lem3107831 : True = term440.
Proof. exact (SYM (@lem3107830)). Qed.
Lemma lem3107832 : term440.
Proof. exact (EQ_MP (@lem3107831) (@lem0)). Qed.
Lemma lem3107833 : term503.
Proof. exact (@lem3107822 (@lem3107832)). Qed.
Lemma lem3107835 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107836 : term440 = term446.
Proof. exact (@lem3107835 (NUMERAL 0) term131). Qed.
Lemma lem3107837 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107838 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107839 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107838 h1) (fun h1 : term446 = True => @lem3107837)). Qed.
Lemma lem3107840 : term446 = True.
Proof. exact (EQ_MP (@lem3107839) (@lem3107837)). Qed.
Lemma lem3107841 : term440 = True.
Proof. exact (TRANS (@lem3107836) (@lem3107840)). Qed.
Lemma lem3107842 : True = term440.
Proof. exact (SYM (@lem3107841)). Qed.
Lemma lem3107843 : term440.
Proof. exact (EQ_MP (@lem3107842) (@lem0)). Qed.
Lemma lem3107844 : term501 = term504.
Proof. exact (@lem3107833 (@lem3107843)). Qed.
Lemma lem3107846 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3107847 : term288 = term293.
Proof. exact (@lem3107846 term131 term131). Qed.
Lemma lem3107848 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107849 : term275 = term131.
Proof. exact (EQ_MP (@lem3107848) (@lem940073)). Qed.
Lemma lem3107850 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107851 : term273 = term224.
Proof. exact (MK_COMB (@lem3107850) (@lem3107849)). Qed.
Lemma lem3107852 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3107853 : term293 = term263.
Proof. exact (MK_COMB (@lem3107852) (@lem3107851)). Qed.
Lemma lem3107854 : term288 = term263.
Proof. exact (TRANS (@lem3107847) (@lem3107853)). Qed.
Lemma lem3107856 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107857 : term451 = term217.
Proof. exact (@lem3107856 term131). Qed.
Lemma lem3107858 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3107859 : term505 = term219.
Proof. exact (MK_COMB (@lem3107858) (@lem3107857)). Qed.
Lemma lem3107860 : term504 = term499.
Proof. exact (MK_COMB (@lem3107859) (@lem3107854)). Qed.
Lemma lem3107862 (m : nat) (n : nat) : (term506 m n) = (term507 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3107863 : term499 = term508.
Proof. exact (@lem3107862 (NUMERAL 0) term131). Qed.
Lemma lem3107864 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107865 (h1 : term447 = (BIT1 0)) : (term131 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3107866 : (term447 = (BIT1 0)) = ((term131 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107865 h1) (fun h1 : (term131 = (NUMERAL 0)) = False => @lem3107864)). Qed.
Lemma lem3107867 : (term131 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3107866) (@lem3107864)). Qed.
Lemma lem3107868 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3107869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3107870 : term509 = (and True).
Proof. exact (MK_COMB (@lem3107869) (@lem3107868)). Qed.
Lemma lem3107871 : term508 = (True /\ False).
Proof. exact (MK_COMB (@lem3107870) (@lem3107867)). Qed.
Lemma lem3107873 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3107874 : term508 = False.
Proof. exact (TRANS (@lem3107871) (@lem3107873)). Qed.
Lemma lem3107875 : term499 = False.
Proof. exact (TRANS (@lem3107863) (@lem3107874)). Qed.
Lemma lem3107876 : term504 = False.
Proof. exact (TRANS (@lem3107860) (@lem3107875)). Qed.
Lemma lem3107877 : term501 = False.
Proof. exact (TRANS (@lem3107844) (@lem3107876)). Qed.
Lemma lem3107878 : term499 = False.
Proof. exact (TRANS (@lem3107821) (@lem3107877)). Qed.
Lemma lem3107879 : term498 = False.
Proof. exact (TRANS (@lem3107812) (@lem3107878)). Qed.
Lemma lem3107880 (_32231 : int) (_32232 : int) (h1 : term567 _32231 _32232) : False.
Proof. exact (EQ_MP (@lem3107879) (@lem3107809 _32231 _32232 h1)). Qed.
Lemma lem3107881 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term568 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3107882 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term414 _32231 _32232.
Proof. exact (proj2 (@lem3107881 _32231 _32232 h1)). Qed.
Lemma lem3107884 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term383 _32231 _32232.
Proof. exact (proj2 (@lem3107882 _32231 _32232 h1)). Qed.
Lemma lem3107886 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term354 _32231 _32232.
Proof. exact (proj2 (@lem3107884 _32231 _32232 h1)). Qed.
Lemma lem3107887 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : (real_of_int _32231) = term217.
Proof. exact (proj1 (@lem3107884 _32231 _32232 h1)). Qed.
Lemma lem3107888 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term331 _32231 _32232.
Proof. exact (proj2 (@lem3107886 _32231 _32232 h1)). Qed.
Lemma lem3107889 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : (real_of_int _32232) = term217.
Proof. exact (proj1 (@lem3107886 _32231 _32232 h1)). Qed.
Lemma lem3107891 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3107892 : term439 = term440.
Proof. exact (@lem3107891 term217 term224). Qed.
Lemma lem3107894 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107895 : term224 = term287.
Proof. exact (@lem3107894 term131). Qed.
Lemma lem3107897 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107898 : term217 = term260.
Proof. exact (@lem3107897 (NUMERAL 0)). Qed.
Lemma lem3107899 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3107900 : term441 = term442.
Proof. exact (MK_COMB (@lem3107899) (@lem3107898)). Qed.
Lemma lem3107901 : term440 = term443.
Proof. exact (MK_COMB (@lem3107900) (@lem3107895)). Qed.
Lemma lem3107902 : term444.
Proof. exact (@lem1980255 term217 term224 term224 term224). Qed.
Lemma lem3107904 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107905 : term440 = term446.
Proof. exact (@lem3107904 (NUMERAL 0) term131). Qed.
Lemma lem3107906 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107907 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107908 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107907 h1) (fun h1 : term446 = True => @lem3107906)). Qed.
Lemma lem3107909 : term446 = True.
Proof. exact (EQ_MP (@lem3107908) (@lem3107906)). Qed.
Lemma lem3107910 : term440 = True.
Proof. exact (TRANS (@lem3107905) (@lem3107909)). Qed.
Lemma lem3107911 : True = term440.
Proof. exact (SYM (@lem3107910)). Qed.
Lemma lem3107912 : term440.
Proof. exact (EQ_MP (@lem3107911) (@lem0)). Qed.
Lemma lem3107913 : term448.
Proof. exact (@lem3107902 (@lem3107912)). Qed.
Lemma lem3107915 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107916 : term440 = term446.
Proof. exact (@lem3107915 (NUMERAL 0) term131). Qed.
Lemma lem3107917 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107918 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107919 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107918 h1) (fun h1 : term446 = True => @lem3107917)). Qed.
Lemma lem3107920 : term446 = True.
Proof. exact (EQ_MP (@lem3107919) (@lem3107917)). Qed.
Lemma lem3107921 : term440 = True.
Proof. exact (TRANS (@lem3107916) (@lem3107920)). Qed.
Lemma lem3107922 : True = term440.
Proof. exact (SYM (@lem3107921)). Qed.
Lemma lem3107923 : term440.
Proof. exact (EQ_MP (@lem3107922) (@lem0)). Qed.
Lemma lem3107924 : term443 = term449.
Proof. exact (@lem3107913 (@lem3107923)). Qed.
Lemma lem3107926 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3107927 : term272 = term273.
Proof. exact (@lem3107926 term131 term131). Qed.
Lemma lem3107928 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3107929 : term275 = term131.
Proof. exact (EQ_MP (@lem3107928) (@lem940073)). Qed.
Lemma lem3107930 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3107931 : term273 = term224.
Proof. exact (MK_COMB (@lem3107930) (@lem3107929)). Qed.
Lemma lem3107932 : term272 = term224.
Proof. exact (TRANS (@lem3107927) (@lem3107931)). Qed.
Lemma lem3107934 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3107935 : term451 = term217.
Proof. exact (@lem3107934 term131). Qed.
Lemma lem3107936 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3107937 : term452 = term441.
Proof. exact (MK_COMB (@lem3107936) (@lem3107935)). Qed.
Lemma lem3107938 : term449 = term440.
Proof. exact (MK_COMB (@lem3107937) (@lem3107932)). Qed.
Lemma lem3107940 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107941 : term440 = term446.
Proof. exact (@lem3107940 (NUMERAL 0) term131). Qed.
Lemma lem3107942 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107943 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3107944 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107943 h1) (fun h1 : term446 = True => @lem3107942)). Qed.
Lemma lem3107945 : term446 = True.
Proof. exact (EQ_MP (@lem3107944) (@lem3107942)). Qed.
Lemma lem3107946 : term440 = True.
Proof. exact (TRANS (@lem3107941) (@lem3107945)). Qed.
Lemma lem3107947 : term449 = True.
Proof. exact (TRANS (@lem3107938) (@lem3107946)). Qed.
Lemma lem3107948 : term443 = True.
Proof. exact (TRANS (@lem3107924) (@lem3107947)). Qed.
Lemma lem3107949 : term440 = True.
Proof. exact (TRANS (@lem3107901) (@lem3107948)). Qed.
Lemma lem3107950 : term439 = True.
Proof. exact (TRANS (@lem3107892) (@lem3107949)). Qed.
Lemma lem3107951 : True = term439.
Proof. exact (SYM (@lem3107950)). Qed.
Lemma lem3107952 : term439.
Proof. exact (EQ_MP (@lem3107951) (@lem0)). Qed.
Lemma lem3107953 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term550 _32231 _32232.
Proof. exact (conj (@lem3107952) (@lem3107888 _32231 _32232 h1)). Qed.
Lemma lem3107955 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3107956 (_32231 : int) (_32232 : int) : term551 _32231 _32232.
Proof. exact (@lem3107955 term224 (term325 _32231 _32232)). Qed.
Lemma lem3107957 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term552 _32231 _32232.
Proof. exact (@lem3107956 _32231 _32232 (@lem3107953 _32231 _32232 h1)). Qed.
Lemma lem3107958 (_32231 : int) (_32232 : int) : (term553 _32231 _32232) = (term325 _32231 _32232).
Proof. exact (@lem1982733 (term325 _32231 _32232)). Qed.
Lemma lem3107959 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3107960 (_32231 : int) (_32232 : int) : (term554 _32231 _32232) = (term330 _32231 _32232).
Proof. exact (MK_COMB (@lem3107959) (@lem3107958 _32231 _32232)). Qed.
Lemma lem3107961 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3107962 (_32231 : int) (_32232 : int) : (term552 _32231 _32232) = (term331 _32231 _32232).
Proof. exact (MK_COMB (@lem3107960 _32231 _32232) (@lem3107961)). Qed.
Lemma lem3107963 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term331 _32231 _32232.
Proof. exact (EQ_MP (@lem3107962 _32231 _32232) (@lem3107957 _32231 _32232 h1)). Qed.
Lemma lem3107965 (y : real) : term516 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3107966 (_32232 : int) : term517 _32232.
Proof. exact (@lem3107965 (real_of_int _32232)). Qed.
Lemma lem3107967 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term518 _32232.
Proof. exact (@lem3107966 _32232 (@lem3107889 _32231 _32232 h1)). Qed.
Lemma lem3107968 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term540 _32232.
Proof. exact (@lem3107967 _32231 _32232 h1 term224). Qed.
Lemma lem3107969 (_32232 : int) : (term540 _32232) = ((term541 _32232) = term217).
Proof. exact (eq_refl (term540 _32232)). Qed.
Lemma lem3107970 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : (term541 _32232) = term217.
Proof. exact (EQ_MP (@lem3107969 _32232) (@lem3107968 _32231 _32232 h1)). Qed.
Lemma lem3107971 (_32232 : int) : (term541 _32232) = (real_of_int _32232).
Proof. exact (@lem1982733 (real_of_int _32232)). Qed.
Lemma lem3107972 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3107973 (_32232 : int) : (term542 _32232) = (term230 _32232).
Proof. exact (MK_COMB (@lem3107972) (@lem3107971 _32232)). Qed.
Lemma lem3107974 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3107975 (_32232 : int) : ((term541 _32232) = term217) = ((real_of_int _32232) = term217).
Proof. exact (MK_COMB (@lem3107973 _32232) (@lem3107974)). Qed.
Lemma lem3107976 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : (real_of_int _32232) = term217.
Proof. exact (EQ_MP (@lem3107975 _32232) (@lem3107970 _32231 _32232 h1)). Qed.
Lemma lem3107977 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term354 _32231 _32232.
Proof. exact (conj (@lem3107976 _32231 _32232 h1) (@lem3107963 _32231 _32232 h1)). Qed.
Lemma lem3107979 (x : real) (y : real) : term521 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3107980 (_32231 : int) (_32232 : int) : term569 _32231 _32232.
Proof. exact (@lem3107979 (real_of_int _32232) (term325 _32231 _32232)). Qed.
Lemma lem3107981 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term570 _32231 _32232.
Proof. exact (@lem3107980 _32231 _32232 (@lem3107977 _32231 _32232 h1)). Qed.
Lemma lem3107982 (_32231 : int) (_32232 : int) : (term571 _32231 _32232) = (term572 _32231 _32232).
Proof. exact (@lem1982757 (real_of_int _32231) (real_of_int _32232) (term324 _32232)). Qed.
Lemma lem3107983 (_32232 : int) : (term546 _32232) = (term547 _32232).
Proof. exact (@lem1982763 (real_of_int _32232) (term312 _32232) term263). Qed.
Lemma lem3107984 (_32232 : int) : (term470 _32232) = (term471 _32232).
Proof. exact (@lem1982715 term263 (real_of_int _32232)). Qed.
Lemma lem3107986 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3107987 : term224 = term287.
Proof. exact (@lem3107986 term131). Qed.
Lemma lem3107989 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3107990 : term263 = term264.
Proof. exact (@lem3107989 term131). Qed.
Lemma lem3107991 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3107992 : term472 = term473.
Proof. exact (MK_COMB (@lem3107991) (@lem3107990)). Qed.
Lemma lem3107993 : term474 = term475.
Proof. exact (MK_COMB (@lem3107992) (@lem3107987)). Qed.
Lemma lem3107994 : term476.
Proof. exact (@lem1981473 term263 term224 term224 term224 term217 term224). Qed.
Lemma lem3107996 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3107997 : term440 = term446.
Proof. exact (@lem3107996 (NUMERAL 0) term131). Qed.
Lemma lem3107998 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3107999 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3108000 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3107999 h1) (fun h1 : term446 = True => @lem3107998)). Qed.
Lemma lem3108001 : term446 = True.
Proof. exact (EQ_MP (@lem3108000) (@lem3107998)). Qed.
Lemma lem3108002 : term440 = True.
Proof. exact (TRANS (@lem3107997) (@lem3108001)). Qed.
Lemma lem3108003 : True = term440.
Proof. exact (SYM (@lem3108002)). Qed.
Lemma lem3108004 : term440.
Proof. exact (EQ_MP (@lem3108003) (@lem0)). Qed.
Lemma lem3108005 : term477.
Proof. exact (@lem3107994 (@lem3108004)). Qed.
Lemma lem3108007 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3108008 : term440 = term446.
Proof. exact (@lem3108007 (NUMERAL 0) term131). Qed.
Lemma lem3108009 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3108010 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3108011 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3108010 h1) (fun h1 : term446 = True => @lem3108009)). Qed.
Lemma lem3108012 : term446 = True.
Proof. exact (EQ_MP (@lem3108011) (@lem3108009)). Qed.
Lemma lem3108013 : term440 = True.
Proof. exact (TRANS (@lem3108008) (@lem3108012)). Qed.
Lemma lem3108014 : True = term440.
Proof. exact (SYM (@lem3108013)). Qed.
Lemma lem3108015 : term440.
Proof. exact (EQ_MP (@lem3108014) (@lem0)). Qed.
Lemma lem3108016 : term478.
Proof. exact (@lem3108005 (@lem3108015)). Qed.
Lemma lem3108018 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3108019 : term440 = term446.
Proof. exact (@lem3108018 (NUMERAL 0) term131). Qed.
Lemma lem3108020 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3108021 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3108022 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3108021 h1) (fun h1 : term446 = True => @lem3108020)). Qed.
Lemma lem3108023 : term446 = True.
Proof. exact (EQ_MP (@lem3108022) (@lem3108020)). Qed.
Lemma lem3108024 : term440 = True.
Proof. exact (TRANS (@lem3108019) (@lem3108023)). Qed.
Lemma lem3108025 : True = term440.
Proof. exact (SYM (@lem3108024)). Qed.
Lemma lem3108026 : term440.
Proof. exact (EQ_MP (@lem3108025) (@lem0)). Qed.
Lemma lem3108027 : term479.
Proof. exact (@lem3108016 (@lem3108026)). Qed.
Lemma lem3108029 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3108030 : term272 = term273.
Proof. exact (@lem3108029 term131 term131). Qed.
Lemma lem3108031 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3108032 : term275 = term131.
Proof. exact (EQ_MP (@lem3108031) (@lem940073)). Qed.
Lemma lem3108033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3108034 : term273 = term224.
Proof. exact (MK_COMB (@lem3108033) (@lem3108032)). Qed.
Lemma lem3108035 : term272 = term224.
Proof. exact (TRANS (@lem3108030) (@lem3108034)). Qed.
Lemma lem3108037 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3108038 : term288 = term293.
Proof. exact (@lem3108037 term131 term131). Qed.
Lemma lem3108039 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3108040 : term275 = term131.
Proof. exact (EQ_MP (@lem3108039) (@lem940073)). Qed.
Lemma lem3108041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3108042 : term273 = term224.
Proof. exact (MK_COMB (@lem3108041) (@lem3108040)). Qed.
Lemma lem3108043 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3108044 : term293 = term263.
Proof. exact (MK_COMB (@lem3108043) (@lem3108042)). Qed.
Lemma lem3108045 : term288 = term263.
Proof. exact (TRANS (@lem3108038) (@lem3108044)). Qed.
Lemma lem3108046 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3108047 : term480 = term472.
Proof. exact (MK_COMB (@lem3108046) (@lem3108045)). Qed.
Lemma lem3108048 : term481 = term474.
Proof. exact (MK_COMB (@lem3108047) (@lem3108035)). Qed.
Lemma lem3108050 (m : nat) : (term482 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3108051 : term474 = term217.
Proof. exact (@lem3108050 term131). Qed.
Lemma lem3108052 : term481 = term217.
Proof. exact (TRANS (@lem3108048) (@lem3108051)). Qed.
Lemma lem3108053 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3108054 : term483 = term484.
Proof. exact (MK_COMB (@lem3108053) (@lem3108052)). Qed.
Lemma lem3108055 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem3108056 : term485 = term451.
Proof. exact (MK_COMB (@lem3108054) (@lem3108055)). Qed.
Lemma lem3108058 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3108059 : term451 = term217.
Proof. exact (@lem3108058 term131). Qed.
Lemma lem3108060 : term485 = term217.
Proof. exact (TRANS (@lem3108056) (@lem3108059)). Qed.
Lemma lem3108062 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3108063 : term272 = term273.
Proof. exact (@lem3108062 term131 term131). Qed.
Lemma lem3108064 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3108065 : term275 = term131.
Proof. exact (EQ_MP (@lem3108064) (@lem940073)). Qed.
Lemma lem3108066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3108067 : term273 = term224.
Proof. exact (MK_COMB (@lem3108066) (@lem3108065)). Qed.
Lemma lem3108068 : term272 = term224.
Proof. exact (TRANS (@lem3108063) (@lem3108067)). Qed.
Lemma lem3108069 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem3108070 : term486 = term451.
Proof. exact (MK_COMB (@lem3108069) (@lem3108068)). Qed.
Lemma lem3108072 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3108073 : term451 = term217.
Proof. exact (@lem3108072 term131). Qed.
Lemma lem3108074 : term486 = term217.
Proof. exact (TRANS (@lem3108070) (@lem3108073)). Qed.
Lemma lem3108075 : term217 = term486.
Proof. exact (SYM (@lem3108074)). Qed.
Lemma lem3108076 : term485 = term486.
Proof. exact (TRANS (@lem3108060) (@lem3108075)). Qed.
Lemma lem3108077 : term475 = term260.
Proof. exact (@lem3108027 (@lem3108076)). Qed.
Lemma lem3108078 : term474 = term260.
Proof. exact (TRANS (@lem3107993) (@lem3108077)). Qed.
Lemma lem3108080 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3108081 : term260 = term217.
Proof. exact (@lem3108080 term217). Qed.
Lemma lem3108082 : term474 = term217.
Proof. exact (TRANS (@lem3108078) (@lem3108081)). Qed.
Lemma lem3108083 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3108084 : term487 = term484.
Proof. exact (MK_COMB (@lem3108083) (@lem3108082)). Qed.
Lemma lem3108085 (_32232 : int) : (real_of_int _32232) = (real_of_int _32232).
Proof. exact (eq_refl (real_of_int _32232)). Qed.
Lemma lem3108086 (_32232 : int) : (term471 _32232) = (term488 _32232).
Proof. exact (MK_COMB (@lem3108084) (@lem3108085 _32232)). Qed.
Lemma lem3108087 (_32232 : int) : (term470 _32232) = (term488 _32232).
Proof. exact (TRANS (@lem3107984 _32232) (@lem3108086 _32232)). Qed.
Lemma lem3108088 (_32232 : int) : (term488 _32232) = term217.
Proof. exact (@lem1982719 (real_of_int _32232)). Qed.
Lemma lem3108089 (_32232 : int) : (term470 _32232) = term217.
Proof. exact (TRANS (@lem3108087 _32232) (@lem3108088 _32232)). Qed.
Lemma lem3108090 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3108091 (_32232 : int) : (term489 _32232) = term490.
Proof. exact (MK_COMB (@lem3108090) (@lem3108089 _32232)). Qed.
Lemma lem3108092 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem3108093 (_32232 : int) : (term547 _32232) = term495.
Proof. exact (MK_COMB (@lem3108091 _32232) (@lem3108092)). Qed.
Lemma lem3108094 (_32232 : int) : (term546 _32232) = term495.
Proof. exact (TRANS (@lem3107983 _32232) (@lem3108093 _32232)). Qed.
Lemma lem3108095 : term495 = term263.
Proof. exact (@lem1982721 term263). Qed.
Lemma lem3108096 (_32232 : int) : (term546 _32232) = term263.
Proof. exact (TRANS (@lem3108094 _32232) (@lem3108095)). Qed.
Lemma lem3108097 (_32231 : int) : (term241 _32231) = (term241 _32231).
Proof. exact (eq_refl (term241 _32231)). Qed.
Lemma lem3108098 (_32232 : int) (_32231 : int) : (term572 _32231 _32232) = (term296 _32231).
Proof. exact (MK_COMB (@lem3108097 _32231) (@lem3108096 _32232)). Qed.
Lemma lem3108099 (_32232 : int) (_32231 : int) : (term571 _32231 _32232) = (term296 _32231).
Proof. exact (TRANS (@lem3107982 _32231 _32232) (@lem3108098 _32232 _32231)). Qed.
Lemma lem3108100 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3108101 (_32232 : int) (_32231 : int) : (term573 _32231 _32232) = (term298 _32231).
Proof. exact (MK_COMB (@lem3108100) (@lem3108099 _32232 _32231)). Qed.
Lemma lem3108102 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3108103 (_32232 : int) (_32231 : int) : (term570 _32231 _32232) = (term299 _32231).
Proof. exact (MK_COMB (@lem3108101 _32232 _32231) (@lem3108102)). Qed.
Lemma lem3108104 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term299 _32231.
Proof. exact (EQ_MP (@lem3108103 _32232 _32231) (@lem3107981 _32231 _32232 h1)). Qed.
Lemma lem3108106 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3108107 : term439 = term440.
Proof. exact (@lem3108106 term217 term224). Qed.
Lemma lem3108109 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3108110 : term224 = term287.
Proof. exact (@lem3108109 term131). Qed.
Lemma lem3108112 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3108113 : term217 = term260.
Proof. exact (@lem3108112 (NUMERAL 0)). Qed.
Lemma lem3108114 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3108115 : term441 = term442.
Proof. exact (MK_COMB (@lem3108114) (@lem3108113)). Qed.
Lemma lem3108116 : term440 = term443.
Proof. exact (MK_COMB (@lem3108115) (@lem3108110)). Qed.
Lemma lem3108117 : term444.
Proof. exact (@lem1980255 term217 term224 term224 term224). Qed.
Lemma lem3108119 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3108120 : term440 = term446.
Proof. exact (@lem3108119 (NUMERAL 0) term131). Qed.
Lemma lem3108121 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3108122 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3108123 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3108122 h1) (fun h1 : term446 = True => @lem3108121)). Qed.
Lemma lem3108124 : term446 = True.
Proof. exact (EQ_MP (@lem3108123) (@lem3108121)). Qed.
Lemma lem3108125 : term440 = True.
Proof. exact (TRANS (@lem3108120) (@lem3108124)). Qed.
Lemma lem3108126 : True = term440.
Proof. exact (SYM (@lem3108125)). Qed.
Lemma lem3108127 : term440.
Proof. exact (EQ_MP (@lem3108126) (@lem0)). Qed.
Lemma lem3108128 : term448.
Proof. exact (@lem3108117 (@lem3108127)). Qed.
Lemma lem3108130 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3108131 : term440 = term446.
Proof. exact (@lem3108130 (NUMERAL 0) term131). Qed.
Lemma lem3108132 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3108133 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3108134 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3108133 h1) (fun h1 : term446 = True => @lem3108132)). Qed.
Lemma lem3108135 : term446 = True.
Proof. exact (EQ_MP (@lem3108134) (@lem3108132)). Qed.
Lemma lem3108136 : term440 = True.
Proof. exact (TRANS (@lem3108131) (@lem3108135)). Qed.
Lemma lem3108137 : True = term440.
Proof. exact (SYM (@lem3108136)). Qed.
Lemma lem3108138 : term440.
Proof. exact (EQ_MP (@lem3108137) (@lem0)). Qed.
Lemma lem3108139 : term443 = term449.
Proof. exact (@lem3108128 (@lem3108138)). Qed.
Lemma lem3108141 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3108142 : term272 = term273.
Proof. exact (@lem3108141 term131 term131). Qed.
Lemma lem3108143 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3108144 : term275 = term131.
Proof. exact (EQ_MP (@lem3108143) (@lem940073)). Qed.
Lemma lem3108145 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3108146 : term273 = term224.
Proof. exact (MK_COMB (@lem3108145) (@lem3108144)). Qed.
Lemma lem3108147 : term272 = term224.
Proof. exact (TRANS (@lem3108142) (@lem3108146)). Qed.
Lemma lem3108149 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3108150 : term451 = term217.
Proof. exact (@lem3108149 term131). Qed.
Lemma lem3108151 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3108152 : term452 = term441.
Proof. exact (MK_COMB (@lem3108151) (@lem3108150)). Qed.
Lemma lem3108153 : term449 = term440.
Proof. exact (MK_COMB (@lem3108152) (@lem3108147)). Qed.
Lemma lem3108155 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3108156 : term440 = term446.
Proof. exact (@lem3108155 (NUMERAL 0) term131). Qed.
Lemma lem3108157 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3108158 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3108159 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3108158 h1) (fun h1 : term446 = True => @lem3108157)). Qed.
Lemma lem3108160 : term446 = True.
Proof. exact (EQ_MP (@lem3108159) (@lem3108157)). Qed.
Lemma lem3108161 : term440 = True.
Proof. exact (TRANS (@lem3108156) (@lem3108160)). Qed.
Lemma lem3108162 : term449 = True.
Proof. exact (TRANS (@lem3108153) (@lem3108161)). Qed.
Lemma lem3108163 : term443 = True.
Proof. exact (TRANS (@lem3108139) (@lem3108162)). Qed.
Lemma lem3108164 : term440 = True.
Proof. exact (TRANS (@lem3108116) (@lem3108163)). Qed.
Lemma lem3108165 : term439 = True.
Proof. exact (TRANS (@lem3108107) (@lem3108164)). Qed.
Lemma lem3108166 : True = term439.
Proof. exact (SYM (@lem3108165)). Qed.
Lemma lem3108167 : term439.
Proof. exact (EQ_MP (@lem3108166) (@lem0)). Qed.
Lemma lem3108168 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term511 _32231.
Proof. exact (conj (@lem3108167) (@lem3108104 _32231 _32232 h1)). Qed.
Lemma lem3108170 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3108171 (_32231 : int) : term512 _32231.
Proof. exact (@lem3108170 term224 (term296 _32231)). Qed.
Lemma lem3108172 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term513 _32231.
Proof. exact (@lem3108171 _32231 (@lem3108168 _32231 _32232 h1)). Qed.
Lemma lem3108173 (_32231 : int) : (term514 _32231) = (term296 _32231).
Proof. exact (@lem1982733 (term296 _32231)). Qed.
Lemma lem3108174 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3108175 (_32231 : int) : (term515 _32231) = (term298 _32231).
Proof. exact (MK_COMB (@lem3108174) (@lem3108173 _32231)). Qed.
Lemma lem3108176 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3108177 (_32231 : int) : (term513 _32231) = (term299 _32231).
Proof. exact (MK_COMB (@lem3108175 _32231) (@lem3108176)). Qed.
Lemma lem3108178 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term299 _32231.
Proof. exact (EQ_MP (@lem3108177 _32231) (@lem3108172 _32231 _32232 h1)). Qed.
Lemma lem3108180 (y : real) : term516 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3108181 (_32231 : int) : term517 _32231.
Proof. exact (@lem3108180 (real_of_int _32231)). Qed.
Lemma lem3108182 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term518 _32231.
Proof. exact (@lem3108181 _32231 (@lem3107887 _32231 _32232 h1)). Qed.
Lemma lem3108183 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term519 _32231.
Proof. exact (@lem3108182 _32231 _32232 h1 term263). Qed.
Lemma lem3108184 (_32231 : int) : (term519 _32231) = ((term312 _32231) = term217).
Proof. exact (eq_refl (term519 _32231)). Qed.
Lemma lem3108191 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : (term312 _32231) = term217.
Proof. exact (EQ_MP (@lem3108184 _32231) (@lem3108183 _32231 _32232 h1)). Qed.
Lemma lem3108192 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term520 _32231.
Proof. exact (conj (@lem3108191 _32231 _32232 h1) (@lem3108178 _32231 _32232 h1)). Qed.
Lemma lem3108194 (x : real) (y : real) : term521 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3108195 (_32231 : int) : term522 _32231.
Proof. exact (@lem3108194 (term312 _32231) (term296 _32231)). Qed.
Lemma lem3108196 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term523 _32231.
Proof. exact (@lem3108195 _32231 (@lem3108192 _32231 _32232 h1)). Qed.
Lemma lem3108197 (_32231 : int) : (term491 _32231) = (term492 _32231).
Proof. exact (@lem1982763 (term312 _32231) (real_of_int _32231) term263). Qed.
Lemma lem3108198 (_32231 : int) : (term493 _32231) = (term471 _32231).
Proof. exact (@lem1982713 term263 (real_of_int _32231)). Qed.
Lemma lem3108200 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3108201 : term224 = term287.
Proof. exact (@lem3108200 term131). Qed.
Lemma lem3108203 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3108204 : term263 = term264.
Proof. exact (@lem3108203 term131). Qed.
Lemma lem3108205 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3108206 : term472 = term473.
Proof. exact (MK_COMB (@lem3108205) (@lem3108204)). Qed.
Lemma lem3108207 : term474 = term475.
Proof. exact (MK_COMB (@lem3108206) (@lem3108201)). Qed.
Lemma lem3108208 : term476.
Proof. exact (@lem1981473 term263 term224 term224 term224 term217 term224). Qed.
Lemma lem3108210 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3108211 : term440 = term446.
Proof. exact (@lem3108210 (NUMERAL 0) term131). Qed.
Lemma lem3108212 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3108213 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3108214 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3108213 h1) (fun h1 : term446 = True => @lem3108212)). Qed.
Lemma lem3108215 : term446 = True.
Proof. exact (EQ_MP (@lem3108214) (@lem3108212)). Qed.
Lemma lem3108216 : term440 = True.
Proof. exact (TRANS (@lem3108211) (@lem3108215)). Qed.
Lemma lem3108217 : True = term440.
Proof. exact (SYM (@lem3108216)). Qed.
Lemma lem3108218 : term440.
Proof. exact (EQ_MP (@lem3108217) (@lem0)). Qed.
Lemma lem3108219 : term477.
Proof. exact (@lem3108208 (@lem3108218)). Qed.
Lemma lem3108221 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3108222 : term440 = term446.
Proof. exact (@lem3108221 (NUMERAL 0) term131). Qed.
Lemma lem3108223 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3108224 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3108225 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3108224 h1) (fun h1 : term446 = True => @lem3108223)). Qed.
Lemma lem3108226 : term446 = True.
Proof. exact (EQ_MP (@lem3108225) (@lem3108223)). Qed.
Lemma lem3108227 : term440 = True.
Proof. exact (TRANS (@lem3108222) (@lem3108226)). Qed.
Lemma lem3108228 : True = term440.
Proof. exact (SYM (@lem3108227)). Qed.
Lemma lem3108229 : term440.
Proof. exact (EQ_MP (@lem3108228) (@lem0)). Qed.
Lemma lem3108230 : term478.
Proof. exact (@lem3108219 (@lem3108229)). Qed.
Lemma lem3108232 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3108233 : term440 = term446.
Proof. exact (@lem3108232 (NUMERAL 0) term131). Qed.
Lemma lem3108234 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3108235 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3108236 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3108235 h1) (fun h1 : term446 = True => @lem3108234)). Qed.
Lemma lem3108237 : term446 = True.
Proof. exact (EQ_MP (@lem3108236) (@lem3108234)). Qed.
Lemma lem3108238 : term440 = True.
Proof. exact (TRANS (@lem3108233) (@lem3108237)). Qed.
Lemma lem3108239 : True = term440.
Proof. exact (SYM (@lem3108238)). Qed.
Lemma lem3108240 : term440.
Proof. exact (EQ_MP (@lem3108239) (@lem0)). Qed.
Lemma lem3108241 : term479.
Proof. exact (@lem3108230 (@lem3108240)). Qed.
Lemma lem3108243 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3108244 : term272 = term273.
Proof. exact (@lem3108243 term131 term131). Qed.
Lemma lem3108245 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3108246 : term275 = term131.
Proof. exact (EQ_MP (@lem3108245) (@lem940073)). Qed.
Lemma lem3108247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3108248 : term273 = term224.
Proof. exact (MK_COMB (@lem3108247) (@lem3108246)). Qed.
Lemma lem3108249 : term272 = term224.
Proof. exact (TRANS (@lem3108244) (@lem3108248)). Qed.
Lemma lem3108251 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3108252 : term288 = term293.
Proof. exact (@lem3108251 term131 term131). Qed.
Lemma lem3108253 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3108254 : term275 = term131.
Proof. exact (EQ_MP (@lem3108253) (@lem940073)). Qed.
Lemma lem3108255 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3108256 : term273 = term224.
Proof. exact (MK_COMB (@lem3108255) (@lem3108254)). Qed.
Lemma lem3108257 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3108258 : term293 = term263.
Proof. exact (MK_COMB (@lem3108257) (@lem3108256)). Qed.
Lemma lem3108259 : term288 = term263.
Proof. exact (TRANS (@lem3108252) (@lem3108258)). Qed.
Lemma lem3108260 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3108261 : term480 = term472.
Proof. exact (MK_COMB (@lem3108260) (@lem3108259)). Qed.
Lemma lem3108262 : term481 = term474.
Proof. exact (MK_COMB (@lem3108261) (@lem3108249)). Qed.
Lemma lem3108264 (m : nat) : (term482 m) = term217.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3108265 : term474 = term217.
Proof. exact (@lem3108264 term131). Qed.
Lemma lem3108266 : term481 = term217.
Proof. exact (TRANS (@lem3108262) (@lem3108265)). Qed.
Lemma lem3108267 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3108268 : term483 = term484.
Proof. exact (MK_COMB (@lem3108267) (@lem3108266)). Qed.
Lemma lem3108269 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem3108270 : term485 = term451.
Proof. exact (MK_COMB (@lem3108268) (@lem3108269)). Qed.
Lemma lem3108272 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3108273 : term451 = term217.
Proof. exact (@lem3108272 term131). Qed.
Lemma lem3108274 : term485 = term217.
Proof. exact (TRANS (@lem3108270) (@lem3108273)). Qed.
Lemma lem3108276 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3108277 : term272 = term273.
Proof. exact (@lem3108276 term131 term131). Qed.
Lemma lem3108278 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3108279 : term275 = term131.
Proof. exact (EQ_MP (@lem3108278) (@lem940073)). Qed.
Lemma lem3108280 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3108281 : term273 = term224.
Proof. exact (MK_COMB (@lem3108280) (@lem3108279)). Qed.
Lemma lem3108282 : term272 = term224.
Proof. exact (TRANS (@lem3108277) (@lem3108281)). Qed.
Lemma lem3108283 : term484 = term484.
Proof. exact (eq_refl term484). Qed.
Lemma lem3108284 : term486 = term451.
Proof. exact (MK_COMB (@lem3108283) (@lem3108282)). Qed.
Lemma lem3108286 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3108287 : term451 = term217.
Proof. exact (@lem3108286 term131). Qed.
Lemma lem3108288 : term486 = term217.
Proof. exact (TRANS (@lem3108284) (@lem3108287)). Qed.
Lemma lem3108289 : term217 = term486.
Proof. exact (SYM (@lem3108288)). Qed.
Lemma lem3108290 : term485 = term486.
Proof. exact (TRANS (@lem3108274) (@lem3108289)). Qed.
Lemma lem3108291 : term475 = term260.
Proof. exact (@lem3108241 (@lem3108290)). Qed.
Lemma lem3108292 : term474 = term260.
Proof. exact (TRANS (@lem3108207) (@lem3108291)). Qed.
Lemma lem3108294 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3108295 : term260 = term217.
Proof. exact (@lem3108294 term217). Qed.
Lemma lem3108296 : term474 = term217.
Proof. exact (TRANS (@lem3108292) (@lem3108295)). Qed.
Lemma lem3108297 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3108298 : term487 = term484.
Proof. exact (MK_COMB (@lem3108297) (@lem3108296)). Qed.
Lemma lem3108299 (_32231 : int) : (real_of_int _32231) = (real_of_int _32231).
Proof. exact (eq_refl (real_of_int _32231)). Qed.
Lemma lem3108300 (_32231 : int) : (term471 _32231) = (term488 _32231).
Proof. exact (MK_COMB (@lem3108298) (@lem3108299 _32231)). Qed.
Lemma lem3108301 (_32231 : int) : (term493 _32231) = (term488 _32231).
Proof. exact (TRANS (@lem3108198 _32231) (@lem3108300 _32231)). Qed.
Lemma lem3108302 (_32231 : int) : (term488 _32231) = term217.
Proof. exact (@lem1982719 (real_of_int _32231)). Qed.
Lemma lem3108303 (_32231 : int) : (term493 _32231) = term217.
Proof. exact (TRANS (@lem3108301 _32231) (@lem3108302 _32231)). Qed.
Lemma lem3108304 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3108305 (_32231 : int) : (term494 _32231) = term490.
Proof. exact (MK_COMB (@lem3108304) (@lem3108303 _32231)). Qed.
Lemma lem3108306 : term263 = term263.
Proof. exact (eq_refl term263). Qed.
Lemma lem3108307 (_32231 : int) : (term492 _32231) = term495.
Proof. exact (MK_COMB (@lem3108305 _32231) (@lem3108306)). Qed.
Lemma lem3108308 (_32231 : int) : (term491 _32231) = term495.
Proof. exact (TRANS (@lem3108197 _32231) (@lem3108307 _32231)). Qed.
Lemma lem3108309 : term495 = term263.
Proof. exact (@lem1982721 term263). Qed.
Lemma lem3108310 (_32231 : int) : (term491 _32231) = term263.
Proof. exact (TRANS (@lem3108308 _32231) (@lem3108309)). Qed.
Lemma lem3108311 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3108312 (_32231 : int) : (term524 _32231) = term497.
Proof. exact (MK_COMB (@lem3108311) (@lem3108310 _32231)). Qed.
Lemma lem3108313 : term217 = term217.
Proof. exact (eq_refl term217). Qed.
Lemma lem3108314 (_32231 : int) : (term523 _32231) = term498.
Proof. exact (MK_COMB (@lem3108312 _32231) (@lem3108313)). Qed.
Lemma lem3108315 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : term498.
Proof. exact (EQ_MP (@lem3108314 _32231) (@lem3108196 _32231 _32232 h1)). Qed.
Lemma lem3108317 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3108318 : term498 = term499.
Proof. exact (@lem3108317 term217 term263). Qed.
Lemma lem3108320 (x : nat) : (term261 x) = (term262 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3108321 : term263 = term264.
Proof. exact (@lem3108320 term131). Qed.
Lemma lem3108323 (x : nat) : (real_of_num x) = (term259 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3108324 : term217 = term260.
Proof. exact (@lem3108323 (NUMERAL 0)). Qed.
Lemma lem3108325 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3108326 : term219 = term500.
Proof. exact (MK_COMB (@lem3108325) (@lem3108324)). Qed.
Lemma lem3108327 : term499 = term501.
Proof. exact (MK_COMB (@lem3108326) (@lem3108321)). Qed.
Lemma lem3108328 : term502.
Proof. exact (@lem1980026 term217 term224 term263 term224). Qed.
Lemma lem3108330 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3108331 : term440 = term446.
Proof. exact (@lem3108330 (NUMERAL 0) term131). Qed.
Lemma lem3108332 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3108333 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3108334 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3108333 h1) (fun h1 : term446 = True => @lem3108332)). Qed.
Lemma lem3108335 : term446 = True.
Proof. exact (EQ_MP (@lem3108334) (@lem3108332)). Qed.
Lemma lem3108336 : term440 = True.
Proof. exact (TRANS (@lem3108331) (@lem3108335)). Qed.
Lemma lem3108337 : True = term440.
Proof. exact (SYM (@lem3108336)). Qed.
Lemma lem3108338 : term440.
Proof. exact (EQ_MP (@lem3108337) (@lem0)). Qed.
Lemma lem3108339 : term503.
Proof. exact (@lem3108328 (@lem3108338)). Qed.
Lemma lem3108341 (m : nat) (n : nat) : (term445 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3108342 : term440 = term446.
Proof. exact (@lem3108341 (NUMERAL 0) term131). Qed.
Lemma lem3108343 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3108344 (h1 : term447 = (BIT1 0)) : term446 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3108345 : (term447 = (BIT1 0)) = (term446 = True).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3108344 h1) (fun h1 : term446 = True => @lem3108343)). Qed.
Lemma lem3108346 : term446 = True.
Proof. exact (EQ_MP (@lem3108345) (@lem3108343)). Qed.
Lemma lem3108347 : term440 = True.
Proof. exact (TRANS (@lem3108342) (@lem3108346)). Qed.
Lemma lem3108348 : True = term440.
Proof. exact (SYM (@lem3108347)). Qed.
Lemma lem3108349 : term440.
Proof. exact (EQ_MP (@lem3108348) (@lem0)). Qed.
Lemma lem3108350 : term501 = term504.
Proof. exact (@lem3108339 (@lem3108349)). Qed.
Lemma lem3108352 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3108353 : term288 = term293.
Proof. exact (@lem3108352 term131 term131). Qed.
Lemma lem3108354 : (term274 = (BIT1 0)) = (term275 = term131).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3108355 : term275 = term131.
Proof. exact (EQ_MP (@lem3108354) (@lem940073)). Qed.
Lemma lem3108356 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3108357 : term273 = term224.
Proof. exact (MK_COMB (@lem3108356) (@lem3108355)). Qed.
Lemma lem3108358 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3108359 : term293 = term263.
Proof. exact (MK_COMB (@lem3108358) (@lem3108357)). Qed.
Lemma lem3108360 : term288 = term263.
Proof. exact (TRANS (@lem3108353) (@lem3108359)). Qed.
Lemma lem3108362 (x : nat) : (term450 x) = term217.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3108363 : term451 = term217.
Proof. exact (@lem3108362 term131). Qed.
Lemma lem3108364 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3108365 : term505 = term219.
Proof. exact (MK_COMB (@lem3108364) (@lem3108363)). Qed.
Lemma lem3108366 : term504 = term499.
Proof. exact (MK_COMB (@lem3108365) (@lem3108360)). Qed.
Lemma lem3108368 (m : nat) (n : nat) : (term506 m n) = (term507 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3108369 : term499 = term508.
Proof. exact (@lem3108368 (NUMERAL 0) term131). Qed.
Lemma lem3108370 : term447 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3108371 (h1 : term447 = (BIT1 0)) : (term131 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3108372 : (term447 = (BIT1 0)) = ((term131 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term447 = (BIT1 0) => @lem3108371 h1) (fun h1 : (term131 = (NUMERAL 0)) = False => @lem3108370)). Qed.
Lemma lem3108373 : (term131 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3108372) (@lem3108370)). Qed.
Lemma lem3108374 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3108375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3108376 : term509 = (and True).
Proof. exact (MK_COMB (@lem3108375) (@lem3108374)). Qed.
Lemma lem3108377 : term508 = (True /\ False).
Proof. exact (MK_COMB (@lem3108376) (@lem3108373)). Qed.
Lemma lem3108379 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3108380 : term508 = False.
Proof. exact (TRANS (@lem3108377) (@lem3108379)). Qed.
Lemma lem3108381 : term499 = False.
Proof. exact (TRANS (@lem3108369) (@lem3108380)). Qed.
Lemma lem3108382 : term504 = False.
Proof. exact (TRANS (@lem3108366) (@lem3108381)). Qed.
Lemma lem3108383 : term501 = False.
Proof. exact (TRANS (@lem3108350) (@lem3108382)). Qed.
Lemma lem3108384 : term499 = False.
Proof. exact (TRANS (@lem3108327) (@lem3108383)). Qed.
Lemma lem3108385 : term498 = False.
Proof. exact (TRANS (@lem3108318) (@lem3108384)). Qed.
Lemma lem3108386 (_32231 : int) (_32232 : int) (h1 : term568 _32231 _32232) : False.
Proof. exact (EQ_MP (@lem3108385) (@lem3108315 _32231 _32232 h1)). Qed.
Lemma lem3108387 (_32231 : int) (_32232 : int) (h1 : term412 _32231 _32232) : False.
Proof. exact (or_elim (@lem3107587 _32231 _32232 h1) (fun h0 : term567 _32231 _32232 => @lem3107880 _32231 _32232 h0) (fun h0 : term568 _32231 _32232 => @lem3108386 _32231 _32232 h0)). Qed.
Lemma lem3108388 (_32231 : int) (_32232 : int) (h1 : term421 _32231 _32232) : False.
Proof. exact (or_elim (@lem3106822 _32231 _32232 h1) (fun h0 : term416 _32231 _32232 => @lem3107586 _32231 _32232 h0) (fun h0 : term412 _32231 _32232 => @lem3108387 _32231 _32232 h0)). Qed.
Lemma lem3108389 (_32231 : int) (_32232 : int) (h1 : term437 _32231 _32232) : False.
Proof. exact (or_elim (@lem3105254 _32231 _32232 h1) (fun h0 : term434 _32231 _32232 => @lem3106821 _32231 _32232 h0) (fun h0 : term421 _32231 _32232 => @lem3108388 _32231 _32232 h0)). Qed.
Lemma lem3108391 (_32231 : int) (_32232 : int) (h1 : term437 _32231 _32232) : term437 _32231 _32232.
Proof. exact (h1). Qed.
Lemma lem3108392 (_32231 : int) (_32232 : int) (h1 : term437 _32231 _32232) : (term437 _32231 _32232) = False.
Proof. exact (prop_ext (fun h2 : term437 _32231 _32232 => @lem3108389 _32231 _32232 h1) (fun h2 : False => @lem3108391 _32231 _32232 h1)). Qed.
Lemma lem3108393 (_32231 : int) (_32232 : int) (h1 : term437 _32231 _32232) : False.
Proof. exact (EQ_MP (@lem3108392 _32231 _32232 h1) (@lem3108391 _32231 _32232 h1)). Qed.
Lemma lem3108394 (_32232 : int) (_32231 : int) (h1 : term255 _32232 _32231) : term255 _32232 _32231.
Proof. exact (h1). Qed.
Lemma lem3108395 (_32232 : int) (_32231 : int) (h1 : term255 _32232 _32231) : term437 _32231 _32232.
Proof. exact (EQ_MP (@lem3105208 _32231 _32232) (@lem3108394 _32232 _32231 h1)). Qed.
Lemma lem3108396 (_32232 : int) (_32231 : int) (h1 : term255 _32232 _32231) : (term437 _32231 _32232) = False.
Proof. exact (prop_ext (fun h2 : term437 _32231 _32232 => @lem3108393 _32231 _32232 h2) (fun h2 : False => @lem3108395 _32232 _32231 h1)). Qed.
Lemma lem3108397 (_32232 : int) (_32231 : int) (h1 : term255 _32232 _32231) : False.
Proof. exact (EQ_MP (@lem3108396 _32232 _32231 h1) (@lem3108395 _32232 _32231 h1)). Qed.
Lemma lem3108398 (_32232 : int) (_32231 : int) : term574 _32232 _32231.
Proof. exact (fun h0 : term255 _32232 _32231 => @lem3108397 _32232 _32231 h0). Qed.
Lemma lem3108399 (_32232 : int) (_32231 : int) : term575 _32232 _32231.
Proof. exact (@lem1386578 (term576 _32232 _32231)). Qed.
Lemma lem3108402 (_32232 : int) (_32231 : int) : term576 _32232 _32231.
Proof. exact (@lem3108399 _32232 _32231 (@lem3108398 _32232 _32231)). Qed.
Lemma lem3108403 (_32231 : int) (_32232 : int) : (term254 _32232 _32231) = (term211 _32231 _32232).
Proof. exact (SYM (@lem3104402 _32232 _32231)). Qed.
Lemma lem3108404 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3108405 (_32231 : int) (_32232 : int) : (term576 _32232 _32231) = (term172 _32231 _32232).
Proof. exact (MK_COMB (@lem3108404) (@lem3108403 _32231 _32232)). Qed.
Lemma lem3108406 (_32231 : int) (_32232 : int) : term172 _32231 _32232.
Proof. exact (EQ_MP (@lem3108405 _32231 _32232) (@lem3108402 _32232 _32231)). Qed.
Lemma lem3108407 (_32231 : int) (_32232 : int) : term173 _32231 _32232.
Proof. exact (EQ_MP (@lem3104129 _32231 _32232) (@lem3108406 _32231 _32232)). Qed.
Lemma lem3108408 (m : nat) (n : nat) : term577 m n.
Proof. exact (@lem3108407 (int_of_num m) (int_of_num n)). Qed.
Lemma lem3108409 (m : nat) (n : nat) : term578 m n.
Proof. exact (@lem3108408 m n (@lem3104125 m)). Qed.
Lemma lem3108410 (m : nat) (n : nat) : term169 m n.
Proof. exact (@lem3108409 m n (@lem3104128 n)). Qed.
Lemma lem3108411 (m : nat) (n : nat) : (term169 m n) = (term153 m n).
Proof. exact (SYM (@lem3104122 m n)). Qed.
Lemma lem3108412 (m : nat) (n : nat) : term153 m n.
Proof. exact (EQ_MP (@lem3108411 m n) (@lem3108410 m n)). Qed.
Lemma lem3108413 (m : nat) (n : nat) : (term153 m n) = ((term153 m n) = True).
Proof. exact (@lem7 (term153 m n)). Qed.
Lemma lem3108414 (m : nat) (n : nat) : (term153 m n) = True.
Proof. exact (EQ_MP (@lem3108413 m n) (@lem3108412 m n)). Qed.
Lemma lem3108415 (m : nat) (n : nat) : True = (term153 m n).
Proof. exact (SYM (@lem3108414 m n)). Qed.
Lemma lem3108416 (m : nat) (n : nat) : term153 m n.
Proof. exact (EQ_MP (@lem3108415 m n) (@lem0)). Qed.
Lemma lem3108417 (n : nat) (m : nat) (h1 : term7 n m) : num_divides n m.
Proof. exact (proj2 (@lem3103880 n m h1)). Qed.
Lemma lem3108418 (n : nat) (m : nat) (h1 : term7 n m) : num_divides m n.
Proof. exact (proj1 (@lem3103880 n m h1)). Qed.
Lemma lem3108419 (n : nat) (m : nat) (h1 : num_divides n m) : term150 m n.
Proof. exact (@lem3108416 m n (@lem3103885 n m h1)). Qed.
Lemma lem3108420 (n : nat) (m : nat) (h1 : num_divides m n) (h2 : num_divides n m) : m = n.
Proof. exact (@lem3108419 n m h2 (@lem3103889 m n h1)). Qed.
Lemma lem3108421 (m : nat) (n : nat) (h1 : term7 n m) (h2 : num_divides m n) : (num_divides n m) = (m = n).
Proof. exact (prop_ext (fun h3 : num_divides n m => @lem3108420 n m h2 h3) (fun h3 : m = n => @lem3108417 n m h1)). Qed.
Lemma lem3108422 (m : nat) (n : nat) (h1 : term7 n m) (h2 : num_divides m n) : m = n.
Proof. exact (EQ_MP (@lem3108421 m n h1 h2) (@lem3108417 n m h1)). Qed.
Lemma lem3108423 (n : nat) (m : nat) (h1 : term7 n m) : (num_divides m n) = (m = n).
Proof. exact (prop_ext (fun h2 : num_divides m n => @lem3108422 m n h1 h2) (fun h2 : m = n => @lem3108418 n m h1)). Qed.
Lemma lem3108424 (n : nat) (m : nat) (h1 : term7 n m) : m = n.
Proof. exact (EQ_MP (@lem3108423 n m h1) (@lem3108418 n m h1)). Qed.
Lemma lem3108425 (m : nat) (n : nat) : term579 m n.
Proof. exact (fun h0 : term7 n m => @lem3108424 n m h0). Qed.
Lemma lem3108426 (n : nat) (m : nat) : term580 n m.
Proof. exact (conj (@lem3108425 m n) (@lem3103879 n m)). Qed.
Lemma lem3108427 (m : nat) (n : nat) : (term580 n m) = ((term7 n m) = (m = n)).
Proof. exact (@lem32 (term7 n m) (m = n)). Qed.
Lemma lem3108428 (m : nat) (n : nat) : (term7 n m) = (m = n).
Proof. exact (EQ_MP (@lem3108427 m n) (@lem3108426 n m)). Qed.
Lemma lem3108433 (m : nat) : term581 m.
Proof. exact (fun n : nat => @lem3108428 m n). Qed.
Lemma lem3108438 : term582.
Proof. exact (fun m : nat => @lem3108433 m). Qed.
