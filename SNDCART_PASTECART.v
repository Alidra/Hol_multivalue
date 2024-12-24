Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SNDCART_PASTECART_term_abbrevs.
Require Import ADD_SUB_spec.
Require Import CART_EQ_spec.
Require Import INT_POS_spec.
Require Import LAMBDA_BETA_spec.
Require Import pastecart_spec.
Require Import sndcart_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032098_spec.
Require Import thm12653_spec.
Require Import thm129_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm137_spec.
Require Import thm1386578_spec.
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
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
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
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
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
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7640410_spec.
Require Import thm7640437_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7643311 (i : nat) (a : nat) : (term0 i a) = (term1 i a).
Proof. exact (@lem17265 (term2 i) (term3 i a)). Qed.
Lemma lem7643312 (a : nat) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7643319 (a : nat) (i : nat) : (Nat.add i a) = (Nat.add a i).
Proof. exact (@lem1032098 a i). Qed.
Lemma lem7643320 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7643321 (a : nat) (i : nat) : (term4 i a) = (term4 a i).
Proof. exact (MK_COMB (@lem7643320) (@lem7643319 a i)). Qed.
Lemma lem7643322 (i : nat) (a : nat) : (term5 i a) = (term6 i a).
Proof. exact (MK_COMB (@lem7643321 a i) (@lem7643312 a)). Qed.
Lemma lem7643323 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7643324 (i : nat) (a : nat) : (term3 i a) = (term7 i a).
Proof. exact (MK_COMB (@lem7643323) (@lem7643322 i a)). Qed.
Lemma lem7643333 (i : nat) : (term8 i) = (term8 i).
Proof. exact (eq_refl (term8 i)). Qed.
Lemma lem7643334 (i : nat) (a : nat) : (term1 i a) = (term9 i a).
Proof. exact (MK_COMB (@lem7643333 i) (@lem7643324 i a)). Qed.
Lemma lem7643337 (i : nat) (a : nat) : (term0 i a) = (term9 i a).
Proof. exact (TRANS (@lem7643311 i a) (@lem7643334 i a)). Qed.
Lemma lem7643339 (m : nat) (n : nat) : (Peano.le m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7643340 (i : nat) : (term2 i) = (term11 i).
Proof. exact (@lem7643339 term12 i). Qed.
Lemma lem7643341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7643342 (i : nat) : (term13 i) = (term14 i).
Proof. exact (MK_COMB (@lem7643341) (@lem7643340 i)). Qed.
Lemma lem7643343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7643344 (i : nat) : (term8 i) = (term15 i).
Proof. exact (MK_COMB (@lem7643343) (@lem7643342 i)). Qed.
Lemma lem7643346 (m : nat) (n : nat) : (Peano.le m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7643347 (i : nat) (a : nat) : (term6 i a) = (term16 i a).
Proof. exact (@lem7643346 (Nat.add a i) a). Qed.
Lemma lem7643349 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7643350 (a : nat) (i : nat) : (term17 a i) = (term18 a i).
Proof. exact (@lem7643349 a i). Qed.
Lemma lem7643351 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem7643352 (a : nat) (i : nat) : (term19 a i) = (term20 a i).
Proof. exact (MK_COMB (@lem7643351) (@lem7643350 a i)). Qed.
Lemma lem7643353 (a : nat) : (int_of_num a) = (int_of_num a).
Proof. exact (eq_refl (int_of_num a)). Qed.
Lemma lem7643354 (i : nat) (a : nat) : (term16 i a) = (term21 i a).
Proof. exact (MK_COMB (@lem7643352 a i) (@lem7643353 a)). Qed.
Lemma lem7643355 (i : nat) (a : nat) : (term6 i a) = (term21 i a).
Proof. exact (TRANS (@lem7643347 i a) (@lem7643354 i a)). Qed.
Lemma lem7643356 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7643357 (i : nat) (a : nat) : (term7 i a) = (term22 i a).
Proof. exact (MK_COMB (@lem7643356) (@lem7643355 i a)). Qed.
Lemma lem7643358 (i : nat) (a : nat) : (term9 i a) = (term23 i a).
Proof. exact (MK_COMB (@lem7643344 i) (@lem7643357 i a)). Qed.
Lemma lem7643359 (i : nat) (a : nat) : (term0 i a) = (term23 i a).
Proof. exact (TRANS (@lem7643337 i a) (@lem7643358 i a)). Qed.
Lemma lem7643360 (a : nat) : term24 a.
Proof. exact (@lem2307535 a). Qed.
Lemma lem7643361 (a : nat) : (term24 a) = (term25 a).
Proof. exact (eq_refl (term24 a)). Qed.
Lemma lem7643362 (a : nat) : term25 a.
Proof. exact (EQ_MP (@lem7643361 a) (@lem7643360 a)). Qed.
Lemma lem7643363 (i : nat) : term24 i.
Proof. exact (@lem2307535 i). Qed.
Lemma lem7643364 (i : nat) : (term24 i) = (term25 i).
Proof. exact (eq_refl (term24 i)). Qed.
Lemma lem7643365 (i : nat) : term25 i.
Proof. exact (EQ_MP (@lem7643364 i) (@lem7643363 i)). Qed.
Lemma lem7643366 (_98505 : int) (_98504 : int) : (term26 _98505 _98504) = (term27 _98505 _98504).
Proof. exact (@lem2318604 (term27 _98505 _98504)). Qed.
Lemma lem7643382 (_98505 : int) : (term28 _98505) = (term29 _98505).
Proof. exact (@lem16933 (term29 _98505)). Qed.
Lemma lem7643385 (_98505 : int) (_98504 : int) : (term30 _98505 _98504) = (term31 _98505 _98504).
Proof. exact (@lem16933 (term31 _98505 _98504)). Qed.
Lemma lem7643386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7643387 (_98505 : int) : (term32 _98505) = (term33 _98505).
Proof. exact (MK_COMB (@lem7643386) (@lem7643382 _98505)). Qed.
Lemma lem7643388 (_98505 : int) (_98504 : int) : (term34 _98505 _98504) = (term35 _98505 _98504).
Proof. exact (MK_COMB (@lem7643387 _98505) (@lem7643385 _98505 _98504)). Qed.
Lemma lem7643389 (_98505 : int) (_98504 : int) : (term36 _98505 _98504) = (term34 _98505 _98504).
Proof. exact (@lem17160 (term37 _98505) (term38 _98505 _98504)). Qed.
Lemma lem7643390 (_98505 : int) (_98504 : int) : (term36 _98505 _98504) = (term35 _98505 _98504).
Proof. exact (TRANS (@lem7643389 _98505 _98504) (@lem7643388 _98505 _98504)). Qed.
Lemma lem7643392 (_98505 : int) : (term39 _98505) = (term39 _98505).
Proof. exact (eq_refl (term39 _98505)). Qed.
Lemma lem7643393 (_98505 : int) (_98504 : int) : (term40 _98505 _98504) = (term41 _98505 _98504).
Proof. exact (MK_COMB (@lem7643392 _98505) (@lem7643390 _98505 _98504)). Qed.
Lemma lem7643394 (_98505 : int) (_98504 : int) : (term42 _98505 _98504) = (term40 _98505 _98504).
Proof. exact (@lem17362 (term43 _98505) (term44 _98505 _98504)). Qed.
Lemma lem7643395 (_98505 : int) (_98504 : int) : (term42 _98505 _98504) = (term41 _98505 _98504).
Proof. exact (TRANS (@lem7643394 _98505 _98504) (@lem7643393 _98505 _98504)). Qed.
Lemma lem7643397 (_98504 : int) : (term39 _98504) = (term39 _98504).
Proof. exact (eq_refl (term39 _98504)). Qed.
Lemma lem7643398 (_98505 : int) (_98504 : int) : (term45 _98505 _98504) = (term46 _98505 _98504).
Proof. exact (MK_COMB (@lem7643397 _98504) (@lem7643395 _98505 _98504)). Qed.
Lemma lem7643399 (_98505 : int) (_98504 : int) : (term47 _98505 _98504) = (term45 _98505 _98504).
Proof. exact (@lem17362 (term43 _98504) (term48 _98505 _98504)). Qed.
Lemma lem7643415 (_98505 : int) (_98504 : int) : (term47 _98505 _98504) = (term46 _98505 _98504).
Proof. exact (TRANS (@lem7643399 _98505 _98504) (@lem7643398 _98505 _98504)). Qed.
Lemma lem7643418 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7643419 (_98504 : int) : (term43 _98504) = (term50 _98504).
Proof. exact (@lem7643418 term51 _98504). Qed.
Lemma lem7643421 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7643422 : term53 = term54.
Proof. exact (@lem7643421 (NUMERAL 0)). Qed.
Lemma lem7643423 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7643424 : term55 = term56.
Proof. exact (MK_COMB (@lem7643423) (@lem7643422)). Qed.
Lemma lem7643425 (_98504 : int) : (real_of_int _98504) = (real_of_int _98504).
Proof. exact (eq_refl (real_of_int _98504)). Qed.
Lemma lem7643426 (_98504 : int) : (term50 _98504) = (term57 _98504).
Proof. exact (MK_COMB (@lem7643424) (@lem7643425 _98504)). Qed.
Lemma lem7643428 (_98504 : int) : (term43 _98504) = (term57 _98504).
Proof. exact (TRANS (@lem7643419 _98504) (@lem7643426 _98504)). Qed.
Lemma lem7643431 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7643432 (_98505 : int) : (term43 _98505) = (term50 _98505).
Proof. exact (@lem7643431 term51 _98505). Qed.
Lemma lem7643434 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7643435 : term53 = term54.
Proof. exact (@lem7643434 (NUMERAL 0)). Qed.
Lemma lem7643436 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7643437 : term55 = term56.
Proof. exact (MK_COMB (@lem7643436) (@lem7643435)). Qed.
Lemma lem7643438 (_98505 : int) : (real_of_int _98505) = (real_of_int _98505).
Proof. exact (eq_refl (real_of_int _98505)). Qed.
Lemma lem7643439 (_98505 : int) : (term50 _98505) = (term57 _98505).
Proof. exact (MK_COMB (@lem7643437) (@lem7643438 _98505)). Qed.
Lemma lem7643441 (_98505 : int) : (term43 _98505) = (term57 _98505).
Proof. exact (TRANS (@lem7643432 _98505) (@lem7643439 _98505)). Qed.
Lemma lem7643444 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7643445 (_98505 : int) : (term29 _98505) = (term58 _98505).
Proof. exact (@lem7643444 term59 _98505). Qed.
Lemma lem7643447 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7643448 : term60 = term61.
Proof. exact (@lem7643447 term12). Qed.
Lemma lem7643449 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7643450 : term62 = term63.
Proof. exact (MK_COMB (@lem7643449) (@lem7643448)). Qed.
Lemma lem7643451 (_98505 : int) : (real_of_int _98505) = (real_of_int _98505).
Proof. exact (eq_refl (real_of_int _98505)). Qed.
Lemma lem7643452 (_98505 : int) : (term58 _98505) = (term64 _98505).
Proof. exact (MK_COMB (@lem7643450) (@lem7643451 _98505)). Qed.
Lemma lem7643454 (_98505 : int) : (term29 _98505) = (term64 _98505).
Proof. exact (TRANS (@lem7643445 _98505) (@lem7643452 _98505)). Qed.
Lemma lem7643457 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7643458 (_98505 : int) (_98504 : int) : (term31 _98505 _98504) = (term65 _98505 _98504).
Proof. exact (@lem7643457 (int_add _98504 _98505) _98504). Qed.
Lemma lem7643460 (x : int) (y : int) : (term66 x y) = (term67 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7643461 (_98504 : int) (_98505 : int) : (term66 _98504 _98505) = (term67 _98504 _98505).
Proof. exact (@lem7643460 _98504 _98505). Qed.
Lemma lem7643462 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7643463 (_98504 : int) (_98505 : int) : (term68 _98504 _98505) = (term69 _98504 _98505).
Proof. exact (MK_COMB (@lem7643462) (@lem7643461 _98504 _98505)). Qed.
Lemma lem7643464 (_98504 : int) : (real_of_int _98504) = (real_of_int _98504).
Proof. exact (eq_refl (real_of_int _98504)). Qed.
Lemma lem7643465 (_98505 : int) (_98504 : int) : (term65 _98505 _98504) = (term70 _98505 _98504).
Proof. exact (MK_COMB (@lem7643463 _98504 _98505) (@lem7643464 _98504)). Qed.
Lemma lem7643467 (_98505 : int) (_98504 : int) : (term31 _98505 _98504) = (term70 _98505 _98504).
Proof. exact (TRANS (@lem7643458 _98505 _98504) (@lem7643465 _98505 _98504)). Qed.
Lemma lem7643468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7643469 (_98505 : int) : (term33 _98505) = (term71 _98505).
Proof. exact (MK_COMB (@lem7643468) (@lem7643454 _98505)). Qed.
Lemma lem7643470 (_98505 : int) (_98504 : int) : (term35 _98505 _98504) = (term72 _98505 _98504).
Proof. exact (MK_COMB (@lem7643469 _98505) (@lem7643467 _98505 _98504)). Qed.
Lemma lem7643471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7643472 (_98505 : int) : (term39 _98505) = (term73 _98505).
Proof. exact (MK_COMB (@lem7643471) (@lem7643441 _98505)). Qed.
Lemma lem7643473 (_98505 : int) (_98504 : int) : (term41 _98505 _98504) = (term74 _98505 _98504).
Proof. exact (MK_COMB (@lem7643472 _98505) (@lem7643470 _98505 _98504)). Qed.
Lemma lem7643474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7643475 (_98504 : int) : (term39 _98504) = (term73 _98504).
Proof. exact (MK_COMB (@lem7643474) (@lem7643428 _98504)). Qed.
Lemma lem7643476 (_98505 : int) (_98504 : int) : (term46 _98505 _98504) = (term75 _98505 _98504).
Proof. exact (MK_COMB (@lem7643475 _98504) (@lem7643473 _98505 _98504)). Qed.
Lemma lem7643477 (_98505 : int) (_98504 : int) : (term47 _98505 _98504) = (term75 _98505 _98504).
Proof. exact (TRANS (@lem7643415 _98505 _98504) (@lem7643476 _98505 _98504)). Qed.
Lemma lem7643481 (t : Prop) : (term76 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7643517 (_98505 : int) (_98504 : int) : (term77 _98505 _98504) = (term75 _98505 _98504).
Proof. exact (@lem7643481 (term75 _98505 _98504)). Qed.
Lemma lem7643518 (_98504 : int) : (term57 _98504) = (term78 _98504).
Proof. exact (@lem1988287 (real_of_int _98504) term54). Qed.
Lemma lem7643524 (_98504 : int) : (term79 _98504) = (term80 _98504).
Proof. exact (@lem1982792 (real_of_int _98504) term54). Qed.
Lemma lem7643526 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7643527 : term54 = term82.
Proof. exact (@lem7643526 (NUMERAL 0)). Qed.
Lemma lem7643529 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7643530 : term85 = term86.
Proof. exact (@lem7643529 term12). Qed.
Lemma lem7643531 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7643532 : term87 = term88.
Proof. exact (MK_COMB (@lem7643531) (@lem7643530)). Qed.
Lemma lem7643533 : term89 = term90.
Proof. exact (MK_COMB (@lem7643532) (@lem7643527)). Qed.
Lemma lem7643534 : term90 = term91.
Proof. exact (@lem1981613 term85 term54 term61 term61). Qed.
Lemma lem7643536 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7643537 : term94 = term95.
Proof. exact (@lem7643536 term12 term12). Qed.
Lemma lem7643538 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7643539 : term97 = term12.
Proof. exact (EQ_MP (@lem7643538) (@lem940073)). Qed.
Lemma lem7643540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7643541 : term95 = term61.
Proof. exact (MK_COMB (@lem7643540) (@lem7643539)). Qed.
Lemma lem7643542 : term94 = term61.
Proof. exact (TRANS (@lem7643537) (@lem7643541)). Qed.
Lemma lem7643544 (x : nat) : (term98 x) = term54.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7643545 : term89 = term54.
Proof. exact (@lem7643544 term12). Qed.
Lemma lem7643546 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7643547 : term99 = term100.
Proof. exact (MK_COMB (@lem7643546) (@lem7643545)). Qed.
Lemma lem7643548 : term91 = term82.
Proof. exact (MK_COMB (@lem7643547) (@lem7643542)). Qed.
Lemma lem7643549 : term90 = term82.
Proof. exact (TRANS (@lem7643534) (@lem7643548)). Qed.
Lemma lem7643550 : term89 = term82.
Proof. exact (TRANS (@lem7643533) (@lem7643549)). Qed.
Lemma lem7643552 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7643553 : term82 = term54.
Proof. exact (@lem7643552 term54). Qed.
Lemma lem7643554 : term89 = term54.
Proof. exact (TRANS (@lem7643550) (@lem7643553)). Qed.
Lemma lem7643555 (_98504 : int) : (term102 _98504) = (term102 _98504).
Proof. exact (eq_refl (term102 _98504)). Qed.
Lemma lem7643556 (_98504 : int) : (term80 _98504) = (term103 _98504).
Proof. exact (MK_COMB (@lem7643555 _98504) (@lem7643554)). Qed.
Lemma lem7643557 (_98504 : int) : (term103 _98504) = (real_of_int _98504).
Proof. exact (@lem1982723 (real_of_int _98504)). Qed.
Lemma lem7643558 (_98504 : int) : (term80 _98504) = (real_of_int _98504).
Proof. exact (TRANS (@lem7643556 _98504) (@lem7643557 _98504)). Qed.
Lemma lem7643560 (_98504 : int) : (term79 _98504) = (real_of_int _98504).
Proof. exact (TRANS (@lem7643524 _98504) (@lem7643558 _98504)). Qed.
Lemma lem7643561 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7643562 (_98504 : int) : (term104 _98504) = (term105 _98504).
Proof. exact (MK_COMB (@lem7643561) (@lem7643560 _98504)). Qed.
Lemma lem7643563 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7643564 (_98504 : int) : (term78 _98504) = (term106 _98504).
Proof. exact (MK_COMB (@lem7643562 _98504) (@lem7643563)). Qed.
Lemma lem7643565 (_98504 : int) : (term57 _98504) = (term106 _98504).
Proof. exact (TRANS (@lem7643518 _98504) (@lem7643564 _98504)). Qed.
Lemma lem7643566 (_98505 : int) : (term57 _98505) = (term78 _98505).
Proof. exact (@lem1988287 (real_of_int _98505) term54). Qed.
Lemma lem7643572 (_98505 : int) : (term79 _98505) = (term80 _98505).
Proof. exact (@lem1982792 (real_of_int _98505) term54). Qed.
Lemma lem7643574 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7643575 : term54 = term82.
Proof. exact (@lem7643574 (NUMERAL 0)). Qed.
Lemma lem7643577 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7643578 : term85 = term86.
Proof. exact (@lem7643577 term12). Qed.
Lemma lem7643579 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7643580 : term87 = term88.
Proof. exact (MK_COMB (@lem7643579) (@lem7643578)). Qed.
Lemma lem7643581 : term89 = term90.
Proof. exact (MK_COMB (@lem7643580) (@lem7643575)). Qed.
Lemma lem7643582 : term90 = term91.
Proof. exact (@lem1981613 term85 term54 term61 term61). Qed.
Lemma lem7643584 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7643585 : term94 = term95.
Proof. exact (@lem7643584 term12 term12). Qed.
Lemma lem7643586 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7643587 : term97 = term12.
Proof. exact (EQ_MP (@lem7643586) (@lem940073)). Qed.
Lemma lem7643588 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7643589 : term95 = term61.
Proof. exact (MK_COMB (@lem7643588) (@lem7643587)). Qed.
Lemma lem7643590 : term94 = term61.
Proof. exact (TRANS (@lem7643585) (@lem7643589)). Qed.
Lemma lem7643592 (x : nat) : (term98 x) = term54.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7643593 : term89 = term54.
Proof. exact (@lem7643592 term12). Qed.
Lemma lem7643594 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7643595 : term99 = term100.
Proof. exact (MK_COMB (@lem7643594) (@lem7643593)). Qed.
Lemma lem7643596 : term91 = term82.
Proof. exact (MK_COMB (@lem7643595) (@lem7643590)). Qed.
Lemma lem7643597 : term90 = term82.
Proof. exact (TRANS (@lem7643582) (@lem7643596)). Qed.
Lemma lem7643598 : term89 = term82.
Proof. exact (TRANS (@lem7643581) (@lem7643597)). Qed.
Lemma lem7643600 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7643601 : term82 = term54.
Proof. exact (@lem7643600 term54). Qed.
Lemma lem7643602 : term89 = term54.
Proof. exact (TRANS (@lem7643598) (@lem7643601)). Qed.
Lemma lem7643603 (_98505 : int) : (term102 _98505) = (term102 _98505).
Proof. exact (eq_refl (term102 _98505)). Qed.
Lemma lem7643604 (_98505 : int) : (term80 _98505) = (term103 _98505).
Proof. exact (MK_COMB (@lem7643603 _98505) (@lem7643602)). Qed.
Lemma lem7643605 (_98505 : int) : (term103 _98505) = (real_of_int _98505).
Proof. exact (@lem1982723 (real_of_int _98505)). Qed.
Lemma lem7643606 (_98505 : int) : (term80 _98505) = (real_of_int _98505).
Proof. exact (TRANS (@lem7643604 _98505) (@lem7643605 _98505)). Qed.
Lemma lem7643608 (_98505 : int) : (term79 _98505) = (real_of_int _98505).
Proof. exact (TRANS (@lem7643572 _98505) (@lem7643606 _98505)). Qed.
Lemma lem7643609 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7643610 (_98505 : int) : (term104 _98505) = (term105 _98505).
Proof. exact (MK_COMB (@lem7643609) (@lem7643608 _98505)). Qed.
Lemma lem7643611 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7643612 (_98505 : int) : (term78 _98505) = (term106 _98505).
Proof. exact (MK_COMB (@lem7643610 _98505) (@lem7643611)). Qed.
Lemma lem7643613 (_98505 : int) : (term57 _98505) = (term106 _98505).
Proof. exact (TRANS (@lem7643566 _98505) (@lem7643612 _98505)). Qed.
Lemma lem7643614 (_98505 : int) : (term64 _98505) = (term107 _98505).
Proof. exact (@lem1988287 (real_of_int _98505) term61). Qed.
Lemma lem7643620 (_98505 : int) : (term108 _98505) = (term109 _98505).
Proof. exact (@lem1982792 (real_of_int _98505) term61). Qed.
Lemma lem7643622 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7643623 : term61 = term110.
Proof. exact (@lem7643622 term12). Qed.
Lemma lem7643625 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7643626 : term85 = term86.
Proof. exact (@lem7643625 term12). Qed.
Lemma lem7643627 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7643628 : term87 = term88.
Proof. exact (MK_COMB (@lem7643627) (@lem7643626)). Qed.
Lemma lem7643629 : term111 = term112.
Proof. exact (MK_COMB (@lem7643628) (@lem7643623)). Qed.
Lemma lem7643630 : term112 = term113.
Proof. exact (@lem1981613 term85 term61 term61 term61). Qed.
Lemma lem7643632 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7643633 : term94 = term95.
Proof. exact (@lem7643632 term12 term12). Qed.
Lemma lem7643634 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7643635 : term97 = term12.
Proof. exact (EQ_MP (@lem7643634) (@lem940073)). Qed.
Lemma lem7643636 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7643637 : term95 = term61.
Proof. exact (MK_COMB (@lem7643636) (@lem7643635)). Qed.
Lemma lem7643638 : term94 = term61.
Proof. exact (TRANS (@lem7643633) (@lem7643637)). Qed.
Lemma lem7643640 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7643641 : term111 = term116.
Proof. exact (@lem7643640 term12 term12). Qed.
Lemma lem7643642 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7643643 : term97 = term12.
Proof. exact (EQ_MP (@lem7643642) (@lem940073)). Qed.
Lemma lem7643644 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7643645 : term95 = term61.
Proof. exact (MK_COMB (@lem7643644) (@lem7643643)). Qed.
Lemma lem7643646 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7643647 : term116 = term85.
Proof. exact (MK_COMB (@lem7643646) (@lem7643645)). Qed.
Lemma lem7643648 : term111 = term85.
Proof. exact (TRANS (@lem7643641) (@lem7643647)). Qed.
Lemma lem7643649 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7643650 : term117 = term118.
Proof. exact (MK_COMB (@lem7643649) (@lem7643648)). Qed.
Lemma lem7643651 : term113 = term86.
Proof. exact (MK_COMB (@lem7643650) (@lem7643638)). Qed.
Lemma lem7643652 : term112 = term86.
Proof. exact (TRANS (@lem7643630) (@lem7643651)). Qed.
Lemma lem7643653 : term111 = term86.
Proof. exact (TRANS (@lem7643629) (@lem7643652)). Qed.
Lemma lem7643655 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7643656 : term86 = term85.
Proof. exact (@lem7643655 term85). Qed.
Lemma lem7643657 : term111 = term85.
Proof. exact (TRANS (@lem7643653) (@lem7643656)). Qed.
Lemma lem7643658 (_98505 : int) : (term102 _98505) = (term102 _98505).
Proof. exact (eq_refl (term102 _98505)). Qed.
Lemma lem7643661 (_98505 : int) : (term109 _98505) = (term119 _98505).
Proof. exact (MK_COMB (@lem7643658 _98505) (@lem7643657)). Qed.
Lemma lem7643663 (_98505 : int) : (term108 _98505) = (term119 _98505).
Proof. exact (TRANS (@lem7643620 _98505) (@lem7643661 _98505)). Qed.
Lemma lem7643664 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7643665 (_98505 : int) : (term120 _98505) = (term121 _98505).
Proof. exact (MK_COMB (@lem7643664) (@lem7643663 _98505)). Qed.
Lemma lem7643666 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7643667 (_98505 : int) : (term107 _98505) = (term122 _98505).
Proof. exact (MK_COMB (@lem7643665 _98505) (@lem7643666)). Qed.
Lemma lem7643668 (_98505 : int) : (term64 _98505) = (term122 _98505).
Proof. exact (TRANS (@lem7643614 _98505) (@lem7643667 _98505)). Qed.
Lemma lem7643669 (_98504 : int) (_98505 : int) : (term70 _98505 _98504) = (term123 _98504 _98505).
Proof. exact (@lem1988287 (real_of_int _98504) (term67 _98504 _98505)). Qed.
Lemma lem7643681 (_98504 : int) (_98505 : int) : (term124 _98504 _98505) = (term125 _98504 _98505).
Proof. exact (@lem1982792 (real_of_int _98504) (term67 _98504 _98505)). Qed.
Lemma lem7643688 (_98504 : int) (_98505 : int) : (term126 _98504 _98505) = (term127 _98504 _98505).
Proof. exact (@lem1982781 (real_of_int _98504) term85 (real_of_int _98505)). Qed.
Lemma lem7643689 (_98504 : int) : (term102 _98504) = (term102 _98504).
Proof. exact (eq_refl (term102 _98504)). Qed.
Lemma lem7643690 (_98504 : int) (_98505 : int) : (term125 _98504 _98505) = (term128 _98504 _98505).
Proof. exact (MK_COMB (@lem7643689 _98504) (@lem7643688 _98504 _98505)). Qed.
Lemma lem7643691 (_98504 : int) (_98505 : int) : (term128 _98504 _98505) = (term129 _98504 _98505).
Proof. exact (@lem1982763 (real_of_int _98504) (term130 _98504) (term130 _98505)). Qed.
Lemma lem7643692 (_98504 : int) : (term131 _98504) = (term132 _98504).
Proof. exact (@lem1982715 term85 (real_of_int _98504)). Qed.
Lemma lem7643694 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7643695 : term61 = term110.
Proof. exact (@lem7643694 term12). Qed.
Lemma lem7643697 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7643698 : term85 = term86.
Proof. exact (@lem7643697 term12). Qed.
Lemma lem7643699 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7643700 : term133 = term134.
Proof. exact (MK_COMB (@lem7643699) (@lem7643698)). Qed.
Lemma lem7643701 : term135 = term136.
Proof. exact (MK_COMB (@lem7643700) (@lem7643695)). Qed.
Lemma lem7643702 : term137.
Proof. exact (@lem1981473 term85 term61 term61 term61 term54 term61). Qed.
Lemma lem7643704 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7643705 : term139 = term140.
Proof. exact (@lem7643704 (NUMERAL 0) term12). Qed.
Lemma lem7643706 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7643707 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7643708 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7643707 h1) (fun h1 : term140 = True => @lem7643706)). Qed.
Lemma lem7643709 : term140 = True.
Proof. exact (EQ_MP (@lem7643708) (@lem7643706)). Qed.
Lemma lem7643710 : term139 = True.
Proof. exact (TRANS (@lem7643705) (@lem7643709)). Qed.
Lemma lem7643711 : True = term139.
Proof. exact (SYM (@lem7643710)). Qed.
Lemma lem7643712 : term139.
Proof. exact (EQ_MP (@lem7643711) (@lem0)). Qed.
Lemma lem7643713 : term142.
Proof. exact (@lem7643702 (@lem7643712)). Qed.
Lemma lem7643715 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7643716 : term139 = term140.
Proof. exact (@lem7643715 (NUMERAL 0) term12). Qed.
Lemma lem7643717 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7643718 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7643719 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7643718 h1) (fun h1 : term140 = True => @lem7643717)). Qed.
Lemma lem7643720 : term140 = True.
Proof. exact (EQ_MP (@lem7643719) (@lem7643717)). Qed.
Lemma lem7643721 : term139 = True.
Proof. exact (TRANS (@lem7643716) (@lem7643720)). Qed.
Lemma lem7643722 : True = term139.
Proof. exact (SYM (@lem7643721)). Qed.
Lemma lem7643723 : term139.
Proof. exact (EQ_MP (@lem7643722) (@lem0)). Qed.
Lemma lem7643724 : term143.
Proof. exact (@lem7643713 (@lem7643723)). Qed.
Lemma lem7643726 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7643727 : term139 = term140.
Proof. exact (@lem7643726 (NUMERAL 0) term12). Qed.
Lemma lem7643728 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7643729 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7643730 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7643729 h1) (fun h1 : term140 = True => @lem7643728)). Qed.
Lemma lem7643731 : term140 = True.
Proof. exact (EQ_MP (@lem7643730) (@lem7643728)). Qed.
Lemma lem7643732 : term139 = True.
Proof. exact (TRANS (@lem7643727) (@lem7643731)). Qed.
Lemma lem7643733 : True = term139.
Proof. exact (SYM (@lem7643732)). Qed.
Lemma lem7643734 : term139.
Proof. exact (EQ_MP (@lem7643733) (@lem0)). Qed.
Lemma lem7643735 : term144.
Proof. exact (@lem7643724 (@lem7643734)). Qed.
Lemma lem7643737 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7643738 : term94 = term95.
Proof. exact (@lem7643737 term12 term12). Qed.
Lemma lem7643739 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7643740 : term97 = term12.
Proof. exact (EQ_MP (@lem7643739) (@lem940073)). Qed.
Lemma lem7643741 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7643742 : term95 = term61.
Proof. exact (MK_COMB (@lem7643741) (@lem7643740)). Qed.
Lemma lem7643743 : term94 = term61.
Proof. exact (TRANS (@lem7643738) (@lem7643742)). Qed.
Lemma lem7643745 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7643746 : term111 = term116.
Proof. exact (@lem7643745 term12 term12). Qed.
Lemma lem7643747 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7643748 : term97 = term12.
Proof. exact (EQ_MP (@lem7643747) (@lem940073)). Qed.
Lemma lem7643749 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7643750 : term95 = term61.
Proof. exact (MK_COMB (@lem7643749) (@lem7643748)). Qed.
Lemma lem7643751 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7643752 : term116 = term85.
Proof. exact (MK_COMB (@lem7643751) (@lem7643750)). Qed.
Lemma lem7643753 : term111 = term85.
Proof. exact (TRANS (@lem7643746) (@lem7643752)). Qed.
Lemma lem7643754 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7643755 : term145 = term133.
Proof. exact (MK_COMB (@lem7643754) (@lem7643753)). Qed.
Lemma lem7643756 : term146 = term135.
Proof. exact (MK_COMB (@lem7643755) (@lem7643743)). Qed.
Lemma lem7643758 (m : nat) : (term147 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7643759 : term135 = term54.
Proof. exact (@lem7643758 term12). Qed.
Lemma lem7643760 : term146 = term54.
Proof. exact (TRANS (@lem7643756) (@lem7643759)). Qed.
Lemma lem7643761 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7643762 : term148 = term149.
Proof. exact (MK_COMB (@lem7643761) (@lem7643760)). Qed.
Lemma lem7643763 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem7643764 : term150 = term151.
Proof. exact (MK_COMB (@lem7643762) (@lem7643763)). Qed.
Lemma lem7643766 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7643767 : term151 = term54.
Proof. exact (@lem7643766 term12). Qed.
Lemma lem7643768 : term150 = term54.
Proof. exact (TRANS (@lem7643764) (@lem7643767)). Qed.
Lemma lem7643770 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7643771 : term94 = term95.
Proof. exact (@lem7643770 term12 term12). Qed.
Lemma lem7643772 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7643773 : term97 = term12.
Proof. exact (EQ_MP (@lem7643772) (@lem940073)). Qed.
Lemma lem7643774 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7643775 : term95 = term61.
Proof. exact (MK_COMB (@lem7643774) (@lem7643773)). Qed.
Lemma lem7643776 : term94 = term61.
Proof. exact (TRANS (@lem7643771) (@lem7643775)). Qed.
Lemma lem7643777 : term149 = term149.
Proof. exact (eq_refl term149). Qed.
Lemma lem7643778 : term153 = term151.
Proof. exact (MK_COMB (@lem7643777) (@lem7643776)). Qed.
Lemma lem7643780 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7643781 : term151 = term54.
Proof. exact (@lem7643780 term12). Qed.
Lemma lem7643782 : term153 = term54.
Proof. exact (TRANS (@lem7643778) (@lem7643781)). Qed.
Lemma lem7643783 : term54 = term153.
Proof. exact (SYM (@lem7643782)). Qed.
Lemma lem7643784 : term150 = term153.
Proof. exact (TRANS (@lem7643768) (@lem7643783)). Qed.
Lemma lem7643785 : term136 = term82.
Proof. exact (@lem7643735 (@lem7643784)). Qed.
Lemma lem7643786 : term135 = term82.
Proof. exact (TRANS (@lem7643701) (@lem7643785)). Qed.
Lemma lem7643788 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7643789 : term82 = term54.
Proof. exact (@lem7643788 term54). Qed.
Lemma lem7643790 : term135 = term54.
Proof. exact (TRANS (@lem7643786) (@lem7643789)). Qed.
Lemma lem7643791 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7643792 : term154 = term149.
Proof. exact (MK_COMB (@lem7643791) (@lem7643790)). Qed.
Lemma lem7643793 (_98504 : int) : (real_of_int _98504) = (real_of_int _98504).
Proof. exact (eq_refl (real_of_int _98504)). Qed.
Lemma lem7643794 (_98504 : int) : (term132 _98504) = (term155 _98504).
Proof. exact (MK_COMB (@lem7643792) (@lem7643793 _98504)). Qed.
Lemma lem7643795 (_98504 : int) : (term131 _98504) = (term155 _98504).
Proof. exact (TRANS (@lem7643692 _98504) (@lem7643794 _98504)). Qed.
Lemma lem7643796 (_98504 : int) : (term155 _98504) = term54.
Proof. exact (@lem1982719 (real_of_int _98504)). Qed.
Lemma lem7643797 (_98504 : int) : (term131 _98504) = term54.
Proof. exact (TRANS (@lem7643795 _98504) (@lem7643796 _98504)). Qed.
Lemma lem7643798 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7643799 (_98504 : int) : (term156 _98504) = term157.
Proof. exact (MK_COMB (@lem7643798) (@lem7643797 _98504)). Qed.
Lemma lem7643800 (_98505 : int) : (term130 _98505) = (term130 _98505).
Proof. exact (eq_refl (term130 _98505)). Qed.
Lemma lem7643801 (_98504 : int) (_98505 : int) : (term129 _98504 _98505) = (term158 _98505).
Proof. exact (MK_COMB (@lem7643799 _98504) (@lem7643800 _98505)). Qed.
Lemma lem7643802 (_98504 : int) (_98505 : int) : (term128 _98504 _98505) = (term158 _98505).
Proof. exact (TRANS (@lem7643691 _98504 _98505) (@lem7643801 _98504 _98505)). Qed.
Lemma lem7643803 (_98505 : int) : (term158 _98505) = (term130 _98505).
Proof. exact (@lem1982721 (term130 _98505)). Qed.
Lemma lem7643804 (_98504 : int) (_98505 : int) : (term128 _98504 _98505) = (term130 _98505).
Proof. exact (TRANS (@lem7643802 _98504 _98505) (@lem7643803 _98505)). Qed.
Lemma lem7643805 (_98504 : int) (_98505 : int) : (term125 _98504 _98505) = (term130 _98505).
Proof. exact (TRANS (@lem7643690 _98504 _98505) (@lem7643804 _98504 _98505)). Qed.
Lemma lem7643807 (_98504 : int) (_98505 : int) : (term124 _98504 _98505) = (term130 _98505).
Proof. exact (TRANS (@lem7643681 _98504 _98505) (@lem7643805 _98504 _98505)). Qed.
Lemma lem7643808 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7643809 (_98504 : int) (_98505 : int) : (term159 _98504 _98505) = (term160 _98505).
Proof. exact (MK_COMB (@lem7643808) (@lem7643807 _98504 _98505)). Qed.
Lemma lem7643810 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7643811 (_98504 : int) (_98505 : int) : (term123 _98504 _98505) = (term161 _98505).
Proof. exact (MK_COMB (@lem7643809 _98504 _98505) (@lem7643810)). Qed.
Lemma lem7643812 (_98504 : int) (_98505 : int) : (term70 _98505 _98504) = (term161 _98505).
Proof. exact (TRANS (@lem7643669 _98504 _98505) (@lem7643811 _98504 _98505)). Qed.
Lemma lem7643813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7643814 (_98505 : int) : (term71 _98505) = (term162 _98505).
Proof. exact (MK_COMB (@lem7643813) (@lem7643668 _98505)). Qed.
Lemma lem7643815 (_98504 : int) (_98505 : int) : (term72 _98505 _98504) = (term163 _98505).
Proof. exact (MK_COMB (@lem7643814 _98505) (@lem7643812 _98504 _98505)). Qed.
Lemma lem7643816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7643817 (_98505 : int) : (term73 _98505) = (term164 _98505).
Proof. exact (MK_COMB (@lem7643816) (@lem7643613 _98505)). Qed.
Lemma lem7643818 (_98504 : int) (_98505 : int) : (term74 _98505 _98504) = (term165 _98505).
Proof. exact (MK_COMB (@lem7643817 _98505) (@lem7643815 _98504 _98505)). Qed.
Lemma lem7643819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7643820 (_98504 : int) : (term73 _98504) = (term164 _98504).
Proof. exact (MK_COMB (@lem7643819) (@lem7643565 _98504)). Qed.
Lemma lem7643821 (_98504 : int) (_98505 : int) : (term75 _98505 _98504) = (term166 _98504 _98505).
Proof. exact (MK_COMB (@lem7643820 _98504) (@lem7643818 _98504 _98505)). Qed.
Lemma lem7643848 (_98504 : int) (_98505 : int) : (term77 _98505 _98504) = (term166 _98504 _98505).
Proof. exact (TRANS (@lem7643517 _98505 _98504) (@lem7643821 _98504 _98505)). Qed.
Lemma lem7643852 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term166 _98504 _98505.
Proof. exact (h1). Qed.
Lemma lem7643853 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term165 _98505.
Proof. exact (proj2 (@lem7643852 _98504 _98505 h1)). Qed.
Lemma lem7643855 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term163 _98505.
Proof. exact (proj2 (@lem7643853 _98504 _98505 h1)). Qed.
Lemma lem7643857 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term161 _98505.
Proof. exact (proj2 (@lem7643855 _98504 _98505 h1)). Qed.
Lemma lem7643858 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term122 _98505.
Proof. exact (proj1 (@lem7643855 _98504 _98505 h1)). Qed.
Lemma lem7643860 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7643861 : term167 = term139.
Proof. exact (@lem7643860 term54 term61). Qed.
Lemma lem7643863 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7643864 : term61 = term110.
Proof. exact (@lem7643863 term12). Qed.
Lemma lem7643866 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7643867 : term54 = term82.
Proof. exact (@lem7643866 (NUMERAL 0)). Qed.
Lemma lem7643868 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7643869 : term168 = term169.
Proof. exact (MK_COMB (@lem7643868) (@lem7643867)). Qed.
Lemma lem7643870 : term139 = term170.
Proof. exact (MK_COMB (@lem7643869) (@lem7643864)). Qed.
Lemma lem7643871 : term171.
Proof. exact (@lem1980255 term54 term61 term61 term61). Qed.
Lemma lem7643873 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7643874 : term139 = term140.
Proof. exact (@lem7643873 (NUMERAL 0) term12). Qed.
Lemma lem7643875 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7643876 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7643877 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7643876 h1) (fun h1 : term140 = True => @lem7643875)). Qed.
Lemma lem7643878 : term140 = True.
Proof. exact (EQ_MP (@lem7643877) (@lem7643875)). Qed.
Lemma lem7643879 : term139 = True.
Proof. exact (TRANS (@lem7643874) (@lem7643878)). Qed.
Lemma lem7643880 : True = term139.
Proof. exact (SYM (@lem7643879)). Qed.
Lemma lem7643881 : term139.
Proof. exact (EQ_MP (@lem7643880) (@lem0)). Qed.
Lemma lem7643882 : term172.
Proof. exact (@lem7643871 (@lem7643881)). Qed.
Lemma lem7643884 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7643885 : term139 = term140.
Proof. exact (@lem7643884 (NUMERAL 0) term12). Qed.
Lemma lem7643886 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7643887 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7643888 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7643887 h1) (fun h1 : term140 = True => @lem7643886)). Qed.
Lemma lem7643889 : term140 = True.
Proof. exact (EQ_MP (@lem7643888) (@lem7643886)). Qed.
Lemma lem7643890 : term139 = True.
Proof. exact (TRANS (@lem7643885) (@lem7643889)). Qed.
Lemma lem7643891 : True = term139.
Proof. exact (SYM (@lem7643890)). Qed.
Lemma lem7643892 : term139.
Proof. exact (EQ_MP (@lem7643891) (@lem0)). Qed.
Lemma lem7643893 : term170 = term173.
Proof. exact (@lem7643882 (@lem7643892)). Qed.
Lemma lem7643895 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7643896 : term94 = term95.
Proof. exact (@lem7643895 term12 term12). Qed.
Lemma lem7643897 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7643898 : term97 = term12.
Proof. exact (EQ_MP (@lem7643897) (@lem940073)). Qed.
Lemma lem7643899 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7643900 : term95 = term61.
Proof. exact (MK_COMB (@lem7643899) (@lem7643898)). Qed.
Lemma lem7643901 : term94 = term61.
Proof. exact (TRANS (@lem7643896) (@lem7643900)). Qed.
Lemma lem7643903 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7643904 : term151 = term54.
Proof. exact (@lem7643903 term12). Qed.
Lemma lem7643905 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7643906 : term174 = term168.
Proof. exact (MK_COMB (@lem7643905) (@lem7643904)). Qed.
Lemma lem7643907 : term173 = term139.
Proof. exact (MK_COMB (@lem7643906) (@lem7643901)). Qed.
Lemma lem7643909 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7643910 : term139 = term140.
Proof. exact (@lem7643909 (NUMERAL 0) term12). Qed.
Lemma lem7643911 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7643912 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7643913 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7643912 h1) (fun h1 : term140 = True => @lem7643911)). Qed.
Lemma lem7643914 : term140 = True.
Proof. exact (EQ_MP (@lem7643913) (@lem7643911)). Qed.
Lemma lem7643915 : term139 = True.
Proof. exact (TRANS (@lem7643910) (@lem7643914)). Qed.
Lemma lem7643916 : term173 = True.
Proof. exact (TRANS (@lem7643907) (@lem7643915)). Qed.
Lemma lem7643917 : term170 = True.
Proof. exact (TRANS (@lem7643893) (@lem7643916)). Qed.
Lemma lem7643918 : term139 = True.
Proof. exact (TRANS (@lem7643870) (@lem7643917)). Qed.
Lemma lem7643919 : term167 = True.
Proof. exact (TRANS (@lem7643861) (@lem7643918)). Qed.
Lemma lem7643920 : True = term167.
Proof. exact (SYM (@lem7643919)). Qed.
Lemma lem7643921 : term167.
Proof. exact (EQ_MP (@lem7643920) (@lem0)). Qed.
Lemma lem7643922 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term175 _98505.
Proof. exact (conj (@lem7643921) (@lem7643858 _98504 _98505 h1)). Qed.
Lemma lem7643924 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7643925 (_98505 : int) : term177 _98505.
Proof. exact (@lem7643924 term61 (term119 _98505)). Qed.
Lemma lem7643926 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term178 _98505.
Proof. exact (@lem7643925 _98505 (@lem7643922 _98504 _98505 h1)). Qed.
Lemma lem7643927 (_98505 : int) : (term179 _98505) = (term119 _98505).
Proof. exact (@lem1982733 (term119 _98505)). Qed.
Lemma lem7643928 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7643929 (_98505 : int) : (term180 _98505) = (term121 _98505).
Proof. exact (MK_COMB (@lem7643928) (@lem7643927 _98505)). Qed.
Lemma lem7643930 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7643931 (_98505 : int) : (term178 _98505) = (term122 _98505).
Proof. exact (MK_COMB (@lem7643929 _98505) (@lem7643930)). Qed.
Lemma lem7643932 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term122 _98505.
Proof. exact (EQ_MP (@lem7643931 _98505) (@lem7643926 _98504 _98505 h1)). Qed.
Lemma lem7643934 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7643935 : term167 = term139.
Proof. exact (@lem7643934 term54 term61). Qed.
Lemma lem7643937 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7643938 : term61 = term110.
Proof. exact (@lem7643937 term12). Qed.
Lemma lem7643940 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7643941 : term54 = term82.
Proof. exact (@lem7643940 (NUMERAL 0)). Qed.
Lemma lem7643942 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7643943 : term168 = term169.
Proof. exact (MK_COMB (@lem7643942) (@lem7643941)). Qed.
Lemma lem7643944 : term139 = term170.
Proof. exact (MK_COMB (@lem7643943) (@lem7643938)). Qed.
Lemma lem7643945 : term171.
Proof. exact (@lem1980255 term54 term61 term61 term61). Qed.
Lemma lem7643947 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7643948 : term139 = term140.
Proof. exact (@lem7643947 (NUMERAL 0) term12). Qed.
Lemma lem7643949 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7643950 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7643951 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7643950 h1) (fun h1 : term140 = True => @lem7643949)). Qed.
Lemma lem7643952 : term140 = True.
Proof. exact (EQ_MP (@lem7643951) (@lem7643949)). Qed.
Lemma lem7643953 : term139 = True.
Proof. exact (TRANS (@lem7643948) (@lem7643952)). Qed.
Lemma lem7643954 : True = term139.
Proof. exact (SYM (@lem7643953)). Qed.
Lemma lem7643955 : term139.
Proof. exact (EQ_MP (@lem7643954) (@lem0)). Qed.
Lemma lem7643956 : term172.
Proof. exact (@lem7643945 (@lem7643955)). Qed.
Lemma lem7643958 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7643959 : term139 = term140.
Proof. exact (@lem7643958 (NUMERAL 0) term12). Qed.
Lemma lem7643960 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7643961 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7643962 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7643961 h1) (fun h1 : term140 = True => @lem7643960)). Qed.
Lemma lem7643963 : term140 = True.
Proof. exact (EQ_MP (@lem7643962) (@lem7643960)). Qed.
Lemma lem7643964 : term139 = True.
Proof. exact (TRANS (@lem7643959) (@lem7643963)). Qed.
Lemma lem7643965 : True = term139.
Proof. exact (SYM (@lem7643964)). Qed.
Lemma lem7643966 : term139.
Proof. exact (EQ_MP (@lem7643965) (@lem0)). Qed.
Lemma lem7643967 : term170 = term173.
Proof. exact (@lem7643956 (@lem7643966)). Qed.
Lemma lem7643969 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7643970 : term94 = term95.
Proof. exact (@lem7643969 term12 term12). Qed.
Lemma lem7643971 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7643972 : term97 = term12.
Proof. exact (EQ_MP (@lem7643971) (@lem940073)). Qed.
Lemma lem7643973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7643974 : term95 = term61.
Proof. exact (MK_COMB (@lem7643973) (@lem7643972)). Qed.
Lemma lem7643975 : term94 = term61.
Proof. exact (TRANS (@lem7643970) (@lem7643974)). Qed.
Lemma lem7643977 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7643978 : term151 = term54.
Proof. exact (@lem7643977 term12). Qed.
Lemma lem7643979 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7643980 : term174 = term168.
Proof. exact (MK_COMB (@lem7643979) (@lem7643978)). Qed.
Lemma lem7643981 : term173 = term139.
Proof. exact (MK_COMB (@lem7643980) (@lem7643975)). Qed.
Lemma lem7643983 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7643984 : term139 = term140.
Proof. exact (@lem7643983 (NUMERAL 0) term12). Qed.
Lemma lem7643985 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7643986 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7643987 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7643986 h1) (fun h1 : term140 = True => @lem7643985)). Qed.
Lemma lem7643988 : term140 = True.
Proof. exact (EQ_MP (@lem7643987) (@lem7643985)). Qed.
Lemma lem7643989 : term139 = True.
Proof. exact (TRANS (@lem7643984) (@lem7643988)). Qed.
Lemma lem7643990 : term173 = True.
Proof. exact (TRANS (@lem7643981) (@lem7643989)). Qed.
Lemma lem7643991 : term170 = True.
Proof. exact (TRANS (@lem7643967) (@lem7643990)). Qed.
Lemma lem7643992 : term139 = True.
Proof. exact (TRANS (@lem7643944) (@lem7643991)). Qed.
Lemma lem7643993 : term167 = True.
Proof. exact (TRANS (@lem7643935) (@lem7643992)). Qed.
Lemma lem7643994 : True = term167.
Proof. exact (SYM (@lem7643993)). Qed.
Lemma lem7643995 : term167.
Proof. exact (EQ_MP (@lem7643994) (@lem0)). Qed.
Lemma lem7643996 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term181 _98505.
Proof. exact (conj (@lem7643995) (@lem7643857 _98504 _98505 h1)). Qed.
Lemma lem7643998 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7643999 (_98505 : int) : term182 _98505.
Proof. exact (@lem7643998 term61 (term130 _98505)). Qed.
Lemma lem7644000 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term183 _98505.
Proof. exact (@lem7643999 _98505 (@lem7643996 _98504 _98505 h1)). Qed.
Lemma lem7644001 (_98505 : int) : (term184 _98505) = (term130 _98505).
Proof. exact (@lem1982733 (term130 _98505)). Qed.
Lemma lem7644002 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7644003 (_98505 : int) : (term185 _98505) = (term160 _98505).
Proof. exact (MK_COMB (@lem7644002) (@lem7644001 _98505)). Qed.
Lemma lem7644004 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7644005 (_98505 : int) : (term183 _98505) = (term161 _98505).
Proof. exact (MK_COMB (@lem7644003 _98505) (@lem7644004)). Qed.
Lemma lem7644006 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term161 _98505.
Proof. exact (EQ_MP (@lem7644005 _98505) (@lem7644000 _98504 _98505 h1)). Qed.
Lemma lem7644007 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term186 _98505.
Proof. exact (conj (@lem7644006 _98504 _98505 h1) (@lem7643932 _98504 _98505 h1)). Qed.
Lemma lem7644009 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7644010 (_98505 : int) : term188 _98505.
Proof. exact (@lem7644009 (term130 _98505) (term119 _98505)). Qed.
Lemma lem7644011 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term189 _98505.
Proof. exact (@lem7644010 _98505 (@lem7644007 _98504 _98505 h1)). Qed.
Lemma lem7644012 (_98505 : int) : (term190 _98505) = (term191 _98505).
Proof. exact (@lem1982763 (term130 _98505) (real_of_int _98505) term85). Qed.
Lemma lem7644013 (_98505 : int) : (term192 _98505) = (term132 _98505).
Proof. exact (@lem1982713 term85 (real_of_int _98505)). Qed.
Lemma lem7644015 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7644016 : term61 = term110.
Proof. exact (@lem7644015 term12). Qed.
Lemma lem7644018 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7644019 : term85 = term86.
Proof. exact (@lem7644018 term12). Qed.
Lemma lem7644020 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7644021 : term133 = term134.
Proof. exact (MK_COMB (@lem7644020) (@lem7644019)). Qed.
Lemma lem7644022 : term135 = term136.
Proof. exact (MK_COMB (@lem7644021) (@lem7644016)). Qed.
Lemma lem7644023 : term137.
Proof. exact (@lem1981473 term85 term61 term61 term61 term54 term61). Qed.
Lemma lem7644025 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7644026 : term139 = term140.
Proof. exact (@lem7644025 (NUMERAL 0) term12). Qed.
Lemma lem7644027 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7644028 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7644029 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7644028 h1) (fun h1 : term140 = True => @lem7644027)). Qed.
Lemma lem7644030 : term140 = True.
Proof. exact (EQ_MP (@lem7644029) (@lem7644027)). Qed.
Lemma lem7644031 : term139 = True.
Proof. exact (TRANS (@lem7644026) (@lem7644030)). Qed.
Lemma lem7644032 : True = term139.
Proof. exact (SYM (@lem7644031)). Qed.
Lemma lem7644033 : term139.
Proof. exact (EQ_MP (@lem7644032) (@lem0)). Qed.
Lemma lem7644034 : term142.
Proof. exact (@lem7644023 (@lem7644033)). Qed.
Lemma lem7644036 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7644037 : term139 = term140.
Proof. exact (@lem7644036 (NUMERAL 0) term12). Qed.
Lemma lem7644038 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7644039 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7644040 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7644039 h1) (fun h1 : term140 = True => @lem7644038)). Qed.
Lemma lem7644041 : term140 = True.
Proof. exact (EQ_MP (@lem7644040) (@lem7644038)). Qed.
Lemma lem7644042 : term139 = True.
Proof. exact (TRANS (@lem7644037) (@lem7644041)). Qed.
Lemma lem7644043 : True = term139.
Proof. exact (SYM (@lem7644042)). Qed.
Lemma lem7644044 : term139.
Proof. exact (EQ_MP (@lem7644043) (@lem0)). Qed.
Lemma lem7644045 : term143.
Proof. exact (@lem7644034 (@lem7644044)). Qed.
Lemma lem7644047 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7644048 : term139 = term140.
Proof. exact (@lem7644047 (NUMERAL 0) term12). Qed.
Lemma lem7644049 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7644050 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7644051 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7644050 h1) (fun h1 : term140 = True => @lem7644049)). Qed.
Lemma lem7644052 : term140 = True.
Proof. exact (EQ_MP (@lem7644051) (@lem7644049)). Qed.
Lemma lem7644053 : term139 = True.
Proof. exact (TRANS (@lem7644048) (@lem7644052)). Qed.
Lemma lem7644054 : True = term139.
Proof. exact (SYM (@lem7644053)). Qed.
Lemma lem7644055 : term139.
Proof. exact (EQ_MP (@lem7644054) (@lem0)). Qed.
Lemma lem7644056 : term144.
Proof. exact (@lem7644045 (@lem7644055)). Qed.
Lemma lem7644058 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7644059 : term94 = term95.
Proof. exact (@lem7644058 term12 term12). Qed.
Lemma lem7644060 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7644061 : term97 = term12.
Proof. exact (EQ_MP (@lem7644060) (@lem940073)). Qed.
Lemma lem7644062 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7644063 : term95 = term61.
Proof. exact (MK_COMB (@lem7644062) (@lem7644061)). Qed.
Lemma lem7644064 : term94 = term61.
Proof. exact (TRANS (@lem7644059) (@lem7644063)). Qed.
Lemma lem7644066 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7644067 : term111 = term116.
Proof. exact (@lem7644066 term12 term12). Qed.
Lemma lem7644068 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7644069 : term97 = term12.
Proof. exact (EQ_MP (@lem7644068) (@lem940073)). Qed.
Lemma lem7644070 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7644071 : term95 = term61.
Proof. exact (MK_COMB (@lem7644070) (@lem7644069)). Qed.
Lemma lem7644072 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7644073 : term116 = term85.
Proof. exact (MK_COMB (@lem7644072) (@lem7644071)). Qed.
Lemma lem7644074 : term111 = term85.
Proof. exact (TRANS (@lem7644067) (@lem7644073)). Qed.
Lemma lem7644075 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7644076 : term145 = term133.
Proof. exact (MK_COMB (@lem7644075) (@lem7644074)). Qed.
Lemma lem7644077 : term146 = term135.
Proof. exact (MK_COMB (@lem7644076) (@lem7644064)). Qed.
Lemma lem7644079 (m : nat) : (term147 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7644080 : term135 = term54.
Proof. exact (@lem7644079 term12). Qed.
Lemma lem7644081 : term146 = term54.
Proof. exact (TRANS (@lem7644077) (@lem7644080)). Qed.
Lemma lem7644082 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7644083 : term148 = term149.
Proof. exact (MK_COMB (@lem7644082) (@lem7644081)). Qed.
Lemma lem7644084 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem7644085 : term150 = term151.
Proof. exact (MK_COMB (@lem7644083) (@lem7644084)). Qed.
Lemma lem7644087 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7644088 : term151 = term54.
Proof. exact (@lem7644087 term12). Qed.
Lemma lem7644089 : term150 = term54.
Proof. exact (TRANS (@lem7644085) (@lem7644088)). Qed.
Lemma lem7644091 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7644092 : term94 = term95.
Proof. exact (@lem7644091 term12 term12). Qed.
Lemma lem7644093 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7644094 : term97 = term12.
Proof. exact (EQ_MP (@lem7644093) (@lem940073)). Qed.
Lemma lem7644095 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7644096 : term95 = term61.
Proof. exact (MK_COMB (@lem7644095) (@lem7644094)). Qed.
Lemma lem7644097 : term94 = term61.
Proof. exact (TRANS (@lem7644092) (@lem7644096)). Qed.
Lemma lem7644098 : term149 = term149.
Proof. exact (eq_refl term149). Qed.
Lemma lem7644099 : term153 = term151.
Proof. exact (MK_COMB (@lem7644098) (@lem7644097)). Qed.
Lemma lem7644101 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7644102 : term151 = term54.
Proof. exact (@lem7644101 term12). Qed.
Lemma lem7644103 : term153 = term54.
Proof. exact (TRANS (@lem7644099) (@lem7644102)). Qed.
Lemma lem7644104 : term54 = term153.
Proof. exact (SYM (@lem7644103)). Qed.
Lemma lem7644105 : term150 = term153.
Proof. exact (TRANS (@lem7644089) (@lem7644104)). Qed.
Lemma lem7644106 : term136 = term82.
Proof. exact (@lem7644056 (@lem7644105)). Qed.
Lemma lem7644107 : term135 = term82.
Proof. exact (TRANS (@lem7644022) (@lem7644106)). Qed.
Lemma lem7644109 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7644110 : term82 = term54.
Proof. exact (@lem7644109 term54). Qed.
Lemma lem7644111 : term135 = term54.
Proof. exact (TRANS (@lem7644107) (@lem7644110)). Qed.
Lemma lem7644112 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7644113 : term154 = term149.
Proof. exact (MK_COMB (@lem7644112) (@lem7644111)). Qed.
Lemma lem7644114 (_98505 : int) : (real_of_int _98505) = (real_of_int _98505).
Proof. exact (eq_refl (real_of_int _98505)). Qed.
Lemma lem7644115 (_98505 : int) : (term132 _98505) = (term155 _98505).
Proof. exact (MK_COMB (@lem7644113) (@lem7644114 _98505)). Qed.
Lemma lem7644116 (_98505 : int) : (term192 _98505) = (term155 _98505).
Proof. exact (TRANS (@lem7644013 _98505) (@lem7644115 _98505)). Qed.
Lemma lem7644117 (_98505 : int) : (term155 _98505) = term54.
Proof. exact (@lem1982719 (real_of_int _98505)). Qed.
Lemma lem7644118 (_98505 : int) : (term192 _98505) = term54.
Proof. exact (TRANS (@lem7644116 _98505) (@lem7644117 _98505)). Qed.
Lemma lem7644119 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7644120 (_98505 : int) : (term193 _98505) = term157.
Proof. exact (MK_COMB (@lem7644119) (@lem7644118 _98505)). Qed.
Lemma lem7644121 : term85 = term85.
Proof. exact (eq_refl term85). Qed.
Lemma lem7644122 (_98505 : int) : (term191 _98505) = term194.
Proof. exact (MK_COMB (@lem7644120 _98505) (@lem7644121)). Qed.
Lemma lem7644123 (_98505 : int) : (term190 _98505) = term194.
Proof. exact (TRANS (@lem7644012 _98505) (@lem7644122 _98505)). Qed.
Lemma lem7644124 : term194 = term85.
Proof. exact (@lem1982721 term85). Qed.
Lemma lem7644125 (_98505 : int) : (term190 _98505) = term85.
Proof. exact (TRANS (@lem7644123 _98505) (@lem7644124)). Qed.
Lemma lem7644126 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7644127 (_98505 : int) : (term195 _98505) = term196.
Proof. exact (MK_COMB (@lem7644126) (@lem7644125 _98505)). Qed.
Lemma lem7644128 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7644129 (_98505 : int) : (term189 _98505) = term197.
Proof. exact (MK_COMB (@lem7644127 _98505) (@lem7644128)). Qed.
Lemma lem7644130 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term197.
Proof. exact (EQ_MP (@lem7644129 _98505) (@lem7644011 _98504 _98505 h1)). Qed.
Lemma lem7644132 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7644133 : term197 = term198.
Proof. exact (@lem7644132 term54 term85). Qed.
Lemma lem7644135 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7644136 : term85 = term86.
Proof. exact (@lem7644135 term12). Qed.
Lemma lem7644138 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7644139 : term54 = term82.
Proof. exact (@lem7644138 (NUMERAL 0)). Qed.
Lemma lem7644140 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7644141 : term56 = term199.
Proof. exact (MK_COMB (@lem7644140) (@lem7644139)). Qed.
Lemma lem7644142 : term198 = term200.
Proof. exact (MK_COMB (@lem7644141) (@lem7644136)). Qed.
Lemma lem7644143 : term201.
Proof. exact (@lem1980026 term54 term61 term85 term61). Qed.
Lemma lem7644145 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7644146 : term139 = term140.
Proof. exact (@lem7644145 (NUMERAL 0) term12). Qed.
Lemma lem7644147 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7644148 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7644149 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7644148 h1) (fun h1 : term140 = True => @lem7644147)). Qed.
Lemma lem7644150 : term140 = True.
Proof. exact (EQ_MP (@lem7644149) (@lem7644147)). Qed.
Lemma lem7644151 : term139 = True.
Proof. exact (TRANS (@lem7644146) (@lem7644150)). Qed.
Lemma lem7644152 : True = term139.
Proof. exact (SYM (@lem7644151)). Qed.
Lemma lem7644153 : term139.
Proof. exact (EQ_MP (@lem7644152) (@lem0)). Qed.
Lemma lem7644154 : term202.
Proof. exact (@lem7644143 (@lem7644153)). Qed.
Lemma lem7644156 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7644157 : term139 = term140.
Proof. exact (@lem7644156 (NUMERAL 0) term12). Qed.
Lemma lem7644158 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7644159 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7644160 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7644159 h1) (fun h1 : term140 = True => @lem7644158)). Qed.
Lemma lem7644161 : term140 = True.
Proof. exact (EQ_MP (@lem7644160) (@lem7644158)). Qed.
Lemma lem7644162 : term139 = True.
Proof. exact (TRANS (@lem7644157) (@lem7644161)). Qed.
Lemma lem7644163 : True = term139.
Proof. exact (SYM (@lem7644162)). Qed.
Lemma lem7644164 : term139.
Proof. exact (EQ_MP (@lem7644163) (@lem0)). Qed.
Lemma lem7644165 : term200 = term203.
Proof. exact (@lem7644154 (@lem7644164)). Qed.
Lemma lem7644167 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7644168 : term111 = term116.
Proof. exact (@lem7644167 term12 term12). Qed.
Lemma lem7644169 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7644170 : term97 = term12.
Proof. exact (EQ_MP (@lem7644169) (@lem940073)). Qed.
Lemma lem7644171 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7644172 : term95 = term61.
Proof. exact (MK_COMB (@lem7644171) (@lem7644170)). Qed.
Lemma lem7644173 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7644174 : term116 = term85.
Proof. exact (MK_COMB (@lem7644173) (@lem7644172)). Qed.
Lemma lem7644175 : term111 = term85.
Proof. exact (TRANS (@lem7644168) (@lem7644174)). Qed.
Lemma lem7644177 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7644178 : term151 = term54.
Proof. exact (@lem7644177 term12). Qed.
Lemma lem7644179 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7644180 : term204 = term56.
Proof. exact (MK_COMB (@lem7644179) (@lem7644178)). Qed.
Lemma lem7644181 : term203 = term198.
Proof. exact (MK_COMB (@lem7644180) (@lem7644175)). Qed.
Lemma lem7644183 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7644184 : term198 = term207.
Proof. exact (@lem7644183 (NUMERAL 0) term12). Qed.
Lemma lem7644185 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7644186 (h1 : term141 = (BIT1 0)) : (term12 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7644187 : (term141 = (BIT1 0)) = ((term12 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7644186 h1) (fun h1 : (term12 = (NUMERAL 0)) = False => @lem7644185)). Qed.
Lemma lem7644188 : (term12 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7644187) (@lem7644185)). Qed.
Lemma lem7644189 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7644190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7644191 : term208 = (and True).
Proof. exact (MK_COMB (@lem7644190) (@lem7644189)). Qed.
Lemma lem7644192 : term207 = (True /\ False).
Proof. exact (MK_COMB (@lem7644191) (@lem7644188)). Qed.
Lemma lem7644194 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7644195 : term207 = False.
Proof. exact (TRANS (@lem7644192) (@lem7644194)). Qed.
Lemma lem7644196 : term198 = False.
Proof. exact (TRANS (@lem7644184) (@lem7644195)). Qed.
Lemma lem7644197 : term203 = False.
Proof. exact (TRANS (@lem7644181) (@lem7644196)). Qed.
Lemma lem7644198 : term200 = False.
Proof. exact (TRANS (@lem7644165) (@lem7644197)). Qed.
Lemma lem7644199 : term198 = False.
Proof. exact (TRANS (@lem7644142) (@lem7644198)). Qed.
Lemma lem7644200 : term197 = False.
Proof. exact (TRANS (@lem7644133) (@lem7644199)). Qed.
Lemma lem7644201 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : False.
Proof. exact (EQ_MP (@lem7644200) (@lem7644130 _98504 _98505 h1)). Qed.
Lemma lem7644203 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : term166 _98504 _98505.
Proof. exact (h1). Qed.
Lemma lem7644204 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : (term166 _98504 _98505) = False.
Proof. exact (prop_ext (fun h2 : term166 _98504 _98505 => @lem7644201 _98504 _98505 h1) (fun h2 : False => @lem7644203 _98504 _98505 h1)). Qed.
Lemma lem7644205 (_98504 : int) (_98505 : int) (h1 : term166 _98504 _98505) : False.
Proof. exact (EQ_MP (@lem7644204 _98504 _98505 h1) (@lem7644203 _98504 _98505 h1)). Qed.
Lemma lem7644206 (_98505 : int) (_98504 : int) (h1 : term77 _98505 _98504) : term77 _98505 _98504.
Proof. exact (h1). Qed.
Lemma lem7644207 (_98505 : int) (_98504 : int) (h1 : term77 _98505 _98504) : term166 _98504 _98505.
Proof. exact (EQ_MP (@lem7643848 _98504 _98505) (@lem7644206 _98505 _98504 h1)). Qed.
Lemma lem7644208 (_98505 : int) (_98504 : int) (h1 : term77 _98505 _98504) : (term166 _98504 _98505) = False.
Proof. exact (prop_ext (fun h2 : term166 _98504 _98505 => @lem7644205 _98504 _98505 h2) (fun h2 : False => @lem7644207 _98505 _98504 h1)). Qed.
Lemma lem7644209 (_98505 : int) (_98504 : int) (h1 : term77 _98505 _98504) : False.
Proof. exact (EQ_MP (@lem7644208 _98505 _98504 h1) (@lem7644207 _98505 _98504 h1)). Qed.
Lemma lem7644210 (_98505 : int) (_98504 : int) : term209 _98505 _98504.
Proof. exact (fun h0 : term77 _98505 _98504 => @lem7644209 _98505 _98504 h0). Qed.
Lemma lem7644211 (_98505 : int) (_98504 : int) : term210 _98505 _98504.
Proof. exact (@lem1386578 (term211 _98505 _98504)). Qed.
Lemma lem7644214 (_98505 : int) (_98504 : int) : term211 _98505 _98504.
Proof. exact (@lem7644211 _98505 _98504 (@lem7644210 _98505 _98504)). Qed.
Lemma lem7644215 (_98505 : int) (_98504 : int) : (term75 _98505 _98504) = (term47 _98505 _98504).
Proof. exact (SYM (@lem7643477 _98505 _98504)). Qed.
Lemma lem7644216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7644217 (_98505 : int) (_98504 : int) : (term211 _98505 _98504) = (term26 _98505 _98504).
Proof. exact (MK_COMB (@lem7644216) (@lem7644215 _98505 _98504)). Qed.
Lemma lem7644218 (_98505 : int) (_98504 : int) : term26 _98505 _98504.
Proof. exact (EQ_MP (@lem7644217 _98505 _98504) (@lem7644214 _98505 _98504)). Qed.
Lemma lem7644219 (_98505 : int) (_98504 : int) : term27 _98505 _98504.
Proof. exact (EQ_MP (@lem7643366 _98505 _98504) (@lem7644218 _98505 _98504)). Qed.
Lemma lem7644220 (i : nat) (a : nat) : term212 i a.
Proof. exact (@lem7644219 (int_of_num i) (int_of_num a)). Qed.
Lemma lem7644221 (i : nat) (a : nat) : term213 i a.
Proof. exact (@lem7644220 i a (@lem7643362 a)). Qed.
Lemma lem7644222 (i : nat) (a : nat) : term23 i a.
Proof. exact (@lem7644221 i a (@lem7643365 i)). Qed.
Lemma lem7644223 (i : nat) (a : nat) : (term23 i a) = (term0 i a).
Proof. exact (SYM (@lem7643359 i a)). Qed.
Lemma lem7644224 (i : nat) (a : nat) : term0 i a.
Proof. exact (EQ_MP (@lem7644223 i a) (@lem7644222 i a)). Qed.
Lemma lem7644252 (i : nat) (b : nat) : (term214 i b) = (term215 i b).
Proof. exact (@lem17045 (term2 i) (Peano.le i b)). Qed.
Lemma lem7644257 (i : nat) (a : nat) (b : nat) : (term216 i a b) = (term216 i a b).
Proof. exact (eq_refl (term216 i a b)). Qed.
Lemma lem7644258 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7644259 (i : nat) (b : nat) : (term217 i b) = (term218 i b).
Proof. exact (MK_COMB (@lem7644258) (@lem7644252 i b)). Qed.
Lemma lem7644260 (i : nat) (a : nat) (b : nat) : (term219 i a b) = (term220 i a b).
Proof. exact (MK_COMB (@lem7644259 i b) (@lem7644257 i a b)). Qed.
Lemma lem7644261 (i : nat) (a : nat) (b : nat) : (term221 i a b) = (term219 i a b).
Proof. exact (@lem17265 (term222 i b) (term216 i a b)). Qed.
Lemma lem7644277 (i : nat) (a : nat) (b : nat) : (term221 i a b) = (term220 i a b).
Proof. exact (TRANS (@lem7644261 i a b) (@lem7644260 i a b)). Qed.
Lemma lem7644284 (a : nat) (b : nat) : (Nat.add a b) = (Nat.add a b).
Proof. exact (eq_refl (Nat.add a b)). Qed.
Lemma lem7644291 (a : nat) (i : nat) : (Nat.add i a) = (Nat.add a i).
Proof. exact (@lem1032098 a i). Qed.
Lemma lem7644292 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7644293 (a : nat) (i : nat) : (term4 i a) = (term4 a i).
Proof. exact (MK_COMB (@lem7644292) (@lem7644291 a i)). Qed.
Lemma lem7644294 (i : nat) (a : nat) (b : nat) : (term223 i a b) = (term224 i a b).
Proof. exact (MK_COMB (@lem7644293 a i) (@lem7644284 a b)). Qed.
Lemma lem7644301 (a : nat) (i : nat) : (Nat.add i a) = (Nat.add a i).
Proof. exact (@lem1032098 a i). Qed.
Lemma lem7644304 : term225 = term225.
Proof. exact (eq_refl term225). Qed.
Lemma lem7644305 (a : nat) (i : nat) : (term226 i a) = (term226 a i).
Proof. exact (MK_COMB (@lem7644304) (@lem7644301 a i)). Qed.
Lemma lem7644306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7644307 (a : nat) (i : nat) : (term227 i a) = (term227 a i).
Proof. exact (MK_COMB (@lem7644306) (@lem7644305 a i)). Qed.
Lemma lem7644308 (i : nat) (a : nat) (b : nat) : (term216 i a b) = (term228 i a b).
Proof. exact (MK_COMB (@lem7644307 a i) (@lem7644294 i a b)). Qed.
Lemma lem7644327 (i : nat) (b : nat) : (term218 i b) = (term218 i b).
Proof. exact (eq_refl (term218 i b)). Qed.
Lemma lem7644328 (i : nat) (a : nat) (b : nat) : (term220 i a b) = (term229 i a b).
Proof. exact (MK_COMB (@lem7644327 i b) (@lem7644308 i a b)). Qed.
Lemma lem7644331 (i : nat) (a : nat) (b : nat) : (term221 i a b) = (term229 i a b).
Proof. exact (TRANS (@lem7644277 i a b) (@lem7644328 i a b)). Qed.
Lemma lem7644333 (m : nat) (n : nat) : (Peano.le m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7644334 (i : nat) : (term2 i) = (term11 i).
Proof. exact (@lem7644333 term12 i). Qed.
Lemma lem7644335 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7644336 (i : nat) : (term13 i) = (term14 i).
Proof. exact (MK_COMB (@lem7644335) (@lem7644334 i)). Qed.
Lemma lem7644337 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7644338 (i : nat) : (term8 i) = (term15 i).
Proof. exact (MK_COMB (@lem7644337) (@lem7644336 i)). Qed.
Lemma lem7644340 (m : nat) (n : nat) : (Peano.le m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7644341 (i : nat) (b : nat) : (Peano.le i b) = (term10 i b).
Proof. exact (@lem7644340 i b). Qed.
Lemma lem7644342 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7644343 (i : nat) (b : nat) : (term230 i b) = (term231 i b).
Proof. exact (MK_COMB (@lem7644342) (@lem7644341 i b)). Qed.
Lemma lem7644344 (i : nat) (b : nat) : (term215 i b) = (term232 i b).
Proof. exact (MK_COMB (@lem7644338 i) (@lem7644343 i b)). Qed.
Lemma lem7644345 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7644346 (i : nat) (b : nat) : (term218 i b) = (term233 i b).
Proof. exact (MK_COMB (@lem7644345) (@lem7644344 i b)). Qed.
Lemma lem7644348 (m : nat) (n : nat) : (Peano.le m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7644349 (a : nat) (i : nat) : (term226 a i) = (term234 a i).
Proof. exact (@lem7644348 term12 (Nat.add a i)). Qed.
Lemma lem7644351 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7644352 (a : nat) (i : nat) : (term17 a i) = (term18 a i).
Proof. exact (@lem7644351 a i). Qed.
Lemma lem7644353 : term235 = term235.
Proof. exact (eq_refl term235). Qed.
Lemma lem7644354 (a : nat) (i : nat) : (term234 a i) = (term236 a i).
Proof. exact (MK_COMB (@lem7644353) (@lem7644352 a i)). Qed.
Lemma lem7644355 (a : nat) (i : nat) : (term226 a i) = (term236 a i).
Proof. exact (TRANS (@lem7644349 a i) (@lem7644354 a i)). Qed.
Lemma lem7644356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7644357 (a : nat) (i : nat) : (term227 a i) = (term237 a i).
Proof. exact (MK_COMB (@lem7644356) (@lem7644355 a i)). Qed.
Lemma lem7644359 (m : nat) (n : nat) : (Peano.le m n) = (term10 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7644360 (i : nat) (a : nat) (b : nat) : (term224 i a b) = (term238 i a b).
Proof. exact (@lem7644359 (Nat.add a i) (Nat.add a b)). Qed.
Lemma lem7644362 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7644363 (a : nat) (i : nat) : (term17 a i) = (term18 a i).
Proof. exact (@lem7644362 a i). Qed.
Lemma lem7644364 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem7644365 (a : nat) (i : nat) : (term19 a i) = (term20 a i).
Proof. exact (MK_COMB (@lem7644364) (@lem7644363 a i)). Qed.
Lemma lem7644367 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7644368 (a : nat) (b : nat) : (term17 a b) = (term18 a b).
Proof. exact (@lem7644367 a b). Qed.
Lemma lem7644369 (i : nat) (a : nat) (b : nat) : (term238 i a b) = (term239 i a b).
Proof. exact (MK_COMB (@lem7644365 a i) (@lem7644368 a b)). Qed.
Lemma lem7644370 (i : nat) (a : nat) (b : nat) : (term224 i a b) = (term239 i a b).
Proof. exact (TRANS (@lem7644360 i a b) (@lem7644369 i a b)). Qed.
Lemma lem7644371 (i : nat) (a : nat) (b : nat) : (term228 i a b) = (term240 i a b).
Proof. exact (MK_COMB (@lem7644357 a i) (@lem7644370 i a b)). Qed.
Lemma lem7644372 (i : nat) (a : nat) (b : nat) : (term229 i a b) = (term241 i a b).
Proof. exact (MK_COMB (@lem7644346 i b) (@lem7644371 i a b)). Qed.
Lemma lem7644373 (i : nat) (a : nat) (b : nat) : (term221 i a b) = (term241 i a b).
Proof. exact (TRANS (@lem7644331 i a b) (@lem7644372 i a b)). Qed.
Lemma lem7644374 (a : nat) : term24 a.
Proof. exact (@lem2307535 a). Qed.
Lemma lem7644375 (a : nat) : (term24 a) = (term25 a).
Proof. exact (eq_refl (term24 a)). Qed.
Lemma lem7644376 (a : nat) : term25 a.
Proof. exact (EQ_MP (@lem7644375 a) (@lem7644374 a)). Qed.
Lemma lem7644377 (b : nat) : term24 b.
Proof. exact (@lem2307535 b). Qed.
Lemma lem7644378 (b : nat) : (term24 b) = (term25 b).
Proof. exact (eq_refl (term24 b)). Qed.
Lemma lem7644379 (b : nat) : term25 b.
Proof. exact (EQ_MP (@lem7644378 b) (@lem7644377 b)). Qed.
Lemma lem7644380 (i : nat) : term24 i.
Proof. exact (@lem2307535 i). Qed.
Lemma lem7644381 (i : nat) : (term24 i) = (term25 i).
Proof. exact (eq_refl (term24 i)). Qed.
Lemma lem7644382 (i : nat) : term25 i.
Proof. exact (EQ_MP (@lem7644381 i) (@lem7644380 i)). Qed.
Lemma lem7644383 (_98510 : int) (_98508 : int) (_98509 : int) : (term242 _98510 _98508 _98509) = (term243 _98510 _98508 _98509).
Proof. exact (@lem2318604 (term243 _98510 _98508 _98509)). Qed.
Lemma lem7644406 (_98510 : int) : (term28 _98510) = (term29 _98510).
Proof. exact (@lem16933 (term29 _98510)). Qed.
Lemma lem7644409 (_98510 : int) (_98509 : int) : (term244 _98510 _98509) = (int_le _98510 _98509).
Proof. exact (@lem16933 (int_le _98510 _98509)). Qed.
Lemma lem7644410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7644411 (_98510 : int) : (term32 _98510) = (term33 _98510).
Proof. exact (MK_COMB (@lem7644410) (@lem7644406 _98510)). Qed.
Lemma lem7644412 (_98510 : int) (_98509 : int) : (term245 _98510 _98509) = (term246 _98510 _98509).
Proof. exact (MK_COMB (@lem7644411 _98510) (@lem7644409 _98510 _98509)). Qed.
Lemma lem7644413 (_98510 : int) (_98509 : int) : (term247 _98510 _98509) = (term245 _98510 _98509).
Proof. exact (@lem17160 (term37 _98510) (term248 _98510 _98509)). Qed.
Lemma lem7644414 (_98510 : int) (_98509 : int) : (term247 _98510 _98509) = (term246 _98510 _98509).
Proof. exact (TRANS (@lem7644413 _98510 _98509) (@lem7644412 _98510 _98509)). Qed.
Lemma lem7644421 (_98510 : int) (_98508 : int) (_98509 : int) : (term249 _98510 _98508 _98509) = (term250 _98510 _98508 _98509).
Proof. exact (@lem17045 (term251 _98508 _98510) (term252 _98510 _98508 _98509)). Qed.
Lemma lem7644422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7644423 (_98510 : int) (_98509 : int) : (term253 _98510 _98509) = (term254 _98510 _98509).
Proof. exact (MK_COMB (@lem7644422) (@lem7644414 _98510 _98509)). Qed.
Lemma lem7644424 (_98510 : int) (_98508 : int) (_98509 : int) : (term255 _98510 _98508 _98509) = (term256 _98510 _98508 _98509).
Proof. exact (MK_COMB (@lem7644423 _98510 _98509) (@lem7644421 _98510 _98508 _98509)). Qed.
Lemma lem7644425 (_98510 : int) (_98508 : int) (_98509 : int) : (term257 _98510 _98508 _98509) = (term255 _98510 _98508 _98509).
Proof. exact (@lem17160 (term258 _98510 _98509) (term259 _98510 _98508 _98509)). Qed.
Lemma lem7644426 (_98510 : int) (_98508 : int) (_98509 : int) : (term257 _98510 _98508 _98509) = (term256 _98510 _98508 _98509).
Proof. exact (TRANS (@lem7644425 _98510 _98508 _98509) (@lem7644424 _98510 _98508 _98509)). Qed.
Lemma lem7644428 (_98510 : int) : (term39 _98510) = (term39 _98510).
Proof. exact (eq_refl (term39 _98510)). Qed.
Lemma lem7644429 (_98510 : int) (_98508 : int) (_98509 : int) : (term260 _98510 _98508 _98509) = (term261 _98510 _98508 _98509).
Proof. exact (MK_COMB (@lem7644428 _98510) (@lem7644426 _98510 _98508 _98509)). Qed.
Lemma lem7644430 (_98510 : int) (_98508 : int) (_98509 : int) : (term262 _98510 _98508 _98509) = (term260 _98510 _98508 _98509).
Proof. exact (@lem17362 (term43 _98510) (term263 _98510 _98508 _98509)). Qed.
Lemma lem7644431 (_98510 : int) (_98508 : int) (_98509 : int) : (term262 _98510 _98508 _98509) = (term261 _98510 _98508 _98509).
Proof. exact (TRANS (@lem7644430 _98510 _98508 _98509) (@lem7644429 _98510 _98508 _98509)). Qed.
Lemma lem7644433 (_98509 : int) : (term39 _98509) = (term39 _98509).
Proof. exact (eq_refl (term39 _98509)). Qed.
Lemma lem7644434 (_98510 : int) (_98508 : int) (_98509 : int) : (term264 _98510 _98508 _98509) = (term265 _98510 _98508 _98509).
Proof. exact (MK_COMB (@lem7644433 _98509) (@lem7644431 _98510 _98508 _98509)). Qed.
Lemma lem7644435 (_98510 : int) (_98508 : int) (_98509 : int) : (term266 _98510 _98508 _98509) = (term264 _98510 _98508 _98509).
Proof. exact (@lem17362 (term43 _98509) (term267 _98510 _98508 _98509)). Qed.
Lemma lem7644436 (_98510 : int) (_98508 : int) (_98509 : int) : (term266 _98510 _98508 _98509) = (term265 _98510 _98508 _98509).
Proof. exact (TRANS (@lem7644435 _98510 _98508 _98509) (@lem7644434 _98510 _98508 _98509)). Qed.
Lemma lem7644438 (_98508 : int) : (term39 _98508) = (term39 _98508).
Proof. exact (eq_refl (term39 _98508)). Qed.
Lemma lem7644439 (_98510 : int) (_98508 : int) (_98509 : int) : (term268 _98510 _98508 _98509) = (term269 _98510 _98508 _98509).
Proof. exact (MK_COMB (@lem7644438 _98508) (@lem7644436 _98510 _98508 _98509)). Qed.
Lemma lem7644440 (_98510 : int) (_98508 : int) (_98509 : int) : (term270 _98510 _98508 _98509) = (term268 _98510 _98508 _98509).
Proof. exact (@lem17362 (term43 _98508) (term271 _98510 _98508 _98509)). Qed.
Lemma lem7644472 (_98510 : int) (_98508 : int) (_98509 : int) : (term270 _98510 _98508 _98509) = (term269 _98510 _98508 _98509).
Proof. exact (TRANS (@lem7644440 _98510 _98508 _98509) (@lem7644439 _98510 _98508 _98509)). Qed.
Lemma lem7644475 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7644476 (_98508 : int) : (term43 _98508) = (term50 _98508).
Proof. exact (@lem7644475 term51 _98508). Qed.
Lemma lem7644478 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7644479 : term53 = term54.
Proof. exact (@lem7644478 (NUMERAL 0)). Qed.
Lemma lem7644480 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7644481 : term55 = term56.
Proof. exact (MK_COMB (@lem7644480) (@lem7644479)). Qed.
Lemma lem7644482 (_98508 : int) : (real_of_int _98508) = (real_of_int _98508).
Proof. exact (eq_refl (real_of_int _98508)). Qed.
Lemma lem7644483 (_98508 : int) : (term50 _98508) = (term57 _98508).
Proof. exact (MK_COMB (@lem7644481) (@lem7644482 _98508)). Qed.
Lemma lem7644485 (_98508 : int) : (term43 _98508) = (term57 _98508).
Proof. exact (TRANS (@lem7644476 _98508) (@lem7644483 _98508)). Qed.
Lemma lem7644488 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7644489 (_98509 : int) : (term43 _98509) = (term50 _98509).
Proof. exact (@lem7644488 term51 _98509). Qed.
Lemma lem7644491 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7644492 : term53 = term54.
Proof. exact (@lem7644491 (NUMERAL 0)). Qed.
Lemma lem7644493 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7644494 : term55 = term56.
Proof. exact (MK_COMB (@lem7644493) (@lem7644492)). Qed.
Lemma lem7644495 (_98509 : int) : (real_of_int _98509) = (real_of_int _98509).
Proof. exact (eq_refl (real_of_int _98509)). Qed.
Lemma lem7644496 (_98509 : int) : (term50 _98509) = (term57 _98509).
Proof. exact (MK_COMB (@lem7644494) (@lem7644495 _98509)). Qed.
Lemma lem7644498 (_98509 : int) : (term43 _98509) = (term57 _98509).
Proof. exact (TRANS (@lem7644489 _98509) (@lem7644496 _98509)). Qed.
Lemma lem7644501 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7644502 (_98510 : int) : (term43 _98510) = (term50 _98510).
Proof. exact (@lem7644501 term51 _98510). Qed.
Lemma lem7644504 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7644505 : term53 = term54.
Proof. exact (@lem7644504 (NUMERAL 0)). Qed.
Lemma lem7644506 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7644507 : term55 = term56.
Proof. exact (MK_COMB (@lem7644506) (@lem7644505)). Qed.
Lemma lem7644508 (_98510 : int) : (real_of_int _98510) = (real_of_int _98510).
Proof. exact (eq_refl (real_of_int _98510)). Qed.
Lemma lem7644509 (_98510 : int) : (term50 _98510) = (term57 _98510).
Proof. exact (MK_COMB (@lem7644507) (@lem7644508 _98510)). Qed.
Lemma lem7644511 (_98510 : int) : (term43 _98510) = (term57 _98510).
Proof. exact (TRANS (@lem7644502 _98510) (@lem7644509 _98510)). Qed.
Lemma lem7644514 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7644515 (_98510 : int) : (term29 _98510) = (term58 _98510).
Proof. exact (@lem7644514 term59 _98510). Qed.
Lemma lem7644517 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7644518 : term60 = term61.
Proof. exact (@lem7644517 term12). Qed.
Lemma lem7644519 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7644520 : term62 = term63.
Proof. exact (MK_COMB (@lem7644519) (@lem7644518)). Qed.
Lemma lem7644521 (_98510 : int) : (real_of_int _98510) = (real_of_int _98510).
Proof. exact (eq_refl (real_of_int _98510)). Qed.
Lemma lem7644522 (_98510 : int) : (term58 _98510) = (term64 _98510).
Proof. exact (MK_COMB (@lem7644520) (@lem7644521 _98510)). Qed.
Lemma lem7644524 (_98510 : int) : (term29 _98510) = (term64 _98510).
Proof. exact (TRANS (@lem7644515 _98510) (@lem7644522 _98510)). Qed.
Lemma lem7644527 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7644529 (_98510 : int) (_98509 : int) : (int_le _98510 _98509) = (term49 _98510 _98509).
Proof. exact (@lem7644527 _98510 _98509). Qed.
Lemma lem7644530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7644531 (_98510 : int) : (term33 _98510) = (term71 _98510).
Proof. exact (MK_COMB (@lem7644530) (@lem7644524 _98510)). Qed.
Lemma lem7644532 (_98510 : int) (_98509 : int) : (term246 _98510 _98509) = (term272 _98510 _98509).
Proof. exact (MK_COMB (@lem7644531 _98510) (@lem7644529 _98510 _98509)). Qed.
Lemma lem7644534 (y : int) (x : int) : (term248 x y) = (term273 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7644535 (_98508 : int) (_98510 : int) : (term274 _98508 _98510) = (term275 _98508 _98510).
Proof. exact (@lem7644534 (int_add _98508 _98510) term59). Qed.
Lemma lem7644537 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7644538 (_98508 : int) (_98510 : int) : (term275 _98508 _98510) = (term276 _98508 _98510).
Proof. exact (@lem7644537 (term277 _98508 _98510) term59). Qed.
Lemma lem7644540 (x : int) (y : int) : (term66 x y) = (term67 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7644541 (_98508 : int) (_98510 : int) : (term278 _98508 _98510) = (term279 _98508 _98510).
Proof. exact (@lem7644540 (int_add _98508 _98510) term59). Qed.
Lemma lem7644543 (x : int) (y : int) : (term66 x y) = (term67 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7644544 (_98508 : int) (_98510 : int) : (term66 _98508 _98510) = (term67 _98508 _98510).
Proof. exact (@lem7644543 _98508 _98510). Qed.
Lemma lem7644545 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7644546 (_98508 : int) (_98510 : int) : (term280 _98508 _98510) = (term281 _98508 _98510).
Proof. exact (MK_COMB (@lem7644545) (@lem7644544 _98508 _98510)). Qed.
Lemma lem7644548 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7644549 : term60 = term61.
Proof. exact (@lem7644548 term12). Qed.
Lemma lem7644550 (_98508 : int) (_98510 : int) : (term279 _98508 _98510) = (term282 _98508 _98510).
Proof. exact (MK_COMB (@lem7644546 _98508 _98510) (@lem7644549)). Qed.
Lemma lem7644551 (_98508 : int) (_98510 : int) : (term278 _98508 _98510) = (term282 _98508 _98510).
Proof. exact (TRANS (@lem7644541 _98508 _98510) (@lem7644550 _98508 _98510)). Qed.
Lemma lem7644552 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7644553 (_98508 : int) (_98510 : int) : (term283 _98508 _98510) = (term284 _98508 _98510).
Proof. exact (MK_COMB (@lem7644552) (@lem7644551 _98508 _98510)). Qed.
Lemma lem7644555 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7644556 : term60 = term61.
Proof. exact (@lem7644555 term12). Qed.
Lemma lem7644557 (_98508 : int) (_98510 : int) : (term276 _98508 _98510) = (term285 _98508 _98510).
Proof. exact (MK_COMB (@lem7644553 _98508 _98510) (@lem7644556)). Qed.
Lemma lem7644558 (_98508 : int) (_98510 : int) : (term275 _98508 _98510) = (term285 _98508 _98510).
Proof. exact (TRANS (@lem7644538 _98508 _98510) (@lem7644557 _98508 _98510)). Qed.
Lemma lem7644559 (_98508 : int) (_98510 : int) : (term274 _98508 _98510) = (term285 _98508 _98510).
Proof. exact (TRANS (@lem7644535 _98508 _98510) (@lem7644558 _98508 _98510)). Qed.
Lemma lem7644561 (y : int) (x : int) : (term248 x y) = (term273 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7644562 (_98509 : int) (_98508 : int) (_98510 : int) : (term286 _98510 _98508 _98509) = (term287 _98509 _98508 _98510).
Proof. exact (@lem7644561 (int_add _98508 _98509) (int_add _98508 _98510)). Qed.
Lemma lem7644564 (x : int) (y : int) : (int_le x y) = (term49 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7644565 (_98509 : int) (_98508 : int) (_98510 : int) : (term287 _98509 _98508 _98510) = (term288 _98509 _98508 _98510).
Proof. exact (@lem7644564 (term277 _98508 _98509) (int_add _98508 _98510)). Qed.
Lemma lem7644567 (x : int) (y : int) : (term66 x y) = (term67 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7644568 (_98508 : int) (_98509 : int) : (term278 _98508 _98509) = (term279 _98508 _98509).
Proof. exact (@lem7644567 (int_add _98508 _98509) term59). Qed.
Lemma lem7644570 (x : int) (y : int) : (term66 x y) = (term67 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7644571 (_98508 : int) (_98509 : int) : (term66 _98508 _98509) = (term67 _98508 _98509).
Proof. exact (@lem7644570 _98508 _98509). Qed.
Lemma lem7644572 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7644573 (_98508 : int) (_98509 : int) : (term280 _98508 _98509) = (term281 _98508 _98509).
Proof. exact (MK_COMB (@lem7644572) (@lem7644571 _98508 _98509)). Qed.
Lemma lem7644575 (n : nat) : (term52 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7644576 : term60 = term61.
Proof. exact (@lem7644575 term12). Qed.
Lemma lem7644577 (_98508 : int) (_98509 : int) : (term279 _98508 _98509) = (term282 _98508 _98509).
Proof. exact (MK_COMB (@lem7644573 _98508 _98509) (@lem7644576)). Qed.
Lemma lem7644578 (_98508 : int) (_98509 : int) : (term278 _98508 _98509) = (term282 _98508 _98509).
Proof. exact (TRANS (@lem7644568 _98508 _98509) (@lem7644577 _98508 _98509)). Qed.
Lemma lem7644579 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7644580 (_98508 : int) (_98509 : int) : (term283 _98508 _98509) = (term284 _98508 _98509).
Proof. exact (MK_COMB (@lem7644579) (@lem7644578 _98508 _98509)). Qed.
Lemma lem7644582 (x : int) (y : int) : (term66 x y) = (term67 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7644583 (_98508 : int) (_98510 : int) : (term66 _98508 _98510) = (term67 _98508 _98510).
Proof. exact (@lem7644582 _98508 _98510). Qed.
Lemma lem7644584 (_98509 : int) (_98508 : int) (_98510 : int) : (term288 _98509 _98508 _98510) = (term289 _98509 _98508 _98510).
Proof. exact (MK_COMB (@lem7644580 _98508 _98509) (@lem7644583 _98508 _98510)). Qed.
Lemma lem7644585 (_98509 : int) (_98508 : int) (_98510 : int) : (term287 _98509 _98508 _98510) = (term289 _98509 _98508 _98510).
Proof. exact (TRANS (@lem7644565 _98509 _98508 _98510) (@lem7644584 _98509 _98508 _98510)). Qed.
Lemma lem7644586 (_98509 : int) (_98508 : int) (_98510 : int) : (term286 _98510 _98508 _98509) = (term289 _98509 _98508 _98510).
Proof. exact (TRANS (@lem7644562 _98509 _98508 _98510) (@lem7644585 _98509 _98508 _98510)). Qed.
Lemma lem7644587 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7644588 (_98508 : int) (_98510 : int) : (term290 _98508 _98510) = (term291 _98508 _98510).
Proof. exact (MK_COMB (@lem7644587) (@lem7644559 _98508 _98510)). Qed.
Lemma lem7644589 (_98509 : int) (_98508 : int) (_98510 : int) : (term250 _98510 _98508 _98509) = (term292 _98509 _98508 _98510).
Proof. exact (MK_COMB (@lem7644588 _98508 _98510) (@lem7644586 _98509 _98508 _98510)). Qed.
Lemma lem7644590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7644591 (_98510 : int) (_98509 : int) : (term254 _98510 _98509) = (term293 _98510 _98509).
Proof. exact (MK_COMB (@lem7644590) (@lem7644532 _98510 _98509)). Qed.
Lemma lem7644592 (_98509 : int) (_98508 : int) (_98510 : int) : (term256 _98510 _98508 _98509) = (term294 _98509 _98508 _98510).
Proof. exact (MK_COMB (@lem7644591 _98510 _98509) (@lem7644589 _98509 _98508 _98510)). Qed.
Lemma lem7644593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7644594 (_98510 : int) : (term39 _98510) = (term73 _98510).
Proof. exact (MK_COMB (@lem7644593) (@lem7644511 _98510)). Qed.
Lemma lem7644595 (_98509 : int) (_98508 : int) (_98510 : int) : (term261 _98510 _98508 _98509) = (term295 _98509 _98508 _98510).
Proof. exact (MK_COMB (@lem7644594 _98510) (@lem7644592 _98509 _98508 _98510)). Qed.
Lemma lem7644596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7644597 (_98509 : int) : (term39 _98509) = (term73 _98509).
Proof. exact (MK_COMB (@lem7644596) (@lem7644498 _98509)). Qed.
Lemma lem7644598 (_98509 : int) (_98508 : int) (_98510 : int) : (term265 _98510 _98508 _98509) = (term296 _98509 _98508 _98510).
Proof. exact (MK_COMB (@lem7644597 _98509) (@lem7644595 _98509 _98508 _98510)). Qed.
Lemma lem7644599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7644600 (_98508 : int) : (term39 _98508) = (term73 _98508).
Proof. exact (MK_COMB (@lem7644599) (@lem7644485 _98508)). Qed.
Lemma lem7644601 (_98509 : int) (_98508 : int) (_98510 : int) : (term269 _98510 _98508 _98509) = (term297 _98509 _98508 _98510).
Proof. exact (MK_COMB (@lem7644600 _98508) (@lem7644598 _98509 _98508 _98510)). Qed.
Lemma lem7644602 (_98509 : int) (_98508 : int) (_98510 : int) : (term270 _98510 _98508 _98509) = (term297 _98509 _98508 _98510).
Proof. exact (TRANS (@lem7644472 _98510 _98508 _98509) (@lem7644601 _98509 _98508 _98510)). Qed.
Lemma lem7644606 (t : Prop) : (term76 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7644672 (_98509 : int) (_98508 : int) (_98510 : int) : (term298 _98509 _98508 _98510) = (term297 _98509 _98508 _98510).
Proof. exact (@lem7644606 (term297 _98509 _98508 _98510)). Qed.
Lemma lem7644673 (_98508 : int) : (term57 _98508) = (term78 _98508).
Proof. exact (@lem1988287 (real_of_int _98508) term54). Qed.
Lemma lem7644679 (_98508 : int) : (term79 _98508) = (term80 _98508).
Proof. exact (@lem1982792 (real_of_int _98508) term54). Qed.
Lemma lem7644681 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7644682 : term54 = term82.
Proof. exact (@lem7644681 (NUMERAL 0)). Qed.
Lemma lem7644684 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7644685 : term85 = term86.
Proof. exact (@lem7644684 term12). Qed.
Lemma lem7644686 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7644687 : term87 = term88.
Proof. exact (MK_COMB (@lem7644686) (@lem7644685)). Qed.
Lemma lem7644688 : term89 = term90.
Proof. exact (MK_COMB (@lem7644687) (@lem7644682)). Qed.
Lemma lem7644689 : term90 = term91.
Proof. exact (@lem1981613 term85 term54 term61 term61). Qed.
Lemma lem7644691 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7644692 : term94 = term95.
Proof. exact (@lem7644691 term12 term12). Qed.
Lemma lem7644693 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7644694 : term97 = term12.
Proof. exact (EQ_MP (@lem7644693) (@lem940073)). Qed.
Lemma lem7644695 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7644696 : term95 = term61.
Proof. exact (MK_COMB (@lem7644695) (@lem7644694)). Qed.
Lemma lem7644697 : term94 = term61.
Proof. exact (TRANS (@lem7644692) (@lem7644696)). Qed.
Lemma lem7644699 (x : nat) : (term98 x) = term54.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7644700 : term89 = term54.
Proof. exact (@lem7644699 term12). Qed.
Lemma lem7644701 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7644702 : term99 = term100.
Proof. exact (MK_COMB (@lem7644701) (@lem7644700)). Qed.
Lemma lem7644703 : term91 = term82.
Proof. exact (MK_COMB (@lem7644702) (@lem7644697)). Qed.
Lemma lem7644704 : term90 = term82.
Proof. exact (TRANS (@lem7644689) (@lem7644703)). Qed.
Lemma lem7644705 : term89 = term82.
Proof. exact (TRANS (@lem7644688) (@lem7644704)). Qed.
Lemma lem7644707 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7644708 : term82 = term54.
Proof. exact (@lem7644707 term54). Qed.
Lemma lem7644709 : term89 = term54.
Proof. exact (TRANS (@lem7644705) (@lem7644708)). Qed.
Lemma lem7644710 (_98508 : int) : (term102 _98508) = (term102 _98508).
Proof. exact (eq_refl (term102 _98508)). Qed.
Lemma lem7644711 (_98508 : int) : (term80 _98508) = (term103 _98508).
Proof. exact (MK_COMB (@lem7644710 _98508) (@lem7644709)). Qed.
Lemma lem7644712 (_98508 : int) : (term103 _98508) = (real_of_int _98508).
Proof. exact (@lem1982723 (real_of_int _98508)). Qed.
Lemma lem7644713 (_98508 : int) : (term80 _98508) = (real_of_int _98508).
Proof. exact (TRANS (@lem7644711 _98508) (@lem7644712 _98508)). Qed.
Lemma lem7644715 (_98508 : int) : (term79 _98508) = (real_of_int _98508).
Proof. exact (TRANS (@lem7644679 _98508) (@lem7644713 _98508)). Qed.
Lemma lem7644716 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7644717 (_98508 : int) : (term104 _98508) = (term105 _98508).
Proof. exact (MK_COMB (@lem7644716) (@lem7644715 _98508)). Qed.
Lemma lem7644718 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7644719 (_98508 : int) : (term78 _98508) = (term106 _98508).
Proof. exact (MK_COMB (@lem7644717 _98508) (@lem7644718)). Qed.
Lemma lem7644720 (_98508 : int) : (term57 _98508) = (term106 _98508).
Proof. exact (TRANS (@lem7644673 _98508) (@lem7644719 _98508)). Qed.
Lemma lem7644721 (_98509 : int) : (term57 _98509) = (term78 _98509).
Proof. exact (@lem1988287 (real_of_int _98509) term54). Qed.
Lemma lem7644727 (_98509 : int) : (term79 _98509) = (term80 _98509).
Proof. exact (@lem1982792 (real_of_int _98509) term54). Qed.
Lemma lem7644729 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7644730 : term54 = term82.
Proof. exact (@lem7644729 (NUMERAL 0)). Qed.
Lemma lem7644732 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7644733 : term85 = term86.
Proof. exact (@lem7644732 term12). Qed.
Lemma lem7644734 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7644735 : term87 = term88.
Proof. exact (MK_COMB (@lem7644734) (@lem7644733)). Qed.
Lemma lem7644736 : term89 = term90.
Proof. exact (MK_COMB (@lem7644735) (@lem7644730)). Qed.
Lemma lem7644737 : term90 = term91.
Proof. exact (@lem1981613 term85 term54 term61 term61). Qed.
Lemma lem7644739 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7644740 : term94 = term95.
Proof. exact (@lem7644739 term12 term12). Qed.
Lemma lem7644741 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7644742 : term97 = term12.
Proof. exact (EQ_MP (@lem7644741) (@lem940073)). Qed.
Lemma lem7644743 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7644744 : term95 = term61.
Proof. exact (MK_COMB (@lem7644743) (@lem7644742)). Qed.
Lemma lem7644745 : term94 = term61.
Proof. exact (TRANS (@lem7644740) (@lem7644744)). Qed.
Lemma lem7644747 (x : nat) : (term98 x) = term54.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7644748 : term89 = term54.
Proof. exact (@lem7644747 term12). Qed.
Lemma lem7644749 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7644750 : term99 = term100.
Proof. exact (MK_COMB (@lem7644749) (@lem7644748)). Qed.
Lemma lem7644751 : term91 = term82.
Proof. exact (MK_COMB (@lem7644750) (@lem7644745)). Qed.
Lemma lem7644752 : term90 = term82.
Proof. exact (TRANS (@lem7644737) (@lem7644751)). Qed.
Lemma lem7644753 : term89 = term82.
Proof. exact (TRANS (@lem7644736) (@lem7644752)). Qed.
Lemma lem7644755 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7644756 : term82 = term54.
Proof. exact (@lem7644755 term54). Qed.
Lemma lem7644757 : term89 = term54.
Proof. exact (TRANS (@lem7644753) (@lem7644756)). Qed.
Lemma lem7644758 (_98509 : int) : (term102 _98509) = (term102 _98509).
Proof. exact (eq_refl (term102 _98509)). Qed.
Lemma lem7644759 (_98509 : int) : (term80 _98509) = (term103 _98509).
Proof. exact (MK_COMB (@lem7644758 _98509) (@lem7644757)). Qed.
Lemma lem7644760 (_98509 : int) : (term103 _98509) = (real_of_int _98509).
Proof. exact (@lem1982723 (real_of_int _98509)). Qed.
Lemma lem7644761 (_98509 : int) : (term80 _98509) = (real_of_int _98509).
Proof. exact (TRANS (@lem7644759 _98509) (@lem7644760 _98509)). Qed.
Lemma lem7644763 (_98509 : int) : (term79 _98509) = (real_of_int _98509).
Proof. exact (TRANS (@lem7644727 _98509) (@lem7644761 _98509)). Qed.
Lemma lem7644764 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7644765 (_98509 : int) : (term104 _98509) = (term105 _98509).
Proof. exact (MK_COMB (@lem7644764) (@lem7644763 _98509)). Qed.
Lemma lem7644766 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7644767 (_98509 : int) : (term78 _98509) = (term106 _98509).
Proof. exact (MK_COMB (@lem7644765 _98509) (@lem7644766)). Qed.
Lemma lem7644768 (_98509 : int) : (term57 _98509) = (term106 _98509).
Proof. exact (TRANS (@lem7644721 _98509) (@lem7644767 _98509)). Qed.
Lemma lem7644769 (_98510 : int) : (term57 _98510) = (term78 _98510).
Proof. exact (@lem1988287 (real_of_int _98510) term54). Qed.
Lemma lem7644775 (_98510 : int) : (term79 _98510) = (term80 _98510).
Proof. exact (@lem1982792 (real_of_int _98510) term54). Qed.
Lemma lem7644777 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7644778 : term54 = term82.
Proof. exact (@lem7644777 (NUMERAL 0)). Qed.
Lemma lem7644780 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7644781 : term85 = term86.
Proof. exact (@lem7644780 term12). Qed.
Lemma lem7644782 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7644783 : term87 = term88.
Proof. exact (MK_COMB (@lem7644782) (@lem7644781)). Qed.
Lemma lem7644784 : term89 = term90.
Proof. exact (MK_COMB (@lem7644783) (@lem7644778)). Qed.
Lemma lem7644785 : term90 = term91.
Proof. exact (@lem1981613 term85 term54 term61 term61). Qed.
Lemma lem7644787 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7644788 : term94 = term95.
Proof. exact (@lem7644787 term12 term12). Qed.
Lemma lem7644789 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7644790 : term97 = term12.
Proof. exact (EQ_MP (@lem7644789) (@lem940073)). Qed.
Lemma lem7644791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7644792 : term95 = term61.
Proof. exact (MK_COMB (@lem7644791) (@lem7644790)). Qed.
Lemma lem7644793 : term94 = term61.
Proof. exact (TRANS (@lem7644788) (@lem7644792)). Qed.
Lemma lem7644795 (x : nat) : (term98 x) = term54.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7644796 : term89 = term54.
Proof. exact (@lem7644795 term12). Qed.
Lemma lem7644797 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7644798 : term99 = term100.
Proof. exact (MK_COMB (@lem7644797) (@lem7644796)). Qed.
Lemma lem7644799 : term91 = term82.
Proof. exact (MK_COMB (@lem7644798) (@lem7644793)). Qed.
Lemma lem7644800 : term90 = term82.
Proof. exact (TRANS (@lem7644785) (@lem7644799)). Qed.
Lemma lem7644801 : term89 = term82.
Proof. exact (TRANS (@lem7644784) (@lem7644800)). Qed.
Lemma lem7644803 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7644804 : term82 = term54.
Proof. exact (@lem7644803 term54). Qed.
Lemma lem7644805 : term89 = term54.
Proof. exact (TRANS (@lem7644801) (@lem7644804)). Qed.
Lemma lem7644806 (_98510 : int) : (term102 _98510) = (term102 _98510).
Proof. exact (eq_refl (term102 _98510)). Qed.
Lemma lem7644807 (_98510 : int) : (term80 _98510) = (term103 _98510).
Proof. exact (MK_COMB (@lem7644806 _98510) (@lem7644805)). Qed.
Lemma lem7644808 (_98510 : int) : (term103 _98510) = (real_of_int _98510).
Proof. exact (@lem1982723 (real_of_int _98510)). Qed.
Lemma lem7644809 (_98510 : int) : (term80 _98510) = (real_of_int _98510).
Proof. exact (TRANS (@lem7644807 _98510) (@lem7644808 _98510)). Qed.
Lemma lem7644811 (_98510 : int) : (term79 _98510) = (real_of_int _98510).
Proof. exact (TRANS (@lem7644775 _98510) (@lem7644809 _98510)). Qed.
Lemma lem7644812 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7644813 (_98510 : int) : (term104 _98510) = (term105 _98510).
Proof. exact (MK_COMB (@lem7644812) (@lem7644811 _98510)). Qed.
Lemma lem7644814 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7644815 (_98510 : int) : (term78 _98510) = (term106 _98510).
Proof. exact (MK_COMB (@lem7644813 _98510) (@lem7644814)). Qed.
Lemma lem7644816 (_98510 : int) : (term57 _98510) = (term106 _98510).
Proof. exact (TRANS (@lem7644769 _98510) (@lem7644815 _98510)). Qed.
Lemma lem7644817 (_98510 : int) : (term64 _98510) = (term107 _98510).
Proof. exact (@lem1988287 (real_of_int _98510) term61). Qed.
Lemma lem7644823 (_98510 : int) : (term108 _98510) = (term109 _98510).
Proof. exact (@lem1982792 (real_of_int _98510) term61). Qed.
Lemma lem7644825 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7644826 : term61 = term110.
Proof. exact (@lem7644825 term12). Qed.
Lemma lem7644828 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7644829 : term85 = term86.
Proof. exact (@lem7644828 term12). Qed.
Lemma lem7644830 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7644831 : term87 = term88.
Proof. exact (MK_COMB (@lem7644830) (@lem7644829)). Qed.
Lemma lem7644832 : term111 = term112.
Proof. exact (MK_COMB (@lem7644831) (@lem7644826)). Qed.
Lemma lem7644833 : term112 = term113.
Proof. exact (@lem1981613 term85 term61 term61 term61). Qed.
Lemma lem7644835 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7644836 : term94 = term95.
Proof. exact (@lem7644835 term12 term12). Qed.
Lemma lem7644837 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7644838 : term97 = term12.
Proof. exact (EQ_MP (@lem7644837) (@lem940073)). Qed.
Lemma lem7644839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7644840 : term95 = term61.
Proof. exact (MK_COMB (@lem7644839) (@lem7644838)). Qed.
Lemma lem7644841 : term94 = term61.
Proof. exact (TRANS (@lem7644836) (@lem7644840)). Qed.
Lemma lem7644843 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7644844 : term111 = term116.
Proof. exact (@lem7644843 term12 term12). Qed.
Lemma lem7644845 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7644846 : term97 = term12.
Proof. exact (EQ_MP (@lem7644845) (@lem940073)). Qed.
Lemma lem7644847 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7644848 : term95 = term61.
Proof. exact (MK_COMB (@lem7644847) (@lem7644846)). Qed.
Lemma lem7644849 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7644850 : term116 = term85.
Proof. exact (MK_COMB (@lem7644849) (@lem7644848)). Qed.
Lemma lem7644851 : term111 = term85.
Proof. exact (TRANS (@lem7644844) (@lem7644850)). Qed.
Lemma lem7644852 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7644853 : term117 = term118.
Proof. exact (MK_COMB (@lem7644852) (@lem7644851)). Qed.
Lemma lem7644854 : term113 = term86.
Proof. exact (MK_COMB (@lem7644853) (@lem7644841)). Qed.
Lemma lem7644855 : term112 = term86.
Proof. exact (TRANS (@lem7644833) (@lem7644854)). Qed.
Lemma lem7644856 : term111 = term86.
Proof. exact (TRANS (@lem7644832) (@lem7644855)). Qed.
Lemma lem7644858 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7644859 : term86 = term85.
Proof. exact (@lem7644858 term85). Qed.
Lemma lem7644860 : term111 = term85.
Proof. exact (TRANS (@lem7644856) (@lem7644859)). Qed.
Lemma lem7644861 (_98510 : int) : (term102 _98510) = (term102 _98510).
Proof. exact (eq_refl (term102 _98510)). Qed.
Lemma lem7644864 (_98510 : int) : (term109 _98510) = (term119 _98510).
Proof. exact (MK_COMB (@lem7644861 _98510) (@lem7644860)). Qed.
Lemma lem7644866 (_98510 : int) : (term108 _98510) = (term119 _98510).
Proof. exact (TRANS (@lem7644823 _98510) (@lem7644864 _98510)). Qed.
Lemma lem7644867 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7644868 (_98510 : int) : (term120 _98510) = (term121 _98510).
Proof. exact (MK_COMB (@lem7644867) (@lem7644866 _98510)). Qed.
Lemma lem7644869 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7644870 (_98510 : int) : (term107 _98510) = (term122 _98510).
Proof. exact (MK_COMB (@lem7644868 _98510) (@lem7644869)). Qed.
Lemma lem7644871 (_98510 : int) : (term64 _98510) = (term122 _98510).
Proof. exact (TRANS (@lem7644817 _98510) (@lem7644870 _98510)). Qed.
Lemma lem7644872 (_98509 : int) (_98510 : int) : (term49 _98510 _98509) = (term299 _98509 _98510).
Proof. exact (@lem1988287 (real_of_int _98509) (real_of_int _98510)). Qed.
Lemma lem7644885 (_98509 : int) (_98510 : int) : (term300 _98509 _98510) = (term301 _98509 _98510).
Proof. exact (@lem1982792 (real_of_int _98509) (real_of_int _98510)). Qed.
Lemma lem7644886 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7644887 (_98509 : int) (_98510 : int) : (term302 _98509 _98510) = (term303 _98509 _98510).
Proof. exact (MK_COMB (@lem7644886) (@lem7644885 _98509 _98510)). Qed.
Lemma lem7644888 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7644889 (_98509 : int) (_98510 : int) : (term299 _98509 _98510) = (term304 _98509 _98510).
Proof. exact (MK_COMB (@lem7644887 _98509 _98510) (@lem7644888)). Qed.
Lemma lem7644890 (_98509 : int) (_98510 : int) : (term49 _98510 _98509) = (term304 _98509 _98510).
Proof. exact (TRANS (@lem7644872 _98509 _98510) (@lem7644889 _98509 _98510)). Qed.
Lemma lem7644891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7644892 (_98510 : int) : (term71 _98510) = (term162 _98510).
Proof. exact (MK_COMB (@lem7644891) (@lem7644871 _98510)). Qed.
Lemma lem7644893 (_98509 : int) (_98510 : int) : (term272 _98510 _98509) = (term305 _98509 _98510).
Proof. exact (MK_COMB (@lem7644892 _98510) (@lem7644890 _98509 _98510)). Qed.
Lemma lem7644894 (_98508 : int) (_98510 : int) : (term285 _98508 _98510) = (term306 _98508 _98510).
Proof. exact (@lem1988287 term61 (term282 _98508 _98510)). Qed.
Lemma lem7644911 (_98508 : int) (_98510 : int) : (term282 _98508 _98510) = (term307 _98508 _98510).
Proof. exact (@lem1982755 (real_of_int _98508) (real_of_int _98510) term61). Qed.
Lemma lem7644914 : term308 = term308.
Proof. exact (eq_refl term308). Qed.
Lemma lem7644915 (_98508 : int) (_98510 : int) : (term309 _98508 _98510) = (term310 _98508 _98510).
Proof. exact (MK_COMB (@lem7644914) (@lem7644911 _98508 _98510)). Qed.
Lemma lem7644916 (_98508 : int) (_98510 : int) : (term310 _98508 _98510) = (term311 _98508 _98510).
Proof. exact (@lem1982792 term61 (term307 _98508 _98510)). Qed.
Lemma lem7644917 (_98508 : int) (_98510 : int) : (term312 _98508 _98510) = (term313 _98508 _98510).
Proof. exact (@lem1982781 (real_of_int _98508) term85 (term314 _98510)). Qed.
Lemma lem7644918 (_98510 : int) : (term315 _98510) = (term316 _98510).
Proof. exact (@lem1982781 (real_of_int _98510) term85 term61). Qed.
Lemma lem7644920 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7644921 : term61 = term110.
Proof. exact (@lem7644920 term12). Qed.
Lemma lem7644923 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7644924 : term85 = term86.
Proof. exact (@lem7644923 term12). Qed.
Lemma lem7644925 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7644926 : term87 = term88.
Proof. exact (MK_COMB (@lem7644925) (@lem7644924)). Qed.
Lemma lem7644927 : term111 = term112.
Proof. exact (MK_COMB (@lem7644926) (@lem7644921)). Qed.
Lemma lem7644928 : term112 = term113.
Proof. exact (@lem1981613 term85 term61 term61 term61). Qed.
Lemma lem7644930 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7644931 : term94 = term95.
Proof. exact (@lem7644930 term12 term12). Qed.
Lemma lem7644932 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7644933 : term97 = term12.
Proof. exact (EQ_MP (@lem7644932) (@lem940073)). Qed.
Lemma lem7644934 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7644935 : term95 = term61.
Proof. exact (MK_COMB (@lem7644934) (@lem7644933)). Qed.
Lemma lem7644936 : term94 = term61.
Proof. exact (TRANS (@lem7644931) (@lem7644935)). Qed.
Lemma lem7644938 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7644939 : term111 = term116.
Proof. exact (@lem7644938 term12 term12). Qed.
Lemma lem7644940 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7644941 : term97 = term12.
Proof. exact (EQ_MP (@lem7644940) (@lem940073)). Qed.
Lemma lem7644942 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7644943 : term95 = term61.
Proof. exact (MK_COMB (@lem7644942) (@lem7644941)). Qed.
Lemma lem7644944 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7644945 : term116 = term85.
Proof. exact (MK_COMB (@lem7644944) (@lem7644943)). Qed.
Lemma lem7644946 : term111 = term85.
Proof. exact (TRANS (@lem7644939) (@lem7644945)). Qed.
Lemma lem7644947 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7644948 : term117 = term118.
Proof. exact (MK_COMB (@lem7644947) (@lem7644946)). Qed.
Lemma lem7644949 : term113 = term86.
Proof. exact (MK_COMB (@lem7644948) (@lem7644936)). Qed.
Lemma lem7644950 : term112 = term86.
Proof. exact (TRANS (@lem7644928) (@lem7644949)). Qed.
Lemma lem7644951 : term111 = term86.
Proof. exact (TRANS (@lem7644927) (@lem7644950)). Qed.
Lemma lem7644953 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7644954 : term86 = term85.
Proof. exact (@lem7644953 term85). Qed.
Lemma lem7644955 : term111 = term85.
Proof. exact (TRANS (@lem7644951) (@lem7644954)). Qed.
Lemma lem7644958 (_98510 : int) : (term317 _98510) = (term317 _98510).
Proof. exact (eq_refl (term317 _98510)). Qed.
Lemma lem7644959 (_98510 : int) : (term316 _98510) = (term318 _98510).
Proof. exact (MK_COMB (@lem7644958 _98510) (@lem7644955)). Qed.
Lemma lem7644960 (_98510 : int) : (term315 _98510) = (term318 _98510).
Proof. exact (TRANS (@lem7644918 _98510) (@lem7644959 _98510)). Qed.
Lemma lem7644963 (_98508 : int) : (term317 _98508) = (term317 _98508).
Proof. exact (eq_refl (term317 _98508)). Qed.
Lemma lem7644964 (_98508 : int) (_98510 : int) : (term313 _98508 _98510) = (term319 _98508 _98510).
Proof. exact (MK_COMB (@lem7644963 _98508) (@lem7644960 _98510)). Qed.
Lemma lem7644965 (_98508 : int) (_98510 : int) : (term312 _98508 _98510) = (term319 _98508 _98510).
Proof. exact (TRANS (@lem7644917 _98508 _98510) (@lem7644964 _98508 _98510)). Qed.
Lemma lem7644966 : term320 = term320.
Proof. exact (eq_refl term320). Qed.
Lemma lem7644967 (_98508 : int) (_98510 : int) : (term311 _98508 _98510) = (term321 _98508 _98510).
Proof. exact (MK_COMB (@lem7644966) (@lem7644965 _98508 _98510)). Qed.
Lemma lem7644968 (_98508 : int) (_98510 : int) : (term321 _98508 _98510) = (term322 _98508 _98510).
Proof. exact (@lem1982757 (term130 _98508) term61 (term318 _98510)). Qed.
Lemma lem7644969 (_98510 : int) : (term323 _98510) = (term324 _98510).
Proof. exact (@lem1982757 (term130 _98510) term61 term85). Qed.
Lemma lem7644971 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7644972 : term85 = term86.
Proof. exact (@lem7644971 term12). Qed.
Lemma lem7644974 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7644975 : term61 = term110.
Proof. exact (@lem7644974 term12). Qed.
Lemma lem7644976 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7644977 : term320 = term325.
Proof. exact (MK_COMB (@lem7644976) (@lem7644975)). Qed.
Lemma lem7644978 : term326 = term327.
Proof. exact (MK_COMB (@lem7644977) (@lem7644972)). Qed.
Lemma lem7644979 : term328.
Proof. exact (@lem1981473 term61 term61 term85 term61 term54 term61). Qed.
Lemma lem7644981 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7644982 : term139 = term140.
Proof. exact (@lem7644981 (NUMERAL 0) term12). Qed.
Lemma lem7644983 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7644984 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7644985 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7644984 h1) (fun h1 : term140 = True => @lem7644983)). Qed.
Lemma lem7644986 : term140 = True.
Proof. exact (EQ_MP (@lem7644985) (@lem7644983)). Qed.
Lemma lem7644987 : term139 = True.
Proof. exact (TRANS (@lem7644982) (@lem7644986)). Qed.
Lemma lem7644988 : True = term139.
Proof. exact (SYM (@lem7644987)). Qed.
Lemma lem7644989 : term139.
Proof. exact (EQ_MP (@lem7644988) (@lem0)). Qed.
Lemma lem7644990 : term329.
Proof. exact (@lem7644979 (@lem7644989)). Qed.
Lemma lem7644992 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7644993 : term139 = term140.
Proof. exact (@lem7644992 (NUMERAL 0) term12). Qed.
Lemma lem7644994 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7644995 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7644996 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7644995 h1) (fun h1 : term140 = True => @lem7644994)). Qed.
Lemma lem7644997 : term140 = True.
Proof. exact (EQ_MP (@lem7644996) (@lem7644994)). Qed.
Lemma lem7644998 : term139 = True.
Proof. exact (TRANS (@lem7644993) (@lem7644997)). Qed.
Lemma lem7644999 : True = term139.
Proof. exact (SYM (@lem7644998)). Qed.
Lemma lem7645000 : term139.
Proof. exact (EQ_MP (@lem7644999) (@lem0)). Qed.
Lemma lem7645001 : term330.
Proof. exact (@lem7644990 (@lem7645000)). Qed.
Lemma lem7645003 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645004 : term139 = term140.
Proof. exact (@lem7645003 (NUMERAL 0) term12). Qed.
Lemma lem7645005 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645006 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645007 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645006 h1) (fun h1 : term140 = True => @lem7645005)). Qed.
Lemma lem7645008 : term140 = True.
Proof. exact (EQ_MP (@lem7645007) (@lem7645005)). Qed.
Lemma lem7645009 : term139 = True.
Proof. exact (TRANS (@lem7645004) (@lem7645008)). Qed.
Lemma lem7645010 : True = term139.
Proof. exact (SYM (@lem7645009)). Qed.
Lemma lem7645011 : term139.
Proof. exact (EQ_MP (@lem7645010) (@lem0)). Qed.
Lemma lem7645012 : term331.
Proof. exact (@lem7645001 (@lem7645011)). Qed.
Lemma lem7645014 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7645015 : term111 = term116.
Proof. exact (@lem7645014 term12 term12). Qed.
Lemma lem7645016 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645017 : term97 = term12.
Proof. exact (EQ_MP (@lem7645016) (@lem940073)). Qed.
Lemma lem7645018 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645019 : term95 = term61.
Proof. exact (MK_COMB (@lem7645018) (@lem7645017)). Qed.
Lemma lem7645020 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7645021 : term116 = term85.
Proof. exact (MK_COMB (@lem7645020) (@lem7645019)). Qed.
Lemma lem7645022 : term111 = term85.
Proof. exact (TRANS (@lem7645015) (@lem7645021)). Qed.
Lemma lem7645024 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645025 : term94 = term95.
Proof. exact (@lem7645024 term12 term12). Qed.
Lemma lem7645026 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645027 : term97 = term12.
Proof. exact (EQ_MP (@lem7645026) (@lem940073)). Qed.
Lemma lem7645028 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645029 : term95 = term61.
Proof. exact (MK_COMB (@lem7645028) (@lem7645027)). Qed.
Lemma lem7645030 : term94 = term61.
Proof. exact (TRANS (@lem7645025) (@lem7645029)). Qed.
Lemma lem7645031 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7645032 : term332 = term320.
Proof. exact (MK_COMB (@lem7645031) (@lem7645030)). Qed.
Lemma lem7645033 : term333 = term326.
Proof. exact (MK_COMB (@lem7645032) (@lem7645022)). Qed.
Lemma lem7645035 (m : nat) : (term334 m) = term54.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem7645036 : term326 = term54.
Proof. exact (@lem7645035 term12). Qed.
Lemma lem7645037 : term333 = term54.
Proof. exact (TRANS (@lem7645033) (@lem7645036)). Qed.
Lemma lem7645038 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7645039 : term335 = term149.
Proof. exact (MK_COMB (@lem7645038) (@lem7645037)). Qed.
Lemma lem7645040 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem7645041 : term336 = term151.
Proof. exact (MK_COMB (@lem7645039) (@lem7645040)). Qed.
Lemma lem7645043 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645044 : term151 = term54.
Proof. exact (@lem7645043 term12). Qed.
Lemma lem7645045 : term336 = term54.
Proof. exact (TRANS (@lem7645041) (@lem7645044)). Qed.
Lemma lem7645047 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645048 : term94 = term95.
Proof. exact (@lem7645047 term12 term12). Qed.
Lemma lem7645049 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645050 : term97 = term12.
Proof. exact (EQ_MP (@lem7645049) (@lem940073)). Qed.
Lemma lem7645051 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645052 : term95 = term61.
Proof. exact (MK_COMB (@lem7645051) (@lem7645050)). Qed.
Lemma lem7645053 : term94 = term61.
Proof. exact (TRANS (@lem7645048) (@lem7645052)). Qed.
Lemma lem7645054 : term149 = term149.
Proof. exact (eq_refl term149). Qed.
Lemma lem7645055 : term153 = term151.
Proof. exact (MK_COMB (@lem7645054) (@lem7645053)). Qed.
Lemma lem7645057 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645058 : term151 = term54.
Proof. exact (@lem7645057 term12). Qed.
Lemma lem7645059 : term153 = term54.
Proof. exact (TRANS (@lem7645055) (@lem7645058)). Qed.
Lemma lem7645060 : term54 = term153.
Proof. exact (SYM (@lem7645059)). Qed.
Lemma lem7645061 : term336 = term153.
Proof. exact (TRANS (@lem7645045) (@lem7645060)). Qed.
Lemma lem7645062 : term327 = term82.
Proof. exact (@lem7645012 (@lem7645061)). Qed.
Lemma lem7645063 : term326 = term82.
Proof. exact (TRANS (@lem7644978) (@lem7645062)). Qed.
Lemma lem7645065 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7645066 : term82 = term54.
Proof. exact (@lem7645065 term54). Qed.
Lemma lem7645067 : term326 = term54.
Proof. exact (TRANS (@lem7645063) (@lem7645066)). Qed.
Lemma lem7645068 (_98510 : int) : (term317 _98510) = (term317 _98510).
Proof. exact (eq_refl (term317 _98510)). Qed.
Lemma lem7645069 (_98510 : int) : (term324 _98510) = (term337 _98510).
Proof. exact (MK_COMB (@lem7645068 _98510) (@lem7645067)). Qed.
Lemma lem7645070 (_98510 : int) : (term323 _98510) = (term337 _98510).
Proof. exact (TRANS (@lem7644969 _98510) (@lem7645069 _98510)). Qed.
Lemma lem7645071 (_98510 : int) : (term337 _98510) = (term130 _98510).
Proof. exact (@lem1982723 (term130 _98510)). Qed.
Lemma lem7645072 (_98510 : int) : (term323 _98510) = (term130 _98510).
Proof. exact (TRANS (@lem7645070 _98510) (@lem7645071 _98510)). Qed.
Lemma lem7645073 (_98508 : int) : (term317 _98508) = (term317 _98508).
Proof. exact (eq_refl (term317 _98508)). Qed.
Lemma lem7645074 (_98508 : int) (_98510 : int) : (term322 _98508 _98510) = (term127 _98508 _98510).
Proof. exact (MK_COMB (@lem7645073 _98508) (@lem7645072 _98510)). Qed.
Lemma lem7645075 (_98508 : int) (_98510 : int) : (term321 _98508 _98510) = (term127 _98508 _98510).
Proof. exact (TRANS (@lem7644968 _98508 _98510) (@lem7645074 _98508 _98510)). Qed.
Lemma lem7645076 (_98508 : int) (_98510 : int) : (term311 _98508 _98510) = (term127 _98508 _98510).
Proof. exact (TRANS (@lem7644967 _98508 _98510) (@lem7645075 _98508 _98510)). Qed.
Lemma lem7645077 (_98508 : int) (_98510 : int) : (term310 _98508 _98510) = (term127 _98508 _98510).
Proof. exact (TRANS (@lem7644916 _98508 _98510) (@lem7645076 _98508 _98510)). Qed.
Lemma lem7645078 (_98508 : int) (_98510 : int) : (term309 _98508 _98510) = (term127 _98508 _98510).
Proof. exact (TRANS (@lem7644915 _98508 _98510) (@lem7645077 _98508 _98510)). Qed.
Lemma lem7645079 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7645080 (_98508 : int) (_98510 : int) : (term338 _98508 _98510) = (term339 _98508 _98510).
Proof. exact (MK_COMB (@lem7645079) (@lem7645078 _98508 _98510)). Qed.
Lemma lem7645081 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7645082 (_98508 : int) (_98510 : int) : (term306 _98508 _98510) = (term340 _98508 _98510).
Proof. exact (MK_COMB (@lem7645080 _98508 _98510) (@lem7645081)). Qed.
Lemma lem7645083 (_98508 : int) (_98510 : int) : (term285 _98508 _98510) = (term340 _98508 _98510).
Proof. exact (TRANS (@lem7644894 _98508 _98510) (@lem7645082 _98508 _98510)). Qed.
Lemma lem7645084 (_98510 : int) (_98508 : int) (_98509 : int) : (term289 _98509 _98508 _98510) = (term341 _98510 _98508 _98509).
Proof. exact (@lem1988287 (term67 _98508 _98510) (term282 _98508 _98509)). Qed.
Lemma lem7645101 (_98508 : int) (_98509 : int) : (term282 _98508 _98509) = (term307 _98508 _98509).
Proof. exact (@lem1982755 (real_of_int _98508) (real_of_int _98509) term61). Qed.
Lemma lem7645110 (_98508 : int) (_98510 : int) : (term342 _98508 _98510) = (term342 _98508 _98510).
Proof. exact (eq_refl (term342 _98508 _98510)). Qed.
Lemma lem7645111 (_98510 : int) (_98508 : int) (_98509 : int) : (term343 _98510 _98508 _98509) = (term344 _98510 _98508 _98509).
Proof. exact (MK_COMB (@lem7645110 _98508 _98510) (@lem7645101 _98508 _98509)). Qed.
Lemma lem7645112 (_98510 : int) (_98508 : int) (_98509 : int) : (term344 _98510 _98508 _98509) = (term345 _98510 _98508 _98509).
Proof. exact (@lem1982792 (term67 _98508 _98510) (term307 _98508 _98509)). Qed.
Lemma lem7645113 (_98508 : int) (_98509 : int) : (term312 _98508 _98509) = (term313 _98508 _98509).
Proof. exact (@lem1982781 (real_of_int _98508) term85 (term314 _98509)). Qed.
Lemma lem7645114 (_98509 : int) : (term315 _98509) = (term316 _98509).
Proof. exact (@lem1982781 (real_of_int _98509) term85 term61). Qed.
Lemma lem7645116 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645117 : term61 = term110.
Proof. exact (@lem7645116 term12). Qed.
Lemma lem7645119 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7645120 : term85 = term86.
Proof. exact (@lem7645119 term12). Qed.
Lemma lem7645121 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7645122 : term87 = term88.
Proof. exact (MK_COMB (@lem7645121) (@lem7645120)). Qed.
Lemma lem7645123 : term111 = term112.
Proof. exact (MK_COMB (@lem7645122) (@lem7645117)). Qed.
Lemma lem7645124 : term112 = term113.
Proof. exact (@lem1981613 term85 term61 term61 term61). Qed.
Lemma lem7645126 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645127 : term94 = term95.
Proof. exact (@lem7645126 term12 term12). Qed.
Lemma lem7645128 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645129 : term97 = term12.
Proof. exact (EQ_MP (@lem7645128) (@lem940073)). Qed.
Lemma lem7645130 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645131 : term95 = term61.
Proof. exact (MK_COMB (@lem7645130) (@lem7645129)). Qed.
Lemma lem7645132 : term94 = term61.
Proof. exact (TRANS (@lem7645127) (@lem7645131)). Qed.
Lemma lem7645134 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7645135 : term111 = term116.
Proof. exact (@lem7645134 term12 term12). Qed.
Lemma lem7645136 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645137 : term97 = term12.
Proof. exact (EQ_MP (@lem7645136) (@lem940073)). Qed.
Lemma lem7645138 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645139 : term95 = term61.
Proof. exact (MK_COMB (@lem7645138) (@lem7645137)). Qed.
Lemma lem7645140 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7645141 : term116 = term85.
Proof. exact (MK_COMB (@lem7645140) (@lem7645139)). Qed.
Lemma lem7645142 : term111 = term85.
Proof. exact (TRANS (@lem7645135) (@lem7645141)). Qed.
Lemma lem7645143 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7645144 : term117 = term118.
Proof. exact (MK_COMB (@lem7645143) (@lem7645142)). Qed.
Lemma lem7645145 : term113 = term86.
Proof. exact (MK_COMB (@lem7645144) (@lem7645132)). Qed.
Lemma lem7645146 : term112 = term86.
Proof. exact (TRANS (@lem7645124) (@lem7645145)). Qed.
Lemma lem7645147 : term111 = term86.
Proof. exact (TRANS (@lem7645123) (@lem7645146)). Qed.
Lemma lem7645149 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7645150 : term86 = term85.
Proof. exact (@lem7645149 term85). Qed.
Lemma lem7645151 : term111 = term85.
Proof. exact (TRANS (@lem7645147) (@lem7645150)). Qed.
Lemma lem7645154 (_98509 : int) : (term317 _98509) = (term317 _98509).
Proof. exact (eq_refl (term317 _98509)). Qed.
Lemma lem7645155 (_98509 : int) : (term316 _98509) = (term318 _98509).
Proof. exact (MK_COMB (@lem7645154 _98509) (@lem7645151)). Qed.
Lemma lem7645156 (_98509 : int) : (term315 _98509) = (term318 _98509).
Proof. exact (TRANS (@lem7645114 _98509) (@lem7645155 _98509)). Qed.
Lemma lem7645159 (_98508 : int) : (term317 _98508) = (term317 _98508).
Proof. exact (eq_refl (term317 _98508)). Qed.
Lemma lem7645160 (_98508 : int) (_98509 : int) : (term313 _98508 _98509) = (term319 _98508 _98509).
Proof. exact (MK_COMB (@lem7645159 _98508) (@lem7645156 _98509)). Qed.
Lemma lem7645161 (_98508 : int) (_98509 : int) : (term312 _98508 _98509) = (term319 _98508 _98509).
Proof. exact (TRANS (@lem7645113 _98508 _98509) (@lem7645160 _98508 _98509)). Qed.
Lemma lem7645162 (_98508 : int) (_98510 : int) : (term281 _98508 _98510) = (term281 _98508 _98510).
Proof. exact (eq_refl (term281 _98508 _98510)). Qed.
Lemma lem7645163 (_98510 : int) (_98508 : int) (_98509 : int) : (term345 _98510 _98508 _98509) = (term346 _98510 _98508 _98509).
Proof. exact (MK_COMB (@lem7645162 _98508 _98510) (@lem7645161 _98508 _98509)). Qed.
Lemma lem7645164 (_98508 : int) (_98510 : int) (_98509 : int) : (term346 _98510 _98508 _98509) = (term347 _98508 _98510 _98509).
Proof. exact (@lem1982753 (real_of_int _98508) (term130 _98508) (real_of_int _98510) (term318 _98509)). Qed.
Lemma lem7645165 (_98508 : int) : (term131 _98508) = (term132 _98508).
Proof. exact (@lem1982715 term85 (real_of_int _98508)). Qed.
Lemma lem7645167 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645168 : term61 = term110.
Proof. exact (@lem7645167 term12). Qed.
Lemma lem7645170 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7645171 : term85 = term86.
Proof. exact (@lem7645170 term12). Qed.
Lemma lem7645172 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7645173 : term133 = term134.
Proof. exact (MK_COMB (@lem7645172) (@lem7645171)). Qed.
Lemma lem7645174 : term135 = term136.
Proof. exact (MK_COMB (@lem7645173) (@lem7645168)). Qed.
Lemma lem7645175 : term137.
Proof. exact (@lem1981473 term85 term61 term61 term61 term54 term61). Qed.
Lemma lem7645177 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645178 : term139 = term140.
Proof. exact (@lem7645177 (NUMERAL 0) term12). Qed.
Lemma lem7645179 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645180 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645181 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645180 h1) (fun h1 : term140 = True => @lem7645179)). Qed.
Lemma lem7645182 : term140 = True.
Proof. exact (EQ_MP (@lem7645181) (@lem7645179)). Qed.
Lemma lem7645183 : term139 = True.
Proof. exact (TRANS (@lem7645178) (@lem7645182)). Qed.
Lemma lem7645184 : True = term139.
Proof. exact (SYM (@lem7645183)). Qed.
Lemma lem7645185 : term139.
Proof. exact (EQ_MP (@lem7645184) (@lem0)). Qed.
Lemma lem7645186 : term142.
Proof. exact (@lem7645175 (@lem7645185)). Qed.
Lemma lem7645188 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645189 : term139 = term140.
Proof. exact (@lem7645188 (NUMERAL 0) term12). Qed.
Lemma lem7645190 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645191 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645192 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645191 h1) (fun h1 : term140 = True => @lem7645190)). Qed.
Lemma lem7645193 : term140 = True.
Proof. exact (EQ_MP (@lem7645192) (@lem7645190)). Qed.
Lemma lem7645194 : term139 = True.
Proof. exact (TRANS (@lem7645189) (@lem7645193)). Qed.
Lemma lem7645195 : True = term139.
Proof. exact (SYM (@lem7645194)). Qed.
Lemma lem7645196 : term139.
Proof. exact (EQ_MP (@lem7645195) (@lem0)). Qed.
Lemma lem7645197 : term143.
Proof. exact (@lem7645186 (@lem7645196)). Qed.
Lemma lem7645199 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645200 : term139 = term140.
Proof. exact (@lem7645199 (NUMERAL 0) term12). Qed.
Lemma lem7645201 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645202 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645203 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645202 h1) (fun h1 : term140 = True => @lem7645201)). Qed.
Lemma lem7645204 : term140 = True.
Proof. exact (EQ_MP (@lem7645203) (@lem7645201)). Qed.
Lemma lem7645205 : term139 = True.
Proof. exact (TRANS (@lem7645200) (@lem7645204)). Qed.
Lemma lem7645206 : True = term139.
Proof. exact (SYM (@lem7645205)). Qed.
Lemma lem7645207 : term139.
Proof. exact (EQ_MP (@lem7645206) (@lem0)). Qed.
Lemma lem7645208 : term144.
Proof. exact (@lem7645197 (@lem7645207)). Qed.
Lemma lem7645210 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645211 : term94 = term95.
Proof. exact (@lem7645210 term12 term12). Qed.
Lemma lem7645212 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645213 : term97 = term12.
Proof. exact (EQ_MP (@lem7645212) (@lem940073)). Qed.
Lemma lem7645214 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645215 : term95 = term61.
Proof. exact (MK_COMB (@lem7645214) (@lem7645213)). Qed.
Lemma lem7645216 : term94 = term61.
Proof. exact (TRANS (@lem7645211) (@lem7645215)). Qed.
Lemma lem7645218 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7645219 : term111 = term116.
Proof. exact (@lem7645218 term12 term12). Qed.
Lemma lem7645220 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645221 : term97 = term12.
Proof. exact (EQ_MP (@lem7645220) (@lem940073)). Qed.
Lemma lem7645222 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645223 : term95 = term61.
Proof. exact (MK_COMB (@lem7645222) (@lem7645221)). Qed.
Lemma lem7645224 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7645225 : term116 = term85.
Proof. exact (MK_COMB (@lem7645224) (@lem7645223)). Qed.
Lemma lem7645226 : term111 = term85.
Proof. exact (TRANS (@lem7645219) (@lem7645225)). Qed.
Lemma lem7645227 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7645228 : term145 = term133.
Proof. exact (MK_COMB (@lem7645227) (@lem7645226)). Qed.
Lemma lem7645229 : term146 = term135.
Proof. exact (MK_COMB (@lem7645228) (@lem7645216)). Qed.
Lemma lem7645231 (m : nat) : (term147 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7645232 : term135 = term54.
Proof. exact (@lem7645231 term12). Qed.
Lemma lem7645233 : term146 = term54.
Proof. exact (TRANS (@lem7645229) (@lem7645232)). Qed.
Lemma lem7645234 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7645235 : term148 = term149.
Proof. exact (MK_COMB (@lem7645234) (@lem7645233)). Qed.
Lemma lem7645236 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem7645237 : term150 = term151.
Proof. exact (MK_COMB (@lem7645235) (@lem7645236)). Qed.
Lemma lem7645239 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645240 : term151 = term54.
Proof. exact (@lem7645239 term12). Qed.
Lemma lem7645241 : term150 = term54.
Proof. exact (TRANS (@lem7645237) (@lem7645240)). Qed.
Lemma lem7645243 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645244 : term94 = term95.
Proof. exact (@lem7645243 term12 term12). Qed.
Lemma lem7645245 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645246 : term97 = term12.
Proof. exact (EQ_MP (@lem7645245) (@lem940073)). Qed.
Lemma lem7645247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645248 : term95 = term61.
Proof. exact (MK_COMB (@lem7645247) (@lem7645246)). Qed.
Lemma lem7645249 : term94 = term61.
Proof. exact (TRANS (@lem7645244) (@lem7645248)). Qed.
Lemma lem7645250 : term149 = term149.
Proof. exact (eq_refl term149). Qed.
Lemma lem7645251 : term153 = term151.
Proof. exact (MK_COMB (@lem7645250) (@lem7645249)). Qed.
Lemma lem7645253 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645254 : term151 = term54.
Proof. exact (@lem7645253 term12). Qed.
Lemma lem7645255 : term153 = term54.
Proof. exact (TRANS (@lem7645251) (@lem7645254)). Qed.
Lemma lem7645256 : term54 = term153.
Proof. exact (SYM (@lem7645255)). Qed.
Lemma lem7645257 : term150 = term153.
Proof. exact (TRANS (@lem7645241) (@lem7645256)). Qed.
Lemma lem7645258 : term136 = term82.
Proof. exact (@lem7645208 (@lem7645257)). Qed.
Lemma lem7645259 : term135 = term82.
Proof. exact (TRANS (@lem7645174) (@lem7645258)). Qed.
Lemma lem7645261 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7645262 : term82 = term54.
Proof. exact (@lem7645261 term54). Qed.
Lemma lem7645263 : term135 = term54.
Proof. exact (TRANS (@lem7645259) (@lem7645262)). Qed.
Lemma lem7645264 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7645265 : term154 = term149.
Proof. exact (MK_COMB (@lem7645264) (@lem7645263)). Qed.
Lemma lem7645266 (_98508 : int) : (real_of_int _98508) = (real_of_int _98508).
Proof. exact (eq_refl (real_of_int _98508)). Qed.
Lemma lem7645267 (_98508 : int) : (term132 _98508) = (term155 _98508).
Proof. exact (MK_COMB (@lem7645265) (@lem7645266 _98508)). Qed.
Lemma lem7645268 (_98508 : int) : (term131 _98508) = (term155 _98508).
Proof. exact (TRANS (@lem7645165 _98508) (@lem7645267 _98508)). Qed.
Lemma lem7645269 (_98508 : int) : (term155 _98508) = term54.
Proof. exact (@lem1982719 (real_of_int _98508)). Qed.
Lemma lem7645270 (_98508 : int) : (term131 _98508) = term54.
Proof. exact (TRANS (@lem7645268 _98508) (@lem7645269 _98508)). Qed.
Lemma lem7645271 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7645272 (_98508 : int) : (term156 _98508) = term157.
Proof. exact (MK_COMB (@lem7645271) (@lem7645270 _98508)). Qed.
Lemma lem7645277 (_98509 : int) (_98510 : int) : (term348 _98510 _98509) = (term349 _98509 _98510).
Proof. exact (@lem1982757 (term130 _98509) (real_of_int _98510) term85). Qed.
Lemma lem7645278 (_98508 : int) (_98509 : int) (_98510 : int) : (term347 _98508 _98510 _98509) = (term350 _98509 _98510).
Proof. exact (MK_COMB (@lem7645272 _98508) (@lem7645277 _98509 _98510)). Qed.
Lemma lem7645279 (_98508 : int) (_98509 : int) (_98510 : int) : (term346 _98510 _98508 _98509) = (term350 _98509 _98510).
Proof. exact (TRANS (@lem7645164 _98508 _98510 _98509) (@lem7645278 _98508 _98509 _98510)). Qed.
Lemma lem7645280 (_98509 : int) (_98510 : int) : (term350 _98509 _98510) = (term349 _98509 _98510).
Proof. exact (@lem1982721 (term349 _98509 _98510)). Qed.
Lemma lem7645281 (_98508 : int) (_98509 : int) (_98510 : int) : (term346 _98510 _98508 _98509) = (term349 _98509 _98510).
Proof. exact (TRANS (@lem7645279 _98508 _98509 _98510) (@lem7645280 _98509 _98510)). Qed.
Lemma lem7645282 (_98508 : int) (_98509 : int) (_98510 : int) : (term345 _98510 _98508 _98509) = (term349 _98509 _98510).
Proof. exact (TRANS (@lem7645163 _98510 _98508 _98509) (@lem7645281 _98508 _98509 _98510)). Qed.
Lemma lem7645283 (_98508 : int) (_98509 : int) (_98510 : int) : (term344 _98510 _98508 _98509) = (term349 _98509 _98510).
Proof. exact (TRANS (@lem7645112 _98510 _98508 _98509) (@lem7645282 _98508 _98509 _98510)). Qed.
Lemma lem7645284 (_98508 : int) (_98509 : int) (_98510 : int) : (term343 _98510 _98508 _98509) = (term349 _98509 _98510).
Proof. exact (TRANS (@lem7645111 _98510 _98508 _98509) (@lem7645283 _98508 _98509 _98510)). Qed.
Lemma lem7645285 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7645286 (_98508 : int) (_98509 : int) (_98510 : int) : (term351 _98510 _98508 _98509) = (term352 _98509 _98510).
Proof. exact (MK_COMB (@lem7645285) (@lem7645284 _98508 _98509 _98510)). Qed.
Lemma lem7645287 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7645288 (_98508 : int) (_98509 : int) (_98510 : int) : (term341 _98510 _98508 _98509) = (term353 _98509 _98510).
Proof. exact (MK_COMB (@lem7645286 _98508 _98509 _98510) (@lem7645287)). Qed.
Lemma lem7645289 (_98508 : int) (_98509 : int) (_98510 : int) : (term289 _98509 _98508 _98510) = (term353 _98509 _98510).
Proof. exact (TRANS (@lem7645084 _98510 _98508 _98509) (@lem7645288 _98508 _98509 _98510)). Qed.
Lemma lem7645290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7645291 (_98508 : int) (_98510 : int) : (term291 _98508 _98510) = (term354 _98508 _98510).
Proof. exact (MK_COMB (@lem7645290) (@lem7645083 _98508 _98510)). Qed.
Lemma lem7645292 (_98508 : int) (_98509 : int) (_98510 : int) : (term292 _98509 _98508 _98510) = (term355 _98508 _98509 _98510).
Proof. exact (MK_COMB (@lem7645291 _98508 _98510) (@lem7645289 _98508 _98509 _98510)). Qed.
Lemma lem7645293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7645294 (_98509 : int) (_98510 : int) : (term293 _98510 _98509) = (term356 _98509 _98510).
Proof. exact (MK_COMB (@lem7645293) (@lem7644893 _98509 _98510)). Qed.
Lemma lem7645295 (_98508 : int) (_98509 : int) (_98510 : int) : (term294 _98509 _98508 _98510) = (term357 _98508 _98509 _98510).
Proof. exact (MK_COMB (@lem7645294 _98509 _98510) (@lem7645292 _98508 _98509 _98510)). Qed.
Lemma lem7645296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7645297 (_98510 : int) : (term73 _98510) = (term164 _98510).
Proof. exact (MK_COMB (@lem7645296) (@lem7644816 _98510)). Qed.
Lemma lem7645298 (_98508 : int) (_98509 : int) (_98510 : int) : (term295 _98509 _98508 _98510) = (term358 _98508 _98509 _98510).
Proof. exact (MK_COMB (@lem7645297 _98510) (@lem7645295 _98508 _98509 _98510)). Qed.
Lemma lem7645299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7645300 (_98509 : int) : (term73 _98509) = (term164 _98509).
Proof. exact (MK_COMB (@lem7645299) (@lem7644768 _98509)). Qed.
Lemma lem7645301 (_98508 : int) (_98509 : int) (_98510 : int) : (term296 _98509 _98508 _98510) = (term359 _98508 _98509 _98510).
Proof. exact (MK_COMB (@lem7645300 _98509) (@lem7645298 _98508 _98509 _98510)). Qed.
Lemma lem7645302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7645303 (_98508 : int) : (term73 _98508) = (term164 _98508).
Proof. exact (MK_COMB (@lem7645302) (@lem7644720 _98508)). Qed.
Lemma lem7645304 (_98508 : int) (_98509 : int) (_98510 : int) : (term297 _98509 _98508 _98510) = (term360 _98508 _98509 _98510).
Proof. exact (MK_COMB (@lem7645303 _98508) (@lem7645301 _98508 _98509 _98510)). Qed.
Lemma lem7645311 (_98508 : int) (_98509 : int) (_98510 : int) : (term298 _98509 _98508 _98510) = (term360 _98508 _98509 _98510).
Proof. exact (TRANS (@lem7644672 _98509 _98508 _98510) (@lem7645304 _98508 _98509 _98510)). Qed.
Lemma lem7645334 (_98508 : int) (_98509 : int) (_98510 : int) : (term357 _98508 _98509 _98510) = (term361 _98508 _98509 _98510).
Proof. exact (@lem19158 (term340 _98508 _98510) (term305 _98509 _98510) (term353 _98509 _98510)). Qed.
Lemma lem7645337 (_98510 : int) : (term164 _98510) = (term164 _98510).
Proof. exact (eq_refl (term164 _98510)). Qed.
Lemma lem7645338 (_98508 : int) (_98509 : int) (_98510 : int) : (term358 _98508 _98509 _98510) = (term362 _98508 _98509 _98510).
Proof. exact (MK_COMB (@lem7645337 _98510) (@lem7645334 _98508 _98509 _98510)). Qed.
Lemma lem7645345 (_98508 : int) (_98509 : int) (_98510 : int) : (term362 _98508 _98509 _98510) = (term363 _98508 _98509 _98510).
Proof. exact (@lem19158 (term364 _98509 _98508 _98510) (term106 _98510) (term365 _98509 _98510)). Qed.
Lemma lem7645346 (_98508 : int) (_98509 : int) (_98510 : int) : (term358 _98508 _98509 _98510) = (term363 _98508 _98509 _98510).
Proof. exact (TRANS (@lem7645338 _98508 _98509 _98510) (@lem7645345 _98508 _98509 _98510)). Qed.
Lemma lem7645349 (_98509 : int) : (term164 _98509) = (term164 _98509).
Proof. exact (eq_refl (term164 _98509)). Qed.
Lemma lem7645350 (_98508 : int) (_98509 : int) (_98510 : int) : (term359 _98508 _98509 _98510) = (term366 _98508 _98509 _98510).
Proof. exact (MK_COMB (@lem7645349 _98509) (@lem7645346 _98508 _98509 _98510)). Qed.
Lemma lem7645357 (_98508 : int) (_98509 : int) (_98510 : int) : (term366 _98508 _98509 _98510) = (term367 _98508 _98509 _98510).
Proof. exact (@lem19158 (term368 _98509 _98508 _98510) (term106 _98509) (term369 _98509 _98510)). Qed.
Lemma lem7645358 (_98508 : int) (_98509 : int) (_98510 : int) : (term359 _98508 _98509 _98510) = (term367 _98508 _98509 _98510).
Proof. exact (TRANS (@lem7645350 _98508 _98509 _98510) (@lem7645357 _98508 _98509 _98510)). Qed.
Lemma lem7645361 (_98508 : int) : (term164 _98508) = (term164 _98508).
Proof. exact (eq_refl (term164 _98508)). Qed.
Lemma lem7645362 (_98508 : int) (_98509 : int) (_98510 : int) : (term360 _98508 _98509 _98510) = (term370 _98508 _98509 _98510).
Proof. exact (MK_COMB (@lem7645361 _98508) (@lem7645358 _98508 _98509 _98510)). Qed.
Lemma lem7645369 (_98508 : int) (_98509 : int) (_98510 : int) : (term370 _98508 _98509 _98510) = (term371 _98508 _98509 _98510).
Proof. exact (@lem19158 (term372 _98509 _98508 _98510) (term106 _98508) (term373 _98509 _98510)). Qed.
Lemma lem7645370 (_98508 : int) (_98509 : int) (_98510 : int) : (term360 _98508 _98509 _98510) = (term371 _98508 _98509 _98510).
Proof. exact (TRANS (@lem7645362 _98508 _98509 _98510) (@lem7645369 _98508 _98509 _98510)). Qed.
Lemma lem7645371 (_98508 : int) (_98509 : int) (_98510 : int) : (term298 _98509 _98508 _98510) = (term371 _98508 _98509 _98510).
Proof. exact (TRANS (@lem7645311 _98508 _98509 _98510) (@lem7645370 _98508 _98509 _98510)). Qed.
Lemma lem7645381 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term371 _98508 _98509 _98510) : term371 _98508 _98509 _98510.
Proof. exact (h1). Qed.
Lemma lem7645382 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term374 _98509 _98508 _98510.
Proof. exact (h1). Qed.
Lemma lem7645383 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term372 _98509 _98508 _98510.
Proof. exact (proj2 (@lem7645382 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645384 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term106 _98508.
Proof. exact (proj1 (@lem7645382 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645385 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term368 _98509 _98508 _98510.
Proof. exact (proj2 (@lem7645383 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645387 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term364 _98509 _98508 _98510.
Proof. exact (proj2 (@lem7645385 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645389 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term340 _98508 _98510.
Proof. exact (proj2 (@lem7645387 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645390 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term305 _98509 _98510.
Proof. exact (proj1 (@lem7645387 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645392 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term122 _98510.
Proof. exact (proj1 (@lem7645390 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645394 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7645395 : term167 = term139.
Proof. exact (@lem7645394 term54 term61). Qed.
Lemma lem7645397 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645398 : term61 = term110.
Proof. exact (@lem7645397 term12). Qed.
Lemma lem7645400 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645401 : term54 = term82.
Proof. exact (@lem7645400 (NUMERAL 0)). Qed.
Lemma lem7645402 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7645403 : term168 = term169.
Proof. exact (MK_COMB (@lem7645402) (@lem7645401)). Qed.
Lemma lem7645404 : term139 = term170.
Proof. exact (MK_COMB (@lem7645403) (@lem7645398)). Qed.
Lemma lem7645405 : term171.
Proof. exact (@lem1980255 term54 term61 term61 term61). Qed.
Lemma lem7645407 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645408 : term139 = term140.
Proof. exact (@lem7645407 (NUMERAL 0) term12). Qed.
Lemma lem7645409 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645410 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645411 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645410 h1) (fun h1 : term140 = True => @lem7645409)). Qed.
Lemma lem7645412 : term140 = True.
Proof. exact (EQ_MP (@lem7645411) (@lem7645409)). Qed.
Lemma lem7645413 : term139 = True.
Proof. exact (TRANS (@lem7645408) (@lem7645412)). Qed.
Lemma lem7645414 : True = term139.
Proof. exact (SYM (@lem7645413)). Qed.
Lemma lem7645415 : term139.
Proof. exact (EQ_MP (@lem7645414) (@lem0)). Qed.
Lemma lem7645416 : term172.
Proof. exact (@lem7645405 (@lem7645415)). Qed.
Lemma lem7645418 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645419 : term139 = term140.
Proof. exact (@lem7645418 (NUMERAL 0) term12). Qed.
Lemma lem7645420 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645421 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645422 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645421 h1) (fun h1 : term140 = True => @lem7645420)). Qed.
Lemma lem7645423 : term140 = True.
Proof. exact (EQ_MP (@lem7645422) (@lem7645420)). Qed.
Lemma lem7645424 : term139 = True.
Proof. exact (TRANS (@lem7645419) (@lem7645423)). Qed.
Lemma lem7645425 : True = term139.
Proof. exact (SYM (@lem7645424)). Qed.
Lemma lem7645426 : term139.
Proof. exact (EQ_MP (@lem7645425) (@lem0)). Qed.
Lemma lem7645427 : term170 = term173.
Proof. exact (@lem7645416 (@lem7645426)). Qed.
Lemma lem7645429 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645430 : term94 = term95.
Proof. exact (@lem7645429 term12 term12). Qed.
Lemma lem7645431 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645432 : term97 = term12.
Proof. exact (EQ_MP (@lem7645431) (@lem940073)). Qed.
Lemma lem7645433 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645434 : term95 = term61.
Proof. exact (MK_COMB (@lem7645433) (@lem7645432)). Qed.
Lemma lem7645435 : term94 = term61.
Proof. exact (TRANS (@lem7645430) (@lem7645434)). Qed.
Lemma lem7645437 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645438 : term151 = term54.
Proof. exact (@lem7645437 term12). Qed.
Lemma lem7645439 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7645440 : term174 = term168.
Proof. exact (MK_COMB (@lem7645439) (@lem7645438)). Qed.
Lemma lem7645441 : term173 = term139.
Proof. exact (MK_COMB (@lem7645440) (@lem7645435)). Qed.
Lemma lem7645443 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645444 : term139 = term140.
Proof. exact (@lem7645443 (NUMERAL 0) term12). Qed.
Lemma lem7645445 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645446 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645447 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645446 h1) (fun h1 : term140 = True => @lem7645445)). Qed.
Lemma lem7645448 : term140 = True.
Proof. exact (EQ_MP (@lem7645447) (@lem7645445)). Qed.
Lemma lem7645449 : term139 = True.
Proof. exact (TRANS (@lem7645444) (@lem7645448)). Qed.
Lemma lem7645450 : term173 = True.
Proof. exact (TRANS (@lem7645441) (@lem7645449)). Qed.
Lemma lem7645451 : term170 = True.
Proof. exact (TRANS (@lem7645427) (@lem7645450)). Qed.
Lemma lem7645452 : term139 = True.
Proof. exact (TRANS (@lem7645404) (@lem7645451)). Qed.
Lemma lem7645453 : term167 = True.
Proof. exact (TRANS (@lem7645395) (@lem7645452)). Qed.
Lemma lem7645454 : True = term167.
Proof. exact (SYM (@lem7645453)). Qed.
Lemma lem7645455 : term167.
Proof. exact (EQ_MP (@lem7645454) (@lem0)). Qed.
Lemma lem7645456 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term175 _98510.
Proof. exact (conj (@lem7645455) (@lem7645392 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645458 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7645459 (_98510 : int) : term177 _98510.
Proof. exact (@lem7645458 term61 (term119 _98510)). Qed.
Lemma lem7645460 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term178 _98510.
Proof. exact (@lem7645459 _98510 (@lem7645456 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645461 (_98510 : int) : (term179 _98510) = (term119 _98510).
Proof. exact (@lem1982733 (term119 _98510)). Qed.
Lemma lem7645462 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7645463 (_98510 : int) : (term180 _98510) = (term121 _98510).
Proof. exact (MK_COMB (@lem7645462) (@lem7645461 _98510)). Qed.
Lemma lem7645464 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7645465 (_98510 : int) : (term178 _98510) = (term122 _98510).
Proof. exact (MK_COMB (@lem7645463 _98510) (@lem7645464)). Qed.
Lemma lem7645466 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term122 _98510.
Proof. exact (EQ_MP (@lem7645465 _98510) (@lem7645460 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645468 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7645469 : term167 = term139.
Proof. exact (@lem7645468 term54 term61). Qed.
Lemma lem7645471 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645472 : term61 = term110.
Proof. exact (@lem7645471 term12). Qed.
Lemma lem7645474 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645475 : term54 = term82.
Proof. exact (@lem7645474 (NUMERAL 0)). Qed.
Lemma lem7645476 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7645477 : term168 = term169.
Proof. exact (MK_COMB (@lem7645476) (@lem7645475)). Qed.
Lemma lem7645478 : term139 = term170.
Proof. exact (MK_COMB (@lem7645477) (@lem7645472)). Qed.
Lemma lem7645479 : term171.
Proof. exact (@lem1980255 term54 term61 term61 term61). Qed.
Lemma lem7645481 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645482 : term139 = term140.
Proof. exact (@lem7645481 (NUMERAL 0) term12). Qed.
Lemma lem7645483 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645484 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645485 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645484 h1) (fun h1 : term140 = True => @lem7645483)). Qed.
Lemma lem7645486 : term140 = True.
Proof. exact (EQ_MP (@lem7645485) (@lem7645483)). Qed.
Lemma lem7645487 : term139 = True.
Proof. exact (TRANS (@lem7645482) (@lem7645486)). Qed.
Lemma lem7645488 : True = term139.
Proof. exact (SYM (@lem7645487)). Qed.
Lemma lem7645489 : term139.
Proof. exact (EQ_MP (@lem7645488) (@lem0)). Qed.
Lemma lem7645490 : term172.
Proof. exact (@lem7645479 (@lem7645489)). Qed.
Lemma lem7645492 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645493 : term139 = term140.
Proof. exact (@lem7645492 (NUMERAL 0) term12). Qed.
Lemma lem7645494 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645495 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645496 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645495 h1) (fun h1 : term140 = True => @lem7645494)). Qed.
Lemma lem7645497 : term140 = True.
Proof. exact (EQ_MP (@lem7645496) (@lem7645494)). Qed.
Lemma lem7645498 : term139 = True.
Proof. exact (TRANS (@lem7645493) (@lem7645497)). Qed.
Lemma lem7645499 : True = term139.
Proof. exact (SYM (@lem7645498)). Qed.
Lemma lem7645500 : term139.
Proof. exact (EQ_MP (@lem7645499) (@lem0)). Qed.
Lemma lem7645501 : term170 = term173.
Proof. exact (@lem7645490 (@lem7645500)). Qed.
Lemma lem7645503 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645504 : term94 = term95.
Proof. exact (@lem7645503 term12 term12). Qed.
Lemma lem7645505 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645506 : term97 = term12.
Proof. exact (EQ_MP (@lem7645505) (@lem940073)). Qed.
Lemma lem7645507 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645508 : term95 = term61.
Proof. exact (MK_COMB (@lem7645507) (@lem7645506)). Qed.
Lemma lem7645509 : term94 = term61.
Proof. exact (TRANS (@lem7645504) (@lem7645508)). Qed.
Lemma lem7645511 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645512 : term151 = term54.
Proof. exact (@lem7645511 term12). Qed.
Lemma lem7645513 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7645514 : term174 = term168.
Proof. exact (MK_COMB (@lem7645513) (@lem7645512)). Qed.
Lemma lem7645515 : term173 = term139.
Proof. exact (MK_COMB (@lem7645514) (@lem7645509)). Qed.
Lemma lem7645517 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645518 : term139 = term140.
Proof. exact (@lem7645517 (NUMERAL 0) term12). Qed.
Lemma lem7645519 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645520 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645521 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645520 h1) (fun h1 : term140 = True => @lem7645519)). Qed.
Lemma lem7645522 : term140 = True.
Proof. exact (EQ_MP (@lem7645521) (@lem7645519)). Qed.
Lemma lem7645523 : term139 = True.
Proof. exact (TRANS (@lem7645518) (@lem7645522)). Qed.
Lemma lem7645524 : term173 = True.
Proof. exact (TRANS (@lem7645515) (@lem7645523)). Qed.
Lemma lem7645525 : term170 = True.
Proof. exact (TRANS (@lem7645501) (@lem7645524)). Qed.
Lemma lem7645526 : term139 = True.
Proof. exact (TRANS (@lem7645478) (@lem7645525)). Qed.
Lemma lem7645527 : term167 = True.
Proof. exact (TRANS (@lem7645469) (@lem7645526)). Qed.
Lemma lem7645528 : True = term167.
Proof. exact (SYM (@lem7645527)). Qed.
Lemma lem7645529 : term167.
Proof. exact (EQ_MP (@lem7645528) (@lem0)). Qed.
Lemma lem7645530 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term375 _98508.
Proof. exact (conj (@lem7645529) (@lem7645384 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645532 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7645533 (_98508 : int) : term376 _98508.
Proof. exact (@lem7645532 term61 (real_of_int _98508)). Qed.
Lemma lem7645534 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term377 _98508.
Proof. exact (@lem7645533 _98508 (@lem7645530 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645535 (_98508 : int) : (term378 _98508) = (real_of_int _98508).
Proof. exact (@lem1982733 (real_of_int _98508)). Qed.
Lemma lem7645536 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7645537 (_98508 : int) : (term379 _98508) = (term105 _98508).
Proof. exact (MK_COMB (@lem7645536) (@lem7645535 _98508)). Qed.
Lemma lem7645538 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7645539 (_98508 : int) : (term377 _98508) = (term106 _98508).
Proof. exact (MK_COMB (@lem7645537 _98508) (@lem7645538)). Qed.
Lemma lem7645540 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term106 _98508.
Proof. exact (EQ_MP (@lem7645539 _98508) (@lem7645534 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645542 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7645543 : term167 = term139.
Proof. exact (@lem7645542 term54 term61). Qed.
Lemma lem7645545 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645546 : term61 = term110.
Proof. exact (@lem7645545 term12). Qed.
Lemma lem7645548 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645549 : term54 = term82.
Proof. exact (@lem7645548 (NUMERAL 0)). Qed.
Lemma lem7645550 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7645551 : term168 = term169.
Proof. exact (MK_COMB (@lem7645550) (@lem7645549)). Qed.
Lemma lem7645552 : term139 = term170.
Proof. exact (MK_COMB (@lem7645551) (@lem7645546)). Qed.
Lemma lem7645553 : term171.
Proof. exact (@lem1980255 term54 term61 term61 term61). Qed.
Lemma lem7645555 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645556 : term139 = term140.
Proof. exact (@lem7645555 (NUMERAL 0) term12). Qed.
Lemma lem7645557 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645558 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645559 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645558 h1) (fun h1 : term140 = True => @lem7645557)). Qed.
Lemma lem7645560 : term140 = True.
Proof. exact (EQ_MP (@lem7645559) (@lem7645557)). Qed.
Lemma lem7645561 : term139 = True.
Proof. exact (TRANS (@lem7645556) (@lem7645560)). Qed.
Lemma lem7645562 : True = term139.
Proof. exact (SYM (@lem7645561)). Qed.
Lemma lem7645563 : term139.
Proof. exact (EQ_MP (@lem7645562) (@lem0)). Qed.
Lemma lem7645564 : term172.
Proof. exact (@lem7645553 (@lem7645563)). Qed.
Lemma lem7645566 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645567 : term139 = term140.
Proof. exact (@lem7645566 (NUMERAL 0) term12). Qed.
Lemma lem7645568 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645569 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645570 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645569 h1) (fun h1 : term140 = True => @lem7645568)). Qed.
Lemma lem7645571 : term140 = True.
Proof. exact (EQ_MP (@lem7645570) (@lem7645568)). Qed.
Lemma lem7645572 : term139 = True.
Proof. exact (TRANS (@lem7645567) (@lem7645571)). Qed.
Lemma lem7645573 : True = term139.
Proof. exact (SYM (@lem7645572)). Qed.
Lemma lem7645574 : term139.
Proof. exact (EQ_MP (@lem7645573) (@lem0)). Qed.
Lemma lem7645575 : term170 = term173.
Proof. exact (@lem7645564 (@lem7645574)). Qed.
Lemma lem7645577 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645578 : term94 = term95.
Proof. exact (@lem7645577 term12 term12). Qed.
Lemma lem7645579 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645580 : term97 = term12.
Proof. exact (EQ_MP (@lem7645579) (@lem940073)). Qed.
Lemma lem7645581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645582 : term95 = term61.
Proof. exact (MK_COMB (@lem7645581) (@lem7645580)). Qed.
Lemma lem7645583 : term94 = term61.
Proof. exact (TRANS (@lem7645578) (@lem7645582)). Qed.
Lemma lem7645585 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645586 : term151 = term54.
Proof. exact (@lem7645585 term12). Qed.
Lemma lem7645587 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7645588 : term174 = term168.
Proof. exact (MK_COMB (@lem7645587) (@lem7645586)). Qed.
Lemma lem7645589 : term173 = term139.
Proof. exact (MK_COMB (@lem7645588) (@lem7645583)). Qed.
Lemma lem7645591 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645592 : term139 = term140.
Proof. exact (@lem7645591 (NUMERAL 0) term12). Qed.
Lemma lem7645593 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645594 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645595 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645594 h1) (fun h1 : term140 = True => @lem7645593)). Qed.
Lemma lem7645596 : term140 = True.
Proof. exact (EQ_MP (@lem7645595) (@lem7645593)). Qed.
Lemma lem7645597 : term139 = True.
Proof. exact (TRANS (@lem7645592) (@lem7645596)). Qed.
Lemma lem7645598 : term173 = True.
Proof. exact (TRANS (@lem7645589) (@lem7645597)). Qed.
Lemma lem7645599 : term170 = True.
Proof. exact (TRANS (@lem7645575) (@lem7645598)). Qed.
Lemma lem7645600 : term139 = True.
Proof. exact (TRANS (@lem7645552) (@lem7645599)). Qed.
Lemma lem7645601 : term167 = True.
Proof. exact (TRANS (@lem7645543) (@lem7645600)). Qed.
Lemma lem7645602 : True = term167.
Proof. exact (SYM (@lem7645601)). Qed.
Lemma lem7645603 : term167.
Proof. exact (EQ_MP (@lem7645602) (@lem0)). Qed.
Lemma lem7645604 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term380 _98508 _98510.
Proof. exact (conj (@lem7645603) (@lem7645389 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645606 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7645607 (_98508 : int) (_98510 : int) : term381 _98508 _98510.
Proof. exact (@lem7645606 term61 (term127 _98508 _98510)). Qed.
Lemma lem7645608 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term382 _98508 _98510.
Proof. exact (@lem7645607 _98508 _98510 (@lem7645604 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645609 (_98508 : int) (_98510 : int) : (term383 _98508 _98510) = (term127 _98508 _98510).
Proof. exact (@lem1982733 (term127 _98508 _98510)). Qed.
Lemma lem7645610 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7645611 (_98508 : int) (_98510 : int) : (term384 _98508 _98510) = (term339 _98508 _98510).
Proof. exact (MK_COMB (@lem7645610) (@lem7645609 _98508 _98510)). Qed.
Lemma lem7645612 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7645613 (_98508 : int) (_98510 : int) : (term382 _98508 _98510) = (term340 _98508 _98510).
Proof. exact (MK_COMB (@lem7645611 _98508 _98510) (@lem7645612)). Qed.
Lemma lem7645614 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term340 _98508 _98510.
Proof. exact (EQ_MP (@lem7645613 _98508 _98510) (@lem7645608 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645615 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term385 _98510 _98508.
Proof. exact (conj (@lem7645614 _98509 _98508 _98510 h1) (@lem7645540 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645617 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7645618 (_98510 : int) (_98508 : int) : term386 _98510 _98508.
Proof. exact (@lem7645617 (term127 _98508 _98510) (real_of_int _98508)). Qed.
Lemma lem7645619 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term387 _98510 _98508.
Proof. exact (@lem7645618 _98510 _98508 (@lem7645615 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645620 (_98508 : int) (_98510 : int) : (term388 _98510 _98508) = (term389 _98508 _98510).
Proof. exact (@lem1982759 (term130 _98508) (real_of_int _98508) (term130 _98510)). Qed.
Lemma lem7645621 (_98508 : int) : (term192 _98508) = (term132 _98508).
Proof. exact (@lem1982713 term85 (real_of_int _98508)). Qed.
Lemma lem7645623 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645624 : term61 = term110.
Proof. exact (@lem7645623 term12). Qed.
Lemma lem7645626 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7645627 : term85 = term86.
Proof. exact (@lem7645626 term12). Qed.
Lemma lem7645628 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7645629 : term133 = term134.
Proof. exact (MK_COMB (@lem7645628) (@lem7645627)). Qed.
Lemma lem7645630 : term135 = term136.
Proof. exact (MK_COMB (@lem7645629) (@lem7645624)). Qed.
Lemma lem7645631 : term137.
Proof. exact (@lem1981473 term85 term61 term61 term61 term54 term61). Qed.
Lemma lem7645633 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645634 : term139 = term140.
Proof. exact (@lem7645633 (NUMERAL 0) term12). Qed.
Lemma lem7645635 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645636 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645637 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645636 h1) (fun h1 : term140 = True => @lem7645635)). Qed.
Lemma lem7645638 : term140 = True.
Proof. exact (EQ_MP (@lem7645637) (@lem7645635)). Qed.
Lemma lem7645639 : term139 = True.
Proof. exact (TRANS (@lem7645634) (@lem7645638)). Qed.
Lemma lem7645640 : True = term139.
Proof. exact (SYM (@lem7645639)). Qed.
Lemma lem7645641 : term139.
Proof. exact (EQ_MP (@lem7645640) (@lem0)). Qed.
Lemma lem7645642 : term142.
Proof. exact (@lem7645631 (@lem7645641)). Qed.
Lemma lem7645644 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645645 : term139 = term140.
Proof. exact (@lem7645644 (NUMERAL 0) term12). Qed.
Lemma lem7645646 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645647 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645648 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645647 h1) (fun h1 : term140 = True => @lem7645646)). Qed.
Lemma lem7645649 : term140 = True.
Proof. exact (EQ_MP (@lem7645648) (@lem7645646)). Qed.
Lemma lem7645650 : term139 = True.
Proof. exact (TRANS (@lem7645645) (@lem7645649)). Qed.
Lemma lem7645651 : True = term139.
Proof. exact (SYM (@lem7645650)). Qed.
Lemma lem7645652 : term139.
Proof. exact (EQ_MP (@lem7645651) (@lem0)). Qed.
Lemma lem7645653 : term143.
Proof. exact (@lem7645642 (@lem7645652)). Qed.
Lemma lem7645655 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645656 : term139 = term140.
Proof. exact (@lem7645655 (NUMERAL 0) term12). Qed.
Lemma lem7645657 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645658 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645659 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645658 h1) (fun h1 : term140 = True => @lem7645657)). Qed.
Lemma lem7645660 : term140 = True.
Proof. exact (EQ_MP (@lem7645659) (@lem7645657)). Qed.
Lemma lem7645661 : term139 = True.
Proof. exact (TRANS (@lem7645656) (@lem7645660)). Qed.
Lemma lem7645662 : True = term139.
Proof. exact (SYM (@lem7645661)). Qed.
Lemma lem7645663 : term139.
Proof. exact (EQ_MP (@lem7645662) (@lem0)). Qed.
Lemma lem7645664 : term144.
Proof. exact (@lem7645653 (@lem7645663)). Qed.
Lemma lem7645666 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645667 : term94 = term95.
Proof. exact (@lem7645666 term12 term12). Qed.
Lemma lem7645668 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645669 : term97 = term12.
Proof. exact (EQ_MP (@lem7645668) (@lem940073)). Qed.
Lemma lem7645670 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645671 : term95 = term61.
Proof. exact (MK_COMB (@lem7645670) (@lem7645669)). Qed.
Lemma lem7645672 : term94 = term61.
Proof. exact (TRANS (@lem7645667) (@lem7645671)). Qed.
Lemma lem7645674 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7645675 : term111 = term116.
Proof. exact (@lem7645674 term12 term12). Qed.
Lemma lem7645676 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645677 : term97 = term12.
Proof. exact (EQ_MP (@lem7645676) (@lem940073)). Qed.
Lemma lem7645678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645679 : term95 = term61.
Proof. exact (MK_COMB (@lem7645678) (@lem7645677)). Qed.
Lemma lem7645680 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7645681 : term116 = term85.
Proof. exact (MK_COMB (@lem7645680) (@lem7645679)). Qed.
Lemma lem7645682 : term111 = term85.
Proof. exact (TRANS (@lem7645675) (@lem7645681)). Qed.
Lemma lem7645683 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7645684 : term145 = term133.
Proof. exact (MK_COMB (@lem7645683) (@lem7645682)). Qed.
Lemma lem7645685 : term146 = term135.
Proof. exact (MK_COMB (@lem7645684) (@lem7645672)). Qed.
Lemma lem7645687 (m : nat) : (term147 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7645688 : term135 = term54.
Proof. exact (@lem7645687 term12). Qed.
Lemma lem7645689 : term146 = term54.
Proof. exact (TRANS (@lem7645685) (@lem7645688)). Qed.
Lemma lem7645690 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7645691 : term148 = term149.
Proof. exact (MK_COMB (@lem7645690) (@lem7645689)). Qed.
Lemma lem7645692 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem7645693 : term150 = term151.
Proof. exact (MK_COMB (@lem7645691) (@lem7645692)). Qed.
Lemma lem7645695 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645696 : term151 = term54.
Proof. exact (@lem7645695 term12). Qed.
Lemma lem7645697 : term150 = term54.
Proof. exact (TRANS (@lem7645693) (@lem7645696)). Qed.
Lemma lem7645699 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645700 : term94 = term95.
Proof. exact (@lem7645699 term12 term12). Qed.
Lemma lem7645701 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645702 : term97 = term12.
Proof. exact (EQ_MP (@lem7645701) (@lem940073)). Qed.
Lemma lem7645703 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645704 : term95 = term61.
Proof. exact (MK_COMB (@lem7645703) (@lem7645702)). Qed.
Lemma lem7645705 : term94 = term61.
Proof. exact (TRANS (@lem7645700) (@lem7645704)). Qed.
Lemma lem7645706 : term149 = term149.
Proof. exact (eq_refl term149). Qed.
Lemma lem7645707 : term153 = term151.
Proof. exact (MK_COMB (@lem7645706) (@lem7645705)). Qed.
Lemma lem7645709 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645710 : term151 = term54.
Proof. exact (@lem7645709 term12). Qed.
Lemma lem7645711 : term153 = term54.
Proof. exact (TRANS (@lem7645707) (@lem7645710)). Qed.
Lemma lem7645712 : term54 = term153.
Proof. exact (SYM (@lem7645711)). Qed.
Lemma lem7645713 : term150 = term153.
Proof. exact (TRANS (@lem7645697) (@lem7645712)). Qed.
Lemma lem7645714 : term136 = term82.
Proof. exact (@lem7645664 (@lem7645713)). Qed.
Lemma lem7645715 : term135 = term82.
Proof. exact (TRANS (@lem7645630) (@lem7645714)). Qed.
Lemma lem7645717 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7645718 : term82 = term54.
Proof. exact (@lem7645717 term54). Qed.
Lemma lem7645719 : term135 = term54.
Proof. exact (TRANS (@lem7645715) (@lem7645718)). Qed.
Lemma lem7645720 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7645721 : term154 = term149.
Proof. exact (MK_COMB (@lem7645720) (@lem7645719)). Qed.
Lemma lem7645722 (_98508 : int) : (real_of_int _98508) = (real_of_int _98508).
Proof. exact (eq_refl (real_of_int _98508)). Qed.
Lemma lem7645723 (_98508 : int) : (term132 _98508) = (term155 _98508).
Proof. exact (MK_COMB (@lem7645721) (@lem7645722 _98508)). Qed.
Lemma lem7645724 (_98508 : int) : (term192 _98508) = (term155 _98508).
Proof. exact (TRANS (@lem7645621 _98508) (@lem7645723 _98508)). Qed.
Lemma lem7645725 (_98508 : int) : (term155 _98508) = term54.
Proof. exact (@lem1982719 (real_of_int _98508)). Qed.
Lemma lem7645726 (_98508 : int) : (term192 _98508) = term54.
Proof. exact (TRANS (@lem7645724 _98508) (@lem7645725 _98508)). Qed.
Lemma lem7645727 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7645728 (_98508 : int) : (term193 _98508) = term157.
Proof. exact (MK_COMB (@lem7645727) (@lem7645726 _98508)). Qed.
Lemma lem7645729 (_98510 : int) : (term130 _98510) = (term130 _98510).
Proof. exact (eq_refl (term130 _98510)). Qed.
Lemma lem7645730 (_98508 : int) (_98510 : int) : (term389 _98508 _98510) = (term158 _98510).
Proof. exact (MK_COMB (@lem7645728 _98508) (@lem7645729 _98510)). Qed.
Lemma lem7645731 (_98508 : int) (_98510 : int) : (term388 _98510 _98508) = (term158 _98510).
Proof. exact (TRANS (@lem7645620 _98508 _98510) (@lem7645730 _98508 _98510)). Qed.
Lemma lem7645732 (_98510 : int) : (term158 _98510) = (term130 _98510).
Proof. exact (@lem1982721 (term130 _98510)). Qed.
Lemma lem7645733 (_98508 : int) (_98510 : int) : (term388 _98510 _98508) = (term130 _98510).
Proof. exact (TRANS (@lem7645731 _98508 _98510) (@lem7645732 _98510)). Qed.
Lemma lem7645734 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7645735 (_98508 : int) (_98510 : int) : (term390 _98510 _98508) = (term160 _98510).
Proof. exact (MK_COMB (@lem7645734) (@lem7645733 _98508 _98510)). Qed.
Lemma lem7645736 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7645737 (_98508 : int) (_98510 : int) : (term387 _98510 _98508) = (term161 _98510).
Proof. exact (MK_COMB (@lem7645735 _98508 _98510) (@lem7645736)). Qed.
Lemma lem7645738 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term161 _98510.
Proof. exact (EQ_MP (@lem7645737 _98508 _98510) (@lem7645619 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645740 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7645741 : term167 = term139.
Proof. exact (@lem7645740 term54 term61). Qed.
Lemma lem7645743 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645744 : term61 = term110.
Proof. exact (@lem7645743 term12). Qed.
Lemma lem7645746 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645747 : term54 = term82.
Proof. exact (@lem7645746 (NUMERAL 0)). Qed.
Lemma lem7645748 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7645749 : term168 = term169.
Proof. exact (MK_COMB (@lem7645748) (@lem7645747)). Qed.
Lemma lem7645750 : term139 = term170.
Proof. exact (MK_COMB (@lem7645749) (@lem7645744)). Qed.
Lemma lem7645751 : term171.
Proof. exact (@lem1980255 term54 term61 term61 term61). Qed.
Lemma lem7645753 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645754 : term139 = term140.
Proof. exact (@lem7645753 (NUMERAL 0) term12). Qed.
Lemma lem7645755 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645756 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645757 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645756 h1) (fun h1 : term140 = True => @lem7645755)). Qed.
Lemma lem7645758 : term140 = True.
Proof. exact (EQ_MP (@lem7645757) (@lem7645755)). Qed.
Lemma lem7645759 : term139 = True.
Proof. exact (TRANS (@lem7645754) (@lem7645758)). Qed.
Lemma lem7645760 : True = term139.
Proof. exact (SYM (@lem7645759)). Qed.
Lemma lem7645761 : term139.
Proof. exact (EQ_MP (@lem7645760) (@lem0)). Qed.
Lemma lem7645762 : term172.
Proof. exact (@lem7645751 (@lem7645761)). Qed.
Lemma lem7645764 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645765 : term139 = term140.
Proof. exact (@lem7645764 (NUMERAL 0) term12). Qed.
Lemma lem7645766 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645767 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645768 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645767 h1) (fun h1 : term140 = True => @lem7645766)). Qed.
Lemma lem7645769 : term140 = True.
Proof. exact (EQ_MP (@lem7645768) (@lem7645766)). Qed.
Lemma lem7645770 : term139 = True.
Proof. exact (TRANS (@lem7645765) (@lem7645769)). Qed.
Lemma lem7645771 : True = term139.
Proof. exact (SYM (@lem7645770)). Qed.
Lemma lem7645772 : term139.
Proof. exact (EQ_MP (@lem7645771) (@lem0)). Qed.
Lemma lem7645773 : term170 = term173.
Proof. exact (@lem7645762 (@lem7645772)). Qed.
Lemma lem7645775 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645776 : term94 = term95.
Proof. exact (@lem7645775 term12 term12). Qed.
Lemma lem7645777 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645778 : term97 = term12.
Proof. exact (EQ_MP (@lem7645777) (@lem940073)). Qed.
Lemma lem7645779 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645780 : term95 = term61.
Proof. exact (MK_COMB (@lem7645779) (@lem7645778)). Qed.
Lemma lem7645781 : term94 = term61.
Proof. exact (TRANS (@lem7645776) (@lem7645780)). Qed.
Lemma lem7645783 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645784 : term151 = term54.
Proof. exact (@lem7645783 term12). Qed.
Lemma lem7645785 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7645786 : term174 = term168.
Proof. exact (MK_COMB (@lem7645785) (@lem7645784)). Qed.
Lemma lem7645787 : term173 = term139.
Proof. exact (MK_COMB (@lem7645786) (@lem7645781)). Qed.
Lemma lem7645789 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645790 : term139 = term140.
Proof. exact (@lem7645789 (NUMERAL 0) term12). Qed.
Lemma lem7645791 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645792 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645793 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645792 h1) (fun h1 : term140 = True => @lem7645791)). Qed.
Lemma lem7645794 : term140 = True.
Proof. exact (EQ_MP (@lem7645793) (@lem7645791)). Qed.
Lemma lem7645795 : term139 = True.
Proof. exact (TRANS (@lem7645790) (@lem7645794)). Qed.
Lemma lem7645796 : term173 = True.
Proof. exact (TRANS (@lem7645787) (@lem7645795)). Qed.
Lemma lem7645797 : term170 = True.
Proof. exact (TRANS (@lem7645773) (@lem7645796)). Qed.
Lemma lem7645798 : term139 = True.
Proof. exact (TRANS (@lem7645750) (@lem7645797)). Qed.
Lemma lem7645799 : term167 = True.
Proof. exact (TRANS (@lem7645741) (@lem7645798)). Qed.
Lemma lem7645800 : True = term167.
Proof. exact (SYM (@lem7645799)). Qed.
Lemma lem7645801 : term167.
Proof. exact (EQ_MP (@lem7645800) (@lem0)). Qed.
Lemma lem7645802 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term181 _98510.
Proof. exact (conj (@lem7645801) (@lem7645738 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645804 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7645805 (_98510 : int) : term182 _98510.
Proof. exact (@lem7645804 term61 (term130 _98510)). Qed.
Lemma lem7645806 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term183 _98510.
Proof. exact (@lem7645805 _98510 (@lem7645802 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645807 (_98510 : int) : (term184 _98510) = (term130 _98510).
Proof. exact (@lem1982733 (term130 _98510)). Qed.
Lemma lem7645808 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7645809 (_98510 : int) : (term185 _98510) = (term160 _98510).
Proof. exact (MK_COMB (@lem7645808) (@lem7645807 _98510)). Qed.
Lemma lem7645810 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7645811 (_98510 : int) : (term183 _98510) = (term161 _98510).
Proof. exact (MK_COMB (@lem7645809 _98510) (@lem7645810)). Qed.
Lemma lem7645812 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term161 _98510.
Proof. exact (EQ_MP (@lem7645811 _98510) (@lem7645806 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645813 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term186 _98510.
Proof. exact (conj (@lem7645812 _98509 _98508 _98510 h1) (@lem7645466 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645815 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7645816 (_98510 : int) : term188 _98510.
Proof. exact (@lem7645815 (term130 _98510) (term119 _98510)). Qed.
Lemma lem7645817 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term189 _98510.
Proof. exact (@lem7645816 _98510 (@lem7645813 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645818 (_98510 : int) : (term190 _98510) = (term191 _98510).
Proof. exact (@lem1982763 (term130 _98510) (real_of_int _98510) term85). Qed.
Lemma lem7645819 (_98510 : int) : (term192 _98510) = (term132 _98510).
Proof. exact (@lem1982713 term85 (real_of_int _98510)). Qed.
Lemma lem7645821 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645822 : term61 = term110.
Proof. exact (@lem7645821 term12). Qed.
Lemma lem7645824 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7645825 : term85 = term86.
Proof. exact (@lem7645824 term12). Qed.
Lemma lem7645826 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7645827 : term133 = term134.
Proof. exact (MK_COMB (@lem7645826) (@lem7645825)). Qed.
Lemma lem7645828 : term135 = term136.
Proof. exact (MK_COMB (@lem7645827) (@lem7645822)). Qed.
Lemma lem7645829 : term137.
Proof. exact (@lem1981473 term85 term61 term61 term61 term54 term61). Qed.
Lemma lem7645831 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645832 : term139 = term140.
Proof. exact (@lem7645831 (NUMERAL 0) term12). Qed.
Lemma lem7645833 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645834 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645835 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645834 h1) (fun h1 : term140 = True => @lem7645833)). Qed.
Lemma lem7645836 : term140 = True.
Proof. exact (EQ_MP (@lem7645835) (@lem7645833)). Qed.
Lemma lem7645837 : term139 = True.
Proof. exact (TRANS (@lem7645832) (@lem7645836)). Qed.
Lemma lem7645838 : True = term139.
Proof. exact (SYM (@lem7645837)). Qed.
Lemma lem7645839 : term139.
Proof. exact (EQ_MP (@lem7645838) (@lem0)). Qed.
Lemma lem7645840 : term142.
Proof. exact (@lem7645829 (@lem7645839)). Qed.
Lemma lem7645842 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645843 : term139 = term140.
Proof. exact (@lem7645842 (NUMERAL 0) term12). Qed.
Lemma lem7645844 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645845 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645846 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645845 h1) (fun h1 : term140 = True => @lem7645844)). Qed.
Lemma lem7645847 : term140 = True.
Proof. exact (EQ_MP (@lem7645846) (@lem7645844)). Qed.
Lemma lem7645848 : term139 = True.
Proof. exact (TRANS (@lem7645843) (@lem7645847)). Qed.
Lemma lem7645849 : True = term139.
Proof. exact (SYM (@lem7645848)). Qed.
Lemma lem7645850 : term139.
Proof. exact (EQ_MP (@lem7645849) (@lem0)). Qed.
Lemma lem7645851 : term143.
Proof. exact (@lem7645840 (@lem7645850)). Qed.
Lemma lem7645853 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645854 : term139 = term140.
Proof. exact (@lem7645853 (NUMERAL 0) term12). Qed.
Lemma lem7645855 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645856 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645857 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645856 h1) (fun h1 : term140 = True => @lem7645855)). Qed.
Lemma lem7645858 : term140 = True.
Proof. exact (EQ_MP (@lem7645857) (@lem7645855)). Qed.
Lemma lem7645859 : term139 = True.
Proof. exact (TRANS (@lem7645854) (@lem7645858)). Qed.
Lemma lem7645860 : True = term139.
Proof. exact (SYM (@lem7645859)). Qed.
Lemma lem7645861 : term139.
Proof. exact (EQ_MP (@lem7645860) (@lem0)). Qed.
Lemma lem7645862 : term144.
Proof. exact (@lem7645851 (@lem7645861)). Qed.
Lemma lem7645864 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645865 : term94 = term95.
Proof. exact (@lem7645864 term12 term12). Qed.
Lemma lem7645866 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645867 : term97 = term12.
Proof. exact (EQ_MP (@lem7645866) (@lem940073)). Qed.
Lemma lem7645868 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645869 : term95 = term61.
Proof. exact (MK_COMB (@lem7645868) (@lem7645867)). Qed.
Lemma lem7645870 : term94 = term61.
Proof. exact (TRANS (@lem7645865) (@lem7645869)). Qed.
Lemma lem7645872 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7645873 : term111 = term116.
Proof. exact (@lem7645872 term12 term12). Qed.
Lemma lem7645874 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645875 : term97 = term12.
Proof. exact (EQ_MP (@lem7645874) (@lem940073)). Qed.
Lemma lem7645876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645877 : term95 = term61.
Proof. exact (MK_COMB (@lem7645876) (@lem7645875)). Qed.
Lemma lem7645878 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7645879 : term116 = term85.
Proof. exact (MK_COMB (@lem7645878) (@lem7645877)). Qed.
Lemma lem7645880 : term111 = term85.
Proof. exact (TRANS (@lem7645873) (@lem7645879)). Qed.
Lemma lem7645881 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7645882 : term145 = term133.
Proof. exact (MK_COMB (@lem7645881) (@lem7645880)). Qed.
Lemma lem7645883 : term146 = term135.
Proof. exact (MK_COMB (@lem7645882) (@lem7645870)). Qed.
Lemma lem7645885 (m : nat) : (term147 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7645886 : term135 = term54.
Proof. exact (@lem7645885 term12). Qed.
Lemma lem7645887 : term146 = term54.
Proof. exact (TRANS (@lem7645883) (@lem7645886)). Qed.
Lemma lem7645888 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7645889 : term148 = term149.
Proof. exact (MK_COMB (@lem7645888) (@lem7645887)). Qed.
Lemma lem7645890 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem7645891 : term150 = term151.
Proof. exact (MK_COMB (@lem7645889) (@lem7645890)). Qed.
Lemma lem7645893 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645894 : term151 = term54.
Proof. exact (@lem7645893 term12). Qed.
Lemma lem7645895 : term150 = term54.
Proof. exact (TRANS (@lem7645891) (@lem7645894)). Qed.
Lemma lem7645897 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7645898 : term94 = term95.
Proof. exact (@lem7645897 term12 term12). Qed.
Lemma lem7645899 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645900 : term97 = term12.
Proof. exact (EQ_MP (@lem7645899) (@lem940073)). Qed.
Lemma lem7645901 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645902 : term95 = term61.
Proof. exact (MK_COMB (@lem7645901) (@lem7645900)). Qed.
Lemma lem7645903 : term94 = term61.
Proof. exact (TRANS (@lem7645898) (@lem7645902)). Qed.
Lemma lem7645904 : term149 = term149.
Proof. exact (eq_refl term149). Qed.
Lemma lem7645905 : term153 = term151.
Proof. exact (MK_COMB (@lem7645904) (@lem7645903)). Qed.
Lemma lem7645907 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645908 : term151 = term54.
Proof. exact (@lem7645907 term12). Qed.
Lemma lem7645909 : term153 = term54.
Proof. exact (TRANS (@lem7645905) (@lem7645908)). Qed.
Lemma lem7645910 : term54 = term153.
Proof. exact (SYM (@lem7645909)). Qed.
Lemma lem7645911 : term150 = term153.
Proof. exact (TRANS (@lem7645895) (@lem7645910)). Qed.
Lemma lem7645912 : term136 = term82.
Proof. exact (@lem7645862 (@lem7645911)). Qed.
Lemma lem7645913 : term135 = term82.
Proof. exact (TRANS (@lem7645828) (@lem7645912)). Qed.
Lemma lem7645915 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7645916 : term82 = term54.
Proof. exact (@lem7645915 term54). Qed.
Lemma lem7645917 : term135 = term54.
Proof. exact (TRANS (@lem7645913) (@lem7645916)). Qed.
Lemma lem7645918 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7645919 : term154 = term149.
Proof. exact (MK_COMB (@lem7645918) (@lem7645917)). Qed.
Lemma lem7645920 (_98510 : int) : (real_of_int _98510) = (real_of_int _98510).
Proof. exact (eq_refl (real_of_int _98510)). Qed.
Lemma lem7645921 (_98510 : int) : (term132 _98510) = (term155 _98510).
Proof. exact (MK_COMB (@lem7645919) (@lem7645920 _98510)). Qed.
Lemma lem7645922 (_98510 : int) : (term192 _98510) = (term155 _98510).
Proof. exact (TRANS (@lem7645819 _98510) (@lem7645921 _98510)). Qed.
Lemma lem7645923 (_98510 : int) : (term155 _98510) = term54.
Proof. exact (@lem1982719 (real_of_int _98510)). Qed.
Lemma lem7645924 (_98510 : int) : (term192 _98510) = term54.
Proof. exact (TRANS (@lem7645922 _98510) (@lem7645923 _98510)). Qed.
Lemma lem7645925 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7645926 (_98510 : int) : (term193 _98510) = term157.
Proof. exact (MK_COMB (@lem7645925) (@lem7645924 _98510)). Qed.
Lemma lem7645927 : term85 = term85.
Proof. exact (eq_refl term85). Qed.
Lemma lem7645928 (_98510 : int) : (term191 _98510) = term194.
Proof. exact (MK_COMB (@lem7645926 _98510) (@lem7645927)). Qed.
Lemma lem7645929 (_98510 : int) : (term190 _98510) = term194.
Proof. exact (TRANS (@lem7645818 _98510) (@lem7645928 _98510)). Qed.
Lemma lem7645930 : term194 = term85.
Proof. exact (@lem1982721 term85). Qed.
Lemma lem7645931 (_98510 : int) : (term190 _98510) = term85.
Proof. exact (TRANS (@lem7645929 _98510) (@lem7645930)). Qed.
Lemma lem7645932 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7645933 (_98510 : int) : (term195 _98510) = term196.
Proof. exact (MK_COMB (@lem7645932) (@lem7645931 _98510)). Qed.
Lemma lem7645934 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7645935 (_98510 : int) : (term189 _98510) = term197.
Proof. exact (MK_COMB (@lem7645933 _98510) (@lem7645934)). Qed.
Lemma lem7645936 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : term197.
Proof. exact (EQ_MP (@lem7645935 _98510) (@lem7645817 _98509 _98508 _98510 h1)). Qed.
Lemma lem7645938 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7645939 : term197 = term198.
Proof. exact (@lem7645938 term54 term85). Qed.
Lemma lem7645941 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7645942 : term85 = term86.
Proof. exact (@lem7645941 term12). Qed.
Lemma lem7645944 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7645945 : term54 = term82.
Proof. exact (@lem7645944 (NUMERAL 0)). Qed.
Lemma lem7645946 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7645947 : term56 = term199.
Proof. exact (MK_COMB (@lem7645946) (@lem7645945)). Qed.
Lemma lem7645948 : term198 = term200.
Proof. exact (MK_COMB (@lem7645947) (@lem7645942)). Qed.
Lemma lem7645949 : term201.
Proof. exact (@lem1980026 term54 term61 term85 term61). Qed.
Lemma lem7645951 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645952 : term139 = term140.
Proof. exact (@lem7645951 (NUMERAL 0) term12). Qed.
Lemma lem7645953 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645954 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645955 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645954 h1) (fun h1 : term140 = True => @lem7645953)). Qed.
Lemma lem7645956 : term140 = True.
Proof. exact (EQ_MP (@lem7645955) (@lem7645953)). Qed.
Lemma lem7645957 : term139 = True.
Proof. exact (TRANS (@lem7645952) (@lem7645956)). Qed.
Lemma lem7645958 : True = term139.
Proof. exact (SYM (@lem7645957)). Qed.
Lemma lem7645959 : term139.
Proof. exact (EQ_MP (@lem7645958) (@lem0)). Qed.
Lemma lem7645960 : term202.
Proof. exact (@lem7645949 (@lem7645959)). Qed.
Lemma lem7645962 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7645963 : term139 = term140.
Proof. exact (@lem7645962 (NUMERAL 0) term12). Qed.
Lemma lem7645964 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645965 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7645966 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645965 h1) (fun h1 : term140 = True => @lem7645964)). Qed.
Lemma lem7645967 : term140 = True.
Proof. exact (EQ_MP (@lem7645966) (@lem7645964)). Qed.
Lemma lem7645968 : term139 = True.
Proof. exact (TRANS (@lem7645963) (@lem7645967)). Qed.
Lemma lem7645969 : True = term139.
Proof. exact (SYM (@lem7645968)). Qed.
Lemma lem7645970 : term139.
Proof. exact (EQ_MP (@lem7645969) (@lem0)). Qed.
Lemma lem7645971 : term200 = term203.
Proof. exact (@lem7645960 (@lem7645970)). Qed.
Lemma lem7645973 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7645974 : term111 = term116.
Proof. exact (@lem7645973 term12 term12). Qed.
Lemma lem7645975 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7645976 : term97 = term12.
Proof. exact (EQ_MP (@lem7645975) (@lem940073)). Qed.
Lemma lem7645977 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7645978 : term95 = term61.
Proof. exact (MK_COMB (@lem7645977) (@lem7645976)). Qed.
Lemma lem7645979 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7645980 : term116 = term85.
Proof. exact (MK_COMB (@lem7645979) (@lem7645978)). Qed.
Lemma lem7645981 : term111 = term85.
Proof. exact (TRANS (@lem7645974) (@lem7645980)). Qed.
Lemma lem7645983 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7645984 : term151 = term54.
Proof. exact (@lem7645983 term12). Qed.
Lemma lem7645985 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7645986 : term204 = term56.
Proof. exact (MK_COMB (@lem7645985) (@lem7645984)). Qed.
Lemma lem7645987 : term203 = term198.
Proof. exact (MK_COMB (@lem7645986) (@lem7645981)). Qed.
Lemma lem7645989 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7645990 : term198 = term207.
Proof. exact (@lem7645989 (NUMERAL 0) term12). Qed.
Lemma lem7645991 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7645992 (h1 : term141 = (BIT1 0)) : (term12 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7645993 : (term141 = (BIT1 0)) = ((term12 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7645992 h1) (fun h1 : (term12 = (NUMERAL 0)) = False => @lem7645991)). Qed.
Lemma lem7645994 : (term12 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7645993) (@lem7645991)). Qed.
Lemma lem7645995 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7645996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7645997 : term208 = (and True).
Proof. exact (MK_COMB (@lem7645996) (@lem7645995)). Qed.
Lemma lem7645998 : term207 = (True /\ False).
Proof. exact (MK_COMB (@lem7645997) (@lem7645994)). Qed.
Lemma lem7646000 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7646001 : term207 = False.
Proof. exact (TRANS (@lem7645998) (@lem7646000)). Qed.
Lemma lem7646002 : term198 = False.
Proof. exact (TRANS (@lem7645990) (@lem7646001)). Qed.
Lemma lem7646003 : term203 = False.
Proof. exact (TRANS (@lem7645987) (@lem7646002)). Qed.
Lemma lem7646004 : term200 = False.
Proof. exact (TRANS (@lem7645971) (@lem7646003)). Qed.
Lemma lem7646005 : term198 = False.
Proof. exact (TRANS (@lem7645948) (@lem7646004)). Qed.
Lemma lem7646006 : term197 = False.
Proof. exact (TRANS (@lem7645939) (@lem7646005)). Qed.
Lemma lem7646007 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term374 _98509 _98508 _98510) : False.
Proof. exact (EQ_MP (@lem7646006) (@lem7645936 _98509 _98508 _98510 h1)). Qed.
Lemma lem7646008 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term391 _98508 _98509 _98510.
Proof. exact (h1). Qed.
Lemma lem7646009 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term373 _98509 _98510.
Proof. exact (proj2 (@lem7646008 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646011 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term369 _98509 _98510.
Proof. exact (proj2 (@lem7646009 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646013 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term365 _98509 _98510.
Proof. exact (proj2 (@lem7646011 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646015 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term353 _98509 _98510.
Proof. exact (proj2 (@lem7646013 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646016 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term305 _98509 _98510.
Proof. exact (proj1 (@lem7646013 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646017 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term304 _98509 _98510.
Proof. exact (proj2 (@lem7646016 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646020 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7646021 : term167 = term139.
Proof. exact (@lem7646020 term54 term61). Qed.
Lemma lem7646023 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7646024 : term61 = term110.
Proof. exact (@lem7646023 term12). Qed.
Lemma lem7646026 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7646027 : term54 = term82.
Proof. exact (@lem7646026 (NUMERAL 0)). Qed.
Lemma lem7646028 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7646029 : term168 = term169.
Proof. exact (MK_COMB (@lem7646028) (@lem7646027)). Qed.
Lemma lem7646030 : term139 = term170.
Proof. exact (MK_COMB (@lem7646029) (@lem7646024)). Qed.
Lemma lem7646031 : term171.
Proof. exact (@lem1980255 term54 term61 term61 term61). Qed.
Lemma lem7646033 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646034 : term139 = term140.
Proof. exact (@lem7646033 (NUMERAL 0) term12). Qed.
Lemma lem7646035 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646036 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646037 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646036 h1) (fun h1 : term140 = True => @lem7646035)). Qed.
Lemma lem7646038 : term140 = True.
Proof. exact (EQ_MP (@lem7646037) (@lem7646035)). Qed.
Lemma lem7646039 : term139 = True.
Proof. exact (TRANS (@lem7646034) (@lem7646038)). Qed.
Lemma lem7646040 : True = term139.
Proof. exact (SYM (@lem7646039)). Qed.
Lemma lem7646041 : term139.
Proof. exact (EQ_MP (@lem7646040) (@lem0)). Qed.
Lemma lem7646042 : term172.
Proof. exact (@lem7646031 (@lem7646041)). Qed.
Lemma lem7646044 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646045 : term139 = term140.
Proof. exact (@lem7646044 (NUMERAL 0) term12). Qed.
Lemma lem7646046 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646047 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646048 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646047 h1) (fun h1 : term140 = True => @lem7646046)). Qed.
Lemma lem7646049 : term140 = True.
Proof. exact (EQ_MP (@lem7646048) (@lem7646046)). Qed.
Lemma lem7646050 : term139 = True.
Proof. exact (TRANS (@lem7646045) (@lem7646049)). Qed.
Lemma lem7646051 : True = term139.
Proof. exact (SYM (@lem7646050)). Qed.
Lemma lem7646052 : term139.
Proof. exact (EQ_MP (@lem7646051) (@lem0)). Qed.
Lemma lem7646053 : term170 = term173.
Proof. exact (@lem7646042 (@lem7646052)). Qed.
Lemma lem7646055 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7646056 : term94 = term95.
Proof. exact (@lem7646055 term12 term12). Qed.
Lemma lem7646057 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7646058 : term97 = term12.
Proof. exact (EQ_MP (@lem7646057) (@lem940073)). Qed.
Lemma lem7646059 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7646060 : term95 = term61.
Proof. exact (MK_COMB (@lem7646059) (@lem7646058)). Qed.
Lemma lem7646061 : term94 = term61.
Proof. exact (TRANS (@lem7646056) (@lem7646060)). Qed.
Lemma lem7646063 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7646064 : term151 = term54.
Proof. exact (@lem7646063 term12). Qed.
Lemma lem7646065 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7646066 : term174 = term168.
Proof. exact (MK_COMB (@lem7646065) (@lem7646064)). Qed.
Lemma lem7646067 : term173 = term139.
Proof. exact (MK_COMB (@lem7646066) (@lem7646061)). Qed.
Lemma lem7646069 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646070 : term139 = term140.
Proof. exact (@lem7646069 (NUMERAL 0) term12). Qed.
Lemma lem7646071 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646072 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646073 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646072 h1) (fun h1 : term140 = True => @lem7646071)). Qed.
Lemma lem7646074 : term140 = True.
Proof. exact (EQ_MP (@lem7646073) (@lem7646071)). Qed.
Lemma lem7646075 : term139 = True.
Proof. exact (TRANS (@lem7646070) (@lem7646074)). Qed.
Lemma lem7646076 : term173 = True.
Proof. exact (TRANS (@lem7646067) (@lem7646075)). Qed.
Lemma lem7646077 : term170 = True.
Proof. exact (TRANS (@lem7646053) (@lem7646076)). Qed.
Lemma lem7646078 : term139 = True.
Proof. exact (TRANS (@lem7646030) (@lem7646077)). Qed.
Lemma lem7646079 : term167 = True.
Proof. exact (TRANS (@lem7646021) (@lem7646078)). Qed.
Lemma lem7646080 : True = term167.
Proof. exact (SYM (@lem7646079)). Qed.
Lemma lem7646081 : term167.
Proof. exact (EQ_MP (@lem7646080) (@lem0)). Qed.
Lemma lem7646082 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term392 _98509 _98510.
Proof. exact (conj (@lem7646081) (@lem7646017 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646084 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7646085 (_98509 : int) (_98510 : int) : term393 _98509 _98510.
Proof. exact (@lem7646084 term61 (term301 _98509 _98510)). Qed.
Lemma lem7646086 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term394 _98509 _98510.
Proof. exact (@lem7646085 _98509 _98510 (@lem7646082 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646087 (_98509 : int) (_98510 : int) : (term395 _98509 _98510) = (term301 _98509 _98510).
Proof. exact (@lem1982733 (term301 _98509 _98510)). Qed.
Lemma lem7646088 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7646089 (_98509 : int) (_98510 : int) : (term396 _98509 _98510) = (term303 _98509 _98510).
Proof. exact (MK_COMB (@lem7646088) (@lem7646087 _98509 _98510)). Qed.
Lemma lem7646090 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7646091 (_98509 : int) (_98510 : int) : (term394 _98509 _98510) = (term304 _98509 _98510).
Proof. exact (MK_COMB (@lem7646089 _98509 _98510) (@lem7646090)). Qed.
Lemma lem7646092 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term304 _98509 _98510.
Proof. exact (EQ_MP (@lem7646091 _98509 _98510) (@lem7646086 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646094 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7646095 : term167 = term139.
Proof. exact (@lem7646094 term54 term61). Qed.
Lemma lem7646097 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7646098 : term61 = term110.
Proof. exact (@lem7646097 term12). Qed.
Lemma lem7646100 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7646101 : term54 = term82.
Proof. exact (@lem7646100 (NUMERAL 0)). Qed.
Lemma lem7646102 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7646103 : term168 = term169.
Proof. exact (MK_COMB (@lem7646102) (@lem7646101)). Qed.
Lemma lem7646104 : term139 = term170.
Proof. exact (MK_COMB (@lem7646103) (@lem7646098)). Qed.
Lemma lem7646105 : term171.
Proof. exact (@lem1980255 term54 term61 term61 term61). Qed.
Lemma lem7646107 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646108 : term139 = term140.
Proof. exact (@lem7646107 (NUMERAL 0) term12). Qed.
Lemma lem7646109 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646110 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646111 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646110 h1) (fun h1 : term140 = True => @lem7646109)). Qed.
Lemma lem7646112 : term140 = True.
Proof. exact (EQ_MP (@lem7646111) (@lem7646109)). Qed.
Lemma lem7646113 : term139 = True.
Proof. exact (TRANS (@lem7646108) (@lem7646112)). Qed.
Lemma lem7646114 : True = term139.
Proof. exact (SYM (@lem7646113)). Qed.
Lemma lem7646115 : term139.
Proof. exact (EQ_MP (@lem7646114) (@lem0)). Qed.
Lemma lem7646116 : term172.
Proof. exact (@lem7646105 (@lem7646115)). Qed.
Lemma lem7646118 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646119 : term139 = term140.
Proof. exact (@lem7646118 (NUMERAL 0) term12). Qed.
Lemma lem7646120 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646121 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646122 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646121 h1) (fun h1 : term140 = True => @lem7646120)). Qed.
Lemma lem7646123 : term140 = True.
Proof. exact (EQ_MP (@lem7646122) (@lem7646120)). Qed.
Lemma lem7646124 : term139 = True.
Proof. exact (TRANS (@lem7646119) (@lem7646123)). Qed.
Lemma lem7646125 : True = term139.
Proof. exact (SYM (@lem7646124)). Qed.
Lemma lem7646126 : term139.
Proof. exact (EQ_MP (@lem7646125) (@lem0)). Qed.
Lemma lem7646127 : term170 = term173.
Proof. exact (@lem7646116 (@lem7646126)). Qed.
Lemma lem7646129 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7646130 : term94 = term95.
Proof. exact (@lem7646129 term12 term12). Qed.
Lemma lem7646131 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7646132 : term97 = term12.
Proof. exact (EQ_MP (@lem7646131) (@lem940073)). Qed.
Lemma lem7646133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7646134 : term95 = term61.
Proof. exact (MK_COMB (@lem7646133) (@lem7646132)). Qed.
Lemma lem7646135 : term94 = term61.
Proof. exact (TRANS (@lem7646130) (@lem7646134)). Qed.
Lemma lem7646137 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7646138 : term151 = term54.
Proof. exact (@lem7646137 term12). Qed.
Lemma lem7646139 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7646140 : term174 = term168.
Proof. exact (MK_COMB (@lem7646139) (@lem7646138)). Qed.
Lemma lem7646141 : term173 = term139.
Proof. exact (MK_COMB (@lem7646140) (@lem7646135)). Qed.
Lemma lem7646143 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646144 : term139 = term140.
Proof. exact (@lem7646143 (NUMERAL 0) term12). Qed.
Lemma lem7646145 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646146 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646147 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646146 h1) (fun h1 : term140 = True => @lem7646145)). Qed.
Lemma lem7646148 : term140 = True.
Proof. exact (EQ_MP (@lem7646147) (@lem7646145)). Qed.
Lemma lem7646149 : term139 = True.
Proof. exact (TRANS (@lem7646144) (@lem7646148)). Qed.
Lemma lem7646150 : term173 = True.
Proof. exact (TRANS (@lem7646141) (@lem7646149)). Qed.
Lemma lem7646151 : term170 = True.
Proof. exact (TRANS (@lem7646127) (@lem7646150)). Qed.
Lemma lem7646152 : term139 = True.
Proof. exact (TRANS (@lem7646104) (@lem7646151)). Qed.
Lemma lem7646153 : term167 = True.
Proof. exact (TRANS (@lem7646095) (@lem7646152)). Qed.
Lemma lem7646154 : True = term167.
Proof. exact (SYM (@lem7646153)). Qed.
Lemma lem7646155 : term167.
Proof. exact (EQ_MP (@lem7646154) (@lem0)). Qed.
Lemma lem7646156 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term397 _98509 _98510.
Proof. exact (conj (@lem7646155) (@lem7646015 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646158 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7646159 (_98509 : int) (_98510 : int) : term398 _98509 _98510.
Proof. exact (@lem7646158 term61 (term349 _98509 _98510)). Qed.
Lemma lem7646160 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term399 _98509 _98510.
Proof. exact (@lem7646159 _98509 _98510 (@lem7646156 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646161 (_98509 : int) (_98510 : int) : (term400 _98509 _98510) = (term349 _98509 _98510).
Proof. exact (@lem1982733 (term349 _98509 _98510)). Qed.
Lemma lem7646162 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7646163 (_98509 : int) (_98510 : int) : (term401 _98509 _98510) = (term352 _98509 _98510).
Proof. exact (MK_COMB (@lem7646162) (@lem7646161 _98509 _98510)). Qed.
Lemma lem7646164 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7646165 (_98509 : int) (_98510 : int) : (term399 _98509 _98510) = (term353 _98509 _98510).
Proof. exact (MK_COMB (@lem7646163 _98509 _98510) (@lem7646164)). Qed.
Lemma lem7646166 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term353 _98509 _98510.
Proof. exact (EQ_MP (@lem7646165 _98509 _98510) (@lem7646160 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646167 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term402 _98509 _98510.
Proof. exact (conj (@lem7646166 _98508 _98509 _98510 h1) (@lem7646092 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646169 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7646170 (_98509 : int) (_98510 : int) : term403 _98509 _98510.
Proof. exact (@lem7646169 (term349 _98509 _98510) (term301 _98509 _98510)). Qed.
Lemma lem7646171 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term404 _98509 _98510.
Proof. exact (@lem7646170 _98509 _98510 (@lem7646167 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646172 (_98509 : int) (_98510 : int) : (term405 _98509 _98510) = (term406 _98509 _98510).
Proof. exact (@lem1982753 (term130 _98509) (real_of_int _98509) (term119 _98510) (term130 _98510)). Qed.
Lemma lem7646173 (_98509 : int) : (term192 _98509) = (term132 _98509).
Proof. exact (@lem1982713 term85 (real_of_int _98509)). Qed.
Lemma lem7646175 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7646176 : term61 = term110.
Proof. exact (@lem7646175 term12). Qed.
Lemma lem7646178 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7646179 : term85 = term86.
Proof. exact (@lem7646178 term12). Qed.
Lemma lem7646180 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7646181 : term133 = term134.
Proof. exact (MK_COMB (@lem7646180) (@lem7646179)). Qed.
Lemma lem7646182 : term135 = term136.
Proof. exact (MK_COMB (@lem7646181) (@lem7646176)). Qed.
Lemma lem7646183 : term137.
Proof. exact (@lem1981473 term85 term61 term61 term61 term54 term61). Qed.
Lemma lem7646185 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646186 : term139 = term140.
Proof. exact (@lem7646185 (NUMERAL 0) term12). Qed.
Lemma lem7646187 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646188 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646189 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646188 h1) (fun h1 : term140 = True => @lem7646187)). Qed.
Lemma lem7646190 : term140 = True.
Proof. exact (EQ_MP (@lem7646189) (@lem7646187)). Qed.
Lemma lem7646191 : term139 = True.
Proof. exact (TRANS (@lem7646186) (@lem7646190)). Qed.
Lemma lem7646192 : True = term139.
Proof. exact (SYM (@lem7646191)). Qed.
Lemma lem7646193 : term139.
Proof. exact (EQ_MP (@lem7646192) (@lem0)). Qed.
Lemma lem7646194 : term142.
Proof. exact (@lem7646183 (@lem7646193)). Qed.
Lemma lem7646196 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646197 : term139 = term140.
Proof. exact (@lem7646196 (NUMERAL 0) term12). Qed.
Lemma lem7646198 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646199 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646200 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646199 h1) (fun h1 : term140 = True => @lem7646198)). Qed.
Lemma lem7646201 : term140 = True.
Proof. exact (EQ_MP (@lem7646200) (@lem7646198)). Qed.
Lemma lem7646202 : term139 = True.
Proof. exact (TRANS (@lem7646197) (@lem7646201)). Qed.
Lemma lem7646203 : True = term139.
Proof. exact (SYM (@lem7646202)). Qed.
Lemma lem7646204 : term139.
Proof. exact (EQ_MP (@lem7646203) (@lem0)). Qed.
Lemma lem7646205 : term143.
Proof. exact (@lem7646194 (@lem7646204)). Qed.
Lemma lem7646207 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646208 : term139 = term140.
Proof. exact (@lem7646207 (NUMERAL 0) term12). Qed.
Lemma lem7646209 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646210 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646211 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646210 h1) (fun h1 : term140 = True => @lem7646209)). Qed.
Lemma lem7646212 : term140 = True.
Proof. exact (EQ_MP (@lem7646211) (@lem7646209)). Qed.
Lemma lem7646213 : term139 = True.
Proof. exact (TRANS (@lem7646208) (@lem7646212)). Qed.
Lemma lem7646214 : True = term139.
Proof. exact (SYM (@lem7646213)). Qed.
Lemma lem7646215 : term139.
Proof. exact (EQ_MP (@lem7646214) (@lem0)). Qed.
Lemma lem7646216 : term144.
Proof. exact (@lem7646205 (@lem7646215)). Qed.
Lemma lem7646218 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7646219 : term94 = term95.
Proof. exact (@lem7646218 term12 term12). Qed.
Lemma lem7646220 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7646221 : term97 = term12.
Proof. exact (EQ_MP (@lem7646220) (@lem940073)). Qed.
Lemma lem7646222 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7646223 : term95 = term61.
Proof. exact (MK_COMB (@lem7646222) (@lem7646221)). Qed.
Lemma lem7646224 : term94 = term61.
Proof. exact (TRANS (@lem7646219) (@lem7646223)). Qed.
Lemma lem7646226 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7646227 : term111 = term116.
Proof. exact (@lem7646226 term12 term12). Qed.
Lemma lem7646228 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7646229 : term97 = term12.
Proof. exact (EQ_MP (@lem7646228) (@lem940073)). Qed.
Lemma lem7646230 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7646231 : term95 = term61.
Proof. exact (MK_COMB (@lem7646230) (@lem7646229)). Qed.
Lemma lem7646232 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7646233 : term116 = term85.
Proof. exact (MK_COMB (@lem7646232) (@lem7646231)). Qed.
Lemma lem7646234 : term111 = term85.
Proof. exact (TRANS (@lem7646227) (@lem7646233)). Qed.
Lemma lem7646235 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7646236 : term145 = term133.
Proof. exact (MK_COMB (@lem7646235) (@lem7646234)). Qed.
Lemma lem7646237 : term146 = term135.
Proof. exact (MK_COMB (@lem7646236) (@lem7646224)). Qed.
Lemma lem7646239 (m : nat) : (term147 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7646240 : term135 = term54.
Proof. exact (@lem7646239 term12). Qed.
Lemma lem7646241 : term146 = term54.
Proof. exact (TRANS (@lem7646237) (@lem7646240)). Qed.
Lemma lem7646242 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7646243 : term148 = term149.
Proof. exact (MK_COMB (@lem7646242) (@lem7646241)). Qed.
Lemma lem7646244 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem7646245 : term150 = term151.
Proof. exact (MK_COMB (@lem7646243) (@lem7646244)). Qed.
Lemma lem7646247 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7646248 : term151 = term54.
Proof. exact (@lem7646247 term12). Qed.
Lemma lem7646249 : term150 = term54.
Proof. exact (TRANS (@lem7646245) (@lem7646248)). Qed.
Lemma lem7646251 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7646252 : term94 = term95.
Proof. exact (@lem7646251 term12 term12). Qed.
Lemma lem7646253 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7646254 : term97 = term12.
Proof. exact (EQ_MP (@lem7646253) (@lem940073)). Qed.
Lemma lem7646255 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7646256 : term95 = term61.
Proof. exact (MK_COMB (@lem7646255) (@lem7646254)). Qed.
Lemma lem7646257 : term94 = term61.
Proof. exact (TRANS (@lem7646252) (@lem7646256)). Qed.
Lemma lem7646258 : term149 = term149.
Proof. exact (eq_refl term149). Qed.
Lemma lem7646259 : term153 = term151.
Proof. exact (MK_COMB (@lem7646258) (@lem7646257)). Qed.
Lemma lem7646261 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7646262 : term151 = term54.
Proof. exact (@lem7646261 term12). Qed.
Lemma lem7646263 : term153 = term54.
Proof. exact (TRANS (@lem7646259) (@lem7646262)). Qed.
Lemma lem7646264 : term54 = term153.
Proof. exact (SYM (@lem7646263)). Qed.
Lemma lem7646265 : term150 = term153.
Proof. exact (TRANS (@lem7646249) (@lem7646264)). Qed.
Lemma lem7646266 : term136 = term82.
Proof. exact (@lem7646216 (@lem7646265)). Qed.
Lemma lem7646267 : term135 = term82.
Proof. exact (TRANS (@lem7646182) (@lem7646266)). Qed.
Lemma lem7646269 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7646270 : term82 = term54.
Proof. exact (@lem7646269 term54). Qed.
Lemma lem7646271 : term135 = term54.
Proof. exact (TRANS (@lem7646267) (@lem7646270)). Qed.
Lemma lem7646272 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7646273 : term154 = term149.
Proof. exact (MK_COMB (@lem7646272) (@lem7646271)). Qed.
Lemma lem7646274 (_98509 : int) : (real_of_int _98509) = (real_of_int _98509).
Proof. exact (eq_refl (real_of_int _98509)). Qed.
Lemma lem7646275 (_98509 : int) : (term132 _98509) = (term155 _98509).
Proof. exact (MK_COMB (@lem7646273) (@lem7646274 _98509)). Qed.
Lemma lem7646276 (_98509 : int) : (term192 _98509) = (term155 _98509).
Proof. exact (TRANS (@lem7646173 _98509) (@lem7646275 _98509)). Qed.
Lemma lem7646277 (_98509 : int) : (term155 _98509) = term54.
Proof. exact (@lem1982719 (real_of_int _98509)). Qed.
Lemma lem7646278 (_98509 : int) : (term192 _98509) = term54.
Proof. exact (TRANS (@lem7646276 _98509) (@lem7646277 _98509)). Qed.
Lemma lem7646279 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7646280 (_98509 : int) : (term193 _98509) = term157.
Proof. exact (MK_COMB (@lem7646279) (@lem7646278 _98509)). Qed.
Lemma lem7646281 (_98510 : int) : (term407 _98510) = (term408 _98510).
Proof. exact (@lem1982759 (real_of_int _98510) (term130 _98510) term85). Qed.
Lemma lem7646282 (_98510 : int) : (term131 _98510) = (term132 _98510).
Proof. exact (@lem1982715 term85 (real_of_int _98510)). Qed.
Lemma lem7646284 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7646285 : term61 = term110.
Proof. exact (@lem7646284 term12). Qed.
Lemma lem7646287 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7646288 : term85 = term86.
Proof. exact (@lem7646287 term12). Qed.
Lemma lem7646289 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7646290 : term133 = term134.
Proof. exact (MK_COMB (@lem7646289) (@lem7646288)). Qed.
Lemma lem7646291 : term135 = term136.
Proof. exact (MK_COMB (@lem7646290) (@lem7646285)). Qed.
Lemma lem7646292 : term137.
Proof. exact (@lem1981473 term85 term61 term61 term61 term54 term61). Qed.
Lemma lem7646294 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646295 : term139 = term140.
Proof. exact (@lem7646294 (NUMERAL 0) term12). Qed.
Lemma lem7646296 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646297 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646298 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646297 h1) (fun h1 : term140 = True => @lem7646296)). Qed.
Lemma lem7646299 : term140 = True.
Proof. exact (EQ_MP (@lem7646298) (@lem7646296)). Qed.
Lemma lem7646300 : term139 = True.
Proof. exact (TRANS (@lem7646295) (@lem7646299)). Qed.
Lemma lem7646301 : True = term139.
Proof. exact (SYM (@lem7646300)). Qed.
Lemma lem7646302 : term139.
Proof. exact (EQ_MP (@lem7646301) (@lem0)). Qed.
Lemma lem7646303 : term142.
Proof. exact (@lem7646292 (@lem7646302)). Qed.
Lemma lem7646305 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646306 : term139 = term140.
Proof. exact (@lem7646305 (NUMERAL 0) term12). Qed.
Lemma lem7646307 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646308 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646309 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646308 h1) (fun h1 : term140 = True => @lem7646307)). Qed.
Lemma lem7646310 : term140 = True.
Proof. exact (EQ_MP (@lem7646309) (@lem7646307)). Qed.
Lemma lem7646311 : term139 = True.
Proof. exact (TRANS (@lem7646306) (@lem7646310)). Qed.
Lemma lem7646312 : True = term139.
Proof. exact (SYM (@lem7646311)). Qed.
Lemma lem7646313 : term139.
Proof. exact (EQ_MP (@lem7646312) (@lem0)). Qed.
Lemma lem7646314 : term143.
Proof. exact (@lem7646303 (@lem7646313)). Qed.
Lemma lem7646316 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646317 : term139 = term140.
Proof. exact (@lem7646316 (NUMERAL 0) term12). Qed.
Lemma lem7646318 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646319 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646320 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646319 h1) (fun h1 : term140 = True => @lem7646318)). Qed.
Lemma lem7646321 : term140 = True.
Proof. exact (EQ_MP (@lem7646320) (@lem7646318)). Qed.
Lemma lem7646322 : term139 = True.
Proof. exact (TRANS (@lem7646317) (@lem7646321)). Qed.
Lemma lem7646323 : True = term139.
Proof. exact (SYM (@lem7646322)). Qed.
Lemma lem7646324 : term139.
Proof. exact (EQ_MP (@lem7646323) (@lem0)). Qed.
Lemma lem7646325 : term144.
Proof. exact (@lem7646314 (@lem7646324)). Qed.
Lemma lem7646327 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7646328 : term94 = term95.
Proof. exact (@lem7646327 term12 term12). Qed.
Lemma lem7646329 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7646330 : term97 = term12.
Proof. exact (EQ_MP (@lem7646329) (@lem940073)). Qed.
Lemma lem7646331 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7646332 : term95 = term61.
Proof. exact (MK_COMB (@lem7646331) (@lem7646330)). Qed.
Lemma lem7646333 : term94 = term61.
Proof. exact (TRANS (@lem7646328) (@lem7646332)). Qed.
Lemma lem7646335 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7646336 : term111 = term116.
Proof. exact (@lem7646335 term12 term12). Qed.
Lemma lem7646337 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7646338 : term97 = term12.
Proof. exact (EQ_MP (@lem7646337) (@lem940073)). Qed.
Lemma lem7646339 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7646340 : term95 = term61.
Proof. exact (MK_COMB (@lem7646339) (@lem7646338)). Qed.
Lemma lem7646341 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7646342 : term116 = term85.
Proof. exact (MK_COMB (@lem7646341) (@lem7646340)). Qed.
Lemma lem7646343 : term111 = term85.
Proof. exact (TRANS (@lem7646336) (@lem7646342)). Qed.
Lemma lem7646344 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7646345 : term145 = term133.
Proof. exact (MK_COMB (@lem7646344) (@lem7646343)). Qed.
Lemma lem7646346 : term146 = term135.
Proof. exact (MK_COMB (@lem7646345) (@lem7646333)). Qed.
Lemma lem7646348 (m : nat) : (term147 m) = term54.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7646349 : term135 = term54.
Proof. exact (@lem7646348 term12). Qed.
Lemma lem7646350 : term146 = term54.
Proof. exact (TRANS (@lem7646346) (@lem7646349)). Qed.
Lemma lem7646351 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7646352 : term148 = term149.
Proof. exact (MK_COMB (@lem7646351) (@lem7646350)). Qed.
Lemma lem7646353 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem7646354 : term150 = term151.
Proof. exact (MK_COMB (@lem7646352) (@lem7646353)). Qed.
Lemma lem7646356 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7646357 : term151 = term54.
Proof. exact (@lem7646356 term12). Qed.
Lemma lem7646358 : term150 = term54.
Proof. exact (TRANS (@lem7646354) (@lem7646357)). Qed.
Lemma lem7646360 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7646361 : term94 = term95.
Proof. exact (@lem7646360 term12 term12). Qed.
Lemma lem7646362 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7646363 : term97 = term12.
Proof. exact (EQ_MP (@lem7646362) (@lem940073)). Qed.
Lemma lem7646364 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7646365 : term95 = term61.
Proof. exact (MK_COMB (@lem7646364) (@lem7646363)). Qed.
Lemma lem7646366 : term94 = term61.
Proof. exact (TRANS (@lem7646361) (@lem7646365)). Qed.
Lemma lem7646367 : term149 = term149.
Proof. exact (eq_refl term149). Qed.
Lemma lem7646368 : term153 = term151.
Proof. exact (MK_COMB (@lem7646367) (@lem7646366)). Qed.
Lemma lem7646370 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7646371 : term151 = term54.
Proof. exact (@lem7646370 term12). Qed.
Lemma lem7646372 : term153 = term54.
Proof. exact (TRANS (@lem7646368) (@lem7646371)). Qed.
Lemma lem7646373 : term54 = term153.
Proof. exact (SYM (@lem7646372)). Qed.
Lemma lem7646374 : term150 = term153.
Proof. exact (TRANS (@lem7646358) (@lem7646373)). Qed.
Lemma lem7646375 : term136 = term82.
Proof. exact (@lem7646325 (@lem7646374)). Qed.
Lemma lem7646376 : term135 = term82.
Proof. exact (TRANS (@lem7646291) (@lem7646375)). Qed.
Lemma lem7646378 (x : real) : (term101 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7646379 : term82 = term54.
Proof. exact (@lem7646378 term54). Qed.
Lemma lem7646380 : term135 = term54.
Proof. exact (TRANS (@lem7646376) (@lem7646379)). Qed.
Lemma lem7646381 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7646382 : term154 = term149.
Proof. exact (MK_COMB (@lem7646381) (@lem7646380)). Qed.
Lemma lem7646383 (_98510 : int) : (real_of_int _98510) = (real_of_int _98510).
Proof. exact (eq_refl (real_of_int _98510)). Qed.
Lemma lem7646384 (_98510 : int) : (term132 _98510) = (term155 _98510).
Proof. exact (MK_COMB (@lem7646382) (@lem7646383 _98510)). Qed.
Lemma lem7646385 (_98510 : int) : (term131 _98510) = (term155 _98510).
Proof. exact (TRANS (@lem7646282 _98510) (@lem7646384 _98510)). Qed.
Lemma lem7646386 (_98510 : int) : (term155 _98510) = term54.
Proof. exact (@lem1982719 (real_of_int _98510)). Qed.
Lemma lem7646387 (_98510 : int) : (term131 _98510) = term54.
Proof. exact (TRANS (@lem7646385 _98510) (@lem7646386 _98510)). Qed.
Lemma lem7646388 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7646389 (_98510 : int) : (term156 _98510) = term157.
Proof. exact (MK_COMB (@lem7646388) (@lem7646387 _98510)). Qed.
Lemma lem7646390 : term85 = term85.
Proof. exact (eq_refl term85). Qed.
Lemma lem7646391 (_98510 : int) : (term408 _98510) = term194.
Proof. exact (MK_COMB (@lem7646389 _98510) (@lem7646390)). Qed.
Lemma lem7646392 (_98510 : int) : (term407 _98510) = term194.
Proof. exact (TRANS (@lem7646281 _98510) (@lem7646391 _98510)). Qed.
Lemma lem7646393 : term194 = term85.
Proof. exact (@lem1982721 term85). Qed.
Lemma lem7646394 (_98510 : int) : (term407 _98510) = term85.
Proof. exact (TRANS (@lem7646392 _98510) (@lem7646393)). Qed.
Lemma lem7646395 (_98509 : int) (_98510 : int) : (term406 _98509 _98510) = term194.
Proof. exact (MK_COMB (@lem7646280 _98509) (@lem7646394 _98510)). Qed.
Lemma lem7646396 (_98509 : int) (_98510 : int) : (term405 _98509 _98510) = term194.
Proof. exact (TRANS (@lem7646172 _98509 _98510) (@lem7646395 _98509 _98510)). Qed.
Lemma lem7646397 : term194 = term85.
Proof. exact (@lem1982721 term85). Qed.
Lemma lem7646398 (_98509 : int) (_98510 : int) : (term405 _98509 _98510) = term85.
Proof. exact (TRANS (@lem7646396 _98509 _98510) (@lem7646397)). Qed.
Lemma lem7646399 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7646400 (_98509 : int) (_98510 : int) : (term409 _98509 _98510) = term196.
Proof. exact (MK_COMB (@lem7646399) (@lem7646398 _98509 _98510)). Qed.
Lemma lem7646401 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem7646402 (_98509 : int) (_98510 : int) : (term404 _98509 _98510) = term197.
Proof. exact (MK_COMB (@lem7646400 _98509 _98510) (@lem7646401)). Qed.
Lemma lem7646403 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : term197.
Proof. exact (EQ_MP (@lem7646402 _98509 _98510) (@lem7646171 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646405 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7646406 : term197 = term198.
Proof. exact (@lem7646405 term54 term85). Qed.
Lemma lem7646408 (x : nat) : (term83 x) = (term84 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7646409 : term85 = term86.
Proof. exact (@lem7646408 term12). Qed.
Lemma lem7646411 (x : nat) : (real_of_num x) = (term81 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7646412 : term54 = term82.
Proof. exact (@lem7646411 (NUMERAL 0)). Qed.
Lemma lem7646413 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7646414 : term56 = term199.
Proof. exact (MK_COMB (@lem7646413) (@lem7646412)). Qed.
Lemma lem7646415 : term198 = term200.
Proof. exact (MK_COMB (@lem7646414) (@lem7646409)). Qed.
Lemma lem7646416 : term201.
Proof. exact (@lem1980026 term54 term61 term85 term61). Qed.
Lemma lem7646418 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646419 : term139 = term140.
Proof. exact (@lem7646418 (NUMERAL 0) term12). Qed.
Lemma lem7646420 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646421 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646422 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646421 h1) (fun h1 : term140 = True => @lem7646420)). Qed.
Lemma lem7646423 : term140 = True.
Proof. exact (EQ_MP (@lem7646422) (@lem7646420)). Qed.
Lemma lem7646424 : term139 = True.
Proof. exact (TRANS (@lem7646419) (@lem7646423)). Qed.
Lemma lem7646425 : True = term139.
Proof. exact (SYM (@lem7646424)). Qed.
Lemma lem7646426 : term139.
Proof. exact (EQ_MP (@lem7646425) (@lem0)). Qed.
Lemma lem7646427 : term202.
Proof. exact (@lem7646416 (@lem7646426)). Qed.
Lemma lem7646429 (m : nat) (n : nat) : (term138 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7646430 : term139 = term140.
Proof. exact (@lem7646429 (NUMERAL 0) term12). Qed.
Lemma lem7646431 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646432 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7646433 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646432 h1) (fun h1 : term140 = True => @lem7646431)). Qed.
Lemma lem7646434 : term140 = True.
Proof. exact (EQ_MP (@lem7646433) (@lem7646431)). Qed.
Lemma lem7646435 : term139 = True.
Proof. exact (TRANS (@lem7646430) (@lem7646434)). Qed.
Lemma lem7646436 : True = term139.
Proof. exact (SYM (@lem7646435)). Qed.
Lemma lem7646437 : term139.
Proof. exact (EQ_MP (@lem7646436) (@lem0)). Qed.
Lemma lem7646438 : term200 = term203.
Proof. exact (@lem7646427 (@lem7646437)). Qed.
Lemma lem7646440 (m : nat) (n : nat) : (term114 m n) = (term115 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7646441 : term111 = term116.
Proof. exact (@lem7646440 term12 term12). Qed.
Lemma lem7646442 : (term96 = (BIT1 0)) = (term97 = term12).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7646443 : term97 = term12.
Proof. exact (EQ_MP (@lem7646442) (@lem940073)). Qed.
Lemma lem7646444 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7646445 : term95 = term61.
Proof. exact (MK_COMB (@lem7646444) (@lem7646443)). Qed.
Lemma lem7646446 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7646447 : term116 = term85.
Proof. exact (MK_COMB (@lem7646446) (@lem7646445)). Qed.
Lemma lem7646448 : term111 = term85.
Proof. exact (TRANS (@lem7646441) (@lem7646447)). Qed.
Lemma lem7646450 (x : nat) : (term152 x) = term54.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7646451 : term151 = term54.
Proof. exact (@lem7646450 term12). Qed.
Lemma lem7646452 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7646453 : term204 = term56.
Proof. exact (MK_COMB (@lem7646452) (@lem7646451)). Qed.
Lemma lem7646454 : term203 = term198.
Proof. exact (MK_COMB (@lem7646453) (@lem7646448)). Qed.
Lemma lem7646456 (m : nat) (n : nat) : (term205 m n) = (term206 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7646457 : term198 = term207.
Proof. exact (@lem7646456 (NUMERAL 0) term12). Qed.
Lemma lem7646458 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7646459 (h1 : term141 = (BIT1 0)) : (term12 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7646460 : (term141 = (BIT1 0)) = ((term12 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem7646459 h1) (fun h1 : (term12 = (NUMERAL 0)) = False => @lem7646458)). Qed.
Lemma lem7646461 : (term12 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7646460) (@lem7646458)). Qed.
Lemma lem7646462 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7646463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7646464 : term208 = (and True).
Proof. exact (MK_COMB (@lem7646463) (@lem7646462)). Qed.
Lemma lem7646465 : term207 = (True /\ False).
Proof. exact (MK_COMB (@lem7646464) (@lem7646461)). Qed.
Lemma lem7646467 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7646468 : term207 = False.
Proof. exact (TRANS (@lem7646465) (@lem7646467)). Qed.
Lemma lem7646469 : term198 = False.
Proof. exact (TRANS (@lem7646457) (@lem7646468)). Qed.
Lemma lem7646470 : term203 = False.
Proof. exact (TRANS (@lem7646454) (@lem7646469)). Qed.
Lemma lem7646471 : term200 = False.
Proof. exact (TRANS (@lem7646438) (@lem7646470)). Qed.
Lemma lem7646472 : term198 = False.
Proof. exact (TRANS (@lem7646415) (@lem7646471)). Qed.
Lemma lem7646473 : term197 = False.
Proof. exact (TRANS (@lem7646406) (@lem7646472)). Qed.
Lemma lem7646474 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term391 _98508 _98509 _98510) : False.
Proof. exact (EQ_MP (@lem7646473) (@lem7646403 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646475 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term371 _98508 _98509 _98510) : False.
Proof. exact (or_elim (@lem7645381 _98508 _98509 _98510 h1) (fun h0 : term374 _98509 _98508 _98510 => @lem7646007 _98509 _98508 _98510 h0) (fun h0 : term391 _98508 _98509 _98510 => @lem7646474 _98508 _98509 _98510 h0)). Qed.
Lemma lem7646477 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term371 _98508 _98509 _98510) : term371 _98508 _98509 _98510.
Proof. exact (h1). Qed.
Lemma lem7646478 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term371 _98508 _98509 _98510) : (term371 _98508 _98509 _98510) = False.
Proof. exact (prop_ext (fun h2 : term371 _98508 _98509 _98510 => @lem7646475 _98508 _98509 _98510 h1) (fun h2 : False => @lem7646477 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646479 (_98508 : int) (_98509 : int) (_98510 : int) (h1 : term371 _98508 _98509 _98510) : False.
Proof. exact (EQ_MP (@lem7646478 _98508 _98509 _98510 h1) (@lem7646477 _98508 _98509 _98510 h1)). Qed.
Lemma lem7646480 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term298 _98509 _98508 _98510) : term298 _98509 _98508 _98510.
Proof. exact (h1). Qed.
Lemma lem7646481 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term298 _98509 _98508 _98510) : term371 _98508 _98509 _98510.
Proof. exact (EQ_MP (@lem7645371 _98508 _98509 _98510) (@lem7646480 _98509 _98508 _98510 h1)). Qed.
Lemma lem7646482 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term298 _98509 _98508 _98510) : (term371 _98508 _98509 _98510) = False.
Proof. exact (prop_ext (fun h2 : term371 _98508 _98509 _98510 => @lem7646479 _98508 _98509 _98510 h2) (fun h2 : False => @lem7646481 _98509 _98508 _98510 h1)). Qed.
Lemma lem7646483 (_98509 : int) (_98508 : int) (_98510 : int) (h1 : term298 _98509 _98508 _98510) : False.
Proof. exact (EQ_MP (@lem7646482 _98509 _98508 _98510 h1) (@lem7646481 _98509 _98508 _98510 h1)). Qed.
Lemma lem7646484 (_98509 : int) (_98508 : int) (_98510 : int) : term410 _98509 _98508 _98510.
Proof. exact (fun h0 : term298 _98509 _98508 _98510 => @lem7646483 _98509 _98508 _98510 h0). Qed.
Lemma lem7646485 (_98509 : int) (_98508 : int) (_98510 : int) : term411 _98509 _98508 _98510.
Proof. exact (@lem1386578 (term412 _98509 _98508 _98510)). Qed.
Lemma lem7646488 (_98509 : int) (_98508 : int) (_98510 : int) : term412 _98509 _98508 _98510.
Proof. exact (@lem7646485 _98509 _98508 _98510 (@lem7646484 _98509 _98508 _98510)). Qed.
Lemma lem7646489 (_98510 : int) (_98508 : int) (_98509 : int) : (term297 _98509 _98508 _98510) = (term270 _98510 _98508 _98509).
Proof. exact (SYM (@lem7644602 _98509 _98508 _98510)). Qed.
Lemma lem7646490 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7646491 (_98510 : int) (_98508 : int) (_98509 : int) : (term412 _98509 _98508 _98510) = (term242 _98510 _98508 _98509).
Proof. exact (MK_COMB (@lem7646490) (@lem7646489 _98510 _98508 _98509)). Qed.
Lemma lem7646492 (_98510 : int) (_98508 : int) (_98509 : int) : term242 _98510 _98508 _98509.
Proof. exact (EQ_MP (@lem7646491 _98510 _98508 _98509) (@lem7646488 _98509 _98508 _98510)). Qed.
Lemma lem7646493 (_98510 : int) (_98508 : int) (_98509 : int) : term243 _98510 _98508 _98509.
Proof. exact (EQ_MP (@lem7644383 _98510 _98508 _98509) (@lem7646492 _98510 _98508 _98509)). Qed.
Lemma lem7646494 (i : nat) (a : nat) (b : nat) : term413 i a b.
Proof. exact (@lem7646493 (int_of_num i) (int_of_num a) (int_of_num b)). Qed.
Lemma lem7646495 (i : nat) (a : nat) (b : nat) : term414 i a b.
Proof. exact (@lem7646494 i a b (@lem7644376 a)). Qed.
Lemma lem7646496 (i : nat) (a : nat) (b : nat) : term415 i a b.
Proof. exact (@lem7646495 i a b (@lem7644379 b)). Qed.
Lemma lem7646497 (i : nat) (a : nat) (b : nat) : term241 i a b.
Proof. exact (@lem7646496 i a b (@lem7644382 i)). Qed.
Lemma lem7646498 (i : nat) (a : nat) (b : nat) : (term241 i a b) = (term221 i a b).
Proof. exact (SYM (@lem7644373 i a b)). Qed.
Lemma lem7646499 (i : nat) (a : nat) (b : nat) : term221 i a b.
Proof. exact (EQ_MP (@lem7646498 i a b) (@lem7646497 i a b)). Qed.
Lemma lem7646500 (i : nat) (a : nat) (b : nat) (h1 : term221 i a b) : term221 i a b.
Proof. exact (h1). Qed.
Lemma lem7646501 (i : nat) (b : nat) (h1 : term222 i b) : term222 i b.
Proof. exact (h1). Qed.
Lemma lem7646502 (i : nat) (a : nat) (b : nat) (h1 : term222 i b) (h2 : term221 i a b) : term216 i a b.
Proof. exact (@lem7646500 i a b h2 (@lem7646501 i b h1)). Qed.
Lemma lem7646503 (a : nat) (i : nat) (b : nat) (h1 : term222 i b) : term416 i a b.
Proof. exact (fun h0 : term221 i a b => @lem7646502 i a b h1 h0). Qed.
Lemma lem7646504 (i : nat) (a : nat) (b : nat) (h1 : term221 i a b) : term221 i a b.
Proof. exact (h1). Qed.
Lemma lem7646505 (i : nat) (a : nat) (b : nat) (h1 : term222 i b) (h2 : term221 i a b) : term216 i a b.
Proof. exact (@lem7646503 a i b h1 (@lem7646504 i a b h2)). Qed.
Lemma lem7646506 (i : nat) (a : nat) (b : nat) (h1 : term221 i a b) : term221 i a b.
Proof. exact (fun h0 : term222 i b => @lem7646505 i a b h0 h1). Qed.
Lemma lem7646507 (i : nat) (a : nat) (b : nat) : term417 i a b.
Proof. exact (fun h0 : term221 i a b => @lem7646506 i a b h0). Qed.
Lemma lem7646509 {A B : Type'} (g : nat -> A) (i : nat) : term418 A B g i.
Proof. exact (@lem7622314 A B g i). Qed.
Lemma lem7646510 {A B : Type'} (g : nat -> A) (i : nat) : (term418 A B g i) = (term419 A B g i).
Proof. exact (eq_refl (term418 A B g i)). Qed.
Lemma lem7646511 {A B : Type'} (g : nat -> A) (i : nat) : term419 A B g i.
Proof. exact (EQ_MP (@lem7646510 A B g i) (@lem7646509 A B g i)). Qed.
Lemma lem7646512 {B : Type'} (i : nat) (h1 : term420 B i) : term420 B i.
Proof. exact (h1). Qed.
Lemma lem7646513 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term420 B i) : (term421 A B g i) = (g i).
Proof. exact (@lem7646511 A B g i (@lem7646512 B i h1)). Qed.
Lemma lem7646519 {A B : Type'} (x : cart A B) : term422 A B x.
Proof. exact (@lem7617066 A B x). Qed.
Lemma lem7646520 {A B : Type'} (x : cart A B) : (term422 A B x) = (term423 A B x).
Proof. exact (eq_refl (term422 A B x)). Qed.
Lemma lem7646521 {A B : Type'} (x : cart A B) : term423 A B x.
Proof. exact (EQ_MP (@lem7646520 A B x) (@lem7646519 A B x)). Qed.
Lemma lem7646522 {A B : Type'} (x : cart A B) (y : cart A B) : term424 A B x y.
Proof. exact (@lem7646521 A B x y). Qed.
Lemma lem7646523 {A B : Type'} (x : cart A B) (y : cart A B) : (term424 A B x y) = ((x = y) = (term425 A B x y)).
Proof. exact (eq_refl (term424 A B x y)). Qed.
Lemma lem7646525 {A M N : Type'} (f : type2 A M N) : term426 A M N f.
Proof. exact (@lem7635254 A M N f). Qed.
Lemma lem7646526 {A M N : Type'} (f : type2 A M N) : (term426 A M N f) = ((@sndcart A M N f) = (term427 A M N f)).
Proof. exact (eq_refl (term426 A M N f)). Qed.
Lemma lem7646528 {A M N : Type'} (f : cart A M) : term428 A M N f.
Proof. exact (@lem7632649 A M N f). Qed.
Lemma lem7646529 {A M N : Type'} (f : cart A M) : (term428 A M N f) = (term429 A M N f).
Proof. exact (eq_refl (term428 A M N f)). Qed.
Lemma lem7646530 {A M N : Type'} (f : cart A M) : term429 A M N f.
Proof. exact (EQ_MP (@lem7646529 A M N f) (@lem7646528 A M N f)). Qed.
Lemma lem7646531 {A M N : Type'} (f : cart A M) (g : cart A N) : term430 A M N f g.
Proof. exact (@lem7646530 A M N f g). Qed.
Lemma lem7646532 {A M N : Type'} (f : cart A M) (g : cart A N) : (term430 A M N f g) = ((@pastecart A M N f g) = (term431 A M N f g)).
Proof. exact (eq_refl (term430 A M N f g)). Qed.
Lemma lem7646545 {A B : Type'} (x : cart A B) (y : cart A B) : (x = y) = (term425 A B x y).
Proof. exact (EQ_MP (@lem7646523 A B x y) (@lem7646522 A B x y)). Qed.
Lemma lem7646546 {A N : Type'} (x : cart A N) (y : cart A N) : (x = y) = (term425 A N x y).
Proof. exact (@lem7646545 A N x y). Qed.
Lemma lem7646547 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term432 A M N x y) = y) = (term433 A M N x y).
Proof. exact (@lem7646546 A N (term432 A M N x y) y). Qed.
Lemma lem7646555 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term434 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7646556 (p : Prop) (q : Prop) (p' : Prop) : term435 p q p'.
Proof. exact (fun q' : Prop => @lem7646555 p q p' q'). Qed.
Lemma lem7646557 (p : Prop) (q : Prop) : term436 p q.
Proof. exact (fun p' : Prop => @lem7646556 p q p'). Qed.
Lemma lem7646558 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : term437 A M N x y i.
Proof. exact (@lem7646557 (term420 N i) ((term438 A M N x y i) = (@dollar A N y i))). Qed.
Lemma lem7646559 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (p' : Prop) : term439 A M N x y i p'.
Proof. exact (@lem7646558 A M N x y i p'). Qed.
Lemma lem7646560 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (p' : Prop) : (term439 A M N x y i p') = (term440 A M N x y i p').
Proof. exact (eq_refl (term439 A M N x y i p')). Qed.
Lemma lem7646561 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (p' : Prop) : term440 A M N x y i p'.
Proof. exact (EQ_MP (@lem7646560 A M N x y i p') (@lem7646559 A M N x y i p')). Qed.
Lemma lem7646562 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (p' : Prop) (q' : Prop) : term441 A M N x y i p' q'.
Proof. exact (@lem7646561 A M N x y i p' q'). Qed.
Lemma lem7646563 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (p' : Prop) (q' : Prop) : (term441 A M N x y i p' q') = (term442 A M N x y i p' q').
Proof. exact (eq_refl (term441 A M N x y i p' q')). Qed.
Lemma lem7646564 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (p' : Prop) (q' : Prop) : term442 A M N x y i p' q'.
Proof. exact (EQ_MP (@lem7646563 A M N x y i p' q') (@lem7646562 A M N x y i p' q')). Qed.
Lemma lem7646567 {N : Type'} (i : nat) : (term420 N i) = (term420 N i).
Proof. exact (eq_refl (term420 N i)). Qed.
Lemma lem7646568 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (q' : Prop) : term443 A M N x y i q'.
Proof. exact (@lem7646564 A M N x y i (term420 N i) q'). Qed.
Lemma lem7646569 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (q' : Prop) : term444 A M N x y i q'.
Proof. exact (@lem7646568 A M N x y i q' (@lem7646567 N i)). Qed.
Lemma lem7646570 {N : Type'} (i : nat) (h1 : term420 N i) : term420 N i.
Proof. exact (h1). Qed.
Lemma lem7646571 {N : Type'} (i : nat) (h1 : term420 N i) : term445 N i.
Proof. exact (proj2 (@lem7646570 N i h1)). Qed.
Lemma lem7646572 {N : Type'} (i : nat) : (term445 N i) = ((term445 N i) = True).
Proof. exact (@lem7 (term445 N i)). Qed.
Lemma lem7646574 {N : Type'} (i : nat) (h1 : term420 N i) : term2 i.
Proof. exact (proj1 (@lem7646570 N i h1)). Qed.
Lemma lem7646575 (i : nat) : (term2 i) = ((term2 i) = True).
Proof. exact (@lem7 (term2 i)). Qed.
Lemma lem7646582 {A M N : Type'} (f : type2 A M N) : (@sndcart A M N f) = (term427 A M N f).
Proof. exact (EQ_MP (@lem7646526 A M N f) (@lem7646525 A M N f)). Qed.
Lemma lem7646583 {A M N : Type'} (f : type2 A M N) : (@sndcart A M N f) = (term427 A M N f).
Proof. exact (@lem7646582 A M N f). Qed.
Lemma lem7646584 {A M N : Type'} (x : cart A M) (y : cart A N) : (term432 A M N x y) = (term446 A M N x y).
Proof. exact (@lem7646583 A M N (@pastecart A M N x y)). Qed.
Lemma lem7646586 {A M N : Type'} (f : cart A M) (g : cart A N) : (@pastecart A M N f g) = (term431 A M N f g).
Proof. exact (EQ_MP (@lem7646532 A M N f g) (@lem7646531 A M N f g)). Qed.
Lemma lem7646587 {A M N : Type'} (f : cart A M) (g : cart A N) : (@pastecart A M N f g) = (term431 A M N f g).
Proof. exact (@lem7646586 A M N f g). Qed.
Lemma lem7646588 {A M N : Type'} (x : cart A M) (y : cart A N) : (@pastecart A M N x y) = (term431 A M N x y).
Proof. exact (@lem7646587 A M N x y). Qed.
Lemma lem7646628 {A M N : Type'} : (@dollar A (finite_sum M N)) = (@dollar A (finite_sum M N)).
Proof. exact (eq_refl (@dollar A (finite_sum M N))). Qed.
Lemma lem7646629 {A M N : Type'} (x : cart A M) (y : cart A N) : (term447 A M N x y) = (term448 A M N x y).
Proof. exact (MK_COMB (@lem7646628 A M N) (@lem7646588 A M N x y)). Qed.
Lemma lem7646669 {M : Type'} (i : nat) : (term449 M i) = (term449 M i).
Proof. exact (eq_refl (term449 M i)). Qed.
Lemma lem7646670 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term450 A M N x y i) = (term451 A M N x y i).
Proof. exact (MK_COMB (@lem7646629 A M N x y) (@lem7646669 M i)). Qed.
Lemma lem7646718 {A M N : Type'} (x : cart A M) (y : cart A N) : (term452 A M N x y) = (term453 A M N x y).
Proof. exact (fun_ext (fun i : nat => @lem7646670 A M N x y i)). Qed.
Lemma lem7646766 {A N : Type'} : (@lambda A N) = (@lambda A N).
Proof. exact (eq_refl (@lambda A N)). Qed.
Lemma lem7646767 {A M N : Type'} (x : cart A M) (y : cart A N) : (term446 A M N x y) = (term454 A M N x y).
Proof. exact (MK_COMB (@lem7646766 A N) (@lem7646718 A M N x y)). Qed.
Lemma lem7646815 {A M N : Type'} (x : cart A M) (y : cart A N) : (term432 A M N x y) = (term454 A M N x y).
Proof. exact (TRANS (@lem7646584 A M N x y) (@lem7646767 A M N x y)). Qed.
Lemma lem7646816 {A N : Type'} : (@dollar A N) = (@dollar A N).
Proof. exact (eq_refl (@dollar A N)). Qed.
Lemma lem7646817 {A M N : Type'} (x : cart A M) (y : cart A N) : (term455 A M N x y) = (term456 A M N x y).
Proof. exact (MK_COMB (@lem7646816 A N) (@lem7646815 A M N x y)). Qed.
Lemma lem7646865 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7646866 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term438 A M N x y i) = (term457 A M N x y i).
Proof. exact (MK_COMB (@lem7646817 A M N x y) (@lem7646865 i)). Qed.
Lemma lem7646868 {A B : Type'} (g : nat -> A) (i : nat) : term419 A B g i.
Proof. exact (fun h0 : term420 B i => @lem7646513 A B g i h0). Qed.
Lemma lem7646869 {A N : Type'} (g : nat -> A) (i : nat) : term419 A N g i.
Proof. exact (@lem7646868 A N g i). Qed.
Lemma lem7646870 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : term458 A M N x y i.
Proof. exact (@lem7646869 A N (term453 A M N x y) i). Qed.
Lemma lem7646874 {N : Type'} (i : nat) (h1 : term420 N i) : (term2 i) = True.
Proof. exact (EQ_MP (@lem7646575 i) (@lem7646574 N i h1)). Qed.
Lemma lem7646875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7646876 {N : Type'} (i : nat) (h1 : term420 N i) : (term459 i) = (and True).
Proof. exact (MK_COMB (@lem7646875) (@lem7646874 N i h1)). Qed.
Lemma lem7646878 {N : Type'} (i : nat) (h1 : term420 N i) : (term445 N i) = True.
Proof. exact (EQ_MP (@lem7646572 N i) (@lem7646571 N i h1)). Qed.
Lemma lem7646879 {N : Type'} (i : nat) (h1 : term420 N i) : (term420 N i) = (True /\ True).
Proof. exact (MK_COMB (@lem7646876 N i h1) (@lem7646878 N i h1)). Qed.
Lemma lem7646881 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7646882 : (True /\ True) = True.
Proof. exact (@lem7646881 True). Qed.
Lemma lem7646883 {N : Type'} (i : nat) (h1 : term420 N i) : (term420 N i) = True.
Proof. exact (TRANS (@lem7646879 N i h1) (@lem7646882)). Qed.
Lemma lem7646884 {N : Type'} (i : nat) (h1 : term420 N i) : True = (term420 N i).
Proof. exact (SYM (@lem7646883 N i h1)). Qed.
Lemma lem7646885 {N : Type'} (i : nat) (h1 : term420 N i) : term420 N i.
Proof. exact (EQ_MP (@lem7646884 N i h1) (@lem0)). Qed.
Lemma lem7646886 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term420 N i) : (term457 A M N x y i) = (term460 A M N x y i).
Proof. exact (@lem7646870 A M N x y i (@lem7646885 N i h1)). Qed.
Lemma lem7646888 {A B : Type'} (f : A -> B) (y : A) : (term461 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7646889 {A : Type'} (f : nat -> A) (y : nat) : (term462 A f y) = (f y).
Proof. exact (@lem7646888 nat A f y). Qed.
Lemma lem7646890 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term463 A M N x y i) = (term460 A M N x y i).
Proof. exact (@lem7646889 A (term453 A M N x y) i). Qed.
Lemma lem7646891 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term460 A M N x y i) = (term451 A M N x y i).
Proof. exact (eq_refl (term460 A M N x y i)). Qed.
Lemma lem7646892 {A M N : Type'} (x : cart A M) (y : cart A N) : (term464 A M N x y) = (term453 A M N x y).
Proof. exact (fun_ext (fun i : nat => @lem7646891 A M N x y i)). Qed.
Lemma lem7646893 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7646894 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term463 A M N x y i) = (term460 A M N x y i).
Proof. exact (MK_COMB (@lem7646892 A M N x y) (@lem7646893 i)). Qed.
Lemma lem7646895 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7646896 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term465 A M N x y i) = (term466 A M N x y i).
Proof. exact (MK_COMB (@lem7646895 A) (@lem7646894 A M N x y i)). Qed.
Lemma lem7646897 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term460 A M N x y i) = (term451 A M N x y i).
Proof. exact (eq_refl (term460 A M N x y i)). Qed.
Lemma lem7646898 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : ((term463 A M N x y i) = (term460 A M N x y i)) = ((term460 A M N x y i) = (term451 A M N x y i)).
Proof. exact (MK_COMB (@lem7646896 A M N x y i) (@lem7646897 A M N x y i)). Qed.
Lemma lem7646899 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term460 A M N x y i) = (term451 A M N x y i).
Proof. exact (EQ_MP (@lem7646898 A M N x y i) (@lem7646890 A M N x y i)). Qed.
Lemma lem7646947 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term420 N i) : (term457 A M N x y i) = (term451 A M N x y i).
Proof. exact (TRANS (@lem7646886 A M N x y i h1) (@lem7646899 A M N x y i)). Qed.
Lemma lem7646948 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term420 N i) : (term438 A M N x y i) = (term451 A M N x y i).
Proof. exact (TRANS (@lem7646866 A M N x y i) (@lem7646947 A M N x y i h1)). Qed.
Lemma lem7646949 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7646950 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term420 N i) : (term467 A M N x y i) = (term468 A M N x y i).
Proof. exact (MK_COMB (@lem7646949 A) (@lem7646948 A M N x y i h1)). Qed.
Lemma lem7646998 {A N : Type'} (y : cart A N) (i : nat) : (@dollar A N y i) = (@dollar A N y i).
Proof. exact (eq_refl (@dollar A N y i)). Qed.
Lemma lem7646999 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term420 N i) : ((term438 A M N x y i) = (@dollar A N y i)) = ((term451 A M N x y i) = (@dollar A N y i)).
Proof. exact (MK_COMB (@lem7646950 A M N x y i h1) (@lem7646998 A N y i)). Qed.
Lemma lem7647051 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : term469 A M N x y i.
Proof. exact (fun h0 : term420 N i => @lem7646999 A M N x y i h0). Qed.
Lemma lem7647052 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : term470 A M N x y i.
Proof. exact (@lem7646569 A M N x y i ((term451 A M N x y i) = (@dollar A N y i))). Qed.
Lemma lem7647053 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term471 A M N x y i) = (term472 A M N x y i).
Proof. exact (@lem7647052 A M N x y i (@lem7647051 A M N x y i)). Qed.
Lemma lem7647181 {A M N : Type'} (x : cart A M) (y : cart A N) : (term473 A M N x y) = (term474 A M N x y).
Proof. exact (fun_ext (fun i : nat => @lem7647053 A M N x y i)). Qed.
Lemma lem7647309 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7647310 {A M N : Type'} (x : cart A M) (y : cart A N) : (term433 A M N x y) = (term475 A M N x y).
Proof. exact (MK_COMB (@lem7647309) (@lem7647181 A M N x y)). Qed.
Lemma lem7647442 {A M N : Type'} (x : cart A M) (y : cart A N) : ((term432 A M N x y) = y) = (term475 A M N x y).
Proof. exact (TRANS (@lem7646547 A M N x y) (@lem7647310 A M N x y)). Qed.
Lemma lem7647443 {A M N : Type'} (x : cart A M) : (term476 A M N x) = (term477 A M N x).
Proof. exact (fun_ext (fun y : cart A N => @lem7647442 A M N x y)). Qed.
Lemma lem7647575 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem7647576 {A M N : Type'} (x : cart A M) : (term478 A M N x) = (term479 A M N x).
Proof. exact (MK_COMB (@lem7647575 A N) (@lem7647443 A M N x)). Qed.
Lemma lem7647712 {A M N : Type'} : (term480 A M N) = (term481 A M N).
Proof. exact (fun_ext (fun x : cart A M => @lem7647576 A M N x)). Qed.
Lemma lem7647848 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem7647849 {A M N : Type'} : (term482 A M N) = (term483 A M N).
Proof. exact (MK_COMB (@lem7647848 A M) (@lem7647712 A M N)). Qed.
Lemma lem7647989 {A M N : Type'} : (term483 A M N) = (term482 A M N).
Proof. exact (SYM (@lem7647849 A M N)). Qed.
Lemma lem7647990 {N : Type'} (i : nat) (h1 : term420 N i) : term420 N i.
Proof. exact (h1). Qed.
Lemma lem7647991 {N : Type'} (i : nat) (h1 : term445 N i) : term445 N i.
Proof. exact (h1). Qed.
Lemma lem7647992 (i : nat) (h1 : term2 i) : term2 i.
Proof. exact (h1). Qed.
Lemma lem7647993 {A B : Type'} (g : nat -> A) (i : nat) : term418 A B g i.
Proof. exact (@lem7622314 A B g i). Qed.
Lemma lem7647994 {A B : Type'} (g : nat -> A) (i : nat) : (term418 A B g i) = (term419 A B g i).
Proof. exact (eq_refl (term418 A B g i)). Qed.
Lemma lem7647997 {A B : Type'} (g : nat -> A) (i : nat) : term419 A B g i.
Proof. exact (EQ_MP (@lem7647994 A B g i) (@lem7647993 A B g i)). Qed.
Lemma lem7647998 {A M N : Type'} (g : nat -> A) (i : nat) : term484 A M N g i.
Proof. exact (@lem7647997 A (finite_sum M N) g i). Qed.
Lemma lem7647999 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : term485 A M N x y i.
Proof. exact (@lem7647998 A M N (term486 A M N x y) (term449 M i)). Qed.
Lemma lem7648001 (p : Prop) (q : Prop) (r : Prop) : term487 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem7648002 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : term488 A M N x y i.
Proof. exact (@lem7648001 (term489 M N i) ((term451 A M N x y i) = (term490 A M N x y i)) ((term451 A M N x y i) = (@dollar A N y i))). Qed.
Lemma lem7648010 {M N : Type'} : (@dimindex (finite_sum M N) (@UNIV (finite_sum M N))) = (term491 M N).
Proof. exact (EQ_MP (@lem7640410 M N) (@lem7640437 M N)). Qed.
Lemma lem7648015 {M : Type'} (i : nat) : (term492 M i) = (term492 M i).
Proof. exact (eq_refl (term492 M i)). Qed.
Lemma lem7648016 {M N : Type'} (i : nat) : (term493 M N i) = (term494 M N i).
Proof. exact (MK_COMB (@lem7648015 M i) (@lem7648010 M N)). Qed.
Lemma lem7648017 {M : Type'} (i : nat) : (term495 M i) = (term495 M i).
Proof. exact (eq_refl (term495 M i)). Qed.
Lemma lem7648018 {M N : Type'} (i : nat) : (term489 M N i) = (term496 M N i).
Proof. exact (MK_COMB (@lem7648017 M i) (@lem7648016 M N i)). Qed.
Lemma lem7648021 {M N : Type'} (i : nat) : (term496 M N i) = (term489 M N i).
Proof. exact (SYM (@lem7648018 M N i)). Qed.
Lemma lem7648023 (i : nat) (a : nat) (b : nat) : term221 i a b.
Proof. exact (@lem7646507 i a b (@lem7646499 i a b)). Qed.
Lemma lem7648024 {M N : Type'} (i : nat) : term497 M N i.
Proof. exact (@lem7648023 i (@dimindex M (@UNIV M)) (@dimindex N (@UNIV N))). Qed.
Lemma lem7648025 (i : nat) : (term2 i) = ((term2 i) = True).
Proof. exact (@lem7 (term2 i)). Qed.
Lemma lem7648027 {N : Type'} (i : nat) : (term445 N i) = ((term445 N i) = True).
Proof. exact (@lem7 (term445 N i)). Qed.
Lemma lem7648032 (i : nat) (h1 : term2 i) : (term2 i) = True.
Proof. exact (EQ_MP (@lem7648025 i) (@lem7647992 i h1)). Qed.
Lemma lem7648033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7648034 (i : nat) (h1 : term2 i) : (term459 i) = (and True).
Proof. exact (MK_COMB (@lem7648033) (@lem7648032 i h1)). Qed.
Lemma lem7648036 {N : Type'} (i : nat) (h1 : term445 N i) : (term445 N i) = True.
Proof. exact (EQ_MP (@lem7648027 N i) (@lem7647991 N i h1)). Qed.
Lemma lem7648037 {N : Type'} (i : nat) (h1 : term445 N i) (h2 : term2 i) : (term420 N i) = (True /\ True).
Proof. exact (MK_COMB (@lem7648034 i h2) (@lem7648036 N i h1)). Qed.
Lemma lem7648039 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7648040 : (True /\ True) = True.
Proof. exact (@lem7648039 True). Qed.
Lemma lem7648041 {N : Type'} (i : nat) (h1 : term445 N i) (h2 : term2 i) : (term420 N i) = True.
Proof. exact (TRANS (@lem7648037 N i h1 h2) (@lem7648040)). Qed.
Lemma lem7648042 {N : Type'} (i : nat) (h1 : term445 N i) (h2 : term2 i) : True = (term420 N i).
Proof. exact (SYM (@lem7648041 N i h1 h2)). Qed.
Lemma lem7648043 {N : Type'} (i : nat) (h1 : term445 N i) (h2 : term2 i) : term420 N i.
Proof. exact (EQ_MP (@lem7648042 N i h1 h2) (@lem0)). Qed.
Lemma lem7648044 {M N : Type'} (i : nat) (h1 : term445 N i) (h2 : term2 i) : term496 M N i.
Proof. exact (@lem7648024 M N i (@lem7648043 N i h1 h2)). Qed.
Lemma lem7648045 {M N : Type'} (i : nat) (h1 : term445 N i) (h2 : term2 i) : term489 M N i.
Proof. exact (EQ_MP (@lem7648021 M N i) (@lem7648044 M N i h1 h2)). Qed.
Lemma lem7648046 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : (term451 A M N x y i) = (term490 A M N x y i)) : (term451 A M N x y i) = (term490 A M N x y i).
Proof. exact (h1). Qed.
Lemma lem7648047 {A N : Type'} (y : cart A N) (i : nat) : (term498 A N y i) = (term498 A N y i).
Proof. exact (eq_refl (term498 A N y i)). Qed.
Lemma lem7648048 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : (term451 A M N x y i) = (term490 A M N x y i)) : (term499 A M N x y i) = (term500 A M N x y i).
Proof. exact (MK_COMB (@lem7648047 A N y i) (@lem7648046 A M N x y i h1)). Qed.
Lemma lem7648049 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term500 A M N x y i) = ((term490 A M N x y i) = (@dollar A N y i)).
Proof. exact (eq_refl (term500 A M N x y i)). Qed.
Lemma lem7648050 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term501 A M N x y i) = (term501 A M N x y i).
Proof. exact (eq_refl (term501 A M N x y i)). Qed.
Lemma lem7648051 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : ((term499 A M N x y i) = (term500 A M N x y i)) = ((term499 A M N x y i) = ((term490 A M N x y i) = (@dollar A N y i))).
Proof. exact (MK_COMB (@lem7648050 A M N x y i) (@lem7648049 A M N x y i)). Qed.
Lemma lem7648052 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term499 A M N x y i) = ((term451 A M N x y i) = (@dollar A N y i)).
Proof. exact (eq_refl (term499 A M N x y i)). Qed.
Lemma lem7648053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7648054 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term501 A M N x y i) = (term502 A M N x y i).
Proof. exact (MK_COMB (@lem7648053) (@lem7648052 A M N x y i)). Qed.
Lemma lem7648055 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : ((term490 A M N x y i) = (@dollar A N y i)) = ((term490 A M N x y i) = (@dollar A N y i)).
Proof. exact (eq_refl ((term490 A M N x y i) = (@dollar A N y i))). Qed.
Lemma lem7648056 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : ((term499 A M N x y i) = ((term490 A M N x y i) = (@dollar A N y i))) = (((term451 A M N x y i) = (@dollar A N y i)) = ((term490 A M N x y i) = (@dollar A N y i))).
Proof. exact (MK_COMB (@lem7648054 A M N x y i) (@lem7648055 A M N x y i)). Qed.
Lemma lem7648057 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : ((term499 A M N x y i) = (term500 A M N x y i)) = (((term451 A M N x y i) = (@dollar A N y i)) = ((term490 A M N x y i) = (@dollar A N y i))).
Proof. exact (TRANS (@lem7648051 A M N x y i) (@lem7648056 A M N x y i)). Qed.
Lemma lem7648058 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : (term451 A M N x y i) = (term490 A M N x y i)) : ((term451 A M N x y i) = (@dollar A N y i)) = ((term490 A M N x y i) = (@dollar A N y i)).
Proof. exact (EQ_MP (@lem7648057 A M N x y i) (@lem7648048 A M N x y i h1)). Qed.
Lemma lem7648059 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : (term451 A M N x y i) = (term490 A M N x y i)) : ((term490 A M N x y i) = (@dollar A N y i)) = ((term451 A M N x y i) = (@dollar A N y i)).
Proof. exact (SYM (@lem7648058 A M N x y i h1)). Qed.
Lemma lem7648063 {A B : Type'} (f : A -> B) (y : A) : (term461 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7648064 {A : Type'} (f : nat -> A) (y : nat) : (term462 A f y) = (f y).
Proof. exact (@lem7648063 nat A f y). Qed.
Lemma lem7648065 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term503 A M N x y i) = (term490 A M N x y i).
Proof. exact (@lem7648064 A (term486 A M N x y) (term449 M i)). Qed.
Lemma lem7648066 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term504 A M N x y i) = (term505 A M N x y i).
Proof. exact (eq_refl (term504 A M N x y i)). Qed.
Lemma lem7648067 {A M N : Type'} (x : cart A M) (y : cart A N) : (term506 A M N x y) = (term486 A M N x y).
Proof. exact (fun_ext (fun i : nat => @lem7648066 A M N x y i)). Qed.
Lemma lem7648068 {M : Type'} (i : nat) : (term449 M i) = (term449 M i).
Proof. exact (eq_refl (term449 M i)). Qed.
Lemma lem7648069 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term503 A M N x y i) = (term490 A M N x y i).
Proof. exact (MK_COMB (@lem7648067 A M N x y) (@lem7648068 M i)). Qed.
Lemma lem7648070 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7648071 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term507 A M N x y i) = (term508 A M N x y i).
Proof. exact (MK_COMB (@lem7648070 A) (@lem7648069 A M N x y i)). Qed.
Lemma lem7648072 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term490 A M N x y i) = (term509 A M N x y i).
Proof. exact (eq_refl (term490 A M N x y i)). Qed.
Lemma lem7648073 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : ((term503 A M N x y i) = (term490 A M N x y i)) = ((term490 A M N x y i) = (term509 A M N x y i)).
Proof. exact (MK_COMB (@lem7648071 A M N x y i) (@lem7648072 A M N x y i)). Qed.
Lemma lem7648074 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term490 A M N x y i) = (term509 A M N x y i).
Proof. exact (EQ_MP (@lem7648073 A M N x y i) (@lem7648065 A M N x y i)). Qed.
Lemma lem7648075 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7648076 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term508 A M N x y i) = (term510 A M N x y i).
Proof. exact (MK_COMB (@lem7648075 A) (@lem7648074 A M N x y i)). Qed.
Lemma lem7648077 {A N : Type'} (y : cart A N) (i : nat) : (@dollar A N y i) = (@dollar A N y i).
Proof. exact (eq_refl (@dollar A N y i)). Qed.
Lemma lem7648078 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : ((term490 A M N x y i) = (@dollar A N y i)) = ((term509 A M N x y i) = (@dollar A N y i)).
Proof. exact (MK_COMB (@lem7648076 A M N x y i) (@lem7648077 A N y i)). Qed.
Lemma lem7648081 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : ((term509 A M N x y i) = (@dollar A N y i)) = ((term490 A M N x y i) = (@dollar A N y i)).
Proof. exact (SYM (@lem7648078 A M N x y i)). Qed.
Lemma lem7648082 (i : nat) (h1 : term2 i) : term2 i.
Proof. exact (h1). Qed.
Lemma lem7648083 (a : nat) (i : nat) (h1 : term2 i) : term3 i a.
Proof. exact (@lem7644224 i a (@lem7648082 i h1)). Qed.
Lemma lem7648084 (i : nat) (a : nat) : term511 i a.
Proof. exact (@lem82 (term5 i a)). Qed.
Lemma lem7648085 (a : nat) (i : nat) (h1 : term2 i) : (term5 i a) = False.
Proof. exact (@lem7648084 i a (@lem7648083 a i h1)). Qed.
Lemma lem7648091 (m : nat) : term512 m.
Proof. exact (@lem135886 m). Qed.
Lemma lem7648092 (m : nat) : (term512 m) = (term513 m).
Proof. exact (eq_refl (term512 m)). Qed.
Lemma lem7648093 (m : nat) : term513 m.
Proof. exact (EQ_MP (@lem7648092 m) (@lem7648091 m)). Qed.
Lemma lem7648094 (m : nat) (n : nat) : term514 m n.
Proof. exact (@lem7648093 m n). Qed.
Lemma lem7648095 (n : nat) (m : nat) : (term514 m n) = ((term515 m n) = m).
Proof. exact (eq_refl (term514 m n)). Qed.
Lemma lem7648097 (i : nat) : (term2 i) = ((term2 i) = True).
Proof. exact (@lem7 (term2 i)). Qed.
Lemma lem7648104 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term516 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7648105 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term517 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7648104 _2963 g t e g' t' e'). Qed.
Lemma lem7648106 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term518 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7648105 _2963 g t e g' t'). Qed.
Lemma lem7648107 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term519 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7648106 _2963 g t e g'). Qed.
Lemma lem7648108 {A : Type'} (g : Prop) (t : A) (e : A) : term519 A g t e.
Proof. exact (@lem7648107 A g t e). Qed.
Lemma lem7648109 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : term520 A M N x y i.
Proof. exact (@lem7648108 A (term521 M i) (term522 A M x i) (term523 A M N y i)). Qed.
Lemma lem7648110 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) : term524 A M N x y i g'.
Proof. exact (@lem7648109 A M N x y i g'). Qed.
Lemma lem7648111 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) : (term524 A M N x y i g') = (term525 A M N x y i g').
Proof. exact (eq_refl (term524 A M N x y i g')). Qed.
Lemma lem7648112 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) : term525 A M N x y i g'.
Proof. exact (EQ_MP (@lem7648111 A M N x y i g') (@lem7648110 A M N x y i g')). Qed.
Lemma lem7648113 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) (t' : A) : term526 A M N x y i g' t'.
Proof. exact (@lem7648112 A M N x y i g' t'). Qed.
Lemma lem7648114 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) (t' : A) : (term526 A M N x y i g' t') = (term527 A M N x y i g' t').
Proof. exact (eq_refl (term526 A M N x y i g' t')). Qed.
Lemma lem7648115 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) (t' : A) : term527 A M N x y i g' t'.
Proof. exact (EQ_MP (@lem7648114 A M N x y i g' t') (@lem7648113 A M N x y i g' t')). Qed.
Lemma lem7648116 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) (t' : A) (e' : A) : term528 A M N x y i g' t' e'.
Proof. exact (@lem7648115 A M N x y i g' t' e'). Qed.
Lemma lem7648117 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) (t' : A) (e' : A) : (term528 A M N x y i g' t' e') = (term529 A M N x y i g' t' e').
Proof. exact (eq_refl (term528 A M N x y i g' t' e')). Qed.
Lemma lem7648118 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (g' : Prop) (t' : A) (e' : A) : term529 A M N x y i g' t' e'.
Proof. exact (EQ_MP (@lem7648117 A M N x y i g' t' e') (@lem7648116 A M N x y i g' t' e')). Qed.
Lemma lem7648120 (i : nat) (a : nat) : term530 i a.
Proof. exact (fun h0 : term2 i => @lem7648085 a i h0). Qed.
Lemma lem7648121 {M : Type'} (i : nat) : term531 M i.
Proof. exact (@lem7648120 i (@dimindex M (@UNIV M))). Qed.
Lemma lem7648123 (i : nat) (h1 : term2 i) : (term2 i) = True.
Proof. exact (EQ_MP (@lem7648097 i) (@lem7647992 i h1)). Qed.
Lemma lem7648124 (i : nat) (h1 : term2 i) : True = (term2 i).
Proof. exact (SYM (@lem7648123 i h1)). Qed.
Lemma lem7648125 (i : nat) (h1 : term2 i) : term2 i.
Proof. exact (EQ_MP (@lem7648124 i h1) (@lem0)). Qed.
Lemma lem7648126 {M : Type'} (i : nat) (h1 : term2 i) : (term521 M i) = False.
Proof. exact (@lem7648121 M i (@lem7648125 i h1)). Qed.
Lemma lem7648127 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (t' : A) (e' : A) : term532 A M N x y i t' e'.
Proof. exact (@lem7648118 A M N x y i False t' e'). Qed.
Lemma lem7648128 {A M N : Type'} (x : cart A M) (y : cart A N) (t' : A) (e' : A) (i : nat) (h1 : term2 i) : term533 A M N x y i t' e'.
Proof. exact (@lem7648127 A M N x y i t' e' (@lem7648126 M i h1)). Qed.
Lemma lem7648132 {A M : Type'} (x : cart A M) (i : nat) : (term522 A M x i) = (term522 A M x i).
Proof. exact (eq_refl (term522 A M x i)). Qed.
Lemma lem7648133 {A M : Type'} (x : cart A M) (i : nat) : term534 A M x i.
Proof. exact (fun h0 : False => @lem7648132 A M x i). Qed.
Lemma lem7648134 {A M N : Type'} (y : cart A N) (x : cart A M) (e' : A) (i : nat) (h1 : term2 i) : term535 A M N y x i e'.
Proof. exact (@lem7648128 A M N x y (term522 A M x i) e' i h1). Qed.
Lemma lem7648135 {A M N : Type'} (y : cart A N) (x : cart A M) (e' : A) (i : nat) (h1 : term2 i) : term536 A M N y x i e'.
Proof. exact (@lem7648134 A M N y x e' i h1 (@lem7648133 A M x i)). Qed.
Lemma lem7648142 (n : nat) (m : nat) : (term515 m n) = m.
Proof. exact (EQ_MP (@lem7648095 n m) (@lem7648094 m n)). Qed.
Lemma lem7648143 {M : Type'} (i : nat) : (term537 M i) = i.
Proof. exact (@lem7648142 (@dimindex M (@UNIV M)) i). Qed.
Lemma lem7648144 {A N : Type'} (y : cart A N) : (@dollar A N y) = (@dollar A N y).
Proof. exact (eq_refl (@dollar A N y)). Qed.
Lemma lem7648145 {A M N : Type'} (y : cart A N) (i : nat) : (term523 A M N y i) = (@dollar A N y i).
Proof. exact (MK_COMB (@lem7648144 A N y) (@lem7648143 M i)). Qed.
Lemma lem7648146 {A M N : Type'} (y : cart A N) (i : nat) : term538 A M N y i.
Proof. exact (fun h0 : ~ False => @lem7648145 A M N y i). Qed.
Lemma lem7648147 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term2 i) : term539 A M N x y i.
Proof. exact (@lem7648135 A M N y x (@dollar A N y i) i h1). Qed.
Lemma lem7648148 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term2 i) : (term509 A M N x y i) = (term540 A M N x y i).
Proof. exact (@lem7648147 A M N x y i h1 (@lem7648146 A M N y i)). Qed.
Lemma lem7648150 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7648151 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem7648150 A t1 t2). Qed.
Lemma lem7648152 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : (term540 A M N x y i) = (@dollar A N y i).
Proof. exact (@lem7648151 A (term522 A M x i) (@dollar A N y i)). Qed.
Lemma lem7648153 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term2 i) : (term509 A M N x y i) = (@dollar A N y i).
Proof. exact (TRANS (@lem7648148 A M N x y i h1) (@lem7648152 A M N x y i)). Qed.
Lemma lem7648154 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7648155 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term2 i) : (term510 A M N x y i) = (term541 A N y i).
Proof. exact (MK_COMB (@lem7648154 A) (@lem7648153 A M N x y i h1)). Qed.
Lemma lem7648156 {A N : Type'} (y : cart A N) (i : nat) : (@dollar A N y i) = (@dollar A N y i).
Proof. exact (eq_refl (@dollar A N y i)). Qed.
Lemma lem7648157 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term2 i) : ((term509 A M N x y i) = (@dollar A N y i)) = ((@dollar A N y i) = (@dollar A N y i)).
Proof. exact (MK_COMB (@lem7648155 A M N x y i h1) (@lem7648156 A N y i)). Qed.
Lemma lem7648159 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7648160 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem7648159 A x). Qed.
Lemma lem7648161 {A N : Type'} (y : cart A N) (i : nat) : ((@dollar A N y i) = (@dollar A N y i)) = True.
Proof. exact (@lem7648160 A (@dollar A N y i)). Qed.
Lemma lem7648162 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term2 i) : ((term509 A M N x y i) = (@dollar A N y i)) = True.
Proof. exact (TRANS (@lem7648157 A M N x y i h1) (@lem7648161 A N y i)). Qed.
Lemma lem7648163 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term2 i) : True = ((term509 A M N x y i) = (@dollar A N y i)).
Proof. exact (SYM (@lem7648162 A M N x y i h1)). Qed.
Lemma lem7648164 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term2 i) : (term509 A M N x y i) = (@dollar A N y i).
Proof. exact (EQ_MP (@lem7648163 A M N x y i h1) (@lem0)). Qed.
Lemma lem7648165 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term2 i) : (term490 A M N x y i) = (@dollar A N y i).
Proof. exact (EQ_MP (@lem7648081 A M N x y i) (@lem7648164 A M N x y i h1)). Qed.
Lemma lem7648166 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term2 i) (h2 : (term451 A M N x y i) = (term490 A M N x y i)) : (term451 A M N x y i) = (@dollar A N y i).
Proof. exact (EQ_MP (@lem7648059 A M N x y i h2) (@lem7648165 A M N x y i h1)). Qed.
Lemma lem7648167 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term2 i) : term542 A M N x y i.
Proof. exact (fun h0 : (term451 A M N x y i) = (term490 A M N x y i) => @lem7648166 A M N x y i h1 h0). Qed.
Lemma lem7648168 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term445 N i) (h2 : term2 i) : term543 A M N x y i.
Proof. exact (conj (@lem7648045 M N i h1 h2) (@lem7648167 A M N x y i h2)). Qed.
Lemma lem7648169 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term445 N i) (h2 : term2 i) : term544 A M N x y i.
Proof. exact (@lem7648002 A M N x y i (@lem7648168 A M N x y i h1 h2)). Qed.
Lemma lem7648170 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term445 N i) (h2 : term2 i) : (term451 A M N x y i) = (@dollar A N y i).
Proof. exact (@lem7648169 A M N x y i h1 h2 (@lem7647999 A M N x y i)). Qed.
Lemma lem7648171 {N : Type'} (i : nat) (h1 : term420 N i) : term445 N i.
Proof. exact (proj2 (@lem7647990 N i h1)). Qed.
Lemma lem7648172 {N : Type'} (i : nat) (h1 : term420 N i) : term2 i.
Proof. exact (proj1 (@lem7647990 N i h1)). Qed.
Lemma lem7648173 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term445 N i) (h2 : term2 i) : (term445 N i) = ((term451 A M N x y i) = (@dollar A N y i)).
Proof. exact (prop_ext (fun h3 : term445 N i => @lem7648170 A M N x y i h1 h2) (fun h3 : (term451 A M N x y i) = (@dollar A N y i) => @lem7647991 N i h1)). Qed.
Lemma lem7648174 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term445 N i) (h2 : term2 i) : (term451 A M N x y i) = (@dollar A N y i).
Proof. exact (EQ_MP (@lem7648173 A M N x y i h1 h2) (@lem7647991 N i h1)). Qed.
Lemma lem7648175 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term445 N i) (h2 : term2 i) : (term2 i) = ((term451 A M N x y i) = (@dollar A N y i)).
Proof. exact (prop_ext (fun h3 : term2 i => @lem7648174 A M N x y i h1 h2) (fun h3 : (term451 A M N x y i) = (@dollar A N y i) => @lem7647992 i h2)). Qed.
Lemma lem7648176 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term445 N i) (h2 : term2 i) : (term451 A M N x y i) = (@dollar A N y i).
Proof. exact (EQ_MP (@lem7648175 A M N x y i h1 h2) (@lem7647992 i h2)). Qed.
Lemma lem7648177 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term420 N i) (h2 : term2 i) : (term445 N i) = ((term451 A M N x y i) = (@dollar A N y i)).
Proof. exact (prop_ext (fun h3 : term445 N i => @lem7648176 A M N x y i h3 h2) (fun h3 : (term451 A M N x y i) = (@dollar A N y i) => @lem7648171 N i h1)). Qed.
Lemma lem7648178 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term420 N i) (h2 : term2 i) : (term451 A M N x y i) = (@dollar A N y i).
Proof. exact (EQ_MP (@lem7648177 A M N x y i h1 h2) (@lem7648171 N i h1)). Qed.
Lemma lem7648179 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term420 N i) : (term2 i) = ((term451 A M N x y i) = (@dollar A N y i)).
Proof. exact (prop_ext (fun h2 : term2 i => @lem7648178 A M N x y i h1 h2) (fun h2 : (term451 A M N x y i) = (@dollar A N y i) => @lem7648172 N i h1)). Qed.
Lemma lem7648180 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) (h1 : term420 N i) : (term451 A M N x y i) = (@dollar A N y i).
Proof. exact (EQ_MP (@lem7648179 A M N x y i h1) (@lem7648172 N i h1)). Qed.
Lemma lem7648181 {A M N : Type'} (x : cart A M) (y : cart A N) (i : nat) : term472 A M N x y i.
Proof. exact (fun h0 : term420 N i => @lem7648180 A M N x y i h0). Qed.
Lemma lem7648186 {A M N : Type'} (x : cart A M) (y : cart A N) : term475 A M N x y.
Proof. exact (fun i : nat => @lem7648181 A M N x y i). Qed.
Lemma lem7648191 {A M N : Type'} (x : cart A M) : term479 A M N x.
Proof. exact (fun y : cart A N => @lem7648186 A M N x y). Qed.
Lemma lem7648196 {A M N : Type'} : term483 A M N.
Proof. exact (fun x : cart A M => @lem7648191 A M N x). Qed.
Lemma lem7648197 {A M N : Type'} : term482 A M N.
Proof. exact (EQ_MP (@lem7647989 A M N) (@lem7648196 A M N)). Qed.
