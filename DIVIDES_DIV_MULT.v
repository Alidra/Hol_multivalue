Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVIDES_DIV_MULT_term_abbrevs.
Require Import INT_MUL_DIV_EQ_spec.
Require Import INT_OF_NUM_DIV_spec.
Require Import INT_OF_NUM_EQ_spec.
Require Import INT_OF_NUM_MUL_spec.
Require Import num_divides_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3112388 (a : nat) (b : nat) (h1 : (num_divides a b) = (term0 a b)) : (num_divides a b) = (term0 a b).
Proof. exact (h1). Qed.
Lemma lem3112389 (a : nat) (b : nat) (h1 : (num_divides a b) = (term0 a b)) : (term0 a b) = (num_divides a b).
Proof. exact (SYM (@lem3112388 a b h1)). Qed.
Lemma lem3112390 (a : nat) (b : nat) (h1 : (term0 a b) = (num_divides a b)) : (term0 a b) = (num_divides a b).
Proof. exact (h1). Qed.
Lemma lem3112391 (a : nat) (b : nat) (h1 : (term0 a b) = (num_divides a b)) : (num_divides a b) = (term0 a b).
Proof. exact (SYM (@lem3112390 a b h1)). Qed.
Lemma lem3112392 (a : nat) (b : nat) : ((num_divides a b) = (term0 a b)) = ((term0 a b) = (num_divides a b)).
Proof. exact (prop_ext (fun h1 : (num_divides a b) = (term0 a b) => @lem3112389 a b h1) (fun h1 : (term0 a b) = (num_divides a b) => @lem3112391 a b h1)). Qed.
Lemma lem3112393 (a : nat) : (term1 a) = (term2 a).
Proof. exact (fun_ext (fun b : nat => @lem3112392 a b)). Qed.
Lemma lem3112394 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112395 (a : nat) : (term3 a) = (term4 a).
Proof. exact (MK_COMB (@lem3112394) (@lem3112393 a)). Qed.
Lemma lem3112396 : term5 = term6.
Proof. exact (fun_ext (fun a : nat => @lem3112395 a)). Qed.
Lemma lem3112397 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112398 : term7 = term8.
Proof. exact (MK_COMB (@lem3112397) (@lem3112396)). Qed.
Lemma lem3112399 : term8.
Proof. exact (EQ_MP (@lem3112398) (@lem2836659)). Qed.
Lemma lem3112402 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term9 m n) = (term10 m n).
Proof. exact (h1). Qed.
Lemma lem3112403 (m : nat) (n : nat) (h1 : (term9 m n) = (term10 m n)) : (term10 m n) = (term9 m n).
Proof. exact (SYM (@lem3112402 m n h1)). Qed.
Lemma lem3112404 (m : nat) (n : nat) (h1 : (term10 m n) = (term9 m n)) : (term10 m n) = (term9 m n).
Proof. exact (h1). Qed.
Lemma lem3112405 (m : nat) (n : nat) (h1 : (term10 m n) = (term9 m n)) : (term9 m n) = (term10 m n).
Proof. exact (SYM (@lem3112404 m n h1)). Qed.
Lemma lem3112406 (m : nat) (n : nat) : ((term9 m n) = (term10 m n)) = ((term10 m n) = (term9 m n)).
Proof. exact (prop_ext (fun h1 : (term9 m n) = (term10 m n) => @lem3112403 m n h1) (fun h1 : (term10 m n) = (term9 m n) => @lem3112405 m n h1)). Qed.
Lemma lem3112407 (m : nat) : (term11 m) = (term12 m).
Proof. exact (fun_ext (fun n : nat => @lem3112406 m n)). Qed.
Lemma lem3112408 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112409 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem3112408) (@lem3112407 m)). Qed.
Lemma lem3112410 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem3112409 m)). Qed.
Lemma lem3112411 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112412 : term17 = term18.
Proof. exact (MK_COMB (@lem3112411) (@lem3112410)). Qed.
Lemma lem3112413 : term18.
Proof. exact (EQ_MP (@lem3112412) (@lem2538105)). Qed.
Lemma lem3112416 (m : nat) (n : nat) (h1 : (term19 m n) = (term20 m n)) : (term19 m n) = (term20 m n).
Proof. exact (h1). Qed.
Lemma lem3112417 (m : nat) (n : nat) (h1 : (term19 m n) = (term20 m n)) : (term20 m n) = (term19 m n).
Proof. exact (SYM (@lem3112416 m n h1)). Qed.
Lemma lem3112418 (m : nat) (n : nat) (h1 : (term20 m n) = (term19 m n)) : (term20 m n) = (term19 m n).
Proof. exact (h1). Qed.
Lemma lem3112419 (m : nat) (n : nat) (h1 : (term20 m n) = (term19 m n)) : (term19 m n) = (term20 m n).
Proof. exact (SYM (@lem3112418 m n h1)). Qed.
Lemma lem3112420 (m : nat) (n : nat) : ((term19 m n) = (term20 m n)) = ((term20 m n) = (term19 m n)).
Proof. exact (prop_ext (fun h1 : (term19 m n) = (term20 m n) => @lem3112417 m n h1) (fun h1 : (term20 m n) = (term19 m n) => @lem3112419 m n h1)). Qed.
Lemma lem3112421 (m : nat) : (term21 m) = (term22 m).
Proof. exact (fun_ext (fun n : nat => @lem3112420 m n)). Qed.
Lemma lem3112422 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112423 (m : nat) : (term23 m) = (term24 m).
Proof. exact (MK_COMB (@lem3112422) (@lem3112421 m)). Qed.
Lemma lem3112424 : term25 = term26.
Proof. exact (fun_ext (fun m : nat => @lem3112423 m)). Qed.
Lemma lem3112425 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112426 : term27 = term28.
Proof. exact (MK_COMB (@lem3112425) (@lem3112424)). Qed.
Lemma lem3112427 : term28.
Proof. exact (EQ_MP (@lem3112426) (@lem2307381)). Qed.
Lemma lem3112430 (m : nat) (n : nat) (h1 : ((int_of_num m) = (int_of_num n)) = (m = n)) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (h1). Qed.
Lemma lem3112431 (m : nat) (n : nat) (h1 : ((int_of_num m) = (int_of_num n)) = (m = n)) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (SYM (@lem3112430 m n h1)). Qed.
Lemma lem3112432 (m : nat) (n : nat) (h1 : (m = n) = ((int_of_num m) = (int_of_num n))) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (h1). Qed.
Lemma lem3112433 (m : nat) (n : nat) (h1 : (m = n) = ((int_of_num m) = (int_of_num n))) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (SYM (@lem3112432 m n h1)). Qed.
Lemma lem3112434 (m : nat) (n : nat) : (((int_of_num m) = (int_of_num n)) = (m = n)) = ((m = n) = ((int_of_num m) = (int_of_num n))).
Proof. exact (prop_ext (fun h1 : ((int_of_num m) = (int_of_num n)) = (m = n) => @lem3112431 m n h1) (fun h1 : (m = n) = ((int_of_num m) = (int_of_num n)) => @lem3112433 m n h1)). Qed.
Lemma lem3112435 (m : nat) : (term29 m) = (term30 m).
Proof. exact (fun_ext (fun n : nat => @lem3112434 m n)). Qed.
Lemma lem3112436 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112437 (m : nat) : (term31 m) = (term32 m).
Proof. exact (MK_COMB (@lem3112436) (@lem3112435 m)). Qed.
Lemma lem3112438 : term33 = term34.
Proof. exact (fun_ext (fun m : nat => @lem3112437 m)). Qed.
Lemma lem3112439 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112440 : term35 = term36.
Proof. exact (MK_COMB (@lem3112439) (@lem3112438)). Qed.
Lemma lem3112441 : term36.
Proof. exact (EQ_MP (@lem3112440) (@lem2307147)). Qed.
Lemma lem3112442 (a : nat) : term37 a.
Proof. exact (@lem3112399 a). Qed.
Lemma lem3112443 (a : nat) : (term37 a) = (term4 a).
Proof. exact (eq_refl (term37 a)). Qed.
Lemma lem3112444 (a : nat) : term4 a.
Proof. exact (EQ_MP (@lem3112443 a) (@lem3112442 a)). Qed.
Lemma lem3112445 (a : nat) (b : nat) : term38 a b.
Proof. exact (@lem3112444 a b). Qed.
Lemma lem3112446 (a : nat) (b : nat) : (term38 a b) = ((term0 a b) = (num_divides a b)).
Proof. exact (eq_refl (term38 a b)). Qed.
Lemma lem3112448 : term39.
Proof. exact (proj2 (@lem2528100)). Qed.
Lemma lem3112449 (m : int) : term40 m.
Proof. exact (@lem3112448 m). Qed.
Lemma lem3112450 (m : int) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem3112451 (m : int) : term41 m.
Proof. exact (EQ_MP (@lem3112450 m) (@lem3112449 m)). Qed.
Lemma lem3112452 (m : int) (n : int) : term42 m n.
Proof. exact (@lem3112451 m n). Qed.
Lemma lem3112453 (n : int) (m : int) : (term42 m n) = (((term43 m n) = m) = (int_divides n m)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem3112462 (m : nat) : term44 m.
Proof. exact (@lem3112413 m). Qed.
Lemma lem3112463 (m : nat) : (term44 m) = (term14 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem3112464 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem3112463 m) (@lem3112462 m)). Qed.
Lemma lem3112465 (m : nat) (n : nat) : term45 m n.
Proof. exact (@lem3112464 m n). Qed.
Lemma lem3112466 (m : nat) (n : nat) : (term45 m n) = ((term10 m n) = (term9 m n)).
Proof. exact (eq_refl (term45 m n)). Qed.
Lemma lem3112468 (m : nat) : term46 m.
Proof. exact (@lem3112427 m). Qed.
Lemma lem3112469 (m : nat) : (term46 m) = (term24 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem3112470 (m : nat) : term24 m.
Proof. exact (EQ_MP (@lem3112469 m) (@lem3112468 m)). Qed.
Lemma lem3112471 (m : nat) (n : nat) : term47 m n.
Proof. exact (@lem3112470 m n). Qed.
Lemma lem3112472 (m : nat) (n : nat) : (term47 m n) = ((term20 m n) = (term19 m n)).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem3112474 (m : nat) : term48 m.
Proof. exact (@lem3112441 m). Qed.
Lemma lem3112475 (m : nat) : (term48 m) = (term32 m).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem3112476 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem3112475 m) (@lem3112474 m)). Qed.
Lemma lem3112477 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem3112476 m n). Qed.
Lemma lem3112478 (m : nat) (n : nat) : (term49 m n) = ((m = n) = ((int_of_num m) = (int_of_num n))).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem3112495 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem3112478 m n) (@lem3112477 m n)). Qed.
Lemma lem3112496 (m : nat) (n : nat) : ((term50 n m) = n) = ((term51 n m) = (int_of_num n)).
Proof. exact (@lem3112495 (term50 n m) n). Qed.
Lemma lem3112502 (m : nat) (n : nat) : (term20 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem3112472 m n) (@lem3112471 m n)). Qed.
Lemma lem3112503 (n : nat) (m : nat) : (term51 n m) = (term52 n m).
Proof. exact (@lem3112502 (Nat.div n m) m). Qed.
Lemma lem3112505 (m : nat) (n : nat) : (term10 m n) = (term9 m n).
Proof. exact (EQ_MP (@lem3112466 m n) (@lem3112465 m n)). Qed.
Lemma lem3112506 (n : nat) (m : nat) : (term10 n m) = (term9 n m).
Proof. exact (@lem3112505 n m). Qed.
Lemma lem3112507 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem3112508 (n : nat) (m : nat) : (term53 n m) = (term54 n m).
Proof. exact (MK_COMB (@lem3112507) (@lem3112506 n m)). Qed.
Lemma lem3112509 (m : nat) : (int_of_num m) = (int_of_num m).
Proof. exact (eq_refl (int_of_num m)). Qed.
Lemma lem3112510 (n : nat) (m : nat) : (term52 n m) = (term55 n m).
Proof. exact (MK_COMB (@lem3112508 n m) (@lem3112509 m)). Qed.
Lemma lem3112511 (n : nat) (m : nat) : (term51 n m) = (term55 n m).
Proof. exact (TRANS (@lem3112503 n m) (@lem3112510 n m)). Qed.
Lemma lem3112512 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3112513 (n : nat) (m : nat) : (term56 n m) = (term57 n m).
Proof. exact (MK_COMB (@lem3112512) (@lem3112511 n m)). Qed.
Lemma lem3112514 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem3112515 (m : nat) (n : nat) : ((term51 n m) = (int_of_num n)) = ((term55 n m) = (int_of_num n)).
Proof. exact (MK_COMB (@lem3112513 n m) (@lem3112514 n)). Qed.
Lemma lem3112517 (n : int) (m : int) : ((term43 m n) = m) = (int_divides n m).
Proof. exact (EQ_MP (@lem3112453 n m) (@lem3112452 m n)). Qed.
Lemma lem3112518 (m : nat) (n : nat) : ((term55 n m) = (int_of_num n)) = (term0 m n).
Proof. exact (@lem3112517 (int_of_num m) (int_of_num n)). Qed.
Lemma lem3112520 (a : nat) (b : nat) : (term0 a b) = (num_divides a b).
Proof. exact (EQ_MP (@lem3112446 a b) (@lem3112445 a b)). Qed.
Lemma lem3112521 (m : nat) (n : nat) : (term0 m n) = (num_divides m n).
Proof. exact (@lem3112520 m n). Qed.
Lemma lem3112522 (m : nat) (n : nat) : ((term55 n m) = (int_of_num n)) = (num_divides m n).
Proof. exact (TRANS (@lem3112518 m n) (@lem3112521 m n)). Qed.
Lemma lem3112523 (m : nat) (n : nat) : ((term51 n m) = (int_of_num n)) = (num_divides m n).
Proof. exact (TRANS (@lem3112515 m n) (@lem3112522 m n)). Qed.
Lemma lem3112524 (m : nat) (n : nat) : ((term50 n m) = n) = (num_divides m n).
Proof. exact (TRANS (@lem3112496 m n) (@lem3112523 m n)). Qed.
Lemma lem3112525 (m : nat) (n : nat) : (term58 m n) = (term58 m n).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem3112526 (m : nat) (n : nat) : ((num_divides m n) = ((term50 n m) = n)) = ((num_divides m n) = (num_divides m n)).
Proof. exact (MK_COMB (@lem3112525 m n) (@lem3112524 m n)). Qed.
Lemma lem3112528 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3112529 (x : Prop) : (x = x) = True.
Proof. exact (@lem3112528 Prop x). Qed.
Lemma lem3112530 (m : nat) (n : nat) : ((num_divides m n) = (num_divides m n)) = True.
Proof. exact (@lem3112529 (num_divides m n)). Qed.
Lemma lem3112531 (m : nat) (n : nat) : ((num_divides m n) = ((term50 n m) = n)) = True.
Proof. exact (TRANS (@lem3112526 m n) (@lem3112530 m n)). Qed.
Lemma lem3112532 (m : nat) : (term59 m) = term60.
Proof. exact (fun_ext (fun n : nat => @lem3112531 m n)). Qed.
Lemma lem3112533 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112534 (m : nat) : (term61 m) = term62.
Proof. exact (MK_COMB (@lem3112533) (@lem3112532 m)). Qed.
Lemma lem3112536 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3112537 (t : Prop) : (term64 t) = t.
Proof. exact (@lem3112536 nat t). Qed.
Lemma lem3112538 : term62 = True.
Proof. exact (@lem3112537 True). Qed.
Lemma lem3112539 (m : nat) : (term61 m) = True.
Proof. exact (TRANS (@lem3112534 m) (@lem3112538)). Qed.
Lemma lem3112540 : term65 = term60.
Proof. exact (fun_ext (fun m : nat => @lem3112539 m)). Qed.
Lemma lem3112541 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112542 : term66 = term62.
Proof. exact (MK_COMB (@lem3112541) (@lem3112540)). Qed.
Lemma lem3112544 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3112545 (t : Prop) : (term64 t) = t.
Proof. exact (@lem3112544 nat t). Qed.
Lemma lem3112546 : term62 = True.
Proof. exact (@lem3112545 True). Qed.
Lemma lem3112547 : term66 = True.
Proof. exact (TRANS (@lem3112542) (@lem3112546)). Qed.
Lemma lem3112548 : True = term66.
Proof. exact (SYM (@lem3112547)). Qed.
Lemma lem3112549 : term66.
Proof. exact (EQ_MP (@lem3112548) (@lem0)). Qed.
