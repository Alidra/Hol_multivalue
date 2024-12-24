Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMSEG_SING_term_abbrevs.
Require Import EXTENSION_spec.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import IN_SING_spec.
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
Require Import thm17362_spec.
Require Import thm17784_spec.
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
Lemma lem5371342 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem5371343 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem5371344 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem5371343 m) (@lem5371342 m)). Qed.
Lemma lem5371345 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem5371344 m n). Qed.
Lemma lem5371346 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem5371347 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem5371346 m n) (@lem5371345 m n)). Qed.
Lemma lem5371348 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem5371347 m n p). Qed.
Lemma lem5371349 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem5371351 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem5371352 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem5371353 {A : Type'} (x : A) : term8 A x.
Proof. exact (EQ_MP (@lem5371352 A x) (@lem5371351 A x)). Qed.
Lemma lem5371354 {A : Type'} (x : A) (y : A) : term9 A x y.
Proof. exact (@lem5371353 A x y). Qed.
Lemma lem5371355 {A : Type'} (x : A) (y : A) : (term9 A x y) = ((term10 A x y) = (x = y)).
Proof. exact (eq_refl (term9 A x y)). Qed.
Lemma lem5371357 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5371358 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem5371359 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (EQ_MP (@lem5371358 A s) (@lem5371357 A s)). Qed.
Lemma lem5371360 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term13 A s t.
Proof. exact (@lem5371359 A s t). Qed.
Lemma lem5371361 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = ((s = t) = (term14 A s t)).
Proof. exact (eq_refl (term13 A s t)). Qed.
Lemma lem5371370 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term14 A s t).
Proof. exact (EQ_MP (@lem5371361 A s t) (@lem5371360 A s t)). Qed.
Lemma lem5371371 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term15 s t).
Proof. exact (@lem5371370 nat s t). Qed.
Lemma lem5371372 (n : nat) : ((dotdot n n) = (@INSERT nat n (@EMPTY nat))) = (term16 n).
Proof. exact (@lem5371371 (dotdot n n) (@INSERT nat n (@EMPTY nat))). Qed.
Lemma lem5371382 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem5371349 m p n) (@lem5371348 m n p)). Qed.
Lemma lem5371383 (x : nat) (n : nat) : (term17 x n) = (term18 x n).
Proof. exact (@lem5371382 n x n). Qed.
Lemma lem5371386 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5371387 (x : nat) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (MK_COMB (@lem5371386) (@lem5371383 x n)). Qed.
Lemma lem5371389 {A : Type'} (x : A) (y : A) : (term10 A x y) = (x = y).
Proof. exact (EQ_MP (@lem5371355 A x y) (@lem5371354 A x y)). Qed.
Lemma lem5371390 (x : nat) (y : nat) : (term21 x y) = (x = y).
Proof. exact (@lem5371389 nat x y). Qed.
Lemma lem5371391 (x : nat) (n : nat) : (term21 x n) = (x = n).
Proof. exact (@lem5371390 x n). Qed.
Lemma lem5371396 (x : nat) (n : nat) : ((term17 x n) = (term21 x n)) = ((term18 x n) = (x = n)).
Proof. exact (MK_COMB (@lem5371387 x n) (@lem5371391 x n)). Qed.
Lemma lem5371401 (n : nat) : (term22 n) = (term23 n).
Proof. exact (fun_ext (fun x : nat => @lem5371396 x n)). Qed.
Lemma lem5371402 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371403 (n : nat) : (term16 n) = (term24 n).
Proof. exact (MK_COMB (@lem5371402) (@lem5371401 n)). Qed.
Lemma lem5371408 (n : nat) : ((dotdot n n) = (@INSERT nat n (@EMPTY nat))) = (term24 n).
Proof. exact (TRANS (@lem5371372 n) (@lem5371403 n)). Qed.
Lemma lem5371409 : term25 = term26.
Proof. exact (fun_ext (fun n : nat => @lem5371408 n)). Qed.
Lemma lem5371410 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371411 : term27 = term28.
Proof. exact (MK_COMB (@lem5371410) (@lem5371409)). Qed.
Lemma lem5371416 : term28 = term27.
Proof. exact (SYM (@lem5371411)). Qed.
Lemma lem5371440 (x : nat) (n : nat) : ((term18 x n) = (x = n)) = ((term18 x n) = (x = n)).
Proof. exact (eq_refl ((term18 x n) = (x = n))). Qed.
Lemma lem5371441 (n : nat) : (term23 n) = (term23 n).
Proof. exact (fun_ext (fun x : nat => @lem5371440 x n)). Qed.
Lemma lem5371442 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371443 (n : nat) : (term24 n) = (term24 n).
Proof. exact (MK_COMB (@lem5371442) (@lem5371441 n)). Qed.
Lemma lem5371444 : term26 = term26.
Proof. exact (fun_ext (fun n : nat => @lem5371443 n)). Qed.
Lemma lem5371445 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371447 : term28 = term28.
Proof. exact (MK_COMB (@lem5371445) (@lem5371444)). Qed.
Lemma lem5371456 (x : nat) (n : nat) : (term29 x n) = (term30 x n).
Proof. exact (@lem17045 (Peano.le n x) (Peano.le x n)). Qed.
Lemma lem5371461 (x : nat) (n : nat) : (x = n) = (x = n).
Proof. exact (eq_refl (x = n)). Qed.
Lemma lem5371462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5371463 (x : nat) (n : nat) : (term31 x n) = (term32 x n).
Proof. exact (MK_COMB (@lem5371462) (@lem5371456 x n)). Qed.
Lemma lem5371464 (x : nat) (n : nat) : (term33 x n) = (term34 x n).
Proof. exact (MK_COMB (@lem5371463 x n) (@lem5371461 x n)). Qed.
Lemma lem5371469 (x : nat) (n : nat) : (term35 x n) = (term35 x n).
Proof. exact (eq_refl (term35 x n)). Qed.
Lemma lem5371470 (x : nat) (n : nat) : (term36 x n) = (term37 x n).
Proof. exact (MK_COMB (@lem5371469 x n) (@lem5371464 x n)). Qed.
Lemma lem5371471 (x : nat) (n : nat) : ((term18 x n) = (x = n)) = (term36 x n).
Proof. exact (@lem17784 (term18 x n) (x = n)). Qed.
Lemma lem5371472 (x : nat) (n : nat) : ((term18 x n) = (x = n)) = (term37 x n).
Proof. exact (TRANS (@lem5371471 x n) (@lem5371470 x n)). Qed.
Lemma lem5371473 (n : nat) : (term23 n) = (term38 n).
Proof. exact (fun_ext (fun x : nat => @lem5371472 x n)). Qed.
Lemma lem5371474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371475 (n : nat) : (term24 n) = (term39 n).
Proof. exact (MK_COMB (@lem5371474) (@lem5371473 n)). Qed.
Lemma lem5371476 : term26 = term40.
Proof. exact (fun_ext (fun n : nat => @lem5371475 n)). Qed.
Lemma lem5371477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371478 : term28 = term41.
Proof. exact (MK_COMB (@lem5371477) (@lem5371476)). Qed.
Lemma lem5371479 : term28 = term41.
Proof. exact (TRANS (@lem5371447) (@lem5371478)). Qed.
Lemma lem5371480 (x : nat) (n : nat) : (term37 x n) = (term37 x n).
Proof. exact (eq_refl (term37 x n)). Qed.
Lemma lem5371481 (n : nat) : (term38 n) = (term38 n).
Proof. exact (fun_ext (fun x : nat => @lem5371480 x n)). Qed.
Lemma lem5371482 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371483 (n : nat) : (term39 n) = (term39 n).
Proof. exact (MK_COMB (@lem5371482) (@lem5371481 n)). Qed.
Lemma lem5371484 : term40 = term40.
Proof. exact (fun_ext (fun n : nat => @lem5371483 n)). Qed.
Lemma lem5371485 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371486 : term41 = term41.
Proof. exact (MK_COMB (@lem5371485) (@lem5371484)). Qed.
Lemma lem5371515 : term28 = term41.
Proof. exact (TRANS (@lem5371479) (@lem5371486)). Qed.
Lemma lem5371566 (x : nat) (n : nat) : (term37 x n) = (term37 x n).
Proof. exact (eq_refl (term37 x n)). Qed.
Lemma lem5371567 (n : nat) : (term38 n) = (term38 n).
Proof. exact (fun_ext (fun x : nat => @lem5371566 x n)). Qed.
Lemma lem5371568 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371569 (n : nat) : (term39 n) = (term39 n).
Proof. exact (MK_COMB (@lem5371568) (@lem5371567 n)). Qed.
Lemma lem5371570 : term40 = term40.
Proof. exact (fun_ext (fun n : nat => @lem5371569 n)). Qed.
Lemma lem5371571 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371572 : term41 = term41.
Proof. exact (MK_COMB (@lem5371571) (@lem5371570)). Qed.
Lemma lem5371575 : term28 = term41.
Proof. exact (TRANS (@lem5371515) (@lem5371572)). Qed.
Lemma lem5371577 (m : nat) (n : nat) : (Peano.le m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5371578 (n : nat) (x : nat) : (Peano.le n x) = (term42 n x).
Proof. exact (@lem5371577 n x). Qed.
Lemma lem5371579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5371580 (n : nat) (x : nat) : (term43 n x) = (term44 n x).
Proof. exact (MK_COMB (@lem5371579) (@lem5371578 n x)). Qed.
Lemma lem5371582 (m : nat) (n : nat) : (Peano.le m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5371583 (x : nat) (n : nat) : (Peano.le x n) = (term42 x n).
Proof. exact (@lem5371582 x n). Qed.
Lemma lem5371584 (x : nat) (n : nat) : (term18 x n) = (term45 x n).
Proof. exact (MK_COMB (@lem5371580 n x) (@lem5371583 x n)). Qed.
Lemma lem5371585 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5371586 (x : nat) (n : nat) : (term46 x n) = (term47 x n).
Proof. exact (MK_COMB (@lem5371585) (@lem5371584 x n)). Qed.
Lemma lem5371588 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5371589 (x : nat) (n : nat) : (x = n) = ((int_of_num x) = (int_of_num n)).
Proof. exact (@lem5371588 x n). Qed.
Lemma lem5371592 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5371593 (x : nat) (n : nat) : (term48 x n) = (term49 x n).
Proof. exact (MK_COMB (@lem5371592) (@lem5371589 x n)). Qed.
Lemma lem5371594 (x : nat) (n : nat) : (term50 x n) = (term51 x n).
Proof. exact (MK_COMB (@lem5371586 x n) (@lem5371593 x n)). Qed.
Lemma lem5371595 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5371596 (x : nat) (n : nat) : (term35 x n) = (term52 x n).
Proof. exact (MK_COMB (@lem5371595) (@lem5371594 x n)). Qed.
Lemma lem5371598 (m : nat) (n : nat) : (Peano.le m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5371599 (n : nat) (x : nat) : (Peano.le n x) = (term42 n x).
Proof. exact (@lem5371598 n x). Qed.
Lemma lem5371600 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5371601 (n : nat) (x : nat) : (term53 n x) = (term54 n x).
Proof. exact (MK_COMB (@lem5371600) (@lem5371599 n x)). Qed.
Lemma lem5371602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5371603 (n : nat) (x : nat) : (term55 n x) = (term56 n x).
Proof. exact (MK_COMB (@lem5371602) (@lem5371601 n x)). Qed.
Lemma lem5371605 (m : nat) (n : nat) : (Peano.le m n) = (term42 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem5371606 (x : nat) (n : nat) : (Peano.le x n) = (term42 x n).
Proof. exact (@lem5371605 x n). Qed.
Lemma lem5371607 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5371608 (x : nat) (n : nat) : (term53 x n) = (term54 x n).
Proof. exact (MK_COMB (@lem5371607) (@lem5371606 x n)). Qed.
Lemma lem5371609 (x : nat) (n : nat) : (term30 x n) = (term57 x n).
Proof. exact (MK_COMB (@lem5371603 n x) (@lem5371608 x n)). Qed.
Lemma lem5371610 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5371611 (x : nat) (n : nat) : (term32 x n) = (term58 x n).
Proof. exact (MK_COMB (@lem5371610) (@lem5371609 x n)). Qed.
Lemma lem5371613 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5371614 (x : nat) (n : nat) : (x = n) = ((int_of_num x) = (int_of_num n)).
Proof. exact (@lem5371613 x n). Qed.
Lemma lem5371617 (x : nat) (n : nat) : (term34 x n) = (term59 x n).
Proof. exact (MK_COMB (@lem5371611 x n) (@lem5371614 x n)). Qed.
Lemma lem5371618 (x : nat) (n : nat) : (term37 x n) = (term60 x n).
Proof. exact (MK_COMB (@lem5371596 x n) (@lem5371617 x n)). Qed.
Lemma lem5371619 (n : nat) : (term38 n) = (term61 n).
Proof. exact (fun_ext (fun x : nat => @lem5371618 x n)). Qed.
Lemma lem5371620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371621 (n : nat) : (term39 n) = (term62 n).
Proof. exact (MK_COMB (@lem5371620) (@lem5371619 n)). Qed.
Lemma lem5371622 : term40 = term63.
Proof. exact (fun_ext (fun n : nat => @lem5371621 n)). Qed.
Lemma lem5371623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5371624 : term41 = term64.
Proof. exact (MK_COMB (@lem5371623) (@lem5371622)). Qed.
Lemma lem5371625 : term28 = term64.
Proof. exact (TRANS (@lem5371575) (@lem5371624)). Qed.
Lemma lem5371626 (n : nat) : term65 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5371627 (n : nat) : (term65 n) = (term66 n).
Proof. exact (eq_refl (term65 n)). Qed.
Lemma lem5371628 (n : nat) : term66 n.
Proof. exact (EQ_MP (@lem5371627 n) (@lem5371626 n)). Qed.
Lemma lem5371629 (x : nat) : term65 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem5371630 (x : nat) : (term65 x) = (term66 x).
Proof. exact (eq_refl (term65 x)). Qed.
Lemma lem5371631 (x : nat) : term66 x.
Proof. exact (EQ_MP (@lem5371630 x) (@lem5371629 x)). Qed.
Lemma lem5371632 (_69741 : int) (_69740 : int) : (term67 _69741 _69740) = (term68 _69741 _69740).
Proof. exact (@lem2318604 (term68 _69741 _69740)). Qed.
Lemma lem5371660 (_69741 : int) (_69740 : int) : (term69 _69741 _69740) = (term70 _69741 _69740).
Proof. exact (@lem17045 (int_le _69740 _69741) (int_le _69741 _69740)). Qed.
Lemma lem5371663 (_69741 : int) (_69740 : int) : (term71 _69741 _69740) = (_69741 = _69740).
Proof. exact (@lem16933 (_69741 = _69740)). Qed.
Lemma lem5371664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5371665 (_69741 : int) (_69740 : int) : (term72 _69741 _69740) = (term73 _69741 _69740).
Proof. exact (MK_COMB (@lem5371664) (@lem5371660 _69741 _69740)). Qed.
Lemma lem5371666 (_69741 : int) (_69740 : int) : (term74 _69741 _69740) = (term75 _69741 _69740).
Proof. exact (MK_COMB (@lem5371665 _69741 _69740) (@lem5371663 _69741 _69740)). Qed.
Lemma lem5371667 (_69741 : int) (_69740 : int) : (term76 _69741 _69740) = (term74 _69741 _69740).
Proof. exact (@lem17160 (term77 _69741 _69740) (term78 _69741 _69740)). Qed.
Lemma lem5371668 (_69741 : int) (_69740 : int) : (term76 _69741 _69740) = (term75 _69741 _69740).
Proof. exact (TRANS (@lem5371667 _69741 _69740) (@lem5371666 _69741 _69740)). Qed.
Lemma lem5371671 (_69740 : int) (_69741 : int) : (term79 _69740 _69741) = (int_le _69740 _69741).
Proof. exact (@lem16933 (int_le _69740 _69741)). Qed.
Lemma lem5371674 (_69741 : int) (_69740 : int) : (term79 _69741 _69740) = (int_le _69741 _69740).
Proof. exact (@lem16933 (int_le _69741 _69740)). Qed.
Lemma lem5371675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5371676 (_69740 : int) (_69741 : int) : (term80 _69740 _69741) = (term81 _69740 _69741).
Proof. exact (MK_COMB (@lem5371675) (@lem5371671 _69740 _69741)). Qed.
Lemma lem5371677 (_69741 : int) (_69740 : int) : (term82 _69741 _69740) = (term77 _69741 _69740).
Proof. exact (MK_COMB (@lem5371676 _69740 _69741) (@lem5371674 _69741 _69740)). Qed.
Lemma lem5371678 (_69741 : int) (_69740 : int) : (term83 _69741 _69740) = (term82 _69741 _69740).
Proof. exact (@lem17160 (term84 _69740 _69741) (term84 _69741 _69740)). Qed.
Lemma lem5371679 (_69741 : int) (_69740 : int) : (term83 _69741 _69740) = (term77 _69741 _69740).
Proof. exact (TRANS (@lem5371678 _69741 _69740) (@lem5371677 _69741 _69740)). Qed.
Lemma lem5371680 (_69741 : int) (_69740 : int) : (term78 _69741 _69740) = (term78 _69741 _69740).
Proof. exact (eq_refl (term78 _69741 _69740)). Qed.
Lemma lem5371681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5371682 (_69741 : int) (_69740 : int) : (term85 _69741 _69740) = (term86 _69741 _69740).
Proof. exact (MK_COMB (@lem5371681) (@lem5371679 _69741 _69740)). Qed.
Lemma lem5371683 (_69741 : int) (_69740 : int) : (term87 _69741 _69740) = (term88 _69741 _69740).
Proof. exact (MK_COMB (@lem5371682 _69741 _69740) (@lem5371680 _69741 _69740)). Qed.
Lemma lem5371684 (_69741 : int) (_69740 : int) : (term89 _69741 _69740) = (term87 _69741 _69740).
Proof. exact (@lem17160 (term70 _69741 _69740) (_69741 = _69740)). Qed.
Lemma lem5371685 (_69741 : int) (_69740 : int) : (term89 _69741 _69740) = (term88 _69741 _69740).
Proof. exact (TRANS (@lem5371684 _69741 _69740) (@lem5371683 _69741 _69740)). Qed.
Lemma lem5371686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5371687 (_69741 : int) (_69740 : int) : (term90 _69741 _69740) = (term91 _69741 _69740).
Proof. exact (MK_COMB (@lem5371686) (@lem5371668 _69741 _69740)). Qed.
Lemma lem5371688 (_69741 : int) (_69740 : int) : (term92 _69741 _69740) = (term93 _69741 _69740).
Proof. exact (MK_COMB (@lem5371687 _69741 _69740) (@lem5371685 _69741 _69740)). Qed.
Lemma lem5371689 (_69741 : int) (_69740 : int) : (term94 _69741 _69740) = (term92 _69741 _69740).
Proof. exact (@lem17045 (term95 _69741 _69740) (term96 _69741 _69740)). Qed.
Lemma lem5371690 (_69741 : int) (_69740 : int) : (term94 _69741 _69740) = (term93 _69741 _69740).
Proof. exact (TRANS (@lem5371689 _69741 _69740) (@lem5371688 _69741 _69740)). Qed.
Lemma lem5371692 (_69741 : int) : (term97 _69741) = (term97 _69741).
Proof. exact (eq_refl (term97 _69741)). Qed.
Lemma lem5371693 (_69741 : int) (_69740 : int) : (term98 _69741 _69740) = (term99 _69741 _69740).
Proof. exact (MK_COMB (@lem5371692 _69741) (@lem5371690 _69741 _69740)). Qed.
Lemma lem5371694 (_69741 : int) (_69740 : int) : (term100 _69741 _69740) = (term98 _69741 _69740).
Proof. exact (@lem17362 (term101 _69741) (term102 _69741 _69740)). Qed.
Lemma lem5371695 (_69741 : int) (_69740 : int) : (term100 _69741 _69740) = (term99 _69741 _69740).
Proof. exact (TRANS (@lem5371694 _69741 _69740) (@lem5371693 _69741 _69740)). Qed.
Lemma lem5371697 (_69740 : int) : (term97 _69740) = (term97 _69740).
Proof. exact (eq_refl (term97 _69740)). Qed.
Lemma lem5371698 (_69741 : int) (_69740 : int) : (term103 _69741 _69740) = (term104 _69741 _69740).
Proof. exact (MK_COMB (@lem5371697 _69740) (@lem5371695 _69741 _69740)). Qed.
Lemma lem5371699 (_69741 : int) (_69740 : int) : (term105 _69741 _69740) = (term103 _69741 _69740).
Proof. exact (@lem17362 (term101 _69740) (term106 _69741 _69740)). Qed.
Lemma lem5371737 (_69741 : int) (_69740 : int) : (term105 _69741 _69740) = (term104 _69741 _69740).
Proof. exact (TRANS (@lem5371699 _69741 _69740) (@lem5371698 _69741 _69740)). Qed.
Lemma lem5371740 (x : int) (y : int) : (int_le x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5371741 (_69740 : int) : (term101 _69740) = (term108 _69740).
Proof. exact (@lem5371740 term109 _69740). Qed.
Lemma lem5371743 (n : nat) : (term110 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5371744 : term111 = term112.
Proof. exact (@lem5371743 (NUMERAL 0)). Qed.
Lemma lem5371745 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5371746 : term113 = term114.
Proof. exact (MK_COMB (@lem5371745) (@lem5371744)). Qed.
Lemma lem5371747 (_69740 : int) : (real_of_int _69740) = (real_of_int _69740).
Proof. exact (eq_refl (real_of_int _69740)). Qed.
Lemma lem5371748 (_69740 : int) : (term108 _69740) = (term115 _69740).
Proof. exact (MK_COMB (@lem5371746) (@lem5371747 _69740)). Qed.
Lemma lem5371750 (_69740 : int) : (term101 _69740) = (term115 _69740).
Proof. exact (TRANS (@lem5371741 _69740) (@lem5371748 _69740)). Qed.
Lemma lem5371753 (x : int) (y : int) : (int_le x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5371754 (_69741 : int) : (term101 _69741) = (term108 _69741).
Proof. exact (@lem5371753 term109 _69741). Qed.
Lemma lem5371756 (n : nat) : (term110 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5371757 : term111 = term112.
Proof. exact (@lem5371756 (NUMERAL 0)). Qed.
Lemma lem5371758 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5371759 : term113 = term114.
Proof. exact (MK_COMB (@lem5371758) (@lem5371757)). Qed.
Lemma lem5371760 (_69741 : int) : (real_of_int _69741) = (real_of_int _69741).
Proof. exact (eq_refl (real_of_int _69741)). Qed.
Lemma lem5371761 (_69741 : int) : (term108 _69741) = (term115 _69741).
Proof. exact (MK_COMB (@lem5371759) (@lem5371760 _69741)). Qed.
Lemma lem5371763 (_69741 : int) : (term101 _69741) = (term115 _69741).
Proof. exact (TRANS (@lem5371754 _69741) (@lem5371761 _69741)). Qed.
Lemma lem5371765 (y : int) (x : int) : (term84 x y) = (term116 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5371766 (_69741 : int) (_69740 : int) : (term84 _69740 _69741) = (term116 _69741 _69740).
Proof. exact (@lem5371765 _69741 _69740). Qed.
Lemma lem5371768 (x : int) (y : int) : (int_le x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5371769 (_69741 : int) (_69740 : int) : (term116 _69741 _69740) = (term117 _69741 _69740).
Proof. exact (@lem5371768 (term118 _69741) _69740). Qed.
Lemma lem5371771 (x : int) (y : int) : (term119 x y) = (term120 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5371772 (_69741 : int) : (term121 _69741) = (term122 _69741).
Proof. exact (@lem5371771 _69741 term123). Qed.
Lemma lem5371774 (n : nat) : (term110 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5371775 : term124 = term125.
Proof. exact (@lem5371774 term126). Qed.
Lemma lem5371776 (_69741 : int) : (term127 _69741) = (term127 _69741).
Proof. exact (eq_refl (term127 _69741)). Qed.
Lemma lem5371777 (_69741 : int) : (term122 _69741) = (term128 _69741).
Proof. exact (MK_COMB (@lem5371776 _69741) (@lem5371775)). Qed.
Lemma lem5371778 (_69741 : int) : (term121 _69741) = (term128 _69741).
Proof. exact (TRANS (@lem5371772 _69741) (@lem5371777 _69741)). Qed.
Lemma lem5371779 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5371780 (_69741 : int) : (term129 _69741) = (term130 _69741).
Proof. exact (MK_COMB (@lem5371779) (@lem5371778 _69741)). Qed.
Lemma lem5371781 (_69740 : int) : (real_of_int _69740) = (real_of_int _69740).
Proof. exact (eq_refl (real_of_int _69740)). Qed.
Lemma lem5371782 (_69741 : int) (_69740 : int) : (term117 _69741 _69740) = (term131 _69741 _69740).
Proof. exact (MK_COMB (@lem5371780 _69741) (@lem5371781 _69740)). Qed.
Lemma lem5371783 (_69741 : int) (_69740 : int) : (term116 _69741 _69740) = (term131 _69741 _69740).
Proof. exact (TRANS (@lem5371769 _69741 _69740) (@lem5371782 _69741 _69740)). Qed.
Lemma lem5371784 (_69741 : int) (_69740 : int) : (term84 _69740 _69741) = (term131 _69741 _69740).
Proof. exact (TRANS (@lem5371766 _69741 _69740) (@lem5371783 _69741 _69740)). Qed.
Lemma lem5371786 (y : int) (x : int) : (term84 x y) = (term116 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem5371787 (_69740 : int) (_69741 : int) : (term84 _69741 _69740) = (term116 _69740 _69741).
Proof. exact (@lem5371786 _69740 _69741). Qed.
Lemma lem5371789 (x : int) (y : int) : (int_le x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5371790 (_69740 : int) (_69741 : int) : (term116 _69740 _69741) = (term117 _69740 _69741).
Proof. exact (@lem5371789 (term118 _69740) _69741). Qed.
Lemma lem5371792 (x : int) (y : int) : (term119 x y) = (term120 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5371793 (_69740 : int) : (term121 _69740) = (term122 _69740).
Proof. exact (@lem5371792 _69740 term123). Qed.
Lemma lem5371795 (n : nat) : (term110 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5371796 : term124 = term125.
Proof. exact (@lem5371795 term126). Qed.
Lemma lem5371797 (_69740 : int) : (term127 _69740) = (term127 _69740).
Proof. exact (eq_refl (term127 _69740)). Qed.
Lemma lem5371798 (_69740 : int) : (term122 _69740) = (term128 _69740).
Proof. exact (MK_COMB (@lem5371797 _69740) (@lem5371796)). Qed.
Lemma lem5371799 (_69740 : int) : (term121 _69740) = (term128 _69740).
Proof. exact (TRANS (@lem5371793 _69740) (@lem5371798 _69740)). Qed.
Lemma lem5371800 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5371801 (_69740 : int) : (term129 _69740) = (term130 _69740).
Proof. exact (MK_COMB (@lem5371800) (@lem5371799 _69740)). Qed.
Lemma lem5371802 (_69741 : int) : (real_of_int _69741) = (real_of_int _69741).
Proof. exact (eq_refl (real_of_int _69741)). Qed.
Lemma lem5371803 (_69740 : int) (_69741 : int) : (term117 _69740 _69741) = (term131 _69740 _69741).
Proof. exact (MK_COMB (@lem5371801 _69740) (@lem5371802 _69741)). Qed.
Lemma lem5371804 (_69740 : int) (_69741 : int) : (term116 _69740 _69741) = (term131 _69740 _69741).
Proof. exact (TRANS (@lem5371790 _69740 _69741) (@lem5371803 _69740 _69741)). Qed.
Lemma lem5371805 (_69740 : int) (_69741 : int) : (term84 _69741 _69740) = (term131 _69740 _69741).
Proof. exact (TRANS (@lem5371787 _69740 _69741) (@lem5371804 _69740 _69741)). Qed.
Lemma lem5371806 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5371807 (_69741 : int) (_69740 : int) : (term132 _69740 _69741) = (term133 _69741 _69740).
Proof. exact (MK_COMB (@lem5371806) (@lem5371784 _69741 _69740)). Qed.
Lemma lem5371808 (_69740 : int) (_69741 : int) : (term70 _69741 _69740) = (term134 _69740 _69741).
Proof. exact (MK_COMB (@lem5371807 _69741 _69740) (@lem5371805 _69740 _69741)). Qed.
Lemma lem5371811 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5371815 (_69741 : int) (_69740 : int) : (_69741 = _69740) = ((real_of_int _69741) = (real_of_int _69740)).
Proof. exact (@lem5371811 _69741 _69740). Qed.
Lemma lem5371816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5371817 (_69740 : int) (_69741 : int) : (term73 _69741 _69740) = (term135 _69740 _69741).
Proof. exact (MK_COMB (@lem5371816) (@lem5371808 _69740 _69741)). Qed.
Lemma lem5371818 (_69741 : int) (_69740 : int) : (term75 _69741 _69740) = (term136 _69741 _69740).
Proof. exact (MK_COMB (@lem5371817 _69740 _69741) (@lem5371815 _69741 _69740)). Qed.
Lemma lem5371821 (x : int) (y : int) : (int_le x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5371823 (_69740 : int) (_69741 : int) : (int_le _69740 _69741) = (term107 _69740 _69741).
Proof. exact (@lem5371821 _69740 _69741). Qed.
Lemma lem5371826 (x : int) (y : int) : (int_le x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5371828 (_69741 : int) (_69740 : int) : (int_le _69741 _69740) = (term107 _69741 _69740).
Proof. exact (@lem5371826 _69741 _69740). Qed.
Lemma lem5371829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5371830 (_69740 : int) (_69741 : int) : (term81 _69740 _69741) = (term137 _69740 _69741).
Proof. exact (MK_COMB (@lem5371829) (@lem5371823 _69740 _69741)). Qed.
Lemma lem5371831 (_69741 : int) (_69740 : int) : (term77 _69741 _69740) = (term138 _69741 _69740).
Proof. exact (MK_COMB (@lem5371830 _69740 _69741) (@lem5371828 _69741 _69740)). Qed.
Lemma lem5371833 (y : int) (x : int) : (term78 x y) = (term139 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem5371834 (_69740 : int) (_69741 : int) : (term78 _69741 _69740) = (term139 _69740 _69741).
Proof. exact (@lem5371833 _69740 _69741). Qed.
Lemma lem5371836 (x : int) (y : int) : (int_le x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5371837 (_69741 : int) (_69740 : int) : (term116 _69741 _69740) = (term117 _69741 _69740).
Proof. exact (@lem5371836 (term118 _69741) _69740). Qed.
Lemma lem5371839 (x : int) (y : int) : (term119 x y) = (term120 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5371840 (_69741 : int) : (term121 _69741) = (term122 _69741).
Proof. exact (@lem5371839 _69741 term123). Qed.
Lemma lem5371842 (n : nat) : (term110 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5371843 : term124 = term125.
Proof. exact (@lem5371842 term126). Qed.
Lemma lem5371844 (_69741 : int) : (term127 _69741) = (term127 _69741).
Proof. exact (eq_refl (term127 _69741)). Qed.
Lemma lem5371845 (_69741 : int) : (term122 _69741) = (term128 _69741).
Proof. exact (MK_COMB (@lem5371844 _69741) (@lem5371843)). Qed.
Lemma lem5371846 (_69741 : int) : (term121 _69741) = (term128 _69741).
Proof. exact (TRANS (@lem5371840 _69741) (@lem5371845 _69741)). Qed.
Lemma lem5371847 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5371848 (_69741 : int) : (term129 _69741) = (term130 _69741).
Proof. exact (MK_COMB (@lem5371847) (@lem5371846 _69741)). Qed.
Lemma lem5371849 (_69740 : int) : (real_of_int _69740) = (real_of_int _69740).
Proof. exact (eq_refl (real_of_int _69740)). Qed.
Lemma lem5371850 (_69741 : int) (_69740 : int) : (term117 _69741 _69740) = (term131 _69741 _69740).
Proof. exact (MK_COMB (@lem5371848 _69741) (@lem5371849 _69740)). Qed.
Lemma lem5371851 (_69741 : int) (_69740 : int) : (term116 _69741 _69740) = (term131 _69741 _69740).
Proof. exact (TRANS (@lem5371837 _69741 _69740) (@lem5371850 _69741 _69740)). Qed.
Lemma lem5371852 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5371853 (_69741 : int) (_69740 : int) : (term140 _69741 _69740) = (term133 _69741 _69740).
Proof. exact (MK_COMB (@lem5371852) (@lem5371851 _69741 _69740)). Qed.
Lemma lem5371855 (x : int) (y : int) : (int_le x y) = (term107 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5371856 (_69740 : int) (_69741 : int) : (term116 _69740 _69741) = (term117 _69740 _69741).
Proof. exact (@lem5371855 (term118 _69740) _69741). Qed.
Lemma lem5371858 (x : int) (y : int) : (term119 x y) = (term120 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5371859 (_69740 : int) : (term121 _69740) = (term122 _69740).
Proof. exact (@lem5371858 _69740 term123). Qed.
Lemma lem5371861 (n : nat) : (term110 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5371862 : term124 = term125.
Proof. exact (@lem5371861 term126). Qed.
Lemma lem5371863 (_69740 : int) : (term127 _69740) = (term127 _69740).
Proof. exact (eq_refl (term127 _69740)). Qed.
Lemma lem5371864 (_69740 : int) : (term122 _69740) = (term128 _69740).
Proof. exact (MK_COMB (@lem5371863 _69740) (@lem5371862)). Qed.
Lemma lem5371865 (_69740 : int) : (term121 _69740) = (term128 _69740).
Proof. exact (TRANS (@lem5371859 _69740) (@lem5371864 _69740)). Qed.
Lemma lem5371866 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5371867 (_69740 : int) : (term129 _69740) = (term130 _69740).
Proof. exact (MK_COMB (@lem5371866) (@lem5371865 _69740)). Qed.
Lemma lem5371868 (_69741 : int) : (real_of_int _69741) = (real_of_int _69741).
Proof. exact (eq_refl (real_of_int _69741)). Qed.
Lemma lem5371869 (_69740 : int) (_69741 : int) : (term117 _69740 _69741) = (term131 _69740 _69741).
Proof. exact (MK_COMB (@lem5371867 _69740) (@lem5371868 _69741)). Qed.
Lemma lem5371870 (_69740 : int) (_69741 : int) : (term116 _69740 _69741) = (term131 _69740 _69741).
Proof. exact (TRANS (@lem5371856 _69740 _69741) (@lem5371869 _69740 _69741)). Qed.
Lemma lem5371871 (_69740 : int) (_69741 : int) : (term139 _69740 _69741) = (term134 _69740 _69741).
Proof. exact (MK_COMB (@lem5371853 _69741 _69740) (@lem5371870 _69740 _69741)). Qed.
Lemma lem5371872 (_69740 : int) (_69741 : int) : (term78 _69741 _69740) = (term134 _69740 _69741).
Proof. exact (TRANS (@lem5371834 _69740 _69741) (@lem5371871 _69740 _69741)). Qed.
Lemma lem5371873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5371874 (_69741 : int) (_69740 : int) : (term86 _69741 _69740) = (term141 _69741 _69740).
Proof. exact (MK_COMB (@lem5371873) (@lem5371831 _69741 _69740)). Qed.
Lemma lem5371875 (_69740 : int) (_69741 : int) : (term88 _69741 _69740) = (term142 _69740 _69741).
Proof. exact (MK_COMB (@lem5371874 _69741 _69740) (@lem5371872 _69740 _69741)). Qed.
Lemma lem5371876 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5371877 (_69741 : int) (_69740 : int) : (term91 _69741 _69740) = (term143 _69741 _69740).
Proof. exact (MK_COMB (@lem5371876) (@lem5371818 _69741 _69740)). Qed.
Lemma lem5371878 (_69740 : int) (_69741 : int) : (term93 _69741 _69740) = (term144 _69740 _69741).
Proof. exact (MK_COMB (@lem5371877 _69741 _69740) (@lem5371875 _69740 _69741)). Qed.
Lemma lem5371879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5371880 (_69741 : int) : (term97 _69741) = (term145 _69741).
Proof. exact (MK_COMB (@lem5371879) (@lem5371763 _69741)). Qed.
Lemma lem5371881 (_69740 : int) (_69741 : int) : (term99 _69741 _69740) = (term146 _69740 _69741).
Proof. exact (MK_COMB (@lem5371880 _69741) (@lem5371878 _69740 _69741)). Qed.
Lemma lem5371882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5371883 (_69740 : int) : (term97 _69740) = (term145 _69740).
Proof. exact (MK_COMB (@lem5371882) (@lem5371750 _69740)). Qed.
Lemma lem5371884 (_69740 : int) (_69741 : int) : (term104 _69741 _69740) = (term147 _69740 _69741).
Proof. exact (MK_COMB (@lem5371883 _69740) (@lem5371881 _69740 _69741)). Qed.
Lemma lem5371885 (_69740 : int) (_69741 : int) : (term105 _69741 _69740) = (term147 _69740 _69741).
Proof. exact (TRANS (@lem5371737 _69741 _69740) (@lem5371884 _69740 _69741)). Qed.
Lemma lem5371889 (t : Prop) : (term148 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5371975 (_69740 : int) (_69741 : int) : (term149 _69740 _69741) = (term147 _69740 _69741).
Proof. exact (@lem5371889 (term147 _69740 _69741)). Qed.
Lemma lem5371976 (_69740 : int) : (term115 _69740) = (term150 _69740).
Proof. exact (@lem1988287 (real_of_int _69740) term112). Qed.
Lemma lem5371982 (_69740 : int) : (term151 _69740) = (term152 _69740).
Proof. exact (@lem1982792 (real_of_int _69740) term112). Qed.
Lemma lem5371984 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5371985 : term112 = term154.
Proof. exact (@lem5371984 (NUMERAL 0)). Qed.
Lemma lem5371987 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5371988 : term157 = term158.
Proof. exact (@lem5371987 term126). Qed.
Lemma lem5371989 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5371990 : term159 = term160.
Proof. exact (MK_COMB (@lem5371989) (@lem5371988)). Qed.
Lemma lem5371991 : term161 = term162.
Proof. exact (MK_COMB (@lem5371990) (@lem5371985)). Qed.
Lemma lem5371992 : term162 = term163.
Proof. exact (@lem1981613 term157 term112 term125 term125). Qed.
Lemma lem5371994 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5371995 : term166 = term167.
Proof. exact (@lem5371994 term126 term126). Qed.
Lemma lem5371996 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5371997 : term169 = term126.
Proof. exact (EQ_MP (@lem5371996) (@lem940073)). Qed.
Lemma lem5371998 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5371999 : term167 = term125.
Proof. exact (MK_COMB (@lem5371998) (@lem5371997)). Qed.
Lemma lem5372000 : term166 = term125.
Proof. exact (TRANS (@lem5371995) (@lem5371999)). Qed.
Lemma lem5372002 (x : nat) : (term170 x) = term112.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5372003 : term161 = term112.
Proof. exact (@lem5372002 term126). Qed.
Lemma lem5372004 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5372005 : term171 = term172.
Proof. exact (MK_COMB (@lem5372004) (@lem5372003)). Qed.
Lemma lem5372006 : term163 = term154.
Proof. exact (MK_COMB (@lem5372005) (@lem5372000)). Qed.
Lemma lem5372007 : term162 = term154.
Proof. exact (TRANS (@lem5371992) (@lem5372006)). Qed.
Lemma lem5372008 : term161 = term154.
Proof. exact (TRANS (@lem5371991) (@lem5372007)). Qed.
Lemma lem5372010 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5372011 : term154 = term112.
Proof. exact (@lem5372010 term112). Qed.
Lemma lem5372012 : term161 = term112.
Proof. exact (TRANS (@lem5372008) (@lem5372011)). Qed.
Lemma lem5372013 (_69740 : int) : (term127 _69740) = (term127 _69740).
Proof. exact (eq_refl (term127 _69740)). Qed.
Lemma lem5372014 (_69740 : int) : (term152 _69740) = (term174 _69740).
Proof. exact (MK_COMB (@lem5372013 _69740) (@lem5372012)). Qed.
Lemma lem5372015 (_69740 : int) : (term174 _69740) = (real_of_int _69740).
Proof. exact (@lem1982723 (real_of_int _69740)). Qed.
Lemma lem5372016 (_69740 : int) : (term152 _69740) = (real_of_int _69740).
Proof. exact (TRANS (@lem5372014 _69740) (@lem5372015 _69740)). Qed.
Lemma lem5372018 (_69740 : int) : (term151 _69740) = (real_of_int _69740).
Proof. exact (TRANS (@lem5371982 _69740) (@lem5372016 _69740)). Qed.
Lemma lem5372019 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5372020 (_69740 : int) : (term175 _69740) = (term176 _69740).
Proof. exact (MK_COMB (@lem5372019) (@lem5372018 _69740)). Qed.
Lemma lem5372021 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5372022 (_69740 : int) : (term150 _69740) = (term177 _69740).
Proof. exact (MK_COMB (@lem5372020 _69740) (@lem5372021)). Qed.
Lemma lem5372023 (_69740 : int) : (term115 _69740) = (term177 _69740).
Proof. exact (TRANS (@lem5371976 _69740) (@lem5372022 _69740)). Qed.
Lemma lem5372024 (_69741 : int) : (term115 _69741) = (term150 _69741).
Proof. exact (@lem1988287 (real_of_int _69741) term112). Qed.
Lemma lem5372030 (_69741 : int) : (term151 _69741) = (term152 _69741).
Proof. exact (@lem1982792 (real_of_int _69741) term112). Qed.
Lemma lem5372032 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5372033 : term112 = term154.
Proof. exact (@lem5372032 (NUMERAL 0)). Qed.
Lemma lem5372035 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5372036 : term157 = term158.
Proof. exact (@lem5372035 term126). Qed.
Lemma lem5372037 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5372038 : term159 = term160.
Proof. exact (MK_COMB (@lem5372037) (@lem5372036)). Qed.
Lemma lem5372039 : term161 = term162.
Proof. exact (MK_COMB (@lem5372038) (@lem5372033)). Qed.
Lemma lem5372040 : term162 = term163.
Proof. exact (@lem1981613 term157 term112 term125 term125). Qed.
Lemma lem5372042 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5372043 : term166 = term167.
Proof. exact (@lem5372042 term126 term126). Qed.
Lemma lem5372044 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372045 : term169 = term126.
Proof. exact (EQ_MP (@lem5372044) (@lem940073)). Qed.
Lemma lem5372046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372047 : term167 = term125.
Proof. exact (MK_COMB (@lem5372046) (@lem5372045)). Qed.
Lemma lem5372048 : term166 = term125.
Proof. exact (TRANS (@lem5372043) (@lem5372047)). Qed.
Lemma lem5372050 (x : nat) : (term170 x) = term112.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5372051 : term161 = term112.
Proof. exact (@lem5372050 term126). Qed.
Lemma lem5372052 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5372053 : term171 = term172.
Proof. exact (MK_COMB (@lem5372052) (@lem5372051)). Qed.
Lemma lem5372054 : term163 = term154.
Proof. exact (MK_COMB (@lem5372053) (@lem5372048)). Qed.
Lemma lem5372055 : term162 = term154.
Proof. exact (TRANS (@lem5372040) (@lem5372054)). Qed.
Lemma lem5372056 : term161 = term154.
Proof. exact (TRANS (@lem5372039) (@lem5372055)). Qed.
Lemma lem5372058 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5372059 : term154 = term112.
Proof. exact (@lem5372058 term112). Qed.
Lemma lem5372060 : term161 = term112.
Proof. exact (TRANS (@lem5372056) (@lem5372059)). Qed.
Lemma lem5372061 (_69741 : int) : (term127 _69741) = (term127 _69741).
Proof. exact (eq_refl (term127 _69741)). Qed.
Lemma lem5372062 (_69741 : int) : (term152 _69741) = (term174 _69741).
Proof. exact (MK_COMB (@lem5372061 _69741) (@lem5372060)). Qed.
Lemma lem5372063 (_69741 : int) : (term174 _69741) = (real_of_int _69741).
Proof. exact (@lem1982723 (real_of_int _69741)). Qed.
Lemma lem5372064 (_69741 : int) : (term152 _69741) = (real_of_int _69741).
Proof. exact (TRANS (@lem5372062 _69741) (@lem5372063 _69741)). Qed.
Lemma lem5372066 (_69741 : int) : (term151 _69741) = (real_of_int _69741).
Proof. exact (TRANS (@lem5372030 _69741) (@lem5372064 _69741)). Qed.
Lemma lem5372067 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5372068 (_69741 : int) : (term175 _69741) = (term176 _69741).
Proof. exact (MK_COMB (@lem5372067) (@lem5372066 _69741)). Qed.
Lemma lem5372069 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5372070 (_69741 : int) : (term150 _69741) = (term177 _69741).
Proof. exact (MK_COMB (@lem5372068 _69741) (@lem5372069)). Qed.
Lemma lem5372071 (_69741 : int) : (term115 _69741) = (term177 _69741).
Proof. exact (TRANS (@lem5372024 _69741) (@lem5372070 _69741)). Qed.
Lemma lem5372072 (_69740 : int) (_69741 : int) : (term131 _69741 _69740) = (term178 _69740 _69741).
Proof. exact (@lem1988287 (real_of_int _69740) (term128 _69741)). Qed.
Lemma lem5372084 (_69740 : int) (_69741 : int) : (term179 _69740 _69741) = (term180 _69740 _69741).
Proof. exact (@lem1982792 (real_of_int _69740) (term128 _69741)). Qed.
Lemma lem5372085 (_69741 : int) : (term181 _69741) = (term182 _69741).
Proof. exact (@lem1982781 (real_of_int _69741) term157 term125). Qed.
Lemma lem5372087 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5372088 : term125 = term183.
Proof. exact (@lem5372087 term126). Qed.
Lemma lem5372090 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5372091 : term157 = term158.
Proof. exact (@lem5372090 term126). Qed.
Lemma lem5372092 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5372093 : term159 = term160.
Proof. exact (MK_COMB (@lem5372092) (@lem5372091)). Qed.
Lemma lem5372094 : term184 = term185.
Proof. exact (MK_COMB (@lem5372093) (@lem5372088)). Qed.
Lemma lem5372095 : term185 = term186.
Proof. exact (@lem1981613 term157 term125 term125 term125). Qed.
Lemma lem5372097 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5372098 : term166 = term167.
Proof. exact (@lem5372097 term126 term126). Qed.
Lemma lem5372099 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372100 : term169 = term126.
Proof. exact (EQ_MP (@lem5372099) (@lem940073)). Qed.
Lemma lem5372101 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372102 : term167 = term125.
Proof. exact (MK_COMB (@lem5372101) (@lem5372100)). Qed.
Lemma lem5372103 : term166 = term125.
Proof. exact (TRANS (@lem5372098) (@lem5372102)). Qed.
Lemma lem5372105 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5372106 : term184 = term189.
Proof. exact (@lem5372105 term126 term126). Qed.
Lemma lem5372107 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372108 : term169 = term126.
Proof. exact (EQ_MP (@lem5372107) (@lem940073)). Qed.
Lemma lem5372109 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372110 : term167 = term125.
Proof. exact (MK_COMB (@lem5372109) (@lem5372108)). Qed.
Lemma lem5372111 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5372112 : term189 = term157.
Proof. exact (MK_COMB (@lem5372111) (@lem5372110)). Qed.
Lemma lem5372113 : term184 = term157.
Proof. exact (TRANS (@lem5372106) (@lem5372112)). Qed.
Lemma lem5372114 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5372115 : term190 = term191.
Proof. exact (MK_COMB (@lem5372114) (@lem5372113)). Qed.
Lemma lem5372116 : term186 = term158.
Proof. exact (MK_COMB (@lem5372115) (@lem5372103)). Qed.
Lemma lem5372117 : term185 = term158.
Proof. exact (TRANS (@lem5372095) (@lem5372116)). Qed.
Lemma lem5372118 : term184 = term158.
Proof. exact (TRANS (@lem5372094) (@lem5372117)). Qed.
Lemma lem5372120 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5372121 : term158 = term157.
Proof. exact (@lem5372120 term157). Qed.
Lemma lem5372122 : term184 = term157.
Proof. exact (TRANS (@lem5372118) (@lem5372121)). Qed.
Lemma lem5372125 (_69741 : int) : (term192 _69741) = (term192 _69741).
Proof. exact (eq_refl (term192 _69741)). Qed.
Lemma lem5372126 (_69741 : int) : (term182 _69741) = (term193 _69741).
Proof. exact (MK_COMB (@lem5372125 _69741) (@lem5372122)). Qed.
Lemma lem5372127 (_69741 : int) : (term181 _69741) = (term193 _69741).
Proof. exact (TRANS (@lem5372085 _69741) (@lem5372126 _69741)). Qed.
Lemma lem5372128 (_69740 : int) : (term127 _69740) = (term127 _69740).
Proof. exact (eq_refl (term127 _69740)). Qed.
Lemma lem5372131 (_69740 : int) (_69741 : int) : (term180 _69740 _69741) = (term194 _69740 _69741).
Proof. exact (MK_COMB (@lem5372128 _69740) (@lem5372127 _69741)). Qed.
Lemma lem5372133 (_69740 : int) (_69741 : int) : (term179 _69740 _69741) = (term194 _69740 _69741).
Proof. exact (TRANS (@lem5372084 _69740 _69741) (@lem5372131 _69740 _69741)). Qed.
Lemma lem5372134 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5372135 (_69740 : int) (_69741 : int) : (term195 _69740 _69741) = (term196 _69740 _69741).
Proof. exact (MK_COMB (@lem5372134) (@lem5372133 _69740 _69741)). Qed.
Lemma lem5372136 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5372137 (_69740 : int) (_69741 : int) : (term178 _69740 _69741) = (term197 _69740 _69741).
Proof. exact (MK_COMB (@lem5372135 _69740 _69741) (@lem5372136)). Qed.
Lemma lem5372138 (_69740 : int) (_69741 : int) : (term131 _69741 _69740) = (term197 _69740 _69741).
Proof. exact (TRANS (@lem5372072 _69740 _69741) (@lem5372137 _69740 _69741)). Qed.
Lemma lem5372139 (_69741 : int) (_69740 : int) : (term131 _69740 _69741) = (term178 _69741 _69740).
Proof. exact (@lem1988287 (real_of_int _69741) (term128 _69740)). Qed.
Lemma lem5372151 (_69741 : int) (_69740 : int) : (term179 _69741 _69740) = (term180 _69741 _69740).
Proof. exact (@lem1982792 (real_of_int _69741) (term128 _69740)). Qed.
Lemma lem5372152 (_69740 : int) : (term181 _69740) = (term182 _69740).
Proof. exact (@lem1982781 (real_of_int _69740) term157 term125). Qed.
Lemma lem5372154 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5372155 : term125 = term183.
Proof. exact (@lem5372154 term126). Qed.
Lemma lem5372157 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5372158 : term157 = term158.
Proof. exact (@lem5372157 term126). Qed.
Lemma lem5372159 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5372160 : term159 = term160.
Proof. exact (MK_COMB (@lem5372159) (@lem5372158)). Qed.
Lemma lem5372161 : term184 = term185.
Proof. exact (MK_COMB (@lem5372160) (@lem5372155)). Qed.
Lemma lem5372162 : term185 = term186.
Proof. exact (@lem1981613 term157 term125 term125 term125). Qed.
Lemma lem5372164 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5372165 : term166 = term167.
Proof. exact (@lem5372164 term126 term126). Qed.
Lemma lem5372166 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372167 : term169 = term126.
Proof. exact (EQ_MP (@lem5372166) (@lem940073)). Qed.
Lemma lem5372168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372169 : term167 = term125.
Proof. exact (MK_COMB (@lem5372168) (@lem5372167)). Qed.
Lemma lem5372170 : term166 = term125.
Proof. exact (TRANS (@lem5372165) (@lem5372169)). Qed.
Lemma lem5372172 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5372173 : term184 = term189.
Proof. exact (@lem5372172 term126 term126). Qed.
Lemma lem5372174 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372175 : term169 = term126.
Proof. exact (EQ_MP (@lem5372174) (@lem940073)). Qed.
Lemma lem5372176 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372177 : term167 = term125.
Proof. exact (MK_COMB (@lem5372176) (@lem5372175)). Qed.
Lemma lem5372178 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5372179 : term189 = term157.
Proof. exact (MK_COMB (@lem5372178) (@lem5372177)). Qed.
Lemma lem5372180 : term184 = term157.
Proof. exact (TRANS (@lem5372173) (@lem5372179)). Qed.
Lemma lem5372181 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5372182 : term190 = term191.
Proof. exact (MK_COMB (@lem5372181) (@lem5372180)). Qed.
Lemma lem5372183 : term186 = term158.
Proof. exact (MK_COMB (@lem5372182) (@lem5372170)). Qed.
Lemma lem5372184 : term185 = term158.
Proof. exact (TRANS (@lem5372162) (@lem5372183)). Qed.
Lemma lem5372185 : term184 = term158.
Proof. exact (TRANS (@lem5372161) (@lem5372184)). Qed.
Lemma lem5372187 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5372188 : term158 = term157.
Proof. exact (@lem5372187 term157). Qed.
Lemma lem5372189 : term184 = term157.
Proof. exact (TRANS (@lem5372185) (@lem5372188)). Qed.
Lemma lem5372192 (_69740 : int) : (term192 _69740) = (term192 _69740).
Proof. exact (eq_refl (term192 _69740)). Qed.
Lemma lem5372193 (_69740 : int) : (term182 _69740) = (term193 _69740).
Proof. exact (MK_COMB (@lem5372192 _69740) (@lem5372189)). Qed.
Lemma lem5372194 (_69740 : int) : (term181 _69740) = (term193 _69740).
Proof. exact (TRANS (@lem5372152 _69740) (@lem5372193 _69740)). Qed.
Lemma lem5372195 (_69741 : int) : (term127 _69741) = (term127 _69741).
Proof. exact (eq_refl (term127 _69741)). Qed.
Lemma lem5372196 (_69741 : int) (_69740 : int) : (term180 _69741 _69740) = (term194 _69741 _69740).
Proof. exact (MK_COMB (@lem5372195 _69741) (@lem5372194 _69740)). Qed.
Lemma lem5372201 (_69740 : int) (_69741 : int) : (term194 _69741 _69740) = (term198 _69740 _69741).
Proof. exact (@lem1982757 (term199 _69740) (real_of_int _69741) term157). Qed.
Lemma lem5372202 (_69740 : int) (_69741 : int) : (term180 _69741 _69740) = (term198 _69740 _69741).
Proof. exact (TRANS (@lem5372196 _69741 _69740) (@lem5372201 _69740 _69741)). Qed.
Lemma lem5372204 (_69740 : int) (_69741 : int) : (term179 _69741 _69740) = (term198 _69740 _69741).
Proof. exact (TRANS (@lem5372151 _69741 _69740) (@lem5372202 _69740 _69741)). Qed.
Lemma lem5372205 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5372206 (_69740 : int) (_69741 : int) : (term195 _69741 _69740) = (term200 _69740 _69741).
Proof. exact (MK_COMB (@lem5372205) (@lem5372204 _69740 _69741)). Qed.
Lemma lem5372207 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5372208 (_69740 : int) (_69741 : int) : (term178 _69741 _69740) = (term201 _69740 _69741).
Proof. exact (MK_COMB (@lem5372206 _69740 _69741) (@lem5372207)). Qed.
Lemma lem5372209 (_69740 : int) (_69741 : int) : (term131 _69740 _69741) = (term201 _69740 _69741).
Proof. exact (TRANS (@lem5372139 _69741 _69740) (@lem5372208 _69740 _69741)). Qed.
Lemma lem5372210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5372211 (_69740 : int) (_69741 : int) : (term133 _69741 _69740) = (term202 _69740 _69741).
Proof. exact (MK_COMB (@lem5372210) (@lem5372138 _69740 _69741)). Qed.
Lemma lem5372212 (_69740 : int) (_69741 : int) : (term134 _69740 _69741) = (term203 _69740 _69741).
Proof. exact (MK_COMB (@lem5372211 _69740 _69741) (@lem5372209 _69740 _69741)). Qed.
Lemma lem5372213 (_69741 : int) (_69740 : int) : ((real_of_int _69741) = (real_of_int _69740)) = ((term204 _69741 _69740) = term112).
Proof. exact (@lem1988293 (real_of_int _69741) (real_of_int _69740)). Qed.
Lemma lem5372219 (_69741 : int) (_69740 : int) : (term204 _69741 _69740) = (term205 _69741 _69740).
Proof. exact (@lem1982792 (real_of_int _69741) (real_of_int _69740)). Qed.
Lemma lem5372224 (_69740 : int) (_69741 : int) : (term205 _69741 _69740) = (term206 _69740 _69741).
Proof. exact (@lem1982761 (term199 _69740) (real_of_int _69741)). Qed.
Lemma lem5372226 (_69740 : int) (_69741 : int) : (term204 _69741 _69740) = (term206 _69740 _69741).
Proof. exact (TRANS (@lem5372219 _69741 _69740) (@lem5372224 _69740 _69741)). Qed.
Lemma lem5372227 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5372228 (_69740 : int) (_69741 : int) : (term207 _69741 _69740) = (term208 _69740 _69741).
Proof. exact (MK_COMB (@lem5372227) (@lem5372226 _69740 _69741)). Qed.
Lemma lem5372229 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5372230 (_69740 : int) (_69741 : int) : ((term204 _69741 _69740) = term112) = ((term206 _69740 _69741) = term112).
Proof. exact (MK_COMB (@lem5372228 _69740 _69741) (@lem5372229)). Qed.
Lemma lem5372231 (_69740 : int) (_69741 : int) : ((real_of_int _69741) = (real_of_int _69740)) = ((term206 _69740 _69741) = term112).
Proof. exact (TRANS (@lem5372213 _69741 _69740) (@lem5372230 _69740 _69741)). Qed.
Lemma lem5372232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5372233 (_69740 : int) (_69741 : int) : (term135 _69740 _69741) = (term209 _69740 _69741).
Proof. exact (MK_COMB (@lem5372232) (@lem5372212 _69740 _69741)). Qed.
Lemma lem5372234 (_69740 : int) (_69741 : int) : (term136 _69741 _69740) = (term210 _69740 _69741).
Proof. exact (MK_COMB (@lem5372233 _69740 _69741) (@lem5372231 _69740 _69741)). Qed.
Lemma lem5372235 (_69741 : int) (_69740 : int) : (term107 _69740 _69741) = (term211 _69741 _69740).
Proof. exact (@lem1988287 (real_of_int _69741) (real_of_int _69740)). Qed.
Lemma lem5372241 (_69741 : int) (_69740 : int) : (term204 _69741 _69740) = (term205 _69741 _69740).
Proof. exact (@lem1982792 (real_of_int _69741) (real_of_int _69740)). Qed.
Lemma lem5372246 (_69740 : int) (_69741 : int) : (term205 _69741 _69740) = (term206 _69740 _69741).
Proof. exact (@lem1982761 (term199 _69740) (real_of_int _69741)). Qed.
Lemma lem5372248 (_69740 : int) (_69741 : int) : (term204 _69741 _69740) = (term206 _69740 _69741).
Proof. exact (TRANS (@lem5372241 _69741 _69740) (@lem5372246 _69740 _69741)). Qed.
Lemma lem5372249 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5372250 (_69740 : int) (_69741 : int) : (term212 _69741 _69740) = (term213 _69740 _69741).
Proof. exact (MK_COMB (@lem5372249) (@lem5372248 _69740 _69741)). Qed.
Lemma lem5372251 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5372252 (_69740 : int) (_69741 : int) : (term211 _69741 _69740) = (term214 _69740 _69741).
Proof. exact (MK_COMB (@lem5372250 _69740 _69741) (@lem5372251)). Qed.
Lemma lem5372253 (_69740 : int) (_69741 : int) : (term107 _69740 _69741) = (term214 _69740 _69741).
Proof. exact (TRANS (@lem5372235 _69741 _69740) (@lem5372252 _69740 _69741)). Qed.
Lemma lem5372254 (_69740 : int) (_69741 : int) : (term107 _69741 _69740) = (term211 _69740 _69741).
Proof. exact (@lem1988287 (real_of_int _69740) (real_of_int _69741)). Qed.
Lemma lem5372267 (_69740 : int) (_69741 : int) : (term204 _69740 _69741) = (term205 _69740 _69741).
Proof. exact (@lem1982792 (real_of_int _69740) (real_of_int _69741)). Qed.
Lemma lem5372268 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5372269 (_69740 : int) (_69741 : int) : (term212 _69740 _69741) = (term215 _69740 _69741).
Proof. exact (MK_COMB (@lem5372268) (@lem5372267 _69740 _69741)). Qed.
Lemma lem5372270 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5372271 (_69740 : int) (_69741 : int) : (term211 _69740 _69741) = (term216 _69740 _69741).
Proof. exact (MK_COMB (@lem5372269 _69740 _69741) (@lem5372270)). Qed.
Lemma lem5372272 (_69740 : int) (_69741 : int) : (term107 _69741 _69740) = (term216 _69740 _69741).
Proof. exact (TRANS (@lem5372254 _69740 _69741) (@lem5372271 _69740 _69741)). Qed.
Lemma lem5372273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5372274 (_69740 : int) (_69741 : int) : (term137 _69740 _69741) = (term217 _69740 _69741).
Proof. exact (MK_COMB (@lem5372273) (@lem5372253 _69740 _69741)). Qed.
Lemma lem5372275 (_69740 : int) (_69741 : int) : (term138 _69741 _69740) = (term218 _69740 _69741).
Proof. exact (MK_COMB (@lem5372274 _69740 _69741) (@lem5372272 _69740 _69741)). Qed.
Lemma lem5372276 (_69740 : int) (_69741 : int) : (term131 _69741 _69740) = (term178 _69740 _69741).
Proof. exact (@lem1988287 (real_of_int _69740) (term128 _69741)). Qed.
Lemma lem5372288 (_69740 : int) (_69741 : int) : (term179 _69740 _69741) = (term180 _69740 _69741).
Proof. exact (@lem1982792 (real_of_int _69740) (term128 _69741)). Qed.
Lemma lem5372289 (_69741 : int) : (term181 _69741) = (term182 _69741).
Proof. exact (@lem1982781 (real_of_int _69741) term157 term125). Qed.
Lemma lem5372291 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5372292 : term125 = term183.
Proof. exact (@lem5372291 term126). Qed.
Lemma lem5372294 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5372295 : term157 = term158.
Proof. exact (@lem5372294 term126). Qed.
Lemma lem5372296 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5372297 : term159 = term160.
Proof. exact (MK_COMB (@lem5372296) (@lem5372295)). Qed.
Lemma lem5372298 : term184 = term185.
Proof. exact (MK_COMB (@lem5372297) (@lem5372292)). Qed.
Lemma lem5372299 : term185 = term186.
Proof. exact (@lem1981613 term157 term125 term125 term125). Qed.
Lemma lem5372301 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5372302 : term166 = term167.
Proof. exact (@lem5372301 term126 term126). Qed.
Lemma lem5372303 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372304 : term169 = term126.
Proof. exact (EQ_MP (@lem5372303) (@lem940073)). Qed.
Lemma lem5372305 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372306 : term167 = term125.
Proof. exact (MK_COMB (@lem5372305) (@lem5372304)). Qed.
Lemma lem5372307 : term166 = term125.
Proof. exact (TRANS (@lem5372302) (@lem5372306)). Qed.
Lemma lem5372309 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5372310 : term184 = term189.
Proof. exact (@lem5372309 term126 term126). Qed.
Lemma lem5372311 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372312 : term169 = term126.
Proof. exact (EQ_MP (@lem5372311) (@lem940073)). Qed.
Lemma lem5372313 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372314 : term167 = term125.
Proof. exact (MK_COMB (@lem5372313) (@lem5372312)). Qed.
Lemma lem5372315 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5372316 : term189 = term157.
Proof. exact (MK_COMB (@lem5372315) (@lem5372314)). Qed.
Lemma lem5372317 : term184 = term157.
Proof. exact (TRANS (@lem5372310) (@lem5372316)). Qed.
Lemma lem5372318 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5372319 : term190 = term191.
Proof. exact (MK_COMB (@lem5372318) (@lem5372317)). Qed.
Lemma lem5372320 : term186 = term158.
Proof. exact (MK_COMB (@lem5372319) (@lem5372307)). Qed.
Lemma lem5372321 : term185 = term158.
Proof. exact (TRANS (@lem5372299) (@lem5372320)). Qed.
Lemma lem5372322 : term184 = term158.
Proof. exact (TRANS (@lem5372298) (@lem5372321)). Qed.
Lemma lem5372324 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5372325 : term158 = term157.
Proof. exact (@lem5372324 term157). Qed.
Lemma lem5372326 : term184 = term157.
Proof. exact (TRANS (@lem5372322) (@lem5372325)). Qed.
Lemma lem5372329 (_69741 : int) : (term192 _69741) = (term192 _69741).
Proof. exact (eq_refl (term192 _69741)). Qed.
Lemma lem5372330 (_69741 : int) : (term182 _69741) = (term193 _69741).
Proof. exact (MK_COMB (@lem5372329 _69741) (@lem5372326)). Qed.
Lemma lem5372331 (_69741 : int) : (term181 _69741) = (term193 _69741).
Proof. exact (TRANS (@lem5372289 _69741) (@lem5372330 _69741)). Qed.
Lemma lem5372332 (_69740 : int) : (term127 _69740) = (term127 _69740).
Proof. exact (eq_refl (term127 _69740)). Qed.
Lemma lem5372335 (_69740 : int) (_69741 : int) : (term180 _69740 _69741) = (term194 _69740 _69741).
Proof. exact (MK_COMB (@lem5372332 _69740) (@lem5372331 _69741)). Qed.
Lemma lem5372337 (_69740 : int) (_69741 : int) : (term179 _69740 _69741) = (term194 _69740 _69741).
Proof. exact (TRANS (@lem5372288 _69740 _69741) (@lem5372335 _69740 _69741)). Qed.
Lemma lem5372338 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5372339 (_69740 : int) (_69741 : int) : (term195 _69740 _69741) = (term196 _69740 _69741).
Proof. exact (MK_COMB (@lem5372338) (@lem5372337 _69740 _69741)). Qed.
Lemma lem5372340 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5372341 (_69740 : int) (_69741 : int) : (term178 _69740 _69741) = (term197 _69740 _69741).
Proof. exact (MK_COMB (@lem5372339 _69740 _69741) (@lem5372340)). Qed.
Lemma lem5372342 (_69740 : int) (_69741 : int) : (term131 _69741 _69740) = (term197 _69740 _69741).
Proof. exact (TRANS (@lem5372276 _69740 _69741) (@lem5372341 _69740 _69741)). Qed.
Lemma lem5372343 (_69741 : int) (_69740 : int) : (term131 _69740 _69741) = (term178 _69741 _69740).
Proof. exact (@lem1988287 (real_of_int _69741) (term128 _69740)). Qed.
Lemma lem5372355 (_69741 : int) (_69740 : int) : (term179 _69741 _69740) = (term180 _69741 _69740).
Proof. exact (@lem1982792 (real_of_int _69741) (term128 _69740)). Qed.
Lemma lem5372356 (_69740 : int) : (term181 _69740) = (term182 _69740).
Proof. exact (@lem1982781 (real_of_int _69740) term157 term125). Qed.
Lemma lem5372358 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5372359 : term125 = term183.
Proof. exact (@lem5372358 term126). Qed.
Lemma lem5372361 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5372362 : term157 = term158.
Proof. exact (@lem5372361 term126). Qed.
Lemma lem5372363 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5372364 : term159 = term160.
Proof. exact (MK_COMB (@lem5372363) (@lem5372362)). Qed.
Lemma lem5372365 : term184 = term185.
Proof. exact (MK_COMB (@lem5372364) (@lem5372359)). Qed.
Lemma lem5372366 : term185 = term186.
Proof. exact (@lem1981613 term157 term125 term125 term125). Qed.
Lemma lem5372368 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5372369 : term166 = term167.
Proof. exact (@lem5372368 term126 term126). Qed.
Lemma lem5372370 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372371 : term169 = term126.
Proof. exact (EQ_MP (@lem5372370) (@lem940073)). Qed.
Lemma lem5372372 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372373 : term167 = term125.
Proof. exact (MK_COMB (@lem5372372) (@lem5372371)). Qed.
Lemma lem5372374 : term166 = term125.
Proof. exact (TRANS (@lem5372369) (@lem5372373)). Qed.
Lemma lem5372376 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5372377 : term184 = term189.
Proof. exact (@lem5372376 term126 term126). Qed.
Lemma lem5372378 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372379 : term169 = term126.
Proof. exact (EQ_MP (@lem5372378) (@lem940073)). Qed.
Lemma lem5372380 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372381 : term167 = term125.
Proof. exact (MK_COMB (@lem5372380) (@lem5372379)). Qed.
Lemma lem5372382 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5372383 : term189 = term157.
Proof. exact (MK_COMB (@lem5372382) (@lem5372381)). Qed.
Lemma lem5372384 : term184 = term157.
Proof. exact (TRANS (@lem5372377) (@lem5372383)). Qed.
Lemma lem5372385 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5372386 : term190 = term191.
Proof. exact (MK_COMB (@lem5372385) (@lem5372384)). Qed.
Lemma lem5372387 : term186 = term158.
Proof. exact (MK_COMB (@lem5372386) (@lem5372374)). Qed.
Lemma lem5372388 : term185 = term158.
Proof. exact (TRANS (@lem5372366) (@lem5372387)). Qed.
Lemma lem5372389 : term184 = term158.
Proof. exact (TRANS (@lem5372365) (@lem5372388)). Qed.
Lemma lem5372391 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5372392 : term158 = term157.
Proof. exact (@lem5372391 term157). Qed.
Lemma lem5372393 : term184 = term157.
Proof. exact (TRANS (@lem5372389) (@lem5372392)). Qed.
Lemma lem5372396 (_69740 : int) : (term192 _69740) = (term192 _69740).
Proof. exact (eq_refl (term192 _69740)). Qed.
Lemma lem5372397 (_69740 : int) : (term182 _69740) = (term193 _69740).
Proof. exact (MK_COMB (@lem5372396 _69740) (@lem5372393)). Qed.
Lemma lem5372398 (_69740 : int) : (term181 _69740) = (term193 _69740).
Proof. exact (TRANS (@lem5372356 _69740) (@lem5372397 _69740)). Qed.
Lemma lem5372399 (_69741 : int) : (term127 _69741) = (term127 _69741).
Proof. exact (eq_refl (term127 _69741)). Qed.
Lemma lem5372400 (_69741 : int) (_69740 : int) : (term180 _69741 _69740) = (term194 _69741 _69740).
Proof. exact (MK_COMB (@lem5372399 _69741) (@lem5372398 _69740)). Qed.
Lemma lem5372405 (_69740 : int) (_69741 : int) : (term194 _69741 _69740) = (term198 _69740 _69741).
Proof. exact (@lem1982757 (term199 _69740) (real_of_int _69741) term157). Qed.
Lemma lem5372406 (_69740 : int) (_69741 : int) : (term180 _69741 _69740) = (term198 _69740 _69741).
Proof. exact (TRANS (@lem5372400 _69741 _69740) (@lem5372405 _69740 _69741)). Qed.
Lemma lem5372408 (_69740 : int) (_69741 : int) : (term179 _69741 _69740) = (term198 _69740 _69741).
Proof. exact (TRANS (@lem5372355 _69741 _69740) (@lem5372406 _69740 _69741)). Qed.
Lemma lem5372409 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5372410 (_69740 : int) (_69741 : int) : (term195 _69741 _69740) = (term200 _69740 _69741).
Proof. exact (MK_COMB (@lem5372409) (@lem5372408 _69740 _69741)). Qed.
Lemma lem5372411 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5372412 (_69740 : int) (_69741 : int) : (term178 _69741 _69740) = (term201 _69740 _69741).
Proof. exact (MK_COMB (@lem5372410 _69740 _69741) (@lem5372411)). Qed.
Lemma lem5372413 (_69740 : int) (_69741 : int) : (term131 _69740 _69741) = (term201 _69740 _69741).
Proof. exact (TRANS (@lem5372343 _69741 _69740) (@lem5372412 _69740 _69741)). Qed.
Lemma lem5372414 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5372415 (_69740 : int) (_69741 : int) : (term133 _69741 _69740) = (term202 _69740 _69741).
Proof. exact (MK_COMB (@lem5372414) (@lem5372342 _69740 _69741)). Qed.
Lemma lem5372416 (_69740 : int) (_69741 : int) : (term134 _69740 _69741) = (term203 _69740 _69741).
Proof. exact (MK_COMB (@lem5372415 _69740 _69741) (@lem5372413 _69740 _69741)). Qed.
Lemma lem5372417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5372418 (_69740 : int) (_69741 : int) : (term141 _69741 _69740) = (term219 _69740 _69741).
Proof. exact (MK_COMB (@lem5372417) (@lem5372275 _69740 _69741)). Qed.
Lemma lem5372419 (_69740 : int) (_69741 : int) : (term142 _69740 _69741) = (term220 _69740 _69741).
Proof. exact (MK_COMB (@lem5372418 _69740 _69741) (@lem5372416 _69740 _69741)). Qed.
Lemma lem5372420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5372421 (_69740 : int) (_69741 : int) : (term143 _69741 _69740) = (term221 _69740 _69741).
Proof. exact (MK_COMB (@lem5372420) (@lem5372234 _69740 _69741)). Qed.
Lemma lem5372422 (_69740 : int) (_69741 : int) : (term144 _69740 _69741) = (term222 _69740 _69741).
Proof. exact (MK_COMB (@lem5372421 _69740 _69741) (@lem5372419 _69740 _69741)). Qed.
Lemma lem5372423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5372424 (_69741 : int) : (term145 _69741) = (term223 _69741).
Proof. exact (MK_COMB (@lem5372423) (@lem5372071 _69741)). Qed.
Lemma lem5372425 (_69740 : int) (_69741 : int) : (term146 _69740 _69741) = (term224 _69740 _69741).
Proof. exact (MK_COMB (@lem5372424 _69741) (@lem5372422 _69740 _69741)). Qed.
Lemma lem5372426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5372427 (_69740 : int) : (term145 _69740) = (term223 _69740).
Proof. exact (MK_COMB (@lem5372426) (@lem5372023 _69740)). Qed.
Lemma lem5372428 (_69740 : int) (_69741 : int) : (term147 _69740 _69741) = (term225 _69740 _69741).
Proof. exact (MK_COMB (@lem5372427 _69740) (@lem5372425 _69740 _69741)). Qed.
Lemma lem5372435 (_69740 : int) (_69741 : int) : (term149 _69740 _69741) = (term225 _69740 _69741).
Proof. exact (TRANS (@lem5371975 _69740 _69741) (@lem5372428 _69740 _69741)). Qed.
Lemma lem5372458 (_69740 : int) (_69741 : int) : (term220 _69740 _69741) = (term226 _69740 _69741).
Proof. exact (@lem19158 (term197 _69740 _69741) (term218 _69740 _69741) (term201 _69740 _69741)). Qed.
Lemma lem5372475 (_69740 : int) (_69741 : int) : (term210 _69740 _69741) = (term227 _69740 _69741).
Proof. exact (@lem19367 (term197 _69740 _69741) (term201 _69740 _69741) ((term206 _69740 _69741) = term112)). Qed.
Lemma lem5372476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5372477 (_69740 : int) (_69741 : int) : (term221 _69740 _69741) = (term228 _69740 _69741).
Proof. exact (MK_COMB (@lem5372476) (@lem5372475 _69740 _69741)). Qed.
Lemma lem5372478 (_69740 : int) (_69741 : int) : (term222 _69740 _69741) = (term229 _69740 _69741).
Proof. exact (MK_COMB (@lem5372477 _69740 _69741) (@lem5372458 _69740 _69741)). Qed.
Lemma lem5372481 (_69741 : int) : (term223 _69741) = (term223 _69741).
Proof. exact (eq_refl (term223 _69741)). Qed.
Lemma lem5372482 (_69740 : int) (_69741 : int) : (term224 _69740 _69741) = (term230 _69740 _69741).
Proof. exact (MK_COMB (@lem5372481 _69741) (@lem5372478 _69740 _69741)). Qed.
Lemma lem5372483 (_69740 : int) (_69741 : int) : (term230 _69740 _69741) = (term231 _69740 _69741).
Proof. exact (@lem19158 (term227 _69740 _69741) (term177 _69741) (term226 _69740 _69741)). Qed.
Lemma lem5372490 (_69740 : int) (_69741 : int) : (term232 _69740 _69741) = (term233 _69740 _69741).
Proof. exact (@lem19158 (term234 _69740 _69741) (term177 _69741) (term235 _69740 _69741)). Qed.
Lemma lem5372497 (_69740 : int) (_69741 : int) : (term236 _69740 _69741) = (term237 _69740 _69741).
Proof. exact (@lem19158 (term238 _69740 _69741) (term177 _69741) (term239 _69740 _69741)). Qed.
Lemma lem5372498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5372499 (_69740 : int) (_69741 : int) : (term240 _69740 _69741) = (term241 _69740 _69741).
Proof. exact (MK_COMB (@lem5372498) (@lem5372497 _69740 _69741)). Qed.
Lemma lem5372500 (_69740 : int) (_69741 : int) : (term231 _69740 _69741) = (term242 _69740 _69741).
Proof. exact (MK_COMB (@lem5372499 _69740 _69741) (@lem5372490 _69740 _69741)). Qed.
Lemma lem5372501 (_69740 : int) (_69741 : int) : (term230 _69740 _69741) = (term242 _69740 _69741).
Proof. exact (TRANS (@lem5372483 _69740 _69741) (@lem5372500 _69740 _69741)). Qed.
Lemma lem5372502 (_69740 : int) (_69741 : int) : (term224 _69740 _69741) = (term242 _69740 _69741).
Proof. exact (TRANS (@lem5372482 _69740 _69741) (@lem5372501 _69740 _69741)). Qed.
Lemma lem5372505 (_69740 : int) : (term223 _69740) = (term223 _69740).
Proof. exact (eq_refl (term223 _69740)). Qed.
Lemma lem5372506 (_69740 : int) (_69741 : int) : (term225 _69740 _69741) = (term243 _69740 _69741).
Proof. exact (MK_COMB (@lem5372505 _69740) (@lem5372502 _69740 _69741)). Qed.
Lemma lem5372507 (_69740 : int) (_69741 : int) : (term243 _69740 _69741) = (term244 _69740 _69741).
Proof. exact (@lem19158 (term237 _69740 _69741) (term177 _69740) (term233 _69740 _69741)). Qed.
Lemma lem5372514 (_69740 : int) (_69741 : int) : (term245 _69740 _69741) = (term246 _69740 _69741).
Proof. exact (@lem19158 (term247 _69740 _69741) (term177 _69740) (term248 _69740 _69741)). Qed.
Lemma lem5372521 (_69740 : int) (_69741 : int) : (term249 _69740 _69741) = (term250 _69740 _69741).
Proof. exact (@lem19158 (term251 _69740 _69741) (term177 _69740) (term252 _69740 _69741)). Qed.
Lemma lem5372522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5372523 (_69740 : int) (_69741 : int) : (term253 _69740 _69741) = (term254 _69740 _69741).
Proof. exact (MK_COMB (@lem5372522) (@lem5372521 _69740 _69741)). Qed.
Lemma lem5372524 (_69740 : int) (_69741 : int) : (term244 _69740 _69741) = (term255 _69740 _69741).
Proof. exact (MK_COMB (@lem5372523 _69740 _69741) (@lem5372514 _69740 _69741)). Qed.
Lemma lem5372525 (_69740 : int) (_69741 : int) : (term243 _69740 _69741) = (term255 _69740 _69741).
Proof. exact (TRANS (@lem5372507 _69740 _69741) (@lem5372524 _69740 _69741)). Qed.
Lemma lem5372526 (_69740 : int) (_69741 : int) : (term225 _69740 _69741) = (term255 _69740 _69741).
Proof. exact (TRANS (@lem5372506 _69740 _69741) (@lem5372525 _69740 _69741)). Qed.
Lemma lem5372527 (_69740 : int) (_69741 : int) : (term149 _69740 _69741) = (term255 _69740 _69741).
Proof. exact (TRANS (@lem5372435 _69740 _69741) (@lem5372526 _69740 _69741)). Qed.
Lemma lem5372549 (_69740 : int) (_69741 : int) (h1 : term255 _69740 _69741) : term255 _69740 _69741.
Proof. exact (h1). Qed.
Lemma lem5372550 (_69740 : int) (_69741 : int) (h1 : term250 _69740 _69741) : term250 _69740 _69741.
Proof. exact (h1). Qed.
Lemma lem5372551 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : term256 _69740 _69741.
Proof. exact (h1). Qed.
Lemma lem5372552 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : term251 _69740 _69741.
Proof. exact (proj2 (@lem5372551 _69740 _69741 h1)). Qed.
Lemma lem5372554 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : term238 _69740 _69741.
Proof. exact (proj2 (@lem5372552 _69740 _69741 h1)). Qed.
Lemma lem5372556 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : (term206 _69740 _69741) = term112.
Proof. exact (proj2 (@lem5372554 _69740 _69741 h1)). Qed.
Lemma lem5372557 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : term197 _69740 _69741.
Proof. exact (proj1 (@lem5372554 _69740 _69741 h1)). Qed.
Lemma lem5372559 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5372560 : term257 = term258.
Proof. exact (@lem5372559 term112 term125). Qed.
Lemma lem5372562 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5372563 : term125 = term183.
Proof. exact (@lem5372562 term126). Qed.
Lemma lem5372565 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5372566 : term112 = term154.
Proof. exact (@lem5372565 (NUMERAL 0)). Qed.
Lemma lem5372567 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5372568 : term259 = term260.
Proof. exact (MK_COMB (@lem5372567) (@lem5372566)). Qed.
Lemma lem5372569 : term258 = term261.
Proof. exact (MK_COMB (@lem5372568) (@lem5372563)). Qed.
Lemma lem5372570 : term262.
Proof. exact (@lem1980255 term112 term125 term125 term125). Qed.
Lemma lem5372572 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372573 : term258 = term264.
Proof. exact (@lem5372572 (NUMERAL 0) term126). Qed.
Lemma lem5372574 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372575 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372576 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372575 h1) (fun h1 : term264 = True => @lem5372574)). Qed.
Lemma lem5372577 : term264 = True.
Proof. exact (EQ_MP (@lem5372576) (@lem5372574)). Qed.
Lemma lem5372578 : term258 = True.
Proof. exact (TRANS (@lem5372573) (@lem5372577)). Qed.
Lemma lem5372579 : True = term258.
Proof. exact (SYM (@lem5372578)). Qed.
Lemma lem5372580 : term258.
Proof. exact (EQ_MP (@lem5372579) (@lem0)). Qed.
Lemma lem5372581 : term266.
Proof. exact (@lem5372570 (@lem5372580)). Qed.
Lemma lem5372583 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372584 : term258 = term264.
Proof. exact (@lem5372583 (NUMERAL 0) term126). Qed.
Lemma lem5372585 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372586 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372587 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372586 h1) (fun h1 : term264 = True => @lem5372585)). Qed.
Lemma lem5372588 : term264 = True.
Proof. exact (EQ_MP (@lem5372587) (@lem5372585)). Qed.
Lemma lem5372589 : term258 = True.
Proof. exact (TRANS (@lem5372584) (@lem5372588)). Qed.
Lemma lem5372590 : True = term258.
Proof. exact (SYM (@lem5372589)). Qed.
Lemma lem5372591 : term258.
Proof. exact (EQ_MP (@lem5372590) (@lem0)). Qed.
Lemma lem5372592 : term261 = term267.
Proof. exact (@lem5372581 (@lem5372591)). Qed.
Lemma lem5372594 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5372595 : term166 = term167.
Proof. exact (@lem5372594 term126 term126). Qed.
Lemma lem5372596 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372597 : term169 = term126.
Proof. exact (EQ_MP (@lem5372596) (@lem940073)). Qed.
Lemma lem5372598 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372599 : term167 = term125.
Proof. exact (MK_COMB (@lem5372598) (@lem5372597)). Qed.
Lemma lem5372600 : term166 = term125.
Proof. exact (TRANS (@lem5372595) (@lem5372599)). Qed.
Lemma lem5372602 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5372603 : term269 = term112.
Proof. exact (@lem5372602 term126). Qed.
Lemma lem5372604 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5372605 : term270 = term259.
Proof. exact (MK_COMB (@lem5372604) (@lem5372603)). Qed.
Lemma lem5372606 : term267 = term258.
Proof. exact (MK_COMB (@lem5372605) (@lem5372600)). Qed.
Lemma lem5372608 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372609 : term258 = term264.
Proof. exact (@lem5372608 (NUMERAL 0) term126). Qed.
Lemma lem5372610 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372611 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372612 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372611 h1) (fun h1 : term264 = True => @lem5372610)). Qed.
Lemma lem5372613 : term264 = True.
Proof. exact (EQ_MP (@lem5372612) (@lem5372610)). Qed.
Lemma lem5372614 : term258 = True.
Proof. exact (TRANS (@lem5372609) (@lem5372613)). Qed.
Lemma lem5372615 : term267 = True.
Proof. exact (TRANS (@lem5372606) (@lem5372614)). Qed.
Lemma lem5372616 : term261 = True.
Proof. exact (TRANS (@lem5372592) (@lem5372615)). Qed.
Lemma lem5372617 : term258 = True.
Proof. exact (TRANS (@lem5372569) (@lem5372616)). Qed.
Lemma lem5372618 : term257 = True.
Proof. exact (TRANS (@lem5372560) (@lem5372617)). Qed.
Lemma lem5372619 : True = term257.
Proof. exact (SYM (@lem5372618)). Qed.
Lemma lem5372620 : term257.
Proof. exact (EQ_MP (@lem5372619) (@lem0)). Qed.
Lemma lem5372621 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : term271 _69740 _69741.
Proof. exact (conj (@lem5372620) (@lem5372557 _69740 _69741 h1)). Qed.
Lemma lem5372623 (x : real) (y : real) : term272 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5372624 (_69740 : int) (_69741 : int) : term273 _69740 _69741.
Proof. exact (@lem5372623 term125 (term194 _69740 _69741)). Qed.
Lemma lem5372625 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : term274 _69740 _69741.
Proof. exact (@lem5372624 _69740 _69741 (@lem5372621 _69740 _69741 h1)). Qed.
Lemma lem5372626 (_69740 : int) (_69741 : int) : (term275 _69740 _69741) = (term194 _69740 _69741).
Proof. exact (@lem1982733 (term194 _69740 _69741)). Qed.
Lemma lem5372627 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5372628 (_69740 : int) (_69741 : int) : (term276 _69740 _69741) = (term196 _69740 _69741).
Proof. exact (MK_COMB (@lem5372627) (@lem5372626 _69740 _69741)). Qed.
Lemma lem5372629 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5372630 (_69740 : int) (_69741 : int) : (term274 _69740 _69741) = (term197 _69740 _69741).
Proof. exact (MK_COMB (@lem5372628 _69740 _69741) (@lem5372629)). Qed.
Lemma lem5372631 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : term197 _69740 _69741.
Proof. exact (EQ_MP (@lem5372630 _69740 _69741) (@lem5372625 _69740 _69741 h1)). Qed.
Lemma lem5372633 (y : real) : term277 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5372634 (_69740 : int) (_69741 : int) : term278 _69740 _69741.
Proof. exact (@lem5372633 (term206 _69740 _69741)). Qed.
Lemma lem5372635 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : term279 _69740 _69741.
Proof. exact (@lem5372634 _69740 _69741 (@lem5372556 _69740 _69741 h1)). Qed.
Lemma lem5372636 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : term280 _69740 _69741.
Proof. exact (@lem5372635 _69740 _69741 h1 term125). Qed.
Lemma lem5372637 (_69740 : int) (_69741 : int) : (term280 _69740 _69741) = ((term281 _69740 _69741) = term112).
Proof. exact (eq_refl (term280 _69740 _69741)). Qed.
Lemma lem5372638 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : (term281 _69740 _69741) = term112.
Proof. exact (EQ_MP (@lem5372637 _69740 _69741) (@lem5372636 _69740 _69741 h1)). Qed.
Lemma lem5372639 (_69740 : int) (_69741 : int) : (term281 _69740 _69741) = (term206 _69740 _69741).
Proof. exact (@lem1982733 (term206 _69740 _69741)). Qed.
Lemma lem5372640 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5372641 (_69740 : int) (_69741 : int) : (term282 _69740 _69741) = (term208 _69740 _69741).
Proof. exact (MK_COMB (@lem5372640) (@lem5372639 _69740 _69741)). Qed.
Lemma lem5372642 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5372643 (_69740 : int) (_69741 : int) : ((term281 _69740 _69741) = term112) = ((term206 _69740 _69741) = term112).
Proof. exact (MK_COMB (@lem5372641 _69740 _69741) (@lem5372642)). Qed.
Lemma lem5372644 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : (term206 _69740 _69741) = term112.
Proof. exact (EQ_MP (@lem5372643 _69740 _69741) (@lem5372638 _69740 _69741 h1)). Qed.
Lemma lem5372645 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : term283 _69740 _69741.
Proof. exact (conj (@lem5372644 _69740 _69741 h1) (@lem5372631 _69740 _69741 h1)). Qed.
Lemma lem5372647 (x : real) (y : real) : term284 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5372648 (_69740 : int) (_69741 : int) : term285 _69740 _69741.
Proof. exact (@lem5372647 (term206 _69740 _69741) (term194 _69740 _69741)). Qed.
Lemma lem5372649 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : term286 _69740 _69741.
Proof. exact (@lem5372648 _69740 _69741 (@lem5372645 _69740 _69741 h1)). Qed.
Lemma lem5372650 (_69740 : int) (_69741 : int) : (term287 _69740 _69741) = (term288 _69740 _69741).
Proof. exact (@lem1982753 (term199 _69740) (real_of_int _69740) (real_of_int _69741) (term193 _69741)). Qed.
Lemma lem5372651 (_69740 : int) : (term289 _69740) = (term290 _69740).
Proof. exact (@lem1982713 term157 (real_of_int _69740)). Qed.
Lemma lem5372653 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5372654 : term125 = term183.
Proof. exact (@lem5372653 term126). Qed.
Lemma lem5372656 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5372657 : term157 = term158.
Proof. exact (@lem5372656 term126). Qed.
Lemma lem5372658 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5372659 : term291 = term292.
Proof. exact (MK_COMB (@lem5372658) (@lem5372657)). Qed.
Lemma lem5372660 : term293 = term294.
Proof. exact (MK_COMB (@lem5372659) (@lem5372654)). Qed.
Lemma lem5372661 : term295.
Proof. exact (@lem1981473 term157 term125 term125 term125 term112 term125). Qed.
Lemma lem5372663 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372664 : term258 = term264.
Proof. exact (@lem5372663 (NUMERAL 0) term126). Qed.
Lemma lem5372665 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372666 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372667 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372666 h1) (fun h1 : term264 = True => @lem5372665)). Qed.
Lemma lem5372668 : term264 = True.
Proof. exact (EQ_MP (@lem5372667) (@lem5372665)). Qed.
Lemma lem5372669 : term258 = True.
Proof. exact (TRANS (@lem5372664) (@lem5372668)). Qed.
Lemma lem5372670 : True = term258.
Proof. exact (SYM (@lem5372669)). Qed.
Lemma lem5372671 : term258.
Proof. exact (EQ_MP (@lem5372670) (@lem0)). Qed.
Lemma lem5372672 : term296.
Proof. exact (@lem5372661 (@lem5372671)). Qed.
Lemma lem5372674 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372675 : term258 = term264.
Proof. exact (@lem5372674 (NUMERAL 0) term126). Qed.
Lemma lem5372676 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372677 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372678 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372677 h1) (fun h1 : term264 = True => @lem5372676)). Qed.
Lemma lem5372679 : term264 = True.
Proof. exact (EQ_MP (@lem5372678) (@lem5372676)). Qed.
Lemma lem5372680 : term258 = True.
Proof. exact (TRANS (@lem5372675) (@lem5372679)). Qed.
Lemma lem5372681 : True = term258.
Proof. exact (SYM (@lem5372680)). Qed.
Lemma lem5372682 : term258.
Proof. exact (EQ_MP (@lem5372681) (@lem0)). Qed.
Lemma lem5372683 : term297.
Proof. exact (@lem5372672 (@lem5372682)). Qed.
Lemma lem5372685 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372686 : term258 = term264.
Proof. exact (@lem5372685 (NUMERAL 0) term126). Qed.
Lemma lem5372687 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372688 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372689 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372688 h1) (fun h1 : term264 = True => @lem5372687)). Qed.
Lemma lem5372690 : term264 = True.
Proof. exact (EQ_MP (@lem5372689) (@lem5372687)). Qed.
Lemma lem5372691 : term258 = True.
Proof. exact (TRANS (@lem5372686) (@lem5372690)). Qed.
Lemma lem5372692 : True = term258.
Proof. exact (SYM (@lem5372691)). Qed.
Lemma lem5372693 : term258.
Proof. exact (EQ_MP (@lem5372692) (@lem0)). Qed.
Lemma lem5372694 : term298.
Proof. exact (@lem5372683 (@lem5372693)). Qed.
Lemma lem5372696 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5372697 : term166 = term167.
Proof. exact (@lem5372696 term126 term126). Qed.
Lemma lem5372698 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372699 : term169 = term126.
Proof. exact (EQ_MP (@lem5372698) (@lem940073)). Qed.
Lemma lem5372700 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372701 : term167 = term125.
Proof. exact (MK_COMB (@lem5372700) (@lem5372699)). Qed.
Lemma lem5372702 : term166 = term125.
Proof. exact (TRANS (@lem5372697) (@lem5372701)). Qed.
Lemma lem5372704 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5372705 : term184 = term189.
Proof. exact (@lem5372704 term126 term126). Qed.
Lemma lem5372706 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372707 : term169 = term126.
Proof. exact (EQ_MP (@lem5372706) (@lem940073)). Qed.
Lemma lem5372708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372709 : term167 = term125.
Proof. exact (MK_COMB (@lem5372708) (@lem5372707)). Qed.
Lemma lem5372710 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5372711 : term189 = term157.
Proof. exact (MK_COMB (@lem5372710) (@lem5372709)). Qed.
Lemma lem5372712 : term184 = term157.
Proof. exact (TRANS (@lem5372705) (@lem5372711)). Qed.
Lemma lem5372713 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5372714 : term299 = term291.
Proof. exact (MK_COMB (@lem5372713) (@lem5372712)). Qed.
Lemma lem5372715 : term300 = term293.
Proof. exact (MK_COMB (@lem5372714) (@lem5372702)). Qed.
Lemma lem5372717 (m : nat) : (term301 m) = term112.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5372718 : term293 = term112.
Proof. exact (@lem5372717 term126). Qed.
Lemma lem5372719 : term300 = term112.
Proof. exact (TRANS (@lem5372715) (@lem5372718)). Qed.
Lemma lem5372720 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5372721 : term302 = term303.
Proof. exact (MK_COMB (@lem5372720) (@lem5372719)). Qed.
Lemma lem5372722 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem5372723 : term304 = term269.
Proof. exact (MK_COMB (@lem5372721) (@lem5372722)). Qed.
Lemma lem5372725 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5372726 : term269 = term112.
Proof. exact (@lem5372725 term126). Qed.
Lemma lem5372727 : term304 = term112.
Proof. exact (TRANS (@lem5372723) (@lem5372726)). Qed.
Lemma lem5372729 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5372730 : term166 = term167.
Proof. exact (@lem5372729 term126 term126). Qed.
Lemma lem5372731 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372732 : term169 = term126.
Proof. exact (EQ_MP (@lem5372731) (@lem940073)). Qed.
Lemma lem5372733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372734 : term167 = term125.
Proof. exact (MK_COMB (@lem5372733) (@lem5372732)). Qed.
Lemma lem5372735 : term166 = term125.
Proof. exact (TRANS (@lem5372730) (@lem5372734)). Qed.
Lemma lem5372736 : term303 = term303.
Proof. exact (eq_refl term303). Qed.
Lemma lem5372737 : term305 = term269.
Proof. exact (MK_COMB (@lem5372736) (@lem5372735)). Qed.
Lemma lem5372739 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5372740 : term269 = term112.
Proof. exact (@lem5372739 term126). Qed.
Lemma lem5372741 : term305 = term112.
Proof. exact (TRANS (@lem5372737) (@lem5372740)). Qed.
Lemma lem5372742 : term112 = term305.
Proof. exact (SYM (@lem5372741)). Qed.
Lemma lem5372743 : term304 = term305.
Proof. exact (TRANS (@lem5372727) (@lem5372742)). Qed.
Lemma lem5372744 : term294 = term154.
Proof. exact (@lem5372694 (@lem5372743)). Qed.
Lemma lem5372745 : term293 = term154.
Proof. exact (TRANS (@lem5372660) (@lem5372744)). Qed.
Lemma lem5372747 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5372748 : term154 = term112.
Proof. exact (@lem5372747 term112). Qed.
Lemma lem5372749 : term293 = term112.
Proof. exact (TRANS (@lem5372745) (@lem5372748)). Qed.
Lemma lem5372750 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5372751 : term306 = term303.
Proof. exact (MK_COMB (@lem5372750) (@lem5372749)). Qed.
Lemma lem5372752 (_69740 : int) : (real_of_int _69740) = (real_of_int _69740).
Proof. exact (eq_refl (real_of_int _69740)). Qed.
Lemma lem5372753 (_69740 : int) : (term290 _69740) = (term307 _69740).
Proof. exact (MK_COMB (@lem5372751) (@lem5372752 _69740)). Qed.
Lemma lem5372754 (_69740 : int) : (term289 _69740) = (term307 _69740).
Proof. exact (TRANS (@lem5372651 _69740) (@lem5372753 _69740)). Qed.
Lemma lem5372755 (_69740 : int) : (term307 _69740) = term112.
Proof. exact (@lem1982719 (real_of_int _69740)). Qed.
Lemma lem5372756 (_69740 : int) : (term289 _69740) = term112.
Proof. exact (TRANS (@lem5372754 _69740) (@lem5372755 _69740)). Qed.
Lemma lem5372757 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5372758 (_69740 : int) : (term308 _69740) = term309.
Proof. exact (MK_COMB (@lem5372757) (@lem5372756 _69740)). Qed.
Lemma lem5372759 (_69741 : int) : (term310 _69741) = (term311 _69741).
Proof. exact (@lem1982763 (real_of_int _69741) (term199 _69741) term157). Qed.
Lemma lem5372760 (_69741 : int) : (term312 _69741) = (term290 _69741).
Proof. exact (@lem1982715 term157 (real_of_int _69741)). Qed.
Lemma lem5372762 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5372763 : term125 = term183.
Proof. exact (@lem5372762 term126). Qed.
Lemma lem5372765 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5372766 : term157 = term158.
Proof. exact (@lem5372765 term126). Qed.
Lemma lem5372767 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5372768 : term291 = term292.
Proof. exact (MK_COMB (@lem5372767) (@lem5372766)). Qed.
Lemma lem5372769 : term293 = term294.
Proof. exact (MK_COMB (@lem5372768) (@lem5372763)). Qed.
Lemma lem5372770 : term295.
Proof. exact (@lem1981473 term157 term125 term125 term125 term112 term125). Qed.
Lemma lem5372772 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372773 : term258 = term264.
Proof. exact (@lem5372772 (NUMERAL 0) term126). Qed.
Lemma lem5372774 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372775 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372776 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372775 h1) (fun h1 : term264 = True => @lem5372774)). Qed.
Lemma lem5372777 : term264 = True.
Proof. exact (EQ_MP (@lem5372776) (@lem5372774)). Qed.
Lemma lem5372778 : term258 = True.
Proof. exact (TRANS (@lem5372773) (@lem5372777)). Qed.
Lemma lem5372779 : True = term258.
Proof. exact (SYM (@lem5372778)). Qed.
Lemma lem5372780 : term258.
Proof. exact (EQ_MP (@lem5372779) (@lem0)). Qed.
Lemma lem5372781 : term296.
Proof. exact (@lem5372770 (@lem5372780)). Qed.
Lemma lem5372783 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372784 : term258 = term264.
Proof. exact (@lem5372783 (NUMERAL 0) term126). Qed.
Lemma lem5372785 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372786 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372787 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372786 h1) (fun h1 : term264 = True => @lem5372785)). Qed.
Lemma lem5372788 : term264 = True.
Proof. exact (EQ_MP (@lem5372787) (@lem5372785)). Qed.
Lemma lem5372789 : term258 = True.
Proof. exact (TRANS (@lem5372784) (@lem5372788)). Qed.
Lemma lem5372790 : True = term258.
Proof. exact (SYM (@lem5372789)). Qed.
Lemma lem5372791 : term258.
Proof. exact (EQ_MP (@lem5372790) (@lem0)). Qed.
Lemma lem5372792 : term297.
Proof. exact (@lem5372781 (@lem5372791)). Qed.
Lemma lem5372794 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372795 : term258 = term264.
Proof. exact (@lem5372794 (NUMERAL 0) term126). Qed.
Lemma lem5372796 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372797 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372798 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372797 h1) (fun h1 : term264 = True => @lem5372796)). Qed.
Lemma lem5372799 : term264 = True.
Proof. exact (EQ_MP (@lem5372798) (@lem5372796)). Qed.
Lemma lem5372800 : term258 = True.
Proof. exact (TRANS (@lem5372795) (@lem5372799)). Qed.
Lemma lem5372801 : True = term258.
Proof. exact (SYM (@lem5372800)). Qed.
Lemma lem5372802 : term258.
Proof. exact (EQ_MP (@lem5372801) (@lem0)). Qed.
Lemma lem5372803 : term298.
Proof. exact (@lem5372792 (@lem5372802)). Qed.
Lemma lem5372805 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5372806 : term166 = term167.
Proof. exact (@lem5372805 term126 term126). Qed.
Lemma lem5372807 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372808 : term169 = term126.
Proof. exact (EQ_MP (@lem5372807) (@lem940073)). Qed.
Lemma lem5372809 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372810 : term167 = term125.
Proof. exact (MK_COMB (@lem5372809) (@lem5372808)). Qed.
Lemma lem5372811 : term166 = term125.
Proof. exact (TRANS (@lem5372806) (@lem5372810)). Qed.
Lemma lem5372813 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5372814 : term184 = term189.
Proof. exact (@lem5372813 term126 term126). Qed.
Lemma lem5372815 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372816 : term169 = term126.
Proof. exact (EQ_MP (@lem5372815) (@lem940073)). Qed.
Lemma lem5372817 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372818 : term167 = term125.
Proof. exact (MK_COMB (@lem5372817) (@lem5372816)). Qed.
Lemma lem5372819 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5372820 : term189 = term157.
Proof. exact (MK_COMB (@lem5372819) (@lem5372818)). Qed.
Lemma lem5372821 : term184 = term157.
Proof. exact (TRANS (@lem5372814) (@lem5372820)). Qed.
Lemma lem5372822 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5372823 : term299 = term291.
Proof. exact (MK_COMB (@lem5372822) (@lem5372821)). Qed.
Lemma lem5372824 : term300 = term293.
Proof. exact (MK_COMB (@lem5372823) (@lem5372811)). Qed.
Lemma lem5372826 (m : nat) : (term301 m) = term112.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5372827 : term293 = term112.
Proof. exact (@lem5372826 term126). Qed.
Lemma lem5372828 : term300 = term112.
Proof. exact (TRANS (@lem5372824) (@lem5372827)). Qed.
Lemma lem5372829 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5372830 : term302 = term303.
Proof. exact (MK_COMB (@lem5372829) (@lem5372828)). Qed.
Lemma lem5372831 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem5372832 : term304 = term269.
Proof. exact (MK_COMB (@lem5372830) (@lem5372831)). Qed.
Lemma lem5372834 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5372835 : term269 = term112.
Proof. exact (@lem5372834 term126). Qed.
Lemma lem5372836 : term304 = term112.
Proof. exact (TRANS (@lem5372832) (@lem5372835)). Qed.
Lemma lem5372838 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5372839 : term166 = term167.
Proof. exact (@lem5372838 term126 term126). Qed.
Lemma lem5372840 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372841 : term169 = term126.
Proof. exact (EQ_MP (@lem5372840) (@lem940073)). Qed.
Lemma lem5372842 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372843 : term167 = term125.
Proof. exact (MK_COMB (@lem5372842) (@lem5372841)). Qed.
Lemma lem5372844 : term166 = term125.
Proof. exact (TRANS (@lem5372839) (@lem5372843)). Qed.
Lemma lem5372845 : term303 = term303.
Proof. exact (eq_refl term303). Qed.
Lemma lem5372846 : term305 = term269.
Proof. exact (MK_COMB (@lem5372845) (@lem5372844)). Qed.
Lemma lem5372848 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5372849 : term269 = term112.
Proof. exact (@lem5372848 term126). Qed.
Lemma lem5372850 : term305 = term112.
Proof. exact (TRANS (@lem5372846) (@lem5372849)). Qed.
Lemma lem5372851 : term112 = term305.
Proof. exact (SYM (@lem5372850)). Qed.
Lemma lem5372852 : term304 = term305.
Proof. exact (TRANS (@lem5372836) (@lem5372851)). Qed.
Lemma lem5372853 : term294 = term154.
Proof. exact (@lem5372803 (@lem5372852)). Qed.
Lemma lem5372854 : term293 = term154.
Proof. exact (TRANS (@lem5372769) (@lem5372853)). Qed.
Lemma lem5372856 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5372857 : term154 = term112.
Proof. exact (@lem5372856 term112). Qed.
Lemma lem5372858 : term293 = term112.
Proof. exact (TRANS (@lem5372854) (@lem5372857)). Qed.
Lemma lem5372859 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5372860 : term306 = term303.
Proof. exact (MK_COMB (@lem5372859) (@lem5372858)). Qed.
Lemma lem5372861 (_69741 : int) : (real_of_int _69741) = (real_of_int _69741).
Proof. exact (eq_refl (real_of_int _69741)). Qed.
Lemma lem5372862 (_69741 : int) : (term290 _69741) = (term307 _69741).
Proof. exact (MK_COMB (@lem5372860) (@lem5372861 _69741)). Qed.
Lemma lem5372863 (_69741 : int) : (term312 _69741) = (term307 _69741).
Proof. exact (TRANS (@lem5372760 _69741) (@lem5372862 _69741)). Qed.
Lemma lem5372864 (_69741 : int) : (term307 _69741) = term112.
Proof. exact (@lem1982719 (real_of_int _69741)). Qed.
Lemma lem5372865 (_69741 : int) : (term312 _69741) = term112.
Proof. exact (TRANS (@lem5372863 _69741) (@lem5372864 _69741)). Qed.
Lemma lem5372866 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5372867 (_69741 : int) : (term313 _69741) = term309.
Proof. exact (MK_COMB (@lem5372866) (@lem5372865 _69741)). Qed.
Lemma lem5372868 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem5372869 (_69741 : int) : (term311 _69741) = term314.
Proof. exact (MK_COMB (@lem5372867 _69741) (@lem5372868)). Qed.
Lemma lem5372870 (_69741 : int) : (term310 _69741) = term314.
Proof. exact (TRANS (@lem5372759 _69741) (@lem5372869 _69741)). Qed.
Lemma lem5372871 : term314 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem5372872 (_69741 : int) : (term310 _69741) = term157.
Proof. exact (TRANS (@lem5372870 _69741) (@lem5372871)). Qed.
Lemma lem5372873 (_69740 : int) (_69741 : int) : (term288 _69740 _69741) = term314.
Proof. exact (MK_COMB (@lem5372758 _69740) (@lem5372872 _69741)). Qed.
Lemma lem5372874 (_69740 : int) (_69741 : int) : (term287 _69740 _69741) = term314.
Proof. exact (TRANS (@lem5372650 _69740 _69741) (@lem5372873 _69740 _69741)). Qed.
Lemma lem5372875 : term314 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem5372876 (_69740 : int) (_69741 : int) : (term287 _69740 _69741) = term157.
Proof. exact (TRANS (@lem5372874 _69740 _69741) (@lem5372875)). Qed.
Lemma lem5372877 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5372878 (_69740 : int) (_69741 : int) : (term315 _69740 _69741) = term316.
Proof. exact (MK_COMB (@lem5372877) (@lem5372876 _69740 _69741)). Qed.
Lemma lem5372879 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5372880 (_69740 : int) (_69741 : int) : (term286 _69740 _69741) = term317.
Proof. exact (MK_COMB (@lem5372878 _69740 _69741) (@lem5372879)). Qed.
Lemma lem5372881 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : term317.
Proof. exact (EQ_MP (@lem5372880 _69740 _69741) (@lem5372649 _69740 _69741 h1)). Qed.
Lemma lem5372883 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5372884 : term317 = term318.
Proof. exact (@lem5372883 term112 term157). Qed.
Lemma lem5372886 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5372887 : term157 = term158.
Proof. exact (@lem5372886 term126). Qed.
Lemma lem5372889 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5372890 : term112 = term154.
Proof. exact (@lem5372889 (NUMERAL 0)). Qed.
Lemma lem5372891 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5372892 : term114 = term319.
Proof. exact (MK_COMB (@lem5372891) (@lem5372890)). Qed.
Lemma lem5372893 : term318 = term320.
Proof. exact (MK_COMB (@lem5372892) (@lem5372887)). Qed.
Lemma lem5372894 : term321.
Proof. exact (@lem1980026 term112 term125 term157 term125). Qed.
Lemma lem5372896 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372897 : term258 = term264.
Proof. exact (@lem5372896 (NUMERAL 0) term126). Qed.
Lemma lem5372898 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372899 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372900 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372899 h1) (fun h1 : term264 = True => @lem5372898)). Qed.
Lemma lem5372901 : term264 = True.
Proof. exact (EQ_MP (@lem5372900) (@lem5372898)). Qed.
Lemma lem5372902 : term258 = True.
Proof. exact (TRANS (@lem5372897) (@lem5372901)). Qed.
Lemma lem5372903 : True = term258.
Proof. exact (SYM (@lem5372902)). Qed.
Lemma lem5372904 : term258.
Proof. exact (EQ_MP (@lem5372903) (@lem0)). Qed.
Lemma lem5372905 : term322.
Proof. exact (@lem5372894 (@lem5372904)). Qed.
Lemma lem5372907 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372908 : term258 = term264.
Proof. exact (@lem5372907 (NUMERAL 0) term126). Qed.
Lemma lem5372909 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372910 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372911 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372910 h1) (fun h1 : term264 = True => @lem5372909)). Qed.
Lemma lem5372912 : term264 = True.
Proof. exact (EQ_MP (@lem5372911) (@lem5372909)). Qed.
Lemma lem5372913 : term258 = True.
Proof. exact (TRANS (@lem5372908) (@lem5372912)). Qed.
Lemma lem5372914 : True = term258.
Proof. exact (SYM (@lem5372913)). Qed.
Lemma lem5372915 : term258.
Proof. exact (EQ_MP (@lem5372914) (@lem0)). Qed.
Lemma lem5372916 : term320 = term323.
Proof. exact (@lem5372905 (@lem5372915)). Qed.
Lemma lem5372918 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5372919 : term184 = term189.
Proof. exact (@lem5372918 term126 term126). Qed.
Lemma lem5372920 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372921 : term169 = term126.
Proof. exact (EQ_MP (@lem5372920) (@lem940073)). Qed.
Lemma lem5372922 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5372923 : term167 = term125.
Proof. exact (MK_COMB (@lem5372922) (@lem5372921)). Qed.
Lemma lem5372924 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5372925 : term189 = term157.
Proof. exact (MK_COMB (@lem5372924) (@lem5372923)). Qed.
Lemma lem5372926 : term184 = term157.
Proof. exact (TRANS (@lem5372919) (@lem5372925)). Qed.
Lemma lem5372928 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5372929 : term269 = term112.
Proof. exact (@lem5372928 term126). Qed.
Lemma lem5372930 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5372931 : term324 = term114.
Proof. exact (MK_COMB (@lem5372930) (@lem5372929)). Qed.
Lemma lem5372932 : term323 = term318.
Proof. exact (MK_COMB (@lem5372931) (@lem5372926)). Qed.
Lemma lem5372934 (m : nat) (n : nat) : (term325 m n) = (term326 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5372935 : term318 = term327.
Proof. exact (@lem5372934 (NUMERAL 0) term126). Qed.
Lemma lem5372936 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372937 (h1 : term265 = (BIT1 0)) : (term126 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5372938 : (term265 = (BIT1 0)) = ((term126 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372937 h1) (fun h1 : (term126 = (NUMERAL 0)) = False => @lem5372936)). Qed.
Lemma lem5372939 : (term126 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5372938) (@lem5372936)). Qed.
Lemma lem5372940 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5372941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5372942 : term328 = (and True).
Proof. exact (MK_COMB (@lem5372941) (@lem5372940)). Qed.
Lemma lem5372943 : term327 = (True /\ False).
Proof. exact (MK_COMB (@lem5372942) (@lem5372939)). Qed.
Lemma lem5372945 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5372946 : term327 = False.
Proof. exact (TRANS (@lem5372943) (@lem5372945)). Qed.
Lemma lem5372947 : term318 = False.
Proof. exact (TRANS (@lem5372935) (@lem5372946)). Qed.
Lemma lem5372948 : term323 = False.
Proof. exact (TRANS (@lem5372932) (@lem5372947)). Qed.
Lemma lem5372949 : term320 = False.
Proof. exact (TRANS (@lem5372916) (@lem5372948)). Qed.
Lemma lem5372950 : term318 = False.
Proof. exact (TRANS (@lem5372893) (@lem5372949)). Qed.
Lemma lem5372951 : term317 = False.
Proof. exact (TRANS (@lem5372884) (@lem5372950)). Qed.
Lemma lem5372952 (_69740 : int) (_69741 : int) (h1 : term256 _69740 _69741) : False.
Proof. exact (EQ_MP (@lem5372951) (@lem5372881 _69740 _69741 h1)). Qed.
Lemma lem5372953 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : term329 _69740 _69741.
Proof. exact (h1). Qed.
Lemma lem5372954 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : term252 _69740 _69741.
Proof. exact (proj2 (@lem5372953 _69740 _69741 h1)). Qed.
Lemma lem5372956 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : term239 _69740 _69741.
Proof. exact (proj2 (@lem5372954 _69740 _69741 h1)). Qed.
Lemma lem5372958 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : (term206 _69740 _69741) = term112.
Proof. exact (proj2 (@lem5372956 _69740 _69741 h1)). Qed.
Lemma lem5372959 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : term201 _69740 _69741.
Proof. exact (proj1 (@lem5372956 _69740 _69741 h1)). Qed.
Lemma lem5372961 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5372962 : term257 = term258.
Proof. exact (@lem5372961 term112 term125). Qed.
Lemma lem5372964 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5372965 : term125 = term183.
Proof. exact (@lem5372964 term126). Qed.
Lemma lem5372967 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5372968 : term112 = term154.
Proof. exact (@lem5372967 (NUMERAL 0)). Qed.
Lemma lem5372969 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5372970 : term259 = term260.
Proof. exact (MK_COMB (@lem5372969) (@lem5372968)). Qed.
Lemma lem5372971 : term258 = term261.
Proof. exact (MK_COMB (@lem5372970) (@lem5372965)). Qed.
Lemma lem5372972 : term262.
Proof. exact (@lem1980255 term112 term125 term125 term125). Qed.
Lemma lem5372974 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372975 : term258 = term264.
Proof. exact (@lem5372974 (NUMERAL 0) term126). Qed.
Lemma lem5372976 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372977 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372978 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372977 h1) (fun h1 : term264 = True => @lem5372976)). Qed.
Lemma lem5372979 : term264 = True.
Proof. exact (EQ_MP (@lem5372978) (@lem5372976)). Qed.
Lemma lem5372980 : term258 = True.
Proof. exact (TRANS (@lem5372975) (@lem5372979)). Qed.
Lemma lem5372981 : True = term258.
Proof. exact (SYM (@lem5372980)). Qed.
Lemma lem5372982 : term258.
Proof. exact (EQ_MP (@lem5372981) (@lem0)). Qed.
Lemma lem5372983 : term266.
Proof. exact (@lem5372972 (@lem5372982)). Qed.
Lemma lem5372985 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5372986 : term258 = term264.
Proof. exact (@lem5372985 (NUMERAL 0) term126). Qed.
Lemma lem5372987 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5372988 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5372989 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5372988 h1) (fun h1 : term264 = True => @lem5372987)). Qed.
Lemma lem5372990 : term264 = True.
Proof. exact (EQ_MP (@lem5372989) (@lem5372987)). Qed.
Lemma lem5372991 : term258 = True.
Proof. exact (TRANS (@lem5372986) (@lem5372990)). Qed.
Lemma lem5372992 : True = term258.
Proof. exact (SYM (@lem5372991)). Qed.
Lemma lem5372993 : term258.
Proof. exact (EQ_MP (@lem5372992) (@lem0)). Qed.
Lemma lem5372994 : term261 = term267.
Proof. exact (@lem5372983 (@lem5372993)). Qed.
Lemma lem5372996 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5372997 : term166 = term167.
Proof. exact (@lem5372996 term126 term126). Qed.
Lemma lem5372998 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5372999 : term169 = term126.
Proof. exact (EQ_MP (@lem5372998) (@lem940073)). Qed.
Lemma lem5373000 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373001 : term167 = term125.
Proof. exact (MK_COMB (@lem5373000) (@lem5372999)). Qed.
Lemma lem5373002 : term166 = term125.
Proof. exact (TRANS (@lem5372997) (@lem5373001)). Qed.
Lemma lem5373004 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373005 : term269 = term112.
Proof. exact (@lem5373004 term126). Qed.
Lemma lem5373006 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5373007 : term270 = term259.
Proof. exact (MK_COMB (@lem5373006) (@lem5373005)). Qed.
Lemma lem5373008 : term267 = term258.
Proof. exact (MK_COMB (@lem5373007) (@lem5373002)). Qed.
Lemma lem5373010 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373011 : term258 = term264.
Proof. exact (@lem5373010 (NUMERAL 0) term126). Qed.
Lemma lem5373012 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373013 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373014 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373013 h1) (fun h1 : term264 = True => @lem5373012)). Qed.
Lemma lem5373015 : term264 = True.
Proof. exact (EQ_MP (@lem5373014) (@lem5373012)). Qed.
Lemma lem5373016 : term258 = True.
Proof. exact (TRANS (@lem5373011) (@lem5373015)). Qed.
Lemma lem5373017 : term267 = True.
Proof. exact (TRANS (@lem5373008) (@lem5373016)). Qed.
Lemma lem5373018 : term261 = True.
Proof. exact (TRANS (@lem5372994) (@lem5373017)). Qed.
Lemma lem5373019 : term258 = True.
Proof. exact (TRANS (@lem5372971) (@lem5373018)). Qed.
Lemma lem5373020 : term257 = True.
Proof. exact (TRANS (@lem5372962) (@lem5373019)). Qed.
Lemma lem5373021 : True = term257.
Proof. exact (SYM (@lem5373020)). Qed.
Lemma lem5373022 : term257.
Proof. exact (EQ_MP (@lem5373021) (@lem0)). Qed.
Lemma lem5373023 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : term330 _69740 _69741.
Proof. exact (conj (@lem5373022) (@lem5372959 _69740 _69741 h1)). Qed.
Lemma lem5373025 (x : real) (y : real) : term272 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5373026 (_69740 : int) (_69741 : int) : term331 _69740 _69741.
Proof. exact (@lem5373025 term125 (term198 _69740 _69741)). Qed.
Lemma lem5373027 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : term332 _69740 _69741.
Proof. exact (@lem5373026 _69740 _69741 (@lem5373023 _69740 _69741 h1)). Qed.
Lemma lem5373028 (_69740 : int) (_69741 : int) : (term333 _69740 _69741) = (term198 _69740 _69741).
Proof. exact (@lem1982733 (term198 _69740 _69741)). Qed.
Lemma lem5373029 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5373030 (_69740 : int) (_69741 : int) : (term334 _69740 _69741) = (term200 _69740 _69741).
Proof. exact (MK_COMB (@lem5373029) (@lem5373028 _69740 _69741)). Qed.
Lemma lem5373031 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5373032 (_69740 : int) (_69741 : int) : (term332 _69740 _69741) = (term201 _69740 _69741).
Proof. exact (MK_COMB (@lem5373030 _69740 _69741) (@lem5373031)). Qed.
Lemma lem5373033 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : term201 _69740 _69741.
Proof. exact (EQ_MP (@lem5373032 _69740 _69741) (@lem5373027 _69740 _69741 h1)). Qed.
Lemma lem5373035 (y : real) : term277 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5373036 (_69740 : int) (_69741 : int) : term278 _69740 _69741.
Proof. exact (@lem5373035 (term206 _69740 _69741)). Qed.
Lemma lem5373037 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : term279 _69740 _69741.
Proof. exact (@lem5373036 _69740 _69741 (@lem5372958 _69740 _69741 h1)). Qed.
Lemma lem5373038 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : term335 _69740 _69741.
Proof. exact (@lem5373037 _69740 _69741 h1 term157). Qed.
Lemma lem5373039 (_69740 : int) (_69741 : int) : (term335 _69740 _69741) = ((term336 _69740 _69741) = term112).
Proof. exact (eq_refl (term335 _69740 _69741)). Qed.
Lemma lem5373040 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : (term336 _69740 _69741) = term112.
Proof. exact (EQ_MP (@lem5373039 _69740 _69741) (@lem5373038 _69740 _69741 h1)). Qed.
Lemma lem5373041 (_69740 : int) (_69741 : int) : (term336 _69740 _69741) = (term337 _69740 _69741).
Proof. exact (@lem1982781 (term199 _69740) term157 (real_of_int _69741)). Qed.
Lemma lem5373042 (_69741 : int) : (term199 _69741) = (term199 _69741).
Proof. exact (eq_refl (term199 _69741)). Qed.
Lemma lem5373043 (_69740 : int) : (term338 _69740) = (term339 _69740).
Proof. exact (@lem1982749 term157 term157 (real_of_int _69740)). Qed.
Lemma lem5373045 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5373046 : term157 = term158.
Proof. exact (@lem5373045 term126). Qed.
Lemma lem5373048 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5373049 : term157 = term158.
Proof. exact (@lem5373048 term126). Qed.
Lemma lem5373050 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5373051 : term159 = term160.
Proof. exact (MK_COMB (@lem5373050) (@lem5373049)). Qed.
Lemma lem5373052 : term340 = term341.
Proof. exact (MK_COMB (@lem5373051) (@lem5373046)). Qed.
Lemma lem5373053 : term341 = term342.
Proof. exact (@lem1981613 term157 term157 term125 term125). Qed.
Lemma lem5373055 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373056 : term166 = term167.
Proof. exact (@lem5373055 term126 term126). Qed.
Lemma lem5373057 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373058 : term169 = term126.
Proof. exact (EQ_MP (@lem5373057) (@lem940073)). Qed.
Lemma lem5373059 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373060 : term167 = term125.
Proof. exact (MK_COMB (@lem5373059) (@lem5373058)). Qed.
Lemma lem5373061 : term166 = term125.
Proof. exact (TRANS (@lem5373056) (@lem5373060)). Qed.
Lemma lem5373063 (m : nat) (n : nat) : (term343 m n) = (term165 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5373064 : term340 = term167.
Proof. exact (@lem5373063 term126 term126). Qed.
Lemma lem5373065 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373066 : term169 = term126.
Proof. exact (EQ_MP (@lem5373065) (@lem940073)). Qed.
Lemma lem5373067 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373068 : term167 = term125.
Proof. exact (MK_COMB (@lem5373067) (@lem5373066)). Qed.
Lemma lem5373069 : term340 = term125.
Proof. exact (TRANS (@lem5373064) (@lem5373068)). Qed.
Lemma lem5373070 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5373071 : term344 = term345.
Proof. exact (MK_COMB (@lem5373070) (@lem5373069)). Qed.
Lemma lem5373072 : term342 = term183.
Proof. exact (MK_COMB (@lem5373071) (@lem5373061)). Qed.
Lemma lem5373073 : term341 = term183.
Proof. exact (TRANS (@lem5373053) (@lem5373072)). Qed.
Lemma lem5373074 : term340 = term183.
Proof. exact (TRANS (@lem5373052) (@lem5373073)). Qed.
Lemma lem5373076 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5373077 : term183 = term125.
Proof. exact (@lem5373076 term125). Qed.
Lemma lem5373078 : term340 = term125.
Proof. exact (TRANS (@lem5373074) (@lem5373077)). Qed.
Lemma lem5373079 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5373080 : term346 = term347.
Proof. exact (MK_COMB (@lem5373079) (@lem5373078)). Qed.
Lemma lem5373081 (_69740 : int) : (real_of_int _69740) = (real_of_int _69740).
Proof. exact (eq_refl (real_of_int _69740)). Qed.
Lemma lem5373082 (_69740 : int) : (term339 _69740) = (term348 _69740).
Proof. exact (MK_COMB (@lem5373080) (@lem5373081 _69740)). Qed.
Lemma lem5373083 (_69740 : int) : (term338 _69740) = (term348 _69740).
Proof. exact (TRANS (@lem5373043 _69740) (@lem5373082 _69740)). Qed.
Lemma lem5373084 (_69740 : int) : (term348 _69740) = (real_of_int _69740).
Proof. exact (@lem1982709 (real_of_int _69740)). Qed.
Lemma lem5373085 (_69740 : int) : (term338 _69740) = (real_of_int _69740).
Proof. exact (TRANS (@lem5373083 _69740) (@lem5373084 _69740)). Qed.
Lemma lem5373086 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373087 (_69740 : int) : (term349 _69740) = (term127 _69740).
Proof. exact (MK_COMB (@lem5373086) (@lem5373085 _69740)). Qed.
Lemma lem5373088 (_69740 : int) (_69741 : int) : (term337 _69740 _69741) = (term205 _69740 _69741).
Proof. exact (MK_COMB (@lem5373087 _69740) (@lem5373042 _69741)). Qed.
Lemma lem5373089 (_69740 : int) (_69741 : int) : (term336 _69740 _69741) = (term205 _69740 _69741).
Proof. exact (TRANS (@lem5373041 _69740 _69741) (@lem5373088 _69740 _69741)). Qed.
Lemma lem5373090 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5373091 (_69740 : int) (_69741 : int) : (term350 _69740 _69741) = (term351 _69740 _69741).
Proof. exact (MK_COMB (@lem5373090) (@lem5373089 _69740 _69741)). Qed.
Lemma lem5373092 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5373093 (_69740 : int) (_69741 : int) : ((term336 _69740 _69741) = term112) = ((term205 _69740 _69741) = term112).
Proof. exact (MK_COMB (@lem5373091 _69740 _69741) (@lem5373092)). Qed.
Lemma lem5373094 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : (term205 _69740 _69741) = term112.
Proof. exact (EQ_MP (@lem5373093 _69740 _69741) (@lem5373040 _69740 _69741 h1)). Qed.
Lemma lem5373095 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : term352 _69740 _69741.
Proof. exact (conj (@lem5373094 _69740 _69741 h1) (@lem5373033 _69740 _69741 h1)). Qed.
Lemma lem5373097 (x : real) (y : real) : term284 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5373098 (_69740 : int) (_69741 : int) : term353 _69740 _69741.
Proof. exact (@lem5373097 (term205 _69740 _69741) (term198 _69740 _69741)). Qed.
Lemma lem5373099 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : term354 _69740 _69741.
Proof. exact (@lem5373098 _69740 _69741 (@lem5373095 _69740 _69741 h1)). Qed.
Lemma lem5373100 (_69740 : int) (_69741 : int) : (term355 _69740 _69741) = (term356 _69740 _69741).
Proof. exact (@lem1982753 (real_of_int _69740) (term199 _69740) (term199 _69741) (term357 _69741)). Qed.
Lemma lem5373101 (_69740 : int) : (term312 _69740) = (term290 _69740).
Proof. exact (@lem1982715 term157 (real_of_int _69740)). Qed.
Lemma lem5373103 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373104 : term125 = term183.
Proof. exact (@lem5373103 term126). Qed.
Lemma lem5373106 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5373107 : term157 = term158.
Proof. exact (@lem5373106 term126). Qed.
Lemma lem5373108 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373109 : term291 = term292.
Proof. exact (MK_COMB (@lem5373108) (@lem5373107)). Qed.
Lemma lem5373110 : term293 = term294.
Proof. exact (MK_COMB (@lem5373109) (@lem5373104)). Qed.
Lemma lem5373111 : term295.
Proof. exact (@lem1981473 term157 term125 term125 term125 term112 term125). Qed.
Lemma lem5373113 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373114 : term258 = term264.
Proof. exact (@lem5373113 (NUMERAL 0) term126). Qed.
Lemma lem5373115 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373116 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373117 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373116 h1) (fun h1 : term264 = True => @lem5373115)). Qed.
Lemma lem5373118 : term264 = True.
Proof. exact (EQ_MP (@lem5373117) (@lem5373115)). Qed.
Lemma lem5373119 : term258 = True.
Proof. exact (TRANS (@lem5373114) (@lem5373118)). Qed.
Lemma lem5373120 : True = term258.
Proof. exact (SYM (@lem5373119)). Qed.
Lemma lem5373121 : term258.
Proof. exact (EQ_MP (@lem5373120) (@lem0)). Qed.
Lemma lem5373122 : term296.
Proof. exact (@lem5373111 (@lem5373121)). Qed.
Lemma lem5373124 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373125 : term258 = term264.
Proof. exact (@lem5373124 (NUMERAL 0) term126). Qed.
Lemma lem5373126 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373127 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373128 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373127 h1) (fun h1 : term264 = True => @lem5373126)). Qed.
Lemma lem5373129 : term264 = True.
Proof. exact (EQ_MP (@lem5373128) (@lem5373126)). Qed.
Lemma lem5373130 : term258 = True.
Proof. exact (TRANS (@lem5373125) (@lem5373129)). Qed.
Lemma lem5373131 : True = term258.
Proof. exact (SYM (@lem5373130)). Qed.
Lemma lem5373132 : term258.
Proof. exact (EQ_MP (@lem5373131) (@lem0)). Qed.
Lemma lem5373133 : term297.
Proof. exact (@lem5373122 (@lem5373132)). Qed.
Lemma lem5373135 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373136 : term258 = term264.
Proof. exact (@lem5373135 (NUMERAL 0) term126). Qed.
Lemma lem5373137 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373138 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373139 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373138 h1) (fun h1 : term264 = True => @lem5373137)). Qed.
Lemma lem5373140 : term264 = True.
Proof. exact (EQ_MP (@lem5373139) (@lem5373137)). Qed.
Lemma lem5373141 : term258 = True.
Proof. exact (TRANS (@lem5373136) (@lem5373140)). Qed.
Lemma lem5373142 : True = term258.
Proof. exact (SYM (@lem5373141)). Qed.
Lemma lem5373143 : term258.
Proof. exact (EQ_MP (@lem5373142) (@lem0)). Qed.
Lemma lem5373144 : term298.
Proof. exact (@lem5373133 (@lem5373143)). Qed.
Lemma lem5373146 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373147 : term166 = term167.
Proof. exact (@lem5373146 term126 term126). Qed.
Lemma lem5373148 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373149 : term169 = term126.
Proof. exact (EQ_MP (@lem5373148) (@lem940073)). Qed.
Lemma lem5373150 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373151 : term167 = term125.
Proof. exact (MK_COMB (@lem5373150) (@lem5373149)). Qed.
Lemma lem5373152 : term166 = term125.
Proof. exact (TRANS (@lem5373147) (@lem5373151)). Qed.
Lemma lem5373154 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5373155 : term184 = term189.
Proof. exact (@lem5373154 term126 term126). Qed.
Lemma lem5373156 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373157 : term169 = term126.
Proof. exact (EQ_MP (@lem5373156) (@lem940073)). Qed.
Lemma lem5373158 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373159 : term167 = term125.
Proof. exact (MK_COMB (@lem5373158) (@lem5373157)). Qed.
Lemma lem5373160 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5373161 : term189 = term157.
Proof. exact (MK_COMB (@lem5373160) (@lem5373159)). Qed.
Lemma lem5373162 : term184 = term157.
Proof. exact (TRANS (@lem5373155) (@lem5373161)). Qed.
Lemma lem5373163 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373164 : term299 = term291.
Proof. exact (MK_COMB (@lem5373163) (@lem5373162)). Qed.
Lemma lem5373165 : term300 = term293.
Proof. exact (MK_COMB (@lem5373164) (@lem5373152)). Qed.
Lemma lem5373167 (m : nat) : (term301 m) = term112.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5373168 : term293 = term112.
Proof. exact (@lem5373167 term126). Qed.
Lemma lem5373169 : term300 = term112.
Proof. exact (TRANS (@lem5373165) (@lem5373168)). Qed.
Lemma lem5373170 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5373171 : term302 = term303.
Proof. exact (MK_COMB (@lem5373170) (@lem5373169)). Qed.
Lemma lem5373172 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem5373173 : term304 = term269.
Proof. exact (MK_COMB (@lem5373171) (@lem5373172)). Qed.
Lemma lem5373175 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373176 : term269 = term112.
Proof. exact (@lem5373175 term126). Qed.
Lemma lem5373177 : term304 = term112.
Proof. exact (TRANS (@lem5373173) (@lem5373176)). Qed.
Lemma lem5373179 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373180 : term166 = term167.
Proof. exact (@lem5373179 term126 term126). Qed.
Lemma lem5373181 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373182 : term169 = term126.
Proof. exact (EQ_MP (@lem5373181) (@lem940073)). Qed.
Lemma lem5373183 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373184 : term167 = term125.
Proof. exact (MK_COMB (@lem5373183) (@lem5373182)). Qed.
Lemma lem5373185 : term166 = term125.
Proof. exact (TRANS (@lem5373180) (@lem5373184)). Qed.
Lemma lem5373186 : term303 = term303.
Proof. exact (eq_refl term303). Qed.
Lemma lem5373187 : term305 = term269.
Proof. exact (MK_COMB (@lem5373186) (@lem5373185)). Qed.
Lemma lem5373189 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373190 : term269 = term112.
Proof. exact (@lem5373189 term126). Qed.
Lemma lem5373191 : term305 = term112.
Proof. exact (TRANS (@lem5373187) (@lem5373190)). Qed.
Lemma lem5373192 : term112 = term305.
Proof. exact (SYM (@lem5373191)). Qed.
Lemma lem5373193 : term304 = term305.
Proof. exact (TRANS (@lem5373177) (@lem5373192)). Qed.
Lemma lem5373194 : term294 = term154.
Proof. exact (@lem5373144 (@lem5373193)). Qed.
Lemma lem5373195 : term293 = term154.
Proof. exact (TRANS (@lem5373110) (@lem5373194)). Qed.
Lemma lem5373197 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5373198 : term154 = term112.
Proof. exact (@lem5373197 term112). Qed.
Lemma lem5373199 : term293 = term112.
Proof. exact (TRANS (@lem5373195) (@lem5373198)). Qed.
Lemma lem5373200 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5373201 : term306 = term303.
Proof. exact (MK_COMB (@lem5373200) (@lem5373199)). Qed.
Lemma lem5373202 (_69740 : int) : (real_of_int _69740) = (real_of_int _69740).
Proof. exact (eq_refl (real_of_int _69740)). Qed.
Lemma lem5373203 (_69740 : int) : (term290 _69740) = (term307 _69740).
Proof. exact (MK_COMB (@lem5373201) (@lem5373202 _69740)). Qed.
Lemma lem5373204 (_69740 : int) : (term312 _69740) = (term307 _69740).
Proof. exact (TRANS (@lem5373101 _69740) (@lem5373203 _69740)). Qed.
Lemma lem5373205 (_69740 : int) : (term307 _69740) = term112.
Proof. exact (@lem1982719 (real_of_int _69740)). Qed.
Lemma lem5373206 (_69740 : int) : (term312 _69740) = term112.
Proof. exact (TRANS (@lem5373204 _69740) (@lem5373205 _69740)). Qed.
Lemma lem5373207 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373208 (_69740 : int) : (term313 _69740) = term309.
Proof. exact (MK_COMB (@lem5373207) (@lem5373206 _69740)). Qed.
Lemma lem5373209 (_69741 : int) : (term358 _69741) = (term359 _69741).
Proof. exact (@lem1982763 (term199 _69741) (real_of_int _69741) term157). Qed.
Lemma lem5373210 (_69741 : int) : (term289 _69741) = (term290 _69741).
Proof. exact (@lem1982713 term157 (real_of_int _69741)). Qed.
Lemma lem5373212 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373213 : term125 = term183.
Proof. exact (@lem5373212 term126). Qed.
Lemma lem5373215 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5373216 : term157 = term158.
Proof. exact (@lem5373215 term126). Qed.
Lemma lem5373217 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373218 : term291 = term292.
Proof. exact (MK_COMB (@lem5373217) (@lem5373216)). Qed.
Lemma lem5373219 : term293 = term294.
Proof. exact (MK_COMB (@lem5373218) (@lem5373213)). Qed.
Lemma lem5373220 : term295.
Proof. exact (@lem1981473 term157 term125 term125 term125 term112 term125). Qed.
Lemma lem5373222 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373223 : term258 = term264.
Proof. exact (@lem5373222 (NUMERAL 0) term126). Qed.
Lemma lem5373224 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373225 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373226 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373225 h1) (fun h1 : term264 = True => @lem5373224)). Qed.
Lemma lem5373227 : term264 = True.
Proof. exact (EQ_MP (@lem5373226) (@lem5373224)). Qed.
Lemma lem5373228 : term258 = True.
Proof. exact (TRANS (@lem5373223) (@lem5373227)). Qed.
Lemma lem5373229 : True = term258.
Proof. exact (SYM (@lem5373228)). Qed.
Lemma lem5373230 : term258.
Proof. exact (EQ_MP (@lem5373229) (@lem0)). Qed.
Lemma lem5373231 : term296.
Proof. exact (@lem5373220 (@lem5373230)). Qed.
Lemma lem5373233 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373234 : term258 = term264.
Proof. exact (@lem5373233 (NUMERAL 0) term126). Qed.
Lemma lem5373235 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373236 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373237 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373236 h1) (fun h1 : term264 = True => @lem5373235)). Qed.
Lemma lem5373238 : term264 = True.
Proof. exact (EQ_MP (@lem5373237) (@lem5373235)). Qed.
Lemma lem5373239 : term258 = True.
Proof. exact (TRANS (@lem5373234) (@lem5373238)). Qed.
Lemma lem5373240 : True = term258.
Proof. exact (SYM (@lem5373239)). Qed.
Lemma lem5373241 : term258.
Proof. exact (EQ_MP (@lem5373240) (@lem0)). Qed.
Lemma lem5373242 : term297.
Proof. exact (@lem5373231 (@lem5373241)). Qed.
Lemma lem5373244 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373245 : term258 = term264.
Proof. exact (@lem5373244 (NUMERAL 0) term126). Qed.
Lemma lem5373246 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373247 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373248 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373247 h1) (fun h1 : term264 = True => @lem5373246)). Qed.
Lemma lem5373249 : term264 = True.
Proof. exact (EQ_MP (@lem5373248) (@lem5373246)). Qed.
Lemma lem5373250 : term258 = True.
Proof. exact (TRANS (@lem5373245) (@lem5373249)). Qed.
Lemma lem5373251 : True = term258.
Proof. exact (SYM (@lem5373250)). Qed.
Lemma lem5373252 : term258.
Proof. exact (EQ_MP (@lem5373251) (@lem0)). Qed.
Lemma lem5373253 : term298.
Proof. exact (@lem5373242 (@lem5373252)). Qed.
Lemma lem5373255 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373256 : term166 = term167.
Proof. exact (@lem5373255 term126 term126). Qed.
Lemma lem5373257 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373258 : term169 = term126.
Proof. exact (EQ_MP (@lem5373257) (@lem940073)). Qed.
Lemma lem5373259 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373260 : term167 = term125.
Proof. exact (MK_COMB (@lem5373259) (@lem5373258)). Qed.
Lemma lem5373261 : term166 = term125.
Proof. exact (TRANS (@lem5373256) (@lem5373260)). Qed.
Lemma lem5373263 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5373264 : term184 = term189.
Proof. exact (@lem5373263 term126 term126). Qed.
Lemma lem5373265 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373266 : term169 = term126.
Proof. exact (EQ_MP (@lem5373265) (@lem940073)). Qed.
Lemma lem5373267 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373268 : term167 = term125.
Proof. exact (MK_COMB (@lem5373267) (@lem5373266)). Qed.
Lemma lem5373269 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5373270 : term189 = term157.
Proof. exact (MK_COMB (@lem5373269) (@lem5373268)). Qed.
Lemma lem5373271 : term184 = term157.
Proof. exact (TRANS (@lem5373264) (@lem5373270)). Qed.
Lemma lem5373272 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373273 : term299 = term291.
Proof. exact (MK_COMB (@lem5373272) (@lem5373271)). Qed.
Lemma lem5373274 : term300 = term293.
Proof. exact (MK_COMB (@lem5373273) (@lem5373261)). Qed.
Lemma lem5373276 (m : nat) : (term301 m) = term112.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5373277 : term293 = term112.
Proof. exact (@lem5373276 term126). Qed.
Lemma lem5373278 : term300 = term112.
Proof. exact (TRANS (@lem5373274) (@lem5373277)). Qed.
Lemma lem5373279 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5373280 : term302 = term303.
Proof. exact (MK_COMB (@lem5373279) (@lem5373278)). Qed.
Lemma lem5373281 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem5373282 : term304 = term269.
Proof. exact (MK_COMB (@lem5373280) (@lem5373281)). Qed.
Lemma lem5373284 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373285 : term269 = term112.
Proof. exact (@lem5373284 term126). Qed.
Lemma lem5373286 : term304 = term112.
Proof. exact (TRANS (@lem5373282) (@lem5373285)). Qed.
Lemma lem5373288 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373289 : term166 = term167.
Proof. exact (@lem5373288 term126 term126). Qed.
Lemma lem5373290 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373291 : term169 = term126.
Proof. exact (EQ_MP (@lem5373290) (@lem940073)). Qed.
Lemma lem5373292 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373293 : term167 = term125.
Proof. exact (MK_COMB (@lem5373292) (@lem5373291)). Qed.
Lemma lem5373294 : term166 = term125.
Proof. exact (TRANS (@lem5373289) (@lem5373293)). Qed.
Lemma lem5373295 : term303 = term303.
Proof. exact (eq_refl term303). Qed.
Lemma lem5373296 : term305 = term269.
Proof. exact (MK_COMB (@lem5373295) (@lem5373294)). Qed.
Lemma lem5373298 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373299 : term269 = term112.
Proof. exact (@lem5373298 term126). Qed.
Lemma lem5373300 : term305 = term112.
Proof. exact (TRANS (@lem5373296) (@lem5373299)). Qed.
Lemma lem5373301 : term112 = term305.
Proof. exact (SYM (@lem5373300)). Qed.
Lemma lem5373302 : term304 = term305.
Proof. exact (TRANS (@lem5373286) (@lem5373301)). Qed.
Lemma lem5373303 : term294 = term154.
Proof. exact (@lem5373253 (@lem5373302)). Qed.
Lemma lem5373304 : term293 = term154.
Proof. exact (TRANS (@lem5373219) (@lem5373303)). Qed.
Lemma lem5373306 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5373307 : term154 = term112.
Proof. exact (@lem5373306 term112). Qed.
Lemma lem5373308 : term293 = term112.
Proof. exact (TRANS (@lem5373304) (@lem5373307)). Qed.
Lemma lem5373309 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5373310 : term306 = term303.
Proof. exact (MK_COMB (@lem5373309) (@lem5373308)). Qed.
Lemma lem5373311 (_69741 : int) : (real_of_int _69741) = (real_of_int _69741).
Proof. exact (eq_refl (real_of_int _69741)). Qed.
Lemma lem5373312 (_69741 : int) : (term290 _69741) = (term307 _69741).
Proof. exact (MK_COMB (@lem5373310) (@lem5373311 _69741)). Qed.
Lemma lem5373313 (_69741 : int) : (term289 _69741) = (term307 _69741).
Proof. exact (TRANS (@lem5373210 _69741) (@lem5373312 _69741)). Qed.
Lemma lem5373314 (_69741 : int) : (term307 _69741) = term112.
Proof. exact (@lem1982719 (real_of_int _69741)). Qed.
Lemma lem5373315 (_69741 : int) : (term289 _69741) = term112.
Proof. exact (TRANS (@lem5373313 _69741) (@lem5373314 _69741)). Qed.
Lemma lem5373316 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373317 (_69741 : int) : (term308 _69741) = term309.
Proof. exact (MK_COMB (@lem5373316) (@lem5373315 _69741)). Qed.
Lemma lem5373318 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem5373319 (_69741 : int) : (term359 _69741) = term314.
Proof. exact (MK_COMB (@lem5373317 _69741) (@lem5373318)). Qed.
Lemma lem5373320 (_69741 : int) : (term358 _69741) = term314.
Proof. exact (TRANS (@lem5373209 _69741) (@lem5373319 _69741)). Qed.
Lemma lem5373321 : term314 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem5373322 (_69741 : int) : (term358 _69741) = term157.
Proof. exact (TRANS (@lem5373320 _69741) (@lem5373321)). Qed.
Lemma lem5373323 (_69740 : int) (_69741 : int) : (term356 _69740 _69741) = term314.
Proof. exact (MK_COMB (@lem5373208 _69740) (@lem5373322 _69741)). Qed.
Lemma lem5373324 (_69740 : int) (_69741 : int) : (term355 _69740 _69741) = term314.
Proof. exact (TRANS (@lem5373100 _69740 _69741) (@lem5373323 _69740 _69741)). Qed.
Lemma lem5373325 : term314 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem5373326 (_69740 : int) (_69741 : int) : (term355 _69740 _69741) = term157.
Proof. exact (TRANS (@lem5373324 _69740 _69741) (@lem5373325)). Qed.
Lemma lem5373327 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5373328 (_69740 : int) (_69741 : int) : (term360 _69740 _69741) = term316.
Proof. exact (MK_COMB (@lem5373327) (@lem5373326 _69740 _69741)). Qed.
Lemma lem5373329 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5373330 (_69740 : int) (_69741 : int) : (term354 _69740 _69741) = term317.
Proof. exact (MK_COMB (@lem5373328 _69740 _69741) (@lem5373329)). Qed.
Lemma lem5373331 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : term317.
Proof. exact (EQ_MP (@lem5373330 _69740 _69741) (@lem5373099 _69740 _69741 h1)). Qed.
Lemma lem5373333 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5373334 : term317 = term318.
Proof. exact (@lem5373333 term112 term157). Qed.
Lemma lem5373336 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5373337 : term157 = term158.
Proof. exact (@lem5373336 term126). Qed.
Lemma lem5373339 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373340 : term112 = term154.
Proof. exact (@lem5373339 (NUMERAL 0)). Qed.
Lemma lem5373341 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5373342 : term114 = term319.
Proof. exact (MK_COMB (@lem5373341) (@lem5373340)). Qed.
Lemma lem5373343 : term318 = term320.
Proof. exact (MK_COMB (@lem5373342) (@lem5373337)). Qed.
Lemma lem5373344 : term321.
Proof. exact (@lem1980026 term112 term125 term157 term125). Qed.
Lemma lem5373346 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373347 : term258 = term264.
Proof. exact (@lem5373346 (NUMERAL 0) term126). Qed.
Lemma lem5373348 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373349 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373350 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373349 h1) (fun h1 : term264 = True => @lem5373348)). Qed.
Lemma lem5373351 : term264 = True.
Proof. exact (EQ_MP (@lem5373350) (@lem5373348)). Qed.
Lemma lem5373352 : term258 = True.
Proof. exact (TRANS (@lem5373347) (@lem5373351)). Qed.
Lemma lem5373353 : True = term258.
Proof. exact (SYM (@lem5373352)). Qed.
Lemma lem5373354 : term258.
Proof. exact (EQ_MP (@lem5373353) (@lem0)). Qed.
Lemma lem5373355 : term322.
Proof. exact (@lem5373344 (@lem5373354)). Qed.
Lemma lem5373357 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373358 : term258 = term264.
Proof. exact (@lem5373357 (NUMERAL 0) term126). Qed.
Lemma lem5373359 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373360 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373361 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373360 h1) (fun h1 : term264 = True => @lem5373359)). Qed.
Lemma lem5373362 : term264 = True.
Proof. exact (EQ_MP (@lem5373361) (@lem5373359)). Qed.
Lemma lem5373363 : term258 = True.
Proof. exact (TRANS (@lem5373358) (@lem5373362)). Qed.
Lemma lem5373364 : True = term258.
Proof. exact (SYM (@lem5373363)). Qed.
Lemma lem5373365 : term258.
Proof. exact (EQ_MP (@lem5373364) (@lem0)). Qed.
Lemma lem5373366 : term320 = term323.
Proof. exact (@lem5373355 (@lem5373365)). Qed.
Lemma lem5373368 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5373369 : term184 = term189.
Proof. exact (@lem5373368 term126 term126). Qed.
Lemma lem5373370 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373371 : term169 = term126.
Proof. exact (EQ_MP (@lem5373370) (@lem940073)). Qed.
Lemma lem5373372 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373373 : term167 = term125.
Proof. exact (MK_COMB (@lem5373372) (@lem5373371)). Qed.
Lemma lem5373374 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5373375 : term189 = term157.
Proof. exact (MK_COMB (@lem5373374) (@lem5373373)). Qed.
Lemma lem5373376 : term184 = term157.
Proof. exact (TRANS (@lem5373369) (@lem5373375)). Qed.
Lemma lem5373378 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373379 : term269 = term112.
Proof. exact (@lem5373378 term126). Qed.
Lemma lem5373380 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5373381 : term324 = term114.
Proof. exact (MK_COMB (@lem5373380) (@lem5373379)). Qed.
Lemma lem5373382 : term323 = term318.
Proof. exact (MK_COMB (@lem5373381) (@lem5373376)). Qed.
Lemma lem5373384 (m : nat) (n : nat) : (term325 m n) = (term326 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5373385 : term318 = term327.
Proof. exact (@lem5373384 (NUMERAL 0) term126). Qed.
Lemma lem5373386 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373387 (h1 : term265 = (BIT1 0)) : (term126 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5373388 : (term265 = (BIT1 0)) = ((term126 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373387 h1) (fun h1 : (term126 = (NUMERAL 0)) = False => @lem5373386)). Qed.
Lemma lem5373389 : (term126 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5373388) (@lem5373386)). Qed.
Lemma lem5373390 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5373391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5373392 : term328 = (and True).
Proof. exact (MK_COMB (@lem5373391) (@lem5373390)). Qed.
Lemma lem5373393 : term327 = (True /\ False).
Proof. exact (MK_COMB (@lem5373392) (@lem5373389)). Qed.
Lemma lem5373395 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5373396 : term327 = False.
Proof. exact (TRANS (@lem5373393) (@lem5373395)). Qed.
Lemma lem5373397 : term318 = False.
Proof. exact (TRANS (@lem5373385) (@lem5373396)). Qed.
Lemma lem5373398 : term323 = False.
Proof. exact (TRANS (@lem5373382) (@lem5373397)). Qed.
Lemma lem5373399 : term320 = False.
Proof. exact (TRANS (@lem5373366) (@lem5373398)). Qed.
Lemma lem5373400 : term318 = False.
Proof. exact (TRANS (@lem5373343) (@lem5373399)). Qed.
Lemma lem5373401 : term317 = False.
Proof. exact (TRANS (@lem5373334) (@lem5373400)). Qed.
Lemma lem5373402 (_69740 : int) (_69741 : int) (h1 : term329 _69740 _69741) : False.
Proof. exact (EQ_MP (@lem5373401) (@lem5373331 _69740 _69741 h1)). Qed.
Lemma lem5373403 (_69740 : int) (_69741 : int) (h1 : term250 _69740 _69741) : False.
Proof. exact (or_elim (@lem5372550 _69740 _69741 h1) (fun h0 : term256 _69740 _69741 => @lem5372952 _69740 _69741 h0) (fun h0 : term329 _69740 _69741 => @lem5373402 _69740 _69741 h0)). Qed.
Lemma lem5373404 (_69740 : int) (_69741 : int) (h1 : term246 _69740 _69741) : term246 _69740 _69741.
Proof. exact (h1). Qed.
Lemma lem5373405 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term361 _69740 _69741.
Proof. exact (h1). Qed.
Lemma lem5373406 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term247 _69740 _69741.
Proof. exact (proj2 (@lem5373405 _69740 _69741 h1)). Qed.
Lemma lem5373408 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term234 _69740 _69741.
Proof. exact (proj2 (@lem5373406 _69740 _69741 h1)). Qed.
Lemma lem5373410 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term197 _69740 _69741.
Proof. exact (proj2 (@lem5373408 _69740 _69741 h1)). Qed.
Lemma lem5373411 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term218 _69740 _69741.
Proof. exact (proj1 (@lem5373408 _69740 _69741 h1)). Qed.
Lemma lem5373413 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term214 _69740 _69741.
Proof. exact (proj1 (@lem5373411 _69740 _69741 h1)). Qed.
Lemma lem5373415 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5373416 : term257 = term258.
Proof. exact (@lem5373415 term112 term125). Qed.
Lemma lem5373418 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373419 : term125 = term183.
Proof. exact (@lem5373418 term126). Qed.
Lemma lem5373421 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373422 : term112 = term154.
Proof. exact (@lem5373421 (NUMERAL 0)). Qed.
Lemma lem5373423 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5373424 : term259 = term260.
Proof. exact (MK_COMB (@lem5373423) (@lem5373422)). Qed.
Lemma lem5373425 : term258 = term261.
Proof. exact (MK_COMB (@lem5373424) (@lem5373419)). Qed.
Lemma lem5373426 : term262.
Proof. exact (@lem1980255 term112 term125 term125 term125). Qed.
Lemma lem5373428 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373429 : term258 = term264.
Proof. exact (@lem5373428 (NUMERAL 0) term126). Qed.
Lemma lem5373430 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373431 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373432 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373431 h1) (fun h1 : term264 = True => @lem5373430)). Qed.
Lemma lem5373433 : term264 = True.
Proof. exact (EQ_MP (@lem5373432) (@lem5373430)). Qed.
Lemma lem5373434 : term258 = True.
Proof. exact (TRANS (@lem5373429) (@lem5373433)). Qed.
Lemma lem5373435 : True = term258.
Proof. exact (SYM (@lem5373434)). Qed.
Lemma lem5373436 : term258.
Proof. exact (EQ_MP (@lem5373435) (@lem0)). Qed.
Lemma lem5373437 : term266.
Proof. exact (@lem5373426 (@lem5373436)). Qed.
Lemma lem5373439 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373440 : term258 = term264.
Proof. exact (@lem5373439 (NUMERAL 0) term126). Qed.
Lemma lem5373441 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373442 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373443 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373442 h1) (fun h1 : term264 = True => @lem5373441)). Qed.
Lemma lem5373444 : term264 = True.
Proof. exact (EQ_MP (@lem5373443) (@lem5373441)). Qed.
Lemma lem5373445 : term258 = True.
Proof. exact (TRANS (@lem5373440) (@lem5373444)). Qed.
Lemma lem5373446 : True = term258.
Proof. exact (SYM (@lem5373445)). Qed.
Lemma lem5373447 : term258.
Proof. exact (EQ_MP (@lem5373446) (@lem0)). Qed.
Lemma lem5373448 : term261 = term267.
Proof. exact (@lem5373437 (@lem5373447)). Qed.
Lemma lem5373450 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373451 : term166 = term167.
Proof. exact (@lem5373450 term126 term126). Qed.
Lemma lem5373452 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373453 : term169 = term126.
Proof. exact (EQ_MP (@lem5373452) (@lem940073)). Qed.
Lemma lem5373454 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373455 : term167 = term125.
Proof. exact (MK_COMB (@lem5373454) (@lem5373453)). Qed.
Lemma lem5373456 : term166 = term125.
Proof. exact (TRANS (@lem5373451) (@lem5373455)). Qed.
Lemma lem5373458 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373459 : term269 = term112.
Proof. exact (@lem5373458 term126). Qed.
Lemma lem5373460 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5373461 : term270 = term259.
Proof. exact (MK_COMB (@lem5373460) (@lem5373459)). Qed.
Lemma lem5373462 : term267 = term258.
Proof. exact (MK_COMB (@lem5373461) (@lem5373456)). Qed.
Lemma lem5373464 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373465 : term258 = term264.
Proof. exact (@lem5373464 (NUMERAL 0) term126). Qed.
Lemma lem5373466 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373467 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373468 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373467 h1) (fun h1 : term264 = True => @lem5373466)). Qed.
Lemma lem5373469 : term264 = True.
Proof. exact (EQ_MP (@lem5373468) (@lem5373466)). Qed.
Lemma lem5373470 : term258 = True.
Proof. exact (TRANS (@lem5373465) (@lem5373469)). Qed.
Lemma lem5373471 : term267 = True.
Proof. exact (TRANS (@lem5373462) (@lem5373470)). Qed.
Lemma lem5373472 : term261 = True.
Proof. exact (TRANS (@lem5373448) (@lem5373471)). Qed.
Lemma lem5373473 : term258 = True.
Proof. exact (TRANS (@lem5373425) (@lem5373472)). Qed.
Lemma lem5373474 : term257 = True.
Proof. exact (TRANS (@lem5373416) (@lem5373473)). Qed.
Lemma lem5373475 : True = term257.
Proof. exact (SYM (@lem5373474)). Qed.
Lemma lem5373476 : term257.
Proof. exact (EQ_MP (@lem5373475) (@lem0)). Qed.
Lemma lem5373477 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term271 _69740 _69741.
Proof. exact (conj (@lem5373476) (@lem5373410 _69740 _69741 h1)). Qed.
Lemma lem5373479 (x : real) (y : real) : term272 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5373480 (_69740 : int) (_69741 : int) : term273 _69740 _69741.
Proof. exact (@lem5373479 term125 (term194 _69740 _69741)). Qed.
Lemma lem5373481 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term274 _69740 _69741.
Proof. exact (@lem5373480 _69740 _69741 (@lem5373477 _69740 _69741 h1)). Qed.
Lemma lem5373482 (_69740 : int) (_69741 : int) : (term275 _69740 _69741) = (term194 _69740 _69741).
Proof. exact (@lem1982733 (term194 _69740 _69741)). Qed.
Lemma lem5373483 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5373484 (_69740 : int) (_69741 : int) : (term276 _69740 _69741) = (term196 _69740 _69741).
Proof. exact (MK_COMB (@lem5373483) (@lem5373482 _69740 _69741)). Qed.
Lemma lem5373485 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5373486 (_69740 : int) (_69741 : int) : (term274 _69740 _69741) = (term197 _69740 _69741).
Proof. exact (MK_COMB (@lem5373484 _69740 _69741) (@lem5373485)). Qed.
Lemma lem5373487 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term197 _69740 _69741.
Proof. exact (EQ_MP (@lem5373486 _69740 _69741) (@lem5373481 _69740 _69741 h1)). Qed.
Lemma lem5373489 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5373490 : term257 = term258.
Proof. exact (@lem5373489 term112 term125). Qed.
Lemma lem5373492 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373493 : term125 = term183.
Proof. exact (@lem5373492 term126). Qed.
Lemma lem5373495 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373496 : term112 = term154.
Proof. exact (@lem5373495 (NUMERAL 0)). Qed.
Lemma lem5373497 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5373498 : term259 = term260.
Proof. exact (MK_COMB (@lem5373497) (@lem5373496)). Qed.
Lemma lem5373499 : term258 = term261.
Proof. exact (MK_COMB (@lem5373498) (@lem5373493)). Qed.
Lemma lem5373500 : term262.
Proof. exact (@lem1980255 term112 term125 term125 term125). Qed.
Lemma lem5373502 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373503 : term258 = term264.
Proof. exact (@lem5373502 (NUMERAL 0) term126). Qed.
Lemma lem5373504 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373505 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373506 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373505 h1) (fun h1 : term264 = True => @lem5373504)). Qed.
Lemma lem5373507 : term264 = True.
Proof. exact (EQ_MP (@lem5373506) (@lem5373504)). Qed.
Lemma lem5373508 : term258 = True.
Proof. exact (TRANS (@lem5373503) (@lem5373507)). Qed.
Lemma lem5373509 : True = term258.
Proof. exact (SYM (@lem5373508)). Qed.
Lemma lem5373510 : term258.
Proof. exact (EQ_MP (@lem5373509) (@lem0)). Qed.
Lemma lem5373511 : term266.
Proof. exact (@lem5373500 (@lem5373510)). Qed.
Lemma lem5373513 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373514 : term258 = term264.
Proof. exact (@lem5373513 (NUMERAL 0) term126). Qed.
Lemma lem5373515 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373516 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373517 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373516 h1) (fun h1 : term264 = True => @lem5373515)). Qed.
Lemma lem5373518 : term264 = True.
Proof. exact (EQ_MP (@lem5373517) (@lem5373515)). Qed.
Lemma lem5373519 : term258 = True.
Proof. exact (TRANS (@lem5373514) (@lem5373518)). Qed.
Lemma lem5373520 : True = term258.
Proof. exact (SYM (@lem5373519)). Qed.
Lemma lem5373521 : term258.
Proof. exact (EQ_MP (@lem5373520) (@lem0)). Qed.
Lemma lem5373522 : term261 = term267.
Proof. exact (@lem5373511 (@lem5373521)). Qed.
Lemma lem5373524 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373525 : term166 = term167.
Proof. exact (@lem5373524 term126 term126). Qed.
Lemma lem5373526 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373527 : term169 = term126.
Proof. exact (EQ_MP (@lem5373526) (@lem940073)). Qed.
Lemma lem5373528 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373529 : term167 = term125.
Proof. exact (MK_COMB (@lem5373528) (@lem5373527)). Qed.
Lemma lem5373530 : term166 = term125.
Proof. exact (TRANS (@lem5373525) (@lem5373529)). Qed.
Lemma lem5373532 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373533 : term269 = term112.
Proof. exact (@lem5373532 term126). Qed.
Lemma lem5373534 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5373535 : term270 = term259.
Proof. exact (MK_COMB (@lem5373534) (@lem5373533)). Qed.
Lemma lem5373536 : term267 = term258.
Proof. exact (MK_COMB (@lem5373535) (@lem5373530)). Qed.
Lemma lem5373538 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373539 : term258 = term264.
Proof. exact (@lem5373538 (NUMERAL 0) term126). Qed.
Lemma lem5373540 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373541 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373542 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373541 h1) (fun h1 : term264 = True => @lem5373540)). Qed.
Lemma lem5373543 : term264 = True.
Proof. exact (EQ_MP (@lem5373542) (@lem5373540)). Qed.
Lemma lem5373544 : term258 = True.
Proof. exact (TRANS (@lem5373539) (@lem5373543)). Qed.
Lemma lem5373545 : term267 = True.
Proof. exact (TRANS (@lem5373536) (@lem5373544)). Qed.
Lemma lem5373546 : term261 = True.
Proof. exact (TRANS (@lem5373522) (@lem5373545)). Qed.
Lemma lem5373547 : term258 = True.
Proof. exact (TRANS (@lem5373499) (@lem5373546)). Qed.
Lemma lem5373548 : term257 = True.
Proof. exact (TRANS (@lem5373490) (@lem5373547)). Qed.
Lemma lem5373549 : True = term257.
Proof. exact (SYM (@lem5373548)). Qed.
Lemma lem5373550 : term257.
Proof. exact (EQ_MP (@lem5373549) (@lem0)). Qed.
Lemma lem5373551 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term362 _69740 _69741.
Proof. exact (conj (@lem5373550) (@lem5373413 _69740 _69741 h1)). Qed.
Lemma lem5373553 (x : real) (y : real) : term272 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5373554 (_69740 : int) (_69741 : int) : term363 _69740 _69741.
Proof. exact (@lem5373553 term125 (term206 _69740 _69741)). Qed.
Lemma lem5373555 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term364 _69740 _69741.
Proof. exact (@lem5373554 _69740 _69741 (@lem5373551 _69740 _69741 h1)). Qed.
Lemma lem5373556 (_69740 : int) (_69741 : int) : (term281 _69740 _69741) = (term206 _69740 _69741).
Proof. exact (@lem1982733 (term206 _69740 _69741)). Qed.
Lemma lem5373557 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5373558 (_69740 : int) (_69741 : int) : (term365 _69740 _69741) = (term213 _69740 _69741).
Proof. exact (MK_COMB (@lem5373557) (@lem5373556 _69740 _69741)). Qed.
Lemma lem5373559 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5373560 (_69740 : int) (_69741 : int) : (term364 _69740 _69741) = (term214 _69740 _69741).
Proof. exact (MK_COMB (@lem5373558 _69740 _69741) (@lem5373559)). Qed.
Lemma lem5373561 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term214 _69740 _69741.
Proof. exact (EQ_MP (@lem5373560 _69740 _69741) (@lem5373555 _69740 _69741 h1)). Qed.
Lemma lem5373562 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term366 _69740 _69741.
Proof. exact (conj (@lem5373561 _69740 _69741 h1) (@lem5373487 _69740 _69741 h1)). Qed.
Lemma lem5373564 (x : real) (y : real) : term367 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5373565 (_69740 : int) (_69741 : int) : term368 _69740 _69741.
Proof. exact (@lem5373564 (term206 _69740 _69741) (term194 _69740 _69741)). Qed.
Lemma lem5373566 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term286 _69740 _69741.
Proof. exact (@lem5373565 _69740 _69741 (@lem5373562 _69740 _69741 h1)). Qed.
Lemma lem5373567 (_69740 : int) (_69741 : int) : (term287 _69740 _69741) = (term288 _69740 _69741).
Proof. exact (@lem1982753 (term199 _69740) (real_of_int _69740) (real_of_int _69741) (term193 _69741)). Qed.
Lemma lem5373568 (_69740 : int) : (term289 _69740) = (term290 _69740).
Proof. exact (@lem1982713 term157 (real_of_int _69740)). Qed.
Lemma lem5373570 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373571 : term125 = term183.
Proof. exact (@lem5373570 term126). Qed.
Lemma lem5373573 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5373574 : term157 = term158.
Proof. exact (@lem5373573 term126). Qed.
Lemma lem5373575 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373576 : term291 = term292.
Proof. exact (MK_COMB (@lem5373575) (@lem5373574)). Qed.
Lemma lem5373577 : term293 = term294.
Proof. exact (MK_COMB (@lem5373576) (@lem5373571)). Qed.
Lemma lem5373578 : term295.
Proof. exact (@lem1981473 term157 term125 term125 term125 term112 term125). Qed.
Lemma lem5373580 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373581 : term258 = term264.
Proof. exact (@lem5373580 (NUMERAL 0) term126). Qed.
Lemma lem5373582 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373583 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373584 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373583 h1) (fun h1 : term264 = True => @lem5373582)). Qed.
Lemma lem5373585 : term264 = True.
Proof. exact (EQ_MP (@lem5373584) (@lem5373582)). Qed.
Lemma lem5373586 : term258 = True.
Proof. exact (TRANS (@lem5373581) (@lem5373585)). Qed.
Lemma lem5373587 : True = term258.
Proof. exact (SYM (@lem5373586)). Qed.
Lemma lem5373588 : term258.
Proof. exact (EQ_MP (@lem5373587) (@lem0)). Qed.
Lemma lem5373589 : term296.
Proof. exact (@lem5373578 (@lem5373588)). Qed.
Lemma lem5373591 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373592 : term258 = term264.
Proof. exact (@lem5373591 (NUMERAL 0) term126). Qed.
Lemma lem5373593 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373594 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373595 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373594 h1) (fun h1 : term264 = True => @lem5373593)). Qed.
Lemma lem5373596 : term264 = True.
Proof. exact (EQ_MP (@lem5373595) (@lem5373593)). Qed.
Lemma lem5373597 : term258 = True.
Proof. exact (TRANS (@lem5373592) (@lem5373596)). Qed.
Lemma lem5373598 : True = term258.
Proof. exact (SYM (@lem5373597)). Qed.
Lemma lem5373599 : term258.
Proof. exact (EQ_MP (@lem5373598) (@lem0)). Qed.
Lemma lem5373600 : term297.
Proof. exact (@lem5373589 (@lem5373599)). Qed.
Lemma lem5373602 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373603 : term258 = term264.
Proof. exact (@lem5373602 (NUMERAL 0) term126). Qed.
Lemma lem5373604 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373605 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373606 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373605 h1) (fun h1 : term264 = True => @lem5373604)). Qed.
Lemma lem5373607 : term264 = True.
Proof. exact (EQ_MP (@lem5373606) (@lem5373604)). Qed.
Lemma lem5373608 : term258 = True.
Proof. exact (TRANS (@lem5373603) (@lem5373607)). Qed.
Lemma lem5373609 : True = term258.
Proof. exact (SYM (@lem5373608)). Qed.
Lemma lem5373610 : term258.
Proof. exact (EQ_MP (@lem5373609) (@lem0)). Qed.
Lemma lem5373611 : term298.
Proof. exact (@lem5373600 (@lem5373610)). Qed.
Lemma lem5373613 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373614 : term166 = term167.
Proof. exact (@lem5373613 term126 term126). Qed.
Lemma lem5373615 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373616 : term169 = term126.
Proof. exact (EQ_MP (@lem5373615) (@lem940073)). Qed.
Lemma lem5373617 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373618 : term167 = term125.
Proof. exact (MK_COMB (@lem5373617) (@lem5373616)). Qed.
Lemma lem5373619 : term166 = term125.
Proof. exact (TRANS (@lem5373614) (@lem5373618)). Qed.
Lemma lem5373621 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5373622 : term184 = term189.
Proof. exact (@lem5373621 term126 term126). Qed.
Lemma lem5373623 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373624 : term169 = term126.
Proof. exact (EQ_MP (@lem5373623) (@lem940073)). Qed.
Lemma lem5373625 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373626 : term167 = term125.
Proof. exact (MK_COMB (@lem5373625) (@lem5373624)). Qed.
Lemma lem5373627 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5373628 : term189 = term157.
Proof. exact (MK_COMB (@lem5373627) (@lem5373626)). Qed.
Lemma lem5373629 : term184 = term157.
Proof. exact (TRANS (@lem5373622) (@lem5373628)). Qed.
Lemma lem5373630 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373631 : term299 = term291.
Proof. exact (MK_COMB (@lem5373630) (@lem5373629)). Qed.
Lemma lem5373632 : term300 = term293.
Proof. exact (MK_COMB (@lem5373631) (@lem5373619)). Qed.
Lemma lem5373634 (m : nat) : (term301 m) = term112.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5373635 : term293 = term112.
Proof. exact (@lem5373634 term126). Qed.
Lemma lem5373636 : term300 = term112.
Proof. exact (TRANS (@lem5373632) (@lem5373635)). Qed.
Lemma lem5373637 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5373638 : term302 = term303.
Proof. exact (MK_COMB (@lem5373637) (@lem5373636)). Qed.
Lemma lem5373639 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem5373640 : term304 = term269.
Proof. exact (MK_COMB (@lem5373638) (@lem5373639)). Qed.
Lemma lem5373642 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373643 : term269 = term112.
Proof. exact (@lem5373642 term126). Qed.
Lemma lem5373644 : term304 = term112.
Proof. exact (TRANS (@lem5373640) (@lem5373643)). Qed.
Lemma lem5373646 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373647 : term166 = term167.
Proof. exact (@lem5373646 term126 term126). Qed.
Lemma lem5373648 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373649 : term169 = term126.
Proof. exact (EQ_MP (@lem5373648) (@lem940073)). Qed.
Lemma lem5373650 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373651 : term167 = term125.
Proof. exact (MK_COMB (@lem5373650) (@lem5373649)). Qed.
Lemma lem5373652 : term166 = term125.
Proof. exact (TRANS (@lem5373647) (@lem5373651)). Qed.
Lemma lem5373653 : term303 = term303.
Proof. exact (eq_refl term303). Qed.
Lemma lem5373654 : term305 = term269.
Proof. exact (MK_COMB (@lem5373653) (@lem5373652)). Qed.
Lemma lem5373656 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373657 : term269 = term112.
Proof. exact (@lem5373656 term126). Qed.
Lemma lem5373658 : term305 = term112.
Proof. exact (TRANS (@lem5373654) (@lem5373657)). Qed.
Lemma lem5373659 : term112 = term305.
Proof. exact (SYM (@lem5373658)). Qed.
Lemma lem5373660 : term304 = term305.
Proof. exact (TRANS (@lem5373644) (@lem5373659)). Qed.
Lemma lem5373661 : term294 = term154.
Proof. exact (@lem5373611 (@lem5373660)). Qed.
Lemma lem5373662 : term293 = term154.
Proof. exact (TRANS (@lem5373577) (@lem5373661)). Qed.
Lemma lem5373664 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5373665 : term154 = term112.
Proof. exact (@lem5373664 term112). Qed.
Lemma lem5373666 : term293 = term112.
Proof. exact (TRANS (@lem5373662) (@lem5373665)). Qed.
Lemma lem5373667 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5373668 : term306 = term303.
Proof. exact (MK_COMB (@lem5373667) (@lem5373666)). Qed.
Lemma lem5373669 (_69740 : int) : (real_of_int _69740) = (real_of_int _69740).
Proof. exact (eq_refl (real_of_int _69740)). Qed.
Lemma lem5373670 (_69740 : int) : (term290 _69740) = (term307 _69740).
Proof. exact (MK_COMB (@lem5373668) (@lem5373669 _69740)). Qed.
Lemma lem5373671 (_69740 : int) : (term289 _69740) = (term307 _69740).
Proof. exact (TRANS (@lem5373568 _69740) (@lem5373670 _69740)). Qed.
Lemma lem5373672 (_69740 : int) : (term307 _69740) = term112.
Proof. exact (@lem1982719 (real_of_int _69740)). Qed.
Lemma lem5373673 (_69740 : int) : (term289 _69740) = term112.
Proof. exact (TRANS (@lem5373671 _69740) (@lem5373672 _69740)). Qed.
Lemma lem5373674 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373675 (_69740 : int) : (term308 _69740) = term309.
Proof. exact (MK_COMB (@lem5373674) (@lem5373673 _69740)). Qed.
Lemma lem5373676 (_69741 : int) : (term310 _69741) = (term311 _69741).
Proof. exact (@lem1982763 (real_of_int _69741) (term199 _69741) term157). Qed.
Lemma lem5373677 (_69741 : int) : (term312 _69741) = (term290 _69741).
Proof. exact (@lem1982715 term157 (real_of_int _69741)). Qed.
Lemma lem5373679 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373680 : term125 = term183.
Proof. exact (@lem5373679 term126). Qed.
Lemma lem5373682 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5373683 : term157 = term158.
Proof. exact (@lem5373682 term126). Qed.
Lemma lem5373684 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373685 : term291 = term292.
Proof. exact (MK_COMB (@lem5373684) (@lem5373683)). Qed.
Lemma lem5373686 : term293 = term294.
Proof. exact (MK_COMB (@lem5373685) (@lem5373680)). Qed.
Lemma lem5373687 : term295.
Proof. exact (@lem1981473 term157 term125 term125 term125 term112 term125). Qed.
Lemma lem5373689 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373690 : term258 = term264.
Proof. exact (@lem5373689 (NUMERAL 0) term126). Qed.
Lemma lem5373691 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373692 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373693 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373692 h1) (fun h1 : term264 = True => @lem5373691)). Qed.
Lemma lem5373694 : term264 = True.
Proof. exact (EQ_MP (@lem5373693) (@lem5373691)). Qed.
Lemma lem5373695 : term258 = True.
Proof. exact (TRANS (@lem5373690) (@lem5373694)). Qed.
Lemma lem5373696 : True = term258.
Proof. exact (SYM (@lem5373695)). Qed.
Lemma lem5373697 : term258.
Proof. exact (EQ_MP (@lem5373696) (@lem0)). Qed.
Lemma lem5373698 : term296.
Proof. exact (@lem5373687 (@lem5373697)). Qed.
Lemma lem5373700 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373701 : term258 = term264.
Proof. exact (@lem5373700 (NUMERAL 0) term126). Qed.
Lemma lem5373702 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373703 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373704 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373703 h1) (fun h1 : term264 = True => @lem5373702)). Qed.
Lemma lem5373705 : term264 = True.
Proof. exact (EQ_MP (@lem5373704) (@lem5373702)). Qed.
Lemma lem5373706 : term258 = True.
Proof. exact (TRANS (@lem5373701) (@lem5373705)). Qed.
Lemma lem5373707 : True = term258.
Proof. exact (SYM (@lem5373706)). Qed.
Lemma lem5373708 : term258.
Proof. exact (EQ_MP (@lem5373707) (@lem0)). Qed.
Lemma lem5373709 : term297.
Proof. exact (@lem5373698 (@lem5373708)). Qed.
Lemma lem5373711 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373712 : term258 = term264.
Proof. exact (@lem5373711 (NUMERAL 0) term126). Qed.
Lemma lem5373713 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373714 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373715 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373714 h1) (fun h1 : term264 = True => @lem5373713)). Qed.
Lemma lem5373716 : term264 = True.
Proof. exact (EQ_MP (@lem5373715) (@lem5373713)). Qed.
Lemma lem5373717 : term258 = True.
Proof. exact (TRANS (@lem5373712) (@lem5373716)). Qed.
Lemma lem5373718 : True = term258.
Proof. exact (SYM (@lem5373717)). Qed.
Lemma lem5373719 : term258.
Proof. exact (EQ_MP (@lem5373718) (@lem0)). Qed.
Lemma lem5373720 : term298.
Proof. exact (@lem5373709 (@lem5373719)). Qed.
Lemma lem5373722 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373723 : term166 = term167.
Proof. exact (@lem5373722 term126 term126). Qed.
Lemma lem5373724 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373725 : term169 = term126.
Proof. exact (EQ_MP (@lem5373724) (@lem940073)). Qed.
Lemma lem5373726 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373727 : term167 = term125.
Proof. exact (MK_COMB (@lem5373726) (@lem5373725)). Qed.
Lemma lem5373728 : term166 = term125.
Proof. exact (TRANS (@lem5373723) (@lem5373727)). Qed.
Lemma lem5373730 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5373731 : term184 = term189.
Proof. exact (@lem5373730 term126 term126). Qed.
Lemma lem5373732 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373733 : term169 = term126.
Proof. exact (EQ_MP (@lem5373732) (@lem940073)). Qed.
Lemma lem5373734 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373735 : term167 = term125.
Proof. exact (MK_COMB (@lem5373734) (@lem5373733)). Qed.
Lemma lem5373736 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5373737 : term189 = term157.
Proof. exact (MK_COMB (@lem5373736) (@lem5373735)). Qed.
Lemma lem5373738 : term184 = term157.
Proof. exact (TRANS (@lem5373731) (@lem5373737)). Qed.
Lemma lem5373739 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373740 : term299 = term291.
Proof. exact (MK_COMB (@lem5373739) (@lem5373738)). Qed.
Lemma lem5373741 : term300 = term293.
Proof. exact (MK_COMB (@lem5373740) (@lem5373728)). Qed.
Lemma lem5373743 (m : nat) : (term301 m) = term112.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5373744 : term293 = term112.
Proof. exact (@lem5373743 term126). Qed.
Lemma lem5373745 : term300 = term112.
Proof. exact (TRANS (@lem5373741) (@lem5373744)). Qed.
Lemma lem5373746 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5373747 : term302 = term303.
Proof. exact (MK_COMB (@lem5373746) (@lem5373745)). Qed.
Lemma lem5373748 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem5373749 : term304 = term269.
Proof. exact (MK_COMB (@lem5373747) (@lem5373748)). Qed.
Lemma lem5373751 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373752 : term269 = term112.
Proof. exact (@lem5373751 term126). Qed.
Lemma lem5373753 : term304 = term112.
Proof. exact (TRANS (@lem5373749) (@lem5373752)). Qed.
Lemma lem5373755 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373756 : term166 = term167.
Proof. exact (@lem5373755 term126 term126). Qed.
Lemma lem5373757 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373758 : term169 = term126.
Proof. exact (EQ_MP (@lem5373757) (@lem940073)). Qed.
Lemma lem5373759 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373760 : term167 = term125.
Proof. exact (MK_COMB (@lem5373759) (@lem5373758)). Qed.
Lemma lem5373761 : term166 = term125.
Proof. exact (TRANS (@lem5373756) (@lem5373760)). Qed.
Lemma lem5373762 : term303 = term303.
Proof. exact (eq_refl term303). Qed.
Lemma lem5373763 : term305 = term269.
Proof. exact (MK_COMB (@lem5373762) (@lem5373761)). Qed.
Lemma lem5373765 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373766 : term269 = term112.
Proof. exact (@lem5373765 term126). Qed.
Lemma lem5373767 : term305 = term112.
Proof. exact (TRANS (@lem5373763) (@lem5373766)). Qed.
Lemma lem5373768 : term112 = term305.
Proof. exact (SYM (@lem5373767)). Qed.
Lemma lem5373769 : term304 = term305.
Proof. exact (TRANS (@lem5373753) (@lem5373768)). Qed.
Lemma lem5373770 : term294 = term154.
Proof. exact (@lem5373720 (@lem5373769)). Qed.
Lemma lem5373771 : term293 = term154.
Proof. exact (TRANS (@lem5373686) (@lem5373770)). Qed.
Lemma lem5373773 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5373774 : term154 = term112.
Proof. exact (@lem5373773 term112). Qed.
Lemma lem5373775 : term293 = term112.
Proof. exact (TRANS (@lem5373771) (@lem5373774)). Qed.
Lemma lem5373776 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5373777 : term306 = term303.
Proof. exact (MK_COMB (@lem5373776) (@lem5373775)). Qed.
Lemma lem5373778 (_69741 : int) : (real_of_int _69741) = (real_of_int _69741).
Proof. exact (eq_refl (real_of_int _69741)). Qed.
Lemma lem5373779 (_69741 : int) : (term290 _69741) = (term307 _69741).
Proof. exact (MK_COMB (@lem5373777) (@lem5373778 _69741)). Qed.
Lemma lem5373780 (_69741 : int) : (term312 _69741) = (term307 _69741).
Proof. exact (TRANS (@lem5373677 _69741) (@lem5373779 _69741)). Qed.
Lemma lem5373781 (_69741 : int) : (term307 _69741) = term112.
Proof. exact (@lem1982719 (real_of_int _69741)). Qed.
Lemma lem5373782 (_69741 : int) : (term312 _69741) = term112.
Proof. exact (TRANS (@lem5373780 _69741) (@lem5373781 _69741)). Qed.
Lemma lem5373783 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5373784 (_69741 : int) : (term313 _69741) = term309.
Proof. exact (MK_COMB (@lem5373783) (@lem5373782 _69741)). Qed.
Lemma lem5373785 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem5373786 (_69741 : int) : (term311 _69741) = term314.
Proof. exact (MK_COMB (@lem5373784 _69741) (@lem5373785)). Qed.
Lemma lem5373787 (_69741 : int) : (term310 _69741) = term314.
Proof. exact (TRANS (@lem5373676 _69741) (@lem5373786 _69741)). Qed.
Lemma lem5373788 : term314 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem5373789 (_69741 : int) : (term310 _69741) = term157.
Proof. exact (TRANS (@lem5373787 _69741) (@lem5373788)). Qed.
Lemma lem5373790 (_69740 : int) (_69741 : int) : (term288 _69740 _69741) = term314.
Proof. exact (MK_COMB (@lem5373675 _69740) (@lem5373789 _69741)). Qed.
Lemma lem5373791 (_69740 : int) (_69741 : int) : (term287 _69740 _69741) = term314.
Proof. exact (TRANS (@lem5373567 _69740 _69741) (@lem5373790 _69740 _69741)). Qed.
Lemma lem5373792 : term314 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem5373793 (_69740 : int) (_69741 : int) : (term287 _69740 _69741) = term157.
Proof. exact (TRANS (@lem5373791 _69740 _69741) (@lem5373792)). Qed.
Lemma lem5373794 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5373795 (_69740 : int) (_69741 : int) : (term315 _69740 _69741) = term316.
Proof. exact (MK_COMB (@lem5373794) (@lem5373793 _69740 _69741)). Qed.
Lemma lem5373796 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5373797 (_69740 : int) (_69741 : int) : (term286 _69740 _69741) = term317.
Proof. exact (MK_COMB (@lem5373795 _69740 _69741) (@lem5373796)). Qed.
Lemma lem5373798 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : term317.
Proof. exact (EQ_MP (@lem5373797 _69740 _69741) (@lem5373566 _69740 _69741 h1)). Qed.
Lemma lem5373800 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5373801 : term317 = term318.
Proof. exact (@lem5373800 term112 term157). Qed.
Lemma lem5373803 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5373804 : term157 = term158.
Proof. exact (@lem5373803 term126). Qed.
Lemma lem5373806 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373807 : term112 = term154.
Proof. exact (@lem5373806 (NUMERAL 0)). Qed.
Lemma lem5373808 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5373809 : term114 = term319.
Proof. exact (MK_COMB (@lem5373808) (@lem5373807)). Qed.
Lemma lem5373810 : term318 = term320.
Proof. exact (MK_COMB (@lem5373809) (@lem5373804)). Qed.
Lemma lem5373811 : term321.
Proof. exact (@lem1980026 term112 term125 term157 term125). Qed.
Lemma lem5373813 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373814 : term258 = term264.
Proof. exact (@lem5373813 (NUMERAL 0) term126). Qed.
Lemma lem5373815 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373816 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373817 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373816 h1) (fun h1 : term264 = True => @lem5373815)). Qed.
Lemma lem5373818 : term264 = True.
Proof. exact (EQ_MP (@lem5373817) (@lem5373815)). Qed.
Lemma lem5373819 : term258 = True.
Proof. exact (TRANS (@lem5373814) (@lem5373818)). Qed.
Lemma lem5373820 : True = term258.
Proof. exact (SYM (@lem5373819)). Qed.
Lemma lem5373821 : term258.
Proof. exact (EQ_MP (@lem5373820) (@lem0)). Qed.
Lemma lem5373822 : term322.
Proof. exact (@lem5373811 (@lem5373821)). Qed.
Lemma lem5373824 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373825 : term258 = term264.
Proof. exact (@lem5373824 (NUMERAL 0) term126). Qed.
Lemma lem5373826 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373827 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373828 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373827 h1) (fun h1 : term264 = True => @lem5373826)). Qed.
Lemma lem5373829 : term264 = True.
Proof. exact (EQ_MP (@lem5373828) (@lem5373826)). Qed.
Lemma lem5373830 : term258 = True.
Proof. exact (TRANS (@lem5373825) (@lem5373829)). Qed.
Lemma lem5373831 : True = term258.
Proof. exact (SYM (@lem5373830)). Qed.
Lemma lem5373832 : term258.
Proof. exact (EQ_MP (@lem5373831) (@lem0)). Qed.
Lemma lem5373833 : term320 = term323.
Proof. exact (@lem5373822 (@lem5373832)). Qed.
Lemma lem5373835 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5373836 : term184 = term189.
Proof. exact (@lem5373835 term126 term126). Qed.
Lemma lem5373837 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373838 : term169 = term126.
Proof. exact (EQ_MP (@lem5373837) (@lem940073)). Qed.
Lemma lem5373839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373840 : term167 = term125.
Proof. exact (MK_COMB (@lem5373839) (@lem5373838)). Qed.
Lemma lem5373841 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5373842 : term189 = term157.
Proof. exact (MK_COMB (@lem5373841) (@lem5373840)). Qed.
Lemma lem5373843 : term184 = term157.
Proof. exact (TRANS (@lem5373836) (@lem5373842)). Qed.
Lemma lem5373845 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373846 : term269 = term112.
Proof. exact (@lem5373845 term126). Qed.
Lemma lem5373847 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5373848 : term324 = term114.
Proof. exact (MK_COMB (@lem5373847) (@lem5373846)). Qed.
Lemma lem5373849 : term323 = term318.
Proof. exact (MK_COMB (@lem5373848) (@lem5373843)). Qed.
Lemma lem5373851 (m : nat) (n : nat) : (term325 m n) = (term326 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5373852 : term318 = term327.
Proof. exact (@lem5373851 (NUMERAL 0) term126). Qed.
Lemma lem5373853 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373854 (h1 : term265 = (BIT1 0)) : (term126 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5373855 : (term265 = (BIT1 0)) = ((term126 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373854 h1) (fun h1 : (term126 = (NUMERAL 0)) = False => @lem5373853)). Qed.
Lemma lem5373856 : (term126 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5373855) (@lem5373853)). Qed.
Lemma lem5373857 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5373858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5373859 : term328 = (and True).
Proof. exact (MK_COMB (@lem5373858) (@lem5373857)). Qed.
Lemma lem5373860 : term327 = (True /\ False).
Proof. exact (MK_COMB (@lem5373859) (@lem5373856)). Qed.
Lemma lem5373862 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5373863 : term327 = False.
Proof. exact (TRANS (@lem5373860) (@lem5373862)). Qed.
Lemma lem5373864 : term318 = False.
Proof. exact (TRANS (@lem5373852) (@lem5373863)). Qed.
Lemma lem5373865 : term323 = False.
Proof. exact (TRANS (@lem5373849) (@lem5373864)). Qed.
Lemma lem5373866 : term320 = False.
Proof. exact (TRANS (@lem5373833) (@lem5373865)). Qed.
Lemma lem5373867 : term318 = False.
Proof. exact (TRANS (@lem5373810) (@lem5373866)). Qed.
Lemma lem5373868 : term317 = False.
Proof. exact (TRANS (@lem5373801) (@lem5373867)). Qed.
Lemma lem5373869 (_69740 : int) (_69741 : int) (h1 : term361 _69740 _69741) : False.
Proof. exact (EQ_MP (@lem5373868) (@lem5373798 _69740 _69741 h1)). Qed.
Lemma lem5373870 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term369 _69740 _69741.
Proof. exact (h1). Qed.
Lemma lem5373871 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term248 _69740 _69741.
Proof. exact (proj2 (@lem5373870 _69740 _69741 h1)). Qed.
Lemma lem5373873 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term235 _69740 _69741.
Proof. exact (proj2 (@lem5373871 _69740 _69741 h1)). Qed.
Lemma lem5373875 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term201 _69740 _69741.
Proof. exact (proj2 (@lem5373873 _69740 _69741 h1)). Qed.
Lemma lem5373876 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term218 _69740 _69741.
Proof. exact (proj1 (@lem5373873 _69740 _69741 h1)). Qed.
Lemma lem5373877 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term216 _69740 _69741.
Proof. exact (proj2 (@lem5373876 _69740 _69741 h1)). Qed.
Lemma lem5373880 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5373881 : term257 = term258.
Proof. exact (@lem5373880 term112 term125). Qed.
Lemma lem5373883 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373884 : term125 = term183.
Proof. exact (@lem5373883 term126). Qed.
Lemma lem5373886 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373887 : term112 = term154.
Proof. exact (@lem5373886 (NUMERAL 0)). Qed.
Lemma lem5373888 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5373889 : term259 = term260.
Proof. exact (MK_COMB (@lem5373888) (@lem5373887)). Qed.
Lemma lem5373890 : term258 = term261.
Proof. exact (MK_COMB (@lem5373889) (@lem5373884)). Qed.
Lemma lem5373891 : term262.
Proof. exact (@lem1980255 term112 term125 term125 term125). Qed.
Lemma lem5373893 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373894 : term258 = term264.
Proof. exact (@lem5373893 (NUMERAL 0) term126). Qed.
Lemma lem5373895 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373896 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373897 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373896 h1) (fun h1 : term264 = True => @lem5373895)). Qed.
Lemma lem5373898 : term264 = True.
Proof. exact (EQ_MP (@lem5373897) (@lem5373895)). Qed.
Lemma lem5373899 : term258 = True.
Proof. exact (TRANS (@lem5373894) (@lem5373898)). Qed.
Lemma lem5373900 : True = term258.
Proof. exact (SYM (@lem5373899)). Qed.
Lemma lem5373901 : term258.
Proof. exact (EQ_MP (@lem5373900) (@lem0)). Qed.
Lemma lem5373902 : term266.
Proof. exact (@lem5373891 (@lem5373901)). Qed.
Lemma lem5373904 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373905 : term258 = term264.
Proof. exact (@lem5373904 (NUMERAL 0) term126). Qed.
Lemma lem5373906 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373907 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373908 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373907 h1) (fun h1 : term264 = True => @lem5373906)). Qed.
Lemma lem5373909 : term264 = True.
Proof. exact (EQ_MP (@lem5373908) (@lem5373906)). Qed.
Lemma lem5373910 : term258 = True.
Proof. exact (TRANS (@lem5373905) (@lem5373909)). Qed.
Lemma lem5373911 : True = term258.
Proof. exact (SYM (@lem5373910)). Qed.
Lemma lem5373912 : term258.
Proof. exact (EQ_MP (@lem5373911) (@lem0)). Qed.
Lemma lem5373913 : term261 = term267.
Proof. exact (@lem5373902 (@lem5373912)). Qed.
Lemma lem5373915 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373916 : term166 = term167.
Proof. exact (@lem5373915 term126 term126). Qed.
Lemma lem5373917 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373918 : term169 = term126.
Proof. exact (EQ_MP (@lem5373917) (@lem940073)). Qed.
Lemma lem5373919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373920 : term167 = term125.
Proof. exact (MK_COMB (@lem5373919) (@lem5373918)). Qed.
Lemma lem5373921 : term166 = term125.
Proof. exact (TRANS (@lem5373916) (@lem5373920)). Qed.
Lemma lem5373923 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373924 : term269 = term112.
Proof. exact (@lem5373923 term126). Qed.
Lemma lem5373925 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5373926 : term270 = term259.
Proof. exact (MK_COMB (@lem5373925) (@lem5373924)). Qed.
Lemma lem5373927 : term267 = term258.
Proof. exact (MK_COMB (@lem5373926) (@lem5373921)). Qed.
Lemma lem5373929 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373930 : term258 = term264.
Proof. exact (@lem5373929 (NUMERAL 0) term126). Qed.
Lemma lem5373931 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373932 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373933 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373932 h1) (fun h1 : term264 = True => @lem5373931)). Qed.
Lemma lem5373934 : term264 = True.
Proof. exact (EQ_MP (@lem5373933) (@lem5373931)). Qed.
Lemma lem5373935 : term258 = True.
Proof. exact (TRANS (@lem5373930) (@lem5373934)). Qed.
Lemma lem5373936 : term267 = True.
Proof. exact (TRANS (@lem5373927) (@lem5373935)). Qed.
Lemma lem5373937 : term261 = True.
Proof. exact (TRANS (@lem5373913) (@lem5373936)). Qed.
Lemma lem5373938 : term258 = True.
Proof. exact (TRANS (@lem5373890) (@lem5373937)). Qed.
Lemma lem5373939 : term257 = True.
Proof. exact (TRANS (@lem5373881) (@lem5373938)). Qed.
Lemma lem5373940 : True = term257.
Proof. exact (SYM (@lem5373939)). Qed.
Lemma lem5373941 : term257.
Proof. exact (EQ_MP (@lem5373940) (@lem0)). Qed.
Lemma lem5373942 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term330 _69740 _69741.
Proof. exact (conj (@lem5373941) (@lem5373875 _69740 _69741 h1)). Qed.
Lemma lem5373944 (x : real) (y : real) : term272 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5373945 (_69740 : int) (_69741 : int) : term331 _69740 _69741.
Proof. exact (@lem5373944 term125 (term198 _69740 _69741)). Qed.
Lemma lem5373946 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term332 _69740 _69741.
Proof. exact (@lem5373945 _69740 _69741 (@lem5373942 _69740 _69741 h1)). Qed.
Lemma lem5373947 (_69740 : int) (_69741 : int) : (term333 _69740 _69741) = (term198 _69740 _69741).
Proof. exact (@lem1982733 (term198 _69740 _69741)). Qed.
Lemma lem5373948 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5373949 (_69740 : int) (_69741 : int) : (term334 _69740 _69741) = (term200 _69740 _69741).
Proof. exact (MK_COMB (@lem5373948) (@lem5373947 _69740 _69741)). Qed.
Lemma lem5373950 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5373951 (_69740 : int) (_69741 : int) : (term332 _69740 _69741) = (term201 _69740 _69741).
Proof. exact (MK_COMB (@lem5373949 _69740 _69741) (@lem5373950)). Qed.
Lemma lem5373952 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term201 _69740 _69741.
Proof. exact (EQ_MP (@lem5373951 _69740 _69741) (@lem5373946 _69740 _69741 h1)). Qed.
Lemma lem5373954 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5373955 : term257 = term258.
Proof. exact (@lem5373954 term112 term125). Qed.
Lemma lem5373957 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373958 : term125 = term183.
Proof. exact (@lem5373957 term126). Qed.
Lemma lem5373960 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5373961 : term112 = term154.
Proof. exact (@lem5373960 (NUMERAL 0)). Qed.
Lemma lem5373962 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5373963 : term259 = term260.
Proof. exact (MK_COMB (@lem5373962) (@lem5373961)). Qed.
Lemma lem5373964 : term258 = term261.
Proof. exact (MK_COMB (@lem5373963) (@lem5373958)). Qed.
Lemma lem5373965 : term262.
Proof. exact (@lem1980255 term112 term125 term125 term125). Qed.
Lemma lem5373967 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373968 : term258 = term264.
Proof. exact (@lem5373967 (NUMERAL 0) term126). Qed.
Lemma lem5373969 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373970 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373971 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373970 h1) (fun h1 : term264 = True => @lem5373969)). Qed.
Lemma lem5373972 : term264 = True.
Proof. exact (EQ_MP (@lem5373971) (@lem5373969)). Qed.
Lemma lem5373973 : term258 = True.
Proof. exact (TRANS (@lem5373968) (@lem5373972)). Qed.
Lemma lem5373974 : True = term258.
Proof. exact (SYM (@lem5373973)). Qed.
Lemma lem5373975 : term258.
Proof. exact (EQ_MP (@lem5373974) (@lem0)). Qed.
Lemma lem5373976 : term266.
Proof. exact (@lem5373965 (@lem5373975)). Qed.
Lemma lem5373978 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5373979 : term258 = term264.
Proof. exact (@lem5373978 (NUMERAL 0) term126). Qed.
Lemma lem5373980 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5373981 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5373982 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5373981 h1) (fun h1 : term264 = True => @lem5373980)). Qed.
Lemma lem5373983 : term264 = True.
Proof. exact (EQ_MP (@lem5373982) (@lem5373980)). Qed.
Lemma lem5373984 : term258 = True.
Proof. exact (TRANS (@lem5373979) (@lem5373983)). Qed.
Lemma lem5373985 : True = term258.
Proof. exact (SYM (@lem5373984)). Qed.
Lemma lem5373986 : term258.
Proof. exact (EQ_MP (@lem5373985) (@lem0)). Qed.
Lemma lem5373987 : term261 = term267.
Proof. exact (@lem5373976 (@lem5373986)). Qed.
Lemma lem5373989 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5373990 : term166 = term167.
Proof. exact (@lem5373989 term126 term126). Qed.
Lemma lem5373991 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5373992 : term169 = term126.
Proof. exact (EQ_MP (@lem5373991) (@lem940073)). Qed.
Lemma lem5373993 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5373994 : term167 = term125.
Proof. exact (MK_COMB (@lem5373993) (@lem5373992)). Qed.
Lemma lem5373995 : term166 = term125.
Proof. exact (TRANS (@lem5373990) (@lem5373994)). Qed.
Lemma lem5373997 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5373998 : term269 = term112.
Proof. exact (@lem5373997 term126). Qed.
Lemma lem5373999 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5374000 : term270 = term259.
Proof. exact (MK_COMB (@lem5373999) (@lem5373998)). Qed.
Lemma lem5374001 : term267 = term258.
Proof. exact (MK_COMB (@lem5374000) (@lem5373995)). Qed.
Lemma lem5374003 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5374004 : term258 = term264.
Proof. exact (@lem5374003 (NUMERAL 0) term126). Qed.
Lemma lem5374005 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5374006 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5374007 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5374006 h1) (fun h1 : term264 = True => @lem5374005)). Qed.
Lemma lem5374008 : term264 = True.
Proof. exact (EQ_MP (@lem5374007) (@lem5374005)). Qed.
Lemma lem5374009 : term258 = True.
Proof. exact (TRANS (@lem5374004) (@lem5374008)). Qed.
Lemma lem5374010 : term267 = True.
Proof. exact (TRANS (@lem5374001) (@lem5374009)). Qed.
Lemma lem5374011 : term261 = True.
Proof. exact (TRANS (@lem5373987) (@lem5374010)). Qed.
Lemma lem5374012 : term258 = True.
Proof. exact (TRANS (@lem5373964) (@lem5374011)). Qed.
Lemma lem5374013 : term257 = True.
Proof. exact (TRANS (@lem5373955) (@lem5374012)). Qed.
Lemma lem5374014 : True = term257.
Proof. exact (SYM (@lem5374013)). Qed.
Lemma lem5374015 : term257.
Proof. exact (EQ_MP (@lem5374014) (@lem0)). Qed.
Lemma lem5374016 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term370 _69740 _69741.
Proof. exact (conj (@lem5374015) (@lem5373877 _69740 _69741 h1)). Qed.
Lemma lem5374018 (x : real) (y : real) : term272 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5374019 (_69740 : int) (_69741 : int) : term371 _69740 _69741.
Proof. exact (@lem5374018 term125 (term205 _69740 _69741)). Qed.
Lemma lem5374020 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term372 _69740 _69741.
Proof. exact (@lem5374019 _69740 _69741 (@lem5374016 _69740 _69741 h1)). Qed.
Lemma lem5374021 (_69740 : int) (_69741 : int) : (term373 _69740 _69741) = (term205 _69740 _69741).
Proof. exact (@lem1982733 (term205 _69740 _69741)). Qed.
Lemma lem5374022 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5374023 (_69740 : int) (_69741 : int) : (term374 _69740 _69741) = (term215 _69740 _69741).
Proof. exact (MK_COMB (@lem5374022) (@lem5374021 _69740 _69741)). Qed.
Lemma lem5374024 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5374025 (_69740 : int) (_69741 : int) : (term372 _69740 _69741) = (term216 _69740 _69741).
Proof. exact (MK_COMB (@lem5374023 _69740 _69741) (@lem5374024)). Qed.
Lemma lem5374026 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term216 _69740 _69741.
Proof. exact (EQ_MP (@lem5374025 _69740 _69741) (@lem5374020 _69740 _69741 h1)). Qed.
Lemma lem5374027 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term375 _69740 _69741.
Proof. exact (conj (@lem5374026 _69740 _69741 h1) (@lem5373952 _69740 _69741 h1)). Qed.
Lemma lem5374029 (x : real) (y : real) : term367 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5374030 (_69740 : int) (_69741 : int) : term376 _69740 _69741.
Proof. exact (@lem5374029 (term205 _69740 _69741) (term198 _69740 _69741)). Qed.
Lemma lem5374031 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term354 _69740 _69741.
Proof. exact (@lem5374030 _69740 _69741 (@lem5374027 _69740 _69741 h1)). Qed.
Lemma lem5374032 (_69740 : int) (_69741 : int) : (term355 _69740 _69741) = (term356 _69740 _69741).
Proof. exact (@lem1982753 (real_of_int _69740) (term199 _69740) (term199 _69741) (term357 _69741)). Qed.
Lemma lem5374033 (_69740 : int) : (term312 _69740) = (term290 _69740).
Proof. exact (@lem1982715 term157 (real_of_int _69740)). Qed.
Lemma lem5374035 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5374036 : term125 = term183.
Proof. exact (@lem5374035 term126). Qed.
Lemma lem5374038 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5374039 : term157 = term158.
Proof. exact (@lem5374038 term126). Qed.
Lemma lem5374040 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5374041 : term291 = term292.
Proof. exact (MK_COMB (@lem5374040) (@lem5374039)). Qed.
Lemma lem5374042 : term293 = term294.
Proof. exact (MK_COMB (@lem5374041) (@lem5374036)). Qed.
Lemma lem5374043 : term295.
Proof. exact (@lem1981473 term157 term125 term125 term125 term112 term125). Qed.
Lemma lem5374045 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5374046 : term258 = term264.
Proof. exact (@lem5374045 (NUMERAL 0) term126). Qed.
Lemma lem5374047 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5374048 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5374049 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5374048 h1) (fun h1 : term264 = True => @lem5374047)). Qed.
Lemma lem5374050 : term264 = True.
Proof. exact (EQ_MP (@lem5374049) (@lem5374047)). Qed.
Lemma lem5374051 : term258 = True.
Proof. exact (TRANS (@lem5374046) (@lem5374050)). Qed.
Lemma lem5374052 : True = term258.
Proof. exact (SYM (@lem5374051)). Qed.
Lemma lem5374053 : term258.
Proof. exact (EQ_MP (@lem5374052) (@lem0)). Qed.
Lemma lem5374054 : term296.
Proof. exact (@lem5374043 (@lem5374053)). Qed.
Lemma lem5374056 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5374057 : term258 = term264.
Proof. exact (@lem5374056 (NUMERAL 0) term126). Qed.
Lemma lem5374058 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5374059 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5374060 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5374059 h1) (fun h1 : term264 = True => @lem5374058)). Qed.
Lemma lem5374061 : term264 = True.
Proof. exact (EQ_MP (@lem5374060) (@lem5374058)). Qed.
Lemma lem5374062 : term258 = True.
Proof. exact (TRANS (@lem5374057) (@lem5374061)). Qed.
Lemma lem5374063 : True = term258.
Proof. exact (SYM (@lem5374062)). Qed.
Lemma lem5374064 : term258.
Proof. exact (EQ_MP (@lem5374063) (@lem0)). Qed.
Lemma lem5374065 : term297.
Proof. exact (@lem5374054 (@lem5374064)). Qed.
Lemma lem5374067 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5374068 : term258 = term264.
Proof. exact (@lem5374067 (NUMERAL 0) term126). Qed.
Lemma lem5374069 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5374070 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5374071 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5374070 h1) (fun h1 : term264 = True => @lem5374069)). Qed.
Lemma lem5374072 : term264 = True.
Proof. exact (EQ_MP (@lem5374071) (@lem5374069)). Qed.
Lemma lem5374073 : term258 = True.
Proof. exact (TRANS (@lem5374068) (@lem5374072)). Qed.
Lemma lem5374074 : True = term258.
Proof. exact (SYM (@lem5374073)). Qed.
Lemma lem5374075 : term258.
Proof. exact (EQ_MP (@lem5374074) (@lem0)). Qed.
Lemma lem5374076 : term298.
Proof. exact (@lem5374065 (@lem5374075)). Qed.
Lemma lem5374078 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5374079 : term166 = term167.
Proof. exact (@lem5374078 term126 term126). Qed.
Lemma lem5374080 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5374081 : term169 = term126.
Proof. exact (EQ_MP (@lem5374080) (@lem940073)). Qed.
Lemma lem5374082 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5374083 : term167 = term125.
Proof. exact (MK_COMB (@lem5374082) (@lem5374081)). Qed.
Lemma lem5374084 : term166 = term125.
Proof. exact (TRANS (@lem5374079) (@lem5374083)). Qed.
Lemma lem5374086 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5374087 : term184 = term189.
Proof. exact (@lem5374086 term126 term126). Qed.
Lemma lem5374088 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5374089 : term169 = term126.
Proof. exact (EQ_MP (@lem5374088) (@lem940073)). Qed.
Lemma lem5374090 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5374091 : term167 = term125.
Proof. exact (MK_COMB (@lem5374090) (@lem5374089)). Qed.
Lemma lem5374092 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5374093 : term189 = term157.
Proof. exact (MK_COMB (@lem5374092) (@lem5374091)). Qed.
Lemma lem5374094 : term184 = term157.
Proof. exact (TRANS (@lem5374087) (@lem5374093)). Qed.
Lemma lem5374095 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5374096 : term299 = term291.
Proof. exact (MK_COMB (@lem5374095) (@lem5374094)). Qed.
Lemma lem5374097 : term300 = term293.
Proof. exact (MK_COMB (@lem5374096) (@lem5374084)). Qed.
Lemma lem5374099 (m : nat) : (term301 m) = term112.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5374100 : term293 = term112.
Proof. exact (@lem5374099 term126). Qed.
Lemma lem5374101 : term300 = term112.
Proof. exact (TRANS (@lem5374097) (@lem5374100)). Qed.
Lemma lem5374102 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5374103 : term302 = term303.
Proof. exact (MK_COMB (@lem5374102) (@lem5374101)). Qed.
Lemma lem5374104 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem5374105 : term304 = term269.
Proof. exact (MK_COMB (@lem5374103) (@lem5374104)). Qed.
Lemma lem5374107 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5374108 : term269 = term112.
Proof. exact (@lem5374107 term126). Qed.
Lemma lem5374109 : term304 = term112.
Proof. exact (TRANS (@lem5374105) (@lem5374108)). Qed.
Lemma lem5374111 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5374112 : term166 = term167.
Proof. exact (@lem5374111 term126 term126). Qed.
Lemma lem5374113 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5374114 : term169 = term126.
Proof. exact (EQ_MP (@lem5374113) (@lem940073)). Qed.
Lemma lem5374115 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5374116 : term167 = term125.
Proof. exact (MK_COMB (@lem5374115) (@lem5374114)). Qed.
Lemma lem5374117 : term166 = term125.
Proof. exact (TRANS (@lem5374112) (@lem5374116)). Qed.
Lemma lem5374118 : term303 = term303.
Proof. exact (eq_refl term303). Qed.
Lemma lem5374119 : term305 = term269.
Proof. exact (MK_COMB (@lem5374118) (@lem5374117)). Qed.
Lemma lem5374121 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5374122 : term269 = term112.
Proof. exact (@lem5374121 term126). Qed.
Lemma lem5374123 : term305 = term112.
Proof. exact (TRANS (@lem5374119) (@lem5374122)). Qed.
Lemma lem5374124 : term112 = term305.
Proof. exact (SYM (@lem5374123)). Qed.
Lemma lem5374125 : term304 = term305.
Proof. exact (TRANS (@lem5374109) (@lem5374124)). Qed.
Lemma lem5374126 : term294 = term154.
Proof. exact (@lem5374076 (@lem5374125)). Qed.
Lemma lem5374127 : term293 = term154.
Proof. exact (TRANS (@lem5374042) (@lem5374126)). Qed.
Lemma lem5374129 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5374130 : term154 = term112.
Proof. exact (@lem5374129 term112). Qed.
Lemma lem5374131 : term293 = term112.
Proof. exact (TRANS (@lem5374127) (@lem5374130)). Qed.
Lemma lem5374132 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5374133 : term306 = term303.
Proof. exact (MK_COMB (@lem5374132) (@lem5374131)). Qed.
Lemma lem5374134 (_69740 : int) : (real_of_int _69740) = (real_of_int _69740).
Proof. exact (eq_refl (real_of_int _69740)). Qed.
Lemma lem5374135 (_69740 : int) : (term290 _69740) = (term307 _69740).
Proof. exact (MK_COMB (@lem5374133) (@lem5374134 _69740)). Qed.
Lemma lem5374136 (_69740 : int) : (term312 _69740) = (term307 _69740).
Proof. exact (TRANS (@lem5374033 _69740) (@lem5374135 _69740)). Qed.
Lemma lem5374137 (_69740 : int) : (term307 _69740) = term112.
Proof. exact (@lem1982719 (real_of_int _69740)). Qed.
Lemma lem5374138 (_69740 : int) : (term312 _69740) = term112.
Proof. exact (TRANS (@lem5374136 _69740) (@lem5374137 _69740)). Qed.
Lemma lem5374139 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5374140 (_69740 : int) : (term313 _69740) = term309.
Proof. exact (MK_COMB (@lem5374139) (@lem5374138 _69740)). Qed.
Lemma lem5374141 (_69741 : int) : (term358 _69741) = (term359 _69741).
Proof. exact (@lem1982763 (term199 _69741) (real_of_int _69741) term157). Qed.
Lemma lem5374142 (_69741 : int) : (term289 _69741) = (term290 _69741).
Proof. exact (@lem1982713 term157 (real_of_int _69741)). Qed.
Lemma lem5374144 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5374145 : term125 = term183.
Proof. exact (@lem5374144 term126). Qed.
Lemma lem5374147 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5374148 : term157 = term158.
Proof. exact (@lem5374147 term126). Qed.
Lemma lem5374149 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5374150 : term291 = term292.
Proof. exact (MK_COMB (@lem5374149) (@lem5374148)). Qed.
Lemma lem5374151 : term293 = term294.
Proof. exact (MK_COMB (@lem5374150) (@lem5374145)). Qed.
Lemma lem5374152 : term295.
Proof. exact (@lem1981473 term157 term125 term125 term125 term112 term125). Qed.
Lemma lem5374154 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5374155 : term258 = term264.
Proof. exact (@lem5374154 (NUMERAL 0) term126). Qed.
Lemma lem5374156 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5374157 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5374158 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5374157 h1) (fun h1 : term264 = True => @lem5374156)). Qed.
Lemma lem5374159 : term264 = True.
Proof. exact (EQ_MP (@lem5374158) (@lem5374156)). Qed.
Lemma lem5374160 : term258 = True.
Proof. exact (TRANS (@lem5374155) (@lem5374159)). Qed.
Lemma lem5374161 : True = term258.
Proof. exact (SYM (@lem5374160)). Qed.
Lemma lem5374162 : term258.
Proof. exact (EQ_MP (@lem5374161) (@lem0)). Qed.
Lemma lem5374163 : term296.
Proof. exact (@lem5374152 (@lem5374162)). Qed.
Lemma lem5374165 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5374166 : term258 = term264.
Proof. exact (@lem5374165 (NUMERAL 0) term126). Qed.
Lemma lem5374167 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5374168 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5374169 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5374168 h1) (fun h1 : term264 = True => @lem5374167)). Qed.
Lemma lem5374170 : term264 = True.
Proof. exact (EQ_MP (@lem5374169) (@lem5374167)). Qed.
Lemma lem5374171 : term258 = True.
Proof. exact (TRANS (@lem5374166) (@lem5374170)). Qed.
Lemma lem5374172 : True = term258.
Proof. exact (SYM (@lem5374171)). Qed.
Lemma lem5374173 : term258.
Proof. exact (EQ_MP (@lem5374172) (@lem0)). Qed.
Lemma lem5374174 : term297.
Proof. exact (@lem5374163 (@lem5374173)). Qed.
Lemma lem5374176 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5374177 : term258 = term264.
Proof. exact (@lem5374176 (NUMERAL 0) term126). Qed.
Lemma lem5374178 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5374179 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5374180 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5374179 h1) (fun h1 : term264 = True => @lem5374178)). Qed.
Lemma lem5374181 : term264 = True.
Proof. exact (EQ_MP (@lem5374180) (@lem5374178)). Qed.
Lemma lem5374182 : term258 = True.
Proof. exact (TRANS (@lem5374177) (@lem5374181)). Qed.
Lemma lem5374183 : True = term258.
Proof. exact (SYM (@lem5374182)). Qed.
Lemma lem5374184 : term258.
Proof. exact (EQ_MP (@lem5374183) (@lem0)). Qed.
Lemma lem5374185 : term298.
Proof. exact (@lem5374174 (@lem5374184)). Qed.
Lemma lem5374187 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5374188 : term166 = term167.
Proof. exact (@lem5374187 term126 term126). Qed.
Lemma lem5374189 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5374190 : term169 = term126.
Proof. exact (EQ_MP (@lem5374189) (@lem940073)). Qed.
Lemma lem5374191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5374192 : term167 = term125.
Proof. exact (MK_COMB (@lem5374191) (@lem5374190)). Qed.
Lemma lem5374193 : term166 = term125.
Proof. exact (TRANS (@lem5374188) (@lem5374192)). Qed.
Lemma lem5374195 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5374196 : term184 = term189.
Proof. exact (@lem5374195 term126 term126). Qed.
Lemma lem5374197 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5374198 : term169 = term126.
Proof. exact (EQ_MP (@lem5374197) (@lem940073)). Qed.
Lemma lem5374199 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5374200 : term167 = term125.
Proof. exact (MK_COMB (@lem5374199) (@lem5374198)). Qed.
Lemma lem5374201 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5374202 : term189 = term157.
Proof. exact (MK_COMB (@lem5374201) (@lem5374200)). Qed.
Lemma lem5374203 : term184 = term157.
Proof. exact (TRANS (@lem5374196) (@lem5374202)). Qed.
Lemma lem5374204 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5374205 : term299 = term291.
Proof. exact (MK_COMB (@lem5374204) (@lem5374203)). Qed.
Lemma lem5374206 : term300 = term293.
Proof. exact (MK_COMB (@lem5374205) (@lem5374193)). Qed.
Lemma lem5374208 (m : nat) : (term301 m) = term112.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5374209 : term293 = term112.
Proof. exact (@lem5374208 term126). Qed.
Lemma lem5374210 : term300 = term112.
Proof. exact (TRANS (@lem5374206) (@lem5374209)). Qed.
Lemma lem5374211 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5374212 : term302 = term303.
Proof. exact (MK_COMB (@lem5374211) (@lem5374210)). Qed.
Lemma lem5374213 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem5374214 : term304 = term269.
Proof. exact (MK_COMB (@lem5374212) (@lem5374213)). Qed.
Lemma lem5374216 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5374217 : term269 = term112.
Proof. exact (@lem5374216 term126). Qed.
Lemma lem5374218 : term304 = term112.
Proof. exact (TRANS (@lem5374214) (@lem5374217)). Qed.
Lemma lem5374220 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5374221 : term166 = term167.
Proof. exact (@lem5374220 term126 term126). Qed.
Lemma lem5374222 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5374223 : term169 = term126.
Proof. exact (EQ_MP (@lem5374222) (@lem940073)). Qed.
Lemma lem5374224 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5374225 : term167 = term125.
Proof. exact (MK_COMB (@lem5374224) (@lem5374223)). Qed.
Lemma lem5374226 : term166 = term125.
Proof. exact (TRANS (@lem5374221) (@lem5374225)). Qed.
Lemma lem5374227 : term303 = term303.
Proof. exact (eq_refl term303). Qed.
Lemma lem5374228 : term305 = term269.
Proof. exact (MK_COMB (@lem5374227) (@lem5374226)). Qed.
Lemma lem5374230 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5374231 : term269 = term112.
Proof. exact (@lem5374230 term126). Qed.
Lemma lem5374232 : term305 = term112.
Proof. exact (TRANS (@lem5374228) (@lem5374231)). Qed.
Lemma lem5374233 : term112 = term305.
Proof. exact (SYM (@lem5374232)). Qed.
Lemma lem5374234 : term304 = term305.
Proof. exact (TRANS (@lem5374218) (@lem5374233)). Qed.
Lemma lem5374235 : term294 = term154.
Proof. exact (@lem5374185 (@lem5374234)). Qed.
Lemma lem5374236 : term293 = term154.
Proof. exact (TRANS (@lem5374151) (@lem5374235)). Qed.
Lemma lem5374238 (x : real) : (term173 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5374239 : term154 = term112.
Proof. exact (@lem5374238 term112). Qed.
Lemma lem5374240 : term293 = term112.
Proof. exact (TRANS (@lem5374236) (@lem5374239)). Qed.
Lemma lem5374241 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5374242 : term306 = term303.
Proof. exact (MK_COMB (@lem5374241) (@lem5374240)). Qed.
Lemma lem5374243 (_69741 : int) : (real_of_int _69741) = (real_of_int _69741).
Proof. exact (eq_refl (real_of_int _69741)). Qed.
Lemma lem5374244 (_69741 : int) : (term290 _69741) = (term307 _69741).
Proof. exact (MK_COMB (@lem5374242) (@lem5374243 _69741)). Qed.
Lemma lem5374245 (_69741 : int) : (term289 _69741) = (term307 _69741).
Proof. exact (TRANS (@lem5374142 _69741) (@lem5374244 _69741)). Qed.
Lemma lem5374246 (_69741 : int) : (term307 _69741) = term112.
Proof. exact (@lem1982719 (real_of_int _69741)). Qed.
Lemma lem5374247 (_69741 : int) : (term289 _69741) = term112.
Proof. exact (TRANS (@lem5374245 _69741) (@lem5374246 _69741)). Qed.
Lemma lem5374248 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5374249 (_69741 : int) : (term308 _69741) = term309.
Proof. exact (MK_COMB (@lem5374248) (@lem5374247 _69741)). Qed.
Lemma lem5374250 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem5374251 (_69741 : int) : (term359 _69741) = term314.
Proof. exact (MK_COMB (@lem5374249 _69741) (@lem5374250)). Qed.
Lemma lem5374252 (_69741 : int) : (term358 _69741) = term314.
Proof. exact (TRANS (@lem5374141 _69741) (@lem5374251 _69741)). Qed.
Lemma lem5374253 : term314 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem5374254 (_69741 : int) : (term358 _69741) = term157.
Proof. exact (TRANS (@lem5374252 _69741) (@lem5374253)). Qed.
Lemma lem5374255 (_69740 : int) (_69741 : int) : (term356 _69740 _69741) = term314.
Proof. exact (MK_COMB (@lem5374140 _69740) (@lem5374254 _69741)). Qed.
Lemma lem5374256 (_69740 : int) (_69741 : int) : (term355 _69740 _69741) = term314.
Proof. exact (TRANS (@lem5374032 _69740 _69741) (@lem5374255 _69740 _69741)). Qed.
Lemma lem5374257 : term314 = term157.
Proof. exact (@lem1982721 term157). Qed.
Lemma lem5374258 (_69740 : int) (_69741 : int) : (term355 _69740 _69741) = term157.
Proof. exact (TRANS (@lem5374256 _69740 _69741) (@lem5374257)). Qed.
Lemma lem5374259 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5374260 (_69740 : int) (_69741 : int) : (term360 _69740 _69741) = term316.
Proof. exact (MK_COMB (@lem5374259) (@lem5374258 _69740 _69741)). Qed.
Lemma lem5374261 : term112 = term112.
Proof. exact (eq_refl term112). Qed.
Lemma lem5374262 (_69740 : int) (_69741 : int) : (term354 _69740 _69741) = term317.
Proof. exact (MK_COMB (@lem5374260 _69740 _69741) (@lem5374261)). Qed.
Lemma lem5374263 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : term317.
Proof. exact (EQ_MP (@lem5374262 _69740 _69741) (@lem5374031 _69740 _69741 h1)). Qed.
Lemma lem5374265 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5374266 : term317 = term318.
Proof. exact (@lem5374265 term112 term157). Qed.
Lemma lem5374268 (x : nat) : (term155 x) = (term156 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5374269 : term157 = term158.
Proof. exact (@lem5374268 term126). Qed.
Lemma lem5374271 (x : nat) : (real_of_num x) = (term153 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5374272 : term112 = term154.
Proof. exact (@lem5374271 (NUMERAL 0)). Qed.
Lemma lem5374273 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5374274 : term114 = term319.
Proof. exact (MK_COMB (@lem5374273) (@lem5374272)). Qed.
Lemma lem5374275 : term318 = term320.
Proof. exact (MK_COMB (@lem5374274) (@lem5374269)). Qed.
Lemma lem5374276 : term321.
Proof. exact (@lem1980026 term112 term125 term157 term125). Qed.
Lemma lem5374278 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5374279 : term258 = term264.
Proof. exact (@lem5374278 (NUMERAL 0) term126). Qed.
Lemma lem5374280 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5374281 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5374282 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5374281 h1) (fun h1 : term264 = True => @lem5374280)). Qed.
Lemma lem5374283 : term264 = True.
Proof. exact (EQ_MP (@lem5374282) (@lem5374280)). Qed.
Lemma lem5374284 : term258 = True.
Proof. exact (TRANS (@lem5374279) (@lem5374283)). Qed.
Lemma lem5374285 : True = term258.
Proof. exact (SYM (@lem5374284)). Qed.
Lemma lem5374286 : term258.
Proof. exact (EQ_MP (@lem5374285) (@lem0)). Qed.
Lemma lem5374287 : term322.
Proof. exact (@lem5374276 (@lem5374286)). Qed.
Lemma lem5374289 (m : nat) (n : nat) : (term263 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5374290 : term258 = term264.
Proof. exact (@lem5374289 (NUMERAL 0) term126). Qed.
Lemma lem5374291 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5374292 (h1 : term265 = (BIT1 0)) : term264 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5374293 : (term265 = (BIT1 0)) = (term264 = True).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5374292 h1) (fun h1 : term264 = True => @lem5374291)). Qed.
Lemma lem5374294 : term264 = True.
Proof. exact (EQ_MP (@lem5374293) (@lem5374291)). Qed.
Lemma lem5374295 : term258 = True.
Proof. exact (TRANS (@lem5374290) (@lem5374294)). Qed.
Lemma lem5374296 : True = term258.
Proof. exact (SYM (@lem5374295)). Qed.
Lemma lem5374297 : term258.
Proof. exact (EQ_MP (@lem5374296) (@lem0)). Qed.
Lemma lem5374298 : term320 = term323.
Proof. exact (@lem5374287 (@lem5374297)). Qed.
Lemma lem5374300 (m : nat) (n : nat) : (term187 m n) = (term188 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5374301 : term184 = term189.
Proof. exact (@lem5374300 term126 term126). Qed.
Lemma lem5374302 : (term168 = (BIT1 0)) = (term169 = term126).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5374303 : term169 = term126.
Proof. exact (EQ_MP (@lem5374302) (@lem940073)). Qed.
Lemma lem5374304 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5374305 : term167 = term125.
Proof. exact (MK_COMB (@lem5374304) (@lem5374303)). Qed.
Lemma lem5374306 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5374307 : term189 = term157.
Proof. exact (MK_COMB (@lem5374306) (@lem5374305)). Qed.
Lemma lem5374308 : term184 = term157.
Proof. exact (TRANS (@lem5374301) (@lem5374307)). Qed.
Lemma lem5374310 (x : nat) : (term268 x) = term112.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5374311 : term269 = term112.
Proof. exact (@lem5374310 term126). Qed.
Lemma lem5374312 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5374313 : term324 = term114.
Proof. exact (MK_COMB (@lem5374312) (@lem5374311)). Qed.
Lemma lem5374314 : term323 = term318.
Proof. exact (MK_COMB (@lem5374313) (@lem5374308)). Qed.
Lemma lem5374316 (m : nat) (n : nat) : (term325 m n) = (term326 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5374317 : term318 = term327.
Proof. exact (@lem5374316 (NUMERAL 0) term126). Qed.
Lemma lem5374318 : term265 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5374319 (h1 : term265 = (BIT1 0)) : (term126 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5374320 : (term265 = (BIT1 0)) = ((term126 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term265 = (BIT1 0) => @lem5374319 h1) (fun h1 : (term126 = (NUMERAL 0)) = False => @lem5374318)). Qed.
Lemma lem5374321 : (term126 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5374320) (@lem5374318)). Qed.
Lemma lem5374322 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5374323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5374324 : term328 = (and True).
Proof. exact (MK_COMB (@lem5374323) (@lem5374322)). Qed.
Lemma lem5374325 : term327 = (True /\ False).
Proof. exact (MK_COMB (@lem5374324) (@lem5374321)). Qed.
Lemma lem5374327 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5374328 : term327 = False.
Proof. exact (TRANS (@lem5374325) (@lem5374327)). Qed.
Lemma lem5374329 : term318 = False.
Proof. exact (TRANS (@lem5374317) (@lem5374328)). Qed.
Lemma lem5374330 : term323 = False.
Proof. exact (TRANS (@lem5374314) (@lem5374329)). Qed.
Lemma lem5374331 : term320 = False.
Proof. exact (TRANS (@lem5374298) (@lem5374330)). Qed.
Lemma lem5374332 : term318 = False.
Proof. exact (TRANS (@lem5374275) (@lem5374331)). Qed.
Lemma lem5374333 : term317 = False.
Proof. exact (TRANS (@lem5374266) (@lem5374332)). Qed.
Lemma lem5374334 (_69740 : int) (_69741 : int) (h1 : term369 _69740 _69741) : False.
Proof. exact (EQ_MP (@lem5374333) (@lem5374263 _69740 _69741 h1)). Qed.
Lemma lem5374335 (_69740 : int) (_69741 : int) (h1 : term246 _69740 _69741) : False.
Proof. exact (or_elim (@lem5373404 _69740 _69741 h1) (fun h0 : term361 _69740 _69741 => @lem5373869 _69740 _69741 h0) (fun h0 : term369 _69740 _69741 => @lem5374334 _69740 _69741 h0)). Qed.
Lemma lem5374336 (_69740 : int) (_69741 : int) (h1 : term255 _69740 _69741) : False.
Proof. exact (or_elim (@lem5372549 _69740 _69741 h1) (fun h0 : term250 _69740 _69741 => @lem5373403 _69740 _69741 h0) (fun h0 : term246 _69740 _69741 => @lem5374335 _69740 _69741 h0)). Qed.
Lemma lem5374338 (_69740 : int) (_69741 : int) (h1 : term255 _69740 _69741) : term255 _69740 _69741.
Proof. exact (h1). Qed.
Lemma lem5374339 (_69740 : int) (_69741 : int) (h1 : term255 _69740 _69741) : (term255 _69740 _69741) = False.
Proof. exact (prop_ext (fun h2 : term255 _69740 _69741 => @lem5374336 _69740 _69741 h1) (fun h2 : False => @lem5374338 _69740 _69741 h1)). Qed.
Lemma lem5374340 (_69740 : int) (_69741 : int) (h1 : term255 _69740 _69741) : False.
Proof. exact (EQ_MP (@lem5374339 _69740 _69741 h1) (@lem5374338 _69740 _69741 h1)). Qed.
Lemma lem5374341 (_69740 : int) (_69741 : int) (h1 : term149 _69740 _69741) : term149 _69740 _69741.
Proof. exact (h1). Qed.
Lemma lem5374342 (_69740 : int) (_69741 : int) (h1 : term149 _69740 _69741) : term255 _69740 _69741.
Proof. exact (EQ_MP (@lem5372527 _69740 _69741) (@lem5374341 _69740 _69741 h1)). Qed.
Lemma lem5374343 (_69740 : int) (_69741 : int) (h1 : term149 _69740 _69741) : (term255 _69740 _69741) = False.
Proof. exact (prop_ext (fun h2 : term255 _69740 _69741 => @lem5374340 _69740 _69741 h2) (fun h2 : False => @lem5374342 _69740 _69741 h1)). Qed.
Lemma lem5374344 (_69740 : int) (_69741 : int) (h1 : term149 _69740 _69741) : False.
Proof. exact (EQ_MP (@lem5374343 _69740 _69741 h1) (@lem5374342 _69740 _69741 h1)). Qed.
Lemma lem5374345 (_69740 : int) (_69741 : int) : term377 _69740 _69741.
Proof. exact (fun h0 : term149 _69740 _69741 => @lem5374344 _69740 _69741 h0). Qed.
Lemma lem5374346 (_69740 : int) (_69741 : int) : term378 _69740 _69741.
Proof. exact (@lem1386578 (term379 _69740 _69741)). Qed.
Lemma lem5374349 (_69740 : int) (_69741 : int) : term379 _69740 _69741.
Proof. exact (@lem5374346 _69740 _69741 (@lem5374345 _69740 _69741)). Qed.
Lemma lem5374350 (_69741 : int) (_69740 : int) : (term147 _69740 _69741) = (term105 _69741 _69740).
Proof. exact (SYM (@lem5371885 _69740 _69741)). Qed.
Lemma lem5374351 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5374352 (_69741 : int) (_69740 : int) : (term379 _69740 _69741) = (term67 _69741 _69740).
Proof. exact (MK_COMB (@lem5374351) (@lem5374350 _69741 _69740)). Qed.
Lemma lem5374353 (_69741 : int) (_69740 : int) : term67 _69741 _69740.
Proof. exact (EQ_MP (@lem5374352 _69741 _69740) (@lem5374349 _69740 _69741)). Qed.
Lemma lem5374354 (_69741 : int) (_69740 : int) : term68 _69741 _69740.
Proof. exact (EQ_MP (@lem5371632 _69741 _69740) (@lem5374353 _69741 _69740)). Qed.
Lemma lem5374355 (x : nat) (n : nat) : term380 x n.
Proof. exact (@lem5374354 (int_of_num x) (int_of_num n)). Qed.
Lemma lem5374356 (x : nat) (n : nat) : term381 x n.
Proof. exact (@lem5374355 x n (@lem5371628 n)). Qed.
Lemma lem5374357 (x : nat) (n : nat) : term60 x n.
Proof. exact (@lem5374356 x n (@lem5371631 x)). Qed.
Lemma lem5374358 (n : nat) : term62 n.
Proof. exact (fun x : nat => @lem5374357 x n). Qed.
Lemma lem5374359 : term64.
Proof. exact (fun n : nat => @lem5374358 n). Qed.
Lemma lem5374360 : term64 = term28.
Proof. exact (SYM (@lem5371625)). Qed.
Lemma lem5374361 : term28.
Proof. exact (EQ_MP (@lem5374360) (@lem5374359)). Qed.
Lemma lem5374362 : term28 = (term28 = True).
Proof. exact (@lem7 term28). Qed.
Lemma lem5374363 : term28 = True.
Proof. exact (EQ_MP (@lem5374362) (@lem5374361)). Qed.
Lemma lem5374364 : True = term28.
Proof. exact (SYM (@lem5374363)). Qed.
Lemma lem5374365 : term28.
Proof. exact (EQ_MP (@lem5374364) (@lem0)). Qed.
Lemma lem5374366 : term27.
Proof. exact (EQ_MP (@lem5371416) (@lem5374365)). Qed.
