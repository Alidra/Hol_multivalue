Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_DIV_EQ_0_term_abbrevs.
Require Import CONJ_SYM_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FORALL_INT_CASES_spec.
Require Import INT_ABS_NEG_spec.
Require Import INT_ABS_NUM_spec.
Require Import INT_ADD_LID_spec.
Require Import INT_DIV_0_spec.
Require Import INT_DIV_LE_EQ_spec.
Require Import INT_DIV_RNEG_spec.
Require Import INT_LE_ANTISYM_spec.
Require Import INT_LE_DIV_EQ_spec.
Require Import INT_MUL_RID_spec.
Require Import INT_MUL_RZERO_spec.
Require Import INT_NEG_EQ_0_spec.
Require Import INT_OF_NUM_EQ_spec.
Require Import INT_OF_NUM_LT_spec.
Require Import LE_1_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem2625419 (x : int) (y : int) (h1 : (term0 y x) = (x = y)) : (term0 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem2625420 (x : int) (y : int) (h1 : (term0 y x) = (x = y)) : (x = y) = (term0 y x).
Proof. exact (SYM (@lem2625419 x y h1)). Qed.
Lemma lem2625421 (y : int) (x : int) (h1 : (x = y) = (term0 y x)) : (x = y) = (term0 y x).
Proof. exact (h1). Qed.
Lemma lem2625422 (y : int) (x : int) (h1 : (x = y) = (term0 y x)) : (term0 y x) = (x = y).
Proof. exact (SYM (@lem2625421 y x h1)). Qed.
Lemma lem2625423 (y : int) (x : int) : ((term0 y x) = (x = y)) = ((x = y) = (term0 y x)).
Proof. exact (prop_ext (fun h1 : (term0 y x) = (x = y) => @lem2625420 x y h1) (fun h1 : (x = y) = (term0 y x) => @lem2625422 y x h1)). Qed.
Lemma lem2625424 (x : int) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : int => @lem2625423 y x)). Qed.
Lemma lem2625425 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2625426 (x : int) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem2625425) (@lem2625424 x)). Qed.
Lemma lem2625427 : term5 = term6.
Proof. exact (fun_ext (fun x : int => @lem2625426 x)). Qed.
Lemma lem2625428 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2625429 : term7 = term8.
Proof. exact (MK_COMB (@lem2625428) (@lem2625427)). Qed.
Lemma lem2625430 : term8.
Proof. exact (EQ_MP (@lem2625429) (@lem2302347)). Qed.
Lemma lem2625431 (n : nat) : term9 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem2625432 (n : nat) : (term9 n) = (term10 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem2625433 (n : nat) : term10 n.
Proof. exact (EQ_MP (@lem2625432 n) (@lem2625431 n)). Qed.
Lemma lem2625435 (n : nat) (h1 : term11 n) : term11 n.
Proof. exact (h1). Qed.
Lemma lem2625436 (x : int) : term12 x.
Proof. exact (@lem2300452 x). Qed.
Lemma lem2625437 (x : int) : (term12 x) = ((term13 x) = (int_abs x)).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem2625439 (x : int) : term14 x.
Proof. exact (@lem2306427 x). Qed.
Lemma lem2625440 (x : int) : (term14 x) = (((int_neg x) = term15) = (x = term15)).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem2625442 (m : int) : term16 m.
Proof. exact (@lem2519806 m). Qed.
Lemma lem2625443 (m : int) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem2625444 (m : int) : term17 m.
Proof. exact (EQ_MP (@lem2625443 m) (@lem2625442 m)). Qed.
Lemma lem2625445 (m : int) (n : int) : term18 m n.
Proof. exact (@lem2625444 m n). Qed.
Lemma lem2625446 (m : int) (n : int) : (term18 m n) = ((term19 m n) = (term20 m n)).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem2625448 (P : int -> Prop) : term21 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem2625449 (P : int -> Prop) : (term21 P) = ((term22 P) = (term23 P)).
Proof. exact (eq_refl (term21 P)). Qed.
Lemma lem2625452 (P : int -> Prop) : (term22 P) = (term23 P).
Proof. exact (EQ_MP (@lem2625449 P) (@lem2625448 P)). Qed.
Lemma lem2625453 (m : int) : (term24 m) = (term25 m).
Proof. exact (@lem2625452 (term26 m)). Qed.
Lemma lem2625454 (m : int) (n : int) : (term27 m n) = (((div m n) = term15) = (term28 m n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem2625455 (m : int) : (term29 m) = (term26 m).
Proof. exact (fun_ext (fun n : int => @lem2625454 m n)). Qed.
Lemma lem2625456 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2625457 (m : int) : (term24 m) = (term30 m).
Proof. exact (MK_COMB (@lem2625456) (@lem2625455 m)). Qed.
Lemma lem2625458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2625459 (m : int) : (term31 m) = (term32 m).
Proof. exact (MK_COMB (@lem2625458) (@lem2625457 m)). Qed.
Lemma lem2625460 (m : int) (n : nat) : (term33 m n) = (((term34 m n) = term15) = (term35 m n)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem2625461 (m : int) : (term36 m) = (term37 m).
Proof. exact (fun_ext (fun n : nat => @lem2625460 m n)). Qed.
Lemma lem2625462 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2625463 (m : int) : (term38 m) = (term39 m).
Proof. exact (MK_COMB (@lem2625462) (@lem2625461 m)). Qed.
Lemma lem2625464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2625465 (m : int) : (term40 m) = (term41 m).
Proof. exact (MK_COMB (@lem2625464) (@lem2625463 m)). Qed.
Lemma lem2625466 (m : int) (n : nat) : (term42 m n) = (((term43 m n) = term15) = (term44 m n)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem2625467 (m : int) : (term45 m) = (term46 m).
Proof. exact (fun_ext (fun n : nat => @lem2625466 m n)). Qed.
Lemma lem2625468 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2625469 (m : int) : (term47 m) = (term48 m).
Proof. exact (MK_COMB (@lem2625468) (@lem2625467 m)). Qed.
Lemma lem2625470 (m : int) : (term25 m) = (term49 m).
Proof. exact (MK_COMB (@lem2625465 m) (@lem2625469 m)). Qed.
Lemma lem2625471 (m : int) : ((term24 m) = (term25 m)) = ((term30 m) = (term49 m)).
Proof. exact (MK_COMB (@lem2625459 m) (@lem2625470 m)). Qed.
Lemma lem2625472 (m : int) : (term30 m) = (term49 m).
Proof. exact (EQ_MP (@lem2625471 m) (@lem2625453 m)). Qed.
Lemma lem2625473 : term50 = term51.
Proof. exact (fun_ext (fun m : int => @lem2625472 m)). Qed.
Lemma lem2625474 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2625475 : term52 = term53.
Proof. exact (MK_COMB (@lem2625474) (@lem2625473)). Qed.
Lemma lem2625476 : term53 = term52.
Proof. exact (SYM (@lem2625475)). Qed.
Lemma lem2625506 (m : int) (n : int) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem2625446 m n) (@lem2625445 m n)). Qed.
Lemma lem2625507 (m : int) (n : nat) : (term43 m n) = (term54 m n).
Proof. exact (@lem2625506 m (int_of_num n)). Qed.
Lemma lem2625508 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2625509 (m : int) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem2625508) (@lem2625507 m n)). Qed.
Lemma lem2625510 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem2625511 (m : int) (n : nat) : ((term43 m n) = term15) = ((term54 m n) = term15).
Proof. exact (MK_COMB (@lem2625509 m n) (@lem2625510)). Qed.
Lemma lem2625513 (x : int) : ((int_neg x) = term15) = (x = term15).
Proof. exact (EQ_MP (@lem2625440 x) (@lem2625439 x)). Qed.
Lemma lem2625514 (m : int) (n : nat) : ((term54 m n) = term15) = ((term34 m n) = term15).
Proof. exact (@lem2625513 (term34 m n)). Qed.
Lemma lem2625517 (m : int) (n : nat) : ((term43 m n) = term15) = ((term34 m n) = term15).
Proof. exact (TRANS (@lem2625511 m n) (@lem2625514 m n)). Qed.
Lemma lem2625518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2625519 (m : int) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem2625518) (@lem2625517 m n)). Qed.
Lemma lem2625523 (x : int) : ((int_neg x) = term15) = (x = term15).
Proof. exact (EQ_MP (@lem2625440 x) (@lem2625439 x)). Qed.
Lemma lem2625524 (n : nat) : ((term59 n) = term15) = ((int_of_num n) = term15).
Proof. exact (@lem2625523 (int_of_num n)). Qed.
Lemma lem2625527 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2625528 (n : nat) : (term60 n) = (term61 n).
Proof. exact (MK_COMB (@lem2625527) (@lem2625524 n)). Qed.
Lemma lem2625532 (x : int) : (term13 x) = (int_abs x).
Proof. exact (EQ_MP (@lem2625437 x) (@lem2625436 x)). Qed.
Lemma lem2625533 (n : nat) : (term62 n) = (term63 n).
Proof. exact (@lem2625532 (int_of_num n)). Qed.
Lemma lem2625534 (m : int) : (int_lt m) = (int_lt m).
Proof. exact (eq_refl (int_lt m)). Qed.
Lemma lem2625535 (m : int) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem2625534 m) (@lem2625533 n)). Qed.
Lemma lem2625536 (m : int) : (term66 m) = (term66 m).
Proof. exact (eq_refl (term66 m)). Qed.
Lemma lem2625537 (m : int) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (MK_COMB (@lem2625536 m) (@lem2625535 m n)). Qed.
Lemma lem2625540 (m : int) (n : nat) : (term44 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem2625528 n) (@lem2625537 m n)). Qed.
Lemma lem2625543 (m : int) (n : nat) : (((term43 m n) = term15) = (term44 m n)) = (((term34 m n) = term15) = (term35 m n)).
Proof. exact (MK_COMB (@lem2625519 m n) (@lem2625540 m n)). Qed.
Lemma lem2625546 (m : int) : (term46 m) = (term37 m).
Proof. exact (fun_ext (fun n : nat => @lem2625543 m n)). Qed.
Lemma lem2625547 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2625548 (m : int) : (term48 m) = (term39 m).
Proof. exact (MK_COMB (@lem2625547) (@lem2625546 m)). Qed.
Lemma lem2625553 (m : int) : (term41 m) = (term41 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem2625554 (m : int) : (term49 m) = (term69 m).
Proof. exact (MK_COMB (@lem2625553 m) (@lem2625548 m)). Qed.
Lemma lem2625556 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem2625557 (m : int) : (term69 m) = (term39 m).
Proof. exact (@lem2625556 (term39 m)). Qed.
Lemma lem2625572 (m : int) : (term49 m) = (term39 m).
Proof. exact (TRANS (@lem2625554 m) (@lem2625557 m)). Qed.
Lemma lem2625573 : term51 = term70.
Proof. exact (fun_ext (fun m : int => @lem2625572 m)). Qed.
Lemma lem2625574 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2625575 : term53 = term71.
Proof. exact (MK_COMB (@lem2625574) (@lem2625573)). Qed.
Lemma lem2625580 : term71 = term53.
Proof. exact (SYM (@lem2625575)). Qed.
Lemma lem2625581 (n : nat) : term72 n.
Proof. exact (@lem2300474 n). Qed.
Lemma lem2625582 (n : nat) : (term72 n) = ((term63 n) = (int_of_num n)).
Proof. exact (eq_refl (term72 n)). Qed.
Lemma lem2625584 (m : nat) : term73 m.
Proof. exact (@lem2307147 m). Qed.
Lemma lem2625585 (m : nat) : (term73 m) = (term74 m).
Proof. exact (eq_refl (term73 m)). Qed.
Lemma lem2625586 (m : nat) : term74 m.
Proof. exact (EQ_MP (@lem2625585 m) (@lem2625584 m)). Qed.
Lemma lem2625587 (m : nat) (n : nat) : term75 m n.
Proof. exact (@lem2625586 m n). Qed.
Lemma lem2625588 (m : nat) (n : nat) : (term75 m n) = (((int_of_num m) = (int_of_num n)) = (m = n)).
Proof. exact (eq_refl (term75 m n)). Qed.
Lemma lem2625590 (m : int) : term76 m.
Proof. exact (@lem2395867 m). Qed.
Lemma lem2625591 (m : int) : (term76 m) = ((term77 m) = term15).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem2625598 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem2625599 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2625600 (n : nat) (h1 : n = (NUMERAL 0)) : (int_of_num n) = term15.
Proof. exact (MK_COMB (@lem2625599) (@lem2625598 n h1)). Qed.
Lemma lem2625601 (m : int) : (div m) = (div m).
Proof. exact (eq_refl (div m)). Qed.
Lemma lem2625602 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term34 m n) = (term77 m).
Proof. exact (MK_COMB (@lem2625601 m) (@lem2625600 n h1)). Qed.
Lemma lem2625604 (m : int) : (term77 m) = term15.
Proof. exact (EQ_MP (@lem2625591 m) (@lem2625590 m)). Qed.
Lemma lem2625605 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term34 m n) = term15.
Proof. exact (TRANS (@lem2625602 m n h1) (@lem2625604 m)). Qed.
Lemma lem2625606 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2625607 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term78 m n) = term79.
Proof. exact (MK_COMB (@lem2625606) (@lem2625605 m n h1)). Qed.
Lemma lem2625608 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem2625609 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : ((term34 m n) = term15) = (term15 = term15).
Proof. exact (MK_COMB (@lem2625607 m n h1) (@lem2625608)). Qed.
Lemma lem2625611 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2625588 m n) (@lem2625587 m n)). Qed.
Lemma lem2625612 : (term15 = term15) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem2625611 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2625614 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2625615 (x : nat) : (x = x) = True.
Proof. exact (@lem2625614 nat x). Qed.
Lemma lem2625616 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem2625615 (NUMERAL 0)). Qed.
Lemma lem2625617 : (term15 = term15) = True.
Proof. exact (TRANS (@lem2625612) (@lem2625616)). Qed.
Lemma lem2625618 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : ((term34 m n) = term15) = True.
Proof. exact (TRANS (@lem2625609 m n h1) (@lem2625617)). Qed.
Lemma lem2625619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2625620 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term58 m n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem2625619) (@lem2625618 m n h1)). Qed.
Lemma lem2625624 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2625588 m n) (@lem2625587 m n)). Qed.
Lemma lem2625625 (n : nat) : ((int_of_num n) = term15) = (n = (NUMERAL 0)).
Proof. exact (@lem2625624 n (NUMERAL 0)). Qed.
Lemma lem2625629 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem2625630 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem2625631 (n : nat) (h1 : n = (NUMERAL 0)) : (@eq nat n) = term80.
Proof. exact (MK_COMB (@lem2625630) (@lem2625629 n h1)). Qed.
Lemma lem2625632 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem2625633 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem2625631 n h1) (@lem2625632)). Qed.
Lemma lem2625635 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2625636 (x : nat) : (x = x) = True.
Proof. exact (@lem2625635 nat x). Qed.
Lemma lem2625637 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem2625636 (NUMERAL 0)). Qed.
Lemma lem2625638 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem2625633 n h1) (@lem2625637)). Qed.
Lemma lem2625639 (n : nat) (h1 : n = (NUMERAL 0)) : ((int_of_num n) = term15) = True.
Proof. exact (TRANS (@lem2625625 n) (@lem2625638 n h1)). Qed.
Lemma lem2625640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2625641 (n : nat) (h1 : n = (NUMERAL 0)) : (term61 n) = (or True).
Proof. exact (MK_COMB (@lem2625640) (@lem2625639 n h1)). Qed.
Lemma lem2625645 (n : nat) : (term63 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2625582 n) (@lem2625581 n)). Qed.
Lemma lem2625647 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem2625648 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2625649 (n : nat) (h1 : n = (NUMERAL 0)) : (int_of_num n) = term15.
Proof. exact (MK_COMB (@lem2625648) (@lem2625647 n h1)). Qed.
Lemma lem2625650 (n : nat) (h1 : n = (NUMERAL 0)) : (term63 n) = term15.
Proof. exact (TRANS (@lem2625645 n) (@lem2625649 n h1)). Qed.
Lemma lem2625651 (m : int) : (int_lt m) = (int_lt m).
Proof. exact (eq_refl (int_lt m)). Qed.
Lemma lem2625652 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term65 m n) = (term81 m).
Proof. exact (MK_COMB (@lem2625651 m) (@lem2625650 n h1)). Qed.
Lemma lem2625653 (m : int) : (term66 m) = (term66 m).
Proof. exact (eq_refl (term66 m)). Qed.
Lemma lem2625654 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term68 m n) = (term82 m).
Proof. exact (MK_COMB (@lem2625653 m) (@lem2625652 m n h1)). Qed.
Lemma lem2625657 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term35 m n) = (term83 m).
Proof. exact (MK_COMB (@lem2625641 n h1) (@lem2625654 m n h1)). Qed.
Lemma lem2625659 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2625660 (m : int) : (term83 m) = True.
Proof. exact (@lem2625659 (term82 m)). Qed.
Lemma lem2625661 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (term35 m n) = True.
Proof. exact (TRANS (@lem2625657 m n h1) (@lem2625660 m)). Qed.
Lemma lem2625662 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (((term34 m n) = term15) = (term35 m n)) = (True = True).
Proof. exact (MK_COMB (@lem2625620 m n h1) (@lem2625661 m n h1)). Qed.
Lemma lem2625664 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2625665 : (True = True) = True.
Proof. exact (@lem2625664 True). Qed.
Lemma lem2625666 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : (((term34 m n) = term15) = (term35 m n)) = True.
Proof. exact (TRANS (@lem2625662 m n h1) (@lem2625665)). Qed.
Lemma lem2625667 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : True = (((term34 m n) = term15) = (term35 m n)).
Proof. exact (SYM (@lem2625666 m n h1)). Qed.
Lemma lem2625668 (m : int) (n : nat) (h1 : n = (NUMERAL 0)) : ((term34 m n) = term15) = (term35 m n).
Proof. exact (EQ_MP (@lem2625667 m n h1) (@lem0)). Qed.
Lemma lem2625669 (n : nat) : term72 n.
Proof. exact (@lem2300474 n). Qed.
Lemma lem2625670 (n : nat) : (term72 n) = ((term63 n) = (int_of_num n)).
Proof. exact (eq_refl (term72 n)). Qed.
Lemma lem2625672 (m : nat) : term73 m.
Proof. exact (@lem2307147 m). Qed.
Lemma lem2625673 (m : nat) : (term73 m) = (term74 m).
Proof. exact (eq_refl (term73 m)). Qed.
Lemma lem2625674 (m : nat) : term74 m.
Proof. exact (EQ_MP (@lem2625673 m) (@lem2625672 m)). Qed.
Lemma lem2625675 (m : nat) (n : nat) : term75 m n.
Proof. exact (@lem2625674 m n). Qed.
Lemma lem2625676 (m : nat) (n : nat) : (term75 m n) = (((int_of_num m) = (int_of_num n)) = (m = n)).
Proof. exact (eq_refl (term75 m n)). Qed.
Lemma lem2625681 (n : nat) : term84 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem2625701 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2625676 m n) (@lem2625675 m n)). Qed.
Lemma lem2625702 (n : nat) : ((int_of_num n) = term15) = (n = (NUMERAL 0)).
Proof. exact (@lem2625701 n (NUMERAL 0)). Qed.
Lemma lem2625704 (n : nat) (h1 : term11 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem2625681 n (@lem2625435 n h1)). Qed.
Lemma lem2625705 (n : nat) (h1 : term11 n) : ((int_of_num n) = term15) = False.
Proof. exact (TRANS (@lem2625702 n) (@lem2625704 n h1)). Qed.
Lemma lem2625706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2625707 (n : nat) (h1 : term11 n) : (term61 n) = (or False).
Proof. exact (MK_COMB (@lem2625706) (@lem2625705 n h1)). Qed.
Lemma lem2625711 (n : nat) : (term63 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2625670 n) (@lem2625669 n)). Qed.
Lemma lem2625712 (m : int) : (int_lt m) = (int_lt m).
Proof. exact (eq_refl (int_lt m)). Qed.
Lemma lem2625713 (m : int) (n : nat) : (term65 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem2625712 m) (@lem2625711 n)). Qed.
Lemma lem2625714 (m : int) : (term66 m) = (term66 m).
Proof. exact (eq_refl (term66 m)). Qed.
Lemma lem2625715 (m : int) (n : nat) : (term68 m n) = (term86 m n).
Proof. exact (MK_COMB (@lem2625714 m) (@lem2625713 m n)). Qed.
Lemma lem2625718 (m : int) (n : nat) (h1 : term11 n) : (term35 m n) = (term87 m n).
Proof. exact (MK_COMB (@lem2625707 n h1) (@lem2625715 m n)). Qed.
Lemma lem2625720 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem2625721 (m : int) (n : nat) : (term87 m n) = (term86 m n).
Proof. exact (@lem2625720 (term86 m n)). Qed.
Lemma lem2625724 (m : int) (n : nat) (h1 : term11 n) : (term35 m n) = (term86 m n).
Proof. exact (TRANS (@lem2625718 m n h1) (@lem2625721 m n)). Qed.
Lemma lem2625725 (m : int) (n : nat) : (term58 m n) = (term58 m n).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem2625726 (m : int) (n : nat) (h1 : term11 n) : (((term34 m n) = term15) = (term35 m n)) = (((term34 m n) = term15) = (term86 m n)).
Proof. exact (MK_COMB (@lem2625725 m n) (@lem2625724 m n h1)). Qed.
Lemma lem2625729 (m : int) (n : nat) (h1 : term11 n) : (((term34 m n) = term15) = (term86 m n)) = (((term34 m n) = term15) = (term35 m n)).
Proof. exact (SYM (@lem2625726 m n h1)). Qed.
Lemma lem2625730 (x : int) : term88 x.
Proof. exact (@lem2306233 x). Qed.
Lemma lem2625731 (x : int) : (term88 x) = ((term89 x) = x).
Proof. exact (eq_refl (term88 x)). Qed.
Lemma lem2625733 (x : int) : term90 x.
Proof. exact (@lem2306290 x). Qed.
Lemma lem2625734 (x : int) : (term90 x) = ((term91 x) = term15).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem2625736 (x : int) : term92 x.
Proof. exact (@lem2301132 x). Qed.
Lemma lem2625737 (x : int) : (term92 x) = ((term93 x) = x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem2625739 : term94.
Proof. exact (proj2 (@lem99082)). Qed.
Lemma lem2625740 : term95.
Proof. exact (proj2 (@lem2625739)). Qed.
Lemma lem2625741 : term96.
Proof. exact (proj2 (@lem2625740)). Qed.
Lemma lem2625742 : term97.
Proof. exact (proj2 (@lem2625741)). Qed.
Lemma lem2625772 : term98.
Proof. exact (proj1 (@lem2625742)). Qed.
Lemma lem2625773 (n : nat) : term99 n.
Proof. exact (@lem2625772 n). Qed.
Lemma lem2625774 (n : nat) : (term99 n) = (term100 n).
Proof. exact (eq_refl (term99 n)). Qed.
Lemma lem2625775 (n : nat) : term100 n.
Proof. exact (EQ_MP (@lem2625774 n) (@lem2625773 n)). Qed.
Lemma lem2625776 (n : nat) (h1 : term101 n) : term101 n.
Proof. exact (h1). Qed.
Lemma lem2625777 (n : nat) (h1 : term101 n) : term102 n.
Proof. exact (@lem2625775 n (@lem2625776 n h1)). Qed.
Lemma lem2625778 (n : nat) : (term102 n) = ((term102 n) = True).
Proof. exact (@lem7 (term102 n)). Qed.
Lemma lem2625779 (n : nat) (h1 : term101 n) : (term102 n) = True.
Proof. exact (EQ_MP (@lem2625778 n) (@lem2625777 n h1)). Qed.
Lemma lem2625827 : term103.
Proof. exact (proj1 (@lem2625739)). Qed.
Lemma lem2625828 (n : nat) : term104 n.
Proof. exact (@lem2625827 n). Qed.
Lemma lem2625829 (n : nat) : (term104 n) = (term105 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2625830 (n : nat) : term105 n.
Proof. exact (EQ_MP (@lem2625829 n) (@lem2625828 n)). Qed.
Lemma lem2625831 (n : nat) (h1 : term11 n) : term11 n.
Proof. exact (h1). Qed.
Lemma lem2625832 (n : nat) (h1 : term11 n) : term101 n.
Proof. exact (@lem2625830 n (@lem2625831 n h1)). Qed.
Lemma lem2625833 (n : nat) : (term101 n) = ((term101 n) = True).
Proof. exact (@lem7 (term101 n)). Qed.
Lemma lem2625834 (n : nat) (h1 : term11 n) : (term101 n) = True.
Proof. exact (EQ_MP (@lem2625833 n) (@lem2625832 n h1)). Qed.
Lemma lem2625853 (m : nat) : term106 m.
Proof. exact (@lem2307247 m). Qed.
Lemma lem2625854 (m : nat) : (term106 m) = (term107 m).
Proof. exact (eq_refl (term106 m)). Qed.
Lemma lem2625855 (m : nat) : term107 m.
Proof. exact (EQ_MP (@lem2625854 m) (@lem2625853 m)). Qed.
Lemma lem2625856 (m : nat) (n : nat) : term108 m n.
Proof. exact (@lem2625855 m n). Qed.
Lemma lem2625857 (m : nat) (n : nat) : (term108 m n) = ((term109 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term108 m n)). Qed.
Lemma lem2625859 (t1 : Prop) : term110 t1.
Proof. exact (@lem539 t1). Qed.
Lemma lem2625860 (t1 : Prop) : (term110 t1) = (term111 t1).
Proof. exact (eq_refl (term110 t1)). Qed.
Lemma lem2625861 (t1 : Prop) : term111 t1.
Proof. exact (EQ_MP (@lem2625860 t1) (@lem2625859 t1)). Qed.
Lemma lem2625862 (t1 : Prop) (t2 : Prop) : term112 t1 t2.
Proof. exact (@lem2625861 t1 t2). Qed.
Lemma lem2625863 (t2 : Prop) (t1 : Prop) : (term112 t1 t2) = ((t1 /\ t2) = (t2 /\ t1)).
Proof. exact (eq_refl (term112 t1 t2)). Qed.
Lemma lem2625865 (a : int) : term113 a.
Proof. exact (@lem2611393 a). Qed.
Lemma lem2625866 (a : int) : (term113 a) = (term114 a).
Proof. exact (eq_refl (term113 a)). Qed.
Lemma lem2625867 (a : int) : term114 a.
Proof. exact (EQ_MP (@lem2625866 a) (@lem2625865 a)). Qed.
Lemma lem2625868 (a : int) (b : int) : term115 a b.
Proof. exact (@lem2625867 a b). Qed.
Lemma lem2625869 (a : int) (b : int) : (term115 a b) = (term116 a b).
Proof. exact (eq_refl (term115 a b)). Qed.
Lemma lem2625870 (a : int) (b : int) : term116 a b.
Proof. exact (EQ_MP (@lem2625869 a b) (@lem2625868 a b)). Qed.
Lemma lem2625871 (a : int) (b : int) (c : int) : term117 a b c.
Proof. exact (@lem2625870 a b c). Qed.
Lemma lem2625872 (a : int) (c : int) (b : int) : (term117 a b c) = (term118 a c b).
Proof. exact (eq_refl (term117 a b c)). Qed.
Lemma lem2625873 (a : int) (c : int) (b : int) : term118 a c b.
Proof. exact (EQ_MP (@lem2625872 a c b) (@lem2625871 a b c)). Qed.
Lemma lem2625874 (a : int) (h1 : term119 a) : term119 a.
Proof. exact (h1). Qed.
Lemma lem2625875 (c : int) (b : int) (a : int) (h1 : term119 a) : (term120 c b a) = (term121 a c b).
Proof. exact (@lem2625873 a c b (@lem2625874 a h1)). Qed.
Lemma lem2625881 (a : int) : term122 a.
Proof. exact (@lem2611502 a). Qed.
Lemma lem2625882 (a : int) : (term122 a) = (term123 a).
Proof. exact (eq_refl (term122 a)). Qed.
Lemma lem2625883 (a : int) : term123 a.
Proof. exact (EQ_MP (@lem2625882 a) (@lem2625881 a)). Qed.
Lemma lem2625884 (a : int) (b : int) : term124 a b.
Proof. exact (@lem2625883 a b). Qed.
Lemma lem2625885 (b : int) (a : int) : (term124 a b) = (term125 b a).
Proof. exact (eq_refl (term124 a b)). Qed.
Lemma lem2625886 (b : int) (a : int) : term125 b a.
Proof. exact (EQ_MP (@lem2625885 b a) (@lem2625884 a b)). Qed.
Lemma lem2625887 (b : int) (a : int) (c : int) : term126 b a c.
Proof. exact (@lem2625886 b a c). Qed.
Lemma lem2625888 (b : int) (a : int) (c : int) : (term126 b a c) = (term127 b a c).
Proof. exact (eq_refl (term126 b a c)). Qed.
Lemma lem2625889 (b : int) (a : int) (c : int) : term127 b a c.
Proof. exact (EQ_MP (@lem2625888 b a c) (@lem2625887 b a c)). Qed.
Lemma lem2625890 (a : int) (h1 : term119 a) : term119 a.
Proof. exact (h1). Qed.
Lemma lem2625891 (b : int) (c : int) (a : int) (h1 : term119 a) : (term128 b a c) = (term129 b a c).
Proof. exact (@lem2625889 b a c (@lem2625890 a h1)). Qed.
Lemma lem2625897 (x : int) : term130 x.
Proof. exact (@lem2625430 x). Qed.
Lemma lem2625898 (x : int) : (term130 x) = (term4 x).
Proof. exact (eq_refl (term130 x)). Qed.
Lemma lem2625899 (x : int) : term4 x.
Proof. exact (EQ_MP (@lem2625898 x) (@lem2625897 x)). Qed.
Lemma lem2625900 (x : int) (y : int) : term131 x y.
Proof. exact (@lem2625899 x y). Qed.
Lemma lem2625901 (y : int) (x : int) : (term131 x y) = ((x = y) = (term0 y x)).
Proof. exact (eq_refl (term131 x y)). Qed.
Lemma lem2625903 (n : nat) : term84 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem2625923 (y : int) (x : int) : (x = y) = (term0 y x).
Proof. exact (EQ_MP (@lem2625901 y x) (@lem2625900 x y)). Qed.
Lemma lem2625924 (m : int) (n : nat) : ((term34 m n) = term15) = (term132 m n).
Proof. exact (@lem2625923 term15 (term34 m n)). Qed.
Lemma lem2625931 (b : int) (a : int) (c : int) : term127 b a c.
Proof. exact (fun h0 : term119 a => @lem2625891 b c a h0). Qed.
Lemma lem2625932 (m : int) (n : nat) : term133 m n.
Proof. exact (@lem2625931 m (int_of_num n) term15). Qed.
Lemma lem2625934 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2625857 m n) (@lem2625856 m n)). Qed.
Lemma lem2625935 (n : nat) : (term134 n) = (term102 n).
Proof. exact (@lem2625934 (NUMERAL 0) n). Qed.
Lemma lem2625937 (n : nat) : term135 n.
Proof. exact (fun h0 : term101 n => @lem2625779 n h0). Qed.
Lemma lem2625947 (n : nat) : term136 n.
Proof. exact (fun h0 : term11 n => @lem2625834 n h0). Qed.
Lemma lem2625949 (n : nat) (h1 : term11 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem2625903 n (@lem2625435 n h1)). Qed.
Lemma lem2625950 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2625951 (n : nat) (h1 : term11 n) : (term11 n) = (~ False).
Proof. exact (MK_COMB (@lem2625950) (@lem2625949 n h1)). Qed.
Lemma lem2625953 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2625954 (n : nat) (h1 : term11 n) : (term11 n) = True.
Proof. exact (TRANS (@lem2625951 n h1) (@lem2625953)). Qed.
Lemma lem2625955 (n : nat) (h1 : term11 n) : True = (term11 n).
Proof. exact (SYM (@lem2625954 n h1)). Qed.
Lemma lem2625956 (n : nat) (h1 : term11 n) : term11 n.
Proof. exact (EQ_MP (@lem2625955 n h1) (@lem0)). Qed.
Lemma lem2625957 (n : nat) (h1 : term11 n) : (term101 n) = True.
Proof. exact (@lem2625947 n (@lem2625956 n h1)). Qed.
Lemma lem2625958 (n : nat) (h1 : term11 n) : True = (term101 n).
Proof. exact (SYM (@lem2625957 n h1)). Qed.
Lemma lem2625959 (n : nat) (h1 : term11 n) : term101 n.
Proof. exact (EQ_MP (@lem2625958 n h1) (@lem0)). Qed.
Lemma lem2625960 (n : nat) (h1 : term11 n) : (term102 n) = True.
Proof. exact (@lem2625937 n (@lem2625959 n h1)). Qed.
Lemma lem2625961 (n : nat) (h1 : term11 n) : (term134 n) = True.
Proof. exact (TRANS (@lem2625935 n) (@lem2625960 n h1)). Qed.
Lemma lem2625962 (n : nat) (h1 : term11 n) : True = (term134 n).
Proof. exact (SYM (@lem2625961 n h1)). Qed.
Lemma lem2625963 (n : nat) (h1 : term11 n) : term134 n.
Proof. exact (EQ_MP (@lem2625962 n h1) (@lem0)). Qed.
Lemma lem2625964 (m : int) (n : nat) (h1 : term11 n) : (term137 m n) = (term138 m n).
Proof. exact (@lem2625932 m n (@lem2625963 n h1)). Qed.
Lemma lem2625966 (x : int) : (term93 x) = x.
Proof. exact (EQ_MP (@lem2625737 x) (@lem2625736 x)). Qed.
Lemma lem2625967 : term139 = term140.
Proof. exact (@lem2625966 term140). Qed.
Lemma lem2625968 (n : nat) : (term141 n) = (term141 n).
Proof. exact (eq_refl (term141 n)). Qed.
Lemma lem2625969 (n : nat) : (term142 n) = (term143 n).
Proof. exact (MK_COMB (@lem2625968 n) (@lem2625967)). Qed.
Lemma lem2625971 (x : int) : (term89 x) = x.
Proof. exact (EQ_MP (@lem2625731 x) (@lem2625730 x)). Qed.
Lemma lem2625972 (n : nat) : (term143 n) = (int_of_num n).
Proof. exact (@lem2625971 (int_of_num n)). Qed.
Lemma lem2625973 (n : nat) : (term142 n) = (int_of_num n).
Proof. exact (TRANS (@lem2625969 n) (@lem2625972 n)). Qed.
Lemma lem2625974 (m : int) : (int_lt m) = (int_lt m).
Proof. exact (eq_refl (int_lt m)). Qed.
Lemma lem2625975 (m : int) (n : nat) : (term138 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem2625974 m) (@lem2625973 n)). Qed.
Lemma lem2625976 (m : int) (n : nat) (h1 : term11 n) : (term137 m n) = (term85 m n).
Proof. exact (TRANS (@lem2625964 m n h1) (@lem2625975 m n)). Qed.
Lemma lem2625977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2625978 (m : int) (n : nat) (h1 : term11 n) : (term144 m n) = (term145 m n).
Proof. exact (MK_COMB (@lem2625977) (@lem2625976 m n h1)). Qed.
Lemma lem2625980 (a : int) (c : int) (b : int) : term118 a c b.
Proof. exact (fun h0 : term119 a => @lem2625875 c b a h0). Qed.
Lemma lem2625981 (n : nat) (m : int) : term146 n m.
Proof. exact (@lem2625980 (int_of_num n) term15 m). Qed.
Lemma lem2625983 (m : nat) (n : nat) : (term109 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2625857 m n) (@lem2625856 m n)). Qed.
Lemma lem2625984 (n : nat) : (term134 n) = (term102 n).
Proof. exact (@lem2625983 (NUMERAL 0) n). Qed.
Lemma lem2625986 (n : nat) : term135 n.
Proof. exact (fun h0 : term101 n => @lem2625779 n h0). Qed.
Lemma lem2625996 (n : nat) : term136 n.
Proof. exact (fun h0 : term11 n => @lem2625834 n h0). Qed.
Lemma lem2625998 (n : nat) (h1 : term11 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem2625903 n (@lem2625435 n h1)). Qed.
Lemma lem2625999 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2626000 (n : nat) (h1 : term11 n) : (term11 n) = (~ False).
Proof. exact (MK_COMB (@lem2625999) (@lem2625998 n h1)). Qed.
Lemma lem2626002 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2626003 (n : nat) (h1 : term11 n) : (term11 n) = True.
Proof. exact (TRANS (@lem2626000 n h1) (@lem2626002)). Qed.
Lemma lem2626004 (n : nat) (h1 : term11 n) : True = (term11 n).
Proof. exact (SYM (@lem2626003 n h1)). Qed.
Lemma lem2626005 (n : nat) (h1 : term11 n) : term11 n.
Proof. exact (EQ_MP (@lem2626004 n h1) (@lem0)). Qed.
Lemma lem2626006 (n : nat) (h1 : term11 n) : (term101 n) = True.
Proof. exact (@lem2625996 n (@lem2626005 n h1)). Qed.
Lemma lem2626007 (n : nat) (h1 : term11 n) : True = (term101 n).
Proof. exact (SYM (@lem2626006 n h1)). Qed.
Lemma lem2626008 (n : nat) (h1 : term11 n) : term101 n.
Proof. exact (EQ_MP (@lem2626007 n h1) (@lem0)). Qed.
Lemma lem2626009 (n : nat) (h1 : term11 n) : (term102 n) = True.
Proof. exact (@lem2625986 n (@lem2626008 n h1)). Qed.
Lemma lem2626010 (n : nat) (h1 : term11 n) : (term134 n) = True.
Proof. exact (TRANS (@lem2625984 n) (@lem2626009 n h1)). Qed.
Lemma lem2626011 (n : nat) (h1 : term11 n) : True = (term134 n).
Proof. exact (SYM (@lem2626010 n h1)). Qed.
Lemma lem2626012 (n : nat) (h1 : term11 n) : term134 n.
Proof. exact (EQ_MP (@lem2626011 n h1) (@lem0)). Qed.
Lemma lem2626013 (m : int) (n : nat) (h1 : term11 n) : (term147 m n) = (term148 n m).
Proof. exact (@lem2625981 n m (@lem2626012 n h1)). Qed.
Lemma lem2626015 (x : int) : (term91 x) = term15.
Proof. exact (EQ_MP (@lem2625734 x) (@lem2625733 x)). Qed.
Lemma lem2626016 (n : nat) : (term149 n) = term15.
Proof. exact (@lem2626015 (int_of_num n)). Qed.
Lemma lem2626017 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem2626018 (n : nat) : (term150 n) = term151.
Proof. exact (MK_COMB (@lem2626017) (@lem2626016 n)). Qed.
Lemma lem2626019 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2626020 (n : nat) (m : int) : (term148 n m) = (term152 m).
Proof. exact (MK_COMB (@lem2626018 n) (@lem2626019 m)). Qed.
Lemma lem2626021 (m : int) (n : nat) (h1 : term11 n) : (term147 m n) = (term152 m).
Proof. exact (TRANS (@lem2626013 m n h1) (@lem2626020 n m)). Qed.
Lemma lem2626022 (m : int) (n : nat) (h1 : term11 n) : (term132 m n) = (term153 n m).
Proof. exact (MK_COMB (@lem2625978 m n h1) (@lem2626021 m n h1)). Qed.
Lemma lem2626026 (t2 : Prop) (t1 : Prop) : (t1 /\ t2) = (t2 /\ t1).
Proof. exact (EQ_MP (@lem2625863 t2 t1) (@lem2625862 t1 t2)). Qed.
Lemma lem2626027 (m : int) (n : nat) : (term153 n m) = (term86 m n).
Proof. exact (@lem2626026 (term152 m) (term85 m n)). Qed.
Lemma lem2626033 (m : int) (n : nat) (h1 : term11 n) : (term132 m n) = (term86 m n).
Proof. exact (TRANS (@lem2626022 m n h1) (@lem2626027 m n)). Qed.
Lemma lem2626034 (m : int) (n : nat) (h1 : term11 n) : ((term34 m n) = term15) = (term86 m n).
Proof. exact (TRANS (@lem2625924 m n) (@lem2626033 m n h1)). Qed.
Lemma lem2626035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2626036 (m : int) (n : nat) (h1 : term11 n) : (term58 m n) = (term154 m n).
Proof. exact (MK_COMB (@lem2626035) (@lem2626034 m n h1)). Qed.
Lemma lem2626047 (m : int) (n : nat) : (term86 m n) = (term86 m n).
Proof. exact (eq_refl (term86 m n)). Qed.
Lemma lem2626048 (m : int) (n : nat) (h1 : term11 n) : (((term34 m n) = term15) = (term86 m n)) = ((term86 m n) = (term86 m n)).
Proof. exact (MK_COMB (@lem2626036 m n h1) (@lem2626047 m n)). Qed.
Lemma lem2626050 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2626051 (x : Prop) : (x = x) = True.
Proof. exact (@lem2626050 Prop x). Qed.
Lemma lem2626052 (m : int) (n : nat) : ((term86 m n) = (term86 m n)) = True.
Proof. exact (@lem2626051 (term86 m n)). Qed.
Lemma lem2626053 (m : int) (n : nat) (h1 : term11 n) : (((term34 m n) = term15) = (term86 m n)) = True.
Proof. exact (TRANS (@lem2626048 m n h1) (@lem2626052 m n)). Qed.
Lemma lem2626054 (m : int) (n : nat) (h1 : term11 n) : True = (((term34 m n) = term15) = (term86 m n)).
Proof. exact (SYM (@lem2626053 m n h1)). Qed.
Lemma lem2626055 (m : int) (n : nat) (h1 : term11 n) : ((term34 m n) = term15) = (term86 m n).
Proof. exact (EQ_MP (@lem2626054 m n h1) (@lem0)). Qed.
Lemma lem2626056 (m : int) (n : nat) (h1 : term11 n) : ((term34 m n) = term15) = (term35 m n).
Proof. exact (EQ_MP (@lem2625729 m n h1) (@lem2626055 m n h1)). Qed.
Lemma lem2626057 (m : int) (n : nat) : ((term34 m n) = term15) = (term35 m n).
Proof. exact (or_elim (@lem2625433 n) (fun h0 : n = (NUMERAL 0) => @lem2625668 m n h0) (fun h0 : term11 n => @lem2626056 m n h0)). Qed.
Lemma lem2626062 (m : int) : term39 m.
Proof. exact (fun n : nat => @lem2626057 m n). Qed.
Lemma lem2626067 : term71.
Proof. exact (fun m : int => @lem2626062 m). Qed.
Lemma lem2626068 : term53.
Proof. exact (EQ_MP (@lem2625580) (@lem2626067)). Qed.
Lemma lem2626069 : term52.
Proof. exact (EQ_MP (@lem2625476) (@lem2626068)). Qed.
