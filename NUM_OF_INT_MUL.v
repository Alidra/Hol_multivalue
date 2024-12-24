Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUM_OF_INT_MUL_term_abbrevs.
Require Import INT_FORALL_POS_spec.
Require Import INT_OF_NUM_MUL_spec.
Require Import NUM_OF_INT_OF_NUM_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem2835462 (P : int -> Prop) (h1 : (term0 P) = (term1 P)) : (term0 P) = (term1 P).
Proof. exact (h1). Qed.
Lemma lem2835463 (P : int -> Prop) (h1 : (term0 P) = (term1 P)) : (term1 P) = (term0 P).
Proof. exact (SYM (@lem2835462 P h1)). Qed.
Lemma lem2835464 (P : int -> Prop) (h1 : (term1 P) = (term0 P)) : (term1 P) = (term0 P).
Proof. exact (h1). Qed.
Lemma lem2835465 (P : int -> Prop) (h1 : (term1 P) = (term0 P)) : (term0 P) = (term1 P).
Proof. exact (SYM (@lem2835464 P h1)). Qed.
Lemma lem2835466 (P : int -> Prop) : ((term0 P) = (term1 P)) = ((term1 P) = (term0 P)).
Proof. exact (prop_ext (fun h1 : (term0 P) = (term1 P) => @lem2835463 P h1) (fun h1 : (term1 P) = (term0 P) => @lem2835465 P h1)). Qed.
Lemma lem2835467 : term2 = term3.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2835466 P)). Qed.
Lemma lem2835468 : (@all (int -> Prop)) = (@all (int -> Prop)).
Proof. exact (eq_refl (@all (int -> Prop))). Qed.
Lemma lem2835469 : term4 = term5.
Proof. exact (MK_COMB (@lem2835468) (@lem2835467)). Qed.
Lemma lem2835470 : term5.
Proof. exact (EQ_MP (@lem2835469) (@lem2315380)). Qed.
Lemma lem2835471 (n : nat) : term6 n.
Proof. exact (@lem2833991 n). Qed.
Lemma lem2835472 (n : nat) : (term6 n) = ((term7 n) = n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem2835474 (m : nat) : term8 m.
Proof. exact (@lem2307381 m). Qed.
Lemma lem2835475 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem2835476 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem2835475 m) (@lem2835474 m)). Qed.
Lemma lem2835477 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem2835476 m n). Qed.
Lemma lem2835478 (m : nat) (n : nat) : (term10 m n) = ((term11 m n) = (term12 m n)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem2835480 (P : int -> Prop) : term13 P.
Proof. exact (@lem2835470 P). Qed.
Lemma lem2835481 (P : int -> Prop) : (term13 P) = ((term1 P) = (term0 P)).
Proof. exact (eq_refl (term13 P)). Qed.
Lemma lem2835483 {A : Type'} (P : Prop) : term14 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem2835484 {A : Type'} (P : Prop) : (term14 A P) = (term15 A P).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem2835485 {A : Type'} (P : Prop) : term15 A P.
Proof. exact (EQ_MP (@lem2835484 A P) (@lem2835483 A P)). Qed.
Lemma lem2835486 {A : Type'} (P : Prop) (Q : A -> Prop) : term16 A P Q.
Proof. exact (@lem2835485 A P Q). Qed.
Lemma lem2835487 {A : Type'} (P : Prop) (Q : A -> Prop) : (term16 A P Q) = ((term17 A P Q) = (term18 A P Q)).
Proof. exact (eq_refl (term16 A P Q)). Qed.
Lemma lem2835518 (p : Prop) (q : Prop) (r : Prop) : (term19 p q r) = (term20 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem2835519 (x : int) (y : int) : (term21 x y) = (term22 x y).
Proof. exact (@lem2835518 (term23 x) (term23 y) ((term24 x y) = (term25 x y))). Qed.
Lemma lem2835526 (x : int) : (term26 x) = (term27 x).
Proof. exact (fun_ext (fun y : int => @lem2835519 x y)). Qed.
Lemma lem2835527 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835528 (x : int) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem2835527) (@lem2835526 x)). Qed.
Lemma lem2835530 {A : Type'} (P : Prop) (Q : A -> Prop) : (term17 A P Q) = (term18 A P Q).
Proof. exact (EQ_MP (@lem2835487 A P Q) (@lem2835486 A P Q)). Qed.
Lemma lem2835531 (P : Prop) (Q : int -> Prop) : (term30 P Q) = (term31 P Q).
Proof. exact (@lem2835530 int P Q). Qed.
Lemma lem2835532 (x : int) : (term32 x) = (term33 x).
Proof. exact (@lem2835531 (term23 x) (term34 x)). Qed.
Lemma lem2835533 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (eq_refl (term35 x y)). Qed.
Lemma lem2835534 (x : int) : (term37 x) = (term37 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem2835535 (x : int) (y : int) : (term38 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem2835534 x) (@lem2835533 x y)). Qed.
Lemma lem2835536 (x : int) : (term39 x) = (term27 x).
Proof. exact (fun_ext (fun y : int => @lem2835535 x y)). Qed.
Lemma lem2835537 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835538 (x : int) : (term32 x) = (term29 x).
Proof. exact (MK_COMB (@lem2835537) (@lem2835536 x)). Qed.
Lemma lem2835539 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2835540 (x : int) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem2835539) (@lem2835538 x)). Qed.
Lemma lem2835541 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (eq_refl (term35 x y)). Qed.
Lemma lem2835542 (x : int) : (term42 x) = (term34 x).
Proof. exact (fun_ext (fun y : int => @lem2835541 x y)). Qed.
Lemma lem2835543 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835544 (x : int) : (term43 x) = (term44 x).
Proof. exact (MK_COMB (@lem2835543) (@lem2835542 x)). Qed.
Lemma lem2835545 (x : int) : (term37 x) = (term37 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem2835546 (x : int) : (term33 x) = (term45 x).
Proof. exact (MK_COMB (@lem2835545 x) (@lem2835544 x)). Qed.
Lemma lem2835547 (x : int) : ((term32 x) = (term33 x)) = ((term29 x) = (term45 x)).
Proof. exact (MK_COMB (@lem2835540 x) (@lem2835546 x)). Qed.
Lemma lem2835548 (x : int) : (term29 x) = (term45 x).
Proof. exact (EQ_MP (@lem2835547 x) (@lem2835532 x)). Qed.
Lemma lem2835579 (x : int) : (term28 x) = (term45 x).
Proof. exact (TRANS (@lem2835528 x) (@lem2835548 x)). Qed.
Lemma lem2835580 : term46 = term47.
Proof. exact (fun_ext (fun x : int => @lem2835579 x)). Qed.
Lemma lem2835581 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835582 : term48 = term49.
Proof. exact (MK_COMB (@lem2835581) (@lem2835580)). Qed.
Lemma lem2835607 : term49 = term48.
Proof. exact (SYM (@lem2835582)). Qed.
Lemma lem2835609 (P : int -> Prop) : (term1 P) = (term0 P).
Proof. exact (EQ_MP (@lem2835481 P) (@lem2835480 P)). Qed.
Lemma lem2835610 : term50 = term51.
Proof. exact (@lem2835609 term52). Qed.
Lemma lem2835611 (x : int) : (term53 x) = (term44 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem2835612 (x : int) : (term37 x) = (term37 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem2835613 (x : int) : (term54 x) = (term45 x).
Proof. exact (MK_COMB (@lem2835612 x) (@lem2835611 x)). Qed.
Lemma lem2835614 : term55 = term47.
Proof. exact (fun_ext (fun x : int => @lem2835613 x)). Qed.
Lemma lem2835615 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835616 : term50 = term49.
Proof. exact (MK_COMB (@lem2835615) (@lem2835614)). Qed.
Lemma lem2835617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2835618 : term56 = term57.
Proof. exact (MK_COMB (@lem2835617) (@lem2835616)). Qed.
Lemma lem2835619 (n : nat) : (term58 n) = (term59 n).
Proof. exact (eq_refl (term58 n)). Qed.
Lemma lem2835620 : term60 = term61.
Proof. exact (fun_ext (fun n : nat => @lem2835619 n)). Qed.
Lemma lem2835621 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835622 : term51 = term62.
Proof. exact (MK_COMB (@lem2835621) (@lem2835620)). Qed.
Lemma lem2835623 : (term50 = term51) = (term49 = term62).
Proof. exact (MK_COMB (@lem2835618) (@lem2835622)). Qed.
Lemma lem2835624 : term49 = term62.
Proof. exact (EQ_MP (@lem2835623) (@lem2835610)). Qed.
Lemma lem2835630 (P : int -> Prop) : (term1 P) = (term0 P).
Proof. exact (EQ_MP (@lem2835481 P) (@lem2835480 P)). Qed.
Lemma lem2835631 (n : nat) : (term63 n) = (term64 n).
Proof. exact (@lem2835630 (term65 n)). Qed.
Lemma lem2835632 (n : nat) (y : int) : (term66 n y) = ((term67 n y) = (term68 n y)).
Proof. exact (eq_refl (term66 n y)). Qed.
Lemma lem2835633 (y : int) : (term37 y) = (term37 y).
Proof. exact (eq_refl (term37 y)). Qed.
Lemma lem2835634 (n : nat) (y : int) : (term69 n y) = (term70 n y).
Proof. exact (MK_COMB (@lem2835633 y) (@lem2835632 n y)). Qed.
Lemma lem2835635 (n : nat) : (term71 n) = (term72 n).
Proof. exact (fun_ext (fun y : int => @lem2835634 n y)). Qed.
Lemma lem2835636 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835637 (n : nat) : (term63 n) = (term59 n).
Proof. exact (MK_COMB (@lem2835636) (@lem2835635 n)). Qed.
Lemma lem2835638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2835639 (n : nat) : (term73 n) = (term74 n).
Proof. exact (MK_COMB (@lem2835638) (@lem2835637 n)). Qed.
Lemma lem2835640 (n : nat) (n' : nat) : (term75 n n') = ((term76 n n') = (term77 n n')).
Proof. exact (eq_refl (term75 n n')). Qed.
Lemma lem2835641 (n : nat) : (term78 n) = (term79 n).
Proof. exact (fun_ext (fun n' : nat => @lem2835640 n n')). Qed.
Lemma lem2835642 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835643 (n : nat) : (term64 n) = (term80 n).
Proof. exact (MK_COMB (@lem2835642) (@lem2835641 n)). Qed.
Lemma lem2835644 (n : nat) : ((term63 n) = (term64 n)) = ((term59 n) = (term80 n)).
Proof. exact (MK_COMB (@lem2835639 n) (@lem2835643 n)). Qed.
Lemma lem2835645 (n : nat) : (term59 n) = (term80 n).
Proof. exact (EQ_MP (@lem2835644 n) (@lem2835631 n)). Qed.
Lemma lem2835653 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (EQ_MP (@lem2835478 m n) (@lem2835477 m n)). Qed.
Lemma lem2835654 (n : nat) (n' : nat) : (term11 n n') = (term12 n n').
Proof. exact (@lem2835653 n n'). Qed.
Lemma lem2835655 : num_of_int = num_of_int.
Proof. exact (eq_refl num_of_int). Qed.
Lemma lem2835656 (n : nat) (n' : nat) : (term76 n n') = (term81 n n').
Proof. exact (MK_COMB (@lem2835655) (@lem2835654 n n')). Qed.
Lemma lem2835658 (n : nat) : (term7 n) = n.
Proof. exact (EQ_MP (@lem2835472 n) (@lem2835471 n)). Qed.
Lemma lem2835659 (n : nat) (n' : nat) : (term81 n n') = (Nat.mul n n').
Proof. exact (@lem2835658 (Nat.mul n n')). Qed.
Lemma lem2835660 (n : nat) (n' : nat) : (term76 n n') = (Nat.mul n n').
Proof. exact (TRANS (@lem2835656 n n') (@lem2835659 n n')). Qed.
Lemma lem2835661 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem2835662 (n : nat) (n' : nat) : (term82 n n') = (term83 n n').
Proof. exact (MK_COMB (@lem2835661) (@lem2835660 n n')). Qed.
Lemma lem2835664 (n : nat) : (term7 n) = n.
Proof. exact (EQ_MP (@lem2835472 n) (@lem2835471 n)). Qed.
Lemma lem2835665 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem2835666 (n : nat) : (term84 n) = (Nat.mul n).
Proof. exact (MK_COMB (@lem2835665) (@lem2835664 n)). Qed.
Lemma lem2835668 (n : nat) : (term7 n) = n.
Proof. exact (EQ_MP (@lem2835472 n) (@lem2835471 n)). Qed.
Lemma lem2835669 (n' : nat) : (term7 n') = n'.
Proof. exact (@lem2835668 n'). Qed.
Lemma lem2835670 (n : nat) (n' : nat) : (term77 n n') = (Nat.mul n n').
Proof. exact (MK_COMB (@lem2835666 n) (@lem2835669 n')). Qed.
Lemma lem2835671 (n : nat) (n' : nat) : ((term76 n n') = (term77 n n')) = ((Nat.mul n n') = (Nat.mul n n')).
Proof. exact (MK_COMB (@lem2835662 n n') (@lem2835670 n n')). Qed.
Lemma lem2835673 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2835674 (x : nat) : (x = x) = True.
Proof. exact (@lem2835673 nat x). Qed.
Lemma lem2835675 (n : nat) (n' : nat) : ((Nat.mul n n') = (Nat.mul n n')) = True.
Proof. exact (@lem2835674 (Nat.mul n n')). Qed.
Lemma lem2835676 (n : nat) (n' : nat) : ((term76 n n') = (term77 n n')) = True.
Proof. exact (TRANS (@lem2835671 n n') (@lem2835675 n n')). Qed.
Lemma lem2835677 (n : nat) : (term79 n) = term85.
Proof. exact (fun_ext (fun n' : nat => @lem2835676 n n')). Qed.
Lemma lem2835678 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835679 (n : nat) : (term80 n) = term86.
Proof. exact (MK_COMB (@lem2835678) (@lem2835677 n)). Qed.
Lemma lem2835681 {A : Type'} (t : Prop) : (term87 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2835682 (t : Prop) : (term88 t) = t.
Proof. exact (@lem2835681 nat t). Qed.
Lemma lem2835683 : term86 = True.
Proof. exact (@lem2835682 True). Qed.
Lemma lem2835684 (n : nat) : (term80 n) = True.
Proof. exact (TRANS (@lem2835679 n) (@lem2835683)). Qed.
Lemma lem2835685 (n : nat) : (term59 n) = True.
Proof. exact (TRANS (@lem2835645 n) (@lem2835684 n)). Qed.
Lemma lem2835686 : term61 = term85.
Proof. exact (fun_ext (fun n : nat => @lem2835685 n)). Qed.
Lemma lem2835687 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835688 : term62 = term86.
Proof. exact (MK_COMB (@lem2835687) (@lem2835686)). Qed.
Lemma lem2835690 {A : Type'} (t : Prop) : (term87 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2835691 (t : Prop) : (term88 t) = t.
Proof. exact (@lem2835690 nat t). Qed.
Lemma lem2835692 : term86 = True.
Proof. exact (@lem2835691 True). Qed.
Lemma lem2835693 : term62 = True.
Proof. exact (TRANS (@lem2835688) (@lem2835692)). Qed.
Lemma lem2835694 : term49 = True.
Proof. exact (TRANS (@lem2835624) (@lem2835693)). Qed.
Lemma lem2835695 : True = term49.
Proof. exact (SYM (@lem2835694)). Qed.
Lemma lem2835696 : term49.
Proof. exact (EQ_MP (@lem2835695) (@lem0)). Qed.
Lemma lem2835697 : term48.
Proof. exact (EQ_MP (@lem2835607) (@lem2835696)). Qed.
