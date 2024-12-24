Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONG_term_abbrevs.
Require Import INT_OF_NUM_EQ_spec.
Require Import INT_OF_NUM_REM_spec.
Require Import INT_REM_EQ_spec.
Require Import num_congruent_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3070518 (m : int) (n : int) (p : int) (h1 : ((rem m p) = (rem n p)) = (term0 m n p)) : ((rem m p) = (rem n p)) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem3070519 (m : int) (n : int) (p : int) (h1 : ((rem m p) = (rem n p)) = (term0 m n p)) : (term0 m n p) = ((rem m p) = (rem n p)).
Proof. exact (SYM (@lem3070518 m n p h1)). Qed.
Lemma lem3070520 (m : int) (n : int) (p : int) (h1 : (term0 m n p) = ((rem m p) = (rem n p))) : (term0 m n p) = ((rem m p) = (rem n p)).
Proof. exact (h1). Qed.
Lemma lem3070521 (m : int) (n : int) (p : int) (h1 : (term0 m n p) = ((rem m p) = (rem n p))) : ((rem m p) = (rem n p)) = (term0 m n p).
Proof. exact (SYM (@lem3070520 m n p h1)). Qed.
Lemma lem3070522 (m : int) (n : int) (p : int) : (((rem m p) = (rem n p)) = (term0 m n p)) = ((term0 m n p) = ((rem m p) = (rem n p))).
Proof. exact (prop_ext (fun h1 : ((rem m p) = (rem n p)) = (term0 m n p) => @lem3070519 m n p h1) (fun h1 : (term0 m n p) = ((rem m p) = (rem n p)) => @lem3070521 m n p h1)). Qed.
Lemma lem3070523 (m : int) (n : int) : (term1 m n) = (term2 m n).
Proof. exact (fun_ext (fun p : int => @lem3070522 m n p)). Qed.
Lemma lem3070524 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3070525 (m : int) (n : int) : (term3 m n) = (term4 m n).
Proof. exact (MK_COMB (@lem3070524) (@lem3070523 m n)). Qed.
Lemma lem3070526 (m : int) : (term5 m) = (term6 m).
Proof. exact (fun_ext (fun n : int => @lem3070525 m n)). Qed.
Lemma lem3070527 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3070528 (m : int) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem3070527) (@lem3070526 m)). Qed.
Lemma lem3070529 : term9 = term10.
Proof. exact (fun_ext (fun m : int => @lem3070528 m)). Qed.
Lemma lem3070530 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3070531 : term11 = term12.
Proof. exact (MK_COMB (@lem3070530) (@lem3070529)). Qed.
Lemma lem3070532 : term12.
Proof. exact (EQ_MP (@lem3070531) (@lem2522863)). Qed.
Lemma lem3070533 (m : nat) : term13 m.
Proof. exact (@lem2307147 m). Qed.
Lemma lem3070534 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem3070535 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem3070534 m) (@lem3070533 m)). Qed.
Lemma lem3070536 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem3070535 m n). Qed.
Lemma lem3070537 (m : nat) (n : nat) : (term15 m n) = (((int_of_num m) = (int_of_num n)) = (m = n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem3070539 (m : nat) : term16 m.
Proof. exact (@lem2538104 m). Qed.
Lemma lem3070540 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem3070541 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem3070540 m) (@lem3070539 m)). Qed.
Lemma lem3070542 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem3070541 m n). Qed.
Lemma lem3070543 (m : nat) (n : nat) : (term18 m n) = ((term19 m n) = (term20 m n)).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem3070545 (m : int) : term21 m.
Proof. exact (@lem3070532 m). Qed.
Lemma lem3070546 (m : int) : (term21 m) = (term8 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem3070547 (m : int) : term8 m.
Proof. exact (EQ_MP (@lem3070546 m) (@lem3070545 m)). Qed.
Lemma lem3070548 (m : int) (n : int) : term22 m n.
Proof. exact (@lem3070547 m n). Qed.
Lemma lem3070549 (m : int) (n : int) : (term22 m n) = (term4 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem3070550 (m : int) (n : int) : term4 m n.
Proof. exact (EQ_MP (@lem3070549 m n) (@lem3070548 m n)). Qed.
Lemma lem3070551 (m : int) (n : int) (p : int) : term23 m n p.
Proof. exact (@lem3070550 m n p). Qed.
Lemma lem3070552 (m : int) (n : int) (p : int) : (term23 m n p) = ((term0 m n p) = ((rem m p) = (rem n p))).
Proof. exact (eq_refl (term23 m n p)). Qed.
Lemma lem3070554 (x : nat) : term24 x.
Proof. exact (@lem2837601 x). Qed.
Lemma lem3070555 (x : nat) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem3070556 (x : nat) : term25 x.
Proof. exact (EQ_MP (@lem3070555 x) (@lem3070554 x)). Qed.
Lemma lem3070557 (x : nat) (y : nat) : term26 x y.
Proof. exact (@lem3070556 x y). Qed.
Lemma lem3070558 (x : nat) (y : nat) : (term26 x y) = (term27 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem3070559 (x : nat) (y : nat) : term27 x y.
Proof. exact (EQ_MP (@lem3070558 x y) (@lem3070557 x y)). Qed.
Lemma lem3070560 (x : nat) (y : nat) (n : nat) : term28 x y n.
Proof. exact (@lem3070559 x y n). Qed.
Lemma lem3070561 (x : nat) (y : nat) (n : nat) : (term28 x y n) = ((term29 x y n) = (term30 x y n)).
Proof. exact (eq_refl (term28 x y n)). Qed.
Lemma lem3070578 (x : nat) (y : nat) (n : nat) : (term29 x y n) = (term30 x y n).
Proof. exact (EQ_MP (@lem3070561 x y n) (@lem3070560 x y n)). Qed.
Lemma lem3070580 (m : int) (n : int) (p : int) : (term0 m n p) = ((rem m p) = (rem n p)).
Proof. exact (EQ_MP (@lem3070552 m n p) (@lem3070551 m n p)). Qed.
Lemma lem3070581 (x : nat) (y : nat) (n : nat) : (term30 x y n) = ((term19 x n) = (term19 y n)).
Proof. exact (@lem3070580 (int_of_num x) (int_of_num y) (int_of_num n)). Qed.
Lemma lem3070584 (x : nat) (y : nat) (n : nat) : (term29 x y n) = ((term19 x n) = (term19 y n)).
Proof. exact (TRANS (@lem3070578 x y n) (@lem3070581 x y n)). Qed.
Lemma lem3070586 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem3070543 m n) (@lem3070542 m n)). Qed.
Lemma lem3070587 (x : nat) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (@lem3070586 x n). Qed.
Lemma lem3070588 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3070589 (x : nat) (n : nat) : (term31 x n) = (term32 x n).
Proof. exact (MK_COMB (@lem3070588) (@lem3070587 x n)). Qed.
Lemma lem3070591 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem3070543 m n) (@lem3070542 m n)). Qed.
Lemma lem3070592 (y : nat) (n : nat) : (term19 y n) = (term20 y n).
Proof. exact (@lem3070591 y n). Qed.
Lemma lem3070593 (x : nat) (y : nat) (n : nat) : ((term19 x n) = (term19 y n)) = ((term20 x n) = (term20 y n)).
Proof. exact (MK_COMB (@lem3070589 x n) (@lem3070592 y n)). Qed.
Lemma lem3070595 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem3070537 m n) (@lem3070536 m n)). Qed.
Lemma lem3070596 (x : nat) (y : nat) (n : nat) : ((term20 x n) = (term20 y n)) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (@lem3070595 (Nat.modulo x n) (Nat.modulo y n)). Qed.
Lemma lem3070599 (x : nat) (y : nat) (n : nat) : ((term19 x n) = (term19 y n)) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (TRANS (@lem3070593 x y n) (@lem3070596 x y n)). Qed.
Lemma lem3070600 (x : nat) (y : nat) (n : nat) : (term29 x y n) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (TRANS (@lem3070584 x y n) (@lem3070599 x y n)). Qed.
Lemma lem3070601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3070602 (x : nat) (y : nat) (n : nat) : (term33 x y n) = (term34 x y n).
Proof. exact (MK_COMB (@lem3070601) (@lem3070600 x y n)). Qed.
Lemma lem3070605 (x : nat) (y : nat) (n : nat) : ((Nat.modulo x n) = (Nat.modulo y n)) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (eq_refl ((Nat.modulo x n) = (Nat.modulo y n))). Qed.
Lemma lem3070606 (x : nat) (y : nat) (n : nat) : ((term29 x y n) = ((Nat.modulo x n) = (Nat.modulo y n))) = (((Nat.modulo x n) = (Nat.modulo y n)) = ((Nat.modulo x n) = (Nat.modulo y n))).
Proof. exact (MK_COMB (@lem3070602 x y n) (@lem3070605 x y n)). Qed.
Lemma lem3070608 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3070609 (x : Prop) : (x = x) = True.
Proof. exact (@lem3070608 Prop x). Qed.
Lemma lem3070610 (x : nat) (y : nat) (n : nat) : (((Nat.modulo x n) = (Nat.modulo y n)) = ((Nat.modulo x n) = (Nat.modulo y n))) = True.
Proof. exact (@lem3070609 ((Nat.modulo x n) = (Nat.modulo y n))). Qed.
Lemma lem3070611 (x : nat) (y : nat) (n : nat) : ((term29 x y n) = ((Nat.modulo x n) = (Nat.modulo y n))) = True.
Proof. exact (TRANS (@lem3070606 x y n) (@lem3070610 x y n)). Qed.
Lemma lem3070612 (x : nat) (y : nat) : (term35 x y) = term36.
Proof. exact (fun_ext (fun n : nat => @lem3070611 x y n)). Qed.
Lemma lem3070613 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070614 (x : nat) (y : nat) : (term37 x y) = term38.
Proof. exact (MK_COMB (@lem3070613) (@lem3070612 x y)). Qed.
Lemma lem3070616 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070617 (t : Prop) : (term40 t) = t.
Proof. exact (@lem3070616 nat t). Qed.
Lemma lem3070618 : term38 = True.
Proof. exact (@lem3070617 True). Qed.
Lemma lem3070619 (x : nat) (y : nat) : (term37 x y) = True.
Proof. exact (TRANS (@lem3070614 x y) (@lem3070618)). Qed.
Lemma lem3070620 (x : nat) : (term41 x) = term36.
Proof. exact (fun_ext (fun y : nat => @lem3070619 x y)). Qed.
Lemma lem3070621 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070622 (x : nat) : (term42 x) = term38.
Proof. exact (MK_COMB (@lem3070621) (@lem3070620 x)). Qed.
Lemma lem3070624 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070625 (t : Prop) : (term40 t) = t.
Proof. exact (@lem3070624 nat t). Qed.
Lemma lem3070626 : term38 = True.
Proof. exact (@lem3070625 True). Qed.
Lemma lem3070627 (x : nat) : (term42 x) = True.
Proof. exact (TRANS (@lem3070622 x) (@lem3070626)). Qed.
Lemma lem3070628 : term43 = term36.
Proof. exact (fun_ext (fun x : nat => @lem3070627 x)). Qed.
Lemma lem3070629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070630 : term44 = term38.
Proof. exact (MK_COMB (@lem3070629) (@lem3070628)). Qed.
Lemma lem3070632 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070633 (t : Prop) : (term40 t) = t.
Proof. exact (@lem3070632 nat t). Qed.
Lemma lem3070634 : term38 = True.
Proof. exact (@lem3070633 True). Qed.
Lemma lem3070635 : term44 = True.
Proof. exact (TRANS (@lem3070630) (@lem3070634)). Qed.
Lemma lem3070636 : True = term44.
Proof. exact (SYM (@lem3070635)). Qed.
Lemma lem3070637 : term44.
Proof. exact (EQ_MP (@lem3070636) (@lem0)). Qed.
