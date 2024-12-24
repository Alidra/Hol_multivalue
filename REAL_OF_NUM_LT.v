Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_LT_term_abbrevs.
Require Import NOT_LE_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm1340282_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1483590 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem1483591 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem1483590 n m h1)). Qed.
Lemma lem1483592 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem1483593 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem1483592 m n h1)). Qed.
Lemma lem1483594 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem1483591 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem1483593 m n h1)). Qed.
Lemma lem1483595 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem1483594 m n)). Qed.
Lemma lem1483596 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1483597 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem1483596) (@lem1483595 m)). Qed.
Lemma lem1483598 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem1483597 m)). Qed.
Lemma lem1483599 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1483600 : term7 = term8.
Proof. exact (MK_COMB (@lem1483599) (@lem1483598)). Qed.
Lemma lem1483601 : term8.
Proof. exact (EQ_MP (@lem1483600) (@lem97961)). Qed.
Lemma lem1483602 (m : nat) : term9 m.
Proof. exact (@lem1340282 m). Qed.
Lemma lem1483603 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1483604 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem1483603 m) (@lem1483602 m)). Qed.
Lemma lem1483605 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem1483604 m n). Qed.
Lemma lem1483606 (m : nat) (n : nat) : (term11 m n) = ((term12 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem1483608 (m : nat) : term13 m.
Proof. exact (@lem1483601 m). Qed.
Lemma lem1483609 (m : nat) : (term13 m) = (term4 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem1483610 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1483609 m) (@lem1483608 m)). Qed.
Lemma lem1483611 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem1483610 m n). Qed.
Lemma lem1483612 (m : nat) (n : nat) : (term14 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem1483614 (y : real) : term15 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1483615 (y : real) : (term15 y) = (term16 y).
Proof. exact (eq_refl (term15 y)). Qed.
Lemma lem1483616 (y : real) : term16 y.
Proof. exact (EQ_MP (@lem1483615 y) (@lem1483614 y)). Qed.
Lemma lem1483617 (y : real) (x : real) : term17 y x.
Proof. exact (@lem1483616 y x). Qed.
Lemma lem1483618 (y : real) (x : real) : (term17 y x) = ((real_lt x y) = (term18 y x)).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1483631 (y : real) (x : real) : (real_lt x y) = (term18 y x).
Proof. exact (EQ_MP (@lem1483618 y x) (@lem1483617 y x)). Qed.
Lemma lem1483632 (n : nat) (m : nat) : (term19 m n) = (term20 n m).
Proof. exact (@lem1483631 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1483634 (m : nat) (n : nat) : (term12 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1483606 m n) (@lem1483605 m n)). Qed.
Lemma lem1483635 (n : nat) (m : nat) : (term12 n m) = (Peano.le n m).
Proof. exact (@lem1483634 n m). Qed.
Lemma lem1483636 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1483637 (n : nat) (m : nat) : (term20 n m) = (term0 n m).
Proof. exact (MK_COMB (@lem1483636) (@lem1483635 n m)). Qed.
Lemma lem1483638 (n : nat) (m : nat) : (term19 m n) = (term0 n m).
Proof. exact (TRANS (@lem1483632 n m) (@lem1483637 n m)). Qed.
Lemma lem1483639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1483640 (n : nat) (m : nat) : (term21 m n) = (term22 n m).
Proof. exact (MK_COMB (@lem1483639) (@lem1483638 n m)). Qed.
Lemma lem1483642 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem1483612 m n) (@lem1483611 m n)). Qed.
Lemma lem1483643 (n : nat) (m : nat) : (Peano.lt m n) = (term0 n m).
Proof. exact (@lem1483642 n m). Qed.
Lemma lem1483644 (n : nat) (m : nat) : ((term19 m n) = (Peano.lt m n)) = ((term0 n m) = (term0 n m)).
Proof. exact (MK_COMB (@lem1483640 n m) (@lem1483643 n m)). Qed.
Lemma lem1483646 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1483647 (x : Prop) : (x = x) = True.
Proof. exact (@lem1483646 Prop x). Qed.
Lemma lem1483648 (n : nat) (m : nat) : ((term0 n m) = (term0 n m)) = True.
Proof. exact (@lem1483647 (term0 n m)). Qed.
Lemma lem1483649 (m : nat) (n : nat) : ((term19 m n) = (Peano.lt m n)) = True.
Proof. exact (TRANS (@lem1483644 n m) (@lem1483648 n m)). Qed.
Lemma lem1483650 (m : nat) : (term23 m) = term24.
Proof. exact (fun_ext (fun n : nat => @lem1483649 m n)). Qed.
Lemma lem1483651 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1483652 (m : nat) : (term25 m) = term26.
Proof. exact (MK_COMB (@lem1483651) (@lem1483650 m)). Qed.
Lemma lem1483654 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1483655 (t : Prop) : (term28 t) = t.
Proof. exact (@lem1483654 nat t). Qed.
Lemma lem1483656 : term26 = True.
Proof. exact (@lem1483655 True). Qed.
Lemma lem1483657 (m : nat) : (term25 m) = True.
Proof. exact (TRANS (@lem1483652 m) (@lem1483656)). Qed.
Lemma lem1483658 : term29 = term24.
Proof. exact (fun_ext (fun m : nat => @lem1483657 m)). Qed.
Lemma lem1483659 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1483660 : term30 = term26.
Proof. exact (MK_COMB (@lem1483659) (@lem1483658)). Qed.
Lemma lem1483662 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1483663 (t : Prop) : (term28 t) = t.
Proof. exact (@lem1483662 nat t). Qed.
Lemma lem1483664 : term26 = True.
Proof. exact (@lem1483663 True). Qed.
Lemma lem1483665 : term30 = True.
Proof. exact (TRANS (@lem1483660) (@lem1483664)). Qed.
Lemma lem1483666 : True = term30.
Proof. exact (SYM (@lem1483665)). Qed.
Lemma lem1483667 : term30.
Proof. exact (EQ_MP (@lem1483666) (@lem0)). Qed.
