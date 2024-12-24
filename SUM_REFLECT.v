Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_REFLECT_term_abbrevs.
Require Import ITERATE_REFLECT_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Require Import thm7064171_spec.
Require Import thm7065437_spec.
Lemma lem7226453 {A : Type'} (op : type1400 A) : term0 A op.
Proof. exact (@lem6377849 A op). Qed.
Lemma lem7226454 {A : Type'} (op : type1400 A) : (term0 A op) = (term1 A op).
Proof. exact (eq_refl (term0 A op)). Qed.
Lemma lem7226457 {A : Type'} (op : type1400 A) : term1 A op.
Proof. exact (EQ_MP (@lem7226454 A op) (@lem7226453 A op)). Qed.
Lemma lem7226458 (op : type1627) : term2 op.
Proof. exact (@lem7226457 real op). Qed.
Lemma lem7226459 : term3.
Proof. exact (@lem7226458 real_add). Qed.
Lemma lem7226460 : term4.
Proof. exact (@lem7226459 (@lem7067132)). Qed.
Lemma lem7226461 (x : nat -> real) : term5 x.
Proof. exact (@lem7226460 x). Qed.
Lemma lem7226462 (x : nat -> real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem7226463 (x : nat -> real) : term6 x.
Proof. exact (EQ_MP (@lem7226462 x) (@lem7226461 x)). Qed.
Lemma lem7226464 (x : nat -> real) (m : nat) : term7 x m.
Proof. exact (@lem7226463 x m). Qed.
Lemma lem7226465 (m : nat) (x : nat -> real) : (term7 x m) = (term8 m x).
Proof. exact (eq_refl (term7 x m)). Qed.
Lemma lem7226466 (m : nat) (x : nat -> real) : term8 m x.
Proof. exact (EQ_MP (@lem7226465 m x) (@lem7226464 x m)). Qed.
Lemma lem7226467 (m : nat) (x : nat -> real) (n : nat) : term9 m x n.
Proof. exact (@lem7226466 m x n). Qed.
Lemma lem7226468 (m : nat) (x : nat -> real) (n : nat) : (term9 m x n) = ((term10 m n x) = (term11 m x n)).
Proof. exact (eq_refl (term9 m x n)). Qed.
Lemma lem7226473 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7226474 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7226473 nat). Qed.
Lemma lem7226475 (m : nat) (n : nat) : (dotdot m n) = (dotdot m n).
Proof. exact (eq_refl (dotdot m n)). Qed.
Lemma lem7226476 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem7226474) (@lem7226475 m n)). Qed.
Lemma lem7226477 (x : nat -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7226478 (m : nat) (n : nat) (x : nat -> real) : (term14 m n x) = (term10 m n x).
Proof. exact (MK_COMB (@lem7226476 m n) (@lem7226477 x)). Qed.
Lemma lem7226479 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7226480 (m : nat) (n : nat) (x : nat -> real) : (term15 m n x) = (term16 m n x).
Proof. exact (MK_COMB (@lem7226479) (@lem7226478 m n x)). Qed.
Lemma lem7226482 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7226483 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7226482 nat). Qed.
Lemma lem7226484 (n : nat) (m : nat) : (term17 n m) = (term17 n m).
Proof. exact (eq_refl (term17 n m)). Qed.
Lemma lem7226485 (n : nat) (m : nat) : (term18 n m) = (term19 n m).
Proof. exact (MK_COMB (@lem7226483) (@lem7226484 n m)). Qed.
Lemma lem7226486 (x : nat -> real) (n : nat) : (term20 x n) = (term20 x n).
Proof. exact (eq_refl (term20 x n)). Qed.
Lemma lem7226487 (m : nat) (x : nat -> real) (n : nat) : (term21 m x n) = (term22 m x n).
Proof. exact (MK_COMB (@lem7226485 n m) (@lem7226486 x n)). Qed.
Lemma lem7226488 (n : nat) (m : nat) : (term23 n m) = (term23 n m).
Proof. exact (eq_refl (term23 n m)). Qed.
Lemma lem7226489 (m : nat) (x : nat -> real) (n : nat) : (term24 m x n) = (term25 m x n).
Proof. exact (MK_COMB (@lem7226488 n m) (@lem7226487 m x n)). Qed.
Lemma lem7226490 (m : nat) (x : nat -> real) (n : nat) : ((term14 m n x) = (term24 m x n)) = ((term10 m n x) = (term25 m x n)).
Proof. exact (MK_COMB (@lem7226480 m n x) (@lem7226489 m x n)). Qed.
Lemma lem7226493 (m : nat) (x : nat -> real) (n : nat) : ((term10 m n x) = (term25 m x n)) = ((term14 m n x) = (term24 m x n)).
Proof. exact (SYM (@lem7226490 m x n)). Qed.
Lemma lem7226495 (m : nat) (x : nat -> real) (n : nat) : (term10 m n x) = (term11 m x n).
Proof. exact (EQ_MP (@lem7226468 m x n) (@lem7226467 m x n)). Qed.
Lemma lem7226496 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7226497 (m : nat) (x : nat -> real) (n : nat) : (term16 m n x) = (term26 m x n).
Proof. exact (MK_COMB (@lem7226496) (@lem7226495 m x n)). Qed.
Lemma lem7226498 (m : nat) (x : nat -> real) (n : nat) : (term25 m x n) = (term25 m x n).
Proof. exact (eq_refl (term25 m x n)). Qed.
Lemma lem7226499 (m : nat) (x : nat -> real) (n : nat) : ((term10 m n x) = (term25 m x n)) = ((term11 m x n) = (term25 m x n)).
Proof. exact (MK_COMB (@lem7226497 m x n) (@lem7226498 m x n)). Qed.
Lemma lem7226500 (m : nat) (x : nat -> real) (n : nat) : ((term11 m x n) = (term25 m x n)) = ((term10 m n x) = (term25 m x n)).
Proof. exact (SYM (@lem7226499 m x n)). Qed.
Lemma lem7226504 : (@neutral real real_add) = term27.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7226505 (n : nat) (m : nat) : (term28 n m) = (term28 n m).
Proof. exact (eq_refl (term28 n m)). Qed.
Lemma lem7226506 (n : nat) (m : nat) : (term29 n m) = (term23 n m).
Proof. exact (MK_COMB (@lem7226505 n m) (@lem7226504)). Qed.
Lemma lem7226507 (m : nat) (x : nat -> real) (n : nat) : (term22 m x n) = (term22 m x n).
Proof. exact (eq_refl (term22 m x n)). Qed.
Lemma lem7226508 (m : nat) (x : nat -> real) (n : nat) : (term11 m x n) = (term25 m x n).
Proof. exact (MK_COMB (@lem7226506 n m) (@lem7226507 m x n)). Qed.
Lemma lem7226509 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7226510 (m : nat) (x : nat -> real) (n : nat) : (term26 m x n) = (term30 m x n).
Proof. exact (MK_COMB (@lem7226509) (@lem7226508 m x n)). Qed.
Lemma lem7226511 (m : nat) (x : nat -> real) (n : nat) : (term25 m x n) = (term25 m x n).
Proof. exact (eq_refl (term25 m x n)). Qed.
Lemma lem7226512 (m : nat) (x : nat -> real) (n : nat) : ((term11 m x n) = (term25 m x n)) = ((term25 m x n) = (term25 m x n)).
Proof. exact (MK_COMB (@lem7226510 m x n) (@lem7226511 m x n)). Qed.
Lemma lem7226514 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7226515 (x : real) : (x = x) = True.
Proof. exact (@lem7226514 real x). Qed.
Lemma lem7226516 (m : nat) (x : nat -> real) (n : nat) : ((term25 m x n) = (term25 m x n)) = True.
Proof. exact (@lem7226515 (term25 m x n)). Qed.
Lemma lem7226517 (m : nat) (x : nat -> real) (n : nat) : ((term11 m x n) = (term25 m x n)) = True.
Proof. exact (TRANS (@lem7226512 m x n) (@lem7226516 m x n)). Qed.
Lemma lem7226518 (m : nat) (x : nat -> real) (n : nat) : True = ((term11 m x n) = (term25 m x n)).
Proof. exact (SYM (@lem7226517 m x n)). Qed.
Lemma lem7226519 (m : nat) (x : nat -> real) (n : nat) : (term11 m x n) = (term25 m x n).
Proof. exact (EQ_MP (@lem7226518 m x n) (@lem0)). Qed.
Lemma lem7226520 (m : nat) (x : nat -> real) (n : nat) : (term10 m n x) = (term25 m x n).
Proof. exact (EQ_MP (@lem7226500 m x n) (@lem7226519 m x n)). Qed.
Lemma lem7226521 (m : nat) (x : nat -> real) (n : nat) : (term14 m n x) = (term24 m x n).
Proof. exact (EQ_MP (@lem7226493 m x n) (@lem7226520 m x n)). Qed.
Lemma lem7226526 (m : nat) (x : nat -> real) : term31 m x.
Proof. exact (fun n : nat => @lem7226521 m x n). Qed.
Lemma lem7226531 (x : nat -> real) : term32 x.
Proof. exact (fun m : nat => @lem7226526 m x). Qed.
Lemma lem7226536 : term33.
Proof. exact (fun x : nat -> real => @lem7226531 x). Qed.
