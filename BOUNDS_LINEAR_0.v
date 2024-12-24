Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BOUNDS_LINEAR_0_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import BOUNDS_LINEAR_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm89498_spec.
Lemma lem1260460 : term0.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem1260461 (m : nat) : term1 m.
Proof. exact (@lem1260460 m). Qed.
Lemma lem1260462 (m : nat) : (term1 m) = ((term2 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1260484 : term3.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem1260485 (n : nat) : term4 n.
Proof. exact (@lem1260484 n). Qed.
Lemma lem1260486 (n : nat) : (term4 n) = ((term5 n) = n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem1260518 : term6.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem1260519 (n : nat) : term7 n.
Proof. exact (@lem1260518 n). Qed.
Lemma lem1260520 (n : nat) : (term7 n) = ((term8 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1260522 (A : nat) : term9 A.
Proof. exact (@lem1260452 A). Qed.
Lemma lem1260523 (A : nat) : (term9 A) = (term10 A).
Proof. exact (eq_refl (term9 A)). Qed.
Lemma lem1260524 (A : nat) : term10 A.
Proof. exact (EQ_MP (@lem1260523 A) (@lem1260522 A)). Qed.
Lemma lem1260525 (A : nat) : term11 A.
Proof. exact (@lem1260524 A (NUMERAL 0)). Qed.
Lemma lem1260526 (A : nat) : (term11 A) = (term12 A).
Proof. exact (eq_refl (term11 A)). Qed.
Lemma lem1260527 (A : nat) : term12 A.
Proof. exact (EQ_MP (@lem1260526 A) (@lem1260525 A)). Qed.
Lemma lem1260528 (A : nat) (B : nat) : term13 A B.
Proof. exact (@lem1260527 A B). Qed.
Lemma lem1260529 (B : nat) (A : nat) : (term13 A B) = ((term14 A B) = (term2 A)).
Proof. exact (eq_refl (term13 A B)). Qed.
Lemma lem1260530 (B : nat) (A : nat) : (term14 A B) = (term2 A).
Proof. exact (EQ_MP (@lem1260529 B A) (@lem1260528 A B)). Qed.
Lemma lem1260542 (n : nat) : (term8 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1260520 n) (@lem1260519 n)). Qed.
Lemma lem1260543 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1260544 (n : nat) : (term15 n) = term16.
Proof. exact (MK_COMB (@lem1260543) (@lem1260542 n)). Qed.
Lemma lem1260545 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1260546 (n : nat) (B : nat) : (term17 n B) = (term5 B).
Proof. exact (MK_COMB (@lem1260544 n) (@lem1260545 B)). Qed.
Lemma lem1260548 (n : nat) : (term5 n) = n.
Proof. exact (EQ_MP (@lem1260486 n) (@lem1260485 n)). Qed.
Lemma lem1260549 (B : nat) : (term5 B) = B.
Proof. exact (@lem1260548 B). Qed.
Lemma lem1260550 (n : nat) (B : nat) : (term17 n B) = B.
Proof. exact (TRANS (@lem1260546 n B) (@lem1260549 B)). Qed.
Lemma lem1260551 (A : nat) (n : nat) : (term18 A n) = (term18 A n).
Proof. exact (eq_refl (term18 A n)). Qed.
Lemma lem1260552 (A : nat) (n : nat) (B : nat) : (term19 A n B) = (term20 A n B).
Proof. exact (MK_COMB (@lem1260551 A n) (@lem1260550 n B)). Qed.
Lemma lem1260553 (A : nat) (B : nat) : (term21 A B) = (term22 A B).
Proof. exact (fun_ext (fun n : nat => @lem1260552 A n B)). Qed.
Lemma lem1260554 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1260555 (A : nat) (B : nat) : (term14 A B) = (term23 A B).
Proof. exact (MK_COMB (@lem1260554) (@lem1260553 A B)). Qed.
Lemma lem1260560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1260561 (A : nat) (B : nat) : (term24 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem1260560) (@lem1260555 A B)). Qed.
Lemma lem1260563 (m : nat) : (term2 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1260462 m) (@lem1260461 m)). Qed.
Lemma lem1260564 (A : nat) : (term2 A) = (A = (NUMERAL 0)).
Proof. exact (@lem1260563 A). Qed.
Lemma lem1260567 (B : nat) (A : nat) : ((term14 A B) = (term2 A)) = ((term23 A B) = (A = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1260561 A B) (@lem1260564 A)). Qed.
Lemma lem1260570 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1260571 (B : nat) (A : nat) : (term26 B A) = (term27 B A).
Proof. exact (MK_COMB (@lem1260570) (@lem1260567 B A)). Qed.
Lemma lem1260580 (B : nat) (A : nat) : ((term23 A B) = (A = (NUMERAL 0))) = ((term23 A B) = (A = (NUMERAL 0))).
Proof. exact (eq_refl ((term23 A B) = (A = (NUMERAL 0)))). Qed.
Lemma lem1260581 (B : nat) (A : nat) : (term28 B A) = (term29 B A).
Proof. exact (MK_COMB (@lem1260571 B A) (@lem1260580 B A)). Qed.
Lemma lem1260585 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1260586 (B : nat) (A : nat) : (term29 B A) = True.
Proof. exact (@lem1260585 ((term23 A B) = (A = (NUMERAL 0)))). Qed.
Lemma lem1260587 (B : nat) (A : nat) : (term28 B A) = True.
Proof. exact (TRANS (@lem1260581 B A) (@lem1260586 B A)). Qed.
Lemma lem1260588 (B : nat) (A : nat) : True = (term28 B A).
Proof. exact (SYM (@lem1260587 B A)). Qed.
Lemma lem1260589 (B : nat) (A : nat) : term28 B A.
Proof. exact (EQ_MP (@lem1260588 B A) (@lem0)). Qed.
Lemma lem1260590 (B : nat) (A : nat) : (term23 A B) = (A = (NUMERAL 0)).
Proof. exact (@lem1260589 B A (@lem1260530 B A)). Qed.
Lemma lem1260595 (A : nat) : term30 A.
Proof. exact (fun B : nat => @lem1260590 B A). Qed.
Lemma lem1260600 : term31.
Proof. exact (fun A : nat => @lem1260595 A). Qed.
