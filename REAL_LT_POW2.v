Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_POW2_term_abbrevs.
Require Import REAL_OF_NUM_LT_spec.
Require Import REAL_POW_LT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm520356_spec.
Require Import thm7_spec.
Lemma lem1642193 : term0.
Proof. exact (EQ_MP (@lem520356) (@lem0)). Qed.
Lemma lem1642194 : term1.
Proof. exact (proj2 (@lem1642193)). Qed.
Lemma lem1642195 : term2.
Proof. exact (proj2 (@lem1642194)). Qed.
Lemma lem1642196 : term3.
Proof. exact (proj2 (@lem1642195)). Qed.
Lemma lem1642197 : term4.
Proof. exact (proj2 (@lem1642196)). Qed.
Lemma lem1642198 : term5.
Proof. exact (proj2 (@lem1642197)). Qed.
Lemma lem1642230 : term6.
Proof. exact (proj1 (@lem1642198)). Qed.
Lemma lem1642231 (n : nat) : term7 n.
Proof. exact (@lem1642230 n). Qed.
Lemma lem1642232 (n : nat) : (term7 n) = ((term8 n) = True).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1642234 : term9.
Proof. exact (proj1 (@lem1642197)). Qed.
Lemma lem1642235 (n : nat) : term10 n.
Proof. exact (@lem1642234 n). Qed.
Lemma lem1642236 (n : nat) : (term10 n) = ((term11 n) = (Peano.lt 0 n)).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem1642247 : term12.
Proof. exact (proj1 (@lem1642193)). Qed.
Lemma lem1642248 (m : nat) : term13 m.
Proof. exact (@lem1642247 m). Qed.
Lemma lem1642249 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem1642250 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem1642249 m) (@lem1642248 m)). Qed.
Lemma lem1642251 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem1642250 m n). Qed.
Lemma lem1642252 (m : nat) (n : nat) : (term15 m n) = ((term16 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem1642626 (m : nat) : term17 m.
Proof. exact (@lem1483667 m). Qed.
Lemma lem1642627 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1642628 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1642627 m) (@lem1642626 m)). Qed.
Lemma lem1642629 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1642628 m n). Qed.
Lemma lem1642630 (m : nat) (n : nat) : (term19 m n) = ((term20 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1642632 (x : real) : term21 x.
Proof. exact (@lem1582551 x). Qed.
Lemma lem1642633 (x : real) : (term21 x) = (term22 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1642634 (x : real) : term22 x.
Proof. exact (EQ_MP (@lem1642633 x) (@lem1642632 x)). Qed.
Lemma lem1642635 (x : real) (n : nat) : term23 x n.
Proof. exact (@lem1642634 x n). Qed.
Lemma lem1642636 (x : real) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem1642637 (x : real) (n : nat) : term24 x n.
Proof. exact (EQ_MP (@lem1642636 x n) (@lem1642635 x n)). Qed.
Lemma lem1642638 (x : real) (h1 : term25 x) : term25 x.
Proof. exact (h1). Qed.
Lemma lem1642639 (n : nat) (x : real) (h1 : term25 x) : term26 x n.
Proof. exact (@lem1642637 x n (@lem1642638 x h1)). Qed.
Lemma lem1642640 (x : real) (n : nat) : (term26 x n) = ((term26 x n) = True).
Proof. exact (@lem7 (term26 x n)). Qed.
Lemma lem1642641 (n : nat) (x : real) (h1 : term25 x) : (term26 x n) = True.
Proof. exact (EQ_MP (@lem1642640 x n) (@lem1642639 n x h1)). Qed.
Lemma lem1642652 (x : real) (n : nat) : term27 x n.
Proof. exact (fun h0 : term25 x => @lem1642641 n x h0). Qed.
Lemma lem1642653 (n : nat) : term28 n.
Proof. exact (@lem1642652 term29 n). Qed.
Lemma lem1642655 (m : nat) (n : nat) : (term20 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1642630 m n) (@lem1642629 m n)). Qed.
Lemma lem1642656 : term30 = term31.
Proof. exact (@lem1642655 (NUMERAL 0) term32). Qed.
Lemma lem1642658 (m : nat) (n : nat) : (term16 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1642252 m n) (@lem1642251 m n)). Qed.
Lemma lem1642659 : term31 = term33.
Proof. exact (@lem1642658 0 term34). Qed.
Lemma lem1642661 (n : nat) : (term11 n) = (Peano.lt 0 n).
Proof. exact (EQ_MP (@lem1642236 n) (@lem1642235 n)). Qed.
Lemma lem1642662 : term33 = term35.
Proof. exact (@lem1642661 (BIT1 0)). Qed.
Lemma lem1642664 (n : nat) : (term8 n) = True.
Proof. exact (EQ_MP (@lem1642232 n) (@lem1642231 n)). Qed.
Lemma lem1642665 : term35 = True.
Proof. exact (@lem1642664 0). Qed.
Lemma lem1642666 : term33 = True.
Proof. exact (TRANS (@lem1642662) (@lem1642665)). Qed.
Lemma lem1642667 : term31 = True.
Proof. exact (TRANS (@lem1642659) (@lem1642666)). Qed.
Lemma lem1642668 : term30 = True.
Proof. exact (TRANS (@lem1642656) (@lem1642667)). Qed.
Lemma lem1642669 : True = term30.
Proof. exact (SYM (@lem1642668)). Qed.
Lemma lem1642670 : term30.
Proof. exact (EQ_MP (@lem1642669) (@lem0)). Qed.
Lemma lem1642671 (n : nat) : (term36 n) = True.
Proof. exact (@lem1642653 n (@lem1642670)). Qed.
Lemma lem1642672 : term37 = term38.
Proof. exact (fun_ext (fun n : nat => @lem1642671 n)). Qed.
Lemma lem1642673 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1642674 : term39 = term40.
Proof. exact (MK_COMB (@lem1642673) (@lem1642672)). Qed.
Lemma lem1642676 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1642677 (t : Prop) : (term42 t) = t.
Proof. exact (@lem1642676 nat t). Qed.
Lemma lem1642678 : term40 = True.
Proof. exact (@lem1642677 True). Qed.
Lemma lem1642679 : term39 = True.
Proof. exact (TRANS (@lem1642674) (@lem1642678)). Qed.
Lemma lem1642680 : True = term39.
Proof. exact (SYM (@lem1642679)). Qed.
Lemma lem1642681 : term39.
Proof. exact (EQ_MP (@lem1642680) (@lem0)). Qed.
