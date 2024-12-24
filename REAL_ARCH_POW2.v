Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ARCH_POW2_term_abbrevs.
Require Import REAL_ARCH_POW_spec.
Require Import REAL_OF_NUM_LT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm520356_spec.
Require Import thm7_spec.
Lemma lem1707193 : term0.
Proof. exact (EQ_MP (@lem520356) (@lem0)). Qed.
Lemma lem1707194 : term1.
Proof. exact (proj2 (@lem1707193)). Qed.
Lemma lem1707195 : term2.
Proof. exact (proj2 (@lem1707194)). Qed.
Lemma lem1707196 : term3.
Proof. exact (proj2 (@lem1707195)). Qed.
Lemma lem1707197 : term4.
Proof. exact (proj2 (@lem1707196)). Qed.
Lemma lem1707198 : term5.
Proof. exact (proj2 (@lem1707197)). Qed.
Lemma lem1707199 : term6.
Proof. exact (proj2 (@lem1707198)). Qed.
Lemma lem1707200 : term7.
Proof. exact (proj2 (@lem1707199)). Qed.
Lemma lem1707201 : term8.
Proof. exact (proj2 (@lem1707200)). Qed.
Lemma lem1707209 : term9.
Proof. exact (proj1 (@lem1707201)). Qed.
Lemma lem1707210 (m : nat) : term10 m.
Proof. exact (@lem1707209 m). Qed.
Lemma lem1707211 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem1707212 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem1707211 m) (@lem1707210 m)). Qed.
Lemma lem1707213 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem1707212 m n). Qed.
Lemma lem1707214 (m : nat) (n : nat) : (term12 m n) = ((term13 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem1707230 : term14.
Proof. exact (proj1 (@lem1707198)). Qed.
Lemma lem1707231 (n : nat) : term15 n.
Proof. exact (@lem1707230 n). Qed.
Lemma lem1707232 (n : nat) : (term15 n) = ((term16 n) = True).
Proof. exact (eq_refl (term15 n)). Qed.
Lemma lem1707247 : term17.
Proof. exact (proj1 (@lem1707193)). Qed.
Lemma lem1707248 (m : nat) : term18 m.
Proof. exact (@lem1707247 m). Qed.
Lemma lem1707249 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1707250 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem1707249 m) (@lem1707248 m)). Qed.
Lemma lem1707251 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem1707250 m n). Qed.
Lemma lem1707252 (m : nat) (n : nat) : (term20 m n) = ((term21 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1707626 (m : nat) : term22 m.
Proof. exact (@lem1483667 m). Qed.
Lemma lem1707627 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem1707628 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem1707627 m) (@lem1707626 m)). Qed.
Lemma lem1707629 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem1707628 m n). Qed.
Lemma lem1707630 (m : nat) (n : nat) : (term24 m n) = ((term25 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem1707632 (x : real) : term26 x.
Proof. exact (@lem1706981 x). Qed.
Lemma lem1707633 (x : real) : (term26 x) = (term27 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1707634 (x : real) : term27 x.
Proof. exact (EQ_MP (@lem1707633 x) (@lem1707632 x)). Qed.
Lemma lem1707635 (x : real) (y : real) : term28 x y.
Proof. exact (@lem1707634 x y). Qed.
Lemma lem1707636 (y : real) (x : real) : (term28 x y) = (term29 y x).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem1707637 (y : real) (x : real) : term29 y x.
Proof. exact (EQ_MP (@lem1707636 y x) (@lem1707635 x y)). Qed.
Lemma lem1707638 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1707639 (y : real) (x : real) (h1 : term30 x) : term31 y x.
Proof. exact (@lem1707637 y x (@lem1707638 x h1)). Qed.
Lemma lem1707640 (y : real) (x : real) : (term31 y x) = ((term31 y x) = True).
Proof. exact (@lem7 (term31 y x)). Qed.
Lemma lem1707641 (y : real) (x : real) (h1 : term30 x) : (term31 y x) = True.
Proof. exact (EQ_MP (@lem1707640 y x) (@lem1707639 y x h1)). Qed.
Lemma lem1707652 (y : real) (x : real) : term32 y x.
Proof. exact (fun h0 : term30 x => @lem1707641 y x h0). Qed.
Lemma lem1707653 (x : real) : term33 x.
Proof. exact (@lem1707652 x term34). Qed.
Lemma lem1707655 (m : nat) (n : nat) : (term25 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1707630 m n) (@lem1707629 m n)). Qed.
Lemma lem1707656 : term35 = term36.
Proof. exact (@lem1707655 term37 term38). Qed.
Lemma lem1707658 (m : nat) (n : nat) : (term21 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1707252 m n) (@lem1707251 m n)). Qed.
Lemma lem1707659 : term36 = term39.
Proof. exact (@lem1707658 (BIT1 0) term40). Qed.
Lemma lem1707661 (m : nat) (n : nat) : (term13 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1707214 m n) (@lem1707213 m n)). Qed.
Lemma lem1707662 : term39 = term41.
Proof. exact (@lem1707661 0 (BIT1 0)). Qed.
Lemma lem1707664 (n : nat) : (term16 n) = True.
Proof. exact (EQ_MP (@lem1707232 n) (@lem1707231 n)). Qed.
Lemma lem1707665 : term41 = True.
Proof. exact (@lem1707664 0). Qed.
Lemma lem1707666 : term39 = True.
Proof. exact (TRANS (@lem1707662) (@lem1707665)). Qed.
Lemma lem1707667 : term36 = True.
Proof. exact (TRANS (@lem1707659) (@lem1707666)). Qed.
Lemma lem1707668 : term35 = True.
Proof. exact (TRANS (@lem1707656) (@lem1707667)). Qed.
Lemma lem1707669 : True = term35.
Proof. exact (SYM (@lem1707668)). Qed.
Lemma lem1707670 : term35.
Proof. exact (EQ_MP (@lem1707669) (@lem0)). Qed.
Lemma lem1707671 (x : real) : (term42 x) = True.
Proof. exact (@lem1707653 x (@lem1707670)). Qed.
Lemma lem1707672 : term43 = term44.
Proof. exact (fun_ext (fun x : real => @lem1707671 x)). Qed.
Lemma lem1707673 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1707674 : term45 = term46.
Proof. exact (MK_COMB (@lem1707673) (@lem1707672)). Qed.
Lemma lem1707676 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1707677 (t : Prop) : (term48 t) = t.
Proof. exact (@lem1707676 real t). Qed.
Lemma lem1707678 : term46 = True.
Proof. exact (@lem1707677 True). Qed.
Lemma lem1707679 : term45 = True.
Proof. exact (TRANS (@lem1707674) (@lem1707678)). Qed.
Lemma lem1707680 : True = term45.
Proof. exact (SYM (@lem1707679)). Qed.
Lemma lem1707681 : term45.
Proof. exact (EQ_MP (@lem1707680) (@lem0)). Qed.
