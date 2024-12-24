Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_EVEN_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm124233_spec.
Require Import thm124616_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem124621 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem124622 : term1.
Proof. exact (@lem124621 term2). Qed.
Lemma lem124623 : term3 = (term4 = term5).
Proof. exact (eq_refl term3). Qed.
Lemma lem124624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem124625 : term6 = term7.
Proof. exact (MK_COMB (@lem124624) (@lem124623)). Qed.
Lemma lem124626 (n : nat) : (term8 n) = ((term9 n) = (Coq.Arith.PeanoNat.Nat.Odd n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem124627 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem124628 (n : nat) : (term10 n) = (term11 n).
Proof. exact (MK_COMB (@lem124627) (@lem124626 n)). Qed.
Lemma lem124629 (n : nat) : (term12 n) = ((term13 n) = (term14 n)).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem124630 (n : nat) : (term15 n) = (term16 n).
Proof. exact (MK_COMB (@lem124628 n) (@lem124629 n)). Qed.
Lemma lem124631 : term17 = term18.
Proof. exact (fun_ext (fun n : nat => @lem124630 n)). Qed.
Lemma lem124632 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem124633 : term19 = term20.
Proof. exact (MK_COMB (@lem124632) (@lem124631)). Qed.
Lemma lem124634 : term21 = term22.
Proof. exact (MK_COMB (@lem124625) (@lem124633)). Qed.
Lemma lem124635 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem124636 : term23 = term24.
Proof. exact (MK_COMB (@lem124635) (@lem124634)). Qed.
Lemma lem124637 (n : nat) : (term8 n) = ((term9 n) = (Coq.Arith.PeanoNat.Nat.Odd n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem124638 : term25 = term2.
Proof. exact (fun_ext (fun n : nat => @lem124637 n)). Qed.
Lemma lem124639 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem124640 : term26 = term27.
Proof. exact (MK_COMB (@lem124639) (@lem124638)). Qed.
Lemma lem124641 : term1 = term28.
Proof. exact (MK_COMB (@lem124636) (@lem124640)). Qed.
Lemma lem124642 : term28.
Proof. exact (EQ_MP (@lem124641) (@lem124622)). Qed.
Lemma lem124657 : term29 = True.
Proof. exact (proj1 (@lem124233)). Qed.
Lemma lem124658 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem124659 : term4 = (~ True).
Proof. exact (MK_COMB (@lem124658) (@lem124657)). Qed.
Lemma lem124661 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem124662 : term4 = False.
Proof. exact (TRANS (@lem124659) (@lem124661)). Qed.
Lemma lem124663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem124664 : term30 = (@eq Prop False).
Proof. exact (MK_COMB (@lem124663) (@lem124662)). Qed.
Lemma lem124666 : term5 = False.
Proof. exact (proj1 (@lem124616)). Qed.
Lemma lem124667 : (term4 = term5) = (False = False).
Proof. exact (MK_COMB (@lem124664) (@lem124666)). Qed.
Lemma lem124669 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem124670 : (False = False) = (~ False).
Proof. exact (@lem124669 False). Qed.
Lemma lem124672 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem124673 : (False = False) = True.
Proof. exact (TRANS (@lem124670) (@lem124672)). Qed.
Lemma lem124674 : (term4 = term5) = True.
Proof. exact (TRANS (@lem124667) (@lem124673)). Qed.
Lemma lem124675 : True = (term4 = term5).
Proof. exact (SYM (@lem124674)). Qed.
Lemma lem124676 : term4 = term5.
Proof. exact (EQ_MP (@lem124675) (@lem0)). Qed.
Lemma lem124677 : term31.
Proof. exact (proj2 (@lem124616)). Qed.
Lemma lem124678 (n : nat) : term32 n.
Proof. exact (@lem124677 n). Qed.
Lemma lem124679 (n : nat) : (term32 n) = ((term14 n) = (term33 n)).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem124682 : term34.
Proof. exact (proj2 (@lem124233)). Qed.
Lemma lem124683 (n : nat) : term35 n.
Proof. exact (@lem124682 n). Qed.
Lemma lem124684 (n : nat) : (term35 n) = ((term36 n) = (term9 n)).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem124690 (n : nat) : (term36 n) = (term9 n).
Proof. exact (EQ_MP (@lem124684 n) (@lem124683 n)). Qed.
Lemma lem124692 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term9 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (h1). Qed.
Lemma lem124693 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term36 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (TRANS (@lem124690 n) (@lem124692 n h1)). Qed.
Lemma lem124694 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem124695 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term13 n) = (term33 n).
Proof. exact (MK_COMB (@lem124694) (@lem124693 n h1)). Qed.
Lemma lem124696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem124697 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem124696) (@lem124695 n h1)). Qed.
Lemma lem124699 (n : nat) : (term14 n) = (term33 n).
Proof. exact (EQ_MP (@lem124679 n) (@lem124678 n)). Qed.
Lemma lem124700 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : ((term13 n) = (term14 n)) = ((term33 n) = (term33 n)).
Proof. exact (MK_COMB (@lem124697 n h1) (@lem124699 n)). Qed.
Lemma lem124702 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem124703 (x : Prop) : (x = x) = True.
Proof. exact (@lem124702 Prop x). Qed.
Lemma lem124704 (n : nat) : ((term33 n) = (term33 n)) = True.
Proof. exact (@lem124703 (term33 n)). Qed.
Lemma lem124705 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : ((term13 n) = (term14 n)) = True.
Proof. exact (TRANS (@lem124700 n h1) (@lem124704 n)). Qed.
Lemma lem124706 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : True = ((term13 n) = (term14 n)).
Proof. exact (SYM (@lem124705 n h1)). Qed.
Lemma lem124707 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term13 n) = (term14 n).
Proof. exact (EQ_MP (@lem124706 n h1) (@lem0)). Qed.
Lemma lem124708 (n : nat) : term16 n.
Proof. exact (fun h0 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Odd n) => @lem124707 n h0). Qed.
Lemma lem124713 : term20.
Proof. exact (fun n : nat => @lem124708 n). Qed.
Lemma lem124714 : term22.
Proof. exact (conj (@lem124676) (@lem124713)). Qed.
Lemma lem124715 : term27.
Proof. exact (@lem124642 (@lem124714)). Qed.
