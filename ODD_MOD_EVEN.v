Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ODD_MOD_EVEN_term_abbrevs.
Require Import EVEN_MOD_EVEN_spec.
Require Import NOT_EVEN_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem204572 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (h1). Qed.
Lemma lem204573 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (SYM (@lem204572 n h1)). Qed.
Lemma lem204574 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem204575 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem204574 n h1)). Qed.
Lemma lem204576 (n : nat) : ((term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n) => @lem204573 n h1) (fun h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n) => @lem204575 n h1)). Qed.
Lemma lem204577 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem204576 n)). Qed.
Lemma lem204578 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem204579 : term3 = term4.
Proof. exact (MK_COMB (@lem204578) (@lem204577)). Qed.
Lemma lem204580 : term4.
Proof. exact (EQ_MP (@lem204579) (@lem124715)). Qed.
Lemma lem204581 (m : nat) : term5 m.
Proof. exact (@lem204570 m). Qed.
Lemma lem204582 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem204583 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem204582 m) (@lem204581 m)). Qed.
Lemma lem204584 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem204583 m n). Qed.
Lemma lem204585 (n : nat) (m : nat) : (term7 m n) = (term8 n m).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem204586 (n : nat) (m : nat) : term8 n m.
Proof. exact (EQ_MP (@lem204585 n m) (@lem204584 m n)). Qed.
Lemma lem204587 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem204588 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term9 m n) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem204586 n m (@lem204587 n h1)). Qed.
Lemma lem204594 (n : nat) : term10 n.
Proof. exact (@lem204580 n). Qed.
Lemma lem204595 (n : nat) : (term10 n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)).
Proof. exact (eq_refl (term10 n)). Qed.
Lemma lem204608 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term11 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem204609 (p : Prop) (q : Prop) (p' : Prop) : term12 p q p'.
Proof. exact (fun q' : Prop => @lem204608 p q p' q'). Qed.
Lemma lem204610 (p : Prop) (q : Prop) : term13 p q.
Proof. exact (fun p' : Prop => @lem204609 p q p'). Qed.
Lemma lem204611 (n : nat) (m : nat) : term14 n m.
Proof. exact (@lem204610 (Coq.Arith.PeanoNat.Nat.Even n) ((term15 m n) = (Coq.Arith.PeanoNat.Nat.Odd m))). Qed.
Lemma lem204612 (n : nat) (m : nat) (p' : Prop) : term16 n m p'.
Proof. exact (@lem204611 n m p'). Qed.
Lemma lem204613 (n : nat) (m : nat) (p' : Prop) : (term16 n m p') = (term17 n m p').
Proof. exact (eq_refl (term16 n m p')). Qed.
Lemma lem204614 (n : nat) (m : nat) (p' : Prop) : term17 n m p'.
Proof. exact (EQ_MP (@lem204613 n m p') (@lem204612 n m p')). Qed.
Lemma lem204615 (n : nat) (m : nat) (p' : Prop) (q' : Prop) : term18 n m p' q'.
Proof. exact (@lem204614 n m p' q'). Qed.
Lemma lem204616 (n : nat) (m : nat) (p' : Prop) (q' : Prop) : (term18 n m p' q') = (term19 n m p' q').
Proof. exact (eq_refl (term18 n m p' q')). Qed.
Lemma lem204617 (n : nat) (m : nat) (p' : Prop) (q' : Prop) : term19 n m p' q'.
Proof. exact (EQ_MP (@lem204616 n m p' q') (@lem204615 n m p' q')). Qed.
Lemma lem204618 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem204619 (m : nat) (n : nat) (q' : Prop) : term20 m n q'.
Proof. exact (@lem204617 n m (Coq.Arith.PeanoNat.Nat.Even n) q'). Qed.
Lemma lem204620 (m : nat) (n : nat) (q' : Prop) : term21 m n q'.
Proof. exact (@lem204619 m n q' (@lem204618 n)). Qed.
Lemma lem204621 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem204622 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = ((Coq.Arith.PeanoNat.Nat.Even n) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem204627 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem204595 n) (@lem204594 n)). Qed.
Lemma lem204628 (m : nat) (n : nat) : (term15 m n) = (term22 m n).
Proof. exact (@lem204627 (Nat.modulo m n)). Qed.
Lemma lem204630 (n : nat) (m : nat) : term8 n m.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem204588 m n h0). Qed.
Lemma lem204632 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (Coq.Arith.PeanoNat.Nat.Even n) = True.
Proof. exact (EQ_MP (@lem204622 n) (@lem204621 n h1)). Qed.
Lemma lem204633 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : True = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (SYM (@lem204632 n h1)). Qed.
Lemma lem204634 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem204633 n h1) (@lem0)). Qed.
Lemma lem204635 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term9 m n) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem204630 n m (@lem204634 n h1)). Qed.
Lemma lem204636 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem204637 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term22 m n) = (term0 m).
Proof. exact (MK_COMB (@lem204636) (@lem204635 m n h1)). Qed.
Lemma lem204638 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term15 m n) = (term0 m).
Proof. exact (TRANS (@lem204628 m n) (@lem204637 m n h1)). Qed.
Lemma lem204639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem204640 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term23 m n) = (term24 m).
Proof. exact (MK_COMB (@lem204639) (@lem204638 m n h1)). Qed.
Lemma lem204642 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem204595 n) (@lem204594 n)). Qed.
Lemma lem204643 (m : nat) : (Coq.Arith.PeanoNat.Nat.Odd m) = (term0 m).
Proof. exact (@lem204642 m). Qed.
Lemma lem204644 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : ((term15 m n) = (Coq.Arith.PeanoNat.Nat.Odd m)) = ((term0 m) = (term0 m)).
Proof. exact (MK_COMB (@lem204640 m n h1) (@lem204643 m)). Qed.
Lemma lem204646 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem204647 (x : Prop) : (x = x) = True.
Proof. exact (@lem204646 Prop x). Qed.
Lemma lem204648 (m : nat) : ((term0 m) = (term0 m)) = True.
Proof. exact (@lem204647 (term0 m)). Qed.
Lemma lem204649 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : ((term15 m n) = (Coq.Arith.PeanoNat.Nat.Odd m)) = True.
Proof. exact (TRANS (@lem204644 m n h1) (@lem204648 m)). Qed.
Lemma lem204650 (n : nat) (m : nat) : term25 n m.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem204649 m n h0). Qed.
Lemma lem204651 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem204620 m n True). Qed.
Lemma lem204652 (m : nat) (n : nat) : (term27 n m) = (term28 n).
Proof. exact (@lem204651 m n (@lem204650 n m)). Qed.
Lemma lem204654 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem204655 (n : nat) : (term28 n) = True.
Proof. exact (@lem204654 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem204656 (n : nat) (m : nat) : (term27 n m) = True.
Proof. exact (TRANS (@lem204652 m n) (@lem204655 n)). Qed.
Lemma lem204657 (m : nat) : (term29 m) = term30.
Proof. exact (fun_ext (fun n : nat => @lem204656 n m)). Qed.
Lemma lem204658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem204659 (m : nat) : (term31 m) = term32.
Proof. exact (MK_COMB (@lem204658) (@lem204657 m)). Qed.
Lemma lem204661 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem204662 (t : Prop) : (term34 t) = t.
Proof. exact (@lem204661 nat t). Qed.
Lemma lem204663 : term32 = True.
Proof. exact (@lem204662 True). Qed.
Lemma lem204664 (m : nat) : (term31 m) = True.
Proof. exact (TRANS (@lem204659 m) (@lem204663)). Qed.
Lemma lem204665 : term35 = term30.
Proof. exact (fun_ext (fun m : nat => @lem204664 m)). Qed.
Lemma lem204666 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem204667 : term36 = term32.
Proof. exact (MK_COMB (@lem204666) (@lem204665)). Qed.
Lemma lem204669 {A : Type'} (t : Prop) : (term33 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem204670 (t : Prop) : (term34 t) = t.
Proof. exact (@lem204669 nat t). Qed.
Lemma lem204671 : term32 = True.
Proof. exact (@lem204670 True). Qed.
Lemma lem204672 : term36 = True.
Proof. exact (TRANS (@lem204667) (@lem204671)). Qed.
Lemma lem204673 : True = term36.
Proof. exact (SYM (@lem204672)). Qed.
Lemma lem204674 : term36.
Proof. exact (EQ_MP (@lem204673) (@lem0)). Qed.
