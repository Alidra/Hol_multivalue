Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_UNIQ_term_abbrevs.
Require Import DIVMOD_UNIQ_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem169652 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : term0 m q r n.
Proof. exact (h1). Qed.
Lemma lem169653 (m : nat) : term1 m.
Proof. exact (@lem169651 m). Qed.
Lemma lem169654 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem169655 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem169654 m) (@lem169653 m)). Qed.
Lemma lem169656 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem169655 m n). Qed.
Lemma lem169657 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem169658 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem169657 m n) (@lem169656 m n)). Qed.
Lemma lem169659 (m : nat) (n : nat) (q : nat) : term5 m n q.
Proof. exact (@lem169658 m n q). Qed.
Lemma lem169660 (q : nat) (m : nat) (n : nat) : (term5 m n q) = (term6 q m n).
Proof. exact (eq_refl (term5 m n q)). Qed.
Lemma lem169661 (q : nat) (m : nat) (n : nat) : term6 q m n.
Proof. exact (EQ_MP (@lem169660 q m n) (@lem169659 m n q)). Qed.
Lemma lem169662 (q : nat) (m : nat) (n : nat) (r : nat) : term7 q m n r.
Proof. exact (@lem169661 q m n r). Qed.
Lemma lem169663 (q : nat) (m : nat) (n : nat) (r : nat) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem169666 (q : nat) (m : nat) (n : nat) (r : nat) : term8 q m n r.
Proof. exact (EQ_MP (@lem169663 q m n r) (@lem169662 q m n r)). Qed.
Lemma lem169667 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : term9 q m n r.
Proof. exact (@lem169666 q m n r (@lem169652 m q r n h1)). Qed.
Lemma lem169673 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : (Nat.modulo m n) = r.
Proof. exact (proj2 (@lem169667 m q r n h1)). Qed.
Lemma lem169674 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem169675 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : (term10 m n) = (@eq nat r).
Proof. exact (MK_COMB (@lem169674) (@lem169673 m q r n h1)). Qed.
Lemma lem169676 (r : nat) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem169677 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : ((Nat.modulo m n) = r) = (r = r).
Proof. exact (MK_COMB (@lem169675 m q r n h1) (@lem169676 r)). Qed.
Lemma lem169679 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem169680 (x : nat) : (x = x) = True.
Proof. exact (@lem169679 nat x). Qed.
Lemma lem169681 (r : nat) : (r = r) = True.
Proof. exact (@lem169680 r). Qed.
Lemma lem169682 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : ((Nat.modulo m n) = r) = True.
Proof. exact (TRANS (@lem169677 m q r n h1) (@lem169681 r)). Qed.
Lemma lem169683 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : True = ((Nat.modulo m n) = r).
Proof. exact (SYM (@lem169682 m q r n h1)). Qed.
Lemma lem169684 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0 m q r n) : (Nat.modulo m n) = r.
Proof. exact (EQ_MP (@lem169683 m q r n h1) (@lem0)). Qed.
Lemma lem169685 (q : nat) (m : nat) (n : nat) (r : nat) : term11 q m n r.
Proof. exact (fun h0 : term0 m q r n => @lem169684 m q r n h0). Qed.
Lemma lem169690 (q : nat) (m : nat) (n : nat) : term12 q m n.
Proof. exact (fun r : nat => @lem169685 q m n r). Qed.
Lemma lem169695 (m : nat) (n : nat) : term13 m n.
Proof. exact (fun q : nat => @lem169690 q m n). Qed.
Lemma lem169700 (m : nat) : term14 m.
Proof. exact (fun n : nat => @lem169695 m n). Qed.
Lemma lem169705 : term15.
Proof. exact (fun m : nat => @lem169700 m). Qed.
