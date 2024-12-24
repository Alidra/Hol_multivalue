Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_OF_NUM_WELLDEF_term_abbrevs.
Require Import TREAL_EQ_REFL_spec.
Lemma lem1332640 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem1332641 (n : nat) : (term0 n) = (term0 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1332642 (m : nat) (n : nat) (h1 : m = n) : (term1 n m) = (term2 n).
Proof. exact (MK_COMB (@lem1332641 n) (@lem1332640 m n h1)). Qed.
Lemma lem1332643 (n : nat) : (term2 n) = (term3 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1332644 (n : nat) (m : nat) : (term4 n m) = (term4 n m).
Proof. exact (eq_refl (term4 n m)). Qed.
Lemma lem1332645 (m : nat) (n : nat) : ((term1 n m) = (term2 n)) = ((term1 n m) = (term3 n)).
Proof. exact (MK_COMB (@lem1332644 n m) (@lem1332643 n)). Qed.
Lemma lem1332646 (m : nat) (n : nat) : (term1 n m) = (term5 m n).
Proof. exact (eq_refl (term1 n m)). Qed.
Lemma lem1332647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1332648 (m : nat) (n : nat) : (term4 n m) = (term6 m n).
Proof. exact (MK_COMB (@lem1332647) (@lem1332646 m n)). Qed.
Lemma lem1332649 (n : nat) : (term3 n) = (term3 n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem1332650 (m : nat) (n : nat) : ((term1 n m) = (term3 n)) = ((term5 m n) = (term3 n)).
Proof. exact (MK_COMB (@lem1332648 m n) (@lem1332649 n)). Qed.
Lemma lem1332651 (m : nat) (n : nat) : ((term1 n m) = (term2 n)) = ((term5 m n) = (term3 n)).
Proof. exact (TRANS (@lem1332645 m n) (@lem1332650 m n)). Qed.
Lemma lem1332652 (m : nat) (n : nat) (h1 : m = n) : (term5 m n) = (term3 n).
Proof. exact (EQ_MP (@lem1332651 m n) (@lem1332642 m n h1)). Qed.
Lemma lem1332653 (m : nat) (n : nat) (h1 : m = n) : (term3 n) = (term5 m n).
Proof. exact (SYM (@lem1332652 m n h1)). Qed.
Lemma lem1332654 (x : prod hreal hreal) : term7 x.
Proof. exact (@lem1326193 x). Qed.
Lemma lem1332655 (x : prod hreal hreal) : (term7 x) = (treal_eq x x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1332658 (x : prod hreal hreal) : treal_eq x x.
Proof. exact (EQ_MP (@lem1332655 x) (@lem1332654 x)). Qed.
Lemma lem1332659 (n : nat) : term3 n.
Proof. exact (@lem1332658 (treal_of_num n)). Qed.
Lemma lem1332660 (m : nat) (n : nat) (h1 : m = n) : term5 m n.
Proof. exact (EQ_MP (@lem1332653 m n h1) (@lem1332659 n)). Qed.
Lemma lem1332661 (m : nat) (n : nat) : term8 m n.
Proof. exact (fun h0 : m = n => @lem1332660 m n h0). Qed.
Lemma lem1332666 (m : nat) : term9 m.
Proof. exact (fun n : nat => @lem1332661 m n). Qed.
Lemma lem1332671 : term10.
Proof. exact (fun m : nat => @lem1332666 m). Qed.
