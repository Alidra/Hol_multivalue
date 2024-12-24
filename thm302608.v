Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302608_term_abbrevs.
Require Import thm302583_spec.
Require Import thm302584_spec.
Lemma lem302600 (n : nat) : (BIT1 n) = (term0 n).
Proof. exact (EQ_MP (@lem302584 n) (@lem302583 n)). Qed.
Lemma lem302601 (m : nat) : (BIT1 m) = (term0 m).
Proof. exact (@lem302600 m). Qed.
Lemma lem302602 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem302603 (m : nat) : (term1 m) = (term2 m).
Proof. exact (MK_COMB (@lem302602) (@lem302601 m)). Qed.
Lemma lem302604 (n : nat) : (term3 n) = (term3 n).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem302605 (m : nat) (n : nat) : ((BIT1 m) = (term3 n)) = ((term0 m) = (term3 n)).
Proof. exact (MK_COMB (@lem302603 m) (@lem302604 n)). Qed.
Lemma lem302606 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem302607 (m : nat) (n : nat) : ((m = n) = ((BIT1 m) = (term3 n))) = ((m = n) = ((term0 m) = (term3 n))).
Proof. exact (MK_COMB (@lem302606 m n) (@lem302605 m n)). Qed.
Lemma lem302608 (m : nat) (n : nat) : ((m = n) = ((term0 m) = (term3 n))) = ((m = n) = ((BIT1 m) = (term3 n))).
Proof. exact (SYM (@lem302607 m n)). Qed.
