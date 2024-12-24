Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm715609_term_abbrevs.
Require Import ARITH_ADD_spec.
Lemma lem715545 : term0.
Proof. exact (proj2 (@lem514291)). Qed.
Lemma lem715546 : term1.
Proof. exact (proj2 (@lem715545)). Qed.
Lemma lem715547 : term2.
Proof. exact (proj2 (@lem715546)). Qed.
Lemma lem715548 : term3.
Proof. exact (proj2 (@lem715547)). Qed.
Lemma lem715585 : term4.
Proof. exact (proj1 (@lem715548)). Qed.
Lemma lem715586 (n : nat) : term5 n.
Proof. exact (@lem715585 n). Qed.
Lemma lem715587 (n : nat) : (term5 n) = ((term6 n) = (BIT0 n)).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem715606 (n : nat) : (term6 n) = (BIT0 n).
Proof. exact (EQ_MP (@lem715587 n) (@lem715586 n)). Qed.
Lemma lem715607 : term7 = term8.
Proof. exact (@lem715606 (BIT1 0)). Qed.
Lemma lem715608 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem715609 : term9 = term10.
Proof. exact (MK_COMB (@lem715608) (@lem715607)). Qed.
