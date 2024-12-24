Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm709031_term_abbrevs.
Require Import ARITH_ADD_spec.
Lemma lem708967 : term0.
Proof. exact (proj2 (@lem514291)). Qed.
Lemma lem708968 : term1.
Proof. exact (proj2 (@lem708967)). Qed.
Lemma lem708969 : term2.
Proof. exact (proj2 (@lem708968)). Qed.
Lemma lem709011 : term3.
Proof. exact (proj1 (@lem708969)). Qed.
Lemma lem709012 (n : nat) : term4 n.
Proof. exact (@lem709011 n). Qed.
Lemma lem709013 (n : nat) : (term4 n) = ((term5 n) = (BIT1 n)).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem709028 (n : nat) : (term5 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem709013 n) (@lem709012 n)). Qed.
Lemma lem709029 : term6 = (BIT1 0).
Proof. exact (@lem709028 0). Qed.
Lemma lem709030 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem709031 : term7 = term8.
Proof. exact (MK_COMB (@lem709030) (@lem709029)). Qed.
