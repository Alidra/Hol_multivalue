Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528176_term_abbrevs.
Require Import thm528154_spec.
Require Import thm528155_spec.
Lemma lem528173 (n : nat) : (term0 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem528155 n) (@lem528154 n)). Qed.
Lemma lem528174 : term1 = (BIT1 0).
Proof. exact (@lem528173 0). Qed.
Lemma lem528175 : BIT1 = BIT1.
Proof. exact (eq_refl BIT1). Qed.
Lemma lem528176 : term2 = term3.
Proof. exact (MK_COMB (@lem528175) (@lem528174)). Qed.
