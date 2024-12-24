Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm531152_term_abbrevs.
Require Import thm531122_spec.
Require Import thm531123_spec.
Lemma lem531149 (n : nat) : (term0 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem531123 n) (@lem531122 n)). Qed.
Lemma lem531150 : term1 = (BIT1 0).
Proof. exact (@lem531149 0). Qed.
Lemma lem531151 : BIT1 = BIT1.
Proof. exact (eq_refl BIT1). Qed.
Lemma lem531152 : term2 = term3.
Proof. exact (MK_COMB (@lem531151) (@lem531150)). Qed.
