Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm712026_term_abbrevs.
Require Import thm711939_spec.
Require Import thm711942_spec.
Require Import thm711943_spec.
Lemma lem712020 (n : nat) : (term0 n) = (term1 n).
Proof. exact (EQ_MP (@lem711943 n) (@lem711942 n)). Qed.
Lemma lem712021 : term2 = term3.
Proof. exact (@lem712020 0). Qed.
Lemma lem712023 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem711939)). Qed.
Lemma lem712024 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem712025 : term3 = term4.
Proof. exact (MK_COMB (@lem712024) (@lem712023)). Qed.
Lemma lem712026 : term2 = term4.
Proof. exact (TRANS (@lem712021) (@lem712025)). Qed.
