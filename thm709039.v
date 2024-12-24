Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm709039_term_abbrevs.
Require Import thm708952_spec.
Require Import thm708955_spec.
Require Import thm708956_spec.
Lemma lem709033 (n : nat) : (term0 n) = (term1 n).
Proof. exact (EQ_MP (@lem708956 n) (@lem708955 n)). Qed.
Lemma lem709034 : term2 = term3.
Proof. exact (@lem709033 0). Qed.
Lemma lem709036 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem708952)). Qed.
Lemma lem709037 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem709038 : term3 = term4.
Proof. exact (MK_COMB (@lem709037) (@lem709036)). Qed.
Lemma lem709039 : term2 = term4.
Proof. exact (TRANS (@lem709034) (@lem709038)). Qed.
