Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm708946_term_abbrevs.
Require Import ARITH_ADD_spec.
Lemma lem708883 : term0.
Proof. exact (proj2 (@lem514291)). Qed.
Lemma lem708944 : (Nat.add 0 0) = 0.
Proof. exact (proj1 (@lem708883)). Qed.
Lemma lem708945 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem708946 : term1 = (S 0).
Proof. exact (MK_COMB (@lem708945) (@lem708944)). Qed.
