Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm706885_term_abbrevs.
Require Import thm528081_spec.
Require Import thm528090_spec.
Lemma lem706885 : term0 = term1.
Proof. exact (TRANS (@lem528081) (@lem528090)). Qed.
