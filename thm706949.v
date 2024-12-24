Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm706949_term_abbrevs.
Require Import thm531147_spec.
Require Import thm531152_spec.
Lemma lem706949 : term0 = term1.
Proof. exact (TRANS (@lem531147) (@lem531152)). Qed.
