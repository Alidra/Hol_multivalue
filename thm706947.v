Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm706947_term_abbrevs.
Require Import thm531066_spec.
Lemma lem706947 : term0 = term1.
Proof. exact (@lem531066 (BIT1 0)). Qed.
