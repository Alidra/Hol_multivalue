Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm706883_term_abbrevs.
Require Import thm528000_spec.
Lemma lem706883 : term0 = (BIT1 0).
Proof. exact (@lem528000 0). Qed.
