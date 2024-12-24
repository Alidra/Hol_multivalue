Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm706821_term_abbrevs.
Require Import thm525520_spec.
Lemma lem706821 : term0 = (BIT1 0).
Proof. exact (@lem525520 0). Qed.
