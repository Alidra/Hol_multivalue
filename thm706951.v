Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm706951_term_abbrevs.
Require Import thm531233_spec.
Require Import thm531248_spec.
Lemma lem706951 : term0 = term1.
Proof. exact (TRANS (@lem531233) (@lem531248)). Qed.
