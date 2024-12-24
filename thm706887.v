Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm706887_term_abbrevs.
Require Import thm528171_spec.
Require Import thm528176_spec.
Lemma lem706887 : term0 = term1.
Proof. exact (TRANS (@lem528171) (@lem528176)). Qed.
