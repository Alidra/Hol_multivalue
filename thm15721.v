Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm15721_term_abbrevs.
Lemma lem15721 (a : unit) : (term0 a) = a.
Proof. exact (@axiom_2 a). Qed.
