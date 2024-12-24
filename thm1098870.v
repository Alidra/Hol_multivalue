Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1098870_term_abbrevs.
Lemma lem1098870 {_25251 : Type'} : (@List.removelast _25251) = (term0 _25251).
Proof. exact (@BUTLAST_def _25251). Qed.
