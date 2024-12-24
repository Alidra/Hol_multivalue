Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1106492_term_abbrevs.
Lemma lem1106492 {_25594 : Type'} : (@FILTER _25594) = (term0 _25594).
Proof. exact (@FILTER_def _25594). Qed.
