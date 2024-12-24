Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1099454_term_abbrevs.
Lemma lem1099454 {_25272 : Type'} : (@repeat_with_perm_args _25272) = (term0 _25272).
Proof. exact (@REPLICATE_def _25272). Qed.
