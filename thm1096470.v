Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1096470_term_abbrevs.
Lemma lem1096470 {A : Type'} : (@List.rev A) = (term0 A).
Proof. exact (@REVERSE_def A). Qed.
