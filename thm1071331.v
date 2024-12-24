Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1071331_term_abbrevs.
Lemma lem1071331 {A : Type'} : (@nil A) = (term0 A).
Proof. exact (@NIL_def A). Qed.
