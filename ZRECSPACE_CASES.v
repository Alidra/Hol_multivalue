Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ZRECSPACE_CASES_term_abbrevs.
Require Import thm1058925_spec.
Lemma lem1058927 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem1058925 A)). Qed.