Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm272790_term_abbrevs.
Require Import REFL_CLAUSE_spec.
Lemma lem272790 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem317 A x). Qed.