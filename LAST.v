Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LAST_term_abbrevs.
Require Import thm1098347_spec.
Require Import thm1098348_spec.
Lemma lem1098349 {A : Type'} (h : A) (t : list A) : (term0 A h t) = (term1 A h t).
Proof. exact (EQ_MP (@lem1098348 A h t) (@lem1098347 A h t)). Qed.
