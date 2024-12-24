Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1110672_term_abbrevs.
Require Import thm1110669_spec.
Lemma lem1110671 {A : Type'} : term0 A.
Proof. exact (proj1 (@lem1110669 A)). Qed.
Lemma lem1110672 {A : Type'} (r : type1402 A) : term1 A r.
Proof. exact (@lem1110671 A r). Qed.
