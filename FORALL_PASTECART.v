Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_PASTECART_term_abbrevs.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem7662540 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term0 _140454 _140455 _140456 P) = (term1 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
