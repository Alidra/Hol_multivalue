Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_PASTECART_term_abbrevs.
Require Import thm7662554_spec.
Require Import thm7664352_spec.
Lemma lem7664353 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term0 _140476 _140477 _140478 P) = (term1 _140476 _140477 _140478 P).
Proof. exact (EQ_MP (@lem7662554 _140476 _140477 _140478 P) (@lem7664352 _140476 _140477 _140478 P)). Qed.
