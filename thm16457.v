Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16457_term_abbrevs.
Require Import FORALL_SIMP_spec.
Lemma lem16457 {A : Type'} (t : Prop) : term0 A t.
Proof. exact (@lem1096 A t). Qed.