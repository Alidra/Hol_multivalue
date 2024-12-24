Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183074_term_abbrevs.
Require Import GSPEC_spec.
Lemma lem3183074 {A : Type'} (p : A -> Prop) : term0 A p.
Proof. exact (@lem3182122 A p). Qed.
