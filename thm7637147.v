Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7637147_term_abbrevs.
Lemma lem7637147 {A : Type'} (s : A -> Prop) : (term0 A s) = ((@dimindex A s) = (@dimindex A (@UNIV A))).
Proof. exact (eq_refl (term0 A s)). Qed.
