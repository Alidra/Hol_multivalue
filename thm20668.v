Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20668_term_abbrevs.
Require Import thm795_spec.
Require Import thm824_spec.
Lemma lem20668 (r : Prop) (p : Prop) (q : Prop) : term0 r p q.
Proof. exact (conj (@lem795 q p r) (@lem824 p q)). Qed.
