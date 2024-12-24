Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm647_term_abbrevs.
Require Import thm618_spec.
Require Import thm646_spec.
Lemma lem647 (r : Prop) (p : Prop) (q : Prop) : term0 r p q.
Proof. exact (conj (@lem618 q p r) (@lem646 p q)). Qed.
