Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm646_term_abbrevs.
Require Import thm628_spec.
Require Import thm645_spec.
Lemma lem646 (p : Prop) (q : Prop) : term0 p q.
Proof. exact (conj (@lem628 p) (@lem645 p q)). Qed.
