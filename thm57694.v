Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm57694_term_abbrevs.
Require Import LET_END_DEF_spec.
Lemma lem57694 {A : Type'} (t : A) : term0 A t.
Proof. exact (@lem44139 A t). Qed.
