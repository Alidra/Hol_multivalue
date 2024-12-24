Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367248_term_abbrevs.
Require Import thm1367246_spec.
Lemma lem1367248 (m : nat) (n : nat) : term0 m n.
Proof. exact (proj1 (@lem1367246 m n)). Qed.
