Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2530573_term_abbrevs.
Require Import thm2528714_spec.
Require Import thm2529651_spec.
Lemma lem2530573 (p : int) (m : int) (n : int) : term0 p m n.
Proof. exact (@lem2529651 p m n (@lem2528714 m n p)). Qed.
