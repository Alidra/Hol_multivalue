Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337537_term_abbrevs.
Require Import thm1337531_spec.
Require Import thm1337536_spec.
Lemma lem1337537 (m : nat) : (term0 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
