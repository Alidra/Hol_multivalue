Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841591_term_abbrevs.
Require Import int_of_num_th_spec.
Lemma lem2841591 (n : nat) : term0 n.
Proof. exact (@lem2271980 n). Qed.