Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2338252_term_abbrevs.
Require Import num_WOP_spec.
Lemma lem2338252 (P : nat -> Prop) : term0 P.
Proof. exact (@lem116994 P). Qed.
