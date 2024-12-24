Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2338274_term_abbrevs.
Require Import thm2338267_spec.
Lemma lem2338274 (P : int -> Prop) : term0 P.
Proof. exact (@lem2338267 P). Qed.
