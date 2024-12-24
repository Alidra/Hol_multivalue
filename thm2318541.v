Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2318541_term_abbrevs.
Require Import int_neg_th_spec.
Lemma lem2318541 (x : int) : term0 x.
Proof. exact (@lem2273074 x). Qed.
