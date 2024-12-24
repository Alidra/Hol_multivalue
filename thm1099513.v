Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1099513_term_abbrevs.
Require Import thm1099511_spec.
Require Import thm1099512_spec.
Lemma lem1099513 {_25272 : Type'} (x : _25272) : (term0 _25272 x) = (@nil _25272).
Proof. exact (EQ_MP (@lem1099512 _25272 x) (@lem1099511 _25272 x)). Qed.
