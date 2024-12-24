Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm124194_term_abbrevs.
Lemma lem124194 : Coq.Arith.PeanoNat.Nat.Even = term0.
Proof. exact (@EVEN_def). Qed.
