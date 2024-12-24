Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm124577_term_abbrevs.
Lemma lem124577 : Coq.Arith.PeanoNat.Nat.Odd = term0.
Proof. exact (@ODD_def). Qed.
