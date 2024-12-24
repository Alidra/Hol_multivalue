Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem6898583 {_126105 : Type'} : (@iterate nat _126105 Nat.mul) = (@iterate nat _126105 Nat.mul).
Proof. exact (eq_refl (@iterate nat _126105 Nat.mul)). Qed.
