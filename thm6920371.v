Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem6920371 {_126417 : Type'} : (@iterate nat _126417 Nat.add) = (@iterate nat _126417 Nat.add).
Proof. exact (eq_refl (@iterate nat _126417 Nat.add)). Qed.
