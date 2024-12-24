Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem523717 : forall n : nat, (Coq.Arith.PeanoNat.Nat.Even (NUMERAL n)) = (Coq.Arith.PeanoNat.Nat.Even n).
