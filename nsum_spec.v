Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6920372 : forall {_126417 : Type'}, (@nsum _126417) = (@iterate nat _126417 Nat.add).
