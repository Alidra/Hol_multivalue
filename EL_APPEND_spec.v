Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1206051 : forall {_28192 : Type'}, forall k : nat, forall l : list _28192, forall m : list _28192, (@EL _28192 k (@List.app _28192 l m)) = (@COND _28192 (Peano.lt k (@List.length _28192 l)) (@EL _28192 k l) (@EL _28192 (Nat.sub k (@List.length _28192 l)) m)).
