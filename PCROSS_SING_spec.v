Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8006149 : forall {_142030 A N : Type'}, forall x : cart A _142030, forall y : cart A N, (@PCROSS A _142030 N (@INSERT (cart A _142030) x (@EMPTY (cart A _142030))) (@INSERT (cart A N) y (@EMPTY (cart A N)))) = (@INSERT (cart A (finite_sum _142030 N)) (@pastecart A _142030 N x y) (@EMPTY (cart A (finite_sum _142030 N)))).
