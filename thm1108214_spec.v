Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1108214 : forall {_25645 _25647 _25655 : Type'} (f : _25647 -> _25655 -> _25645 -> _25645) (l2 : list _25655) (b : _25645), ((fun b' : _25645 => (@ITLIST2 _25645 _25647 _25655 f (@nil _25647) l2 b') = b') b) = ((@ITLIST2 _25645 _25647 _25655 f (@nil _25647) l2 b) = b).
