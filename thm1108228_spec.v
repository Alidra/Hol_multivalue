Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1108228 : forall {_25645 _25647 _25655 : Type'} (h1' : _25647) (f : _25647 -> _25655 -> _25645 -> _25645) (t1 : list _25647) (l2 : list _25655) (b : _25645), (fun b' : _25645 => (@ITLIST2 _25645 _25647 _25655 f (@cons _25647 h1' t1) l2 b') = (f h1' (@hd _25655 l2) (@ITLIST2 _25645 _25647 _25655 f t1 (@tl _25655 l2) b'))) b.
