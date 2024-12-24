Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3576206 : forall {_91560 _91563 : Type'} (f : _91563 -> _91560), (forall y : _91560, exists x : _91563, (f x) = y) = (exists g : _91560 -> _91563, forall y : _91560, (f (g y)) = y).
