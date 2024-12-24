Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem15219 : forall {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) (g : Prop) (h1 : g = False), (g = g') -> (g' -> t = t') -> ((~ g') -> e = e') -> (@COND _2963 g t e) = (@COND _2963 g' t' e').
