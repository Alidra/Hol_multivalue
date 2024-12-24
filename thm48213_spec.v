Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem48213 : forall {A B : Type'} (x : A) (y : B), (fun y' : B => (@snd A B (@pair A B x y')) = y') y.
