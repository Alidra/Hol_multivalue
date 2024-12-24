Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3183065 : forall {_83031 : Type'} (P : Prop) (v : _83031) (t : _83031), (fun t' : _83031 => (@SETSPEC _83031 v P t') = (P /\ (v = t'))) t.
