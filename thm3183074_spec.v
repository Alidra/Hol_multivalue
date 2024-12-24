Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3183074 : forall {A : Type'} (p : A -> Prop), (fun p' : A -> Prop => (@GSPEC A p') = p') p.
