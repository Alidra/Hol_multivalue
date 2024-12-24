Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1100835 : forall {_25307 : Type'} (P : _25307 -> Prop), ((fun P' : _25307 -> Prop => (@List.Forall _25307 P' (@nil _25307)) = True) P) = ((@List.Forall _25307 P (@nil _25307)) = True).
