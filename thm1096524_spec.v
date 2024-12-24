Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1096524 : forall {A : Type'} (l : list A) (x : A), ((fun x' : A => (@List.rev A (@cons A x' l)) = (@List.app A (@List.rev A l) (@cons A x' (@nil A)))) x) = ((@List.rev A (@cons A x l)) = (@List.app A (@List.rev A l) (@cons A x (@nil A)))).
