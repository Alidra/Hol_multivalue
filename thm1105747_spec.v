Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1105747 : forall {_25569 : Type'} (n : nat) (l : list _25569), (fun l' : list _25569 => (@EL _25569 (S n) l') = (@EL _25569 n (@tl _25569 l'))) l.
