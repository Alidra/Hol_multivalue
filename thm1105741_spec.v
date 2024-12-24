Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1105741 : forall {_25569 : Type'} (l : list _25569), (fun l' : list _25569 => (@EL _25569 (NUMERAL 0) l') = (@hd _25569 l')) l.
