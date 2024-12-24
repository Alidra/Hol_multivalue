Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4786583 : forall {_110256 : Type'}, forall s : _110256 -> Prop, (@list_of_set _110256 s) = (@ε (list _110256) (fun l : list _110256 => ((@set_of_list _110256 l) = s) /\ ((@List.length _110256 l) = (@CARD _110256 s)))).
