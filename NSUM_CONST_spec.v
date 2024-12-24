Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6940531 : forall {_127196 : Type'}, forall c : nat, forall s : _127196 -> Prop, (@FINITE _127196 s) -> (@nsum _127196 s (fun n : _127196 => c)) = (Nat.mul (@CARD _127196 s) c).
