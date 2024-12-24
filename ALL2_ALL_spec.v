Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1187294 : forall {_27624 : Type'}, forall P : _27624 -> _27624 -> Prop, forall l : list _27624, (@ALL2 _27624 _27624 P l l) = (@List.Forall _27624 (fun x : _27624 => P x x) l).
