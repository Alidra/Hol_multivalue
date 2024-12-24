Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1123467 : forall {_26368 : Type'}, forall P : _26368 -> Prop, forall l : list _26368, (~ (@EX _26368 P l)) = (@List.Forall _26368 (fun x : _26368 => ~ (P x)) l).
