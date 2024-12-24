Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1123621 : forall {_26390 : Type'}, forall P : _26390 -> Prop, forall l : list _26390, (~ (@List.Forall _26390 P l)) = (@EX _26390 (fun x : _26390 => ~ (P x)) l).
