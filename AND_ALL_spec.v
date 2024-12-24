Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1133441 : forall {_26720 : Type'} (P : _26720 -> Prop) (Q : _26720 -> Prop), forall l : list _26720, ((@List.Forall _26720 P l) /\ (@List.Forall _26720 Q l)) = (@List.Forall _26720 (fun x : _26720 => (P x) /\ (Q x)) l).
