Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1133060 : forall {_26690 : Type'}, forall P : _26690 -> Prop, forall Q : _26690 -> Prop, forall l : list _26690, ((@List.Forall _26690 (fun x : _26690 => (P x) -> Q x) l) /\ (@List.Forall _26690 P l)) -> @List.Forall _26690 Q l.
