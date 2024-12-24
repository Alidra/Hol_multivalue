Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1163656 : forall {_27338 : Type'}, forall P : _27338 -> Prop, forall l : list _27338, (forall i : nat, (Peano.lt i (@List.length _27338 l)) -> P (@EL _27338 i l)) = (@List.Forall _27338 P l).
