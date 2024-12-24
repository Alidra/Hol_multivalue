Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1200074 : forall {_27941 : Type'}, forall l : list _27941, (@List.map _27941 _27941 (fun x : _27941 => x) l) = l.
