Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3392828 : forall {_88095 _88100 : Type'}, forall s : _88095 -> Prop, forall c : _88100, (@IMAGE _88095 _88100 (fun x : _88095 => c) s) = (@COND (_88100 -> Prop) (s = (@EMPTY _88095)) (@EMPTY _88100) (@INSERT _88100 c (@EMPTY _88100))).
