Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1104055 : forall {_25409 _25416 : Type'} (h1' : _25409) (P : _25409 -> _25416 -> Prop) (t1 : list _25409) (l2 : list _25416), (fun l2' : list _25416 => (@ALL2 _25409 _25416 P (@cons _25409 h1' t1) l2') = (@COND Prop (l2' = (@nil _25416)) False ((P h1' (@hd _25416 l2')) /\ (@ALL2 _25409 _25416 P t1 (@tl _25416 l2'))))) l2.
