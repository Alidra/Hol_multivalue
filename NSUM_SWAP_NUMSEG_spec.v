Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7047627 : forall a : nat, forall b : nat, forall c : nat, forall d : nat, forall f : nat -> nat -> nat, (@nsum nat (dotdot a b) (fun i : nat => @nsum nat (dotdot c d) (f i))) = (@nsum nat (dotdot c d) (fun j : nat => @nsum nat (dotdot a b) (fun i : nat => f i j))).
