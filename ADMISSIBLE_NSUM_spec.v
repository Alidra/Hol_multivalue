Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8220444 : forall {A B C P : Type'}, forall lt2 : B -> A -> Prop, forall p : (B -> C) -> P -> Prop, forall s : P -> A, forall h : (B -> C) -> P -> nat -> nat, forall a : P -> nat, forall b : P -> nat, (@admissible A C B nat (prod nat P) lt2 (fun f : B -> C => @GABS ((prod nat P) -> Prop) (fun f' : (prod nat P) -> Prop => forall k : nat, forall x : P, @GEQ Prop (f' (@pair nat P k x)) ((Peano.le (a x) k) /\ ((Peano.le k (b x)) /\ (p f x))))) (@GABS ((prod nat P) -> A) (fun f : (prod nat P) -> A => forall k : nat, forall x : P, @GEQ A (f (@pair nat P k x)) (s x))) (fun f : B -> C => @GABS ((prod nat P) -> nat) (fun f' : (prod nat P) -> nat => forall k : nat, forall x : P, @GEQ nat (f' (@pair nat P k x)) (h f x k)))) -> @admissible A C B nat P lt2 p s (fun f : B -> C => fun x : P => @nsum nat (dotdot (a x) (b x)) (h f x)).
