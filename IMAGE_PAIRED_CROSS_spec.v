Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4360022 : forall {A B C D : Type'}, forall f : A -> B, forall g : C -> D, forall s : A -> Prop, forall t : C -> Prop, (@IMAGE (prod A C) (prod B D) (@GABS ((prod A C) -> prod B D) (fun f' : (prod A C) -> prod B D => forall x : A, forall y : C, @GEQ (prod B D) (f' (@pair A C x y)) (@pair B D (f x) (g y)))) (@CROSS C A s t)) = (@CROSS D B (@IMAGE A B f s) (@IMAGE C D g t)).
