Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem44424 : forall {A B : Type'}, (fun x : A -> B -> Prop => exists a : A, exists b : B, x = (@mk_pair A B a b)) (@ε (A -> B -> Prop) (fun x : A -> B -> Prop => exists a : A, exists b : B, x = (@mk_pair A B a b))).
