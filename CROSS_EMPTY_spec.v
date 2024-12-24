Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4327078 : forall {_103859 _103872 A B : Type'}, (forall s : A -> Prop, (@CROSS _103859 A s (@EMPTY _103859)) = (@EMPTY (prod A _103859))) /\ (forall t : B -> Prop, (@CROSS B _103872 (@EMPTY _103872) t) = (@EMPTY (prod _103872 B))).
