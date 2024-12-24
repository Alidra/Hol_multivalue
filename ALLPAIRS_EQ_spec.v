Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1187163 : forall {A B : Type'} (R : A -> B -> Prop) (R' : A -> B -> Prop), forall l : list A, forall m : list B, forall P : A -> Prop, forall Q : B -> Prop, ((@List.Forall A P l) /\ ((@List.Forall B Q m) /\ (forall p : A, forall q : B, ((P p) /\ (Q q)) -> (R p q) = (R' p q)))) -> (@ALLPAIRS B A R l m) = (@ALLPAIRS B A R' l m).
