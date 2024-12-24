Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1066937 : forall {A B : Type'} (sum' : (recspace (prod A B)) -> Prop) (INL' : A -> recspace (prod A B)) (INR' : B -> recspace (prod A B)) (h1 : sum' = (fun a : recspace (prod A B) => forall sum'' : (recspace (prod A B)) -> Prop, (forall a' : recspace (prod A B), ((exists a'' : A, a' = (INL' a'')) \/ (exists a'' : B, a' = (INR' a''))) -> sum'' a') -> sum'' a)), (forall sum'' : (recspace (prod A B)) -> Prop, ((forall a : A, sum'' (INL' a)) /\ (forall a : B, sum'' (INR' a))) -> forall a : recspace (prod A B), (sum' a) -> sum'' a) /\ (forall a : recspace (prod A B), (sum' a) = ((exists a' : A, a = (INL' a')) \/ (exists a' : B, a = (INR' a')))).
