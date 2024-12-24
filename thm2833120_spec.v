Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2833120 : forall (a : int) (d : int) (b : int), (fun b' : int => (int_divides d (int_gcd (@pair int int a b'))) = ((int_divides d a) /\ (int_divides d b'))) b.
