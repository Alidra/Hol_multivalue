Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2528721 : forall (m : int) (n : int) (p : int), (fun p' : int => ((rem m p') = (rem n p')) = (@eq2 int m n (int_mod p'))) p.
