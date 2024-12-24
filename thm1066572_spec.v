Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1066572 : forall {A B : Type'} (INR' : B -> recspace (prod A B)) (h1 : INR' = (fun a : B => @CONSTR (prod A B) (S (NUMERAL 0)) (@pair A B (@ε A (fun v : A => True)) a) (fun n : nat => @BOTTOM (prod A B)))), INR' = (fun a : B => @CONSTR (prod A B) (S (NUMERAL 0)) (@pair A B (@ε A (fun v : A => True)) a) (fun n : nat => @BOTTOM (prod A B))).
