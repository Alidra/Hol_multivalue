Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1067344 : forall {A B : Type'} (INR' : B -> recspace (prod A B)) (h1 : INR' = (fun a : B => @CONSTR (prod A B) (S (NUMERAL 0)) (@pair A B (@ε A (fun v : A => True)) a) (fun n : nat => @BOTTOM (prod A B)))), (fun a : B => @_mk_sum A B (INR' a)) = (fun a : B => @_mk_sum A B ((fun a' : B => @CONSTR (prod A B) (S (NUMERAL 0)) (@pair A B (@ε A (fun v : A => True)) a') (fun n : nat => @BOTTOM (prod A B))) a)).
