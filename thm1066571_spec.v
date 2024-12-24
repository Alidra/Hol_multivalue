Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1066571 : forall {A B : Type'} (INL' : A -> recspace (prod A B)) (h1 : INL' = (fun a : A => @CONSTR (prod A B) (NUMERAL 0) (@pair A B a (@ε B (fun v : B => True))) (fun n : nat => @BOTTOM (prod A B)))), INL' = (fun a : A => @CONSTR (prod A B) (NUMERAL 0) (@pair A B a (@ε B (fun v : B => True))) (fun n : nat => @BOTTOM (prod A B))).
