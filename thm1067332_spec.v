Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1067332 : forall {A B : Type'} (INL' : A -> recspace (prod A B)) (h1 : INL' = (fun a : A => @CONSTR (prod A B) (NUMERAL 0) (@pair A B a (@ε B (fun v : B => True))) (fun n : nat => @BOTTOM (prod A B)))), (@inl A B) = (fun a : A => @_mk_sum A B (INL' a)).
