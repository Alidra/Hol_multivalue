Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1069415 : forall {A : Type'} (r : recspace A), ((fun a : recspace A => forall option' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))) \/ (exists a'' : A, a' = ((fun a''' : A => @CONSTR A (S (NUMERAL 0)) a''' (fun n : nat => @BOTTOM A)) a''))) -> option' a') -> option' a) r) = ((@_dest_option A (@_mk_option A r)) = r).