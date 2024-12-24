Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1069419 : forall {A : Type'} (r : recspace A) (option' : (recspace A) -> Prop) (SOME' : A -> recspace A) (NONE' : recspace A) (h1 : SOME' = (fun a : A => @CONSTR A (S (NUMERAL 0)) a (fun n : nat => @BOTTOM A))) (h2 : option' = (fun a : recspace A => forall option'' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = NONE') \/ (exists a'' : A, a' = (SOME' a''))) -> option'' a') -> option'' a)) (h3 : NONE' = (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))), (option' r) = ((fun a : recspace A => forall option'' : (recspace A) -> Prop, (forall a' : recspace A, ((a' = (@CONSTR A (NUMERAL 0) (@ε A (fun v : A => True)) (fun n : nat => @BOTTOM A))) \/ (exists a'' : A, a' = ((fun a''' : A => @CONSTR A (S (NUMERAL 0)) a''' (fun n : nat => @BOTTOM A)) a''))) -> option'' a') -> option'' a) r).
