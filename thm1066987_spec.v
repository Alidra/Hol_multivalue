Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1066987 : forall {A B : Type'} (a : A), (fun a' : recspace (prod A B) => forall sum' : (recspace (prod A B)) -> Prop, (forall a'' : recspace (prod A B), ((exists a''' : A, a'' = ((fun a'''' : A => @CONSTR (prod A B) (NUMERAL 0) (@pair A B a'''' (@ε B (fun v : B => True))) (fun n : nat => @BOTTOM (prod A B))) a''')) \/ (exists a''' : B, a'' = ((fun a'''' : B => @CONSTR (prod A B) (S (NUMERAL 0)) (@pair A B (@ε A (fun v : A => True)) a'''') (fun n : nat => @BOTTOM (prod A B))) a'''))) -> sum' a'') -> sum' a') ((fun a' : A => @CONSTR (prod A B) (NUMERAL 0) (@pair A B a' (@ε B (fun v : B => True))) (fun n : nat => @BOTTOM (prod A B))) a).
