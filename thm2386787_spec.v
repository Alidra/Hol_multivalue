Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2386787 : (fun r : (prod nat (prod nat nat)) -> int -> int -> int => forall _29200 : prod nat (prod nat nat), forall m : int, forall n : int, @COND Prop (n = (int_of_num (NUMERAL 0))) (((div m n) = (int_of_num (NUMERAL 0))) /\ ((r _29200 m n) = m)) ((int_le (int_of_num (NUMERAL 0)) (r _29200 m n)) /\ ((int_lt (r _29200 m n) (int_abs n)) /\ (m = (int_add (int_mul (div m n) n) (r _29200 m n)))))) (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun r : (prod nat (prod nat nat)) -> int -> int -> int => forall _29200 : prod nat (prod nat nat), forall m : int, forall n : int, @COND Prop (n = (int_of_num (NUMERAL 0))) (((div m n) = (int_of_num (NUMERAL 0))) /\ ((r _29200 m n) = m)) ((int_le (int_of_num (NUMERAL 0)) (r _29200 m n)) /\ ((int_lt (r _29200 m n) (int_abs n)) /\ (m = (int_add (int_mul (div m n) n) (r _29200 m n))))))).
