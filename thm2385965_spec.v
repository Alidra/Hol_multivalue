Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2385965 : (fun q : (prod nat (prod nat nat)) -> int -> int -> int => forall _29199 : prod nat (prod nat nat), exists r : int -> int -> int, forall m : int, forall n : int, @COND Prop (n = (int_of_num (NUMERAL 0))) (((q _29199 m n) = (int_of_num (NUMERAL 0))) /\ ((r m n) = m)) ((int_le (int_of_num (NUMERAL 0)) (r m n)) /\ ((int_lt (r m n) (int_abs n)) /\ (m = (int_add (int_mul (q _29199 m n) n) (r m n)))))) (@ε ((prod nat (prod nat nat)) -> int -> int -> int) (fun q : (prod nat (prod nat nat)) -> int -> int -> int => forall _29199 : prod nat (prod nat nat), exists r : int -> int -> int, forall m : int, forall n : int, @COND Prop (n = (int_of_num (NUMERAL 0))) (((q _29199 m n) = (int_of_num (NUMERAL 0))) /\ ((r m n) = m)) ((int_le (int_of_num (NUMERAL 0)) (r m n)) /\ ((int_lt (r m n) (int_abs n)) /\ (m = (int_add (int_mul (q _29199 m n) n) (r m n))))))).
