Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom axiom_21 : forall (a : hreal), (mk_hreal (dest_hreal a)) = a.
Axiom axiom_22 : forall (r : nadd -> Prop), ((fun s : nadd -> Prop => exists x : nadd, s = (nadd_eq x)) r) = ((dest_hreal (mk_hreal r)) = r).
Axiom axiom_23 : forall (a : real), (mk_real (dest_real a)) = a.
Axiom axiom_24 : forall (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop => exists x : prod hreal hreal, s = (treal_eq x)) r) = ((dest_real (mk_real r)) = r).
Axiom axiom_25 : forall (a : int), (int_of_real (real_of_int a)) = a.
Axiom axiom_26 : forall (r : real), ((fun x : real => integer x) r) = ((real_of_int (int_of_real r)) = r).
Axiom axiom_27 : forall {A : Type'} (a : finite_image A), (@finite_index A (@dest_finite_image A a)) = a.
Axiom axiom_28 : forall {A : Type'} (r : nat), ((fun x : nat => @IN nat x (dotdot (NUMERAL (BIT1 0)) (@dimindex A (@UNIV A)))) r) = ((@dest_finite_image A (@finite_index A r)) = r).
Axiom axiom_29 : forall {A B : Type'} (a : cart A B), (@mk_cart A B (@dest_cart A B a)) = a.
Axiom axiom_30 : forall {A B : Type'} (r : (finite_image B) -> A), ((fun f : (finite_image B) -> A => True) r) = ((@dest_cart A B (@mk_cart A B r)) = r).
Axiom axiom_31 : forall {A B : Type'} (a : finite_sum A B), (@mk_finite_sum A B (@dest_finite_sum A B a)) = a.
Axiom axiom_32 : forall {A B : Type'} (r : nat), ((fun x : nat => @IN nat x (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))))) r) = ((@dest_finite_sum A B (@mk_finite_sum A B r)) = r).
Axiom axiom_33 : forall {A B : Type'} (a : finite_diff A B), (@mk_finite_diff A B (@dest_finite_diff A B a)) = a.
Axiom axiom_34 : forall {A B : Type'} (r : nat), ((fun x : nat => @IN nat x (dotdot (NUMERAL (BIT1 0)) (@COND nat (Peano.lt (@dimindex B (@UNIV B)) (@dimindex A (@UNIV A))) (Nat.sub (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))) (NUMERAL (BIT1 0))))) r) = ((@dest_finite_diff A B (@mk_finite_diff A B r)) = r).
Axiom axiom_35 : forall {A B : Type'} (a : finite_prod A B), (@mk_finite_prod A B (@dest_finite_prod A B a)) = a.
Axiom axiom_36 : forall {A B : Type'} (r : nat), ((fun x : nat => @IN nat x (dotdot (NUMERAL (BIT1 0)) (Nat.mul (@dimindex A (@UNIV A)) (@dimindex B (@UNIV B))))) r) = ((@dest_finite_prod A B (@mk_finite_prod A B r)) = r).
Axiom axiom_37 : forall {A : Type'} (a : tybit0 A), (@_mk_tybit0 A (@_dest_tybit0 A a)) = a.
Axiom axiom_38 : forall {A : Type'} (r : recspace (finite_sum A A)), ((fun a : recspace (finite_sum A A) => forall tybit0' : (recspace (finite_sum A A)) -> Prop, (forall a' : recspace (finite_sum A A), (exists a'' : finite_sum A A, a' = ((fun a''' : finite_sum A A => @CONSTR (finite_sum A A) (NUMERAL 0) a''' (fun n : nat => @BOTTOM (finite_sum A A))) a'')) -> tybit0' a') -> tybit0' a) r) = ((@_dest_tybit0 A (@_mk_tybit0 A r)) = r).
Axiom axiom_39 : forall {A : Type'} (a : tybit1 A), (@_mk_tybit1 A (@_dest_tybit1 A a)) = a.
Axiom axiom_40 : forall {A : Type'} (r : recspace (finite_sum (finite_sum A A) unit)), ((fun a : recspace (finite_sum (finite_sum A A) unit) => forall tybit1' : (recspace (finite_sum (finite_sum A A) unit)) -> Prop, (forall a' : recspace (finite_sum (finite_sum A A) unit), (exists a'' : finite_sum (finite_sum A A) unit, a' = ((fun a''' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) (NUMERAL 0) a''' (fun n : nat => @BOTTOM (finite_sum (finite_sum A A) unit))) a'')) -> tybit1' a') -> tybit1' a) r) = ((@_dest_tybit1 A (@_mk_tybit1 A r)) = r).
