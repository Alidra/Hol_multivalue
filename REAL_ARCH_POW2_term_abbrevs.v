Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (x0 : nat) := (fun y0 : nat => (Peano.lt 0 (BIT1 y0)) = True) x0.
Definition term39 := Peano.lt (BIT1 0) (BIT0 (BIT1 0)).
Definition term25 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term29 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL (BIT1 0))) x1) -> exists y0 : nat, real_lt x0 (real_pow x1 y0).
Definition term35 := real_lt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term4 := (forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))))).
Definition term47 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term33 (x0 : real) := (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))) -> (exists y0 : nat, real_lt x0 (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0)) = True.
Definition term44 := fun y0 : real => True.
Definition term8 := (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)).
Definition term23 (x0 : nat) := forall y0 : nat, (real_lt (real_of_num x0) (real_of_num y0)) = (Peano.lt x0 y0).
Definition term19 (x0 : nat) := forall y0 : nat, (Peano.lt (NUMERAL x0) (NUMERAL y0)) = (Peano.lt x0 y0).
Definition term11 (x0 : nat) := forall y0 : nat, (Peano.lt (BIT1 x0) (BIT0 y0)) = (Peano.lt x0 y0).
Definition term46 := forall y0 : real, True.
Definition term48 (x0 : Prop) := forall y0 : real, x0.
Definition term32 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL (BIT1 0))) x1) -> (exists y0 : nat, real_lt x0 (real_pow x1 y0)) = True.
Definition term6 := (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))).
Definition term27 (x0 : real) := forall y0 : real, (real_lt (real_of_num (NUMERAL (BIT1 0))) x0) -> exists y1 : nat, real_lt y0 (real_pow x0 y1).
Definition term0 := (forall y0 : nat, forall y1 : nat, (Peano.lt (NUMERAL y0) (NUMERAL y1)) = (Peano.lt y0 y1)) /\ (((Peano.lt 0 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))))))))).
Definition term7 := (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))).
Definition term42 (x0 : real) := exists y0 : nat, real_lt x0 (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0).
Definition term17 := forall y0 : nat, forall y1 : nat, (Peano.lt (NUMERAL y0) (NUMERAL y1)) = (Peano.lt y0 y1).
Definition term9 := forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1).
Definition term45 := forall y0 : real, exists y1 : nat, real_lt y0 (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y1).
Definition term28 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL (BIT1 0))) x0) -> exists y1 : nat, real_lt y0 (real_pow x0 y1)) x1.
Definition term16 (x0 : nat) := Peano.lt 0 (BIT1 x0).
Definition term1 := ((Peano.lt 0 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))))))))).
Definition term26 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt (real_of_num (NUMERAL (BIT1 0))) y0) -> exists y2 : nat, real_lt y1 (real_pow y0 y2)) x0.
Definition term34 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term24 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_lt (real_of_num x0) (real_of_num y0)) = (Peano.lt x0 y0)) x1.
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL x0) (NUMERAL y0)) = (Peano.lt x0 y0)) x1.
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (BIT1 x0) (BIT0 y0)) = (Peano.lt x0 y0)) x1.
Definition term36 := Peano.lt (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term38 := NUMERAL (BIT0 (BIT1 0)).
Definition term22 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) x0.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL y0) (NUMERAL y1)) = (Peano.lt y0 y1)) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) x0.
Definition term13 (x0 : nat) (x1 : nat) := Peano.lt (BIT1 x0) (BIT0 x1).
Definition term40 := BIT0 (BIT1 0).
Definition term21 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL x0) (NUMERAL x1).
Definition term3 := (forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))))))).
Definition term2 := (forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))))))).
Definition term43 := fun y0 : real => exists y1 : nat, real_lt y0 (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y1).
Definition term41 := Peano.lt 0 (BIT1 0).
Definition term30 (x0 : real) := real_lt (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term5 := (forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))))).
Definition term37 := NUMERAL (BIT1 0).
Definition term14 := forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True.
Definition term31 (x0 : real) (x1 : real) := exists y0 : nat, real_lt x0 (real_pow x1 y0).
