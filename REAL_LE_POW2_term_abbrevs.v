Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term70 := Peano.le (BIT1 0) (BIT0 (BIT1 0)).
Definition term73 := and (real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term8 (x0 : nat) := (fun y0 : nat => (Peano.lt 0 (BIT1 y0)) = True) x0.
Definition term74 (x0 : nat) := (real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))) /\ (Peano.le (NUMERAL 0) x0).
Definition term64 (x0 : nat) := ((real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))) /\ (Peano.le (NUMERAL 0) x0)) -> (real_le (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL 0)) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)) = True.
Definition term60 (x0 : nat) := (exists y0 : real, (real_le (real_of_num (NUMERAL (BIT1 0))) y0) /\ (real_le y0 (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0))) -> real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term62 (x0 : nat) := real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term35 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y2) /\ (Peano.le y0 y1)) -> real_le (real_pow y2 y0) (real_pow y2 y1)) x0.
Definition term83 := real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term11 := ((Peano.le 0 0) = True) /\ ((forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))))))).
Definition term10 := (forall y0 : nat, forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1)) /\ (((Peano.le 0 0) = True) /\ ((forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))))))).
Definition term12 := (forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))))).
Definition term5 := (forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))))).
Definition term87 := forall y0 : nat, real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) y0).
Definition term18 := (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)).
Definition term57 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term52 (x0 : real) (x1 : real) := exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1).
Definition term63 (x0 : nat) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL (BIT1 0))) x1) /\ (Peano.le x0 x2)) -> (real_le (real_pow x1 x0) (real_pow x1 x2)) = True.
Definition term75 (x0 : nat) := real_le (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL 0)) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term53 (x0 : real) (x1 : real) := fun y0 : real => (real_le x0 y0) /\ (real_le y0 x1).
Definition term30 (x0 : nat) := forall y0 : nat, (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0).
Definition term26 (x0 : nat) := forall y0 : nat, (Peano.le (NUMERAL x0) (NUMERAL y0)) = (Peano.le x0 y0).
Definition term21 (x0 : nat) := forall y0 : nat, (Peano.le (BIT1 x0) (BIT0 y0)) = (Peano.lt x0 y0).
Definition term66 := real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term33 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term80 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term56 := forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term45 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term43 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term49 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term79 := real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL 0)).
Definition term38 (x0 : nat) (x1 : nat) := forall y0 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y0) /\ (Peano.le x0 x1)) -> real_le (real_pow y0 x0) (real_pow y0 x1).
Definition term16 := (forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))).
Definition term42 (x0 : nat) (x1 : real) (x2 : nat) := real_le (real_pow x1 x0) (real_pow x1 x2).
Definition term85 (x0 : nat) := fun y0 : real => (real_le (real_of_num (NUMERAL (BIT1 0))) y0) /\ (real_le y0 (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)).
Definition term1 := (forall y0 : nat, forall y1 : nat, (Peano.lt (NUMERAL y0) (NUMERAL y1)) = (Peano.lt y0 y1)) /\ (((Peano.lt 0 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))))))))).
Definition term17 := (forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))).
Definition term51 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> real_le x0 x1.
Definition term55 (x0 : real) := forall y0 : real, (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0.
Definition term31 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0)) x1.
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (NUMERAL x0) (NUMERAL y0)) = (Peano.le x0 y0)) x1.
Definition term54 (x0 : real) (x1 : real) := (exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1)) -> real_le x0 x1.
Definition term67 := Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term36 (x0 : nat) := forall y0 : nat, forall y1 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y1) /\ (Peano.le x0 y0)) -> real_le (real_pow y1 x0) (real_pow y1 y0).
Definition term24 := forall y0 : nat, forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1).
Definition term19 := forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1).
Definition term84 (x0 : nat) := exists y0 : real, (real_le (real_of_num (NUMERAL (BIT1 0))) y0) /\ (real_le y0 (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)).
Definition term9 (x0 : nat) := Peano.lt 0 (BIT1 x0).
Definition term2 := ((Peano.lt 0 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))))))))).
Definition term58 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1) x0.
Definition term34 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term65 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (BIT1 x0) (BIT0 y0)) = (Peano.lt x0 y0)) x1.
Definition term46 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1) x1.
Definition term69 := NUMERAL (BIT0 (BIT1 0)).
Definition term40 (x0 : nat) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL (BIT1 0))) x1) /\ (Peano.le x0 x2)) -> real_le (real_pow x1 x0) (real_pow x1 x2).
Definition term86 (x0 : nat) := real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term23 (x0 : nat) (x1 : nat) := Peano.le (BIT1 x0) (BIT0 x1).
Definition term48 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0) x2.
Definition term77 (x0 : nat) := (real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL 0))) /\ (real_le (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL 0)) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)).
Definition term29 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1)) x0.
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) x0.
Definition term59 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0) x1.
Definition term0 (x0 : real) := (fun y0 : real => real_le y0 y0) x0.
Definition term41 (x0 : real) (x1 : nat) (x2 : nat) := (real_le (real_of_num (NUMERAL (BIT1 0))) x0) /\ (Peano.le x1 x2).
Definition term61 := real_of_num (NUMERAL (BIT1 0)).
Definition term47 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term71 := BIT0 (BIT1 0).
Definition term28 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL x0) (NUMERAL x1).
Definition term37 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : real, ((real_le (real_of_num (NUMERAL (BIT1 0))) y1) /\ (Peano.le x0 y0)) -> real_le (real_pow y1 x0) (real_pow y1 y0)) x1.
Definition term50 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term39 (x0 : nat) (x1 : nat) (x2 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL (BIT1 0))) y0) /\ (Peano.le x0 x1)) -> real_le (real_pow y0 x0) (real_pow y0 x1)) x2.
Definition term76 := and (real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL 0))).
Definition term32 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_of_num x1).
Definition term14 := (forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))).
Definition term13 := (forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))))).
Definition term4 := (forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))))))).
Definition term3 := (forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))))))).
Definition term82 := real_le (real_of_num (NUMERAL (BIT1 0))).
Definition term72 := Peano.lt 0 (BIT1 0).
Definition term44 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) x0.
Definition term81 := real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL 0).
Definition term78 := (real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (NUMERAL 0))) /\ True.
Definition term15 := (forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))).
Definition term6 := (forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))))).
Definition term68 := NUMERAL (BIT1 0).
Definition term7 := forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True.
