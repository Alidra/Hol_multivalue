Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term31 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term47 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := and (Peano.le (dest_nadd x0 x2) (Nat.add (Nat.mul x1 x2) x3)).
Definition term43 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) x0.
Definition term8 (x0 : nat) := (fun y0 : nat => y0 = (Nat.mul y0 (NUMERAL (BIT1 0)))) x0.
Definition term78 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (Nat.mul y0 y2) y1).
Definition term76 (x0 : nadd) := fun y0 : nat => exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (dest_nadd x0 y2) (Nat.mul y0 y2).
Definition term73 (x0 : nadd) (x1 : nat) (x2 : nat) := exists y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> Peano.le (dest_nadd x0 y1) (Nat.mul (Nat.add x1 x2) y1).
Definition term41 (x0 : nadd) (x1 : nat) := exists y0 : nat, forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (Nat.mul x1 y1) y0).
Definition term6 := fun y0 : nat => y0 = (Nat.mul y0 (NUMERAL (BIT1 0))).
Definition term1 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term56 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y1) (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (Peano.le y1 y2))) x0.
Definition term23 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.le y1 y2)) x0.
Definition term53 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.mul x0 x1).
Definition term44 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (exists y0 : nat, (Peano.le (dest_nadd x0 x3) y0) /\ (Peano.le y0 (Nat.mul (Nat.add x1 x2) x3))) -> Peano.le (dest_nadd x0 x3) (Nat.mul (Nat.add x1 x2) x3).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0)) x2.
Definition term36 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term66 (x0 : nat) := (x0 = (NUMERAL 0)) \/ True.
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le x1 x2).
Definition term42 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, Peano.le (dest_nadd x0 y0) (Nat.add (Nat.mul x1 y0) x2).
Definition term12 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0).
Definition term30 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul x0 x2) x1) (Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2)).
Definition term34 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term54 (x0 : nat) := Peano.le (Nat.mul x0 (NUMERAL (BIT1 0))).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul x0 x2) x1) (Nat.mul (Nat.add x0 x1) x2).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x1 x0) (Nat.add x1 x2).
Definition term45 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le (dest_nadd x0 y0) (Nat.add (Nat.mul x1 y0) x2)) x3.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term5 := fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term58 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1))) x1.
Definition term25 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1)) x1.
Definition term77 (x0 : nadd) (x1 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dest_nadd x0 y1) (Nat.add (Nat.mul x1 y1) y0).
Definition term3 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term70 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd x0 x3) (Nat.mul (Nat.add x1 x2) x3).
Definition term72 (x0 : nadd) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le (NUMERAL (BIT1 0)) y0) -> Peano.le (dest_nadd x0 y0) (Nat.mul (Nat.add x1 x2) y0).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term71 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (NUMERAL (BIT1 0)) x3) -> Peano.le (dest_nadd x0 x3) (Nat.mul (Nat.add x1 x2) x3).
Definition term65 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term57 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (Peano.le y0 y1)).
Definition term35 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term24 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term22 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term16 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term10 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1).
Definition term67 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := exists y0 : nat, (Peano.le (dest_nadd x0 x3) y0) /\ (Peano.le y0 (Nat.mul (Nat.add x1 x2) x3)).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term59 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0)).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term2 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term26 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term79 := forall y0 : nadd, exists y1 : nat, exists y2 : nat, forall y3 : nat, (Peano.le y2 y3) -> Peano.le (dest_nadd y0 y3) (Nat.mul y1 y3).
Definition term7 := forall y0 : nat, y0 = (Nat.mul y0 (NUMERAL (BIT1 0))).
Definition term4 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add (Nat.mul x0 x1) x2).
Definition term37 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := True /\ (Peano.le (Nat.add (Nat.mul x0 x2) x1) (Nat.mul (Nat.add x0 x1) x2)).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 x1) (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (Peano.le x1 y0))) x2.
Definition term68 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => (Peano.le (dest_nadd x0 x3) y0) /\ (Peano.le y0 (Nat.mul (Nat.add x1 x2) x3)).
Definition term18 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term33 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term46 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (dest_nadd x0 x2) (Nat.add (Nat.mul x1 x2) x3).
Definition term55 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul x0 (NUMERAL (BIT1 0))) (Nat.mul x0 x1).
Definition term39 (x0 : nadd) := (fun y0 : nadd => exists y1 : nat, exists y2 : nat, forall y3 : nat, Peano.le (dest_nadd y0 y3) (Nat.add (Nat.mul y1 y3) y2)) x0.
Definition term32 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term75 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, (Peano.le y1 y2) -> Peano.le (dest_nadd x0 y2) (Nat.mul y0 y2).
Definition term40 (x0 : nadd) := exists y0 : nat, exists y1 : nat, forall y2 : nat, Peano.le (dest_nadd x0 y2) (Nat.add (Nat.mul y0 y2) y1).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term63 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.le (NUMERAL (BIT1 0)) x1).
Definition term49 (x0 : nadd) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (dest_nadd x0 x3) (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.le (Nat.add (Nat.mul x1 x3) x2) (Nat.mul (Nat.add x1 x2) x3)).
Definition term0 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term74 (x0 : nadd) (x1 : nat) (x2 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> Peano.le (dest_nadd x0 y1) (Nat.mul (Nat.add x1 x2) y1).
Definition term64 := NUMERAL (BIT1 0).
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
