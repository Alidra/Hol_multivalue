Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term24 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_eq x1 x0) /\ (nadd_eq x0 x2)) -> nadd_eq x1 x2.
Definition term33 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (exists y2 : nadd, (nadd_eq y0 y2) /\ (nadd_eq y2 y1)) -> nadd_eq y0 y1) x0.
Definition term14 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) x0.
Definition term50 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_mul x0 x2) (nadd_mul x1 x2).
Definition term7 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term5 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) -> nadd_eq (nadd_mul x1 x0) (nadd_mul x1 y0)) x2.
Definition term59 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> nadd_eq (nadd_mul y0 y2) (nadd_mul y1 y3).
Definition term58 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> nadd_eq (nadd_mul x0 y1) (nadd_mul y0 y2).
Definition term57 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> nadd_eq (nadd_mul x0 y0) (nadd_mul x1 y1).
Definition term31 := forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, (nadd_eq y0 y2) /\ (nadd_eq y2 y1)) -> nadd_eq y0 y1.
Definition term20 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y0 y1)) -> nadd_eq x0 y1.
Definition term18 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2.
Definition term10 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_eq y0 y2) -> nadd_eq (nadd_mul y1 y0) (nadd_mul y1 y2).
Definition term9 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_eq x0 y1) -> nadd_eq (nadd_mul y0 x0) (nadd_mul y0 y1).
Definition term2 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) -> nadd_eq (nadd_mul x0 y0) (nadd_mul x0 y1).
Definition term0 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_eq y1 y2) -> nadd_eq (nadd_mul y0 y1) (nadd_mul y0 y2).
Definition term35 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x0 x1) /\ (nadd_eq x2 x3).
Definition term34 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (exists y1 : nadd, (nadd_eq x0 y1) /\ (nadd_eq y1 y0)) -> nadd_eq x0 y0) x1.
Definition term32 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) -> forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, (nadd_eq y0 y2) /\ (nadd_eq y2 y1)) -> nadd_eq y0 y1.
Definition term11 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_eq y1 y2) -> nadd_eq (nadd_mul y0 y1) (nadd_mul y0 y2)) -> forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_eq y0 y2) -> nadd_eq (nadd_mul y1 y0) (nadd_mul y1 y2).
Definition term41 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_mul x0 x1) (nadd_mul x1 x2).
Definition term30 (x0 : nadd) := forall y0 : nadd, (exists y1 : nadd, (nadd_eq x0 y1) /\ (nadd_eq y1 y0)) -> nadd_eq x0 y0.
Definition term38 (x0 : nadd) (x1 : nadd) (x2 : nadd) := and (nadd_eq (nadd_mul x0 x1) (nadd_mul x1 x2)).
Definition term49 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nadd => (nadd_eq (nadd_mul x0 x2) y0) /\ (nadd_eq y0 (nadd_mul x1 x2)).
Definition term47 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nadd => (nadd_eq (nadd_mul x0 x1) y0) /\ (nadd_eq y0 (nadd_mul x1 x2)).
Definition term54 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := nadd_eq (nadd_mul x0 x1) (nadd_mul x2 x3).
Definition term52 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := exists y0 : nadd, (nadd_eq (nadd_mul x0 x1) y0) /\ (nadd_eq y0 (nadd_mul x2 x3)).
Definition term48 (x0 : nadd) (x1 : nadd) (x2 : nadd) := exists y0 : nadd, (nadd_eq (nadd_mul x0 x2) y0) /\ (nadd_eq y0 (nadd_mul x1 x2)).
Definition term46 (x0 : nadd) (x1 : nadd) (x2 : nadd) := exists y0 : nadd, (nadd_eq (nadd_mul x0 x1) y0) /\ (nadd_eq y0 (nadd_mul x1 x2)).
Definition term45 (x0 : nadd) (x1 : nadd) (x2 : nadd) := True /\ (nadd_eq (nadd_mul x1 x0) (nadd_mul x1 x2)).
Definition term15 (x0 : nadd) := forall y0 : nadd, nadd_eq (nadd_mul x0 y0) (nadd_mul y0 x0).
Definition term53 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := fun y0 : nadd => (nadd_eq (nadd_mul x0 x1) y0) /\ (nadd_eq y0 (nadd_mul x2 x3)).
Definition term6 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq x0 x2) -> nadd_eq (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term19 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) x0.
Definition term12 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_eq y0 y2) -> nadd_eq (nadd_mul y1 y0) (nadd_mul y1 y2)) x0.
Definition term1 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_eq y1 y2) -> nadd_eq (nadd_mul y0 y1) (nadd_mul y0 y2)) x0.
Definition term43 (x0 : nadd) (x1 : nadd) := and (nadd_eq (nadd_mul x1 x0) (nadd_mul x0 x1)).
Definition term42 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (exists y0 : nadd, (nadd_eq (nadd_mul x0 x1) y0) /\ (nadd_eq y0 (nadd_mul x1 x2))) -> nadd_eq (nadd_mul x0 x1) (nadd_mul x1 x2).
Definition term17 (x0 : nadd) (x1 : nadd) := nadd_eq (nadd_mul x1 x0) (nadd_mul x0 x1).
Definition term23 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => ((nadd_eq x1 x0) /\ (nadd_eq x0 y0)) -> nadd_eq x1 y0) x2.
Definition term44 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_mul x0 x1) (nadd_mul x1 x0)) /\ (nadd_eq (nadd_mul x1 x0) (nadd_mul x1 x2)).
Definition term37 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (exists y0 : nadd, (nadd_eq (nadd_mul x0 x2) y0) /\ (nadd_eq y0 (nadd_mul x1 x2))) -> nadd_eq (nadd_mul x0 x2) (nadd_mul x1 x2).
Definition term29 (x0 : nadd) (x1 : nadd) := (exists y0 : nadd, (nadd_eq x0 y0) /\ (nadd_eq y0 x1)) -> nadd_eq x0 x1.
Definition term40 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_mul x0 x1) (nadd_mul x1 x2)) /\ True.
Definition term27 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (nadd_eq x0 y0) /\ (nadd_eq y0 x1).
Definition term4 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) -> nadd_eq (nadd_mul x1 x0) (nadd_mul x1 y0).
Definition term8 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_eq y1 y2) -> nadd_eq (nadd_mul y0 y1) (nadd_mul y0 y2)) -> nadd_eq (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term55 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ (nadd_eq x1 x3)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul x2 x3).
Definition term51 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq (nadd_mul x0 x1) (nadd_mul x2 x1)) /\ (nadd_eq (nadd_mul x2 x1) (nadd_mul x2 x3)).
Definition term39 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_mul x0 x2) (nadd_mul x2 x1)) /\ (nadd_eq (nadd_mul x2 x1) (nadd_mul x1 x2)).
Definition term36 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (exists y0 : nadd, (nadd_eq (nadd_mul x0 x1) y0) /\ (nadd_eq y0 (nadd_mul x2 x3))) -> nadd_eq (nadd_mul x0 x1) (nadd_mul x2 x3).
Definition term22 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ((nadd_eq x1 x0) /\ (nadd_eq x0 y0)) -> nadd_eq x1 y0.
Definition term26 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) -> nadd_eq x0 x1.
Definition term16 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => nadd_eq (nadd_mul x0 y0) (nadd_mul y0 x0)) x1.
Definition term56 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul x2 y0).
Definition term21 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y0 y1)) -> nadd_eq x0 y1) x1.
Definition term13 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq x0 y1) -> nadd_eq (nadd_mul y0 x0) (nadd_mul y0 y1)) x1.
Definition term3 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) -> nadd_eq (nadd_mul x0 y0) (nadd_mul x0 y1)) x1.
Definition term25 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq x0 x1) /\ (nadd_eq x1 x2).
Definition term28 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_eq x0 y0) /\ (nadd_eq y0 x1).
