Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term34 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_eq x1 x0) /\ (nadd_eq x0 x2)) -> nadd_eq x1 x2.
Definition term82 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := nadd_le (nadd_add (nadd_mul x2 x0) (nadd_mul x2 x1)) (nadd_mul x2 x3).
Definition term73 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) -> exists y2 : nadd, nadd_eq y1 (nadd_add y0 y2)) x0.
Definition term71 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (exists y2 : nadd, (nadd_le y0 y2) /\ (nadd_le y2 y1)) -> nadd_le y0 y1) x0.
Definition term52 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, nadd_le y0 (nadd_add y0 y1)) x0.
Definition term46 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) -> nadd_le y0 y1) x0.
Definition term43 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (exists y2 : nadd, (nadd_eq y0 y2) /\ (nadd_eq y2 y1)) -> nadd_eq y0 y1) x0.
Definition term25 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = (nadd_eq y1 y0)) x0.
Definition term7 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (fun y0 : nadd => ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul x2 y0)) x3.
Definition term11 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> nadd_eq (nadd_mul y0 y2) (nadd_mul y1 y3)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul x2 x3).
Definition term100 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x0 x0) /\ (nadd_eq x1 (nadd_add x2 x3)).
Definition term48 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) -> nadd_le x0 y0) x1.
Definition term62 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_le x1 x0) /\ (nadd_le x0 x2)) -> nadd_le x1 x2.
Definition term88 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_add (nadd_mul x0 x1) (nadd_mul x0 x2)) (nadd_mul x0 (nadd_add x1 x2)).
Definition term106 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term26 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = (nadd_eq y0 x0).
Definition term111 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2).
Definition term110 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul x0 y0) (nadd_mul x0 y1).
Definition term69 := forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, (nadd_le y0 y2) /\ (nadd_le y2 y1)) -> nadd_le y0 y1.
Definition term58 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_le x0 y0) /\ (nadd_le y0 y1)) -> nadd_le x0 y1.
Definition term56 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_le y0 y1) /\ (nadd_le y1 y2)) -> nadd_le y0 y2.
Definition term45 := forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) -> nadd_le y0 y1.
Definition term41 := forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, (nadd_eq y0 y2) /\ (nadd_eq y2 y1)) -> nadd_eq y0 y1.
Definition term30 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y0 y1)) -> nadd_eq x0 y1.
Definition term28 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2.
Definition term20 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul x0 (nadd_add y0 y1)) (nadd_add (nadd_mul x0 y0) (nadd_mul x0 y1)).
Definition term14 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y2) /\ (nadd_eq y1 y3)) -> nadd_eq (nadd_mul y0 y1) (nadd_mul y2 y3).
Definition term13 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y1) /\ (nadd_eq y0 y2)) -> nadd_eq (nadd_mul x0 y0) (nadd_mul y1 y2).
Definition term12 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq x1 y1)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul y0 y1).
Definition term4 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> nadd_eq (nadd_mul x0 y0) (nadd_mul x1 y1).
Definition term2 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> nadd_eq (nadd_mul x0 y1) (nadd_mul y0 y2).
Definition term0 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> nadd_eq (nadd_mul y0 y2) (nadd_mul y1 y3).
Definition term87 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (exists y0 : nadd, (nadd_eq (nadd_add (nadd_mul x2 x0) (nadd_mul x2 x1)) y0) /\ (nadd_eq y0 (nadd_mul x2 x3))) -> nadd_eq (nadd_add (nadd_mul x2 x0) (nadd_mul x2 x1)) (nadd_mul x2 x3).
Definition term9 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x0 x1) /\ (nadd_eq x2 x3).
Definition term47 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) -> nadd_le x0 y0.
Definition term86 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_add (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term55 (x0 : nadd) (x1 : nadd) := nadd_le x0 (nadd_add x0 x1).
Definition term61 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => ((nadd_le x1 x0) /\ (nadd_le x0 y0)) -> nadd_le x1 y0) x2.
Definition term72 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (exists y1 : nadd, (nadd_le x0 y1) /\ (nadd_le y1 y0)) -> nadd_le x0 y0) x1.
Definition term44 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (exists y1 : nadd, (nadd_eq x0 y1) /\ (nadd_eq y1 y0)) -> nadd_eq x0 y0) x1.
Definition term70 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_le y0 y1) /\ (nadd_le y1 y2)) -> nadd_le y0 y2) -> forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, (nadd_le y0 y2) /\ (nadd_le y2 y1)) -> nadd_le y0 y1.
Definition term51 := (forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) -> nadd_le y0 y1) -> forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) -> nadd_le y0 y1.
Definition term42 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) -> forall y0 : nadd, forall y1 : nadd, (exists y2 : nadd, (nadd_eq y0 y2) /\ (nadd_eq y2 y1)) -> nadd_eq y0 y1.
Definition term15 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> nadd_eq (nadd_mul y0 y2) (nadd_mul y1 y3)) -> forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y2) /\ (nadd_eq y1 y3)) -> nadd_eq (nadd_mul y0 y1) (nadd_mul y2 y3).
Definition term63 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le x0 x1) /\ (nadd_le x1 x2).
Definition term103 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := nadd_eq (nadd_add (nadd_mul x2 x0) (nadd_mul x2 x1)) (nadd_mul x2 x3).
Definition term64 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_le y0 y1) /\ (nadd_le y1 y2)) -> nadd_le y0 y2) -> nadd_le x0 x1.
Definition term50 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) -> nadd_le y0 y1) -> nadd_le x0 x1.
Definition term54 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => nadd_le x0 (nadd_add x0 y0)) x1.
Definition term68 (x0 : nadd) := forall y0 : nadd, (exists y1 : nadd, (nadd_le x0 y1) /\ (nadd_le y1 y0)) -> nadd_le x0 y0.
Definition term40 (x0 : nadd) := forall y0 : nadd, (exists y1 : nadd, (nadd_eq x0 y1) /\ (nadd_eq y1 y0)) -> nadd_eq x0 y0.
Definition term77 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, nadd_eq x0 (nadd_add x1 y0).
Definition term10 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := nadd_eq (nadd_mul x0 x1) (nadd_mul x2 x3).
Definition term17 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y1) /\ (nadd_eq y0 y2)) -> nadd_eq (nadd_mul x0 y0) (nadd_mul y1 y2)) x1.
Definition term3 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> nadd_eq (nadd_mul x0 y1) (nadd_mul y0 y2)) x1.
Definition term107 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => nadd_eq x0 (nadd_add x1 y0).
Definition term94 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq (nadd_add (nadd_mul x2 x0) (nadd_mul x2 x1)) (nadd_mul x2 (nadd_add x0 x1))) /\ (nadd_eq (nadd_mul x2 (nadd_add x0 x1)) (nadd_mul x2 x3)).
Definition term104 (x0 : nadd) (x1 : nadd) (x2 : nadd) := exists y0 : nadd, (nadd_le (nadd_mul x1 x0) y0) /\ (nadd_le y0 (nadd_mul x1 x2)).
Definition term101 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := exists y0 : nadd, (nadd_eq (nadd_add (nadd_mul x2 x0) (nadd_mul x2 x1)) y0) /\ (nadd_eq y0 (nadd_mul x2 x3)).
Definition term93 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := nadd_eq (nadd_mul x1 x0) (nadd_mul x1 (nadd_add x2 x3)).
Definition term95 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq (nadd_mul x1 (nadd_add x2 x3)) (nadd_add (nadd_mul x1 x2) (nadd_mul x1 x3))) /\ (nadd_eq (nadd_mul x1 x0) (nadd_mul x1 (nadd_add x2 x3))).
Definition term80 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_le (nadd_mul x1 x0) (nadd_add (nadd_mul x1 x0) (nadd_mul x1 x2)).
Definition term102 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := fun y0 : nadd => (nadd_eq (nadd_add (nadd_mul x2 x0) (nadd_mul x2 x1)) y0) /\ (nadd_eq y0 (nadd_mul x2 x3)).
Definition term108 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le x0 x2) -> nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term85 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq (nadd_add (nadd_mul x2 x0) (nadd_mul x2 x1)) (nadd_mul x2 x3)) -> nadd_le (nadd_add (nadd_mul x2 x0) (nadd_mul x2 x1)) (nadd_mul x2 x3).
Definition term76 (x0 : nadd) (x1 : nadd) := (nadd_le x1 x0) -> exists y0 : nadd, nadd_eq x0 (nadd_add x1 y0).
Definition term98 (x0 : nadd) := (fun y0 : nadd => nadd_eq y0 y0) x0.
Definition term57 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_le y0 y1) /\ (nadd_le y1 y2)) -> nadd_le y0 y2) x0.
Definition term29 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) x0.
Definition term19 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, nadd_eq (nadd_mul y0 (nadd_add y1 y2)) (nadd_add (nadd_mul y0 y1) (nadd_mul y0 y2))) x0.
Definition term16 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y2) /\ (nadd_eq y1 y3)) -> nadd_eq (nadd_mul y0 y1) (nadd_mul y2 y3)) x0.
Definition term1 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> nadd_eq (nadd_mul y0 y2) (nadd_mul y1 y3)) x0.
Definition term78 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq x0 (nadd_add x1 x2).
Definition term79 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (exists y0 : nadd, (nadd_le (nadd_mul x1 x0) y0) /\ (nadd_le y0 (nadd_mul x1 x2))) -> nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term83 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_le (nadd_mul x2 x0) (nadd_add (nadd_mul x2 x0) (nadd_mul x2 x1))) /\ (nadd_le (nadd_add (nadd_mul x2 x0) (nadd_mul x2 x1)) (nadd_mul x2 x3)).
Definition term18 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq x1 y1)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul y0 y1)) x2.
Definition term5 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> nadd_eq (nadd_mul x0 y0) (nadd_mul x1 y1)) x2.
Definition term49 (x0 : nadd) (x1 : nadd) := (nadd_eq x0 x1) -> nadd_le x0 x1.
Definition term92 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := nadd_eq (nadd_mul x2 (nadd_add x0 x1)) (nadd_mul x2 x3).
Definition term90 (x0 : nadd) (x1 : nadd) (x2 : nadd) := and (nadd_eq (nadd_add (nadd_mul x0 x1) (nadd_mul x0 x2)) (nadd_mul x0 (nadd_add x1 x2))).
Definition term33 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => ((nadd_eq x1 x0) /\ (nadd_eq x0 y0)) -> nadd_eq x1 y0) x2.
Definition term97 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x1 x1) /\ (nadd_eq x0 (nadd_add x2 x3))) -> nadd_eq (nadd_mul x1 x0) (nadd_mul x1 (nadd_add x2 x3)).
Definition term39 (x0 : nadd) (x1 : nadd) := (exists y0 : nadd, (nadd_eq x0 y0) /\ (nadd_eq y0 x1)) -> nadd_eq x0 x1.
Definition term65 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (nadd_le x0 y0) /\ (nadd_le y0 x1).
Definition term37 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (nadd_eq x0 y0) /\ (nadd_eq y0 x1).
Definition term66 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_le x0 y0) /\ (nadd_le y0 x1).
Definition term109 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (nadd_le x0 y0) -> nadd_le (nadd_mul x1 x0) (nadd_mul x1 y0).
Definition term23 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => nadd_eq (nadd_mul x1 (nadd_add x0 y0)) (nadd_add (nadd_mul x1 x0) (nadd_mul x1 y0))) x2.
Definition term8 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ (nadd_eq x1 x3)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul x2 x3).
Definition term24 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_eq (nadd_mul x1 (nadd_add x0 x2)) (nadd_add (nadd_mul x1 x0) (nadd_mul x1 x2)).
Definition term105 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nadd => (nadd_le (nadd_mul x1 x0) y0) /\ (nadd_le y0 (nadd_mul x1 x2)).
Definition term53 (x0 : nadd) := forall y0 : nadd, nadd_le x0 (nadd_add x0 y0).
Definition term96 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := True /\ (nadd_eq (nadd_mul x1 x0) (nadd_mul x1 (nadd_add x2 x3))).
Definition term81 (x0 : nadd) (x1 : nadd) (x2 : nadd) := and (nadd_le (nadd_mul x1 x0) (nadd_add (nadd_mul x1 x0) (nadd_mul x1 x2))).
Definition term60 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ((nadd_le x1 x0) /\ (nadd_le x0 y0)) -> nadd_le x1 y0.
Definition term32 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, ((nadd_eq x1 x0) /\ (nadd_eq x0 y0)) -> nadd_eq x1 y0.
Definition term36 (x0 : nadd) (x1 : nadd) := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) -> nadd_eq x0 x1.
Definition term6 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> nadd_eq (nadd_mul x0 x1) (nadd_mul x2 y0).
Definition term89 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_mul x0 (nadd_add x1 x2).
Definition term59 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_le x0 y0) /\ (nadd_le y0 y1)) -> nadd_le x0 y1) x1.
Definition term31 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y0 y1)) -> nadd_eq x0 y1) x1.
Definition term21 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, nadd_eq (nadd_mul x0 (nadd_add y0 y1)) (nadd_add (nadd_mul x0 y0) (nadd_mul x0 y1))) x1.
Definition term74 (x0 : nadd) := forall y0 : nadd, (nadd_le x0 y0) -> exists y1 : nadd, nadd_eq y0 (nadd_add x0 y1).
Definition term91 (x0 : nadd) (x1 : nadd) (x2 : nadd) := and (nadd_eq (nadd_mul x1 (nadd_add x0 x2)) (nadd_add (nadd_mul x1 x0) (nadd_mul x1 x2))).
Definition term75 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_le x0 y0) -> exists y1 : nadd, nadd_eq y0 (nadd_add x0 y1)) x1.
Definition term27 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = (nadd_eq y0 x0)) x1.
Definition term22 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, nadd_eq (nadd_mul x1 (nadd_add x0 y0)) (nadd_add (nadd_mul x1 x0) (nadd_mul x1 y0)).
Definition term99 (x0 : nadd) := and (nadd_eq x0 x0).
Definition term67 (x0 : nadd) (x1 : nadd) := (exists y0 : nadd, (nadd_le x0 y0) /\ (nadd_le y0 x1)) -> nadd_le x0 x1.
Definition term84 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := True /\ (nadd_le (nadd_add (nadd_mul x2 x0) (nadd_mul x2 x1)) (nadd_mul x2 x3)).
Definition term35 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq x0 x1) /\ (nadd_eq x1 x2).
Definition term38 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_eq x0 y0) /\ (nadd_eq y0 x1).
