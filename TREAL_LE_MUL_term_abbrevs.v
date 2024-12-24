Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term84 := @eq Prop (forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y0) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y0 y1)).
Definition term118 := hreal_of_num (NUMERAL 0).
Definition term82 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y0) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y0 y1).
Definition term4 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_le x0 x1) -> hreal_le (hreal_mul x0 y0) (hreal_mul x1 y0).
Definition term15 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => (hreal_add x0 (hreal_add x1 y0)) = (hreal_add (hreal_add x0 x1) y0).
Definition term59 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @pair hreal hreal (hreal_add (hreal_mul x0 x3) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term108 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y2)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) y2)) (@pair hreal hreal y0 y1).
Definition term91 := fun y0 : hreal => forall y1 : hreal, (fun y2 : prod hreal hreal => forall y3 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y2) /\ (treal_le (treal_of_num (NUMERAL 0)) y3)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y2 y3)) (@pair hreal hreal y0 y1).
Definition term149 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => hreal_le (hreal_add (hreal_mul x0 x2) (hreal_mul x1 y0)) (hreal_add (hreal_mul x0 y0) (hreal_mul x1 x2)).
Definition term106 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) y1)) (@pair hreal hreal x2 y0).
Definition term19 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, (hreal_add x0 (hreal_add y0 y1)) = (hreal_add (hreal_add x0 y0) y1).
Definition term147 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := ((hreal_le x2 x0) /\ (hreal_le x3 x1)) -> hreal_le (hreal_add (hreal_mul x0 x3) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term72 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term49 (x0 : hreal) := (fun y0 : hreal => (hreal_add (hreal_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term156 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_add (hreal_mul x0 x2) (hreal_mul x1 (hreal_add x2 x3)).
Definition term66 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add x2 y0))) x3.
Definition term64 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_le (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add y0 y1))) x2.
Definition term55 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => forall y1 : hreal, (treal_mul (@pair hreal hreal x0 y0) (@pair hreal hreal y1 x1)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y1) (hreal_mul y0 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul y0 y1)))) x2.
Definition term81 := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y1) /\ (treal_le (treal_of_num (NUMERAL 0)) y2)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y1 y2)) y0.
Definition term155 (x0 : hreal) (x1 : hreal) := hreal_add (hreal_mul x0 x1).
Definition term165 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add (hreal_mul x0 x3) (hreal_add (hreal_mul x2 x3) (hreal_mul x2 x1))) (hreal_add (hreal_mul x0 x3) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3))).
Definition term121 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x2 x3)).
Definition term145 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_add (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)) (hreal_of_num (NUMERAL 0)).
Definition term45 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (hreal_le x0 y0) -> exists y1 : hreal, y0 = (hreal_add x0 y1)) x1.
Definition term14 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add (hreal_add x0 x1) x2.
Definition term128 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3).
Definition term112 := @pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0)).
Definition term144 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term152 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add (hreal_mul x0 x3) (hreal_mul x2 (hreal_add x3 x1))) (hreal_add (hreal_mul x0 (hreal_add x3 x1)) (hreal_mul x2 x3)).
Definition term113 := treal_le (treal_of_num (NUMERAL 0)).
Definition term162 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_add (hreal_mul x0 (hreal_add x3 x1)) (hreal_mul x2 x3).
Definition term86 (x0 : hreal) (x1 : hreal) := forall y0 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y0)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) y0).
Definition term80 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) x0) /\ (treal_le (treal_of_num (NUMERAL 0)) y0)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul x0 y0).
Definition term68 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add x0 x1) (hreal_add x2 x3).
Definition term5 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => (hreal_le x0 x1) -> hreal_le (hreal_mul x0 y0) (hreal_mul x1 y0)) x2.
Definition term89 (x0 : hreal) := forall y0 : hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y1) /\ (treal_le (treal_of_num (NUMERAL 0)) y2)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y1 y2)) (@pair hreal hreal x0 y0).
Definition term100 (x0 : hreal) (x1 : hreal) := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) y1)) y0).
Definition term83 := @eq Prop (forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y1) /\ (treal_le (treal_of_num (NUMERAL 0)) y2)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y1 y2)) y0).
Definition term87 (x0 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y1) /\ (treal_le (treal_of_num (NUMERAL 0)) y2)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y1 y2)) (@pair hreal hreal x0 y0).
Definition term166 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add (hreal_mul x2 x3) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term146 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add (hreal_mul x0 x3) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term62 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_le (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = (hreal_le (hreal_add x0 y0) (hreal_add y1 y2))) x1.
Definition term53 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (treal_mul (@pair hreal hreal x0 y1) (@pair hreal hreal y2 y0)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y2) (hreal_mul y1 y0)) (hreal_add (hreal_mul x0 y0) (hreal_mul y1 y2)))) x1.
Definition term158 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add (hreal_mul x0 x2) (hreal_mul x1 (hreal_add x2 x3))).
Definition term163 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_add (hreal_add (hreal_mul x0 x3) (hreal_mul x0 x1)) (hreal_mul x2 x3).
Definition term6 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (hreal_le x0 x1) -> hreal_le (hreal_mul x0 x2) (hreal_mul x1 x2).
Definition term131 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, ((hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x2) (hreal_add x0 (hreal_of_num (NUMERAL 0)))) /\ (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) y0) (hreal_add x1 (hreal_of_num (NUMERAL 0))))) -> hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_mul x0 y0) (hreal_mul x2 x1))) (hreal_add (hreal_add (hreal_mul x0 x1) (hreal_mul x2 y0)) (hreal_of_num (NUMERAL 0))).
Definition term107 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x2 y0))) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) (@pair hreal hreal x2 y0)).
Definition term115 (x0 : hreal) (x1 : hreal) := treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1).
Definition term50 (x0 : hreal) := hreal_add (hreal_of_num (NUMERAL 0)) x0.
Definition term153 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @eq Prop ((fun y0 : hreal => hreal_le (hreal_add (hreal_mul x0 x2) (hreal_mul x1 y0)) (hreal_add (hreal_mul x0 y0) (hreal_mul x1 x2))) x3).
Definition term42 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add (hreal_mul x1 x0) (hreal_mul x1 x2).
Definition term29 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => (hreal_add (hreal_add x0 x1) y0) = (hreal_add x0 (hreal_add x1 y0))) x2.
Definition term57 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (treal_mul (@pair hreal hreal x0 x2) (@pair hreal hreal y0 x1)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y0) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 y0)))) x3.
Definition term111 := treal_of_num (NUMERAL 0).
Definition term124 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := imp ((hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x0) (hreal_add x1 (hreal_of_num (NUMERAL 0)))) /\ (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x2) (hreal_add x3 (hreal_of_num (NUMERAL 0))))).
Definition term7 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_le (hreal_mul x0 x2) (hreal_mul x1 x2).
Definition term34 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => (hreal_le (hreal_add x0 x1) (hreal_add x0 y0)) = (hreal_le x1 y0)) x2.
Definition term41 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_mul x0 (hreal_add x1 x2).
Definition term143 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3))).
Definition term8 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_le y0 y1) -> hreal_le (hreal_mul y0 y2) (hreal_mul y1 y2)) -> hreal_le (hreal_mul x0 x2) (hreal_mul x1 x2).
Definition term48 (x0 : hreal) := hreal_add x0 (hreal_of_num (NUMERAL 0)).
Definition term35 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_le (hreal_add x1 x0) (hreal_add x1 x2).
Definition term127 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_mul x0 x3) (hreal_mul x2 x1))) (hreal_add (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)) (hreal_of_num (NUMERAL 0))).
Definition term161 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add (hreal_add (hreal_mul x1 x0) (hreal_mul x1 x2)).
Definition term130 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => ((hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x2) (hreal_add x0 (hreal_of_num (NUMERAL 0)))) /\ (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) y0) (hreal_add x1 (hreal_of_num (NUMERAL 0))))) -> hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_mul x0 y0) (hreal_mul x2 x1))) (hreal_add (hreal_add (hreal_mul x0 x1) (hreal_mul x2 y0)) (hreal_of_num (NUMERAL 0))).
Definition term137 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, ((hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) y1) (hreal_add y0 (hreal_of_num (NUMERAL 0)))) /\ (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) y3) (hreal_add y2 (hreal_of_num (NUMERAL 0))))) -> hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_mul y0 y3) (hreal_mul y1 y2))) (hreal_add (hreal_add (hreal_mul y0 y2) (hreal_mul y1 y3)) (hreal_of_num (NUMERAL 0))).
Definition term135 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, ((hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) y0) (hreal_add x0 (hreal_of_num (NUMERAL 0)))) /\ (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) y2) (hreal_add y1 (hreal_of_num (NUMERAL 0))))) -> hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_mul x0 y2) (hreal_mul y0 y1))) (hreal_add (hreal_add (hreal_mul x0 y1) (hreal_mul y0 y2)) (hreal_of_num (NUMERAL 0))).
Definition term133 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, ((hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x1) (hreal_add x0 (hreal_of_num (NUMERAL 0)))) /\ (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) y1) (hreal_add y0 (hreal_of_num (NUMERAL 0))))) -> hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_mul x0 y1) (hreal_mul x1 y0))) (hreal_add (hreal_add (hreal_mul x0 y0) (hreal_mul x1 y1)) (hreal_of_num (NUMERAL 0))).
Definition term110 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal y0 y1))) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) (@pair hreal hreal y0 y1)).
Definition term95 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y2)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) y2)) (@pair hreal hreal y0 y1).
Definition term93 := forall y0 : hreal, forall y1 : hreal, forall y2 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal y0 y1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y2)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal y0 y1) y2).
Definition term90 (x0 : hreal) := forall y0 : hreal, forall y1 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 y0)) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 y0) y1).
Definition term77 := forall y0 : hreal, forall y1 : hreal, (fun y2 : prod hreal hreal => forall y3 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y2) /\ (treal_le (treal_of_num (NUMERAL 0)) y3)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y2 y3)) (@pair hreal hreal y0 y1).
Definition term75 (x0 : type1233) := forall y0 : hreal, forall y1 : hreal, x0 (@pair hreal hreal y0 y1).
Definition term63 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_le (@pair hreal hreal x0 y1) (@pair hreal hreal y0 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add y0 y1)).
Definition term61 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_le (@pair hreal hreal x0 y2) (@pair hreal hreal y1 y0)) = (hreal_le (hreal_add x0 y0) (hreal_add y1 y2)).
Definition term54 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, forall y1 : hreal, (treal_mul (@pair hreal hreal x0 y0) (@pair hreal hreal y1 x1)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y1) (hreal_mul y0 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul y0 y1))).
Definition term52 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (treal_mul (@pair hreal hreal x0 y1) (@pair hreal hreal y2 y0)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y2) (hreal_mul y1 y0)) (hreal_add (hreal_mul x0 y0) (hreal_mul y1 y2))).
Definition term37 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_mul x0 (hreal_add y0 y1)) = (hreal_add (hreal_mul x0 y0) (hreal_mul x0 y1)).
Definition term31 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_le (hreal_add x0 y0) (hreal_add x0 y1)) = (hreal_le y0 y1).
Definition term26 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_add (hreal_add y0 y1) y2) = (hreal_add y0 (hreal_add y1 y2)).
Definition term25 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_add y0 (hreal_add y1 y2)) = (hreal_add (hreal_add y0 y1) y2).
Definition term22 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_add (hreal_add x0 y0) y1) = (hreal_add x0 (hreal_add y0 y1)).
Definition term21 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_add x0 (hreal_add y0 y1)) = (hreal_add (hreal_add x0 y0) y1).
Definition term2 (x0 : hreal) := forall y0 : hreal, forall y1 : hreal, (hreal_le x0 y0) -> hreal_le (hreal_mul x0 y1) (hreal_mul y0 y1).
Definition term0 := forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_le y0 y1) -> hreal_le (hreal_mul y0 y2) (hreal_mul y1 y2).
Definition term138 (x0 : hreal) := hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x0).
Definition term70 (x0 : nat) := @pair hreal hreal (hreal_of_num x0) (hreal_of_num (NUMERAL 0)).
Definition term154 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := @eq Prop (hreal_le (hreal_add (hreal_mul x0 x3) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3))).
Definition term97 (x0 : hreal) (x1 : hreal) (x2 : prod hreal hreal) := (fun y0 : prod hreal hreal => ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y0)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) y0)) x2.
Definition term78 := fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y0) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y0 y1).
Definition term101 (x0 : hreal) (x1 : hreal) := @eq Prop (forall y0 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y0)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) y0)).
Definition term9 := (forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_le y0 y1) -> hreal_le (hreal_mul y0 y2) (hreal_mul y1 y2)) -> forall y0 : hreal, forall y1 : hreal, forall y2 : hreal, (hreal_le y0 y1) -> hreal_le (hreal_mul y0 y2) (hreal_mul y1 y2).
Definition term141 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := imp ((hreal_le x0 x1) /\ (hreal_le x2 x3)).
Definition term56 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_mul (@pair hreal hreal x0 x2) (@pair hreal hreal y0 x1)) = (@pair hreal hreal (hreal_add (hreal_mul x0 y0) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 y0))).
Definition term17 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_add x0 (hreal_add x1 y0)) = (hreal_add (hreal_add x0 x1) y0).
Definition term114 := treal_le (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))).
Definition term170 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (hreal_le x3 x1) -> hreal_le (hreal_add (hreal_mul x0 x3) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term47 (x0 : hreal) := (fun y0 : hreal => (hreal_add y0 (hreal_of_num (NUMERAL 0))) = y0) x0.
Definition term136 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, ((hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) y1) (hreal_add y0 (hreal_of_num (NUMERAL 0)))) /\ (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) y3) (hreal_add y2 (hreal_of_num (NUMERAL 0))))) -> hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_mul y0 y3) (hreal_mul y1 y2))) (hreal_add (hreal_add (hreal_mul y0 y2) (hreal_mul y1 y3)) (hreal_of_num (NUMERAL 0))).
Definition term134 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, ((hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) y0) (hreal_add x0 (hreal_of_num (NUMERAL 0)))) /\ (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) y2) (hreal_add y1 (hreal_of_num (NUMERAL 0))))) -> hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_mul x0 y2) (hreal_mul y0 y1))) (hreal_add (hreal_add (hreal_mul x0 y1) (hreal_mul y0 y2)) (hreal_of_num (NUMERAL 0))).
Definition term92 := fun y0 : hreal => forall y1 : hreal, forall y2 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal y0 y1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y2)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal y0 y1) y2).
Definition term24 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add (hreal_add y0 y1) y2) = (hreal_add y0 (hreal_add y1 y2)).
Definition term23 := fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add y0 (hreal_add y1 y2)) = (hreal_add (hreal_add y0 y1) y2).
Definition term74 (x0 : type1233) := forall y0 : prod hreal hreal, x0 y0.
Definition term132 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => forall y1 : hreal, ((hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x1) (hreal_add x0 (hreal_of_num (NUMERAL 0)))) /\ (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) y1) (hreal_add y0 (hreal_of_num (NUMERAL 0))))) -> hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_mul x0 y1) (hreal_mul x1 y0))) (hreal_add (hreal_add (hreal_mul x0 y0) (hreal_mul x1 y1)) (hreal_of_num (NUMERAL 0))).
Definition term109 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => forall y1 : hreal, ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal y0 y1))) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) (@pair hreal hreal y0 y1)).
Definition term20 (x0 : hreal) := fun y0 : hreal => forall y1 : hreal, (hreal_add (hreal_add x0 y0) y1) = (hreal_add x0 (hreal_add y0 y1)).
Definition term150 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => hreal_le (hreal_add (hreal_mul x0 x2) (hreal_mul x1 y0)) (hreal_add (hreal_mul x0 y0) (hreal_mul x1 x2))) x3.
Definition term33 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_le (hreal_add x0 x1) (hreal_add x0 y0)) = (hreal_le x1 y0).
Definition term79 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y0) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y0 y1)) x0.
Definition term40 (x0 : hreal) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => (hreal_mul x1 (hreal_add x0 y0)) = (hreal_add (hreal_mul x1 x0) (hreal_mul x1 y0))) x2.
Definition term16 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => (hreal_add (hreal_add x0 x1) y0) = (hreal_add x0 (hreal_add x1 y0)).
Definition term73 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term116 (x0 : hreal) (x1 : hreal) := treal_le (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal x0 x1).
Definition term12 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (hreal_add x0 y0) = (hreal_add y0 x0)) x1.
Definition term148 (x0 : hreal) (x1 : hreal) := exists y0 : hreal, x0 = (hreal_add x1 y0).
Definition term43 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) -> exists y2 : hreal, y1 = (hreal_add y0 y2)) x0.
Definition term10 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_add y0 y1) = (hreal_add y1 y0)) x0.
Definition term103 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x2 x3))) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3)).
Definition term94 (x0 : hreal) (x1 : hreal) := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) y1)) y0.
Definition term122 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x0) (hreal_add x1 (hreal_of_num (NUMERAL 0)))) /\ (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x2) (hreal_add x3 (hreal_of_num (NUMERAL 0)))).
Definition term96 (x0 : hreal) (x1 : hreal) := fun y0 : prod hreal hreal => ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y0)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) y0).
Definition term58 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_mul (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term38 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_mul x0 (hreal_add y0 y1)) = (hreal_add (hreal_mul x0 y0) (hreal_mul x0 y1))) x1.
Definition term32 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_le (hreal_add x0 y0) (hreal_add x0 y1)) = (hreal_le y0 y1)) x1.
Definition term28 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_add (hreal_add x0 y0) y1) = (hreal_add x0 (hreal_add y0 y1))) x1.
Definition term3 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_le x0 y0) -> hreal_le (hreal_mul x0 y1) (hreal_mul y0 y1)) x1.
Definition term102 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : prod hreal hreal => ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y0)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) y0)) (@pair hreal hreal x2 x3).
Definition term123 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := imp ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x2 x3))).
Definition term157 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_add (hreal_mul x0 x1) (hreal_add (hreal_mul x2 x1) (hreal_mul x2 x3)).
Definition term85 (x0 : hreal) (x1 : hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y0) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y0 y1)) (@pair hreal hreal x0 x1).
Definition term125 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3)).
Definition term67 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_le (@pair hreal hreal x0 x1) (@pair hreal hreal x2 x3).
Definition term69 (x0 : nat) := (fun y0 : nat => (treal_of_num y0) = (@pair hreal hreal (hreal_of_num y0) (hreal_of_num (NUMERAL 0)))) x0.
Definition term126 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := treal_le (@pair hreal hreal (hreal_of_num (NUMERAL 0)) (hreal_of_num (NUMERAL 0))) (@pair hreal hreal (hreal_add (hreal_mul x0 x3) (hreal_mul x2 x1)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3))).
Definition term18 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_add (hreal_add x0 x1) y0) = (hreal_add x0 (hreal_add x1 y0)).
Definition term76 := forall y0 : prod hreal hreal, (fun y1 : prod hreal hreal => forall y2 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) y1) /\ (treal_le (treal_of_num (NUMERAL 0)) y2)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul y1 y2)) y0.
Definition term65 (x0 : hreal) (x1 : hreal) (x2 : hreal) := forall y0 : hreal, (treal_le (@pair hreal hreal x0 y0) (@pair hreal hreal x2 x1)) = (hreal_le (hreal_add x0 x1) (hreal_add x2 y0)).
Definition term39 (x0 : hreal) (x1 : hreal) := forall y0 : hreal, (hreal_mul x1 (hreal_add x0 y0)) = (hreal_add (hreal_mul x1 x0) (hreal_mul x1 y0)).
Definition term119 (x0 : hreal) (x1 : hreal) := and (treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)).
Definition term105 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x2 y0))) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) (@pair hreal hreal x2 y0)).
Definition term160 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add (hreal_mul x0 (hreal_add x1 x2)).
Definition term46 (x0 : hreal) (x1 : hreal) := (hreal_le x1 x0) -> exists y0 : hreal, x0 = (hreal_add x1 y0).
Definition term164 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_add (hreal_mul x0 x3) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term117 (x0 : hreal) (x1 : hreal) := hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x0) (hreal_add x1 (hreal_of_num (NUMERAL 0))).
Definition term11 (x0 : hreal) := forall y0 : hreal, (hreal_add x0 y0) = (hreal_add y0 x0).
Definition term168 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add (hreal_mul x0 x1) (hreal_mul x0 x3)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term120 (x0 : hreal) (x1 : hreal) := and (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x0) (hreal_add x1 (hreal_of_num (NUMERAL 0)))).
Definition term13 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_add x0 (hreal_add x1 x2).
Definition term151 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => hreal_le (hreal_add (hreal_mul x0 x2) (hreal_mul x1 y0)) (hreal_add (hreal_mul x0 y0) (hreal_mul x1 x2))) (hreal_add x2 x3).
Definition term142 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_add (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)).
Definition term44 (x0 : hreal) := forall y0 : hreal, (hreal_le x0 y0) -> exists y1 : hreal, y0 = (hreal_add x0 y1).
Definition term139 (x0 : hreal) (x1 : hreal) := and (hreal_le x0 x1).
Definition term98 (x0 : hreal) (x1 : hreal) (x2 : prod hreal hreal) := ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) x2)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) x2).
Definition term104 (x0 : hreal) (x1 : hreal) (x2 : hreal) := fun y0 : hreal => (fun y1 : prod hreal hreal => ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) y1)) (@pair hreal hreal x2 y0).
Definition term88 (x0 : hreal) := fun y0 : hreal => forall y1 : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 y0)) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 y0) y1).
Definition term99 (x0 : hreal) (x1 : hreal) := fun y0 : prod hreal hreal => (fun y1 : prod hreal hreal => ((treal_le (treal_of_num (NUMERAL 0)) (@pair hreal hreal x0 x1)) /\ (treal_le (treal_of_num (NUMERAL 0)) y1)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul (@pair hreal hreal x0 x1) y1)) y0.
Definition term140 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := (hreal_le x0 x1) /\ (hreal_le x2 x3).
Definition term167 (x0 : hreal) (x1 : hreal) (x2 : hreal) := hreal_le (hreal_add (hreal_mul x1 x0) (hreal_mul x1 x2)).
Definition term159 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := hreal_le (hreal_add (hreal_mul x0 x1) (hreal_add (hreal_mul x2 x1) (hreal_mul x2 x3))).
Definition term71 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term60 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_le (@pair hreal hreal y0 y3) (@pair hreal hreal y2 y1)) = (hreal_le (hreal_add y0 y1) (hreal_add y2 y3))) x0.
Definition term51 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, forall y3 : hreal, (treal_mul (@pair hreal hreal y0 y2) (@pair hreal hreal y3 y1)) = (@pair hreal hreal (hreal_add (hreal_mul y0 y3) (hreal_mul y2 y1)) (hreal_add (hreal_mul y0 y1) (hreal_mul y2 y3)))) x0.
Definition term36 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_mul y0 (hreal_add y1 y2)) = (hreal_add (hreal_mul y0 y1) (hreal_mul y0 y2))) x0.
Definition term30 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_le (hreal_add y0 y1) (hreal_add y0 y2)) = (hreal_le y1 y2)) x0.
Definition term27 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_add (hreal_add y0 y1) y2) = (hreal_add y0 (hreal_add y1 y2))) x0.
Definition term1 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, forall y2 : hreal, (hreal_le y0 y1) -> hreal_le (hreal_mul y0 y2) (hreal_mul y1 y2)) x0.
Definition term169 (x0 : hreal) (x1 : hreal) := fun y0 : hreal => x0 = (hreal_add x1 y0).
Definition term129 (x0 : hreal) (x1 : hreal) (x2 : hreal) (x3 : hreal) := ((hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x2) (hreal_add x0 (hreal_of_num (NUMERAL 0)))) /\ (hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) x3) (hreal_add x1 (hreal_of_num (NUMERAL 0))))) -> hreal_le (hreal_add (hreal_of_num (NUMERAL 0)) (hreal_add (hreal_mul x0 x3) (hreal_mul x2 x1))) (hreal_add (hreal_add (hreal_mul x0 x1) (hreal_mul x2 x3)) (hreal_of_num (NUMERAL 0))).
