Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term75 (x0 : hreal -> real) := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (x0 ((fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) y0)) = y0.
Definition term28 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term27 (x0 : real) := fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term39 (x0 : real) (x1 : hreal -> real) := exists y0 : hreal, x0 = (x1 y0).
Definition term61 (x0 : hreal -> real) := and (forall y0 : hreal, (@ε hreal (fun y1 : hreal => (x0 y0) = (x0 y1))) = y0).
Definition term60 (x0 : hreal -> real) := and (forall y0 : hreal, ((fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) (x0 y0)) = y0).
Definition term63 (x0 : real) (x1 : hreal -> real) := imp (exists y0 : hreal, x0 = (x1 y0)).
Definition term71 (x0 : hreal -> real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x1) -> (x0 ((fun y0 : real => @ε hreal (fun y1 : hreal => y0 = (x0 y1))) x1)) = x1.
Definition term43 (x0 : hreal) (x1 : hreal -> real) (x2 : hreal) := real_le (x1 x0) (x1 x2).
Definition term72 (x0 : hreal -> real) (x1 : real) := (exists y0 : hreal, x1 = (x0 y0)) -> (x0 (@ε hreal (fun y0 : hreal => x1 = (x0 y0)))) = x1.
Definition term113 (x0 : hreal -> real) := fun y0 : hreal => forall y1 : hreal, ((x0 y0) = (x0 y1)) = (y0 = y1).
Definition term21 := fun y0 : hreal => forall y1 : hreal, ((hreal_le y0 y1) /\ (hreal_le y1 y0)) = (y0 = y1).
Definition term117 (x0 : hreal) (x1 : hreal -> real) := fun y0 : hreal => (x1 x0) = (x1 y0).
Definition term129 := exists y0 : real -> hreal, exists y1 : hreal -> real, (forall y2 : hreal, (y0 (y1 y2)) = y2) /\ ((forall y2 : real, (real_le (real_of_num (NUMERAL 0)) y2) -> (y1 (y0 y2)) = y2) /\ ((forall y2 : hreal, real_le (real_of_num (NUMERAL 0)) (y1 y2)) /\ (forall y2 : hreal, forall y3 : hreal, (hreal_le y2 y3) = (real_le (y1 y2) (y1 y3))))).
Definition term99 (x0 : hreal -> real) := (forall y0 : hreal, ((fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) (x0 y0)) = y0) /\ ((forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (x0 ((fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) y0)) = y0) /\ ((forall y0 : hreal, real_le (real_of_num (NUMERAL 0)) (x0 y0)) /\ (forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (real_le (x0 y0) (x0 y1))))).
Definition term11 (a0 : Type') (x0 : a0) := forall y0 : a0, (x0 = y0) = (y0 = x0).
Definition term3 (a0 : Type') (x0 : a0) := exists y0 : a0, x0 = y0.
Definition term78 (x0 : hreal -> real) := and (forall y0 : real, (exists y1 : hreal, y0 = (x0 y1)) -> (x0 (@ε hreal (fun y1 : hreal => y0 = (x0 y1)))) = y0).
Definition term77 (x0 : hreal -> real) := and (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (x0 ((fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) y0)) = y0).
Definition term92 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term62 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) x0).
Definition term74 (x0 : hreal -> real) := fun y0 : real => (exists y1 : hreal, y0 = (x0 y1)) -> (x0 (@ε hreal (fun y1 : hreal => y0 = (x0 y1)))) = y0.
Definition term16 (x0 : hreal) (x1 : hreal) := (hreal_le x1 x0) /\ (hreal_le x0 x1).
Definition term130 := fun y0 : real -> hreal => exists y1 : hreal -> real, (forall y2 : hreal, (y0 (y1 y2)) = y2) /\ ((forall y2 : real, (real_le (real_of_num (NUMERAL 0)) y2) -> (y1 (y0 y2)) = y2) /\ ((forall y2 : hreal, real_le (real_of_num (NUMERAL 0)) (y1 y2)) /\ (forall y2 : hreal, forall y3 : hreal, (hreal_le y2 y3) = (real_le (y1 y2) (y1 y3))))).
Definition term127 (x0 : hreal -> real) := exists y0 : hreal -> real, (forall y1 : hreal, ((fun y2 : real => @ε hreal (fun y3 : hreal => y2 = (x0 y3))) (y0 y1)) = y1) /\ ((forall y1 : real, (real_le (real_of_num (NUMERAL 0)) y1) -> (y0 ((fun y2 : real => @ε hreal (fun y3 : hreal => y2 = (x0 y3))) y1)) = y1) /\ ((forall y1 : hreal, real_le (real_of_num (NUMERAL 0)) (y0 y1)) /\ (forall y1 : hreal, forall y2 : hreal, (hreal_le y1 y2) = (real_le (y0 y1) (y0 y2))))).
Definition term49 (x0 : hreal -> real) (x1 : real) := (fun y0 : real => @ε hreal (fun y1 : hreal => y0 = (x0 y1))) x1.
Definition term83 (x0 : hreal -> real) := forall y0 : hreal, real_le (real_of_num (NUMERAL 0)) (x0 y0).
Definition term13 (a0 : Type') (x0 : a0) := @ε a0 (fun y0 : a0 => x0 = y0).
Definition term84 (x0 : hreal -> real) := forall y0 : hreal, exists y1 : hreal, (x0 y0) = (x0 y1).
Definition term105 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0))) x1.
Definition term14 (a0 : Type') (x0 : a0) := @eq a0 (@ε a0 (fun y0 : a0 => y0 = x0)).
Definition term66 (x0 : hreal -> real) (x1 : real) := @eq hreal ((fun y0 : real => @ε hreal (fun y1 : hreal => y0 = (x0 y1))) x1).
Definition term5 (a0 : Type') := fun y0 : a0 => exists y1 : a0, y0 = y1.
Definition term106 (x0 : hreal) (x1 : hreal -> real) (x2 : hreal) := (real_le (x1 x2) (x1 x0)) /\ (real_le (x1 x0) (x1 x2)).
Definition term42 (x0 : hreal) (x1 : hreal -> real) (x2 : hreal) := (fun y0 : hreal => (hreal_le x0 y0) = (real_le (x1 x0) (x1 y0))) x2.
Definition term91 := forall y0 : hreal, True.
Definition term108 (x0 : hreal) (x1 : hreal -> real) (x2 : hreal) := @eq Prop ((real_le (x1 x2) (x1 x0)) /\ (real_le (x1 x0) (x1 x2))).
Definition term7 (a0 : Type') := forall y0 : a0, exists y1 : a0, y0 = y1.
Definition term6 (a0 : Type') := forall y0 : a0, exists y1 : a0, y1 = y0.
Definition term10 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (y0 = y1) = (y1 = y0)) x0.
Definition term33 := forall y0 : real, forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term32 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term114 (a0 : Type') (x0 : a0) := (fun y0 : a0 => exists y1 : a0, y0 = y1) x0.
Definition term131 := fun y0 : hreal -> real => (forall y1 : real, (real_le (real_of_num (NUMERAL 0)) y1) = (exists y2 : hreal, y1 = (y0 y2))) /\ (forall y1 : hreal, forall y2 : hreal, (hreal_le y1 y2) = (real_le (y0 y1) (y0 y2))).
Definition term36 (x0 : hreal -> real) := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : hreal, y0 = (x0 y1)).
Definition term107 (x0 : hreal) (x1 : hreal -> real) (x2 : hreal) := @eq Prop ((x1 x0) = (x1 x2)).
Definition term37 (x0 : hreal -> real) (x1 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : hreal, y0 = (x0 y1))) x1.
Definition term121 (x0 : hreal -> real) := (forall y0 : real, (exists y1 : hreal, y0 = (x0 y1)) -> (x0 (@ε hreal (fun y1 : hreal => y0 = (x0 y1)))) = y0) /\ True.
Definition term47 (x0 : hreal -> real) (x1 : hreal) := (fun y0 : real => @ε hreal (fun y1 : hreal => y0 = (x0 y1))) (x0 x1).
Definition term111 (x0 : hreal -> real) (x1 : hreal) := fun y0 : hreal => ((x0 x1) = (x0 y0)) = (x1 = y0).
Definition term80 (x0 : hreal) (x1 : hreal -> real) := exists y0 : hreal, (x1 x0) = (x1 y0).
Definition term31 := fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term25 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x0 x1).
Definition term124 (x0 : real) (x1 : hreal -> real) := (exists y0 : hreal, x0 = (x1 y0)) -> (fun y0 : hreal => x0 = (x1 y0)) (@ε hreal (fun y0 : hreal => x0 = (x1 y0))).
Definition term51 (x0 : hreal -> real) := fun y0 : real => (fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) y0.
Definition term82 (x0 : hreal -> real) := fun y0 : hreal => exists y1 : hreal, (x0 y0) = (x0 y1).
Definition term76 (x0 : hreal -> real) := forall y0 : real, (exists y1 : hreal, y0 = (x0 y1)) -> (x0 (@ε hreal (fun y1 : hreal => y0 = (x0 y1)))) = y0.
Definition term97 (x0 : hreal -> real) := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (x0 ((fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) y0)) = y0) /\ ((forall y0 : hreal, real_le (real_of_num (NUMERAL 0)) (x0 y0)) /\ (forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (real_le (x0 y0) (x0 y1)))).
Definition term119 (x0 : hreal) := @ε hreal (fun y0 : hreal => x0 = y0).
Definition term101 (x0 : hreal -> real) := forall y0 : hreal, forall y1 : hreal, ((x0 y0) = (x0 y1)) = (y0 = y1).
Definition term35 (x0 : hreal -> real) := forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (real_le (x0 y0) (x0 y1)).
Definition term24 := forall y0 : hreal, forall y1 : hreal, (y0 = y1) = ((hreal_le y0 y1) /\ (hreal_le y1 y0)).
Definition term23 := forall y0 : hreal, forall y1 : hreal, ((hreal_le y0 y1) /\ (hreal_le y1 y0)) = (y0 = y1).
Definition term44 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term68 (x0 : real) (x1 : hreal -> real) := x1 (@ε hreal (fun y0 : hreal => x0 = (x1 y0))).
Definition term122 (x0 : hreal -> real) := True /\ (forall y0 : real, (exists y1 : hreal, y0 = (x0 y1)) -> (x0 (@ε hreal (fun y1 : hreal => y0 = (x0 y1)))) = y0).
Definition term98 (x0 : hreal -> real) := (forall y0 : real, (exists y1 : hreal, y0 = (x0 y1)) -> (x0 (@ε hreal (fun y1 : hreal => y0 = (x0 y1)))) = y0) /\ (forall y0 : hreal, exists y1 : hreal, (x0 y0) = (x0 y1)).
Definition term95 (x0 : hreal -> real) := (forall y0 : hreal, real_le (real_of_num (NUMERAL 0)) (x0 y0)) /\ (forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (real_le (x0 y0) (x0 y1))).
Definition term34 (x0 : hreal -> real) := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) = (exists y1 : hreal, y0 = (x0 y1))) /\ (forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (real_le (x0 y0) (x0 y1))).
Definition term53 (x0 : hreal -> real) (x1 : hreal) := @eq hreal ((fun y0 : real => @ε hreal (fun y1 : hreal => y0 = (x0 y1))) (x0 x1)).
Definition term45 (x0 : real -> hreal) (x1 : real) := (fun y0 : real => x0 y0) x1.
Definition term110 (x0 : hreal) (x1 : hreal -> real) (x2 : hreal) := and (real_le (x1 x0) (x1 x2)).
Definition term56 (x0 : hreal -> real) := fun y0 : hreal => ((fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) (x0 y0)) = y0.
Definition term30 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term15 (a0 : Type') (x0 : a0) := @eq a0 (@ε a0 (fun y0 : a0 => x0 = y0)).
Definition term104 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0))) x0.
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (x0 = y0) = (y0 = x0)) x1.
Definition term125 (x0 : real) (x1 : hreal -> real) := fun y0 : hreal => x0 = (x1 y0).
Definition term59 (x0 : hreal -> real) := forall y0 : hreal, (@ε hreal (fun y1 : hreal => (x0 y0) = (x0 y1))) = y0.
Definition term38 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term48 (x0 : hreal -> real) := fun y0 : real => @ε hreal (fun y1 : hreal => y0 = (x0 y1)).
Definition term128 (x0 : hreal -> real) := fun y0 : hreal -> real => (forall y1 : hreal, ((fun y2 : real => @ε hreal (fun y3 : hreal => y2 = (x0 y3))) (y0 y1)) = y1) /\ ((forall y1 : real, (real_le (real_of_num (NUMERAL 0)) y1) -> (y0 ((fun y2 : real => @ε hreal (fun y3 : hreal => y2 = (x0 y3))) y1)) = y1) /\ ((forall y1 : hreal, real_le (real_of_num (NUMERAL 0)) (y0 y1)) /\ (forall y1 : hreal, forall y2 : hreal, (hreal_le y1 y2) = (real_le (y0 y1) (y0 y2))))).
Definition term2 (a0 : Type') (x0 : a0) := exists y0 : a0, y0 = x0.
Definition term123 (x0 : hreal -> Prop) := (ex x0) -> x0 (@ε hreal x0).
Definition term4 (a0 : Type') := fun y0 : a0 => exists y1 : a0, y1 = y0.
Definition term93 (x0 : Prop) := forall y0 : hreal, x0.
Definition term94 (x0 : hreal -> real) := fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) = (real_le (x0 y0) (x0 y1)).
Definition term22 := fun y0 : hreal => forall y1 : hreal, (y0 = y1) = ((hreal_le y0 y1) /\ (hreal_le y1 y0)).
Definition term26 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term57 (x0 : hreal -> real) := fun y0 : hreal => (@ε hreal (fun y1 : hreal => (x0 y0) = (x0 y1))) = y0.
Definition term0 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term100 (x0 : hreal -> real) := (forall y0 : hreal, (@ε hreal (fun y1 : hreal => (x0 y0) = (x0 y1))) = y0) /\ ((forall y0 : real, (exists y1 : hreal, y0 = (x0 y1)) -> (x0 (@ε hreal (fun y1 : hreal => y0 = (x0 y1)))) = y0) /\ (forall y0 : hreal, exists y1 : hreal, (x0 y0) = (x0 y1))).
Definition term52 (x0 : hreal -> real) (x1 : hreal) := @eq hreal ((fun y0 : real => (fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) y0) (x0 x1)).
Definition term112 (x0 : hreal -> real) (x1 : hreal) := forall y0 : hreal, ((x0 x1) = (x0 y0)) = (x1 = y0).
Definition term19 (x0 : hreal) := forall y0 : hreal, ((hreal_le x0 y0) /\ (hreal_le y0 x0)) = (x0 = y0).
Definition term70 (x0 : real) (x1 : hreal -> real) := @eq real (x1 (@ε hreal (fun y0 : hreal => x0 = (x1 y0)))).
Definition term88 (x0 : hreal) (x1 : hreal -> real) (x2 : hreal) := @eq Prop (real_le (x1 x0) (x1 x2)).
Definition term67 (x0 : hreal -> real) (x1 : real) := x0 ((fun y0 : real => @ε hreal (fun y1 : hreal => y0 = (x0 y1))) x1).
Definition term79 (x0 : hreal -> real) (x1 : hreal) := real_le (real_of_num (NUMERAL 0)) (x0 x1).
Definition term102 (x0 : hreal) := (fun y0 : hreal => forall y1 : hreal, (y0 = y1) = ((hreal_le y0 y1) /\ (hreal_le y1 y0))) x0.
Definition term115 (x0 : hreal -> real) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, ((x0 y0) = (x0 y1)) = (y0 = y1)) x1.
Definition term40 (x0 : hreal -> real) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) = (real_le (x0 y0) (x0 y1))) x1.
Definition term9 (a0 : Type') (x0 : a0) := @ε a0 (fun y0 : a0 => y0 = x0).
Definition term50 (x0 : real) (x1 : hreal -> real) := @ε hreal (fun y0 : hreal => x0 = (x1 y0)).
Definition term18 (x0 : hreal) := fun y0 : hreal => (x0 = y0) = ((hreal_le x0 y0) /\ (hreal_le y0 x0)).
Definition term65 (x0 : hreal -> real) (x1 : real) := @eq hreal ((fun y0 : real => (fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) y0) x1).
Definition term96 (x0 : hreal -> real) := (forall y0 : hreal, exists y1 : hreal, (x0 y0) = (x0 y1)) /\ True.
Definition term87 (x0 : hreal) (x1 : hreal) := @eq Prop (hreal_le x0 x1).
Definition term73 (x0 : hreal -> real) := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> (x0 ((fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) y0)) = y0.
Definition term81 (x0 : hreal -> real) := fun y0 : hreal => real_le (real_of_num (NUMERAL 0)) (x0 y0).
Definition term69 (x0 : hreal -> real) (x1 : real) := @eq real (x0 ((fun y0 : real => @ε hreal (fun y1 : hreal => y0 = (x0 y1))) x1)).
Definition term64 (x0 : hreal -> real) (x1 : real) := (fun y0 : real => (fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) y0) x1.
Definition term103 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => (x0 = y0) = ((hreal_le x0 y0) /\ (hreal_le y0 x0))) x1.
Definition term54 (x0 : hreal) (x1 : hreal -> real) := @ε hreal (fun y0 : hreal => (x1 x0) = (x1 y0)).
Definition term120 (x0 : hreal) := exists y0 : hreal, x0 = y0.
Definition term118 (x0 : hreal) := fun y0 : hreal => x0 = y0.
Definition term90 := fun y0 : hreal => True.
Definition term86 (x0 : hreal -> real) := and (forall y0 : hreal, exists y1 : hreal, (x0 y0) = (x0 y1)).
Definition term46 (x0 : hreal -> real) (x1 : hreal) := (fun y0 : real => (fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) y0) (x0 x1).
Definition term55 (x0 : hreal) (x1 : hreal -> real) := @eq hreal (@ε hreal (fun y0 : hreal => (x1 x0) = (x1 y0))).
Definition term116 (x0 : hreal -> real) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => ((x0 x1) = (x0 y0)) = (x1 = y0)) x2.
Definition term1 (a0 : Type') (x0 : a0) := fun y0 : a0 => x0 = y0.
Definition term29 (x0 : real) := forall y0 : real, (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term109 (x0 : hreal) (x1 : hreal) := and (hreal_le x0 x1).
Definition term126 (x0 : real) (x1 : hreal -> real) := (fun y0 : hreal => x0 = (x1 y0)) (@ε hreal (fun y0 : hreal => x0 = (x1 y0))).
Definition term41 (x0 : hreal) (x1 : hreal -> real) := forall y0 : hreal, (hreal_le x0 y0) = (real_le (x1 x0) (x1 y0)).
Definition term17 (x0 : hreal) := fun y0 : hreal => ((hreal_le x0 y0) /\ (hreal_le y0 x0)) = (x0 = y0).
Definition term89 (x0 : hreal) (x1 : hreal -> real) := fun y0 : hreal => (hreal_le x0 y0) = (real_le (x1 x0) (x1 y0)).
Definition term20 (x0 : hreal) := forall y0 : hreal, (x0 = y0) = ((hreal_le x0 y0) /\ (hreal_le y0 x0)).
Definition term85 (x0 : hreal -> real) := and (forall y0 : hreal, real_le (real_of_num (NUMERAL 0)) (x0 y0)).
Definition term58 (x0 : hreal -> real) := forall y0 : hreal, ((fun y1 : real => @ε hreal (fun y2 : hreal => y1 = (x0 y2))) (x0 y0)) = y0.
Definition term8 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (@ε a0 (fun y1 : a0 => y1 = y0)) = y0) x0.
