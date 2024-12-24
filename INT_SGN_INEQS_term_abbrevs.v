Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term44 (x0 : int) := real_ge (real_of_int (int_sgn x0)) (real_of_int (int_of_num (NUMERAL 0))).
Definition term10 (x0 : int) := real_sgn (real_of_int x0).
Definition term16 := real_of_int (int_of_num (NUMERAL 0)).
Definition term29 (x0 : int) (x1 : int) := real_gt (real_of_int x0) (real_of_int x1).
Definition term11 := real_of_num (NUMERAL 0).
Definition term132 (x0 : int) := real_lt (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term62 (x0 : int) := int_lt (int_sgn x0) (int_of_num (NUMERAL 0)).
Definition term40 (x0 : int) := real_ge (real_sgn (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term149 := (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_le (int_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_lt (int_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : int, (int_ge (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_ge (int_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : int, (int_gt (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_gt (int_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : int, ((int_of_num (NUMERAL 0)) = (int_sgn y0)) = ((int_of_num (NUMERAL 0)) = y0)) /\ ((forall y0 : int, (int_le (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_le y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_lt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_lt y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_ge (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_ge y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_gt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_gt y0 (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0)))))))))))).
Definition term135 := (forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_lt (int_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : int, (int_ge (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_ge (int_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : int, (int_gt (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_gt (int_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : int, ((int_of_num (NUMERAL 0)) = (int_sgn y0)) = ((int_of_num (NUMERAL 0)) = y0)) /\ ((forall y0 : int, (int_le (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_le y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_lt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_lt y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_ge (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_ge y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_gt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_gt y0 (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0))))))))))).
Definition term121 := (forall y0 : int, (int_ge (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_ge (int_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : int, (int_gt (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_gt (int_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : int, ((int_of_num (NUMERAL 0)) = (int_sgn y0)) = ((int_of_num (NUMERAL 0)) = y0)) /\ ((forall y0 : int, (int_le (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_le y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_lt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_lt y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_ge (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_ge y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_gt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_gt y0 (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0)))))))))).
Definition term107 := (forall y0 : int, (int_gt (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_gt (int_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : int, ((int_of_num (NUMERAL 0)) = (int_sgn y0)) = ((int_of_num (NUMERAL 0)) = y0)) /\ ((forall y0 : int, (int_le (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_le y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_lt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_lt y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_ge (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_ge y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_gt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_gt y0 (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0))))))))).
Definition term93 := (forall y0 : int, ((int_of_num (NUMERAL 0)) = (int_sgn y0)) = ((int_of_num (NUMERAL 0)) = y0)) /\ ((forall y0 : int, (int_le (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_le y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_lt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_lt y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_ge (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_ge y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_gt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_gt y0 (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0)))))))).
Definition term3 := (forall y0 : real, ((real_of_num (NUMERAL 0)) = (real_sgn y0)) = ((real_of_num (NUMERAL 0)) = y0)) /\ ((forall y0 : real, (real_le (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_le y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_lt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_lt y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_ge (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_ge y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_gt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))))))).
Definition term2 := (forall y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_gt (real_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : real, ((real_of_num (NUMERAL 0)) = (real_sgn y0)) = ((real_of_num (NUMERAL 0)) = y0)) /\ ((forall y0 : real, (real_le (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_le y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_lt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_lt y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_ge (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_ge y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_gt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))))))))).
Definition term1 := (forall y0 : real, (real_ge (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_ge (real_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_gt (real_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : real, ((real_of_num (NUMERAL 0)) = (real_sgn y0)) = ((real_of_num (NUMERAL 0)) = y0)) /\ ((forall y0 : real, (real_le (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_le y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_lt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_lt y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_ge (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_ge y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_gt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))))))))).
Definition term0 := (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : real, (real_ge (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_ge (real_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_gt (real_of_num (NUMERAL 0)) y0)) /\ ((forall y0 : real, ((real_of_num (NUMERAL 0)) = (real_sgn y0)) = ((real_of_num (NUMERAL 0)) = y0)) /\ ((forall y0 : real, (real_le (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_le y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_lt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_lt y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_ge (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_ge y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_gt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))))))))))).
Definition term17 := int_of_num (NUMERAL 0).
Definition term67 (x0 : int) := int_lt x0 (int_of_num (NUMERAL 0)).
Definition term57 (x0 : int) := real_lt (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term19 (x0 : int) := @eq Prop ((int_sgn x0) = (int_of_num (NUMERAL 0))).
Definition term142 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_sgn x0)).
Definition term46 (x0 : int) := int_ge (int_sgn x0) (int_of_num (NUMERAL 0)).
Definition term128 (x0 : int) := real_lt (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_sgn x0)).
Definition term41 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term51 (x0 : int) := int_ge x0 (int_of_num (NUMERAL 0)).
Definition term115 (x0 : int) := int_ge (int_of_num (NUMERAL 0)) (int_sgn x0).
Definition term91 (x0 : int) := @eq Prop ((int_of_num (NUMERAL 0)) = (int_sgn x0)).
Definition term144 (x0 : int) := @eq Prop (real_le (real_of_num (NUMERAL 0)) (real_sgn (real_of_int x0))).
Definition term139 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term37 := (forall y0 : int, (int_gt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_gt y0 (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0)))).
Definition term56 (x0 : int) := real_lt (real_sgn (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term49 (x0 : int) := real_ge (real_of_int x0).
Definition term131 (x0 : int) := @eq Prop (int_lt (int_of_num (NUMERAL 0)) (int_sgn x0)).
Definition term43 (x0 : int) := real_ge (real_of_int (int_sgn x0)).
Definition term33 (x0 : int) := real_gt (real_of_int x0).
Definition term58 (x0 : int) := real_lt (real_sgn (real_of_int x0)).
Definition term113 := real_ge (real_of_int (int_of_num (NUMERAL 0))).
Definition term63 (x0 : int) := @eq Prop (real_lt (real_sgn (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term34 (x0 : int) := real_gt (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term116 (x0 : int) := @eq Prop (real_ge (real_of_num (NUMERAL 0)) (real_sgn (real_of_int x0))).
Definition term25 (x0 : int) := real_gt (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term71 (x0 : int) := (fun y0 : real => (real_le (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_le y0 (real_of_num (NUMERAL 0)))) (real_of_int x0).
Definition term55 (x0 : int) := (fun y0 : real => (real_lt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_lt y0 (real_of_num (NUMERAL 0)))) (real_of_int x0).
Definition term39 (x0 : int) := (fun y0 : real => (real_ge (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_ge y0 (real_of_num (NUMERAL 0)))) (real_of_int x0).
Definition term23 (x0 : int) := (fun y0 : real => (real_gt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_gt y0 (real_of_num (NUMERAL 0)))) (real_of_int x0).
Definition term9 (x0 : int) := (fun y0 : real => ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) (real_of_int x0).
Definition term14 (x0 : int) := @eq real (real_of_int (int_sgn x0)).
Definition term60 (x0 : int) := real_lt (real_of_int (int_sgn x0)) (real_of_int (int_of_num (NUMERAL 0))).
Definition term105 (x0 : int) := int_gt (int_of_num (NUMERAL 0)) x0.
Definition term75 (x0 : int) := real_le (real_of_int (int_sgn x0)).
Definition term140 := real_le (real_of_num (NUMERAL 0)).
Definition term26 (x0 : int) := real_gt (real_sgn (real_of_int x0)).
Definition term126 := real_lt (real_of_num (NUMERAL 0)).
Definition term42 (x0 : int) := real_ge (real_sgn (real_of_int x0)).
Definition term15 (x0 : nat) := real_of_int (int_of_num x0).
Definition term138 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_sgn (real_of_int x0)).
Definition term133 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) x0.
Definition term30 (x0 : int) := int_gt (int_sgn x0) (int_of_num (NUMERAL 0)).
Definition term82 (x0 : int) := real_le (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term136 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term122 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_lt (real_of_num (NUMERAL 0)) y0).
Definition term108 := forall y0 : real, (real_ge (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_ge (real_of_num (NUMERAL 0)) y0).
Definition term94 := forall y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_gt (real_of_num (NUMERAL 0)) y0).
Definition term86 := forall y0 : real, ((real_of_num (NUMERAL 0)) = (real_sgn y0)) = ((real_of_num (NUMERAL 0)) = y0).
Definition term61 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term88 := @eq real (real_of_num (NUMERAL 0)).
Definition term53 := (forall y0 : int, (int_ge (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_ge y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_gt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_gt y0 (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0))))).
Definition term6 := (forall y0 : real, (real_ge (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_ge y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_gt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))))).
Definition term148 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_le (int_of_num (NUMERAL 0)) y0).
Definition term134 := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_lt (int_of_num (NUMERAL 0)) y0).
Definition term120 := forall y0 : int, (int_ge (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_ge (int_of_num (NUMERAL 0)) y0).
Definition term106 := forall y0 : int, (int_gt (int_of_num (NUMERAL 0)) (int_sgn y0)) = (int_gt (int_of_num (NUMERAL 0)) y0).
Definition term92 := forall y0 : int, ((int_of_num (NUMERAL 0)) = (int_sgn y0)) = ((int_of_num (NUMERAL 0)) = y0).
Definition term102 (x0 : int) := @eq Prop (real_gt (real_of_num (NUMERAL 0)) (real_sgn (real_of_int x0))).
Definition term7 := (forall y0 : real, (real_gt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))).
Definition term130 (x0 : int) := @eq Prop (real_lt (real_of_num (NUMERAL 0)) (real_sgn (real_of_int x0))).
Definition term47 (x0 : int) := @eq Prop (real_ge (real_sgn (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term114 (x0 : int) := real_ge (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_sgn x0)).
Definition term104 (x0 : int) := real_gt (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term118 (x0 : int) := real_ge (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term59 (x0 : int) := real_lt (real_of_int (int_sgn x0)).
Definition term137 (x0 : int) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_le (real_of_num (NUMERAL 0)) y0)) (real_of_int x0).
Definition term123 (x0 : int) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) (real_of_int x0).
Definition term109 (x0 : int) := (fun y0 : real => (real_ge (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_ge (real_of_num (NUMERAL 0)) y0)) (real_of_int x0).
Definition term95 (x0 : int) := (fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_sgn y0)) = (real_gt (real_of_num (NUMERAL 0)) y0)) (real_of_int x0).
Definition term87 (x0 : int) := (fun y0 : real => ((real_of_num (NUMERAL 0)) = (real_sgn y0)) = ((real_of_num (NUMERAL 0)) = y0)) (real_of_int x0).
Definition term45 (x0 : int) (x1 : int) := real_ge (real_of_int x0) (real_of_int x1).
Definition term66 (x0 : int) := real_lt (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term27 (x0 : int) := real_gt (real_of_int (int_sgn x0)).
Definition term73 (x0 : int) := real_le (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term103 (x0 : int) := @eq Prop (int_gt (int_of_num (NUMERAL 0)) (int_sgn x0)).
Definition term119 (x0 : int) := int_ge (int_of_num (NUMERAL 0)) x0.
Definition term127 := real_lt (real_of_int (int_of_num (NUMERAL 0))).
Definition term129 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) (int_sgn x0).
Definition term12 (x0 : int) := real_of_int (int_sgn x0).
Definition term111 (x0 : int) := real_ge (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term13 (x0 : int) := @eq real (real_sgn (real_of_int x0)).
Definition term28 (x0 : int) := real_gt (real_of_int (int_sgn x0)) (real_of_int (int_of_num (NUMERAL 0))).
Definition term18 (x0 : int) := @eq Prop ((real_sgn (real_of_int x0)) = (real_of_num (NUMERAL 0))).
Definition term24 (x0 : int) := real_gt (real_sgn (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term83 (x0 : int) := int_le x0 (int_of_num (NUMERAL 0)).
Definition term125 (x0 : int) := real_lt (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term72 (x0 : int) := real_le (real_sgn (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term97 (x0 : int) := real_gt (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term76 (x0 : int) := real_le (real_of_int (int_sgn x0)) (real_of_int (int_of_num (NUMERAL 0))).
Definition term80 (x0 : int) := @eq Prop (int_le (int_sgn x0) (int_of_num (NUMERAL 0))).
Definition term143 (x0 : int) := int_le (int_of_num (NUMERAL 0)) (int_sgn x0).
Definition term117 (x0 : int) := @eq Prop (int_ge (int_of_num (NUMERAL 0)) (int_sgn x0)).
Definition term35 (x0 : int) := int_gt x0 (int_of_num (NUMERAL 0)).
Definition term77 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term69 := (forall y0 : int, (int_lt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_lt y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_ge (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_ge y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_gt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_gt y0 (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0)))))).
Definition term5 := (forall y0 : real, (real_lt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_lt y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_ge (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_ge y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_gt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))))).
Definition term48 (x0 : int) := @eq Prop (int_ge (int_sgn x0) (int_of_num (NUMERAL 0))).
Definition term89 := @eq real (real_of_int (int_of_num (NUMERAL 0))).
Definition term74 (x0 : int) := real_le (real_sgn (real_of_int x0)).
Definition term84 := forall y0 : int, (int_le (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_le y0 (int_of_num (NUMERAL 0))).
Definition term68 := forall y0 : int, (int_lt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_lt y0 (int_of_num (NUMERAL 0))).
Definition term52 := forall y0 : int, (int_ge (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_ge y0 (int_of_num (NUMERAL 0))).
Definition term36 := forall y0 : int, (int_gt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_gt y0 (int_of_num (NUMERAL 0))).
Definition term21 := forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0))).
Definition term145 (x0 : int) := @eq Prop (int_le (int_of_num (NUMERAL 0)) (int_sgn x0)).
Definition term32 (x0 : int) := @eq Prop (int_gt (int_sgn x0) (int_of_num (NUMERAL 0))).
Definition term110 (x0 : int) := real_ge (real_of_num (NUMERAL 0)) (real_sgn (real_of_int x0)).
Definition term112 := real_ge (real_of_num (NUMERAL 0)).
Definition term101 (x0 : int) := int_gt (int_of_num (NUMERAL 0)) (int_sgn x0).
Definition term146 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term70 := forall y0 : real, (real_le (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_le y0 (real_of_num (NUMERAL 0))).
Definition term54 := forall y0 : real, (real_lt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_lt y0 (real_of_num (NUMERAL 0))).
Definition term38 := forall y0 : real, (real_ge (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_ge y0 (real_of_num (NUMERAL 0))).
Definition term22 := forall y0 : real, (real_gt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_gt y0 (real_of_num (NUMERAL 0))).
Definition term8 := forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term99 := real_gt (real_of_int (int_of_num (NUMERAL 0))).
Definition term65 (x0 : int) := real_lt (real_of_int x0).
Definition term96 (x0 : int) := real_gt (real_of_num (NUMERAL 0)) (real_sgn (real_of_int x0)).
Definition term81 (x0 : int) := real_le (real_of_int x0).
Definition term50 (x0 : int) := real_ge (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term20 (x0 : int) := @eq real (real_of_int x0).
Definition term147 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term79 (x0 : int) := @eq Prop (real_le (real_sgn (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term90 (x0 : int) := @eq Prop ((real_of_num (NUMERAL 0)) = (real_sgn (real_of_int x0))).
Definition term141 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term124 (x0 : int) := real_lt (real_of_num (NUMERAL 0)) (real_sgn (real_of_int x0)).
Definition term78 (x0 : int) := int_le (int_sgn x0) (int_of_num (NUMERAL 0)).
Definition term85 := (forall y0 : int, (int_le (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_le y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_lt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_lt y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_ge (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_ge y0 (int_of_num (NUMERAL 0)))) /\ ((forall y0 : int, (int_gt (int_sgn y0) (int_of_num (NUMERAL 0))) = (int_gt y0 (int_of_num (NUMERAL 0)))) /\ (forall y0 : int, ((int_sgn y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0))))))).
Definition term4 := (forall y0 : real, (real_le (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_le y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_lt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_lt y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_ge (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_ge y0 (real_of_num (NUMERAL 0)))) /\ ((forall y0 : real, (real_gt (real_sgn y0) (real_of_num (NUMERAL 0))) = (real_gt y0 (real_of_num (NUMERAL 0)))) /\ (forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))))))).
Definition term31 (x0 : int) := @eq Prop (real_gt (real_sgn (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term100 (x0 : int) := real_gt (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_sgn x0)).
Definition term64 (x0 : int) := @eq Prop (int_lt (int_sgn x0) (int_of_num (NUMERAL 0))).
Definition term98 := real_gt (real_of_num (NUMERAL 0)).
