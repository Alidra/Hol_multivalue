Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd -> Prop => fun y1 : nadd -> Prop => (hreal_le (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (@ε Prop (fun y2 : Prop => exists y3 : nadd, exists y4 : nadd, ((nadd_le y3 y4) = y2) /\ ((y0 y3) /\ (y1 y4))))) (dest_hreal (mk_hreal (nadd_eq x1))).
Definition term36 (x0 : Prop) (x1 : nadd) (x2 : nadd) (x3 : nadd) := fun y0 : nadd => ((nadd_le x2 y0) = x0) /\ ((nadd_eq x1 x2) /\ (nadd_eq x3 y0)).
Definition term33 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (fun y0 : nadd => ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> (nadd_le x0 x1) = (nadd_le x2 y0)) x3.
Definition term22 (x0 : nadd) (x1 : nadd) := @ε Prop (fun y0 : Prop => exists y1 : nadd, exists y2 : nadd, ((nadd_le y1 y2) = y0) /\ ((nadd_eq x0 y1) /\ (nadd_eq x1 y2))).
Definition term11 (x0 : nadd) (x1 : nadd) := @ε Prop (fun y0 : Prop => exists y1 : nadd, exists y2 : nadd, ((nadd_le y1 y2) = y0) /\ ((dest_hreal (mk_hreal (nadd_eq x0)) y1) /\ (dest_hreal (mk_hreal (nadd_eq x1)) y2))).
Definition term5 (x0 : hreal) (x1 : hreal) := @ε Prop (fun y0 : Prop => exists y1 : nadd, exists y2 : nadd, ((nadd_le y1 y2) = y0) /\ ((dest_hreal x0 y1) /\ (dest_hreal x1 y2))).
Definition term15 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd -> Prop => fun y1 : nadd -> Prop => (hreal_le (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (@ε Prop (fun y2 : Prop => exists y3 : nadd, exists y4 : nadd, ((nadd_le y3 y4) = y2) /\ ((y0 y3) /\ (y1 y4))))) (nadd_eq x1).
Definition term30 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> (nadd_le x0 y0) = (nadd_le x1 y1).
Definition term28 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> (nadd_le x0 y1) = (nadd_le y0 y2).
Definition term34 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ (nadd_eq x1 x3)) -> (nadd_le x0 x1) = (nadd_le x2 x3).
Definition term51 (a0 : Type') (x0 : a0) := @ε a0 (fun y0 : a0 => x0 = y0).
Definition term26 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x0 x1) /\ (nadd_eq x2 x3).
Definition term46 (x0 : Prop) (x1 : nadd) (x2 : nadd) := ((exists y0 : nadd, exists y1 : nadd, ((nadd_le y0 y1) = x0) /\ ((nadd_eq x1 y0) /\ (nadd_eq x2 y1))) -> (nadd_le x1 x2) = x0) /\ (((nadd_le x1 x2) = x0) -> exists y0 : nadd, exists y1 : nadd, ((nadd_le y0 y1) = x0) /\ ((nadd_eq x1 y0) /\ (nadd_eq x2 y1))).
Definition term17 (x0 : nadd) (x1 : nadd) := @eq ((nadd -> Prop) -> Prop) ((fun y0 : nadd -> Prop => fun y1 : nadd -> Prop => (hreal_le (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (@ε Prop (fun y2 : Prop => exists y3 : nadd, exists y4 : nadd, ((nadd_le y3 y4) = y2) /\ ((y0 y3) /\ (y1 y4))))) (dest_hreal (mk_hreal (nadd_eq x1)))).
Definition term48 (x0 : nadd) (x1 : nadd) := fun y0 : Prop => (nadd_le x0 x1) = y0.
Definition term24 (x0 : nadd) (x1 : nadd) := @eq Prop ((hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (@ε Prop (fun y0 : Prop => exists y1 : nadd, exists y2 : nadd, ((nadd_le y1 y2) = y0) /\ ((dest_hreal (mk_hreal (nadd_eq x0)) y1) /\ (dest_hreal (mk_hreal (nadd_eq x1)) y2))))).
Definition term1 (x0 : hreal) := (fun y0 : hreal => fun y1 : hreal => @ε Prop (fun y2 : Prop => exists y3 : nadd, exists y4 : nadd, ((nadd_le y3 y4) = y2) /\ ((dest_hreal y0 y3) /\ (dest_hreal y1 y4)))) x0.
Definition term29 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> (nadd_le x0 y1) = (nadd_le y0 y2)) x1.
Definition term40 (x0 : nadd) (x1 : nadd) := (nadd_eq x0 x0) /\ (nadd_eq x1 x1).
Definition term25 (x0 : Prop) (x1 : nadd) (x2 : nadd) (x3 : nadd) (x4 : nadd) := ((nadd_le x2 x4) = x0) /\ ((nadd_eq x1 x2) /\ (nadd_eq x3 x4)).
Definition term0 := fun y0 : hreal => fun y1 : hreal => @ε Prop (fun y2 : Prop => exists y3 : nadd, exists y4 : nadd, ((nadd_le y3 y4) = y2) /\ ((dest_hreal y0 y3) /\ (dest_hreal y1 y4))).
Definition term9 (x0 : nadd) := fun y0 : nadd => (nadd_eq x0) = (nadd_eq y0).
Definition term41 (x0 : Prop) (x1 : nadd) (x2 : nadd) := ((nadd_le x1 x2) = x0) /\ ((nadd_eq x1 x1) /\ (nadd_eq x2 x2)).
Definition term23 (x0 : nadd) (x1 : nadd) := @eq Prop ((fun y0 : nadd -> Prop => (hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (@ε Prop (fun y1 : Prop => exists y2 : nadd, exists y3 : nadd, ((nadd_le y2 y3) = y1) /\ ((dest_hreal (mk_hreal (nadd_eq x0)) y2) /\ (y0 y3))))) (dest_hreal (mk_hreal (nadd_eq x1)))).
Definition term10 (x0 : nadd) (x1 : nadd) := hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term39 (x0 : nadd) := (fun y0 : nadd => nadd_eq y0 y0) x0.
Definition term27 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) x0.
Definition term4 (x0 : hreal) (x1 : hreal) := (fun y0 : hreal => @ε Prop (fun y1 : Prop => exists y2 : nadd, exists y3 : nadd, ((nadd_le y2 y3) = y1) /\ ((dest_hreal x0 y2) /\ (dest_hreal y0 y3)))) x1.
Definition term3 (x0 : hreal) := @eq (hreal -> Prop) (hreal_le x0).
Definition term21 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd -> Prop => (hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (@ε Prop (fun y1 : Prop => exists y2 : nadd, exists y3 : nadd, ((nadd_le y2 y3) = y1) /\ ((nadd_eq x0 y2) /\ (y0 y3))))) (nadd_eq x1).
Definition term12 (x0 : nadd) := mk_hreal (nadd_eq x0).
Definition term31 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> (nadd_le x0 y0) = (nadd_le x1 y1)) x2.
Definition term47 (x0 : nadd) (x1 : nadd) := fun y0 : Prop => exists y1 : nadd, exists y2 : nadd, ((nadd_le y1 y2) = y0) /\ ((nadd_eq x0 y1) /\ (nadd_eq x1 y2)).
Definition term19 (x0 : nadd) (x1 : nadd) := @eq ((nadd -> Prop) -> Prop) (fun y0 : nadd -> Prop => (hreal_le (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (@ε Prop (fun y1 : Prop => exists y2 : nadd, exists y3 : nadd, ((nadd_le y2 y3) = y1) /\ ((dest_hreal (mk_hreal (nadd_eq x1)) y2) /\ (y0 y3))))).
Definition term35 (x0 : Prop) (x1 : nadd) (x2 : nadd) (x3 : nadd) := exists y0 : nadd, ((nadd_le x2 y0) = x0) /\ ((nadd_eq x1 x2) /\ (nadd_eq x3 y0)).
Definition term7 (x0 : nadd) := exists y0 : nadd, (nadd_eq x0) = (nadd_eq y0).
Definition term38 (x0 : Prop) (x1 : nadd) (x2 : nadd) := fun y0 : nadd => exists y1 : nadd, ((nadd_le y0 y1) = x0) /\ ((nadd_eq x1 y0) /\ (nadd_eq x2 y1)).
Definition term8 (x0 : nadd) := dest_hreal (mk_hreal (nadd_eq x0)).
Definition term37 (x0 : Prop) (x1 : nadd) (x2 : nadd) := exists y0 : nadd, exists y1 : nadd, ((nadd_le y0 y1) = x0) /\ ((nadd_eq x1 y0) /\ (nadd_eq x2 y1)).
Definition term18 (x0 : nadd) (x1 : nadd) := fun y0 : nadd -> Prop => (hreal_le (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (@ε Prop (fun y1 : Prop => exists y2 : nadd, exists y3 : nadd, ((nadd_le y2 y3) = y1) /\ ((dest_hreal (mk_hreal (nadd_eq x1)) y2) /\ (y0 y3)))).
Definition term16 (x0 : nadd) (x1 : nadd) := fun y0 : nadd -> Prop => (hreal_le (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x0))) = (@ε Prop (fun y1 : Prop => exists y2 : nadd, exists y3 : nadd, ((nadd_le y2 y3) = y1) /\ ((nadd_eq x1 y2) /\ (y0 y3)))).
Definition term6 (x0 : hreal) (x1 : hreal) := @eq Prop (hreal_le x0 x1).
Definition term49 (x0 : nadd) (x1 : nadd) := @ε Prop (fun y0 : Prop => (nadd_le x0 x1) = y0).
Definition term32 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> (nadd_le x0 x1) = (nadd_le x2 y0).
Definition term20 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd -> Prop => (hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (@ε Prop (fun y1 : Prop => exists y2 : nadd, exists y3 : nadd, ((nadd_le y2 y3) = y1) /\ ((dest_hreal (mk_hreal (nadd_eq x0)) y2) /\ (y0 y3))))) (dest_hreal (mk_hreal (nadd_eq x1))).
Definition term2 (x0 : hreal) := fun y0 : hreal => @ε Prop (fun y1 : Prop => exists y2 : nadd, exists y3 : nadd, ((nadd_le y2 y3) = y1) /\ ((dest_hreal x0 y2) /\ (dest_hreal y0 y3))).
Definition term13 (x0 : nadd) (x1 : nadd) := fun y0 : nadd -> Prop => fun y1 : nadd -> Prop => (hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))) = (@ε Prop (fun y2 : Prop => exists y3 : nadd, exists y4 : nadd, ((nadd_le y3 y4) = y2) /\ ((y0 y3) /\ (y1 y4)))).
Definition term52 (x0 : Prop) := @ε Prop (fun y0 : Prop => x0 = y0).
Definition term45 (x0 : nadd) (x1 : nadd) (x2 : Prop) := (exists y0 : nadd, exists y1 : nadd, ((nadd_le y0 y1) = x2) /\ ((nadd_eq x0 y0) /\ (nadd_eq x1 y1))) -> (nadd_le x0 x1) = x2.
Definition term43 (x0 : Prop) (x1 : nadd) (x2 : nadd) := (((nadd_le x1 x2) = x0) /\ ((nadd_eq x1 x1) /\ (nadd_eq x2 x2))) -> exists y0 : nadd, exists y1 : nadd, ((nadd_le y0 y1) = x0) /\ ((nadd_eq x1 y0) /\ (nadd_eq x2 y1)).
Definition term42 (x0 : nadd) (x1 : nadd) (x2 : Prop) (x3 : nadd) (x4 : nadd) := (((nadd_le x0 x1) = x2) /\ ((nadd_eq x3 x0) /\ (nadd_eq x4 x1))) -> exists y0 : nadd, exists y1 : nadd, ((nadd_le y0 y1) = x2) /\ ((nadd_eq x3 y0) /\ (nadd_eq x4 y1)).
Definition term53 (x0 : nadd) (x1 : nadd) := @eq Prop (hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1))).
Definition term50 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (@ε a0 (fun y1 : a0 => y0 = y1)) = y0) x0.
Definition term44 (x0 : Prop) (x1 : nadd) (x2 : nadd) := ((nadd_le x1 x2) = x0) -> exists y0 : nadd, exists y1 : nadd, ((nadd_le y0 y1) = x0) /\ ((nadd_eq x1 y0) /\ (nadd_eq x2 y1)).
