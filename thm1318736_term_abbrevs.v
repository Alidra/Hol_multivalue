Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term48 (x0 : hreal -> Prop) (x1 : hreal) (x2 : nadd) := (x0 x1) -> hreal_le x1 (mk_hreal (nadd_eq x2)).
Definition term22 (x0 : hreal -> Prop) := exists y0 : hreal, x0 y0.
Definition term74 (x0 : nadd -> Prop) (x1 : nadd) (x2 : nadd) := (forall y0 : nadd, (x0 y0) -> nadd_le y0 x2) -> nadd_le x1 x2.
Definition term50 (x0 : hreal -> Prop) (x1 : nadd) := forall y0 : hreal, (x0 y0) -> hreal_le y0 (mk_hreal (nadd_eq x1)).
Definition term57 (x0 : hreal -> Prop) := fun y0 : hreal => forall y1 : hreal, (x0 y1) -> hreal_le y1 y0.
Definition term1 (x0 : hreal -> Prop) (x1 : nadd) := (fun y0 : nadd => x0 (mk_hreal (nadd_eq y0))) x1.
Definition term4 (x0 : nadd -> Prop) := (fun y0 : nadd -> Prop => ((exists y1 : nadd, y0 y1) /\ (exists y1 : nadd, forall y2 : nadd, (y0 y2) -> nadd_le y2 y1)) -> exists y1 : nadd, (forall y2 : nadd, (y0 y2) -> nadd_le y2 y1) /\ (forall y2 : nadd, (forall y3 : nadd, (y0 y3) -> nadd_le y3 y2) -> nadd_le y1 y2)) x0.
Definition term83 (x0 : hreal -> Prop) (x1 : nadd) (x2 : nadd) := (fun y0 : hreal => (forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) -> hreal_le (mk_hreal (nadd_eq x1)) y0) (mk_hreal (nadd_eq x2)).
Definition term18 := (forall y0 : hreal -> Prop, (exists y1 : nadd, y0 (mk_hreal (nadd_eq y1))) = (exists y1 : hreal, y0 y1)) /\ (forall y0 : hreal, (mk_hreal (nadd_eq (@ε nadd (dest_hreal y0)))) = y0).
Definition term91 (x0 : nadd -> Prop) (x1 : nadd) := (forall y0 : nadd, (x0 y0) -> nadd_le y0 x1) /\ (forall y0 : nadd, (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) -> nadd_le x1 y0).
Definition term51 (x0 : nadd -> Prop) := fun y0 : nadd => forall y1 : nadd, (x0 y1) -> nadd_le y1 y0.
Definition term98 (x0 : hreal -> Prop) := exists y0 : hreal, (fun y1 : hreal => (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) /\ (forall y2 : hreal, (forall y3 : hreal, (x0 y3) -> hreal_le y3 y2) -> hreal_le y1 y2)) y0.
Definition term104 (x0 : hreal -> Prop) (x1 : hreal) := (fun y0 : hreal => (forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le y0 y1)) x1.
Definition term11 := (forall y0 : nadd, nadd_eq y0 y0) /\ ((forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) = (nadd_eq y1 y0)) /\ ((forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) /\ ((forall y0 : hreal, (mk_hreal (dest_hreal y0)) = y0) /\ (forall y0 : nadd -> Prop, (exists y1 : nadd, y0 = (nadd_eq y1)) = ((dest_hreal (mk_hreal y0)) = y0))))).
Definition term90 (x0 : hreal -> Prop) (x1 : nadd) := forall y0 : hreal, (forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) -> hreal_le (mk_hreal (nadd_eq x1)) y0.
Definition term15 := ((forall y0 : nadd, nadd_eq y0 y0) /\ ((forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) = (nadd_eq y1 y0)) /\ ((forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) /\ ((forall y0 : hreal, (mk_hreal (dest_hreal y0)) = y0) /\ (forall y0 : nadd -> Prop, (exists y1 : nadd, y0 = (nadd_eq y1)) = ((dest_hreal (mk_hreal y0)) = y0)))))) -> (forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) = ((mk_hreal (nadd_eq y0)) = (mk_hreal (nadd_eq y1)))) /\ ((forall y0 : hreal -> Prop, (forall y1 : nadd, y0 (mk_hreal (nadd_eq y1))) = (forall y1 : hreal, y0 y1)) /\ ((forall y0 : hreal -> Prop, (exists y1 : nadd, y0 (mk_hreal (nadd_eq y1))) = (exists y1 : hreal, y0 y1)) /\ (forall y0 : hreal, (mk_hreal (nadd_eq (@ε nadd (dest_hreal y0)))) = y0))).
Definition term14 (x0 : type926) (x1 : type1554) (x2 : type1546) := ((forall y0 : nadd, x1 y0 y0) /\ ((forall y0 : nadd, forall y1 : nadd, (x1 y0 y1) = (x1 y1 y0)) /\ ((forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((x1 y0 y1) /\ (x1 y1 y2)) -> x1 y0 y2) /\ ((forall y0 : hreal, (x0 (x2 y0)) = y0) /\ (forall y0 : nadd -> Prop, (exists y1 : nadd, y0 = (x1 y1)) = ((x2 (x0 y0)) = y0)))))) -> (forall y0 : nadd, forall y1 : nadd, (x1 y0 y1) = ((x0 (x1 y0)) = (x0 (x1 y1)))) /\ ((forall y0 : hreal -> Prop, (forall y1 : nadd, y0 (x0 (x1 y1))) = (forall y1 : hreal, y0 y1)) /\ ((forall y0 : hreal -> Prop, (exists y1 : nadd, y0 (x0 (x1 y1))) = (exists y1 : hreal, y0 y1)) /\ (forall y0 : hreal, (x0 (x1 (@ε nadd (x2 y0)))) = y0))).
Definition term12 (a0 : Type') (a1 : Type') (x0 : type862 a0 a1) (x1 : type1402 a1) (x2 : type1413 a0 a1) := ((forall y0 : a1, x1 y0 y0) /\ ((forall y0 : a1, forall y1 : a1, (x1 y0 y1) = (x1 y1 y0)) /\ ((forall y0 : a1, forall y1 : a1, forall y2 : a1, ((x1 y0 y1) /\ (x1 y1 y2)) -> x1 y0 y2) /\ ((forall y0 : a0, (x0 (x2 y0)) = y0) /\ (forall y0 : a1 -> Prop, (exists y1 : a1, y0 = (x1 y1)) = ((x2 (x0 y0)) = y0)))))) -> (forall y0 : a1, forall y1 : a1, (x1 y0 y1) = ((x0 (x1 y0)) = (x0 (x1 y1)))) /\ ((forall y0 : a0 -> Prop, (forall y1 : a1, y0 (x0 (x1 y1))) = (forall y1 : a0, y0 y1)) /\ ((forall y0 : a0 -> Prop, (exists y1 : a1, y0 (x0 (x1 y1))) = (exists y1 : a0, y0 y1)) /\ (forall y0 : a0, (x0 (x1 (@ε a1 (x2 y0)))) = y0))).
Definition term81 (x0 : hreal -> Prop) (x1 : nadd) := forall y0 : hreal, (fun y1 : hreal => (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le (mk_hreal (nadd_eq x1)) y1) y0.
Definition term41 (x0 : hreal -> Prop) (x1 : nadd) := forall y0 : hreal, (fun y1 : hreal => (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq x1))) y0.
Definition term20 (x0 : hreal -> Prop) := (fun y0 : hreal -> Prop => (exists y1 : nadd, y0 (mk_hreal (nadd_eq y1))) = (exists y1 : hreal, y0 y1)) x0.
Definition term80 (x0 : hreal -> Prop) (x1 : nadd) := forall y0 : nadd, (fun y1 : hreal => (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le (mk_hreal (nadd_eq x1)) y1) (mk_hreal (nadd_eq y0)).
Definition term40 (x0 : hreal -> Prop) (x1 : nadd) := forall y0 : nadd, (fun y1 : hreal => (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq x1))) (mk_hreal (nadd_eq y0)).
Definition term108 (x0 : hreal -> Prop) := ((exists y0 : hreal, x0 y0) /\ (exists y0 : hreal, forall y1 : hreal, (x0 y1) -> hreal_le y1 y0)) -> exists y0 : hreal, (forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le y0 y1).
Definition term72 (x0 : nadd -> Prop) (x1 : nadd) := imp (forall y0 : nadd, (x0 y0) -> nadd_le y0 x1).
Definition term100 (x0 : hreal -> Prop) (x1 : nadd) := (fun y0 : hreal => (forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le y0 y1)) (mk_hreal (nadd_eq x1)).
Definition term94 (x0 : hreal -> Prop) := fun y0 : nadd => (forall y1 : hreal, (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq y0))) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le (mk_hreal (nadd_eq y0)) y1).
Definition term93 (x0 : nadd -> Prop) := fun y0 : nadd => (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) /\ (forall y1 : nadd, (forall y2 : nadd, (x0 y2) -> nadd_le y2 y1) -> nadd_le y0 y1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : type1402 a1) (x1 : type1413 a0 a1) (x2 : type862 a0 a1) := (forall y0 : a1, x0 y0 y0) /\ ((forall y0 : a1, forall y1 : a1, (x0 y0 y1) = (x0 y1 y0)) /\ ((forall y0 : a1, forall y1 : a1, forall y2 : a1, ((x0 y0 y1) /\ (x0 y1 y2)) -> x0 y0 y2) /\ ((forall y0 : a0, (x2 (x1 y0)) = y0) /\ (forall y0 : a1 -> Prop, (exists y1 : a1, y0 = (x0 y1)) = ((x1 (x2 y0)) = y0))))).
Definition term21 (x0 : hreal -> Prop) := exists y0 : nadd, x0 (mk_hreal (nadd_eq y0)).
Definition term78 (x0 : nadd -> Prop) (x1 : nadd) := forall y0 : nadd, (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) -> nadd_le x1 y0.
Definition term47 (x0 : hreal -> Prop) (x1 : nadd) (x2 : hreal) := (fun y0 : hreal => (x0 y0) -> hreal_le y0 (mk_hreal (nadd_eq x1))) x2.
Definition term88 (x0 : hreal -> Prop) (x1 : nadd) (x2 : hreal) := (forall y0 : hreal, (x0 y0) -> hreal_le y0 x2) -> hreal_le (mk_hreal (nadd_eq x1)) x2.
Definition term16 := (forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) = ((mk_hreal (nadd_eq y0)) = (mk_hreal (nadd_eq y1)))) /\ ((forall y0 : hreal -> Prop, (forall y1 : nadd, y0 (mk_hreal (nadd_eq y1))) = (forall y1 : hreal, y0 y1)) /\ ((forall y0 : hreal -> Prop, (exists y1 : nadd, y0 (mk_hreal (nadd_eq y1))) = (exists y1 : hreal, y0 y1)) /\ (forall y0 : hreal, (mk_hreal (nadd_eq (@ε nadd (dest_hreal y0)))) = y0))).
Definition term10 := (forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) = (nadd_eq y1 y0)) /\ ((forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) /\ ((forall y0 : hreal, (mk_hreal (dest_hreal y0)) = y0) /\ (forall y0 : nadd -> Prop, (exists y1 : nadd, y0 = (nadd_eq y1)) = ((dest_hreal (mk_hreal y0)) = y0)))).
Definition term5 (x0 : nadd -> Prop) := ((exists y0 : nadd, x0 y0) /\ (exists y0 : nadd, forall y1 : nadd, (x0 y1) -> nadd_le y1 y0)) -> exists y0 : nadd, (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) /\ (forall y1 : nadd, (forall y2 : nadd, (x0 y2) -> nadd_le y2 y1) -> nadd_le y0 y1).
Definition term24 (x0 : hreal -> Prop) := (fun y0 : hreal -> Prop => (forall y1 : nadd, y0 (mk_hreal (nadd_eq y1))) = (forall y1 : hreal, y0 y1)) x0.
Definition term99 (x0 : hreal -> Prop) := fun y0 : hreal => (forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le y0 y1).
Definition term110 (x0 : hreal -> Prop) := ((fun y0 : nadd => x0 (mk_hreal (nadd_eq y0))) = (fun y0 : nadd => x0 (mk_hreal (nadd_eq y0)))) -> ((exists y0 : hreal, x0 y0) /\ (exists y0 : hreal, forall y1 : hreal, (x0 y1) -> hreal_le y1 y0)) -> exists y0 : hreal, (forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le y0 y1).
Definition term9 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y1 y2)) -> nadd_eq y0 y2) /\ ((forall y0 : hreal, (mk_hreal (dest_hreal y0)) = y0) /\ (forall y0 : nadd -> Prop, (exists y1 : nadd, y0 = (nadd_eq y1)) = ((dest_hreal (mk_hreal y0)) = y0))).
Definition term28 (x0 : nadd -> Prop) := exists y0 : nadd, x0 y0.
Definition term56 (x0 : hreal -> Prop) := exists y0 : hreal, (fun y1 : hreal => forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) y0.
Definition term23 := forall y0 : hreal -> Prop, (forall y1 : nadd, y0 (mk_hreal (nadd_eq y1))) = (forall y1 : hreal, y0 y1).
Definition term64 (x0 : hreal -> Prop) := fun y0 : hreal => (fun y1 : hreal => forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) y0.
Definition term33 (x0 : nadd) (x1 : nadd) := hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term106 (x0 : hreal -> Prop) := fun y0 : hreal => (fun y1 : hreal => (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) /\ (forall y2 : hreal, (forall y3 : hreal, (x0 y3) -> hreal_le y3 y2) -> hreal_le y1 y2)) y0.
Definition term2 (x0 : hreal -> Prop) (x1 : nadd) := x0 (mk_hreal (nadd_eq x1)).
Definition term103 (x0 : hreal -> Prop) := @eq Prop (exists y0 : nadd, (forall y1 : hreal, (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq y0))) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le (mk_hreal (nadd_eq y0)) y1)).
Definition term17 := (forall y0 : hreal -> Prop, (forall y1 : nadd, y0 (mk_hreal (nadd_eq y1))) = (forall y1 : hreal, y0 y1)) /\ ((forall y0 : hreal -> Prop, (exists y1 : nadd, y0 (mk_hreal (nadd_eq y1))) = (exists y1 : hreal, y0 y1)) /\ (forall y0 : hreal, (mk_hreal (nadd_eq (@ε nadd (dest_hreal y0)))) = y0)).
Definition term0 (x0 : hreal -> Prop) := fun y0 : nadd => x0 (mk_hreal (nadd_eq y0)).
Definition term44 (x0 : hreal -> Prop) (x1 : nadd) := fun y0 : nadd => (fun y1 : hreal => (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq x1))) (mk_hreal (nadd_eq y0)).
Definition term29 (x0 : nadd -> Prop) := and (exists y0 : nadd, x0 y0).
Definition term73 (x0 : hreal -> Prop) (x1 : nadd) := imp (forall y0 : hreal, (x0 y0) -> hreal_le y0 (mk_hreal (nadd_eq x1))).
Definition term69 (x0 : hreal -> Prop) := imp ((exists y0 : hreal, x0 y0) /\ (exists y0 : hreal, forall y1 : hreal, (x0 y1) -> hreal_le y1 y0)).
Definition term68 (x0 : nadd -> Prop) := imp ((exists y0 : nadd, x0 y0) /\ (exists y0 : nadd, forall y1 : nadd, (x0 y1) -> nadd_le y1 y0)).
Definition term61 (x0 : hreal -> Prop) := @eq Prop (exists y0 : nadd, forall y1 : hreal, (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq y0))).
Definition term3 (x0 : nadd -> Prop) (x1 : nadd) := @eq Prop (x0 x1).
Definition term55 (x0 : hreal -> Prop) := exists y0 : nadd, (fun y1 : hreal => forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) (mk_hreal (nadd_eq y0)).
Definition term97 (x0 : hreal -> Prop) := exists y0 : nadd, (fun y1 : hreal => (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) /\ (forall y2 : hreal, (forall y3 : hreal, (x0 y3) -> hreal_le y3 y2) -> hreal_le y1 y2)) (mk_hreal (nadd_eq y0)).
Definition term107 (x0 : hreal -> Prop) := exists y0 : hreal, (forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le y0 y1).
Definition term54 (x0 : hreal -> Prop) := exists y0 : nadd, forall y1 : hreal, (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq y0)).
Definition term53 (x0 : nadd -> Prop) := exists y0 : nadd, forall y1 : nadd, (x0 y1) -> nadd_le y1 y0.
Definition term86 (x0 : hreal -> Prop) (x1 : nadd) := @eq Prop (forall y0 : nadd, (forall y1 : hreal, (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq y0))) -> hreal_le (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq y0))).
Definition term46 (x0 : hreal -> Prop) (x1 : nadd) := @eq Prop (forall y0 : nadd, (x0 (mk_hreal (nadd_eq y0))) -> hreal_le (mk_hreal (nadd_eq y0)) (mk_hreal (nadd_eq x1))).
Definition term27 (x0 : nadd -> Prop) := fun y0 : nadd => x0 y0.
Definition term31 (x0 : nadd -> Prop) (x1 : nadd) := imp (x0 x1).
Definition term82 (x0 : hreal -> Prop) (x1 : nadd) := fun y0 : hreal => (forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) -> hreal_le (mk_hreal (nadd_eq x1)) y0.
Definition term38 (x0 : nadd -> Prop) (x1 : nadd) := forall y0 : nadd, (x0 y0) -> nadd_le y0 x1.
Definition term70 (x0 : nadd -> Prop) (x1 : nadd) := and (forall y0 : nadd, (x0 y0) -> nadd_le y0 x1).
Definition term49 (x0 : hreal -> Prop) (x1 : nadd) := fun y0 : hreal => (fun y1 : hreal => (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq x1))) y0.
Definition term34 (x0 : nadd -> Prop) (x1 : nadd) (x2 : nadd) := (x0 x1) -> nadd_le x1 x2.
Definition term105 (x0 : hreal -> Prop) (x1 : hreal) := (forall y0 : hreal, (x0 y0) -> hreal_le y0 x1) /\ (forall y0 : hreal, (forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) -> hreal_le x1 y0).
Definition term92 (x0 : hreal -> Prop) (x1 : nadd) := (forall y0 : hreal, (x0 y0) -> hreal_le y0 (mk_hreal (nadd_eq x1))) /\ (forall y0 : hreal, (forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) -> hreal_le (mk_hreal (nadd_eq x1)) y0).
Definition term109 (x0 : nadd -> Prop) (x1 : hreal -> Prop) := (x0 = (fun y0 : nadd => x1 (mk_hreal (nadd_eq y0)))) -> ((exists y0 : hreal, x1 y0) /\ (exists y0 : hreal, forall y1 : hreal, (x1 y1) -> hreal_le y1 y0)) -> exists y0 : hreal, (forall y1 : hreal, (x1 y1) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x1 y2) -> hreal_le y2 y1) -> hreal_le y0 y1).
Definition term36 (x0 : nadd -> Prop) (x1 : nadd) := fun y0 : nadd => (x0 y0) -> nadd_le y0 x1.
Definition term111 := forall y0 : hreal -> Prop, ((exists y1 : hreal, y0 y1) /\ (exists y1 : hreal, forall y2 : hreal, (y0 y2) -> hreal_le y2 y1)) -> exists y1 : hreal, (forall y2 : hreal, (y0 y2) -> hreal_le y2 y1) /\ (forall y2 : hreal, (forall y3 : hreal, (y0 y3) -> hreal_le y3 y2) -> hreal_le y1 y2).
Definition term58 (x0 : hreal -> Prop) (x1 : nadd) := (fun y0 : hreal => forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) (mk_hreal (nadd_eq x1)).
Definition term62 (x0 : hreal -> Prop) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) x1.
Definition term42 (x0 : hreal -> Prop) (x1 : nadd) := fun y0 : hreal => (x0 y0) -> hreal_le y0 (mk_hreal (nadd_eq x1)).
Definition term66 (x0 : nadd -> Prop) := (exists y0 : nadd, x0 y0) /\ (exists y0 : nadd, forall y1 : nadd, (x0 y1) -> nadd_le y1 y0).
Definition term67 (x0 : hreal -> Prop) := (exists y0 : hreal, x0 y0) /\ (exists y0 : hreal, forall y1 : hreal, (x0 y1) -> hreal_le y1 y0).
Definition term96 (x0 : hreal -> Prop) := exists y0 : nadd, (forall y1 : hreal, (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq y0))) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le (mk_hreal (nadd_eq y0)) y1).
Definition term95 (x0 : nadd -> Prop) := exists y0 : nadd, (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) /\ (forall y1 : nadd, (forall y2 : nadd, (x0 y2) -> nadd_le y2 y1) -> nadd_le y0 y1).
Definition term8 := (forall y0 : hreal, (mk_hreal (dest_hreal y0)) = y0) /\ (forall y0 : nadd -> Prop, (exists y1 : nadd, y0 = (nadd_eq y1)) = ((dest_hreal (mk_hreal y0)) = y0)).
Definition term76 (x0 : nadd -> Prop) (x1 : nadd) := fun y0 : nadd => (forall y1 : nadd, (x0 y1) -> nadd_le y1 y0) -> nadd_le x1 y0.
Definition term65 (x0 : hreal -> Prop) := exists y0 : hreal, forall y1 : hreal, (x0 y1) -> hreal_le y1 y0.
Definition term19 := forall y0 : hreal -> Prop, (exists y1 : nadd, y0 (mk_hreal (nadd_eq y1))) = (exists y1 : hreal, y0 y1).
Definition term32 (x0 : hreal -> Prop) (x1 : nadd) := imp (x0 (mk_hreal (nadd_eq x1))).
Definition term52 (x0 : hreal -> Prop) := fun y0 : nadd => forall y1 : hreal, (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq y0)).
Definition term101 (x0 : hreal -> Prop) := fun y0 : nadd => (fun y1 : hreal => (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) /\ (forall y2 : hreal, (forall y3 : hreal, (x0 y3) -> hreal_le y3 y2) -> hreal_le y1 y2)) (mk_hreal (nadd_eq y0)).
Definition term89 (x0 : hreal -> Prop) (x1 : nadd) := fun y0 : hreal => (fun y1 : hreal => (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le (mk_hreal (nadd_eq x1)) y1) y0.
Definition term26 (x0 : hreal -> Prop) := forall y0 : hreal, x0 y0.
Definition term6 := forall y0 : hreal, (mk_hreal (dest_hreal y0)) = y0.
Definition term25 (x0 : hreal -> Prop) := forall y0 : nadd, x0 (mk_hreal (nadd_eq y0)).
Definition term30 (x0 : hreal -> Prop) := and (exists y0 : hreal, x0 y0).
Definition term87 (x0 : hreal -> Prop) (x1 : nadd) (x2 : hreal) := (fun y0 : hreal => (forall y1 : hreal, (x0 y1) -> hreal_le y1 y0) -> hreal_le (mk_hreal (nadd_eq x1)) y0) x2.
Definition term7 := forall y0 : nadd -> Prop, (exists y1 : nadd, y0 = (nadd_eq y1)) = ((dest_hreal (mk_hreal y0)) = y0).
Definition term77 (x0 : hreal -> Prop) (x1 : nadd) := fun y0 : nadd => (forall y1 : hreal, (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq y0))) -> hreal_le (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq y0)).
Definition term37 (x0 : hreal -> Prop) (x1 : nadd) := fun y0 : nadd => (x0 (mk_hreal (nadd_eq y0))) -> hreal_le (mk_hreal (nadd_eq y0)) (mk_hreal (nadd_eq x1)).
Definition term39 (x0 : hreal -> Prop) (x1 : nadd) := forall y0 : nadd, (x0 (mk_hreal (nadd_eq y0))) -> hreal_le (mk_hreal (nadd_eq y0)) (mk_hreal (nadd_eq x1)).
Definition term79 (x0 : hreal -> Prop) (x1 : nadd) := forall y0 : nadd, (forall y1 : hreal, (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq y0))) -> hreal_le (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq y0)).
Definition term63 (x0 : hreal -> Prop) (x1 : hreal) := forall y0 : hreal, (x0 y0) -> hreal_le y0 x1.
Definition term84 (x0 : hreal -> Prop) (x1 : nadd) := fun y0 : nadd => (fun y1 : hreal => (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le (mk_hreal (nadd_eq x1)) y1) (mk_hreal (nadd_eq y0)).
Definition term59 (x0 : hreal -> Prop) := fun y0 : nadd => (fun y1 : hreal => forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) (mk_hreal (nadd_eq y0)).
Definition term43 (x0 : hreal -> Prop) (x1 : nadd) (x2 : nadd) := (fun y0 : hreal => (x0 y0) -> hreal_le y0 (mk_hreal (nadd_eq x1))) (mk_hreal (nadd_eq x2)).
Definition term35 (x0 : hreal -> Prop) (x1 : nadd) (x2 : nadd) := (x0 (mk_hreal (nadd_eq x1))) -> hreal_le (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x2)).
Definition term75 (x0 : hreal -> Prop) (x1 : nadd) (x2 : nadd) := (forall y0 : hreal, (x0 y0) -> hreal_le y0 (mk_hreal (nadd_eq x2))) -> hreal_le (mk_hreal (nadd_eq x1)) (mk_hreal (nadd_eq x2)).
Definition term71 (x0 : hreal -> Prop) (x1 : nadd) := and (forall y0 : hreal, (x0 y0) -> hreal_le y0 (mk_hreal (nadd_eq x1))).
Definition term85 (x0 : hreal -> Prop) (x1 : nadd) := @eq Prop (forall y0 : nadd, (fun y1 : hreal => (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) -> hreal_le (mk_hreal (nadd_eq x1)) y1) (mk_hreal (nadd_eq y0))).
Definition term45 (x0 : hreal -> Prop) (x1 : nadd) := @eq Prop (forall y0 : nadd, (fun y1 : hreal => (x0 y1) -> hreal_le y1 (mk_hreal (nadd_eq x1))) (mk_hreal (nadd_eq y0))).
Definition term102 (x0 : hreal -> Prop) := @eq Prop (exists y0 : nadd, (fun y1 : hreal => (forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) /\ (forall y2 : hreal, (forall y3 : hreal, (x0 y3) -> hreal_le y3 y2) -> hreal_le y1 y2)) (mk_hreal (nadd_eq y0))).
Definition term60 (x0 : hreal -> Prop) := @eq Prop (exists y0 : nadd, (fun y1 : hreal => forall y2 : hreal, (x0 y2) -> hreal_le y2 y1) (mk_hreal (nadd_eq y0))).
