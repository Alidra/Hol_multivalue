Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term62 (a0 : Type') (a1 : Type') (a2 : Type') := fun y0 : type524 a0 a1 a2 => (exists y1 : a0 -> a1, exists y2 : a0 -> a2, y0 y1 y2) = (exists y1 : type1430 a0 a1 a2, y0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y1) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y1)).
Definition term45 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) (x2 : a0) := @pair a1 a2 (x0 x2) (x1 x2).
Definition term51 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @fst a0 a1 (@pair a0 a1 x0 x1).
Definition term38 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) := @o a0 (prod a1 a2) a1 (@fst a1 a2) (fun y0 : a0 => @pair a1 a2 (x0 y0) (x1 y0)).
Definition term56 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) (x2 : a0) := @snd a1 a2 ((fun y0 : a0 => @pair a1 a2 (x0 y0) (x1 y0)) x2).
Definition term11 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) (x1 : a0 -> a1) := exists y0 : a0 -> a2, x0 x1 y0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term66 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term57 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) (x2 : a0) := @snd a1 a2 (@pair a1 a2 (x0 x2) (x1 x2)).
Definition term32 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) (x1 : a0 -> a1) := exists y0 : a0 -> a2, (fun y1 : type1430 a0 a1 a2 => x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y1) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y1)) (fun y1 : a0 => @pair a1 a2 (x1 y1) (y0 y1)).
Definition term30 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) (x1 : a0 -> a1) := fun y0 : a0 -> a2 => (fun y1 : type1430 a0 a1 a2 => x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y1) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y1)) (fun y1 : a0 => @pair a1 a2 (x1 y1) (y0 y1)).
Definition term21 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := fun y0 : type1430 a0 a1 a2 => x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y0) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y0).
Definition term35 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := fun y0 : a0 -> a1 => exists y1 : a0 -> a2, x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2))) (@o a0 (prod a1 a2) a2 (@snd a1 a2) (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2))).
Definition term25 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := exists y0 : type1430 a0 a1 a2, x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y0) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y0).
Definition term10 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) (x1 : a0 -> a1) := fun y0 : a0 -> a2 => x0 x1 y0.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0) x0.
Definition term15 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := exists y0 : a0 -> a1, exists y1 : a0 -> a2, x0 y0 y1.
Definition term40 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) := fun y0 : a0 => @pair a1 a2 (x0 y0) (x1 y0).
Definition term12 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) (x1 : a0 -> a1) := ex (x0 x1).
Definition term50 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) (x2 : a0) := @fst a1 a2 (@pair a1 a2 (x0 x2) (x1 x2)).
Definition term27 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := @eq Prop (exists y0 : type1430 a0 a1 a2, x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y0) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y0)).
Definition term39 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) := fun y0 : a0 => @fst a1 a2 ((fun y1 : a0 => @pair a1 a2 (x0 y1) (x1 y1)) y0).
Definition term22 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) (x1 : type1430 a0 a1 a2) := (fun y0 : type1430 a0 a1 a2 => x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y0) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y0)) x1.
Definition term61 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := @eq Prop (((exists y0 : a0 -> a1, ex (x0 y0)) = (exists y0 : a0 -> a1, ex (x0 y0))) = True).
Definition term9 (a0 : Type') (a1 : Type') (x0 : type572 a0 a1) := fun y0 : a0 -> a1 => x0 y0.
Definition term44 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) (x2 : a0) := (fun y0 : a0 => @pair a1 a2 (x0 y0) (x1 y0)) x2.
Definition term33 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) (x1 : a0 -> a1) := exists y0 : a0 -> a2, x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) (fun y1 : a0 => @pair a1 a2 (x1 y1) (y0 y1))) (@o a0 (prod a1 a2) a2 (@snd a1 a2) (fun y1 : a0 => @pair a1 a2 (x1 y1) (y0 y1))).
Definition term47 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) (x2 : a0) := @eq (prod a1 a2) ((fun y0 : a0 => (fun y1 : a0 => @pair a1 a2 (x0 y1) (x1 y1)) y0) x2).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term65 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type524 a0 a1 a2, True.
Definition term60 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := @eq Prop ((fun y0 : Prop => y0 = True) ((exists y0 : a0 -> a1, ex (x0 y0)) = (exists y0 : a0 -> a1, ex (x0 y0)))).
Definition term42 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1430 a0 a1 a2) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term46 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) := fun y0 : a0 => (fun y1 : a0 => @pair a1 a2 (x0 y1) (x1 y1)) y0.
Definition term6 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) := (fun y0 : type478 a0 a1 a2 => (exists y1 : type1430 a0 a1 a2, y0 y1) = (exists y1 : a0 -> a1, exists y2 : a0 -> a2, y0 (fun y3 : a0 => @pair a1 a2 (y1 y3) (y2 y3)))) x0.
Definition term16 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := exists y0 : a0 -> a1, ex (x0 y0).
Definition term63 (a0 : Type') (a1 : Type') (a2 : Type') := fun y0 : type524 a0 a1 a2 => True.
Definition term8 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) := exists y0 : a0 -> a1, exists y1 : a0 -> a2, x0 (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2)).
Definition term26 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := @eq Prop (exists y0 : type1430 a0 a1 a2, (fun y1 : type1430 a0 a1 a2 => x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y1) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y1)) y0).
Definition term13 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := fun y0 : a0 -> a1 => exists y1 : a0 -> a2, x0 y0 y1.
Definition term34 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := fun y0 : a0 -> a1 => exists y1 : a0 -> a2, (fun y2 : type1430 a0 a1 a2 => x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y2) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y2)) (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2)).
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) := (fun y0 : a1 -> a2 => forall y1 : a0 -> a1, (@o a0 a1 a2 y0 y1) = (fun y2 : a0 => y0 (y1 y2))) x0.
Definition term31 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) (x1 : a0 -> a1) := fun y0 : a0 -> a2 => x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) (fun y1 : a0 => @pair a1 a2 (x1 y1) (y0 y1))) (@o a0 (prod a1 a2) a2 (@snd a1 a2) (fun y1 : a0 => @pair a1 a2 (x1 y1) (y0 y1))).
Definition term23 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) (x1 : type1430 a0 a1 a2) := x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) x1) (@o a0 (prod a1 a2) a2 (@snd a1 a2) x1).
Definition term7 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type478 a0 a1 a2) := exists y0 : type1430 a0 a1 a2, x0 y0.
Definition term18 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := @eq Prop (exists y0 : a0 -> a1, ex (x0 y0)).
Definition term49 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) (x2 : a0) := @fst a1 a2 ((fun y0 : a0 => @pair a1 a2 (x0 y0) (x1 y0)) x2).
Definition term43 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) (x2 : a0) := (fun y0 : a0 => (fun y1 : a0 => @pair a1 a2 (x0 y1) (x1 y1)) y0) x2.
Definition term67 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : Prop) := forall y0 : type524 a0 a1 a2, x0.
Definition term64 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type524 a0 a1 a2, (exists y1 : a0 -> a1, exists y2 : a0 -> a2, y0 y1 y2) = (exists y1 : type1430 a0 a1 a2, y0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y1) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y1)).
Definition term17 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := @eq Prop (exists y0 : a0 -> a1, exists y1 : a0 -> a2, x0 y0 y1).
Definition term36 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := exists y0 : a0 -> a1, exists y1 : a0 -> a2, x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2))) (@o a0 (prod a1 a2) a2 (@snd a1 a2) (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2))).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) := forall y0 : a0 -> a1, (@o a0 a1 a2 x0 y0) = (fun y1 : a0 => x0 (y0 y1)).
Definition term24 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := fun y0 : type1430 a0 a1 a2 => (fun y1 : type1430 a0 a1 a2 => x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y1) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y1)) y0.
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (@o a0 a1 a2 x0 y0) = (fun y1 : a0 => x0 (y0 y1))) x1.
Definition term58 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @snd a0 a1 (@pair a0 a1 x0 x1).
Definition term48 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) (x2 : a0) := @eq (prod a1 a2) ((fun y0 : a0 => @pair a1 a2 (x0 y0) (x1 y0)) x2).
Definition term28 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) (x1 : a0 -> a1) (x2 : a0 -> a2) := (fun y0 : type1430 a0 a1 a2 => x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y0) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y0)) (fun y0 : a0 => @pair a1 a2 (x1 y0) (x2 y0)).
Definition term59 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := (fun y0 : Prop => y0 = True) ((exists y0 : a0 -> a1, ex (x0 y0)) = (exists y0 : a0 -> a1, ex (x0 y0))).
Definition term20 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := exists y0 : a0 -> a1, exists y1 : a0 -> a2, (fun y2 : type1430 a0 a1 a2 => x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y2) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y2)) (fun y2 : a0 => @pair a1 a2 (y0 y2) (y1 y2)).
Definition term29 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) (x1 : a0 -> a1) (x2 : a0 -> a2) := x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) (fun y0 : a0 => @pair a1 a2 (x1 y0) (x2 y0))) (@o a0 (prod a1 a2) a2 (@snd a1 a2) (fun y0 : a0 => @pair a1 a2 (x1 y0) (x2 y0))).
Definition term14 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := fun y0 : a0 -> a1 => ex (x0 y0).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := fun y0 : a0 => x0 (x1 y0).
Definition term54 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) := @o a0 (prod a1 a2) a2 (@snd a1 a2) (fun y0 : a0 => @pair a1 a2 (x0 y0) (x1 y0)).
Definition term55 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a0 -> a1) (x1 : a0 -> a2) := fun y0 : a0 => @snd a1 a2 ((fun y1 : a0 => @pair a1 a2 (x0 y1) (x1 y1)) y0).
Definition term19 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) := exists y0 : type1430 a0 a1 a2, (fun y1 : type1430 a0 a1 a2 => x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) y1) (@o a0 (prod a1 a2) a2 (@snd a1 a2) y1)) y0.
Definition term52 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type524 a0 a1 a2) (x1 : a0 -> a1) (x2 : a0 -> a2) := x0 (@o a0 (prod a1 a2) a1 (@fst a1 a2) (fun y0 : a0 => @pair a1 a2 (x1 y0) (x2 y0))).
Definition term53 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1208 a1 a2) (x1 : type1430 a0 a1 a2) := fun y0 : a0 => x0 (x1 y0).
Definition term37 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1207 a1 a2) (x1 : type1430 a0 a1 a2) := fun y0 : a0 => x0 (x1 y0).
