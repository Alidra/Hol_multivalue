Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (a0 : Type') (a1 : Type') (x0 : type1329 a0) (x1 : type39 a0) (x2 : type1350 a0 a1) (x3 : type1328 a0 a1) (x4 : type6 a0) := (x1 = (fun y0 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)))) -> (x0 = (fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = (x1 y3)) -> y1 y2) -> y1 y0)) -> (x2 (@_103802 a0 x4)) = (x3 (@CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) x4 (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)))).
Definition term1 (a0 : Type') := fun y0 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)).
Definition term38 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) := fun y0 : type6 a0 => fun y1 : type1610 a0 => fun y2 : nat -> a1 => x0 y0.
Definition term6 (a0 : Type') (x0 : type1329 a0) (x1 : type39 a0) (x2 : type6 a0) := (fun y0 : type6 a0 => x0 (x1 y0)) x2.
Definition term57 (a0 : Type') (a1 : Type') (x0 : type1328 a0 a1) (x1 : type41 a0 a1) := (forall y0 : type1350 a0 a1, (y0 = (fun y1 : tybit1 a0 => x0 (@_dest_tybit1 a0 y1))) -> (fun y1 : type1350 a0 a1 => forall y2 : type6 a0, (y1 (@_103802 a0 y2)) = (x1 y2)) y0) -> exists y0 : type1350 a0 a1, forall y1 : type6 a0, (y0 (@_103802 a0 y1)) = (x1 y1).
Definition term37 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) := @FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y0 : type6 a0 => fun y1 : type1610 a0 => fun y2 : nat -> a1 => x0 y0) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) (NUMERAL 0).
Definition term61 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) := fun y0 : type1328 a0 a1 => forall y1 : nat, forall y2 : type6 a0, forall y3 : type1610 a0, (y0 (@CONSTR (finite_sum (finite_sum a0 a0) unit) y1 y2 y3)) = (@FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y4 : type6 a0 => fun y5 : type1610 a0 => fun y6 : nat -> a1 => x0 y4) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) y1 y2 y3 (fun y4 : nat => y0 (y3 y4))).
Definition term59 (a0 : Type') (a1 : Type') (x0 : type1328 a0 a1) (x1 : type41 a0 a1) := forall y0 : type1350 a0 a1, (y0 = (fun y1 : tybit1 a0 => x0 (@_dest_tybit1 a0 y1))) -> (fun y1 : type1350 a0 a1 => forall y2 : type6 a0, (y1 (@_103802 a0 y2)) = (x1 y2)) y0.
Definition term23 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) := @FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y0 : type6 a0 => fun y1 : type1610 a0 => fun y2 : nat -> a1 => x0 y0) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)).
Definition term32 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : nat) (x2 : type6 a0) (x3 : type1328 a0 a1) (x4 : type1610 a0) := @FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y0 : type6 a0 => fun y1 : type1610 a0 => fun y2 : nat -> a1 => x0 y0) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) x1 x2 x4 (fun y0 : nat => x3 (x4 y0)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : type1329 a0) (x1 : type1350 a0 a1) (x2 : type1328 a0 a1) (x3 : type6 a0) := ((fun y0 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) = (fun y0 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)))) -> (x0 = (fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = ((fun y4 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y3)) -> y1 y2) -> y1 y0)) -> (x1 (@_103802 a0 x3)) = (x2 (@CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) x3 (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)))).
Definition term13 (a0 : Type') (x0 : type39 a0) (x1 : type6 a0) := @eq (recspace (finite_sum (finite_sum a0 a0) unit)) (x0 x1).
Definition term45 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type6 a0) := fun y0 : type1610 a0 => fun y1 : nat -> a1 => x0 x1.
Definition term41 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type6 a0) := @FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y0 : type6 a0 => fun y1 : type1610 a0 => fun y2 : nat -> a1 => x0 y0) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) (NUMERAL 0) x1 (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)).
Definition term35 (a0 : Type') (x0 : a0) (x1 : nat -> a0) := @FCONS a0 x0 x1 (NUMERAL 0).
Definition term60 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) := exists y0 : type1350 a0 a1, forall y1 : type6 a0, (y0 (@_103802 a0 y1)) = (x0 y1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1328 a0 a1) (x1 : type39 a0) (x2 : type6 a0) := (fun y0 : tybit1 a0 => x0 (@_dest_tybit1 a0 y0)) (@_mk_tybit1 a0 (x1 x2)).
Definition term62 (a0 : Type') (a1 : Type') := forall y0 : type41 a0 a1, exists y1 : type1350 a0 a1, forall y2 : type6 a0, (y1 (@_103802 a0 y2)) = (y0 y2).
Definition term21 (a0 : Type') (a1 : Type') := forall y0 : type1561 a0 a1, exists y1 : type1328 a0 a1, forall y2 : nat, forall y3 : type6 a0, forall y4 : type1610 a0, (y1 (@CONSTR (finite_sum (finite_sum a0 a0) unit) y2 y3 y4)) = (y0 y2 y3 y4 (fun y5 : nat => y1 (y4 y5))).
Definition term50 (a0 : Type') (a1 : Type') (x0 : type1350 a0 a1) (x1 : type41 a0 a1) := forall y0 : type6 a0, (x0 (@_103802 a0 y0)) = (x1 y0).
Definition term51 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type1350 a0 a1) := (fun y0 : type1350 a0 a1 => forall y1 : type6 a0, (y0 (@_103802 a0 y1)) = (x0 y1)) x1.
Definition term9 (a0 : Type') (x0 : type39 a0) (x1 : type6 a0) := @_dest_tybit1 a0 (@_mk_tybit1 a0 (x0 x1)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1328 a0 a1) (x1 : type6 a0) := x0 (@CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) x1 (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))).
Definition term34 (a0 : Type') := fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1328 a0 a1) := fun y0 : tybit1 a0 => x0 (@_dest_tybit1 a0 y0).
Definition term49 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type6 a0) (x2 : type1328 a0 a1) := (fun y0 : nat -> a1 => x0 x1) (fun y0 : nat => x2 ((fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)) y0)).
Definition term55 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) := forall y0 : type1350 a0 a1, (forall y1 : type1350 a0 a1, (y1 = y0) -> (fun y2 : type1350 a0 a1 => forall y3 : type6 a0, (y2 (@_103802 a0 y3)) = (x0 y3)) y1) -> exists y1 : type1350 a0 a1, forall y2 : type6 a0, (y1 (@_103802 a0 y2)) = (x0 y2).
Definition term56 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type1328 a0 a1) := (fun y0 : type1350 a0 a1 => (forall y1 : type1350 a0 a1, (y1 = y0) -> (fun y2 : type1350 a0 a1 => forall y3 : type6 a0, (y2 (@_103802 a0 y3)) = (x0 y3)) y1) -> exists y1 : type1350 a0 a1, forall y2 : type6 a0, (y1 (@_103802 a0 y2)) = (x0 y2)) (fun y0 : tybit1 a0 => x1 (@_dest_tybit1 a0 y0)).
Definition term29 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : nat) (x2 : type6 a0) (x3 : type1328 a0 a1) := forall y0 : type1610 a0, (x3 (@CONSTR (finite_sum (finite_sum a0 a0) unit) x1 x2 y0)) = (@FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y1 : type6 a0 => fun y2 : type1610 a0 => fun y3 : nat -> a1 => x0 y1) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) x1 x2 y0 (fun y1 : nat => x3 (y0 y1))).
Definition term28 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : nat) (x2 : type1328 a0 a1) (x3 : type6 a0) := (fun y0 : type6 a0 => forall y1 : type1610 a0, (x2 (@CONSTR (finite_sum (finite_sum a0 a0) unit) x1 y0 y1)) = (@FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y2 : type6 a0 => fun y3 : type1610 a0 => fun y4 : nat -> a1 => x0 y2) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) x1 y0 y1 (fun y2 : nat => x2 (y1 y2)))) x3.
Definition term25 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type1328 a0 a1) := forall y0 : nat, forall y1 : type6 a0, forall y2 : type1610 a0, (x1 (@CONSTR (finite_sum (finite_sum a0 a0) unit) y0 y1 y2)) = (@FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y3 : type6 a0 => fun y4 : type1610 a0 => fun y5 : nat -> a1 => x0 y3) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) y0 y1 y2 (fun y3 : nat => x1 (y2 y3))).
Definition term58 (a0 : Type') (a1 : Type') (x0 : type1328 a0 a1) (x1 : type41 a0 a1) (x2 : type1350 a0 a1) := (x2 = (fun y0 : tybit1 a0 => x0 (@_dest_tybit1 a0 y0))) -> (fun y0 : type1350 a0 a1 => forall y1 : type6 a0, (y0 (@_103802 a0 y1)) = (x1 y1)) x2.
Definition term19 (a0 : Type') := fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = ((fun y4 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y3)) -> y1 y2) -> y1 y0.
Definition term5 (a0 : Type') (x0 : type39 a0) := fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = (x0 y3)) -> y1 y2) -> y1 y0.
Definition term26 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type1328 a0 a1) (x2 : nat) := (fun y0 : nat => forall y1 : type6 a0, forall y2 : type1610 a0, (x1 (@CONSTR (finite_sum (finite_sum a0 a0) unit) y0 y1 y2)) = (@FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y3 : type6 a0 => fun y4 : type1610 a0 => fun y5 : nat -> a1 => x0 y3) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) y0 y1 y2 (fun y3 : nat => x1 (y2 y3)))) x2.
Definition term12 (a0 : Type') (x0 : type6 a0) := @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) x0 (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)).
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1329 a0) (x1 : type1350 a0 a1) (x2 : type1328 a0 a1) (x3 : type6 a0) := (x0 = (fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = ((fun y4 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y3)) -> y1 y2) -> y1 y0)) -> (x1 (@_103802 a0 x3)) = (x2 (@CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) x3 (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)))).
Definition term36 (a0 : Type') (a1 : Type') (x0 : type38 a0 a1) (x1 : type1561 a0 a1) := @FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) x0 x1 (NUMERAL 0).
Definition term46 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type6 a0) := (fun y0 : type1610 a0 => fun y1 : nat -> a1 => x0 x1) (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)).
Definition term48 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type6 a0) := fun y0 : nat -> a1 => x0 x1.
Definition term22 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) := (fun y0 : type1561 a0 a1 => exists y1 : type1328 a0 a1, forall y2 : nat, forall y3 : type6 a0, forall y4 : type1610 a0, (y1 (@CONSTR (finite_sum (finite_sum a0 a0) unit) y2 y3 y4)) = (y0 y2 y3 y4 (fun y5 : nat => y1 (y4 y5)))) (@FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y0 : type6 a0 => fun y1 : type1610 a0 => fun y2 : nat -> a1 => x0 y0) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1))).
Definition term31 (a0 : Type') (a1 : Type') (x0 : type1328 a0 a1) (x1 : nat) (x2 : type6 a0) (x3 : type1610 a0) := x0 (@CONSTR (finite_sum (finite_sum a0 a0) unit) x1 x2 x3).
Definition term15 (a0 : Type') (a1 : Type') (x0 : type1329 a0) (x1 : type39 a0) (x2 : type1350 a0 a1) (x3 : type1328 a0 a1) (x4 : type6 a0) := (x0 = (fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = (x1 y3)) -> y1 y2) -> y1 y0)) -> (x2 (@_103802 a0 x4)) = (x3 (@CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) x4 (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)))).
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1350 a0 a1) (x1 : type1328 a0 a1) (x2 : type6 a0) := ((fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = ((fun y4 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y3)) -> y1 y2) -> y1 y0) = (fun y0 : type1675 a0 => forall y1 : type1329 a0, (forall y2 : type1675 a0, (exists y3 : type6 a0, y2 = ((fun y4 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y4 (fun y5 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) y3)) -> y1 y2) -> y1 y0)) -> (x0 (@_103802 a0 x2)) = (x1 (@CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) x2 (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)))).
Definition term52 (a0 : Type') (a1 : Type') := forall y0 : type386 a0 a1, forall y1 : type1350 a0 a1, (forall y2 : type1350 a0 a1, (y2 = y1) -> y0 y2) -> ex y0.
Definition term54 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) := fun y0 : type1350 a0 a1 => forall y1 : type6 a0, (y0 (@_103802 a0 y1)) = (x0 y1).
Definition term53 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) := (fun y0 : type386 a0 a1 => forall y1 : type1350 a0 a1, (forall y2 : type1350 a0 a1, (y2 = y1) -> y0 y2) -> ex y0) (fun y0 : type1350 a0 a1 => forall y1 : type6 a0, (y0 (@_103802 a0 y1)) = (x0 y1)).
Definition term24 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) := exists y0 : type1328 a0 a1, forall y1 : nat, forall y2 : type6 a0, forall y3 : type1610 a0, (y0 (@CONSTR (finite_sum (finite_sum a0 a0) unit) y1 y2 y3)) = (@FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y4 : type6 a0 => fun y5 : type1610 a0 => fun y6 : nat -> a1 => x0 y4) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) y1 y2 y3 (fun y4 : nat => y0 (y3 y4))).
Definition term30 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : nat) (x2 : type6 a0) (x3 : type1328 a0 a1) (x4 : type1610 a0) := (fun y0 : type1610 a0 => (x3 (@CONSTR (finite_sum (finite_sum a0 a0) unit) x1 x2 y0)) = (@FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y1 : type6 a0 => fun y2 : type1610 a0 => fun y3 : nat -> a1 => x0 y1) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) x1 x2 y0 (fun y1 : nat => x3 (y0 y1)))) x4.
Definition term27 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : nat) (x2 : type1328 a0 a1) := forall y0 : type6 a0, forall y1 : type1610 a0, (x2 (@CONSTR (finite_sum (finite_sum a0 a0) unit) x1 y0 y1)) = (@FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y2 : type6 a0 => fun y3 : type1610 a0 => fun y4 : nat -> a1 => x0 y2) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) x1 y0 y1 (fun y2 : nat => x2 (y1 y2))).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1350 a0 a1) (x1 : type6 a0) := x0 (@_103802 a0 x1).
Definition term43 (a0 : Type') (a1 : Type') (x0 : type1328 a0 a1) := fun y0 : nat => x0 ((fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)) y0).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1328 a0 a1) (x1 : type39 a0) (x2 : type6 a0) := x0 (@_dest_tybit1 a0 (@_mk_tybit1 a0 (x1 x2))).
Definition term11 (a0 : Type') (x0 : type6 a0) := (fun y0 : type6 a0 => @CONSTR (finite_sum (finite_sum a0 a0) unit) (NUMERAL 0) y0 (fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit))) x0.
Definition term8 (a0 : Type') (x0 : type1675 a0) := @_dest_tybit1 a0 (@_mk_tybit1 a0 x0).
Definition term10 (a0 : Type') (a1 : Type') (x0 : type1328 a0 a1) (x1 : type39 a0) (x2 : type6 a0) := x0 (x1 x2).
Definition term7 (a0 : Type') (x0 : type1329 a0) (x1 : type39 a0) (x2 : type6 a0) := x0 (x1 x2).
Definition term33 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type6 a0) (x2 : type1328 a0 a1) := @FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y0 : type6 a0 => fun y1 : type1610 a0 => fun y2 : nat -> a1 => x0 y0) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) (NUMERAL 0) x1 (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)) (fun y0 : nat => x2 ((fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)) y0)).
Definition term44 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type6 a0) (x2 : type1328 a0 a1) := (fun y0 : type6 a0 => fun y1 : type1610 a0 => fun y2 : nat -> a1 => x0 y0) x1 (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)) (fun y0 : nat => x2 ((fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)) y0)).
Definition term42 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type6 a0) := (fun y0 : type6 a0 => fun y1 : type1610 a0 => fun y2 : nat -> a1 => x0 y0) x1 (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)).
Definition term39 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type6 a0) := @FCONS ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1) (fun y0 : type6 a0 => fun y1 : type1610 a0 => fun y2 : nat -> a1 => x0 y0) (@FNIL ((finite_sum (finite_sum a0 a0) unit) -> (nat -> recspace (finite_sum (finite_sum a0 a0) unit)) -> (nat -> a1) -> a1)) (NUMERAL 0) x1.
Definition term40 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type6 a0) := (fun y0 : type6 a0 => fun y1 : type1610 a0 => fun y2 : nat -> a1 => x0 y0) x1.
Definition term47 (a0 : Type') (a1 : Type') (x0 : type41 a0 a1) (x1 : type6 a0) (x2 : type1328 a0 a1) := (fun y0 : type1610 a0 => fun y1 : nat -> a1 => x0 x1) (fun y0 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)) (fun y0 : nat => x2 ((fun y1 : nat => @BOTTOM (finite_sum (finite_sum a0 a0) unit)) y0)).