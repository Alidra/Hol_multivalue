Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3421247 : forall {_88856 _88857 : Type'}, forall P : (prod _88857 _88856) -> Prop, (@GSPEC (prod _88857 _88856) (fun GEN_PVAR_37 : prod _88857 _88856 => exists p : prod _88857 _88856, @SETSPEC (prod _88857 _88856) GEN_PVAR_37 (P p) p)) = (@GSPEC (prod _88857 _88856) (fun GEN_PVAR_38 : prod _88857 _88856 => exists a : _88857, exists b : _88856, @SETSPEC (prod _88857 _88856) GEN_PVAR_38 (P (@pair _88857 _88856 a b)) (@pair _88857 _88856 a b))).
