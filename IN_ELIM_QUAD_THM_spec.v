Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3421067 : forall {_88646 _88647 _88648 _88649 _88729 _88730 _88731 _88732 _88810 _88811 _88812 _88813 : Type'}, (forall P : _88649 -> _88648 -> _88647 -> _88646 -> Prop, forall a : _88649, forall b : _88648, forall c : _88647, forall d : _88646, (@IN (prod _88649 (prod _88648 (prod _88647 _88646))) (@pair _88649 (prod _88648 (prod _88647 _88646)) a (@pair _88648 (prod _88647 _88646) b (@pair _88647 _88646 c d))) (@GSPEC (prod _88649 (prod _88648 (prod _88647 _88646))) (fun GEN_PVAR_34 : prod _88649 (prod _88648 (prod _88647 _88646)) => exists w : _88649, exists x : _88648, exists y : _88647, exists z : _88646, @SETSPEC (prod _88649 (prod _88648 (prod _88647 _88646))) GEN_PVAR_34 (P w x y z) (@pair _88649 (prod _88648 (prod _88647 _88646)) w (@pair _88648 (prod _88647 _88646) x (@pair _88647 _88646 y z)))))) = (P a b c d)) /\ ((forall P : _88732 -> _88731 -> _88730 -> _88729 -> Prop, forall a : _88732, forall b : _88731, forall c : _88730, forall d : _88729, (@IN (prod (prod _88732 _88731) (prod _88730 _88729)) (@pair (prod _88732 _88731) (prod _88730 _88729) (@pair _88732 _88731 a b) (@pair _88730 _88729 c d)) (@GSPEC (prod (prod _88732 _88731) (prod _88730 _88729)) (fun GEN_PVAR_35 : prod (prod _88732 _88731) (prod _88730 _88729) => exists w : _88732, exists x : _88731, exists y : _88730, exists z : _88729, @SETSPEC (prod (prod _88732 _88731) (prod _88730 _88729)) GEN_PVAR_35 (P w x y z) (@pair (prod _88732 _88731) (prod _88730 _88729) (@pair _88732 _88731 w x) (@pair _88730 _88729 y z))))) = (P a b c d)) /\ (forall P : _88813 -> _88812 -> _88811 -> _88810 -> Prop, forall a : _88813, forall b : _88812, forall c : _88811, forall d : _88810, (@IN (prod (prod (prod _88813 _88812) _88811) _88810) (@pair (prod (prod _88813 _88812) _88811) _88810 (@pair (prod _88813 _88812) _88811 (@pair _88813 _88812 a b) c) d) (@GSPEC (prod (prod (prod _88813 _88812) _88811) _88810) (fun GEN_PVAR_36 : prod (prod (prod _88813 _88812) _88811) _88810 => exists w : _88813, exists x : _88812, exists y : _88811, exists z : _88810, @SETSPEC (prod (prod (prod _88813 _88812) _88811) _88810) GEN_PVAR_36 (P w x y z) (@pair (prod (prod _88813 _88812) _88811) _88810 (@pair (prod _88813 _88812) _88811 (@pair _88813 _88812 w x) y) z)))) = (P a b c d))).