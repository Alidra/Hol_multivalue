Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4372153 : forall {_104757 _104758 _104795 _104796 : Type'}, (forall s : _104757 -> Prop, forall f : (_104758 -> Prop) -> Prop, (@CROSS _104758 _104757 s (@UNIONS _104758 f)) = (@UNIONS (prod _104757 _104758) (@GSPEC ((prod _104757 _104758) -> Prop) (fun GEN_PVAR_132 : (prod _104757 _104758) -> Prop => exists t : _104758 -> Prop, @SETSPEC ((prod _104757 _104758) -> Prop) GEN_PVAR_132 (@IN (_104758 -> Prop) t f) (@CROSS _104758 _104757 s t))))) /\ (forall f : (_104795 -> Prop) -> Prop, forall t : _104796 -> Prop, (@CROSS _104796 _104795 (@UNIONS _104795 f) t) = (@UNIONS (prod _104795 _104796) (@GSPEC ((prod _104795 _104796) -> Prop) (fun GEN_PVAR_133 : (prod _104795 _104796) -> Prop => exists s : _104795 -> Prop, @SETSPEC ((prod _104795 _104796) -> Prop) GEN_PVAR_133 (@IN (_104795 -> Prop) s f) (@CROSS _104796 _104795 s t))))).
