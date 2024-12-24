Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3323992 : forall {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop), (@UNIONS _86827 (@INSERT (_86827 -> Prop) s (@INSERT (_86827 -> Prop) t (@EMPTY (_86827 -> Prop))))) = (@UNION _86827 s t).
