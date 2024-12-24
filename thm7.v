Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm0_spec.
Lemma lem2 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem3 (t : Prop) (h1 : t) : t = True.
Proof. exact (prop_ext (fun h2 : t => @lem0) (fun h2 : True => @lem2 t h1)). Qed.
Lemma lem4 (t : Prop) (h1 : t = True) : t = True.
Proof. exact (h1). Qed.
Lemma lem5 (t : Prop) (h1 : t = True) : True = t.
Proof. exact (SYM (@lem4 t h1)). Qed.
Lemma lem6 (t : Prop) (h1 : t = True) : t.
Proof. exact (EQ_MP (@lem5 t h1) (@lem0)). Qed.
Lemma lem7 (t : Prop) : t = (t = True).
Proof. exact (prop_ext (fun h1 : t => @lem3 t h1) (fun h1 : t = True => @lem6 t h1)). Qed.
