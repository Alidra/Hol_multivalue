Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7260968_term_abbrevs.
Require Import thm7260959_spec.
Require Import thm7260960_spec.
Lemma lem7260966 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : term0 _132349 f s g.
Proof. exact (EQ_MP (@lem7260960 _132349 f s g) (@lem7260959 _132349 f s g)). Qed.
Lemma lem7260967 {_137613 : Type'} (f : _137613 -> real) (s : _137613 -> Prop) (g : _137613 -> real) : term0 _137613 f s g.
Proof. exact (@lem7260966 _137613 f s g). Qed.
Lemma lem7260968 {_137613 : Type'} (f : _137613 -> real) (s : _137613 -> Prop) (g : _137613 -> real) : term1 _137613 f s g.
Proof. exact (@lem7260967 _137613 (term2 _137613 f) s g). Qed.
