Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1108213_spec.
Require Import thm1108214_spec.
Lemma lem1108215 {_25645 _25647 _25655 : Type'} (f : type1474 _25645 _25647 _25655) (l2 : list _25655) (b : _25645) : (@ITLIST2 _25645 _25647 _25655 f (@nil _25647) l2 b) = b.
Proof. exact (EQ_MP (@lem1108214 _25645 _25647 _25655 f l2 b) (@lem1108213 _25645 _25647 _25655 f l2 b)). Qed.
