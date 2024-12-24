Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1105052_spec.
Require Import thm1105053_spec.
Lemma lem1105054 {_25498 _25501 _25508 : Type'} (f : type1475 _25498 _25501 _25508) (l : list _25508) : (@MAP2 _25498 _25501 _25508 f (@nil _25501) l) = (@nil _25498).
Proof. exact (EQ_MP (@lem1105053 _25498 _25501 _25508 f l) (@lem1105052 _25498 _25501 _25508 f l)). Qed.
