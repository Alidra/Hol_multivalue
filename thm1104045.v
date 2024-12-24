Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1104043_spec.
Require Import thm1104044_spec.
Lemma lem1104045 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) : (@ALL2 _25409 _25416 P (@nil _25409) l2) = (l2 = (@nil _25416)).
Proof. exact (EQ_MP (@lem1104044 _25409 _25416 P l2) (@lem1104043 _25409 _25416 P l2)). Qed.
