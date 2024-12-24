Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1105053_term_abbrevs.
Lemma lem1105053 {_25498 _25501 _25508 : Type'} (f : type1475 _25498 _25501 _25508) (l : list _25508) : (term0 _25498 _25501 _25508 f l) = ((@MAP2 _25498 _25501 _25508 f (@nil _25501) l) = (@nil _25498)).
Proof. exact (eq_refl (term0 _25498 _25501 _25508 f l)). Qed.
