Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1105743_term_abbrevs.
Require Import thm1105741_spec.
Require Import thm1105742_spec.
Lemma lem1105743 {_25569 : Type'} (l : list _25569) : (term0 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
