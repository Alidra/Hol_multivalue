Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HD_term_abbrevs.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Lemma lem1094867 {A : Type'} (t : list A) (h : A) : (term0 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
