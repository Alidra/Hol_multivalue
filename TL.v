Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TL_term_abbrevs.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Lemma lem1095390 {A : Type'} (h : A) (t : list A) : (term0 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
