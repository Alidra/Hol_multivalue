Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184694_term_abbrevs.
Require Import thm3183255_spec.
Require Import thm3183343_spec.
Require Import thm3183481_spec.
Lemma lem3184693 {_83064 : Type'} (x : _83064) : (@SETSPEC _83064 x) = (term0 _83064 x).
Proof. exact (EQ_MP (@lem3183343 _83064 x) (@lem3183481 _83064 x)). Qed.
Lemma lem3184694 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term1 _83064 P x) = (term2 _83064 P x).
Proof. exact (MK_COMB (@lem3183255 _83064 P) (@lem3184693 _83064 x)). Qed.
