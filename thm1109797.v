Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1109797_term_abbrevs.
Lemma lem1109797 {_25786 _25787 : Type'} : (@ALLPAIRS _25786 _25787) = (term0 _25786 _25787).
Proof. exact (@ALLPAIRS_def _25786 _25787). Qed.
