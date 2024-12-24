Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1108938_term_abbrevs.
Lemma lem1108938 {_25719 _25727 : Type'} (l2 : list _25727) : (term0 _25719 _25727 l2) = ((@ZIP _25719 _25727 (@nil _25719) l2) = (@nil (prod _25719 _25727))).
Proof. exact (eq_refl (term0 _25719 _25727 l2)). Qed.
