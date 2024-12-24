Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1108947_term_abbrevs.
Lemma lem1108947 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (l2 : list _25727) : (term0 _25719 _25727 h1' t1 l2) = ((term1 _25719 _25727 h1' t1 l2) = (term2 _25719 _25727 h1' t1 l2)).
Proof. exact (eq_refl (term0 _25719 _25727 h1' t1 l2)). Qed.
