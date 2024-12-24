Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1109885_term_abbrevs.
Lemma lem1109885 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) (l : list _25786) : (term0 _25786 _25787 h f t l) = ((term1 _25786 _25787 f h t l) = (term2 _25786 _25787 h f t l)).
Proof. exact (eq_refl (term0 _25786 _25787 h f t l)). Qed.
