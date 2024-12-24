Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1109873_term_abbrevs.
Lemma lem1109873 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) : (term0 _25786 _25787 f l) = ((@ALLPAIRS _25786 _25787 f (@nil _25787) l) = True).
Proof. exact (eq_refl (term0 _25786 _25787 f l)). Qed.
