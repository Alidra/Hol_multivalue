Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1104056_term_abbrevs.
Lemma lem1104056 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) (l2 : list _25416) : (term0 _25409 _25416 h1' P t1 l2) = ((term1 _25409 _25416 P h1' t1 l2) = (term2 _25409 _25416 h1' P t1 l2)).
Proof. exact (eq_refl (term0 _25409 _25416 h1' P t1 l2)). Qed.
