Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ZIP_DEF_term_abbrevs.
Require Import thm1108939_spec.
Require Import thm1108946_spec.
Require Import thm1108947_spec.
Lemma lem1108948 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (l2 : list _25727) : (term0 _25719 _25727 h1' t1 l2) = (term1 _25719 _25727 h1' t1 l2).
Proof. exact (EQ_MP (@lem1108947 _25719 _25727 h1' t1 l2) (@lem1108946 _25719 _25727 h1' t1 l2)). Qed.
Lemma lem1108949 {_25719 _25727 : Type'} (h1' : _25719) (t1 : list _25719) (l2 : list _25727) : term2 _25719 _25727 h1' t1 l2.
Proof. exact (conj (@lem1108939 _25719 _25727 l2) (@lem1108948 _25719 _25727 h1' t1 l2)). Qed.
