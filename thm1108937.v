Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1108937_term_abbrevs.
Require Import thm1108934_spec.
Lemma lem1108936 {_25719 _25727 : Type'} : term0 _25719 _25727.
Proof. exact (proj1 (@lem1108934 _25719 _25727)). Qed.
Lemma lem1108937 {_25719 _25727 : Type'} (l2 : list _25727) : term1 _25719 _25727 l2.
Proof. exact (@lem1108936 _25719 _25727 l2). Qed.
