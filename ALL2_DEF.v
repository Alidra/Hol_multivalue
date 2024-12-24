Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL2_DEF_term_abbrevs.
Require Import thm1104045_spec.
Require Import thm1104055_spec.
Require Import thm1104056_spec.
Lemma lem1104057 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) (l2 : list _25416) : (term0 _25409 _25416 P h1' t1 l2) = (term1 _25409 _25416 h1' P t1 l2).
Proof. exact (EQ_MP (@lem1104056 _25409 _25416 h1' P t1 l2) (@lem1104055 _25409 _25416 h1' P t1 l2)). Qed.
Lemma lem1104058 {_25409 _25416 : Type'} (h1' : _25409) (P : type1413 _25409 _25416) (t1 : list _25409) (l2 : list _25416) : term2 _25409 _25416 h1' P t1 l2.
Proof. exact (conj (@lem1104045 _25409 _25416 P l2) (@lem1104057 _25409 _25416 h1' P t1 l2)). Qed.
