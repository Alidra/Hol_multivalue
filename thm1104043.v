Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1104043_term_abbrevs.
Require Import thm1104037_spec.
Lemma lem1104039 {_25409 _25416 : Type'} : term0 _25409 _25416.
Proof. exact (proj1 (@lem1104037 _25409 _25416)). Qed.
Lemma lem1104040 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : term1 _25409 _25416 P.
Proof. exact (@lem1104039 _25409 _25416 P). Qed.
Lemma lem1104041 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : (term1 _25409 _25416 P) = (term2 _25409 _25416 P).
Proof. exact (eq_refl (term1 _25409 _25416 P)). Qed.
Lemma lem1104042 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) : term2 _25409 _25416 P.
Proof. exact (EQ_MP (@lem1104041 _25409 _25416 P) (@lem1104040 _25409 _25416 P)). Qed.
Lemma lem1104043 {_25409 _25416 : Type'} (P : type1413 _25409 _25416) (l2 : list _25416) : term3 _25409 _25416 P l2.
Proof. exact (@lem1104042 _25409 _25416 P l2). Qed.
