Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7929765_term_abbrevs.
Require Import thm7928467_spec.
Require Import thm7929757_spec.
Lemma lem7929758 {A : Type'} (_103802' : type39 A) (h1 : _103802' = (term0 A)) : (term1 A) = (term2 A _103802').
Proof. exact (SYM (@lem7928467 A _103802' h1)). Qed.
Lemma lem7929759 {A : Type'} (_103802' : type39 A) (h1 : _103802' = (term0 A)) : (@_103802 A) = (term2 A _103802').
Proof. exact (TRANS (@lem7929757 A) (@lem7929758 A _103802' h1)). Qed.
Lemma lem7929760 {A : Type'} (a : type6 A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7929761 {A : Type'} (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term0 A)) : (@_103802 A a) = (term3 A _103802' a).
Proof. exact (MK_COMB (@lem7929759 A _103802' h1) (@lem7929760 A a)). Qed.
Lemma lem7929762 {A : Type'} (_103802' : type39 A) (a : type6 A) : (term3 A _103802' a) = (term4 A _103802' a).
Proof. exact (eq_refl (term3 A _103802' a)). Qed.
Lemma lem7929763 {A : Type'} (a : type6 A) : (term5 A a) = (term5 A a).
Proof. exact (eq_refl (term5 A a)). Qed.
Lemma lem7929764 {A : Type'} (_103802' : type39 A) (a : type6 A) : ((@_103802 A a) = (term3 A _103802' a)) = ((@_103802 A a) = (term4 A _103802' a)).
Proof. exact (MK_COMB (@lem7929763 A a) (@lem7929762 A _103802' a)). Qed.
Lemma lem7929765 {A : Type'} (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term0 A)) : (@_103802 A a) = (term4 A _103802' a).
Proof. exact (EQ_MP (@lem7929764 A _103802' a) (@lem7929761 A a _103802' h1)). Qed.
