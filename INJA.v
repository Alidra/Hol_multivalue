Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJA_term_abbrevs.
Lemma lem1055829 {A : Type'} : (@INJA A) = (term0 A).
Proof. exact (@INJA_def A). Qed.
Lemma lem1055830 {A : Type'} (_17379 : A) : _17379 = _17379.
Proof. exact (eq_refl _17379). Qed.
Lemma lem1055831 {A : Type'} (_17379 : A) : (@INJA A _17379) = (term1 A _17379).
Proof. exact (MK_COMB (@lem1055829 A) (@lem1055830 A _17379)). Qed.
Lemma lem1055832 {A : Type'} (_17379 : A) : (term1 A _17379) = (term2 A _17379).
Proof. exact (eq_refl (term1 A _17379)). Qed.
Lemma lem1055833 {A : Type'} (_17379 : A) : (@INJA A _17379) = (term2 A _17379).
Proof. exact (TRANS (@lem1055831 A _17379) (@lem1055832 A _17379)). Qed.
Lemma lem1055834 {A : Type'} : term3 A.
Proof. exact (fun _17379 : A => @lem1055833 A _17379). Qed.
Lemma lem1055835 {A : Type'} (_17379 : A) : term4 A _17379.
Proof. exact (@lem1055834 A _17379). Qed.
Lemma lem1055836 {A : Type'} (_17379 : A) : (term4 A _17379) = ((@INJA A _17379) = (term2 A _17379)).
Proof. exact (eq_refl (term4 A _17379)). Qed.
Lemma lem1055837 {A : Type'} (_17379 : A) : (@INJA A _17379) = (term2 A _17379).
Proof. exact (EQ_MP (@lem1055836 A _17379) (@lem1055835 A _17379)). Qed.
Lemma lem1055867 {A : Type'} (a : A) : (@INJA A a) = (term2 A a).
Proof. exact (@lem1055837 A a). Qed.
Lemma lem1055868 {A : Type'} : term3 A.
Proof. exact (fun a : A => @lem1055867 A a). Qed.
