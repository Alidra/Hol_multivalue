Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1110681_term_abbrevs.
Require Import thm1110670_spec.
Lemma lem1110675 {A : Type'} (h : A) : term0 A h.
Proof. exact (@lem1110670 A h). Qed.
Lemma lem1110676 {A : Type'} (h : A) : (term0 A h) = (term1 A h).
Proof. exact (eq_refl (term0 A h)). Qed.
Lemma lem1110677 {A : Type'} (h : A) : term1 A h.
Proof. exact (EQ_MP (@lem1110676 A h) (@lem1110675 A h)). Qed.
Lemma lem1110678 {A : Type'} (h : A) (r : type1402 A) : term2 A h r.
Proof. exact (@lem1110677 A h r). Qed.
Lemma lem1110679 {A : Type'} (h : A) (r : type1402 A) : (term2 A h r) = (term3 A h r).
Proof. exact (eq_refl (term2 A h r)). Qed.
Lemma lem1110680 {A : Type'} (h : A) (r : type1402 A) : term3 A h r.
Proof. exact (EQ_MP (@lem1110679 A h r) (@lem1110678 A h r)). Qed.
Lemma lem1110681 {A : Type'} (h : A) (r : type1402 A) (t : list A) : term4 A h r t.
Proof. exact (@lem1110680 A h r t). Qed.
