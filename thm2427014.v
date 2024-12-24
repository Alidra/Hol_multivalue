Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2427014_term_abbrevs.
Require Import thm2427002_spec.
Lemma lem2427004 : term0.
Proof. exact (proj1 (@lem2427002)). Qed.
Lemma lem2427005 (a : int) : term1 a.
Proof. exact (@lem2427004 a). Qed.
Lemma lem2427006 (a : int) : (term1 a) = (term2 a).
Proof. exact (eq_refl (term1 a)). Qed.
Lemma lem2427007 (a : int) : term2 a.
Proof. exact (EQ_MP (@lem2427006 a) (@lem2427005 a)). Qed.
Lemma lem2427008 (a : int) (b : int) : term3 a b.
Proof. exact (@lem2427007 a b). Qed.
Lemma lem2427009 (a : int) (b : int) : (term3 a b) = (term4 a b).
Proof. exact (eq_refl (term3 a b)). Qed.
Lemma lem2427010 (a : int) (b : int) : term4 a b.
Proof. exact (EQ_MP (@lem2427009 a b) (@lem2427008 a b)). Qed.
Lemma lem2427011 (a : int) (b : int) (c : int) : term5 a b c.
Proof. exact (@lem2427010 a b c). Qed.
Lemma lem2427012 (a : int) (b : int) (c : int) : (term5 a b c) = (term6 a b c).
Proof. exact (eq_refl (term5 a b c)). Qed.
Lemma lem2427013 (a : int) (b : int) (c : int) : term6 a b c.
Proof. exact (EQ_MP (@lem2427012 a b c) (@lem2427011 a b c)). Qed.
Lemma lem2427014 (a : int) (b : int) (c : int) (d : int) : term7 a b c d.
Proof. exact (@lem2427013 a b c d). Qed.
