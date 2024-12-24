Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416594_term_abbrevs.
Require Import thm2416504_spec.
Lemma lem2416588 : term0.
Proof. exact (proj2 (@lem2416504)). Qed.
Lemma lem2416589 (x : int) : term1 x.
Proof. exact (@lem2416588 x). Qed.
Lemma lem2416590 (x : int) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem2416591 (x : int) : term2 x.
Proof. exact (EQ_MP (@lem2416590 x) (@lem2416589 x)). Qed.
Lemma lem2416592 (x : int) (y : int) : term3 x y.
Proof. exact (@lem2416591 x y). Qed.
Lemma lem2416593 (x : int) (y : int) : (term3 x y) = ((int_sub x y) = (term4 x y)).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem2416594 (x : int) (y : int) : (int_sub x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2416593 x y) (@lem2416592 x y)). Qed.
