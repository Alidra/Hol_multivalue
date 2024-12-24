Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299876_term_abbrevs.
Require Import thm2299866_spec.
Lemma lem2299873 (x : int) : term0 x.
Proof. exact (@lem2299866 x). Qed.
Lemma lem2299874 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2299875 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2299874 x) (@lem2299873 x)). Qed.
Lemma lem2299876 (x : int) (n : nat) : term2 x n.
Proof. exact (@lem2299875 x n). Qed.
