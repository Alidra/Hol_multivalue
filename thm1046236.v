Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1046236_term_abbrevs.
Require Import thm1046224_spec.
Lemma lem1046226 : term0.
Proof. exact (proj1 (@lem1046224)). Qed.
Lemma lem1046227 (a : nat) : term1 a.
Proof. exact (@lem1046226 a). Qed.
Lemma lem1046228 (a : nat) : (term1 a) = (term2 a).
Proof. exact (eq_refl (term1 a)). Qed.
Lemma lem1046229 (a : nat) : term2 a.
Proof. exact (EQ_MP (@lem1046228 a) (@lem1046227 a)). Qed.
Lemma lem1046230 (a : nat) (b : nat) : term3 a b.
Proof. exact (@lem1046229 a b). Qed.
Lemma lem1046231 (a : nat) (b : nat) : (term3 a b) = (term4 a b).
Proof. exact (eq_refl (term3 a b)). Qed.
Lemma lem1046232 (a : nat) (b : nat) : term4 a b.
Proof. exact (EQ_MP (@lem1046231 a b) (@lem1046230 a b)). Qed.
Lemma lem1046233 (a : nat) (b : nat) (c : nat) : term5 a b c.
Proof. exact (@lem1046232 a b c). Qed.
Lemma lem1046234 (a : nat) (b : nat) (c : nat) : (term5 a b c) = (term6 a b c).
Proof. exact (eq_refl (term5 a b c)). Qed.
Lemma lem1046235 (a : nat) (b : nat) (c : nat) : term6 a b c.
Proof. exact (EQ_MP (@lem1046234 a b c) (@lem1046233 a b c)). Qed.
Lemma lem1046236 (a : nat) (b : nat) (c : nat) (d : nat) : term7 a b c d.
Proof. exact (@lem1046235 a b c d). Qed.
