Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117492_term_abbrevs.
Require Import num_coprime_spec.
Lemma lem3117489 (a : nat) : term0 a.
Proof. exact (@lem2838452 a). Qed.
Lemma lem3117490 (a : nat) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem3117491 (a : nat) : term1 a.
Proof. exact (EQ_MP (@lem3117490 a) (@lem3117489 a)). Qed.
Lemma lem3117492 (a : nat) (b : nat) : term2 a b.
Proof. exact (@lem3117491 a b). Qed.
