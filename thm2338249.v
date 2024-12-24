Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2338249_term_abbrevs.
Require Import thm2338239_spec.
Lemma lem2338246 (m : nat) : term0 m.
Proof. exact (@lem2338239 m). Qed.
Lemma lem2338247 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2338248 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2338247 m) (@lem2338246 m)). Qed.
Lemma lem2338249 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2338248 m n). Qed.
