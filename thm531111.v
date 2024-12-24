Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm531111_term_abbrevs.
Require Import thm531090_spec.
Lemma lem531091 : term0.
Proof. exact (proj2 (@lem531090)). Qed.
Lemma lem531107 : term1.
Proof. exact (proj1 (@lem531091)). Qed.
Lemma lem531108 (m : nat) : term2 m.
Proof. exact (@lem531107 m). Qed.
Lemma lem531109 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem531110 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem531109 m) (@lem531108 m)). Qed.
Lemma lem531111 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem531110 m n). Qed.
