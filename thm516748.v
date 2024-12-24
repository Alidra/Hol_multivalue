Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516748_term_abbrevs.
Require Import LE_SUC_LT_spec.
Lemma lem516745 (m : nat) : term0 m.
Proof. exact (@lem91144 m). Qed.
Lemma lem516746 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem516747 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem516746 m) (@lem516745 m)). Qed.
Lemma lem516748 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem516747 m n). Qed.
