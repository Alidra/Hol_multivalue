Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516851_term_abbrevs.
Require Import LE_MULT_LCANCEL_spec.
Lemma lem516845 (m : nat) : term0 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem516846 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem516847 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem516846 m) (@lem516845 m)). Qed.
Lemma lem516848 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem516847 m n). Qed.
Lemma lem516849 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem516850 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem516849 m n) (@lem516848 m n)). Qed.
Lemma lem516851 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem516850 m n p). Qed.
