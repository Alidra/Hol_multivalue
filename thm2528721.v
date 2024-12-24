Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2528721_term_abbrevs.
Require Import INT_REM_EQ_spec.
Lemma lem2528715 (m : int) : term0 m.
Proof. exact (@lem2522863 m). Qed.
Lemma lem2528716 (m : int) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2528717 (m : int) : term1 m.
Proof. exact (EQ_MP (@lem2528716 m) (@lem2528715 m)). Qed.
Lemma lem2528718 (m : int) (n : int) : term2 m n.
Proof. exact (@lem2528717 m n). Qed.
Lemma lem2528719 (m : int) (n : int) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2528720 (m : int) (n : int) : term3 m n.
Proof. exact (EQ_MP (@lem2528719 m n) (@lem2528718 m n)). Qed.
Lemma lem2528721 (m : int) (n : int) (p : int) : term4 m n p.
Proof. exact (@lem2528720 m n p). Qed.
