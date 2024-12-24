Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm528081_term_abbrevs.
Require Import thm528019_spec.
Lemma lem528020 : term0.
Proof. exact (proj2 (@lem528019)). Qed.
Lemma lem528021 : term1.
Proof. exact (proj2 (@lem528020)). Qed.
Lemma lem528022 : term2.
Proof. exact (proj2 (@lem528021)). Qed.
Lemma lem528023 : term3.
Proof. exact (proj2 (@lem528022)). Qed.
Lemma lem528024 : term4.
Proof. exact (proj2 (@lem528023)). Qed.
Lemma lem528025 : term5.
Proof. exact (proj2 (@lem528024)). Qed.
Lemma lem528026 : term6.
Proof. exact (proj2 (@lem528025)). Qed.
Lemma lem528027 : term7.
Proof. exact (proj2 (@lem528026)). Qed.
Lemma lem528028 (m : nat) : term8 m.
Proof. exact (@lem528027 m). Qed.
Lemma lem528029 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem528030 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem528029 m) (@lem528028 m)). Qed.
Lemma lem528031 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem528030 m n). Qed.
Lemma lem528032 (m : nat) (n : nat) : (term10 m n) = ((term11 m n) = (term12 m n)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem528080 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (EQ_MP (@lem528032 m n) (@lem528031 m n)). Qed.
Lemma lem528081 : term13 = term14.
Proof. exact (@lem528080 0 0). Qed.
