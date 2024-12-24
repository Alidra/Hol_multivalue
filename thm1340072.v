Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1340072_term_abbrevs.
Require Import thm1337531_spec.
Require Import thm1337536_spec.
Require Import thm1338076_spec.
Require Import thm1338081_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1340051 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1340052 : term1 = (term2 = term3).
Proof. exact (@lem1340051 term4 term5). Qed.
Lemma lem1340056 (x : prod hreal hreal) : (term6 x) = (term7 x).
Proof. exact (EQ_MP (@lem1338081 x) (@lem1338076 x)). Qed.
Lemma lem1340057 : term2 = term8.
Proof. exact (@lem1340056 term5). Qed.
Lemma lem1340059 (m : nat) : (term9 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340060 : term3 = term10.
Proof. exact (@lem1340059 (NUMERAL 0)). Qed.
Lemma lem1340061 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1340062 : term8 = term11.
Proof. exact (MK_COMB (@lem1340061) (@lem1340060)). Qed.
Lemma lem1340063 : term2 = term11.
Proof. exact (TRANS (@lem1340057) (@lem1340062)). Qed.
Lemma lem1340064 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1340065 : term12 = term13.
Proof. exact (MK_COMB (@lem1340064) (@lem1340063)). Qed.
Lemma lem1340067 (m : nat) : (term9 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340068 : term3 = term10.
Proof. exact (@lem1340067 (NUMERAL 0)). Qed.
Lemma lem1340069 : (term2 = term3) = (term11 = term10).
Proof. exact (MK_COMB (@lem1340065) (@lem1340068)). Qed.
Lemma lem1340072 : term1 = (term11 = term10).
Proof. exact (TRANS (@lem1340052) (@lem1340069)). Qed.
