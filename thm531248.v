Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm531248_term_abbrevs.
Require Import thm531156_spec.
Require Import thm531171_spec.
Require Import thm531183_spec.
Require Import thm531184_spec.
Lemma lem531235 (m : nat) (n : nat) : (term0 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem531184 m n) (@lem531183 m n)). Qed.
Lemma lem531236 : term2 = term3.
Proof. exact (@lem531235 0 0). Qed.
Lemma lem531238 : (Nat.add 0 0) = 0.
Proof. exact (proj1 (@lem531171)). Qed.
Lemma lem531239 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem531240 : term4 = (S 0).
Proof. exact (MK_COMB (@lem531239) (@lem531238)). Qed.
Lemma lem531242 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem531156)). Qed.
Lemma lem531243 : term4 = (BIT1 0).
Proof. exact (TRANS (@lem531240) (@lem531242)). Qed.
Lemma lem531244 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem531245 : term3 = term5.
Proof. exact (MK_COMB (@lem531244) (@lem531243)). Qed.
Lemma lem531246 : term2 = term5.
Proof. exact (TRANS (@lem531236) (@lem531245)). Qed.
Lemma lem531247 : BIT0 = BIT0.
Proof. exact (eq_refl BIT0). Qed.
Lemma lem531248 : term6 = term7.
Proof. exact (MK_COMB (@lem531247) (@lem531246)). Qed.
