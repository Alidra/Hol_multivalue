Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm759283_term_abbrevs.
Require Import ARITH_ADD_spec.
Lemma lem759219 : term0.
Proof. exact (proj2 (@lem514291)). Qed.
Lemma lem759220 : term1.
Proof. exact (proj2 (@lem759219)). Qed.
Lemma lem759221 : term2.
Proof. exact (proj2 (@lem759220)). Qed.
Lemma lem759222 : term3.
Proof. exact (proj2 (@lem759221)). Qed.
Lemma lem759223 : term4.
Proof. exact (proj2 (@lem759222)). Qed.
Lemma lem759255 : term5.
Proof. exact (proj1 (@lem759223)). Qed.
Lemma lem759256 (n : nat) : term6 n.
Proof. exact (@lem759255 n). Qed.
Lemma lem759257 (n : nat) : (term6 n) = ((term7 n) = (BIT1 n)).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem759280 (n : nat) : (term7 n) = (BIT1 n).
Proof. exact (EQ_MP (@lem759257 n) (@lem759256 n)). Qed.
Lemma lem759281 : term8 = term9.
Proof. exact (@lem759280 term10). Qed.
Lemma lem759282 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem759283 : term11 = term12.
Proof. exact (MK_COMB (@lem759282) (@lem759281)). Qed.
