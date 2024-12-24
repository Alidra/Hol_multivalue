Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841326_term_abbrevs.
Require Import INT_OF_NUM_ADD_spec.
Lemma lem2841315 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term0 m n) = (term1 m n).
Proof. exact (h1). Qed.
Lemma lem2841316 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term1 m n) = (term0 m n).
Proof. exact (SYM (@lem2841315 m n h1)). Qed.
Lemma lem2841317 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term1 m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem2841318 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term0 m n) = (term1 m n).
Proof. exact (SYM (@lem2841317 m n h1)). Qed.
Lemma lem2841319 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = ((term1 m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (term1 m n) => @lem2841316 m n h1) (fun h1 : (term1 m n) = (term0 m n) => @lem2841318 m n h1)). Qed.
Lemma lem2841320 (m : nat) : (term2 m) = (term3 m).
Proof. exact (fun_ext (fun n : nat => @lem2841319 m n)). Qed.
Lemma lem2841321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841322 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem2841321) (@lem2841320 m)). Qed.
Lemma lem2841323 : term6 = term7.
Proof. exact (fun_ext (fun m : nat => @lem2841322 m)). Qed.
Lemma lem2841324 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841325 : term8 = term9.
Proof. exact (MK_COMB (@lem2841324) (@lem2841323)). Qed.
Lemma lem2841326 : term9.
Proof. exact (EQ_MP (@lem2841325) (@lem2306816)). Qed.
