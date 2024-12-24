Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841368_term_abbrevs.
Require Import INT_OF_NUM_MIN_spec.
Lemma lem2841353 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term0 m n) = (term1 m n).
Proof. exact (h1). Qed.
Lemma lem2841354 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term1 m n) = (term0 m n).
Proof. exact (SYM (@lem2841353 m n h1)). Qed.
Lemma lem2841355 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term1 m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem2841356 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term0 m n) = (term1 m n).
Proof. exact (SYM (@lem2841355 m n h1)). Qed.
Lemma lem2841357 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = ((term1 m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (term1 m n) => @lem2841354 m n h1) (fun h1 : (term1 m n) = (term0 m n) => @lem2841356 m n h1)). Qed.
Lemma lem2841358 (m : nat) : (term2 m) = (term3 m).
Proof. exact (fun_ext (fun n : nat => @lem2841357 m n)). Qed.
Lemma lem2841359 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841360 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem2841359) (@lem2841358 m)). Qed.
Lemma lem2841361 : term6 = term7.
Proof. exact (fun_ext (fun m : nat => @lem2841360 m)). Qed.
Lemma lem2841362 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841363 : term8 = term9.
Proof. exact (MK_COMB (@lem2841362) (@lem2841361)). Qed.
Lemma lem2841364 : term9.
Proof. exact (EQ_MP (@lem2841363) (@lem2307309)). Qed.
Lemma lem2841365 (m : nat) : term10 m.
Proof. exact (@lem2841364 m). Qed.
Lemma lem2841366 (m : nat) : (term10 m) = (term5 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem2841367 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem2841366 m) (@lem2841365 m)). Qed.
Lemma lem2841368 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem2841367 m n). Qed.
