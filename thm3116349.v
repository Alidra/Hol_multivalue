Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3116349_term_abbrevs.
Require Import DIVIDES_ANTISYM_spec.
Lemma lem3116334 (m : nat) (n : nat) (h1 : (term0 n m) = (m = n)) : (term0 n m) = (m = n).
Proof. exact (h1). Qed.
Lemma lem3116335 (m : nat) (n : nat) (h1 : (term0 n m) = (m = n)) : (m = n) = (term0 n m).
Proof. exact (SYM (@lem3116334 m n h1)). Qed.
Lemma lem3116336 (n : nat) (m : nat) (h1 : (m = n) = (term0 n m)) : (m = n) = (term0 n m).
Proof. exact (h1). Qed.
Lemma lem3116337 (n : nat) (m : nat) (h1 : (m = n) = (term0 n m)) : (term0 n m) = (m = n).
Proof. exact (SYM (@lem3116336 n m h1)). Qed.
Lemma lem3116338 (n : nat) (m : nat) : ((term0 n m) = (m = n)) = ((m = n) = (term0 n m)).
Proof. exact (prop_ext (fun h1 : (term0 n m) = (m = n) => @lem3116335 m n h1) (fun h1 : (m = n) = (term0 n m) => @lem3116337 n m h1)). Qed.
Lemma lem3116339 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem3116338 n m)). Qed.
Lemma lem3116340 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3116341 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem3116340) (@lem3116339 m)). Qed.
Lemma lem3116342 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem3116341 m)). Qed.
Lemma lem3116343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3116344 : term7 = term8.
Proof. exact (MK_COMB (@lem3116343) (@lem3116342)). Qed.
Lemma lem3116345 : term8.
Proof. exact (EQ_MP (@lem3116344) (@lem3108438)). Qed.
Lemma lem3116346 (m : nat) : term9 m.
Proof. exact (@lem3116345 m). Qed.
Lemma lem3116347 (m : nat) : (term9 m) = (term4 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem3116348 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem3116347 m) (@lem3116346 m)). Qed.
Lemma lem3116349 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem3116348 m n). Qed.
