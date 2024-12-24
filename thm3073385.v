Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3073385_term_abbrevs.
Require Import INT_OF_NUM_EQ_spec.
Lemma lem3073370 (m : nat) (n : nat) (h1 : ((int_of_num m) = (int_of_num n)) = (m = n)) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (h1). Qed.
Lemma lem3073371 (m : nat) (n : nat) (h1 : ((int_of_num m) = (int_of_num n)) = (m = n)) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (SYM (@lem3073370 m n h1)). Qed.
Lemma lem3073372 (m : nat) (n : nat) (h1 : (m = n) = ((int_of_num m) = (int_of_num n))) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (h1). Qed.
Lemma lem3073373 (m : nat) (n : nat) (h1 : (m = n) = ((int_of_num m) = (int_of_num n))) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (SYM (@lem3073372 m n h1)). Qed.
Lemma lem3073374 (m : nat) (n : nat) : (((int_of_num m) = (int_of_num n)) = (m = n)) = ((m = n) = ((int_of_num m) = (int_of_num n))).
Proof. exact (prop_ext (fun h1 : ((int_of_num m) = (int_of_num n)) = (m = n) => @lem3073371 m n h1) (fun h1 : (m = n) = ((int_of_num m) = (int_of_num n)) => @lem3073373 m n h1)). Qed.
Lemma lem3073375 (m : nat) : (term0 m) = (term1 m).
Proof. exact (fun_ext (fun n : nat => @lem3073374 m n)). Qed.
Lemma lem3073376 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3073377 (m : nat) : (term2 m) = (term3 m).
Proof. exact (MK_COMB (@lem3073376) (@lem3073375 m)). Qed.
Lemma lem3073378 : term4 = term5.
Proof. exact (fun_ext (fun m : nat => @lem3073377 m)). Qed.
Lemma lem3073379 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3073380 : term6 = term7.
Proof. exact (MK_COMB (@lem3073379) (@lem3073378)). Qed.
Lemma lem3073381 : term7.
Proof. exact (EQ_MP (@lem3073380) (@lem2307147)). Qed.
Lemma lem3073382 (m : nat) : term8 m.
Proof. exact (@lem3073381 m). Qed.
Lemma lem3073383 (m : nat) : (term8 m) = (term3 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem3073384 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem3073383 m) (@lem3073382 m)). Qed.
Lemma lem3073385 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem3073384 m n). Qed.
