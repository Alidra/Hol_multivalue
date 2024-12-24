Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117317_term_abbrevs.
Require Import INT_OF_NUM_EQ_spec.
Lemma lem3117306 (m : nat) (n : nat) (h1 : ((int_of_num m) = (int_of_num n)) = (m = n)) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (h1). Qed.
Lemma lem3117307 (m : nat) (n : nat) (h1 : ((int_of_num m) = (int_of_num n)) = (m = n)) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (SYM (@lem3117306 m n h1)). Qed.
Lemma lem3117308 (m : nat) (n : nat) (h1 : (m = n) = ((int_of_num m) = (int_of_num n))) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (h1). Qed.
Lemma lem3117309 (m : nat) (n : nat) (h1 : (m = n) = ((int_of_num m) = (int_of_num n))) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (SYM (@lem3117308 m n h1)). Qed.
Lemma lem3117310 (m : nat) (n : nat) : (((int_of_num m) = (int_of_num n)) = (m = n)) = ((m = n) = ((int_of_num m) = (int_of_num n))).
Proof. exact (prop_ext (fun h1 : ((int_of_num m) = (int_of_num n)) = (m = n) => @lem3117307 m n h1) (fun h1 : (m = n) = ((int_of_num m) = (int_of_num n)) => @lem3117309 m n h1)). Qed.
Lemma lem3117311 (m : nat) : (term0 m) = (term1 m).
Proof. exact (fun_ext (fun n : nat => @lem3117310 m n)). Qed.
Lemma lem3117312 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3117313 (m : nat) : (term2 m) = (term3 m).
Proof. exact (MK_COMB (@lem3117312) (@lem3117311 m)). Qed.
Lemma lem3117314 : term4 = term5.
Proof. exact (fun_ext (fun m : nat => @lem3117313 m)). Qed.
Lemma lem3117315 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3117316 : term6 = term7.
Proof. exact (MK_COMB (@lem3117315) (@lem3117314)). Qed.
Lemma lem3117317 : term7.
Proof. exact (EQ_MP (@lem3117316) (@lem2307147)). Qed.
