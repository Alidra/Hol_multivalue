Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841256_term_abbrevs.
Require Import INT_OF_NUM_EQ_spec.
Lemma lem2841245 (m : nat) (n : nat) (h1 : ((int_of_num m) = (int_of_num n)) = (m = n)) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (h1). Qed.
Lemma lem2841246 (m : nat) (n : nat) (h1 : ((int_of_num m) = (int_of_num n)) = (m = n)) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (SYM (@lem2841245 m n h1)). Qed.
Lemma lem2841247 (m : nat) (n : nat) (h1 : (m = n) = ((int_of_num m) = (int_of_num n))) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (h1). Qed.
Lemma lem2841248 (m : nat) (n : nat) (h1 : (m = n) = ((int_of_num m) = (int_of_num n))) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (SYM (@lem2841247 m n h1)). Qed.
Lemma lem2841249 (m : nat) (n : nat) : (((int_of_num m) = (int_of_num n)) = (m = n)) = ((m = n) = ((int_of_num m) = (int_of_num n))).
Proof. exact (prop_ext (fun h1 : ((int_of_num m) = (int_of_num n)) = (m = n) => @lem2841246 m n h1) (fun h1 : (m = n) = ((int_of_num m) = (int_of_num n)) => @lem2841248 m n h1)). Qed.
Lemma lem2841250 (m : nat) : (term0 m) = (term1 m).
Proof. exact (fun_ext (fun n : nat => @lem2841249 m n)). Qed.
Lemma lem2841251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841252 (m : nat) : (term2 m) = (term3 m).
Proof. exact (MK_COMB (@lem2841251) (@lem2841250 m)). Qed.
Lemma lem2841253 : term4 = term5.
Proof. exact (fun_ext (fun m : nat => @lem2841252 m)). Qed.
Lemma lem2841254 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841255 : term6 = term7.
Proof. exact (MK_COMB (@lem2841254) (@lem2841253)). Qed.
Lemma lem2841256 : term7.
Proof. exact (EQ_MP (@lem2841255) (@lem2307147)). Qed.
