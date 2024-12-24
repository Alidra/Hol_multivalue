Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299752_term_abbrevs.
Require Import int_of_num_th_spec.
Lemma lem2299744 (n : nat) (h1 : (term0 n) = (real_of_num n)) : (term0 n) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2299745 (n : nat) (h1 : (term0 n) = (real_of_num n)) : (real_of_num n) = (term0 n).
Proof. exact (SYM (@lem2299744 n h1)). Qed.
Lemma lem2299746 (n : nat) (h1 : (real_of_num n) = (term0 n)) : (real_of_num n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem2299747 (n : nat) (h1 : (real_of_num n) = (term0 n)) : (term0 n) = (real_of_num n).
Proof. exact (SYM (@lem2299746 n h1)). Qed.
Lemma lem2299748 (n : nat) : ((term0 n) = (real_of_num n)) = ((real_of_num n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (real_of_num n) => @lem2299745 n h1) (fun h1 : (real_of_num n) = (term0 n) => @lem2299747 n h1)). Qed.
Lemma lem2299749 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem2299748 n)). Qed.
Lemma lem2299750 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2299751 : term3 = term4.
Proof. exact (MK_COMB (@lem2299750) (@lem2299749)). Qed.
Lemma lem2299752 : term4.
Proof. exact (EQ_MP (@lem2299751) (@lem2271980)). Qed.
