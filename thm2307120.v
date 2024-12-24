Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2307120_term_abbrevs.
Require Import REAL_OF_NUM_CLAUSES_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307096 : term0.
Proof. exact (proj1 (@lem1486246)). Qed.
Lemma lem2307097 (m : nat) : term1 m.
Proof. exact (@lem2307096 m). Qed.
Lemma lem2307098 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2307099 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem2307098 m) (@lem2307097 m)). Qed.
Lemma lem2307100 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem2307099 m n). Qed.
Lemma lem2307101 (m : nat) (n : nat) : (term3 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2307102 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2307101 m n) (@lem2307100 m n)). Qed.
Lemma lem2307104 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307105 (m : nat) : (real_of_num m) = (term4 m).
Proof. exact (@lem2307104 m). Qed.
Lemma lem2307106 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307107 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem2307106) (@lem2307105 m)). Qed.
Lemma lem2307109 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307110 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = ((term4 m) = (term4 n)).
Proof. exact (MK_COMB (@lem2307107 m) (@lem2307109 n)). Qed.
Lemma lem2307112 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307113 (m : nat) (n : nat) : ((term4 m) = (term4 n)) = ((int_of_num m) = (int_of_num n)).
Proof. exact (@lem2307112 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307114 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = ((int_of_num m) = (int_of_num n)).
Proof. exact (TRANS (@lem2307110 m n) (@lem2307113 m n)). Qed.
Lemma lem2307115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307116 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem2307115) (@lem2307114 m n)). Qed.
Lemma lem2307117 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem2307118 (m : nat) (n : nat) : (((real_of_num m) = (real_of_num n)) = (m = n)) = (((int_of_num m) = (int_of_num n)) = (m = n)).
Proof. exact (MK_COMB (@lem2307116 m n) (@lem2307117 m n)). Qed.
Lemma lem2307119 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2307118 m n) (@lem2307102 m n)). Qed.
Lemma lem2307120 (m : nat) : term9 m.
Proof. exact (fun n : nat => @lem2307119 m n). Qed.
