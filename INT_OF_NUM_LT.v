Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_LT_term_abbrevs.
Require Import REAL_OF_NUM_LT_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2307223 (m : nat) : term0 m.
Proof. exact (@lem1483667 m). Qed.
Lemma lem2307224 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2307225 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2307224 m) (@lem2307223 m)). Qed.
Lemma lem2307226 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2307225 m n). Qed.
Lemma lem2307227 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2307228 (m : nat) (n : nat) : (term3 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2307227 m n) (@lem2307226 m n)). Qed.
Lemma lem2307230 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307231 (m : nat) : (real_of_num m) = (term4 m).
Proof. exact (@lem2307230 m). Qed.
Lemma lem2307232 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2307233 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem2307232) (@lem2307231 m)). Qed.
Lemma lem2307235 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307236 (m : nat) (n : nat) : (term3 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem2307233 m) (@lem2307235 n)). Qed.
Lemma lem2307238 (x : int) (y : int) : (term8 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2307239 (m : nat) (n : nat) : (term7 m n) = (term9 m n).
Proof. exact (@lem2307238 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307240 (m : nat) (n : nat) : (term3 m n) = (term9 m n).
Proof. exact (TRANS (@lem2307236 m n) (@lem2307239 m n)). Qed.
Lemma lem2307241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307242 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem2307241) (@lem2307240 m n)). Qed.
Lemma lem2307243 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem2307244 (m : nat) (n : nat) : ((term3 m n) = (Peano.lt m n)) = ((term9 m n) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem2307242 m n) (@lem2307243 m n)). Qed.
Lemma lem2307245 (m : nat) (n : nat) : (term9 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2307244 m n) (@lem2307228 m n)). Qed.
Lemma lem2307246 (m : nat) : term12 m.
Proof. exact (fun n : nat => @lem2307245 m n). Qed.
Lemma lem2307247 : term13.
Proof. exact (fun m : nat => @lem2307246 m). Qed.
