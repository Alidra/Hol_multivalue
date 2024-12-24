Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2307093_term_abbrevs.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299930_spec.
Require Import thm2299931_spec.
Require Import thm2306817_spec.
Lemma lem2307069 : term0.
Proof. exact (proj1 (@lem2306817)). Qed.
Lemma lem2307070 (m : nat) : term1 m.
Proof. exact (@lem2307069 m). Qed.
Lemma lem2307071 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2307072 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem2307071 m) (@lem2307070 m)). Qed.
Lemma lem2307073 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem2307072 m n). Qed.
Lemma lem2307074 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (Peano.ge m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2307075 (m : nat) (n : nat) : (term4 m n) = (Peano.ge m n).
Proof. exact (EQ_MP (@lem2307074 m n) (@lem2307073 m n)). Qed.
Lemma lem2307077 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307078 (m : nat) : (real_of_num m) = (term5 m).
Proof. exact (@lem2307077 m). Qed.
Lemma lem2307079 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2307080 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem2307079) (@lem2307078 m)). Qed.
Lemma lem2307082 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307083 (m : nat) (n : nat) : (term4 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem2307080 m) (@lem2307082 n)). Qed.
Lemma lem2307085 (x : int) (y : int) : (term9 x y) = (int_ge x y).
Proof. exact (EQ_MP (@lem2299931 x y) (@lem2299930 x y)). Qed.
Lemma lem2307086 (m : nat) (n : nat) : (term8 m n) = (term10 m n).
Proof. exact (@lem2307085 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307087 (m : nat) (n : nat) : (term4 m n) = (term10 m n).
Proof. exact (TRANS (@lem2307083 m n) (@lem2307086 m n)). Qed.
Lemma lem2307088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307089 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem2307088) (@lem2307087 m n)). Qed.
Lemma lem2307090 (m : nat) (n : nat) : (Peano.ge m n) = (Peano.ge m n).
Proof. exact (eq_refl (Peano.ge m n)). Qed.
Lemma lem2307091 (m : nat) (n : nat) : ((term4 m n) = (Peano.ge m n)) = ((term10 m n) = (Peano.ge m n)).
Proof. exact (MK_COMB (@lem2307089 m n) (@lem2307090 m n)). Qed.
Lemma lem2307092 (m : nat) (n : nat) : (term10 m n) = (Peano.ge m n).
Proof. exact (EQ_MP (@lem2307091 m n) (@lem2307075 m n)). Qed.
Lemma lem2307093 (m : nat) : term13 m.
Proof. exact (fun n : nat => @lem2307092 m n). Qed.
