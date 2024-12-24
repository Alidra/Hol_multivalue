Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2307012_term_abbrevs.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2306820_spec.
Lemma lem2306988 : term0.
Proof. exact (proj1 (@lem2306820)). Qed.
Lemma lem2306989 (m : nat) : term1 m.
Proof. exact (@lem2306988 m). Qed.
Lemma lem2306990 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2306991 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem2306990 m) (@lem2306989 m)). Qed.
Lemma lem2306992 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem2306991 m n). Qed.
Lemma lem2306993 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2306994 (m : nat) (n : nat) : (term4 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2306993 m n) (@lem2306992 m n)). Qed.
Lemma lem2306996 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306997 (m : nat) : (real_of_num m) = (term5 m).
Proof. exact (@lem2306996 m). Qed.
Lemma lem2306998 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2306999 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem2306998) (@lem2306997 m)). Qed.
Lemma lem2307001 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307002 (m : nat) (n : nat) : (term4 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem2306999 m) (@lem2307001 n)). Qed.
Lemma lem2307004 (x : int) (y : int) : (term9 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2307005 (m : nat) (n : nat) : (term8 m n) = (term10 m n).
Proof. exact (@lem2307004 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307006 (m : nat) (n : nat) : (term4 m n) = (term10 m n).
Proof. exact (TRANS (@lem2307002 m n) (@lem2307005 m n)). Qed.
Lemma lem2307007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307008 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem2307007) (@lem2307006 m n)). Qed.
Lemma lem2307009 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem2307010 (m : nat) (n : nat) : ((term4 m n) = (Peano.lt m n)) = ((term10 m n) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem2307008 m n) (@lem2307009 m n)). Qed.
Lemma lem2307011 (m : nat) (n : nat) : (term10 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2307010 m n) (@lem2306994 m n)). Qed.
Lemma lem2307012 (m : nat) : term13 m.
Proof. exact (fun n : nat => @lem2307011 m n). Qed.
