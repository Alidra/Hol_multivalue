Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299969_term_abbrevs.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2299952 (n : nat) : (real_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2299953 : term1 = term2.
Proof. exact (@lem2299952 (NUMERAL 0)). Qed.
Lemma lem2299954 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2299955 : term3 = term4.
Proof. exact (MK_COMB (@lem2299954) (@lem2299953)). Qed.
Lemma lem2299957 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2299958 : term4 = term7.
Proof. exact (@lem2299957 term8). Qed.
Lemma lem2299959 : term3 = term7.
Proof. exact (TRANS (@lem2299955) (@lem2299958)). Qed.
Lemma lem2299960 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2299961 : term9 = term10.
Proof. exact (MK_COMB (@lem2299960) (@lem2299959)). Qed.
Lemma lem2299963 (n : nat) : (real_of_num n) = (term0 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2299964 : term1 = term2.
Proof. exact (@lem2299963 (NUMERAL 0)). Qed.
Lemma lem2299965 : (term3 = term1) = (term7 = term2).
Proof. exact (MK_COMB (@lem2299961) (@lem2299964)). Qed.
Lemma lem2299967 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2299968 : (term7 = term2) = (term11 = term8).
Proof. exact (@lem2299967 term11 term8). Qed.
Lemma lem2299969 : (term3 = term1) = (term11 = term8).
Proof. exact (TRANS (@lem2299965) (@lem2299968)). Qed.
