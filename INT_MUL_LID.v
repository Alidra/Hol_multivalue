Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_LID_term_abbrevs.
Require Import thm1338986_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305958 (x : int) : term0 x.
Proof. exact (@lem1338986 (real_of_int x)). Qed.
Lemma lem2305959 (x : int) : (term0 x) = ((term1 x) = (real_of_int x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305960 (x : int) : (term1 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2305959 x) (@lem2305958 x)). Qed.
Lemma lem2305962 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2305963 : term3 = term4.
Proof. exact (@lem2305962 term5). Qed.
Lemma lem2305964 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2305965 : term6 = term7.
Proof. exact (MK_COMB (@lem2305964) (@lem2305963)). Qed.
Lemma lem2305966 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2305967 (x : int) : (term1 x) = (term8 x).
Proof. exact (MK_COMB (@lem2305965) (@lem2305966 x)). Qed.
Lemma lem2305969 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305970 (x : int) : (term8 x) = (term11 x).
Proof. exact (@lem2305969 term12 x). Qed.
Lemma lem2305971 (x : int) : (term1 x) = (term11 x).
Proof. exact (TRANS (@lem2305967 x) (@lem2305970 x)). Qed.
Lemma lem2305972 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305973 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2305972) (@lem2305971 x)). Qed.
Lemma lem2305974 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2305975 (x : int) : ((term1 x) = (real_of_int x)) = ((term11 x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2305973 x) (@lem2305974 x)). Qed.
Lemma lem2305977 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305978 (x : int) : ((term11 x) = (real_of_int x)) = ((term15 x) = x).
Proof. exact (@lem2305977 (term15 x) x). Qed.
Lemma lem2305979 (x : int) : ((term1 x) = (real_of_int x)) = ((term15 x) = x).
Proof. exact (TRANS (@lem2305975 x) (@lem2305978 x)). Qed.
Lemma lem2305980 (x : int) : (term15 x) = x.
Proof. exact (EQ_MP (@lem2305979 x) (@lem2305960 x)). Qed.
Lemma lem2305981 : term16.
Proof. exact (fun x : int => @lem2305980 x). Qed.
