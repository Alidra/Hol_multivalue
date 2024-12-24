Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_NEGL_term_abbrevs.
Require Import REAL_LE_NEGL_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302945 (x : int) : term0 x.
Proof. exact (@lem1506376 (real_of_int x)). Qed.
Lemma lem2302946 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302947 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2302946 x) (@lem2302945 x)). Qed.
Lemma lem2302949 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2302950 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302951 (x : int) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem2302950) (@lem2302949 x)). Qed.
Lemma lem2302952 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2302953 (x : int) : (term1 x) = (term7 x).
Proof. exact (MK_COMB (@lem2302951 x) (@lem2302952 x)). Qed.
Lemma lem2302955 (x : int) (y : int) : (term8 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302956 (x : int) : (term7 x) = (term9 x).
Proof. exact (@lem2302955 (int_neg x) x). Qed.
Lemma lem2302957 (x : int) : (term1 x) = (term9 x).
Proof. exact (TRANS (@lem2302953 x) (@lem2302956 x)). Qed.
Lemma lem2302958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302959 (x : int) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem2302958) (@lem2302957 x)). Qed.
Lemma lem2302961 (n : nat) : (real_of_num n) = (term12 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302962 : term13 = term14.
Proof. exact (@lem2302961 (NUMERAL 0)). Qed.
Lemma lem2302963 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302964 : term15 = term16.
Proof. exact (MK_COMB (@lem2302963) (@lem2302962)). Qed.
Lemma lem2302965 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2302966 (x : int) : (term2 x) = (term17 x).
Proof. exact (MK_COMB (@lem2302964) (@lem2302965 x)). Qed.
Lemma lem2302968 (x : int) (y : int) : (term8 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302969 (x : int) : (term17 x) = (term18 x).
Proof. exact (@lem2302968 term19 x). Qed.
Lemma lem2302970 (x : int) : (term2 x) = (term18 x).
Proof. exact (TRANS (@lem2302966 x) (@lem2302969 x)). Qed.
Lemma lem2302971 (x : int) : ((term1 x) = (term2 x)) = ((term9 x) = (term18 x)).
Proof. exact (MK_COMB (@lem2302959 x) (@lem2302970 x)). Qed.
Lemma lem2302972 (x : int) : (term9 x) = (term18 x).
Proof. exact (EQ_MP (@lem2302971 x) (@lem2302947 x)). Qed.
Lemma lem2302973 : term20.
Proof. exact (fun x : int => @lem2302972 x). Qed.
