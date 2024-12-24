Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_NEGTOTAL_term_abbrevs.
Require Import REAL_LE_NEGTOTAL_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302999 (x : int) : term0 x.
Proof. exact (@lem1382820 (real_of_int x)). Qed.
Lemma lem2303000 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303001 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303000 x) (@lem2302999 x)). Qed.
Lemma lem2303003 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303004 : term3 = term4.
Proof. exact (@lem2303003 (NUMERAL 0)). Qed.
Lemma lem2303005 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303006 : term5 = term6.
Proof. exact (MK_COMB (@lem2303005) (@lem2303004)). Qed.
Lemma lem2303007 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2303008 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2303006) (@lem2303007 x)). Qed.
Lemma lem2303010 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303011 (x : int) : (term8 x) = (term10 x).
Proof. exact (@lem2303010 term11 x). Qed.
Lemma lem2303012 (x : int) : (term7 x) = (term10 x).
Proof. exact (TRANS (@lem2303008 x) (@lem2303011 x)). Qed.
Lemma lem2303013 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2303014 (x : int) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem2303013) (@lem2303012 x)). Qed.
Lemma lem2303016 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303017 : term3 = term4.
Proof. exact (@lem2303016 (NUMERAL 0)). Qed.
Lemma lem2303018 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303019 : term5 = term6.
Proof. exact (MK_COMB (@lem2303018) (@lem2303017)). Qed.
Lemma lem2303021 (x : int) : (term14 x) = (term15 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2303022 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2303019) (@lem2303021 x)). Qed.
Lemma lem2303024 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303025 (x : int) : (term17 x) = (term18 x).
Proof. exact (@lem2303024 term11 (int_neg x)). Qed.
Lemma lem2303026 (x : int) : (term16 x) = (term18 x).
Proof. exact (TRANS (@lem2303022 x) (@lem2303025 x)). Qed.
Lemma lem2303027 (x : int) : (term1 x) = (term19 x).
Proof. exact (MK_COMB (@lem2303014 x) (@lem2303026 x)). Qed.
Lemma lem2303028 (x : int) : term19 x.
Proof. exact (EQ_MP (@lem2303027 x) (@lem2303001 x)). Qed.
Lemma lem2303029 : term20.
Proof. exact (fun x : int => @lem2303028 x). Qed.
