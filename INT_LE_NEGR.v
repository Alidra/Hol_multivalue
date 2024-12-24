Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_NEGR_term_abbrevs.
Require Import REAL_LE_NEGR_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302974 (x : int) : term0 x.
Proof. exact (@lem1506933 (real_of_int x)). Qed.
Lemma lem2302975 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302976 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2302975 x) (@lem2302974 x)). Qed.
Lemma lem2302978 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2302979 (x : int) : (term5 x) = (term5 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2302980 (x : int) : (term1 x) = (term6 x).
Proof. exact (MK_COMB (@lem2302979 x) (@lem2302978 x)). Qed.
Lemma lem2302982 (x : int) (y : int) : (term7 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302983 (x : int) : (term6 x) = (term8 x).
Proof. exact (@lem2302982 x (int_neg x)). Qed.
Lemma lem2302984 (x : int) : (term1 x) = (term8 x).
Proof. exact (TRANS (@lem2302980 x) (@lem2302983 x)). Qed.
Lemma lem2302985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302986 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2302985) (@lem2302984 x)). Qed.
Lemma lem2302988 (n : nat) : (real_of_num n) = (term11 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302989 : term12 = term13.
Proof. exact (@lem2302988 (NUMERAL 0)). Qed.
Lemma lem2302990 (x : int) : (term5 x) = (term5 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2302991 (x : int) : (term2 x) = (term14 x).
Proof. exact (MK_COMB (@lem2302990 x) (@lem2302989)). Qed.
Lemma lem2302993 (x : int) (y : int) : (term7 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302994 (x : int) : (term14 x) = (term15 x).
Proof. exact (@lem2302993 x term16). Qed.
Lemma lem2302995 (x : int) : (term2 x) = (term15 x).
Proof. exact (TRANS (@lem2302991 x) (@lem2302994 x)). Qed.
Lemma lem2302996 (x : int) : ((term1 x) = (term2 x)) = ((term8 x) = (term15 x)).
Proof. exact (MK_COMB (@lem2302986 x) (@lem2302995 x)). Qed.
Lemma lem2302997 (x : int) : (term8 x) = (term15 x).
Proof. exact (EQ_MP (@lem2302996 x) (@lem2302976 x)). Qed.
Lemma lem2302998 : term17.
Proof. exact (fun x : int => @lem2302997 x). Qed.
