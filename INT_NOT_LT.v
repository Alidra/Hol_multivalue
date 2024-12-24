Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NOT_LT_term_abbrevs.
Require Import REAL_NOT_LT_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2306767 (x : int) : term0 x.
Proof. exact (@lem1376537 (real_of_int x)). Qed.
Lemma lem2306768 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306769 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306768 x) (@lem2306767 x)). Qed.
Lemma lem2306770 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306769 x (real_of_int y)). Qed.
Lemma lem2306771 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term4 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306772 (y : int) (x : int) : (term3 x y) = (term4 y x).
Proof. exact (EQ_MP (@lem2306771 y x) (@lem2306770 x y)). Qed.
Lemma lem2306774 (x : int) (y : int) : (term5 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306775 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2306776 (x : int) (y : int) : (term3 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2306775) (@lem2306774 x y)). Qed.
Lemma lem2306777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2306778 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2306777) (@lem2306776 x y)). Qed.
Lemma lem2306780 (x : int) (y : int) : (term4 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2306781 (y : int) (x : int) : (term4 y x) = (int_le y x).
Proof. exact (@lem2306780 y x). Qed.
Lemma lem2306782 (y : int) (x : int) : ((term3 x y) = (term4 y x)) = ((term6 x y) = (int_le y x)).
Proof. exact (MK_COMB (@lem2306778 x y) (@lem2306781 y x)). Qed.
Lemma lem2306783 (y : int) (x : int) : (term6 x y) = (int_le y x).
Proof. exact (EQ_MP (@lem2306782 y x) (@lem2306772 y x)). Qed.
Lemma lem2306784 (x : int) : term9 x.
Proof. exact (fun y : int => @lem2306783 y x). Qed.
Lemma lem2306785 : term10.
Proof. exact (fun x : int => @lem2306784 x). Qed.
