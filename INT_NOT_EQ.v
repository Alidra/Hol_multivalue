Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NOT_EQ_term_abbrevs.
Require Import REAL_NOT_EQ_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306724 (x : int) : term0 x.
Proof. exact (@lem1495214 (real_of_int x)). Qed.
Lemma lem2306725 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306726 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306725 x) (@lem2306724 x)). Qed.
Lemma lem2306727 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306726 x (real_of_int y)). Qed.
Lemma lem2306728 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term4 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306729 (y : int) (x : int) : (term3 x y) = (term4 y x).
Proof. exact (EQ_MP (@lem2306728 y x) (@lem2306727 x y)). Qed.
Lemma lem2306731 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306732 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2306733 (x : int) (y : int) : (term3 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem2306732) (@lem2306731 x y)). Qed.
Lemma lem2306734 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2306735 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2306734) (@lem2306733 x y)). Qed.
Lemma lem2306737 (x : int) (y : int) : (term8 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2306739 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2306738) (@lem2306737 x y)). Qed.
Lemma lem2306741 (x : int) (y : int) : (term8 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306742 (y : int) (x : int) : (term8 y x) = (int_lt y x).
Proof. exact (@lem2306741 y x). Qed.
Lemma lem2306743 (y : int) (x : int) : (term4 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem2306739 x y) (@lem2306742 y x)). Qed.
Lemma lem2306744 (y : int) (x : int) : ((term3 x y) = (term4 y x)) = ((term5 x y) = (term11 y x)).
Proof. exact (MK_COMB (@lem2306735 x y) (@lem2306743 y x)). Qed.
Lemma lem2306745 (y : int) (x : int) : (term5 x y) = (term11 y x).
Proof. exact (EQ_MP (@lem2306744 y x) (@lem2306729 y x)). Qed.
Lemma lem2306746 (x : int) : term12 x.
Proof. exact (fun y : int => @lem2306745 y x). Qed.
Lemma lem2306747 : term13.
Proof. exact (fun x : int => @lem2306746 x). Qed.
