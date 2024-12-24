Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_SUB_term_abbrevs.
Require Import REAL_NEG_SUB_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306697 (x : int) : term0 x.
Proof. exact (@lem1374337 (real_of_int x)). Qed.
Lemma lem2306698 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306699 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306698 x) (@lem2306697 x)). Qed.
Lemma lem2306700 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306699 x (real_of_int y)). Qed.
Lemma lem2306701 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term4 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306702 (y : int) (x : int) : (term3 x y) = (term4 y x).
Proof. exact (EQ_MP (@lem2306701 y x) (@lem2306700 x y)). Qed.
Lemma lem2306704 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2306705 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2306706 (x : int) (y : int) : (term3 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2306705) (@lem2306704 x y)). Qed.
Lemma lem2306708 (x : int) : (term7 x) = (term8 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306709 (x : int) (y : int) : (term6 x y) = (term9 x y).
Proof. exact (@lem2306708 (int_sub x y)). Qed.
Lemma lem2306710 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (TRANS (@lem2306706 x y) (@lem2306709 x y)). Qed.
Lemma lem2306711 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306712 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (MK_COMB (@lem2306711) (@lem2306710 x y)). Qed.
Lemma lem2306714 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2306715 (y : int) (x : int) : (term4 y x) = (term5 y x).
Proof. exact (@lem2306714 y x). Qed.
Lemma lem2306716 (y : int) (x : int) : ((term3 x y) = (term4 y x)) = ((term9 x y) = (term5 y x)).
Proof. exact (MK_COMB (@lem2306712 x y) (@lem2306715 y x)). Qed.
Lemma lem2306718 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306719 (y : int) (x : int) : ((term9 x y) = (term5 y x)) = ((term12 x y) = (int_sub y x)).
Proof. exact (@lem2306718 (term12 x y) (int_sub y x)). Qed.
Lemma lem2306720 (y : int) (x : int) : ((term3 x y) = (term4 y x)) = ((term12 x y) = (int_sub y x)).
Proof. exact (TRANS (@lem2306716 y x) (@lem2306719 y x)). Qed.
Lemma lem2306721 (y : int) (x : int) : (term12 x y) = (int_sub y x).
Proof. exact (EQ_MP (@lem2306720 y x) (@lem2306702 y x)). Qed.
Lemma lem2306722 (x : int) : term13 x.
Proof. exact (fun y : int => @lem2306721 y x). Qed.
Lemma lem2306723 : term14.
Proof. exact (fun x : int => @lem2306722 x). Qed.
