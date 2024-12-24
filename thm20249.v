Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20249_term_abbrevs.
Require Import thm20235_spec.
Lemma lem20237 (x : Prop) (x1 : Prop) (x0 : Prop) : (term0 x x1 x0) = (term0 x x1 x0).
Proof. exact (eq_refl (term0 x x1 x0)). Qed.
Lemma lem20238 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = True) : (term1 x x1 x0 b) = (term2 x x1 x0).
Proof. exact (MK_COMB (@lem20237 x x1 x0) (@lem20235 b h1)). Qed.
Lemma lem20239 (x : Prop) (x1 : Prop) (x0 : Prop) : (term2 x x1 x0) = (term3 x x1 x0).
Proof. exact (eq_refl (term2 x x1 x0)). Qed.
Lemma lem20240 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) : (term4 x x1 x0 b) = (term4 x x1 x0 b).
Proof. exact (eq_refl (term4 x x1 x0 b)). Qed.
Lemma lem20241 (b : Prop) (x : Prop) (x1 : Prop) (x0 : Prop) : ((term1 x x1 x0 b) = (term2 x x1 x0)) = ((term1 x x1 x0 b) = (term3 x x1 x0)).
Proof. exact (MK_COMB (@lem20240 x x1 x0 b) (@lem20239 x x1 x0)). Qed.
Lemma lem20242 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : (term1 x x1 x0 b) = (term5 x x1 b x0).
Proof. exact (eq_refl (term1 x x1 x0 b)). Qed.
Lemma lem20243 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20244 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : (term4 x x1 x0 b) = (term6 x x1 b x0).
Proof. exact (MK_COMB (@lem20243) (@lem20242 x x1 b x0)). Qed.
Lemma lem20245 (x : Prop) (x1 : Prop) (x0 : Prop) : (term3 x x1 x0) = (term3 x x1 x0).
Proof. exact (eq_refl (term3 x x1 x0)). Qed.
Lemma lem20246 (b : Prop) (x : Prop) (x1 : Prop) (x0 : Prop) : ((term1 x x1 x0 b) = (term3 x x1 x0)) = ((term5 x x1 b x0) = (term3 x x1 x0)).
Proof. exact (MK_COMB (@lem20244 x x1 b x0) (@lem20245 x x1 x0)). Qed.
Lemma lem20247 (b : Prop) (x : Prop) (x1 : Prop) (x0 : Prop) : ((term1 x x1 x0 b) = (term2 x x1 x0)) = ((term5 x x1 b x0) = (term3 x x1 x0)).
Proof. exact (TRANS (@lem20241 b x x1 x0) (@lem20246 b x x1 x0)). Qed.
Lemma lem20248 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = True) : (term5 x x1 b x0) = (term3 x x1 x0).
Proof. exact (EQ_MP (@lem20247 b x x1 x0) (@lem20238 x x1 x0 b h1)). Qed.
Lemma lem20249 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = True) : (term3 x x1 x0) = (term5 x x1 b x0).
Proof. exact (SYM (@lem20248 x x1 x0 b h1)). Qed.
