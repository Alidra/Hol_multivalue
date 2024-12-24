Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20262_term_abbrevs.
Require Import thm20236_spec.
Lemma lem20250 (x : Prop) (x1 : Prop) (x0 : Prop) : (term0 x x1 x0) = (term0 x x1 x0).
Proof. exact (eq_refl (term0 x x1 x0)). Qed.
Lemma lem20251 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = False) : (term1 x x1 x0 b) = (term2 x x1 x0).
Proof. exact (MK_COMB (@lem20250 x x1 x0) (@lem20236 b h1)). Qed.
Lemma lem20252 (x : Prop) (x1 : Prop) (x0 : Prop) : (term2 x x1 x0) = (term3 x x1 x0).
Proof. exact (eq_refl (term2 x x1 x0)). Qed.
Lemma lem20253 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) : (term4 x x1 x0 b) = (term4 x x1 x0 b).
Proof. exact (eq_refl (term4 x x1 x0 b)). Qed.
Lemma lem20254 (b : Prop) (x : Prop) (x1 : Prop) (x0 : Prop) : ((term1 x x1 x0 b) = (term2 x x1 x0)) = ((term1 x x1 x0 b) = (term3 x x1 x0)).
Proof. exact (MK_COMB (@lem20253 x x1 x0 b) (@lem20252 x x1 x0)). Qed.
Lemma lem20255 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : (term1 x x1 x0 b) = (term5 x x1 b x0).
Proof. exact (eq_refl (term1 x x1 x0 b)). Qed.
Lemma lem20256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20257 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : (term4 x x1 x0 b) = (term6 x x1 b x0).
Proof. exact (MK_COMB (@lem20256) (@lem20255 x x1 b x0)). Qed.
Lemma lem20258 (x : Prop) (x1 : Prop) (x0 : Prop) : (term3 x x1 x0) = (term3 x x1 x0).
Proof. exact (eq_refl (term3 x x1 x0)). Qed.
Lemma lem20259 (b : Prop) (x : Prop) (x1 : Prop) (x0 : Prop) : ((term1 x x1 x0 b) = (term3 x x1 x0)) = ((term5 x x1 b x0) = (term3 x x1 x0)).
Proof. exact (MK_COMB (@lem20257 x x1 b x0) (@lem20258 x x1 x0)). Qed.
Lemma lem20260 (b : Prop) (x : Prop) (x1 : Prop) (x0 : Prop) : ((term1 x x1 x0 b) = (term2 x x1 x0)) = ((term5 x x1 b x0) = (term3 x x1 x0)).
Proof. exact (TRANS (@lem20254 b x x1 x0) (@lem20259 b x x1 x0)). Qed.
Lemma lem20261 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = False) : (term5 x x1 b x0) = (term3 x x1 x0).
Proof. exact (EQ_MP (@lem20260 b x x1 x0) (@lem20251 x x1 x0 b h1)). Qed.
Lemma lem20262 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = False) : (term3 x x1 x0) = (term5 x x1 b x0).
Proof. exact (SYM (@lem20261 x x1 x0 b h1)). Qed.
