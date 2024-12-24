Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21433_term_abbrevs.
Require Import thm21399_spec.
Lemma lem21421 (b : Prop) : (term0 b) = (term0 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem21422 (b : Prop) (a : Prop) (h1 : a = False) : (term1 b a) = (term2 b).
Proof. exact (MK_COMB (@lem21421 b) (@lem21399 a h1)). Qed.
Lemma lem21423 (b : Prop) : (term2 b) = ((False -> b) = (term3 b)).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem21424 (b : Prop) (a : Prop) : (term4 b a) = (term4 b a).
Proof. exact (eq_refl (term4 b a)). Qed.
Lemma lem21425 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = ((term1 b a) = ((False -> b) = (term3 b))).
Proof. exact (MK_COMB (@lem21424 b a) (@lem21423 b)). Qed.
Lemma lem21426 (a : Prop) (b : Prop) : (term1 b a) = ((a -> b) = (term5 a b)).
Proof. exact (eq_refl (term1 b a)). Qed.
Lemma lem21427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21428 (a : Prop) (b : Prop) : (term4 b a) = (term6 a b).
Proof. exact (MK_COMB (@lem21427) (@lem21426 a b)). Qed.
Lemma lem21429 (b : Prop) : ((False -> b) = (term3 b)) = ((False -> b) = (term3 b)).
Proof. exact (eq_refl ((False -> b) = (term3 b))). Qed.
Lemma lem21430 (a : Prop) (b : Prop) : ((term1 b a) = ((False -> b) = (term3 b))) = (((a -> b) = (term5 a b)) = ((False -> b) = (term3 b))).
Proof. exact (MK_COMB (@lem21428 a b) (@lem21429 b)). Qed.
Lemma lem21431 (a : Prop) (b : Prop) : ((term1 b a) = (term2 b)) = (((a -> b) = (term5 a b)) = ((False -> b) = (term3 b))).
Proof. exact (TRANS (@lem21425 a b) (@lem21430 a b)). Qed.
Lemma lem21432 (b : Prop) (a : Prop) (h1 : a = False) : ((a -> b) = (term5 a b)) = ((False -> b) = (term3 b)).
Proof. exact (EQ_MP (@lem21431 a b) (@lem21422 b a h1)). Qed.
Lemma lem21433 (b : Prop) (a : Prop) (h1 : a = False) : ((False -> b) = (term3 b)) = ((a -> b) = (term5 a b)).
Proof. exact (SYM (@lem21432 b a h1)). Qed.
