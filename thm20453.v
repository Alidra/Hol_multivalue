Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20453_term_abbrevs.
Require Import thm20427_spec.
Lemma lem20441 (x : Prop) (x1 : Prop) (x0 : Prop) : (term0 x x1 x0) = (term0 x x1 x0).
Proof. exact (eq_refl (term0 x x1 x0)). Qed.
Lemma lem20442 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = False) : (term1 x x1 x0 b) = (term2 x x1 x0).
Proof. exact (MK_COMB (@lem20441 x x1 x0) (@lem20427 b h1)). Qed.
Lemma lem20443 (x : Prop) (x1 : Prop) (x0 : Prop) : (term2 x x1 x0) = (term3 x x1 x0).
Proof. exact (eq_refl (term2 x x1 x0)). Qed.
Lemma lem20444 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) : (term4 x x1 x0 b) = (term4 x x1 x0 b).
Proof. exact (eq_refl (term4 x x1 x0 b)). Qed.
Lemma lem20445 (b : Prop) (x : Prop) (x1 : Prop) (x0 : Prop) : ((term1 x x1 x0 b) = (term2 x x1 x0)) = ((term1 x x1 x0 b) = (term3 x x1 x0)).
Proof. exact (MK_COMB (@lem20444 x x1 x0 b) (@lem20443 x x1 x0)). Qed.
Lemma lem20446 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : (term1 x x1 x0 b) = (term5 x x1 b x0).
Proof. exact (eq_refl (term1 x x1 x0 b)). Qed.
Lemma lem20447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20448 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : (term4 x x1 x0 b) = (term6 x x1 b x0).
Proof. exact (MK_COMB (@lem20447) (@lem20446 x x1 b x0)). Qed.
Lemma lem20449 (x : Prop) (x1 : Prop) (x0 : Prop) : (term3 x x1 x0) = (term3 x x1 x0).
Proof. exact (eq_refl (term3 x x1 x0)). Qed.
Lemma lem20450 (b : Prop) (x : Prop) (x1 : Prop) (x0 : Prop) : ((term1 x x1 x0 b) = (term3 x x1 x0)) = ((term5 x x1 b x0) = (term3 x x1 x0)).
Proof. exact (MK_COMB (@lem20448 x x1 b x0) (@lem20449 x x1 x0)). Qed.
Lemma lem20451 (b : Prop) (x : Prop) (x1 : Prop) (x0 : Prop) : ((term1 x x1 x0 b) = (term2 x x1 x0)) = ((term5 x x1 b x0) = (term3 x x1 x0)).
Proof. exact (TRANS (@lem20445 b x x1 x0) (@lem20450 b x x1 x0)). Qed.
Lemma lem20452 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = False) : (term5 x x1 b x0) = (term3 x x1 x0).
Proof. exact (EQ_MP (@lem20451 b x x1 x0) (@lem20442 x x1 x0 b h1)). Qed.
Lemma lem20453 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = False) : (term3 x x1 x0) = (term5 x x1 b x0).
Proof. exact (SYM (@lem20452 x x1 x0 b h1)). Qed.
