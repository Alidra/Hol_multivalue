Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20440_term_abbrevs.
Require Import thm20426_spec.
Lemma lem20428 (x : Prop) (x1 : Prop) (x0 : Prop) : (term0 x x1 x0) = (term0 x x1 x0).
Proof. exact (eq_refl (term0 x x1 x0)). Qed.
Lemma lem20429 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = True) : (term1 x x1 x0 b) = (term2 x x1 x0).
Proof. exact (MK_COMB (@lem20428 x x1 x0) (@lem20426 b h1)). Qed.
Lemma lem20430 (x : Prop) (x1 : Prop) (x0 : Prop) : (term2 x x1 x0) = (term3 x x1 x0).
Proof. exact (eq_refl (term2 x x1 x0)). Qed.
Lemma lem20431 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) : (term4 x x1 x0 b) = (term4 x x1 x0 b).
Proof. exact (eq_refl (term4 x x1 x0 b)). Qed.
Lemma lem20432 (b : Prop) (x : Prop) (x1 : Prop) (x0 : Prop) : ((term1 x x1 x0 b) = (term2 x x1 x0)) = ((term1 x x1 x0 b) = (term3 x x1 x0)).
Proof. exact (MK_COMB (@lem20431 x x1 x0 b) (@lem20430 x x1 x0)). Qed.
Lemma lem20433 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : (term1 x x1 x0 b) = (term5 x x1 b x0).
Proof. exact (eq_refl (term1 x x1 x0 b)). Qed.
Lemma lem20434 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20435 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : (term4 x x1 x0 b) = (term6 x x1 b x0).
Proof. exact (MK_COMB (@lem20434) (@lem20433 x x1 b x0)). Qed.
Lemma lem20436 (x : Prop) (x1 : Prop) (x0 : Prop) : (term3 x x1 x0) = (term3 x x1 x0).
Proof. exact (eq_refl (term3 x x1 x0)). Qed.
Lemma lem20437 (b : Prop) (x : Prop) (x1 : Prop) (x0 : Prop) : ((term1 x x1 x0 b) = (term3 x x1 x0)) = ((term5 x x1 b x0) = (term3 x x1 x0)).
Proof. exact (MK_COMB (@lem20435 x x1 b x0) (@lem20436 x x1 x0)). Qed.
Lemma lem20438 (b : Prop) (x : Prop) (x1 : Prop) (x0 : Prop) : ((term1 x x1 x0 b) = (term2 x x1 x0)) = ((term5 x x1 b x0) = (term3 x x1 x0)).
Proof. exact (TRANS (@lem20432 b x x1 x0) (@lem20437 b x x1 x0)). Qed.
Lemma lem20439 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = True) : (term5 x x1 b x0) = (term3 x x1 x0).
Proof. exact (EQ_MP (@lem20438 b x x1 x0) (@lem20429 x x1 x0 b h1)). Qed.
Lemma lem20440 (x : Prop) (x1 : Prop) (x0 : Prop) (b : Prop) (h1 : b = True) : (term3 x x1 x0) = (term5 x x1 b x0).
Proof. exact (SYM (@lem20439 x x1 x0 b h1)). Qed.
