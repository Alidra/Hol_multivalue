Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1317744_term_abbrevs.
Lemma lem1317736 (r : nadd -> Prop) : (term0 r) = ((term1 r) = r).
Proof. exact (@axiom_22 r). Qed.
Lemma lem1317739 (r : nadd -> Prop) : (term0 r) = (term2 r).
Proof. exact (eq_refl (term0 r)). Qed.
Lemma lem1317740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1317741 (r : nadd -> Prop) : (term3 r) = (term4 r).
Proof. exact (MK_COMB (@lem1317740) (@lem1317739 r)). Qed.
Lemma lem1317742 (r : nadd -> Prop) : ((term1 r) = r) = ((term1 r) = r).
Proof. exact (eq_refl ((term1 r) = r)). Qed.
Lemma lem1317743 (r : nadd -> Prop) : ((term0 r) = ((term1 r) = r)) = ((term2 r) = ((term1 r) = r)).
Proof. exact (MK_COMB (@lem1317741 r) (@lem1317742 r)). Qed.
Lemma lem1317744 (r : nadd -> Prop) : (term2 r) = ((term1 r) = r).
Proof. exact (EQ_MP (@lem1317743 r) (@lem1317736 r)). Qed.
