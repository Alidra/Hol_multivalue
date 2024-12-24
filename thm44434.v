Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm44434_term_abbrevs.
Lemma lem44426 {A B : Type'} (r : type1413 A B) : (term0 A B r) = ((term1 A B r) = r).
Proof. exact (@axiom_5 A B r). Qed.
Lemma lem44429 {A B : Type'} (r : type1413 A B) : (term0 A B r) = (term2 A B r).
Proof. exact (eq_refl (term0 A B r)). Qed.
Lemma lem44430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem44431 {A B : Type'} (r : type1413 A B) : (term3 A B r) = (term4 A B r).
Proof. exact (MK_COMB (@lem44430) (@lem44429 A B r)). Qed.
Lemma lem44432 {A B : Type'} (r : type1413 A B) : ((term1 A B r) = r) = ((term1 A B r) = r).
Proof. exact (eq_refl ((term1 A B r) = r)). Qed.
Lemma lem44433 {A B : Type'} (r : type1413 A B) : ((term0 A B r) = ((term1 A B r) = r)) = ((term2 A B r) = ((term1 A B r) = r)).
Proof. exact (MK_COMB (@lem44431 A B r) (@lem44432 A B r)). Qed.
Lemma lem44434 {A B : Type'} (r : type1413 A B) : (term2 A B r) = ((term1 A B r) = r).
Proof. exact (EQ_MP (@lem44433 A B r) (@lem44426 A B r)). Qed.
