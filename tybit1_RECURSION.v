Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import tybit1_RECURSION_term_abbrevs.
Require Import thm7930003_spec.
Require Import thm7931296_spec.
Lemma lem7931310 {A Z : Type'} (f : type41 A Z) : term0 A Z f.
Proof. exact (@lem7930003 A Z f). Qed.
Lemma lem7931311 {A Z : Type'} (f : type41 A Z) : (term0 A Z f) = (term1 A Z f).
Proof. exact (eq_refl (term0 A Z f)). Qed.
Lemma lem7931312 {A Z : Type'} (f : type41 A Z) : term1 A Z f.
Proof. exact (EQ_MP (@lem7931311 A Z f) (@lem7931310 A Z f)). Qed.
Lemma lem7931313 {A Z : Type'} (f : type41 A Z) : (term2 A Z f) = (term2 A Z f).
Proof. exact (eq_refl (term2 A Z f)). Qed.
Lemma lem7931314 {A Z : Type'} (f : type41 A Z) : (term3 A Z f) = (term4 A Z f).
Proof. exact (MK_COMB (@lem7931313 A Z f) (@lem7931296 A)). Qed.
Lemma lem7931315 {A Z : Type'} (f : type41 A Z) : (term4 A Z f) = (term5 A Z f).
Proof. exact (eq_refl (term4 A Z f)). Qed.
Lemma lem7931316 {A Z : Type'} (f : type41 A Z) : (term6 A Z f) = (term6 A Z f).
Proof. exact (eq_refl (term6 A Z f)). Qed.
Lemma lem7931317 {A Z : Type'} (f : type41 A Z) : ((term3 A Z f) = (term4 A Z f)) = ((term3 A Z f) = (term5 A Z f)).
Proof. exact (MK_COMB (@lem7931316 A Z f) (@lem7931315 A Z f)). Qed.
Lemma lem7931318 {A Z : Type'} (f : type41 A Z) : (term3 A Z f) = (term1 A Z f).
Proof. exact (eq_refl (term3 A Z f)). Qed.
Lemma lem7931319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7931320 {A Z : Type'} (f : type41 A Z) : (term6 A Z f) = (term7 A Z f).
Proof. exact (MK_COMB (@lem7931319) (@lem7931318 A Z f)). Qed.
Lemma lem7931321 {A Z : Type'} (f : type41 A Z) : (term5 A Z f) = (term5 A Z f).
Proof. exact (eq_refl (term5 A Z f)). Qed.
Lemma lem7931322 {A Z : Type'} (f : type41 A Z) : ((term3 A Z f) = (term5 A Z f)) = ((term1 A Z f) = (term5 A Z f)).
Proof. exact (MK_COMB (@lem7931320 A Z f) (@lem7931321 A Z f)). Qed.
Lemma lem7931323 {A Z : Type'} (f : type41 A Z) : ((term3 A Z f) = (term4 A Z f)) = ((term1 A Z f) = (term5 A Z f)).
Proof. exact (TRANS (@lem7931317 A Z f) (@lem7931322 A Z f)). Qed.
Lemma lem7931324 {A Z : Type'} (f : type41 A Z) : (term1 A Z f) = (term5 A Z f).
Proof. exact (EQ_MP (@lem7931323 A Z f) (@lem7931314 A Z f)). Qed.
Lemma lem7931325 {A Z : Type'} (f : type41 A Z) : term5 A Z f.
Proof. exact (EQ_MP (@lem7931324 A Z f) (@lem7931312 A Z f)). Qed.
Lemma lem7931326 {A Z : Type'} : term8 A Z.
Proof. exact (fun f : type41 A Z => @lem7931325 A Z f). Qed.
