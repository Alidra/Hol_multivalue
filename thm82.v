Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm82_term_abbrevs.
Require Import F_DEF_spec.
Require Import thm32_spec.
Require Import thm62_spec.
Lemma lem70 (P : Prop) (h1 : ~ P) : ~ P.
Proof. exact (h1). Qed.
Lemma lem71 (P : Prop) : (~ P) = (P -> False).
Proof. exact (@lem62 P). Qed.
Lemma lem72 (P : Prop) (h1 : ~ P) : P -> False.
Proof. exact (EQ_MP (@lem71 P) (@lem70 P h1)). Qed.
Lemma lem73 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem74 (h1 : False) : term0.
Proof. exact (EQ_MP (@lem55) (@lem73 h1)). Qed.
Lemma lem75 (P : Prop) (h1 : False) : term1 P.
Proof. exact (@lem74 h1 P). Qed.
Lemma lem76 (P : Prop) : (term1 P) = P.
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem77 (P : Prop) (h1 : False) : P.
Proof. exact (EQ_MP (@lem76 P) (@lem75 P h1)). Qed.
Lemma lem78 (P : Prop) : False -> P.
Proof. exact (fun h0 : False => @lem77 P h0). Qed.
Lemma lem79 (P : Prop) (h1 : ~ P) : term2 P.
Proof. exact (conj (@lem72 P h1) (@lem78 P)). Qed.
Lemma lem80 (P : Prop) : (term2 P) = (P = False).
Proof. exact (@lem32 P False). Qed.
Lemma lem81 (P : Prop) (h1 : ~ P) : P = False.
Proof. exact (EQ_MP (@lem80 P) (@lem79 P h1)). Qed.
Lemma lem82 (P : Prop) : term3 P.
Proof. exact (fun h0 : ~ P => @lem81 P h0). Qed.
