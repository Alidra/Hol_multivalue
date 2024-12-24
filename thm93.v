Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm93_term_abbrevs.
Require Import F_DEF_spec.
Require Import thm69_spec.
Lemma lem83 (P : Prop) (h1 : P) : P.
Proof. exact (h1). Qed.
Lemma lem84 (P : Prop) (h1 : P = False) : P = False.
Proof. exact (h1). Qed.
Lemma lem85 (P : Prop) (h1 : P) (h2 : P = False) : False.
Proof. exact (EQ_MP (@lem84 P h2) (@lem83 P h1)). Qed.
Lemma lem86 (P : Prop) (h1 : P) (h2 : P = False) : term0.
Proof. exact (EQ_MP (@lem55) (@lem85 P h1 h2)). Qed.
Lemma lem87 (P : Prop) (h1 : P) (h2 : P = False) : term1.
Proof. exact (@lem86 P h1 h2 False). Qed.
Lemma lem88 : term1 = False.
Proof. exact (eq_refl term1). Qed.
Lemma lem89 (P : Prop) (h1 : P) (h2 : P = False) : False.
Proof. exact (EQ_MP (@lem88) (@lem87 P h1 h2)). Qed.
Lemma lem90 (P : Prop) (h1 : P = False) : P -> False.
Proof. exact (fun h0 : P => @lem89 P h0 h1). Qed.
Lemma lem91 (P : Prop) : (P -> False) = (~ P).
Proof. exact (@lem69 P). Qed.
Lemma lem92 (P : Prop) (h1 : P = False) : ~ P.
Proof. exact (EQ_MP (@lem91 P) (@lem90 P h1)). Qed.
Lemma lem93 (P : Prop) : term2 P.
Proof. exact (fun h0 : P = False => @lem92 P h0). Qed.
