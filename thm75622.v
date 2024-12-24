Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm75622_term_abbrevs.
Require Import num_INDUCTION_spec.
Lemma lem75609 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem75610 (P : nat -> Prop) (h1 : term0) : term1 P.
Proof. exact (@lem75609 h1 P). Qed.
Lemma lem75611 (P : nat -> Prop) : (term1 P) = (term2 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem75612 (P : nat -> Prop) (h1 : term0) : term2 P.
Proof. exact (EQ_MP (@lem75611 P) (@lem75610 P h1)). Qed.
Lemma lem75613 (P : nat -> Prop) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem75614 (P : nat -> Prop) (h1 : term0) (h2 : term3 P) : term4 P.
Proof. exact (@lem75612 P h1 (@lem75613 P h2)). Qed.
Lemma lem75615 (P : nat -> Prop) (h1 : term3 P) : term5 P.
Proof. exact (fun h0 : term0 => @lem75614 P h0 h1). Qed.
Lemma lem75616 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem75617 (P : nat -> Prop) (h1 : term0) (h2 : term3 P) : term4 P.
Proof. exact (@lem75615 P h2 (@lem75616 h1)). Qed.
Lemma lem75618 (P : nat -> Prop) (h1 : term0) : term2 P.
Proof. exact (fun h0 : term3 P => @lem75617 P h1 h0). Qed.
Lemma lem75619 (h1 : term0) : term0.
Proof. exact (fun P : nat -> Prop => @lem75618 P h1). Qed.
Lemma lem75620 : term6.
Proof. exact (fun h0 : term0 => @lem75619 h0). Qed.
Lemma lem75621 : term0.
Proof. exact (@lem75620 (@lem75586)). Qed.
Lemma lem75622 (P : nat -> Prop) : term1 P.
Proof. exact (@lem75621 P). Qed.
