Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm113_term_abbrevs.
Require Import EXISTS_UNIQUE_DEF_spec.
Require Import thm37_spec.
Lemma lem100 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem101 {A : Type'} (P : A -> Prop) : (@ex1 A P) = (term0 A P).
Proof. exact (MK_COMB (@lem99 A) (@lem100 A P)). Qed.
Lemma lem102 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem103 {A : Type'} (P : A -> Prop) : (term2 A P) = (term2 A P).
Proof. exact (eq_refl (term2 A P)). Qed.
Lemma lem104 {A : Type'} (P : A -> Prop) : ((@ex1 A P) = (term0 A P)) = ((@ex1 A P) = (term1 A P)).
Proof. exact (MK_COMB (@lem103 A P) (@lem102 A P)). Qed.
Lemma lem105 {A : Type'} (P : A -> Prop) : (@ex1 A P) = (term1 A P).
Proof. exact (EQ_MP (@lem104 A P) (@lem101 A P)). Qed.
Lemma lem108 {A : Type'} (P : A -> Prop) : term3 A P.
Proof. exact (@lem37 (@ex1 A P) (term1 A P)). Qed.
Lemma lem109 {A : Type'} (P : A -> Prop) : term4 A P.
Proof. exact (@lem108 A P (@lem105 A P)). Qed.
Lemma lem110 {A : Type'} (P : A -> Prop) (h1 : @ex1 A P) : @ex1 A P.
Proof. exact (h1). Qed.
Lemma lem111 {A : Type'} (P : A -> Prop) (h1 : @ex1 A P) : term1 A P.
Proof. exact (@lem109 A P (@lem110 A P h1)). Qed.
Lemma lem112 {A : Type'} (P : A -> Prop) (h1 : @ex1 A P) : ex P.
Proof. exact (proj1 (@lem111 A P h1)). Qed.
Lemma lem113 {A : Type'} (P : A -> Prop) : term5 A P.
Proof. exact (fun h0 : @ex1 A P => @lem112 A P h0). Qed.
