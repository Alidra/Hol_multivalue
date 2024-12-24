Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_SIMP_term_abbrevs.
Require Import thm32_spec.
Lemma lem1107 {A : Type'} (t : Prop) (h1 : term0 A t) : term0 A t.
Proof. exact (h1). Qed.
Lemma lem1108 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1109 {A : Type'} (t : Prop) (h1 : term0 A t) : t.
Proof. exact (ex_elim (@lem1107 A t h1) (fun x : A => fun h0 : term1 A t x => @lem1108 t h0)). Qed.
Lemma lem1110 {A : Type'} (t : Prop) : term2 A t.
Proof. exact (fun h0 : term0 A t => @lem1109 A t h0). Qed.
Lemma lem1111 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1112 {A : Type'} (t : Prop) (h1 : t) : term0 A t.
Proof. exact (ex_intro (term1 A t) (@el A) (@lem1111 t h1)). Qed.
Lemma lem1113 {A : Type'} (t : Prop) : term3 A t.
Proof. exact (fun h0 : t => @lem1112 A t h0). Qed.
Lemma lem1114 {A : Type'} (t : Prop) : term4 A t.
Proof. exact (conj (@lem1110 A t) (@lem1113 A t)). Qed.
Lemma lem1115 {A : Type'} (t : Prop) : (term4 A t) = ((term0 A t) = t).
Proof. exact (@lem32 (term0 A t) t). Qed.
Lemma lem1116 {A : Type'} (t : Prop) : (term0 A t) = t.
Proof. exact (EQ_MP (@lem1115 A t) (@lem1114 A t)). Qed.
Lemma lem1121 {A : Type'} : term5 A.
Proof. exact (fun t : Prop => @lem1116 A t). Qed.
