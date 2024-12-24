Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_SIMP_term_abbrevs.
Require Import thm32_spec.
Lemma lem1072 {A : Type'} (t : Prop) (h1 : term0 A t) : term0 A t.
Proof. exact (h1). Qed.
Lemma lem1073 {A : Type'} (_13 : A) (t : Prop) (h1 : term0 A t) : term1 A t _13.
Proof. exact (@lem1072 A t h1 _13). Qed.
Lemma lem1074 {A : Type'} (_13 : A) (t : Prop) : (term1 A t _13) = t.
Proof. exact (eq_refl (term1 A t _13)). Qed.
Lemma lem1075 {A : Type'} (t : Prop) (h1 : term0 A t) : t.
Proof. exact (EQ_MP (@lem1074 A (@el A) t) (@lem1073 A (@el A) t h1)). Qed.
Lemma lem1079 {A : Type'} (t : Prop) (h1 : term0 A t) : (term0 A t) = t.
Proof. exact (prop_ext (fun h2 : term0 A t => @lem1075 A t h1) (fun h2 : t => @lem1072 A t h1)). Qed.
Lemma lem1080 {A : Type'} (t : Prop) (h1 : term0 A t) : t.
Proof. exact (EQ_MP (@lem1079 A t h1) (@lem1072 A t h1)). Qed.
Lemma lem1081 {A : Type'} (t : Prop) : term2 A t.
Proof. exact (fun h0 : term0 A t => @lem1080 A t h0). Qed.
Lemma lem1082 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem1087 {A : Type'} (t : Prop) (h1 : t) : term0 A t.
Proof. exact (fun x : A => @lem1082 t h1). Qed.
Lemma lem1088 {A : Type'} (t : Prop) : term3 A t.
Proof. exact (fun h0 : t => @lem1087 A t h0). Qed.
Lemma lem1089 {A : Type'} (t : Prop) : term4 A t.
Proof. exact (conj (@lem1081 A t) (@lem1088 A t)). Qed.
Lemma lem1090 {A : Type'} (t : Prop) : (term4 A t) = ((term0 A t) = t).
Proof. exact (@lem32 (term0 A t) t). Qed.
Lemma lem1091 {A : Type'} (t : Prop) : (term0 A t) = t.
Proof. exact (EQ_MP (@lem1090 A t) (@lem1089 A t)). Qed.
Lemma lem1096 {A : Type'} : term5 A.
Proof. exact (fun t : Prop => @lem1091 A t). Qed.
