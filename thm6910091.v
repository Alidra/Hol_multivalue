Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6910091_term_abbrevs.
Require Import SELECT_UNIQUE_spec.
Lemma lem6910071 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6910072 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term1 A P.
Proof. exact (@lem6910071 A h1 P). Qed.
Lemma lem6910073 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem6910074 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem6910073 A P) (@lem6910072 A P h1)). Qed.
Lemma lem6910075 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term3 A P x.
Proof. exact (@lem6910074 A P h1 x). Qed.
Lemma lem6910076 {A : Type'} (P : A -> Prop) (x : A) : (term3 A P x) = (term4 A P x).
Proof. exact (eq_refl (term3 A P x)). Qed.
Lemma lem6910077 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (EQ_MP (@lem6910076 A P x) (@lem6910075 A P x h1)). Qed.
Lemma lem6910078 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term5 A P x.
Proof. exact (h1). Qed.
Lemma lem6910079 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem6910077 A P x h2 (@lem6910078 A P x h1)). Qed.
Lemma lem6910080 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term6 A P x.
Proof. exact (fun h0 : term0 A => @lem6910079 A P x h1 h0). Qed.
Lemma lem6910081 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem6910082 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem6910080 A P x h1 (@lem6910081 A h2)). Qed.
Lemma lem6910083 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (fun h0 : term5 A P x => @lem6910082 A P x h0 h1). Qed.
Lemma lem6910084 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (fun x : A => @lem6910083 A P x h1). Qed.
Lemma lem6910085 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : A -> Prop => @lem6910084 A P h1). Qed.
Lemma lem6910086 {A : Type'} : term7 A.
Proof. exact (fun h0 : term0 A => @lem6910085 A h0). Qed.
Lemma lem6910087 {A : Type'} : term0 A.
Proof. exact (@lem6910086 A (@lem9522 A)). Qed.
Lemma lem6910088 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (@lem6910087 A P). Qed.
Lemma lem6910089 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem6910090 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (EQ_MP (@lem6910089 A P) (@lem6910088 A P)). Qed.
Lemma lem6910091 {A : Type'} (P : A -> Prop) (x : A) : term3 A P x.
Proof. exact (@lem6910090 A P x). Qed.
