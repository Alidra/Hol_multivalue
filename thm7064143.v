Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7064143_term_abbrevs.
Require Import SELECT_UNIQUE_spec.
Lemma lem7064123 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7064124 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term1 A P.
Proof. exact (@lem7064123 A h1 P). Qed.
Lemma lem7064125 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem7064126 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem7064125 A P) (@lem7064124 A P h1)). Qed.
Lemma lem7064127 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term3 A P x.
Proof. exact (@lem7064126 A P h1 x). Qed.
Lemma lem7064128 {A : Type'} (P : A -> Prop) (x : A) : (term3 A P x) = (term4 A P x).
Proof. exact (eq_refl (term3 A P x)). Qed.
Lemma lem7064129 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (EQ_MP (@lem7064128 A P x) (@lem7064127 A P x h1)). Qed.
Lemma lem7064130 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term5 A P x.
Proof. exact (h1). Qed.
Lemma lem7064131 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem7064129 A P x h2 (@lem7064130 A P x h1)). Qed.
Lemma lem7064132 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) : term6 A P x.
Proof. exact (fun h0 : term0 A => @lem7064131 A P x h1 h0). Qed.
Lemma lem7064133 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7064134 {A : Type'} (P : A -> Prop) (x : A) (h1 : term5 A P x) (h2 : term0 A) : (@ε A P) = x.
Proof. exact (@lem7064132 A P x h1 (@lem7064133 A h2)). Qed.
Lemma lem7064135 {A : Type'} (P : A -> Prop) (x : A) (h1 : term0 A) : term4 A P x.
Proof. exact (fun h0 : term5 A P x => @lem7064134 A P x h0 h1). Qed.
Lemma lem7064136 {A : Type'} (P : A -> Prop) (h1 : term0 A) : term2 A P.
Proof. exact (fun x : A => @lem7064135 A P x h1). Qed.
Lemma lem7064137 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : A -> Prop => @lem7064136 A P h1). Qed.
Lemma lem7064138 {A : Type'} : term7 A.
Proof. exact (fun h0 : term0 A => @lem7064137 A h0). Qed.
Lemma lem7064139 {A : Type'} : term0 A.
Proof. exact (@lem7064138 A (@lem9522 A)). Qed.
Lemma lem7064140 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (@lem7064139 A P). Qed.
Lemma lem7064141 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem7064142 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (EQ_MP (@lem7064141 A P) (@lem7064140 A P)). Qed.
Lemma lem7064143 {A : Type'} (P : A -> Prop) (x : A) : term3 A P x.
Proof. exact (@lem7064142 A P x). Qed.
