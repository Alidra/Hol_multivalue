Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_AND_FORALL_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5278 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5280 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : P.
Proof. exact (proj1 (@lem5278 A P Q h1)). Qed.
Lemma lem5281 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term1 A Q.
Proof. exact (proj2 (@lem5278 A P Q h1)). Qed.
Lemma lem5283 {A : Type'} (_136 : A) (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term2 A Q _136.
Proof. exact (@lem5281 A P Q h1 _136). Qed.
Lemma lem5284 {A : Type'} (Q : A -> Prop) (_136 : A) : (term2 A Q _136) = (Q _136).
Proof. exact (eq_refl (term2 A Q _136)). Qed.
Lemma lem5285 {A : Type'} (_136 : A) (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : Q _136.
Proof. exact (EQ_MP (@lem5284 A Q _136) (@lem5283 A _136 P Q h1)). Qed.
Lemma lem5286 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : Q x.
Proof. exact (@lem5285 A x P Q h1). Qed.
Lemma lem5293 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : P.
Proof. exact (@lem5280 A P Q h1). Qed.
Lemma lem5294 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q x.
Proof. exact (conj (@lem5293 A P Q h1) (@lem5286 A x P Q h1)). Qed.
Lemma lem5299 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term4 A P Q.
Proof. exact (fun x : A => @lem5294 A x P Q h1). Qed.
Lemma lem5300 {A : Type'} (P : Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5299 A P Q h0). Qed.
Lemma lem5301 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (h1). Qed.
Lemma lem5302 {A : Type'} (_137 : A) (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term6 A P Q _137.
Proof. exact (@lem5301 A P Q h1 _137). Qed.
Lemma lem5303 {A : Type'} (P : Prop) (Q : A -> Prop) (_137 : A) : (term6 A P Q _137) = (term3 A P Q _137).
Proof. exact (eq_refl (term6 A P Q _137)). Qed.
Lemma lem5304 {A : Type'} (_137 : A) (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term3 A P Q _137.
Proof. exact (EQ_MP (@lem5303 A P Q _137) (@lem5302 A _137 P Q h1)). Qed.
Lemma lem5306 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : P.
Proof. exact (proj1 (@lem5304 A (@el A) P Q h1)). Qed.
Lemma lem5310 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : (term4 A P Q) = P.
Proof. exact (prop_ext (fun h2 : term4 A P Q => @lem5306 A P Q h1) (fun h2 : P => @lem5301 A P Q h1)). Qed.
Lemma lem5311 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : P.
Proof. exact (EQ_MP (@lem5310 A P Q h1) (@lem5301 A P Q h1)). Qed.
Lemma lem5312 {A : Type'} (_138 : A) (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term6 A P Q _138.
Proof. exact (@lem5301 A P Q h1 _138). Qed.
Lemma lem5313 {A : Type'} (P : Prop) (Q : A -> Prop) (_138 : A) : (term6 A P Q _138) = (term3 A P Q _138).
Proof. exact (eq_refl (term6 A P Q _138)). Qed.
Lemma lem5314 {A : Type'} (_138 : A) (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term3 A P Q _138.
Proof. exact (EQ_MP (@lem5313 A P Q _138) (@lem5312 A _138 P Q h1)). Qed.
Lemma lem5315 {A : Type'} (_138 : A) (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : Q _138.
Proof. exact (proj2 (@lem5314 A _138 P Q h1)). Qed.
Lemma lem5317 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : Q x.
Proof. exact (@lem5315 A x P Q h1). Qed.
Lemma lem5323 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (@lem5301 A P Q h1). Qed.
Lemma lem5324 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : (term4 A P Q) = (Q x).
Proof. exact (prop_ext (fun h2 : term4 A P Q => @lem5317 A x P Q h1) (fun h2 : Q x => @lem5323 A P Q h1)). Qed.
Lemma lem5325 {A : Type'} (x : A) (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : Q x.
Proof. exact (EQ_MP (@lem5324 A x P Q h1) (@lem5323 A P Q h1)). Qed.
Lemma lem5330 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term1 A Q.
Proof. exact (fun x : A => @lem5325 A x P Q h1). Qed.
Lemma lem5331 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : P.
Proof. exact (@lem5311 A P Q h1). Qed.
Lemma lem5332 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term0 A P Q.
Proof. exact (conj (@lem5331 A P Q h1) (@lem5330 A P Q h1)). Qed.
Lemma lem5333 {A : Type'} (P : Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (fun h0 : term4 A P Q => @lem5332 A P Q h0). Qed.
Lemma lem5334 {A : Type'} (P : Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (@lem5300 A P Q). Qed.
Lemma lem5335 {A : Type'} (P : Prop) (Q : A -> Prop) : term8 A P Q.
Proof. exact (conj (@lem5334 A P Q) (@lem5333 A P Q)). Qed.
Lemma lem5336 {A : Type'} (P : Prop) (Q : A -> Prop) : (term8 A P Q) = ((term0 A P Q) = (term4 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term4 A P Q)). Qed.
Lemma lem5337 {A : Type'} (P : Prop) (Q : A -> Prop) : (term0 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem5336 A P Q) (@lem5335 A P Q)). Qed.
Lemma lem5342 {A : Type'} (P : Prop) : term9 A P.
Proof. exact (fun Q : A -> Prop => @lem5337 A P Q). Qed.
Lemma lem5347 {A : Type'} : term10 A.
Proof. exact (fun P : Prop => @lem5342 A P). Qed.
Lemma lem5348 {A : Type'} : term10 A.
Proof. exact (@lem5347 A). Qed.
