Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_EXISTS_IMP_THM_term_abbrevs.
Require Import RIGHT_IMP_EXISTS_THM_spec.
Lemma lem12265 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : (term0 A P Q) = (term1 A P Q)) : (term0 A P Q) = (term1 A P Q).
Proof. exact (h1). Qed.
Lemma lem12266 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : (term0 A P Q) = (term1 A P Q)) : (term1 A P Q) = (term0 A P Q).
Proof. exact (SYM (@lem12265 A P Q h1)). Qed.
Lemma lem12267 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : (term1 A P Q) = (term0 A P Q)) : (term1 A P Q) = (term0 A P Q).
Proof. exact (h1). Qed.
Lemma lem12268 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : (term1 A P Q) = (term0 A P Q)) : (term0 A P Q) = (term1 A P Q).
Proof. exact (SYM (@lem12267 A P Q h1)). Qed.
Lemma lem12269 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term0 A P Q) = (term1 A P Q)) = ((term1 A P Q) = (term0 A P Q)).
Proof. exact (prop_ext (fun h1 : (term0 A P Q) = (term1 A P Q) => @lem12266 A P Q h1) (fun h1 : (term1 A P Q) = (term0 A P Q) => @lem12268 A P Q h1)). Qed.
Lemma lem12270 {A : Type'} (P : Prop) : (term2 A P) = (term3 A P).
Proof. exact (fun_ext (fun Q : A -> Prop => @lem12269 A P Q)). Qed.
Lemma lem12271 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem12272 {A : Type'} (P : Prop) : (term4 A P) = (term5 A P).
Proof. exact (MK_COMB (@lem12271 A) (@lem12270 A P)). Qed.
Lemma lem12273 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun P : Prop => @lem12272 A P)). Qed.
Lemma lem12274 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem12275 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem12274) (@lem12273 A)). Qed.
Lemma lem12276 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem12275 A) (@lem12262 A)). Qed.
Lemma lem12277 {A : Type'} (P : Prop) : term10 A P.
Proof. exact (@lem12276 A P). Qed.
Lemma lem12278 {A : Type'} (P : Prop) : (term10 A P) = (term5 A P).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem12279 {A : Type'} (P : Prop) : term5 A P.
Proof. exact (EQ_MP (@lem12278 A P) (@lem12277 A P)). Qed.
Lemma lem12280 {A : Type'} (P : Prop) (Q : A -> Prop) : term11 A P Q.
Proof. exact (@lem12279 A P Q). Qed.
Lemma lem12281 {A : Type'} (P : Prop) (Q : A -> Prop) : (term11 A P Q) = ((term1 A P Q) = (term0 A P Q)).
Proof. exact (eq_refl (term11 A P Q)). Qed.
Lemma lem12284 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1 A P Q) = (term0 A P Q).
Proof. exact (EQ_MP (@lem12281 A P Q) (@lem12280 A P Q)). Qed.
Lemma lem12285 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1 A P Q) = (term0 A P Q).
Proof. exact (@lem12284 A P Q). Qed.
Lemma lem12290 {A : Type'} (P : Prop) : term5 A P.
Proof. exact (fun Q : A -> Prop => @lem12285 A P Q). Qed.
Lemma lem12295 {A : Type'} : term9 A.
Proof. exact (fun P : Prop => @lem12290 A P). Qed.
