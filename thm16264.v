Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm16264_term_abbrevs.
Require Import one_INDUCT_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem16238 (P : unit -> Prop) : term0 P.
Proof. exact (@lem16018 P). Qed.
Lemma lem16239 (P : unit -> Prop) : (term0 P) = (term1 P).
Proof. exact (eq_refl (term0 P)). Qed.
Lemma lem16240 (P : unit -> Prop) : term1 P.
Proof. exact (EQ_MP (@lem16239 P) (@lem16238 P)). Qed.
Lemma lem16241 (P : unit -> Prop) : (term1 P) = ((term1 P) = True).
Proof. exact (@lem7 (term1 P)). Qed.
Lemma lem16252 (P : unit -> Prop) : (term1 P) = True.
Proof. exact (EQ_MP (@lem16241 P) (@lem16240 P)). Qed.
Lemma lem16253 (P : unit -> Prop) : True = (term1 P).
Proof. exact (SYM (@lem16252 P)). Qed.
Lemma lem16254 (P : unit -> Prop) : term1 P.
Proof. exact (EQ_MP (@lem16253 P) (@lem0)). Qed.
Lemma lem16255 (P : unit -> Prop) (h1 : term2 P) : term2 P.
Proof. exact (h1). Qed.
Lemma lem16256 (x : unit) (P : unit -> Prop) (h1 : term2 P) : term3 P x.
Proof. exact (@lem16255 P h1 x). Qed.
Lemma lem16257 (P : unit -> Prop) (x : unit) : (term3 P x) = (P x).
Proof. exact (eq_refl (term3 P x)). Qed.
Lemma lem16260 (x : unit) (P : unit -> Prop) (h1 : term2 P) : P x.
Proof. exact (EQ_MP (@lem16257 P x) (@lem16256 x P h1)). Qed.
Lemma lem16261 (P : unit -> Prop) (h1 : term2 P) : P tt.
Proof. exact (@lem16260 tt P h1). Qed.
Lemma lem16263 (P : unit -> Prop) : term4 P.
Proof. exact (fun h0 : term2 P => @lem16261 P h0). Qed.
Lemma lem16264 (P : unit -> Prop) : term5 P.
Proof. exact (conj (@lem16263 P) (@lem16254 P)). Qed.
