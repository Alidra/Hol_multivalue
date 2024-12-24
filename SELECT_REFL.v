Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SELECT_REFL_term_abbrevs.
Require Import thm9425_spec.
Lemma lem9426 {A : Type'} (P : A -> Prop) : (term0 A P) = (ex P).
Proof. exact (@lem9425 A P). Qed.
Lemma lem9427 {A : Type'} (x : A) : (term1 A x) = (term2 A x).
Proof. exact (@lem9426 A (term3 A x)). Qed.
Lemma lem9428 {A : Type'} (x : A) : (term1 A x) = ((term4 A x) = x).
Proof. exact (eq_refl (term1 A x)). Qed.
Lemma lem9429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9430 {A : Type'} (x : A) : (term5 A x) = (term6 A x).
Proof. exact (MK_COMB (@lem9429) (@lem9428 A x)). Qed.
Lemma lem9431 {A : Type'} (x : A) : (term2 A x) = (term2 A x).
Proof. exact (eq_refl (term2 A x)). Qed.
Lemma lem9432 {A : Type'} (x : A) : ((term1 A x) = (term2 A x)) = (((term4 A x) = x) = (term2 A x)).
Proof. exact (MK_COMB (@lem9430 A x) (@lem9431 A x)). Qed.
Lemma lem9433 {A : Type'} (x : A) : ((term4 A x) = x) = (term2 A x).
Proof. exact (EQ_MP (@lem9432 A x) (@lem9427 A x)). Qed.
Lemma lem9434 {A : Type'} (x : A) : (term2 A x) = ((term4 A x) = x).
Proof. exact (SYM (@lem9433 A x)). Qed.
Lemma lem9435 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem9436 {A : Type'} (x : A) : term2 A x.
Proof. exact (ex_intro (term3 A x) x (@lem9435 A x)). Qed.
Lemma lem9437 {A : Type'} (x : A) : (term4 A x) = x.
Proof. exact (EQ_MP (@lem9434 A x) (@lem9436 A x)). Qed.
Lemma lem9442 {A : Type'} : term7 A.
Proof. exact (fun x : A => @lem9437 A x). Qed.
