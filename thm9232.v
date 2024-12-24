Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm9232_term_abbrevs.
Require Import ETA_AX_spec.
Lemma lem9223 {A B : Type'} (t : A -> B) (h1 : (term0 A B t) = t) : (term0 A B t) = t.
Proof. exact (h1). Qed.
Lemma lem9224 {A B : Type'} (t : A -> B) (h1 : (term0 A B t) = t) : t = (term0 A B t).
Proof. exact (SYM (@lem9223 A B t h1)). Qed.
Lemma lem9225 {A B : Type'} (t : A -> B) (h1 : t = (term0 A B t)) : t = (term0 A B t).
Proof. exact (h1). Qed.
Lemma lem9226 {A B : Type'} (t : A -> B) (h1 : t = (term0 A B t)) : (term0 A B t) = t.
Proof. exact (SYM (@lem9225 A B t h1)). Qed.
Lemma lem9227 {A B : Type'} (t : A -> B) : ((term0 A B t) = t) = (t = (term0 A B t)).
Proof. exact (prop_ext (fun h1 : (term0 A B t) = t => @lem9224 A B t h1) (fun h1 : t = (term0 A B t) => @lem9226 A B t h1)). Qed.
Lemma lem9228 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (fun_ext (fun t : A -> B => @lem9227 A B t)). Qed.
Lemma lem9229 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem9230 {A B : Type'} : (term3 A B) = (term4 A B).
Proof. exact (MK_COMB (@lem9229 A B) (@lem9228 A B)). Qed.
Lemma lem9231 {A B : Type'} : term4 A B.
Proof. exact (EQ_MP (@lem9230 A B) (@lem9121 A B)). Qed.
Lemma lem9232 {A B : Type'} (t : A -> B) : term5 A B t.
Proof. exact (@lem9231 A B t). Qed.
