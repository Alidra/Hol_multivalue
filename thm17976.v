Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17976_term_abbrevs.
Require Import ETA_AX_spec.
Lemma lem17967 {A B : Type'} (t : A -> B) (h1 : (term0 A B t) = t) : (term0 A B t) = t.
Proof. exact (h1). Qed.
Lemma lem17968 {A B : Type'} (t : A -> B) (h1 : (term0 A B t) = t) : t = (term0 A B t).
Proof. exact (SYM (@lem17967 A B t h1)). Qed.
Lemma lem17969 {A B : Type'} (t : A -> B) (h1 : t = (term0 A B t)) : t = (term0 A B t).
Proof. exact (h1). Qed.
Lemma lem17970 {A B : Type'} (t : A -> B) (h1 : t = (term0 A B t)) : (term0 A B t) = t.
Proof. exact (SYM (@lem17969 A B t h1)). Qed.
Lemma lem17971 {A B : Type'} (t : A -> B) : ((term0 A B t) = t) = (t = (term0 A B t)).
Proof. exact (prop_ext (fun h1 : (term0 A B t) = t => @lem17968 A B t h1) (fun h1 : t = (term0 A B t) => @lem17970 A B t h1)). Qed.
Lemma lem17972 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (fun_ext (fun t : A -> B => @lem17971 A B t)). Qed.
Lemma lem17973 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem17974 {A B : Type'} : (term3 A B) = (term4 A B).
Proof. exact (MK_COMB (@lem17973 A B) (@lem17972 A B)). Qed.
Lemma lem17975 {A B : Type'} : term4 A B.
Proof. exact (EQ_MP (@lem17974 A B) (@lem9121 A B)). Qed.
Lemma lem17976 {A B : Type'} (t : A -> B) : term5 A B t.
Proof. exact (@lem17975 A B t). Qed.
