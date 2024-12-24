Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183065_term_abbrevs.
Require Import SETSPEC_spec.
Lemma lem3183059 {_83031 : Type'} (P : Prop) : term0 _83031 P.
Proof. exact (@lem3183048 _83031 P). Qed.
Lemma lem3183060 {_83031 : Type'} (P : Prop) : (term0 _83031 P) = (term1 _83031 P).
Proof. exact (eq_refl (term0 _83031 P)). Qed.
Lemma lem3183061 {_83031 : Type'} (P : Prop) : term1 _83031 P.
Proof. exact (EQ_MP (@lem3183060 _83031 P) (@lem3183059 _83031 P)). Qed.
Lemma lem3183062 {_83031 : Type'} (P : Prop) (v : _83031) : term2 _83031 P v.
Proof. exact (@lem3183061 _83031 P v). Qed.
Lemma lem3183063 {_83031 : Type'} (P : Prop) (v : _83031) : (term2 _83031 P v) = (term3 _83031 P v).
Proof. exact (eq_refl (term2 _83031 P v)). Qed.
Lemma lem3183064 {_83031 : Type'} (P : Prop) (v : _83031) : term3 _83031 P v.
Proof. exact (EQ_MP (@lem3183063 _83031 P v) (@lem3183062 _83031 P v)). Qed.
Lemma lem3183065 {_83031 : Type'} (P : Prop) (v : _83031) (t : _83031) : term4 _83031 P v t.
Proof. exact (@lem3183064 _83031 P v t). Qed.
