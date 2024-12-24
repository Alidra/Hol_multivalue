Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3453899_term_abbrevs.
Require Import IN_UNIONS_spec.
Lemma lem3453896 {A : Type'} (s : type686 A) : term0 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem3453897 {A : Type'} (s : type686 A) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3453898 {A : Type'} (s : type686 A) : term1 A s.
Proof. exact (EQ_MP (@lem3453897 A s) (@lem3453896 A s)). Qed.
Lemma lem3453899 {A : Type'} (s : type686 A) (x : A) : term2 A s x.
Proof. exact (@lem3453898 A s x). Qed.
