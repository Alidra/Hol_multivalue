Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3459028_term_abbrevs.
Require Import IN_INTERS_spec.
Lemma lem3459025 {A : Type'} (s : type686 A) : term0 A s.
Proof. exact (@lem3205364 A s). Qed.
Lemma lem3459026 {A : Type'} (s : type686 A) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3459027 {A : Type'} (s : type686 A) : term1 A s.
Proof. exact (EQ_MP (@lem3459026 A s) (@lem3459025 A s)). Qed.
Lemma lem3459028 {A : Type'} (s : type686 A) (x : A) : term2 A s x.
Proof. exact (@lem3459027 A s x). Qed.
