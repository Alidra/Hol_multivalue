Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7926442_term_abbrevs.
Require Import thm7925148_spec.
Require Import thm7926434_spec.
Lemma lem7926435 {A : Type'} (_103783' : type45 A) (h1 : _103783' = (term0 A)) : (term1 A) = (term2 A _103783').
Proof. exact (SYM (@lem7925148 A _103783' h1)). Qed.
Lemma lem7926436 {A : Type'} (_103783' : type45 A) (h1 : _103783' = (term0 A)) : (@_103783 A) = (term2 A _103783').
Proof. exact (TRANS (@lem7926434 A) (@lem7926435 A _103783' h1)). Qed.
Lemma lem7926437 {A : Type'} (a : finite_sum A A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7926438 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term0 A)) : (@_103783 A a) = (term3 A _103783' a).
Proof. exact (MK_COMB (@lem7926436 A _103783' h1) (@lem7926437 A a)). Qed.
Lemma lem7926439 {A : Type'} (_103783' : type45 A) (a : finite_sum A A) : (term3 A _103783' a) = (term4 A _103783' a).
Proof. exact (eq_refl (term3 A _103783' a)). Qed.
Lemma lem7926440 {A : Type'} (a : finite_sum A A) : (term5 A a) = (term5 A a).
Proof. exact (eq_refl (term5 A a)). Qed.
Lemma lem7926441 {A : Type'} (_103783' : type45 A) (a : finite_sum A A) : ((@_103783 A a) = (term3 A _103783' a)) = ((@_103783 A a) = (term4 A _103783' a)).
Proof. exact (MK_COMB (@lem7926440 A a) (@lem7926439 A _103783' a)). Qed.
Lemma lem7926442 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term0 A)) : (@_103783 A a) = (term4 A _103783' a).
Proof. exact (EQ_MP (@lem7926441 A _103783' a) (@lem7926438 A a _103783' h1)). Qed.
