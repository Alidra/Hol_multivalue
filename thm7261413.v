Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7261413_term_abbrevs.
Require Import thm7260963_spec.
Require Import thm7261376_spec.
Lemma lem7261396 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term0 a b f g) : (term0 a b f g) = ((term1 a b f) = (term2 a b g)).
Proof. exact (prop_ext (fun h2 : term0 a b f g => @lem7261376 a b f g h1) (fun h2 : (term1 a b f) = (term2 a b g) => @lem7260963 a b f g h1)). Qed.
Lemma lem7261397 (a : nat) (b : nat) (f : nat -> real) (g : nat -> real) (h1 : term0 a b f g) : (term1 a b f) = (term2 a b g).
Proof. exact (EQ_MP (@lem7261396 a b f g h1) (@lem7260963 a b f g h1)). Qed.
Lemma lem7261398 (f : nat -> real) (a : nat) (b : nat) (g : nat -> real) : term3 f a b g.
Proof. exact (fun h0 : term0 a b f g => @lem7261397 a b f g h0). Qed.
Lemma lem7261403 (f : nat -> real) (a : nat) (g : nat -> real) : term4 f a g.
Proof. exact (fun b : nat => @lem7261398 f a b g). Qed.
Lemma lem7261408 (f : nat -> real) (g : nat -> real) : term5 f g.
Proof. exact (fun a : nat => @lem7261403 f a g). Qed.
Lemma lem7261413 (f : nat -> real) : term6 f.
Proof. exact (fun g : nat -> real => @lem7261408 f g). Qed.
