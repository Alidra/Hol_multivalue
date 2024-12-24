Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm0_spec.
Require Import thm7936917_spec.
Lemma lem7948705 {A : Type'} (s : A -> Prop) (n : nat) : ((@dimindex A (@UNIV A)) = n) = ((@dimindex A s) = (NUMERAL n)).
Proof. exact (EQ_MP (@lem7936917 A s n) (@lem0)). Qed.
