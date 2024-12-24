Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_IN_PCROSS_term_abbrevs.
Require Import thm0_spec.
Require Import thm8003920_spec.
Lemma lem8003921 {_141853 _141854 _141855 : Type'} (s : type24 _141853 _141854) (t : type24 _141853 _141855) (P : type16 _141853 _141854 _141855) : (term0 _141853 _141854 _141855 s t P) = (term1 _141853 _141854 _141855 s t P).
Proof. exact (EQ_MP (@lem8003920 _141853 _141854 _141855 s t P) (@lem0)). Qed.
