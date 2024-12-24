Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7660850_term_abbrevs.
Require Import thm10578_spec.
Require Import thm10597_spec.
Lemma lem7660848 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7660849 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : ((term1 _140454 _140455 _140456 P) = (term2 _140454 _140455 _140456 P)) = (term3 _140454 _140455 _140456 P).
Proof. exact (@lem7660848 ((term1 _140454 _140455 _140456 P) = (term2 _140454 _140455 _140456 P))). Qed.
Lemma lem7660850 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term3 _140454 _140455 _140456 P) = ((term1 _140454 _140455 _140456 P) = (term2 _140454 _140455 _140456 P)).
Proof. exact (SYM (@lem7660849 _140454 _140455 _140456 P)). Qed.
