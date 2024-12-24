Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338105_term_abbrevs.
Require Import thm1338093_spec.
Lemma lem1338094 : term0.
Proof. exact (proj2 (@lem1338093)). Qed.
Lemma lem1338104 : term1.
Proof. exact (proj1 (@lem1338094)). Qed.
Lemma lem1338105 (P : real -> Prop) : term2 P.
Proof. exact (@lem1338104 P). Qed.
