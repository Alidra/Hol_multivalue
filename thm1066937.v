Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066937_term_abbrevs.
Require Import thm1066936_spec.
Lemma lem1066937 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term1 A B sum' INL' INR'.
Proof. exact (proj2 (@lem1066936 A B sum' INL' INR' h1)). Qed.
