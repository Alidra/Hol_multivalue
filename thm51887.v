Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm51887_term_abbrevs.
Lemma lem51887 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term0 _5106 _5107 P) = ((term1 _5106 _5107 P) = (term2 _5106 _5107 P)).
Proof. exact (eq_refl (term0 _5106 _5107 P)). Qed.
