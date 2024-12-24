Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1110673_term_abbrevs.
Lemma lem1110673 {A : Type'} (r : type1402 A) : (term0 A r) = ((@List.ForallOrdPairs A r (@nil A)) = True).
Proof. exact (eq_refl (term0 A r)). Qed.
