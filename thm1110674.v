Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1110672_spec.
Require Import thm1110673_spec.
Lemma lem1110674 {A : Type'} (r : type1402 A) : (@List.ForallOrdPairs A r (@nil A)) = True.
Proof. exact (EQ_MP (@lem1110673 A r) (@lem1110672 A r)). Qed.
