Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3458942_term_abbrevs.
Require Import thm3453922_spec.
Require Import thm3458939_spec.
Lemma lem3458942 {_89646 _89670 _89671 _89672 : Type'} (P : type1517 _89670 _89671 _89672) (f : type1524 _89646 _89670 _89671 _89672) : (term0 _89646 _89670 _89671 _89672 P f) = (term1 _89646 _89670 _89671 _89672 P f).
Proof. exact (EQ_MP (@lem3453922 _89646 _89670 _89671 _89672 P f) (@lem3458939 _89646 _89670 _89671 _89672 P f)). Qed.
