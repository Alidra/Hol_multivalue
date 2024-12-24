Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3464374_term_abbrevs.
Require Import thm3459338_spec.
Require Import thm3462445_spec.
Lemma lem3464374 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : term0 _89769 _89788 _89789 P f.
Proof. exact (EQ_MP (@lem3459338 _89769 _89788 _89789 P f) (@lem3462445 _89769 _89788 _89789 P f)). Qed.
