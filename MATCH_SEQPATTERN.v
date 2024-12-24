Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MATCH_SEQPATTERN_term_abbrevs.
Require Import thm8096294_spec.
Require Import thm8099922_spec.
Lemma lem8099923 {_143642 _143649 : Type'} (r : type1470 _143642 _143649) (x : _143649) (s : type1470 _143642 _143649) : (term0 _143642 _143649 x r s) = (term1 _143642 _143649 r x s).
Proof. exact (EQ_MP (@lem8096294 _143642 _143649 r x s) (@lem8099922 _143642 _143649 r s x)). Qed.
