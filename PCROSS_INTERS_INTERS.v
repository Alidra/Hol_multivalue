Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PCROSS_INTERS_INTERS_term_abbrevs.
Require Import thm8057206_spec.
Require Import thm8057209_spec.
Lemma lem8057213 {_142951 _142952 _142953 : Type'} : term0 _142951 _142952 _142953.
Proof. exact (EQ_MP (@lem8057209 _142951 _142952 _142953) (@lem8057206 _142951 _142952 _142953)). Qed.
