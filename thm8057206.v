Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8057206_term_abbrevs.
Require Import thm8057205_spec.
Lemma lem8057206 {_142951 _142952 _142953 : Type'} : term0 _142951 _142952 _142953.
Proof. exact (fun f : type56 _142951 _142952 => @lem8057205 _142951 _142952 _142953 f). Qed.
