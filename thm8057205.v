Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8057205_term_abbrevs.
Require Import thm8057179_spec.
Lemma lem8057205 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) : term0 _142951 _142952 _142953 f.
Proof. exact (fun g : type56 _142951 _142953 => @lem8057179 _142951 _142952 _142953 f g). Qed.
