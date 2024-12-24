Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem1059234 {A : Type'} : (@_mk_rec A (@ZBOT A)) = (@_mk_rec A (@ZBOT A)).
Proof. exact (eq_refl (@_mk_rec A (@ZBOT A))). Qed.
