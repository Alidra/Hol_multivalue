Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem1059220 {A : Type'} : (@BOTTOM A) = (@_mk_rec A (@ZBOT A)).
Proof. exact (@BOTTOM_def A). Qed.
