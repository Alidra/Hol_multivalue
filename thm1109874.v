Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1109872_spec.
Require Import thm1109873_spec.
Lemma lem1109874 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) : (@ALLPAIRS _25786 _25787 f (@nil _25787) l) = True.
Proof. exact (EQ_MP (@lem1109873 _25786 _25787 f l) (@lem1109872 _25786 _25787 f l)). Qed.
