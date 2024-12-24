Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318766_term_abbrevs.
Require Import thm1318747_spec.
Lemma lem1318762 : term0.
Proof. exact (proj1 (@lem1318747)). Qed.
Lemma lem1318763 (x : nadd) : term1 x.
Proof. exact (@lem1318762 x). Qed.
Lemma lem1318764 (x : nadd) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1318765 (x : nadd) : term2 x.
Proof. exact (EQ_MP (@lem1318764 x) (@lem1318763 x)). Qed.
Lemma lem1318766 (x : nadd) (y : nadd) : term3 x y.
Proof. exact (@lem1318765 x y). Qed.
