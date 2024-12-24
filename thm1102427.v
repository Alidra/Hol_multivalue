Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1102427_term_abbrevs.
Require Import thm1102421_spec.
Lemma lem1102423 {_25350 _25351 : Type'} : term0 _25350 _25351.
Proof. exact (proj1 (@lem1102421 _25350 _25351)). Qed.
Lemma lem1102424 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : term1 _25350 _25351 f.
Proof. exact (@lem1102423 _25350 _25351 f). Qed.
Lemma lem1102425 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : (term1 _25350 _25351 f) = (term2 _25350 _25351 f).
Proof. exact (eq_refl (term1 _25350 _25351 f)). Qed.
Lemma lem1102426 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) : term2 _25350 _25351 f.
Proof. exact (EQ_MP (@lem1102425 _25350 _25351 f) (@lem1102424 _25350 _25351 f)). Qed.
Lemma lem1102427 {_25350 _25351 : Type'} (f : type1467 _25350 _25351) (b : _25350) : term3 _25350 _25351 f b.
Proof. exact (@lem1102426 _25350 _25351 f b). Qed.
