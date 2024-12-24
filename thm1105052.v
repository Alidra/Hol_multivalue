Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1105052_term_abbrevs.
Require Import thm1105046_spec.
Lemma lem1105048 {_25498 _25501 _25508 : Type'} : term0 _25498 _25501 _25508.
Proof. exact (proj1 (@lem1105046 _25498 _25501 _25508)). Qed.
Lemma lem1105049 {_25498 _25501 _25508 : Type'} (f : type1475 _25498 _25501 _25508) : term1 _25498 _25501 _25508 f.
Proof. exact (@lem1105048 _25498 _25501 _25508 f). Qed.
Lemma lem1105050 {_25498 _25501 _25508 : Type'} (f : type1475 _25498 _25501 _25508) : (term1 _25498 _25501 _25508 f) = (term2 _25498 _25501 _25508 f).
Proof. exact (eq_refl (term1 _25498 _25501 _25508 f)). Qed.
Lemma lem1105051 {_25498 _25501 _25508 : Type'} (f : type1475 _25498 _25501 _25508) : term2 _25498 _25501 _25508 f.
Proof. exact (EQ_MP (@lem1105050 _25498 _25501 _25508 f) (@lem1105049 _25498 _25501 _25508 f)). Qed.
Lemma lem1105052 {_25498 _25501 _25508 : Type'} (f : type1475 _25498 _25501 _25508) (l : list _25508) : term3 _25498 _25501 _25508 f l.
Proof. exact (@lem1105051 _25498 _25501 _25508 f l). Qed.
