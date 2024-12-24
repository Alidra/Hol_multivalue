Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP2_DEF_term_abbrevs.
Require Import thm1105054_spec.
Require Import thm1105064_spec.
Require Import thm1105065_spec.
Lemma lem1105066 {_25498 _25501 _25508 : Type'} (h1' : _25501) (f : type1475 _25498 _25501 _25508) (t1 : list _25501) (l : list _25508) : (term0 _25498 _25501 _25508 f h1' t1 l) = (term1 _25498 _25501 _25508 h1' f t1 l).
Proof. exact (EQ_MP (@lem1105065 _25498 _25501 _25508 h1' f t1 l) (@lem1105064 _25498 _25501 _25508 h1' f t1 l)). Qed.
Lemma lem1105067 {_25498 _25501 _25508 : Type'} (h1' : _25501) (f : type1475 _25498 _25501 _25508) (t1 : list _25501) (l : list _25508) : term2 _25498 _25501 _25508 h1' f t1 l.
Proof. exact (conj (@lem1105054 _25498 _25501 _25508 f l) (@lem1105066 _25498 _25501 _25508 h1' f t1 l)). Qed.
