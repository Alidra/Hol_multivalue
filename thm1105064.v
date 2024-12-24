Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1105064_term_abbrevs.
Require Import thm1105047_spec.
Lemma lem1105055 {_25498 _25501 _25508 : Type'} (h1' : _25501) : term0 _25498 _25501 _25508 h1'.
Proof. exact (@lem1105047 _25498 _25501 _25508 h1'). Qed.
Lemma lem1105056 {_25498 _25501 _25508 : Type'} (h1' : _25501) : (term0 _25498 _25501 _25508 h1') = (term1 _25498 _25501 _25508 h1').
Proof. exact (eq_refl (term0 _25498 _25501 _25508 h1')). Qed.
Lemma lem1105057 {_25498 _25501 _25508 : Type'} (h1' : _25501) : term1 _25498 _25501 _25508 h1'.
Proof. exact (EQ_MP (@lem1105056 _25498 _25501 _25508 h1') (@lem1105055 _25498 _25501 _25508 h1')). Qed.
Lemma lem1105058 {_25498 _25501 _25508 : Type'} (h1' : _25501) (f : type1475 _25498 _25501 _25508) : term2 _25498 _25501 _25508 h1' f.
Proof. exact (@lem1105057 _25498 _25501 _25508 h1' f). Qed.
Lemma lem1105059 {_25498 _25501 _25508 : Type'} (h1' : _25501) (f : type1475 _25498 _25501 _25508) : (term2 _25498 _25501 _25508 h1' f) = (term3 _25498 _25501 _25508 h1' f).
Proof. exact (eq_refl (term2 _25498 _25501 _25508 h1' f)). Qed.
Lemma lem1105060 {_25498 _25501 _25508 : Type'} (h1' : _25501) (f : type1475 _25498 _25501 _25508) : term3 _25498 _25501 _25508 h1' f.
Proof. exact (EQ_MP (@lem1105059 _25498 _25501 _25508 h1' f) (@lem1105058 _25498 _25501 _25508 h1' f)). Qed.
Lemma lem1105061 {_25498 _25501 _25508 : Type'} (h1' : _25501) (f : type1475 _25498 _25501 _25508) (t1 : list _25501) : term4 _25498 _25501 _25508 h1' f t1.
Proof. exact (@lem1105060 _25498 _25501 _25508 h1' f t1). Qed.
Lemma lem1105062 {_25498 _25501 _25508 : Type'} (h1' : _25501) (f : type1475 _25498 _25501 _25508) (t1 : list _25501) : (term4 _25498 _25501 _25508 h1' f t1) = (term5 _25498 _25501 _25508 h1' f t1).
Proof. exact (eq_refl (term4 _25498 _25501 _25508 h1' f t1)). Qed.
Lemma lem1105063 {_25498 _25501 _25508 : Type'} (h1' : _25501) (f : type1475 _25498 _25501 _25508) (t1 : list _25501) : term5 _25498 _25501 _25508 h1' f t1.
Proof. exact (EQ_MP (@lem1105062 _25498 _25501 _25508 h1' f t1) (@lem1105061 _25498 _25501 _25508 h1' f t1)). Qed.
Lemma lem1105064 {_25498 _25501 _25508 : Type'} (h1' : _25501) (f : type1475 _25498 _25501 _25508) (t1 : list _25501) (l : list _25508) : term6 _25498 _25501 _25508 h1' f t1 l.
Proof. exact (@lem1105063 _25498 _25501 _25508 h1' f t1 l). Qed.
