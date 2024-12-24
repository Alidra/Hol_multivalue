Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALLPAIRS_term_abbrevs.
Require Import thm1109874_spec.
Require Import thm1109884_spec.
Require Import thm1109885_spec.
Lemma lem1109886 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) (l : list _25786) : (term0 _25786 _25787 f h t l) = (term1 _25786 _25787 h f t l).
Proof. exact (EQ_MP (@lem1109885 _25786 _25787 h f t l) (@lem1109884 _25786 _25787 h f t l)). Qed.
Lemma lem1109887 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) (l : list _25786) : term2 _25786 _25787 h f t l.
Proof. exact (conj (@lem1109874 _25786 _25787 f l) (@lem1109886 _25786 _25787 h f t l)). Qed.
