Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1109884_term_abbrevs.
Require Import thm1109867_spec.
Lemma lem1109875 {_25786 _25787 : Type'} (h : _25787) : term0 _25786 _25787 h.
Proof. exact (@lem1109867 _25786 _25787 h). Qed.
Lemma lem1109876 {_25786 _25787 : Type'} (h : _25787) : (term0 _25786 _25787 h) = (term1 _25786 _25787 h).
Proof. exact (eq_refl (term0 _25786 _25787 h)). Qed.
Lemma lem1109877 {_25786 _25787 : Type'} (h : _25787) : term1 _25786 _25787 h.
Proof. exact (EQ_MP (@lem1109876 _25786 _25787 h) (@lem1109875 _25786 _25787 h)). Qed.
Lemma lem1109878 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) : term2 _25786 _25787 h f.
Proof. exact (@lem1109877 _25786 _25787 h f). Qed.
Lemma lem1109879 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) : (term2 _25786 _25787 h f) = (term3 _25786 _25787 h f).
Proof. exact (eq_refl (term2 _25786 _25787 h f)). Qed.
Lemma lem1109880 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) : term3 _25786 _25787 h f.
Proof. exact (EQ_MP (@lem1109879 _25786 _25787 h f) (@lem1109878 _25786 _25787 h f)). Qed.
Lemma lem1109881 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) : term4 _25786 _25787 h f t.
Proof. exact (@lem1109880 _25786 _25787 h f t). Qed.
Lemma lem1109882 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) : (term4 _25786 _25787 h f t) = (term5 _25786 _25787 h f t).
Proof. exact (eq_refl (term4 _25786 _25787 h f t)). Qed.
Lemma lem1109883 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) : term5 _25786 _25787 h f t.
Proof. exact (EQ_MP (@lem1109882 _25786 _25787 h f t) (@lem1109881 _25786 _25787 h f t)). Qed.
Lemma lem1109884 {_25786 _25787 : Type'} (h : _25787) (f : type1470 _25786 _25787) (t : list _25787) (l : list _25786) : term6 _25786 _25787 h f t l.
Proof. exact (@lem1109883 _25786 _25787 h f t l). Qed.
