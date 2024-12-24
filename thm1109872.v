Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1109872_term_abbrevs.
Require Import thm1109866_spec.
Lemma lem1109868 {_25786 _25787 : Type'} : term0 _25786 _25787.
Proof. exact (proj1 (@lem1109866 _25786 _25787)). Qed.
Lemma lem1109869 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : term1 _25786 _25787 f.
Proof. exact (@lem1109868 _25786 _25787 f). Qed.
Lemma lem1109870 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : (term1 _25786 _25787 f) = (term2 _25786 _25787 f).
Proof. exact (eq_refl (term1 _25786 _25787 f)). Qed.
Lemma lem1109871 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) : term2 _25786 _25787 f.
Proof. exact (EQ_MP (@lem1109870 _25786 _25787 f) (@lem1109869 _25786 _25787 f)). Qed.
Lemma lem1109872 {_25786 _25787 : Type'} (f : type1470 _25786 _25787) (l : list _25786) : term3 _25786 _25787 f l.
Proof. exact (@lem1109871 _25786 _25787 f l). Qed.
