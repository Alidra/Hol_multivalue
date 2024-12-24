Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3459046_term_abbrevs.
Require Import thm3459034_spec.
Require Import thm3459035_spec.
Lemma lem3459043 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3459035 A s t) (@lem3459034 A s t)). Qed.
Lemma lem3459044 {_89769 : Type'} (s : _89769 -> Prop) (t : _89769 -> Prop) : (s = t) = (term0 _89769 s t).
Proof. exact (@lem3459043 _89769 s t). Qed.
Lemma lem3459045 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : ((term1 _89769 _89788 _89789 P f) = (term2 _89769 _89788 _89789 P f)) = (term3 _89769 _89788 _89789 P f).
Proof. exact (@lem3459044 _89769 (term1 _89769 _89788 _89789 P f) (term2 _89769 _89788 _89789 P f)). Qed.
Lemma lem3459046 {_89769 _89788 _89789 : Type'} (P : type1470 _89788 _89789) (f : type1517 _89769 _89788 _89789) : (term3 _89769 _89788 _89789 P f) = ((term1 _89769 _89788 _89789 P f) = (term2 _89769 _89788 _89789 P f)).
Proof. exact (SYM (@lem3459045 _89769 _89788 _89789 P f)). Qed.
