Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6904637_term_abbrevs.
Require Import neutral_spec.
Lemma lem6904612 {_119565 : Type'} (op : type1400 _119565) : term0 _119565 op.
Proof. exact (@lem5711574 _119565 op). Qed.
Lemma lem6904613 {_119565 : Type'} (op : type1400 _119565) : (term0 _119565 op) = ((@neutral _119565 op) = (term1 _119565 op)).
Proof. exact (eq_refl (term0 _119565 op)). Qed.
Lemma lem6904618 {_119565 : Type'} (op : type1400 _119565) : (@neutral _119565 op) = (term1 _119565 op).
Proof. exact (EQ_MP (@lem6904613 _119565 op) (@lem6904612 _119565 op)). Qed.
Lemma lem6904619 (op : type1551) : (@neutral int op) = (term2 op).
Proof. exact (@lem6904618 int op). Qed.
Lemma lem6904620 : (@neutral int int_mul) = term3.
Proof. exact (@lem6904619 int_mul). Qed.
Lemma lem6904631 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem6904632 : term4 = term5.
Proof. exact (MK_COMB (@lem6904631) (@lem6904620)). Qed.
Lemma lem6904633 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem6904634 : ((@neutral int int_mul) = term6) = (term3 = term6).
Proof. exact (MK_COMB (@lem6904632) (@lem6904633)). Qed.
Lemma lem6904637 : (term3 = term6) = ((@neutral int int_mul) = term6).
Proof. exact (SYM (@lem6904634)). Qed.
