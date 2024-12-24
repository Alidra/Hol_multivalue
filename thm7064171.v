Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7064171_term_abbrevs.
Require Import neutral_spec.
Lemma lem7064146 {_119565 : Type'} (op : type1400 _119565) : term0 _119565 op.
Proof. exact (@lem5711574 _119565 op). Qed.
Lemma lem7064147 {_119565 : Type'} (op : type1400 _119565) : (term0 _119565 op) = ((@neutral _119565 op) = (term1 _119565 op)).
Proof. exact (eq_refl (term0 _119565 op)). Qed.
Lemma lem7064152 {_119565 : Type'} (op : type1400 _119565) : (@neutral _119565 op) = (term1 _119565 op).
Proof. exact (EQ_MP (@lem7064147 _119565 op) (@lem7064146 _119565 op)). Qed.
Lemma lem7064153 (op : type1627) : (@neutral real op) = (term2 op).
Proof. exact (@lem7064152 real op). Qed.
Lemma lem7064154 : (@neutral real real_add) = term3.
Proof. exact (@lem7064153 real_add). Qed.
Lemma lem7064165 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7064166 : term4 = term5.
Proof. exact (MK_COMB (@lem7064165) (@lem7064154)). Qed.
Lemma lem7064167 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem7064168 : ((@neutral real real_add) = term6) = (term3 = term6).
Proof. exact (MK_COMB (@lem7064166) (@lem7064167)). Qed.
Lemma lem7064171 : (term3 = term6) = ((@neutral real real_add) = term6).
Proof. exact (SYM (@lem7064168)). Qed.
