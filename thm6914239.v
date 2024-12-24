Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6914239_term_abbrevs.
Require Import neutral_spec.
Lemma lem6914214 {_119565 : Type'} (op : type1400 _119565) : term0 _119565 op.
Proof. exact (@lem5711574 _119565 op). Qed.
Lemma lem6914215 {_119565 : Type'} (op : type1400 _119565) : (term0 _119565 op) = ((@neutral _119565 op) = (term1 _119565 op)).
Proof. exact (eq_refl (term0 _119565 op)). Qed.
Lemma lem6914220 {_119565 : Type'} (op : type1400 _119565) : (@neutral _119565 op) = (term1 _119565 op).
Proof. exact (EQ_MP (@lem6914215 _119565 op) (@lem6914214 _119565 op)). Qed.
Lemma lem6914221 (op : type1551) : (@neutral int op) = (term2 op).
Proof. exact (@lem6914220 int op). Qed.
Lemma lem6914222 : (@neutral int int_add) = term3.
Proof. exact (@lem6914221 int_add). Qed.
Lemma lem6914233 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem6914234 : term4 = term5.
Proof. exact (MK_COMB (@lem6914233) (@lem6914222)). Qed.
Lemma lem6914235 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem6914236 : ((@neutral int int_add) = term6) = (term3 = term6).
Proof. exact (MK_COMB (@lem6914234) (@lem6914235)). Qed.
Lemma lem6914239 : (term3 = term6) = ((@neutral int int_add) = term6).
Proof. exact (SYM (@lem6914236)). Qed.
