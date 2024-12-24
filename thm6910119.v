Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6910119_term_abbrevs.
Require Import neutral_spec.
Lemma lem6910094 {_119565 : Type'} (op : type1400 _119565) : term0 _119565 op.
Proof. exact (@lem5711574 _119565 op). Qed.
Lemma lem6910095 {_119565 : Type'} (op : type1400 _119565) : (term0 _119565 op) = ((@neutral _119565 op) = (term1 _119565 op)).
Proof. exact (eq_refl (term0 _119565 op)). Qed.
Lemma lem6910100 {_119565 : Type'} (op : type1400 _119565) : (@neutral _119565 op) = (term1 _119565 op).
Proof. exact (EQ_MP (@lem6910095 _119565 op) (@lem6910094 _119565 op)). Qed.
Lemma lem6910101 (op : type1627) : (@neutral real op) = (term2 op).
Proof. exact (@lem6910100 real op). Qed.
Lemma lem6910102 : (@neutral real real_mul) = term3.
Proof. exact (@lem6910101 real_mul). Qed.
Lemma lem6910113 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6910114 : term4 = term5.
Proof. exact (MK_COMB (@lem6910113) (@lem6910102)). Qed.
Lemma lem6910115 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem6910116 : ((@neutral real real_mul) = term6) = (term3 = term6).
Proof. exact (MK_COMB (@lem6910114) (@lem6910115)). Qed.
Lemma lem6910119 : (term3 = term6) = ((@neutral real real_mul) = term6).
Proof. exact (SYM (@lem6910116)). Qed.
