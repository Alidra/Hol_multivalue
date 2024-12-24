Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm14821_term_abbrevs.
Require Import thm14785_spec.
Lemma lem14809 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term0 _2963 t e g' t' e') = (term0 _2963 t e g' t' e').
Proof. exact (eq_refl (term0 _2963 t e g' t' e')). Qed.
Lemma lem14810 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) (g : Prop) (h1 : g = True) : (term1 _2963 t e g' t' e' g) = (term2 _2963 t e g' t' e').
Proof. exact (MK_COMB (@lem14809 _2963 t e g' t' e') (@lem14785 g h1)). Qed.
Lemma lem14811 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term2 _2963 t e g' t' e') = (term3 _2963 t e g' t' e').
Proof. exact (eq_refl (term2 _2963 t e g' t' e')). Qed.
Lemma lem14812 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) (g : Prop) : (term4 _2963 t e g' t' e' g) = (term4 _2963 t e g' t' e' g).
Proof. exact (eq_refl (term4 _2963 t e g' t' e' g)). Qed.
Lemma lem14813 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : ((term1 _2963 t e g' t' e' g) = (term2 _2963 t e g' t' e')) = ((term1 _2963 t e g' t' e' g) = (term3 _2963 t e g' t' e')).
Proof. exact (MK_COMB (@lem14812 _2963 t e g' t' e' g) (@lem14811 _2963 t e g' t' e')). Qed.
Lemma lem14814 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term1 _2963 t e g' t' e' g) = (term5 _2963 g t e g' t' e').
Proof. exact (eq_refl (term1 _2963 t e g' t' e' g)). Qed.
Lemma lem14815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem14816 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term4 _2963 t e g' t' e' g) = (term6 _2963 g t e g' t' e').
Proof. exact (MK_COMB (@lem14815) (@lem14814 _2963 g t e g' t' e')). Qed.
Lemma lem14817 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term3 _2963 t e g' t' e') = (term3 _2963 t e g' t' e').
Proof. exact (eq_refl (term3 _2963 t e g' t' e')). Qed.
Lemma lem14818 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : ((term1 _2963 t e g' t' e' g) = (term3 _2963 t e g' t' e')) = ((term5 _2963 g t e g' t' e') = (term3 _2963 t e g' t' e')).
Proof. exact (MK_COMB (@lem14816 _2963 g t e g' t' e') (@lem14817 _2963 t e g' t' e')). Qed.
Lemma lem14819 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : ((term1 _2963 t e g' t' e' g) = (term2 _2963 t e g' t' e')) = ((term5 _2963 g t e g' t' e') = (term3 _2963 t e g' t' e')).
Proof. exact (TRANS (@lem14813 _2963 g t e g' t' e') (@lem14818 _2963 g t e g' t' e')). Qed.
Lemma lem14820 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) (g : Prop) (h1 : g = True) : (term5 _2963 g t e g' t' e') = (term3 _2963 t e g' t' e').
Proof. exact (EQ_MP (@lem14819 _2963 g t e g' t' e') (@lem14810 _2963 t e g' t' e' g h1)). Qed.
Lemma lem14821 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) (g : Prop) (h1 : g = True) : (term3 _2963 t e g' t' e') = (term5 _2963 g t e g' t' e').
Proof. exact (SYM (@lem14820 _2963 t e g' t' e' g h1)). Qed.
