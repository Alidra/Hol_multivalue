Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm14834_term_abbrevs.
Require Import thm14786_spec.
Lemma lem14822 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term0 _2963 t e g' t' e') = (term0 _2963 t e g' t' e').
Proof. exact (eq_refl (term0 _2963 t e g' t' e')). Qed.
Lemma lem14823 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) (g : Prop) (h1 : g = False) : (term1 _2963 t e g' t' e' g) = (term2 _2963 t e g' t' e').
Proof. exact (MK_COMB (@lem14822 _2963 t e g' t' e') (@lem14786 g h1)). Qed.
Lemma lem14824 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term2 _2963 t e g' t' e') = (term3 _2963 t e g' t' e').
Proof. exact (eq_refl (term2 _2963 t e g' t' e')). Qed.
Lemma lem14825 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) (g : Prop) : (term4 _2963 t e g' t' e' g) = (term4 _2963 t e g' t' e' g).
Proof. exact (eq_refl (term4 _2963 t e g' t' e' g)). Qed.
Lemma lem14826 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : ((term1 _2963 t e g' t' e' g) = (term2 _2963 t e g' t' e')) = ((term1 _2963 t e g' t' e' g) = (term3 _2963 t e g' t' e')).
Proof. exact (MK_COMB (@lem14825 _2963 t e g' t' e' g) (@lem14824 _2963 t e g' t' e')). Qed.
Lemma lem14827 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term1 _2963 t e g' t' e' g) = (term5 _2963 g t e g' t' e').
Proof. exact (eq_refl (term1 _2963 t e g' t' e' g)). Qed.
Lemma lem14828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem14829 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term4 _2963 t e g' t' e' g) = (term6 _2963 g t e g' t' e').
Proof. exact (MK_COMB (@lem14828) (@lem14827 _2963 g t e g' t' e')). Qed.
Lemma lem14830 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term3 _2963 t e g' t' e') = (term3 _2963 t e g' t' e').
Proof. exact (eq_refl (term3 _2963 t e g' t' e')). Qed.
Lemma lem14831 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : ((term1 _2963 t e g' t' e' g) = (term3 _2963 t e g' t' e')) = ((term5 _2963 g t e g' t' e') = (term3 _2963 t e g' t' e')).
Proof. exact (MK_COMB (@lem14829 _2963 g t e g' t' e') (@lem14830 _2963 t e g' t' e')). Qed.
Lemma lem14832 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : ((term1 _2963 t e g' t' e' g) = (term2 _2963 t e g' t' e')) = ((term5 _2963 g t e g' t' e') = (term3 _2963 t e g' t' e')).
Proof. exact (TRANS (@lem14826 _2963 g t e g' t' e') (@lem14831 _2963 g t e g' t' e')). Qed.
Lemma lem14833 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) (g : Prop) (h1 : g = False) : (term5 _2963 g t e g' t' e') = (term3 _2963 t e g' t' e').
Proof. exact (EQ_MP (@lem14832 _2963 g t e g' t' e') (@lem14823 _2963 t e g' t' e' g h1)). Qed.
Lemma lem14834 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) (g : Prop) (h1 : g = False) : (term3 _2963 t e g' t' e') = (term5 _2963 g t e g' t' e').
Proof. exact (SYM (@lem14833 _2963 t e g' t' e' g h1)). Qed.
