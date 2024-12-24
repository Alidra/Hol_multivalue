Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import has_inf_term_abbrevs.
Lemma lem5289924 : has_inf = term0.
Proof. exact (@has_inf_def). Qed.
Lemma lem5289925 (_69254 : real -> Prop) : _69254 = _69254.
Proof. exact (eq_refl _69254). Qed.
Lemma lem5289926 (_69254 : real -> Prop) : (has_inf _69254) = (term1 _69254).
Proof. exact (MK_COMB (@lem5289924) (@lem5289925 _69254)). Qed.
Lemma lem5289927 (_69254 : real -> Prop) : (term1 _69254) = (term2 _69254).
Proof. exact (eq_refl (term1 _69254)). Qed.
Lemma lem5289928 (_69254 : real -> Prop) : (has_inf _69254) = (term2 _69254).
Proof. exact (TRANS (@lem5289926 _69254) (@lem5289927 _69254)). Qed.
Lemma lem5289929 (_69255 : real) : _69255 = _69255.
Proof. exact (eq_refl _69255). Qed.
Lemma lem5289930 (_69254 : real -> Prop) (_69255 : real) : (has_inf _69254 _69255) = (term3 _69254 _69255).
Proof. exact (MK_COMB (@lem5289928 _69254) (@lem5289929 _69255)). Qed.
Lemma lem5289931 (_69254 : real -> Prop) (_69255 : real) : (term3 _69254 _69255) = (term4 _69254 _69255).
Proof. exact (eq_refl (term3 _69254 _69255)). Qed.
Lemma lem5289932 (_69254 : real -> Prop) (_69255 : real) : (has_inf _69254 _69255) = (term4 _69254 _69255).
Proof. exact (TRANS (@lem5289930 _69254 _69255) (@lem5289931 _69254 _69255)). Qed.
Lemma lem5289933 (_69254 : real -> Prop) : term5 _69254.
Proof. exact (fun _69255 : real => @lem5289932 _69254 _69255). Qed.
Lemma lem5289934 : term6.
Proof. exact (fun _69254 : real -> Prop => @lem5289933 _69254). Qed.
Lemma lem5289935 (_69254 : real -> Prop) : term7 _69254.
Proof. exact (@lem5289934 _69254). Qed.
Lemma lem5289936 (_69254 : real -> Prop) : (term7 _69254) = (term5 _69254).
Proof. exact (eq_refl (term7 _69254)). Qed.
Lemma lem5289937 (_69254 : real -> Prop) : term5 _69254.
Proof. exact (EQ_MP (@lem5289936 _69254) (@lem5289935 _69254)). Qed.
Lemma lem5289938 (_69254 : real -> Prop) (_69255 : real) : term8 _69254 _69255.
Proof. exact (@lem5289937 _69254 _69255). Qed.
Lemma lem5289939 (_69254 : real -> Prop) (_69255 : real) : (term8 _69254 _69255) = ((has_inf _69254 _69255) = (term4 _69254 _69255)).
Proof. exact (eq_refl (term8 _69254 _69255)). Qed.
Lemma lem5289940 (_69254 : real -> Prop) (_69255 : real) : (has_inf _69254 _69255) = (term4 _69254 _69255).
Proof. exact (EQ_MP (@lem5289939 _69254 _69255) (@lem5289938 _69254 _69255)). Qed.
Lemma lem5289983 (s : real -> Prop) (b : real) : (has_inf s b) = (term4 s b).
Proof. exact (@lem5289940 s b). Qed.
Lemma lem5289984 (s : real -> Prop) : term5 s.
Proof. exact (fun b : real => @lem5289983 s b). Qed.
Lemma lem5289985 : term6.
Proof. exact (fun s : real -> Prop => @lem5289984 s). Qed.
