Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_INV_term_abbrevs.
Require Import REAL_LE_INV_EQ_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Lemma lem1591908 (x : real) : term0 x.
Proof. exact (@lem1591907 x). Qed.
Lemma lem1591909 (x : real) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1591918 (x : real) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem1591909 x) (@lem1591908 x)). Qed.
Lemma lem1591919 (x : real) : (term3 x) = (term3 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1591920 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem1591919 x) (@lem1591918 x)). Qed.
Lemma lem1591922 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1591923 (x : real) : (term5 x) = True.
Proof. exact (@lem1591922 (term2 x)). Qed.
Lemma lem1591924 (x : real) : (term4 x) = True.
Proof. exact (TRANS (@lem1591920 x) (@lem1591923 x)). Qed.
Lemma lem1591925 : term6 = term7.
Proof. exact (fun_ext (fun x : real => @lem1591924 x)). Qed.
Lemma lem1591926 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1591927 : term8 = term9.
Proof. exact (MK_COMB (@lem1591926) (@lem1591925)). Qed.
Lemma lem1591929 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1591930 (t : Prop) : (term11 t) = t.
Proof. exact (@lem1591929 real t). Qed.
Lemma lem1591931 : term9 = True.
Proof. exact (@lem1591930 True). Qed.
Lemma lem1591932 : term8 = True.
Proof. exact (TRANS (@lem1591927) (@lem1591931)). Qed.
Lemma lem1591933 : True = term8.
Proof. exact (SYM (@lem1591932)). Qed.
Lemma lem1591934 : term8.
Proof. exact (EQ_MP (@lem1591933) (@lem0)). Qed.
