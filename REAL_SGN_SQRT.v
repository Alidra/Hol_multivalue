Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_SQRT_term_abbrevs.
Require Import SQRT_WORKS_GEN_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1921836 (x : real) : term0 x.
Proof. exact (@lem1919069 x). Qed.
Lemma lem1921837 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1921838 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1921837 x) (@lem1921836 x)). Qed.
Lemma lem1921848 (x : real) : (term2 x) = (real_sgn x).
Proof. exact (proj1 (@lem1921838 x)). Qed.
Lemma lem1921849 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1921850 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1921849) (@lem1921848 x)). Qed.
Lemma lem1921851 (x : real) : (real_sgn x) = (real_sgn x).
Proof. exact (eq_refl (real_sgn x)). Qed.
Lemma lem1921852 (x : real) : ((term2 x) = (real_sgn x)) = ((real_sgn x) = (real_sgn x)).
Proof. exact (MK_COMB (@lem1921850 x) (@lem1921851 x)). Qed.
Lemma lem1921854 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1921855 (x : real) : (x = x) = True.
Proof. exact (@lem1921854 real x). Qed.
Lemma lem1921856 (x : real) : ((real_sgn x) = (real_sgn x)) = True.
Proof. exact (@lem1921855 (real_sgn x)). Qed.
Lemma lem1921857 (x : real) : ((term2 x) = (real_sgn x)) = True.
Proof. exact (TRANS (@lem1921852 x) (@lem1921856 x)). Qed.
Lemma lem1921858 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem1921857 x)). Qed.
Lemma lem1921859 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1921860 : term7 = term8.
Proof. exact (MK_COMB (@lem1921859) (@lem1921858)). Qed.
Lemma lem1921862 {A : Type'} (t : Prop) : (term9 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1921863 (t : Prop) : (term10 t) = t.
Proof. exact (@lem1921862 real t). Qed.
Lemma lem1921864 : term8 = True.
Proof. exact (@lem1921863 True). Qed.
Lemma lem1921865 : term7 = True.
Proof. exact (TRANS (@lem1921860) (@lem1921864)). Qed.
Lemma lem1921866 : True = term7.
Proof. exact (SYM (@lem1921865)). Qed.
Lemma lem1921867 : term7.
Proof. exact (EQ_MP (@lem1921866) (@lem0)). Qed.
