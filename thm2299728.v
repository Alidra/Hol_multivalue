Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299728_term_abbrevs.
Require Import int_ge_spec.
Lemma lem2299717 (x : int) (y : int) (h1 : (int_ge x y) = (term0 x y)) : (int_ge x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2299718 (x : int) (y : int) (h1 : (int_ge x y) = (term0 x y)) : (term0 x y) = (int_ge x y).
Proof. exact (SYM (@lem2299717 x y h1)). Qed.
Lemma lem2299719 (x : int) (y : int) (h1 : (term0 x y) = (int_ge x y)) : (term0 x y) = (int_ge x y).
Proof. exact (h1). Qed.
Lemma lem2299720 (x : int) (y : int) (h1 : (term0 x y) = (int_ge x y)) : (int_ge x y) = (term0 x y).
Proof. exact (SYM (@lem2299719 x y h1)). Qed.
Lemma lem2299721 (x : int) (y : int) : ((int_ge x y) = (term0 x y)) = ((term0 x y) = (int_ge x y)).
Proof. exact (prop_ext (fun h1 : (int_ge x y) = (term0 x y) => @lem2299718 x y h1) (fun h1 : (term0 x y) = (int_ge x y) => @lem2299720 x y h1)). Qed.
Lemma lem2299722 (x : int) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : int => @lem2299721 x y)). Qed.
Lemma lem2299723 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299724 (x : int) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem2299723) (@lem2299722 x)). Qed.
Lemma lem2299725 : term5 = term6.
Proof. exact (fun_ext (fun x : int => @lem2299724 x)). Qed.
Lemma lem2299726 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299727 : term7 = term8.
Proof. exact (MK_COMB (@lem2299726) (@lem2299725)). Qed.
Lemma lem2299728 : term8.
Proof. exact (EQ_MP (@lem2299727) (@lem2270452)). Qed.
