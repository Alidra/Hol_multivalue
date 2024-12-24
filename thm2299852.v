Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299852_term_abbrevs.
Require Import int_min_th_spec.
Lemma lem2299841 (x : int) (y : int) (h1 : (term0 x y) = (term1 x y)) : (term0 x y) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem2299842 (x : int) (y : int) (h1 : (term0 x y) = (term1 x y)) : (term1 x y) = (term0 x y).
Proof. exact (SYM (@lem2299841 x y h1)). Qed.
Lemma lem2299843 (x : int) (y : int) (h1 : (term1 x y) = (term0 x y)) : (term1 x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2299844 (x : int) (y : int) (h1 : (term1 x y) = (term0 x y)) : (term0 x y) = (term1 x y).
Proof. exact (SYM (@lem2299843 x y h1)). Qed.
Lemma lem2299845 (x : int) (y : int) : ((term0 x y) = (term1 x y)) = ((term1 x y) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (term1 x y) => @lem2299842 x y h1) (fun h1 : (term1 x y) = (term0 x y) => @lem2299844 x y h1)). Qed.
Lemma lem2299846 (x : int) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun y : int => @lem2299845 x y)). Qed.
Lemma lem2299847 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299848 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2299847) (@lem2299846 x)). Qed.
Lemma lem2299849 : term6 = term7.
Proof. exact (fun_ext (fun x : int => @lem2299848 x)). Qed.
Lemma lem2299850 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299851 : term8 = term9.
Proof. exact (MK_COMB (@lem2299850) (@lem2299849)). Qed.
Lemma lem2299852 : term9.
Proof. exact (EQ_MP (@lem2299851) (@lem2293297)). Qed.
