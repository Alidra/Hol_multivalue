Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299814_term_abbrevs.
Require Import int_sub_th_spec.
Lemma lem2299803 (x : int) (y : int) (h1 : (term0 x y) = (term1 x y)) : (term0 x y) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem2299804 (x : int) (y : int) (h1 : (term0 x y) = (term1 x y)) : (term1 x y) = (term0 x y).
Proof. exact (SYM (@lem2299803 x y h1)). Qed.
Lemma lem2299805 (x : int) (y : int) (h1 : (term1 x y) = (term0 x y)) : (term1 x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2299806 (x : int) (y : int) (h1 : (term1 x y) = (term0 x y)) : (term0 x y) = (term1 x y).
Proof. exact (SYM (@lem2299805 x y h1)). Qed.
Lemma lem2299807 (x : int) (y : int) : ((term0 x y) = (term1 x y)) = ((term1 x y) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (term1 x y) => @lem2299804 x y h1) (fun h1 : (term1 x y) = (term0 x y) => @lem2299806 x y h1)). Qed.
Lemma lem2299808 (x : int) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun y : int => @lem2299807 x y)). Qed.
Lemma lem2299809 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299810 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2299809) (@lem2299808 x)). Qed.
Lemma lem2299811 : term6 = term7.
Proof. exact (fun_ext (fun x : int => @lem2299810 x)). Qed.
Lemma lem2299812 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299813 : term8 = term9.
Proof. exact (MK_COMB (@lem2299812) (@lem2299811)). Qed.
Lemma lem2299814 : term9.
Proof. exact (EQ_MP (@lem2299813) (@lem2285582)). Qed.
