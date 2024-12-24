Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299824_term_abbrevs.
Require Import int_abs_th_spec.
Lemma lem2299816 (x : int) (h1 : (term0 x) = (term1 x)) : (term0 x) = (term1 x).
Proof. exact (h1). Qed.
Lemma lem2299817 (x : int) (h1 : (term0 x) = (term1 x)) : (term1 x) = (term0 x).
Proof. exact (SYM (@lem2299816 x h1)). Qed.
Lemma lem2299818 (x : int) (h1 : (term1 x) = (term0 x)) : (term1 x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem2299819 (x : int) (h1 : (term1 x) = (term0 x)) : (term0 x) = (term1 x).
Proof. exact (SYM (@lem2299818 x h1)). Qed.
Lemma lem2299820 (x : int) : ((term0 x) = (term1 x)) = ((term1 x) = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = (term1 x) => @lem2299817 x h1) (fun h1 : (term1 x) = (term0 x) => @lem2299819 x h1)). Qed.
Lemma lem2299821 : term2 = term3.
Proof. exact (fun_ext (fun x : int => @lem2299820 x)). Qed.
Lemma lem2299822 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299823 : term4 = term5.
Proof. exact (MK_COMB (@lem2299822) (@lem2299821)). Qed.
Lemma lem2299824 : term5.
Proof. exact (EQ_MP (@lem2299823) (@lem2288272)). Qed.
