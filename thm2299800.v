Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299800_term_abbrevs.
Require Import int_sgn_th_spec.
Lemma lem2299792 (x : int) (h1 : (term0 x) = (term1 x)) : (term0 x) = (term1 x).
Proof. exact (h1). Qed.
Lemma lem2299793 (x : int) (h1 : (term0 x) = (term1 x)) : (term1 x) = (term0 x).
Proof. exact (SYM (@lem2299792 x h1)). Qed.
Lemma lem2299794 (x : int) (h1 : (term1 x) = (term0 x)) : (term1 x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem2299795 (x : int) (h1 : (term1 x) = (term0 x)) : (term0 x) = (term1 x).
Proof. exact (SYM (@lem2299794 x h1)). Qed.
Lemma lem2299796 (x : int) : ((term0 x) = (term1 x)) = ((term1 x) = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = (term1 x) => @lem2299793 x h1) (fun h1 : (term1 x) = (term0 x) => @lem2299795 x h1)). Qed.
Lemma lem2299797 : term2 = term3.
Proof. exact (fun_ext (fun x : int => @lem2299796 x)). Qed.
Lemma lem2299798 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299799 : term4 = term5.
Proof. exact (MK_COMB (@lem2299798) (@lem2299797)). Qed.
Lemma lem2299800 : term5.
Proof. exact (EQ_MP (@lem2299799) (@lem2291527)). Qed.
