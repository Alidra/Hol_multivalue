Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299762_term_abbrevs.
Require Import int_neg_th_spec.
Lemma lem2299754 (x : int) (h1 : (term0 x) = (term1 x)) : (term0 x) = (term1 x).
Proof. exact (h1). Qed.
Lemma lem2299755 (x : int) (h1 : (term0 x) = (term1 x)) : (term1 x) = (term0 x).
Proof. exact (SYM (@lem2299754 x h1)). Qed.
Lemma lem2299756 (x : int) (h1 : (term1 x) = (term0 x)) : (term1 x) = (term0 x).
Proof. exact (h1). Qed.
Lemma lem2299757 (x : int) (h1 : (term1 x) = (term0 x)) : (term0 x) = (term1 x).
Proof. exact (SYM (@lem2299756 x h1)). Qed.
Lemma lem2299758 (x : int) : ((term0 x) = (term1 x)) = ((term1 x) = (term0 x)).
Proof. exact (prop_ext (fun h1 : (term0 x) = (term1 x) => @lem2299755 x h1) (fun h1 : (term1 x) = (term0 x) => @lem2299757 x h1)). Qed.
Lemma lem2299759 : term2 = term3.
Proof. exact (fun_ext (fun x : int => @lem2299758 x)). Qed.
Lemma lem2299760 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299761 : term4 = term5.
Proof. exact (MK_COMB (@lem2299760) (@lem2299759)). Qed.
Lemma lem2299762 : term5.
Proof. exact (EQ_MP (@lem2299761) (@lem2273074)). Qed.
