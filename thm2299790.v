Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299790_term_abbrevs.
Require Import int_mul_th_spec.
Lemma lem2299779 (x : int) (y : int) (h1 : (term0 x y) = (term1 x y)) : (term0 x y) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem2299780 (x : int) (y : int) (h1 : (term0 x y) = (term1 x y)) : (term1 x y) = (term0 x y).
Proof. exact (SYM (@lem2299779 x y h1)). Qed.
Lemma lem2299781 (x : int) (y : int) (h1 : (term1 x y) = (term0 x y)) : (term1 x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2299782 (x : int) (y : int) (h1 : (term1 x y) = (term0 x y)) : (term0 x y) = (term1 x y).
Proof. exact (SYM (@lem2299781 x y h1)). Qed.
Lemma lem2299783 (x : int) (y : int) : ((term0 x y) = (term1 x y)) = ((term1 x y) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (term1 x y) => @lem2299780 x y h1) (fun h1 : (term1 x y) = (term0 x y) => @lem2299782 x y h1)). Qed.
Lemma lem2299784 (x : int) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun y : int => @lem2299783 x y)). Qed.
Lemma lem2299785 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299786 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2299785) (@lem2299784 x)). Qed.
Lemma lem2299787 : term6 = term7.
Proof. exact (fun_ext (fun x : int => @lem2299786 x)). Qed.
Lemma lem2299788 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299789 : term8 = term9.
Proof. exact (MK_COMB (@lem2299788) (@lem2299787)). Qed.
Lemma lem2299790 : term9.
Proof. exact (EQ_MP (@lem2299789) (@lem2287415)). Qed.
