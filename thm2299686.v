Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299686_term_abbrevs.
Require Import int_eq_spec.
Lemma lem2299675 (x : int) (y : int) (h1 : (x = y) = ((real_of_int x) = (real_of_int y))) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (h1). Qed.
Lemma lem2299676 (x : int) (y : int) (h1 : (x = y) = ((real_of_int x) = (real_of_int y))) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (SYM (@lem2299675 x y h1)). Qed.
Lemma lem2299677 (x : int) (y : int) (h1 : ((real_of_int x) = (real_of_int y)) = (x = y)) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (h1). Qed.
Lemma lem2299678 (x : int) (y : int) (h1 : ((real_of_int x) = (real_of_int y)) = (x = y)) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (SYM (@lem2299677 x y h1)). Qed.
Lemma lem2299679 (x : int) (y : int) : ((x = y) = ((real_of_int x) = (real_of_int y))) = (((real_of_int x) = (real_of_int y)) = (x = y)).
Proof. exact (prop_ext (fun h1 : (x = y) = ((real_of_int x) = (real_of_int y)) => @lem2299676 x y h1) (fun h1 : ((real_of_int x) = (real_of_int y)) = (x = y) => @lem2299678 x y h1)). Qed.
Lemma lem2299680 (x : int) : (term0 x) = (term1 x).
Proof. exact (fun_ext (fun y : int => @lem2299679 x y)). Qed.
Lemma lem2299681 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299682 (x : int) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem2299681) (@lem2299680 x)). Qed.
Lemma lem2299683 : term4 = term5.
Proof. exact (fun_ext (fun x : int => @lem2299682 x)). Qed.
Lemma lem2299684 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299685 : term6 = term7.
Proof. exact (MK_COMB (@lem2299684) (@lem2299683)). Qed.
Lemma lem2299686 : term7.
Proof. exact (EQ_MP (@lem2299685) (@lem2268427)). Qed.
