Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299838_term_abbrevs.
Require Import int_max_th_spec.
Lemma lem2299827 (x : int) (y : int) (h1 : (term0 x y) = (term1 x y)) : (term0 x y) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem2299828 (x : int) (y : int) (h1 : (term0 x y) = (term1 x y)) : (term1 x y) = (term0 x y).
Proof. exact (SYM (@lem2299827 x y h1)). Qed.
Lemma lem2299829 (x : int) (y : int) (h1 : (term1 x y) = (term0 x y)) : (term1 x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2299830 (x : int) (y : int) (h1 : (term1 x y) = (term0 x y)) : (term0 x y) = (term1 x y).
Proof. exact (SYM (@lem2299829 x y h1)). Qed.
Lemma lem2299831 (x : int) (y : int) : ((term0 x y) = (term1 x y)) = ((term1 x y) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (term1 x y) => @lem2299828 x y h1) (fun h1 : (term1 x y) = (term0 x y) => @lem2299830 x y h1)). Qed.
Lemma lem2299832 (x : int) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun y : int => @lem2299831 x y)). Qed.
Lemma lem2299833 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299834 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2299833) (@lem2299832 x)). Qed.
Lemma lem2299835 : term6 = term7.
Proof. exact (fun_ext (fun x : int => @lem2299834 x)). Qed.
Lemma lem2299836 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299837 : term8 = term9.
Proof. exact (MK_COMB (@lem2299836) (@lem2299835)). Qed.
Lemma lem2299838 : term9.
Proof. exact (EQ_MP (@lem2299837) (@lem2292408)). Qed.
