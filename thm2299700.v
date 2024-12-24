Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299700_term_abbrevs.
Require Import int_le_spec.
Lemma lem2299689 (x : int) (y : int) (h1 : (int_le x y) = (term0 x y)) : (int_le x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2299690 (x : int) (y : int) (h1 : (int_le x y) = (term0 x y)) : (term0 x y) = (int_le x y).
Proof. exact (SYM (@lem2299689 x y h1)). Qed.
Lemma lem2299691 (x : int) (y : int) (h1 : (term0 x y) = (int_le x y)) : (term0 x y) = (int_le x y).
Proof. exact (h1). Qed.
Lemma lem2299692 (x : int) (y : int) (h1 : (term0 x y) = (int_le x y)) : (int_le x y) = (term0 x y).
Proof. exact (SYM (@lem2299691 x y h1)). Qed.
Lemma lem2299693 (x : int) (y : int) : ((int_le x y) = (term0 x y)) = ((term0 x y) = (int_le x y)).
Proof. exact (prop_ext (fun h1 : (int_le x y) = (term0 x y) => @lem2299690 x y h1) (fun h1 : (term0 x y) = (int_le x y) => @lem2299692 x y h1)). Qed.
Lemma lem2299694 (x : int) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : int => @lem2299693 x y)). Qed.
Lemma lem2299695 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299696 (x : int) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem2299695) (@lem2299694 x)). Qed.
Lemma lem2299697 : term5 = term6.
Proof. exact (fun_ext (fun x : int => @lem2299696 x)). Qed.
Lemma lem2299698 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299699 : term7 = term8.
Proof. exact (MK_COMB (@lem2299698) (@lem2299697)). Qed.
Lemma lem2299700 : term8.
Proof. exact (EQ_MP (@lem2299699) (@lem2269094)). Qed.
