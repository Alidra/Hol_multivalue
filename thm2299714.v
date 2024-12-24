Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299714_term_abbrevs.
Require Import int_lt_spec.
Lemma lem2299703 (x : int) (y : int) (h1 : (int_lt x y) = (term0 x y)) : (int_lt x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2299704 (x : int) (y : int) (h1 : (int_lt x y) = (term0 x y)) : (term0 x y) = (int_lt x y).
Proof. exact (SYM (@lem2299703 x y h1)). Qed.
Lemma lem2299705 (x : int) (y : int) (h1 : (term0 x y) = (int_lt x y)) : (term0 x y) = (int_lt x y).
Proof. exact (h1). Qed.
Lemma lem2299706 (x : int) (y : int) (h1 : (term0 x y) = (int_lt x y)) : (int_lt x y) = (term0 x y).
Proof. exact (SYM (@lem2299705 x y h1)). Qed.
Lemma lem2299707 (x : int) (y : int) : ((int_lt x y) = (term0 x y)) = ((term0 x y) = (int_lt x y)).
Proof. exact (prop_ext (fun h1 : (int_lt x y) = (term0 x y) => @lem2299704 x y h1) (fun h1 : (term0 x y) = (int_lt x y) => @lem2299706 x y h1)). Qed.
Lemma lem2299708 (x : int) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : int => @lem2299707 x y)). Qed.
Lemma lem2299709 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299710 (x : int) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem2299709) (@lem2299708 x)). Qed.
Lemma lem2299711 : term5 = term6.
Proof. exact (fun_ext (fun x : int => @lem2299710 x)). Qed.
Lemma lem2299712 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299713 : term7 = term8.
Proof. exact (MK_COMB (@lem2299712) (@lem2299711)). Qed.
Lemma lem2299714 : term8.
Proof. exact (EQ_MP (@lem2299713) (@lem2269769)). Qed.
