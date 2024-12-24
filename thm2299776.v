Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299776_term_abbrevs.
Require Import int_add_th_spec.
Lemma lem2299765 (x : int) (y : int) (h1 : (term0 x y) = (term1 x y)) : (term0 x y) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem2299766 (x : int) (y : int) (h1 : (term0 x y) = (term1 x y)) : (term1 x y) = (term0 x y).
Proof. exact (SYM (@lem2299765 x y h1)). Qed.
Lemma lem2299767 (x : int) (y : int) (h1 : (term1 x y) = (term0 x y)) : (term1 x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2299768 (x : int) (y : int) (h1 : (term1 x y) = (term0 x y)) : (term0 x y) = (term1 x y).
Proof. exact (SYM (@lem2299767 x y h1)). Qed.
Lemma lem2299769 (x : int) (y : int) : ((term0 x y) = (term1 x y)) = ((term1 x y) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (term1 x y) => @lem2299766 x y h1) (fun h1 : (term1 x y) = (term0 x y) => @lem2299768 x y h1)). Qed.
Lemma lem2299770 (x : int) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun y : int => @lem2299769 x y)). Qed.
Lemma lem2299771 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299772 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2299771) (@lem2299770 x)). Qed.
Lemma lem2299773 : term6 = term7.
Proof. exact (fun_ext (fun x : int => @lem2299772 x)). Qed.
Lemma lem2299774 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299775 : term8 = term9.
Proof. exact (MK_COMB (@lem2299774) (@lem2299773)). Qed.
Lemma lem2299776 : term9.
Proof. exact (EQ_MP (@lem2299775) (@lem2284714)). Qed.
