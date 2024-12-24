Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1592014_term_abbrevs.
Require Import REAL_MUL_RINV_UNIQ_spec.
Lemma lem1591989 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1591990 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1591989 h1 x). Qed.
Lemma lem1591991 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1591992 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1591991 x) (@lem1591990 x h1)). Qed.
Lemma lem1591993 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1591992 x h1 y). Qed.
Lemma lem1591994 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1591995 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (EQ_MP (@lem1591994 x y) (@lem1591993 x y h1)). Qed.
Lemma lem1591996 (x : real) (y : real) (h1 : (real_mul x y) = term5) : (real_mul x y) = term5.
Proof. exact (h1). Qed.
Lemma lem1591997 (x : real) (y : real) (h1 : term0) (h2 : (real_mul x y) = term5) : (real_inv x) = y.
Proof. exact (@lem1591995 x y h1 (@lem1591996 x y h2)). Qed.
Lemma lem1591998 (x : real) (y : real) (h1 : (real_mul x y) = term5) : term6 x y.
Proof. exact (fun h0 : term0 => @lem1591997 x y h0 h1). Qed.
Lemma lem1591999 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1592000 (x : real) (y : real) (h1 : term0) (h2 : (real_mul x y) = term5) : (real_inv x) = y.
Proof. exact (@lem1591998 x y h2 (@lem1591999 h1)). Qed.
Lemma lem1592001 (x : real) (y : real) (h1 : term0) : term4 x y.
Proof. exact (fun h0 : (real_mul x y) = term5 => @lem1592000 x y h1 h0). Qed.
Lemma lem1592002 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun y : real => @lem1592001 x y h1). Qed.
Lemma lem1592003 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1592002 x h1). Qed.
Lemma lem1592004 : term7.
Proof. exact (fun h0 : term0 => @lem1592003 h0). Qed.
Lemma lem1592005 : term0.
Proof. exact (@lem1592004 (@lem1587797)). Qed.
Lemma lem1592006 (x : real) : term1 x.
Proof. exact (@lem1592005 x). Qed.
Lemma lem1592007 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1592008 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1592007 x) (@lem1592006 x)). Qed.
Lemma lem1592009 (x : real) (y : real) : term3 x y.
Proof. exact (@lem1592008 x y). Qed.
Lemma lem1592010 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1592013 (x : real) (y : real) : term4 x y.
Proof. exact (EQ_MP (@lem1592010 x y) (@lem1592009 x y)). Qed.
Lemma lem1592014 : term8.
Proof. exact (@lem1592013 term5 term5). Qed.
