Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_DIV_REFL_term_abbrevs.
Require Import REAL_MUL_RINV_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem1592966 (x : real) : term0 x.
Proof. exact (@lem1591985 x). Qed.
Lemma lem1592967 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1592968 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1592967 x) (@lem1592966 x)). Qed.
Lemma lem1592969 (x : real) : (term1 x) = ((term1 x) = True).
Proof. exact (@lem7 (term1 x)). Qed.
Lemma lem1592971 (x : real) : term2 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1592972 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1592973 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1592972 x) (@lem1592971 x)). Qed.
Lemma lem1592974 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1592973 x y). Qed.
Lemma lem1592975 (x : real) (y : real) : (term4 x y) = ((real_div x y) = (term5 x y)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1592984 (x : real) (y : real) : (real_div x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1592975 x y) (@lem1592974 x y)). Qed.
Lemma lem1592985 (x : real) : (real_div x x) = (term6 x).
Proof. exact (@lem1592984 x x). Qed.
Lemma lem1592986 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1592987 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1592986) (@lem1592985 x)). Qed.
Lemma lem1592988 : term9 = term9.
Proof. exact (eq_refl term9). Qed.
Lemma lem1592989 (x : real) : ((real_div x x) = term9) = ((term6 x) = term9).
Proof. exact (MK_COMB (@lem1592987 x) (@lem1592988)). Qed.
Lemma lem1592992 (x : real) : (term10 x) = (term10 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1592993 (x : real) : (term11 x) = (term1 x).
Proof. exact (MK_COMB (@lem1592992 x) (@lem1592989 x)). Qed.
Lemma lem1592995 (x : real) : (term1 x) = True.
Proof. exact (EQ_MP (@lem1592969 x) (@lem1592968 x)). Qed.
Lemma lem1592996 (x : real) : (term11 x) = True.
Proof. exact (TRANS (@lem1592993 x) (@lem1592995 x)). Qed.
Lemma lem1592997 (x : real) : True = (term11 x).
Proof. exact (SYM (@lem1592996 x)). Qed.
Lemma lem1592998 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1592997 x) (@lem0)). Qed.
Lemma lem1593003 : term12.
Proof. exact (fun x : real => @lem1592998 x). Qed.
