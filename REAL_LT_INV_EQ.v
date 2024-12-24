Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_INV_EQ_term_abbrevs.
Require Import REAL_INV_INV_spec.
Require Import REAL_LT_INV_spec.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem1589985 (x : real) : term0 x.
Proof. exact (@lem1589984 x). Qed.
Lemma lem1589986 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1589987 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1589986 x) (@lem1589985 x)). Qed.
Lemma lem1589988 (x : real) : (term1 x) = ((term1 x) = True).
Proof. exact (@lem7 (term1 x)). Qed.
Lemma lem1589991 (x : real) (h1 : (term2 x) = x) : (term2 x) = x.
Proof. exact (h1). Qed.
Lemma lem1589992 (x : real) (h1 : (term2 x) = x) : x = (term2 x).
Proof. exact (SYM (@lem1589991 x h1)). Qed.
Lemma lem1589993 (x : real) (h1 : x = (term2 x)) : x = (term2 x).
Proof. exact (h1). Qed.
Lemma lem1589994 (x : real) (h1 : x = (term2 x)) : (term2 x) = x.
Proof. exact (SYM (@lem1589993 x h1)). Qed.
Lemma lem1589995 (x : real) : ((term2 x) = x) = (x = (term2 x)).
Proof. exact (prop_ext (fun h1 : (term2 x) = x => @lem1589992 x h1) (fun h1 : x = (term2 x) => @lem1589994 x h1)). Qed.
Lemma lem1589996 : term3 = term4.
Proof. exact (fun_ext (fun x : real => @lem1589995 x)). Qed.
Lemma lem1589997 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1589998 : term5 = term6.
Proof. exact (MK_COMB (@lem1589997) (@lem1589996)). Qed.
Lemma lem1589999 : term6.
Proof. exact (EQ_MP (@lem1589998) (@lem1587920)). Qed.
Lemma lem1590000 (x : real) : term7 x.
Proof. exact (@lem1589999 x). Qed.
Lemma lem1590001 (x : real) : (term7 x) = (x = (term2 x)).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1590003 (x : real) : term0 x.
Proof. exact (@lem1589984 x). Qed.
Lemma lem1590004 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1590005 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1590004 x) (@lem1590003 x)). Qed.
Lemma lem1590006 (x : real) : (term1 x) = ((term1 x) = True).
Proof. exact (@lem7 (term1 x)). Qed.
Lemma lem1590013 (x : real) : (term1 x) = True.
Proof. exact (EQ_MP (@lem1590006 x) (@lem1590005 x)). Qed.
Lemma lem1590014 (x : real) : True = (term1 x).
Proof. exact (SYM (@lem1590013 x)). Qed.
Lemma lem1590015 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1590014 x) (@lem0)). Qed.
Lemma lem1590017 (x : real) : x = (term2 x).
Proof. exact (EQ_MP (@lem1590001 x) (@lem1590000 x)). Qed.
Lemma lem1590018 : term8 = term8.
Proof. exact (eq_refl term8). Qed.
Lemma lem1590019 (x : real) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1590018) (@lem1590017 x)). Qed.
Lemma lem1590020 (x : real) : (term11 x) = (term11 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1590021 (x : real) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem1590020 x) (@lem1590019 x)). Qed.
Lemma lem1590022 (x : real) : (term13 x) = (term12 x).
Proof. exact (SYM (@lem1590021 x)). Qed.
Lemma lem1590024 (x : real) : (term1 x) = True.
Proof. exact (EQ_MP (@lem1589988 x) (@lem1589987 x)). Qed.
Lemma lem1590025 (x : real) : (term13 x) = True.
Proof. exact (@lem1590024 (real_inv x)). Qed.
Lemma lem1590026 (x : real) : True = (term13 x).
Proof. exact (SYM (@lem1590025 x)). Qed.
Lemma lem1590027 (x : real) : term13 x.
Proof. exact (EQ_MP (@lem1590026 x) (@lem0)). Qed.
Lemma lem1590029 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1590022 x) (@lem1590027 x)). Qed.
Lemma lem1590030 (x : real) : term14 x.
Proof. exact (conj (@lem1590029 x) (@lem1590015 x)). Qed.
Lemma lem1590031 (x : real) : (term14 x) = ((term15 x) = (term9 x)).
Proof. exact (@lem32 (term15 x) (term9 x)). Qed.
Lemma lem1590032 (x : real) : (term15 x) = (term9 x).
Proof. exact (EQ_MP (@lem1590031 x) (@lem1590030 x)). Qed.
Lemma lem1590037 : term16.
Proof. exact (fun x : real => @lem1590032 x). Qed.
