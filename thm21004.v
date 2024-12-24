Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21004_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm20943_spec.
Lemma lem20978 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem20979 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem20980 : term0 = (or True).
Proof. exact (MK_COMB (@lem20979) (@lem20978)). Qed.
Lemma lem20981 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem20982 (b : Prop) : (term1 b) = (term2 b).
Proof. exact (MK_COMB (@lem20980) (@lem20981 b)). Qed.
Lemma lem20984 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem20985 (b : Prop) : (term2 b) = True.
Proof. exact (@lem20984 (~ b)). Qed.
Lemma lem20986 (b : Prop) : (term1 b) = True.
Proof. exact (TRANS (@lem20982 b) (@lem20985 b)). Qed.
Lemma lem20987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem20988 (b : Prop) : (term3 b) = (@eq Prop True).
Proof. exact (MK_COMB (@lem20987) (@lem20986 b)). Qed.
Lemma lem20990 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem20991 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem20990 b). Qed.
Lemma lem20992 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem20993 (b : Prop) : (term4 b) = (~ False).
Proof. exact (MK_COMB (@lem20992) (@lem20991 b)). Qed.
Lemma lem20995 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem20996 (b : Prop) : (term4 b) = True.
Proof. exact (TRANS (@lem20993 b) (@lem20995)). Qed.
Lemma lem20997 (b : Prop) : ((term1 b) = (term4 b)) = (True = True).
Proof. exact (MK_COMB (@lem20988 b) (@lem20996 b)). Qed.
Lemma lem20999 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem21000 : (True = True) = True.
Proof. exact (@lem20999 True). Qed.
Lemma lem21001 (b : Prop) : ((term1 b) = (term4 b)) = True.
Proof. exact (TRANS (@lem20997 b) (@lem21000)). Qed.
Lemma lem21002 (b : Prop) : True = ((term1 b) = (term4 b)).
Proof. exact (SYM (@lem21001 b)). Qed.
Lemma lem21003 (b : Prop) : (term1 b) = (term4 b).
Proof. exact (EQ_MP (@lem21002 b) (@lem0)). Qed.
Lemma lem21004 (b : Prop) (a : Prop) (h1 : a = False) : (term5 a b) = (term6 a b).
Proof. exact (EQ_MP (@lem20943 b a h1) (@lem21003 b)). Qed.
