Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_INV_0_term_abbrevs.
Require Import NADD_EQ_REFL_spec.
Require Import nadd_inv_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm7_spec.
Lemma lem1308985 (x : nadd) : term0 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1308986 (x : nadd) : (term0 x) = (nadd_eq x x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1308987 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1308986 x) (@lem1308985 x)). Qed.
Lemma lem1308988 (x : nadd) : (nadd_eq x x) = ((nadd_eq x x) = True).
Proof. exact (@lem7 (nadd_eq x x)). Qed.
Lemma lem1308990 (x : nadd) : term1 x.
Proof. exact (@lem1308008 x). Qed.
Lemma lem1308991 (x : nadd) : (term1 x) = ((nadd_inv x) = (term2 x)).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1308996 (x : nadd) : (nadd_inv x) = (term2 x).
Proof. exact (EQ_MP (@lem1308991 x) (@lem1308990 x)). Qed.
Lemma lem1308997 : term3 = term4.
Proof. exact (@lem1308996 term5). Qed.
Lemma lem1308999 (x : nadd) : (nadd_eq x x) = True.
Proof. exact (EQ_MP (@lem1308988 x) (@lem1308987 x)). Qed.
Lemma lem1309000 : term6 = True.
Proof. exact (@lem1308999 term5). Qed.
Lemma lem1309001 : (@COND nadd) = (@COND nadd).
Proof. exact (eq_refl (@COND nadd)). Qed.
Lemma lem1309002 : term7 = (@COND nadd True).
Proof. exact (MK_COMB (@lem1309001) (@lem1309000)). Qed.
Lemma lem1309003 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1309004 : term8 = term9.
Proof. exact (MK_COMB (@lem1309002) (@lem1309003)). Qed.
Lemma lem1309005 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1309006 : term4 = term11.
Proof. exact (MK_COMB (@lem1309004) (@lem1309005)). Qed.
Lemma lem1309008 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1309009 (t2 : nadd) (t1 : nadd) : (@COND nadd True t1 t2) = t1.
Proof. exact (@lem1309008 nadd t2 t1). Qed.
Lemma lem1309010 : term11 = term5.
Proof. exact (@lem1309009 term10 term5). Qed.
Lemma lem1309011 : term4 = term5.
Proof. exact (TRANS (@lem1309006) (@lem1309010)). Qed.
Lemma lem1309012 : term3 = term5.
Proof. exact (TRANS (@lem1308997) (@lem1309011)). Qed.
Lemma lem1309013 : nadd_eq = nadd_eq.
Proof. exact (eq_refl nadd_eq). Qed.
Lemma lem1309014 : term12 = term13.
Proof. exact (MK_COMB (@lem1309013) (@lem1309012)). Qed.
Lemma lem1309015 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1309016 : term14 = term6.
Proof. exact (MK_COMB (@lem1309014) (@lem1309015)). Qed.
Lemma lem1309018 (x : nadd) : (nadd_eq x x) = True.
Proof. exact (EQ_MP (@lem1308988 x) (@lem1308987 x)). Qed.
Lemma lem1309019 : term6 = True.
Proof. exact (@lem1309018 term5). Qed.
Lemma lem1309020 : term14 = True.
Proof. exact (TRANS (@lem1309016) (@lem1309019)). Qed.
Lemma lem1309021 : True = term14.
Proof. exact (SYM (@lem1309020)). Qed.
Lemma lem1309022 : term14.
Proof. exact (EQ_MP (@lem1309021) (@lem0)). Qed.
