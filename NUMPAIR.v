Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMPAIR_term_abbrevs.
Lemma lem1046813 : NUMPAIR = term0.
Proof. exact (@NUMPAIR_def). Qed.
Lemma lem1046814 (_17324 : nat) : _17324 = _17324.
Proof. exact (eq_refl _17324). Qed.
Lemma lem1046815 (_17324 : nat) : (NUMPAIR _17324) = (term1 _17324).
Proof. exact (MK_COMB (@lem1046813) (@lem1046814 _17324)). Qed.
Lemma lem1046816 (_17324 : nat) : (term1 _17324) = (term2 _17324).
Proof. exact (eq_refl (term1 _17324)). Qed.
Lemma lem1046817 (_17324 : nat) : (NUMPAIR _17324) = (term2 _17324).
Proof. exact (TRANS (@lem1046815 _17324) (@lem1046816 _17324)). Qed.
Lemma lem1046818 (_17325 : nat) : _17325 = _17325.
Proof. exact (eq_refl _17325). Qed.
Lemma lem1046819 (_17324 : nat) (_17325 : nat) : (NUMPAIR _17324 _17325) = (term3 _17324 _17325).
Proof. exact (MK_COMB (@lem1046817 _17324) (@lem1046818 _17325)). Qed.
Lemma lem1046820 (_17324 : nat) (_17325 : nat) : (term3 _17324 _17325) = (term4 _17324 _17325).
Proof. exact (eq_refl (term3 _17324 _17325)). Qed.
Lemma lem1046821 (_17324 : nat) (_17325 : nat) : (NUMPAIR _17324 _17325) = (term4 _17324 _17325).
Proof. exact (TRANS (@lem1046819 _17324 _17325) (@lem1046820 _17324 _17325)). Qed.
Lemma lem1046822 (_17324 : nat) : term5 _17324.
Proof. exact (fun _17325 : nat => @lem1046821 _17324 _17325). Qed.
Lemma lem1046823 : term6.
Proof. exact (fun _17324 : nat => @lem1046822 _17324). Qed.
Lemma lem1046824 (_17324 : nat) : term7 _17324.
Proof. exact (@lem1046823 _17324). Qed.
Lemma lem1046825 (_17324 : nat) : (term7 _17324) = (term5 _17324).
Proof. exact (eq_refl (term7 _17324)). Qed.
Lemma lem1046826 (_17324 : nat) : term5 _17324.
Proof. exact (EQ_MP (@lem1046825 _17324) (@lem1046824 _17324)). Qed.
Lemma lem1046827 (_17324 : nat) (_17325 : nat) : term8 _17324 _17325.
Proof. exact (@lem1046826 _17324 _17325). Qed.
Lemma lem1046828 (_17324 : nat) (_17325 : nat) : (term8 _17324 _17325) = ((NUMPAIR _17324 _17325) = (term4 _17324 _17325)).
Proof. exact (eq_refl (term8 _17324 _17325)). Qed.
Lemma lem1046829 (_17324 : nat) (_17325 : nat) : (NUMPAIR _17324 _17325) = (term4 _17324 _17325).
Proof. exact (EQ_MP (@lem1046828 _17324 _17325) (@lem1046827 _17324 _17325)). Qed.
Lemma lem1046872 (x : nat) (y : nat) : (NUMPAIR x y) = (term4 x y).
Proof. exact (@lem1046829 x y). Qed.
Lemma lem1046873 (x : nat) : term5 x.
Proof. exact (fun y : nat => @lem1046872 x y). Qed.
Lemma lem1046874 : term6.
Proof. exact (fun x : nat => @lem1046873 x). Qed.
