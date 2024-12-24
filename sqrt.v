Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import sqrt_term_abbrevs.
Lemma lem1868792 : sqrt = term0.
Proof. exact (@sqrt_def). Qed.
Lemma lem1868793 (_27022 : real) : _27022 = _27022.
Proof. exact (eq_refl _27022). Qed.
Lemma lem1868794 (_27022 : real) : (sqrt _27022) = (term1 _27022).
Proof. exact (MK_COMB (@lem1868792) (@lem1868793 _27022)). Qed.
Lemma lem1868795 (_27022 : real) : (term1 _27022) = (term2 _27022).
Proof. exact (eq_refl (term1 _27022)). Qed.
Lemma lem1868796 (_27022 : real) : (sqrt _27022) = (term2 _27022).
Proof. exact (TRANS (@lem1868794 _27022) (@lem1868795 _27022)). Qed.
Lemma lem1868797 : term3.
Proof. exact (fun _27022 : real => @lem1868796 _27022). Qed.
Lemma lem1868798 (_27022 : real) : term4 _27022.
Proof. exact (@lem1868797 _27022). Qed.
Lemma lem1868799 (_27022 : real) : (term4 _27022) = ((sqrt _27022) = (term2 _27022)).
Proof. exact (eq_refl (term4 _27022)). Qed.
Lemma lem1868800 (_27022 : real) : (sqrt _27022) = (term2 _27022).
Proof. exact (EQ_MP (@lem1868799 _27022) (@lem1868798 _27022)). Qed.
Lemma lem1868830 (x : real) : (sqrt x) = (term2 x).
Proof. exact (@lem1868800 x). Qed.
Lemma lem1868831 : term3.
Proof. exact (fun x : real => @lem1868830 x). Qed.
