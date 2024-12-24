Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_le_term_abbrevs.
Lemma lem2269033 : int_le = term0.
Proof. exact (@int_le_def). Qed.
Lemma lem2269034 (_28614 : int) : _28614 = _28614.
Proof. exact (eq_refl _28614). Qed.
Lemma lem2269035 (_28614 : int) : (int_le _28614) = (term1 _28614).
Proof. exact (MK_COMB (@lem2269033) (@lem2269034 _28614)). Qed.
Lemma lem2269036 (_28614 : int) : (term1 _28614) = (term2 _28614).
Proof. exact (eq_refl (term1 _28614)). Qed.
Lemma lem2269037 (_28614 : int) : (int_le _28614) = (term2 _28614).
Proof. exact (TRANS (@lem2269035 _28614) (@lem2269036 _28614)). Qed.
Lemma lem2269038 (_28615 : int) : _28615 = _28615.
Proof. exact (eq_refl _28615). Qed.
Lemma lem2269039 (_28614 : int) (_28615 : int) : (int_le _28614 _28615) = (term3 _28614 _28615).
Proof. exact (MK_COMB (@lem2269037 _28614) (@lem2269038 _28615)). Qed.
Lemma lem2269040 (_28614 : int) (_28615 : int) : (term3 _28614 _28615) = (term4 _28614 _28615).
Proof. exact (eq_refl (term3 _28614 _28615)). Qed.
Lemma lem2269041 (_28614 : int) (_28615 : int) : (int_le _28614 _28615) = (term4 _28614 _28615).
Proof. exact (TRANS (@lem2269039 _28614 _28615) (@lem2269040 _28614 _28615)). Qed.
Lemma lem2269042 (_28614 : int) : term5 _28614.
Proof. exact (fun _28615 : int => @lem2269041 _28614 _28615). Qed.
Lemma lem2269043 : term6.
Proof. exact (fun _28614 : int => @lem2269042 _28614). Qed.
Lemma lem2269044 (_28614 : int) : term7 _28614.
Proof. exact (@lem2269043 _28614). Qed.
Lemma lem2269045 (_28614 : int) : (term7 _28614) = (term5 _28614).
Proof. exact (eq_refl (term7 _28614)). Qed.
Lemma lem2269046 (_28614 : int) : term5 _28614.
Proof. exact (EQ_MP (@lem2269045 _28614) (@lem2269044 _28614)). Qed.
Lemma lem2269047 (_28614 : int) (_28615 : int) : term8 _28614 _28615.
Proof. exact (@lem2269046 _28614 _28615). Qed.
Lemma lem2269048 (_28614 : int) (_28615 : int) : (term8 _28614 _28615) = ((int_le _28614 _28615) = (term4 _28614 _28615)).
Proof. exact (eq_refl (term8 _28614 _28615)). Qed.
Lemma lem2269049 (_28614 : int) (_28615 : int) : (int_le _28614 _28615) = (term4 _28614 _28615).
Proof. exact (EQ_MP (@lem2269048 _28614 _28615) (@lem2269047 _28614 _28615)). Qed.
Lemma lem2269092 (x : int) (y : int) : (int_le x y) = (term4 x y).
Proof. exact (@lem2269049 x y). Qed.
Lemma lem2269093 (x : int) : term5 x.
Proof. exact (fun y : int => @lem2269092 x y). Qed.
Lemma lem2269094 : term6.
Proof. exact (fun x : int => @lem2269093 x). Qed.
