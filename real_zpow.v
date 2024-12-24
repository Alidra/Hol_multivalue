Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_zpow_term_abbrevs.
Lemma lem3169103 : real_zpow = term0.
Proof. exact (@real_zpow_def). Qed.
Lemma lem3169104 (_32626 : real) : _32626 = _32626.
Proof. exact (eq_refl _32626). Qed.
Lemma lem3169105 (_32626 : real) : (real_zpow _32626) = (term1 _32626).
Proof. exact (MK_COMB (@lem3169103) (@lem3169104 _32626)). Qed.
Lemma lem3169106 (_32626 : real) : (term1 _32626) = (term2 _32626).
Proof. exact (eq_refl (term1 _32626)). Qed.
Lemma lem3169107 (_32626 : real) : (real_zpow _32626) = (term2 _32626).
Proof. exact (TRANS (@lem3169105 _32626) (@lem3169106 _32626)). Qed.
Lemma lem3169108 (_32627 : int) : _32627 = _32627.
Proof. exact (eq_refl _32627). Qed.
Lemma lem3169109 (_32626 : real) (_32627 : int) : (real_zpow _32626 _32627) = (term3 _32626 _32627).
Proof. exact (MK_COMB (@lem3169107 _32626) (@lem3169108 _32627)). Qed.
Lemma lem3169110 (_32626 : real) (_32627 : int) : (term3 _32626 _32627) = (term4 _32626 _32627).
Proof. exact (eq_refl (term3 _32626 _32627)). Qed.
Lemma lem3169111 (_32626 : real) (_32627 : int) : (real_zpow _32626 _32627) = (term4 _32626 _32627).
Proof. exact (TRANS (@lem3169109 _32626 _32627) (@lem3169110 _32626 _32627)). Qed.
Lemma lem3169112 (_32626 : real) : term5 _32626.
Proof. exact (fun _32627 : int => @lem3169111 _32626 _32627). Qed.
Lemma lem3169113 : term6.
Proof. exact (fun _32626 : real => @lem3169112 _32626). Qed.
Lemma lem3169114 (_32626 : real) : term7 _32626.
Proof. exact (@lem3169113 _32626). Qed.
Lemma lem3169115 (_32626 : real) : (term7 _32626) = (term5 _32626).
Proof. exact (eq_refl (term7 _32626)). Qed.
Lemma lem3169116 (_32626 : real) : term5 _32626.
Proof. exact (EQ_MP (@lem3169115 _32626) (@lem3169114 _32626)). Qed.
Lemma lem3169117 (_32626 : real) (_32627 : int) : term8 _32626 _32627.
Proof. exact (@lem3169116 _32626 _32627). Qed.
Lemma lem3169118 (_32626 : real) (_32627 : int) : (term8 _32626 _32627) = ((real_zpow _32626 _32627) = (term4 _32626 _32627)).
Proof. exact (eq_refl (term8 _32626 _32627)). Qed.
Lemma lem3169119 (_32626 : real) (_32627 : int) : (real_zpow _32626 _32627) = (term4 _32626 _32627).
Proof. exact (EQ_MP (@lem3169118 _32626 _32627) (@lem3169117 _32626 _32627)). Qed.
Lemma lem3169162 (z : real) (i : int) : (real_zpow z i) = (term4 z i).
Proof. exact (@lem3169119 z i). Qed.
Lemma lem3169163 (z : real) : term5 z.
Proof. exact (fun i : int => @lem3169162 z i). Qed.
Lemma lem3169164 : term6.
Proof. exact (fun z : real => @lem3169163 z). Qed.
