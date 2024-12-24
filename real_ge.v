Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_ge_term_abbrevs.
Lemma lem1342102 : real_ge = term0.
Proof. exact (@real_ge_def). Qed.
Lemma lem1342103 (_23923 : real) : _23923 = _23923.
Proof. exact (eq_refl _23923). Qed.
Lemma lem1342104 (_23923 : real) : (real_ge _23923) = (term1 _23923).
Proof. exact (MK_COMB (@lem1342102) (@lem1342103 _23923)). Qed.
Lemma lem1342105 (_23923 : real) : (term1 _23923) = (term2 _23923).
Proof. exact (eq_refl (term1 _23923)). Qed.
Lemma lem1342106 (_23923 : real) : (real_ge _23923) = (term2 _23923).
Proof. exact (TRANS (@lem1342104 _23923) (@lem1342105 _23923)). Qed.
Lemma lem1342107 (_23924 : real) : _23924 = _23924.
Proof. exact (eq_refl _23924). Qed.
Lemma lem1342108 (_23923 : real) (_23924 : real) : (real_ge _23923 _23924) = (term3 _23923 _23924).
Proof. exact (MK_COMB (@lem1342106 _23923) (@lem1342107 _23924)). Qed.
Lemma lem1342109 (_23924 : real) (_23923 : real) : (term3 _23923 _23924) = (real_le _23924 _23923).
Proof. exact (eq_refl (term3 _23923 _23924)). Qed.
Lemma lem1342110 (_23924 : real) (_23923 : real) : (real_ge _23923 _23924) = (real_le _23924 _23923).
Proof. exact (TRANS (@lem1342108 _23923 _23924) (@lem1342109 _23924 _23923)). Qed.
Lemma lem1342111 (_23923 : real) : term4 _23923.
Proof. exact (fun _23924 : real => @lem1342110 _23924 _23923). Qed.
Lemma lem1342112 : term5.
Proof. exact (fun _23923 : real => @lem1342111 _23923). Qed.
Lemma lem1342113 (_23923 : real) : term6 _23923.
Proof. exact (@lem1342112 _23923). Qed.
Lemma lem1342114 (_23923 : real) : (term6 _23923) = (term4 _23923).
Proof. exact (eq_refl (term6 _23923)). Qed.
Lemma lem1342115 (_23923 : real) : term4 _23923.
Proof. exact (EQ_MP (@lem1342114 _23923) (@lem1342113 _23923)). Qed.
Lemma lem1342116 (_23923 : real) (_23924 : real) : term7 _23923 _23924.
Proof. exact (@lem1342115 _23923 _23924). Qed.
Lemma lem1342117 (_23924 : real) (_23923 : real) : (term7 _23923 _23924) = ((real_ge _23923 _23924) = (real_le _23924 _23923)).
Proof. exact (eq_refl (term7 _23923 _23924)). Qed.
Lemma lem1342118 (_23924 : real) (_23923 : real) : (real_ge _23923 _23924) = (real_le _23924 _23923).
Proof. exact (EQ_MP (@lem1342117 _23924 _23923) (@lem1342116 _23923 _23924)). Qed.
Lemma lem1342161 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (@lem1342118 y x). Qed.
Lemma lem1342162 (y : real) : term8 y.
Proof. exact (fun x : real => @lem1342161 y x). Qed.
Lemma lem1342163 : term9.
Proof. exact (fun y : real => @lem1342162 y). Qed.
