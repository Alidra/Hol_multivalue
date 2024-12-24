Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_gt_term_abbrevs.
Lemma lem1342707 : real_gt = term0.
Proof. exact (@real_gt_def). Qed.
Lemma lem1342708 (_23935 : real) : _23935 = _23935.
Proof. exact (eq_refl _23935). Qed.
Lemma lem1342709 (_23935 : real) : (real_gt _23935) = (term1 _23935).
Proof. exact (MK_COMB (@lem1342707) (@lem1342708 _23935)). Qed.
Lemma lem1342710 (_23935 : real) : (term1 _23935) = (term2 _23935).
Proof. exact (eq_refl (term1 _23935)). Qed.
Lemma lem1342711 (_23935 : real) : (real_gt _23935) = (term2 _23935).
Proof. exact (TRANS (@lem1342709 _23935) (@lem1342710 _23935)). Qed.
Lemma lem1342712 (_23936 : real) : _23936 = _23936.
Proof. exact (eq_refl _23936). Qed.
Lemma lem1342713 (_23935 : real) (_23936 : real) : (real_gt _23935 _23936) = (term3 _23935 _23936).
Proof. exact (MK_COMB (@lem1342711 _23935) (@lem1342712 _23936)). Qed.
Lemma lem1342714 (_23936 : real) (_23935 : real) : (term3 _23935 _23936) = (real_lt _23936 _23935).
Proof. exact (eq_refl (term3 _23935 _23936)). Qed.
Lemma lem1342715 (_23936 : real) (_23935 : real) : (real_gt _23935 _23936) = (real_lt _23936 _23935).
Proof. exact (TRANS (@lem1342713 _23935 _23936) (@lem1342714 _23936 _23935)). Qed.
Lemma lem1342716 (_23935 : real) : term4 _23935.
Proof. exact (fun _23936 : real => @lem1342715 _23936 _23935). Qed.
Lemma lem1342717 : term5.
Proof. exact (fun _23935 : real => @lem1342716 _23935). Qed.
Lemma lem1342718 (_23935 : real) : term6 _23935.
Proof. exact (@lem1342717 _23935). Qed.
Lemma lem1342719 (_23935 : real) : (term6 _23935) = (term4 _23935).
Proof. exact (eq_refl (term6 _23935)). Qed.
Lemma lem1342720 (_23935 : real) : term4 _23935.
Proof. exact (EQ_MP (@lem1342719 _23935) (@lem1342718 _23935)). Qed.
Lemma lem1342721 (_23935 : real) (_23936 : real) : term7 _23935 _23936.
Proof. exact (@lem1342720 _23935 _23936). Qed.
Lemma lem1342722 (_23936 : real) (_23935 : real) : (term7 _23935 _23936) = ((real_gt _23935 _23936) = (real_lt _23936 _23935)).
Proof. exact (eq_refl (term7 _23935 _23936)). Qed.
Lemma lem1342723 (_23936 : real) (_23935 : real) : (real_gt _23935 _23936) = (real_lt _23936 _23935).
Proof. exact (EQ_MP (@lem1342722 _23936 _23935) (@lem1342721 _23935 _23936)). Qed.
Lemma lem1342766 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (@lem1342723 y x). Qed.
Lemma lem1342767 (y : real) : term8 y.
Proof. exact (fun x : real => @lem1342766 y x). Qed.
Lemma lem1342768 : term9.
Proof. exact (fun y : real => @lem1342767 y). Qed.
