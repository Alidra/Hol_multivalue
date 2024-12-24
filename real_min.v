Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_min_term_abbrevs.
Lemma lem1346139 : real_min = term0.
Proof. exact (@real_min_def). Qed.
Lemma lem1346140 (_23983 : real) : _23983 = _23983.
Proof. exact (eq_refl _23983). Qed.
Lemma lem1346141 (_23983 : real) : (real_min _23983) = (term1 _23983).
Proof. exact (MK_COMB (@lem1346139) (@lem1346140 _23983)). Qed.
Lemma lem1346142 (_23983 : real) : (term1 _23983) = (term2 _23983).
Proof. exact (eq_refl (term1 _23983)). Qed.
Lemma lem1346143 (_23983 : real) : (real_min _23983) = (term2 _23983).
Proof. exact (TRANS (@lem1346141 _23983) (@lem1346142 _23983)). Qed.
Lemma lem1346144 (_23984 : real) : _23984 = _23984.
Proof. exact (eq_refl _23984). Qed.
Lemma lem1346145 (_23983 : real) (_23984 : real) : (real_min _23983 _23984) = (term3 _23983 _23984).
Proof. exact (MK_COMB (@lem1346143 _23983) (@lem1346144 _23984)). Qed.
Lemma lem1346146 (_23983 : real) (_23984 : real) : (term3 _23983 _23984) = (term4 _23983 _23984).
Proof. exact (eq_refl (term3 _23983 _23984)). Qed.
Lemma lem1346147 (_23983 : real) (_23984 : real) : (real_min _23983 _23984) = (term4 _23983 _23984).
Proof. exact (TRANS (@lem1346145 _23983 _23984) (@lem1346146 _23983 _23984)). Qed.
Lemma lem1346148 (_23983 : real) : term5 _23983.
Proof. exact (fun _23984 : real => @lem1346147 _23983 _23984). Qed.
Lemma lem1346149 : term6.
Proof. exact (fun _23983 : real => @lem1346148 _23983). Qed.
Lemma lem1346150 (_23983 : real) : term7 _23983.
Proof. exact (@lem1346149 _23983). Qed.
Lemma lem1346151 (_23983 : real) : (term7 _23983) = (term5 _23983).
Proof. exact (eq_refl (term7 _23983)). Qed.
Lemma lem1346152 (_23983 : real) : term5 _23983.
Proof. exact (EQ_MP (@lem1346151 _23983) (@lem1346150 _23983)). Qed.
Lemma lem1346153 (_23983 : real) (_23984 : real) : term8 _23983 _23984.
Proof. exact (@lem1346152 _23983 _23984). Qed.
Lemma lem1346154 (_23983 : real) (_23984 : real) : (term8 _23983 _23984) = ((real_min _23983 _23984) = (term4 _23983 _23984)).
Proof. exact (eq_refl (term8 _23983 _23984)). Qed.
Lemma lem1346155 (_23983 : real) (_23984 : real) : (real_min _23983 _23984) = (term4 _23983 _23984).
Proof. exact (EQ_MP (@lem1346154 _23983 _23984) (@lem1346153 _23983 _23984)). Qed.
Lemma lem1346198 (m : real) (n : real) : (real_min m n) = (term4 m n).
Proof. exact (@lem1346155 m n). Qed.
Lemma lem1346199 (m : real) : term5 m.
Proof. exact (fun n : real => @lem1346198 m n). Qed.
Lemma lem1346200 : term6.
Proof. exact (fun m : real => @lem1346199 m). Qed.
