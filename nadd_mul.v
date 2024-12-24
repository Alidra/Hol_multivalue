Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import nadd_mul_term_abbrevs.
Lemma lem1276705 : nadd_mul = term0.
Proof. exact (@nadd_mul_def). Qed.
Lemma lem1276706 (_23198 : nadd) : _23198 = _23198.
Proof. exact (eq_refl _23198). Qed.
Lemma lem1276707 (_23198 : nadd) : (nadd_mul _23198) = (term1 _23198).
Proof. exact (MK_COMB (@lem1276705) (@lem1276706 _23198)). Qed.
Lemma lem1276708 (_23198 : nadd) : (term1 _23198) = (term2 _23198).
Proof. exact (eq_refl (term1 _23198)). Qed.
Lemma lem1276709 (_23198 : nadd) : (nadd_mul _23198) = (term2 _23198).
Proof. exact (TRANS (@lem1276707 _23198) (@lem1276708 _23198)). Qed.
Lemma lem1276710 (_23199 : nadd) : _23199 = _23199.
Proof. exact (eq_refl _23199). Qed.
Lemma lem1276711 (_23198 : nadd) (_23199 : nadd) : (nadd_mul _23198 _23199) = (term3 _23198 _23199).
Proof. exact (MK_COMB (@lem1276709 _23198) (@lem1276710 _23199)). Qed.
Lemma lem1276712 (_23198 : nadd) (_23199 : nadd) : (term3 _23198 _23199) = (term4 _23198 _23199).
Proof. exact (eq_refl (term3 _23198 _23199)). Qed.
Lemma lem1276713 (_23198 : nadd) (_23199 : nadd) : (nadd_mul _23198 _23199) = (term4 _23198 _23199).
Proof. exact (TRANS (@lem1276711 _23198 _23199) (@lem1276712 _23198 _23199)). Qed.
Lemma lem1276714 (_23198 : nadd) : term5 _23198.
Proof. exact (fun _23199 : nadd => @lem1276713 _23198 _23199). Qed.
Lemma lem1276715 : term6.
Proof. exact (fun _23198 : nadd => @lem1276714 _23198). Qed.
Lemma lem1276716 (_23198 : nadd) : term7 _23198.
Proof. exact (@lem1276715 _23198). Qed.
Lemma lem1276717 (_23198 : nadd) : (term7 _23198) = (term5 _23198).
Proof. exact (eq_refl (term7 _23198)). Qed.
Lemma lem1276718 (_23198 : nadd) : term5 _23198.
Proof. exact (EQ_MP (@lem1276717 _23198) (@lem1276716 _23198)). Qed.
Lemma lem1276719 (_23198 : nadd) (_23199 : nadd) : term8 _23198 _23199.
Proof. exact (@lem1276718 _23198 _23199). Qed.
Lemma lem1276720 (_23198 : nadd) (_23199 : nadd) : (term8 _23198 _23199) = ((nadd_mul _23198 _23199) = (term4 _23198 _23199)).
Proof. exact (eq_refl (term8 _23198 _23199)). Qed.
Lemma lem1276721 (_23198 : nadd) (_23199 : nadd) : (nadd_mul _23198 _23199) = (term4 _23198 _23199).
Proof. exact (EQ_MP (@lem1276720 _23198 _23199) (@lem1276719 _23198 _23199)). Qed.
Lemma lem1276764 (x : nadd) (y : nadd) : (nadd_mul x y) = (term4 x y).
Proof. exact (@lem1276721 x y). Qed.
Lemma lem1276765 (x : nadd) : term5 x.
Proof. exact (fun y : nadd => @lem1276764 x y). Qed.
Lemma lem1276766 : term6.
Proof. exact (fun x : nadd => @lem1276765 x). Qed.
