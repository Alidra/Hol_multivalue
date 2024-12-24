Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import nadd_add_term_abbrevs.
Lemma lem1273698 : nadd_add = term0.
Proof. exact (@nadd_add_def). Qed.
Lemma lem1273699 (_23184 : nadd) : _23184 = _23184.
Proof. exact (eq_refl _23184). Qed.
Lemma lem1273700 (_23184 : nadd) : (nadd_add _23184) = (term1 _23184).
Proof. exact (MK_COMB (@lem1273698) (@lem1273699 _23184)). Qed.
Lemma lem1273701 (_23184 : nadd) : (term1 _23184) = (term2 _23184).
Proof. exact (eq_refl (term1 _23184)). Qed.
Lemma lem1273702 (_23184 : nadd) : (nadd_add _23184) = (term2 _23184).
Proof. exact (TRANS (@lem1273700 _23184) (@lem1273701 _23184)). Qed.
Lemma lem1273703 (_23185 : nadd) : _23185 = _23185.
Proof. exact (eq_refl _23185). Qed.
Lemma lem1273704 (_23184 : nadd) (_23185 : nadd) : (nadd_add _23184 _23185) = (term3 _23184 _23185).
Proof. exact (MK_COMB (@lem1273702 _23184) (@lem1273703 _23185)). Qed.
Lemma lem1273705 (_23184 : nadd) (_23185 : nadd) : (term3 _23184 _23185) = (term4 _23184 _23185).
Proof. exact (eq_refl (term3 _23184 _23185)). Qed.
Lemma lem1273706 (_23184 : nadd) (_23185 : nadd) : (nadd_add _23184 _23185) = (term4 _23184 _23185).
Proof. exact (TRANS (@lem1273704 _23184 _23185) (@lem1273705 _23184 _23185)). Qed.
Lemma lem1273707 (_23184 : nadd) : term5 _23184.
Proof. exact (fun _23185 : nadd => @lem1273706 _23184 _23185). Qed.
Lemma lem1273708 : term6.
Proof. exact (fun _23184 : nadd => @lem1273707 _23184). Qed.
Lemma lem1273709 (_23184 : nadd) : term7 _23184.
Proof. exact (@lem1273708 _23184). Qed.
Lemma lem1273710 (_23184 : nadd) : (term7 _23184) = (term5 _23184).
Proof. exact (eq_refl (term7 _23184)). Qed.
Lemma lem1273711 (_23184 : nadd) : term5 _23184.
Proof. exact (EQ_MP (@lem1273710 _23184) (@lem1273709 _23184)). Qed.
Lemma lem1273712 (_23184 : nadd) (_23185 : nadd) : term8 _23184 _23185.
Proof. exact (@lem1273711 _23184 _23185). Qed.
Lemma lem1273713 (_23184 : nadd) (_23185 : nadd) : (term8 _23184 _23185) = ((nadd_add _23184 _23185) = (term4 _23184 _23185)).
Proof. exact (eq_refl (term8 _23184 _23185)). Qed.
Lemma lem1273714 (_23184 : nadd) (_23185 : nadd) : (nadd_add _23184 _23185) = (term4 _23184 _23185).
Proof. exact (EQ_MP (@lem1273713 _23184 _23185) (@lem1273712 _23184 _23185)). Qed.
Lemma lem1273757 (x : nadd) (y : nadd) : (nadd_add x y) = (term4 x y).
Proof. exact (@lem1273714 x y). Qed.
Lemma lem1273758 (x : nadd) : term5 x.
Proof. exact (fun y : nadd => @lem1273757 x y). Qed.
Lemma lem1273759 : term6.
Proof. exact (fun x : nadd => @lem1273758 x). Qed.
