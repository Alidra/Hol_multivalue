Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1319042_term_abbrevs.
Require Import NADD_LE_REFL_spec.
Require Import thm1318142_spec.
Require Import thm1318147_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Lemma lem1319011 (x : nadd) (y : nadd) : (nadd_le x y) = (term0 x y).
Proof. exact (EQ_MP (@lem1318147 x y) (@lem1318142 x y)). Qed.
Lemma lem1319012 (x : nadd) : (nadd_le x x) = (term1 x).
Proof. exact (@lem1319011 x x). Qed.
Lemma lem1319013 : term2 = term3.
Proof. exact (fun_ext (fun x : nadd => @lem1319012 x)). Qed.
Lemma lem1319014 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319015 : term4 = term5.
Proof. exact (MK_COMB (@lem1319014) (@lem1319013)). Qed.
Lemma lem1319021 (P : hreal -> Prop) : (term6 P) = (term7 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1319022 : term8 = term9.
Proof. exact (@lem1319021 term10). Qed.
Lemma lem1319023 (x : nadd) : (term11 x) = (term1 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1319024 : term12 = term3.
Proof. exact (fun_ext (fun x : nadd => @lem1319023 x)). Qed.
Lemma lem1319025 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1319026 : term8 = term5.
Proof. exact (MK_COMB (@lem1319025) (@lem1319024)). Qed.
Lemma lem1319027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1319028 : term13 = term14.
Proof. exact (MK_COMB (@lem1319027) (@lem1319026)). Qed.
Lemma lem1319029 (x : hreal) : (term15 x) = (hreal_le x x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1319030 : term16 = term10.
Proof. exact (fun_ext (fun x : hreal => @lem1319029 x)). Qed.
Lemma lem1319031 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1319032 : term9 = term17.
Proof. exact (MK_COMB (@lem1319031) (@lem1319030)). Qed.
Lemma lem1319033 : (term8 = term9) = (term5 = term17).
Proof. exact (MK_COMB (@lem1319028) (@lem1319032)). Qed.
Lemma lem1319034 : term5 = term17.
Proof. exact (EQ_MP (@lem1319033) (@lem1319022)). Qed.
Lemma lem1319041 : term4 = term17.
Proof. exact (TRANS (@lem1319015) (@lem1319034)). Qed.
Lemma lem1319042 : term17.
Proof. exact (EQ_MP (@lem1319041) (@lem1270628)). Qed.
