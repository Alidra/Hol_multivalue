Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import nadd_eq_term_abbrevs.
Lemma lem1267869 : nadd_eq = term0.
Proof. exact (@nadd_eq_def). Qed.
Lemma lem1267870 (_23149 : nadd) : _23149 = _23149.
Proof. exact (eq_refl _23149). Qed.
Lemma lem1267871 (_23149 : nadd) : (nadd_eq _23149) = (term1 _23149).
Proof. exact (MK_COMB (@lem1267869) (@lem1267870 _23149)). Qed.
Lemma lem1267872 (_23149 : nadd) : (term1 _23149) = (term2 _23149).
Proof. exact (eq_refl (term1 _23149)). Qed.
Lemma lem1267873 (_23149 : nadd) : (nadd_eq _23149) = (term2 _23149).
Proof. exact (TRANS (@lem1267871 _23149) (@lem1267872 _23149)). Qed.
Lemma lem1267874 (_23150 : nadd) : _23150 = _23150.
Proof. exact (eq_refl _23150). Qed.
Lemma lem1267875 (_23149 : nadd) (_23150 : nadd) : (nadd_eq _23149 _23150) = (term3 _23149 _23150).
Proof. exact (MK_COMB (@lem1267873 _23149) (@lem1267874 _23150)). Qed.
Lemma lem1267876 (_23149 : nadd) (_23150 : nadd) : (term3 _23149 _23150) = (term4 _23149 _23150).
Proof. exact (eq_refl (term3 _23149 _23150)). Qed.
Lemma lem1267877 (_23149 : nadd) (_23150 : nadd) : (nadd_eq _23149 _23150) = (term4 _23149 _23150).
Proof. exact (TRANS (@lem1267875 _23149 _23150) (@lem1267876 _23149 _23150)). Qed.
Lemma lem1267878 (_23149 : nadd) : term5 _23149.
Proof. exact (fun _23150 : nadd => @lem1267877 _23149 _23150). Qed.
Lemma lem1267879 : term6.
Proof. exact (fun _23149 : nadd => @lem1267878 _23149). Qed.
Lemma lem1267880 (_23149 : nadd) : term7 _23149.
Proof. exact (@lem1267879 _23149). Qed.
Lemma lem1267881 (_23149 : nadd) : (term7 _23149) = (term5 _23149).
Proof. exact (eq_refl (term7 _23149)). Qed.
Lemma lem1267882 (_23149 : nadd) : term5 _23149.
Proof. exact (EQ_MP (@lem1267881 _23149) (@lem1267880 _23149)). Qed.
Lemma lem1267883 (_23149 : nadd) (_23150 : nadd) : term8 _23149 _23150.
Proof. exact (@lem1267882 _23149 _23150). Qed.
Lemma lem1267884 (_23149 : nadd) (_23150 : nadd) : (term8 _23149 _23150) = ((nadd_eq _23149 _23150) = (term4 _23149 _23150)).
Proof. exact (eq_refl (term8 _23149 _23150)). Qed.
Lemma lem1267885 (_23149 : nadd) (_23150 : nadd) : (nadd_eq _23149 _23150) = (term4 _23149 _23150).
Proof. exact (EQ_MP (@lem1267884 _23149 _23150) (@lem1267883 _23149 _23150)). Qed.
Lemma lem1267928 (x : nadd) (y : nadd) : (nadd_eq x y) = (term4 x y).
Proof. exact (@lem1267885 x y). Qed.
Lemma lem1267929 (x : nadd) : term5 x.
Proof. exact (fun y : nadd => @lem1267928 x y). Qed.
Lemma lem1267930 : term6.
Proof. exact (fun x : nadd => @lem1267929 x). Qed.
