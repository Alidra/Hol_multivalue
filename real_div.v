Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_div_term_abbrevs.
Lemma lem1344875 : real_div = term0.
Proof. exact (@real_div_def). Qed.
Lemma lem1344876 (_23959 : real) : _23959 = _23959.
Proof. exact (eq_refl _23959). Qed.
Lemma lem1344877 (_23959 : real) : (real_div _23959) = (term1 _23959).
Proof. exact (MK_COMB (@lem1344875) (@lem1344876 _23959)). Qed.
Lemma lem1344878 (_23959 : real) : (term1 _23959) = (term2 _23959).
Proof. exact (eq_refl (term1 _23959)). Qed.
Lemma lem1344879 (_23959 : real) : (real_div _23959) = (term2 _23959).
Proof. exact (TRANS (@lem1344877 _23959) (@lem1344878 _23959)). Qed.
Lemma lem1344880 (_23960 : real) : _23960 = _23960.
Proof. exact (eq_refl _23960). Qed.
Lemma lem1344881 (_23959 : real) (_23960 : real) : (real_div _23959 _23960) = (term3 _23959 _23960).
Proof. exact (MK_COMB (@lem1344879 _23959) (@lem1344880 _23960)). Qed.
Lemma lem1344882 (_23959 : real) (_23960 : real) : (term3 _23959 _23960) = (term4 _23959 _23960).
Proof. exact (eq_refl (term3 _23959 _23960)). Qed.
Lemma lem1344883 (_23959 : real) (_23960 : real) : (real_div _23959 _23960) = (term4 _23959 _23960).
Proof. exact (TRANS (@lem1344881 _23959 _23960) (@lem1344882 _23959 _23960)). Qed.
Lemma lem1344884 (_23959 : real) : term5 _23959.
Proof. exact (fun _23960 : real => @lem1344883 _23959 _23960). Qed.
Lemma lem1344885 : term6.
Proof. exact (fun _23959 : real => @lem1344884 _23959). Qed.
Lemma lem1344886 (_23959 : real) : term7 _23959.
Proof. exact (@lem1344885 _23959). Qed.
Lemma lem1344887 (_23959 : real) : (term7 _23959) = (term5 _23959).
Proof. exact (eq_refl (term7 _23959)). Qed.
Lemma lem1344888 (_23959 : real) : term5 _23959.
Proof. exact (EQ_MP (@lem1344887 _23959) (@lem1344886 _23959)). Qed.
Lemma lem1344889 (_23959 : real) (_23960 : real) : term8 _23959 _23960.
Proof. exact (@lem1344888 _23959 _23960). Qed.
Lemma lem1344890 (_23959 : real) (_23960 : real) : (term8 _23959 _23960) = ((real_div _23959 _23960) = (term4 _23959 _23960)).
Proof. exact (eq_refl (term8 _23959 _23960)). Qed.
Lemma lem1344891 (_23959 : real) (_23960 : real) : (real_div _23959 _23960) = (term4 _23959 _23960).
Proof. exact (EQ_MP (@lem1344890 _23959 _23960) (@lem1344889 _23959 _23960)). Qed.
Lemma lem1344934 (x : real) (y : real) : (real_div x y) = (term4 x y).
Proof. exact (@lem1344891 x y). Qed.
Lemma lem1344935 (x : real) : term5 x.
Proof. exact (fun y : real => @lem1344934 x y). Qed.
Lemma lem1344936 : term6.
Proof. exact (fun x : real => @lem1344935 x). Qed.
