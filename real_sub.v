Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_sub_term_abbrevs.
Lemma lem1340916 : real_sub = term0.
Proof. exact (@real_sub_def). Qed.
Lemma lem1340917 (_23899 : real) : _23899 = _23899.
Proof. exact (eq_refl _23899). Qed.
Lemma lem1340918 (_23899 : real) : (real_sub _23899) = (term1 _23899).
Proof. exact (MK_COMB (@lem1340916) (@lem1340917 _23899)). Qed.
Lemma lem1340919 (_23899 : real) : (term1 _23899) = (term2 _23899).
Proof. exact (eq_refl (term1 _23899)). Qed.
Lemma lem1340920 (_23899 : real) : (real_sub _23899) = (term2 _23899).
Proof. exact (TRANS (@lem1340918 _23899) (@lem1340919 _23899)). Qed.
Lemma lem1340921 (_23900 : real) : _23900 = _23900.
Proof. exact (eq_refl _23900). Qed.
Lemma lem1340922 (_23899 : real) (_23900 : real) : (real_sub _23899 _23900) = (term3 _23899 _23900).
Proof. exact (MK_COMB (@lem1340920 _23899) (@lem1340921 _23900)). Qed.
Lemma lem1340923 (_23899 : real) (_23900 : real) : (term3 _23899 _23900) = (term4 _23899 _23900).
Proof. exact (eq_refl (term3 _23899 _23900)). Qed.
Lemma lem1340924 (_23899 : real) (_23900 : real) : (real_sub _23899 _23900) = (term4 _23899 _23900).
Proof. exact (TRANS (@lem1340922 _23899 _23900) (@lem1340923 _23899 _23900)). Qed.
Lemma lem1340925 (_23899 : real) : term5 _23899.
Proof. exact (fun _23900 : real => @lem1340924 _23899 _23900). Qed.
Lemma lem1340926 : term6.
Proof. exact (fun _23899 : real => @lem1340925 _23899). Qed.
Lemma lem1340927 (_23899 : real) : term7 _23899.
Proof. exact (@lem1340926 _23899). Qed.
Lemma lem1340928 (_23899 : real) : (term7 _23899) = (term5 _23899).
Proof. exact (eq_refl (term7 _23899)). Qed.
Lemma lem1340929 (_23899 : real) : term5 _23899.
Proof. exact (EQ_MP (@lem1340928 _23899) (@lem1340927 _23899)). Qed.
Lemma lem1340930 (_23899 : real) (_23900 : real) : term8 _23899 _23900.
Proof. exact (@lem1340929 _23899 _23900). Qed.
Lemma lem1340931 (_23899 : real) (_23900 : real) : (term8 _23899 _23900) = ((real_sub _23899 _23900) = (term4 _23899 _23900)).
Proof. exact (eq_refl (term8 _23899 _23900)). Qed.
Lemma lem1340932 (_23899 : real) (_23900 : real) : (real_sub _23899 _23900) = (term4 _23899 _23900).
Proof. exact (EQ_MP (@lem1340931 _23899 _23900) (@lem1340930 _23899 _23900)). Qed.
Lemma lem1340975 (x : real) (y : real) : (real_sub x y) = (term4 x y).
Proof. exact (@lem1340932 x y). Qed.
Lemma lem1340976 (x : real) : term5 x.
Proof. exact (fun y : real => @lem1340975 x y). Qed.
Lemma lem1340977 : term6.
Proof. exact (fun x : real => @lem1340976 x). Qed.
