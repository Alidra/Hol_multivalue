Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2299742_term_abbrevs.
Require Import int_gt_spec.
Lemma lem2299731 (x : int) (y : int) (h1 : (int_gt x y) = (term0 x y)) : (int_gt x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2299732 (x : int) (y : int) (h1 : (int_gt x y) = (term0 x y)) : (term0 x y) = (int_gt x y).
Proof. exact (SYM (@lem2299731 x y h1)). Qed.
Lemma lem2299733 (x : int) (y : int) (h1 : (term0 x y) = (int_gt x y)) : (term0 x y) = (int_gt x y).
Proof. exact (h1). Qed.
Lemma lem2299734 (x : int) (y : int) (h1 : (term0 x y) = (int_gt x y)) : (int_gt x y) = (term0 x y).
Proof. exact (SYM (@lem2299733 x y h1)). Qed.
Lemma lem2299735 (x : int) (y : int) : ((int_gt x y) = (term0 x y)) = ((term0 x y) = (int_gt x y)).
Proof. exact (prop_ext (fun h1 : (int_gt x y) = (term0 x y) => @lem2299732 x y h1) (fun h1 : (term0 x y) = (int_gt x y) => @lem2299734 x y h1)). Qed.
Lemma lem2299736 (x : int) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : int => @lem2299735 x y)). Qed.
Lemma lem2299737 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299738 (x : int) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem2299737) (@lem2299736 x)). Qed.
Lemma lem2299739 : term5 = term6.
Proof. exact (fun_ext (fun x : int => @lem2299738 x)). Qed.
Lemma lem2299740 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2299741 : term7 = term8.
Proof. exact (MK_COMB (@lem2299740) (@lem2299739)). Qed.
Lemma lem2299742 : term8.
Proof. exact (EQ_MP (@lem2299741) (@lem2271143)). Qed.
