Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ADD_LINV_term_abbrevs.
Require Import thm1338588_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301133 (x : int) : term0 x.
Proof. exact (@lem1338588 (real_of_int x)). Qed.
Lemma lem2301134 (x : int) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301135 (x : int) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem2301134 x) (@lem2301133 x)). Qed.
Lemma lem2301137 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2301138 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2301139 (x : int) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem2301138) (@lem2301137 x)). Qed.
Lemma lem2301140 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2301141 (x : int) : (term1 x) = (term7 x).
Proof. exact (MK_COMB (@lem2301139 x) (@lem2301140 x)). Qed.
Lemma lem2301143 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301144 (x : int) : (term7 x) = (term10 x).
Proof. exact (@lem2301143 (int_neg x) x). Qed.
Lemma lem2301145 (x : int) : (term1 x) = (term10 x).
Proof. exact (TRANS (@lem2301141 x) (@lem2301144 x)). Qed.
Lemma lem2301146 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301147 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2301146) (@lem2301145 x)). Qed.
Lemma lem2301149 (n : nat) : (real_of_num n) = (term13 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301150 : term2 = term14.
Proof. exact (@lem2301149 (NUMERAL 0)). Qed.
Lemma lem2301151 (x : int) : ((term1 x) = term2) = ((term10 x) = term14).
Proof. exact (MK_COMB (@lem2301147 x) (@lem2301150)). Qed.
Lemma lem2301153 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301154 (x : int) : ((term10 x) = term14) = ((term15 x) = term16).
Proof. exact (@lem2301153 (term15 x) term16). Qed.
Lemma lem2301155 (x : int) : ((term1 x) = term2) = ((term15 x) = term16).
Proof. exact (TRANS (@lem2301151 x) (@lem2301154 x)). Qed.
Lemma lem2301156 (x : int) : (term15 x) = term16.
Proof. exact (EQ_MP (@lem2301155 x) (@lem2301135 x)). Qed.
Lemma lem2301157 : term17.
Proof. exact (fun x : int => @lem2301156 x). Qed.
