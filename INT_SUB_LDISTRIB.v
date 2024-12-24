Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_LDISTRIB_term_abbrevs.
Require Import REAL_SUB_LDISTRIB_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310152 (x : int) : term0 x.
Proof. exact (@lem1526444 (real_of_int x)). Qed.
Lemma lem2310153 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310154 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310153 x) (@lem2310152 x)). Qed.
Lemma lem2310155 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310154 x (real_of_int y)). Qed.
Lemma lem2310156 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310157 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2310156 y x) (@lem2310155 x y)). Qed.
Lemma lem2310158 (y : int) (x : int) (z : int) : term4 y x z.
Proof. exact (@lem2310157 y x (real_of_int z)). Qed.
Lemma lem2310159 (y : int) (x : int) (z : int) : (term4 y x z) = ((term5 x y z) = (term6 y x z)).
Proof. exact (eq_refl (term4 y x z)). Qed.
Lemma lem2310160 (y : int) (x : int) (z : int) : (term5 x y z) = (term6 y x z).
Proof. exact (EQ_MP (@lem2310159 y x z) (@lem2310158 y x z)). Qed.
Lemma lem2310162 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310163 (y : int) (z : int) : (term7 y z) = (term8 y z).
Proof. exact (@lem2310162 y z). Qed.
Lemma lem2310164 (x : int) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2310165 (x : int) (y : int) (z : int) : (term5 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem2310164 x) (@lem2310163 y z)). Qed.
Lemma lem2310167 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2310168 (x : int) (y : int) (z : int) : (term10 x y z) = (term13 x y z).
Proof. exact (@lem2310167 x (int_sub y z)). Qed.
Lemma lem2310169 (x : int) (y : int) (z : int) : (term5 x y z) = (term13 x y z).
Proof. exact (TRANS (@lem2310165 x y z) (@lem2310168 x y z)). Qed.
Lemma lem2310170 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310171 (x : int) (y : int) (z : int) : (term14 x y z) = (term15 x y z).
Proof. exact (MK_COMB (@lem2310170) (@lem2310169 x y z)). Qed.
Lemma lem2310173 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2310174 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2310175 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2310174) (@lem2310173 x y)). Qed.
Lemma lem2310177 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2310178 (x : int) (z : int) : (term11 x z) = (term12 x z).
Proof. exact (@lem2310177 x z). Qed.
Lemma lem2310179 (y : int) (x : int) (z : int) : (term6 y x z) = (term18 y x z).
Proof. exact (MK_COMB (@lem2310175 x y) (@lem2310178 x z)). Qed.
Lemma lem2310181 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310182 (y : int) (x : int) (z : int) : (term18 y x z) = (term19 y x z).
Proof. exact (@lem2310181 (int_mul x y) (int_mul x z)). Qed.
Lemma lem2310183 (y : int) (x : int) (z : int) : (term6 y x z) = (term19 y x z).
Proof. exact (TRANS (@lem2310179 y x z) (@lem2310182 y x z)). Qed.
Lemma lem2310184 (y : int) (x : int) (z : int) : ((term5 x y z) = (term6 y x z)) = ((term13 x y z) = (term19 y x z)).
Proof. exact (MK_COMB (@lem2310171 x y z) (@lem2310183 y x z)). Qed.
Lemma lem2310186 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310187 (y : int) (x : int) (z : int) : ((term13 x y z) = (term19 y x z)) = ((term20 x y z) = (term21 y x z)).
Proof. exact (@lem2310186 (term20 x y z) (term21 y x z)). Qed.
Lemma lem2310188 (y : int) (x : int) (z : int) : ((term5 x y z) = (term6 y x z)) = ((term20 x y z) = (term21 y x z)).
Proof. exact (TRANS (@lem2310184 y x z) (@lem2310187 y x z)). Qed.
Lemma lem2310189 (y : int) (x : int) (z : int) : (term20 x y z) = (term21 y x z).
Proof. exact (EQ_MP (@lem2310188 y x z) (@lem2310160 y x z)). Qed.
Lemma lem2310190 (y : int) (x : int) : term22 y x.
Proof. exact (fun z : int => @lem2310189 y x z). Qed.
Lemma lem2310191 (x : int) : term23 x.
Proof. exact (fun y : int => @lem2310190 y x). Qed.
Lemma lem2310192 : term24.
Proof. exact (fun x : int => @lem2310191 x). Qed.
