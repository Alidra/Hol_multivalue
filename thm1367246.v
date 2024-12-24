Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367246_term_abbrevs.
Require Import REAL_MUL_LNEG_spec.
Require Import REAL_MUL_RNEG_spec.
Require Import REAL_NEG_NEG_spec.
Require Import thm0_spec.
Require Import thm1340396_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1367112 (m : nat) : term0 m.
Proof. exact (@lem1340396 m). Qed.
Lemma lem1367113 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1367114 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1367113 m) (@lem1367112 m)). Qed.
Lemma lem1367115 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1367114 m n). Qed.
Lemma lem1367116 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1367118 (x : real) : term5 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem1367119 (x : real) : (term5 x) = ((term6 x) = x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1367121 (x : real) : term7 x.
Proof. exact (@lem1360282 x). Qed.
Lemma lem1367122 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1367123 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1367122 x) (@lem1367121 x)). Qed.
Lemma lem1367124 (x : real) (y : real) : term9 x y.
Proof. exact (@lem1367123 x y). Qed.
Lemma lem1367125 (x : real) (y : real) : (term9 x y) = ((term10 x y) = (term11 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1367127 (x : real) : term12 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem1367128 (x : real) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1367129 (x : real) : term13 x.
Proof. exact (EQ_MP (@lem1367128 x) (@lem1367127 x)). Qed.
Lemma lem1367130 (x : real) (y : real) : term14 x y.
Proof. exact (@lem1367129 x y). Qed.
Lemma lem1367131 (x : real) (y : real) : (term14 x y) = ((term15 x y) = (term11 x y)).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem1367142 (x : real) (y : real) : (term15 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1367131 x y) (@lem1367130 x y)). Qed.
Lemma lem1367143 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (@lem1367142 (real_of_num m) (term18 n)). Qed.
Lemma lem1367145 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1367125 x y) (@lem1367124 x y)). Qed.
Lemma lem1367146 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (@lem1367145 (real_of_num m) (real_of_num n)). Qed.
Lemma lem1367147 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1367148 (m : nat) (n : nat) : (term17 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem1367147) (@lem1367146 m n)). Qed.
Lemma lem1367150 (x : real) : (term6 x) = x.
Proof. exact (EQ_MP (@lem1367119 x) (@lem1367118 x)). Qed.
Lemma lem1367151 (m : nat) (n : nat) : (term21 m n) = (term3 m n).
Proof. exact (@lem1367150 (term3 m n)). Qed.
Lemma lem1367152 (m : nat) (n : nat) : (term17 m n) = (term3 m n).
Proof. exact (TRANS (@lem1367148 m n) (@lem1367151 m n)). Qed.
Lemma lem1367153 (m : nat) (n : nat) : (term16 m n) = (term3 m n).
Proof. exact (TRANS (@lem1367143 m n) (@lem1367152 m n)). Qed.
Lemma lem1367154 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367155 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem1367154) (@lem1367153 m n)). Qed.
Lemma lem1367156 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem1367157 (m : nat) (n : nat) : ((term16 m n) = (term4 m n)) = ((term3 m n) = (term4 m n)).
Proof. exact (MK_COMB (@lem1367155 m n) (@lem1367156 m n)). Qed.
Lemma lem1367160 (m : nat) (n : nat) : (term24 m n) = (term24 m n).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem1367161 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (MK_COMB (@lem1367160 m n) (@lem1367157 m n)). Qed.
Lemma lem1367163 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem1367164 (m : nat) (n : nat) : (term26 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (@lem1367163 ((term3 m n) = (term4 m n))). Qed.
Lemma lem1367167 (m : nat) (n : nat) : (term25 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (TRANS (@lem1367161 m n) (@lem1367164 m n)). Qed.
Lemma lem1367168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367169 (m : nat) (n : nat) : (term27 m n) = (term24 m n).
Proof. exact (MK_COMB (@lem1367168) (@lem1367167 m n)). Qed.
Lemma lem1367175 (x : real) (y : real) : (term15 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1367131 x y) (@lem1367130 x y)). Qed.
Lemma lem1367176 (m : nat) (n : nat) : (term28 m n) = (term20 m n).
Proof. exact (@lem1367175 (real_of_num m) (real_of_num n)). Qed.
Lemma lem1367177 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367178 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (MK_COMB (@lem1367177) (@lem1367176 m n)). Qed.
Lemma lem1367179 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem1367180 (m : nat) (n : nat) : ((term28 m n) = (term31 m n)) = ((term20 m n) = (term31 m n)).
Proof. exact (MK_COMB (@lem1367178 m n) (@lem1367179 m n)). Qed.
Lemma lem1367183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367184 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (MK_COMB (@lem1367183) (@lem1367180 m n)). Qed.
Lemma lem1367188 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1367125 x y) (@lem1367124 x y)). Qed.
Lemma lem1367189 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (@lem1367188 (real_of_num m) (real_of_num n)). Qed.
Lemma lem1367190 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367191 (m : nat) (n : nat) : (term34 m n) = (term30 m n).
Proof. exact (MK_COMB (@lem1367190) (@lem1367189 m n)). Qed.
Lemma lem1367192 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem1367193 (m : nat) (n : nat) : ((term19 m n) = (term31 m n)) = ((term20 m n) = (term31 m n)).
Proof. exact (MK_COMB (@lem1367191 m n) (@lem1367192 m n)). Qed.
Lemma lem1367196 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem1367184 m n) (@lem1367193 m n)). Qed.
Lemma lem1367198 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem1367199 (m : nat) (n : nat) : (term36 m n) = ((term20 m n) = (term31 m n)).
Proof. exact (@lem1367198 ((term20 m n) = (term31 m n))). Qed.
Lemma lem1367202 (m : nat) (n : nat) : (term35 m n) = ((term20 m n) = (term31 m n)).
Proof. exact (TRANS (@lem1367196 m n) (@lem1367199 m n)). Qed.
Lemma lem1367203 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem1367169 m n) (@lem1367202 m n)). Qed.
Lemma lem1367206 (m : nat) (n : nat) : (term38 m n) = (term37 m n).
Proof. exact (SYM (@lem1367203 m n)). Qed.
Lemma lem1367212 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1367116 m n) (@lem1367115 m n)). Qed.
Lemma lem1367213 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367214 (m : nat) (n : nat) : (term23 m n) = (term39 m n).
Proof. exact (MK_COMB (@lem1367213) (@lem1367212 m n)). Qed.
Lemma lem1367215 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem1367216 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term4 m n) = (term4 m n)).
Proof. exact (MK_COMB (@lem1367214 m n) (@lem1367215 m n)). Qed.
Lemma lem1367218 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367219 (x : real) : (x = x) = True.
Proof. exact (@lem1367218 real x). Qed.
Lemma lem1367220 (m : nat) (n : nat) : ((term4 m n) = (term4 m n)) = True.
Proof. exact (@lem1367219 (term4 m n)). Qed.
Lemma lem1367221 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = True.
Proof. exact (TRANS (@lem1367216 m n) (@lem1367220 m n)). Qed.
Lemma lem1367222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367223 (m : nat) (n : nat) : (term24 m n) = (and True).
Proof. exact (MK_COMB (@lem1367222) (@lem1367221 m n)). Qed.
Lemma lem1367227 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1367116 m n) (@lem1367115 m n)). Qed.
Lemma lem1367228 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1367229 (m : nat) (n : nat) : (term20 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem1367228) (@lem1367227 m n)). Qed.
Lemma lem1367230 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367231 (m : nat) (n : nat) : (term30 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem1367230) (@lem1367229 m n)). Qed.
Lemma lem1367232 (m : nat) (n : nat) : (term31 m n) = (term31 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem1367233 (m : nat) (n : nat) : ((term20 m n) = (term31 m n)) = ((term31 m n) = (term31 m n)).
Proof. exact (MK_COMB (@lem1367231 m n) (@lem1367232 m n)). Qed.
Lemma lem1367235 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367236 (x : real) : (x = x) = True.
Proof. exact (@lem1367235 real x). Qed.
Lemma lem1367237 (m : nat) (n : nat) : ((term31 m n) = (term31 m n)) = True.
Proof. exact (@lem1367236 (term31 m n)). Qed.
Lemma lem1367238 (m : nat) (n : nat) : ((term20 m n) = (term31 m n)) = True.
Proof. exact (TRANS (@lem1367233 m n) (@lem1367237 m n)). Qed.
Lemma lem1367239 (m : nat) (n : nat) : (term38 m n) = (True /\ True).
Proof. exact (MK_COMB (@lem1367223 m n) (@lem1367238 m n)). Qed.
Lemma lem1367241 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1367242 : (True /\ True) = True.
Proof. exact (@lem1367241 True). Qed.
Lemma lem1367243 (m : nat) (n : nat) : (term38 m n) = True.
Proof. exact (TRANS (@lem1367239 m n) (@lem1367242)). Qed.
Lemma lem1367244 (m : nat) (n : nat) : True = (term38 m n).
Proof. exact (SYM (@lem1367243 m n)). Qed.
Lemma lem1367245 (m : nat) (n : nat) : term38 m n.
Proof. exact (EQ_MP (@lem1367244 m n) (@lem0)). Qed.
Lemma lem1367246 (m : nat) (n : nat) : term37 m n.
Proof. exact (EQ_MP (@lem1367206 m n) (@lem1367245 m n)). Qed.
