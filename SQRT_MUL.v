Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_MUL_term_abbrevs.
Require Import REAL_ABS_MUL_spec.
Require Import REAL_POW_MUL_spec.
Require Import REAL_SGN_MUL_spec.
Require Import SQRT_UNIQUE_GEN_spec.
Require Import SQRT_WORKS_GEN_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1947158 (x : real) : term0 x.
Proof. exact (@lem1582313 x). Qed.
Lemma lem1947159 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1947160 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1947159 x) (@lem1947158 x)). Qed.
Lemma lem1947161 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1947160 x y). Qed.
Lemma lem1947162 (x : real) (y : real) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1947164 (x : real) : term5 x.
Proof. exact (@lem1919069 x). Qed.
Lemma lem1947165 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1947166 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem1947165 x) (@lem1947164 x)). Qed.
Lemma lem1947169 (x : real) : term7 x.
Proof. exact (@lem1595570 x). Qed.
Lemma lem1947170 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1947171 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1947170 x) (@lem1947169 x)). Qed.
Lemma lem1947172 (x : real) (y : real) : term9 x y.
Proof. exact (@lem1947171 x y). Qed.
Lemma lem1947173 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1947174 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem1947173 x y) (@lem1947172 x y)). Qed.
Lemma lem1947175 (x : real) (y : real) (n : nat) : term11 x y n.
Proof. exact (@lem1947174 x y n). Qed.
Lemma lem1947176 (x : real) (y : real) (n : nat) : (term11 x y n) = ((term12 x y n) = (term13 x y n)).
Proof. exact (eq_refl (term11 x y n)). Qed.
Lemma lem1947178 (x : real) : term14 x.
Proof. exact (@lem1734254 x). Qed.
Lemma lem1947179 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1947180 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem1947179 x) (@lem1947178 x)). Qed.
Lemma lem1947181 (x : real) (y : real) : term16 x y.
Proof. exact (@lem1947180 x y). Qed.
Lemma lem1947182 (x : real) (y : real) : (term16 x y) = ((term17 x y) = (term18 x y)).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1947184 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem1947185 (x : real) (h1 : term19) : term20 x.
Proof. exact (@lem1947184 h1 x). Qed.
Lemma lem1947186 (x : real) : (term20 x) = (term21 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1947187 (x : real) (h1 : term19) : term21 x.
Proof. exact (EQ_MP (@lem1947186 x) (@lem1947185 x h1)). Qed.
Lemma lem1947188 (x : real) (y : real) (h1 : term19) : term22 x y.
Proof. exact (@lem1947187 x h1 y). Qed.
Lemma lem1947189 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (eq_refl (term22 x y)). Qed.
Lemma lem1947190 (x : real) (y : real) (h1 : term19) : term23 x y.
Proof. exact (EQ_MP (@lem1947189 x y) (@lem1947188 x y h1)). Qed.
Lemma lem1947191 (y : real) (x : real) (h1 : term24 y x) : term24 y x.
Proof. exact (h1). Qed.
Lemma lem1947192 (y : real) (x : real) (h1 : term19) (h2 : term24 y x) : (sqrt x) = y.
Proof. exact (@lem1947190 x y h1 (@lem1947191 y x h2)). Qed.
Lemma lem1947193 (y : real) (x : real) (h1 : term24 y x) : term25 x y.
Proof. exact (fun h0 : term19 => @lem1947192 y x h0 h1). Qed.
Lemma lem1947194 (h1 : term19) : term19.
Proof. exact (h1). Qed.
Lemma lem1947195 (y : real) (x : real) (h1 : term19) (h2 : term24 y x) : (sqrt x) = y.
Proof. exact (@lem1947193 y x h2 (@lem1947194 h1)). Qed.
Lemma lem1947196 (x : real) (y : real) (h1 : term19) : term23 x y.
Proof. exact (fun h0 : term24 y x => @lem1947195 y x h1 h0). Qed.
Lemma lem1947197 (x : real) (h1 : term19) : term21 x.
Proof. exact (fun y : real => @lem1947196 x y h1). Qed.
Lemma lem1947198 (h1 : term19) : term19.
Proof. exact (fun x : real => @lem1947197 x h1). Qed.
Lemma lem1947199 : term26.
Proof. exact (fun h0 : term19 => @lem1947198 h0). Qed.
Lemma lem1947200 : term19.
Proof. exact (@lem1947199 (@lem1921051)). Qed.
Lemma lem1947201 (x : real) : term20 x.
Proof. exact (@lem1947200 x). Qed.
Lemma lem1947202 (x : real) : (term20 x) = (term21 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1947203 (x : real) : term21 x.
Proof. exact (EQ_MP (@lem1947202 x) (@lem1947201 x)). Qed.
Lemma lem1947204 (x : real) (y : real) : term22 x y.
Proof. exact (@lem1947203 x y). Qed.
Lemma lem1947205 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (eq_refl (term22 x y)). Qed.
Lemma lem1947208 (x : real) (y : real) : term23 x y.
Proof. exact (EQ_MP (@lem1947205 x y) (@lem1947204 x y)). Qed.
Lemma lem1947209 (x : real) (y : real) : term27 x y.
Proof. exact (@lem1947208 (real_mul x y) (term28 x y)). Qed.
Lemma lem1947215 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem1947182 x y) (@lem1947181 x y)). Qed.
Lemma lem1947216 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (@lem1947215 (sqrt x) (sqrt y)). Qed.
Lemma lem1947218 (x : real) : (term31 x) = (real_sgn x).
Proof. exact (proj1 (@lem1947166 x)). Qed.
Lemma lem1947219 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1947220 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem1947219) (@lem1947218 x)). Qed.
Lemma lem1947222 (x : real) : (term31 x) = (real_sgn x).
Proof. exact (proj1 (@lem1947166 x)). Qed.
Lemma lem1947223 (y : real) : (term31 y) = (real_sgn y).
Proof. exact (@lem1947222 y). Qed.
Lemma lem1947224 (x : real) (y : real) : (term30 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem1947220 x) (@lem1947223 y)). Qed.
Lemma lem1947225 (x : real) (y : real) : (term29 x y) = (term18 x y).
Proof. exact (TRANS (@lem1947216 x y) (@lem1947224 x y)). Qed.
Lemma lem1947226 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1947227 (x : real) (y : real) : (term34 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1947226) (@lem1947225 x y)). Qed.
Lemma lem1947229 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem1947182 x y) (@lem1947181 x y)). Qed.
Lemma lem1947230 (x : real) (y : real) : ((term29 x y) = (term17 x y)) = ((term18 x y) = (term18 x y)).
Proof. exact (MK_COMB (@lem1947227 x y) (@lem1947229 x y)). Qed.
Lemma lem1947232 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1947233 (x : real) : (x = x) = True.
Proof. exact (@lem1947232 real x). Qed.
Lemma lem1947234 (x : real) (y : real) : ((term18 x y) = (term18 x y)) = True.
Proof. exact (@lem1947233 (term18 x y)). Qed.
Lemma lem1947235 (x : real) (y : real) : ((term29 x y) = (term17 x y)) = True.
Proof. exact (TRANS (@lem1947230 x y) (@lem1947234 x y)). Qed.
Lemma lem1947236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1947237 (x : real) (y : real) : (term36 x y) = (and True).
Proof. exact (MK_COMB (@lem1947236) (@lem1947235 x y)). Qed.
Lemma lem1947241 (x : real) (y : real) (n : nat) : (term12 x y n) = (term13 x y n).
Proof. exact (EQ_MP (@lem1947176 x y n) (@lem1947175 x y n)). Qed.
Lemma lem1947242 (x : real) (y : real) : (term37 x y) = (term38 x y).
Proof. exact (@lem1947241 (sqrt x) (sqrt y) term39). Qed.
Lemma lem1947244 (x : real) : (term40 x) = (real_abs x).
Proof. exact (proj2 (@lem1947166 x)). Qed.
Lemma lem1947245 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1947246 (x : real) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem1947245) (@lem1947244 x)). Qed.
Lemma lem1947248 (x : real) : (term40 x) = (real_abs x).
Proof. exact (proj2 (@lem1947166 x)). Qed.
Lemma lem1947249 (y : real) : (term40 y) = (real_abs y).
Proof. exact (@lem1947248 y). Qed.
Lemma lem1947250 (x : real) (y : real) : (term38 x y) = (term4 x y).
Proof. exact (MK_COMB (@lem1947246 x) (@lem1947249 y)). Qed.
Lemma lem1947251 (x : real) (y : real) : (term37 x y) = (term4 x y).
Proof. exact (TRANS (@lem1947242 x y) (@lem1947250 x y)). Qed.
Lemma lem1947252 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1947253 (x : real) (y : real) : (term43 x y) = (term44 x y).
Proof. exact (MK_COMB (@lem1947252) (@lem1947251 x y)). Qed.
Lemma lem1947255 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1947162 x y) (@lem1947161 x y)). Qed.
Lemma lem1947256 (x : real) (y : real) : ((term37 x y) = (term3 x y)) = ((term4 x y) = (term4 x y)).
Proof. exact (MK_COMB (@lem1947253 x y) (@lem1947255 x y)). Qed.
Lemma lem1947258 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1947259 (x : real) : (x = x) = True.
Proof. exact (@lem1947258 real x). Qed.
Lemma lem1947260 (x : real) (y : real) : ((term4 x y) = (term4 x y)) = True.
Proof. exact (@lem1947259 (term4 x y)). Qed.
Lemma lem1947261 (x : real) (y : real) : ((term37 x y) = (term3 x y)) = True.
Proof. exact (TRANS (@lem1947256 x y) (@lem1947260 x y)). Qed.
Lemma lem1947262 (x : real) (y : real) : (term45 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1947237 x y) (@lem1947261 x y)). Qed.
Lemma lem1947264 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1947265 : (True /\ True) = True.
Proof. exact (@lem1947264 True). Qed.
Lemma lem1947266 (x : real) (y : real) : (term45 x y) = True.
Proof. exact (TRANS (@lem1947262 x y) (@lem1947265)). Qed.
Lemma lem1947267 (x : real) (y : real) : True = (term45 x y).
Proof. exact (SYM (@lem1947266 x y)). Qed.
Lemma lem1947268 (x : real) (y : real) : term45 x y.
Proof. exact (EQ_MP (@lem1947267 x y) (@lem0)). Qed.
Lemma lem1947269 (x : real) (y : real) : (term46 x y) = (term28 x y).
Proof. exact (@lem1947209 x y (@lem1947268 x y)). Qed.
Lemma lem1947274 (x : real) : term47 x.
Proof. exact (fun y : real => @lem1947269 x y). Qed.
Lemma lem1947279 : term48.
Proof. exact (fun x : real => @lem1947274 x). Qed.
