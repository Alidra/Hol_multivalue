Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21384_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem21184 {A : Type'} (x : A) (y : A) : term0 A x y.
Proof. exact (@lem9784 (x = y)). Qed.
Lemma lem21185 {A : Type'} (x : A) (y : A) : (term0 A x y) = (term1 A x y).
Proof. exact (eq_refl (term0 A x y)). Qed.
Lemma lem21186 {A : Type'} (x : A) (y : A) : term1 A x y.
Proof. exact (EQ_MP (@lem21185 A x y) (@lem21184 A x y)). Qed.
Lemma lem21188 {A : Type'} (x : A) (y : A) (h1 : term2 A x y) : term2 A x y.
Proof. exact (h1). Qed.
Lemma lem21192 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem21193 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem21192 A x). Qed.
Lemma lem21194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem21195 {A : Type'} (x : A) : (term3 A x) = (and True).
Proof. exact (MK_COMB (@lem21194) (@lem21193 A x)). Qed.
Lemma lem21206 {A : Type'} (x : A) (y : A) (z : A) : (term4 A x y z) = (term4 A x y z).
Proof. exact (eq_refl (term4 A x y z)). Qed.
Lemma lem21207 {A : Type'} (x : A) (y : A) (z : A) : (term5 A x y z) = (term6 A x y z).
Proof. exact (MK_COMB (@lem21195 A x) (@lem21206 A x y z)). Qed.
Lemma lem21209 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem21210 {A : Type'} (x : A) (y : A) (z : A) : (term6 A x y z) = (term4 A x y z).
Proof. exact (@lem21209 (term4 A x y z)). Qed.
Lemma lem21221 {A : Type'} (x : A) (y : A) (z : A) : (term5 A x y z) = (term4 A x y z).
Proof. exact (TRANS (@lem21207 A x y z) (@lem21210 A x y z)). Qed.
Lemma lem21222 {A : Type'} (x : A) (y : A) (z : A) : (term4 A x y z) = (term5 A x y z).
Proof. exact (SYM (@lem21221 A x y z)). Qed.
Lemma lem21228 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem21229 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem21230 {A : Type'} (x : A) (y : A) (h1 : x = y) : (@eq A x) = (@eq A y).
Proof. exact (MK_COMB (@lem21229 A) (@lem21228 A x y h1)). Qed.
Lemma lem21231 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem21232 {A : Type'} (x : A) (y : A) (h1 : x = y) : (x = y) = (y = y).
Proof. exact (MK_COMB (@lem21230 A x y h1) (@lem21231 A y)). Qed.
Lemma lem21234 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem21235 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem21234 A x). Qed.
Lemma lem21236 {A : Type'} (y : A) : (y = y) = True.
Proof. exact (@lem21235 A y). Qed.
Lemma lem21237 {A : Type'} (x : A) (y : A) (h1 : x = y) : (x = y) = True.
Proof. exact (TRANS (@lem21232 A x y h1) (@lem21236 A y)). Qed.
Lemma lem21238 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem21239 {A : Type'} (x : A) (y : A) (h1 : x = y) : (term2 A x y) = (~ True).
Proof. exact (MK_COMB (@lem21238) (@lem21237 A x y h1)). Qed.
Lemma lem21241 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem21242 {A : Type'} (x : A) (y : A) (h1 : x = y) : (term2 A x y) = False.
Proof. exact (TRANS (@lem21239 A x y h1) (@lem21241)). Qed.
Lemma lem21243 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem21244 {A : Type'} (x : A) (y : A) (h1 : x = y) : (term7 A x y) = (or False).
Proof. exact (MK_COMB (@lem21243) (@lem21242 A x y h1)). Qed.
Lemma lem21250 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem21251 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem21252 {A : Type'} (x : A) (y : A) (h1 : x = y) : (@eq A x) = (@eq A y).
Proof. exact (MK_COMB (@lem21251 A) (@lem21250 A x y h1)). Qed.
Lemma lem21253 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem21254 {A : Type'} (z : A) (x : A) (y : A) (h1 : x = y) : (x = z) = (y = z).
Proof. exact (MK_COMB (@lem21252 A x y h1) (@lem21253 A z)). Qed.
Lemma lem21257 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem21258 {A : Type'} (z : A) (x : A) (y : A) (h1 : x = y) : (term2 A x z) = (term2 A y z).
Proof. exact (MK_COMB (@lem21257) (@lem21254 A z x y h1)). Qed.
Lemma lem21259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem21260 {A : Type'} (z : A) (x : A) (y : A) (h1 : x = y) : (term7 A x z) = (term7 A y z).
Proof. exact (MK_COMB (@lem21259) (@lem21258 A z x y h1)). Qed.
Lemma lem21263 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem21264 {A : Type'} (z : A) (x : A) (y : A) (h1 : x = y) : (term8 A x y z) = (term9 A y z).
Proof. exact (MK_COMB (@lem21260 A z x y h1) (@lem21263 A y z)). Qed.
Lemma lem21267 {A : Type'} (z : A) (x : A) (y : A) (h1 : x = y) : (term4 A x y z) = (term10 A y z).
Proof. exact (MK_COMB (@lem21244 A x y h1) (@lem21264 A z x y h1)). Qed.
Lemma lem21269 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem21270 {A : Type'} (y : A) (z : A) : (term10 A y z) = (term9 A y z).
Proof. exact (@lem21269 (term9 A y z)). Qed.
Lemma lem21277 {A : Type'} (z : A) (x : A) (y : A) (h1 : x = y) : (term4 A x y z) = (term9 A y z).
Proof. exact (TRANS (@lem21267 A z x y h1) (@lem21270 A y z)). Qed.
Lemma lem21278 {A : Type'} (z : A) (x : A) (y : A) (h1 : x = y) : (term9 A y z) = (term4 A x y z).
Proof. exact (SYM (@lem21277 A z x y h1)). Qed.
Lemma lem21279 {A : Type'} (x : A) (y : A) : term11 A x y.
Proof. exact (@lem82 (x = y)). Qed.
Lemma lem21295 {A : Type'} (x : A) (y : A) (h1 : term2 A x y) : (x = y) = False.
Proof. exact (@lem21279 A x y (@lem21188 A x y h1)). Qed.
Lemma lem21296 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem21297 {A : Type'} (x : A) (y : A) (h1 : term2 A x y) : (term2 A x y) = (~ False).
Proof. exact (MK_COMB (@lem21296) (@lem21295 A x y h1)). Qed.
Lemma lem21299 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem21300 {A : Type'} (x : A) (y : A) (h1 : term2 A x y) : (term2 A x y) = True.
Proof. exact (TRANS (@lem21297 A x y h1) (@lem21299)). Qed.
Lemma lem21301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem21302 {A : Type'} (x : A) (y : A) (h1 : term2 A x y) : (term7 A x y) = (or True).
Proof. exact (MK_COMB (@lem21301) (@lem21300 A x y h1)). Qed.
Lemma lem21309 {A : Type'} (x : A) (y : A) (z : A) : (term8 A x y z) = (term8 A x y z).
Proof. exact (eq_refl (term8 A x y z)). Qed.
Lemma lem21310 {A : Type'} (z : A) (x : A) (y : A) (h1 : term2 A x y) : (term4 A x y z) = (term12 A x y z).
Proof. exact (MK_COMB (@lem21302 A x y h1) (@lem21309 A x y z)). Qed.
Lemma lem21312 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem21313 {A : Type'} (x : A) (y : A) (z : A) : (term12 A x y z) = True.
Proof. exact (@lem21312 (term8 A x y z)). Qed.
Lemma lem21314 {A : Type'} (z : A) (x : A) (y : A) (h1 : term2 A x y) : (term4 A x y z) = True.
Proof. exact (TRANS (@lem21310 A z x y h1) (@lem21313 A x y z)). Qed.
Lemma lem21315 {A : Type'} (z : A) (x : A) (y : A) (h1 : term2 A x y) : True = (term4 A x y z).
Proof. exact (SYM (@lem21314 A z x y h1)). Qed.
Lemma lem21316 {A : Type'} (z : A) (x : A) (y : A) (h1 : term2 A x y) : term4 A x y z.
Proof. exact (EQ_MP (@lem21315 A z x y h1) (@lem0)). Qed.
Lemma lem21325 {A : Type'} (y : A) (z : A) : term13 A y z.
Proof. exact (@lem9851 (y = z)). Qed.
Lemma lem21326 {A : Type'} (y : A) (z : A) : (term13 A y z) = (term14 A y z).
Proof. exact (eq_refl (term13 A y z)). Qed.
Lemma lem21327 {A : Type'} (y : A) (z : A) : term14 A y z.
Proof. exact (EQ_MP (@lem21326 A y z) (@lem21325 A y z)). Qed.
Lemma lem21328 {A : Type'} (y : A) (z : A) (h1 : (y = z) = True) : (y = z) = True.
Proof. exact (h1). Qed.
Lemma lem21329 {A : Type'} (y : A) (z : A) (h1 : (y = z) = False) : (y = z) = False.
Proof. exact (h1). Qed.
Lemma lem21338 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem21339 {A : Type'} (y : A) (z : A) (h1 : (y = z) = True) : (term16 A y z) = term17.
Proof. exact (MK_COMB (@lem21338) (@lem21328 A y z h1)). Qed.
Lemma lem21340 : term17 = term18.
Proof. exact (eq_refl term17). Qed.
Lemma lem21341 {A : Type'} (y : A) (z : A) : (term19 A y z) = (term19 A y z).
Proof. exact (eq_refl (term19 A y z)). Qed.
Lemma lem21342 {A : Type'} (y : A) (z : A) : ((term16 A y z) = term17) = ((term16 A y z) = term18).
Proof. exact (MK_COMB (@lem21341 A y z) (@lem21340)). Qed.
Lemma lem21343 {A : Type'} (y : A) (z : A) : (term16 A y z) = (term9 A y z).
Proof. exact (eq_refl (term16 A y z)). Qed.
Lemma lem21344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21345 {A : Type'} (y : A) (z : A) : (term19 A y z) = (term20 A y z).
Proof. exact (MK_COMB (@lem21344) (@lem21343 A y z)). Qed.
Lemma lem21346 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem21347 {A : Type'} (y : A) (z : A) : ((term16 A y z) = term18) = ((term9 A y z) = term18).
Proof. exact (MK_COMB (@lem21345 A y z) (@lem21346)). Qed.
Lemma lem21348 {A : Type'} (y : A) (z : A) : ((term16 A y z) = term17) = ((term9 A y z) = term18).
Proof. exact (TRANS (@lem21342 A y z) (@lem21347 A y z)). Qed.
Lemma lem21349 {A : Type'} (y : A) (z : A) (h1 : (y = z) = True) : (term9 A y z) = term18.
Proof. exact (EQ_MP (@lem21348 A y z) (@lem21339 A y z h1)). Qed.
Lemma lem21350 {A : Type'} (y : A) (z : A) (h1 : (y = z) = True) : term18 = (term9 A y z).
Proof. exact (SYM (@lem21349 A y z h1)). Qed.
Lemma lem21351 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem21352 {A : Type'} (y : A) (z : A) (h1 : (y = z) = False) : (term16 A y z) = term21.
Proof. exact (MK_COMB (@lem21351) (@lem21329 A y z h1)). Qed.
Lemma lem21353 : term21 = term22.
Proof. exact (eq_refl term21). Qed.
Lemma lem21354 {A : Type'} (y : A) (z : A) : (term19 A y z) = (term19 A y z).
Proof. exact (eq_refl (term19 A y z)). Qed.
Lemma lem21355 {A : Type'} (y : A) (z : A) : ((term16 A y z) = term21) = ((term16 A y z) = term22).
Proof. exact (MK_COMB (@lem21354 A y z) (@lem21353)). Qed.
Lemma lem21356 {A : Type'} (y : A) (z : A) : (term16 A y z) = (term9 A y z).
Proof. exact (eq_refl (term16 A y z)). Qed.
Lemma lem21357 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21358 {A : Type'} (y : A) (z : A) : (term19 A y z) = (term20 A y z).
Proof. exact (MK_COMB (@lem21357) (@lem21356 A y z)). Qed.
Lemma lem21359 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem21360 {A : Type'} (y : A) (z : A) : ((term16 A y z) = term22) = ((term9 A y z) = term22).
Proof. exact (MK_COMB (@lem21358 A y z) (@lem21359)). Qed.
Lemma lem21361 {A : Type'} (y : A) (z : A) : ((term16 A y z) = term21) = ((term9 A y z) = term22).
Proof. exact (TRANS (@lem21355 A y z) (@lem21360 A y z)). Qed.
Lemma lem21362 {A : Type'} (y : A) (z : A) (h1 : (y = z) = False) : (term9 A y z) = term22.
Proof. exact (EQ_MP (@lem21361 A y z) (@lem21352 A y z h1)). Qed.
Lemma lem21363 {A : Type'} (y : A) (z : A) (h1 : (y = z) = False) : term22 = (term9 A y z).
Proof. exact (SYM (@lem21362 A y z h1)). Qed.
Lemma lem21365 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem21366 : term18 = True.
Proof. exact (@lem21365 (~ True)). Qed.
Lemma lem21367 : True = term18.
Proof. exact (SYM (@lem21366)). Qed.
Lemma lem21368 : term18.
Proof. exact (EQ_MP (@lem21367) (@lem0)). Qed.
Lemma lem21370 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem21371 : term22 = (~ False).
Proof. exact (@lem21370 (~ False)). Qed.
Lemma lem21373 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem21374 : term22 = True.
Proof. exact (TRANS (@lem21371) (@lem21373)). Qed.
Lemma lem21375 : True = term22.
Proof. exact (SYM (@lem21374)). Qed.
Lemma lem21376 : term22.
Proof. exact (EQ_MP (@lem21375) (@lem0)). Qed.
Lemma lem21377 {A : Type'} (y : A) (z : A) (h1 : (y = z) = False) : term9 A y z.
Proof. exact (EQ_MP (@lem21363 A y z h1) (@lem21376)). Qed.
Lemma lem21378 {A : Type'} (y : A) (z : A) (h1 : (y = z) = True) : term9 A y z.
Proof. exact (EQ_MP (@lem21350 A y z h1) (@lem21368)). Qed.
Lemma lem21381 {A : Type'} (y : A) (z : A) : term9 A y z.
Proof. exact (or_elim (@lem21327 A y z) (fun h0 : (y = z) = True => @lem21378 A y z h0) (fun h0 : (y = z) = False => @lem21377 A y z h0)). Qed.
Lemma lem21382 {A : Type'} (z : A) (x : A) (y : A) (h1 : x = y) : term4 A x y z.
Proof. exact (EQ_MP (@lem21278 A z x y h1) (@lem21381 A y z)). Qed.
Lemma lem21383 {A : Type'} (x : A) (y : A) (z : A) : term4 A x y z.
Proof. exact (or_elim (@lem21186 A x y) (fun h0 : x = y => @lem21382 A z x y h0) (fun h0 : term2 A x y => @lem21316 A z x y h0)). Qed.
Lemma lem21384 {A : Type'} (x : A) (y : A) (z : A) : term5 A x y z.
Proof. exact (EQ_MP (@lem21222 A x y z) (@lem21383 A x y z)). Qed.
