Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483429_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import real_ge_spec.
Require Import real_gt_spec.
Require Import real_lt_spec.
Require Import real_min_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1483206 (y : real) : term0 y.
Proof. exact (@lem1342163 y). Qed.
Lemma lem1483207 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem1483208 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem1483207 y) (@lem1483206 y)). Qed.
Lemma lem1483209 (y : real) (x : real) : term2 y x.
Proof. exact (@lem1483208 y x). Qed.
Lemma lem1483210 (y : real) (x : real) : (term2 y x) = ((real_ge x y) = (real_le y x)).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem1483212 (y : real) : term3 y.
Proof. exact (@lem1342768 y). Qed.
Lemma lem1483213 (y : real) : (term3 y) = (term4 y).
Proof. exact (eq_refl (term3 y)). Qed.
Lemma lem1483214 (y : real) : term4 y.
Proof. exact (EQ_MP (@lem1483213 y) (@lem1483212 y)). Qed.
Lemma lem1483215 (y : real) (x : real) : term5 y x.
Proof. exact (@lem1483214 y x). Qed.
Lemma lem1483216 (y : real) (x : real) : (term5 y x) = ((real_gt x y) = (real_lt y x)).
Proof. exact (eq_refl (term5 y x)). Qed.
Lemma lem1483218 (m : real) : term6 m.
Proof. exact (@lem1346200 m). Qed.
Lemma lem1483219 (m : real) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem1483220 (m : real) : term7 m.
Proof. exact (EQ_MP (@lem1483219 m) (@lem1483218 m)). Qed.
Lemma lem1483221 (m : real) (n : real) : term8 m n.
Proof. exact (@lem1483220 m n). Qed.
Lemma lem1483222 (m : real) (n : real) : (term8 m n) = ((real_min m n) = (term9 m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem1483227 (m : real) (n : real) : (real_min m n) = (term9 m n).
Proof. exact (EQ_MP (@lem1483222 m n) (@lem1483221 m n)). Qed.
Lemma lem1483228 (x : real) (y : real) : (real_min x y) = (term9 x y).
Proof. exact (@lem1483227 x y). Qed.
Lemma lem1483229 (P : real -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1483230 (P : real -> Prop) (x : real) (y : real) : (term10 P x y) = (term11 P x y).
Proof. exact (MK_COMB (@lem1483229 P) (@lem1483228 x y)). Qed.
Lemma lem1483231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1483232 (P : real -> Prop) (x : real) (y : real) : (term12 P x y) = (term13 P x y).
Proof. exact (MK_COMB (@lem1483231) (@lem1483230 P x y)). Qed.
Lemma lem1483238 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1483210 y x) (@lem1483209 y x)). Qed.
Lemma lem1483239 (x : real) (y : real) : (real_ge y x) = (real_le x y).
Proof. exact (@lem1483238 x y). Qed.
Lemma lem1483240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1483241 (x : real) (y : real) : (term14 y x) = (term15 x y).
Proof. exact (MK_COMB (@lem1483240) (@lem1483239 x y)). Qed.
Lemma lem1483242 (P : real -> Prop) (x : real) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1483243 (y : real) (P : real -> Prop) (x : real) : (term16 y P x) = (term17 y P x).
Proof. exact (MK_COMB (@lem1483241 x y) (@lem1483242 P x)). Qed.
Lemma lem1483246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1483247 (y : real) (P : real -> Prop) (x : real) : (term18 y P x) = (term19 y P x).
Proof. exact (MK_COMB (@lem1483246) (@lem1483243 y P x)). Qed.
Lemma lem1483251 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1483216 y x) (@lem1483215 y x)). Qed.
Lemma lem1483252 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1483253 (y : real) (x : real) : (term20 x y) = (term21 y x).
Proof. exact (MK_COMB (@lem1483252) (@lem1483251 y x)). Qed.
Lemma lem1483254 (P : real -> Prop) (y : real) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem1483255 (x : real) (P : real -> Prop) (y : real) : (term22 x P y) = (term23 x P y).
Proof. exact (MK_COMB (@lem1483253 y x) (@lem1483254 P y)). Qed.
Lemma lem1483258 (x : real) (P : real -> Prop) (y : real) : (term24 x P y) = (term25 x P y).
Proof. exact (MK_COMB (@lem1483247 y P x) (@lem1483255 x P y)). Qed.
Lemma lem1483261 (x : real) (P : real -> Prop) (y : real) : ((term10 P x y) = (term24 x P y)) = ((term11 P x y) = (term25 x P y)).
Proof. exact (MK_COMB (@lem1483232 P x y) (@lem1483258 x P y)). Qed.
Lemma lem1483264 (x : real) (P : real -> Prop) (y : real) : ((term11 P x y) = (term25 x P y)) = ((term10 P x y) = (term24 x P y)).
Proof. exact (SYM (@lem1483261 x P y)). Qed.
Lemma lem1483265 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term26 _476 _475 _474 _477) = (term27 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1483266 (_474 : real) (_475 : Prop) (x : real) (P : real -> Prop) (y : real) (_477 : real) : (term28 x P y _475 _474 _477) = (term29 _474 _475 x P y _477).
Proof. exact (@lem1483265 _474 _475 (term30 x P y) _477). Qed.
Lemma lem1483267 (x : real) (P : real -> Prop) (y : real) : (term31 P x y) = (term32 x P y).
Proof. exact (@lem1483266 x (real_le x y) x P y y). Qed.
Lemma lem1483268 (x : real) (P : real -> Prop) (y : real) : (term33 x P y) = ((P y) = (term25 x P y)).
Proof. exact (eq_refl (term33 x P y)). Qed.
Lemma lem1483269 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1483270 (x : real) (P : real -> Prop) (y : real) : (term35 x P y) = (term36 x P y).
Proof. exact (MK_COMB (@lem1483269 x y) (@lem1483268 x P y)). Qed.
Lemma lem1483271 (x : real) (P : real -> Prop) (y : real) : (term37 P y x) = ((P x) = (term25 x P y)).
Proof. exact (eq_refl (term37 P y x)). Qed.
Lemma lem1483272 (x : real) (y : real) : (term38 x y) = (term38 x y).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem1483273 (x : real) (P : real -> Prop) (y : real) : (term39 P y x) = (term40 x P y).
Proof. exact (MK_COMB (@lem1483272 x y) (@lem1483271 x P y)). Qed.
Lemma lem1483274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1483275 (x : real) (P : real -> Prop) (y : real) : (term41 P y x) = (term42 x P y).
Proof. exact (MK_COMB (@lem1483274) (@lem1483273 x P y)). Qed.
Lemma lem1483276 (x : real) (P : real -> Prop) (y : real) : (term32 x P y) = (term43 x P y).
Proof. exact (MK_COMB (@lem1483275 x P y) (@lem1483270 x P y)). Qed.
Lemma lem1483277 (x : real) (P : real -> Prop) (y : real) : (term31 P x y) = ((term11 P x y) = (term25 x P y)).
Proof. exact (eq_refl (term31 P x y)). Qed.
Lemma lem1483278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1483279 (x : real) (P : real -> Prop) (y : real) : (term44 P x y) = (term45 x P y).
Proof. exact (MK_COMB (@lem1483278) (@lem1483277 x P y)). Qed.
Lemma lem1483280 (x : real) (P : real -> Prop) (y : real) : ((term31 P x y) = (term32 x P y)) = (((term11 P x y) = (term25 x P y)) = (term43 x P y)).
Proof. exact (MK_COMB (@lem1483279 x P y) (@lem1483276 x P y)). Qed.
Lemma lem1483281 (x : real) (P : real -> Prop) (y : real) : ((term11 P x y) = (term25 x P y)) = (term43 x P y).
Proof. exact (EQ_MP (@lem1483280 x P y) (@lem1483267 x P y)). Qed.
Lemma lem1483282 (x : real) (P : real -> Prop) (y : real) : (term43 x P y) = ((term11 P x y) = (term25 x P y)).
Proof. exact (SYM (@lem1483281 x P y)). Qed.
Lemma lem1483283 (x : real) (y : real) (h1 : real_le x y) : real_le x y.
Proof. exact (h1). Qed.
Lemma lem1483284 (x : real) (y : real) : (real_le x y) = ((real_le x y) = True).
Proof. exact (@lem7 (real_le x y)). Qed.
Lemma lem1483285 (x : real) (y : real) (h1 : real_le x y) : (real_le x y) = True.
Proof. exact (EQ_MP (@lem1483284 x y) (@lem1483283 x y h1)). Qed.
Lemma lem1483286 (x : real) (P : real -> Prop) (y : real) : (term46 x P y) = (term46 x P y).
Proof. exact (eq_refl (term46 x P y)). Qed.
Lemma lem1483287 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (term47 P x y) = (term48 x P y).
Proof. exact (MK_COMB (@lem1483286 x P y) (@lem1483285 x y h1)). Qed.
Lemma lem1483288 (x : real) (P : real -> Prop) (y : real) : (term48 x P y) = ((P x) = (term49 x P y)).
Proof. exact (eq_refl (term48 x P y)). Qed.
Lemma lem1483289 (P : real -> Prop) (x : real) (y : real) : (term50 P x y) = (term50 P x y).
Proof. exact (eq_refl (term50 P x y)). Qed.
Lemma lem1483290 (x : real) (P : real -> Prop) (y : real) : ((term47 P x y) = (term48 x P y)) = ((term47 P x y) = ((P x) = (term49 x P y))).
Proof. exact (MK_COMB (@lem1483289 P x y) (@lem1483288 x P y)). Qed.
Lemma lem1483291 (x : real) (P : real -> Prop) (y : real) : (term47 P x y) = ((P x) = (term25 x P y)).
Proof. exact (eq_refl (term47 P x y)). Qed.
Lemma lem1483292 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1483293 (x : real) (P : real -> Prop) (y : real) : (term50 P x y) = (term51 x P y).
Proof. exact (MK_COMB (@lem1483292) (@lem1483291 x P y)). Qed.
Lemma lem1483294 (x : real) (P : real -> Prop) (y : real) : ((P x) = (term49 x P y)) = ((P x) = (term49 x P y)).
Proof. exact (eq_refl ((P x) = (term49 x P y))). Qed.
Lemma lem1483295 (x : real) (P : real -> Prop) (y : real) : ((term47 P x y) = ((P x) = (term49 x P y))) = (((P x) = (term25 x P y)) = ((P x) = (term49 x P y))).
Proof. exact (MK_COMB (@lem1483293 x P y) (@lem1483294 x P y)). Qed.
Lemma lem1483296 (x : real) (P : real -> Prop) (y : real) : ((term47 P x y) = (term48 x P y)) = (((P x) = (term25 x P y)) = ((P x) = (term49 x P y))).
Proof. exact (TRANS (@lem1483290 x P y) (@lem1483295 x P y)). Qed.
Lemma lem1483297 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : ((P x) = (term25 x P y)) = ((P x) = (term49 x P y)).
Proof. exact (EQ_MP (@lem1483296 x P y) (@lem1483287 P x y h1)). Qed.
Lemma lem1483298 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : ((P x) = (term49 x P y)) = ((P x) = (term25 x P y)).
Proof. exact (SYM (@lem1483297 P x y h1)). Qed.
Lemma lem1483299 (x : real) (y : real) (h1 : term52 x y) : term52 x y.
Proof. exact (h1). Qed.
Lemma lem1483300 (x : real) (y : real) : term53 x y.
Proof. exact (@lem82 (real_le x y)). Qed.
Lemma lem1483301 (x : real) (y : real) (h1 : term52 x y) : (real_le x y) = False.
Proof. exact (@lem1483300 x y (@lem1483299 x y h1)). Qed.
Lemma lem1483302 (x : real) (P : real -> Prop) (y : real) : (term54 x P y) = (term54 x P y).
Proof. exact (eq_refl (term54 x P y)). Qed.
Lemma lem1483303 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (term55 P x y) = (term56 x P y).
Proof. exact (MK_COMB (@lem1483302 x P y) (@lem1483301 x y h1)). Qed.
Lemma lem1483304 (x : real) (P : real -> Prop) (y : real) : (term56 x P y) = ((P y) = (term57 x P y)).
Proof. exact (eq_refl (term56 x P y)). Qed.
Lemma lem1483305 (P : real -> Prop) (x : real) (y : real) : (term58 P x y) = (term58 P x y).
Proof. exact (eq_refl (term58 P x y)). Qed.
Lemma lem1483306 (x : real) (P : real -> Prop) (y : real) : ((term55 P x y) = (term56 x P y)) = ((term55 P x y) = ((P y) = (term57 x P y))).
Proof. exact (MK_COMB (@lem1483305 P x y) (@lem1483304 x P y)). Qed.
Lemma lem1483307 (x : real) (P : real -> Prop) (y : real) : (term55 P x y) = ((P y) = (term25 x P y)).
Proof. exact (eq_refl (term55 P x y)). Qed.
Lemma lem1483308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1483309 (x : real) (P : real -> Prop) (y : real) : (term58 P x y) = (term59 x P y).
Proof. exact (MK_COMB (@lem1483308) (@lem1483307 x P y)). Qed.
Lemma lem1483310 (x : real) (P : real -> Prop) (y : real) : ((P y) = (term57 x P y)) = ((P y) = (term57 x P y)).
Proof. exact (eq_refl ((P y) = (term57 x P y))). Qed.
Lemma lem1483311 (x : real) (P : real -> Prop) (y : real) : ((term55 P x y) = ((P y) = (term57 x P y))) = (((P y) = (term25 x P y)) = ((P y) = (term57 x P y))).
Proof. exact (MK_COMB (@lem1483309 x P y) (@lem1483310 x P y)). Qed.
Lemma lem1483312 (x : real) (P : real -> Prop) (y : real) : ((term55 P x y) = (term56 x P y)) = (((P y) = (term25 x P y)) = ((P y) = (term57 x P y))).
Proof. exact (TRANS (@lem1483306 x P y) (@lem1483311 x P y)). Qed.
Lemma lem1483313 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : ((P y) = (term25 x P y)) = ((P y) = (term57 x P y)).
Proof. exact (EQ_MP (@lem1483312 x P y) (@lem1483303 P x y h1)). Qed.
Lemma lem1483314 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : ((P y) = (term57 x P y)) = ((P y) = (term25 x P y)).
Proof. exact (SYM (@lem1483313 P x y h1)). Qed.
Lemma lem1483315 (y : real) : term60 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1483316 (y : real) : (term60 y) = (term61 y).
Proof. exact (eq_refl (term60 y)). Qed.
Lemma lem1483317 (y : real) : term61 y.
Proof. exact (EQ_MP (@lem1483316 y) (@lem1483315 y)). Qed.
Lemma lem1483318 (y : real) (x : real) : term62 y x.
Proof. exact (@lem1483317 y x). Qed.
Lemma lem1483319 (y : real) (x : real) : (term62 y x) = ((real_lt x y) = (term52 y x)).
Proof. exact (eq_refl (term62 y x)). Qed.
Lemma lem1483321 (x : real) (y : real) : (real_le x y) = ((real_le x y) = True).
Proof. exact (@lem7 (real_le x y)). Qed.
Lemma lem1483328 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1483329 (P : real -> Prop) (x : real) : (term63 P x) = (P x).
Proof. exact (@lem1483328 (P x)). Qed.
Lemma lem1483330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1483331 (P : real -> Prop) (x : real) : (term64 P x) = (term65 P x).
Proof. exact (MK_COMB (@lem1483330) (@lem1483329 P x)). Qed.
Lemma lem1483335 (y : real) (x : real) : (real_lt x y) = (term52 y x).
Proof. exact (EQ_MP (@lem1483319 y x) (@lem1483318 y x)). Qed.
Lemma lem1483336 (x : real) (y : real) : (real_lt y x) = (term52 x y).
Proof. exact (@lem1483335 x y). Qed.
Lemma lem1483338 (x : real) (y : real) (h1 : real_le x y) : (real_le x y) = True.
Proof. exact (EQ_MP (@lem1483321 x y) (@lem1483283 x y h1)). Qed.
Lemma lem1483339 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1483340 (x : real) (y : real) (h1 : real_le x y) : (term52 x y) = (~ True).
Proof. exact (MK_COMB (@lem1483339) (@lem1483338 x y h1)). Qed.
Lemma lem1483342 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1483343 (x : real) (y : real) (h1 : real_le x y) : (term52 x y) = False.
Proof. exact (TRANS (@lem1483340 x y h1) (@lem1483342)). Qed.
Lemma lem1483344 (x : real) (y : real) (h1 : real_le x y) : (real_lt y x) = False.
Proof. exact (TRANS (@lem1483336 x y) (@lem1483343 x y h1)). Qed.
Lemma lem1483345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1483346 (x : real) (y : real) (h1 : real_le x y) : (term21 y x) = (and False).
Proof. exact (MK_COMB (@lem1483345) (@lem1483344 x y h1)). Qed.
Lemma lem1483347 (P : real -> Prop) (y : real) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem1483348 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (term23 x P y) = (term66 P y).
Proof. exact (MK_COMB (@lem1483346 x y h1) (@lem1483347 P y)). Qed.
Lemma lem1483350 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1483351 (P : real -> Prop) (y : real) : (term66 P y) = False.
Proof. exact (@lem1483350 (P y)). Qed.
Lemma lem1483352 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (term23 x P y) = False.
Proof. exact (TRANS (@lem1483348 P x y h1) (@lem1483351 P y)). Qed.
Lemma lem1483353 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (term49 x P y) = (term67 P x).
Proof. exact (MK_COMB (@lem1483331 P x) (@lem1483352 P x y h1)). Qed.
Lemma lem1483355 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1483356 (P : real -> Prop) (x : real) : (term67 P x) = (P x).
Proof. exact (@lem1483355 (P x)). Qed.
Lemma lem1483357 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (term49 x P y) = (P x).
Proof. exact (TRANS (@lem1483353 P x y h1) (@lem1483356 P x)). Qed.
Lemma lem1483358 (P : real -> Prop) (x : real) : (term68 P x) = (term68 P x).
Proof. exact (eq_refl (term68 P x)). Qed.
Lemma lem1483359 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : ((P x) = (term49 x P y)) = ((P x) = (P x)).
Proof. exact (MK_COMB (@lem1483358 P x) (@lem1483357 P x y h1)). Qed.
Lemma lem1483361 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1483362 (x : Prop) : (x = x) = True.
Proof. exact (@lem1483361 Prop x). Qed.
Lemma lem1483363 (P : real -> Prop) (x : real) : ((P x) = (P x)) = True.
Proof. exact (@lem1483362 (P x)). Qed.
Lemma lem1483364 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : ((P x) = (term49 x P y)) = True.
Proof. exact (TRANS (@lem1483359 P x y h1) (@lem1483363 P x)). Qed.
Lemma lem1483365 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : True = ((P x) = (term49 x P y)).
Proof. exact (SYM (@lem1483364 P x y h1)). Qed.
Lemma lem1483366 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (P x) = (term49 x P y).
Proof. exact (EQ_MP (@lem1483365 P x y h1) (@lem0)). Qed.
Lemma lem1483367 (y : real) : term60 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1483368 (y : real) : (term60 y) = (term61 y).
Proof. exact (eq_refl (term60 y)). Qed.
Lemma lem1483369 (y : real) : term61 y.
Proof. exact (EQ_MP (@lem1483368 y) (@lem1483367 y)). Qed.
Lemma lem1483370 (y : real) (x : real) : term62 y x.
Proof. exact (@lem1483369 y x). Qed.
Lemma lem1483371 (y : real) (x : real) : (term62 y x) = ((real_lt x y) = (term52 y x)).
Proof. exact (eq_refl (term62 y x)). Qed.
Lemma lem1483373 (x : real) (y : real) : term53 x y.
Proof. exact (@lem82 (real_le x y)). Qed.
Lemma lem1483380 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1483381 (P : real -> Prop) (x : real) : (term66 P x) = False.
Proof. exact (@lem1483380 (P x)). Qed.
Lemma lem1483382 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1483383 (P : real -> Prop) (x : real) : (term69 P x) = (or False).
Proof. exact (MK_COMB (@lem1483382) (@lem1483381 P x)). Qed.
Lemma lem1483387 (y : real) (x : real) : (real_lt x y) = (term52 y x).
Proof. exact (EQ_MP (@lem1483371 y x) (@lem1483370 y x)). Qed.
Lemma lem1483388 (x : real) (y : real) : (real_lt y x) = (term52 x y).
Proof. exact (@lem1483387 x y). Qed.
Lemma lem1483390 (x : real) (y : real) (h1 : term52 x y) : (real_le x y) = False.
Proof. exact (@lem1483373 x y (@lem1483299 x y h1)). Qed.
Lemma lem1483391 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1483392 (x : real) (y : real) (h1 : term52 x y) : (term52 x y) = (~ False).
Proof. exact (MK_COMB (@lem1483391) (@lem1483390 x y h1)). Qed.
Lemma lem1483394 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1483395 (x : real) (y : real) (h1 : term52 x y) : (term52 x y) = True.
Proof. exact (TRANS (@lem1483392 x y h1) (@lem1483394)). Qed.
Lemma lem1483396 (x : real) (y : real) (h1 : term52 x y) : (real_lt y x) = True.
Proof. exact (TRANS (@lem1483388 x y) (@lem1483395 x y h1)). Qed.
Lemma lem1483397 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1483398 (x : real) (y : real) (h1 : term52 x y) : (term21 y x) = (and True).
Proof. exact (MK_COMB (@lem1483397) (@lem1483396 x y h1)). Qed.
Lemma lem1483399 (P : real -> Prop) (y : real) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem1483400 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (term23 x P y) = (term63 P y).
Proof. exact (MK_COMB (@lem1483398 x y h1) (@lem1483399 P y)). Qed.
Lemma lem1483402 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1483403 (P : real -> Prop) (y : real) : (term63 P y) = (P y).
Proof. exact (@lem1483402 (P y)). Qed.
Lemma lem1483404 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (term23 x P y) = (P y).
Proof. exact (TRANS (@lem1483400 P x y h1) (@lem1483403 P y)). Qed.
Lemma lem1483405 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (term57 x P y) = (term70 P y).
Proof. exact (MK_COMB (@lem1483383 P x) (@lem1483404 P x y h1)). Qed.
Lemma lem1483407 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1483408 (P : real -> Prop) (y : real) : (term70 P y) = (P y).
Proof. exact (@lem1483407 (P y)). Qed.
Lemma lem1483409 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (term57 x P y) = (P y).
Proof. exact (TRANS (@lem1483405 P x y h1) (@lem1483408 P y)). Qed.
Lemma lem1483410 (P : real -> Prop) (y : real) : (term68 P y) = (term68 P y).
Proof. exact (eq_refl (term68 P y)). Qed.
Lemma lem1483411 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : ((P y) = (term57 x P y)) = ((P y) = (P y)).
Proof. exact (MK_COMB (@lem1483410 P y) (@lem1483409 P x y h1)). Qed.
Lemma lem1483413 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1483414 (x : Prop) : (x = x) = True.
Proof. exact (@lem1483413 Prop x). Qed.
Lemma lem1483415 (P : real -> Prop) (y : real) : ((P y) = (P y)) = True.
Proof. exact (@lem1483414 (P y)). Qed.
Lemma lem1483416 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : ((P y) = (term57 x P y)) = True.
Proof. exact (TRANS (@lem1483411 P x y h1) (@lem1483415 P y)). Qed.
Lemma lem1483417 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : True = ((P y) = (term57 x P y)).
Proof. exact (SYM (@lem1483416 P x y h1)). Qed.
Lemma lem1483418 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (P y) = (term57 x P y).
Proof. exact (EQ_MP (@lem1483417 P x y h1) (@lem0)). Qed.
Lemma lem1483419 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (P y) = (term25 x P y).
Proof. exact (EQ_MP (@lem1483314 P x y h1) (@lem1483418 P x y h1)). Qed.
Lemma lem1483420 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (term52 x y) = ((P y) = (term25 x P y)).
Proof. exact (prop_ext (fun h2 : term52 x y => @lem1483419 P x y h1) (fun h2 : (P y) = (term25 x P y) => @lem1483299 x y h1)). Qed.
Lemma lem1483421 (P : real -> Prop) (x : real) (y : real) (h1 : term52 x y) : (P y) = (term25 x P y).
Proof. exact (EQ_MP (@lem1483420 P x y h1) (@lem1483299 x y h1)). Qed.
Lemma lem1483422 (x : real) (P : real -> Prop) (y : real) : term36 x P y.
Proof. exact (fun h0 : term52 x y => @lem1483421 P x y h0). Qed.
Lemma lem1483423 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (P x) = (term25 x P y).
Proof. exact (EQ_MP (@lem1483298 P x y h1) (@lem1483366 P x y h1)). Qed.
Lemma lem1483424 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (real_le x y) = ((P x) = (term25 x P y)).
Proof. exact (prop_ext (fun h2 : real_le x y => @lem1483423 P x y h1) (fun h2 : (P x) = (term25 x P y) => @lem1483283 x y h1)). Qed.
Lemma lem1483425 (P : real -> Prop) (x : real) (y : real) (h1 : real_le x y) : (P x) = (term25 x P y).
Proof. exact (EQ_MP (@lem1483424 P x y h1) (@lem1483283 x y h1)). Qed.
Lemma lem1483426 (x : real) (P : real -> Prop) (y : real) : term40 x P y.
Proof. exact (fun h0 : real_le x y => @lem1483425 P x y h0). Qed.
Lemma lem1483427 (x : real) (P : real -> Prop) (y : real) : term43 x P y.
Proof. exact (conj (@lem1483426 x P y) (@lem1483422 x P y)). Qed.
Lemma lem1483428 (x : real) (P : real -> Prop) (y : real) : (term11 P x y) = (term25 x P y).
Proof. exact (EQ_MP (@lem1483282 x P y) (@lem1483427 x P y)). Qed.
Lemma lem1483429 (x : real) (P : real -> Prop) (y : real) : (term10 P x y) = (term24 x P y).
Proof. exact (EQ_MP (@lem1483264 x P y) (@lem1483428 x P y)). Qed.
