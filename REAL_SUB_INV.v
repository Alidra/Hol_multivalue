Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_INV_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_DIV_LMUL_spec.
Require Import REAL_INV_MUL_spec.
Require Import REAL_MUL_RINV_spec.
Require Import REAL_SUB_RDISTRIB_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1338912_spec.
Require Import thm1338986_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm82_spec.
Lemma lem1633185 (x : real) : term0 x.
Proof. exact (@lem1593226 x). Qed.
Lemma lem1633186 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1633187 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1633186 x) (@lem1633185 x)). Qed.
Lemma lem1633188 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1633187 x y). Qed.
Lemma lem1633189 (y : real) (x : real) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1633190 (y : real) (x : real) : term3 y x.
Proof. exact (EQ_MP (@lem1633189 y x) (@lem1633188 x y)). Qed.
Lemma lem1633191 (y : real) (h1 : term4 y) : term4 y.
Proof. exact (h1). Qed.
Lemma lem1633192 (x : real) (y : real) (h1 : term4 y) : (term5 x y) = x.
Proof. exact (@lem1633190 y x (@lem1633191 y h1)). Qed.
Lemma lem1633200 (x : real) (y : real) (h1 : (real_div x y) = (term6 x y)) : (real_div x y) = (term6 x y).
Proof. exact (h1). Qed.
Lemma lem1633201 (x : real) (y : real) (h1 : (real_div x y) = (term6 x y)) : (term6 x y) = (real_div x y).
Proof. exact (SYM (@lem1633200 x y h1)). Qed.
Lemma lem1633202 (x : real) (y : real) (h1 : (term6 x y) = (real_div x y)) : (term6 x y) = (real_div x y).
Proof. exact (h1). Qed.
Lemma lem1633203 (x : real) (y : real) (h1 : (term6 x y) = (real_div x y)) : (real_div x y) = (term6 x y).
Proof. exact (SYM (@lem1633202 x y h1)). Qed.
Lemma lem1633204 (x : real) (y : real) : ((real_div x y) = (term6 x y)) = ((term6 x y) = (real_div x y)).
Proof. exact (prop_ext (fun h1 : (real_div x y) = (term6 x y) => @lem1633201 x y h1) (fun h1 : (term6 x y) = (real_div x y) => @lem1633203 x y h1)). Qed.
Lemma lem1633205 (x : real) : (term7 x) = (term8 x).
Proof. exact (fun_ext (fun y : real => @lem1633204 x y)). Qed.
Lemma lem1633206 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633207 (x : real) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1633206) (@lem1633205 x)). Qed.
Lemma lem1633208 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem1633207 x)). Qed.
Lemma lem1633209 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633210 : term13 = term14.
Proof. exact (MK_COMB (@lem1633209) (@lem1633208)). Qed.
Lemma lem1633211 : term14.
Proof. exact (EQ_MP (@lem1633210) (@lem1344936)). Qed.
Lemma lem1633212 (x : real) : term15 x.
Proof. exact (@lem1633211 x). Qed.
Lemma lem1633213 (x : real) : (term15 x) = (term10 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1633214 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1633213 x) (@lem1633212 x)). Qed.
Lemma lem1633215 (x : real) (y : real) : term16 x y.
Proof. exact (@lem1633214 x y). Qed.
Lemma lem1633216 (x : real) (y : real) : (term16 x y) = ((term6 x y) = (real_div x y)).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1633221 (x : real) (y : real) (z : real) (h1 : (term17 x y z) = (term18 x y z)) : (term17 x y z) = (term18 x y z).
Proof. exact (h1). Qed.
Lemma lem1633222 (x : real) (y : real) (z : real) (h1 : (term17 x y z) = (term18 x y z)) : (term18 x y z) = (term17 x y z).
Proof. exact (SYM (@lem1633221 x y z h1)). Qed.
Lemma lem1633223 (x : real) (y : real) (z : real) (h1 : (term18 x y z) = (term17 x y z)) : (term18 x y z) = (term17 x y z).
Proof. exact (h1). Qed.
Lemma lem1633224 (x : real) (y : real) (z : real) (h1 : (term18 x y z) = (term17 x y z)) : (term17 x y z) = (term18 x y z).
Proof. exact (SYM (@lem1633223 x y z h1)). Qed.
Lemma lem1633225 (x : real) (y : real) (z : real) : ((term17 x y z) = (term18 x y z)) = ((term18 x y z) = (term17 x y z)).
Proof. exact (prop_ext (fun h1 : (term17 x y z) = (term18 x y z) => @lem1633222 x y z h1) (fun h1 : (term18 x y z) = (term17 x y z) => @lem1633224 x y z h1)). Qed.
Lemma lem1633226 (x : real) (y : real) : (term19 x y) = (term20 x y).
Proof. exact (fun_ext (fun z : real => @lem1633225 x y z)). Qed.
Lemma lem1633227 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633228 (x : real) (y : real) : (term21 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1633227) (@lem1633226 x y)). Qed.
Lemma lem1633229 (x : real) : (term23 x) = (term24 x).
Proof. exact (fun_ext (fun y : real => @lem1633228 x y)). Qed.
Lemma lem1633230 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633231 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1633230) (@lem1633229 x)). Qed.
Lemma lem1633232 : term27 = term28.
Proof. exact (fun_ext (fun x : real => @lem1633231 x)). Qed.
Lemma lem1633233 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633234 : term29 = term30.
Proof. exact (MK_COMB (@lem1633233) (@lem1633232)). Qed.
Lemma lem1633235 : term30.
Proof. exact (EQ_MP (@lem1633234) (@lem1338912)). Qed.
Lemma lem1633236 (x : real) : term31 x.
Proof. exact (@lem1633235 x). Qed.
Lemma lem1633237 (x : real) : (term31 x) = (term26 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1633238 (x : real) : term26 x.
Proof. exact (EQ_MP (@lem1633237 x) (@lem1633236 x)). Qed.
Lemma lem1633239 (x : real) (y : real) : term32 x y.
Proof. exact (@lem1633238 x y). Qed.
Lemma lem1633240 (x : real) (y : real) : (term32 x y) = (term22 x y).
Proof. exact (eq_refl (term32 x y)). Qed.
Lemma lem1633241 (x : real) (y : real) : term22 x y.
Proof. exact (EQ_MP (@lem1633240 x y) (@lem1633239 x y)). Qed.
Lemma lem1633242 (x : real) (y : real) (z : real) : term33 x y z.
Proof. exact (@lem1633241 x y z). Qed.
Lemma lem1633243 (x : real) (y : real) (z : real) : (term33 x y z) = ((term18 x y z) = (term17 x y z)).
Proof. exact (eq_refl (term33 x y z)). Qed.
Lemma lem1633245 (x : real) : term34 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem1633246 (x : real) : (term34 x) = ((term35 x) = x).
Proof. exact (eq_refl (term34 x)). Qed.
Lemma lem1633248 (x : real) : term36 x.
Proof. exact (@lem1591985 x). Qed.
Lemma lem1633249 (x : real) : (term36 x) = (term37 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1633250 (x : real) : term37 x.
Proof. exact (EQ_MP (@lem1633249 x) (@lem1633248 x)). Qed.
Lemma lem1633251 (x : real) (h1 : term4 x) : term4 x.
Proof. exact (h1). Qed.
Lemma lem1633252 (x : real) (h1 : term4 x) : (term38 x) = term39.
Proof. exact (@lem1633250 x (@lem1633251 x h1)). Qed.
Lemma lem1633258 (x : real) : term40 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem1633259 (x : real) : (term40 x) = (term25 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1633260 (x : real) : term25 x.
Proof. exact (EQ_MP (@lem1633259 x) (@lem1633258 x)). Qed.
Lemma lem1633261 (x : real) (y : real) : term41 x y.
Proof. exact (@lem1633260 x y). Qed.
Lemma lem1633262 (x : real) (y : real) : (term41 x y) = (term21 x y).
Proof. exact (eq_refl (term41 x y)). Qed.
Lemma lem1633263 (x : real) (y : real) : term21 x y.
Proof. exact (EQ_MP (@lem1633262 x y) (@lem1633261 x y)). Qed.
Lemma lem1633264 (x : real) (y : real) (z : real) : term42 x y z.
Proof. exact (@lem1633263 x y z). Qed.
Lemma lem1633265 (x : real) (y : real) (z : real) : (term42 x y z) = ((term17 x y z) = (term18 x y z)).
Proof. exact (eq_refl (term42 x y z)). Qed.
Lemma lem1633267 (x : real) : term43 x.
Proof. exact (@lem1595294 x). Qed.
Lemma lem1633268 (x : real) : (term43 x) = (term44 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1633269 (x : real) : term44 x.
Proof. exact (EQ_MP (@lem1633268 x) (@lem1633267 x)). Qed.
Lemma lem1633270 (x : real) (y : real) : term45 x y.
Proof. exact (@lem1633269 x y). Qed.
Lemma lem1633271 (x : real) (y : real) : (term45 x y) = ((term46 x y) = (term47 x y)).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1633273 (x : real) : term48 x.
Proof. exact (@lem1526749 x). Qed.
Lemma lem1633274 (x : real) : (term48 x) = (term49 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1633275 (x : real) : term49 x.
Proof. exact (EQ_MP (@lem1633274 x) (@lem1633273 x)). Qed.
Lemma lem1633276 (x : real) (y : real) : term50 x y.
Proof. exact (@lem1633275 x y). Qed.
Lemma lem1633277 (x : real) (y : real) : (term50 x y) = (term51 x y).
Proof. exact (eq_refl (term50 x y)). Qed.
Lemma lem1633278 (x : real) (y : real) : term51 x y.
Proof. exact (EQ_MP (@lem1633277 x y) (@lem1633276 x y)). Qed.
Lemma lem1633279 (x : real) (y : real) (z : real) : term52 x y z.
Proof. exact (@lem1633278 x y z). Qed.
Lemma lem1633280 (x : real) (y : real) (z : real) : (term52 x y z) = ((term53 x y z) = (term54 x y z)).
Proof. exact (eq_refl (term52 x y z)). Qed.
Lemma lem1633282 (x : real) : term55 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1633283 (x : real) : (term55 x) = (term9 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1633284 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1633283 x) (@lem1633282 x)). Qed.
Lemma lem1633285 (x : real) (y : real) : term56 x y.
Proof. exact (@lem1633284 x y). Qed.
Lemma lem1633286 (x : real) (y : real) : (term56 x y) = ((real_div x y) = (term6 x y)).
Proof. exact (eq_refl (term56 x y)). Qed.
Lemma lem1633307 (x : real) (y : real) : (real_div x y) = (term6 x y).
Proof. exact (EQ_MP (@lem1633286 x y) (@lem1633285 x y)). Qed.
Lemma lem1633308 (x : real) (y : real) : (term57 x y) = (term58 x y).
Proof. exact (@lem1633307 (real_sub y x) (real_mul x y)). Qed.
Lemma lem1633310 (x : real) (y : real) (z : real) : (term53 x y z) = (term54 x y z).
Proof. exact (EQ_MP (@lem1633280 x y z) (@lem1633279 x y z)). Qed.
Lemma lem1633311 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (@lem1633310 y x (term46 x y)). Qed.
Lemma lem1633312 (x : real) (y : real) : (term57 x y) = (term59 x y).
Proof. exact (TRANS (@lem1633308 x y) (@lem1633311 x y)). Qed.
Lemma lem1633314 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (EQ_MP (@lem1633271 x y) (@lem1633270 x y)). Qed.
Lemma lem1633315 (y : real) : (real_mul y) = (real_mul y).
Proof. exact (eq_refl (real_mul y)). Qed.
Lemma lem1633316 (x : real) (y : real) : (term60 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1633315 y) (@lem1633314 x y)). Qed.
Lemma lem1633317 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1633318 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1633317) (@lem1633316 x y)). Qed.
Lemma lem1633320 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (EQ_MP (@lem1633271 x y) (@lem1633270 x y)). Qed.
Lemma lem1633321 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1633322 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1633321 x) (@lem1633320 x y)). Qed.
Lemma lem1633323 (x : real) (y : real) : (term59 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem1633318 x y) (@lem1633322 x y)). Qed.
Lemma lem1633324 (x : real) (y : real) : (term57 x y) = (term66 x y).
Proof. exact (TRANS (@lem1633312 x y) (@lem1633323 x y)). Qed.
Lemma lem1633325 (x : real) (y : real) : (term67 x y) = (term67 x y).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem1633326 (x : real) (y : real) : ((term68 x y) = (term57 x y)) = ((term68 x y) = (term66 x y)).
Proof. exact (MK_COMB (@lem1633325 x y) (@lem1633324 x y)). Qed.
Lemma lem1633329 (x : real) (y : real) : (term69 x y) = (term69 x y).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1633330 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1633329 x y) (@lem1633326 x y)). Qed.
Lemma lem1633333 (x : real) : (term72 x) = (term73 x).
Proof. exact (fun_ext (fun y : real => @lem1633330 x y)). Qed.
Lemma lem1633334 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633335 (x : real) : (term74 x) = (term75 x).
Proof. exact (MK_COMB (@lem1633334) (@lem1633333 x)). Qed.
Lemma lem1633340 : term76 = term77.
Proof. exact (fun_ext (fun x : real => @lem1633335 x)). Qed.
Lemma lem1633341 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633342 : term78 = term79.
Proof. exact (MK_COMB (@lem1633341) (@lem1633340)). Qed.
Lemma lem1633347 : term79 = term78.
Proof. exact (SYM (@lem1633342)). Qed.
Lemma lem1633359 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term80 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1633360 (p : Prop) (q : Prop) (p' : Prop) : term81 p q p'.
Proof. exact (fun q' : Prop => @lem1633359 p q p' q'). Qed.
Lemma lem1633361 (p : Prop) (q : Prop) : term82 p q.
Proof. exact (fun p' : Prop => @lem1633360 p q p'). Qed.
Lemma lem1633362 (x : real) (y : real) : term83 x y.
Proof. exact (@lem1633361 (term84 x y) ((term68 x y) = (term66 x y))). Qed.
Lemma lem1633363 (x : real) (y : real) (p' : Prop) : term85 x y p'.
Proof. exact (@lem1633362 x y p'). Qed.
Lemma lem1633364 (x : real) (y : real) (p' : Prop) : (term85 x y p') = (term86 x y p').
Proof. exact (eq_refl (term85 x y p')). Qed.
Lemma lem1633365 (x : real) (y : real) (p' : Prop) : term86 x y p'.
Proof. exact (EQ_MP (@lem1633364 x y p') (@lem1633363 x y p')). Qed.
Lemma lem1633366 (x : real) (y : real) (p' : Prop) (q' : Prop) : term87 x y p' q'.
Proof. exact (@lem1633365 x y p' q'). Qed.
Lemma lem1633367 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term87 x y p' q') = (term88 x y p' q').
Proof. exact (eq_refl (term87 x y p' q')). Qed.
Lemma lem1633368 (x : real) (y : real) (p' : Prop) (q' : Prop) : term88 x y p' q'.
Proof. exact (EQ_MP (@lem1633367 x y p' q') (@lem1633366 x y p' q')). Qed.
Lemma lem1633375 (x : real) (y : real) : (term84 x y) = (term84 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1633376 (x : real) (y : real) (q' : Prop) : term89 x y q'.
Proof. exact (@lem1633368 x y (term84 x y) q'). Qed.
Lemma lem1633377 (x : real) (y : real) (q' : Prop) : term90 x y q'.
Proof. exact (@lem1633376 x y q' (@lem1633375 x y)). Qed.
Lemma lem1633378 (x : real) (y : real) (h1 : term84 x y) : term84 x y.
Proof. exact (h1). Qed.
Lemma lem1633393 (x : real) (y : real) (h1 : term84 x y) : term4 x.
Proof. exact (proj1 (@lem1633378 x y h1)). Qed.
Lemma lem1633394 (x : real) : term91 x.
Proof. exact (@lem82 (x = term92)). Qed.
Lemma lem1633410 (x : real) (y : real) (z : real) : (term17 x y z) = (term18 x y z).
Proof. exact (EQ_MP (@lem1633265 x y z) (@lem1633264 x y z)). Qed.
Lemma lem1633411 (x : real) (y : real) : (term61 x y) = (term93 x y).
Proof. exact (@lem1633410 y (real_inv x) (real_inv y)). Qed.
Lemma lem1633416 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1633417 (x : real) (y : real) : (term63 x y) = (term94 x y).
Proof. exact (MK_COMB (@lem1633416) (@lem1633411 x y)). Qed.
Lemma lem1633423 (x : real) (y : real) (z : real) : (term17 x y z) = (term18 x y z).
Proof. exact (EQ_MP (@lem1633265 x y z) (@lem1633264 x y z)). Qed.
Lemma lem1633424 (x : real) (y : real) : (term65 x y) = (term95 x y).
Proof. exact (@lem1633423 x (real_inv x) (real_inv y)). Qed.
Lemma lem1633428 (x : real) : term37 x.
Proof. exact (fun h0 : term4 x => @lem1633252 x h0). Qed.
Lemma lem1633430 (x : real) (y : real) (h1 : term84 x y) : (x = term92) = False.
Proof. exact (@lem1633394 x (@lem1633393 x y h1)). Qed.
Lemma lem1633431 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1633432 (x : real) (y : real) (h1 : term84 x y) : (term4 x) = (~ False).
Proof. exact (MK_COMB (@lem1633431) (@lem1633430 x y h1)). Qed.
Lemma lem1633434 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1633435 (x : real) (y : real) (h1 : term84 x y) : (term4 x) = True.
Proof. exact (TRANS (@lem1633432 x y h1) (@lem1633434)). Qed.
Lemma lem1633436 (x : real) (y : real) (h1 : term84 x y) : True = (term4 x).
Proof. exact (SYM (@lem1633435 x y h1)). Qed.
Lemma lem1633437 (x : real) (y : real) (h1 : term84 x y) : term4 x.
Proof. exact (EQ_MP (@lem1633436 x y h1) (@lem0)). Qed.
Lemma lem1633438 (x : real) (y : real) (h1 : term84 x y) : (term38 x) = term39.
Proof. exact (@lem1633428 x (@lem1633437 x y h1)). Qed.
Lemma lem1633439 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1633440 (x : real) (y : real) (h1 : term84 x y) : (term96 x) = term97.
Proof. exact (MK_COMB (@lem1633439) (@lem1633438 x y h1)). Qed.
Lemma lem1633441 (y : real) : (real_inv y) = (real_inv y).
Proof. exact (eq_refl (real_inv y)). Qed.
Lemma lem1633442 (x : real) (y : real) (h1 : term84 x y) : (term95 x y) = (term98 y).
Proof. exact (MK_COMB (@lem1633440 x y h1) (@lem1633441 y)). Qed.
Lemma lem1633444 (x : real) : (term35 x) = x.
Proof. exact (EQ_MP (@lem1633246 x) (@lem1633245 x)). Qed.
Lemma lem1633445 (y : real) : (term98 y) = (real_inv y).
Proof. exact (@lem1633444 (real_inv y)). Qed.
Lemma lem1633446 (x : real) (y : real) (h1 : term84 x y) : (term95 x y) = (real_inv y).
Proof. exact (TRANS (@lem1633442 x y h1) (@lem1633445 y)). Qed.
Lemma lem1633447 (x : real) (y : real) (h1 : term84 x y) : (term65 x y) = (real_inv y).
Proof. exact (TRANS (@lem1633424 x y) (@lem1633446 x y h1)). Qed.
Lemma lem1633448 (x : real) (y : real) (h1 : term84 x y) : (term66 x y) = (term99 x y).
Proof. exact (MK_COMB (@lem1633417 x y) (@lem1633447 x y h1)). Qed.
Lemma lem1633453 (x : real) (y : real) : (term67 x y) = (term67 x y).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem1633454 (x : real) (y : real) (h1 : term84 x y) : ((term68 x y) = (term66 x y)) = ((term68 x y) = (term99 x y)).
Proof. exact (MK_COMB (@lem1633453 x y) (@lem1633448 x y h1)). Qed.
Lemma lem1633461 (x : real) (y : real) : term100 x y.
Proof. exact (fun h0 : term84 x y => @lem1633454 x y h0). Qed.
Lemma lem1633462 (x : real) (y : real) : term101 x y.
Proof. exact (@lem1633377 x y ((term68 x y) = (term99 x y))). Qed.
Lemma lem1633463 (x : real) (y : real) : (term71 x y) = (term102 x y).
Proof. exact (@lem1633462 x y (@lem1633461 x y)). Qed.
Lemma lem1633537 (x : real) : (term73 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1633463 x y)). Qed.
Lemma lem1633611 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633612 (x : real) : (term75 x) = (term104 x).
Proof. exact (MK_COMB (@lem1633611) (@lem1633537 x)). Qed.
Lemma lem1633690 : term77 = term105.
Proof. exact (fun_ext (fun x : real => @lem1633612 x)). Qed.
Lemma lem1633768 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633769 : term79 = term106.
Proof. exact (MK_COMB (@lem1633768) (@lem1633690)). Qed.
Lemma lem1633851 : term106 = term79.
Proof. exact (SYM (@lem1633769)). Qed.
Lemma lem1633871 (x : real) (y : real) (z : real) : (term18 x y z) = (term17 x y z).
Proof. exact (EQ_MP (@lem1633243 x y z) (@lem1633242 x y z)). Qed.
Lemma lem1633872 (x : real) (y : real) : (term93 x y) = (term61 x y).
Proof. exact (@lem1633871 y (real_inv x) (real_inv y)). Qed.
Lemma lem1633873 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1633874 (x : real) (y : real) : (term94 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1633873) (@lem1633872 x y)). Qed.
Lemma lem1633875 (y : real) : (real_inv y) = (real_inv y).
Proof. exact (eq_refl (real_inv y)). Qed.
Lemma lem1633876 (x : real) (y : real) : (term99 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem1633874 x y) (@lem1633875 y)). Qed.
Lemma lem1633877 (x : real) (y : real) : (term67 x y) = (term67 x y).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem1633878 (x : real) (y : real) : ((term68 x y) = (term99 x y)) = ((term68 x y) = (term107 x y)).
Proof. exact (MK_COMB (@lem1633877 x y) (@lem1633876 x y)). Qed.
Lemma lem1633881 (x : real) (y : real) : (term69 x y) = (term69 x y).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1633882 (x : real) (y : real) : (term102 x y) = (term108 x y).
Proof. exact (MK_COMB (@lem1633881 x y) (@lem1633878 x y)). Qed.
Lemma lem1633885 (x : real) : (term103 x) = (term109 x).
Proof. exact (fun_ext (fun y : real => @lem1633882 x y)). Qed.
Lemma lem1633886 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633887 (x : real) : (term104 x) = (term110 x).
Proof. exact (MK_COMB (@lem1633886) (@lem1633885 x)). Qed.
Lemma lem1633892 : term105 = term111.
Proof. exact (fun_ext (fun x : real => @lem1633887 x)). Qed.
Lemma lem1633893 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633894 : term106 = term112.
Proof. exact (MK_COMB (@lem1633893) (@lem1633892)). Qed.
Lemma lem1633899 : term112 = term106.
Proof. exact (SYM (@lem1633894)). Qed.
Lemma lem1633919 (x : real) (y : real) : (term6 x y) = (real_div x y).
Proof. exact (EQ_MP (@lem1633216 x y) (@lem1633215 x y)). Qed.
Lemma lem1633920 (x : real) (y : real) : (term47 x y) = (term113 x y).
Proof. exact (@lem1633919 (real_inv x) y). Qed.
Lemma lem1633921 (y : real) : (real_mul y) = (real_mul y).
Proof. exact (eq_refl (real_mul y)). Qed.
Lemma lem1633922 (x : real) (y : real) : (term61 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem1633921 y) (@lem1633920 x y)). Qed.
Lemma lem1633923 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1633924 (x : real) (y : real) : (term63 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1633923) (@lem1633922 x y)). Qed.
Lemma lem1633925 (y : real) : (real_inv y) = (real_inv y).
Proof. exact (eq_refl (real_inv y)). Qed.
Lemma lem1633926 (x : real) (y : real) : (term107 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1633924 x y) (@lem1633925 y)). Qed.
Lemma lem1633927 (x : real) (y : real) : (term67 x y) = (term67 x y).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem1633928 (x : real) (y : real) : ((term68 x y) = (term107 x y)) = ((term68 x y) = (term116 x y)).
Proof. exact (MK_COMB (@lem1633927 x y) (@lem1633926 x y)). Qed.
Lemma lem1633931 (x : real) (y : real) : (term69 x y) = (term69 x y).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1633932 (x : real) (y : real) : (term108 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1633931 x y) (@lem1633928 x y)). Qed.
Lemma lem1633935 (x : real) : (term109 x) = (term118 x).
Proof. exact (fun_ext (fun y : real => @lem1633932 x y)). Qed.
Lemma lem1633936 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633937 (x : real) : (term110 x) = (term119 x).
Proof. exact (MK_COMB (@lem1633936) (@lem1633935 x)). Qed.
Lemma lem1633942 : term111 = term120.
Proof. exact (fun_ext (fun x : real => @lem1633937 x)). Qed.
Lemma lem1633943 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1633944 : term112 = term121.
Proof. exact (MK_COMB (@lem1633943) (@lem1633942)). Qed.
Lemma lem1633949 : term121 = term112.
Proof. exact (SYM (@lem1633944)). Qed.
Lemma lem1633961 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term80 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1633962 (p : Prop) (q : Prop) (p' : Prop) : term81 p q p'.
Proof. exact (fun q' : Prop => @lem1633961 p q p' q'). Qed.
Lemma lem1633963 (p : Prop) (q : Prop) : term82 p q.
Proof. exact (fun p' : Prop => @lem1633962 p q p'). Qed.
Lemma lem1633964 (x : real) (y : real) : term122 x y.
Proof. exact (@lem1633963 (term84 x y) ((term68 x y) = (term116 x y))). Qed.
Lemma lem1633965 (x : real) (y : real) (p' : Prop) : term123 x y p'.
Proof. exact (@lem1633964 x y p'). Qed.
Lemma lem1633966 (x : real) (y : real) (p' : Prop) : (term123 x y p') = (term124 x y p').
Proof. exact (eq_refl (term123 x y p')). Qed.
Lemma lem1633967 (x : real) (y : real) (p' : Prop) : term124 x y p'.
Proof. exact (EQ_MP (@lem1633966 x y p') (@lem1633965 x y p')). Qed.
Lemma lem1633968 (x : real) (y : real) (p' : Prop) (q' : Prop) : term125 x y p' q'.
Proof. exact (@lem1633967 x y p' q'). Qed.
Lemma lem1633969 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term125 x y p' q') = (term126 x y p' q').
Proof. exact (eq_refl (term125 x y p' q')). Qed.
Lemma lem1633970 (x : real) (y : real) (p' : Prop) (q' : Prop) : term126 x y p' q'.
Proof. exact (EQ_MP (@lem1633969 x y p' q') (@lem1633968 x y p' q')). Qed.
Lemma lem1633977 (x : real) (y : real) : (term84 x y) = (term84 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1633978 (x : real) (y : real) (q' : Prop) : term127 x y q'.
Proof. exact (@lem1633970 x y (term84 x y) q'). Qed.
Lemma lem1633979 (x : real) (y : real) (q' : Prop) : term128 x y q'.
Proof. exact (@lem1633978 x y q' (@lem1633977 x y)). Qed.
Lemma lem1633980 (x : real) (y : real) (h1 : term84 x y) : term84 x y.
Proof. exact (h1). Qed.
Lemma lem1633981 (x : real) (y : real) (h1 : term84 x y) : term4 y.
Proof. exact (proj2 (@lem1633980 x y h1)). Qed.
Lemma lem1633982 (y : real) : term91 y.
Proof. exact (@lem82 (y = term92)). Qed.
Lemma lem1634012 (y : real) (x : real) : term3 y x.
Proof. exact (fun h0 : term4 y => @lem1633192 x y h0). Qed.
Lemma lem1634013 (y : real) (x : real) : term129 y x.
Proof. exact (@lem1634012 y (real_inv x)). Qed.
Lemma lem1634015 (x : real) (y : real) (h1 : term84 x y) : (y = term92) = False.
Proof. exact (@lem1633982 y (@lem1633981 x y h1)). Qed.
Lemma lem1634016 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1634017 (x : real) (y : real) (h1 : term84 x y) : (term4 y) = (~ False).
Proof. exact (MK_COMB (@lem1634016) (@lem1634015 x y h1)). Qed.
Lemma lem1634019 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1634020 (x : real) (y : real) (h1 : term84 x y) : (term4 y) = True.
Proof. exact (TRANS (@lem1634017 x y h1) (@lem1634019)). Qed.
Lemma lem1634021 (x : real) (y : real) (h1 : term84 x y) : True = (term4 y).
Proof. exact (SYM (@lem1634020 x y h1)). Qed.
Lemma lem1634022 (x : real) (y : real) (h1 : term84 x y) : term4 y.
Proof. exact (EQ_MP (@lem1634021 x y h1) (@lem0)). Qed.
Lemma lem1634023 (x : real) (y : real) (h1 : term84 x y) : (term114 x y) = (real_inv x).
Proof. exact (@lem1634013 y x (@lem1634022 x y h1)). Qed.
Lemma lem1634024 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1634025 (x : real) (y : real) (h1 : term84 x y) : (term115 x y) = (term130 x).
Proof. exact (MK_COMB (@lem1634024) (@lem1634023 x y h1)). Qed.
Lemma lem1634026 (y : real) : (real_inv y) = (real_inv y).
Proof. exact (eq_refl (real_inv y)). Qed.
Lemma lem1634027 (x : real) (y : real) (h1 : term84 x y) : (term116 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1634025 x y h1) (@lem1634026 y)). Qed.
Lemma lem1634028 (x : real) (y : real) : (term67 x y) = (term67 x y).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem1634029 (x : real) (y : real) (h1 : term84 x y) : ((term68 x y) = (term116 x y)) = ((term68 x y) = (term68 x y)).
Proof. exact (MK_COMB (@lem1634028 x y) (@lem1634027 x y h1)). Qed.
Lemma lem1634031 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1634032 (x : real) : (x = x) = True.
Proof. exact (@lem1634031 real x). Qed.
Lemma lem1634033 (x : real) (y : real) : ((term68 x y) = (term68 x y)) = True.
Proof. exact (@lem1634032 (term68 x y)). Qed.
Lemma lem1634034 (x : real) (y : real) (h1 : term84 x y) : ((term68 x y) = (term116 x y)) = True.
Proof. exact (TRANS (@lem1634029 x y h1) (@lem1634033 x y)). Qed.
Lemma lem1634035 (x : real) (y : real) : term131 x y.
Proof. exact (fun h0 : term84 x y => @lem1634034 x y h0). Qed.
Lemma lem1634036 (x : real) (y : real) : term132 x y.
Proof. exact (@lem1633979 x y True). Qed.
Lemma lem1634037 (x : real) (y : real) : (term117 x y) = (term133 x y).
Proof. exact (@lem1634036 x y (@lem1634035 x y)). Qed.
Lemma lem1634039 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1634040 (x : real) (y : real) : (term133 x y) = True.
Proof. exact (@lem1634039 (term84 x y)). Qed.
Lemma lem1634041 (x : real) (y : real) : (term117 x y) = True.
Proof. exact (TRANS (@lem1634037 x y) (@lem1634040 x y)). Qed.
Lemma lem1634042 (x : real) : (term118 x) = term134.
Proof. exact (fun_ext (fun y : real => @lem1634041 x y)). Qed.
Lemma lem1634043 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1634044 (x : real) : (term119 x) = term135.
Proof. exact (MK_COMB (@lem1634043) (@lem1634042 x)). Qed.
Lemma lem1634046 {A : Type'} (t : Prop) : (term136 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1634047 (t : Prop) : (term137 t) = t.
Proof. exact (@lem1634046 real t). Qed.
Lemma lem1634048 : term135 = True.
Proof. exact (@lem1634047 True). Qed.
Lemma lem1634049 (x : real) : (term119 x) = True.
Proof. exact (TRANS (@lem1634044 x) (@lem1634048)). Qed.
Lemma lem1634050 : term120 = term134.
Proof. exact (fun_ext (fun x : real => @lem1634049 x)). Qed.
Lemma lem1634051 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1634052 : term121 = term135.
Proof. exact (MK_COMB (@lem1634051) (@lem1634050)). Qed.
Lemma lem1634054 {A : Type'} (t : Prop) : (term136 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1634055 (t : Prop) : (term137 t) = t.
Proof. exact (@lem1634054 real t). Qed.
Lemma lem1634056 : term135 = True.
Proof. exact (@lem1634055 True). Qed.
Lemma lem1634057 : term121 = True.
Proof. exact (TRANS (@lem1634052) (@lem1634056)). Qed.
Lemma lem1634058 : True = term121.
Proof. exact (SYM (@lem1634057)). Qed.
Lemma lem1634059 : term121.
Proof. exact (EQ_MP (@lem1634058) (@lem0)). Qed.
Lemma lem1634060 : term112.
Proof. exact (EQ_MP (@lem1633949) (@lem1634059)). Qed.
Lemma lem1634061 : term106.
Proof. exact (EQ_MP (@lem1633899) (@lem1634060)). Qed.
Lemma lem1634062 : term79.
Proof. exact (EQ_MP (@lem1633851) (@lem1634061)). Qed.
Lemma lem1634063 : term78.
Proof. exact (EQ_MP (@lem1633347) (@lem1634062)). Qed.
