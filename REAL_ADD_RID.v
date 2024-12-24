Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ADD_RID_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338238_spec.
Require Import thm1338512_spec.
Require Import thm16474_spec.
Require Import thm18392_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm69_spec.
Lemma lem1361107 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1361108 : term1 = term2.
Proof. exact (@lem1361107 term1). Qed.
Lemma lem1361109 : term2 = term1.
Proof. exact (SYM (@lem1361108)). Qed.
Lemma lem1361110 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1361113 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1361114 : term5.
Proof. exact (fun h0 : term4 => @lem1361113 h0). Qed.
Lemma lem1361115 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1361116 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1361117 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1361115 h2 (@lem1361116 h1)). Qed.
Lemma lem1361118 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1361117 h1 h0). Qed.
Lemma lem1361119 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1361120 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1361118 h1 (@lem1361119 h2)). Qed.
Lemma lem1361121 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1361120 h0 h1). Qed.
Lemma lem1361122 : term7.
Proof. exact (fun h0 : term5 => @lem1361121 h0). Qed.
Lemma lem1361125 : term5.
Proof. exact (@lem1361122 (@lem1361114)). Qed.
Lemma lem1361139 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1361140 : term8 = term9.
Proof. exact (@lem1361139 term10). Qed.
Lemma lem1361149 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1361150 : term12 = term13.
Proof. exact (MK_COMB (@lem1361149) (@lem1361140)). Qed.
Lemma lem1361153 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1361160 : term4 = term15.
Proof. exact (MK_COMB (@lem1361153) (@lem1361150)). Qed.
Lemma lem1361161 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1361162 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1361161 y x)). Qed.
Lemma lem1361163 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361164 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1361163) (@lem1361162 x)). Qed.
Lemma lem1361165 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1361164 x)). Qed.
Lemma lem1361166 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361167 : term10 = term10.
Proof. exact (MK_COMB (@lem1361166) (@lem1361165)). Qed.
Lemma lem1361168 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1361169 : term9 = term9.
Proof. exact (MK_COMB (@lem1361168) (@lem1361167)). Qed.
Lemma lem1361170 (x : real) : ((term19 x) = x) = ((term19 x) = x).
Proof. exact (eq_refl ((term19 x) = x)). Qed.
Lemma lem1361171 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1361170 x)). Qed.
Lemma lem1361172 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361173 : term21 = term21.
Proof. exact (MK_COMB (@lem1361172) (@lem1361171)). Qed.
Lemma lem1361174 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1361175 : term11 = term11.
Proof. exact (MK_COMB (@lem1361174) (@lem1361173)). Qed.
Lemma lem1361176 : term13 = term13.
Proof. exact (MK_COMB (@lem1361175) (@lem1361169)). Qed.
Lemma lem1361177 (x : real) : ((term22 x) = x) = ((term22 x) = x).
Proof. exact (eq_refl ((term22 x) = x)). Qed.
Lemma lem1361178 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1361177 x)). Qed.
Lemma lem1361179 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361180 : term1 = term1.
Proof. exact (MK_COMB (@lem1361179) (@lem1361178)). Qed.
Lemma lem1361181 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1361182 : term3 = term3.
Proof. exact (MK_COMB (@lem1361181) (@lem1361180)). Qed.
Lemma lem1361183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1361184 : term14 = term14.
Proof. exact (MK_COMB (@lem1361183) (@lem1361182)). Qed.
Lemma lem1361185 : term15 = term15.
Proof. exact (MK_COMB (@lem1361184) (@lem1361176)). Qed.
Lemma lem1361216 : term4 = term15.
Proof. exact (TRANS (@lem1361160) (@lem1361185)). Qed.
Lemma lem1361217 : term15 = term4.
Proof. exact (SYM (@lem1361216)). Qed.
Lemma lem1361218 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1361219 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem1361220 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1361222 (P : real -> Prop) : (term24 P) = (term25 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1361223 : term3 = term26.
Proof. exact (@lem1361222 term23). Qed.
Lemma lem1361224 (x : real) : (term27 x) = ((term22 x) = x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1361225 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1361227 (x : real) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem1361225) (@lem1361224 x)). Qed.
Lemma lem1361228 : term30 = term31.
Proof. exact (fun_ext (fun x : real => @lem1361227 x)). Qed.
Lemma lem1361229 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1361230 : term26 = term32.
Proof. exact (MK_COMB (@lem1361229) (@lem1361228)). Qed.
Lemma lem1361239 : term3 = term32.
Proof. exact (TRANS (@lem1361223) (@lem1361230)). Qed.
Lemma lem1361240 (h1 : term3) : term32.
Proof. exact (EQ_MP (@lem1361239) (@lem1361218 h1)). Qed.
Lemma lem1361241 (x : real) : ((term19 x) = x) = ((term19 x) = x).
Proof. exact (eq_refl ((term19 x) = x)). Qed.
Lemma lem1361242 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1361241 x)). Qed.
Lemma lem1361243 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361252 : term21 = term21.
Proof. exact (MK_COMB (@lem1361243) (@lem1361242)). Qed.
Lemma lem1361253 (h1 : term21) : term21.
Proof. exact (EQ_MP (@lem1361252) (@lem1361219 h1)). Qed.
Lemma lem1361254 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1361255 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1361254 y x)). Qed.
Lemma lem1361256 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361257 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1361256) (@lem1361255 x)). Qed.
Lemma lem1361258 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1361257 x)). Qed.
Lemma lem1361259 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361272 : term10 = term10.
Proof. exact (MK_COMB (@lem1361259) (@lem1361258)). Qed.
Lemma lem1361273 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1361272) (@lem1361220 h1)). Qed.
Lemma lem1361287 (x : real) : ((term19 x) = x) = ((term19 x) = x).
Proof. exact (eq_refl ((term19 x) = x)). Qed.
Lemma lem1361288 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1361287 x)). Qed.
Lemma lem1361289 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361290 : term21 = term21.
Proof. exact (MK_COMB (@lem1361289) (@lem1361288)). Qed.
Lemma lem1361291 (h1 : term21) : term21.
Proof. exact (EQ_MP (@lem1361290) (@lem1361253 h1)). Qed.
Lemma lem1361304 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1361305 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1361304 y x)). Qed.
Lemma lem1361306 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361307 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1361306) (@lem1361305 x)). Qed.
Lemma lem1361308 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1361307 x)). Qed.
Lemma lem1361309 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361310 : term10 = term10.
Proof. exact (MK_COMB (@lem1361309) (@lem1361308)). Qed.
Lemma lem1361311 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1361310) (@lem1361273 h1)). Qed.
Lemma lem1361327 (x : real) (h1 : term29 x) : term29 x.
Proof. exact (h1). Qed.
Lemma lem1361329 (x : real) : ((term19 x) = x) = ((term19 x) = x).
Proof. exact (eq_refl ((term19 x) = x)). Qed.
Lemma lem1361330 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1361329 x)). Qed.
Lemma lem1361331 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361333 : term21 = term21.
Proof. exact (MK_COMB (@lem1361331) (@lem1361330)). Qed.
Lemma lem1361334 (h1 : term21) : term21.
Proof. exact (EQ_MP (@lem1361333) (@lem1361291 h1)). Qed.
Lemma lem1361336 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1361337 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1361336 y x)). Qed.
Lemma lem1361338 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361339 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1361338) (@lem1361337 x)). Qed.
Lemma lem1361340 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1361339 x)). Qed.
Lemma lem1361341 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1361343 : term10 = term10.
Proof. exact (MK_COMB (@lem1361341) (@lem1361340)). Qed.
Lemma lem1361344 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1361343) (@lem1361311 h1)). Qed.
Lemma lem1361348 (x : real) (h1 : term29 x) : term29 x.
Proof. exact (h1). Qed.
Lemma lem1361349 (_24205 : real) (h1 : term21) : term33 _24205.
Proof. exact (@lem1361334 h1 _24205). Qed.
Lemma lem1361350 (_24205 : real) : (term33 _24205) = ((term19 _24205) = _24205).
Proof. exact (eq_refl (term33 _24205)). Qed.
Lemma lem1361352 (_24206 : real) (h1 : term10) : term34 _24206.
Proof. exact (@lem1361344 h1 _24206). Qed.
Lemma lem1361353 (_24206 : real) : (term34 _24206) = (term17 _24206).
Proof. exact (eq_refl (term34 _24206)). Qed.
Lemma lem1361354 (_24206 : real) (h1 : term10) : term17 _24206.
Proof. exact (EQ_MP (@lem1361353 _24206) (@lem1361352 _24206 h1)). Qed.
Lemma lem1361355 (_24206 : real) (_24207 : real) (h1 : term10) : term35 _24206 _24207.
Proof. exact (@lem1361354 _24206 h1 _24207). Qed.
Lemma lem1361356 (_24207 : real) (_24206 : real) : (term35 _24206 _24207) = ((real_add _24206 _24207) = (real_add _24207 _24206)).
Proof. exact (eq_refl (term35 _24206 _24207)). Qed.
Lemma lem1361363 (x : real) (h1 : term29 x) : term29 x.
Proof. exact (h1). Qed.
Lemma lem1361396 (x : real) (y : real) (z : real) : term36 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1361400 (_24207 : real) (_24206 : real) (h1 : term10) : (real_add _24206 _24207) = (real_add _24207 _24206).
Proof. exact (EQ_MP (@lem1361356 _24207 _24206) (@lem1361355 _24206 _24207 h1)). Qed.
Lemma lem1361401 (x : real) (h1 : term10) : (term19 x) = (term22 x).
Proof. exact (@lem1361400 x term37 h1). Qed.
Lemma lem1361402 (x : real) (h1 : term10) : term38 x.
Proof. exact (fun h0 : term39 x => @lem1361401 x h1). Qed.
Lemma lem1361404 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1361405 (x : real) : (term38 x) = ((term19 x) = (term22 x)).
Proof. exact (@lem1361404 ((term19 x) = (term22 x))). Qed.
Lemma lem1361406 (x : real) (h1 : term10) : (term19 x) = (term22 x).
Proof. exact (EQ_MP (@lem1361405 x) (@lem1361402 x h1)). Qed.
Lemma lem1361408 (_24205 : real) (h1 : term21) : (term19 _24205) = _24205.
Proof. exact (EQ_MP (@lem1361350 _24205) (@lem1361349 _24205 h1)). Qed.
Lemma lem1361409 (x : real) (h1 : term21) : (term19 x) = x.
Proof. exact (@lem1361408 x h1). Qed.
Lemma lem1361410 (x : real) (h1 : term21) : term41 x.
Proof. exact (fun h0 : term42 x => @lem1361409 x h1). Qed.
Lemma lem1361412 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1361413 (x : real) : (term41 x) = ((term19 x) = x).
Proof. exact (@lem1361412 ((term19 x) = x)). Qed.
Lemma lem1361414 (x : real) (h1 : term21) : (term19 x) = x.
Proof. exact (EQ_MP (@lem1361413 x) (@lem1361410 x h1)). Qed.
Lemma lem1361432 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1361433 (y : real) (x : real) (z : real) : (term43 x y z) = (term44 y x z).
Proof. exact (@lem1361432 (y = z) (term45 x z)). Qed.
Lemma lem1361443 (x : real) (y : real) : (term46 x y) = (term46 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1361444 (y : real) (x : real) (z : real) : (term36 x y z) = (term47 y x z).
Proof. exact (MK_COMB (@lem1361443 x y) (@lem1361433 y x z)). Qed.
Lemma lem1361448 (q : Prop) (p : Prop) (r : Prop) : (term48 p q r) = (term48 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1361449 (y : real) (x : real) (z : real) : (term47 y x z) = (term49 y x z).
Proof. exact (@lem1361448 (y = z) (term45 x y) (term45 x z)). Qed.
Lemma lem1361471 (y : real) (x : real) (z : real) : (term36 x y z) = (term49 y x z).
Proof. exact (TRANS (@lem1361444 y x z) (@lem1361449 y x z)). Qed.
Lemma lem1361472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1361473 (y : real) (x : real) (z : real) : (term50 x y z) = (term51 y x z).
Proof. exact (MK_COMB (@lem1361472) (@lem1361471 y x z)). Qed.
Lemma lem1361495 (y : real) (x : real) (z : real) : (term49 y x z) = (term49 y x z).
Proof. exact (eq_refl (term49 y x z)). Qed.
Lemma lem1361496 (y : real) (x : real) (z : real) : ((term36 x y z) = (term49 y x z)) = ((term49 y x z) = (term49 y x z)).
Proof. exact (MK_COMB (@lem1361473 y x z) (@lem1361495 y x z)). Qed.
Lemma lem1361498 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1361499 (x : Prop) : (x = x) = True.
Proof. exact (@lem1361498 Prop x). Qed.
Lemma lem1361500 (y : real) (x : real) (z : real) : ((term49 y x z) = (term49 y x z)) = True.
Proof. exact (@lem1361499 (term49 y x z)). Qed.
Lemma lem1361501 (y : real) (x : real) (z : real) : ((term36 x y z) = (term49 y x z)) = True.
Proof. exact (TRANS (@lem1361496 y x z) (@lem1361500 y x z)). Qed.
Lemma lem1361502 (y : real) (x : real) (z : real) : True = ((term36 x y z) = (term49 y x z)).
Proof. exact (SYM (@lem1361501 y x z)). Qed.
Lemma lem1361503 (y : real) (x : real) (z : real) : (term36 x y z) = (term49 y x z).
Proof. exact (EQ_MP (@lem1361502 y x z) (@lem0)). Qed.
Lemma lem1361504 (y : real) (x : real) (z : real) : term49 y x z.
Proof. exact (EQ_MP (@lem1361503 y x z) (@lem1361396 x y z)). Qed.
Lemma lem1361506 (b : Prop) (a : Prop) : (a \/ b) = (term52 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1361507 (x : real) (y : real) (z : real) : (term49 y x z) = (term53 x y z).
Proof. exact (@lem1361506 (term54 y x z) (y = z)). Qed.
Lemma lem1361509 (a : Prop) (b : Prop) : (term55 a b) = (term56 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1361510 (y : real) (x : real) (z : real) : (term57 y x z) = (term58 y x z).
Proof. exact (@lem1361509 (term45 x y) (term45 x z)). Qed.
Lemma lem1361512 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1361513 (x : real) (y : real) : (term60 x y) = (x = y).
Proof. exact (@lem1361512 (x = y)). Qed.
Lemma lem1361514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1361515 (x : real) (y : real) : (term61 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1361514) (@lem1361513 x y)). Qed.
Lemma lem1361517 (a : Prop) : (term59 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1361518 (x : real) (z : real) : (term60 x z) = (x = z).
Proof. exact (@lem1361517 (x = z)). Qed.
Lemma lem1361519 (y : real) (x : real) (z : real) : (term58 y x z) = (term63 y x z).
Proof. exact (MK_COMB (@lem1361515 x y) (@lem1361518 x z)). Qed.
Lemma lem1361520 (y : real) (x : real) (z : real) : (term57 y x z) = (term63 y x z).
Proof. exact (TRANS (@lem1361510 y x z) (@lem1361519 y x z)). Qed.
Lemma lem1361521 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1361522 (y : real) (x : real) (z : real) : (term64 y x z) = (term65 y x z).
Proof. exact (MK_COMB (@lem1361521) (@lem1361520 y x z)). Qed.
Lemma lem1361523 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1361524 (x : real) (y : real) (z : real) : (term53 x y z) = (term66 x y z).
Proof. exact (MK_COMB (@lem1361522 y x z) (@lem1361523 y z)). Qed.
Lemma lem1361525 (x : real) (y : real) (z : real) : (term49 y x z) = (term66 x y z).
Proof. exact (TRANS (@lem1361507 x y z) (@lem1361524 x y z)). Qed.
Lemma lem1361527 (x : real) (h1 : term10) (h2 : term21) : term67 x.
Proof. exact (conj (@lem1361406 x h1) (@lem1361414 x h2)). Qed.
Lemma lem1361529 (x : real) (y : real) (z : real) : term66 x y z.
Proof. exact (EQ_MP (@lem1361525 x y z) (@lem1361504 y x z)). Qed.
Lemma lem1361530 (x : real) : term68 x.
Proof. exact (@lem1361529 (term19 x) (term22 x) x). Qed.
Lemma lem1361533 (x : real) (h1 : term10) (h2 : term21) : (term22 x) = x.
Proof. exact (@lem1361530 x (@lem1361527 x h1 h2)). Qed.
Lemma lem1361534 (x : real) (h1 : term10) (h2 : term21) : term69 x.
Proof. exact (fun h0 : term29 x => @lem1361533 x h1 h2). Qed.
Lemma lem1361536 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1361537 (x : real) : (term69 x) = ((term22 x) = x).
Proof. exact (@lem1361536 ((term22 x) = x)). Qed.
Lemma lem1361538 (x : real) (h1 : term10) (h2 : term21) : (term22 x) = x.
Proof. exact (EQ_MP (@lem1361537 x) (@lem1361534 x h1 h2)). Qed.
Lemma lem1361541 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1361543 (x : real) : (term29 x) = (term70 x).
Proof. exact (@lem1361541 ((term22 x) = x)). Qed.
Lemma lem1361546 (x : real) (h1 : term29 x) : term70 x.
Proof. exact (EQ_MP (@lem1361543 x) (@lem1361363 x h1)). Qed.
Lemma lem1361549 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : False.
Proof. exact (@lem1361546 x h3 (@lem1361538 x h1 h2)). Qed.
Lemma lem1361550 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : term71.
Proof. exact (fun h0 : ~ False => @lem1361549 x h1 h2 h3). Qed.
Lemma lem1361552 (p : Prop) : (term40 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1361553 : term71 = False.
Proof. exact (@lem1361552 False). Qed.
Lemma lem1361554 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1361553) (@lem1361550 x h1 h2 h3)). Qed.
Lemma lem1361555 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : (term29 x) = False.
Proof. exact (prop_ext (fun h4 : term29 x => @lem1361554 x h1 h2 h3) (fun h4 : False => @lem1361363 x h3)). Qed.
Lemma lem1361556 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1361555 x h1 h2 h3) (@lem1361363 x h3)). Qed.
Lemma lem1361557 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : (term29 x) = False.
Proof. exact (prop_ext (fun h4 : term29 x => @lem1361556 x h1 h2 h3) (fun h4 : False => @lem1361348 x h3)). Qed.
Lemma lem1361558 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1361557 x h1 h2 h3) (@lem1361348 x h3)). Qed.
Lemma lem1361559 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : (term29 x) = False.
Proof. exact (prop_ext (fun h4 : term29 x => @lem1361558 x h1 h2 h3) (fun h4 : False => @lem1361348 x h3)). Qed.
Lemma lem1361560 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1361559 x h1 h2 h3) (@lem1361348 x h3)). Qed.
Lemma lem1361561 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1361560 x h1 h2 h3) (fun h4 : False => @lem1361344 h1)). Qed.
Lemma lem1361562 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1361561 x h1 h2 h3) (@lem1361344 h1)). Qed.
Lemma lem1361563 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : term21 = False.
Proof. exact (prop_ext (fun h4 : term21 => @lem1361562 x h1 h2 h3) (fun h4 : False => @lem1361334 h2)). Qed.
Lemma lem1361564 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1361563 x h1 h2 h3) (@lem1361334 h2)). Qed.
Lemma lem1361565 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : (term29 x) = False.
Proof. exact (prop_ext (fun h4 : term29 x => @lem1361564 x h1 h2 h3) (fun h4 : False => @lem1361327 x h3)). Qed.
Lemma lem1361566 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1361565 x h1 h2 h3) (@lem1361327 x h3)). Qed.
Lemma lem1361567 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1361566 x h1 h2 h3) (fun h4 : False => @lem1361311 h1)). Qed.
Lemma lem1361568 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1361567 x h1 h2 h3) (@lem1361311 h1)). Qed.
Lemma lem1361569 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : term21 = False.
Proof. exact (prop_ext (fun h4 : term21 => @lem1361568 x h1 h2 h3) (fun h4 : False => @lem1361291 h2)). Qed.
Lemma lem1361570 (x : real) (h1 : term10) (h2 : term21) (h3 : term29 x) : False.
Proof. exact (EQ_MP (@lem1361569 x h1 h2 h3) (@lem1361291 h2)). Qed.
Lemma lem1361571 (h1 : term10) (h2 : term21) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1361240 h3) (fun x : real => fun h0 : term31 x => @lem1361570 x h1 h2 h0)). Qed.
Lemma lem1361572 (h1 : term10) (h2 : term21) (h3 : term3) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1361571 h1 h2 h3) (fun h4 : False => @lem1361273 h1)). Qed.
Lemma lem1361573 (h1 : term10) (h2 : term21) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1361572 h1 h2 h3) (@lem1361273 h1)). Qed.
Lemma lem1361574 (h1 : term10) (h2 : term21) (h3 : term3) : term21 = False.
Proof. exact (prop_ext (fun h4 : term21 => @lem1361573 h1 h2 h3) (fun h4 : False => @lem1361253 h2)). Qed.
Lemma lem1361575 (h1 : term10) (h2 : term21) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1361574 h1 h2 h3) (@lem1361253 h2)). Qed.
Lemma lem1361576 (h1 : term21) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1361575 h0 h1 h2). Qed.
Lemma lem1361577 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1361578 (h1 : term21) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1361577) (@lem1361576 h1 h2)). Qed.
Lemma lem1361579 (h1 : term3) : term13.
Proof. exact (fun h0 : term21 => @lem1361578 h0 h1). Qed.
Lemma lem1361580 : term15.
Proof. exact (fun h0 : term3 => @lem1361579 h0). Qed.
Lemma lem1361581 : term4.
Proof. exact (EQ_MP (@lem1361217) (@lem1361580)). Qed.
Lemma lem1361583 : term4.
Proof. exact (@lem1361125 (@lem1361581)). Qed.
Lemma lem1361584 (h1 : term3) : term12.
Proof. exact (@lem1361583 (@lem1361110 h1)). Qed.
Lemma lem1361585 (h1 : term3) : term8.
Proof. exact (@lem1361584 h1 (@lem1338512)). Qed.
Lemma lem1361586 (h1 : term3) : False.
Proof. exact (@lem1361585 h1 (@lem1338238)). Qed.
Lemma lem1361587 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1361586 h1) (fun h2 : False => @lem1361110 h1)). Qed.
Lemma lem1361588 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1361587 h1) (@lem1361110 h1)). Qed.
Lemma lem1361589 : term2.
Proof. exact (fun h0 : term3 => @lem1361588 h0). Qed.
Lemma lem1361590 : term1.
Proof. exact (EQ_MP (@lem1361109) (@lem1361589)). Qed.
