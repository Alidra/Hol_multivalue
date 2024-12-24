Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_APPROACH_term_abbrevs.
Require Import DE_MORGAN_THM_spec.
Require Import DISJ_ACI_spec.
Require Import INF_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import REAL_NOT_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm1823_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem5284187 (s : real -> Prop) : term0 s.
Proof. exact (@lem5214027 s). Qed.
Lemma lem5284188 (s : real -> Prop) : (term0 s) = (term1 s).
Proof. exact (eq_refl (term0 s)). Qed.
Lemma lem5284190 (x : real) : term2 x.
Proof. exact (@lem1376537 x). Qed.
Lemma lem5284191 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem5284192 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem5284191 x) (@lem5284190 x)). Qed.
Lemma lem5284193 (x : real) (y : real) : term4 x y.
Proof. exact (@lem5284192 x y). Qed.
Lemma lem5284194 (y : real) (x : real) : (term4 x y) = ((term5 x y) = (real_le y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem5284196 (x : real) : term2 x.
Proof. exact (@lem1376537 x). Qed.
Lemma lem5284197 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem5284198 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem5284197 x) (@lem5284196 x)). Qed.
Lemma lem5284199 (x : real) (y : real) : term4 x y.
Proof. exact (@lem5284198 x y). Qed.
Lemma lem5284200 (y : real) (x : real) : (term4 x y) = ((term5 x y) = (real_le y x)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem5284202 (t1 : Prop) : term6 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem5284203 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (eq_refl (term6 t1)). Qed.
Lemma lem5284204 (t1 : Prop) : term7 t1.
Proof. exact (EQ_MP (@lem5284203 t1) (@lem5284202 t1)). Qed.
Lemma lem5284205 (t1 : Prop) (t2 : Prop) : term8 t1 t2.
Proof. exact (@lem5284204 t1 t2). Qed.
Lemma lem5284206 (t1 : Prop) (t2 : Prop) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (eq_refl (term8 t1 t2)). Qed.
Lemma lem5284207 (t1 : Prop) (t2 : Prop) : term9 t1 t2.
Proof. exact (EQ_MP (@lem5284206 t1 t2) (@lem5284205 t1 t2)). Qed.
Lemma lem5284210 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem5284211 {A : Type'} (P : A -> Prop) : (term10 A P) = ((term11 A P) = (term12 A P)).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem5284217 (s : real -> Prop) (c : real) (h1 : term13 s c) : term13 s c.
Proof. exact (h1). Qed.
Lemma lem5284218 (s : real -> Prop) (c : real) (h1 : term14 s c) : term14 s c.
Proof. exact (h1). Qed.
Lemma lem5284219 (s : real -> Prop) (h1 : term15 s) : term15 s.
Proof. exact (h1). Qed.
Lemma lem5284220 (s : real -> Prop) (c : real) (h1 : term16 s c) : term16 s c.
Proof. exact (h1). Qed.
Lemma lem5284221 (s : real -> Prop) (h1 : term17 s) : term17 s.
Proof. exact (h1). Qed.
Lemma lem5284223 (p : Prop) : p = (term18 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5284224 (s : real -> Prop) (c : real) : (term19 s c) = (term20 s c).
Proof. exact (@lem5284223 (term19 s c)). Qed.
Lemma lem5284225 (s : real -> Prop) (c : real) : (term20 s c) = (term19 s c).
Proof. exact (SYM (@lem5284224 s c)). Qed.
Lemma lem5284226 (s : real -> Prop) (c : real) (h1 : term21 s c) : term21 s c.
Proof. exact (h1). Qed.
Lemma lem5284228 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (EQ_MP (@lem5284211 A P) (@lem5284210 A P)). Qed.
Lemma lem5284229 (P : real -> Prop) : (term22 P) = (term23 P).
Proof. exact (@lem5284228 real P). Qed.
Lemma lem5284230 (s : real -> Prop) (c : real) : (term24 s c) = (term25 s c).
Proof. exact (@lem5284229 (term26 s c)). Qed.
Lemma lem5284231 (s : real -> Prop) (x : real) (c : real) : (term27 s c x) = (term28 s x c).
Proof. exact (eq_refl (term27 s c x)). Qed.
Lemma lem5284232 (s : real -> Prop) (c : real) : (term29 s c) = (term26 s c).
Proof. exact (fun_ext (fun x : real => @lem5284231 s x c)). Qed.
Lemma lem5284233 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5284234 (s : real -> Prop) (c : real) : (term30 s c) = (term19 s c).
Proof. exact (MK_COMB (@lem5284233) (@lem5284232 s c)). Qed.
Lemma lem5284235 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5284236 (s : real -> Prop) (c : real) : (term24 s c) = (term21 s c).
Proof. exact (MK_COMB (@lem5284235) (@lem5284234 s c)). Qed.
Lemma lem5284237 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5284238 (s : real -> Prop) (c : real) : (term31 s c) = (term32 s c).
Proof. exact (MK_COMB (@lem5284237) (@lem5284236 s c)). Qed.
Lemma lem5284239 (s : real -> Prop) (x : real) (c : real) : (term27 s c x) = (term28 s x c).
Proof. exact (eq_refl (term27 s c x)). Qed.
Lemma lem5284240 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5284241 (s : real -> Prop) (x : real) (c : real) : (term33 s c x) = (term34 s x c).
Proof. exact (MK_COMB (@lem5284240) (@lem5284239 s x c)). Qed.
Lemma lem5284242 (s : real -> Prop) (c : real) : (term35 s c) = (term36 s c).
Proof. exact (fun_ext (fun x : real => @lem5284241 s x c)). Qed.
Lemma lem5284243 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5284244 (s : real -> Prop) (c : real) : (term25 s c) = (term37 s c).
Proof. exact (MK_COMB (@lem5284243) (@lem5284242 s c)). Qed.
Lemma lem5284245 (s : real -> Prop) (c : real) : ((term24 s c) = (term25 s c)) = ((term21 s c) = (term37 s c)).
Proof. exact (MK_COMB (@lem5284238 s c) (@lem5284244 s c)). Qed.
Lemma lem5284246 (s : real -> Prop) (c : real) : (term21 s c) = (term37 s c).
Proof. exact (EQ_MP (@lem5284245 s c) (@lem5284230 s c)). Qed.
Lemma lem5284252 (t1 : Prop) (t2 : Prop) : (term38 t1 t2) = (term39 t1 t2).
Proof. exact (proj1 (@lem5284207 t1 t2)). Qed.
Lemma lem5284253 (s : real -> Prop) (x : real) (c : real) : (term34 s x c) = (term40 s x c).
Proof. exact (@lem5284252 (@IN real x s) (real_lt x c)). Qed.
Lemma lem5284257 (y : real) (x : real) : (term5 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem5284200 y x) (@lem5284199 x y)). Qed.
Lemma lem5284258 (c : real) (x : real) : (term5 x c) = (real_le c x).
Proof. exact (@lem5284257 c x). Qed.
Lemma lem5284259 (x : real) (s : real -> Prop) : (term41 x s) = (term41 x s).
Proof. exact (eq_refl (term41 x s)). Qed.
Lemma lem5284260 (s : real -> Prop) (c : real) (x : real) : (term40 s x c) = (term42 s c x).
Proof. exact (MK_COMB (@lem5284259 x s) (@lem5284258 c x)). Qed.
Lemma lem5284263 (s : real -> Prop) (c : real) (x : real) : (term34 s x c) = (term42 s c x).
Proof. exact (TRANS (@lem5284253 s x c) (@lem5284260 s c x)). Qed.
Lemma lem5284264 (s : real -> Prop) (c : real) : (term36 s c) = (term43 s c).
Proof. exact (fun_ext (fun x : real => @lem5284263 s c x)). Qed.
Lemma lem5284265 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5284266 (s : real -> Prop) (c : real) : (term37 s c) = (term44 s c).
Proof. exact (MK_COMB (@lem5284265) (@lem5284264 s c)). Qed.
Lemma lem5284271 (s : real -> Prop) (c : real) : (term21 s c) = (term44 s c).
Proof. exact (TRANS (@lem5284246 s c) (@lem5284266 s c)). Qed.
Lemma lem5284272 (s : real -> Prop) (c : real) (h1 : term21 s c) : term44 s c.
Proof. exact (EQ_MP (@lem5284271 s c) (@lem5284226 s c h1)). Qed.
Lemma lem5284274 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem5284275 (s : real -> Prop) (c : real) : (term45 s c) = (term46 s c).
Proof. exact (@lem5284274 (term16 s c)). Qed.
Lemma lem5284277 (y : real) (x : real) : (term5 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem5284194 y x) (@lem5284193 x y)). Qed.
Lemma lem5284278 (c : real) (s : real -> Prop) : (term46 s c) = (term47 c s).
Proof. exact (@lem5284277 c (inf s)). Qed.
Lemma lem5284279 (c : real) (s : real -> Prop) : (term45 s c) = (term47 c s).
Proof. exact (TRANS (@lem5284275 s c) (@lem5284278 c s)). Qed.
Lemma lem5284280 (s : real -> Prop) (c : real) : (term47 c s) = (term45 s c).
Proof. exact (SYM (@lem5284279 c s)). Qed.
Lemma lem5284281 (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) : term48 s.
Proof. exact (conj (@lem5284219 s h2) (@lem5284221 s h1)). Qed.
Lemma lem5284283 (s : real -> Prop) : term1 s.
Proof. exact (EQ_MP (@lem5284188 s) (@lem5284187 s)). Qed.
Lemma lem5284284 (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) : term49 s.
Proof. exact (@lem5284283 s (@lem5284281 s h1 h2)). Qed.
Lemma lem5284285 (s : real -> Prop) (h1 : term49 s) : term49 s.
Proof. exact (h1). Qed.
Lemma lem5284286 (s : real -> Prop) (h1 : term50 s) : term50 s.
Proof. exact (h1). Qed.
Lemma lem5284288 (s : real -> Prop) (h1 : term50 s) : term50 s.
Proof. exact (h1). Qed.
Lemma lem5284289 (b : real) (s : real -> Prop) (h1 : term50 s) : term51 s b.
Proof. exact (@lem5284288 s h1 b). Qed.
Lemma lem5284290 (b : real) (s : real -> Prop) : (term51 s b) = (term52 b s).
Proof. exact (eq_refl (term51 s b)). Qed.
Lemma lem5284291 (b : real) (s : real -> Prop) (h1 : term50 s) : term52 b s.
Proof. exact (EQ_MP (@lem5284290 b s) (@lem5284289 b s h1)). Qed.
Lemma lem5284292 (s : real -> Prop) (b : real) (h1 : term53 s b) : term53 s b.
Proof. exact (h1). Qed.
Lemma lem5284293 (s : real -> Prop) (b : real) (h1 : term50 s) (h2 : term53 s b) : term47 b s.
Proof. exact (@lem5284291 b s h1 (@lem5284292 s b h2)). Qed.
Lemma lem5284294 (s : real -> Prop) (b : real) (h1 : term53 s b) : term54 b s.
Proof. exact (fun h0 : term50 s => @lem5284293 s b h0 h1). Qed.
Lemma lem5284295 (s : real -> Prop) (h1 : term50 s) : term50 s.
Proof. exact (h1). Qed.
Lemma lem5284296 (s : real -> Prop) (b : real) (h1 : term50 s) (h2 : term53 s b) : term47 b s.
Proof. exact (@lem5284294 s b h2 (@lem5284295 s h1)). Qed.
Lemma lem5284297 (b : real) (s : real -> Prop) (h1 : term50 s) : term52 b s.
Proof. exact (fun h0 : term53 s b => @lem5284296 s b h1 h0). Qed.
Lemma lem5284298 (s : real -> Prop) (h1 : term50 s) : term50 s.
Proof. exact (fun b : real => @lem5284297 b s h1). Qed.
Lemma lem5284299 (s : real -> Prop) : term55 s.
Proof. exact (fun h0 : term50 s => @lem5284298 s h0). Qed.
Lemma lem5284300 (s : real -> Prop) (h1 : term50 s) : term50 s.
Proof. exact (@lem5284299 s (@lem5284286 s h1)). Qed.
Lemma lem5284301 (b : real) (s : real -> Prop) (h1 : term50 s) : term51 s b.
Proof. exact (@lem5284300 s h1 b). Qed.
Lemma lem5284302 (b : real) (s : real -> Prop) : (term51 s b) = (term52 b s).
Proof. exact (eq_refl (term51 s b)). Qed.
Lemma lem5284305 (b : real) (s : real -> Prop) (h1 : term50 s) : term52 b s.
Proof. exact (EQ_MP (@lem5284302 b s) (@lem5284301 b s h1)). Qed.
Lemma lem5284306 (c : real) (s : real -> Prop) (h1 : term50 s) : term52 c s.
Proof. exact (@lem5284305 c s h1). Qed.
Lemma lem5284308 (p : Prop) : p = (term18 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5284309 (s : real -> Prop) (c : real) : (term53 s c) = (term56 s c).
Proof. exact (@lem5284308 (term53 s c)). Qed.
Lemma lem5284310 (s : real -> Prop) (c : real) : (term56 s c) = (term53 s c).
Proof. exact (SYM (@lem5284309 s c)). Qed.
Lemma lem5284311 (s : real -> Prop) (c : real) (h1 : term57 s c) : term57 s c.
Proof. exact (h1). Qed.
Lemma lem5284314 (s : real -> Prop) (c : real) (h1 : term58 s c) : term58 s c.
Proof. exact (h1). Qed.
Lemma lem5284315 (s : real -> Prop) (c : real) : term59 s c.
Proof. exact (fun h0 : term58 s c => @lem5284314 s c h0). Qed.
Lemma lem5284316 (s : real -> Prop) (c : real) (h1 : term59 s c) : term59 s c.
Proof. exact (h1). Qed.
Lemma lem5284317 (s : real -> Prop) (c : real) (h1 : term58 s c) : term58 s c.
Proof. exact (h1). Qed.
Lemma lem5284318 (s : real -> Prop) (c : real) (h1 : term58 s c) (h2 : term59 s c) : term58 s c.
Proof. exact (@lem5284316 s c h2 (@lem5284317 s c h1)). Qed.
Lemma lem5284319 (s : real -> Prop) (c : real) (h1 : term58 s c) : term60 s c.
Proof. exact (fun h0 : term59 s c => @lem5284318 s c h1 h0). Qed.
Lemma lem5284320 (s : real -> Prop) (c : real) (h1 : term59 s c) : term59 s c.
Proof. exact (h1). Qed.
Lemma lem5284321 (s : real -> Prop) (c : real) (h1 : term58 s c) (h2 : term59 s c) : term58 s c.
Proof. exact (@lem5284319 s c h1 (@lem5284320 s c h2)). Qed.
Lemma lem5284322 (s : real -> Prop) (c : real) (h1 : term59 s c) : term59 s c.
Proof. exact (fun h0 : term58 s c => @lem5284321 s c h0 h1). Qed.
Lemma lem5284323 (s : real -> Prop) (c : real) : term61 s c.
Proof. exact (fun h0 : term59 s c => @lem5284322 s c h0). Qed.
Lemma lem5284326 (s : real -> Prop) (c : real) : term59 s c.
Proof. exact (@lem5284323 s c (@lem5284315 s c)). Qed.
Lemma lem5284402 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5284403 (s : real -> Prop) (c : real) : (term56 s c) = (term62 s c).
Proof. exact (@lem5284402 (term57 s c)). Qed.
Lemma lem5284405 (t : Prop) : (term63 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5284406 (s : real -> Prop) (c : real) : (term62 s c) = (term53 s c).
Proof. exact (@lem5284405 (term53 s c)). Qed.
Lemma lem5284411 (s : real -> Prop) (c : real) : (term56 s c) = (term53 s c).
Proof. exact (TRANS (@lem5284403 s c) (@lem5284406 s c)). Qed.
Lemma lem5284414 (s : real -> Prop) (c : real) : (term64 s c) = (term64 s c).
Proof. exact (eq_refl (term64 s c)). Qed.
Lemma lem5284415 (s : real -> Prop) (c : real) : (term65 s c) = (term66 s c).
Proof. exact (MK_COMB (@lem5284414 s c) (@lem5284411 s c)). Qed.
Lemma lem5284418 (s : real -> Prop) : (term67 s) = (term67 s).
Proof. exact (eq_refl (term67 s)). Qed.
Lemma lem5284419 (s : real -> Prop) (c : real) : (term68 s c) = (term69 s c).
Proof. exact (MK_COMB (@lem5284418 s) (@lem5284415 s c)). Qed.
Lemma lem5284422 (s : real -> Prop) : (term70 s) = (term70 s).
Proof. exact (eq_refl (term70 s)). Qed.
Lemma lem5284423 (s : real -> Prop) (c : real) : (term58 s c) = (term71 s c).
Proof. exact (MK_COMB (@lem5284422 s) (@lem5284419 s c)). Qed.
Lemma lem5284426 (c : real) : (term72 c) = (term73 c).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5284423 s c)). Qed.
Lemma lem5284427 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5284428 (c : real) : (term74 c) = (term75 c).
Proof. exact (MK_COMB (@lem5284427) (@lem5284426 c)). Qed.
Lemma lem5284433 : term76 = term77.
Proof. exact (fun_ext (fun c : real => @lem5284428 c)). Qed.
Lemma lem5284434 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5284443 : term78 = term79.
Proof. exact (MK_COMB (@lem5284434) (@lem5284433)). Qed.
Lemma lem5284448 (s : real -> Prop) (c : real) (x : real) : (term80 s c x) = (term80 s c x).
Proof. exact (eq_refl (term80 s c x)). Qed.
Lemma lem5284449 (s : real -> Prop) (c : real) : (term81 s c) = (term81 s c).
Proof. exact (fun_ext (fun x : real => @lem5284448 s c x)). Qed.
Lemma lem5284450 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5284451 (s : real -> Prop) (c : real) : (term53 s c) = (term53 s c).
Proof. exact (MK_COMB (@lem5284450) (@lem5284449 s c)). Qed.
Lemma lem5284458 (s : real -> Prop) (c : real) (x : real) : (term42 s c x) = (term42 s c x).
Proof. exact (eq_refl (term42 s c x)). Qed.
Lemma lem5284459 (s : real -> Prop) (c : real) : (term43 s c) = (term43 s c).
Proof. exact (fun_ext (fun x : real => @lem5284458 s c x)). Qed.
Lemma lem5284460 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5284461 (s : real -> Prop) (c : real) : (term44 s c) = (term44 s c).
Proof. exact (MK_COMB (@lem5284460) (@lem5284459 s c)). Qed.
Lemma lem5284462 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5284463 (s : real -> Prop) (c : real) : (term64 s c) = (term64 s c).
Proof. exact (MK_COMB (@lem5284462) (@lem5284461 s c)). Qed.
Lemma lem5284464 (s : real -> Prop) (c : real) : (term66 s c) = (term66 s c).
Proof. exact (MK_COMB (@lem5284463 s c) (@lem5284451 s c)). Qed.
Lemma lem5284469 (s : real -> Prop) (b : real) (x : real) : (term80 s b x) = (term80 s b x).
Proof. exact (eq_refl (term80 s b x)). Qed.
Lemma lem5284470 (s : real -> Prop) (b : real) : (term81 s b) = (term81 s b).
Proof. exact (fun_ext (fun x : real => @lem5284469 s b x)). Qed.
Lemma lem5284471 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5284472 (s : real -> Prop) (b : real) : (term53 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5284471) (@lem5284470 s b)). Qed.
Lemma lem5284473 (s : real -> Prop) : (term82 s) = (term82 s).
Proof. exact (fun_ext (fun b : real => @lem5284472 s b)). Qed.
Lemma lem5284474 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5284475 (s : real -> Prop) : (term17 s) = (term17 s).
Proof. exact (MK_COMB (@lem5284474) (@lem5284473 s)). Qed.
Lemma lem5284476 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5284477 (s : real -> Prop) : (term67 s) = (term67 s).
Proof. exact (MK_COMB (@lem5284476) (@lem5284475 s)). Qed.
Lemma lem5284478 (s : real -> Prop) (c : real) : (term69 s c) = (term69 s c).
Proof. exact (MK_COMB (@lem5284477 s) (@lem5284464 s c)). Qed.
Lemma lem5284483 (s : real -> Prop) : (term70 s) = (term70 s).
Proof. exact (eq_refl (term70 s)). Qed.
Lemma lem5284484 (s : real -> Prop) (c : real) : (term71 s c) = (term71 s c).
Proof. exact (MK_COMB (@lem5284483 s) (@lem5284478 s c)). Qed.
Lemma lem5284485 (c : real) : (term73 c) = (term73 c).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5284484 s c)). Qed.
Lemma lem5284486 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5284487 (c : real) : (term75 c) = (term75 c).
Proof. exact (MK_COMB (@lem5284486) (@lem5284485 c)). Qed.
Lemma lem5284488 : term77 = term77.
Proof. exact (fun_ext (fun c : real => @lem5284487 c)). Qed.
Lemma lem5284489 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5284490 : term79 = term79.
Proof. exact (MK_COMB (@lem5284489) (@lem5284488)). Qed.
Lemma lem5284541 : term78 = term79.
Proof. exact (TRANS (@lem5284443) (@lem5284490)). Qed.
Lemma lem5284542 : term79 = term78.
Proof. exact (SYM (@lem5284541)). Qed.
Lemma lem5284544 (s : real -> Prop) (h1 : term17 s) : term17 s.
Proof. exact (h1). Qed.
Lemma lem5284545 (s : real -> Prop) (c : real) (h1 : term44 s c) : term44 s c.
Proof. exact (h1). Qed.
Lemma lem5284548 (p : Prop) : p = (term18 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5284549 (c : real) (x : real) : (real_le c x) = (term83 c x).
Proof. exact (@lem5284548 (real_le c x)). Qed.
Lemma lem5284550 (c : real) (x : real) : (term83 c x) = (real_le c x).
Proof. exact (SYM (@lem5284549 c x)). Qed.
Lemma lem5284551 (c : real) (x : real) (h1 : term84 c x) : term84 c x.
Proof. exact (h1). Qed.
Lemma lem5284564 (s : real -> Prop) (b : real) (x : real) : (term80 s b x) = (term42 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5284565 (s : real -> Prop) (b : real) : (term81 s b) = (term43 s b).
Proof. exact (fun_ext (fun x : real => @lem5284564 s b x)). Qed.
Lemma lem5284566 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5284567 (s : real -> Prop) (b : real) : (term53 s b) = (term44 s b).
Proof. exact (MK_COMB (@lem5284566) (@lem5284565 s b)). Qed.
Lemma lem5284568 (s : real -> Prop) : (term82 s) = (term85 s).
Proof. exact (fun_ext (fun b : real => @lem5284567 s b)). Qed.
Lemma lem5284569 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5284626 (s : real -> Prop) : (term17 s) = (term86 s).
Proof. exact (MK_COMB (@lem5284569) (@lem5284568 s)). Qed.
Lemma lem5284627 (s : real -> Prop) (h1 : term17 s) : term86 s.
Proof. exact (EQ_MP (@lem5284626 s) (@lem5284544 s h1)). Qed.
Lemma lem5284632 (s : real -> Prop) (c : real) (x : real) : (term42 s c x) = (term42 s c x).
Proof. exact (eq_refl (term42 s c x)). Qed.
Lemma lem5284633 (s : real -> Prop) (c : real) : (term43 s c) = (term43 s c).
Proof. exact (fun_ext (fun x : real => @lem5284632 s c x)). Qed.
Lemma lem5284634 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5284687 (s : real -> Prop) (c : real) : (term44 s c) = (term44 s c).
Proof. exact (MK_COMB (@lem5284634) (@lem5284633 s c)). Qed.
Lemma lem5284688 (s : real -> Prop) (c : real) (h1 : term44 s c) : term44 s c.
Proof. exact (EQ_MP (@lem5284687 s c) (@lem5284545 s c h1)). Qed.
Lemma lem5284694 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5284700 (c : real) (x : real) (h1 : term84 c x) : term84 c x.
Proof. exact (h1). Qed.
Lemma lem5284724 (s : real -> Prop) (c : real) (x : real) : (term42 s c x) = (term42 s c x).
Proof. exact (eq_refl (term42 s c x)). Qed.
Lemma lem5284725 (s : real -> Prop) (c : real) : (term43 s c) = (term43 s c).
Proof. exact (fun_ext (fun x : real => @lem5284724 s c x)). Qed.
Lemma lem5284726 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5284727 (s : real -> Prop) (c : real) : (term44 s c) = (term44 s c).
Proof. exact (MK_COMB (@lem5284726) (@lem5284725 s c)). Qed.
Lemma lem5284728 (s : real -> Prop) (c : real) (h1 : term44 s c) : term44 s c.
Proof. exact (EQ_MP (@lem5284727 s c) (@lem5284688 s c h1)). Qed.
Lemma lem5284734 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5284742 (c : real) (x : real) (h1 : term84 c x) : term84 c x.
Proof. exact (h1). Qed.
Lemma lem5284773 (s : real -> Prop) (c : real) (x : real) : (term42 s c x) = (term42 s c x).
Proof. exact (eq_refl (term42 s c x)). Qed.
Lemma lem5284774 (s : real -> Prop) (c : real) : (term43 s c) = (term43 s c).
Proof. exact (fun_ext (fun x : real => @lem5284773 s c x)). Qed.
Lemma lem5284775 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5284777 (s : real -> Prop) (c : real) : (term44 s c) = (term44 s c).
Proof. exact (MK_COMB (@lem5284775) (@lem5284774 s c)). Qed.
Lemma lem5284778 (s : real -> Prop) (c : real) (h1 : term44 s c) : term44 s c.
Proof. exact (EQ_MP (@lem5284777 s c) (@lem5284728 s c h1)). Qed.
Lemma lem5284782 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5284786 (c : real) (x : real) (h1 : term84 c x) : term84 c x.
Proof. exact (h1). Qed.
Lemma lem5284800 (_69157 : real) (s : real -> Prop) (c : real) (h1 : term44 s c) : term87 s c _69157.
Proof. exact (@lem5284778 s c h1 _69157). Qed.
Lemma lem5284801 (s : real -> Prop) (c : real) (_69157 : real) : (term87 s c _69157) = (term42 s c _69157).
Proof. exact (eq_refl (term87 s c _69157)). Qed.
Lemma lem5284813 (_69157 : real) (s : real -> Prop) (c : real) (h1 : term44 s c) : term42 s c _69157.
Proof. exact (EQ_MP (@lem5284801 s c _69157) (@lem5284800 _69157 s c h1)). Qed.
Lemma lem5284815 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5284817 (c : real) (x : real) (h1 : term84 c x) : term84 c x.
Proof. exact (h1). Qed.
Lemma lem5284867 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (h1). Qed.
Lemma lem5284868 (x : real) (s : real -> Prop) (h1 : @IN real x s) : term88 x s.
Proof. exact (fun h0 : term89 x s => @lem5284867 x s h1). Qed.
Lemma lem5284870 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5284871 (x : real) (s : real -> Prop) : (term88 x s) = (@IN real x s).
Proof. exact (@lem5284870 (@IN real x s)). Qed.
Lemma lem5284872 (x : real) (s : real -> Prop) (h1 : @IN real x s) : @IN real x s.
Proof. exact (EQ_MP (@lem5284871 x s) (@lem5284868 x s h1)). Qed.
Lemma lem5284878 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5284879 (c : real) (_69157 : real) (s : real -> Prop) : (term42 s c _69157) = (term91 c _69157 s).
Proof. exact (@lem5284878 (real_le c _69157) (term89 _69157 s)). Qed.
Lemma lem5284885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5284886 (c : real) (_69157 : real) (s : real -> Prop) : (term92 s c _69157) = (term93 c _69157 s).
Proof. exact (MK_COMB (@lem5284885) (@lem5284879 c _69157 s)). Qed.
Lemma lem5284892 (c : real) (_69157 : real) (s : real -> Prop) : (term91 c _69157 s) = (term91 c _69157 s).
Proof. exact (eq_refl (term91 c _69157 s)). Qed.
Lemma lem5284893 (c : real) (_69157 : real) (s : real -> Prop) : ((term42 s c _69157) = (term91 c _69157 s)) = ((term91 c _69157 s) = (term91 c _69157 s)).
Proof. exact (MK_COMB (@lem5284886 c _69157 s) (@lem5284892 c _69157 s)). Qed.
Lemma lem5284895 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5284896 (x : Prop) : (x = x) = True.
Proof. exact (@lem5284895 Prop x). Qed.
Lemma lem5284897 (c : real) (_69157 : real) (s : real -> Prop) : ((term91 c _69157 s) = (term91 c _69157 s)) = True.
Proof. exact (@lem5284896 (term91 c _69157 s)). Qed.
Lemma lem5284898 (c : real) (_69157 : real) (s : real -> Prop) : ((term42 s c _69157) = (term91 c _69157 s)) = True.
Proof. exact (TRANS (@lem5284893 c _69157 s) (@lem5284897 c _69157 s)). Qed.
Lemma lem5284899 (c : real) (_69157 : real) (s : real -> Prop) : True = ((term42 s c _69157) = (term91 c _69157 s)).
Proof. exact (SYM (@lem5284898 c _69157 s)). Qed.
Lemma lem5284900 (c : real) (_69157 : real) (s : real -> Prop) : (term42 s c _69157) = (term91 c _69157 s).
Proof. exact (EQ_MP (@lem5284899 c _69157 s) (@lem0)). Qed.
Lemma lem5284901 (_69157 : real) (s : real -> Prop) (c : real) (h1 : term44 s c) : term91 c _69157 s.
Proof. exact (EQ_MP (@lem5284900 c _69157 s) (@lem5284813 _69157 s c h1)). Qed.
Lemma lem5284903 (b : Prop) (a : Prop) : (a \/ b) = (term94 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5284904 (s : real -> Prop) (c : real) (_69157 : real) : (term91 c _69157 s) = (term95 s c _69157).
Proof. exact (@lem5284903 (term89 _69157 s) (real_le c _69157)). Qed.
Lemma lem5284906 (a : Prop) : (term63 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5284907 (_69157 : real) (s : real -> Prop) : (term96 _69157 s) = (@IN real _69157 s).
Proof. exact (@lem5284906 (@IN real _69157 s)). Qed.
Lemma lem5284908 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5284909 (_69157 : real) (s : real -> Prop) : (term97 _69157 s) = (term98 _69157 s).
Proof. exact (MK_COMB (@lem5284908) (@lem5284907 _69157 s)). Qed.
Lemma lem5284910 (c : real) (_69157 : real) : (real_le c _69157) = (real_le c _69157).
Proof. exact (eq_refl (real_le c _69157)). Qed.
Lemma lem5284911 (s : real -> Prop) (c : real) (_69157 : real) : (term95 s c _69157) = (term80 s c _69157).
Proof. exact (MK_COMB (@lem5284909 _69157 s) (@lem5284910 c _69157)). Qed.
Lemma lem5284912 (s : real -> Prop) (c : real) (_69157 : real) : (term91 c _69157 s) = (term80 s c _69157).
Proof. exact (TRANS (@lem5284904 s c _69157) (@lem5284911 s c _69157)). Qed.
Lemma lem5284915 (_69157 : real) (s : real -> Prop) (c : real) (h1 : term44 s c) : term80 s c _69157.
Proof. exact (EQ_MP (@lem5284912 s c _69157) (@lem5284901 _69157 s c h1)). Qed.
Lemma lem5284916 (x : real) (s : real -> Prop) (c : real) (h1 : term44 s c) : term80 s c x.
Proof. exact (@lem5284915 x s c h1). Qed.
Lemma lem5284919 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : @IN real x s) : real_le c x.
Proof. exact (@lem5284916 x s c h1 (@lem5284872 x s h2)). Qed.
Lemma lem5284920 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : @IN real x s) : term99 c x.
Proof. exact (fun h0 : term84 c x => @lem5284919 c x s h1 h2). Qed.
Lemma lem5284922 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5284923 (c : real) (x : real) : (term99 c x) = (real_le c x).
Proof. exact (@lem5284922 (real_le c x)). Qed.
Lemma lem5284924 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : @IN real x s) : real_le c x.
Proof. exact (EQ_MP (@lem5284923 c x) (@lem5284920 c x s h1 h2)). Qed.
Lemma lem5284927 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5284929 (c : real) (x : real) : (term84 c x) = (term100 c x).
Proof. exact (@lem5284927 (real_le c x)). Qed.
Lemma lem5284932 (c : real) (x : real) (h1 : term84 c x) : term100 c x.
Proof. exact (EQ_MP (@lem5284929 c x) (@lem5284817 c x h1)). Qed.
Lemma lem5284935 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : False.
Proof. exact (@lem5284932 c x h2 (@lem5284924 c x s h1 h3)). Qed.
Lemma lem5284936 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : term101.
Proof. exact (fun h0 : ~ False => @lem5284935 c x s h1 h2 h3). Qed.
Lemma lem5284938 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5284939 : term101 = False.
Proof. exact (@lem5284938 False). Qed.
Lemma lem5284940 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284939) (@lem5284936 c x s h1 h2 h3)). Qed.
Lemma lem5284941 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : (term84 c x) = False.
Proof. exact (prop_ext (fun h4 : term84 c x => @lem5284940 c x s h1 h2 h3) (fun h4 : False => @lem5284817 c x h2)). Qed.
Lemma lem5284942 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284941 c x s h1 h2 h3) (@lem5284817 c x h2)). Qed.
Lemma lem5284943 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : (@IN real x s) = False.
Proof. exact (prop_ext (fun h4 : @IN real x s => @lem5284942 c x s h1 h2 h3) (fun h4 : False => @lem5284815 x s h3)). Qed.
Lemma lem5284944 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284943 c x s h1 h2 h3) (@lem5284815 x s h3)). Qed.
Lemma lem5284945 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : (term84 c x) = False.
Proof. exact (prop_ext (fun h4 : term84 c x => @lem5284944 c x s h1 h2 h3) (fun h4 : False => @lem5284786 c x h2)). Qed.
Lemma lem5284946 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284945 c x s h1 h2 h3) (@lem5284786 c x h2)). Qed.
Lemma lem5284947 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : (@IN real x s) = False.
Proof. exact (prop_ext (fun h4 : @IN real x s => @lem5284946 c x s h1 h2 h3) (fun h4 : False => @lem5284782 x s h3)). Qed.
Lemma lem5284948 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284947 c x s h1 h2 h3) (@lem5284782 x s h3)). Qed.
Lemma lem5284949 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : (term84 c x) = False.
Proof. exact (prop_ext (fun h4 : term84 c x => @lem5284948 c x s h1 h2 h3) (fun h4 : False => @lem5284786 c x h2)). Qed.
Lemma lem5284950 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284949 c x s h1 h2 h3) (@lem5284786 c x h2)). Qed.
Lemma lem5284951 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : (@IN real x s) = False.
Proof. exact (prop_ext (fun h4 : @IN real x s => @lem5284950 c x s h1 h2 h3) (fun h4 : False => @lem5284782 x s h3)). Qed.
Lemma lem5284952 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284951 c x s h1 h2 h3) (@lem5284782 x s h3)). Qed.
Lemma lem5284953 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : (term44 s c) = False.
Proof. exact (prop_ext (fun h4 : term44 s c => @lem5284952 c x s h1 h2 h3) (fun h4 : False => @lem5284778 s c h1)). Qed.
Lemma lem5284954 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284953 c x s h1 h2 h3) (@lem5284778 s c h1)). Qed.
Lemma lem5284955 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : (term84 c x) = False.
Proof. exact (prop_ext (fun h4 : term84 c x => @lem5284954 c x s h1 h2 h3) (fun h4 : False => @lem5284742 c x h2)). Qed.
Lemma lem5284956 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284955 c x s h1 h2 h3) (@lem5284742 c x h2)). Qed.
Lemma lem5284957 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : (@IN real x s) = False.
Proof. exact (prop_ext (fun h4 : @IN real x s => @lem5284956 c x s h1 h2 h3) (fun h4 : False => @lem5284734 x s h3)). Qed.
Lemma lem5284958 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284957 c x s h1 h2 h3) (@lem5284734 x s h3)). Qed.
Lemma lem5284959 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : (term44 s c) = False.
Proof. exact (prop_ext (fun h4 : term44 s c => @lem5284958 c x s h1 h2 h3) (fun h4 : False => @lem5284728 s c h1)). Qed.
Lemma lem5284960 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term84 c x) (h3 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284959 c x s h1 h2 h3) (@lem5284728 s c h1)). Qed.
Lemma lem5284961 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 c x) (h4 : @IN real x s) : False.
Proof. exact (ex_elim (@lem5284627 s h2) (fun b : real => fun h0 : term85 s b => @lem5284960 c x s h1 h3 h4)). Qed.
Lemma lem5284962 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 c x) (h4 : @IN real x s) : (term84 c x) = False.
Proof. exact (prop_ext (fun h5 : term84 c x => @lem5284961 c x s h1 h2 h3 h4) (fun h5 : False => @lem5284700 c x h3)). Qed.
Lemma lem5284963 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 c x) (h4 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284962 c x s h1 h2 h3 h4) (@lem5284700 c x h3)). Qed.
Lemma lem5284964 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 c x) (h4 : @IN real x s) : (@IN real x s) = False.
Proof. exact (prop_ext (fun h5 : @IN real x s => @lem5284963 c x s h1 h2 h3 h4) (fun h5 : False => @lem5284694 x s h4)). Qed.
Lemma lem5284965 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 c x) (h4 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284964 c x s h1 h2 h3 h4) (@lem5284694 x s h4)). Qed.
Lemma lem5284966 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 c x) (h4 : @IN real x s) : (term44 s c) = False.
Proof. exact (prop_ext (fun h5 : term44 s c => @lem5284965 c x s h1 h2 h3 h4) (fun h5 : False => @lem5284688 s c h1)). Qed.
Lemma lem5284967 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 c x) (h4 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284966 c x s h1 h2 h3 h4) (@lem5284688 s c h1)). Qed.
Lemma lem5284968 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 c x) (h4 : @IN real x s) : (term84 c x) = False.
Proof. exact (prop_ext (fun h5 : term84 c x => @lem5284967 c x s h1 h2 h3 h4) (fun h5 : False => @lem5284551 c x h3)). Qed.
Lemma lem5284969 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : term84 c x) (h4 : @IN real x s) : False.
Proof. exact (EQ_MP (@lem5284968 c x s h1 h2 h3 h4) (@lem5284551 c x h3)). Qed.
Lemma lem5284970 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : @IN real x s) : term83 c x.
Proof. exact (fun h0 : term84 c x => @lem5284969 c x s h1 h2 h0 h3). Qed.
Lemma lem5284971 (c : real) (x : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) (h3 : @IN real x s) : real_le c x.
Proof. exact (EQ_MP (@lem5284550 c x) (@lem5284970 c x s h1 h2 h3)). Qed.
Lemma lem5284972 (x : real) (c : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) : term80 s c x.
Proof. exact (fun h0 : @IN real x s => @lem5284971 c x s h1 h2 h0). Qed.
Lemma lem5284977 (c : real) (s : real -> Prop) (h1 : term44 s c) (h2 : term17 s) : term53 s c.
Proof. exact (fun x : real => @lem5284972 x c s h1 h2). Qed.
Lemma lem5284978 (c : real) (s : real -> Prop) (h1 : term17 s) : term66 s c.
Proof. exact (fun h0 : term44 s c => @lem5284977 c s h0 h1). Qed.
Lemma lem5284979 (s : real -> Prop) (c : real) : term69 s c.
Proof. exact (fun h0 : term17 s => @lem5284978 c s h0). Qed.
Lemma lem5284980 (s : real -> Prop) (c : real) : term71 s c.
Proof. exact (fun h0 : term15 s => @lem5284979 s c). Qed.
Lemma lem5284985 (c : real) : term75 c.
Proof. exact (fun s : real -> Prop => @lem5284980 s c). Qed.
Lemma lem5284990 : term79.
Proof. exact (fun c : real => @lem5284985 c). Qed.
Lemma lem5284991 : term78.
Proof. exact (EQ_MP (@lem5284542) (@lem5284990)). Qed.
Lemma lem5284992 (c : real) : term102 c.
Proof. exact (@lem5284991 c). Qed.
Lemma lem5284993 (c : real) : (term102 c) = (term74 c).
Proof. exact (eq_refl (term102 c)). Qed.
Lemma lem5284994 (c : real) : term74 c.
Proof. exact (EQ_MP (@lem5284993 c) (@lem5284992 c)). Qed.
Lemma lem5284995 (c : real) (s : real -> Prop) : term103 c s.
Proof. exact (@lem5284994 c s). Qed.
Lemma lem5284996 (s : real -> Prop) (c : real) : (term103 c s) = (term58 s c).
Proof. exact (eq_refl (term103 c s)). Qed.
Lemma lem5284997 (s : real -> Prop) (c : real) : term58 s c.
Proof. exact (EQ_MP (@lem5284996 s c) (@lem5284995 c s)). Qed.
Lemma lem5284999 (s : real -> Prop) (c : real) : term58 s c.
Proof. exact (@lem5284326 s c (@lem5284997 s c)). Qed.
Lemma lem5285000 (c : real) (s : real -> Prop) (h1 : term15 s) : term68 s c.
Proof. exact (@lem5284999 s c (@lem5284219 s h1)). Qed.
Lemma lem5285001 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term15 s) : term65 s c.
Proof. exact (@lem5285000 c s h2 (@lem5284221 s h1)). Qed.
Lemma lem5285002 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) : term56 s c.
Proof. exact (@lem5285001 c s h1 h3 (@lem5284272 s c h2)). Qed.
Lemma lem5285003 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term57 s c) (h3 : term21 s c) (h4 : term15 s) : False.
Proof. exact (@lem5285002 c s h1 h3 h4 (@lem5284311 s c h2)). Qed.
Lemma lem5285004 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term57 s c) (h3 : term21 s c) (h4 : term15 s) : (term57 s c) = False.
Proof. exact (prop_ext (fun h5 : term57 s c => @lem5285003 c s h1 h2 h3 h4) (fun h5 : False => @lem5284311 s c h2)). Qed.
Lemma lem5285005 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term57 s c) (h3 : term21 s c) (h4 : term15 s) : False.
Proof. exact (EQ_MP (@lem5285004 c s h1 h2 h3 h4) (@lem5284311 s c h2)). Qed.
Lemma lem5285006 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) : term56 s c.
Proof. exact (fun h0 : term57 s c => @lem5285005 c s h1 h0 h2 h3). Qed.
Lemma lem5285007 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) : term53 s c.
Proof. exact (EQ_MP (@lem5284310 s c) (@lem5285006 c s h1 h2 h3)). Qed.
Lemma lem5285008 (c : real) (s : real -> Prop) (h1 : term50 s) (h2 : term17 s) (h3 : term21 s c) (h4 : term15 s) : term47 c s.
Proof. exact (@lem5284306 c s h1 (@lem5285007 c s h2 h3 h4)). Qed.
Lemma lem5285009 (s : real -> Prop) (h1 : term49 s) : term50 s.
Proof. exact (proj2 (@lem5284285 s h1)). Qed.
Lemma lem5285011 (c : real) (s : real -> Prop) (h1 : term50 s) (h2 : term17 s) (h3 : term21 s c) (h4 : term15 s) : (term50 s) = (term47 c s).
Proof. exact (prop_ext (fun h5 : term50 s => @lem5285008 c s h1 h2 h3 h4) (fun h5 : term47 c s => @lem5284286 s h1)). Qed.
Lemma lem5285012 (c : real) (s : real -> Prop) (h1 : term50 s) (h2 : term17 s) (h3 : term21 s c) (h4 : term15 s) : term47 c s.
Proof. exact (EQ_MP (@lem5285011 c s h1 h2 h3 h4) (@lem5284286 s h1)). Qed.
Lemma lem5285013 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) (h4 : term49 s) : (term50 s) = (term47 c s).
Proof. exact (prop_ext (fun h5 : term50 s => @lem5285012 c s h5 h1 h2 h3) (fun h5 : term47 c s => @lem5285009 s h4)). Qed.
Lemma lem5285014 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) (h4 : term49 s) : term47 c s.
Proof. exact (EQ_MP (@lem5285013 c s h1 h2 h3 h4) (@lem5285009 s h4)). Qed.
Lemma lem5285015 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) : term104 c s.
Proof. exact (fun h0 : term49 s => @lem5285014 c s h1 h2 h3 h0). Qed.
Lemma lem5285016 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) : term47 c s.
Proof. exact (@lem5285015 c s h1 h2 h3 (@lem5284284 s h1 h3)). Qed.
Lemma lem5285017 (c : real) (s : real -> Prop) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) : term45 s c.
Proof. exact (EQ_MP (@lem5284280 s c) (@lem5285016 c s h1 h2 h3)). Qed.
Lemma lem5285018 (s : real -> Prop) (c : real) (h1 : term17 s) (h2 : term21 s c) (h3 : term15 s) (h4 : term16 s c) : False.
Proof. exact (@lem5285017 c s h1 h2 h3 (@lem5284220 s c h4)). Qed.
Lemma lem5285019 (s : real -> Prop) (c : real) (h1 : term17 s) (h2 : term15 s) (h3 : term16 s c) : term20 s c.
Proof. exact (fun h0 : term21 s c => @lem5285018 s c h1 h0 h2 h3). Qed.
Lemma lem5285020 (s : real -> Prop) (c : real) (h1 : term17 s) (h2 : term15 s) (h3 : term16 s c) : term19 s c.
Proof. exact (EQ_MP (@lem5284225 s c) (@lem5285019 s c h1 h2 h3)). Qed.
Lemma lem5285021 (s : real -> Prop) (c : real) (h1 : term13 s c) : term14 s c.
Proof. exact (proj2 (@lem5284217 s c h1)). Qed.
Lemma lem5285022 (s : real -> Prop) (c : real) (h1 : term13 s c) : term15 s.
Proof. exact (proj1 (@lem5284217 s c h1)). Qed.
Lemma lem5285023 (s : real -> Prop) (c : real) (h1 : term14 s c) : term16 s c.
Proof. exact (proj2 (@lem5284218 s c h1)). Qed.
Lemma lem5285024 (s : real -> Prop) (c : real) (h1 : term14 s c) : term17 s.
Proof. exact (proj1 (@lem5284218 s c h1)). Qed.
Lemma lem5285025 (s : real -> Prop) (c : real) (h1 : term17 s) (h2 : term15 s) (h3 : term16 s c) : (term16 s c) = (term19 s c).
Proof. exact (prop_ext (fun h4 : term16 s c => @lem5285020 s c h1 h2 h3) (fun h4 : term19 s c => @lem5284220 s c h3)). Qed.
Lemma lem5285026 (s : real -> Prop) (c : real) (h1 : term17 s) (h2 : term15 s) (h3 : term16 s c) : term19 s c.
Proof. exact (EQ_MP (@lem5285025 s c h1 h2 h3) (@lem5284220 s c h3)). Qed.
Lemma lem5285027 (s : real -> Prop) (c : real) (h1 : term17 s) (h2 : term15 s) (h3 : term16 s c) : (term17 s) = (term19 s c).
Proof. exact (prop_ext (fun h4 : term17 s => @lem5285026 s c h1 h2 h3) (fun h4 : term19 s c => @lem5284221 s h1)). Qed.
Lemma lem5285028 (s : real -> Prop) (c : real) (h1 : term17 s) (h2 : term15 s) (h3 : term16 s c) : term19 s c.
Proof. exact (EQ_MP (@lem5285027 s c h1 h2 h3) (@lem5284221 s h1)). Qed.
Lemma lem5285029 (s : real -> Prop) (c : real) (h1 : term17 s) (h2 : term15 s) (h3 : term14 s c) : (term16 s c) = (term19 s c).
Proof. exact (prop_ext (fun h4 : term16 s c => @lem5285028 s c h1 h2 h4) (fun h4 : term19 s c => @lem5285023 s c h3)). Qed.
Lemma lem5285030 (s : real -> Prop) (c : real) (h1 : term17 s) (h2 : term15 s) (h3 : term14 s c) : term19 s c.
Proof. exact (EQ_MP (@lem5285029 s c h1 h2 h3) (@lem5285023 s c h3)). Qed.
Lemma lem5285031 (s : real -> Prop) (c : real) (h1 : term15 s) (h2 : term14 s c) : (term17 s) = (term19 s c).
Proof. exact (prop_ext (fun h3 : term17 s => @lem5285030 s c h3 h1 h2) (fun h3 : term19 s c => @lem5285024 s c h2)). Qed.
Lemma lem5285032 (s : real -> Prop) (c : real) (h1 : term15 s) (h2 : term14 s c) : term19 s c.
Proof. exact (EQ_MP (@lem5285031 s c h1 h2) (@lem5285024 s c h2)). Qed.
Lemma lem5285033 (s : real -> Prop) (c : real) (h1 : term15 s) (h2 : term14 s c) : (term15 s) = (term19 s c).
Proof. exact (prop_ext (fun h3 : term15 s => @lem5285032 s c h1 h2) (fun h3 : term19 s c => @lem5284219 s h1)). Qed.
Lemma lem5285034 (s : real -> Prop) (c : real) (h1 : term15 s) (h2 : term14 s c) : term19 s c.
Proof. exact (EQ_MP (@lem5285033 s c h1 h2) (@lem5284219 s h1)). Qed.
Lemma lem5285035 (s : real -> Prop) (c : real) (h1 : term15 s) (h2 : term13 s c) : (term14 s c) = (term19 s c).
Proof. exact (prop_ext (fun h3 : term14 s c => @lem5285034 s c h1 h3) (fun h3 : term19 s c => @lem5285021 s c h2)). Qed.
Lemma lem5285036 (s : real -> Prop) (c : real) (h1 : term15 s) (h2 : term13 s c) : term19 s c.
Proof. exact (EQ_MP (@lem5285035 s c h1 h2) (@lem5285021 s c h2)). Qed.
Lemma lem5285037 (s : real -> Prop) (c : real) (h1 : term13 s c) : (term15 s) = (term19 s c).
Proof. exact (prop_ext (fun h2 : term15 s => @lem5285036 s c h2 h1) (fun h2 : term19 s c => @lem5285022 s c h1)). Qed.
Lemma lem5285038 (s : real -> Prop) (c : real) (h1 : term13 s c) : term19 s c.
Proof. exact (EQ_MP (@lem5285037 s c h1) (@lem5285022 s c h1)). Qed.
Lemma lem5285039 (s : real -> Prop) (c : real) : term105 s c.
Proof. exact (fun h0 : term13 s c => @lem5285038 s c h0). Qed.
Lemma lem5285045 (s : real -> Prop) : term106 s.
Proof. exact (fun c : real => @lem5285039 s c). Qed.
Lemma lem5285051 : term107.
Proof. exact (fun s : real -> Prop => @lem5285045 s). Qed.
