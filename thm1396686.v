Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1396686_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_ENTIRE_spec.
Require Import REAL_LT_LE_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import real_ge_spec.
Require Import real_gt_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1340049_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem1393137 (x : real) : term0 x.
Proof. exact (@lem1340049 x). Qed.
Lemma lem1393138 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1393139 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1393138 x) (@lem1393137 x)). Qed.
Lemma lem1393140 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1393139 x y). Qed.
Lemma lem1393141 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1393142 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1393141 x y) (@lem1393140 x y)). Qed.
Lemma lem1393143 (x : real) (y : real) (h1 : term4 x y) : term4 x y.
Proof. exact (h1). Qed.
Lemma lem1393144 (x : real) (y : real) (h1 : term4 x y) : term5 x y.
Proof. exact (@lem1393142 x y (@lem1393143 x y h1)). Qed.
Lemma lem1393145 (x : real) (y : real) : (term5 x y) = ((term5 x y) = True).
Proof. exact (@lem7 (term5 x y)). Qed.
Lemma lem1393146 (x : real) (y : real) (h1 : term4 x y) : (term5 x y) = True.
Proof. exact (EQ_MP (@lem1393145 x y) (@lem1393144 x y h1)). Qed.
Lemma lem1393152 (x : real) : term6 x.
Proof. exact (@lem1379381 x). Qed.
Lemma lem1393153 (x : real) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1393154 (x : real) : term7 x.
Proof. exact (EQ_MP (@lem1393153 x) (@lem1393152 x)). Qed.
Lemma lem1393155 (x : real) (y : real) : term8 x y.
Proof. exact (@lem1393154 x y). Qed.
Lemma lem1393156 (x : real) (y : real) : (term8 x y) = ((real_lt x y) = (term9 x y)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1393158 (y : real) : term10 y.
Proof. exact (@lem1342768 y). Qed.
Lemma lem1393159 (y : real) : (term10 y) = (term11 y).
Proof. exact (eq_refl (term10 y)). Qed.
Lemma lem1393160 (y : real) : term11 y.
Proof. exact (EQ_MP (@lem1393159 y) (@lem1393158 y)). Qed.
Lemma lem1393161 (y : real) (x : real) : term12 y x.
Proof. exact (@lem1393160 y x). Qed.
Lemma lem1393162 (y : real) (x : real) : (term12 y x) = ((real_gt x y) = (real_lt y x)).
Proof. exact (eq_refl (term12 y x)). Qed.
Lemma lem1393164 (y : real) : term13 y.
Proof. exact (@lem1342163 y). Qed.
Lemma lem1393165 (y : real) : (term13 y) = (term14 y).
Proof. exact (eq_refl (term13 y)). Qed.
Lemma lem1393166 (y : real) : term14 y.
Proof. exact (EQ_MP (@lem1393165 y) (@lem1393164 y)). Qed.
Lemma lem1393167 (y : real) (x : real) : term15 y x.
Proof. exact (@lem1393166 y x). Qed.
Lemma lem1393168 (y : real) (x : real) : (term15 y x) = ((real_ge x y) = (real_le y x)).
Proof. exact (eq_refl (term15 y x)). Qed.
Lemma lem1393170 (x : real) : term16 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem1393171 (x : real) : (term16 x) = ((term17 x) = term18).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1393173 (x : real) : term19 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1393174 (x : real) : (term19 x) = ((term20 x) = term18).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1393181 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1393182 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1393181 p q p' q'). Qed.
Lemma lem1393183 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1393182 p q p'). Qed.
Lemma lem1393184 (x : real) (y : real) : term24 x y.
Proof. exact (@lem1393183 (term25 x y) ((real_mul x y) = term18)). Qed.
Lemma lem1393185 (x : real) (y : real) (p' : Prop) : term26 x y p'.
Proof. exact (@lem1393184 x y p'). Qed.
Lemma lem1393186 (x : real) (y : real) (p' : Prop) : (term26 x y p') = (term27 x y p').
Proof. exact (eq_refl (term26 x y p')). Qed.
Lemma lem1393187 (x : real) (y : real) (p' : Prop) : term27 x y p'.
Proof. exact (EQ_MP (@lem1393186 x y p') (@lem1393185 x y p')). Qed.
Lemma lem1393188 (x : real) (y : real) (p' : Prop) (q' : Prop) : term28 x y p' q'.
Proof. exact (@lem1393187 x y p' q'). Qed.
Lemma lem1393189 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term28 x y p' q') = (term29 x y p' q').
Proof. exact (eq_refl (term28 x y p' q')). Qed.
Lemma lem1393190 (x : real) (y : real) (p' : Prop) (q' : Prop) : term29 x y p' q'.
Proof. exact (EQ_MP (@lem1393189 x y p' q') (@lem1393188 x y p' q')). Qed.
Lemma lem1393197 (x : real) (y : real) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1393198 (x : real) (y : real) (q' : Prop) : term30 x y q'.
Proof. exact (@lem1393190 x y (term25 x y) q'). Qed.
Lemma lem1393199 (x : real) (y : real) (q' : Prop) : term31 x y q'.
Proof. exact (@lem1393198 x y q' (@lem1393197 x y)). Qed.
Lemma lem1393200 (x : real) (y : real) (h1 : term25 x y) : term25 x y.
Proof. exact (h1). Qed.
Lemma lem1393206 (x : real) (y : real) (h1 : term25 x y) : x = term18.
Proof. exact (proj1 (@lem1393200 x y h1)). Qed.
Lemma lem1393207 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1393208 (x : real) (y : real) (h1 : term25 x y) : (real_mul x) = term32.
Proof. exact (MK_COMB (@lem1393207) (@lem1393206 x y h1)). Qed.
Lemma lem1393210 (x : real) (y : real) (h1 : term25 x y) : y = term18.
Proof. exact (proj2 (@lem1393200 x y h1)). Qed.
Lemma lem1393211 (x : real) (y : real) (h1 : term25 x y) : (real_mul x y) = term33.
Proof. exact (MK_COMB (@lem1393208 x y h1) (@lem1393210 x y h1)). Qed.
Lemma lem1393213 (x : real) : (term20 x) = term18.
Proof. exact (EQ_MP (@lem1393174 x) (@lem1393173 x)). Qed.
Lemma lem1393214 : term33 = term18.
Proof. exact (@lem1393213 term18). Qed.
Lemma lem1393215 (x : real) (y : real) (h1 : term25 x y) : (real_mul x y) = term18.
Proof. exact (TRANS (@lem1393211 x y h1) (@lem1393214)). Qed.
Lemma lem1393216 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1393217 (x : real) (y : real) (h1 : term25 x y) : (term34 x y) = term35.
Proof. exact (MK_COMB (@lem1393216) (@lem1393215 x y h1)). Qed.
Lemma lem1393218 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1393219 (x : real) (y : real) (h1 : term25 x y) : ((real_mul x y) = term18) = (term18 = term18).
Proof. exact (MK_COMB (@lem1393217 x y h1) (@lem1393218)). Qed.
Lemma lem1393221 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1393222 (x : real) : (x = x) = True.
Proof. exact (@lem1393221 real x). Qed.
Lemma lem1393223 : (term18 = term18) = True.
Proof. exact (@lem1393222 term18). Qed.
Lemma lem1393224 (x : real) (y : real) (h1 : term25 x y) : ((real_mul x y) = term18) = True.
Proof. exact (TRANS (@lem1393219 x y h1) (@lem1393223)). Qed.
Lemma lem1393225 (x : real) (y : real) : term36 x y.
Proof. exact (fun h0 : term25 x y => @lem1393224 x y h0). Qed.
Lemma lem1393226 (x : real) (y : real) : term37 x y.
Proof. exact (@lem1393199 x y True). Qed.
Lemma lem1393227 (x : real) (y : real) : (term38 x y) = (term39 x y).
Proof. exact (@lem1393226 x y (@lem1393225 x y)). Qed.
Lemma lem1393229 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1393230 (x : real) (y : real) : (term39 x y) = True.
Proof. exact (@lem1393229 (term25 x y)). Qed.
Lemma lem1393231 (x : real) (y : real) : (term38 x y) = True.
Proof. exact (TRANS (@lem1393227 x y) (@lem1393230 x y)). Qed.
Lemma lem1393232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393233 (x : real) (y : real) : (term40 x y) = (and True).
Proof. exact (MK_COMB (@lem1393232) (@lem1393231 x y)). Qed.
Lemma lem1393239 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1393240 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1393239 p q p' q'). Qed.
Lemma lem1393241 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1393240 p q p'). Qed.
Lemma lem1393242 (x : real) (y : real) : term41 x y.
Proof. exact (@lem1393241 (term42 x y) ((real_mul x y) = term18)). Qed.
Lemma lem1393243 (x : real) (y : real) (p' : Prop) : term43 x y p'.
Proof. exact (@lem1393242 x y p'). Qed.
Lemma lem1393244 (x : real) (y : real) (p' : Prop) : (term43 x y p') = (term44 x y p').
Proof. exact (eq_refl (term43 x y p')). Qed.
Lemma lem1393245 (x : real) (y : real) (p' : Prop) : term44 x y p'.
Proof. exact (EQ_MP (@lem1393244 x y p') (@lem1393243 x y p')). Qed.
Lemma lem1393246 (x : real) (y : real) (p' : Prop) (q' : Prop) : term45 x y p' q'.
Proof. exact (@lem1393245 x y p' q'). Qed.
Lemma lem1393247 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term45 x y p' q') = (term46 x y p' q').
Proof. exact (eq_refl (term45 x y p' q')). Qed.
Lemma lem1393248 (x : real) (y : real) (p' : Prop) (q' : Prop) : term46 x y p' q'.
Proof. exact (EQ_MP (@lem1393247 x y p' q') (@lem1393246 x y p' q')). Qed.
Lemma lem1393254 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1393168 y x) (@lem1393167 y x)). Qed.
Lemma lem1393255 (y : real) : (term47 y) = (term48 y).
Proof. exact (@lem1393254 term18 y). Qed.
Lemma lem1393256 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1393257 (x : real) (y : real) : (term42 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem1393256 x) (@lem1393255 y)). Qed.
Lemma lem1393262 (x : real) (y : real) (q' : Prop) : term51 x y q'.
Proof. exact (@lem1393248 x y (term50 x y) q'). Qed.
Lemma lem1393263 (x : real) (y : real) (q' : Prop) : term52 x y q'.
Proof. exact (@lem1393262 x y q' (@lem1393257 x y)). Qed.
Lemma lem1393264 (x : real) (y : real) (h1 : term50 x y) : term50 x y.
Proof. exact (h1). Qed.
Lemma lem1393272 (x : real) (y : real) (h1 : term50 x y) : x = term18.
Proof. exact (proj1 (@lem1393264 x y h1)). Qed.
Lemma lem1393273 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1393274 (x : real) (y : real) (h1 : term50 x y) : (real_mul x) = term32.
Proof. exact (MK_COMB (@lem1393273) (@lem1393272 x y h1)). Qed.
Lemma lem1393275 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1393276 (x : real) (y : real) (h1 : term50 x y) : (real_mul x y) = (term20 y).
Proof. exact (MK_COMB (@lem1393274 x y h1) (@lem1393275 y)). Qed.
Lemma lem1393278 (x : real) : (term20 x) = term18.
Proof. exact (EQ_MP (@lem1393174 x) (@lem1393173 x)). Qed.
Lemma lem1393279 (y : real) : (term20 y) = term18.
Proof. exact (@lem1393278 y). Qed.
Lemma lem1393280 (x : real) (y : real) (h1 : term50 x y) : (real_mul x y) = term18.
Proof. exact (TRANS (@lem1393276 x y h1) (@lem1393279 y)). Qed.
Lemma lem1393281 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1393282 (x : real) (y : real) (h1 : term50 x y) : (term34 x y) = term35.
Proof. exact (MK_COMB (@lem1393281) (@lem1393280 x y h1)). Qed.
Lemma lem1393283 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1393284 (x : real) (y : real) (h1 : term50 x y) : ((real_mul x y) = term18) = (term18 = term18).
Proof. exact (MK_COMB (@lem1393282 x y h1) (@lem1393283)). Qed.
Lemma lem1393286 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1393287 (x : real) : (x = x) = True.
Proof. exact (@lem1393286 real x). Qed.
Lemma lem1393288 : (term18 = term18) = True.
Proof. exact (@lem1393287 term18). Qed.
Lemma lem1393289 (x : real) (y : real) (h1 : term50 x y) : ((real_mul x y) = term18) = True.
Proof. exact (TRANS (@lem1393284 x y h1) (@lem1393288)). Qed.
Lemma lem1393290 (x : real) (y : real) : term53 x y.
Proof. exact (fun h0 : term50 x y => @lem1393289 x y h0). Qed.
Lemma lem1393291 (x : real) (y : real) : term54 x y.
Proof. exact (@lem1393263 x y True). Qed.
Lemma lem1393292 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (@lem1393291 x y (@lem1393290 x y)). Qed.
Lemma lem1393294 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1393295 (x : real) (y : real) : (term56 x y) = True.
Proof. exact (@lem1393294 (term50 x y)). Qed.
Lemma lem1393296 (x : real) (y : real) : (term55 x y) = True.
Proof. exact (TRANS (@lem1393292 x y) (@lem1393295 x y)). Qed.
Lemma lem1393297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393298 (x : real) (y : real) : (term57 x y) = (and True).
Proof. exact (MK_COMB (@lem1393297) (@lem1393296 x y)). Qed.
Lemma lem1393304 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1393305 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1393304 p q p' q'). Qed.
Lemma lem1393306 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1393305 p q p'). Qed.
Lemma lem1393307 (x : real) (y : real) : term58 x y.
Proof. exact (@lem1393306 (term59 x y) ((real_mul x y) = term18)). Qed.
Lemma lem1393308 (x : real) (y : real) (p' : Prop) : term60 x y p'.
Proof. exact (@lem1393307 x y p'). Qed.
Lemma lem1393309 (x : real) (y : real) (p' : Prop) : (term60 x y p') = (term61 x y p').
Proof. exact (eq_refl (term60 x y p')). Qed.
Lemma lem1393310 (x : real) (y : real) (p' : Prop) : term61 x y p'.
Proof. exact (EQ_MP (@lem1393309 x y p') (@lem1393308 x y p')). Qed.
Lemma lem1393311 (x : real) (y : real) (p' : Prop) (q' : Prop) : term62 x y p' q'.
Proof. exact (@lem1393310 x y p' q'). Qed.
Lemma lem1393312 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term62 x y p' q') = (term63 x y p' q').
Proof. exact (eq_refl (term62 x y p' q')). Qed.
Lemma lem1393313 (x : real) (y : real) (p' : Prop) (q' : Prop) : term63 x y p' q'.
Proof. exact (EQ_MP (@lem1393312 x y p' q') (@lem1393311 x y p' q')). Qed.
Lemma lem1393319 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1393162 y x) (@lem1393161 y x)). Qed.
Lemma lem1393320 (y : real) : (term64 y) = (term65 y).
Proof. exact (@lem1393319 term18 y). Qed.
Lemma lem1393321 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1393322 (x : real) (y : real) : (term59 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem1393321 x) (@lem1393320 y)). Qed.
Lemma lem1393327 (x : real) (y : real) (q' : Prop) : term67 x y q'.
Proof. exact (@lem1393313 x y (term66 x y) q'). Qed.
Lemma lem1393328 (x : real) (y : real) (q' : Prop) : term68 x y q'.
Proof. exact (@lem1393327 x y q' (@lem1393322 x y)). Qed.
Lemma lem1393329 (x : real) (y : real) (h1 : term66 x y) : term66 x y.
Proof. exact (h1). Qed.
Lemma lem1393337 (x : real) (y : real) (h1 : term66 x y) : x = term18.
Proof. exact (proj1 (@lem1393329 x y h1)). Qed.
Lemma lem1393338 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1393339 (x : real) (y : real) (h1 : term66 x y) : (real_mul x) = term32.
Proof. exact (MK_COMB (@lem1393338) (@lem1393337 x y h1)). Qed.
Lemma lem1393340 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1393341 (x : real) (y : real) (h1 : term66 x y) : (real_mul x y) = (term20 y).
Proof. exact (MK_COMB (@lem1393339 x y h1) (@lem1393340 y)). Qed.
Lemma lem1393343 (x : real) : (term20 x) = term18.
Proof. exact (EQ_MP (@lem1393174 x) (@lem1393173 x)). Qed.
Lemma lem1393344 (y : real) : (term20 y) = term18.
Proof. exact (@lem1393343 y). Qed.
Lemma lem1393345 (x : real) (y : real) (h1 : term66 x y) : (real_mul x y) = term18.
Proof. exact (TRANS (@lem1393341 x y h1) (@lem1393344 y)). Qed.
Lemma lem1393346 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1393347 (x : real) (y : real) (h1 : term66 x y) : (term34 x y) = term35.
Proof. exact (MK_COMB (@lem1393346) (@lem1393345 x y h1)). Qed.
Lemma lem1393348 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1393349 (x : real) (y : real) (h1 : term66 x y) : ((real_mul x y) = term18) = (term18 = term18).
Proof. exact (MK_COMB (@lem1393347 x y h1) (@lem1393348)). Qed.
Lemma lem1393351 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1393352 (x : real) : (x = x) = True.
Proof. exact (@lem1393351 real x). Qed.
Lemma lem1393353 : (term18 = term18) = True.
Proof. exact (@lem1393352 term18). Qed.
Lemma lem1393354 (x : real) (y : real) (h1 : term66 x y) : ((real_mul x y) = term18) = True.
Proof. exact (TRANS (@lem1393349 x y h1) (@lem1393353)). Qed.
Lemma lem1393355 (x : real) (y : real) : term69 x y.
Proof. exact (fun h0 : term66 x y => @lem1393354 x y h0). Qed.
Lemma lem1393356 (x : real) (y : real) : term70 x y.
Proof. exact (@lem1393328 x y True). Qed.
Lemma lem1393357 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (@lem1393356 x y (@lem1393355 x y)). Qed.
Lemma lem1393359 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1393360 (x : real) (y : real) : (term72 x y) = True.
Proof. exact (@lem1393359 (term66 x y)). Qed.
Lemma lem1393361 (x : real) (y : real) : (term71 x y) = True.
Proof. exact (TRANS (@lem1393357 x y) (@lem1393360 x y)). Qed.
Lemma lem1393362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393363 (x : real) (y : real) : (term73 x y) = (and True).
Proof. exact (MK_COMB (@lem1393362) (@lem1393361 x y)). Qed.
Lemma lem1393369 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1393370 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1393369 p q p' q'). Qed.
Lemma lem1393371 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1393370 p q p'). Qed.
Lemma lem1393372 (x : real) (y : real) : term74 x y.
Proof. exact (@lem1393371 (term75 x y) ((real_mul x y) = term18)). Qed.
Lemma lem1393373 (x : real) (y : real) (p' : Prop) : term76 x y p'.
Proof. exact (@lem1393372 x y p'). Qed.
Lemma lem1393374 (x : real) (y : real) (p' : Prop) : (term76 x y p') = (term77 x y p').
Proof. exact (eq_refl (term76 x y p')). Qed.
Lemma lem1393375 (x : real) (y : real) (p' : Prop) : term77 x y p'.
Proof. exact (EQ_MP (@lem1393374 x y p') (@lem1393373 x y p')). Qed.
Lemma lem1393376 (x : real) (y : real) (p' : Prop) (q' : Prop) : term78 x y p' q'.
Proof. exact (@lem1393375 x y p' q'). Qed.
Lemma lem1393377 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term78 x y p' q') = (term79 x y p' q').
Proof. exact (eq_refl (term78 x y p' q')). Qed.
Lemma lem1393378 (x : real) (y : real) (p' : Prop) (q' : Prop) : term79 x y p' q'.
Proof. exact (EQ_MP (@lem1393377 x y p' q') (@lem1393376 x y p' q')). Qed.
Lemma lem1393382 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1393168 y x) (@lem1393167 y x)). Qed.
Lemma lem1393383 (x : real) : (term47 x) = (term48 x).
Proof. exact (@lem1393382 term18 x). Qed.
Lemma lem1393384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393385 (x : real) : (term80 x) = (term81 x).
Proof. exact (MK_COMB (@lem1393384) (@lem1393383 x)). Qed.
Lemma lem1393388 (y : real) : (y = term18) = (y = term18).
Proof. exact (eq_refl (y = term18)). Qed.
Lemma lem1393389 (x : real) (y : real) : (term75 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1393385 x) (@lem1393388 y)). Qed.
Lemma lem1393394 (x : real) (y : real) (q' : Prop) : term83 x y q'.
Proof. exact (@lem1393378 x y (term82 x y) q'). Qed.
Lemma lem1393395 (x : real) (y : real) (q' : Prop) : term84 x y q'.
Proof. exact (@lem1393394 x y q' (@lem1393389 x y)). Qed.
Lemma lem1393396 (x : real) (y : real) (h1 : term82 x y) : term82 x y.
Proof. exact (h1). Qed.
Lemma lem1393404 (x : real) (y : real) (h1 : term82 x y) : y = term18.
Proof. exact (proj2 (@lem1393396 x y h1)). Qed.
Lemma lem1393405 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1393406 (x : real) (y : real) (h1 : term82 x y) : (real_mul x y) = (term17 x).
Proof. exact (MK_COMB (@lem1393405 x) (@lem1393404 x y h1)). Qed.
Lemma lem1393408 (x : real) : (term17 x) = term18.
Proof. exact (EQ_MP (@lem1393171 x) (@lem1393170 x)). Qed.
Lemma lem1393409 (x : real) (y : real) (h1 : term82 x y) : (real_mul x y) = term18.
Proof. exact (TRANS (@lem1393406 x y h1) (@lem1393408 x)). Qed.
Lemma lem1393410 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1393411 (x : real) (y : real) (h1 : term82 x y) : (term34 x y) = term35.
Proof. exact (MK_COMB (@lem1393410) (@lem1393409 x y h1)). Qed.
Lemma lem1393412 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1393413 (x : real) (y : real) (h1 : term82 x y) : ((real_mul x y) = term18) = (term18 = term18).
Proof. exact (MK_COMB (@lem1393411 x y h1) (@lem1393412)). Qed.
Lemma lem1393415 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1393416 (x : real) : (x = x) = True.
Proof. exact (@lem1393415 real x). Qed.
Lemma lem1393417 : (term18 = term18) = True.
Proof. exact (@lem1393416 term18). Qed.
Lemma lem1393418 (x : real) (y : real) (h1 : term82 x y) : ((real_mul x y) = term18) = True.
Proof. exact (TRANS (@lem1393413 x y h1) (@lem1393417)). Qed.
Lemma lem1393419 (x : real) (y : real) : term85 x y.
Proof. exact (fun h0 : term82 x y => @lem1393418 x y h0). Qed.
Lemma lem1393420 (x : real) (y : real) : term86 x y.
Proof. exact (@lem1393395 x y True). Qed.
Lemma lem1393421 (x : real) (y : real) : (term87 x y) = (term88 x y).
Proof. exact (@lem1393420 x y (@lem1393419 x y)). Qed.
Lemma lem1393423 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1393424 (x : real) (y : real) : (term88 x y) = True.
Proof. exact (@lem1393423 (term82 x y)). Qed.
Lemma lem1393425 (x : real) (y : real) : (term87 x y) = True.
Proof. exact (TRANS (@lem1393421 x y) (@lem1393424 x y)). Qed.
Lemma lem1393426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393427 (x : real) (y : real) : (term89 x y) = (and True).
Proof. exact (MK_COMB (@lem1393426) (@lem1393425 x y)). Qed.
Lemma lem1393433 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1393434 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1393433 p q p' q'). Qed.
Lemma lem1393435 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1393434 p q p'). Qed.
Lemma lem1393436 (x : real) (y : real) : term90 x y.
Proof. exact (@lem1393435 (term91 x y) (term92 x y)). Qed.
Lemma lem1393437 (x : real) (y : real) (p' : Prop) : term93 x y p'.
Proof. exact (@lem1393436 x y p'). Qed.
Lemma lem1393438 (x : real) (y : real) (p' : Prop) : (term93 x y p') = (term94 x y p').
Proof. exact (eq_refl (term93 x y p')). Qed.
Lemma lem1393439 (x : real) (y : real) (p' : Prop) : term94 x y p'.
Proof. exact (EQ_MP (@lem1393438 x y p') (@lem1393437 x y p')). Qed.
Lemma lem1393440 (x : real) (y : real) (p' : Prop) (q' : Prop) : term95 x y p' q'.
Proof. exact (@lem1393439 x y p' q'). Qed.
Lemma lem1393441 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term95 x y p' q') = (term96 x y p' q').
Proof. exact (eq_refl (term95 x y p' q')). Qed.
Lemma lem1393442 (x : real) (y : real) (p' : Prop) (q' : Prop) : term96 x y p' q'.
Proof. exact (EQ_MP (@lem1393441 x y p' q') (@lem1393440 x y p' q')). Qed.
Lemma lem1393446 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1393168 y x) (@lem1393167 y x)). Qed.
Lemma lem1393447 (x : real) : (term47 x) = (term48 x).
Proof. exact (@lem1393446 term18 x). Qed.
Lemma lem1393448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393449 (x : real) : (term80 x) = (term81 x).
Proof. exact (MK_COMB (@lem1393448) (@lem1393447 x)). Qed.
Lemma lem1393451 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1393168 y x) (@lem1393167 y x)). Qed.
Lemma lem1393452 (y : real) : (term47 y) = (term48 y).
Proof. exact (@lem1393451 term18 y). Qed.
Lemma lem1393453 (x : real) (y : real) : (term91 x y) = (term4 x y).
Proof. exact (MK_COMB (@lem1393449 x) (@lem1393452 y)). Qed.
Lemma lem1393456 (x : real) (y : real) (q' : Prop) : term97 x y q'.
Proof. exact (@lem1393442 x y (term4 x y) q'). Qed.
Lemma lem1393457 (x : real) (y : real) (q' : Prop) : term98 x y q'.
Proof. exact (@lem1393456 x y q' (@lem1393453 x y)). Qed.
Lemma lem1393466 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1393168 y x) (@lem1393167 y x)). Qed.
Lemma lem1393467 (x : real) (y : real) : (term92 x y) = (term5 x y).
Proof. exact (@lem1393466 term18 (real_mul x y)). Qed.
Lemma lem1393468 (x : real) (y : real) : term99 x y.
Proof. exact (fun h0 : term4 x y => @lem1393467 x y). Qed.
Lemma lem1393469 (x : real) (y : real) : term100 x y.
Proof. exact (@lem1393457 x y (term5 x y)). Qed.
Lemma lem1393470 (x : real) (y : real) : (term101 x y) = (term3 x y).
Proof. exact (@lem1393469 x y (@lem1393468 x y)). Qed.
Lemma lem1393502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393503 (x : real) (y : real) : (term102 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem1393502) (@lem1393470 x y)). Qed.
Lemma lem1393540 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1393541 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1393540 p q p' q'). Qed.
Lemma lem1393542 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1393541 p q p'). Qed.
Lemma lem1393543 (x : real) (y : real) : term104 x y.
Proof. exact (@lem1393542 (term105 x y) (term92 x y)). Qed.
Lemma lem1393544 (x : real) (y : real) (p' : Prop) : term106 x y p'.
Proof. exact (@lem1393543 x y p'). Qed.
Lemma lem1393545 (x : real) (y : real) (p' : Prop) : (term106 x y p') = (term107 x y p').
Proof. exact (eq_refl (term106 x y p')). Qed.
Lemma lem1393546 (x : real) (y : real) (p' : Prop) : term107 x y p'.
Proof. exact (EQ_MP (@lem1393545 x y p') (@lem1393544 x y p')). Qed.
Lemma lem1393547 (x : real) (y : real) (p' : Prop) (q' : Prop) : term108 x y p' q'.
Proof. exact (@lem1393546 x y p' q'). Qed.
Lemma lem1393548 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term108 x y p' q') = (term109 x y p' q').
Proof. exact (eq_refl (term108 x y p' q')). Qed.
Lemma lem1393549 (x : real) (y : real) (p' : Prop) (q' : Prop) : term109 x y p' q'.
Proof. exact (EQ_MP (@lem1393548 x y p' q') (@lem1393547 x y p' q')). Qed.
Lemma lem1393553 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1393168 y x) (@lem1393167 y x)). Qed.
Lemma lem1393554 (x : real) : (term47 x) = (term48 x).
Proof. exact (@lem1393553 term18 x). Qed.
Lemma lem1393555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393556 (x : real) : (term80 x) = (term81 x).
Proof. exact (MK_COMB (@lem1393555) (@lem1393554 x)). Qed.
Lemma lem1393558 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1393162 y x) (@lem1393161 y x)). Qed.
Lemma lem1393559 (y : real) : (term64 y) = (term65 y).
Proof. exact (@lem1393558 term18 y). Qed.
Lemma lem1393560 (x : real) (y : real) : (term105 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1393556 x) (@lem1393559 y)). Qed.
Lemma lem1393563 (x : real) (y : real) (q' : Prop) : term111 x y q'.
Proof. exact (@lem1393549 x y (term110 x y) q'). Qed.
Lemma lem1393564 (x : real) (y : real) (q' : Prop) : term112 x y q'.
Proof. exact (@lem1393563 x y q' (@lem1393560 x y)). Qed.
Lemma lem1393573 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1393168 y x) (@lem1393167 y x)). Qed.
Lemma lem1393574 (x : real) (y : real) : (term92 x y) = (term5 x y).
Proof. exact (@lem1393573 term18 (real_mul x y)). Qed.
Lemma lem1393575 (x : real) (y : real) : term113 x y.
Proof. exact (fun h0 : term110 x y => @lem1393574 x y). Qed.
Lemma lem1393576 (x : real) (y : real) : term114 x y.
Proof. exact (@lem1393564 x y (term5 x y)). Qed.
Lemma lem1393577 (x : real) (y : real) : (term115 x y) = (term116 x y).
Proof. exact (@lem1393576 x y (@lem1393575 x y)). Qed.
Lemma lem1393609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393610 (x : real) (y : real) : (term117 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1393609) (@lem1393577 x y)). Qed.
Lemma lem1393647 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1393648 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1393647 p q p' q'). Qed.
Lemma lem1393649 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1393648 p q p'). Qed.
Lemma lem1393650 (x : real) (y : real) : term119 x y.
Proof. exact (@lem1393649 (term120 x y) ((real_mul x y) = term18)). Qed.
Lemma lem1393651 (x : real) (y : real) (p' : Prop) : term121 x y p'.
Proof. exact (@lem1393650 x y p'). Qed.
Lemma lem1393652 (x : real) (y : real) (p' : Prop) : (term121 x y p') = (term122 x y p').
Proof. exact (eq_refl (term121 x y p')). Qed.
Lemma lem1393653 (x : real) (y : real) (p' : Prop) : term122 x y p'.
Proof. exact (EQ_MP (@lem1393652 x y p') (@lem1393651 x y p')). Qed.
Lemma lem1393654 (x : real) (y : real) (p' : Prop) (q' : Prop) : term123 x y p' q'.
Proof. exact (@lem1393653 x y p' q'). Qed.
Lemma lem1393655 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term123 x y p' q') = (term124 x y p' q').
Proof. exact (eq_refl (term123 x y p' q')). Qed.
Lemma lem1393656 (x : real) (y : real) (p' : Prop) (q' : Prop) : term124 x y p' q'.
Proof. exact (EQ_MP (@lem1393655 x y p' q') (@lem1393654 x y p' q')). Qed.
Lemma lem1393660 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1393162 y x) (@lem1393161 y x)). Qed.
Lemma lem1393661 (x : real) : (term64 x) = (term65 x).
Proof. exact (@lem1393660 term18 x). Qed.
Lemma lem1393662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393663 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1393662) (@lem1393661 x)). Qed.
Lemma lem1393666 (y : real) : (y = term18) = (y = term18).
Proof. exact (eq_refl (y = term18)). Qed.
Lemma lem1393667 (x : real) (y : real) : (term120 x y) = (term127 x y).
Proof. exact (MK_COMB (@lem1393663 x) (@lem1393666 y)). Qed.
Lemma lem1393672 (x : real) (y : real) (q' : Prop) : term128 x y q'.
Proof. exact (@lem1393656 x y (term127 x y) q'). Qed.
Lemma lem1393673 (x : real) (y : real) (q' : Prop) : term129 x y q'.
Proof. exact (@lem1393672 x y q' (@lem1393667 x y)). Qed.
Lemma lem1393674 (x : real) (y : real) (h1 : term127 x y) : term127 x y.
Proof. exact (h1). Qed.
Lemma lem1393682 (x : real) (y : real) (h1 : term127 x y) : y = term18.
Proof. exact (proj2 (@lem1393674 x y h1)). Qed.
Lemma lem1393683 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1393684 (x : real) (y : real) (h1 : term127 x y) : (real_mul x y) = (term17 x).
Proof. exact (MK_COMB (@lem1393683 x) (@lem1393682 x y h1)). Qed.
Lemma lem1393686 (x : real) : (term17 x) = term18.
Proof. exact (EQ_MP (@lem1393171 x) (@lem1393170 x)). Qed.
Lemma lem1393687 (x : real) (y : real) (h1 : term127 x y) : (real_mul x y) = term18.
Proof. exact (TRANS (@lem1393684 x y h1) (@lem1393686 x)). Qed.
Lemma lem1393688 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1393689 (x : real) (y : real) (h1 : term127 x y) : (term34 x y) = term35.
Proof. exact (MK_COMB (@lem1393688) (@lem1393687 x y h1)). Qed.
Lemma lem1393690 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1393691 (x : real) (y : real) (h1 : term127 x y) : ((real_mul x y) = term18) = (term18 = term18).
Proof. exact (MK_COMB (@lem1393689 x y h1) (@lem1393690)). Qed.
Lemma lem1393693 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1393694 (x : real) : (x = x) = True.
Proof. exact (@lem1393693 real x). Qed.
Lemma lem1393695 : (term18 = term18) = True.
Proof. exact (@lem1393694 term18). Qed.
Lemma lem1393696 (x : real) (y : real) (h1 : term127 x y) : ((real_mul x y) = term18) = True.
Proof. exact (TRANS (@lem1393691 x y h1) (@lem1393695)). Qed.
Lemma lem1393697 (x : real) (y : real) : term130 x y.
Proof. exact (fun h0 : term127 x y => @lem1393696 x y h0). Qed.
Lemma lem1393698 (x : real) (y : real) : term131 x y.
Proof. exact (@lem1393673 x y True). Qed.
Lemma lem1393699 (x : real) (y : real) : (term132 x y) = (term133 x y).
Proof. exact (@lem1393698 x y (@lem1393697 x y)). Qed.
Lemma lem1393701 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1393702 (x : real) (y : real) : (term133 x y) = True.
Proof. exact (@lem1393701 (term127 x y)). Qed.
Lemma lem1393703 (x : real) (y : real) : (term132 x y) = True.
Proof. exact (TRANS (@lem1393699 x y) (@lem1393702 x y)). Qed.
Lemma lem1393704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393705 (x : real) (y : real) : (term134 x y) = (and True).
Proof. exact (MK_COMB (@lem1393704) (@lem1393703 x y)). Qed.
Lemma lem1393711 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1393712 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1393711 p q p' q'). Qed.
Lemma lem1393713 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1393712 p q p'). Qed.
Lemma lem1393714 (x : real) (y : real) : term135 x y.
Proof. exact (@lem1393713 (term136 x y) (term92 x y)). Qed.
Lemma lem1393715 (x : real) (y : real) (p' : Prop) : term137 x y p'.
Proof. exact (@lem1393714 x y p'). Qed.
Lemma lem1393716 (x : real) (y : real) (p' : Prop) : (term137 x y p') = (term138 x y p').
Proof. exact (eq_refl (term137 x y p')). Qed.
Lemma lem1393717 (x : real) (y : real) (p' : Prop) : term138 x y p'.
Proof. exact (EQ_MP (@lem1393716 x y p') (@lem1393715 x y p')). Qed.
Lemma lem1393718 (x : real) (y : real) (p' : Prop) (q' : Prop) : term139 x y p' q'.
Proof. exact (@lem1393717 x y p' q'). Qed.
Lemma lem1393719 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term139 x y p' q') = (term140 x y p' q').
Proof. exact (eq_refl (term139 x y p' q')). Qed.
Lemma lem1393720 (x : real) (y : real) (p' : Prop) (q' : Prop) : term140 x y p' q'.
Proof. exact (EQ_MP (@lem1393719 x y p' q') (@lem1393718 x y p' q')). Qed.
Lemma lem1393724 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1393162 y x) (@lem1393161 y x)). Qed.
Lemma lem1393725 (x : real) : (term64 x) = (term65 x).
Proof. exact (@lem1393724 term18 x). Qed.
Lemma lem1393726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393727 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1393726) (@lem1393725 x)). Qed.
Lemma lem1393729 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1393168 y x) (@lem1393167 y x)). Qed.
Lemma lem1393730 (y : real) : (term47 y) = (term48 y).
Proof. exact (@lem1393729 term18 y). Qed.
Lemma lem1393731 (x : real) (y : real) : (term136 x y) = (term141 x y).
Proof. exact (MK_COMB (@lem1393727 x) (@lem1393730 y)). Qed.
Lemma lem1393734 (x : real) (y : real) (q' : Prop) : term142 x y q'.
Proof. exact (@lem1393720 x y (term141 x y) q'). Qed.
Lemma lem1393735 (x : real) (y : real) (q' : Prop) : term143 x y q'.
Proof. exact (@lem1393734 x y q' (@lem1393731 x y)). Qed.
Lemma lem1393744 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1393168 y x) (@lem1393167 y x)). Qed.
Lemma lem1393745 (x : real) (y : real) : (term92 x y) = (term5 x y).
Proof. exact (@lem1393744 term18 (real_mul x y)). Qed.
Lemma lem1393746 (x : real) (y : real) : term144 x y.
Proof. exact (fun h0 : term141 x y => @lem1393745 x y). Qed.
Lemma lem1393747 (x : real) (y : real) : term145 x y.
Proof. exact (@lem1393735 x y (term5 x y)). Qed.
Lemma lem1393748 (x : real) (y : real) : (term146 x y) = (term147 x y).
Proof. exact (@lem1393747 x y (@lem1393746 x y)). Qed.
Lemma lem1393780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393781 (x : real) (y : real) : (term148 x y) = (term149 x y).
Proof. exact (MK_COMB (@lem1393780) (@lem1393748 x y)). Qed.
Lemma lem1393816 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1393817 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1393816 p q p' q'). Qed.
Lemma lem1393818 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1393817 p q p'). Qed.
Lemma lem1393819 (x : real) (y : real) : term150 x y.
Proof. exact (@lem1393818 (term151 x y) (term152 x y)). Qed.
Lemma lem1393820 (x : real) (y : real) (p' : Prop) : term153 x y p'.
Proof. exact (@lem1393819 x y p'). Qed.
Lemma lem1393821 (x : real) (y : real) (p' : Prop) : (term153 x y p') = (term154 x y p').
Proof. exact (eq_refl (term153 x y p')). Qed.
Lemma lem1393822 (x : real) (y : real) (p' : Prop) : term154 x y p'.
Proof. exact (EQ_MP (@lem1393821 x y p') (@lem1393820 x y p')). Qed.
Lemma lem1393823 (x : real) (y : real) (p' : Prop) (q' : Prop) : term155 x y p' q'.
Proof. exact (@lem1393822 x y p' q'). Qed.
Lemma lem1393824 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term155 x y p' q') = (term156 x y p' q').
Proof. exact (eq_refl (term155 x y p' q')). Qed.
Lemma lem1393825 (x : real) (y : real) (p' : Prop) (q' : Prop) : term156 x y p' q'.
Proof. exact (EQ_MP (@lem1393824 x y p' q') (@lem1393823 x y p' q')). Qed.
Lemma lem1393829 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1393162 y x) (@lem1393161 y x)). Qed.
Lemma lem1393830 (x : real) : (term64 x) = (term65 x).
Proof. exact (@lem1393829 term18 x). Qed.
Lemma lem1393831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1393832 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1393831) (@lem1393830 x)). Qed.
Lemma lem1393834 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1393162 y x) (@lem1393161 y x)). Qed.
Lemma lem1393835 (y : real) : (term64 y) = (term65 y).
Proof. exact (@lem1393834 term18 y). Qed.
Lemma lem1393836 (x : real) (y : real) : (term151 x y) = (term157 x y).
Proof. exact (MK_COMB (@lem1393832 x) (@lem1393835 y)). Qed.
Lemma lem1393839 (x : real) (y : real) (q' : Prop) : term158 x y q'.
Proof. exact (@lem1393825 x y (term157 x y) q'). Qed.
Lemma lem1393840 (x : real) (y : real) (q' : Prop) : term159 x y q'.
Proof. exact (@lem1393839 x y q' (@lem1393836 x y)). Qed.
Lemma lem1393849 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1393162 y x) (@lem1393161 y x)). Qed.
Lemma lem1393850 (x : real) (y : real) : (term152 x y) = (term160 x y).
Proof. exact (@lem1393849 term18 (real_mul x y)). Qed.
Lemma lem1393851 (x : real) (y : real) : term161 x y.
Proof. exact (fun h0 : term157 x y => @lem1393850 x y). Qed.
Lemma lem1393852 (x : real) (y : real) : term162 x y.
Proof. exact (@lem1393840 x y (term160 x y)). Qed.
Lemma lem1393853 (x : real) (y : real) : (term163 x y) = (term164 x y).
Proof. exact (@lem1393852 x y (@lem1393851 x y)). Qed.
Lemma lem1393885 (x : real) (y : real) : (term165 x y) = (term166 x y).
Proof. exact (MK_COMB (@lem1393781 x y) (@lem1393853 x y)). Qed.
Lemma lem1393950 (x : real) (y : real) : (term167 x y) = (term168 x y).
Proof. exact (MK_COMB (@lem1393705 x y) (@lem1393885 x y)). Qed.
Lemma lem1393952 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1393953 (x : real) (y : real) : (term168 x y) = (term166 x y).
Proof. exact (@lem1393952 (term166 x y)). Qed.
Lemma lem1394018 (x : real) (y : real) : (term167 x y) = (term166 x y).
Proof. exact (TRANS (@lem1393950 x y) (@lem1393953 x y)). Qed.
Lemma lem1394019 (x : real) (y : real) : (term169 x y) = (term170 x y).
Proof. exact (MK_COMB (@lem1393610 x y) (@lem1394018 x y)). Qed.
Lemma lem1394117 (x : real) (y : real) : (term171 x y) = (term172 x y).
Proof. exact (MK_COMB (@lem1393503 x y) (@lem1394019 x y)). Qed.
Lemma lem1394248 (x : real) (y : real) : (term173 x y) = (term174 x y).
Proof. exact (MK_COMB (@lem1393427 x y) (@lem1394117 x y)). Qed.
Lemma lem1394250 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1394251 (x : real) (y : real) : (term174 x y) = (term172 x y).
Proof. exact (@lem1394250 (term172 x y)). Qed.
Lemma lem1394382 (x : real) (y : real) : (term173 x y) = (term172 x y).
Proof. exact (TRANS (@lem1394248 x y) (@lem1394251 x y)). Qed.
Lemma lem1394383 (x : real) (y : real) : (term175 x y) = (term174 x y).
Proof. exact (MK_COMB (@lem1393363 x y) (@lem1394382 x y)). Qed.
Lemma lem1394385 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1394386 (x : real) (y : real) : (term174 x y) = (term172 x y).
Proof. exact (@lem1394385 (term172 x y)). Qed.
Lemma lem1394517 (x : real) (y : real) : (term175 x y) = (term172 x y).
Proof. exact (TRANS (@lem1394383 x y) (@lem1394386 x y)). Qed.
Lemma lem1394518 (x : real) (y : real) : (term176 x y) = (term174 x y).
Proof. exact (MK_COMB (@lem1393298 x y) (@lem1394517 x y)). Qed.
Lemma lem1394520 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1394521 (x : real) (y : real) : (term174 x y) = (term172 x y).
Proof. exact (@lem1394520 (term172 x y)). Qed.
Lemma lem1394652 (x : real) (y : real) : (term176 x y) = (term172 x y).
Proof. exact (TRANS (@lem1394518 x y) (@lem1394521 x y)). Qed.
Lemma lem1394653 (x : real) (y : real) : (term177 x y) = (term174 x y).
Proof. exact (MK_COMB (@lem1393233 x y) (@lem1394652 x y)). Qed.
Lemma lem1394655 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1394656 (x : real) (y : real) : (term174 x y) = (term172 x y).
Proof. exact (@lem1394655 (term172 x y)). Qed.
Lemma lem1394787 (x : real) (y : real) : (term177 x y) = (term172 x y).
Proof. exact (TRANS (@lem1394653 x y) (@lem1394656 x y)). Qed.
Lemma lem1394788 (x : real) (y : real) : (term172 x y) = (term177 x y).
Proof. exact (SYM (@lem1394787 x y)). Qed.
Lemma lem1394794 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1394795 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1394794 p q p' q'). Qed.
Lemma lem1394796 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1394795 p q p'). Qed.
Lemma lem1394797 (x : real) (y : real) : term178 x y.
Proof. exact (@lem1394796 (term4 x y) (term5 x y)). Qed.
Lemma lem1394798 (x : real) (y : real) (p' : Prop) : term179 x y p'.
Proof. exact (@lem1394797 x y p'). Qed.
Lemma lem1394799 (x : real) (y : real) (p' : Prop) : (term179 x y p') = (term180 x y p').
Proof. exact (eq_refl (term179 x y p')). Qed.
Lemma lem1394800 (x : real) (y : real) (p' : Prop) : term180 x y p'.
Proof. exact (EQ_MP (@lem1394799 x y p') (@lem1394798 x y p')). Qed.
Lemma lem1394801 (x : real) (y : real) (p' : Prop) (q' : Prop) : term181 x y p' q'.
Proof. exact (@lem1394800 x y p' q'). Qed.
Lemma lem1394802 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term181 x y p' q') = (term182 x y p' q').
Proof. exact (eq_refl (term181 x y p' q')). Qed.
Lemma lem1394803 (x : real) (y : real) (p' : Prop) (q' : Prop) : term182 x y p' q'.
Proof. exact (EQ_MP (@lem1394802 x y p' q') (@lem1394801 x y p' q')). Qed.
Lemma lem1394806 (x : real) (y : real) : (term4 x y) = (term4 x y).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1394807 (x : real) (y : real) (q' : Prop) : term183 x y q'.
Proof. exact (@lem1394803 x y (term4 x y) q'). Qed.
Lemma lem1394808 (x : real) (y : real) (q' : Prop) : term184 x y q'.
Proof. exact (@lem1394807 x y q' (@lem1394806 x y)). Qed.
Lemma lem1394809 (x : real) (y : real) (h1 : term4 x y) : term4 x y.
Proof. exact (h1). Qed.
Lemma lem1394810 (x : real) (y : real) (h1 : term4 x y) : term48 y.
Proof. exact (proj2 (@lem1394809 x y h1)). Qed.
Lemma lem1394811 (y : real) : (term48 y) = ((term48 y) = True).
Proof. exact (@lem7 (term48 y)). Qed.
Lemma lem1394813 (x : real) (y : real) (h1 : term4 x y) : term48 x.
Proof. exact (proj1 (@lem1394809 x y h1)). Qed.
Lemma lem1394814 (x : real) : (term48 x) = ((term48 x) = True).
Proof. exact (@lem7 (term48 x)). Qed.
Lemma lem1394817 (x : real) (y : real) : term185 x y.
Proof. exact (fun h0 : term4 x y => @lem1393146 x y h0). Qed.
Lemma lem1394821 (x : real) (y : real) (h1 : term4 x y) : (term48 x) = True.
Proof. exact (EQ_MP (@lem1394814 x) (@lem1394813 x y h1)). Qed.
Lemma lem1394822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1394823 (x : real) (y : real) (h1 : term4 x y) : (term81 x) = (and True).
Proof. exact (MK_COMB (@lem1394822) (@lem1394821 x y h1)). Qed.
Lemma lem1394825 (x : real) (y : real) (h1 : term4 x y) : (term48 y) = True.
Proof. exact (EQ_MP (@lem1394811 y) (@lem1394810 x y h1)). Qed.
Lemma lem1394826 (x : real) (y : real) (h1 : term4 x y) : (term4 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1394823 x y h1) (@lem1394825 x y h1)). Qed.
Lemma lem1394828 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1394829 : (True /\ True) = True.
Proof. exact (@lem1394828 True). Qed.
Lemma lem1394830 (x : real) (y : real) (h1 : term4 x y) : (term4 x y) = True.
Proof. exact (TRANS (@lem1394826 x y h1) (@lem1394829)). Qed.
Lemma lem1394831 (x : real) (y : real) (h1 : term4 x y) : True = (term4 x y).
Proof. exact (SYM (@lem1394830 x y h1)). Qed.
Lemma lem1394832 (x : real) (y : real) (h1 : term4 x y) : term4 x y.
Proof. exact (EQ_MP (@lem1394831 x y h1) (@lem0)). Qed.
Lemma lem1394833 (x : real) (y : real) (h1 : term4 x y) : (term5 x y) = True.
Proof. exact (@lem1394817 x y (@lem1394832 x y h1)). Qed.
Lemma lem1394834 (x : real) (y : real) : term185 x y.
Proof. exact (fun h0 : term4 x y => @lem1394833 x y h0). Qed.
Lemma lem1394835 (x : real) (y : real) : term186 x y.
Proof. exact (@lem1394808 x y True). Qed.
Lemma lem1394836 (x : real) (y : real) : (term3 x y) = (term187 x y).
Proof. exact (@lem1394835 x y (@lem1394834 x y)). Qed.
Lemma lem1394838 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1394839 (x : real) (y : real) : (term187 x y) = True.
Proof. exact (@lem1394838 (term4 x y)). Qed.
Lemma lem1394840 (x : real) (y : real) : (term3 x y) = True.
Proof. exact (TRANS (@lem1394836 x y) (@lem1394839 x y)). Qed.
Lemma lem1394841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1394842 (x : real) (y : real) : (term103 x y) = (and True).
Proof. exact (MK_COMB (@lem1394841) (@lem1394840 x y)). Qed.
Lemma lem1394848 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1394849 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1394848 p q p' q'). Qed.
Lemma lem1394850 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1394849 p q p'). Qed.
Lemma lem1394851 (x : real) (y : real) : term188 x y.
Proof. exact (@lem1394850 (term110 x y) (term5 x y)). Qed.
Lemma lem1394852 (x : real) (y : real) (p' : Prop) : term189 x y p'.
Proof. exact (@lem1394851 x y p'). Qed.
Lemma lem1394853 (x : real) (y : real) (p' : Prop) : (term189 x y p') = (term190 x y p').
Proof. exact (eq_refl (term189 x y p')). Qed.
Lemma lem1394854 (x : real) (y : real) (p' : Prop) : term190 x y p'.
Proof. exact (EQ_MP (@lem1394853 x y p') (@lem1394852 x y p')). Qed.
Lemma lem1394855 (x : real) (y : real) (p' : Prop) (q' : Prop) : term191 x y p' q'.
Proof. exact (@lem1394854 x y p' q'). Qed.
Lemma lem1394856 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term191 x y p' q') = (term192 x y p' q').
Proof. exact (eq_refl (term191 x y p' q')). Qed.
Lemma lem1394857 (x : real) (y : real) (p' : Prop) (q' : Prop) : term192 x y p' q'.
Proof. exact (EQ_MP (@lem1394856 x y p' q') (@lem1394855 x y p' q')). Qed.
Lemma lem1394861 (x : real) (y : real) : (real_lt x y) = (term9 x y).
Proof. exact (EQ_MP (@lem1393156 x y) (@lem1393155 x y)). Qed.
Lemma lem1394862 (y : real) : (term65 y) = (term193 y).
Proof. exact (@lem1394861 term18 y). Qed.
Lemma lem1394867 (x : real) : (term81 x) = (term81 x).
Proof. exact (eq_refl (term81 x)). Qed.
Lemma lem1394868 (x : real) (y : real) : (term110 x y) = (term194 x y).
Proof. exact (MK_COMB (@lem1394867 x) (@lem1394862 y)). Qed.
Lemma lem1394875 (x : real) (y : real) (q' : Prop) : term195 x y q'.
Proof. exact (@lem1394857 x y (term194 x y) q'). Qed.
Lemma lem1394876 (x : real) (y : real) (q' : Prop) : term196 x y q'.
Proof. exact (@lem1394875 x y q' (@lem1394868 x y)). Qed.
Lemma lem1394877 (x : real) (y : real) (h1 : term194 x y) : term194 x y.
Proof. exact (h1). Qed.
Lemma lem1394878 (x : real) (y : real) (h1 : term194 x y) : term193 y.
Proof. exact (proj2 (@lem1394877 x y h1)). Qed.
Lemma lem1394893 (x : real) (y : real) (h1 : term194 x y) : term48 y.
Proof. exact (proj1 (@lem1394878 x y h1)). Qed.
Lemma lem1394894 (y : real) : (term48 y) = ((term48 y) = True).
Proof. exact (@lem7 (term48 y)). Qed.
Lemma lem1394896 (x : real) (y : real) (h1 : term194 x y) : term48 x.
Proof. exact (proj1 (@lem1394877 x y h1)). Qed.
Lemma lem1394897 (x : real) : (term48 x) = ((term48 x) = True).
Proof. exact (@lem7 (term48 x)). Qed.
Lemma lem1394900 (x : real) (y : real) : term185 x y.
Proof. exact (fun h0 : term4 x y => @lem1393146 x y h0). Qed.
Lemma lem1394904 (x : real) (y : real) (h1 : term194 x y) : (term48 x) = True.
Proof. exact (EQ_MP (@lem1394897 x) (@lem1394896 x y h1)). Qed.
Lemma lem1394905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1394906 (x : real) (y : real) (h1 : term194 x y) : (term81 x) = (and True).
Proof. exact (MK_COMB (@lem1394905) (@lem1394904 x y h1)). Qed.
Lemma lem1394908 (x : real) (y : real) (h1 : term194 x y) : (term48 y) = True.
Proof. exact (EQ_MP (@lem1394894 y) (@lem1394893 x y h1)). Qed.
Lemma lem1394909 (x : real) (y : real) (h1 : term194 x y) : (term4 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1394906 x y h1) (@lem1394908 x y h1)). Qed.
Lemma lem1394911 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1394912 : (True /\ True) = True.
Proof. exact (@lem1394911 True). Qed.
Lemma lem1394913 (x : real) (y : real) (h1 : term194 x y) : (term4 x y) = True.
Proof. exact (TRANS (@lem1394909 x y h1) (@lem1394912)). Qed.
Lemma lem1394914 (x : real) (y : real) (h1 : term194 x y) : True = (term4 x y).
Proof. exact (SYM (@lem1394913 x y h1)). Qed.
Lemma lem1394915 (x : real) (y : real) (h1 : term194 x y) : term4 x y.
Proof. exact (EQ_MP (@lem1394914 x y h1) (@lem0)). Qed.
Lemma lem1394916 (x : real) (y : real) (h1 : term194 x y) : (term5 x y) = True.
Proof. exact (@lem1394900 x y (@lem1394915 x y h1)). Qed.
Lemma lem1394917 (x : real) (y : real) : term197 x y.
Proof. exact (fun h0 : term194 x y => @lem1394916 x y h0). Qed.
Lemma lem1394918 (x : real) (y : real) : term198 x y.
Proof. exact (@lem1394876 x y True). Qed.
Lemma lem1394919 (x : real) (y : real) : (term116 x y) = (term199 x y).
Proof. exact (@lem1394918 x y (@lem1394917 x y)). Qed.
Lemma lem1394921 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1394922 (x : real) (y : real) : (term199 x y) = True.
Proof. exact (@lem1394921 (term194 x y)). Qed.
Lemma lem1394923 (x : real) (y : real) : (term116 x y) = True.
Proof. exact (TRANS (@lem1394919 x y) (@lem1394922 x y)). Qed.
Lemma lem1394924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1394925 (x : real) (y : real) : (term118 x y) = (and True).
Proof. exact (MK_COMB (@lem1394924) (@lem1394923 x y)). Qed.
Lemma lem1394931 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1394932 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1394931 p q p' q'). Qed.
Lemma lem1394933 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1394932 p q p'). Qed.
Lemma lem1394934 (x : real) (y : real) : term200 x y.
Proof. exact (@lem1394933 (term141 x y) (term5 x y)). Qed.
Lemma lem1394935 (x : real) (y : real) (p' : Prop) : term201 x y p'.
Proof. exact (@lem1394934 x y p'). Qed.
Lemma lem1394936 (x : real) (y : real) (p' : Prop) : (term201 x y p') = (term202 x y p').
Proof. exact (eq_refl (term201 x y p')). Qed.
Lemma lem1394937 (x : real) (y : real) (p' : Prop) : term202 x y p'.
Proof. exact (EQ_MP (@lem1394936 x y p') (@lem1394935 x y p')). Qed.
Lemma lem1394938 (x : real) (y : real) (p' : Prop) (q' : Prop) : term203 x y p' q'.
Proof. exact (@lem1394937 x y p' q'). Qed.
Lemma lem1394939 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term203 x y p' q') = (term204 x y p' q').
Proof. exact (eq_refl (term203 x y p' q')). Qed.
Lemma lem1394940 (x : real) (y : real) (p' : Prop) (q' : Prop) : term204 x y p' q'.
Proof. exact (EQ_MP (@lem1394939 x y p' q') (@lem1394938 x y p' q')). Qed.
Lemma lem1394944 (x : real) (y : real) : (real_lt x y) = (term9 x y).
Proof. exact (EQ_MP (@lem1393156 x y) (@lem1393155 x y)). Qed.
Lemma lem1394945 (x : real) : (term65 x) = (term193 x).
Proof. exact (@lem1394944 term18 x). Qed.
Lemma lem1394950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1394951 (x : real) : (term126 x) = (term205 x).
Proof. exact (MK_COMB (@lem1394950) (@lem1394945 x)). Qed.
Lemma lem1394956 (y : real) : (term48 y) = (term48 y).
Proof. exact (eq_refl (term48 y)). Qed.
Lemma lem1394957 (x : real) (y : real) : (term141 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem1394951 x) (@lem1394956 y)). Qed.
Lemma lem1394964 (x : real) (y : real) (q' : Prop) : term207 x y q'.
Proof. exact (@lem1394940 x y (term206 x y) q'). Qed.
Lemma lem1394965 (x : real) (y : real) (q' : Prop) : term208 x y q'.
Proof. exact (@lem1394964 x y q' (@lem1394957 x y)). Qed.
Lemma lem1394966 (x : real) (y : real) (h1 : term206 x y) : term206 x y.
Proof. exact (h1). Qed.
Lemma lem1394967 (x : real) (y : real) (h1 : term206 x y) : term48 y.
Proof. exact (proj2 (@lem1394966 x y h1)). Qed.
Lemma lem1394968 (y : real) : (term48 y) = ((term48 y) = True).
Proof. exact (@lem7 (term48 y)). Qed.
Lemma lem1394970 (x : real) (y : real) (h1 : term206 x y) : term193 x.
Proof. exact (proj1 (@lem1394966 x y h1)). Qed.
Lemma lem1394985 (x : real) (y : real) (h1 : term206 x y) : term48 x.
Proof. exact (proj1 (@lem1394970 x y h1)). Qed.
Lemma lem1394986 (x : real) : (term48 x) = ((term48 x) = True).
Proof. exact (@lem7 (term48 x)). Qed.
Lemma lem1394989 (x : real) (y : real) : term185 x y.
Proof. exact (fun h0 : term4 x y => @lem1393146 x y h0). Qed.
Lemma lem1394993 (x : real) (y : real) (h1 : term206 x y) : (term48 x) = True.
Proof. exact (EQ_MP (@lem1394986 x) (@lem1394985 x y h1)). Qed.
Lemma lem1394994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1394995 (x : real) (y : real) (h1 : term206 x y) : (term81 x) = (and True).
Proof. exact (MK_COMB (@lem1394994) (@lem1394993 x y h1)). Qed.
Lemma lem1394997 (x : real) (y : real) (h1 : term206 x y) : (term48 y) = True.
Proof. exact (EQ_MP (@lem1394968 y) (@lem1394967 x y h1)). Qed.
Lemma lem1394998 (x : real) (y : real) (h1 : term206 x y) : (term4 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1394995 x y h1) (@lem1394997 x y h1)). Qed.
Lemma lem1395000 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1395001 : (True /\ True) = True.
Proof. exact (@lem1395000 True). Qed.
Lemma lem1395002 (x : real) (y : real) (h1 : term206 x y) : (term4 x y) = True.
Proof. exact (TRANS (@lem1394998 x y h1) (@lem1395001)). Qed.
Lemma lem1395003 (x : real) (y : real) (h1 : term206 x y) : True = (term4 x y).
Proof. exact (SYM (@lem1395002 x y h1)). Qed.
Lemma lem1395004 (x : real) (y : real) (h1 : term206 x y) : term4 x y.
Proof. exact (EQ_MP (@lem1395003 x y h1) (@lem0)). Qed.
Lemma lem1395005 (x : real) (y : real) (h1 : term206 x y) : (term5 x y) = True.
Proof. exact (@lem1394989 x y (@lem1395004 x y h1)). Qed.
Lemma lem1395006 (x : real) (y : real) : term209 x y.
Proof. exact (fun h0 : term206 x y => @lem1395005 x y h0). Qed.
Lemma lem1395007 (x : real) (y : real) : term210 x y.
Proof. exact (@lem1394965 x y True). Qed.
Lemma lem1395008 (x : real) (y : real) : (term147 x y) = (term211 x y).
Proof. exact (@lem1395007 x y (@lem1395006 x y)). Qed.
Lemma lem1395010 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1395011 (x : real) (y : real) : (term211 x y) = True.
Proof. exact (@lem1395010 (term206 x y)). Qed.
Lemma lem1395012 (x : real) (y : real) : (term147 x y) = True.
Proof. exact (TRANS (@lem1395008 x y) (@lem1395011 x y)). Qed.
Lemma lem1395013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1395014 (x : real) (y : real) : (term149 x y) = (and True).
Proof. exact (MK_COMB (@lem1395013) (@lem1395012 x y)). Qed.
Lemma lem1395018 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term21 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1395019 (p : Prop) (q : Prop) (p' : Prop) : term22 p q p'.
Proof. exact (fun q' : Prop => @lem1395018 p q p' q'). Qed.
Lemma lem1395020 (p : Prop) (q : Prop) : term23 p q.
Proof. exact (fun p' : Prop => @lem1395019 p q p'). Qed.
Lemma lem1395021 (x : real) (y : real) : term212 x y.
Proof. exact (@lem1395020 (term157 x y) (term160 x y)). Qed.
Lemma lem1395022 (x : real) (y : real) (p' : Prop) : term213 x y p'.
Proof. exact (@lem1395021 x y p'). Qed.
Lemma lem1395023 (x : real) (y : real) (p' : Prop) : (term213 x y p') = (term214 x y p').
Proof. exact (eq_refl (term213 x y p')). Qed.
Lemma lem1395024 (x : real) (y : real) (p' : Prop) : term214 x y p'.
Proof. exact (EQ_MP (@lem1395023 x y p') (@lem1395022 x y p')). Qed.
Lemma lem1395025 (x : real) (y : real) (p' : Prop) (q' : Prop) : term215 x y p' q'.
Proof. exact (@lem1395024 x y p' q'). Qed.
Lemma lem1395026 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term215 x y p' q') = (term216 x y p' q').
Proof. exact (eq_refl (term215 x y p' q')). Qed.
Lemma lem1395027 (x : real) (y : real) (p' : Prop) (q' : Prop) : term216 x y p' q'.
Proof. exact (EQ_MP (@lem1395026 x y p' q') (@lem1395025 x y p' q')). Qed.
Lemma lem1395031 (x : real) (y : real) : (real_lt x y) = (term9 x y).
Proof. exact (EQ_MP (@lem1393156 x y) (@lem1393155 x y)). Qed.
Lemma lem1395032 (x : real) : (term65 x) = (term193 x).
Proof. exact (@lem1395031 term18 x). Qed.
Lemma lem1395037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1395038 (x : real) : (term126 x) = (term205 x).
Proof. exact (MK_COMB (@lem1395037) (@lem1395032 x)). Qed.
Lemma lem1395044 (x : real) (y : real) : (real_lt x y) = (term9 x y).
Proof. exact (EQ_MP (@lem1393156 x y) (@lem1393155 x y)). Qed.
Lemma lem1395045 (y : real) : (term65 y) = (term193 y).
Proof. exact (@lem1395044 term18 y). Qed.
Lemma lem1395050 (x : real) (y : real) : (term157 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem1395038 x) (@lem1395045 y)). Qed.
Lemma lem1395061 (x : real) (y : real) (q' : Prop) : term218 x y q'.
Proof. exact (@lem1395027 x y (term217 x y) q'). Qed.
Lemma lem1395062 (x : real) (y : real) (q' : Prop) : term219 x y q'.
Proof. exact (@lem1395061 x y q' (@lem1395050 x y)). Qed.
Lemma lem1395063 (x : real) (y : real) (h1 : term217 x y) : term217 x y.
Proof. exact (h1). Qed.
Lemma lem1395064 (x : real) (y : real) (h1 : term217 x y) : term193 y.
Proof. exact (proj2 (@lem1395063 x y h1)). Qed.
Lemma lem1395079 (x : real) (y : real) (h1 : term217 x y) : term48 y.
Proof. exact (proj1 (@lem1395064 x y h1)). Qed.
Lemma lem1395080 (y : real) : (term48 y) = ((term48 y) = True).
Proof. exact (@lem7 (term48 y)). Qed.
Lemma lem1395082 (x : real) (y : real) (h1 : term217 x y) : term193 x.
Proof. exact (proj1 (@lem1395063 x y h1)). Qed.
Lemma lem1395097 (x : real) (y : real) (h1 : term217 x y) : term48 x.
Proof. exact (proj1 (@lem1395082 x y h1)). Qed.
Lemma lem1395098 (x : real) : (term48 x) = ((term48 x) = True).
Proof. exact (@lem7 (term48 x)). Qed.
Lemma lem1395101 (x : real) (y : real) : (real_lt x y) = (term9 x y).
Proof. exact (EQ_MP (@lem1393156 x y) (@lem1393155 x y)). Qed.
Lemma lem1395102 (x : real) (y : real) : (term160 x y) = (term220 x y).
Proof. exact (@lem1395101 term18 (real_mul x y)). Qed.
Lemma lem1395106 (x : real) (y : real) : term185 x y.
Proof. exact (fun h0 : term4 x y => @lem1393146 x y h0). Qed.
Lemma lem1395110 (x : real) (y : real) (h1 : term217 x y) : (term48 x) = True.
Proof. exact (EQ_MP (@lem1395098 x) (@lem1395097 x y h1)). Qed.
Lemma lem1395111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1395112 (x : real) (y : real) (h1 : term217 x y) : (term81 x) = (and True).
Proof. exact (MK_COMB (@lem1395111) (@lem1395110 x y h1)). Qed.
Lemma lem1395114 (x : real) (y : real) (h1 : term217 x y) : (term48 y) = True.
Proof. exact (EQ_MP (@lem1395080 y) (@lem1395079 x y h1)). Qed.
Lemma lem1395115 (x : real) (y : real) (h1 : term217 x y) : (term4 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1395112 x y h1) (@lem1395114 x y h1)). Qed.
Lemma lem1395117 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1395118 : (True /\ True) = True.
Proof. exact (@lem1395117 True). Qed.
Lemma lem1395119 (x : real) (y : real) (h1 : term217 x y) : (term4 x y) = True.
Proof. exact (TRANS (@lem1395115 x y h1) (@lem1395118)). Qed.
Lemma lem1395120 (x : real) (y : real) (h1 : term217 x y) : True = (term4 x y).
Proof. exact (SYM (@lem1395119 x y h1)). Qed.
Lemma lem1395121 (x : real) (y : real) (h1 : term217 x y) : term4 x y.
Proof. exact (EQ_MP (@lem1395120 x y h1) (@lem0)). Qed.
Lemma lem1395122 (x : real) (y : real) (h1 : term217 x y) : (term5 x y) = True.
Proof. exact (@lem1395106 x y (@lem1395121 x y h1)). Qed.
Lemma lem1395123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1395124 (x : real) (y : real) (h1 : term217 x y) : (term221 x y) = (and True).
Proof. exact (MK_COMB (@lem1395123) (@lem1395122 x y h1)). Qed.
Lemma lem1395127 (x : real) (y : real) : (term222 x y) = (term222 x y).
Proof. exact (eq_refl (term222 x y)). Qed.
Lemma lem1395128 (x : real) (y : real) (h1 : term217 x y) : (term220 x y) = (term223 x y).
Proof. exact (MK_COMB (@lem1395124 x y h1) (@lem1395127 x y)). Qed.
Lemma lem1395130 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1395131 (x : real) (y : real) : (term223 x y) = (term222 x y).
Proof. exact (@lem1395130 (term222 x y)). Qed.
Lemma lem1395134 (x : real) (y : real) (h1 : term217 x y) : (term220 x y) = (term222 x y).
Proof. exact (TRANS (@lem1395128 x y h1) (@lem1395131 x y)). Qed.
Lemma lem1395135 (x : real) (y : real) (h1 : term217 x y) : (term160 x y) = (term222 x y).
Proof. exact (TRANS (@lem1395102 x y) (@lem1395134 x y h1)). Qed.
Lemma lem1395136 (x : real) (y : real) : term224 x y.
Proof. exact (fun h0 : term217 x y => @lem1395135 x y h0). Qed.
Lemma lem1395137 (x : real) (y : real) : term225 x y.
Proof. exact (@lem1395062 x y (term222 x y)). Qed.
Lemma lem1395138 (x : real) (y : real) : (term164 x y) = (term226 x y).
Proof. exact (@lem1395137 x y (@lem1395136 x y)). Qed.
Lemma lem1395220 (x : real) (y : real) : (term166 x y) = (term227 x y).
Proof. exact (MK_COMB (@lem1395014 x y) (@lem1395138 x y)). Qed.
Lemma lem1395222 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1395223 (x : real) (y : real) : (term227 x y) = (term226 x y).
Proof. exact (@lem1395222 (term226 x y)). Qed.
Lemma lem1395305 (x : real) (y : real) : (term166 x y) = (term226 x y).
Proof. exact (TRANS (@lem1395220 x y) (@lem1395223 x y)). Qed.
Lemma lem1395306 (x : real) (y : real) : (term170 x y) = (term227 x y).
Proof. exact (MK_COMB (@lem1394925 x y) (@lem1395305 x y)). Qed.
Lemma lem1395308 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1395309 (x : real) (y : real) : (term227 x y) = (term226 x y).
Proof. exact (@lem1395308 (term226 x y)). Qed.
Lemma lem1395391 (x : real) (y : real) : (term170 x y) = (term226 x y).
Proof. exact (TRANS (@lem1395306 x y) (@lem1395309 x y)). Qed.
Lemma lem1395392 (x : real) (y : real) : (term172 x y) = (term227 x y).
Proof. exact (MK_COMB (@lem1394842 x y) (@lem1395391 x y)). Qed.
Lemma lem1395394 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1395395 (x : real) (y : real) : (term227 x y) = (term226 x y).
Proof. exact (@lem1395394 (term226 x y)). Qed.
Lemma lem1395477 (x : real) (y : real) : (term172 x y) = (term226 x y).
Proof. exact (TRANS (@lem1395392 x y) (@lem1395395 x y)). Qed.
Lemma lem1395478 (x : real) (y : real) : (term226 x y) = (term172 x y).
Proof. exact (SYM (@lem1395477 x y)). Qed.
Lemma lem1395480 (p : Prop) : p = (term228 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1395481 (x : real) (y : real) : (term226 x y) = (term229 x y).
Proof. exact (@lem1395480 (term226 x y)). Qed.
Lemma lem1395482 (x : real) (y : real) : (term229 x y) = (term226 x y).
Proof. exact (SYM (@lem1395481 x y)). Qed.
Lemma lem1395483 (x : real) (y : real) (h1 : term230 x y) : term230 x y.
Proof. exact (h1). Qed.
Lemma lem1395486 (x : real) (y : real) (h1 : term231 x y) : term231 x y.
Proof. exact (h1). Qed.
Lemma lem1395487 (x : real) (y : real) : term232 x y.
Proof. exact (fun h0 : term231 x y => @lem1395486 x y h0). Qed.
Lemma lem1395488 (x : real) (y : real) (h1 : term232 x y) : term232 x y.
Proof. exact (h1). Qed.
Lemma lem1395489 (x : real) (y : real) (h1 : term231 x y) : term231 x y.
Proof. exact (h1). Qed.
Lemma lem1395490 (x : real) (y : real) (h1 : term231 x y) (h2 : term232 x y) : term231 x y.
Proof. exact (@lem1395488 x y h2 (@lem1395489 x y h1)). Qed.
Lemma lem1395491 (x : real) (y : real) (h1 : term231 x y) : term233 x y.
Proof. exact (fun h0 : term232 x y => @lem1395490 x y h1 h0). Qed.
Lemma lem1395492 (x : real) (y : real) (h1 : term232 x y) : term232 x y.
Proof. exact (h1). Qed.
Lemma lem1395493 (x : real) (y : real) (h1 : term231 x y) (h2 : term232 x y) : term231 x y.
Proof. exact (@lem1395491 x y h1 (@lem1395492 x y h2)). Qed.
Lemma lem1395494 (x : real) (y : real) (h1 : term232 x y) : term232 x y.
Proof. exact (fun h0 : term231 x y => @lem1395493 x y h0 h1). Qed.
Lemma lem1395495 (x : real) (y : real) : term234 x y.
Proof. exact (fun h0 : term232 x y => @lem1395494 x y h0). Qed.
Lemma lem1395498 (x : real) (y : real) : term232 x y.
Proof. exact (@lem1395495 x y (@lem1395487 x y)). Qed.
Lemma lem1395518 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1395519 : term235 = term236.
Proof. exact (@lem1395518 term237). Qed.
Lemma lem1395530 (x : real) (y : real) : (term238 x y) = (term238 x y).
Proof. exact (eq_refl (term238 x y)). Qed.
Lemma lem1395531 (x : real) (y : real) : (term231 x y) = (term239 x y).
Proof. exact (MK_COMB (@lem1395530 x y) (@lem1395519)). Qed.
Lemma lem1395534 (y : real) : (term240 y) = (term241 y).
Proof. exact (fun_ext (fun x : real => @lem1395531 x y)). Qed.
Lemma lem1395535 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395536 (y : real) : (term242 y) = (term243 y).
Proof. exact (MK_COMB (@lem1395535) (@lem1395534 y)). Qed.
Lemma lem1395541 : term244 = term245.
Proof. exact (fun_ext (fun y : real => @lem1395536 y)). Qed.
Lemma lem1395542 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395551 : term246 = term247.
Proof. exact (MK_COMB (@lem1395542) (@lem1395541)). Qed.
Lemma lem1395560 (x : real) (y : real) : (((real_mul x y) = term18) = (term248 x y)) = (((real_mul x y) = term18) = (term248 x y)).
Proof. exact (eq_refl (((real_mul x y) = term18) = (term248 x y))). Qed.
Lemma lem1395561 (x : real) : (term249 x) = (term249 x).
Proof. exact (fun_ext (fun y : real => @lem1395560 x y)). Qed.
Lemma lem1395562 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395563 (x : real) : (term250 x) = (term250 x).
Proof. exact (MK_COMB (@lem1395562) (@lem1395561 x)). Qed.
Lemma lem1395564 : term251 = term251.
Proof. exact (fun_ext (fun x : real => @lem1395563 x)). Qed.
Lemma lem1395565 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395566 : term237 = term237.
Proof. exact (MK_COMB (@lem1395565) (@lem1395564)). Qed.
Lemma lem1395567 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1395568 : term236 = term236.
Proof. exact (MK_COMB (@lem1395567) (@lem1395566)). Qed.
Lemma lem1395595 (x : real) (y : real) : (term238 x y) = (term238 x y).
Proof. exact (eq_refl (term238 x y)). Qed.
Lemma lem1395596 (x : real) (y : real) : (term239 x y) = (term239 x y).
Proof. exact (MK_COMB (@lem1395595 x y) (@lem1395568)). Qed.
Lemma lem1395597 (y : real) : (term241 y) = (term241 y).
Proof. exact (fun_ext (fun x : real => @lem1395596 x y)). Qed.
Lemma lem1395598 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395599 (y : real) : (term243 y) = (term243 y).
Proof. exact (MK_COMB (@lem1395598) (@lem1395597 y)). Qed.
Lemma lem1395600 : term245 = term245.
Proof. exact (fun_ext (fun y : real => @lem1395599 y)). Qed.
Lemma lem1395601 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395602 : term247 = term247.
Proof. exact (MK_COMB (@lem1395601) (@lem1395600)). Qed.
Lemma lem1395641 : term246 = term247.
Proof. exact (TRANS (@lem1395551) (@lem1395602)). Qed.
Lemma lem1395642 : term247 = term246.
Proof. exact (SYM (@lem1395641)). Qed.
Lemma lem1395643 (x : real) (y : real) (h1 : term230 x y) : term230 x y.
Proof. exact (h1). Qed.
Lemma lem1395644 (h1 : term237) : term237.
Proof. exact (h1). Qed.
Lemma lem1395660 (x : real) (y : real) : (term252 x y) = (term18 = (real_mul x y)).
Proof. exact (@lem16933 (term18 = (real_mul x y))). Qed.
Lemma lem1395662 (x : real) (y : real) : (term253 x y) = (term253 x y).
Proof. exact (eq_refl (term253 x y)). Qed.
Lemma lem1395663 (x : real) (y : real) : (term254 x y) = (term255 x y).
Proof. exact (MK_COMB (@lem1395662 x y) (@lem1395660 x y)). Qed.
Lemma lem1395664 (x : real) (y : real) : (term230 x y) = (term254 x y).
Proof. exact (@lem17362 (term217 x y) (term222 x y)). Qed.
Lemma lem1395669 (x : real) (y : real) : (term230 x y) = (term255 x y).
Proof. exact (TRANS (@lem1395664 x y) (@lem1395663 x y)). Qed.
Lemma lem1395681 (x : real) (y : real) : (term256 x y) = (term257 x y).
Proof. exact (@lem17160 (x = term18) (y = term18)). Qed.
Lemma lem1395687 (x : real) (y : real) : (term258 x y) = (term258 x y).
Proof. exact (eq_refl (term258 x y)). Qed.
Lemma lem1395689 (x : real) (y : real) : (term259 x y) = (term259 x y).
Proof. exact (eq_refl (term259 x y)). Qed.
Lemma lem1395690 (x : real) (y : real) : (term260 x y) = (term261 x y).
Proof. exact (MK_COMB (@lem1395689 x y) (@lem1395681 x y)). Qed.
Lemma lem1395691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1395692 (x : real) (y : real) : (term262 x y) = (term263 x y).
Proof. exact (MK_COMB (@lem1395691) (@lem1395690 x y)). Qed.
Lemma lem1395693 (x : real) (y : real) : (term264 x y) = (term265 x y).
Proof. exact (MK_COMB (@lem1395692 x y) (@lem1395687 x y)). Qed.
Lemma lem1395694 (x : real) (y : real) : (((real_mul x y) = term18) = (term248 x y)) = (term264 x y).
Proof. exact (@lem17784 ((real_mul x y) = term18) (term248 x y)). Qed.
Lemma lem1395695 (x : real) (y : real) : (((real_mul x y) = term18) = (term248 x y)) = (term265 x y).
Proof. exact (TRANS (@lem1395694 x y) (@lem1395693 x y)). Qed.
Lemma lem1395696 (x : real) : (term249 x) = (term266 x).
Proof. exact (fun_ext (fun y : real => @lem1395695 x y)). Qed.
Lemma lem1395697 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395698 (x : real) : (term250 x) = (term267 x).
Proof. exact (MK_COMB (@lem1395697) (@lem1395696 x)). Qed.
Lemma lem1395699 : term251 = term268.
Proof. exact (fun_ext (fun x : real => @lem1395698 x)). Qed.
Lemma lem1395700 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395701 : term237 = term269.
Proof. exact (MK_COMB (@lem1395700) (@lem1395699)). Qed.
Lemma lem1395707 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1395708 (P : real -> Prop) (Q : real -> Prop) : (term272 P Q) = (term273 P Q).
Proof. exact (@lem1395707 real P Q). Qed.
Lemma lem1395709 (x : real) : (term274 x) = (term275 x).
Proof. exact (@lem1395708 (term276 x) (term277 x)). Qed.
Lemma lem1395710 (x : real) (y : real) : (term278 x y) = (term261 x y).
Proof. exact (eq_refl (term278 x y)). Qed.
Lemma lem1395711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1395712 (x : real) (y : real) : (term279 x y) = (term263 x y).
Proof. exact (MK_COMB (@lem1395711) (@lem1395710 x y)). Qed.
Lemma lem1395713 (x : real) (y : real) : (term280 x y) = (term258 x y).
Proof. exact (eq_refl (term280 x y)). Qed.
Lemma lem1395714 (x : real) (y : real) : (term281 x y) = (term265 x y).
Proof. exact (MK_COMB (@lem1395712 x y) (@lem1395713 x y)). Qed.
Lemma lem1395715 (x : real) : (term282 x) = (term266 x).
Proof. exact (fun_ext (fun y : real => @lem1395714 x y)). Qed.
Lemma lem1395716 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395717 (x : real) : (term274 x) = (term267 x).
Proof. exact (MK_COMB (@lem1395716) (@lem1395715 x)). Qed.
Lemma lem1395718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1395719 (x : real) : (term283 x) = (term284 x).
Proof. exact (MK_COMB (@lem1395718) (@lem1395717 x)). Qed.
Lemma lem1395720 (x : real) (y : real) : (term278 x y) = (term261 x y).
Proof. exact (eq_refl (term278 x y)). Qed.
Lemma lem1395721 (x : real) : (term285 x) = (term276 x).
Proof. exact (fun_ext (fun y : real => @lem1395720 x y)). Qed.
Lemma lem1395722 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395723 (x : real) : (term286 x) = (term287 x).
Proof. exact (MK_COMB (@lem1395722) (@lem1395721 x)). Qed.
Lemma lem1395724 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1395725 (x : real) : (term288 x) = (term289 x).
Proof. exact (MK_COMB (@lem1395724) (@lem1395723 x)). Qed.
Lemma lem1395726 (x : real) (y : real) : (term280 x y) = (term258 x y).
Proof. exact (eq_refl (term280 x y)). Qed.
Lemma lem1395727 (x : real) : (term290 x) = (term277 x).
Proof. exact (fun_ext (fun y : real => @lem1395726 x y)). Qed.
Lemma lem1395728 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395729 (x : real) : (term291 x) = (term292 x).
Proof. exact (MK_COMB (@lem1395728) (@lem1395727 x)). Qed.
Lemma lem1395730 (x : real) : (term275 x) = (term293 x).
Proof. exact (MK_COMB (@lem1395725 x) (@lem1395729 x)). Qed.
Lemma lem1395731 (x : real) : ((term274 x) = (term275 x)) = ((term267 x) = (term293 x)).
Proof. exact (MK_COMB (@lem1395719 x) (@lem1395730 x)). Qed.
Lemma lem1395732 (x : real) : (term267 x) = (term293 x).
Proof. exact (EQ_MP (@lem1395731 x) (@lem1395709 x)). Qed.
Lemma lem1395829 : term268 = term294.
Proof. exact (fun_ext (fun x : real => @lem1395732 x)). Qed.
Lemma lem1395830 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395831 : term269 = term295.
Proof. exact (MK_COMB (@lem1395830) (@lem1395829)). Qed.
Lemma lem1395833 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1395834 (P : real -> Prop) (Q : real -> Prop) : (term272 P Q) = (term273 P Q).
Proof. exact (@lem1395833 real P Q). Qed.
Lemma lem1395835 : term296 = term297.
Proof. exact (@lem1395834 term298 term299). Qed.
Lemma lem1395836 (x : real) : (term300 x) = (term287 x).
Proof. exact (eq_refl (term300 x)). Qed.
Lemma lem1395837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1395838 (x : real) : (term301 x) = (term289 x).
Proof. exact (MK_COMB (@lem1395837) (@lem1395836 x)). Qed.
Lemma lem1395839 (x : real) : (term302 x) = (term292 x).
Proof. exact (eq_refl (term302 x)). Qed.
Lemma lem1395840 (x : real) : (term303 x) = (term293 x).
Proof. exact (MK_COMB (@lem1395838 x) (@lem1395839 x)). Qed.
Lemma lem1395841 : term304 = term294.
Proof. exact (fun_ext (fun x : real => @lem1395840 x)). Qed.
Lemma lem1395842 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395843 : term296 = term295.
Proof. exact (MK_COMB (@lem1395842) (@lem1395841)). Qed.
Lemma lem1395844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1395845 : term305 = term306.
Proof. exact (MK_COMB (@lem1395844) (@lem1395843)). Qed.
Lemma lem1395846 (x : real) : (term300 x) = (term287 x).
Proof. exact (eq_refl (term300 x)). Qed.
Lemma lem1395847 : term307 = term298.
Proof. exact (fun_ext (fun x : real => @lem1395846 x)). Qed.
Lemma lem1395848 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395849 : term308 = term309.
Proof. exact (MK_COMB (@lem1395848) (@lem1395847)). Qed.
Lemma lem1395850 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1395851 : term310 = term311.
Proof. exact (MK_COMB (@lem1395850) (@lem1395849)). Qed.
Lemma lem1395852 (x : real) : (term302 x) = (term292 x).
Proof. exact (eq_refl (term302 x)). Qed.
Lemma lem1395853 : term312 = term299.
Proof. exact (fun_ext (fun x : real => @lem1395852 x)). Qed.
Lemma lem1395854 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1395855 : term313 = term314.
Proof. exact (MK_COMB (@lem1395854) (@lem1395853)). Qed.
Lemma lem1395856 : term297 = term315.
Proof. exact (MK_COMB (@lem1395851) (@lem1395855)). Qed.
Lemma lem1395857 : (term296 = term297) = (term295 = term315).
Proof. exact (MK_COMB (@lem1395845) (@lem1395856)). Qed.
Lemma lem1395858 : term295 = term315.
Proof. exact (EQ_MP (@lem1395857) (@lem1395835)). Qed.
Lemma lem1395965 : term269 = term315.
Proof. exact (TRANS (@lem1395831) (@lem1395858)). Qed.
Lemma lem1395966 : term237 = term315.
Proof. exact (TRANS (@lem1395701) (@lem1395965)). Qed.
Lemma lem1395967 (h1 : term237) : term315.
Proof. exact (EQ_MP (@lem1395966) (@lem1395644 h1)). Qed.
Lemma lem1396033 (x : real) (y : real) (h1 : term230 x y) : term255 x y.
Proof. exact (EQ_MP (@lem1395669 x y) (@lem1395643 x y h1)). Qed.
Lemma lem1396072 (x : real) (y : real) : (term258 x y) = (term258 x y).
Proof. exact (eq_refl (term258 x y)). Qed.
Lemma lem1396073 (x : real) : (term277 x) = (term277 x).
Proof. exact (fun_ext (fun y : real => @lem1396072 x y)). Qed.
Lemma lem1396074 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1396075 (x : real) : (term292 x) = (term292 x).
Proof. exact (MK_COMB (@lem1396074) (@lem1396073 x)). Qed.
Lemma lem1396076 : term299 = term299.
Proof. exact (fun_ext (fun x : real => @lem1396075 x)). Qed.
Lemma lem1396077 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1396078 : term314 = term314.
Proof. exact (MK_COMB (@lem1396077) (@lem1396076)). Qed.
Lemma lem1396119 (x : real) (y : real) : (term261 x y) = (term261 x y).
Proof. exact (eq_refl (term261 x y)). Qed.
Lemma lem1396120 (x : real) : (term276 x) = (term276 x).
Proof. exact (fun_ext (fun y : real => @lem1396119 x y)). Qed.
Lemma lem1396121 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1396122 (x : real) : (term287 x) = (term287 x).
Proof. exact (MK_COMB (@lem1396121) (@lem1396120 x)). Qed.
Lemma lem1396123 : term298 = term298.
Proof. exact (fun_ext (fun x : real => @lem1396122 x)). Qed.
Lemma lem1396124 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1396125 : term309 = term309.
Proof. exact (MK_COMB (@lem1396124) (@lem1396123)). Qed.
Lemma lem1396126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1396127 : term311 = term311.
Proof. exact (MK_COMB (@lem1396126) (@lem1396125)). Qed.
Lemma lem1396128 : term315 = term315.
Proof. exact (MK_COMB (@lem1396127) (@lem1396078)). Qed.
Lemma lem1396129 (h1 : term237) : term315.
Proof. exact (EQ_MP (@lem1396128) (@lem1395967 h1)). Qed.
Lemma lem1396130 (h1 : term237) : term314.
Proof. exact (proj2 (@lem1396129 h1)). Qed.
Lemma lem1396133 (x : real) (y : real) (h1 : term230 x y) : term217 x y.
Proof. exact (proj1 (@lem1396033 x y h1)). Qed.
Lemma lem1396134 (x : real) (y : real) (h1 : term230 x y) : term193 y.
Proof. exact (proj2 (@lem1396133 x y h1)). Qed.
Lemma lem1396135 (x : real) (y : real) (h1 : term230 x y) : term193 x.
Proof. exact (proj1 (@lem1396133 x y h1)). Qed.
Lemma lem1396179 (x : real) (y : real) : (term258 x y) = (term258 x y).
Proof. exact (eq_refl (term258 x y)). Qed.
Lemma lem1396180 (x : real) : (term277 x) = (term277 x).
Proof. exact (fun_ext (fun y : real => @lem1396179 x y)). Qed.
Lemma lem1396181 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1396182 (x : real) : (term292 x) = (term292 x).
Proof. exact (MK_COMB (@lem1396181) (@lem1396180 x)). Qed.
Lemma lem1396183 : term299 = term299.
Proof. exact (fun_ext (fun x : real => @lem1396182 x)). Qed.
Lemma lem1396184 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1396186 : term314 = term314.
Proof. exact (MK_COMB (@lem1396184) (@lem1396183)). Qed.
Lemma lem1396187 (h1 : term237) : term314.
Proof. exact (EQ_MP (@lem1396186) (@lem1396130 h1)). Qed.
Lemma lem1396214 (_24776 : real) (h1 : term237) : term302 _24776.
Proof. exact (@lem1396187 h1 _24776). Qed.
Lemma lem1396215 (_24776 : real) : (term302 _24776) = (term292 _24776).
Proof. exact (eq_refl (term302 _24776)). Qed.
Lemma lem1396216 (_24776 : real) (h1 : term237) : term292 _24776.
Proof. exact (EQ_MP (@lem1396215 _24776) (@lem1396214 _24776 h1)). Qed.
Lemma lem1396217 (_24776 : real) (_24777 : real) (h1 : term237) : term280 _24776 _24777.
Proof. exact (@lem1396216 _24776 h1 _24777). Qed.
Lemma lem1396218 (_24776 : real) (_24777 : real) : (term280 _24776 _24777) = (term258 _24776 _24777).
Proof. exact (eq_refl (term280 _24776 _24777)). Qed.
Lemma lem1396231 (_24776 : real) (_24777 : real) (h1 : term237) : term258 _24776 _24777.
Proof. exact (EQ_MP (@lem1396218 _24776 _24777) (@lem1396217 _24776 _24777 h1)). Qed.
Lemma lem1396241 (x : real) (y : real) (h1 : term230 x y) : term316 x.
Proof. exact (proj2 (@lem1396135 x y h1)). Qed.
Lemma lem1396305 (x : real) (y : real) (z : real) : term317 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1396309 (x : real) (y : real) (h1 : term230 x y) : term18 = (real_mul x y).
Proof. exact (proj2 (@lem1396033 x y h1)). Qed.
Lemma lem1396310 (x : real) (y : real) (h1 : term230 x y) : term318 x y.
Proof. exact (fun h0 : term222 x y => @lem1396309 x y h1). Qed.
Lemma lem1396312 (p : Prop) : (term319 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1396313 (x : real) (y : real) : (term318 x y) = (term18 = (real_mul x y)).
Proof. exact (@lem1396312 (term18 = (real_mul x y))). Qed.
Lemma lem1396314 (x : real) (y : real) (h1 : term230 x y) : term18 = (real_mul x y).
Proof. exact (EQ_MP (@lem1396313 x y) (@lem1396310 x y h1)). Qed.
Lemma lem1396316 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1396317 : term18 = term18.
Proof. exact (@lem1396316 term18). Qed.
Lemma lem1396318 : term320.
Proof. exact (fun h0 : term321 => @lem1396317). Qed.
Lemma lem1396320 (p : Prop) : (term319 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1396321 : term320 = (term18 = term18).
Proof. exact (@lem1396320 (term18 = term18)). Qed.
Lemma lem1396322 : term18 = term18.
Proof. exact (EQ_MP (@lem1396321) (@lem1396318)). Qed.
Lemma lem1396340 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1396341 (y : real) (x : real) (z : real) : (term322 x y z) = (term323 y x z).
Proof. exact (@lem1396340 (y = z) (term324 x z)). Qed.
Lemma lem1396351 (x : real) (y : real) : (term325 x y) = (term325 x y).
Proof. exact (eq_refl (term325 x y)). Qed.
Lemma lem1396352 (y : real) (x : real) (z : real) : (term317 x y z) = (term326 y x z).
Proof. exact (MK_COMB (@lem1396351 x y) (@lem1396341 y x z)). Qed.
Lemma lem1396356 (q : Prop) (p : Prop) (r : Prop) : (term327 p q r) = (term327 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1396357 (y : real) (x : real) (z : real) : (term326 y x z) = (term328 y x z).
Proof. exact (@lem1396356 (y = z) (term324 x y) (term324 x z)). Qed.
Lemma lem1396379 (y : real) (x : real) (z : real) : (term317 x y z) = (term328 y x z).
Proof. exact (TRANS (@lem1396352 y x z) (@lem1396357 y x z)). Qed.
Lemma lem1396380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1396381 (y : real) (x : real) (z : real) : (term329 x y z) = (term330 y x z).
Proof. exact (MK_COMB (@lem1396380) (@lem1396379 y x z)). Qed.
Lemma lem1396403 (y : real) (x : real) (z : real) : (term328 y x z) = (term328 y x z).
Proof. exact (eq_refl (term328 y x z)). Qed.
Lemma lem1396404 (y : real) (x : real) (z : real) : ((term317 x y z) = (term328 y x z)) = ((term328 y x z) = (term328 y x z)).
Proof. exact (MK_COMB (@lem1396381 y x z) (@lem1396403 y x z)). Qed.
Lemma lem1396406 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1396407 (x : Prop) : (x = x) = True.
Proof. exact (@lem1396406 Prop x). Qed.
Lemma lem1396408 (y : real) (x : real) (z : real) : ((term328 y x z) = (term328 y x z)) = True.
Proof. exact (@lem1396407 (term328 y x z)). Qed.
Lemma lem1396409 (y : real) (x : real) (z : real) : ((term317 x y z) = (term328 y x z)) = True.
Proof. exact (TRANS (@lem1396404 y x z) (@lem1396408 y x z)). Qed.
Lemma lem1396410 (y : real) (x : real) (z : real) : True = ((term317 x y z) = (term328 y x z)).
Proof. exact (SYM (@lem1396409 y x z)). Qed.
Lemma lem1396411 (y : real) (x : real) (z : real) : (term317 x y z) = (term328 y x z).
Proof. exact (EQ_MP (@lem1396410 y x z) (@lem0)). Qed.
Lemma lem1396412 (y : real) (x : real) (z : real) : term328 y x z.
Proof. exact (EQ_MP (@lem1396411 y x z) (@lem1396305 x y z)). Qed.
Lemma lem1396414 (b : Prop) (a : Prop) : (a \/ b) = (term331 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1396415 (x : real) (y : real) (z : real) : (term328 y x z) = (term332 x y z).
Proof. exact (@lem1396414 (term333 y x z) (y = z)). Qed.
Lemma lem1396417 (a : Prop) (b : Prop) : (term334 a b) = (term335 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1396418 (y : real) (x : real) (z : real) : (term336 y x z) = (term337 y x z).
Proof. exact (@lem1396417 (term324 x y) (term324 x z)). Qed.
Lemma lem1396420 (a : Prop) : (term338 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1396421 (x : real) (y : real) : (term339 x y) = (x = y).
Proof. exact (@lem1396420 (x = y)). Qed.
Lemma lem1396422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1396423 (x : real) (y : real) : (term340 x y) = (term341 x y).
Proof. exact (MK_COMB (@lem1396422) (@lem1396421 x y)). Qed.
Lemma lem1396425 (a : Prop) : (term338 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1396426 (x : real) (z : real) : (term339 x z) = (x = z).
Proof. exact (@lem1396425 (x = z)). Qed.
Lemma lem1396427 (y : real) (x : real) (z : real) : (term337 y x z) = (term342 y x z).
Proof. exact (MK_COMB (@lem1396423 x y) (@lem1396426 x z)). Qed.
Lemma lem1396428 (y : real) (x : real) (z : real) : (term336 y x z) = (term342 y x z).
Proof. exact (TRANS (@lem1396418 y x z) (@lem1396427 y x z)). Qed.
Lemma lem1396429 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1396430 (y : real) (x : real) (z : real) : (term343 y x z) = (term344 y x z).
Proof. exact (MK_COMB (@lem1396429) (@lem1396428 y x z)). Qed.
Lemma lem1396431 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1396432 (x : real) (y : real) (z : real) : (term332 x y z) = (term345 x y z).
Proof. exact (MK_COMB (@lem1396430 y x z) (@lem1396431 y z)). Qed.
Lemma lem1396433 (x : real) (y : real) (z : real) : (term328 y x z) = (term345 x y z).
Proof. exact (TRANS (@lem1396415 x y z) (@lem1396432 x y z)). Qed.
Lemma lem1396435 (x : real) (y : real) (h1 : term230 x y) : term346 x y.
Proof. exact (conj (@lem1396314 x y h1) (@lem1396322)). Qed.
Lemma lem1396437 (x : real) (y : real) (z : real) : term345 x y z.
Proof. exact (EQ_MP (@lem1396433 x y z) (@lem1396412 y x z)). Qed.
Lemma lem1396438 (x : real) (y : real) : term347 x y.
Proof. exact (@lem1396437 term18 (real_mul x y) term18). Qed.
Lemma lem1396441 (x : real) (y : real) (h1 : term230 x y) : (real_mul x y) = term18.
Proof. exact (@lem1396438 x y (@lem1396435 x y h1)). Qed.
Lemma lem1396442 (x : real) (y : real) (h1 : term230 x y) : term348 x y.
Proof. exact (fun h0 : term349 x y => @lem1396441 x y h1). Qed.
Lemma lem1396444 (p : Prop) : (term319 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1396445 (x : real) (y : real) : (term348 x y) = ((real_mul x y) = term18).
Proof. exact (@lem1396444 ((real_mul x y) = term18)). Qed.
Lemma lem1396446 (x : real) (y : real) (h1 : term230 x y) : (real_mul x y) = term18.
Proof. exact (EQ_MP (@lem1396445 x y) (@lem1396442 x y h1)). Qed.
Lemma lem1396448 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1396449 (y : real) : y = y.
Proof. exact (@lem1396448 y). Qed.
Lemma lem1396450 (y : real) : term350 y.
Proof. exact (fun h0 : term351 y => @lem1396449 y). Qed.
Lemma lem1396452 (p : Prop) : (term319 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1396453 (y : real) : (term350 y) = (y = y).
Proof. exact (@lem1396452 (y = y)). Qed.
Lemma lem1396454 (y : real) : y = y.
Proof. exact (EQ_MP (@lem1396453 y) (@lem1396450 y)). Qed.
Lemma lem1396456 (x : real) (y : real) (h1 : term230 x y) : term316 y.
Proof. exact (proj2 (@lem1396134 x y h1)). Qed.
Lemma lem1396457 (x : real) (y : real) (h1 : term230 x y) : term352 y.
Proof. exact (fun h0 : term18 = y => @lem1396456 x y h1). Qed.
Lemma lem1396459 (p : Prop) : (term353 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1396460 (y : real) : (term352 y) = (term316 y).
Proof. exact (@lem1396459 (term18 = y)). Qed.
Lemma lem1396461 (x : real) (y : real) (h1 : term230 x y) : term316 y.
Proof. exact (EQ_MP (@lem1396460 y) (@lem1396457 x y h1)). Qed.
Lemma lem1396463 (b : Prop) (a : Prop) : (a \/ b) = (term331 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1396464 (z : real) (x : real) (y : real) : (term317 x y z) = (term354 z x y).
Proof. exact (@lem1396463 (term322 x y z) (term324 x y)). Qed.
Lemma lem1396466 (a : Prop) (b : Prop) : (term334 a b) = (term335 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1396467 (x : real) (y : real) (z : real) : (term355 x y z) = (term356 x y z).
Proof. exact (@lem1396466 (term324 x z) (y = z)). Qed.
Lemma lem1396469 (a : Prop) : (term338 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1396470 (x : real) (z : real) : (term339 x z) = (x = z).
Proof. exact (@lem1396469 (x = z)). Qed.
Lemma lem1396471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1396472 (x : real) (z : real) : (term340 x z) = (term341 x z).
Proof. exact (MK_COMB (@lem1396471) (@lem1396470 x z)). Qed.
Lemma lem1396473 (y : real) (z : real) : (term324 y z) = (term324 y z).
Proof. exact (eq_refl (term324 y z)). Qed.
Lemma lem1396474 (x : real) (y : real) (z : real) : (term356 x y z) = (term357 x y z).
Proof. exact (MK_COMB (@lem1396472 x z) (@lem1396473 y z)). Qed.
Lemma lem1396475 (x : real) (y : real) (z : real) : (term355 x y z) = (term357 x y z).
Proof. exact (TRANS (@lem1396467 x y z) (@lem1396474 x y z)). Qed.
Lemma lem1396476 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1396477 (x : real) (y : real) (z : real) : (term358 x y z) = (term359 x y z).
Proof. exact (MK_COMB (@lem1396476) (@lem1396475 x y z)). Qed.
Lemma lem1396478 (x : real) (y : real) : (term324 x y) = (term324 x y).
Proof. exact (eq_refl (term324 x y)). Qed.
Lemma lem1396479 (z : real) (x : real) (y : real) : (term354 z x y) = (term360 z x y).
Proof. exact (MK_COMB (@lem1396477 x y z) (@lem1396478 x y)). Qed.
Lemma lem1396480 (z : real) (x : real) (y : real) : (term317 x y z) = (term360 z x y).
Proof. exact (TRANS (@lem1396464 z x y) (@lem1396479 z x y)). Qed.
Lemma lem1396482 (x : real) (y : real) (h1 : term230 x y) : term361 y.
Proof. exact (conj (@lem1396454 y) (@lem1396461 x y h1)). Qed.
Lemma lem1396484 (z : real) (x : real) (y : real) : term360 z x y.
Proof. exact (EQ_MP (@lem1396480 z x y) (@lem1396305 x y z)). Qed.
Lemma lem1396485 (y : real) : term362 y.
Proof. exact (@lem1396484 y y term18). Qed.
Lemma lem1396488 (x : real) (y : real) (h1 : term230 x y) : term363 y.
Proof. exact (@lem1396485 y (@lem1396482 x y h1)). Qed.
Lemma lem1396489 (x : real) (y : real) (h1 : term230 x y) : term364 y.
Proof. exact (fun h0 : y = term18 => @lem1396488 x y h1). Qed.
Lemma lem1396491 (p : Prop) : (term353 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1396492 (y : real) : (term364 y) = (term363 y).
Proof. exact (@lem1396491 (y = term18)). Qed.
Lemma lem1396493 (x : real) (y : real) (h1 : term230 x y) : term363 y.
Proof. exact (EQ_MP (@lem1396492 y) (@lem1396489 x y h1)). Qed.
Lemma lem1396499 (q : Prop) (p : Prop) (r : Prop) : (term327 p q r) = (term327 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1396500 (_24776 : real) (_24777 : real) : (term258 _24776 _24777) = (term365 _24776 _24777).
Proof. exact (@lem1396499 (_24776 = term18) (term349 _24776 _24777) (_24777 = term18)). Qed.
Lemma lem1396516 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1396517 (_24776 : real) (_24777 : real) : (term366 _24776 _24777) = (term367 _24776 _24777).
Proof. exact (@lem1396516 (_24777 = term18) (term349 _24776 _24777)). Qed.
Lemma lem1396527 (_24776 : real) : (term368 _24776) = (term368 _24776).
Proof. exact (eq_refl (term368 _24776)). Qed.
Lemma lem1396528 (_24776 : real) (_24777 : real) : (term365 _24776 _24777) = (term369 _24776 _24777).
Proof. exact (MK_COMB (@lem1396527 _24776) (@lem1396517 _24776 _24777)). Qed.
Lemma lem1396539 (_24776 : real) (_24777 : real) : (term258 _24776 _24777) = (term369 _24776 _24777).
Proof. exact (TRANS (@lem1396500 _24776 _24777) (@lem1396528 _24776 _24777)). Qed.
Lemma lem1396540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1396541 (_24776 : real) (_24777 : real) : (term370 _24776 _24777) = (term371 _24776 _24777).
Proof. exact (MK_COMB (@lem1396540) (@lem1396539 _24776 _24777)). Qed.
Lemma lem1396557 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1396558 (_24776 : real) (_24777 : real) : (term366 _24776 _24777) = (term367 _24776 _24777).
Proof. exact (@lem1396557 (_24777 = term18) (term349 _24776 _24777)). Qed.
Lemma lem1396568 (_24776 : real) : (term368 _24776) = (term368 _24776).
Proof. exact (eq_refl (term368 _24776)). Qed.
Lemma lem1396569 (_24776 : real) (_24777 : real) : (term365 _24776 _24777) = (term369 _24776 _24777).
Proof. exact (MK_COMB (@lem1396568 _24776) (@lem1396558 _24776 _24777)). Qed.
Lemma lem1396580 (_24776 : real) (_24777 : real) : ((term258 _24776 _24777) = (term365 _24776 _24777)) = ((term369 _24776 _24777) = (term369 _24776 _24777)).
Proof. exact (MK_COMB (@lem1396541 _24776 _24777) (@lem1396569 _24776 _24777)). Qed.
Lemma lem1396582 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1396583 (x : Prop) : (x = x) = True.
Proof. exact (@lem1396582 Prop x). Qed.
Lemma lem1396584 (_24776 : real) (_24777 : real) : ((term369 _24776 _24777) = (term369 _24776 _24777)) = True.
Proof. exact (@lem1396583 (term369 _24776 _24777)). Qed.
Lemma lem1396585 (_24776 : real) (_24777 : real) : ((term258 _24776 _24777) = (term365 _24776 _24777)) = True.
Proof. exact (TRANS (@lem1396580 _24776 _24777) (@lem1396584 _24776 _24777)). Qed.
Lemma lem1396586 (_24776 : real) (_24777 : real) : True = ((term258 _24776 _24777) = (term365 _24776 _24777)).
Proof. exact (SYM (@lem1396585 _24776 _24777)). Qed.
Lemma lem1396587 (_24776 : real) (_24777 : real) : (term258 _24776 _24777) = (term365 _24776 _24777).
Proof. exact (EQ_MP (@lem1396586 _24776 _24777) (@lem0)). Qed.
Lemma lem1396588 (_24776 : real) (_24777 : real) (h1 : term237) : term365 _24776 _24777.
Proof. exact (EQ_MP (@lem1396587 _24776 _24777) (@lem1396231 _24776 _24777 h1)). Qed.
Lemma lem1396590 (b : Prop) (a : Prop) : (a \/ b) = (term331 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1396591 (_24777 : real) (_24776 : real) : (term365 _24776 _24777) = (term372 _24777 _24776).
Proof. exact (@lem1396590 (term366 _24776 _24777) (_24776 = term18)). Qed.
Lemma lem1396593 (a : Prop) (b : Prop) : (term334 a b) = (term335 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1396594 (_24776 : real) (_24777 : real) : (term373 _24776 _24777) = (term374 _24776 _24777).
Proof. exact (@lem1396593 (term349 _24776 _24777) (_24777 = term18)). Qed.
Lemma lem1396596 (a : Prop) : (term338 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1396597 (_24776 : real) (_24777 : real) : (term375 _24776 _24777) = ((real_mul _24776 _24777) = term18).
Proof. exact (@lem1396596 ((real_mul _24776 _24777) = term18)). Qed.
Lemma lem1396598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1396599 (_24776 : real) (_24777 : real) : (term376 _24776 _24777) = (term377 _24776 _24777).
Proof. exact (MK_COMB (@lem1396598) (@lem1396597 _24776 _24777)). Qed.
Lemma lem1396600 (_24777 : real) : (term363 _24777) = (term363 _24777).
Proof. exact (eq_refl (term363 _24777)). Qed.
Lemma lem1396601 (_24776 : real) (_24777 : real) : (term374 _24776 _24777) = (term378 _24776 _24777).
Proof. exact (MK_COMB (@lem1396599 _24776 _24777) (@lem1396600 _24777)). Qed.
Lemma lem1396602 (_24776 : real) (_24777 : real) : (term373 _24776 _24777) = (term378 _24776 _24777).
Proof. exact (TRANS (@lem1396594 _24776 _24777) (@lem1396601 _24776 _24777)). Qed.
Lemma lem1396603 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1396604 (_24776 : real) (_24777 : real) : (term379 _24776 _24777) = (term380 _24776 _24777).
Proof. exact (MK_COMB (@lem1396603) (@lem1396602 _24776 _24777)). Qed.
Lemma lem1396605 (_24776 : real) : (_24776 = term18) = (_24776 = term18).
Proof. exact (eq_refl (_24776 = term18)). Qed.
Lemma lem1396606 (_24777 : real) (_24776 : real) : (term372 _24777 _24776) = (term381 _24777 _24776).
Proof. exact (MK_COMB (@lem1396604 _24776 _24777) (@lem1396605 _24776)). Qed.
Lemma lem1396607 (_24777 : real) (_24776 : real) : (term365 _24776 _24777) = (term381 _24777 _24776).
Proof. exact (TRANS (@lem1396591 _24777 _24776) (@lem1396606 _24777 _24776)). Qed.
Lemma lem1396609 (x : real) (y : real) (h1 : term230 x y) : term378 x y.
Proof. exact (conj (@lem1396446 x y h1) (@lem1396493 x y h1)). Qed.
Lemma lem1396611 (_24777 : real) (_24776 : real) (h1 : term237) : term381 _24777 _24776.
Proof. exact (EQ_MP (@lem1396607 _24777 _24776) (@lem1396588 _24776 _24777 h1)). Qed.
Lemma lem1396612 (y : real) (x : real) (h1 : term237) : term381 y x.
Proof. exact (@lem1396611 y x h1). Qed.
Lemma lem1396615 (x : real) (y : real) (h1 : term237) (h2 : term230 x y) : x = term18.
Proof. exact (@lem1396612 y x h1 (@lem1396609 x y h2)). Qed.
Lemma lem1396616 (x : real) (y : real) (h1 : term237) (h2 : term230 x y) : term382 x.
Proof. exact (fun h0 : term363 x => @lem1396615 x y h1 h2). Qed.
Lemma lem1396618 (p : Prop) : (term319 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1396619 (x : real) : (term382 x) = (x = term18).
Proof. exact (@lem1396618 (x = term18)). Qed.
Lemma lem1396620 (x : real) (y : real) (h1 : term237) (h2 : term230 x y) : x = term18.
Proof. exact (EQ_MP (@lem1396619 x) (@lem1396616 x y h1 h2)). Qed.
Lemma lem1396622 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1396623 (x : real) : term350 x.
Proof. exact (fun h0 : term351 x => @lem1396622 x). Qed.
Lemma lem1396625 (p : Prop) : (term319 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1396626 (x : real) : (term350 x) = (x = x).
Proof. exact (@lem1396625 (x = x)). Qed.
Lemma lem1396627 (x : real) : x = x.
Proof. exact (EQ_MP (@lem1396626 x) (@lem1396623 x)). Qed.
Lemma lem1396628 (x : real) (y : real) (h1 : term237) (h2 : term230 x y) : term383 x.
Proof. exact (conj (@lem1396620 x y h1 h2) (@lem1396627 x)). Qed.
Lemma lem1396630 (x : real) (y : real) (z : real) : term345 x y z.
Proof. exact (EQ_MP (@lem1396433 x y z) (@lem1396412 y x z)). Qed.
Lemma lem1396631 (x : real) : term384 x.
Proof. exact (@lem1396630 x term18 x). Qed.
Lemma lem1396634 (x : real) (y : real) (h1 : term237) (h2 : term230 x y) : term18 = x.
Proof. exact (@lem1396631 x (@lem1396628 x y h1 h2)). Qed.
Lemma lem1396635 (x : real) (y : real) (h1 : term237) (h2 : term230 x y) : term385 x.
Proof. exact (fun h0 : term316 x => @lem1396634 x y h1 h2). Qed.
Lemma lem1396637 (p : Prop) : (term319 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1396638 (x : real) : (term385 x) = (term18 = x).
Proof. exact (@lem1396637 (term18 = x)). Qed.
Lemma lem1396639 (x : real) (y : real) (h1 : term237) (h2 : term230 x y) : term18 = x.
Proof. exact (EQ_MP (@lem1396638 x) (@lem1396635 x y h1 h2)). Qed.
Lemma lem1396642 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1396644 (x : real) : (term316 x) = (term386 x).
Proof. exact (@lem1396642 (term18 = x)). Qed.
Lemma lem1396647 (x : real) (y : real) (h1 : term230 x y) : term386 x.
Proof. exact (EQ_MP (@lem1396644 x) (@lem1396241 x y h1)). Qed.
Lemma lem1396650 (x : real) (y : real) (h1 : term237) (h2 : term230 x y) : False.
Proof. exact (@lem1396647 x y h2 (@lem1396639 x y h1 h2)). Qed.
Lemma lem1396651 (x : real) (y : real) (h1 : term237) (h2 : term230 x y) : term387.
Proof. exact (fun h0 : ~ False => @lem1396650 x y h1 h2). Qed.
Lemma lem1396653 (p : Prop) : (term319 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1396654 : term387 = False.
Proof. exact (@lem1396653 False). Qed.
Lemma lem1396655 (x : real) (y : real) (h1 : term237) (h2 : term230 x y) : False.
Proof. exact (EQ_MP (@lem1396654) (@lem1396651 x y h1 h2)). Qed.
Lemma lem1396656 (x : real) (y : real) (h1 : term230 x y) : term235.
Proof. exact (fun h0 : term237 => @lem1396655 x y h0 h1). Qed.
Lemma lem1396657 : term235 = term236.
Proof. exact (@lem69 term237). Qed.
Lemma lem1396658 (x : real) (y : real) (h1 : term230 x y) : term236.
Proof. exact (EQ_MP (@lem1396657) (@lem1396656 x y h1)). Qed.
Lemma lem1396659 (x : real) (y : real) : term239 x y.
Proof. exact (fun h0 : term230 x y => @lem1396658 x y h0). Qed.
Lemma lem1396664 (y : real) : term243 y.
Proof. exact (fun x : real => @lem1396659 x y). Qed.
Lemma lem1396669 : term247.
Proof. exact (fun y : real => @lem1396664 y). Qed.
Lemma lem1396670 : term246.
Proof. exact (EQ_MP (@lem1395642) (@lem1396669)). Qed.
Lemma lem1396671 (y : real) : term388 y.
Proof. exact (@lem1396670 y). Qed.
Lemma lem1396672 (y : real) : (term388 y) = (term242 y).
Proof. exact (eq_refl (term388 y)). Qed.
Lemma lem1396673 (y : real) : term242 y.
Proof. exact (EQ_MP (@lem1396672 y) (@lem1396671 y)). Qed.
Lemma lem1396674 (y : real) (x : real) : term389 y x.
Proof. exact (@lem1396673 y x). Qed.
Lemma lem1396675 (x : real) (y : real) : (term389 y x) = (term231 x y).
Proof. exact (eq_refl (term389 y x)). Qed.
Lemma lem1396676 (x : real) (y : real) : term231 x y.
Proof. exact (EQ_MP (@lem1396675 x y) (@lem1396674 y x)). Qed.
Lemma lem1396678 (x : real) (y : real) : term231 x y.
Proof. exact (@lem1395498 x y (@lem1396676 x y)). Qed.
Lemma lem1396679 (x : real) (y : real) (h1 : term230 x y) : term235.
Proof. exact (@lem1396678 x y (@lem1395483 x y h1)). Qed.
Lemma lem1396680 (x : real) (y : real) (h1 : term230 x y) : False.
Proof. exact (@lem1396679 x y h1 (@lem1382769)). Qed.
Lemma lem1396681 (x : real) (y : real) (h1 : term230 x y) : (term230 x y) = False.
Proof. exact (prop_ext (fun h2 : term230 x y => @lem1396680 x y h1) (fun h2 : False => @lem1395483 x y h1)). Qed.
Lemma lem1396682 (x : real) (y : real) (h1 : term230 x y) : False.
Proof. exact (EQ_MP (@lem1396681 x y h1) (@lem1395483 x y h1)). Qed.
Lemma lem1396683 (x : real) (y : real) : term229 x y.
Proof. exact (fun h0 : term230 x y => @lem1396682 x y h0). Qed.
Lemma lem1396684 (x : real) (y : real) : term226 x y.
Proof. exact (EQ_MP (@lem1395482 x y) (@lem1396683 x y)). Qed.
Lemma lem1396685 (x : real) (y : real) : term172 x y.
Proof. exact (EQ_MP (@lem1395478 x y) (@lem1396684 x y)). Qed.
Lemma lem1396686 (x : real) (y : real) : term177 x y.
Proof. exact (EQ_MP (@lem1394788 x y) (@lem1396685 x y)). Qed.
