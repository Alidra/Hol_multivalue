Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUP_INSERT_INSERT_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import SUP_EQ_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482686_spec.
Require Import thm1483205_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982761_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988297_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5178242 (s : real -> Prop) (c : real) : term0 s c.
Proof. exact (@lem9784 (term1 s c)). Qed.
Lemma lem5178243 (s : real -> Prop) (c : real) : (term0 s c) = (term2 s c).
Proof. exact (eq_refl (term0 s c)). Qed.
Lemma lem5178244 (s : real -> Prop) (c : real) : term2 s c.
Proof. exact (EQ_MP (@lem5178243 s c) (@lem5178242 s c)). Qed.
Lemma lem5178245 (s : real -> Prop) (c : real) (h1 : term1 s c) : term1 s c.
Proof. exact (h1). Qed.
Lemma lem5178246 (s : real -> Prop) (c : real) (h1 : term3 s c) : term3 s c.
Proof. exact (h1). Qed.
Lemma lem5178247 {_83983 : Type'} (P : _83983 -> Prop) : term4 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem5178248 {_83983 : Type'} (P : _83983 -> Prop) : (term4 _83983 P) = (term5 _83983 P).
Proof. exact (eq_refl (term4 _83983 P)). Qed.
Lemma lem5178249 {_83983 : Type'} (P : _83983 -> Prop) : term5 _83983 P.
Proof. exact (EQ_MP (@lem5178248 _83983 P) (@lem5178247 _83983 P)). Qed.
Lemma lem5178250 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term6 _83983 P a.
Proof. exact (@lem5178249 _83983 P a). Qed.
Lemma lem5178251 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term6 _83983 P a) = (term7 _83983 a P).
Proof. exact (eq_refl (term6 _83983 P a)). Qed.
Lemma lem5178252 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term7 _83983 a P.
Proof. exact (EQ_MP (@lem5178251 _83983 a P) (@lem5178250 _83983 P a)). Qed.
Lemma lem5178253 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term8 _83983 a P s.
Proof. exact (@lem5178252 _83983 a P s). Qed.
Lemma lem5178254 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term8 _83983 a P s) = ((term9 _83983 a s P) = (term10 _83983 a s P)).
Proof. exact (eq_refl (term8 _83983 a P s)). Qed.
Lemma lem5178256 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5178257 (s : real -> Prop) (h1 : term11) : term12 s.
Proof. exact (@lem5178256 h1 s). Qed.
Lemma lem5178258 (s : real -> Prop) : (term12 s) = (term13 s).
Proof. exact (eq_refl (term12 s)). Qed.
Lemma lem5178259 (s : real -> Prop) (h1 : term11) : term13 s.
Proof. exact (EQ_MP (@lem5178258 s) (@lem5178257 s h1)). Qed.
Lemma lem5178260 (s : real -> Prop) (t : real -> Prop) (h1 : term11) : term14 s t.
Proof. exact (@lem5178259 s h1 t). Qed.
Lemma lem5178261 (s : real -> Prop) (t : real -> Prop) : (term14 s t) = (term15 s t).
Proof. exact (eq_refl (term14 s t)). Qed.
Lemma lem5178262 (s : real -> Prop) (t : real -> Prop) (h1 : term11) : term15 s t.
Proof. exact (EQ_MP (@lem5178261 s t) (@lem5178260 s t h1)). Qed.
Lemma lem5178263 (s : real -> Prop) (t : real -> Prop) (h1 : term16 s t) : term16 s t.
Proof. exact (h1). Qed.
Lemma lem5178264 (s : real -> Prop) (t : real -> Prop) (h1 : term11) (h2 : term16 s t) : (sup s) = (sup t).
Proof. exact (@lem5178262 s t h1 (@lem5178263 s t h2)). Qed.
Lemma lem5178265 (s : real -> Prop) (t : real -> Prop) (h1 : term16 s t) : term17 s t.
Proof. exact (fun h0 : term11 => @lem5178264 s t h0 h1). Qed.
Lemma lem5178266 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5178267 (s : real -> Prop) (t : real -> Prop) (h1 : term11) (h2 : term16 s t) : (sup s) = (sup t).
Proof. exact (@lem5178265 s t h2 (@lem5178266 h1)). Qed.
Lemma lem5178268 (s : real -> Prop) (t : real -> Prop) (h1 : term11) : term15 s t.
Proof. exact (fun h0 : term16 s t => @lem5178267 s t h1 h0). Qed.
Lemma lem5178269 (s : real -> Prop) (h1 : term11) : term13 s.
Proof. exact (fun t : real -> Prop => @lem5178268 s t h1). Qed.
Lemma lem5178270 (h1 : term11) : term11.
Proof. exact (fun s : real -> Prop => @lem5178269 s h1). Qed.
Lemma lem5178271 : term18.
Proof. exact (fun h0 : term11 => @lem5178270 h0). Qed.
Lemma lem5178272 : term11.
Proof. exact (@lem5178271 (@lem5135108)). Qed.
Lemma lem5178273 (s : real -> Prop) : term12 s.
Proof. exact (@lem5178272 s). Qed.
Lemma lem5178274 (s : real -> Prop) : (term12 s) = (term13 s).
Proof. exact (eq_refl (term12 s)). Qed.
Lemma lem5178275 (s : real -> Prop) : term13 s.
Proof. exact (EQ_MP (@lem5178274 s) (@lem5178273 s)). Qed.
Lemma lem5178276 (s : real -> Prop) (t : real -> Prop) : term14 s t.
Proof. exact (@lem5178275 s t). Qed.
Lemma lem5178277 (s : real -> Prop) (t : real -> Prop) : (term14 s t) = (term15 s t).
Proof. exact (eq_refl (term14 s t)). Qed.
Lemma lem5178280 (s : real -> Prop) (t : real -> Prop) : term15 s t.
Proof. exact (EQ_MP (@lem5178277 s t) (@lem5178276 s t)). Qed.
Lemma lem5178281 (a : real) (b : real) (s : real -> Prop) : term19 a b s.
Proof. exact (@lem5178280 (term20 b a s) (term21 a b s)). Qed.
Lemma lem5178285 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term9 _83983 a s P) = (term10 _83983 a s P).
Proof. exact (EQ_MP (@lem5178254 _83983 a s P) (@lem5178253 _83983 a P s)). Qed.
Lemma lem5178286 (a : real) (s : real -> Prop) (P : real -> Prop) : (term22 a s P) = (term23 a s P).
Proof. exact (@lem5178285 real a s P). Qed.
Lemma lem5178287 (b : real) (a : real) (s : real -> Prop) (c : real) : (term24 b a s c) = (term25 b a s c).
Proof. exact (@lem5178286 b (@INSERT real a s) (term26 c)). Qed.
Lemma lem5178288 (x : real) (c : real) : (term27 c x) = (real_le x c).
Proof. exact (eq_refl (term27 c x)). Qed.
Lemma lem5178289 (x : real) (b : real) (a : real) (s : real -> Prop) : (term28 x b a s) = (term28 x b a s).
Proof. exact (eq_refl (term28 x b a s)). Qed.
Lemma lem5178290 (b : real) (a : real) (s : real -> Prop) (x : real) (c : real) : (term29 b a s c x) = (term30 b a s x c).
Proof. exact (MK_COMB (@lem5178289 x b a s) (@lem5178288 x c)). Qed.
Lemma lem5178291 (b : real) (a : real) (s : real -> Prop) (c : real) : (term31 b a s c) = (term32 b a s c).
Proof. exact (fun_ext (fun x : real => @lem5178290 b a s x c)). Qed.
Lemma lem5178292 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5178293 (b : real) (a : real) (s : real -> Prop) (c : real) : (term24 b a s c) = (term33 b a s c).
Proof. exact (MK_COMB (@lem5178292) (@lem5178291 b a s c)). Qed.
Lemma lem5178294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5178295 (b : real) (a : real) (s : real -> Prop) (c : real) : (term34 b a s c) = (term35 b a s c).
Proof. exact (MK_COMB (@lem5178294) (@lem5178293 b a s c)). Qed.
Lemma lem5178296 (b : real) (c : real) : (term27 c b) = (real_le b c).
Proof. exact (eq_refl (term27 c b)). Qed.
Lemma lem5178297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5178298 (b : real) (c : real) : (term36 c b) = (term37 b c).
Proof. exact (MK_COMB (@lem5178297) (@lem5178296 b c)). Qed.
Lemma lem5178299 (x : real) (c : real) : (term27 c x) = (real_le x c).
Proof. exact (eq_refl (term27 c x)). Qed.
Lemma lem5178300 (x : real) (a : real) (s : real -> Prop) : (term38 x a s) = (term38 x a s).
Proof. exact (eq_refl (term38 x a s)). Qed.
Lemma lem5178301 (a : real) (s : real -> Prop) (x : real) (c : real) : (term39 a s c x) = (term40 a s x c).
Proof. exact (MK_COMB (@lem5178300 x a s) (@lem5178299 x c)). Qed.
Lemma lem5178302 (a : real) (s : real -> Prop) (c : real) : (term41 a s c) = (term42 a s c).
Proof. exact (fun_ext (fun x : real => @lem5178301 a s x c)). Qed.
Lemma lem5178303 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5178304 (a : real) (s : real -> Prop) (c : real) : (term43 a s c) = (term44 a s c).
Proof. exact (MK_COMB (@lem5178303) (@lem5178302 a s c)). Qed.
Lemma lem5178305 (b : real) (a : real) (s : real -> Prop) (c : real) : (term25 b a s c) = (term45 b a s c).
Proof. exact (MK_COMB (@lem5178298 b c) (@lem5178304 a s c)). Qed.
Lemma lem5178306 (b : real) (a : real) (s : real -> Prop) (c : real) : ((term24 b a s c) = (term25 b a s c)) = ((term33 b a s c) = (term45 b a s c)).
Proof. exact (MK_COMB (@lem5178295 b a s c) (@lem5178305 b a s c)). Qed.
Lemma lem5178307 (b : real) (a : real) (s : real -> Prop) (c : real) : (term33 b a s c) = (term45 b a s c).
Proof. exact (EQ_MP (@lem5178306 b a s c) (@lem5178287 b a s c)). Qed.
Lemma lem5178311 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term9 _83983 a s P) = (term10 _83983 a s P).
Proof. exact (EQ_MP (@lem5178254 _83983 a s P) (@lem5178253 _83983 a P s)). Qed.
Lemma lem5178312 (a : real) (s : real -> Prop) (P : real -> Prop) : (term22 a s P) = (term23 a s P).
Proof. exact (@lem5178311 real a s P). Qed.
Lemma lem5178313 (a : real) (s : real -> Prop) (c : real) : (term43 a s c) = (term46 a s c).
Proof. exact (@lem5178312 a s (term26 c)). Qed.
Lemma lem5178314 (x : real) (c : real) : (term27 c x) = (real_le x c).
Proof. exact (eq_refl (term27 c x)). Qed.
Lemma lem5178315 (x : real) (a : real) (s : real -> Prop) : (term38 x a s) = (term38 x a s).
Proof. exact (eq_refl (term38 x a s)). Qed.
Lemma lem5178316 (a : real) (s : real -> Prop) (x : real) (c : real) : (term39 a s c x) = (term40 a s x c).
Proof. exact (MK_COMB (@lem5178315 x a s) (@lem5178314 x c)). Qed.
Lemma lem5178317 (a : real) (s : real -> Prop) (c : real) : (term41 a s c) = (term42 a s c).
Proof. exact (fun_ext (fun x : real => @lem5178316 a s x c)). Qed.
Lemma lem5178318 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5178319 (a : real) (s : real -> Prop) (c : real) : (term43 a s c) = (term44 a s c).
Proof. exact (MK_COMB (@lem5178318) (@lem5178317 a s c)). Qed.
Lemma lem5178320 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5178321 (a : real) (s : real -> Prop) (c : real) : (term47 a s c) = (term48 a s c).
Proof. exact (MK_COMB (@lem5178320) (@lem5178319 a s c)). Qed.
Lemma lem5178322 (a : real) (c : real) : (term27 c a) = (real_le a c).
Proof. exact (eq_refl (term27 c a)). Qed.
Lemma lem5178323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5178324 (a : real) (c : real) : (term36 c a) = (term37 a c).
Proof. exact (MK_COMB (@lem5178323) (@lem5178322 a c)). Qed.
Lemma lem5178325 (x : real) (c : real) : (term27 c x) = (real_le x c).
Proof. exact (eq_refl (term27 c x)). Qed.
Lemma lem5178326 (x : real) (s : real -> Prop) : (term49 x s) = (term49 x s).
Proof. exact (eq_refl (term49 x s)). Qed.
Lemma lem5178327 (s : real -> Prop) (x : real) (c : real) : (term50 s c x) = (term51 s x c).
Proof. exact (MK_COMB (@lem5178326 x s) (@lem5178325 x c)). Qed.
Lemma lem5178328 (s : real -> Prop) (c : real) : (term52 s c) = (term53 s c).
Proof. exact (fun_ext (fun x : real => @lem5178327 s x c)). Qed.
Lemma lem5178329 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5178330 (s : real -> Prop) (c : real) : (term54 s c) = (term1 s c).
Proof. exact (MK_COMB (@lem5178329) (@lem5178328 s c)). Qed.
Lemma lem5178331 (a : real) (s : real -> Prop) (c : real) : (term46 a s c) = (term55 a s c).
Proof. exact (MK_COMB (@lem5178324 a c) (@lem5178330 s c)). Qed.
Lemma lem5178332 (a : real) (s : real -> Prop) (c : real) : ((term43 a s c) = (term46 a s c)) = ((term44 a s c) = (term55 a s c)).
Proof. exact (MK_COMB (@lem5178321 a s c) (@lem5178331 a s c)). Qed.
Lemma lem5178333 (a : real) (s : real -> Prop) (c : real) : (term44 a s c) = (term55 a s c).
Proof. exact (EQ_MP (@lem5178332 a s c) (@lem5178313 a s c)). Qed.
Lemma lem5178342 (b : real) (c : real) : (term37 b c) = (term37 b c).
Proof. exact (eq_refl (term37 b c)). Qed.
Lemma lem5178343 (b : real) (a : real) (s : real -> Prop) (c : real) : (term45 b a s c) = (term56 b a s c).
Proof. exact (MK_COMB (@lem5178342 b c) (@lem5178333 a s c)). Qed.
Lemma lem5178346 (b : real) (a : real) (s : real -> Prop) (c : real) : (term33 b a s c) = (term56 b a s c).
Proof. exact (TRANS (@lem5178307 b a s c) (@lem5178343 b a s c)). Qed.
Lemma lem5178347 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5178348 (b : real) (a : real) (s : real -> Prop) (c : real) : (term35 b a s c) = (term57 b a s c).
Proof. exact (MK_COMB (@lem5178347) (@lem5178346 b a s c)). Qed.
Lemma lem5178350 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term9 _83983 a s P) = (term10 _83983 a s P).
Proof. exact (EQ_MP (@lem5178254 _83983 a s P) (@lem5178253 _83983 a P s)). Qed.
Lemma lem5178351 (a : real) (s : real -> Prop) (P : real -> Prop) : (term22 a s P) = (term23 a s P).
Proof. exact (@lem5178350 real a s P). Qed.
Lemma lem5178352 (a : real) (b : real) (s : real -> Prop) (c : real) : (term58 a b s c) = (term59 a b s c).
Proof. exact (@lem5178351 (real_max a b) s (term26 c)). Qed.
Lemma lem5178353 (x : real) (c : real) : (term27 c x) = (real_le x c).
Proof. exact (eq_refl (term27 c x)). Qed.
Lemma lem5178354 (x : real) (a : real) (b : real) (s : real -> Prop) : (term60 x a b s) = (term60 x a b s).
Proof. exact (eq_refl (term60 x a b s)). Qed.
Lemma lem5178355 (a : real) (b : real) (s : real -> Prop) (x : real) (c : real) : (term61 a b s c x) = (term62 a b s x c).
Proof. exact (MK_COMB (@lem5178354 x a b s) (@lem5178353 x c)). Qed.
Lemma lem5178356 (a : real) (b : real) (s : real -> Prop) (c : real) : (term63 a b s c) = (term64 a b s c).
Proof. exact (fun_ext (fun x : real => @lem5178355 a b s x c)). Qed.
Lemma lem5178357 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5178358 (a : real) (b : real) (s : real -> Prop) (c : real) : (term58 a b s c) = (term65 a b s c).
Proof. exact (MK_COMB (@lem5178357) (@lem5178356 a b s c)). Qed.
Lemma lem5178359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5178360 (a : real) (b : real) (s : real -> Prop) (c : real) : (term66 a b s c) = (term67 a b s c).
Proof. exact (MK_COMB (@lem5178359) (@lem5178358 a b s c)). Qed.
Lemma lem5178361 (a : real) (b : real) (c : real) : (term68 c a b) = (term69 a b c).
Proof. exact (eq_refl (term68 c a b)). Qed.
Lemma lem5178362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5178363 (a : real) (b : real) (c : real) : (term70 c a b) = (term71 a b c).
Proof. exact (MK_COMB (@lem5178362) (@lem5178361 a b c)). Qed.
Lemma lem5178364 (x : real) (c : real) : (term27 c x) = (real_le x c).
Proof. exact (eq_refl (term27 c x)). Qed.
Lemma lem5178365 (x : real) (s : real -> Prop) : (term49 x s) = (term49 x s).
Proof. exact (eq_refl (term49 x s)). Qed.
Lemma lem5178366 (s : real -> Prop) (x : real) (c : real) : (term50 s c x) = (term51 s x c).
Proof. exact (MK_COMB (@lem5178365 x s) (@lem5178364 x c)). Qed.
Lemma lem5178367 (s : real -> Prop) (c : real) : (term52 s c) = (term53 s c).
Proof. exact (fun_ext (fun x : real => @lem5178366 s x c)). Qed.
Lemma lem5178368 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5178369 (s : real -> Prop) (c : real) : (term54 s c) = (term1 s c).
Proof. exact (MK_COMB (@lem5178368) (@lem5178367 s c)). Qed.
Lemma lem5178370 (a : real) (b : real) (s : real -> Prop) (c : real) : (term59 a b s c) = (term72 a b s c).
Proof. exact (MK_COMB (@lem5178363 a b c) (@lem5178369 s c)). Qed.
Lemma lem5178371 (a : real) (b : real) (s : real -> Prop) (c : real) : ((term58 a b s c) = (term59 a b s c)) = ((term65 a b s c) = (term72 a b s c)).
Proof. exact (MK_COMB (@lem5178360 a b s c) (@lem5178370 a b s c)). Qed.
Lemma lem5178372 (a : real) (b : real) (s : real -> Prop) (c : real) : (term65 a b s c) = (term72 a b s c).
Proof. exact (EQ_MP (@lem5178371 a b s c) (@lem5178352 a b s c)). Qed.
Lemma lem5178381 (a : real) (b : real) (s : real -> Prop) (c : real) : ((term33 b a s c) = (term65 a b s c)) = ((term56 b a s c) = (term72 a b s c)).
Proof. exact (MK_COMB (@lem5178348 b a s c) (@lem5178372 a b s c)). Qed.
Lemma lem5178384 (a : real) (b : real) (s : real -> Prop) (c : real) : ((term56 b a s c) = (term72 a b s c)) = ((term33 b a s c) = (term65 a b s c)).
Proof. exact (SYM (@lem5178381 a b s c)). Qed.
Lemma lem5178385 (x : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : term73 s c x.
Proof. exact (@lem5178245 s c h1 x). Qed.
Lemma lem5178386 (s : real -> Prop) (x : real) (c : real) : (term73 s c x) = (term51 s x c).
Proof. exact (eq_refl (term73 s c x)). Qed.
Lemma lem5178387 (x : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : term51 s x c.
Proof. exact (EQ_MP (@lem5178386 s x c) (@lem5178385 x s c h1)). Qed.
Lemma lem5178388 (s : real -> Prop) (x : real) (c : real) : (term51 s x c) = ((term51 s x c) = True).
Proof. exact (@lem7 (term51 s x c)). Qed.
Lemma lem5178401 (x : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term51 s x c) = True.
Proof. exact (EQ_MP (@lem5178388 s x c) (@lem5178387 x s c h1)). Qed.
Lemma lem5178402 (s : real -> Prop) (c : real) (h1 : term1 s c) : (term53 s c) = term74.
Proof. exact (fun_ext (fun x : real => @lem5178401 x s c h1)). Qed.
Lemma lem5178403 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5178404 (s : real -> Prop) (c : real) (h1 : term1 s c) : (term1 s c) = term75.
Proof. exact (MK_COMB (@lem5178403) (@lem5178402 s c h1)). Qed.
Lemma lem5178406 {A : Type'} (t : Prop) : (term76 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5178407 (t : Prop) : (term77 t) = t.
Proof. exact (@lem5178406 real t). Qed.
Lemma lem5178408 : term75 = True.
Proof. exact (@lem5178407 True). Qed.
Lemma lem5178409 (s : real -> Prop) (c : real) (h1 : term1 s c) : (term1 s c) = True.
Proof. exact (TRANS (@lem5178404 s c h1) (@lem5178408)). Qed.
Lemma lem5178410 (a : real) (c : real) : (term37 a c) = (term37 a c).
Proof. exact (eq_refl (term37 a c)). Qed.
Lemma lem5178411 (a : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term55 a s c) = (term78 a c).
Proof. exact (MK_COMB (@lem5178410 a c) (@lem5178409 s c h1)). Qed.
Lemma lem5178413 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem5178414 (a : real) (c : real) : (term78 a c) = (real_le a c).
Proof. exact (@lem5178413 (real_le a c)). Qed.
Lemma lem5178415 (a : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term55 a s c) = (real_le a c).
Proof. exact (TRANS (@lem5178411 a s c h1) (@lem5178414 a c)). Qed.
Lemma lem5178416 (b : real) (c : real) : (term37 b c) = (term37 b c).
Proof. exact (eq_refl (term37 b c)). Qed.
Lemma lem5178417 (b : real) (a : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term56 b a s c) = (term79 b a c).
Proof. exact (MK_COMB (@lem5178416 b c) (@lem5178415 a s c h1)). Qed.
Lemma lem5178420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5178421 (b : real) (a : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term57 b a s c) = (term80 b a c).
Proof. exact (MK_COMB (@lem5178420) (@lem5178417 b a s c h1)). Qed.
Lemma lem5178429 (x : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term51 s x c) = True.
Proof. exact (EQ_MP (@lem5178388 s x c) (@lem5178387 x s c h1)). Qed.
Lemma lem5178430 (s : real -> Prop) (c : real) (h1 : term1 s c) : (term53 s c) = term74.
Proof. exact (fun_ext (fun x : real => @lem5178429 x s c h1)). Qed.
Lemma lem5178431 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5178432 (s : real -> Prop) (c : real) (h1 : term1 s c) : (term1 s c) = term75.
Proof. exact (MK_COMB (@lem5178431) (@lem5178430 s c h1)). Qed.
Lemma lem5178434 {A : Type'} (t : Prop) : (term76 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5178435 (t : Prop) : (term77 t) = t.
Proof. exact (@lem5178434 real t). Qed.
Lemma lem5178436 : term75 = True.
Proof. exact (@lem5178435 True). Qed.
Lemma lem5178437 (s : real -> Prop) (c : real) (h1 : term1 s c) : (term1 s c) = True.
Proof. exact (TRANS (@lem5178432 s c h1) (@lem5178436)). Qed.
Lemma lem5178438 (a : real) (b : real) (c : real) : (term71 a b c) = (term71 a b c).
Proof. exact (eq_refl (term71 a b c)). Qed.
Lemma lem5178439 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term72 a b s c) = (term81 a b c).
Proof. exact (MK_COMB (@lem5178438 a b c) (@lem5178437 s c h1)). Qed.
Lemma lem5178441 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem5178442 (a : real) (b : real) (c : real) : (term81 a b c) = (term69 a b c).
Proof. exact (@lem5178441 (term69 a b c)). Qed.
Lemma lem5178443 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term72 a b s c) = (term69 a b c).
Proof. exact (TRANS (@lem5178439 a b s c h1) (@lem5178442 a b c)). Qed.
Lemma lem5178444 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : ((term56 b a s c) = (term72 a b s c)) = ((term79 b a c) = (term69 a b c)).
Proof. exact (MK_COMB (@lem5178421 b a s c h1) (@lem5178443 a b s c h1)). Qed.
Lemma lem5178447 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : ((term79 b a c) = (term69 a b c)) = ((term56 b a s c) = (term72 a b s c)).
Proof. exact (SYM (@lem5178444 a b s c h1)). Qed.
Lemma lem5178448 (s : real -> Prop) (c : real) : term82 s c.
Proof. exact (@lem82 (term1 s c)). Qed.
Lemma lem5178457 (s : real -> Prop) (c : real) (h1 : term3 s c) : (term1 s c) = False.
Proof. exact (@lem5178448 s c (@lem5178246 s c h1)). Qed.
Lemma lem5178458 (a : real) (c : real) : (term37 a c) = (term37 a c).
Proof. exact (eq_refl (term37 a c)). Qed.
Lemma lem5178459 (a : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term55 a s c) = (term83 a c).
Proof. exact (MK_COMB (@lem5178458 a c) (@lem5178457 s c h1)). Qed.
Lemma lem5178461 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem5178462 (a : real) (c : real) : (term83 a c) = False.
Proof. exact (@lem5178461 (real_le a c)). Qed.
Lemma lem5178463 (a : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term55 a s c) = False.
Proof. exact (TRANS (@lem5178459 a s c h1) (@lem5178462 a c)). Qed.
Lemma lem5178464 (b : real) (c : real) : (term37 b c) = (term37 b c).
Proof. exact (eq_refl (term37 b c)). Qed.
Lemma lem5178465 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term56 b a s c) = (term83 b c).
Proof. exact (MK_COMB (@lem5178464 b c) (@lem5178463 a s c h1)). Qed.
Lemma lem5178467 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem5178468 (b : real) (c : real) : (term83 b c) = False.
Proof. exact (@lem5178467 (real_le b c)). Qed.
Lemma lem5178469 (b : real) (a : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term56 b a s c) = False.
Proof. exact (TRANS (@lem5178465 a b s c h1) (@lem5178468 b c)). Qed.
Lemma lem5178470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5178471 (b : real) (a : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term57 b a s c) = (@eq Prop False).
Proof. exact (MK_COMB (@lem5178470) (@lem5178469 b a s c h1)). Qed.
Lemma lem5178475 (s : real -> Prop) (c : real) (h1 : term3 s c) : (term1 s c) = False.
Proof. exact (@lem5178448 s c (@lem5178246 s c h1)). Qed.
Lemma lem5178476 (a : real) (b : real) (c : real) : (term71 a b c) = (term71 a b c).
Proof. exact (eq_refl (term71 a b c)). Qed.
Lemma lem5178477 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term72 a b s c) = (term84 a b c).
Proof. exact (MK_COMB (@lem5178476 a b c) (@lem5178475 s c h1)). Qed.
Lemma lem5178479 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem5178480 (a : real) (b : real) (c : real) : (term84 a b c) = False.
Proof. exact (@lem5178479 (term69 a b c)). Qed.
Lemma lem5178481 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term72 a b s c) = False.
Proof. exact (TRANS (@lem5178477 a b s c h1) (@lem5178480 a b c)). Qed.
Lemma lem5178482 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : ((term56 b a s c) = (term72 a b s c)) = (False = False).
Proof. exact (MK_COMB (@lem5178471 b a s c h1) (@lem5178481 a b s c h1)). Qed.
Lemma lem5178484 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem5178485 : (False = False) = (~ False).
Proof. exact (@lem5178484 False). Qed.
Lemma lem5178487 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5178488 : (False = False) = True.
Proof. exact (TRANS (@lem5178485) (@lem5178487)). Qed.
Lemma lem5178489 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : ((term56 b a s c) = (term72 a b s c)) = True.
Proof. exact (TRANS (@lem5178482 a b s c h1) (@lem5178488)). Qed.
Lemma lem5178490 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : True = ((term56 b a s c) = (term72 a b s c)).
Proof. exact (SYM (@lem5178489 a b s c h1)). Qed.
Lemma lem5178491 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term3 s c) : (term56 b a s c) = (term72 a b s c).
Proof. exact (EQ_MP (@lem5178490 a b s c h1) (@lem0)). Qed.
Lemma lem5178506 (b : real) (a : real) (c : real) : (term85 b a c) = (term86 b a c).
Proof. exact (@lem17045 (real_le b c) (real_le a c)). Qed.
Lemma lem5178511 (a : real) (b : real) (c : real) : (term69 a b c) = (term69 a b c).
Proof. exact (eq_refl (term69 a b c)). Qed.
Lemma lem5178512 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5178513 (b : real) (a : real) (c : real) : (term87 b a c) = (term88 b a c).
Proof. exact (MK_COMB (@lem5178512) (@lem5178506 b a c)). Qed.
Lemma lem5178514 (a : real) (b : real) (c : real) : (term89 a b c) = (term90 a b c).
Proof. exact (MK_COMB (@lem5178513 b a c) (@lem5178511 a b c)). Qed.
Lemma lem5178519 (a : real) (b : real) (c : real) : (term91 a b c) = (term91 a b c).
Proof. exact (eq_refl (term91 a b c)). Qed.
Lemma lem5178520 (a : real) (b : real) (c : real) : (term92 a b c) = (term93 a b c).
Proof. exact (MK_COMB (@lem5178519 a b c) (@lem5178514 a b c)). Qed.
Lemma lem5178521 (a : real) (b : real) (c : real) : (term94 a b c) = (term92 a b c).
Proof. exact (@lem17646 (term79 b a c) (term69 a b c)). Qed.
Lemma lem5178551 (a : real) (b : real) (c : real) : (term94 a b c) = (term93 a b c).
Proof. exact (TRANS (@lem5178521 a b c) (@lem5178520 a b c)). Qed.
Lemma lem5178552 (c : real) (b : real) : (real_le b c) = (term95 c b).
Proof. exact (@lem1988287 c b). Qed.
Lemma lem5178558 (c : real) (b : real) : (real_sub c b) = (term96 c b).
Proof. exact (@lem1982792 c b). Qed.
Lemma lem5178563 (b : real) (c : real) : (term96 c b) = (term97 b c).
Proof. exact (@lem1982761 (term98 b) c). Qed.
Lemma lem5178565 (b : real) (c : real) : (real_sub c b) = (term97 b c).
Proof. exact (TRANS (@lem5178558 c b) (@lem5178563 b c)). Qed.
Lemma lem5178566 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5178567 (b : real) (c : real) : (term99 c b) = (term100 b c).
Proof. exact (MK_COMB (@lem5178566) (@lem5178565 b c)). Qed.
Lemma lem5178568 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178569 (b : real) (c : real) : (term95 c b) = (term102 b c).
Proof. exact (MK_COMB (@lem5178567 b c) (@lem5178568)). Qed.
Lemma lem5178570 (b : real) (c : real) : (real_le b c) = (term102 b c).
Proof. exact (TRANS (@lem5178552 c b) (@lem5178569 b c)). Qed.
Lemma lem5178571 (c : real) (a : real) : (real_le a c) = (term95 c a).
Proof. exact (@lem1988287 c a). Qed.
Lemma lem5178577 (c : real) (a : real) : (real_sub c a) = (term96 c a).
Proof. exact (@lem1982792 c a). Qed.
Lemma lem5178582 (a : real) (c : real) : (term96 c a) = (term97 a c).
Proof. exact (@lem1982761 (term98 a) c). Qed.
Lemma lem5178584 (a : real) (c : real) : (real_sub c a) = (term97 a c).
Proof. exact (TRANS (@lem5178577 c a) (@lem5178582 a c)). Qed.
Lemma lem5178585 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5178586 (a : real) (c : real) : (term99 c a) = (term100 a c).
Proof. exact (MK_COMB (@lem5178585) (@lem5178584 a c)). Qed.
Lemma lem5178587 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178588 (a : real) (c : real) : (term95 c a) = (term102 a c).
Proof. exact (MK_COMB (@lem5178586 a c) (@lem5178587)). Qed.
Lemma lem5178589 (a : real) (c : real) : (real_le a c) = (term102 a c).
Proof. exact (TRANS (@lem5178571 c a) (@lem5178588 a c)). Qed.
Lemma lem5178590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5178591 (b : real) (c : real) : (term37 b c) = (term103 b c).
Proof. exact (MK_COMB (@lem5178590) (@lem5178570 b c)). Qed.
Lemma lem5178592 (b : real) (a : real) (c : real) : (term79 b a c) = (term104 b a c).
Proof. exact (MK_COMB (@lem5178591 b c) (@lem5178589 a c)). Qed.
Lemma lem5178593 (a : real) (b : real) (c : real) : (term105 a b c) = (term106 a b c).
Proof. exact (@lem1988297 (real_max a b) c). Qed.
Lemma lem5178603 (a : real) (b : real) (c : real) : (term107 a b c) = (term108 a b c).
Proof. exact (@lem1982792 (real_max a b) c). Qed.
Lemma lem5178608 (c : real) (a : real) (b : real) : (term108 a b c) = (term109 c a b).
Proof. exact (@lem1982761 (term98 c) (real_max a b)). Qed.
Lemma lem5178610 (c : real) (a : real) (b : real) : (term107 a b c) = (term109 c a b).
Proof. exact (TRANS (@lem5178603 a b c) (@lem5178608 c a b)). Qed.
Lemma lem5178611 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5178612 (c : real) (a : real) (b : real) : (term110 a b c) = (term111 c a b).
Proof. exact (MK_COMB (@lem5178611) (@lem5178610 c a b)). Qed.
Lemma lem5178613 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178614 (c : real) (a : real) (b : real) : (term106 a b c) = (term112 c a b).
Proof. exact (MK_COMB (@lem5178612 c a b) (@lem5178613)). Qed.
Lemma lem5178615 (c : real) (a : real) (b : real) : (term105 a b c) = (term112 c a b).
Proof. exact (TRANS (@lem5178593 a b c) (@lem5178614 c a b)). Qed.
Lemma lem5178616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5178617 (b : real) (a : real) (c : real) : (term113 b a c) = (term114 b a c).
Proof. exact (MK_COMB (@lem5178616) (@lem5178592 b a c)). Qed.
Lemma lem5178618 (c : real) (a : real) (b : real) : (term115 a b c) = (term116 c a b).
Proof. exact (MK_COMB (@lem5178617 b a c) (@lem5178615 c a b)). Qed.
Lemma lem5178619 (b : real) (c : real) : (term117 b c) = (term118 b c).
Proof. exact (@lem1988297 b c). Qed.
Lemma lem5178632 (b : real) (c : real) : (real_sub b c) = (term96 b c).
Proof. exact (@lem1982792 b c). Qed.
Lemma lem5178633 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5178634 (b : real) (c : real) : (term119 b c) = (term120 b c).
Proof. exact (MK_COMB (@lem5178633) (@lem5178632 b c)). Qed.
Lemma lem5178635 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178636 (b : real) (c : real) : (term118 b c) = (term121 b c).
Proof. exact (MK_COMB (@lem5178634 b c) (@lem5178635)). Qed.
Lemma lem5178637 (b : real) (c : real) : (term117 b c) = (term121 b c).
Proof. exact (TRANS (@lem5178619 b c) (@lem5178636 b c)). Qed.
Lemma lem5178638 (a : real) (c : real) : (term117 a c) = (term118 a c).
Proof. exact (@lem1988297 a c). Qed.
Lemma lem5178651 (a : real) (c : real) : (real_sub a c) = (term96 a c).
Proof. exact (@lem1982792 a c). Qed.
Lemma lem5178652 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5178653 (a : real) (c : real) : (term119 a c) = (term120 a c).
Proof. exact (MK_COMB (@lem5178652) (@lem5178651 a c)). Qed.
Lemma lem5178654 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178655 (a : real) (c : real) : (term118 a c) = (term121 a c).
Proof. exact (MK_COMB (@lem5178653 a c) (@lem5178654)). Qed.
Lemma lem5178656 (a : real) (c : real) : (term117 a c) = (term121 a c).
Proof. exact (TRANS (@lem5178638 a c) (@lem5178655 a c)). Qed.
Lemma lem5178657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5178658 (b : real) (c : real) : (term122 b c) = (term123 b c).
Proof. exact (MK_COMB (@lem5178657) (@lem5178637 b c)). Qed.
Lemma lem5178659 (b : real) (a : real) (c : real) : (term86 b a c) = (term124 b a c).
Proof. exact (MK_COMB (@lem5178658 b c) (@lem5178656 a c)). Qed.
Lemma lem5178660 (c : real) (a : real) (b : real) : (term69 a b c) = (term125 c a b).
Proof. exact (@lem1988287 c (real_max a b)). Qed.
Lemma lem5178677 (c : real) (a : real) (b : real) : (term126 c a b) = (term127 c a b).
Proof. exact (@lem1982792 c (real_max a b)). Qed.
Lemma lem5178678 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5178679 (c : real) (a : real) (b : real) : (term128 c a b) = (term129 c a b).
Proof. exact (MK_COMB (@lem5178678) (@lem5178677 c a b)). Qed.
Lemma lem5178680 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178681 (c : real) (a : real) (b : real) : (term125 c a b) = (term130 c a b).
Proof. exact (MK_COMB (@lem5178679 c a b) (@lem5178680)). Qed.
Lemma lem5178682 (c : real) (a : real) (b : real) : (term69 a b c) = (term130 c a b).
Proof. exact (TRANS (@lem5178660 c a b) (@lem5178681 c a b)). Qed.
Lemma lem5178683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5178684 (b : real) (a : real) (c : real) : (term88 b a c) = (term131 b a c).
Proof. exact (MK_COMB (@lem5178683) (@lem5178659 b a c)). Qed.
Lemma lem5178685 (c : real) (a : real) (b : real) : (term90 a b c) = (term132 c a b).
Proof. exact (MK_COMB (@lem5178684 b a c) (@lem5178682 c a b)). Qed.
Lemma lem5178686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5178687 (c : real) (a : real) (b : real) : (term91 a b c) = (term133 c a b).
Proof. exact (MK_COMB (@lem5178686) (@lem5178618 c a b)). Qed.
Lemma lem5178688 (c : real) (a : real) (b : real) : (term93 a b c) = (term134 c a b).
Proof. exact (MK_COMB (@lem5178687 c a b) (@lem5178685 c a b)). Qed.
Lemma lem5178695 (c : real) (a : real) (b : real) : (term94 a b c) = (term134 c a b).
Proof. exact (TRANS (@lem5178551 a b c) (@lem5178688 c a b)). Qed.
Lemma lem5178712 (c : real) (a : real) (b : real) : (term132 c a b) = (term135 c a b).
Proof. exact (@lem19367 (term121 b c) (term121 a c) (term130 c a b)). Qed.
Lemma lem5178727 (c : real) (a : real) (b : real) : (term133 c a b) = (term133 c a b).
Proof. exact (eq_refl (term133 c a b)). Qed.
Lemma lem5178728 (c : real) (a : real) (b : real) : (term134 c a b) = (term136 c a b).
Proof. exact (MK_COMB (@lem5178727 c a b) (@lem5178712 c a b)). Qed.
Lemma lem5178729 (c : real) (a : real) (b : real) : (term94 a b c) = (term136 c a b).
Proof. exact (TRANS (@lem5178695 c a b) (@lem5178728 c a b)). Qed.
Lemma lem5178731 (c : real) (a : real) (b : real) : (term137 c a b) = (term116 c a b).
Proof. exact (eq_refl (term137 c a b)). Qed.
Lemma lem5178732 (c : real) (a : real) (b : real) : (term116 c a b) = (term137 c a b).
Proof. exact (SYM (@lem5178731 c a b)). Qed.
Lemma lem5178733 (b : real) (c : real) (a : real) : (term137 c a b) = (term138 b c a).
Proof. exact (@lem1483205 b (term139 b a c) a). Qed.
Lemma lem5178734 (b : real) (c : real) (a : real) : (term116 c a b) = (term138 b c a).
Proof. exact (TRANS (@lem5178732 c a b) (@lem5178733 b c a)). Qed.
Lemma lem5178735 (b : real) (c : real) (a : real) : (term140 b c a) = (term141 b c a).
Proof. exact (eq_refl (term140 b c a)). Qed.
Lemma lem5178736 (a : real) (b : real) : (term142 a b) = (term142 a b).
Proof. exact (eq_refl (term142 a b)). Qed.
Lemma lem5178737 (b : real) (c : real) (a : real) : (term143 b c a) = (term144 b c a).
Proof. exact (MK_COMB (@lem5178736 a b) (@lem5178735 b c a)). Qed.
Lemma lem5178738 (a : real) (c : real) (b : real) : (term145 a c b) = (term146 a c b).
Proof. exact (eq_refl (term145 a c b)). Qed.
Lemma lem5178739 (b : real) (a : real) : (term147 b a) = (term147 b a).
Proof. exact (eq_refl (term147 b a)). Qed.
Lemma lem5178740 (a : real) (c : real) (b : real) : (term148 a c b) = (term149 a c b).
Proof. exact (MK_COMB (@lem5178739 b a) (@lem5178738 a c b)). Qed.
Lemma lem5178741 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5178742 (a : real) (c : real) (b : real) : (term150 a c b) = (term151 a c b).
Proof. exact (MK_COMB (@lem5178741) (@lem5178740 a c b)). Qed.
Lemma lem5178743 (b : real) (c : real) (a : real) : (term138 b c a) = (term152 b c a).
Proof. exact (MK_COMB (@lem5178742 a c b) (@lem5178737 b c a)). Qed.
Lemma lem5178744 (c : real) (a : real) (b : real) : (term153 c a b) = (term153 c a b).
Proof. exact (eq_refl (term153 c a b)). Qed.
Lemma lem5178745 (b : real) (c : real) (a : real) : ((term116 c a b) = (term138 b c a)) = ((term116 c a b) = (term152 b c a)).
Proof. exact (MK_COMB (@lem5178744 c a b) (@lem5178743 b c a)). Qed.
Lemma lem5178746 (b : real) (c : real) (a : real) : (term116 c a b) = (term152 b c a).
Proof. exact (EQ_MP (@lem5178745 b c a) (@lem5178734 b c a)). Qed.
Lemma lem5178747 (b : real) (a : real) : (real_ge b a) = (term95 b a).
Proof. exact (@lem1988291 b a). Qed.
Lemma lem5178753 (b : real) (a : real) : (real_sub b a) = (term96 b a).
Proof. exact (@lem1982792 b a). Qed.
Lemma lem5178758 (a : real) (b : real) : (term96 b a) = (term97 a b).
Proof. exact (@lem1982761 (term98 a) b). Qed.
Lemma lem5178760 (a : real) (b : real) : (real_sub b a) = (term97 a b).
Proof. exact (TRANS (@lem5178753 b a) (@lem5178758 a b)). Qed.
Lemma lem5178761 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5178762 (a : real) (b : real) : (term99 b a) = (term100 a b).
Proof. exact (MK_COMB (@lem5178761) (@lem5178760 a b)). Qed.
Lemma lem5178763 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178764 (a : real) (b : real) : (term95 b a) = (term102 a b).
Proof. exact (MK_COMB (@lem5178762 a b) (@lem5178763)). Qed.
Lemma lem5178765 (a : real) (b : real) : (real_ge b a) = (term102 a b).
Proof. exact (TRANS (@lem5178747 b a) (@lem5178764 a b)). Qed.
Lemma lem5178766 (b : real) (c : real) : (term102 b c) = (term154 b c).
Proof. exact (@lem1988291 (term97 b c) term101). Qed.
Lemma lem5178784 (b : real) (c : real) : (term155 b c) = (term156 b c).
Proof. exact (@lem1982792 (term97 b c) term101). Qed.
Lemma lem5178786 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5178787 : term101 = term158.
Proof. exact (@lem5178786 (NUMERAL 0)). Qed.
Lemma lem5178789 (x : nat) : (term159 x) = (term160 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5178790 : term161 = term162.
Proof. exact (@lem5178789 term163). Qed.
Lemma lem5178791 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5178792 : term164 = term165.
Proof. exact (MK_COMB (@lem5178791) (@lem5178790)). Qed.
Lemma lem5178793 : term166 = term167.
Proof. exact (MK_COMB (@lem5178792) (@lem5178787)). Qed.
Lemma lem5178794 : term167 = term168.
Proof. exact (@lem1981613 term161 term101 term169 term169). Qed.
Lemma lem5178796 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5178797 : term172 = term173.
Proof. exact (@lem5178796 term163 term163). Qed.
Lemma lem5178798 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5178799 : term175 = term163.
Proof. exact (EQ_MP (@lem5178798) (@lem940073)). Qed.
Lemma lem5178800 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5178801 : term173 = term169.
Proof. exact (MK_COMB (@lem5178800) (@lem5178799)). Qed.
Lemma lem5178802 : term172 = term169.
Proof. exact (TRANS (@lem5178797) (@lem5178801)). Qed.
Lemma lem5178804 (x : nat) : (term176 x) = term101.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5178805 : term166 = term101.
Proof. exact (@lem5178804 term163). Qed.
Lemma lem5178806 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5178807 : term177 = term178.
Proof. exact (MK_COMB (@lem5178806) (@lem5178805)). Qed.
Lemma lem5178808 : term168 = term158.
Proof. exact (MK_COMB (@lem5178807) (@lem5178802)). Qed.
Lemma lem5178809 : term167 = term158.
Proof. exact (TRANS (@lem5178794) (@lem5178808)). Qed.
Lemma lem5178810 : term166 = term158.
Proof. exact (TRANS (@lem5178793) (@lem5178809)). Qed.
Lemma lem5178812 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5178813 : term158 = term101.
Proof. exact (@lem5178812 term101). Qed.
Lemma lem5178814 : term166 = term101.
Proof. exact (TRANS (@lem5178810) (@lem5178813)). Qed.
Lemma lem5178815 (b : real) (c : real) : (term180 b c) = (term180 b c).
Proof. exact (eq_refl (term180 b c)). Qed.
Lemma lem5178816 (b : real) (c : real) : (term156 b c) = (term181 b c).
Proof. exact (MK_COMB (@lem5178815 b c) (@lem5178814)). Qed.
Lemma lem5178817 (b : real) (c : real) : (term181 b c) = (term97 b c).
Proof. exact (@lem1982723 (term97 b c)). Qed.
Lemma lem5178818 (b : real) (c : real) : (term156 b c) = (term97 b c).
Proof. exact (TRANS (@lem5178816 b c) (@lem5178817 b c)). Qed.
Lemma lem5178820 (b : real) (c : real) : (term155 b c) = (term97 b c).
Proof. exact (TRANS (@lem5178784 b c) (@lem5178818 b c)). Qed.
Lemma lem5178821 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5178822 (b : real) (c : real) : (term182 b c) = (term100 b c).
Proof. exact (MK_COMB (@lem5178821) (@lem5178820 b c)). Qed.
Lemma lem5178823 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178824 (b : real) (c : real) : (term154 b c) = (term102 b c).
Proof. exact (MK_COMB (@lem5178822 b c) (@lem5178823)). Qed.
Lemma lem5178825 (b : real) (c : real) : (term102 b c) = (term102 b c).
Proof. exact (TRANS (@lem5178766 b c) (@lem5178824 b c)). Qed.
Lemma lem5178826 (a : real) (c : real) : (term102 a c) = (term154 a c).
Proof. exact (@lem1988291 (term97 a c) term101). Qed.
Lemma lem5178844 (a : real) (c : real) : (term155 a c) = (term156 a c).
Proof. exact (@lem1982792 (term97 a c) term101). Qed.
Lemma lem5178846 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5178847 : term101 = term158.
Proof. exact (@lem5178846 (NUMERAL 0)). Qed.
Lemma lem5178849 (x : nat) : (term159 x) = (term160 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5178850 : term161 = term162.
Proof. exact (@lem5178849 term163). Qed.
Lemma lem5178851 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5178852 : term164 = term165.
Proof. exact (MK_COMB (@lem5178851) (@lem5178850)). Qed.
Lemma lem5178853 : term166 = term167.
Proof. exact (MK_COMB (@lem5178852) (@lem5178847)). Qed.
Lemma lem5178854 : term167 = term168.
Proof. exact (@lem1981613 term161 term101 term169 term169). Qed.
Lemma lem5178856 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5178857 : term172 = term173.
Proof. exact (@lem5178856 term163 term163). Qed.
Lemma lem5178858 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5178859 : term175 = term163.
Proof. exact (EQ_MP (@lem5178858) (@lem940073)). Qed.
Lemma lem5178860 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5178861 : term173 = term169.
Proof. exact (MK_COMB (@lem5178860) (@lem5178859)). Qed.
Lemma lem5178862 : term172 = term169.
Proof. exact (TRANS (@lem5178857) (@lem5178861)). Qed.
Lemma lem5178864 (x : nat) : (term176 x) = term101.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5178865 : term166 = term101.
Proof. exact (@lem5178864 term163). Qed.
Lemma lem5178866 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5178867 : term177 = term178.
Proof. exact (MK_COMB (@lem5178866) (@lem5178865)). Qed.
Lemma lem5178868 : term168 = term158.
Proof. exact (MK_COMB (@lem5178867) (@lem5178862)). Qed.
Lemma lem5178869 : term167 = term158.
Proof. exact (TRANS (@lem5178854) (@lem5178868)). Qed.
Lemma lem5178870 : term166 = term158.
Proof. exact (TRANS (@lem5178853) (@lem5178869)). Qed.
Lemma lem5178872 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5178873 : term158 = term101.
Proof. exact (@lem5178872 term101). Qed.
Lemma lem5178874 : term166 = term101.
Proof. exact (TRANS (@lem5178870) (@lem5178873)). Qed.
Lemma lem5178875 (a : real) (c : real) : (term180 a c) = (term180 a c).
Proof. exact (eq_refl (term180 a c)). Qed.
Lemma lem5178876 (a : real) (c : real) : (term156 a c) = (term181 a c).
Proof. exact (MK_COMB (@lem5178875 a c) (@lem5178874)). Qed.
Lemma lem5178877 (a : real) (c : real) : (term181 a c) = (term97 a c).
Proof. exact (@lem1982723 (term97 a c)). Qed.
Lemma lem5178878 (a : real) (c : real) : (term156 a c) = (term97 a c).
Proof. exact (TRANS (@lem5178876 a c) (@lem5178877 a c)). Qed.
Lemma lem5178880 (a : real) (c : real) : (term155 a c) = (term97 a c).
Proof. exact (TRANS (@lem5178844 a c) (@lem5178878 a c)). Qed.
Lemma lem5178881 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5178882 (a : real) (c : real) : (term182 a c) = (term100 a c).
Proof. exact (MK_COMB (@lem5178881) (@lem5178880 a c)). Qed.
Lemma lem5178883 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178884 (a : real) (c : real) : (term154 a c) = (term102 a c).
Proof. exact (MK_COMB (@lem5178882 a c) (@lem5178883)). Qed.
Lemma lem5178885 (a : real) (c : real) : (term102 a c) = (term102 a c).
Proof. exact (TRANS (@lem5178826 a c) (@lem5178884 a c)). Qed.
Lemma lem5178886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5178887 (b : real) (c : real) : (term103 b c) = (term103 b c).
Proof. exact (MK_COMB (@lem5178886) (@lem5178825 b c)). Qed.
Lemma lem5178888 (b : real) (a : real) (c : real) : (term104 b a c) = (term104 b a c).
Proof. exact (MK_COMB (@lem5178887 b c) (@lem5178885 a c)). Qed.
Lemma lem5178889 (c : real) (b : real) : (term183 c b) = (term184 c b).
Proof. exact (@lem1988289 (term97 c b) term101). Qed.
Lemma lem5178890 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178903 (b : real) (c : real) : (term97 c b) = (term96 b c).
Proof. exact (@lem1982761 b (term98 c)). Qed.
Lemma lem5178904 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5178905 (b : real) (c : real) : (term185 c b) = (term186 b c).
Proof. exact (MK_COMB (@lem5178904) (@lem5178903 b c)). Qed.
Lemma lem5178906 (b : real) (c : real) : (term155 c b) = (term187 b c).
Proof. exact (MK_COMB (@lem5178905 b c) (@lem5178890)). Qed.
Lemma lem5178907 (b : real) (c : real) : (term187 b c) = (term188 b c).
Proof. exact (@lem1982792 (term96 b c) term101). Qed.
Lemma lem5178909 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5178910 : term101 = term158.
Proof. exact (@lem5178909 (NUMERAL 0)). Qed.
Lemma lem5178912 (x : nat) : (term159 x) = (term160 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5178913 : term161 = term162.
Proof. exact (@lem5178912 term163). Qed.
Lemma lem5178914 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5178915 : term164 = term165.
Proof. exact (MK_COMB (@lem5178914) (@lem5178913)). Qed.
Lemma lem5178916 : term166 = term167.
Proof. exact (MK_COMB (@lem5178915) (@lem5178910)). Qed.
Lemma lem5178917 : term167 = term168.
Proof. exact (@lem1981613 term161 term101 term169 term169). Qed.
Lemma lem5178919 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5178920 : term172 = term173.
Proof. exact (@lem5178919 term163 term163). Qed.
Lemma lem5178921 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5178922 : term175 = term163.
Proof. exact (EQ_MP (@lem5178921) (@lem940073)). Qed.
Lemma lem5178923 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5178924 : term173 = term169.
Proof. exact (MK_COMB (@lem5178923) (@lem5178922)). Qed.
Lemma lem5178925 : term172 = term169.
Proof. exact (TRANS (@lem5178920) (@lem5178924)). Qed.
Lemma lem5178927 (x : nat) : (term176 x) = term101.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5178928 : term166 = term101.
Proof. exact (@lem5178927 term163). Qed.
Lemma lem5178929 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5178930 : term177 = term178.
Proof. exact (MK_COMB (@lem5178929) (@lem5178928)). Qed.
Lemma lem5178931 : term168 = term158.
Proof. exact (MK_COMB (@lem5178930) (@lem5178925)). Qed.
Lemma lem5178932 : term167 = term158.
Proof. exact (TRANS (@lem5178917) (@lem5178931)). Qed.
Lemma lem5178933 : term166 = term158.
Proof. exact (TRANS (@lem5178916) (@lem5178932)). Qed.
Lemma lem5178935 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5178936 : term158 = term101.
Proof. exact (@lem5178935 term101). Qed.
Lemma lem5178937 : term166 = term101.
Proof. exact (TRANS (@lem5178933) (@lem5178936)). Qed.
Lemma lem5178938 (b : real) (c : real) : (term189 b c) = (term189 b c).
Proof. exact (eq_refl (term189 b c)). Qed.
Lemma lem5178939 (b : real) (c : real) : (term188 b c) = (term190 b c).
Proof. exact (MK_COMB (@lem5178938 b c) (@lem5178937)). Qed.
Lemma lem5178940 (b : real) (c : real) : (term190 b c) = (term96 b c).
Proof. exact (@lem1982723 (term96 b c)). Qed.
Lemma lem5178941 (b : real) (c : real) : (term188 b c) = (term96 b c).
Proof. exact (TRANS (@lem5178939 b c) (@lem5178940 b c)). Qed.
Lemma lem5178942 (b : real) (c : real) : (term187 b c) = (term96 b c).
Proof. exact (TRANS (@lem5178907 b c) (@lem5178941 b c)). Qed.
Lemma lem5178943 (b : real) (c : real) : (term155 c b) = (term96 b c).
Proof. exact (TRANS (@lem5178906 b c) (@lem5178942 b c)). Qed.
Lemma lem5178944 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5178945 (b : real) (c : real) : (term191 c b) = (term120 b c).
Proof. exact (MK_COMB (@lem5178944) (@lem5178943 b c)). Qed.
Lemma lem5178946 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178947 (b : real) (c : real) : (term184 c b) = (term121 b c).
Proof. exact (MK_COMB (@lem5178945 b c) (@lem5178946)). Qed.
Lemma lem5178948 (b : real) (c : real) : (term183 c b) = (term121 b c).
Proof. exact (TRANS (@lem5178889 c b) (@lem5178947 b c)). Qed.
Lemma lem5178949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5178950 (b : real) (a : real) (c : real) : (term114 b a c) = (term114 b a c).
Proof. exact (MK_COMB (@lem5178949) (@lem5178888 b a c)). Qed.
Lemma lem5178951 (a : real) (b : real) (c : real) : (term146 a c b) = (term192 a b c).
Proof. exact (MK_COMB (@lem5178950 b a c) (@lem5178948 b c)). Qed.
Lemma lem5178952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5178953 (a : real) (b : real) : (term147 b a) = (term103 a b).
Proof. exact (MK_COMB (@lem5178952) (@lem5178765 a b)). Qed.
Lemma lem5178954 (a : real) (b : real) (c : real) : (term149 a c b) = (term193 a b c).
Proof. exact (MK_COMB (@lem5178953 a b) (@lem5178951 a b c)). Qed.
Lemma lem5178955 (a : real) (b : real) : (real_gt a b) = (term118 a b).
Proof. exact (@lem1988289 a b). Qed.
Lemma lem5178968 (a : real) (b : real) : (real_sub a b) = (term96 a b).
Proof. exact (@lem1982792 a b). Qed.
Lemma lem5178969 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5178970 (a : real) (b : real) : (term119 a b) = (term120 a b).
Proof. exact (MK_COMB (@lem5178969) (@lem5178968 a b)). Qed.
Lemma lem5178971 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178972 (a : real) (b : real) : (term118 a b) = (term121 a b).
Proof. exact (MK_COMB (@lem5178970 a b) (@lem5178971)). Qed.
Lemma lem5178973 (a : real) (b : real) : (real_gt a b) = (term121 a b).
Proof. exact (TRANS (@lem5178955 a b) (@lem5178972 a b)). Qed.
Lemma lem5178974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5178975 (b : real) (c : real) : (term103 b c) = (term103 b c).
Proof. exact (MK_COMB (@lem5178974) (@lem5178825 b c)). Qed.
Lemma lem5178976 (b : real) (a : real) (c : real) : (term104 b a c) = (term104 b a c).
Proof. exact (MK_COMB (@lem5178975 b c) (@lem5178885 a c)). Qed.
Lemma lem5178977 (c : real) (a : real) : (term183 c a) = (term184 c a).
Proof. exact (@lem1988289 (term97 c a) term101). Qed.
Lemma lem5178978 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5178991 (a : real) (c : real) : (term97 c a) = (term96 a c).
Proof. exact (@lem1982761 a (term98 c)). Qed.
Lemma lem5178992 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5178993 (a : real) (c : real) : (term185 c a) = (term186 a c).
Proof. exact (MK_COMB (@lem5178992) (@lem5178991 a c)). Qed.
Lemma lem5178994 (a : real) (c : real) : (term155 c a) = (term187 a c).
Proof. exact (MK_COMB (@lem5178993 a c) (@lem5178978)). Qed.
Lemma lem5178995 (a : real) (c : real) : (term187 a c) = (term188 a c).
Proof. exact (@lem1982792 (term96 a c) term101). Qed.
Lemma lem5178997 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5178998 : term101 = term158.
Proof. exact (@lem5178997 (NUMERAL 0)). Qed.
Lemma lem5179000 (x : nat) : (term159 x) = (term160 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5179001 : term161 = term162.
Proof. exact (@lem5179000 term163). Qed.
Lemma lem5179002 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5179003 : term164 = term165.
Proof. exact (MK_COMB (@lem5179002) (@lem5179001)). Qed.
Lemma lem5179004 : term166 = term167.
Proof. exact (MK_COMB (@lem5179003) (@lem5178998)). Qed.
Lemma lem5179005 : term167 = term168.
Proof. exact (@lem1981613 term161 term101 term169 term169). Qed.
Lemma lem5179007 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179008 : term172 = term173.
Proof. exact (@lem5179007 term163 term163). Qed.
Lemma lem5179009 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179010 : term175 = term163.
Proof. exact (EQ_MP (@lem5179009) (@lem940073)). Qed.
Lemma lem5179011 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179012 : term173 = term169.
Proof. exact (MK_COMB (@lem5179011) (@lem5179010)). Qed.
Lemma lem5179013 : term172 = term169.
Proof. exact (TRANS (@lem5179008) (@lem5179012)). Qed.
Lemma lem5179015 (x : nat) : (term176 x) = term101.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5179016 : term166 = term101.
Proof. exact (@lem5179015 term163). Qed.
Lemma lem5179017 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5179018 : term177 = term178.
Proof. exact (MK_COMB (@lem5179017) (@lem5179016)). Qed.
Lemma lem5179019 : term168 = term158.
Proof. exact (MK_COMB (@lem5179018) (@lem5179013)). Qed.
Lemma lem5179020 : term167 = term158.
Proof. exact (TRANS (@lem5179005) (@lem5179019)). Qed.
Lemma lem5179021 : term166 = term158.
Proof. exact (TRANS (@lem5179004) (@lem5179020)). Qed.
Lemma lem5179023 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5179024 : term158 = term101.
Proof. exact (@lem5179023 term101). Qed.
Lemma lem5179025 : term166 = term101.
Proof. exact (TRANS (@lem5179021) (@lem5179024)). Qed.
Lemma lem5179026 (a : real) (c : real) : (term189 a c) = (term189 a c).
Proof. exact (eq_refl (term189 a c)). Qed.
Lemma lem5179027 (a : real) (c : real) : (term188 a c) = (term190 a c).
Proof. exact (MK_COMB (@lem5179026 a c) (@lem5179025)). Qed.
Lemma lem5179028 (a : real) (c : real) : (term190 a c) = (term96 a c).
Proof. exact (@lem1982723 (term96 a c)). Qed.
Lemma lem5179029 (a : real) (c : real) : (term188 a c) = (term96 a c).
Proof. exact (TRANS (@lem5179027 a c) (@lem5179028 a c)). Qed.
Lemma lem5179030 (a : real) (c : real) : (term187 a c) = (term96 a c).
Proof. exact (TRANS (@lem5178995 a c) (@lem5179029 a c)). Qed.
Lemma lem5179031 (a : real) (c : real) : (term155 c a) = (term96 a c).
Proof. exact (TRANS (@lem5178994 a c) (@lem5179030 a c)). Qed.
Lemma lem5179032 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5179033 (a : real) (c : real) : (term191 c a) = (term120 a c).
Proof. exact (MK_COMB (@lem5179032) (@lem5179031 a c)). Qed.
Lemma lem5179034 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5179035 (a : real) (c : real) : (term184 c a) = (term121 a c).
Proof. exact (MK_COMB (@lem5179033 a c) (@lem5179034)). Qed.
Lemma lem5179036 (a : real) (c : real) : (term183 c a) = (term121 a c).
Proof. exact (TRANS (@lem5178977 c a) (@lem5179035 a c)). Qed.
Lemma lem5179037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5179038 (b : real) (a : real) (c : real) : (term114 b a c) = (term114 b a c).
Proof. exact (MK_COMB (@lem5179037) (@lem5178976 b a c)). Qed.
Lemma lem5179039 (b : real) (a : real) (c : real) : (term141 b c a) = (term194 b a c).
Proof. exact (MK_COMB (@lem5179038 b a c) (@lem5179036 a c)). Qed.
Lemma lem5179040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5179041 (a : real) (b : real) : (term142 a b) = (term195 a b).
Proof. exact (MK_COMB (@lem5179040) (@lem5178973 a b)). Qed.
Lemma lem5179042 (b : real) (a : real) (c : real) : (term144 b c a) = (term196 b a c).
Proof. exact (MK_COMB (@lem5179041 a b) (@lem5179039 b a c)). Qed.
Lemma lem5179043 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5179044 (a : real) (b : real) (c : real) : (term151 a c b) = (term197 a b c).
Proof. exact (MK_COMB (@lem5179043) (@lem5178954 a b c)). Qed.
Lemma lem5179045 (b : real) (a : real) (c : real) : (term152 b c a) = (term198 b a c).
Proof. exact (MK_COMB (@lem5179044 a b c) (@lem5179042 b a c)). Qed.
Lemma lem5179057 (b : real) (a : real) (c : real) : (term116 c a b) = (term198 b a c).
Proof. exact (TRANS (@lem5178746 b c a) (@lem5179045 b a c)). Qed.
Lemma lem5179059 (x : real) (a : real) (y : real) (r : real) : (term199 a x y r) = (term200 x a y r).
Proof. exact (proj1 (@lem1482686 x a (@el real) y (@el real) r)). Qed.
Lemma lem5179060 (a : real) (c : real) (b : real) : (term130 c a b) = (term201 a c b).
Proof. exact (@lem5179059 a c b term101). Qed.
Lemma lem5179073 (b : real) (c : real) : (term96 c b) = (term97 b c).
Proof. exact (@lem1982761 (term98 b) c). Qed.
Lemma lem5179074 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5179075 (b : real) (c : real) : (term202 c b) = (term100 b c).
Proof. exact (MK_COMB (@lem5179074) (@lem5179073 b c)). Qed.
Lemma lem5179076 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5179077 (b : real) (c : real) : (term203 c b) = (term102 b c).
Proof. exact (MK_COMB (@lem5179075 b c) (@lem5179076)). Qed.
Lemma lem5179090 (a : real) (c : real) : (term96 c a) = (term97 a c).
Proof. exact (@lem1982761 (term98 a) c). Qed.
Lemma lem5179091 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5179092 (a : real) (c : real) : (term202 c a) = (term100 a c).
Proof. exact (MK_COMB (@lem5179091) (@lem5179090 a c)). Qed.
Lemma lem5179093 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5179094 (a : real) (c : real) : (term203 c a) = (term102 a c).
Proof. exact (MK_COMB (@lem5179092 a c) (@lem5179093)). Qed.
Lemma lem5179095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5179096 (a : real) (c : real) : (term204 c a) = (term103 a c).
Proof. exact (MK_COMB (@lem5179095) (@lem5179094 a c)). Qed.
Lemma lem5179097 (a : real) (b : real) (c : real) : (term201 a c b) = (term104 a b c).
Proof. exact (MK_COMB (@lem5179096 a c) (@lem5179077 b c)). Qed.
Lemma lem5179098 (a : real) (b : real) (c : real) : (term130 c a b) = (term104 a b c).
Proof. exact (TRANS (@lem5179060 a c b) (@lem5179097 a b c)). Qed.
Lemma lem5179099 (b : real) (c : real) : (term195 b c) = (term195 b c).
Proof. exact (eq_refl (term195 b c)). Qed.
Lemma lem5179102 (a : real) (b : real) (c : real) : (term205 c a b) = (term206 a b c).
Proof. exact (MK_COMB (@lem5179099 b c) (@lem5179098 a b c)). Qed.
Lemma lem5179104 (x : real) (a : real) (y : real) (r : real) : (term199 a x y r) = (term200 x a y r).
Proof. exact (proj1 (@lem1482686 x a (@el real) y (@el real) r)). Qed.
Lemma lem5179105 (a : real) (c : real) (b : real) : (term130 c a b) = (term201 a c b).
Proof. exact (@lem5179104 a c b term101). Qed.
Lemma lem5179118 (b : real) (c : real) : (term96 c b) = (term97 b c).
Proof. exact (@lem1982761 (term98 b) c). Qed.
Lemma lem5179119 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5179120 (b : real) (c : real) : (term202 c b) = (term100 b c).
Proof. exact (MK_COMB (@lem5179119) (@lem5179118 b c)). Qed.
Lemma lem5179121 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5179122 (b : real) (c : real) : (term203 c b) = (term102 b c).
Proof. exact (MK_COMB (@lem5179120 b c) (@lem5179121)). Qed.
Lemma lem5179135 (a : real) (c : real) : (term96 c a) = (term97 a c).
Proof. exact (@lem1982761 (term98 a) c). Qed.
Lemma lem5179136 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5179137 (a : real) (c : real) : (term202 c a) = (term100 a c).
Proof. exact (MK_COMB (@lem5179136) (@lem5179135 a c)). Qed.
Lemma lem5179138 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5179139 (a : real) (c : real) : (term203 c a) = (term102 a c).
Proof. exact (MK_COMB (@lem5179137 a c) (@lem5179138)). Qed.
Lemma lem5179140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5179141 (a : real) (c : real) : (term204 c a) = (term103 a c).
Proof. exact (MK_COMB (@lem5179140) (@lem5179139 a c)). Qed.
Lemma lem5179142 (a : real) (b : real) (c : real) : (term201 a c b) = (term104 a b c).
Proof. exact (MK_COMB (@lem5179141 a c) (@lem5179122 b c)). Qed.
Lemma lem5179143 (a : real) (b : real) (c : real) : (term130 c a b) = (term104 a b c).
Proof. exact (TRANS (@lem5179105 a c b) (@lem5179142 a b c)). Qed.
Lemma lem5179144 (a : real) (c : real) : (term195 a c) = (term195 a c).
Proof. exact (eq_refl (term195 a c)). Qed.
Lemma lem5179147 (a : real) (b : real) (c : real) : (term207 c a b) = (term208 a b c).
Proof. exact (MK_COMB (@lem5179144 a c) (@lem5179143 a b c)). Qed.
Lemma lem5179148 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5179149 (a : real) (b : real) (c : real) : (term209 c a b) = (term210 a b c).
Proof. exact (MK_COMB (@lem5179148) (@lem5179102 a b c)). Qed.
Lemma lem5179150 (a : real) (b : real) (c : real) : (term135 c a b) = (term211 a b c).
Proof. exact (MK_COMB (@lem5179149 a b c) (@lem5179147 a b c)). Qed.
Lemma lem5179151 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5179152 (b : real) (a : real) (c : real) : (term133 c a b) = (term212 b a c).
Proof. exact (MK_COMB (@lem5179151) (@lem5179057 b a c)). Qed.
Lemma lem5179153 (a : real) (b : real) (c : real) : (term136 c a b) = (term213 a b c).
Proof. exact (MK_COMB (@lem5179152 b a c) (@lem5179150 a b c)). Qed.
Lemma lem5179154 (a : real) (b : real) (c : real) (h1 : term213 a b c) : term213 a b c.
Proof. exact (h1). Qed.
Lemma lem5179155 (b : real) (a : real) (c : real) (h1 : term198 b a c) : term198 b a c.
Proof. exact (h1). Qed.
Lemma lem5179156 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term193 a b c.
Proof. exact (h1). Qed.
Lemma lem5179157 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term192 a b c.
Proof. exact (proj2 (@lem5179156 a b c h1)). Qed.
Lemma lem5179159 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term121 b c.
Proof. exact (proj2 (@lem5179157 a b c h1)). Qed.
Lemma lem5179160 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term104 b a c.
Proof. exact (proj1 (@lem5179157 a b c h1)). Qed.
Lemma lem5179162 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term102 b c.
Proof. exact (proj1 (@lem5179160 a b c h1)). Qed.
Lemma lem5179164 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5179165 : term214 = term215.
Proof. exact (@lem5179164 term101 term169). Qed.
Lemma lem5179167 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179168 : term169 = term216.
Proof. exact (@lem5179167 term163). Qed.
Lemma lem5179170 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179171 : term101 = term158.
Proof. exact (@lem5179170 (NUMERAL 0)). Qed.
Lemma lem5179172 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5179173 : term217 = term218.
Proof. exact (MK_COMB (@lem5179172) (@lem5179171)). Qed.
Lemma lem5179174 : term215 = term219.
Proof. exact (MK_COMB (@lem5179173) (@lem5179168)). Qed.
Lemma lem5179175 : term220.
Proof. exact (@lem1980255 term101 term169 term169 term169). Qed.
Lemma lem5179177 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179178 : term215 = term222.
Proof. exact (@lem5179177 (NUMERAL 0) term163). Qed.
Lemma lem5179179 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179180 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179181 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179180 h1) (fun h1 : term222 = True => @lem5179179)). Qed.
Lemma lem5179182 : term222 = True.
Proof. exact (EQ_MP (@lem5179181) (@lem5179179)). Qed.
Lemma lem5179183 : term215 = True.
Proof. exact (TRANS (@lem5179178) (@lem5179182)). Qed.
Lemma lem5179184 : True = term215.
Proof. exact (SYM (@lem5179183)). Qed.
Lemma lem5179185 : term215.
Proof. exact (EQ_MP (@lem5179184) (@lem0)). Qed.
Lemma lem5179186 : term224.
Proof. exact (@lem5179175 (@lem5179185)). Qed.
Lemma lem5179188 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179189 : term215 = term222.
Proof. exact (@lem5179188 (NUMERAL 0) term163). Qed.
Lemma lem5179190 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179191 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179192 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179191 h1) (fun h1 : term222 = True => @lem5179190)). Qed.
Lemma lem5179193 : term222 = True.
Proof. exact (EQ_MP (@lem5179192) (@lem5179190)). Qed.
Lemma lem5179194 : term215 = True.
Proof. exact (TRANS (@lem5179189) (@lem5179193)). Qed.
Lemma lem5179195 : True = term215.
Proof. exact (SYM (@lem5179194)). Qed.
Lemma lem5179196 : term215.
Proof. exact (EQ_MP (@lem5179195) (@lem0)). Qed.
Lemma lem5179197 : term219 = term225.
Proof. exact (@lem5179186 (@lem5179196)). Qed.
Lemma lem5179199 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179200 : term172 = term173.
Proof. exact (@lem5179199 term163 term163). Qed.
Lemma lem5179201 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179202 : term175 = term163.
Proof. exact (EQ_MP (@lem5179201) (@lem940073)). Qed.
Lemma lem5179203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179204 : term173 = term169.
Proof. exact (MK_COMB (@lem5179203) (@lem5179202)). Qed.
Lemma lem5179205 : term172 = term169.
Proof. exact (TRANS (@lem5179200) (@lem5179204)). Qed.
Lemma lem5179207 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179208 : term227 = term101.
Proof. exact (@lem5179207 term163). Qed.
Lemma lem5179209 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5179210 : term228 = term217.
Proof. exact (MK_COMB (@lem5179209) (@lem5179208)). Qed.
Lemma lem5179211 : term225 = term215.
Proof. exact (MK_COMB (@lem5179210) (@lem5179205)). Qed.
Lemma lem5179213 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179214 : term215 = term222.
Proof. exact (@lem5179213 (NUMERAL 0) term163). Qed.
Lemma lem5179215 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179216 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179217 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179216 h1) (fun h1 : term222 = True => @lem5179215)). Qed.
Lemma lem5179218 : term222 = True.
Proof. exact (EQ_MP (@lem5179217) (@lem5179215)). Qed.
Lemma lem5179219 : term215 = True.
Proof. exact (TRANS (@lem5179214) (@lem5179218)). Qed.
Lemma lem5179220 : term225 = True.
Proof. exact (TRANS (@lem5179211) (@lem5179219)). Qed.
Lemma lem5179221 : term219 = True.
Proof. exact (TRANS (@lem5179197) (@lem5179220)). Qed.
Lemma lem5179222 : term215 = True.
Proof. exact (TRANS (@lem5179174) (@lem5179221)). Qed.
Lemma lem5179223 : term214 = True.
Proof. exact (TRANS (@lem5179165) (@lem5179222)). Qed.
Lemma lem5179224 : True = term214.
Proof. exact (SYM (@lem5179223)). Qed.
Lemma lem5179225 : term214.
Proof. exact (EQ_MP (@lem5179224) (@lem0)). Qed.
Lemma lem5179226 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term229 b c.
Proof. exact (conj (@lem5179225) (@lem5179162 a b c h1)). Qed.
Lemma lem5179228 (x : real) (y : real) : term230 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5179229 (b : real) (c : real) : term231 b c.
Proof. exact (@lem5179228 term169 (term97 b c)). Qed.
Lemma lem5179230 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term232 b c.
Proof. exact (@lem5179229 b c (@lem5179226 a b c h1)). Qed.
Lemma lem5179231 (b : real) (c : real) : (term233 b c) = (term97 b c).
Proof. exact (@lem1982733 (term97 b c)). Qed.
Lemma lem5179232 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5179233 (b : real) (c : real) : (term234 b c) = (term100 b c).
Proof. exact (MK_COMB (@lem5179232) (@lem5179231 b c)). Qed.
Lemma lem5179234 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5179235 (b : real) (c : real) : (term232 b c) = (term102 b c).
Proof. exact (MK_COMB (@lem5179233 b c) (@lem5179234)). Qed.
Lemma lem5179236 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term102 b c.
Proof. exact (EQ_MP (@lem5179235 b c) (@lem5179230 a b c h1)). Qed.
Lemma lem5179238 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5179239 : term214 = term215.
Proof. exact (@lem5179238 term101 term169). Qed.
Lemma lem5179241 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179242 : term169 = term216.
Proof. exact (@lem5179241 term163). Qed.
Lemma lem5179244 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179245 : term101 = term158.
Proof. exact (@lem5179244 (NUMERAL 0)). Qed.
Lemma lem5179246 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5179247 : term217 = term218.
Proof. exact (MK_COMB (@lem5179246) (@lem5179245)). Qed.
Lemma lem5179248 : term215 = term219.
Proof. exact (MK_COMB (@lem5179247) (@lem5179242)). Qed.
Lemma lem5179249 : term220.
Proof. exact (@lem1980255 term101 term169 term169 term169). Qed.
Lemma lem5179251 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179252 : term215 = term222.
Proof. exact (@lem5179251 (NUMERAL 0) term163). Qed.
Lemma lem5179253 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179254 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179255 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179254 h1) (fun h1 : term222 = True => @lem5179253)). Qed.
Lemma lem5179256 : term222 = True.
Proof. exact (EQ_MP (@lem5179255) (@lem5179253)). Qed.
Lemma lem5179257 : term215 = True.
Proof. exact (TRANS (@lem5179252) (@lem5179256)). Qed.
Lemma lem5179258 : True = term215.
Proof. exact (SYM (@lem5179257)). Qed.
Lemma lem5179259 : term215.
Proof. exact (EQ_MP (@lem5179258) (@lem0)). Qed.
Lemma lem5179260 : term224.
Proof. exact (@lem5179249 (@lem5179259)). Qed.
Lemma lem5179262 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179263 : term215 = term222.
Proof. exact (@lem5179262 (NUMERAL 0) term163). Qed.
Lemma lem5179264 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179265 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179266 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179265 h1) (fun h1 : term222 = True => @lem5179264)). Qed.
Lemma lem5179267 : term222 = True.
Proof. exact (EQ_MP (@lem5179266) (@lem5179264)). Qed.
Lemma lem5179268 : term215 = True.
Proof. exact (TRANS (@lem5179263) (@lem5179267)). Qed.
Lemma lem5179269 : True = term215.
Proof. exact (SYM (@lem5179268)). Qed.
Lemma lem5179270 : term215.
Proof. exact (EQ_MP (@lem5179269) (@lem0)). Qed.
Lemma lem5179271 : term219 = term225.
Proof. exact (@lem5179260 (@lem5179270)). Qed.
Lemma lem5179273 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179274 : term172 = term173.
Proof. exact (@lem5179273 term163 term163). Qed.
Lemma lem5179275 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179276 : term175 = term163.
Proof. exact (EQ_MP (@lem5179275) (@lem940073)). Qed.
Lemma lem5179277 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179278 : term173 = term169.
Proof. exact (MK_COMB (@lem5179277) (@lem5179276)). Qed.
Lemma lem5179279 : term172 = term169.
Proof. exact (TRANS (@lem5179274) (@lem5179278)). Qed.
Lemma lem5179281 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179282 : term227 = term101.
Proof. exact (@lem5179281 term163). Qed.
Lemma lem5179283 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5179284 : term228 = term217.
Proof. exact (MK_COMB (@lem5179283) (@lem5179282)). Qed.
Lemma lem5179285 : term225 = term215.
Proof. exact (MK_COMB (@lem5179284) (@lem5179279)). Qed.
Lemma lem5179287 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179288 : term215 = term222.
Proof. exact (@lem5179287 (NUMERAL 0) term163). Qed.
Lemma lem5179289 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179290 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179291 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179290 h1) (fun h1 : term222 = True => @lem5179289)). Qed.
Lemma lem5179292 : term222 = True.
Proof. exact (EQ_MP (@lem5179291) (@lem5179289)). Qed.
Lemma lem5179293 : term215 = True.
Proof. exact (TRANS (@lem5179288) (@lem5179292)). Qed.
Lemma lem5179294 : term225 = True.
Proof. exact (TRANS (@lem5179285) (@lem5179293)). Qed.
Lemma lem5179295 : term219 = True.
Proof. exact (TRANS (@lem5179271) (@lem5179294)). Qed.
Lemma lem5179296 : term215 = True.
Proof. exact (TRANS (@lem5179248) (@lem5179295)). Qed.
Lemma lem5179297 : term214 = True.
Proof. exact (TRANS (@lem5179239) (@lem5179296)). Qed.
Lemma lem5179298 : True = term214.
Proof. exact (SYM (@lem5179297)). Qed.
Lemma lem5179299 : term214.
Proof. exact (EQ_MP (@lem5179298) (@lem0)). Qed.
Lemma lem5179300 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term235 b c.
Proof. exact (conj (@lem5179299) (@lem5179159 a b c h1)). Qed.
Lemma lem5179302 (x : real) (y : real) : term236 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5179303 (b : real) (c : real) : term237 b c.
Proof. exact (@lem5179302 term169 (term96 b c)). Qed.
Lemma lem5179304 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term238 b c.
Proof. exact (@lem5179303 b c (@lem5179300 a b c h1)). Qed.
Lemma lem5179305 (b : real) (c : real) : (term239 b c) = (term96 b c).
Proof. exact (@lem1982733 (term96 b c)). Qed.
Lemma lem5179306 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5179307 (b : real) (c : real) : (term240 b c) = (term120 b c).
Proof. exact (MK_COMB (@lem5179306) (@lem5179305 b c)). Qed.
Lemma lem5179308 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5179309 (b : real) (c : real) : (term238 b c) = (term121 b c).
Proof. exact (MK_COMB (@lem5179307 b c) (@lem5179308)). Qed.
Lemma lem5179310 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term121 b c.
Proof. exact (EQ_MP (@lem5179309 b c) (@lem5179304 a b c h1)). Qed.
Lemma lem5179311 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term241 b c.
Proof. exact (conj (@lem5179310 a b c h1) (@lem5179236 a b c h1)). Qed.
Lemma lem5179313 (x : real) (y : real) : term242 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5179314 (b : real) (c : real) : term243 b c.
Proof. exact (@lem5179313 (term96 b c) (term97 b c)). Qed.
Lemma lem5179315 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term244 b c.
Proof. exact (@lem5179314 b c (@lem5179311 a b c h1)). Qed.
Lemma lem5179316 (b : real) (c : real) : (term245 b c) = (term246 b c).
Proof. exact (@lem1982753 b (term98 b) (term98 c) c). Qed.
Lemma lem5179317 (b : real) : (term247 b) = (term248 b).
Proof. exact (@lem1982715 term161 b). Qed.
Lemma lem5179319 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179320 : term169 = term216.
Proof. exact (@lem5179319 term163). Qed.
Lemma lem5179322 (x : nat) : (term159 x) = (term160 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5179323 : term161 = term162.
Proof. exact (@lem5179322 term163). Qed.
Lemma lem5179324 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5179325 : term249 = term250.
Proof. exact (MK_COMB (@lem5179324) (@lem5179323)). Qed.
Lemma lem5179326 : term251 = term252.
Proof. exact (MK_COMB (@lem5179325) (@lem5179320)). Qed.
Lemma lem5179327 : term253.
Proof. exact (@lem1981473 term161 term169 term169 term169 term101 term169). Qed.
Lemma lem5179329 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179330 : term215 = term222.
Proof. exact (@lem5179329 (NUMERAL 0) term163). Qed.
Lemma lem5179331 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179332 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179333 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179332 h1) (fun h1 : term222 = True => @lem5179331)). Qed.
Lemma lem5179334 : term222 = True.
Proof. exact (EQ_MP (@lem5179333) (@lem5179331)). Qed.
Lemma lem5179335 : term215 = True.
Proof. exact (TRANS (@lem5179330) (@lem5179334)). Qed.
Lemma lem5179336 : True = term215.
Proof. exact (SYM (@lem5179335)). Qed.
Lemma lem5179337 : term215.
Proof. exact (EQ_MP (@lem5179336) (@lem0)). Qed.
Lemma lem5179338 : term254.
Proof. exact (@lem5179327 (@lem5179337)). Qed.
Lemma lem5179340 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179341 : term215 = term222.
Proof. exact (@lem5179340 (NUMERAL 0) term163). Qed.
Lemma lem5179342 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179343 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179344 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179343 h1) (fun h1 : term222 = True => @lem5179342)). Qed.
Lemma lem5179345 : term222 = True.
Proof. exact (EQ_MP (@lem5179344) (@lem5179342)). Qed.
Lemma lem5179346 : term215 = True.
Proof. exact (TRANS (@lem5179341) (@lem5179345)). Qed.
Lemma lem5179347 : True = term215.
Proof. exact (SYM (@lem5179346)). Qed.
Lemma lem5179348 : term215.
Proof. exact (EQ_MP (@lem5179347) (@lem0)). Qed.
Lemma lem5179349 : term255.
Proof. exact (@lem5179338 (@lem5179348)). Qed.
Lemma lem5179351 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179352 : term215 = term222.
Proof. exact (@lem5179351 (NUMERAL 0) term163). Qed.
Lemma lem5179353 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179354 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179355 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179354 h1) (fun h1 : term222 = True => @lem5179353)). Qed.
Lemma lem5179356 : term222 = True.
Proof. exact (EQ_MP (@lem5179355) (@lem5179353)). Qed.
Lemma lem5179357 : term215 = True.
Proof. exact (TRANS (@lem5179352) (@lem5179356)). Qed.
Lemma lem5179358 : True = term215.
Proof. exact (SYM (@lem5179357)). Qed.
Lemma lem5179359 : term215.
Proof. exact (EQ_MP (@lem5179358) (@lem0)). Qed.
Lemma lem5179360 : term256.
Proof. exact (@lem5179349 (@lem5179359)). Qed.
Lemma lem5179362 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179363 : term172 = term173.
Proof. exact (@lem5179362 term163 term163). Qed.
Lemma lem5179364 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179365 : term175 = term163.
Proof. exact (EQ_MP (@lem5179364) (@lem940073)). Qed.
Lemma lem5179366 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179367 : term173 = term169.
Proof. exact (MK_COMB (@lem5179366) (@lem5179365)). Qed.
Lemma lem5179368 : term172 = term169.
Proof. exact (TRANS (@lem5179363) (@lem5179367)). Qed.
Lemma lem5179370 (m : nat) (n : nat) : (term257 m n) = (term258 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5179371 : term259 = term260.
Proof. exact (@lem5179370 term163 term163). Qed.
Lemma lem5179372 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179373 : term175 = term163.
Proof. exact (EQ_MP (@lem5179372) (@lem940073)). Qed.
Lemma lem5179374 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179375 : term173 = term169.
Proof. exact (MK_COMB (@lem5179374) (@lem5179373)). Qed.
Lemma lem5179376 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5179377 : term260 = term161.
Proof. exact (MK_COMB (@lem5179376) (@lem5179375)). Qed.
Lemma lem5179378 : term259 = term161.
Proof. exact (TRANS (@lem5179371) (@lem5179377)). Qed.
Lemma lem5179379 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5179380 : term261 = term249.
Proof. exact (MK_COMB (@lem5179379) (@lem5179378)). Qed.
Lemma lem5179381 : term262 = term251.
Proof. exact (MK_COMB (@lem5179380) (@lem5179368)). Qed.
Lemma lem5179383 (m : nat) : (term263 m) = term101.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5179384 : term251 = term101.
Proof. exact (@lem5179383 term163). Qed.
Lemma lem5179385 : term262 = term101.
Proof. exact (TRANS (@lem5179381) (@lem5179384)). Qed.
Lemma lem5179386 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5179387 : term264 = term265.
Proof. exact (MK_COMB (@lem5179386) (@lem5179385)). Qed.
Lemma lem5179388 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem5179389 : term266 = term227.
Proof. exact (MK_COMB (@lem5179387) (@lem5179388)). Qed.
Lemma lem5179391 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179392 : term227 = term101.
Proof. exact (@lem5179391 term163). Qed.
Lemma lem5179393 : term266 = term101.
Proof. exact (TRANS (@lem5179389) (@lem5179392)). Qed.
Lemma lem5179395 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179396 : term172 = term173.
Proof. exact (@lem5179395 term163 term163). Qed.
Lemma lem5179397 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179398 : term175 = term163.
Proof. exact (EQ_MP (@lem5179397) (@lem940073)). Qed.
Lemma lem5179399 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179400 : term173 = term169.
Proof. exact (MK_COMB (@lem5179399) (@lem5179398)). Qed.
Lemma lem5179401 : term172 = term169.
Proof. exact (TRANS (@lem5179396) (@lem5179400)). Qed.
Lemma lem5179402 : term265 = term265.
Proof. exact (eq_refl term265). Qed.
Lemma lem5179403 : term267 = term227.
Proof. exact (MK_COMB (@lem5179402) (@lem5179401)). Qed.
Lemma lem5179405 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179406 : term227 = term101.
Proof. exact (@lem5179405 term163). Qed.
Lemma lem5179407 : term267 = term101.
Proof. exact (TRANS (@lem5179403) (@lem5179406)). Qed.
Lemma lem5179408 : term101 = term267.
Proof. exact (SYM (@lem5179407)). Qed.
Lemma lem5179409 : term266 = term267.
Proof. exact (TRANS (@lem5179393) (@lem5179408)). Qed.
Lemma lem5179410 : term252 = term158.
Proof. exact (@lem5179360 (@lem5179409)). Qed.
Lemma lem5179411 : term251 = term158.
Proof. exact (TRANS (@lem5179326) (@lem5179410)). Qed.
Lemma lem5179413 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5179414 : term158 = term101.
Proof. exact (@lem5179413 term101). Qed.
Lemma lem5179415 : term251 = term101.
Proof. exact (TRANS (@lem5179411) (@lem5179414)). Qed.
Lemma lem5179416 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5179417 : term268 = term265.
Proof. exact (MK_COMB (@lem5179416) (@lem5179415)). Qed.
Lemma lem5179418 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5179419 (b : real) : (term248 b) = (term269 b).
Proof. exact (MK_COMB (@lem5179417) (@lem5179418 b)). Qed.
Lemma lem5179420 (b : real) : (term247 b) = (term269 b).
Proof. exact (TRANS (@lem5179317 b) (@lem5179419 b)). Qed.
Lemma lem5179421 (b : real) : (term269 b) = term101.
Proof. exact (@lem1982719 b). Qed.
Lemma lem5179422 (b : real) : (term247 b) = term101.
Proof. exact (TRANS (@lem5179420 b) (@lem5179421 b)). Qed.
Lemma lem5179423 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5179424 (b : real) : (term270 b) = term271.
Proof. exact (MK_COMB (@lem5179423) (@lem5179422 b)). Qed.
Lemma lem5179425 (c : real) : (term272 c) = (term248 c).
Proof. exact (@lem1982713 term161 c). Qed.
Lemma lem5179427 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179428 : term169 = term216.
Proof. exact (@lem5179427 term163). Qed.
Lemma lem5179430 (x : nat) : (term159 x) = (term160 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5179431 : term161 = term162.
Proof. exact (@lem5179430 term163). Qed.
Lemma lem5179432 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5179433 : term249 = term250.
Proof. exact (MK_COMB (@lem5179432) (@lem5179431)). Qed.
Lemma lem5179434 : term251 = term252.
Proof. exact (MK_COMB (@lem5179433) (@lem5179428)). Qed.
Lemma lem5179435 : term253.
Proof. exact (@lem1981473 term161 term169 term169 term169 term101 term169). Qed.
Lemma lem5179437 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179438 : term215 = term222.
Proof. exact (@lem5179437 (NUMERAL 0) term163). Qed.
Lemma lem5179439 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179440 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179441 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179440 h1) (fun h1 : term222 = True => @lem5179439)). Qed.
Lemma lem5179442 : term222 = True.
Proof. exact (EQ_MP (@lem5179441) (@lem5179439)). Qed.
Lemma lem5179443 : term215 = True.
Proof. exact (TRANS (@lem5179438) (@lem5179442)). Qed.
Lemma lem5179444 : True = term215.
Proof. exact (SYM (@lem5179443)). Qed.
Lemma lem5179445 : term215.
Proof. exact (EQ_MP (@lem5179444) (@lem0)). Qed.
Lemma lem5179446 : term254.
Proof. exact (@lem5179435 (@lem5179445)). Qed.
Lemma lem5179448 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179449 : term215 = term222.
Proof. exact (@lem5179448 (NUMERAL 0) term163). Qed.
Lemma lem5179450 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179451 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179452 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179451 h1) (fun h1 : term222 = True => @lem5179450)). Qed.
Lemma lem5179453 : term222 = True.
Proof. exact (EQ_MP (@lem5179452) (@lem5179450)). Qed.
Lemma lem5179454 : term215 = True.
Proof. exact (TRANS (@lem5179449) (@lem5179453)). Qed.
Lemma lem5179455 : True = term215.
Proof. exact (SYM (@lem5179454)). Qed.
Lemma lem5179456 : term215.
Proof. exact (EQ_MP (@lem5179455) (@lem0)). Qed.
Lemma lem5179457 : term255.
Proof. exact (@lem5179446 (@lem5179456)). Qed.
Lemma lem5179459 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179460 : term215 = term222.
Proof. exact (@lem5179459 (NUMERAL 0) term163). Qed.
Lemma lem5179461 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179462 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179463 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179462 h1) (fun h1 : term222 = True => @lem5179461)). Qed.
Lemma lem5179464 : term222 = True.
Proof. exact (EQ_MP (@lem5179463) (@lem5179461)). Qed.
Lemma lem5179465 : term215 = True.
Proof. exact (TRANS (@lem5179460) (@lem5179464)). Qed.
Lemma lem5179466 : True = term215.
Proof. exact (SYM (@lem5179465)). Qed.
Lemma lem5179467 : term215.
Proof. exact (EQ_MP (@lem5179466) (@lem0)). Qed.
Lemma lem5179468 : term256.
Proof. exact (@lem5179457 (@lem5179467)). Qed.
Lemma lem5179470 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179471 : term172 = term173.
Proof. exact (@lem5179470 term163 term163). Qed.
Lemma lem5179472 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179473 : term175 = term163.
Proof. exact (EQ_MP (@lem5179472) (@lem940073)). Qed.
Lemma lem5179474 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179475 : term173 = term169.
Proof. exact (MK_COMB (@lem5179474) (@lem5179473)). Qed.
Lemma lem5179476 : term172 = term169.
Proof. exact (TRANS (@lem5179471) (@lem5179475)). Qed.
Lemma lem5179478 (m : nat) (n : nat) : (term257 m n) = (term258 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5179479 : term259 = term260.
Proof. exact (@lem5179478 term163 term163). Qed.
Lemma lem5179480 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179481 : term175 = term163.
Proof. exact (EQ_MP (@lem5179480) (@lem940073)). Qed.
Lemma lem5179482 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179483 : term173 = term169.
Proof. exact (MK_COMB (@lem5179482) (@lem5179481)). Qed.
Lemma lem5179484 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5179485 : term260 = term161.
Proof. exact (MK_COMB (@lem5179484) (@lem5179483)). Qed.
Lemma lem5179486 : term259 = term161.
Proof. exact (TRANS (@lem5179479) (@lem5179485)). Qed.
Lemma lem5179487 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5179488 : term261 = term249.
Proof. exact (MK_COMB (@lem5179487) (@lem5179486)). Qed.
Lemma lem5179489 : term262 = term251.
Proof. exact (MK_COMB (@lem5179488) (@lem5179476)). Qed.
Lemma lem5179491 (m : nat) : (term263 m) = term101.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5179492 : term251 = term101.
Proof. exact (@lem5179491 term163). Qed.
Lemma lem5179493 : term262 = term101.
Proof. exact (TRANS (@lem5179489) (@lem5179492)). Qed.
Lemma lem5179494 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5179495 : term264 = term265.
Proof. exact (MK_COMB (@lem5179494) (@lem5179493)). Qed.
Lemma lem5179496 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem5179497 : term266 = term227.
Proof. exact (MK_COMB (@lem5179495) (@lem5179496)). Qed.
Lemma lem5179499 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179500 : term227 = term101.
Proof. exact (@lem5179499 term163). Qed.
Lemma lem5179501 : term266 = term101.
Proof. exact (TRANS (@lem5179497) (@lem5179500)). Qed.
Lemma lem5179503 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179504 : term172 = term173.
Proof. exact (@lem5179503 term163 term163). Qed.
Lemma lem5179505 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179506 : term175 = term163.
Proof. exact (EQ_MP (@lem5179505) (@lem940073)). Qed.
Lemma lem5179507 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179508 : term173 = term169.
Proof. exact (MK_COMB (@lem5179507) (@lem5179506)). Qed.
Lemma lem5179509 : term172 = term169.
Proof. exact (TRANS (@lem5179504) (@lem5179508)). Qed.
Lemma lem5179510 : term265 = term265.
Proof. exact (eq_refl term265). Qed.
Lemma lem5179511 : term267 = term227.
Proof. exact (MK_COMB (@lem5179510) (@lem5179509)). Qed.
Lemma lem5179513 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179514 : term227 = term101.
Proof. exact (@lem5179513 term163). Qed.
Lemma lem5179515 : term267 = term101.
Proof. exact (TRANS (@lem5179511) (@lem5179514)). Qed.
Lemma lem5179516 : term101 = term267.
Proof. exact (SYM (@lem5179515)). Qed.
Lemma lem5179517 : term266 = term267.
Proof. exact (TRANS (@lem5179501) (@lem5179516)). Qed.
Lemma lem5179518 : term252 = term158.
Proof. exact (@lem5179468 (@lem5179517)). Qed.
Lemma lem5179519 : term251 = term158.
Proof. exact (TRANS (@lem5179434) (@lem5179518)). Qed.
Lemma lem5179521 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5179522 : term158 = term101.
Proof. exact (@lem5179521 term101). Qed.
Lemma lem5179523 : term251 = term101.
Proof. exact (TRANS (@lem5179519) (@lem5179522)). Qed.
Lemma lem5179524 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5179525 : term268 = term265.
Proof. exact (MK_COMB (@lem5179524) (@lem5179523)). Qed.
Lemma lem5179526 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5179527 (c : real) : (term248 c) = (term269 c).
Proof. exact (MK_COMB (@lem5179525) (@lem5179526 c)). Qed.
Lemma lem5179528 (c : real) : (term272 c) = (term269 c).
Proof. exact (TRANS (@lem5179425 c) (@lem5179527 c)). Qed.
Lemma lem5179529 (c : real) : (term269 c) = term101.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5179530 (c : real) : (term272 c) = term101.
Proof. exact (TRANS (@lem5179528 c) (@lem5179529 c)). Qed.
Lemma lem5179531 (b : real) (c : real) : (term246 b c) = term273.
Proof. exact (MK_COMB (@lem5179424 b) (@lem5179530 c)). Qed.
Lemma lem5179532 (b : real) (c : real) : (term245 b c) = term273.
Proof. exact (TRANS (@lem5179316 b c) (@lem5179531 b c)). Qed.
Lemma lem5179533 : term273 = term101.
Proof. exact (@lem1982721 term101). Qed.
Lemma lem5179534 (b : real) (c : real) : (term245 b c) = term101.
Proof. exact (TRANS (@lem5179532 b c) (@lem5179533)). Qed.
Lemma lem5179535 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5179536 (b : real) (c : real) : (term274 b c) = term275.
Proof. exact (MK_COMB (@lem5179535) (@lem5179534 b c)). Qed.
Lemma lem5179537 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5179538 (b : real) (c : real) : (term244 b c) = term276.
Proof. exact (MK_COMB (@lem5179536 b c) (@lem5179537)). Qed.
Lemma lem5179539 (a : real) (b : real) (c : real) (h1 : term193 a b c) : term276.
Proof. exact (EQ_MP (@lem5179538 b c) (@lem5179315 a b c h1)). Qed.
Lemma lem5179541 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5179542 : term276 = term277.
Proof. exact (@lem5179541 term101 term101). Qed.
Lemma lem5179544 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179545 : term101 = term158.
Proof. exact (@lem5179544 (NUMERAL 0)). Qed.
Lemma lem5179547 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179548 : term101 = term158.
Proof. exact (@lem5179547 (NUMERAL 0)). Qed.
Lemma lem5179549 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5179550 : term217 = term218.
Proof. exact (MK_COMB (@lem5179549) (@lem5179548)). Qed.
Lemma lem5179551 : term277 = term278.
Proof. exact (MK_COMB (@lem5179550) (@lem5179545)). Qed.
Lemma lem5179552 : term279.
Proof. exact (@lem1980255 term101 term169 term101 term169). Qed.
Lemma lem5179554 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179555 : term215 = term222.
Proof. exact (@lem5179554 (NUMERAL 0) term163). Qed.
Lemma lem5179556 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179557 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179558 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179557 h1) (fun h1 : term222 = True => @lem5179556)). Qed.
Lemma lem5179559 : term222 = True.
Proof. exact (EQ_MP (@lem5179558) (@lem5179556)). Qed.
Lemma lem5179560 : term215 = True.
Proof. exact (TRANS (@lem5179555) (@lem5179559)). Qed.
Lemma lem5179561 : True = term215.
Proof. exact (SYM (@lem5179560)). Qed.
Lemma lem5179562 : term215.
Proof. exact (EQ_MP (@lem5179561) (@lem0)). Qed.
Lemma lem5179563 : term280.
Proof. exact (@lem5179552 (@lem5179562)). Qed.
Lemma lem5179565 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179566 : term215 = term222.
Proof. exact (@lem5179565 (NUMERAL 0) term163). Qed.
Lemma lem5179567 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179568 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179569 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179568 h1) (fun h1 : term222 = True => @lem5179567)). Qed.
Lemma lem5179570 : term222 = True.
Proof. exact (EQ_MP (@lem5179569) (@lem5179567)). Qed.
Lemma lem5179571 : term215 = True.
Proof. exact (TRANS (@lem5179566) (@lem5179570)). Qed.
Lemma lem5179572 : True = term215.
Proof. exact (SYM (@lem5179571)). Qed.
Lemma lem5179573 : term215.
Proof. exact (EQ_MP (@lem5179572) (@lem0)). Qed.
Lemma lem5179574 : term278 = term281.
Proof. exact (@lem5179563 (@lem5179573)). Qed.
Lemma lem5179576 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179577 : term227 = term101.
Proof. exact (@lem5179576 term163). Qed.
Lemma lem5179579 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179580 : term227 = term101.
Proof. exact (@lem5179579 term163). Qed.
Lemma lem5179581 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5179582 : term228 = term217.
Proof. exact (MK_COMB (@lem5179581) (@lem5179580)). Qed.
Lemma lem5179583 : term281 = term277.
Proof. exact (MK_COMB (@lem5179582) (@lem5179577)). Qed.
Lemma lem5179585 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179586 : term277 = term282.
Proof. exact (@lem5179585 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5179587 : term282 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5179588 : term277 = False.
Proof. exact (TRANS (@lem5179586) (@lem5179587)). Qed.
Lemma lem5179589 : term281 = False.
Proof. exact (TRANS (@lem5179583) (@lem5179588)). Qed.
Lemma lem5179590 : term278 = False.
Proof. exact (TRANS (@lem5179574) (@lem5179589)). Qed.
Lemma lem5179591 : term277 = False.
Proof. exact (TRANS (@lem5179551) (@lem5179590)). Qed.
Lemma lem5179592 : term276 = False.
Proof. exact (TRANS (@lem5179542) (@lem5179591)). Qed.
Lemma lem5179593 (a : real) (b : real) (c : real) (h1 : term193 a b c) : False.
Proof. exact (EQ_MP (@lem5179592) (@lem5179539 a b c h1)). Qed.
Lemma lem5179594 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term196 b a c.
Proof. exact (h1). Qed.
Lemma lem5179595 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term194 b a c.
Proof. exact (proj2 (@lem5179594 b a c h1)). Qed.
Lemma lem5179597 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term121 a c.
Proof. exact (proj2 (@lem5179595 b a c h1)). Qed.
Lemma lem5179598 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term104 b a c.
Proof. exact (proj1 (@lem5179595 b a c h1)). Qed.
Lemma lem5179599 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term102 a c.
Proof. exact (proj2 (@lem5179598 b a c h1)). Qed.
Lemma lem5179602 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5179603 : term214 = term215.
Proof. exact (@lem5179602 term101 term169). Qed.
Lemma lem5179605 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179606 : term169 = term216.
Proof. exact (@lem5179605 term163). Qed.
Lemma lem5179608 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179609 : term101 = term158.
Proof. exact (@lem5179608 (NUMERAL 0)). Qed.
Lemma lem5179610 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5179611 : term217 = term218.
Proof. exact (MK_COMB (@lem5179610) (@lem5179609)). Qed.
Lemma lem5179612 : term215 = term219.
Proof. exact (MK_COMB (@lem5179611) (@lem5179606)). Qed.
Lemma lem5179613 : term220.
Proof. exact (@lem1980255 term101 term169 term169 term169). Qed.
Lemma lem5179615 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179616 : term215 = term222.
Proof. exact (@lem5179615 (NUMERAL 0) term163). Qed.
Lemma lem5179617 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179618 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179619 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179618 h1) (fun h1 : term222 = True => @lem5179617)). Qed.
Lemma lem5179620 : term222 = True.
Proof. exact (EQ_MP (@lem5179619) (@lem5179617)). Qed.
Lemma lem5179621 : term215 = True.
Proof. exact (TRANS (@lem5179616) (@lem5179620)). Qed.
Lemma lem5179622 : True = term215.
Proof. exact (SYM (@lem5179621)). Qed.
Lemma lem5179623 : term215.
Proof. exact (EQ_MP (@lem5179622) (@lem0)). Qed.
Lemma lem5179624 : term224.
Proof. exact (@lem5179613 (@lem5179623)). Qed.
Lemma lem5179626 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179627 : term215 = term222.
Proof. exact (@lem5179626 (NUMERAL 0) term163). Qed.
Lemma lem5179628 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179629 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179630 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179629 h1) (fun h1 : term222 = True => @lem5179628)). Qed.
Lemma lem5179631 : term222 = True.
Proof. exact (EQ_MP (@lem5179630) (@lem5179628)). Qed.
Lemma lem5179632 : term215 = True.
Proof. exact (TRANS (@lem5179627) (@lem5179631)). Qed.
Lemma lem5179633 : True = term215.
Proof. exact (SYM (@lem5179632)). Qed.
Lemma lem5179634 : term215.
Proof. exact (EQ_MP (@lem5179633) (@lem0)). Qed.
Lemma lem5179635 : term219 = term225.
Proof. exact (@lem5179624 (@lem5179634)). Qed.
Lemma lem5179637 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179638 : term172 = term173.
Proof. exact (@lem5179637 term163 term163). Qed.
Lemma lem5179639 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179640 : term175 = term163.
Proof. exact (EQ_MP (@lem5179639) (@lem940073)). Qed.
Lemma lem5179641 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179642 : term173 = term169.
Proof. exact (MK_COMB (@lem5179641) (@lem5179640)). Qed.
Lemma lem5179643 : term172 = term169.
Proof. exact (TRANS (@lem5179638) (@lem5179642)). Qed.
Lemma lem5179645 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179646 : term227 = term101.
Proof. exact (@lem5179645 term163). Qed.
Lemma lem5179647 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5179648 : term228 = term217.
Proof. exact (MK_COMB (@lem5179647) (@lem5179646)). Qed.
Lemma lem5179649 : term225 = term215.
Proof. exact (MK_COMB (@lem5179648) (@lem5179643)). Qed.
Lemma lem5179651 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179652 : term215 = term222.
Proof. exact (@lem5179651 (NUMERAL 0) term163). Qed.
Lemma lem5179653 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179654 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179655 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179654 h1) (fun h1 : term222 = True => @lem5179653)). Qed.
Lemma lem5179656 : term222 = True.
Proof. exact (EQ_MP (@lem5179655) (@lem5179653)). Qed.
Lemma lem5179657 : term215 = True.
Proof. exact (TRANS (@lem5179652) (@lem5179656)). Qed.
Lemma lem5179658 : term225 = True.
Proof. exact (TRANS (@lem5179649) (@lem5179657)). Qed.
Lemma lem5179659 : term219 = True.
Proof. exact (TRANS (@lem5179635) (@lem5179658)). Qed.
Lemma lem5179660 : term215 = True.
Proof. exact (TRANS (@lem5179612) (@lem5179659)). Qed.
Lemma lem5179661 : term214 = True.
Proof. exact (TRANS (@lem5179603) (@lem5179660)). Qed.
Lemma lem5179662 : True = term214.
Proof. exact (SYM (@lem5179661)). Qed.
Lemma lem5179663 : term214.
Proof. exact (EQ_MP (@lem5179662) (@lem0)). Qed.
Lemma lem5179664 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term229 a c.
Proof. exact (conj (@lem5179663) (@lem5179599 b a c h1)). Qed.
Lemma lem5179666 (x : real) (y : real) : term230 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5179667 (a : real) (c : real) : term231 a c.
Proof. exact (@lem5179666 term169 (term97 a c)). Qed.
Lemma lem5179668 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term232 a c.
Proof. exact (@lem5179667 a c (@lem5179664 b a c h1)). Qed.
Lemma lem5179669 (a : real) (c : real) : (term233 a c) = (term97 a c).
Proof. exact (@lem1982733 (term97 a c)). Qed.
Lemma lem5179670 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5179671 (a : real) (c : real) : (term234 a c) = (term100 a c).
Proof. exact (MK_COMB (@lem5179670) (@lem5179669 a c)). Qed.
Lemma lem5179672 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5179673 (a : real) (c : real) : (term232 a c) = (term102 a c).
Proof. exact (MK_COMB (@lem5179671 a c) (@lem5179672)). Qed.
Lemma lem5179674 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term102 a c.
Proof. exact (EQ_MP (@lem5179673 a c) (@lem5179668 b a c h1)). Qed.
Lemma lem5179676 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5179677 : term214 = term215.
Proof. exact (@lem5179676 term101 term169). Qed.
Lemma lem5179679 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179680 : term169 = term216.
Proof. exact (@lem5179679 term163). Qed.
Lemma lem5179682 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179683 : term101 = term158.
Proof. exact (@lem5179682 (NUMERAL 0)). Qed.
Lemma lem5179684 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5179685 : term217 = term218.
Proof. exact (MK_COMB (@lem5179684) (@lem5179683)). Qed.
Lemma lem5179686 : term215 = term219.
Proof. exact (MK_COMB (@lem5179685) (@lem5179680)). Qed.
Lemma lem5179687 : term220.
Proof. exact (@lem1980255 term101 term169 term169 term169). Qed.
Lemma lem5179689 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179690 : term215 = term222.
Proof. exact (@lem5179689 (NUMERAL 0) term163). Qed.
Lemma lem5179691 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179692 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179693 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179692 h1) (fun h1 : term222 = True => @lem5179691)). Qed.
Lemma lem5179694 : term222 = True.
Proof. exact (EQ_MP (@lem5179693) (@lem5179691)). Qed.
Lemma lem5179695 : term215 = True.
Proof. exact (TRANS (@lem5179690) (@lem5179694)). Qed.
Lemma lem5179696 : True = term215.
Proof. exact (SYM (@lem5179695)). Qed.
Lemma lem5179697 : term215.
Proof. exact (EQ_MP (@lem5179696) (@lem0)). Qed.
Lemma lem5179698 : term224.
Proof. exact (@lem5179687 (@lem5179697)). Qed.
Lemma lem5179700 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179701 : term215 = term222.
Proof. exact (@lem5179700 (NUMERAL 0) term163). Qed.
Lemma lem5179702 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179703 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179704 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179703 h1) (fun h1 : term222 = True => @lem5179702)). Qed.
Lemma lem5179705 : term222 = True.
Proof. exact (EQ_MP (@lem5179704) (@lem5179702)). Qed.
Lemma lem5179706 : term215 = True.
Proof. exact (TRANS (@lem5179701) (@lem5179705)). Qed.
Lemma lem5179707 : True = term215.
Proof. exact (SYM (@lem5179706)). Qed.
Lemma lem5179708 : term215.
Proof. exact (EQ_MP (@lem5179707) (@lem0)). Qed.
Lemma lem5179709 : term219 = term225.
Proof. exact (@lem5179698 (@lem5179708)). Qed.
Lemma lem5179711 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179712 : term172 = term173.
Proof. exact (@lem5179711 term163 term163). Qed.
Lemma lem5179713 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179714 : term175 = term163.
Proof. exact (EQ_MP (@lem5179713) (@lem940073)). Qed.
Lemma lem5179715 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179716 : term173 = term169.
Proof. exact (MK_COMB (@lem5179715) (@lem5179714)). Qed.
Lemma lem5179717 : term172 = term169.
Proof. exact (TRANS (@lem5179712) (@lem5179716)). Qed.
Lemma lem5179719 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179720 : term227 = term101.
Proof. exact (@lem5179719 term163). Qed.
Lemma lem5179721 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5179722 : term228 = term217.
Proof. exact (MK_COMB (@lem5179721) (@lem5179720)). Qed.
Lemma lem5179723 : term225 = term215.
Proof. exact (MK_COMB (@lem5179722) (@lem5179717)). Qed.
Lemma lem5179725 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179726 : term215 = term222.
Proof. exact (@lem5179725 (NUMERAL 0) term163). Qed.
Lemma lem5179727 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179728 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179729 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179728 h1) (fun h1 : term222 = True => @lem5179727)). Qed.
Lemma lem5179730 : term222 = True.
Proof. exact (EQ_MP (@lem5179729) (@lem5179727)). Qed.
Lemma lem5179731 : term215 = True.
Proof. exact (TRANS (@lem5179726) (@lem5179730)). Qed.
Lemma lem5179732 : term225 = True.
Proof. exact (TRANS (@lem5179723) (@lem5179731)). Qed.
Lemma lem5179733 : term219 = True.
Proof. exact (TRANS (@lem5179709) (@lem5179732)). Qed.
Lemma lem5179734 : term215 = True.
Proof. exact (TRANS (@lem5179686) (@lem5179733)). Qed.
Lemma lem5179735 : term214 = True.
Proof. exact (TRANS (@lem5179677) (@lem5179734)). Qed.
Lemma lem5179736 : True = term214.
Proof. exact (SYM (@lem5179735)). Qed.
Lemma lem5179737 : term214.
Proof. exact (EQ_MP (@lem5179736) (@lem0)). Qed.
Lemma lem5179738 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term235 a c.
Proof. exact (conj (@lem5179737) (@lem5179597 b a c h1)). Qed.
Lemma lem5179740 (x : real) (y : real) : term236 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5179741 (a : real) (c : real) : term237 a c.
Proof. exact (@lem5179740 term169 (term96 a c)). Qed.
Lemma lem5179742 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term238 a c.
Proof. exact (@lem5179741 a c (@lem5179738 b a c h1)). Qed.
Lemma lem5179743 (a : real) (c : real) : (term239 a c) = (term96 a c).
Proof. exact (@lem1982733 (term96 a c)). Qed.
Lemma lem5179744 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5179745 (a : real) (c : real) : (term240 a c) = (term120 a c).
Proof. exact (MK_COMB (@lem5179744) (@lem5179743 a c)). Qed.
Lemma lem5179746 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5179747 (a : real) (c : real) : (term238 a c) = (term121 a c).
Proof. exact (MK_COMB (@lem5179745 a c) (@lem5179746)). Qed.
Lemma lem5179748 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term121 a c.
Proof. exact (EQ_MP (@lem5179747 a c) (@lem5179742 b a c h1)). Qed.
Lemma lem5179749 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term241 a c.
Proof. exact (conj (@lem5179748 b a c h1) (@lem5179674 b a c h1)). Qed.
Lemma lem5179751 (x : real) (y : real) : term242 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5179752 (a : real) (c : real) : term243 a c.
Proof. exact (@lem5179751 (term96 a c) (term97 a c)). Qed.
Lemma lem5179753 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term244 a c.
Proof. exact (@lem5179752 a c (@lem5179749 b a c h1)). Qed.
Lemma lem5179754 (a : real) (c : real) : (term245 a c) = (term246 a c).
Proof. exact (@lem1982753 a (term98 a) (term98 c) c). Qed.
Lemma lem5179755 (a : real) : (term247 a) = (term248 a).
Proof. exact (@lem1982715 term161 a). Qed.
Lemma lem5179757 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179758 : term169 = term216.
Proof. exact (@lem5179757 term163). Qed.
Lemma lem5179760 (x : nat) : (term159 x) = (term160 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5179761 : term161 = term162.
Proof. exact (@lem5179760 term163). Qed.
Lemma lem5179762 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5179763 : term249 = term250.
Proof. exact (MK_COMB (@lem5179762) (@lem5179761)). Qed.
Lemma lem5179764 : term251 = term252.
Proof. exact (MK_COMB (@lem5179763) (@lem5179758)). Qed.
Lemma lem5179765 : term253.
Proof. exact (@lem1981473 term161 term169 term169 term169 term101 term169). Qed.
Lemma lem5179767 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179768 : term215 = term222.
Proof. exact (@lem5179767 (NUMERAL 0) term163). Qed.
Lemma lem5179769 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179770 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179771 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179770 h1) (fun h1 : term222 = True => @lem5179769)). Qed.
Lemma lem5179772 : term222 = True.
Proof. exact (EQ_MP (@lem5179771) (@lem5179769)). Qed.
Lemma lem5179773 : term215 = True.
Proof. exact (TRANS (@lem5179768) (@lem5179772)). Qed.
Lemma lem5179774 : True = term215.
Proof. exact (SYM (@lem5179773)). Qed.
Lemma lem5179775 : term215.
Proof. exact (EQ_MP (@lem5179774) (@lem0)). Qed.
Lemma lem5179776 : term254.
Proof. exact (@lem5179765 (@lem5179775)). Qed.
Lemma lem5179778 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179779 : term215 = term222.
Proof. exact (@lem5179778 (NUMERAL 0) term163). Qed.
Lemma lem5179780 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179781 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179782 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179781 h1) (fun h1 : term222 = True => @lem5179780)). Qed.
Lemma lem5179783 : term222 = True.
Proof. exact (EQ_MP (@lem5179782) (@lem5179780)). Qed.
Lemma lem5179784 : term215 = True.
Proof. exact (TRANS (@lem5179779) (@lem5179783)). Qed.
Lemma lem5179785 : True = term215.
Proof. exact (SYM (@lem5179784)). Qed.
Lemma lem5179786 : term215.
Proof. exact (EQ_MP (@lem5179785) (@lem0)). Qed.
Lemma lem5179787 : term255.
Proof. exact (@lem5179776 (@lem5179786)). Qed.
Lemma lem5179789 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179790 : term215 = term222.
Proof. exact (@lem5179789 (NUMERAL 0) term163). Qed.
Lemma lem5179791 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179792 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179793 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179792 h1) (fun h1 : term222 = True => @lem5179791)). Qed.
Lemma lem5179794 : term222 = True.
Proof. exact (EQ_MP (@lem5179793) (@lem5179791)). Qed.
Lemma lem5179795 : term215 = True.
Proof. exact (TRANS (@lem5179790) (@lem5179794)). Qed.
Lemma lem5179796 : True = term215.
Proof. exact (SYM (@lem5179795)). Qed.
Lemma lem5179797 : term215.
Proof. exact (EQ_MP (@lem5179796) (@lem0)). Qed.
Lemma lem5179798 : term256.
Proof. exact (@lem5179787 (@lem5179797)). Qed.
Lemma lem5179800 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179801 : term172 = term173.
Proof. exact (@lem5179800 term163 term163). Qed.
Lemma lem5179802 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179803 : term175 = term163.
Proof. exact (EQ_MP (@lem5179802) (@lem940073)). Qed.
Lemma lem5179804 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179805 : term173 = term169.
Proof. exact (MK_COMB (@lem5179804) (@lem5179803)). Qed.
Lemma lem5179806 : term172 = term169.
Proof. exact (TRANS (@lem5179801) (@lem5179805)). Qed.
Lemma lem5179808 (m : nat) (n : nat) : (term257 m n) = (term258 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5179809 : term259 = term260.
Proof. exact (@lem5179808 term163 term163). Qed.
Lemma lem5179810 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179811 : term175 = term163.
Proof. exact (EQ_MP (@lem5179810) (@lem940073)). Qed.
Lemma lem5179812 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179813 : term173 = term169.
Proof. exact (MK_COMB (@lem5179812) (@lem5179811)). Qed.
Lemma lem5179814 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5179815 : term260 = term161.
Proof. exact (MK_COMB (@lem5179814) (@lem5179813)). Qed.
Lemma lem5179816 : term259 = term161.
Proof. exact (TRANS (@lem5179809) (@lem5179815)). Qed.
Lemma lem5179817 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5179818 : term261 = term249.
Proof. exact (MK_COMB (@lem5179817) (@lem5179816)). Qed.
Lemma lem5179819 : term262 = term251.
Proof. exact (MK_COMB (@lem5179818) (@lem5179806)). Qed.
Lemma lem5179821 (m : nat) : (term263 m) = term101.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5179822 : term251 = term101.
Proof. exact (@lem5179821 term163). Qed.
Lemma lem5179823 : term262 = term101.
Proof. exact (TRANS (@lem5179819) (@lem5179822)). Qed.
Lemma lem5179824 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5179825 : term264 = term265.
Proof. exact (MK_COMB (@lem5179824) (@lem5179823)). Qed.
Lemma lem5179826 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem5179827 : term266 = term227.
Proof. exact (MK_COMB (@lem5179825) (@lem5179826)). Qed.
Lemma lem5179829 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179830 : term227 = term101.
Proof. exact (@lem5179829 term163). Qed.
Lemma lem5179831 : term266 = term101.
Proof. exact (TRANS (@lem5179827) (@lem5179830)). Qed.
Lemma lem5179833 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179834 : term172 = term173.
Proof. exact (@lem5179833 term163 term163). Qed.
Lemma lem5179835 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179836 : term175 = term163.
Proof. exact (EQ_MP (@lem5179835) (@lem940073)). Qed.
Lemma lem5179837 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179838 : term173 = term169.
Proof. exact (MK_COMB (@lem5179837) (@lem5179836)). Qed.
Lemma lem5179839 : term172 = term169.
Proof. exact (TRANS (@lem5179834) (@lem5179838)). Qed.
Lemma lem5179840 : term265 = term265.
Proof. exact (eq_refl term265). Qed.
Lemma lem5179841 : term267 = term227.
Proof. exact (MK_COMB (@lem5179840) (@lem5179839)). Qed.
Lemma lem5179843 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179844 : term227 = term101.
Proof. exact (@lem5179843 term163). Qed.
Lemma lem5179845 : term267 = term101.
Proof. exact (TRANS (@lem5179841) (@lem5179844)). Qed.
Lemma lem5179846 : term101 = term267.
Proof. exact (SYM (@lem5179845)). Qed.
Lemma lem5179847 : term266 = term267.
Proof. exact (TRANS (@lem5179831) (@lem5179846)). Qed.
Lemma lem5179848 : term252 = term158.
Proof. exact (@lem5179798 (@lem5179847)). Qed.
Lemma lem5179849 : term251 = term158.
Proof. exact (TRANS (@lem5179764) (@lem5179848)). Qed.
Lemma lem5179851 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5179852 : term158 = term101.
Proof. exact (@lem5179851 term101). Qed.
Lemma lem5179853 : term251 = term101.
Proof. exact (TRANS (@lem5179849) (@lem5179852)). Qed.
Lemma lem5179854 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5179855 : term268 = term265.
Proof. exact (MK_COMB (@lem5179854) (@lem5179853)). Qed.
Lemma lem5179856 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5179857 (a : real) : (term248 a) = (term269 a).
Proof. exact (MK_COMB (@lem5179855) (@lem5179856 a)). Qed.
Lemma lem5179858 (a : real) : (term247 a) = (term269 a).
Proof. exact (TRANS (@lem5179755 a) (@lem5179857 a)). Qed.
Lemma lem5179859 (a : real) : (term269 a) = term101.
Proof. exact (@lem1982719 a). Qed.
Lemma lem5179860 (a : real) : (term247 a) = term101.
Proof. exact (TRANS (@lem5179858 a) (@lem5179859 a)). Qed.
Lemma lem5179861 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5179862 (a : real) : (term270 a) = term271.
Proof. exact (MK_COMB (@lem5179861) (@lem5179860 a)). Qed.
Lemma lem5179863 (c : real) : (term272 c) = (term248 c).
Proof. exact (@lem1982713 term161 c). Qed.
Lemma lem5179865 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179866 : term169 = term216.
Proof. exact (@lem5179865 term163). Qed.
Lemma lem5179868 (x : nat) : (term159 x) = (term160 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5179869 : term161 = term162.
Proof. exact (@lem5179868 term163). Qed.
Lemma lem5179870 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5179871 : term249 = term250.
Proof. exact (MK_COMB (@lem5179870) (@lem5179869)). Qed.
Lemma lem5179872 : term251 = term252.
Proof. exact (MK_COMB (@lem5179871) (@lem5179866)). Qed.
Lemma lem5179873 : term253.
Proof. exact (@lem1981473 term161 term169 term169 term169 term101 term169). Qed.
Lemma lem5179875 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179876 : term215 = term222.
Proof. exact (@lem5179875 (NUMERAL 0) term163). Qed.
Lemma lem5179877 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179878 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179879 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179878 h1) (fun h1 : term222 = True => @lem5179877)). Qed.
Lemma lem5179880 : term222 = True.
Proof. exact (EQ_MP (@lem5179879) (@lem5179877)). Qed.
Lemma lem5179881 : term215 = True.
Proof. exact (TRANS (@lem5179876) (@lem5179880)). Qed.
Lemma lem5179882 : True = term215.
Proof. exact (SYM (@lem5179881)). Qed.
Lemma lem5179883 : term215.
Proof. exact (EQ_MP (@lem5179882) (@lem0)). Qed.
Lemma lem5179884 : term254.
Proof. exact (@lem5179873 (@lem5179883)). Qed.
Lemma lem5179886 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179887 : term215 = term222.
Proof. exact (@lem5179886 (NUMERAL 0) term163). Qed.
Lemma lem5179888 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179889 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179890 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179889 h1) (fun h1 : term222 = True => @lem5179888)). Qed.
Lemma lem5179891 : term222 = True.
Proof. exact (EQ_MP (@lem5179890) (@lem5179888)). Qed.
Lemma lem5179892 : term215 = True.
Proof. exact (TRANS (@lem5179887) (@lem5179891)). Qed.
Lemma lem5179893 : True = term215.
Proof. exact (SYM (@lem5179892)). Qed.
Lemma lem5179894 : term215.
Proof. exact (EQ_MP (@lem5179893) (@lem0)). Qed.
Lemma lem5179895 : term255.
Proof. exact (@lem5179884 (@lem5179894)). Qed.
Lemma lem5179897 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179898 : term215 = term222.
Proof. exact (@lem5179897 (NUMERAL 0) term163). Qed.
Lemma lem5179899 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179900 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179901 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179900 h1) (fun h1 : term222 = True => @lem5179899)). Qed.
Lemma lem5179902 : term222 = True.
Proof. exact (EQ_MP (@lem5179901) (@lem5179899)). Qed.
Lemma lem5179903 : term215 = True.
Proof. exact (TRANS (@lem5179898) (@lem5179902)). Qed.
Lemma lem5179904 : True = term215.
Proof. exact (SYM (@lem5179903)). Qed.
Lemma lem5179905 : term215.
Proof. exact (EQ_MP (@lem5179904) (@lem0)). Qed.
Lemma lem5179906 : term256.
Proof. exact (@lem5179895 (@lem5179905)). Qed.
Lemma lem5179908 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179909 : term172 = term173.
Proof. exact (@lem5179908 term163 term163). Qed.
Lemma lem5179910 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179911 : term175 = term163.
Proof. exact (EQ_MP (@lem5179910) (@lem940073)). Qed.
Lemma lem5179912 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179913 : term173 = term169.
Proof. exact (MK_COMB (@lem5179912) (@lem5179911)). Qed.
Lemma lem5179914 : term172 = term169.
Proof. exact (TRANS (@lem5179909) (@lem5179913)). Qed.
Lemma lem5179916 (m : nat) (n : nat) : (term257 m n) = (term258 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5179917 : term259 = term260.
Proof. exact (@lem5179916 term163 term163). Qed.
Lemma lem5179918 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179919 : term175 = term163.
Proof. exact (EQ_MP (@lem5179918) (@lem940073)). Qed.
Lemma lem5179920 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179921 : term173 = term169.
Proof. exact (MK_COMB (@lem5179920) (@lem5179919)). Qed.
Lemma lem5179922 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5179923 : term260 = term161.
Proof. exact (MK_COMB (@lem5179922) (@lem5179921)). Qed.
Lemma lem5179924 : term259 = term161.
Proof. exact (TRANS (@lem5179917) (@lem5179923)). Qed.
Lemma lem5179925 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5179926 : term261 = term249.
Proof. exact (MK_COMB (@lem5179925) (@lem5179924)). Qed.
Lemma lem5179927 : term262 = term251.
Proof. exact (MK_COMB (@lem5179926) (@lem5179914)). Qed.
Lemma lem5179929 (m : nat) : (term263 m) = term101.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5179930 : term251 = term101.
Proof. exact (@lem5179929 term163). Qed.
Lemma lem5179931 : term262 = term101.
Proof. exact (TRANS (@lem5179927) (@lem5179930)). Qed.
Lemma lem5179932 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5179933 : term264 = term265.
Proof. exact (MK_COMB (@lem5179932) (@lem5179931)). Qed.
Lemma lem5179934 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem5179935 : term266 = term227.
Proof. exact (MK_COMB (@lem5179933) (@lem5179934)). Qed.
Lemma lem5179937 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179938 : term227 = term101.
Proof. exact (@lem5179937 term163). Qed.
Lemma lem5179939 : term266 = term101.
Proof. exact (TRANS (@lem5179935) (@lem5179938)). Qed.
Lemma lem5179941 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5179942 : term172 = term173.
Proof. exact (@lem5179941 term163 term163). Qed.
Lemma lem5179943 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5179944 : term175 = term163.
Proof. exact (EQ_MP (@lem5179943) (@lem940073)). Qed.
Lemma lem5179945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5179946 : term173 = term169.
Proof. exact (MK_COMB (@lem5179945) (@lem5179944)). Qed.
Lemma lem5179947 : term172 = term169.
Proof. exact (TRANS (@lem5179942) (@lem5179946)). Qed.
Lemma lem5179948 : term265 = term265.
Proof. exact (eq_refl term265). Qed.
Lemma lem5179949 : term267 = term227.
Proof. exact (MK_COMB (@lem5179948) (@lem5179947)). Qed.
Lemma lem5179951 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5179952 : term227 = term101.
Proof. exact (@lem5179951 term163). Qed.
Lemma lem5179953 : term267 = term101.
Proof. exact (TRANS (@lem5179949) (@lem5179952)). Qed.
Lemma lem5179954 : term101 = term267.
Proof. exact (SYM (@lem5179953)). Qed.
Lemma lem5179955 : term266 = term267.
Proof. exact (TRANS (@lem5179939) (@lem5179954)). Qed.
Lemma lem5179956 : term252 = term158.
Proof. exact (@lem5179906 (@lem5179955)). Qed.
Lemma lem5179957 : term251 = term158.
Proof. exact (TRANS (@lem5179872) (@lem5179956)). Qed.
Lemma lem5179959 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5179960 : term158 = term101.
Proof. exact (@lem5179959 term101). Qed.
Lemma lem5179961 : term251 = term101.
Proof. exact (TRANS (@lem5179957) (@lem5179960)). Qed.
Lemma lem5179962 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5179963 : term268 = term265.
Proof. exact (MK_COMB (@lem5179962) (@lem5179961)). Qed.
Lemma lem5179964 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5179965 (c : real) : (term248 c) = (term269 c).
Proof. exact (MK_COMB (@lem5179963) (@lem5179964 c)). Qed.
Lemma lem5179966 (c : real) : (term272 c) = (term269 c).
Proof. exact (TRANS (@lem5179863 c) (@lem5179965 c)). Qed.
Lemma lem5179967 (c : real) : (term269 c) = term101.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5179968 (c : real) : (term272 c) = term101.
Proof. exact (TRANS (@lem5179966 c) (@lem5179967 c)). Qed.
Lemma lem5179969 (a : real) (c : real) : (term246 a c) = term273.
Proof. exact (MK_COMB (@lem5179862 a) (@lem5179968 c)). Qed.
Lemma lem5179970 (a : real) (c : real) : (term245 a c) = term273.
Proof. exact (TRANS (@lem5179754 a c) (@lem5179969 a c)). Qed.
Lemma lem5179971 : term273 = term101.
Proof. exact (@lem1982721 term101). Qed.
Lemma lem5179972 (a : real) (c : real) : (term245 a c) = term101.
Proof. exact (TRANS (@lem5179970 a c) (@lem5179971)). Qed.
Lemma lem5179973 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5179974 (a : real) (c : real) : (term274 a c) = term275.
Proof. exact (MK_COMB (@lem5179973) (@lem5179972 a c)). Qed.
Lemma lem5179975 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5179976 (a : real) (c : real) : (term244 a c) = term276.
Proof. exact (MK_COMB (@lem5179974 a c) (@lem5179975)). Qed.
Lemma lem5179977 (b : real) (a : real) (c : real) (h1 : term196 b a c) : term276.
Proof. exact (EQ_MP (@lem5179976 a c) (@lem5179753 b a c h1)). Qed.
Lemma lem5179979 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5179980 : term276 = term277.
Proof. exact (@lem5179979 term101 term101). Qed.
Lemma lem5179982 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179983 : term101 = term158.
Proof. exact (@lem5179982 (NUMERAL 0)). Qed.
Lemma lem5179985 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5179986 : term101 = term158.
Proof. exact (@lem5179985 (NUMERAL 0)). Qed.
Lemma lem5179987 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5179988 : term217 = term218.
Proof. exact (MK_COMB (@lem5179987) (@lem5179986)). Qed.
Lemma lem5179989 : term277 = term278.
Proof. exact (MK_COMB (@lem5179988) (@lem5179983)). Qed.
Lemma lem5179990 : term279.
Proof. exact (@lem1980255 term101 term169 term101 term169). Qed.
Lemma lem5179992 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5179993 : term215 = term222.
Proof. exact (@lem5179992 (NUMERAL 0) term163). Qed.
Lemma lem5179994 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5179995 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5179996 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5179995 h1) (fun h1 : term222 = True => @lem5179994)). Qed.
Lemma lem5179997 : term222 = True.
Proof. exact (EQ_MP (@lem5179996) (@lem5179994)). Qed.
Lemma lem5179998 : term215 = True.
Proof. exact (TRANS (@lem5179993) (@lem5179997)). Qed.
Lemma lem5179999 : True = term215.
Proof. exact (SYM (@lem5179998)). Qed.
Lemma lem5180000 : term215.
Proof. exact (EQ_MP (@lem5179999) (@lem0)). Qed.
Lemma lem5180001 : term280.
Proof. exact (@lem5179990 (@lem5180000)). Qed.
Lemma lem5180003 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180004 : term215 = term222.
Proof. exact (@lem5180003 (NUMERAL 0) term163). Qed.
Lemma lem5180005 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180006 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180007 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180006 h1) (fun h1 : term222 = True => @lem5180005)). Qed.
Lemma lem5180008 : term222 = True.
Proof. exact (EQ_MP (@lem5180007) (@lem5180005)). Qed.
Lemma lem5180009 : term215 = True.
Proof. exact (TRANS (@lem5180004) (@lem5180008)). Qed.
Lemma lem5180010 : True = term215.
Proof. exact (SYM (@lem5180009)). Qed.
Lemma lem5180011 : term215.
Proof. exact (EQ_MP (@lem5180010) (@lem0)). Qed.
Lemma lem5180012 : term278 = term281.
Proof. exact (@lem5180001 (@lem5180011)). Qed.
Lemma lem5180014 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180015 : term227 = term101.
Proof. exact (@lem5180014 term163). Qed.
Lemma lem5180017 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180018 : term227 = term101.
Proof. exact (@lem5180017 term163). Qed.
Lemma lem5180019 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180020 : term228 = term217.
Proof. exact (MK_COMB (@lem5180019) (@lem5180018)). Qed.
Lemma lem5180021 : term281 = term277.
Proof. exact (MK_COMB (@lem5180020) (@lem5180015)). Qed.
Lemma lem5180023 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180024 : term277 = term282.
Proof. exact (@lem5180023 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5180025 : term282 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5180026 : term277 = False.
Proof. exact (TRANS (@lem5180024) (@lem5180025)). Qed.
Lemma lem5180027 : term281 = False.
Proof. exact (TRANS (@lem5180021) (@lem5180026)). Qed.
Lemma lem5180028 : term278 = False.
Proof. exact (TRANS (@lem5180012) (@lem5180027)). Qed.
Lemma lem5180029 : term277 = False.
Proof. exact (TRANS (@lem5179989) (@lem5180028)). Qed.
Lemma lem5180030 : term276 = False.
Proof. exact (TRANS (@lem5179980) (@lem5180029)). Qed.
Lemma lem5180031 (b : real) (a : real) (c : real) (h1 : term196 b a c) : False.
Proof. exact (EQ_MP (@lem5180030) (@lem5179977 b a c h1)). Qed.
Lemma lem5180032 (b : real) (a : real) (c : real) (h1 : term198 b a c) : False.
Proof. exact (or_elim (@lem5179155 b a c h1) (fun h0 : term193 a b c => @lem5179593 a b c h0) (fun h0 : term196 b a c => @lem5180031 b a c h0)). Qed.
Lemma lem5180033 (a : real) (b : real) (c : real) (h1 : term211 a b c) : term211 a b c.
Proof. exact (h1). Qed.
Lemma lem5180034 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term206 a b c.
Proof. exact (h1). Qed.
Lemma lem5180035 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term104 a b c.
Proof. exact (proj2 (@lem5180034 a b c h1)). Qed.
Lemma lem5180036 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term121 b c.
Proof. exact (proj1 (@lem5180034 a b c h1)). Qed.
Lemma lem5180037 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term102 b c.
Proof. exact (proj2 (@lem5180035 a b c h1)). Qed.
Lemma lem5180040 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5180041 : term214 = term215.
Proof. exact (@lem5180040 term101 term169). Qed.
Lemma lem5180043 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180044 : term169 = term216.
Proof. exact (@lem5180043 term163). Qed.
Lemma lem5180046 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180047 : term101 = term158.
Proof. exact (@lem5180046 (NUMERAL 0)). Qed.
Lemma lem5180048 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180049 : term217 = term218.
Proof. exact (MK_COMB (@lem5180048) (@lem5180047)). Qed.
Lemma lem5180050 : term215 = term219.
Proof. exact (MK_COMB (@lem5180049) (@lem5180044)). Qed.
Lemma lem5180051 : term220.
Proof. exact (@lem1980255 term101 term169 term169 term169). Qed.
Lemma lem5180053 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180054 : term215 = term222.
Proof. exact (@lem5180053 (NUMERAL 0) term163). Qed.
Lemma lem5180055 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180056 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180057 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180056 h1) (fun h1 : term222 = True => @lem5180055)). Qed.
Lemma lem5180058 : term222 = True.
Proof. exact (EQ_MP (@lem5180057) (@lem5180055)). Qed.
Lemma lem5180059 : term215 = True.
Proof. exact (TRANS (@lem5180054) (@lem5180058)). Qed.
Lemma lem5180060 : True = term215.
Proof. exact (SYM (@lem5180059)). Qed.
Lemma lem5180061 : term215.
Proof. exact (EQ_MP (@lem5180060) (@lem0)). Qed.
Lemma lem5180062 : term224.
Proof. exact (@lem5180051 (@lem5180061)). Qed.
Lemma lem5180064 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180065 : term215 = term222.
Proof. exact (@lem5180064 (NUMERAL 0) term163). Qed.
Lemma lem5180066 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180067 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180068 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180067 h1) (fun h1 : term222 = True => @lem5180066)). Qed.
Lemma lem5180069 : term222 = True.
Proof. exact (EQ_MP (@lem5180068) (@lem5180066)). Qed.
Lemma lem5180070 : term215 = True.
Proof. exact (TRANS (@lem5180065) (@lem5180069)). Qed.
Lemma lem5180071 : True = term215.
Proof. exact (SYM (@lem5180070)). Qed.
Lemma lem5180072 : term215.
Proof. exact (EQ_MP (@lem5180071) (@lem0)). Qed.
Lemma lem5180073 : term219 = term225.
Proof. exact (@lem5180062 (@lem5180072)). Qed.
Lemma lem5180075 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5180076 : term172 = term173.
Proof. exact (@lem5180075 term163 term163). Qed.
Lemma lem5180077 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180078 : term175 = term163.
Proof. exact (EQ_MP (@lem5180077) (@lem940073)). Qed.
Lemma lem5180079 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180080 : term173 = term169.
Proof. exact (MK_COMB (@lem5180079) (@lem5180078)). Qed.
Lemma lem5180081 : term172 = term169.
Proof. exact (TRANS (@lem5180076) (@lem5180080)). Qed.
Lemma lem5180083 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180084 : term227 = term101.
Proof. exact (@lem5180083 term163). Qed.
Lemma lem5180085 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180086 : term228 = term217.
Proof. exact (MK_COMB (@lem5180085) (@lem5180084)). Qed.
Lemma lem5180087 : term225 = term215.
Proof. exact (MK_COMB (@lem5180086) (@lem5180081)). Qed.
Lemma lem5180089 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180090 : term215 = term222.
Proof. exact (@lem5180089 (NUMERAL 0) term163). Qed.
Lemma lem5180091 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180092 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180093 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180092 h1) (fun h1 : term222 = True => @lem5180091)). Qed.
Lemma lem5180094 : term222 = True.
Proof. exact (EQ_MP (@lem5180093) (@lem5180091)). Qed.
Lemma lem5180095 : term215 = True.
Proof. exact (TRANS (@lem5180090) (@lem5180094)). Qed.
Lemma lem5180096 : term225 = True.
Proof. exact (TRANS (@lem5180087) (@lem5180095)). Qed.
Lemma lem5180097 : term219 = True.
Proof. exact (TRANS (@lem5180073) (@lem5180096)). Qed.
Lemma lem5180098 : term215 = True.
Proof. exact (TRANS (@lem5180050) (@lem5180097)). Qed.
Lemma lem5180099 : term214 = True.
Proof. exact (TRANS (@lem5180041) (@lem5180098)). Qed.
Lemma lem5180100 : True = term214.
Proof. exact (SYM (@lem5180099)). Qed.
Lemma lem5180101 : term214.
Proof. exact (EQ_MP (@lem5180100) (@lem0)). Qed.
Lemma lem5180102 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term229 b c.
Proof. exact (conj (@lem5180101) (@lem5180037 a b c h1)). Qed.
Lemma lem5180104 (x : real) (y : real) : term230 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5180105 (b : real) (c : real) : term231 b c.
Proof. exact (@lem5180104 term169 (term97 b c)). Qed.
Lemma lem5180106 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term232 b c.
Proof. exact (@lem5180105 b c (@lem5180102 a b c h1)). Qed.
Lemma lem5180107 (b : real) (c : real) : (term233 b c) = (term97 b c).
Proof. exact (@lem1982733 (term97 b c)). Qed.
Lemma lem5180108 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5180109 (b : real) (c : real) : (term234 b c) = (term100 b c).
Proof. exact (MK_COMB (@lem5180108) (@lem5180107 b c)). Qed.
Lemma lem5180110 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5180111 (b : real) (c : real) : (term232 b c) = (term102 b c).
Proof. exact (MK_COMB (@lem5180109 b c) (@lem5180110)). Qed.
Lemma lem5180112 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term102 b c.
Proof. exact (EQ_MP (@lem5180111 b c) (@lem5180106 a b c h1)). Qed.
Lemma lem5180114 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5180115 : term214 = term215.
Proof. exact (@lem5180114 term101 term169). Qed.
Lemma lem5180117 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180118 : term169 = term216.
Proof. exact (@lem5180117 term163). Qed.
Lemma lem5180120 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180121 : term101 = term158.
Proof. exact (@lem5180120 (NUMERAL 0)). Qed.
Lemma lem5180122 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180123 : term217 = term218.
Proof. exact (MK_COMB (@lem5180122) (@lem5180121)). Qed.
Lemma lem5180124 : term215 = term219.
Proof. exact (MK_COMB (@lem5180123) (@lem5180118)). Qed.
Lemma lem5180125 : term220.
Proof. exact (@lem1980255 term101 term169 term169 term169). Qed.
Lemma lem5180127 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180128 : term215 = term222.
Proof. exact (@lem5180127 (NUMERAL 0) term163). Qed.
Lemma lem5180129 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180130 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180131 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180130 h1) (fun h1 : term222 = True => @lem5180129)). Qed.
Lemma lem5180132 : term222 = True.
Proof. exact (EQ_MP (@lem5180131) (@lem5180129)). Qed.
Lemma lem5180133 : term215 = True.
Proof. exact (TRANS (@lem5180128) (@lem5180132)). Qed.
Lemma lem5180134 : True = term215.
Proof. exact (SYM (@lem5180133)). Qed.
Lemma lem5180135 : term215.
Proof. exact (EQ_MP (@lem5180134) (@lem0)). Qed.
Lemma lem5180136 : term224.
Proof. exact (@lem5180125 (@lem5180135)). Qed.
Lemma lem5180138 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180139 : term215 = term222.
Proof. exact (@lem5180138 (NUMERAL 0) term163). Qed.
Lemma lem5180140 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180141 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180142 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180141 h1) (fun h1 : term222 = True => @lem5180140)). Qed.
Lemma lem5180143 : term222 = True.
Proof. exact (EQ_MP (@lem5180142) (@lem5180140)). Qed.
Lemma lem5180144 : term215 = True.
Proof. exact (TRANS (@lem5180139) (@lem5180143)). Qed.
Lemma lem5180145 : True = term215.
Proof. exact (SYM (@lem5180144)). Qed.
Lemma lem5180146 : term215.
Proof. exact (EQ_MP (@lem5180145) (@lem0)). Qed.
Lemma lem5180147 : term219 = term225.
Proof. exact (@lem5180136 (@lem5180146)). Qed.
Lemma lem5180149 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5180150 : term172 = term173.
Proof. exact (@lem5180149 term163 term163). Qed.
Lemma lem5180151 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180152 : term175 = term163.
Proof. exact (EQ_MP (@lem5180151) (@lem940073)). Qed.
Lemma lem5180153 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180154 : term173 = term169.
Proof. exact (MK_COMB (@lem5180153) (@lem5180152)). Qed.
Lemma lem5180155 : term172 = term169.
Proof. exact (TRANS (@lem5180150) (@lem5180154)). Qed.
Lemma lem5180157 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180158 : term227 = term101.
Proof. exact (@lem5180157 term163). Qed.
Lemma lem5180159 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180160 : term228 = term217.
Proof. exact (MK_COMB (@lem5180159) (@lem5180158)). Qed.
Lemma lem5180161 : term225 = term215.
Proof. exact (MK_COMB (@lem5180160) (@lem5180155)). Qed.
Lemma lem5180163 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180164 : term215 = term222.
Proof. exact (@lem5180163 (NUMERAL 0) term163). Qed.
Lemma lem5180165 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180166 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180167 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180166 h1) (fun h1 : term222 = True => @lem5180165)). Qed.
Lemma lem5180168 : term222 = True.
Proof. exact (EQ_MP (@lem5180167) (@lem5180165)). Qed.
Lemma lem5180169 : term215 = True.
Proof. exact (TRANS (@lem5180164) (@lem5180168)). Qed.
Lemma lem5180170 : term225 = True.
Proof. exact (TRANS (@lem5180161) (@lem5180169)). Qed.
Lemma lem5180171 : term219 = True.
Proof. exact (TRANS (@lem5180147) (@lem5180170)). Qed.
Lemma lem5180172 : term215 = True.
Proof. exact (TRANS (@lem5180124) (@lem5180171)). Qed.
Lemma lem5180173 : term214 = True.
Proof. exact (TRANS (@lem5180115) (@lem5180172)). Qed.
Lemma lem5180174 : True = term214.
Proof. exact (SYM (@lem5180173)). Qed.
Lemma lem5180175 : term214.
Proof. exact (EQ_MP (@lem5180174) (@lem0)). Qed.
Lemma lem5180176 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term235 b c.
Proof. exact (conj (@lem5180175) (@lem5180036 a b c h1)). Qed.
Lemma lem5180178 (x : real) (y : real) : term236 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5180179 (b : real) (c : real) : term237 b c.
Proof. exact (@lem5180178 term169 (term96 b c)). Qed.
Lemma lem5180180 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term238 b c.
Proof. exact (@lem5180179 b c (@lem5180176 a b c h1)). Qed.
Lemma lem5180181 (b : real) (c : real) : (term239 b c) = (term96 b c).
Proof. exact (@lem1982733 (term96 b c)). Qed.
Lemma lem5180182 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5180183 (b : real) (c : real) : (term240 b c) = (term120 b c).
Proof. exact (MK_COMB (@lem5180182) (@lem5180181 b c)). Qed.
Lemma lem5180184 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5180185 (b : real) (c : real) : (term238 b c) = (term121 b c).
Proof. exact (MK_COMB (@lem5180183 b c) (@lem5180184)). Qed.
Lemma lem5180186 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term121 b c.
Proof. exact (EQ_MP (@lem5180185 b c) (@lem5180180 a b c h1)). Qed.
Lemma lem5180187 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term241 b c.
Proof. exact (conj (@lem5180186 a b c h1) (@lem5180112 a b c h1)). Qed.
Lemma lem5180189 (x : real) (y : real) : term242 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5180190 (b : real) (c : real) : term243 b c.
Proof. exact (@lem5180189 (term96 b c) (term97 b c)). Qed.
Lemma lem5180191 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term244 b c.
Proof. exact (@lem5180190 b c (@lem5180187 a b c h1)). Qed.
Lemma lem5180192 (b : real) (c : real) : (term245 b c) = (term246 b c).
Proof. exact (@lem1982753 b (term98 b) (term98 c) c). Qed.
Lemma lem5180193 (b : real) : (term247 b) = (term248 b).
Proof. exact (@lem1982715 term161 b). Qed.
Lemma lem5180195 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180196 : term169 = term216.
Proof. exact (@lem5180195 term163). Qed.
Lemma lem5180198 (x : nat) : (term159 x) = (term160 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5180199 : term161 = term162.
Proof. exact (@lem5180198 term163). Qed.
Lemma lem5180200 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5180201 : term249 = term250.
Proof. exact (MK_COMB (@lem5180200) (@lem5180199)). Qed.
Lemma lem5180202 : term251 = term252.
Proof. exact (MK_COMB (@lem5180201) (@lem5180196)). Qed.
Lemma lem5180203 : term253.
Proof. exact (@lem1981473 term161 term169 term169 term169 term101 term169). Qed.
Lemma lem5180205 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180206 : term215 = term222.
Proof. exact (@lem5180205 (NUMERAL 0) term163). Qed.
Lemma lem5180207 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180208 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180209 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180208 h1) (fun h1 : term222 = True => @lem5180207)). Qed.
Lemma lem5180210 : term222 = True.
Proof. exact (EQ_MP (@lem5180209) (@lem5180207)). Qed.
Lemma lem5180211 : term215 = True.
Proof. exact (TRANS (@lem5180206) (@lem5180210)). Qed.
Lemma lem5180212 : True = term215.
Proof. exact (SYM (@lem5180211)). Qed.
Lemma lem5180213 : term215.
Proof. exact (EQ_MP (@lem5180212) (@lem0)). Qed.
Lemma lem5180214 : term254.
Proof. exact (@lem5180203 (@lem5180213)). Qed.
Lemma lem5180216 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180217 : term215 = term222.
Proof. exact (@lem5180216 (NUMERAL 0) term163). Qed.
Lemma lem5180218 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180219 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180220 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180219 h1) (fun h1 : term222 = True => @lem5180218)). Qed.
Lemma lem5180221 : term222 = True.
Proof. exact (EQ_MP (@lem5180220) (@lem5180218)). Qed.
Lemma lem5180222 : term215 = True.
Proof. exact (TRANS (@lem5180217) (@lem5180221)). Qed.
Lemma lem5180223 : True = term215.
Proof. exact (SYM (@lem5180222)). Qed.
Lemma lem5180224 : term215.
Proof. exact (EQ_MP (@lem5180223) (@lem0)). Qed.
Lemma lem5180225 : term255.
Proof. exact (@lem5180214 (@lem5180224)). Qed.
Lemma lem5180227 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180228 : term215 = term222.
Proof. exact (@lem5180227 (NUMERAL 0) term163). Qed.
Lemma lem5180229 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180230 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180231 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180230 h1) (fun h1 : term222 = True => @lem5180229)). Qed.
Lemma lem5180232 : term222 = True.
Proof. exact (EQ_MP (@lem5180231) (@lem5180229)). Qed.
Lemma lem5180233 : term215 = True.
Proof. exact (TRANS (@lem5180228) (@lem5180232)). Qed.
Lemma lem5180234 : True = term215.
Proof. exact (SYM (@lem5180233)). Qed.
Lemma lem5180235 : term215.
Proof. exact (EQ_MP (@lem5180234) (@lem0)). Qed.
Lemma lem5180236 : term256.
Proof. exact (@lem5180225 (@lem5180235)). Qed.
Lemma lem5180238 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5180239 : term172 = term173.
Proof. exact (@lem5180238 term163 term163). Qed.
Lemma lem5180240 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180241 : term175 = term163.
Proof. exact (EQ_MP (@lem5180240) (@lem940073)). Qed.
Lemma lem5180242 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180243 : term173 = term169.
Proof. exact (MK_COMB (@lem5180242) (@lem5180241)). Qed.
Lemma lem5180244 : term172 = term169.
Proof. exact (TRANS (@lem5180239) (@lem5180243)). Qed.
Lemma lem5180246 (m : nat) (n : nat) : (term257 m n) = (term258 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5180247 : term259 = term260.
Proof. exact (@lem5180246 term163 term163). Qed.
Lemma lem5180248 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180249 : term175 = term163.
Proof. exact (EQ_MP (@lem5180248) (@lem940073)). Qed.
Lemma lem5180250 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180251 : term173 = term169.
Proof. exact (MK_COMB (@lem5180250) (@lem5180249)). Qed.
Lemma lem5180252 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5180253 : term260 = term161.
Proof. exact (MK_COMB (@lem5180252) (@lem5180251)). Qed.
Lemma lem5180254 : term259 = term161.
Proof. exact (TRANS (@lem5180247) (@lem5180253)). Qed.
Lemma lem5180255 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5180256 : term261 = term249.
Proof. exact (MK_COMB (@lem5180255) (@lem5180254)). Qed.
Lemma lem5180257 : term262 = term251.
Proof. exact (MK_COMB (@lem5180256) (@lem5180244)). Qed.
Lemma lem5180259 (m : nat) : (term263 m) = term101.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5180260 : term251 = term101.
Proof. exact (@lem5180259 term163). Qed.
Lemma lem5180261 : term262 = term101.
Proof. exact (TRANS (@lem5180257) (@lem5180260)). Qed.
Lemma lem5180262 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5180263 : term264 = term265.
Proof. exact (MK_COMB (@lem5180262) (@lem5180261)). Qed.
Lemma lem5180264 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem5180265 : term266 = term227.
Proof. exact (MK_COMB (@lem5180263) (@lem5180264)). Qed.
Lemma lem5180267 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180268 : term227 = term101.
Proof. exact (@lem5180267 term163). Qed.
Lemma lem5180269 : term266 = term101.
Proof. exact (TRANS (@lem5180265) (@lem5180268)). Qed.
Lemma lem5180271 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5180272 : term172 = term173.
Proof. exact (@lem5180271 term163 term163). Qed.
Lemma lem5180273 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180274 : term175 = term163.
Proof. exact (EQ_MP (@lem5180273) (@lem940073)). Qed.
Lemma lem5180275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180276 : term173 = term169.
Proof. exact (MK_COMB (@lem5180275) (@lem5180274)). Qed.
Lemma lem5180277 : term172 = term169.
Proof. exact (TRANS (@lem5180272) (@lem5180276)). Qed.
Lemma lem5180278 : term265 = term265.
Proof. exact (eq_refl term265). Qed.
Lemma lem5180279 : term267 = term227.
Proof. exact (MK_COMB (@lem5180278) (@lem5180277)). Qed.
Lemma lem5180281 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180282 : term227 = term101.
Proof. exact (@lem5180281 term163). Qed.
Lemma lem5180283 : term267 = term101.
Proof. exact (TRANS (@lem5180279) (@lem5180282)). Qed.
Lemma lem5180284 : term101 = term267.
Proof. exact (SYM (@lem5180283)). Qed.
Lemma lem5180285 : term266 = term267.
Proof. exact (TRANS (@lem5180269) (@lem5180284)). Qed.
Lemma lem5180286 : term252 = term158.
Proof. exact (@lem5180236 (@lem5180285)). Qed.
Lemma lem5180287 : term251 = term158.
Proof. exact (TRANS (@lem5180202) (@lem5180286)). Qed.
Lemma lem5180289 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5180290 : term158 = term101.
Proof. exact (@lem5180289 term101). Qed.
Lemma lem5180291 : term251 = term101.
Proof. exact (TRANS (@lem5180287) (@lem5180290)). Qed.
Lemma lem5180292 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5180293 : term268 = term265.
Proof. exact (MK_COMB (@lem5180292) (@lem5180291)). Qed.
Lemma lem5180294 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5180295 (b : real) : (term248 b) = (term269 b).
Proof. exact (MK_COMB (@lem5180293) (@lem5180294 b)). Qed.
Lemma lem5180296 (b : real) : (term247 b) = (term269 b).
Proof. exact (TRANS (@lem5180193 b) (@lem5180295 b)). Qed.
Lemma lem5180297 (b : real) : (term269 b) = term101.
Proof. exact (@lem1982719 b). Qed.
Lemma lem5180298 (b : real) : (term247 b) = term101.
Proof. exact (TRANS (@lem5180296 b) (@lem5180297 b)). Qed.
Lemma lem5180299 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5180300 (b : real) : (term270 b) = term271.
Proof. exact (MK_COMB (@lem5180299) (@lem5180298 b)). Qed.
Lemma lem5180301 (c : real) : (term272 c) = (term248 c).
Proof. exact (@lem1982713 term161 c). Qed.
Lemma lem5180303 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180304 : term169 = term216.
Proof. exact (@lem5180303 term163). Qed.
Lemma lem5180306 (x : nat) : (term159 x) = (term160 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5180307 : term161 = term162.
Proof. exact (@lem5180306 term163). Qed.
Lemma lem5180308 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5180309 : term249 = term250.
Proof. exact (MK_COMB (@lem5180308) (@lem5180307)). Qed.
Lemma lem5180310 : term251 = term252.
Proof. exact (MK_COMB (@lem5180309) (@lem5180304)). Qed.
Lemma lem5180311 : term253.
Proof. exact (@lem1981473 term161 term169 term169 term169 term101 term169). Qed.
Lemma lem5180313 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180314 : term215 = term222.
Proof. exact (@lem5180313 (NUMERAL 0) term163). Qed.
Lemma lem5180315 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180316 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180317 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180316 h1) (fun h1 : term222 = True => @lem5180315)). Qed.
Lemma lem5180318 : term222 = True.
Proof. exact (EQ_MP (@lem5180317) (@lem5180315)). Qed.
Lemma lem5180319 : term215 = True.
Proof. exact (TRANS (@lem5180314) (@lem5180318)). Qed.
Lemma lem5180320 : True = term215.
Proof. exact (SYM (@lem5180319)). Qed.
Lemma lem5180321 : term215.
Proof. exact (EQ_MP (@lem5180320) (@lem0)). Qed.
Lemma lem5180322 : term254.
Proof. exact (@lem5180311 (@lem5180321)). Qed.
Lemma lem5180324 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180325 : term215 = term222.
Proof. exact (@lem5180324 (NUMERAL 0) term163). Qed.
Lemma lem5180326 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180327 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180328 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180327 h1) (fun h1 : term222 = True => @lem5180326)). Qed.
Lemma lem5180329 : term222 = True.
Proof. exact (EQ_MP (@lem5180328) (@lem5180326)). Qed.
Lemma lem5180330 : term215 = True.
Proof. exact (TRANS (@lem5180325) (@lem5180329)). Qed.
Lemma lem5180331 : True = term215.
Proof. exact (SYM (@lem5180330)). Qed.
Lemma lem5180332 : term215.
Proof. exact (EQ_MP (@lem5180331) (@lem0)). Qed.
Lemma lem5180333 : term255.
Proof. exact (@lem5180322 (@lem5180332)). Qed.
Lemma lem5180335 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180336 : term215 = term222.
Proof. exact (@lem5180335 (NUMERAL 0) term163). Qed.
Lemma lem5180337 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180338 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180339 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180338 h1) (fun h1 : term222 = True => @lem5180337)). Qed.
Lemma lem5180340 : term222 = True.
Proof. exact (EQ_MP (@lem5180339) (@lem5180337)). Qed.
Lemma lem5180341 : term215 = True.
Proof. exact (TRANS (@lem5180336) (@lem5180340)). Qed.
Lemma lem5180342 : True = term215.
Proof. exact (SYM (@lem5180341)). Qed.
Lemma lem5180343 : term215.
Proof. exact (EQ_MP (@lem5180342) (@lem0)). Qed.
Lemma lem5180344 : term256.
Proof. exact (@lem5180333 (@lem5180343)). Qed.
Lemma lem5180346 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5180347 : term172 = term173.
Proof. exact (@lem5180346 term163 term163). Qed.
Lemma lem5180348 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180349 : term175 = term163.
Proof. exact (EQ_MP (@lem5180348) (@lem940073)). Qed.
Lemma lem5180350 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180351 : term173 = term169.
Proof. exact (MK_COMB (@lem5180350) (@lem5180349)). Qed.
Lemma lem5180352 : term172 = term169.
Proof. exact (TRANS (@lem5180347) (@lem5180351)). Qed.
Lemma lem5180354 (m : nat) (n : nat) : (term257 m n) = (term258 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5180355 : term259 = term260.
Proof. exact (@lem5180354 term163 term163). Qed.
Lemma lem5180356 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180357 : term175 = term163.
Proof. exact (EQ_MP (@lem5180356) (@lem940073)). Qed.
Lemma lem5180358 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180359 : term173 = term169.
Proof. exact (MK_COMB (@lem5180358) (@lem5180357)). Qed.
Lemma lem5180360 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5180361 : term260 = term161.
Proof. exact (MK_COMB (@lem5180360) (@lem5180359)). Qed.
Lemma lem5180362 : term259 = term161.
Proof. exact (TRANS (@lem5180355) (@lem5180361)). Qed.
Lemma lem5180363 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5180364 : term261 = term249.
Proof. exact (MK_COMB (@lem5180363) (@lem5180362)). Qed.
Lemma lem5180365 : term262 = term251.
Proof. exact (MK_COMB (@lem5180364) (@lem5180352)). Qed.
Lemma lem5180367 (m : nat) : (term263 m) = term101.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5180368 : term251 = term101.
Proof. exact (@lem5180367 term163). Qed.
Lemma lem5180369 : term262 = term101.
Proof. exact (TRANS (@lem5180365) (@lem5180368)). Qed.
Lemma lem5180370 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5180371 : term264 = term265.
Proof. exact (MK_COMB (@lem5180370) (@lem5180369)). Qed.
Lemma lem5180372 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem5180373 : term266 = term227.
Proof. exact (MK_COMB (@lem5180371) (@lem5180372)). Qed.
Lemma lem5180375 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180376 : term227 = term101.
Proof. exact (@lem5180375 term163). Qed.
Lemma lem5180377 : term266 = term101.
Proof. exact (TRANS (@lem5180373) (@lem5180376)). Qed.
Lemma lem5180379 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5180380 : term172 = term173.
Proof. exact (@lem5180379 term163 term163). Qed.
Lemma lem5180381 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180382 : term175 = term163.
Proof. exact (EQ_MP (@lem5180381) (@lem940073)). Qed.
Lemma lem5180383 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180384 : term173 = term169.
Proof. exact (MK_COMB (@lem5180383) (@lem5180382)). Qed.
Lemma lem5180385 : term172 = term169.
Proof. exact (TRANS (@lem5180380) (@lem5180384)). Qed.
Lemma lem5180386 : term265 = term265.
Proof. exact (eq_refl term265). Qed.
Lemma lem5180387 : term267 = term227.
Proof. exact (MK_COMB (@lem5180386) (@lem5180385)). Qed.
Lemma lem5180389 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180390 : term227 = term101.
Proof. exact (@lem5180389 term163). Qed.
Lemma lem5180391 : term267 = term101.
Proof. exact (TRANS (@lem5180387) (@lem5180390)). Qed.
Lemma lem5180392 : term101 = term267.
Proof. exact (SYM (@lem5180391)). Qed.
Lemma lem5180393 : term266 = term267.
Proof. exact (TRANS (@lem5180377) (@lem5180392)). Qed.
Lemma lem5180394 : term252 = term158.
Proof. exact (@lem5180344 (@lem5180393)). Qed.
Lemma lem5180395 : term251 = term158.
Proof. exact (TRANS (@lem5180310) (@lem5180394)). Qed.
Lemma lem5180397 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5180398 : term158 = term101.
Proof. exact (@lem5180397 term101). Qed.
Lemma lem5180399 : term251 = term101.
Proof. exact (TRANS (@lem5180395) (@lem5180398)). Qed.
Lemma lem5180400 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5180401 : term268 = term265.
Proof. exact (MK_COMB (@lem5180400) (@lem5180399)). Qed.
Lemma lem5180402 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5180403 (c : real) : (term248 c) = (term269 c).
Proof. exact (MK_COMB (@lem5180401) (@lem5180402 c)). Qed.
Lemma lem5180404 (c : real) : (term272 c) = (term269 c).
Proof. exact (TRANS (@lem5180301 c) (@lem5180403 c)). Qed.
Lemma lem5180405 (c : real) : (term269 c) = term101.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5180406 (c : real) : (term272 c) = term101.
Proof. exact (TRANS (@lem5180404 c) (@lem5180405 c)). Qed.
Lemma lem5180407 (b : real) (c : real) : (term246 b c) = term273.
Proof. exact (MK_COMB (@lem5180300 b) (@lem5180406 c)). Qed.
Lemma lem5180408 (b : real) (c : real) : (term245 b c) = term273.
Proof. exact (TRANS (@lem5180192 b c) (@lem5180407 b c)). Qed.
Lemma lem5180409 : term273 = term101.
Proof. exact (@lem1982721 term101). Qed.
Lemma lem5180410 (b : real) (c : real) : (term245 b c) = term101.
Proof. exact (TRANS (@lem5180408 b c) (@lem5180409)). Qed.
Lemma lem5180411 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5180412 (b : real) (c : real) : (term274 b c) = term275.
Proof. exact (MK_COMB (@lem5180411) (@lem5180410 b c)). Qed.
Lemma lem5180413 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5180414 (b : real) (c : real) : (term244 b c) = term276.
Proof. exact (MK_COMB (@lem5180412 b c) (@lem5180413)). Qed.
Lemma lem5180415 (a : real) (b : real) (c : real) (h1 : term206 a b c) : term276.
Proof. exact (EQ_MP (@lem5180414 b c) (@lem5180191 a b c h1)). Qed.
Lemma lem5180417 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5180418 : term276 = term277.
Proof. exact (@lem5180417 term101 term101). Qed.
Lemma lem5180420 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180421 : term101 = term158.
Proof. exact (@lem5180420 (NUMERAL 0)). Qed.
Lemma lem5180423 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180424 : term101 = term158.
Proof. exact (@lem5180423 (NUMERAL 0)). Qed.
Lemma lem5180425 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180426 : term217 = term218.
Proof. exact (MK_COMB (@lem5180425) (@lem5180424)). Qed.
Lemma lem5180427 : term277 = term278.
Proof. exact (MK_COMB (@lem5180426) (@lem5180421)). Qed.
Lemma lem5180428 : term279.
Proof. exact (@lem1980255 term101 term169 term101 term169). Qed.
Lemma lem5180430 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180431 : term215 = term222.
Proof. exact (@lem5180430 (NUMERAL 0) term163). Qed.
Lemma lem5180432 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180433 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180434 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180433 h1) (fun h1 : term222 = True => @lem5180432)). Qed.
Lemma lem5180435 : term222 = True.
Proof. exact (EQ_MP (@lem5180434) (@lem5180432)). Qed.
Lemma lem5180436 : term215 = True.
Proof. exact (TRANS (@lem5180431) (@lem5180435)). Qed.
Lemma lem5180437 : True = term215.
Proof. exact (SYM (@lem5180436)). Qed.
Lemma lem5180438 : term215.
Proof. exact (EQ_MP (@lem5180437) (@lem0)). Qed.
Lemma lem5180439 : term280.
Proof. exact (@lem5180428 (@lem5180438)). Qed.
Lemma lem5180441 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180442 : term215 = term222.
Proof. exact (@lem5180441 (NUMERAL 0) term163). Qed.
Lemma lem5180443 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180444 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180445 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180444 h1) (fun h1 : term222 = True => @lem5180443)). Qed.
Lemma lem5180446 : term222 = True.
Proof. exact (EQ_MP (@lem5180445) (@lem5180443)). Qed.
Lemma lem5180447 : term215 = True.
Proof. exact (TRANS (@lem5180442) (@lem5180446)). Qed.
Lemma lem5180448 : True = term215.
Proof. exact (SYM (@lem5180447)). Qed.
Lemma lem5180449 : term215.
Proof. exact (EQ_MP (@lem5180448) (@lem0)). Qed.
Lemma lem5180450 : term278 = term281.
Proof. exact (@lem5180439 (@lem5180449)). Qed.
Lemma lem5180452 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180453 : term227 = term101.
Proof. exact (@lem5180452 term163). Qed.
Lemma lem5180455 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180456 : term227 = term101.
Proof. exact (@lem5180455 term163). Qed.
Lemma lem5180457 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180458 : term228 = term217.
Proof. exact (MK_COMB (@lem5180457) (@lem5180456)). Qed.
Lemma lem5180459 : term281 = term277.
Proof. exact (MK_COMB (@lem5180458) (@lem5180453)). Qed.
Lemma lem5180461 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180462 : term277 = term282.
Proof. exact (@lem5180461 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5180463 : term282 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5180464 : term277 = False.
Proof. exact (TRANS (@lem5180462) (@lem5180463)). Qed.
Lemma lem5180465 : term281 = False.
Proof. exact (TRANS (@lem5180459) (@lem5180464)). Qed.
Lemma lem5180466 : term278 = False.
Proof. exact (TRANS (@lem5180450) (@lem5180465)). Qed.
Lemma lem5180467 : term277 = False.
Proof. exact (TRANS (@lem5180427) (@lem5180466)). Qed.
Lemma lem5180468 : term276 = False.
Proof. exact (TRANS (@lem5180418) (@lem5180467)). Qed.
Lemma lem5180469 (a : real) (b : real) (c : real) (h1 : term206 a b c) : False.
Proof. exact (EQ_MP (@lem5180468) (@lem5180415 a b c h1)). Qed.
Lemma lem5180470 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term208 a b c.
Proof. exact (h1). Qed.
Lemma lem5180471 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term104 a b c.
Proof. exact (proj2 (@lem5180470 a b c h1)). Qed.
Lemma lem5180472 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term121 a c.
Proof. exact (proj1 (@lem5180470 a b c h1)). Qed.
Lemma lem5180474 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term102 a c.
Proof. exact (proj1 (@lem5180471 a b c h1)). Qed.
Lemma lem5180476 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5180477 : term214 = term215.
Proof. exact (@lem5180476 term101 term169). Qed.
Lemma lem5180479 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180480 : term169 = term216.
Proof. exact (@lem5180479 term163). Qed.
Lemma lem5180482 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180483 : term101 = term158.
Proof. exact (@lem5180482 (NUMERAL 0)). Qed.
Lemma lem5180484 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180485 : term217 = term218.
Proof. exact (MK_COMB (@lem5180484) (@lem5180483)). Qed.
Lemma lem5180486 : term215 = term219.
Proof. exact (MK_COMB (@lem5180485) (@lem5180480)). Qed.
Lemma lem5180487 : term220.
Proof. exact (@lem1980255 term101 term169 term169 term169). Qed.
Lemma lem5180489 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180490 : term215 = term222.
Proof. exact (@lem5180489 (NUMERAL 0) term163). Qed.
Lemma lem5180491 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180492 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180493 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180492 h1) (fun h1 : term222 = True => @lem5180491)). Qed.
Lemma lem5180494 : term222 = True.
Proof. exact (EQ_MP (@lem5180493) (@lem5180491)). Qed.
Lemma lem5180495 : term215 = True.
Proof. exact (TRANS (@lem5180490) (@lem5180494)). Qed.
Lemma lem5180496 : True = term215.
Proof. exact (SYM (@lem5180495)). Qed.
Lemma lem5180497 : term215.
Proof. exact (EQ_MP (@lem5180496) (@lem0)). Qed.
Lemma lem5180498 : term224.
Proof. exact (@lem5180487 (@lem5180497)). Qed.
Lemma lem5180500 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180501 : term215 = term222.
Proof. exact (@lem5180500 (NUMERAL 0) term163). Qed.
Lemma lem5180502 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180503 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180504 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180503 h1) (fun h1 : term222 = True => @lem5180502)). Qed.
Lemma lem5180505 : term222 = True.
Proof. exact (EQ_MP (@lem5180504) (@lem5180502)). Qed.
Lemma lem5180506 : term215 = True.
Proof. exact (TRANS (@lem5180501) (@lem5180505)). Qed.
Lemma lem5180507 : True = term215.
Proof. exact (SYM (@lem5180506)). Qed.
Lemma lem5180508 : term215.
Proof. exact (EQ_MP (@lem5180507) (@lem0)). Qed.
Lemma lem5180509 : term219 = term225.
Proof. exact (@lem5180498 (@lem5180508)). Qed.
Lemma lem5180511 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5180512 : term172 = term173.
Proof. exact (@lem5180511 term163 term163). Qed.
Lemma lem5180513 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180514 : term175 = term163.
Proof. exact (EQ_MP (@lem5180513) (@lem940073)). Qed.
Lemma lem5180515 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180516 : term173 = term169.
Proof. exact (MK_COMB (@lem5180515) (@lem5180514)). Qed.
Lemma lem5180517 : term172 = term169.
Proof. exact (TRANS (@lem5180512) (@lem5180516)). Qed.
Lemma lem5180519 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180520 : term227 = term101.
Proof. exact (@lem5180519 term163). Qed.
Lemma lem5180521 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180522 : term228 = term217.
Proof. exact (MK_COMB (@lem5180521) (@lem5180520)). Qed.
Lemma lem5180523 : term225 = term215.
Proof. exact (MK_COMB (@lem5180522) (@lem5180517)). Qed.
Lemma lem5180525 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180526 : term215 = term222.
Proof. exact (@lem5180525 (NUMERAL 0) term163). Qed.
Lemma lem5180527 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180528 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180529 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180528 h1) (fun h1 : term222 = True => @lem5180527)). Qed.
Lemma lem5180530 : term222 = True.
Proof. exact (EQ_MP (@lem5180529) (@lem5180527)). Qed.
Lemma lem5180531 : term215 = True.
Proof. exact (TRANS (@lem5180526) (@lem5180530)). Qed.
Lemma lem5180532 : term225 = True.
Proof. exact (TRANS (@lem5180523) (@lem5180531)). Qed.
Lemma lem5180533 : term219 = True.
Proof. exact (TRANS (@lem5180509) (@lem5180532)). Qed.
Lemma lem5180534 : term215 = True.
Proof. exact (TRANS (@lem5180486) (@lem5180533)). Qed.
Lemma lem5180535 : term214 = True.
Proof. exact (TRANS (@lem5180477) (@lem5180534)). Qed.
Lemma lem5180536 : True = term214.
Proof. exact (SYM (@lem5180535)). Qed.
Lemma lem5180537 : term214.
Proof. exact (EQ_MP (@lem5180536) (@lem0)). Qed.
Lemma lem5180538 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term229 a c.
Proof. exact (conj (@lem5180537) (@lem5180474 a b c h1)). Qed.
Lemma lem5180540 (x : real) (y : real) : term230 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5180541 (a : real) (c : real) : term231 a c.
Proof. exact (@lem5180540 term169 (term97 a c)). Qed.
Lemma lem5180542 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term232 a c.
Proof. exact (@lem5180541 a c (@lem5180538 a b c h1)). Qed.
Lemma lem5180543 (a : real) (c : real) : (term233 a c) = (term97 a c).
Proof. exact (@lem1982733 (term97 a c)). Qed.
Lemma lem5180544 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5180545 (a : real) (c : real) : (term234 a c) = (term100 a c).
Proof. exact (MK_COMB (@lem5180544) (@lem5180543 a c)). Qed.
Lemma lem5180546 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5180547 (a : real) (c : real) : (term232 a c) = (term102 a c).
Proof. exact (MK_COMB (@lem5180545 a c) (@lem5180546)). Qed.
Lemma lem5180548 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term102 a c.
Proof. exact (EQ_MP (@lem5180547 a c) (@lem5180542 a b c h1)). Qed.
Lemma lem5180550 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5180551 : term214 = term215.
Proof. exact (@lem5180550 term101 term169). Qed.
Lemma lem5180553 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180554 : term169 = term216.
Proof. exact (@lem5180553 term163). Qed.
Lemma lem5180556 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180557 : term101 = term158.
Proof. exact (@lem5180556 (NUMERAL 0)). Qed.
Lemma lem5180558 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180559 : term217 = term218.
Proof. exact (MK_COMB (@lem5180558) (@lem5180557)). Qed.
Lemma lem5180560 : term215 = term219.
Proof. exact (MK_COMB (@lem5180559) (@lem5180554)). Qed.
Lemma lem5180561 : term220.
Proof. exact (@lem1980255 term101 term169 term169 term169). Qed.
Lemma lem5180563 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180564 : term215 = term222.
Proof. exact (@lem5180563 (NUMERAL 0) term163). Qed.
Lemma lem5180565 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180566 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180567 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180566 h1) (fun h1 : term222 = True => @lem5180565)). Qed.
Lemma lem5180568 : term222 = True.
Proof. exact (EQ_MP (@lem5180567) (@lem5180565)). Qed.
Lemma lem5180569 : term215 = True.
Proof. exact (TRANS (@lem5180564) (@lem5180568)). Qed.
Lemma lem5180570 : True = term215.
Proof. exact (SYM (@lem5180569)). Qed.
Lemma lem5180571 : term215.
Proof. exact (EQ_MP (@lem5180570) (@lem0)). Qed.
Lemma lem5180572 : term224.
Proof. exact (@lem5180561 (@lem5180571)). Qed.
Lemma lem5180574 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180575 : term215 = term222.
Proof. exact (@lem5180574 (NUMERAL 0) term163). Qed.
Lemma lem5180576 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180577 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180578 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180577 h1) (fun h1 : term222 = True => @lem5180576)). Qed.
Lemma lem5180579 : term222 = True.
Proof. exact (EQ_MP (@lem5180578) (@lem5180576)). Qed.
Lemma lem5180580 : term215 = True.
Proof. exact (TRANS (@lem5180575) (@lem5180579)). Qed.
Lemma lem5180581 : True = term215.
Proof. exact (SYM (@lem5180580)). Qed.
Lemma lem5180582 : term215.
Proof. exact (EQ_MP (@lem5180581) (@lem0)). Qed.
Lemma lem5180583 : term219 = term225.
Proof. exact (@lem5180572 (@lem5180582)). Qed.
Lemma lem5180585 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5180586 : term172 = term173.
Proof. exact (@lem5180585 term163 term163). Qed.
Lemma lem5180587 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180588 : term175 = term163.
Proof. exact (EQ_MP (@lem5180587) (@lem940073)). Qed.
Lemma lem5180589 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180590 : term173 = term169.
Proof. exact (MK_COMB (@lem5180589) (@lem5180588)). Qed.
Lemma lem5180591 : term172 = term169.
Proof. exact (TRANS (@lem5180586) (@lem5180590)). Qed.
Lemma lem5180593 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180594 : term227 = term101.
Proof. exact (@lem5180593 term163). Qed.
Lemma lem5180595 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180596 : term228 = term217.
Proof. exact (MK_COMB (@lem5180595) (@lem5180594)). Qed.
Lemma lem5180597 : term225 = term215.
Proof. exact (MK_COMB (@lem5180596) (@lem5180591)). Qed.
Lemma lem5180599 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180600 : term215 = term222.
Proof. exact (@lem5180599 (NUMERAL 0) term163). Qed.
Lemma lem5180601 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180602 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180603 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180602 h1) (fun h1 : term222 = True => @lem5180601)). Qed.
Lemma lem5180604 : term222 = True.
Proof. exact (EQ_MP (@lem5180603) (@lem5180601)). Qed.
Lemma lem5180605 : term215 = True.
Proof. exact (TRANS (@lem5180600) (@lem5180604)). Qed.
Lemma lem5180606 : term225 = True.
Proof. exact (TRANS (@lem5180597) (@lem5180605)). Qed.
Lemma lem5180607 : term219 = True.
Proof. exact (TRANS (@lem5180583) (@lem5180606)). Qed.
Lemma lem5180608 : term215 = True.
Proof. exact (TRANS (@lem5180560) (@lem5180607)). Qed.
Lemma lem5180609 : term214 = True.
Proof. exact (TRANS (@lem5180551) (@lem5180608)). Qed.
Lemma lem5180610 : True = term214.
Proof. exact (SYM (@lem5180609)). Qed.
Lemma lem5180611 : term214.
Proof. exact (EQ_MP (@lem5180610) (@lem0)). Qed.
Lemma lem5180612 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term235 a c.
Proof. exact (conj (@lem5180611) (@lem5180472 a b c h1)). Qed.
Lemma lem5180614 (x : real) (y : real) : term236 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5180615 (a : real) (c : real) : term237 a c.
Proof. exact (@lem5180614 term169 (term96 a c)). Qed.
Lemma lem5180616 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term238 a c.
Proof. exact (@lem5180615 a c (@lem5180612 a b c h1)). Qed.
Lemma lem5180617 (a : real) (c : real) : (term239 a c) = (term96 a c).
Proof. exact (@lem1982733 (term96 a c)). Qed.
Lemma lem5180618 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5180619 (a : real) (c : real) : (term240 a c) = (term120 a c).
Proof. exact (MK_COMB (@lem5180618) (@lem5180617 a c)). Qed.
Lemma lem5180620 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5180621 (a : real) (c : real) : (term238 a c) = (term121 a c).
Proof. exact (MK_COMB (@lem5180619 a c) (@lem5180620)). Qed.
Lemma lem5180622 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term121 a c.
Proof. exact (EQ_MP (@lem5180621 a c) (@lem5180616 a b c h1)). Qed.
Lemma lem5180623 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term241 a c.
Proof. exact (conj (@lem5180622 a b c h1) (@lem5180548 a b c h1)). Qed.
Lemma lem5180625 (x : real) (y : real) : term242 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5180626 (a : real) (c : real) : term243 a c.
Proof. exact (@lem5180625 (term96 a c) (term97 a c)). Qed.
Lemma lem5180627 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term244 a c.
Proof. exact (@lem5180626 a c (@lem5180623 a b c h1)). Qed.
Lemma lem5180628 (a : real) (c : real) : (term245 a c) = (term246 a c).
Proof. exact (@lem1982753 a (term98 a) (term98 c) c). Qed.
Lemma lem5180629 (a : real) : (term247 a) = (term248 a).
Proof. exact (@lem1982715 term161 a). Qed.
Lemma lem5180631 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180632 : term169 = term216.
Proof. exact (@lem5180631 term163). Qed.
Lemma lem5180634 (x : nat) : (term159 x) = (term160 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5180635 : term161 = term162.
Proof. exact (@lem5180634 term163). Qed.
Lemma lem5180636 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5180637 : term249 = term250.
Proof. exact (MK_COMB (@lem5180636) (@lem5180635)). Qed.
Lemma lem5180638 : term251 = term252.
Proof. exact (MK_COMB (@lem5180637) (@lem5180632)). Qed.
Lemma lem5180639 : term253.
Proof. exact (@lem1981473 term161 term169 term169 term169 term101 term169). Qed.
Lemma lem5180641 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180642 : term215 = term222.
Proof. exact (@lem5180641 (NUMERAL 0) term163). Qed.
Lemma lem5180643 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180644 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180645 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180644 h1) (fun h1 : term222 = True => @lem5180643)). Qed.
Lemma lem5180646 : term222 = True.
Proof. exact (EQ_MP (@lem5180645) (@lem5180643)). Qed.
Lemma lem5180647 : term215 = True.
Proof. exact (TRANS (@lem5180642) (@lem5180646)). Qed.
Lemma lem5180648 : True = term215.
Proof. exact (SYM (@lem5180647)). Qed.
Lemma lem5180649 : term215.
Proof. exact (EQ_MP (@lem5180648) (@lem0)). Qed.
Lemma lem5180650 : term254.
Proof. exact (@lem5180639 (@lem5180649)). Qed.
Lemma lem5180652 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180653 : term215 = term222.
Proof. exact (@lem5180652 (NUMERAL 0) term163). Qed.
Lemma lem5180654 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180655 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180656 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180655 h1) (fun h1 : term222 = True => @lem5180654)). Qed.
Lemma lem5180657 : term222 = True.
Proof. exact (EQ_MP (@lem5180656) (@lem5180654)). Qed.
Lemma lem5180658 : term215 = True.
Proof. exact (TRANS (@lem5180653) (@lem5180657)). Qed.
Lemma lem5180659 : True = term215.
Proof. exact (SYM (@lem5180658)). Qed.
Lemma lem5180660 : term215.
Proof. exact (EQ_MP (@lem5180659) (@lem0)). Qed.
Lemma lem5180661 : term255.
Proof. exact (@lem5180650 (@lem5180660)). Qed.
Lemma lem5180663 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180664 : term215 = term222.
Proof. exact (@lem5180663 (NUMERAL 0) term163). Qed.
Lemma lem5180665 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180666 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180667 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180666 h1) (fun h1 : term222 = True => @lem5180665)). Qed.
Lemma lem5180668 : term222 = True.
Proof. exact (EQ_MP (@lem5180667) (@lem5180665)). Qed.
Lemma lem5180669 : term215 = True.
Proof. exact (TRANS (@lem5180664) (@lem5180668)). Qed.
Lemma lem5180670 : True = term215.
Proof. exact (SYM (@lem5180669)). Qed.
Lemma lem5180671 : term215.
Proof. exact (EQ_MP (@lem5180670) (@lem0)). Qed.
Lemma lem5180672 : term256.
Proof. exact (@lem5180661 (@lem5180671)). Qed.
Lemma lem5180674 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5180675 : term172 = term173.
Proof. exact (@lem5180674 term163 term163). Qed.
Lemma lem5180676 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180677 : term175 = term163.
Proof. exact (EQ_MP (@lem5180676) (@lem940073)). Qed.
Lemma lem5180678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180679 : term173 = term169.
Proof. exact (MK_COMB (@lem5180678) (@lem5180677)). Qed.
Lemma lem5180680 : term172 = term169.
Proof. exact (TRANS (@lem5180675) (@lem5180679)). Qed.
Lemma lem5180682 (m : nat) (n : nat) : (term257 m n) = (term258 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5180683 : term259 = term260.
Proof. exact (@lem5180682 term163 term163). Qed.
Lemma lem5180684 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180685 : term175 = term163.
Proof. exact (EQ_MP (@lem5180684) (@lem940073)). Qed.
Lemma lem5180686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180687 : term173 = term169.
Proof. exact (MK_COMB (@lem5180686) (@lem5180685)). Qed.
Lemma lem5180688 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5180689 : term260 = term161.
Proof. exact (MK_COMB (@lem5180688) (@lem5180687)). Qed.
Lemma lem5180690 : term259 = term161.
Proof. exact (TRANS (@lem5180683) (@lem5180689)). Qed.
Lemma lem5180691 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5180692 : term261 = term249.
Proof. exact (MK_COMB (@lem5180691) (@lem5180690)). Qed.
Lemma lem5180693 : term262 = term251.
Proof. exact (MK_COMB (@lem5180692) (@lem5180680)). Qed.
Lemma lem5180695 (m : nat) : (term263 m) = term101.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5180696 : term251 = term101.
Proof. exact (@lem5180695 term163). Qed.
Lemma lem5180697 : term262 = term101.
Proof. exact (TRANS (@lem5180693) (@lem5180696)). Qed.
Lemma lem5180698 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5180699 : term264 = term265.
Proof. exact (MK_COMB (@lem5180698) (@lem5180697)). Qed.
Lemma lem5180700 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem5180701 : term266 = term227.
Proof. exact (MK_COMB (@lem5180699) (@lem5180700)). Qed.
Lemma lem5180703 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180704 : term227 = term101.
Proof. exact (@lem5180703 term163). Qed.
Lemma lem5180705 : term266 = term101.
Proof. exact (TRANS (@lem5180701) (@lem5180704)). Qed.
Lemma lem5180707 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5180708 : term172 = term173.
Proof. exact (@lem5180707 term163 term163). Qed.
Lemma lem5180709 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180710 : term175 = term163.
Proof. exact (EQ_MP (@lem5180709) (@lem940073)). Qed.
Lemma lem5180711 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180712 : term173 = term169.
Proof. exact (MK_COMB (@lem5180711) (@lem5180710)). Qed.
Lemma lem5180713 : term172 = term169.
Proof. exact (TRANS (@lem5180708) (@lem5180712)). Qed.
Lemma lem5180714 : term265 = term265.
Proof. exact (eq_refl term265). Qed.
Lemma lem5180715 : term267 = term227.
Proof. exact (MK_COMB (@lem5180714) (@lem5180713)). Qed.
Lemma lem5180717 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180718 : term227 = term101.
Proof. exact (@lem5180717 term163). Qed.
Lemma lem5180719 : term267 = term101.
Proof. exact (TRANS (@lem5180715) (@lem5180718)). Qed.
Lemma lem5180720 : term101 = term267.
Proof. exact (SYM (@lem5180719)). Qed.
Lemma lem5180721 : term266 = term267.
Proof. exact (TRANS (@lem5180705) (@lem5180720)). Qed.
Lemma lem5180722 : term252 = term158.
Proof. exact (@lem5180672 (@lem5180721)). Qed.
Lemma lem5180723 : term251 = term158.
Proof. exact (TRANS (@lem5180638) (@lem5180722)). Qed.
Lemma lem5180725 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5180726 : term158 = term101.
Proof. exact (@lem5180725 term101). Qed.
Lemma lem5180727 : term251 = term101.
Proof. exact (TRANS (@lem5180723) (@lem5180726)). Qed.
Lemma lem5180728 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5180729 : term268 = term265.
Proof. exact (MK_COMB (@lem5180728) (@lem5180727)). Qed.
Lemma lem5180730 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5180731 (a : real) : (term248 a) = (term269 a).
Proof. exact (MK_COMB (@lem5180729) (@lem5180730 a)). Qed.
Lemma lem5180732 (a : real) : (term247 a) = (term269 a).
Proof. exact (TRANS (@lem5180629 a) (@lem5180731 a)). Qed.
Lemma lem5180733 (a : real) : (term269 a) = term101.
Proof. exact (@lem1982719 a). Qed.
Lemma lem5180734 (a : real) : (term247 a) = term101.
Proof. exact (TRANS (@lem5180732 a) (@lem5180733 a)). Qed.
Lemma lem5180735 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5180736 (a : real) : (term270 a) = term271.
Proof. exact (MK_COMB (@lem5180735) (@lem5180734 a)). Qed.
Lemma lem5180737 (c : real) : (term272 c) = (term248 c).
Proof. exact (@lem1982713 term161 c). Qed.
Lemma lem5180739 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180740 : term169 = term216.
Proof. exact (@lem5180739 term163). Qed.
Lemma lem5180742 (x : nat) : (term159 x) = (term160 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5180743 : term161 = term162.
Proof. exact (@lem5180742 term163). Qed.
Lemma lem5180744 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5180745 : term249 = term250.
Proof. exact (MK_COMB (@lem5180744) (@lem5180743)). Qed.
Lemma lem5180746 : term251 = term252.
Proof. exact (MK_COMB (@lem5180745) (@lem5180740)). Qed.
Lemma lem5180747 : term253.
Proof. exact (@lem1981473 term161 term169 term169 term169 term101 term169). Qed.
Lemma lem5180749 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180750 : term215 = term222.
Proof. exact (@lem5180749 (NUMERAL 0) term163). Qed.
Lemma lem5180751 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180752 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180753 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180752 h1) (fun h1 : term222 = True => @lem5180751)). Qed.
Lemma lem5180754 : term222 = True.
Proof. exact (EQ_MP (@lem5180753) (@lem5180751)). Qed.
Lemma lem5180755 : term215 = True.
Proof. exact (TRANS (@lem5180750) (@lem5180754)). Qed.
Lemma lem5180756 : True = term215.
Proof. exact (SYM (@lem5180755)). Qed.
Lemma lem5180757 : term215.
Proof. exact (EQ_MP (@lem5180756) (@lem0)). Qed.
Lemma lem5180758 : term254.
Proof. exact (@lem5180747 (@lem5180757)). Qed.
Lemma lem5180760 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180761 : term215 = term222.
Proof. exact (@lem5180760 (NUMERAL 0) term163). Qed.
Lemma lem5180762 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180763 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180764 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180763 h1) (fun h1 : term222 = True => @lem5180762)). Qed.
Lemma lem5180765 : term222 = True.
Proof. exact (EQ_MP (@lem5180764) (@lem5180762)). Qed.
Lemma lem5180766 : term215 = True.
Proof. exact (TRANS (@lem5180761) (@lem5180765)). Qed.
Lemma lem5180767 : True = term215.
Proof. exact (SYM (@lem5180766)). Qed.
Lemma lem5180768 : term215.
Proof. exact (EQ_MP (@lem5180767) (@lem0)). Qed.
Lemma lem5180769 : term255.
Proof. exact (@lem5180758 (@lem5180768)). Qed.
Lemma lem5180771 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180772 : term215 = term222.
Proof. exact (@lem5180771 (NUMERAL 0) term163). Qed.
Lemma lem5180773 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180774 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180775 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180774 h1) (fun h1 : term222 = True => @lem5180773)). Qed.
Lemma lem5180776 : term222 = True.
Proof. exact (EQ_MP (@lem5180775) (@lem5180773)). Qed.
Lemma lem5180777 : term215 = True.
Proof. exact (TRANS (@lem5180772) (@lem5180776)). Qed.
Lemma lem5180778 : True = term215.
Proof. exact (SYM (@lem5180777)). Qed.
Lemma lem5180779 : term215.
Proof. exact (EQ_MP (@lem5180778) (@lem0)). Qed.
Lemma lem5180780 : term256.
Proof. exact (@lem5180769 (@lem5180779)). Qed.
Lemma lem5180782 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5180783 : term172 = term173.
Proof. exact (@lem5180782 term163 term163). Qed.
Lemma lem5180784 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180785 : term175 = term163.
Proof. exact (EQ_MP (@lem5180784) (@lem940073)). Qed.
Lemma lem5180786 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180787 : term173 = term169.
Proof. exact (MK_COMB (@lem5180786) (@lem5180785)). Qed.
Lemma lem5180788 : term172 = term169.
Proof. exact (TRANS (@lem5180783) (@lem5180787)). Qed.
Lemma lem5180790 (m : nat) (n : nat) : (term257 m n) = (term258 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5180791 : term259 = term260.
Proof. exact (@lem5180790 term163 term163). Qed.
Lemma lem5180792 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180793 : term175 = term163.
Proof. exact (EQ_MP (@lem5180792) (@lem940073)). Qed.
Lemma lem5180794 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180795 : term173 = term169.
Proof. exact (MK_COMB (@lem5180794) (@lem5180793)). Qed.
Lemma lem5180796 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5180797 : term260 = term161.
Proof. exact (MK_COMB (@lem5180796) (@lem5180795)). Qed.
Lemma lem5180798 : term259 = term161.
Proof. exact (TRANS (@lem5180791) (@lem5180797)). Qed.
Lemma lem5180799 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5180800 : term261 = term249.
Proof. exact (MK_COMB (@lem5180799) (@lem5180798)). Qed.
Lemma lem5180801 : term262 = term251.
Proof. exact (MK_COMB (@lem5180800) (@lem5180788)). Qed.
Lemma lem5180803 (m : nat) : (term263 m) = term101.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5180804 : term251 = term101.
Proof. exact (@lem5180803 term163). Qed.
Lemma lem5180805 : term262 = term101.
Proof. exact (TRANS (@lem5180801) (@lem5180804)). Qed.
Lemma lem5180806 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5180807 : term264 = term265.
Proof. exact (MK_COMB (@lem5180806) (@lem5180805)). Qed.
Lemma lem5180808 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem5180809 : term266 = term227.
Proof. exact (MK_COMB (@lem5180807) (@lem5180808)). Qed.
Lemma lem5180811 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180812 : term227 = term101.
Proof. exact (@lem5180811 term163). Qed.
Lemma lem5180813 : term266 = term101.
Proof. exact (TRANS (@lem5180809) (@lem5180812)). Qed.
Lemma lem5180815 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5180816 : term172 = term173.
Proof. exact (@lem5180815 term163 term163). Qed.
Lemma lem5180817 : (term174 = (BIT1 0)) = (term175 = term163).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5180818 : term175 = term163.
Proof. exact (EQ_MP (@lem5180817) (@lem940073)). Qed.
Lemma lem5180819 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5180820 : term173 = term169.
Proof. exact (MK_COMB (@lem5180819) (@lem5180818)). Qed.
Lemma lem5180821 : term172 = term169.
Proof. exact (TRANS (@lem5180816) (@lem5180820)). Qed.
Lemma lem5180822 : term265 = term265.
Proof. exact (eq_refl term265). Qed.
Lemma lem5180823 : term267 = term227.
Proof. exact (MK_COMB (@lem5180822) (@lem5180821)). Qed.
Lemma lem5180825 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180826 : term227 = term101.
Proof. exact (@lem5180825 term163). Qed.
Lemma lem5180827 : term267 = term101.
Proof. exact (TRANS (@lem5180823) (@lem5180826)). Qed.
Lemma lem5180828 : term101 = term267.
Proof. exact (SYM (@lem5180827)). Qed.
Lemma lem5180829 : term266 = term267.
Proof. exact (TRANS (@lem5180813) (@lem5180828)). Qed.
Lemma lem5180830 : term252 = term158.
Proof. exact (@lem5180780 (@lem5180829)). Qed.
Lemma lem5180831 : term251 = term158.
Proof. exact (TRANS (@lem5180746) (@lem5180830)). Qed.
Lemma lem5180833 (x : real) : (term179 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5180834 : term158 = term101.
Proof. exact (@lem5180833 term101). Qed.
Lemma lem5180835 : term251 = term101.
Proof. exact (TRANS (@lem5180831) (@lem5180834)). Qed.
Lemma lem5180836 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5180837 : term268 = term265.
Proof. exact (MK_COMB (@lem5180836) (@lem5180835)). Qed.
Lemma lem5180838 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5180839 (c : real) : (term248 c) = (term269 c).
Proof. exact (MK_COMB (@lem5180837) (@lem5180838 c)). Qed.
Lemma lem5180840 (c : real) : (term272 c) = (term269 c).
Proof. exact (TRANS (@lem5180737 c) (@lem5180839 c)). Qed.
Lemma lem5180841 (c : real) : (term269 c) = term101.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5180842 (c : real) : (term272 c) = term101.
Proof. exact (TRANS (@lem5180840 c) (@lem5180841 c)). Qed.
Lemma lem5180843 (a : real) (c : real) : (term246 a c) = term273.
Proof. exact (MK_COMB (@lem5180736 a) (@lem5180842 c)). Qed.
Lemma lem5180844 (a : real) (c : real) : (term245 a c) = term273.
Proof. exact (TRANS (@lem5180628 a c) (@lem5180843 a c)). Qed.
Lemma lem5180845 : term273 = term101.
Proof. exact (@lem1982721 term101). Qed.
Lemma lem5180846 (a : real) (c : real) : (term245 a c) = term101.
Proof. exact (TRANS (@lem5180844 a c) (@lem5180845)). Qed.
Lemma lem5180847 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5180848 (a : real) (c : real) : (term274 a c) = term275.
Proof. exact (MK_COMB (@lem5180847) (@lem5180846 a c)). Qed.
Lemma lem5180849 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem5180850 (a : real) (c : real) : (term244 a c) = term276.
Proof. exact (MK_COMB (@lem5180848 a c) (@lem5180849)). Qed.
Lemma lem5180851 (a : real) (b : real) (c : real) (h1 : term208 a b c) : term276.
Proof. exact (EQ_MP (@lem5180850 a c) (@lem5180627 a b c h1)). Qed.
Lemma lem5180853 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5180854 : term276 = term277.
Proof. exact (@lem5180853 term101 term101). Qed.
Lemma lem5180856 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180857 : term101 = term158.
Proof. exact (@lem5180856 (NUMERAL 0)). Qed.
Lemma lem5180859 (x : nat) : (real_of_num x) = (term157 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5180860 : term101 = term158.
Proof. exact (@lem5180859 (NUMERAL 0)). Qed.
Lemma lem5180861 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180862 : term217 = term218.
Proof. exact (MK_COMB (@lem5180861) (@lem5180860)). Qed.
Lemma lem5180863 : term277 = term278.
Proof. exact (MK_COMB (@lem5180862) (@lem5180857)). Qed.
Lemma lem5180864 : term279.
Proof. exact (@lem1980255 term101 term169 term101 term169). Qed.
Lemma lem5180866 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180867 : term215 = term222.
Proof. exact (@lem5180866 (NUMERAL 0) term163). Qed.
Lemma lem5180868 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180869 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180870 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180869 h1) (fun h1 : term222 = True => @lem5180868)). Qed.
Lemma lem5180871 : term222 = True.
Proof. exact (EQ_MP (@lem5180870) (@lem5180868)). Qed.
Lemma lem5180872 : term215 = True.
Proof. exact (TRANS (@lem5180867) (@lem5180871)). Qed.
Lemma lem5180873 : True = term215.
Proof. exact (SYM (@lem5180872)). Qed.
Lemma lem5180874 : term215.
Proof. exact (EQ_MP (@lem5180873) (@lem0)). Qed.
Lemma lem5180875 : term280.
Proof. exact (@lem5180864 (@lem5180874)). Qed.
Lemma lem5180877 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180878 : term215 = term222.
Proof. exact (@lem5180877 (NUMERAL 0) term163). Qed.
Lemma lem5180879 : term223 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5180880 (h1 : term223 = (BIT1 0)) : term222 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5180881 : (term223 = (BIT1 0)) = (term222 = True).
Proof. exact (prop_ext (fun h1 : term223 = (BIT1 0) => @lem5180880 h1) (fun h1 : term222 = True => @lem5180879)). Qed.
Lemma lem5180882 : term222 = True.
Proof. exact (EQ_MP (@lem5180881) (@lem5180879)). Qed.
Lemma lem5180883 : term215 = True.
Proof. exact (TRANS (@lem5180878) (@lem5180882)). Qed.
Lemma lem5180884 : True = term215.
Proof. exact (SYM (@lem5180883)). Qed.
Lemma lem5180885 : term215.
Proof. exact (EQ_MP (@lem5180884) (@lem0)). Qed.
Lemma lem5180886 : term278 = term281.
Proof. exact (@lem5180875 (@lem5180885)). Qed.
Lemma lem5180888 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180889 : term227 = term101.
Proof. exact (@lem5180888 term163). Qed.
Lemma lem5180891 (x : nat) : (term226 x) = term101.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5180892 : term227 = term101.
Proof. exact (@lem5180891 term163). Qed.
Lemma lem5180893 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5180894 : term228 = term217.
Proof. exact (MK_COMB (@lem5180893) (@lem5180892)). Qed.
Lemma lem5180895 : term281 = term277.
Proof. exact (MK_COMB (@lem5180894) (@lem5180889)). Qed.
Lemma lem5180897 (m : nat) (n : nat) : (term221 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5180898 : term277 = term282.
Proof. exact (@lem5180897 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5180899 : term282 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5180900 : term277 = False.
Proof. exact (TRANS (@lem5180898) (@lem5180899)). Qed.
Lemma lem5180901 : term281 = False.
Proof. exact (TRANS (@lem5180895) (@lem5180900)). Qed.
Lemma lem5180902 : term278 = False.
Proof. exact (TRANS (@lem5180886) (@lem5180901)). Qed.
Lemma lem5180903 : term277 = False.
Proof. exact (TRANS (@lem5180863) (@lem5180902)). Qed.
Lemma lem5180904 : term276 = False.
Proof. exact (TRANS (@lem5180854) (@lem5180903)). Qed.
Lemma lem5180905 (a : real) (b : real) (c : real) (h1 : term208 a b c) : False.
Proof. exact (EQ_MP (@lem5180904) (@lem5180851 a b c h1)). Qed.
Lemma lem5180906 (a : real) (b : real) (c : real) (h1 : term211 a b c) : False.
Proof. exact (or_elim (@lem5180033 a b c h1) (fun h0 : term206 a b c => @lem5180469 a b c h0) (fun h0 : term208 a b c => @lem5180905 a b c h0)). Qed.
Lemma lem5180907 (a : real) (b : real) (c : real) (h1 : term213 a b c) : False.
Proof. exact (or_elim (@lem5179154 a b c h1) (fun h0 : term198 b a c => @lem5180032 b a c h0) (fun h0 : term211 a b c => @lem5180906 a b c h0)). Qed.
Lemma lem5180908 (c : real) (a : real) (b : real) (h1 : term136 c a b) : term136 c a b.
Proof. exact (h1). Qed.
Lemma lem5180909 (c : real) (a : real) (b : real) (h1 : term136 c a b) : term213 a b c.
Proof. exact (EQ_MP (@lem5179153 a b c) (@lem5180908 c a b h1)). Qed.
Lemma lem5180910 (c : real) (a : real) (b : real) (h1 : term136 c a b) : (term213 a b c) = False.
Proof. exact (prop_ext (fun h2 : term213 a b c => @lem5180907 a b c h2) (fun h2 : False => @lem5180909 c a b h1)). Qed.
Lemma lem5180911 (c : real) (a : real) (b : real) (h1 : term136 c a b) : False.
Proof. exact (EQ_MP (@lem5180910 c a b h1) (@lem5180909 c a b h1)). Qed.
Lemma lem5180912 (a : real) (b : real) (c : real) (h1 : term94 a b c) : term94 a b c.
Proof. exact (h1). Qed.
Lemma lem5180913 (a : real) (b : real) (c : real) (h1 : term94 a b c) : term136 c a b.
Proof. exact (EQ_MP (@lem5178729 c a b) (@lem5180912 a b c h1)). Qed.
Lemma lem5180914 (a : real) (b : real) (c : real) (h1 : term94 a b c) : (term136 c a b) = False.
Proof. exact (prop_ext (fun h2 : term136 c a b => @lem5180911 c a b h2) (fun h2 : False => @lem5180913 a b c h1)). Qed.
Lemma lem5180915 (a : real) (b : real) (c : real) (h1 : term94 a b c) : False.
Proof. exact (EQ_MP (@lem5180914 a b c h1) (@lem5180913 a b c h1)). Qed.
Lemma lem5180916 (a : real) (b : real) (c : real) : term283 a b c.
Proof. exact (fun h0 : term94 a b c => @lem5180915 a b c h0). Qed.
Lemma lem5180917 (a : real) (b : real) (c : real) : term284 a b c.
Proof. exact (@lem1386578 ((term79 b a c) = (term69 a b c))). Qed.
Lemma lem5180920 (a : real) (b : real) (c : real) : (term79 b a c) = (term69 a b c).
Proof. exact (@lem5180917 a b c (@lem5180916 a b c)). Qed.
Lemma lem5180921 (a : real) (b : real) (s : real -> Prop) (c : real) (h1 : term1 s c) : (term56 b a s c) = (term72 a b s c).
Proof. exact (EQ_MP (@lem5178447 a b s c h1) (@lem5180920 a b c)). Qed.
Lemma lem5180922 (a : real) (b : real) (s : real -> Prop) (c : real) : (term56 b a s c) = (term72 a b s c).
Proof. exact (or_elim (@lem5178244 s c) (fun h0 : term1 s c => @lem5180921 a b s c h0) (fun h0 : term3 s c => @lem5178491 a b s c h0)). Qed.
Lemma lem5180923 (a : real) (b : real) (s : real -> Prop) (c : real) : (term33 b a s c) = (term65 a b s c).
Proof. exact (EQ_MP (@lem5178384 a b s c) (@lem5180922 a b s c)). Qed.
Lemma lem5180928 (a : real) (b : real) (s : real -> Prop) : term285 a b s.
Proof. exact (fun c : real => @lem5180923 a b s c). Qed.
Lemma lem5180929 (a : real) (b : real) (s : real -> Prop) : (term286 b a s) = (term287 a b s).
Proof. exact (@lem5178281 a b s (@lem5180928 a b s)). Qed.
Lemma lem5180934 (a : real) (b : real) : term288 a b.
Proof. exact (fun s : real -> Prop => @lem5180929 a b s). Qed.
Lemma lem5180939 (a : real) : term289 a.
Proof. exact (fun b : real => @lem5180934 a b). Qed.
Lemma lem5180944 : term290.
Proof. exact (fun a : real => @lem5180939 a). Qed.
