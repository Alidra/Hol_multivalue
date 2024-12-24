Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_LE_MUL_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import HREAL_ADD_RID_spec.
Require Import HREAL_LE_ADD_LCANCEL_spec.
Require Import HREAL_LE_MUL_RCANCEL_IMP_spec.
Require Import thm0_spec.
Require Import thm1319802_spec.
Require Import thm1320004_spec.
Require Import thm1320203_spec.
Require Import thm1320277_spec.
Require Import thm1321091_spec.
Require Import thm7_spec.
Require Import treal_le_spec.
Require Import treal_mul_spec.
Require Import treal_of_num_spec.
Lemma lem1331250 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1331251 (a : hreal) (h1 : term0) : term1 a.
Proof. exact (@lem1331250 h1 a). Qed.
Lemma lem1331252 (a : hreal) : (term1 a) = (term2 a).
Proof. exact (eq_refl (term1 a)). Qed.
Lemma lem1331253 (a : hreal) (h1 : term0) : term2 a.
Proof. exact (EQ_MP (@lem1331252 a) (@lem1331251 a h1)). Qed.
Lemma lem1331254 (a : hreal) (b : hreal) (h1 : term0) : term3 a b.
Proof. exact (@lem1331253 a h1 b). Qed.
Lemma lem1331255 (a : hreal) (b : hreal) : (term3 a b) = (term4 a b).
Proof. exact (eq_refl (term3 a b)). Qed.
Lemma lem1331256 (a : hreal) (b : hreal) (h1 : term0) : term4 a b.
Proof. exact (EQ_MP (@lem1331255 a b) (@lem1331254 a b h1)). Qed.
Lemma lem1331257 (a : hreal) (b : hreal) (c : hreal) (h1 : term0) : term5 a b c.
Proof. exact (@lem1331256 a b h1 c). Qed.
Lemma lem1331258 (a : hreal) (b : hreal) (c : hreal) : (term5 a b c) = (term6 a b c).
Proof. exact (eq_refl (term5 a b c)). Qed.
Lemma lem1331259 (a : hreal) (b : hreal) (c : hreal) (h1 : term0) : term6 a b c.
Proof. exact (EQ_MP (@lem1331258 a b c) (@lem1331257 a b c h1)). Qed.
Lemma lem1331260 (a : hreal) (b : hreal) (h1 : hreal_le a b) : hreal_le a b.
Proof. exact (h1). Qed.
Lemma lem1331261 (c : hreal) (a : hreal) (b : hreal) (h1 : term0) (h2 : hreal_le a b) : term7 a b c.
Proof. exact (@lem1331259 a b c h1 (@lem1331260 a b h2)). Qed.
Lemma lem1331262 (c : hreal) (a : hreal) (b : hreal) (h1 : hreal_le a b) : term8 a b c.
Proof. exact (fun h0 : term0 => @lem1331261 c a b h0 h1). Qed.
Lemma lem1331263 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1331264 (c : hreal) (a : hreal) (b : hreal) (h1 : term0) (h2 : hreal_le a b) : term7 a b c.
Proof. exact (@lem1331262 c a b h2 (@lem1331263 h1)). Qed.
Lemma lem1331265 (a : hreal) (b : hreal) (c : hreal) (h1 : term0) : term6 a b c.
Proof. exact (fun h0 : hreal_le a b => @lem1331264 c a b h1 h0). Qed.
Lemma lem1331266 (a : hreal) (b : hreal) (h1 : term0) : term4 a b.
Proof. exact (fun c : hreal => @lem1331265 a b c h1). Qed.
Lemma lem1331267 (a : hreal) (h1 : term0) : term2 a.
Proof. exact (fun b : hreal => @lem1331266 a b h1). Qed.
Lemma lem1331268 (h1 : term0) : term0.
Proof. exact (fun a : hreal => @lem1331267 a h1). Qed.
Lemma lem1331269 : term9.
Proof. exact (fun h0 : term0 => @lem1331268 h0). Qed.
Lemma lem1331270 : term0.
Proof. exact (@lem1331269 (@lem1322260)). Qed.
Lemma lem1331271 (a : hreal) : term1 a.
Proof. exact (@lem1331270 a). Qed.
Lemma lem1331272 (a : hreal) : (term1 a) = (term2 a).
Proof. exact (eq_refl (term1 a)). Qed.
Lemma lem1331273 (a : hreal) : term2 a.
Proof. exact (EQ_MP (@lem1331272 a) (@lem1331271 a)). Qed.
Lemma lem1331274 (a : hreal) (b : hreal) : term3 a b.
Proof. exact (@lem1331273 a b). Qed.
Lemma lem1331275 (a : hreal) (b : hreal) : (term3 a b) = (term4 a b).
Proof. exact (eq_refl (term3 a b)). Qed.
Lemma lem1331276 (a : hreal) (b : hreal) : term4 a b.
Proof. exact (EQ_MP (@lem1331275 a b) (@lem1331274 a b)). Qed.
Lemma lem1331277 (a : hreal) (b : hreal) (c : hreal) : term5 a b c.
Proof. exact (@lem1331276 a b c). Qed.
Lemma lem1331278 (a : hreal) (b : hreal) (c : hreal) : (term5 a b c) = (term6 a b c).
Proof. exact (eq_refl (term5 a b c)). Qed.
Lemma lem1331280 (x : hreal) : term10 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1331281 (x : hreal) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1331282 (x : hreal) : term11 x.
Proof. exact (EQ_MP (@lem1331281 x) (@lem1331280 x)). Qed.
Lemma lem1331283 (x : hreal) (y : hreal) : term12 x y.
Proof. exact (@lem1331282 x y). Qed.
Lemma lem1331284 (y : hreal) (x : hreal) : (term12 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1331289 (x : hreal) (y : hreal) (z : hreal) (h1 : (term13 x y z) = (term14 x y z)) : (term13 x y z) = (term14 x y z).
Proof. exact (h1). Qed.
Lemma lem1331290 (x : hreal) (y : hreal) (z : hreal) (h1 : (term13 x y z) = (term14 x y z)) : (term14 x y z) = (term13 x y z).
Proof. exact (SYM (@lem1331289 x y z h1)). Qed.
Lemma lem1331291 (x : hreal) (y : hreal) (z : hreal) (h1 : (term14 x y z) = (term13 x y z)) : (term14 x y z) = (term13 x y z).
Proof. exact (h1). Qed.
Lemma lem1331292 (x : hreal) (y : hreal) (z : hreal) (h1 : (term14 x y z) = (term13 x y z)) : (term13 x y z) = (term14 x y z).
Proof. exact (SYM (@lem1331291 x y z h1)). Qed.
Lemma lem1331293 (x : hreal) (y : hreal) (z : hreal) : ((term13 x y z) = (term14 x y z)) = ((term14 x y z) = (term13 x y z)).
Proof. exact (prop_ext (fun h1 : (term13 x y z) = (term14 x y z) => @lem1331290 x y z h1) (fun h1 : (term14 x y z) = (term13 x y z) => @lem1331292 x y z h1)). Qed.
Lemma lem1331294 (x : hreal) (y : hreal) : (term15 x y) = (term16 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1331293 x y z)). Qed.
Lemma lem1331295 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331296 (x : hreal) (y : hreal) : (term17 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem1331295) (@lem1331294 x y)). Qed.
Lemma lem1331297 (x : hreal) : (term19 x) = (term20 x).
Proof. exact (fun_ext (fun y : hreal => @lem1331296 x y)). Qed.
Lemma lem1331298 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331299 (x : hreal) : (term21 x) = (term22 x).
Proof. exact (MK_COMB (@lem1331298) (@lem1331297 x)). Qed.
Lemma lem1331300 : term23 = term24.
Proof. exact (fun_ext (fun x : hreal => @lem1331299 x)). Qed.
Lemma lem1331301 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331302 : term25 = term26.
Proof. exact (MK_COMB (@lem1331301) (@lem1331300)). Qed.
Lemma lem1331303 : term26.
Proof. exact (EQ_MP (@lem1331302) (@lem1320203)). Qed.
Lemma lem1331304 (x : hreal) : term27 x.
Proof. exact (@lem1331303 x). Qed.
Lemma lem1331305 (x : hreal) : (term27 x) = (term22 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1331306 (x : hreal) : term22 x.
Proof. exact (EQ_MP (@lem1331305 x) (@lem1331304 x)). Qed.
Lemma lem1331307 (x : hreal) (y : hreal) : term28 x y.
Proof. exact (@lem1331306 x y). Qed.
Lemma lem1331308 (x : hreal) (y : hreal) : (term28 x y) = (term18 x y).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem1331309 (x : hreal) (y : hreal) : term18 x y.
Proof. exact (EQ_MP (@lem1331308 x y) (@lem1331307 x y)). Qed.
Lemma lem1331310 (x : hreal) (y : hreal) (z : hreal) : term29 x y z.
Proof. exact (@lem1331309 x y z). Qed.
Lemma lem1331311 (x : hreal) (y : hreal) (z : hreal) : (term29 x y z) = ((term14 x y z) = (term13 x y z)).
Proof. exact (eq_refl (term29 x y z)). Qed.
Lemma lem1331313 (m : hreal) : term30 m.
Proof. exact (@lem1321588 m). Qed.
Lemma lem1331314 (m : hreal) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem1331315 (m : hreal) : term31 m.
Proof. exact (EQ_MP (@lem1331314 m) (@lem1331313 m)). Qed.
Lemma lem1331316 (m : hreal) (n : hreal) : term32 m n.
Proof. exact (@lem1331315 m n). Qed.
Lemma lem1331317 (m : hreal) (n : hreal) : (term32 m n) = (term33 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1331318 (m : hreal) (n : hreal) : term33 m n.
Proof. exact (EQ_MP (@lem1331317 m n) (@lem1331316 m n)). Qed.
Lemma lem1331319 (m : hreal) (n : hreal) (p : hreal) : term34 m n p.
Proof. exact (@lem1331318 m n p). Qed.
Lemma lem1331320 (m : hreal) (n : hreal) (p : hreal) : (term34 m n p) = ((term35 n m p) = (hreal_le n p)).
Proof. exact (eq_refl (term34 m n p)). Qed.
Lemma lem1331322 (x : hreal) : term36 x.
Proof. exact (@lem1321091 x). Qed.
Lemma lem1331323 (x : hreal) : (term36 x) = (term37 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1331324 (x : hreal) : term37 x.
Proof. exact (EQ_MP (@lem1331323 x) (@lem1331322 x)). Qed.
Lemma lem1331325 (x : hreal) (y : hreal) : term38 x y.
Proof. exact (@lem1331324 x y). Qed.
Lemma lem1331326 (y : hreal) (x : hreal) : (term38 x y) = (term39 y x).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem1331327 (y : hreal) (x : hreal) : term39 y x.
Proof. exact (EQ_MP (@lem1331326 y x) (@lem1331325 x y)). Qed.
Lemma lem1331328 (y : hreal) (x : hreal) (z : hreal) : term40 y x z.
Proof. exact (@lem1331327 y x z). Qed.
Lemma lem1331329 (y : hreal) (x : hreal) (z : hreal) : (term40 y x z) = ((term41 x y z) = (term42 y x z)).
Proof. exact (eq_refl (term40 y x z)). Qed.
Lemma lem1331331 (x : hreal) : term43 x.
Proof. exact (@lem1319802 x). Qed.
Lemma lem1331332 (x : hreal) : (term43 x) = (term44 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1331333 (x : hreal) : term44 x.
Proof. exact (EQ_MP (@lem1331332 x) (@lem1331331 x)). Qed.
Lemma lem1331334 (x : hreal) (y : hreal) : term45 x y.
Proof. exact (@lem1331333 x y). Qed.
Lemma lem1331335 (y : hreal) (x : hreal) : (term45 x y) = (term46 y x).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1331337 (n : hreal) : term47 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1331338 (n : hreal) : (term47 n) = ((term48 n) = n).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem1331340 (x : hreal) : term49 x.
Proof. exact (@lem1320277 x). Qed.
Lemma lem1331341 (x : hreal) : (term49 x) = ((term50 x) = x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1331343 (x1 : hreal) : term51 x1.
Proof. exact (@lem1324372 x1). Qed.
Lemma lem1331344 (x1 : hreal) : (term51 x1) = (term52 x1).
Proof. exact (eq_refl (term51 x1)). Qed.
Lemma lem1331345 (x1 : hreal) : term52 x1.
Proof. exact (EQ_MP (@lem1331344 x1) (@lem1331343 x1)). Qed.
Lemma lem1331346 (x1 : hreal) (y2 : hreal) : term53 x1 y2.
Proof. exact (@lem1331345 x1 y2). Qed.
Lemma lem1331347 (x1 : hreal) (y2 : hreal) : (term53 x1 y2) = (term54 x1 y2).
Proof. exact (eq_refl (term53 x1 y2)). Qed.
Lemma lem1331348 (x1 : hreal) (y2 : hreal) : term54 x1 y2.
Proof. exact (EQ_MP (@lem1331347 x1 y2) (@lem1331346 x1 y2)). Qed.
Lemma lem1331349 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term55 x1 y2 y1.
Proof. exact (@lem1331348 x1 y2 y1). Qed.
Lemma lem1331350 (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term55 x1 y2 y1) = (term56 x1 y2 y1).
Proof. exact (eq_refl (term55 x1 y2 y1)). Qed.
Lemma lem1331351 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term56 x1 y2 y1.
Proof. exact (EQ_MP (@lem1331350 x1 y2 y1) (@lem1331349 x1 y2 y1)). Qed.
Lemma lem1331352 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : term57 x1 y2 y1 x2.
Proof. exact (@lem1331351 x1 y2 y1 x2). Qed.
Lemma lem1331353 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term57 x1 y2 y1 x2) = ((term58 x1 y1 x2 y2) = (term59 x1 y2 y1 x2)).
Proof. exact (eq_refl (term57 x1 y2 y1 x2)). Qed.
Lemma lem1331355 (x1 : hreal) : term60 x1.
Proof. exact (@lem1324956 x1). Qed.
Lemma lem1331356 (x1 : hreal) : (term60 x1) = (term61 x1).
Proof. exact (eq_refl (term60 x1)). Qed.
Lemma lem1331357 (x1 : hreal) : term61 x1.
Proof. exact (EQ_MP (@lem1331356 x1) (@lem1331355 x1)). Qed.
Lemma lem1331358 (x1 : hreal) (y2 : hreal) : term62 x1 y2.
Proof. exact (@lem1331357 x1 y2). Qed.
Lemma lem1331359 (x1 : hreal) (y2 : hreal) : (term62 x1 y2) = (term63 x1 y2).
Proof. exact (eq_refl (term62 x1 y2)). Qed.
Lemma lem1331360 (x1 : hreal) (y2 : hreal) : term63 x1 y2.
Proof. exact (EQ_MP (@lem1331359 x1 y2) (@lem1331358 x1 y2)). Qed.
Lemma lem1331361 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term64 x1 y2 x2.
Proof. exact (@lem1331360 x1 y2 x2). Qed.
Lemma lem1331362 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term64 x1 y2 x2) = (term65 x1 y2 x2).
Proof. exact (eq_refl (term64 x1 y2 x2)). Qed.
Lemma lem1331363 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term65 x1 y2 x2.
Proof. exact (EQ_MP (@lem1331362 x1 y2 x2) (@lem1331361 x1 y2 x2)). Qed.
Lemma lem1331364 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term66 x1 y2 x2 y1.
Proof. exact (@lem1331363 x1 y2 x2 y1). Qed.
Lemma lem1331365 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term66 x1 y2 x2 y1) = ((term67 x1 y1 x2 y2) = (term68 x1 y2 x2 y1)).
Proof. exact (eq_refl (term66 x1 y2 x2 y1)). Qed.
Lemma lem1331367 (n : nat) : term69 n.
Proof. exact (@lem1322742 n). Qed.
Lemma lem1331368 (n : nat) : (term69 n) = ((treal_of_num n) = (term70 n)).
Proof. exact (eq_refl (term69 n)). Qed.
Lemma lem1331370 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term71 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1331371 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term71 _5106 _5107 P) = ((term72 _5106 _5107 P) = (term73 _5106 _5107 P)).
Proof. exact (eq_refl (term71 _5106 _5107 P)). Qed.
Lemma lem1331378 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term72 _5106 _5107 P) = (term73 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1331371 _5106 _5107 P) (@lem1331370 _5106 _5107 P)). Qed.
Lemma lem1331379 (P : type1233) : (term74 P) = (term75 P).
Proof. exact (@lem1331378 hreal hreal P). Qed.
Lemma lem1331380 : term76 = term77.
Proof. exact (@lem1331379 term78). Qed.
Lemma lem1331381 (x : prod hreal hreal) : (term79 x) = (term80 x).
Proof. exact (eq_refl (term79 x)). Qed.
Lemma lem1331382 : term81 = term78.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1331381 x)). Qed.
Lemma lem1331383 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1331384 : term76 = term82.
Proof. exact (MK_COMB (@lem1331383) (@lem1331382)). Qed.
Lemma lem1331385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1331386 : term83 = term84.
Proof. exact (MK_COMB (@lem1331385) (@lem1331384)). Qed.
Lemma lem1331387 (p1 : hreal) (p2 : hreal) : (term85 p1 p2) = (term86 p1 p2).
Proof. exact (eq_refl (term85 p1 p2)). Qed.
Lemma lem1331388 (p1 : hreal) : (term87 p1) = (term88 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1331387 p1 p2)). Qed.
Lemma lem1331389 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331390 (p1 : hreal) : (term89 p1) = (term90 p1).
Proof. exact (MK_COMB (@lem1331389) (@lem1331388 p1)). Qed.
Lemma lem1331391 : term91 = term92.
Proof. exact (fun_ext (fun p1 : hreal => @lem1331390 p1)). Qed.
Lemma lem1331392 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331393 : term77 = term93.
Proof. exact (MK_COMB (@lem1331392) (@lem1331391)). Qed.
Lemma lem1331394 : (term76 = term77) = (term82 = term93).
Proof. exact (MK_COMB (@lem1331386) (@lem1331393)). Qed.
Lemma lem1331395 : term82 = term93.
Proof. exact (EQ_MP (@lem1331394) (@lem1331380)). Qed.
Lemma lem1331413 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term72 _5106 _5107 P) = (term73 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1331371 _5106 _5107 P) (@lem1331370 _5106 _5107 P)). Qed.
Lemma lem1331414 (P : type1233) : (term74 P) = (term75 P).
Proof. exact (@lem1331413 hreal hreal P). Qed.
Lemma lem1331415 (p1 : hreal) (p2 : hreal) : (term94 p1 p2) = (term95 p1 p2).
Proof. exact (@lem1331414 (term96 p1 p2)). Qed.
Lemma lem1331416 (p1 : hreal) (p2 : hreal) (y : prod hreal hreal) : (term97 p1 p2 y) = (term98 p1 p2 y).
Proof. exact (eq_refl (term97 p1 p2 y)). Qed.
Lemma lem1331417 (p1 : hreal) (p2 : hreal) : (term99 p1 p2) = (term96 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1331416 p1 p2 y)). Qed.
Lemma lem1331418 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1331419 (p1 : hreal) (p2 : hreal) : (term94 p1 p2) = (term86 p1 p2).
Proof. exact (MK_COMB (@lem1331418) (@lem1331417 p1 p2)). Qed.
Lemma lem1331420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1331421 (p1 : hreal) (p2 : hreal) : (term100 p1 p2) = (term101 p1 p2).
Proof. exact (MK_COMB (@lem1331420) (@lem1331419 p1 p2)). Qed.
Lemma lem1331422 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term102 p1 p2 p1' p2') = (term103 p1 p2 p1' p2').
Proof. exact (eq_refl (term102 p1 p2 p1' p2')). Qed.
Lemma lem1331423 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term104 p1 p2 p1') = (term105 p1 p2 p1').
Proof. exact (fun_ext (fun p2' : hreal => @lem1331422 p1 p2 p1' p2')). Qed.
Lemma lem1331424 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331425 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term106 p1 p2 p1') = (term107 p1 p2 p1').
Proof. exact (MK_COMB (@lem1331424) (@lem1331423 p1 p2 p1')). Qed.
Lemma lem1331426 (p1 : hreal) (p2 : hreal) : (term108 p1 p2) = (term109 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1331425 p1 p2 p1')). Qed.
Lemma lem1331427 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331428 (p1 : hreal) (p2 : hreal) : (term95 p1 p2) = (term110 p1 p2).
Proof. exact (MK_COMB (@lem1331427) (@lem1331426 p1 p2)). Qed.
Lemma lem1331429 (p1 : hreal) (p2 : hreal) : ((term94 p1 p2) = (term95 p1 p2)) = ((term86 p1 p2) = (term110 p1 p2)).
Proof. exact (MK_COMB (@lem1331421 p1 p2) (@lem1331428 p1 p2)). Qed.
Lemma lem1331430 (p1 : hreal) (p2 : hreal) : (term86 p1 p2) = (term110 p1 p2).
Proof. exact (EQ_MP (@lem1331429 p1 p2) (@lem1331415 p1 p2)). Qed.
Lemma lem1331448 (n : nat) : (treal_of_num n) = (term70 n).
Proof. exact (EQ_MP (@lem1331368 n) (@lem1331367 n)). Qed.
Lemma lem1331449 : term111 = term112.
Proof. exact (@lem1331448 (NUMERAL 0)). Qed.
Lemma lem1331450 : treal_le = treal_le.
Proof. exact (eq_refl treal_le). Qed.
Lemma lem1331451 : term113 = term114.
Proof. exact (MK_COMB (@lem1331450) (@lem1331449)). Qed.
Lemma lem1331452 (p1 : hreal) (p2 : hreal) : (@pair hreal hreal p1 p2) = (@pair hreal hreal p1 p2).
Proof. exact (eq_refl (@pair hreal hreal p1 p2)). Qed.
Lemma lem1331453 (p1 : hreal) (p2 : hreal) : (term115 p1 p2) = (term116 p1 p2).
Proof. exact (MK_COMB (@lem1331451) (@lem1331452 p1 p2)). Qed.
Lemma lem1331455 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term67 x1 y1 x2 y2) = (term68 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1331365 x1 y2 x2 y1) (@lem1331364 x1 y2 x2 y1)). Qed.
Lemma lem1331456 (p2 : hreal) (p1 : hreal) : (term116 p1 p2) = (term117 p2 p1).
Proof. exact (@lem1331455 term118 p2 p1 term118). Qed.
Lemma lem1331457 (p2 : hreal) (p1 : hreal) : (term115 p1 p2) = (term117 p2 p1).
Proof. exact (TRANS (@lem1331453 p1 p2) (@lem1331456 p2 p1)). Qed.
Lemma lem1331458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1331459 (p2 : hreal) (p1 : hreal) : (term119 p1 p2) = (term120 p2 p1).
Proof. exact (MK_COMB (@lem1331458) (@lem1331457 p2 p1)). Qed.
Lemma lem1331461 (n : nat) : (treal_of_num n) = (term70 n).
Proof. exact (EQ_MP (@lem1331368 n) (@lem1331367 n)). Qed.
Lemma lem1331462 : term111 = term112.
Proof. exact (@lem1331461 (NUMERAL 0)). Qed.
Lemma lem1331463 : treal_le = treal_le.
Proof. exact (eq_refl treal_le). Qed.
Lemma lem1331464 : term113 = term114.
Proof. exact (MK_COMB (@lem1331463) (@lem1331462)). Qed.
Lemma lem1331465 (p1' : hreal) (p2' : hreal) : (@pair hreal hreal p1' p2') = (@pair hreal hreal p1' p2').
Proof. exact (eq_refl (@pair hreal hreal p1' p2')). Qed.
Lemma lem1331466 (p1' : hreal) (p2' : hreal) : (term115 p1' p2') = (term116 p1' p2').
Proof. exact (MK_COMB (@lem1331464) (@lem1331465 p1' p2')). Qed.
Lemma lem1331468 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term67 x1 y1 x2 y2) = (term68 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1331365 x1 y2 x2 y1) (@lem1331364 x1 y2 x2 y1)). Qed.
Lemma lem1331469 (p2' : hreal) (p1' : hreal) : (term116 p1' p2') = (term117 p2' p1').
Proof. exact (@lem1331468 term118 p2' p1' term118). Qed.
Lemma lem1331470 (p2' : hreal) (p1' : hreal) : (term115 p1' p2') = (term117 p2' p1').
Proof. exact (TRANS (@lem1331466 p1' p2') (@lem1331469 p2' p1')). Qed.
Lemma lem1331471 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) : (term121 p1 p2 p1' p2') = (term122 p2 p1 p2' p1').
Proof. exact (MK_COMB (@lem1331459 p2 p1) (@lem1331470 p2' p1')). Qed.
Lemma lem1331474 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1331475 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) : (term123 p1 p2 p1' p2') = (term124 p2 p1 p2' p1').
Proof. exact (MK_COMB (@lem1331474) (@lem1331471 p2 p1 p2' p1')). Qed.
Lemma lem1331477 (n : nat) : (treal_of_num n) = (term70 n).
Proof. exact (EQ_MP (@lem1331368 n) (@lem1331367 n)). Qed.
Lemma lem1331478 : term111 = term112.
Proof. exact (@lem1331477 (NUMERAL 0)). Qed.
Lemma lem1331479 : treal_le = treal_le.
Proof. exact (eq_refl treal_le). Qed.
Lemma lem1331480 : term113 = term114.
Proof. exact (MK_COMB (@lem1331479) (@lem1331478)). Qed.
Lemma lem1331482 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term58 x1 y1 x2 y2) = (term59 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1331353 x1 y2 y1 x2) (@lem1331352 x1 y2 y1 x2)). Qed.
Lemma lem1331483 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) : (term58 p1 p2 p1' p2') = (term59 p1 p2' p2 p1').
Proof. exact (@lem1331482 p1 p2' p2 p1'). Qed.
Lemma lem1331484 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) : (term125 p1 p2 p1' p2') = (term126 p1 p2' p2 p1').
Proof. exact (MK_COMB (@lem1331480) (@lem1331483 p1 p2' p2 p1')). Qed.
Lemma lem1331486 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term67 x1 y1 x2 y2) = (term68 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1331365 x1 y2 x2 y1) (@lem1331364 x1 y2 x2 y1)). Qed.
Lemma lem1331487 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term126 p1 p2' p2 p1') = (term127 p1 p1' p2 p2').
Proof. exact (@lem1331486 term118 (term128 p1 p2' p2 p1') (term128 p1 p1' p2 p2') term118). Qed.
Lemma lem1331488 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term125 p1 p2 p1' p2') = (term127 p1 p1' p2 p2').
Proof. exact (TRANS (@lem1331484 p1 p2' p2 p1') (@lem1331487 p1 p1' p2 p2')). Qed.
Lemma lem1331489 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term103 p1 p2 p1' p2') = (term129 p1 p1' p2 p2').
Proof. exact (MK_COMB (@lem1331475 p2 p1 p2' p1') (@lem1331488 p1 p1' p2 p2')). Qed.
Lemma lem1331492 (p1 : hreal) (p1' : hreal) (p2 : hreal) : (term105 p1 p2 p1') = (term130 p1 p1' p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1331489 p1 p1' p2 p2')). Qed.
Lemma lem1331493 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331494 (p1 : hreal) (p1' : hreal) (p2 : hreal) : (term107 p1 p2 p1') = (term131 p1 p1' p2).
Proof. exact (MK_COMB (@lem1331493) (@lem1331492 p1 p1' p2)). Qed.
Lemma lem1331501 (p1 : hreal) (p2 : hreal) : (term109 p1 p2) = (term132 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1331494 p1 p1' p2)). Qed.
Lemma lem1331502 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331503 (p1 : hreal) (p2 : hreal) : (term110 p1 p2) = (term133 p1 p2).
Proof. exact (MK_COMB (@lem1331502) (@lem1331501 p1 p2)). Qed.
Lemma lem1331510 (p1 : hreal) (p2 : hreal) : (term86 p1 p2) = (term133 p1 p2).
Proof. exact (TRANS (@lem1331430 p1 p2) (@lem1331503 p1 p2)). Qed.
Lemma lem1331511 (p1 : hreal) : (term88 p1) = (term134 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1331510 p1 p2)). Qed.
Lemma lem1331512 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331513 (p1 : hreal) : (term90 p1) = (term135 p1).
Proof. exact (MK_COMB (@lem1331512) (@lem1331511 p1)). Qed.
Lemma lem1331520 : term92 = term136.
Proof. exact (fun_ext (fun p1 : hreal => @lem1331513 p1)). Qed.
Lemma lem1331521 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331522 : term93 = term137.
Proof. exact (MK_COMB (@lem1331521) (@lem1331520)). Qed.
Lemma lem1331529 : term82 = term137.
Proof. exact (TRANS (@lem1331395) (@lem1331522)). Qed.
Lemma lem1331530 : term137 = term82.
Proof. exact (SYM (@lem1331529)). Qed.
Lemma lem1331536 (x : hreal) : (term50 x) = x.
Proof. exact (EQ_MP (@lem1331341 x) (@lem1331340 x)). Qed.
Lemma lem1331537 (p2 : hreal) : (term50 p2) = p2.
Proof. exact (@lem1331536 p2). Qed.
Lemma lem1331538 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1331539 (p2 : hreal) : (term138 p2) = (hreal_le p2).
Proof. exact (MK_COMB (@lem1331538) (@lem1331537 p2)). Qed.
Lemma lem1331541 (n : hreal) : (term48 n) = n.
Proof. exact (EQ_MP (@lem1331338 n) (@lem1331337 n)). Qed.
Lemma lem1331542 (p1 : hreal) : (term48 p1) = p1.
Proof. exact (@lem1331541 p1). Qed.
Lemma lem1331543 (p2 : hreal) (p1 : hreal) : (term117 p2 p1) = (hreal_le p2 p1).
Proof. exact (MK_COMB (@lem1331539 p2) (@lem1331542 p1)). Qed.
Lemma lem1331544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1331545 (p2 : hreal) (p1 : hreal) : (term120 p2 p1) = (term139 p2 p1).
Proof. exact (MK_COMB (@lem1331544) (@lem1331543 p2 p1)). Qed.
Lemma lem1331547 (x : hreal) : (term50 x) = x.
Proof. exact (EQ_MP (@lem1331341 x) (@lem1331340 x)). Qed.
Lemma lem1331548 (p2' : hreal) : (term50 p2') = p2'.
Proof. exact (@lem1331547 p2'). Qed.
Lemma lem1331549 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1331550 (p2' : hreal) : (term138 p2') = (hreal_le p2').
Proof. exact (MK_COMB (@lem1331549) (@lem1331548 p2')). Qed.
Lemma lem1331552 (n : hreal) : (term48 n) = n.
Proof. exact (EQ_MP (@lem1331338 n) (@lem1331337 n)). Qed.
Lemma lem1331553 (p1' : hreal) : (term48 p1') = p1'.
Proof. exact (@lem1331552 p1'). Qed.
Lemma lem1331554 (p2' : hreal) (p1' : hreal) : (term117 p2' p1') = (hreal_le p2' p1').
Proof. exact (MK_COMB (@lem1331550 p2') (@lem1331553 p1')). Qed.
Lemma lem1331555 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) : (term122 p2 p1 p2' p1') = (term140 p2 p1 p2' p1').
Proof. exact (MK_COMB (@lem1331545 p2 p1) (@lem1331554 p2' p1')). Qed.
Lemma lem1331558 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1331559 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) : (term124 p2 p1 p2' p1') = (term141 p2 p1 p2' p1').
Proof. exact (MK_COMB (@lem1331558) (@lem1331555 p2 p1 p2' p1')). Qed.
Lemma lem1331561 (x : hreal) : (term50 x) = x.
Proof. exact (EQ_MP (@lem1331341 x) (@lem1331340 x)). Qed.
Lemma lem1331562 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) : (term142 p1 p2' p2 p1') = (term128 p1 p2' p2 p1').
Proof. exact (@lem1331561 (term128 p1 p2' p2 p1')). Qed.
Lemma lem1331563 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1331564 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) : (term143 p1 p2' p2 p1') = (term144 p1 p2' p2 p1').
Proof. exact (MK_COMB (@lem1331563) (@lem1331562 p1 p2' p2 p1')). Qed.
Lemma lem1331566 (n : hreal) : (term48 n) = n.
Proof. exact (EQ_MP (@lem1331338 n) (@lem1331337 n)). Qed.
Lemma lem1331567 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term145 p1 p1' p2 p2') = (term128 p1 p1' p2 p2').
Proof. exact (@lem1331566 (term128 p1 p1' p2 p2')). Qed.
Lemma lem1331568 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term127 p1 p1' p2 p2') = (term146 p1 p1' p2 p2').
Proof. exact (MK_COMB (@lem1331564 p1 p2' p2 p1') (@lem1331567 p1 p1' p2 p2')). Qed.
Lemma lem1331569 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term129 p1 p1' p2 p2') = (term147 p1 p1' p2 p2').
Proof. exact (MK_COMB (@lem1331559 p2 p1 p2' p1') (@lem1331568 p1 p1' p2 p2')). Qed.
Lemma lem1331572 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term147 p1 p1' p2 p2') = (term129 p1 p1' p2 p2').
Proof. exact (SYM (@lem1331569 p1 p1' p2 p2')). Qed.
Lemma lem1331573 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (h1 : term140 p2 p1 p2' p1') : term140 p2 p1 p2' p1'.
Proof. exact (h1). Qed.
Lemma lem1331574 (p2' : hreal) (p1' : hreal) (h1 : hreal_le p2' p1') : hreal_le p2' p1'.
Proof. exact (h1). Qed.
Lemma lem1331575 (p2 : hreal) (p1 : hreal) (h1 : hreal_le p2 p1) : hreal_le p2 p1.
Proof. exact (h1). Qed.
Lemma lem1331576 (p2' : hreal) (p1' : hreal) (h1 : hreal_le p2' p1') : hreal_le p2' p1'.
Proof. exact (h1). Qed.
Lemma lem1331578 (y : hreal) (x : hreal) : term46 y x.
Proof. exact (EQ_MP (@lem1331335 y x) (@lem1331334 x y)). Qed.
Lemma lem1331579 (p1' : hreal) (p2' : hreal) : term46 p1' p2'.
Proof. exact (@lem1331578 p1' p2'). Qed.
Lemma lem1331580 (p2' : hreal) (p1' : hreal) (h1 : hreal_le p2' p1') : term148 p1' p2'.
Proof. exact (@lem1331579 p1' p2' (@lem1331576 p2' p1' h1)). Qed.
Lemma lem1331581 (p1' : hreal) (p2' : hreal) (d : hreal) (h1 : p1' = (hreal_add p2' d)) : p1' = (hreal_add p2' d).
Proof. exact (h1). Qed.
Lemma lem1331582 (p1 : hreal) (p2 : hreal) (p2' : hreal) : (term149 p1 p2 p2') = (term149 p1 p2 p2').
Proof. exact (eq_refl (term149 p1 p2 p2')). Qed.
Lemma lem1331583 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (d : hreal) (h1 : p1' = (hreal_add p2' d)) : (term150 p1 p2 p2' p1') = (term151 p1 p2 p2' d).
Proof. exact (MK_COMB (@lem1331582 p1 p2 p2') (@lem1331581 p1' p2' d h1)). Qed.
Lemma lem1331584 (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : (term151 p1 p2 p2' d) = (term152 p1 d p2 p2').
Proof. exact (eq_refl (term151 p1 p2 p2' d)). Qed.
Lemma lem1331585 (p1 : hreal) (p2 : hreal) (p2' : hreal) (p1' : hreal) : (term153 p1 p2 p2' p1') = (term153 p1 p2 p2' p1').
Proof. exact (eq_refl (term153 p1 p2 p2' p1')). Qed.
Lemma lem1331586 (p1' : hreal) (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : ((term150 p1 p2 p2' p1') = (term151 p1 p2 p2' d)) = ((term150 p1 p2 p2' p1') = (term152 p1 d p2 p2')).
Proof. exact (MK_COMB (@lem1331585 p1 p2 p2' p1') (@lem1331584 p1 d p2 p2')). Qed.
Lemma lem1331587 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term150 p1 p2 p2' p1') = (term146 p1 p1' p2 p2').
Proof. exact (eq_refl (term150 p1 p2 p2' p1')). Qed.
Lemma lem1331588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1331589 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term153 p1 p2 p2' p1') = (term154 p1 p1' p2 p2').
Proof. exact (MK_COMB (@lem1331588) (@lem1331587 p1 p1' p2 p2')). Qed.
Lemma lem1331590 (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : (term152 p1 d p2 p2') = (term152 p1 d p2 p2').
Proof. exact (eq_refl (term152 p1 d p2 p2')). Qed.
Lemma lem1331591 (p1' : hreal) (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : ((term150 p1 p2 p2' p1') = (term152 p1 d p2 p2')) = ((term146 p1 p1' p2 p2') = (term152 p1 d p2 p2')).
Proof. exact (MK_COMB (@lem1331589 p1 p1' p2 p2') (@lem1331590 p1 d p2 p2')). Qed.
Lemma lem1331592 (p1' : hreal) (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : ((term150 p1 p2 p2' p1') = (term151 p1 p2 p2' d)) = ((term146 p1 p1' p2 p2') = (term152 p1 d p2 p2')).
Proof. exact (TRANS (@lem1331586 p1' p1 d p2 p2') (@lem1331591 p1' p1 d p2 p2')). Qed.
Lemma lem1331593 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (d : hreal) (h1 : p1' = (hreal_add p2' d)) : (term146 p1 p1' p2 p2') = (term152 p1 d p2 p2').
Proof. exact (EQ_MP (@lem1331592 p1' p1 d p2 p2') (@lem1331583 p1 p2 p1' p2' d h1)). Qed.
Lemma lem1331594 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (d : hreal) (h1 : p1' = (hreal_add p2' d)) : (term152 p1 d p2 p2') = (term146 p1 p1' p2 p2').
Proof. exact (SYM (@lem1331593 p1 p2 p1' p2' d h1)). Qed.
Lemma lem1331598 (y : hreal) (x : hreal) (z : hreal) : (term41 x y z) = (term42 y x z).
Proof. exact (EQ_MP (@lem1331329 y x z) (@lem1331328 y x z)). Qed.
Lemma lem1331599 (p2' : hreal) (p2 : hreal) (d : hreal) : (term41 p2 p2' d) = (term42 p2' p2 d).
Proof. exact (@lem1331598 p2' p2 d). Qed.
Lemma lem1331600 (p1 : hreal) (p2' : hreal) : (term155 p1 p2') = (term155 p1 p2').
Proof. exact (eq_refl (term155 p1 p2')). Qed.
Lemma lem1331601 (p1 : hreal) (p2' : hreal) (p2 : hreal) (d : hreal) : (term156 p1 p2 p2' d) = (term157 p1 p2' p2 d).
Proof. exact (MK_COMB (@lem1331600 p1 p2') (@lem1331599 p2' p2 d)). Qed.
Lemma lem1331602 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1331603 (p1 : hreal) (p2' : hreal) (p2 : hreal) (d : hreal) : (term158 p1 p2 p2' d) = (term159 p1 p2' p2 d).
Proof. exact (MK_COMB (@lem1331602) (@lem1331601 p1 p2' p2 d)). Qed.
Lemma lem1331605 (y : hreal) (x : hreal) (z : hreal) : (term41 x y z) = (term42 y x z).
Proof. exact (EQ_MP (@lem1331329 y x z) (@lem1331328 y x z)). Qed.
Lemma lem1331606 (p2' : hreal) (p1 : hreal) (d : hreal) : (term41 p1 p2' d) = (term42 p2' p1 d).
Proof. exact (@lem1331605 p2' p1 d). Qed.
Lemma lem1331607 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1331608 (p2' : hreal) (p1 : hreal) (d : hreal) : (term160 p1 p2' d) = (term161 p2' p1 d).
Proof. exact (MK_COMB (@lem1331607) (@lem1331606 p2' p1 d)). Qed.
Lemma lem1331609 (p2 : hreal) (p2' : hreal) : (hreal_mul p2 p2') = (hreal_mul p2 p2').
Proof. exact (eq_refl (hreal_mul p2 p2')). Qed.
Lemma lem1331610 (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : (term162 p1 d p2 p2') = (term163 p1 d p2 p2').
Proof. exact (MK_COMB (@lem1331608 p2' p1 d) (@lem1331609 p2 p2')). Qed.
Lemma lem1331612 (x : hreal) (y : hreal) (z : hreal) : (term14 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem1331311 x y z) (@lem1331310 x y z)). Qed.
Lemma lem1331613 (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : (term163 p1 d p2 p2') = (term164 p1 d p2 p2').
Proof. exact (@lem1331612 (hreal_mul p1 p2') (hreal_mul p1 d) (hreal_mul p2 p2')). Qed.
Lemma lem1331614 (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : (term162 p1 d p2 p2') = (term164 p1 d p2 p2').
Proof. exact (TRANS (@lem1331610 p1 d p2 p2') (@lem1331613 p1 d p2 p2')). Qed.
Lemma lem1331615 (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : (term152 p1 d p2 p2') = (term165 p1 d p2 p2').
Proof. exact (MK_COMB (@lem1331603 p1 p2' p2 d) (@lem1331614 p1 d p2 p2')). Qed.
Lemma lem1331617 (m : hreal) (n : hreal) (p : hreal) : (term35 n m p) = (hreal_le n p).
Proof. exact (EQ_MP (@lem1331320 m n p) (@lem1331319 m n p)). Qed.
Lemma lem1331618 (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : (term165 p1 d p2 p2') = (term166 p1 d p2 p2').
Proof. exact (@lem1331617 (hreal_mul p1 p2') (term42 p2' p2 d) (term128 p1 d p2 p2')). Qed.
Lemma lem1331621 (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : (term152 p1 d p2 p2') = (term166 p1 d p2 p2').
Proof. exact (TRANS (@lem1331615 p1 d p2 p2') (@lem1331618 p1 d p2 p2')). Qed.
Lemma lem1331622 (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : (term166 p1 d p2 p2') = (term152 p1 d p2 p2').
Proof. exact (SYM (@lem1331621 p1 d p2 p2')). Qed.
Lemma lem1331624 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1331284 y x) (@lem1331283 x y)). Qed.
Lemma lem1331625 (p2 : hreal) (p2' : hreal) (p1 : hreal) (d : hreal) : (term128 p1 d p2 p2') = (term128 p2 p2' p1 d).
Proof. exact (@lem1331624 (hreal_mul p2 p2') (hreal_mul p1 d)). Qed.
Lemma lem1331626 (p2' : hreal) (p2 : hreal) (d : hreal) : (term167 p2' p2 d) = (term167 p2' p2 d).
Proof. exact (eq_refl (term167 p2' p2 d)). Qed.
Lemma lem1331627 (p2 : hreal) (p2' : hreal) (p1 : hreal) (d : hreal) : (term166 p1 d p2 p2') = (term168 p2 p2' p1 d).
Proof. exact (MK_COMB (@lem1331626 p2' p2 d) (@lem1331625 p2 p2' p1 d)). Qed.
Lemma lem1331628 (p1 : hreal) (d : hreal) (p2 : hreal) (p2' : hreal) : (term168 p2 p2' p1 d) = (term166 p1 d p2 p2').
Proof. exact (SYM (@lem1331627 p2 p2' p1 d)). Qed.
Lemma lem1331629 (m : hreal) : term30 m.
Proof. exact (@lem1321588 m). Qed.
Lemma lem1331630 (m : hreal) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem1331631 (m : hreal) : term31 m.
Proof. exact (EQ_MP (@lem1331630 m) (@lem1331629 m)). Qed.
Lemma lem1331632 (m : hreal) (n : hreal) : term32 m n.
Proof. exact (@lem1331631 m n). Qed.
Lemma lem1331633 (m : hreal) (n : hreal) : (term32 m n) = (term33 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1331634 (m : hreal) (n : hreal) : term33 m n.
Proof. exact (EQ_MP (@lem1331633 m n) (@lem1331632 m n)). Qed.
Lemma lem1331635 (m : hreal) (n : hreal) (p : hreal) : term34 m n p.
Proof. exact (@lem1331634 m n p). Qed.
Lemma lem1331636 (m : hreal) (n : hreal) (p : hreal) : (term34 m n p) = ((term35 n m p) = (hreal_le n p)).
Proof. exact (eq_refl (term34 m n p)). Qed.
Lemma lem1331641 (m : hreal) (n : hreal) (p : hreal) : (term35 n m p) = (hreal_le n p).
Proof. exact (EQ_MP (@lem1331636 m n p) (@lem1331635 m n p)). Qed.
Lemma lem1331642 (p2' : hreal) (p2 : hreal) (p1 : hreal) (d : hreal) : (term168 p2 p2' p1 d) = (term7 p2 p1 d).
Proof. exact (@lem1331641 (hreal_mul p2 p2') (hreal_mul p2 d) (hreal_mul p1 d)). Qed.
Lemma lem1331643 (p2 : hreal) (p2' : hreal) (p1 : hreal) (d : hreal) : (term7 p2 p1 d) = (term168 p2 p2' p1 d).
Proof. exact (SYM (@lem1331642 p2' p2 p1 d)). Qed.
Lemma lem1331645 (a : hreal) (b : hreal) (c : hreal) : term6 a b c.
Proof. exact (EQ_MP (@lem1331278 a b c) (@lem1331277 a b c)). Qed.
Lemma lem1331646 (p2 : hreal) (p1 : hreal) (d : hreal) : term6 p2 p1 d.
Proof. exact (@lem1331645 p2 p1 d). Qed.
Lemma lem1331647 (p2 : hreal) (p1 : hreal) : (hreal_le p2 p1) = ((hreal_le p2 p1) = True).
Proof. exact (@lem7 (hreal_le p2 p1)). Qed.
Lemma lem1331650 (p2 : hreal) (p1 : hreal) (h1 : hreal_le p2 p1) : (hreal_le p2 p1) = True.
Proof. exact (EQ_MP (@lem1331647 p2 p1) (@lem1331575 p2 p1 h1)). Qed.
Lemma lem1331651 (p2 : hreal) (p1 : hreal) (h1 : hreal_le p2 p1) : True = (hreal_le p2 p1).
Proof. exact (SYM (@lem1331650 p2 p1 h1)). Qed.
Lemma lem1331652 (p2 : hreal) (p1 : hreal) (h1 : hreal_le p2 p1) : hreal_le p2 p1.
Proof. exact (EQ_MP (@lem1331651 p2 p1 h1) (@lem0)). Qed.
Lemma lem1331653 (d : hreal) (p2 : hreal) (p1 : hreal) (h1 : hreal_le p2 p1) : term7 p2 p1 d.
Proof. exact (@lem1331646 p2 p1 d (@lem1331652 p2 p1 h1)). Qed.
Lemma lem1331654 (p2' : hreal) (d : hreal) (p2 : hreal) (p1 : hreal) (h1 : hreal_le p2 p1) : term168 p2 p2' p1 d.
Proof. exact (EQ_MP (@lem1331643 p2 p2' p1 d) (@lem1331653 d p2 p1 h1)). Qed.
Lemma lem1331655 (d : hreal) (p2' : hreal) (p2 : hreal) (p1 : hreal) (h1 : hreal_le p2 p1) : term166 p1 d p2 p2'.
Proof. exact (EQ_MP (@lem1331628 p1 d p2 p2') (@lem1331654 p2' d p2 p1 h1)). Qed.
Lemma lem1331656 (d : hreal) (p2' : hreal) (p2 : hreal) (p1 : hreal) (h1 : hreal_le p2 p1) : term152 p1 d p2 p2'.
Proof. exact (EQ_MP (@lem1331622 p1 d p2 p2') (@lem1331655 d p2' p2 p1 h1)). Qed.
Lemma lem1331657 (p1' : hreal) (p2' : hreal) (d : hreal) (p2 : hreal) (p1 : hreal) (h1 : p1' = (hreal_add p2' d)) (h2 : hreal_le p2 p1) : term146 p1 p1' p2 p2'.
Proof. exact (EQ_MP (@lem1331594 p1 p2 p1' p2' d h1) (@lem1331656 d p2' p2 p1 h2)). Qed.
Lemma lem1331658 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (h1 : hreal_le p2 p1) (h2 : hreal_le p2' p1') : term146 p1 p1' p2 p2'.
Proof. exact (ex_elim (@lem1331580 p2' p1' h2) (fun d : hreal => fun h0 : term169 p1' p2' d => @lem1331657 p1' p2' d p2 p1 h0 h1)). Qed.
Lemma lem1331659 (p1' : hreal) (p2' : hreal) (p2 : hreal) (p1 : hreal) (h1 : hreal_le p2 p1) : term170 p1 p1' p2 p2'.
Proof. exact (fun h0 : hreal_le p2' p1' => @lem1331658 p2 p1 p2' p1' h1 h0). Qed.
Lemma lem1331660 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (h1 : term140 p2 p1 p2' p1') : hreal_le p2' p1'.
Proof. exact (proj2 (@lem1331573 p2 p1 p2' p1' h1)). Qed.
Lemma lem1331661 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (h1 : term140 p2 p1 p2' p1') : hreal_le p2 p1.
Proof. exact (proj1 (@lem1331573 p2 p1 p2' p1' h1)). Qed.
Lemma lem1331662 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (h1 : hreal_le p2 p1) (h2 : hreal_le p2' p1') : term146 p1 p1' p2 p2'.
Proof. exact (@lem1331659 p1' p2' p2 p1 h1 (@lem1331574 p2' p1' h2)). Qed.
Lemma lem1331663 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (h1 : hreal_le p2 p1) (h2 : hreal_le p2' p1') : (hreal_le p2 p1) = (term146 p1 p1' p2 p2').
Proof. exact (prop_ext (fun h3 : hreal_le p2 p1 => @lem1331662 p2 p1 p2' p1' h1 h2) (fun h3 : term146 p1 p1' p2 p2' => @lem1331575 p2 p1 h1)). Qed.
Lemma lem1331664 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (h1 : hreal_le p2 p1) (h2 : hreal_le p2' p1') : term146 p1 p1' p2 p2'.
Proof. exact (EQ_MP (@lem1331663 p2 p1 p2' p1' h1 h2) (@lem1331575 p2 p1 h1)). Qed.
Lemma lem1331665 (p2' : hreal) (p1' : hreal) (p2 : hreal) (p1 : hreal) (h1 : term140 p2 p1 p2' p1') (h2 : hreal_le p2 p1) : (hreal_le p2' p1') = (term146 p1 p1' p2 p2').
Proof. exact (prop_ext (fun h3 : hreal_le p2' p1' => @lem1331664 p2 p1 p2' p1' h2 h3) (fun h3 : term146 p1 p1' p2 p2' => @lem1331660 p2 p1 p2' p1' h1)). Qed.
Lemma lem1331666 (p2' : hreal) (p1' : hreal) (p2 : hreal) (p1 : hreal) (h1 : term140 p2 p1 p2' p1') (h2 : hreal_le p2 p1) : term146 p1 p1' p2 p2'.
Proof. exact (EQ_MP (@lem1331665 p2' p1' p2 p1 h1 h2) (@lem1331660 p2 p1 p2' p1' h1)). Qed.
Lemma lem1331667 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (h1 : term140 p2 p1 p2' p1') : (hreal_le p2 p1) = (term146 p1 p1' p2 p2').
Proof. exact (prop_ext (fun h2 : hreal_le p2 p1 => @lem1331666 p2' p1' p2 p1 h1 h2) (fun h2 : term146 p1 p1' p2 p2' => @lem1331661 p2 p1 p2' p1' h1)). Qed.
Lemma lem1331668 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) (h1 : term140 p2 p1 p2' p1') : term146 p1 p1' p2 p2'.
Proof. exact (EQ_MP (@lem1331667 p2 p1 p2' p1' h1) (@lem1331661 p2 p1 p2' p1' h1)). Qed.
Lemma lem1331669 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : term147 p1 p1' p2 p2'.
Proof. exact (fun h0 : term140 p2 p1 p2' p1' => @lem1331668 p2 p1 p2' p1' h0). Qed.
Lemma lem1331670 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : term129 p1 p1' p2 p2'.
Proof. exact (EQ_MP (@lem1331572 p1 p1' p2 p2') (@lem1331669 p1 p1' p2 p2')). Qed.
Lemma lem1331675 (p1 : hreal) (p1' : hreal) (p2 : hreal) : term131 p1 p1' p2.
Proof. exact (fun p2' : hreal => @lem1331670 p1 p1' p2 p2'). Qed.
Lemma lem1331680 (p1 : hreal) (p2 : hreal) : term133 p1 p2.
Proof. exact (fun p1' : hreal => @lem1331675 p1 p1' p2). Qed.
Lemma lem1331685 (p1 : hreal) : term135 p1.
Proof. exact (fun p2 : hreal => @lem1331680 p1 p2). Qed.
Lemma lem1331690 : term137.
Proof. exact (fun p1 : hreal => @lem1331685 p1). Qed.
Lemma lem1331691 : term82.
Proof. exact (EQ_MP (@lem1331530) (@lem1331690)). Qed.
