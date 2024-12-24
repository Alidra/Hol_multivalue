Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVMOD_UNIQ_LEMMA_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_RCANCEL_spec.
Require Import EQ_MULT_RCANCEL_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_0_spec.
Require Import LE_ADD_spec.
Require Import LE_CASES_spec.
Require Import LE_EXISTS_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_SYM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem168236 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem168237 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem168236 n m h1)). Qed.
Lemma lem168238 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem168239 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem168238 m n h1)). Qed.
Lemma lem168240 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem168237 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem168239 m n h1)). Qed.
Lemma lem168241 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem168240 m n)). Qed.
Lemma lem168242 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168243 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem168242) (@lem168241 m)). Qed.
Lemma lem168244 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem168243 m)). Qed.
Lemma lem168245 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168246 : term7 = term8.
Proof. exact (MK_COMB (@lem168245) (@lem168244)). Qed.
Lemma lem168247 : term8.
Proof. exact (EQ_MP (@lem168246) (@lem97961)). Qed.
Lemma lem168248 (n : nat) : term9 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem168249 (n : nat) : (term9 n) = (term10 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem168250 (n : nat) : term10 n.
Proof. exact (EQ_MP (@lem168249 n) (@lem168248 n)). Qed.
Lemma lem168252 (n : nat) (h1 : term11 n) : term11 n.
Proof. exact (h1). Qed.
Lemma lem168256 (m : nat) (n : nat) (p : nat) (h1 : (term12 m n p) = (term13 m n p)) : (term12 m n p) = (term13 m n p).
Proof. exact (h1). Qed.
Lemma lem168257 (m : nat) (n : nat) (p : nat) (h1 : (term12 m n p) = (term13 m n p)) : (term13 m n p) = (term12 m n p).
Proof. exact (SYM (@lem168256 m n p h1)). Qed.
Lemma lem168258 (m : nat) (n : nat) (p : nat) (h1 : (term13 m n p) = (term12 m n p)) : (term13 m n p) = (term12 m n p).
Proof. exact (h1). Qed.
Lemma lem168259 (m : nat) (n : nat) (p : nat) (h1 : (term13 m n p) = (term12 m n p)) : (term12 m n p) = (term13 m n p).
Proof. exact (SYM (@lem168258 m n p h1)). Qed.
Lemma lem168260 (m : nat) (n : nat) (p : nat) : ((term12 m n p) = (term13 m n p)) = ((term13 m n p) = (term12 m n p)).
Proof. exact (prop_ext (fun h1 : (term12 m n p) = (term13 m n p) => @lem168257 m n p h1) (fun h1 : (term13 m n p) = (term12 m n p) => @lem168259 m n p h1)). Qed.
Lemma lem168261 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (fun_ext (fun p : nat => @lem168260 m n p)). Qed.
Lemma lem168262 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168263 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (MK_COMB (@lem168262) (@lem168261 m n)). Qed.
Lemma lem168264 (m : nat) : (term18 m) = (term19 m).
Proof. exact (fun_ext (fun n : nat => @lem168263 m n)). Qed.
Lemma lem168265 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168266 (m : nat) : (term20 m) = (term21 m).
Proof. exact (MK_COMB (@lem168265) (@lem168264 m)). Qed.
Lemma lem168267 : term22 = term23.
Proof. exact (fun_ext (fun m : nat => @lem168266 m)). Qed.
Lemma lem168268 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168269 : term24 = term25.
Proof. exact (MK_COMB (@lem168268) (@lem168267)). Qed.
Lemma lem168270 : term25.
Proof. exact (EQ_MP (@lem168269) (@lem77960)). Qed.
Lemma lem168273 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem168274 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem168273 n m h1)). Qed.
Lemma lem168275 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem168276 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem168275 m n h1)). Qed.
Lemma lem168277 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem168274 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem168276 m n h1)). Qed.
Lemma lem168278 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem168277 m n)). Qed.
Lemma lem168279 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168280 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem168279) (@lem168278 m)). Qed.
Lemma lem168281 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem168280 m)). Qed.
Lemma lem168282 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168283 : term7 = term8.
Proof. exact (MK_COMB (@lem168282) (@lem168281)). Qed.
Lemma lem168284 : term8.
Proof. exact (EQ_MP (@lem168283) (@lem97961)). Qed.
Lemma lem168285 (m : nat) : term26 m.
Proof. exact (@lem168270 m). Qed.
Lemma lem168286 (m : nat) : (term26 m) = (term21 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem168287 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem168286 m) (@lem168285 m)). Qed.
Lemma lem168288 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem168287 m n). Qed.
Lemma lem168289 (m : nat) (n : nat) : (term27 m n) = (term17 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem168290 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem168289 m n) (@lem168288 m n)). Qed.
Lemma lem168291 (m : nat) (n : nat) (p : nat) : term28 m n p.
Proof. exact (@lem168290 m n p). Qed.
Lemma lem168292 (m : nat) (n : nat) (p : nat) : (term28 m n p) = ((term13 m n p) = (term12 m n p)).
Proof. exact (eq_refl (term28 m n p)). Qed.
Lemma lem168294 (m : nat) : term29 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem168295 (m : nat) : (term29 m) = (term30 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem168296 (m : nat) : term30 m.
Proof. exact (EQ_MP (@lem168295 m) (@lem168294 m)). Qed.
Lemma lem168297 (m : nat) (n : nat) : term31 m n.
Proof. exact (@lem168296 m n). Qed.
Lemma lem168298 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem168299 (m : nat) (n : nat) : term32 m n.
Proof. exact (EQ_MP (@lem168298 m n) (@lem168297 m n)). Qed.
Lemma lem168300 (m : nat) (n : nat) : (term32 m n) = ((term32 m n) = True).
Proof. exact (@lem7 (term32 m n)). Qed.
Lemma lem168302 (m : nat) : term33 m.
Proof. exact (@lem168284 m). Qed.
Lemma lem168303 (m : nat) : (term33 m) = (term4 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem168304 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem168303 m) (@lem168302 m)). Qed.
Lemma lem168305 (m : nat) (n : nat) : term34 m n.
Proof. exact (@lem168304 m n). Qed.
Lemma lem168306 (m : nat) (n : nat) : (term34 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem168308 : term35.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem168309 : term36.
Proof. exact (proj2 (@lem168308)). Qed.
Lemma lem168310 : term37.
Proof. exact (proj2 (@lem168309)). Qed.
Lemma lem168311 : term38.
Proof. exact (proj2 (@lem168310)). Qed.
Lemma lem168312 : term39.
Proof. exact (proj2 (@lem168311)). Qed.
Lemma lem168313 (m : nat) : term40 m.
Proof. exact (@lem168312 m). Qed.
Lemma lem168314 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem168315 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem168314 m) (@lem168313 m)). Qed.
Lemma lem168316 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem168315 m n). Qed.
Lemma lem168317 (m : nat) (n : nat) : (term42 m n) = ((term43 m n) = (term44 m n)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem168334 : term45.
Proof. exact (proj1 (@lem168308)). Qed.
Lemma lem168335 (m : nat) : term46 m.
Proof. exact (@lem168334 m). Qed.
Lemma lem168336 (m : nat) : (term46 m) = ((term47 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem168362 : term48.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem168363 (n : nat) : term49 n.
Proof. exact (@lem168362 n). Qed.
Lemma lem168364 (n : nat) : (term49 n) = ((term50 n) = n).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem168366 (m : nat) : term51 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem168367 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem168368 (m : nat) : term52 m.
Proof. exact (EQ_MP (@lem168367 m) (@lem168366 m)). Qed.
Lemma lem168369 (m : nat) (n : nat) : term53 m n.
Proof. exact (@lem168368 m n). Qed.
Lemma lem168370 (n : nat) (m : nat) : (term53 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem168375 (m : nat) (n : nat) (p : nat) (h1 : (term12 m n p) = (term13 m n p)) : (term12 m n p) = (term13 m n p).
Proof. exact (h1). Qed.
Lemma lem168376 (m : nat) (n : nat) (p : nat) (h1 : (term12 m n p) = (term13 m n p)) : (term13 m n p) = (term12 m n p).
Proof. exact (SYM (@lem168375 m n p h1)). Qed.
Lemma lem168377 (m : nat) (n : nat) (p : nat) (h1 : (term13 m n p) = (term12 m n p)) : (term13 m n p) = (term12 m n p).
Proof. exact (h1). Qed.
Lemma lem168378 (m : nat) (n : nat) (p : nat) (h1 : (term13 m n p) = (term12 m n p)) : (term12 m n p) = (term13 m n p).
Proof. exact (SYM (@lem168377 m n p h1)). Qed.
Lemma lem168379 (m : nat) (n : nat) (p : nat) : ((term12 m n p) = (term13 m n p)) = ((term13 m n p) = (term12 m n p)).
Proof. exact (prop_ext (fun h1 : (term12 m n p) = (term13 m n p) => @lem168376 m n p h1) (fun h1 : (term13 m n p) = (term12 m n p) => @lem168378 m n p h1)). Qed.
Lemma lem168380 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (fun_ext (fun p : nat => @lem168379 m n p)). Qed.
Lemma lem168381 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168382 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (MK_COMB (@lem168381) (@lem168380 m n)). Qed.
Lemma lem168383 (m : nat) : (term18 m) = (term19 m).
Proof. exact (fun_ext (fun n : nat => @lem168382 m n)). Qed.
Lemma lem168384 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168385 (m : nat) : (term20 m) = (term21 m).
Proof. exact (MK_COMB (@lem168384) (@lem168383 m)). Qed.
Lemma lem168386 : term22 = term23.
Proof. exact (fun_ext (fun m : nat => @lem168385 m)). Qed.
Lemma lem168387 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168388 : term24 = term25.
Proof. exact (MK_COMB (@lem168387) (@lem168386)). Qed.
Lemma lem168389 : term25.
Proof. exact (EQ_MP (@lem168388) (@lem77960)). Qed.
Lemma lem168390 (m : nat) : term54 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem168391 (m : nat) : (term54 m) = (term55 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem168392 (m : nat) : term55 m.
Proof. exact (EQ_MP (@lem168391 m) (@lem168390 m)). Qed.
Lemma lem168393 (m : nat) (n : nat) : term56 m n.
Proof. exact (@lem168392 m n). Qed.
Lemma lem168394 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem168395 (m : nat) (n : nat) : term57 m n.
Proof. exact (EQ_MP (@lem168394 m n) (@lem168393 m n)). Qed.
Lemma lem168396 (m : nat) (n : nat) (p : nat) : term58 m n p.
Proof. exact (@lem168395 m n p). Qed.
Lemma lem168397 (m : nat) (n : nat) (p : nat) : (term58 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term58 m n p)). Qed.
Lemma lem168399 (m : nat) : term26 m.
Proof. exact (@lem168389 m). Qed.
Lemma lem168400 (m : nat) : (term26 m) = (term21 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem168401 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem168400 m) (@lem168399 m)). Qed.
Lemma lem168402 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem168401 m n). Qed.
Lemma lem168403 (m : nat) (n : nat) : (term27 m n) = (term17 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem168404 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem168403 m n) (@lem168402 m n)). Qed.
Lemma lem168405 (m : nat) (n : nat) (p : nat) : term28 m n p.
Proof. exact (@lem168404 m n p). Qed.
Lemma lem168406 (m : nat) (n : nat) (p : nat) : (term28 m n p) = ((term13 m n p) = (term12 m n p)).
Proof. exact (eq_refl (term28 m n p)). Qed.
Lemma lem168408 (m : nat) : term59 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem168409 (m : nat) : (term59 m) = (term60 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem168410 (m : nat) : term60 m.
Proof. exact (EQ_MP (@lem168409 m) (@lem168408 m)). Qed.
Lemma lem168411 (m : nat) (n : nat) : term61 m n.
Proof. exact (@lem168410 m n). Qed.
Lemma lem168412 (m : nat) (n : nat) : (term61 m n) = (term62 m n).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem168413 (m : nat) (n : nat) : term62 m n.
Proof. exact (EQ_MP (@lem168412 m n) (@lem168411 m n)). Qed.
Lemma lem168414 (m : nat) (n : nat) (p : nat) : term63 m n p.
Proof. exact (@lem168413 m n p). Qed.
Lemma lem168415 (m : nat) (n : nat) (p : nat) : (term63 m n p) = ((term64 m n p) = (term65 m n p)).
Proof. exact (eq_refl (term63 m n p)). Qed.
Lemma lem168417 (m : nat) : term66 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem168418 (m : nat) : (term66 m) = (term67 m).
Proof. exact (eq_refl (term66 m)). Qed.
Lemma lem168419 (m : nat) : term67 m.
Proof. exact (EQ_MP (@lem168418 m) (@lem168417 m)). Qed.
Lemma lem168420 (m : nat) (n : nat) : term68 m n.
Proof. exact (@lem168419 m n). Qed.
Lemma lem168421 (n : nat) (m : nat) : (term68 m n) = ((Peano.le m n) = (term69 n m)).
Proof. exact (eq_refl (term68 m n)). Qed.
Lemma lem168423 (q1 : nat) : term70 q1.
Proof. exact (@lem96155 q1). Qed.
Lemma lem168424 (q1 : nat) : (term70 q1) = (term71 q1).
Proof. exact (eq_refl (term70 q1)). Qed.
Lemma lem168425 (q1 : nat) : term71 q1.
Proof. exact (EQ_MP (@lem168424 q1) (@lem168423 q1)). Qed.
Lemma lem168426 (q1 : nat) (q2 : nat) : term72 q1 q2.
Proof. exact (@lem168425 q1 q2). Qed.
Lemma lem168427 (q2 : nat) (q1 : nat) : (term72 q1 q2) = (term73 q2 q1).
Proof. exact (eq_refl (term72 q1 q2)). Qed.
Lemma lem168428 (q2 : nat) (q1 : nat) : term73 q2 q1.
Proof. exact (EQ_MP (@lem168427 q2 q1) (@lem168426 q1 q2)). Qed.
Lemma lem168429 (q1 : nat) (q2 : nat) (h1 : Peano.le q1 q2) : Peano.le q1 q2.
Proof. exact (h1). Qed.
Lemma lem168430 (q2 : nat) (q1 : nat) (h1 : Peano.le q2 q1) : Peano.le q2 q1.
Proof. exact (h1). Qed.
Lemma lem168431 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term74 q1 r1 m q2 r2 n) : term74 q1 r1 m q2 r2 n.
Proof. exact (h1). Qed.
Lemma lem168432 (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term75 m q2 r2 n) : term75 m q2 r2 n.
Proof. exact (h1). Qed.
Lemma lem168433 (m : nat) (q1 : nat) (r1 : nat) (n : nat) (h1 : term75 m q1 r1 n) : term75 m q1 r1 n.
Proof. exact (h1). Qed.
Lemma lem168434 (r1 : nat) (n : nat) (h1 : Peano.lt r1 n) : Peano.lt r1 n.
Proof. exact (h1). Qed.
Lemma lem168435 (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : m = (term76 q1 n r1)) : m = (term76 q1 n r1).
Proof. exact (h1). Qed.
Lemma lem168436 (r2 : nat) (n : nat) (h1 : Peano.lt r2 n) : Peano.lt r2 n.
Proof. exact (h1). Qed.
Lemma lem168437 (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : m = (term76 q2 n r2)) : m = (term76 q2 n r2).
Proof. exact (h1). Qed.
Lemma lem168438 (r1 : nat) (r2 : nat) (h1 : r1 = r2) : r1 = r2.
Proof. exact (h1). Qed.
Lemma lem168450 (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : m = (term76 q1 n r1)) : m = (term76 q1 n r1).
Proof. exact (h1). Qed.
Lemma lem168451 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem168452 (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : m = (term76 q1 n r1)) : (@eq nat m) = (term77 q1 n r1).
Proof. exact (MK_COMB (@lem168451) (@lem168450 m q1 n r1 h1)). Qed.
Lemma lem168453 (q2 : nat) (n : nat) (r2 : nat) : (term76 q2 n r2) = (term76 q2 n r2).
Proof. exact (eq_refl (term76 q2 n r2)). Qed.
Lemma lem168454 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : m = (term76 q1 n r1)) : (m = (term76 q2 n r2)) = ((term76 q1 n r1) = (term76 q2 n r2)).
Proof. exact (MK_COMB (@lem168452 m q1 n r1 h1) (@lem168453 q2 n r2)). Qed.
Lemma lem168457 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168458 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : m = (term76 q1 n r1)) : (term78 m q2 n r2) = (term79 q1 r1 q2 n r2).
Proof. exact (MK_COMB (@lem168457) (@lem168454 q2 r2 m q1 n r1 h1)). Qed.
Lemma lem168461 (r1 : nat) (r2 : nat) : (r1 = r2) = (r1 = r2).
Proof. exact (eq_refl (r1 = r2)). Qed.
Lemma lem168462 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : m = (term76 q1 n r1)) : (term80 m q2 n r1 r2) = (term81 q1 q2 n r1 r2).
Proof. exact (MK_COMB (@lem168458 q2 r2 m q1 n r1 h1) (@lem168461 r1 r2)). Qed.
Lemma lem168467 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : m = (term76 q1 n r1)) : (term81 q1 q2 n r1 r2) = (term80 m q2 n r1 r2).
Proof. exact (SYM (@lem168462 q2 r2 m q1 n r1 h1)). Qed.
Lemma lem168468 (q1 : nat) (q2 : nat) (h1 : Peano.le q1 q2) : Peano.le q1 q2.
Proof. exact (h1). Qed.
Lemma lem168470 (n : nat) (m : nat) : (Peano.le m n) = (term69 n m).
Proof. exact (EQ_MP (@lem168421 n m) (@lem168420 m n)). Qed.
Lemma lem168471 (q2 : nat) (q1 : nat) : (Peano.le q1 q2) = (term69 q2 q1).
Proof. exact (@lem168470 q2 q1). Qed.
Lemma lem168478 (q1 : nat) (q2 : nat) (h1 : Peano.le q1 q2) : term69 q2 q1.
Proof. exact (EQ_MP (@lem168471 q2 q1) (@lem168468 q1 q2 h1)). Qed.
Lemma lem168479 (q2 : nat) (q1 : nat) (d : nat) (h1 : q2 = (Nat.add q1 d)) : q2 = (Nat.add q1 d).
Proof. exact (h1). Qed.
Lemma lem168480 (q1 : nat) (n : nat) (r1 : nat) (r2 : nat) : (term82 q1 n r1 r2) = (term82 q1 n r1 r2).
Proof. exact (eq_refl (term82 q1 n r1 r2)). Qed.
Lemma lem168481 (n : nat) (r1 : nat) (r2 : nat) (q2 : nat) (q1 : nat) (d : nat) (h1 : q2 = (Nat.add q1 d)) : (term83 q1 n r1 r2 q2) = (term84 n r1 r2 q1 d).
Proof. exact (MK_COMB (@lem168480 q1 n r1 r2) (@lem168479 q2 q1 d h1)). Qed.
Lemma lem168482 (q1 : nat) (d : nat) (n : nat) (r1 : nat) (r2 : nat) : (term84 n r1 r2 q1 d) = (term85 q1 d n r1 r2).
Proof. exact (eq_refl (term84 n r1 r2 q1 d)). Qed.
Lemma lem168483 (q1 : nat) (n : nat) (r1 : nat) (r2 : nat) (q2 : nat) : (term86 q1 n r1 r2 q2) = (term86 q1 n r1 r2 q2).
Proof. exact (eq_refl (term86 q1 n r1 r2 q2)). Qed.
Lemma lem168484 (q2 : nat) (q1 : nat) (d : nat) (n : nat) (r1 : nat) (r2 : nat) : ((term83 q1 n r1 r2 q2) = (term84 n r1 r2 q1 d)) = ((term83 q1 n r1 r2 q2) = (term85 q1 d n r1 r2)).
Proof. exact (MK_COMB (@lem168483 q1 n r1 r2 q2) (@lem168482 q1 d n r1 r2)). Qed.
Lemma lem168485 (q1 : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) : (term83 q1 n r1 r2 q2) = (term81 q1 q2 n r1 r2).
Proof. exact (eq_refl (term83 q1 n r1 r2 q2)). Qed.
Lemma lem168486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem168487 (q1 : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) : (term86 q1 n r1 r2 q2) = (term87 q1 q2 n r1 r2).
Proof. exact (MK_COMB (@lem168486) (@lem168485 q1 q2 n r1 r2)). Qed.
Lemma lem168488 (q1 : nat) (d : nat) (n : nat) (r1 : nat) (r2 : nat) : (term85 q1 d n r1 r2) = (term85 q1 d n r1 r2).
Proof. exact (eq_refl (term85 q1 d n r1 r2)). Qed.
Lemma lem168489 (q2 : nat) (q1 : nat) (d : nat) (n : nat) (r1 : nat) (r2 : nat) : ((term83 q1 n r1 r2 q2) = (term85 q1 d n r1 r2)) = ((term81 q1 q2 n r1 r2) = (term85 q1 d n r1 r2)).
Proof. exact (MK_COMB (@lem168487 q1 q2 n r1 r2) (@lem168488 q1 d n r1 r2)). Qed.
Lemma lem168490 (q2 : nat) (q1 : nat) (d : nat) (n : nat) (r1 : nat) (r2 : nat) : ((term83 q1 n r1 r2 q2) = (term84 n r1 r2 q1 d)) = ((term81 q1 q2 n r1 r2) = (term85 q1 d n r1 r2)).
Proof. exact (TRANS (@lem168484 q2 q1 d n r1 r2) (@lem168489 q2 q1 d n r1 r2)). Qed.
Lemma lem168491 (n : nat) (r1 : nat) (r2 : nat) (q2 : nat) (q1 : nat) (d : nat) (h1 : q2 = (Nat.add q1 d)) : (term81 q1 q2 n r1 r2) = (term85 q1 d n r1 r2).
Proof. exact (EQ_MP (@lem168490 q2 q1 d n r1 r2) (@lem168481 n r1 r2 q2 q1 d h1)). Qed.
Lemma lem168492 (n : nat) (r1 : nat) (r2 : nat) (q2 : nat) (q1 : nat) (d : nat) (h1 : q2 = (Nat.add q1 d)) : (term85 q1 d n r1 r2) = (term81 q1 q2 n r1 r2).
Proof. exact (SYM (@lem168491 n r1 r2 q2 q1 d h1)). Qed.
Lemma lem168493 (q2 : nat) (q1 : nat) (h1 : Peano.le q2 q1) : Peano.le q2 q1.
Proof. exact (h1). Qed.
Lemma lem168495 (n : nat) (m : nat) : (Peano.le m n) = (term69 n m).
Proof. exact (EQ_MP (@lem168421 n m) (@lem168420 m n)). Qed.
Lemma lem168496 (q1 : nat) (q2 : nat) : (Peano.le q2 q1) = (term69 q1 q2).
Proof. exact (@lem168495 q1 q2). Qed.
Lemma lem168503 (q2 : nat) (q1 : nat) (h1 : Peano.le q2 q1) : term69 q1 q2.
Proof. exact (EQ_MP (@lem168496 q1 q2) (@lem168493 q2 q1 h1)). Qed.
Lemma lem168504 (q1 : nat) (q2 : nat) (d : nat) (h1 : q1 = (Nat.add q2 d)) : q1 = (Nat.add q2 d).
Proof. exact (h1). Qed.
Lemma lem168505 (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) : (term88 q2 n r1 r2) = (term88 q2 n r1 r2).
Proof. exact (eq_refl (term88 q2 n r1 r2)). Qed.
Lemma lem168506 (n : nat) (r1 : nat) (r2 : nat) (q1 : nat) (q2 : nat) (d : nat) (h1 : q1 = (Nat.add q2 d)) : (term89 q2 n r1 r2 q1) = (term90 n r1 r2 q2 d).
Proof. exact (MK_COMB (@lem168505 q2 n r1 r2) (@lem168504 q1 q2 d h1)). Qed.
Lemma lem168507 (d : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) : (term90 n r1 r2 q2 d) = (term91 d q2 n r1 r2).
Proof. exact (eq_refl (term90 n r1 r2 q2 d)). Qed.
Lemma lem168508 (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (q1 : nat) : (term92 q2 n r1 r2 q1) = (term92 q2 n r1 r2 q1).
Proof. exact (eq_refl (term92 q2 n r1 r2 q1)). Qed.
Lemma lem168509 (q1 : nat) (d : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) : ((term89 q2 n r1 r2 q1) = (term90 n r1 r2 q2 d)) = ((term89 q2 n r1 r2 q1) = (term91 d q2 n r1 r2)).
Proof. exact (MK_COMB (@lem168508 q2 n r1 r2 q1) (@lem168507 d q2 n r1 r2)). Qed.
Lemma lem168510 (q1 : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) : (term89 q2 n r1 r2 q1) = (term81 q1 q2 n r1 r2).
Proof. exact (eq_refl (term89 q2 n r1 r2 q1)). Qed.
Lemma lem168511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem168512 (q1 : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) : (term92 q2 n r1 r2 q1) = (term87 q1 q2 n r1 r2).
Proof. exact (MK_COMB (@lem168511) (@lem168510 q1 q2 n r1 r2)). Qed.
Lemma lem168513 (d : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) : (term91 d q2 n r1 r2) = (term91 d q2 n r1 r2).
Proof. exact (eq_refl (term91 d q2 n r1 r2)). Qed.
Lemma lem168514 (q1 : nat) (d : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) : ((term89 q2 n r1 r2 q1) = (term91 d q2 n r1 r2)) = ((term81 q1 q2 n r1 r2) = (term91 d q2 n r1 r2)).
Proof. exact (MK_COMB (@lem168512 q1 q2 n r1 r2) (@lem168513 d q2 n r1 r2)). Qed.
Lemma lem168515 (q1 : nat) (d : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) : ((term89 q2 n r1 r2 q1) = (term90 n r1 r2 q2 d)) = ((term81 q1 q2 n r1 r2) = (term91 d q2 n r1 r2)).
Proof. exact (TRANS (@lem168509 q1 d q2 n r1 r2) (@lem168514 q1 d q2 n r1 r2)). Qed.
Lemma lem168516 (n : nat) (r1 : nat) (r2 : nat) (q1 : nat) (q2 : nat) (d : nat) (h1 : q1 = (Nat.add q2 d)) : (term81 q1 q2 n r1 r2) = (term91 d q2 n r1 r2).
Proof. exact (EQ_MP (@lem168515 q1 d q2 n r1 r2) (@lem168506 n r1 r2 q1 q2 d h1)). Qed.
Lemma lem168517 (n : nat) (r1 : nat) (r2 : nat) (q1 : nat) (q2 : nat) (d : nat) (h1 : q1 = (Nat.add q2 d)) : (term91 d q2 n r1 r2) = (term81 q1 q2 n r1 r2).
Proof. exact (SYM (@lem168516 n r1 r2 q1 q2 d h1)). Qed.
Lemma lem168527 (m : nat) (n : nat) (p : nat) : (term64 m n p) = (term65 m n p).
Proof. exact (EQ_MP (@lem168415 m n p) (@lem168414 m n p)). Qed.
Lemma lem168528 (q1 : nat) (d : nat) (n : nat) : (term64 q1 d n) = (term65 q1 d n).
Proof. exact (@lem168527 q1 d n). Qed.
Lemma lem168529 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168530 (q1 : nat) (d : nat) (n : nat) : (term93 q1 d n) = (term94 q1 d n).
Proof. exact (MK_COMB (@lem168529) (@lem168528 q1 d n)). Qed.
Lemma lem168531 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem168532 (q1 : nat) (d : nat) (n : nat) (r2 : nat) : (term95 q1 d n r2) = (term96 q1 d n r2).
Proof. exact (MK_COMB (@lem168530 q1 d n) (@lem168531 r2)). Qed.
Lemma lem168534 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term12 m n p).
Proof. exact (EQ_MP (@lem168406 m n p) (@lem168405 m n p)). Qed.
Lemma lem168535 (q1 : nat) (d : nat) (n : nat) (r2 : nat) : (term96 q1 d n r2) = (term97 q1 d n r2).
Proof. exact (@lem168534 (Nat.mul q1 n) (Nat.mul d n) r2). Qed.
Lemma lem168536 (q1 : nat) (d : nat) (n : nat) (r2 : nat) : (term95 q1 d n r2) = (term97 q1 d n r2).
Proof. exact (TRANS (@lem168532 q1 d n r2) (@lem168535 q1 d n r2)). Qed.
Lemma lem168537 (q1 : nat) (n : nat) (r1 : nat) : (term77 q1 n r1) = (term77 q1 n r1).
Proof. exact (eq_refl (term77 q1 n r1)). Qed.
Lemma lem168538 (r1 : nat) (q1 : nat) (d : nat) (n : nat) (r2 : nat) : ((term76 q1 n r1) = (term95 q1 d n r2)) = ((term76 q1 n r1) = (term97 q1 d n r2)).
Proof. exact (MK_COMB (@lem168537 q1 n r1) (@lem168536 q1 d n r2)). Qed.
Lemma lem168540 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem168397 m n p) (@lem168396 m n p)). Qed.
Lemma lem168541 (q1 : nat) (r1 : nat) (d : nat) (n : nat) (r2 : nat) : ((term76 q1 n r1) = (term97 q1 d n r2)) = (r1 = (term76 d n r2)).
Proof. exact (@lem168540 (Nat.mul q1 n) r1 (term76 d n r2)). Qed.
Lemma lem168544 (q1 : nat) (r1 : nat) (d : nat) (n : nat) (r2 : nat) : ((term76 q1 n r1) = (term95 q1 d n r2)) = (r1 = (term76 d n r2)).
Proof. exact (TRANS (@lem168538 r1 q1 d n r2) (@lem168541 q1 r1 d n r2)). Qed.
Lemma lem168545 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168546 (q1 : nat) (r1 : nat) (d : nat) (n : nat) (r2 : nat) : (term98 r1 q1 d n r2) = (term78 r1 d n r2).
Proof. exact (MK_COMB (@lem168545) (@lem168544 q1 r1 d n r2)). Qed.
Lemma lem168549 (r1 : nat) (r2 : nat) : (r1 = r2) = (r1 = r2).
Proof. exact (eq_refl (r1 = r2)). Qed.
Lemma lem168550 (q1 : nat) (d : nat) (n : nat) (r1 : nat) (r2 : nat) : (term85 q1 d n r1 r2) = (term99 d n r1 r2).
Proof. exact (MK_COMB (@lem168546 q1 r1 d n r2) (@lem168549 r1 r2)). Qed.
Lemma lem168555 (q1 : nat) (d : nat) (n : nat) (r1 : nat) (r2 : nat) : (term99 d n r1 r2) = (term85 q1 d n r1 r2).
Proof. exact (SYM (@lem168550 q1 d n r1 r2)). Qed.
Lemma lem168565 (m : nat) (n : nat) (p : nat) : (term64 m n p) = (term65 m n p).
Proof. exact (EQ_MP (@lem168415 m n p) (@lem168414 m n p)). Qed.
Lemma lem168566 (q2 : nat) (d : nat) (n : nat) : (term64 q2 d n) = (term65 q2 d n).
Proof. exact (@lem168565 q2 d n). Qed.
Lemma lem168567 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168568 (q2 : nat) (d : nat) (n : nat) : (term93 q2 d n) = (term94 q2 d n).
Proof. exact (MK_COMB (@lem168567) (@lem168566 q2 d n)). Qed.
Lemma lem168569 (r1 : nat) : r1 = r1.
Proof. exact (eq_refl r1). Qed.
Lemma lem168570 (q2 : nat) (d : nat) (n : nat) (r1 : nat) : (term95 q2 d n r1) = (term96 q2 d n r1).
Proof. exact (MK_COMB (@lem168568 q2 d n) (@lem168569 r1)). Qed.
Lemma lem168572 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term12 m n p).
Proof. exact (EQ_MP (@lem168406 m n p) (@lem168405 m n p)). Qed.
Lemma lem168573 (q2 : nat) (d : nat) (n : nat) (r1 : nat) : (term96 q2 d n r1) = (term97 q2 d n r1).
Proof. exact (@lem168572 (Nat.mul q2 n) (Nat.mul d n) r1). Qed.
Lemma lem168574 (q2 : nat) (d : nat) (n : nat) (r1 : nat) : (term95 q2 d n r1) = (term97 q2 d n r1).
Proof. exact (TRANS (@lem168570 q2 d n r1) (@lem168573 q2 d n r1)). Qed.
Lemma lem168575 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem168576 (q2 : nat) (d : nat) (n : nat) (r1 : nat) : (term100 q2 d n r1) = (term101 q2 d n r1).
Proof. exact (MK_COMB (@lem168575) (@lem168574 q2 d n r1)). Qed.
Lemma lem168577 (q2 : nat) (n : nat) (r2 : nat) : (term76 q2 n r2) = (term76 q2 n r2).
Proof. exact (eq_refl (term76 q2 n r2)). Qed.
Lemma lem168578 (d : nat) (r1 : nat) (q2 : nat) (n : nat) (r2 : nat) : ((term95 q2 d n r1) = (term76 q2 n r2)) = ((term97 q2 d n r1) = (term76 q2 n r2)).
Proof. exact (MK_COMB (@lem168576 q2 d n r1) (@lem168577 q2 n r2)). Qed.
Lemma lem168580 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem168397 m n p) (@lem168396 m n p)). Qed.
Lemma lem168581 (q2 : nat) (d : nat) (n : nat) (r1 : nat) (r2 : nat) : ((term97 q2 d n r1) = (term76 q2 n r2)) = ((term76 d n r1) = r2).
Proof. exact (@lem168580 (Nat.mul q2 n) (term76 d n r1) r2). Qed.
Lemma lem168584 (q2 : nat) (d : nat) (n : nat) (r1 : nat) (r2 : nat) : ((term95 q2 d n r1) = (term76 q2 n r2)) = ((term76 d n r1) = r2).
Proof. exact (TRANS (@lem168578 d r1 q2 n r2) (@lem168581 q2 d n r1 r2)). Qed.
Lemma lem168585 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168586 (q2 : nat) (d : nat) (n : nat) (r1 : nat) (r2 : nat) : (term102 d r1 q2 n r2) = (term103 d n r1 r2).
Proof. exact (MK_COMB (@lem168585) (@lem168584 q2 d n r1 r2)). Qed.
Lemma lem168589 (r1 : nat) (r2 : nat) : (r1 = r2) = (r1 = r2).
Proof. exact (eq_refl (r1 = r2)). Qed.
Lemma lem168590 (q2 : nat) (d : nat) (n : nat) (r1 : nat) (r2 : nat) : (term91 d q2 n r1 r2) = (term104 d n r1 r2).
Proof. exact (MK_COMB (@lem168586 q2 d n r1 r2) (@lem168589 r1 r2)). Qed.
Lemma lem168595 (d : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) : (term104 d n r1 r2) = (term91 d q2 n r1 r2).
Proof. exact (SYM (@lem168590 q2 d n r1 r2)). Qed.
Lemma lem168597 (d : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : (term76 d n r1) = r2) : (term76 d n r1) = r2.
Proof. exact (h1). Qed.
Lemma lem168604 (r1 : nat) (d : nat) (n : nat) (r2 : nat) (h1 : r1 = (term76 d n r2)) : r1 = (term76 d n r2).
Proof. exact (h1). Qed.
Lemma lem168605 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem168606 (r1 : nat) (d : nat) (n : nat) (r2 : nat) (h1 : r1 = (term76 d n r2)) : (Peano.lt r1) = (term105 d n r2).
Proof. exact (MK_COMB (@lem168605) (@lem168604 r1 d n r2 h1)). Qed.
Lemma lem168607 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem168608 (r1 : nat) (d : nat) (n : nat) (r2 : nat) (h1 : r1 = (term76 d n r2)) : (Peano.lt r1 n) = (term106 d r2 n).
Proof. exact (MK_COMB (@lem168606 r1 d n r2 h1) (@lem168607 n)). Qed.
Lemma lem168609 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168610 (r1 : nat) (d : nat) (n : nat) (r2 : nat) (h1 : r1 = (term76 d n r2)) : (term107 r1 n) = (term108 d r2 n).
Proof. exact (MK_COMB (@lem168609) (@lem168608 r1 d n r2 h1)). Qed.
Lemma lem168614 (r1 : nat) (d : nat) (n : nat) (r2 : nat) (h1 : r1 = (term76 d n r2)) : r1 = (term76 d n r2).
Proof. exact (h1). Qed.
Lemma lem168615 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem168616 (r1 : nat) (d : nat) (n : nat) (r2 : nat) (h1 : r1 = (term76 d n r2)) : (@eq nat r1) = (term77 d n r2).
Proof. exact (MK_COMB (@lem168615) (@lem168614 r1 d n r2 h1)). Qed.
Lemma lem168617 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem168618 (r1 : nat) (d : nat) (n : nat) (r2 : nat) (h1 : r1 = (term76 d n r2)) : (r1 = r2) = ((term76 d n r2) = r2).
Proof. exact (MK_COMB (@lem168616 r1 d n r2 h1) (@lem168617 r2)). Qed.
Lemma lem168621 (r1 : nat) (d : nat) (n : nat) (r2 : nat) (h1 : r1 = (term76 d n r2)) : (term109 n r1 r2) = (term110 d n r2).
Proof. exact (MK_COMB (@lem168610 r1 d n r2 h1) (@lem168618 r1 d n r2 h1)). Qed.
Lemma lem168624 (r1 : nat) (d : nat) (n : nat) (r2 : nat) (h1 : r1 = (term76 d n r2)) : (term110 d n r2) = (term109 n r1 r2).
Proof. exact (SYM (@lem168621 r1 d n r2 h1)). Qed.
Lemma lem168630 (d : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : (term76 d n r1) = r2) : r2 = (term76 d n r1).
Proof. exact (SYM (@lem168597 d n r1 r2 h1)). Qed.
Lemma lem168631 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem168632 (d : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : (term76 d n r1) = r2) : (Peano.lt r2) = (term105 d n r1).
Proof. exact (MK_COMB (@lem168631) (@lem168630 d n r1 r2 h1)). Qed.
Lemma lem168633 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem168634 (d : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : (term76 d n r1) = r2) : (Peano.lt r2 n) = (term106 d r1 n).
Proof. exact (MK_COMB (@lem168632 d n r1 r2 h1) (@lem168633 n)). Qed.
Lemma lem168635 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168636 (d : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : (term76 d n r1) = r2) : (term107 r2 n) = (term108 d r1 n).
Proof. exact (MK_COMB (@lem168635) (@lem168634 d n r1 r2 h1)). Qed.
Lemma lem168640 (d : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : (term76 d n r1) = r2) : r2 = (term76 d n r1).
Proof. exact (SYM (@lem168597 d n r1 r2 h1)). Qed.
Lemma lem168641 (r1 : nat) : (@eq nat r1) = (@eq nat r1).
Proof. exact (eq_refl (@eq nat r1)). Qed.
Lemma lem168642 (d : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : (term76 d n r1) = r2) : (r1 = r2) = (r1 = (term76 d n r1)).
Proof. exact (MK_COMB (@lem168641 r1) (@lem168640 d n r1 r2 h1)). Qed.
Lemma lem168645 (d : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : (term76 d n r1) = r2) : (term111 n r1 r2) = (term112 d n r1).
Proof. exact (MK_COMB (@lem168636 d n r1 r2 h1) (@lem168642 d n r1 r2 h1)). Qed.
Lemma lem168648 (d : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : (term76 d n r1) = r2) : (term112 d n r1) = (term111 n r1 r2).
Proof. exact (SYM (@lem168645 d n r1 r2 h1)). Qed.
Lemma lem168652 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem168370 n m) (@lem168369 m n)). Qed.
Lemma lem168653 (n : nat) (d : nat) : (Nat.mul d n) = (Nat.mul n d).
Proof. exact (@lem168652 n d). Qed.
Lemma lem168654 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168655 (n : nat) (d : nat) : (term113 d n) = (term113 n d).
Proof. exact (MK_COMB (@lem168654) (@lem168653 n d)). Qed.
Lemma lem168656 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem168657 (n : nat) (d : nat) (r2 : nat) : (term76 d n r2) = (term76 n d r2).
Proof. exact (MK_COMB (@lem168655 n d) (@lem168656 r2)). Qed.
Lemma lem168658 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem168659 (n : nat) (d : nat) (r2 : nat) : (term105 d n r2) = (term105 n d r2).
Proof. exact (MK_COMB (@lem168658) (@lem168657 n d r2)). Qed.
Lemma lem168660 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem168661 (d : nat) (r2 : nat) (n : nat) : (term106 d r2 n) = (term114 d r2 n).
Proof. exact (MK_COMB (@lem168659 n d r2) (@lem168660 n)). Qed.
Lemma lem168662 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168663 (d : nat) (r2 : nat) (n : nat) : (term108 d r2 n) = (term115 d r2 n).
Proof. exact (MK_COMB (@lem168662) (@lem168661 d r2 n)). Qed.
Lemma lem168667 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem168370 n m) (@lem168369 m n)). Qed.
Lemma lem168668 (n : nat) (d : nat) : (Nat.mul d n) = (Nat.mul n d).
Proof. exact (@lem168667 n d). Qed.
Lemma lem168669 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168670 (n : nat) (d : nat) : (term113 d n) = (term113 n d).
Proof. exact (MK_COMB (@lem168669) (@lem168668 n d)). Qed.
Lemma lem168671 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem168672 (n : nat) (d : nat) (r2 : nat) : (term76 d n r2) = (term76 n d r2).
Proof. exact (MK_COMB (@lem168670 n d) (@lem168671 r2)). Qed.
Lemma lem168673 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem168674 (n : nat) (d : nat) (r2 : nat) : (term77 d n r2) = (term77 n d r2).
Proof. exact (MK_COMB (@lem168673) (@lem168672 n d r2)). Qed.
Lemma lem168675 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem168676 (n : nat) (d : nat) (r2 : nat) : ((term76 d n r2) = r2) = ((term76 n d r2) = r2).
Proof. exact (MK_COMB (@lem168674 n d r2) (@lem168675 r2)). Qed.
Lemma lem168677 (n : nat) (d : nat) (r2 : nat) : (term110 d n r2) = (term116 n d r2).
Proof. exact (MK_COMB (@lem168663 d r2 n) (@lem168676 n d r2)). Qed.
Lemma lem168678 (d : nat) (n : nat) (r2 : nat) : (term116 n d r2) = (term110 d n r2).
Proof. exact (SYM (@lem168677 n d r2)). Qed.
Lemma lem168682 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem168370 n m) (@lem168369 m n)). Qed.
Lemma lem168683 (n : nat) (d : nat) : (Nat.mul d n) = (Nat.mul n d).
Proof. exact (@lem168682 n d). Qed.
Lemma lem168684 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168685 (n : nat) (d : nat) : (term113 d n) = (term113 n d).
Proof. exact (MK_COMB (@lem168684) (@lem168683 n d)). Qed.
Lemma lem168686 (r1 : nat) : r1 = r1.
Proof. exact (eq_refl r1). Qed.
Lemma lem168687 (n : nat) (d : nat) (r1 : nat) : (term76 d n r1) = (term76 n d r1).
Proof. exact (MK_COMB (@lem168685 n d) (@lem168686 r1)). Qed.
Lemma lem168688 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem168689 (n : nat) (d : nat) (r1 : nat) : (term105 d n r1) = (term105 n d r1).
Proof. exact (MK_COMB (@lem168688) (@lem168687 n d r1)). Qed.
Lemma lem168690 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem168691 (d : nat) (r1 : nat) (n : nat) : (term106 d r1 n) = (term114 d r1 n).
Proof. exact (MK_COMB (@lem168689 n d r1) (@lem168690 n)). Qed.
Lemma lem168692 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168693 (d : nat) (r1 : nat) (n : nat) : (term108 d r1 n) = (term115 d r1 n).
Proof. exact (MK_COMB (@lem168692) (@lem168691 d r1 n)). Qed.
Lemma lem168697 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem168370 n m) (@lem168369 m n)). Qed.
Lemma lem168698 (n : nat) (d : nat) : (Nat.mul d n) = (Nat.mul n d).
Proof. exact (@lem168697 n d). Qed.
Lemma lem168699 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168700 (n : nat) (d : nat) : (term113 d n) = (term113 n d).
Proof. exact (MK_COMB (@lem168699) (@lem168698 n d)). Qed.
Lemma lem168701 (r1 : nat) : r1 = r1.
Proof. exact (eq_refl r1). Qed.
Lemma lem168702 (n : nat) (d : nat) (r1 : nat) : (term76 d n r1) = (term76 n d r1).
Proof. exact (MK_COMB (@lem168700 n d) (@lem168701 r1)). Qed.
Lemma lem168703 (r1 : nat) : (@eq nat r1) = (@eq nat r1).
Proof. exact (eq_refl (@eq nat r1)). Qed.
Lemma lem168704 (n : nat) (d : nat) (r1 : nat) : (r1 = (term76 d n r1)) = (r1 = (term76 n d r1)).
Proof. exact (MK_COMB (@lem168703 r1) (@lem168702 n d r1)). Qed.
Lemma lem168705 (n : nat) (d : nat) (r1 : nat) : (term112 d n r1) = (term117 n d r1).
Proof. exact (MK_COMB (@lem168693 d r1 n) (@lem168704 n d r1)). Qed.
Lemma lem168706 (d : nat) (n : nat) (r1 : nat) : (term117 n d r1) = (term112 d n r1).
Proof. exact (SYM (@lem168705 n d r1)). Qed.
Lemma lem168708 (P : nat -> Prop) : term118 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem168709 (n : nat) (r2 : nat) : term119 n r2.
Proof. exact (@lem168708 (term120 n r2)). Qed.
Lemma lem168710 (n : nat) (r2 : nat) : (term121 n r2) = (term122 n r2).
Proof. exact (eq_refl (term121 n r2)). Qed.
Lemma lem168711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem168712 (n : nat) (r2 : nat) : (term123 n r2) = (term124 n r2).
Proof. exact (MK_COMB (@lem168711) (@lem168710 n r2)). Qed.
Lemma lem168713 (n : nat) (d : nat) (r2 : nat) : (term125 n r2 d) = (term116 n d r2).
Proof. exact (eq_refl (term125 n r2 d)). Qed.
Lemma lem168714 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168715 (n : nat) (d : nat) (r2 : nat) : (term126 n r2 d) = (term127 n d r2).
Proof. exact (MK_COMB (@lem168714) (@lem168713 n d r2)). Qed.
Lemma lem168716 (n : nat) (d : nat) (r2 : nat) : (term128 n r2 d) = (term129 n d r2).
Proof. exact (eq_refl (term128 n r2 d)). Qed.
Lemma lem168717 (n : nat) (d : nat) (r2 : nat) : (term130 n r2 d) = (term131 n d r2).
Proof. exact (MK_COMB (@lem168715 n d r2) (@lem168716 n d r2)). Qed.
Lemma lem168718 (n : nat) (r2 : nat) : (term132 n r2) = (term133 n r2).
Proof. exact (fun_ext (fun d : nat => @lem168717 n d r2)). Qed.
Lemma lem168719 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168720 (n : nat) (r2 : nat) : (term134 n r2) = (term135 n r2).
Proof. exact (MK_COMB (@lem168719) (@lem168718 n r2)). Qed.
Lemma lem168721 (n : nat) (r2 : nat) : (term136 n r2) = (term137 n r2).
Proof. exact (MK_COMB (@lem168712 n r2) (@lem168720 n r2)). Qed.
Lemma lem168722 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168723 (n : nat) (r2 : nat) : (term138 n r2) = (term139 n r2).
Proof. exact (MK_COMB (@lem168722) (@lem168721 n r2)). Qed.
Lemma lem168724 (n : nat) (d : nat) (r2 : nat) : (term125 n r2 d) = (term116 n d r2).
Proof. exact (eq_refl (term125 n r2 d)). Qed.
Lemma lem168725 (n : nat) (r2 : nat) : (term140 n r2) = (term120 n r2).
Proof. exact (fun_ext (fun d : nat => @lem168724 n d r2)). Qed.
Lemma lem168726 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168727 (n : nat) (r2 : nat) : (term141 n r2) = (term142 n r2).
Proof. exact (MK_COMB (@lem168726) (@lem168725 n r2)). Qed.
Lemma lem168728 (n : nat) (r2 : nat) : (term119 n r2) = (term143 n r2).
Proof. exact (MK_COMB (@lem168723 n r2) (@lem168727 n r2)). Qed.
Lemma lem168729 (n : nat) (r2 : nat) : term143 n r2.
Proof. exact (EQ_MP (@lem168728 n r2) (@lem168709 n r2)). Qed.
Lemma lem168732 (P : nat -> Prop) : term118 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem168733 (n : nat) (r1 : nat) : term144 n r1.
Proof. exact (@lem168732 (term145 n r1)). Qed.
Lemma lem168734 (n : nat) (r1 : nat) : (term146 n r1) = (term147 n r1).
Proof. exact (eq_refl (term146 n r1)). Qed.
Lemma lem168735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem168736 (n : nat) (r1 : nat) : (term148 n r1) = (term149 n r1).
Proof. exact (MK_COMB (@lem168735) (@lem168734 n r1)). Qed.
Lemma lem168737 (n : nat) (d : nat) (r1 : nat) : (term150 n r1 d) = (term117 n d r1).
Proof. exact (eq_refl (term150 n r1 d)). Qed.
Lemma lem168738 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168739 (n : nat) (d : nat) (r1 : nat) : (term151 n r1 d) = (term152 n d r1).
Proof. exact (MK_COMB (@lem168738) (@lem168737 n d r1)). Qed.
Lemma lem168740 (n : nat) (d : nat) (r1 : nat) : (term153 n r1 d) = (term154 n d r1).
Proof. exact (eq_refl (term153 n r1 d)). Qed.
Lemma lem168741 (n : nat) (d : nat) (r1 : nat) : (term155 n r1 d) = (term156 n d r1).
Proof. exact (MK_COMB (@lem168739 n d r1) (@lem168740 n d r1)). Qed.
Lemma lem168742 (n : nat) (r1 : nat) : (term157 n r1) = (term158 n r1).
Proof. exact (fun_ext (fun d : nat => @lem168741 n d r1)). Qed.
Lemma lem168743 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168744 (n : nat) (r1 : nat) : (term159 n r1) = (term160 n r1).
Proof. exact (MK_COMB (@lem168743) (@lem168742 n r1)). Qed.
Lemma lem168745 (n : nat) (r1 : nat) : (term161 n r1) = (term162 n r1).
Proof. exact (MK_COMB (@lem168736 n r1) (@lem168744 n r1)). Qed.
Lemma lem168746 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168747 (n : nat) (r1 : nat) : (term163 n r1) = (term164 n r1).
Proof. exact (MK_COMB (@lem168746) (@lem168745 n r1)). Qed.
Lemma lem168748 (n : nat) (d : nat) (r1 : nat) : (term150 n r1 d) = (term117 n d r1).
Proof. exact (eq_refl (term150 n r1 d)). Qed.
Lemma lem168749 (n : nat) (r1 : nat) : (term165 n r1) = (term145 n r1).
Proof. exact (fun_ext (fun d : nat => @lem168748 n d r1)). Qed.
Lemma lem168750 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem168751 (n : nat) (r1 : nat) : (term166 n r1) = (term167 n r1).
Proof. exact (MK_COMB (@lem168750) (@lem168749 n r1)). Qed.
Lemma lem168752 (n : nat) (r1 : nat) : (term144 n r1) = (term168 n r1).
Proof. exact (MK_COMB (@lem168747 n r1) (@lem168751 n r1)). Qed.
Lemma lem168753 (n : nat) (r1 : nat) : term168 n r1.
Proof. exact (EQ_MP (@lem168752 n r1) (@lem168733 n r1)). Qed.
Lemma lem168758 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem168306 m n) (@lem168305 m n)). Qed.
Lemma lem168759 (n : nat) (r2 : nat) : (term169 r2 n) = (term170 n r2).
Proof. exact (@lem168758 n (term171 n r2)). Qed.
Lemma lem168763 (m : nat) : (term47 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem168336 m) (@lem168335 m)). Qed.
Lemma lem168764 (n : nat) : (term47 n) = (NUMERAL 0).
Proof. exact (@lem168763 n). Qed.
Lemma lem168765 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168766 (n : nat) : (term172 n) = term173.
Proof. exact (MK_COMB (@lem168765) (@lem168764 n)). Qed.
Lemma lem168767 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem168768 (n : nat) (r2 : nat) : (term171 n r2) = (term50 r2).
Proof. exact (MK_COMB (@lem168766 n) (@lem168767 r2)). Qed.
Lemma lem168770 (n : nat) : (term50 n) = n.
Proof. exact (EQ_MP (@lem168364 n) (@lem168363 n)). Qed.
Lemma lem168771 (r2 : nat) : (term50 r2) = r2.
Proof. exact (@lem168770 r2). Qed.
Lemma lem168772 (n : nat) (r2 : nat) : (term171 n r2) = r2.
Proof. exact (TRANS (@lem168768 n r2) (@lem168771 r2)). Qed.
Lemma lem168773 (n : nat) : (Peano.le n) = (Peano.le n).
Proof. exact (eq_refl (Peano.le n)). Qed.
Lemma lem168774 (n : nat) (r2 : nat) : (term174 n r2) = (Peano.le n r2).
Proof. exact (MK_COMB (@lem168773 n) (@lem168772 n r2)). Qed.
Lemma lem168775 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem168776 (n : nat) (r2 : nat) : (term170 n r2) = (term0 n r2).
Proof. exact (MK_COMB (@lem168775) (@lem168774 n r2)). Qed.
Lemma lem168777 (n : nat) (r2 : nat) : (term169 r2 n) = (term0 n r2).
Proof. exact (TRANS (@lem168759 n r2) (@lem168776 n r2)). Qed.
Lemma lem168778 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168779 (n : nat) (r2 : nat) : (term175 r2 n) = (term176 n r2).
Proof. exact (MK_COMB (@lem168778) (@lem168777 n r2)). Qed.
Lemma lem168783 (m : nat) : (term47 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem168336 m) (@lem168335 m)). Qed.
Lemma lem168784 (n : nat) : (term47 n) = (NUMERAL 0).
Proof. exact (@lem168783 n). Qed.
Lemma lem168785 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168786 (n : nat) : (term172 n) = term173.
Proof. exact (MK_COMB (@lem168785) (@lem168784 n)). Qed.
Lemma lem168787 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem168788 (n : nat) (r2 : nat) : (term171 n r2) = (term50 r2).
Proof. exact (MK_COMB (@lem168786 n) (@lem168787 r2)). Qed.
Lemma lem168790 (n : nat) : (term50 n) = n.
Proof. exact (EQ_MP (@lem168364 n) (@lem168363 n)). Qed.
Lemma lem168791 (r2 : nat) : (term50 r2) = r2.
Proof. exact (@lem168790 r2). Qed.
Lemma lem168792 (n : nat) (r2 : nat) : (term171 n r2) = r2.
Proof. exact (TRANS (@lem168788 n r2) (@lem168791 r2)). Qed.
Lemma lem168793 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem168794 (n : nat) (r2 : nat) : (term177 n r2) = (@eq nat r2).
Proof. exact (MK_COMB (@lem168793) (@lem168792 n r2)). Qed.
Lemma lem168795 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem168796 (n : nat) (r2 : nat) : ((term171 n r2) = r2) = (r2 = r2).
Proof. exact (MK_COMB (@lem168794 n r2) (@lem168795 r2)). Qed.
Lemma lem168798 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem168799 (x : nat) : (x = x) = True.
Proof. exact (@lem168798 nat x). Qed.
Lemma lem168800 (r2 : nat) : (r2 = r2) = True.
Proof. exact (@lem168799 r2). Qed.
Lemma lem168801 (n : nat) (r2 : nat) : ((term171 n r2) = r2) = True.
Proof. exact (TRANS (@lem168796 n r2) (@lem168800 r2)). Qed.
Lemma lem168802 (n : nat) (r2 : nat) : (term122 n r2) = (term178 n r2).
Proof. exact (MK_COMB (@lem168779 n r2) (@lem168801 n r2)). Qed.
Lemma lem168804 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem168805 (n : nat) (r2 : nat) : (term178 n r2) = True.
Proof. exact (@lem168804 (term0 n r2)). Qed.
Lemma lem168806 (n : nat) (r2 : nat) : (term122 n r2) = True.
Proof. exact (TRANS (@lem168802 n r2) (@lem168805 n r2)). Qed.
Lemma lem168807 (n : nat) (r2 : nat) : True = (term122 n r2).
Proof. exact (SYM (@lem168806 n r2)). Qed.
Lemma lem168808 (n : nat) (r2 : nat) : term122 n r2.
Proof. exact (EQ_MP (@lem168807 n r2) (@lem0)). Qed.
Lemma lem168812 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem168306 m n) (@lem168305 m n)). Qed.
Lemma lem168813 (n : nat) (d' : nat) (r2 : nat) : (term179 d' r2 n) = (term180 n d' r2).
Proof. exact (@lem168812 n (term181 n d' r2)). Qed.
Lemma lem168817 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem168317 m n) (@lem168316 m n)). Qed.
Lemma lem168818 (n : nat) (d' : nat) : (term43 n d') = (term44 n d').
Proof. exact (@lem168817 n d'). Qed.
Lemma lem168819 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168820 (n : nat) (d' : nat) : (term182 n d') = (term183 n d').
Proof. exact (MK_COMB (@lem168819) (@lem168818 n d')). Qed.
Lemma lem168821 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem168822 (n : nat) (d' : nat) (r2 : nat) : (term181 n d' r2) = (term184 n d' r2).
Proof. exact (MK_COMB (@lem168820 n d') (@lem168821 r2)). Qed.
Lemma lem168824 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term12 m n p).
Proof. exact (EQ_MP (@lem168292 m n p) (@lem168291 m n p)). Qed.
Lemma lem168825 (n : nat) (d' : nat) (r2 : nat) : (term184 n d' r2) = (term185 n d' r2).
Proof. exact (@lem168824 n (Nat.mul n d') r2). Qed.
Lemma lem168826 (n : nat) (d' : nat) (r2 : nat) : (term181 n d' r2) = (term185 n d' r2).
Proof. exact (TRANS (@lem168822 n d' r2) (@lem168825 n d' r2)). Qed.
Lemma lem168827 (n : nat) : (Peano.le n) = (Peano.le n).
Proof. exact (eq_refl (Peano.le n)). Qed.
Lemma lem168828 (n : nat) (d' : nat) (r2 : nat) : (term186 n d' r2) = (term187 n d' r2).
Proof. exact (MK_COMB (@lem168827 n) (@lem168826 n d' r2)). Qed.
Lemma lem168830 (m : nat) (n : nat) : (term32 m n) = True.
Proof. exact (EQ_MP (@lem168300 m n) (@lem168299 m n)). Qed.
Lemma lem168831 (n : nat) (d' : nat) (r2 : nat) : (term187 n d' r2) = True.
Proof. exact (@lem168830 n (term76 n d' r2)). Qed.
Lemma lem168832 (n : nat) (d' : nat) (r2 : nat) : (term186 n d' r2) = True.
Proof. exact (TRANS (@lem168828 n d' r2) (@lem168831 n d' r2)). Qed.
Lemma lem168833 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem168834 (n : nat) (d' : nat) (r2 : nat) : (term180 n d' r2) = (~ True).
Proof. exact (MK_COMB (@lem168833) (@lem168832 n d' r2)). Qed.
Lemma lem168836 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem168837 (n : nat) (d' : nat) (r2 : nat) : (term180 n d' r2) = False.
Proof. exact (TRANS (@lem168834 n d' r2) (@lem168836)). Qed.
Lemma lem168838 (d' : nat) (r2 : nat) (n : nat) : (term179 d' r2 n) = False.
Proof. exact (TRANS (@lem168813 n d' r2) (@lem168837 n d' r2)). Qed.
Lemma lem168839 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168840 (d' : nat) (r2 : nat) (n : nat) : (term188 d' r2 n) = (imp False).
Proof. exact (MK_COMB (@lem168839) (@lem168838 d' r2 n)). Qed.
Lemma lem168844 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem168317 m n) (@lem168316 m n)). Qed.
Lemma lem168845 (n : nat) (d' : nat) : (term43 n d') = (term44 n d').
Proof. exact (@lem168844 n d'). Qed.
Lemma lem168846 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168847 (n : nat) (d' : nat) : (term182 n d') = (term183 n d').
Proof. exact (MK_COMB (@lem168846) (@lem168845 n d')). Qed.
Lemma lem168848 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem168849 (n : nat) (d' : nat) (r2 : nat) : (term181 n d' r2) = (term184 n d' r2).
Proof. exact (MK_COMB (@lem168847 n d') (@lem168848 r2)). Qed.
Lemma lem168851 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term12 m n p).
Proof. exact (EQ_MP (@lem168292 m n p) (@lem168291 m n p)). Qed.
Lemma lem168852 (n : nat) (d' : nat) (r2 : nat) : (term184 n d' r2) = (term185 n d' r2).
Proof. exact (@lem168851 n (Nat.mul n d') r2). Qed.
Lemma lem168853 (n : nat) (d' : nat) (r2 : nat) : (term181 n d' r2) = (term185 n d' r2).
Proof. exact (TRANS (@lem168849 n d' r2) (@lem168852 n d' r2)). Qed.
Lemma lem168854 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem168855 (n : nat) (d' : nat) (r2 : nat) : (term189 n d' r2) = (term190 n d' r2).
Proof. exact (MK_COMB (@lem168854) (@lem168853 n d' r2)). Qed.
Lemma lem168856 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem168857 (n : nat) (d' : nat) (r2 : nat) : ((term181 n d' r2) = r2) = ((term185 n d' r2) = r2).
Proof. exact (MK_COMB (@lem168855 n d' r2) (@lem168856 r2)). Qed.
Lemma lem168860 (n : nat) (d' : nat) (r2 : nat) : (term129 n d' r2) = (term191 n d' r2).
Proof. exact (MK_COMB (@lem168840 d' r2 n) (@lem168857 n d' r2)). Qed.
Lemma lem168862 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem168863 (n : nat) (d' : nat) (r2 : nat) : (term191 n d' r2) = True.
Proof. exact (@lem168862 ((term185 n d' r2) = r2)). Qed.
Lemma lem168864 (n : nat) (d' : nat) (r2 : nat) : (term129 n d' r2) = True.
Proof. exact (TRANS (@lem168860 n d' r2) (@lem168863 n d' r2)). Qed.
Lemma lem168865 (n : nat) (d' : nat) (r2 : nat) : True = (term129 n d' r2).
Proof. exact (SYM (@lem168864 n d' r2)). Qed.
Lemma lem168866 (n : nat) (d' : nat) (r2 : nat) : term129 n d' r2.
Proof. exact (EQ_MP (@lem168865 n d' r2) (@lem0)). Qed.
Lemma lem168870 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem168306 m n) (@lem168305 m n)). Qed.
Lemma lem168871 (n : nat) (r1 : nat) : (term169 r1 n) = (term170 n r1).
Proof. exact (@lem168870 n (term171 n r1)). Qed.
Lemma lem168875 (m : nat) : (term47 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem168336 m) (@lem168335 m)). Qed.
Lemma lem168876 (n : nat) : (term47 n) = (NUMERAL 0).
Proof. exact (@lem168875 n). Qed.
Lemma lem168877 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168878 (n : nat) : (term172 n) = term173.
Proof. exact (MK_COMB (@lem168877) (@lem168876 n)). Qed.
Lemma lem168879 (r1 : nat) : r1 = r1.
Proof. exact (eq_refl r1). Qed.
Lemma lem168880 (n : nat) (r1 : nat) : (term171 n r1) = (term50 r1).
Proof. exact (MK_COMB (@lem168878 n) (@lem168879 r1)). Qed.
Lemma lem168882 (n : nat) : (term50 n) = n.
Proof. exact (EQ_MP (@lem168364 n) (@lem168363 n)). Qed.
Lemma lem168883 (r1 : nat) : (term50 r1) = r1.
Proof. exact (@lem168882 r1). Qed.
Lemma lem168884 (n : nat) (r1 : nat) : (term171 n r1) = r1.
Proof. exact (TRANS (@lem168880 n r1) (@lem168883 r1)). Qed.
Lemma lem168885 (n : nat) : (Peano.le n) = (Peano.le n).
Proof. exact (eq_refl (Peano.le n)). Qed.
Lemma lem168886 (n : nat) (r1 : nat) : (term174 n r1) = (Peano.le n r1).
Proof. exact (MK_COMB (@lem168885 n) (@lem168884 n r1)). Qed.
Lemma lem168887 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem168888 (n : nat) (r1 : nat) : (term170 n r1) = (term0 n r1).
Proof. exact (MK_COMB (@lem168887) (@lem168886 n r1)). Qed.
Lemma lem168889 (n : nat) (r1 : nat) : (term169 r1 n) = (term0 n r1).
Proof. exact (TRANS (@lem168871 n r1) (@lem168888 n r1)). Qed.
Lemma lem168890 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168891 (n : nat) (r1 : nat) : (term175 r1 n) = (term176 n r1).
Proof. exact (MK_COMB (@lem168890) (@lem168889 n r1)). Qed.
Lemma lem168895 (m : nat) : (term47 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem168336 m) (@lem168335 m)). Qed.
Lemma lem168896 (n : nat) : (term47 n) = (NUMERAL 0).
Proof. exact (@lem168895 n). Qed.
Lemma lem168897 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168898 (n : nat) : (term172 n) = term173.
Proof. exact (MK_COMB (@lem168897) (@lem168896 n)). Qed.
Lemma lem168899 (r1 : nat) : r1 = r1.
Proof. exact (eq_refl r1). Qed.
Lemma lem168900 (n : nat) (r1 : nat) : (term171 n r1) = (term50 r1).
Proof. exact (MK_COMB (@lem168898 n) (@lem168899 r1)). Qed.
Lemma lem168902 (n : nat) : (term50 n) = n.
Proof. exact (EQ_MP (@lem168364 n) (@lem168363 n)). Qed.
Lemma lem168903 (r1 : nat) : (term50 r1) = r1.
Proof. exact (@lem168902 r1). Qed.
Lemma lem168904 (n : nat) (r1 : nat) : (term171 n r1) = r1.
Proof. exact (TRANS (@lem168900 n r1) (@lem168903 r1)). Qed.
Lemma lem168905 (r1 : nat) : (@eq nat r1) = (@eq nat r1).
Proof. exact (eq_refl (@eq nat r1)). Qed.
Lemma lem168906 (n : nat) (r1 : nat) : (r1 = (term171 n r1)) = (r1 = r1).
Proof. exact (MK_COMB (@lem168905 r1) (@lem168904 n r1)). Qed.
Lemma lem168908 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem168909 (x : nat) : (x = x) = True.
Proof. exact (@lem168908 nat x). Qed.
Lemma lem168910 (r1 : nat) : (r1 = r1) = True.
Proof. exact (@lem168909 r1). Qed.
Lemma lem168911 (n : nat) (r1 : nat) : (r1 = (term171 n r1)) = True.
Proof. exact (TRANS (@lem168906 n r1) (@lem168910 r1)). Qed.
Lemma lem168912 (n : nat) (r1 : nat) : (term147 n r1) = (term178 n r1).
Proof. exact (MK_COMB (@lem168891 n r1) (@lem168911 n r1)). Qed.
Lemma lem168914 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem168915 (n : nat) (r1 : nat) : (term178 n r1) = True.
Proof. exact (@lem168914 (term0 n r1)). Qed.
Lemma lem168916 (n : nat) (r1 : nat) : (term147 n r1) = True.
Proof. exact (TRANS (@lem168912 n r1) (@lem168915 n r1)). Qed.
Lemma lem168917 (n : nat) (r1 : nat) : True = (term147 n r1).
Proof. exact (SYM (@lem168916 n r1)). Qed.
Lemma lem168918 (n : nat) (r1 : nat) : term147 n r1.
Proof. exact (EQ_MP (@lem168917 n r1) (@lem0)). Qed.
Lemma lem168922 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem168306 m n) (@lem168305 m n)). Qed.
Lemma lem168923 (n : nat) (d' : nat) (r1 : nat) : (term179 d' r1 n) = (term180 n d' r1).
Proof. exact (@lem168922 n (term181 n d' r1)). Qed.
Lemma lem168927 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem168317 m n) (@lem168316 m n)). Qed.
Lemma lem168928 (n : nat) (d' : nat) : (term43 n d') = (term44 n d').
Proof. exact (@lem168927 n d'). Qed.
Lemma lem168929 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168930 (n : nat) (d' : nat) : (term182 n d') = (term183 n d').
Proof. exact (MK_COMB (@lem168929) (@lem168928 n d')). Qed.
Lemma lem168931 (r1 : nat) : r1 = r1.
Proof. exact (eq_refl r1). Qed.
Lemma lem168932 (n : nat) (d' : nat) (r1 : nat) : (term181 n d' r1) = (term184 n d' r1).
Proof. exact (MK_COMB (@lem168930 n d') (@lem168931 r1)). Qed.
Lemma lem168934 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term12 m n p).
Proof. exact (EQ_MP (@lem168292 m n p) (@lem168291 m n p)). Qed.
Lemma lem168935 (n : nat) (d' : nat) (r1 : nat) : (term184 n d' r1) = (term185 n d' r1).
Proof. exact (@lem168934 n (Nat.mul n d') r1). Qed.
Lemma lem168936 (n : nat) (d' : nat) (r1 : nat) : (term181 n d' r1) = (term185 n d' r1).
Proof. exact (TRANS (@lem168932 n d' r1) (@lem168935 n d' r1)). Qed.
Lemma lem168937 (n : nat) : (Peano.le n) = (Peano.le n).
Proof. exact (eq_refl (Peano.le n)). Qed.
Lemma lem168938 (n : nat) (d' : nat) (r1 : nat) : (term186 n d' r1) = (term187 n d' r1).
Proof. exact (MK_COMB (@lem168937 n) (@lem168936 n d' r1)). Qed.
Lemma lem168940 (m : nat) (n : nat) : (term32 m n) = True.
Proof. exact (EQ_MP (@lem168300 m n) (@lem168299 m n)). Qed.
Lemma lem168941 (n : nat) (d' : nat) (r1 : nat) : (term187 n d' r1) = True.
Proof. exact (@lem168940 n (term76 n d' r1)). Qed.
Lemma lem168942 (n : nat) (d' : nat) (r1 : nat) : (term186 n d' r1) = True.
Proof. exact (TRANS (@lem168938 n d' r1) (@lem168941 n d' r1)). Qed.
Lemma lem168943 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem168944 (n : nat) (d' : nat) (r1 : nat) : (term180 n d' r1) = (~ True).
Proof. exact (MK_COMB (@lem168943) (@lem168942 n d' r1)). Qed.
Lemma lem168946 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem168947 (n : nat) (d' : nat) (r1 : nat) : (term180 n d' r1) = False.
Proof. exact (TRANS (@lem168944 n d' r1) (@lem168946)). Qed.
Lemma lem168948 (d' : nat) (r1 : nat) (n : nat) : (term179 d' r1 n) = False.
Proof. exact (TRANS (@lem168923 n d' r1) (@lem168947 n d' r1)). Qed.
Lemma lem168949 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168950 (d' : nat) (r1 : nat) (n : nat) : (term188 d' r1 n) = (imp False).
Proof. exact (MK_COMB (@lem168949) (@lem168948 d' r1 n)). Qed.
Lemma lem168954 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (EQ_MP (@lem168317 m n) (@lem168316 m n)). Qed.
Lemma lem168955 (n : nat) (d' : nat) : (term43 n d') = (term44 n d').
Proof. exact (@lem168954 n d'). Qed.
Lemma lem168956 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem168957 (n : nat) (d' : nat) : (term182 n d') = (term183 n d').
Proof. exact (MK_COMB (@lem168956) (@lem168955 n d')). Qed.
Lemma lem168958 (r1 : nat) : r1 = r1.
Proof. exact (eq_refl r1). Qed.
Lemma lem168959 (n : nat) (d' : nat) (r1 : nat) : (term181 n d' r1) = (term184 n d' r1).
Proof. exact (MK_COMB (@lem168957 n d') (@lem168958 r1)). Qed.
Lemma lem168961 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term12 m n p).
Proof. exact (EQ_MP (@lem168292 m n p) (@lem168291 m n p)). Qed.
Lemma lem168962 (n : nat) (d' : nat) (r1 : nat) : (term184 n d' r1) = (term185 n d' r1).
Proof. exact (@lem168961 n (Nat.mul n d') r1). Qed.
Lemma lem168963 (n : nat) (d' : nat) (r1 : nat) : (term181 n d' r1) = (term185 n d' r1).
Proof. exact (TRANS (@lem168959 n d' r1) (@lem168962 n d' r1)). Qed.
Lemma lem168964 (r1 : nat) : (@eq nat r1) = (@eq nat r1).
Proof. exact (eq_refl (@eq nat r1)). Qed.
Lemma lem168965 (n : nat) (d' : nat) (r1 : nat) : (r1 = (term181 n d' r1)) = (r1 = (term185 n d' r1)).
Proof. exact (MK_COMB (@lem168964 r1) (@lem168963 n d' r1)). Qed.
Lemma lem168968 (n : nat) (d' : nat) (r1 : nat) : (term154 n d' r1) = (term192 n d' r1).
Proof. exact (MK_COMB (@lem168950 d' r1 n) (@lem168965 n d' r1)). Qed.
Lemma lem168970 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem168971 (n : nat) (d' : nat) (r1 : nat) : (term192 n d' r1) = True.
Proof. exact (@lem168970 (r1 = (term185 n d' r1))). Qed.
Lemma lem168972 (n : nat) (d' : nat) (r1 : nat) : (term154 n d' r1) = True.
Proof. exact (TRANS (@lem168968 n d' r1) (@lem168971 n d' r1)). Qed.
Lemma lem168973 (n : nat) (d' : nat) (r1 : nat) : True = (term154 n d' r1).
Proof. exact (SYM (@lem168972 n d' r1)). Qed.
Lemma lem168974 (n : nat) (d' : nat) (r1 : nat) : term154 n d' r1.
Proof. exact (EQ_MP (@lem168973 n d' r1) (@lem0)). Qed.
Lemma lem168975 (n : nat) (d' : nat) (r1 : nat) : term156 n d' r1.
Proof. exact (fun h0 : term117 n d' r1 => @lem168974 n d' r1). Qed.
Lemma lem168980 (n : nat) (r1 : nat) : term160 n r1.
Proof. exact (fun d' : nat => @lem168975 n d' r1). Qed.
Lemma lem168981 (n : nat) (r1 : nat) : term162 n r1.
Proof. exact (conj (@lem168918 n r1) (@lem168980 n r1)). Qed.
Lemma lem168982 (n : nat) (r1 : nat) : term167 n r1.
Proof. exact (@lem168753 n r1 (@lem168981 n r1)). Qed.
Lemma lem168983 (n : nat) (d' : nat) (r2 : nat) : term131 n d' r2.
Proof. exact (fun h0 : term116 n d' r2 => @lem168866 n d' r2). Qed.
Lemma lem168988 (n : nat) (r2 : nat) : term135 n r2.
Proof. exact (fun d' : nat => @lem168983 n d' r2). Qed.
Lemma lem168989 (n : nat) (r2 : nat) : term137 n r2.
Proof. exact (conj (@lem168808 n r2) (@lem168988 n r2)). Qed.
Lemma lem168990 (n : nat) (r2 : nat) : term142 n r2.
Proof. exact (@lem168729 n r2 (@lem168989 n r2)). Qed.
Lemma lem168991 (n : nat) (r1 : nat) (d : nat) : term150 n r1 d.
Proof. exact (@lem168982 n r1 d). Qed.
Lemma lem168992 (n : nat) (d : nat) (r1 : nat) : (term150 n r1 d) = (term117 n d r1).
Proof. exact (eq_refl (term150 n r1 d)). Qed.
Lemma lem168993 (n : nat) (d : nat) (r1 : nat) : term117 n d r1.
Proof. exact (EQ_MP (@lem168992 n d r1) (@lem168991 n r1 d)). Qed.
Lemma lem168994 (n : nat) (r2 : nat) (d : nat) : term125 n r2 d.
Proof. exact (@lem168990 n r2 d). Qed.
Lemma lem168995 (n : nat) (d : nat) (r2 : nat) : (term125 n r2 d) = (term116 n d r2).
Proof. exact (eq_refl (term125 n r2 d)). Qed.
Lemma lem168996 (n : nat) (d : nat) (r2 : nat) : term116 n d r2.
Proof. exact (EQ_MP (@lem168995 n d r2) (@lem168994 n r2 d)). Qed.
Lemma lem168997 (d : nat) (n : nat) (r1 : nat) : term112 d n r1.
Proof. exact (EQ_MP (@lem168706 d n r1) (@lem168993 n d r1)). Qed.
Lemma lem168998 (d : nat) (n : nat) (r2 : nat) : term110 d n r2.
Proof. exact (EQ_MP (@lem168678 d n r2) (@lem168996 n d r2)). Qed.
Lemma lem168999 (d : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : (term76 d n r1) = r2) : term111 n r1 r2.
Proof. exact (EQ_MP (@lem168648 d n r1 r2 h1) (@lem168997 d n r1)). Qed.
Lemma lem169000 (r1 : nat) (d : nat) (n : nat) (r2 : nat) (h1 : r1 = (term76 d n r2)) : term109 n r1 r2.
Proof. exact (EQ_MP (@lem168624 r1 d n r2 h1) (@lem168998 d n r2)). Qed.
Lemma lem169001 (d : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r2 n) (h2 : (term76 d n r1) = r2) : r1 = r2.
Proof. exact (@lem168999 d n r1 r2 h2 (@lem168436 r2 n h1)). Qed.
Lemma lem169002 (d : nat) (r1 : nat) (r2 : nat) (n : nat) (h1 : Peano.lt r2 n) : term104 d n r1 r2.
Proof. exact (fun h0 : (term76 d n r1) = r2 => @lem169001 d n r1 r2 h1 h0). Qed.
Lemma lem169003 (r1 : nat) (d : nat) (n : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : r1 = (term76 d n r2)) : r1 = r2.
Proof. exact (@lem169000 r1 d n r2 h2 (@lem168434 r1 n h1)). Qed.
Lemma lem169004 (d : nat) (r2 : nat) (r1 : nat) (n : nat) (h1 : Peano.lt r1 n) : term99 d n r1 r2.
Proof. exact (fun h0 : r1 = (term76 d n r2) => @lem169003 r1 d n r2 h1 h0). Qed.
Lemma lem169005 (d : nat) (q2 : nat) (r1 : nat) (r2 : nat) (n : nat) (h1 : Peano.lt r2 n) : term91 d q2 n r1 r2.
Proof. exact (EQ_MP (@lem168595 d q2 n r1 r2) (@lem169002 d r1 r2 n h1)). Qed.
Lemma lem169006 (q1 : nat) (d : nat) (r2 : nat) (r1 : nat) (n : nat) (h1 : Peano.lt r1 n) : term85 q1 d n r1 r2.
Proof. exact (EQ_MP (@lem168555 q1 d n r1 r2) (@lem169004 d r2 r1 n h1)). Qed.
Lemma lem169007 (r1 : nat) (r2 : nat) (n : nat) (q1 : nat) (q2 : nat) (d : nat) (h1 : Peano.lt r2 n) (h2 : q1 = (Nat.add q2 d)) : term81 q1 q2 n r1 r2.
Proof. exact (EQ_MP (@lem168517 n r1 r2 q1 q2 d h2) (@lem169005 d q2 r1 r2 n h1)). Qed.
Lemma lem169008 (r1 : nat) (r2 : nat) (n : nat) (q2 : nat) (q1 : nat) (h1 : Peano.lt r2 n) (h2 : Peano.le q2 q1) : term81 q1 q2 n r1 r2.
Proof. exact (ex_elim (@lem168503 q2 q1 h2) (fun d : nat => fun h0 : term193 q1 q2 d => @lem169007 r1 r2 n q1 q2 d h1 h0)). Qed.
Lemma lem169009 (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) (n : nat) (h1 : Peano.lt r2 n) : term194 q1 q2 n r1 r2.
Proof. exact (fun h0 : Peano.le q2 q1 => @lem169008 r1 r2 n q2 q1 h1 h0). Qed.
Lemma lem169010 (r2 : nat) (r1 : nat) (n : nat) (q2 : nat) (q1 : nat) (d : nat) (h1 : Peano.lt r1 n) (h2 : q2 = (Nat.add q1 d)) : term81 q1 q2 n r1 r2.
Proof. exact (EQ_MP (@lem168492 n r1 r2 q2 q1 d h2) (@lem169006 q1 d r2 r1 n h1)). Qed.
Lemma lem169011 (r2 : nat) (r1 : nat) (n : nat) (q1 : nat) (q2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.le q1 q2) : term81 q1 q2 n r1 r2.
Proof. exact (ex_elim (@lem168478 q1 q2 h2) (fun d : nat => fun h0 : term193 q2 q1 d => @lem169010 r2 r1 n q2 q1 d h1 h0)). Qed.
Lemma lem169012 (q1 : nat) (q2 : nat) (r2 : nat) (r1 : nat) (n : nat) (h1 : Peano.lt r1 n) : term195 q1 q2 n r1 r2.
Proof. exact (fun h0 : Peano.le q1 q2 => @lem169011 r2 r1 n q1 q2 h1 h0). Qed.
Lemma lem169013 (r1 : nat) (r2 : nat) (n : nat) (q2 : nat) (q1 : nat) (h1 : Peano.lt r2 n) (h2 : Peano.le q2 q1) : term81 q1 q2 n r1 r2.
Proof. exact (@lem169009 q1 q2 r1 r2 n h1 (@lem168430 q2 q1 h2)). Qed.
Lemma lem169014 (r2 : nat) (r1 : nat) (n : nat) (q1 : nat) (q2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.le q1 q2) : term81 q1 q2 n r1 r2.
Proof. exact (@lem169012 q1 q2 r2 r1 n h1 (@lem168429 q1 q2 h2)). Qed.
Lemma lem169015 (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) (n : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) : term81 q1 q2 n r1 r2.
Proof. exact (or_elim (@lem168428 q2 q1) (fun h0 : Peano.le q1 q2 => @lem169014 r2 r1 n q1 q2 h1 h0) (fun h0 : Peano.le q2 q1 => @lem169013 r1 r2 n q2 q1 h2 h0)). Qed.
Lemma lem169016 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) : term80 m q2 n r1 r2.
Proof. exact (EQ_MP (@lem168467 q2 r2 m q1 n r1 h3) (@lem169015 q1 q2 r1 r2 n h1 h2)). Qed.
Lemma lem169017 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) : r1 = r2.
Proof. exact (@lem169016 q2 r2 m q1 n r1 h1 h2 h3 (@lem168437 m q2 n r2 h4)). Qed.
Lemma lem169018 (r1 : nat) (r2 : nat) (h1 : r1 = r2) : r1 = r2.
Proof. exact (h1). Qed.
Lemma lem169019 (q1 : nat) (q2 : nat) (r2 : nat) : (term196 q1 q2 r2) = (term196 q1 q2 r2).
Proof. exact (eq_refl (term196 q1 q2 r2)). Qed.
Lemma lem169020 (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) (h1 : r1 = r2) : (term197 q1 q2 r2 r1) = (term198 q1 q2 r2).
Proof. exact (MK_COMB (@lem169019 q1 q2 r2) (@lem169018 r1 r2 h1)). Qed.
Lemma lem169021 (q1 : nat) (q2 : nat) (r2 : nat) : (term198 q1 q2 r2) = (term199 q1 q2 r2).
Proof. exact (eq_refl (term198 q1 q2 r2)). Qed.
Lemma lem169022 (q1 : nat) (q2 : nat) (r2 : nat) (r1 : nat) : (term200 q1 q2 r2 r1) = (term200 q1 q2 r2 r1).
Proof. exact (eq_refl (term200 q1 q2 r2 r1)). Qed.
Lemma lem169023 (r1 : nat) (q1 : nat) (q2 : nat) (r2 : nat) : ((term197 q1 q2 r2 r1) = (term198 q1 q2 r2)) = ((term197 q1 q2 r2 r1) = (term199 q1 q2 r2)).
Proof. exact (MK_COMB (@lem169022 q1 q2 r2 r1) (@lem169021 q1 q2 r2)). Qed.
Lemma lem169024 (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) : (term197 q1 q2 r2 r1) = (term201 q1 q2 r1 r2).
Proof. exact (eq_refl (term197 q1 q2 r2 r1)). Qed.
Lemma lem169025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem169026 (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) : (term200 q1 q2 r2 r1) = (term202 q1 q2 r1 r2).
Proof. exact (MK_COMB (@lem169025) (@lem169024 q1 q2 r1 r2)). Qed.
Lemma lem169027 (q1 : nat) (q2 : nat) (r2 : nat) : (term199 q1 q2 r2) = (term199 q1 q2 r2).
Proof. exact (eq_refl (term199 q1 q2 r2)). Qed.
Lemma lem169028 (r1 : nat) (q1 : nat) (q2 : nat) (r2 : nat) : ((term197 q1 q2 r2 r1) = (term199 q1 q2 r2)) = ((term201 q1 q2 r1 r2) = (term199 q1 q2 r2)).
Proof. exact (MK_COMB (@lem169026 q1 q2 r1 r2) (@lem169027 q1 q2 r2)). Qed.
Lemma lem169029 (r1 : nat) (q1 : nat) (q2 : nat) (r2 : nat) : ((term197 q1 q2 r2 r1) = (term198 q1 q2 r2)) = ((term201 q1 q2 r1 r2) = (term199 q1 q2 r2)).
Proof. exact (TRANS (@lem169023 r1 q1 q2 r2) (@lem169028 r1 q1 q2 r2)). Qed.
Lemma lem169030 (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) (h1 : r1 = r2) : (term201 q1 q2 r1 r2) = (term199 q1 q2 r2).
Proof. exact (EQ_MP (@lem169029 r1 q1 q2 r2) (@lem169020 q1 q2 r1 r2 h1)). Qed.
Lemma lem169031 (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) (h1 : r1 = r2) : (term199 q1 q2 r2) = (term201 q1 q2 r1 r2).
Proof. exact (SYM (@lem169030 q1 q2 r1 r2 h1)). Qed.
Lemma lem169032 (m : nat) (q1 : nat) (n : nat) : (term203 m q1 n) = (term203 m q1 n).
Proof. exact (eq_refl (term203 m q1 n)). Qed.
Lemma lem169033 (m : nat) (q1 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : r1 = r2) : (term204 m q1 n r1) = (term204 m q1 n r2).
Proof. exact (MK_COMB (@lem169032 m q1 n) (@lem169018 r1 r2 h1)). Qed.
Lemma lem169034 (m : nat) (q1 : nat) (n : nat) (r2 : nat) : (term204 m q1 n r2) = (m = (term76 q1 n r2)).
Proof. exact (eq_refl (term204 m q1 n r2)). Qed.
Lemma lem169035 (m : nat) (q1 : nat) (n : nat) (r1 : nat) : (term205 m q1 n r1) = (term205 m q1 n r1).
Proof. exact (eq_refl (term205 m q1 n r1)). Qed.
Lemma lem169036 (r1 : nat) (m : nat) (q1 : nat) (n : nat) (r2 : nat) : ((term204 m q1 n r1) = (term204 m q1 n r2)) = ((term204 m q1 n r1) = (m = (term76 q1 n r2))).
Proof. exact (MK_COMB (@lem169035 m q1 n r1) (@lem169034 m q1 n r2)). Qed.
Lemma lem169037 (m : nat) (q1 : nat) (n : nat) (r1 : nat) : (term204 m q1 n r1) = (m = (term76 q1 n r1)).
Proof. exact (eq_refl (term204 m q1 n r1)). Qed.
Lemma lem169038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem169039 (m : nat) (q1 : nat) (n : nat) (r1 : nat) : (term205 m q1 n r1) = (term206 m q1 n r1).
Proof. exact (MK_COMB (@lem169038) (@lem169037 m q1 n r1)). Qed.
Lemma lem169040 (m : nat) (q1 : nat) (n : nat) (r2 : nat) : (m = (term76 q1 n r2)) = (m = (term76 q1 n r2)).
Proof. exact (eq_refl (m = (term76 q1 n r2))). Qed.
Lemma lem169041 (r1 : nat) (m : nat) (q1 : nat) (n : nat) (r2 : nat) : ((term204 m q1 n r1) = (m = (term76 q1 n r2))) = ((m = (term76 q1 n r1)) = (m = (term76 q1 n r2))).
Proof. exact (MK_COMB (@lem169039 m q1 n r1) (@lem169040 m q1 n r2)). Qed.
Lemma lem169042 (r1 : nat) (m : nat) (q1 : nat) (n : nat) (r2 : nat) : ((term204 m q1 n r1) = (term204 m q1 n r2)) = ((m = (term76 q1 n r1)) = (m = (term76 q1 n r2))).
Proof. exact (TRANS (@lem169036 r1 m q1 n r2) (@lem169041 r1 m q1 n r2)). Qed.
Lemma lem169043 (m : nat) (q1 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : r1 = r2) : (m = (term76 q1 n r1)) = (m = (term76 q1 n r2)).
Proof. exact (EQ_MP (@lem169042 r1 m q1 n r2) (@lem169033 m q1 n r1 r2 h1)). Qed.
Lemma lem169044 (m : nat) (q1 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : m = (term76 q1 n r1)) (h2 : r1 = r2) : m = (term76 q1 n r2).
Proof. exact (EQ_MP (@lem169043 m q1 n r1 r2 h2) (@lem168435 m q1 n r1 h1)). Qed.
Lemma lem169045 (n : nat) : (term207 n) = (term207 n).
Proof. exact (eq_refl (term207 n)). Qed.
Lemma lem169046 (n : nat) (r1 : nat) (r2 : nat) (h1 : r1 = r2) : (term208 n r1) = (term208 n r2).
Proof. exact (MK_COMB (@lem169045 n) (@lem169018 r1 r2 h1)). Qed.
Lemma lem169047 (r2 : nat) (n : nat) : (term208 n r2) = (Peano.lt r2 n).
Proof. exact (eq_refl (term208 n r2)). Qed.
Lemma lem169048 (n : nat) (r1 : nat) : (term209 n r1) = (term209 n r1).
Proof. exact (eq_refl (term209 n r1)). Qed.
Lemma lem169049 (r1 : nat) (r2 : nat) (n : nat) : ((term208 n r1) = (term208 n r2)) = ((term208 n r1) = (Peano.lt r2 n)).
Proof. exact (MK_COMB (@lem169048 n r1) (@lem169047 r2 n)). Qed.
Lemma lem169050 (r1 : nat) (n : nat) : (term208 n r1) = (Peano.lt r1 n).
Proof. exact (eq_refl (term208 n r1)). Qed.
Lemma lem169051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem169052 (r1 : nat) (n : nat) : (term209 n r1) = (term210 r1 n).
Proof. exact (MK_COMB (@lem169051) (@lem169050 r1 n)). Qed.
Lemma lem169053 (r2 : nat) (n : nat) : (Peano.lt r2 n) = (Peano.lt r2 n).
Proof. exact (eq_refl (Peano.lt r2 n)). Qed.
Lemma lem169054 (r1 : nat) (r2 : nat) (n : nat) : ((term208 n r1) = (Peano.lt r2 n)) = ((Peano.lt r1 n) = (Peano.lt r2 n)).
Proof. exact (MK_COMB (@lem169052 r1 n) (@lem169053 r2 n)). Qed.
Lemma lem169055 (r1 : nat) (r2 : nat) (n : nat) : ((term208 n r1) = (term208 n r2)) = ((Peano.lt r1 n) = (Peano.lt r2 n)).
Proof. exact (TRANS (@lem169049 r1 r2 n) (@lem169054 r1 r2 n)). Qed.
Lemma lem169056 (n : nat) (r1 : nat) (r2 : nat) (h1 : r1 = r2) : (Peano.lt r1 n) = (Peano.lt r2 n).
Proof. exact (EQ_MP (@lem169055 r1 r2 n) (@lem169046 n r1 r2 h1)). Qed.
Lemma lem169057 (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : r1 = r2) : Peano.lt r2 n.
Proof. exact (EQ_MP (@lem169056 n r1 r2 h2) (@lem168434 r1 n h1)). Qed.
Lemma lem169071 (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : m = (term76 q2 n r2)) : m = (term76 q2 n r2).
Proof. exact (h1). Qed.
Lemma lem169085 (r2 : nat) (n : nat) (h1 : Peano.lt r2 n) : Peano.lt r2 n.
Proof. exact (h1). Qed.
Lemma lem169091 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem169092 (x : nat) : (x = x) = True.
Proof. exact (@lem169091 nat x). Qed.
Lemma lem169093 (r2 : nat) : (r2 = r2) = True.
Proof. exact (@lem169092 r2). Qed.
Lemma lem169094 (q1 : nat) (q2 : nat) : (term211 q1 q2) = (term211 q1 q2).
Proof. exact (eq_refl (term211 q1 q2)). Qed.
Lemma lem169095 (r2 : nat) (q1 : nat) (q2 : nat) : (term199 q1 q2 r2) = (term212 q1 q2).
Proof. exact (MK_COMB (@lem169094 q1 q2) (@lem169093 r2)). Qed.
Lemma lem169097 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem169098 (q1 : nat) (q2 : nat) : (term212 q1 q2) = (q1 = q2).
Proof. exact (@lem169097 (q1 = q2)). Qed.
Lemma lem169101 (r2 : nat) (q1 : nat) (q2 : nat) : (term199 q1 q2 r2) = (q1 = q2).
Proof. exact (TRANS (@lem169095 r2 q1 q2) (@lem169098 q1 q2)). Qed.
Lemma lem169102 (q1 : nat) (q2 : nat) (r2 : nat) : (q1 = q2) = (term199 q1 q2 r2).
Proof. exact (SYM (@lem169101 r2 q1 q2)). Qed.
Lemma lem169103 (q1 : nat) (q2 : nat) (h1 : q1 = q2) : q1 = q2.
Proof. exact (h1). Qed.
Lemma lem169104 (q1 : nat) (q2 : nat) (h1 : q1 = q2) : q2 = q1.
Proof. exact (SYM (@lem169103 q1 q2 h1)). Qed.
Lemma lem169105 (q2 : nat) (q1 : nat) (h1 : q2 = q1) : q2 = q1.
Proof. exact (h1). Qed.
Lemma lem169106 (q2 : nat) (q1 : nat) (h1 : q2 = q1) : q1 = q2.
Proof. exact (SYM (@lem169105 q2 q1 h1)). Qed.
Lemma lem169107 (q2 : nat) (q1 : nat) : (q1 = q2) = (q2 = q1).
Proof. exact (prop_ext (fun h1 : q1 = q2 => @lem169104 q1 q2 h1) (fun h1 : q2 = q1 => @lem169106 q2 q1 h1)). Qed.
Lemma lem169108 (q1 : nat) (q2 : nat) : (q2 = q1) = (q1 = q2).
Proof. exact (SYM (@lem169107 q2 q1)). Qed.
Lemma lem169109 (m : nat) : term213 m.
Proof. exact (@lem84913 m). Qed.
Lemma lem169110 (m : nat) : (term213 m) = (term214 m).
Proof. exact (eq_refl (term213 m)). Qed.
Lemma lem169111 (m : nat) : term214 m.
Proof. exact (EQ_MP (@lem169110 m) (@lem169109 m)). Qed.
Lemma lem169112 (m : nat) (n : nat) : term215 m n.
Proof. exact (@lem169111 m n). Qed.
Lemma lem169113 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (eq_refl (term215 m n)). Qed.
Lemma lem169114 (m : nat) (n : nat) : term216 m n.
Proof. exact (EQ_MP (@lem169113 m n) (@lem169112 m n)). Qed.
Lemma lem169115 (m : nat) (n : nat) (p : nat) : term217 m n p.
Proof. exact (@lem169114 m n p). Qed.
Lemma lem169116 (m : nat) (n : nat) (p : nat) : (term217 m n p) = (((Nat.mul m p) = (Nat.mul n p)) = (term218 m n p)).
Proof. exact (eq_refl (term217 m n p)). Qed.
Lemma lem169118 (m : nat) : term219 m.
Proof. exact (@lem79714 m). Qed.
Lemma lem169119 (m : nat) : (term219 m) = (term220 m).
Proof. exact (eq_refl (term219 m)). Qed.
Lemma lem169120 (m : nat) : term220 m.
Proof. exact (EQ_MP (@lem169119 m) (@lem169118 m)). Qed.
Lemma lem169121 (m : nat) (n : nat) : term221 m n.
Proof. exact (@lem169120 m n). Qed.
Lemma lem169122 (m : nat) (n : nat) : (term221 m n) = (term222 m n).
Proof. exact (eq_refl (term221 m n)). Qed.
Lemma lem169123 (m : nat) (n : nat) : term222 m n.
Proof. exact (EQ_MP (@lem169122 m n) (@lem169121 m n)). Qed.
Lemma lem169124 (m : nat) (n : nat) (p : nat) : term223 m n p.
Proof. exact (@lem169123 m n p). Qed.
Lemma lem169125 (p : nat) (m : nat) (n : nat) : (term223 m n p) = (((Nat.add m p) = (Nat.add n p)) = (m = n)).
Proof. exact (eq_refl (term223 m n p)). Qed.
Lemma lem169138 (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : m = (term76 q2 n r2)) : m = (term76 q2 n r2).
Proof. exact (h1). Qed.
Lemma lem169139 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem169140 (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : m = (term76 q2 n r2)) : (@eq nat m) = (term77 q2 n r2).
Proof. exact (MK_COMB (@lem169139) (@lem169138 m q2 n r2 h1)). Qed.
Lemma lem169141 (q1 : nat) (n : nat) (r2 : nat) : (term76 q1 n r2) = (term76 q1 n r2).
Proof. exact (eq_refl (term76 q1 n r2)). Qed.
Lemma lem169142 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : m = (term76 q2 n r2)) : (m = (term76 q1 n r2)) = ((term76 q2 n r2) = (term76 q1 n r2)).
Proof. exact (MK_COMB (@lem169140 m q2 n r2 h1) (@lem169141 q1 n r2)). Qed.
Lemma lem169144 (p : nat) (m : nat) (n : nat) : ((Nat.add m p) = (Nat.add n p)) = (m = n).
Proof. exact (EQ_MP (@lem169125 p m n) (@lem169124 m n p)). Qed.
Lemma lem169145 (r2 : nat) (q2 : nat) (q1 : nat) (n : nat) : ((term76 q2 n r2) = (term76 q1 n r2)) = ((Nat.mul q2 n) = (Nat.mul q1 n)).
Proof. exact (@lem169144 r2 (Nat.mul q2 n) (Nat.mul q1 n)). Qed.
Lemma lem169147 (m : nat) (n : nat) (p : nat) : ((Nat.mul m p) = (Nat.mul n p)) = (term218 m n p).
Proof. exact (EQ_MP (@lem169116 m n p) (@lem169115 m n p)). Qed.
Lemma lem169148 (q2 : nat) (q1 : nat) (n : nat) : ((Nat.mul q2 n) = (Nat.mul q1 n)) = (term218 q2 q1 n).
Proof. exact (@lem169147 q2 q1 n). Qed.
Lemma lem169155 (r2 : nat) (q2 : nat) (q1 : nat) (n : nat) : ((term76 q2 n r2) = (term76 q1 n r2)) = (term218 q2 q1 n).
Proof. exact (TRANS (@lem169145 r2 q2 q1 n) (@lem169148 q2 q1 n)). Qed.
Lemma lem169156 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : m = (term76 q2 n r2)) : (m = (term76 q1 n r2)) = (term218 q2 q1 n).
Proof. exact (TRANS (@lem169142 q1 m q2 n r2 h1) (@lem169155 r2 q2 q1 n)). Qed.
Lemma lem169157 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem169158 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : m = (term76 q2 n r2)) : (term78 m q1 n r2) = (term224 q2 q1 n).
Proof. exact (MK_COMB (@lem169157) (@lem169156 q1 m q2 n r2 h1)). Qed.
Lemma lem169161 (q2 : nat) (q1 : nat) : (q2 = q1) = (q2 = q1).
Proof. exact (eq_refl (q2 = q1)). Qed.
Lemma lem169162 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : m = (term76 q2 n r2)) : (term225 m n r2 q2 q1) = (term226 n q2 q1).
Proof. exact (MK_COMB (@lem169158 q1 m q2 n r2 h1) (@lem169161 q2 q1)). Qed.
Lemma lem169165 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : m = (term76 q2 n r2)) : (term226 n q2 q1) = (term225 m n r2 q2 q1).
Proof. exact (SYM (@lem169162 q1 m q2 n r2 h1)). Qed.
Lemma lem169166 (n : nat) : term227 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem169167 (n : nat) : (term227 n) = (term228 n).
Proof. exact (eq_refl (term227 n)). Qed.
Lemma lem169168 (n : nat) : term228 n.
Proof. exact (EQ_MP (@lem169167 n) (@lem169166 n)). Qed.
Lemma lem169169 (n : nat) : (term228 n) = ((term228 n) = True).
Proof. exact (@lem7 (term228 n)). Qed.
Lemma lem169171 (m : nat) : term33 m.
Proof. exact (@lem168247 m). Qed.
Lemma lem169172 (m : nat) : (term33 m) = (term4 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem169173 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem169172 m) (@lem169171 m)). Qed.
Lemma lem169174 (m : nat) (n : nat) : term34 m n.
Proof. exact (@lem169173 m n). Qed.
Lemma lem169175 (m : nat) (n : nat) : (term34 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem169180 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem169175 m n) (@lem169174 m n)). Qed.
Lemma lem169181 (n : nat) (r2 : nat) : (Peano.lt r2 n) = (term0 n r2).
Proof. exact (@lem169180 n r2). Qed.
Lemma lem169183 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem169184 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem169185 (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.le n) = term229.
Proof. exact (MK_COMB (@lem169184) (@lem169183 n h1)). Qed.
Lemma lem169186 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem169187 (r2 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.le n r2) = (term228 r2).
Proof. exact (MK_COMB (@lem169185 n h1) (@lem169186 r2)). Qed.
Lemma lem169189 (n : nat) : (term228 n) = True.
Proof. exact (EQ_MP (@lem169169 n) (@lem169168 n)). Qed.
Lemma lem169190 (r2 : nat) : (term228 r2) = True.
Proof. exact (@lem169189 r2). Qed.
Lemma lem169191 (r2 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.le n r2) = True.
Proof. exact (TRANS (@lem169187 r2 n h1) (@lem169190 r2)). Qed.
Lemma lem169192 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem169193 (r2 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term0 n r2) = (~ True).
Proof. exact (MK_COMB (@lem169192) (@lem169191 r2 n h1)). Qed.
Lemma lem169195 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem169196 (r2 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term0 n r2) = False.
Proof. exact (TRANS (@lem169193 r2 n h1) (@lem169195)). Qed.
Lemma lem169197 (r2 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.lt r2 n) = False.
Proof. exact (TRANS (@lem169181 n r2) (@lem169196 r2 n h1)). Qed.
Lemma lem169198 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem169199 (r2 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term107 r2 n) = (imp False).
Proof. exact (MK_COMB (@lem169198) (@lem169197 r2 n h1)). Qed.
Lemma lem169203 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem169175 m n) (@lem169174 m n)). Qed.
Lemma lem169204 (n : nat) (r2 : nat) : (Peano.lt r2 n) = (term0 n r2).
Proof. exact (@lem169203 n r2). Qed.
Lemma lem169206 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem169207 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem169208 (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.le n) = term229.
Proof. exact (MK_COMB (@lem169207) (@lem169206 n h1)). Qed.
Lemma lem169209 (r2 : nat) : r2 = r2.
Proof. exact (eq_refl r2). Qed.
Lemma lem169210 (r2 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.le n r2) = (term228 r2).
Proof. exact (MK_COMB (@lem169208 n h1) (@lem169209 r2)). Qed.
Lemma lem169212 (n : nat) : (term228 n) = True.
Proof. exact (EQ_MP (@lem169169 n) (@lem169168 n)). Qed.
Lemma lem169213 (r2 : nat) : (term228 r2) = True.
Proof. exact (@lem169212 r2). Qed.
Lemma lem169214 (r2 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.le n r2) = True.
Proof. exact (TRANS (@lem169210 r2 n h1) (@lem169213 r2)). Qed.
Lemma lem169215 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem169216 (r2 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term0 n r2) = (~ True).
Proof. exact (MK_COMB (@lem169215) (@lem169214 r2 n h1)). Qed.
Lemma lem169218 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem169219 (r2 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term0 n r2) = False.
Proof. exact (TRANS (@lem169216 r2 n h1) (@lem169218)). Qed.
Lemma lem169220 (r2 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.lt r2 n) = False.
Proof. exact (TRANS (@lem169204 n r2) (@lem169219 r2 n h1)). Qed.
Lemma lem169221 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem169222 (r2 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term107 r2 n) = (imp False).
Proof. exact (MK_COMB (@lem169221) (@lem169220 r2 n h1)). Qed.
Lemma lem169232 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem169233 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem169234 (n : nat) (h1 : n = (NUMERAL 0)) : (@eq nat n) = term230.
Proof. exact (MK_COMB (@lem169233) (@lem169232 n h1)). Qed.
Lemma lem169235 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem169236 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem169234 n h1) (@lem169235)). Qed.
Lemma lem169238 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem169239 (x : nat) : (x = x) = True.
Proof. exact (@lem169238 nat x). Qed.
Lemma lem169240 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem169239 (NUMERAL 0)). Qed.
Lemma lem169241 (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem169236 n h1) (@lem169240)). Qed.
Lemma lem169242 (q2 : nat) (q1 : nat) : (term231 q2 q1) = (term231 q2 q1).
Proof. exact (eq_refl (term231 q2 q1)). Qed.
Lemma lem169243 (q2 : nat) (q1 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term218 q2 q1 n) = (term232 q2 q1).
Proof. exact (MK_COMB (@lem169242 q2 q1) (@lem169241 n h1)). Qed.
Lemma lem169245 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem169246 (q2 : nat) (q1 : nat) : (term232 q2 q1) = True.
Proof. exact (@lem169245 (q2 = q1)). Qed.
Lemma lem169247 (q2 : nat) (q1 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term218 q2 q1 n) = True.
Proof. exact (TRANS (@lem169243 q2 q1 n h1) (@lem169246 q2 q1)). Qed.
Lemma lem169248 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem169249 (q2 : nat) (q1 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term224 q2 q1 n) = (imp True).
Proof. exact (MK_COMB (@lem169248) (@lem169247 q2 q1 n h1)). Qed.
Lemma lem169252 (q2 : nat) (q1 : nat) : (q2 = q1) = (q2 = q1).
Proof. exact (eq_refl (q2 = q1)). Qed.
Lemma lem169253 (q2 : nat) (q1 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term226 n q2 q1) = (term233 q2 q1).
Proof. exact (MK_COMB (@lem169249 q2 q1 n h1) (@lem169252 q2 q1)). Qed.
Lemma lem169255 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem169256 (q2 : nat) (q1 : nat) : (term233 q2 q1) = (q2 = q1).
Proof. exact (@lem169255 (q2 = q1)). Qed.
Lemma lem169259 (q2 : nat) (q1 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term226 n q2 q1) = (q2 = q1).
Proof. exact (TRANS (@lem169253 q2 q1 n h1) (@lem169256 q2 q1)). Qed.
Lemma lem169260 (r2 : nat) (q2 : nat) (q1 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term234 r2 n q2 q1) = (term235 q2 q1).
Proof. exact (MK_COMB (@lem169222 r2 n h1) (@lem169259 q2 q1 n h1)). Qed.
Lemma lem169262 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem169263 (q2 : nat) (q1 : nat) : (term235 q2 q1) = True.
Proof. exact (@lem169262 (q2 = q1)). Qed.
Lemma lem169264 (r2 : nat) (q2 : nat) (q1 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term234 r2 n q2 q1) = True.
Proof. exact (TRANS (@lem169260 r2 q2 q1 n h1) (@lem169263 q2 q1)). Qed.
Lemma lem169265 (r2 : nat) (q2 : nat) (q1 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term236 r2 n q2 q1) = (False -> True).
Proof. exact (MK_COMB (@lem169199 r2 n h1) (@lem169264 r2 q2 q1 n h1)). Qed.
Lemma lem169267 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem169268 : (False -> True) = True.
Proof. exact (@lem169267 True). Qed.
Lemma lem169269 (r2 : nat) (q2 : nat) (q1 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term236 r2 n q2 q1) = True.
Proof. exact (TRANS (@lem169265 r2 q2 q1 n h1) (@lem169268)). Qed.
Lemma lem169270 (r2 : nat) (q2 : nat) (q1 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term236 r2 n q2 q1).
Proof. exact (SYM (@lem169269 r2 q2 q1 n h1)). Qed.
Lemma lem169271 (r2 : nat) (q2 : nat) (q1 : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term236 r2 n q2 q1.
Proof. exact (EQ_MP (@lem169270 r2 q2 q1 n h1) (@lem0)). Qed.
Lemma lem169277 (m : nat) : term33 m.
Proof. exact (@lem168247 m). Qed.
Lemma lem169278 (m : nat) : (term33 m) = (term4 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem169279 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem169278 m) (@lem169277 m)). Qed.
Lemma lem169280 (m : nat) (n : nat) : term34 m n.
Proof. exact (@lem169279 m n). Qed.
Lemma lem169281 (m : nat) (n : nat) : (term34 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem169283 (n : nat) : term237 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem169299 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem169281 m n) (@lem169280 m n)). Qed.
Lemma lem169300 (n : nat) (r2 : nat) : (Peano.lt r2 n) = (term0 n r2).
Proof. exact (@lem169299 n r2). Qed.
Lemma lem169301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem169302 (n : nat) (r2 : nat) : (term107 r2 n) = (term176 n r2).
Proof. exact (MK_COMB (@lem169301) (@lem169300 n r2)). Qed.
Lemma lem169306 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem169281 m n) (@lem169280 m n)). Qed.
Lemma lem169307 (n : nat) (r2 : nat) : (Peano.lt r2 n) = (term0 n r2).
Proof. exact (@lem169306 n r2). Qed.
Lemma lem169308 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem169309 (n : nat) (r2 : nat) : (term107 r2 n) = (term176 n r2).
Proof. exact (MK_COMB (@lem169308) (@lem169307 n r2)). Qed.
Lemma lem169317 (n : nat) (h1 : term11 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem169283 n (@lem168252 n h1)). Qed.
Lemma lem169318 (q2 : nat) (q1 : nat) : (term231 q2 q1) = (term231 q2 q1).
Proof. exact (eq_refl (term231 q2 q1)). Qed.
Lemma lem169319 (q2 : nat) (q1 : nat) (n : nat) (h1 : term11 n) : (term218 q2 q1 n) = (term238 q2 q1).
Proof. exact (MK_COMB (@lem169318 q2 q1) (@lem169317 n h1)). Qed.
Lemma lem169321 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem169322 (q2 : nat) (q1 : nat) : (term238 q2 q1) = (q2 = q1).
Proof. exact (@lem169321 (q2 = q1)). Qed.
Lemma lem169325 (q2 : nat) (q1 : nat) (n : nat) (h1 : term11 n) : (term218 q2 q1 n) = (q2 = q1).
Proof. exact (TRANS (@lem169319 q2 q1 n h1) (@lem169322 q2 q1)). Qed.
Lemma lem169326 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem169327 (q2 : nat) (q1 : nat) (n : nat) (h1 : term11 n) : (term224 q2 q1 n) = (term239 q2 q1).
Proof. exact (MK_COMB (@lem169326) (@lem169325 q2 q1 n h1)). Qed.
Lemma lem169330 (q2 : nat) (q1 : nat) : (q2 = q1) = (q2 = q1).
Proof. exact (eq_refl (q2 = q1)). Qed.
Lemma lem169331 (q2 : nat) (q1 : nat) (n : nat) (h1 : term11 n) : (term226 n q2 q1) = (term240 q2 q1).
Proof. exact (MK_COMB (@lem169327 q2 q1 n h1) (@lem169330 q2 q1)). Qed.
Lemma lem169335 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem169336 (q2 : nat) (q1 : nat) : (term240 q2 q1) = True.
Proof. exact (@lem169335 (q2 = q1)). Qed.
Lemma lem169337 (q2 : nat) (q1 : nat) (n : nat) (h1 : term11 n) : (term226 n q2 q1) = True.
Proof. exact (TRANS (@lem169331 q2 q1 n h1) (@lem169336 q2 q1)). Qed.
Lemma lem169338 (q2 : nat) (q1 : nat) (r2 : nat) (n : nat) (h1 : term11 n) : (term234 r2 n q2 q1) = (term178 n r2).
Proof. exact (MK_COMB (@lem169309 n r2) (@lem169337 q2 q1 n h1)). Qed.
Lemma lem169340 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem169341 (n : nat) (r2 : nat) : (term178 n r2) = True.
Proof. exact (@lem169340 (term0 n r2)). Qed.
Lemma lem169342 (r2 : nat) (q2 : nat) (q1 : nat) (n : nat) (h1 : term11 n) : (term234 r2 n q2 q1) = True.
Proof. exact (TRANS (@lem169338 q2 q1 r2 n h1) (@lem169341 n r2)). Qed.
Lemma lem169343 (q2 : nat) (q1 : nat) (r2 : nat) (n : nat) (h1 : term11 n) : (term236 r2 n q2 q1) = (term178 n r2).
Proof. exact (MK_COMB (@lem169302 n r2) (@lem169342 r2 q2 q1 n h1)). Qed.
Lemma lem169345 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem169346 (n : nat) (r2 : nat) : (term178 n r2) = True.
Proof. exact (@lem169345 (term0 n r2)). Qed.
Lemma lem169347 (r2 : nat) (q2 : nat) (q1 : nat) (n : nat) (h1 : term11 n) : (term236 r2 n q2 q1) = True.
Proof. exact (TRANS (@lem169343 q2 q1 r2 n h1) (@lem169346 n r2)). Qed.
Lemma lem169348 (r2 : nat) (q2 : nat) (q1 : nat) (n : nat) (h1 : term11 n) : True = (term236 r2 n q2 q1).
Proof. exact (SYM (@lem169347 r2 q2 q1 n h1)). Qed.
Lemma lem169349 (r2 : nat) (q2 : nat) (q1 : nat) (n : nat) (h1 : term11 n) : term236 r2 n q2 q1.
Proof. exact (EQ_MP (@lem169348 r2 q2 q1 n h1) (@lem0)). Qed.
Lemma lem169350 (r2 : nat) (n : nat) (q2 : nat) (q1 : nat) : term236 r2 n q2 q1.
Proof. exact (or_elim (@lem168250 n) (fun h0 : n = (NUMERAL 0) => @lem169271 r2 q2 q1 n h0) (fun h0 : term11 n => @lem169349 r2 q2 q1 n h0)). Qed.
Lemma lem169351 (q2 : nat) (q1 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : r1 = r2) : term234 r2 n q2 q1.
Proof. exact (@lem169350 r2 n q2 q1 (@lem169057 n r1 r2 h1 h2)). Qed.
Lemma lem169352 (q2 : nat) (q1 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : r1 = r2) : term226 n q2 q1.
Proof. exact (@lem169351 q2 q1 n r1 r2 h1 h3 (@lem169085 r2 n h2)). Qed.
Lemma lem169353 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q2 n r2)) (h4 : r1 = r2) : term225 m n r2 q2 q1.
Proof. exact (EQ_MP (@lem169165 q1 m q2 n r2 h3) (@lem169352 q2 q1 n r1 r2 h1 h2 h4)). Qed.
Lemma lem169354 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) (h5 : r1 = r2) : q2 = q1.
Proof. exact (@lem169353 q1 m q2 n r1 r2 h1 h2 h4 h5 (@lem169044 m q1 n r1 r2 h3 h5)). Qed.
Lemma lem169355 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) (h5 : r1 = r2) : q1 = q2.
Proof. exact (EQ_MP (@lem169108 q1 q2) (@lem169354 q1 m q2 n r1 r2 h1 h2 h3 h4 h5)). Qed.
Lemma lem169356 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) (h5 : r1 = r2) : term199 q1 q2 r2.
Proof. exact (EQ_MP (@lem169102 q1 q2 r2) (@lem169355 q1 m q2 n r1 r2 h1 h2 h3 h4 h5)). Qed.
Lemma lem169357 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) (h5 : r1 = r2) : (Peano.lt r2 n) = (term199 q1 q2 r2).
Proof. exact (prop_ext (fun h6 : Peano.lt r2 n => @lem169356 q1 m q2 n r1 r2 h1 h2 h3 h4 h5) (fun h6 : term199 q1 q2 r2 => @lem169085 r2 n h2)). Qed.
Lemma lem169358 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) (h5 : r1 = r2) : term199 q1 q2 r2.
Proof. exact (EQ_MP (@lem169357 q1 m q2 n r1 r2 h1 h2 h3 h4 h5) (@lem169085 r2 n h2)). Qed.
Lemma lem169359 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) (h5 : r1 = r2) : (m = (term76 q2 n r2)) = (term199 q1 q2 r2).
Proof. exact (prop_ext (fun h6 : m = (term76 q2 n r2) => @lem169358 q1 m q2 n r1 r2 h1 h2 h3 h4 h5) (fun h6 : term199 q1 q2 r2 => @lem169071 m q2 n r2 h4)). Qed.
Lemma lem169360 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) (h5 : r1 = r2) : term199 q1 q2 r2.
Proof. exact (EQ_MP (@lem169359 q1 m q2 n r1 r2 h1 h2 h3 h4 h5) (@lem169071 m q2 n r2 h4)). Qed.
Lemma lem169361 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : m = (term76 q1 n r1)) (h3 : m = (term76 q2 n r2)) (h4 : r1 = r2) : (Peano.lt r2 n) = (term199 q1 q2 r2).
Proof. exact (prop_ext (fun h5 : Peano.lt r2 n => @lem169360 q1 m q2 n r1 r2 h1 h5 h2 h3 h4) (fun h5 : term199 q1 q2 r2 => @lem169057 n r1 r2 h1 h4)). Qed.
Lemma lem169362 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : m = (term76 q1 n r1)) (h3 : m = (term76 q2 n r2)) (h4 : r1 = r2) : term199 q1 q2 r2.
Proof. exact (EQ_MP (@lem169361 q1 m q2 n r1 r2 h1 h2 h3 h4) (@lem169057 n r1 r2 h1 h4)). Qed.
Lemma lem169363 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : m = (term76 q1 n r1)) (h3 : m = (term76 q2 n r2)) (h4 : r1 = r2) : term201 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169031 q1 q2 r1 r2 h4) (@lem169362 q1 m q2 n r1 r2 h1 h2 h3 h4)). Qed.
Lemma lem169364 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : m = (term76 q1 n r1)) (h3 : m = (term76 q2 n r2)) : term241 q1 q2 r1 r2.
Proof. exact (fun h0 : r1 = r2 => @lem169363 q1 m q2 n r1 r2 h1 h2 h3 h0). Qed.
Lemma lem169365 (q1 : nat) (m : nat) (q2 : nat) (n : nat) (r1 : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : m = (term76 q1 n r1)) (h3 : m = (term76 q2 n r2)) (h4 : r1 = r2) : term201 q1 q2 r1 r2.
Proof. exact (@lem169364 q1 r1 m q2 n r2 h1 h2 h3 (@lem168438 r1 r2 h4)). Qed.
Lemma lem169366 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) : (r1 = r2) = (term201 q1 q2 r1 r2).
Proof. exact (prop_ext (fun h5 : r1 = r2 => @lem169365 q1 m q2 n r1 r2 h1 h3 h4 h5) (fun h5 : term201 q1 q2 r1 r2 => @lem169017 q1 r1 m q2 n r2 h1 h2 h3 h4)). Qed.
Lemma lem169367 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) : term201 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169366 q1 r1 m q2 n r2 h1 h2 h3 h4) (@lem169017 q1 r1 m q2 n r2 h1 h2 h3 h4)). Qed.
Lemma lem169368 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term74 q1 r1 m q2 r2 n) : term75 m q2 r2 n.
Proof. exact (proj2 (@lem168431 q1 r1 m q2 r2 n h1)). Qed.
Lemma lem169369 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term74 q1 r1 m q2 r2 n) : term75 m q1 r1 n.
Proof. exact (proj1 (@lem168431 q1 r1 m q2 r2 n h1)). Qed.
Lemma lem169370 (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term75 m q2 r2 n) : Peano.lt r2 n.
Proof. exact (proj2 (@lem168432 m q2 r2 n h1)). Qed.
Lemma lem169371 (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term75 m q2 r2 n) : m = (term76 q2 n r2).
Proof. exact (proj1 (@lem168432 m q2 r2 n h1)). Qed.
Lemma lem169372 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) : (Peano.lt r2 n) = (term201 q1 q2 r1 r2).
Proof. exact (prop_ext (fun h5 : Peano.lt r2 n => @lem169367 q1 r1 m q2 n r2 h1 h2 h3 h4) (fun h5 : term201 q1 q2 r1 r2 => @lem168436 r2 n h2)). Qed.
Lemma lem169373 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) : term201 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169372 q1 r1 m q2 n r2 h1 h2 h3 h4) (@lem168436 r2 n h2)). Qed.
Lemma lem169374 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) : (m = (term76 q2 n r2)) = (term201 q1 q2 r1 r2).
Proof. exact (prop_ext (fun h5 : m = (term76 q2 n r2) => @lem169373 q1 r1 m q2 n r2 h1 h2 h3 h4) (fun h5 : term201 q1 q2 r1 r2 => @lem168437 m q2 n r2 h4)). Qed.
Lemma lem169375 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : Peano.lt r1 n) (h2 : Peano.lt r2 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) : term201 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169374 q1 r1 m q2 n r2 h1 h2 h3 h4) (@lem168437 m q2 n r2 h4)). Qed.
Lemma lem169376 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : term75 m q2 r2 n) (h2 : Peano.lt r1 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) : (Peano.lt r2 n) = (term201 q1 q2 r1 r2).
Proof. exact (prop_ext (fun h5 : Peano.lt r2 n => @lem169375 q1 r1 m q2 n r2 h2 h5 h3 h4) (fun h5 : term201 q1 q2 r1 r2 => @lem169370 m q2 r2 n h1)). Qed.
Lemma lem169377 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (n : nat) (r2 : nat) (h1 : term75 m q2 r2 n) (h2 : Peano.lt r1 n) (h3 : m = (term76 q1 n r1)) (h4 : m = (term76 q2 n r2)) : term201 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169376 q1 r1 m q2 n r2 h1 h2 h3 h4) (@lem169370 m q2 r2 n h1)). Qed.
Lemma lem169378 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : term75 m q2 r2 n) (h2 : Peano.lt r1 n) (h3 : m = (term76 q1 n r1)) : (m = (term76 q2 n r2)) = (term201 q1 q2 r1 r2).
Proof. exact (prop_ext (fun h4 : m = (term76 q2 n r2) => @lem169377 q1 r1 m q2 n r2 h1 h2 h3 h4) (fun h4 : term201 q1 q2 r1 r2 => @lem169371 m q2 r2 n h1)). Qed.
Lemma lem169379 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : term75 m q2 r2 n) (h2 : Peano.lt r1 n) (h3 : m = (term76 q1 n r1)) : term201 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169378 q2 r2 m q1 n r1 h1 h2 h3) (@lem169371 m q2 r2 n h1)). Qed.
Lemma lem169380 (m : nat) (q1 : nat) (r1 : nat) (n : nat) (h1 : term75 m q1 r1 n) : Peano.lt r1 n.
Proof. exact (proj2 (@lem168433 m q1 r1 n h1)). Qed.
Lemma lem169381 (m : nat) (q1 : nat) (r1 : nat) (n : nat) (h1 : term75 m q1 r1 n) : m = (term76 q1 n r1).
Proof. exact (proj1 (@lem168433 m q1 r1 n h1)). Qed.
Lemma lem169382 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : term75 m q2 r2 n) (h2 : Peano.lt r1 n) (h3 : m = (term76 q1 n r1)) : (Peano.lt r1 n) = (term201 q1 q2 r1 r2).
Proof. exact (prop_ext (fun h4 : Peano.lt r1 n => @lem169379 q2 r2 m q1 n r1 h1 h2 h3) (fun h4 : term201 q1 q2 r1 r2 => @lem168434 r1 n h2)). Qed.
Lemma lem169383 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : term75 m q2 r2 n) (h2 : Peano.lt r1 n) (h3 : m = (term76 q1 n r1)) : term201 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169382 q2 r2 m q1 n r1 h1 h2 h3) (@lem168434 r1 n h2)). Qed.
Lemma lem169384 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : term75 m q2 r2 n) (h2 : Peano.lt r1 n) (h3 : m = (term76 q1 n r1)) : (m = (term76 q1 n r1)) = (term201 q1 q2 r1 r2).
Proof. exact (prop_ext (fun h4 : m = (term76 q1 n r1) => @lem169383 q2 r2 m q1 n r1 h1 h2 h3) (fun h4 : term201 q1 q2 r1 r2 => @lem168435 m q1 n r1 h3)). Qed.
Lemma lem169385 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : term75 m q2 r2 n) (h2 : Peano.lt r1 n) (h3 : m = (term76 q1 n r1)) : term201 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169384 q2 r2 m q1 n r1 h1 h2 h3) (@lem168435 m q1 n r1 h3)). Qed.
Lemma lem169386 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : term75 m q1 r1 n) (h2 : term75 m q2 r2 n) (h3 : m = (term76 q1 n r1)) : (Peano.lt r1 n) = (term201 q1 q2 r1 r2).
Proof. exact (prop_ext (fun h4 : Peano.lt r1 n => @lem169385 q2 r2 m q1 n r1 h2 h4 h3) (fun h4 : term201 q1 q2 r1 r2 => @lem169380 m q1 r1 n h1)). Qed.
Lemma lem169387 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (n : nat) (r1 : nat) (h1 : term75 m q1 r1 n) (h2 : term75 m q2 r2 n) (h3 : m = (term76 q1 n r1)) : term201 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169386 q2 r2 m q1 n r1 h1 h2 h3) (@lem169380 m q1 r1 n h1)). Qed.
Lemma lem169388 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term75 m q1 r1 n) (h2 : term75 m q2 r2 n) : (m = (term76 q1 n r1)) = (term201 q1 q2 r1 r2).
Proof. exact (prop_ext (fun h3 : m = (term76 q1 n r1) => @lem169387 q2 r2 m q1 n r1 h1 h2 h3) (fun h3 : term201 q1 q2 r1 r2 => @lem169381 m q1 r1 n h1)). Qed.
Lemma lem169389 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term75 m q1 r1 n) (h2 : term75 m q2 r2 n) : term201 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169388 q1 r1 m q2 r2 n h1 h2) (@lem169381 m q1 r1 n h1)). Qed.
Lemma lem169390 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (r1 : nat) (n : nat) (h1 : term74 q1 r1 m q2 r2 n) (h2 : term75 m q1 r1 n) : (term75 m q2 r2 n) = (term201 q1 q2 r1 r2).
Proof. exact (prop_ext (fun h3 : term75 m q2 r2 n => @lem169389 q1 r1 m q2 r2 n h2 h3) (fun h3 : term201 q1 q2 r1 r2 => @lem169368 q1 r1 m q2 r2 n h1)). Qed.
Lemma lem169391 (q2 : nat) (r2 : nat) (m : nat) (q1 : nat) (r1 : nat) (n : nat) (h1 : term74 q1 r1 m q2 r2 n) (h2 : term75 m q1 r1 n) : term201 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169390 q2 r2 m q1 r1 n h1 h2) (@lem169368 q1 r1 m q2 r2 n h1)). Qed.
Lemma lem169392 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term74 q1 r1 m q2 r2 n) : (term75 m q1 r1 n) = (term201 q1 q2 r1 r2).
Proof. exact (prop_ext (fun h2 : term75 m q1 r1 n => @lem169391 q2 r2 m q1 r1 n h1 h2) (fun h2 : term201 q1 q2 r1 r2 => @lem169369 q1 r1 m q2 r2 n h1)). Qed.
Lemma lem169393 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term74 q1 r1 m q2 r2 n) : term201 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169392 q1 r1 m q2 r2 n h1) (@lem169369 q1 r1 m q2 r2 n h1)). Qed.
Lemma lem169394 (m : nat) (n : nat) (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) : term242 m n q1 q2 r1 r2.
Proof. exact (fun h0 : term74 q1 r1 m q2 r2 n => @lem169393 q1 r1 m q2 r2 n h0). Qed.
Lemma lem169399 (m : nat) (n : nat) (q1 : nat) (q2 : nat) (r1 : nat) : term243 m n q1 q2 r1.
Proof. exact (fun r2 : nat => @lem169394 m n q1 q2 r1 r2). Qed.
Lemma lem169404 (m : nat) (n : nat) (q1 : nat) (r1 : nat) : term244 m n q1 r1.
Proof. exact (fun q2 : nat => @lem169399 m n q1 q2 r1). Qed.
Lemma lem169409 (m : nat) (n : nat) (q1 : nat) : term245 m n q1.
Proof. exact (fun r1 : nat => @lem169404 m n q1 r1). Qed.
Lemma lem169414 (m : nat) (n : nat) : term246 m n.
Proof. exact (fun q1 : nat => @lem169409 m n q1). Qed.
Lemma lem169419 (m : nat) : term247 m.
Proof. exact (fun n : nat => @lem169414 m n). Qed.
Lemma lem169424 : term248.
Proof. exact (fun m : nat => @lem169419 m). Qed.
