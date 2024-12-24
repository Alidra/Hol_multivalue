Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL_EL_term_abbrevs.
Require Import ALL_MEM_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import MEM_EXISTS_EL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm21386_spec.
Lemma lem1162241 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1162242 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1162243 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1162242 t1) (@lem1162241 t1)). Qed.
Lemma lem1162244 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1162243 t1 t2). Qed.
Lemma lem1162245 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1162246 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1162245 t1 t2) (@lem1162244 t1 t2)). Qed.
Lemma lem1162247 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1162246 t1 t2 t3). Qed.
Lemma lem1162248 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1162249 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1162248 t1 t2 t3) (@lem1162247 t1 t2 t3)). Qed.
Lemma lem1162250 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1162249 t1 t2 t3)). Qed.
Lemma lem1162253 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term7 _26777 l P) = (@List.Forall _26777 P l)) : (term7 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (h1). Qed.
Lemma lem1162254 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term7 _26777 l P) = (@List.Forall _26777 P l)) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (SYM (@lem1162253 _26777 P l h1)). Qed.
Lemma lem1162255 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term7 _26777 l P)) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (h1). Qed.
Lemma lem1162256 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term7 _26777 l P)) : (term7 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (SYM (@lem1162255 _26777 l P h1)). Qed.
Lemma lem1162257 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : ((term7 _26777 l P) = (@List.Forall _26777 P l)) = ((@List.Forall _26777 P l) = (term7 _26777 l P)).
Proof. exact (prop_ext (fun h1 : (term7 _26777 l P) = (@List.Forall _26777 P l) => @lem1162254 _26777 P l h1) (fun h1 : (@List.Forall _26777 P l) = (term7 _26777 l P) => @lem1162256 _26777 l P h1)). Qed.
Lemma lem1162258 {_26777 : Type'} (P : _26777 -> Prop) : (term8 _26777 P) = (term9 _26777 P).
Proof. exact (fun_ext (fun l : list _26777 => @lem1162257 _26777 l P)). Qed.
Lemma lem1162259 {_26777 : Type'} : (@all (list _26777)) = (@all (list _26777)).
Proof. exact (eq_refl (@all (list _26777))). Qed.
Lemma lem1162260 {_26777 : Type'} (P : _26777 -> Prop) : (term10 _26777 P) = (term11 _26777 P).
Proof. exact (MK_COMB (@lem1162259 _26777) (@lem1162258 _26777 P)). Qed.
Lemma lem1162261 {_26777 : Type'} : (term12 _26777) = (term13 _26777).
Proof. exact (fun_ext (fun P : _26777 -> Prop => @lem1162260 _26777 P)). Qed.
Lemma lem1162262 {_26777 : Type'} : (@all (_26777 -> Prop)) = (@all (_26777 -> Prop)).
Proof. exact (eq_refl (@all (_26777 -> Prop))). Qed.
Lemma lem1162263 {_26777 : Type'} : (term14 _26777) = (term15 _26777).
Proof. exact (MK_COMB (@lem1162262 _26777) (@lem1162261 _26777)). Qed.
Lemma lem1162264 {_26777 : Type'} : term15 _26777.
Proof. exact (EQ_MP (@lem1162263 _26777) (@lem1138070 _26777)). Qed.
Lemma lem1162265 {_27312 : Type'} (l : list _27312) : term16 _27312 l.
Proof. exact (@lem1162240 _27312 l). Qed.
Lemma lem1162266 {_27312 : Type'} (l : list _27312) : (term16 _27312 l) = (term17 _27312 l).
Proof. exact (eq_refl (term16 _27312 l)). Qed.
Lemma lem1162267 {_27312 : Type'} (l : list _27312) : term17 _27312 l.
Proof. exact (EQ_MP (@lem1162266 _27312 l) (@lem1162265 _27312 l)). Qed.
Lemma lem1162268 {_27312 : Type'} (l : list _27312) (x : _27312) : term18 _27312 l x.
Proof. exact (@lem1162267 _27312 l x). Qed.
Lemma lem1162269 {_27312 : Type'} (x : _27312) (l : list _27312) : (term18 _27312 l x) = ((@List.In _27312 x l) = (term19 _27312 x l)).
Proof. exact (eq_refl (term18 _27312 l x)). Qed.
Lemma lem1162271 {_26777 : Type'} (P : _26777 -> Prop) : term20 _26777 P.
Proof. exact (@lem1162264 _26777 P). Qed.
Lemma lem1162272 {_26777 : Type'} (P : _26777 -> Prop) : (term20 _26777 P) = (term11 _26777 P).
Proof. exact (eq_refl (term20 _26777 P)). Qed.
Lemma lem1162273 {_26777 : Type'} (P : _26777 -> Prop) : term11 _26777 P.
Proof. exact (EQ_MP (@lem1162272 _26777 P) (@lem1162271 _26777 P)). Qed.
Lemma lem1162274 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) : term21 _26777 P l.
Proof. exact (@lem1162273 _26777 P l). Qed.
Lemma lem1162275 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (term21 _26777 P l) = ((@List.Forall _26777 P l) = (term7 _26777 l P)).
Proof. exact (eq_refl (term21 _26777 P l)). Qed.
Lemma lem1162294 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (EQ_MP (@lem1162275 _26777 l P) (@lem1162274 _26777 P l)). Qed.
Lemma lem1162295 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (@List.Forall _27338 P l) = (term7 _27338 l P).
Proof. exact (@lem1162294 _27338 l P). Qed.
Lemma lem1162303 {_27312 : Type'} (x : _27312) (l : list _27312) : (@List.In _27312 x l) = (term19 _27312 x l).
Proof. exact (EQ_MP (@lem1162269 _27312 x l) (@lem1162268 _27312 l x)). Qed.
Lemma lem1162304 {_27338 : Type'} (x : _27338) (l : list _27338) : (@List.In _27338 x l) = (term19 _27338 x l).
Proof. exact (@lem1162303 _27338 x l). Qed.
Lemma lem1162313 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1162314 {_27338 : Type'} (x : _27338) (l : list _27338) : (term22 _27338 x l) = (term23 _27338 x l).
Proof. exact (MK_COMB (@lem1162313) (@lem1162304 _27338 x l)). Qed.
Lemma lem1162315 {_27338 : Type'} (P : _27338 -> Prop) (x : _27338) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1162316 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term24 _27338 l P x) = (term25 _27338 l P x).
Proof. exact (MK_COMB (@lem1162314 _27338 x l) (@lem1162315 _27338 P x)). Qed.
Lemma lem1162319 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term26 _27338 l P) = (term27 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1162316 _27338 l P x)). Qed.
Lemma lem1162320 {_27338 : Type'} : (@all _27338) = (@all _27338).
Proof. exact (eq_refl (@all _27338)). Qed.
Lemma lem1162321 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term7 _27338 l P) = (term28 _27338 l P).
Proof. exact (MK_COMB (@lem1162320 _27338) (@lem1162319 _27338 l P)). Qed.
Lemma lem1162326 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (@List.Forall _27338 P l) = (term28 _27338 l P).
Proof. exact (TRANS (@lem1162295 _27338 l P) (@lem1162321 _27338 l P)). Qed.
Lemma lem1162327 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term29 _27338 P l) = (term29 _27338 P l).
Proof. exact (eq_refl (term29 _27338 P l)). Qed.
Lemma lem1162328 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : ((term30 _27338 P l) = (@List.Forall _27338 P l)) = ((term30 _27338 P l) = (term28 _27338 l P)).
Proof. exact (MK_COMB (@lem1162327 _27338 P l) (@lem1162326 _27338 l P)). Qed.
Lemma lem1162331 {_27338 : Type'} (P : _27338 -> Prop) : (term31 _27338 P) = (term32 _27338 P).
Proof. exact (fun_ext (fun l : list _27338 => @lem1162328 _27338 l P)). Qed.
Lemma lem1162332 {_27338 : Type'} : (@all (list _27338)) = (@all (list _27338)).
Proof. exact (eq_refl (@all (list _27338))). Qed.
Lemma lem1162333 {_27338 : Type'} (P : _27338 -> Prop) : (term33 _27338 P) = (term34 _27338 P).
Proof. exact (MK_COMB (@lem1162332 _27338) (@lem1162331 _27338 P)). Qed.
Lemma lem1162338 {_27338 : Type'} : (term35 _27338) = (term36 _27338).
Proof. exact (fun_ext (fun P : _27338 -> Prop => @lem1162333 _27338 P)). Qed.
Lemma lem1162339 {_27338 : Type'} : (@all (_27338 -> Prop)) = (@all (_27338 -> Prop)).
Proof. exact (eq_refl (@all (_27338 -> Prop))). Qed.
Lemma lem1162340 {_27338 : Type'} : (term37 _27338) = (term38 _27338).
Proof. exact (MK_COMB (@lem1162339 _27338) (@lem1162338 _27338)). Qed.
Lemma lem1162345 {_27338 : Type'} : (term38 _27338) = (term37 _27338).
Proof. exact (SYM (@lem1162340 _27338)). Qed.
Lemma lem1162347 (p : Prop) : p = (term39 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1162348 {_27338 : Type'} : (term38 _27338) = (term40 _27338).
Proof. exact (@lem1162347 (term38 _27338)). Qed.
Lemma lem1162349 {_27338 : Type'} : (term40 _27338) = (term38 _27338).
Proof. exact (SYM (@lem1162348 _27338)). Qed.
Lemma lem1162350 {_27338 : Type'} (h1 : term41 _27338) : term41 _27338.
Proof. exact (h1). Qed.
Lemma lem1162353 {_27338 : Type'} (h1 : term40 _27338) : term40 _27338.
Proof. exact (h1). Qed.
Lemma lem1162354 {_27338 : Type'} : term42 _27338.
Proof. exact (fun h0 : term40 _27338 => @lem1162353 _27338 h0). Qed.
Lemma lem1162355 {_27338 : Type'} (h1 : term42 _27338) : term42 _27338.
Proof. exact (h1). Qed.
Lemma lem1162356 {_27338 : Type'} (h1 : term40 _27338) : term40 _27338.
Proof. exact (h1). Qed.
Lemma lem1162357 {_27338 : Type'} (h1 : term40 _27338) (h2 : term42 _27338) : term40 _27338.
Proof. exact (@lem1162355 _27338 h2 (@lem1162356 _27338 h1)). Qed.
Lemma lem1162358 {_27338 : Type'} (h1 : term40 _27338) : term43 _27338.
Proof. exact (fun h0 : term42 _27338 => @lem1162357 _27338 h1 h0). Qed.
Lemma lem1162359 {_27338 : Type'} (h1 : term42 _27338) : term42 _27338.
Proof. exact (h1). Qed.
Lemma lem1162360 {_27338 : Type'} (h1 : term40 _27338) (h2 : term42 _27338) : term40 _27338.
Proof. exact (@lem1162358 _27338 h1 (@lem1162359 _27338 h2)). Qed.
Lemma lem1162361 {_27338 : Type'} (h1 : term42 _27338) : term42 _27338.
Proof. exact (fun h0 : term40 _27338 => @lem1162360 _27338 h0 h1). Qed.
Lemma lem1162362 {_27338 : Type'} : term44 _27338.
Proof. exact (fun h0 : term42 _27338 => @lem1162361 _27338 h0). Qed.
Lemma lem1162365 {_27338 : Type'} : term42 _27338.
Proof. exact (@lem1162362 _27338 (@lem1162354 _27338)). Qed.
Lemma lem1162366 {_27338 : Type'} : term42 _27338.
Proof. exact (@lem1162365 _27338). Qed.
Lemma lem1162368 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1162369 {_27338 : Type'} : (term40 _27338) = (term45 _27338).
Proof. exact (@lem1162368 (term41 _27338)). Qed.
Lemma lem1162371 (t : Prop) : (term46 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1162372 {_27338 : Type'} : (term45 _27338) = (term38 _27338).
Proof. exact (@lem1162371 (term38 _27338)). Qed.
Lemma lem1162447 {_27338 : Type'} : (term40 _27338) = (term38 _27338).
Proof. exact (TRANS (@lem1162369 _27338) (@lem1162372 _27338)). Qed.
Lemma lem1162448 {_27338 : Type'} (P : _27338 -> Prop) (x : _27338) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1162453 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term47 _27338 x i l) = (term47 _27338 x i l).
Proof. exact (eq_refl (term47 _27338 x i l)). Qed.
Lemma lem1162454 {_27338 : Type'} (x : _27338) (l : list _27338) : (term48 _27338 x l) = (term48 _27338 x l).
Proof. exact (fun_ext (fun i : nat => @lem1162453 _27338 x i l)). Qed.
Lemma lem1162455 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162456 {_27338 : Type'} (x : _27338) (l : list _27338) : (term19 _27338 x l) = (term19 _27338 x l).
Proof. exact (MK_COMB (@lem1162455) (@lem1162454 _27338 x l)). Qed.
Lemma lem1162457 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1162458 {_27338 : Type'} (x : _27338) (l : list _27338) : (term23 _27338 x l) = (term23 _27338 x l).
Proof. exact (MK_COMB (@lem1162457) (@lem1162456 _27338 x l)). Qed.
Lemma lem1162459 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term25 _27338 l P x) = (term25 _27338 l P x).
Proof. exact (MK_COMB (@lem1162458 _27338 x l) (@lem1162448 _27338 P x)). Qed.
Lemma lem1162460 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term27 _27338 l P) = (term27 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1162459 _27338 l P x)). Qed.
Lemma lem1162461 {_27338 : Type'} : (@all _27338) = (@all _27338).
Proof. exact (eq_refl (@all _27338)). Qed.
Lemma lem1162462 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term28 _27338 l P) = (term28 _27338 l P).
Proof. exact (MK_COMB (@lem1162461 _27338) (@lem1162460 _27338 l P)). Qed.
Lemma lem1162467 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term49 _27338 P i l) = (term49 _27338 P i l).
Proof. exact (eq_refl (term49 _27338 P i l)). Qed.
Lemma lem1162468 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term50 _27338 P l) = (term50 _27338 P l).
Proof. exact (fun_ext (fun i : nat => @lem1162467 _27338 P i l)). Qed.
Lemma lem1162469 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1162470 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term30 _27338 P l) = (term30 _27338 P l).
Proof. exact (MK_COMB (@lem1162469) (@lem1162468 _27338 P l)). Qed.
Lemma lem1162471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1162472 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term29 _27338 P l) = (term29 _27338 P l).
Proof. exact (MK_COMB (@lem1162471) (@lem1162470 _27338 P l)). Qed.
Lemma lem1162473 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : ((term30 _27338 P l) = (term28 _27338 l P)) = ((term30 _27338 P l) = (term28 _27338 l P)).
Proof. exact (MK_COMB (@lem1162472 _27338 P l) (@lem1162462 _27338 l P)). Qed.
Lemma lem1162474 {_27338 : Type'} (P : _27338 -> Prop) : (term32 _27338 P) = (term32 _27338 P).
Proof. exact (fun_ext (fun l : list _27338 => @lem1162473 _27338 l P)). Qed.
Lemma lem1162475 {_27338 : Type'} : (@all (list _27338)) = (@all (list _27338)).
Proof. exact (eq_refl (@all (list _27338))). Qed.
Lemma lem1162476 {_27338 : Type'} (P : _27338 -> Prop) : (term34 _27338 P) = (term34 _27338 P).
Proof. exact (MK_COMB (@lem1162475 _27338) (@lem1162474 _27338 P)). Qed.
Lemma lem1162477 {_27338 : Type'} : (term36 _27338) = (term36 _27338).
Proof. exact (fun_ext (fun P : _27338 -> Prop => @lem1162476 _27338 P)). Qed.
Lemma lem1162478 {_27338 : Type'} : (@all (_27338 -> Prop)) = (@all (_27338 -> Prop)).
Proof. exact (eq_refl (@all (_27338 -> Prop))). Qed.
Lemma lem1162479 {_27338 : Type'} : (term38 _27338) = (term38 _27338).
Proof. exact (MK_COMB (@lem1162478 _27338) (@lem1162477 _27338)). Qed.
Lemma lem1162518 {_27338 : Type'} : (term40 _27338) = (term38 _27338).
Proof. exact (TRANS (@lem1162447 _27338) (@lem1162479 _27338)). Qed.
Lemma lem1162519 {_27338 : Type'} : (term38 _27338) = (term40 _27338).
Proof. exact (SYM (@lem1162518 _27338)). Qed.
Lemma lem1162521 (p : Prop) : p = (term39 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1162522 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : ((term30 _27338 P l) = (term28 _27338 l P)) = (term51 _27338 l P).
Proof. exact (@lem1162521 ((term30 _27338 P l) = (term28 _27338 l P))). Qed.
Lemma lem1162523 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term51 _27338 l P) = ((term30 _27338 P l) = (term28 _27338 l P)).
Proof. exact (SYM (@lem1162522 _27338 l P)). Qed.
Lemma lem1162524 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (h1 : term52 _27338 l P) : term52 _27338 l P.
Proof. exact (h1). Qed.
Lemma lem1162533 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term53 _27338 P i l) = (term54 _27338 P i l).
Proof. exact (@lem17362 (term55 _27338 i l) (term56 _27338 P i l)). Qed.
Lemma lem1162538 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term49 _27338 P i l) = (term57 _27338 P i l).
Proof. exact (@lem17265 (term55 _27338 i l) (term56 _27338 P i l)). Qed.
Lemma lem1162539 (P : nat -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1162540 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term60 _27338 P l) = (term61 _27338 P l).
Proof. exact (@lem1162539 (term50 _27338 P l)). Qed.
Lemma lem1162541 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term62 _27338 P l i) = (term49 _27338 P i l).
Proof. exact (eq_refl (term62 _27338 P l i)). Qed.
Lemma lem1162542 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1162543 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term63 _27338 P l i) = (term53 _27338 P i l).
Proof. exact (MK_COMB (@lem1162542) (@lem1162541 _27338 P i l)). Qed.
Lemma lem1162544 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term63 _27338 P l i) = (term54 _27338 P i l).
Proof. exact (TRANS (@lem1162543 _27338 P i l) (@lem1162533 _27338 P i l)). Qed.
Lemma lem1162545 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term64 _27338 P l) = (term65 _27338 P l).
Proof. exact (fun_ext (fun i : nat => @lem1162544 _27338 P i l)). Qed.
Lemma lem1162546 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162547 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term61 _27338 P l) = (term66 _27338 P l).
Proof. exact (MK_COMB (@lem1162546) (@lem1162545 _27338 P l)). Qed.
Lemma lem1162548 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term60 _27338 P l) = (term66 _27338 P l).
Proof. exact (TRANS (@lem1162540 _27338 P l) (@lem1162547 _27338 P l)). Qed.
Lemma lem1162549 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term50 _27338 P l) = (term67 _27338 P l).
Proof. exact (fun_ext (fun i : nat => @lem1162538 _27338 P i l)). Qed.
Lemma lem1162550 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1162551 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term30 _27338 P l) = (term68 _27338 P l).
Proof. exact (MK_COMB (@lem1162550) (@lem1162549 _27338 P l)). Qed.
Lemma lem1162560 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term69 _27338 x i l) = (term70 _27338 x i l).
Proof. exact (@lem17045 (term55 _27338 i l) (x = (@EL _27338 i l))). Qed.
Lemma lem1162563 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term47 _27338 x i l) = (term47 _27338 x i l).
Proof. exact (eq_refl (term47 _27338 x i l)). Qed.
Lemma lem1162564 (P : nat -> Prop) : (term71 P) = (term72 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1162565 {_27338 : Type'} (x : _27338) (l : list _27338) : (term73 _27338 x l) = (term74 _27338 x l).
Proof. exact (@lem1162564 (term48 _27338 x l)). Qed.
Lemma lem1162566 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term75 _27338 x l i) = (term47 _27338 x i l).
Proof. exact (eq_refl (term75 _27338 x l i)). Qed.
Lemma lem1162567 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1162568 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term76 _27338 x l i) = (term69 _27338 x i l).
Proof. exact (MK_COMB (@lem1162567) (@lem1162566 _27338 x i l)). Qed.
Lemma lem1162569 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term76 _27338 x l i) = (term70 _27338 x i l).
Proof. exact (TRANS (@lem1162568 _27338 x i l) (@lem1162560 _27338 x i l)). Qed.
Lemma lem1162570 {_27338 : Type'} (x : _27338) (l : list _27338) : (term77 _27338 x l) = (term78 _27338 x l).
Proof. exact (fun_ext (fun i : nat => @lem1162569 _27338 x i l)). Qed.
Lemma lem1162571 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1162572 {_27338 : Type'} (x : _27338) (l : list _27338) : (term74 _27338 x l) = (term79 _27338 x l).
Proof. exact (MK_COMB (@lem1162571) (@lem1162570 _27338 x l)). Qed.
Lemma lem1162573 {_27338 : Type'} (x : _27338) (l : list _27338) : (term73 _27338 x l) = (term79 _27338 x l).
Proof. exact (TRANS (@lem1162565 _27338 x l) (@lem1162572 _27338 x l)). Qed.
Lemma lem1162574 {_27338 : Type'} (x : _27338) (l : list _27338) : (term48 _27338 x l) = (term48 _27338 x l).
Proof. exact (fun_ext (fun i : nat => @lem1162563 _27338 x i l)). Qed.
Lemma lem1162575 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162576 {_27338 : Type'} (x : _27338) (l : list _27338) : (term19 _27338 x l) = (term19 _27338 x l).
Proof. exact (MK_COMB (@lem1162575) (@lem1162574 _27338 x l)). Qed.
Lemma lem1162577 {_27338 : Type'} (P : _27338 -> Prop) (x : _27338) : (term80 _27338 P x) = (term80 _27338 P x).
Proof. exact (eq_refl (term80 _27338 P x)). Qed.
Lemma lem1162578 {_27338 : Type'} (P : _27338 -> Prop) (x : _27338) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1162579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1162580 {_27338 : Type'} (x : _27338) (l : list _27338) : (term81 _27338 x l) = (term81 _27338 x l).
Proof. exact (MK_COMB (@lem1162579) (@lem1162576 _27338 x l)). Qed.
Lemma lem1162581 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term82 _27338 l P x) = (term82 _27338 l P x).
Proof. exact (MK_COMB (@lem1162580 _27338 x l) (@lem1162577 _27338 P x)). Qed.
Lemma lem1162582 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term83 _27338 l P x) = (term82 _27338 l P x).
Proof. exact (@lem17362 (term19 _27338 x l) (P x)). Qed.
Lemma lem1162583 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term83 _27338 l P x) = (term82 _27338 l P x).
Proof. exact (TRANS (@lem1162582 _27338 l P x) (@lem1162581 _27338 l P x)). Qed.
Lemma lem1162584 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1162585 {_27338 : Type'} (x : _27338) (l : list _27338) : (term84 _27338 x l) = (term85 _27338 x l).
Proof. exact (MK_COMB (@lem1162584) (@lem1162573 _27338 x l)). Qed.
Lemma lem1162586 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term86 _27338 l P x) = (term87 _27338 l P x).
Proof. exact (MK_COMB (@lem1162585 _27338 x l) (@lem1162578 _27338 P x)). Qed.
Lemma lem1162587 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term25 _27338 l P x) = (term86 _27338 l P x).
Proof. exact (@lem17265 (term19 _27338 x l) (P x)). Qed.
Lemma lem1162588 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term25 _27338 l P x) = (term87 _27338 l P x).
Proof. exact (TRANS (@lem1162587 _27338 l P x) (@lem1162586 _27338 l P x)). Qed.
Lemma lem1162589 {_27338 : Type'} (P : _27338 -> Prop) : (term88 _27338 P) = (term89 _27338 P).
Proof. exact (@lem18392 _27338 P). Qed.
Lemma lem1162590 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term90 _27338 l P) = (term91 _27338 l P).
Proof. exact (@lem1162589 _27338 (term27 _27338 l P)). Qed.
Lemma lem1162591 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term92 _27338 l P x) = (term25 _27338 l P x).
Proof. exact (eq_refl (term92 _27338 l P x)). Qed.
Lemma lem1162592 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1162593 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term93 _27338 l P x) = (term83 _27338 l P x).
Proof. exact (MK_COMB (@lem1162592) (@lem1162591 _27338 l P x)). Qed.
Lemma lem1162594 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term93 _27338 l P x) = (term82 _27338 l P x).
Proof. exact (TRANS (@lem1162593 _27338 l P x) (@lem1162583 _27338 l P x)). Qed.
Lemma lem1162595 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term94 _27338 l P) = (term95 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1162594 _27338 l P x)). Qed.
Lemma lem1162596 {_27338 : Type'} : (@ex _27338) = (@ex _27338).
Proof. exact (eq_refl (@ex _27338)). Qed.
Lemma lem1162597 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term91 _27338 l P) = (term96 _27338 l P).
Proof. exact (MK_COMB (@lem1162596 _27338) (@lem1162595 _27338 l P)). Qed.
Lemma lem1162598 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term90 _27338 l P) = (term96 _27338 l P).
Proof. exact (TRANS (@lem1162590 _27338 l P) (@lem1162597 _27338 l P)). Qed.
Lemma lem1162599 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term27 _27338 l P) = (term97 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1162588 _27338 l P x)). Qed.
Lemma lem1162600 {_27338 : Type'} : (@all _27338) = (@all _27338).
Proof. exact (eq_refl (@all _27338)). Qed.
Lemma lem1162601 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term28 _27338 l P) = (term98 _27338 l P).
Proof. exact (MK_COMB (@lem1162600 _27338) (@lem1162599 _27338 l P)). Qed.
Lemma lem1162602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1162603 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term99 _27338 P l) = (term100 _27338 P l).
Proof. exact (MK_COMB (@lem1162602) (@lem1162548 _27338 P l)). Qed.
Lemma lem1162604 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term101 _27338 l P) = (term102 _27338 l P).
Proof. exact (MK_COMB (@lem1162603 _27338 P l) (@lem1162601 _27338 l P)). Qed.
Lemma lem1162605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1162606 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term103 _27338 P l) = (term104 _27338 P l).
Proof. exact (MK_COMB (@lem1162605) (@lem1162551 _27338 P l)). Qed.
Lemma lem1162607 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term105 _27338 l P) = (term106 _27338 l P).
Proof. exact (MK_COMB (@lem1162606 _27338 P l) (@lem1162598 _27338 l P)). Qed.
Lemma lem1162608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1162609 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term107 _27338 l P) = (term108 _27338 l P).
Proof. exact (MK_COMB (@lem1162608) (@lem1162607 _27338 l P)). Qed.
Lemma lem1162610 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term109 _27338 l P) = (term110 _27338 l P).
Proof. exact (MK_COMB (@lem1162609 _27338 l P) (@lem1162604 _27338 l P)). Qed.
Lemma lem1162611 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term52 _27338 l P) = (term109 _27338 l P).
Proof. exact (@lem17646 (term30 _27338 P l) (term28 _27338 l P)). Qed.
Lemma lem1162612 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term52 _27338 l P) = (term110 _27338 l P).
Proof. exact (TRANS (@lem1162611 _27338 l P) (@lem1162610 _27338 l P)). Qed.
Lemma lem1162887 {A : Type'} (P : A -> Prop) (Q : Prop) : (term111 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1162888 (P : nat -> Prop) (Q : Prop) : (term113 P Q) = (term114 P Q).
Proof. exact (@lem1162887 nat P Q). Qed.
Lemma lem1162889 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term115 _27338 l P x) = (term116 _27338 l P x).
Proof. exact (@lem1162888 (term48 _27338 x l) (term80 _27338 P x)). Qed.
Lemma lem1162890 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term75 _27338 x l i) = (term47 _27338 x i l).
Proof. exact (eq_refl (term75 _27338 x l i)). Qed.
Lemma lem1162891 {_27338 : Type'} (x : _27338) (l : list _27338) : (term117 _27338 x l) = (term48 _27338 x l).
Proof. exact (fun_ext (fun i : nat => @lem1162890 _27338 x i l)). Qed.
Lemma lem1162892 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162893 {_27338 : Type'} (x : _27338) (l : list _27338) : (term118 _27338 x l) = (term19 _27338 x l).
Proof. exact (MK_COMB (@lem1162892) (@lem1162891 _27338 x l)). Qed.
Lemma lem1162894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1162895 {_27338 : Type'} (x : _27338) (l : list _27338) : (term119 _27338 x l) = (term81 _27338 x l).
Proof. exact (MK_COMB (@lem1162894) (@lem1162893 _27338 x l)). Qed.
Lemma lem1162896 {_27338 : Type'} (P : _27338 -> Prop) (x : _27338) : (term80 _27338 P x) = (term80 _27338 P x).
Proof. exact (eq_refl (term80 _27338 P x)). Qed.
Lemma lem1162897 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term115 _27338 l P x) = (term82 _27338 l P x).
Proof. exact (MK_COMB (@lem1162895 _27338 x l) (@lem1162896 _27338 P x)). Qed.
Lemma lem1162898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1162899 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term120 _27338 l P x) = (term121 _27338 l P x).
Proof. exact (MK_COMB (@lem1162898) (@lem1162897 _27338 l P x)). Qed.
Lemma lem1162900 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term75 _27338 x l i) = (term47 _27338 x i l).
Proof. exact (eq_refl (term75 _27338 x l i)). Qed.
Lemma lem1162901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1162902 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term122 _27338 x l i) = (term123 _27338 x i l).
Proof. exact (MK_COMB (@lem1162901) (@lem1162900 _27338 x i l)). Qed.
Lemma lem1162903 {_27338 : Type'} (P : _27338 -> Prop) (x : _27338) : (term80 _27338 P x) = (term80 _27338 P x).
Proof. exact (eq_refl (term80 _27338 P x)). Qed.
Lemma lem1162904 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term124 _27338 l i P x) = (term125 _27338 i l P x).
Proof. exact (MK_COMB (@lem1162902 _27338 x i l) (@lem1162903 _27338 P x)). Qed.
Lemma lem1162905 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term126 _27338 l P x) = (term127 _27338 l P x).
Proof. exact (fun_ext (fun i : nat => @lem1162904 _27338 i l P x)). Qed.
Lemma lem1162906 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162907 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term116 _27338 l P x) = (term128 _27338 l P x).
Proof. exact (MK_COMB (@lem1162906) (@lem1162905 _27338 l P x)). Qed.
Lemma lem1162908 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : ((term115 _27338 l P x) = (term116 _27338 l P x)) = ((term82 _27338 l P x) = (term128 _27338 l P x)).
Proof. exact (MK_COMB (@lem1162899 _27338 l P x) (@lem1162907 _27338 l P x)). Qed.
Lemma lem1162909 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term82 _27338 l P x) = (term128 _27338 l P x).
Proof. exact (EQ_MP (@lem1162908 _27338 l P x) (@lem1162889 _27338 l P x)). Qed.
Lemma lem1162910 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term95 _27338 l P) = (term129 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1162909 _27338 l P x)). Qed.
Lemma lem1162911 {_27338 : Type'} : (@ex _27338) = (@ex _27338).
Proof. exact (eq_refl (@ex _27338)). Qed.
Lemma lem1162912 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term96 _27338 l P) = (term130 _27338 l P).
Proof. exact (MK_COMB (@lem1162911 _27338) (@lem1162910 _27338 l P)). Qed.
Lemma lem1162913 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term104 _27338 P l) = (term104 _27338 P l).
Proof. exact (eq_refl (term104 _27338 P l)). Qed.
Lemma lem1162914 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term106 _27338 l P) = (term131 _27338 l P).
Proof. exact (MK_COMB (@lem1162913 _27338 P l) (@lem1162912 _27338 l P)). Qed.
Lemma lem1162916 {A : Type'} (P : Prop) (Q : A -> Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1162917 {_27338 : Type'} (P : Prop) (Q : _27338 -> Prop) : (term132 _27338 P Q) = (term133 _27338 P Q).
Proof. exact (@lem1162916 _27338 P Q). Qed.
Lemma lem1162918 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term134 _27338 l P) = (term135 _27338 l P).
Proof. exact (@lem1162917 _27338 (term68 _27338 P l) (term129 _27338 l P)). Qed.
Lemma lem1162919 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term136 _27338 l P x) = (term128 _27338 l P x).
Proof. exact (eq_refl (term136 _27338 l P x)). Qed.
Lemma lem1162920 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term137 _27338 l P) = (term129 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1162919 _27338 l P x)). Qed.
Lemma lem1162921 {_27338 : Type'} : (@ex _27338) = (@ex _27338).
Proof. exact (eq_refl (@ex _27338)). Qed.
Lemma lem1162922 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term138 _27338 l P) = (term130 _27338 l P).
Proof. exact (MK_COMB (@lem1162921 _27338) (@lem1162920 _27338 l P)). Qed.
Lemma lem1162923 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term104 _27338 P l) = (term104 _27338 P l).
Proof. exact (eq_refl (term104 _27338 P l)). Qed.
Lemma lem1162924 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term134 _27338 l P) = (term131 _27338 l P).
Proof. exact (MK_COMB (@lem1162923 _27338 P l) (@lem1162922 _27338 l P)). Qed.
Lemma lem1162925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1162926 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term139 _27338 l P) = (term140 _27338 l P).
Proof. exact (MK_COMB (@lem1162925) (@lem1162924 _27338 l P)). Qed.
Lemma lem1162927 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term136 _27338 l P x) = (term128 _27338 l P x).
Proof. exact (eq_refl (term136 _27338 l P x)). Qed.
Lemma lem1162928 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term104 _27338 P l) = (term104 _27338 P l).
Proof. exact (eq_refl (term104 _27338 P l)). Qed.
Lemma lem1162929 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term141 _27338 l P x) = (term142 _27338 l P x).
Proof. exact (MK_COMB (@lem1162928 _27338 P l) (@lem1162927 _27338 l P x)). Qed.
Lemma lem1162930 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term143 _27338 l P) = (term144 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1162929 _27338 l P x)). Qed.
Lemma lem1162931 {_27338 : Type'} : (@ex _27338) = (@ex _27338).
Proof. exact (eq_refl (@ex _27338)). Qed.
Lemma lem1162932 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term135 _27338 l P) = (term145 _27338 l P).
Proof. exact (MK_COMB (@lem1162931 _27338) (@lem1162930 _27338 l P)). Qed.
Lemma lem1162933 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : ((term134 _27338 l P) = (term135 _27338 l P)) = ((term131 _27338 l P) = (term145 _27338 l P)).
Proof. exact (MK_COMB (@lem1162926 _27338 l P) (@lem1162932 _27338 l P)). Qed.
Lemma lem1162934 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term131 _27338 l P) = (term145 _27338 l P).
Proof. exact (EQ_MP (@lem1162933 _27338 l P) (@lem1162918 _27338 l P)). Qed.
Lemma lem1162936 {A : Type'} (P : Prop) (Q : A -> Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1162937 (P : Prop) (Q : nat -> Prop) : (term146 P Q) = (term147 P Q).
Proof. exact (@lem1162936 nat P Q). Qed.
Lemma lem1162938 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term148 _27338 l P x) = (term149 _27338 l P x).
Proof. exact (@lem1162937 (term68 _27338 P l) (term127 _27338 l P x)). Qed.
Lemma lem1162939 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term150 _27338 l P x i) = (term125 _27338 i l P x).
Proof. exact (eq_refl (term150 _27338 l P x i)). Qed.
Lemma lem1162940 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term151 _27338 l P x) = (term127 _27338 l P x).
Proof. exact (fun_ext (fun i : nat => @lem1162939 _27338 i l P x)). Qed.
Lemma lem1162941 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162942 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term152 _27338 l P x) = (term128 _27338 l P x).
Proof. exact (MK_COMB (@lem1162941) (@lem1162940 _27338 l P x)). Qed.
Lemma lem1162943 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term104 _27338 P l) = (term104 _27338 P l).
Proof. exact (eq_refl (term104 _27338 P l)). Qed.
Lemma lem1162944 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term148 _27338 l P x) = (term142 _27338 l P x).
Proof. exact (MK_COMB (@lem1162943 _27338 P l) (@lem1162942 _27338 l P x)). Qed.
Lemma lem1162945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1162946 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term153 _27338 l P x) = (term154 _27338 l P x).
Proof. exact (MK_COMB (@lem1162945) (@lem1162944 _27338 l P x)). Qed.
Lemma lem1162947 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term150 _27338 l P x i) = (term125 _27338 i l P x).
Proof. exact (eq_refl (term150 _27338 l P x i)). Qed.
Lemma lem1162948 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term104 _27338 P l) = (term104 _27338 P l).
Proof. exact (eq_refl (term104 _27338 P l)). Qed.
Lemma lem1162949 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term155 _27338 l P x i) = (term156 _27338 i l P x).
Proof. exact (MK_COMB (@lem1162948 _27338 P l) (@lem1162947 _27338 i l P x)). Qed.
Lemma lem1162950 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term157 _27338 l P x) = (term158 _27338 l P x).
Proof. exact (fun_ext (fun i : nat => @lem1162949 _27338 i l P x)). Qed.
Lemma lem1162951 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162952 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term149 _27338 l P x) = (term159 _27338 l P x).
Proof. exact (MK_COMB (@lem1162951) (@lem1162950 _27338 l P x)). Qed.
Lemma lem1162953 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : ((term148 _27338 l P x) = (term149 _27338 l P x)) = ((term142 _27338 l P x) = (term159 _27338 l P x)).
Proof. exact (MK_COMB (@lem1162946 _27338 l P x) (@lem1162952 _27338 l P x)). Qed.
Lemma lem1162954 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term142 _27338 l P x) = (term159 _27338 l P x).
Proof. exact (EQ_MP (@lem1162953 _27338 l P x) (@lem1162938 _27338 l P x)). Qed.
Lemma lem1162955 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term144 _27338 l P) = (term160 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1162954 _27338 l P x)). Qed.
Lemma lem1162956 {_27338 : Type'} : (@ex _27338) = (@ex _27338).
Proof. exact (eq_refl (@ex _27338)). Qed.
Lemma lem1162957 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term145 _27338 l P) = (term161 _27338 l P).
Proof. exact (MK_COMB (@lem1162956 _27338) (@lem1162955 _27338 l P)). Qed.
Lemma lem1162958 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term131 _27338 l P) = (term161 _27338 l P).
Proof. exact (TRANS (@lem1162934 _27338 l P) (@lem1162957 _27338 l P)). Qed.
Lemma lem1162959 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term106 _27338 l P) = (term161 _27338 l P).
Proof. exact (TRANS (@lem1162914 _27338 l P) (@lem1162958 _27338 l P)). Qed.
Lemma lem1162960 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1162961 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term108 _27338 l P) = (term162 _27338 l P).
Proof. exact (MK_COMB (@lem1162960) (@lem1162959 _27338 l P)). Qed.
Lemma lem1162963 {A : Type'} (P : A -> Prop) (Q : Prop) : (term111 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1162964 (P : nat -> Prop) (Q : Prop) : (term113 P Q) = (term114 P Q).
Proof. exact (@lem1162963 nat P Q). Qed.
Lemma lem1162965 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term163 _27338 l P) = (term164 _27338 l P).
Proof. exact (@lem1162964 (term65 _27338 P l) (term98 _27338 l P)). Qed.
Lemma lem1162966 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term165 _27338 P l i) = (term54 _27338 P i l).
Proof. exact (eq_refl (term165 _27338 P l i)). Qed.
Lemma lem1162967 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term166 _27338 P l) = (term65 _27338 P l).
Proof. exact (fun_ext (fun i : nat => @lem1162966 _27338 P i l)). Qed.
Lemma lem1162968 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162969 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term167 _27338 P l) = (term66 _27338 P l).
Proof. exact (MK_COMB (@lem1162968) (@lem1162967 _27338 P l)). Qed.
Lemma lem1162970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1162971 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term168 _27338 P l) = (term100 _27338 P l).
Proof. exact (MK_COMB (@lem1162970) (@lem1162969 _27338 P l)). Qed.
Lemma lem1162972 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term98 _27338 l P) = (term98 _27338 l P).
Proof. exact (eq_refl (term98 _27338 l P)). Qed.
Lemma lem1162973 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term163 _27338 l P) = (term102 _27338 l P).
Proof. exact (MK_COMB (@lem1162971 _27338 P l) (@lem1162972 _27338 l P)). Qed.
Lemma lem1162974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1162975 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term169 _27338 l P) = (term170 _27338 l P).
Proof. exact (MK_COMB (@lem1162974) (@lem1162973 _27338 l P)). Qed.
Lemma lem1162976 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term165 _27338 P l i) = (term54 _27338 P i l).
Proof. exact (eq_refl (term165 _27338 P l i)). Qed.
Lemma lem1162977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1162978 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term171 _27338 P l i) = (term172 _27338 P i l).
Proof. exact (MK_COMB (@lem1162977) (@lem1162976 _27338 P i l)). Qed.
Lemma lem1162979 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term98 _27338 l P) = (term98 _27338 l P).
Proof. exact (eq_refl (term98 _27338 l P)). Qed.
Lemma lem1162980 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) : (term173 _27338 i l P) = (term174 _27338 i l P).
Proof. exact (MK_COMB (@lem1162978 _27338 P i l) (@lem1162979 _27338 l P)). Qed.
Lemma lem1162981 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term175 _27338 l P) = (term176 _27338 l P).
Proof. exact (fun_ext (fun i : nat => @lem1162980 _27338 i l P)). Qed.
Lemma lem1162982 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1162983 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term164 _27338 l P) = (term177 _27338 l P).
Proof. exact (MK_COMB (@lem1162982) (@lem1162981 _27338 l P)). Qed.
Lemma lem1162984 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : ((term163 _27338 l P) = (term164 _27338 l P)) = ((term102 _27338 l P) = (term177 _27338 l P)).
Proof. exact (MK_COMB (@lem1162975 _27338 l P) (@lem1162983 _27338 l P)). Qed.
Lemma lem1162985 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term102 _27338 l P) = (term177 _27338 l P).
Proof. exact (EQ_MP (@lem1162984 _27338 l P) (@lem1162965 _27338 l P)). Qed.
Lemma lem1162986 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term110 _27338 l P) = (term178 _27338 l P).
Proof. exact (MK_COMB (@lem1162961 _27338 l P) (@lem1162985 _27338 l P)). Qed.
Lemma lem1162990 {A : Type'} (P : A -> Prop) (Q : Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1162991 {_27338 : Type'} (P : _27338 -> Prop) (Q : Prop) : (term179 _27338 P Q) = (term180 _27338 P Q).
Proof. exact (@lem1162990 _27338 P Q). Qed.
Lemma lem1162992 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term181 _27338 l P) = (term182 _27338 l P).
Proof. exact (@lem1162991 _27338 (term160 _27338 l P) (term177 _27338 l P)). Qed.
Lemma lem1162993 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term183 _27338 l P x) = (term159 _27338 l P x).
Proof. exact (eq_refl (term183 _27338 l P x)). Qed.
Lemma lem1162994 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term184 _27338 l P) = (term160 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1162993 _27338 l P x)). Qed.
Lemma lem1162995 {_27338 : Type'} : (@ex _27338) = (@ex _27338).
Proof. exact (eq_refl (@ex _27338)). Qed.
Lemma lem1162996 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term185 _27338 l P) = (term161 _27338 l P).
Proof. exact (MK_COMB (@lem1162995 _27338) (@lem1162994 _27338 l P)). Qed.
Lemma lem1162997 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1162998 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term186 _27338 l P) = (term162 _27338 l P).
Proof. exact (MK_COMB (@lem1162997) (@lem1162996 _27338 l P)). Qed.
Lemma lem1162999 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term177 _27338 l P) = (term177 _27338 l P).
Proof. exact (eq_refl (term177 _27338 l P)). Qed.
Lemma lem1163000 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term181 _27338 l P) = (term178 _27338 l P).
Proof. exact (MK_COMB (@lem1162998 _27338 l P) (@lem1162999 _27338 l P)). Qed.
Lemma lem1163001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1163002 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term187 _27338 l P) = (term188 _27338 l P).
Proof. exact (MK_COMB (@lem1163001) (@lem1163000 _27338 l P)). Qed.
Lemma lem1163003 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term183 _27338 l P x) = (term159 _27338 l P x).
Proof. exact (eq_refl (term183 _27338 l P x)). Qed.
Lemma lem1163004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1163005 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term189 _27338 l P x) = (term190 _27338 l P x).
Proof. exact (MK_COMB (@lem1163004) (@lem1163003 _27338 l P x)). Qed.
Lemma lem1163006 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term177 _27338 l P) = (term177 _27338 l P).
Proof. exact (eq_refl (term177 _27338 l P)). Qed.
Lemma lem1163007 {_27338 : Type'} (x : _27338) (l : list _27338) (P : _27338 -> Prop) : (term191 _27338 x l P) = (term192 _27338 x l P).
Proof. exact (MK_COMB (@lem1163005 _27338 l P x) (@lem1163006 _27338 l P)). Qed.
Lemma lem1163008 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term193 _27338 l P) = (term194 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1163007 _27338 x l P)). Qed.
Lemma lem1163009 {_27338 : Type'} : (@ex _27338) = (@ex _27338).
Proof. exact (eq_refl (@ex _27338)). Qed.
Lemma lem1163010 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term182 _27338 l P) = (term195 _27338 l P).
Proof. exact (MK_COMB (@lem1163009 _27338) (@lem1163008 _27338 l P)). Qed.
Lemma lem1163011 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : ((term181 _27338 l P) = (term182 _27338 l P)) = ((term178 _27338 l P) = (term195 _27338 l P)).
Proof. exact (MK_COMB (@lem1163002 _27338 l P) (@lem1163010 _27338 l P)). Qed.
Lemma lem1163012 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term178 _27338 l P) = (term195 _27338 l P).
Proof. exact (EQ_MP (@lem1163011 _27338 l P) (@lem1162992 _27338 l P)). Qed.
Lemma lem1163014 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term196 A P Q) = (term197 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1163015 (P : nat -> Prop) (Q : nat -> Prop) : (term198 P Q) = (term199 P Q).
Proof. exact (@lem1163014 nat P Q). Qed.
Lemma lem1163016 {_27338 : Type'} (x : _27338) (l : list _27338) (P : _27338 -> Prop) : (term200 _27338 x l P) = (term201 _27338 x l P).
Proof. exact (@lem1163015 (term158 _27338 l P x) (term176 _27338 l P)). Qed.
Lemma lem1163017 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term202 _27338 l P x i) = (term156 _27338 i l P x).
Proof. exact (eq_refl (term202 _27338 l P x i)). Qed.
Lemma lem1163018 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term203 _27338 l P x) = (term158 _27338 l P x).
Proof. exact (fun_ext (fun i : nat => @lem1163017 _27338 i l P x)). Qed.
Lemma lem1163019 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1163020 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term204 _27338 l P x) = (term159 _27338 l P x).
Proof. exact (MK_COMB (@lem1163019) (@lem1163018 _27338 l P x)). Qed.
Lemma lem1163021 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1163022 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term205 _27338 l P x) = (term190 _27338 l P x).
Proof. exact (MK_COMB (@lem1163021) (@lem1163020 _27338 l P x)). Qed.
Lemma lem1163023 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) : (term206 _27338 l P i) = (term174 _27338 i l P).
Proof. exact (eq_refl (term206 _27338 l P i)). Qed.
Lemma lem1163024 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term207 _27338 l P) = (term176 _27338 l P).
Proof. exact (fun_ext (fun i : nat => @lem1163023 _27338 i l P)). Qed.
Lemma lem1163025 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1163026 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term208 _27338 l P) = (term177 _27338 l P).
Proof. exact (MK_COMB (@lem1163025) (@lem1163024 _27338 l P)). Qed.
Lemma lem1163027 {_27338 : Type'} (x : _27338) (l : list _27338) (P : _27338 -> Prop) : (term200 _27338 x l P) = (term192 _27338 x l P).
Proof. exact (MK_COMB (@lem1163022 _27338 l P x) (@lem1163026 _27338 l P)). Qed.
Lemma lem1163028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1163029 {_27338 : Type'} (x : _27338) (l : list _27338) (P : _27338 -> Prop) : (term209 _27338 x l P) = (term210 _27338 x l P).
Proof. exact (MK_COMB (@lem1163028) (@lem1163027 _27338 x l P)). Qed.
Lemma lem1163030 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term202 _27338 l P x i) = (term156 _27338 i l P x).
Proof. exact (eq_refl (term202 _27338 l P x i)). Qed.
Lemma lem1163031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1163032 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term211 _27338 l P x i) = (term212 _27338 i l P x).
Proof. exact (MK_COMB (@lem1163031) (@lem1163030 _27338 i l P x)). Qed.
Lemma lem1163033 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) : (term206 _27338 l P i) = (term174 _27338 i l P).
Proof. exact (eq_refl (term206 _27338 l P i)). Qed.
Lemma lem1163034 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) : (term213 _27338 x l P i) = (term214 _27338 x i l P).
Proof. exact (MK_COMB (@lem1163032 _27338 i l P x) (@lem1163033 _27338 i l P)). Qed.
Lemma lem1163035 {_27338 : Type'} (x : _27338) (l : list _27338) (P : _27338 -> Prop) : (term215 _27338 x l P) = (term216 _27338 x l P).
Proof. exact (fun_ext (fun i : nat => @lem1163034 _27338 x i l P)). Qed.
Lemma lem1163036 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1163037 {_27338 : Type'} (x : _27338) (l : list _27338) (P : _27338 -> Prop) : (term201 _27338 x l P) = (term217 _27338 x l P).
Proof. exact (MK_COMB (@lem1163036) (@lem1163035 _27338 x l P)). Qed.
Lemma lem1163038 {_27338 : Type'} (x : _27338) (l : list _27338) (P : _27338 -> Prop) : ((term200 _27338 x l P) = (term201 _27338 x l P)) = ((term192 _27338 x l P) = (term217 _27338 x l P)).
Proof. exact (MK_COMB (@lem1163029 _27338 x l P) (@lem1163037 _27338 x l P)). Qed.
Lemma lem1163039 {_27338 : Type'} (x : _27338) (l : list _27338) (P : _27338 -> Prop) : (term192 _27338 x l P) = (term217 _27338 x l P).
Proof. exact (EQ_MP (@lem1163038 _27338 x l P) (@lem1163016 _27338 x l P)). Qed.
Lemma lem1163040 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term194 _27338 l P) = (term218 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1163039 _27338 x l P)). Qed.
Lemma lem1163041 {_27338 : Type'} : (@ex _27338) = (@ex _27338).
Proof. exact (eq_refl (@ex _27338)). Qed.
Lemma lem1163042 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term195 _27338 l P) = (term219 _27338 l P).
Proof. exact (MK_COMB (@lem1163041 _27338) (@lem1163040 _27338 l P)). Qed.
Lemma lem1163043 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term178 _27338 l P) = (term219 _27338 l P).
Proof. exact (TRANS (@lem1163012 _27338 l P) (@lem1163042 _27338 l P)). Qed.
Lemma lem1163045 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term110 _27338 l P) = (term219 _27338 l P).
Proof. exact (TRANS (@lem1162986 _27338 l P) (@lem1163043 _27338 l P)). Qed.
Lemma lem1163046 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term52 _27338 l P) = (term219 _27338 l P).
Proof. exact (TRANS (@lem1162612 _27338 l P) (@lem1163045 _27338 l P)). Qed.
Lemma lem1163047 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (h1 : term52 _27338 l P) : term219 _27338 l P.
Proof. exact (EQ_MP (@lem1163046 _27338 l P) (@lem1162524 _27338 l P h1)). Qed.
Lemma lem1163048 {_27338 : Type'} (x : _27338) (l : list _27338) (P : _27338 -> Prop) (h1 : term217 _27338 x l P) : term217 _27338 x l P.
Proof. exact (h1). Qed.
Lemma lem1163049 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term214 _27338 x i l P) : term214 _27338 x i l P.
Proof. exact (h1). Qed.
Lemma lem1163052 {_27338 : Type'} (P : _27338 -> Prop) (x : _27338) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1163075 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term70 _27338 x i l) = (term70 _27338 x i l).
Proof. exact (eq_refl (term70 _27338 x i l)). Qed.
Lemma lem1163076 {_27338 : Type'} (x : _27338) (l : list _27338) : (term78 _27338 x l) = (term78 _27338 x l).
Proof. exact (fun_ext (fun i : nat => @lem1163075 _27338 x i l)). Qed.
Lemma lem1163077 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1163078 {_27338 : Type'} (x : _27338) (l : list _27338) : (term79 _27338 x l) = (term79 _27338 x l).
Proof. exact (MK_COMB (@lem1163077) (@lem1163076 _27338 x l)). Qed.
Lemma lem1163079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1163080 {_27338 : Type'} (x : _27338) (l : list _27338) : (term85 _27338 x l) = (term85 _27338 x l).
Proof. exact (MK_COMB (@lem1163079) (@lem1163078 _27338 x l)). Qed.
Lemma lem1163081 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term87 _27338 l P x) = (term87 _27338 l P x).
Proof. exact (MK_COMB (@lem1163080 _27338 x l) (@lem1163052 _27338 P x)). Qed.
Lemma lem1163082 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term97 _27338 l P) = (term97 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1163081 _27338 l P x)). Qed.
Lemma lem1163083 {_27338 : Type'} : (@all _27338) = (@all _27338).
Proof. exact (eq_refl (@all _27338)). Qed.
Lemma lem1163084 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term98 _27338 l P) = (term98 _27338 l P).
Proof. exact (MK_COMB (@lem1163083 _27338) (@lem1163082 _27338 l P)). Qed.
Lemma lem1163105 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term172 _27338 P i l) = (term172 _27338 P i l).
Proof. exact (eq_refl (term172 _27338 P i l)). Qed.
Lemma lem1163106 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) : (term174 _27338 i l P) = (term174 _27338 i l P).
Proof. exact (MK_COMB (@lem1163105 _27338 P i l) (@lem1163084 _27338 l P)). Qed.
Lemma lem1163133 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term125 _27338 i l P x) = (term125 _27338 i l P x).
Proof. exact (eq_refl (term125 _27338 i l P x)). Qed.
Lemma lem1163152 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term57 _27338 P i l) = (term57 _27338 P i l).
Proof. exact (eq_refl (term57 _27338 P i l)). Qed.
Lemma lem1163153 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term67 _27338 P l) = (term67 _27338 P l).
Proof. exact (fun_ext (fun i : nat => @lem1163152 _27338 P i l)). Qed.
Lemma lem1163154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1163155 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term68 _27338 P l) = (term68 _27338 P l).
Proof. exact (MK_COMB (@lem1163154) (@lem1163153 _27338 P l)). Qed.
Lemma lem1163156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1163157 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term104 _27338 P l) = (term104 _27338 P l).
Proof. exact (MK_COMB (@lem1163156) (@lem1163155 _27338 P l)). Qed.
Lemma lem1163158 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term156 _27338 i l P x) = (term156 _27338 i l P x).
Proof. exact (MK_COMB (@lem1163157 _27338 P l) (@lem1163133 _27338 i l P x)). Qed.
Lemma lem1163159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1163160 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term212 _27338 i l P x) = (term212 _27338 i l P x).
Proof. exact (MK_COMB (@lem1163159) (@lem1163158 _27338 i l P x)). Qed.
Lemma lem1163161 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) : (term214 _27338 x i l P) = (term214 _27338 x i l P).
Proof. exact (MK_COMB (@lem1163160 _27338 i l P x) (@lem1163106 _27338 i l P)). Qed.
Lemma lem1163162 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term214 _27338 x i l P) : term214 _27338 x i l P.
Proof. exact (EQ_MP (@lem1163161 _27338 x i l P) (@lem1163049 _27338 x i l P h1)). Qed.
Lemma lem1163163 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term156 _27338 i l P x.
Proof. exact (h1). Qed.
Lemma lem1163164 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term174 _27338 i l P.
Proof. exact (h1). Qed.
Lemma lem1163165 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term125 _27338 i l P x.
Proof. exact (proj2 (@lem1163163 _27338 i l P x h1)). Qed.
Lemma lem1163166 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term68 _27338 P l.
Proof. exact (proj1 (@lem1163163 _27338 i l P x h1)). Qed.
Lemma lem1163168 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term47 _27338 x i l.
Proof. exact (proj1 (@lem1163165 _27338 i l P x h1)). Qed.
Lemma lem1163171 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term98 _27338 l P.
Proof. exact (proj2 (@lem1163164 _27338 i l P h1)). Qed.
Lemma lem1163172 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term54 _27338 P i l.
Proof. exact (proj1 (@lem1163164 _27338 i l P h1)). Qed.
Lemma lem1163182 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term57 _27338 P i l) = (term57 _27338 P i l).
Proof. exact (eq_refl (term57 _27338 P i l)). Qed.
Lemma lem1163183 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term67 _27338 P l) = (term67 _27338 P l).
Proof. exact (fun_ext (fun i : nat => @lem1163182 _27338 P i l)). Qed.
Lemma lem1163184 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1163186 {_27338 : Type'} (P : _27338 -> Prop) (l : list _27338) : (term68 _27338 P l) = (term68 _27338 P l).
Proof. exact (MK_COMB (@lem1163184) (@lem1163183 _27338 P l)). Qed.
Lemma lem1163187 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term68 _27338 P l.
Proof. exact (EQ_MP (@lem1163186 _27338 P l) (@lem1163166 _27338 i l P x h1)). Qed.
Lemma lem1163201 {A : Type'} (P : A -> Prop) (Q : Prop) : (term220 A P Q) = (term221 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1163202 (P : nat -> Prop) (Q : Prop) : (term222 P Q) = (term223 P Q).
Proof. exact (@lem1163201 nat P Q). Qed.
Lemma lem1163203 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term224 _27338 l P x) = (term225 _27338 l P x).
Proof. exact (@lem1163202 (term78 _27338 x l) (P x)). Qed.
Lemma lem1163204 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term226 _27338 x l i) = (term70 _27338 x i l).
Proof. exact (eq_refl (term226 _27338 x l i)). Qed.
Lemma lem1163205 {_27338 : Type'} (x : _27338) (l : list _27338) : (term227 _27338 x l) = (term78 _27338 x l).
Proof. exact (fun_ext (fun i : nat => @lem1163204 _27338 x i l)). Qed.
Lemma lem1163206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1163207 {_27338 : Type'} (x : _27338) (l : list _27338) : (term228 _27338 x l) = (term79 _27338 x l).
Proof. exact (MK_COMB (@lem1163206) (@lem1163205 _27338 x l)). Qed.
Lemma lem1163208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1163209 {_27338 : Type'} (x : _27338) (l : list _27338) : (term229 _27338 x l) = (term85 _27338 x l).
Proof. exact (MK_COMB (@lem1163208) (@lem1163207 _27338 x l)). Qed.
Lemma lem1163210 {_27338 : Type'} (P : _27338 -> Prop) (x : _27338) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1163211 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term224 _27338 l P x) = (term87 _27338 l P x).
Proof. exact (MK_COMB (@lem1163209 _27338 x l) (@lem1163210 _27338 P x)). Qed.
Lemma lem1163212 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1163213 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term230 _27338 l P x) = (term231 _27338 l P x).
Proof. exact (MK_COMB (@lem1163212) (@lem1163211 _27338 l P x)). Qed.
Lemma lem1163214 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term226 _27338 x l i) = (term70 _27338 x i l).
Proof. exact (eq_refl (term226 _27338 x l i)). Qed.
Lemma lem1163215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1163216 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) : (term232 _27338 x l i) = (term233 _27338 x i l).
Proof. exact (MK_COMB (@lem1163215) (@lem1163214 _27338 x i l)). Qed.
Lemma lem1163217 {_27338 : Type'} (P : _27338 -> Prop) (x : _27338) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem1163218 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term234 _27338 l i P x) = (term235 _27338 i l P x).
Proof. exact (MK_COMB (@lem1163216 _27338 x i l) (@lem1163217 _27338 P x)). Qed.
Lemma lem1163219 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term236 _27338 l P x) = (term237 _27338 l P x).
Proof. exact (fun_ext (fun i : nat => @lem1163218 _27338 i l P x)). Qed.
Lemma lem1163220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1163221 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term225 _27338 l P x) = (term238 _27338 l P x).
Proof. exact (MK_COMB (@lem1163220) (@lem1163219 _27338 l P x)). Qed.
Lemma lem1163222 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : ((term224 _27338 l P x) = (term225 _27338 l P x)) = ((term87 _27338 l P x) = (term238 _27338 l P x)).
Proof. exact (MK_COMB (@lem1163213 _27338 l P x) (@lem1163221 _27338 l P x)). Qed.
Lemma lem1163223 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term87 _27338 l P x) = (term238 _27338 l P x).
Proof. exact (EQ_MP (@lem1163222 _27338 l P x) (@lem1163203 _27338 l P x)). Qed.
Lemma lem1163224 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term97 _27338 l P) = (term239 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1163223 _27338 l P x)). Qed.
Lemma lem1163225 {_27338 : Type'} : (@all _27338) = (@all _27338).
Proof. exact (eq_refl (@all _27338)). Qed.
Lemma lem1163226 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term98 _27338 l P) = (term240 _27338 l P).
Proof. exact (MK_COMB (@lem1163225 _27338) (@lem1163224 _27338 l P)). Qed.
Lemma lem1163239 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term235 _27338 i l P x) = (term235 _27338 i l P x).
Proof. exact (eq_refl (term235 _27338 i l P x)). Qed.
Lemma lem1163240 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term237 _27338 l P x) = (term237 _27338 l P x).
Proof. exact (fun_ext (fun i : nat => @lem1163239 _27338 i l P x)). Qed.
Lemma lem1163241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1163242 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (x : _27338) : (term238 _27338 l P x) = (term238 _27338 l P x).
Proof. exact (MK_COMB (@lem1163241) (@lem1163240 _27338 l P x)). Qed.
Lemma lem1163243 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term239 _27338 l P) = (term239 _27338 l P).
Proof. exact (fun_ext (fun x : _27338 => @lem1163242 _27338 l P x)). Qed.
Lemma lem1163244 {_27338 : Type'} : (@all _27338) = (@all _27338).
Proof. exact (eq_refl (@all _27338)). Qed.
Lemma lem1163245 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term240 _27338 l P) = (term240 _27338 l P).
Proof. exact (MK_COMB (@lem1163244 _27338) (@lem1163243 _27338 l P)). Qed.
Lemma lem1163246 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term98 _27338 l P) = (term240 _27338 l P).
Proof. exact (TRANS (@lem1163226 _27338 l P) (@lem1163245 _27338 l P)). Qed.
Lemma lem1163247 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term240 _27338 l P.
Proof. exact (EQ_MP (@lem1163246 _27338 l P) (@lem1163171 _27338 i l P h1)). Qed.
Lemma lem1163256 {_27338 : Type'} (_19585 : nat) (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term241 _27338 P l _19585.
Proof. exact (@lem1163187 _27338 i l P x h1 _19585). Qed.
Lemma lem1163257 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : (term241 _27338 P l _19585) = (term57 _27338 P _19585 l).
Proof. exact (eq_refl (term241 _27338 P l _19585)). Qed.
Lemma lem1163259 {_27338 : Type'} (_19586 : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term242 _27338 l P _19586.
Proof. exact (@lem1163247 _27338 i l P h1 _19586). Qed.
Lemma lem1163260 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (_19586 : _27338) : (term242 _27338 l P _19586) = (term238 _27338 l P _19586).
Proof. exact (eq_refl (term242 _27338 l P _19586)). Qed.
Lemma lem1163261 {_27338 : Type'} (_19586 : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term238 _27338 l P _19586.
Proof. exact (EQ_MP (@lem1163260 _27338 l P _19586) (@lem1163259 _27338 _19586 i l P h1)). Qed.
Lemma lem1163262 {_27338 : Type'} (_19586 : _27338) (_19587 : nat) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term243 _27338 l P _19586 _19587.
Proof. exact (@lem1163261 _27338 _19586 i l P h1 _19587). Qed.
Lemma lem1163263 {_27338 : Type'} (_19587 : nat) (l : list _27338) (P : _27338 -> Prop) (_19586 : _27338) : (term243 _27338 l P _19586 _19587) = (term235 _27338 _19587 l P _19586).
Proof. exact (eq_refl (term243 _27338 l P _19586 _19587)). Qed.
Lemma lem1163264 {_27338 : Type'} (_19587 : nat) (_19586 : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term235 _27338 _19587 l P _19586.
Proof. exact (EQ_MP (@lem1163263 _27338 _19587 l P _19586) (@lem1163262 _27338 _19586 _19587 i l P h1)). Qed.
Lemma lem1163272 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term80 _27338 P x.
Proof. exact (proj2 (@lem1163165 _27338 i l P x h1)). Qed.
Lemma lem1163276 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : x = (@EL _27338 i l).
Proof. exact (proj2 (@lem1163168 _27338 i l P x h1)). Qed.
Lemma lem1163287 {_27338 : Type'} (_19587 : nat) (l : list _27338) (P : _27338 -> Prop) (_19586 : _27338) : (term235 _27338 _19587 l P _19586) = (term244 _27338 _19587 l P _19586).
Proof. exact (@lem1162250 (term245 _27338 _19587 l) (term246 _27338 _19586 _19587 l) (P _19586)). Qed.
Lemma lem1163288 {_27338 : Type'} (_19587 : nat) (_19586 : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term244 _27338 _19587 l P _19586.
Proof. exact (EQ_MP (@lem1163287 _27338 _19587 l P _19586) (@lem1163264 _27338 _19587 _19586 i l P h1)). Qed.
Lemma lem1163292 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term247 _27338 P i l.
Proof. exact (proj2 (@lem1163172 _27338 i l P h1)). Qed.
Lemma lem1163320 {_27338 : Type'} (_19585 : nat) (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term57 _27338 P _19585 l.
Proof. exact (EQ_MP (@lem1163257 _27338 P _19585 l) (@lem1163256 _27338 _19585 i l P x h1)). Qed.
Lemma lem1163321 {_27338 : Type'} (P : _27338 -> Prop) : (term248 _27338 P) = (term248 _27338 P).
Proof. exact (eq_refl (term248 _27338 P)). Qed.
Lemma lem1163322 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : (term249 _27338 P x) = (term250 _27338 P i l).
Proof. exact (MK_COMB (@lem1163321 _27338 P) (@lem1163276 _27338 i l P x h1)). Qed.
Lemma lem1163323 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term250 _27338 P i l) = (term247 _27338 P i l).
Proof. exact (eq_refl (term250 _27338 P i l)). Qed.
Lemma lem1163324 {_27338 : Type'} (P : _27338 -> Prop) (x : _27338) : (term251 _27338 P x) = (term251 _27338 P x).
Proof. exact (eq_refl (term251 _27338 P x)). Qed.
Lemma lem1163325 {_27338 : Type'} (x : _27338) (P : _27338 -> Prop) (i : nat) (l : list _27338) : ((term249 _27338 P x) = (term250 _27338 P i l)) = ((term249 _27338 P x) = (term247 _27338 P i l)).
Proof. exact (MK_COMB (@lem1163324 _27338 P x) (@lem1163323 _27338 P i l)). Qed.
Lemma lem1163326 {_27338 : Type'} (P : _27338 -> Prop) (x : _27338) : (term249 _27338 P x) = (term80 _27338 P x).
Proof. exact (eq_refl (term249 _27338 P x)). Qed.
Lemma lem1163327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1163328 {_27338 : Type'} (P : _27338 -> Prop) (x : _27338) : (term251 _27338 P x) = (term252 _27338 P x).
Proof. exact (MK_COMB (@lem1163327) (@lem1163326 _27338 P x)). Qed.
Lemma lem1163329 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term247 _27338 P i l) = (term247 _27338 P i l).
Proof. exact (eq_refl (term247 _27338 P i l)). Qed.
Lemma lem1163330 {_27338 : Type'} (x : _27338) (P : _27338 -> Prop) (i : nat) (l : list _27338) : ((term249 _27338 P x) = (term247 _27338 P i l)) = ((term80 _27338 P x) = (term247 _27338 P i l)).
Proof. exact (MK_COMB (@lem1163328 _27338 P x) (@lem1163329 _27338 P i l)). Qed.
Lemma lem1163331 {_27338 : Type'} (x : _27338) (P : _27338 -> Prop) (i : nat) (l : list _27338) : ((term249 _27338 P x) = (term250 _27338 P i l)) = ((term80 _27338 P x) = (term247 _27338 P i l)).
Proof. exact (TRANS (@lem1163325 _27338 x P i l) (@lem1163330 _27338 x P i l)). Qed.
Lemma lem1163332 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : (term80 _27338 P x) = (term247 _27338 P i l).
Proof. exact (EQ_MP (@lem1163331 _27338 x P i l) (@lem1163322 _27338 i l P x h1)). Qed.
Lemma lem1163333 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term247 _27338 P i l.
Proof. exact (EQ_MP (@lem1163332 _27338 i l P x h1) (@lem1163272 _27338 i l P x h1)). Qed.
Lemma lem1163349 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term55 _27338 i l.
Proof. exact (proj1 (@lem1163168 _27338 i l P x h1)). Qed.
Lemma lem1163350 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term253 _27338 i l.
Proof. exact (fun h0 : term245 _27338 i l => @lem1163349 _27338 i l P x h1). Qed.
Lemma lem1163352 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1163353 {_27338 : Type'} (i : nat) (l : list _27338) : (term253 _27338 i l) = (term55 _27338 i l).
Proof. exact (@lem1163352 (term55 _27338 i l)). Qed.
Lemma lem1163354 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term55 _27338 i l.
Proof. exact (EQ_MP (@lem1163353 _27338 i l) (@lem1163350 _27338 i l P x h1)). Qed.
Lemma lem1163360 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1163361 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : (term57 _27338 P _19585 l) = (term255 _27338 P _19585 l).
Proof. exact (@lem1163360 (term56 _27338 P _19585 l) (term245 _27338 _19585 l)). Qed.
Lemma lem1163367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1163368 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : (term256 _27338 P _19585 l) = (term257 _27338 P _19585 l).
Proof. exact (MK_COMB (@lem1163367) (@lem1163361 _27338 P _19585 l)). Qed.
Lemma lem1163374 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : (term255 _27338 P _19585 l) = (term255 _27338 P _19585 l).
Proof. exact (eq_refl (term255 _27338 P _19585 l)). Qed.
Lemma lem1163375 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : ((term57 _27338 P _19585 l) = (term255 _27338 P _19585 l)) = ((term255 _27338 P _19585 l) = (term255 _27338 P _19585 l)).
Proof. exact (MK_COMB (@lem1163368 _27338 P _19585 l) (@lem1163374 _27338 P _19585 l)). Qed.
Lemma lem1163377 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1163378 (x : Prop) : (x = x) = True.
Proof. exact (@lem1163377 Prop x). Qed.
Lemma lem1163379 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : ((term255 _27338 P _19585 l) = (term255 _27338 P _19585 l)) = True.
Proof. exact (@lem1163378 (term255 _27338 P _19585 l)). Qed.
Lemma lem1163380 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : ((term57 _27338 P _19585 l) = (term255 _27338 P _19585 l)) = True.
Proof. exact (TRANS (@lem1163375 _27338 P _19585 l) (@lem1163379 _27338 P _19585 l)). Qed.
Lemma lem1163381 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : True = ((term57 _27338 P _19585 l) = (term255 _27338 P _19585 l)).
Proof. exact (SYM (@lem1163380 _27338 P _19585 l)). Qed.
Lemma lem1163382 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : (term57 _27338 P _19585 l) = (term255 _27338 P _19585 l).
Proof. exact (EQ_MP (@lem1163381 _27338 P _19585 l) (@lem0)). Qed.
Lemma lem1163383 {_27338 : Type'} (_19585 : nat) (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term255 _27338 P _19585 l.
Proof. exact (EQ_MP (@lem1163382 _27338 P _19585 l) (@lem1163320 _27338 _19585 i l P x h1)). Qed.
Lemma lem1163385 (b : Prop) (a : Prop) : (a \/ b) = (term258 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1163386 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : (term255 _27338 P _19585 l) = (term259 _27338 P _19585 l).
Proof. exact (@lem1163385 (term245 _27338 _19585 l) (term56 _27338 P _19585 l)). Qed.
Lemma lem1163388 (a : Prop) : (term46 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1163389 {_27338 : Type'} (_19585 : nat) (l : list _27338) : (term260 _27338 _19585 l) = (term55 _27338 _19585 l).
Proof. exact (@lem1163388 (term55 _27338 _19585 l)). Qed.
Lemma lem1163390 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1163391 {_27338 : Type'} (_19585 : nat) (l : list _27338) : (term261 _27338 _19585 l) = (term262 _27338 _19585 l).
Proof. exact (MK_COMB (@lem1163390) (@lem1163389 _27338 _19585 l)). Qed.
Lemma lem1163392 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : (term56 _27338 P _19585 l) = (term56 _27338 P _19585 l).
Proof. exact (eq_refl (term56 _27338 P _19585 l)). Qed.
Lemma lem1163393 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : (term259 _27338 P _19585 l) = (term49 _27338 P _19585 l).
Proof. exact (MK_COMB (@lem1163391 _27338 _19585 l) (@lem1163392 _27338 P _19585 l)). Qed.
Lemma lem1163394 {_27338 : Type'} (P : _27338 -> Prop) (_19585 : nat) (l : list _27338) : (term255 _27338 P _19585 l) = (term49 _27338 P _19585 l).
Proof. exact (TRANS (@lem1163386 _27338 P _19585 l) (@lem1163393 _27338 P _19585 l)). Qed.
Lemma lem1163397 {_27338 : Type'} (_19585 : nat) (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term49 _27338 P _19585 l.
Proof. exact (EQ_MP (@lem1163394 _27338 P _19585 l) (@lem1163383 _27338 _19585 i l P x h1)). Qed.
Lemma lem1163398 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term49 _27338 P i l.
Proof. exact (@lem1163397 _27338 i i l P x h1). Qed.
Lemma lem1163401 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term56 _27338 P i l.
Proof. exact (@lem1163398 _27338 i l P x h1 (@lem1163354 _27338 i l P x h1)). Qed.
Lemma lem1163402 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term263 _27338 P i l.
Proof. exact (fun h0 : term247 _27338 P i l => @lem1163401 _27338 i l P x h1). Qed.
Lemma lem1163404 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1163405 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term263 _27338 P i l) = (term56 _27338 P i l).
Proof. exact (@lem1163404 (term56 _27338 P i l)). Qed.
Lemma lem1163406 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term56 _27338 P i l.
Proof. exact (EQ_MP (@lem1163405 _27338 P i l) (@lem1163402 _27338 i l P x h1)). Qed.
Lemma lem1163409 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1163411 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term247 _27338 P i l) = (term264 _27338 P i l).
Proof. exact (@lem1163409 (term56 _27338 P i l)). Qed.
Lemma lem1163414 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term264 _27338 P i l.
Proof. exact (EQ_MP (@lem1163411 _27338 P i l) (@lem1163333 _27338 i l P x h1)). Qed.
Lemma lem1163417 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : False.
Proof. exact (@lem1163414 _27338 i l P x h1 (@lem1163406 _27338 i l P x h1)). Qed.
Lemma lem1163418 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : term265.
Proof. exact (fun h0 : ~ False => @lem1163417 _27338 i l P x h1). Qed.
Lemma lem1163420 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1163421 : term265 = False.
Proof. exact (@lem1163420 False). Qed.
Lemma lem1163484 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term55 _27338 i l.
Proof. exact (proj1 (@lem1163172 _27338 i l P h1)). Qed.
Lemma lem1163485 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term253 _27338 i l.
Proof. exact (fun h0 : term245 _27338 i l => @lem1163484 _27338 i l P h1). Qed.
Lemma lem1163487 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1163488 {_27338 : Type'} (i : nat) (l : list _27338) : (term253 _27338 i l) = (term55 _27338 i l).
Proof. exact (@lem1163487 (term55 _27338 i l)). Qed.
Lemma lem1163489 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term55 _27338 i l.
Proof. exact (EQ_MP (@lem1163488 _27338 i l) (@lem1163485 _27338 i l P h1)). Qed.
Lemma lem1163491 {_27338 : Type'} (x : _27338) : x = x.
Proof. exact (@lem21386 _27338 x). Qed.
Lemma lem1163492 {_27338 : Type'} (x : _27338) : x = x.
Proof. exact (@lem1163491 _27338 x). Qed.
Lemma lem1163493 {_27338 : Type'} (i : nat) (l : list _27338) : (@EL _27338 i l) = (@EL _27338 i l).
Proof. exact (@lem1163492 _27338 (@EL _27338 i l)). Qed.
Lemma lem1163494 {_27338 : Type'} (i : nat) (l : list _27338) : term266 _27338 i l.
Proof. exact (fun h0 : term267 _27338 i l => @lem1163493 _27338 i l). Qed.
Lemma lem1163496 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1163497 {_27338 : Type'} (i : nat) (l : list _27338) : (term266 _27338 i l) = ((@EL _27338 i l) = (@EL _27338 i l)).
Proof. exact (@lem1163496 ((@EL _27338 i l) = (@EL _27338 i l))). Qed.
Lemma lem1163498 {_27338 : Type'} (i : nat) (l : list _27338) : (@EL _27338 i l) = (@EL _27338 i l).
Proof. exact (EQ_MP (@lem1163497 _27338 i l) (@lem1163494 _27338 i l)). Qed.
Lemma lem1163514 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1163515 {_27338 : Type'} (P : _27338 -> Prop) (_19586 : _27338) (_19587 : nat) (l : list _27338) : (term268 _27338 _19587 l P _19586) = (term269 _27338 P _19586 _19587 l).
Proof. exact (@lem1163514 (P _19586) (term246 _27338 _19586 _19587 l)). Qed.
Lemma lem1163523 {_27338 : Type'} (_19587 : nat) (l : list _27338) : (term270 _27338 _19587 l) = (term270 _27338 _19587 l).
Proof. exact (eq_refl (term270 _27338 _19587 l)). Qed.
Lemma lem1163524 {_27338 : Type'} (P : _27338 -> Prop) (_19586 : _27338) (_19587 : nat) (l : list _27338) : (term244 _27338 _19587 l P _19586) = (term271 _27338 P _19586 _19587 l).
Proof. exact (MK_COMB (@lem1163523 _27338 _19587 l) (@lem1163515 _27338 P _19586 _19587 l)). Qed.
Lemma lem1163528 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1163529 {_27338 : Type'} (P : _27338 -> Prop) (_19586 : _27338) (_19587 : nat) (l : list _27338) : (term271 _27338 P _19586 _19587 l) = (term272 _27338 P _19586 _19587 l).
Proof. exact (@lem1163528 (P _19586) (term245 _27338 _19587 l) (term246 _27338 _19586 _19587 l)). Qed.
Lemma lem1163547 {_27338 : Type'} (P : _27338 -> Prop) (_19586 : _27338) (_19587 : nat) (l : list _27338) : (term244 _27338 _19587 l P _19586) = (term272 _27338 P _19586 _19587 l).
Proof. exact (TRANS (@lem1163524 _27338 P _19586 _19587 l) (@lem1163529 _27338 P _19586 _19587 l)). Qed.
Lemma lem1163548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1163549 {_27338 : Type'} (P : _27338 -> Prop) (_19586 : _27338) (_19587 : nat) (l : list _27338) : (term273 _27338 _19587 l P _19586) = (term274 _27338 P _19586 _19587 l).
Proof. exact (MK_COMB (@lem1163548) (@lem1163547 _27338 P _19586 _19587 l)). Qed.
Lemma lem1163567 {_27338 : Type'} (P : _27338 -> Prop) (_19586 : _27338) (_19587 : nat) (l : list _27338) : (term272 _27338 P _19586 _19587 l) = (term272 _27338 P _19586 _19587 l).
Proof. exact (eq_refl (term272 _27338 P _19586 _19587 l)). Qed.
Lemma lem1163568 {_27338 : Type'} (P : _27338 -> Prop) (_19586 : _27338) (_19587 : nat) (l : list _27338) : ((term244 _27338 _19587 l P _19586) = (term272 _27338 P _19586 _19587 l)) = ((term272 _27338 P _19586 _19587 l) = (term272 _27338 P _19586 _19587 l)).
Proof. exact (MK_COMB (@lem1163549 _27338 P _19586 _19587 l) (@lem1163567 _27338 P _19586 _19587 l)). Qed.
Lemma lem1163570 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1163571 (x : Prop) : (x = x) = True.
Proof. exact (@lem1163570 Prop x). Qed.
Lemma lem1163572 {_27338 : Type'} (P : _27338 -> Prop) (_19586 : _27338) (_19587 : nat) (l : list _27338) : ((term272 _27338 P _19586 _19587 l) = (term272 _27338 P _19586 _19587 l)) = True.
Proof. exact (@lem1163571 (term272 _27338 P _19586 _19587 l)). Qed.
Lemma lem1163573 {_27338 : Type'} (P : _27338 -> Prop) (_19586 : _27338) (_19587 : nat) (l : list _27338) : ((term244 _27338 _19587 l P _19586) = (term272 _27338 P _19586 _19587 l)) = True.
Proof. exact (TRANS (@lem1163568 _27338 P _19586 _19587 l) (@lem1163572 _27338 P _19586 _19587 l)). Qed.
Lemma lem1163574 {_27338 : Type'} (P : _27338 -> Prop) (_19586 : _27338) (_19587 : nat) (l : list _27338) : True = ((term244 _27338 _19587 l P _19586) = (term272 _27338 P _19586 _19587 l)).
Proof. exact (SYM (@lem1163573 _27338 P _19586 _19587 l)). Qed.
Lemma lem1163575 {_27338 : Type'} (P : _27338 -> Prop) (_19586 : _27338) (_19587 : nat) (l : list _27338) : (term244 _27338 _19587 l P _19586) = (term272 _27338 P _19586 _19587 l).
Proof. exact (EQ_MP (@lem1163574 _27338 P _19586 _19587 l) (@lem0)). Qed.
Lemma lem1163576 {_27338 : Type'} (_19586 : _27338) (_19587 : nat) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term272 _27338 P _19586 _19587 l.
Proof. exact (EQ_MP (@lem1163575 _27338 P _19586 _19587 l) (@lem1163288 _27338 _19587 _19586 i l P h1)). Qed.
Lemma lem1163578 (b : Prop) (a : Prop) : (a \/ b) = (term258 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1163579 {_27338 : Type'} (_19587 : nat) (l : list _27338) (P : _27338 -> Prop) (_19586 : _27338) : (term272 _27338 P _19586 _19587 l) = (term275 _27338 _19587 l P _19586).
Proof. exact (@lem1163578 (term70 _27338 _19586 _19587 l) (P _19586)). Qed.
Lemma lem1163581 (a : Prop) (b : Prop) : (term276 a b) = (term277 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1163582 {_27338 : Type'} (_19586 : _27338) (_19587 : nat) (l : list _27338) : (term278 _27338 _19586 _19587 l) = (term279 _27338 _19586 _19587 l).
Proof. exact (@lem1163581 (term245 _27338 _19587 l) (term246 _27338 _19586 _19587 l)). Qed.
Lemma lem1163584 (a : Prop) : (term46 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1163585 {_27338 : Type'} (_19587 : nat) (l : list _27338) : (term260 _27338 _19587 l) = (term55 _27338 _19587 l).
Proof. exact (@lem1163584 (term55 _27338 _19587 l)). Qed.
Lemma lem1163586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1163587 {_27338 : Type'} (_19587 : nat) (l : list _27338) : (term280 _27338 _19587 l) = (term281 _27338 _19587 l).
Proof. exact (MK_COMB (@lem1163586) (@lem1163585 _27338 _19587 l)). Qed.
Lemma lem1163589 (a : Prop) : (term46 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1163590 {_27338 : Type'} (_19586 : _27338) (_19587 : nat) (l : list _27338) : (term282 _27338 _19586 _19587 l) = (_19586 = (@EL _27338 _19587 l)).
Proof. exact (@lem1163589 (_19586 = (@EL _27338 _19587 l))). Qed.
Lemma lem1163591 {_27338 : Type'} (_19586 : _27338) (_19587 : nat) (l : list _27338) : (term279 _27338 _19586 _19587 l) = (term47 _27338 _19586 _19587 l).
Proof. exact (MK_COMB (@lem1163587 _27338 _19587 l) (@lem1163590 _27338 _19586 _19587 l)). Qed.
Lemma lem1163592 {_27338 : Type'} (_19586 : _27338) (_19587 : nat) (l : list _27338) : (term278 _27338 _19586 _19587 l) = (term47 _27338 _19586 _19587 l).
Proof. exact (TRANS (@lem1163582 _27338 _19586 _19587 l) (@lem1163591 _27338 _19586 _19587 l)). Qed.
Lemma lem1163593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1163594 {_27338 : Type'} (_19586 : _27338) (_19587 : nat) (l : list _27338) : (term283 _27338 _19586 _19587 l) = (term284 _27338 _19586 _19587 l).
Proof. exact (MK_COMB (@lem1163593) (@lem1163592 _27338 _19586 _19587 l)). Qed.
Lemma lem1163595 {_27338 : Type'} (P : _27338 -> Prop) (_19586 : _27338) : (P _19586) = (P _19586).
Proof. exact (eq_refl (P _19586)). Qed.
Lemma lem1163596 {_27338 : Type'} (_19587 : nat) (l : list _27338) (P : _27338 -> Prop) (_19586 : _27338) : (term275 _27338 _19587 l P _19586) = (term285 _27338 _19587 l P _19586).
Proof. exact (MK_COMB (@lem1163594 _27338 _19586 _19587 l) (@lem1163595 _27338 P _19586)). Qed.
Lemma lem1163597 {_27338 : Type'} (_19587 : nat) (l : list _27338) (P : _27338 -> Prop) (_19586 : _27338) : (term272 _27338 P _19586 _19587 l) = (term285 _27338 _19587 l P _19586).
Proof. exact (TRANS (@lem1163579 _27338 _19587 l P _19586) (@lem1163596 _27338 _19587 l P _19586)). Qed.
Lemma lem1163599 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term286 _27338 i l.
Proof. exact (conj (@lem1163489 _27338 i l P h1) (@lem1163498 _27338 i l)). Qed.
Lemma lem1163601 {_27338 : Type'} (_19587 : nat) (_19586 : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term285 _27338 _19587 l P _19586.
Proof. exact (EQ_MP (@lem1163597 _27338 _19587 l P _19586) (@lem1163576 _27338 _19586 _19587 i l P h1)). Qed.
Lemma lem1163602 {_27338 : Type'} (_19587 : nat) (_19586 : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term285 _27338 _19587 l P _19586.
Proof. exact (@lem1163601 _27338 _19587 _19586 i l P h1). Qed.
Lemma lem1163603 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term287 _27338 P i l.
Proof. exact (@lem1163602 _27338 i (@EL _27338 i l) i l P h1). Qed.
Lemma lem1163606 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term56 _27338 P i l.
Proof. exact (@lem1163603 _27338 i l P h1 (@lem1163599 _27338 i l P h1)). Qed.
Lemma lem1163607 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term263 _27338 P i l.
Proof. exact (fun h0 : term247 _27338 P i l => @lem1163606 _27338 i l P h1). Qed.
Lemma lem1163609 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1163610 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term263 _27338 P i l) = (term56 _27338 P i l).
Proof. exact (@lem1163609 (term56 _27338 P i l)). Qed.
Lemma lem1163611 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term56 _27338 P i l.
Proof. exact (EQ_MP (@lem1163610 _27338 P i l) (@lem1163607 _27338 i l P h1)). Qed.
Lemma lem1163614 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1163616 {_27338 : Type'} (P : _27338 -> Prop) (i : nat) (l : list _27338) : (term247 _27338 P i l) = (term264 _27338 P i l).
Proof. exact (@lem1163614 (term56 _27338 P i l)). Qed.
Lemma lem1163619 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term264 _27338 P i l.
Proof. exact (EQ_MP (@lem1163616 _27338 P i l) (@lem1163292 _27338 i l P h1)). Qed.
Lemma lem1163622 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : False.
Proof. exact (@lem1163619 _27338 i l P h1 (@lem1163611 _27338 i l P h1)). Qed.
Lemma lem1163623 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : term265.
Proof. exact (fun h0 : ~ False => @lem1163622 _27338 i l P h1). Qed.
Lemma lem1163625 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1163626 : term265 = False.
Proof. exact (@lem1163625 False). Qed.
Lemma lem1163627 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term174 _27338 i l P) : False.
Proof. exact (EQ_MP (@lem1163626) (@lem1163623 _27338 i l P h1)). Qed.
Lemma lem1163628 {_27338 : Type'} (i : nat) (l : list _27338) (P : _27338 -> Prop) (x : _27338) (h1 : term156 _27338 i l P x) : False.
Proof. exact (EQ_MP (@lem1163421) (@lem1163418 _27338 i l P x h1)). Qed.
Lemma lem1163629 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term214 _27338 x i l P) : False.
Proof. exact (or_elim (@lem1163162 _27338 x i l P h1) (fun h0 : term156 _27338 i l P x => @lem1163628 _27338 i l P x h0) (fun h0 : term174 _27338 i l P => @lem1163627 _27338 i l P h0)). Qed.
Lemma lem1163630 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term214 _27338 x i l P) : (term214 _27338 x i l P) = False.
Proof. exact (prop_ext (fun h2 : term214 _27338 x i l P => @lem1163629 _27338 x i l P h1) (fun h2 : False => @lem1163162 _27338 x i l P h1)). Qed.
Lemma lem1163631 {_27338 : Type'} (x : _27338) (i : nat) (l : list _27338) (P : _27338 -> Prop) (h1 : term214 _27338 x i l P) : False.
Proof. exact (EQ_MP (@lem1163630 _27338 x i l P h1) (@lem1163162 _27338 x i l P h1)). Qed.
Lemma lem1163632 {_27338 : Type'} (x : _27338) (l : list _27338) (P : _27338 -> Prop) (h1 : term217 _27338 x l P) : False.
Proof. exact (ex_elim (@lem1163048 _27338 x l P h1) (fun i : nat => fun h0 : term216 _27338 x l P i => @lem1163631 _27338 x i l P h0)). Qed.
Lemma lem1163633 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (h1 : term52 _27338 l P) : False.
Proof. exact (ex_elim (@lem1163047 _27338 l P h1) (fun x : _27338 => fun h0 : term218 _27338 l P x => @lem1163632 _27338 x l P h0)). Qed.
Lemma lem1163634 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (h1 : term52 _27338 l P) : (term52 _27338 l P) = False.
Proof. exact (prop_ext (fun h2 : term52 _27338 l P => @lem1163633 _27338 l P h1) (fun h2 : False => @lem1162524 _27338 l P h1)). Qed.
Lemma lem1163635 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) (h1 : term52 _27338 l P) : False.
Proof. exact (EQ_MP (@lem1163634 _27338 l P h1) (@lem1162524 _27338 l P h1)). Qed.
Lemma lem1163636 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : term51 _27338 l P.
Proof. exact (fun h0 : term52 _27338 l P => @lem1163635 _27338 l P h0). Qed.
Lemma lem1163637 {_27338 : Type'} (l : list _27338) (P : _27338 -> Prop) : (term30 _27338 P l) = (term28 _27338 l P).
Proof. exact (EQ_MP (@lem1162523 _27338 l P) (@lem1163636 _27338 l P)). Qed.
Lemma lem1163642 {_27338 : Type'} (P : _27338 -> Prop) : term34 _27338 P.
Proof. exact (fun l : list _27338 => @lem1163637 _27338 l P). Qed.
Lemma lem1163647 {_27338 : Type'} : term38 _27338.
Proof. exact (fun P : _27338 -> Prop => @lem1163642 _27338 P). Qed.
Lemma lem1163648 {_27338 : Type'} : term40 _27338.
Proof. exact (EQ_MP (@lem1162519 _27338) (@lem1163647 _27338)). Qed.
Lemma lem1163650 {_27338 : Type'} : term40 _27338.
Proof. exact (@lem1162366 _27338 (@lem1163648 _27338)). Qed.
Lemma lem1163651 {_27338 : Type'} (h1 : term41 _27338) : False.
Proof. exact (@lem1163650 _27338 (@lem1162350 _27338 h1)). Qed.
Lemma lem1163652 {_27338 : Type'} (h1 : term41 _27338) : (term41 _27338) = False.
Proof. exact (prop_ext (fun h2 : term41 _27338 => @lem1163651 _27338 h1) (fun h2 : False => @lem1162350 _27338 h1)). Qed.
Lemma lem1163653 {_27338 : Type'} (h1 : term41 _27338) : False.
Proof. exact (EQ_MP (@lem1163652 _27338 h1) (@lem1162350 _27338 h1)). Qed.
Lemma lem1163654 {_27338 : Type'} : term40 _27338.
Proof. exact (fun h0 : term41 _27338 => @lem1163653 _27338 h0). Qed.
Lemma lem1163655 {_27338 : Type'} : term38 _27338.
Proof. exact (EQ_MP (@lem1162349 _27338) (@lem1163654 _27338)). Qed.
Lemma lem1163656 {_27338 : Type'} : term37 _27338.
Proof. exact (EQ_MP (@lem1162345 _27338) (@lem1163655 _27338)). Qed.
