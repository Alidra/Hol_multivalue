Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_LT_ALL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import REAL_LT_IMP_LE_spec.
Require Import SUM_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm69_spec.
Lemma lem7073064 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7073065 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7073066 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7073065 t1) (@lem7073064 t1)). Qed.
Lemma lem7073067 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7073066 t1 t2). Qed.
Lemma lem7073068 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7073069 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7073068 t1 t2) (@lem7073067 t1 t2)). Qed.
Lemma lem7073070 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7073069 t1 t2 t3). Qed.
Lemma lem7073071 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7073072 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7073071 t1 t2 t3) (@lem7073070 t1 t2 t3)). Qed.
Lemma lem7073073 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7073072 t1 t2 t3)). Qed.
Lemma lem7073075 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7073076 {_132203 : Type'} : (term8 _132203) = (term9 _132203).
Proof. exact (@lem7073075 (term8 _132203)). Qed.
Lemma lem7073077 {_132203 : Type'} : (term9 _132203) = (term8 _132203).
Proof. exact (SYM (@lem7073076 _132203)). Qed.
Lemma lem7073078 {_132203 : Type'} (h1 : term10 _132203) : term10 _132203.
Proof. exact (h1). Qed.
Lemma lem7073079 {_132203 : Type'} : term11 _132203.
Proof. exact (@lem3216368 _132203). Qed.
Lemma lem7073082 {_132203 : Type'} : term12 _132203.
Proof. exact (@lem7073063 _132203). Qed.
Lemma lem7073087 {_132203 A : Type'} (h1 : term13 _132203 A) : term13 _132203 A.
Proof. exact (h1). Qed.
Lemma lem7073088 {_132203 A : Type'} : term14 _132203 A.
Proof. exact (fun h0 : term13 _132203 A => @lem7073087 _132203 A h0). Qed.
Lemma lem7073089 {_132203 A : Type'} (h1 : term14 _132203 A) : term14 _132203 A.
Proof. exact (h1). Qed.
Lemma lem7073090 {_132203 A : Type'} (h1 : term13 _132203 A) : term13 _132203 A.
Proof. exact (h1). Qed.
Lemma lem7073091 {_132203 A : Type'} (h1 : term13 _132203 A) (h2 : term14 _132203 A) : term13 _132203 A.
Proof. exact (@lem7073089 _132203 A h2 (@lem7073090 _132203 A h1)). Qed.
Lemma lem7073092 {_132203 A : Type'} (h1 : term13 _132203 A) : term15 _132203 A.
Proof. exact (fun h0 : term14 _132203 A => @lem7073091 _132203 A h1 h0). Qed.
Lemma lem7073093 {_132203 A : Type'} (h1 : term14 _132203 A) : term14 _132203 A.
Proof. exact (h1). Qed.
Lemma lem7073094 {_132203 A : Type'} (h1 : term13 _132203 A) (h2 : term14 _132203 A) : term13 _132203 A.
Proof. exact (@lem7073092 _132203 A h1 (@lem7073093 _132203 A h2)). Qed.
Lemma lem7073095 {_132203 A : Type'} (h1 : term14 _132203 A) : term14 _132203 A.
Proof. exact (fun h0 : term13 _132203 A => @lem7073094 _132203 A h0 h1). Qed.
Lemma lem7073096 {_132203 A : Type'} : term16 _132203 A.
Proof. exact (fun h0 : term14 _132203 A => @lem7073095 _132203 A h0). Qed.
Lemma lem7073099 {_132203 A : Type'} : term14 _132203 A.
Proof. exact (@lem7073096 _132203 A (@lem7073088 _132203 A)). Qed.
Lemma lem7073100 {_132203 A : Type'} : term14 _132203 A.
Proof. exact (@lem7073099 _132203 A). Qed.
Lemma lem7073292 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7073293 {_132203 : Type'} : (term17 _132203) = (term18 _132203).
Proof. exact (@lem7073292 (term11 _132203)). Qed.
Lemma lem7073302 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem7073303 {_132203 : Type'} : (term20 _132203) = (term21 _132203).
Proof. exact (MK_COMB (@lem7073302) (@lem7073293 _132203)). Qed.
Lemma lem7073306 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem7073307 {_132203 A : Type'} : (term23 _132203 A) = (term24 _132203 A).
Proof. exact (MK_COMB (@lem7073306 A) (@lem7073303 _132203)). Qed.
Lemma lem7073310 {_132203 : Type'} : (term22 _132203) = (term22 _132203).
Proof. exact (eq_refl (term22 _132203)). Qed.
Lemma lem7073311 {_132203 A : Type'} : (term25 _132203 A) = (term26 _132203 A).
Proof. exact (MK_COMB (@lem7073310 _132203) (@lem7073307 _132203 A)). Qed.
Lemma lem7073314 {_132203 : Type'} : (term27 _132203) = (term27 _132203).
Proof. exact (eq_refl (term27 _132203)). Qed.
Lemma lem7073321 {_132203 A : Type'} : (term13 _132203 A) = (term28 _132203 A).
Proof. exact (MK_COMB (@lem7073314 _132203) (@lem7073311 _132203 A)). Qed.
Lemma lem7073324 {_132203 : Type'} (s : _132203 -> Prop) : (term29 _132203 s) = (term29 _132203 s).
Proof. exact (eq_refl (term29 _132203 s)). Qed.
Lemma lem7073325 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (@IN _132203 x s) = (@IN _132203 x s).
Proof. exact (eq_refl (@IN _132203 x s)). Qed.
Lemma lem7073326 {_132203 : Type'} (s : _132203 -> Prop) : (term30 _132203 s) = (term30 _132203 s).
Proof. exact (fun_ext (fun x : _132203 => @lem7073325 _132203 x s)). Qed.
Lemma lem7073327 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7073328 {_132203 : Type'} (s : _132203 -> Prop) : (term31 _132203 s) = (term31 _132203 s).
Proof. exact (MK_COMB (@lem7073327 _132203) (@lem7073326 _132203 s)). Qed.
Lemma lem7073329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7073330 {_132203 : Type'} (s : _132203 -> Prop) : (term32 _132203 s) = (term32 _132203 s).
Proof. exact (MK_COMB (@lem7073329) (@lem7073328 _132203 s)). Qed.
Lemma lem7073331 {_132203 : Type'} (s : _132203 -> Prop) : ((term31 _132203 s) = (term29 _132203 s)) = ((term31 _132203 s) = (term29 _132203 s)).
Proof. exact (MK_COMB (@lem7073330 _132203 s) (@lem7073324 _132203 s)). Qed.
Lemma lem7073332 {_132203 : Type'} : (term33 _132203) = (term33 _132203).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7073331 _132203 s)). Qed.
Lemma lem7073333 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7073334 {_132203 : Type'} : (term11 _132203) = (term11 _132203).
Proof. exact (MK_COMB (@lem7073333 _132203) (@lem7073332 _132203)). Qed.
Lemma lem7073335 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7073336 {_132203 : Type'} : (term18 _132203) = (term18 _132203).
Proof. exact (MK_COMB (@lem7073335) (@lem7073334 _132203)). Qed.
Lemma lem7073341 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem7073342 (x : real) : (term35 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem7073341 x y)). Qed.
Lemma lem7073343 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7073344 (x : real) : (term36 x) = (term36 x).
Proof. exact (MK_COMB (@lem7073343) (@lem7073342 x)). Qed.
Lemma lem7073345 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem7073344 x)). Qed.
Lemma lem7073346 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7073347 : term38 = term38.
Proof. exact (MK_COMB (@lem7073346) (@lem7073345)). Qed.
Lemma lem7073348 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7073349 : term19 = term19.
Proof. exact (MK_COMB (@lem7073348) (@lem7073347)). Qed.
Lemma lem7073350 {_132203 : Type'} : (term21 _132203) = (term21 _132203).
Proof. exact (MK_COMB (@lem7073349) (@lem7073336 _132203)). Qed.
Lemma lem7073351 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term39 A f s g) = (term39 A f s g).
Proof. exact (eq_refl (term39 A f s g)). Qed.
Lemma lem7073356 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term40 A s f g x) = (term40 A s f g x).
Proof. exact (eq_refl (term40 A s f g x)). Qed.
Lemma lem7073357 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term41 A s f g) = (term41 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7073356 A s f g x)). Qed.
Lemma lem7073358 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7073359 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term42 A s f g) = (term42 A s f g).
Proof. exact (MK_COMB (@lem7073358 A) (@lem7073357 A s f g)). Qed.
Lemma lem7073364 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term43 A s f g x) = (term43 A s f g x).
Proof. exact (eq_refl (term43 A s f g x)). Qed.
Lemma lem7073365 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term44 A s f g) = (term44 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7073364 A s f g x)). Qed.
Lemma lem7073366 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7073367 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term45 A s f g) = (term45 A s f g).
Proof. exact (MK_COMB (@lem7073366 A) (@lem7073365 A s f g)). Qed.
Lemma lem7073368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7073369 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term46 A s f g) = (term46 A s f g).
Proof. exact (MK_COMB (@lem7073368) (@lem7073367 A s f g)). Qed.
Lemma lem7073370 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term47 A s f g) = (term47 A s f g).
Proof. exact (MK_COMB (@lem7073369 A s f g) (@lem7073359 A s f g)). Qed.
Lemma lem7073373 {A : Type'} (s : A -> Prop) : (term48 A s) = (term48 A s).
Proof. exact (eq_refl (term48 A s)). Qed.
Lemma lem7073374 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term49 A s f g) = (term49 A s f g).
Proof. exact (MK_COMB (@lem7073373 A s) (@lem7073370 A s f g)). Qed.
Lemma lem7073375 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7073376 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term50 A s f g) = (term50 A s f g).
Proof. exact (MK_COMB (@lem7073375) (@lem7073374 A s f g)). Qed.
Lemma lem7073377 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term51 A f s g) = (term51 A f s g).
Proof. exact (MK_COMB (@lem7073376 A s f g) (@lem7073351 A f s g)). Qed.
Lemma lem7073378 {A : Type'} (f : A -> real) (g : A -> real) : (term52 A f g) = (term52 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7073377 A f s g)). Qed.
Lemma lem7073379 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7073380 {A : Type'} (f : A -> real) (g : A -> real) : (term53 A f g) = (term53 A f g).
Proof. exact (MK_COMB (@lem7073379 A) (@lem7073378 A f g)). Qed.
Lemma lem7073381 {A : Type'} (f : A -> real) : (term54 A f) = (term54 A f).
Proof. exact (fun_ext (fun g : A -> real => @lem7073380 A f g)). Qed.
Lemma lem7073382 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7073383 {A : Type'} (f : A -> real) : (term55 A f) = (term55 A f).
Proof. exact (MK_COMB (@lem7073382 A) (@lem7073381 A f)). Qed.
Lemma lem7073384 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7073383 A f)). Qed.
Lemma lem7073385 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7073386 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem7073385 A) (@lem7073384 A)). Qed.
Lemma lem7073387 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7073388 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem7073387) (@lem7073386 A)). Qed.
Lemma lem7073389 {_132203 A : Type'} : (term24 _132203 A) = (term24 _132203 A).
Proof. exact (MK_COMB (@lem7073388 A) (@lem7073350 _132203)). Qed.
Lemma lem7073390 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term39 _132203 f s g) = (term39 _132203 f s g).
Proof. exact (eq_refl (term39 _132203 f s g)). Qed.
Lemma lem7073395 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term40 _132203 s f g x) = (term40 _132203 s f g x).
Proof. exact (eq_refl (term40 _132203 s f g x)). Qed.
Lemma lem7073396 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term41 _132203 s f g) = (term41 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7073395 _132203 s f g x)). Qed.
Lemma lem7073397 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7073398 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term42 _132203 s f g) = (term42 _132203 s f g).
Proof. exact (MK_COMB (@lem7073397 _132203) (@lem7073396 _132203 s f g)). Qed.
Lemma lem7073403 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term43 _132203 s f g x) = (term43 _132203 s f g x).
Proof. exact (eq_refl (term43 _132203 s f g x)). Qed.
Lemma lem7073404 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term44 _132203 s f g) = (term44 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7073403 _132203 s f g x)). Qed.
Lemma lem7073405 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7073406 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term45 _132203 s f g) = (term45 _132203 s f g).
Proof. exact (MK_COMB (@lem7073405 _132203) (@lem7073404 _132203 s f g)). Qed.
Lemma lem7073407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7073408 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term46 _132203 s f g) = (term46 _132203 s f g).
Proof. exact (MK_COMB (@lem7073407) (@lem7073406 _132203 s f g)). Qed.
Lemma lem7073409 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term47 _132203 s f g) = (term47 _132203 s f g).
Proof. exact (MK_COMB (@lem7073408 _132203 s f g) (@lem7073398 _132203 s f g)). Qed.
Lemma lem7073412 {_132203 : Type'} (s : _132203 -> Prop) : (term48 _132203 s) = (term48 _132203 s).
Proof. exact (eq_refl (term48 _132203 s)). Qed.
Lemma lem7073413 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term49 _132203 s f g) = (term49 _132203 s f g).
Proof. exact (MK_COMB (@lem7073412 _132203 s) (@lem7073409 _132203 s f g)). Qed.
Lemma lem7073414 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7073415 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term50 _132203 s f g) = (term50 _132203 s f g).
Proof. exact (MK_COMB (@lem7073414) (@lem7073413 _132203 s f g)). Qed.
Lemma lem7073416 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term51 _132203 f s g) = (term51 _132203 f s g).
Proof. exact (MK_COMB (@lem7073415 _132203 s f g) (@lem7073390 _132203 f s g)). Qed.
Lemma lem7073417 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term52 _132203 f g) = (term52 _132203 f g).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7073416 _132203 f s g)). Qed.
Lemma lem7073418 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7073419 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term53 _132203 f g) = (term53 _132203 f g).
Proof. exact (MK_COMB (@lem7073418 _132203) (@lem7073417 _132203 f g)). Qed.
Lemma lem7073420 {_132203 : Type'} (f : _132203 -> real) : (term54 _132203 f) = (term54 _132203 f).
Proof. exact (fun_ext (fun g : _132203 -> real => @lem7073419 _132203 f g)). Qed.
Lemma lem7073421 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7073422 {_132203 : Type'} (f : _132203 -> real) : (term55 _132203 f) = (term55 _132203 f).
Proof. exact (MK_COMB (@lem7073421 _132203) (@lem7073420 _132203 f)). Qed.
Lemma lem7073423 {_132203 : Type'} : (term56 _132203) = (term56 _132203).
Proof. exact (fun_ext (fun f : _132203 -> real => @lem7073422 _132203 f)). Qed.
Lemma lem7073424 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7073425 {_132203 : Type'} : (term12 _132203) = (term12 _132203).
Proof. exact (MK_COMB (@lem7073424 _132203) (@lem7073423 _132203)). Qed.
Lemma lem7073426 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7073427 {_132203 : Type'} : (term22 _132203) = (term22 _132203).
Proof. exact (MK_COMB (@lem7073426) (@lem7073425 _132203)). Qed.
Lemma lem7073428 {_132203 A : Type'} : (term26 _132203 A) = (term26 _132203 A).
Proof. exact (MK_COMB (@lem7073427 _132203) (@lem7073389 _132203 A)). Qed.
Lemma lem7073429 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term39 _132203 f s g) = (term39 _132203 f s g).
Proof. exact (eq_refl (term39 _132203 f s g)). Qed.
Lemma lem7073434 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term57 _132203 s f g x) = (term57 _132203 s f g x).
Proof. exact (eq_refl (term57 _132203 s f g x)). Qed.
Lemma lem7073435 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term58 _132203 s f g) = (term58 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7073434 _132203 s f g x)). Qed.
Lemma lem7073436 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7073437 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term59 _132203 s f g) = (term59 _132203 s f g).
Proof. exact (MK_COMB (@lem7073436 _132203) (@lem7073435 _132203 s f g)). Qed.
Lemma lem7073442 {_132203 : Type'} (s : _132203 -> Prop) : (term60 _132203 s) = (term60 _132203 s).
Proof. exact (eq_refl (term60 _132203 s)). Qed.
Lemma lem7073443 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term61 _132203 s f g) = (term61 _132203 s f g).
Proof. exact (MK_COMB (@lem7073442 _132203 s) (@lem7073437 _132203 s f g)). Qed.
Lemma lem7073446 {_132203 : Type'} (s : _132203 -> Prop) : (term48 _132203 s) = (term48 _132203 s).
Proof. exact (eq_refl (term48 _132203 s)). Qed.
Lemma lem7073447 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term62 _132203 s f g) = (term62 _132203 s f g).
Proof. exact (MK_COMB (@lem7073446 _132203 s) (@lem7073443 _132203 s f g)). Qed.
Lemma lem7073448 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7073449 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term63 _132203 s f g) = (term63 _132203 s f g).
Proof. exact (MK_COMB (@lem7073448) (@lem7073447 _132203 s f g)). Qed.
Lemma lem7073450 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term64 _132203 f s g) = (term64 _132203 f s g).
Proof. exact (MK_COMB (@lem7073449 _132203 s f g) (@lem7073429 _132203 f s g)). Qed.
Lemma lem7073451 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term65 _132203 f g) = (term65 _132203 f g).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7073450 _132203 f s g)). Qed.
Lemma lem7073452 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7073453 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term66 _132203 f g) = (term66 _132203 f g).
Proof. exact (MK_COMB (@lem7073452 _132203) (@lem7073451 _132203 f g)). Qed.
Lemma lem7073454 {_132203 : Type'} (f : _132203 -> real) : (term67 _132203 f) = (term67 _132203 f).
Proof. exact (fun_ext (fun g : _132203 -> real => @lem7073453 _132203 f g)). Qed.
Lemma lem7073455 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7073456 {_132203 : Type'} (f : _132203 -> real) : (term68 _132203 f) = (term68 _132203 f).
Proof. exact (MK_COMB (@lem7073455 _132203) (@lem7073454 _132203 f)). Qed.
Lemma lem7073457 {_132203 : Type'} : (term69 _132203) = (term69 _132203).
Proof. exact (fun_ext (fun f : _132203 -> real => @lem7073456 _132203 f)). Qed.
Lemma lem7073458 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7073459 {_132203 : Type'} : (term8 _132203) = (term8 _132203).
Proof. exact (MK_COMB (@lem7073458 _132203) (@lem7073457 _132203)). Qed.
Lemma lem7073460 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7073461 {_132203 : Type'} : (term10 _132203) = (term10 _132203).
Proof. exact (MK_COMB (@lem7073460) (@lem7073459 _132203)). Qed.
Lemma lem7073462 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7073463 {_132203 : Type'} : (term27 _132203) = (term27 _132203).
Proof. exact (MK_COMB (@lem7073462) (@lem7073461 _132203)). Qed.
Lemma lem7073464 {_132203 A : Type'} : (term28 _132203 A) = (term28 _132203 A).
Proof. exact (MK_COMB (@lem7073463 _132203) (@lem7073428 _132203 A)). Qed.
Lemma lem7073613 {_132203 A : Type'} : (term13 _132203 A) = (term28 _132203 A).
Proof. exact (TRANS (@lem7073321 _132203 A) (@lem7073464 _132203 A)). Qed.
Lemma lem7073614 {_132203 A : Type'} : (term28 _132203 A) = (term13 _132203 A).
Proof. exact (SYM (@lem7073613 _132203 A)). Qed.
Lemma lem7073615 {_132203 : Type'} (h1 : term10 _132203) : term10 _132203.
Proof. exact (h1). Qed.
Lemma lem7073616 {_132203 : Type'} (h1 : term12 _132203) : term12 _132203.
Proof. exact (h1). Qed.
Lemma lem7073617 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem7073618 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem7073619 {_132203 : Type'} (h1 : term11 _132203) : term11 _132203.
Proof. exact (h1). Qed.
Lemma lem7073628 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term57 _132203 s f g x) = (term70 _132203 s f g x).
Proof. exact (@lem17265 (@IN _132203 x s) (term71 _132203 f g x)). Qed.
Lemma lem7073629 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term58 _132203 s f g) = (term72 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7073628 _132203 s f g x)). Qed.
Lemma lem7073630 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7073631 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term59 _132203 s f g) = (term73 _132203 s f g).
Proof. exact (MK_COMB (@lem7073630 _132203) (@lem7073629 _132203 s f g)). Qed.
Lemma lem7073633 {_132203 : Type'} (s : _132203 -> Prop) : (term60 _132203 s) = (term60 _132203 s).
Proof. exact (eq_refl (term60 _132203 s)). Qed.
Lemma lem7073634 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term61 _132203 s f g) = (term74 _132203 s f g).
Proof. exact (MK_COMB (@lem7073633 _132203 s) (@lem7073631 _132203 s f g)). Qed.
Lemma lem7073636 {_132203 : Type'} (s : _132203 -> Prop) : (term48 _132203 s) = (term48 _132203 s).
Proof. exact (eq_refl (term48 _132203 s)). Qed.
Lemma lem7073637 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term62 _132203 s f g) = (term75 _132203 s f g).
Proof. exact (MK_COMB (@lem7073636 _132203 s) (@lem7073634 _132203 s f g)). Qed.
Lemma lem7073638 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term76 _132203 f s g) = (term76 _132203 f s g).
Proof. exact (eq_refl (term76 _132203 f s g)). Qed.
Lemma lem7073639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7073640 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term77 _132203 s f g) = (term78 _132203 s f g).
Proof. exact (MK_COMB (@lem7073639) (@lem7073637 _132203 s f g)). Qed.
Lemma lem7073641 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term79 _132203 f s g) = (term80 _132203 f s g).
Proof. exact (MK_COMB (@lem7073640 _132203 s f g) (@lem7073638 _132203 f s g)). Qed.
Lemma lem7073642 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term81 _132203 f s g) = (term79 _132203 f s g).
Proof. exact (@lem17362 (term62 _132203 s f g) (term39 _132203 f s g)). Qed.
Lemma lem7073643 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term81 _132203 f s g) = (term80 _132203 f s g).
Proof. exact (TRANS (@lem7073642 _132203 f s g) (@lem7073641 _132203 f s g)). Qed.
Lemma lem7073644 {_132203 : Type'} (P : type686 _132203) : (term82 _132203 P) = (term83 _132203 P).
Proof. exact (@lem18392 (_132203 -> Prop) P). Qed.
Lemma lem7073645 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term84 _132203 f g) = (term85 _132203 f g).
Proof. exact (@lem7073644 _132203 (term65 _132203 f g)). Qed.
Lemma lem7073646 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term86 _132203 f g s) = (term64 _132203 f s g).
Proof. exact (eq_refl (term86 _132203 f g s)). Qed.
Lemma lem7073647 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7073648 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term87 _132203 f g s) = (term81 _132203 f s g).
Proof. exact (MK_COMB (@lem7073647) (@lem7073646 _132203 f s g)). Qed.
Lemma lem7073649 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term87 _132203 f g s) = (term80 _132203 f s g).
Proof. exact (TRANS (@lem7073648 _132203 f s g) (@lem7073643 _132203 f s g)). Qed.
Lemma lem7073650 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term88 _132203 f g) = (term89 _132203 f g).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7073649 _132203 f s g)). Qed.
Lemma lem7073651 {_132203 : Type'} : (@ex (_132203 -> Prop)) = (@ex (_132203 -> Prop)).
Proof. exact (eq_refl (@ex (_132203 -> Prop))). Qed.
Lemma lem7073652 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term85 _132203 f g) = (term90 _132203 f g).
Proof. exact (MK_COMB (@lem7073651 _132203) (@lem7073650 _132203 f g)). Qed.
Lemma lem7073653 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term84 _132203 f g) = (term90 _132203 f g).
Proof. exact (TRANS (@lem7073645 _132203 f g) (@lem7073652 _132203 f g)). Qed.
Lemma lem7073654 {_132203 : Type'} (P : type716 _132203) : (term91 _132203 P) = (term92 _132203 P).
Proof. exact (@lem18392 (_132203 -> real) P). Qed.
Lemma lem7073655 {_132203 : Type'} (f : _132203 -> real) : (term93 _132203 f) = (term94 _132203 f).
Proof. exact (@lem7073654 _132203 (term67 _132203 f)). Qed.
Lemma lem7073656 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term95 _132203 f g) = (term66 _132203 f g).
Proof. exact (eq_refl (term95 _132203 f g)). Qed.
Lemma lem7073657 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7073658 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term96 _132203 f g) = (term84 _132203 f g).
Proof. exact (MK_COMB (@lem7073657) (@lem7073656 _132203 f g)). Qed.
Lemma lem7073659 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term96 _132203 f g) = (term90 _132203 f g).
Proof. exact (TRANS (@lem7073658 _132203 f g) (@lem7073653 _132203 f g)). Qed.
Lemma lem7073660 {_132203 : Type'} (f : _132203 -> real) : (term97 _132203 f) = (term98 _132203 f).
Proof. exact (fun_ext (fun g : _132203 -> real => @lem7073659 _132203 f g)). Qed.
Lemma lem7073661 {_132203 : Type'} : (@ex (_132203 -> real)) = (@ex (_132203 -> real)).
Proof. exact (eq_refl (@ex (_132203 -> real))). Qed.
Lemma lem7073662 {_132203 : Type'} (f : _132203 -> real) : (term94 _132203 f) = (term99 _132203 f).
Proof. exact (MK_COMB (@lem7073661 _132203) (@lem7073660 _132203 f)). Qed.
Lemma lem7073663 {_132203 : Type'} (f : _132203 -> real) : (term93 _132203 f) = (term99 _132203 f).
Proof. exact (TRANS (@lem7073655 _132203 f) (@lem7073662 _132203 f)). Qed.
Lemma lem7073664 {_132203 : Type'} (P : type716 _132203) : (term91 _132203 P) = (term92 _132203 P).
Proof. exact (@lem18392 (_132203 -> real) P). Qed.
Lemma lem7073665 {_132203 : Type'} : (term10 _132203) = (term100 _132203).
Proof. exact (@lem7073664 _132203 (term69 _132203)). Qed.
Lemma lem7073666 {_132203 : Type'} (f : _132203 -> real) : (term101 _132203 f) = (term68 _132203 f).
Proof. exact (eq_refl (term101 _132203 f)). Qed.
Lemma lem7073667 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7073668 {_132203 : Type'} (f : _132203 -> real) : (term102 _132203 f) = (term93 _132203 f).
Proof. exact (MK_COMB (@lem7073667) (@lem7073666 _132203 f)). Qed.
Lemma lem7073669 {_132203 : Type'} (f : _132203 -> real) : (term102 _132203 f) = (term99 _132203 f).
Proof. exact (TRANS (@lem7073668 _132203 f) (@lem7073663 _132203 f)). Qed.
Lemma lem7073670 {_132203 : Type'} : (term103 _132203) = (term104 _132203).
Proof. exact (fun_ext (fun f : _132203 -> real => @lem7073669 _132203 f)). Qed.
Lemma lem7073671 {_132203 : Type'} : (@ex (_132203 -> real)) = (@ex (_132203 -> real)).
Proof. exact (eq_refl (@ex (_132203 -> real))). Qed.
Lemma lem7073672 {_132203 : Type'} : (term100 _132203) = (term105 _132203).
Proof. exact (MK_COMB (@lem7073671 _132203) (@lem7073670 _132203)). Qed.
Lemma lem7073781 {_132203 : Type'} : (term10 _132203) = (term105 _132203).
Proof. exact (TRANS (@lem7073665 _132203) (@lem7073672 _132203)). Qed.
Lemma lem7073782 {_132203 : Type'} (h1 : term10 _132203) : term105 _132203.
Proof. exact (EQ_MP (@lem7073781 _132203) (@lem7073615 _132203 h1)). Qed.
Lemma lem7073790 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term106 _132203 s f g x) = (term107 _132203 s f g x).
Proof. exact (@lem17362 (@IN _132203 x s) (term108 _132203 f g x)). Qed.
Lemma lem7073791 {_132203 : Type'} (P : _132203 -> Prop) : (term109 _132203 P) = (term110 _132203 P).
Proof. exact (@lem18392 _132203 P). Qed.
Lemma lem7073792 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term111 _132203 s f g) = (term112 _132203 s f g).
Proof. exact (@lem7073791 _132203 (term44 _132203 s f g)). Qed.
Lemma lem7073793 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term113 _132203 s f g x) = (term43 _132203 s f g x).
Proof. exact (eq_refl (term113 _132203 s f g x)). Qed.
Lemma lem7073794 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7073795 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term114 _132203 s f g x) = (term106 _132203 s f g x).
Proof. exact (MK_COMB (@lem7073794) (@lem7073793 _132203 s f g x)). Qed.
Lemma lem7073796 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term114 _132203 s f g x) = (term107 _132203 s f g x).
Proof. exact (TRANS (@lem7073795 _132203 s f g x) (@lem7073790 _132203 s f g x)). Qed.
Lemma lem7073797 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term115 _132203 s f g) = (term116 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7073796 _132203 s f g x)). Qed.
Lemma lem7073798 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7073799 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term112 _132203 s f g) = (term117 _132203 s f g).
Proof. exact (MK_COMB (@lem7073798 _132203) (@lem7073797 _132203 s f g)). Qed.
Lemma lem7073800 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term111 _132203 s f g) = (term117 _132203 s f g).
Proof. exact (TRANS (@lem7073792 _132203 s f g) (@lem7073799 _132203 s f g)). Qed.
Lemma lem7073807 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term118 _132203 s f g x) = (term119 _132203 s f g x).
Proof. exact (@lem17045 (@IN _132203 x s) (term71 _132203 f g x)). Qed.
Lemma lem7073808 {_132203 : Type'} (P : _132203 -> Prop) : (term120 _132203 P) = (term121 _132203 P).
Proof. exact (@lem18394 _132203 P). Qed.
Lemma lem7073809 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term122 _132203 s f g) = (term123 _132203 s f g).
Proof. exact (@lem7073808 _132203 (term41 _132203 s f g)). Qed.
Lemma lem7073810 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term124 _132203 s f g x) = (term40 _132203 s f g x).
Proof. exact (eq_refl (term124 _132203 s f g x)). Qed.
Lemma lem7073811 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7073812 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term125 _132203 s f g x) = (term118 _132203 s f g x).
Proof. exact (MK_COMB (@lem7073811) (@lem7073810 _132203 s f g x)). Qed.
Lemma lem7073813 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term125 _132203 s f g x) = (term119 _132203 s f g x).
Proof. exact (TRANS (@lem7073812 _132203 s f g x) (@lem7073807 _132203 s f g x)). Qed.
Lemma lem7073814 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term126 _132203 s f g) = (term127 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7073813 _132203 s f g x)). Qed.
Lemma lem7073815 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7073816 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term123 _132203 s f g) = (term128 _132203 s f g).
Proof. exact (MK_COMB (@lem7073815 _132203) (@lem7073814 _132203 s f g)). Qed.
Lemma lem7073817 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term122 _132203 s f g) = (term128 _132203 s f g).
Proof. exact (TRANS (@lem7073809 _132203 s f g) (@lem7073816 _132203 s f g)). Qed.
Lemma lem7073818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7073819 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term129 _132203 s f g) = (term130 _132203 s f g).
Proof. exact (MK_COMB (@lem7073818) (@lem7073800 _132203 s f g)). Qed.
Lemma lem7073820 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term131 _132203 s f g) = (term132 _132203 s f g).
Proof. exact (MK_COMB (@lem7073819 _132203 s f g) (@lem7073817 _132203 s f g)). Qed.
Lemma lem7073821 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term133 _132203 s f g) = (term131 _132203 s f g).
Proof. exact (@lem17045 (term45 _132203 s f g) (term42 _132203 s f g)). Qed.
Lemma lem7073822 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term133 _132203 s f g) = (term132 _132203 s f g).
Proof. exact (TRANS (@lem7073821 _132203 s f g) (@lem7073820 _132203 s f g)). Qed.
Lemma lem7073824 {_132203 : Type'} (s : _132203 -> Prop) : (term134 _132203 s) = (term134 _132203 s).
Proof. exact (eq_refl (term134 _132203 s)). Qed.
Lemma lem7073825 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term135 _132203 s f g) = (term136 _132203 s f g).
Proof. exact (MK_COMB (@lem7073824 _132203 s) (@lem7073822 _132203 s f g)). Qed.
Lemma lem7073826 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term137 _132203 s f g) = (term135 _132203 s f g).
Proof. exact (@lem17045 (@FINITE _132203 s) (term47 _132203 s f g)). Qed.
Lemma lem7073827 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term137 _132203 s f g) = (term136 _132203 s f g).
Proof. exact (TRANS (@lem7073826 _132203 s f g) (@lem7073825 _132203 s f g)). Qed.
Lemma lem7073828 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term39 _132203 f s g) = (term39 _132203 f s g).
Proof. exact (eq_refl (term39 _132203 f s g)). Qed.
Lemma lem7073829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7073830 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term138 _132203 s f g) = (term139 _132203 s f g).
Proof. exact (MK_COMB (@lem7073829) (@lem7073827 _132203 s f g)). Qed.
Lemma lem7073831 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term140 _132203 f s g) = (term141 _132203 f s g).
Proof. exact (MK_COMB (@lem7073830 _132203 s f g) (@lem7073828 _132203 f s g)). Qed.
Lemma lem7073832 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term51 _132203 f s g) = (term140 _132203 f s g).
Proof. exact (@lem17265 (term49 _132203 s f g) (term39 _132203 f s g)). Qed.
Lemma lem7073833 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term51 _132203 f s g) = (term141 _132203 f s g).
Proof. exact (TRANS (@lem7073832 _132203 f s g) (@lem7073831 _132203 f s g)). Qed.
Lemma lem7073834 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term52 _132203 f g) = (term142 _132203 f g).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7073833 _132203 f s g)). Qed.
Lemma lem7073835 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7073836 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term53 _132203 f g) = (term143 _132203 f g).
Proof. exact (MK_COMB (@lem7073835 _132203) (@lem7073834 _132203 f g)). Qed.
Lemma lem7073837 {_132203 : Type'} (f : _132203 -> real) : (term54 _132203 f) = (term144 _132203 f).
Proof. exact (fun_ext (fun g : _132203 -> real => @lem7073836 _132203 f g)). Qed.
Lemma lem7073838 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7073839 {_132203 : Type'} (f : _132203 -> real) : (term55 _132203 f) = (term145 _132203 f).
Proof. exact (MK_COMB (@lem7073838 _132203) (@lem7073837 _132203 f)). Qed.
Lemma lem7073840 {_132203 : Type'} : (term56 _132203) = (term146 _132203).
Proof. exact (fun_ext (fun f : _132203 -> real => @lem7073839 _132203 f)). Qed.
Lemma lem7073841 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7073842 {_132203 : Type'} : (term12 _132203) = (term147 _132203).
Proof. exact (MK_COMB (@lem7073841 _132203) (@lem7073840 _132203)). Qed.
Lemma lem7073997 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7073998 {_132203 : Type'} (P : _132203 -> Prop) (Q : Prop) : (term148 _132203 P Q) = (term149 _132203 P Q).
Proof. exact (@lem7073997 _132203 P Q). Qed.
Lemma lem7073999 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term150 _132203 s f g) = (term151 _132203 s f g).
Proof. exact (@lem7073998 _132203 (term116 _132203 s f g) (term128 _132203 s f g)). Qed.
Lemma lem7074000 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term152 _132203 s f g x) = (term107 _132203 s f g x).
Proof. exact (eq_refl (term152 _132203 s f g x)). Qed.
Lemma lem7074001 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term153 _132203 s f g) = (term116 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7074000 _132203 s f g x)). Qed.
Lemma lem7074002 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7074003 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term154 _132203 s f g) = (term117 _132203 s f g).
Proof. exact (MK_COMB (@lem7074002 _132203) (@lem7074001 _132203 s f g)). Qed.
Lemma lem7074004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074005 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term155 _132203 s f g) = (term130 _132203 s f g).
Proof. exact (MK_COMB (@lem7074004) (@lem7074003 _132203 s f g)). Qed.
Lemma lem7074006 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term128 _132203 s f g) = (term128 _132203 s f g).
Proof. exact (eq_refl (term128 _132203 s f g)). Qed.
Lemma lem7074007 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term150 _132203 s f g) = (term132 _132203 s f g).
Proof. exact (MK_COMB (@lem7074005 _132203 s f g) (@lem7074006 _132203 s f g)). Qed.
Lemma lem7074008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074009 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term156 _132203 s f g) = (term157 _132203 s f g).
Proof. exact (MK_COMB (@lem7074008) (@lem7074007 _132203 s f g)). Qed.
Lemma lem7074010 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term152 _132203 s f g x) = (term107 _132203 s f g x).
Proof. exact (eq_refl (term152 _132203 s f g x)). Qed.
Lemma lem7074011 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074012 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term158 _132203 s f g x) = (term159 _132203 s f g x).
Proof. exact (MK_COMB (@lem7074011) (@lem7074010 _132203 s f g x)). Qed.
Lemma lem7074013 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term128 _132203 s f g) = (term128 _132203 s f g).
Proof. exact (eq_refl (term128 _132203 s f g)). Qed.
Lemma lem7074014 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term160 _132203 x s f g) = (term161 _132203 x s f g).
Proof. exact (MK_COMB (@lem7074012 _132203 s f g x) (@lem7074013 _132203 s f g)). Qed.
Lemma lem7074015 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term162 _132203 s f g) = (term163 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7074014 _132203 x s f g)). Qed.
Lemma lem7074016 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7074017 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term151 _132203 s f g) = (term164 _132203 s f g).
Proof. exact (MK_COMB (@lem7074016 _132203) (@lem7074015 _132203 s f g)). Qed.
Lemma lem7074018 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : ((term150 _132203 s f g) = (term151 _132203 s f g)) = ((term132 _132203 s f g) = (term164 _132203 s f g)).
Proof. exact (MK_COMB (@lem7074009 _132203 s f g) (@lem7074017 _132203 s f g)). Qed.
Lemma lem7074019 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term132 _132203 s f g) = (term164 _132203 s f g).
Proof. exact (EQ_MP (@lem7074018 _132203 s f g) (@lem7073999 _132203 s f g)). Qed.
Lemma lem7074020 {_132203 : Type'} (s : _132203 -> Prop) : (term134 _132203 s) = (term134 _132203 s).
Proof. exact (eq_refl (term134 _132203 s)). Qed.
Lemma lem7074021 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term136 _132203 s f g) = (term165 _132203 s f g).
Proof. exact (MK_COMB (@lem7074020 _132203 s) (@lem7074019 _132203 s f g)). Qed.
Lemma lem7074023 {A : Type'} (P : Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7074024 {_132203 : Type'} (P : Prop) (Q : _132203 -> Prop) : (term166 _132203 P Q) = (term167 _132203 P Q).
Proof. exact (@lem7074023 _132203 P Q). Qed.
Lemma lem7074025 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term168 _132203 s f g) = (term169 _132203 s f g).
Proof. exact (@lem7074024 _132203 (term170 _132203 s) (term163 _132203 s f g)). Qed.
Lemma lem7074026 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term171 _132203 s f g x) = (term161 _132203 x s f g).
Proof. exact (eq_refl (term171 _132203 s f g x)). Qed.
Lemma lem7074027 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term172 _132203 s f g) = (term163 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7074026 _132203 x s f g)). Qed.
Lemma lem7074028 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7074029 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term173 _132203 s f g) = (term164 _132203 s f g).
Proof. exact (MK_COMB (@lem7074028 _132203) (@lem7074027 _132203 s f g)). Qed.
Lemma lem7074030 {_132203 : Type'} (s : _132203 -> Prop) : (term134 _132203 s) = (term134 _132203 s).
Proof. exact (eq_refl (term134 _132203 s)). Qed.
Lemma lem7074031 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term168 _132203 s f g) = (term165 _132203 s f g).
Proof. exact (MK_COMB (@lem7074030 _132203 s) (@lem7074029 _132203 s f g)). Qed.
Lemma lem7074032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074033 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term174 _132203 s f g) = (term175 _132203 s f g).
Proof. exact (MK_COMB (@lem7074032) (@lem7074031 _132203 s f g)). Qed.
Lemma lem7074034 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term171 _132203 s f g x) = (term161 _132203 x s f g).
Proof. exact (eq_refl (term171 _132203 s f g x)). Qed.
Lemma lem7074035 {_132203 : Type'} (s : _132203 -> Prop) : (term134 _132203 s) = (term134 _132203 s).
Proof. exact (eq_refl (term134 _132203 s)). Qed.
Lemma lem7074036 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term176 _132203 s f g x) = (term177 _132203 x s f g).
Proof. exact (MK_COMB (@lem7074035 _132203 s) (@lem7074034 _132203 x s f g)). Qed.
Lemma lem7074037 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term178 _132203 s f g) = (term179 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7074036 _132203 x s f g)). Qed.
Lemma lem7074038 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7074039 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term169 _132203 s f g) = (term180 _132203 s f g).
Proof. exact (MK_COMB (@lem7074038 _132203) (@lem7074037 _132203 s f g)). Qed.
Lemma lem7074040 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : ((term168 _132203 s f g) = (term169 _132203 s f g)) = ((term165 _132203 s f g) = (term180 _132203 s f g)).
Proof. exact (MK_COMB (@lem7074033 _132203 s f g) (@lem7074039 _132203 s f g)). Qed.
Lemma lem7074041 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term165 _132203 s f g) = (term180 _132203 s f g).
Proof. exact (EQ_MP (@lem7074040 _132203 s f g) (@lem7074025 _132203 s f g)). Qed.
Lemma lem7074042 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term136 _132203 s f g) = (term180 _132203 s f g).
Proof. exact (TRANS (@lem7074021 _132203 s f g) (@lem7074041 _132203 s f g)). Qed.
Lemma lem7074043 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074044 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term139 _132203 s f g) = (term181 _132203 s f g).
Proof. exact (MK_COMB (@lem7074043) (@lem7074042 _132203 s f g)). Qed.
Lemma lem7074045 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term39 _132203 f s g) = (term39 _132203 f s g).
Proof. exact (eq_refl (term39 _132203 f s g)). Qed.
Lemma lem7074046 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term141 _132203 f s g) = (term182 _132203 f s g).
Proof. exact (MK_COMB (@lem7074044 _132203 s f g) (@lem7074045 _132203 f s g)). Qed.
Lemma lem7074048 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7074049 {_132203 : Type'} (P : _132203 -> Prop) (Q : Prop) : (term148 _132203 P Q) = (term149 _132203 P Q).
Proof. exact (@lem7074048 _132203 P Q). Qed.
Lemma lem7074050 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term183 _132203 f s g) = (term184 _132203 f s g).
Proof. exact (@lem7074049 _132203 (term179 _132203 s f g) (term39 _132203 f s g)). Qed.
Lemma lem7074051 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term185 _132203 s f g x) = (term177 _132203 x s f g).
Proof. exact (eq_refl (term185 _132203 s f g x)). Qed.
Lemma lem7074052 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term186 _132203 s f g) = (term179 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7074051 _132203 x s f g)). Qed.
Lemma lem7074053 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7074054 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term187 _132203 s f g) = (term180 _132203 s f g).
Proof. exact (MK_COMB (@lem7074053 _132203) (@lem7074052 _132203 s f g)). Qed.
Lemma lem7074055 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074056 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term188 _132203 s f g) = (term181 _132203 s f g).
Proof. exact (MK_COMB (@lem7074055) (@lem7074054 _132203 s f g)). Qed.
Lemma lem7074057 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term39 _132203 f s g) = (term39 _132203 f s g).
Proof. exact (eq_refl (term39 _132203 f s g)). Qed.
Lemma lem7074058 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term183 _132203 f s g) = (term182 _132203 f s g).
Proof. exact (MK_COMB (@lem7074056 _132203 s f g) (@lem7074057 _132203 f s g)). Qed.
Lemma lem7074059 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074060 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term189 _132203 f s g) = (term190 _132203 f s g).
Proof. exact (MK_COMB (@lem7074059) (@lem7074058 _132203 f s g)). Qed.
Lemma lem7074061 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term185 _132203 s f g x) = (term177 _132203 x s f g).
Proof. exact (eq_refl (term185 _132203 s f g x)). Qed.
Lemma lem7074062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074063 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term191 _132203 s f g x) = (term192 _132203 x s f g).
Proof. exact (MK_COMB (@lem7074062) (@lem7074061 _132203 x s f g)). Qed.
Lemma lem7074064 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term39 _132203 f s g) = (term39 _132203 f s g).
Proof. exact (eq_refl (term39 _132203 f s g)). Qed.
Lemma lem7074065 {_132203 : Type'} (x : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term193 _132203 x f s g) = (term194 _132203 x f s g).
Proof. exact (MK_COMB (@lem7074063 _132203 x s f g) (@lem7074064 _132203 f s g)). Qed.
Lemma lem7074066 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term195 _132203 f s g) = (term196 _132203 f s g).
Proof. exact (fun_ext (fun x : _132203 => @lem7074065 _132203 x f s g)). Qed.
Lemma lem7074067 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7074068 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term184 _132203 f s g) = (term197 _132203 f s g).
Proof. exact (MK_COMB (@lem7074067 _132203) (@lem7074066 _132203 f s g)). Qed.
Lemma lem7074069 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : ((term183 _132203 f s g) = (term184 _132203 f s g)) = ((term182 _132203 f s g) = (term197 _132203 f s g)).
Proof. exact (MK_COMB (@lem7074060 _132203 f s g) (@lem7074068 _132203 f s g)). Qed.
Lemma lem7074070 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term182 _132203 f s g) = (term197 _132203 f s g).
Proof. exact (EQ_MP (@lem7074069 _132203 f s g) (@lem7074050 _132203 f s g)). Qed.
Lemma lem7074071 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term141 _132203 f s g) = (term197 _132203 f s g).
Proof. exact (TRANS (@lem7074046 _132203 f s g) (@lem7074070 _132203 f s g)). Qed.
Lemma lem7074072 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term142 _132203 f g) = (term198 _132203 f g).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7074071 _132203 f s g)). Qed.
Lemma lem7074073 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7074074 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term143 _132203 f g) = (term199 _132203 f g).
Proof. exact (MK_COMB (@lem7074073 _132203) (@lem7074072 _132203 f g)). Qed.
Lemma lem7074076 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7074077 {_132203 : Type'} (P : type672 _132203) : (term202 _132203 P) = (term203 _132203 P).
Proof. exact (@lem7074076 (_132203 -> Prop) _132203 P). Qed.
Lemma lem7074078 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term204 _132203 f g) = (term205 _132203 f g).
Proof. exact (@lem7074077 _132203 (term206 _132203 f g)). Qed.
Lemma lem7074079 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term207 _132203 f g s) = (term196 _132203 f s g).
Proof. exact (eq_refl (term207 _132203 f g s)). Qed.
Lemma lem7074080 {_132203 : Type'} (x : _132203) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7074081 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (x : _132203) : (term208 _132203 f g s x) = (term209 _132203 f s g x).
Proof. exact (MK_COMB (@lem7074079 _132203 f s g) (@lem7074080 _132203 x)). Qed.
Lemma lem7074082 {_132203 : Type'} (x : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term209 _132203 f s g x) = (term194 _132203 x f s g).
Proof. exact (eq_refl (term209 _132203 f s g x)). Qed.
Lemma lem7074083 {_132203 : Type'} (x : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term208 _132203 f g s x) = (term194 _132203 x f s g).
Proof. exact (TRANS (@lem7074081 _132203 f s g x) (@lem7074082 _132203 x f s g)). Qed.
Lemma lem7074084 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term210 _132203 f g s) = (term196 _132203 f s g).
Proof. exact (fun_ext (fun x : _132203 => @lem7074083 _132203 x f s g)). Qed.
Lemma lem7074085 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7074086 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term211 _132203 f g s) = (term197 _132203 f s g).
Proof. exact (MK_COMB (@lem7074085 _132203) (@lem7074084 _132203 f s g)). Qed.
Lemma lem7074087 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term212 _132203 f g) = (term198 _132203 f g).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7074086 _132203 f s g)). Qed.
Lemma lem7074088 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7074089 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term204 _132203 f g) = (term199 _132203 f g).
Proof. exact (MK_COMB (@lem7074088 _132203) (@lem7074087 _132203 f g)). Qed.
Lemma lem7074090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074091 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term213 _132203 f g) = (term214 _132203 f g).
Proof. exact (MK_COMB (@lem7074090) (@lem7074089 _132203 f g)). Qed.
Lemma lem7074092 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term207 _132203 f g s) = (term196 _132203 f s g).
Proof. exact (eq_refl (term207 _132203 f g s)). Qed.
Lemma lem7074093 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7074094 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : type684 _132203) (s : _132203 -> Prop) : (term215 _132203 f g x s) = (term216 _132203 f g x s).
Proof. exact (MK_COMB (@lem7074092 _132203 f s g) (@lem7074093 _132203 x s)). Qed.
Lemma lem7074095 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term216 _132203 f g x s) = (term217 _132203 x f s g).
Proof. exact (eq_refl (term216 _132203 f g x s)). Qed.
Lemma lem7074096 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term215 _132203 f g x s) = (term217 _132203 x f s g).
Proof. exact (TRANS (@lem7074094 _132203 f g x s) (@lem7074095 _132203 x f s g)). Qed.
Lemma lem7074097 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (g : _132203 -> real) : (term218 _132203 f g x) = (term219 _132203 x f g).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7074096 _132203 x f s g)). Qed.
Lemma lem7074098 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7074099 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (g : _132203 -> real) : (term220 _132203 f g x) = (term221 _132203 x f g).
Proof. exact (MK_COMB (@lem7074098 _132203) (@lem7074097 _132203 x f g)). Qed.
Lemma lem7074100 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term222 _132203 f g) = (term223 _132203 f g).
Proof. exact (fun_ext (fun x : type684 _132203 => @lem7074099 _132203 x f g)). Qed.
Lemma lem7074101 {_132203 : Type'} : (@ex ((_132203 -> Prop) -> _132203)) = (@ex ((_132203 -> Prop) -> _132203)).
Proof. exact (eq_refl (@ex ((_132203 -> Prop) -> _132203))). Qed.
Lemma lem7074102 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term205 _132203 f g) = (term224 _132203 f g).
Proof. exact (MK_COMB (@lem7074101 _132203) (@lem7074100 _132203 f g)). Qed.
Lemma lem7074103 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : ((term204 _132203 f g) = (term205 _132203 f g)) = ((term199 _132203 f g) = (term224 _132203 f g)).
Proof. exact (MK_COMB (@lem7074091 _132203 f g) (@lem7074102 _132203 f g)). Qed.
Lemma lem7074104 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term199 _132203 f g) = (term224 _132203 f g).
Proof. exact (EQ_MP (@lem7074103 _132203 f g) (@lem7074078 _132203 f g)). Qed.
Lemma lem7074105 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term143 _132203 f g) = (term224 _132203 f g).
Proof. exact (TRANS (@lem7074074 _132203 f g) (@lem7074104 _132203 f g)). Qed.
Lemma lem7074106 {_132203 : Type'} (f : _132203 -> real) : (term144 _132203 f) = (term225 _132203 f).
Proof. exact (fun_ext (fun g : _132203 -> real => @lem7074105 _132203 f g)). Qed.
Lemma lem7074107 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7074108 {_132203 : Type'} (f : _132203 -> real) : (term145 _132203 f) = (term226 _132203 f).
Proof. exact (MK_COMB (@lem7074107 _132203) (@lem7074106 _132203 f)). Qed.
Lemma lem7074110 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7074111 {_132203 : Type'} (P : type707 _132203) : (term227 _132203 P) = (term228 _132203 P).
Proof. exact (@lem7074110 (_132203 -> real) (type684 _132203) P). Qed.
Lemma lem7074112 {_132203 : Type'} (f : _132203 -> real) : (term229 _132203 f) = (term230 _132203 f).
Proof. exact (@lem7074111 _132203 (term231 _132203 f)). Qed.
Lemma lem7074113 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term232 _132203 f g) = (term223 _132203 f g).
Proof. exact (eq_refl (term232 _132203 f g)). Qed.
Lemma lem7074114 {_132203 : Type'} (x : type684 _132203) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7074115 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : type684 _132203) : (term233 _132203 f g x) = (term234 _132203 f g x).
Proof. exact (MK_COMB (@lem7074113 _132203 f g) (@lem7074114 _132203 x)). Qed.
Lemma lem7074116 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (g : _132203 -> real) : (term234 _132203 f g x) = (term221 _132203 x f g).
Proof. exact (eq_refl (term234 _132203 f g x)). Qed.
Lemma lem7074117 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (g : _132203 -> real) : (term233 _132203 f g x) = (term221 _132203 x f g).
Proof. exact (TRANS (@lem7074115 _132203 f g x) (@lem7074116 _132203 x f g)). Qed.
Lemma lem7074118 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term235 _132203 f g) = (term223 _132203 f g).
Proof. exact (fun_ext (fun x : type684 _132203 => @lem7074117 _132203 x f g)). Qed.
Lemma lem7074119 {_132203 : Type'} : (@ex ((_132203 -> Prop) -> _132203)) = (@ex ((_132203 -> Prop) -> _132203)).
Proof. exact (eq_refl (@ex ((_132203 -> Prop) -> _132203))). Qed.
Lemma lem7074120 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term236 _132203 f g) = (term224 _132203 f g).
Proof. exact (MK_COMB (@lem7074119 _132203) (@lem7074118 _132203 f g)). Qed.
Lemma lem7074121 {_132203 : Type'} (f : _132203 -> real) : (term237 _132203 f) = (term225 _132203 f).
Proof. exact (fun_ext (fun g : _132203 -> real => @lem7074120 _132203 f g)). Qed.
Lemma lem7074122 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7074123 {_132203 : Type'} (f : _132203 -> real) : (term229 _132203 f) = (term226 _132203 f).
Proof. exact (MK_COMB (@lem7074122 _132203) (@lem7074121 _132203 f)). Qed.
Lemma lem7074124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074125 {_132203 : Type'} (f : _132203 -> real) : (term238 _132203 f) = (term239 _132203 f).
Proof. exact (MK_COMB (@lem7074124) (@lem7074123 _132203 f)). Qed.
Lemma lem7074126 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) : (term232 _132203 f g) = (term223 _132203 f g).
Proof. exact (eq_refl (term232 _132203 f g)). Qed.
Lemma lem7074127 {_132203 : Type'} (x : type710 _132203) (g : _132203 -> real) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7074128 {_132203 : Type'} (f : _132203 -> real) (x : type710 _132203) (g : _132203 -> real) : (term240 _132203 f x g) = (term241 _132203 f x g).
Proof. exact (MK_COMB (@lem7074126 _132203 f g) (@lem7074127 _132203 x g)). Qed.
Lemma lem7074129 {_132203 : Type'} (x : type710 _132203) (f : _132203 -> real) (g : _132203 -> real) : (term241 _132203 f x g) = (term242 _132203 x f g).
Proof. exact (eq_refl (term241 _132203 f x g)). Qed.
Lemma lem7074130 {_132203 : Type'} (x : type710 _132203) (f : _132203 -> real) (g : _132203 -> real) : (term240 _132203 f x g) = (term242 _132203 x f g).
Proof. exact (TRANS (@lem7074128 _132203 f x g) (@lem7074129 _132203 x f g)). Qed.
Lemma lem7074131 {_132203 : Type'} (x : type710 _132203) (f : _132203 -> real) : (term243 _132203 f x) = (term244 _132203 x f).
Proof. exact (fun_ext (fun g : _132203 -> real => @lem7074130 _132203 x f g)). Qed.
Lemma lem7074132 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7074133 {_132203 : Type'} (x : type710 _132203) (f : _132203 -> real) : (term245 _132203 f x) = (term246 _132203 x f).
Proof. exact (MK_COMB (@lem7074132 _132203) (@lem7074131 _132203 x f)). Qed.
Lemma lem7074134 {_132203 : Type'} (f : _132203 -> real) : (term247 _132203 f) = (term248 _132203 f).
Proof. exact (fun_ext (fun x : type710 _132203 => @lem7074133 _132203 x f)). Qed.
Lemma lem7074135 {_132203 : Type'} : (@ex ((_132203 -> real) -> (_132203 -> Prop) -> _132203)) = (@ex ((_132203 -> real) -> (_132203 -> Prop) -> _132203)).
Proof. exact (eq_refl (@ex ((_132203 -> real) -> (_132203 -> Prop) -> _132203))). Qed.
Lemma lem7074136 {_132203 : Type'} (f : _132203 -> real) : (term230 _132203 f) = (term249 _132203 f).
Proof. exact (MK_COMB (@lem7074135 _132203) (@lem7074134 _132203 f)). Qed.
Lemma lem7074137 {_132203 : Type'} (f : _132203 -> real) : ((term229 _132203 f) = (term230 _132203 f)) = ((term226 _132203 f) = (term249 _132203 f)).
Proof. exact (MK_COMB (@lem7074125 _132203 f) (@lem7074136 _132203 f)). Qed.
Lemma lem7074138 {_132203 : Type'} (f : _132203 -> real) : (term226 _132203 f) = (term249 _132203 f).
Proof. exact (EQ_MP (@lem7074137 _132203 f) (@lem7074112 _132203 f)). Qed.
Lemma lem7074139 {_132203 : Type'} (f : _132203 -> real) : (term145 _132203 f) = (term249 _132203 f).
Proof. exact (TRANS (@lem7074108 _132203 f) (@lem7074138 _132203 f)). Qed.
Lemma lem7074140 {_132203 : Type'} : (term146 _132203) = (term250 _132203).
Proof. exact (fun_ext (fun f : _132203 -> real => @lem7074139 _132203 f)). Qed.
Lemma lem7074141 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7074142 {_132203 : Type'} : (term147 _132203) = (term251 _132203).
Proof. exact (MK_COMB (@lem7074141 _132203) (@lem7074140 _132203)). Qed.
Lemma lem7074144 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7074145 {_132203 : Type'} (P : type708 _132203) : (term252 _132203 P) = (term253 _132203 P).
Proof. exact (@lem7074144 (_132203 -> real) (type710 _132203) P). Qed.
Lemma lem7074146 {_132203 : Type'} : (term254 _132203) = (term255 _132203).
Proof. exact (@lem7074145 _132203 (term256 _132203)). Qed.
Lemma lem7074147 {_132203 : Type'} (f : _132203 -> real) : (term257 _132203 f) = (term248 _132203 f).
Proof. exact (eq_refl (term257 _132203 f)). Qed.
Lemma lem7074148 {_132203 : Type'} (x : type710 _132203) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7074149 {_132203 : Type'} (f : _132203 -> real) (x : type710 _132203) : (term258 _132203 f x) = (term259 _132203 f x).
Proof. exact (MK_COMB (@lem7074147 _132203 f) (@lem7074148 _132203 x)). Qed.
Lemma lem7074150 {_132203 : Type'} (x : type710 _132203) (f : _132203 -> real) : (term259 _132203 f x) = (term246 _132203 x f).
Proof. exact (eq_refl (term259 _132203 f x)). Qed.
Lemma lem7074151 {_132203 : Type'} (x : type710 _132203) (f : _132203 -> real) : (term258 _132203 f x) = (term246 _132203 x f).
Proof. exact (TRANS (@lem7074149 _132203 f x) (@lem7074150 _132203 x f)). Qed.
Lemma lem7074152 {_132203 : Type'} (f : _132203 -> real) : (term260 _132203 f) = (term248 _132203 f).
Proof. exact (fun_ext (fun x : type710 _132203 => @lem7074151 _132203 x f)). Qed.
Lemma lem7074153 {_132203 : Type'} : (@ex ((_132203 -> real) -> (_132203 -> Prop) -> _132203)) = (@ex ((_132203 -> real) -> (_132203 -> Prop) -> _132203)).
Proof. exact (eq_refl (@ex ((_132203 -> real) -> (_132203 -> Prop) -> _132203))). Qed.
Lemma lem7074154 {_132203 : Type'} (f : _132203 -> real) : (term261 _132203 f) = (term249 _132203 f).
Proof. exact (MK_COMB (@lem7074153 _132203) (@lem7074152 _132203 f)). Qed.
Lemma lem7074155 {_132203 : Type'} : (term262 _132203) = (term250 _132203).
Proof. exact (fun_ext (fun f : _132203 -> real => @lem7074154 _132203 f)). Qed.
Lemma lem7074156 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7074157 {_132203 : Type'} : (term254 _132203) = (term251 _132203).
Proof. exact (MK_COMB (@lem7074156 _132203) (@lem7074155 _132203)). Qed.
Lemma lem7074158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074159 {_132203 : Type'} : (term263 _132203) = (term264 _132203).
Proof. exact (MK_COMB (@lem7074158) (@lem7074157 _132203)). Qed.
Lemma lem7074160 {_132203 : Type'} (f : _132203 -> real) : (term257 _132203 f) = (term248 _132203 f).
Proof. exact (eq_refl (term257 _132203 f)). Qed.
Lemma lem7074161 {_132203 : Type'} (x : type711 _132203) (f : _132203 -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7074162 {_132203 : Type'} (x : type711 _132203) (f : _132203 -> real) : (term265 _132203 x f) = (term266 _132203 x f).
Proof. exact (MK_COMB (@lem7074160 _132203 f) (@lem7074161 _132203 x f)). Qed.
Lemma lem7074163 {_132203 : Type'} (x : type711 _132203) (f : _132203 -> real) : (term266 _132203 x f) = (term267 _132203 x f).
Proof. exact (eq_refl (term266 _132203 x f)). Qed.
Lemma lem7074164 {_132203 : Type'} (x : type711 _132203) (f : _132203 -> real) : (term265 _132203 x f) = (term267 _132203 x f).
Proof. exact (TRANS (@lem7074162 _132203 x f) (@lem7074163 _132203 x f)). Qed.
Lemma lem7074165 {_132203 : Type'} (x : type711 _132203) : (term268 _132203 x) = (term269 _132203 x).
Proof. exact (fun_ext (fun f : _132203 -> real => @lem7074164 _132203 x f)). Qed.
Lemma lem7074166 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7074167 {_132203 : Type'} (x : type711 _132203) : (term270 _132203 x) = (term271 _132203 x).
Proof. exact (MK_COMB (@lem7074166 _132203) (@lem7074165 _132203 x)). Qed.
Lemma lem7074168 {_132203 : Type'} : (term272 _132203) = (term273 _132203).
Proof. exact (fun_ext (fun x : type711 _132203 => @lem7074167 _132203 x)). Qed.
Lemma lem7074169 {_132203 : Type'} : (@ex ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203)) = (@ex ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203)).
Proof. exact (eq_refl (@ex ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203))). Qed.
Lemma lem7074170 {_132203 : Type'} : (term255 _132203) = (term274 _132203).
Proof. exact (MK_COMB (@lem7074169 _132203) (@lem7074168 _132203)). Qed.
Lemma lem7074171 {_132203 : Type'} : ((term254 _132203) = (term255 _132203)) = ((term251 _132203) = (term274 _132203)).
Proof. exact (MK_COMB (@lem7074159 _132203) (@lem7074170 _132203)). Qed.
Lemma lem7074172 {_132203 : Type'} : (term251 _132203) = (term274 _132203).
Proof. exact (EQ_MP (@lem7074171 _132203) (@lem7074146 _132203)). Qed.
Lemma lem7074174 {_132203 : Type'} : (term147 _132203) = (term274 _132203).
Proof. exact (TRANS (@lem7074142 _132203) (@lem7074172 _132203)). Qed.
Lemma lem7074175 {_132203 : Type'} : (term12 _132203) = (term274 _132203).
Proof. exact (TRANS (@lem7073842 _132203) (@lem7074174 _132203)). Qed.
Lemma lem7074176 {_132203 : Type'} (h1 : term12 _132203) : term274 _132203.
Proof. exact (EQ_MP (@lem7074175 _132203) (@lem7073616 _132203 h1)). Qed.
Lemma lem7074184 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term106 A s f g x) = (term107 A s f g x).
Proof. exact (@lem17362 (@IN A x s) (term108 A f g x)). Qed.
Lemma lem7074185 {A : Type'} (P : A -> Prop) : (term109 A P) = (term110 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7074186 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term111 A s f g) = (term112 A s f g).
Proof. exact (@lem7074185 A (term44 A s f g)). Qed.
Lemma lem7074187 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term113 A s f g x) = (term43 A s f g x).
Proof. exact (eq_refl (term113 A s f g x)). Qed.
Lemma lem7074188 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7074189 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term114 A s f g x) = (term106 A s f g x).
Proof. exact (MK_COMB (@lem7074188) (@lem7074187 A s f g x)). Qed.
Lemma lem7074190 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term114 A s f g x) = (term107 A s f g x).
Proof. exact (TRANS (@lem7074189 A s f g x) (@lem7074184 A s f g x)). Qed.
Lemma lem7074191 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term115 A s f g) = (term116 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7074190 A s f g x)). Qed.
Lemma lem7074192 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7074193 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term112 A s f g) = (term117 A s f g).
Proof. exact (MK_COMB (@lem7074192 A) (@lem7074191 A s f g)). Qed.
Lemma lem7074194 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term111 A s f g) = (term117 A s f g).
Proof. exact (TRANS (@lem7074186 A s f g) (@lem7074193 A s f g)). Qed.
Lemma lem7074201 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term118 A s f g x) = (term119 A s f g x).
Proof. exact (@lem17045 (@IN A x s) (term71 A f g x)). Qed.
Lemma lem7074202 {A : Type'} (P : A -> Prop) : (term120 A P) = (term121 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem7074203 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term122 A s f g) = (term123 A s f g).
Proof. exact (@lem7074202 A (term41 A s f g)). Qed.
Lemma lem7074204 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term124 A s f g x) = (term40 A s f g x).
Proof. exact (eq_refl (term124 A s f g x)). Qed.
Lemma lem7074205 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7074206 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term125 A s f g x) = (term118 A s f g x).
Proof. exact (MK_COMB (@lem7074205) (@lem7074204 A s f g x)). Qed.
Lemma lem7074207 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term125 A s f g x) = (term119 A s f g x).
Proof. exact (TRANS (@lem7074206 A s f g x) (@lem7074201 A s f g x)). Qed.
Lemma lem7074208 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term126 A s f g) = (term127 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7074207 A s f g x)). Qed.
Lemma lem7074209 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7074210 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term123 A s f g) = (term128 A s f g).
Proof. exact (MK_COMB (@lem7074209 A) (@lem7074208 A s f g)). Qed.
Lemma lem7074211 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term122 A s f g) = (term128 A s f g).
Proof. exact (TRANS (@lem7074203 A s f g) (@lem7074210 A s f g)). Qed.
Lemma lem7074212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074213 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term129 A s f g) = (term130 A s f g).
Proof. exact (MK_COMB (@lem7074212) (@lem7074194 A s f g)). Qed.
Lemma lem7074214 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term131 A s f g) = (term132 A s f g).
Proof. exact (MK_COMB (@lem7074213 A s f g) (@lem7074211 A s f g)). Qed.
Lemma lem7074215 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term133 A s f g) = (term131 A s f g).
Proof. exact (@lem17045 (term45 A s f g) (term42 A s f g)). Qed.
Lemma lem7074216 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term133 A s f g) = (term132 A s f g).
Proof. exact (TRANS (@lem7074215 A s f g) (@lem7074214 A s f g)). Qed.
Lemma lem7074218 {A : Type'} (s : A -> Prop) : (term134 A s) = (term134 A s).
Proof. exact (eq_refl (term134 A s)). Qed.
Lemma lem7074219 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term135 A s f g) = (term136 A s f g).
Proof. exact (MK_COMB (@lem7074218 A s) (@lem7074216 A s f g)). Qed.
Lemma lem7074220 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term137 A s f g) = (term135 A s f g).
Proof. exact (@lem17045 (@FINITE A s) (term47 A s f g)). Qed.
Lemma lem7074221 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term137 A s f g) = (term136 A s f g).
Proof. exact (TRANS (@lem7074220 A s f g) (@lem7074219 A s f g)). Qed.
Lemma lem7074222 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term39 A f s g) = (term39 A f s g).
Proof. exact (eq_refl (term39 A f s g)). Qed.
Lemma lem7074223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074224 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term138 A s f g) = (term139 A s f g).
Proof. exact (MK_COMB (@lem7074223) (@lem7074221 A s f g)). Qed.
Lemma lem7074225 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term140 A f s g) = (term141 A f s g).
Proof. exact (MK_COMB (@lem7074224 A s f g) (@lem7074222 A f s g)). Qed.
Lemma lem7074226 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term51 A f s g) = (term140 A f s g).
Proof. exact (@lem17265 (term49 A s f g) (term39 A f s g)). Qed.
Lemma lem7074227 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term51 A f s g) = (term141 A f s g).
Proof. exact (TRANS (@lem7074226 A f s g) (@lem7074225 A f s g)). Qed.
Lemma lem7074228 {A : Type'} (f : A -> real) (g : A -> real) : (term52 A f g) = (term142 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7074227 A f s g)). Qed.
Lemma lem7074229 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7074230 {A : Type'} (f : A -> real) (g : A -> real) : (term53 A f g) = (term143 A f g).
Proof. exact (MK_COMB (@lem7074229 A) (@lem7074228 A f g)). Qed.
Lemma lem7074231 {A : Type'} (f : A -> real) : (term54 A f) = (term144 A f).
Proof. exact (fun_ext (fun g : A -> real => @lem7074230 A f g)). Qed.
Lemma lem7074232 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7074233 {A : Type'} (f : A -> real) : (term55 A f) = (term145 A f).
Proof. exact (MK_COMB (@lem7074232 A) (@lem7074231 A f)). Qed.
Lemma lem7074234 {A : Type'} : (term56 A) = (term146 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7074233 A f)). Qed.
Lemma lem7074235 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7074236 {A : Type'} : (term12 A) = (term147 A).
Proof. exact (MK_COMB (@lem7074235 A) (@lem7074234 A)). Qed.
Lemma lem7074391 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7074392 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (@lem7074391 A P Q). Qed.
Lemma lem7074393 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term150 A s f g) = (term151 A s f g).
Proof. exact (@lem7074392 A (term116 A s f g) (term128 A s f g)). Qed.
Lemma lem7074394 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term152 A s f g x) = (term107 A s f g x).
Proof. exact (eq_refl (term152 A s f g x)). Qed.
Lemma lem7074395 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term153 A s f g) = (term116 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7074394 A s f g x)). Qed.
Lemma lem7074396 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7074397 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term154 A s f g) = (term117 A s f g).
Proof. exact (MK_COMB (@lem7074396 A) (@lem7074395 A s f g)). Qed.
Lemma lem7074398 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074399 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term155 A s f g) = (term130 A s f g).
Proof. exact (MK_COMB (@lem7074398) (@lem7074397 A s f g)). Qed.
Lemma lem7074400 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term128 A s f g) = (term128 A s f g).
Proof. exact (eq_refl (term128 A s f g)). Qed.
Lemma lem7074401 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term150 A s f g) = (term132 A s f g).
Proof. exact (MK_COMB (@lem7074399 A s f g) (@lem7074400 A s f g)). Qed.
Lemma lem7074402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074403 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term156 A s f g) = (term157 A s f g).
Proof. exact (MK_COMB (@lem7074402) (@lem7074401 A s f g)). Qed.
Lemma lem7074404 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term152 A s f g x) = (term107 A s f g x).
Proof. exact (eq_refl (term152 A s f g x)). Qed.
Lemma lem7074405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074406 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term158 A s f g x) = (term159 A s f g x).
Proof. exact (MK_COMB (@lem7074405) (@lem7074404 A s f g x)). Qed.
Lemma lem7074407 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term128 A s f g) = (term128 A s f g).
Proof. exact (eq_refl (term128 A s f g)). Qed.
Lemma lem7074408 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) : (term160 A x s f g) = (term161 A x s f g).
Proof. exact (MK_COMB (@lem7074406 A s f g x) (@lem7074407 A s f g)). Qed.
Lemma lem7074409 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term162 A s f g) = (term163 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7074408 A x s f g)). Qed.
Lemma lem7074410 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7074411 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term151 A s f g) = (term164 A s f g).
Proof. exact (MK_COMB (@lem7074410 A) (@lem7074409 A s f g)). Qed.
Lemma lem7074412 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : ((term150 A s f g) = (term151 A s f g)) = ((term132 A s f g) = (term164 A s f g)).
Proof. exact (MK_COMB (@lem7074403 A s f g) (@lem7074411 A s f g)). Qed.
Lemma lem7074413 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term132 A s f g) = (term164 A s f g).
Proof. exact (EQ_MP (@lem7074412 A s f g) (@lem7074393 A s f g)). Qed.
Lemma lem7074414 {A : Type'} (s : A -> Prop) : (term134 A s) = (term134 A s).
Proof. exact (eq_refl (term134 A s)). Qed.
Lemma lem7074415 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term136 A s f g) = (term165 A s f g).
Proof. exact (MK_COMB (@lem7074414 A s) (@lem7074413 A s f g)). Qed.
Lemma lem7074417 {A : Type'} (P : Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7074418 {A : Type'} (P : Prop) (Q : A -> Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (@lem7074417 A P Q). Qed.
Lemma lem7074419 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term168 A s f g) = (term169 A s f g).
Proof. exact (@lem7074418 A (term170 A s) (term163 A s f g)). Qed.
Lemma lem7074420 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) : (term171 A s f g x) = (term161 A x s f g).
Proof. exact (eq_refl (term171 A s f g x)). Qed.
Lemma lem7074421 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term172 A s f g) = (term163 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7074420 A x s f g)). Qed.
Lemma lem7074422 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7074423 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term173 A s f g) = (term164 A s f g).
Proof. exact (MK_COMB (@lem7074422 A) (@lem7074421 A s f g)). Qed.
Lemma lem7074424 {A : Type'} (s : A -> Prop) : (term134 A s) = (term134 A s).
Proof. exact (eq_refl (term134 A s)). Qed.
Lemma lem7074425 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term168 A s f g) = (term165 A s f g).
Proof. exact (MK_COMB (@lem7074424 A s) (@lem7074423 A s f g)). Qed.
Lemma lem7074426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074427 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term174 A s f g) = (term175 A s f g).
Proof. exact (MK_COMB (@lem7074426) (@lem7074425 A s f g)). Qed.
Lemma lem7074428 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) : (term171 A s f g x) = (term161 A x s f g).
Proof. exact (eq_refl (term171 A s f g x)). Qed.
Lemma lem7074429 {A : Type'} (s : A -> Prop) : (term134 A s) = (term134 A s).
Proof. exact (eq_refl (term134 A s)). Qed.
Lemma lem7074430 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) : (term176 A s f g x) = (term177 A x s f g).
Proof. exact (MK_COMB (@lem7074429 A s) (@lem7074428 A x s f g)). Qed.
Lemma lem7074431 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term178 A s f g) = (term179 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7074430 A x s f g)). Qed.
Lemma lem7074432 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7074433 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term169 A s f g) = (term180 A s f g).
Proof. exact (MK_COMB (@lem7074432 A) (@lem7074431 A s f g)). Qed.
Lemma lem7074434 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : ((term168 A s f g) = (term169 A s f g)) = ((term165 A s f g) = (term180 A s f g)).
Proof. exact (MK_COMB (@lem7074427 A s f g) (@lem7074433 A s f g)). Qed.
Lemma lem7074435 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term165 A s f g) = (term180 A s f g).
Proof. exact (EQ_MP (@lem7074434 A s f g) (@lem7074419 A s f g)). Qed.
Lemma lem7074436 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term136 A s f g) = (term180 A s f g).
Proof. exact (TRANS (@lem7074415 A s f g) (@lem7074435 A s f g)). Qed.
Lemma lem7074437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074438 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term139 A s f g) = (term181 A s f g).
Proof. exact (MK_COMB (@lem7074437) (@lem7074436 A s f g)). Qed.
Lemma lem7074439 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term39 A f s g) = (term39 A f s g).
Proof. exact (eq_refl (term39 A f s g)). Qed.
Lemma lem7074440 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term141 A f s g) = (term182 A f s g).
Proof. exact (MK_COMB (@lem7074438 A s f g) (@lem7074439 A f s g)). Qed.
Lemma lem7074442 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7074443 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (@lem7074442 A P Q). Qed.
Lemma lem7074444 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term183 A f s g) = (term184 A f s g).
Proof. exact (@lem7074443 A (term179 A s f g) (term39 A f s g)). Qed.
Lemma lem7074445 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) : (term185 A s f g x) = (term177 A x s f g).
Proof. exact (eq_refl (term185 A s f g x)). Qed.
Lemma lem7074446 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term186 A s f g) = (term179 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7074445 A x s f g)). Qed.
Lemma lem7074447 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7074448 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term187 A s f g) = (term180 A s f g).
Proof. exact (MK_COMB (@lem7074447 A) (@lem7074446 A s f g)). Qed.
Lemma lem7074449 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074450 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term188 A s f g) = (term181 A s f g).
Proof. exact (MK_COMB (@lem7074449) (@lem7074448 A s f g)). Qed.
Lemma lem7074451 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term39 A f s g) = (term39 A f s g).
Proof. exact (eq_refl (term39 A f s g)). Qed.
Lemma lem7074452 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term183 A f s g) = (term182 A f s g).
Proof. exact (MK_COMB (@lem7074450 A s f g) (@lem7074451 A f s g)). Qed.
Lemma lem7074453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074454 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term189 A f s g) = (term190 A f s g).
Proof. exact (MK_COMB (@lem7074453) (@lem7074452 A f s g)). Qed.
Lemma lem7074455 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) : (term185 A s f g x) = (term177 A x s f g).
Proof. exact (eq_refl (term185 A s f g x)). Qed.
Lemma lem7074456 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074457 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (g : A -> real) : (term191 A s f g x) = (term192 A x s f g).
Proof. exact (MK_COMB (@lem7074456) (@lem7074455 A x s f g)). Qed.
Lemma lem7074458 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term39 A f s g) = (term39 A f s g).
Proof. exact (eq_refl (term39 A f s g)). Qed.
Lemma lem7074459 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term193 A x f s g) = (term194 A x f s g).
Proof. exact (MK_COMB (@lem7074457 A x s f g) (@lem7074458 A f s g)). Qed.
Lemma lem7074460 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term195 A f s g) = (term196 A f s g).
Proof. exact (fun_ext (fun x : A => @lem7074459 A x f s g)). Qed.
Lemma lem7074461 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7074462 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term184 A f s g) = (term197 A f s g).
Proof. exact (MK_COMB (@lem7074461 A) (@lem7074460 A f s g)). Qed.
Lemma lem7074463 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : ((term183 A f s g) = (term184 A f s g)) = ((term182 A f s g) = (term197 A f s g)).
Proof. exact (MK_COMB (@lem7074454 A f s g) (@lem7074462 A f s g)). Qed.
Lemma lem7074464 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term182 A f s g) = (term197 A f s g).
Proof. exact (EQ_MP (@lem7074463 A f s g) (@lem7074444 A f s g)). Qed.
Lemma lem7074465 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term141 A f s g) = (term197 A f s g).
Proof. exact (TRANS (@lem7074440 A f s g) (@lem7074464 A f s g)). Qed.
Lemma lem7074466 {A : Type'} (f : A -> real) (g : A -> real) : (term142 A f g) = (term198 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7074465 A f s g)). Qed.
Lemma lem7074467 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7074468 {A : Type'} (f : A -> real) (g : A -> real) : (term143 A f g) = (term199 A f g).
Proof. exact (MK_COMB (@lem7074467 A) (@lem7074466 A f g)). Qed.
Lemma lem7074470 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7074471 {A : Type'} (P : type672 A) : (term202 A P) = (term203 A P).
Proof. exact (@lem7074470 (A -> Prop) A P). Qed.
Lemma lem7074472 {A : Type'} (f : A -> real) (g : A -> real) : (term204 A f g) = (term205 A f g).
Proof. exact (@lem7074471 A (term206 A f g)). Qed.
Lemma lem7074473 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term207 A f g s) = (term196 A f s g).
Proof. exact (eq_refl (term207 A f g s)). Qed.
Lemma lem7074474 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7074475 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (x : A) : (term208 A f g s x) = (term209 A f s g x).
Proof. exact (MK_COMB (@lem7074473 A f s g) (@lem7074474 A x)). Qed.
Lemma lem7074476 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term209 A f s g x) = (term194 A x f s g).
Proof. exact (eq_refl (term209 A f s g x)). Qed.
Lemma lem7074477 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term208 A f g s x) = (term194 A x f s g).
Proof. exact (TRANS (@lem7074475 A f s g x) (@lem7074476 A x f s g)). Qed.
Lemma lem7074478 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term210 A f g s) = (term196 A f s g).
Proof. exact (fun_ext (fun x : A => @lem7074477 A x f s g)). Qed.
Lemma lem7074479 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7074480 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term211 A f g s) = (term197 A f s g).
Proof. exact (MK_COMB (@lem7074479 A) (@lem7074478 A f s g)). Qed.
Lemma lem7074481 {A : Type'} (f : A -> real) (g : A -> real) : (term212 A f g) = (term198 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7074480 A f s g)). Qed.
Lemma lem7074482 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7074483 {A : Type'} (f : A -> real) (g : A -> real) : (term204 A f g) = (term199 A f g).
Proof. exact (MK_COMB (@lem7074482 A) (@lem7074481 A f g)). Qed.
Lemma lem7074484 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074485 {A : Type'} (f : A -> real) (g : A -> real) : (term213 A f g) = (term214 A f g).
Proof. exact (MK_COMB (@lem7074484) (@lem7074483 A f g)). Qed.
Lemma lem7074486 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term207 A f g s) = (term196 A f s g).
Proof. exact (eq_refl (term207 A f g s)). Qed.
Lemma lem7074487 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7074488 {A : Type'} (f : A -> real) (g : A -> real) (x : type684 A) (s : A -> Prop) : (term215 A f g x s) = (term216 A f g x s).
Proof. exact (MK_COMB (@lem7074486 A f s g) (@lem7074487 A x s)). Qed.
Lemma lem7074489 {A : Type'} (x : type684 A) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term216 A f g x s) = (term217 A x f s g).
Proof. exact (eq_refl (term216 A f g x s)). Qed.
Lemma lem7074490 {A : Type'} (x : type684 A) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term215 A f g x s) = (term217 A x f s g).
Proof. exact (TRANS (@lem7074488 A f g x s) (@lem7074489 A x f s g)). Qed.
Lemma lem7074491 {A : Type'} (x : type684 A) (f : A -> real) (g : A -> real) : (term218 A f g x) = (term219 A x f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7074490 A x f s g)). Qed.
Lemma lem7074492 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7074493 {A : Type'} (x : type684 A) (f : A -> real) (g : A -> real) : (term220 A f g x) = (term221 A x f g).
Proof. exact (MK_COMB (@lem7074492 A) (@lem7074491 A x f g)). Qed.
Lemma lem7074494 {A : Type'} (f : A -> real) (g : A -> real) : (term222 A f g) = (term223 A f g).
Proof. exact (fun_ext (fun x : type684 A => @lem7074493 A x f g)). Qed.
Lemma lem7074495 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7074496 {A : Type'} (f : A -> real) (g : A -> real) : (term205 A f g) = (term224 A f g).
Proof. exact (MK_COMB (@lem7074495 A) (@lem7074494 A f g)). Qed.
Lemma lem7074497 {A : Type'} (f : A -> real) (g : A -> real) : ((term204 A f g) = (term205 A f g)) = ((term199 A f g) = (term224 A f g)).
Proof. exact (MK_COMB (@lem7074485 A f g) (@lem7074496 A f g)). Qed.
Lemma lem7074498 {A : Type'} (f : A -> real) (g : A -> real) : (term199 A f g) = (term224 A f g).
Proof. exact (EQ_MP (@lem7074497 A f g) (@lem7074472 A f g)). Qed.
Lemma lem7074499 {A : Type'} (f : A -> real) (g : A -> real) : (term143 A f g) = (term224 A f g).
Proof. exact (TRANS (@lem7074468 A f g) (@lem7074498 A f g)). Qed.
Lemma lem7074500 {A : Type'} (f : A -> real) : (term144 A f) = (term225 A f).
Proof. exact (fun_ext (fun g : A -> real => @lem7074499 A f g)). Qed.
Lemma lem7074501 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7074502 {A : Type'} (f : A -> real) : (term145 A f) = (term226 A f).
Proof. exact (MK_COMB (@lem7074501 A) (@lem7074500 A f)). Qed.
Lemma lem7074504 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7074505 {A : Type'} (P : type707 A) : (term227 A P) = (term228 A P).
Proof. exact (@lem7074504 (A -> real) (type684 A) P). Qed.
Lemma lem7074506 {A : Type'} (f : A -> real) : (term229 A f) = (term230 A f).
Proof. exact (@lem7074505 A (term231 A f)). Qed.
Lemma lem7074507 {A : Type'} (f : A -> real) (g : A -> real) : (term232 A f g) = (term223 A f g).
Proof. exact (eq_refl (term232 A f g)). Qed.
Lemma lem7074508 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7074509 {A : Type'} (f : A -> real) (g : A -> real) (x : type684 A) : (term233 A f g x) = (term234 A f g x).
Proof. exact (MK_COMB (@lem7074507 A f g) (@lem7074508 A x)). Qed.
Lemma lem7074510 {A : Type'} (x : type684 A) (f : A -> real) (g : A -> real) : (term234 A f g x) = (term221 A x f g).
Proof. exact (eq_refl (term234 A f g x)). Qed.
Lemma lem7074511 {A : Type'} (x : type684 A) (f : A -> real) (g : A -> real) : (term233 A f g x) = (term221 A x f g).
Proof. exact (TRANS (@lem7074509 A f g x) (@lem7074510 A x f g)). Qed.
Lemma lem7074512 {A : Type'} (f : A -> real) (g : A -> real) : (term235 A f g) = (term223 A f g).
Proof. exact (fun_ext (fun x : type684 A => @lem7074511 A x f g)). Qed.
Lemma lem7074513 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7074514 {A : Type'} (f : A -> real) (g : A -> real) : (term236 A f g) = (term224 A f g).
Proof. exact (MK_COMB (@lem7074513 A) (@lem7074512 A f g)). Qed.
Lemma lem7074515 {A : Type'} (f : A -> real) : (term237 A f) = (term225 A f).
Proof. exact (fun_ext (fun g : A -> real => @lem7074514 A f g)). Qed.
Lemma lem7074516 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7074517 {A : Type'} (f : A -> real) : (term229 A f) = (term226 A f).
Proof. exact (MK_COMB (@lem7074516 A) (@lem7074515 A f)). Qed.
Lemma lem7074518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074519 {A : Type'} (f : A -> real) : (term238 A f) = (term239 A f).
Proof. exact (MK_COMB (@lem7074518) (@lem7074517 A f)). Qed.
Lemma lem7074520 {A : Type'} (f : A -> real) (g : A -> real) : (term232 A f g) = (term223 A f g).
Proof. exact (eq_refl (term232 A f g)). Qed.
Lemma lem7074521 {A : Type'} (x : type710 A) (g : A -> real) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7074522 {A : Type'} (f : A -> real) (x : type710 A) (g : A -> real) : (term240 A f x g) = (term241 A f x g).
Proof. exact (MK_COMB (@lem7074520 A f g) (@lem7074521 A x g)). Qed.
Lemma lem7074523 {A : Type'} (x : type710 A) (f : A -> real) (g : A -> real) : (term241 A f x g) = (term242 A x f g).
Proof. exact (eq_refl (term241 A f x g)). Qed.
Lemma lem7074524 {A : Type'} (x : type710 A) (f : A -> real) (g : A -> real) : (term240 A f x g) = (term242 A x f g).
Proof. exact (TRANS (@lem7074522 A f x g) (@lem7074523 A x f g)). Qed.
Lemma lem7074525 {A : Type'} (x : type710 A) (f : A -> real) : (term243 A f x) = (term244 A x f).
Proof. exact (fun_ext (fun g : A -> real => @lem7074524 A x f g)). Qed.
Lemma lem7074526 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7074527 {A : Type'} (x : type710 A) (f : A -> real) : (term245 A f x) = (term246 A x f).
Proof. exact (MK_COMB (@lem7074526 A) (@lem7074525 A x f)). Qed.
Lemma lem7074528 {A : Type'} (f : A -> real) : (term247 A f) = (term248 A f).
Proof. exact (fun_ext (fun x : type710 A => @lem7074527 A x f)). Qed.
Lemma lem7074529 {A : Type'} : (@ex ((A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7074530 {A : Type'} (f : A -> real) : (term230 A f) = (term249 A f).
Proof. exact (MK_COMB (@lem7074529 A) (@lem7074528 A f)). Qed.
Lemma lem7074531 {A : Type'} (f : A -> real) : ((term229 A f) = (term230 A f)) = ((term226 A f) = (term249 A f)).
Proof. exact (MK_COMB (@lem7074519 A f) (@lem7074530 A f)). Qed.
Lemma lem7074532 {A : Type'} (f : A -> real) : (term226 A f) = (term249 A f).
Proof. exact (EQ_MP (@lem7074531 A f) (@lem7074506 A f)). Qed.
Lemma lem7074533 {A : Type'} (f : A -> real) : (term145 A f) = (term249 A f).
Proof. exact (TRANS (@lem7074502 A f) (@lem7074532 A f)). Qed.
Lemma lem7074534 {A : Type'} : (term146 A) = (term250 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7074533 A f)). Qed.
Lemma lem7074535 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7074536 {A : Type'} : (term147 A) = (term251 A).
Proof. exact (MK_COMB (@lem7074535 A) (@lem7074534 A)). Qed.
Lemma lem7074538 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7074539 {A : Type'} (P : type708 A) : (term252 A P) = (term253 A P).
Proof. exact (@lem7074538 (A -> real) (type710 A) P). Qed.
Lemma lem7074540 {A : Type'} : (term254 A) = (term255 A).
Proof. exact (@lem7074539 A (term256 A)). Qed.
Lemma lem7074541 {A : Type'} (f : A -> real) : (term257 A f) = (term248 A f).
Proof. exact (eq_refl (term257 A f)). Qed.
Lemma lem7074542 {A : Type'} (x : type710 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7074543 {A : Type'} (f : A -> real) (x : type710 A) : (term258 A f x) = (term259 A f x).
Proof. exact (MK_COMB (@lem7074541 A f) (@lem7074542 A x)). Qed.
Lemma lem7074544 {A : Type'} (x : type710 A) (f : A -> real) : (term259 A f x) = (term246 A x f).
Proof. exact (eq_refl (term259 A f x)). Qed.
Lemma lem7074545 {A : Type'} (x : type710 A) (f : A -> real) : (term258 A f x) = (term246 A x f).
Proof. exact (TRANS (@lem7074543 A f x) (@lem7074544 A x f)). Qed.
Lemma lem7074546 {A : Type'} (f : A -> real) : (term260 A f) = (term248 A f).
Proof. exact (fun_ext (fun x : type710 A => @lem7074545 A x f)). Qed.
Lemma lem7074547 {A : Type'} : (@ex ((A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7074548 {A : Type'} (f : A -> real) : (term261 A f) = (term249 A f).
Proof. exact (MK_COMB (@lem7074547 A) (@lem7074546 A f)). Qed.
Lemma lem7074549 {A : Type'} : (term262 A) = (term250 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7074548 A f)). Qed.
Lemma lem7074550 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7074551 {A : Type'} : (term254 A) = (term251 A).
Proof. exact (MK_COMB (@lem7074550 A) (@lem7074549 A)). Qed.
Lemma lem7074552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074553 {A : Type'} : (term263 A) = (term264 A).
Proof. exact (MK_COMB (@lem7074552) (@lem7074551 A)). Qed.
Lemma lem7074554 {A : Type'} (f : A -> real) : (term257 A f) = (term248 A f).
Proof. exact (eq_refl (term257 A f)). Qed.
Lemma lem7074555 {A : Type'} (x : type711 A) (f : A -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7074556 {A : Type'} (x : type711 A) (f : A -> real) : (term265 A x f) = (term266 A x f).
Proof. exact (MK_COMB (@lem7074554 A f) (@lem7074555 A x f)). Qed.
Lemma lem7074557 {A : Type'} (x : type711 A) (f : A -> real) : (term266 A x f) = (term267 A x f).
Proof. exact (eq_refl (term266 A x f)). Qed.
Lemma lem7074558 {A : Type'} (x : type711 A) (f : A -> real) : (term265 A x f) = (term267 A x f).
Proof. exact (TRANS (@lem7074556 A x f) (@lem7074557 A x f)). Qed.
Lemma lem7074559 {A : Type'} (x : type711 A) : (term268 A x) = (term269 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7074558 A x f)). Qed.
Lemma lem7074560 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7074561 {A : Type'} (x : type711 A) : (term270 A x) = (term271 A x).
Proof. exact (MK_COMB (@lem7074560 A) (@lem7074559 A x)). Qed.
Lemma lem7074562 {A : Type'} : (term272 A) = (term273 A).
Proof. exact (fun_ext (fun x : type711 A => @lem7074561 A x)). Qed.
Lemma lem7074563 {A : Type'} : (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7074564 {A : Type'} : (term255 A) = (term274 A).
Proof. exact (MK_COMB (@lem7074563 A) (@lem7074562 A)). Qed.
Lemma lem7074565 {A : Type'} : ((term254 A) = (term255 A)) = ((term251 A) = (term274 A)).
Proof. exact (MK_COMB (@lem7074553 A) (@lem7074564 A)). Qed.
Lemma lem7074566 {A : Type'} : (term251 A) = (term274 A).
Proof. exact (EQ_MP (@lem7074565 A) (@lem7074540 A)). Qed.
Lemma lem7074568 {A : Type'} : (term147 A) = (term274 A).
Proof. exact (TRANS (@lem7074536 A) (@lem7074566 A)). Qed.
Lemma lem7074569 {A : Type'} : (term12 A) = (term274 A).
Proof. exact (TRANS (@lem7074236 A) (@lem7074568 A)). Qed.
Lemma lem7074570 {A : Type'} (h1 : term12 A) : term274 A.
Proof. exact (EQ_MP (@lem7074569 A) (@lem7073617 A h1)). Qed.
Lemma lem7074577 (x : real) (y : real) : (term34 x y) = (term275 x y).
Proof. exact (@lem17265 (real_lt x y) (real_le x y)). Qed.
Lemma lem7074578 (x : real) : (term35 x) = (term276 x).
Proof. exact (fun_ext (fun y : real => @lem7074577 x y)). Qed.
Lemma lem7074579 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7074580 (x : real) : (term36 x) = (term277 x).
Proof. exact (MK_COMB (@lem7074579) (@lem7074578 x)). Qed.
Lemma lem7074581 : term37 = term278.
Proof. exact (fun_ext (fun x : real => @lem7074580 x)). Qed.
Lemma lem7074582 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7074639 : term38 = term279.
Proof. exact (MK_COMB (@lem7074582) (@lem7074581)). Qed.
Lemma lem7074640 (h1 : term38) : term279.
Proof. exact (EQ_MP (@lem7074639) (@lem7073618 h1)). Qed.
Lemma lem7074642 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (@IN _132203 x s) = (@IN _132203 x s).
Proof. exact (eq_refl (@IN _132203 x s)). Qed.
Lemma lem7074643 {_132203 : Type'} (P : _132203 -> Prop) : (term120 _132203 P) = (term121 _132203 P).
Proof. exact (@lem18394 _132203 P). Qed.
Lemma lem7074644 {_132203 : Type'} (s : _132203 -> Prop) : (term280 _132203 s) = (term281 _132203 s).
Proof. exact (@lem7074643 _132203 (term30 _132203 s)). Qed.
Lemma lem7074645 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term282 _132203 s x) = (@IN _132203 x s).
Proof. exact (eq_refl (term282 _132203 s x)). Qed.
Lemma lem7074646 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7074648 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term283 _132203 s x) = (term284 _132203 x s).
Proof. exact (MK_COMB (@lem7074646) (@lem7074645 _132203 x s)). Qed.
Lemma lem7074649 {_132203 : Type'} (s : _132203 -> Prop) : (term285 _132203 s) = (term286 _132203 s).
Proof. exact (fun_ext (fun x : _132203 => @lem7074648 _132203 x s)). Qed.
Lemma lem7074650 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7074651 {_132203 : Type'} (s : _132203 -> Prop) : (term281 _132203 s) = (term287 _132203 s).
Proof. exact (MK_COMB (@lem7074650 _132203) (@lem7074649 _132203 s)). Qed.
Lemma lem7074652 {_132203 : Type'} (s : _132203 -> Prop) : (term280 _132203 s) = (term287 _132203 s).
Proof. exact (TRANS (@lem7074644 _132203 s) (@lem7074651 _132203 s)). Qed.
Lemma lem7074653 {_132203 : Type'} (s : _132203 -> Prop) : (term30 _132203 s) = (term30 _132203 s).
Proof. exact (fun_ext (fun x : _132203 => @lem7074642 _132203 x s)). Qed.
Lemma lem7074654 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7074655 {_132203 : Type'} (s : _132203 -> Prop) : (term31 _132203 s) = (term31 _132203 s).
Proof. exact (MK_COMB (@lem7074654 _132203) (@lem7074653 _132203 s)). Qed.
Lemma lem7074656 {_132203 : Type'} (s : _132203 -> Prop) : (term29 _132203 s) = (term29 _132203 s).
Proof. exact (eq_refl (term29 _132203 s)). Qed.
Lemma lem7074659 {_132203 : Type'} (s : _132203 -> Prop) : (term288 _132203 s) = (s = (@EMPTY _132203)).
Proof. exact (@lem16933 (s = (@EMPTY _132203))). Qed.
Lemma lem7074660 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074661 {_132203 : Type'} (s : _132203 -> Prop) : (term289 _132203 s) = (term290 _132203 s).
Proof. exact (MK_COMB (@lem7074660) (@lem7074652 _132203 s)). Qed.
Lemma lem7074662 {_132203 : Type'} (s : _132203 -> Prop) : (term291 _132203 s) = (term292 _132203 s).
Proof. exact (MK_COMB (@lem7074661 _132203 s) (@lem7074656 _132203 s)). Qed.
Lemma lem7074663 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074664 {_132203 : Type'} (s : _132203 -> Prop) : (term293 _132203 s) = (term293 _132203 s).
Proof. exact (MK_COMB (@lem7074663) (@lem7074655 _132203 s)). Qed.
Lemma lem7074665 {_132203 : Type'} (s : _132203 -> Prop) : (term294 _132203 s) = (term295 _132203 s).
Proof. exact (MK_COMB (@lem7074664 _132203 s) (@lem7074659 _132203 s)). Qed.
Lemma lem7074666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7074667 {_132203 : Type'} (s : _132203 -> Prop) : (term296 _132203 s) = (term297 _132203 s).
Proof. exact (MK_COMB (@lem7074666) (@lem7074665 _132203 s)). Qed.
Lemma lem7074668 {_132203 : Type'} (s : _132203 -> Prop) : (term298 _132203 s) = (term299 _132203 s).
Proof. exact (MK_COMB (@lem7074667 _132203 s) (@lem7074662 _132203 s)). Qed.
Lemma lem7074669 {_132203 : Type'} (s : _132203 -> Prop) : ((term31 _132203 s) = (term29 _132203 s)) = (term298 _132203 s).
Proof. exact (@lem17784 (term31 _132203 s) (term29 _132203 s)). Qed.
Lemma lem7074670 {_132203 : Type'} (s : _132203 -> Prop) : ((term31 _132203 s) = (term29 _132203 s)) = (term299 _132203 s).
Proof. exact (TRANS (@lem7074669 _132203 s) (@lem7074668 _132203 s)). Qed.
Lemma lem7074671 {_132203 : Type'} : (term33 _132203) = (term300 _132203).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7074670 _132203 s)). Qed.
Lemma lem7074672 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7074673 {_132203 : Type'} : (term11 _132203) = (term301 _132203).
Proof. exact (MK_COMB (@lem7074672 _132203) (@lem7074671 _132203)). Qed.
Lemma lem7074675 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term302 A P Q) = (term303 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7074676 {_132203 : Type'} (P : type686 _132203) (Q : type686 _132203) : (term304 _132203 P Q) = (term305 _132203 P Q).
Proof. exact (@lem7074675 (_132203 -> Prop) P Q). Qed.
Lemma lem7074677 {_132203 : Type'} : (term306 _132203) = (term307 _132203).
Proof. exact (@lem7074676 _132203 (term308 _132203) (term309 _132203)). Qed.
Lemma lem7074678 {_132203 : Type'} (s : _132203 -> Prop) : (term310 _132203 s) = (term295 _132203 s).
Proof. exact (eq_refl (term310 _132203 s)). Qed.
Lemma lem7074679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7074680 {_132203 : Type'} (s : _132203 -> Prop) : (term311 _132203 s) = (term297 _132203 s).
Proof. exact (MK_COMB (@lem7074679) (@lem7074678 _132203 s)). Qed.
Lemma lem7074681 {_132203 : Type'} (s : _132203 -> Prop) : (term312 _132203 s) = (term292 _132203 s).
Proof. exact (eq_refl (term312 _132203 s)). Qed.
Lemma lem7074682 {_132203 : Type'} (s : _132203 -> Prop) : (term313 _132203 s) = (term299 _132203 s).
Proof. exact (MK_COMB (@lem7074680 _132203 s) (@lem7074681 _132203 s)). Qed.
Lemma lem7074683 {_132203 : Type'} : (term314 _132203) = (term300 _132203).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7074682 _132203 s)). Qed.
Lemma lem7074684 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7074685 {_132203 : Type'} : (term306 _132203) = (term301 _132203).
Proof. exact (MK_COMB (@lem7074684 _132203) (@lem7074683 _132203)). Qed.
Lemma lem7074686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074687 {_132203 : Type'} : (term315 _132203) = (term316 _132203).
Proof. exact (MK_COMB (@lem7074686) (@lem7074685 _132203)). Qed.
Lemma lem7074688 {_132203 : Type'} (s : _132203 -> Prop) : (term310 _132203 s) = (term295 _132203 s).
Proof. exact (eq_refl (term310 _132203 s)). Qed.
Lemma lem7074689 {_132203 : Type'} : (term317 _132203) = (term308 _132203).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7074688 _132203 s)). Qed.
Lemma lem7074690 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7074691 {_132203 : Type'} : (term318 _132203) = (term319 _132203).
Proof. exact (MK_COMB (@lem7074690 _132203) (@lem7074689 _132203)). Qed.
Lemma lem7074692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7074693 {_132203 : Type'} : (term320 _132203) = (term321 _132203).
Proof. exact (MK_COMB (@lem7074692) (@lem7074691 _132203)). Qed.
Lemma lem7074694 {_132203 : Type'} (s : _132203 -> Prop) : (term312 _132203 s) = (term292 _132203 s).
Proof. exact (eq_refl (term312 _132203 s)). Qed.
Lemma lem7074695 {_132203 : Type'} : (term322 _132203) = (term309 _132203).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7074694 _132203 s)). Qed.
Lemma lem7074696 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7074697 {_132203 : Type'} : (term323 _132203) = (term324 _132203).
Proof. exact (MK_COMB (@lem7074696 _132203) (@lem7074695 _132203)). Qed.
Lemma lem7074698 {_132203 : Type'} : (term307 _132203) = (term325 _132203).
Proof. exact (MK_COMB (@lem7074693 _132203) (@lem7074697 _132203)). Qed.
Lemma lem7074699 {_132203 : Type'} : ((term306 _132203) = (term307 _132203)) = ((term301 _132203) = (term325 _132203)).
Proof. exact (MK_COMB (@lem7074687 _132203) (@lem7074698 _132203)). Qed.
Lemma lem7074700 {_132203 : Type'} : (term301 _132203) = (term325 _132203).
Proof. exact (EQ_MP (@lem7074699 _132203) (@lem7074677 _132203)). Qed.
Lemma lem7074806 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7074807 {_132203 : Type'} (P : _132203 -> Prop) (Q : Prop) : (term148 _132203 P Q) = (term149 _132203 P Q).
Proof. exact (@lem7074806 _132203 P Q). Qed.
Lemma lem7074808 {_132203 : Type'} (s : _132203 -> Prop) : (term326 _132203 s) = (term327 _132203 s).
Proof. exact (@lem7074807 _132203 (term30 _132203 s) (s = (@EMPTY _132203))). Qed.
Lemma lem7074809 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term282 _132203 s x) = (@IN _132203 x s).
Proof. exact (eq_refl (term282 _132203 s x)). Qed.
Lemma lem7074810 {_132203 : Type'} (s : _132203 -> Prop) : (term328 _132203 s) = (term30 _132203 s).
Proof. exact (fun_ext (fun x : _132203 => @lem7074809 _132203 x s)). Qed.
Lemma lem7074811 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7074812 {_132203 : Type'} (s : _132203 -> Prop) : (term329 _132203 s) = (term31 _132203 s).
Proof. exact (MK_COMB (@lem7074811 _132203) (@lem7074810 _132203 s)). Qed.
Lemma lem7074813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074814 {_132203 : Type'} (s : _132203 -> Prop) : (term330 _132203 s) = (term293 _132203 s).
Proof. exact (MK_COMB (@lem7074813) (@lem7074812 _132203 s)). Qed.
Lemma lem7074815 {_132203 : Type'} (s : _132203 -> Prop) : (s = (@EMPTY _132203)) = (s = (@EMPTY _132203)).
Proof. exact (eq_refl (s = (@EMPTY _132203))). Qed.
Lemma lem7074816 {_132203 : Type'} (s : _132203 -> Prop) : (term326 _132203 s) = (term295 _132203 s).
Proof. exact (MK_COMB (@lem7074814 _132203 s) (@lem7074815 _132203 s)). Qed.
Lemma lem7074817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074818 {_132203 : Type'} (s : _132203 -> Prop) : (term331 _132203 s) = (term332 _132203 s).
Proof. exact (MK_COMB (@lem7074817) (@lem7074816 _132203 s)). Qed.
Lemma lem7074819 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term282 _132203 s x) = (@IN _132203 x s).
Proof. exact (eq_refl (term282 _132203 s x)). Qed.
Lemma lem7074820 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074821 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term333 _132203 s x) = (term334 _132203 x s).
Proof. exact (MK_COMB (@lem7074820) (@lem7074819 _132203 x s)). Qed.
Lemma lem7074822 {_132203 : Type'} (s : _132203 -> Prop) : (s = (@EMPTY _132203)) = (s = (@EMPTY _132203)).
Proof. exact (eq_refl (s = (@EMPTY _132203))). Qed.
Lemma lem7074823 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term335 _132203 x s) = (term336 _132203 x s).
Proof. exact (MK_COMB (@lem7074821 _132203 x s) (@lem7074822 _132203 s)). Qed.
Lemma lem7074824 {_132203 : Type'} (s : _132203 -> Prop) : (term337 _132203 s) = (term338 _132203 s).
Proof. exact (fun_ext (fun x : _132203 => @lem7074823 _132203 x s)). Qed.
Lemma lem7074825 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7074826 {_132203 : Type'} (s : _132203 -> Prop) : (term327 _132203 s) = (term339 _132203 s).
Proof. exact (MK_COMB (@lem7074825 _132203) (@lem7074824 _132203 s)). Qed.
Lemma lem7074827 {_132203 : Type'} (s : _132203 -> Prop) : ((term326 _132203 s) = (term327 _132203 s)) = ((term295 _132203 s) = (term339 _132203 s)).
Proof. exact (MK_COMB (@lem7074818 _132203 s) (@lem7074826 _132203 s)). Qed.
Lemma lem7074828 {_132203 : Type'} (s : _132203 -> Prop) : (term295 _132203 s) = (term339 _132203 s).
Proof. exact (EQ_MP (@lem7074827 _132203 s) (@lem7074808 _132203 s)). Qed.
Lemma lem7074829 {_132203 : Type'} : (term308 _132203) = (term340 _132203).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7074828 _132203 s)). Qed.
Lemma lem7074830 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7074831 {_132203 : Type'} : (term319 _132203) = (term341 _132203).
Proof. exact (MK_COMB (@lem7074830 _132203) (@lem7074829 _132203)). Qed.
Lemma lem7074833 {A B : Type'} (P : type1413 A B) : (term200 A B P) = (term201 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7074834 {_132203 : Type'} (P : type672 _132203) : (term202 _132203 P) = (term203 _132203 P).
Proof. exact (@lem7074833 (_132203 -> Prop) _132203 P). Qed.
Lemma lem7074835 {_132203 : Type'} : (term342 _132203) = (term343 _132203).
Proof. exact (@lem7074834 _132203 (term344 _132203)). Qed.
Lemma lem7074836 {_132203 : Type'} (s : _132203 -> Prop) : (term345 _132203 s) = (term338 _132203 s).
Proof. exact (eq_refl (term345 _132203 s)). Qed.
Lemma lem7074837 {_132203 : Type'} (x : _132203) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7074838 {_132203 : Type'} (s : _132203 -> Prop) (x : _132203) : (term346 _132203 s x) = (term347 _132203 s x).
Proof. exact (MK_COMB (@lem7074836 _132203 s) (@lem7074837 _132203 x)). Qed.
Lemma lem7074839 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term347 _132203 s x) = (term336 _132203 x s).
Proof. exact (eq_refl (term347 _132203 s x)). Qed.
Lemma lem7074840 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term346 _132203 s x) = (term336 _132203 x s).
Proof. exact (TRANS (@lem7074838 _132203 s x) (@lem7074839 _132203 x s)). Qed.
Lemma lem7074841 {_132203 : Type'} (s : _132203 -> Prop) : (term348 _132203 s) = (term338 _132203 s).
Proof. exact (fun_ext (fun x : _132203 => @lem7074840 _132203 x s)). Qed.
Lemma lem7074842 {_132203 : Type'} : (@ex _132203) = (@ex _132203).
Proof. exact (eq_refl (@ex _132203)). Qed.
Lemma lem7074843 {_132203 : Type'} (s : _132203 -> Prop) : (term349 _132203 s) = (term339 _132203 s).
Proof. exact (MK_COMB (@lem7074842 _132203) (@lem7074841 _132203 s)). Qed.
Lemma lem7074844 {_132203 : Type'} : (term350 _132203) = (term340 _132203).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7074843 _132203 s)). Qed.
Lemma lem7074845 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7074846 {_132203 : Type'} : (term342 _132203) = (term341 _132203).
Proof. exact (MK_COMB (@lem7074845 _132203) (@lem7074844 _132203)). Qed.
Lemma lem7074847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074848 {_132203 : Type'} : (term351 _132203) = (term352 _132203).
Proof. exact (MK_COMB (@lem7074847) (@lem7074846 _132203)). Qed.
Lemma lem7074849 {_132203 : Type'} (s : _132203 -> Prop) : (term345 _132203 s) = (term338 _132203 s).
Proof. exact (eq_refl (term345 _132203 s)). Qed.
Lemma lem7074850 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7074851 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term353 _132203 x s) = (term354 _132203 x s).
Proof. exact (MK_COMB (@lem7074849 _132203 s) (@lem7074850 _132203 x s)). Qed.
Lemma lem7074852 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term354 _132203 x s) = (term355 _132203 x s).
Proof. exact (eq_refl (term354 _132203 x s)). Qed.
Lemma lem7074853 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term353 _132203 x s) = (term355 _132203 x s).
Proof. exact (TRANS (@lem7074851 _132203 x s) (@lem7074852 _132203 x s)). Qed.
Lemma lem7074854 {_132203 : Type'} (x : type684 _132203) : (term356 _132203 x) = (term357 _132203 x).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7074853 _132203 x s)). Qed.
Lemma lem7074855 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7074856 {_132203 : Type'} (x : type684 _132203) : (term358 _132203 x) = (term359 _132203 x).
Proof. exact (MK_COMB (@lem7074855 _132203) (@lem7074854 _132203 x)). Qed.
Lemma lem7074857 {_132203 : Type'} : (term360 _132203) = (term361 _132203).
Proof. exact (fun_ext (fun x : type684 _132203 => @lem7074856 _132203 x)). Qed.
Lemma lem7074858 {_132203 : Type'} : (@ex ((_132203 -> Prop) -> _132203)) = (@ex ((_132203 -> Prop) -> _132203)).
Proof. exact (eq_refl (@ex ((_132203 -> Prop) -> _132203))). Qed.
Lemma lem7074859 {_132203 : Type'} : (term343 _132203) = (term362 _132203).
Proof. exact (MK_COMB (@lem7074858 _132203) (@lem7074857 _132203)). Qed.
Lemma lem7074860 {_132203 : Type'} : ((term342 _132203) = (term343 _132203)) = ((term341 _132203) = (term362 _132203)).
Proof. exact (MK_COMB (@lem7074848 _132203) (@lem7074859 _132203)). Qed.
Lemma lem7074861 {_132203 : Type'} : (term341 _132203) = (term362 _132203).
Proof. exact (EQ_MP (@lem7074860 _132203) (@lem7074835 _132203)). Qed.
Lemma lem7074862 {_132203 : Type'} : (term319 _132203) = (term362 _132203).
Proof. exact (TRANS (@lem7074831 _132203) (@lem7074861 _132203)). Qed.
Lemma lem7074863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7074864 {_132203 : Type'} : (term321 _132203) = (term363 _132203).
Proof. exact (MK_COMB (@lem7074863) (@lem7074862 _132203)). Qed.
Lemma lem7074865 {_132203 : Type'} : (term324 _132203) = (term324 _132203).
Proof. exact (eq_refl (term324 _132203)). Qed.
Lemma lem7074866 {_132203 : Type'} : (term325 _132203) = (term364 _132203).
Proof. exact (MK_COMB (@lem7074864 _132203) (@lem7074865 _132203)). Qed.
Lemma lem7074868 {A : Type'} (P : A -> Prop) (Q : Prop) : (term365 A P Q) = (term366 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7074869 {_132203 : Type'} (P : type162 _132203) (Q : Prop) : (term367 _132203 P Q) = (term368 _132203 P Q).
Proof. exact (@lem7074868 (type684 _132203) P Q). Qed.
Lemma lem7074870 {_132203 : Type'} : (term369 _132203) = (term370 _132203).
Proof. exact (@lem7074869 _132203 (term361 _132203) (term324 _132203)). Qed.
Lemma lem7074871 {_132203 : Type'} (x : type684 _132203) : (term371 _132203 x) = (term359 _132203 x).
Proof. exact (eq_refl (term371 _132203 x)). Qed.
Lemma lem7074872 {_132203 : Type'} : (term372 _132203) = (term361 _132203).
Proof. exact (fun_ext (fun x : type684 _132203 => @lem7074871 _132203 x)). Qed.
Lemma lem7074873 {_132203 : Type'} : (@ex ((_132203 -> Prop) -> _132203)) = (@ex ((_132203 -> Prop) -> _132203)).
Proof. exact (eq_refl (@ex ((_132203 -> Prop) -> _132203))). Qed.
Lemma lem7074874 {_132203 : Type'} : (term373 _132203) = (term362 _132203).
Proof. exact (MK_COMB (@lem7074873 _132203) (@lem7074872 _132203)). Qed.
Lemma lem7074875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7074876 {_132203 : Type'} : (term374 _132203) = (term363 _132203).
Proof. exact (MK_COMB (@lem7074875) (@lem7074874 _132203)). Qed.
Lemma lem7074877 {_132203 : Type'} : (term324 _132203) = (term324 _132203).
Proof. exact (eq_refl (term324 _132203)). Qed.
Lemma lem7074878 {_132203 : Type'} : (term369 _132203) = (term364 _132203).
Proof. exact (MK_COMB (@lem7074876 _132203) (@lem7074877 _132203)). Qed.
Lemma lem7074879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7074880 {_132203 : Type'} : (term375 _132203) = (term376 _132203).
Proof. exact (MK_COMB (@lem7074879) (@lem7074878 _132203)). Qed.
Lemma lem7074881 {_132203 : Type'} (x : type684 _132203) : (term371 _132203 x) = (term359 _132203 x).
Proof. exact (eq_refl (term371 _132203 x)). Qed.
Lemma lem7074882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7074883 {_132203 : Type'} (x : type684 _132203) : (term377 _132203 x) = (term378 _132203 x).
Proof. exact (MK_COMB (@lem7074882) (@lem7074881 _132203 x)). Qed.
Lemma lem7074884 {_132203 : Type'} : (term324 _132203) = (term324 _132203).
Proof. exact (eq_refl (term324 _132203)). Qed.
Lemma lem7074885 {_132203 : Type'} (x : type684 _132203) : (term379 _132203 x) = (term380 _132203 x).
Proof. exact (MK_COMB (@lem7074883 _132203 x) (@lem7074884 _132203)). Qed.
Lemma lem7074886 {_132203 : Type'} : (term381 _132203) = (term382 _132203).
Proof. exact (fun_ext (fun x : type684 _132203 => @lem7074885 _132203 x)). Qed.
Lemma lem7074887 {_132203 : Type'} : (@ex ((_132203 -> Prop) -> _132203)) = (@ex ((_132203 -> Prop) -> _132203)).
Proof. exact (eq_refl (@ex ((_132203 -> Prop) -> _132203))). Qed.
Lemma lem7074888 {_132203 : Type'} : (term370 _132203) = (term383 _132203).
Proof. exact (MK_COMB (@lem7074887 _132203) (@lem7074886 _132203)). Qed.
Lemma lem7074889 {_132203 : Type'} : ((term369 _132203) = (term370 _132203)) = ((term364 _132203) = (term383 _132203)).
Proof. exact (MK_COMB (@lem7074880 _132203) (@lem7074888 _132203)). Qed.
Lemma lem7074890 {_132203 : Type'} : (term364 _132203) = (term383 _132203).
Proof. exact (EQ_MP (@lem7074889 _132203) (@lem7074870 _132203)). Qed.
Lemma lem7074891 {_132203 : Type'} : (term325 _132203) = (term383 _132203).
Proof. exact (TRANS (@lem7074866 _132203) (@lem7074890 _132203)). Qed.
Lemma lem7074892 {_132203 : Type'} : (term301 _132203) = (term383 _132203).
Proof. exact (TRANS (@lem7074700 _132203) (@lem7074891 _132203)). Qed.
Lemma lem7074893 {_132203 : Type'} : (term11 _132203) = (term383 _132203).
Proof. exact (TRANS (@lem7074673 _132203) (@lem7074892 _132203)). Qed.
Lemma lem7074894 {_132203 : Type'} (h1 : term11 _132203) : term383 _132203.
Proof. exact (EQ_MP (@lem7074893 _132203) (@lem7073619 _132203 h1)). Qed.
Lemma lem7074895 {_132203 : Type'} (x : type684 _132203) (h1 : term380 _132203 x) : term380 _132203 x.
Proof. exact (h1). Qed.
Lemma lem7074897 {_132203 : Type'} (x'' : type711 _132203) (h1 : term271 _132203 x'') : term271 _132203 x''.
Proof. exact (h1). Qed.
Lemma lem7074898 {_132203 : Type'} (f : _132203 -> real) (h1 : term99 _132203 f) : term99 _132203 f.
Proof. exact (h1). Qed.
Lemma lem7074899 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (h1 : term90 _132203 f g) : term90 _132203 f g.
Proof. exact (h1). Qed.
Lemma lem7074900 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term80 _132203 f s g.
Proof. exact (h1). Qed.
Lemma lem7074907 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7074908 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7074907 real (real -> Prop) f x). Qed.
Lemma lem7074909 (x : real) : (real_le x) = (@I (real -> real -> Prop) real_le x).
Proof. exact (@lem7074908 real_le x). Qed.
Lemma lem7074910 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7074911 (x : real) (y : real) : (real_le x y) = (@I (real -> real -> Prop) real_le x y).
Proof. exact (MK_COMB (@lem7074909 x) (@lem7074910 y)). Qed.
Lemma lem7074913 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7074914 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7074913 real Prop f x). Qed.
Lemma lem7074915 (x : real) (y : real) : (@I (real -> real -> Prop) real_le x y) = (term384 x y).
Proof. exact (@lem7074914 (@I (real -> real -> Prop) real_le x) y). Qed.
Lemma lem7074917 (x : real) (y : real) : (real_le x y) = (term384 x y).
Proof. exact (TRANS (@lem7074911 x y) (@lem7074915 x y)). Qed.
Lemma lem7074918 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7074925 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7074926 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7074925 real (real -> Prop) f x). Qed.
Lemma lem7074927 (x : real) : (real_lt x) = (@I (real -> real -> Prop) real_lt x).
Proof. exact (@lem7074926 real_lt x). Qed.
Lemma lem7074928 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7074929 (x : real) (y : real) : (real_lt x y) = (@I (real -> real -> Prop) real_lt x y).
Proof. exact (MK_COMB (@lem7074927 x) (@lem7074928 y)). Qed.
Lemma lem7074931 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7074932 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7074931 real Prop f x). Qed.
Lemma lem7074933 (x : real) (y : real) : (@I (real -> real -> Prop) real_lt x y) = (term385 x y).
Proof. exact (@lem7074932 (@I (real -> real -> Prop) real_lt x) y). Qed.
Lemma lem7074935 (x : real) (y : real) : (real_lt x y) = (term385 x y).
Proof. exact (TRANS (@lem7074929 x y) (@lem7074933 x y)). Qed.
Lemma lem7074936 (x : real) (y : real) : (term386 x y) = (term387 x y).
Proof. exact (MK_COMB (@lem7074918) (@lem7074935 x y)). Qed.
Lemma lem7074937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074938 (x : real) (y : real) : (term388 x y) = (term389 x y).
Proof. exact (MK_COMB (@lem7074937) (@lem7074936 x y)). Qed.
Lemma lem7074939 (x : real) (y : real) : (term275 x y) = (term390 x y).
Proof. exact (MK_COMB (@lem7074938 x y) (@lem7074917 x y)). Qed.
Lemma lem7074940 (x : real) : (term276 x) = (term391 x).
Proof. exact (fun_ext (fun y : real => @lem7074939 x y)). Qed.
Lemma lem7074941 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7074942 (x : real) : (term277 x) = (term392 x).
Proof. exact (MK_COMB (@lem7074941) (@lem7074940 x)). Qed.
Lemma lem7074943 : term278 = term393.
Proof. exact (fun_ext (fun x : real => @lem7074942 x)). Qed.
Lemma lem7074944 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7074945 : term279 = term394.
Proof. exact (MK_COMB (@lem7074944) (@lem7074943)). Qed.
Lemma lem7074946 (h1 : term38) : term394.
Proof. exact (EQ_MP (@lem7074945) (@lem7074640 h1)). Qed.
Lemma lem7074953 {_132203 : Type'} (s : _132203 -> Prop) : (term29 _132203 s) = (term29 _132203 s).
Proof. exact (eq_refl (term29 _132203 s)). Qed.
Lemma lem7074954 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7074961 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7074962 {_132203 : Type'} (f : type1364 _132203) (x : _132203) : (f x) = (@I (_132203 -> (_132203 -> Prop) -> Prop) f x).
Proof. exact (@lem7074961 _132203 (type686 _132203) f x). Qed.
Lemma lem7074963 {_132203 : Type'} (x : _132203) : (@IN _132203 x) = (@I (_132203 -> (_132203 -> Prop) -> Prop) (@IN _132203) x).
Proof. exact (@lem7074962 _132203 (@IN _132203) x). Qed.
Lemma lem7074964 {_132203 : Type'} (s : _132203 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7074965 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (@IN _132203 x s) = (@I (_132203 -> (_132203 -> Prop) -> Prop) (@IN _132203) x s).
Proof. exact (MK_COMB (@lem7074963 _132203 x) (@lem7074964 _132203 s)). Qed.
Lemma lem7074967 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7074968 {_132203 : Type'} (f : type686 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> Prop) f x).
Proof. exact (@lem7074967 (_132203 -> Prop) Prop f x). Qed.
Lemma lem7074969 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (@I (_132203 -> (_132203 -> Prop) -> Prop) (@IN _132203) x s) = (term395 _132203 x s).
Proof. exact (@lem7074968 _132203 (@I (_132203 -> (_132203 -> Prop) -> Prop) (@IN _132203) x) s). Qed.
Lemma lem7074971 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (@IN _132203 x s) = (term395 _132203 x s).
Proof. exact (TRANS (@lem7074965 _132203 x s) (@lem7074969 _132203 x s)). Qed.
Lemma lem7074972 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term284 _132203 x s) = (term396 _132203 x s).
Proof. exact (MK_COMB (@lem7074954) (@lem7074971 _132203 x s)). Qed.
Lemma lem7074973 {_132203 : Type'} (s : _132203 -> Prop) : (term286 _132203 s) = (term397 _132203 s).
Proof. exact (fun_ext (fun x : _132203 => @lem7074972 _132203 x s)). Qed.
Lemma lem7074974 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7074975 {_132203 : Type'} (s : _132203 -> Prop) : (term287 _132203 s) = (term398 _132203 s).
Proof. exact (MK_COMB (@lem7074974 _132203) (@lem7074973 _132203 s)). Qed.
Lemma lem7074976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7074977 {_132203 : Type'} (s : _132203 -> Prop) : (term290 _132203 s) = (term399 _132203 s).
Proof. exact (MK_COMB (@lem7074976) (@lem7074975 _132203 s)). Qed.
Lemma lem7074978 {_132203 : Type'} (s : _132203 -> Prop) : (term292 _132203 s) = (term400 _132203 s).
Proof. exact (MK_COMB (@lem7074977 _132203 s) (@lem7074953 _132203 s)). Qed.
Lemma lem7074979 {_132203 : Type'} : (term309 _132203) = (term401 _132203).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7074978 _132203 s)). Qed.
Lemma lem7074980 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7074981 {_132203 : Type'} : (term324 _132203) = (term402 _132203).
Proof. exact (MK_COMB (@lem7074980 _132203) (@lem7074979 _132203)). Qed.
Lemma lem7074986 {_132203 : Type'} (s : _132203 -> Prop) : (s = (@EMPTY _132203)) = (s = (@EMPTY _132203)).
Proof. exact (eq_refl (s = (@EMPTY _132203))). Qed.
Lemma lem7074987 {_132203 : Type'} : (@IN _132203) = (@IN _132203).
Proof. exact (eq_refl (@IN _132203)). Qed.
Lemma lem7074992 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7074993 {_132203 : Type'} (f : type684 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> _132203) f x).
Proof. exact (@lem7074992 (_132203 -> Prop) _132203 f x). Qed.
Lemma lem7074995 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (x s) = (@I ((_132203 -> Prop) -> _132203) x s).
Proof. exact (@lem7074993 _132203 x s). Qed.
Lemma lem7074996 {_132203 : Type'} (s : _132203 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7074997 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term403 _132203 x s) = (term404 _132203 x s).
Proof. exact (MK_COMB (@lem7074987 _132203) (@lem7074995 _132203 x s)). Qed.
Lemma lem7074998 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term405 _132203 x s) = (term406 _132203 x s).
Proof. exact (MK_COMB (@lem7074997 _132203 x s) (@lem7074996 _132203 s)). Qed.
Lemma lem7075000 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075001 {_132203 : Type'} (f : type1364 _132203) (x : _132203) : (f x) = (@I (_132203 -> (_132203 -> Prop) -> Prop) f x).
Proof. exact (@lem7075000 _132203 (type686 _132203) f x). Qed.
Lemma lem7075002 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term404 _132203 x s) = (term407 _132203 x s).
Proof. exact (@lem7075001 _132203 (@IN _132203) (@I ((_132203 -> Prop) -> _132203) x s)). Qed.
Lemma lem7075003 {_132203 : Type'} (s : _132203 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7075004 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term406 _132203 x s) = (term408 _132203 x s).
Proof. exact (MK_COMB (@lem7075002 _132203 x s) (@lem7075003 _132203 s)). Qed.
Lemma lem7075006 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075007 {_132203 : Type'} (f : type686 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> Prop) f x).
Proof. exact (@lem7075006 (_132203 -> Prop) Prop f x). Qed.
Lemma lem7075008 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term408 _132203 x s) = (term409 _132203 x s).
Proof. exact (@lem7075007 _132203 (term407 _132203 x s) s). Qed.
Lemma lem7075009 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term406 _132203 x s) = (term409 _132203 x s).
Proof. exact (TRANS (@lem7075004 _132203 x s) (@lem7075008 _132203 x s)). Qed.
Lemma lem7075010 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term405 _132203 x s) = (term409 _132203 x s).
Proof. exact (TRANS (@lem7074998 _132203 x s) (@lem7075009 _132203 x s)). Qed.
Lemma lem7075011 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7075012 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term410 _132203 x s) = (term411 _132203 x s).
Proof. exact (MK_COMB (@lem7075011) (@lem7075010 _132203 x s)). Qed.
Lemma lem7075013 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term355 _132203 x s) = (term412 _132203 x s).
Proof. exact (MK_COMB (@lem7075012 _132203 x s) (@lem7074986 _132203 s)). Qed.
Lemma lem7075014 {_132203 : Type'} (x : type684 _132203) : (term357 _132203 x) = (term413 _132203 x).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7075013 _132203 x s)). Qed.
Lemma lem7075015 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7075016 {_132203 : Type'} (x : type684 _132203) : (term359 _132203 x) = (term414 _132203 x).
Proof. exact (MK_COMB (@lem7075015 _132203) (@lem7075014 _132203 x)). Qed.
Lemma lem7075017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7075018 {_132203 : Type'} (x : type684 _132203) : (term378 _132203 x) = (term415 _132203 x).
Proof. exact (MK_COMB (@lem7075017) (@lem7075016 _132203 x)). Qed.
Lemma lem7075019 {_132203 : Type'} (x : type684 _132203) : (term380 _132203 x) = (term416 _132203 x).
Proof. exact (MK_COMB (@lem7075018 _132203 x) (@lem7074981 _132203)). Qed.
Lemma lem7075020 {_132203 : Type'} (x : type684 _132203) (h1 : term380 _132203 x) : term416 _132203 x.
Proof. exact (EQ_MP (@lem7075019 _132203 x) (@lem7074895 _132203 x h1)). Qed.
Lemma lem7075284 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7075291 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075292 {_132203 : Type'} (f : type646 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) f x).
Proof. exact (@lem7075291 (_132203 -> Prop) (type717 _132203) f x). Qed.
Lemma lem7075293 {_132203 : Type'} (s : _132203 -> Prop) : (@sum _132203 s) = (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s).
Proof. exact (@lem7075292 _132203 (@sum _132203) s). Qed.
Lemma lem7075294 {_132203 : Type'} (f : _132203 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7075295 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) : (@sum _132203 s f) = (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s f).
Proof. exact (MK_COMB (@lem7075293 _132203 s) (@lem7075294 _132203 f)). Qed.
Lemma lem7075297 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075298 {_132203 : Type'} (f : type717 _132203) (x : _132203 -> real) : (f x) = (@I ((_132203 -> real) -> real) f x).
Proof. exact (@lem7075297 (_132203 -> real) real f x). Qed.
Lemma lem7075299 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) : (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s f) = (term417 _132203 s f).
Proof. exact (@lem7075298 _132203 (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s) f). Qed.
Lemma lem7075301 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) : (@sum _132203 s f) = (term417 _132203 s f).
Proof. exact (TRANS (@lem7075295 _132203 s f) (@lem7075299 _132203 s f)). Qed.
Lemma lem7075308 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075309 {_132203 : Type'} (f : type646 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) f x).
Proof. exact (@lem7075308 (_132203 -> Prop) (type717 _132203) f x). Qed.
Lemma lem7075310 {_132203 : Type'} (s : _132203 -> Prop) : (@sum _132203 s) = (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s).
Proof. exact (@lem7075309 _132203 (@sum _132203) s). Qed.
Lemma lem7075311 {_132203 : Type'} (g : _132203 -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7075312 {_132203 : Type'} (s : _132203 -> Prop) (g : _132203 -> real) : (@sum _132203 s g) = (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s g).
Proof. exact (MK_COMB (@lem7075310 _132203 s) (@lem7075311 _132203 g)). Qed.
Lemma lem7075314 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075315 {_132203 : Type'} (f : type717 _132203) (x : _132203 -> real) : (f x) = (@I ((_132203 -> real) -> real) f x).
Proof. exact (@lem7075314 (_132203 -> real) real f x). Qed.
Lemma lem7075316 {_132203 : Type'} (s : _132203 -> Prop) (g : _132203 -> real) : (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s g) = (term417 _132203 s g).
Proof. exact (@lem7075315 _132203 (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s) g). Qed.
Lemma lem7075318 {_132203 : Type'} (s : _132203 -> Prop) (g : _132203 -> real) : (@sum _132203 s g) = (term417 _132203 s g).
Proof. exact (TRANS (@lem7075312 _132203 s g) (@lem7075316 _132203 s g)). Qed.
Lemma lem7075319 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) : (term418 _132203 s f) = (term419 _132203 s f).
Proof. exact (MK_COMB (@lem7075284) (@lem7075301 _132203 s f)). Qed.
Lemma lem7075320 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term39 _132203 f s g) = (term420 _132203 f s g).
Proof. exact (MK_COMB (@lem7075319 _132203 s f) (@lem7075318 _132203 s g)). Qed.
Lemma lem7075322 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075323 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7075322 real (real -> Prop) f x). Qed.
Lemma lem7075324 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) : (term419 _132203 s f) = (term421 _132203 s f).
Proof. exact (@lem7075323 real_lt (term417 _132203 s f)). Qed.
Lemma lem7075325 {_132203 : Type'} (s : _132203 -> Prop) (g : _132203 -> real) : (term417 _132203 s g) = (term417 _132203 s g).
Proof. exact (eq_refl (term417 _132203 s g)). Qed.
Lemma lem7075326 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term420 _132203 f s g) = (term422 _132203 f s g).
Proof. exact (MK_COMB (@lem7075324 _132203 s f) (@lem7075325 _132203 s g)). Qed.
Lemma lem7075328 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075329 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7075328 real Prop f x). Qed.
Lemma lem7075330 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term422 _132203 f s g) = (term423 _132203 f s g).
Proof. exact (@lem7075329 (term421 _132203 s f) (term417 _132203 s g)). Qed.
Lemma lem7075331 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term420 _132203 f s g) = (term423 _132203 f s g).
Proof. exact (TRANS (@lem7075326 _132203 f s g) (@lem7075330 _132203 f s g)). Qed.
Lemma lem7075332 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term39 _132203 f s g) = (term423 _132203 f s g).
Proof. exact (TRANS (@lem7075320 _132203 f s g) (@lem7075331 _132203 f s g)). Qed.
Lemma lem7075333 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7075334 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7075339 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075341 {_132203 : Type'} (f : _132203 -> real) (x : _132203) : (f x) = (@I (_132203 -> real) f x).
Proof. exact (@lem7075339 _132203 real f x). Qed.
Lemma lem7075346 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075347 {_132203 : Type'} (f : _132203 -> real) (x : _132203) : (f x) = (@I (_132203 -> real) f x).
Proof. exact (@lem7075346 _132203 real f x). Qed.
Lemma lem7075349 {_132203 : Type'} (g : _132203 -> real) (x : _132203) : (g x) = (@I (_132203 -> real) g x).
Proof. exact (@lem7075347 _132203 g x). Qed.
Lemma lem7075350 {_132203 : Type'} (f : _132203 -> real) (x : _132203) : (term424 _132203 f x) = (term425 _132203 f x).
Proof. exact (MK_COMB (@lem7075334) (@lem7075341 _132203 f x)). Qed.
Lemma lem7075351 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term71 _132203 f g x) = (term426 _132203 f g x).
Proof. exact (MK_COMB (@lem7075350 _132203 f x) (@lem7075349 _132203 g x)). Qed.
Lemma lem7075353 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075354 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7075353 real (real -> Prop) f x). Qed.
Lemma lem7075355 {_132203 : Type'} (f : _132203 -> real) (x : _132203) : (term425 _132203 f x) = (term427 _132203 f x).
Proof. exact (@lem7075354 real_lt (@I (_132203 -> real) f x)). Qed.
Lemma lem7075356 {_132203 : Type'} (g : _132203 -> real) (x : _132203) : (@I (_132203 -> real) g x) = (@I (_132203 -> real) g x).
Proof. exact (eq_refl (@I (_132203 -> real) g x)). Qed.
Lemma lem7075357 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term426 _132203 f g x) = (term428 _132203 f g x).
Proof. exact (MK_COMB (@lem7075355 _132203 f x) (@lem7075356 _132203 g x)). Qed.
Lemma lem7075359 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075360 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7075359 real Prop f x). Qed.
Lemma lem7075361 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term428 _132203 f g x) = (term429 _132203 f g x).
Proof. exact (@lem7075360 (term427 _132203 f x) (@I (_132203 -> real) g x)). Qed.
Lemma lem7075362 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term426 _132203 f g x) = (term429 _132203 f g x).
Proof. exact (TRANS (@lem7075357 _132203 f g x) (@lem7075361 _132203 f g x)). Qed.
Lemma lem7075363 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term71 _132203 f g x) = (term429 _132203 f g x).
Proof. exact (TRANS (@lem7075351 _132203 f g x) (@lem7075362 _132203 f g x)). Qed.
Lemma lem7075364 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term430 _132203 f g x) = (term431 _132203 f g x).
Proof. exact (MK_COMB (@lem7075333) (@lem7075363 _132203 f g x)). Qed.
Lemma lem7075365 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7075372 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075373 {_132203 : Type'} (f : type1364 _132203) (x : _132203) : (f x) = (@I (_132203 -> (_132203 -> Prop) -> Prop) f x).
Proof. exact (@lem7075372 _132203 (type686 _132203) f x). Qed.
Lemma lem7075374 {_132203 : Type'} (x : _132203) : (@IN _132203 x) = (@I (_132203 -> (_132203 -> Prop) -> Prop) (@IN _132203) x).
Proof. exact (@lem7075373 _132203 (@IN _132203) x). Qed.
Lemma lem7075375 {_132203 : Type'} (s : _132203 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7075376 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (@IN _132203 x s) = (@I (_132203 -> (_132203 -> Prop) -> Prop) (@IN _132203) x s).
Proof. exact (MK_COMB (@lem7075374 _132203 x) (@lem7075375 _132203 s)). Qed.
Lemma lem7075378 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075379 {_132203 : Type'} (f : type686 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> Prop) f x).
Proof. exact (@lem7075378 (_132203 -> Prop) Prop f x). Qed.
Lemma lem7075380 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (@I (_132203 -> (_132203 -> Prop) -> Prop) (@IN _132203) x s) = (term395 _132203 x s).
Proof. exact (@lem7075379 _132203 (@I (_132203 -> (_132203 -> Prop) -> Prop) (@IN _132203) x) s). Qed.
Lemma lem7075382 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (@IN _132203 x s) = (term395 _132203 x s).
Proof. exact (TRANS (@lem7075376 _132203 x s) (@lem7075380 _132203 x s)). Qed.
Lemma lem7075383 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term284 _132203 x s) = (term396 _132203 x s).
Proof. exact (MK_COMB (@lem7075365) (@lem7075382 _132203 x s)). Qed.
Lemma lem7075384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7075385 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term432 _132203 x s) = (term433 _132203 x s).
Proof. exact (MK_COMB (@lem7075384) (@lem7075383 _132203 x s)). Qed.
Lemma lem7075386 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term119 _132203 s f g x) = (term434 _132203 s f g x).
Proof. exact (MK_COMB (@lem7075385 _132203 x s) (@lem7075364 _132203 f g x)). Qed.
Lemma lem7075387 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term127 _132203 s f g) = (term435 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7075386 _132203 s f g x)). Qed.
Lemma lem7075388 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7075389 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term128 _132203 s f g) = (term436 _132203 s f g).
Proof. exact (MK_COMB (@lem7075388 _132203) (@lem7075387 _132203 s f g)). Qed.
Lemma lem7075390 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7075391 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7075392 {_132203 : Type'} (f : _132203 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7075401 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075402 {_132203 : Type'} (f : type711 _132203) (x : _132203 -> real) : (f x) = (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) f x).
Proof. exact (@lem7075401 (_132203 -> real) (type710 _132203) f x). Qed.
Lemma lem7075403 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) : (x'' f) = (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) x'' f).
Proof. exact (@lem7075402 _132203 x'' f). Qed.
Lemma lem7075404 {_132203 : Type'} (g : _132203 -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7075405 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (x'' f g) = (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) x'' f g).
Proof. exact (MK_COMB (@lem7075403 _132203 x'' f) (@lem7075404 _132203 g)). Qed.
Lemma lem7075407 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075408 {_132203 : Type'} (f : type710 _132203) (x : _132203 -> real) : (f x) = (@I ((_132203 -> real) -> (_132203 -> Prop) -> _132203) f x).
Proof. exact (@lem7075407 (_132203 -> real) (type684 _132203) f x). Qed.
Lemma lem7075409 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) x'' f g) = (term437 _132203 x'' f g).
Proof. exact (@lem7075408 _132203 (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) x'' f) g). Qed.
Lemma lem7075410 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (x'' f g) = (term437 _132203 x'' f g).
Proof. exact (TRANS (@lem7075405 _132203 x'' f g) (@lem7075409 _132203 x'' f g)). Qed.
Lemma lem7075411 {_132203 : Type'} (s : _132203 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7075412 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (x'' f g s) = (term438 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075410 _132203 x'' f g) (@lem7075411 _132203 s)). Qed.
Lemma lem7075414 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075415 {_132203 : Type'} (f : type684 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> _132203) f x).
Proof. exact (@lem7075414 (_132203 -> Prop) _132203 f x). Qed.
Lemma lem7075416 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term438 _132203 x'' f g s) = (term439 _132203 x'' f g s).
Proof. exact (@lem7075415 _132203 (term437 _132203 x'' f g) s). Qed.
Lemma lem7075418 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (x'' f g s) = (term439 _132203 x'' f g s).
Proof. exact (TRANS (@lem7075412 _132203 x'' f g s) (@lem7075416 _132203 x'' f g s)). Qed.
Lemma lem7075419 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term440 _132203 x'' f g s) = (term441 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075392 _132203 f) (@lem7075418 _132203 x'' f g s)). Qed.
Lemma lem7075421 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075422 {_132203 : Type'} (f : _132203 -> real) (x : _132203) : (f x) = (@I (_132203 -> real) f x).
Proof. exact (@lem7075421 _132203 real f x). Qed.
Lemma lem7075423 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term441 _132203 x'' f g s) = (term442 _132203 x'' f g s).
Proof. exact (@lem7075422 _132203 f (term439 _132203 x'' f g s)). Qed.
Lemma lem7075424 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term440 _132203 x'' f g s) = (term442 _132203 x'' f g s).
Proof. exact (TRANS (@lem7075419 _132203 x'' f g s) (@lem7075423 _132203 x'' f g s)). Qed.
Lemma lem7075425 {_132203 : Type'} (g : _132203 -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7075434 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075435 {_132203 : Type'} (f : type711 _132203) (x : _132203 -> real) : (f x) = (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) f x).
Proof. exact (@lem7075434 (_132203 -> real) (type710 _132203) f x). Qed.
Lemma lem7075436 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) : (x'' f) = (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) x'' f).
Proof. exact (@lem7075435 _132203 x'' f). Qed.
Lemma lem7075437 {_132203 : Type'} (g : _132203 -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7075438 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (x'' f g) = (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) x'' f g).
Proof. exact (MK_COMB (@lem7075436 _132203 x'' f) (@lem7075437 _132203 g)). Qed.
Lemma lem7075440 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075441 {_132203 : Type'} (f : type710 _132203) (x : _132203 -> real) : (f x) = (@I ((_132203 -> real) -> (_132203 -> Prop) -> _132203) f x).
Proof. exact (@lem7075440 (_132203 -> real) (type684 _132203) f x). Qed.
Lemma lem7075442 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) x'' f g) = (term437 _132203 x'' f g).
Proof. exact (@lem7075441 _132203 (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) x'' f) g). Qed.
Lemma lem7075443 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (x'' f g) = (term437 _132203 x'' f g).
Proof. exact (TRANS (@lem7075438 _132203 x'' f g) (@lem7075442 _132203 x'' f g)). Qed.
Lemma lem7075444 {_132203 : Type'} (s : _132203 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7075445 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (x'' f g s) = (term438 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075443 _132203 x'' f g) (@lem7075444 _132203 s)). Qed.
Lemma lem7075447 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075448 {_132203 : Type'} (f : type684 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> _132203) f x).
Proof. exact (@lem7075447 (_132203 -> Prop) _132203 f x). Qed.
Lemma lem7075449 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term438 _132203 x'' f g s) = (term439 _132203 x'' f g s).
Proof. exact (@lem7075448 _132203 (term437 _132203 x'' f g) s). Qed.
Lemma lem7075451 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (x'' f g s) = (term439 _132203 x'' f g s).
Proof. exact (TRANS (@lem7075445 _132203 x'' f g s) (@lem7075449 _132203 x'' f g s)). Qed.
Lemma lem7075452 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term443 _132203 x'' f g s) = (term444 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075425 _132203 g) (@lem7075451 _132203 x'' f g s)). Qed.
Lemma lem7075454 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075455 {_132203 : Type'} (f : _132203 -> real) (x : _132203) : (f x) = (@I (_132203 -> real) f x).
Proof. exact (@lem7075454 _132203 real f x). Qed.
Lemma lem7075456 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term444 _132203 x'' f g s) = (term445 _132203 x'' f g s).
Proof. exact (@lem7075455 _132203 g (term439 _132203 x'' f g s)). Qed.
Lemma lem7075457 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term443 _132203 x'' f g s) = (term445 _132203 x'' f g s).
Proof. exact (TRANS (@lem7075452 _132203 x'' f g s) (@lem7075456 _132203 x'' f g s)). Qed.
Lemma lem7075458 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term446 _132203 x'' f g s) = (term447 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075391) (@lem7075424 _132203 x'' f g s)). Qed.
Lemma lem7075459 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term448 _132203 x'' f g s) = (term449 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075458 _132203 x'' f g s) (@lem7075457 _132203 x'' f g s)). Qed.
Lemma lem7075461 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075462 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7075461 real (real -> Prop) f x). Qed.
Lemma lem7075463 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term447 _132203 x'' f g s) = (term450 _132203 x'' f g s).
Proof. exact (@lem7075462 real_le (term442 _132203 x'' f g s)). Qed.
Lemma lem7075464 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term445 _132203 x'' f g s) = (term445 _132203 x'' f g s).
Proof. exact (eq_refl (term445 _132203 x'' f g s)). Qed.
Lemma lem7075465 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term449 _132203 x'' f g s) = (term451 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075463 _132203 x'' f g s) (@lem7075464 _132203 x'' f g s)). Qed.
Lemma lem7075467 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075468 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7075467 real Prop f x). Qed.
Lemma lem7075469 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term451 _132203 x'' f g s) = (term452 _132203 x'' f g s).
Proof. exact (@lem7075468 (term450 _132203 x'' f g s) (term445 _132203 x'' f g s)). Qed.
Lemma lem7075470 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term449 _132203 x'' f g s) = (term452 _132203 x'' f g s).
Proof. exact (TRANS (@lem7075465 _132203 x'' f g s) (@lem7075469 _132203 x'' f g s)). Qed.
Lemma lem7075471 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term448 _132203 x'' f g s) = (term452 _132203 x'' f g s).
Proof. exact (TRANS (@lem7075459 _132203 x'' f g s) (@lem7075470 _132203 x'' f g s)). Qed.
Lemma lem7075472 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term453 _132203 x'' f g s) = (term454 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075390) (@lem7075471 _132203 x'' f g s)). Qed.
Lemma lem7075473 {_132203 : Type'} : (@IN _132203) = (@IN _132203).
Proof. exact (eq_refl (@IN _132203)). Qed.
Lemma lem7075482 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075483 {_132203 : Type'} (f : type711 _132203) (x : _132203 -> real) : (f x) = (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) f x).
Proof. exact (@lem7075482 (_132203 -> real) (type710 _132203) f x). Qed.
Lemma lem7075484 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) : (x'' f) = (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) x'' f).
Proof. exact (@lem7075483 _132203 x'' f). Qed.
Lemma lem7075485 {_132203 : Type'} (g : _132203 -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7075486 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (x'' f g) = (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) x'' f g).
Proof. exact (MK_COMB (@lem7075484 _132203 x'' f) (@lem7075485 _132203 g)). Qed.
Lemma lem7075488 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075489 {_132203 : Type'} (f : type710 _132203) (x : _132203 -> real) : (f x) = (@I ((_132203 -> real) -> (_132203 -> Prop) -> _132203) f x).
Proof. exact (@lem7075488 (_132203 -> real) (type684 _132203) f x). Qed.
Lemma lem7075490 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) x'' f g) = (term437 _132203 x'' f g).
Proof. exact (@lem7075489 _132203 (@I ((_132203 -> real) -> (_132203 -> real) -> (_132203 -> Prop) -> _132203) x'' f) g). Qed.
Lemma lem7075491 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (x'' f g) = (term437 _132203 x'' f g).
Proof. exact (TRANS (@lem7075486 _132203 x'' f g) (@lem7075490 _132203 x'' f g)). Qed.
Lemma lem7075492 {_132203 : Type'} (s : _132203 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7075493 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (x'' f g s) = (term438 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075491 _132203 x'' f g) (@lem7075492 _132203 s)). Qed.
Lemma lem7075495 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075496 {_132203 : Type'} (f : type684 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> _132203) f x).
Proof. exact (@lem7075495 (_132203 -> Prop) _132203 f x). Qed.
Lemma lem7075497 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term438 _132203 x'' f g s) = (term439 _132203 x'' f g s).
Proof. exact (@lem7075496 _132203 (term437 _132203 x'' f g) s). Qed.
Lemma lem7075499 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (x'' f g s) = (term439 _132203 x'' f g s).
Proof. exact (TRANS (@lem7075493 _132203 x'' f g s) (@lem7075497 _132203 x'' f g s)). Qed.
Lemma lem7075500 {_132203 : Type'} (s : _132203 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7075501 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term455 _132203 x'' f g s) = (term456 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075473 _132203) (@lem7075499 _132203 x'' f g s)). Qed.
Lemma lem7075502 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term457 _132203 x'' f g s) = (term458 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075501 _132203 x'' f g s) (@lem7075500 _132203 s)). Qed.
Lemma lem7075504 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075505 {_132203 : Type'} (f : type1364 _132203) (x : _132203) : (f x) = (@I (_132203 -> (_132203 -> Prop) -> Prop) f x).
Proof. exact (@lem7075504 _132203 (type686 _132203) f x). Qed.
Lemma lem7075506 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term456 _132203 x'' f g s) = (term459 _132203 x'' f g s).
Proof. exact (@lem7075505 _132203 (@IN _132203) (term439 _132203 x'' f g s)). Qed.
Lemma lem7075507 {_132203 : Type'} (s : _132203 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7075508 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term458 _132203 x'' f g s) = (term460 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075506 _132203 x'' f g s) (@lem7075507 _132203 s)). Qed.
Lemma lem7075510 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075511 {_132203 : Type'} (f : type686 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> Prop) f x).
Proof. exact (@lem7075510 (_132203 -> Prop) Prop f x). Qed.
Lemma lem7075512 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term460 _132203 x'' f g s) = (term461 _132203 x'' f g s).
Proof. exact (@lem7075511 _132203 (term459 _132203 x'' f g s) s). Qed.
Lemma lem7075513 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term458 _132203 x'' f g s) = (term461 _132203 x'' f g s).
Proof. exact (TRANS (@lem7075508 _132203 x'' f g s) (@lem7075512 _132203 x'' f g s)). Qed.
Lemma lem7075514 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term457 _132203 x'' f g s) = (term461 _132203 x'' f g s).
Proof. exact (TRANS (@lem7075502 _132203 x'' f g s) (@lem7075513 _132203 x'' f g s)). Qed.
Lemma lem7075515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7075516 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term462 _132203 x'' f g s) = (term463 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075515) (@lem7075514 _132203 x'' f g s)). Qed.
Lemma lem7075517 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term464 _132203 x'' f g s) = (term465 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075516 _132203 x'' f g s) (@lem7075472 _132203 x'' f g s)). Qed.
Lemma lem7075518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7075519 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term466 _132203 x'' f g s) = (term467 _132203 x'' f g s).
Proof. exact (MK_COMB (@lem7075518) (@lem7075517 _132203 x'' f g s)). Qed.
Lemma lem7075520 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term468 _132203 x'' s f g) = (term469 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075519 _132203 x'' f g s) (@lem7075389 _132203 s f g)). Qed.
Lemma lem7075521 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7075526 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075527 {_132203 : Type'} (f : type686 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> Prop) f x).
Proof. exact (@lem7075526 (_132203 -> Prop) Prop f x). Qed.
Lemma lem7075529 {_132203 : Type'} (s : _132203 -> Prop) : (@FINITE _132203 s) = (@I ((_132203 -> Prop) -> Prop) (@FINITE _132203) s).
Proof. exact (@lem7075527 _132203 (@FINITE _132203) s). Qed.
Lemma lem7075530 {_132203 : Type'} (s : _132203 -> Prop) : (term170 _132203 s) = (term470 _132203 s).
Proof. exact (MK_COMB (@lem7075521) (@lem7075529 _132203 s)). Qed.
Lemma lem7075531 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7075532 {_132203 : Type'} (s : _132203 -> Prop) : (term134 _132203 s) = (term471 _132203 s).
Proof. exact (MK_COMB (@lem7075531) (@lem7075530 _132203 s)). Qed.
Lemma lem7075533 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term472 _132203 x'' s f g) = (term473 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075532 _132203 s) (@lem7075520 _132203 x'' s f g)). Qed.
Lemma lem7075534 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7075535 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term474 _132203 x'' s f g) = (term475 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075534) (@lem7075533 _132203 x'' s f g)). Qed.
Lemma lem7075536 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term476 _132203 x'' f s g) = (term477 _132203 x'' f s g).
Proof. exact (MK_COMB (@lem7075535 _132203 x'' s f g) (@lem7075332 _132203 f s g)). Qed.
Lemma lem7075537 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (term478 _132203 x'' f g) = (term479 _132203 x'' f g).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7075536 _132203 x'' f s g)). Qed.
Lemma lem7075538 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7075539 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (term480 _132203 x'' f g) = (term481 _132203 x'' f g).
Proof. exact (MK_COMB (@lem7075538 _132203) (@lem7075537 _132203 x'' f g)). Qed.
Lemma lem7075540 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) : (term482 _132203 x'' f) = (term483 _132203 x'' f).
Proof. exact (fun_ext (fun g : _132203 -> real => @lem7075539 _132203 x'' f g)). Qed.
Lemma lem7075541 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7075542 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) : (term267 _132203 x'' f) = (term484 _132203 x'' f).
Proof. exact (MK_COMB (@lem7075541 _132203) (@lem7075540 _132203 x'' f)). Qed.
Lemma lem7075543 {_132203 : Type'} (x'' : type711 _132203) : (term269 _132203 x'') = (term485 _132203 x'').
Proof. exact (fun_ext (fun f : _132203 -> real => @lem7075542 _132203 x'' f)). Qed.
Lemma lem7075544 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7075545 {_132203 : Type'} (x'' : type711 _132203) : (term271 _132203 x'') = (term486 _132203 x'').
Proof. exact (MK_COMB (@lem7075544 _132203) (@lem7075543 _132203 x'')). Qed.
Lemma lem7075546 {_132203 : Type'} (x'' : type711 _132203) (h1 : term271 _132203 x'') : term486 _132203 x''.
Proof. exact (EQ_MP (@lem7075545 _132203 x'') (@lem7074897 _132203 x'' h1)). Qed.
Lemma lem7075547 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7075548 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7075555 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075556 {_132203 : Type'} (f : type646 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) f x).
Proof. exact (@lem7075555 (_132203 -> Prop) (type717 _132203) f x). Qed.
Lemma lem7075557 {_132203 : Type'} (s : _132203 -> Prop) : (@sum _132203 s) = (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s).
Proof. exact (@lem7075556 _132203 (@sum _132203) s). Qed.
Lemma lem7075558 {_132203 : Type'} (f : _132203 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7075559 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) : (@sum _132203 s f) = (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s f).
Proof. exact (MK_COMB (@lem7075557 _132203 s) (@lem7075558 _132203 f)). Qed.
Lemma lem7075561 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075562 {_132203 : Type'} (f : type717 _132203) (x : _132203 -> real) : (f x) = (@I ((_132203 -> real) -> real) f x).
Proof. exact (@lem7075561 (_132203 -> real) real f x). Qed.
Lemma lem7075563 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) : (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s f) = (term417 _132203 s f).
Proof. exact (@lem7075562 _132203 (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s) f). Qed.
Lemma lem7075565 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) : (@sum _132203 s f) = (term417 _132203 s f).
Proof. exact (TRANS (@lem7075559 _132203 s f) (@lem7075563 _132203 s f)). Qed.
Lemma lem7075572 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075573 {_132203 : Type'} (f : type646 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) f x).
Proof. exact (@lem7075572 (_132203 -> Prop) (type717 _132203) f x). Qed.
Lemma lem7075574 {_132203 : Type'} (s : _132203 -> Prop) : (@sum _132203 s) = (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s).
Proof. exact (@lem7075573 _132203 (@sum _132203) s). Qed.
Lemma lem7075575 {_132203 : Type'} (g : _132203 -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7075576 {_132203 : Type'} (s : _132203 -> Prop) (g : _132203 -> real) : (@sum _132203 s g) = (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s g).
Proof. exact (MK_COMB (@lem7075574 _132203 s) (@lem7075575 _132203 g)). Qed.
Lemma lem7075578 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075579 {_132203 : Type'} (f : type717 _132203) (x : _132203 -> real) : (f x) = (@I ((_132203 -> real) -> real) f x).
Proof. exact (@lem7075578 (_132203 -> real) real f x). Qed.
Lemma lem7075580 {_132203 : Type'} (s : _132203 -> Prop) (g : _132203 -> real) : (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s g) = (term417 _132203 s g).
Proof. exact (@lem7075579 _132203 (@I ((_132203 -> Prop) -> (_132203 -> real) -> real) (@sum _132203) s) g). Qed.
Lemma lem7075582 {_132203 : Type'} (s : _132203 -> Prop) (g : _132203 -> real) : (@sum _132203 s g) = (term417 _132203 s g).
Proof. exact (TRANS (@lem7075576 _132203 s g) (@lem7075580 _132203 s g)). Qed.
Lemma lem7075583 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) : (term418 _132203 s f) = (term419 _132203 s f).
Proof. exact (MK_COMB (@lem7075548) (@lem7075565 _132203 s f)). Qed.
Lemma lem7075584 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term39 _132203 f s g) = (term420 _132203 f s g).
Proof. exact (MK_COMB (@lem7075583 _132203 s f) (@lem7075582 _132203 s g)). Qed.
Lemma lem7075586 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075587 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7075586 real (real -> Prop) f x). Qed.
Lemma lem7075588 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) : (term419 _132203 s f) = (term421 _132203 s f).
Proof. exact (@lem7075587 real_lt (term417 _132203 s f)). Qed.
Lemma lem7075589 {_132203 : Type'} (s : _132203 -> Prop) (g : _132203 -> real) : (term417 _132203 s g) = (term417 _132203 s g).
Proof. exact (eq_refl (term417 _132203 s g)). Qed.
Lemma lem7075590 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term420 _132203 f s g) = (term422 _132203 f s g).
Proof. exact (MK_COMB (@lem7075588 _132203 s f) (@lem7075589 _132203 s g)). Qed.
Lemma lem7075592 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075593 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7075592 real Prop f x). Qed.
Lemma lem7075594 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term422 _132203 f s g) = (term423 _132203 f s g).
Proof. exact (@lem7075593 (term421 _132203 s f) (term417 _132203 s g)). Qed.
Lemma lem7075595 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term420 _132203 f s g) = (term423 _132203 f s g).
Proof. exact (TRANS (@lem7075590 _132203 f s g) (@lem7075594 _132203 f s g)). Qed.
Lemma lem7075596 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term39 _132203 f s g) = (term423 _132203 f s g).
Proof. exact (TRANS (@lem7075584 _132203 f s g) (@lem7075595 _132203 f s g)). Qed.
Lemma lem7075597 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term76 _132203 f s g) = (term487 _132203 f s g).
Proof. exact (MK_COMB (@lem7075547) (@lem7075596 _132203 f s g)). Qed.
Lemma lem7075598 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7075603 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075605 {_132203 : Type'} (f : _132203 -> real) (x : _132203) : (f x) = (@I (_132203 -> real) f x).
Proof. exact (@lem7075603 _132203 real f x). Qed.
Lemma lem7075610 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075611 {_132203 : Type'} (f : _132203 -> real) (x : _132203) : (f x) = (@I (_132203 -> real) f x).
Proof. exact (@lem7075610 _132203 real f x). Qed.
Lemma lem7075613 {_132203 : Type'} (g : _132203 -> real) (x : _132203) : (g x) = (@I (_132203 -> real) g x).
Proof. exact (@lem7075611 _132203 g x). Qed.
Lemma lem7075614 {_132203 : Type'} (f : _132203 -> real) (x : _132203) : (term424 _132203 f x) = (term425 _132203 f x).
Proof. exact (MK_COMB (@lem7075598) (@lem7075605 _132203 f x)). Qed.
Lemma lem7075615 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term71 _132203 f g x) = (term426 _132203 f g x).
Proof. exact (MK_COMB (@lem7075614 _132203 f x) (@lem7075613 _132203 g x)). Qed.
Lemma lem7075617 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075618 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7075617 real (real -> Prop) f x). Qed.
Lemma lem7075619 {_132203 : Type'} (f : _132203 -> real) (x : _132203) : (term425 _132203 f x) = (term427 _132203 f x).
Proof. exact (@lem7075618 real_lt (@I (_132203 -> real) f x)). Qed.
Lemma lem7075620 {_132203 : Type'} (g : _132203 -> real) (x : _132203) : (@I (_132203 -> real) g x) = (@I (_132203 -> real) g x).
Proof. exact (eq_refl (@I (_132203 -> real) g x)). Qed.
Lemma lem7075621 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term426 _132203 f g x) = (term428 _132203 f g x).
Proof. exact (MK_COMB (@lem7075619 _132203 f x) (@lem7075620 _132203 g x)). Qed.
Lemma lem7075623 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075624 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7075623 real Prop f x). Qed.
Lemma lem7075625 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term428 _132203 f g x) = (term429 _132203 f g x).
Proof. exact (@lem7075624 (term427 _132203 f x) (@I (_132203 -> real) g x)). Qed.
Lemma lem7075626 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term426 _132203 f g x) = (term429 _132203 f g x).
Proof. exact (TRANS (@lem7075621 _132203 f g x) (@lem7075625 _132203 f g x)). Qed.
Lemma lem7075627 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term71 _132203 f g x) = (term429 _132203 f g x).
Proof. exact (TRANS (@lem7075615 _132203 f g x) (@lem7075626 _132203 f g x)). Qed.
Lemma lem7075628 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7075635 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075636 {_132203 : Type'} (f : type1364 _132203) (x : _132203) : (f x) = (@I (_132203 -> (_132203 -> Prop) -> Prop) f x).
Proof. exact (@lem7075635 _132203 (type686 _132203) f x). Qed.
Lemma lem7075637 {_132203 : Type'} (x : _132203) : (@IN _132203 x) = (@I (_132203 -> (_132203 -> Prop) -> Prop) (@IN _132203) x).
Proof. exact (@lem7075636 _132203 (@IN _132203) x). Qed.
Lemma lem7075638 {_132203 : Type'} (s : _132203 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7075639 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (@IN _132203 x s) = (@I (_132203 -> (_132203 -> Prop) -> Prop) (@IN _132203) x s).
Proof. exact (MK_COMB (@lem7075637 _132203 x) (@lem7075638 _132203 s)). Qed.
Lemma lem7075641 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075642 {_132203 : Type'} (f : type686 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> Prop) f x).
Proof. exact (@lem7075641 (_132203 -> Prop) Prop f x). Qed.
Lemma lem7075643 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (@I (_132203 -> (_132203 -> Prop) -> Prop) (@IN _132203) x s) = (term395 _132203 x s).
Proof. exact (@lem7075642 _132203 (@I (_132203 -> (_132203 -> Prop) -> Prop) (@IN _132203) x) s). Qed.
Lemma lem7075645 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (@IN _132203 x s) = (term395 _132203 x s).
Proof. exact (TRANS (@lem7075639 _132203 x s) (@lem7075643 _132203 x s)). Qed.
Lemma lem7075646 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term284 _132203 x s) = (term396 _132203 x s).
Proof. exact (MK_COMB (@lem7075628) (@lem7075645 _132203 x s)). Qed.
Lemma lem7075647 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7075648 {_132203 : Type'} (x : _132203) (s : _132203 -> Prop) : (term432 _132203 x s) = (term433 _132203 x s).
Proof. exact (MK_COMB (@lem7075647) (@lem7075646 _132203 x s)). Qed.
Lemma lem7075649 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term70 _132203 s f g x) = (term488 _132203 s f g x).
Proof. exact (MK_COMB (@lem7075648 _132203 x s) (@lem7075627 _132203 f g x)). Qed.
Lemma lem7075650 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term72 _132203 s f g) = (term489 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7075649 _132203 s f g x)). Qed.
Lemma lem7075651 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7075652 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term73 _132203 s f g) = (term490 _132203 s f g).
Proof. exact (MK_COMB (@lem7075651 _132203) (@lem7075650 _132203 s f g)). Qed.
Lemma lem7075661 {_132203 : Type'} (s : _132203 -> Prop) : (term60 _132203 s) = (term60 _132203 s).
Proof. exact (eq_refl (term60 _132203 s)). Qed.
Lemma lem7075662 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term74 _132203 s f g) = (term491 _132203 s f g).
Proof. exact (MK_COMB (@lem7075661 _132203 s) (@lem7075652 _132203 s f g)). Qed.
Lemma lem7075667 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7075668 {_132203 : Type'} (f : type686 _132203) (x : _132203 -> Prop) : (f x) = (@I ((_132203 -> Prop) -> Prop) f x).
Proof. exact (@lem7075667 (_132203 -> Prop) Prop f x). Qed.
Lemma lem7075670 {_132203 : Type'} (s : _132203 -> Prop) : (@FINITE _132203 s) = (@I ((_132203 -> Prop) -> Prop) (@FINITE _132203) s).
Proof. exact (@lem7075668 _132203 (@FINITE _132203) s). Qed.
Lemma lem7075671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7075672 {_132203 : Type'} (s : _132203 -> Prop) : (term48 _132203 s) = (term492 _132203 s).
Proof. exact (MK_COMB (@lem7075671) (@lem7075670 _132203 s)). Qed.
Lemma lem7075673 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term75 _132203 s f g) = (term493 _132203 s f g).
Proof. exact (MK_COMB (@lem7075672 _132203 s) (@lem7075662 _132203 s f g)). Qed.
Lemma lem7075674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7075675 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term78 _132203 s f g) = (term494 _132203 s f g).
Proof. exact (MK_COMB (@lem7075674) (@lem7075673 _132203 s f g)). Qed.
Lemma lem7075676 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term80 _132203 f s g) = (term495 _132203 f s g).
Proof. exact (MK_COMB (@lem7075675 _132203 s f g) (@lem7075597 _132203 f s g)). Qed.
Lemma lem7075677 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term495 _132203 f s g.
Proof. exact (EQ_MP (@lem7075676 _132203 f s g) (@lem7074900 _132203 f s g h1)). Qed.
Lemma lem7075679 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term493 _132203 s f g.
Proof. exact (proj1 (@lem7075677 _132203 f s g h1)). Qed.
Lemma lem7075680 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term491 _132203 s f g.
Proof. exact (proj2 (@lem7075679 _132203 f s g h1)). Qed.
Lemma lem7075682 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term490 _132203 s f g.
Proof. exact (proj2 (@lem7075680 _132203 f s g h1)). Qed.
Lemma lem7075685 {_132203 : Type'} (x : type684 _132203) (h1 : term380 _132203 x) : term414 _132203 x.
Proof. exact (proj1 (@lem7075020 _132203 x h1)). Qed.
Lemma lem7075693 (x : real) (y : real) : (term390 x y) = (term390 x y).
Proof. exact (eq_refl (term390 x y)). Qed.
Lemma lem7075694 (x : real) : (term391 x) = (term391 x).
Proof. exact (fun_ext (fun y : real => @lem7075693 x y)). Qed.
Lemma lem7075695 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7075696 (x : real) : (term392 x) = (term392 x).
Proof. exact (MK_COMB (@lem7075695) (@lem7075694 x)). Qed.
Lemma lem7075697 : term393 = term393.
Proof. exact (fun_ext (fun x : real => @lem7075696 x)). Qed.
Lemma lem7075698 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7075700 : term394 = term394.
Proof. exact (MK_COMB (@lem7075698) (@lem7075697)). Qed.
Lemma lem7075701 (h1 : term38) : term394.
Proof. exact (EQ_MP (@lem7075700) (@lem7074946 h1)). Qed.
Lemma lem7075845 {A : Type'} (P : Prop) (Q : A -> Prop) : (term496 A P Q) = (term497 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7075846 {_132203 : Type'} (P : Prop) (Q : _132203 -> Prop) : (term496 _132203 P Q) = (term497 _132203 P Q).
Proof. exact (@lem7075845 _132203 P Q). Qed.
Lemma lem7075847 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term498 _132203 x'' s f g) = (term499 _132203 x'' s f g).
Proof. exact (@lem7075846 _132203 (term465 _132203 x'' f g s) (term435 _132203 s f g)). Qed.
Lemma lem7075848 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term500 _132203 s f g x) = (term434 _132203 s f g x).
Proof. exact (eq_refl (term500 _132203 s f g x)). Qed.
Lemma lem7075849 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term501 _132203 s f g) = (term435 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7075848 _132203 s f g x)). Qed.
Lemma lem7075850 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7075851 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term502 _132203 s f g) = (term436 _132203 s f g).
Proof. exact (MK_COMB (@lem7075850 _132203) (@lem7075849 _132203 s f g)). Qed.
Lemma lem7075852 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term467 _132203 x'' f g s) = (term467 _132203 x'' f g s).
Proof. exact (eq_refl (term467 _132203 x'' f g s)). Qed.
Lemma lem7075853 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term498 _132203 x'' s f g) = (term469 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075852 _132203 x'' f g s) (@lem7075851 _132203 s f g)). Qed.
Lemma lem7075854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7075855 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term503 _132203 x'' s f g) = (term504 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075854) (@lem7075853 _132203 x'' s f g)). Qed.
Lemma lem7075856 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term500 _132203 s f g x) = (term434 _132203 s f g x).
Proof. exact (eq_refl (term500 _132203 s f g x)). Qed.
Lemma lem7075857 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term467 _132203 x'' f g s) = (term467 _132203 x'' f g s).
Proof. exact (eq_refl (term467 _132203 x'' f g s)). Qed.
Lemma lem7075858 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term505 _132203 x'' s f g x) = (term506 _132203 x'' s f g x).
Proof. exact (MK_COMB (@lem7075857 _132203 x'' f g s) (@lem7075856 _132203 s f g x)). Qed.
Lemma lem7075859 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term507 _132203 x'' s f g) = (term508 _132203 x'' s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7075858 _132203 x'' s f g x)). Qed.
Lemma lem7075860 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7075861 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term499 _132203 x'' s f g) = (term509 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075860 _132203) (@lem7075859 _132203 x'' s f g)). Qed.
Lemma lem7075862 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : ((term498 _132203 x'' s f g) = (term499 _132203 x'' s f g)) = ((term469 _132203 x'' s f g) = (term509 _132203 x'' s f g)).
Proof. exact (MK_COMB (@lem7075855 _132203 x'' s f g) (@lem7075861 _132203 x'' s f g)). Qed.
Lemma lem7075863 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term469 _132203 x'' s f g) = (term509 _132203 x'' s f g).
Proof. exact (EQ_MP (@lem7075862 _132203 x'' s f g) (@lem7075847 _132203 x'' s f g)). Qed.
Lemma lem7075864 {_132203 : Type'} (s : _132203 -> Prop) : (term471 _132203 s) = (term471 _132203 s).
Proof. exact (eq_refl (term471 _132203 s)). Qed.
Lemma lem7075865 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term473 _132203 x'' s f g) = (term510 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075864 _132203 s) (@lem7075863 _132203 x'' s f g)). Qed.
Lemma lem7075867 {A : Type'} (P : Prop) (Q : A -> Prop) : (term496 A P Q) = (term497 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7075868 {_132203 : Type'} (P : Prop) (Q : _132203 -> Prop) : (term496 _132203 P Q) = (term497 _132203 P Q).
Proof. exact (@lem7075867 _132203 P Q). Qed.
Lemma lem7075869 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term511 _132203 x'' s f g) = (term512 _132203 x'' s f g).
Proof. exact (@lem7075868 _132203 (term470 _132203 s) (term508 _132203 x'' s f g)). Qed.
Lemma lem7075870 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term513 _132203 x'' s f g x) = (term506 _132203 x'' s f g x).
Proof. exact (eq_refl (term513 _132203 x'' s f g x)). Qed.
Lemma lem7075871 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term514 _132203 x'' s f g) = (term508 _132203 x'' s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7075870 _132203 x'' s f g x)). Qed.
Lemma lem7075872 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7075873 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term515 _132203 x'' s f g) = (term509 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075872 _132203) (@lem7075871 _132203 x'' s f g)). Qed.
Lemma lem7075874 {_132203 : Type'} (s : _132203 -> Prop) : (term471 _132203 s) = (term471 _132203 s).
Proof. exact (eq_refl (term471 _132203 s)). Qed.
Lemma lem7075875 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term511 _132203 x'' s f g) = (term510 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075874 _132203 s) (@lem7075873 _132203 x'' s f g)). Qed.
Lemma lem7075876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7075877 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term516 _132203 x'' s f g) = (term517 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075876) (@lem7075875 _132203 x'' s f g)). Qed.
Lemma lem7075878 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term513 _132203 x'' s f g x) = (term506 _132203 x'' s f g x).
Proof. exact (eq_refl (term513 _132203 x'' s f g x)). Qed.
Lemma lem7075879 {_132203 : Type'} (s : _132203 -> Prop) : (term471 _132203 s) = (term471 _132203 s).
Proof. exact (eq_refl (term471 _132203 s)). Qed.
Lemma lem7075880 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term518 _132203 x'' s f g x) = (term519 _132203 x'' s f g x).
Proof. exact (MK_COMB (@lem7075879 _132203 s) (@lem7075878 _132203 x'' s f g x)). Qed.
Lemma lem7075881 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term520 _132203 x'' s f g) = (term521 _132203 x'' s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7075880 _132203 x'' s f g x)). Qed.
Lemma lem7075882 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7075883 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term512 _132203 x'' s f g) = (term522 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075882 _132203) (@lem7075881 _132203 x'' s f g)). Qed.
Lemma lem7075884 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : ((term511 _132203 x'' s f g) = (term512 _132203 x'' s f g)) = ((term510 _132203 x'' s f g) = (term522 _132203 x'' s f g)).
Proof. exact (MK_COMB (@lem7075877 _132203 x'' s f g) (@lem7075883 _132203 x'' s f g)). Qed.
Lemma lem7075885 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term510 _132203 x'' s f g) = (term522 _132203 x'' s f g).
Proof. exact (EQ_MP (@lem7075884 _132203 x'' s f g) (@lem7075869 _132203 x'' s f g)). Qed.
Lemma lem7075886 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term473 _132203 x'' s f g) = (term522 _132203 x'' s f g).
Proof. exact (TRANS (@lem7075865 _132203 x'' s f g) (@lem7075885 _132203 x'' s f g)). Qed.
Lemma lem7075887 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7075888 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term475 _132203 x'' s f g) = (term523 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075887) (@lem7075886 _132203 x'' s f g)). Qed.
Lemma lem7075889 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term423 _132203 f s g) = (term423 _132203 f s g).
Proof. exact (eq_refl (term423 _132203 f s g)). Qed.
Lemma lem7075890 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term477 _132203 x'' f s g) = (term524 _132203 x'' f s g).
Proof. exact (MK_COMB (@lem7075888 _132203 x'' s f g) (@lem7075889 _132203 f s g)). Qed.
Lemma lem7075892 {A : Type'} (P : A -> Prop) (Q : Prop) : (term525 A P Q) = (term526 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem7075893 {_132203 : Type'} (P : _132203 -> Prop) (Q : Prop) : (term525 _132203 P Q) = (term526 _132203 P Q).
Proof. exact (@lem7075892 _132203 P Q). Qed.
Lemma lem7075894 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term527 _132203 x'' f s g) = (term528 _132203 x'' f s g).
Proof. exact (@lem7075893 _132203 (term521 _132203 x'' s f g) (term423 _132203 f s g)). Qed.
Lemma lem7075895 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term529 _132203 x'' s f g x) = (term519 _132203 x'' s f g x).
Proof. exact (eq_refl (term529 _132203 x'' s f g x)). Qed.
Lemma lem7075896 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term530 _132203 x'' s f g) = (term521 _132203 x'' s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7075895 _132203 x'' s f g x)). Qed.
Lemma lem7075897 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7075898 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term531 _132203 x'' s f g) = (term522 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075897 _132203) (@lem7075896 _132203 x'' s f g)). Qed.
Lemma lem7075899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7075900 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term532 _132203 x'' s f g) = (term523 _132203 x'' s f g).
Proof. exact (MK_COMB (@lem7075899) (@lem7075898 _132203 x'' s f g)). Qed.
Lemma lem7075901 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term423 _132203 f s g) = (term423 _132203 f s g).
Proof. exact (eq_refl (term423 _132203 f s g)). Qed.
Lemma lem7075902 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term527 _132203 x'' f s g) = (term524 _132203 x'' f s g).
Proof. exact (MK_COMB (@lem7075900 _132203 x'' s f g) (@lem7075901 _132203 f s g)). Qed.
Lemma lem7075903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7075904 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term533 _132203 x'' f s g) = (term534 _132203 x'' f s g).
Proof. exact (MK_COMB (@lem7075903) (@lem7075902 _132203 x'' f s g)). Qed.
Lemma lem7075905 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term529 _132203 x'' s f g x) = (term519 _132203 x'' s f g x).
Proof. exact (eq_refl (term529 _132203 x'' s f g x)). Qed.
Lemma lem7075906 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7075907 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term535 _132203 x'' s f g x) = (term536 _132203 x'' s f g x).
Proof. exact (MK_COMB (@lem7075906) (@lem7075905 _132203 x'' s f g x)). Qed.
Lemma lem7075908 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term423 _132203 f s g) = (term423 _132203 f s g).
Proof. exact (eq_refl (term423 _132203 f s g)). Qed.
Lemma lem7075909 {_132203 : Type'} (x'' : type711 _132203) (x : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term537 _132203 x'' x f s g) = (term538 _132203 x'' x f s g).
Proof. exact (MK_COMB (@lem7075907 _132203 x'' s f g x) (@lem7075908 _132203 f s g)). Qed.
Lemma lem7075910 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term539 _132203 x'' f s g) = (term540 _132203 x'' f s g).
Proof. exact (fun_ext (fun x : _132203 => @lem7075909 _132203 x'' x f s g)). Qed.
Lemma lem7075911 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7075912 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term528 _132203 x'' f s g) = (term541 _132203 x'' f s g).
Proof. exact (MK_COMB (@lem7075911 _132203) (@lem7075910 _132203 x'' f s g)). Qed.
Lemma lem7075913 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : ((term527 _132203 x'' f s g) = (term528 _132203 x'' f s g)) = ((term524 _132203 x'' f s g) = (term541 _132203 x'' f s g)).
Proof. exact (MK_COMB (@lem7075904 _132203 x'' f s g) (@lem7075912 _132203 x'' f s g)). Qed.
Lemma lem7075914 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term524 _132203 x'' f s g) = (term541 _132203 x'' f s g).
Proof. exact (EQ_MP (@lem7075913 _132203 x'' f s g) (@lem7075894 _132203 x'' f s g)). Qed.
Lemma lem7075915 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term477 _132203 x'' f s g) = (term541 _132203 x'' f s g).
Proof. exact (TRANS (@lem7075890 _132203 x'' f s g) (@lem7075914 _132203 x'' f s g)). Qed.
Lemma lem7075916 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (term479 _132203 x'' f g) = (term542 _132203 x'' f g).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7075915 _132203 x'' f s g)). Qed.
Lemma lem7075917 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7075918 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (term481 _132203 x'' f g) = (term543 _132203 x'' f g).
Proof. exact (MK_COMB (@lem7075917 _132203) (@lem7075916 _132203 x'' f g)). Qed.
Lemma lem7075919 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) : (term483 _132203 x'' f) = (term544 _132203 x'' f).
Proof. exact (fun_ext (fun g : _132203 -> real => @lem7075918 _132203 x'' f g)). Qed.
Lemma lem7075920 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7075921 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) : (term484 _132203 x'' f) = (term545 _132203 x'' f).
Proof. exact (MK_COMB (@lem7075920 _132203) (@lem7075919 _132203 x'' f)). Qed.
Lemma lem7075922 {_132203 : Type'} (x'' : type711 _132203) : (term485 _132203 x'') = (term546 _132203 x'').
Proof. exact (fun_ext (fun f : _132203 -> real => @lem7075921 _132203 x'' f)). Qed.
Lemma lem7075923 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7075924 {_132203 : Type'} (x'' : type711 _132203) : (term486 _132203 x'') = (term547 _132203 x'').
Proof. exact (MK_COMB (@lem7075923 _132203) (@lem7075922 _132203 x'')). Qed.
Lemma lem7075925 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term423 _132203 f s g) = (term423 _132203 f s g).
Proof. exact (eq_refl (term423 _132203 f s g)). Qed.
Lemma lem7075948 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term506 _132203 x'' s f g x) = (term548 _132203 x'' s f g x).
Proof. exact (@lem19699 (term461 _132203 x'' f g s) (term454 _132203 x'' f g s) (term434 _132203 s f g x)). Qed.
Lemma lem7075951 {_132203 : Type'} (s : _132203 -> Prop) : (term471 _132203 s) = (term471 _132203 s).
Proof. exact (eq_refl (term471 _132203 s)). Qed.
Lemma lem7075952 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term519 _132203 x'' s f g x) = (term549 _132203 x'' s f g x).
Proof. exact (MK_COMB (@lem7075951 _132203 s) (@lem7075948 _132203 x'' s f g x)). Qed.
Lemma lem7075959 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term549 _132203 x'' s f g x) = (term550 _132203 x'' s f g x).
Proof. exact (@lem19490 (term551 _132203 x'' s f g x) (term470 _132203 s) (term552 _132203 x'' s f g x)). Qed.
Lemma lem7075960 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term519 _132203 x'' s f g x) = (term550 _132203 x'' s f g x).
Proof. exact (TRANS (@lem7075952 _132203 x'' s f g x) (@lem7075959 _132203 x'' s f g x)). Qed.
Lemma lem7075961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7075962 {_132203 : Type'} (x'' : type711 _132203) (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term536 _132203 x'' s f g x) = (term553 _132203 x'' s f g x).
Proof. exact (MK_COMB (@lem7075961) (@lem7075960 _132203 x'' s f g x)). Qed.
Lemma lem7075963 {_132203 : Type'} (x'' : type711 _132203) (x : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term538 _132203 x'' x f s g) = (term554 _132203 x'' x f s g).
Proof. exact (MK_COMB (@lem7075962 _132203 x'' s f g x) (@lem7075925 _132203 f s g)). Qed.
Lemma lem7075970 {_132203 : Type'} (x'' : type711 _132203) (x : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term554 _132203 x'' x f s g) = (term555 _132203 x'' x f s g).
Proof. exact (@lem19699 (term556 _132203 x'' s f g x) (term557 _132203 x'' s f g x) (term423 _132203 f s g)). Qed.
Lemma lem7075971 {_132203 : Type'} (x'' : type711 _132203) (x : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term538 _132203 x'' x f s g) = (term555 _132203 x'' x f s g).
Proof. exact (TRANS (@lem7075963 _132203 x'' x f s g) (@lem7075970 _132203 x'' x f s g)). Qed.
Lemma lem7075972 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term540 _132203 x'' f s g) = (term558 _132203 x'' f s g).
Proof. exact (fun_ext (fun x : _132203 => @lem7075971 _132203 x'' x f s g)). Qed.
Lemma lem7075973 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7075974 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term541 _132203 x'' f s g) = (term559 _132203 x'' f s g).
Proof. exact (MK_COMB (@lem7075973 _132203) (@lem7075972 _132203 x'' f s g)). Qed.
Lemma lem7075975 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (term542 _132203 x'' f g) = (term560 _132203 x'' f g).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7075974 _132203 x'' f s g)). Qed.
Lemma lem7075976 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7075977 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) : (term543 _132203 x'' f g) = (term561 _132203 x'' f g).
Proof. exact (MK_COMB (@lem7075976 _132203) (@lem7075975 _132203 x'' f g)). Qed.
Lemma lem7075978 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) : (term544 _132203 x'' f) = (term562 _132203 x'' f).
Proof. exact (fun_ext (fun g : _132203 -> real => @lem7075977 _132203 x'' f g)). Qed.
Lemma lem7075979 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7075980 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) : (term545 _132203 x'' f) = (term563 _132203 x'' f).
Proof. exact (MK_COMB (@lem7075979 _132203) (@lem7075978 _132203 x'' f)). Qed.
Lemma lem7075981 {_132203 : Type'} (x'' : type711 _132203) : (term546 _132203 x'') = (term564 _132203 x'').
Proof. exact (fun_ext (fun f : _132203 -> real => @lem7075980 _132203 x'' f)). Qed.
Lemma lem7075982 {_132203 : Type'} : (@all (_132203 -> real)) = (@all (_132203 -> real)).
Proof. exact (eq_refl (@all (_132203 -> real))). Qed.
Lemma lem7075983 {_132203 : Type'} (x'' : type711 _132203) : (term547 _132203 x'') = (term565 _132203 x'').
Proof. exact (MK_COMB (@lem7075982 _132203) (@lem7075981 _132203 x'')). Qed.
Lemma lem7075984 {_132203 : Type'} (x'' : type711 _132203) : (term486 _132203 x'') = (term565 _132203 x'').
Proof. exact (TRANS (@lem7075924 _132203 x'') (@lem7075983 _132203 x'')). Qed.
Lemma lem7075985 {_132203 : Type'} (x'' : type711 _132203) (h1 : term271 _132203 x'') : term565 _132203 x''.
Proof. exact (EQ_MP (@lem7075984 _132203 x'') (@lem7075546 _132203 x'' h1)). Qed.
Lemma lem7076005 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (x : _132203) : (term488 _132203 s f g x) = (term488 _132203 s f g x).
Proof. exact (eq_refl (term488 _132203 s f g x)). Qed.
Lemma lem7076006 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term489 _132203 s f g) = (term489 _132203 s f g).
Proof. exact (fun_ext (fun x : _132203 => @lem7076005 _132203 s f g x)). Qed.
Lemma lem7076007 {_132203 : Type'} : (@all _132203) = (@all _132203).
Proof. exact (eq_refl (@all _132203)). Qed.
Lemma lem7076009 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) : (term490 _132203 s f g) = (term490 _132203 s f g).
Proof. exact (MK_COMB (@lem7076007 _132203) (@lem7076006 _132203 s f g)). Qed.
Lemma lem7076010 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term490 _132203 s f g.
Proof. exact (EQ_MP (@lem7076009 _132203 s f g) (@lem7075682 _132203 f s g h1)). Qed.
Lemma lem7076018 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term412 _132203 x s) = (term412 _132203 x s).
Proof. exact (eq_refl (term412 _132203 x s)). Qed.
Lemma lem7076019 {_132203 : Type'} (x : type684 _132203) : (term413 _132203 x) = (term413 _132203 x).
Proof. exact (fun_ext (fun s : _132203 -> Prop => @lem7076018 _132203 x s)). Qed.
Lemma lem7076020 {_132203 : Type'} : (@all (_132203 -> Prop)) = (@all (_132203 -> Prop)).
Proof. exact (eq_refl (@all (_132203 -> Prop))). Qed.
Lemma lem7076022 {_132203 : Type'} (x : type684 _132203) : (term414 _132203 x) = (term414 _132203 x).
Proof. exact (MK_COMB (@lem7076020 _132203) (@lem7076019 _132203 x)). Qed.
Lemma lem7076023 {_132203 : Type'} (x : type684 _132203) (h1 : term380 _132203 x) : term414 _132203 x.
Proof. exact (EQ_MP (@lem7076022 _132203 x) (@lem7075685 _132203 x h1)). Qed.
Lemma lem7076066 (_94369 : real) (h1 : term38) : term566 _94369.
Proof. exact (@lem7075701 h1 _94369). Qed.
Lemma lem7076067 (_94369 : real) : (term566 _94369) = (term392 _94369).
Proof. exact (eq_refl (term566 _94369)). Qed.
Lemma lem7076068 (_94369 : real) (h1 : term38) : term392 _94369.
Proof. exact (EQ_MP (@lem7076067 _94369) (@lem7076066 _94369 h1)). Qed.
Lemma lem7076069 (_94369 : real) (_94370 : real) (h1 : term38) : term567 _94369 _94370.
Proof. exact (@lem7076068 _94369 h1 _94370). Qed.
Lemma lem7076070 (_94369 : real) (_94370 : real) : (term567 _94369 _94370) = (term390 _94369 _94370).
Proof. exact (eq_refl (term567 _94369 _94370)). Qed.
Lemma lem7076084 {_132203 : Type'} (_94375 : _132203 -> real) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term568 _132203 x'' _94375.
Proof. exact (@lem7075985 _132203 x'' h1 _94375). Qed.
Lemma lem7076085 {_132203 : Type'} (x'' : type711 _132203) (_94375 : _132203 -> real) : (term568 _132203 x'' _94375) = (term563 _132203 x'' _94375).
Proof. exact (eq_refl (term568 _132203 x'' _94375)). Qed.
Lemma lem7076086 {_132203 : Type'} (_94375 : _132203 -> real) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term563 _132203 x'' _94375.
Proof. exact (EQ_MP (@lem7076085 _132203 x'' _94375) (@lem7076084 _132203 _94375 x'' h1)). Qed.
Lemma lem7076087 {_132203 : Type'} (_94375 : _132203 -> real) (_94376 : _132203 -> real) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term569 _132203 x'' _94375 _94376.
Proof. exact (@lem7076086 _132203 _94375 x'' h1 _94376). Qed.
Lemma lem7076088 {_132203 : Type'} (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) : (term569 _132203 x'' _94375 _94376) = (term561 _132203 x'' _94375 _94376).
Proof. exact (eq_refl (term569 _132203 x'' _94375 _94376)). Qed.
Lemma lem7076089 {_132203 : Type'} (_94375 : _132203 -> real) (_94376 : _132203 -> real) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term561 _132203 x'' _94375 _94376.
Proof. exact (EQ_MP (@lem7076088 _132203 x'' _94375 _94376) (@lem7076087 _132203 _94375 _94376 x'' h1)). Qed.
Lemma lem7076090 {_132203 : Type'} (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term570 _132203 x'' _94375 _94376 _94377.
Proof. exact (@lem7076089 _132203 _94375 _94376 x'' h1 _94377). Qed.
Lemma lem7076091 {_132203 : Type'} (x'' : type711 _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term570 _132203 x'' _94375 _94376 _94377) = (term559 _132203 x'' _94375 _94377 _94376).
Proof. exact (eq_refl (term570 _132203 x'' _94375 _94376 _94377)). Qed.
Lemma lem7076092 {_132203 : Type'} (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term559 _132203 x'' _94375 _94377 _94376.
Proof. exact (EQ_MP (@lem7076091 _132203 x'' _94375 _94377 _94376) (@lem7076090 _132203 _94375 _94376 _94377 x'' h1)). Qed.
Lemma lem7076093 {_132203 : Type'} (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) (_94378 : _132203) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term571 _132203 x'' _94375 _94377 _94376 _94378.
Proof. exact (@lem7076092 _132203 _94375 _94377 _94376 x'' h1 _94378). Qed.
Lemma lem7076094 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term571 _132203 x'' _94375 _94377 _94376 _94378) = (term555 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (eq_refl (term571 _132203 x'' _94375 _94377 _94376 _94378)). Qed.
Lemma lem7076095 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term555 _132203 x'' _94378 _94375 _94377 _94376.
Proof. exact (EQ_MP (@lem7076094 _132203 x'' _94378 _94375 _94377 _94376) (@lem7076093 _132203 _94375 _94377 _94376 _94378 x'' h1)). Qed.
Lemma lem7076096 {_132203 : Type'} (_94379 : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term572 _132203 s f g _94379.
Proof. exact (@lem7076010 _132203 f s g h1 _94379). Qed.
Lemma lem7076097 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) : (term572 _132203 s f g _94379) = (term488 _132203 s f g _94379).
Proof. exact (eq_refl (term572 _132203 s f g _94379)). Qed.
Lemma lem7076099 {_132203 : Type'} (_94380 : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term573 _132203 x _94380.
Proof. exact (@lem7076023 _132203 x h1 _94380). Qed.
Lemma lem7076100 {_132203 : Type'} (x : type684 _132203) (_94380 : _132203 -> Prop) : (term573 _132203 x _94380) = (term412 _132203 x _94380).
Proof. exact (eq_refl (term573 _132203 x _94380)). Qed.
Lemma lem7076108 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term574 _132203 x'' _94378 _94375 _94377 _94376.
Proof. exact (proj2 (@lem7076095 _132203 _94378 _94375 _94377 _94376 x'' h1)). Qed.
Lemma lem7076109 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term575 _132203 x'' _94378 _94375 _94377 _94376.
Proof. exact (proj1 (@lem7076095 _132203 _94378 _94375 _94377 _94376 x'' h1)). Qed.
Lemma lem7076117 (_94369 : real) (_94370 : real) (h1 : term38) : term390 _94369 _94370.
Proof. exact (EQ_MP (@lem7076070 _94369 _94370) (@lem7076069 _94369 _94370 h1)). Qed.
Lemma lem7076123 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term29 _132203 s.
Proof. exact (proj1 (@lem7075680 _132203 f s g h1)). Qed.
Lemma lem7076129 {_132203 : Type'} (_94379 : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term488 _132203 s f g _94379.
Proof. exact (EQ_MP (@lem7076097 _132203 s f g _94379) (@lem7076096 _132203 _94379 f s g h1)). Qed.
Lemma lem7076135 {_132203 : Type'} (_94380 : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term412 _132203 x _94380.
Proof. exact (EQ_MP (@lem7076100 _132203 x _94380) (@lem7076099 _132203 _94380 x h1)). Qed.
Lemma lem7076145 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term575 _132203 x'' _94378 _94375 _94377 _94376) = (term576 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (@lem7073073 (term470 _132203 _94377) (term551 _132203 x'' _94377 _94375 _94376 _94378) (term423 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7076146 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term577 _132203 x'' _94378 _94375 _94377 _94376) = (term578 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (@lem7073073 (term461 _132203 x'' _94375 _94376 _94377) (term434 _132203 _94377 _94375 _94376 _94378) (term423 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7076153 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term579 _132203 _94378 _94375 _94377 _94376) = (term580 _132203 _94378 _94375 _94377 _94376).
Proof. exact (@lem7073073 (term396 _132203 _94378 _94377) (term431 _132203 _94375 _94376 _94378) (term423 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7076154 {_132203 : Type'} (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) : (term581 _132203 x'' _94375 _94376 _94377) = (term581 _132203 x'' _94375 _94376 _94377).
Proof. exact (eq_refl (term581 _132203 x'' _94375 _94376 _94377)). Qed.
Lemma lem7076157 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term578 _132203 x'' _94378 _94375 _94377 _94376) = (term582 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (MK_COMB (@lem7076154 _132203 x'' _94375 _94376 _94377) (@lem7076153 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076158 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term577 _132203 x'' _94378 _94375 _94377 _94376) = (term582 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (TRANS (@lem7076146 _132203 x'' _94378 _94375 _94377 _94376) (@lem7076157 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076159 {_132203 : Type'} (_94377 : _132203 -> Prop) : (term471 _132203 _94377) = (term471 _132203 _94377).
Proof. exact (eq_refl (term471 _132203 _94377)). Qed.
Lemma lem7076162 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term576 _132203 x'' _94378 _94375 _94377 _94376) = (term583 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (MK_COMB (@lem7076159 _132203 _94377) (@lem7076158 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076164 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term575 _132203 x'' _94378 _94375 _94377 _94376) = (term583 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (TRANS (@lem7076145 _132203 x'' _94378 _94375 _94377 _94376) (@lem7076162 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076165 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term583 _132203 x'' _94378 _94375 _94377 _94376.
Proof. exact (EQ_MP (@lem7076164 _132203 x'' _94378 _94375 _94377 _94376) (@lem7076109 _132203 _94378 _94375 _94377 _94376 x'' h1)). Qed.
Lemma lem7076169 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term574 _132203 x'' _94378 _94375 _94377 _94376) = (term584 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (@lem7073073 (term470 _132203 _94377) (term552 _132203 x'' _94377 _94375 _94376 _94378) (term423 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7076170 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term585 _132203 x'' _94378 _94375 _94377 _94376) = (term586 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (@lem7073073 (term454 _132203 x'' _94375 _94376 _94377) (term434 _132203 _94377 _94375 _94376 _94378) (term423 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7076177 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term579 _132203 _94378 _94375 _94377 _94376) = (term580 _132203 _94378 _94375 _94377 _94376).
Proof. exact (@lem7073073 (term396 _132203 _94378 _94377) (term431 _132203 _94375 _94376 _94378) (term423 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7076178 {_132203 : Type'} (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) : (term587 _132203 x'' _94375 _94376 _94377) = (term587 _132203 x'' _94375 _94376 _94377).
Proof. exact (eq_refl (term587 _132203 x'' _94375 _94376 _94377)). Qed.
Lemma lem7076181 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term586 _132203 x'' _94378 _94375 _94377 _94376) = (term588 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (MK_COMB (@lem7076178 _132203 x'' _94375 _94376 _94377) (@lem7076177 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076182 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term585 _132203 x'' _94378 _94375 _94377 _94376) = (term588 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (TRANS (@lem7076170 _132203 x'' _94378 _94375 _94377 _94376) (@lem7076181 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076183 {_132203 : Type'} (_94377 : _132203 -> Prop) : (term471 _132203 _94377) = (term471 _132203 _94377).
Proof. exact (eq_refl (term471 _132203 _94377)). Qed.
Lemma lem7076186 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term584 _132203 x'' _94378 _94375 _94377 _94376) = (term589 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (MK_COMB (@lem7076183 _132203 _94377) (@lem7076182 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076188 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term574 _132203 x'' _94378 _94375 _94377 _94376) = (term589 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (TRANS (@lem7076169 _132203 x'' _94378 _94375 _94377 _94376) (@lem7076186 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076189 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term589 _132203 x'' _94378 _94375 _94377 _94376.
Proof. exact (EQ_MP (@lem7076188 _132203 x'' _94378 _94375 _94377 _94376) (@lem7076108 _132203 _94378 _94375 _94377 _94376 x'' h1)). Qed.
Lemma lem7076567 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : @I ((_132203 -> Prop) -> Prop) (@FINITE _132203) s.
Proof. exact (proj1 (@lem7075679 _132203 f s g h1)). Qed.
Lemma lem7076568 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term590 _132203 s.
Proof. exact (fun h0 : term470 _132203 s => @lem7076567 _132203 f s g h1). Qed.
Lemma lem7076570 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7076571 {_132203 : Type'} (s : _132203 -> Prop) : (term590 _132203 s) = (@I ((_132203 -> Prop) -> Prop) (@FINITE _132203) s).
Proof. exact (@lem7076570 (@I ((_132203 -> Prop) -> Prop) (@FINITE _132203) s)). Qed.
Lemma lem7076572 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : @I ((_132203 -> Prop) -> Prop) (@FINITE _132203) s.
Proof. exact (EQ_MP (@lem7076571 _132203 s) (@lem7076568 _132203 f s g h1)). Qed.
Lemma lem7076574 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : @I ((_132203 -> Prop) -> Prop) (@FINITE _132203) s.
Proof. exact (proj1 (@lem7075679 _132203 f s g h1)). Qed.
Lemma lem7076575 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term590 _132203 s.
Proof. exact (fun h0 : term470 _132203 s => @lem7076574 _132203 f s g h1). Qed.
Lemma lem7076577 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7076578 {_132203 : Type'} (s : _132203 -> Prop) : (term590 _132203 s) = (@I ((_132203 -> Prop) -> Prop) (@FINITE _132203) s).
Proof. exact (@lem7076577 (@I ((_132203 -> Prop) -> Prop) (@FINITE _132203) s)). Qed.
Lemma lem7076579 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : @I ((_132203 -> Prop) -> Prop) (@FINITE _132203) s.
Proof. exact (EQ_MP (@lem7076578 _132203 s) (@lem7076575 _132203 f s g h1)). Qed.
Lemma lem7076582 {_132203 : Type'} (s : _132203 -> Prop) (h1 : term29 _132203 s) : term29 _132203 s.
Proof. exact (h1). Qed.
Lemma lem7076583 {_132203 : Type'} (s : _132203 -> Prop) (h1 : term29 _132203 s) : term592 _132203 s.
Proof. exact (fun h0 : s = (@EMPTY _132203) => @lem7076582 _132203 s h1). Qed.
Lemma lem7076585 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7076586 {_132203 : Type'} (s : _132203 -> Prop) : (term592 _132203 s) = (term29 _132203 s).
Proof. exact (@lem7076585 (s = (@EMPTY _132203))). Qed.
Lemma lem7076587 {_132203 : Type'} (s : _132203 -> Prop) (h1 : term29 _132203 s) : term29 _132203 s.
Proof. exact (EQ_MP (@lem7076586 _132203 s) (@lem7076583 _132203 s h1)). Qed.
Lemma lem7076589 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7076592 {_132203 : Type'} (x : type684 _132203) (_94380 : _132203 -> Prop) : (term412 _132203 x _94380) = (term595 _132203 x _94380).
Proof. exact (@lem7076589 (_94380 = (@EMPTY _132203)) (term409 _132203 x _94380)). Qed.
Lemma lem7076595 {_132203 : Type'} (_94380 : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term595 _132203 x _94380.
Proof. exact (EQ_MP (@lem7076592 _132203 x _94380) (@lem7076135 _132203 _94380 x h1)). Qed.
Lemma lem7076596 {_132203 : Type'} (_94380 : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term595 _132203 x _94380.
Proof. exact (@lem7076595 _132203 _94380 x h1). Qed.
Lemma lem7076597 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term595 _132203 x s.
Proof. exact (@lem7076596 _132203 s x h1). Qed.
Lemma lem7076600 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term29 _132203 s) (h2 : term380 _132203 x) : term409 _132203 x s.
Proof. exact (@lem7076597 _132203 s x h2 (@lem7076587 _132203 s h1)). Qed.
Lemma lem7076601 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term29 _132203 s) (h2 : term380 _132203 x) : term596 _132203 x s.
Proof. exact (fun h0 : term597 _132203 x s => @lem7076600 _132203 s x h1 h2). Qed.
Lemma lem7076603 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7076604 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term596 _132203 x s) = (term409 _132203 x s).
Proof. exact (@lem7076603 (term409 _132203 x s)). Qed.
Lemma lem7076605 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term29 _132203 s) (h2 : term380 _132203 x) : term409 _132203 x s.
Proof. exact (EQ_MP (@lem7076604 _132203 x s) (@lem7076601 _132203 s x h1 h2)). Qed.
Lemma lem7076608 {_132203 : Type'} (s : _132203 -> Prop) (h1 : term29 _132203 s) : term29 _132203 s.
Proof. exact (h1). Qed.
Lemma lem7076609 {_132203 : Type'} (s : _132203 -> Prop) (h1 : term29 _132203 s) : term592 _132203 s.
Proof. exact (fun h0 : s = (@EMPTY _132203) => @lem7076608 _132203 s h1). Qed.
Lemma lem7076611 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7076612 {_132203 : Type'} (s : _132203 -> Prop) : (term592 _132203 s) = (term29 _132203 s).
Proof. exact (@lem7076611 (s = (@EMPTY _132203))). Qed.
Lemma lem7076613 {_132203 : Type'} (s : _132203 -> Prop) (h1 : term29 _132203 s) : term29 _132203 s.
Proof. exact (EQ_MP (@lem7076612 _132203 s) (@lem7076609 _132203 s h1)). Qed.
Lemma lem7076615 {_132203 : Type'} (_94380 : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term595 _132203 x _94380.
Proof. exact (EQ_MP (@lem7076592 _132203 x _94380) (@lem7076135 _132203 _94380 x h1)). Qed.
Lemma lem7076616 {_132203 : Type'} (_94380 : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term595 _132203 x _94380.
Proof. exact (@lem7076615 _132203 _94380 x h1). Qed.
Lemma lem7076617 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term595 _132203 x s.
Proof. exact (@lem7076616 _132203 s x h1). Qed.
Lemma lem7076620 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term29 _132203 s) (h2 : term380 _132203 x) : term409 _132203 x s.
Proof. exact (@lem7076617 _132203 s x h2 (@lem7076613 _132203 s h1)). Qed.
Lemma lem7076621 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term29 _132203 s) (h2 : term380 _132203 x) : term596 _132203 x s.
Proof. exact (fun h0 : term597 _132203 x s => @lem7076620 _132203 s x h1 h2). Qed.
Lemma lem7076623 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7076624 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term596 _132203 x s) = (term409 _132203 x s).
Proof. exact (@lem7076623 (term409 _132203 x s)). Qed.
Lemma lem7076625 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term29 _132203 s) (h2 : term380 _132203 x) : term409 _132203 x s.
Proof. exact (EQ_MP (@lem7076624 _132203 x s) (@lem7076621 _132203 s x h1 h2)). Qed.
Lemma lem7076631 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7076632 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) (s : _132203 -> Prop) : (term488 _132203 s f g _94379) = (term598 _132203 f g _94379 s).
Proof. exact (@lem7076631 (term429 _132203 f g _94379) (term396 _132203 _94379 s)). Qed.
Lemma lem7076638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7076639 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) (s : _132203 -> Prop) : (term599 _132203 s f g _94379) = (term600 _132203 f g _94379 s).
Proof. exact (MK_COMB (@lem7076638) (@lem7076632 _132203 f g _94379 s)). Qed.
Lemma lem7076645 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) (s : _132203 -> Prop) : (term598 _132203 f g _94379 s) = (term598 _132203 f g _94379 s).
Proof. exact (eq_refl (term598 _132203 f g _94379 s)). Qed.
Lemma lem7076646 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) (s : _132203 -> Prop) : ((term488 _132203 s f g _94379) = (term598 _132203 f g _94379 s)) = ((term598 _132203 f g _94379 s) = (term598 _132203 f g _94379 s)).
Proof. exact (MK_COMB (@lem7076639 _132203 f g _94379 s) (@lem7076645 _132203 f g _94379 s)). Qed.
Lemma lem7076648 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7076649 (x : Prop) : (x = x) = True.
Proof. exact (@lem7076648 Prop x). Qed.
Lemma lem7076650 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) (s : _132203 -> Prop) : ((term598 _132203 f g _94379 s) = (term598 _132203 f g _94379 s)) = True.
Proof. exact (@lem7076649 (term598 _132203 f g _94379 s)). Qed.
Lemma lem7076651 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) (s : _132203 -> Prop) : ((term488 _132203 s f g _94379) = (term598 _132203 f g _94379 s)) = True.
Proof. exact (TRANS (@lem7076646 _132203 f g _94379 s) (@lem7076650 _132203 f g _94379 s)). Qed.
Lemma lem7076652 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) (s : _132203 -> Prop) : True = ((term488 _132203 s f g _94379) = (term598 _132203 f g _94379 s)).
Proof. exact (SYM (@lem7076651 _132203 f g _94379 s)). Qed.
Lemma lem7076653 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) (s : _132203 -> Prop) : (term488 _132203 s f g _94379) = (term598 _132203 f g _94379 s).
Proof. exact (EQ_MP (@lem7076652 _132203 f g _94379 s) (@lem0)). Qed.
Lemma lem7076654 {_132203 : Type'} (_94379 : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term598 _132203 f g _94379 s.
Proof. exact (EQ_MP (@lem7076653 _132203 f g _94379 s) (@lem7076129 _132203 _94379 f s g h1)). Qed.
Lemma lem7076656 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7076657 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) : (term598 _132203 f g _94379 s) = (term601 _132203 s f g _94379).
Proof. exact (@lem7076656 (term396 _132203 _94379 s) (term429 _132203 f g _94379)). Qed.
Lemma lem7076659 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7076660 {_132203 : Type'} (_94379 : _132203) (s : _132203 -> Prop) : (term603 _132203 _94379 s) = (term395 _132203 _94379 s).
Proof. exact (@lem7076659 (term395 _132203 _94379 s)). Qed.
Lemma lem7076661 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7076662 {_132203 : Type'} (_94379 : _132203) (s : _132203 -> Prop) : (term604 _132203 _94379 s) = (term605 _132203 _94379 s).
Proof. exact (MK_COMB (@lem7076661) (@lem7076660 _132203 _94379 s)). Qed.
Lemma lem7076663 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) : (term429 _132203 f g _94379) = (term429 _132203 f g _94379).
Proof. exact (eq_refl (term429 _132203 f g _94379)). Qed.
Lemma lem7076664 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) : (term601 _132203 s f g _94379) = (term606 _132203 s f g _94379).
Proof. exact (MK_COMB (@lem7076662 _132203 _94379 s) (@lem7076663 _132203 f g _94379)). Qed.
Lemma lem7076665 {_132203 : Type'} (s : _132203 -> Prop) (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) : (term598 _132203 f g _94379 s) = (term606 _132203 s f g _94379).
Proof. exact (TRANS (@lem7076657 _132203 s f g _94379) (@lem7076664 _132203 s f g _94379)). Qed.
Lemma lem7076668 {_132203 : Type'} (_94379 : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term606 _132203 s f g _94379.
Proof. exact (EQ_MP (@lem7076665 _132203 s f g _94379) (@lem7076654 _132203 _94379 f s g h1)). Qed.
Lemma lem7076669 {_132203 : Type'} (_94379 : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term606 _132203 s f g _94379.
Proof. exact (@lem7076668 _132203 _94379 f s g h1). Qed.
Lemma lem7076670 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term607 _132203 f g x s.
Proof. exact (@lem7076669 _132203 (@I ((_132203 -> Prop) -> _132203) x s) f s g h1). Qed.
Lemma lem7076673 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term29 _132203 s) (h2 : term380 _132203 x) (h3 : term80 _132203 f s g) : term608 _132203 f g x s.
Proof. exact (@lem7076670 _132203 x f s g h3 (@lem7076625 _132203 s x h1 h2)). Qed.
Lemma lem7076674 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term29 _132203 s) (h2 : term380 _132203 x) (h3 : term80 _132203 f s g) : term609 _132203 f g x s.
Proof. exact (fun h0 : term610 _132203 f g x s => @lem7076673 _132203 x f s g h1 h2 h3). Qed.
Lemma lem7076676 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7076677 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : type684 _132203) (s : _132203 -> Prop) : (term609 _132203 f g x s) = (term608 _132203 f g x s).
Proof. exact (@lem7076676 (term608 _132203 f g x s)). Qed.
Lemma lem7076678 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term29 _132203 s) (h2 : term380 _132203 x) (h3 : term80 _132203 f s g) : term608 _132203 f g x s.
Proof. exact (EQ_MP (@lem7076677 _132203 f g x s) (@lem7076674 _132203 x f s g h1 h2 h3)). Qed.
Lemma lem7076680 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term487 _132203 f s g.
Proof. exact (proj2 (@lem7075677 _132203 f s g h1)). Qed.
Lemma lem7076681 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term611 _132203 f s g.
Proof. exact (fun h0 : term423 _132203 f s g => @lem7076680 _132203 f s g h1). Qed.
Lemma lem7076683 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7076684 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term611 _132203 f s g) = (term487 _132203 f s g).
Proof. exact (@lem7076683 (term423 _132203 f s g)). Qed.
Lemma lem7076685 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term487 _132203 f s g.
Proof. exact (EQ_MP (@lem7076684 _132203 f s g) (@lem7076681 _132203 f s g h1)). Qed.
Lemma lem7076691 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7076692 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term583 _132203 x'' _94378 _94375 _94377 _94376) = (term612 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (@lem7076691 (term461 _132203 x'' _94375 _94376 _94377) (term470 _132203 _94377) (term580 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076726 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7076727 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term613 _132203 _94378 _94375 _94377 _94376) = (term614 _132203 _94377 _94375 _94376 _94378).
Proof. exact (@lem7076726 (term423 _132203 _94375 _94377 _94376) (term431 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7076733 {_132203 : Type'} (_94378 : _132203) (_94377 : _132203 -> Prop) : (term433 _132203 _94378 _94377) = (term433 _132203 _94378 _94377).
Proof. exact (eq_refl (term433 _132203 _94378 _94377)). Qed.
Lemma lem7076734 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term580 _132203 _94378 _94375 _94377 _94376) = (term615 _132203 _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7076733 _132203 _94378 _94377) (@lem7076727 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076738 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7076739 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term615 _132203 _94377 _94375 _94376 _94378) = (term616 _132203 _94377 _94375 _94376 _94378).
Proof. exact (@lem7076738 (term423 _132203 _94375 _94377 _94376) (term396 _132203 _94378 _94377) (term431 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7076755 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term580 _132203 _94378 _94375 _94377 _94376) = (term616 _132203 _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7076734 _132203 _94377 _94375 _94376 _94378) (@lem7076739 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076756 {_132203 : Type'} (_94377 : _132203 -> Prop) : (term471 _132203 _94377) = (term471 _132203 _94377).
Proof. exact (eq_refl (term471 _132203 _94377)). Qed.
Lemma lem7076757 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term617 _132203 _94378 _94375 _94377 _94376) = (term618 _132203 _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7076756 _132203 _94377) (@lem7076755 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076761 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7076762 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term618 _132203 _94377 _94375 _94376 _94378) = (term619 _132203 _94377 _94375 _94376 _94378).
Proof. exact (@lem7076761 (term423 _132203 _94375 _94377 _94376) (term470 _132203 _94377) (term434 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076788 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term617 _132203 _94378 _94375 _94377 _94376) = (term619 _132203 _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7076757 _132203 _94377 _94375 _94376 _94378) (@lem7076762 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076789 {_132203 : Type'} (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) : (term581 _132203 x'' _94375 _94376 _94377) = (term581 _132203 x'' _94375 _94376 _94377).
Proof. exact (eq_refl (term581 _132203 x'' _94375 _94376 _94377)). Qed.
Lemma lem7076790 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term612 _132203 x'' _94378 _94375 _94377 _94376) = (term620 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7076789 _132203 x'' _94375 _94376 _94377) (@lem7076788 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076801 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term583 _132203 x'' _94378 _94375 _94377 _94376) = (term620 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7076692 _132203 x'' _94378 _94375 _94377 _94376) (@lem7076790 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076802 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7076803 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term621 _132203 x'' _94378 _94375 _94377 _94376) = (term622 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7076802) (@lem7076801 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076837 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7076838 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term613 _132203 _94378 _94375 _94377 _94376) = (term614 _132203 _94377 _94375 _94376 _94378).
Proof. exact (@lem7076837 (term423 _132203 _94375 _94377 _94376) (term431 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7076844 {_132203 : Type'} (_94378 : _132203) (_94377 : _132203 -> Prop) : (term433 _132203 _94378 _94377) = (term433 _132203 _94378 _94377).
Proof. exact (eq_refl (term433 _132203 _94378 _94377)). Qed.
Lemma lem7076845 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term580 _132203 _94378 _94375 _94377 _94376) = (term615 _132203 _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7076844 _132203 _94378 _94377) (@lem7076838 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076849 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7076850 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term615 _132203 _94377 _94375 _94376 _94378) = (term616 _132203 _94377 _94375 _94376 _94378).
Proof. exact (@lem7076849 (term423 _132203 _94375 _94377 _94376) (term396 _132203 _94378 _94377) (term431 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7076866 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term580 _132203 _94378 _94375 _94377 _94376) = (term616 _132203 _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7076845 _132203 _94377 _94375 _94376 _94378) (@lem7076850 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076867 {_132203 : Type'} (_94377 : _132203 -> Prop) : (term471 _132203 _94377) = (term471 _132203 _94377).
Proof. exact (eq_refl (term471 _132203 _94377)). Qed.
Lemma lem7076868 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term617 _132203 _94378 _94375 _94377 _94376) = (term618 _132203 _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7076867 _132203 _94377) (@lem7076866 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076872 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7076873 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term618 _132203 _94377 _94375 _94376 _94378) = (term619 _132203 _94377 _94375 _94376 _94378).
Proof. exact (@lem7076872 (term423 _132203 _94375 _94377 _94376) (term470 _132203 _94377) (term434 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076899 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term617 _132203 _94378 _94375 _94377 _94376) = (term619 _132203 _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7076868 _132203 _94377 _94375 _94376 _94378) (@lem7076873 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076900 {_132203 : Type'} (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) : (term581 _132203 x'' _94375 _94376 _94377) = (term581 _132203 x'' _94375 _94376 _94377).
Proof. exact (eq_refl (term581 _132203 x'' _94375 _94376 _94377)). Qed.
Lemma lem7076901 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term612 _132203 x'' _94378 _94375 _94377 _94376) = (term620 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7076900 _132203 x'' _94375 _94376 _94377) (@lem7076899 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076912 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : ((term583 _132203 x'' _94378 _94375 _94377 _94376) = (term612 _132203 x'' _94378 _94375 _94377 _94376)) = ((term620 _132203 x'' _94377 _94375 _94376 _94378) = (term620 _132203 x'' _94377 _94375 _94376 _94378)).
Proof. exact (MK_COMB (@lem7076803 _132203 x'' _94377 _94375 _94376 _94378) (@lem7076901 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076914 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7076915 (x : Prop) : (x = x) = True.
Proof. exact (@lem7076914 Prop x). Qed.
Lemma lem7076916 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : ((term620 _132203 x'' _94377 _94375 _94376 _94378) = (term620 _132203 x'' _94377 _94375 _94376 _94378)) = True.
Proof. exact (@lem7076915 (term620 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076917 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : ((term583 _132203 x'' _94378 _94375 _94377 _94376) = (term612 _132203 x'' _94378 _94375 _94377 _94376)) = True.
Proof. exact (TRANS (@lem7076912 _132203 x'' _94377 _94375 _94376 _94378) (@lem7076916 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7076918 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : True = ((term583 _132203 x'' _94378 _94375 _94377 _94376) = (term612 _132203 x'' _94378 _94375 _94377 _94376)).
Proof. exact (SYM (@lem7076917 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076919 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term583 _132203 x'' _94378 _94375 _94377 _94376) = (term612 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (EQ_MP (@lem7076918 _132203 x'' _94378 _94375 _94377 _94376) (@lem0)). Qed.
Lemma lem7076920 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term612 _132203 x'' _94378 _94375 _94377 _94376.
Proof. exact (EQ_MP (@lem7076919 _132203 x'' _94378 _94375 _94377 _94376) (@lem7076165 _132203 _94378 _94375 _94377 _94376 x'' h1)). Qed.
Lemma lem7076922 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7076923 {_132203 : Type'} (_94378 : _132203) (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) : (term612 _132203 x'' _94378 _94375 _94377 _94376) = (term623 _132203 _94378 x'' _94375 _94376 _94377).
Proof. exact (@lem7076922 (term617 _132203 _94378 _94375 _94377 _94376) (term461 _132203 x'' _94375 _94376 _94377)). Qed.
Lemma lem7076925 (a : Prop) (b : Prop) : (term624 a b) = (term625 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7076926 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term626 _132203 _94378 _94375 _94377 _94376) = (term627 _132203 _94378 _94375 _94377 _94376).
Proof. exact (@lem7076925 (term470 _132203 _94377) (term580 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076928 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7076929 {_132203 : Type'} (_94377 : _132203 -> Prop) : (term628 _132203 _94377) = (@I ((_132203 -> Prop) -> Prop) (@FINITE _132203) _94377).
Proof. exact (@lem7076928 (@I ((_132203 -> Prop) -> Prop) (@FINITE _132203) _94377)). Qed.
Lemma lem7076930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7076931 {_132203 : Type'} (_94377 : _132203 -> Prop) : (term629 _132203 _94377) = (term492 _132203 _94377).
Proof. exact (MK_COMB (@lem7076930) (@lem7076929 _132203 _94377)). Qed.
Lemma lem7076933 (a : Prop) (b : Prop) : (term624 a b) = (term625 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7076934 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term630 _132203 _94378 _94375 _94377 _94376) = (term631 _132203 _94378 _94375 _94377 _94376).
Proof. exact (@lem7076933 (term396 _132203 _94378 _94377) (term613 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076936 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7076937 {_132203 : Type'} (_94378 : _132203) (_94377 : _132203 -> Prop) : (term603 _132203 _94378 _94377) = (term395 _132203 _94378 _94377).
Proof. exact (@lem7076936 (term395 _132203 _94378 _94377)). Qed.
Lemma lem7076938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7076939 {_132203 : Type'} (_94378 : _132203) (_94377 : _132203 -> Prop) : (term632 _132203 _94378 _94377) = (term633 _132203 _94378 _94377).
Proof. exact (MK_COMB (@lem7076938) (@lem7076937 _132203 _94378 _94377)). Qed.
Lemma lem7076941 (a : Prop) (b : Prop) : (term624 a b) = (term625 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7076942 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term634 _132203 _94378 _94375 _94377 _94376) = (term635 _132203 _94378 _94375 _94377 _94376).
Proof. exact (@lem7076941 (term431 _132203 _94375 _94376 _94378) (term423 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7076944 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7076945 {_132203 : Type'} (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term636 _132203 _94375 _94376 _94378) = (term429 _132203 _94375 _94376 _94378).
Proof. exact (@lem7076944 (term429 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7076946 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7076947 {_132203 : Type'} (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term637 _132203 _94375 _94376 _94378) = (term638 _132203 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7076946) (@lem7076945 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7076948 {_132203 : Type'} (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term487 _132203 _94375 _94377 _94376) = (term487 _132203 _94375 _94377 _94376).
Proof. exact (eq_refl (term487 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7076949 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term635 _132203 _94378 _94375 _94377 _94376) = (term639 _132203 _94378 _94375 _94377 _94376).
Proof. exact (MK_COMB (@lem7076947 _132203 _94375 _94376 _94378) (@lem7076948 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7076950 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term634 _132203 _94378 _94375 _94377 _94376) = (term639 _132203 _94378 _94375 _94377 _94376).
Proof. exact (TRANS (@lem7076942 _132203 _94378 _94375 _94377 _94376) (@lem7076949 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076951 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term631 _132203 _94378 _94375 _94377 _94376) = (term640 _132203 _94378 _94375 _94377 _94376).
Proof. exact (MK_COMB (@lem7076939 _132203 _94378 _94377) (@lem7076950 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076952 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term630 _132203 _94378 _94375 _94377 _94376) = (term640 _132203 _94378 _94375 _94377 _94376).
Proof. exact (TRANS (@lem7076934 _132203 _94378 _94375 _94377 _94376) (@lem7076951 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076953 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term627 _132203 _94378 _94375 _94377 _94376) = (term641 _132203 _94378 _94375 _94377 _94376).
Proof. exact (MK_COMB (@lem7076931 _132203 _94377) (@lem7076952 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076954 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term626 _132203 _94378 _94375 _94377 _94376) = (term641 _132203 _94378 _94375 _94377 _94376).
Proof. exact (TRANS (@lem7076926 _132203 _94378 _94375 _94377 _94376) (@lem7076953 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076955 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7076956 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term642 _132203 _94378 _94375 _94377 _94376) = (term643 _132203 _94378 _94375 _94377 _94376).
Proof. exact (MK_COMB (@lem7076955) (@lem7076954 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7076957 {_132203 : Type'} (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) : (term461 _132203 x'' _94375 _94376 _94377) = (term461 _132203 x'' _94375 _94376 _94377).
Proof. exact (eq_refl (term461 _132203 x'' _94375 _94376 _94377)). Qed.
Lemma lem7076958 {_132203 : Type'} (_94378 : _132203) (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) : (term623 _132203 _94378 x'' _94375 _94376 _94377) = (term644 _132203 _94378 x'' _94375 _94376 _94377).
Proof. exact (MK_COMB (@lem7076956 _132203 _94378 _94375 _94377 _94376) (@lem7076957 _132203 x'' _94375 _94376 _94377)). Qed.
Lemma lem7076959 {_132203 : Type'} (_94378 : _132203) (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) : (term612 _132203 x'' _94378 _94375 _94377 _94376) = (term644 _132203 _94378 x'' _94375 _94376 _94377).
Proof. exact (TRANS (@lem7076923 _132203 _94378 x'' _94375 _94376 _94377) (@lem7076958 _132203 _94378 x'' _94375 _94376 _94377)). Qed.
Lemma lem7076961 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term29 _132203 s) (h2 : term380 _132203 x) (h3 : term80 _132203 f s g) : term645 _132203 x f s g.
Proof. exact (conj (@lem7076678 _132203 x f s g h1 h2 h3) (@lem7076685 _132203 f s g h3)). Qed.
Lemma lem7076962 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term29 _132203 s) (h2 : term380 _132203 x) (h3 : term80 _132203 f s g) : term646 _132203 x f s g.
Proof. exact (conj (@lem7076605 _132203 s x h1 h2) (@lem7076961 _132203 x f s g h1 h2 h3)). Qed.
Lemma lem7076963 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term29 _132203 s) (h2 : term380 _132203 x) (h3 : term80 _132203 f s g) : term647 _132203 x f s g.
Proof. exact (conj (@lem7076579 _132203 f s g h3) (@lem7076962 _132203 x f s g h1 h2 h3)). Qed.
Lemma lem7076965 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term644 _132203 _94378 x'' _94375 _94376 _94377.
Proof. exact (EQ_MP (@lem7076959 _132203 _94378 x'' _94375 _94376 _94377) (@lem7076920 _132203 _94378 _94375 _94377 _94376 x'' h1)). Qed.
Lemma lem7076966 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term644 _132203 _94378 x'' _94375 _94376 _94377.
Proof. exact (@lem7076965 _132203 _94378 _94375 _94376 _94377 x'' h1). Qed.
Lemma lem7076967 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term648 _132203 x x'' f g s.
Proof. exact (@lem7076966 _132203 (@I ((_132203 -> Prop) -> _132203) x s) f g s x'' h1). Qed.
Lemma lem7076970 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term29 _132203 s) (h3 : term380 _132203 x) (h4 : term80 _132203 f s g) : term461 _132203 x'' f g s.
Proof. exact (@lem7076967 _132203 x f g s x'' h1 (@lem7076963 _132203 x f s g h2 h3 h4)). Qed.
Lemma lem7076971 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term29 _132203 s) (h3 : term380 _132203 x) (h4 : term80 _132203 f s g) : term649 _132203 x'' f g s.
Proof. exact (fun h0 : term650 _132203 x'' f g s => @lem7076970 _132203 x'' x f s g h1 h2 h3 h4). Qed.
Lemma lem7076973 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7076974 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term649 _132203 x'' f g s) = (term461 _132203 x'' f g s).
Proof. exact (@lem7076973 (term461 _132203 x'' f g s)). Qed.
Lemma lem7076975 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term29 _132203 s) (h3 : term380 _132203 x) (h4 : term80 _132203 f s g) : term461 _132203 x'' f g s.
Proof. exact (EQ_MP (@lem7076974 _132203 x'' f g s) (@lem7076971 _132203 x'' x f s g h1 h2 h3 h4)). Qed.
Lemma lem7076977 {_132203 : Type'} (_94379 : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term606 _132203 s f g _94379.
Proof. exact (EQ_MP (@lem7076665 _132203 s f g _94379) (@lem7076654 _132203 _94379 f s g h1)). Qed.
Lemma lem7076978 {_132203 : Type'} (_94379 : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term606 _132203 s f g _94379.
Proof. exact (@lem7076977 _132203 _94379 f s g h1). Qed.
Lemma lem7076979 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term651 _132203 x'' f g s.
Proof. exact (@lem7076978 _132203 (term439 _132203 x'' f g s) f s g h1). Qed.
Lemma lem7076982 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term29 _132203 s) (h3 : term380 _132203 x) (h4 : term80 _132203 f s g) : term652 _132203 x'' f g s.
Proof. exact (@lem7076979 _132203 x'' f s g h4 (@lem7076975 _132203 x'' x f s g h1 h2 h3 h4)). Qed.
Lemma lem7076983 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term29 _132203 s) (h3 : term380 _132203 x) (h4 : term80 _132203 f s g) : term653 _132203 x'' f g s.
Proof. exact (fun h0 : term654 _132203 x'' f g s => @lem7076982 _132203 x'' x f s g h1 h2 h3 h4). Qed.
Lemma lem7076985 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7076986 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term653 _132203 x'' f g s) = (term652 _132203 x'' f g s).
Proof. exact (@lem7076985 (term652 _132203 x'' f g s)). Qed.
Lemma lem7076987 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term29 _132203 s) (h3 : term380 _132203 x) (h4 : term80 _132203 f s g) : term652 _132203 x'' f g s.
Proof. exact (EQ_MP (@lem7076986 _132203 x'' f g s) (@lem7076983 _132203 x'' x f s g h1 h2 h3 h4)). Qed.
Lemma lem7076993 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7076994 (_94369 : real) (_94370 : real) : (term390 _94369 _94370) = (term655 _94369 _94370).
Proof. exact (@lem7076993 (term384 _94369 _94370) (term387 _94369 _94370)). Qed.
Lemma lem7077000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7077001 (_94369 : real) (_94370 : real) : (term656 _94369 _94370) = (term657 _94369 _94370).
Proof. exact (MK_COMB (@lem7077000) (@lem7076994 _94369 _94370)). Qed.
Lemma lem7077007 (_94369 : real) (_94370 : real) : (term655 _94369 _94370) = (term655 _94369 _94370).
Proof. exact (eq_refl (term655 _94369 _94370)). Qed.
Lemma lem7077008 (_94369 : real) (_94370 : real) : ((term390 _94369 _94370) = (term655 _94369 _94370)) = ((term655 _94369 _94370) = (term655 _94369 _94370)).
Proof. exact (MK_COMB (@lem7077001 _94369 _94370) (@lem7077007 _94369 _94370)). Qed.
Lemma lem7077010 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7077011 (x : Prop) : (x = x) = True.
Proof. exact (@lem7077010 Prop x). Qed.
Lemma lem7077012 (_94369 : real) (_94370 : real) : ((term655 _94369 _94370) = (term655 _94369 _94370)) = True.
Proof. exact (@lem7077011 (term655 _94369 _94370)). Qed.
Lemma lem7077013 (_94369 : real) (_94370 : real) : ((term390 _94369 _94370) = (term655 _94369 _94370)) = True.
Proof. exact (TRANS (@lem7077008 _94369 _94370) (@lem7077012 _94369 _94370)). Qed.
Lemma lem7077014 (_94369 : real) (_94370 : real) : True = ((term390 _94369 _94370) = (term655 _94369 _94370)).
Proof. exact (SYM (@lem7077013 _94369 _94370)). Qed.
Lemma lem7077015 (_94369 : real) (_94370 : real) : (term390 _94369 _94370) = (term655 _94369 _94370).
Proof. exact (EQ_MP (@lem7077014 _94369 _94370) (@lem0)). Qed.
Lemma lem7077016 (_94369 : real) (_94370 : real) (h1 : term38) : term655 _94369 _94370.
Proof. exact (EQ_MP (@lem7077015 _94369 _94370) (@lem7076117 _94369 _94370 h1)). Qed.
Lemma lem7077018 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7077019 (_94369 : real) (_94370 : real) : (term655 _94369 _94370) = (term658 _94369 _94370).
Proof. exact (@lem7077018 (term387 _94369 _94370) (term384 _94369 _94370)). Qed.
Lemma lem7077021 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7077022 (_94369 : real) (_94370 : real) : (term659 _94369 _94370) = (term385 _94369 _94370).
Proof. exact (@lem7077021 (term385 _94369 _94370)). Qed.
Lemma lem7077023 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7077024 (_94369 : real) (_94370 : real) : (term660 _94369 _94370) = (term661 _94369 _94370).
Proof. exact (MK_COMB (@lem7077023) (@lem7077022 _94369 _94370)). Qed.
Lemma lem7077025 (_94369 : real) (_94370 : real) : (term384 _94369 _94370) = (term384 _94369 _94370).
Proof. exact (eq_refl (term384 _94369 _94370)). Qed.
Lemma lem7077026 (_94369 : real) (_94370 : real) : (term658 _94369 _94370) = (term662 _94369 _94370).
Proof. exact (MK_COMB (@lem7077024 _94369 _94370) (@lem7077025 _94369 _94370)). Qed.
Lemma lem7077027 (_94369 : real) (_94370 : real) : (term655 _94369 _94370) = (term662 _94369 _94370).
Proof. exact (TRANS (@lem7077019 _94369 _94370) (@lem7077026 _94369 _94370)). Qed.
Lemma lem7077030 (_94369 : real) (_94370 : real) (h1 : term38) : term662 _94369 _94370.
Proof. exact (EQ_MP (@lem7077027 _94369 _94370) (@lem7077016 _94369 _94370 h1)). Qed.
Lemma lem7077031 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) (h1 : term38) : term663 _132203 x'' f g s.
Proof. exact (@lem7077030 (term442 _132203 x'' f g s) (term445 _132203 x'' f g s) h1). Qed.
Lemma lem7077034 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term29 _132203 s) (h4 : term380 _132203 x) (h5 : term80 _132203 f s g) : term452 _132203 x'' f g s.
Proof. exact (@lem7077031 _132203 x'' f g s h2 (@lem7076987 _132203 x'' x f s g h1 h3 h4 h5)). Qed.
Lemma lem7077035 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term29 _132203 s) (h4 : term380 _132203 x) (h5 : term80 _132203 f s g) : term664 _132203 x'' f g s.
Proof. exact (fun h0 : term454 _132203 x'' f g s => @lem7077034 _132203 x'' x f s g h1 h2 h3 h4 h5). Qed.
Lemma lem7077037 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7077038 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (s : _132203 -> Prop) : (term664 _132203 x'' f g s) = (term452 _132203 x'' f g s).
Proof. exact (@lem7077037 (term452 _132203 x'' f g s)). Qed.
Lemma lem7077039 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term29 _132203 s) (h4 : term380 _132203 x) (h5 : term80 _132203 f s g) : term452 _132203 x'' f g s.
Proof. exact (EQ_MP (@lem7077038 _132203 x'' f g s) (@lem7077035 _132203 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7077042 {_132203 : Type'} (s : _132203 -> Prop) (h1 : term29 _132203 s) : term29 _132203 s.
Proof. exact (h1). Qed.
Lemma lem7077043 {_132203 : Type'} (s : _132203 -> Prop) (h1 : term29 _132203 s) : term592 _132203 s.
Proof. exact (fun h0 : s = (@EMPTY _132203) => @lem7077042 _132203 s h1). Qed.
Lemma lem7077045 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7077046 {_132203 : Type'} (s : _132203 -> Prop) : (term592 _132203 s) = (term29 _132203 s).
Proof. exact (@lem7077045 (s = (@EMPTY _132203))). Qed.
Lemma lem7077047 {_132203 : Type'} (s : _132203 -> Prop) (h1 : term29 _132203 s) : term29 _132203 s.
Proof. exact (EQ_MP (@lem7077046 _132203 s) (@lem7077043 _132203 s h1)). Qed.
Lemma lem7077049 {_132203 : Type'} (_94380 : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term595 _132203 x _94380.
Proof. exact (EQ_MP (@lem7076592 _132203 x _94380) (@lem7076135 _132203 _94380 x h1)). Qed.
Lemma lem7077050 {_132203 : Type'} (_94380 : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term595 _132203 x _94380.
Proof. exact (@lem7077049 _132203 _94380 x h1). Qed.
Lemma lem7077051 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term595 _132203 x s.
Proof. exact (@lem7077050 _132203 s x h1). Qed.
Lemma lem7077054 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term29 _132203 s) (h2 : term380 _132203 x) : term409 _132203 x s.
Proof. exact (@lem7077051 _132203 s x h2 (@lem7077047 _132203 s h1)). Qed.
Lemma lem7077055 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term29 _132203 s) (h2 : term380 _132203 x) : term596 _132203 x s.
Proof. exact (fun h0 : term597 _132203 x s => @lem7077054 _132203 s x h1 h2). Qed.
Lemma lem7077057 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7077058 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term596 _132203 x s) = (term409 _132203 x s).
Proof. exact (@lem7077057 (term409 _132203 x s)). Qed.
Lemma lem7077059 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term29 _132203 s) (h2 : term380 _132203 x) : term409 _132203 x s.
Proof. exact (EQ_MP (@lem7077058 _132203 x s) (@lem7077055 _132203 s x h1 h2)). Qed.
Lemma lem7077061 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term487 _132203 f s g.
Proof. exact (proj2 (@lem7075677 _132203 f s g h1)). Qed.
Lemma lem7077062 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term611 _132203 f s g.
Proof. exact (fun h0 : term423 _132203 f s g => @lem7077061 _132203 f s g h1). Qed.
Lemma lem7077064 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7077065 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) : (term611 _132203 f s g) = (term487 _132203 f s g).
Proof. exact (@lem7077064 (term423 _132203 f s g)). Qed.
Lemma lem7077066 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term487 _132203 f s g.
Proof. exact (EQ_MP (@lem7077065 _132203 f s g) (@lem7077062 _132203 f s g h1)). Qed.
Lemma lem7077082 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7077083 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term588 _132203 x'' _94378 _94375 _94377 _94376) = (term665 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (@lem7077082 (term396 _132203 _94378 _94377) (term454 _132203 x'' _94375 _94376 _94377) (term613 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7077107 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7077108 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term613 _132203 _94378 _94375 _94377 _94376) = (term614 _132203 _94377 _94375 _94376 _94378).
Proof. exact (@lem7077107 (term423 _132203 _94375 _94377 _94376) (term431 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7077114 {_132203 : Type'} (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) : (term587 _132203 x'' _94375 _94376 _94377) = (term587 _132203 x'' _94375 _94376 _94377).
Proof. exact (eq_refl (term587 _132203 x'' _94375 _94376 _94377)). Qed.
Lemma lem7077115 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term666 _132203 x'' _94378 _94375 _94377 _94376) = (term667 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7077114 _132203 x'' _94375 _94376 _94377) (@lem7077108 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077119 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7077120 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term667 _132203 x'' _94377 _94375 _94376 _94378) = (term668 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (@lem7077119 (term423 _132203 _94375 _94377 _94376) (term454 _132203 x'' _94375 _94376 _94377) (term431 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7077136 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term666 _132203 x'' _94378 _94375 _94377 _94376) = (term668 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7077115 _132203 x'' _94377 _94375 _94376 _94378) (@lem7077120 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077137 {_132203 : Type'} (_94378 : _132203) (_94377 : _132203 -> Prop) : (term433 _132203 _94378 _94377) = (term433 _132203 _94378 _94377).
Proof. exact (eq_refl (term433 _132203 _94378 _94377)). Qed.
Lemma lem7077138 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term665 _132203 x'' _94378 _94375 _94377 _94376) = (term669 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7077137 _132203 _94378 _94377) (@lem7077136 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077142 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7077143 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term669 _132203 x'' _94377 _94375 _94376 _94378) = (term670 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (@lem7077142 (term423 _132203 _94375 _94377 _94376) (term396 _132203 _94378 _94377) (term671 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077169 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term665 _132203 x'' _94378 _94375 _94377 _94376) = (term670 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7077138 _132203 x'' _94377 _94375 _94376 _94378) (@lem7077143 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077170 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term588 _132203 x'' _94378 _94375 _94377 _94376) = (term670 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7077083 _132203 x'' _94378 _94375 _94377 _94376) (@lem7077169 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077171 {_132203 : Type'} (_94377 : _132203 -> Prop) : (term471 _132203 _94377) = (term471 _132203 _94377).
Proof. exact (eq_refl (term471 _132203 _94377)). Qed.
Lemma lem7077172 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term589 _132203 x'' _94378 _94375 _94377 _94376) = (term672 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7077171 _132203 _94377) (@lem7077170 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077176 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7077177 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term672 _132203 x'' _94377 _94375 _94376 _94378) = (term673 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (@lem7077176 (term423 _132203 _94375 _94377 _94376) (term470 _132203 _94377) (term674 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077213 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term589 _132203 x'' _94378 _94375 _94377 _94376) = (term673 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7077172 _132203 x'' _94377 _94375 _94376 _94378) (@lem7077177 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7077215 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term675 _132203 x'' _94378 _94375 _94377 _94376) = (term676 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7077214) (@lem7077213 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077219 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7077220 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term677 _132203 x'' _94378 _94375 _94377 _94376) = (term678 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (@lem7077219 (term470 _132203 _94377) (term431 _132203 _94375 _94376 _94378) (term679 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7077234 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7077235 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term680 _132203 x'' _94378 _94375 _94377 _94376) = (term681 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (@lem7077234 (term454 _132203 x'' _94375 _94376 _94377) (term431 _132203 _94375 _94376 _94378) (term682 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7077249 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7077250 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term683 _132203 _94378 _94375 _94377 _94376) = (term580 _132203 _94378 _94375 _94377 _94376).
Proof. exact (@lem7077249 (term396 _132203 _94378 _94377) (term431 _132203 _94375 _94376 _94378) (term423 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7077264 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7077265 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term613 _132203 _94378 _94375 _94377 _94376) = (term614 _132203 _94377 _94375 _94376 _94378).
Proof. exact (@lem7077264 (term423 _132203 _94375 _94377 _94376) (term431 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7077271 {_132203 : Type'} (_94378 : _132203) (_94377 : _132203 -> Prop) : (term433 _132203 _94378 _94377) = (term433 _132203 _94378 _94377).
Proof. exact (eq_refl (term433 _132203 _94378 _94377)). Qed.
Lemma lem7077272 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term580 _132203 _94378 _94375 _94377 _94376) = (term615 _132203 _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7077271 _132203 _94378 _94377) (@lem7077265 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077276 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7077277 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term615 _132203 _94377 _94375 _94376 _94378) = (term616 _132203 _94377 _94375 _94376 _94378).
Proof. exact (@lem7077276 (term423 _132203 _94375 _94377 _94376) (term396 _132203 _94378 _94377) (term431 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7077293 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term580 _132203 _94378 _94375 _94377 _94376) = (term616 _132203 _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7077272 _132203 _94377 _94375 _94376 _94378) (@lem7077277 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077294 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term683 _132203 _94378 _94375 _94377 _94376) = (term616 _132203 _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7077250 _132203 _94378 _94375 _94377 _94376) (@lem7077293 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077295 {_132203 : Type'} (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) : (term587 _132203 x'' _94375 _94376 _94377) = (term587 _132203 x'' _94375 _94376 _94377).
Proof. exact (eq_refl (term587 _132203 x'' _94375 _94376 _94377)). Qed.
Lemma lem7077296 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term681 _132203 x'' _94378 _94375 _94377 _94376) = (term684 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7077295 _132203 x'' _94375 _94376 _94377) (@lem7077294 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077300 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7077301 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term684 _132203 x'' _94377 _94375 _94376 _94378) = (term685 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (@lem7077300 (term423 _132203 _94375 _94377 _94376) (term454 _132203 x'' _94375 _94376 _94377) (term434 _132203 _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077315 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7077316 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term552 _132203 x'' _94377 _94375 _94376 _94378) = (term674 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (@lem7077315 (term396 _132203 _94378 _94377) (term454 _132203 x'' _94375 _94376 _94377) (term431 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7077332 {_132203 : Type'} (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term686 _132203 _94375 _94377 _94376) = (term686 _132203 _94375 _94377 _94376).
Proof. exact (eq_refl (term686 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7077333 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term685 _132203 x'' _94377 _94375 _94376 _94378) = (term670 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7077332 _132203 _94375 _94377 _94376) (@lem7077316 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077344 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term684 _132203 x'' _94377 _94375 _94376 _94378) = (term670 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7077301 _132203 x'' _94377 _94375 _94376 _94378) (@lem7077333 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077345 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term681 _132203 x'' _94378 _94375 _94377 _94376) = (term670 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7077296 _132203 x'' _94377 _94375 _94376 _94378) (@lem7077344 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077346 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term680 _132203 x'' _94378 _94375 _94377 _94376) = (term670 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7077235 _132203 x'' _94378 _94375 _94377 _94376) (@lem7077345 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077347 {_132203 : Type'} (_94377 : _132203 -> Prop) : (term471 _132203 _94377) = (term471 _132203 _94377).
Proof. exact (eq_refl (term471 _132203 _94377)). Qed.
Lemma lem7077348 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term678 _132203 x'' _94378 _94375 _94377 _94376) = (term672 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7077347 _132203 _94377) (@lem7077346 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077352 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7077353 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term672 _132203 x'' _94377 _94375 _94376 _94378) = (term673 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (@lem7077352 (term423 _132203 _94375 _94377 _94376) (term470 _132203 _94377) (term674 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077389 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term678 _132203 x'' _94378 _94375 _94377 _94376) = (term673 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7077348 _132203 x'' _94377 _94375 _94376 _94378) (@lem7077353 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077390 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term677 _132203 x'' _94378 _94375 _94377 _94376) = (term673 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7077220 _132203 x'' _94378 _94375 _94377 _94376) (@lem7077389 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077391 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : ((term589 _132203 x'' _94378 _94375 _94377 _94376) = (term677 _132203 x'' _94378 _94375 _94377 _94376)) = ((term673 _132203 x'' _94377 _94375 _94376 _94378) = (term673 _132203 x'' _94377 _94375 _94376 _94378)).
Proof. exact (MK_COMB (@lem7077215 _132203 x'' _94377 _94375 _94376 _94378) (@lem7077390 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077393 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7077394 (x : Prop) : (x = x) = True.
Proof. exact (@lem7077393 Prop x). Qed.
Lemma lem7077395 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : ((term673 _132203 x'' _94377 _94375 _94376 _94378) = (term673 _132203 x'' _94377 _94375 _94376 _94378)) = True.
Proof. exact (@lem7077394 (term673 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077396 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : ((term589 _132203 x'' _94378 _94375 _94377 _94376) = (term677 _132203 x'' _94378 _94375 _94377 _94376)) = True.
Proof. exact (TRANS (@lem7077391 _132203 x'' _94377 _94375 _94376 _94378) (@lem7077395 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077397 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : True = ((term589 _132203 x'' _94378 _94375 _94377 _94376) = (term677 _132203 x'' _94378 _94375 _94377 _94376)).
Proof. exact (SYM (@lem7077396 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7077398 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term589 _132203 x'' _94378 _94375 _94377 _94376) = (term677 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (EQ_MP (@lem7077397 _132203 x'' _94378 _94375 _94377 _94376) (@lem0)). Qed.
Lemma lem7077399 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term677 _132203 x'' _94378 _94375 _94377 _94376.
Proof. exact (EQ_MP (@lem7077398 _132203 x'' _94378 _94375 _94377 _94376) (@lem7076189 _132203 _94378 _94375 _94377 _94376 x'' h1)). Qed.
Lemma lem7077401 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7077402 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term677 _132203 x'' _94378 _94375 _94377 _94376) = (term687 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (@lem7077401 (term688 _132203 x'' _94378 _94375 _94377 _94376) (term431 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7077404 (a : Prop) (b : Prop) : (term624 a b) = (term625 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7077405 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term689 _132203 x'' _94378 _94375 _94377 _94376) = (term690 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (@lem7077404 (term470 _132203 _94377) (term679 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7077407 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7077408 {_132203 : Type'} (_94377 : _132203 -> Prop) : (term628 _132203 _94377) = (@I ((_132203 -> Prop) -> Prop) (@FINITE _132203) _94377).
Proof. exact (@lem7077407 (@I ((_132203 -> Prop) -> Prop) (@FINITE _132203) _94377)). Qed.
Lemma lem7077409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7077410 {_132203 : Type'} (_94377 : _132203 -> Prop) : (term629 _132203 _94377) = (term492 _132203 _94377).
Proof. exact (MK_COMB (@lem7077409) (@lem7077408 _132203 _94377)). Qed.
Lemma lem7077412 (a : Prop) (b : Prop) : (term624 a b) = (term625 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7077413 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term691 _132203 x'' _94378 _94375 _94377 _94376) = (term692 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (@lem7077412 (term454 _132203 x'' _94375 _94376 _94377) (term682 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7077415 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7077416 {_132203 : Type'} (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) : (term693 _132203 x'' _94375 _94376 _94377) = (term452 _132203 x'' _94375 _94376 _94377).
Proof. exact (@lem7077415 (term452 _132203 x'' _94375 _94376 _94377)). Qed.
Lemma lem7077417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7077418 {_132203 : Type'} (x'' : type711 _132203) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94377 : _132203 -> Prop) : (term694 _132203 x'' _94375 _94376 _94377) = (term695 _132203 x'' _94375 _94376 _94377).
Proof. exact (MK_COMB (@lem7077417) (@lem7077416 _132203 x'' _94375 _94376 _94377)). Qed.
Lemma lem7077420 (a : Prop) (b : Prop) : (term624 a b) = (term625 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7077421 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term696 _132203 _94378 _94375 _94377 _94376) = (term697 _132203 _94378 _94375 _94377 _94376).
Proof. exact (@lem7077420 (term396 _132203 _94378 _94377) (term423 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7077423 (a : Prop) : (term602 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7077424 {_132203 : Type'} (_94378 : _132203) (_94377 : _132203 -> Prop) : (term603 _132203 _94378 _94377) = (term395 _132203 _94378 _94377).
Proof. exact (@lem7077423 (term395 _132203 _94378 _94377)). Qed.
Lemma lem7077425 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7077426 {_132203 : Type'} (_94378 : _132203) (_94377 : _132203 -> Prop) : (term632 _132203 _94378 _94377) = (term633 _132203 _94378 _94377).
Proof. exact (MK_COMB (@lem7077425) (@lem7077424 _132203 _94378 _94377)). Qed.
Lemma lem7077427 {_132203 : Type'} (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term487 _132203 _94375 _94377 _94376) = (term487 _132203 _94375 _94377 _94376).
Proof. exact (eq_refl (term487 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7077428 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term697 _132203 _94378 _94375 _94377 _94376) = (term698 _132203 _94378 _94375 _94377 _94376).
Proof. exact (MK_COMB (@lem7077426 _132203 _94378 _94377) (@lem7077427 _132203 _94375 _94377 _94376)). Qed.
Lemma lem7077429 {_132203 : Type'} (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term696 _132203 _94378 _94375 _94377 _94376) = (term698 _132203 _94378 _94375 _94377 _94376).
Proof. exact (TRANS (@lem7077421 _132203 _94378 _94375 _94377 _94376) (@lem7077428 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7077430 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term692 _132203 x'' _94378 _94375 _94377 _94376) = (term699 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (MK_COMB (@lem7077418 _132203 x'' _94375 _94376 _94377) (@lem7077429 _132203 _94378 _94375 _94377 _94376)). Qed.
Lemma lem7077431 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term691 _132203 x'' _94378 _94375 _94377 _94376) = (term699 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (TRANS (@lem7077413 _132203 x'' _94378 _94375 _94377 _94376) (@lem7077430 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7077432 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term690 _132203 x'' _94378 _94375 _94377 _94376) = (term700 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (MK_COMB (@lem7077410 _132203 _94377) (@lem7077431 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7077433 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term689 _132203 x'' _94378 _94375 _94377 _94376) = (term700 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (TRANS (@lem7077405 _132203 x'' _94378 _94375 _94377 _94376) (@lem7077432 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7077434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7077435 {_132203 : Type'} (x'' : type711 _132203) (_94378 : _132203) (_94375 : _132203 -> real) (_94377 : _132203 -> Prop) (_94376 : _132203 -> real) : (term701 _132203 x'' _94378 _94375 _94377 _94376) = (term702 _132203 x'' _94378 _94375 _94377 _94376).
Proof. exact (MK_COMB (@lem7077434) (@lem7077433 _132203 x'' _94378 _94375 _94377 _94376)). Qed.
Lemma lem7077436 {_132203 : Type'} (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term431 _132203 _94375 _94376 _94378) = (term431 _132203 _94375 _94376 _94378).
Proof. exact (eq_refl (term431 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7077437 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term687 _132203 x'' _94377 _94375 _94376 _94378) = (term703 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (MK_COMB (@lem7077435 _132203 x'' _94378 _94375 _94377 _94376) (@lem7077436 _132203 _94375 _94376 _94378)). Qed.
Lemma lem7077438 {_132203 : Type'} (x'' : type711 _132203) (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) : (term677 _132203 x'' _94378 _94375 _94377 _94376) = (term703 _132203 x'' _94377 _94375 _94376 _94378).
Proof. exact (TRANS (@lem7077402 _132203 x'' _94377 _94375 _94376 _94378) (@lem7077437 _132203 x'' _94377 _94375 _94376 _94378)). Qed.
Lemma lem7077440 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term29 _132203 s) (h2 : term380 _132203 x) (h3 : term80 _132203 f s g) : term704 _132203 x f s g.
Proof. exact (conj (@lem7077059 _132203 s x h1 h2) (@lem7077066 _132203 f s g h3)). Qed.
Lemma lem7077441 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term29 _132203 s) (h4 : term380 _132203 x) (h5 : term80 _132203 f s g) : term705 _132203 x'' x f s g.
Proof. exact (conj (@lem7077039 _132203 x'' x f s g h1 h2 h3 h4 h5) (@lem7077440 _132203 x f s g h3 h4 h5)). Qed.
Lemma lem7077442 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term29 _132203 s) (h4 : term380 _132203 x) (h5 : term80 _132203 f s g) : term706 _132203 x'' x f s g.
Proof. exact (conj (@lem7076572 _132203 f s g h5) (@lem7077441 _132203 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7077444 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term703 _132203 x'' _94377 _94375 _94376 _94378.
Proof. exact (EQ_MP (@lem7077438 _132203 x'' _94377 _94375 _94376 _94378) (@lem7077399 _132203 _94378 _94375 _94377 _94376 x'' h1)). Qed.
Lemma lem7077445 {_132203 : Type'} (_94377 : _132203 -> Prop) (_94375 : _132203 -> real) (_94376 : _132203 -> real) (_94378 : _132203) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term703 _132203 x'' _94377 _94375 _94376 _94378.
Proof. exact (@lem7077444 _132203 _94377 _94375 _94376 _94378 x'' h1). Qed.
Lemma lem7077446 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : type684 _132203) (s : _132203 -> Prop) (x'' : type711 _132203) (h1 : term271 _132203 x'') : term707 _132203 x'' f g x s.
Proof. exact (@lem7077445 _132203 s f g (@I ((_132203 -> Prop) -> _132203) x s) x'' h1). Qed.
Lemma lem7077449 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term29 _132203 s) (h4 : term380 _132203 x) (h5 : term80 _132203 f s g) : term610 _132203 f g x s.
Proof. exact (@lem7077446 _132203 f g x s x'' h1 (@lem7077442 _132203 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7077450 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term29 _132203 s) (h4 : term380 _132203 x) (h5 : term80 _132203 f s g) : term708 _132203 f g x s.
Proof. exact (fun h0 : term608 _132203 f g x s => @lem7077449 _132203 x'' x f s g h1 h2 h3 h4 h5). Qed.
Lemma lem7077452 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7077453 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (x : type684 _132203) (s : _132203 -> Prop) : (term708 _132203 f g x s) = (term610 _132203 f g x s).
Proof. exact (@lem7077452 (term608 _132203 f g x s)). Qed.
Lemma lem7077454 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term29 _132203 s) (h4 : term380 _132203 x) (h5 : term80 _132203 f s g) : term610 _132203 f g x s.
Proof. exact (EQ_MP (@lem7077453 _132203 f g x s) (@lem7077450 _132203 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7077456 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7077459 {_132203 : Type'} (f : _132203 -> real) (g : _132203 -> real) (_94379 : _132203) (s : _132203 -> Prop) : (term488 _132203 s f g _94379) = (term709 _132203 f g _94379 s).
Proof. exact (@lem7077456 (term429 _132203 f g _94379) (term396 _132203 _94379 s)). Qed.
Lemma lem7077462 {_132203 : Type'} (_94379 : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term709 _132203 f g _94379 s.
Proof. exact (EQ_MP (@lem7077459 _132203 f g _94379 s) (@lem7076129 _132203 _94379 f s g h1)). Qed.
Lemma lem7077463 {_132203 : Type'} (_94379 : _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term709 _132203 f g _94379 s.
Proof. exact (@lem7077462 _132203 _94379 f s g h1). Qed.
Lemma lem7077464 {_132203 : Type'} (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term710 _132203 f g x s.
Proof. exact (@lem7077463 _132203 (@I ((_132203 -> Prop) -> _132203) x s) f s g h1). Qed.
Lemma lem7077467 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term29 _132203 s) (h4 : term380 _132203 x) (h5 : term80 _132203 f s g) : term597 _132203 x s.
Proof. exact (@lem7077464 _132203 x f s g h5 (@lem7077454 _132203 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7077468 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term29 _132203 s) (h4 : term380 _132203 x) (h5 : term80 _132203 f s g) : term711 _132203 x s.
Proof. exact (fun h0 : term409 _132203 x s => @lem7077467 _132203 x'' x f s g h1 h2 h3 h4 h5). Qed.
Lemma lem7077470 (p : Prop) : (term593 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7077471 {_132203 : Type'} (x : type684 _132203) (s : _132203 -> Prop) : (term711 _132203 x s) = (term597 _132203 x s).
Proof. exact (@lem7077470 (term409 _132203 x s)). Qed.
Lemma lem7077472 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term29 _132203 s) (h4 : term380 _132203 x) (h5 : term80 _132203 f s g) : term597 _132203 x s.
Proof. exact (EQ_MP (@lem7077471 _132203 x s) (@lem7077468 _132203 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7077478 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7077479 {_132203 : Type'} (x : type684 _132203) (_94380 : _132203 -> Prop) : (term412 _132203 x _94380) = (term712 _132203 x _94380).
Proof. exact (@lem7077478 (_94380 = (@EMPTY _132203)) (term409 _132203 x _94380)). Qed.
Lemma lem7077487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7077488 {_132203 : Type'} (x : type684 _132203) (_94380 : _132203 -> Prop) : (term713 _132203 x _94380) = (term714 _132203 x _94380).
Proof. exact (MK_COMB (@lem7077487) (@lem7077479 _132203 x _94380)). Qed.
Lemma lem7077496 {_132203 : Type'} (x : type684 _132203) (_94380 : _132203 -> Prop) : (term712 _132203 x _94380) = (term712 _132203 x _94380).
Proof. exact (eq_refl (term712 _132203 x _94380)). Qed.
Lemma lem7077497 {_132203 : Type'} (x : type684 _132203) (_94380 : _132203 -> Prop) : ((term412 _132203 x _94380) = (term712 _132203 x _94380)) = ((term712 _132203 x _94380) = (term712 _132203 x _94380)).
Proof. exact (MK_COMB (@lem7077488 _132203 x _94380) (@lem7077496 _132203 x _94380)). Qed.
Lemma lem7077499 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7077500 (x : Prop) : (x = x) = True.
Proof. exact (@lem7077499 Prop x). Qed.
Lemma lem7077501 {_132203 : Type'} (x : type684 _132203) (_94380 : _132203 -> Prop) : ((term712 _132203 x _94380) = (term712 _132203 x _94380)) = True.
Proof. exact (@lem7077500 (term712 _132203 x _94380)). Qed.
Lemma lem7077502 {_132203 : Type'} (x : type684 _132203) (_94380 : _132203 -> Prop) : ((term412 _132203 x _94380) = (term712 _132203 x _94380)) = True.
Proof. exact (TRANS (@lem7077497 _132203 x _94380) (@lem7077501 _132203 x _94380)). Qed.
Lemma lem7077503 {_132203 : Type'} (x : type684 _132203) (_94380 : _132203 -> Prop) : True = ((term412 _132203 x _94380) = (term712 _132203 x _94380)).
Proof. exact (SYM (@lem7077502 _132203 x _94380)). Qed.
Lemma lem7077504 {_132203 : Type'} (x : type684 _132203) (_94380 : _132203 -> Prop) : (term412 _132203 x _94380) = (term712 _132203 x _94380).
Proof. exact (EQ_MP (@lem7077503 _132203 x _94380) (@lem0)). Qed.
Lemma lem7077505 {_132203 : Type'} (_94380 : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term712 _132203 x _94380.
Proof. exact (EQ_MP (@lem7077504 _132203 x _94380) (@lem7076135 _132203 _94380 x h1)). Qed.
Lemma lem7077507 (b : Prop) (a : Prop) : (a \/ b) = (term594 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7077510 {_132203 : Type'} (x : type684 _132203) (_94380 : _132203 -> Prop) : (term712 _132203 x _94380) = (term715 _132203 x _94380).
Proof. exact (@lem7077507 (term409 _132203 x _94380) (_94380 = (@EMPTY _132203))). Qed.
Lemma lem7077513 {_132203 : Type'} (_94380 : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term715 _132203 x _94380.
Proof. exact (EQ_MP (@lem7077510 _132203 x _94380) (@lem7077505 _132203 _94380 x h1)). Qed.
Lemma lem7077514 {_132203 : Type'} (_94380 : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term715 _132203 x _94380.
Proof. exact (@lem7077513 _132203 _94380 x h1). Qed.
Lemma lem7077515 {_132203 : Type'} (s : _132203 -> Prop) (x : type684 _132203) (h1 : term380 _132203 x) : term715 _132203 x s.
Proof. exact (@lem7077514 _132203 s x h1). Qed.
Lemma lem7077518 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term29 _132203 s) (h4 : term380 _132203 x) (h5 : term80 _132203 f s g) : s = (@EMPTY _132203).
Proof. exact (@lem7077515 _132203 s x h4 (@lem7077472 _132203 x'' x f s g h1 h2 h3 h4 h5)). Qed.
Lemma lem7077519 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term380 _132203 x) (h4 : term80 _132203 f s g) : term716 _132203 s.
Proof. exact (fun h0 : term29 _132203 s => @lem7077518 _132203 x'' x f s g h1 h2 h0 h3 h4). Qed.
Lemma lem7077521 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7077522 {_132203 : Type'} (s : _132203 -> Prop) : (term716 _132203 s) = (s = (@EMPTY _132203)).
Proof. exact (@lem7077521 (s = (@EMPTY _132203))). Qed.
Lemma lem7077523 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term380 _132203 x) (h4 : term80 _132203 f s g) : s = (@EMPTY _132203).
Proof. exact (EQ_MP (@lem7077522 _132203 s) (@lem7077519 _132203 x'' x f s g h1 h2 h3 h4)). Qed.
Lemma lem7077526 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7077528 {_132203 : Type'} (s : _132203 -> Prop) : (term29 _132203 s) = (term717 _132203 s).
Proof. exact (@lem7077526 (s = (@EMPTY _132203))). Qed.
Lemma lem7077531 {_132203 : Type'} (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term80 _132203 f s g) : term717 _132203 s.
Proof. exact (EQ_MP (@lem7077528 _132203 s) (@lem7076123 _132203 f s g h1)). Qed.
Lemma lem7077534 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term380 _132203 x) (h4 : term80 _132203 f s g) : False.
Proof. exact (@lem7077531 _132203 f s g h4 (@lem7077523 _132203 x'' x f s g h1 h2 h3 h4)). Qed.
Lemma lem7077535 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term380 _132203 x) (h4 : term80 _132203 f s g) : term718.
Proof. exact (fun h0 : ~ False => @lem7077534 _132203 x'' x f s g h1 h2 h3 h4). Qed.
Lemma lem7077537 (p : Prop) : (term591 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7077538 : term718 = False.
Proof. exact (@lem7077537 False). Qed.
Lemma lem7077539 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (f : _132203 -> real) (s : _132203 -> Prop) (g : _132203 -> real) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term380 _132203 x) (h4 : term80 _132203 f s g) : False.
Proof. exact (EQ_MP (@lem7077538) (@lem7077535 _132203 x'' x f s g h1 h2 h3 h4)). Qed.
Lemma lem7077540 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (g : _132203 -> real) (x : type684 _132203) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term90 _132203 f g) (h4 : term380 _132203 x) : False.
Proof. exact (ex_elim (@lem7074899 _132203 f g h3) (fun s : _132203 -> Prop => fun h0 : term89 _132203 f g s => @lem7077539 _132203 x'' x f s g h1 h2 h4 h0)). Qed.
Lemma lem7077541 {_132203 : Type'} (x'' : type711 _132203) (f : _132203 -> real) (x : type684 _132203) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term99 _132203 f) (h4 : term380 _132203 x) : False.
Proof. exact (ex_elim (@lem7074898 _132203 f h3) (fun g : _132203 -> real => fun h0 : term98 _132203 f g => @lem7077540 _132203 x'' f g x h1 h2 h0 h4)). Qed.
Lemma lem7077542 {_132203 : Type'} (x'' : type711 _132203) (x : type684 _132203) (h1 : term271 _132203 x'') (h2 : term38) (h3 : term10 _132203) (h4 : term380 _132203 x) : False.
Proof. exact (ex_elim (@lem7073782 _132203 h3) (fun f : _132203 -> real => fun h0 : term104 _132203 f => @lem7077541 _132203 x'' f x h1 h2 h0 h4)). Qed.
Lemma lem7077543 {_132203 : Type'} (x : type684 _132203) (h1 : term12 _132203) (h2 : term38) (h3 : term10 _132203) (h4 : term380 _132203 x) : False.
Proof. exact (ex_elim (@lem7074176 _132203 h1) (fun x'' : type711 _132203 => fun h0 : term273 _132203 x'' => @lem7077542 _132203 x'' x h0 h2 h3 h4)). Qed.
Lemma lem7077544 {_132203 A : Type'} (x : type684 _132203) (h1 : term12 _132203) (h2 : term12 A) (h3 : term38) (h4 : term10 _132203) (h5 : term380 _132203 x) : False.
Proof. exact (ex_elim (@lem7074570 A h2) (fun x' : type711 A => fun h0 : term273 A x' => @lem7077543 _132203 x h1 h3 h4 h5)). Qed.
Lemma lem7077545 {_132203 A : Type'} (h1 : term11 _132203) (h2 : term12 _132203) (h3 : term12 A) (h4 : term38) (h5 : term10 _132203) : False.
Proof. exact (ex_elim (@lem7074894 _132203 h1) (fun x : type684 _132203 => fun h0 : term382 _132203 x => @lem7077544 _132203 A x h2 h3 h4 h5 h0)). Qed.
Lemma lem7077546 {_132203 A : Type'} (h1 : term12 _132203) (h2 : term12 A) (h3 : term38) (h4 : term10 _132203) : term17 _132203.
Proof. exact (fun h0 : term11 _132203 => @lem7077545 _132203 A h0 h1 h2 h3 h4). Qed.
Lemma lem7077547 {_132203 : Type'} : (term17 _132203) = (term18 _132203).
Proof. exact (@lem69 (term11 _132203)). Qed.
Lemma lem7077548 {_132203 A : Type'} (h1 : term12 _132203) (h2 : term12 A) (h3 : term38) (h4 : term10 _132203) : term18 _132203.
Proof. exact (EQ_MP (@lem7077547 _132203) (@lem7077546 _132203 A h1 h2 h3 h4)). Qed.
Lemma lem7077549 {_132203 A : Type'} (h1 : term12 _132203) (h2 : term12 A) (h3 : term10 _132203) : term21 _132203.
Proof. exact (fun h0 : term38 => @lem7077548 _132203 A h1 h2 h0 h3). Qed.
Lemma lem7077550 {_132203 A : Type'} (h1 : term12 _132203) (h2 : term10 _132203) : term24 _132203 A.
Proof. exact (fun h0 : term12 A => @lem7077549 _132203 A h1 h0 h2). Qed.
Lemma lem7077551 {_132203 A : Type'} (h1 : term10 _132203) : term26 _132203 A.
Proof. exact (fun h0 : term12 _132203 => @lem7077550 _132203 A h0 h1). Qed.
Lemma lem7077552 {_132203 A : Type'} : term28 _132203 A.
Proof. exact (fun h0 : term10 _132203 => @lem7077551 _132203 A h0). Qed.
Lemma lem7077553 {_132203 A : Type'} : term13 _132203 A.
Proof. exact (EQ_MP (@lem7073614 _132203 A) (@lem7077552 _132203 A)). Qed.
Lemma lem7077555 {_132203 A : Type'} : term13 _132203 A.
Proof. exact (@lem7073100 _132203 A (@lem7077553 _132203 A)). Qed.
Lemma lem7077556 {_132203 A : Type'} (h1 : term10 _132203) : term25 _132203 A.
Proof. exact (@lem7077555 _132203 A (@lem7073078 _132203 h1)). Qed.
Lemma lem7077557 {_132203 A : Type'} (h1 : term10 _132203) : term23 _132203 A.
Proof. exact (@lem7077556 _132203 A h1 (@lem7073082 _132203)). Qed.
Lemma lem7077558 {_132203 : Type'} (h1 : term10 _132203) : term20 _132203.
Proof. exact (@lem7077557 _132203 Prop h1 (@lem7073063 Prop)). Qed.
Lemma lem7077559 {_132203 : Type'} (h1 : term10 _132203) : term17 _132203.
Proof. exact (@lem7077558 _132203 h1 (@lem1369133)). Qed.
Lemma lem7077560 {_132203 : Type'} (h1 : term10 _132203) : False.
Proof. exact (@lem7077559 _132203 h1 (@lem7073079 _132203)). Qed.
Lemma lem7077561 {_132203 : Type'} (h1 : term10 _132203) : (term10 _132203) = False.
Proof. exact (prop_ext (fun h2 : term10 _132203 => @lem7077560 _132203 h1) (fun h2 : False => @lem7073078 _132203 h1)). Qed.
Lemma lem7077562 {_132203 : Type'} (h1 : term10 _132203) : False.
Proof. exact (EQ_MP (@lem7077561 _132203 h1) (@lem7073078 _132203 h1)). Qed.
Lemma lem7077563 {_132203 : Type'} : term9 _132203.
Proof. exact (fun h0 : term10 _132203 => @lem7077562 _132203 h0). Qed.
Lemma lem7077564 {_132203 : Type'} : term8 _132203.
Proof. exact (EQ_MP (@lem7073077 _132203) (@lem7077563 _132203)). Qed.
