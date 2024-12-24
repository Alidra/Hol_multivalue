Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_UNION_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3279178 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (_476 : type686 A) (_477 : A -> Prop) : (term0 A _476 _475 _474 _477) = (term1 A _474 _475 _476 _477).
Proof. exact (@lem13473 (A -> Prop) _474 _475 _476 _477). Qed.
Lemma lem3279179 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (x : A) (s : A -> Prop) (t : A -> Prop) (_477 : A -> Prop) : (term2 A x s t _475 _474 _477) = (term3 A _474 _475 x s t _477).
Proof. exact (@lem3279178 A _474 _475 (term4 A x s t) _477). Qed.
Lemma lem3279180 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term5 A x s t) = (term6 A x s t).
Proof. exact (@lem3279179 A (@UNION A s t) (@IN A x t) x s t (term7 A x s t)). Qed.
Lemma lem3279181 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term8 A x s t) = ((term9 A x s t) = (term7 A x s t)).
Proof. exact (eq_refl (term8 A x s t)). Qed.
Lemma lem3279182 {A : Type'} (x : A) (t : A -> Prop) : (term10 A x t) = (term10 A x t).
Proof. exact (eq_refl (term10 A x t)). Qed.
Lemma lem3279183 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term11 A x s t) = (term12 A x s t).
Proof. exact (MK_COMB (@lem3279182 A x t) (@lem3279181 A x s t)). Qed.
Lemma lem3279184 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term13 A x s t) = ((term9 A x s t) = (@UNION A s t)).
Proof. exact (eq_refl (term13 A x s t)). Qed.
Lemma lem3279185 {A : Type'} (x : A) (t : A -> Prop) : (term14 A x t) = (term14 A x t).
Proof. exact (eq_refl (term14 A x t)). Qed.
Lemma lem3279186 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term15 A x s t) = (term16 A x s t).
Proof. exact (MK_COMB (@lem3279185 A x t) (@lem3279184 A x s t)). Qed.
Lemma lem3279187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3279188 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term17 A x s t) = (term18 A x s t).
Proof. exact (MK_COMB (@lem3279187) (@lem3279186 A x s t)). Qed.
Lemma lem3279189 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term6 A x s t) = (term19 A x s t).
Proof. exact (MK_COMB (@lem3279188 A x s t) (@lem3279183 A x s t)). Qed.
Lemma lem3279190 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term5 A x s t) = ((term9 A x s t) = (term20 A x s t)).
Proof. exact (eq_refl (term5 A x s t)). Qed.
Lemma lem3279191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3279192 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term21 A x s t) = (term22 A x s t).
Proof. exact (MK_COMB (@lem3279191) (@lem3279190 A x s t)). Qed.
Lemma lem3279193 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term5 A x s t) = (term6 A x s t)) = (((term9 A x s t) = (term20 A x s t)) = (term19 A x s t)).
Proof. exact (MK_COMB (@lem3279192 A x s t) (@lem3279189 A x s t)). Qed.
Lemma lem3279194 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term9 A x s t) = (term20 A x s t)) = (term19 A x s t).
Proof. exact (EQ_MP (@lem3279193 A x s t) (@lem3279180 A x s t)). Qed.
Lemma lem3279195 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term19 A x s t) = ((term9 A x s t) = (term20 A x s t)).
Proof. exact (SYM (@lem3279194 A x s t)). Qed.
Lemma lem3279196 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3279213 {A : Type'} (x : A) (t : A -> Prop) (h1 : term23 A x t) : term23 A x t.
Proof. exact (h1). Qed.
Lemma lem3279235 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3279236 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (@lem3279235 A s t). Qed.
Lemma lem3279237 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term9 A x s t) = (@UNION A s t)) = (term25 A x s t).
Proof. exact (@lem3279236 A (term9 A x s t) (@UNION A s t)). Qed.
Lemma lem3279246 {A : Type'} (x : A) (t : A -> Prop) : (term14 A x t) = (term14 A x t).
Proof. exact (eq_refl (term14 A x t)). Qed.
Lemma lem3279247 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term16 A x s t) = (term26 A x s t).
Proof. exact (MK_COMB (@lem3279246 A x t) (@lem3279237 A x s t)). Qed.
Lemma lem3279250 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term26 A x s t) = (term16 A x s t).
Proof. exact (SYM (@lem3279247 A x s t)). Qed.
Lemma lem3279254 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3279255 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3279254 A P x). Qed.
Lemma lem3279256 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3279255 A t x). Qed.
Lemma lem3279257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3279258 {A : Type'} (t : A -> Prop) (x : A) : (term14 A x t) = (term27 A t x).
Proof. exact (MK_COMB (@lem3279257) (@lem3279256 A t x)). Qed.
Lemma lem3279266 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3279267 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (@lem3279266 A s x t). Qed.
Lemma lem3279268 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term30 A x' x s t) = (term31 A x s x' t).
Proof. exact (@lem3279267 A (@INSERT A x s) x' t). Qed.
Lemma lem3279272 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3279273 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (@lem3279272 A y x s). Qed.
Lemma lem3279274 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term32 A x' x s) = (term33 A x x' s).
Proof. exact (@lem3279273 A x x' s). Qed.
Lemma lem3279280 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3279281 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3279280 A P x). Qed.
Lemma lem3279282 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3279281 A s x'). Qed.
Lemma lem3279283 {A : Type'} (x' : A) (x : A) : (term34 A x' x) = (term34 A x' x).
Proof. exact (eq_refl (term34 A x' x)). Qed.
Lemma lem3279284 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term33 A x x' s) = (term35 A x s x').
Proof. exact (MK_COMB (@lem3279283 A x' x) (@lem3279282 A s x')). Qed.
Lemma lem3279287 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term32 A x' x s) = (term35 A x s x').
Proof. exact (TRANS (@lem3279274 A x x' s) (@lem3279284 A x s x')). Qed.
Lemma lem3279288 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3279289 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term36 A x' x s) = (term37 A x s x').
Proof. exact (MK_COMB (@lem3279288) (@lem3279287 A x s x')). Qed.
Lemma lem3279291 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3279292 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3279291 A P x). Qed.
Lemma lem3279293 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3279292 A t x'). Qed.
Lemma lem3279294 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term31 A x s x' t) = (term38 A x s t x').
Proof. exact (MK_COMB (@lem3279289 A x s x') (@lem3279293 A t x')). Qed.
Lemma lem3279297 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term30 A x' x s t) = (term38 A x s t x').
Proof. exact (TRANS (@lem3279268 A x s x' t) (@lem3279294 A x s t x')). Qed.
Lemma lem3279298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3279299 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term39 A x' x s t) = (term40 A x s t x').
Proof. exact (MK_COMB (@lem3279298) (@lem3279297 A x s t x')). Qed.
Lemma lem3279301 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3279302 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (@lem3279301 A s x t). Qed.
Lemma lem3279303 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) : (term28 A x' s t) = (term29 A s x' t).
Proof. exact (@lem3279302 A s x' t). Qed.
Lemma lem3279307 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3279308 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3279307 A P x). Qed.
Lemma lem3279309 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3279308 A s x'). Qed.
Lemma lem3279310 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3279311 {A : Type'} (s : A -> Prop) (x' : A) : (term41 A x' s) = (term42 A s x').
Proof. exact (MK_COMB (@lem3279310) (@lem3279309 A s x')). Qed.
Lemma lem3279313 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3279314 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3279313 A P x). Qed.
Lemma lem3279315 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3279314 A t x'). Qed.
Lemma lem3279316 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term29 A s x' t) = (term43 A s t x').
Proof. exact (MK_COMB (@lem3279311 A s x') (@lem3279315 A t x')). Qed.
Lemma lem3279319 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term28 A x' s t) = (term43 A s t x').
Proof. exact (TRANS (@lem3279303 A s x' t) (@lem3279316 A s t x')). Qed.
Lemma lem3279320 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term30 A x' x s t) = (term28 A x' s t)) = ((term38 A x s t x') = (term43 A s t x')).
Proof. exact (MK_COMB (@lem3279299 A x s t x') (@lem3279319 A s t x')). Qed.
Lemma lem3279323 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term44 A x s t) = (term45 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3279320 A x s t x')). Qed.
Lemma lem3279324 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3279325 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term25 A x s t) = (term46 A x s t).
Proof. exact (MK_COMB (@lem3279324 A) (@lem3279323 A x s t)). Qed.
Lemma lem3279330 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term26 A x s t) = (term47 A x s t).
Proof. exact (MK_COMB (@lem3279258 A t x) (@lem3279325 A x s t)). Qed.
Lemma lem3279333 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term47 A x s t) = (term26 A x s t).
Proof. exact (SYM (@lem3279330 A x s t)). Qed.
Lemma lem3279335 (p : Prop) : p = (term48 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3279336 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term47 A x s t) = (term49 A x s t).
Proof. exact (@lem3279335 (term47 A x s t)). Qed.
Lemma lem3279337 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term49 A x s t) = (term47 A x s t).
Proof. exact (SYM (@lem3279336 A x s t)). Qed.
Lemma lem3279338 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term50 A x s t) : term50 A x s t.
Proof. exact (h1). Qed.
Lemma lem3279341 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term49 A x s t) : term49 A x s t.
Proof. exact (h1). Qed.
Lemma lem3279342 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term51 A x s t.
Proof. exact (fun h0 : term49 A x s t => @lem3279341 A x s t h0). Qed.
Lemma lem3279343 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term51 A x s t) : term51 A x s t.
Proof. exact (h1). Qed.
Lemma lem3279344 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term49 A x s t) : term49 A x s t.
Proof. exact (h1). Qed.
Lemma lem3279345 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term49 A x s t) (h2 : term51 A x s t) : term49 A x s t.
Proof. exact (@lem3279343 A x s t h2 (@lem3279344 A x s t h1)). Qed.
Lemma lem3279346 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term49 A x s t) : term52 A x s t.
Proof. exact (fun h0 : term51 A x s t => @lem3279345 A x s t h1 h0). Qed.
Lemma lem3279347 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term51 A x s t) : term51 A x s t.
Proof. exact (h1). Qed.
Lemma lem3279348 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term49 A x s t) (h2 : term51 A x s t) : term49 A x s t.
Proof. exact (@lem3279346 A x s t h1 (@lem3279347 A x s t h2)). Qed.
Lemma lem3279349 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term51 A x s t) : term51 A x s t.
Proof. exact (fun h0 : term49 A x s t => @lem3279348 A x s t h0 h1). Qed.
Lemma lem3279350 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term53 A x s t.
Proof. exact (fun h0 : term51 A x s t => @lem3279349 A x s t h0). Qed.
Lemma lem3279353 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term51 A x s t.
Proof. exact (@lem3279350 A x s t (@lem3279342 A x s t)). Qed.
Lemma lem3279354 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term51 A x s t.
Proof. exact (@lem3279353 A x s t). Qed.
Lemma lem3279368 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3279369 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term49 A x s t) = (term54 A x s t).
Proof. exact (@lem3279368 (term50 A x s t)). Qed.
Lemma lem3279371 (t : Prop) : (term55 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3279372 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term54 A x s t) = (term47 A x s t).
Proof. exact (@lem3279371 (term47 A x s t)). Qed.
Lemma lem3279375 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term49 A x s t) = (term47 A x s t).
Proof. exact (TRANS (@lem3279369 A x s t) (@lem3279372 A x s t)). Qed.
Lemma lem3279386 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term56 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3279375 A x s t)). Qed.
Lemma lem3279387 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3279388 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term59 A s t).
Proof. exact (MK_COMB (@lem3279387 A) (@lem3279386 A s t)). Qed.
Lemma lem3279393 {A : Type'} (t : A -> Prop) : (term60 A t) = (term61 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3279388 A s t)). Qed.
Lemma lem3279394 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3279395 {A : Type'} (t : A -> Prop) : (term62 A t) = (term63 A t).
Proof. exact (MK_COMB (@lem3279394 A) (@lem3279393 A t)). Qed.
Lemma lem3279400 {A : Type'} : (term64 A) = (term65 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3279395 A t)). Qed.
Lemma lem3279401 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3279410 {A : Type'} : (term66 A) = (term67 A).
Proof. exact (MK_COMB (@lem3279401 A) (@lem3279400 A)). Qed.
Lemma lem3279427 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term38 A x s t x') = (term43 A s t x')) = ((term38 A x s t x') = (term43 A s t x')).
Proof. exact (eq_refl ((term38 A x s t x') = (term43 A s t x'))). Qed.
Lemma lem3279428 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term45 A x s t) = (term45 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3279427 A x s t x')). Qed.
Lemma lem3279429 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3279430 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term46 A x s t) = (term46 A x s t).
Proof. exact (MK_COMB (@lem3279429 A) (@lem3279428 A x s t)). Qed.
Lemma lem3279433 {A : Type'} (t : A -> Prop) (x : A) : (term27 A t x) = (term27 A t x).
Proof. exact (eq_refl (term27 A t x)). Qed.
Lemma lem3279434 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term47 A x s t) = (term47 A x s t).
Proof. exact (MK_COMB (@lem3279433 A t x) (@lem3279430 A x s t)). Qed.
Lemma lem3279435 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term57 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3279434 A x s t)). Qed.
Lemma lem3279436 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3279437 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term59 A s t) = (term59 A s t).
Proof. exact (MK_COMB (@lem3279436 A) (@lem3279435 A s t)). Qed.
Lemma lem3279438 {A : Type'} (t : A -> Prop) : (term61 A t) = (term61 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3279437 A s t)). Qed.
Lemma lem3279439 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3279440 {A : Type'} (t : A -> Prop) : (term63 A t) = (term63 A t).
Proof. exact (MK_COMB (@lem3279439 A) (@lem3279438 A t)). Qed.
Lemma lem3279441 {A : Type'} : (term65 A) = (term65 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3279440 A t)). Qed.
Lemma lem3279442 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3279443 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (MK_COMB (@lem3279442 A) (@lem3279441 A)). Qed.
Lemma lem3279478 {A : Type'} : (term66 A) = (term67 A).
Proof. exact (TRANS (@lem3279410 A) (@lem3279443 A)). Qed.
Lemma lem3279479 {A : Type'} : (term67 A) = (term66 A).
Proof. exact (SYM (@lem3279478 A)). Qed.
Lemma lem3279482 (p : Prop) : p = (term48 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3279483 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term38 A x s t x') = (term43 A s t x')) = (term68 A x s t x').
Proof. exact (@lem3279482 ((term38 A x s t x') = (term43 A s t x'))). Qed.
Lemma lem3279484 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term68 A x s t x') = ((term38 A x s t x') = (term43 A s t x')).
Proof. exact (SYM (@lem3279483 A x s t x')). Qed.
Lemma lem3279485 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term69 A x s t x') : term69 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3279491 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3279500 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term70 A x s x') = (term71 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3279504 {A : Type'} (t : A -> Prop) (x' : A) : (term72 A t x') = (term72 A t x').
Proof. exact (eq_refl (term72 A t x')). Qed.
Lemma lem3279506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3279507 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term73 A x s x') = (term74 A x s x').
Proof. exact (MK_COMB (@lem3279506) (@lem3279500 A x s x')). Qed.
Lemma lem3279508 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term75 A x s t x') = (term76 A x s t x').
Proof. exact (MK_COMB (@lem3279507 A x s x') (@lem3279504 A t x')). Qed.
Lemma lem3279509 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term77 A x s t x') = (term75 A x s t x').
Proof. exact (@lem17160 (term35 A x s x') (t x')). Qed.
Lemma lem3279510 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term77 A x s t x') = (term76 A x s t x').
Proof. exact (TRANS (@lem3279509 A x s t x') (@lem3279508 A x s t x')). Qed.
Lemma lem3279522 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term78 A s t x') = (term79 A s t x').
Proof. exact (@lem17160 (s x') (t x')). Qed.
Lemma lem3279525 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term43 A s t x') = (term43 A s t x').
Proof. exact (eq_refl (term43 A s t x')). Qed.
Lemma lem3279526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3279527 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term80 A x s t x') = (term81 A x s t x').
Proof. exact (MK_COMB (@lem3279526) (@lem3279510 A x s t x')). Qed.
Lemma lem3279528 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term82 A x s t x') = (term83 A x s t x').
Proof. exact (MK_COMB (@lem3279527 A x s t x') (@lem3279525 A s t x')). Qed.
Lemma lem3279530 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term84 A x s t x') = (term84 A x s t x').
Proof. exact (eq_refl (term84 A x s t x')). Qed.
Lemma lem3279531 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term85 A x s t x') = (term86 A x s t x').
Proof. exact (MK_COMB (@lem3279530 A x s t x') (@lem3279522 A s t x')). Qed.
Lemma lem3279532 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3279533 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term87 A x s t x') = (term88 A x s t x').
Proof. exact (MK_COMB (@lem3279532) (@lem3279531 A x s t x')). Qed.
Lemma lem3279534 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term89 A x s t x') = (term90 A x s t x').
Proof. exact (MK_COMB (@lem3279533 A x s t x') (@lem3279528 A x s t x')). Qed.
Lemma lem3279535 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term69 A x s t x') = (term89 A x s t x').
Proof. exact (@lem17646 (term38 A x s t x') (term43 A s t x')). Qed.
Lemma lem3279540 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term69 A x s t x') = (term90 A x s t x').
Proof. exact (TRANS (@lem3279535 A x s t x') (@lem3279534 A x s t x')). Qed.
Lemma lem3279545 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3279617 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term69 A x s t x') : term90 A x s t x'.
Proof. exact (EQ_MP (@lem3279540 A x s t x') (@lem3279485 A x s t x' h1)). Qed.
Lemma lem3279618 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term86 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3279619 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term83 A x s t x') : term83 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3279620 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term79 A s t x'.
Proof. exact (proj2 (@lem3279618 A x s t x' h1)). Qed.
Lemma lem3279621 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term38 A x s t x'.
Proof. exact (proj1 (@lem3279618 A x s t x' h1)). Qed.
Lemma lem3279624 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term35 A x s x') : term35 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3279628 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term83 A x s t x') : term43 A s t x'.
Proof. exact (proj2 (@lem3279619 A x s t x' h1)). Qed.
Lemma lem3279629 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term83 A x s t x') : term76 A x s t x'.
Proof. exact (proj1 (@lem3279619 A x s t x' h1)). Qed.
Lemma lem3279631 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term83 A x s t x') : term71 A x s x'.
Proof. exact (proj1 (@lem3279629 A x s t x' h1)). Qed.
Lemma lem3279639 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3279651 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3279667 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3279683 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3279703 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3279723 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3279725 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3279729 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term72 A t x'.
Proof. exact (proj2 (@lem3279620 A x s t x' h1)). Qed.
Lemma lem3279731 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3279735 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term72 A s x'.
Proof. exact (proj1 (@lem3279620 A x s t x' h1)). Qed.
Lemma lem3279739 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3279745 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term72 A t x'.
Proof. exact (proj2 (@lem3279620 A x s t x' h1)). Qed.
Lemma lem3279747 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3279755 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term83 A x s t x') : term72 A s x'.
Proof. exact (proj2 (@lem3279631 A x s t x' h1)). Qed.
Lemma lem3279757 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3279761 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term83 A x s t x') : term72 A t x'.
Proof. exact (proj2 (@lem3279629 A x s t x' h1)). Qed.
Lemma lem3279767 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3279795 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3279809 {A : Type'} (t : A -> Prop) : (term91 A t) = (term91 A t).
Proof. exact (eq_refl (term91 A t)). Qed.
Lemma lem3279810 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term92 A t x') = (term92 A t x).
Proof. exact (MK_COMB (@lem3279809 A t) (@lem3279731 A x' x h1)). Qed.
Lemma lem3279811 {A : Type'} (t : A -> Prop) (x : A) : (term92 A t x) = (term72 A t x).
Proof. exact (eq_refl (term92 A t x)). Qed.
Lemma lem3279812 {A : Type'} (t : A -> Prop) (x' : A) : (term93 A t x') = (term93 A t x').
Proof. exact (eq_refl (term93 A t x')). Qed.
Lemma lem3279813 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term92 A t x') = (term92 A t x)) = ((term92 A t x') = (term72 A t x)).
Proof. exact (MK_COMB (@lem3279812 A t x') (@lem3279811 A t x)). Qed.
Lemma lem3279814 {A : Type'} (t : A -> Prop) (x' : A) : (term92 A t x') = (term72 A t x').
Proof. exact (eq_refl (term92 A t x')). Qed.
Lemma lem3279815 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3279816 {A : Type'} (t : A -> Prop) (x' : A) : (term93 A t x') = (term94 A t x').
Proof. exact (MK_COMB (@lem3279815) (@lem3279814 A t x')). Qed.
Lemma lem3279817 {A : Type'} (t : A -> Prop) (x : A) : (term72 A t x) = (term72 A t x).
Proof. exact (eq_refl (term72 A t x)). Qed.
Lemma lem3279818 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term92 A t x') = (term72 A t x)) = ((term72 A t x') = (term72 A t x)).
Proof. exact (MK_COMB (@lem3279816 A t x') (@lem3279817 A t x)). Qed.
Lemma lem3279819 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term92 A t x') = (term92 A t x)) = ((term72 A t x') = (term72 A t x)).
Proof. exact (TRANS (@lem3279813 A x' t x) (@lem3279818 A x' t x)). Qed.
Lemma lem3279820 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term72 A t x') = (term72 A t x).
Proof. exact (EQ_MP (@lem3279819 A x' t x) (@lem3279810 A t x' x h1)). Qed.
Lemma lem3279821 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term86 A x s t x') (h2 : x' = x) : term72 A t x.
Proof. exact (EQ_MP (@lem3279820 A t x' x h2) (@lem3279729 A x s t x' h1)). Qed.
Lemma lem3279823 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3279824 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term95 A t x.
Proof. exact (fun h0 : term72 A t x => @lem3279823 A t x h1). Qed.
Lemma lem3279826 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3279827 {A : Type'} (t : A -> Prop) (x : A) : (term95 A t x) = (t x).
Proof. exact (@lem3279826 (t x)). Qed.
Lemma lem3279828 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3279827 A t x) (@lem3279824 A t x h1)). Qed.
Lemma lem3279831 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3279833 {A : Type'} (t : A -> Prop) (x : A) : (term72 A t x) = (term97 A t x).
Proof. exact (@lem3279831 (t x)). Qed.
Lemma lem3279836 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term86 A x s t x') (h2 : x' = x) : term97 A t x.
Proof. exact (EQ_MP (@lem3279833 A t x) (@lem3279821 A s t x' x h1 h2)). Qed.
Lemma lem3279839 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : False.
Proof. exact (@lem3279836 A s t x' x h2 h3 (@lem3279828 A t x h1)). Qed.
Lemma lem3279840 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : term98.
Proof. exact (fun h0 : ~ False => @lem3279839 A s t x' x h1 h2 h3). Qed.
Lemma lem3279842 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3279843 : term98 = False.
Proof. exact (@lem3279842 False). Qed.
Lemma lem3279844 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3279843) (@lem3279840 A s t x' x h1 h2 h3)). Qed.
Lemma lem3279846 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3279847 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term95 A s x'.
Proof. exact (fun h0 : term72 A s x' => @lem3279846 A s x' h1). Qed.
Lemma lem3279849 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3279850 {A : Type'} (s : A -> Prop) (x' : A) : (term95 A s x') = (s x').
Proof. exact (@lem3279849 (s x')). Qed.
Lemma lem3279851 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3279850 A s x') (@lem3279847 A s x' h1)). Qed.
Lemma lem3279854 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3279856 {A : Type'} (s : A -> Prop) (x' : A) : (term72 A s x') = (term97 A s x').
Proof. exact (@lem3279854 (s x')). Qed.
Lemma lem3279859 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term97 A s x'.
Proof. exact (EQ_MP (@lem3279856 A s x') (@lem3279735 A x s t x' h1)). Qed.
Lemma lem3279862 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term86 A x s t x') : False.
Proof. exact (@lem3279859 A x s t x' h2 (@lem3279851 A s x' h1)). Qed.
Lemma lem3279863 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term86 A x s t x') : term98.
Proof. exact (fun h0 : ~ False => @lem3279862 A x s t x' h1 h2). Qed.
Lemma lem3279865 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3279866 : term98 = False.
Proof. exact (@lem3279865 False). Qed.
Lemma lem3279867 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3279866) (@lem3279863 A x s t x' h1 h2)). Qed.
Lemma lem3279869 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3279870 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term95 A t x'.
Proof. exact (fun h0 : term72 A t x' => @lem3279869 A t x' h1). Qed.
Lemma lem3279872 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3279873 {A : Type'} (t : A -> Prop) (x' : A) : (term95 A t x') = (t x').
Proof. exact (@lem3279872 (t x')). Qed.
Lemma lem3279874 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3279873 A t x') (@lem3279870 A t x' h1)). Qed.
Lemma lem3279877 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3279879 {A : Type'} (t : A -> Prop) (x' : A) : (term72 A t x') = (term97 A t x').
Proof. exact (@lem3279877 (t x')). Qed.
Lemma lem3279882 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term86 A x s t x') : term97 A t x'.
Proof. exact (EQ_MP (@lem3279879 A t x') (@lem3279745 A x s t x' h1)). Qed.
Lemma lem3279885 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : False.
Proof. exact (@lem3279882 A x s t x' h2 (@lem3279874 A t x' h1)). Qed.
Lemma lem3279886 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : term98.
Proof. exact (fun h0 : ~ False => @lem3279885 A x s t x' h1 h2). Qed.
Lemma lem3279888 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3279889 : term98 = False.
Proof. exact (@lem3279888 False). Qed.
Lemma lem3279890 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3279889) (@lem3279886 A x s t x' h1 h2)). Qed.
Lemma lem3279918 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3279919 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term95 A s x'.
Proof. exact (fun h0 : term72 A s x' => @lem3279918 A s x' h1). Qed.
Lemma lem3279921 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3279922 {A : Type'} (s : A -> Prop) (x' : A) : (term95 A s x') = (s x').
Proof. exact (@lem3279921 (s x')). Qed.
Lemma lem3279923 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3279922 A s x') (@lem3279919 A s x' h1)). Qed.
Lemma lem3279926 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3279928 {A : Type'} (s : A -> Prop) (x' : A) : (term72 A s x') = (term97 A s x').
Proof. exact (@lem3279926 (s x')). Qed.
Lemma lem3279931 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term83 A x s t x') : term97 A s x'.
Proof. exact (EQ_MP (@lem3279928 A s x') (@lem3279755 A x s t x' h1)). Qed.
Lemma lem3279934 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term83 A x s t x') : False.
Proof. exact (@lem3279931 A x s t x' h2 (@lem3279923 A s x' h1)). Qed.
Lemma lem3279935 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term83 A x s t x') : term98.
Proof. exact (fun h0 : ~ False => @lem3279934 A x s t x' h1 h2). Qed.
Lemma lem3279937 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3279938 : term98 = False.
Proof. exact (@lem3279937 False). Qed.
Lemma lem3279939 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term83 A x s t x') : False.
Proof. exact (EQ_MP (@lem3279938) (@lem3279935 A x s t x' h1 h2)). Qed.
Lemma lem3279967 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3279968 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term95 A t x'.
Proof. exact (fun h0 : term72 A t x' => @lem3279967 A t x' h1). Qed.
Lemma lem3279970 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3279971 {A : Type'} (t : A -> Prop) (x' : A) : (term95 A t x') = (t x').
Proof. exact (@lem3279970 (t x')). Qed.
Lemma lem3279972 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3279971 A t x') (@lem3279968 A t x' h1)). Qed.
Lemma lem3279975 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3279977 {A : Type'} (t : A -> Prop) (x' : A) : (term72 A t x') = (term97 A t x').
Proof. exact (@lem3279975 (t x')). Qed.
Lemma lem3279980 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term83 A x s t x') : term97 A t x'.
Proof. exact (EQ_MP (@lem3279977 A t x') (@lem3279761 A x s t x' h1)). Qed.
Lemma lem3279983 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term83 A x s t x') : False.
Proof. exact (@lem3279980 A x s t x' h2 (@lem3279972 A t x' h1)). Qed.
Lemma lem3279984 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term83 A x s t x') : term98.
Proof. exact (fun h0 : ~ False => @lem3279983 A x s t x' h1 h2). Qed.
Lemma lem3279986 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3279987 : term98 = False.
Proof. exact (@lem3279986 False). Qed.
Lemma lem3279988 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term83 A x s t x') : False.
Proof. exact (EQ_MP (@lem3279987) (@lem3279984 A x s t x' h1 h2)). Qed.
Lemma lem3279989 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3279844 A s t x' x h1 h2 h3) (fun h4 : False => @lem3279795 A t x h1)). Qed.
Lemma lem3279991 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3279989 A s t x' x h1 h2 h3) (@lem3279795 A t x h1)). Qed.
Lemma lem3279992 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term83 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3279988 A x s t x' h1 h2) (fun h3 : False => @lem3279767 A t x' h1)). Qed.
Lemma lem3279993 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term83 A x s t x') : False.
Proof. exact (EQ_MP (@lem3279992 A x s t x' h1 h2) (@lem3279767 A t x' h1)). Qed.
Lemma lem3279994 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term83 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3279939 A x s t x' h1 h2) (fun h3 : False => @lem3279757 A s x' h1)). Qed.
Lemma lem3279995 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term83 A x s t x') : False.
Proof. exact (EQ_MP (@lem3279994 A x s t x' h1 h2) (@lem3279757 A s x' h1)). Qed.
Lemma lem3279996 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3279890 A x s t x' h1 h2) (fun h3 : False => @lem3279747 A t x' h1)). Qed.
Lemma lem3279997 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3279996 A x s t x' h1 h2) (@lem3279747 A t x' h1)). Qed.
Lemma lem3279998 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term86 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3279867 A x s t x' h1 h2) (fun h3 : False => @lem3279739 A s x' h1)). Qed.
Lemma lem3279999 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3279998 A x s t x' h1 h2) (@lem3279739 A s x' h1)). Qed.
Lemma lem3280000 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3279991 A s t x' x h1 h2 h3) (fun h4 : False => @lem3279731 A x' x h3)). Qed.
Lemma lem3280001 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3280000 A s t x' x h1 h2 h3) (@lem3279731 A x' x h3)). Qed.
Lemma lem3280002 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3280001 A s t x' x h1 h2 h3) (fun h4 : False => @lem3279725 A t x h1)). Qed.
Lemma lem3280003 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3280002 A s t x' x h1 h2 h3) (@lem3279725 A t x h1)). Qed.
Lemma lem3280004 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term83 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3279993 A x s t x' h1 h2) (fun h3 : False => @lem3279723 A t x' h1)). Qed.
Lemma lem3280005 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term83 A x s t x') : False.
Proof. exact (EQ_MP (@lem3280004 A x s t x' h1 h2) (@lem3279723 A t x' h1)). Qed.
Lemma lem3280006 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term83 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3279995 A x s t x' h1 h2) (fun h3 : False => @lem3279703 A s x' h1)). Qed.
Lemma lem3280007 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term83 A x s t x') : False.
Proof. exact (EQ_MP (@lem3280006 A x s t x' h1 h2) (@lem3279703 A s x' h1)). Qed.
Lemma lem3280008 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3279997 A x s t x' h1 h2) (fun h3 : False => @lem3279683 A t x' h1)). Qed.
Lemma lem3280009 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3280008 A x s t x' h1 h2) (@lem3279683 A t x' h1)). Qed.
Lemma lem3280010 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term86 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3279999 A x s t x' h1 h2) (fun h3 : False => @lem3279667 A s x' h1)). Qed.
Lemma lem3280011 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3280010 A x s t x' h1 h2) (@lem3279667 A s x' h1)). Qed.
Lemma lem3280012 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3280003 A s t x' x h1 h2 h3) (fun h4 : False => @lem3279651 A x' x h3)). Qed.
Lemma lem3280013 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3280012 A s t x' x h1 h2 h3) (@lem3279651 A x' x h3)). Qed.
Lemma lem3280014 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3280013 A s t x' x h1 h2 h3) (fun h4 : False => @lem3279639 A t x h1)). Qed.
Lemma lem3280015 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3280014 A s t x' x h1 h2 h3) (@lem3279639 A t x h1)). Qed.
Lemma lem3280016 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term83 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3280005 A x s t x' h1 h2) (fun h3 : False => @lem3279723 A t x' h1)). Qed.
Lemma lem3280017 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term83 A x s t x') : False.
Proof. exact (EQ_MP (@lem3280016 A x s t x' h1 h2) (@lem3279723 A t x' h1)). Qed.
Lemma lem3280018 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term83 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3280007 A x s t x' h1 h2) (fun h3 : False => @lem3279703 A s x' h1)). Qed.
Lemma lem3280019 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term83 A x s t x') : False.
Proof. exact (EQ_MP (@lem3280018 A x s t x' h1 h2) (@lem3279703 A s x' h1)). Qed.
Lemma lem3280020 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3280009 A x s t x' h1 h2) (fun h3 : False => @lem3279683 A t x' h1)). Qed.
Lemma lem3280021 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3280020 A x s t x' h1 h2) (@lem3279683 A t x' h1)). Qed.
Lemma lem3280022 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term86 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3280011 A x s t x' h1 h2) (fun h3 : False => @lem3279667 A s x' h1)). Qed.
Lemma lem3280023 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term86 A x s t x') : False.
Proof. exact (EQ_MP (@lem3280022 A x s t x' h1 h2) (@lem3279667 A s x' h1)). Qed.
Lemma lem3280024 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3280015 A s t x' x h1 h2 h3) (fun h4 : False => @lem3279651 A x' x h3)). Qed.
Lemma lem3280025 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3280024 A s t x' x h1 h2 h3) (@lem3279651 A x' x h3)). Qed.
Lemma lem3280026 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3280025 A s t x' x h1 h2 h3) (fun h4 : False => @lem3279639 A t x h1)). Qed.
Lemma lem3280027 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3280026 A s t x' x h1 h2 h3) (@lem3279639 A t x h1)). Qed.
Lemma lem3280028 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term83 A x s t x') : False.
Proof. exact (or_elim (@lem3279628 A x s t x' h1) (fun h0 : s x' => @lem3280019 A x s t x' h0 h1) (fun h0 : t x' => @lem3280017 A x s t x' h0 h1)). Qed.
Lemma lem3280029 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : t x) (h2 : term86 A x s t x') (h3 : term35 A x s x') : False.
Proof. exact (or_elim (@lem3279624 A x s x' h3) (fun h0 : x' = x => @lem3280027 A s t x' x h1 h2 h0) (fun h0 : s x' => @lem3280023 A x s t x' h0 h2)). Qed.
Lemma lem3280030 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x) (h2 : term86 A x s t x') : False.
Proof. exact (or_elim (@lem3279621 A x s t x' h2) (fun h0 : term35 A x s x' => @lem3280029 A t x s x' h1 h2 h0) (fun h0 : t x' => @lem3280021 A x s t x' h0 h2)). Qed.
Lemma lem3280031 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term69 A x s t x') (h2 : t x) : False.
Proof. exact (or_elim (@lem3279617 A x s t x' h1) (fun h0 : term86 A x s t x' => @lem3280030 A x s t x' h2 h0) (fun h0 : term83 A x s t x' => @lem3280028 A x s t x' h0)). Qed.
Lemma lem3280032 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term69 A x s t x') (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3280031 A s x' t x h1 h2) (fun h3 : False => @lem3279545 A t x h2)). Qed.
Lemma lem3280033 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term69 A x s t x') (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3280032 A s x' t x h1 h2) (@lem3279545 A t x h2)). Qed.
Lemma lem3280034 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term69 A x s t x') (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3280033 A s x' t x h1 h2) (fun h3 : False => @lem3279491 A t x h2)). Qed.
Lemma lem3280035 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term69 A x s t x') (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3280034 A s x' t x h1 h2) (@lem3279491 A t x h2)). Qed.
Lemma lem3280036 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term69 A x s t x') (h2 : t x) : (term69 A x s t x') = False.
Proof. exact (prop_ext (fun h3 : term69 A x s t x' => @lem3280035 A s x' t x h1 h2) (fun h3 : False => @lem3279485 A x s t x' h1)). Qed.
Lemma lem3280037 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term69 A x s t x') (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3280036 A s x' t x h1 h2) (@lem3279485 A x s t x' h1)). Qed.
Lemma lem3280038 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) : term68 A x s t x'.
Proof. exact (fun h0 : term69 A x s t x' => @lem3280037 A s x' t x h0 h1). Qed.
Lemma lem3280039 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) : (term38 A x s t x') = (term43 A s t x').
Proof. exact (EQ_MP (@lem3279484 A x s t x') (@lem3280038 A s x' t x h1)). Qed.
Lemma lem3280044 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) : term46 A x s t.
Proof. exact (fun x' : A => @lem3280039 A s x' t x h1). Qed.
Lemma lem3280045 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term47 A x s t.
Proof. exact (fun h0 : t x => @lem3280044 A s t x h0). Qed.
Lemma lem3280050 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term59 A s t.
Proof. exact (fun x : A => @lem3280045 A x s t). Qed.
Lemma lem3280055 {A : Type'} (t : A -> Prop) : term63 A t.
Proof. exact (fun s : A -> Prop => @lem3280050 A s t). Qed.
Lemma lem3280060 {A : Type'} : term67 A.
Proof. exact (fun t : A -> Prop => @lem3280055 A t). Qed.
Lemma lem3280061 {A : Type'} : term66 A.
Proof. exact (EQ_MP (@lem3279479 A) (@lem3280060 A)). Qed.
Lemma lem3280062 {A : Type'} (t : A -> Prop) : term99 A t.
Proof. exact (@lem3280061 A t). Qed.
Lemma lem3280063 {A : Type'} (t : A -> Prop) : (term99 A t) = (term62 A t).
Proof. exact (eq_refl (term99 A t)). Qed.
Lemma lem3280064 {A : Type'} (t : A -> Prop) : term62 A t.
Proof. exact (EQ_MP (@lem3280063 A t) (@lem3280062 A t)). Qed.
Lemma lem3280065 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term100 A t s.
Proof. exact (@lem3280064 A t s). Qed.
Lemma lem3280066 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term100 A t s) = (term58 A s t).
Proof. exact (eq_refl (term100 A t s)). Qed.
Lemma lem3280067 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term58 A s t.
Proof. exact (EQ_MP (@lem3280066 A s t) (@lem3280065 A t s)). Qed.
Lemma lem3280068 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term101 A s t x.
Proof. exact (@lem3280067 A s t x). Qed.
Lemma lem3280069 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term101 A s t x) = (term49 A x s t).
Proof. exact (eq_refl (term101 A s t x)). Qed.
Lemma lem3280070 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term49 A x s t.
Proof. exact (EQ_MP (@lem3280069 A x s t) (@lem3280068 A s t x)). Qed.
Lemma lem3280072 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term49 A x s t.
Proof. exact (@lem3279354 A x s t (@lem3280070 A x s t)). Qed.
Lemma lem3280073 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term50 A x s t) : False.
Proof. exact (@lem3280072 A x s t (@lem3279338 A x s t h1)). Qed.
Lemma lem3280074 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term50 A x s t) : (term50 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term50 A x s t => @lem3280073 A x s t h1) (fun h2 : False => @lem3279338 A x s t h1)). Qed.
Lemma lem3280075 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term50 A x s t) : False.
Proof. exact (EQ_MP (@lem3280074 A x s t h1) (@lem3279338 A x s t h1)). Qed.
Lemma lem3280076 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term49 A x s t.
Proof. exact (fun h0 : term50 A x s t => @lem3280075 A x s t h0). Qed.
Lemma lem3280077 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term47 A x s t.
Proof. exact (EQ_MP (@lem3279337 A x s t) (@lem3280076 A x s t)). Qed.
Lemma lem3280078 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term26 A x s t.
Proof. exact (EQ_MP (@lem3279333 A x s t) (@lem3280077 A x s t)). Qed.
Lemma lem3280079 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term16 A x s t.
Proof. exact (EQ_MP (@lem3279250 A x s t) (@lem3280078 A x s t)). Qed.
Lemma lem3280085 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3280086 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (@lem3280085 A s t). Qed.
Lemma lem3280087 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term9 A x s t) = (term7 A x s t)) = (term102 A x s t).
Proof. exact (@lem3280086 A (term9 A x s t) (term7 A x s t)). Qed.
Lemma lem3280096 {A : Type'} (x : A) (t : A -> Prop) : (term10 A x t) = (term10 A x t).
Proof. exact (eq_refl (term10 A x t)). Qed.
Lemma lem3280097 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term12 A x s t) = (term103 A x s t).
Proof. exact (MK_COMB (@lem3280096 A x t) (@lem3280087 A x s t)). Qed.
Lemma lem3280100 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term103 A x s t) = (term12 A x s t).
Proof. exact (SYM (@lem3280097 A x s t)). Qed.
Lemma lem3280104 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3280105 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3280104 A P x). Qed.
Lemma lem3280106 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3280105 A t x). Qed.
Lemma lem3280107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3280108 {A : Type'} (t : A -> Prop) (x : A) : (term23 A x t) = (term72 A t x).
Proof. exact (MK_COMB (@lem3280107) (@lem3280106 A t x)). Qed.
Lemma lem3280109 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3280110 {A : Type'} (t : A -> Prop) (x : A) : (term10 A x t) = (term104 A t x).
Proof. exact (MK_COMB (@lem3280109) (@lem3280108 A t x)). Qed.
Lemma lem3280118 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3280119 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (@lem3280118 A s x t). Qed.
Lemma lem3280120 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term30 A x' x s t) = (term31 A x s x' t).
Proof. exact (@lem3280119 A (@INSERT A x s) x' t). Qed.
Lemma lem3280124 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3280125 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (@lem3280124 A y x s). Qed.
Lemma lem3280126 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term32 A x' x s) = (term33 A x x' s).
Proof. exact (@lem3280125 A x x' s). Qed.
Lemma lem3280132 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3280133 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3280132 A P x). Qed.
Lemma lem3280134 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3280133 A s x'). Qed.
Lemma lem3280135 {A : Type'} (x' : A) (x : A) : (term34 A x' x) = (term34 A x' x).
Proof. exact (eq_refl (term34 A x' x)). Qed.
Lemma lem3280136 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term33 A x x' s) = (term35 A x s x').
Proof. exact (MK_COMB (@lem3280135 A x' x) (@lem3280134 A s x')). Qed.
Lemma lem3280139 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term32 A x' x s) = (term35 A x s x').
Proof. exact (TRANS (@lem3280126 A x x' s) (@lem3280136 A x s x')). Qed.
Lemma lem3280140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3280141 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term36 A x' x s) = (term37 A x s x').
Proof. exact (MK_COMB (@lem3280140) (@lem3280139 A x s x')). Qed.
Lemma lem3280143 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3280144 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3280143 A P x). Qed.
Lemma lem3280145 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3280144 A t x'). Qed.
Lemma lem3280146 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term31 A x s x' t) = (term38 A x s t x').
Proof. exact (MK_COMB (@lem3280141 A x s x') (@lem3280145 A t x')). Qed.
Lemma lem3280149 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term30 A x' x s t) = (term38 A x s t x').
Proof. exact (TRANS (@lem3280120 A x s x' t) (@lem3280146 A x s t x')). Qed.
Lemma lem3280150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3280151 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term39 A x' x s t) = (term40 A x s t x').
Proof. exact (MK_COMB (@lem3280150) (@lem3280149 A x s t x')). Qed.
Lemma lem3280153 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3280154 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (@lem3280153 A y x s). Qed.
Lemma lem3280155 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term105 A x' x s t) = (term106 A x x' s t).
Proof. exact (@lem3280154 A x x' (@UNION A s t)). Qed.
Lemma lem3280161 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3280162 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (@lem3280161 A s x t). Qed.
Lemma lem3280163 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) : (term28 A x' s t) = (term29 A s x' t).
Proof. exact (@lem3280162 A s x' t). Qed.
Lemma lem3280167 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3280168 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3280167 A P x). Qed.
Lemma lem3280169 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3280168 A s x'). Qed.
Lemma lem3280170 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3280171 {A : Type'} (s : A -> Prop) (x' : A) : (term41 A x' s) = (term42 A s x').
Proof. exact (MK_COMB (@lem3280170) (@lem3280169 A s x')). Qed.
Lemma lem3280173 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3280174 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3280173 A P x). Qed.
Lemma lem3280175 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3280174 A t x'). Qed.
Lemma lem3280176 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term29 A s x' t) = (term43 A s t x').
Proof. exact (MK_COMB (@lem3280171 A s x') (@lem3280175 A t x')). Qed.
Lemma lem3280179 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term28 A x' s t) = (term43 A s t x').
Proof. exact (TRANS (@lem3280163 A s x' t) (@lem3280176 A s t x')). Qed.
Lemma lem3280180 {A : Type'} (x' : A) (x : A) : (term34 A x' x) = (term34 A x' x).
Proof. exact (eq_refl (term34 A x' x)). Qed.
Lemma lem3280181 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term106 A x x' s t) = (term107 A x s t x').
Proof. exact (MK_COMB (@lem3280180 A x' x) (@lem3280179 A s t x')). Qed.
Lemma lem3280184 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term105 A x' x s t) = (term107 A x s t x').
Proof. exact (TRANS (@lem3280155 A x x' s t) (@lem3280181 A x s t x')). Qed.
Lemma lem3280185 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term30 A x' x s t) = (term105 A x' x s t)) = ((term38 A x s t x') = (term107 A x s t x')).
Proof. exact (MK_COMB (@lem3280151 A x s t x') (@lem3280184 A x s t x')). Qed.
Lemma lem3280188 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term108 A x s t) = (term109 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3280185 A x s t x')). Qed.
Lemma lem3280189 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3280190 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term102 A x s t) = (term110 A x s t).
Proof. exact (MK_COMB (@lem3280189 A) (@lem3280188 A x s t)). Qed.
Lemma lem3280195 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term103 A x s t) = (term111 A x s t).
Proof. exact (MK_COMB (@lem3280110 A t x) (@lem3280190 A x s t)). Qed.
Lemma lem3280198 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term111 A x s t) = (term103 A x s t).
Proof. exact (SYM (@lem3280195 A x s t)). Qed.
Lemma lem3280200 (p : Prop) : p = (term48 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3280201 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term111 A x s t) = (term112 A x s t).
Proof. exact (@lem3280200 (term111 A x s t)). Qed.
Lemma lem3280202 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term112 A x s t) = (term111 A x s t).
Proof. exact (SYM (@lem3280201 A x s t)). Qed.
Lemma lem3280203 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term113 A x s t) : term113 A x s t.
Proof. exact (h1). Qed.
Lemma lem3280206 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term112 A x s t) : term112 A x s t.
Proof. exact (h1). Qed.
Lemma lem3280207 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term114 A x s t.
Proof. exact (fun h0 : term112 A x s t => @lem3280206 A x s t h0). Qed.
Lemma lem3280208 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term114 A x s t) : term114 A x s t.
Proof. exact (h1). Qed.
Lemma lem3280209 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term112 A x s t) : term112 A x s t.
Proof. exact (h1). Qed.
Lemma lem3280210 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term112 A x s t) (h2 : term114 A x s t) : term112 A x s t.
Proof. exact (@lem3280208 A x s t h2 (@lem3280209 A x s t h1)). Qed.
Lemma lem3280211 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term112 A x s t) : term115 A x s t.
Proof. exact (fun h0 : term114 A x s t => @lem3280210 A x s t h1 h0). Qed.
Lemma lem3280212 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term114 A x s t) : term114 A x s t.
Proof. exact (h1). Qed.
Lemma lem3280213 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term112 A x s t) (h2 : term114 A x s t) : term112 A x s t.
Proof. exact (@lem3280211 A x s t h1 (@lem3280212 A x s t h2)). Qed.
Lemma lem3280214 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term114 A x s t) : term114 A x s t.
Proof. exact (fun h0 : term112 A x s t => @lem3280213 A x s t h0 h1). Qed.
Lemma lem3280215 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term116 A x s t.
Proof. exact (fun h0 : term114 A x s t => @lem3280214 A x s t h0). Qed.
Lemma lem3280218 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term114 A x s t.
Proof. exact (@lem3280215 A x s t (@lem3280207 A x s t)). Qed.
Lemma lem3280219 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term114 A x s t.
Proof. exact (@lem3280218 A x s t). Qed.
Lemma lem3280233 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3280234 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term112 A x s t) = (term117 A x s t).
Proof. exact (@lem3280233 (term113 A x s t)). Qed.
Lemma lem3280236 (t : Prop) : (term55 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3280237 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term117 A x s t) = (term111 A x s t).
Proof. exact (@lem3280236 (term111 A x s t)). Qed.
Lemma lem3280240 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term112 A x s t) = (term111 A x s t).
Proof. exact (TRANS (@lem3280234 A x s t) (@lem3280237 A x s t)). Qed.
Lemma lem3280253 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term118 A s t) = (term119 A s t).
Proof. exact (fun_ext (fun x : A => @lem3280240 A x s t)). Qed.
Lemma lem3280254 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3280255 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term120 A s t) = (term121 A s t).
Proof. exact (MK_COMB (@lem3280254 A) (@lem3280253 A s t)). Qed.
Lemma lem3280260 {A : Type'} (t : A -> Prop) : (term122 A t) = (term123 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3280255 A s t)). Qed.
Lemma lem3280261 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3280262 {A : Type'} (t : A -> Prop) : (term124 A t) = (term125 A t).
Proof. exact (MK_COMB (@lem3280261 A) (@lem3280260 A t)). Qed.
Lemma lem3280267 {A : Type'} : (term126 A) = (term127 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3280262 A t)). Qed.
Lemma lem3280268 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3280277 {A : Type'} : (term128 A) = (term129 A).
Proof. exact (MK_COMB (@lem3280268 A) (@lem3280267 A)). Qed.
Lemma lem3280298 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term38 A x s t x') = (term107 A x s t x')) = ((term38 A x s t x') = (term107 A x s t x')).
Proof. exact (eq_refl ((term38 A x s t x') = (term107 A x s t x'))). Qed.
Lemma lem3280299 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term109 A x s t) = (term109 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3280298 A x s t x')). Qed.
Lemma lem3280300 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3280301 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term110 A x s t) = (term110 A x s t).
Proof. exact (MK_COMB (@lem3280300 A) (@lem3280299 A x s t)). Qed.
Lemma lem3280306 {A : Type'} (t : A -> Prop) (x : A) : (term104 A t x) = (term104 A t x).
Proof. exact (eq_refl (term104 A t x)). Qed.
Lemma lem3280307 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term111 A x s t) = (term111 A x s t).
Proof. exact (MK_COMB (@lem3280306 A t x) (@lem3280301 A x s t)). Qed.
Lemma lem3280308 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term119 A s t) = (term119 A s t).
Proof. exact (fun_ext (fun x : A => @lem3280307 A x s t)). Qed.
Lemma lem3280309 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3280310 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term121 A s t) = (term121 A s t).
Proof. exact (MK_COMB (@lem3280309 A) (@lem3280308 A s t)). Qed.
Lemma lem3280311 {A : Type'} (t : A -> Prop) : (term123 A t) = (term123 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3280310 A s t)). Qed.
Lemma lem3280312 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3280313 {A : Type'} (t : A -> Prop) : (term125 A t) = (term125 A t).
Proof. exact (MK_COMB (@lem3280312 A) (@lem3280311 A t)). Qed.
Lemma lem3280314 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3280313 A t)). Qed.
Lemma lem3280315 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3280316 {A : Type'} : (term129 A) = (term129 A).
Proof. exact (MK_COMB (@lem3280315 A) (@lem3280314 A)). Qed.
Lemma lem3280353 {A : Type'} : (term128 A) = (term129 A).
Proof. exact (TRANS (@lem3280277 A) (@lem3280316 A)). Qed.
Lemma lem3280354 {A : Type'} : (term129 A) = (term128 A).
Proof. exact (SYM (@lem3280353 A)). Qed.
Lemma lem3280357 (p : Prop) : p = (term48 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3280358 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term38 A x s t x') = (term107 A x s t x')) = (term130 A x s t x').
Proof. exact (@lem3280357 ((term38 A x s t x') = (term107 A x s t x'))). Qed.
Lemma lem3280359 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term130 A x s t x') = ((term38 A x s t x') = (term107 A x s t x')).
Proof. exact (SYM (@lem3280358 A x s t x')). Qed.
Lemma lem3280360 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term131 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3280375 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term70 A x s x') = (term71 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3280379 {A : Type'} (t : A -> Prop) (x' : A) : (term72 A t x') = (term72 A t x').
Proof. exact (eq_refl (term72 A t x')). Qed.
Lemma lem3280381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3280382 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term73 A x s x') = (term74 A x s x').
Proof. exact (MK_COMB (@lem3280381) (@lem3280375 A x s x')). Qed.
Lemma lem3280383 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term75 A x s t x') = (term76 A x s t x').
Proof. exact (MK_COMB (@lem3280382 A x s x') (@lem3280379 A t x')). Qed.
Lemma lem3280384 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term77 A x s t x') = (term75 A x s t x').
Proof. exact (@lem17160 (term35 A x s x') (t x')). Qed.
Lemma lem3280385 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term77 A x s t x') = (term76 A x s t x').
Proof. exact (TRANS (@lem3280384 A x s t x') (@lem3280383 A x s t x')). Qed.
Lemma lem3280399 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term78 A s t x') = (term79 A s t x').
Proof. exact (@lem17160 (s x') (t x')). Qed.
Lemma lem3280404 {A : Type'} (x' : A) (x : A) : (term132 A x' x) = (term132 A x' x).
Proof. exact (eq_refl (term132 A x' x)). Qed.
Lemma lem3280405 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term133 A x s t x') = (term134 A x s t x').
Proof. exact (MK_COMB (@lem3280404 A x' x) (@lem3280399 A s t x')). Qed.
Lemma lem3280406 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term135 A x s t x') = (term133 A x s t x').
Proof. exact (@lem17160 (x' = x) (term43 A s t x')). Qed.
Lemma lem3280407 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term135 A x s t x') = (term134 A x s t x').
Proof. exact (TRANS (@lem3280406 A x s t x') (@lem3280405 A x s t x')). Qed.
Lemma lem3280410 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term107 A x s t x') = (term107 A x s t x').
Proof. exact (eq_refl (term107 A x s t x')). Qed.
Lemma lem3280411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3280412 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term80 A x s t x') = (term81 A x s t x').
Proof. exact (MK_COMB (@lem3280411) (@lem3280385 A x s t x')). Qed.
Lemma lem3280413 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term136 A x s t x') = (term137 A x s t x').
Proof. exact (MK_COMB (@lem3280412 A x s t x') (@lem3280410 A x s t x')). Qed.
Lemma lem3280415 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term84 A x s t x') = (term84 A x s t x').
Proof. exact (eq_refl (term84 A x s t x')). Qed.
Lemma lem3280416 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term138 A x s t x') = (term139 A x s t x').
Proof. exact (MK_COMB (@lem3280415 A x s t x') (@lem3280407 A x s t x')). Qed.
Lemma lem3280417 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3280418 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term140 A x s t x') = (term141 A x s t x').
Proof. exact (MK_COMB (@lem3280417) (@lem3280416 A x s t x')). Qed.
Lemma lem3280419 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term142 A x s t x') = (term143 A x s t x').
Proof. exact (MK_COMB (@lem3280418 A x s t x') (@lem3280413 A x s t x')). Qed.
Lemma lem3280420 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term131 A x s t x') = (term142 A x s t x').
Proof. exact (@lem17646 (term38 A x s t x') (term107 A x s t x')). Qed.
Lemma lem3280425 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term131 A x s t x') = (term143 A x s t x').
Proof. exact (TRANS (@lem3280420 A x s t x') (@lem3280419 A x s t x')). Qed.
Lemma lem3280522 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : term143 A x s t x'.
Proof. exact (EQ_MP (@lem3280425 A x s t x') (@lem3280360 A x s t x' h1)). Qed.
Lemma lem3280523 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term139 A x s t x') : term139 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3280524 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term137 A x s t x') : term137 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3280525 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term139 A x s t x') : term134 A x s t x'.
Proof. exact (proj2 (@lem3280523 A x s t x' h1)). Qed.
Lemma lem3280526 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term139 A x s t x') : term38 A x s t x'.
Proof. exact (proj1 (@lem3280523 A x s t x' h1)). Qed.
Lemma lem3280527 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term139 A x s t x') : term79 A s t x'.
Proof. exact (proj2 (@lem3280525 A x s t x' h1)). Qed.
Lemma lem3280531 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term35 A x s x') : term35 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3280535 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term137 A x s t x') : term107 A x s t x'.
Proof. exact (proj2 (@lem3280524 A x s t x' h1)). Qed.
Lemma lem3280536 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term137 A x s t x') : term76 A x s t x'.
Proof. exact (proj1 (@lem3280524 A x s t x' h1)). Qed.
Lemma lem3280538 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term137 A x s t x') : term71 A x s x'.
Proof. exact (proj1 (@lem3280536 A x s t x' h1)). Qed.
Lemma lem3280542 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term43 A s t x') : term43 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3280564 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3280584 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3280604 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3280624 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3280644 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3280664 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3280668 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term139 A x s t x') : term144 A x' x.
Proof. exact (proj1 (@lem3280525 A x s t x' h1)). Qed.
Lemma lem3280674 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3280680 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term139 A x s t x') : term72 A s x'.
Proof. exact (proj1 (@lem3280527 A x s t x' h1)). Qed.
Lemma lem3280684 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3280692 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term139 A x s t x') : term72 A t x'.
Proof. exact (proj2 (@lem3280527 A x s t x' h1)). Qed.
Lemma lem3280694 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3280700 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term137 A x s t x') : term144 A x' x.
Proof. exact (proj1 (@lem3280538 A x s t x' h1)). Qed.
Lemma lem3280704 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3280712 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term137 A x s t x') : term72 A s x'.
Proof. exact (proj2 (@lem3280538 A x s t x' h1)). Qed.
Lemma lem3280714 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3280718 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term137 A x s t x') : term72 A t x'.
Proof. exact (proj2 (@lem3280536 A x s t x' h1)). Qed.
Lemma lem3280724 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3280753 {A : Type'} (x : A) : (term145 A x) = (term145 A x).
Proof. exact (eq_refl (term145 A x)). Qed.
Lemma lem3280754 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term146 A x x') = (term147 A x).
Proof. exact (MK_COMB (@lem3280753 A x) (@lem3280674 A x' x h1)). Qed.
Lemma lem3280755 {A : Type'} (x : A) : (term147 A x) = (term148 A x).
Proof. exact (eq_refl (term147 A x)). Qed.
Lemma lem3280756 {A : Type'} (x : A) (x' : A) : (term149 A x x') = (term149 A x x').
Proof. exact (eq_refl (term149 A x x')). Qed.
Lemma lem3280757 {A : Type'} (x' : A) (x : A) : ((term146 A x x') = (term147 A x)) = ((term146 A x x') = (term148 A x)).
Proof. exact (MK_COMB (@lem3280756 A x x') (@lem3280755 A x)). Qed.
Lemma lem3280758 {A : Type'} (x' : A) (x : A) : (term146 A x x') = (term144 A x' x).
Proof. exact (eq_refl (term146 A x x')). Qed.
Lemma lem3280759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3280760 {A : Type'} (x' : A) (x : A) : (term149 A x x') = (term150 A x' x).
Proof. exact (MK_COMB (@lem3280759) (@lem3280758 A x' x)). Qed.
Lemma lem3280761 {A : Type'} (x : A) : (term148 A x) = (term148 A x).
Proof. exact (eq_refl (term148 A x)). Qed.
Lemma lem3280762 {A : Type'} (x' : A) (x : A) : ((term146 A x x') = (term148 A x)) = ((term144 A x' x) = (term148 A x)).
Proof. exact (MK_COMB (@lem3280760 A x' x) (@lem3280761 A x)). Qed.
Lemma lem3280763 {A : Type'} (x' : A) (x : A) : ((term146 A x x') = (term147 A x)) = ((term144 A x' x) = (term148 A x)).
Proof. exact (TRANS (@lem3280757 A x' x) (@lem3280762 A x' x)). Qed.
Lemma lem3280764 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term144 A x' x) = (term148 A x).
Proof. exact (EQ_MP (@lem3280763 A x' x) (@lem3280754 A x' x h1)). Qed.
Lemma lem3280765 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term139 A x s t x') (h2 : x' = x) : term148 A x.
Proof. exact (EQ_MP (@lem3280764 A x' x h2) (@lem3280668 A x s t x' h1)). Qed.
Lemma lem3280833 {A : Type'} (x : A) : (term145 A x) = (term145 A x).
Proof. exact (eq_refl (term145 A x)). Qed.
Lemma lem3280834 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term146 A x x') = (term147 A x).
Proof. exact (MK_COMB (@lem3280833 A x) (@lem3280704 A x' x h1)). Qed.
Lemma lem3280835 {A : Type'} (x : A) : (term147 A x) = (term148 A x).
Proof. exact (eq_refl (term147 A x)). Qed.
Lemma lem3280836 {A : Type'} (x : A) (x' : A) : (term149 A x x') = (term149 A x x').
Proof. exact (eq_refl (term149 A x x')). Qed.
Lemma lem3280837 {A : Type'} (x' : A) (x : A) : ((term146 A x x') = (term147 A x)) = ((term146 A x x') = (term148 A x)).
Proof. exact (MK_COMB (@lem3280836 A x x') (@lem3280835 A x)). Qed.
Lemma lem3280838 {A : Type'} (x' : A) (x : A) : (term146 A x x') = (term144 A x' x).
Proof. exact (eq_refl (term146 A x x')). Qed.
Lemma lem3280839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3280840 {A : Type'} (x' : A) (x : A) : (term149 A x x') = (term150 A x' x).
Proof. exact (MK_COMB (@lem3280839) (@lem3280838 A x' x)). Qed.
Lemma lem3280841 {A : Type'} (x : A) : (term148 A x) = (term148 A x).
Proof. exact (eq_refl (term148 A x)). Qed.
Lemma lem3280842 {A : Type'} (x' : A) (x : A) : ((term146 A x x') = (term148 A x)) = ((term144 A x' x) = (term148 A x)).
Proof. exact (MK_COMB (@lem3280840 A x' x) (@lem3280841 A x)). Qed.
Lemma lem3280843 {A : Type'} (x' : A) (x : A) : ((term146 A x x') = (term147 A x)) = ((term144 A x' x) = (term148 A x)).
Proof. exact (TRANS (@lem3280837 A x' x) (@lem3280842 A x' x)). Qed.
Lemma lem3280844 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term144 A x' x) = (term148 A x).
Proof. exact (EQ_MP (@lem3280843 A x' x) (@lem3280834 A x' x h1)). Qed.
Lemma lem3280845 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term137 A x s t x') (h2 : x' = x) : term148 A x.
Proof. exact (EQ_MP (@lem3280844 A x' x h2) (@lem3280700 A x s t x' h1)). Qed.
Lemma lem3280886 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3280887 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3280886 A x). Qed.
Lemma lem3280888 {A : Type'} (x : A) : term151 A x.
Proof. exact (fun h0 : term148 A x => @lem3280887 A x). Qed.
Lemma lem3280890 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3280891 {A : Type'} (x : A) : (term151 A x) = (x = x).
Proof. exact (@lem3280890 (x = x)). Qed.
Lemma lem3280892 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3280891 A x) (@lem3280888 A x)). Qed.
Lemma lem3280895 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3280897 {A : Type'} (x : A) : (term148 A x) = (term152 A x).
Proof. exact (@lem3280895 (x = x)). Qed.
Lemma lem3280900 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term139 A x s t x') (h2 : x' = x) : term152 A x.
Proof. exact (EQ_MP (@lem3280897 A x) (@lem3280765 A s t x' x h1 h2)). Qed.
Lemma lem3280903 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term139 A x s t x') (h2 : x' = x) : False.
Proof. exact (@lem3280900 A s t x' x h1 h2 (@lem3280892 A x)). Qed.
Lemma lem3280904 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term139 A x s t x') (h2 : x' = x) : term98.
Proof. exact (fun h0 : ~ False => @lem3280903 A s t x' x h1 h2). Qed.
Lemma lem3280906 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3280907 : term98 = False.
Proof. exact (@lem3280906 False). Qed.
Lemma lem3280936 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3280937 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term95 A s x'.
Proof. exact (fun h0 : term72 A s x' => @lem3280936 A s x' h1). Qed.
Lemma lem3280939 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3280940 {A : Type'} (s : A -> Prop) (x' : A) : (term95 A s x') = (s x').
Proof. exact (@lem3280939 (s x')). Qed.
Lemma lem3280941 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3280940 A s x') (@lem3280937 A s x' h1)). Qed.
Lemma lem3280944 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3280946 {A : Type'} (s : A -> Prop) (x' : A) : (term72 A s x') = (term97 A s x').
Proof. exact (@lem3280944 (s x')). Qed.
Lemma lem3280949 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term139 A x s t x') : term97 A s x'.
Proof. exact (EQ_MP (@lem3280946 A s x') (@lem3280680 A x s t x' h1)). Qed.
Lemma lem3280952 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term139 A x s t x') : False.
Proof. exact (@lem3280949 A x s t x' h2 (@lem3280941 A s x' h1)). Qed.
Lemma lem3280953 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term139 A x s t x') : term98.
Proof. exact (fun h0 : ~ False => @lem3280952 A x s t x' h1 h2). Qed.
Lemma lem3280955 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3280956 : term98 = False.
Proof. exact (@lem3280955 False). Qed.
Lemma lem3280957 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term139 A x s t x') : False.
Proof. exact (EQ_MP (@lem3280956) (@lem3280953 A x s t x' h1 h2)). Qed.
Lemma lem3280985 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3280986 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term95 A t x'.
Proof. exact (fun h0 : term72 A t x' => @lem3280985 A t x' h1). Qed.
Lemma lem3280988 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3280989 {A : Type'} (t : A -> Prop) (x' : A) : (term95 A t x') = (t x').
Proof. exact (@lem3280988 (t x')). Qed.
Lemma lem3280990 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3280989 A t x') (@lem3280986 A t x' h1)). Qed.
Lemma lem3280993 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3280995 {A : Type'} (t : A -> Prop) (x' : A) : (term72 A t x') = (term97 A t x').
Proof. exact (@lem3280993 (t x')). Qed.
Lemma lem3280998 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term139 A x s t x') : term97 A t x'.
Proof. exact (EQ_MP (@lem3280995 A t x') (@lem3280692 A x s t x' h1)). Qed.
Lemma lem3281001 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term139 A x s t x') : False.
Proof. exact (@lem3280998 A x s t x' h2 (@lem3280990 A t x' h1)). Qed.
Lemma lem3281002 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term139 A x s t x') : term98.
Proof. exact (fun h0 : ~ False => @lem3281001 A x s t x' h1 h2). Qed.
Lemma lem3281004 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3281005 : term98 = False.
Proof. exact (@lem3281004 False). Qed.
Lemma lem3281006 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term139 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281005) (@lem3281002 A x s t x' h1 h2)). Qed.
Lemma lem3281034 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3281035 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3281034 A x). Qed.
Lemma lem3281036 {A : Type'} (x : A) : term151 A x.
Proof. exact (fun h0 : term148 A x => @lem3281035 A x). Qed.
Lemma lem3281038 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3281039 {A : Type'} (x : A) : (term151 A x) = (x = x).
Proof. exact (@lem3281038 (x = x)). Qed.
Lemma lem3281040 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3281039 A x) (@lem3281036 A x)). Qed.
Lemma lem3281043 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3281045 {A : Type'} (x : A) : (term148 A x) = (term152 A x).
Proof. exact (@lem3281043 (x = x)). Qed.
Lemma lem3281048 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term137 A x s t x') (h2 : x' = x) : term152 A x.
Proof. exact (EQ_MP (@lem3281045 A x) (@lem3280845 A s t x' x h1 h2)). Qed.
Lemma lem3281051 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term137 A x s t x') (h2 : x' = x) : False.
Proof. exact (@lem3281048 A s t x' x h1 h2 (@lem3281040 A x)). Qed.
Lemma lem3281052 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term137 A x s t x') (h2 : x' = x) : term98.
Proof. exact (fun h0 : ~ False => @lem3281051 A s t x' x h1 h2). Qed.
Lemma lem3281054 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3281055 : term98 = False.
Proof. exact (@lem3281054 False). Qed.
Lemma lem3281084 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3281085 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term95 A s x'.
Proof. exact (fun h0 : term72 A s x' => @lem3281084 A s x' h1). Qed.
Lemma lem3281087 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3281088 {A : Type'} (s : A -> Prop) (x' : A) : (term95 A s x') = (s x').
Proof. exact (@lem3281087 (s x')). Qed.
Lemma lem3281089 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3281088 A s x') (@lem3281085 A s x' h1)). Qed.
Lemma lem3281092 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3281094 {A : Type'} (s : A -> Prop) (x' : A) : (term72 A s x') = (term97 A s x').
Proof. exact (@lem3281092 (s x')). Qed.
Lemma lem3281097 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term137 A x s t x') : term97 A s x'.
Proof. exact (EQ_MP (@lem3281094 A s x') (@lem3280712 A x s t x' h1)). Qed.
Lemma lem3281100 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term137 A x s t x') : False.
Proof. exact (@lem3281097 A x s t x' h2 (@lem3281089 A s x' h1)). Qed.
Lemma lem3281101 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term137 A x s t x') : term98.
Proof. exact (fun h0 : ~ False => @lem3281100 A x s t x' h1 h2). Qed.
Lemma lem3281103 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3281104 : term98 = False.
Proof. exact (@lem3281103 False). Qed.
Lemma lem3281105 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term137 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281104) (@lem3281101 A x s t x' h1 h2)). Qed.
Lemma lem3281133 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3281134 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term95 A t x'.
Proof. exact (fun h0 : term72 A t x' => @lem3281133 A t x' h1). Qed.
Lemma lem3281136 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3281137 {A : Type'} (t : A -> Prop) (x' : A) : (term95 A t x') = (t x').
Proof. exact (@lem3281136 (t x')). Qed.
Lemma lem3281138 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3281137 A t x') (@lem3281134 A t x' h1)). Qed.
Lemma lem3281141 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3281143 {A : Type'} (t : A -> Prop) (x' : A) : (term72 A t x') = (term97 A t x').
Proof. exact (@lem3281141 (t x')). Qed.
Lemma lem3281146 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term137 A x s t x') : term97 A t x'.
Proof. exact (EQ_MP (@lem3281143 A t x') (@lem3280718 A x s t x' h1)). Qed.
Lemma lem3281149 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term137 A x s t x') : False.
Proof. exact (@lem3281146 A x s t x' h2 (@lem3281138 A t x' h1)). Qed.
Lemma lem3281150 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term137 A x s t x') : term98.
Proof. exact (fun h0 : ~ False => @lem3281149 A x s t x' h1 h2). Qed.
Lemma lem3281152 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3281153 : term98 = False.
Proof. exact (@lem3281152 False). Qed.
Lemma lem3281154 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term137 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281153) (@lem3281150 A x s t x' h1 h2)). Qed.
Lemma lem3281155 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term137 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3281055) (@lem3281052 A s t x' x h1 h2)). Qed.
Lemma lem3281156 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term139 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3280907) (@lem3280904 A s t x' x h1 h2)). Qed.
Lemma lem3281157 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term137 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3281154 A x s t x' h1 h2) (fun h3 : False => @lem3280724 A t x' h1)). Qed.
Lemma lem3281158 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term137 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281157 A x s t x' h1 h2) (@lem3280724 A t x' h1)). Qed.
Lemma lem3281159 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term137 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3281105 A x s t x' h1 h2) (fun h3 : False => @lem3280714 A s x' h1)). Qed.
Lemma lem3281160 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term137 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281159 A x s t x' h1 h2) (@lem3280714 A s x' h1)). Qed.
Lemma lem3281161 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term137 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3281155 A s t x' x h1 h2) (fun h3 : False => @lem3280704 A x' x h2)). Qed.
Lemma lem3281162 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term137 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3281161 A s t x' x h1 h2) (@lem3280704 A x' x h2)). Qed.
Lemma lem3281163 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term139 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3281006 A x s t x' h1 h2) (fun h3 : False => @lem3280694 A t x' h1)). Qed.
Lemma lem3281164 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term139 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281163 A x s t x' h1 h2) (@lem3280694 A t x' h1)). Qed.
Lemma lem3281165 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term139 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3280957 A x s t x' h1 h2) (fun h3 : False => @lem3280684 A s x' h1)). Qed.
Lemma lem3281166 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term139 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281165 A x s t x' h1 h2) (@lem3280684 A s x' h1)). Qed.
Lemma lem3281167 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term139 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3281156 A s t x' x h1 h2) (fun h3 : False => @lem3280674 A x' x h2)). Qed.
Lemma lem3281168 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term139 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3281167 A s t x' x h1 h2) (@lem3280674 A x' x h2)). Qed.
Lemma lem3281169 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term137 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3281158 A x s t x' h1 h2) (fun h3 : False => @lem3280664 A t x' h1)). Qed.
Lemma lem3281170 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term137 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281169 A x s t x' h1 h2) (@lem3280664 A t x' h1)). Qed.
Lemma lem3281171 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term137 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3281160 A x s t x' h1 h2) (fun h3 : False => @lem3280644 A s x' h1)). Qed.
Lemma lem3281172 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term137 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281171 A x s t x' h1 h2) (@lem3280644 A s x' h1)). Qed.
Lemma lem3281173 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term137 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3281162 A s t x' x h1 h2) (fun h3 : False => @lem3280624 A x' x h2)). Qed.
Lemma lem3281174 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term137 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3281173 A s t x' x h1 h2) (@lem3280624 A x' x h2)). Qed.
Lemma lem3281175 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term139 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3281164 A x s t x' h1 h2) (fun h3 : False => @lem3280604 A t x' h1)). Qed.
Lemma lem3281176 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term139 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281175 A x s t x' h1 h2) (@lem3280604 A t x' h1)). Qed.
Lemma lem3281177 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term139 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3281166 A x s t x' h1 h2) (fun h3 : False => @lem3280584 A s x' h1)). Qed.
Lemma lem3281178 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term139 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281177 A x s t x' h1 h2) (@lem3280584 A s x' h1)). Qed.
Lemma lem3281179 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term139 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3281168 A s t x' x h1 h2) (fun h3 : False => @lem3280564 A x' x h2)). Qed.
Lemma lem3281180 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term139 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3281179 A s t x' x h1 h2) (@lem3280564 A x' x h2)). Qed.
Lemma lem3281181 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term137 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3281170 A x s t x' h1 h2) (fun h3 : False => @lem3280664 A t x' h1)). Qed.
Lemma lem3281182 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term137 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281181 A x s t x' h1 h2) (@lem3280664 A t x' h1)). Qed.
Lemma lem3281183 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term137 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3281172 A x s t x' h1 h2) (fun h3 : False => @lem3280644 A s x' h1)). Qed.
Lemma lem3281184 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term137 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281183 A x s t x' h1 h2) (@lem3280644 A s x' h1)). Qed.
Lemma lem3281185 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term137 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3281174 A s t x' x h1 h2) (fun h3 : False => @lem3280624 A x' x h2)). Qed.
Lemma lem3281186 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term137 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3281185 A s t x' x h1 h2) (@lem3280624 A x' x h2)). Qed.
Lemma lem3281187 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term139 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3281176 A x s t x' h1 h2) (fun h3 : False => @lem3280604 A t x' h1)). Qed.
Lemma lem3281188 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term139 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281187 A x s t x' h1 h2) (@lem3280604 A t x' h1)). Qed.
Lemma lem3281189 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term139 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3281178 A x s t x' h1 h2) (fun h3 : False => @lem3280584 A s x' h1)). Qed.
Lemma lem3281190 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term139 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281189 A x s t x' h1 h2) (@lem3280584 A s x' h1)). Qed.
Lemma lem3281191 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term139 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3281180 A s t x' x h1 h2) (fun h3 : False => @lem3280564 A x' x h2)). Qed.
Lemma lem3281192 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term139 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3281191 A s t x' x h1 h2) (@lem3280564 A x' x h2)). Qed.
Lemma lem3281193 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term137 A x s t x') (h2 : term43 A s t x') : False.
Proof. exact (or_elim (@lem3280542 A s t x' h2) (fun h0 : s x' => @lem3281184 A x s t x' h0 h1) (fun h0 : t x' => @lem3281182 A x s t x' h0 h1)). Qed.
Lemma lem3281194 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term137 A x s t x') : False.
Proof. exact (or_elim (@lem3280535 A x s t x' h1) (fun h0 : x' = x => @lem3281186 A s t x' x h1 h0) (fun h0 : term43 A s t x' => @lem3281193 A x s t x' h1 h0)). Qed.
Lemma lem3281195 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term139 A x s t x') (h2 : term35 A x s x') : False.
Proof. exact (or_elim (@lem3280531 A x s x' h2) (fun h0 : x' = x => @lem3281192 A s t x' x h1 h0) (fun h0 : s x' => @lem3281190 A x s t x' h0 h1)). Qed.
Lemma lem3281196 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term139 A x s t x') : False.
Proof. exact (or_elim (@lem3280526 A x s t x' h1) (fun h0 : term35 A x s x' => @lem3281195 A t x s x' h1 h0) (fun h0 : t x' => @lem3281188 A x s t x' h0 h1)). Qed.
Lemma lem3281197 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : False.
Proof. exact (or_elim (@lem3280522 A x s t x' h1) (fun h0 : term139 A x s t x' => @lem3281196 A x s t x' h0) (fun h0 : term137 A x s t x' => @lem3281194 A x s t x' h0)). Qed.
Lemma lem3281198 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : (term131 A x s t x') = False.
Proof. exact (prop_ext (fun h2 : term131 A x s t x' => @lem3281197 A x s t x' h1) (fun h2 : False => @lem3280360 A x s t x' h1)). Qed.
Lemma lem3281199 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term131 A x s t x') : False.
Proof. exact (EQ_MP (@lem3281198 A x s t x' h1) (@lem3280360 A x s t x' h1)). Qed.
Lemma lem3281200 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : term130 A x s t x'.
Proof. exact (fun h0 : term131 A x s t x' => @lem3281199 A x s t x' h0). Qed.
Lemma lem3281201 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term38 A x s t x') = (term107 A x s t x').
Proof. exact (EQ_MP (@lem3280359 A x s t x') (@lem3281200 A x s t x')). Qed.
Lemma lem3281206 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term110 A x s t.
Proof. exact (fun x' : A => @lem3281201 A x s t x'). Qed.
Lemma lem3281207 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term111 A x s t.
Proof. exact (fun h0 : term72 A t x => @lem3281206 A x s t). Qed.
Lemma lem3281212 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term121 A s t.
Proof. exact (fun x : A => @lem3281207 A x s t). Qed.
Lemma lem3281217 {A : Type'} (t : A -> Prop) : term125 A t.
Proof. exact (fun s : A -> Prop => @lem3281212 A s t). Qed.
Lemma lem3281222 {A : Type'} : term129 A.
Proof. exact (fun t : A -> Prop => @lem3281217 A t). Qed.
Lemma lem3281223 {A : Type'} : term128 A.
Proof. exact (EQ_MP (@lem3280354 A) (@lem3281222 A)). Qed.
Lemma lem3281224 {A : Type'} (t : A -> Prop) : term153 A t.
Proof. exact (@lem3281223 A t). Qed.
Lemma lem3281225 {A : Type'} (t : A -> Prop) : (term153 A t) = (term124 A t).
Proof. exact (eq_refl (term153 A t)). Qed.
Lemma lem3281226 {A : Type'} (t : A -> Prop) : term124 A t.
Proof. exact (EQ_MP (@lem3281225 A t) (@lem3281224 A t)). Qed.
Lemma lem3281227 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term154 A t s.
Proof. exact (@lem3281226 A t s). Qed.
Lemma lem3281228 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term154 A t s) = (term120 A s t).
Proof. exact (eq_refl (term154 A t s)). Qed.
Lemma lem3281229 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term120 A s t.
Proof. exact (EQ_MP (@lem3281228 A s t) (@lem3281227 A t s)). Qed.
Lemma lem3281230 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term155 A s t x.
Proof. exact (@lem3281229 A s t x). Qed.
Lemma lem3281231 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term155 A s t x) = (term112 A x s t).
Proof. exact (eq_refl (term155 A s t x)). Qed.
Lemma lem3281232 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term112 A x s t.
Proof. exact (EQ_MP (@lem3281231 A x s t) (@lem3281230 A s t x)). Qed.
Lemma lem3281234 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term112 A x s t.
Proof. exact (@lem3280219 A x s t (@lem3281232 A x s t)). Qed.
Lemma lem3281235 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term113 A x s t) : False.
Proof. exact (@lem3281234 A x s t (@lem3280203 A x s t h1)). Qed.
Lemma lem3281236 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term113 A x s t) : (term113 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term113 A x s t => @lem3281235 A x s t h1) (fun h2 : False => @lem3280203 A x s t h1)). Qed.
Lemma lem3281237 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term113 A x s t) : False.
Proof. exact (EQ_MP (@lem3281236 A x s t h1) (@lem3280203 A x s t h1)). Qed.
Lemma lem3281238 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term112 A x s t.
Proof. exact (fun h0 : term113 A x s t => @lem3281237 A x s t h0). Qed.
Lemma lem3281239 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term111 A x s t.
Proof. exact (EQ_MP (@lem3280202 A x s t) (@lem3281238 A x s t)). Qed.
Lemma lem3281240 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term103 A x s t.
Proof. exact (EQ_MP (@lem3280198 A x s t) (@lem3281239 A x s t)). Qed.
Lemma lem3281241 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term12 A x s t.
Proof. exact (EQ_MP (@lem3280100 A x s t) (@lem3281240 A x s t)). Qed.
Lemma lem3281244 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term23 A x t) : (term9 A x s t) = (term7 A x s t).
Proof. exact (@lem3281241 A x s t (@lem3279213 A x t h1)). Qed.
Lemma lem3281245 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term23 A x t) : (term23 A x t) = ((term9 A x s t) = (term7 A x s t)).
Proof. exact (prop_ext (fun h2 : term23 A x t => @lem3281244 A s x t h1) (fun h2 : (term9 A x s t) = (term7 A x s t) => @lem3279213 A x t h1)). Qed.
Lemma lem3281246 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term23 A x t) : (term9 A x s t) = (term7 A x s t).
Proof. exact (EQ_MP (@lem3281245 A s x t h1) (@lem3279213 A x t h1)). Qed.
Lemma lem3281247 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term12 A x s t.
Proof. exact (fun h0 : term23 A x t => @lem3281246 A s x t h0). Qed.
Lemma lem3281248 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : @IN A x t) : (term9 A x s t) = (@UNION A s t).
Proof. exact (@lem3280079 A x s t (@lem3279196 A x t h1)). Qed.
Lemma lem3281249 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : @IN A x t) : (@IN A x t) = ((term9 A x s t) = (@UNION A s t)).
Proof. exact (prop_ext (fun h2 : @IN A x t => @lem3281248 A s x t h1) (fun h2 : (term9 A x s t) = (@UNION A s t) => @lem3279196 A x t h1)). Qed.
Lemma lem3281250 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : @IN A x t) : (term9 A x s t) = (@UNION A s t).
Proof. exact (EQ_MP (@lem3281249 A s x t h1) (@lem3279196 A x t h1)). Qed.
Lemma lem3281251 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term16 A x s t.
Proof. exact (fun h0 : @IN A x t => @lem3281250 A s x t h0). Qed.
Lemma lem3281252 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term19 A x s t.
Proof. exact (conj (@lem3281251 A x s t) (@lem3281247 A x s t)). Qed.
Lemma lem3281253 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term9 A x s t) = (term20 A x s t).
Proof. exact (EQ_MP (@lem3279195 A x s t) (@lem3281252 A x s t)). Qed.
Lemma lem3281258 {A : Type'} (x : A) (s : A -> Prop) : term156 A x s.
Proof. exact (fun t : A -> Prop => @lem3281253 A x s t). Qed.
Lemma lem3281263 {A : Type'} (x : A) : term157 A x.
Proof. exact (fun s : A -> Prop => @lem3281258 A x s). Qed.
Lemma lem3281268 {A : Type'} : term158 A.
Proof. exact (fun x : A => @lem3281263 A x). Qed.
