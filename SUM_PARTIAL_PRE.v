Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_PARTIAL_PRE_term_abbrevs.
Require Import ADD_SUB_spec.
Require Import SUM_PARTIAL_SUC_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1823_spec.
Lemma lem7233250 (m : nat) : term0 m.
Proof. exact (@lem135886 m). Qed.
Lemma lem7233251 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7233252 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7233251 m) (@lem7233250 m)). Qed.
Lemma lem7233253 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7233252 m n). Qed.
Lemma lem7233254 (n : nat) (m : nat) : (term2 m n) = ((term3 m n) = m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7233256 (f : nat -> real) : term4 f.
Proof. exact (@lem7233249 f). Qed.
Lemma lem7233257 (f : nat -> real) : (term4 f) = (term5 f).
Proof. exact (eq_refl (term4 f)). Qed.
Lemma lem7233258 (f : nat -> real) : term5 f.
Proof. exact (EQ_MP (@lem7233257 f) (@lem7233256 f)). Qed.
Lemma lem7233259 (f : nat -> real) (g : nat -> real) : term6 f g.
Proof. exact (@lem7233258 f (term7 g)). Qed.
Lemma lem7233260 (g : nat -> real) (f : nat -> real) : (term6 f g) = (term8 g f).
Proof. exact (eq_refl (term6 f g)). Qed.
Lemma lem7233261 (g : nat -> real) (f : nat -> real) : term8 g f.
Proof. exact (EQ_MP (@lem7233260 g f) (@lem7233259 f g)). Qed.
Lemma lem7233262 (g : nat -> real) (f : nat -> real) (m : nat) : term9 g f m.
Proof. exact (@lem7233261 g f m). Qed.
Lemma lem7233263 (m : nat) (g : nat -> real) (f : nat -> real) : (term9 g f m) = (term10 m g f).
Proof. exact (eq_refl (term9 g f m)). Qed.
Lemma lem7233264 (m : nat) (g : nat -> real) (f : nat -> real) : term10 m g f.
Proof. exact (EQ_MP (@lem7233263 m g f) (@lem7233262 g f m)). Qed.
Lemma lem7233265 (m : nat) (g : nat -> real) (f : nat -> real) (n : nat) : term11 m g f n.
Proof. exact (@lem7233264 m g f n). Qed.
Lemma lem7233266 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term11 m g f n) = ((term12 m n f g) = (term13 m n g f)).
Proof. exact (eq_refl (term11 m g f n)). Qed.
Lemma lem7233267 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term12 m n f g) = (term13 m n g f).
Proof. exact (EQ_MP (@lem7233266 m n g f) (@lem7233265 m g f n)). Qed.
Lemma lem7233275 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7233276 (f : nat -> real) (y : nat) : (term15 f y) = (f y).
Proof. exact (@lem7233275 nat real f y). Qed.
Lemma lem7233277 (g : nat -> real) (k : nat) : (term16 g k) = (term17 g k).
Proof. exact (@lem7233276 (term7 g) (term18 k)). Qed.
Lemma lem7233278 (g : nat -> real) (k : nat) : (term19 g k) = (term20 g k).
Proof. exact (eq_refl (term19 g k)). Qed.
Lemma lem7233279 (g : nat -> real) : (term21 g) = (term7 g).
Proof. exact (fun_ext (fun k : nat => @lem7233278 g k)). Qed.
Lemma lem7233280 (k : nat) : (term18 k) = (term18 k).
Proof. exact (eq_refl (term18 k)). Qed.
Lemma lem7233281 (g : nat -> real) (k : nat) : (term16 g k) = (term17 g k).
Proof. exact (MK_COMB (@lem7233279 g) (@lem7233280 k)). Qed.
Lemma lem7233282 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7233283 (g : nat -> real) (k : nat) : (term22 g k) = (term23 g k).
Proof. exact (MK_COMB (@lem7233282) (@lem7233281 g k)). Qed.
Lemma lem7233284 (g : nat -> real) (k : nat) : (term17 g k) = (term24 g k).
Proof. exact (eq_refl (term17 g k)). Qed.
Lemma lem7233285 (g : nat -> real) (k : nat) : ((term16 g k) = (term17 g k)) = ((term17 g k) = (term24 g k)).
Proof. exact (MK_COMB (@lem7233283 g k) (@lem7233284 g k)). Qed.
Lemma lem7233286 (g : nat -> real) (k : nat) : (term17 g k) = (term24 g k).
Proof. exact (EQ_MP (@lem7233285 g k) (@lem7233277 g k)). Qed.
Lemma lem7233288 (n : nat) (m : nat) : (term3 m n) = m.
Proof. exact (EQ_MP (@lem7233254 n m) (@lem7233253 m n)). Qed.
Lemma lem7233289 (k : nat) : (term25 k) = k.
Proof. exact (@lem7233288 term26 k). Qed.
Lemma lem7233290 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7233291 (g : nat -> real) (k : nat) : (term24 g k) = (g k).
Proof. exact (MK_COMB (@lem7233290 g) (@lem7233289 k)). Qed.
Lemma lem7233292 (g : nat -> real) (k : nat) : (term17 g k) = (g k).
Proof. exact (TRANS (@lem7233286 g k) (@lem7233291 g k)). Qed.
Lemma lem7233293 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7233294 (g : nat -> real) (k : nat) : (term27 g k) = (term28 g k).
Proof. exact (MK_COMB (@lem7233293) (@lem7233292 g k)). Qed.
Lemma lem7233296 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7233297 (f : nat -> real) (y : nat) : (term15 f y) = (f y).
Proof. exact (@lem7233296 nat real f y). Qed.
Lemma lem7233298 (g : nat -> real) (k : nat) : (term29 g k) = (term19 g k).
Proof. exact (@lem7233297 (term7 g) k). Qed.
Lemma lem7233299 (g : nat -> real) (k : nat) : (term19 g k) = (term20 g k).
Proof. exact (eq_refl (term19 g k)). Qed.
Lemma lem7233300 (g : nat -> real) : (term21 g) = (term7 g).
Proof. exact (fun_ext (fun k : nat => @lem7233299 g k)). Qed.
Lemma lem7233301 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem7233302 (g : nat -> real) (k : nat) : (term29 g k) = (term19 g k).
Proof. exact (MK_COMB (@lem7233300 g) (@lem7233301 k)). Qed.
Lemma lem7233303 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7233304 (g : nat -> real) (k : nat) : (term30 g k) = (term31 g k).
Proof. exact (MK_COMB (@lem7233303) (@lem7233302 g k)). Qed.
Lemma lem7233305 (g : nat -> real) (k : nat) : (term19 g k) = (term20 g k).
Proof. exact (eq_refl (term19 g k)). Qed.
Lemma lem7233306 (g : nat -> real) (k : nat) : ((term29 g k) = (term19 g k)) = ((term19 g k) = (term20 g k)).
Proof. exact (MK_COMB (@lem7233304 g k) (@lem7233305 g k)). Qed.
Lemma lem7233307 (g : nat -> real) (k : nat) : (term19 g k) = (term20 g k).
Proof. exact (EQ_MP (@lem7233306 g k) (@lem7233298 g k)). Qed.
Lemma lem7233308 (g : nat -> real) (k : nat) : (term32 g k) = (term33 g k).
Proof. exact (MK_COMB (@lem7233294 g k) (@lem7233307 g k)). Qed.
Lemma lem7233309 (f : nat -> real) (k : nat) : (term34 f k) = (term34 f k).
Proof. exact (eq_refl (term34 f k)). Qed.
Lemma lem7233310 (f : nat -> real) (g : nat -> real) (k : nat) : (term35 f g k) = (term36 f g k).
Proof. exact (MK_COMB (@lem7233309 f k) (@lem7233308 g k)). Qed.
Lemma lem7233311 (f : nat -> real) (g : nat -> real) : (term37 f g) = (term38 f g).
Proof. exact (fun_ext (fun k : nat => @lem7233310 f g k)). Qed.
Lemma lem7233312 (m : nat) (n : nat) : (term39 m n) = (term39 m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem7233313 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term12 m n f g) = (term40 m n f g).
Proof. exact (MK_COMB (@lem7233312 m n) (@lem7233311 f g)). Qed.
Lemma lem7233314 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7233315 (m : nat) (n : nat) (f : nat -> real) (g : nat -> real) : (term41 m n f g) = (term42 m n f g).
Proof. exact (MK_COMB (@lem7233314) (@lem7233313 m n f g)). Qed.
Lemma lem7233317 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7233318 (f : nat -> real) (y : nat) : (term15 f y) = (f y).
Proof. exact (@lem7233317 nat real f y). Qed.
Lemma lem7233319 (g : nat -> real) (n : nat) : (term16 g n) = (term17 g n).
Proof. exact (@lem7233318 (term7 g) (term18 n)). Qed.
Lemma lem7233320 (g : nat -> real) (k : nat) : (term19 g k) = (term20 g k).
Proof. exact (eq_refl (term19 g k)). Qed.
Lemma lem7233321 (g : nat -> real) : (term21 g) = (term7 g).
Proof. exact (fun_ext (fun k : nat => @lem7233320 g k)). Qed.
Lemma lem7233322 (n : nat) : (term18 n) = (term18 n).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem7233323 (g : nat -> real) (n : nat) : (term16 g n) = (term17 g n).
Proof. exact (MK_COMB (@lem7233321 g) (@lem7233322 n)). Qed.
Lemma lem7233324 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7233325 (g : nat -> real) (n : nat) : (term22 g n) = (term23 g n).
Proof. exact (MK_COMB (@lem7233324) (@lem7233323 g n)). Qed.
Lemma lem7233326 (g : nat -> real) (n : nat) : (term17 g n) = (term24 g n).
Proof. exact (eq_refl (term17 g n)). Qed.
Lemma lem7233327 (g : nat -> real) (n : nat) : ((term16 g n) = (term17 g n)) = ((term17 g n) = (term24 g n)).
Proof. exact (MK_COMB (@lem7233325 g n) (@lem7233326 g n)). Qed.
Lemma lem7233328 (g : nat -> real) (n : nat) : (term17 g n) = (term24 g n).
Proof. exact (EQ_MP (@lem7233327 g n) (@lem7233319 g n)). Qed.
Lemma lem7233330 (n : nat) (m : nat) : (term3 m n) = m.
Proof. exact (EQ_MP (@lem7233254 n m) (@lem7233253 m n)). Qed.
Lemma lem7233331 (n : nat) : (term25 n) = n.
Proof. exact (@lem7233330 term26 n). Qed.
Lemma lem7233332 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7233333 (g : nat -> real) (n : nat) : (term24 g n) = (g n).
Proof. exact (MK_COMB (@lem7233332 g) (@lem7233331 n)). Qed.
Lemma lem7233334 (g : nat -> real) (n : nat) : (term17 g n) = (g n).
Proof. exact (TRANS (@lem7233328 g n) (@lem7233333 g n)). Qed.
Lemma lem7233335 (f : nat -> real) (n : nat) : (term43 f n) = (term43 f n).
Proof. exact (eq_refl (term43 f n)). Qed.
Lemma lem7233336 (f : nat -> real) (g : nat -> real) (n : nat) : (term44 f g n) = (term45 f g n).
Proof. exact (MK_COMB (@lem7233335 f n) (@lem7233334 g n)). Qed.
Lemma lem7233337 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7233338 (f : nat -> real) (g : nat -> real) (n : nat) : (term46 f g n) = (term47 f g n).
Proof. exact (MK_COMB (@lem7233337) (@lem7233336 f g n)). Qed.
Lemma lem7233340 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7233341 (f : nat -> real) (y : nat) : (term15 f y) = (f y).
Proof. exact (@lem7233340 nat real f y). Qed.
Lemma lem7233342 (g : nat -> real) (m : nat) : (term29 g m) = (term19 g m).
Proof. exact (@lem7233341 (term7 g) m). Qed.
Lemma lem7233343 (g : nat -> real) (k : nat) : (term19 g k) = (term20 g k).
Proof. exact (eq_refl (term19 g k)). Qed.
Lemma lem7233344 (g : nat -> real) : (term21 g) = (term7 g).
Proof. exact (fun_ext (fun k : nat => @lem7233343 g k)). Qed.
Lemma lem7233345 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7233346 (g : nat -> real) (m : nat) : (term29 g m) = (term19 g m).
Proof. exact (MK_COMB (@lem7233344 g) (@lem7233345 m)). Qed.
Lemma lem7233347 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7233348 (g : nat -> real) (m : nat) : (term30 g m) = (term31 g m).
Proof. exact (MK_COMB (@lem7233347) (@lem7233346 g m)). Qed.
Lemma lem7233349 (g : nat -> real) (m : nat) : (term19 g m) = (term20 g m).
Proof. exact (eq_refl (term19 g m)). Qed.
Lemma lem7233350 (g : nat -> real) (m : nat) : ((term29 g m) = (term19 g m)) = ((term19 g m) = (term20 g m)).
Proof. exact (MK_COMB (@lem7233348 g m) (@lem7233349 g m)). Qed.
Lemma lem7233351 (g : nat -> real) (m : nat) : (term19 g m) = (term20 g m).
Proof. exact (EQ_MP (@lem7233350 g m) (@lem7233342 g m)). Qed.
Lemma lem7233352 (f : nat -> real) (m : nat) : (term34 f m) = (term34 f m).
Proof. exact (eq_refl (term34 f m)). Qed.
Lemma lem7233353 (f : nat -> real) (g : nat -> real) (m : nat) : (term48 f g m) = (term49 f g m).
Proof. exact (MK_COMB (@lem7233352 f m) (@lem7233351 g m)). Qed.
Lemma lem7233354 (n : nat) (f : nat -> real) (g : nat -> real) (m : nat) : (term50 n f g m) = (term51 n f g m).
Proof. exact (MK_COMB (@lem7233338 f g n) (@lem7233353 f g m)). Qed.
Lemma lem7233355 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7233356 (n : nat) (f : nat -> real) (g : nat -> real) (m : nat) : (term52 n f g m) = (term53 n f g m).
Proof. exact (MK_COMB (@lem7233355) (@lem7233354 n f g m)). Qed.
Lemma lem7233358 {A B : Type'} (f : A -> B) (y : A) : (term14 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7233359 (f : nat -> real) (y : nat) : (term15 f y) = (f y).
Proof. exact (@lem7233358 nat real f y). Qed.
Lemma lem7233360 (g : nat -> real) (k : nat) : (term16 g k) = (term17 g k).
Proof. exact (@lem7233359 (term7 g) (term18 k)). Qed.
Lemma lem7233361 (g : nat -> real) (k : nat) : (term19 g k) = (term20 g k).
Proof. exact (eq_refl (term19 g k)). Qed.
Lemma lem7233362 (g : nat -> real) : (term21 g) = (term7 g).
Proof. exact (fun_ext (fun k : nat => @lem7233361 g k)). Qed.
Lemma lem7233363 (k : nat) : (term18 k) = (term18 k).
Proof. exact (eq_refl (term18 k)). Qed.
Lemma lem7233364 (g : nat -> real) (k : nat) : (term16 g k) = (term17 g k).
Proof. exact (MK_COMB (@lem7233362 g) (@lem7233363 k)). Qed.
Lemma lem7233365 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7233366 (g : nat -> real) (k : nat) : (term22 g k) = (term23 g k).
Proof. exact (MK_COMB (@lem7233365) (@lem7233364 g k)). Qed.
Lemma lem7233367 (g : nat -> real) (k : nat) : (term17 g k) = (term24 g k).
Proof. exact (eq_refl (term17 g k)). Qed.
Lemma lem7233368 (g : nat -> real) (k : nat) : ((term16 g k) = (term17 g k)) = ((term17 g k) = (term24 g k)).
Proof. exact (MK_COMB (@lem7233366 g k) (@lem7233367 g k)). Qed.
Lemma lem7233369 (g : nat -> real) (k : nat) : (term17 g k) = (term24 g k).
Proof. exact (EQ_MP (@lem7233368 g k) (@lem7233360 g k)). Qed.
Lemma lem7233371 (n : nat) (m : nat) : (term3 m n) = m.
Proof. exact (EQ_MP (@lem7233254 n m) (@lem7233253 m n)). Qed.
Lemma lem7233372 (k : nat) : (term25 k) = k.
Proof. exact (@lem7233371 term26 k). Qed.
Lemma lem7233373 (g : nat -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7233374 (g : nat -> real) (k : nat) : (term24 g k) = (g k).
Proof. exact (MK_COMB (@lem7233373 g) (@lem7233372 k)). Qed.
Lemma lem7233375 (g : nat -> real) (k : nat) : (term17 g k) = (g k).
Proof. exact (TRANS (@lem7233369 g k) (@lem7233374 g k)). Qed.
Lemma lem7233376 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7233377 (g : nat -> real) (k : nat) : (term54 g k) = (term34 g k).
Proof. exact (MK_COMB (@lem7233376) (@lem7233375 g k)). Qed.
Lemma lem7233378 (f : nat -> real) (k : nat) : (term55 f k) = (term55 f k).
Proof. exact (eq_refl (term55 f k)). Qed.
Lemma lem7233379 (g : nat -> real) (f : nat -> real) (k : nat) : (term56 g f k) = (term57 g f k).
Proof. exact (MK_COMB (@lem7233377 g k) (@lem7233378 f k)). Qed.
Lemma lem7233380 (g : nat -> real) (f : nat -> real) : (term58 g f) = (term59 g f).
Proof. exact (fun_ext (fun k : nat => @lem7233379 g f k)). Qed.
Lemma lem7233381 (m : nat) (n : nat) : (term39 m n) = (term39 m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem7233382 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term60 m n g f) = (term61 m n g f).
Proof. exact (MK_COMB (@lem7233381 m n) (@lem7233380 g f)). Qed.
Lemma lem7233383 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term62 m n g f) = (term63 m n g f).
Proof. exact (MK_COMB (@lem7233356 n f g m) (@lem7233382 m n g f)). Qed.
Lemma lem7233384 (m : nat) (n : nat) : (term64 m n) = (term64 m n).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem7233385 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term65 m n g f) = (term66 m n g f).
Proof. exact (MK_COMB (@lem7233384 m n) (@lem7233383 m n g f)). Qed.
Lemma lem7233386 : term67 = term67.
Proof. exact (eq_refl term67). Qed.
Lemma lem7233387 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term13 m n g f) = (term68 m n g f).
Proof. exact (MK_COMB (@lem7233385 m n g f) (@lem7233386)). Qed.
Lemma lem7233388 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : ((term12 m n f g) = (term13 m n g f)) = ((term40 m n f g) = (term68 m n g f)).
Proof. exact (MK_COMB (@lem7233315 m n f g) (@lem7233387 m n g f)). Qed.
Lemma lem7233391 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7233392 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term69 m n g f) = (term70 m n g f).
Proof. exact (MK_COMB (@lem7233391) (@lem7233388 m n g f)). Qed.
Lemma lem7233395 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : ((term40 m n f g) = (term68 m n g f)) = ((term40 m n f g) = (term68 m n g f)).
Proof. exact (eq_refl ((term40 m n f g) = (term68 m n g f))). Qed.
Lemma lem7233396 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term71 m n g f) = (term72 m n g f).
Proof. exact (MK_COMB (@lem7233392 m n g f) (@lem7233395 m n g f)). Qed.
Lemma lem7233400 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7233401 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term72 m n g f) = True.
Proof. exact (@lem7233400 ((term40 m n f g) = (term68 m n g f))). Qed.
Lemma lem7233402 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term71 m n g f) = True.
Proof. exact (TRANS (@lem7233396 m n g f) (@lem7233401 m n g f)). Qed.
Lemma lem7233403 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : True = (term71 m n g f).
Proof. exact (SYM (@lem7233402 m n g f)). Qed.
Lemma lem7233404 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : term71 m n g f.
Proof. exact (EQ_MP (@lem7233403 m n g f) (@lem0)). Qed.
Lemma lem7233405 (m : nat) (n : nat) (g : nat -> real) (f : nat -> real) : (term40 m n f g) = (term68 m n g f).
Proof. exact (@lem7233404 m n g f (@lem7233267 m n g f)). Qed.
Lemma lem7233410 (m : nat) (g : nat -> real) (f : nat -> real) : term73 m g f.
Proof. exact (fun n : nat => @lem7233405 m n g f). Qed.
Lemma lem7233415 (g : nat -> real) (f : nat -> real) : term74 g f.
Proof. exact (fun m : nat => @lem7233410 m g f). Qed.
Lemma lem7233420 (f : nat -> real) : term75 f.
Proof. exact (fun g : nat -> real => @lem7233415 g f). Qed.
Lemma lem7233425 : term76.
Proof. exact (fun f : nat -> real => @lem7233420 f). Qed.
