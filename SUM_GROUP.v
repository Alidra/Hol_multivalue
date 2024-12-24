Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_GROUP_term_abbrevs.
Require Import SUM_EQ_0_spec.
Require Import SUM_IMAGE_GEN_spec.
Require Import SUM_SUPERSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm7_spec.
Lemma lem7159248 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7159249 {A : Type'} (f : A -> real) (h1 : term0 A) : term1 A f.
Proof. exact (@lem7159248 A h1 f). Qed.
Lemma lem7159250 {A : Type'} (f : A -> real) : (term1 A f) = (term2 A f).
Proof. exact (eq_refl (term1 A f)). Qed.
Lemma lem7159251 {A : Type'} (f : A -> real) (h1 : term0 A) : term2 A f.
Proof. exact (EQ_MP (@lem7159250 A f) (@lem7159249 A f h1)). Qed.
Lemma lem7159252 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term0 A) : term3 A f s.
Proof. exact (@lem7159251 A f h1 s). Qed.
Lemma lem7159253 {A : Type'} (s : A -> Prop) (f : A -> real) : (term3 A f s) = (term4 A s f).
Proof. exact (eq_refl (term3 A f s)). Qed.
Lemma lem7159254 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term0 A) : term4 A s f.
Proof. exact (EQ_MP (@lem7159253 A s f) (@lem7159252 A f s h1)). Qed.
Lemma lem7159255 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term5 A s f) : term5 A s f.
Proof. exact (h1). Qed.
Lemma lem7159256 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term5 A s f) (h2 : term0 A) : (@sum A s f) = term6.
Proof. exact (@lem7159254 A s f h2 (@lem7159255 A s f h1)). Qed.
Lemma lem7159257 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term5 A s f) : term7 A s f.
Proof. exact (fun h0 : term0 A => @lem7159256 A s f h1 h0). Qed.
Lemma lem7159258 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7159259 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term5 A s f) (h2 : term0 A) : (@sum A s f) = term6.
Proof. exact (@lem7159257 A s f h1 (@lem7159258 A h2)). Qed.
Lemma lem7159260 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term0 A) : term4 A s f.
Proof. exact (fun h0 : term5 A s f => @lem7159259 A s f h0 h1). Qed.
Lemma lem7159261 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term8 A s.
Proof. exact (fun f : A -> real => @lem7159260 A s f h1). Qed.
Lemma lem7159262 {A : Type'} (h1 : term0 A) : term9 A.
Proof. exact (fun s : A -> Prop => @lem7159261 A s h1). Qed.
Lemma lem7159263 {A : Type'} : term10 A.
Proof. exact (fun h0 : term0 A => @lem7159262 A h0). Qed.
Lemma lem7159264 {A : Type'} : term9 A.
Proof. exact (@lem7159263 A (@lem7069292 A)). Qed.
Lemma lem7159265 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (@lem7159264 A s). Qed.
Lemma lem7159266 {A : Type'} (s : A -> Prop) : (term11 A s) = (term8 A s).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem7159267 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem7159266 A s) (@lem7159265 A s)). Qed.
Lemma lem7159268 {A : Type'} (s : A -> Prop) (f : A -> real) : term12 A s f.
Proof. exact (@lem7159267 A s f). Qed.
Lemma lem7159269 {A : Type'} (s : A -> Prop) (f : A -> real) : (term12 A s f) = (term4 A s f).
Proof. exact (eq_refl (term12 A s f)). Qed.
Lemma lem7159271 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem7159272 {A : Type'} (f : A -> real) (h1 : term13 A) : term14 A f.
Proof. exact (@lem7159271 A h1 f). Qed.
Lemma lem7159273 {A : Type'} (f : A -> real) : (term14 A f) = (term15 A f).
Proof. exact (eq_refl (term14 A f)). Qed.
Lemma lem7159274 {A : Type'} (f : A -> real) (h1 : term13 A) : term15 A f.
Proof. exact (EQ_MP (@lem7159273 A f) (@lem7159272 A f h1)). Qed.
Lemma lem7159275 {A : Type'} (f : A -> real) (u : A -> Prop) (h1 : term13 A) : term16 A f u.
Proof. exact (@lem7159274 A f h1 u). Qed.
Lemma lem7159276 {A : Type'} (u : A -> Prop) (f : A -> real) : (term16 A f u) = (term17 A u f).
Proof. exact (eq_refl (term16 A f u)). Qed.
Lemma lem7159277 {A : Type'} (u : A -> Prop) (f : A -> real) (h1 : term13 A) : term17 A u f.
Proof. exact (EQ_MP (@lem7159276 A u f) (@lem7159275 A f u h1)). Qed.
Lemma lem7159278 {A : Type'} (u : A -> Prop) (f : A -> real) (v : A -> Prop) (h1 : term13 A) : term18 A u f v.
Proof. exact (@lem7159277 A u f h1 v). Qed.
Lemma lem7159279 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term18 A u f v) = (term19 A v u f).
Proof. exact (eq_refl (term18 A u f v)). Qed.
Lemma lem7159280 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term13 A) : term19 A v u f.
Proof. exact (EQ_MP (@lem7159279 A v u f) (@lem7159278 A u f v h1)). Qed.
Lemma lem7159281 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term20 A v u f.
Proof. exact (h1). Qed.
Lemma lem7159282 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term13 A) (h2 : term20 A v u f) : (@sum A v f) = (@sum A u f).
Proof. exact (@lem7159280 A v u f h1 (@lem7159281 A v u f h2)). Qed.
Lemma lem7159283 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term20 A v u f) : term21 A v u f.
Proof. exact (fun h0 : term13 A => @lem7159282 A v u f h0 h1). Qed.
Lemma lem7159284 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem7159285 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term13 A) (h2 : term20 A v u f) : (@sum A v f) = (@sum A u f).
Proof. exact (@lem7159283 A v u f h2 (@lem7159284 A h1)). Qed.
Lemma lem7159286 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (h1 : term13 A) : term19 A v u f.
Proof. exact (fun h0 : term20 A v u f => @lem7159285 A v u f h1 h0). Qed.
Lemma lem7159287 {A : Type'} (v : A -> Prop) (u : A -> Prop) (h1 : term13 A) : term22 A v u.
Proof. exact (fun f : A -> real => @lem7159286 A v u f h1). Qed.
Lemma lem7159288 {A : Type'} (v : A -> Prop) (h1 : term13 A) : term23 A v.
Proof. exact (fun u : A -> Prop => @lem7159287 A v u h1). Qed.
Lemma lem7159289 {A : Type'} (h1 : term13 A) : term24 A.
Proof. exact (fun v : A -> Prop => @lem7159288 A v h1). Qed.
Lemma lem7159290 {A : Type'} : term25 A.
Proof. exact (fun h0 : term13 A => @lem7159289 A h0). Qed.
Lemma lem7159291 {A : Type'} : term24 A.
Proof. exact (@lem7159290 A (@lem7124972 A)). Qed.
Lemma lem7159292 {A : Type'} (v : A -> Prop) : term26 A v.
Proof. exact (@lem7159291 A v). Qed.
Lemma lem7159293 {A : Type'} (v : A -> Prop) : (term26 A v) = (term23 A v).
Proof. exact (eq_refl (term26 A v)). Qed.
Lemma lem7159294 {A : Type'} (v : A -> Prop) : term23 A v.
Proof. exact (EQ_MP (@lem7159293 A v) (@lem7159292 A v)). Qed.
Lemma lem7159295 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term27 A v u.
Proof. exact (@lem7159294 A v u). Qed.
Lemma lem7159296 {A : Type'} (v : A -> Prop) (u : A -> Prop) : (term27 A v u) = (term22 A v u).
Proof. exact (eq_refl (term27 A v u)). Qed.
Lemma lem7159297 {A : Type'} (v : A -> Prop) (u : A -> Prop) : term22 A v u.
Proof. exact (EQ_MP (@lem7159296 A v u) (@lem7159295 A v u)). Qed.
Lemma lem7159298 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term28 A v u f.
Proof. exact (@lem7159297 A v u f). Qed.
Lemma lem7159299 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term28 A v u f) = (term19 A v u f).
Proof. exact (eq_refl (term28 A v u f)). Qed.
Lemma lem7159301 {A B : Type'} : term29 A B.
Proof. exact (@lem7159247 A B). Qed.
Lemma lem7159302 {A B : Type'} (f : A -> B) : term30 A B f.
Proof. exact (@lem7159301 A B f). Qed.
Lemma lem7159303 {A B : Type'} (f : A -> B) : (term30 A B f) = (term31 A B f).
Proof. exact (eq_refl (term30 A B f)). Qed.
Lemma lem7159304 {A B : Type'} (f : A -> B) : term31 A B f.
Proof. exact (EQ_MP (@lem7159303 A B f) (@lem7159302 A B f)). Qed.
Lemma lem7159305 {A B : Type'} (f : A -> B) (g : A -> real) : term32 A B f g.
Proof. exact (@lem7159304 A B f g). Qed.
Lemma lem7159306 {A B : Type'} (f : A -> B) (g : A -> real) : (term32 A B f g) = (term33 A B f g).
Proof. exact (eq_refl (term32 A B f g)). Qed.
Lemma lem7159307 {A B : Type'} (f : A -> B) (g : A -> real) : term33 A B f g.
Proof. exact (EQ_MP (@lem7159306 A B f g) (@lem7159305 A B f g)). Qed.
Lemma lem7159308 {A B : Type'} (f : A -> B) (g : A -> real) (s : A -> Prop) : term34 A B f g s.
Proof. exact (@lem7159307 A B f g s). Qed.
Lemma lem7159309 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) : (term34 A B f g s) = (term35 A B s f g).
Proof. exact (eq_refl (term34 A B f g s)). Qed.
Lemma lem7159310 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) : term35 A B s f g.
Proof. exact (EQ_MP (@lem7159309 A B s f g) (@lem7159308 A B f g s)). Qed.
Lemma lem7159311 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term36 A B f s t) : term36 A B f s t.
Proof. exact (h1). Qed.
Lemma lem7159312 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B f s t) : term37 A B f s t.
Proof. exact (h1). Qed.
Lemma lem7159313 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7159314 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7159323 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7159314 A s) (@lem7159313 A s h1)). Qed.
Lemma lem7159324 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7159325 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term38 A s) = (imp True).
Proof. exact (MK_COMB (@lem7159324) (@lem7159323 A s h1)). Qed.
Lemma lem7159336 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) : ((@sum A s g) = (term39 A B s f g)) = ((@sum A s g) = (term39 A B s f g)).
Proof. exact (eq_refl ((@sum A s g) = (term39 A B s f g))). Qed.
Lemma lem7159337 {A B : Type'} (f : A -> B) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term35 A B s f g) = (term40 A B s f g).
Proof. exact (MK_COMB (@lem7159325 A s h1) (@lem7159336 A B s f g)). Qed.
Lemma lem7159339 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7159340 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) : (term40 A B s f g) = ((@sum A s g) = (term39 A B s f g)).
Proof. exact (@lem7159339 ((@sum A s g) = (term39 A B s f g))). Qed.
Lemma lem7159351 {A B : Type'} (f : A -> B) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term35 A B s f g) = ((@sum A s g) = (term39 A B s f g)).
Proof. exact (TRANS (@lem7159337 A B f g s h1) (@lem7159340 A B s f g)). Qed.
Lemma lem7159352 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7159353 {A B : Type'} (f : A -> B) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term41 A B s f g) = (term42 A B s f g).
Proof. exact (MK_COMB (@lem7159352) (@lem7159351 A B f g s h1)). Qed.
Lemma lem7159364 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (g : A -> real) : ((term43 A B t s f g) = (@sum A s g)) = ((term43 A B t s f g) = (@sum A s g)).
Proof. exact (eq_refl ((term43 A B t s f g) = (@sum A s g))). Qed.
Lemma lem7159365 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term44 A B t f s g) = (term45 A B t f s g).
Proof. exact (MK_COMB (@lem7159353 A B f g s h1) (@lem7159364 A B t f s g)). Qed.
Lemma lem7159370 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : (term45 A B t f s g) = (term44 A B t f s g).
Proof. exact (SYM (@lem7159365 A B t f g s h1)). Qed.
Lemma lem7159371 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) (h1 : (@sum A s g) = (term39 A B s f g)) : (@sum A s g) = (term39 A B s f g).
Proof. exact (h1). Qed.
Lemma lem7159372 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : (term46 A B t s f g) = (term46 A B t s f g).
Proof. exact (eq_refl (term46 A B t s f g)). Qed.
Lemma lem7159373 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) (h1 : (@sum A s g) = (term39 A B s f g)) : (term47 A B t f s g) = (term48 A B t s f g).
Proof. exact (MK_COMB (@lem7159372 A B t s f g) (@lem7159371 A B s f g h1)). Qed.
Lemma lem7159374 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : (term48 A B t s f g) = ((term43 A B t s f g) = (term39 A B s f g)).
Proof. exact (eq_refl (term48 A B t s f g)). Qed.
Lemma lem7159375 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (g : A -> real) : (term49 A B t f s g) = (term49 A B t f s g).
Proof. exact (eq_refl (term49 A B t f s g)). Qed.
Lemma lem7159376 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : ((term47 A B t f s g) = (term48 A B t s f g)) = ((term47 A B t f s g) = ((term43 A B t s f g) = (term39 A B s f g))).
Proof. exact (MK_COMB (@lem7159375 A B t f s g) (@lem7159374 A B t s f g)). Qed.
Lemma lem7159377 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (g : A -> real) : (term47 A B t f s g) = ((term43 A B t s f g) = (@sum A s g)).
Proof. exact (eq_refl (term47 A B t f s g)). Qed.
Lemma lem7159378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7159379 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (g : A -> real) : (term49 A B t f s g) = (term50 A B t f s g).
Proof. exact (MK_COMB (@lem7159378) (@lem7159377 A B t f s g)). Qed.
Lemma lem7159380 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : ((term43 A B t s f g) = (term39 A B s f g)) = ((term43 A B t s f g) = (term39 A B s f g)).
Proof. exact (eq_refl ((term43 A B t s f g) = (term39 A B s f g))). Qed.
Lemma lem7159381 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : ((term47 A B t f s g) = ((term43 A B t s f g) = (term39 A B s f g))) = (((term43 A B t s f g) = (@sum A s g)) = ((term43 A B t s f g) = (term39 A B s f g))).
Proof. exact (MK_COMB (@lem7159379 A B t f s g) (@lem7159380 A B t s f g)). Qed.
Lemma lem7159382 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : ((term47 A B t f s g) = (term48 A B t s f g)) = (((term43 A B t s f g) = (@sum A s g)) = ((term43 A B t s f g) = (term39 A B s f g))).
Proof. exact (TRANS (@lem7159376 A B t s f g) (@lem7159381 A B t s f g)). Qed.
Lemma lem7159383 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) (h1 : (@sum A s g) = (term39 A B s f g)) : ((term43 A B t s f g) = (@sum A s g)) = ((term43 A B t s f g) = (term39 A B s f g)).
Proof. exact (EQ_MP (@lem7159382 A B t s f g) (@lem7159373 A B t s f g h1)). Qed.
Lemma lem7159384 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) (h1 : (@sum A s g) = (term39 A B s f g)) : ((term43 A B t s f g) = (term39 A B s f g)) = ((term43 A B t s f g) = (@sum A s g)).
Proof. exact (SYM (@lem7159383 A B t s f g h1)). Qed.
Lemma lem7159386 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : term19 A v u f.
Proof. exact (EQ_MP (@lem7159299 A v u f) (@lem7159298 A v u f)). Qed.
Lemma lem7159387 {B : Type'} (v : B -> Prop) (u : B -> Prop) (f : B -> real) : term19 B v u f.
Proof. exact (@lem7159386 B v u f). Qed.
Lemma lem7159388 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : term51 A B t s f g.
Proof. exact (@lem7159387 B t (@IMAGE A B f s) (term52 A B s f g)). Qed.
Lemma lem7159391 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : (term53 A B t s f g) = (term53 A B t s f g).
Proof. exact (eq_refl (term53 A B t s f g)). Qed.
Lemma lem7159392 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : (term53 A B t s f g) = (term51 A B t s f g).
Proof. exact (eq_refl (term53 A B t s f g)). Qed.
Lemma lem7159393 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : (term54 A B t s f g) = (term54 A B t s f g).
Proof. exact (eq_refl (term54 A B t s f g)). Qed.
Lemma lem7159394 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : ((term53 A B t s f g) = (term53 A B t s f g)) = ((term53 A B t s f g) = (term51 A B t s f g)).
Proof. exact (MK_COMB (@lem7159393 A B t s f g) (@lem7159392 A B t s f g)). Qed.
Lemma lem7159395 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : (term53 A B t s f g) = (term51 A B t s f g).
Proof. exact (eq_refl (term53 A B t s f g)). Qed.
Lemma lem7159396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7159397 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : (term54 A B t s f g) = (term55 A B t s f g).
Proof. exact (MK_COMB (@lem7159396) (@lem7159395 A B t s f g)). Qed.
Lemma lem7159398 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : (term51 A B t s f g) = (term51 A B t s f g).
Proof. exact (eq_refl (term51 A B t s f g)). Qed.
Lemma lem7159399 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : ((term53 A B t s f g) = (term51 A B t s f g)) = ((term51 A B t s f g) = (term51 A B t s f g)).
Proof. exact (MK_COMB (@lem7159397 A B t s f g) (@lem7159398 A B t s f g)). Qed.
Lemma lem7159400 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : ((term53 A B t s f g) = (term53 A B t s f g)) = ((term51 A B t s f g) = (term51 A B t s f g)).
Proof. exact (TRANS (@lem7159394 A B t s f g) (@lem7159399 A B t s f g)). Qed.
Lemma lem7159401 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : (term51 A B t s f g) = (term51 A B t s f g).
Proof. exact (EQ_MP (@lem7159400 A B t s f g) (@lem7159391 A B t s f g)). Qed.
Lemma lem7159402 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : term51 A B t s f g.
Proof. exact (EQ_MP (@lem7159401 A B t s f g) (@lem7159388 A B t s f g)). Qed.
Lemma lem7159405 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term37 A B f s t) = ((term37 A B f s t) = True).
Proof. exact (@lem7 (term37 A B f s t)). Qed.
Lemma lem7159410 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B f s t) : (term37 A B f s t) = True.
Proof. exact (EQ_MP (@lem7159405 A B f s t) (@lem7159312 A B f s t h1)). Qed.
Lemma lem7159411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7159412 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B f s t) : (term56 A B f s t) = (and True).
Proof. exact (MK_COMB (@lem7159411) (@lem7159410 A B f s t h1)). Qed.
Lemma lem7159424 {A B : Type'} (f : A -> B) (y : A) : (term57 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7159425 {B : Type'} (f : B -> real) (y : B) : (term58 B f y) = (f y).
Proof. exact (@lem7159424 B real f y). Qed.
Lemma lem7159426 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) (x : B) : (term59 A B s f g x) = (term60 A B s f g x).
Proof. exact (@lem7159425 B (term52 A B s f g) x). Qed.
Lemma lem7159427 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (g : A -> real) : (term60 A B s f g y) = (term61 A B s f y g).
Proof. exact (eq_refl (term60 A B s f g y)). Qed.
Lemma lem7159428 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) : (term62 A B s f g) = (term52 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem7159427 A B s f y g)). Qed.
Lemma lem7159429 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7159430 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) (x : B) : (term59 A B s f g x) = (term60 A B s f g x).
Proof. exact (MK_COMB (@lem7159428 A B s f g) (@lem7159429 B x)). Qed.
Lemma lem7159431 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7159432 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> real) (x : B) : (term63 A B s f g x) = (term64 A B s f g x).
Proof. exact (MK_COMB (@lem7159431) (@lem7159430 A B s f g x)). Qed.
Lemma lem7159433 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term60 A B s f g x) = (term61 A B s f x g).
Proof. exact (eq_refl (term60 A B s f g x)). Qed.
Lemma lem7159434 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : ((term59 A B s f g x) = (term60 A B s f g x)) = ((term60 A B s f g x) = (term61 A B s f x g)).
Proof. exact (MK_COMB (@lem7159432 A B s f g x) (@lem7159433 A B s f x g)). Qed.
Lemma lem7159435 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term60 A B s f g x) = (term61 A B s f x g).
Proof. exact (EQ_MP (@lem7159434 A B s f x g) (@lem7159426 A B s f g x)). Qed.
Lemma lem7159444 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7159445 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term64 A B s f g x) = (term65 A B s f x g).
Proof. exact (MK_COMB (@lem7159444) (@lem7159435 A B s f x g)). Qed.
Lemma lem7159446 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem7159447 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : ((term60 A B s f g x) = term6) = ((term61 A B s f x g) = term6).
Proof. exact (MK_COMB (@lem7159445 A B s f x g) (@lem7159446)). Qed.
Lemma lem7159450 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) : (term66 A B t x f s) = (term66 A B t x f s).
Proof. exact (eq_refl (term66 A B t x f s)). Qed.
Lemma lem7159451 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term67 A B t s f g x) = (term68 A B t s f x g).
Proof. exact (MK_COMB (@lem7159450 A B t x f s) (@lem7159447 A B s f x g)). Qed.
Lemma lem7159454 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : (term69 A B t s f g) = (term70 A B t s f g).
Proof. exact (fun_ext (fun x : B => @lem7159451 A B t s f x g)). Qed.
Lemma lem7159455 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7159456 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : (term71 A B t s f g) = (term72 A B t s f g).
Proof. exact (MK_COMB (@lem7159455 B) (@lem7159454 A B t s f g)). Qed.
Lemma lem7159461 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B f s t) : (term73 A B t s f g) = (term74 A B t s f g).
Proof. exact (MK_COMB (@lem7159412 A B f s t h1) (@lem7159456 A B t s f g)). Qed.
Lemma lem7159463 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7159464 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> real) : (term74 A B t s f g) = (term72 A B t s f g).
Proof. exact (@lem7159463 (term72 A B t s f g)). Qed.
Lemma lem7159483 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B f s t) : (term73 A B t s f g) = (term72 A B t s f g).
Proof. exact (TRANS (@lem7159461 A B g f s t h1) (@lem7159464 A B t s f g)). Qed.
Lemma lem7159484 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term37 A B f s t) : (term72 A B t s f g) = (term73 A B t s f g).
Proof. exact (SYM (@lem7159483 A B g f s t h1)). Qed.
Lemma lem7159485 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term75 A B t x f s) : term75 A B t x f s.
Proof. exact (h1). Qed.
Lemma lem7159486 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (h1 : term76 A B x f s) : term76 A B x f s.
Proof. exact (h1). Qed.
Lemma lem7159487 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : @IN B x t.
Proof. exact (h1). Qed.
Lemma lem7159489 {A : Type'} (s : A -> Prop) (f : A -> real) : term4 A s f.
Proof. exact (EQ_MP (@lem7159269 A s f) (@lem7159268 A s f)). Qed.
Lemma lem7159490 {A : Type'} (s : A -> Prop) (f : A -> real) : term4 A s f.
Proof. exact (@lem7159489 A s f). Qed.
Lemma lem7159491 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term77 A B s f x g.
Proof. exact (@lem7159490 A (term78 A B s f x) g). Qed.
Lemma lem7159502 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term37 A B f s t) : term79 A B f t s.
Proof. exact (conj (@lem7159312 A B f s t h2) (@lem7159313 A s h1)). Qed.
Lemma lem7159503 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @IN B x t) (h3 : term37 A B f s t) : term80 A B x f t s.
Proof. exact (conj (@lem7159487 B x t h2) (@lem7159502 A B f s t h1 h3)). Qed.
Lemma lem7159504 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term76 A B x f s) (h3 : @IN B x t) (h4 : term37 A B f s t) : term81 A B x f t s.
Proof. exact (conj (@lem7159486 A B x f s h2) (@lem7159503 A B x f s t h1 h3 h4)). Qed.
Lemma lem7159514 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term82 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem7159515 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term82 B s t).
Proof. exact (@lem7159514 B s t). Qed.
Lemma lem7159516 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term37 A B f s t) = (term83 A B f s t).
Proof. exact (@lem7159515 B (@IMAGE A B f s) t). Qed.
Lemma lem7159523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7159524 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term56 A B f s t) = (term84 A B f s t).
Proof. exact (MK_COMB (@lem7159523) (@lem7159516 A B f s t)). Qed.
Lemma lem7159525 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7159526 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term79 A B f t s) = (term85 A B f t s).
Proof. exact (MK_COMB (@lem7159524 A B f s t) (@lem7159525 A s)). Qed.
Lemma lem7159529 {B : Type'} (x : B) (t : B -> Prop) : (term86 B x t) = (term86 B x t).
Proof. exact (eq_refl (term86 B x t)). Qed.
Lemma lem7159530 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term80 A B x f t s) = (term87 A B x f t s).
Proof. exact (MK_COMB (@lem7159529 B x t) (@lem7159526 A B f t s)). Qed.
Lemma lem7159533 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term88 A B x f s) = (term88 A B x f s).
Proof. exact (eq_refl (term88 A B x f s)). Qed.
Lemma lem7159534 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term81 A B x f t s) = (term89 A B x f t s).
Proof. exact (MK_COMB (@lem7159533 A B x f s) (@lem7159530 A B x f t s)). Qed.
Lemma lem7159537 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7159538 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term90 A B x f t s) = (term91 A B x f t s).
Proof. exact (MK_COMB (@lem7159537) (@lem7159534 A B x f t s)). Qed.
Lemma lem7159559 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term92 A B s f x g) = (term92 A B s f x g).
Proof. exact (eq_refl (term92 A B s f x g)). Qed.
Lemma lem7159560 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term93 A B t s f x g) = (term94 A B t s f x g).
Proof. exact (MK_COMB (@lem7159538 A B x f t s) (@lem7159559 A B s f x g)). Qed.
Lemma lem7159563 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term94 A B t s f x g) = (term93 A B t s f x g).
Proof. exact (SYM (@lem7159560 A B t s f x g)). Qed.
Lemma lem7159569 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term95 A B y f s) = (term96 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem7159570 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term95 A B y f s) = (term96 A B y f s).
Proof. exact (@lem7159569 A B y f s). Qed.
Lemma lem7159571 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term95 A B x f s) = (term96 A B x f s).
Proof. exact (@lem7159570 A B x f s). Qed.
Lemma lem7159581 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7159582 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7159581 A P x). Qed.
Lemma lem7159583 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem7159582 A s x). Qed.
Lemma lem7159584 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term97 A B x f x') = (term97 A B x f x').
Proof. exact (eq_refl (term97 A B x f x')). Qed.
Lemma lem7159585 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term98 A B x f x' s) = (term99 A B x f s x').
Proof. exact (MK_COMB (@lem7159584 A B x f x') (@lem7159583 A s x')). Qed.
Lemma lem7159588 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term100 A B x f s) = (term101 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem7159585 A B x f s x')). Qed.
Lemma lem7159589 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7159590 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term96 A B x f s) = (term102 A B x f s).
Proof. exact (MK_COMB (@lem7159589 A) (@lem7159588 A B x f s)). Qed.
Lemma lem7159595 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term95 A B x f s) = (term102 A B x f s).
Proof. exact (TRANS (@lem7159571 A B x f s) (@lem7159590 A B x f s)). Qed.
Lemma lem7159596 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7159597 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term76 A B x f s) = (term103 A B x f s).
Proof. exact (MK_COMB (@lem7159596) (@lem7159595 A B x f s)). Qed.
Lemma lem7159598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7159599 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term88 A B x f s) = (term104 A B x f s).
Proof. exact (MK_COMB (@lem7159598) (@lem7159597 A B x f s)). Qed.
Lemma lem7159603 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7159604 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem7159603 B P x). Qed.
Lemma lem7159605 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem7159604 B t x). Qed.
Lemma lem7159606 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7159607 {B : Type'} (t : B -> Prop) (x : B) : (term86 B x t) = (term105 B t x).
Proof. exact (MK_COMB (@lem7159606) (@lem7159605 B t x)). Qed.
Lemma lem7159617 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term95 A B y f s) = (term96 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem7159618 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term95 A B y f s) = (term96 A B y f s).
Proof. exact (@lem7159617 A B y f s). Qed.
Lemma lem7159619 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term95 A B x f s) = (term96 A B x f s).
Proof. exact (@lem7159618 A B x f s). Qed.
Lemma lem7159629 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7159630 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7159629 A P x). Qed.
Lemma lem7159631 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem7159630 A s x). Qed.
Lemma lem7159632 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term97 A B x f x') = (term97 A B x f x').
Proof. exact (eq_refl (term97 A B x f x')). Qed.
Lemma lem7159633 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term98 A B x f x' s) = (term99 A B x f s x').
Proof. exact (MK_COMB (@lem7159632 A B x f x') (@lem7159631 A s x')). Qed.
Lemma lem7159636 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term100 A B x f s) = (term101 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem7159633 A B x f s x')). Qed.
Lemma lem7159637 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7159638 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term96 A B x f s) = (term102 A B x f s).
Proof. exact (MK_COMB (@lem7159637 A) (@lem7159636 A B x f s)). Qed.
Lemma lem7159643 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term95 A B x f s) = (term102 A B x f s).
Proof. exact (TRANS (@lem7159619 A B x f s) (@lem7159638 A B x f s)). Qed.
Lemma lem7159644 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7159645 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term106 A B x f s) = (term107 A B x f s).
Proof. exact (MK_COMB (@lem7159644) (@lem7159643 A B x f s)). Qed.
Lemma lem7159647 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7159648 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem7159647 B P x). Qed.
Lemma lem7159649 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem7159648 B t x). Qed.
Lemma lem7159650 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term108 A B f s x t) = (term109 A B f s t x).
Proof. exact (MK_COMB (@lem7159645 A B x f s) (@lem7159649 B t x)). Qed.
Lemma lem7159653 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term110 A B f s t) = (term111 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem7159650 A B f s t x)). Qed.
Lemma lem7159654 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7159655 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term83 A B f s t) = (term112 A B f s t).
Proof. exact (MK_COMB (@lem7159654 B) (@lem7159653 A B f s t)). Qed.
Lemma lem7159660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7159661 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term84 A B f s t) = (term113 A B f s t).
Proof. exact (MK_COMB (@lem7159660) (@lem7159655 A B f s t)). Qed.
Lemma lem7159662 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7159663 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term85 A B f t s) = (term114 A B f t s).
Proof. exact (MK_COMB (@lem7159661 A B f s t) (@lem7159662 A s)). Qed.
Lemma lem7159666 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term87 A B x f t s) = (term115 A B x f t s).
Proof. exact (MK_COMB (@lem7159607 B t x) (@lem7159663 A B f t s)). Qed.
Lemma lem7159669 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term89 A B x f t s) = (term116 A B x f t s).
Proof. exact (MK_COMB (@lem7159599 A B x f s) (@lem7159666 A B x f t s)). Qed.
Lemma lem7159672 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7159673 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term91 A B x f t s) = (term117 A B x f t s).
Proof. exact (MK_COMB (@lem7159672) (@lem7159669 A B x f t s)). Qed.
Lemma lem7159681 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term118 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem7159682 {A : Type'} (p : A -> Prop) (x : A) : (term118 A x p) = (p x).
Proof. exact (@lem7159681 A p x). Qed.
Lemma lem7159683 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (x' : A) : (term119 A B x' s f x) = (term120 A B s f x x').
Proof. exact (@lem7159682 A (term121 A B s f x) x'). Qed.
Lemma lem7159684 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term120 A B s f x' x) = (term122 A B s f x x').
Proof. exact (eq_refl (term120 A B s f x' x)). Qed.
Lemma lem7159685 {A : Type'} (GEN_PVAR_325 : A) : (@SETSPEC A GEN_PVAR_325) = (@SETSPEC A GEN_PVAR_325).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_325)). Qed.
Lemma lem7159686 {A B : Type'} (GEN_PVAR_325 : A) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term123 A B GEN_PVAR_325 s f x' x) = (term124 A B GEN_PVAR_325 s f x x').
Proof. exact (MK_COMB (@lem7159685 A GEN_PVAR_325) (@lem7159684 A B s f x x')). Qed.
Lemma lem7159687 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7159688 {A B : Type'} (GEN_PVAR_325 : A) (s : A -> Prop) (f : A -> B) (x : B) (x' : A) : (term125 A B GEN_PVAR_325 s f x x') = (term126 A B GEN_PVAR_325 s f x x').
Proof. exact (MK_COMB (@lem7159686 A B GEN_PVAR_325 s f x' x) (@lem7159687 A x')). Qed.
Lemma lem7159689 {A B : Type'} (GEN_PVAR_325 : A) (s : A -> Prop) (f : A -> B) (x : B) : (term127 A B GEN_PVAR_325 s f x) = (term128 A B GEN_PVAR_325 s f x).
Proof. exact (fun_ext (fun x' : A => @lem7159688 A B GEN_PVAR_325 s f x x')). Qed.
Lemma lem7159690 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7159691 {A B : Type'} (GEN_PVAR_325 : A) (s : A -> Prop) (f : A -> B) (x : B) : (term129 A B GEN_PVAR_325 s f x) = (term130 A B GEN_PVAR_325 s f x).
Proof. exact (MK_COMB (@lem7159690 A) (@lem7159689 A B GEN_PVAR_325 s f x)). Qed.
Lemma lem7159692 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term131 A B s f x) = (term132 A B s f x).
Proof. exact (fun_ext (fun GEN_PVAR_325 : A => @lem7159691 A B GEN_PVAR_325 s f x)). Qed.
Lemma lem7159693 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7159694 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term133 A B s f x) = (term78 A B s f x).
Proof. exact (MK_COMB (@lem7159693 A) (@lem7159692 A B s f x)). Qed.
Lemma lem7159695 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem7159696 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : B) : (term119 A B x s f x') = (term134 A B x s f x').
Proof. exact (MK_COMB (@lem7159695 A x) (@lem7159694 A B s f x')). Qed.
Lemma lem7159697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7159698 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : B) : (term135 A B x s f x') = (term136 A B x s f x').
Proof. exact (MK_COMB (@lem7159697) (@lem7159696 A B x s f x')). Qed.
Lemma lem7159699 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term120 A B s f x' x) = (term122 A B s f x x').
Proof. exact (eq_refl (term120 A B s f x' x)). Qed.
Lemma lem7159700 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : ((term119 A B x s f x') = (term120 A B s f x' x)) = ((term134 A B x s f x') = (term122 A B s f x x')).
Proof. exact (MK_COMB (@lem7159698 A B x s f x') (@lem7159699 A B s f x x')). Qed.
Lemma lem7159701 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term134 A B x s f x') = (term122 A B s f x x').
Proof. exact (EQ_MP (@lem7159700 A B s f x x') (@lem7159683 A B s f x' x)). Qed.
Lemma lem7159705 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem7159706 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem7159705 A P x). Qed.
Lemma lem7159707 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem7159706 A s x). Qed.
Lemma lem7159708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7159709 {A : Type'} (s : A -> Prop) (x : A) : (term86 A x s) = (term105 A s x).
Proof. exact (MK_COMB (@lem7159708) (@lem7159707 A s x)). Qed.
Lemma lem7159712 {A B : Type'} (f : A -> B) (x : A) (x' : B) : ((f x) = x') = ((f x) = x').
Proof. exact (eq_refl ((f x) = x')). Qed.
Lemma lem7159713 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term122 A B s f x x') = (term137 A B s f x x').
Proof. exact (MK_COMB (@lem7159709 A s x) (@lem7159712 A B f x x')). Qed.
Lemma lem7159716 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term134 A B x s f x') = (term137 A B s f x x').
Proof. exact (TRANS (@lem7159701 A B s f x x') (@lem7159713 A B s f x x')). Qed.
Lemma lem7159717 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7159718 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term138 A B x s f x') = (term139 A B s f x x').
Proof. exact (MK_COMB (@lem7159717) (@lem7159716 A B s f x x')). Qed.
Lemma lem7159721 {A : Type'} (g : A -> real) (x : A) : ((g x) = term6) = ((g x) = term6).
Proof. exact (eq_refl ((g x) = term6)). Qed.
Lemma lem7159722 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (x' : A) : (term140 A B s f x g x') = (term141 A B s f x g x').
Proof. exact (MK_COMB (@lem7159718 A B s f x' x) (@lem7159721 A g x')). Qed.
Lemma lem7159725 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term142 A B s f x g) = (term143 A B s f x g).
Proof. exact (fun_ext (fun x' : A => @lem7159722 A B s f x g x')). Qed.
Lemma lem7159726 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7159727 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term92 A B s f x g) = (term144 A B s f x g).
Proof. exact (MK_COMB (@lem7159726 A) (@lem7159725 A B s f x g)). Qed.
Lemma lem7159732 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term94 A B t s f x g) = (term145 A B t s f x g).
Proof. exact (MK_COMB (@lem7159673 A B x f t s) (@lem7159727 A B s f x g)). Qed.
Lemma lem7159735 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term145 A B t s f x g) = (term94 A B t s f x g).
Proof. exact (SYM (@lem7159732 A B t s f x g)). Qed.
Lemma lem7159737 (p : Prop) : p = (term146 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7159738 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term145 A B t s f x g) = (term147 A B t s f x g).
Proof. exact (@lem7159737 (term145 A B t s f x g)). Qed.
Lemma lem7159739 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term147 A B t s f x g) = (term145 A B t s f x g).
Proof. exact (SYM (@lem7159738 A B t s f x g)). Qed.
Lemma lem7159740 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (h1 : term148 A B t s f x g) : term148 A B t s f x g.
Proof. exact (h1). Qed.
Lemma lem7159743 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (h1 : term147 A B t s f x g) : term147 A B t s f x g.
Proof. exact (h1). Qed.
Lemma lem7159744 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term149 A B t s f x g.
Proof. exact (fun h0 : term147 A B t s f x g => @lem7159743 A B t s f x g h0). Qed.
Lemma lem7159745 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (h1 : term149 A B t s f x g) : term149 A B t s f x g.
Proof. exact (h1). Qed.
Lemma lem7159746 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (h1 : term147 A B t s f x g) : term147 A B t s f x g.
Proof. exact (h1). Qed.
Lemma lem7159747 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (h1 : term147 A B t s f x g) (h2 : term149 A B t s f x g) : term147 A B t s f x g.
Proof. exact (@lem7159745 A B t s f x g h2 (@lem7159746 A B t s f x g h1)). Qed.
Lemma lem7159748 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (h1 : term147 A B t s f x g) : term150 A B t s f x g.
Proof. exact (fun h0 : term149 A B t s f x g => @lem7159747 A B t s f x g h1 h0). Qed.
Lemma lem7159749 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (h1 : term149 A B t s f x g) : term149 A B t s f x g.
Proof. exact (h1). Qed.
Lemma lem7159750 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (h1 : term147 A B t s f x g) (h2 : term149 A B t s f x g) : term147 A B t s f x g.
Proof. exact (@lem7159748 A B t s f x g h1 (@lem7159749 A B t s f x g h2)). Qed.
Lemma lem7159751 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (h1 : term149 A B t s f x g) : term149 A B t s f x g.
Proof. exact (fun h0 : term147 A B t s f x g => @lem7159750 A B t s f x g h0 h1). Qed.
Lemma lem7159752 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term151 A B t s f x g.
Proof. exact (fun h0 : term149 A B t s f x g => @lem7159751 A B t s f x g h0). Qed.
Lemma lem7159755 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term149 A B t s f x g.
Proof. exact (@lem7159752 A B t s f x g (@lem7159744 A B t s f x g)). Qed.
Lemma lem7159756 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term149 A B t s f x g.
Proof. exact (@lem7159755 A B t s f x g). Qed.
Lemma lem7159778 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7159779 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term147 A B t s f x g) = (term152 A B t s f x g).
Proof. exact (@lem7159778 (term148 A B t s f x g)). Qed.
Lemma lem7159781 (t : Prop) : (term153 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7159782 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term152 A B t s f x g) = (term145 A B t s f x g).
Proof. exact (@lem7159781 (term145 A B t s f x g)). Qed.
Lemma lem7159785 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term147 A B t s f x g) = (term145 A B t s f x g).
Proof. exact (TRANS (@lem7159779 A B t s f x g) (@lem7159782 A B t s f x g)). Qed.
Lemma lem7159874 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term154 A B s f x g) = (term155 A B s f x g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7159785 A B t s f x g)). Qed.
Lemma lem7159875 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7159876 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term156 A B s f x g) = (term157 A B s f x g).
Proof. exact (MK_COMB (@lem7159875 B) (@lem7159874 A B s f x g)). Qed.
Lemma lem7159881 {A B : Type'} (f : A -> B) (x : B) (g : A -> real) : (term158 A B f x g) = (term159 A B f x g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7159876 A B s f x g)). Qed.
Lemma lem7159882 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7159883 {A B : Type'} (f : A -> B) (x : B) (g : A -> real) : (term160 A B f x g) = (term161 A B f x g).
Proof. exact (MK_COMB (@lem7159882 A) (@lem7159881 A B f x g)). Qed.
Lemma lem7159888 {A B : Type'} (x : B) (g : A -> real) : (term162 A B x g) = (term163 A B x g).
Proof. exact (fun_ext (fun f : A -> B => @lem7159883 A B f x g)). Qed.
Lemma lem7159889 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7159890 {A B : Type'} (x : B) (g : A -> real) : (term164 A B x g) = (term165 A B x g).
Proof. exact (MK_COMB (@lem7159889 A B) (@lem7159888 A B x g)). Qed.
Lemma lem7159895 {A B : Type'} (g : A -> real) : (term166 A B g) = (term167 A B g).
Proof. exact (fun_ext (fun x : B => @lem7159890 A B x g)). Qed.
Lemma lem7159896 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7159897 {A B : Type'} (g : A -> real) : (term168 A B g) = (term169 A B g).
Proof. exact (MK_COMB (@lem7159896 B) (@lem7159895 A B g)). Qed.
Lemma lem7159902 {A B : Type'} : (term170 A B) = (term171 A B).
Proof. exact (fun_ext (fun g : A -> real => @lem7159897 A B g)). Qed.
Lemma lem7159903 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7159912 {A B : Type'} : (term172 A B) = (term173 A B).
Proof. exact (MK_COMB (@lem7159903 A) (@lem7159902 A B)). Qed.
Lemma lem7159921 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (x' : A) : (term141 A B s f x g x') = (term141 A B s f x g x').
Proof. exact (eq_refl (term141 A B s f x g x')). Qed.
Lemma lem7159922 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term143 A B s f x g) = (term143 A B s f x g).
Proof. exact (fun_ext (fun x' : A => @lem7159921 A B s f x g x')). Qed.
Lemma lem7159923 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7159924 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term144 A B s f x g) = (term144 A B s f x g).
Proof. exact (MK_COMB (@lem7159923 A) (@lem7159922 A B s f x g)). Qed.
Lemma lem7159925 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7159926 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem7159931 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term99 A B x f s x') = (term99 A B x f s x').
Proof. exact (eq_refl (term99 A B x f s x')). Qed.
Lemma lem7159932 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term101 A B x f s) = (term101 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem7159931 A B x f s x')). Qed.
Lemma lem7159933 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7159934 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term102 A B x f s) = (term102 A B x f s).
Proof. exact (MK_COMB (@lem7159933 A) (@lem7159932 A B x f s)). Qed.
Lemma lem7159935 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7159936 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term107 A B x f s) = (term107 A B x f s).
Proof. exact (MK_COMB (@lem7159935) (@lem7159934 A B x f s)). Qed.
Lemma lem7159937 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term109 A B f s t x) = (term109 A B f s t x).
Proof. exact (MK_COMB (@lem7159936 A B x f s) (@lem7159926 B t x)). Qed.
Lemma lem7159938 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term111 A B f s t) = (term111 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem7159937 A B f s t x)). Qed.
Lemma lem7159939 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7159940 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term112 A B f s t) = (term112 A B f s t).
Proof. exact (MK_COMB (@lem7159939 B) (@lem7159938 A B f s t)). Qed.
Lemma lem7159941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7159942 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term113 A B f s t) = (term113 A B f s t).
Proof. exact (MK_COMB (@lem7159941) (@lem7159940 A B f s t)). Qed.
Lemma lem7159943 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term114 A B f t s) = (term114 A B f t s).
Proof. exact (MK_COMB (@lem7159942 A B f s t) (@lem7159925 A s)). Qed.
Lemma lem7159946 {B : Type'} (t : B -> Prop) (x : B) : (term105 B t x) = (term105 B t x).
Proof. exact (eq_refl (term105 B t x)). Qed.
Lemma lem7159947 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term115 A B x f t s) = (term115 A B x f t s).
Proof. exact (MK_COMB (@lem7159946 B t x) (@lem7159943 A B f t s)). Qed.
Lemma lem7159952 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term99 A B x f s x') = (term99 A B x f s x').
Proof. exact (eq_refl (term99 A B x f s x')). Qed.
Lemma lem7159953 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term101 A B x f s) = (term101 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem7159952 A B x f s x')). Qed.
Lemma lem7159954 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7159955 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term102 A B x f s) = (term102 A B x f s).
Proof. exact (MK_COMB (@lem7159954 A) (@lem7159953 A B x f s)). Qed.
Lemma lem7159956 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7159957 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term103 A B x f s) = (term103 A B x f s).
Proof. exact (MK_COMB (@lem7159956) (@lem7159955 A B x f s)). Qed.
Lemma lem7159958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7159959 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term104 A B x f s) = (term104 A B x f s).
Proof. exact (MK_COMB (@lem7159958) (@lem7159957 A B x f s)). Qed.
Lemma lem7159960 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term116 A B x f t s) = (term116 A B x f t s).
Proof. exact (MK_COMB (@lem7159959 A B x f s) (@lem7159947 A B x f t s)). Qed.
Lemma lem7159961 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7159962 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term117 A B x f t s) = (term117 A B x f t s).
Proof. exact (MK_COMB (@lem7159961) (@lem7159960 A B x f t s)). Qed.
Lemma lem7159963 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term145 A B t s f x g) = (term145 A B t s f x g).
Proof. exact (MK_COMB (@lem7159962 A B x f t s) (@lem7159924 A B s f x g)). Qed.
Lemma lem7159964 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term155 A B s f x g) = (term155 A B s f x g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7159963 A B t s f x g)). Qed.
Lemma lem7159965 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7159966 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term157 A B s f x g) = (term157 A B s f x g).
Proof. exact (MK_COMB (@lem7159965 B) (@lem7159964 A B s f x g)). Qed.
Lemma lem7159967 {A B : Type'} (f : A -> B) (x : B) (g : A -> real) : (term159 A B f x g) = (term159 A B f x g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7159966 A B s f x g)). Qed.
Lemma lem7159968 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7159969 {A B : Type'} (f : A -> B) (x : B) (g : A -> real) : (term161 A B f x g) = (term161 A B f x g).
Proof. exact (MK_COMB (@lem7159968 A) (@lem7159967 A B f x g)). Qed.
Lemma lem7159970 {A B : Type'} (x : B) (g : A -> real) : (term163 A B x g) = (term163 A B x g).
Proof. exact (fun_ext (fun f : A -> B => @lem7159969 A B f x g)). Qed.
Lemma lem7159971 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7159972 {A B : Type'} (x : B) (g : A -> real) : (term165 A B x g) = (term165 A B x g).
Proof. exact (MK_COMB (@lem7159971 A B) (@lem7159970 A B x g)). Qed.
Lemma lem7159973 {A B : Type'} (g : A -> real) : (term167 A B g) = (term167 A B g).
Proof. exact (fun_ext (fun x : B => @lem7159972 A B x g)). Qed.
Lemma lem7159974 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7159975 {A B : Type'} (g : A -> real) : (term169 A B g) = (term169 A B g).
Proof. exact (MK_COMB (@lem7159974 B) (@lem7159973 A B g)). Qed.
Lemma lem7159976 {A B : Type'} : (term171 A B) = (term171 A B).
Proof. exact (fun_ext (fun g : A -> real => @lem7159975 A B g)). Qed.
Lemma lem7159977 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7159978 {A B : Type'} : (term173 A B) = (term173 A B).
Proof. exact (MK_COMB (@lem7159977 A) (@lem7159976 A B)). Qed.
Lemma lem7160053 {A B : Type'} : (term172 A B) = (term173 A B).
Proof. exact (TRANS (@lem7159912 A B) (@lem7159978 A B)). Qed.
Lemma lem7160054 {A B : Type'} : (term173 A B) = (term172 A B).
Proof. exact (SYM (@lem7160053 A B)). Qed.
Lemma lem7160055 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term116 A B x f t s) : term116 A B x f t s.
Proof. exact (h1). Qed.
Lemma lem7160058 (p : Prop) : p = (term146 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7160059 {A : Type'} (g : A -> real) (x' : A) : ((g x') = term6) = (term174 A g x').
Proof. exact (@lem7160058 ((g x') = term6)). Qed.
Lemma lem7160060 {A : Type'} (g : A -> real) (x' : A) : (term174 A g x') = ((g x') = term6).
Proof. exact (SYM (@lem7160059 A g x')). Qed.
Lemma lem7160068 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term175 A B x f s x') = (term176 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem7160069 {A : Type'} (P : A -> Prop) : (term177 A P) = (term178 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem7160070 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term103 A B x f s) = (term179 A B x f s).
Proof. exact (@lem7160069 A (term101 A B x f s)). Qed.
Lemma lem7160071 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term180 A B x f s x') = (term99 A B x f s x').
Proof. exact (eq_refl (term180 A B x f s x')). Qed.
Lemma lem7160072 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7160073 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term181 A B x f s x') = (term175 A B x f s x').
Proof. exact (MK_COMB (@lem7160072) (@lem7160071 A B x f s x')). Qed.
Lemma lem7160074 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term181 A B x f s x') = (term176 A B x f s x').
Proof. exact (TRANS (@lem7160073 A B x f s x') (@lem7160068 A B x f s x')). Qed.
Lemma lem7160075 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term182 A B x f s) = (term183 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem7160074 A B x f s x')). Qed.
Lemma lem7160076 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7160077 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term179 A B x f s) = (term184 A B x f s).
Proof. exact (MK_COMB (@lem7160076 A) (@lem7160075 A B x f s)). Qed.
Lemma lem7160078 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term103 A B x f s) = (term184 A B x f s).
Proof. exact (TRANS (@lem7160070 A B x f s) (@lem7160077 A B x f s)). Qed.
Lemma lem7160086 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term175 A B x f s x') = (term176 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem7160087 {A : Type'} (P : A -> Prop) : (term177 A P) = (term178 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem7160088 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term103 A B x f s) = (term179 A B x f s).
Proof. exact (@lem7160087 A (term101 A B x f s)). Qed.
Lemma lem7160089 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term180 A B x f s x') = (term99 A B x f s x').
Proof. exact (eq_refl (term180 A B x f s x')). Qed.
Lemma lem7160090 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7160091 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term181 A B x f s x') = (term175 A B x f s x').
Proof. exact (MK_COMB (@lem7160090) (@lem7160089 A B x f s x')). Qed.
Lemma lem7160092 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term181 A B x f s x') = (term176 A B x f s x').
Proof. exact (TRANS (@lem7160091 A B x f s x') (@lem7160086 A B x f s x')). Qed.
Lemma lem7160093 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term182 A B x f s) = (term183 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem7160092 A B x f s x')). Qed.
Lemma lem7160094 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7160095 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term179 A B x f s) = (term184 A B x f s).
Proof. exact (MK_COMB (@lem7160094 A) (@lem7160093 A B x f s)). Qed.
Lemma lem7160096 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term103 A B x f s) = (term184 A B x f s).
Proof. exact (TRANS (@lem7160088 A B x f s) (@lem7160095 A B x f s)). Qed.
Lemma lem7160097 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem7160098 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7160099 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term185 A B x f s) = (term186 A B x f s).
Proof. exact (MK_COMB (@lem7160098) (@lem7160096 A B x f s)). Qed.
Lemma lem7160100 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term187 A B f s t x) = (term188 A B f s t x).
Proof. exact (MK_COMB (@lem7160099 A B x f s) (@lem7160097 B t x)). Qed.
Lemma lem7160101 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term109 A B f s t x) = (term187 A B f s t x).
Proof. exact (@lem17265 (term102 A B x f s) (t x)). Qed.
Lemma lem7160102 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term109 A B f s t x) = (term188 A B f s t x).
Proof. exact (TRANS (@lem7160101 A B f s t x) (@lem7160100 A B f s t x)). Qed.
Lemma lem7160103 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term111 A B f s t) = (term189 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem7160102 A B f s t x)). Qed.
Lemma lem7160104 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7160105 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term112 A B f s t) = (term190 A B f s t).
Proof. exact (MK_COMB (@lem7160104 B) (@lem7160103 A B f s t)). Qed.
Lemma lem7160106 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7160107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7160108 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term113 A B f s t) = (term191 A B f s t).
Proof. exact (MK_COMB (@lem7160107) (@lem7160105 A B f s t)). Qed.
Lemma lem7160109 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term114 A B f t s) = (term192 A B f t s).
Proof. exact (MK_COMB (@lem7160108 A B f s t) (@lem7160106 A s)). Qed.
Lemma lem7160111 {B : Type'} (t : B -> Prop) (x : B) : (term105 B t x) = (term105 B t x).
Proof. exact (eq_refl (term105 B t x)). Qed.
Lemma lem7160112 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term115 A B x f t s) = (term193 A B x f t s).
Proof. exact (MK_COMB (@lem7160111 B t x) (@lem7160109 A B f t s)). Qed.
Lemma lem7160113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7160114 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term104 A B x f s) = (term194 A B x f s).
Proof. exact (MK_COMB (@lem7160113) (@lem7160078 A B x f s)). Qed.
Lemma lem7160247 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term116 A B x f t s) = (term195 A B x f t s).
Proof. exact (MK_COMB (@lem7160114 A B x f s) (@lem7160112 A B x f t s)). Qed.
Lemma lem7160248 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term116 A B x f t s) : term195 A B x f t s.
Proof. exact (EQ_MP (@lem7160247 A B x f t s) (@lem7160055 A B x f t s h1)). Qed.
Lemma lem7160258 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term137 A B s f x' x) : term137 A B s f x' x.
Proof. exact (h1). Qed.
Lemma lem7160267 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem7160270 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem7160271 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7160276 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7160277 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem7160276 A Prop f x). Qed.
Lemma lem7160279 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem7160277 A s x). Qed.
Lemma lem7160280 {A : Type'} (s : A -> Prop) (x : A) : (term196 A s x) = (term197 A s x).
Proof. exact (MK_COMB (@lem7160271) (@lem7160279 A s x)). Qed.
Lemma lem7160291 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term198 A B x f x') = (term198 A B x f x').
Proof. exact (eq_refl (term198 A B x f x')). Qed.
Lemma lem7160292 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term176 A B x f s x') = (term199 A B x f s x').
Proof. exact (MK_COMB (@lem7160291 A B x f x') (@lem7160280 A s x')). Qed.
Lemma lem7160293 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term183 A B x f s) = (term200 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem7160292 A B x f s x')). Qed.
Lemma lem7160294 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7160295 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term184 A B x f s) = (term201 A B x f s).
Proof. exact (MK_COMB (@lem7160294 A) (@lem7160293 A B x f s)). Qed.
Lemma lem7160296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7160297 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term186 A B x f s) = (term202 A B x f s).
Proof. exact (MK_COMB (@lem7160296) (@lem7160295 A B x f s)). Qed.
Lemma lem7160298 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term188 A B f s t x) = (term203 A B f s t x).
Proof. exact (MK_COMB (@lem7160297 A B x f s) (@lem7160270 B t x)). Qed.
Lemma lem7160299 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term189 A B f s t) = (term204 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem7160298 A B f s t x)). Qed.
Lemma lem7160300 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem7160301 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term190 A B f s t) = (term205 A B f s t).
Proof. exact (MK_COMB (@lem7160300 B) (@lem7160299 A B f s t)). Qed.
Lemma lem7160302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7160303 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term191 A B f s t) = (term206 A B f s t).
Proof. exact (MK_COMB (@lem7160302) (@lem7160301 A B f s t)). Qed.
Lemma lem7160304 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term192 A B f t s) = (term207 A B f t s).
Proof. exact (MK_COMB (@lem7160303 A B f s t) (@lem7160267 A s)). Qed.
Lemma lem7160309 {B : Type'} (t : B -> Prop) (x : B) : (term105 B t x) = (term105 B t x).
Proof. exact (eq_refl (term105 B t x)). Qed.
Lemma lem7160310 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term193 A B x f t s) = (term208 A B x f t s).
Proof. exact (MK_COMB (@lem7160309 B t x) (@lem7160304 A B f t s)). Qed.
Lemma lem7160311 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7160316 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7160317 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem7160316 A Prop f x). Qed.
Lemma lem7160319 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem7160317 A s x). Qed.
Lemma lem7160320 {A : Type'} (s : A -> Prop) (x : A) : (term196 A s x) = (term197 A s x).
Proof. exact (MK_COMB (@lem7160311) (@lem7160319 A s x)). Qed.
Lemma lem7160331 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term198 A B x f x') = (term198 A B x f x').
Proof. exact (eq_refl (term198 A B x f x')). Qed.
Lemma lem7160332 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term176 A B x f s x') = (term199 A B x f s x').
Proof. exact (MK_COMB (@lem7160331 A B x f x') (@lem7160320 A s x')). Qed.
Lemma lem7160333 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term183 A B x f s) = (term200 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem7160332 A B x f s x')). Qed.
Lemma lem7160334 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7160335 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term184 A B x f s) = (term201 A B x f s).
Proof. exact (MK_COMB (@lem7160334 A) (@lem7160333 A B x f s)). Qed.
Lemma lem7160336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7160337 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term194 A B x f s) = (term209 A B x f s).
Proof. exact (MK_COMB (@lem7160336) (@lem7160335 A B x f s)). Qed.
Lemma lem7160338 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term195 A B x f t s) = (term210 A B x f t s).
Proof. exact (MK_COMB (@lem7160337 A B x f s) (@lem7160310 A B x f t s)). Qed.
Lemma lem7160339 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term116 A B x f t s) : term210 A B x f t s.
Proof. exact (EQ_MP (@lem7160338 A B x f t s) (@lem7160248 A B x f t s h1)). Qed.
Lemma lem7160346 {A B : Type'} (f : A -> B) (x' : A) (x : B) : ((f x') = x) = ((f x') = x).
Proof. exact (eq_refl ((f x') = x)). Qed.
Lemma lem7160351 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7160352 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem7160351 A Prop f x). Qed.
Lemma lem7160354 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7160352 A s x'). Qed.
Lemma lem7160355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7160356 {A : Type'} (s : A -> Prop) (x' : A) : (term105 A s x') = (term211 A s x').
Proof. exact (MK_COMB (@lem7160355) (@lem7160354 A s x')). Qed.
Lemma lem7160357 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) : (term137 A B s f x' x) = (term212 A B s f x' x).
Proof. exact (MK_COMB (@lem7160356 A s x') (@lem7160346 A B f x' x)). Qed.
Lemma lem7160358 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term137 A B s f x' x) : term212 A B s f x' x.
Proof. exact (EQ_MP (@lem7160357 A B s f x' x) (@lem7160258 A B s f x' x h1)). Qed.
Lemma lem7160376 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term116 A B x f t s) : term201 A B x f s.
Proof. exact (proj1 (@lem7160339 A B x f t s h1)). Qed.
Lemma lem7160400 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term199 A B x f s x') = (term199 A B x f s x').
Proof. exact (eq_refl (term199 A B x f s x')). Qed.
Lemma lem7160401 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term200 A B x f s) = (term200 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem7160400 A B x f s x')). Qed.
Lemma lem7160402 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7160404 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term201 A B x f s) = (term201 A B x f s).
Proof. exact (MK_COMB (@lem7160402 A) (@lem7160401 A B x f s)). Qed.
Lemma lem7160405 {A B : Type'} (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term116 A B x f t s) : term201 A B x f s.
Proof. exact (EQ_MP (@lem7160404 A B x f s) (@lem7160376 A B x f t s h1)). Qed.
Lemma lem7160462 {A B : Type'} (_95834 : A) (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term116 A B x f t s) : term213 A B x f s _95834.
Proof. exact (@lem7160405 A B x f t s h1 _95834). Qed.
Lemma lem7160463 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_95834 : A) : (term213 A B x f s _95834) = (term199 A B x f s _95834).
Proof. exact (eq_refl (term213 A B x f s _95834)). Qed.
Lemma lem7160476 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term137 A B s f x' x) : (f x') = x.
Proof. exact (proj2 (@lem7160358 A B s f x' x h1)). Qed.
Lemma lem7160482 {A B : Type'} (_95834 : A) (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term116 A B x f t s) : term199 A B x f s _95834.
Proof. exact (EQ_MP (@lem7160463 A B x f s _95834) (@lem7160462 A B _95834 x f t s h1)). Qed.
Lemma lem7160499 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term137 A B s f x' x) : x = (f x').
Proof. exact (SYM (@lem7160476 A B s f x' x h1)). Qed.
Lemma lem7160542 {A B : Type'} (f : A -> B) (s : A -> Prop) (_95834 : A) : (term214 A B f s _95834) = (term214 A B f s _95834).
Proof. exact (eq_refl (term214 A B f s _95834)). Qed.
Lemma lem7160543 {A B : Type'} (_95834 : A) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term137 A B s f x' x) : (term215 A B f s _95834 x) = (term216 A B s _95834 f x').
Proof. exact (MK_COMB (@lem7160542 A B f s _95834) (@lem7160499 A B s f x' x h1)). Qed.
Lemma lem7160544 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_95834 : A) : (term216 A B s _95834 f x') = (term217 A B x' f s _95834).
Proof. exact (eq_refl (term216 A B s _95834 f x')). Qed.
Lemma lem7160545 {A B : Type'} (f : A -> B) (s : A -> Prop) (_95834 : A) (x : B) : (term218 A B f s _95834 x) = (term218 A B f s _95834 x).
Proof. exact (eq_refl (term218 A B f s _95834 x)). Qed.
Lemma lem7160546 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_95834 : A) : ((term215 A B f s _95834 x) = (term216 A B s _95834 f x')) = ((term215 A B f s _95834 x) = (term217 A B x' f s _95834)).
Proof. exact (MK_COMB (@lem7160545 A B f s _95834 x) (@lem7160544 A B x' f s _95834)). Qed.
Lemma lem7160547 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_95834 : A) : (term215 A B f s _95834 x) = (term199 A B x f s _95834).
Proof. exact (eq_refl (term215 A B f s _95834 x)). Qed.
Lemma lem7160548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7160549 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (_95834 : A) : (term218 A B f s _95834 x) = (term219 A B x f s _95834).
Proof. exact (MK_COMB (@lem7160548) (@lem7160547 A B x f s _95834)). Qed.
Lemma lem7160550 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_95834 : A) : (term217 A B x' f s _95834) = (term217 A B x' f s _95834).
Proof. exact (eq_refl (term217 A B x' f s _95834)). Qed.
Lemma lem7160551 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_95834 : A) : ((term215 A B f s _95834 x) = (term217 A B x' f s _95834)) = ((term199 A B x f s _95834) = (term217 A B x' f s _95834)).
Proof. exact (MK_COMB (@lem7160549 A B x f s _95834) (@lem7160550 A B x' f s _95834)). Qed.
Lemma lem7160552 {A B : Type'} (x : B) (x' : A) (f : A -> B) (s : A -> Prop) (_95834 : A) : ((term215 A B f s _95834 x) = (term216 A B s _95834 f x')) = ((term199 A B x f s _95834) = (term217 A B x' f s _95834)).
Proof. exact (TRANS (@lem7160546 A B x x' f s _95834) (@lem7160551 A B x x' f s _95834)). Qed.
Lemma lem7160553 {A B : Type'} (_95834 : A) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term137 A B s f x' x) : (term199 A B x f s _95834) = (term217 A B x' f s _95834).
Proof. exact (EQ_MP (@lem7160552 A B x x' f s _95834) (@lem7160543 A B _95834 s f x' x h1)). Qed.
Lemma lem7160554 {A B : Type'} (_95834 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term116 A B x f t s) (h2 : term137 A B s f x' x) : term217 A B x' f s _95834.
Proof. exact (EQ_MP (@lem7160553 A B _95834 s f x' x h2) (@lem7160482 A B _95834 x f t s h1)). Qed.
Lemma lem7160682 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem7160683 {B : Type'} (x : B) : x = x.
Proof. exact (@lem7160682 B x). Qed.
Lemma lem7160684 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem7160683 B (f x')). Qed.
Lemma lem7160685 {A B : Type'} (f : A -> B) (x' : A) : term220 A B f x'.
Proof. exact (fun h0 : term221 A B f x' => @lem7160684 A B f x'). Qed.
Lemma lem7160687 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7160688 {A B : Type'} (f : A -> B) (x' : A) : (term220 A B f x') = ((f x') = (f x')).
Proof. exact (@lem7160687 ((f x') = (f x'))). Qed.
Lemma lem7160689 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem7160688 A B f x') (@lem7160685 A B f x')). Qed.
Lemma lem7160691 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term137 A B s f x' x) : @I (A -> Prop) s x'.
Proof. exact (proj1 (@lem7160358 A B s f x' x h1)). Qed.
Lemma lem7160692 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term137 A B s f x' x) : term223 A s x'.
Proof. exact (fun h0 : term197 A s x' => @lem7160691 A B s f x' x h1). Qed.
Lemma lem7160694 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7160695 {A : Type'} (s : A -> Prop) (x' : A) : (term223 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem7160694 (@I (A -> Prop) s x')). Qed.
Lemma lem7160696 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term137 A B s f x' x) : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem7160695 A s x') (@lem7160692 A B s f x' x h1)). Qed.
Lemma lem7160698 (a : Prop) (b : Prop) : (term224 a b) = (term225 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7160699 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_95834 : A) : (term217 A B x' f s _95834) = (term226 A B x' f s _95834).
Proof. exact (@lem7160698 ((f x') = (f _95834)) (@I (A -> Prop) s _95834)). Qed.
Lemma lem7160701 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7160702 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_95834 : A) : (term226 A B x' f s _95834) = (term227 A B x' f s _95834).
Proof. exact (@lem7160701 (term228 A B x' f s _95834)). Qed.
Lemma lem7160703 {A B : Type'} (x' : A) (f : A -> B) (s : A -> Prop) (_95834 : A) : (term217 A B x' f s _95834) = (term227 A B x' f s _95834).
Proof. exact (TRANS (@lem7160699 A B x' f s _95834) (@lem7160702 A B x' f s _95834)). Qed.
Lemma lem7160705 {A B : Type'} (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term137 A B s f x' x) : term229 A B f s x'.
Proof. exact (conj (@lem7160689 A B f x') (@lem7160696 A B s f x' x h1)). Qed.
Lemma lem7160707 {A B : Type'} (_95834 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term116 A B x f t s) (h2 : term137 A B s f x' x) : term227 A B x' f s _95834.
Proof. exact (EQ_MP (@lem7160703 A B x' f s _95834) (@lem7160554 A B _95834 t s f x' x h1 h2)). Qed.
Lemma lem7160708 {A B : Type'} (_95834 : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term116 A B x f t s) (h2 : term137 A B s f x' x) : term227 A B x' f s _95834.
Proof. exact (@lem7160707 A B _95834 t s f x' x h1 h2). Qed.
Lemma lem7160709 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term116 A B x f t s) (h2 : term137 A B s f x' x) : term230 A B f s x'.
Proof. exact (@lem7160708 A B x' t s f x' x h1 h2). Qed.
Lemma lem7160712 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term116 A B x f t s) (h2 : term137 A B s f x' x) : False.
Proof. exact (@lem7160709 A B t s f x' x h1 h2 (@lem7160705 A B s f x' x h2)). Qed.
Lemma lem7160713 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term116 A B x f t s) (h2 : term137 A B s f x' x) : term231.
Proof. exact (fun h0 : ~ False => @lem7160712 A B t s f x' x h1 h2). Qed.
Lemma lem7160715 (p : Prop) : (term222 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7160716 : term231 = False.
Proof. exact (@lem7160715 False). Qed.
Lemma lem7160718 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term116 A B x f t s) (h2 : term137 A B s f x' x) : False.
Proof. exact (EQ_MP (@lem7160716) (@lem7160713 A B t s f x' x h1 h2)). Qed.
Lemma lem7160719 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term116 A B x f t s) (h2 : term137 A B s f x' x) : (term137 A B s f x' x) = False.
Proof. exact (prop_ext (fun h3 : term137 A B s f x' x => @lem7160718 A B t s f x' x h1 h2) (fun h3 : False => @lem7160258 A B s f x' x h2)). Qed.
Lemma lem7160720 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term116 A B x f t s) (h2 : term137 A B s f x' x) : False.
Proof. exact (EQ_MP (@lem7160719 A B t s f x' x h1 h2) (@lem7160258 A B s f x' x h2)). Qed.
Lemma lem7160721 {A B : Type'} (g : A -> real) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term116 A B x f t s) (h2 : term137 A B s f x' x) : term174 A g x'.
Proof. exact (fun h0 : term232 A g x' => @lem7160720 A B t s f x' x h1 h2). Qed.
Lemma lem7160722 {A B : Type'} (g : A -> real) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x' : A) (x : B) (h1 : term116 A B x f t s) (h2 : term137 A B s f x' x) : (g x') = term6.
Proof. exact (EQ_MP (@lem7160060 A g x') (@lem7160721 A B g t s f x' x h1 h2)). Qed.
Lemma lem7160723 {A B : Type'} (g : A -> real) (x' : A) (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term116 A B x f t s) : term141 A B s f x g x'.
Proof. exact (fun h0 : term137 A B s f x' x => @lem7160722 A B g t s f x' x h1 h0). Qed.
Lemma lem7160728 {A B : Type'} (g : A -> real) (x : B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) (h1 : term116 A B x f t s) : term144 A B s f x g.
Proof. exact (fun x' : A => @lem7160723 A B g x' x f t s h1). Qed.
Lemma lem7160729 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term145 A B t s f x g.
Proof. exact (fun h0 : term116 A B x f t s => @lem7160728 A B g x f t s h0). Qed.
Lemma lem7160734 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term157 A B s f x g.
Proof. exact (fun t : B -> Prop => @lem7160729 A B t s f x g). Qed.
Lemma lem7160739 {A B : Type'} (f : A -> B) (x : B) (g : A -> real) : term161 A B f x g.
Proof. exact (fun s : A -> Prop => @lem7160734 A B s f x g). Qed.
Lemma lem7160744 {A B : Type'} (x : B) (g : A -> real) : term165 A B x g.
Proof. exact (fun f : A -> B => @lem7160739 A B f x g). Qed.
Lemma lem7160749 {A B : Type'} (g : A -> real) : term169 A B g.
Proof. exact (fun x : B => @lem7160744 A B x g). Qed.
Lemma lem7160754 {A B : Type'} : term173 A B.
Proof. exact (fun g : A -> real => @lem7160749 A B g). Qed.
Lemma lem7160755 {A B : Type'} : term172 A B.
Proof. exact (EQ_MP (@lem7160054 A B) (@lem7160754 A B)). Qed.
Lemma lem7160756 {A B : Type'} (g : A -> real) : term233 A B g.
Proof. exact (@lem7160755 A B g). Qed.
Lemma lem7160757 {A B : Type'} (g : A -> real) : (term233 A B g) = (term168 A B g).
Proof. exact (eq_refl (term233 A B g)). Qed.
Lemma lem7160758 {A B : Type'} (g : A -> real) : term168 A B g.
Proof. exact (EQ_MP (@lem7160757 A B g) (@lem7160756 A B g)). Qed.
Lemma lem7160759 {A B : Type'} (g : A -> real) (x : B) : term234 A B g x.
Proof. exact (@lem7160758 A B g x). Qed.
Lemma lem7160760 {A B : Type'} (x : B) (g : A -> real) : (term234 A B g x) = (term164 A B x g).
Proof. exact (eq_refl (term234 A B g x)). Qed.
Lemma lem7160761 {A B : Type'} (x : B) (g : A -> real) : term164 A B x g.
Proof. exact (EQ_MP (@lem7160760 A B x g) (@lem7160759 A B g x)). Qed.
Lemma lem7160762 {A B : Type'} (x : B) (g : A -> real) (f : A -> B) : term235 A B x g f.
Proof. exact (@lem7160761 A B x g f). Qed.
Lemma lem7160763 {A B : Type'} (f : A -> B) (x : B) (g : A -> real) : (term235 A B x g f) = (term160 A B f x g).
Proof. exact (eq_refl (term235 A B x g f)). Qed.
Lemma lem7160764 {A B : Type'} (f : A -> B) (x : B) (g : A -> real) : term160 A B f x g.
Proof. exact (EQ_MP (@lem7160763 A B f x g) (@lem7160762 A B x g f)). Qed.
Lemma lem7160765 {A B : Type'} (f : A -> B) (x : B) (g : A -> real) (s : A -> Prop) : term236 A B f x g s.
Proof. exact (@lem7160764 A B f x g s). Qed.
Lemma lem7160766 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term236 A B f x g s) = (term156 A B s f x g).
Proof. exact (eq_refl (term236 A B f x g s)). Qed.
Lemma lem7160767 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term156 A B s f x g.
Proof. exact (EQ_MP (@lem7160766 A B s f x g) (@lem7160765 A B f x g s)). Qed.
Lemma lem7160768 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (t : B -> Prop) : term237 A B s f x g t.
Proof. exact (@lem7160767 A B s f x g t). Qed.
Lemma lem7160769 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : (term237 A B s f x g t) = (term147 A B t s f x g).
Proof. exact (eq_refl (term237 A B s f x g t)). Qed.
Lemma lem7160770 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term147 A B t s f x g.
Proof. exact (EQ_MP (@lem7160769 A B t s f x g) (@lem7160768 A B s f x g t)). Qed.
Lemma lem7160772 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term147 A B t s f x g.
Proof. exact (@lem7159756 A B t s f x g (@lem7160770 A B t s f x g)). Qed.
Lemma lem7160773 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (h1 : term148 A B t s f x g) : False.
Proof. exact (@lem7160772 A B t s f x g (@lem7159740 A B t s f x g h1)). Qed.
Lemma lem7160774 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (h1 : term148 A B t s f x g) : (term148 A B t s f x g) = False.
Proof. exact (prop_ext (fun h2 : term148 A B t s f x g => @lem7160773 A B t s f x g h1) (fun h2 : False => @lem7159740 A B t s f x g h1)). Qed.
Lemma lem7160775 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) (h1 : term148 A B t s f x g) : False.
Proof. exact (EQ_MP (@lem7160774 A B t s f x g h1) (@lem7159740 A B t s f x g h1)). Qed.
Lemma lem7160776 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term147 A B t s f x g.
Proof. exact (fun h0 : term148 A B t s f x g => @lem7160775 A B t s f x g h0). Qed.
Lemma lem7160777 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term145 A B t s f x g.
Proof. exact (EQ_MP (@lem7159739 A B t s f x g) (@lem7160776 A B t s f x g)). Qed.
Lemma lem7160778 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term94 A B t s f x g.
Proof. exact (EQ_MP (@lem7159735 A B t s f x g) (@lem7160777 A B t s f x g)). Qed.
Lemma lem7160779 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (g : A -> real) : term93 A B t s f x g.
Proof. exact (EQ_MP (@lem7159563 A B t s f x g) (@lem7160778 A B t s f x g)). Qed.
Lemma lem7160780 {A B : Type'} (g : A -> real) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term76 A B x f s) (h3 : @IN B x t) (h4 : term37 A B f s t) : term92 A B s f x g.
Proof. exact (@lem7160779 A B t s f x g (@lem7159504 A B x f s t h1 h2 h3 h4)). Qed.
Lemma lem7160781 {A B : Type'} (g : A -> real) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term76 A B x f s) (h3 : @IN B x t) (h4 : term37 A B f s t) : (term61 A B s f x g) = term6.
Proof. exact (@lem7159491 A B s f x g (@lem7160780 A B g x f s t h1 h2 h3 h4)). Qed.
Lemma lem7160782 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term75 A B t x f s) : term76 A B x f s.
Proof. exact (proj2 (@lem7159485 A B t x f s h1)). Qed.
Lemma lem7160783 {A B : Type'} (t : B -> Prop) (x : B) (f : A -> B) (s : A -> Prop) (h1 : term75 A B t x f s) : @IN B x t.
Proof. exact (proj1 (@lem7159485 A B t x f s h1)). Qed.
Lemma lem7160784 {A B : Type'} (g : A -> real) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term76 A B x f s) (h3 : @IN B x t) (h4 : term37 A B f s t) : (term76 A B x f s) = ((term61 A B s f x g) = term6).
Proof. exact (prop_ext (fun h5 : term76 A B x f s => @lem7160781 A B g x f s t h1 h2 h3 h4) (fun h5 : (term61 A B s f x g) = term6 => @lem7159486 A B x f s h2)). Qed.
Lemma lem7160785 {A B : Type'} (g : A -> real) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term76 A B x f s) (h3 : @IN B x t) (h4 : term37 A B f s t) : (term61 A B s f x g) = term6.
Proof. exact (EQ_MP (@lem7160784 A B g x f s t h1 h2 h3 h4) (@lem7159486 A B x f s h2)). Qed.
Lemma lem7160786 {A B : Type'} (g : A -> real) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term76 A B x f s) (h3 : @IN B x t) (h4 : term37 A B f s t) : (@IN B x t) = ((term61 A B s f x g) = term6).
Proof. exact (prop_ext (fun h5 : @IN B x t => @lem7160785 A B g x f s t h1 h2 h3 h4) (fun h5 : (term61 A B s f x g) = term6 => @lem7159487 B x t h3)). Qed.
Lemma lem7160787 {A B : Type'} (g : A -> real) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term76 A B x f s) (h3 : @IN B x t) (h4 : term37 A B f s t) : (term61 A B s f x g) = term6.
Proof. exact (EQ_MP (@lem7160786 A B g x f s t h1 h2 h3 h4) (@lem7159487 B x t h3)). Qed.
Lemma lem7160788 {A B : Type'} (g : A -> real) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term75 A B t x f s) (h3 : @IN B x t) (h4 : term37 A B f s t) : (term76 A B x f s) = ((term61 A B s f x g) = term6).
Proof. exact (prop_ext (fun h5 : term76 A B x f s => @lem7160787 A B g x f s t h1 h5 h3 h4) (fun h5 : (term61 A B s f x g) = term6 => @lem7160782 A B t x f s h2)). Qed.
Lemma lem7160789 {A B : Type'} (g : A -> real) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term75 A B t x f s) (h3 : @IN B x t) (h4 : term37 A B f s t) : (term61 A B s f x g) = term6.
Proof. exact (EQ_MP (@lem7160788 A B g x f s t h1 h2 h3 h4) (@lem7160782 A B t x f s h2)). Qed.
Lemma lem7160790 {A B : Type'} (g : A -> real) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term75 A B t x f s) (h3 : term37 A B f s t) : (@IN B x t) = ((term61 A B s f x g) = term6).
Proof. exact (prop_ext (fun h4 : @IN B x t => @lem7160789 A B g x f s t h1 h2 h4 h3) (fun h4 : (term61 A B s f x g) = term6 => @lem7160783 A B t x f s h2)). Qed.
Lemma lem7160791 {A B : Type'} (g : A -> real) (x : B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term75 A B t x f s) (h3 : term37 A B f s t) : (term61 A B s f x g) = term6.
Proof. exact (EQ_MP (@lem7160790 A B g x f s t h1 h2 h3) (@lem7160783 A B t x f s h2)). Qed.
Lemma lem7160792 {A B : Type'} (x : B) (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term37 A B f s t) : term68 A B t s f x g.
Proof. exact (fun h0 : term75 A B t x f s => @lem7160791 A B g x f s t h1 h0 h2). Qed.
Lemma lem7160797 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term37 A B f s t) : term72 A B t s f g.
Proof. exact (fun x : B => @lem7160792 A B x g f s t h1 h2). Qed.
Lemma lem7160798 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term37 A B f s t) : term73 A B t s f g.
Proof. exact (EQ_MP (@lem7159484 A B g f s t h2) (@lem7160797 A B g f s t h1 h2)). Qed.
Lemma lem7160799 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term37 A B f s t) : (term43 A B t s f g) = (term39 A B s f g).
Proof. exact (@lem7159402 A B t s f g (@lem7160798 A B g f s t h1 h2)). Qed.
Lemma lem7160800 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : (@sum A s g) = (term39 A B s f g)) (h3 : term37 A B f s t) : (term43 A B t s f g) = (@sum A s g).
Proof. exact (EQ_MP (@lem7159384 A B t s f g h2) (@lem7160799 A B g f s t h1 h3)). Qed.
Lemma lem7160801 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term37 A B f s t) : term45 A B t f s g.
Proof. exact (fun h0 : (@sum A s g) = (term39 A B s f g) => @lem7160800 A B g f s t h1 h0 h2). Qed.
Lemma lem7160802 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term37 A B f s t) : term44 A B t f s g.
Proof. exact (EQ_MP (@lem7159370 A B t f g s h1) (@lem7160801 A B g f s t h1 h2)). Qed.
Lemma lem7160803 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term37 A B f s t) : (term43 A B t s f g) = (@sum A s g).
Proof. exact (@lem7160802 A B g f s t h1 h2 (@lem7159310 A B s f g)). Qed.
Lemma lem7160804 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term36 A B f s t) : term37 A B f s t.
Proof. exact (proj2 (@lem7159311 A B f s t h1)). Qed.
Lemma lem7160805 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term36 A B f s t) : @FINITE A s.
Proof. exact (proj1 (@lem7159311 A B f s t h1)). Qed.
Lemma lem7160806 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term37 A B f s t) : (term37 A B f s t) = ((term43 A B t s f g) = (@sum A s g)).
Proof. exact (prop_ext (fun h3 : term37 A B f s t => @lem7160803 A B g f s t h1 h2) (fun h3 : (term43 A B t s f g) = (@sum A s g) => @lem7159312 A B f s t h2)). Qed.
Lemma lem7160807 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term37 A B f s t) : (term43 A B t s f g) = (@sum A s g).
Proof. exact (EQ_MP (@lem7160806 A B g f s t h1 h2) (@lem7159312 A B f s t h2)). Qed.
Lemma lem7160808 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term37 A B f s t) : (@FINITE A s) = ((term43 A B t s f g) = (@sum A s g)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7160807 A B g f s t h1 h2) (fun h3 : (term43 A B t s f g) = (@sum A s g) => @lem7159313 A s h1)). Qed.
Lemma lem7160809 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term37 A B f s t) : (term43 A B t s f g) = (@sum A s g).
Proof. exact (EQ_MP (@lem7160808 A B g f s t h1 h2) (@lem7159313 A s h1)). Qed.
Lemma lem7160810 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : (term37 A B f s t) = ((term43 A B t s f g) = (@sum A s g)).
Proof. exact (prop_ext (fun h3 : term37 A B f s t => @lem7160809 A B g f s t h1 h3) (fun h3 : (term43 A B t s f g) = (@sum A s g) => @lem7160804 A B f s t h2)). Qed.
Lemma lem7160811 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term36 A B f s t) : (term43 A B t s f g) = (@sum A s g).
Proof. exact (EQ_MP (@lem7160810 A B g f s t h1 h2) (@lem7160804 A B f s t h2)). Qed.
Lemma lem7160812 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term36 A B f s t) : (@FINITE A s) = ((term43 A B t s f g) = (@sum A s g)).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7160811 A B g f s t h2 h1) (fun h2 : (term43 A B t s f g) = (@sum A s g) => @lem7160805 A B f s t h1)). Qed.
Lemma lem7160813 {A B : Type'} (g : A -> real) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term36 A B f s t) : (term43 A B t s f g) = (@sum A s g).
Proof. exact (EQ_MP (@lem7160812 A B g f s t h1) (@lem7160805 A B f s t h1)). Qed.
Lemma lem7160814 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (g : A -> real) : term238 A B t f s g.
Proof. exact (fun h0 : term36 A B f s t => @lem7160813 A B g f s t h0). Qed.
Lemma lem7160819 {A B : Type'} (f : A -> B) (s : A -> Prop) (g : A -> real) : term239 A B f s g.
Proof. exact (fun t : B -> Prop => @lem7160814 A B t f s g). Qed.
Lemma lem7160824 {A B : Type'} (f : A -> B) (g : A -> real) : term240 A B f g.
Proof. exact (fun s : A -> Prop => @lem7160819 A B f s g). Qed.
Lemma lem7160829 {A B : Type'} (f : A -> B) : term241 A B f.
Proof. exact (fun g : A -> real => @lem7160824 A B f g). Qed.
Lemma lem7160834 {A B : Type'} : term242 A B.
Proof. exact (fun f : A -> B => @lem7160829 A B f). Qed.
