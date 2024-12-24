Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_EQ_SUPERSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SUM_EQ_spec.
Require Import SUM_SUPERSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem7153074 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7153075 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7153076 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7153075 t1) (@lem7153074 t1)). Qed.
Lemma lem7153077 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7153076 t1 t2). Qed.
Lemma lem7153078 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7153079 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7153078 t1 t2) (@lem7153077 t1 t2)). Qed.
Lemma lem7153080 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7153079 t1 t2 t3). Qed.
Lemma lem7153081 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7153082 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7153081 t1 t2 t3) (@lem7153080 t1 t2 t3)). Qed.
Lemma lem7153083 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7153082 t1 t2 t3)). Qed.
Lemma lem7153085 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7153086 {A : Type'} (g : A -> real) : (term8 A g) = (term9 A g).
Proof. exact (@lem7153085 (term8 A g)). Qed.
Lemma lem7153087 {A : Type'} (g : A -> real) : (term9 A g) = (term8 A g).
Proof. exact (SYM (@lem7153086 A g)). Qed.
Lemma lem7153088 {A : Type'} (g : A -> real) (h1 : term10 A g) : term10 A g.
Proof. exact (h1). Qed.
Lemma lem7153089 {A : Type'} : term11 A.
Proof. exact (@lem7124972 A). Qed.
Lemma lem7153092 {A : Type'} : term12 A.
Proof. exact (@lem7081239 A). Qed.
Lemma lem7153096 {_132349 A : Type'} (g : A -> real) (h1 : term13 _132349 A g) : term13 _132349 A g.
Proof. exact (h1). Qed.
Lemma lem7153097 {_132349 A : Type'} (g : A -> real) : term14 _132349 A g.
Proof. exact (fun h0 : term13 _132349 A g => @lem7153096 _132349 A g h0). Qed.
Lemma lem7153098 {_132349 A : Type'} (g : A -> real) (h1 : term14 _132349 A g) : term14 _132349 A g.
Proof. exact (h1). Qed.
Lemma lem7153099 {_132349 A : Type'} (g : A -> real) (h1 : term13 _132349 A g) : term13 _132349 A g.
Proof. exact (h1). Qed.
Lemma lem7153100 {_132349 A : Type'} (g : A -> real) (h1 : term13 _132349 A g) (h2 : term14 _132349 A g) : term13 _132349 A g.
Proof. exact (@lem7153098 _132349 A g h2 (@lem7153099 _132349 A g h1)). Qed.
Lemma lem7153101 {_132349 A : Type'} (g : A -> real) (h1 : term13 _132349 A g) : term15 _132349 A g.
Proof. exact (fun h0 : term14 _132349 A g => @lem7153100 _132349 A g h1 h0). Qed.
Lemma lem7153102 {_132349 A : Type'} (g : A -> real) (h1 : term14 _132349 A g) : term14 _132349 A g.
Proof. exact (h1). Qed.
Lemma lem7153103 {_132349 A : Type'} (g : A -> real) (h1 : term13 _132349 A g) (h2 : term14 _132349 A g) : term13 _132349 A g.
Proof. exact (@lem7153101 _132349 A g h1 (@lem7153102 _132349 A g h2)). Qed.
Lemma lem7153104 {_132349 A : Type'} (g : A -> real) (h1 : term14 _132349 A g) : term14 _132349 A g.
Proof. exact (fun h0 : term13 _132349 A g => @lem7153103 _132349 A g h0 h1). Qed.
Lemma lem7153105 {_132349 A : Type'} (g : A -> real) : term16 _132349 A g.
Proof. exact (fun h0 : term14 _132349 A g => @lem7153104 _132349 A g h0). Qed.
Lemma lem7153108 {_132349 A : Type'} (g : A -> real) : term14 _132349 A g.
Proof. exact (@lem7153105 _132349 A g (@lem7153097 _132349 A g)). Qed.
Lemma lem7153109 {_132349 A : Type'} (g : A -> real) : term14 _132349 A g.
Proof. exact (@lem7153108 _132349 A g). Qed.
Lemma lem7153195 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7153196 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem7153195 (term11 A)). Qed.
Lemma lem7153221 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem7153222 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem7153221 A) (@lem7153196 A)). Qed.
Lemma lem7153225 {_132349 : Type'} : (term19 _132349) = (term19 _132349).
Proof. exact (eq_refl (term19 _132349)). Qed.
Lemma lem7153226 {_132349 A : Type'} : (term22 _132349 A) = (term23 _132349 A).
Proof. exact (MK_COMB (@lem7153225 _132349) (@lem7153222 A)). Qed.
Lemma lem7153229 {A : Type'} (g : A -> real) : (term24 A g) = (term24 A g).
Proof. exact (eq_refl (term24 A g)). Qed.
Lemma lem7153230 {_132349 A : Type'} (g : A -> real) : (term13 _132349 A g) = (term25 _132349 A g).
Proof. exact (MK_COMB (@lem7153229 A g) (@lem7153226 _132349 A)). Qed.
Lemma lem7153233 {_132349 A : Type'} : (term26 _132349 A) = (term27 _132349 A).
Proof. exact (fun_ext (fun g : A -> real => @lem7153230 _132349 A g)). Qed.
Lemma lem7153234 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7153243 {_132349 A : Type'} : (term28 _132349 A) = (term29 _132349 A).
Proof. exact (MK_COMB (@lem7153234 A) (@lem7153233 _132349 A)). Qed.
Lemma lem7153244 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((@sum A v f) = (@sum A u f)) = ((@sum A v f) = (@sum A u f)).
Proof. exact (eq_refl ((@sum A v f) = (@sum A u f))). Qed.
Lemma lem7153255 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term30 A v u f x) = (term30 A v u f x).
Proof. exact (eq_refl (term30 A v u f x)). Qed.
Lemma lem7153256 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term31 A v u f) = (term31 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7153255 A v u f x)). Qed.
Lemma lem7153257 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7153258 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term32 A v u f) = (term32 A v u f).
Proof. exact (MK_COMB (@lem7153257 A) (@lem7153256 A v u f)). Qed.
Lemma lem7153261 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term33 A u v) = (term33 A u v).
Proof. exact (eq_refl (term33 A u v)). Qed.
Lemma lem7153262 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term34 A v u f) = (term34 A v u f).
Proof. exact (MK_COMB (@lem7153261 A u v) (@lem7153258 A v u f)). Qed.
Lemma lem7153263 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7153264 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term35 A v u f) = (term35 A v u f).
Proof. exact (MK_COMB (@lem7153263) (@lem7153262 A v u f)). Qed.
Lemma lem7153265 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term36 A v u f) = (term36 A v u f).
Proof. exact (MK_COMB (@lem7153264 A v u f) (@lem7153244 A v u f)). Qed.
Lemma lem7153266 {A : Type'} (u : A -> Prop) (f : A -> real) : (term37 A u f) = (term37 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7153265 A v u f)). Qed.
Lemma lem7153267 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7153268 {A : Type'} (u : A -> Prop) (f : A -> real) : (term38 A u f) = (term38 A u f).
Proof. exact (MK_COMB (@lem7153267 A) (@lem7153266 A u f)). Qed.
Lemma lem7153269 {A : Type'} (f : A -> real) : (term39 A f) = (term39 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7153268 A u f)). Qed.
Lemma lem7153270 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7153271 {A : Type'} (f : A -> real) : (term40 A f) = (term40 A f).
Proof. exact (MK_COMB (@lem7153270 A) (@lem7153269 A f)). Qed.
Lemma lem7153272 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7153271 A f)). Qed.
Lemma lem7153273 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7153274 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem7153273 A) (@lem7153272 A)). Qed.
Lemma lem7153275 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7153276 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem7153275) (@lem7153274 A)). Qed.
Lemma lem7153277 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : ((@sum A s f) = (@sum A s g)) = ((@sum A s f) = (@sum A s g)).
Proof. exact (eq_refl ((@sum A s f) = (@sum A s g))). Qed.
Lemma lem7153282 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term42 A s f g x) = (term42 A s f g x).
Proof. exact (eq_refl (term42 A s f g x)). Qed.
Lemma lem7153283 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term43 A s f g) = (term43 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7153282 A s f g x)). Qed.
Lemma lem7153284 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7153285 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term44 A s f g) = (term44 A s f g).
Proof. exact (MK_COMB (@lem7153284 A) (@lem7153283 A s f g)). Qed.
Lemma lem7153286 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7153287 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term45 A s f g) = (term45 A s f g).
Proof. exact (MK_COMB (@lem7153286) (@lem7153285 A s f g)). Qed.
Lemma lem7153288 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term46 A f s g) = (term46 A f s g).
Proof. exact (MK_COMB (@lem7153287 A s f g) (@lem7153277 A f s g)). Qed.
Lemma lem7153289 {A : Type'} (f : A -> real) (g : A -> real) : (term47 A f g) = (term47 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7153288 A f s g)). Qed.
Lemma lem7153290 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7153291 {A : Type'} (f : A -> real) (g : A -> real) : (term48 A f g) = (term48 A f g).
Proof. exact (MK_COMB (@lem7153290 A) (@lem7153289 A f g)). Qed.
Lemma lem7153292 {A : Type'} (f : A -> real) : (term49 A f) = (term49 A f).
Proof. exact (fun_ext (fun g : A -> real => @lem7153291 A f g)). Qed.
Lemma lem7153293 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7153294 {A : Type'} (f : A -> real) : (term50 A f) = (term50 A f).
Proof. exact (MK_COMB (@lem7153293 A) (@lem7153292 A f)). Qed.
Lemma lem7153295 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7153294 A f)). Qed.
Lemma lem7153296 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7153297 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem7153296 A) (@lem7153295 A)). Qed.
Lemma lem7153298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7153299 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem7153298) (@lem7153297 A)). Qed.
Lemma lem7153300 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem7153299 A) (@lem7153276 A)). Qed.
Lemma lem7153301 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : ((@sum _132349 s f) = (@sum _132349 s g)) = ((@sum _132349 s f) = (@sum _132349 s g)).
Proof. exact (eq_refl ((@sum _132349 s f) = (@sum _132349 s g))). Qed.
Lemma lem7153306 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term42 _132349 s f g x) = (term42 _132349 s f g x).
Proof. exact (eq_refl (term42 _132349 s f g x)). Qed.
Lemma lem7153307 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term43 _132349 s f g) = (term43 _132349 s f g).
Proof. exact (fun_ext (fun x : _132349 => @lem7153306 _132349 s f g x)). Qed.
Lemma lem7153308 {_132349 : Type'} : (@all _132349) = (@all _132349).
Proof. exact (eq_refl (@all _132349)). Qed.
Lemma lem7153309 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term44 _132349 s f g) = (term44 _132349 s f g).
Proof. exact (MK_COMB (@lem7153308 _132349) (@lem7153307 _132349 s f g)). Qed.
Lemma lem7153310 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7153311 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term45 _132349 s f g) = (term45 _132349 s f g).
Proof. exact (MK_COMB (@lem7153310) (@lem7153309 _132349 s f g)). Qed.
Lemma lem7153312 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term46 _132349 f s g) = (term46 _132349 f s g).
Proof. exact (MK_COMB (@lem7153311 _132349 s f g) (@lem7153301 _132349 f s g)). Qed.
Lemma lem7153313 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term47 _132349 f g) = (term47 _132349 f g).
Proof. exact (fun_ext (fun s : _132349 -> Prop => @lem7153312 _132349 f s g)). Qed.
Lemma lem7153314 {_132349 : Type'} : (@all (_132349 -> Prop)) = (@all (_132349 -> Prop)).
Proof. exact (eq_refl (@all (_132349 -> Prop))). Qed.
Lemma lem7153315 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term48 _132349 f g) = (term48 _132349 f g).
Proof. exact (MK_COMB (@lem7153314 _132349) (@lem7153313 _132349 f g)). Qed.
Lemma lem7153316 {_132349 : Type'} (f : _132349 -> real) : (term49 _132349 f) = (term49 _132349 f).
Proof. exact (fun_ext (fun g : _132349 -> real => @lem7153315 _132349 f g)). Qed.
Lemma lem7153317 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7153318 {_132349 : Type'} (f : _132349 -> real) : (term50 _132349 f) = (term50 _132349 f).
Proof. exact (MK_COMB (@lem7153317 _132349) (@lem7153316 _132349 f)). Qed.
Lemma lem7153319 {_132349 : Type'} : (term51 _132349) = (term51 _132349).
Proof. exact (fun_ext (fun f : _132349 -> real => @lem7153318 _132349 f)). Qed.
Lemma lem7153320 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7153321 {_132349 : Type'} : (term12 _132349) = (term12 _132349).
Proof. exact (MK_COMB (@lem7153320 _132349) (@lem7153319 _132349)). Qed.
Lemma lem7153322 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7153323 {_132349 : Type'} : (term19 _132349) = (term19 _132349).
Proof. exact (MK_COMB (@lem7153322) (@lem7153321 _132349)). Qed.
Lemma lem7153324 {_132349 A : Type'} : (term23 _132349 A) = (term23 _132349 A).
Proof. exact (MK_COMB (@lem7153323 _132349) (@lem7153300 A)). Qed.
Lemma lem7153325 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : ((@sum A s f) = (@sum A t g)) = ((@sum A s f) = (@sum A t g)).
Proof. exact (eq_refl ((@sum A s f) = (@sum A t g))). Qed.
Lemma lem7153336 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (x : A) : (term30 A s t f x) = (term30 A s t f x).
Proof. exact (eq_refl (term30 A s t f x)). Qed.
Lemma lem7153337 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term31 A s t f) = (term31 A s t f).
Proof. exact (fun_ext (fun x : A => @lem7153336 A s t f x)). Qed.
Lemma lem7153338 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7153339 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term32 A s t f) = (term32 A s t f).
Proof. exact (MK_COMB (@lem7153338 A) (@lem7153337 A s t f)). Qed.
Lemma lem7153344 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term42 A t f g x) = (term42 A t f g x).
Proof. exact (eq_refl (term42 A t f g x)). Qed.
Lemma lem7153345 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) : (term43 A t f g) = (term43 A t f g).
Proof. exact (fun_ext (fun x : A => @lem7153344 A t f g x)). Qed.
Lemma lem7153346 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7153347 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) : (term44 A t f g) = (term44 A t f g).
Proof. exact (MK_COMB (@lem7153346 A) (@lem7153345 A t f g)). Qed.
Lemma lem7153348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7153349 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) : (term52 A t f g) = (term52 A t f g).
Proof. exact (MK_COMB (@lem7153348) (@lem7153347 A t f g)). Qed.
Lemma lem7153350 {A : Type'} (g : A -> real) (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term53 A g s t f) = (term53 A g s t f).
Proof. exact (MK_COMB (@lem7153349 A t f g) (@lem7153339 A s t f)). Qed.
Lemma lem7153353 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term33 A t s) = (term33 A t s).
Proof. exact (eq_refl (term33 A t s)). Qed.
Lemma lem7153354 {A : Type'} (g : A -> real) (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term54 A g s t f) = (term54 A g s t f).
Proof. exact (MK_COMB (@lem7153353 A t s) (@lem7153350 A g s t f)). Qed.
Lemma lem7153357 {A : Type'} (t : A -> Prop) : (term55 A t) = (term55 A t).
Proof. exact (eq_refl (term55 A t)). Qed.
Lemma lem7153358 {A : Type'} (g : A -> real) (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term56 A g s t f) = (term56 A g s t f).
Proof. exact (MK_COMB (@lem7153357 A t) (@lem7153354 A g s t f)). Qed.
Lemma lem7153359 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7153360 {A : Type'} (g : A -> real) (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term57 A g s t f) = (term57 A g s t f).
Proof. exact (MK_COMB (@lem7153359) (@lem7153358 A g s t f)). Qed.
Lemma lem7153361 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : (term58 A s f t g) = (term58 A s f t g).
Proof. exact (MK_COMB (@lem7153360 A g s t f) (@lem7153325 A s f t g)). Qed.
Lemma lem7153362 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term59 A s f g) = (term59 A s f g).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7153361 A s f t g)). Qed.
Lemma lem7153363 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7153364 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term60 A s f g) = (term60 A s f g).
Proof. exact (MK_COMB (@lem7153363 A) (@lem7153362 A s f g)). Qed.
Lemma lem7153365 {A : Type'} (f : A -> real) (g : A -> real) : (term61 A f g) = (term61 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7153364 A s f g)). Qed.
Lemma lem7153366 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7153367 {A : Type'} (f : A -> real) (g : A -> real) : (term62 A f g) = (term62 A f g).
Proof. exact (MK_COMB (@lem7153366 A) (@lem7153365 A f g)). Qed.
Lemma lem7153368 {A : Type'} (g : A -> real) : (term63 A g) = (term63 A g).
Proof. exact (fun_ext (fun f : A -> real => @lem7153367 A f g)). Qed.
Lemma lem7153369 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7153370 {A : Type'} (g : A -> real) : (term8 A g) = (term8 A g).
Proof. exact (MK_COMB (@lem7153369 A) (@lem7153368 A g)). Qed.
Lemma lem7153371 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7153372 {A : Type'} (g : A -> real) : (term10 A g) = (term10 A g).
Proof. exact (MK_COMB (@lem7153371) (@lem7153370 A g)). Qed.
Lemma lem7153373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7153374 {A : Type'} (g : A -> real) : (term24 A g) = (term24 A g).
Proof. exact (MK_COMB (@lem7153373) (@lem7153372 A g)). Qed.
Lemma lem7153375 {_132349 A : Type'} (g : A -> real) : (term25 _132349 A g) = (term25 _132349 A g).
Proof. exact (MK_COMB (@lem7153374 A g) (@lem7153324 _132349 A)). Qed.
Lemma lem7153376 {_132349 A : Type'} : (term27 _132349 A) = (term27 _132349 A).
Proof. exact (fun_ext (fun g : A -> real => @lem7153375 _132349 A g)). Qed.
Lemma lem7153377 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7153378 {_132349 A : Type'} : (term29 _132349 A) = (term29 _132349 A).
Proof. exact (MK_COMB (@lem7153377 A) (@lem7153376 _132349 A)). Qed.
Lemma lem7153525 {_132349 A : Type'} : (term28 _132349 A) = (term29 _132349 A).
Proof. exact (TRANS (@lem7153243 _132349 A) (@lem7153378 _132349 A)). Qed.
Lemma lem7153526 {_132349 A : Type'} : (term29 _132349 A) = (term28 _132349 A).
Proof. exact (SYM (@lem7153525 _132349 A)). Qed.
Lemma lem7153527 {A : Type'} (g : A -> real) (h1 : term10 A g) : term10 A g.
Proof. exact (h1). Qed.
Lemma lem7153528 {_132349 : Type'} (h1 : term12 _132349) : term12 _132349.
Proof. exact (h1). Qed.
Lemma lem7153529 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem7153530 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem7153539 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term42 A t f g x) = (term64 A t f g x).
Proof. exact (@lem17265 (@IN A x t) ((f x) = (g x))). Qed.
Lemma lem7153540 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) : (term43 A t f g) = (term65 A t f g).
Proof. exact (fun_ext (fun x : A => @lem7153539 A t f g x)). Qed.
Lemma lem7153541 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7153542 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) : (term44 A t f g) = (term66 A t f g).
Proof. exact (MK_COMB (@lem7153541 A) (@lem7153540 A t f g)). Qed.
Lemma lem7153546 {A : Type'} (x : A) (t : A -> Prop) : (term67 A x t) = (@IN A x t).
Proof. exact (@lem16933 (@IN A x t)). Qed.
Lemma lem7153548 {A : Type'} (x : A) (s : A -> Prop) : (term68 A x s) = (term68 A x s).
Proof. exact (eq_refl (term68 A x s)). Qed.
Lemma lem7153549 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term69 A s x t) = (term70 A s x t).
Proof. exact (MK_COMB (@lem7153548 A x s) (@lem7153546 A x t)). Qed.
Lemma lem7153550 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term71 A s x t) = (term69 A s x t).
Proof. exact (@lem17045 (@IN A x s) (term72 A x t)). Qed.
Lemma lem7153551 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term71 A s x t) = (term70 A s x t).
Proof. exact (TRANS (@lem7153550 A s x t) (@lem7153549 A s x t)). Qed.
Lemma lem7153552 {A : Type'} (f : A -> real) (x : A) : ((f x) = term73) = ((f x) = term73).
Proof. exact (eq_refl ((f x) = term73)). Qed.
Lemma lem7153553 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7153554 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term74 A s x t) = (term75 A s x t).
Proof. exact (MK_COMB (@lem7153553) (@lem7153551 A s x t)). Qed.
Lemma lem7153555 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (x : A) : (term76 A s t f x) = (term77 A s t f x).
Proof. exact (MK_COMB (@lem7153554 A s x t) (@lem7153552 A f x)). Qed.
Lemma lem7153556 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (x : A) : (term30 A s t f x) = (term76 A s t f x).
Proof. exact (@lem17265 (term78 A s x t) ((f x) = term73)). Qed.
Lemma lem7153557 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (x : A) : (term30 A s t f x) = (term77 A s t f x).
Proof. exact (TRANS (@lem7153556 A s t f x) (@lem7153555 A s t f x)). Qed.
Lemma lem7153558 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term31 A s t f) = (term79 A s t f).
Proof. exact (fun_ext (fun x : A => @lem7153557 A s t f x)). Qed.
Lemma lem7153559 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7153560 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term32 A s t f) = (term80 A s t f).
Proof. exact (MK_COMB (@lem7153559 A) (@lem7153558 A s t f)). Qed.
Lemma lem7153561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7153562 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) : (term52 A t f g) = (term81 A t f g).
Proof. exact (MK_COMB (@lem7153561) (@lem7153542 A t f g)). Qed.
Lemma lem7153563 {A : Type'} (g : A -> real) (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term53 A g s t f) = (term82 A g s t f).
Proof. exact (MK_COMB (@lem7153562 A t f g) (@lem7153560 A s t f)). Qed.
Lemma lem7153565 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term33 A t s) = (term33 A t s).
Proof. exact (eq_refl (term33 A t s)). Qed.
Lemma lem7153566 {A : Type'} (g : A -> real) (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term54 A g s t f) = (term83 A g s t f).
Proof. exact (MK_COMB (@lem7153565 A t s) (@lem7153563 A g s t f)). Qed.
Lemma lem7153568 {A : Type'} (t : A -> Prop) : (term55 A t) = (term55 A t).
Proof. exact (eq_refl (term55 A t)). Qed.
Lemma lem7153569 {A : Type'} (g : A -> real) (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term56 A g s t f) = (term84 A g s t f).
Proof. exact (MK_COMB (@lem7153568 A t) (@lem7153566 A g s t f)). Qed.
Lemma lem7153570 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : (term85 A s f t g) = (term85 A s f t g).
Proof. exact (eq_refl (term85 A s f t g)). Qed.
Lemma lem7153571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7153572 {A : Type'} (g : A -> real) (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term86 A g s t f) = (term87 A g s t f).
Proof. exact (MK_COMB (@lem7153571) (@lem7153569 A g s t f)). Qed.
Lemma lem7153573 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : (term88 A s f t g) = (term89 A s f t g).
Proof. exact (MK_COMB (@lem7153572 A g s t f) (@lem7153570 A s f t g)). Qed.
Lemma lem7153574 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : (term90 A s f t g) = (term88 A s f t g).
Proof. exact (@lem17362 (term56 A g s t f) ((@sum A s f) = (@sum A t g))). Qed.
Lemma lem7153575 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : (term90 A s f t g) = (term89 A s f t g).
Proof. exact (TRANS (@lem7153574 A s f t g) (@lem7153573 A s f t g)). Qed.
Lemma lem7153576 {A : Type'} (P : type686 A) : (term91 A P) = (term92 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem7153577 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term93 A s f g) = (term94 A s f g).
Proof. exact (@lem7153576 A (term59 A s f g)). Qed.
Lemma lem7153578 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : (term95 A s f g t) = (term58 A s f t g).
Proof. exact (eq_refl (term95 A s f g t)). Qed.
Lemma lem7153579 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7153580 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : (term96 A s f g t) = (term90 A s f t g).
Proof. exact (MK_COMB (@lem7153579) (@lem7153578 A s f t g)). Qed.
Lemma lem7153581 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : (term96 A s f g t) = (term89 A s f t g).
Proof. exact (TRANS (@lem7153580 A s f t g) (@lem7153575 A s f t g)). Qed.
Lemma lem7153582 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term97 A s f g) = (term98 A s f g).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7153581 A s f t g)). Qed.
Lemma lem7153583 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7153584 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term94 A s f g) = (term99 A s f g).
Proof. exact (MK_COMB (@lem7153583 A) (@lem7153582 A s f g)). Qed.
Lemma lem7153585 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term93 A s f g) = (term99 A s f g).
Proof. exact (TRANS (@lem7153577 A s f g) (@lem7153584 A s f g)). Qed.
Lemma lem7153586 {A : Type'} (P : type686 A) : (term91 A P) = (term92 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem7153587 {A : Type'} (f : A -> real) (g : A -> real) : (term100 A f g) = (term101 A f g).
Proof. exact (@lem7153586 A (term61 A f g)). Qed.
Lemma lem7153588 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term102 A f g s) = (term60 A s f g).
Proof. exact (eq_refl (term102 A f g s)). Qed.
Lemma lem7153589 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7153590 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term103 A f g s) = (term93 A s f g).
Proof. exact (MK_COMB (@lem7153589) (@lem7153588 A s f g)). Qed.
Lemma lem7153591 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term103 A f g s) = (term99 A s f g).
Proof. exact (TRANS (@lem7153590 A s f g) (@lem7153585 A s f g)). Qed.
Lemma lem7153592 {A : Type'} (f : A -> real) (g : A -> real) : (term104 A f g) = (term105 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7153591 A s f g)). Qed.
Lemma lem7153593 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7153594 {A : Type'} (f : A -> real) (g : A -> real) : (term101 A f g) = (term106 A f g).
Proof. exact (MK_COMB (@lem7153593 A) (@lem7153592 A f g)). Qed.
Lemma lem7153595 {A : Type'} (f : A -> real) (g : A -> real) : (term100 A f g) = (term106 A f g).
Proof. exact (TRANS (@lem7153587 A f g) (@lem7153594 A f g)). Qed.
Lemma lem7153596 {A : Type'} (P : type716 A) : (term107 A P) = (term108 A P).
Proof. exact (@lem18392 (A -> real) P). Qed.
Lemma lem7153597 {A : Type'} (g : A -> real) : (term10 A g) = (term109 A g).
Proof. exact (@lem7153596 A (term63 A g)). Qed.
Lemma lem7153598 {A : Type'} (f : A -> real) (g : A -> real) : (term110 A g f) = (term62 A f g).
Proof. exact (eq_refl (term110 A g f)). Qed.
Lemma lem7153599 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7153600 {A : Type'} (f : A -> real) (g : A -> real) : (term111 A g f) = (term100 A f g).
Proof. exact (MK_COMB (@lem7153599) (@lem7153598 A f g)). Qed.
Lemma lem7153601 {A : Type'} (f : A -> real) (g : A -> real) : (term111 A g f) = (term106 A f g).
Proof. exact (TRANS (@lem7153600 A f g) (@lem7153595 A f g)). Qed.
Lemma lem7153602 {A : Type'} (g : A -> real) : (term112 A g) = (term113 A g).
Proof. exact (fun_ext (fun f : A -> real => @lem7153601 A f g)). Qed.
Lemma lem7153603 {A : Type'} : (@ex (A -> real)) = (@ex (A -> real)).
Proof. exact (eq_refl (@ex (A -> real))). Qed.
Lemma lem7153604 {A : Type'} (g : A -> real) : (term109 A g) = (term114 A g).
Proof. exact (MK_COMB (@lem7153603 A) (@lem7153602 A g)). Qed.
Lemma lem7153761 {A : Type'} (g : A -> real) : (term10 A g) = (term114 A g).
Proof. exact (TRANS (@lem7153597 A g) (@lem7153604 A g)). Qed.
Lemma lem7153762 {A : Type'} (g : A -> real) (h1 : term10 A g) : term114 A g.
Proof. exact (EQ_MP (@lem7153761 A g) (@lem7153527 A g h1)). Qed.
Lemma lem7153769 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term115 _132349 s f g x) = (term116 _132349 s f g x).
Proof. exact (@lem17362 (@IN _132349 x s) ((f x) = (g x))). Qed.
Lemma lem7153770 {_132349 : Type'} (P : _132349 -> Prop) : (term117 _132349 P) = (term118 _132349 P).
Proof. exact (@lem18392 _132349 P). Qed.
Lemma lem7153771 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term119 _132349 s f g) = (term120 _132349 s f g).
Proof. exact (@lem7153770 _132349 (term43 _132349 s f g)). Qed.
Lemma lem7153772 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term121 _132349 s f g x) = (term42 _132349 s f g x).
Proof. exact (eq_refl (term121 _132349 s f g x)). Qed.
Lemma lem7153773 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7153774 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term122 _132349 s f g x) = (term115 _132349 s f g x).
Proof. exact (MK_COMB (@lem7153773) (@lem7153772 _132349 s f g x)). Qed.
Lemma lem7153775 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term122 _132349 s f g x) = (term116 _132349 s f g x).
Proof. exact (TRANS (@lem7153774 _132349 s f g x) (@lem7153769 _132349 s f g x)). Qed.
Lemma lem7153776 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term123 _132349 s f g) = (term124 _132349 s f g).
Proof. exact (fun_ext (fun x : _132349 => @lem7153775 _132349 s f g x)). Qed.
Lemma lem7153777 {_132349 : Type'} : (@ex _132349) = (@ex _132349).
Proof. exact (eq_refl (@ex _132349)). Qed.
Lemma lem7153778 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term120 _132349 s f g) = (term125 _132349 s f g).
Proof. exact (MK_COMB (@lem7153777 _132349) (@lem7153776 _132349 s f g)). Qed.
Lemma lem7153779 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term119 _132349 s f g) = (term125 _132349 s f g).
Proof. exact (TRANS (@lem7153771 _132349 s f g) (@lem7153778 _132349 s f g)). Qed.
Lemma lem7153780 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : ((@sum _132349 s f) = (@sum _132349 s g)) = ((@sum _132349 s f) = (@sum _132349 s g)).
Proof. exact (eq_refl ((@sum _132349 s f) = (@sum _132349 s g))). Qed.
Lemma lem7153781 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7153782 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term126 _132349 s f g) = (term127 _132349 s f g).
Proof. exact (MK_COMB (@lem7153781) (@lem7153779 _132349 s f g)). Qed.
Lemma lem7153783 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term128 _132349 f s g) = (term129 _132349 f s g).
Proof. exact (MK_COMB (@lem7153782 _132349 s f g) (@lem7153780 _132349 f s g)). Qed.
Lemma lem7153784 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term46 _132349 f s g) = (term128 _132349 f s g).
Proof. exact (@lem17265 (term44 _132349 s f g) ((@sum _132349 s f) = (@sum _132349 s g))). Qed.
Lemma lem7153785 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term46 _132349 f s g) = (term129 _132349 f s g).
Proof. exact (TRANS (@lem7153784 _132349 f s g) (@lem7153783 _132349 f s g)). Qed.
Lemma lem7153786 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term47 _132349 f g) = (term130 _132349 f g).
Proof. exact (fun_ext (fun s : _132349 -> Prop => @lem7153785 _132349 f s g)). Qed.
Lemma lem7153787 {_132349 : Type'} : (@all (_132349 -> Prop)) = (@all (_132349 -> Prop)).
Proof. exact (eq_refl (@all (_132349 -> Prop))). Qed.
Lemma lem7153788 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term48 _132349 f g) = (term131 _132349 f g).
Proof. exact (MK_COMB (@lem7153787 _132349) (@lem7153786 _132349 f g)). Qed.
Lemma lem7153789 {_132349 : Type'} (f : _132349 -> real) : (term49 _132349 f) = (term132 _132349 f).
Proof. exact (fun_ext (fun g : _132349 -> real => @lem7153788 _132349 f g)). Qed.
Lemma lem7153790 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7153791 {_132349 : Type'} (f : _132349 -> real) : (term50 _132349 f) = (term133 _132349 f).
Proof. exact (MK_COMB (@lem7153790 _132349) (@lem7153789 _132349 f)). Qed.
Lemma lem7153792 {_132349 : Type'} : (term51 _132349) = (term134 _132349).
Proof. exact (fun_ext (fun f : _132349 -> real => @lem7153791 _132349 f)). Qed.
Lemma lem7153793 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7153794 {_132349 : Type'} : (term12 _132349) = (term135 _132349).
Proof. exact (MK_COMB (@lem7153793 _132349) (@lem7153792 _132349)). Qed.
Lemma lem7153901 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7153902 {_132349 : Type'} (P : _132349 -> Prop) (Q : Prop) : (term136 _132349 P Q) = (term137 _132349 P Q).
Proof. exact (@lem7153901 _132349 P Q). Qed.
Lemma lem7153903 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term138 _132349 f s g) = (term139 _132349 f s g).
Proof. exact (@lem7153902 _132349 (term124 _132349 s f g) ((@sum _132349 s f) = (@sum _132349 s g))). Qed.
Lemma lem7153904 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term140 _132349 s f g x) = (term116 _132349 s f g x).
Proof. exact (eq_refl (term140 _132349 s f g x)). Qed.
Lemma lem7153905 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term141 _132349 s f g) = (term124 _132349 s f g).
Proof. exact (fun_ext (fun x : _132349 => @lem7153904 _132349 s f g x)). Qed.
Lemma lem7153906 {_132349 : Type'} : (@ex _132349) = (@ex _132349).
Proof. exact (eq_refl (@ex _132349)). Qed.
Lemma lem7153907 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term142 _132349 s f g) = (term125 _132349 s f g).
Proof. exact (MK_COMB (@lem7153906 _132349) (@lem7153905 _132349 s f g)). Qed.
Lemma lem7153908 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7153909 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) : (term143 _132349 s f g) = (term127 _132349 s f g).
Proof. exact (MK_COMB (@lem7153908) (@lem7153907 _132349 s f g)). Qed.
Lemma lem7153910 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : ((@sum _132349 s f) = (@sum _132349 s g)) = ((@sum _132349 s f) = (@sum _132349 s g)).
Proof. exact (eq_refl ((@sum _132349 s f) = (@sum _132349 s g))). Qed.
Lemma lem7153911 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term138 _132349 f s g) = (term129 _132349 f s g).
Proof. exact (MK_COMB (@lem7153909 _132349 s f g) (@lem7153910 _132349 f s g)). Qed.
Lemma lem7153912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7153913 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term144 _132349 f s g) = (term145 _132349 f s g).
Proof. exact (MK_COMB (@lem7153912) (@lem7153911 _132349 f s g)). Qed.
Lemma lem7153914 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term140 _132349 s f g x) = (term116 _132349 s f g x).
Proof. exact (eq_refl (term140 _132349 s f g x)). Qed.
Lemma lem7153915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7153916 {_132349 : Type'} (s : _132349 -> Prop) (f : _132349 -> real) (g : _132349 -> real) (x : _132349) : (term146 _132349 s f g x) = (term147 _132349 s f g x).
Proof. exact (MK_COMB (@lem7153915) (@lem7153914 _132349 s f g x)). Qed.
Lemma lem7153917 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : ((@sum _132349 s f) = (@sum _132349 s g)) = ((@sum _132349 s f) = (@sum _132349 s g)).
Proof. exact (eq_refl ((@sum _132349 s f) = (@sum _132349 s g))). Qed.
Lemma lem7153918 {_132349 : Type'} (x : _132349) (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term148 _132349 x f s g) = (term149 _132349 x f s g).
Proof. exact (MK_COMB (@lem7153916 _132349 s f g x) (@lem7153917 _132349 f s g)). Qed.
Lemma lem7153919 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term150 _132349 f s g) = (term151 _132349 f s g).
Proof. exact (fun_ext (fun x : _132349 => @lem7153918 _132349 x f s g)). Qed.
Lemma lem7153920 {_132349 : Type'} : (@ex _132349) = (@ex _132349).
Proof. exact (eq_refl (@ex _132349)). Qed.
Lemma lem7153921 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term139 _132349 f s g) = (term152 _132349 f s g).
Proof. exact (MK_COMB (@lem7153920 _132349) (@lem7153919 _132349 f s g)). Qed.
Lemma lem7153922 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : ((term138 _132349 f s g) = (term139 _132349 f s g)) = ((term129 _132349 f s g) = (term152 _132349 f s g)).
Proof. exact (MK_COMB (@lem7153913 _132349 f s g) (@lem7153921 _132349 f s g)). Qed.
Lemma lem7153923 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term129 _132349 f s g) = (term152 _132349 f s g).
Proof. exact (EQ_MP (@lem7153922 _132349 f s g) (@lem7153903 _132349 f s g)). Qed.
Lemma lem7153924 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term130 _132349 f g) = (term153 _132349 f g).
Proof. exact (fun_ext (fun s : _132349 -> Prop => @lem7153923 _132349 f s g)). Qed.
Lemma lem7153925 {_132349 : Type'} : (@all (_132349 -> Prop)) = (@all (_132349 -> Prop)).
Proof. exact (eq_refl (@all (_132349 -> Prop))). Qed.
Lemma lem7153926 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term131 _132349 f g) = (term154 _132349 f g).
Proof. exact (MK_COMB (@lem7153925 _132349) (@lem7153924 _132349 f g)). Qed.
Lemma lem7153928 {A B : Type'} (P : type1413 A B) : (term155 A B P) = (term156 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7153929 {_132349 : Type'} (P : type672 _132349) : (term157 _132349 P) = (term158 _132349 P).
Proof. exact (@lem7153928 (_132349 -> Prop) _132349 P). Qed.
Lemma lem7153930 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term159 _132349 f g) = (term160 _132349 f g).
Proof. exact (@lem7153929 _132349 (term161 _132349 f g)). Qed.
Lemma lem7153931 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term162 _132349 f g s) = (term151 _132349 f s g).
Proof. exact (eq_refl (term162 _132349 f g s)). Qed.
Lemma lem7153932 {_132349 : Type'} (x : _132349) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7153933 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) (x : _132349) : (term163 _132349 f g s x) = (term164 _132349 f s g x).
Proof. exact (MK_COMB (@lem7153931 _132349 f s g) (@lem7153932 _132349 x)). Qed.
Lemma lem7153934 {_132349 : Type'} (x : _132349) (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term164 _132349 f s g x) = (term149 _132349 x f s g).
Proof. exact (eq_refl (term164 _132349 f s g x)). Qed.
Lemma lem7153935 {_132349 : Type'} (x : _132349) (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term163 _132349 f g s x) = (term149 _132349 x f s g).
Proof. exact (TRANS (@lem7153933 _132349 f s g x) (@lem7153934 _132349 x f s g)). Qed.
Lemma lem7153936 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term165 _132349 f g s) = (term151 _132349 f s g).
Proof. exact (fun_ext (fun x : _132349 => @lem7153935 _132349 x f s g)). Qed.
Lemma lem7153937 {_132349 : Type'} : (@ex _132349) = (@ex _132349).
Proof. exact (eq_refl (@ex _132349)). Qed.
Lemma lem7153938 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term166 _132349 f g s) = (term152 _132349 f s g).
Proof. exact (MK_COMB (@lem7153937 _132349) (@lem7153936 _132349 f s g)). Qed.
Lemma lem7153939 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term167 _132349 f g) = (term153 _132349 f g).
Proof. exact (fun_ext (fun s : _132349 -> Prop => @lem7153938 _132349 f s g)). Qed.
Lemma lem7153940 {_132349 : Type'} : (@all (_132349 -> Prop)) = (@all (_132349 -> Prop)).
Proof. exact (eq_refl (@all (_132349 -> Prop))). Qed.
Lemma lem7153941 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term159 _132349 f g) = (term154 _132349 f g).
Proof. exact (MK_COMB (@lem7153940 _132349) (@lem7153939 _132349 f g)). Qed.
Lemma lem7153942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7153943 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term168 _132349 f g) = (term169 _132349 f g).
Proof. exact (MK_COMB (@lem7153942) (@lem7153941 _132349 f g)). Qed.
Lemma lem7153944 {_132349 : Type'} (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term162 _132349 f g s) = (term151 _132349 f s g).
Proof. exact (eq_refl (term162 _132349 f g s)). Qed.
Lemma lem7153945 {_132349 : Type'} (x : type684 _132349) (s : _132349 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7153946 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (x : type684 _132349) (s : _132349 -> Prop) : (term170 _132349 f g x s) = (term171 _132349 f g x s).
Proof. exact (MK_COMB (@lem7153944 _132349 f s g) (@lem7153945 _132349 x s)). Qed.
Lemma lem7153947 {_132349 : Type'} (x : type684 _132349) (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term171 _132349 f g x s) = (term172 _132349 x f s g).
Proof. exact (eq_refl (term171 _132349 f g x s)). Qed.
Lemma lem7153948 {_132349 : Type'} (x : type684 _132349) (f : _132349 -> real) (s : _132349 -> Prop) (g : _132349 -> real) : (term170 _132349 f g x s) = (term172 _132349 x f s g).
Proof. exact (TRANS (@lem7153946 _132349 f g x s) (@lem7153947 _132349 x f s g)). Qed.
Lemma lem7153949 {_132349 : Type'} (x : type684 _132349) (f : _132349 -> real) (g : _132349 -> real) : (term173 _132349 f g x) = (term174 _132349 x f g).
Proof. exact (fun_ext (fun s : _132349 -> Prop => @lem7153948 _132349 x f s g)). Qed.
Lemma lem7153950 {_132349 : Type'} : (@all (_132349 -> Prop)) = (@all (_132349 -> Prop)).
Proof. exact (eq_refl (@all (_132349 -> Prop))). Qed.
Lemma lem7153951 {_132349 : Type'} (x : type684 _132349) (f : _132349 -> real) (g : _132349 -> real) : (term175 _132349 f g x) = (term176 _132349 x f g).
Proof. exact (MK_COMB (@lem7153950 _132349) (@lem7153949 _132349 x f g)). Qed.
Lemma lem7153952 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term177 _132349 f g) = (term178 _132349 f g).
Proof. exact (fun_ext (fun x : type684 _132349 => @lem7153951 _132349 x f g)). Qed.
Lemma lem7153953 {_132349 : Type'} : (@ex ((_132349 -> Prop) -> _132349)) = (@ex ((_132349 -> Prop) -> _132349)).
Proof. exact (eq_refl (@ex ((_132349 -> Prop) -> _132349))). Qed.
Lemma lem7153954 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term160 _132349 f g) = (term179 _132349 f g).
Proof. exact (MK_COMB (@lem7153953 _132349) (@lem7153952 _132349 f g)). Qed.
Lemma lem7153955 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : ((term159 _132349 f g) = (term160 _132349 f g)) = ((term154 _132349 f g) = (term179 _132349 f g)).
Proof. exact (MK_COMB (@lem7153943 _132349 f g) (@lem7153954 _132349 f g)). Qed.
Lemma lem7153956 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term154 _132349 f g) = (term179 _132349 f g).
Proof. exact (EQ_MP (@lem7153955 _132349 f g) (@lem7153930 _132349 f g)). Qed.
Lemma lem7153957 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term131 _132349 f g) = (term179 _132349 f g).
Proof. exact (TRANS (@lem7153926 _132349 f g) (@lem7153956 _132349 f g)). Qed.
Lemma lem7153958 {_132349 : Type'} (f : _132349 -> real) : (term132 _132349 f) = (term180 _132349 f).
Proof. exact (fun_ext (fun g : _132349 -> real => @lem7153957 _132349 f g)). Qed.
Lemma lem7153959 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7153960 {_132349 : Type'} (f : _132349 -> real) : (term133 _132349 f) = (term181 _132349 f).
Proof. exact (MK_COMB (@lem7153959 _132349) (@lem7153958 _132349 f)). Qed.
Lemma lem7153962 {A B : Type'} (P : type1413 A B) : (term155 A B P) = (term156 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7153963 {_132349 : Type'} (P : type707 _132349) : (term182 _132349 P) = (term183 _132349 P).
Proof. exact (@lem7153962 (_132349 -> real) (type684 _132349) P). Qed.
Lemma lem7153964 {_132349 : Type'} (f : _132349 -> real) : (term184 _132349 f) = (term185 _132349 f).
Proof. exact (@lem7153963 _132349 (term186 _132349 f)). Qed.
Lemma lem7153965 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term187 _132349 f g) = (term178 _132349 f g).
Proof. exact (eq_refl (term187 _132349 f g)). Qed.
Lemma lem7153966 {_132349 : Type'} (x : type684 _132349) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7153967 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) (x : type684 _132349) : (term188 _132349 f g x) = (term189 _132349 f g x).
Proof. exact (MK_COMB (@lem7153965 _132349 f g) (@lem7153966 _132349 x)). Qed.
Lemma lem7153968 {_132349 : Type'} (x : type684 _132349) (f : _132349 -> real) (g : _132349 -> real) : (term189 _132349 f g x) = (term176 _132349 x f g).
Proof. exact (eq_refl (term189 _132349 f g x)). Qed.
Lemma lem7153969 {_132349 : Type'} (x : type684 _132349) (f : _132349 -> real) (g : _132349 -> real) : (term188 _132349 f g x) = (term176 _132349 x f g).
Proof. exact (TRANS (@lem7153967 _132349 f g x) (@lem7153968 _132349 x f g)). Qed.
Lemma lem7153970 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term190 _132349 f g) = (term178 _132349 f g).
Proof. exact (fun_ext (fun x : type684 _132349 => @lem7153969 _132349 x f g)). Qed.
Lemma lem7153971 {_132349 : Type'} : (@ex ((_132349 -> Prop) -> _132349)) = (@ex ((_132349 -> Prop) -> _132349)).
Proof. exact (eq_refl (@ex ((_132349 -> Prop) -> _132349))). Qed.
Lemma lem7153972 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term191 _132349 f g) = (term179 _132349 f g).
Proof. exact (MK_COMB (@lem7153971 _132349) (@lem7153970 _132349 f g)). Qed.
Lemma lem7153973 {_132349 : Type'} (f : _132349 -> real) : (term192 _132349 f) = (term180 _132349 f).
Proof. exact (fun_ext (fun g : _132349 -> real => @lem7153972 _132349 f g)). Qed.
Lemma lem7153974 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7153975 {_132349 : Type'} (f : _132349 -> real) : (term184 _132349 f) = (term181 _132349 f).
Proof. exact (MK_COMB (@lem7153974 _132349) (@lem7153973 _132349 f)). Qed.
Lemma lem7153976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7153977 {_132349 : Type'} (f : _132349 -> real) : (term193 _132349 f) = (term194 _132349 f).
Proof. exact (MK_COMB (@lem7153976) (@lem7153975 _132349 f)). Qed.
Lemma lem7153978 {_132349 : Type'} (f : _132349 -> real) (g : _132349 -> real) : (term187 _132349 f g) = (term178 _132349 f g).
Proof. exact (eq_refl (term187 _132349 f g)). Qed.
Lemma lem7153979 {_132349 : Type'} (x : type710 _132349) (g : _132349 -> real) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7153980 {_132349 : Type'} (f : _132349 -> real) (x : type710 _132349) (g : _132349 -> real) : (term195 _132349 f x g) = (term196 _132349 f x g).
Proof. exact (MK_COMB (@lem7153978 _132349 f g) (@lem7153979 _132349 x g)). Qed.
Lemma lem7153981 {_132349 : Type'} (x : type710 _132349) (f : _132349 -> real) (g : _132349 -> real) : (term196 _132349 f x g) = (term197 _132349 x f g).
Proof. exact (eq_refl (term196 _132349 f x g)). Qed.
Lemma lem7153982 {_132349 : Type'} (x : type710 _132349) (f : _132349 -> real) (g : _132349 -> real) : (term195 _132349 f x g) = (term197 _132349 x f g).
Proof. exact (TRANS (@lem7153980 _132349 f x g) (@lem7153981 _132349 x f g)). Qed.
Lemma lem7153983 {_132349 : Type'} (x : type710 _132349) (f : _132349 -> real) : (term198 _132349 f x) = (term199 _132349 x f).
Proof. exact (fun_ext (fun g : _132349 -> real => @lem7153982 _132349 x f g)). Qed.
Lemma lem7153984 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7153985 {_132349 : Type'} (x : type710 _132349) (f : _132349 -> real) : (term200 _132349 f x) = (term201 _132349 x f).
Proof. exact (MK_COMB (@lem7153984 _132349) (@lem7153983 _132349 x f)). Qed.
Lemma lem7153986 {_132349 : Type'} (f : _132349 -> real) : (term202 _132349 f) = (term203 _132349 f).
Proof. exact (fun_ext (fun x : type710 _132349 => @lem7153985 _132349 x f)). Qed.
Lemma lem7153987 {_132349 : Type'} : (@ex ((_132349 -> real) -> (_132349 -> Prop) -> _132349)) = (@ex ((_132349 -> real) -> (_132349 -> Prop) -> _132349)).
Proof. exact (eq_refl (@ex ((_132349 -> real) -> (_132349 -> Prop) -> _132349))). Qed.
Lemma lem7153988 {_132349 : Type'} (f : _132349 -> real) : (term185 _132349 f) = (term204 _132349 f).
Proof. exact (MK_COMB (@lem7153987 _132349) (@lem7153986 _132349 f)). Qed.
Lemma lem7153989 {_132349 : Type'} (f : _132349 -> real) : ((term184 _132349 f) = (term185 _132349 f)) = ((term181 _132349 f) = (term204 _132349 f)).
Proof. exact (MK_COMB (@lem7153977 _132349 f) (@lem7153988 _132349 f)). Qed.
Lemma lem7153990 {_132349 : Type'} (f : _132349 -> real) : (term181 _132349 f) = (term204 _132349 f).
Proof. exact (EQ_MP (@lem7153989 _132349 f) (@lem7153964 _132349 f)). Qed.
Lemma lem7153991 {_132349 : Type'} (f : _132349 -> real) : (term133 _132349 f) = (term204 _132349 f).
Proof. exact (TRANS (@lem7153960 _132349 f) (@lem7153990 _132349 f)). Qed.
Lemma lem7153992 {_132349 : Type'} : (term134 _132349) = (term205 _132349).
Proof. exact (fun_ext (fun f : _132349 -> real => @lem7153991 _132349 f)). Qed.
Lemma lem7153993 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7153994 {_132349 : Type'} : (term135 _132349) = (term206 _132349).
Proof. exact (MK_COMB (@lem7153993 _132349) (@lem7153992 _132349)). Qed.
Lemma lem7153996 {A B : Type'} (P : type1413 A B) : (term155 A B P) = (term156 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7153997 {_132349 : Type'} (P : type708 _132349) : (term207 _132349 P) = (term208 _132349 P).
Proof. exact (@lem7153996 (_132349 -> real) (type710 _132349) P). Qed.
Lemma lem7153998 {_132349 : Type'} : (term209 _132349) = (term210 _132349).
Proof. exact (@lem7153997 _132349 (term211 _132349)). Qed.
Lemma lem7153999 {_132349 : Type'} (f : _132349 -> real) : (term212 _132349 f) = (term203 _132349 f).
Proof. exact (eq_refl (term212 _132349 f)). Qed.
Lemma lem7154000 {_132349 : Type'} (x : type710 _132349) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7154001 {_132349 : Type'} (f : _132349 -> real) (x : type710 _132349) : (term213 _132349 f x) = (term214 _132349 f x).
Proof. exact (MK_COMB (@lem7153999 _132349 f) (@lem7154000 _132349 x)). Qed.
Lemma lem7154002 {_132349 : Type'} (x : type710 _132349) (f : _132349 -> real) : (term214 _132349 f x) = (term201 _132349 x f).
Proof. exact (eq_refl (term214 _132349 f x)). Qed.
Lemma lem7154003 {_132349 : Type'} (x : type710 _132349) (f : _132349 -> real) : (term213 _132349 f x) = (term201 _132349 x f).
Proof. exact (TRANS (@lem7154001 _132349 f x) (@lem7154002 _132349 x f)). Qed.
Lemma lem7154004 {_132349 : Type'} (f : _132349 -> real) : (term215 _132349 f) = (term203 _132349 f).
Proof. exact (fun_ext (fun x : type710 _132349 => @lem7154003 _132349 x f)). Qed.
Lemma lem7154005 {_132349 : Type'} : (@ex ((_132349 -> real) -> (_132349 -> Prop) -> _132349)) = (@ex ((_132349 -> real) -> (_132349 -> Prop) -> _132349)).
Proof. exact (eq_refl (@ex ((_132349 -> real) -> (_132349 -> Prop) -> _132349))). Qed.
Lemma lem7154006 {_132349 : Type'} (f : _132349 -> real) : (term216 _132349 f) = (term204 _132349 f).
Proof. exact (MK_COMB (@lem7154005 _132349) (@lem7154004 _132349 f)). Qed.
Lemma lem7154007 {_132349 : Type'} : (term217 _132349) = (term205 _132349).
Proof. exact (fun_ext (fun f : _132349 -> real => @lem7154006 _132349 f)). Qed.
Lemma lem7154008 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7154009 {_132349 : Type'} : (term209 _132349) = (term206 _132349).
Proof. exact (MK_COMB (@lem7154008 _132349) (@lem7154007 _132349)). Qed.
Lemma lem7154010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7154011 {_132349 : Type'} : (term218 _132349) = (term219 _132349).
Proof. exact (MK_COMB (@lem7154010) (@lem7154009 _132349)). Qed.
Lemma lem7154012 {_132349 : Type'} (f : _132349 -> real) : (term212 _132349 f) = (term203 _132349 f).
Proof. exact (eq_refl (term212 _132349 f)). Qed.
Lemma lem7154013 {_132349 : Type'} (x : type711 _132349) (f : _132349 -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7154014 {_132349 : Type'} (x : type711 _132349) (f : _132349 -> real) : (term220 _132349 x f) = (term221 _132349 x f).
Proof. exact (MK_COMB (@lem7154012 _132349 f) (@lem7154013 _132349 x f)). Qed.
Lemma lem7154015 {_132349 : Type'} (x : type711 _132349) (f : _132349 -> real) : (term221 _132349 x f) = (term222 _132349 x f).
Proof. exact (eq_refl (term221 _132349 x f)). Qed.
Lemma lem7154016 {_132349 : Type'} (x : type711 _132349) (f : _132349 -> real) : (term220 _132349 x f) = (term222 _132349 x f).
Proof. exact (TRANS (@lem7154014 _132349 x f) (@lem7154015 _132349 x f)). Qed.
Lemma lem7154017 {_132349 : Type'} (x : type711 _132349) : (term223 _132349 x) = (term224 _132349 x).
Proof. exact (fun_ext (fun f : _132349 -> real => @lem7154016 _132349 x f)). Qed.
Lemma lem7154018 {_132349 : Type'} : (@all (_132349 -> real)) = (@all (_132349 -> real)).
Proof. exact (eq_refl (@all (_132349 -> real))). Qed.
Lemma lem7154019 {_132349 : Type'} (x : type711 _132349) : (term225 _132349 x) = (term226 _132349 x).
Proof. exact (MK_COMB (@lem7154018 _132349) (@lem7154017 _132349 x)). Qed.
Lemma lem7154020 {_132349 : Type'} : (term227 _132349) = (term228 _132349).
Proof. exact (fun_ext (fun x : type711 _132349 => @lem7154019 _132349 x)). Qed.
Lemma lem7154021 {_132349 : Type'} : (@ex ((_132349 -> real) -> (_132349 -> real) -> (_132349 -> Prop) -> _132349)) = (@ex ((_132349 -> real) -> (_132349 -> real) -> (_132349 -> Prop) -> _132349)).
Proof. exact (eq_refl (@ex ((_132349 -> real) -> (_132349 -> real) -> (_132349 -> Prop) -> _132349))). Qed.
Lemma lem7154022 {_132349 : Type'} : (term210 _132349) = (term229 _132349).
Proof. exact (MK_COMB (@lem7154021 _132349) (@lem7154020 _132349)). Qed.
Lemma lem7154023 {_132349 : Type'} : ((term209 _132349) = (term210 _132349)) = ((term206 _132349) = (term229 _132349)).
Proof. exact (MK_COMB (@lem7154011 _132349) (@lem7154022 _132349)). Qed.
Lemma lem7154024 {_132349 : Type'} : (term206 _132349) = (term229 _132349).
Proof. exact (EQ_MP (@lem7154023 _132349) (@lem7153998 _132349)). Qed.
Lemma lem7154026 {_132349 : Type'} : (term135 _132349) = (term229 _132349).
Proof. exact (TRANS (@lem7153994 _132349) (@lem7154024 _132349)). Qed.
Lemma lem7154027 {_132349 : Type'} : (term12 _132349) = (term229 _132349).
Proof. exact (TRANS (@lem7153794 _132349) (@lem7154026 _132349)). Qed.
Lemma lem7154028 {_132349 : Type'} (h1 : term12 _132349) : term229 _132349.
Proof. exact (EQ_MP (@lem7154027 _132349) (@lem7153528 _132349 h1)). Qed.
Lemma lem7154035 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term115 A s f g x) = (term116 A s f g x).
Proof. exact (@lem17362 (@IN A x s) ((f x) = (g x))). Qed.
Lemma lem7154036 {A : Type'} (P : A -> Prop) : (term117 A P) = (term118 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7154037 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term119 A s f g) = (term120 A s f g).
Proof. exact (@lem7154036 A (term43 A s f g)). Qed.
Lemma lem7154038 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term121 A s f g x) = (term42 A s f g x).
Proof. exact (eq_refl (term121 A s f g x)). Qed.
Lemma lem7154039 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7154040 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term122 A s f g x) = (term115 A s f g x).
Proof. exact (MK_COMB (@lem7154039) (@lem7154038 A s f g x)). Qed.
Lemma lem7154041 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term122 A s f g x) = (term116 A s f g x).
Proof. exact (TRANS (@lem7154040 A s f g x) (@lem7154035 A s f g x)). Qed.
Lemma lem7154042 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term123 A s f g) = (term124 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7154041 A s f g x)). Qed.
Lemma lem7154043 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7154044 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term120 A s f g) = (term125 A s f g).
Proof. exact (MK_COMB (@lem7154043 A) (@lem7154042 A s f g)). Qed.
Lemma lem7154045 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term119 A s f g) = (term125 A s f g).
Proof. exact (TRANS (@lem7154037 A s f g) (@lem7154044 A s f g)). Qed.
Lemma lem7154046 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : ((@sum A s f) = (@sum A s g)) = ((@sum A s f) = (@sum A s g)).
Proof. exact (eq_refl ((@sum A s f) = (@sum A s g))). Qed.
Lemma lem7154047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7154048 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term126 A s f g) = (term127 A s f g).
Proof. exact (MK_COMB (@lem7154047) (@lem7154045 A s f g)). Qed.
Lemma lem7154049 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term128 A f s g) = (term129 A f s g).
Proof. exact (MK_COMB (@lem7154048 A s f g) (@lem7154046 A f s g)). Qed.
Lemma lem7154050 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term46 A f s g) = (term128 A f s g).
Proof. exact (@lem17265 (term44 A s f g) ((@sum A s f) = (@sum A s g))). Qed.
Lemma lem7154051 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term46 A f s g) = (term129 A f s g).
Proof. exact (TRANS (@lem7154050 A f s g) (@lem7154049 A f s g)). Qed.
Lemma lem7154052 {A : Type'} (f : A -> real) (g : A -> real) : (term47 A f g) = (term130 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7154051 A f s g)). Qed.
Lemma lem7154053 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154054 {A : Type'} (f : A -> real) (g : A -> real) : (term48 A f g) = (term131 A f g).
Proof. exact (MK_COMB (@lem7154053 A) (@lem7154052 A f g)). Qed.
Lemma lem7154055 {A : Type'} (f : A -> real) : (term49 A f) = (term132 A f).
Proof. exact (fun_ext (fun g : A -> real => @lem7154054 A f g)). Qed.
Lemma lem7154056 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154057 {A : Type'} (f : A -> real) : (term50 A f) = (term133 A f).
Proof. exact (MK_COMB (@lem7154056 A) (@lem7154055 A f)). Qed.
Lemma lem7154058 {A : Type'} : (term51 A) = (term134 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7154057 A f)). Qed.
Lemma lem7154059 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154060 {A : Type'} : (term12 A) = (term135 A).
Proof. exact (MK_COMB (@lem7154059 A) (@lem7154058 A)). Qed.
Lemma lem7154167 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7154168 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (@lem7154167 A P Q). Qed.
Lemma lem7154169 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term138 A f s g) = (term139 A f s g).
Proof. exact (@lem7154168 A (term124 A s f g) ((@sum A s f) = (@sum A s g))). Qed.
Lemma lem7154170 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term140 A s f g x) = (term116 A s f g x).
Proof. exact (eq_refl (term140 A s f g x)). Qed.
Lemma lem7154171 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term141 A s f g) = (term124 A s f g).
Proof. exact (fun_ext (fun x : A => @lem7154170 A s f g x)). Qed.
Lemma lem7154172 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7154173 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term142 A s f g) = (term125 A s f g).
Proof. exact (MK_COMB (@lem7154172 A) (@lem7154171 A s f g)). Qed.
Lemma lem7154174 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7154175 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) : (term143 A s f g) = (term127 A s f g).
Proof. exact (MK_COMB (@lem7154174) (@lem7154173 A s f g)). Qed.
Lemma lem7154176 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : ((@sum A s f) = (@sum A s g)) = ((@sum A s f) = (@sum A s g)).
Proof. exact (eq_refl ((@sum A s f) = (@sum A s g))). Qed.
Lemma lem7154177 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term138 A f s g) = (term129 A f s g).
Proof. exact (MK_COMB (@lem7154175 A s f g) (@lem7154176 A f s g)). Qed.
Lemma lem7154178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7154179 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term144 A f s g) = (term145 A f s g).
Proof. exact (MK_COMB (@lem7154178) (@lem7154177 A f s g)). Qed.
Lemma lem7154180 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term140 A s f g x) = (term116 A s f g x).
Proof. exact (eq_refl (term140 A s f g x)). Qed.
Lemma lem7154181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7154182 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term146 A s f g x) = (term147 A s f g x).
Proof. exact (MK_COMB (@lem7154181) (@lem7154180 A s f g x)). Qed.
Lemma lem7154183 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : ((@sum A s f) = (@sum A s g)) = ((@sum A s f) = (@sum A s g)).
Proof. exact (eq_refl ((@sum A s f) = (@sum A s g))). Qed.
Lemma lem7154184 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term148 A x f s g) = (term149 A x f s g).
Proof. exact (MK_COMB (@lem7154182 A s f g x) (@lem7154183 A f s g)). Qed.
Lemma lem7154185 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term150 A f s g) = (term151 A f s g).
Proof. exact (fun_ext (fun x : A => @lem7154184 A x f s g)). Qed.
Lemma lem7154186 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7154187 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term139 A f s g) = (term152 A f s g).
Proof. exact (MK_COMB (@lem7154186 A) (@lem7154185 A f s g)). Qed.
Lemma lem7154188 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : ((term138 A f s g) = (term139 A f s g)) = ((term129 A f s g) = (term152 A f s g)).
Proof. exact (MK_COMB (@lem7154179 A f s g) (@lem7154187 A f s g)). Qed.
Lemma lem7154189 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term129 A f s g) = (term152 A f s g).
Proof. exact (EQ_MP (@lem7154188 A f s g) (@lem7154169 A f s g)). Qed.
Lemma lem7154190 {A : Type'} (f : A -> real) (g : A -> real) : (term130 A f g) = (term153 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7154189 A f s g)). Qed.
Lemma lem7154191 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154192 {A : Type'} (f : A -> real) (g : A -> real) : (term131 A f g) = (term154 A f g).
Proof. exact (MK_COMB (@lem7154191 A) (@lem7154190 A f g)). Qed.
Lemma lem7154194 {A B : Type'} (P : type1413 A B) : (term155 A B P) = (term156 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7154195 {A : Type'} (P : type672 A) : (term157 A P) = (term158 A P).
Proof. exact (@lem7154194 (A -> Prop) A P). Qed.
Lemma lem7154196 {A : Type'} (f : A -> real) (g : A -> real) : (term159 A f g) = (term160 A f g).
Proof. exact (@lem7154195 A (term161 A f g)). Qed.
Lemma lem7154197 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term162 A f g s) = (term151 A f s g).
Proof. exact (eq_refl (term162 A f g s)). Qed.
Lemma lem7154198 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7154199 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) (x : A) : (term163 A f g s x) = (term164 A f s g x).
Proof. exact (MK_COMB (@lem7154197 A f s g) (@lem7154198 A x)). Qed.
Lemma lem7154200 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term164 A f s g x) = (term149 A x f s g).
Proof. exact (eq_refl (term164 A f s g x)). Qed.
Lemma lem7154201 {A : Type'} (x : A) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term163 A f g s x) = (term149 A x f s g).
Proof. exact (TRANS (@lem7154199 A f s g x) (@lem7154200 A x f s g)). Qed.
Lemma lem7154202 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term165 A f g s) = (term151 A f s g).
Proof. exact (fun_ext (fun x : A => @lem7154201 A x f s g)). Qed.
Lemma lem7154203 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7154204 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term166 A f g s) = (term152 A f s g).
Proof. exact (MK_COMB (@lem7154203 A) (@lem7154202 A f s g)). Qed.
Lemma lem7154205 {A : Type'} (f : A -> real) (g : A -> real) : (term167 A f g) = (term153 A f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7154204 A f s g)). Qed.
Lemma lem7154206 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154207 {A : Type'} (f : A -> real) (g : A -> real) : (term159 A f g) = (term154 A f g).
Proof. exact (MK_COMB (@lem7154206 A) (@lem7154205 A f g)). Qed.
Lemma lem7154208 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7154209 {A : Type'} (f : A -> real) (g : A -> real) : (term168 A f g) = (term169 A f g).
Proof. exact (MK_COMB (@lem7154208) (@lem7154207 A f g)). Qed.
Lemma lem7154210 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : (term162 A f g s) = (term151 A f s g).
Proof. exact (eq_refl (term162 A f g s)). Qed.
Lemma lem7154211 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7154212 {A : Type'} (f : A -> real) (g : A -> real) (x : type684 A) (s : A -> Prop) : (term170 A f g x s) = (term171 A f g x s).
Proof. exact (MK_COMB (@lem7154210 A f s g) (@lem7154211 A x s)). Qed.
Lemma lem7154213 {A : Type'} (x : type684 A) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term171 A f g x s) = (term172 A x f s g).
Proof. exact (eq_refl (term171 A f g x s)). Qed.
Lemma lem7154214 {A : Type'} (x : type684 A) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term170 A f g x s) = (term172 A x f s g).
Proof. exact (TRANS (@lem7154212 A f g x s) (@lem7154213 A x f s g)). Qed.
Lemma lem7154215 {A : Type'} (x : type684 A) (f : A -> real) (g : A -> real) : (term173 A f g x) = (term174 A x f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7154214 A x f s g)). Qed.
Lemma lem7154216 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154217 {A : Type'} (x : type684 A) (f : A -> real) (g : A -> real) : (term175 A f g x) = (term176 A x f g).
Proof. exact (MK_COMB (@lem7154216 A) (@lem7154215 A x f g)). Qed.
Lemma lem7154218 {A : Type'} (f : A -> real) (g : A -> real) : (term177 A f g) = (term178 A f g).
Proof. exact (fun_ext (fun x : type684 A => @lem7154217 A x f g)). Qed.
Lemma lem7154219 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7154220 {A : Type'} (f : A -> real) (g : A -> real) : (term160 A f g) = (term179 A f g).
Proof. exact (MK_COMB (@lem7154219 A) (@lem7154218 A f g)). Qed.
Lemma lem7154221 {A : Type'} (f : A -> real) (g : A -> real) : ((term159 A f g) = (term160 A f g)) = ((term154 A f g) = (term179 A f g)).
Proof. exact (MK_COMB (@lem7154209 A f g) (@lem7154220 A f g)). Qed.
Lemma lem7154222 {A : Type'} (f : A -> real) (g : A -> real) : (term154 A f g) = (term179 A f g).
Proof. exact (EQ_MP (@lem7154221 A f g) (@lem7154196 A f g)). Qed.
Lemma lem7154223 {A : Type'} (f : A -> real) (g : A -> real) : (term131 A f g) = (term179 A f g).
Proof. exact (TRANS (@lem7154192 A f g) (@lem7154222 A f g)). Qed.
Lemma lem7154224 {A : Type'} (f : A -> real) : (term132 A f) = (term180 A f).
Proof. exact (fun_ext (fun g : A -> real => @lem7154223 A f g)). Qed.
Lemma lem7154225 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154226 {A : Type'} (f : A -> real) : (term133 A f) = (term181 A f).
Proof. exact (MK_COMB (@lem7154225 A) (@lem7154224 A f)). Qed.
Lemma lem7154228 {A B : Type'} (P : type1413 A B) : (term155 A B P) = (term156 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7154229 {A : Type'} (P : type707 A) : (term182 A P) = (term183 A P).
Proof. exact (@lem7154228 (A -> real) (type684 A) P). Qed.
Lemma lem7154230 {A : Type'} (f : A -> real) : (term184 A f) = (term185 A f).
Proof. exact (@lem7154229 A (term186 A f)). Qed.
Lemma lem7154231 {A : Type'} (f : A -> real) (g : A -> real) : (term187 A f g) = (term178 A f g).
Proof. exact (eq_refl (term187 A f g)). Qed.
Lemma lem7154232 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7154233 {A : Type'} (f : A -> real) (g : A -> real) (x : type684 A) : (term188 A f g x) = (term189 A f g x).
Proof. exact (MK_COMB (@lem7154231 A f g) (@lem7154232 A x)). Qed.
Lemma lem7154234 {A : Type'} (x : type684 A) (f : A -> real) (g : A -> real) : (term189 A f g x) = (term176 A x f g).
Proof. exact (eq_refl (term189 A f g x)). Qed.
Lemma lem7154235 {A : Type'} (x : type684 A) (f : A -> real) (g : A -> real) : (term188 A f g x) = (term176 A x f g).
Proof. exact (TRANS (@lem7154233 A f g x) (@lem7154234 A x f g)). Qed.
Lemma lem7154236 {A : Type'} (f : A -> real) (g : A -> real) : (term190 A f g) = (term178 A f g).
Proof. exact (fun_ext (fun x : type684 A => @lem7154235 A x f g)). Qed.
Lemma lem7154237 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7154238 {A : Type'} (f : A -> real) (g : A -> real) : (term191 A f g) = (term179 A f g).
Proof. exact (MK_COMB (@lem7154237 A) (@lem7154236 A f g)). Qed.
Lemma lem7154239 {A : Type'} (f : A -> real) : (term192 A f) = (term180 A f).
Proof. exact (fun_ext (fun g : A -> real => @lem7154238 A f g)). Qed.
Lemma lem7154240 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154241 {A : Type'} (f : A -> real) : (term184 A f) = (term181 A f).
Proof. exact (MK_COMB (@lem7154240 A) (@lem7154239 A f)). Qed.
Lemma lem7154242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7154243 {A : Type'} (f : A -> real) : (term193 A f) = (term194 A f).
Proof. exact (MK_COMB (@lem7154242) (@lem7154241 A f)). Qed.
Lemma lem7154244 {A : Type'} (f : A -> real) (g : A -> real) : (term187 A f g) = (term178 A f g).
Proof. exact (eq_refl (term187 A f g)). Qed.
Lemma lem7154245 {A : Type'} (x : type710 A) (g : A -> real) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem7154246 {A : Type'} (f : A -> real) (x : type710 A) (g : A -> real) : (term195 A f x g) = (term196 A f x g).
Proof. exact (MK_COMB (@lem7154244 A f g) (@lem7154245 A x g)). Qed.
Lemma lem7154247 {A : Type'} (x : type710 A) (f : A -> real) (g : A -> real) : (term196 A f x g) = (term197 A x f g).
Proof. exact (eq_refl (term196 A f x g)). Qed.
Lemma lem7154248 {A : Type'} (x : type710 A) (f : A -> real) (g : A -> real) : (term195 A f x g) = (term197 A x f g).
Proof. exact (TRANS (@lem7154246 A f x g) (@lem7154247 A x f g)). Qed.
Lemma lem7154249 {A : Type'} (x : type710 A) (f : A -> real) : (term198 A f x) = (term199 A x f).
Proof. exact (fun_ext (fun g : A -> real => @lem7154248 A x f g)). Qed.
Lemma lem7154250 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154251 {A : Type'} (x : type710 A) (f : A -> real) : (term200 A f x) = (term201 A x f).
Proof. exact (MK_COMB (@lem7154250 A) (@lem7154249 A x f)). Qed.
Lemma lem7154252 {A : Type'} (f : A -> real) : (term202 A f) = (term203 A f).
Proof. exact (fun_ext (fun x : type710 A => @lem7154251 A x f)). Qed.
Lemma lem7154253 {A : Type'} : (@ex ((A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7154254 {A : Type'} (f : A -> real) : (term185 A f) = (term204 A f).
Proof. exact (MK_COMB (@lem7154253 A) (@lem7154252 A f)). Qed.
Lemma lem7154255 {A : Type'} (f : A -> real) : ((term184 A f) = (term185 A f)) = ((term181 A f) = (term204 A f)).
Proof. exact (MK_COMB (@lem7154243 A f) (@lem7154254 A f)). Qed.
Lemma lem7154256 {A : Type'} (f : A -> real) : (term181 A f) = (term204 A f).
Proof. exact (EQ_MP (@lem7154255 A f) (@lem7154230 A f)). Qed.
Lemma lem7154257 {A : Type'} (f : A -> real) : (term133 A f) = (term204 A f).
Proof. exact (TRANS (@lem7154226 A f) (@lem7154256 A f)). Qed.
Lemma lem7154258 {A : Type'} : (term134 A) = (term205 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7154257 A f)). Qed.
Lemma lem7154259 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154260 {A : Type'} : (term135 A) = (term206 A).
Proof. exact (MK_COMB (@lem7154259 A) (@lem7154258 A)). Qed.
Lemma lem7154262 {A B : Type'} (P : type1413 A B) : (term155 A B P) = (term156 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7154263 {A : Type'} (P : type708 A) : (term207 A P) = (term208 A P).
Proof. exact (@lem7154262 (A -> real) (type710 A) P). Qed.
Lemma lem7154264 {A : Type'} : (term209 A) = (term210 A).
Proof. exact (@lem7154263 A (term211 A)). Qed.
Lemma lem7154265 {A : Type'} (f : A -> real) : (term212 A f) = (term203 A f).
Proof. exact (eq_refl (term212 A f)). Qed.
Lemma lem7154266 {A : Type'} (x : type710 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7154267 {A : Type'} (f : A -> real) (x : type710 A) : (term213 A f x) = (term214 A f x).
Proof. exact (MK_COMB (@lem7154265 A f) (@lem7154266 A x)). Qed.
Lemma lem7154268 {A : Type'} (x : type710 A) (f : A -> real) : (term214 A f x) = (term201 A x f).
Proof. exact (eq_refl (term214 A f x)). Qed.
Lemma lem7154269 {A : Type'} (x : type710 A) (f : A -> real) : (term213 A f x) = (term201 A x f).
Proof. exact (TRANS (@lem7154267 A f x) (@lem7154268 A x f)). Qed.
Lemma lem7154270 {A : Type'} (f : A -> real) : (term215 A f) = (term203 A f).
Proof. exact (fun_ext (fun x : type710 A => @lem7154269 A x f)). Qed.
Lemma lem7154271 {A : Type'} : (@ex ((A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7154272 {A : Type'} (f : A -> real) : (term216 A f) = (term204 A f).
Proof. exact (MK_COMB (@lem7154271 A) (@lem7154270 A f)). Qed.
Lemma lem7154273 {A : Type'} : (term217 A) = (term205 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7154272 A f)). Qed.
Lemma lem7154274 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154275 {A : Type'} : (term209 A) = (term206 A).
Proof. exact (MK_COMB (@lem7154274 A) (@lem7154273 A)). Qed.
Lemma lem7154276 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7154277 {A : Type'} : (term218 A) = (term219 A).
Proof. exact (MK_COMB (@lem7154276) (@lem7154275 A)). Qed.
Lemma lem7154278 {A : Type'} (f : A -> real) : (term212 A f) = (term203 A f).
Proof. exact (eq_refl (term212 A f)). Qed.
Lemma lem7154279 {A : Type'} (x : type711 A) (f : A -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7154280 {A : Type'} (x : type711 A) (f : A -> real) : (term220 A x f) = (term221 A x f).
Proof. exact (MK_COMB (@lem7154278 A f) (@lem7154279 A x f)). Qed.
Lemma lem7154281 {A : Type'} (x : type711 A) (f : A -> real) : (term221 A x f) = (term222 A x f).
Proof. exact (eq_refl (term221 A x f)). Qed.
Lemma lem7154282 {A : Type'} (x : type711 A) (f : A -> real) : (term220 A x f) = (term222 A x f).
Proof. exact (TRANS (@lem7154280 A x f) (@lem7154281 A x f)). Qed.
Lemma lem7154283 {A : Type'} (x : type711 A) : (term223 A x) = (term224 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7154282 A x f)). Qed.
Lemma lem7154284 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154285 {A : Type'} (x : type711 A) : (term225 A x) = (term226 A x).
Proof. exact (MK_COMB (@lem7154284 A) (@lem7154283 A x)). Qed.
Lemma lem7154286 {A : Type'} : (term227 A) = (term228 A).
Proof. exact (fun_ext (fun x : type711 A => @lem7154285 A x)). Qed.
Lemma lem7154287 {A : Type'} : (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7154288 {A : Type'} : (term210 A) = (term229 A).
Proof. exact (MK_COMB (@lem7154287 A) (@lem7154286 A)). Qed.
Lemma lem7154289 {A : Type'} : ((term209 A) = (term210 A)) = ((term206 A) = (term229 A)).
Proof. exact (MK_COMB (@lem7154277 A) (@lem7154288 A)). Qed.
Lemma lem7154290 {A : Type'} : (term206 A) = (term229 A).
Proof. exact (EQ_MP (@lem7154289 A) (@lem7154264 A)). Qed.
Lemma lem7154292 {A : Type'} : (term135 A) = (term229 A).
Proof. exact (TRANS (@lem7154260 A) (@lem7154290 A)). Qed.
Lemma lem7154293 {A : Type'} : (term12 A) = (term229 A).
Proof. exact (TRANS (@lem7154060 A) (@lem7154292 A)). Qed.
Lemma lem7154294 {A : Type'} (h1 : term12 A) : term229 A.
Proof. exact (EQ_MP (@lem7154293 A) (@lem7153529 A h1)). Qed.
Lemma lem7154306 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term230 A v u f x) = (term231 A v u f x).
Proof. exact (@lem17362 (term78 A v x u) ((f x) = term73)). Qed.
Lemma lem7154307 {A : Type'} (P : A -> Prop) : (term117 A P) = (term118 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7154308 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term232 A v u f) = (term233 A v u f).
Proof. exact (@lem7154307 A (term31 A v u f)). Qed.
Lemma lem7154309 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term234 A v u f x) = (term30 A v u f x).
Proof. exact (eq_refl (term234 A v u f x)). Qed.
Lemma lem7154310 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7154311 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term235 A v u f x) = (term230 A v u f x).
Proof. exact (MK_COMB (@lem7154310) (@lem7154309 A v u f x)). Qed.
Lemma lem7154312 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term235 A v u f x) = (term231 A v u f x).
Proof. exact (TRANS (@lem7154311 A v u f x) (@lem7154306 A v u f x)). Qed.
Lemma lem7154313 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term236 A v u f) = (term237 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7154312 A v u f x)). Qed.
Lemma lem7154314 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7154315 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term233 A v u f) = (term238 A v u f).
Proof. exact (MK_COMB (@lem7154314 A) (@lem7154313 A v u f)). Qed.
Lemma lem7154316 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term232 A v u f) = (term238 A v u f).
Proof. exact (TRANS (@lem7154308 A v u f) (@lem7154315 A v u f)). Qed.
Lemma lem7154318 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term239 A u v) = (term239 A u v).
Proof. exact (eq_refl (term239 A u v)). Qed.
Lemma lem7154319 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term240 A v u f) = (term241 A v u f).
Proof. exact (MK_COMB (@lem7154318 A u v) (@lem7154316 A v u f)). Qed.
Lemma lem7154320 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term242 A v u f) = (term240 A v u f).
Proof. exact (@lem17045 (@SUBSET A u v) (term32 A v u f)). Qed.
Lemma lem7154321 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term242 A v u f) = (term241 A v u f).
Proof. exact (TRANS (@lem7154320 A v u f) (@lem7154319 A v u f)). Qed.
Lemma lem7154322 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((@sum A v f) = (@sum A u f)) = ((@sum A v f) = (@sum A u f)).
Proof. exact (eq_refl ((@sum A v f) = (@sum A u f))). Qed.
Lemma lem7154323 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7154324 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term243 A v u f) = (term244 A v u f).
Proof. exact (MK_COMB (@lem7154323) (@lem7154321 A v u f)). Qed.
Lemma lem7154325 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term245 A v u f) = (term246 A v u f).
Proof. exact (MK_COMB (@lem7154324 A v u f) (@lem7154322 A v u f)). Qed.
Lemma lem7154326 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term36 A v u f) = (term245 A v u f).
Proof. exact (@lem17265 (term34 A v u f) ((@sum A v f) = (@sum A u f))). Qed.
Lemma lem7154327 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term36 A v u f) = (term246 A v u f).
Proof. exact (TRANS (@lem7154326 A v u f) (@lem7154325 A v u f)). Qed.
Lemma lem7154328 {A : Type'} (u : A -> Prop) (f : A -> real) : (term37 A u f) = (term247 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7154327 A v u f)). Qed.
Lemma lem7154329 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154330 {A : Type'} (u : A -> Prop) (f : A -> real) : (term38 A u f) = (term248 A u f).
Proof. exact (MK_COMB (@lem7154329 A) (@lem7154328 A u f)). Qed.
Lemma lem7154331 {A : Type'} (f : A -> real) : (term39 A f) = (term249 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7154330 A u f)). Qed.
Lemma lem7154332 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154333 {A : Type'} (f : A -> real) : (term40 A f) = (term250 A f).
Proof. exact (MK_COMB (@lem7154332 A) (@lem7154331 A f)). Qed.
Lemma lem7154334 {A : Type'} : (term41 A) = (term251 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7154333 A f)). Qed.
Lemma lem7154335 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154336 {A : Type'} : (term11 A) = (term252 A).
Proof. exact (MK_COMB (@lem7154335 A) (@lem7154334 A)). Qed.
Lemma lem7154443 {A : Type'} (P : Prop) (Q : A -> Prop) : (term253 A P Q) = (term254 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7154444 {A : Type'} (P : Prop) (Q : A -> Prop) : (term253 A P Q) = (term254 A P Q).
Proof. exact (@lem7154443 A P Q). Qed.
Lemma lem7154445 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term255 A v u f) = (term256 A v u f).
Proof. exact (@lem7154444 A (term257 A u v) (term237 A v u f)). Qed.
Lemma lem7154446 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term258 A v u f x) = (term231 A v u f x).
Proof. exact (eq_refl (term258 A v u f x)). Qed.
Lemma lem7154447 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term259 A v u f) = (term237 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7154446 A v u f x)). Qed.
Lemma lem7154448 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7154449 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term260 A v u f) = (term238 A v u f).
Proof. exact (MK_COMB (@lem7154448 A) (@lem7154447 A v u f)). Qed.
Lemma lem7154450 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term239 A u v) = (term239 A u v).
Proof. exact (eq_refl (term239 A u v)). Qed.
Lemma lem7154451 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term255 A v u f) = (term241 A v u f).
Proof. exact (MK_COMB (@lem7154450 A u v) (@lem7154449 A v u f)). Qed.
Lemma lem7154452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7154453 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term261 A v u f) = (term262 A v u f).
Proof. exact (MK_COMB (@lem7154452) (@lem7154451 A v u f)). Qed.
Lemma lem7154454 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term258 A v u f x) = (term231 A v u f x).
Proof. exact (eq_refl (term258 A v u f x)). Qed.
Lemma lem7154455 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term239 A u v) = (term239 A u v).
Proof. exact (eq_refl (term239 A u v)). Qed.
Lemma lem7154456 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term263 A v u f x) = (term264 A v u f x).
Proof. exact (MK_COMB (@lem7154455 A u v) (@lem7154454 A v u f x)). Qed.
Lemma lem7154457 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term265 A v u f) = (term266 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7154456 A v u f x)). Qed.
Lemma lem7154458 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7154459 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term256 A v u f) = (term267 A v u f).
Proof. exact (MK_COMB (@lem7154458 A) (@lem7154457 A v u f)). Qed.
Lemma lem7154460 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term255 A v u f) = (term256 A v u f)) = ((term241 A v u f) = (term267 A v u f)).
Proof. exact (MK_COMB (@lem7154453 A v u f) (@lem7154459 A v u f)). Qed.
Lemma lem7154461 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term241 A v u f) = (term267 A v u f).
Proof. exact (EQ_MP (@lem7154460 A v u f) (@lem7154445 A v u f)). Qed.
Lemma lem7154462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7154463 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term244 A v u f) = (term268 A v u f).
Proof. exact (MK_COMB (@lem7154462) (@lem7154461 A v u f)). Qed.
Lemma lem7154464 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((@sum A v f) = (@sum A u f)) = ((@sum A v f) = (@sum A u f)).
Proof. exact (eq_refl ((@sum A v f) = (@sum A u f))). Qed.
Lemma lem7154465 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term246 A v u f) = (term269 A v u f).
Proof. exact (MK_COMB (@lem7154463 A v u f) (@lem7154464 A v u f)). Qed.
Lemma lem7154467 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7154468 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (@lem7154467 A P Q). Qed.
Lemma lem7154469 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term270 A v u f) = (term271 A v u f).
Proof. exact (@lem7154468 A (term266 A v u f) ((@sum A v f) = (@sum A u f))). Qed.
Lemma lem7154470 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term272 A v u f x) = (term264 A v u f x).
Proof. exact (eq_refl (term272 A v u f x)). Qed.
Lemma lem7154471 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term273 A v u f) = (term266 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7154470 A v u f x)). Qed.
Lemma lem7154472 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7154473 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term274 A v u f) = (term267 A v u f).
Proof. exact (MK_COMB (@lem7154472 A) (@lem7154471 A v u f)). Qed.
Lemma lem7154474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7154475 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term275 A v u f) = (term268 A v u f).
Proof. exact (MK_COMB (@lem7154474) (@lem7154473 A v u f)). Qed.
Lemma lem7154476 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((@sum A v f) = (@sum A u f)) = ((@sum A v f) = (@sum A u f)).
Proof. exact (eq_refl ((@sum A v f) = (@sum A u f))). Qed.
Lemma lem7154477 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term270 A v u f) = (term269 A v u f).
Proof. exact (MK_COMB (@lem7154475 A v u f) (@lem7154476 A v u f)). Qed.
Lemma lem7154478 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7154479 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term276 A v u f) = (term277 A v u f).
Proof. exact (MK_COMB (@lem7154478) (@lem7154477 A v u f)). Qed.
Lemma lem7154480 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term272 A v u f x) = (term264 A v u f x).
Proof. exact (eq_refl (term272 A v u f x)). Qed.
Lemma lem7154481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7154482 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term278 A v u f x) = (term279 A v u f x).
Proof. exact (MK_COMB (@lem7154481) (@lem7154480 A v u f x)). Qed.
Lemma lem7154483 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((@sum A v f) = (@sum A u f)) = ((@sum A v f) = (@sum A u f)).
Proof. exact (eq_refl ((@sum A v f) = (@sum A u f))). Qed.
Lemma lem7154484 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term280 A x v u f) = (term281 A x v u f).
Proof. exact (MK_COMB (@lem7154482 A v u f x) (@lem7154483 A v u f)). Qed.
Lemma lem7154485 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term282 A v u f) = (term283 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7154484 A x v u f)). Qed.
Lemma lem7154486 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7154487 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term271 A v u f) = (term284 A v u f).
Proof. exact (MK_COMB (@lem7154486 A) (@lem7154485 A v u f)). Qed.
Lemma lem7154488 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term270 A v u f) = (term271 A v u f)) = ((term269 A v u f) = (term284 A v u f)).
Proof. exact (MK_COMB (@lem7154479 A v u f) (@lem7154487 A v u f)). Qed.
Lemma lem7154489 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term269 A v u f) = (term284 A v u f).
Proof. exact (EQ_MP (@lem7154488 A v u f) (@lem7154469 A v u f)). Qed.
Lemma lem7154490 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term246 A v u f) = (term284 A v u f).
Proof. exact (TRANS (@lem7154465 A v u f) (@lem7154489 A v u f)). Qed.
Lemma lem7154491 {A : Type'} (u : A -> Prop) (f : A -> real) : (term247 A u f) = (term285 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7154490 A v u f)). Qed.
Lemma lem7154492 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154493 {A : Type'} (u : A -> Prop) (f : A -> real) : (term248 A u f) = (term286 A u f).
Proof. exact (MK_COMB (@lem7154492 A) (@lem7154491 A u f)). Qed.
Lemma lem7154495 {A B : Type'} (P : type1413 A B) : (term155 A B P) = (term156 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7154496 {A : Type'} (P : type672 A) : (term157 A P) = (term158 A P).
Proof. exact (@lem7154495 (A -> Prop) A P). Qed.
Lemma lem7154497 {A : Type'} (u : A -> Prop) (f : A -> real) : (term287 A u f) = (term288 A u f).
Proof. exact (@lem7154496 A (term289 A u f)). Qed.
Lemma lem7154498 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term290 A u f v) = (term283 A v u f).
Proof. exact (eq_refl (term290 A u f v)). Qed.
Lemma lem7154499 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7154500 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) (x : A) : (term291 A u f v x) = (term292 A v u f x).
Proof. exact (MK_COMB (@lem7154498 A v u f) (@lem7154499 A x)). Qed.
Lemma lem7154501 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term292 A v u f x) = (term281 A x v u f).
Proof. exact (eq_refl (term292 A v u f x)). Qed.
Lemma lem7154502 {A : Type'} (x : A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term291 A u f v x) = (term281 A x v u f).
Proof. exact (TRANS (@lem7154500 A v u f x) (@lem7154501 A x v u f)). Qed.
Lemma lem7154503 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term293 A u f v) = (term283 A v u f).
Proof. exact (fun_ext (fun x : A => @lem7154502 A x v u f)). Qed.
Lemma lem7154504 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7154505 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term294 A u f v) = (term284 A v u f).
Proof. exact (MK_COMB (@lem7154504 A) (@lem7154503 A v u f)). Qed.
Lemma lem7154506 {A : Type'} (u : A -> Prop) (f : A -> real) : (term295 A u f) = (term285 A u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7154505 A v u f)). Qed.
Lemma lem7154507 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154508 {A : Type'} (u : A -> Prop) (f : A -> real) : (term287 A u f) = (term286 A u f).
Proof. exact (MK_COMB (@lem7154507 A) (@lem7154506 A u f)). Qed.
Lemma lem7154509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7154510 {A : Type'} (u : A -> Prop) (f : A -> real) : (term296 A u f) = (term297 A u f).
Proof. exact (MK_COMB (@lem7154509) (@lem7154508 A u f)). Qed.
Lemma lem7154511 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term290 A u f v) = (term283 A v u f).
Proof. exact (eq_refl (term290 A u f v)). Qed.
Lemma lem7154512 {A : Type'} (x : type684 A) (v : A -> Prop) : (x v) = (x v).
Proof. exact (eq_refl (x v)). Qed.
Lemma lem7154513 {A : Type'} (u : A -> Prop) (f : A -> real) (x : type684 A) (v : A -> Prop) : (term298 A u f x v) = (term299 A u f x v).
Proof. exact (MK_COMB (@lem7154511 A v u f) (@lem7154512 A x v)). Qed.
Lemma lem7154514 {A : Type'} (x : type684 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term299 A u f x v) = (term300 A x v u f).
Proof. exact (eq_refl (term299 A u f x v)). Qed.
Lemma lem7154515 {A : Type'} (x : type684 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term298 A u f x v) = (term300 A x v u f).
Proof. exact (TRANS (@lem7154513 A u f x v) (@lem7154514 A x v u f)). Qed.
Lemma lem7154516 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> real) : (term301 A u f x) = (term302 A x u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7154515 A x v u f)). Qed.
Lemma lem7154517 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154518 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> real) : (term303 A u f x) = (term304 A x u f).
Proof. exact (MK_COMB (@lem7154517 A) (@lem7154516 A x u f)). Qed.
Lemma lem7154519 {A : Type'} (u : A -> Prop) (f : A -> real) : (term305 A u f) = (term306 A u f).
Proof. exact (fun_ext (fun x : type684 A => @lem7154518 A x u f)). Qed.
Lemma lem7154520 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7154521 {A : Type'} (u : A -> Prop) (f : A -> real) : (term288 A u f) = (term307 A u f).
Proof. exact (MK_COMB (@lem7154520 A) (@lem7154519 A u f)). Qed.
Lemma lem7154522 {A : Type'} (u : A -> Prop) (f : A -> real) : ((term287 A u f) = (term288 A u f)) = ((term286 A u f) = (term307 A u f)).
Proof. exact (MK_COMB (@lem7154510 A u f) (@lem7154521 A u f)). Qed.
Lemma lem7154523 {A : Type'} (u : A -> Prop) (f : A -> real) : (term286 A u f) = (term307 A u f).
Proof. exact (EQ_MP (@lem7154522 A u f) (@lem7154497 A u f)). Qed.
Lemma lem7154524 {A : Type'} (u : A -> Prop) (f : A -> real) : (term248 A u f) = (term307 A u f).
Proof. exact (TRANS (@lem7154493 A u f) (@lem7154523 A u f)). Qed.
Lemma lem7154525 {A : Type'} (f : A -> real) : (term249 A f) = (term308 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7154524 A u f)). Qed.
Lemma lem7154526 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154527 {A : Type'} (f : A -> real) : (term250 A f) = (term309 A f).
Proof. exact (MK_COMB (@lem7154526 A) (@lem7154525 A f)). Qed.
Lemma lem7154529 {A B : Type'} (P : type1413 A B) : (term155 A B P) = (term156 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7154530 {A : Type'} (P : type597 A) : (term310 A P) = (term311 A P).
Proof. exact (@lem7154529 (A -> Prop) (type684 A) P). Qed.
Lemma lem7154531 {A : Type'} (f : A -> real) : (term312 A f) = (term313 A f).
Proof. exact (@lem7154530 A (term314 A f)). Qed.
Lemma lem7154532 {A : Type'} (u : A -> Prop) (f : A -> real) : (term315 A f u) = (term306 A u f).
Proof. exact (eq_refl (term315 A f u)). Qed.
Lemma lem7154533 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7154534 {A : Type'} (u : A -> Prop) (f : A -> real) (x : type684 A) : (term316 A f u x) = (term317 A u f x).
Proof. exact (MK_COMB (@lem7154532 A u f) (@lem7154533 A x)). Qed.
Lemma lem7154535 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> real) : (term317 A u f x) = (term304 A x u f).
Proof. exact (eq_refl (term317 A u f x)). Qed.
Lemma lem7154536 {A : Type'} (x : type684 A) (u : A -> Prop) (f : A -> real) : (term316 A f u x) = (term304 A x u f).
Proof. exact (TRANS (@lem7154534 A u f x) (@lem7154535 A x u f)). Qed.
Lemma lem7154537 {A : Type'} (u : A -> Prop) (f : A -> real) : (term318 A f u) = (term306 A u f).
Proof. exact (fun_ext (fun x : type684 A => @lem7154536 A x u f)). Qed.
Lemma lem7154538 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7154539 {A : Type'} (u : A -> Prop) (f : A -> real) : (term319 A f u) = (term307 A u f).
Proof. exact (MK_COMB (@lem7154538 A) (@lem7154537 A u f)). Qed.
Lemma lem7154540 {A : Type'} (f : A -> real) : (term320 A f) = (term308 A f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7154539 A u f)). Qed.
Lemma lem7154541 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154542 {A : Type'} (f : A -> real) : (term312 A f) = (term309 A f).
Proof. exact (MK_COMB (@lem7154541 A) (@lem7154540 A f)). Qed.
Lemma lem7154543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7154544 {A : Type'} (f : A -> real) : (term321 A f) = (term322 A f).
Proof. exact (MK_COMB (@lem7154543) (@lem7154542 A f)). Qed.
Lemma lem7154545 {A : Type'} (u : A -> Prop) (f : A -> real) : (term315 A f u) = (term306 A u f).
Proof. exact (eq_refl (term315 A f u)). Qed.
Lemma lem7154546 {A : Type'} (x : type638 A) (u : A -> Prop) : (x u) = (x u).
Proof. exact (eq_refl (x u)). Qed.
Lemma lem7154547 {A : Type'} (f : A -> real) (x : type638 A) (u : A -> Prop) : (term323 A f x u) = (term324 A f x u).
Proof. exact (MK_COMB (@lem7154545 A u f) (@lem7154546 A x u)). Qed.
Lemma lem7154548 {A : Type'} (x : type638 A) (u : A -> Prop) (f : A -> real) : (term324 A f x u) = (term325 A x u f).
Proof. exact (eq_refl (term324 A f x u)). Qed.
Lemma lem7154549 {A : Type'} (x : type638 A) (u : A -> Prop) (f : A -> real) : (term323 A f x u) = (term325 A x u f).
Proof. exact (TRANS (@lem7154547 A f x u) (@lem7154548 A x u f)). Qed.
Lemma lem7154550 {A : Type'} (x : type638 A) (f : A -> real) : (term326 A f x) = (term327 A x f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7154549 A x u f)). Qed.
Lemma lem7154551 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154552 {A : Type'} (x : type638 A) (f : A -> real) : (term328 A f x) = (term329 A x f).
Proof. exact (MK_COMB (@lem7154551 A) (@lem7154550 A x f)). Qed.
Lemma lem7154553 {A : Type'} (f : A -> real) : (term330 A f) = (term331 A f).
Proof. exact (fun_ext (fun x : type638 A => @lem7154552 A x f)). Qed.
Lemma lem7154554 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem7154555 {A : Type'} (f : A -> real) : (term313 A f) = (term332 A f).
Proof. exact (MK_COMB (@lem7154554 A) (@lem7154553 A f)). Qed.
Lemma lem7154556 {A : Type'} (f : A -> real) : ((term312 A f) = (term313 A f)) = ((term309 A f) = (term332 A f)).
Proof. exact (MK_COMB (@lem7154544 A f) (@lem7154555 A f)). Qed.
Lemma lem7154557 {A : Type'} (f : A -> real) : (term309 A f) = (term332 A f).
Proof. exact (EQ_MP (@lem7154556 A f) (@lem7154531 A f)). Qed.
Lemma lem7154558 {A : Type'} (f : A -> real) : (term250 A f) = (term332 A f).
Proof. exact (TRANS (@lem7154527 A f) (@lem7154557 A f)). Qed.
Lemma lem7154559 {A : Type'} : (term251 A) = (term333 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7154558 A f)). Qed.
Lemma lem7154560 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154561 {A : Type'} : (term252 A) = (term334 A).
Proof. exact (MK_COMB (@lem7154560 A) (@lem7154559 A)). Qed.
Lemma lem7154563 {A B : Type'} (P : type1413 A B) : (term155 A B P) = (term156 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7154564 {A : Type'} (P : type706 A) : (term335 A P) = (term336 A P).
Proof. exact (@lem7154563 (A -> real) (type638 A) P). Qed.
Lemma lem7154565 {A : Type'} : (term337 A) = (term338 A).
Proof. exact (@lem7154564 A (term339 A)). Qed.
Lemma lem7154566 {A : Type'} (f : A -> real) : (term340 A f) = (term331 A f).
Proof. exact (eq_refl (term340 A f)). Qed.
Lemma lem7154567 {A : Type'} (x : type638 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7154568 {A : Type'} (f : A -> real) (x : type638 A) : (term341 A f x) = (term342 A f x).
Proof. exact (MK_COMB (@lem7154566 A f) (@lem7154567 A x)). Qed.
Lemma lem7154569 {A : Type'} (x : type638 A) (f : A -> real) : (term342 A f x) = (term329 A x f).
Proof. exact (eq_refl (term342 A f x)). Qed.
Lemma lem7154570 {A : Type'} (x : type638 A) (f : A -> real) : (term341 A f x) = (term329 A x f).
Proof. exact (TRANS (@lem7154568 A f x) (@lem7154569 A x f)). Qed.
Lemma lem7154571 {A : Type'} (f : A -> real) : (term343 A f) = (term331 A f).
Proof. exact (fun_ext (fun x : type638 A => @lem7154570 A x f)). Qed.
Lemma lem7154572 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem7154573 {A : Type'} (f : A -> real) : (term344 A f) = (term332 A f).
Proof. exact (MK_COMB (@lem7154572 A) (@lem7154571 A f)). Qed.
Lemma lem7154574 {A : Type'} : (term345 A) = (term333 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7154573 A f)). Qed.
Lemma lem7154575 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154576 {A : Type'} : (term337 A) = (term334 A).
Proof. exact (MK_COMB (@lem7154575 A) (@lem7154574 A)). Qed.
Lemma lem7154577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7154578 {A : Type'} : (term346 A) = (term347 A).
Proof. exact (MK_COMB (@lem7154577) (@lem7154576 A)). Qed.
Lemma lem7154579 {A : Type'} (f : A -> real) : (term340 A f) = (term331 A f).
Proof. exact (eq_refl (term340 A f)). Qed.
Lemma lem7154580 {A : Type'} (x : type709 A) (f : A -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7154581 {A : Type'} (x : type709 A) (f : A -> real) : (term348 A x f) = (term349 A x f).
Proof. exact (MK_COMB (@lem7154579 A f) (@lem7154580 A x f)). Qed.
Lemma lem7154582 {A : Type'} (x : type709 A) (f : A -> real) : (term349 A x f) = (term350 A x f).
Proof. exact (eq_refl (term349 A x f)). Qed.
Lemma lem7154583 {A : Type'} (x : type709 A) (f : A -> real) : (term348 A x f) = (term350 A x f).
Proof. exact (TRANS (@lem7154581 A x f) (@lem7154582 A x f)). Qed.
Lemma lem7154584 {A : Type'} (x : type709 A) : (term351 A x) = (term352 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7154583 A x f)). Qed.
Lemma lem7154585 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154586 {A : Type'} (x : type709 A) : (term353 A x) = (term354 A x).
Proof. exact (MK_COMB (@lem7154585 A) (@lem7154584 A x)). Qed.
Lemma lem7154587 {A : Type'} : (term355 A) = (term356 A).
Proof. exact (fun_ext (fun x : type709 A => @lem7154586 A x)). Qed.
Lemma lem7154588 {A : Type'} : (@ex ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A))). Qed.
Lemma lem7154589 {A : Type'} : (term338 A) = (term357 A).
Proof. exact (MK_COMB (@lem7154588 A) (@lem7154587 A)). Qed.
Lemma lem7154590 {A : Type'} : ((term337 A) = (term338 A)) = ((term334 A) = (term357 A)).
Proof. exact (MK_COMB (@lem7154578 A) (@lem7154589 A)). Qed.
Lemma lem7154591 {A : Type'} : (term334 A) = (term357 A).
Proof. exact (EQ_MP (@lem7154590 A) (@lem7154565 A)). Qed.
Lemma lem7154593 {A : Type'} : (term252 A) = (term357 A).
Proof. exact (TRANS (@lem7154561 A) (@lem7154591 A)). Qed.
Lemma lem7154594 {A : Type'} : (term11 A) = (term357 A).
Proof. exact (TRANS (@lem7154336 A) (@lem7154593 A)). Qed.
Lemma lem7154595 {A : Type'} (h1 : term11 A) : term357 A.
Proof. exact (EQ_MP (@lem7154594 A) (@lem7153530 A h1)). Qed.
Lemma lem7154596 {A : Type'} (x : type709 A) (h1 : term354 A x) : term354 A x.
Proof. exact (h1). Qed.
Lemma lem7154597 {A : Type'} (x' : type711 A) (h1 : term226 A x') : term226 A x'.
Proof. exact (h1). Qed.
Lemma lem7154599 {A : Type'} (f : A -> real) (g : A -> real) (h1 : term106 A f g) : term106 A f g.
Proof. exact (h1). Qed.
Lemma lem7154600 {A : Type'} (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term99 A s f g) : term99 A s f g.
Proof. exact (h1). Qed.
Lemma lem7154601 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term89 A s f t g.
Proof. exact (h1). Qed.
Lemma lem7154602 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7154609 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154610 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7154609 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7154611 {A : Type'} (v : A -> Prop) : (@sum A v) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) v).
Proof. exact (@lem7154610 A (@sum A) v). Qed.
Lemma lem7154612 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7154613 {A : Type'} (v : A -> Prop) (f : A -> real) : (@sum A v f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) v f).
Proof. exact (MK_COMB (@lem7154611 A v) (@lem7154612 A f)). Qed.
Lemma lem7154615 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154616 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7154615 (A -> real) real f x). Qed.
Lemma lem7154617 {A : Type'} (v : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) v f) = (term358 A v f).
Proof. exact (@lem7154616 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) v) f). Qed.
Lemma lem7154619 {A : Type'} (v : A -> Prop) (f : A -> real) : (@sum A v f) = (term358 A v f).
Proof. exact (TRANS (@lem7154613 A v f) (@lem7154617 A v f)). Qed.
Lemma lem7154626 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154627 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7154626 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7154628 {A : Type'} (u : A -> Prop) : (@sum A u) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) u).
Proof. exact (@lem7154627 A (@sum A) u). Qed.
Lemma lem7154629 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7154630 {A : Type'} (u : A -> Prop) (f : A -> real) : (@sum A u f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) u f).
Proof. exact (MK_COMB (@lem7154628 A u) (@lem7154629 A f)). Qed.
Lemma lem7154632 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154633 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7154632 (A -> real) real f x). Qed.
Lemma lem7154634 {A : Type'} (u : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) u f) = (term358 A u f).
Proof. exact (@lem7154633 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) u) f). Qed.
Lemma lem7154636 {A : Type'} (u : A -> Prop) (f : A -> real) : (@sum A u f) = (term358 A u f).
Proof. exact (TRANS (@lem7154630 A u f) (@lem7154634 A u f)). Qed.
Lemma lem7154637 {A : Type'} (v : A -> Prop) (f : A -> real) : (term359 A v f) = (term360 A v f).
Proof. exact (MK_COMB (@lem7154602) (@lem7154619 A v f)). Qed.
Lemma lem7154638 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((@sum A v f) = (@sum A u f)) = ((term358 A v f) = (term358 A u f)).
Proof. exact (MK_COMB (@lem7154637 A v f) (@lem7154636 A u f)). Qed.
Lemma lem7154639 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7154640 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7154641 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7154650 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154651 {A : Type'} (f : type709 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7154650 (A -> real) (type638 A) f x). Qed.
Lemma lem7154652 {A : Type'} (x : type709 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7154651 A x f). Qed.
Lemma lem7154653 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7154654 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (x f u) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f u).
Proof. exact (MK_COMB (@lem7154652 A x f) (@lem7154653 A u)). Qed.
Lemma lem7154656 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154657 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7154656 (A -> Prop) (type684 A) f x). Qed.
Lemma lem7154658 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f u) = (term361 A x f u).
Proof. exact (@lem7154657 A (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f) u). Qed.
Lemma lem7154659 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (x f u) = (term361 A x f u).
Proof. exact (TRANS (@lem7154654 A x f u) (@lem7154658 A x f u)). Qed.
Lemma lem7154660 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7154661 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term362 A x f u v).
Proof. exact (MK_COMB (@lem7154659 A x f u) (@lem7154660 A v)). Qed.
Lemma lem7154663 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154664 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7154663 (A -> Prop) A f x). Qed.
Lemma lem7154665 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term362 A x f u v) = (term363 A x f u v).
Proof. exact (@lem7154664 A (term361 A x f u) v). Qed.
Lemma lem7154667 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term363 A x f u v).
Proof. exact (TRANS (@lem7154661 A x f u v) (@lem7154665 A x f u v)). Qed.
Lemma lem7154668 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term364 A x f u v) = (term365 A x f u v).
Proof. exact (MK_COMB (@lem7154641 A f) (@lem7154667 A x f u v)). Qed.
Lemma lem7154670 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154671 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7154670 A real f x). Qed.
Lemma lem7154672 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term365 A x f u v) = (term366 A x f u v).
Proof. exact (@lem7154671 A f (term363 A x f u v)). Qed.
Lemma lem7154673 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term364 A x f u v) = (term366 A x f u v).
Proof. exact (TRANS (@lem7154668 A x f u v) (@lem7154672 A x f u v)). Qed.
Lemma lem7154674 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7154679 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154680 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7154679 nat nat f x). Qed.
Lemma lem7154682 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7154680 NUMERAL 0). Qed.
Lemma lem7154683 : term73 = term367.
Proof. exact (MK_COMB (@lem7154674) (@lem7154682)). Qed.
Lemma lem7154685 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154686 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7154685 nat real f x). Qed.
Lemma lem7154687 : term367 = term368.
Proof. exact (@lem7154686 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7154688 : term73 = term368.
Proof. exact (TRANS (@lem7154683) (@lem7154687)). Qed.
Lemma lem7154689 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term369 A x f u v) = (term370 A x f u v).
Proof. exact (MK_COMB (@lem7154640) (@lem7154673 A x f u v)). Qed.
Lemma lem7154690 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : ((term364 A x f u v) = term73) = ((term366 A x f u v) = term368).
Proof. exact (MK_COMB (@lem7154689 A x f u v) (@lem7154688)). Qed.
Lemma lem7154691 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term371 A x f u v) = (term372 A x f u v).
Proof. exact (MK_COMB (@lem7154639) (@lem7154690 A x f u v)). Qed.
Lemma lem7154692 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7154693 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem7154702 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154703 {A : Type'} (f : type709 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7154702 (A -> real) (type638 A) f x). Qed.
Lemma lem7154704 {A : Type'} (x : type709 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7154703 A x f). Qed.
Lemma lem7154705 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7154706 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (x f u) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f u).
Proof. exact (MK_COMB (@lem7154704 A x f) (@lem7154705 A u)). Qed.
Lemma lem7154708 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154709 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7154708 (A -> Prop) (type684 A) f x). Qed.
Lemma lem7154710 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f u) = (term361 A x f u).
Proof. exact (@lem7154709 A (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f) u). Qed.
Lemma lem7154711 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (x f u) = (term361 A x f u).
Proof. exact (TRANS (@lem7154706 A x f u) (@lem7154710 A x f u)). Qed.
Lemma lem7154712 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7154713 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term362 A x f u v).
Proof. exact (MK_COMB (@lem7154711 A x f u) (@lem7154712 A v)). Qed.
Lemma lem7154715 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154716 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7154715 (A -> Prop) A f x). Qed.
Lemma lem7154717 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term362 A x f u v) = (term363 A x f u v).
Proof. exact (@lem7154716 A (term361 A x f u) v). Qed.
Lemma lem7154719 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term363 A x f u v).
Proof. exact (TRANS (@lem7154713 A x f u v) (@lem7154717 A x f u v)). Qed.
Lemma lem7154720 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7154721 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term373 A x f u v) = (term374 A x f u v).
Proof. exact (MK_COMB (@lem7154693 A) (@lem7154719 A x f u v)). Qed.
Lemma lem7154722 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term375 A x f v u) = (term376 A x f v u).
Proof. exact (MK_COMB (@lem7154721 A x f u v) (@lem7154720 A u)). Qed.
Lemma lem7154724 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154725 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7154724 A (type686 A) f x). Qed.
Lemma lem7154726 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term374 A x f u v) = (term377 A x f u v).
Proof. exact (@lem7154725 A (@IN A) (term363 A x f u v)). Qed.
Lemma lem7154727 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7154728 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term376 A x f v u) = (term378 A x f v u).
Proof. exact (MK_COMB (@lem7154726 A x f u v) (@lem7154727 A u)). Qed.
Lemma lem7154730 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154731 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7154730 (A -> Prop) Prop f x). Qed.
Lemma lem7154732 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term378 A x f v u) = (term379 A x f v u).
Proof. exact (@lem7154731 A (term377 A x f u v) u). Qed.
Lemma lem7154733 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term376 A x f v u) = (term379 A x f v u).
Proof. exact (TRANS (@lem7154728 A x f v u) (@lem7154732 A x f v u)). Qed.
Lemma lem7154734 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term375 A x f v u) = (term379 A x f v u).
Proof. exact (TRANS (@lem7154722 A x f v u) (@lem7154733 A x f v u)). Qed.
Lemma lem7154735 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term380 A x f v u) = (term381 A x f v u).
Proof. exact (MK_COMB (@lem7154692) (@lem7154734 A x f v u)). Qed.
Lemma lem7154736 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem7154745 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154746 {A : Type'} (f : type709 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7154745 (A -> real) (type638 A) f x). Qed.
Lemma lem7154747 {A : Type'} (x : type709 A) (f : A -> real) : (x f) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f).
Proof. exact (@lem7154746 A x f). Qed.
Lemma lem7154748 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem7154749 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (x f u) = (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f u).
Proof. exact (MK_COMB (@lem7154747 A x f) (@lem7154748 A u)). Qed.
Lemma lem7154751 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154752 {A : Type'} (f : type638 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7154751 (A -> Prop) (type684 A) f x). Qed.
Lemma lem7154753 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f u) = (term361 A x f u).
Proof. exact (@lem7154752 A (@I ((A -> real) -> (A -> Prop) -> (A -> Prop) -> A) x f) u). Qed.
Lemma lem7154754 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) : (x f u) = (term361 A x f u).
Proof. exact (TRANS (@lem7154749 A x f u) (@lem7154753 A x f u)). Qed.
Lemma lem7154755 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7154756 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term362 A x f u v).
Proof. exact (MK_COMB (@lem7154754 A x f u) (@lem7154755 A v)). Qed.
Lemma lem7154758 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154759 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7154758 (A -> Prop) A f x). Qed.
Lemma lem7154760 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term362 A x f u v) = (term363 A x f u v).
Proof. exact (@lem7154759 A (term361 A x f u) v). Qed.
Lemma lem7154762 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (x f u v) = (term363 A x f u v).
Proof. exact (TRANS (@lem7154756 A x f u v) (@lem7154760 A x f u v)). Qed.
Lemma lem7154763 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7154764 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term373 A x f u v) = (term374 A x f u v).
Proof. exact (MK_COMB (@lem7154736 A) (@lem7154762 A x f u v)). Qed.
Lemma lem7154765 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term382 A x f u v) = (term383 A x f u v).
Proof. exact (MK_COMB (@lem7154764 A x f u v) (@lem7154763 A v)). Qed.
Lemma lem7154767 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154768 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7154767 A (type686 A) f x). Qed.
Lemma lem7154769 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term374 A x f u v) = (term377 A x f u v).
Proof. exact (@lem7154768 A (@IN A) (term363 A x f u v)). Qed.
Lemma lem7154770 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7154771 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term383 A x f u v) = (term384 A x f u v).
Proof. exact (MK_COMB (@lem7154769 A x f u v) (@lem7154770 A v)). Qed.
Lemma lem7154773 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154774 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7154773 (A -> Prop) Prop f x). Qed.
Lemma lem7154775 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term384 A x f u v) = (term385 A x f u v).
Proof. exact (@lem7154774 A (term377 A x f u v) v). Qed.
Lemma lem7154776 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term383 A x f u v) = (term385 A x f u v).
Proof. exact (TRANS (@lem7154771 A x f u v) (@lem7154775 A x f u v)). Qed.
Lemma lem7154777 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term382 A x f u v) = (term385 A x f u v).
Proof. exact (TRANS (@lem7154765 A x f u v) (@lem7154776 A x f u v)). Qed.
Lemma lem7154778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7154779 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term386 A x f u v) = (term387 A x f u v).
Proof. exact (MK_COMB (@lem7154778) (@lem7154777 A x f u v)). Qed.
Lemma lem7154780 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term388 A x f v u) = (term389 A x f v u).
Proof. exact (MK_COMB (@lem7154779 A x f u v) (@lem7154735 A x f v u)). Qed.
Lemma lem7154781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7154782 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term390 A x f v u) = (term391 A x f v u).
Proof. exact (MK_COMB (@lem7154781) (@lem7154780 A x f v u)). Qed.
Lemma lem7154783 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term392 A x f u v) = (term393 A x f u v).
Proof. exact (MK_COMB (@lem7154782 A x f v u) (@lem7154691 A x f u v)). Qed.
Lemma lem7154784 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7154791 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154792 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7154791 (A -> Prop) (type686 A) f x). Qed.
Lemma lem7154793 {A : Type'} (u : A -> Prop) : (@SUBSET A u) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) u).
Proof. exact (@lem7154792 A (@SUBSET A) u). Qed.
Lemma lem7154794 {A : Type'} (v : A -> Prop) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem7154795 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@SUBSET A u v) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) u v).
Proof. exact (MK_COMB (@lem7154793 A u) (@lem7154794 A v)). Qed.
Lemma lem7154797 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154798 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7154797 (A -> Prop) Prop f x). Qed.
Lemma lem7154799 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) u v) = (term394 A u v).
Proof. exact (@lem7154798 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) u) v). Qed.
Lemma lem7154801 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (@SUBSET A u v) = (term394 A u v).
Proof. exact (TRANS (@lem7154795 A u v) (@lem7154799 A u v)). Qed.
Lemma lem7154802 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term257 A u v) = (term395 A u v).
Proof. exact (MK_COMB (@lem7154784) (@lem7154801 A u v)). Qed.
Lemma lem7154803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7154804 {A : Type'} (u : A -> Prop) (v : A -> Prop) : (term239 A u v) = (term396 A u v).
Proof. exact (MK_COMB (@lem7154803) (@lem7154802 A u v)). Qed.
Lemma lem7154805 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term397 A x f u v) = (term398 A x f u v).
Proof. exact (MK_COMB (@lem7154804 A u v) (@lem7154783 A x f u v)). Qed.
Lemma lem7154806 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7154807 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term399 A x f u v) = (term400 A x f u v).
Proof. exact (MK_COMB (@lem7154806) (@lem7154805 A x f u v)). Qed.
Lemma lem7154808 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term401 A x v u f) = (term402 A x v u f).
Proof. exact (MK_COMB (@lem7154807 A x f u v) (@lem7154638 A v u f)). Qed.
Lemma lem7154809 {A : Type'} (x : type709 A) (u : A -> Prop) (f : A -> real) : (term403 A x u f) = (term404 A x u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7154808 A x v u f)). Qed.
Lemma lem7154810 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154811 {A : Type'} (x : type709 A) (u : A -> Prop) (f : A -> real) : (term405 A x u f) = (term406 A x u f).
Proof. exact (MK_COMB (@lem7154810 A) (@lem7154809 A x u f)). Qed.
Lemma lem7154812 {A : Type'} (x : type709 A) (f : A -> real) : (term407 A x f) = (term408 A x f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7154811 A x u f)). Qed.
Lemma lem7154813 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154814 {A : Type'} (x : type709 A) (f : A -> real) : (term350 A x f) = (term409 A x f).
Proof. exact (MK_COMB (@lem7154813 A) (@lem7154812 A x f)). Qed.
Lemma lem7154815 {A : Type'} (x : type709 A) : (term352 A x) = (term410 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7154814 A x f)). Qed.
Lemma lem7154816 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154817 {A : Type'} (x : type709 A) : (term354 A x) = (term411 A x).
Proof. exact (MK_COMB (@lem7154816 A) (@lem7154815 A x)). Qed.
Lemma lem7154818 {A : Type'} (x : type709 A) (h1 : term354 A x) : term411 A x.
Proof. exact (EQ_MP (@lem7154817 A x) (@lem7154596 A x h1)). Qed.
Lemma lem7154819 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7154826 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154827 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7154826 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7154828 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7154827 A (@sum A) s). Qed.
Lemma lem7154829 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7154830 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7154828 A s) (@lem7154829 A f)). Qed.
Lemma lem7154832 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154833 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7154832 (A -> real) real f x). Qed.
Lemma lem7154834 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term358 A s f).
Proof. exact (@lem7154833 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7154836 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term358 A s f).
Proof. exact (TRANS (@lem7154830 A s f) (@lem7154834 A s f)). Qed.
Lemma lem7154843 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154844 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7154843 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7154845 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7154844 A (@sum A) s). Qed.
Lemma lem7154846 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7154847 {A : Type'} (s : A -> Prop) (g : A -> real) : (@sum A s g) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s g).
Proof. exact (MK_COMB (@lem7154845 A s) (@lem7154846 A g)). Qed.
Lemma lem7154849 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154850 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7154849 (A -> real) real f x). Qed.
Lemma lem7154851 {A : Type'} (s : A -> Prop) (g : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s g) = (term358 A s g).
Proof. exact (@lem7154850 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) g). Qed.
Lemma lem7154853 {A : Type'} (s : A -> Prop) (g : A -> real) : (@sum A s g) = (term358 A s g).
Proof. exact (TRANS (@lem7154847 A s g) (@lem7154851 A s g)). Qed.
Lemma lem7154854 {A : Type'} (s : A -> Prop) (f : A -> real) : (term359 A s f) = (term360 A s f).
Proof. exact (MK_COMB (@lem7154819) (@lem7154836 A s f)). Qed.
Lemma lem7154855 {A : Type'} (f : A -> real) (s : A -> Prop) (g : A -> real) : ((@sum A s f) = (@sum A s g)) = ((term358 A s f) = (term358 A s g)).
Proof. exact (MK_COMB (@lem7154854 A s f) (@lem7154853 A s g)). Qed.
Lemma lem7154856 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7154857 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7154858 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7154867 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154868 {A : Type'} (f : type711 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7154867 (A -> real) (type710 A) f x). Qed.
Lemma lem7154869 {A : Type'} (x' : type711 A) (f : A -> real) : (x' f) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x' f).
Proof. exact (@lem7154868 A x' f). Qed.
Lemma lem7154870 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7154871 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (x' f g) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x' f g).
Proof. exact (MK_COMB (@lem7154869 A x' f) (@lem7154870 A g)). Qed.
Lemma lem7154873 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154874 {A : Type'} (f : type710 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7154873 (A -> real) (type684 A) f x). Qed.
Lemma lem7154875 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x' f g) = (term412 A x' f g).
Proof. exact (@lem7154874 A (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x' f) g). Qed.
Lemma lem7154876 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (x' f g) = (term412 A x' f g).
Proof. exact (TRANS (@lem7154871 A x' f g) (@lem7154875 A x' f g)). Qed.
Lemma lem7154877 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7154878 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x' f g s) = (term413 A x' f g s).
Proof. exact (MK_COMB (@lem7154876 A x' f g) (@lem7154877 A s)). Qed.
Lemma lem7154880 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154881 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7154880 (A -> Prop) A f x). Qed.
Lemma lem7154882 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term413 A x' f g s) = (term414 A x' f g s).
Proof. exact (@lem7154881 A (term412 A x' f g) s). Qed.
Lemma lem7154884 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x' f g s) = (term414 A x' f g s).
Proof. exact (TRANS (@lem7154878 A x' f g s) (@lem7154882 A x' f g s)). Qed.
Lemma lem7154885 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term415 A x' f g s) = (term416 A x' f g s).
Proof. exact (MK_COMB (@lem7154858 A f) (@lem7154884 A x' f g s)). Qed.
Lemma lem7154887 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154888 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7154887 A real f x). Qed.
Lemma lem7154889 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term416 A x' f g s) = (term417 A x' f g s).
Proof. exact (@lem7154888 A f (term414 A x' f g s)). Qed.
Lemma lem7154890 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term415 A x' f g s) = (term417 A x' f g s).
Proof. exact (TRANS (@lem7154885 A x' f g s) (@lem7154889 A x' f g s)). Qed.
Lemma lem7154891 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7154900 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154901 {A : Type'} (f : type711 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7154900 (A -> real) (type710 A) f x). Qed.
Lemma lem7154902 {A : Type'} (x' : type711 A) (f : A -> real) : (x' f) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x' f).
Proof. exact (@lem7154901 A x' f). Qed.
Lemma lem7154903 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7154904 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (x' f g) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x' f g).
Proof. exact (MK_COMB (@lem7154902 A x' f) (@lem7154903 A g)). Qed.
Lemma lem7154906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154907 {A : Type'} (f : type710 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7154906 (A -> real) (type684 A) f x). Qed.
Lemma lem7154908 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x' f g) = (term412 A x' f g).
Proof. exact (@lem7154907 A (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x' f) g). Qed.
Lemma lem7154909 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (x' f g) = (term412 A x' f g).
Proof. exact (TRANS (@lem7154904 A x' f g) (@lem7154908 A x' f g)). Qed.
Lemma lem7154910 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7154911 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x' f g s) = (term413 A x' f g s).
Proof. exact (MK_COMB (@lem7154909 A x' f g) (@lem7154910 A s)). Qed.
Lemma lem7154913 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154914 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7154913 (A -> Prop) A f x). Qed.
Lemma lem7154915 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term413 A x' f g s) = (term414 A x' f g s).
Proof. exact (@lem7154914 A (term412 A x' f g) s). Qed.
Lemma lem7154917 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x' f g s) = (term414 A x' f g s).
Proof. exact (TRANS (@lem7154911 A x' f g s) (@lem7154915 A x' f g s)). Qed.
Lemma lem7154918 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term418 A x' f g s) = (term419 A x' f g s).
Proof. exact (MK_COMB (@lem7154891 A g) (@lem7154917 A x' f g s)). Qed.
Lemma lem7154920 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154921 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7154920 A real f x). Qed.
Lemma lem7154922 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term419 A x' f g s) = (term420 A x' f g s).
Proof. exact (@lem7154921 A g (term414 A x' f g s)). Qed.
Lemma lem7154923 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term418 A x' f g s) = (term420 A x' f g s).
Proof. exact (TRANS (@lem7154918 A x' f g s) (@lem7154922 A x' f g s)). Qed.
Lemma lem7154924 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term421 A x' f g s) = (term422 A x' f g s).
Proof. exact (MK_COMB (@lem7154857) (@lem7154890 A x' f g s)). Qed.
Lemma lem7154925 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : ((term415 A x' f g s) = (term418 A x' f g s)) = ((term417 A x' f g s) = (term420 A x' f g s)).
Proof. exact (MK_COMB (@lem7154924 A x' f g s) (@lem7154923 A x' f g s)). Qed.
Lemma lem7154926 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term423 A x' f g s) = (term424 A x' f g s).
Proof. exact (MK_COMB (@lem7154856) (@lem7154925 A x' f g s)). Qed.
Lemma lem7154927 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem7154936 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154937 {A : Type'} (f : type711 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7154936 (A -> real) (type710 A) f x). Qed.
Lemma lem7154938 {A : Type'} (x' : type711 A) (f : A -> real) : (x' f) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x' f).
Proof. exact (@lem7154937 A x' f). Qed.
Lemma lem7154939 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7154940 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (x' f g) = (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x' f g).
Proof. exact (MK_COMB (@lem7154938 A x' f) (@lem7154939 A g)). Qed.
Lemma lem7154942 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154943 {A : Type'} (f : type710 A) (x : A -> real) : (f x) = (@I ((A -> real) -> (A -> Prop) -> A) f x).
Proof. exact (@lem7154942 (A -> real) (type684 A) f x). Qed.
Lemma lem7154944 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x' f g) = (term412 A x' f g).
Proof. exact (@lem7154943 A (@I ((A -> real) -> (A -> real) -> (A -> Prop) -> A) x' f) g). Qed.
Lemma lem7154945 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (x' f g) = (term412 A x' f g).
Proof. exact (TRANS (@lem7154940 A x' f g) (@lem7154944 A x' f g)). Qed.
Lemma lem7154946 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7154947 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x' f g s) = (term413 A x' f g s).
Proof. exact (MK_COMB (@lem7154945 A x' f g) (@lem7154946 A s)). Qed.
Lemma lem7154949 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154950 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem7154949 (A -> Prop) A f x). Qed.
Lemma lem7154951 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term413 A x' f g s) = (term414 A x' f g s).
Proof. exact (@lem7154950 A (term412 A x' f g) s). Qed.
Lemma lem7154953 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (x' f g s) = (term414 A x' f g s).
Proof. exact (TRANS (@lem7154947 A x' f g s) (@lem7154951 A x' f g s)). Qed.
Lemma lem7154954 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7154955 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term425 A x' f g s) = (term426 A x' f g s).
Proof. exact (MK_COMB (@lem7154927 A) (@lem7154953 A x' f g s)). Qed.
Lemma lem7154956 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term427 A x' f g s) = (term428 A x' f g s).
Proof. exact (MK_COMB (@lem7154955 A x' f g s) (@lem7154954 A s)). Qed.
Lemma lem7154958 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154959 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7154958 A (type686 A) f x). Qed.
Lemma lem7154960 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term426 A x' f g s) = (term429 A x' f g s).
Proof. exact (@lem7154959 A (@IN A) (term414 A x' f g s)). Qed.
Lemma lem7154961 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7154962 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term428 A x' f g s) = (term430 A x' f g s).
Proof. exact (MK_COMB (@lem7154960 A x' f g s) (@lem7154961 A s)). Qed.
Lemma lem7154964 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7154965 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7154964 (A -> Prop) Prop f x). Qed.
Lemma lem7154966 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term430 A x' f g s) = (term431 A x' f g s).
Proof. exact (@lem7154965 A (term429 A x' f g s) s). Qed.
Lemma lem7154967 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term428 A x' f g s) = (term431 A x' f g s).
Proof. exact (TRANS (@lem7154962 A x' f g s) (@lem7154966 A x' f g s)). Qed.
Lemma lem7154968 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term427 A x' f g s) = (term431 A x' f g s).
Proof. exact (TRANS (@lem7154956 A x' f g s) (@lem7154967 A x' f g s)). Qed.
Lemma lem7154969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7154970 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term432 A x' f g s) = (term433 A x' f g s).
Proof. exact (MK_COMB (@lem7154969) (@lem7154968 A x' f g s)). Qed.
Lemma lem7154971 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term434 A x' f g s) = (term435 A x' f g s).
Proof. exact (MK_COMB (@lem7154970 A x' f g s) (@lem7154926 A x' f g s)). Qed.
Lemma lem7154972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7154973 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (s : A -> Prop) : (term436 A x' f g s) = (term437 A x' f g s).
Proof. exact (MK_COMB (@lem7154972) (@lem7154971 A x' f g s)). Qed.
Lemma lem7154974 {A : Type'} (x' : type711 A) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term438 A x' f s g) = (term439 A x' f s g).
Proof. exact (MK_COMB (@lem7154973 A x' f g s) (@lem7154855 A f s g)). Qed.
Lemma lem7154975 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (term440 A x' f g) = (term441 A x' f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7154974 A x' f s g)). Qed.
Lemma lem7154976 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7154977 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (term442 A x' f g) = (term443 A x' f g).
Proof. exact (MK_COMB (@lem7154976 A) (@lem7154975 A x' f g)). Qed.
Lemma lem7154978 {A : Type'} (x' : type711 A) (f : A -> real) : (term444 A x' f) = (term445 A x' f).
Proof. exact (fun_ext (fun g : A -> real => @lem7154977 A x' f g)). Qed.
Lemma lem7154979 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154980 {A : Type'} (x' : type711 A) (f : A -> real) : (term222 A x' f) = (term446 A x' f).
Proof. exact (MK_COMB (@lem7154979 A) (@lem7154978 A x' f)). Qed.
Lemma lem7154981 {A : Type'} (x' : type711 A) : (term224 A x') = (term447 A x').
Proof. exact (fun_ext (fun f : A -> real => @lem7154980 A x' f)). Qed.
Lemma lem7154982 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7154983 {A : Type'} (x' : type711 A) : (term226 A x') = (term448 A x').
Proof. exact (MK_COMB (@lem7154982 A) (@lem7154981 A x')). Qed.
Lemma lem7154984 {A : Type'} (x' : type711 A) (h1 : term226 A x') : term448 A x'.
Proof. exact (EQ_MP (@lem7154983 A x') (@lem7154597 A x' h1)). Qed.
Lemma lem7155151 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7155152 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7155159 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155160 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7155159 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7155161 {A : Type'} (s : A -> Prop) : (@sum A s) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s).
Proof. exact (@lem7155160 A (@sum A) s). Qed.
Lemma lem7155162 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7155163 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f).
Proof. exact (MK_COMB (@lem7155161 A s) (@lem7155162 A f)). Qed.
Lemma lem7155165 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155166 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7155165 (A -> real) real f x). Qed.
Lemma lem7155167 {A : Type'} (s : A -> Prop) (f : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s f) = (term358 A s f).
Proof. exact (@lem7155166 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) s) f). Qed.
Lemma lem7155169 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term358 A s f).
Proof. exact (TRANS (@lem7155163 A s f) (@lem7155167 A s f)). Qed.
Lemma lem7155176 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155177 {A : Type'} (f : type646 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> real) -> real) f x).
Proof. exact (@lem7155176 (A -> Prop) (type717 A) f x). Qed.
Lemma lem7155178 {A : Type'} (t : A -> Prop) : (@sum A t) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) t).
Proof. exact (@lem7155177 A (@sum A) t). Qed.
Lemma lem7155179 {A : Type'} (g : A -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7155180 {A : Type'} (t : A -> Prop) (g : A -> real) : (@sum A t g) = (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) t g).
Proof. exact (MK_COMB (@lem7155178 A t) (@lem7155179 A g)). Qed.
Lemma lem7155182 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155183 {A : Type'} (f : type717 A) (x : A -> real) : (f x) = (@I ((A -> real) -> real) f x).
Proof. exact (@lem7155182 (A -> real) real f x). Qed.
Lemma lem7155184 {A : Type'} (t : A -> Prop) (g : A -> real) : (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) t g) = (term358 A t g).
Proof. exact (@lem7155183 A (@I ((A -> Prop) -> (A -> real) -> real) (@sum A) t) g). Qed.
Lemma lem7155186 {A : Type'} (t : A -> Prop) (g : A -> real) : (@sum A t g) = (term358 A t g).
Proof. exact (TRANS (@lem7155180 A t g) (@lem7155184 A t g)). Qed.
Lemma lem7155187 {A : Type'} (s : A -> Prop) (f : A -> real) : (term359 A s f) = (term360 A s f).
Proof. exact (MK_COMB (@lem7155152) (@lem7155169 A s f)). Qed.
Lemma lem7155188 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : ((@sum A s f) = (@sum A t g)) = ((term358 A s f) = (term358 A t g)).
Proof. exact (MK_COMB (@lem7155187 A s f) (@lem7155186 A t g)). Qed.
Lemma lem7155189 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : (term85 A s f t g) = (term449 A s f t g).
Proof. exact (MK_COMB (@lem7155151) (@lem7155188 A s f t g)). Qed.
Lemma lem7155190 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7155195 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155197 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7155195 A real f x). Qed.
Lemma lem7155198 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7155203 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155204 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7155203 nat nat f x). Qed.
Lemma lem7155206 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7155204 NUMERAL 0). Qed.
Lemma lem7155207 : term73 = term367.
Proof. exact (MK_COMB (@lem7155198) (@lem7155206)). Qed.
Lemma lem7155209 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155210 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7155209 nat real f x). Qed.
Lemma lem7155211 : term367 = term368.
Proof. exact (@lem7155210 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7155212 : term73 = term368.
Proof. exact (TRANS (@lem7155207) (@lem7155211)). Qed.
Lemma lem7155213 {A : Type'} (f : A -> real) (x : A) : (term450 A f x) = (term451 A f x).
Proof. exact (MK_COMB (@lem7155190) (@lem7155197 A f x)). Qed.
Lemma lem7155214 {A : Type'} (f : A -> real) (x : A) : ((f x) = term73) = ((@I (A -> real) f x) = term368).
Proof. exact (MK_COMB (@lem7155213 A f x) (@lem7155212)). Qed.
Lemma lem7155221 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155222 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7155221 A (type686 A) f x). Qed.
Lemma lem7155223 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7155222 A (@IN A) x). Qed.
Lemma lem7155224 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7155225 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x t).
Proof. exact (MK_COMB (@lem7155223 A x) (@lem7155224 A t)). Qed.
Lemma lem7155227 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155228 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7155227 (A -> Prop) Prop f x). Qed.
Lemma lem7155229 {A : Type'} (x : A) (t : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x t) = (term452 A x t).
Proof. exact (@lem7155228 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) t). Qed.
Lemma lem7155231 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (term452 A x t).
Proof. exact (TRANS (@lem7155225 A x t) (@lem7155229 A x t)). Qed.
Lemma lem7155232 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7155239 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155240 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7155239 A (type686 A) f x). Qed.
Lemma lem7155241 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7155240 A (@IN A) x). Qed.
Lemma lem7155242 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7155243 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem7155241 A x) (@lem7155242 A s)). Qed.
Lemma lem7155245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155246 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7155245 (A -> Prop) Prop f x). Qed.
Lemma lem7155247 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term452 A x s).
Proof. exact (@lem7155246 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem7155249 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term452 A x s).
Proof. exact (TRANS (@lem7155243 A x s) (@lem7155247 A x s)). Qed.
Lemma lem7155250 {A : Type'} (x : A) (s : A -> Prop) : (term72 A x s) = (term453 A x s).
Proof. exact (MK_COMB (@lem7155232) (@lem7155249 A x s)). Qed.
Lemma lem7155251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7155252 {A : Type'} (x : A) (s : A -> Prop) : (term68 A x s) = (term454 A x s).
Proof. exact (MK_COMB (@lem7155251) (@lem7155250 A x s)). Qed.
Lemma lem7155253 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term70 A s x t) = (term455 A s x t).
Proof. exact (MK_COMB (@lem7155252 A x s) (@lem7155231 A x t)). Qed.
Lemma lem7155254 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7155255 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term75 A s x t) = (term456 A s x t).
Proof. exact (MK_COMB (@lem7155254) (@lem7155253 A s x t)). Qed.
Lemma lem7155256 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (x : A) : (term77 A s t f x) = (term457 A s t f x).
Proof. exact (MK_COMB (@lem7155255 A s x t) (@lem7155214 A f x)). Qed.
Lemma lem7155257 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term79 A s t f) = (term458 A s t f).
Proof. exact (fun_ext (fun x : A => @lem7155256 A s t f x)). Qed.
Lemma lem7155258 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7155259 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term80 A s t f) = (term459 A s t f).
Proof. exact (MK_COMB (@lem7155258 A) (@lem7155257 A s t f)). Qed.
Lemma lem7155260 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7155265 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155267 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7155265 A real f x). Qed.
Lemma lem7155272 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155273 {A : Type'} (f : A -> real) (x : A) : (f x) = (@I (A -> real) f x).
Proof. exact (@lem7155272 A real f x). Qed.
Lemma lem7155275 {A : Type'} (g : A -> real) (x : A) : (g x) = (@I (A -> real) g x).
Proof. exact (@lem7155273 A g x). Qed.
Lemma lem7155276 {A : Type'} (f : A -> real) (x : A) : (term450 A f x) = (term451 A f x).
Proof. exact (MK_COMB (@lem7155260) (@lem7155267 A f x)). Qed.
Lemma lem7155277 {A : Type'} (f : A -> real) (g : A -> real) (x : A) : ((f x) = (g x)) = ((@I (A -> real) f x) = (@I (A -> real) g x)).
Proof. exact (MK_COMB (@lem7155276 A f x) (@lem7155275 A g x)). Qed.
Lemma lem7155278 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7155285 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155286 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7155285 A (type686 A) f x). Qed.
Lemma lem7155287 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem7155286 A (@IN A) x). Qed.
Lemma lem7155288 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7155289 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x t).
Proof. exact (MK_COMB (@lem7155287 A x) (@lem7155288 A t)). Qed.
Lemma lem7155291 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155292 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7155291 (A -> Prop) Prop f x). Qed.
Lemma lem7155293 {A : Type'} (x : A) (t : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x t) = (term452 A x t).
Proof. exact (@lem7155292 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) t). Qed.
Lemma lem7155295 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (term452 A x t).
Proof. exact (TRANS (@lem7155289 A x t) (@lem7155293 A x t)). Qed.
Lemma lem7155296 {A : Type'} (x : A) (t : A -> Prop) : (term72 A x t) = (term453 A x t).
Proof. exact (MK_COMB (@lem7155278) (@lem7155295 A x t)). Qed.
Lemma lem7155297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7155298 {A : Type'} (x : A) (t : A -> Prop) : (term68 A x t) = (term454 A x t).
Proof. exact (MK_COMB (@lem7155297) (@lem7155296 A x t)). Qed.
Lemma lem7155299 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term64 A t f g x) = (term460 A t f g x).
Proof. exact (MK_COMB (@lem7155298 A x t) (@lem7155277 A f g x)). Qed.
Lemma lem7155300 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) : (term65 A t f g) = (term461 A t f g).
Proof. exact (fun_ext (fun x : A => @lem7155299 A t f g x)). Qed.
Lemma lem7155301 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7155302 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) : (term66 A t f g) = (term462 A t f g).
Proof. exact (MK_COMB (@lem7155301 A) (@lem7155300 A t f g)). Qed.
Lemma lem7155303 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7155304 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) : (term81 A t f g) = (term463 A t f g).
Proof. exact (MK_COMB (@lem7155303) (@lem7155302 A t f g)). Qed.
Lemma lem7155305 {A : Type'} (g : A -> real) (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term82 A g s t f) = (term464 A g s t f).
Proof. exact (MK_COMB (@lem7155304 A t f g) (@lem7155259 A s t f)). Qed.
Lemma lem7155312 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155313 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem7155312 (A -> Prop) (type686 A) f x). Qed.
Lemma lem7155314 {A : Type'} (t : A -> Prop) : (@SUBSET A t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) t).
Proof. exact (@lem7155313 A (@SUBSET A) t). Qed.
Lemma lem7155315 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7155316 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) t s).
Proof. exact (MK_COMB (@lem7155314 A t) (@lem7155315 A s)). Qed.
Lemma lem7155318 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155319 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7155318 (A -> Prop) Prop f x). Qed.
Lemma lem7155320 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) t s) = (term394 A t s).
Proof. exact (@lem7155319 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) (@SUBSET A) t) s). Qed.
Lemma lem7155322 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term394 A t s).
Proof. exact (TRANS (@lem7155316 A t s) (@lem7155320 A t s)). Qed.
Lemma lem7155323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7155324 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term33 A t s) = (term465 A t s).
Proof. exact (MK_COMB (@lem7155323) (@lem7155322 A t s)). Qed.
Lemma lem7155325 {A : Type'} (g : A -> real) (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term83 A g s t f) = (term466 A g s t f).
Proof. exact (MK_COMB (@lem7155324 A t s) (@lem7155305 A g s t f)). Qed.
Lemma lem7155330 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7155331 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem7155330 (A -> Prop) Prop f x). Qed.
Lemma lem7155333 {A : Type'} (t : A -> Prop) : (@FINITE A t) = (@I ((A -> Prop) -> Prop) (@FINITE A) t).
Proof. exact (@lem7155331 A (@FINITE A) t). Qed.
Lemma lem7155334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7155335 {A : Type'} (t : A -> Prop) : (term55 A t) = (term467 A t).
Proof. exact (MK_COMB (@lem7155334) (@lem7155333 A t)). Qed.
Lemma lem7155336 {A : Type'} (g : A -> real) (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term84 A g s t f) = (term468 A g s t f).
Proof. exact (MK_COMB (@lem7155335 A t) (@lem7155325 A g s t f)). Qed.
Lemma lem7155337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7155338 {A : Type'} (g : A -> real) (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term87 A g s t f) = (term469 A g s t f).
Proof. exact (MK_COMB (@lem7155337) (@lem7155336 A g s t f)). Qed.
Lemma lem7155339 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : (term89 A s f t g) = (term470 A s f t g).
Proof. exact (MK_COMB (@lem7155338 A g s t f) (@lem7155189 A s f t g)). Qed.
Lemma lem7155340 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term470 A s f t g.
Proof. exact (EQ_MP (@lem7155339 A s f t g) (@lem7154601 A s f t g h1)). Qed.
Lemma lem7155342 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term468 A g s t f.
Proof. exact (proj1 (@lem7155340 A s f t g h1)). Qed.
Lemma lem7155343 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term466 A g s t f.
Proof. exact (proj2 (@lem7155342 A s f t g h1)). Qed.
Lemma lem7155345 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term464 A g s t f.
Proof. exact (proj2 (@lem7155343 A s f t g h1)). Qed.
Lemma lem7155347 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term459 A s t f.
Proof. exact (proj2 (@lem7155345 A s f t g h1)). Qed.
Lemma lem7155348 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term462 A t f g.
Proof. exact (proj1 (@lem7155345 A s f t g h1)). Qed.
Lemma lem7155350 {A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> real) : ((term358 A v f) = (term358 A u f)) = ((term358 A v f) = (term358 A u f)).
Proof. exact (eq_refl ((term358 A v f) = (term358 A u f))). Qed.
Lemma lem7155364 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term398 A x f u v) = (term471 A x f u v).
Proof. exact (@lem19490 (term389 A x f v u) (term395 A u v) (term372 A x f u v)). Qed.
Lemma lem7155365 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term472 A x f u v) = (term472 A x f u v).
Proof. exact (eq_refl (term472 A x f u v)). Qed.
Lemma lem7155372 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term473 A x f v u) = (term474 A x f v u).
Proof. exact (@lem19490 (term385 A x f u v) (term395 A u v) (term381 A x f v u)). Qed.
Lemma lem7155373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7155374 {A : Type'} (x : type709 A) (f : A -> real) (v : A -> Prop) (u : A -> Prop) : (term475 A x f v u) = (term476 A x f v u).
Proof. exact (MK_COMB (@lem7155373) (@lem7155372 A x f v u)). Qed.
Lemma lem7155375 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term471 A x f u v) = (term477 A x f u v).
Proof. exact (MK_COMB (@lem7155374 A x f v u) (@lem7155365 A x f u v)). Qed.
Lemma lem7155377 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term398 A x f u v) = (term477 A x f u v).
Proof. exact (TRANS (@lem7155364 A x f u v) (@lem7155375 A x f u v)). Qed.
Lemma lem7155378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7155379 {A : Type'} (x : type709 A) (f : A -> real) (u : A -> Prop) (v : A -> Prop) : (term400 A x f u v) = (term478 A x f u v).
Proof. exact (MK_COMB (@lem7155378) (@lem7155377 A x f u v)). Qed.
Lemma lem7155380 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term402 A x v u f) = (term479 A x v u f).
Proof. exact (MK_COMB (@lem7155379 A x f u v) (@lem7155350 A v u f)). Qed.
Lemma lem7155381 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term479 A x v u f) = (term480 A x v u f).
Proof. exact (@lem19699 (term474 A x f v u) (term472 A x f u v) ((term358 A v f) = (term358 A u f))). Qed.
Lemma lem7155382 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term481 A x v u f) = (term481 A x v u f).
Proof. exact (eq_refl (term481 A x v u f)). Qed.
Lemma lem7155389 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term482 A x v u f) = (term483 A x v u f).
Proof. exact (@lem19699 (term484 A x f u v) (term485 A x f v u) ((term358 A v f) = (term358 A u f))). Qed.
Lemma lem7155390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7155391 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term486 A x v u f) = (term487 A x v u f).
Proof. exact (MK_COMB (@lem7155390) (@lem7155389 A x v u f)). Qed.
Lemma lem7155392 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term480 A x v u f) = (term488 A x v u f).
Proof. exact (MK_COMB (@lem7155391 A x v u f) (@lem7155382 A x v u f)). Qed.
Lemma lem7155393 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term479 A x v u f) = (term488 A x v u f).
Proof. exact (TRANS (@lem7155381 A x v u f) (@lem7155392 A x v u f)). Qed.
Lemma lem7155394 {A : Type'} (x : type709 A) (v : A -> Prop) (u : A -> Prop) (f : A -> real) : (term402 A x v u f) = (term488 A x v u f).
Proof. exact (TRANS (@lem7155380 A x v u f) (@lem7155393 A x v u f)). Qed.
Lemma lem7155395 {A : Type'} (x : type709 A) (u : A -> Prop) (f : A -> real) : (term404 A x u f) = (term489 A x u f).
Proof. exact (fun_ext (fun v : A -> Prop => @lem7155394 A x v u f)). Qed.
Lemma lem7155396 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7155397 {A : Type'} (x : type709 A) (u : A -> Prop) (f : A -> real) : (term406 A x u f) = (term490 A x u f).
Proof. exact (MK_COMB (@lem7155396 A) (@lem7155395 A x u f)). Qed.
Lemma lem7155398 {A : Type'} (x : type709 A) (f : A -> real) : (term408 A x f) = (term491 A x f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem7155397 A x u f)). Qed.
Lemma lem7155399 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7155400 {A : Type'} (x : type709 A) (f : A -> real) : (term409 A x f) = (term492 A x f).
Proof. exact (MK_COMB (@lem7155399 A) (@lem7155398 A x f)). Qed.
Lemma lem7155401 {A : Type'} (x : type709 A) : (term410 A x) = (term493 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7155400 A x f)). Qed.
Lemma lem7155402 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7155404 {A : Type'} (x : type709 A) : (term411 A x) = (term494 A x).
Proof. exact (MK_COMB (@lem7155402 A) (@lem7155401 A x)). Qed.
Lemma lem7155405 {A : Type'} (x : type709 A) (h1 : term354 A x) : term494 A x.
Proof. exact (EQ_MP (@lem7155404 A x) (@lem7154818 A x h1)). Qed.
Lemma lem7155423 {A : Type'} (x' : type711 A) (f : A -> real) (s : A -> Prop) (g : A -> real) : (term439 A x' f s g) = (term495 A x' f s g).
Proof. exact (@lem19699 (term431 A x' f g s) (term424 A x' f g s) ((term358 A s f) = (term358 A s g))). Qed.
Lemma lem7155424 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (term441 A x' f g) = (term496 A x' f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7155423 A x' f s g)). Qed.
Lemma lem7155425 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7155426 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) : (term443 A x' f g) = (term497 A x' f g).
Proof. exact (MK_COMB (@lem7155425 A) (@lem7155424 A x' f g)). Qed.
Lemma lem7155427 {A : Type'} (x' : type711 A) (f : A -> real) : (term445 A x' f) = (term498 A x' f).
Proof. exact (fun_ext (fun g : A -> real => @lem7155426 A x' f g)). Qed.
Lemma lem7155428 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7155429 {A : Type'} (x' : type711 A) (f : A -> real) : (term446 A x' f) = (term499 A x' f).
Proof. exact (MK_COMB (@lem7155428 A) (@lem7155427 A x' f)). Qed.
Lemma lem7155430 {A : Type'} (x' : type711 A) : (term447 A x') = (term500 A x').
Proof. exact (fun_ext (fun f : A -> real => @lem7155429 A x' f)). Qed.
Lemma lem7155431 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7155433 {A : Type'} (x' : type711 A) : (term448 A x') = (term501 A x').
Proof. exact (MK_COMB (@lem7155431 A) (@lem7155430 A x')). Qed.
Lemma lem7155434 {A : Type'} (x' : type711 A) (h1 : term226 A x') : term501 A x'.
Proof. exact (EQ_MP (@lem7155433 A x') (@lem7154984 A x' h1)). Qed.
Lemma lem7155483 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) (x : A) : (term460 A t f g x) = (term460 A t f g x).
Proof. exact (eq_refl (term460 A t f g x)). Qed.
Lemma lem7155484 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) : (term461 A t f g) = (term461 A t f g).
Proof. exact (fun_ext (fun x : A => @lem7155483 A t f g x)). Qed.
Lemma lem7155485 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7155487 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) : (term462 A t f g) = (term462 A t f g).
Proof. exact (MK_COMB (@lem7155485 A) (@lem7155484 A t f g)). Qed.
Lemma lem7155488 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term462 A t f g.
Proof. exact (EQ_MP (@lem7155487 A t f g) (@lem7155348 A s f t g h1)). Qed.
Lemma lem7155502 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (x : A) : (term457 A s t f x) = (term457 A s t f x).
Proof. exact (eq_refl (term457 A s t f x)). Qed.
Lemma lem7155503 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term458 A s t f) = (term458 A s t f).
Proof. exact (fun_ext (fun x : A => @lem7155502 A s t f x)). Qed.
Lemma lem7155504 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7155506 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term459 A s t f) = (term459 A s t f).
Proof. exact (MK_COMB (@lem7155504 A) (@lem7155503 A s t f)). Qed.
Lemma lem7155507 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term459 A s t f.
Proof. exact (EQ_MP (@lem7155506 A s t f) (@lem7155347 A s f t g h1)). Qed.
Lemma lem7155508 {A : Type'} (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term502 A x _95731.
Proof. exact (@lem7155405 A x h1 _95731). Qed.
Lemma lem7155509 {A : Type'} (x : type709 A) (_95731 : A -> real) : (term502 A x _95731) = (term492 A x _95731).
Proof. exact (eq_refl (term502 A x _95731)). Qed.
Lemma lem7155510 {A : Type'} (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term492 A x _95731.
Proof. exact (EQ_MP (@lem7155509 A x _95731) (@lem7155508 A _95731 x h1)). Qed.
Lemma lem7155511 {A : Type'} (_95731 : A -> real) (_95732 : A -> Prop) (x : type709 A) (h1 : term354 A x) : term503 A x _95731 _95732.
Proof. exact (@lem7155510 A _95731 x h1 _95732). Qed.
Lemma lem7155512 {A : Type'} (x : type709 A) (_95732 : A -> Prop) (_95731 : A -> real) : (term503 A x _95731 _95732) = (term490 A x _95732 _95731).
Proof. exact (eq_refl (term503 A x _95731 _95732)). Qed.
Lemma lem7155513 {A : Type'} (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term490 A x _95732 _95731.
Proof. exact (EQ_MP (@lem7155512 A x _95732 _95731) (@lem7155511 A _95731 _95732 x h1)). Qed.
Lemma lem7155514 {A : Type'} (_95732 : A -> Prop) (_95731 : A -> real) (_95733 : A -> Prop) (x : type709 A) (h1 : term354 A x) : term504 A x _95732 _95731 _95733.
Proof. exact (@lem7155513 A _95732 _95731 x h1 _95733). Qed.
Lemma lem7155515 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term504 A x _95732 _95731 _95733) = (term488 A x _95733 _95732 _95731).
Proof. exact (eq_refl (term504 A x _95732 _95731 _95733)). Qed.
Lemma lem7155516 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term488 A x _95733 _95732 _95731.
Proof. exact (EQ_MP (@lem7155515 A x _95733 _95732 _95731) (@lem7155514 A _95732 _95731 _95733 x h1)). Qed.
Lemma lem7155517 {A : Type'} (_95734 : A -> real) (x' : type711 A) (h1 : term226 A x') : term505 A x' _95734.
Proof. exact (@lem7155434 A x' h1 _95734). Qed.
Lemma lem7155518 {A : Type'} (x' : type711 A) (_95734 : A -> real) : (term505 A x' _95734) = (term499 A x' _95734).
Proof. exact (eq_refl (term505 A x' _95734)). Qed.
Lemma lem7155519 {A : Type'} (_95734 : A -> real) (x' : type711 A) (h1 : term226 A x') : term499 A x' _95734.
Proof. exact (EQ_MP (@lem7155518 A x' _95734) (@lem7155517 A _95734 x' h1)). Qed.
Lemma lem7155520 {A : Type'} (_95734 : A -> real) (_95735 : A -> real) (x' : type711 A) (h1 : term226 A x') : term506 A x' _95734 _95735.
Proof. exact (@lem7155519 A _95734 x' h1 _95735). Qed.
Lemma lem7155521 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95735 : A -> real) : (term506 A x' _95734 _95735) = (term497 A x' _95734 _95735).
Proof. exact (eq_refl (term506 A x' _95734 _95735)). Qed.
Lemma lem7155522 {A : Type'} (_95734 : A -> real) (_95735 : A -> real) (x' : type711 A) (h1 : term226 A x') : term497 A x' _95734 _95735.
Proof. exact (EQ_MP (@lem7155521 A x' _95734 _95735) (@lem7155520 A _95734 _95735 x' h1)). Qed.
Lemma lem7155523 {A : Type'} (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) (x' : type711 A) (h1 : term226 A x') : term507 A x' _95734 _95735 _95736.
Proof. exact (@lem7155522 A _95734 _95735 x' h1 _95736). Qed.
Lemma lem7155524 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95736 : A -> Prop) (_95735 : A -> real) : (term507 A x' _95734 _95735 _95736) = (term495 A x' _95734 _95736 _95735).
Proof. exact (eq_refl (term507 A x' _95734 _95735 _95736)). Qed.
Lemma lem7155525 {A : Type'} (_95734 : A -> real) (_95736 : A -> Prop) (_95735 : A -> real) (x' : type711 A) (h1 : term226 A x') : term495 A x' _95734 _95736 _95735.
Proof. exact (EQ_MP (@lem7155524 A x' _95734 _95736 _95735) (@lem7155523 A _95734 _95735 _95736 x' h1)). Qed.
Lemma lem7155535 {A : Type'} (_95740 : A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term508 A t f g _95740.
Proof. exact (@lem7155488 A s f t g h1 _95740). Qed.
Lemma lem7155536 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) (_95740 : A) : (term508 A t f g _95740) = (term460 A t f g _95740).
Proof. exact (eq_refl (term508 A t f g _95740)). Qed.
Lemma lem7155538 {A : Type'} (_95741 : A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term509 A s t f _95741.
Proof. exact (@lem7155507 A s f t g h1 _95741). Qed.
Lemma lem7155539 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (_95741 : A) : (term509 A s t f _95741) = (term457 A s t f _95741).
Proof. exact (eq_refl (term509 A s t f _95741)). Qed.
Lemma lem7155540 {A : Type'} (_95741 : A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term457 A s t f _95741.
Proof. exact (EQ_MP (@lem7155539 A s t f _95741) (@lem7155538 A _95741 s f t g h1)). Qed.
Lemma lem7155545 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term481 A x _95733 _95732 _95731.
Proof. exact (proj2 (@lem7155516 A _95733 _95732 _95731 x h1)). Qed.
Lemma lem7155546 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term483 A x _95733 _95732 _95731.
Proof. exact (proj1 (@lem7155516 A _95733 _95732 _95731 x h1)). Qed.
Lemma lem7155547 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term510 A x _95733 _95732 _95731.
Proof. exact (proj2 (@lem7155546 A _95733 _95732 _95731 x h1)). Qed.
Lemma lem7155548 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term511 A x _95733 _95732 _95731.
Proof. exact (proj1 (@lem7155546 A _95733 _95732 _95731 x h1)). Qed.
Lemma lem7155550 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term449 A s f t g.
Proof. exact (proj2 (@lem7155340 A s f t g h1)). Qed.
Lemma lem7155560 {A : Type'} (_95740 : A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term460 A t f g _95740.
Proof. exact (EQ_MP (@lem7155536 A t f g _95740) (@lem7155535 A _95740 s f t g h1)). Qed.
Lemma lem7155571 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (_95741 : A) : (term457 A s t f _95741) = (term512 A s t f _95741).
Proof. exact (@lem7153083 (term453 A _95741 s) (term452 A _95741 t) ((@I (A -> real) f _95741) = term368)). Qed.
Lemma lem7155572 {A : Type'} (_95741 : A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term512 A s t f _95741.
Proof. exact (EQ_MP (@lem7155571 A s t f _95741) (@lem7155540 A _95741 s f t g h1)). Qed.
Lemma lem7155590 {A : Type'} (_95734 : A -> real) (_95736 : A -> Prop) (_95735 : A -> real) (x' : type711 A) (h1 : term226 A x') : term513 A x' _95734 _95736 _95735.
Proof. exact (proj1 (@lem7155525 A _95734 _95736 _95735 x' h1)). Qed.
Lemma lem7155596 {A : Type'} (_95734 : A -> real) (_95736 : A -> Prop) (_95735 : A -> real) (x' : type711 A) (h1 : term226 A x') : term514 A x' _95734 _95736 _95735.
Proof. exact (proj2 (@lem7155525 A _95734 _95736 _95735 x' h1)). Qed.
Lemma lem7155607 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term481 A x _95733 _95732 _95731) = (term515 A x _95733 _95732 _95731).
Proof. exact (@lem7153083 (term395 A _95732 _95733) (term372 A x _95731 _95732 _95733) ((term358 A _95733 _95731) = (term358 A _95732 _95731))). Qed.
Lemma lem7155608 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term515 A x _95733 _95732 _95731.
Proof. exact (EQ_MP (@lem7155607 A x _95733 _95732 _95731) (@lem7155545 A _95733 _95732 _95731 x h1)). Qed.
Lemma lem7155619 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term511 A x _95733 _95732 _95731) = (term516 A x _95733 _95732 _95731).
Proof. exact (@lem7153083 (term395 A _95732 _95733) (term385 A x _95731 _95732 _95733) ((term358 A _95733 _95731) = (term358 A _95732 _95731))). Qed.
Lemma lem7155620 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term516 A x _95733 _95732 _95731.
Proof. exact (EQ_MP (@lem7155619 A x _95733 _95732 _95731) (@lem7155548 A _95733 _95732 _95731 x h1)). Qed.
Lemma lem7155631 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term510 A x _95733 _95732 _95731) = (term517 A x _95733 _95732 _95731).
Proof. exact (@lem7153083 (term395 A _95732 _95733) (term381 A x _95731 _95733 _95732) ((term358 A _95733 _95731) = (term358 A _95732 _95731))). Qed.
Lemma lem7155632 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term517 A x _95733 _95732 _95731.
Proof. exact (EQ_MP (@lem7155631 A x _95733 _95732 _95731) (@lem7155547 A _95733 _95732 _95731 x h1)). Qed.
Lemma lem7155957 (x : real) (y : real) (z : real) : term518 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem7156011 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term394 A t s.
Proof. exact (proj1 (@lem7155343 A s f t g h1)). Qed.
Lemma lem7156012 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term519 A t s.
Proof. exact (fun h0 : term395 A t s => @lem7156011 A s f t g h1). Qed.
Lemma lem7156014 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156015 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term519 A t s) = (term394 A t s).
Proof. exact (@lem7156014 (term394 A t s)). Qed.
Lemma lem7156016 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term394 A t s.
Proof. exact (EQ_MP (@lem7156015 A t s) (@lem7156012 A s f t g h1)). Qed.
Lemma lem7156018 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term394 A t s.
Proof. exact (proj1 (@lem7155343 A s f t g h1)). Qed.
Lemma lem7156019 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term519 A t s.
Proof. exact (fun h0 : term395 A t s => @lem7156018 A s f t g h1). Qed.
Lemma lem7156021 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156022 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term519 A t s) = (term394 A t s).
Proof. exact (@lem7156021 (term394 A t s)). Qed.
Lemma lem7156023 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term394 A t s.
Proof. exact (EQ_MP (@lem7156022 A t s) (@lem7156019 A s f t g h1)). Qed.
Lemma lem7156026 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (h1 : term521 A s t f) : term521 A s t f.
Proof. exact (h1). Qed.
Lemma lem7156027 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (h1 : term521 A s t f) : term522 A s t f.
Proof. exact (fun h0 : (term358 A s f) = (term358 A t f) => @lem7156026 A s t f h1). Qed.
Lemma lem7156029 (p : Prop) : (term523 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7156030 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term522 A s t f) = (term521 A s t f).
Proof. exact (@lem7156029 ((term358 A s f) = (term358 A t f))). Qed.
Lemma lem7156031 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (h1 : term521 A s t f) : term521 A s t f.
Proof. exact (EQ_MP (@lem7156030 A s t f) (@lem7156027 A s t f h1)). Qed.
Lemma lem7156037 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7156038 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term516 A x _95733 _95732 _95731) = (term524 A x _95733 _95732 _95731).
Proof. exact (@lem7156037 (term385 A x _95731 _95732 _95733) (term395 A _95732 _95733) ((term358 A _95733 _95731) = (term358 A _95732 _95731))). Qed.
Lemma lem7156052 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7156053 {A : Type'} (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term525 A _95733 _95732 _95731) = (term526 A _95731 _95732 _95733).
Proof. exact (@lem7156052 ((term358 A _95733 _95731) = (term358 A _95732 _95731)) (term395 A _95732 _95733)). Qed.
Lemma lem7156061 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term527 A x _95731 _95732 _95733) = (term527 A x _95731 _95732 _95733).
Proof. exact (eq_refl (term527 A x _95731 _95732 _95733)). Qed.
Lemma lem7156062 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term524 A x _95733 _95732 _95731) = (term528 A x _95731 _95732 _95733).
Proof. exact (MK_COMB (@lem7156061 A x _95731 _95732 _95733) (@lem7156053 A _95731 _95732 _95733)). Qed.
Lemma lem7156066 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7156067 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term528 A x _95731 _95732 _95733) = (term529 A x _95731 _95732 _95733).
Proof. exact (@lem7156066 ((term358 A _95733 _95731) = (term358 A _95732 _95731)) (term385 A x _95731 _95732 _95733) (term395 A _95732 _95733)). Qed.
Lemma lem7156085 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term524 A x _95733 _95732 _95731) = (term529 A x _95731 _95732 _95733).
Proof. exact (TRANS (@lem7156062 A x _95731 _95732 _95733) (@lem7156067 A x _95731 _95732 _95733)). Qed.
Lemma lem7156086 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term516 A x _95733 _95732 _95731) = (term529 A x _95731 _95732 _95733).
Proof. exact (TRANS (@lem7156038 A x _95733 _95732 _95731) (@lem7156085 A x _95731 _95732 _95733)). Qed.
Lemma lem7156087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7156088 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term530 A x _95733 _95732 _95731) = (term531 A x _95731 _95732 _95733).
Proof. exact (MK_COMB (@lem7156087) (@lem7156086 A x _95731 _95732 _95733)). Qed.
Lemma lem7156102 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7156103 {A : Type'} (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term525 A _95733 _95732 _95731) = (term526 A _95731 _95732 _95733).
Proof. exact (@lem7156102 ((term358 A _95733 _95731) = (term358 A _95732 _95731)) (term395 A _95732 _95733)). Qed.
Lemma lem7156111 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term527 A x _95731 _95732 _95733) = (term527 A x _95731 _95732 _95733).
Proof. exact (eq_refl (term527 A x _95731 _95732 _95733)). Qed.
Lemma lem7156112 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term524 A x _95733 _95732 _95731) = (term528 A x _95731 _95732 _95733).
Proof. exact (MK_COMB (@lem7156111 A x _95731 _95732 _95733) (@lem7156103 A _95731 _95732 _95733)). Qed.
Lemma lem7156116 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7156117 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term528 A x _95731 _95732 _95733) = (term529 A x _95731 _95732 _95733).
Proof. exact (@lem7156116 ((term358 A _95733 _95731) = (term358 A _95732 _95731)) (term385 A x _95731 _95732 _95733) (term395 A _95732 _95733)). Qed.
Lemma lem7156135 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term524 A x _95733 _95732 _95731) = (term529 A x _95731 _95732 _95733).
Proof. exact (TRANS (@lem7156112 A x _95731 _95732 _95733) (@lem7156117 A x _95731 _95732 _95733)). Qed.
Lemma lem7156136 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : ((term516 A x _95733 _95732 _95731) = (term524 A x _95733 _95732 _95731)) = ((term529 A x _95731 _95732 _95733) = (term529 A x _95731 _95732 _95733)).
Proof. exact (MK_COMB (@lem7156088 A x _95731 _95732 _95733) (@lem7156135 A x _95731 _95732 _95733)). Qed.
Lemma lem7156138 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7156139 (x : Prop) : (x = x) = True.
Proof. exact (@lem7156138 Prop x). Qed.
Lemma lem7156140 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : ((term529 A x _95731 _95732 _95733) = (term529 A x _95731 _95732 _95733)) = True.
Proof. exact (@lem7156139 (term529 A x _95731 _95732 _95733)). Qed.
Lemma lem7156141 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : ((term516 A x _95733 _95732 _95731) = (term524 A x _95733 _95732 _95731)) = True.
Proof. exact (TRANS (@lem7156136 A x _95731 _95732 _95733) (@lem7156140 A x _95731 _95732 _95733)). Qed.
Lemma lem7156142 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : True = ((term516 A x _95733 _95732 _95731) = (term524 A x _95733 _95732 _95731)).
Proof. exact (SYM (@lem7156141 A x _95733 _95732 _95731)). Qed.
Lemma lem7156143 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term516 A x _95733 _95732 _95731) = (term524 A x _95733 _95732 _95731).
Proof. exact (EQ_MP (@lem7156142 A x _95733 _95732 _95731) (@lem0)). Qed.
Lemma lem7156144 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term524 A x _95733 _95732 _95731.
Proof. exact (EQ_MP (@lem7156143 A x _95733 _95732 _95731) (@lem7155620 A _95733 _95732 _95731 x h1)). Qed.
Lemma lem7156146 (b : Prop) (a : Prop) : (a \/ b) = (term532 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7156147 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term524 A x _95733 _95732 _95731) = (term533 A x _95731 _95732 _95733).
Proof. exact (@lem7156146 (term525 A _95733 _95732 _95731) (term385 A x _95731 _95732 _95733)). Qed.
Lemma lem7156149 (a : Prop) (b : Prop) : (term534 a b) = (term535 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7156150 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term536 A _95733 _95732 _95731) = (term537 A _95733 _95732 _95731).
Proof. exact (@lem7156149 (term395 A _95732 _95733) ((term358 A _95733 _95731) = (term358 A _95732 _95731))). Qed.
Lemma lem7156152 (a : Prop) : (term538 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7156153 {A : Type'} (_95732 : A -> Prop) (_95733 : A -> Prop) : (term539 A _95732 _95733) = (term394 A _95732 _95733).
Proof. exact (@lem7156152 (term394 A _95732 _95733)). Qed.
Lemma lem7156154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7156155 {A : Type'} (_95732 : A -> Prop) (_95733 : A -> Prop) : (term540 A _95732 _95733) = (term465 A _95732 _95733).
Proof. exact (MK_COMB (@lem7156154) (@lem7156153 A _95732 _95733)). Qed.
Lemma lem7156156 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term521 A _95733 _95732 _95731) = (term521 A _95733 _95732 _95731).
Proof. exact (eq_refl (term521 A _95733 _95732 _95731)). Qed.
Lemma lem7156157 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term537 A _95733 _95732 _95731) = (term541 A _95733 _95732 _95731).
Proof. exact (MK_COMB (@lem7156155 A _95732 _95733) (@lem7156156 A _95733 _95732 _95731)). Qed.
Lemma lem7156158 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term536 A _95733 _95732 _95731) = (term541 A _95733 _95732 _95731).
Proof. exact (TRANS (@lem7156150 A _95733 _95732 _95731) (@lem7156157 A _95733 _95732 _95731)). Qed.
Lemma lem7156159 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7156160 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term542 A _95733 _95732 _95731) = (term543 A _95733 _95732 _95731).
Proof. exact (MK_COMB (@lem7156159) (@lem7156158 A _95733 _95732 _95731)). Qed.
Lemma lem7156161 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term385 A x _95731 _95732 _95733) = (term385 A x _95731 _95732 _95733).
Proof. exact (eq_refl (term385 A x _95731 _95732 _95733)). Qed.
Lemma lem7156162 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term533 A x _95731 _95732 _95733) = (term544 A x _95731 _95732 _95733).
Proof. exact (MK_COMB (@lem7156160 A _95733 _95732 _95731) (@lem7156161 A x _95731 _95732 _95733)). Qed.
Lemma lem7156163 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term524 A x _95733 _95732 _95731) = (term544 A x _95731 _95732 _95733).
Proof. exact (TRANS (@lem7156147 A x _95731 _95732 _95733) (@lem7156162 A x _95731 _95732 _95733)). Qed.
Lemma lem7156165 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term521 A s t f) (h2 : term89 A s f t g) : term541 A s t f.
Proof. exact (conj (@lem7156023 A s f t g h2) (@lem7156031 A s t f h1)). Qed.
Lemma lem7156167 {A : Type'} (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) (x : type709 A) (h1 : term354 A x) : term544 A x _95731 _95732 _95733.
Proof. exact (EQ_MP (@lem7156163 A x _95731 _95732 _95733) (@lem7156144 A _95733 _95732 _95731 x h1)). Qed.
Lemma lem7156168 {A : Type'} (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) (x : type709 A) (h1 : term354 A x) : term544 A x _95731 _95732 _95733.
Proof. exact (@lem7156167 A _95731 _95732 _95733 x h1). Qed.
Lemma lem7156169 {A : Type'} (f : A -> real) (t : A -> Prop) (s : A -> Prop) (x : type709 A) (h1 : term354 A x) : term544 A x f t s.
Proof. exact (@lem7156168 A f t s x h1). Qed.
Lemma lem7156172 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term521 A s t f) (h3 : term89 A s f t g) : term385 A x f t s.
Proof. exact (@lem7156169 A f t s x h1 (@lem7156165 A s f t g h2 h3)). Qed.
Lemma lem7156173 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term521 A s t f) (h3 : term89 A s f t g) : term545 A x f t s.
Proof. exact (fun h0 : term546 A x f t s => @lem7156172 A x s f t g h1 h2 h3). Qed.
Lemma lem7156175 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156176 {A : Type'} (x : type709 A) (f : A -> real) (t : A -> Prop) (s : A -> Prop) : (term545 A x f t s) = (term385 A x f t s).
Proof. exact (@lem7156175 (term385 A x f t s)). Qed.
Lemma lem7156177 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term521 A s t f) (h3 : term89 A s f t g) : term385 A x f t s.
Proof. exact (EQ_MP (@lem7156176 A x f t s) (@lem7156173 A x s f t g h1 h2 h3)). Qed.
Lemma lem7156179 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term394 A t s.
Proof. exact (proj1 (@lem7155343 A s f t g h1)). Qed.
Lemma lem7156180 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term519 A t s.
Proof. exact (fun h0 : term395 A t s => @lem7156179 A s f t g h1). Qed.
Lemma lem7156182 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156183 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term519 A t s) = (term394 A t s).
Proof. exact (@lem7156182 (term394 A t s)). Qed.
Lemma lem7156184 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term394 A t s.
Proof. exact (EQ_MP (@lem7156183 A t s) (@lem7156180 A s f t g h1)). Qed.
Lemma lem7156187 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (h1 : term521 A s t f) : term521 A s t f.
Proof. exact (h1). Qed.
Lemma lem7156188 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (h1 : term521 A s t f) : term522 A s t f.
Proof. exact (fun h0 : (term358 A s f) = (term358 A t f) => @lem7156187 A s t f h1). Qed.
Lemma lem7156190 (p : Prop) : (term523 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7156191 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term522 A s t f) = (term521 A s t f).
Proof. exact (@lem7156190 ((term358 A s f) = (term358 A t f))). Qed.
Lemma lem7156192 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (h1 : term521 A s t f) : term521 A s t f.
Proof. exact (EQ_MP (@lem7156191 A s t f) (@lem7156188 A s t f h1)). Qed.
Lemma lem7156198 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7156199 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term515 A x _95733 _95732 _95731) = (term547 A x _95733 _95732 _95731).
Proof. exact (@lem7156198 (term372 A x _95731 _95732 _95733) (term395 A _95732 _95733) ((term358 A _95733 _95731) = (term358 A _95732 _95731))). Qed.
Lemma lem7156215 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7156216 {A : Type'} (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term525 A _95733 _95732 _95731) = (term526 A _95731 _95732 _95733).
Proof. exact (@lem7156215 ((term358 A _95733 _95731) = (term358 A _95732 _95731)) (term395 A _95732 _95733)). Qed.
Lemma lem7156224 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term548 A x _95731 _95732 _95733) = (term548 A x _95731 _95732 _95733).
Proof. exact (eq_refl (term548 A x _95731 _95732 _95733)). Qed.
Lemma lem7156225 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term547 A x _95733 _95732 _95731) = (term549 A x _95731 _95732 _95733).
Proof. exact (MK_COMB (@lem7156224 A x _95731 _95732 _95733) (@lem7156216 A _95731 _95732 _95733)). Qed.
Lemma lem7156229 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7156230 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term549 A x _95731 _95732 _95733) = (term550 A x _95731 _95732 _95733).
Proof. exact (@lem7156229 ((term358 A _95733 _95731) = (term358 A _95732 _95731)) (term372 A x _95731 _95732 _95733) (term395 A _95732 _95733)). Qed.
Lemma lem7156250 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term547 A x _95733 _95732 _95731) = (term550 A x _95731 _95732 _95733).
Proof. exact (TRANS (@lem7156225 A x _95731 _95732 _95733) (@lem7156230 A x _95731 _95732 _95733)). Qed.
Lemma lem7156251 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term515 A x _95733 _95732 _95731) = (term550 A x _95731 _95732 _95733).
Proof. exact (TRANS (@lem7156199 A x _95733 _95732 _95731) (@lem7156250 A x _95731 _95732 _95733)). Qed.
Lemma lem7156252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7156253 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term551 A x _95733 _95732 _95731) = (term552 A x _95731 _95732 _95733).
Proof. exact (MK_COMB (@lem7156252) (@lem7156251 A x _95731 _95732 _95733)). Qed.
Lemma lem7156269 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7156270 {A : Type'} (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term525 A _95733 _95732 _95731) = (term526 A _95731 _95732 _95733).
Proof. exact (@lem7156269 ((term358 A _95733 _95731) = (term358 A _95732 _95731)) (term395 A _95732 _95733)). Qed.
Lemma lem7156278 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term548 A x _95731 _95732 _95733) = (term548 A x _95731 _95732 _95733).
Proof. exact (eq_refl (term548 A x _95731 _95732 _95733)). Qed.
Lemma lem7156279 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term547 A x _95733 _95732 _95731) = (term549 A x _95731 _95732 _95733).
Proof. exact (MK_COMB (@lem7156278 A x _95731 _95732 _95733) (@lem7156270 A _95731 _95732 _95733)). Qed.
Lemma lem7156283 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7156284 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term549 A x _95731 _95732 _95733) = (term550 A x _95731 _95732 _95733).
Proof. exact (@lem7156283 ((term358 A _95733 _95731) = (term358 A _95732 _95731)) (term372 A x _95731 _95732 _95733) (term395 A _95732 _95733)). Qed.
Lemma lem7156304 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term547 A x _95733 _95732 _95731) = (term550 A x _95731 _95732 _95733).
Proof. exact (TRANS (@lem7156279 A x _95731 _95732 _95733) (@lem7156284 A x _95731 _95732 _95733)). Qed.
Lemma lem7156305 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : ((term515 A x _95733 _95732 _95731) = (term547 A x _95733 _95732 _95731)) = ((term550 A x _95731 _95732 _95733) = (term550 A x _95731 _95732 _95733)).
Proof. exact (MK_COMB (@lem7156253 A x _95731 _95732 _95733) (@lem7156304 A x _95731 _95732 _95733)). Qed.
Lemma lem7156307 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7156308 (x : Prop) : (x = x) = True.
Proof. exact (@lem7156307 Prop x). Qed.
Lemma lem7156309 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : ((term550 A x _95731 _95732 _95733) = (term550 A x _95731 _95732 _95733)) = True.
Proof. exact (@lem7156308 (term550 A x _95731 _95732 _95733)). Qed.
Lemma lem7156310 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : ((term515 A x _95733 _95732 _95731) = (term547 A x _95733 _95732 _95731)) = True.
Proof. exact (TRANS (@lem7156305 A x _95731 _95732 _95733) (@lem7156309 A x _95731 _95732 _95733)). Qed.
Lemma lem7156311 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : True = ((term515 A x _95733 _95732 _95731) = (term547 A x _95733 _95732 _95731)).
Proof. exact (SYM (@lem7156310 A x _95733 _95732 _95731)). Qed.
Lemma lem7156312 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term515 A x _95733 _95732 _95731) = (term547 A x _95733 _95732 _95731).
Proof. exact (EQ_MP (@lem7156311 A x _95733 _95732 _95731) (@lem0)). Qed.
Lemma lem7156313 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term547 A x _95733 _95732 _95731.
Proof. exact (EQ_MP (@lem7156312 A x _95733 _95732 _95731) (@lem7155608 A _95733 _95732 _95731 x h1)). Qed.
Lemma lem7156315 (b : Prop) (a : Prop) : (a \/ b) = (term532 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7156316 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term547 A x _95733 _95732 _95731) = (term553 A x _95731 _95732 _95733).
Proof. exact (@lem7156315 (term525 A _95733 _95732 _95731) (term372 A x _95731 _95732 _95733)). Qed.
Lemma lem7156318 (a : Prop) (b : Prop) : (term534 a b) = (term535 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7156319 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term536 A _95733 _95732 _95731) = (term537 A _95733 _95732 _95731).
Proof. exact (@lem7156318 (term395 A _95732 _95733) ((term358 A _95733 _95731) = (term358 A _95732 _95731))). Qed.
Lemma lem7156321 (a : Prop) : (term538 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7156322 {A : Type'} (_95732 : A -> Prop) (_95733 : A -> Prop) : (term539 A _95732 _95733) = (term394 A _95732 _95733).
Proof. exact (@lem7156321 (term394 A _95732 _95733)). Qed.
Lemma lem7156323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7156324 {A : Type'} (_95732 : A -> Prop) (_95733 : A -> Prop) : (term540 A _95732 _95733) = (term465 A _95732 _95733).
Proof. exact (MK_COMB (@lem7156323) (@lem7156322 A _95732 _95733)). Qed.
Lemma lem7156325 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term521 A _95733 _95732 _95731) = (term521 A _95733 _95732 _95731).
Proof. exact (eq_refl (term521 A _95733 _95732 _95731)). Qed.
Lemma lem7156326 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term537 A _95733 _95732 _95731) = (term541 A _95733 _95732 _95731).
Proof. exact (MK_COMB (@lem7156324 A _95732 _95733) (@lem7156325 A _95733 _95732 _95731)). Qed.
Lemma lem7156327 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term536 A _95733 _95732 _95731) = (term541 A _95733 _95732 _95731).
Proof. exact (TRANS (@lem7156319 A _95733 _95732 _95731) (@lem7156326 A _95733 _95732 _95731)). Qed.
Lemma lem7156328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7156329 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term542 A _95733 _95732 _95731) = (term543 A _95733 _95732 _95731).
Proof. exact (MK_COMB (@lem7156328) (@lem7156327 A _95733 _95732 _95731)). Qed.
Lemma lem7156330 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term372 A x _95731 _95732 _95733) = (term372 A x _95731 _95732 _95733).
Proof. exact (eq_refl (term372 A x _95731 _95732 _95733)). Qed.
Lemma lem7156331 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term553 A x _95731 _95732 _95733) = (term554 A x _95731 _95732 _95733).
Proof. exact (MK_COMB (@lem7156329 A _95733 _95732 _95731) (@lem7156330 A x _95731 _95732 _95733)). Qed.
Lemma lem7156332 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term547 A x _95733 _95732 _95731) = (term554 A x _95731 _95732 _95733).
Proof. exact (TRANS (@lem7156316 A x _95731 _95732 _95733) (@lem7156331 A x _95731 _95732 _95733)). Qed.
Lemma lem7156334 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term521 A s t f) (h2 : term89 A s f t g) : term541 A s t f.
Proof. exact (conj (@lem7156184 A s f t g h2) (@lem7156192 A s t f h1)). Qed.
Lemma lem7156336 {A : Type'} (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) (x : type709 A) (h1 : term354 A x) : term554 A x _95731 _95732 _95733.
Proof. exact (EQ_MP (@lem7156332 A x _95731 _95732 _95733) (@lem7156313 A _95733 _95732 _95731 x h1)). Qed.
Lemma lem7156337 {A : Type'} (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) (x : type709 A) (h1 : term354 A x) : term554 A x _95731 _95732 _95733.
Proof. exact (@lem7156336 A _95731 _95732 _95733 x h1). Qed.
Lemma lem7156338 {A : Type'} (f : A -> real) (t : A -> Prop) (s : A -> Prop) (x : type709 A) (h1 : term354 A x) : term554 A x f t s.
Proof. exact (@lem7156337 A f t s x h1). Qed.
Lemma lem7156341 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term521 A s t f) (h3 : term89 A s f t g) : term372 A x f t s.
Proof. exact (@lem7156338 A f t s x h1 (@lem7156334 A s f t g h2 h3)). Qed.
Lemma lem7156342 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term521 A s t f) (h3 : term89 A s f t g) : term555 A x f t s.
Proof. exact (fun h0 : (term366 A x f t s) = term368 => @lem7156341 A x s f t g h1 h2 h3). Qed.
Lemma lem7156344 (p : Prop) : (term523 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7156345 {A : Type'} (x : type709 A) (f : A -> real) (t : A -> Prop) (s : A -> Prop) : (term555 A x f t s) = (term372 A x f t s).
Proof. exact (@lem7156344 ((term366 A x f t s) = term368)). Qed.
Lemma lem7156346 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term521 A s t f) (h3 : term89 A s f t g) : term372 A x f t s.
Proof. exact (EQ_MP (@lem7156345 A x f t s) (@lem7156342 A x s f t g h1 h2 h3)). Qed.
Lemma lem7156352 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7156353 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> real) (_95741 : A) : (term512 A s t f _95741) = (term556 A t s f _95741).
Proof. exact (@lem7156352 (term452 A _95741 t) (term453 A _95741 s) ((@I (A -> real) f _95741) = term368)). Qed.
Lemma lem7156367 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7156368 {A : Type'} (f : A -> real) (_95741 : A) (s : A -> Prop) : (term557 A s f _95741) = (term558 A f _95741 s).
Proof. exact (@lem7156367 ((@I (A -> real) f _95741) = term368) (term453 A _95741 s)). Qed.
Lemma lem7156376 {A : Type'} (_95741 : A) (t : A -> Prop) : (term559 A _95741 t) = (term559 A _95741 t).
Proof. exact (eq_refl (term559 A _95741 t)). Qed.
Lemma lem7156377 {A : Type'} (t : A -> Prop) (f : A -> real) (_95741 : A) (s : A -> Prop) : (term556 A t s f _95741) = (term560 A t f _95741 s).
Proof. exact (MK_COMB (@lem7156376 A _95741 t) (@lem7156368 A f _95741 s)). Qed.
Lemma lem7156381 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7156382 {A : Type'} (f : A -> real) (t : A -> Prop) (_95741 : A) (s : A -> Prop) : (term560 A t f _95741 s) = (term561 A f t _95741 s).
Proof. exact (@lem7156381 ((@I (A -> real) f _95741) = term368) (term452 A _95741 t) (term453 A _95741 s)). Qed.
Lemma lem7156400 {A : Type'} (f : A -> real) (t : A -> Prop) (_95741 : A) (s : A -> Prop) : (term556 A t s f _95741) = (term561 A f t _95741 s).
Proof. exact (TRANS (@lem7156377 A t f _95741 s) (@lem7156382 A f t _95741 s)). Qed.
Lemma lem7156401 {A : Type'} (f : A -> real) (t : A -> Prop) (_95741 : A) (s : A -> Prop) : (term512 A s t f _95741) = (term561 A f t _95741 s).
Proof. exact (TRANS (@lem7156353 A t s f _95741) (@lem7156400 A f t _95741 s)). Qed.
Lemma lem7156402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7156403 {A : Type'} (f : A -> real) (t : A -> Prop) (_95741 : A) (s : A -> Prop) : (term562 A s t f _95741) = (term563 A f t _95741 s).
Proof. exact (MK_COMB (@lem7156402) (@lem7156401 A f t _95741 s)). Qed.
Lemma lem7156417 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7156418 {A : Type'} (f : A -> real) (_95741 : A) (s : A -> Prop) : (term557 A s f _95741) = (term558 A f _95741 s).
Proof. exact (@lem7156417 ((@I (A -> real) f _95741) = term368) (term453 A _95741 s)). Qed.
Lemma lem7156426 {A : Type'} (_95741 : A) (t : A -> Prop) : (term559 A _95741 t) = (term559 A _95741 t).
Proof. exact (eq_refl (term559 A _95741 t)). Qed.
Lemma lem7156427 {A : Type'} (t : A -> Prop) (f : A -> real) (_95741 : A) (s : A -> Prop) : (term556 A t s f _95741) = (term560 A t f _95741 s).
Proof. exact (MK_COMB (@lem7156426 A _95741 t) (@lem7156418 A f _95741 s)). Qed.
Lemma lem7156431 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7156432 {A : Type'} (f : A -> real) (t : A -> Prop) (_95741 : A) (s : A -> Prop) : (term560 A t f _95741 s) = (term561 A f t _95741 s).
Proof. exact (@lem7156431 ((@I (A -> real) f _95741) = term368) (term452 A _95741 t) (term453 A _95741 s)). Qed.
Lemma lem7156450 {A : Type'} (f : A -> real) (t : A -> Prop) (_95741 : A) (s : A -> Prop) : (term556 A t s f _95741) = (term561 A f t _95741 s).
Proof. exact (TRANS (@lem7156427 A t f _95741 s) (@lem7156432 A f t _95741 s)). Qed.
Lemma lem7156451 {A : Type'} (f : A -> real) (t : A -> Prop) (_95741 : A) (s : A -> Prop) : ((term512 A s t f _95741) = (term556 A t s f _95741)) = ((term561 A f t _95741 s) = (term561 A f t _95741 s)).
Proof. exact (MK_COMB (@lem7156403 A f t _95741 s) (@lem7156450 A f t _95741 s)). Qed.
Lemma lem7156453 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7156454 (x : Prop) : (x = x) = True.
Proof. exact (@lem7156453 Prop x). Qed.
Lemma lem7156455 {A : Type'} (f : A -> real) (t : A -> Prop) (_95741 : A) (s : A -> Prop) : ((term561 A f t _95741 s) = (term561 A f t _95741 s)) = True.
Proof. exact (@lem7156454 (term561 A f t _95741 s)). Qed.
Lemma lem7156456 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> real) (_95741 : A) : ((term512 A s t f _95741) = (term556 A t s f _95741)) = True.
Proof. exact (TRANS (@lem7156451 A f t _95741 s) (@lem7156455 A f t _95741 s)). Qed.
Lemma lem7156457 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> real) (_95741 : A) : True = ((term512 A s t f _95741) = (term556 A t s f _95741)).
Proof. exact (SYM (@lem7156456 A t s f _95741)). Qed.
Lemma lem7156458 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> real) (_95741 : A) : (term512 A s t f _95741) = (term556 A t s f _95741).
Proof. exact (EQ_MP (@lem7156457 A t s f _95741) (@lem0)). Qed.
Lemma lem7156459 {A : Type'} (_95741 : A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term556 A t s f _95741.
Proof. exact (EQ_MP (@lem7156458 A t s f _95741) (@lem7155572 A _95741 s f t g h1)). Qed.
Lemma lem7156461 (b : Prop) (a : Prop) : (a \/ b) = (term532 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7156462 {A : Type'} (s : A -> Prop) (f : A -> real) (_95741 : A) (t : A -> Prop) : (term556 A t s f _95741) = (term564 A s f _95741 t).
Proof. exact (@lem7156461 (term557 A s f _95741) (term452 A _95741 t)). Qed.
Lemma lem7156464 (a : Prop) (b : Prop) : (term534 a b) = (term535 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7156465 {A : Type'} (s : A -> Prop) (f : A -> real) (_95741 : A) : (term565 A s f _95741) = (term566 A s f _95741).
Proof. exact (@lem7156464 (term453 A _95741 s) ((@I (A -> real) f _95741) = term368)). Qed.
Lemma lem7156467 (a : Prop) : (term538 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7156468 {A : Type'} (_95741 : A) (s : A -> Prop) : (term567 A _95741 s) = (term452 A _95741 s).
Proof. exact (@lem7156467 (term452 A _95741 s)). Qed.
Lemma lem7156469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7156470 {A : Type'} (_95741 : A) (s : A -> Prop) : (term568 A _95741 s) = (term569 A _95741 s).
Proof. exact (MK_COMB (@lem7156469) (@lem7156468 A _95741 s)). Qed.
Lemma lem7156471 {A : Type'} (f : A -> real) (_95741 : A) : (term570 A f _95741) = (term570 A f _95741).
Proof. exact (eq_refl (term570 A f _95741)). Qed.
Lemma lem7156472 {A : Type'} (s : A -> Prop) (f : A -> real) (_95741 : A) : (term566 A s f _95741) = (term571 A s f _95741).
Proof. exact (MK_COMB (@lem7156470 A _95741 s) (@lem7156471 A f _95741)). Qed.
Lemma lem7156473 {A : Type'} (s : A -> Prop) (f : A -> real) (_95741 : A) : (term565 A s f _95741) = (term571 A s f _95741).
Proof. exact (TRANS (@lem7156465 A s f _95741) (@lem7156472 A s f _95741)). Qed.
Lemma lem7156474 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7156475 {A : Type'} (s : A -> Prop) (f : A -> real) (_95741 : A) : (term572 A s f _95741) = (term573 A s f _95741).
Proof. exact (MK_COMB (@lem7156474) (@lem7156473 A s f _95741)). Qed.
Lemma lem7156476 {A : Type'} (_95741 : A) (t : A -> Prop) : (term452 A _95741 t) = (term452 A _95741 t).
Proof. exact (eq_refl (term452 A _95741 t)). Qed.
Lemma lem7156477 {A : Type'} (s : A -> Prop) (f : A -> real) (_95741 : A) (t : A -> Prop) : (term564 A s f _95741 t) = (term574 A s f _95741 t).
Proof. exact (MK_COMB (@lem7156475 A s f _95741) (@lem7156476 A _95741 t)). Qed.
Lemma lem7156478 {A : Type'} (s : A -> Prop) (f : A -> real) (_95741 : A) (t : A -> Prop) : (term556 A t s f _95741) = (term574 A s f _95741 t).
Proof. exact (TRANS (@lem7156462 A s f _95741 t) (@lem7156477 A s f _95741 t)). Qed.
Lemma lem7156480 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term521 A s t f) (h3 : term89 A s f t g) : term575 A x f t s.
Proof. exact (conj (@lem7156177 A x s f t g h1 h2 h3) (@lem7156346 A x s f t g h1 h2 h3)). Qed.
Lemma lem7156482 {A : Type'} (_95741 : A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term574 A s f _95741 t.
Proof. exact (EQ_MP (@lem7156478 A s f _95741 t) (@lem7156459 A _95741 s f t g h1)). Qed.
Lemma lem7156483 {A : Type'} (_95741 : A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term574 A s f _95741 t.
Proof. exact (@lem7156482 A _95741 s f t g h1). Qed.
Lemma lem7156484 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term576 A x f s t.
Proof. exact (@lem7156483 A (term363 A x f t s) s f t g h1). Qed.
Lemma lem7156487 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term521 A s t f) (h3 : term89 A s f t g) : term379 A x f s t.
Proof. exact (@lem7156484 A x s f t g h3 (@lem7156480 A x s f t g h1 h2 h3)). Qed.
Lemma lem7156488 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term521 A s t f) (h3 : term89 A s f t g) : term577 A x f s t.
Proof. exact (fun h0 : term381 A x f s t => @lem7156487 A x s f t g h1 h2 h3). Qed.
Lemma lem7156490 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156491 {A : Type'} (x : type709 A) (f : A -> real) (s : A -> Prop) (t : A -> Prop) : (term577 A x f s t) = (term379 A x f s t).
Proof. exact (@lem7156490 (term379 A x f s t)). Qed.
Lemma lem7156492 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term521 A s t f) (h3 : term89 A s f t g) : term379 A x f s t.
Proof. exact (EQ_MP (@lem7156491 A x f s t) (@lem7156488 A x s f t g h1 h2 h3)). Qed.
Lemma lem7156498 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7156499 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term517 A x _95733 _95732 _95731) = (term578 A x _95733 _95732 _95731).
Proof. exact (@lem7156498 (term381 A x _95731 _95733 _95732) (term395 A _95732 _95733) ((term358 A _95733 _95731) = (term358 A _95732 _95731))). Qed.
Lemma lem7156513 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7156514 {A : Type'} (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term525 A _95733 _95732 _95731) = (term526 A _95731 _95732 _95733).
Proof. exact (@lem7156513 ((term358 A _95733 _95731) = (term358 A _95732 _95731)) (term395 A _95732 _95733)). Qed.
Lemma lem7156522 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95733 : A -> Prop) (_95732 : A -> Prop) : (term579 A x _95731 _95733 _95732) = (term579 A x _95731 _95733 _95732).
Proof. exact (eq_refl (term579 A x _95731 _95733 _95732)). Qed.
Lemma lem7156523 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term578 A x _95733 _95732 _95731) = (term580 A x _95731 _95732 _95733).
Proof. exact (MK_COMB (@lem7156522 A x _95731 _95733 _95732) (@lem7156514 A _95731 _95732 _95733)). Qed.
Lemma lem7156527 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7156528 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term580 A x _95731 _95732 _95733) = (term581 A x _95731 _95732 _95733).
Proof. exact (@lem7156527 ((term358 A _95733 _95731) = (term358 A _95732 _95731)) (term381 A x _95731 _95733 _95732) (term395 A _95732 _95733)). Qed.
Lemma lem7156546 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term578 A x _95733 _95732 _95731) = (term581 A x _95731 _95732 _95733).
Proof. exact (TRANS (@lem7156523 A x _95731 _95732 _95733) (@lem7156528 A x _95731 _95732 _95733)). Qed.
Lemma lem7156547 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term517 A x _95733 _95732 _95731) = (term581 A x _95731 _95732 _95733).
Proof. exact (TRANS (@lem7156499 A x _95733 _95732 _95731) (@lem7156546 A x _95731 _95732 _95733)). Qed.
Lemma lem7156548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7156549 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term582 A x _95733 _95732 _95731) = (term583 A x _95731 _95732 _95733).
Proof. exact (MK_COMB (@lem7156548) (@lem7156547 A x _95731 _95732 _95733)). Qed.
Lemma lem7156565 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7156566 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term485 A x _95731 _95733 _95732) = (term584 A x _95731 _95732 _95733).
Proof. exact (@lem7156565 (term381 A x _95731 _95733 _95732) (term395 A _95732 _95733)). Qed.
Lemma lem7156572 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term585 A _95733 _95732 _95731) = (term585 A _95733 _95732 _95731).
Proof. exact (eq_refl (term585 A _95733 _95732 _95731)). Qed.
Lemma lem7156573 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : (term586 A x _95731 _95733 _95732) = (term581 A x _95731 _95732 _95733).
Proof. exact (MK_COMB (@lem7156572 A _95733 _95732 _95731) (@lem7156566 A x _95731 _95732 _95733)). Qed.
Lemma lem7156584 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : ((term517 A x _95733 _95732 _95731) = (term586 A x _95731 _95733 _95732)) = ((term581 A x _95731 _95732 _95733) = (term581 A x _95731 _95732 _95733)).
Proof. exact (MK_COMB (@lem7156549 A x _95731 _95732 _95733) (@lem7156573 A x _95731 _95732 _95733)). Qed.
Lemma lem7156586 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7156587 (x : Prop) : (x = x) = True.
Proof. exact (@lem7156586 Prop x). Qed.
Lemma lem7156588 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95732 : A -> Prop) (_95733 : A -> Prop) : ((term581 A x _95731 _95732 _95733) = (term581 A x _95731 _95732 _95733)) = True.
Proof. exact (@lem7156587 (term581 A x _95731 _95732 _95733)). Qed.
Lemma lem7156589 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95733 : A -> Prop) (_95732 : A -> Prop) : ((term517 A x _95733 _95732 _95731) = (term586 A x _95731 _95733 _95732)) = True.
Proof. exact (TRANS (@lem7156584 A x _95731 _95732 _95733) (@lem7156588 A x _95731 _95732 _95733)). Qed.
Lemma lem7156590 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95733 : A -> Prop) (_95732 : A -> Prop) : True = ((term517 A x _95733 _95732 _95731) = (term586 A x _95731 _95733 _95732)).
Proof. exact (SYM (@lem7156589 A x _95731 _95733 _95732)). Qed.
Lemma lem7156591 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95733 : A -> Prop) (_95732 : A -> Prop) : (term517 A x _95733 _95732 _95731) = (term586 A x _95731 _95733 _95732).
Proof. exact (EQ_MP (@lem7156590 A x _95731 _95733 _95732) (@lem0)). Qed.
Lemma lem7156592 {A : Type'} (_95731 : A -> real) (_95733 : A -> Prop) (_95732 : A -> Prop) (x : type709 A) (h1 : term354 A x) : term586 A x _95731 _95733 _95732.
Proof. exact (EQ_MP (@lem7156591 A x _95731 _95733 _95732) (@lem7155632 A _95733 _95732 _95731 x h1)). Qed.
Lemma lem7156594 (b : Prop) (a : Prop) : (a \/ b) = (term532 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7156595 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term586 A x _95731 _95733 _95732) = (term587 A x _95733 _95732 _95731).
Proof. exact (@lem7156594 (term485 A x _95731 _95733 _95732) ((term358 A _95733 _95731) = (term358 A _95732 _95731))). Qed.
Lemma lem7156597 (a : Prop) (b : Prop) : (term534 a b) = (term535 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7156598 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95733 : A -> Prop) (_95732 : A -> Prop) : (term588 A x _95731 _95733 _95732) = (term589 A x _95731 _95733 _95732).
Proof. exact (@lem7156597 (term395 A _95732 _95733) (term381 A x _95731 _95733 _95732)). Qed.
Lemma lem7156600 (a : Prop) : (term538 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7156601 {A : Type'} (_95732 : A -> Prop) (_95733 : A -> Prop) : (term539 A _95732 _95733) = (term394 A _95732 _95733).
Proof. exact (@lem7156600 (term394 A _95732 _95733)). Qed.
Lemma lem7156602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7156603 {A : Type'} (_95732 : A -> Prop) (_95733 : A -> Prop) : (term540 A _95732 _95733) = (term465 A _95732 _95733).
Proof. exact (MK_COMB (@lem7156602) (@lem7156601 A _95732 _95733)). Qed.
Lemma lem7156605 (a : Prop) : (term538 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7156606 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95733 : A -> Prop) (_95732 : A -> Prop) : (term590 A x _95731 _95733 _95732) = (term379 A x _95731 _95733 _95732).
Proof. exact (@lem7156605 (term379 A x _95731 _95733 _95732)). Qed.
Lemma lem7156607 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95733 : A -> Prop) (_95732 : A -> Prop) : (term589 A x _95731 _95733 _95732) = (term591 A x _95731 _95733 _95732).
Proof. exact (MK_COMB (@lem7156603 A _95732 _95733) (@lem7156606 A x _95731 _95733 _95732)). Qed.
Lemma lem7156608 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95733 : A -> Prop) (_95732 : A -> Prop) : (term588 A x _95731 _95733 _95732) = (term591 A x _95731 _95733 _95732).
Proof. exact (TRANS (@lem7156598 A x _95731 _95733 _95732) (@lem7156607 A x _95731 _95733 _95732)). Qed.
Lemma lem7156609 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7156610 {A : Type'} (x : type709 A) (_95731 : A -> real) (_95733 : A -> Prop) (_95732 : A -> Prop) : (term592 A x _95731 _95733 _95732) = (term593 A x _95731 _95733 _95732).
Proof. exact (MK_COMB (@lem7156609) (@lem7156608 A x _95731 _95733 _95732)). Qed.
Lemma lem7156611 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : ((term358 A _95733 _95731) = (term358 A _95732 _95731)) = ((term358 A _95733 _95731) = (term358 A _95732 _95731)).
Proof. exact (eq_refl ((term358 A _95733 _95731) = (term358 A _95732 _95731))). Qed.
Lemma lem7156612 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term587 A x _95733 _95732 _95731) = (term594 A x _95733 _95732 _95731).
Proof. exact (MK_COMB (@lem7156610 A x _95731 _95733 _95732) (@lem7156611 A _95733 _95732 _95731)). Qed.
Lemma lem7156613 {A : Type'} (x : type709 A) (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) : (term586 A x _95731 _95733 _95732) = (term594 A x _95733 _95732 _95731).
Proof. exact (TRANS (@lem7156595 A x _95733 _95732 _95731) (@lem7156612 A x _95733 _95732 _95731)). Qed.
Lemma lem7156615 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term521 A s t f) (h3 : term89 A s f t g) : term591 A x f s t.
Proof. exact (conj (@lem7156016 A s f t g h3) (@lem7156492 A x s f t g h1 h2 h3)). Qed.
Lemma lem7156617 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term594 A x _95733 _95732 _95731.
Proof. exact (EQ_MP (@lem7156613 A x _95733 _95732 _95731) (@lem7156592 A _95731 _95733 _95732 x h1)). Qed.
Lemma lem7156618 {A : Type'} (_95733 : A -> Prop) (_95732 : A -> Prop) (_95731 : A -> real) (x : type709 A) (h1 : term354 A x) : term594 A x _95733 _95732 _95731.
Proof. exact (@lem7156617 A _95733 _95732 _95731 x h1). Qed.
Lemma lem7156619 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) (x : type709 A) (h1 : term354 A x) : term594 A x s t f.
Proof. exact (@lem7156618 A s t f x h1). Qed.
Lemma lem7156622 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term521 A s t f) (h3 : term89 A s f t g) : (term358 A s f) = (term358 A t f).
Proof. exact (@lem7156619 A s t f x h1 (@lem7156615 A x s f t g h1 h2 h3)). Qed.
Lemma lem7156623 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term89 A s f t g) : term595 A s t f.
Proof. exact (fun h0 : term521 A s t f => @lem7156622 A x s f t g h1 h0 h2). Qed.
Lemma lem7156625 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156626 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : (term595 A s t f) = ((term358 A s f) = (term358 A t f)).
Proof. exact (@lem7156625 ((term358 A s f) = (term358 A t f))). Qed.
Lemma lem7156627 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term89 A s f t g) : (term358 A s f) = (term358 A t f).
Proof. exact (EQ_MP (@lem7156626 A s t f) (@lem7156623 A x s f t g h1 h2)). Qed.
Lemma lem7156629 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem7156630 {A : Type'} (s : A -> Prop) (f : A -> real) : (term358 A s f) = (term358 A s f).
Proof. exact (@lem7156629 (term358 A s f)). Qed.
Lemma lem7156631 {A : Type'} (s : A -> Prop) (f : A -> real) : term596 A s f.
Proof. exact (fun h0 : term597 A s f => @lem7156630 A s f). Qed.
Lemma lem7156633 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156634 {A : Type'} (s : A -> Prop) (f : A -> real) : (term596 A s f) = ((term358 A s f) = (term358 A s f)).
Proof. exact (@lem7156633 ((term358 A s f) = (term358 A s f))). Qed.
Lemma lem7156635 {A : Type'} (s : A -> Prop) (f : A -> real) : (term358 A s f) = (term358 A s f).
Proof. exact (EQ_MP (@lem7156634 A s f) (@lem7156631 A s f)). Qed.
Lemma lem7156653 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7156654 (y : real) (x : real) (z : real) : (term598 x y z) = (term599 y x z).
Proof. exact (@lem7156653 (y = z) (term600 x z)). Qed.
Lemma lem7156664 (x : real) (y : real) : (term601 x y) = (term601 x y).
Proof. exact (eq_refl (term601 x y)). Qed.
Lemma lem7156665 (y : real) (x : real) (z : real) : (term518 x y z) = (term602 y x z).
Proof. exact (MK_COMB (@lem7156664 x y) (@lem7156654 y x z)). Qed.
Lemma lem7156669 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7156670 (y : real) (x : real) (z : real) : (term602 y x z) = (term603 y x z).
Proof. exact (@lem7156669 (y = z) (term600 x y) (term600 x z)). Qed.
Lemma lem7156692 (y : real) (x : real) (z : real) : (term518 x y z) = (term603 y x z).
Proof. exact (TRANS (@lem7156665 y x z) (@lem7156670 y x z)). Qed.
Lemma lem7156693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7156694 (y : real) (x : real) (z : real) : (term604 x y z) = (term605 y x z).
Proof. exact (MK_COMB (@lem7156693) (@lem7156692 y x z)). Qed.
Lemma lem7156716 (y : real) (x : real) (z : real) : (term603 y x z) = (term603 y x z).
Proof. exact (eq_refl (term603 y x z)). Qed.
Lemma lem7156717 (y : real) (x : real) (z : real) : ((term518 x y z) = (term603 y x z)) = ((term603 y x z) = (term603 y x z)).
Proof. exact (MK_COMB (@lem7156694 y x z) (@lem7156716 y x z)). Qed.
Lemma lem7156719 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7156720 (x : Prop) : (x = x) = True.
Proof. exact (@lem7156719 Prop x). Qed.
Lemma lem7156721 (y : real) (x : real) (z : real) : ((term603 y x z) = (term603 y x z)) = True.
Proof. exact (@lem7156720 (term603 y x z)). Qed.
Lemma lem7156722 (y : real) (x : real) (z : real) : ((term518 x y z) = (term603 y x z)) = True.
Proof. exact (TRANS (@lem7156717 y x z) (@lem7156721 y x z)). Qed.
Lemma lem7156723 (y : real) (x : real) (z : real) : True = ((term518 x y z) = (term603 y x z)).
Proof. exact (SYM (@lem7156722 y x z)). Qed.
Lemma lem7156724 (y : real) (x : real) (z : real) : (term518 x y z) = (term603 y x z).
Proof. exact (EQ_MP (@lem7156723 y x z) (@lem0)). Qed.
Lemma lem7156725 (y : real) (x : real) (z : real) : term603 y x z.
Proof. exact (EQ_MP (@lem7156724 y x z) (@lem7155957 x y z)). Qed.
Lemma lem7156727 (b : Prop) (a : Prop) : (a \/ b) = (term532 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7156728 (x : real) (y : real) (z : real) : (term603 y x z) = (term606 x y z).
Proof. exact (@lem7156727 (term607 y x z) (y = z)). Qed.
Lemma lem7156730 (a : Prop) (b : Prop) : (term534 a b) = (term535 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7156731 (y : real) (x : real) (z : real) : (term608 y x z) = (term609 y x z).
Proof. exact (@lem7156730 (term600 x y) (term600 x z)). Qed.
Lemma lem7156733 (a : Prop) : (term538 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7156734 (x : real) (y : real) : (term610 x y) = (x = y).
Proof. exact (@lem7156733 (x = y)). Qed.
Lemma lem7156735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7156736 (x : real) (y : real) : (term611 x y) = (term612 x y).
Proof. exact (MK_COMB (@lem7156735) (@lem7156734 x y)). Qed.
Lemma lem7156738 (a : Prop) : (term538 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7156739 (x : real) (z : real) : (term610 x z) = (x = z).
Proof. exact (@lem7156738 (x = z)). Qed.
Lemma lem7156740 (y : real) (x : real) (z : real) : (term609 y x z) = (term613 y x z).
Proof. exact (MK_COMB (@lem7156736 x y) (@lem7156739 x z)). Qed.
Lemma lem7156741 (y : real) (x : real) (z : real) : (term608 y x z) = (term613 y x z).
Proof. exact (TRANS (@lem7156731 y x z) (@lem7156740 y x z)). Qed.
Lemma lem7156742 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7156743 (y : real) (x : real) (z : real) : (term614 y x z) = (term615 y x z).
Proof. exact (MK_COMB (@lem7156742) (@lem7156741 y x z)). Qed.
Lemma lem7156744 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7156745 (x : real) (y : real) (z : real) : (term606 x y z) = (term616 x y z).
Proof. exact (MK_COMB (@lem7156743 y x z) (@lem7156744 y z)). Qed.
Lemma lem7156746 (x : real) (y : real) (z : real) : (term603 y x z) = (term616 x y z).
Proof. exact (TRANS (@lem7156728 x y z) (@lem7156745 x y z)). Qed.
Lemma lem7156748 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term89 A s f t g) : term617 A t s f.
Proof. exact (conj (@lem7156627 A x s f t g h1 h2) (@lem7156635 A s f)). Qed.
Lemma lem7156750 (x : real) (y : real) (z : real) : term616 x y z.
Proof. exact (EQ_MP (@lem7156746 x y z) (@lem7156725 y x z)). Qed.
Lemma lem7156751 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> real) : term618 A t s f.
Proof. exact (@lem7156750 (term358 A s f) (term358 A t f) (term358 A s f)). Qed.
Lemma lem7156754 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term89 A s f t g) : (term358 A t f) = (term358 A s f).
Proof. exact (@lem7156751 A t s f (@lem7156748 A x s f t g h1 h2)). Qed.
Lemma lem7156755 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term89 A s f t g) : term595 A t s f.
Proof. exact (fun h0 : term521 A t s f => @lem7156754 A x s f t g h1 h2). Qed.
Lemma lem7156757 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156758 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> real) : (term595 A t s f) = ((term358 A t f) = (term358 A s f)).
Proof. exact (@lem7156757 ((term358 A t f) = (term358 A s f))). Qed.
Lemma lem7156759 {A : Type'} (x : type709 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term89 A s f t g) : (term358 A t f) = (term358 A s f).
Proof. exact (EQ_MP (@lem7156758 A t s f) (@lem7156755 A x s f t g h1 h2)). Qed.
Lemma lem7156762 {A : Type'} (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term619 A f t g) : term619 A f t g.
Proof. exact (h1). Qed.
Lemma lem7156763 {A : Type'} (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term619 A f t g) : term620 A f t g.
Proof. exact (fun h0 : (term358 A t f) = (term358 A t g) => @lem7156762 A f t g h1). Qed.
Lemma lem7156765 (p : Prop) : (term523 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7156766 {A : Type'} (f : A -> real) (t : A -> Prop) (g : A -> real) : (term620 A f t g) = (term619 A f t g).
Proof. exact (@lem7156765 ((term358 A t f) = (term358 A t g))). Qed.
Lemma lem7156767 {A : Type'} (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term619 A f t g) : term619 A f t g.
Proof. exact (EQ_MP (@lem7156766 A f t g) (@lem7156763 A f t g h1)). Qed.
Lemma lem7156769 (b : Prop) (a : Prop) : (a \/ b) = (term532 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7156772 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) : (term513 A x' _95734 _95736 _95735) = (term621 A x' _95734 _95735 _95736).
Proof. exact (@lem7156769 ((term358 A _95736 _95734) = (term358 A _95736 _95735)) (term431 A x' _95734 _95735 _95736)). Qed.
Lemma lem7156775 {A : Type'} (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) (x' : type711 A) (h1 : term226 A x') : term621 A x' _95734 _95735 _95736.
Proof. exact (EQ_MP (@lem7156772 A x' _95734 _95735 _95736) (@lem7155590 A _95734 _95736 _95735 x' h1)). Qed.
Lemma lem7156776 {A : Type'} (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) (x' : type711 A) (h1 : term226 A x') : term621 A x' _95734 _95735 _95736.
Proof. exact (@lem7156775 A _95734 _95735 _95736 x' h1). Qed.
Lemma lem7156777 {A : Type'} (f : A -> real) (g : A -> real) (t : A -> Prop) (x' : type711 A) (h1 : term226 A x') : term621 A x' f g t.
Proof. exact (@lem7156776 A f g t x' h1). Qed.
Lemma lem7156780 {A : Type'} (x' : type711 A) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term226 A x') (h2 : term619 A f t g) : term431 A x' f g t.
Proof. exact (@lem7156777 A f g t x' h1 (@lem7156767 A f t g h2)). Qed.
Lemma lem7156781 {A : Type'} (x' : type711 A) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term226 A x') (h2 : term619 A f t g) : term622 A x' f g t.
Proof. exact (fun h0 : term623 A x' f g t => @lem7156780 A x' f t g h1 h2). Qed.
Lemma lem7156783 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156784 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (t : A -> Prop) : (term622 A x' f g t) = (term431 A x' f g t).
Proof. exact (@lem7156783 (term431 A x' f g t)). Qed.
Lemma lem7156785 {A : Type'} (x' : type711 A) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term226 A x') (h2 : term619 A f t g) : term431 A x' f g t.
Proof. exact (EQ_MP (@lem7156784 A x' f g t) (@lem7156781 A x' f t g h1 h2)). Qed.
Lemma lem7156791 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7156792 {A : Type'} (f : A -> real) (g : A -> real) (_95740 : A) (t : A -> Prop) : (term460 A t f g _95740) = (term624 A f g _95740 t).
Proof. exact (@lem7156791 ((@I (A -> real) f _95740) = (@I (A -> real) g _95740)) (term453 A _95740 t)). Qed.
Lemma lem7156800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7156801 {A : Type'} (f : A -> real) (g : A -> real) (_95740 : A) (t : A -> Prop) : (term625 A t f g _95740) = (term626 A f g _95740 t).
Proof. exact (MK_COMB (@lem7156800) (@lem7156792 A f g _95740 t)). Qed.
Lemma lem7156809 {A : Type'} (f : A -> real) (g : A -> real) (_95740 : A) (t : A -> Prop) : (term624 A f g _95740 t) = (term624 A f g _95740 t).
Proof. exact (eq_refl (term624 A f g _95740 t)). Qed.
Lemma lem7156810 {A : Type'} (f : A -> real) (g : A -> real) (_95740 : A) (t : A -> Prop) : ((term460 A t f g _95740) = (term624 A f g _95740 t)) = ((term624 A f g _95740 t) = (term624 A f g _95740 t)).
Proof. exact (MK_COMB (@lem7156801 A f g _95740 t) (@lem7156809 A f g _95740 t)). Qed.
Lemma lem7156812 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7156813 (x : Prop) : (x = x) = True.
Proof. exact (@lem7156812 Prop x). Qed.
Lemma lem7156814 {A : Type'} (f : A -> real) (g : A -> real) (_95740 : A) (t : A -> Prop) : ((term624 A f g _95740 t) = (term624 A f g _95740 t)) = True.
Proof. exact (@lem7156813 (term624 A f g _95740 t)). Qed.
Lemma lem7156815 {A : Type'} (f : A -> real) (g : A -> real) (_95740 : A) (t : A -> Prop) : ((term460 A t f g _95740) = (term624 A f g _95740 t)) = True.
Proof. exact (TRANS (@lem7156810 A f g _95740 t) (@lem7156814 A f g _95740 t)). Qed.
Lemma lem7156816 {A : Type'} (f : A -> real) (g : A -> real) (_95740 : A) (t : A -> Prop) : True = ((term460 A t f g _95740) = (term624 A f g _95740 t)).
Proof. exact (SYM (@lem7156815 A f g _95740 t)). Qed.
Lemma lem7156817 {A : Type'} (f : A -> real) (g : A -> real) (_95740 : A) (t : A -> Prop) : (term460 A t f g _95740) = (term624 A f g _95740 t).
Proof. exact (EQ_MP (@lem7156816 A f g _95740 t) (@lem0)). Qed.
Lemma lem7156818 {A : Type'} (_95740 : A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term624 A f g _95740 t.
Proof. exact (EQ_MP (@lem7156817 A f g _95740 t) (@lem7155560 A _95740 s f t g h1)). Qed.
Lemma lem7156820 (b : Prop) (a : Prop) : (a \/ b) = (term532 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7156821 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) (_95740 : A) : (term624 A f g _95740 t) = (term627 A t f g _95740).
Proof. exact (@lem7156820 (term453 A _95740 t) ((@I (A -> real) f _95740) = (@I (A -> real) g _95740))). Qed.
Lemma lem7156823 (a : Prop) : (term538 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7156824 {A : Type'} (_95740 : A) (t : A -> Prop) : (term567 A _95740 t) = (term452 A _95740 t).
Proof. exact (@lem7156823 (term452 A _95740 t)). Qed.
Lemma lem7156825 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7156826 {A : Type'} (_95740 : A) (t : A -> Prop) : (term628 A _95740 t) = (term629 A _95740 t).
Proof. exact (MK_COMB (@lem7156825) (@lem7156824 A _95740 t)). Qed.
Lemma lem7156827 {A : Type'} (f : A -> real) (g : A -> real) (_95740 : A) : ((@I (A -> real) f _95740) = (@I (A -> real) g _95740)) = ((@I (A -> real) f _95740) = (@I (A -> real) g _95740)).
Proof. exact (eq_refl ((@I (A -> real) f _95740) = (@I (A -> real) g _95740))). Qed.
Lemma lem7156828 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) (_95740 : A) : (term627 A t f g _95740) = (term630 A t f g _95740).
Proof. exact (MK_COMB (@lem7156826 A _95740 t) (@lem7156827 A f g _95740)). Qed.
Lemma lem7156829 {A : Type'} (t : A -> Prop) (f : A -> real) (g : A -> real) (_95740 : A) : (term624 A f g _95740 t) = (term630 A t f g _95740).
Proof. exact (TRANS (@lem7156821 A t f g _95740) (@lem7156828 A t f g _95740)). Qed.
Lemma lem7156832 {A : Type'} (_95740 : A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term630 A t f g _95740.
Proof. exact (EQ_MP (@lem7156829 A t f g _95740) (@lem7156818 A _95740 s f t g h1)). Qed.
Lemma lem7156833 {A : Type'} (_95740 : A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term630 A t f g _95740.
Proof. exact (@lem7156832 A _95740 s f t g h1). Qed.
Lemma lem7156834 {A : Type'} (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term631 A x' f g t.
Proof. exact (@lem7156833 A (term414 A x' f g t) s f t g h1). Qed.
Lemma lem7156837 {A : Type'} (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term226 A x') (h2 : term619 A f t g) (h3 : term89 A s f t g) : (term417 A x' f g t) = (term420 A x' f g t).
Proof. exact (@lem7156834 A x' s f t g h3 (@lem7156785 A x' f t g h1 h2)). Qed.
Lemma lem7156838 {A : Type'} (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term226 A x') (h2 : term619 A f t g) (h3 : term89 A s f t g) : term632 A x' f g t.
Proof. exact (fun h0 : term424 A x' f g t => @lem7156837 A x' s f t g h1 h2 h3). Qed.
Lemma lem7156840 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156841 {A : Type'} (x' : type711 A) (f : A -> real) (g : A -> real) (t : A -> Prop) : (term632 A x' f g t) = ((term417 A x' f g t) = (term420 A x' f g t)).
Proof. exact (@lem7156840 ((term417 A x' f g t) = (term420 A x' f g t))). Qed.
Lemma lem7156842 {A : Type'} (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term226 A x') (h2 : term619 A f t g) (h3 : term89 A s f t g) : (term417 A x' f g t) = (term420 A x' f g t).
Proof. exact (EQ_MP (@lem7156841 A x' f g t) (@lem7156838 A x' s f t g h1 h2 h3)). Qed.
Lemma lem7156848 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7156849 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) : (term514 A x' _95734 _95736 _95735) = (term633 A x' _95734 _95735 _95736).
Proof. exact (@lem7156848 ((term358 A _95736 _95734) = (term358 A _95736 _95735)) (term424 A x' _95734 _95735 _95736)). Qed.
Lemma lem7156859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7156860 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) : (term634 A x' _95734 _95736 _95735) = (term635 A x' _95734 _95735 _95736).
Proof. exact (MK_COMB (@lem7156859) (@lem7156849 A x' _95734 _95735 _95736)). Qed.
Lemma lem7156870 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) : (term633 A x' _95734 _95735 _95736) = (term633 A x' _95734 _95735 _95736).
Proof. exact (eq_refl (term633 A x' _95734 _95735 _95736)). Qed.
Lemma lem7156871 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) : ((term514 A x' _95734 _95736 _95735) = (term633 A x' _95734 _95735 _95736)) = ((term633 A x' _95734 _95735 _95736) = (term633 A x' _95734 _95735 _95736)).
Proof. exact (MK_COMB (@lem7156860 A x' _95734 _95735 _95736) (@lem7156870 A x' _95734 _95735 _95736)). Qed.
Lemma lem7156873 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7156874 (x : Prop) : (x = x) = True.
Proof. exact (@lem7156873 Prop x). Qed.
Lemma lem7156875 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) : ((term633 A x' _95734 _95735 _95736) = (term633 A x' _95734 _95735 _95736)) = True.
Proof. exact (@lem7156874 (term633 A x' _95734 _95735 _95736)). Qed.
Lemma lem7156876 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) : ((term514 A x' _95734 _95736 _95735) = (term633 A x' _95734 _95735 _95736)) = True.
Proof. exact (TRANS (@lem7156871 A x' _95734 _95735 _95736) (@lem7156875 A x' _95734 _95735 _95736)). Qed.
Lemma lem7156877 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) : True = ((term514 A x' _95734 _95736 _95735) = (term633 A x' _95734 _95735 _95736)).
Proof. exact (SYM (@lem7156876 A x' _95734 _95735 _95736)). Qed.
Lemma lem7156878 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) : (term514 A x' _95734 _95736 _95735) = (term633 A x' _95734 _95735 _95736).
Proof. exact (EQ_MP (@lem7156877 A x' _95734 _95735 _95736) (@lem0)). Qed.
Lemma lem7156879 {A : Type'} (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) (x' : type711 A) (h1 : term226 A x') : term633 A x' _95734 _95735 _95736.
Proof. exact (EQ_MP (@lem7156878 A x' _95734 _95735 _95736) (@lem7155596 A _95734 _95736 _95735 x' h1)). Qed.
Lemma lem7156881 (b : Prop) (a : Prop) : (a \/ b) = (term532 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7156882 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95736 : A -> Prop) (_95735 : A -> real) : (term633 A x' _95734 _95735 _95736) = (term636 A x' _95734 _95736 _95735).
Proof. exact (@lem7156881 (term424 A x' _95734 _95735 _95736) ((term358 A _95736 _95734) = (term358 A _95736 _95735))). Qed.
Lemma lem7156884 (a : Prop) : (term538 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7156885 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) : (term637 A x' _95734 _95735 _95736) = ((term417 A x' _95734 _95735 _95736) = (term420 A x' _95734 _95735 _95736)).
Proof. exact (@lem7156884 ((term417 A x' _95734 _95735 _95736) = (term420 A x' _95734 _95735 _95736))). Qed.
Lemma lem7156886 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7156887 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95735 : A -> real) (_95736 : A -> Prop) : (term638 A x' _95734 _95735 _95736) = (term639 A x' _95734 _95735 _95736).
Proof. exact (MK_COMB (@lem7156886) (@lem7156885 A x' _95734 _95735 _95736)). Qed.
Lemma lem7156888 {A : Type'} (_95734 : A -> real) (_95736 : A -> Prop) (_95735 : A -> real) : ((term358 A _95736 _95734) = (term358 A _95736 _95735)) = ((term358 A _95736 _95734) = (term358 A _95736 _95735)).
Proof. exact (eq_refl ((term358 A _95736 _95734) = (term358 A _95736 _95735))). Qed.
Lemma lem7156889 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95736 : A -> Prop) (_95735 : A -> real) : (term636 A x' _95734 _95736 _95735) = (term640 A x' _95734 _95736 _95735).
Proof. exact (MK_COMB (@lem7156887 A x' _95734 _95735 _95736) (@lem7156888 A _95734 _95736 _95735)). Qed.
Lemma lem7156890 {A : Type'} (x' : type711 A) (_95734 : A -> real) (_95736 : A -> Prop) (_95735 : A -> real) : (term633 A x' _95734 _95735 _95736) = (term640 A x' _95734 _95736 _95735).
Proof. exact (TRANS (@lem7156882 A x' _95734 _95736 _95735) (@lem7156889 A x' _95734 _95736 _95735)). Qed.
Lemma lem7156893 {A : Type'} (_95734 : A -> real) (_95736 : A -> Prop) (_95735 : A -> real) (x' : type711 A) (h1 : term226 A x') : term640 A x' _95734 _95736 _95735.
Proof. exact (EQ_MP (@lem7156890 A x' _95734 _95736 _95735) (@lem7156879 A _95734 _95735 _95736 x' h1)). Qed.
Lemma lem7156894 {A : Type'} (_95734 : A -> real) (_95736 : A -> Prop) (_95735 : A -> real) (x' : type711 A) (h1 : term226 A x') : term640 A x' _95734 _95736 _95735.
Proof. exact (@lem7156893 A _95734 _95736 _95735 x' h1). Qed.
Lemma lem7156895 {A : Type'} (f : A -> real) (t : A -> Prop) (g : A -> real) (x' : type711 A) (h1 : term226 A x') : term640 A x' f t g.
Proof. exact (@lem7156894 A f t g x' h1). Qed.
Lemma lem7156898 {A : Type'} (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term226 A x') (h2 : term619 A f t g) (h3 : term89 A s f t g) : (term358 A t f) = (term358 A t g).
Proof. exact (@lem7156895 A f t g x' h1 (@lem7156842 A x' s f t g h1 h2 h3)). Qed.
Lemma lem7156899 {A : Type'} (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term226 A x') (h2 : term89 A s f t g) : term641 A f t g.
Proof. exact (fun h0 : term619 A f t g => @lem7156898 A x' s f t g h1 h0 h2). Qed.
Lemma lem7156901 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156902 {A : Type'} (f : A -> real) (t : A -> Prop) (g : A -> real) : (term641 A f t g) = ((term358 A t f) = (term358 A t g)).
Proof. exact (@lem7156901 ((term358 A t f) = (term358 A t g))). Qed.
Lemma lem7156903 {A : Type'} (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term226 A x') (h2 : term89 A s f t g) : (term358 A t f) = (term358 A t g).
Proof. exact (EQ_MP (@lem7156902 A f t g) (@lem7156899 A x' s f t g h1 h2)). Qed.
Lemma lem7156904 {A : Type'} (x : type709 A) (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term226 A x') (h3 : term89 A s f t g) : term642 A s f t g.
Proof. exact (conj (@lem7156759 A x s f t g h1 h3) (@lem7156903 A x' s f t g h2 h3)). Qed.
Lemma lem7156906 (x : real) (y : real) (z : real) : term616 x y z.
Proof. exact (EQ_MP (@lem7156746 x y z) (@lem7156725 y x z)). Qed.
Lemma lem7156907 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : term643 A s f t g.
Proof. exact (@lem7156906 (term358 A t f) (term358 A s f) (term358 A t g)). Qed.
Lemma lem7156910 {A : Type'} (x : type709 A) (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term226 A x') (h3 : term89 A s f t g) : (term358 A s f) = (term358 A t g).
Proof. exact (@lem7156907 A s f t g (@lem7156904 A x x' s f t g h1 h2 h3)). Qed.
Lemma lem7156911 {A : Type'} (x : type709 A) (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term226 A x') (h3 : term89 A s f t g) : term644 A s f t g.
Proof. exact (fun h0 : term449 A s f t g => @lem7156910 A x x' s f t g h1 h2 h3). Qed.
Lemma lem7156913 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156914 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : (term644 A s f t g) = ((term358 A s f) = (term358 A t g)).
Proof. exact (@lem7156913 ((term358 A s f) = (term358 A t g))). Qed.
Lemma lem7156915 {A : Type'} (x : type709 A) (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term226 A x') (h3 : term89 A s f t g) : (term358 A s f) = (term358 A t g).
Proof. exact (EQ_MP (@lem7156914 A s f t g) (@lem7156911 A x x' s f t g h1 h2 h3)). Qed.
Lemma lem7156918 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7156920 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) : (term449 A s f t g) = (term645 A s f t g).
Proof. exact (@lem7156918 ((term358 A s f) = (term358 A t g))). Qed.
Lemma lem7156923 {A : Type'} (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term89 A s f t g) : term645 A s f t g.
Proof. exact (EQ_MP (@lem7156920 A s f t g) (@lem7155550 A s f t g h1)). Qed.
Lemma lem7156926 {A : Type'} (x : type709 A) (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term226 A x') (h3 : term89 A s f t g) : False.
Proof. exact (@lem7156923 A s f t g h3 (@lem7156915 A x x' s f t g h1 h2 h3)). Qed.
Lemma lem7156927 {A : Type'} (x : type709 A) (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term226 A x') (h3 : term89 A s f t g) : term646.
Proof. exact (fun h0 : ~ False => @lem7156926 A x x' s f t g h1 h2 h3). Qed.
Lemma lem7156929 (p : Prop) : (term520 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7156930 : term646 = False.
Proof. exact (@lem7156929 False). Qed.
Lemma lem7156931 {A : Type'} (x : type709 A) (x' : type711 A) (s : A -> Prop) (f : A -> real) (t : A -> Prop) (g : A -> real) (h1 : term354 A x) (h2 : term226 A x') (h3 : term89 A s f t g) : False.
Proof. exact (EQ_MP (@lem7156930) (@lem7156927 A x x' s f t g h1 h2 h3)). Qed.
Lemma lem7156932 {A : Type'} (x : type709 A) (x' : type711 A) (s : A -> Prop) (f : A -> real) (g : A -> real) (h1 : term354 A x) (h2 : term226 A x') (h3 : term99 A s f g) : False.
Proof. exact (ex_elim (@lem7154600 A s f g h3) (fun t : A -> Prop => fun h0 : term98 A s f g t => @lem7156931 A x x' s f t g h1 h2 h0)). Qed.
Lemma lem7156933 {A : Type'} (x : type709 A) (x' : type711 A) (f : A -> real) (g : A -> real) (h1 : term354 A x) (h2 : term226 A x') (h3 : term106 A f g) : False.
Proof. exact (ex_elim (@lem7154599 A f g h3) (fun s : A -> Prop => fun h0 : term105 A f g s => @lem7156932 A x x' s f g h1 h2 h0)). Qed.
Lemma lem7156934 {A : Type'} (x : type709 A) (x' : type711 A) (g : A -> real) (h1 : term354 A x) (h2 : term226 A x') (h3 : term10 A g) : False.
Proof. exact (ex_elim (@lem7153762 A g h3) (fun f : A -> real => fun h0 : term113 A g f => @lem7156933 A x x' f g h1 h2 h0)). Qed.
Lemma lem7156935 {_132349 A : Type'} (x : type709 A) (x' : type711 A) (g : A -> real) (h1 : term12 _132349) (h2 : term354 A x) (h3 : term226 A x') (h4 : term10 A g) : False.
Proof. exact (ex_elim (@lem7154028 _132349 h1) (fun x'' : type711 _132349 => fun h0 : term228 _132349 x'' => @lem7156934 A x x' g h2 h3 h4)). Qed.
Lemma lem7156936 {_132349 A : Type'} (x : type709 A) (g : A -> real) (h1 : term12 _132349) (h2 : term354 A x) (h3 : term12 A) (h4 : term10 A g) : False.
Proof. exact (ex_elim (@lem7154294 A h3) (fun x' : type711 A => fun h0 : term228 A x' => @lem7156935 _132349 A x x' g h1 h2 h0 h4)). Qed.
Lemma lem7156937 {_132349 A : Type'} (g : A -> real) (h1 : term12 _132349) (h2 : term11 A) (h3 : term12 A) (h4 : term10 A g) : False.
Proof. exact (ex_elim (@lem7154595 A h2) (fun x : type709 A => fun h0 : term356 A x => @lem7156936 _132349 A x g h1 h0 h3 h4)). Qed.
Lemma lem7156938 {_132349 A : Type'} (g : A -> real) (h1 : term12 _132349) (h2 : term12 A) (h3 : term10 A g) : term17 A.
Proof. exact (fun h0 : term11 A => @lem7156937 _132349 A g h1 h0 h2 h3). Qed.
Lemma lem7156939 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem69 (term11 A)). Qed.
Lemma lem7156940 {_132349 A : Type'} (g : A -> real) (h1 : term12 _132349) (h2 : term12 A) (h3 : term10 A g) : term18 A.
Proof. exact (EQ_MP (@lem7156939 A) (@lem7156938 _132349 A g h1 h2 h3)). Qed.
Lemma lem7156941 {_132349 A : Type'} (g : A -> real) (h1 : term12 _132349) (h2 : term10 A g) : term21 A.
Proof. exact (fun h0 : term12 A => @lem7156940 _132349 A g h1 h0 h2). Qed.
Lemma lem7156942 {_132349 A : Type'} (g : A -> real) (h1 : term10 A g) : term23 _132349 A.
Proof. exact (fun h0 : term12 _132349 => @lem7156941 _132349 A g h0 h1). Qed.
Lemma lem7156943 {_132349 A : Type'} (g : A -> real) : term25 _132349 A g.
Proof. exact (fun h0 : term10 A g => @lem7156942 _132349 A g h0). Qed.
Lemma lem7156948 {_132349 A : Type'} : term29 _132349 A.
Proof. exact (fun g : A -> real => @lem7156943 _132349 A g). Qed.
Lemma lem7156949 {_132349 A : Type'} : term28 _132349 A.
Proof. exact (EQ_MP (@lem7153526 _132349 A) (@lem7156948 _132349 A)). Qed.
Lemma lem7156950 {_132349 A : Type'} (g : A -> real) : term647 _132349 A g.
Proof. exact (@lem7156949 _132349 A g). Qed.
Lemma lem7156951 {_132349 A : Type'} (g : A -> real) : (term647 _132349 A g) = (term13 _132349 A g).
Proof. exact (eq_refl (term647 _132349 A g)). Qed.
Lemma lem7156952 {_132349 A : Type'} (g : A -> real) : term13 _132349 A g.
Proof. exact (EQ_MP (@lem7156951 _132349 A g) (@lem7156950 _132349 A g)). Qed.
Lemma lem7156954 {_132349 A : Type'} (g : A -> real) : term13 _132349 A g.
Proof. exact (@lem7153109 _132349 A g (@lem7156952 _132349 A g)). Qed.
Lemma lem7156955 {_132349 A : Type'} (g : A -> real) (h1 : term10 A g) : term22 _132349 A.
Proof. exact (@lem7156954 _132349 A g (@lem7153088 A g h1)). Qed.
Lemma lem7156956 {A : Type'} (g : A -> real) (h1 : term10 A g) : term20 A.
Proof. exact (@lem7156955 Prop A g h1 (@lem7081239 Prop)). Qed.
Lemma lem7156957 {A : Type'} (g : A -> real) (h1 : term10 A g) : term17 A.
Proof. exact (@lem7156956 A g h1 (@lem7153092 A)). Qed.
Lemma lem7156958 {A : Type'} (g : A -> real) (h1 : term10 A g) : False.
Proof. exact (@lem7156957 A g h1 (@lem7153089 A)). Qed.
Lemma lem7156959 {A : Type'} (g : A -> real) (h1 : term10 A g) : (term10 A g) = False.
Proof. exact (prop_ext (fun h2 : term10 A g => @lem7156958 A g h1) (fun h2 : False => @lem7153088 A g h1)). Qed.
Lemma lem7156960 {A : Type'} (g : A -> real) (h1 : term10 A g) : False.
Proof. exact (EQ_MP (@lem7156959 A g h1) (@lem7153088 A g h1)). Qed.
Lemma lem7156961 {A : Type'} (g : A -> real) : term9 A g.
Proof. exact (fun h0 : term10 A g => @lem7156960 A g h0). Qed.
Lemma lem7156962 {A : Type'} (g : A -> real) : term8 A g.
Proof. exact (EQ_MP (@lem7153087 A g) (@lem7156961 A g)). Qed.
