Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_PRODUCT_MAP_term_abbrevs.
Require Import CARTESIAN_PRODUCT_AS_RESTRICTIONS_spec.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import IMAGE_o_spec.
Require Import IN_IMAGE_spec.
Require Import RESTRICTION_spec.
Require Import RESTRICTION_EXTENSION_spec.
Require Import SIMPLE_IMAGE_GEN_spec.
Require Import o_DEF_spec.
Require Import product_map_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1843_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Lemma lem4457283 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4457284 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem4457283 _83095 p). Qed.
Lemma lem4457285 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem4457286 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem4457285 _83095 p) (@lem4457284 _83095 p)). Qed.
Lemma lem4457287 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem4457286 _83095 p x). Qed.
Lemma lem4457288 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem4457297 {A B : Type'} (s : A -> Prop) : term5 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4457298 {A B : Type'} (s : A -> Prop) : (term5 A B s) = (term6 A B s).
Proof. exact (eq_refl (term5 A B s)). Qed.
Lemma lem4457299 {A B : Type'} (s : A -> Prop) : term6 A B s.
Proof. exact (EQ_MP (@lem4457298 A B s) (@lem4457297 A B s)). Qed.
Lemma lem4457300 {A B : Type'} (s : A -> Prop) (f : A -> B) : term7 A B s f.
Proof. exact (@lem4457299 A B s f). Qed.
Lemma lem4457301 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term7 A B s f) = (term8 A B s f).
Proof. exact (eq_refl (term7 A B s f)). Qed.
Lemma lem4457302 {A B : Type'} (s : A -> Prop) (f : A -> B) : term8 A B s f.
Proof. exact (EQ_MP (@lem4457301 A B s f) (@lem4457300 A B s f)). Qed.
Lemma lem4457303 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term9 A B s f x.
Proof. exact (@lem4457302 A B s f x). Qed.
Lemma lem4457304 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term9 A B s f x) = ((@RESTRICTION A B s f x) = (term10 A B s f x)).
Proof. exact (eq_refl (term9 A B s f x)). Qed.
Lemma lem4457306 {A B : Type'} (y : B) : term11 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4457307 {A B : Type'} (y : B) : (term11 A B y) = (term12 A B y).
Proof. exact (eq_refl (term11 A B y)). Qed.
Lemma lem4457308 {A B : Type'} (y : B) : term12 A B y.
Proof. exact (EQ_MP (@lem4457307 A B y) (@lem4457306 A B y)). Qed.
Lemma lem4457309 {A B : Type'} (y : B) (s : A -> Prop) : term13 A B y s.
Proof. exact (@lem4457308 A B y s). Qed.
Lemma lem4457310 {A B : Type'} (y : B) (s : A -> Prop) : (term13 A B y s) = (term14 A B y s).
Proof. exact (eq_refl (term13 A B y s)). Qed.
Lemma lem4457311 {A B : Type'} (y : B) (s : A -> Prop) : term14 A B y s.
Proof. exact (EQ_MP (@lem4457310 A B y s) (@lem4457309 A B y s)). Qed.
Lemma lem4457312 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term15 A B y s f.
Proof. exact (@lem4457311 A B y s f). Qed.
Lemma lem4457313 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y s f) = ((term16 A B y f s) = (term17 A B y f s)).
Proof. exact (eq_refl (term15 A B y s f)). Qed.
Lemma lem4457315 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4457316 {A : Type'} (s : A -> Prop) : (term18 A s) = (term19 A s).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem4457317 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (EQ_MP (@lem4457316 A s) (@lem4457315 A s)). Qed.
Lemma lem4457318 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term20 A s t.
Proof. exact (@lem4457317 A s t). Qed.
Lemma lem4457319 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term20 A s t) = ((s = t) = (term21 A s t)).
Proof. exact (eq_refl (term20 A s t)). Qed.
Lemma lem4457324 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : (term22 _87566 _87571 _87575 f g s) = (term23 _87566 _87571 _87575 f g s)) : (term22 _87566 _87571 _87575 f g s) = (term23 _87566 _87571 _87575 f g s).
Proof. exact (h1). Qed.
Lemma lem4457325 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : (term22 _87566 _87571 _87575 f g s) = (term23 _87566 _87571 _87575 f g s)) : (term23 _87566 _87571 _87575 f g s) = (term22 _87566 _87571 _87575 f g s).
Proof. exact (SYM (@lem4457324 _87566 _87571 _87575 f g s h1)). Qed.
Lemma lem4457326 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : (term23 _87566 _87571 _87575 f g s) = (term22 _87566 _87571 _87575 f g s)) : (term23 _87566 _87571 _87575 f g s) = (term22 _87566 _87571 _87575 f g s).
Proof. exact (h1). Qed.
Lemma lem4457327 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) (h1 : (term23 _87566 _87571 _87575 f g s) = (term22 _87566 _87571 _87575 f g s)) : (term22 _87566 _87571 _87575 f g s) = (term23 _87566 _87571 _87575 f g s).
Proof. exact (SYM (@lem4457326 _87566 _87571 _87575 f g s h1)). Qed.
Lemma lem4457328 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : ((term22 _87566 _87571 _87575 f g s) = (term23 _87566 _87571 _87575 f g s)) = ((term23 _87566 _87571 _87575 f g s) = (term22 _87566 _87571 _87575 f g s)).
Proof. exact (prop_ext (fun h1 : (term22 _87566 _87571 _87575 f g s) = (term23 _87566 _87571 _87575 f g s) => @lem4457325 _87566 _87571 _87575 f g s h1) (fun h1 : (term23 _87566 _87571 _87575 f g s) = (term22 _87566 _87571 _87575 f g s) => @lem4457327 _87566 _87571 _87575 f g s h1)). Qed.
Lemma lem4457329 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) : (term24 _87566 _87571 _87575 f g) = (term25 _87566 _87571 _87575 f g).
Proof. exact (fun_ext (fun s : _87566 -> Prop => @lem4457328 _87566 _87571 _87575 f g s)). Qed.
Lemma lem4457330 {_87566 : Type'} : (@all (_87566 -> Prop)) = (@all (_87566 -> Prop)).
Proof. exact (eq_refl (@all (_87566 -> Prop))). Qed.
Lemma lem4457331 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) : (term26 _87566 _87571 _87575 f g) = (term27 _87566 _87571 _87575 f g).
Proof. exact (MK_COMB (@lem4457330 _87566) (@lem4457329 _87566 _87571 _87575 f g)). Qed.
Lemma lem4457332 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) : (term28 _87566 _87571 _87575 f) = (term29 _87566 _87571 _87575 f).
Proof. exact (fun_ext (fun g : _87566 -> _87575 => @lem4457331 _87566 _87571 _87575 f g)). Qed.
Lemma lem4457333 {_87566 _87575 : Type'} : (@all (_87566 -> _87575)) = (@all (_87566 -> _87575)).
Proof. exact (eq_refl (@all (_87566 -> _87575))). Qed.
Lemma lem4457334 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) : (term30 _87566 _87571 _87575 f) = (term31 _87566 _87571 _87575 f).
Proof. exact (MK_COMB (@lem4457333 _87566 _87575) (@lem4457332 _87566 _87571 _87575 f)). Qed.
Lemma lem4457335 {_87566 _87571 _87575 : Type'} : (term32 _87566 _87571 _87575) = (term33 _87566 _87571 _87575).
Proof. exact (fun_ext (fun f : _87575 -> _87571 => @lem4457334 _87566 _87571 _87575 f)). Qed.
Lemma lem4457336 {_87571 _87575 : Type'} : (@all (_87575 -> _87571)) = (@all (_87575 -> _87571)).
Proof. exact (eq_refl (@all (_87575 -> _87571))). Qed.
Lemma lem4457337 {_87566 _87571 _87575 : Type'} : (term34 _87566 _87571 _87575) = (term35 _87566 _87571 _87575).
Proof. exact (MK_COMB (@lem4457336 _87571 _87575) (@lem4457335 _87566 _87571 _87575)). Qed.
Lemma lem4457338 {_87566 _87571 _87575 : Type'} : term35 _87566 _87571 _87575.
Proof. exact (EQ_MP (@lem4457337 _87566 _87571 _87575) (@lem3370560 _87566 _87571 _87575)). Qed.
Lemma lem4457339 {A B C : Type'} (f : B -> C) : term36 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem4457340 {A B C : Type'} (f : B -> C) : (term36 A B C f) = (term37 A B C f).
Proof. exact (eq_refl (term36 A B C f)). Qed.
Lemma lem4457341 {A B C : Type'} (f : B -> C) : term37 A B C f.
Proof. exact (EQ_MP (@lem4457340 A B C f) (@lem4457339 A B C f)). Qed.
Lemma lem4457342 {A B C : Type'} (f : B -> C) (g : A -> B) : term38 A B C f g.
Proof. exact (@lem4457341 A B C f g). Qed.
Lemma lem4457343 {A B C : Type'} (f : B -> C) (g : A -> B) : (term38 A B C f g) = ((@o A B C f g) = (term39 A B C f g)).
Proof. exact (eq_refl (term38 A B C f g)). Qed.
Lemma lem4457345 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) : term40 _87566 _87571 _87575 f.
Proof. exact (@lem4457338 _87566 _87571 _87575 f). Qed.
Lemma lem4457346 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) : (term40 _87566 _87571 _87575 f) = (term31 _87566 _87571 _87575 f).
Proof. exact (eq_refl (term40 _87566 _87571 _87575 f)). Qed.
Lemma lem4457347 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) : term31 _87566 _87571 _87575 f.
Proof. exact (EQ_MP (@lem4457346 _87566 _87571 _87575 f) (@lem4457345 _87566 _87571 _87575 f)). Qed.
Lemma lem4457348 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) : term41 _87566 _87571 _87575 f g.
Proof. exact (@lem4457347 _87566 _87571 _87575 f g). Qed.
Lemma lem4457349 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) : (term41 _87566 _87571 _87575 f g) = (term27 _87566 _87571 _87575 f g).
Proof. exact (eq_refl (term41 _87566 _87571 _87575 f g)). Qed.
Lemma lem4457350 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) : term27 _87566 _87571 _87575 f g.
Proof. exact (EQ_MP (@lem4457349 _87566 _87571 _87575 f g) (@lem4457348 _87566 _87571 _87575 f g)). Qed.
Lemma lem4457351 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : term42 _87566 _87571 _87575 f g s.
Proof. exact (@lem4457350 _87566 _87571 _87575 f g s). Qed.
Lemma lem4457352 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term42 _87566 _87571 _87575 f g s) = ((term23 _87566 _87571 _87575 f g s) = (term22 _87566 _87571 _87575 f g s)).
Proof. exact (eq_refl (term42 _87566 _87571 _87575 f g s)). Qed.
Lemma lem4457354 {A B K : Type'} (k : K -> Prop) : term43 A B K k.
Proof. exact (@lem4456752 A B K k). Qed.
Lemma lem4457355 {A B K : Type'} (k : K -> Prop) : (term43 A B K k) = (term44 A B K k).
Proof. exact (eq_refl (term43 A B K k)). Qed.
Lemma lem4457356 {A B K : Type'} (k : K -> Prop) : term44 A B K k.
Proof. exact (EQ_MP (@lem4457355 A B K k) (@lem4457354 A B K k)). Qed.
Lemma lem4457357 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : term45 A B K k f.
Proof. exact (@lem4457356 A B K k f). Qed.
Lemma lem4457358 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (term45 A B K k f) = ((@product_map A B K k f) = (term46 A B K k f)).
Proof. exact (eq_refl (term45 A B K k f)). Qed.
Lemma lem4457360 {_88162 _88175 : Type'} (f : _88175 -> _88162) : term47 _88162 _88175 f.
Proof. exact (@lem3395052 _88162 _88175 f). Qed.
Lemma lem4457361 {_88162 _88175 : Type'} (f : _88175 -> _88162) : (term47 _88162 _88175 f) = (term48 _88162 _88175 f).
Proof. exact (eq_refl (term47 _88162 _88175 f)). Qed.
Lemma lem4457362 {_88162 _88175 : Type'} (f : _88175 -> _88162) : term48 _88162 _88175 f.
Proof. exact (EQ_MP (@lem4457361 _88162 _88175 f) (@lem4457360 _88162 _88175 f)). Qed.
Lemma lem4457363 {_88162 _88175 : Type'} (f : _88175 -> _88162) (P : _88175 -> Prop) : term49 _88162 _88175 f P.
Proof. exact (@lem4457362 _88162 _88175 f P). Qed.
Lemma lem4457364 {_88162 _88175 : Type'} (f : _88175 -> _88162) (P : _88175 -> Prop) : (term49 _88162 _88175 f P) = ((term50 _88162 _88175 P f) = (term51 _88162 _88175 f P)).
Proof. exact (eq_refl (term49 _88162 _88175 f P)). Qed.
Lemma lem4457366 {A K : Type'} (k : K -> Prop) : term52 A K k.
Proof. exact (@lem4406347 A K k). Qed.
Lemma lem4457367 {A K : Type'} (k : K -> Prop) : (term52 A K k) = (term53 A K k).
Proof. exact (eq_refl (term52 A K k)). Qed.
Lemma lem4457368 {A K : Type'} (k : K -> Prop) : term53 A K k.
Proof. exact (EQ_MP (@lem4457367 A K k) (@lem4457366 A K k)). Qed.
Lemma lem4457369 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term54 A K k s.
Proof. exact (@lem4457368 A K k s). Qed.
Lemma lem4457370 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term54 A K k s) = ((@cartesian_product A K k s) = (term55 A K s k)).
Proof. exact (eq_refl (term54 A K k s)). Qed.
Lemma lem4457375 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (@cartesian_product A K k s) = (term55 A K s k).
Proof. exact (EQ_MP (@lem4457370 A K s k) (@lem4457369 A K k s)). Qed.
Lemma lem4457376 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (@cartesian_product A K k s) = (term55 A K s k).
Proof. exact (@lem4457375 A K s k). Qed.
Lemma lem4457387 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (term56 A B K k f) = (term56 A B K k f).
Proof. exact (eq_refl (term56 A B K k f)). Qed.
Lemma lem4457388 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term57 A B K f k s) = (term58 A B K f s k).
Proof. exact (MK_COMB (@lem4457387 A B K k f) (@lem4457376 A K s k)). Qed.
Lemma lem4457389 {B K : Type'} : (@eq ((K -> B) -> Prop)) = (@eq ((K -> B) -> Prop)).
Proof. exact (eq_refl (@eq ((K -> B) -> Prop))). Qed.
Lemma lem4457390 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term59 A B K f k s) = (term60 A B K f s k).
Proof. exact (MK_COMB (@lem4457389 B K) (@lem4457388 A B K f s k)). Qed.
Lemma lem4457392 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (@cartesian_product A K k s) = (term55 A K s k).
Proof. exact (EQ_MP (@lem4457370 A K s k) (@lem4457369 A K k s)). Qed.
Lemma lem4457393 {B K : Type'} (s : type1470 B K) (k : K -> Prop) : (@cartesian_product B K k s) = (term55 B K s k).
Proof. exact (@lem4457392 B K s k). Qed.
Lemma lem4457394 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term61 A B K k f s) = (term62 A B K f s k).
Proof. exact (@lem4457393 B K (term63 A B K f s) k). Qed.
Lemma lem4457406 {A B : Type'} (f : A -> B) (y : A) : (term64 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4457407 {B K : Type'} (f : type1470 B K) (y : K) : (term65 B K f y) = (f y).
Proof. exact (@lem4457406 K (B -> Prop) f y). Qed.
Lemma lem4457408 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : K) : (term66 A B K f s i) = (term67 A B K f s i).
Proof. exact (@lem4457407 B K (term63 A B K f s) i). Qed.
Lemma lem4457409 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : K) : (term67 A B K f s i) = (term68 A B K f s i).
Proof. exact (eq_refl (term67 A B K f s i)). Qed.
Lemma lem4457410 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) : (term69 A B K f s) = (term63 A B K f s).
Proof. exact (fun_ext (fun i : K => @lem4457409 A B K f s i)). Qed.
Lemma lem4457411 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4457412 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : K) : (term66 A B K f s i) = (term67 A B K f s i).
Proof. exact (MK_COMB (@lem4457410 A B K f s) (@lem4457411 K i)). Qed.
Lemma lem4457413 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem4457414 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : K) : (term70 A B K f s i) = (term71 A B K f s i).
Proof. exact (MK_COMB (@lem4457413 B) (@lem4457412 A B K f s i)). Qed.
Lemma lem4457415 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : K) : (term67 A B K f s i) = (term68 A B K f s i).
Proof. exact (eq_refl (term67 A B K f s i)). Qed.
Lemma lem4457416 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : K) : ((term66 A B K f s i) = (term67 A B K f s i)) = ((term67 A B K f s i) = (term68 A B K f s i)).
Proof. exact (MK_COMB (@lem4457414 A B K f s i) (@lem4457415 A B K f s i)). Qed.
Lemma lem4457417 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : K) : (term67 A B K f s i) = (term68 A B K f s i).
Proof. exact (EQ_MP (@lem4457416 A B K f s i) (@lem4457408 A B K f s i)). Qed.
Lemma lem4457418 {B K : Type'} (f : K -> B) (i : K) : (term72 B K f i) = (term72 B K f i).
Proof. exact (eq_refl (term72 B K f i)). Qed.
Lemma lem4457419 {A B K : Type'} (f : K -> B) (f' : type1514 A B K) (s : type1470 A K) (i : K) : (term73 A B K f f' s i) = (term74 A B K f f' s i).
Proof. exact (MK_COMB (@lem4457418 B K f i) (@lem4457417 A B K f' s i)). Qed.
Lemma lem4457420 {K : Type'} (i : K) (k : K -> Prop) : (term75 K i k) = (term75 K i k).
Proof. exact (eq_refl (term75 K i k)). Qed.
Lemma lem4457421 {A B K : Type'} (k : K -> Prop) (f : K -> B) (f' : type1514 A B K) (s : type1470 A K) (i : K) : (term76 A B K k f f' s i) = (term77 A B K k f f' s i).
Proof. exact (MK_COMB (@lem4457420 K i k) (@lem4457419 A B K f f' s i)). Qed.
Lemma lem4457424 {A B K : Type'} (k : K -> Prop) (f : K -> B) (f' : type1514 A B K) (s : type1470 A K) : (term78 A B K k f f' s) = (term79 A B K k f f' s).
Proof. exact (fun_ext (fun i : K => @lem4457421 A B K k f f' s i)). Qed.
Lemma lem4457425 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4457426 {A B K : Type'} (k : K -> Prop) (f : K -> B) (f' : type1514 A B K) (s : type1470 A K) : (term80 A B K k f f' s) = (term81 A B K k f f' s).
Proof. exact (MK_COMB (@lem4457425 K) (@lem4457424 A B K k f f' s)). Qed.
Lemma lem4457431 {B K : Type'} (GEN_PVAR_142 : K -> B) : (@SETSPEC (K -> B) GEN_PVAR_142) = (@SETSPEC (K -> B) GEN_PVAR_142).
Proof. exact (eq_refl (@SETSPEC (K -> B) GEN_PVAR_142)). Qed.
Lemma lem4457432 {A B K : Type'} (GEN_PVAR_142 : K -> B) (k : K -> Prop) (f : K -> B) (f' : type1514 A B K) (s : type1470 A K) : (term82 A B K GEN_PVAR_142 k f f' s) = (term83 A B K GEN_PVAR_142 k f f' s).
Proof. exact (MK_COMB (@lem4457431 B K GEN_PVAR_142) (@lem4457426 A B K k f f' s)). Qed.
Lemma lem4457433 {B K : Type'} (k : K -> Prop) (f : K -> B) : (@RESTRICTION K B k f) = (@RESTRICTION K B k f).
Proof. exact (eq_refl (@RESTRICTION K B k f)). Qed.
Lemma lem4457434 {A B K : Type'} (GEN_PVAR_142 : K -> B) (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) (f' : K -> B) : (term84 A B K GEN_PVAR_142 f s k f') = (term85 A B K GEN_PVAR_142 f s k f').
Proof. exact (MK_COMB (@lem4457432 A B K GEN_PVAR_142 k f' f s) (@lem4457433 B K k f')). Qed.
Lemma lem4457435 {A B K : Type'} (GEN_PVAR_142 : K -> B) (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term86 A B K GEN_PVAR_142 f s k) = (term87 A B K GEN_PVAR_142 f s k).
Proof. exact (fun_ext (fun f' : K -> B => @lem4457434 A B K GEN_PVAR_142 f s k f')). Qed.
Lemma lem4457436 {B K : Type'} : (@ex (K -> B)) = (@ex (K -> B)).
Proof. exact (eq_refl (@ex (K -> B))). Qed.
Lemma lem4457437 {A B K : Type'} (GEN_PVAR_142 : K -> B) (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term88 A B K GEN_PVAR_142 f s k) = (term89 A B K GEN_PVAR_142 f s k).
Proof. exact (MK_COMB (@lem4457436 B K) (@lem4457435 A B K GEN_PVAR_142 f s k)). Qed.
Lemma lem4457442 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term90 A B K f s k) = (term91 A B K f s k).
Proof. exact (fun_ext (fun GEN_PVAR_142 : K -> B => @lem4457437 A B K GEN_PVAR_142 f s k)). Qed.
Lemma lem4457443 {B K : Type'} : (@GSPEC (K -> B)) = (@GSPEC (K -> B)).
Proof. exact (eq_refl (@GSPEC (K -> B))). Qed.
Lemma lem4457444 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term62 A B K f s k) = (term92 A B K f s k).
Proof. exact (MK_COMB (@lem4457443 B K) (@lem4457442 A B K f s k)). Qed.
Lemma lem4457445 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term61 A B K k f s) = (term92 A B K f s k).
Proof. exact (TRANS (@lem4457394 A B K f s k) (@lem4457444 A B K f s k)). Qed.
Lemma lem4457446 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : ((term57 A B K f k s) = (term61 A B K k f s)) = ((term58 A B K f s k) = (term92 A B K f s k)).
Proof. exact (MK_COMB (@lem4457390 A B K f s k) (@lem4457445 A B K f s k)). Qed.
Lemma lem4457449 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : ((term58 A B K f s k) = (term92 A B K f s k)) = ((term57 A B K f k s) = (term61 A B K k f s)).
Proof. exact (SYM (@lem4457446 A B K f s k)). Qed.
Lemma lem4457453 {_88162 _88175 : Type'} (f : _88175 -> _88162) (P : _88175 -> Prop) : (term50 _88162 _88175 P f) = (term51 _88162 _88175 f P).
Proof. exact (EQ_MP (@lem4457364 _88162 _88175 f P) (@lem4457363 _88162 _88175 f P)). Qed.
Lemma lem4457454 {A K : Type'} (f : type796 A K) (P : type805 A K) : (term93 A K P f) = (term94 A K f P).
Proof. exact (@lem4457453 (K -> A) (K -> A) f P). Qed.
Lemma lem4457455 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term95 A K s k) = (term96 A K k s).
Proof. exact (@lem4457454 A K (term97 A K k) (term98 A K k s)). Qed.
Lemma lem4457456 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term99 A K k s f) = (term100 A K k f s).
Proof. exact (eq_refl (term99 A K k s f)). Qed.
Lemma lem4457457 {A K : Type'} (GEN_PVAR_142 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_142) = (@SETSPEC (K -> A) GEN_PVAR_142).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_142)). Qed.
Lemma lem4457458 {A K : Type'} (GEN_PVAR_142 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term101 A K GEN_PVAR_142 k s f) = (term102 A K GEN_PVAR_142 k f s).
Proof. exact (MK_COMB (@lem4457457 A K GEN_PVAR_142) (@lem4457456 A K k f s)). Qed.
Lemma lem4457459 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term103 A K k f) = (@RESTRICTION K A k f).
Proof. exact (eq_refl (term103 A K k f)). Qed.
Lemma lem4457460 {A K : Type'} (GEN_PVAR_142 : K -> A) (s : type1470 A K) (k : K -> Prop) (f : K -> A) : (term104 A K GEN_PVAR_142 s k f) = (term105 A K GEN_PVAR_142 s k f).
Proof. exact (MK_COMB (@lem4457458 A K GEN_PVAR_142 k f s) (@lem4457459 A K k f)). Qed.
Lemma lem4457461 {A K : Type'} (GEN_PVAR_142 : K -> A) (s : type1470 A K) (k : K -> Prop) : (term106 A K GEN_PVAR_142 s k) = (term107 A K GEN_PVAR_142 s k).
Proof. exact (fun_ext (fun f : K -> A => @lem4457460 A K GEN_PVAR_142 s k f)). Qed.
Lemma lem4457462 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4457463 {A K : Type'} (GEN_PVAR_142 : K -> A) (s : type1470 A K) (k : K -> Prop) : (term108 A K GEN_PVAR_142 s k) = (term109 A K GEN_PVAR_142 s k).
Proof. exact (MK_COMB (@lem4457462 A K) (@lem4457461 A K GEN_PVAR_142 s k)). Qed.
Lemma lem4457464 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term110 A K s k) = (term111 A K s k).
Proof. exact (fun_ext (fun GEN_PVAR_142 : K -> A => @lem4457463 A K GEN_PVAR_142 s k)). Qed.
Lemma lem4457465 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4457466 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term95 A K s k) = (term55 A K s k).
Proof. exact (MK_COMB (@lem4457465 A K) (@lem4457464 A K s k)). Qed.
Lemma lem4457467 {A K : Type'} : (@eq ((K -> A) -> Prop)) = (@eq ((K -> A) -> Prop)).
Proof. exact (eq_refl (@eq ((K -> A) -> Prop))). Qed.
Lemma lem4457468 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term112 A K s k) = (term113 A K s k).
Proof. exact (MK_COMB (@lem4457467 A K) (@lem4457466 A K s k)). Qed.
Lemma lem4457469 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term99 A K k s f) = (term100 A K k f s).
Proof. exact (eq_refl (term99 A K k s f)). Qed.
Lemma lem4457470 {A K : Type'} (GEN_PVAR_25 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_25) = (@SETSPEC (K -> A) GEN_PVAR_25).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_25)). Qed.
Lemma lem4457471 {A K : Type'} (GEN_PVAR_25 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term101 A K GEN_PVAR_25 k s f) = (term102 A K GEN_PVAR_25 k f s).
Proof. exact (MK_COMB (@lem4457470 A K GEN_PVAR_25) (@lem4457469 A K k f s)). Qed.
Lemma lem4457472 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4457473 {A K : Type'} (GEN_PVAR_25 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term114 A K GEN_PVAR_25 k s f) = (term115 A K GEN_PVAR_25 k s f).
Proof. exact (MK_COMB (@lem4457471 A K GEN_PVAR_25 k f s) (@lem4457472 A K f)). Qed.
Lemma lem4457474 {A K : Type'} (GEN_PVAR_25 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term116 A K GEN_PVAR_25 k s) = (term117 A K GEN_PVAR_25 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4457473 A K GEN_PVAR_25 k s f)). Qed.
Lemma lem4457475 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4457476 {A K : Type'} (GEN_PVAR_25 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term118 A K GEN_PVAR_25 k s) = (term119 A K GEN_PVAR_25 k s).
Proof. exact (MK_COMB (@lem4457475 A K) (@lem4457474 A K GEN_PVAR_25 k s)). Qed.
Lemma lem4457477 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term120 A K k s) = (term121 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_25 : K -> A => @lem4457476 A K GEN_PVAR_25 k s)). Qed.
Lemma lem4457478 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4457479 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term122 A K k s) = (term123 A K k s).
Proof. exact (MK_COMB (@lem4457478 A K) (@lem4457477 A K k s)). Qed.
Lemma lem4457480 {A K : Type'} (k : K -> Prop) : (term124 A K k) = (term124 A K k).
Proof. exact (eq_refl (term124 A K k)). Qed.
Lemma lem4457481 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term96 A K k s) = (term125 A K k s).
Proof. exact (MK_COMB (@lem4457480 A K k) (@lem4457479 A K k s)). Qed.
Lemma lem4457482 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term95 A K s k) = (term96 A K k s)) = ((term55 A K s k) = (term125 A K k s)).
Proof. exact (MK_COMB (@lem4457468 A K s k) (@lem4457481 A K k s)). Qed.
Lemma lem4457483 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term55 A K s k) = (term125 A K k s).
Proof. exact (EQ_MP (@lem4457482 A K k s) (@lem4457455 A K k s)). Qed.
Lemma lem4457484 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (term56 A B K k f) = (term56 A B K k f).
Proof. exact (eq_refl (term56 A B K k f)). Qed.
Lemma lem4457485 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term58 A B K f s k) = (term126 A B K f k s).
Proof. exact (MK_COMB (@lem4457484 A B K k f) (@lem4457483 A K k s)). Qed.
Lemma lem4457486 {B K : Type'} : (@eq ((K -> B) -> Prop)) = (@eq ((K -> B) -> Prop)).
Proof. exact (eq_refl (@eq ((K -> B) -> Prop))). Qed.
Lemma lem4457487 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term60 A B K f s k) = (term127 A B K f k s).
Proof. exact (MK_COMB (@lem4457486 B K) (@lem4457485 A B K f k s)). Qed.
Lemma lem4457489 {_88162 _88175 : Type'} (f : _88175 -> _88162) (P : _88175 -> Prop) : (term50 _88162 _88175 P f) = (term51 _88162 _88175 f P).
Proof. exact (EQ_MP (@lem4457364 _88162 _88175 f P) (@lem4457363 _88162 _88175 f P)). Qed.
Lemma lem4457490 {B K : Type'} (f : type796 B K) (P : type805 B K) : (term93 B K P f) = (term94 B K f P).
Proof. exact (@lem4457489 (K -> B) (K -> B) f P). Qed.
Lemma lem4457491 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term128 A B K f s k) = (term129 A B K k f s).
Proof. exact (@lem4457490 B K (term97 B K k) (term130 A B K k f s)). Qed.
Lemma lem4457492 {A B K : Type'} (k : K -> Prop) (f : K -> B) (f' : type1514 A B K) (s : type1470 A K) : (term131 A B K k f' s f) = (term81 A B K k f f' s).
Proof. exact (eq_refl (term131 A B K k f' s f)). Qed.
Lemma lem4457493 {B K : Type'} (GEN_PVAR_142 : K -> B) : (@SETSPEC (K -> B) GEN_PVAR_142) = (@SETSPEC (K -> B) GEN_PVAR_142).
Proof. exact (eq_refl (@SETSPEC (K -> B) GEN_PVAR_142)). Qed.
Lemma lem4457494 {A B K : Type'} (GEN_PVAR_142 : K -> B) (k : K -> Prop) (f : K -> B) (f' : type1514 A B K) (s : type1470 A K) : (term132 A B K GEN_PVAR_142 k f' s f) = (term83 A B K GEN_PVAR_142 k f f' s).
Proof. exact (MK_COMB (@lem4457493 B K GEN_PVAR_142) (@lem4457492 A B K k f f' s)). Qed.
Lemma lem4457495 {B K : Type'} (k : K -> Prop) (f : K -> B) : (term103 B K k f) = (@RESTRICTION K B k f).
Proof. exact (eq_refl (term103 B K k f)). Qed.
Lemma lem4457496 {A B K : Type'} (GEN_PVAR_142 : K -> B) (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) (f' : K -> B) : (term133 A B K GEN_PVAR_142 f s k f') = (term85 A B K GEN_PVAR_142 f s k f').
Proof. exact (MK_COMB (@lem4457494 A B K GEN_PVAR_142 k f' f s) (@lem4457495 B K k f')). Qed.
Lemma lem4457497 {A B K : Type'} (GEN_PVAR_142 : K -> B) (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term134 A B K GEN_PVAR_142 f s k) = (term87 A B K GEN_PVAR_142 f s k).
Proof. exact (fun_ext (fun f' : K -> B => @lem4457496 A B K GEN_PVAR_142 f s k f')). Qed.
Lemma lem4457498 {B K : Type'} : (@ex (K -> B)) = (@ex (K -> B)).
Proof. exact (eq_refl (@ex (K -> B))). Qed.
Lemma lem4457499 {A B K : Type'} (GEN_PVAR_142 : K -> B) (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term135 A B K GEN_PVAR_142 f s k) = (term89 A B K GEN_PVAR_142 f s k).
Proof. exact (MK_COMB (@lem4457498 B K) (@lem4457497 A B K GEN_PVAR_142 f s k)). Qed.
Lemma lem4457500 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term136 A B K f s k) = (term91 A B K f s k).
Proof. exact (fun_ext (fun GEN_PVAR_142 : K -> B => @lem4457499 A B K GEN_PVAR_142 f s k)). Qed.
Lemma lem4457501 {B K : Type'} : (@GSPEC (K -> B)) = (@GSPEC (K -> B)).
Proof. exact (eq_refl (@GSPEC (K -> B))). Qed.
Lemma lem4457502 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term128 A B K f s k) = (term92 A B K f s k).
Proof. exact (MK_COMB (@lem4457501 B K) (@lem4457500 A B K f s k)). Qed.
Lemma lem4457503 {B K : Type'} : (@eq ((K -> B) -> Prop)) = (@eq ((K -> B) -> Prop)).
Proof. exact (eq_refl (@eq ((K -> B) -> Prop))). Qed.
Lemma lem4457504 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term137 A B K f s k) = (term138 A B K f s k).
Proof. exact (MK_COMB (@lem4457503 B K) (@lem4457502 A B K f s k)). Qed.
Lemma lem4457505 {A B K : Type'} (k : K -> Prop) (f : K -> B) (f' : type1514 A B K) (s : type1470 A K) : (term131 A B K k f' s f) = (term81 A B K k f f' s).
Proof. exact (eq_refl (term131 A B K k f' s f)). Qed.
Lemma lem4457506 {B K : Type'} (GEN_PVAR_25 : K -> B) : (@SETSPEC (K -> B) GEN_PVAR_25) = (@SETSPEC (K -> B) GEN_PVAR_25).
Proof. exact (eq_refl (@SETSPEC (K -> B) GEN_PVAR_25)). Qed.
Lemma lem4457507 {A B K : Type'} (GEN_PVAR_25 : K -> B) (k : K -> Prop) (f : K -> B) (f' : type1514 A B K) (s : type1470 A K) : (term132 A B K GEN_PVAR_25 k f' s f) = (term83 A B K GEN_PVAR_25 k f f' s).
Proof. exact (MK_COMB (@lem4457506 B K GEN_PVAR_25) (@lem4457505 A B K k f f' s)). Qed.
Lemma lem4457508 {B K : Type'} (f : K -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4457509 {A B K : Type'} (GEN_PVAR_25 : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (f' : K -> B) : (term139 A B K GEN_PVAR_25 k f s f') = (term140 A B K GEN_PVAR_25 k f s f').
Proof. exact (MK_COMB (@lem4457507 A B K GEN_PVAR_25 k f' f s) (@lem4457508 B K f')). Qed.
Lemma lem4457510 {A B K : Type'} (GEN_PVAR_25 : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term141 A B K GEN_PVAR_25 k f s) = (term142 A B K GEN_PVAR_25 k f s).
Proof. exact (fun_ext (fun f' : K -> B => @lem4457509 A B K GEN_PVAR_25 k f s f')). Qed.
Lemma lem4457511 {B K : Type'} : (@ex (K -> B)) = (@ex (K -> B)).
Proof. exact (eq_refl (@ex (K -> B))). Qed.
Lemma lem4457512 {A B K : Type'} (GEN_PVAR_25 : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term143 A B K GEN_PVAR_25 k f s) = (term144 A B K GEN_PVAR_25 k f s).
Proof. exact (MK_COMB (@lem4457511 B K) (@lem4457510 A B K GEN_PVAR_25 k f s)). Qed.
Lemma lem4457513 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term145 A B K k f s) = (term146 A B K k f s).
Proof. exact (fun_ext (fun GEN_PVAR_25 : K -> B => @lem4457512 A B K GEN_PVAR_25 k f s)). Qed.
Lemma lem4457514 {B K : Type'} : (@GSPEC (K -> B)) = (@GSPEC (K -> B)).
Proof. exact (eq_refl (@GSPEC (K -> B))). Qed.
Lemma lem4457515 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term147 A B K k f s) = (term148 A B K k f s).
Proof. exact (MK_COMB (@lem4457514 B K) (@lem4457513 A B K k f s)). Qed.
Lemma lem4457516 {B K : Type'} (k : K -> Prop) : (term124 B K k) = (term124 B K k).
Proof. exact (eq_refl (term124 B K k)). Qed.
Lemma lem4457517 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term129 A B K k f s) = (term149 A B K k f s).
Proof. exact (MK_COMB (@lem4457516 B K k) (@lem4457515 A B K k f s)). Qed.
Lemma lem4457518 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : ((term128 A B K f s k) = (term129 A B K k f s)) = ((term92 A B K f s k) = (term149 A B K k f s)).
Proof. exact (MK_COMB (@lem4457504 A B K f s k) (@lem4457517 A B K k f s)). Qed.
Lemma lem4457519 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term92 A B K f s k) = (term149 A B K k f s).
Proof. exact (EQ_MP (@lem4457518 A B K k f s) (@lem4457491 A B K k f s)). Qed.
Lemma lem4457520 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : ((term58 A B K f s k) = (term92 A B K f s k)) = ((term126 A B K f k s) = (term149 A B K k f s)).
Proof. exact (MK_COMB (@lem4457487 A B K f k s) (@lem4457519 A B K k f s)). Qed.
Lemma lem4457521 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : ((term126 A B K f k s) = (term149 A B K k f s)) = ((term58 A B K f s k) = (term92 A B K f s k)).
Proof. exact (SYM (@lem4457520 A B K k f s)). Qed.
Lemma lem4457525 {_87566 _87571 _87575 : Type'} (f : _87575 -> _87571) (g : _87566 -> _87575) (s : _87566 -> Prop) : (term23 _87566 _87571 _87575 f g s) = (term22 _87566 _87571 _87575 f g s).
Proof. exact (EQ_MP (@lem4457352 _87566 _87571 _87575 f g s) (@lem4457351 _87566 _87571 _87575 f g s)). Qed.
Lemma lem4457526 {A B K : Type'} (f : type887 A B K) (g : type796 A K) (s : type805 A K) : (term150 A B K f g s) = (term151 A B K f g s).
Proof. exact (@lem4457525 (K -> A) (K -> B) (K -> A) f g s). Qed.
Lemma lem4457527 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term126 A B K f k s) = (term152 A B K f k s).
Proof. exact (@lem4457526 A B K (@product_map A B K k f) (term97 A K k) (term123 A K k s)). Qed.
Lemma lem4457529 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term39 A B C f g).
Proof. exact (EQ_MP (@lem4457343 A B C f g) (@lem4457342 A B C f g)). Qed.
Lemma lem4457530 {A B K : Type'} (f : type887 A B K) (g : type796 A K) : (@o (K -> A) (K -> A) (K -> B) f g) = (term153 A B K f g).
Proof. exact (@lem4457529 (K -> A) (K -> A) (K -> B) f g). Qed.
Lemma lem4457531 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) : (term154 A B K f k) = (term155 A B K f k).
Proof. exact (@lem4457530 A B K (@product_map A B K k f) (term97 A K k)). Qed.
Lemma lem4457533 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (@product_map A B K k f) = (term46 A B K k f).
Proof. exact (EQ_MP (@lem4457358 A B K k f) (@lem4457357 A B K k f)). Qed.
Lemma lem4457534 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (@product_map A B K k f) = (term46 A B K k f).
Proof. exact (@lem4457533 A B K k f). Qed.
Lemma lem4457536 {A B : Type'} (f : A -> B) (y : A) : (term64 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4457537 {A K : Type'} (f : type796 A K) (y : K -> A) : (term156 A K f y) = (f y).
Proof. exact (@lem4457536 (K -> A) (K -> A) f y). Qed.
Lemma lem4457538 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term157 A K k x) = (term103 A K k x).
Proof. exact (@lem4457537 A K (term97 A K k) x). Qed.
Lemma lem4457539 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term103 A K k f) = (@RESTRICTION K A k f).
Proof. exact (eq_refl (term103 A K k f)). Qed.
Lemma lem4457540 {A K : Type'} (k : K -> Prop) : (term158 A K k) = (term97 A K k).
Proof. exact (fun_ext (fun f : K -> A => @lem4457539 A K k f)). Qed.
Lemma lem4457541 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4457542 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term157 A K k x) = (term103 A K k x).
Proof. exact (MK_COMB (@lem4457540 A K k) (@lem4457541 A K x)). Qed.
Lemma lem4457543 {A K : Type'} : (@eq (K -> A)) = (@eq (K -> A)).
Proof. exact (eq_refl (@eq (K -> A))). Qed.
Lemma lem4457544 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term159 A K k x) = (term160 A K k x).
Proof. exact (MK_COMB (@lem4457543 A K) (@lem4457542 A K k x)). Qed.
Lemma lem4457545 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term103 A K k x) = (@RESTRICTION K A k x).
Proof. exact (eq_refl (term103 A K k x)). Qed.
Lemma lem4457546 {A K : Type'} (k : K -> Prop) (x : K -> A) : ((term157 A K k x) = (term103 A K k x)) = ((term103 A K k x) = (@RESTRICTION K A k x)).
Proof. exact (MK_COMB (@lem4457544 A K k x) (@lem4457545 A K k x)). Qed.
Lemma lem4457547 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term103 A K k x) = (@RESTRICTION K A k x).
Proof. exact (EQ_MP (@lem4457546 A K k x) (@lem4457538 A K k x)). Qed.
Lemma lem4457548 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term161 A B K f k x) = (term162 A B K f k x).
Proof. exact (MK_COMB (@lem4457534 A B K k f) (@lem4457547 A K k x)). Qed.
Lemma lem4457550 {A B : Type'} (f : A -> B) (y : A) : (term64 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4457551 {A B K : Type'} (f : type887 A B K) (y : K -> A) : (term163 A B K f y) = (f y).
Proof. exact (@lem4457550 (K -> A) (K -> B) f y). Qed.
Lemma lem4457552 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term164 A B K f k x) = (term162 A B K f k x).
Proof. exact (@lem4457551 A B K (term46 A B K k f) (@RESTRICTION K A k x)). Qed.
Lemma lem4457553 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term165 A B K k f x) = (term166 A B K k f x).
Proof. exact (eq_refl (term165 A B K k f x)). Qed.
Lemma lem4457554 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : (term167 A B K k f) = (term46 A B K k f).
Proof. exact (fun_ext (fun x : K -> A => @lem4457553 A B K k f x)). Qed.
Lemma lem4457555 {A K : Type'} (k : K -> Prop) (x : K -> A) : (@RESTRICTION K A k x) = (@RESTRICTION K A k x).
Proof. exact (eq_refl (@RESTRICTION K A k x)). Qed.
Lemma lem4457556 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term164 A B K f k x) = (term162 A B K f k x).
Proof. exact (MK_COMB (@lem4457554 A B K k f) (@lem4457555 A K k x)). Qed.
Lemma lem4457557 {B K : Type'} : (@eq (K -> B)) = (@eq (K -> B)).
Proof. exact (eq_refl (@eq (K -> B))). Qed.
Lemma lem4457558 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term168 A B K f k x) = (term169 A B K f k x).
Proof. exact (MK_COMB (@lem4457557 B K) (@lem4457556 A B K f k x)). Qed.
Lemma lem4457559 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term162 A B K f k x) = (term170 A B K f k x).
Proof. exact (eq_refl (term162 A B K f k x)). Qed.
Lemma lem4457560 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : ((term164 A B K f k x) = (term162 A B K f k x)) = ((term162 A B K f k x) = (term170 A B K f k x)).
Proof. exact (MK_COMB (@lem4457558 A B K f k x) (@lem4457559 A B K f k x)). Qed.
Lemma lem4457561 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term162 A B K f k x) = (term170 A B K f k x).
Proof. exact (EQ_MP (@lem4457560 A B K f k x) (@lem4457552 A B K f k x)). Qed.
Lemma lem4457562 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term161 A B K f k x) = (term170 A B K f k x).
Proof. exact (TRANS (@lem4457548 A B K f k x) (@lem4457561 A B K f k x)). Qed.
Lemma lem4457563 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) : (term155 A B K f k) = (term171 A B K f k).
Proof. exact (fun_ext (fun x : K -> A => @lem4457562 A B K f k x)). Qed.
Lemma lem4457564 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) : (term154 A B K f k) = (term171 A B K f k).
Proof. exact (TRANS (@lem4457531 A B K f k) (@lem4457563 A B K f k)). Qed.
Lemma lem4457565 {A B K : Type'} : (@IMAGE (K -> A) (K -> B)) = (@IMAGE (K -> A) (K -> B)).
Proof. exact (eq_refl (@IMAGE (K -> A) (K -> B))). Qed.
Lemma lem4457566 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) : (term172 A B K f k) = (term173 A B K f k).
Proof. exact (MK_COMB (@lem4457565 A B K) (@lem4457564 A B K f k)). Qed.
Lemma lem4457577 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term123 A K k s) = (term123 A K k s).
Proof. exact (eq_refl (term123 A K k s)). Qed.
Lemma lem4457578 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term152 A B K f k s) = (term174 A B K f k s).
Proof. exact (MK_COMB (@lem4457566 A B K f k) (@lem4457577 A K k s)). Qed.
Lemma lem4457579 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term126 A B K f k s) = (term174 A B K f k s).
Proof. exact (TRANS (@lem4457527 A B K f k s) (@lem4457578 A B K f k s)). Qed.
Lemma lem4457580 {B K : Type'} : (@eq ((K -> B) -> Prop)) = (@eq ((K -> B) -> Prop)).
Proof. exact (eq_refl (@eq ((K -> B) -> Prop))). Qed.
Lemma lem4457581 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term127 A B K f k s) = (term175 A B K f k s).
Proof. exact (MK_COMB (@lem4457580 B K) (@lem4457579 A B K f k s)). Qed.
Lemma lem4457592 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term149 A B K k f s) = (term149 A B K k f s).
Proof. exact (eq_refl (term149 A B K k f s)). Qed.
Lemma lem4457593 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : ((term126 A B K f k s) = (term149 A B K k f s)) = ((term174 A B K f k s) = (term149 A B K k f s)).
Proof. exact (MK_COMB (@lem4457581 A B K f k s) (@lem4457592 A B K k f s)). Qed.
Lemma lem4457596 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : ((term174 A B K f k s) = (term149 A B K k f s)) = ((term126 A B K f k s) = (term149 A B K k f s)).
Proof. exact (SYM (@lem4457593 A B K k f s)). Qed.
Lemma lem4457598 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term21 A s t).
Proof. exact (EQ_MP (@lem4457319 A s t) (@lem4457318 A s t)). Qed.
Lemma lem4457599 {B K : Type'} (s : type805 B K) (t : type805 B K) : (s = t) = (term176 B K s t).
Proof. exact (@lem4457598 (K -> B) s t). Qed.
Lemma lem4457600 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : ((term174 A B K f k s) = (term149 A B K k f s)) = (term177 A B K k f s).
Proof. exact (@lem4457599 B K (term174 A B K f k s) (term149 A B K k f s)). Qed.
Lemma lem4457601 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term177 A B K k f s) = ((term174 A B K f k s) = (term149 A B K k f s)).
Proof. exact (SYM (@lem4457600 A B K k f s)). Qed.
Lemma lem4457605 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term16 A B y f s) = (term17 A B y f s).
Proof. exact (EQ_MP (@lem4457313 A B y f s) (@lem4457312 A B y s f)). Qed.
Lemma lem4457606 {A B K : Type'} (y : K -> B) (f : type887 A B K) (s : type805 A K) : (term178 A B K y f s) = (term179 A B K y f s).
Proof. exact (@lem4457605 (K -> A) (K -> B) y f s). Qed.
Lemma lem4457607 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term180 A B K g f k s) = (term181 A B K g f k s).
Proof. exact (@lem4457606 A B K g (term171 A B K f k) (term123 A K k s)). Qed.
Lemma lem4457617 {A B : Type'} (f : A -> B) (y : A) : (term64 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4457618 {A B K : Type'} (f : type887 A B K) (y : K -> A) : (term163 A B K f y) = (f y).
Proof. exact (@lem4457617 (K -> A) (K -> B) f y). Qed.
Lemma lem4457619 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term182 A B K f k x) = (term183 A B K f k x).
Proof. exact (@lem4457618 A B K (term171 A B K f k) x). Qed.
Lemma lem4457620 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term183 A B K f k x) = (term170 A B K f k x).
Proof. exact (eq_refl (term183 A B K f k x)). Qed.
Lemma lem4457621 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) : (term184 A B K f k) = (term171 A B K f k).
Proof. exact (fun_ext (fun x : K -> A => @lem4457620 A B K f k x)). Qed.
Lemma lem4457622 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4457623 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term182 A B K f k x) = (term183 A B K f k x).
Proof. exact (MK_COMB (@lem4457621 A B K f k) (@lem4457622 A K x)). Qed.
Lemma lem4457624 {B K : Type'} : (@eq (K -> B)) = (@eq (K -> B)).
Proof. exact (eq_refl (@eq (K -> B))). Qed.
Lemma lem4457625 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term185 A B K f k x) = (term186 A B K f k x).
Proof. exact (MK_COMB (@lem4457624 B K) (@lem4457623 A B K f k x)). Qed.
Lemma lem4457626 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term183 A B K f k x) = (term170 A B K f k x).
Proof. exact (eq_refl (term183 A B K f k x)). Qed.
Lemma lem4457627 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : ((term182 A B K f k x) = (term183 A B K f k x)) = ((term183 A B K f k x) = (term170 A B K f k x)).
Proof. exact (MK_COMB (@lem4457625 A B K f k x) (@lem4457626 A B K f k x)). Qed.
Lemma lem4457628 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term183 A B K f k x) = (term170 A B K f k x).
Proof. exact (EQ_MP (@lem4457627 A B K f k x) (@lem4457619 A B K f k x)). Qed.
Lemma lem4457630 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term10 A B s f x).
Proof. exact (EQ_MP (@lem4457304 A B s f x) (@lem4457303 A B s f x)). Qed.
Lemma lem4457631 {A K : Type'} (s : K -> Prop) (f : K -> A) (x : K) : (@RESTRICTION K A s f x) = (term187 A K s f x).
Proof. exact (@lem4457630 K A s f x). Qed.
Lemma lem4457632 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (@RESTRICTION K A k x i) = (term187 A K k x i).
Proof. exact (@lem4457631 A K k x i). Qed.
Lemma lem4457633 {A B K : Type'} (f : type1514 A B K) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4457634 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term188 A B K f k x i) = (term189 A B K f k x i).
Proof. exact (MK_COMB (@lem4457633 A B K f i) (@lem4457632 A K k x i)). Qed.
Lemma lem4457635 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term190 A B K f k x) = (term191 A B K f k x).
Proof. exact (fun_ext (fun i : K => @lem4457634 A B K f k x i)). Qed.
Lemma lem4457636 {B K : Type'} (k : K -> Prop) : (@RESTRICTION K B k) = (@RESTRICTION K B k).
Proof. exact (eq_refl (@RESTRICTION K B k)). Qed.
Lemma lem4457637 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term170 A B K f k x) = (term192 A B K f k x).
Proof. exact (MK_COMB (@lem4457636 B K k) (@lem4457635 A B K f k x)). Qed.
Lemma lem4457638 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term183 A B K f k x) = (term192 A B K f k x).
Proof. exact (TRANS (@lem4457628 A B K f k x) (@lem4457637 A B K f k x)). Qed.
Lemma lem4457639 {B K : Type'} (g : K -> B) : (@eq (K -> B) g) = (@eq (K -> B) g).
Proof. exact (eq_refl (@eq (K -> B) g)). Qed.
Lemma lem4457640 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (g = (term183 A B K f k x)) = (g = (term192 A B K f k x)).
Proof. exact (MK_COMB (@lem4457639 B K g) (@lem4457638 A B K f k x)). Qed.
Lemma lem4457643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4457644 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term193 A B K g f k x) = (term194 A B K g f k x).
Proof. exact (MK_COMB (@lem4457643) (@lem4457640 A B K g f k x)). Qed.
Lemma lem4457646 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4457288 _83095 p x) (@lem4457287 _83095 p x)). Qed.
Lemma lem4457647 {A K : Type'} (p : type805 A K) (x : K -> A) : (term195 A K x p) = (p x).
Proof. exact (@lem4457646 (K -> A) p x). Qed.
Lemma lem4457648 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term196 A K x k s) = (term99 A K k s x).
Proof. exact (@lem4457647 A K (term98 A K k s) x). Qed.
Lemma lem4457649 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term99 A K k s f) = (term100 A K k f s).
Proof. exact (eq_refl (term99 A K k s f)). Qed.
Lemma lem4457650 {A K : Type'} (GEN_PVAR_25 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_25) = (@SETSPEC (K -> A) GEN_PVAR_25).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_25)). Qed.
Lemma lem4457651 {A K : Type'} (GEN_PVAR_25 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term101 A K GEN_PVAR_25 k s f) = (term102 A K GEN_PVAR_25 k f s).
Proof. exact (MK_COMB (@lem4457650 A K GEN_PVAR_25) (@lem4457649 A K k f s)). Qed.
Lemma lem4457652 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4457653 {A K : Type'} (GEN_PVAR_25 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term114 A K GEN_PVAR_25 k s f) = (term115 A K GEN_PVAR_25 k s f).
Proof. exact (MK_COMB (@lem4457651 A K GEN_PVAR_25 k f s) (@lem4457652 A K f)). Qed.
Lemma lem4457654 {A K : Type'} (GEN_PVAR_25 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term116 A K GEN_PVAR_25 k s) = (term117 A K GEN_PVAR_25 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4457653 A K GEN_PVAR_25 k s f)). Qed.
Lemma lem4457655 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4457656 {A K : Type'} (GEN_PVAR_25 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term118 A K GEN_PVAR_25 k s) = (term119 A K GEN_PVAR_25 k s).
Proof. exact (MK_COMB (@lem4457655 A K) (@lem4457654 A K GEN_PVAR_25 k s)). Qed.
Lemma lem4457657 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term120 A K k s) = (term121 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_25 : K -> A => @lem4457656 A K GEN_PVAR_25 k s)). Qed.
Lemma lem4457658 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4457659 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term122 A K k s) = (term123 A K k s).
Proof. exact (MK_COMB (@lem4457658 A K) (@lem4457657 A K k s)). Qed.
Lemma lem4457660 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4457661 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term196 A K x k s) = (term197 A K x k s).
Proof. exact (MK_COMB (@lem4457660 A K x) (@lem4457659 A K k s)). Qed.
Lemma lem4457662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4457663 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term198 A K x k s) = (term199 A K x k s).
Proof. exact (MK_COMB (@lem4457662) (@lem4457661 A K x k s)). Qed.
Lemma lem4457664 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term99 A K k s x) = (term100 A K k x s).
Proof. exact (eq_refl (term99 A K k s x)). Qed.
Lemma lem4457665 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term196 A K x k s) = (term99 A K k s x)) = ((term197 A K x k s) = (term100 A K k x s)).
Proof. exact (MK_COMB (@lem4457663 A K x k s) (@lem4457664 A K k x s)). Qed.
Lemma lem4457666 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term197 A K x k s) = (term100 A K k x s).
Proof. exact (EQ_MP (@lem4457665 A K k x s) (@lem4457648 A K k s x)). Qed.
Lemma lem4457673 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term200 A B K g f x k s) = (term201 A B K g f k x s).
Proof. exact (MK_COMB (@lem4457644 A B K g f k x) (@lem4457666 A K k x s)). Qed.
Lemma lem4457676 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term202 A B K g f k s) = (term203 A B K g f k s).
Proof. exact (fun_ext (fun x : K -> A => @lem4457673 A B K g f k x s)). Qed.
Lemma lem4457677 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4457678 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term181 A B K g f k s) = (term204 A B K g f k s).
Proof. exact (MK_COMB (@lem4457677 A K) (@lem4457676 A B K g f k s)). Qed.
Lemma lem4457683 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term180 A B K g f k s) = (term204 A B K g f k s).
Proof. exact (TRANS (@lem4457607 A B K g f k s) (@lem4457678 A B K g f k s)). Qed.
Lemma lem4457684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4457685 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term205 A B K g f k s) = (term206 A B K g f k s).
Proof. exact (MK_COMB (@lem4457684) (@lem4457683 A B K g f k s)). Qed.
Lemma lem4457687 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term16 A B y f s) = (term17 A B y f s).
Proof. exact (EQ_MP (@lem4457313 A B y f s) (@lem4457312 A B y s f)). Qed.
Lemma lem4457688 {B K : Type'} (y : K -> B) (f : type796 B K) (s : type805 B K) : (term207 B K y f s) = (term208 B K y f s).
Proof. exact (@lem4457687 (K -> B) (K -> B) y f s). Qed.
Lemma lem4457689 {A B K : Type'} (g : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term209 A B K g k f s) = (term210 A B K g k f s).
Proof. exact (@lem4457688 B K g (term97 B K k) (term148 A B K k f s)). Qed.
Lemma lem4457699 {A B : Type'} (f : A -> B) (y : A) : (term64 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4457700 {B K : Type'} (f : type796 B K) (y : K -> B) : (term156 B K f y) = (f y).
Proof. exact (@lem4457699 (K -> B) (K -> B) f y). Qed.
Lemma lem4457701 {B K : Type'} (k : K -> Prop) (x : K -> B) : (term157 B K k x) = (term103 B K k x).
Proof. exact (@lem4457700 B K (term97 B K k) x). Qed.
Lemma lem4457702 {B K : Type'} (k : K -> Prop) (f : K -> B) : (term103 B K k f) = (@RESTRICTION K B k f).
Proof. exact (eq_refl (term103 B K k f)). Qed.
Lemma lem4457703 {B K : Type'} (k : K -> Prop) : (term158 B K k) = (term97 B K k).
Proof. exact (fun_ext (fun f : K -> B => @lem4457702 B K k f)). Qed.
Lemma lem4457704 {B K : Type'} (x : K -> B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4457705 {B K : Type'} (k : K -> Prop) (x : K -> B) : (term157 B K k x) = (term103 B K k x).
Proof. exact (MK_COMB (@lem4457703 B K k) (@lem4457704 B K x)). Qed.
Lemma lem4457706 {B K : Type'} : (@eq (K -> B)) = (@eq (K -> B)).
Proof. exact (eq_refl (@eq (K -> B))). Qed.
Lemma lem4457707 {B K : Type'} (k : K -> Prop) (x : K -> B) : (term159 B K k x) = (term160 B K k x).
Proof. exact (MK_COMB (@lem4457706 B K) (@lem4457705 B K k x)). Qed.
Lemma lem4457708 {B K : Type'} (k : K -> Prop) (x : K -> B) : (term103 B K k x) = (@RESTRICTION K B k x).
Proof. exact (eq_refl (term103 B K k x)). Qed.
Lemma lem4457709 {B K : Type'} (k : K -> Prop) (x : K -> B) : ((term157 B K k x) = (term103 B K k x)) = ((term103 B K k x) = (@RESTRICTION K B k x)).
Proof. exact (MK_COMB (@lem4457707 B K k x) (@lem4457708 B K k x)). Qed.
Lemma lem4457710 {B K : Type'} (k : K -> Prop) (x : K -> B) : (term103 B K k x) = (@RESTRICTION K B k x).
Proof. exact (EQ_MP (@lem4457709 B K k x) (@lem4457701 B K k x)). Qed.
Lemma lem4457711 {B K : Type'} (g : K -> B) : (@eq (K -> B) g) = (@eq (K -> B) g).
Proof. exact (eq_refl (@eq (K -> B) g)). Qed.
Lemma lem4457712 {B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) : (g = (term103 B K k x)) = (g = (@RESTRICTION K B k x)).
Proof. exact (MK_COMB (@lem4457711 B K g) (@lem4457710 B K k x)). Qed.
Lemma lem4457715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4457716 {B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) : (term211 B K g k x) = (term212 B K g k x).
Proof. exact (MK_COMB (@lem4457715) (@lem4457712 B K g k x)). Qed.
Lemma lem4457718 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4457288 _83095 p x) (@lem4457287 _83095 p x)). Qed.
Lemma lem4457719 {B K : Type'} (p : type805 B K) (x : K -> B) : (term195 B K x p) = (p x).
Proof. exact (@lem4457718 (K -> B) p x). Qed.
Lemma lem4457720 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (x : K -> B) : (term213 A B K x k f s) = (term131 A B K k f s x).
Proof. exact (@lem4457719 B K (term130 A B K k f s) x). Qed.
Lemma lem4457721 {A B K : Type'} (k : K -> Prop) (f : K -> B) (f' : type1514 A B K) (s : type1470 A K) : (term131 A B K k f' s f) = (term81 A B K k f f' s).
Proof. exact (eq_refl (term131 A B K k f' s f)). Qed.
Lemma lem4457722 {B K : Type'} (GEN_PVAR_25 : K -> B) : (@SETSPEC (K -> B) GEN_PVAR_25) = (@SETSPEC (K -> B) GEN_PVAR_25).
Proof. exact (eq_refl (@SETSPEC (K -> B) GEN_PVAR_25)). Qed.
Lemma lem4457723 {A B K : Type'} (GEN_PVAR_25 : K -> B) (k : K -> Prop) (f : K -> B) (f' : type1514 A B K) (s : type1470 A K) : (term132 A B K GEN_PVAR_25 k f' s f) = (term83 A B K GEN_PVAR_25 k f f' s).
Proof. exact (MK_COMB (@lem4457722 B K GEN_PVAR_25) (@lem4457721 A B K k f f' s)). Qed.
Lemma lem4457724 {B K : Type'} (f : K -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4457725 {A B K : Type'} (GEN_PVAR_25 : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (f' : K -> B) : (term139 A B K GEN_PVAR_25 k f s f') = (term140 A B K GEN_PVAR_25 k f s f').
Proof. exact (MK_COMB (@lem4457723 A B K GEN_PVAR_25 k f' f s) (@lem4457724 B K f')). Qed.
Lemma lem4457726 {A B K : Type'} (GEN_PVAR_25 : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term141 A B K GEN_PVAR_25 k f s) = (term142 A B K GEN_PVAR_25 k f s).
Proof. exact (fun_ext (fun f' : K -> B => @lem4457725 A B K GEN_PVAR_25 k f s f')). Qed.
Lemma lem4457727 {B K : Type'} : (@ex (K -> B)) = (@ex (K -> B)).
Proof. exact (eq_refl (@ex (K -> B))). Qed.
Lemma lem4457728 {A B K : Type'} (GEN_PVAR_25 : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term143 A B K GEN_PVAR_25 k f s) = (term144 A B K GEN_PVAR_25 k f s).
Proof. exact (MK_COMB (@lem4457727 B K) (@lem4457726 A B K GEN_PVAR_25 k f s)). Qed.
Lemma lem4457729 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term145 A B K k f s) = (term146 A B K k f s).
Proof. exact (fun_ext (fun GEN_PVAR_25 : K -> B => @lem4457728 A B K GEN_PVAR_25 k f s)). Qed.
Lemma lem4457730 {B K : Type'} : (@GSPEC (K -> B)) = (@GSPEC (K -> B)).
Proof. exact (eq_refl (@GSPEC (K -> B))). Qed.
Lemma lem4457731 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term147 A B K k f s) = (term148 A B K k f s).
Proof. exact (MK_COMB (@lem4457730 B K) (@lem4457729 A B K k f s)). Qed.
Lemma lem4457732 {B K : Type'} (x : K -> B) : (@IN (K -> B) x) = (@IN (K -> B) x).
Proof. exact (eq_refl (@IN (K -> B) x)). Qed.
Lemma lem4457733 {A B K : Type'} (x : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term213 A B K x k f s) = (term214 A B K x k f s).
Proof. exact (MK_COMB (@lem4457732 B K x) (@lem4457731 A B K k f s)). Qed.
Lemma lem4457734 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4457735 {A B K : Type'} (x : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term215 A B K x k f s) = (term216 A B K x k f s).
Proof. exact (MK_COMB (@lem4457734) (@lem4457733 A B K x k f s)). Qed.
Lemma lem4457736 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term131 A B K k f s x) = (term81 A B K k x f s).
Proof. exact (eq_refl (term131 A B K k f s x)). Qed.
Lemma lem4457737 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : ((term213 A B K x k f s) = (term131 A B K k f s x)) = ((term214 A B K x k f s) = (term81 A B K k x f s)).
Proof. exact (MK_COMB (@lem4457735 A B K x k f s) (@lem4457736 A B K k x f s)). Qed.
Lemma lem4457738 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term214 A B K x k f s) = (term81 A B K k x f s).
Proof. exact (EQ_MP (@lem4457737 A B K k x f s) (@lem4457720 A B K k f s x)). Qed.
Lemma lem4457746 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term16 A B y f s) = (term17 A B y f s).
Proof. exact (EQ_MP (@lem4457313 A B y f s) (@lem4457312 A B y s f)). Qed.
Lemma lem4457747 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term16 A B y f s) = (term17 A B y f s).
Proof. exact (@lem4457746 A B y f s). Qed.
Lemma lem4457748 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term74 A B K x f s i) = (term217 A B K x f s i).
Proof. exact (@lem4457747 A B (x i) (f i) (s i)). Qed.
Lemma lem4457757 {K : Type'} (i : K) (k : K -> Prop) : (term75 K i k) = (term75 K i k).
Proof. exact (eq_refl (term75 K i k)). Qed.
Lemma lem4457758 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term77 A B K k x f s i) = (term218 A B K k x f s i).
Proof. exact (MK_COMB (@lem4457757 K i k) (@lem4457748 A B K x f s i)). Qed.
Lemma lem4457761 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term79 A B K k x f s) = (term219 A B K k x f s).
Proof. exact (fun_ext (fun i : K => @lem4457758 A B K k x f s i)). Qed.
Lemma lem4457762 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4457763 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term81 A B K k x f s) = (term220 A B K k x f s).
Proof. exact (MK_COMB (@lem4457762 K) (@lem4457761 A B K k x f s)). Qed.
Lemma lem4457768 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term214 A B K x k f s) = (term220 A B K k x f s).
Proof. exact (TRANS (@lem4457738 A B K k x f s) (@lem4457763 A B K k x f s)). Qed.
Lemma lem4457769 {A B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term221 A B K g x k f s) = (term222 A B K g k x f s).
Proof. exact (MK_COMB (@lem4457716 B K g k x) (@lem4457768 A B K k x f s)). Qed.
Lemma lem4457772 {A B K : Type'} (g : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term223 A B K g k f s) = (term224 A B K g k f s).
Proof. exact (fun_ext (fun x : K -> B => @lem4457769 A B K g k x f s)). Qed.
Lemma lem4457773 {B K : Type'} : (@ex (K -> B)) = (@ex (K -> B)).
Proof. exact (eq_refl (@ex (K -> B))). Qed.
Lemma lem4457774 {A B K : Type'} (g : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term210 A B K g k f s) = (term225 A B K g k f s).
Proof. exact (MK_COMB (@lem4457773 B K) (@lem4457772 A B K g k f s)). Qed.
Lemma lem4457779 {A B K : Type'} (g : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term209 A B K g k f s) = (term225 A B K g k f s).
Proof. exact (TRANS (@lem4457689 A B K g k f s) (@lem4457774 A B K g k f s)). Qed.
Lemma lem4457780 {A B K : Type'} (g : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : ((term180 A B K g f k s) = (term209 A B K g k f s)) = ((term204 A B K g f k s) = (term225 A B K g k f s)).
Proof. exact (MK_COMB (@lem4457685 A B K g f k s) (@lem4457779 A B K g k f s)). Qed.
Lemma lem4457783 {A B K : Type'} (g : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : ((term204 A B K g f k s) = (term225 A B K g k f s)) = ((term180 A B K g f k s) = (term209 A B K g k f s)).
Proof. exact (SYM (@lem4457780 A B K g k f s)). Qed.
Lemma lem4457784 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term204 A B K g f k s) : term204 A B K g f k s.
Proof. exact (h1). Qed.
Lemma lem4457785 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term201 A B K g f k x s) : term201 A B K g f k x s.
Proof. exact (h1). Qed.
Lemma lem4457786 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term100 A K k x s) : term100 A K k x s.
Proof. exact (h1). Qed.
Lemma lem4457787 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : g = (term192 A B K f k x)) : g = (term192 A B K f k x).
Proof. exact (h1). Qed.
Lemma lem4457788 {A B K : Type'} (g : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term225 A B K g k f s) : term225 A B K g k f s.
Proof. exact (h1). Qed.
Lemma lem4457789 {A B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (h1 : term222 A B K g k x f s) : term222 A B K g k x f s.
Proof. exact (h1). Qed.
Lemma lem4457790 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (h1 : term220 A B K k x f s) : term220 A B K k x f s.
Proof. exact (h1). Qed.
Lemma lem4457791 {B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : g = (@RESTRICTION K B k x)) : g = (@RESTRICTION K B k x).
Proof. exact (h1). Qed.
Lemma lem4457792 {A B : Type'} (s : A -> Prop) : term226 A B s.
Proof. exact (@lem4388360 A B s). Qed.
Lemma lem4457793 {A B : Type'} (s : A -> Prop) : (term226 A B s) = (term227 A B s).
Proof. exact (eq_refl (term226 A B s)). Qed.
Lemma lem4457794 {A B : Type'} (s : A -> Prop) : term227 A B s.
Proof. exact (EQ_MP (@lem4457793 A B s) (@lem4457792 A B s)). Qed.
Lemma lem4457795 {A B : Type'} (s : A -> Prop) (f : A -> B) : term228 A B s f.
Proof. exact (@lem4457794 A B s f). Qed.
Lemma lem4457796 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term228 A B s f) = (term229 A B s f).
Proof. exact (eq_refl (term228 A B s f)). Qed.
Lemma lem4457797 {A B : Type'} (s : A -> Prop) (f : A -> B) : term229 A B s f.
Proof. exact (EQ_MP (@lem4457796 A B s f) (@lem4457795 A B s f)). Qed.
Lemma lem4457798 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term230 A B s f g.
Proof. exact (@lem4457797 A B s f g). Qed.
Lemma lem4457799 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term230 A B s f g) = (((@RESTRICTION A B s f) = (@RESTRICTION A B s g)) = (term231 A B s f g)).
Proof. exact (eq_refl (term230 A B s f g)). Qed.
Lemma lem4457815 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : g = (term192 A B K f k x)) : g = (term192 A B K f k x).
Proof. exact (h1). Qed.
Lemma lem4457816 {B K : Type'} : (@eq (K -> B)) = (@eq (K -> B)).
Proof. exact (eq_refl (@eq (K -> B))). Qed.
Lemma lem4457817 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : g = (term192 A B K f k x)) : (@eq (K -> B) g) = (term232 A B K f k x).
Proof. exact (MK_COMB (@lem4457816 B K) (@lem4457815 A B K g f k x h1)). Qed.
Lemma lem4457818 {B K : Type'} (k : K -> Prop) (x : K -> B) : (@RESTRICTION K B k x) = (@RESTRICTION K B k x).
Proof. exact (eq_refl (@RESTRICTION K B k x)). Qed.
Lemma lem4457819 {A B K : Type'} (x : K -> B) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) (h1 : g = (term192 A B K f k x')) : (g = (@RESTRICTION K B k x)) = ((term192 A B K f k x') = (@RESTRICTION K B k x)).
Proof. exact (MK_COMB (@lem4457817 A B K g f k x' h1) (@lem4457818 B K k x)). Qed.
Lemma lem4457821 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((@RESTRICTION A B s f) = (@RESTRICTION A B s g)) = (term231 A B s f g).
Proof. exact (EQ_MP (@lem4457799 A B s f g) (@lem4457798 A B s f g)). Qed.
Lemma lem4457822 {B K : Type'} (s : K -> Prop) (f : K -> B) (g : K -> B) : ((@RESTRICTION K B s f) = (@RESTRICTION K B s g)) = (term233 B K s f g).
Proof. exact (@lem4457821 K B s f g). Qed.
Lemma lem4457823 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) : ((term192 A B K f k x) = (@RESTRICTION K B k x')) = (term234 A B K f k x x').
Proof. exact (@lem4457822 B K k (term191 A B K f k x) x'). Qed.
Lemma lem4457833 {A B : Type'} (f : A -> B) (y : A) : (term64 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4457834 {B K : Type'} (f : K -> B) (y : K) : (term235 B K f y) = (f y).
Proof. exact (@lem4457833 K B f y). Qed.
Lemma lem4457835 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term236 A B K f k x x') = (term237 A B K f k x x').
Proof. exact (@lem4457834 B K (term191 A B K f k x) x'). Qed.
Lemma lem4457836 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term237 A B K f k x i) = (term189 A B K f k x i).
Proof. exact (eq_refl (term237 A B K f k x i)). Qed.
Lemma lem4457837 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term238 A B K f k x) = (term191 A B K f k x).
Proof. exact (fun_ext (fun i : K => @lem4457836 A B K f k x i)). Qed.
Lemma lem4457838 {K : Type'} (x : K) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4457839 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term236 A B K f k x x') = (term237 A B K f k x x').
Proof. exact (MK_COMB (@lem4457837 A B K f k x) (@lem4457838 K x')). Qed.
Lemma lem4457840 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4457841 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term239 A B K f k x x') = (term240 A B K f k x x').
Proof. exact (MK_COMB (@lem4457840 B) (@lem4457839 A B K f k x x')). Qed.
Lemma lem4457842 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term237 A B K f k x x') = (term189 A B K f k x x').
Proof. exact (eq_refl (term237 A B K f k x x')). Qed.
Lemma lem4457843 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : ((term236 A B K f k x x') = (term237 A B K f k x x')) = ((term237 A B K f k x x') = (term189 A B K f k x x')).
Proof. exact (MK_COMB (@lem4457841 A B K f k x x') (@lem4457842 A B K f k x x')). Qed.
Lemma lem4457844 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term237 A B K f k x x') = (term189 A B K f k x x').
Proof. exact (EQ_MP (@lem4457843 A B K f k x x') (@lem4457835 A B K f k x x')). Qed.
Lemma lem4457845 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4457846 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term240 A B K f k x x') = (term241 A B K f k x x').
Proof. exact (MK_COMB (@lem4457845 B) (@lem4457844 A B K f k x x')). Qed.
Lemma lem4457847 {B K : Type'} (x : K -> B) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4457848 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) (x'' : K) : ((term237 A B K f k x x'') = (x' x'')) = ((term189 A B K f k x x'') = (x' x'')).
Proof. exact (MK_COMB (@lem4457846 A B K f k x x'') (@lem4457847 B K x' x'')). Qed.
Lemma lem4457851 {K : Type'} (x : K) (k : K -> Prop) : (term75 K x k) = (term75 K x k).
Proof. exact (eq_refl (term75 K x k)). Qed.
Lemma lem4457852 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) (x'' : K) : (term242 A B K f k x x' x'') = (term243 A B K f k x x' x'').
Proof. exact (MK_COMB (@lem4457851 K x'' k) (@lem4457848 A B K f k x x' x'')). Qed.
Lemma lem4457855 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) : (term244 A B K f k x x') = (term245 A B K f k x x').
Proof. exact (fun_ext (fun x'' : K => @lem4457852 A B K f k x x' x'')). Qed.
Lemma lem4457856 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4457857 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) : (term234 A B K f k x x') = (term246 A B K f k x x').
Proof. exact (MK_COMB (@lem4457856 K) (@lem4457855 A B K f k x x')). Qed.
Lemma lem4457862 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) : ((term192 A B K f k x) = (@RESTRICTION K B k x')) = (term246 A B K f k x x').
Proof. exact (TRANS (@lem4457823 A B K f k x x') (@lem4457857 A B K f k x x')). Qed.
Lemma lem4457863 {A B K : Type'} (x : K -> B) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) (h1 : g = (term192 A B K f k x')) : (g = (@RESTRICTION K B k x)) = (term246 A B K f k x' x).
Proof. exact (TRANS (@lem4457819 A B K x g f k x' h1) (@lem4457862 A B K f k x' x)). Qed.
Lemma lem4457864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4457865 {A B K : Type'} (x : K -> B) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) (h1 : g = (term192 A B K f k x')) : (term212 B K g k x) = (term247 A B K f k x' x).
Proof. exact (MK_COMB (@lem4457864) (@lem4457863 A B K x g f k x' h1)). Qed.
Lemma lem4457880 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term220 A B K k x f s) = (term220 A B K k x f s).
Proof. exact (eq_refl (term220 A B K k x f s)). Qed.
Lemma lem4457881 {A B K : Type'} (x : K -> B) (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) (h1 : g = (term192 A B K f k x')) : (term222 A B K g k x f s) = (term248 A B K x' k x f s).
Proof. exact (MK_COMB (@lem4457865 A B K x g f k x' h1) (@lem4457880 A B K k x f s)). Qed.
Lemma lem4457884 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : g = (term192 A B K f k x)) : (term224 A B K g k f s) = (term249 A B K x k f s).
Proof. exact (fun_ext (fun x' : K -> B => @lem4457881 A B K x' s g f k x h1)). Qed.
Lemma lem4457885 {B K : Type'} : (@ex (K -> B)) = (@ex (K -> B)).
Proof. exact (eq_refl (@ex (K -> B))). Qed.
Lemma lem4457886 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : g = (term192 A B K f k x)) : (term225 A B K g k f s) = (term250 A B K x k f s).
Proof. exact (MK_COMB (@lem4457885 B K) (@lem4457884 A B K s g f k x h1)). Qed.
Lemma lem4457891 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : g = (term192 A B K f k x)) : (term250 A B K x k f s) = (term225 A B K g k f s).
Proof. exact (SYM (@lem4457886 A B K s g f k x h1)). Qed.
Lemma lem4457892 {A B : Type'} (s : A -> Prop) : term226 A B s.
Proof. exact (@lem4388360 A B s). Qed.
Lemma lem4457893 {A B : Type'} (s : A -> Prop) : (term226 A B s) = (term227 A B s).
Proof. exact (eq_refl (term226 A B s)). Qed.
Lemma lem4457894 {A B : Type'} (s : A -> Prop) : term227 A B s.
Proof. exact (EQ_MP (@lem4457893 A B s) (@lem4457892 A B s)). Qed.
Lemma lem4457895 {A B : Type'} (s : A -> Prop) (f : A -> B) : term228 A B s f.
Proof. exact (@lem4457894 A B s f). Qed.
Lemma lem4457896 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term228 A B s f) = (term229 A B s f).
Proof. exact (eq_refl (term228 A B s f)). Qed.
Lemma lem4457897 {A B : Type'} (s : A -> Prop) (f : A -> B) : term229 A B s f.
Proof. exact (EQ_MP (@lem4457896 A B s f) (@lem4457895 A B s f)). Qed.
Lemma lem4457898 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : term230 A B s f g.
Proof. exact (@lem4457897 A B s f g). Qed.
Lemma lem4457899 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : (term230 A B s f g) = (((@RESTRICTION A B s f) = (@RESTRICTION A B s g)) = (term231 A B s f g)).
Proof. exact (eq_refl (term230 A B s f g)). Qed.
Lemma lem4457915 {B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : g = (@RESTRICTION K B k x)) : g = (@RESTRICTION K B k x).
Proof. exact (h1). Qed.
Lemma lem4457916 {B K : Type'} : (@eq (K -> B)) = (@eq (K -> B)).
Proof. exact (eq_refl (@eq (K -> B))). Qed.
Lemma lem4457917 {B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : g = (@RESTRICTION K B k x)) : (@eq (K -> B) g) = (term251 B K k x).
Proof. exact (MK_COMB (@lem4457916 B K) (@lem4457915 B K g k x h1)). Qed.
Lemma lem4457918 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term192 A B K f k x) = (term192 A B K f k x).
Proof. exact (eq_refl (term192 A B K f k x)). Qed.
Lemma lem4457919 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (g : K -> B) (k : K -> Prop) (x' : K -> B) (h1 : g = (@RESTRICTION K B k x')) : (g = (term192 A B K f k x)) = ((@RESTRICTION K B k x') = (term192 A B K f k x)).
Proof. exact (MK_COMB (@lem4457917 B K g k x' h1) (@lem4457918 A B K f k x)). Qed.
Lemma lem4457921 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> B) : ((@RESTRICTION A B s f) = (@RESTRICTION A B s g)) = (term231 A B s f g).
Proof. exact (EQ_MP (@lem4457899 A B s f g) (@lem4457898 A B s f g)). Qed.
Lemma lem4457922 {B K : Type'} (s : K -> Prop) (f : K -> B) (g : K -> B) : ((@RESTRICTION K B s f) = (@RESTRICTION K B s g)) = (term233 B K s f g).
Proof. exact (@lem4457921 K B s f g). Qed.
Lemma lem4457923 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) : ((@RESTRICTION K B k x) = (term192 A B K f k x')) = (term252 A B K x f k x').
Proof. exact (@lem4457922 B K k x (term191 A B K f k x')). Qed.
Lemma lem4457933 {A B : Type'} (f : A -> B) (y : A) : (term64 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4457934 {B K : Type'} (f : K -> B) (y : K) : (term235 B K f y) = (f y).
Proof. exact (@lem4457933 K B f y). Qed.
Lemma lem4457935 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term236 A B K f k x x') = (term237 A B K f k x x').
Proof. exact (@lem4457934 B K (term191 A B K f k x) x'). Qed.
Lemma lem4457936 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term237 A B K f k x i) = (term189 A B K f k x i).
Proof. exact (eq_refl (term237 A B K f k x i)). Qed.
Lemma lem4457937 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term238 A B K f k x) = (term191 A B K f k x).
Proof. exact (fun_ext (fun i : K => @lem4457936 A B K f k x i)). Qed.
Lemma lem4457938 {K : Type'} (x : K) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4457939 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term236 A B K f k x x') = (term237 A B K f k x x').
Proof. exact (MK_COMB (@lem4457937 A B K f k x) (@lem4457938 K x')). Qed.
Lemma lem4457940 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4457941 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term239 A B K f k x x') = (term240 A B K f k x x').
Proof. exact (MK_COMB (@lem4457940 B) (@lem4457939 A B K f k x x')). Qed.
Lemma lem4457942 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term237 A B K f k x x') = (term189 A B K f k x x').
Proof. exact (eq_refl (term237 A B K f k x x')). Qed.
Lemma lem4457943 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : ((term236 A B K f k x x') = (term237 A B K f k x x')) = ((term237 A B K f k x x') = (term189 A B K f k x x')).
Proof. exact (MK_COMB (@lem4457941 A B K f k x x') (@lem4457942 A B K f k x x')). Qed.
Lemma lem4457944 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term237 A B K f k x x') = (term189 A B K f k x x').
Proof. exact (EQ_MP (@lem4457943 A B K f k x x') (@lem4457935 A B K f k x x')). Qed.
Lemma lem4457945 {B K : Type'} (x : K -> B) (x' : K) : (term253 B K x x') = (term253 B K x x').
Proof. exact (eq_refl (term253 B K x x')). Qed.
Lemma lem4457946 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) (x'' : K) : ((x x'') = (term237 A B K f k x' x'')) = ((x x'') = (term189 A B K f k x' x'')).
Proof. exact (MK_COMB (@lem4457945 B K x x'') (@lem4457944 A B K f k x' x'')). Qed.
Lemma lem4457949 {K : Type'} (x : K) (k : K -> Prop) : (term75 K x k) = (term75 K x k).
Proof. exact (eq_refl (term75 K x k)). Qed.
Lemma lem4457950 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) (x'' : K) : (term254 A B K x f k x' x'') = (term255 A B K x f k x' x'').
Proof. exact (MK_COMB (@lem4457949 K x'' k) (@lem4457946 A B K x f k x' x'')). Qed.
Lemma lem4457953 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) : (term256 A B K x f k x') = (term257 A B K x f k x').
Proof. exact (fun_ext (fun x'' : K => @lem4457950 A B K x f k x' x'')). Qed.
Lemma lem4457954 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4457955 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) : (term252 A B K x f k x') = (term258 A B K x f k x').
Proof. exact (MK_COMB (@lem4457954 K) (@lem4457953 A B K x f k x')). Qed.
Lemma lem4457960 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) : ((@RESTRICTION K B k x) = (term192 A B K f k x')) = (term258 A B K x f k x').
Proof. exact (TRANS (@lem4457923 A B K x f k x') (@lem4457955 A B K x f k x')). Qed.
Lemma lem4457961 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (g : K -> B) (k : K -> Prop) (x' : K -> B) (h1 : g = (@RESTRICTION K B k x')) : (g = (term192 A B K f k x)) = (term258 A B K x' f k x).
Proof. exact (TRANS (@lem4457919 A B K f x g k x' h1) (@lem4457960 A B K x' f k x)). Qed.
Lemma lem4457962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4457963 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (g : K -> B) (k : K -> Prop) (x' : K -> B) (h1 : g = (@RESTRICTION K B k x')) : (term194 A B K g f k x) = (term259 A B K x' f k x).
Proof. exact (MK_COMB (@lem4457962) (@lem4457961 A B K f x g k x' h1)). Qed.
Lemma lem4457970 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term100 A K k x s) = (term100 A K k x s).
Proof. exact (eq_refl (term100 A K k x s)). Qed.
Lemma lem4457971 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x' : K -> B) (h1 : g = (@RESTRICTION K B k x')) : (term201 A B K g f k x s) = (term260 A B K x' f k x s).
Proof. exact (MK_COMB (@lem4457963 A B K f x g k x' h1) (@lem4457970 A K k x s)). Qed.
Lemma lem4457974 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : g = (@RESTRICTION K B k x)) : (term203 A B K g f k s) = (term261 A B K x f k s).
Proof. exact (fun_ext (fun x' : K -> A => @lem4457971 A B K f x' s g k x h1)). Qed.
Lemma lem4457975 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4457976 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : g = (@RESTRICTION K B k x)) : (term204 A B K g f k s) = (term262 A B K x f k s).
Proof. exact (MK_COMB (@lem4457975 A K) (@lem4457974 A B K f s g k x h1)). Qed.
Lemma lem4457981 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : g = (@RESTRICTION K B k x)) : (term262 A B K x f k s) = (term204 A B K g f k s).
Proof. exact (SYM (@lem4457976 A B K f s g k x h1)). Qed.
Lemma lem4457992 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term100 A K k x s) (h2 : g = (term192 A B K f k x)) : term263 A B K s g f k x.
Proof. exact (conj (@lem4457786 A K k x s h1) (@lem4457787 A B K g f k x h2)). Qed.
Lemma lem4458052 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4458053 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4458052 K P x). Qed.
Lemma lem4458054 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4458053 K k i). Qed.
Lemma lem4458055 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4458056 {K : Type'} (k : K -> Prop) (i : K) : (term75 K i k) = (term264 K k i).
Proof. exact (MK_COMB (@lem4458055) (@lem4458054 K k i)). Qed.
Lemma lem4458058 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4458059 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4458058 A P x). Qed.
Lemma lem4458060 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term265 A K x s i) = (term266 A K s x i).
Proof. exact (@lem4458059 A (s i) (x i)). Qed.
Lemma lem4458061 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term267 A K k x s i) = (term268 A K k s x i).
Proof. exact (MK_COMB (@lem4458056 K k i) (@lem4458060 A K s x i)). Qed.
Lemma lem4458064 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term269 A K k x s) = (term270 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4458061 A K k s x i)). Qed.
Lemma lem4458065 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4458066 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term100 A K k x s) = (term271 A K k s x).
Proof. exact (MK_COMB (@lem4458065 K) (@lem4458064 A K k s x)). Qed.
Lemma lem4458071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4458072 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term272 A K k x s) = (term273 A K k s x).
Proof. exact (MK_COMB (@lem4458071) (@lem4458066 A K k s x)). Qed.
Lemma lem4458076 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4458077 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4458076 K P x). Qed.
Lemma lem4458078 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4458077 K k i). Qed.
Lemma lem4458079 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4458080 {A K : Type'} (k : K -> Prop) (i : K) : (term274 A K i k) = (term275 A K k i).
Proof. exact (MK_COMB (@lem4458079 A) (@lem4458078 K k i)). Qed.
Lemma lem4458081 {A K : Type'} (x : K -> A) (i : K) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem4458082 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term276 A K k x i) = (term277 A K k x i).
Proof. exact (MK_COMB (@lem4458080 A K k i) (@lem4458081 A K x i)). Qed.
Lemma lem4458083 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4458084 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term187 A K k x i) = (term278 A K k x i).
Proof. exact (MK_COMB (@lem4458082 A K k x i) (@lem4458083 A)). Qed.
Lemma lem4458085 {A B K : Type'} (f : type1514 A B K) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4458086 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term189 A B K f k x i) = (term279 A B K f k x i).
Proof. exact (MK_COMB (@lem4458085 A B K f i) (@lem4458084 A K k x i)). Qed.
Lemma lem4458087 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term191 A B K f k x) = (term280 A B K f k x).
Proof. exact (fun_ext (fun i : K => @lem4458086 A B K f k x i)). Qed.
Lemma lem4458088 {B K : Type'} (k : K -> Prop) : (@RESTRICTION K B k) = (@RESTRICTION K B k).
Proof. exact (eq_refl (@RESTRICTION K B k)). Qed.
Lemma lem4458089 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term192 A B K f k x) = (term281 A B K f k x).
Proof. exact (MK_COMB (@lem4458088 B K k) (@lem4458087 A B K f k x)). Qed.
Lemma lem4458090 {B K : Type'} (g : K -> B) : (@eq (K -> B) g) = (@eq (K -> B) g).
Proof. exact (eq_refl (@eq (K -> B) g)). Qed.
Lemma lem4458091 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (g = (term192 A B K f k x)) = (g = (term281 A B K f k x)).
Proof. exact (MK_COMB (@lem4458090 B K g) (@lem4458089 A B K f k x)). Qed.
Lemma lem4458094 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term263 A B K s g f k x) = (term282 A B K s g f k x).
Proof. exact (MK_COMB (@lem4458072 A K k s x) (@lem4458091 A B K g f k x)). Qed.
Lemma lem4458097 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4458098 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term283 A B K s g f k x) = (term284 A B K s g f k x).
Proof. exact (MK_COMB (@lem4458097) (@lem4458094 A B K s g f k x)). Qed.
Lemma lem4458112 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4458113 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4458112 K P x). Qed.
Lemma lem4458114 {K : Type'} (k : K -> Prop) (x : K) : (@IN K x k) = (k x).
Proof. exact (@lem4458113 K k x). Qed.
Lemma lem4458115 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4458116 {K : Type'} (k : K -> Prop) (x : K) : (term75 K x k) = (term264 K k x).
Proof. exact (MK_COMB (@lem4458115) (@lem4458114 K k x)). Qed.
Lemma lem4458120 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4458121 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4458120 K P x). Qed.
Lemma lem4458122 {K : Type'} (k : K -> Prop) (x : K) : (@IN K x k) = (k x).
Proof. exact (@lem4458121 K k x). Qed.
Lemma lem4458123 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4458124 {A K : Type'} (k : K -> Prop) (x : K) : (term274 A K x k) = (term275 A K k x).
Proof. exact (MK_COMB (@lem4458123 A) (@lem4458122 K k x)). Qed.
Lemma lem4458125 {A K : Type'} (x : K -> A) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4458126 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term276 A K k x x') = (term277 A K k x x').
Proof. exact (MK_COMB (@lem4458124 A K k x') (@lem4458125 A K x x')). Qed.
Lemma lem4458127 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4458128 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term187 A K k x x') = (term278 A K k x x').
Proof. exact (MK_COMB (@lem4458126 A K k x x') (@lem4458127 A)). Qed.
Lemma lem4458129 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4458130 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term189 A B K f k x x') = (term279 A B K f k x x').
Proof. exact (MK_COMB (@lem4458129 A B K f x') (@lem4458128 A K k x x')). Qed.
Lemma lem4458131 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4458132 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term241 A B K f k x x') = (term285 A B K f k x x').
Proof. exact (MK_COMB (@lem4458131 B) (@lem4458130 A B K f k x x')). Qed.
Lemma lem4458133 {B K : Type'} (x : K -> B) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4458134 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) (x'' : K) : ((term189 A B K f k x x'') = (x' x'')) = ((term279 A B K f k x x'') = (x' x'')).
Proof. exact (MK_COMB (@lem4458132 A B K f k x x'') (@lem4458133 B K x' x'')). Qed.
Lemma lem4458137 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) (x'' : K) : (term243 A B K f k x x' x'') = (term286 A B K f k x x' x'').
Proof. exact (MK_COMB (@lem4458116 K k x'') (@lem4458134 A B K f k x x' x'')). Qed.
Lemma lem4458140 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) : (term245 A B K f k x x') = (term287 A B K f k x x').
Proof. exact (fun_ext (fun x'' : K => @lem4458137 A B K f k x x' x'')). Qed.
Lemma lem4458141 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4458142 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) : (term246 A B K f k x x') = (term288 A B K f k x x').
Proof. exact (MK_COMB (@lem4458141 K) (@lem4458140 A B K f k x x')). Qed.
Lemma lem4458147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4458148 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) : (term247 A B K f k x x') = (term289 A B K f k x x').
Proof. exact (MK_COMB (@lem4458147) (@lem4458142 A B K f k x x')). Qed.
Lemma lem4458156 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4458157 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4458156 K P x). Qed.
Lemma lem4458158 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4458157 K k i). Qed.
Lemma lem4458159 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4458160 {K : Type'} (k : K -> Prop) (i : K) : (term75 K i k) = (term264 K k i).
Proof. exact (MK_COMB (@lem4458159) (@lem4458158 K k i)). Qed.
Lemma lem4458170 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4458171 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4458170 A P x). Qed.
Lemma lem4458172 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term290 A K x s i) = (s i x).
Proof. exact (@lem4458171 A (s i) x). Qed.
Lemma lem4458173 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (i : K) (x' : A) : (term291 A B K x f i x') = (term291 A B K x f i x').
Proof. exact (eq_refl (term291 A B K x f i x')). Qed.
Lemma lem4458174 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term292 A B K x f x' s i) = (term293 A B K x f s i x').
Proof. exact (MK_COMB (@lem4458173 A B K x f i x') (@lem4458172 A K s i x')). Qed.
Lemma lem4458177 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term294 A B K x f s i) = (term295 A B K x f s i).
Proof. exact (fun_ext (fun x' : A => @lem4458174 A B K x f s i x')). Qed.
Lemma lem4458178 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4458179 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term217 A B K x f s i) = (term296 A B K x f s i).
Proof. exact (MK_COMB (@lem4458178 A) (@lem4458177 A B K x f s i)). Qed.
Lemma lem4458184 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term218 A B K k x f s i) = (term297 A B K k x f s i).
Proof. exact (MK_COMB (@lem4458160 K k i) (@lem4458179 A B K x f s i)). Qed.
Lemma lem4458187 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term219 A B K k x f s) = (term298 A B K k x f s).
Proof. exact (fun_ext (fun i : K => @lem4458184 A B K k x f s i)). Qed.
Lemma lem4458188 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4458189 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term220 A B K k x f s) = (term299 A B K k x f s).
Proof. exact (MK_COMB (@lem4458188 K) (@lem4458187 A B K k x f s)). Qed.
Lemma lem4458194 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term248 A B K x k x' f s) = (term300 A B K x k x' f s).
Proof. exact (MK_COMB (@lem4458148 A B K f k x x') (@lem4458189 A B K k x' f s)). Qed.
Lemma lem4458197 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term249 A B K x k f s) = (term301 A B K x k f s).
Proof. exact (fun_ext (fun x' : K -> B => @lem4458194 A B K x k x' f s)). Qed.
Lemma lem4458198 {B K : Type'} : (@ex (K -> B)) = (@ex (K -> B)).
Proof. exact (eq_refl (@ex (K -> B))). Qed.
Lemma lem4458199 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term250 A B K x k f s) = (term302 A B K x k f s).
Proof. exact (MK_COMB (@lem4458198 B K) (@lem4458197 A B K x k f s)). Qed.
Lemma lem4458204 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term303 A B K g x k f s) = (term304 A B K g x k f s).
Proof. exact (MK_COMB (@lem4458098 A B K s g f k x) (@lem4458199 A B K x k f s)). Qed.
Lemma lem4458207 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term304 A B K g x k f s) = (term303 A B K g x k f s).
Proof. exact (SYM (@lem4458204 A B K g x k f s)). Qed.
Lemma lem4458209 (p : Prop) : p = (term305 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4458210 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term304 A B K g x k f s) = (term306 A B K g x k f s).
Proof. exact (@lem4458209 (term304 A B K g x k f s)). Qed.
Lemma lem4458211 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term306 A B K g x k f s) = (term304 A B K g x k f s).
Proof. exact (SYM (@lem4458210 A B K g x k f s)). Qed.
Lemma lem4458212 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term307 A B K g x k f s) : term307 A B K g x k f s.
Proof. exact (h1). Qed.
Lemma lem4458215 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term306 A B K g x k f s) : term306 A B K g x k f s.
Proof. exact (h1). Qed.
Lemma lem4458216 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term308 A B K g x k f s.
Proof. exact (fun h0 : term306 A B K g x k f s => @lem4458215 A B K g x k f s h0). Qed.
Lemma lem4458217 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term308 A B K g x k f s) : term308 A B K g x k f s.
Proof. exact (h1). Qed.
Lemma lem4458218 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term306 A B K g x k f s) : term306 A B K g x k f s.
Proof. exact (h1). Qed.
Lemma lem4458219 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term306 A B K g x k f s) (h2 : term308 A B K g x k f s) : term306 A B K g x k f s.
Proof. exact (@lem4458217 A B K g x k f s h2 (@lem4458218 A B K g x k f s h1)). Qed.
Lemma lem4458220 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term306 A B K g x k f s) : term309 A B K g x k f s.
Proof. exact (fun h0 : term308 A B K g x k f s => @lem4458219 A B K g x k f s h1 h0). Qed.
Lemma lem4458221 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term308 A B K g x k f s) : term308 A B K g x k f s.
Proof. exact (h1). Qed.
Lemma lem4458222 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term306 A B K g x k f s) (h2 : term308 A B K g x k f s) : term306 A B K g x k f s.
Proof. exact (@lem4458220 A B K g x k f s h1 (@lem4458221 A B K g x k f s h2)). Qed.
Lemma lem4458223 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term308 A B K g x k f s) : term308 A B K g x k f s.
Proof. exact (fun h0 : term306 A B K g x k f s => @lem4458222 A B K g x k f s h0 h1). Qed.
Lemma lem4458224 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term310 A B K g x k f s.
Proof. exact (fun h0 : term308 A B K g x k f s => @lem4458223 A B K g x k f s h0). Qed.
Lemma lem4458227 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term308 A B K g x k f s.
Proof. exact (@lem4458224 A B K g x k f s (@lem4458216 A B K g x k f s)). Qed.
Lemma lem4458228 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term308 A B K g x k f s.
Proof. exact (@lem4458227 A B K g x k f s). Qed.
Lemma lem4458250 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4458251 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term306 A B K g x k f s) = (term311 A B K g x k f s).
Proof. exact (@lem4458250 (term307 A B K g x k f s)). Qed.
Lemma lem4458253 (t : Prop) : (term312 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4458254 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term311 A B K g x k f s) = (term304 A B K g x k f s).
Proof. exact (@lem4458253 (term304 A B K g x k f s)). Qed.
Lemma lem4458257 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term306 A B K g x k f s) = (term304 A B K g x k f s).
Proof. exact (TRANS (@lem4458251 A B K g x k f s) (@lem4458254 A B K g x k f s)). Qed.
Lemma lem4458378 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term313 A B K x k f s) = (term314 A B K x k f s).
Proof. exact (fun_ext (fun g : K -> B => @lem4458257 A B K g x k f s)). Qed.
Lemma lem4458379 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4458380 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term315 A B K x k f s) = (term316 A B K x k f s).
Proof. exact (MK_COMB (@lem4458379 B K) (@lem4458378 A B K x k f s)). Qed.
Lemma lem4458385 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term317 A B K k f s) = (term318 A B K k f s).
Proof. exact (fun_ext (fun x : K -> A => @lem4458380 A B K x k f s)). Qed.
Lemma lem4458386 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4458387 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term319 A B K k f s) = (term320 A B K k f s).
Proof. exact (MK_COMB (@lem4458386 A K) (@lem4458385 A B K k f s)). Qed.
Lemma lem4458392 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) : (term321 A B K f s) = (term322 A B K f s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4458387 A B K k f s)). Qed.
Lemma lem4458393 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4458394 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) : (term323 A B K f s) = (term324 A B K f s).
Proof. exact (MK_COMB (@lem4458393 K) (@lem4458392 A B K f s)). Qed.
Lemma lem4458399 {A B K : Type'} (s : type1470 A K) : (term325 A B K s) = (term326 A B K s).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4458394 A B K f s)). Qed.
Lemma lem4458400 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4458401 {A B K : Type'} (s : type1470 A K) : (term327 A B K s) = (term328 A B K s).
Proof. exact (MK_COMB (@lem4458400 A B K) (@lem4458399 A B K s)). Qed.
Lemma lem4458406 {A B K : Type'} : (term329 A B K) = (term330 A B K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4458401 A B K s)). Qed.
Lemma lem4458407 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4458414 {A B K : Type'} : (term331 A B K) = (term332 A B K).
Proof. exact (MK_COMB (@lem4458407 A K) (@lem4458406 A B K)). Qed.
Lemma lem4458415 {A B K : Type'} (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : _51538 = (term333 A B K).
Proof. exact (h1). Qed.
Lemma lem4458416 {A B K : Type'} (f : type1514 A B K) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4458417 {A B K : Type'} (f : type1514 A B K) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (_51538 f) = (term334 A B K f).
Proof. exact (MK_COMB (@lem4458415 A B K _51538 h1) (@lem4458416 A B K f)). Qed.
Lemma lem4458418 {A B K : Type'} (f : type1514 A B K) : (term334 A B K f) = (term335 A B K f).
Proof. exact (eq_refl (term334 A B K f)). Qed.
Lemma lem4458419 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term336 A B K _51538 f) = (term336 A B K _51538 f).
Proof. exact (eq_refl (term336 A B K _51538 f)). Qed.
Lemma lem4458420 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : ((_51538 f) = (term334 A B K f)) = ((_51538 f) = (term335 A B K f)).
Proof. exact (MK_COMB (@lem4458419 A B K _51538 f) (@lem4458418 A B K f)). Qed.
Lemma lem4458421 {A B K : Type'} (f : type1514 A B K) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (_51538 f) = (term335 A B K f).
Proof. exact (EQ_MP (@lem4458420 A B K _51538 f) (@lem4458417 A B K f _51538 h1)). Qed.
Lemma lem4458422 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4458423 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (_51538 f k) = (term337 A B K f k).
Proof. exact (MK_COMB (@lem4458421 A B K f _51538 h1) (@lem4458422 K k)). Qed.
Lemma lem4458424 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) : (term337 A B K f k) = (term338 A B K f k).
Proof. exact (eq_refl (term337 A B K f k)). Qed.
Lemma lem4458425 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (term339 A B K _51538 f k) = (term339 A B K _51538 f k).
Proof. exact (eq_refl (term339 A B K _51538 f k)). Qed.
Lemma lem4458426 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : ((_51538 f k) = (term337 A B K f k)) = ((_51538 f k) = (term338 A B K f k)).
Proof. exact (MK_COMB (@lem4458425 A B K _51538 f k) (@lem4458424 A B K f k)). Qed.
Lemma lem4458427 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (_51538 f k) = (term338 A B K f k).
Proof. exact (EQ_MP (@lem4458426 A B K _51538 f k) (@lem4458423 A B K f k _51538 h1)). Qed.
Lemma lem4458428 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4458429 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (_51538 f k x) = (term340 A B K f k x).
Proof. exact (MK_COMB (@lem4458427 A B K f k _51538 h1) (@lem4458428 A K x)). Qed.
Lemma lem4458430 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term340 A B K f k x) = (term280 A B K f k x).
Proof. exact (eq_refl (term340 A B K f k x)). Qed.
Lemma lem4458431 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term341 A B K _51538 f k x) = (term341 A B K _51538 f k x).
Proof. exact (eq_refl (term341 A B K _51538 f k x)). Qed.
Lemma lem4458432 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : ((_51538 f k x) = (term340 A B K f k x)) = ((_51538 f k x) = (term280 A B K f k x)).
Proof. exact (MK_COMB (@lem4458431 A B K _51538 f k x) (@lem4458430 A B K f k x)). Qed.
Lemma lem4458433 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (_51538 f k x) = (term280 A B K f k x).
Proof. exact (EQ_MP (@lem4458432 A B K _51538 f k x) (@lem4458429 A B K f k x _51538 h1)). Qed.
Lemma lem4458453 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term293 A B K x f s i x') = (term293 A B K x f s i x').
Proof. exact (eq_refl (term293 A B K x f s i x')). Qed.
Lemma lem4458454 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term295 A B K x f s i) = (term295 A B K x f s i).
Proof. exact (fun_ext (fun x' : A => @lem4458453 A B K x f s i x')). Qed.
Lemma lem4458455 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4458456 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term296 A B K x f s i) = (term296 A B K x f s i).
Proof. exact (MK_COMB (@lem4458455 A) (@lem4458454 A B K x f s i)). Qed.
Lemma lem4458461 {K : Type'} (k : K -> Prop) (i : K) : (term264 K k i) = (term264 K k i).
Proof. exact (eq_refl (term264 K k i)). Qed.
Lemma lem4458462 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term297 A B K k x f s i) = (term297 A B K k x f s i).
Proof. exact (MK_COMB (@lem4458461 K k i) (@lem4458456 A B K x f s i)). Qed.
Lemma lem4458463 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term298 A B K k x f s) = (term298 A B K k x f s).
Proof. exact (fun_ext (fun i : K => @lem4458462 A B K k x f s i)). Qed.
Lemma lem4458464 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4458465 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term299 A B K k x f s) = (term299 A B K k x f s).
Proof. exact (MK_COMB (@lem4458464 K) (@lem4458463 A B K k x f s)). Qed.
Lemma lem4458492 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) (x'' : K) : (term286 A B K f k x x' x'') = (term286 A B K f k x x' x'').
Proof. exact (eq_refl (term286 A B K f k x x' x'')). Qed.
Lemma lem4458493 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) : (term287 A B K f k x x') = (term287 A B K f k x x').
Proof. exact (fun_ext (fun x'' : K => @lem4458492 A B K f k x x' x'')). Qed.
Lemma lem4458494 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4458495 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) : (term288 A B K f k x x') = (term288 A B K f k x x').
Proof. exact (MK_COMB (@lem4458494 K) (@lem4458493 A B K f k x x')). Qed.
Lemma lem4458496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4458497 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) : (term289 A B K f k x x') = (term289 A B K f k x x').
Proof. exact (MK_COMB (@lem4458496) (@lem4458495 A B K f k x x')). Qed.
Lemma lem4458498 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term300 A B K x k x' f s) = (term300 A B K x k x' f s).
Proof. exact (MK_COMB (@lem4458497 A B K f k x x') (@lem4458465 A B K k x' f s)). Qed.
Lemma lem4458499 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term301 A B K x k f s) = (term301 A B K x k f s).
Proof. exact (fun_ext (fun x' : K -> B => @lem4458498 A B K x k x' f s)). Qed.
Lemma lem4458500 {B K : Type'} : (@ex (K -> B)) = (@ex (K -> B)).
Proof. exact (eq_refl (@ex (K -> B))). Qed.
Lemma lem4458501 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term302 A B K x k f s) = (term302 A B K x k f s).
Proof. exact (MK_COMB (@lem4458500 B K) (@lem4458499 A B K x k f s)). Qed.
Lemma lem4458503 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term280 A B K f k x) = (_51538 f k x).
Proof. exact (SYM (@lem4458433 A B K f k x _51538 h1)). Qed.
Lemma lem4458504 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term280 A B K f k x) = (_51538 f k x).
Proof. exact (@lem4458503 A B K f k x _51538 h1). Qed.
Lemma lem4458507 {B K : Type'} (k : K -> Prop) : (@RESTRICTION K B k) = (@RESTRICTION K B k).
Proof. exact (eq_refl (@RESTRICTION K B k)). Qed.
Lemma lem4458508 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term281 A B K f k x) = (term342 A B K _51538 f k x).
Proof. exact (MK_COMB (@lem4458507 B K k) (@lem4458504 A B K f k x _51538 h1)). Qed.
Lemma lem4458511 {B K : Type'} (g : K -> B) : (@eq (K -> B) g) = (@eq (K -> B) g).
Proof. exact (eq_refl (@eq (K -> B) g)). Qed.
Lemma lem4458512 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (g = (term281 A B K f k x)) = (g = (term342 A B K _51538 f k x)).
Proof. exact (MK_COMB (@lem4458511 B K g) (@lem4458508 A B K f k x _51538 h1)). Qed.
Lemma lem4458525 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term268 A K k s x i) = (term268 A K k s x i).
Proof. exact (eq_refl (term268 A K k s x i)). Qed.
Lemma lem4458526 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term270 A K k s x) = (term270 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4458525 A K k s x i)). Qed.
Lemma lem4458527 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4458528 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term271 A K k s x) = (term271 A K k s x).
Proof. exact (MK_COMB (@lem4458527 K) (@lem4458526 A K k s x)). Qed.
Lemma lem4458529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4458530 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term273 A K k s x) = (term273 A K k s x).
Proof. exact (MK_COMB (@lem4458529) (@lem4458528 A K k s x)). Qed.
Lemma lem4458531 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term282 A B K s g f k x) = (term343 A B K s g _51538 f k x).
Proof. exact (MK_COMB (@lem4458530 A K k s x) (@lem4458512 A B K g f k x _51538 h1)). Qed.
Lemma lem4458532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4458533 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term284 A B K s g f k x) = (term344 A B K s g _51538 f k x).
Proof. exact (MK_COMB (@lem4458532) (@lem4458531 A B K s g f k x _51538 h1)). Qed.
Lemma lem4458534 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term304 A B K g x k f s) = (term345 A B K g _51538 x k f s).
Proof. exact (MK_COMB (@lem4458533 A B K s g f k x _51538 h1) (@lem4458501 A B K x k f s)). Qed.
Lemma lem4458535 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term314 A B K x k f s) = (term346 A B K _51538 x k f s).
Proof. exact (fun_ext (fun g : K -> B => @lem4458534 A B K g x k f s _51538 h1)). Qed.
Lemma lem4458536 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4458537 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term316 A B K x k f s) = (term347 A B K _51538 x k f s).
Proof. exact (MK_COMB (@lem4458536 B K) (@lem4458535 A B K x k f s _51538 h1)). Qed.
Lemma lem4458538 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term318 A B K k f s) = (term348 A B K _51538 k f s).
Proof. exact (fun_ext (fun x : K -> A => @lem4458537 A B K x k f s _51538 h1)). Qed.
Lemma lem4458539 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4458540 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term320 A B K k f s) = (term349 A B K _51538 k f s).
Proof. exact (MK_COMB (@lem4458539 A K) (@lem4458538 A B K k f s _51538 h1)). Qed.
Lemma lem4458541 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term322 A B K f s) = (term350 A B K _51538 f s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4458540 A B K k f s _51538 h1)). Qed.
Lemma lem4458542 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4458543 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term324 A B K f s) = (term351 A B K _51538 f s).
Proof. exact (MK_COMB (@lem4458542 K) (@lem4458541 A B K f s _51538 h1)). Qed.
Lemma lem4458544 {A B K : Type'} (s : type1470 A K) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term326 A B K s) = (term352 A B K _51538 s).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4458543 A B K f s _51538 h1)). Qed.
Lemma lem4458545 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4458546 {A B K : Type'} (s : type1470 A K) (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term328 A B K s) = (term353 A B K _51538 s).
Proof. exact (MK_COMB (@lem4458545 A B K) (@lem4458544 A B K s _51538 h1)). Qed.
Lemma lem4458547 {A B K : Type'} (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term330 A B K) = (term354 A B K _51538).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4458546 A B K s _51538 h1)). Qed.
Lemma lem4458548 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4458549 {A B K : Type'} (_51538 : type868 A B K) (h1 : _51538 = (term333 A B K)) : (term332 A B K) = (term355 A B K _51538).
Proof. exact (MK_COMB (@lem4458548 A K) (@lem4458547 A B K _51538 h1)). Qed.
Lemma lem4458550 {A B K : Type'} (_51538 : type868 A B K) : term356 A B K _51538.
Proof. exact (fun h0 : _51538 = (term333 A B K) => @lem4458549 A B K _51538 h0). Qed.
Lemma lem4458551 {A B K : Type'} : term357 A B K.
Proof. exact (fun _51538 : type868 A B K => @lem4458550 A B K _51538). Qed.
Lemma lem4458553 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term358 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem4458554 {A B K : Type'} (P : Prop) (c : type868 A B K) (Q : type236 A B K) : term359 A B K P c Q.
Proof. exact (@lem4458553 (type868 A B K) P c Q). Qed.
Lemma lem4458555 {A B K : Type'} : term360 A B K.
Proof. exact (@lem4458554 A B K (term332 A B K) (term333 A B K) (term361 A B K)). Qed.
Lemma lem4458556 {A B K : Type'} (_51538 : type868 A B K) : (term362 A B K _51538) = (term355 A B K _51538).
Proof. exact (eq_refl (term362 A B K _51538)). Qed.
Lemma lem4458557 {A B K : Type'} : (term363 A B K) = (term363 A B K).
Proof. exact (eq_refl (term363 A B K)). Qed.
Lemma lem4458558 {A B K : Type'} (_51538 : type868 A B K) : ((term332 A B K) = (term362 A B K _51538)) = ((term332 A B K) = (term355 A B K _51538)).
Proof. exact (MK_COMB (@lem4458557 A B K) (@lem4458556 A B K _51538)). Qed.
Lemma lem4458559 {A B K : Type'} (_51538 : type868 A B K) : (term364 A B K _51538) = (term364 A B K _51538).
Proof. exact (eq_refl (term364 A B K _51538)). Qed.
Lemma lem4458560 {A B K : Type'} (_51538 : type868 A B K) : (term365 A B K _51538) = (term356 A B K _51538).
Proof. exact (MK_COMB (@lem4458559 A B K _51538) (@lem4458558 A B K _51538)). Qed.
Lemma lem4458561 {A B K : Type'} : (term366 A B K) = (term367 A B K).
Proof. exact (fun_ext (fun _51538 : type868 A B K => @lem4458560 A B K _51538)). Qed.
Lemma lem4458562 {A B K : Type'} : (@all ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B)) = (@all ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B)).
Proof. exact (eq_refl (@all ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B))). Qed.
Lemma lem4458563 {A B K : Type'} : (term368 A B K) = (term357 A B K).
Proof. exact (MK_COMB (@lem4458562 A B K) (@lem4458561 A B K)). Qed.
Lemma lem4458564 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4458565 {A B K : Type'} : (term369 A B K) = (term370 A B K).
Proof. exact (MK_COMB (@lem4458564) (@lem4458563 A B K)). Qed.
Lemma lem4458566 {A B K : Type'} (_51538 : type868 A B K) : (term362 A B K _51538) = (term355 A B K _51538).
Proof. exact (eq_refl (term362 A B K _51538)). Qed.
Lemma lem4458567 {A B K : Type'} (_51538 : type868 A B K) : (term364 A B K _51538) = (term364 A B K _51538).
Proof. exact (eq_refl (term364 A B K _51538)). Qed.
Lemma lem4458568 {A B K : Type'} (_51538 : type868 A B K) : (term371 A B K _51538) = (term372 A B K _51538).
Proof. exact (MK_COMB (@lem4458567 A B K _51538) (@lem4458566 A B K _51538)). Qed.
Lemma lem4458569 {A B K : Type'} : (term373 A B K) = (term374 A B K).
Proof. exact (fun_ext (fun _51538 : type868 A B K => @lem4458568 A B K _51538)). Qed.
Lemma lem4458570 {A B K : Type'} : (@all ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B)) = (@all ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B)).
Proof. exact (eq_refl (@all ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B))). Qed.
Lemma lem4458571 {A B K : Type'} : (term375 A B K) = (term376 A B K).
Proof. exact (MK_COMB (@lem4458570 A B K) (@lem4458569 A B K)). Qed.
Lemma lem4458572 {A B K : Type'} : (term363 A B K) = (term363 A B K).
Proof. exact (eq_refl (term363 A B K)). Qed.
Lemma lem4458573 {A B K : Type'} : ((term332 A B K) = (term375 A B K)) = ((term332 A B K) = (term376 A B K)).
Proof. exact (MK_COMB (@lem4458572 A B K) (@lem4458571 A B K)). Qed.
Lemma lem4458574 {A B K : Type'} : (term360 A B K) = (term377 A B K).
Proof. exact (MK_COMB (@lem4458565 A B K) (@lem4458573 A B K)). Qed.
Lemma lem4458575 {A B K : Type'} : term377 A B K.
Proof. exact (EQ_MP (@lem4458574 A B K) (@lem4458555 A B K)). Qed.
Lemma lem4458576 {A B K : Type'} : (term332 A B K) = (term376 A B K).
Proof. exact (@lem4458575 A B K (@lem4458551 A B K)). Qed.
Lemma lem4458578 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term378 _3571 _3575 t)) = (term379 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4458579 {A B K : Type'} (s : type868 A B K) (t : type868 A B K) : (s = (term380 A B K t)) = (term381 A B K s t).
Proof. exact (@lem4458578 (type892 A B K) (type1514 A B K) s t). Qed.
Lemma lem4458580 {A B K : Type'} (_51538 : type868 A B K) : (_51538 = (term382 A B K)) = (term383 A B K _51538).
Proof. exact (@lem4458579 A B K _51538 (term333 A B K)). Qed.
Lemma lem4458581 {A B K : Type'} (f : type1514 A B K) : (term334 A B K f) = (term335 A B K f).
Proof. exact (eq_refl (term334 A B K f)). Qed.
Lemma lem4458582 {A B K : Type'} : (term382 A B K) = (term333 A B K).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4458581 A B K f)). Qed.
Lemma lem4458583 {A B K : Type'} (_51538 : type868 A B K) : (@eq ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538) = (@eq ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538).
Proof. exact (eq_refl (@eq ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538)). Qed.
Lemma lem4458584 {A B K : Type'} (_51538 : type868 A B K) : (_51538 = (term382 A B K)) = (_51538 = (term333 A B K)).
Proof. exact (MK_COMB (@lem4458583 A B K _51538) (@lem4458582 A B K)). Qed.
Lemma lem4458585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4458586 {A B K : Type'} (_51538 : type868 A B K) : (term384 A B K _51538) = (term385 A B K _51538).
Proof. exact (MK_COMB (@lem4458585) (@lem4458584 A B K _51538)). Qed.
Lemma lem4458587 {A B K : Type'} (f : type1514 A B K) : (term334 A B K f) = (term335 A B K f).
Proof. exact (eq_refl (term334 A B K f)). Qed.
Lemma lem4458588 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term336 A B K _51538 f) = (term336 A B K _51538 f).
Proof. exact (eq_refl (term336 A B K _51538 f)). Qed.
Lemma lem4458589 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : ((_51538 f) = (term334 A B K f)) = ((_51538 f) = (term335 A B K f)).
Proof. exact (MK_COMB (@lem4458588 A B K _51538 f) (@lem4458587 A B K f)). Qed.
Lemma lem4458590 {A B K : Type'} (_51538 : type868 A B K) : (term386 A B K _51538) = (term387 A B K _51538).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4458589 A B K _51538 f)). Qed.
Lemma lem4458591 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4458592 {A B K : Type'} (_51538 : type868 A B K) : (term383 A B K _51538) = (term388 A B K _51538).
Proof. exact (MK_COMB (@lem4458591 A B K) (@lem4458590 A B K _51538)). Qed.
Lemma lem4458593 {A B K : Type'} (_51538 : type868 A B K) : ((_51538 = (term382 A B K)) = (term383 A B K _51538)) = ((_51538 = (term333 A B K)) = (term388 A B K _51538)).
Proof. exact (MK_COMB (@lem4458586 A B K _51538) (@lem4458592 A B K _51538)). Qed.
Lemma lem4458594 {A B K : Type'} (_51538 : type868 A B K) : (_51538 = (term333 A B K)) = (term388 A B K _51538).
Proof. exact (EQ_MP (@lem4458593 A B K _51538) (@lem4458580 A B K _51538)). Qed.
Lemma lem4458596 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term378 _3571 _3575 t)) = (term379 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4458597 {A B K : Type'} (s : type892 A B K) (t : type892 A B K) : (s = (term389 A B K t)) = (term390 A B K s t).
Proof. exact (@lem4458596 (type887 A B K) (K -> Prop) s t). Qed.
Lemma lem4458598 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : ((_51538 f) = (term391 A B K f)) = (term392 A B K _51538 f).
Proof. exact (@lem4458597 A B K (_51538 f) (term335 A B K f)). Qed.
Lemma lem4458599 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) : (term337 A B K f k) = (term338 A B K f k).
Proof. exact (eq_refl (term337 A B K f k)). Qed.
Lemma lem4458600 {A B K : Type'} (f : type1514 A B K) : (term391 A B K f) = (term335 A B K f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4458599 A B K f k)). Qed.
Lemma lem4458601 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term336 A B K _51538 f) = (term336 A B K _51538 f).
Proof. exact (eq_refl (term336 A B K _51538 f)). Qed.
Lemma lem4458602 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : ((_51538 f) = (term391 A B K f)) = ((_51538 f) = (term335 A B K f)).
Proof. exact (MK_COMB (@lem4458601 A B K _51538 f) (@lem4458600 A B K f)). Qed.
Lemma lem4458603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4458604 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term393 A B K _51538 f) = (term394 A B K _51538 f).
Proof. exact (MK_COMB (@lem4458603) (@lem4458602 A B K _51538 f)). Qed.
Lemma lem4458605 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) : (term337 A B K f k) = (term338 A B K f k).
Proof. exact (eq_refl (term337 A B K f k)). Qed.
Lemma lem4458606 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (term339 A B K _51538 f k) = (term339 A B K _51538 f k).
Proof. exact (eq_refl (term339 A B K _51538 f k)). Qed.
Lemma lem4458607 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : ((_51538 f k) = (term337 A B K f k)) = ((_51538 f k) = (term338 A B K f k)).
Proof. exact (MK_COMB (@lem4458606 A B K _51538 f k) (@lem4458605 A B K f k)). Qed.
Lemma lem4458608 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term395 A B K _51538 f) = (term396 A B K _51538 f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4458607 A B K _51538 f k)). Qed.
Lemma lem4458609 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4458610 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term392 A B K _51538 f) = (term397 A B K _51538 f).
Proof. exact (MK_COMB (@lem4458609 K) (@lem4458608 A B K _51538 f)). Qed.
Lemma lem4458611 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (((_51538 f) = (term391 A B K f)) = (term392 A B K _51538 f)) = (((_51538 f) = (term335 A B K f)) = (term397 A B K _51538 f)).
Proof. exact (MK_COMB (@lem4458604 A B K _51538 f) (@lem4458610 A B K _51538 f)). Qed.
Lemma lem4458612 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : ((_51538 f) = (term335 A B K f)) = (term397 A B K _51538 f).
Proof. exact (EQ_MP (@lem4458611 A B K _51538 f) (@lem4458598 A B K _51538 f)). Qed.
Lemma lem4458614 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term378 _3571 _3575 t)) = (term379 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4458615 {A B K : Type'} (s : type887 A B K) (t : type887 A B K) : (s = (term398 A B K t)) = (term399 A B K s t).
Proof. exact (@lem4458614 (K -> B) (K -> A) s t). Qed.
Lemma lem4458616 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : ((_51538 f k) = (term400 A B K f k)) = (term401 A B K _51538 f k).
Proof. exact (@lem4458615 A B K (_51538 f k) (term338 A B K f k)). Qed.
Lemma lem4458617 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term340 A B K f k x) = (term280 A B K f k x).
Proof. exact (eq_refl (term340 A B K f k x)). Qed.
Lemma lem4458618 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) : (term400 A B K f k) = (term338 A B K f k).
Proof. exact (fun_ext (fun x : K -> A => @lem4458617 A B K f k x)). Qed.
Lemma lem4458619 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (term339 A B K _51538 f k) = (term339 A B K _51538 f k).
Proof. exact (eq_refl (term339 A B K _51538 f k)). Qed.
Lemma lem4458620 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : ((_51538 f k) = (term400 A B K f k)) = ((_51538 f k) = (term338 A B K f k)).
Proof. exact (MK_COMB (@lem4458619 A B K _51538 f k) (@lem4458618 A B K f k)). Qed.
Lemma lem4458621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4458622 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (term402 A B K _51538 f k) = (term403 A B K _51538 f k).
Proof. exact (MK_COMB (@lem4458621) (@lem4458620 A B K _51538 f k)). Qed.
Lemma lem4458623 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term340 A B K f k x) = (term280 A B K f k x).
Proof. exact (eq_refl (term340 A B K f k x)). Qed.
Lemma lem4458624 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term341 A B K _51538 f k x) = (term341 A B K _51538 f k x).
Proof. exact (eq_refl (term341 A B K _51538 f k x)). Qed.
Lemma lem4458625 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : ((_51538 f k x) = (term340 A B K f k x)) = ((_51538 f k x) = (term280 A B K f k x)).
Proof. exact (MK_COMB (@lem4458624 A B K _51538 f k x) (@lem4458623 A B K f k x)). Qed.
Lemma lem4458626 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (term404 A B K _51538 f k) = (term405 A B K _51538 f k).
Proof. exact (fun_ext (fun x : K -> A => @lem4458625 A B K _51538 f k x)). Qed.
Lemma lem4458627 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4458628 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (term401 A B K _51538 f k) = (term406 A B K _51538 f k).
Proof. exact (MK_COMB (@lem4458627 A K) (@lem4458626 A B K _51538 f k)). Qed.
Lemma lem4458629 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (((_51538 f k) = (term400 A B K f k)) = (term401 A B K _51538 f k)) = (((_51538 f k) = (term338 A B K f k)) = (term406 A B K _51538 f k)).
Proof. exact (MK_COMB (@lem4458622 A B K _51538 f k) (@lem4458628 A B K _51538 f k)). Qed.
Lemma lem4458630 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : ((_51538 f k) = (term338 A B K f k)) = (term406 A B K _51538 f k).
Proof. exact (EQ_MP (@lem4458629 A B K _51538 f k) (@lem4458616 A B K _51538 f k)). Qed.
Lemma lem4458632 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term378 _3571 _3575 t)) = (term379 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4458633 {B K : Type'} (s : K -> B) (t : K -> B) : (s = (term378 B K t)) = (term379 B K s t).
Proof. exact (@lem4458632 B K s t). Qed.
Lemma lem4458634 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : ((_51538 f k x) = (term407 A B K f k x)) = (term408 A B K _51538 f k x).
Proof. exact (@lem4458633 B K (_51538 f k x) (term280 A B K f k x)). Qed.
Lemma lem4458635 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term409 A B K f k x i) = (term279 A B K f k x i).
Proof. exact (eq_refl (term409 A B K f k x i)). Qed.
Lemma lem4458636 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term407 A B K f k x) = (term280 A B K f k x).
Proof. exact (fun_ext (fun i : K => @lem4458635 A B K f k x i)). Qed.
Lemma lem4458637 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term341 A B K _51538 f k x) = (term341 A B K _51538 f k x).
Proof. exact (eq_refl (term341 A B K _51538 f k x)). Qed.
Lemma lem4458638 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : ((_51538 f k x) = (term407 A B K f k x)) = ((_51538 f k x) = (term280 A B K f k x)).
Proof. exact (MK_COMB (@lem4458637 A B K _51538 f k x) (@lem4458636 A B K f k x)). Qed.
Lemma lem4458639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4458640 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term410 A B K _51538 f k x) = (term411 A B K _51538 f k x).
Proof. exact (MK_COMB (@lem4458639) (@lem4458638 A B K _51538 f k x)). Qed.
Lemma lem4458641 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term409 A B K f k x i) = (term279 A B K f k x i).
Proof. exact (eq_refl (term409 A B K f k x i)). Qed.
Lemma lem4458642 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term412 A B K _51538 f k x i) = (term412 A B K _51538 f k x i).
Proof. exact (eq_refl (term412 A B K _51538 f k x i)). Qed.
Lemma lem4458643 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : ((_51538 f k x i) = (term409 A B K f k x i)) = ((_51538 f k x i) = (term279 A B K f k x i)).
Proof. exact (MK_COMB (@lem4458642 A B K _51538 f k x i) (@lem4458641 A B K f k x i)). Qed.
Lemma lem4458644 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term413 A B K _51538 f k x) = (term414 A B K _51538 f k x).
Proof. exact (fun_ext (fun i : K => @lem4458643 A B K _51538 f k x i)). Qed.
Lemma lem4458645 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4458646 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term408 A B K _51538 f k x) = (term415 A B K _51538 f k x).
Proof. exact (MK_COMB (@lem4458645 K) (@lem4458644 A B K _51538 f k x)). Qed.
Lemma lem4458647 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (((_51538 f k x) = (term407 A B K f k x)) = (term408 A B K _51538 f k x)) = (((_51538 f k x) = (term280 A B K f k x)) = (term415 A B K _51538 f k x)).
Proof. exact (MK_COMB (@lem4458640 A B K _51538 f k x) (@lem4458646 A B K _51538 f k x)). Qed.
Lemma lem4458648 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : ((_51538 f k x) = (term280 A B K f k x)) = (term415 A B K _51538 f k x).
Proof. exact (EQ_MP (@lem4458647 A B K _51538 f k x) (@lem4458634 A B K _51538 f k x)). Qed.
Lemma lem4458649 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : ((_51538 f k x i) = (term279 A B K f k x i)) = ((_51538 f k x i) = (term279 A B K f k x i)).
Proof. exact (eq_refl ((_51538 f k x i) = (term279 A B K f k x i))). Qed.
Lemma lem4458650 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term414 A B K _51538 f k x) = (term414 A B K _51538 f k x).
Proof. exact (fun_ext (fun i : K => @lem4458649 A B K _51538 f k x i)). Qed.
Lemma lem4458651 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4458652 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term415 A B K _51538 f k x) = (term415 A B K _51538 f k x).
Proof. exact (MK_COMB (@lem4458651 K) (@lem4458650 A B K _51538 f k x)). Qed.
Lemma lem4458653 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : ((_51538 f k x) = (term280 A B K f k x)) = (term415 A B K _51538 f k x).
Proof. exact (TRANS (@lem4458648 A B K _51538 f k x) (@lem4458652 A B K _51538 f k x)). Qed.
Lemma lem4458654 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (term405 A B K _51538 f k) = (term416 A B K _51538 f k).
Proof. exact (fun_ext (fun x : K -> A => @lem4458653 A B K _51538 f k x)). Qed.
Lemma lem4458655 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4458656 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (term406 A B K _51538 f k) = (term417 A B K _51538 f k).
Proof. exact (MK_COMB (@lem4458655 A K) (@lem4458654 A B K _51538 f k)). Qed.
Lemma lem4458657 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : ((_51538 f k) = (term338 A B K f k)) = (term417 A B K _51538 f k).
Proof. exact (TRANS (@lem4458630 A B K _51538 f k) (@lem4458656 A B K _51538 f k)). Qed.
Lemma lem4458658 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term396 A B K _51538 f) = (term418 A B K _51538 f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4458657 A B K _51538 f k)). Qed.
Lemma lem4458659 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4458660 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term397 A B K _51538 f) = (term419 A B K _51538 f).
Proof. exact (MK_COMB (@lem4458659 K) (@lem4458658 A B K _51538 f)). Qed.
Lemma lem4458661 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : ((_51538 f) = (term335 A B K f)) = (term419 A B K _51538 f).
Proof. exact (TRANS (@lem4458612 A B K _51538 f) (@lem4458660 A B K _51538 f)). Qed.
Lemma lem4458662 {A B K : Type'} (_51538 : type868 A B K) : (term387 A B K _51538) = (term420 A B K _51538).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4458661 A B K _51538 f)). Qed.
Lemma lem4458663 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4458664 {A B K : Type'} (_51538 : type868 A B K) : (term388 A B K _51538) = (term421 A B K _51538).
Proof. exact (MK_COMB (@lem4458663 A B K) (@lem4458662 A B K _51538)). Qed.
Lemma lem4458665 {A B K : Type'} (_51538 : type868 A B K) : (_51538 = (term333 A B K)) = (term421 A B K _51538).
Proof. exact (TRANS (@lem4458594 A B K _51538) (@lem4458664 A B K _51538)). Qed.
Lemma lem4458666 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4458667 {A B K : Type'} (_51538 : type868 A B K) : (term364 A B K _51538) = (term422 A B K _51538).
Proof. exact (MK_COMB (@lem4458666) (@lem4458665 A B K _51538)). Qed.
Lemma lem4458668 {A B K : Type'} (_51538 : type868 A B K) : (term355 A B K _51538) = (term355 A B K _51538).
Proof. exact (eq_refl (term355 A B K _51538)). Qed.
Lemma lem4458669 {A B K : Type'} (_51538 : type868 A B K) : (term372 A B K _51538) = (term423 A B K _51538).
Proof. exact (MK_COMB (@lem4458667 A B K _51538) (@lem4458668 A B K _51538)). Qed.
Lemma lem4458670 {A B K : Type'} : (term374 A B K) = (term424 A B K).
Proof. exact (fun_ext (fun _51538 : type868 A B K => @lem4458669 A B K _51538)). Qed.
Lemma lem4458671 {A B K : Type'} : (@all ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B)) = (@all ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B)).
Proof. exact (eq_refl (@all ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B))). Qed.
Lemma lem4458672 {A B K : Type'} : (term376 A B K) = (term425 A B K).
Proof. exact (MK_COMB (@lem4458671 A B K) (@lem4458670 A B K)). Qed.
Lemma lem4458673 {A B K : Type'} : (term363 A B K) = (term363 A B K).
Proof. exact (eq_refl (term363 A B K)). Qed.
Lemma lem4458674 {A B K : Type'} : ((term332 A B K) = (term376 A B K)) = ((term332 A B K) = (term425 A B K)).
Proof. exact (MK_COMB (@lem4458673 A B K) (@lem4458672 A B K)). Qed.
Lemma lem4458677 {A B K : Type'} : (term332 A B K) = (term425 A B K).
Proof. exact (EQ_MP (@lem4458674 A B K) (@lem4458576 A B K)). Qed.
Lemma lem4458678 {A B K : Type'} : (term331 A B K) = (term425 A B K).
Proof. exact (TRANS (@lem4458414 A B K) (@lem4458677 A B K)). Qed.
Lemma lem4458683 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term293 A B K x f s i x') = (term293 A B K x f s i x').
Proof. exact (eq_refl (term293 A B K x f s i x')). Qed.
Lemma lem4458684 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term295 A B K x f s i) = (term295 A B K x f s i).
Proof. exact (fun_ext (fun x' : A => @lem4458683 A B K x f s i x')). Qed.
Lemma lem4458685 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4458686 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term296 A B K x f s i) = (term296 A B K x f s i).
Proof. exact (MK_COMB (@lem4458685 A) (@lem4458684 A B K x f s i)). Qed.
Lemma lem4458689 {K : Type'} (k : K -> Prop) (i : K) : (term264 K k i) = (term264 K k i).
Proof. exact (eq_refl (term264 K k i)). Qed.
Lemma lem4458690 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term297 A B K k x f s i) = (term297 A B K k x f s i).
Proof. exact (MK_COMB (@lem4458689 K k i) (@lem4458686 A B K x f s i)). Qed.
Lemma lem4458691 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term298 A B K k x f s) = (term298 A B K k x f s).
Proof. exact (fun_ext (fun i : K => @lem4458690 A B K k x f s i)). Qed.
Lemma lem4458692 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4458693 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term299 A B K k x f s) = (term299 A B K k x f s).
Proof. exact (MK_COMB (@lem4458692 K) (@lem4458691 A B K k x f s)). Qed.
Lemma lem4458697 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (k x) = False.
Proof. exact (h1). Qed.
Lemma lem4458698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4458699 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term264 K k x) = (imp False).
Proof. exact (MK_COMB (@lem4458698) (@lem4458697 K k x h1)). Qed.
Lemma lem4458701 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (k x) = False.
Proof. exact (h1). Qed.
Lemma lem4458702 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4458703 {A K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term275 A K k x) = (@COND A False).
Proof. exact (MK_COMB (@lem4458702 A) (@lem4458701 K k x h1)). Qed.
Lemma lem4458704 {A K : Type'} (x : K -> A) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4458705 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = False) : (term277 A K k x x') = (term426 A K x x').
Proof. exact (MK_COMB (@lem4458703 A K k x' h1) (@lem4458704 A K x x')). Qed.
Lemma lem4458706 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4458707 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = False) : (term278 A K k x x') = (term427 A K x x').
Proof. exact (MK_COMB (@lem4458705 A K x k x' h1) (@lem4458706 A)). Qed.
Lemma lem4458709 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4458710 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4458709 A t1 t2). Qed.
Lemma lem4458711 {A K : Type'} (x : K -> A) (x' : K) : (term427 A K x x') = (@ARB A).
Proof. exact (@lem4458710 A (x x') (@ARB A)). Qed.
Lemma lem4458712 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = False) : (term278 A K k x x') = (@ARB A).
Proof. exact (TRANS (@lem4458707 A K x k x' h1) (@lem4458711 A K x x')). Qed.
Lemma lem4458713 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4458714 {A B K : Type'} (x : K -> A) (f : type1514 A B K) (k : K -> Prop) (x' : K) (h1 : (k x') = False) : (term279 A B K f k x x') = (f x' (@ARB A)).
Proof. exact (MK_COMB (@lem4458713 A B K f x') (@lem4458712 A K x k x' h1)). Qed.
Lemma lem4458715 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4458716 {A B K : Type'} (x : K -> A) (f : type1514 A B K) (k : K -> Prop) (x' : K) (h1 : (k x') = False) : (term285 A B K f k x x') = (term428 A B K f x').
Proof. exact (MK_COMB (@lem4458715 B) (@lem4458714 A B K x f k x' h1)). Qed.
Lemma lem4458717 {B K : Type'} (x : K -> B) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4458718 {A B K : Type'} (x : K -> A) (f : type1514 A B K) (x' : K -> B) (k : K -> Prop) (x'' : K) (h1 : (k x'') = False) : ((term279 A B K f k x x'') = (x' x'')) = ((f x'' (@ARB A)) = (x' x'')).
Proof. exact (MK_COMB (@lem4458716 A B K x f k x'' h1) (@lem4458717 B K x' x'')). Qed.
Lemma lem4458721 {A B K : Type'} (x : K -> A) (f : type1514 A B K) (x' : K -> B) (k : K -> Prop) (x'' : K) (h1 : (k x'') = False) : (term286 A B K f k x x' x'') = (term429 A B K f x' x'').
Proof. exact (MK_COMB (@lem4458699 K k x'' h1) (@lem4458718 A B K x f x' k x'' h1)). Qed.
Lemma lem4458723 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4458724 {A B K : Type'} (f : type1514 A B K) (x : K -> B) (x' : K) : (term429 A B K f x x') = True.
Proof. exact (@lem4458723 ((f x' (@ARB A)) = (x x'))). Qed.
Lemma lem4458725 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K -> B) (k : K -> Prop) (x'' : K) (h1 : (k x'') = False) : (term286 A B K f k x x' x'') = True.
Proof. exact (TRANS (@lem4458721 A B K x f x' k x'' h1) (@lem4458724 A B K f x' x'')). Qed.
Lemma lem4458726 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K -> B) (x'' : K) : term430 A B K f k x x' x''.
Proof. exact (fun h0 : (k x'') = False => @lem4458725 A B K f x x' k x'' h0). Qed.
Lemma lem4458728 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (k x) = True.
Proof. exact (h1). Qed.
Lemma lem4458729 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4458730 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term264 K k x) = (imp True).
Proof. exact (MK_COMB (@lem4458729) (@lem4458728 K k x h1)). Qed.
Lemma lem4458732 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (k x) = True.
Proof. exact (h1). Qed.
Lemma lem4458733 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4458734 {A K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term275 A K k x) = (@COND A True).
Proof. exact (MK_COMB (@lem4458733 A) (@lem4458732 K k x h1)). Qed.
Lemma lem4458735 {A K : Type'} (x : K -> A) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4458736 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = True) : (term277 A K k x x') = (term431 A K x x').
Proof. exact (MK_COMB (@lem4458734 A K k x' h1) (@lem4458735 A K x x')). Qed.
Lemma lem4458737 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4458738 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = True) : (term278 A K k x x') = (term432 A K x x').
Proof. exact (MK_COMB (@lem4458736 A K x k x' h1) (@lem4458737 A)). Qed.
Lemma lem4458740 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4458741 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4458740 A t2 t1). Qed.
Lemma lem4458742 {A K : Type'} (x : K -> A) (x' : K) : (term432 A K x x') = (x x').
Proof. exact (@lem4458741 A (@ARB A) (x x')). Qed.
Lemma lem4458743 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = True) : (term278 A K k x x') = (x x').
Proof. exact (TRANS (@lem4458738 A K x k x' h1) (@lem4458742 A K x x')). Qed.
Lemma lem4458744 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4458745 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = True) : (term279 A B K f k x x') = (term433 A B K f x x').
Proof. exact (MK_COMB (@lem4458744 A B K f x') (@lem4458743 A K x k x' h1)). Qed.
Lemma lem4458746 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4458747 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = True) : (term285 A B K f k x x') = (term434 A B K f x x').
Proof. exact (MK_COMB (@lem4458746 B) (@lem4458745 A B K f x k x' h1)). Qed.
Lemma lem4458748 {B K : Type'} (x : K -> B) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4458749 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K -> B) (k : K -> Prop) (x'' : K) (h1 : (k x'') = True) : ((term279 A B K f k x x'') = (x' x'')) = ((term433 A B K f x x'') = (x' x'')).
Proof. exact (MK_COMB (@lem4458747 A B K f x k x'' h1) (@lem4458748 B K x' x'')). Qed.
Lemma lem4458752 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K -> B) (k : K -> Prop) (x'' : K) (h1 : (k x'') = True) : (term286 A B K f k x x' x'') = (term435 A B K f x x' x'').
Proof. exact (MK_COMB (@lem4458730 K k x'' h1) (@lem4458749 A B K f x x' k x'' h1)). Qed.
Lemma lem4458754 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4458755 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term435 A B K f x x' x'') = ((term433 A B K f x x'') = (x' x'')).
Proof. exact (@lem4458754 ((term433 A B K f x x'') = (x' x''))). Qed.
Lemma lem4458758 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K -> B) (k : K -> Prop) (x'' : K) (h1 : (k x'') = True) : (term286 A B K f k x x' x'') = ((term433 A B K f x x'') = (x' x'')).
Proof. exact (TRANS (@lem4458752 A B K f x x' k x'' h1) (@lem4458755 A B K f x x' x'')). Qed.
Lemma lem4458759 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : term436 A B K k f x x' x''.
Proof. exact (fun h0 : (k x'') = True => @lem4458758 A B K f x x' k x'' h0). Qed.
Lemma lem4458760 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : term437 A B K k f x x' x''.
Proof. exact (conj (@lem4458726 A B K f k x x' x'') (@lem4458759 A B K k f x x' x'')). Qed.
Lemma lem4458762 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term438 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4458763 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K -> B) (k : K -> Prop) (x'' : K) : term439 A B K f x x' k x''.
Proof. exact (@lem4458762 (term286 A B K f k x x' x'') ((term433 A B K f x x'') = (x' x'')) (k x'') True). Qed.
Lemma lem4458764 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K -> B) (k : K -> Prop) (x'' : K) : (term286 A B K f k x x' x'') = (term440 A B K f x x' k x'').
Proof. exact (@lem4458763 A B K f x x' k x'' (@lem4458760 A B K k f x x' x'')). Qed.
Lemma lem4458766 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4458767 {K : Type'} (k : K -> Prop) (x : K) : (term441 K k x) = True.
Proof. exact (@lem4458766 (k x)). Qed.
Lemma lem4458772 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term442 A B K k f x x' x'') = (term442 A B K k f x x' x'').
Proof. exact (eq_refl (term442 A B K k f x x' x'')). Qed.
Lemma lem4458773 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term440 A B K f x x' k x'') = (term443 A B K k f x x' x'').
Proof. exact (MK_COMB (@lem4458772 A B K k f x x' x'') (@lem4458767 K k x'')). Qed.
Lemma lem4458775 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4458776 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term443 A B K k f x x' x'') = (term444 A B K k f x x' x'').
Proof. exact (@lem4458775 (term444 A B K k f x x' x'')). Qed.
Lemma lem4458777 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term440 A B K f x x' k x'') = (term444 A B K k f x x' x'').
Proof. exact (TRANS (@lem4458773 A B K k f x x' x'') (@lem4458776 A B K k f x x' x'')). Qed.
Lemma lem4458788 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term286 A B K f k x x' x'') = (term444 A B K k f x x' x'').
Proof. exact (TRANS (@lem4458764 A B K f x x' k x'') (@lem4458777 A B K k f x x' x'')). Qed.
Lemma lem4458789 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) : (term287 A B K f k x x') = (term445 A B K k f x x').
Proof. exact (fun_ext (fun x'' : K => @lem4458788 A B K k f x x' x'')). Qed.
Lemma lem4458790 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4458791 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) : (term288 A B K f k x x') = (term446 A B K k f x x').
Proof. exact (MK_COMB (@lem4458790 K) (@lem4458789 A B K k f x x')). Qed.
Lemma lem4458792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4458793 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) : (term289 A B K f k x x') = (term447 A B K k f x x').
Proof. exact (MK_COMB (@lem4458792) (@lem4458791 A B K k f x x')). Qed.
Lemma lem4458794 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term300 A B K x k x' f s) = (term448 A B K x k x' f s).
Proof. exact (MK_COMB (@lem4458793 A B K k f x x') (@lem4458693 A B K k x' f s)). Qed.
Lemma lem4458795 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term301 A B K x k f s) = (term449 A B K x k f s).
Proof. exact (fun_ext (fun x' : K -> B => @lem4458794 A B K x k x' f s)). Qed.
Lemma lem4458796 {B K : Type'} : (@ex (K -> B)) = (@ex (K -> B)).
Proof. exact (eq_refl (@ex (K -> B))). Qed.
Lemma lem4458797 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term302 A B K x k f s) = (term450 A B K x k f s).
Proof. exact (MK_COMB (@lem4458796 B K) (@lem4458795 A B K x k f s)). Qed.
Lemma lem4458798 {A B K : Type'} (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (g = (term342 A B K _51538 f k x)) = (g = (term342 A B K _51538 f k x)).
Proof. exact (eq_refl (g = (term342 A B K _51538 f k x))). Qed.
Lemma lem4458803 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term268 A K k s x i) = (term268 A K k s x i).
Proof. exact (eq_refl (term268 A K k s x i)). Qed.
Lemma lem4458804 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term270 A K k s x) = (term270 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4458803 A K k s x i)). Qed.
Lemma lem4458805 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4458806 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term271 A K k s x) = (term271 A K k s x).
Proof. exact (MK_COMB (@lem4458805 K) (@lem4458804 A K k s x)). Qed.
Lemma lem4458807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4458808 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term273 A K k s x) = (term273 A K k s x).
Proof. exact (MK_COMB (@lem4458807) (@lem4458806 A K k s x)). Qed.
Lemma lem4458809 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term343 A B K s g _51538 f k x) = (term343 A B K s g _51538 f k x).
Proof. exact (MK_COMB (@lem4458808 A K k s x) (@lem4458798 A B K g _51538 f k x)). Qed.
Lemma lem4458810 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4458811 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term344 A B K s g _51538 f k x) = (term344 A B K s g _51538 f k x).
Proof. exact (MK_COMB (@lem4458810) (@lem4458809 A B K s g _51538 f k x)). Qed.
Lemma lem4458812 {A B K : Type'} (g : K -> B) (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term345 A B K g _51538 x k f s) = (term451 A B K g _51538 x k f s).
Proof. exact (MK_COMB (@lem4458811 A B K s g _51538 f k x) (@lem4458797 A B K x k f s)). Qed.
Lemma lem4458813 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term346 A B K _51538 x k f s) = (term452 A B K _51538 x k f s).
Proof. exact (fun_ext (fun g : K -> B => @lem4458812 A B K g _51538 x k f s)). Qed.
Lemma lem4458814 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4458815 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term347 A B K _51538 x k f s) = (term453 A B K _51538 x k f s).
Proof. exact (MK_COMB (@lem4458814 B K) (@lem4458813 A B K _51538 x k f s)). Qed.
Lemma lem4458816 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term348 A B K _51538 k f s) = (term454 A B K _51538 k f s).
Proof. exact (fun_ext (fun x : K -> A => @lem4458815 A B K _51538 x k f s)). Qed.
Lemma lem4458817 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4458818 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term349 A B K _51538 k f s) = (term455 A B K _51538 k f s).
Proof. exact (MK_COMB (@lem4458817 A K) (@lem4458816 A B K _51538 k f s)). Qed.
Lemma lem4458819 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (s : type1470 A K) : (term350 A B K _51538 f s) = (term456 A B K _51538 f s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4458818 A B K _51538 k f s)). Qed.
Lemma lem4458820 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4458821 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (s : type1470 A K) : (term351 A B K _51538 f s) = (term457 A B K _51538 f s).
Proof. exact (MK_COMB (@lem4458820 K) (@lem4458819 A B K _51538 f s)). Qed.
Lemma lem4458822 {A B K : Type'} (_51538 : type868 A B K) (s : type1470 A K) : (term352 A B K _51538 s) = (term458 A B K _51538 s).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4458821 A B K _51538 f s)). Qed.
Lemma lem4458823 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4458824 {A B K : Type'} (_51538 : type868 A B K) (s : type1470 A K) : (term353 A B K _51538 s) = (term459 A B K _51538 s).
Proof. exact (MK_COMB (@lem4458823 A B K) (@lem4458822 A B K _51538 s)). Qed.
Lemma lem4458825 {A B K : Type'} (_51538 : type868 A B K) : (term354 A B K _51538) = (term460 A B K _51538).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4458824 A B K _51538 s)). Qed.
Lemma lem4458826 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4458827 {A B K : Type'} (_51538 : type868 A B K) : (term355 A B K _51538) = (term461 A B K _51538).
Proof. exact (MK_COMB (@lem4458826 A K) (@lem4458825 A B K _51538)). Qed.
Lemma lem4458831 {K : Type'} (k : K -> Prop) (i : K) (h1 : (k i) = False) : (k i) = False.
Proof. exact (h1). Qed.
Lemma lem4458832 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4458833 {A K : Type'} (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term275 A K k i) = (@COND A False).
Proof. exact (MK_COMB (@lem4458832 A) (@lem4458831 K k i h1)). Qed.
Lemma lem4458834 {A K : Type'} (x : K -> A) (i : K) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem4458835 {A K : Type'} (x : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term277 A K k x i) = (term426 A K x i).
Proof. exact (MK_COMB (@lem4458833 A K k i h1) (@lem4458834 A K x i)). Qed.
Lemma lem4458836 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4458837 {A K : Type'} (x : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term278 A K k x i) = (term427 A K x i).
Proof. exact (MK_COMB (@lem4458835 A K x k i h1) (@lem4458836 A)). Qed.
Lemma lem4458839 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4458840 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4458839 A t1 t2). Qed.
Lemma lem4458841 {A K : Type'} (x : K -> A) (i : K) : (term427 A K x i) = (@ARB A).
Proof. exact (@lem4458840 A (x i) (@ARB A)). Qed.
Lemma lem4458842 {A K : Type'} (x : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term278 A K k x i) = (@ARB A).
Proof. exact (TRANS (@lem4458837 A K x k i h1) (@lem4458841 A K x i)). Qed.
Lemma lem4458843 {A B K : Type'} (f : type1514 A B K) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4458844 {A B K : Type'} (x : K -> A) (f : type1514 A B K) (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term279 A B K f k x i) = (f i (@ARB A)).
Proof. exact (MK_COMB (@lem4458843 A B K f i) (@lem4458842 A K x k i h1)). Qed.
Lemma lem4458845 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term412 A B K _51538 f k x i) = (term412 A B K _51538 f k x i).
Proof. exact (eq_refl (term412 A B K _51538 f k x i)). Qed.
Lemma lem4458846 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (f : type1514 A B K) (k : K -> Prop) (i : K) (h1 : (k i) = False) : ((_51538 f k x i) = (term279 A B K f k x i)) = ((_51538 f k x i) = (f i (@ARB A))).
Proof. exact (MK_COMB (@lem4458845 A B K _51538 f k x i) (@lem4458844 A B K x f k i h1)). Qed.
Lemma lem4458849 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (i : K) : term462 A B K _51538 k x f i.
Proof. exact (fun h0 : (k i) = False => @lem4458846 A B K _51538 x f k i h0). Qed.
Lemma lem4458851 {K : Type'} (k : K -> Prop) (i : K) (h1 : (k i) = True) : (k i) = True.
Proof. exact (h1). Qed.
Lemma lem4458852 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4458853 {A K : Type'} (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term275 A K k i) = (@COND A True).
Proof. exact (MK_COMB (@lem4458852 A) (@lem4458851 K k i h1)). Qed.
Lemma lem4458854 {A K : Type'} (x : K -> A) (i : K) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem4458855 {A K : Type'} (x : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term277 A K k x i) = (term431 A K x i).
Proof. exact (MK_COMB (@lem4458853 A K k i h1) (@lem4458854 A K x i)). Qed.
Lemma lem4458856 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4458857 {A K : Type'} (x : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term278 A K k x i) = (term432 A K x i).
Proof. exact (MK_COMB (@lem4458855 A K x k i h1) (@lem4458856 A)). Qed.
Lemma lem4458859 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4458860 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4458859 A t2 t1). Qed.
Lemma lem4458861 {A K : Type'} (x : K -> A) (i : K) : (term432 A K x i) = (x i).
Proof. exact (@lem4458860 A (@ARB A) (x i)). Qed.
Lemma lem4458862 {A K : Type'} (x : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term278 A K k x i) = (x i).
Proof. exact (TRANS (@lem4458857 A K x k i h1) (@lem4458861 A K x i)). Qed.
Lemma lem4458863 {A B K : Type'} (f : type1514 A B K) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4458864 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term279 A B K f k x i) = (term433 A B K f x i).
Proof. exact (MK_COMB (@lem4458863 A B K f i) (@lem4458862 A K x k i h1)). Qed.
Lemma lem4458865 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term412 A B K _51538 f k x i) = (term412 A B K _51538 f k x i).
Proof. exact (eq_refl (term412 A B K _51538 f k x i)). Qed.
Lemma lem4458866 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (x : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = True) : ((_51538 f k x i) = (term279 A B K f k x i)) = ((_51538 f k x i) = (term433 A B K f x i)).
Proof. exact (MK_COMB (@lem4458865 A B K _51538 f k x i) (@lem4458864 A B K f x k i h1)). Qed.
Lemma lem4458869 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : K) : term463 A B K _51538 k f x i.
Proof. exact (fun h0 : (k i) = True => @lem4458866 A B K _51538 f x k i h0). Qed.
Lemma lem4458870 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : K) : term464 A B K _51538 k f x i.
Proof. exact (conj (@lem4458849 A B K _51538 k x f i) (@lem4458869 A B K _51538 k f x i)). Qed.
Lemma lem4458872 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term438 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4458873 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (i : K) : term465 A B K _51538 k x f i.
Proof. exact (@lem4458872 ((_51538 f k x i) = (term279 A B K f k x i)) ((_51538 f k x i) = (term433 A B K f x i)) (k i) ((_51538 f k x i) = (f i (@ARB A)))). Qed.
Lemma lem4458906 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (i : K) : ((_51538 f k x i) = (term279 A B K f k x i)) = (term466 A B K _51538 k x f i).
Proof. exact (@lem4458873 A B K _51538 k x f i (@lem4458870 A B K _51538 k f x i)). Qed.
Lemma lem4458907 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term414 A B K _51538 f k x) = (term467 A B K _51538 k x f).
Proof. exact (fun_ext (fun i : K => @lem4458906 A B K _51538 k x f i)). Qed.
Lemma lem4458908 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4458909 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term415 A B K _51538 f k x) = (term468 A B K _51538 k x f).
Proof. exact (MK_COMB (@lem4458908 K) (@lem4458907 A B K _51538 k x f)). Qed.
Lemma lem4458910 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term416 A B K _51538 f k) = (term469 A B K _51538 k f).
Proof. exact (fun_ext (fun x : K -> A => @lem4458909 A B K _51538 k x f)). Qed.
Lemma lem4458911 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4458912 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term417 A B K _51538 f k) = (term470 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4458911 A K) (@lem4458910 A B K _51538 k f)). Qed.
Lemma lem4458913 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term418 A B K _51538 f) = (term471 A B K _51538 f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4458912 A B K _51538 k f)). Qed.
Lemma lem4458914 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4458915 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term419 A B K _51538 f) = (term472 A B K _51538 f).
Proof. exact (MK_COMB (@lem4458914 K) (@lem4458913 A B K _51538 f)). Qed.
Lemma lem4458916 {A B K : Type'} (_51538 : type868 A B K) : (term420 A B K _51538) = (term473 A B K _51538).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4458915 A B K _51538 f)). Qed.
Lemma lem4458917 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4458918 {A B K : Type'} (_51538 : type868 A B K) : (term421 A B K _51538) = (term474 A B K _51538).
Proof. exact (MK_COMB (@lem4458917 A B K) (@lem4458916 A B K _51538)). Qed.
Lemma lem4458919 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4458920 {A B K : Type'} (_51538 : type868 A B K) : (term422 A B K _51538) = (term475 A B K _51538).
Proof. exact (MK_COMB (@lem4458919) (@lem4458918 A B K _51538)). Qed.
Lemma lem4458921 {A B K : Type'} (_51538 : type868 A B K) : (term423 A B K _51538) = (term476 A B K _51538).
Proof. exact (MK_COMB (@lem4458920 A B K _51538) (@lem4458827 A B K _51538)). Qed.
Lemma lem4458922 {A B K : Type'} : (term424 A B K) = (term477 A B K).
Proof. exact (fun_ext (fun _51538 : type868 A B K => @lem4458921 A B K _51538)). Qed.
Lemma lem4458923 {A B K : Type'} : (@all ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B)) = (@all ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B)).
Proof. exact (eq_refl (@all ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B))). Qed.
Lemma lem4458924 {A B K : Type'} : (term425 A B K) = (term478 A B K).
Proof. exact (MK_COMB (@lem4458923 A B K) (@lem4458922 A B K)). Qed.
Lemma lem4459039 {A B K : Type'} : (term331 A B K) = (term478 A B K).
Proof. exact (TRANS (@lem4458678 A B K) (@lem4458924 A B K)). Qed.
Lemma lem4459040 {A B K : Type'} : (term478 A B K) = (term331 A B K).
Proof. exact (SYM (@lem4459039 A B K)). Qed.
Lemma lem4459041 {A B K : Type'} (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term474 A B K _51538.
Proof. exact (h1). Qed.
Lemma lem4459042 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term343 A B K s g _51538 f k x) : term343 A B K s g _51538 f k x.
Proof. exact (h1). Qed.
Lemma lem4459044 (p : Prop) : p = (term305 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4459045 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term450 A B K x k f s) = (term479 A B K x k f s).
Proof. exact (@lem4459044 (term450 A B K x k f s)). Qed.
Lemma lem4459046 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term479 A B K x k f s) = (term450 A B K x k f s).
Proof. exact (SYM (@lem4459045 A B K x k f s)). Qed.
Lemma lem4459047 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term480 A B K x k f s) : term480 A B K x k f s.
Proof. exact (h1). Qed.
Lemma lem4459060 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (i : K) : (term466 A B K _51538 k x f i) = (term466 A B K _51538 k x f i).
Proof. exact (eq_refl (term466 A B K _51538 k x f i)). Qed.
Lemma lem4459061 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term467 A B K _51538 k x f) = (term467 A B K _51538 k x f).
Proof. exact (fun_ext (fun i : K => @lem4459060 A B K _51538 k x f i)). Qed.
Lemma lem4459062 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4459063 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term468 A B K _51538 k x f) = (term468 A B K _51538 k x f).
Proof. exact (MK_COMB (@lem4459062 K) (@lem4459061 A B K _51538 k x f)). Qed.
Lemma lem4459064 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term469 A B K _51538 k f) = (term469 A B K _51538 k f).
Proof. exact (fun_ext (fun x : K -> A => @lem4459063 A B K _51538 k x f)). Qed.
Lemma lem4459065 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4459066 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term470 A B K _51538 k f) = (term470 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4459065 A K) (@lem4459064 A B K _51538 k f)). Qed.
Lemma lem4459067 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term471 A B K _51538 f) = (term471 A B K _51538 f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4459066 A B K _51538 k f)). Qed.
Lemma lem4459068 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4459069 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term472 A B K _51538 f) = (term472 A B K _51538 f).
Proof. exact (MK_COMB (@lem4459068 K) (@lem4459067 A B K _51538 f)). Qed.
Lemma lem4459070 {A B K : Type'} (_51538 : type868 A B K) : (term473 A B K _51538) = (term473 A B K _51538).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4459069 A B K _51538 f)). Qed.
Lemma lem4459071 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4459072 {A B K : Type'} (_51538 : type868 A B K) : (term474 A B K _51538) = (term474 A B K _51538).
Proof. exact (MK_COMB (@lem4459071 A B K) (@lem4459070 A B K _51538)). Qed.
Lemma lem4459086 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term481 A P Q) = (term482 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4459087 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term481 K P Q) = (term482 K P Q).
Proof. exact (@lem4459086 K P Q). Qed.
Lemma lem4459088 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term483 A B K _51538 k x f) = (term484 A B K _51538 k x f).
Proof. exact (@lem4459087 K (term485 A B K _51538 k f x) (term486 A B K _51538 k x f)). Qed.
Lemma lem4459089 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : K) : (term487 A B K _51538 k f x i) = (term488 A B K _51538 k f x i).
Proof. exact (eq_refl (term487 A B K _51538 k f x i)). Qed.
Lemma lem4459090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4459091 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : K) : (term489 A B K _51538 k f x i) = (term490 A B K _51538 k f x i).
Proof. exact (MK_COMB (@lem4459090) (@lem4459089 A B K _51538 k f x i)). Qed.
Lemma lem4459092 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (i : K) : (term491 A B K _51538 k x f i) = (term492 A B K _51538 k x f i).
Proof. exact (eq_refl (term491 A B K _51538 k x f i)). Qed.
Lemma lem4459093 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (i : K) : (term493 A B K _51538 k x f i) = (term466 A B K _51538 k x f i).
Proof. exact (MK_COMB (@lem4459091 A B K _51538 k f x i) (@lem4459092 A B K _51538 k x f i)). Qed.
Lemma lem4459094 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term494 A B K _51538 k x f) = (term467 A B K _51538 k x f).
Proof. exact (fun_ext (fun i : K => @lem4459093 A B K _51538 k x f i)). Qed.
Lemma lem4459095 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4459096 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term483 A B K _51538 k x f) = (term468 A B K _51538 k x f).
Proof. exact (MK_COMB (@lem4459095 K) (@lem4459094 A B K _51538 k x f)). Qed.
Lemma lem4459097 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4459098 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term495 A B K _51538 k x f) = (term496 A B K _51538 k x f).
Proof. exact (MK_COMB (@lem4459097) (@lem4459096 A B K _51538 k x f)). Qed.
Lemma lem4459099 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : K) : (term487 A B K _51538 k f x i) = (term488 A B K _51538 k f x i).
Proof. exact (eq_refl (term487 A B K _51538 k f x i)). Qed.
Lemma lem4459100 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term497 A B K _51538 k f x) = (term485 A B K _51538 k f x).
Proof. exact (fun_ext (fun i : K => @lem4459099 A B K _51538 k f x i)). Qed.
Lemma lem4459101 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4459102 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term498 A B K _51538 k f x) = (term499 A B K _51538 k f x).
Proof. exact (MK_COMB (@lem4459101 K) (@lem4459100 A B K _51538 k f x)). Qed.
Lemma lem4459103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4459104 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term500 A B K _51538 k f x) = (term501 A B K _51538 k f x).
Proof. exact (MK_COMB (@lem4459103) (@lem4459102 A B K _51538 k f x)). Qed.
Lemma lem4459105 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (i : K) : (term491 A B K _51538 k x f i) = (term492 A B K _51538 k x f i).
Proof. exact (eq_refl (term491 A B K _51538 k x f i)). Qed.
Lemma lem4459106 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term502 A B K _51538 k x f) = (term486 A B K _51538 k x f).
Proof. exact (fun_ext (fun i : K => @lem4459105 A B K _51538 k x f i)). Qed.
Lemma lem4459107 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4459108 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term503 A B K _51538 k x f) = (term504 A B K _51538 k x f).
Proof. exact (MK_COMB (@lem4459107 K) (@lem4459106 A B K _51538 k x f)). Qed.
Lemma lem4459109 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term484 A B K _51538 k x f) = (term505 A B K _51538 k x f).
Proof. exact (MK_COMB (@lem4459104 A B K _51538 k f x) (@lem4459108 A B K _51538 k x f)). Qed.
Lemma lem4459110 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : ((term483 A B K _51538 k x f) = (term484 A B K _51538 k x f)) = ((term468 A B K _51538 k x f) = (term505 A B K _51538 k x f)).
Proof. exact (MK_COMB (@lem4459098 A B K _51538 k x f) (@lem4459109 A B K _51538 k x f)). Qed.
Lemma lem4459111 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term468 A B K _51538 k x f) = (term505 A B K _51538 k x f).
Proof. exact (EQ_MP (@lem4459110 A B K _51538 k x f) (@lem4459088 A B K _51538 k x f)). Qed.
Lemma lem4459188 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term469 A B K _51538 k f) = (term506 A B K _51538 k f).
Proof. exact (fun_ext (fun x : K -> A => @lem4459111 A B K _51538 k x f)). Qed.
Lemma lem4459189 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4459190 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term470 A B K _51538 k f) = (term507 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4459189 A K) (@lem4459188 A B K _51538 k f)). Qed.
Lemma lem4459192 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term481 A P Q) = (term482 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4459193 {A K : Type'} (P : type805 A K) (Q : type805 A K) : (term508 A K P Q) = (term509 A K P Q).
Proof. exact (@lem4459192 (K -> A) P Q). Qed.
Lemma lem4459194 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term510 A B K _51538 k f) = (term511 A B K _51538 k f).
Proof. exact (@lem4459193 A K (term512 A B K _51538 k f) (term513 A B K _51538 k f)). Qed.
Lemma lem4459195 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term514 A B K _51538 k f x) = (term499 A B K _51538 k f x).
Proof. exact (eq_refl (term514 A B K _51538 k f x)). Qed.
Lemma lem4459196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4459197 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term515 A B K _51538 k f x) = (term501 A B K _51538 k f x).
Proof. exact (MK_COMB (@lem4459196) (@lem4459195 A B K _51538 k f x)). Qed.
Lemma lem4459198 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term516 A B K _51538 k f x) = (term504 A B K _51538 k x f).
Proof. exact (eq_refl (term516 A B K _51538 k f x)). Qed.
Lemma lem4459199 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term517 A B K _51538 k f x) = (term505 A B K _51538 k x f).
Proof. exact (MK_COMB (@lem4459197 A B K _51538 k f x) (@lem4459198 A B K _51538 k x f)). Qed.
Lemma lem4459200 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term518 A B K _51538 k f) = (term506 A B K _51538 k f).
Proof. exact (fun_ext (fun x : K -> A => @lem4459199 A B K _51538 k x f)). Qed.
Lemma lem4459201 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4459202 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term510 A B K _51538 k f) = (term507 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4459201 A K) (@lem4459200 A B K _51538 k f)). Qed.
Lemma lem4459203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4459204 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term519 A B K _51538 k f) = (term520 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4459203) (@lem4459202 A B K _51538 k f)). Qed.
Lemma lem4459205 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term514 A B K _51538 k f x) = (term499 A B K _51538 k f x).
Proof. exact (eq_refl (term514 A B K _51538 k f x)). Qed.
Lemma lem4459206 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term521 A B K _51538 k f) = (term512 A B K _51538 k f).
Proof. exact (fun_ext (fun x : K -> A => @lem4459205 A B K _51538 k f x)). Qed.
Lemma lem4459207 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4459208 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term522 A B K _51538 k f) = (term523 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4459207 A K) (@lem4459206 A B K _51538 k f)). Qed.
Lemma lem4459209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4459210 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term524 A B K _51538 k f) = (term525 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4459209) (@lem4459208 A B K _51538 k f)). Qed.
Lemma lem4459211 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term516 A B K _51538 k f x) = (term504 A B K _51538 k x f).
Proof. exact (eq_refl (term516 A B K _51538 k f x)). Qed.
Lemma lem4459212 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term526 A B K _51538 k f) = (term513 A B K _51538 k f).
Proof. exact (fun_ext (fun x : K -> A => @lem4459211 A B K _51538 k x f)). Qed.
Lemma lem4459213 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4459214 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term527 A B K _51538 k f) = (term528 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4459213 A K) (@lem4459212 A B K _51538 k f)). Qed.
Lemma lem4459215 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term511 A B K _51538 k f) = (term529 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4459210 A B K _51538 k f) (@lem4459214 A B K _51538 k f)). Qed.
Lemma lem4459216 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : ((term510 A B K _51538 k f) = (term511 A B K _51538 k f)) = ((term507 A B K _51538 k f) = (term529 A B K _51538 k f)).
Proof. exact (MK_COMB (@lem4459204 A B K _51538 k f) (@lem4459215 A B K _51538 k f)). Qed.
Lemma lem4459217 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term507 A B K _51538 k f) = (term529 A B K _51538 k f).
Proof. exact (EQ_MP (@lem4459216 A B K _51538 k f) (@lem4459194 A B K _51538 k f)). Qed.
Lemma lem4459302 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term470 A B K _51538 k f) = (term529 A B K _51538 k f).
Proof. exact (TRANS (@lem4459190 A B K _51538 k f) (@lem4459217 A B K _51538 k f)). Qed.
Lemma lem4459303 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term471 A B K _51538 f) = (term530 A B K _51538 f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4459302 A B K _51538 k f)). Qed.
Lemma lem4459304 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4459305 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term472 A B K _51538 f) = (term531 A B K _51538 f).
Proof. exact (MK_COMB (@lem4459304 K) (@lem4459303 A B K _51538 f)). Qed.
Lemma lem4459307 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term481 A P Q) = (term482 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4459308 {K : Type'} (P : type686 K) (Q : type686 K) : (term532 K P Q) = (term533 K P Q).
Proof. exact (@lem4459307 (K -> Prop) P Q). Qed.
Lemma lem4459309 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term534 A B K _51538 f) = (term535 A B K _51538 f).
Proof. exact (@lem4459308 K (term536 A B K _51538 f) (term537 A B K _51538 f)). Qed.
Lemma lem4459310 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term538 A B K _51538 f k) = (term523 A B K _51538 k f).
Proof. exact (eq_refl (term538 A B K _51538 f k)). Qed.
Lemma lem4459311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4459312 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term539 A B K _51538 f k) = (term525 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4459311) (@lem4459310 A B K _51538 k f)). Qed.
Lemma lem4459313 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term540 A B K _51538 f k) = (term528 A B K _51538 k f).
Proof. exact (eq_refl (term540 A B K _51538 f k)). Qed.
Lemma lem4459314 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term541 A B K _51538 f k) = (term529 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4459312 A B K _51538 k f) (@lem4459313 A B K _51538 k f)). Qed.
Lemma lem4459315 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term542 A B K _51538 f) = (term530 A B K _51538 f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4459314 A B K _51538 k f)). Qed.
Lemma lem4459316 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4459317 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term534 A B K _51538 f) = (term531 A B K _51538 f).
Proof. exact (MK_COMB (@lem4459316 K) (@lem4459315 A B K _51538 f)). Qed.
Lemma lem4459318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4459319 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term543 A B K _51538 f) = (term544 A B K _51538 f).
Proof. exact (MK_COMB (@lem4459318) (@lem4459317 A B K _51538 f)). Qed.
Lemma lem4459320 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term538 A B K _51538 f k) = (term523 A B K _51538 k f).
Proof. exact (eq_refl (term538 A B K _51538 f k)). Qed.
Lemma lem4459321 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term545 A B K _51538 f) = (term536 A B K _51538 f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4459320 A B K _51538 k f)). Qed.
Lemma lem4459322 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4459323 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term546 A B K _51538 f) = (term547 A B K _51538 f).
Proof. exact (MK_COMB (@lem4459322 K) (@lem4459321 A B K _51538 f)). Qed.
Lemma lem4459324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4459325 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term548 A B K _51538 f) = (term549 A B K _51538 f).
Proof. exact (MK_COMB (@lem4459324) (@lem4459323 A B K _51538 f)). Qed.
Lemma lem4459326 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term540 A B K _51538 f k) = (term528 A B K _51538 k f).
Proof. exact (eq_refl (term540 A B K _51538 f k)). Qed.
Lemma lem4459327 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term550 A B K _51538 f) = (term537 A B K _51538 f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4459326 A B K _51538 k f)). Qed.
Lemma lem4459328 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4459329 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term551 A B K _51538 f) = (term552 A B K _51538 f).
Proof. exact (MK_COMB (@lem4459328 K) (@lem4459327 A B K _51538 f)). Qed.
Lemma lem4459330 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term535 A B K _51538 f) = (term553 A B K _51538 f).
Proof. exact (MK_COMB (@lem4459325 A B K _51538 f) (@lem4459329 A B K _51538 f)). Qed.
Lemma lem4459331 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : ((term534 A B K _51538 f) = (term535 A B K _51538 f)) = ((term531 A B K _51538 f) = (term553 A B K _51538 f)).
Proof. exact (MK_COMB (@lem4459319 A B K _51538 f) (@lem4459330 A B K _51538 f)). Qed.
Lemma lem4459332 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term531 A B K _51538 f) = (term553 A B K _51538 f).
Proof. exact (EQ_MP (@lem4459331 A B K _51538 f) (@lem4459309 A B K _51538 f)). Qed.
Lemma lem4459425 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term472 A B K _51538 f) = (term553 A B K _51538 f).
Proof. exact (TRANS (@lem4459305 A B K _51538 f) (@lem4459332 A B K _51538 f)). Qed.
Lemma lem4459426 {A B K : Type'} (_51538 : type868 A B K) : (term473 A B K _51538) = (term554 A B K _51538).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4459425 A B K _51538 f)). Qed.
Lemma lem4459427 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4459428 {A B K : Type'} (_51538 : type868 A B K) : (term474 A B K _51538) = (term555 A B K _51538).
Proof. exact (MK_COMB (@lem4459427 A B K) (@lem4459426 A B K _51538)). Qed.
Lemma lem4459430 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term481 A P Q) = (term482 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4459431 {A B K : Type'} (P : type869 A B K) (Q : type869 A B K) : (term556 A B K P Q) = (term557 A B K P Q).
Proof. exact (@lem4459430 (type1514 A B K) P Q). Qed.
Lemma lem4459432 {A B K : Type'} (_51538 : type868 A B K) : (term558 A B K _51538) = (term559 A B K _51538).
Proof. exact (@lem4459431 A B K (term560 A B K _51538) (term561 A B K _51538)). Qed.
Lemma lem4459433 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term562 A B K _51538 f) = (term547 A B K _51538 f).
Proof. exact (eq_refl (term562 A B K _51538 f)). Qed.
Lemma lem4459434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4459435 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term563 A B K _51538 f) = (term549 A B K _51538 f).
Proof. exact (MK_COMB (@lem4459434) (@lem4459433 A B K _51538 f)). Qed.
Lemma lem4459436 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term564 A B K _51538 f) = (term552 A B K _51538 f).
Proof. exact (eq_refl (term564 A B K _51538 f)). Qed.
Lemma lem4459437 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term565 A B K _51538 f) = (term553 A B K _51538 f).
Proof. exact (MK_COMB (@lem4459435 A B K _51538 f) (@lem4459436 A B K _51538 f)). Qed.
Lemma lem4459438 {A B K : Type'} (_51538 : type868 A B K) : (term566 A B K _51538) = (term554 A B K _51538).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4459437 A B K _51538 f)). Qed.
Lemma lem4459439 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4459440 {A B K : Type'} (_51538 : type868 A B K) : (term558 A B K _51538) = (term555 A B K _51538).
Proof. exact (MK_COMB (@lem4459439 A B K) (@lem4459438 A B K _51538)). Qed.
Lemma lem4459441 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4459442 {A B K : Type'} (_51538 : type868 A B K) : (term567 A B K _51538) = (term568 A B K _51538).
Proof. exact (MK_COMB (@lem4459441) (@lem4459440 A B K _51538)). Qed.
Lemma lem4459443 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term562 A B K _51538 f) = (term547 A B K _51538 f).
Proof. exact (eq_refl (term562 A B K _51538 f)). Qed.
Lemma lem4459444 {A B K : Type'} (_51538 : type868 A B K) : (term569 A B K _51538) = (term560 A B K _51538).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4459443 A B K _51538 f)). Qed.
Lemma lem4459445 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4459446 {A B K : Type'} (_51538 : type868 A B K) : (term570 A B K _51538) = (term571 A B K _51538).
Proof. exact (MK_COMB (@lem4459445 A B K) (@lem4459444 A B K _51538)). Qed.
Lemma lem4459447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4459448 {A B K : Type'} (_51538 : type868 A B K) : (term572 A B K _51538) = (term573 A B K _51538).
Proof. exact (MK_COMB (@lem4459447) (@lem4459446 A B K _51538)). Qed.
Lemma lem4459449 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term564 A B K _51538 f) = (term552 A B K _51538 f).
Proof. exact (eq_refl (term564 A B K _51538 f)). Qed.
Lemma lem4459450 {A B K : Type'} (_51538 : type868 A B K) : (term574 A B K _51538) = (term561 A B K _51538).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4459449 A B K _51538 f)). Qed.
Lemma lem4459451 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4459452 {A B K : Type'} (_51538 : type868 A B K) : (term575 A B K _51538) = (term576 A B K _51538).
Proof. exact (MK_COMB (@lem4459451 A B K) (@lem4459450 A B K _51538)). Qed.
Lemma lem4459453 {A B K : Type'} (_51538 : type868 A B K) : (term559 A B K _51538) = (term577 A B K _51538).
Proof. exact (MK_COMB (@lem4459448 A B K _51538) (@lem4459452 A B K _51538)). Qed.
Lemma lem4459454 {A B K : Type'} (_51538 : type868 A B K) : ((term558 A B K _51538) = (term559 A B K _51538)) = ((term555 A B K _51538) = (term577 A B K _51538)).
Proof. exact (MK_COMB (@lem4459442 A B K _51538) (@lem4459453 A B K _51538)). Qed.
Lemma lem4459455 {A B K : Type'} (_51538 : type868 A B K) : (term555 A B K _51538) = (term577 A B K _51538).
Proof. exact (EQ_MP (@lem4459454 A B K _51538) (@lem4459432 A B K _51538)). Qed.
Lemma lem4459558 {A B K : Type'} (_51538 : type868 A B K) : (term474 A B K _51538) = (term577 A B K _51538).
Proof. exact (TRANS (@lem4459428 A B K _51538) (@lem4459455 A B K _51538)). Qed.
Lemma lem4459559 {A B K : Type'} (_51538 : type868 A B K) : (term474 A B K _51538) = (term577 A B K _51538).
Proof. exact (TRANS (@lem4459072 A B K _51538) (@lem4459558 A B K _51538)). Qed.
Lemma lem4459560 {A B K : Type'} (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term577 A B K _51538.
Proof. exact (EQ_MP (@lem4459559 A B K _51538) (@lem4459041 A B K _51538 h1)). Qed.
Lemma lem4459567 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term268 A K k s x i) = (term578 A K k s x i).
Proof. exact (@lem17265 (k i) (term266 A K s x i)). Qed.
Lemma lem4459568 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term270 A K k s x) = (term579 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4459567 A K k s x i)). Qed.
Lemma lem4459569 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4459570 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term271 A K k s x) = (term580 A K k s x).
Proof. exact (MK_COMB (@lem4459569 K) (@lem4459568 A K k s x)). Qed.
Lemma lem4459571 {A B K : Type'} (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (g = (term342 A B K _51538 f k x)) = (g = (term342 A B K _51538 f k x)).
Proof. exact (eq_refl (g = (term342 A B K _51538 f k x))). Qed.
Lemma lem4459572 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4459573 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term273 A K k s x) = (term581 A K k s x).
Proof. exact (MK_COMB (@lem4459572) (@lem4459570 A K k s x)). Qed.
Lemma lem4459626 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term343 A B K s g _51538 f k x) = (term582 A B K s g _51538 f k x).
Proof. exact (MK_COMB (@lem4459573 A K k s x) (@lem4459571 A B K g _51538 f k x)). Qed.
Lemma lem4459627 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term343 A B K s g _51538 f k x) : term582 A B K s g _51538 f k x.
Proof. exact (EQ_MP (@lem4459626 A B K s g _51538 f k x) (@lem4459042 A B K s g _51538 f k x h1)). Qed.
Lemma lem4459630 {K : Type'} (k : K -> Prop) (x : K) : (term583 K k x) = (k x).
Proof. exact (@lem16933 (k x)). Qed.
Lemma lem4459631 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term584 A B K f x x' x'') = (term584 A B K f x x' x'').
Proof. exact (eq_refl (term584 A B K f x x' x'')). Qed.
Lemma lem4459632 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4459633 {K : Type'} (k : K -> Prop) (x : K) : (term585 K k x) = (term586 K k x).
Proof. exact (MK_COMB (@lem4459632) (@lem4459630 K k x)). Qed.
Lemma lem4459634 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term587 A B K k f x x' x'') = (term588 A B K k f x x' x'').
Proof. exact (MK_COMB (@lem4459633 K k x'') (@lem4459631 A B K f x x' x'')). Qed.
Lemma lem4459635 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term589 A B K k f x x' x'') = (term587 A B K k f x x' x'').
Proof. exact (@lem17160 (term590 K k x'') ((term433 A B K f x x'') = (x' x''))). Qed.
Lemma lem4459636 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term589 A B K k f x x' x'') = (term588 A B K k f x x' x'').
Proof. exact (TRANS (@lem4459635 A B K k f x x' x'') (@lem4459634 A B K k f x x' x'')). Qed.
Lemma lem4459637 {K : Type'} (P : K -> Prop) : (term591 K P) = (term592 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4459638 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) : (term593 A B K k f x x') = (term594 A B K k f x x').
Proof. exact (@lem4459637 K (term445 A B K k f x x')). Qed.
Lemma lem4459639 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term595 A B K k f x x' x'') = (term444 A B K k f x x' x'').
Proof. exact (eq_refl (term595 A B K k f x x' x'')). Qed.
Lemma lem4459640 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4459641 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term596 A B K k f x x' x'') = (term589 A B K k f x x' x'').
Proof. exact (MK_COMB (@lem4459640) (@lem4459639 A B K k f x x' x'')). Qed.
Lemma lem4459642 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (x'' : K) : (term596 A B K k f x x' x'') = (term588 A B K k f x x' x'').
Proof. exact (TRANS (@lem4459641 A B K k f x x' x'') (@lem4459636 A B K k f x x' x'')). Qed.
Lemma lem4459643 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) : (term597 A B K k f x x') = (term598 A B K k f x x').
Proof. exact (fun_ext (fun x'' : K => @lem4459642 A B K k f x x' x'')). Qed.
Lemma lem4459644 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4459645 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) : (term594 A B K k f x x') = (term599 A B K k f x x').
Proof. exact (MK_COMB (@lem4459644 K) (@lem4459643 A B K k f x x')). Qed.
Lemma lem4459646 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) : (term593 A B K k f x x') = (term599 A B K k f x x').
Proof. exact (TRANS (@lem4459638 A B K k f x x') (@lem4459645 A B K k f x x')). Qed.
Lemma lem4459654 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term600 A B K x f s i x') = (term601 A B K x f s i x').
Proof. exact (@lem17045 ((x i) = (f i x')) (s i x')). Qed.
Lemma lem4459655 {A : Type'} (P : A -> Prop) : (term602 A P) = (term603 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4459656 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term604 A B K x f s i) = (term605 A B K x f s i).
Proof. exact (@lem4459655 A (term295 A B K x f s i)). Qed.
Lemma lem4459657 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term606 A B K x f s i x') = (term293 A B K x f s i x').
Proof. exact (eq_refl (term606 A B K x f s i x')). Qed.
Lemma lem4459658 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4459659 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term607 A B K x f s i x') = (term600 A B K x f s i x').
Proof. exact (MK_COMB (@lem4459658) (@lem4459657 A B K x f s i x')). Qed.
Lemma lem4459660 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term607 A B K x f s i x') = (term601 A B K x f s i x').
Proof. exact (TRANS (@lem4459659 A B K x f s i x') (@lem4459654 A B K x f s i x')). Qed.
Lemma lem4459661 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term608 A B K x f s i) = (term609 A B K x f s i).
Proof. exact (fun_ext (fun x' : A => @lem4459660 A B K x f s i x')). Qed.
Lemma lem4459662 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4459663 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term605 A B K x f s i) = (term610 A B K x f s i).
Proof. exact (MK_COMB (@lem4459662 A) (@lem4459661 A B K x f s i)). Qed.
Lemma lem4459664 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term604 A B K x f s i) = (term610 A B K x f s i).
Proof. exact (TRANS (@lem4459656 A B K x f s i) (@lem4459663 A B K x f s i)). Qed.
Lemma lem4459666 {K : Type'} (k : K -> Prop) (i : K) : (term586 K k i) = (term586 K k i).
Proof. exact (eq_refl (term586 K k i)). Qed.
Lemma lem4459667 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term611 A B K k x f s i) = (term612 A B K k x f s i).
Proof. exact (MK_COMB (@lem4459666 K k i) (@lem4459664 A B K x f s i)). Qed.
Lemma lem4459668 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term613 A B K k x f s i) = (term611 A B K k x f s i).
Proof. exact (@lem17362 (k i) (term296 A B K x f s i)). Qed.
Lemma lem4459669 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term613 A B K k x f s i) = (term612 A B K k x f s i).
Proof. exact (TRANS (@lem4459668 A B K k x f s i) (@lem4459667 A B K k x f s i)). Qed.
Lemma lem4459670 {K : Type'} (P : K -> Prop) : (term591 K P) = (term592 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4459671 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term614 A B K k x f s) = (term615 A B K k x f s).
Proof. exact (@lem4459670 K (term298 A B K k x f s)). Qed.
Lemma lem4459672 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term616 A B K k x f s i) = (term297 A B K k x f s i).
Proof. exact (eq_refl (term616 A B K k x f s i)). Qed.
Lemma lem4459673 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4459674 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term617 A B K k x f s i) = (term613 A B K k x f s i).
Proof. exact (MK_COMB (@lem4459673) (@lem4459672 A B K k x f s i)). Qed.
Lemma lem4459675 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term617 A B K k x f s i) = (term612 A B K k x f s i).
Proof. exact (TRANS (@lem4459674 A B K k x f s i) (@lem4459669 A B K k x f s i)). Qed.
Lemma lem4459676 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term618 A B K k x f s) = (term619 A B K k x f s).
Proof. exact (fun_ext (fun i : K => @lem4459675 A B K k x f s i)). Qed.
Lemma lem4459677 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4459678 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term615 A B K k x f s) = (term620 A B K k x f s).
Proof. exact (MK_COMB (@lem4459677 K) (@lem4459676 A B K k x f s)). Qed.
Lemma lem4459679 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term614 A B K k x f s) = (term620 A B K k x f s).
Proof. exact (TRANS (@lem4459671 A B K k x f s) (@lem4459678 A B K k x f s)). Qed.
Lemma lem4459680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4459681 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) : (term621 A B K k f x x') = (term622 A B K k f x x').
Proof. exact (MK_COMB (@lem4459680) (@lem4459646 A B K k f x x')). Qed.
Lemma lem4459682 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term623 A B K x k x' f s) = (term624 A B K x k x' f s).
Proof. exact (MK_COMB (@lem4459681 A B K k f x x') (@lem4459679 A B K k x' f s)). Qed.
Lemma lem4459683 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term625 A B K x k x' f s) = (term623 A B K x k x' f s).
Proof. exact (@lem17045 (term446 A B K k f x x') (term299 A B K k x' f s)). Qed.
Lemma lem4459684 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term625 A B K x k x' f s) = (term624 A B K x k x' f s).
Proof. exact (TRANS (@lem4459683 A B K x k x' f s) (@lem4459682 A B K x k x' f s)). Qed.
Lemma lem4459685 {B K : Type'} (P : type805 B K) : (term626 B K P) = (term627 B K P).
Proof. exact (@lem18394 (K -> B) P). Qed.
Lemma lem4459686 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term480 A B K x k f s) = (term628 A B K x k f s).
Proof. exact (@lem4459685 B K (term449 A B K x k f s)). Qed.
Lemma lem4459687 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term629 A B K x k f s x') = (term448 A B K x k x' f s).
Proof. exact (eq_refl (term629 A B K x k f s x')). Qed.
Lemma lem4459688 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4459689 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term630 A B K x k f s x') = (term625 A B K x k x' f s).
Proof. exact (MK_COMB (@lem4459688) (@lem4459687 A B K x k x' f s)). Qed.
Lemma lem4459690 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term630 A B K x k f s x') = (term624 A B K x k x' f s).
Proof. exact (TRANS (@lem4459689 A B K x k x' f s) (@lem4459684 A B K x k x' f s)). Qed.
Lemma lem4459691 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term631 A B K x k f s) = (term632 A B K x k f s).
Proof. exact (fun_ext (fun x' : K -> B => @lem4459690 A B K x k x' f s)). Qed.
Lemma lem4459692 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4459693 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term628 A B K x k f s) = (term633 A B K x k f s).
Proof. exact (MK_COMB (@lem4459692 B K) (@lem4459691 A B K x k f s)). Qed.
Lemma lem4459694 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term480 A B K x k f s) = (term633 A B K x k f s).
Proof. exact (TRANS (@lem4459686 A B K x k f s) (@lem4459693 A B K x k f s)). Qed.
Lemma lem4459849 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term634 A P Q) = (term635 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4459850 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term634 K P Q) = (term635 K P Q).
Proof. exact (@lem4459849 K P Q). Qed.
Lemma lem4459851 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term636 A B K x k x' f s) = (term637 A B K x k x' f s).
Proof. exact (@lem4459850 K (term598 A B K k f x x') (term619 A B K k x' f s)). Qed.
Lemma lem4459852 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (i : K) : (term638 A B K k f x x' i) = (term588 A B K k f x x' i).
Proof. exact (eq_refl (term638 A B K k f x x' i)). Qed.
Lemma lem4459853 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) : (term639 A B K k f x x') = (term598 A B K k f x x').
Proof. exact (fun_ext (fun i : K => @lem4459852 A B K k f x x' i)). Qed.
Lemma lem4459854 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4459855 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) : (term640 A B K k f x x') = (term599 A B K k f x x').
Proof. exact (MK_COMB (@lem4459854 K) (@lem4459853 A B K k f x x')). Qed.
Lemma lem4459856 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4459857 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) : (term641 A B K k f x x') = (term622 A B K k f x x').
Proof. exact (MK_COMB (@lem4459856) (@lem4459855 A B K k f x x')). Qed.
Lemma lem4459858 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term642 A B K k x f s i) = (term612 A B K k x f s i).
Proof. exact (eq_refl (term642 A B K k x f s i)). Qed.
Lemma lem4459859 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term643 A B K k x f s) = (term619 A B K k x f s).
Proof. exact (fun_ext (fun i : K => @lem4459858 A B K k x f s i)). Qed.
Lemma lem4459860 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4459861 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term644 A B K k x f s) = (term620 A B K k x f s).
Proof. exact (MK_COMB (@lem4459860 K) (@lem4459859 A B K k x f s)). Qed.
Lemma lem4459862 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term636 A B K x k x' f s) = (term624 A B K x k x' f s).
Proof. exact (MK_COMB (@lem4459857 A B K k f x x') (@lem4459861 A B K k x' f s)). Qed.
Lemma lem4459863 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4459864 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term645 A B K x k x' f s) = (term646 A B K x k x' f s).
Proof. exact (MK_COMB (@lem4459863) (@lem4459862 A B K x k x' f s)). Qed.
Lemma lem4459865 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (i : K) : (term638 A B K k f x x' i) = (term588 A B K k f x x' i).
Proof. exact (eq_refl (term638 A B K k f x x' i)). Qed.
Lemma lem4459866 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4459867 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (x' : K -> B) (i : K) : (term647 A B K k f x x' i) = (term648 A B K k f x x' i).
Proof. exact (MK_COMB (@lem4459866) (@lem4459865 A B K k f x x' i)). Qed.
Lemma lem4459868 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term642 A B K k x f s i) = (term612 A B K k x f s i).
Proof. exact (eq_refl (term642 A B K k x f s i)). Qed.
Lemma lem4459869 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term649 A B K x k x' f s i) = (term650 A B K x k x' f s i).
Proof. exact (MK_COMB (@lem4459867 A B K k f x x' i) (@lem4459868 A B K k x' f s i)). Qed.
Lemma lem4459870 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term651 A B K x k x' f s) = (term652 A B K x k x' f s).
Proof. exact (fun_ext (fun i : K => @lem4459869 A B K x k x' f s i)). Qed.
Lemma lem4459871 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4459872 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term637 A B K x k x' f s) = (term653 A B K x k x' f s).
Proof. exact (MK_COMB (@lem4459871 K) (@lem4459870 A B K x k x' f s)). Qed.
Lemma lem4459873 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : ((term636 A B K x k x' f s) = (term637 A B K x k x' f s)) = ((term624 A B K x k x' f s) = (term653 A B K x k x' f s)).
Proof. exact (MK_COMB (@lem4459864 A B K x k x' f s) (@lem4459872 A B K x k x' f s)). Qed.
Lemma lem4459874 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term624 A B K x k x' f s) = (term653 A B K x k x' f s).
Proof. exact (EQ_MP (@lem4459873 A B K x k x' f s) (@lem4459851 A B K x k x' f s)). Qed.
Lemma lem4459877 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term654 A B K x k x' f s) = (term654 A B K x k x' f s).
Proof. exact (eq_refl (term654 A B K x k x' f s)). Qed.
Lemma lem4459878 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term654 A B K x k x' f s) = ((term624 A B K x k x' f s) = (term653 A B K x k x' f s)).
Proof. exact (eq_refl (term654 A B K x k x' f s)). Qed.
Lemma lem4459879 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term655 A B K x k x' f s) = (term655 A B K x k x' f s).
Proof. exact (eq_refl (term655 A B K x k x' f s)). Qed.
Lemma lem4459880 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : ((term654 A B K x k x' f s) = (term654 A B K x k x' f s)) = ((term654 A B K x k x' f s) = ((term624 A B K x k x' f s) = (term653 A B K x k x' f s))).
Proof. exact (MK_COMB (@lem4459879 A B K x k x' f s) (@lem4459878 A B K x k x' f s)). Qed.
Lemma lem4459881 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term654 A B K x k x' f s) = ((term624 A B K x k x' f s) = (term653 A B K x k x' f s)).
Proof. exact (eq_refl (term654 A B K x k x' f s)). Qed.
Lemma lem4459882 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4459883 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term655 A B K x k x' f s) = (term656 A B K x k x' f s).
Proof. exact (MK_COMB (@lem4459882) (@lem4459881 A B K x k x' f s)). Qed.
Lemma lem4459884 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : ((term624 A B K x k x' f s) = (term653 A B K x k x' f s)) = ((term624 A B K x k x' f s) = (term653 A B K x k x' f s)).
Proof. exact (eq_refl ((term624 A B K x k x' f s) = (term653 A B K x k x' f s))). Qed.
Lemma lem4459885 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : ((term654 A B K x k x' f s) = ((term624 A B K x k x' f s) = (term653 A B K x k x' f s))) = (((term624 A B K x k x' f s) = (term653 A B K x k x' f s)) = ((term624 A B K x k x' f s) = (term653 A B K x k x' f s))).
Proof. exact (MK_COMB (@lem4459883 A B K x k x' f s) (@lem4459884 A B K x k x' f s)). Qed.
Lemma lem4459886 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : ((term654 A B K x k x' f s) = (term654 A B K x k x' f s)) = (((term624 A B K x k x' f s) = (term653 A B K x k x' f s)) = ((term624 A B K x k x' f s) = (term653 A B K x k x' f s))).
Proof. exact (TRANS (@lem4459880 A B K x k x' f s) (@lem4459885 A B K x k x' f s)). Qed.
Lemma lem4459887 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : ((term624 A B K x k x' f s) = (term653 A B K x k x' f s)) = ((term624 A B K x k x' f s) = (term653 A B K x k x' f s)).
Proof. exact (EQ_MP (@lem4459886 A B K x k x' f s) (@lem4459877 A B K x k x' f s)). Qed.
Lemma lem4459888 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term624 A B K x k x' f s) = (term653 A B K x k x' f s).
Proof. exact (EQ_MP (@lem4459887 A B K x k x' f s) (@lem4459874 A B K x k x' f s)). Qed.
Lemma lem4459889 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term632 A B K x k f s) = (term657 A B K x k f s).
Proof. exact (fun_ext (fun x' : K -> B => @lem4459888 A B K x k x' f s)). Qed.
Lemma lem4459890 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4459891 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term633 A B K x k f s) = (term658 A B K x k f s).
Proof. exact (MK_COMB (@lem4459890 B K) (@lem4459889 A B K x k f s)). Qed.
Lemma lem4459893 {A B : Type'} (P : type1413 A B) : (term659 A B P) = (term660 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4459894 {B K : Type'} (P : type799 B K) : (term661 B K P) = (term662 B K P).
Proof. exact (@lem4459893 (K -> B) K P). Qed.
Lemma lem4459895 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term663 A B K x k f s) = (term664 A B K x k f s).
Proof. exact (@lem4459894 B K (term665 A B K x k f s)). Qed.
Lemma lem4459896 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term666 A B K x k f s x') = (term652 A B K x k x' f s).
Proof. exact (eq_refl (term666 A B K x k f s x')). Qed.
Lemma lem4459897 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4459898 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term667 A B K x k f s x' i) = (term668 A B K x k x' f s i).
Proof. exact (MK_COMB (@lem4459896 A B K x k x' f s) (@lem4459897 K i)). Qed.
Lemma lem4459899 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term668 A B K x k x' f s i) = (term650 A B K x k x' f s i).
Proof. exact (eq_refl (term668 A B K x k x' f s i)). Qed.
Lemma lem4459900 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term667 A B K x k f s x' i) = (term650 A B K x k x' f s i).
Proof. exact (TRANS (@lem4459898 A B K x k x' f s i) (@lem4459899 A B K x k x' f s i)). Qed.
Lemma lem4459901 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term669 A B K x k f s x') = (term652 A B K x k x' f s).
Proof. exact (fun_ext (fun i : K => @lem4459900 A B K x k x' f s i)). Qed.
Lemma lem4459902 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4459903 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term670 A B K x k f s x') = (term653 A B K x k x' f s).
Proof. exact (MK_COMB (@lem4459902 K) (@lem4459901 A B K x k x' f s)). Qed.
Lemma lem4459904 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term671 A B K x k f s) = (term657 A B K x k f s).
Proof. exact (fun_ext (fun x' : K -> B => @lem4459903 A B K x k x' f s)). Qed.
Lemma lem4459905 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4459906 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term663 A B K x k f s) = (term658 A B K x k f s).
Proof. exact (MK_COMB (@lem4459905 B K) (@lem4459904 A B K x k f s)). Qed.
Lemma lem4459907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4459908 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term672 A B K x k f s) = (term673 A B K x k f s).
Proof. exact (MK_COMB (@lem4459907) (@lem4459906 A B K x k f s)). Qed.
Lemma lem4459909 {A B K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term666 A B K x k f s x') = (term652 A B K x k x' f s).
Proof. exact (eq_refl (term666 A B K x k f s x')). Qed.
Lemma lem4459910 {B K : Type'} (i : type803 B K) (x : K -> B) : (i x) = (i x).
Proof. exact (eq_refl (i x)). Qed.
Lemma lem4459911 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term674 A B K x k f s i x') = (term675 A B K x k f s i x').
Proof. exact (MK_COMB (@lem4459909 A B K x k x' f s) (@lem4459910 B K i x')). Qed.
Lemma lem4459912 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term675 A B K x k f s i x') = (term676 A B K x k f s i x').
Proof. exact (eq_refl (term675 A B K x k f s i x')). Qed.
Lemma lem4459913 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term674 A B K x k f s i x') = (term676 A B K x k f s i x').
Proof. exact (TRANS (@lem4459911 A B K x k f s i x') (@lem4459912 A B K x k f s i x')). Qed.
Lemma lem4459914 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) : (term677 A B K x k f s i) = (term678 A B K x k f s i).
Proof. exact (fun_ext (fun x' : K -> B => @lem4459913 A B K x k f s i x')). Qed.
Lemma lem4459915 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4459916 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) : (term679 A B K x k f s i) = (term680 A B K x k f s i).
Proof. exact (MK_COMB (@lem4459915 B K) (@lem4459914 A B K x k f s i)). Qed.
Lemma lem4459917 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term681 A B K x k f s) = (term682 A B K x k f s).
Proof. exact (fun_ext (fun i : type803 B K => @lem4459916 A B K x k f s i)). Qed.
Lemma lem4459918 {B K : Type'} : (@ex ((K -> B) -> K)) = (@ex ((K -> B) -> K)).
Proof. exact (eq_refl (@ex ((K -> B) -> K))). Qed.
Lemma lem4459919 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term664 A B K x k f s) = (term683 A B K x k f s).
Proof. exact (MK_COMB (@lem4459918 B K) (@lem4459917 A B K x k f s)). Qed.
Lemma lem4459920 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : ((term663 A B K x k f s) = (term664 A B K x k f s)) = ((term658 A B K x k f s) = (term683 A B K x k f s)).
Proof. exact (MK_COMB (@lem4459908 A B K x k f s) (@lem4459919 A B K x k f s)). Qed.
Lemma lem4459921 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term658 A B K x k f s) = (term683 A B K x k f s).
Proof. exact (EQ_MP (@lem4459920 A B K x k f s) (@lem4459895 A B K x k f s)). Qed.
Lemma lem4459923 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term633 A B K x k f s) = (term683 A B K x k f s).
Proof. exact (TRANS (@lem4459891 A B K x k f s) (@lem4459921 A B K x k f s)). Qed.
Lemma lem4459924 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term480 A B K x k f s) = (term683 A B K x k f s).
Proof. exact (TRANS (@lem4459694 A B K x k f s) (@lem4459923 A B K x k f s)). Qed.
Lemma lem4459925 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term480 A B K x k f s) : term683 A B K x k f s.
Proof. exact (EQ_MP (@lem4459924 A B K x k f s) (@lem4459047 A B K x k f s h1)). Qed.
Lemma lem4459926 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term680 A B K x k f s i.
Proof. exact (h1). Qed.
Lemma lem4459927 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4459938 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4459939 {A B K : Type'} (f : type868 A B K) (x : type1514 A B K) : (f x) = (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) f x).
Proof. exact (@lem4459938 (type1514 A B K) (type892 A B K) f x). Qed.
Lemma lem4459940 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (_51538 f) = (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538 f).
Proof. exact (@lem4459939 A B K _51538 f). Qed.
Lemma lem4459941 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4459942 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (_51538 f k) = (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538 f k).
Proof. exact (MK_COMB (@lem4459940 A B K _51538 f) (@lem4459941 K k)). Qed.
Lemma lem4459944 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4459945 {A B K : Type'} (f : type892 A B K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A) -> K -> B) f x).
Proof. exact (@lem4459944 (K -> Prop) (type887 A B K) f x). Qed.
Lemma lem4459946 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538 f k) = (term684 A B K _51538 f k).
Proof. exact (@lem4459945 A B K (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538 f) k). Qed.
Lemma lem4459947 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (_51538 f k) = (term684 A B K _51538 f k).
Proof. exact (TRANS (@lem4459942 A B K _51538 f k) (@lem4459946 A B K _51538 f k)). Qed.
Lemma lem4459948 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4459949 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (_51538 f k x) = (term685 A B K _51538 f k x).
Proof. exact (MK_COMB (@lem4459947 A B K _51538 f k) (@lem4459948 A K x)). Qed.
Lemma lem4459951 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4459952 {A B K : Type'} (f : type887 A B K) (x : K -> A) : (f x) = (@I ((K -> A) -> K -> B) f x).
Proof. exact (@lem4459951 (K -> A) (K -> B) f x). Qed.
Lemma lem4459953 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term685 A B K _51538 f k x) = (term686 A B K _51538 f k x).
Proof. exact (@lem4459952 A B K (term684 A B K _51538 f k) x). Qed.
Lemma lem4459954 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (_51538 f k x) = (term686 A B K _51538 f k x).
Proof. exact (TRANS (@lem4459949 A B K _51538 f k x) (@lem4459953 A B K _51538 f k x)). Qed.
Lemma lem4459955 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4459956 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (_51538 f k x i) = (term687 A B K _51538 f k x i).
Proof. exact (MK_COMB (@lem4459954 A B K _51538 f k x) (@lem4459955 K i)). Qed.
Lemma lem4459958 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4459959 {B K : Type'} (f : K -> B) (x : K) : (f x) = (@I (K -> B) f x).
Proof. exact (@lem4459958 K B f x). Qed.
Lemma lem4459960 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term687 A B K _51538 f k x i) = (term688 A B K _51538 f k x i).
Proof. exact (@lem4459959 B K (term686 A B K _51538 f k x) i). Qed.
Lemma lem4459962 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (_51538 f k x i) = (term688 A B K _51538 f k x i).
Proof. exact (TRANS (@lem4459956 A B K _51538 f k x i) (@lem4459960 A B K _51538 f k x i)). Qed.
Lemma lem4459969 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4459970 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (@I (K -> A -> B) f x).
Proof. exact (@lem4459969 K (A -> B) f x). Qed.
Lemma lem4459971 {A B K : Type'} (f : type1514 A B K) (i : K) : (f i) = (@I (K -> A -> B) f i).
Proof. exact (@lem4459970 A B K f i). Qed.
Lemma lem4459972 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4459973 {A B K : Type'} (f : type1514 A B K) (i : K) : (f i (@ARB A)) = (@I (K -> A -> B) f i (@ARB A)).
Proof. exact (MK_COMB (@lem4459971 A B K f i) (@lem4459972 A)). Qed.
Lemma lem4459975 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4459976 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4459975 A B f x). Qed.
Lemma lem4459977 {A B K : Type'} (f : type1514 A B K) (i : K) : (@I (K -> A -> B) f i (@ARB A)) = (term689 A B K f i).
Proof. exact (@lem4459976 A B (@I (K -> A -> B) f i) (@ARB A)). Qed.
Lemma lem4459979 {A B K : Type'} (f : type1514 A B K) (i : K) : (f i (@ARB A)) = (term689 A B K f i).
Proof. exact (TRANS (@lem4459973 A B K f i) (@lem4459977 A B K f i)). Qed.
Lemma lem4459980 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term412 A B K _51538 f k x i) = (term690 A B K _51538 f k x i).
Proof. exact (MK_COMB (@lem4459927 B) (@lem4459962 A B K _51538 f k x i)). Qed.
Lemma lem4459981 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (i : K) : ((_51538 f k x i) = (f i (@ARB A))) = ((term688 A B K _51538 f k x i) = (term689 A B K f i)).
Proof. exact (MK_COMB (@lem4459980 A B K _51538 f k x i) (@lem4459979 A B K f i)). Qed.
Lemma lem4459986 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4459987 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4459986 K Prop f x). Qed.
Lemma lem4459989 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4459987 K k i). Qed.
Lemma lem4459990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4459991 {K : Type'} (k : K -> Prop) (i : K) : (term691 K k i) = (term692 K k i).
Proof. exact (MK_COMB (@lem4459990) (@lem4459989 K k i)). Qed.
Lemma lem4459992 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (i : K) : (term492 A B K _51538 k x f i) = (term693 A B K _51538 k x f i).
Proof. exact (MK_COMB (@lem4459991 K k i) (@lem4459981 A B K _51538 k x f i)). Qed.
Lemma lem4459993 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term486 A B K _51538 k x f) = (term694 A B K _51538 k x f).
Proof. exact (fun_ext (fun i : K => @lem4459992 A B K _51538 k x f i)). Qed.
Lemma lem4459994 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4459995 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (x : K -> A) (f : type1514 A B K) : (term504 A B K _51538 k x f) = (term695 A B K _51538 k x f).
Proof. exact (MK_COMB (@lem4459994 K) (@lem4459993 A B K _51538 k x f)). Qed.
Lemma lem4459996 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term513 A B K _51538 k f) = (term696 A B K _51538 k f).
Proof. exact (fun_ext (fun x : K -> A => @lem4459995 A B K _51538 k x f)). Qed.
Lemma lem4459997 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4459998 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term528 A B K _51538 k f) = (term697 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4459997 A K) (@lem4459996 A B K _51538 k f)). Qed.
Lemma lem4459999 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term537 A B K _51538 f) = (term698 A B K _51538 f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4459998 A B K _51538 k f)). Qed.
Lemma lem4460000 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4460001 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term552 A B K _51538 f) = (term699 A B K _51538 f).
Proof. exact (MK_COMB (@lem4460000 K) (@lem4459999 A B K _51538 f)). Qed.
Lemma lem4460002 {A B K : Type'} (_51538 : type868 A B K) : (term561 A B K _51538) = (term700 A B K _51538).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4460001 A B K _51538 f)). Qed.
Lemma lem4460003 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4460004 {A B K : Type'} (_51538 : type868 A B K) : (term576 A B K _51538) = (term701 A B K _51538).
Proof. exact (MK_COMB (@lem4460003 A B K) (@lem4460002 A B K _51538)). Qed.
Lemma lem4460005 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4460016 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460017 {A B K : Type'} (f : type868 A B K) (x : type1514 A B K) : (f x) = (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) f x).
Proof. exact (@lem4460016 (type1514 A B K) (type892 A B K) f x). Qed.
Lemma lem4460018 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (_51538 f) = (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538 f).
Proof. exact (@lem4460017 A B K _51538 f). Qed.
Lemma lem4460019 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4460020 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (_51538 f k) = (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538 f k).
Proof. exact (MK_COMB (@lem4460018 A B K _51538 f) (@lem4460019 K k)). Qed.
Lemma lem4460022 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460023 {A B K : Type'} (f : type892 A B K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A) -> K -> B) f x).
Proof. exact (@lem4460022 (K -> Prop) (type887 A B K) f x). Qed.
Lemma lem4460024 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538 f k) = (term684 A B K _51538 f k).
Proof. exact (@lem4460023 A B K (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538 f) k). Qed.
Lemma lem4460025 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (_51538 f k) = (term684 A B K _51538 f k).
Proof. exact (TRANS (@lem4460020 A B K _51538 f k) (@lem4460024 A B K _51538 f k)). Qed.
Lemma lem4460026 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4460027 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (_51538 f k x) = (term685 A B K _51538 f k x).
Proof. exact (MK_COMB (@lem4460025 A B K _51538 f k) (@lem4460026 A K x)). Qed.
Lemma lem4460029 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460030 {A B K : Type'} (f : type887 A B K) (x : K -> A) : (f x) = (@I ((K -> A) -> K -> B) f x).
Proof. exact (@lem4460029 (K -> A) (K -> B) f x). Qed.
Lemma lem4460031 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term685 A B K _51538 f k x) = (term686 A B K _51538 f k x).
Proof. exact (@lem4460030 A B K (term684 A B K _51538 f k) x). Qed.
Lemma lem4460032 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (_51538 f k x) = (term686 A B K _51538 f k x).
Proof. exact (TRANS (@lem4460027 A B K _51538 f k x) (@lem4460031 A B K _51538 f k x)). Qed.
Lemma lem4460033 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4460034 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (_51538 f k x i) = (term687 A B K _51538 f k x i).
Proof. exact (MK_COMB (@lem4460032 A B K _51538 f k x) (@lem4460033 K i)). Qed.
Lemma lem4460036 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460037 {B K : Type'} (f : K -> B) (x : K) : (f x) = (@I (K -> B) f x).
Proof. exact (@lem4460036 K B f x). Qed.
Lemma lem4460038 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term687 A B K _51538 f k x i) = (term688 A B K _51538 f k x i).
Proof. exact (@lem4460037 B K (term686 A B K _51538 f k x) i). Qed.
Lemma lem4460040 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (_51538 f k x i) = (term688 A B K _51538 f k x i).
Proof. exact (TRANS (@lem4460034 A B K _51538 f k x i) (@lem4460038 A B K _51538 f k x i)). Qed.
Lemma lem4460047 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460048 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4460047 K A f x). Qed.
Lemma lem4460050 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4460048 A K x i). Qed.
Lemma lem4460051 {A B K : Type'} (f : type1514 A B K) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4460052 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : K) : (term433 A B K f x i) = (term702 A B K f x i).
Proof. exact (MK_COMB (@lem4460051 A B K f i) (@lem4460050 A K x i)). Qed.
Lemma lem4460054 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460055 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (@I (K -> A -> B) f x).
Proof. exact (@lem4460054 K (A -> B) f x). Qed.
Lemma lem4460056 {A B K : Type'} (f : type1514 A B K) (i : K) : (f i) = (@I (K -> A -> B) f i).
Proof. exact (@lem4460055 A B K f i). Qed.
Lemma lem4460057 {A K : Type'} (x : K -> A) (i : K) : (@I (K -> A) x i) = (@I (K -> A) x i).
Proof. exact (eq_refl (@I (K -> A) x i)). Qed.
Lemma lem4460058 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : K) : (term702 A B K f x i) = (term703 A B K f x i).
Proof. exact (MK_COMB (@lem4460056 A B K f i) (@lem4460057 A K x i)). Qed.
Lemma lem4460060 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460061 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4460060 A B f x). Qed.
Lemma lem4460062 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : K) : (term703 A B K f x i) = (term704 A B K f x i).
Proof. exact (@lem4460061 A B (@I (K -> A -> B) f i) (@I (K -> A) x i)). Qed.
Lemma lem4460063 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : K) : (term702 A B K f x i) = (term704 A B K f x i).
Proof. exact (TRANS (@lem4460058 A B K f x i) (@lem4460062 A B K f x i)). Qed.
Lemma lem4460064 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : K) : (term433 A B K f x i) = (term704 A B K f x i).
Proof. exact (TRANS (@lem4460052 A B K f x i) (@lem4460063 A B K f x i)). Qed.
Lemma lem4460065 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (i : K) : (term412 A B K _51538 f k x i) = (term690 A B K _51538 f k x i).
Proof. exact (MK_COMB (@lem4460005 B) (@lem4460040 A B K _51538 f k x i)). Qed.
Lemma lem4460066 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : K) : ((_51538 f k x i) = (term433 A B K f x i)) = ((term688 A B K _51538 f k x i) = (term704 A B K f x i)).
Proof. exact (MK_COMB (@lem4460065 A B K _51538 f k x i) (@lem4460064 A B K f x i)). Qed.
Lemma lem4460067 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4460072 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460073 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4460072 K Prop f x). Qed.
Lemma lem4460075 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4460073 K k i). Qed.
Lemma lem4460076 {K : Type'} (k : K -> Prop) (i : K) : (term590 K k i) = (term705 K k i).
Proof. exact (MK_COMB (@lem4460067) (@lem4460075 K k i)). Qed.
Lemma lem4460077 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4460078 {K : Type'} (k : K -> Prop) (i : K) : (term706 K k i) = (term707 K k i).
Proof. exact (MK_COMB (@lem4460077) (@lem4460076 K k i)). Qed.
Lemma lem4460079 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : K) : (term488 A B K _51538 k f x i) = (term708 A B K _51538 k f x i).
Proof. exact (MK_COMB (@lem4460078 K k i) (@lem4460066 A B K _51538 k f x i)). Qed.
Lemma lem4460080 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term485 A B K _51538 k f x) = (term709 A B K _51538 k f x).
Proof. exact (fun_ext (fun i : K => @lem4460079 A B K _51538 k f x i)). Qed.
Lemma lem4460081 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4460082 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term499 A B K _51538 k f x) = (term710 A B K _51538 k f x).
Proof. exact (MK_COMB (@lem4460081 K) (@lem4460080 A B K _51538 k f x)). Qed.
Lemma lem4460083 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term512 A B K _51538 k f) = (term711 A B K _51538 k f).
Proof. exact (fun_ext (fun x : K -> A => @lem4460082 A B K _51538 k f x)). Qed.
Lemma lem4460084 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4460085 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term523 A B K _51538 k f) = (term712 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4460084 A K) (@lem4460083 A B K _51538 k f)). Qed.
Lemma lem4460086 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term536 A B K _51538 f) = (term713 A B K _51538 f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4460085 A B K _51538 k f)). Qed.
Lemma lem4460087 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4460088 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term547 A B K _51538 f) = (term714 A B K _51538 f).
Proof. exact (MK_COMB (@lem4460087 K) (@lem4460086 A B K _51538 f)). Qed.
Lemma lem4460089 {A B K : Type'} (_51538 : type868 A B K) : (term560 A B K _51538) = (term715 A B K _51538).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4460088 A B K _51538 f)). Qed.
Lemma lem4460090 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4460091 {A B K : Type'} (_51538 : type868 A B K) : (term571 A B K _51538) = (term716 A B K _51538).
Proof. exact (MK_COMB (@lem4460090 A B K) (@lem4460089 A B K _51538)). Qed.
Lemma lem4460092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4460093 {A B K : Type'} (_51538 : type868 A B K) : (term573 A B K _51538) = (term717 A B K _51538).
Proof. exact (MK_COMB (@lem4460092) (@lem4460091 A B K _51538)). Qed.
Lemma lem4460094 {A B K : Type'} (_51538 : type868 A B K) : (term577 A B K _51538) = (term718 A B K _51538).
Proof. exact (MK_COMB (@lem4460093 A B K _51538) (@lem4460004 A B K _51538)). Qed.
Lemma lem4460095 {A B K : Type'} (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term718 A B K _51538.
Proof. exact (EQ_MP (@lem4460094 A B K _51538) (@lem4459560 A B K _51538 h1)). Qed.
Lemma lem4460108 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460109 {A B K : Type'} (f : type868 A B K) (x : type1514 A B K) : (f x) = (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) f x).
Proof. exact (@lem4460108 (type1514 A B K) (type892 A B K) f x). Qed.
Lemma lem4460110 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (_51538 f) = (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538 f).
Proof. exact (@lem4460109 A B K _51538 f). Qed.
Lemma lem4460111 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4460112 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (_51538 f k) = (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538 f k).
Proof. exact (MK_COMB (@lem4460110 A B K _51538 f) (@lem4460111 K k)). Qed.
Lemma lem4460114 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460115 {A B K : Type'} (f : type892 A B K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A) -> K -> B) f x).
Proof. exact (@lem4460114 (K -> Prop) (type887 A B K) f x). Qed.
Lemma lem4460116 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538 f k) = (term684 A B K _51538 f k).
Proof. exact (@lem4460115 A B K (@I ((K -> A -> B) -> (K -> Prop) -> (K -> A) -> K -> B) _51538 f) k). Qed.
Lemma lem4460117 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) : (_51538 f k) = (term684 A B K _51538 f k).
Proof. exact (TRANS (@lem4460112 A B K _51538 f k) (@lem4460116 A B K _51538 f k)). Qed.
Lemma lem4460118 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4460119 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (_51538 f k x) = (term685 A B K _51538 f k x).
Proof. exact (MK_COMB (@lem4460117 A B K _51538 f k) (@lem4460118 A K x)). Qed.
Lemma lem4460121 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460122 {A B K : Type'} (f : type887 A B K) (x : K -> A) : (f x) = (@I ((K -> A) -> K -> B) f x).
Proof. exact (@lem4460121 (K -> A) (K -> B) f x). Qed.
Lemma lem4460123 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term685 A B K _51538 f k x) = (term686 A B K _51538 f k x).
Proof. exact (@lem4460122 A B K (term684 A B K _51538 f k) x). Qed.
Lemma lem4460125 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (_51538 f k x) = (term686 A B K _51538 f k x).
Proof. exact (TRANS (@lem4460119 A B K _51538 f k x) (@lem4460123 A B K _51538 f k x)). Qed.
Lemma lem4460126 {B K : Type'} (k : K -> Prop) : (@RESTRICTION K B k) = (@RESTRICTION K B k).
Proof. exact (eq_refl (@RESTRICTION K B k)). Qed.
Lemma lem4460127 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term342 A B K _51538 f k x) = (term719 A B K _51538 f k x).
Proof. exact (MK_COMB (@lem4460126 B K k) (@lem4460125 A B K _51538 f k x)). Qed.
Lemma lem4460129 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460130 {B K : Type'} (f : type853 B K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> B) -> K -> B) f x).
Proof. exact (@lem4460129 (K -> Prop) (type796 B K) f x). Qed.
Lemma lem4460131 {B K : Type'} (k : K -> Prop) : (@RESTRICTION K B k) = (@I ((K -> Prop) -> (K -> B) -> K -> B) (@RESTRICTION K B) k).
Proof. exact (@lem4460130 B K (@RESTRICTION K B) k). Qed.
Lemma lem4460132 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term686 A B K _51538 f k x) = (term686 A B K _51538 f k x).
Proof. exact (eq_refl (term686 A B K _51538 f k x)). Qed.
Lemma lem4460133 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term719 A B K _51538 f k x) = (term720 A B K _51538 f k x).
Proof. exact (MK_COMB (@lem4460131 B K k) (@lem4460132 A B K _51538 f k x)). Qed.
Lemma lem4460135 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460136 {B K : Type'} (f : type796 B K) (x : K -> B) : (f x) = (@I ((K -> B) -> K -> B) f x).
Proof. exact (@lem4460135 (K -> B) (K -> B) f x). Qed.
Lemma lem4460137 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term720 A B K _51538 f k x) = (term721 A B K _51538 f k x).
Proof. exact (@lem4460136 B K (@I ((K -> Prop) -> (K -> B) -> K -> B) (@RESTRICTION K B) k) (term686 A B K _51538 f k x)). Qed.
Lemma lem4460138 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term719 A B K _51538 f k x) = (term721 A B K _51538 f k x).
Proof. exact (TRANS (@lem4460133 A B K _51538 f k x) (@lem4460137 A B K _51538 f k x)). Qed.
Lemma lem4460139 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term342 A B K _51538 f k x) = (term721 A B K _51538 f k x).
Proof. exact (TRANS (@lem4460127 A B K _51538 f k x) (@lem4460138 A B K _51538 f k x)). Qed.
Lemma lem4460140 {B K : Type'} (g : K -> B) : (@eq (K -> B) g) = (@eq (K -> B) g).
Proof. exact (eq_refl (@eq (K -> B) g)). Qed.
Lemma lem4460141 {A B K : Type'} (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (g = (term342 A B K _51538 f k x)) = (g = (term721 A B K _51538 f k x)).
Proof. exact (MK_COMB (@lem4460140 B K g) (@lem4460139 A B K _51538 f k x)). Qed.
Lemma lem4460148 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460149 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4460148 K A f x). Qed.
Lemma lem4460151 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4460149 A K x i). Qed.
Lemma lem4460152 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4460153 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term266 A K s x i) = (term722 A K s x i).
Proof. exact (MK_COMB (@lem4460152 A K s i) (@lem4460151 A K x i)). Qed.
Lemma lem4460155 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460156 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4460155 K (A -> Prop) f x). Qed.
Lemma lem4460157 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4460156 A K s i). Qed.
Lemma lem4460158 {A K : Type'} (x : K -> A) (i : K) : (@I (K -> A) x i) = (@I (K -> A) x i).
Proof. exact (eq_refl (@I (K -> A) x i)). Qed.
Lemma lem4460159 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term722 A K s x i) = (term723 A K s x i).
Proof. exact (MK_COMB (@lem4460157 A K s i) (@lem4460158 A K x i)). Qed.
Lemma lem4460161 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460162 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4460161 A Prop f x). Qed.
Lemma lem4460163 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term723 A K s x i) = (term724 A K s x i).
Proof. exact (@lem4460162 A (@I (K -> A -> Prop) s i) (@I (K -> A) x i)). Qed.
Lemma lem4460164 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term722 A K s x i) = (term724 A K s x i).
Proof. exact (TRANS (@lem4460159 A K s x i) (@lem4460163 A K s x i)). Qed.
Lemma lem4460165 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term266 A K s x i) = (term724 A K s x i).
Proof. exact (TRANS (@lem4460153 A K s x i) (@lem4460164 A K s x i)). Qed.
Lemma lem4460166 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4460171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460172 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4460171 K Prop f x). Qed.
Lemma lem4460174 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4460172 K k i). Qed.
Lemma lem4460175 {K : Type'} (k : K -> Prop) (i : K) : (term590 K k i) = (term705 K k i).
Proof. exact (MK_COMB (@lem4460166) (@lem4460174 K k i)). Qed.
Lemma lem4460176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4460177 {K : Type'} (k : K -> Prop) (i : K) : (term706 K k i) = (term707 K k i).
Proof. exact (MK_COMB (@lem4460176) (@lem4460175 K k i)). Qed.
Lemma lem4460178 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term578 A K k s x i) = (term725 A K k s x i).
Proof. exact (MK_COMB (@lem4460177 K k i) (@lem4460165 A K s x i)). Qed.
Lemma lem4460179 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term579 A K k s x) = (term726 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4460178 A K k s x i)). Qed.
Lemma lem4460180 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4460181 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term580 A K k s x) = (term727 A K k s x).
Proof. exact (MK_COMB (@lem4460180 K) (@lem4460179 A K k s x)). Qed.
Lemma lem4460182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4460183 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term581 A K k s x) = (term728 A K k s x).
Proof. exact (MK_COMB (@lem4460182) (@lem4460181 A K k s x)). Qed.
Lemma lem4460184 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term582 A B K s g _51538 f k x) = (term729 A B K s g _51538 f k x).
Proof. exact (MK_COMB (@lem4460183 A K k s x) (@lem4460141 A B K g _51538 f k x)). Qed.
Lemma lem4460185 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term343 A B K s g _51538 f k x) : term729 A B K s g _51538 f k x.
Proof. exact (EQ_MP (@lem4460184 A B K s g _51538 f k x) (@lem4459627 A B K s g _51538 f k x h1)). Qed.
Lemma lem4460186 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4460187 {A K : Type'} (s : type1470 A K) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4460192 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460193 {B K : Type'} (f : type803 B K) (x : K -> B) : (f x) = (@I ((K -> B) -> K) f x).
Proof. exact (@lem4460192 (K -> B) K f x). Qed.
Lemma lem4460195 {B K : Type'} (i : type803 B K) (x : K -> B) : (i x) = (@I ((K -> B) -> K) i x).
Proof. exact (@lem4460193 B K i x). Qed.
Lemma lem4460196 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4460197 {A B K : Type'} (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term730 A B K s i x) = (term731 A B K s i x).
Proof. exact (MK_COMB (@lem4460187 A K s) (@lem4460195 B K i x)). Qed.
Lemma lem4460198 {A B K : Type'} (s : type1470 A K) (i : type803 B K) (x : K -> B) (x' : A) : (term732 A B K s i x x') = (term733 A B K s i x x').
Proof. exact (MK_COMB (@lem4460197 A B K s i x) (@lem4460196 A x')). Qed.
Lemma lem4460200 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460201 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4460200 K (A -> Prop) f x). Qed.
Lemma lem4460202 {A B K : Type'} (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term731 A B K s i x) = (term734 A B K s i x).
Proof. exact (@lem4460201 A K s (@I ((K -> B) -> K) i x)). Qed.
Lemma lem4460203 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4460204 {A B K : Type'} (s : type1470 A K) (i : type803 B K) (x : K -> B) (x' : A) : (term733 A B K s i x x') = (term735 A B K s i x x').
Proof. exact (MK_COMB (@lem4460202 A B K s i x) (@lem4460203 A x')). Qed.
Lemma lem4460206 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460207 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4460206 A Prop f x). Qed.
Lemma lem4460208 {A B K : Type'} (s : type1470 A K) (i : type803 B K) (x : K -> B) (x' : A) : (term735 A B K s i x x') = (term736 A B K s i x x').
Proof. exact (@lem4460207 A (term734 A B K s i x) x'). Qed.
Lemma lem4460209 {A B K : Type'} (s : type1470 A K) (i : type803 B K) (x : K -> B) (x' : A) : (term733 A B K s i x x') = (term736 A B K s i x x').
Proof. exact (TRANS (@lem4460204 A B K s i x x') (@lem4460208 A B K s i x x')). Qed.
Lemma lem4460210 {A B K : Type'} (s : type1470 A K) (i : type803 B K) (x : K -> B) (x' : A) : (term732 A B K s i x x') = (term736 A B K s i x x').
Proof. exact (TRANS (@lem4460198 A B K s i x x') (@lem4460209 A B K s i x x')). Qed.
Lemma lem4460211 {A B K : Type'} (s : type1470 A K) (i : type803 B K) (x : K -> B) (x' : A) : (term737 A B K s i x x') = (term738 A B K s i x x').
Proof. exact (MK_COMB (@lem4460186) (@lem4460210 A B K s i x x')). Qed.
Lemma lem4460212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4460213 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4460214 {B K : Type'} (x : K -> B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4460219 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460220 {B K : Type'} (f : type803 B K) (x : K -> B) : (f x) = (@I ((K -> B) -> K) f x).
Proof. exact (@lem4460219 (K -> B) K f x). Qed.
Lemma lem4460222 {B K : Type'} (i : type803 B K) (x : K -> B) : (i x) = (@I ((K -> B) -> K) i x).
Proof. exact (@lem4460220 B K i x). Qed.
Lemma lem4460223 {B K : Type'} (i : type803 B K) (x : K -> B) : (term739 B K i x) = (term740 B K i x).
Proof. exact (MK_COMB (@lem4460214 B K x) (@lem4460222 B K i x)). Qed.
Lemma lem4460225 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460226 {B K : Type'} (f : K -> B) (x : K) : (f x) = (@I (K -> B) f x).
Proof. exact (@lem4460225 K B f x). Qed.
Lemma lem4460227 {B K : Type'} (i : type803 B K) (x : K -> B) : (term740 B K i x) = (term741 B K i x).
Proof. exact (@lem4460226 B K x (@I ((K -> B) -> K) i x)). Qed.
Lemma lem4460228 {B K : Type'} (i : type803 B K) (x : K -> B) : (term739 B K i x) = (term741 B K i x).
Proof. exact (TRANS (@lem4460223 B K i x) (@lem4460227 B K i x)). Qed.
Lemma lem4460229 {A B K : Type'} (f : type1514 A B K) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4460234 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460235 {B K : Type'} (f : type803 B K) (x : K -> B) : (f x) = (@I ((K -> B) -> K) f x).
Proof. exact (@lem4460234 (K -> B) K f x). Qed.
Lemma lem4460237 {B K : Type'} (i : type803 B K) (x : K -> B) : (i x) = (@I ((K -> B) -> K) i x).
Proof. exact (@lem4460235 B K i x). Qed.
Lemma lem4460238 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4460239 {A B K : Type'} (f : type1514 A B K) (i : type803 B K) (x : K -> B) : (term742 A B K f i x) = (term743 A B K f i x).
Proof. exact (MK_COMB (@lem4460229 A B K f) (@lem4460237 B K i x)). Qed.
Lemma lem4460240 {A B K : Type'} (f : type1514 A B K) (i : type803 B K) (x : K -> B) (x' : A) : (term744 A B K f i x x') = (term745 A B K f i x x').
Proof. exact (MK_COMB (@lem4460239 A B K f i x) (@lem4460238 A x')). Qed.
Lemma lem4460242 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460243 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (@I (K -> A -> B) f x).
Proof. exact (@lem4460242 K (A -> B) f x). Qed.
Lemma lem4460244 {A B K : Type'} (f : type1514 A B K) (i : type803 B K) (x : K -> B) : (term743 A B K f i x) = (term746 A B K f i x).
Proof. exact (@lem4460243 A B K f (@I ((K -> B) -> K) i x)). Qed.
Lemma lem4460245 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4460246 {A B K : Type'} (f : type1514 A B K) (i : type803 B K) (x : K -> B) (x' : A) : (term745 A B K f i x x') = (term747 A B K f i x x').
Proof. exact (MK_COMB (@lem4460244 A B K f i x) (@lem4460245 A x')). Qed.
Lemma lem4460248 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460249 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4460248 A B f x). Qed.
Lemma lem4460250 {A B K : Type'} (f : type1514 A B K) (i : type803 B K) (x : K -> B) (x' : A) : (term747 A B K f i x x') = (term748 A B K f i x x').
Proof. exact (@lem4460249 A B (term746 A B K f i x) x'). Qed.
Lemma lem4460251 {A B K : Type'} (f : type1514 A B K) (i : type803 B K) (x : K -> B) (x' : A) : (term745 A B K f i x x') = (term748 A B K f i x x').
Proof. exact (TRANS (@lem4460246 A B K f i x x') (@lem4460250 A B K f i x x')). Qed.
Lemma lem4460252 {A B K : Type'} (f : type1514 A B K) (i : type803 B K) (x : K -> B) (x' : A) : (term744 A B K f i x x') = (term748 A B K f i x x').
Proof. exact (TRANS (@lem4460240 A B K f i x x') (@lem4460251 A B K f i x x')). Qed.
Lemma lem4460253 {B K : Type'} (i : type803 B K) (x : K -> B) : (term749 B K i x) = (term750 B K i x).
Proof. exact (MK_COMB (@lem4460213 B) (@lem4460228 B K i x)). Qed.
Lemma lem4460254 {A B K : Type'} (f : type1514 A B K) (i : type803 B K) (x : K -> B) (x' : A) : ((term739 B K i x) = (term744 A B K f i x x')) = ((term741 B K i x) = (term748 A B K f i x x')).
Proof. exact (MK_COMB (@lem4460253 B K i x) (@lem4460252 A B K f i x x')). Qed.
Lemma lem4460255 {A B K : Type'} (f : type1514 A B K) (i : type803 B K) (x : K -> B) (x' : A) : (term751 A B K f i x x') = (term752 A B K f i x x').
Proof. exact (MK_COMB (@lem4460212) (@lem4460254 A B K f i x x')). Qed.
Lemma lem4460256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4460257 {A B K : Type'} (f : type1514 A B K) (i : type803 B K) (x : K -> B) (x' : A) : (term753 A B K f i x x') = (term754 A B K f i x x').
Proof. exact (MK_COMB (@lem4460256) (@lem4460255 A B K f i x x')). Qed.
Lemma lem4460258 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) (x' : A) : (term755 A B K f s i x x') = (term756 A B K f s i x x').
Proof. exact (MK_COMB (@lem4460257 A B K f i x x') (@lem4460211 A B K s i x x')). Qed.
Lemma lem4460259 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term757 A B K f s i x) = (term758 A B K f s i x).
Proof. exact (fun_ext (fun x' : A => @lem4460258 A B K f s i x x')). Qed.
Lemma lem4460260 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4460261 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term759 A B K f s i x) = (term760 A B K f s i x).
Proof. exact (MK_COMB (@lem4460260 A) (@lem4460259 A B K f s i x)). Qed.
Lemma lem4460262 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4460267 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460268 {B K : Type'} (f : type803 B K) (x : K -> B) : (f x) = (@I ((K -> B) -> K) f x).
Proof. exact (@lem4460267 (K -> B) K f x). Qed.
Lemma lem4460270 {B K : Type'} (i : type803 B K) (x : K -> B) : (i x) = (@I ((K -> B) -> K) i x).
Proof. exact (@lem4460268 B K i x). Qed.
Lemma lem4460271 {B K : Type'} (k : K -> Prop) (i : type803 B K) (x : K -> B) : (term761 B K k i x) = (term762 B K k i x).
Proof. exact (MK_COMB (@lem4460262 K k) (@lem4460270 B K i x)). Qed.
Lemma lem4460273 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460274 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4460273 K Prop f x). Qed.
Lemma lem4460275 {B K : Type'} (k : K -> Prop) (i : type803 B K) (x : K -> B) : (term762 B K k i x) = (term763 B K k i x).
Proof. exact (@lem4460274 K k (@I ((K -> B) -> K) i x)). Qed.
Lemma lem4460276 {B K : Type'} (k : K -> Prop) (i : type803 B K) (x : K -> B) : (term761 B K k i x) = (term763 B K k i x).
Proof. exact (TRANS (@lem4460271 B K k i x) (@lem4460275 B K k i x)). Qed.
Lemma lem4460277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4460278 {B K : Type'} (k : K -> Prop) (i : type803 B K) (x : K -> B) : (term764 B K k i x) = (term765 B K k i x).
Proof. exact (MK_COMB (@lem4460277) (@lem4460276 B K k i x)). Qed.
Lemma lem4460279 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term766 A B K k f s i x) = (term767 A B K k f s i x).
Proof. exact (MK_COMB (@lem4460278 B K k i x) (@lem4460261 A B K f s i x)). Qed.
Lemma lem4460280 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4460281 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4460282 {A B K : Type'} (f : type1514 A B K) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4460287 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460288 {B K : Type'} (f : type803 B K) (x : K -> B) : (f x) = (@I ((K -> B) -> K) f x).
Proof. exact (@lem4460287 (K -> B) K f x). Qed.
Lemma lem4460290 {B K : Type'} (i : type803 B K) (x : K -> B) : (i x) = (@I ((K -> B) -> K) i x).
Proof. exact (@lem4460288 B K i x). Qed.
Lemma lem4460291 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4460296 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460297 {B K : Type'} (f : type803 B K) (x : K -> B) : (f x) = (@I ((K -> B) -> K) f x).
Proof. exact (@lem4460296 (K -> B) K f x). Qed.
Lemma lem4460299 {B K : Type'} (i : type803 B K) (x : K -> B) : (i x) = (@I ((K -> B) -> K) i x).
Proof. exact (@lem4460297 B K i x). Qed.
Lemma lem4460300 {A B K : Type'} (x : K -> A) (i : type803 B K) (x' : K -> B) : (term768 A B K x i x') = (term769 A B K x i x').
Proof. exact (MK_COMB (@lem4460291 A K x) (@lem4460299 B K i x')). Qed.
Lemma lem4460302 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460303 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4460302 K A f x). Qed.
Lemma lem4460304 {A B K : Type'} (x : K -> A) (i : type803 B K) (x' : K -> B) : (term769 A B K x i x') = (term770 A B K x i x').
Proof. exact (@lem4460303 A K x (@I ((K -> B) -> K) i x')). Qed.
Lemma lem4460305 {A B K : Type'} (x : K -> A) (i : type803 B K) (x' : K -> B) : (term768 A B K x i x') = (term770 A B K x i x').
Proof. exact (TRANS (@lem4460300 A B K x i x') (@lem4460304 A B K x i x')). Qed.
Lemma lem4460306 {A B K : Type'} (f : type1514 A B K) (i : type803 B K) (x : K -> B) : (term742 A B K f i x) = (term743 A B K f i x).
Proof. exact (MK_COMB (@lem4460282 A B K f) (@lem4460290 B K i x)). Qed.
Lemma lem4460307 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : (term771 A B K f x i x') = (term772 A B K f x i x').
Proof. exact (MK_COMB (@lem4460306 A B K f i x') (@lem4460305 A B K x i x')). Qed.
Lemma lem4460309 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460310 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (@I (K -> A -> B) f x).
Proof. exact (@lem4460309 K (A -> B) f x). Qed.
Lemma lem4460311 {A B K : Type'} (f : type1514 A B K) (i : type803 B K) (x : K -> B) : (term743 A B K f i x) = (term746 A B K f i x).
Proof. exact (@lem4460310 A B K f (@I ((K -> B) -> K) i x)). Qed.
Lemma lem4460312 {A B K : Type'} (x : K -> A) (i : type803 B K) (x' : K -> B) : (term770 A B K x i x') = (term770 A B K x i x').
Proof. exact (eq_refl (term770 A B K x i x')). Qed.
Lemma lem4460313 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : (term772 A B K f x i x') = (term773 A B K f x i x').
Proof. exact (MK_COMB (@lem4460311 A B K f i x') (@lem4460312 A B K x i x')). Qed.
Lemma lem4460315 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460316 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4460315 A B f x). Qed.
Lemma lem4460317 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : (term773 A B K f x i x') = (term774 A B K f x i x').
Proof. exact (@lem4460316 A B (term746 A B K f i x') (term770 A B K x i x')). Qed.
Lemma lem4460318 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : (term772 A B K f x i x') = (term774 A B K f x i x').
Proof. exact (TRANS (@lem4460313 A B K f x i x') (@lem4460317 A B K f x i x')). Qed.
Lemma lem4460319 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : (term771 A B K f x i x') = (term774 A B K f x i x').
Proof. exact (TRANS (@lem4460307 A B K f x i x') (@lem4460318 A B K f x i x')). Qed.
Lemma lem4460320 {B K : Type'} (x : K -> B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4460325 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460326 {B K : Type'} (f : type803 B K) (x : K -> B) : (f x) = (@I ((K -> B) -> K) f x).
Proof. exact (@lem4460325 (K -> B) K f x). Qed.
Lemma lem4460328 {B K : Type'} (i : type803 B K) (x : K -> B) : (i x) = (@I ((K -> B) -> K) i x).
Proof. exact (@lem4460326 B K i x). Qed.
Lemma lem4460329 {B K : Type'} (i : type803 B K) (x : K -> B) : (term739 B K i x) = (term740 B K i x).
Proof. exact (MK_COMB (@lem4460320 B K x) (@lem4460328 B K i x)). Qed.
Lemma lem4460331 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460332 {B K : Type'} (f : K -> B) (x : K) : (f x) = (@I (K -> B) f x).
Proof. exact (@lem4460331 K B f x). Qed.
Lemma lem4460333 {B K : Type'} (i : type803 B K) (x : K -> B) : (term740 B K i x) = (term741 B K i x).
Proof. exact (@lem4460332 B K x (@I ((K -> B) -> K) i x)). Qed.
Lemma lem4460334 {B K : Type'} (i : type803 B K) (x : K -> B) : (term739 B K i x) = (term741 B K i x).
Proof. exact (TRANS (@lem4460329 B K i x) (@lem4460333 B K i x)). Qed.
Lemma lem4460335 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : (term775 A B K f x i x') = (term776 A B K f x i x').
Proof. exact (MK_COMB (@lem4460281 B) (@lem4460319 A B K f x i x')). Qed.
Lemma lem4460336 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : ((term771 A B K f x i x') = (term739 B K i x')) = ((term774 A B K f x i x') = (term741 B K i x')).
Proof. exact (MK_COMB (@lem4460335 A B K f x i x') (@lem4460334 B K i x')). Qed.
Lemma lem4460337 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : (term777 A B K f x i x') = (term778 A B K f x i x').
Proof. exact (MK_COMB (@lem4460280) (@lem4460336 A B K f x i x')). Qed.
Lemma lem4460338 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4460343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460344 {B K : Type'} (f : type803 B K) (x : K -> B) : (f x) = (@I ((K -> B) -> K) f x).
Proof. exact (@lem4460343 (K -> B) K f x). Qed.
Lemma lem4460346 {B K : Type'} (i : type803 B K) (x : K -> B) : (i x) = (@I ((K -> B) -> K) i x).
Proof. exact (@lem4460344 B K i x). Qed.
Lemma lem4460347 {B K : Type'} (k : K -> Prop) (i : type803 B K) (x : K -> B) : (term761 B K k i x) = (term762 B K k i x).
Proof. exact (MK_COMB (@lem4460338 K k) (@lem4460346 B K i x)). Qed.
Lemma lem4460349 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4460350 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4460349 K Prop f x). Qed.
Lemma lem4460351 {B K : Type'} (k : K -> Prop) (i : type803 B K) (x : K -> B) : (term762 B K k i x) = (term763 B K k i x).
Proof. exact (@lem4460350 K k (@I ((K -> B) -> K) i x)). Qed.
Lemma lem4460352 {B K : Type'} (k : K -> Prop) (i : type803 B K) (x : K -> B) : (term761 B K k i x) = (term763 B K k i x).
Proof. exact (TRANS (@lem4460347 B K k i x) (@lem4460351 B K k i x)). Qed.
Lemma lem4460353 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4460354 {B K : Type'} (k : K -> Prop) (i : type803 B K) (x : K -> B) : (term764 B K k i x) = (term765 B K k i x).
Proof. exact (MK_COMB (@lem4460353) (@lem4460352 B K k i x)). Qed.
Lemma lem4460355 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : (term779 A B K k f x i x') = (term780 A B K k f x i x').
Proof. exact (MK_COMB (@lem4460354 B K k i x') (@lem4460337 A B K f x i x')). Qed.
Lemma lem4460356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4460357 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : (term781 A B K k f x i x') = (term782 A B K k f x i x').
Proof. exact (MK_COMB (@lem4460356) (@lem4460355 A B K k f x i x')). Qed.
Lemma lem4460358 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term676 A B K x k f s i x') = (term783 A B K x k f s i x').
Proof. exact (MK_COMB (@lem4460357 A B K k f x i x') (@lem4460279 A B K k f s i x')). Qed.
Lemma lem4460359 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) : (term678 A B K x k f s i) = (term784 A B K x k f s i).
Proof. exact (fun_ext (fun x' : K -> B => @lem4460358 A B K x k f s i x')). Qed.
Lemma lem4460360 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4460361 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) : (term680 A B K x k f s i) = (term785 A B K x k f s i).
Proof. exact (MK_COMB (@lem4460360 B K) (@lem4460359 A B K x k f s i)). Qed.
Lemma lem4460362 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term785 A B K x k f s i.
Proof. exact (EQ_MP (@lem4460361 A B K x k f s i) (@lem4459926 A B K x k f s i h1)). Qed.
Lemma lem4460364 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term343 A B K s g _51538 f k x) : term727 A K k s x.
Proof. exact (proj1 (@lem4460185 A B K s g _51538 f k x h1)). Qed.
Lemma lem4460366 {A B K : Type'} (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term716 A B K _51538.
Proof. exact (proj1 (@lem4460095 A B K _51538 h1)). Qed.
Lemma lem4460368 {A : Type'} (P : Prop) (Q : A -> Prop) : (term786 A P Q) = (term787 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4460369 {A : Type'} (P : Prop) (Q : A -> Prop) : (term786 A P Q) = (term787 A P Q).
Proof. exact (@lem4460368 A P Q). Qed.
Lemma lem4460370 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term788 A B K k f s i x) = (term789 A B K k f s i x).
Proof. exact (@lem4460369 A (term763 B K k i x) (term758 A B K f s i x)). Qed.
Lemma lem4460371 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) (x' : A) : (term790 A B K f s i x x') = (term756 A B K f s i x x').
Proof. exact (eq_refl (term790 A B K f s i x x')). Qed.
Lemma lem4460372 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term791 A B K f s i x) = (term758 A B K f s i x).
Proof. exact (fun_ext (fun x' : A => @lem4460371 A B K f s i x x')). Qed.
Lemma lem4460373 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4460374 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term792 A B K f s i x) = (term760 A B K f s i x).
Proof. exact (MK_COMB (@lem4460373 A) (@lem4460372 A B K f s i x)). Qed.
Lemma lem4460375 {B K : Type'} (k : K -> Prop) (i : type803 B K) (x : K -> B) : (term765 B K k i x) = (term765 B K k i x).
Proof. exact (eq_refl (term765 B K k i x)). Qed.
Lemma lem4460376 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term788 A B K k f s i x) = (term767 A B K k f s i x).
Proof. exact (MK_COMB (@lem4460375 B K k i x) (@lem4460374 A B K f s i x)). Qed.
Lemma lem4460377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4460378 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term793 A B K k f s i x) = (term794 A B K k f s i x).
Proof. exact (MK_COMB (@lem4460377) (@lem4460376 A B K k f s i x)). Qed.
Lemma lem4460379 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) (x' : A) : (term790 A B K f s i x x') = (term756 A B K f s i x x').
Proof. exact (eq_refl (term790 A B K f s i x x')). Qed.
Lemma lem4460380 {B K : Type'} (k : K -> Prop) (i : type803 B K) (x : K -> B) : (term765 B K k i x) = (term765 B K k i x).
Proof. exact (eq_refl (term765 B K k i x)). Qed.
Lemma lem4460381 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) (x' : A) : (term795 A B K k f s i x x') = (term796 A B K k f s i x x').
Proof. exact (MK_COMB (@lem4460380 B K k i x) (@lem4460379 A B K f s i x x')). Qed.
Lemma lem4460382 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term797 A B K k f s i x) = (term798 A B K k f s i x).
Proof. exact (fun_ext (fun x' : A => @lem4460381 A B K k f s i x x')). Qed.
Lemma lem4460383 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4460384 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term789 A B K k f s i x) = (term799 A B K k f s i x).
Proof. exact (MK_COMB (@lem4460383 A) (@lem4460382 A B K k f s i x)). Qed.
Lemma lem4460385 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : ((term788 A B K k f s i x) = (term789 A B K k f s i x)) = ((term767 A B K k f s i x) = (term799 A B K k f s i x)).
Proof. exact (MK_COMB (@lem4460378 A B K k f s i x) (@lem4460384 A B K k f s i x)). Qed.
Lemma lem4460386 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term767 A B K k f s i x) = (term799 A B K k f s i x).
Proof. exact (EQ_MP (@lem4460385 A B K k f s i x) (@lem4460370 A B K k f s i x)). Qed.
Lemma lem4460387 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : (term782 A B K k f x i x') = (term782 A B K k f x i x').
Proof. exact (eq_refl (term782 A B K k f x i x')). Qed.
Lemma lem4460388 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term783 A B K x k f s i x') = (term800 A B K x k f s i x').
Proof. exact (MK_COMB (@lem4460387 A B K k f x i x') (@lem4460386 A B K k f s i x')). Qed.
Lemma lem4460390 {A : Type'} (P : Prop) (Q : A -> Prop) : (term801 A P Q) = (term802 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4460391 {A : Type'} (P : Prop) (Q : A -> Prop) : (term801 A P Q) = (term802 A P Q).
Proof. exact (@lem4460390 A P Q). Qed.
Lemma lem4460392 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term803 A B K x k f s i x') = (term804 A B K x k f s i x').
Proof. exact (@lem4460391 A (term780 A B K k f x i x') (term798 A B K k f s i x')). Qed.
Lemma lem4460393 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) (x' : A) : (term805 A B K k f s i x x') = (term796 A B K k f s i x x').
Proof. exact (eq_refl (term805 A B K k f s i x x')). Qed.
Lemma lem4460394 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term806 A B K k f s i x) = (term798 A B K k f s i x).
Proof. exact (fun_ext (fun x' : A => @lem4460393 A B K k f s i x x')). Qed.
Lemma lem4460395 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4460396 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) : (term807 A B K k f s i x) = (term799 A B K k f s i x).
Proof. exact (MK_COMB (@lem4460395 A) (@lem4460394 A B K k f s i x)). Qed.
Lemma lem4460397 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : (term782 A B K k f x i x') = (term782 A B K k f x i x').
Proof. exact (eq_refl (term782 A B K k f x i x')). Qed.
Lemma lem4460398 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term803 A B K x k f s i x') = (term800 A B K x k f s i x').
Proof. exact (MK_COMB (@lem4460397 A B K k f x i x') (@lem4460396 A B K k f s i x')). Qed.
Lemma lem4460399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4460400 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term808 A B K x k f s i x') = (term809 A B K x k f s i x').
Proof. exact (MK_COMB (@lem4460399) (@lem4460398 A B K x k f s i x')). Qed.
Lemma lem4460401 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x : K -> B) (x' : A) : (term805 A B K k f s i x x') = (term796 A B K k f s i x x').
Proof. exact (eq_refl (term805 A B K k f s i x x')). Qed.
Lemma lem4460402 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : type803 B K) (x' : K -> B) : (term782 A B K k f x i x') = (term782 A B K k f x i x').
Proof. exact (eq_refl (term782 A B K k f x i x')). Qed.
Lemma lem4460403 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) (x'' : A) : (term810 A B K x k f s i x' x'') = (term811 A B K x k f s i x' x'').
Proof. exact (MK_COMB (@lem4460402 A B K k f x i x') (@lem4460401 A B K k f s i x' x'')). Qed.
Lemma lem4460404 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term812 A B K x k f s i x') = (term813 A B K x k f s i x').
Proof. exact (fun_ext (fun x'' : A => @lem4460403 A B K x k f s i x' x'')). Qed.
Lemma lem4460405 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4460406 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term804 A B K x k f s i x') = (term814 A B K x k f s i x').
Proof. exact (MK_COMB (@lem4460405 A) (@lem4460404 A B K x k f s i x')). Qed.
Lemma lem4460407 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : ((term803 A B K x k f s i x') = (term804 A B K x k f s i x')) = ((term800 A B K x k f s i x') = (term814 A B K x k f s i x')).
Proof. exact (MK_COMB (@lem4460400 A B K x k f s i x') (@lem4460406 A B K x k f s i x')). Qed.
Lemma lem4460408 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term800 A B K x k f s i x') = (term814 A B K x k f s i x').
Proof. exact (EQ_MP (@lem4460407 A B K x k f s i x') (@lem4460392 A B K x k f s i x')). Qed.
Lemma lem4460409 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term783 A B K x k f s i x') = (term814 A B K x k f s i x').
Proof. exact (TRANS (@lem4460388 A B K x k f s i x') (@lem4460408 A B K x k f s i x')). Qed.
Lemma lem4460410 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) : (term784 A B K x k f s i) = (term815 A B K x k f s i).
Proof. exact (fun_ext (fun x' : K -> B => @lem4460409 A B K x k f s i x')). Qed.
Lemma lem4460411 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4460412 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) : (term785 A B K x k f s i) = (term816 A B K x k f s i).
Proof. exact (MK_COMB (@lem4460411 B K) (@lem4460410 A B K x k f s i)). Qed.
Lemma lem4460432 {A B K : Type'} (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) (x'' : A) : (term811 A B K x k f s i x' x'') = (term817 A B K k x f s i x' x'').
Proof. exact (@lem19490 (term763 B K k i x') (term780 A B K k f x i x') (term756 A B K f s i x' x'')). Qed.
Lemma lem4460439 {A B K : Type'} (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) (x'' : A) : (term818 A B K k x f s i x' x'') = (term819 A B K k x f s i x' x'').
Proof. exact (@lem19699 (term763 B K k i x') (term778 A B K f x i x') (term756 A B K f s i x' x'')). Qed.
Lemma lem4460446 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (k : K -> Prop) (i : type803 B K) (x' : K -> B) : (term820 A B K f x k i x') = (term821 A B K f x k i x').
Proof. exact (@lem19699 (term763 B K k i x') (term778 A B K f x i x') (term763 B K k i x')). Qed.
Lemma lem4460447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4460448 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (k : K -> Prop) (i : type803 B K) (x' : K -> B) : (term822 A B K f x k i x') = (term823 A B K f x k i x').
Proof. exact (MK_COMB (@lem4460447) (@lem4460446 A B K f x k i x')). Qed.
Lemma lem4460449 {A B K : Type'} (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) (x'' : A) : (term817 A B K k x f s i x' x'') = (term824 A B K k x f s i x' x'').
Proof. exact (MK_COMB (@lem4460448 A B K f x k i x') (@lem4460439 A B K k x f s i x' x'')). Qed.
Lemma lem4460451 {A B K : Type'} (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) (x'' : A) : (term811 A B K x k f s i x' x'') = (term824 A B K k x f s i x' x'').
Proof. exact (TRANS (@lem4460432 A B K k x f s i x' x'') (@lem4460449 A B K k x f s i x' x'')). Qed.
Lemma lem4460452 {A B K : Type'} (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term813 A B K x k f s i x') = (term825 A B K k x f s i x').
Proof. exact (fun_ext (fun x'' : A => @lem4460451 A B K k x f s i x' x'')). Qed.
Lemma lem4460453 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4460454 {A B K : Type'} (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (x' : K -> B) : (term814 A B K x k f s i x') = (term826 A B K k x f s i x').
Proof. exact (MK_COMB (@lem4460453 A) (@lem4460452 A B K k x f s i x')). Qed.
Lemma lem4460455 {A B K : Type'} (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) : (term815 A B K x k f s i) = (term827 A B K k x f s i).
Proof. exact (fun_ext (fun x' : K -> B => @lem4460454 A B K k x f s i x')). Qed.
Lemma lem4460456 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4460457 {A B K : Type'} (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) : (term816 A B K x k f s i) = (term828 A B K k x f s i).
Proof. exact (MK_COMB (@lem4460456 B K) (@lem4460455 A B K k x f s i)). Qed.
Lemma lem4460458 {A B K : Type'} (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) : (term785 A B K x k f s i) = (term828 A B K k x f s i).
Proof. exact (TRANS (@lem4460412 A B K x k f s i) (@lem4460457 A B K k x f s i)). Qed.
Lemma lem4460459 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term828 A B K k x f s i.
Proof. exact (EQ_MP (@lem4460458 A B K k x f s i) (@lem4460362 A B K x k f s i h1)). Qed.
Lemma lem4460467 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term725 A K k s x i) = (term725 A K k s x i).
Proof. exact (eq_refl (term725 A K k s x i)). Qed.
Lemma lem4460468 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term726 A K k s x) = (term726 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4460467 A K k s x i)). Qed.
Lemma lem4460469 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4460471 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term727 A K k s x) = (term727 A K k s x).
Proof. exact (MK_COMB (@lem4460469 K) (@lem4460468 A K k s x)). Qed.
Lemma lem4460472 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term343 A B K s g _51538 f k x) : term727 A K k s x.
Proof. exact (EQ_MP (@lem4460471 A K k s x) (@lem4460364 A B K s g _51538 f k x h1)). Qed.
Lemma lem4460484 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) (i : K) : (term708 A B K _51538 k f x i) = (term708 A B K _51538 k f x i).
Proof. exact (eq_refl (term708 A B K _51538 k f x i)). Qed.
Lemma lem4460485 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term709 A B K _51538 k f x) = (term709 A B K _51538 k f x).
Proof. exact (fun_ext (fun i : K => @lem4460484 A B K _51538 k f x i)). Qed.
Lemma lem4460486 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4460487 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) (x : K -> A) : (term710 A B K _51538 k f x) = (term710 A B K _51538 k f x).
Proof. exact (MK_COMB (@lem4460486 K) (@lem4460485 A B K _51538 k f x)). Qed.
Lemma lem4460488 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term711 A B K _51538 k f) = (term711 A B K _51538 k f).
Proof. exact (fun_ext (fun x : K -> A => @lem4460487 A B K _51538 k f x)). Qed.
Lemma lem4460489 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4460490 {A B K : Type'} (_51538 : type868 A B K) (k : K -> Prop) (f : type1514 A B K) : (term712 A B K _51538 k f) = (term712 A B K _51538 k f).
Proof. exact (MK_COMB (@lem4460489 A K) (@lem4460488 A B K _51538 k f)). Qed.
Lemma lem4460491 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term713 A B K _51538 f) = (term713 A B K _51538 f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4460490 A B K _51538 k f)). Qed.
Lemma lem4460492 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4460493 {A B K : Type'} (_51538 : type868 A B K) (f : type1514 A B K) : (term714 A B K _51538 f) = (term714 A B K _51538 f).
Proof. exact (MK_COMB (@lem4460492 K) (@lem4460491 A B K _51538 f)). Qed.
Lemma lem4460494 {A B K : Type'} (_51538 : type868 A B K) : (term715 A B K _51538) = (term715 A B K _51538).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4460493 A B K _51538 f)). Qed.
Lemma lem4460495 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4460497 {A B K : Type'} (_51538 : type868 A B K) : (term716 A B K _51538) = (term716 A B K _51538).
Proof. exact (MK_COMB (@lem4460495 A B K) (@lem4460494 A B K _51538)). Qed.
Lemma lem4460498 {A B K : Type'} (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term716 A B K _51538.
Proof. exact (EQ_MP (@lem4460497 A B K _51538) (@lem4460366 A B K _51538 h1)). Qed.
Lemma lem4460521 {A B K : Type'} (_51541 : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term829 A B K k x f s i _51541.
Proof. exact (@lem4460459 A B K x k f s i h1 _51541). Qed.
Lemma lem4460522 {A B K : Type'} (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51541 : K -> B) : (term829 A B K k x f s i _51541) = (term826 A B K k x f s i _51541).
Proof. exact (eq_refl (term829 A B K k x f s i _51541)). Qed.
Lemma lem4460523 {A B K : Type'} (_51541 : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term826 A B K k x f s i _51541.
Proof. exact (EQ_MP (@lem4460522 A B K k x f s i _51541) (@lem4460521 A B K _51541 x k f s i h1)). Qed.
Lemma lem4460524 {A B K : Type'} (_51541 : K -> B) (_51542 : A) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term830 A B K k x f s i _51541 _51542.
Proof. exact (@lem4460523 A B K _51541 x k f s i h1 _51542). Qed.
Lemma lem4460525 {A B K : Type'} (k : K -> Prop) (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51541 : K -> B) (_51542 : A) : (term830 A B K k x f s i _51541 _51542) = (term824 A B K k x f s i _51541 _51542).
Proof. exact (eq_refl (term830 A B K k x f s i _51541 _51542)). Qed.
Lemma lem4460526 {A B K : Type'} (_51541 : K -> B) (_51542 : A) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term824 A B K k x f s i _51541 _51542.
Proof. exact (EQ_MP (@lem4460525 A B K k x f s i _51541 _51542) (@lem4460524 A B K _51541 _51542 x k f s i h1)). Qed.
Lemma lem4460527 {A B K : Type'} (_51543 : K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term343 A B K s g _51538 f k x) : term831 A K k s x _51543.
Proof. exact (@lem4460472 A B K s g _51538 f k x h1 _51543). Qed.
Lemma lem4460528 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (_51543 : K) : (term831 A K k s x _51543) = (term725 A K k s x _51543).
Proof. exact (eq_refl (term831 A K k s x _51543)). Qed.
Lemma lem4460530 {A B K : Type'} (_51544 : type1514 A B K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term832 A B K _51538 _51544.
Proof. exact (@lem4460498 A B K _51538 h1 _51544). Qed.
Lemma lem4460531 {A B K : Type'} (_51538 : type868 A B K) (_51544 : type1514 A B K) : (term832 A B K _51538 _51544) = (term714 A B K _51538 _51544).
Proof. exact (eq_refl (term832 A B K _51538 _51544)). Qed.
Lemma lem4460532 {A B K : Type'} (_51544 : type1514 A B K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term714 A B K _51538 _51544.
Proof. exact (EQ_MP (@lem4460531 A B K _51538 _51544) (@lem4460530 A B K _51544 _51538 h1)). Qed.
Lemma lem4460533 {A B K : Type'} (_51544 : type1514 A B K) (_51545 : K -> Prop) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term833 A B K _51538 _51544 _51545.
Proof. exact (@lem4460532 A B K _51544 _51538 h1 _51545). Qed.
Lemma lem4460534 {A B K : Type'} (_51538 : type868 A B K) (_51545 : K -> Prop) (_51544 : type1514 A B K) : (term833 A B K _51538 _51544 _51545) = (term712 A B K _51538 _51545 _51544).
Proof. exact (eq_refl (term833 A B K _51538 _51544 _51545)). Qed.
Lemma lem4460535 {A B K : Type'} (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term712 A B K _51538 _51545 _51544.
Proof. exact (EQ_MP (@lem4460534 A B K _51538 _51545 _51544) (@lem4460533 A B K _51544 _51545 _51538 h1)). Qed.
Lemma lem4460536 {A B K : Type'} (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term834 A B K _51538 _51545 _51544 _51546.
Proof. exact (@lem4460535 A B K _51545 _51544 _51538 h1 _51546). Qed.
Lemma lem4460537 {A B K : Type'} (_51538 : type868 A B K) (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) : (term834 A B K _51538 _51545 _51544 _51546) = (term710 A B K _51538 _51545 _51544 _51546).
Proof. exact (eq_refl (term834 A B K _51538 _51545 _51544 _51546)). Qed.
Lemma lem4460538 {A B K : Type'} (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term710 A B K _51538 _51545 _51544 _51546.
Proof. exact (EQ_MP (@lem4460537 A B K _51538 _51545 _51544 _51546) (@lem4460536 A B K _51545 _51544 _51546 _51538 h1)). Qed.
Lemma lem4460539 {A B K : Type'} (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51547 : K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term835 A B K _51538 _51545 _51544 _51546 _51547.
Proof. exact (@lem4460538 A B K _51545 _51544 _51546 _51538 h1 _51547). Qed.
Lemma lem4460540 {A B K : Type'} (_51538 : type868 A B K) (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51547 : K) : (term835 A B K _51538 _51545 _51544 _51546 _51547) = (term708 A B K _51538 _51545 _51544 _51546 _51547).
Proof. exact (eq_refl (term835 A B K _51538 _51545 _51544 _51546 _51547)). Qed.
Lemma lem4460554 {A B K : Type'} (_51541 : K -> B) (_51542 : A) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term819 A B K k x f s i _51541 _51542.
Proof. exact (proj2 (@lem4460526 A B K _51541 _51542 x k f s i h1)). Qed.
Lemma lem4460555 {A B K : Type'} (_51541 : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term821 A B K f x k i _51541.
Proof. exact (proj1 (@lem4460526 A B K _51541 (@el A) x k f s i h1)). Qed.
Lemma lem4460639 {A B K : Type'} (_51543 : K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term343 A B K s g _51538 f k x) : term725 A K k s x _51543.
Proof. exact (EQ_MP (@lem4460528 A K k s x _51543) (@lem4460527 A B K _51543 s g _51538 f k x h1)). Qed.
Lemma lem4460653 {A B K : Type'} (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51547 : K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term708 A B K _51538 _51545 _51544 _51546 _51547.
Proof. exact (EQ_MP (@lem4460540 A B K _51538 _51545 _51544 _51546 _51547) (@lem4460539 A B K _51545 _51544 _51546 _51547 _51538 h1)). Qed.
Lemma lem4460695 {A B K : Type'} (_51541 : K -> B) (_51542 : A) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term836 A B K x f s i _51541 _51542.
Proof. exact (proj2 (@lem4460554 A B K _51541 _51542 x k f s i h1)). Qed.
Lemma lem4460709 {A B K : Type'} (_51541 : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term837 B K k i _51541.
Proof. exact (proj1 (@lem4460555 A B K _51541 x k f s i h1)). Qed.
Lemma lem4460908 {B : Type'} (x : B) (y : B) (z : B) : term838 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem4460927 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term839 A B K i _51538 f k x) : term839 A B K i _51538 f k x.
Proof. exact (h1). Qed.
Lemma lem4460928 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term839 A B K i _51538 f k x) : term840 A B K i _51538 f k x.
Proof. exact (fun h0 : term841 A B K i _51538 f k x => @lem4460927 A B K i _51538 f k x h1). Qed.
Lemma lem4460930 (p : Prop) : (term842 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4460931 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term840 A B K i _51538 f k x) = (term839 A B K i _51538 f k x).
Proof. exact (@lem4460930 (term841 A B K i _51538 f k x)). Qed.
Lemma lem4460932 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term839 A B K i _51538 f k x) : term839 A B K i _51538 f k x.
Proof. exact (EQ_MP (@lem4460931 A B K i _51538 f k x) (@lem4460928 A B K i _51538 f k x h1)). Qed.
Lemma lem4460934 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4460935 (x : Prop) : (x = x) = True.
Proof. exact (@lem4460934 Prop x). Qed.
Lemma lem4460936 {B K : Type'} (k : K -> Prop) (i : type803 B K) (_51541 : K -> B) : ((term837 B K k i _51541) = (term837 B K k i _51541)) = True.
Proof. exact (@lem4460935 (term837 B K k i _51541)). Qed.
Lemma lem4460937 {B K : Type'} (k : K -> Prop) (i : type803 B K) (_51541 : K -> B) : True = ((term837 B K k i _51541) = (term837 B K k i _51541)).
Proof. exact (SYM (@lem4460936 B K k i _51541)). Qed.
Lemma lem4460938 {B K : Type'} (k : K -> Prop) (i : type803 B K) (_51541 : K -> B) : (term837 B K k i _51541) = (term837 B K k i _51541).
Proof. exact (EQ_MP (@lem4460937 B K k i _51541) (@lem0)). Qed.
Lemma lem4460939 {A B K : Type'} (_51541 : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term837 B K k i _51541.
Proof. exact (EQ_MP (@lem4460938 B K k i _51541) (@lem4460709 A B K _51541 x k f s i h1)). Qed.
Lemma lem4460941 (b : Prop) (a : Prop) : (a \/ b) = (term843 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4460944 {B K : Type'} (k : K -> Prop) (i : type803 B K) (_51541 : K -> B) : (term837 B K k i _51541) = (term844 B K k i _51541).
Proof. exact (@lem4460941 (term763 B K k i _51541) (term763 B K k i _51541)). Qed.
Lemma lem4460947 {A B K : Type'} (_51541 : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term844 B K k i _51541.
Proof. exact (EQ_MP (@lem4460944 B K k i _51541) (@lem4460939 A B K _51541 x k f s i h1)). Qed.
Lemma lem4460948 {A B K : Type'} (_51541 : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term844 B K k i _51541.
Proof. exact (@lem4460947 A B K _51541 x k f s i h1). Qed.
Lemma lem4460949 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term845 A B K i _51538 f k x.
Proof. exact (@lem4460948 A B K (term686 A B K _51538 f k x) x k f s i h1). Qed.
Lemma lem4460952 {A B K : Type'} (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term680 A B K x k f s i) (h2 : term839 A B K i _51538 f k x) : term841 A B K i _51538 f k x.
Proof. exact (@lem4460949 A B K _51538 x k f s i h1 (@lem4460932 A B K i _51538 f k x h2)). Qed.
Lemma lem4460953 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term845 A B K i _51538 f k x.
Proof. exact (fun h0 : term839 A B K i _51538 f k x => @lem4460952 A B K s i _51538 f k x h1 h0). Qed.
Lemma lem4460955 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4460956 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term845 A B K i _51538 f k x) = (term841 A B K i _51538 f k x).
Proof. exact (@lem4460955 (term841 A B K i _51538 f k x)). Qed.
Lemma lem4460957 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term841 A B K i _51538 f k x.
Proof. exact (EQ_MP (@lem4460956 A B K i _51538 f k x) (@lem4460953 A B K _51538 x k f s i h1)). Qed.
Lemma lem4460963 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4460964 {A B K : Type'} (_51538 : type868 A B K) (_51544 : type1514 A B K) (_51546 : K -> A) (_51545 : K -> Prop) (_51547 : K) : (term708 A B K _51538 _51545 _51544 _51546 _51547) = (term847 A B K _51538 _51544 _51546 _51545 _51547).
Proof. exact (@lem4460963 ((term688 A B K _51538 _51544 _51545 _51546 _51547) = (term704 A B K _51544 _51546 _51547)) (term705 K _51545 _51547)). Qed.
Lemma lem4460972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4460973 {A B K : Type'} (_51538 : type868 A B K) (_51544 : type1514 A B K) (_51546 : K -> A) (_51545 : K -> Prop) (_51547 : K) : (term848 A B K _51538 _51545 _51544 _51546 _51547) = (term849 A B K _51538 _51544 _51546 _51545 _51547).
Proof. exact (MK_COMB (@lem4460972) (@lem4460964 A B K _51538 _51544 _51546 _51545 _51547)). Qed.
Lemma lem4460981 {A B K : Type'} (_51538 : type868 A B K) (_51544 : type1514 A B K) (_51546 : K -> A) (_51545 : K -> Prop) (_51547 : K) : (term847 A B K _51538 _51544 _51546 _51545 _51547) = (term847 A B K _51538 _51544 _51546 _51545 _51547).
Proof. exact (eq_refl (term847 A B K _51538 _51544 _51546 _51545 _51547)). Qed.
Lemma lem4460982 {A B K : Type'} (_51538 : type868 A B K) (_51544 : type1514 A B K) (_51546 : K -> A) (_51545 : K -> Prop) (_51547 : K) : ((term708 A B K _51538 _51545 _51544 _51546 _51547) = (term847 A B K _51538 _51544 _51546 _51545 _51547)) = ((term847 A B K _51538 _51544 _51546 _51545 _51547) = (term847 A B K _51538 _51544 _51546 _51545 _51547)).
Proof. exact (MK_COMB (@lem4460973 A B K _51538 _51544 _51546 _51545 _51547) (@lem4460981 A B K _51538 _51544 _51546 _51545 _51547)). Qed.
Lemma lem4460984 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4460985 (x : Prop) : (x = x) = True.
Proof. exact (@lem4460984 Prop x). Qed.
Lemma lem4460986 {A B K : Type'} (_51538 : type868 A B K) (_51544 : type1514 A B K) (_51546 : K -> A) (_51545 : K -> Prop) (_51547 : K) : ((term847 A B K _51538 _51544 _51546 _51545 _51547) = (term847 A B K _51538 _51544 _51546 _51545 _51547)) = True.
Proof. exact (@lem4460985 (term847 A B K _51538 _51544 _51546 _51545 _51547)). Qed.
Lemma lem4460987 {A B K : Type'} (_51538 : type868 A B K) (_51544 : type1514 A B K) (_51546 : K -> A) (_51545 : K -> Prop) (_51547 : K) : ((term708 A B K _51538 _51545 _51544 _51546 _51547) = (term847 A B K _51538 _51544 _51546 _51545 _51547)) = True.
Proof. exact (TRANS (@lem4460982 A B K _51538 _51544 _51546 _51545 _51547) (@lem4460986 A B K _51538 _51544 _51546 _51545 _51547)). Qed.
Lemma lem4460988 {A B K : Type'} (_51538 : type868 A B K) (_51544 : type1514 A B K) (_51546 : K -> A) (_51545 : K -> Prop) (_51547 : K) : True = ((term708 A B K _51538 _51545 _51544 _51546 _51547) = (term847 A B K _51538 _51544 _51546 _51545 _51547)).
Proof. exact (SYM (@lem4460987 A B K _51538 _51544 _51546 _51545 _51547)). Qed.
Lemma lem4460989 {A B K : Type'} (_51538 : type868 A B K) (_51544 : type1514 A B K) (_51546 : K -> A) (_51545 : K -> Prop) (_51547 : K) : (term708 A B K _51538 _51545 _51544 _51546 _51547) = (term847 A B K _51538 _51544 _51546 _51545 _51547).
Proof. exact (EQ_MP (@lem4460988 A B K _51538 _51544 _51546 _51545 _51547) (@lem0)). Qed.
Lemma lem4460990 {A B K : Type'} (_51544 : type1514 A B K) (_51546 : K -> A) (_51545 : K -> Prop) (_51547 : K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term847 A B K _51538 _51544 _51546 _51545 _51547.
Proof. exact (EQ_MP (@lem4460989 A B K _51538 _51544 _51546 _51545 _51547) (@lem4460653 A B K _51545 _51544 _51546 _51547 _51538 h1)). Qed.
Lemma lem4460992 (b : Prop) (a : Prop) : (a \/ b) = (term843 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4460993 {A B K : Type'} (_51538 : type868 A B K) (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51547 : K) : (term847 A B K _51538 _51544 _51546 _51545 _51547) = (term850 A B K _51538 _51545 _51544 _51546 _51547).
Proof. exact (@lem4460992 (term705 K _51545 _51547) ((term688 A B K _51538 _51544 _51545 _51546 _51547) = (term704 A B K _51544 _51546 _51547))). Qed.
Lemma lem4460995 (a : Prop) : (term312 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4460996 {K : Type'} (_51545 : K -> Prop) (_51547 : K) : (term851 K _51545 _51547) = (@I (K -> Prop) _51545 _51547).
Proof. exact (@lem4460995 (@I (K -> Prop) _51545 _51547)). Qed.
Lemma lem4460997 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4460998 {K : Type'} (_51545 : K -> Prop) (_51547 : K) : (term852 K _51545 _51547) = (term853 K _51545 _51547).
Proof. exact (MK_COMB (@lem4460997) (@lem4460996 K _51545 _51547)). Qed.
Lemma lem4460999 {A B K : Type'} (_51538 : type868 A B K) (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51547 : K) : ((term688 A B K _51538 _51544 _51545 _51546 _51547) = (term704 A B K _51544 _51546 _51547)) = ((term688 A B K _51538 _51544 _51545 _51546 _51547) = (term704 A B K _51544 _51546 _51547)).
Proof. exact (eq_refl ((term688 A B K _51538 _51544 _51545 _51546 _51547) = (term704 A B K _51544 _51546 _51547))). Qed.
Lemma lem4461000 {A B K : Type'} (_51538 : type868 A B K) (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51547 : K) : (term850 A B K _51538 _51545 _51544 _51546 _51547) = (term854 A B K _51538 _51545 _51544 _51546 _51547).
Proof. exact (MK_COMB (@lem4460998 K _51545 _51547) (@lem4460999 A B K _51538 _51545 _51544 _51546 _51547)). Qed.
Lemma lem4461001 {A B K : Type'} (_51538 : type868 A B K) (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51547 : K) : (term847 A B K _51538 _51544 _51546 _51545 _51547) = (term854 A B K _51538 _51545 _51544 _51546 _51547).
Proof. exact (TRANS (@lem4460993 A B K _51538 _51545 _51544 _51546 _51547) (@lem4461000 A B K _51538 _51545 _51544 _51546 _51547)). Qed.
Lemma lem4461004 {A B K : Type'} (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51547 : K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term854 A B K _51538 _51545 _51544 _51546 _51547.
Proof. exact (EQ_MP (@lem4461001 A B K _51538 _51545 _51544 _51546 _51547) (@lem4460990 A B K _51544 _51546 _51545 _51547 _51538 h1)). Qed.
Lemma lem4461005 {A B K : Type'} (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51547 : K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term854 A B K _51538 _51545 _51544 _51546 _51547.
Proof. exact (@lem4461004 A B K _51545 _51544 _51546 _51547 _51538 h1). Qed.
Lemma lem4461006 {A B K : Type'} (_51544 : type1514 A B K) (_51546 : K -> A) (i : type803 B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term855 A B K _51544 _51546 i _51538 f k x.
Proof. exact (@lem4461005 A B K k _51544 _51546 (term856 A B K i _51538 f k x) _51538 h1). Qed.
Lemma lem4461009 {A B K : Type'} (_51544 : type1514 A B K) (_51546 : K -> A) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : (term857 A B K _51544 _51546 i _51538 f k x) = (term858 A B K _51544 _51546 i _51538 f k x).
Proof. exact (@lem4461006 A B K _51544 _51546 i f k x _51538 h2 (@lem4460957 A B K _51538 x k f s i h1)). Qed.
Lemma lem4461010 {A B K : Type'} (_51544 : type1514 A B K) (_51546 : K -> A) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : (term857 A B K _51544 _51546 i _51538 f k x) = (term858 A B K _51544 _51546 i _51538 f k x).
Proof. exact (@lem4461009 A B K _51544 _51546 x k f s i _51538 h1 h2). Qed.
Lemma lem4461011 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : (term859 A B K i _51538 f k x) = (term860 A B K i _51538 f k x).
Proof. exact (@lem4461010 A B K f x x k f s i _51538 h1 h2). Qed.
Lemma lem4461012 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : term861 A B K i _51538 f k x.
Proof. exact (fun h0 : term862 A B K i _51538 f k x => @lem4461011 A B K x k f s i _51538 h1 h2). Qed.
Lemma lem4461014 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4461015 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term861 A B K i _51538 f k x) = ((term859 A B K i _51538 f k x) = (term860 A B K i _51538 f k x)).
Proof. exact (@lem4461014 ((term859 A B K i _51538 f k x) = (term860 A B K i _51538 f k x))). Qed.
Lemma lem4461016 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : (term859 A B K i _51538 f k x) = (term860 A B K i _51538 f k x).
Proof. exact (EQ_MP (@lem4461015 A B K i _51538 f k x) (@lem4461012 A B K x k f s i _51538 h1 h2)). Qed.
Lemma lem4461018 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4461019 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4461018 B x). Qed.
Lemma lem4461020 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term859 A B K i _51538 f k x) = (term859 A B K i _51538 f k x).
Proof. exact (@lem4461019 B (term859 A B K i _51538 f k x)). Qed.
Lemma lem4461021 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : term863 A B K i _51538 f k x.
Proof. exact (fun h0 : term864 A B K i _51538 f k x => @lem4461020 A B K i _51538 f k x). Qed.
Lemma lem4461023 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4461024 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term863 A B K i _51538 f k x) = ((term859 A B K i _51538 f k x) = (term859 A B K i _51538 f k x)).
Proof. exact (@lem4461023 ((term859 A B K i _51538 f k x) = (term859 A B K i _51538 f k x))). Qed.
Lemma lem4461025 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term859 A B K i _51538 f k x) = (term859 A B K i _51538 f k x).
Proof. exact (EQ_MP (@lem4461024 A B K i _51538 f k x) (@lem4461021 A B K i _51538 f k x)). Qed.
Lemma lem4461043 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4461044 {B : Type'} (y : B) (x : B) (z : B) : (term865 B x y z) = (term866 B y x z).
Proof. exact (@lem4461043 (y = z) (term867 B x z)). Qed.
Lemma lem4461054 {B : Type'} (x : B) (y : B) : (term868 B x y) = (term868 B x y).
Proof. exact (eq_refl (term868 B x y)). Qed.
Lemma lem4461055 {B : Type'} (y : B) (x : B) (z : B) : (term838 B x y z) = (term869 B y x z).
Proof. exact (MK_COMB (@lem4461054 B x y) (@lem4461044 B y x z)). Qed.
Lemma lem4461059 (q : Prop) (p : Prop) (r : Prop) : (term870 p q r) = (term870 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4461060 {B : Type'} (y : B) (x : B) (z : B) : (term869 B y x z) = (term871 B y x z).
Proof. exact (@lem4461059 (y = z) (term867 B x y) (term867 B x z)). Qed.
Lemma lem4461082 {B : Type'} (y : B) (x : B) (z : B) : (term838 B x y z) = (term871 B y x z).
Proof. exact (TRANS (@lem4461055 B y x z) (@lem4461060 B y x z)). Qed.
Lemma lem4461083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4461084 {B : Type'} (y : B) (x : B) (z : B) : (term872 B x y z) = (term873 B y x z).
Proof. exact (MK_COMB (@lem4461083) (@lem4461082 B y x z)). Qed.
Lemma lem4461106 {B : Type'} (y : B) (x : B) (z : B) : (term871 B y x z) = (term871 B y x z).
Proof. exact (eq_refl (term871 B y x z)). Qed.
Lemma lem4461107 {B : Type'} (y : B) (x : B) (z : B) : ((term838 B x y z) = (term871 B y x z)) = ((term871 B y x z) = (term871 B y x z)).
Proof. exact (MK_COMB (@lem4461084 B y x z) (@lem4461106 B y x z)). Qed.
Lemma lem4461109 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4461110 (x : Prop) : (x = x) = True.
Proof. exact (@lem4461109 Prop x). Qed.
Lemma lem4461111 {B : Type'} (y : B) (x : B) (z : B) : ((term871 B y x z) = (term871 B y x z)) = True.
Proof. exact (@lem4461110 (term871 B y x z)). Qed.
Lemma lem4461112 {B : Type'} (y : B) (x : B) (z : B) : ((term838 B x y z) = (term871 B y x z)) = True.
Proof. exact (TRANS (@lem4461107 B y x z) (@lem4461111 B y x z)). Qed.
Lemma lem4461113 {B : Type'} (y : B) (x : B) (z : B) : True = ((term838 B x y z) = (term871 B y x z)).
Proof. exact (SYM (@lem4461112 B y x z)). Qed.
Lemma lem4461114 {B : Type'} (y : B) (x : B) (z : B) : (term838 B x y z) = (term871 B y x z).
Proof. exact (EQ_MP (@lem4461113 B y x z) (@lem0)). Qed.
Lemma lem4461115 {B : Type'} (y : B) (x : B) (z : B) : term871 B y x z.
Proof. exact (EQ_MP (@lem4461114 B y x z) (@lem4460908 B x y z)). Qed.
Lemma lem4461117 (b : Prop) (a : Prop) : (a \/ b) = (term843 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4461118 {B : Type'} (x : B) (y : B) (z : B) : (term871 B y x z) = (term874 B x y z).
Proof. exact (@lem4461117 (term875 B y x z) (y = z)). Qed.
Lemma lem4461120 (a : Prop) (b : Prop) : (term876 a b) = (term877 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4461121 {B : Type'} (y : B) (x : B) (z : B) : (term878 B y x z) = (term879 B y x z).
Proof. exact (@lem4461120 (term867 B x y) (term867 B x z)). Qed.
Lemma lem4461123 (a : Prop) : (term312 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4461124 {B : Type'} (x : B) (y : B) : (term880 B x y) = (x = y).
Proof. exact (@lem4461123 (x = y)). Qed.
Lemma lem4461125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4461126 {B : Type'} (x : B) (y : B) : (term881 B x y) = (term882 B x y).
Proof. exact (MK_COMB (@lem4461125) (@lem4461124 B x y)). Qed.
Lemma lem4461128 (a : Prop) : (term312 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4461129 {B : Type'} (x : B) (z : B) : (term880 B x z) = (x = z).
Proof. exact (@lem4461128 (x = z)). Qed.
Lemma lem4461130 {B : Type'} (y : B) (x : B) (z : B) : (term879 B y x z) = (term883 B y x z).
Proof. exact (MK_COMB (@lem4461126 B x y) (@lem4461129 B x z)). Qed.
Lemma lem4461131 {B : Type'} (y : B) (x : B) (z : B) : (term878 B y x z) = (term883 B y x z).
Proof. exact (TRANS (@lem4461121 B y x z) (@lem4461130 B y x z)). Qed.
Lemma lem4461132 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4461133 {B : Type'} (y : B) (x : B) (z : B) : (term884 B y x z) = (term885 B y x z).
Proof. exact (MK_COMB (@lem4461132) (@lem4461131 B y x z)). Qed.
Lemma lem4461134 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4461135 {B : Type'} (x : B) (y : B) (z : B) : (term874 B x y z) = (term886 B x y z).
Proof. exact (MK_COMB (@lem4461133 B y x z) (@lem4461134 B y z)). Qed.
Lemma lem4461136 {B : Type'} (x : B) (y : B) (z : B) : (term871 B y x z) = (term886 B x y z).
Proof. exact (TRANS (@lem4461118 B x y z) (@lem4461135 B x y z)). Qed.
Lemma lem4461138 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : term887 A B K i _51538 f k x.
Proof. exact (conj (@lem4461016 A B K x k f s i _51538 h1 h2) (@lem4461025 A B K i _51538 f k x)). Qed.
Lemma lem4461140 {B : Type'} (x : B) (y : B) (z : B) : term886 B x y z.
Proof. exact (EQ_MP (@lem4461136 B x y z) (@lem4461115 B y x z)). Qed.
Lemma lem4461141 {B : Type'} (x : B) (y : B) (z : B) : term886 B x y z.
Proof. exact (@lem4461140 B x y z). Qed.
Lemma lem4461142 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : term888 A B K i _51538 f k x.
Proof. exact (@lem4461141 B (term859 A B K i _51538 f k x) (term860 A B K i _51538 f k x) (term859 A B K i _51538 f k x)). Qed.
Lemma lem4461145 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : (term860 A B K i _51538 f k x) = (term859 A B K i _51538 f k x).
Proof. exact (@lem4461142 A B K i _51538 f k x (@lem4461138 A B K x k f s i _51538 h1 h2)). Qed.
Lemma lem4461146 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : term889 A B K i _51538 f k x.
Proof. exact (fun h0 : term890 A B K i _51538 f k x => @lem4461145 A B K x k f s i _51538 h1 h2). Qed.
Lemma lem4461148 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4461149 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term889 A B K i _51538 f k x) = ((term860 A B K i _51538 f k x) = (term859 A B K i _51538 f k x)).
Proof. exact (@lem4461148 ((term860 A B K i _51538 f k x) = (term859 A B K i _51538 f k x))). Qed.
Lemma lem4461150 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : (term860 A B K i _51538 f k x) = (term859 A B K i _51538 f k x).
Proof. exact (EQ_MP (@lem4461149 A B K i _51538 f k x) (@lem4461146 A B K x k f s i _51538 h1 h2)). Qed.
Lemma lem4461153 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term839 A B K i _51538 f k x) : term839 A B K i _51538 f k x.
Proof. exact (h1). Qed.
Lemma lem4461154 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term839 A B K i _51538 f k x) : term840 A B K i _51538 f k x.
Proof. exact (fun h0 : term841 A B K i _51538 f k x => @lem4461153 A B K i _51538 f k x h1). Qed.
Lemma lem4461156 (p : Prop) : (term842 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4461157 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term840 A B K i _51538 f k x) = (term839 A B K i _51538 f k x).
Proof. exact (@lem4461156 (term841 A B K i _51538 f k x)). Qed.
Lemma lem4461158 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term839 A B K i _51538 f k x) : term839 A B K i _51538 f k x.
Proof. exact (EQ_MP (@lem4461157 A B K i _51538 f k x) (@lem4461154 A B K i _51538 f k x h1)). Qed.
Lemma lem4461160 {A B K : Type'} (_51541 : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term844 B K k i _51541.
Proof. exact (EQ_MP (@lem4460944 B K k i _51541) (@lem4460939 A B K _51541 x k f s i h1)). Qed.
Lemma lem4461161 {A B K : Type'} (_51541 : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term844 B K k i _51541.
Proof. exact (@lem4461160 A B K _51541 x k f s i h1). Qed.
Lemma lem4461162 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term845 A B K i _51538 f k x.
Proof. exact (@lem4461161 A B K (term686 A B K _51538 f k x) x k f s i h1). Qed.
Lemma lem4461165 {A B K : Type'} (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term680 A B K x k f s i) (h2 : term839 A B K i _51538 f k x) : term841 A B K i _51538 f k x.
Proof. exact (@lem4461162 A B K _51538 x k f s i h1 (@lem4461158 A B K i _51538 f k x h2)). Qed.
Lemma lem4461166 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term845 A B K i _51538 f k x.
Proof. exact (fun h0 : term839 A B K i _51538 f k x => @lem4461165 A B K s i _51538 f k x h1 h0). Qed.
Lemma lem4461168 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4461169 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term845 A B K i _51538 f k x) = (term841 A B K i _51538 f k x).
Proof. exact (@lem4461168 (term841 A B K i _51538 f k x)). Qed.
Lemma lem4461170 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term841 A B K i _51538 f k x.
Proof. exact (EQ_MP (@lem4461169 A B K i _51538 f k x) (@lem4461166 A B K _51538 x k f s i h1)). Qed.
Lemma lem4461172 {A B K : Type'} (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51547 : K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term854 A B K _51538 _51545 _51544 _51546 _51547.
Proof. exact (EQ_MP (@lem4461001 A B K _51538 _51545 _51544 _51546 _51547) (@lem4460990 A B K _51544 _51546 _51545 _51547 _51538 h1)). Qed.
Lemma lem4461173 {A B K : Type'} (_51545 : K -> Prop) (_51544 : type1514 A B K) (_51546 : K -> A) (_51547 : K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term854 A B K _51538 _51545 _51544 _51546 _51547.
Proof. exact (@lem4461172 A B K _51545 _51544 _51546 _51547 _51538 h1). Qed.
Lemma lem4461174 {A B K : Type'} (_51544 : type1514 A B K) (_51546 : K -> A) (i : type803 B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term855 A B K _51544 _51546 i _51538 f k x.
Proof. exact (@lem4461173 A B K k _51544 _51546 (term856 A B K i _51538 f k x) _51538 h1). Qed.
Lemma lem4461177 {A B K : Type'} (_51544 : type1514 A B K) (_51546 : K -> A) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : (term857 A B K _51544 _51546 i _51538 f k x) = (term858 A B K _51544 _51546 i _51538 f k x).
Proof. exact (@lem4461174 A B K _51544 _51546 i f k x _51538 h2 (@lem4461170 A B K _51538 x k f s i h1)). Qed.
Lemma lem4461178 {A B K : Type'} (_51544 : type1514 A B K) (_51546 : K -> A) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : (term857 A B K _51544 _51546 i _51538 f k x) = (term858 A B K _51544 _51546 i _51538 f k x).
Proof. exact (@lem4461177 A B K _51544 _51546 x k f s i _51538 h1 h2). Qed.
Lemma lem4461179 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : (term859 A B K i _51538 f k x) = (term860 A B K i _51538 f k x).
Proof. exact (@lem4461178 A B K f x x k f s i _51538 h1 h2). Qed.
Lemma lem4461180 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : term861 A B K i _51538 f k x.
Proof. exact (fun h0 : term862 A B K i _51538 f k x => @lem4461179 A B K x k f s i _51538 h1 h2). Qed.
Lemma lem4461182 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4461183 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term861 A B K i _51538 f k x) = ((term859 A B K i _51538 f k x) = (term860 A B K i _51538 f k x)).
Proof. exact (@lem4461182 ((term859 A B K i _51538 f k x) = (term860 A B K i _51538 f k x))). Qed.
Lemma lem4461184 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) : (term859 A B K i _51538 f k x) = (term860 A B K i _51538 f k x).
Proof. exact (EQ_MP (@lem4461183 A B K i _51538 f k x) (@lem4461180 A B K x k f s i _51538 h1 h2)). Qed.
Lemma lem4461187 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term839 A B K i _51538 f k x) : term839 A B K i _51538 f k x.
Proof. exact (h1). Qed.
Lemma lem4461188 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term839 A B K i _51538 f k x) : term840 A B K i _51538 f k x.
Proof. exact (fun h0 : term841 A B K i _51538 f k x => @lem4461187 A B K i _51538 f k x h1). Qed.
Lemma lem4461190 (p : Prop) : (term842 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4461191 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term840 A B K i _51538 f k x) = (term839 A B K i _51538 f k x).
Proof. exact (@lem4461190 (term841 A B K i _51538 f k x)). Qed.
Lemma lem4461192 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term839 A B K i _51538 f k x) : term839 A B K i _51538 f k x.
Proof. exact (EQ_MP (@lem4461191 A B K i _51538 f k x) (@lem4461188 A B K i _51538 f k x h1)). Qed.
Lemma lem4461194 {A B K : Type'} (_51541 : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term844 B K k i _51541.
Proof. exact (EQ_MP (@lem4460944 B K k i _51541) (@lem4460939 A B K _51541 x k f s i h1)). Qed.
Lemma lem4461195 {A B K : Type'} (_51541 : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term844 B K k i _51541.
Proof. exact (@lem4461194 A B K _51541 x k f s i h1). Qed.
Lemma lem4461196 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term845 A B K i _51538 f k x.
Proof. exact (@lem4461195 A B K (term686 A B K _51538 f k x) x k f s i h1). Qed.
Lemma lem4461199 {A B K : Type'} (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term680 A B K x k f s i) (h2 : term839 A B K i _51538 f k x) : term841 A B K i _51538 f k x.
Proof. exact (@lem4461196 A B K _51538 x k f s i h1 (@lem4461192 A B K i _51538 f k x h2)). Qed.
Lemma lem4461200 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term845 A B K i _51538 f k x.
Proof. exact (fun h0 : term839 A B K i _51538 f k x => @lem4461199 A B K s i _51538 f k x h1 h0). Qed.
Lemma lem4461202 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4461203 {A B K : Type'} (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term845 A B K i _51538 f k x) = (term841 A B K i _51538 f k x).
Proof. exact (@lem4461202 (term841 A B K i _51538 f k x)). Qed.
Lemma lem4461204 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term841 A B K i _51538 f k x.
Proof. exact (EQ_MP (@lem4461203 A B K i _51538 f k x) (@lem4461200 A B K _51538 x k f s i h1)). Qed.
Lemma lem4461210 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4461211 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_51543 : K) : (term725 A K k s x _51543) = (term891 A K s x k _51543).
Proof. exact (@lem4461210 (term724 A K s x _51543) (term705 K k _51543)). Qed.
Lemma lem4461217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4461218 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_51543 : K) : (term892 A K k s x _51543) = (term893 A K s x k _51543).
Proof. exact (MK_COMB (@lem4461217) (@lem4461211 A K s x k _51543)). Qed.
Lemma lem4461224 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_51543 : K) : (term891 A K s x k _51543) = (term891 A K s x k _51543).
Proof. exact (eq_refl (term891 A K s x k _51543)). Qed.
Lemma lem4461225 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_51543 : K) : ((term725 A K k s x _51543) = (term891 A K s x k _51543)) = ((term891 A K s x k _51543) = (term891 A K s x k _51543)).
Proof. exact (MK_COMB (@lem4461218 A K s x k _51543) (@lem4461224 A K s x k _51543)). Qed.
Lemma lem4461227 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4461228 (x : Prop) : (x = x) = True.
Proof. exact (@lem4461227 Prop x). Qed.
Lemma lem4461229 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_51543 : K) : ((term891 A K s x k _51543) = (term891 A K s x k _51543)) = True.
Proof. exact (@lem4461228 (term891 A K s x k _51543)). Qed.
Lemma lem4461230 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_51543 : K) : ((term725 A K k s x _51543) = (term891 A K s x k _51543)) = True.
Proof. exact (TRANS (@lem4461225 A K s x k _51543) (@lem4461229 A K s x k _51543)). Qed.
Lemma lem4461231 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_51543 : K) : True = ((term725 A K k s x _51543) = (term891 A K s x k _51543)).
Proof. exact (SYM (@lem4461230 A K s x k _51543)). Qed.
Lemma lem4461232 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_51543 : K) : (term725 A K k s x _51543) = (term891 A K s x k _51543).
Proof. exact (EQ_MP (@lem4461231 A K s x k _51543) (@lem0)). Qed.
Lemma lem4461233 {A B K : Type'} (_51543 : K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term343 A B K s g _51538 f k x) : term891 A K s x k _51543.
Proof. exact (EQ_MP (@lem4461232 A K s x k _51543) (@lem4460639 A B K _51543 s g _51538 f k x h1)). Qed.
Lemma lem4461235 (b : Prop) (a : Prop) : (a \/ b) = (term843 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4461236 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (_51543 : K) : (term891 A K s x k _51543) = (term894 A K k s x _51543).
Proof. exact (@lem4461235 (term705 K k _51543) (term724 A K s x _51543)). Qed.
Lemma lem4461238 (a : Prop) : (term312 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4461239 {K : Type'} (k : K -> Prop) (_51543 : K) : (term851 K k _51543) = (@I (K -> Prop) k _51543).
Proof. exact (@lem4461238 (@I (K -> Prop) k _51543)). Qed.
Lemma lem4461240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4461241 {K : Type'} (k : K -> Prop) (_51543 : K) : (term852 K k _51543) = (term853 K k _51543).
Proof. exact (MK_COMB (@lem4461240) (@lem4461239 K k _51543)). Qed.
Lemma lem4461242 {A K : Type'} (s : type1470 A K) (x : K -> A) (_51543 : K) : (term724 A K s x _51543) = (term724 A K s x _51543).
Proof. exact (eq_refl (term724 A K s x _51543)). Qed.
Lemma lem4461243 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (_51543 : K) : (term894 A K k s x _51543) = (term895 A K k s x _51543).
Proof. exact (MK_COMB (@lem4461241 K k _51543) (@lem4461242 A K s x _51543)). Qed.
Lemma lem4461244 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (_51543 : K) : (term891 A K s x k _51543) = (term895 A K k s x _51543).
Proof. exact (TRANS (@lem4461236 A K k s x _51543) (@lem4461243 A K k s x _51543)). Qed.
Lemma lem4461247 {A B K : Type'} (_51543 : K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term343 A B K s g _51538 f k x) : term895 A K k s x _51543.
Proof. exact (EQ_MP (@lem4461244 A K k s x _51543) (@lem4461233 A B K _51543 s g _51538 f k x h1)). Qed.
Lemma lem4461248 {A B K : Type'} (_51543 : K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term343 A B K s g _51538 f k x) : term895 A K k s x _51543.
Proof. exact (@lem4461247 A B K _51543 s g _51538 f k x h1). Qed.
Lemma lem4461249 {A B K : Type'} (i : type803 B K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term343 A B K s g _51538 f k x) : term896 A B K s i _51538 f k x.
Proof. exact (@lem4461248 A B K (term856 A B K i _51538 f k x) s g _51538 f k x h1). Qed.
Lemma lem4461252 {A B K : Type'} (i : type803 B K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term680 A B K x k f s i) (h2 : term343 A B K s g _51538 f k x) : term897 A B K s i _51538 f k x.
Proof. exact (@lem4461249 A B K i s g _51538 f k x h2 (@lem4461204 A B K _51538 x k f s i h1)). Qed.
Lemma lem4461253 {A B K : Type'} (i : type803 B K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term680 A B K x k f s i) (h2 : term343 A B K s g _51538 f k x) : term898 A B K s i _51538 f k x.
Proof. exact (fun h0 : term899 A B K s i _51538 f k x => @lem4461252 A B K i s g _51538 f k x h1 h2). Qed.
Lemma lem4461255 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4461256 {A B K : Type'} (s : type1470 A K) (i : type803 B K) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) : (term898 A B K s i _51538 f k x) = (term897 A B K s i _51538 f k x).
Proof. exact (@lem4461255 (term897 A B K s i _51538 f k x)). Qed.
Lemma lem4461257 {A B K : Type'} (i : type803 B K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term680 A B K x k f s i) (h2 : term343 A B K s g _51538 f k x) : term897 A B K s i _51538 f k x.
Proof. exact (EQ_MP (@lem4461256 A B K s i _51538 f k x) (@lem4461253 A B K i s g _51538 f k x h1 h2)). Qed.
Lemma lem4461259 (a : Prop) (b : Prop) : (term900 a b) = (term901 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4461260 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51541 : K -> B) (_51542 : A) : (term756 A B K f s i _51541 _51542) = (term902 A B K f s i _51541 _51542).
Proof. exact (@lem4461259 ((term741 B K i _51541) = (term748 A B K f i _51541 _51542)) (term736 A B K s i _51541 _51542)). Qed.
Lemma lem4461261 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (i : type803 B K) (_51541 : K -> B) : (term903 A B K f x i _51541) = (term903 A B K f x i _51541).
Proof. exact (eq_refl (term903 A B K f x i _51541)). Qed.
Lemma lem4461262 {A B K : Type'} (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51541 : K -> B) (_51542 : A) : (term836 A B K x f s i _51541 _51542) = (term904 A B K x f s i _51541 _51542).
Proof. exact (MK_COMB (@lem4461261 A B K f x i _51541) (@lem4461260 A B K f s i _51541 _51542)). Qed.
Lemma lem4461264 (a : Prop) (b : Prop) : (term900 a b) = (term901 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4461265 {A B K : Type'} (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51541 : K -> B) (_51542 : A) : (term904 A B K x f s i _51541 _51542) = (term905 A B K x f s i _51541 _51542).
Proof. exact (@lem4461264 ((term774 A B K f x i _51541) = (term741 B K i _51541)) (term906 A B K f s i _51541 _51542)). Qed.
Lemma lem4461266 {A B K : Type'} (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51541 : K -> B) (_51542 : A) : (term836 A B K x f s i _51541 _51542) = (term905 A B K x f s i _51541 _51542).
Proof. exact (TRANS (@lem4461262 A B K x f s i _51541 _51542) (@lem4461265 A B K x f s i _51541 _51542)). Qed.
Lemma lem4461268 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4461269 {A B K : Type'} (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51541 : K -> B) (_51542 : A) : (term905 A B K x f s i _51541 _51542) = (term907 A B K x f s i _51541 _51542).
Proof. exact (@lem4461268 (term908 A B K x f s i _51541 _51542)). Qed.
Lemma lem4461270 {A B K : Type'} (x : K -> A) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (_51541 : K -> B) (_51542 : A) : (term836 A B K x f s i _51541 _51542) = (term907 A B K x f s i _51541 _51542).
Proof. exact (TRANS (@lem4461266 A B K x f s i _51541 _51542) (@lem4461269 A B K x f s i _51541 _51542)). Qed.
Lemma lem4461272 {A B K : Type'} (i : type803 B K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) (h3 : term343 A B K s g _51538 f k x) : term909 A B K s i _51538 f k x.
Proof. exact (conj (@lem4461184 A B K x k f s i _51538 h1 h2) (@lem4461257 A B K i s g _51538 f k x h1 h3)). Qed.
Lemma lem4461273 {A B K : Type'} (i : type803 B K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) (h3 : term343 A B K s g _51538 f k x) : term910 A B K s i _51538 f k x.
Proof. exact (conj (@lem4461150 A B K x k f s i _51538 h1 h2) (@lem4461272 A B K i s g _51538 f k x h1 h2 h3)). Qed.
Lemma lem4461275 {A B K : Type'} (_51541 : K -> B) (_51542 : A) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term907 A B K x f s i _51541 _51542.
Proof. exact (EQ_MP (@lem4461270 A B K x f s i _51541 _51542) (@lem4460695 A B K _51541 _51542 x k f s i h1)). Qed.
Lemma lem4461276 {A B K : Type'} (_51541 : K -> B) (_51542 : A) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term907 A B K x f s i _51541 _51542.
Proof. exact (@lem4461275 A B K _51541 _51542 x k f s i h1). Qed.
Lemma lem4461277 {A B K : Type'} (_51538 : type868 A B K) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (i : type803 B K) (h1 : term680 A B K x k f s i) : term911 A B K s i _51538 f k x.
Proof. exact (@lem4461276 A B K (term686 A B K _51538 f k x) (term912 A B K i _51538 f k x) x k f s i h1). Qed.
Lemma lem4461280 {A B K : Type'} (i : type803 B K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) (h3 : term343 A B K s g _51538 f k x) : False.
Proof. exact (@lem4461277 A B K _51538 x k f s i h1 (@lem4461273 A B K i s g _51538 f k x h1 h2 h3)). Qed.
Lemma lem4461281 {A B K : Type'} (i : type803 B K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) (h3 : term343 A B K s g _51538 f k x) : term913.
Proof. exact (fun h0 : ~ False => @lem4461280 A B K i s g _51538 f k x h1 h2 h3). Qed.
Lemma lem4461283 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4461284 : term913 = False.
Proof. exact (@lem4461283 False). Qed.
Lemma lem4461286 {A B K : Type'} (i : type803 B K) (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term680 A B K x k f s i) (h2 : term474 A B K _51538) (h3 : term343 A B K s g _51538 f k x) : False.
Proof. exact (EQ_MP (@lem4461284) (@lem4461281 A B K i s g _51538 f k x h1 h2 h3)). Qed.
Lemma lem4461287 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term474 A B K _51538) (h2 : term480 A B K x k f s) (h3 : term343 A B K s g _51538 f k x) : False.
Proof. exact (ex_elim (@lem4459925 A B K x k f s h2) (fun i : type803 B K => fun h0 : term682 A B K x k f s i => @lem4461286 A B K i s g _51538 f k x h0 h1 h3)). Qed.
Lemma lem4461288 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term474 A B K _51538) (h2 : term480 A B K x k f s) (h3 : term343 A B K s g _51538 f k x) : (term480 A B K x k f s) = False.
Proof. exact (prop_ext (fun h4 : term480 A B K x k f s => @lem4461287 A B K s g _51538 f k x h1 h2 h3) (fun h4 : False => @lem4459047 A B K x k f s h2)). Qed.
Lemma lem4461289 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term474 A B K _51538) (h2 : term480 A B K x k f s) (h3 : term343 A B K s g _51538 f k x) : False.
Proof. exact (EQ_MP (@lem4461288 A B K s g _51538 f k x h1 h2 h3) (@lem4459047 A B K x k f s h2)). Qed.
Lemma lem4461290 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term474 A B K _51538) (h2 : term343 A B K s g _51538 f k x) : term479 A B K x k f s.
Proof. exact (fun h0 : term480 A B K x k f s => @lem4461289 A B K s g _51538 f k x h1 h0 h2). Qed.
Lemma lem4461291 {A B K : Type'} (s : type1470 A K) (g : K -> B) (_51538 : type868 A B K) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term474 A B K _51538) (h2 : term343 A B K s g _51538 f k x) : term450 A B K x k f s.
Proof. exact (EQ_MP (@lem4459046 A B K x k f s) (@lem4461290 A B K s g _51538 f k x h1 h2)). Qed.
Lemma lem4461292 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term451 A B K g _51538 x k f s.
Proof. exact (fun h0 : term343 A B K s g _51538 f k x => @lem4461291 A B K s g _51538 f k x h1 h0). Qed.
Lemma lem4461297 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term453 A B K _51538 x k f s.
Proof. exact (fun g : K -> B => @lem4461292 A B K g x k f s _51538 h1). Qed.
Lemma lem4461302 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term455 A B K _51538 k f s.
Proof. exact (fun x : K -> A => @lem4461297 A B K x k f s _51538 h1). Qed.
Lemma lem4461307 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term457 A B K _51538 f s.
Proof. exact (fun k : K -> Prop => @lem4461302 A B K k f s _51538 h1). Qed.
Lemma lem4461312 {A B K : Type'} (s : type1470 A K) (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term459 A B K _51538 s.
Proof. exact (fun f : type1514 A B K => @lem4461307 A B K f s _51538 h1). Qed.
Lemma lem4461317 {A B K : Type'} (_51538 : type868 A B K) (h1 : term474 A B K _51538) : term461 A B K _51538.
Proof. exact (fun s : type1470 A K => @lem4461312 A B K s _51538 h1). Qed.
Lemma lem4461318 {A B K : Type'} (_51538 : type868 A B K) : term476 A B K _51538.
Proof. exact (fun h0 : term474 A B K _51538 => @lem4461317 A B K _51538 h0). Qed.
Lemma lem4461323 {A B K : Type'} : term478 A B K.
Proof. exact (fun _51538 : type868 A B K => @lem4461318 A B K _51538). Qed.
Lemma lem4461324 {A B K : Type'} : term331 A B K.
Proof. exact (EQ_MP (@lem4459040 A B K) (@lem4461323 A B K)). Qed.
Lemma lem4461325 {A B K : Type'} (s : type1470 A K) : term914 A B K s.
Proof. exact (@lem4461324 A B K s). Qed.
Lemma lem4461326 {A B K : Type'} (s : type1470 A K) : (term914 A B K s) = (term327 A B K s).
Proof. exact (eq_refl (term914 A B K s)). Qed.
Lemma lem4461327 {A B K : Type'} (s : type1470 A K) : term327 A B K s.
Proof. exact (EQ_MP (@lem4461326 A B K s) (@lem4461325 A B K s)). Qed.
Lemma lem4461328 {A B K : Type'} (s : type1470 A K) (f : type1514 A B K) : term915 A B K s f.
Proof. exact (@lem4461327 A B K s f). Qed.
Lemma lem4461329 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) : (term915 A B K s f) = (term323 A B K f s).
Proof. exact (eq_refl (term915 A B K s f)). Qed.
Lemma lem4461330 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) : term323 A B K f s.
Proof. exact (EQ_MP (@lem4461329 A B K f s) (@lem4461328 A B K s f)). Qed.
Lemma lem4461331 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : term916 A B K f s k.
Proof. exact (@lem4461330 A B K f s k). Qed.
Lemma lem4461332 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term916 A B K f s k) = (term319 A B K k f s).
Proof. exact (eq_refl (term916 A B K f s k)). Qed.
Lemma lem4461333 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term319 A B K k f s.
Proof. exact (EQ_MP (@lem4461332 A B K k f s) (@lem4461331 A B K f s k)). Qed.
Lemma lem4461334 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (x : K -> A) : term917 A B K k f s x.
Proof. exact (@lem4461333 A B K k f s x). Qed.
Lemma lem4461335 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term917 A B K k f s x) = (term315 A B K x k f s).
Proof. exact (eq_refl (term917 A B K k f s x)). Qed.
Lemma lem4461336 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term315 A B K x k f s.
Proof. exact (EQ_MP (@lem4461335 A B K x k f s) (@lem4461334 A B K k f s x)). Qed.
Lemma lem4461337 {A B K : Type'} (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (g : K -> B) : term918 A B K x k f s g.
Proof. exact (@lem4461336 A B K x k f s g). Qed.
Lemma lem4461338 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term918 A B K x k f s g) = (term306 A B K g x k f s).
Proof. exact (eq_refl (term918 A B K x k f s g)). Qed.
Lemma lem4461339 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term306 A B K g x k f s.
Proof. exact (EQ_MP (@lem4461338 A B K g x k f s) (@lem4461337 A B K x k f s g)). Qed.
Lemma lem4461341 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term306 A B K g x k f s.
Proof. exact (@lem4458228 A B K g x k f s (@lem4461339 A B K g x k f s)). Qed.
Lemma lem4461342 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term307 A B K g x k f s) : False.
Proof. exact (@lem4461341 A B K g x k f s (@lem4458212 A B K g x k f s h1)). Qed.
Lemma lem4461343 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term307 A B K g x k f s) : (term307 A B K g x k f s) = False.
Proof. exact (prop_ext (fun h2 : term307 A B K g x k f s => @lem4461342 A B K g x k f s h1) (fun h2 : False => @lem4458212 A B K g x k f s h1)). Qed.
Lemma lem4461344 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term307 A B K g x k f s) : False.
Proof. exact (EQ_MP (@lem4461343 A B K g x k f s h1) (@lem4458212 A B K g x k f s h1)). Qed.
Lemma lem4461345 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term306 A B K g x k f s.
Proof. exact (fun h0 : term307 A B K g x k f s => @lem4461344 A B K g x k f s h0). Qed.
Lemma lem4461346 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term304 A B K g x k f s.
Proof. exact (EQ_MP (@lem4458211 A B K g x k f s) (@lem4461345 A B K g x k f s)). Qed.
Lemma lem4461348 {A B K : Type'} (g : K -> B) (x : K -> A) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term303 A B K g x k f s.
Proof. exact (EQ_MP (@lem4458207 A B K g x k f s) (@lem4461346 A B K g x k f s)). Qed.
Lemma lem4461349 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term100 A K k x s) (h2 : g = (term192 A B K f k x)) : term250 A B K x k f s.
Proof. exact (@lem4461348 A B K g x k f s (@lem4457992 A B K s g f k x h1 h2)). Qed.
Lemma lem4461360 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term220 A B K k x f s) (h2 : g = (@RESTRICTION K B k x)) : term919 A B K f s g k x.
Proof. exact (conj (@lem4457790 A B K k x f s h1) (@lem4457791 B K g k x h2)). Qed.
Lemma lem4461420 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4461421 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4461420 K P x). Qed.
Lemma lem4461422 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4461421 K k i). Qed.
Lemma lem4461423 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4461424 {K : Type'} (k : K -> Prop) (i : K) : (term75 K i k) = (term264 K k i).
Proof. exact (MK_COMB (@lem4461423) (@lem4461422 K k i)). Qed.
Lemma lem4461434 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4461435 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4461434 A P x). Qed.
Lemma lem4461436 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term290 A K x s i) = (s i x).
Proof. exact (@lem4461435 A (s i) x). Qed.
Lemma lem4461437 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (i : K) (x' : A) : (term291 A B K x f i x') = (term291 A B K x f i x').
Proof. exact (eq_refl (term291 A B K x f i x')). Qed.
Lemma lem4461438 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term292 A B K x f x' s i) = (term293 A B K x f s i x').
Proof. exact (MK_COMB (@lem4461437 A B K x f i x') (@lem4461436 A K s i x')). Qed.
Lemma lem4461441 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term294 A B K x f s i) = (term295 A B K x f s i).
Proof. exact (fun_ext (fun x' : A => @lem4461438 A B K x f s i x')). Qed.
Lemma lem4461442 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4461443 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term217 A B K x f s i) = (term296 A B K x f s i).
Proof. exact (MK_COMB (@lem4461442 A) (@lem4461441 A B K x f s i)). Qed.
Lemma lem4461448 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term218 A B K k x f s i) = (term297 A B K k x f s i).
Proof. exact (MK_COMB (@lem4461424 K k i) (@lem4461443 A B K x f s i)). Qed.
Lemma lem4461451 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term219 A B K k x f s) = (term298 A B K k x f s).
Proof. exact (fun_ext (fun i : K => @lem4461448 A B K k x f s i)). Qed.
Lemma lem4461452 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4461453 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term220 A B K k x f s) = (term299 A B K k x f s).
Proof. exact (MK_COMB (@lem4461452 K) (@lem4461451 A B K k x f s)). Qed.
Lemma lem4461458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4461459 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term920 A B K k x f s) = (term921 A B K k x f s).
Proof. exact (MK_COMB (@lem4461458) (@lem4461453 A B K k x f s)). Qed.
Lemma lem4461462 {B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) : (g = (@RESTRICTION K B k x)) = (g = (@RESTRICTION K B k x)).
Proof. exact (eq_refl (g = (@RESTRICTION K B k x))). Qed.
Lemma lem4461463 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term919 A B K f s g k x) = (term922 A B K f s g k x).
Proof. exact (MK_COMB (@lem4461459 A B K k x f s) (@lem4461462 B K g k x)). Qed.
Lemma lem4461466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4461467 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term923 A B K f s g k x) = (term924 A B K f s g k x).
Proof. exact (MK_COMB (@lem4461466) (@lem4461463 A B K f s g k x)). Qed.
Lemma lem4461481 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4461482 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4461481 K P x). Qed.
Lemma lem4461483 {K : Type'} (k : K -> Prop) (x : K) : (@IN K x k) = (k x).
Proof. exact (@lem4461482 K k x). Qed.
Lemma lem4461484 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4461485 {K : Type'} (k : K -> Prop) (x : K) : (term75 K x k) = (term264 K k x).
Proof. exact (MK_COMB (@lem4461484) (@lem4461483 K k x)). Qed.
Lemma lem4461489 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4461490 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4461489 K P x). Qed.
Lemma lem4461491 {K : Type'} (k : K -> Prop) (x : K) : (@IN K x k) = (k x).
Proof. exact (@lem4461490 K k x). Qed.
Lemma lem4461492 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4461493 {A K : Type'} (k : K -> Prop) (x : K) : (term274 A K x k) = (term275 A K k x).
Proof. exact (MK_COMB (@lem4461492 A) (@lem4461491 K k x)). Qed.
Lemma lem4461494 {A K : Type'} (x : K -> A) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4461495 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term276 A K k x x') = (term277 A K k x x').
Proof. exact (MK_COMB (@lem4461493 A K k x') (@lem4461494 A K x x')). Qed.
Lemma lem4461496 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4461497 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term187 A K k x x') = (term278 A K k x x').
Proof. exact (MK_COMB (@lem4461495 A K k x x') (@lem4461496 A)). Qed.
Lemma lem4461498 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4461499 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (x' : K) : (term189 A B K f k x x') = (term279 A B K f k x x').
Proof. exact (MK_COMB (@lem4461498 A B K f x') (@lem4461497 A K k x x')). Qed.
Lemma lem4461500 {B K : Type'} (x : K -> B) (x' : K) : (term253 B K x x') = (term253 B K x x').
Proof. exact (eq_refl (term253 B K x x')). Qed.
Lemma lem4461501 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) (x'' : K) : ((x x'') = (term189 A B K f k x' x'')) = ((x x'') = (term279 A B K f k x' x'')).
Proof. exact (MK_COMB (@lem4461500 B K x x'') (@lem4461499 A B K f k x' x'')). Qed.
Lemma lem4461504 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) (x'' : K) : (term255 A B K x f k x' x'') = (term925 A B K x f k x' x'').
Proof. exact (MK_COMB (@lem4461485 K k x'') (@lem4461501 A B K x f k x' x'')). Qed.
Lemma lem4461507 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) : (term257 A B K x f k x') = (term926 A B K x f k x').
Proof. exact (fun_ext (fun x'' : K => @lem4461504 A B K x f k x' x'')). Qed.
Lemma lem4461508 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4461509 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) : (term258 A B K x f k x') = (term927 A B K x f k x').
Proof. exact (MK_COMB (@lem4461508 K) (@lem4461507 A B K x f k x')). Qed.
Lemma lem4461514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4461515 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) : (term259 A B K x f k x') = (term928 A B K x f k x').
Proof. exact (MK_COMB (@lem4461514) (@lem4461509 A B K x f k x')). Qed.
Lemma lem4461523 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4461524 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4461523 K P x). Qed.
Lemma lem4461525 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4461524 K k i). Qed.
Lemma lem4461526 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4461527 {K : Type'} (k : K -> Prop) (i : K) : (term75 K i k) = (term264 K k i).
Proof. exact (MK_COMB (@lem4461526) (@lem4461525 K k i)). Qed.
Lemma lem4461529 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4461530 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4461529 A P x). Qed.
Lemma lem4461531 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term265 A K x s i) = (term266 A K s x i).
Proof. exact (@lem4461530 A (s i) (x i)). Qed.
Lemma lem4461532 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term267 A K k x s i) = (term268 A K k s x i).
Proof. exact (MK_COMB (@lem4461527 K k i) (@lem4461531 A K s x i)). Qed.
Lemma lem4461535 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term269 A K k x s) = (term270 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4461532 A K k s x i)). Qed.
Lemma lem4461536 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4461537 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term100 A K k x s) = (term271 A K k s x).
Proof. exact (MK_COMB (@lem4461536 K) (@lem4461535 A K k s x)). Qed.
Lemma lem4461542 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term260 A B K x f k x' s) = (term929 A B K x f k s x').
Proof. exact (MK_COMB (@lem4461515 A B K x f k x') (@lem4461537 A K k s x')). Qed.
Lemma lem4461545 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term261 A B K x f k s) = (term930 A B K x f k s).
Proof. exact (fun_ext (fun x' : K -> A => @lem4461542 A B K x f k s x')). Qed.
Lemma lem4461546 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4461547 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term262 A B K x f k s) = (term931 A B K x f k s).
Proof. exact (MK_COMB (@lem4461546 A K) (@lem4461545 A B K x f k s)). Qed.
Lemma lem4461552 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term932 A B K g x f k s) = (term933 A B K g x f k s).
Proof. exact (MK_COMB (@lem4461467 A B K f s g k x) (@lem4461547 A B K x f k s)). Qed.
Lemma lem4461555 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term933 A B K g x f k s) = (term932 A B K g x f k s).
Proof. exact (SYM (@lem4461552 A B K g x f k s)). Qed.
Lemma lem4461557 (p : Prop) : p = (term305 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4461558 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term933 A B K g x f k s) = (term934 A B K g x f k s).
Proof. exact (@lem4461557 (term933 A B K g x f k s)). Qed.
Lemma lem4461559 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term934 A B K g x f k s) = (term933 A B K g x f k s).
Proof. exact (SYM (@lem4461558 A B K g x f k s)). Qed.
Lemma lem4461560 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term935 A B K g x f k s) : term935 A B K g x f k s.
Proof. exact (h1). Qed.
Lemma lem4461563 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term934 A B K g x f k s) : term934 A B K g x f k s.
Proof. exact (h1). Qed.
Lemma lem4461564 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term936 A B K g x f k s.
Proof. exact (fun h0 : term934 A B K g x f k s => @lem4461563 A B K g x f k s h0). Qed.
Lemma lem4461565 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term936 A B K g x f k s) : term936 A B K g x f k s.
Proof. exact (h1). Qed.
Lemma lem4461566 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term934 A B K g x f k s) : term934 A B K g x f k s.
Proof. exact (h1). Qed.
Lemma lem4461567 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term934 A B K g x f k s) (h2 : term936 A B K g x f k s) : term934 A B K g x f k s.
Proof. exact (@lem4461565 A B K g x f k s h2 (@lem4461566 A B K g x f k s h1)). Qed.
Lemma lem4461568 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term934 A B K g x f k s) : term937 A B K g x f k s.
Proof. exact (fun h0 : term936 A B K g x f k s => @lem4461567 A B K g x f k s h1 h0). Qed.
Lemma lem4461569 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term936 A B K g x f k s) : term936 A B K g x f k s.
Proof. exact (h1). Qed.
Lemma lem4461570 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term934 A B K g x f k s) (h2 : term936 A B K g x f k s) : term934 A B K g x f k s.
Proof. exact (@lem4461568 A B K g x f k s h1 (@lem4461569 A B K g x f k s h2)). Qed.
Lemma lem4461571 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term936 A B K g x f k s) : term936 A B K g x f k s.
Proof. exact (fun h0 : term934 A B K g x f k s => @lem4461570 A B K g x f k s h0 h1). Qed.
Lemma lem4461572 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term938 A B K g x f k s.
Proof. exact (fun h0 : term936 A B K g x f k s => @lem4461571 A B K g x f k s h0). Qed.
Lemma lem4461575 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term936 A B K g x f k s.
Proof. exact (@lem4461572 A B K g x f k s (@lem4461564 A B K g x f k s)). Qed.
Lemma lem4461576 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term936 A B K g x f k s.
Proof. exact (@lem4461575 A B K g x f k s). Qed.
Lemma lem4461598 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4461599 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term934 A B K g x f k s) = (term939 A B K g x f k s).
Proof. exact (@lem4461598 (term935 A B K g x f k s)). Qed.
Lemma lem4461601 (t : Prop) : (term312 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4461602 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term939 A B K g x f k s) = (term933 A B K g x f k s).
Proof. exact (@lem4461601 (term933 A B K g x f k s)). Qed.
Lemma lem4461605 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term934 A B K g x f k s) = (term933 A B K g x f k s).
Proof. exact (TRANS (@lem4461599 A B K g x f k s) (@lem4461602 A B K g x f k s)). Qed.
Lemma lem4461726 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term940 A B K x f k s) = (term941 A B K x f k s).
Proof. exact (fun_ext (fun g : K -> B => @lem4461605 A B K g x f k s)). Qed.
Lemma lem4461727 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4461728 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term942 A B K x f k s) = (term943 A B K x f k s).
Proof. exact (MK_COMB (@lem4461727 B K) (@lem4461726 A B K x f k s)). Qed.
Lemma lem4461733 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term944 A B K f k s) = (term945 A B K f k s).
Proof. exact (fun_ext (fun x : K -> B => @lem4461728 A B K x f k s)). Qed.
Lemma lem4461734 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4461735 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term946 A B K f k s) = (term947 A B K f k s).
Proof. exact (MK_COMB (@lem4461734 B K) (@lem4461733 A B K f k s)). Qed.
Lemma lem4461740 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) : (term948 A B K k s) = (term949 A B K k s).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4461735 A B K f k s)). Qed.
Lemma lem4461741 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4461742 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) : (term950 A B K k s) = (term951 A B K k s).
Proof. exact (MK_COMB (@lem4461741 A B K) (@lem4461740 A B K k s)). Qed.
Lemma lem4461747 {A B K : Type'} (s : type1470 A K) : (term952 A B K s) = (term953 A B K s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4461742 A B K k s)). Qed.
Lemma lem4461748 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4461749 {A B K : Type'} (s : type1470 A K) : (term954 A B K s) = (term955 A B K s).
Proof. exact (MK_COMB (@lem4461748 K) (@lem4461747 A B K s)). Qed.
Lemma lem4461754 {A B K : Type'} : (term956 A B K) = (term957 A B K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4461749 A B K s)). Qed.
Lemma lem4461755 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4461764 {A B K : Type'} : (term958 A B K) = (term959 A B K).
Proof. exact (MK_COMB (@lem4461755 A K) (@lem4461754 A B K)). Qed.
Lemma lem4461769 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term268 A K k s x i) = (term268 A K k s x i).
Proof. exact (eq_refl (term268 A K k s x i)). Qed.
Lemma lem4461770 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term270 A K k s x) = (term270 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4461769 A K k s x i)). Qed.
Lemma lem4461771 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4461772 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term271 A K k s x) = (term271 A K k s x).
Proof. exact (MK_COMB (@lem4461771 K) (@lem4461770 A K k s x)). Qed.
Lemma lem4461776 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (k x) = False.
Proof. exact (h1). Qed.
Lemma lem4461777 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4461778 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term264 K k x) = (imp False).
Proof. exact (MK_COMB (@lem4461777) (@lem4461776 K k x h1)). Qed.
Lemma lem4461780 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (k x) = False.
Proof. exact (h1). Qed.
Lemma lem4461781 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4461782 {A K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term275 A K k x) = (@COND A False).
Proof. exact (MK_COMB (@lem4461781 A) (@lem4461780 K k x h1)). Qed.
Lemma lem4461783 {A K : Type'} (x : K -> A) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4461784 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = False) : (term277 A K k x x') = (term426 A K x x').
Proof. exact (MK_COMB (@lem4461782 A K k x' h1) (@lem4461783 A K x x')). Qed.
Lemma lem4461785 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4461786 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = False) : (term278 A K k x x') = (term427 A K x x').
Proof. exact (MK_COMB (@lem4461784 A K x k x' h1) (@lem4461785 A)). Qed.
Lemma lem4461788 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4461789 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4461788 A t1 t2). Qed.
Lemma lem4461790 {A K : Type'} (x : K -> A) (x' : K) : (term427 A K x x') = (@ARB A).
Proof. exact (@lem4461789 A (x x') (@ARB A)). Qed.
Lemma lem4461791 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = False) : (term278 A K k x x') = (@ARB A).
Proof. exact (TRANS (@lem4461786 A K x k x' h1) (@lem4461790 A K x x')). Qed.
Lemma lem4461792 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4461793 {A B K : Type'} (x : K -> A) (f : type1514 A B K) (k : K -> Prop) (x' : K) (h1 : (k x') = False) : (term279 A B K f k x x') = (f x' (@ARB A)).
Proof. exact (MK_COMB (@lem4461792 A B K f x') (@lem4461791 A K x k x' h1)). Qed.
Lemma lem4461794 {B K : Type'} (x : K -> B) (x' : K) : (term253 B K x x') = (term253 B K x x').
Proof. exact (eq_refl (term253 B K x x')). Qed.
Lemma lem4461795 {A B K : Type'} (x : K -> A) (x' : K -> B) (f : type1514 A B K) (k : K -> Prop) (x'' : K) (h1 : (k x'') = False) : ((x' x'') = (term279 A B K f k x x'')) = ((x' x'') = (f x'' (@ARB A))).
Proof. exact (MK_COMB (@lem4461794 B K x' x'') (@lem4461793 A B K x f k x'' h1)). Qed.
Lemma lem4461798 {A B K : Type'} (x : K -> A) (x' : K -> B) (f : type1514 A B K) (k : K -> Prop) (x'' : K) (h1 : (k x'') = False) : (term925 A B K x' f k x x'') = (term960 A B K x' f x'').
Proof. exact (MK_COMB (@lem4461778 K k x'' h1) (@lem4461795 A B K x x' f k x'' h1)). Qed.
Lemma lem4461800 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4461801 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K) : (term960 A B K x f x') = True.
Proof. exact (@lem4461800 ((x x') = (f x' (@ARB A)))). Qed.
Lemma lem4461802 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (x'' : K) (h1 : (k x'') = False) : (term925 A B K x f k x' x'') = True.
Proof. exact (TRANS (@lem4461798 A B K x' x f k x'' h1) (@lem4461801 A B K x f x'')). Qed.
Lemma lem4461803 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (x' : K -> A) (x'' : K) : term961 A B K x f k x' x''.
Proof. exact (fun h0 : (k x'') = False => @lem4461802 A B K x f x' k x'' h0). Qed.
Lemma lem4461805 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (k x) = True.
Proof. exact (h1). Qed.
Lemma lem4461806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4461807 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term264 K k x) = (imp True).
Proof. exact (MK_COMB (@lem4461806) (@lem4461805 K k x h1)). Qed.
Lemma lem4461809 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (k x) = True.
Proof. exact (h1). Qed.
Lemma lem4461810 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4461811 {A K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term275 A K k x) = (@COND A True).
Proof. exact (MK_COMB (@lem4461810 A) (@lem4461809 K k x h1)). Qed.
Lemma lem4461812 {A K : Type'} (x : K -> A) (x' : K) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4461813 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = True) : (term277 A K k x x') = (term431 A K x x').
Proof. exact (MK_COMB (@lem4461811 A K k x' h1) (@lem4461812 A K x x')). Qed.
Lemma lem4461814 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4461815 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = True) : (term278 A K k x x') = (term432 A K x x').
Proof. exact (MK_COMB (@lem4461813 A K x k x' h1) (@lem4461814 A)). Qed.
Lemma lem4461817 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4461818 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4461817 A t2 t1). Qed.
Lemma lem4461819 {A K : Type'} (x : K -> A) (x' : K) : (term432 A K x x') = (x x').
Proof. exact (@lem4461818 A (@ARB A) (x x')). Qed.
Lemma lem4461820 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = True) : (term278 A K k x x') = (x x').
Proof. exact (TRANS (@lem4461815 A K x k x' h1) (@lem4461819 A K x x')). Qed.
Lemma lem4461821 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4461822 {A B K : Type'} (f : type1514 A B K) (x : K -> A) (k : K -> Prop) (x' : K) (h1 : (k x') = True) : (term279 A B K f k x x') = (term433 A B K f x x').
Proof. exact (MK_COMB (@lem4461821 A B K f x') (@lem4461820 A K x k x' h1)). Qed.
Lemma lem4461823 {B K : Type'} (x : K -> B) (x' : K) : (term253 B K x x') = (term253 B K x x').
Proof. exact (eq_refl (term253 B K x x')). Qed.
Lemma lem4461824 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (x'' : K) (h1 : (k x'') = True) : ((x x'') = (term279 A B K f k x' x'')) = ((x x'') = (term433 A B K f x' x'')).
Proof. exact (MK_COMB (@lem4461823 B K x x'') (@lem4461822 A B K f x' k x'' h1)). Qed.
Lemma lem4461827 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (x'' : K) (h1 : (k x'') = True) : (term925 A B K x f k x' x'') = (term962 A B K x f x' x'').
Proof. exact (MK_COMB (@lem4461807 K k x'' h1) (@lem4461824 A B K x f x' k x'' h1)). Qed.
Lemma lem4461829 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4461830 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term962 A B K x f x' x'') = ((x x'') = (term433 A B K f x' x'')).
Proof. exact (@lem4461829 ((x x'') = (term433 A B K f x' x''))). Qed.
Lemma lem4461833 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (x'' : K) (h1 : (k x'') = True) : (term925 A B K x f k x' x'') = ((x x'') = (term433 A B K f x' x'')).
Proof. exact (TRANS (@lem4461827 A B K x f x' k x'' h1) (@lem4461830 A B K x f x' x'')). Qed.
Lemma lem4461834 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : term963 A B K k x f x' x''.
Proof. exact (fun h0 : (k x'') = True => @lem4461833 A B K x f x' k x'' h0). Qed.
Lemma lem4461835 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : term964 A B K k x f x' x''.
Proof. exact (conj (@lem4461803 A B K x f k x' x'') (@lem4461834 A B K k x f x' x'')). Qed.
Lemma lem4461837 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term438 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4461838 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (x'' : K) : term965 A B K x f x' k x''.
Proof. exact (@lem4461837 (term925 A B K x f k x' x'') ((x x'') = (term433 A B K f x' x'')) (k x'') True). Qed.
Lemma lem4461839 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (x'' : K) : (term925 A B K x f k x' x'') = (term966 A B K x f x' k x'').
Proof. exact (@lem4461838 A B K x f x' k x'' (@lem4461835 A B K k x f x' x'')). Qed.
Lemma lem4461841 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4461842 {K : Type'} (k : K -> Prop) (x : K) : (term441 K k x) = True.
Proof. exact (@lem4461841 (k x)). Qed.
Lemma lem4461847 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term967 A B K k x f x' x'') = (term967 A B K k x f x' x'').
Proof. exact (eq_refl (term967 A B K k x f x' x'')). Qed.
Lemma lem4461848 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term966 A B K x f x' k x'') = (term968 A B K k x f x' x'').
Proof. exact (MK_COMB (@lem4461847 A B K k x f x' x'') (@lem4461842 K k x'')). Qed.
Lemma lem4461850 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4461851 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term968 A B K k x f x' x'') = (term969 A B K k x f x' x'').
Proof. exact (@lem4461850 (term969 A B K k x f x' x'')). Qed.
Lemma lem4461852 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term966 A B K x f x' k x'') = (term969 A B K k x f x' x'').
Proof. exact (TRANS (@lem4461848 A B K k x f x' x'') (@lem4461851 A B K k x f x' x'')). Qed.
Lemma lem4461863 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term925 A B K x f k x' x'') = (term969 A B K k x f x' x'').
Proof. exact (TRANS (@lem4461839 A B K x f x' k x'') (@lem4461852 A B K k x f x' x'')). Qed.
Lemma lem4461864 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) : (term926 A B K x f k x') = (term970 A B K k x f x').
Proof. exact (fun_ext (fun x'' : K => @lem4461863 A B K k x f x' x'')). Qed.
Lemma lem4461865 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4461866 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) : (term927 A B K x f k x') = (term971 A B K k x f x').
Proof. exact (MK_COMB (@lem4461865 K) (@lem4461864 A B K k x f x')). Qed.
Lemma lem4461867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4461868 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) : (term928 A B K x f k x') = (term972 A B K k x f x').
Proof. exact (MK_COMB (@lem4461867) (@lem4461866 A B K k x f x')). Qed.
Lemma lem4461869 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term929 A B K x f k s x') = (term973 A B K x f k s x').
Proof. exact (MK_COMB (@lem4461868 A B K k x f x') (@lem4461772 A K k s x')). Qed.
Lemma lem4461870 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term930 A B K x f k s) = (term974 A B K x f k s).
Proof. exact (fun_ext (fun x' : K -> A => @lem4461869 A B K x f k s x')). Qed.
Lemma lem4461871 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4461872 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term931 A B K x f k s) = (term975 A B K x f k s).
Proof. exact (MK_COMB (@lem4461871 A K) (@lem4461870 A B K x f k s)). Qed.
Lemma lem4461873 {B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) : (g = (@RESTRICTION K B k x)) = (g = (@RESTRICTION K B k x)).
Proof. exact (eq_refl (g = (@RESTRICTION K B k x))). Qed.
Lemma lem4461878 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term293 A B K x f s i x') = (term293 A B K x f s i x').
Proof. exact (eq_refl (term293 A B K x f s i x')). Qed.
Lemma lem4461879 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term295 A B K x f s i) = (term295 A B K x f s i).
Proof. exact (fun_ext (fun x' : A => @lem4461878 A B K x f s i x')). Qed.
Lemma lem4461880 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4461881 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term296 A B K x f s i) = (term296 A B K x f s i).
Proof. exact (MK_COMB (@lem4461880 A) (@lem4461879 A B K x f s i)). Qed.
Lemma lem4461884 {K : Type'} (k : K -> Prop) (i : K) : (term264 K k i) = (term264 K k i).
Proof. exact (eq_refl (term264 K k i)). Qed.
Lemma lem4461885 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term297 A B K k x f s i) = (term297 A B K k x f s i).
Proof. exact (MK_COMB (@lem4461884 K k i) (@lem4461881 A B K x f s i)). Qed.
Lemma lem4461886 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term298 A B K k x f s) = (term298 A B K k x f s).
Proof. exact (fun_ext (fun i : K => @lem4461885 A B K k x f s i)). Qed.
Lemma lem4461887 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4461888 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term299 A B K k x f s) = (term299 A B K k x f s).
Proof. exact (MK_COMB (@lem4461887 K) (@lem4461886 A B K k x f s)). Qed.
Lemma lem4461889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4461890 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term921 A B K k x f s) = (term921 A B K k x f s).
Proof. exact (MK_COMB (@lem4461889) (@lem4461888 A B K k x f s)). Qed.
Lemma lem4461891 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term922 A B K f s g k x) = (term922 A B K f s g k x).
Proof. exact (MK_COMB (@lem4461890 A B K k x f s) (@lem4461873 B K g k x)). Qed.
Lemma lem4461892 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4461893 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term924 A B K f s g k x) = (term924 A B K f s g k x).
Proof. exact (MK_COMB (@lem4461892) (@lem4461891 A B K f s g k x)). Qed.
Lemma lem4461894 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term933 A B K g x f k s) = (term976 A B K g x f k s).
Proof. exact (MK_COMB (@lem4461893 A B K f s g k x) (@lem4461872 A B K x f k s)). Qed.
Lemma lem4461895 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term941 A B K x f k s) = (term977 A B K x f k s).
Proof. exact (fun_ext (fun g : K -> B => @lem4461894 A B K g x f k s)). Qed.
Lemma lem4461896 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4461897 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term943 A B K x f k s) = (term978 A B K x f k s).
Proof. exact (MK_COMB (@lem4461896 B K) (@lem4461895 A B K x f k s)). Qed.
Lemma lem4461898 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term945 A B K f k s) = (term979 A B K f k s).
Proof. exact (fun_ext (fun x : K -> B => @lem4461897 A B K x f k s)). Qed.
Lemma lem4461899 {B K : Type'} : (@all (K -> B)) = (@all (K -> B)).
Proof. exact (eq_refl (@all (K -> B))). Qed.
Lemma lem4461900 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term947 A B K f k s) = (term980 A B K f k s).
Proof. exact (MK_COMB (@lem4461899 B K) (@lem4461898 A B K f k s)). Qed.
Lemma lem4461901 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) : (term949 A B K k s) = (term981 A B K k s).
Proof. exact (fun_ext (fun f : type1514 A B K => @lem4461900 A B K f k s)). Qed.
Lemma lem4461902 {A B K : Type'} : (@all (K -> A -> B)) = (@all (K -> A -> B)).
Proof. exact (eq_refl (@all (K -> A -> B))). Qed.
Lemma lem4461903 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) : (term951 A B K k s) = (term982 A B K k s).
Proof. exact (MK_COMB (@lem4461902 A B K) (@lem4461901 A B K k s)). Qed.
Lemma lem4461904 {A B K : Type'} (s : type1470 A K) : (term953 A B K s) = (term983 A B K s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4461903 A B K k s)). Qed.
Lemma lem4461905 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4461906 {A B K : Type'} (s : type1470 A K) : (term955 A B K s) = (term984 A B K s).
Proof. exact (MK_COMB (@lem4461905 K) (@lem4461904 A B K s)). Qed.
Lemma lem4461907 {A B K : Type'} : (term957 A B K) = (term985 A B K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4461906 A B K s)). Qed.
Lemma lem4461908 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4461909 {A B K : Type'} : (term959 A B K) = (term986 A B K).
Proof. exact (MK_COMB (@lem4461908 A K) (@lem4461907 A B K)). Qed.
Lemma lem4461986 {A B K : Type'} : (term958 A B K) = (term986 A B K).
Proof. exact (TRANS (@lem4461764 A B K) (@lem4461909 A B K)). Qed.
Lemma lem4461987 {A B K : Type'} : (term986 A B K) = (term958 A B K).
Proof. exact (SYM (@lem4461986 A B K)). Qed.
Lemma lem4461988 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term922 A B K f s g k x) : term922 A B K f s g k x.
Proof. exact (h1). Qed.
Lemma lem4461990 (p : Prop) : p = (term305 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4461991 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term975 A B K x f k s) = (term987 A B K x f k s).
Proof. exact (@lem4461990 (term975 A B K x f k s)). Qed.
Lemma lem4461992 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term987 A B K x f k s) = (term975 A B K x f k s).
Proof. exact (SYM (@lem4461991 A B K x f k s)). Qed.
Lemma lem4461993 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term988 A B K x f k s) : term988 A B K x f k s.
Proof. exact (h1). Qed.
Lemma lem4461999 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term293 A B K x f s i x') = (term293 A B K x f s i x').
Proof. exact (eq_refl (term293 A B K x f s i x')). Qed.
Lemma lem4462000 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term295 A B K x f s i) = (term295 A B K x f s i).
Proof. exact (fun_ext (fun x' : A => @lem4461999 A B K x f s i x')). Qed.
Lemma lem4462001 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4462002 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term296 A B K x f s i) = (term296 A B K x f s i).
Proof. exact (MK_COMB (@lem4462001 A) (@lem4462000 A B K x f s i)). Qed.
Lemma lem4462004 {K : Type'} (k : K -> Prop) (i : K) : (term706 K k i) = (term706 K k i).
Proof. exact (eq_refl (term706 K k i)). Qed.
Lemma lem4462005 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term989 A B K k x f s i) = (term989 A B K k x f s i).
Proof. exact (MK_COMB (@lem4462004 K k i) (@lem4462002 A B K x f s i)). Qed.
Lemma lem4462006 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term297 A B K k x f s i) = (term989 A B K k x f s i).
Proof. exact (@lem17265 (k i) (term296 A B K x f s i)). Qed.
Lemma lem4462007 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term297 A B K k x f s i) = (term989 A B K k x f s i).
Proof. exact (TRANS (@lem4462006 A B K k x f s i) (@lem4462005 A B K k x f s i)). Qed.
Lemma lem4462008 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term298 A B K k x f s) = (term990 A B K k x f s).
Proof. exact (fun_ext (fun i : K => @lem4462007 A B K k x f s i)). Qed.
Lemma lem4462009 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4462010 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term299 A B K k x f s) = (term991 A B K k x f s).
Proof. exact (MK_COMB (@lem4462009 K) (@lem4462008 A B K k x f s)). Qed.
Lemma lem4462011 {B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) : (g = (@RESTRICTION K B k x)) = (g = (@RESTRICTION K B k x)).
Proof. exact (eq_refl (g = (@RESTRICTION K B k x))). Qed.
Lemma lem4462012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4462013 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term921 A B K k x f s) = (term992 A B K k x f s).
Proof. exact (MK_COMB (@lem4462012) (@lem4462010 A B K k x f s)). Qed.
Lemma lem4462014 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term922 A B K f s g k x) = (term993 A B K f s g k x).
Proof. exact (MK_COMB (@lem4462013 A B K k x f s) (@lem4462011 B K g k x)). Qed.
Lemma lem4462113 {A : Type'} (P : Prop) (Q : A -> Prop) : (term994 A P Q) = (term995 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4462114 {A : Type'} (P : Prop) (Q : A -> Prop) : (term994 A P Q) = (term995 A P Q).
Proof. exact (@lem4462113 A P Q). Qed.
Lemma lem4462115 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term996 A B K k x f s i) = (term997 A B K k x f s i).
Proof. exact (@lem4462114 A (term590 K k i) (term295 A B K x f s i)). Qed.
Lemma lem4462116 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term606 A B K x f s i x') = (term293 A B K x f s i x').
Proof. exact (eq_refl (term606 A B K x f s i x')). Qed.
Lemma lem4462117 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term998 A B K x f s i) = (term295 A B K x f s i).
Proof. exact (fun_ext (fun x' : A => @lem4462116 A B K x f s i x')). Qed.
Lemma lem4462118 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4462119 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term999 A B K x f s i) = (term296 A B K x f s i).
Proof. exact (MK_COMB (@lem4462118 A) (@lem4462117 A B K x f s i)). Qed.
Lemma lem4462120 {K : Type'} (k : K -> Prop) (i : K) : (term706 K k i) = (term706 K k i).
Proof. exact (eq_refl (term706 K k i)). Qed.
Lemma lem4462121 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term996 A B K k x f s i) = (term989 A B K k x f s i).
Proof. exact (MK_COMB (@lem4462120 K k i) (@lem4462119 A B K x f s i)). Qed.
Lemma lem4462122 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4462123 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term1000 A B K k x f s i) = (term1001 A B K k x f s i).
Proof. exact (MK_COMB (@lem4462122) (@lem4462121 A B K k x f s i)). Qed.
Lemma lem4462124 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term606 A B K x f s i x') = (term293 A B K x f s i x').
Proof. exact (eq_refl (term606 A B K x f s i x')). Qed.
Lemma lem4462125 {K : Type'} (k : K -> Prop) (i : K) : (term706 K k i) = (term706 K k i).
Proof. exact (eq_refl (term706 K k i)). Qed.
Lemma lem4462126 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term1002 A B K k x f s i x') = (term1003 A B K k x f s i x').
Proof. exact (MK_COMB (@lem4462125 K k i) (@lem4462124 A B K x f s i x')). Qed.
Lemma lem4462127 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term1004 A B K k x f s i) = (term1005 A B K k x f s i).
Proof. exact (fun_ext (fun x' : A => @lem4462126 A B K k x f s i x')). Qed.
Lemma lem4462128 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4462129 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term997 A B K k x f s i) = (term1006 A B K k x f s i).
Proof. exact (MK_COMB (@lem4462128 A) (@lem4462127 A B K k x f s i)). Qed.
Lemma lem4462130 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : ((term996 A B K k x f s i) = (term997 A B K k x f s i)) = ((term989 A B K k x f s i) = (term1006 A B K k x f s i)).
Proof. exact (MK_COMB (@lem4462123 A B K k x f s i) (@lem4462129 A B K k x f s i)). Qed.
Lemma lem4462131 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term989 A B K k x f s i) = (term1006 A B K k x f s i).
Proof. exact (EQ_MP (@lem4462130 A B K k x f s i) (@lem4462115 A B K k x f s i)). Qed.
Lemma lem4462132 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term990 A B K k x f s) = (term1007 A B K k x f s).
Proof. exact (fun_ext (fun i : K => @lem4462131 A B K k x f s i)). Qed.
Lemma lem4462133 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4462134 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term991 A B K k x f s) = (term1008 A B K k x f s).
Proof. exact (MK_COMB (@lem4462133 K) (@lem4462132 A B K k x f s)). Qed.
Lemma lem4462136 {A B : Type'} (P : type1413 A B) : (term659 A B P) = (term660 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4462137 {A K : Type'} (P : type1470 A K) : (term1009 A K P) = (term1010 A K P).
Proof. exact (@lem4462136 K A P). Qed.
Lemma lem4462138 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term1011 A B K k x f s) = (term1012 A B K k x f s).
Proof. exact (@lem4462137 A K (term1013 A B K k x f s)). Qed.
Lemma lem4462139 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term1014 A B K k x f s i) = (term1005 A B K k x f s i).
Proof. exact (eq_refl (term1014 A B K k x f s i)). Qed.
Lemma lem4462140 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4462141 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term1015 A B K k x f s i x') = (term1016 A B K k x f s i x').
Proof. exact (MK_COMB (@lem4462139 A B K k x f s i) (@lem4462140 A x')). Qed.
Lemma lem4462142 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term1016 A B K k x f s i x') = (term1003 A B K k x f s i x').
Proof. exact (eq_refl (term1016 A B K k x f s i x')). Qed.
Lemma lem4462143 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) (x' : A) : (term1015 A B K k x f s i x') = (term1003 A B K k x f s i x').
Proof. exact (TRANS (@lem4462141 A B K k x f s i x') (@lem4462142 A B K k x f s i x')). Qed.
Lemma lem4462144 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term1017 A B K k x f s i) = (term1005 A B K k x f s i).
Proof. exact (fun_ext (fun x' : A => @lem4462143 A B K k x f s i x')). Qed.
Lemma lem4462145 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4462146 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term1018 A B K k x f s i) = (term1006 A B K k x f s i).
Proof. exact (MK_COMB (@lem4462145 A) (@lem4462144 A B K k x f s i)). Qed.
Lemma lem4462147 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term1019 A B K k x f s) = (term1007 A B K k x f s).
Proof. exact (fun_ext (fun i : K => @lem4462146 A B K k x f s i)). Qed.
Lemma lem4462148 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4462149 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term1011 A B K k x f s) = (term1008 A B K k x f s).
Proof. exact (MK_COMB (@lem4462148 K) (@lem4462147 A B K k x f s)). Qed.
Lemma lem4462150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4462151 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term1020 A B K k x f s) = (term1021 A B K k x f s).
Proof. exact (MK_COMB (@lem4462150) (@lem4462149 A B K k x f s)). Qed.
Lemma lem4462152 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : K) : (term1014 A B K k x f s i) = (term1005 A B K k x f s i).
Proof. exact (eq_refl (term1014 A B K k x f s i)). Qed.
Lemma lem4462153 {A K : Type'} (x : K -> A) (i : K) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem4462154 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (i : K) : (term1022 A B K k x f s x' i) = (term1023 A B K k x f s x' i).
Proof. exact (MK_COMB (@lem4462152 A B K k x f s i) (@lem4462153 A K x' i)). Qed.
Lemma lem4462155 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (i : K) : (term1023 A B K k x f s x' i) = (term1024 A B K k x f s x' i).
Proof. exact (eq_refl (term1023 A B K k x f s x' i)). Qed.
Lemma lem4462156 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (i : K) : (term1022 A B K k x f s x' i) = (term1024 A B K k x f s x' i).
Proof. exact (TRANS (@lem4462154 A B K k x f s x' i) (@lem4462155 A B K k x f s x' i)). Qed.
Lemma lem4462157 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) : (term1025 A B K k x f s x') = (term1026 A B K k x f s x').
Proof. exact (fun_ext (fun i : K => @lem4462156 A B K k x f s x' i)). Qed.
Lemma lem4462158 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4462159 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) : (term1027 A B K k x f s x') = (term1028 A B K k x f s x').
Proof. exact (MK_COMB (@lem4462158 K) (@lem4462157 A B K k x f s x')). Qed.
Lemma lem4462160 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term1029 A B K k x f s) = (term1030 A B K k x f s).
Proof. exact (fun_ext (fun x' : K -> A => @lem4462159 A B K k x f s x')). Qed.
Lemma lem4462161 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4462162 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term1012 A B K k x f s) = (term1031 A B K k x f s).
Proof. exact (MK_COMB (@lem4462161 A K) (@lem4462160 A B K k x f s)). Qed.
Lemma lem4462163 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : ((term1011 A B K k x f s) = (term1012 A B K k x f s)) = ((term1008 A B K k x f s) = (term1031 A B K k x f s)).
Proof. exact (MK_COMB (@lem4462151 A B K k x f s) (@lem4462162 A B K k x f s)). Qed.
Lemma lem4462164 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term1008 A B K k x f s) = (term1031 A B K k x f s).
Proof. exact (EQ_MP (@lem4462163 A B K k x f s) (@lem4462138 A B K k x f s)). Qed.
Lemma lem4462165 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term991 A B K k x f s) = (term1031 A B K k x f s).
Proof. exact (TRANS (@lem4462134 A B K k x f s) (@lem4462164 A B K k x f s)). Qed.
Lemma lem4462166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4462167 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term992 A B K k x f s) = (term1032 A B K k x f s).
Proof. exact (MK_COMB (@lem4462166) (@lem4462165 A B K k x f s)). Qed.
Lemma lem4462168 {B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) : (g = (@RESTRICTION K B k x)) = (g = (@RESTRICTION K B k x)).
Proof. exact (eq_refl (g = (@RESTRICTION K B k x))). Qed.
Lemma lem4462169 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term993 A B K f s g k x) = (term1033 A B K f s g k x).
Proof. exact (MK_COMB (@lem4462167 A B K k x f s) (@lem4462168 B K g k x)). Qed.
Lemma lem4462171 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1034 A P Q) = (term1035 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4462172 {A K : Type'} (P : type805 A K) (Q : Prop) : (term1036 A K P Q) = (term1037 A K P Q).
Proof. exact (@lem4462171 (K -> A) P Q). Qed.
Lemma lem4462173 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term1038 A B K f s g k x) = (term1039 A B K f s g k x).
Proof. exact (@lem4462172 A K (term1030 A B K k x f s) (g = (@RESTRICTION K B k x))). Qed.
Lemma lem4462174 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) : (term1040 A B K k x f s x') = (term1028 A B K k x f s x').
Proof. exact (eq_refl (term1040 A B K k x f s x')). Qed.
Lemma lem4462175 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term1041 A B K k x f s) = (term1030 A B K k x f s).
Proof. exact (fun_ext (fun x' : K -> A => @lem4462174 A B K k x f s x')). Qed.
Lemma lem4462176 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4462177 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term1042 A B K k x f s) = (term1031 A B K k x f s).
Proof. exact (MK_COMB (@lem4462176 A K) (@lem4462175 A B K k x f s)). Qed.
Lemma lem4462178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4462179 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) : (term1043 A B K k x f s) = (term1032 A B K k x f s).
Proof. exact (MK_COMB (@lem4462178) (@lem4462177 A B K k x f s)). Qed.
Lemma lem4462180 {B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) : (g = (@RESTRICTION K B k x)) = (g = (@RESTRICTION K B k x)).
Proof. exact (eq_refl (g = (@RESTRICTION K B k x))). Qed.
Lemma lem4462181 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term1038 A B K f s g k x) = (term1033 A B K f s g k x).
Proof. exact (MK_COMB (@lem4462179 A B K k x f s) (@lem4462180 B K g k x)). Qed.
Lemma lem4462182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4462183 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term1044 A B K f s g k x) = (term1045 A B K f s g k x).
Proof. exact (MK_COMB (@lem4462182) (@lem4462181 A B K f s g k x)). Qed.
Lemma lem4462184 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) : (term1040 A B K k x f s x') = (term1028 A B K k x f s x').
Proof. exact (eq_refl (term1040 A B K k x f s x')). Qed.
Lemma lem4462185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4462186 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) : (term1046 A B K k x f s x') = (term1047 A B K k x f s x').
Proof. exact (MK_COMB (@lem4462185) (@lem4462184 A B K k x f s x')). Qed.
Lemma lem4462187 {B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) : (g = (@RESTRICTION K B k x)) = (g = (@RESTRICTION K B k x)).
Proof. exact (eq_refl (g = (@RESTRICTION K B k x))). Qed.
Lemma lem4462188 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (x : K -> A) (g : K -> B) (k : K -> Prop) (x' : K -> B) : (term1048 A B K f s x g k x') = (term1049 A B K f s x g k x').
Proof. exact (MK_COMB (@lem4462186 A B K k x' f s x) (@lem4462187 B K g k x')). Qed.
Lemma lem4462189 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term1050 A B K f s g k x) = (term1051 A B K f s g k x).
Proof. exact (fun_ext (fun x' : K -> A => @lem4462188 A B K f s x' g k x)). Qed.
Lemma lem4462190 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4462191 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term1039 A B K f s g k x) = (term1052 A B K f s g k x).
Proof. exact (MK_COMB (@lem4462190 A K) (@lem4462189 A B K f s g k x)). Qed.
Lemma lem4462192 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : ((term1038 A B K f s g k x) = (term1039 A B K f s g k x)) = ((term1033 A B K f s g k x) = (term1052 A B K f s g k x)).
Proof. exact (MK_COMB (@lem4462183 A B K f s g k x) (@lem4462191 A B K f s g k x)). Qed.
Lemma lem4462193 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term1033 A B K f s g k x) = (term1052 A B K f s g k x).
Proof. exact (EQ_MP (@lem4462192 A B K f s g k x) (@lem4462173 A B K f s g k x)). Qed.
Lemma lem4462195 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term993 A B K f s g k x) = (term1052 A B K f s g k x).
Proof. exact (TRANS (@lem4462169 A B K f s g k x) (@lem4462193 A B K f s g k x)). Qed.
Lemma lem4462196 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term922 A B K f s g k x) = (term1052 A B K f s g k x).
Proof. exact (TRANS (@lem4462014 A B K f s g k x) (@lem4462195 A B K f s g k x)). Qed.
Lemma lem4462197 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term922 A B K f s g k x) : term1052 A B K f s g k x.
Proof. exact (EQ_MP (@lem4462196 A B K f s g k x) (@lem4461988 A B K f s g k x h1)). Qed.
Lemma lem4462200 {K : Type'} (k : K -> Prop) (x : K) : (term583 K k x) = (k x).
Proof. exact (@lem16933 (k x)). Qed.
Lemma lem4462201 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term1053 A B K x f x' x'') = (term1053 A B K x f x' x'').
Proof. exact (eq_refl (term1053 A B K x f x' x'')). Qed.
Lemma lem4462202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4462203 {K : Type'} (k : K -> Prop) (x : K) : (term585 K k x) = (term586 K k x).
Proof. exact (MK_COMB (@lem4462202) (@lem4462200 K k x)). Qed.
Lemma lem4462204 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term1054 A B K k x f x' x'') = (term1055 A B K k x f x' x'').
Proof. exact (MK_COMB (@lem4462203 K k x'') (@lem4462201 A B K x f x' x'')). Qed.
Lemma lem4462205 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term1056 A B K k x f x' x'') = (term1054 A B K k x f x' x'').
Proof. exact (@lem17160 (term590 K k x'') ((x x'') = (term433 A B K f x' x''))). Qed.
Lemma lem4462206 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term1056 A B K k x f x' x'') = (term1055 A B K k x f x' x'').
Proof. exact (TRANS (@lem4462205 A B K k x f x' x'') (@lem4462204 A B K k x f x' x'')). Qed.
Lemma lem4462207 {K : Type'} (P : K -> Prop) : (term591 K P) = (term592 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4462208 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) : (term1057 A B K k x f x') = (term1058 A B K k x f x').
Proof. exact (@lem4462207 K (term970 A B K k x f x')). Qed.
Lemma lem4462209 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term1059 A B K k x f x' x'') = (term969 A B K k x f x' x'').
Proof. exact (eq_refl (term1059 A B K k x f x' x'')). Qed.
Lemma lem4462210 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4462211 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term1060 A B K k x f x' x'') = (term1056 A B K k x f x' x'').
Proof. exact (MK_COMB (@lem4462210) (@lem4462209 A B K k x f x' x'')). Qed.
Lemma lem4462212 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (x'' : K) : (term1060 A B K k x f x' x'') = (term1055 A B K k x f x' x'').
Proof. exact (TRANS (@lem4462211 A B K k x f x' x'') (@lem4462206 A B K k x f x' x'')). Qed.
Lemma lem4462213 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) : (term1061 A B K k x f x') = (term1062 A B K k x f x').
Proof. exact (fun_ext (fun x'' : K => @lem4462212 A B K k x f x' x'')). Qed.
Lemma lem4462214 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4462215 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) : (term1058 A B K k x f x') = (term1063 A B K k x f x').
Proof. exact (MK_COMB (@lem4462214 K) (@lem4462213 A B K k x f x')). Qed.
Lemma lem4462216 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) : (term1057 A B K k x f x') = (term1063 A B K k x f x').
Proof. exact (TRANS (@lem4462208 A B K k x f x') (@lem4462215 A B K k x f x')). Qed.
Lemma lem4462223 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term1064 A K k s x i) = (term1065 A K k s x i).
Proof. exact (@lem17362 (k i) (term266 A K s x i)). Qed.
Lemma lem4462224 {K : Type'} (P : K -> Prop) : (term591 K P) = (term592 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4462225 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term1066 A K k s x) = (term1067 A K k s x).
Proof. exact (@lem4462224 K (term270 A K k s x)). Qed.
Lemma lem4462226 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term1068 A K k s x i) = (term268 A K k s x i).
Proof. exact (eq_refl (term1068 A K k s x i)). Qed.
Lemma lem4462227 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4462228 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term1069 A K k s x i) = (term1064 A K k s x i).
Proof. exact (MK_COMB (@lem4462227) (@lem4462226 A K k s x i)). Qed.
Lemma lem4462229 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term1069 A K k s x i) = (term1065 A K k s x i).
Proof. exact (TRANS (@lem4462228 A K k s x i) (@lem4462223 A K k s x i)). Qed.
Lemma lem4462230 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term1070 A K k s x) = (term1071 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4462229 A K k s x i)). Qed.
Lemma lem4462231 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4462232 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term1067 A K k s x) = (term1072 A K k s x).
Proof. exact (MK_COMB (@lem4462231 K) (@lem4462230 A K k s x)). Qed.
Lemma lem4462233 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term1066 A K k s x) = (term1072 A K k s x).
Proof. exact (TRANS (@lem4462225 A K k s x) (@lem4462232 A K k s x)). Qed.
Lemma lem4462234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4462235 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) : (term1073 A B K k x f x') = (term1074 A B K k x f x').
Proof. exact (MK_COMB (@lem4462234) (@lem4462216 A B K k x f x')). Qed.
Lemma lem4462236 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1075 A B K x f k s x') = (term1076 A B K x f k s x').
Proof. exact (MK_COMB (@lem4462235 A B K k x f x') (@lem4462233 A K k s x')). Qed.
Lemma lem4462237 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1077 A B K x f k s x') = (term1075 A B K x f k s x').
Proof. exact (@lem17045 (term971 A B K k x f x') (term271 A K k s x')). Qed.
Lemma lem4462238 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1077 A B K x f k s x') = (term1076 A B K x f k s x').
Proof. exact (TRANS (@lem4462237 A B K x f k s x') (@lem4462236 A B K x f k s x')). Qed.
Lemma lem4462239 {A K : Type'} (P : type805 A K) : (term626 A K P) = (term627 A K P).
Proof. exact (@lem18394 (K -> A) P). Qed.
Lemma lem4462240 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term988 A B K x f k s) = (term1078 A B K x f k s).
Proof. exact (@lem4462239 A K (term974 A B K x f k s)). Qed.
Lemma lem4462241 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1079 A B K x f k s x') = (term973 A B K x f k s x').
Proof. exact (eq_refl (term1079 A B K x f k s x')). Qed.
Lemma lem4462242 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4462243 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1080 A B K x f k s x') = (term1077 A B K x f k s x').
Proof. exact (MK_COMB (@lem4462242) (@lem4462241 A B K x f k s x')). Qed.
Lemma lem4462244 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1080 A B K x f k s x') = (term1076 A B K x f k s x').
Proof. exact (TRANS (@lem4462243 A B K x f k s x') (@lem4462238 A B K x f k s x')). Qed.
Lemma lem4462245 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1081 A B K x f k s) = (term1082 A B K x f k s).
Proof. exact (fun_ext (fun x' : K -> A => @lem4462244 A B K x f k s x')). Qed.
Lemma lem4462246 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4462247 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1078 A B K x f k s) = (term1083 A B K x f k s).
Proof. exact (MK_COMB (@lem4462246 A K) (@lem4462245 A B K x f k s)). Qed.
Lemma lem4462248 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term988 A B K x f k s) = (term1083 A B K x f k s).
Proof. exact (TRANS (@lem4462240 A B K x f k s) (@lem4462247 A B K x f k s)). Qed.
Lemma lem4462355 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term634 A P Q) = (term635 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4462356 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term634 K P Q) = (term635 K P Q).
Proof. exact (@lem4462355 K P Q). Qed.
Lemma lem4462357 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1084 A B K x f k s x') = (term1085 A B K x f k s x').
Proof. exact (@lem4462356 K (term1062 A B K k x f x') (term1071 A K k s x')). Qed.
Lemma lem4462358 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (i : K) : (term1086 A B K k x f x' i) = (term1055 A B K k x f x' i).
Proof. exact (eq_refl (term1086 A B K k x f x' i)). Qed.
Lemma lem4462359 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) : (term1087 A B K k x f x') = (term1062 A B K k x f x').
Proof. exact (fun_ext (fun i : K => @lem4462358 A B K k x f x' i)). Qed.
Lemma lem4462360 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4462361 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) : (term1088 A B K k x f x') = (term1063 A B K k x f x').
Proof. exact (MK_COMB (@lem4462360 K) (@lem4462359 A B K k x f x')). Qed.
Lemma lem4462362 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4462363 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) : (term1089 A B K k x f x') = (term1074 A B K k x f x').
Proof. exact (MK_COMB (@lem4462362) (@lem4462361 A B K k x f x')). Qed.
Lemma lem4462364 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term1090 A K k s x i) = (term1065 A K k s x i).
Proof. exact (eq_refl (term1090 A K k s x i)). Qed.
Lemma lem4462365 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term1091 A K k s x) = (term1071 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4462364 A K k s x i)). Qed.
Lemma lem4462366 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4462367 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term1092 A K k s x) = (term1072 A K k s x).
Proof. exact (MK_COMB (@lem4462366 K) (@lem4462365 A K k s x)). Qed.
Lemma lem4462368 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1084 A B K x f k s x') = (term1076 A B K x f k s x').
Proof. exact (MK_COMB (@lem4462363 A B K k x f x') (@lem4462367 A K k s x')). Qed.
Lemma lem4462369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4462370 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1093 A B K x f k s x') = (term1094 A B K x f k s x').
Proof. exact (MK_COMB (@lem4462369) (@lem4462368 A B K x f k s x')). Qed.
Lemma lem4462371 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (i : K) : (term1086 A B K k x f x' i) = (term1055 A B K k x f x' i).
Proof. exact (eq_refl (term1086 A B K k x f x' i)). Qed.
Lemma lem4462372 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4462373 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (i : K) : (term1095 A B K k x f x' i) = (term1096 A B K k x f x' i).
Proof. exact (MK_COMB (@lem4462372) (@lem4462371 A B K k x f x' i)). Qed.
Lemma lem4462374 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term1090 A K k s x i) = (term1065 A K k s x i).
Proof. exact (eq_refl (term1090 A K k s x i)). Qed.
Lemma lem4462375 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) (i : K) : (term1097 A B K x f k s x' i) = (term1098 A B K x f k s x' i).
Proof. exact (MK_COMB (@lem4462373 A B K k x f x' i) (@lem4462374 A K k s x' i)). Qed.
Lemma lem4462376 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1099 A B K x f k s x') = (term1100 A B K x f k s x').
Proof. exact (fun_ext (fun i : K => @lem4462375 A B K x f k s x' i)). Qed.
Lemma lem4462377 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4462378 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1085 A B K x f k s x') = (term1101 A B K x f k s x').
Proof. exact (MK_COMB (@lem4462377 K) (@lem4462376 A B K x f k s x')). Qed.
Lemma lem4462379 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : ((term1084 A B K x f k s x') = (term1085 A B K x f k s x')) = ((term1076 A B K x f k s x') = (term1101 A B K x f k s x')).
Proof. exact (MK_COMB (@lem4462370 A B K x f k s x') (@lem4462378 A B K x f k s x')). Qed.
Lemma lem4462380 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1076 A B K x f k s x') = (term1101 A B K x f k s x').
Proof. exact (EQ_MP (@lem4462379 A B K x f k s x') (@lem4462357 A B K x f k s x')). Qed.
Lemma lem4462383 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1102 A B K x f k s x') = (term1102 A B K x f k s x').
Proof. exact (eq_refl (term1102 A B K x f k s x')). Qed.
Lemma lem4462384 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1102 A B K x f k s x') = ((term1076 A B K x f k s x') = (term1101 A B K x f k s x')).
Proof. exact (eq_refl (term1102 A B K x f k s x')). Qed.
Lemma lem4462385 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1103 A B K x f k s x') = (term1103 A B K x f k s x').
Proof. exact (eq_refl (term1103 A B K x f k s x')). Qed.
Lemma lem4462386 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : ((term1102 A B K x f k s x') = (term1102 A B K x f k s x')) = ((term1102 A B K x f k s x') = ((term1076 A B K x f k s x') = (term1101 A B K x f k s x'))).
Proof. exact (MK_COMB (@lem4462385 A B K x f k s x') (@lem4462384 A B K x f k s x')). Qed.
Lemma lem4462387 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1102 A B K x f k s x') = ((term1076 A B K x f k s x') = (term1101 A B K x f k s x')).
Proof. exact (eq_refl (term1102 A B K x f k s x')). Qed.
Lemma lem4462388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4462389 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1103 A B K x f k s x') = (term1104 A B K x f k s x').
Proof. exact (MK_COMB (@lem4462388) (@lem4462387 A B K x f k s x')). Qed.
Lemma lem4462390 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : ((term1076 A B K x f k s x') = (term1101 A B K x f k s x')) = ((term1076 A B K x f k s x') = (term1101 A B K x f k s x')).
Proof. exact (eq_refl ((term1076 A B K x f k s x') = (term1101 A B K x f k s x'))). Qed.
Lemma lem4462391 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : ((term1102 A B K x f k s x') = ((term1076 A B K x f k s x') = (term1101 A B K x f k s x'))) = (((term1076 A B K x f k s x') = (term1101 A B K x f k s x')) = ((term1076 A B K x f k s x') = (term1101 A B K x f k s x'))).
Proof. exact (MK_COMB (@lem4462389 A B K x f k s x') (@lem4462390 A B K x f k s x')). Qed.
Lemma lem4462392 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : ((term1102 A B K x f k s x') = (term1102 A B K x f k s x')) = (((term1076 A B K x f k s x') = (term1101 A B K x f k s x')) = ((term1076 A B K x f k s x') = (term1101 A B K x f k s x'))).
Proof. exact (TRANS (@lem4462386 A B K x f k s x') (@lem4462391 A B K x f k s x')). Qed.
Lemma lem4462393 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : ((term1076 A B K x f k s x') = (term1101 A B K x f k s x')) = ((term1076 A B K x f k s x') = (term1101 A B K x f k s x')).
Proof. exact (EQ_MP (@lem4462392 A B K x f k s x') (@lem4462383 A B K x f k s x')). Qed.
Lemma lem4462394 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1076 A B K x f k s x') = (term1101 A B K x f k s x').
Proof. exact (EQ_MP (@lem4462393 A B K x f k s x') (@lem4462380 A B K x f k s x')). Qed.
Lemma lem4462395 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1082 A B K x f k s) = (term1105 A B K x f k s).
Proof. exact (fun_ext (fun x' : K -> A => @lem4462394 A B K x f k s x')). Qed.
Lemma lem4462396 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4462397 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1083 A B K x f k s) = (term1106 A B K x f k s).
Proof. exact (MK_COMB (@lem4462396 A K) (@lem4462395 A B K x f k s)). Qed.
Lemma lem4462399 {A B : Type'} (P : type1413 A B) : (term659 A B P) = (term660 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4462400 {A K : Type'} (P : type799 A K) : (term661 A K P) = (term662 A K P).
Proof. exact (@lem4462399 (K -> A) K P). Qed.
Lemma lem4462401 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1107 A B K x f k s) = (term1108 A B K x f k s).
Proof. exact (@lem4462400 A K (term1109 A B K x f k s)). Qed.
Lemma lem4462402 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1110 A B K x f k s x') = (term1100 A B K x f k s x').
Proof. exact (eq_refl (term1110 A B K x f k s x')). Qed.
Lemma lem4462403 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4462404 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) (i : K) : (term1111 A B K x f k s x' i) = (term1112 A B K x f k s x' i).
Proof. exact (MK_COMB (@lem4462402 A B K x f k s x') (@lem4462403 K i)). Qed.
Lemma lem4462405 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) (i : K) : (term1112 A B K x f k s x' i) = (term1098 A B K x f k s x' i).
Proof. exact (eq_refl (term1112 A B K x f k s x' i)). Qed.
Lemma lem4462406 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) (i : K) : (term1111 A B K x f k s x' i) = (term1098 A B K x f k s x' i).
Proof. exact (TRANS (@lem4462404 A B K x f k s x' i) (@lem4462405 A B K x f k s x' i)). Qed.
Lemma lem4462407 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1113 A B K x f k s x') = (term1100 A B K x f k s x').
Proof. exact (fun_ext (fun i : K => @lem4462406 A B K x f k s x' i)). Qed.
Lemma lem4462408 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4462409 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1114 A B K x f k s x') = (term1101 A B K x f k s x').
Proof. exact (MK_COMB (@lem4462408 K) (@lem4462407 A B K x f k s x')). Qed.
Lemma lem4462410 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1115 A B K x f k s) = (term1105 A B K x f k s).
Proof. exact (fun_ext (fun x' : K -> A => @lem4462409 A B K x f k s x')). Qed.
Lemma lem4462411 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4462412 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1107 A B K x f k s) = (term1106 A B K x f k s).
Proof. exact (MK_COMB (@lem4462411 A K) (@lem4462410 A B K x f k s)). Qed.
Lemma lem4462413 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4462414 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1116 A B K x f k s) = (term1117 A B K x f k s).
Proof. exact (MK_COMB (@lem4462413) (@lem4462412 A B K x f k s)). Qed.
Lemma lem4462415 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1110 A B K x f k s x') = (term1100 A B K x f k s x').
Proof. exact (eq_refl (term1110 A B K x f k s x')). Qed.
Lemma lem4462416 {A K : Type'} (i : type803 A K) (x : K -> A) : (i x) = (i x).
Proof. exact (eq_refl (i x)). Qed.
Lemma lem4462417 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (x' : K -> A) : (term1118 A B K x f k s i x') = (term1119 A B K x f k s i x').
Proof. exact (MK_COMB (@lem4462415 A B K x f k s x') (@lem4462416 A K i x')). Qed.
Lemma lem4462418 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (x' : K -> A) : (term1119 A B K x f k s i x') = (term1120 A B K x f k s i x').
Proof. exact (eq_refl (term1119 A B K x f k s i x')). Qed.
Lemma lem4462419 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (x' : K -> A) : (term1118 A B K x f k s i x') = (term1120 A B K x f k s i x').
Proof. exact (TRANS (@lem4462417 A B K x f k s i x') (@lem4462418 A B K x f k s i x')). Qed.
Lemma lem4462420 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) : (term1121 A B K x f k s i) = (term1122 A B K x f k s i).
Proof. exact (fun_ext (fun x' : K -> A => @lem4462419 A B K x f k s i x')). Qed.
Lemma lem4462421 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4462422 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) : (term1123 A B K x f k s i) = (term1124 A B K x f k s i).
Proof. exact (MK_COMB (@lem4462421 A K) (@lem4462420 A B K x f k s i)). Qed.
Lemma lem4462423 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1125 A B K x f k s) = (term1126 A B K x f k s).
Proof. exact (fun_ext (fun i : type803 A K => @lem4462422 A B K x f k s i)). Qed.
Lemma lem4462424 {A K : Type'} : (@ex ((K -> A) -> K)) = (@ex ((K -> A) -> K)).
Proof. exact (eq_refl (@ex ((K -> A) -> K))). Qed.
Lemma lem4462425 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1108 A B K x f k s) = (term1127 A B K x f k s).
Proof. exact (MK_COMB (@lem4462424 A K) (@lem4462423 A B K x f k s)). Qed.
Lemma lem4462426 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : ((term1107 A B K x f k s) = (term1108 A B K x f k s)) = ((term1106 A B K x f k s) = (term1127 A B K x f k s)).
Proof. exact (MK_COMB (@lem4462414 A B K x f k s) (@lem4462425 A B K x f k s)). Qed.
Lemma lem4462427 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1106 A B K x f k s) = (term1127 A B K x f k s).
Proof. exact (EQ_MP (@lem4462426 A B K x f k s) (@lem4462401 A B K x f k s)). Qed.
Lemma lem4462429 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1083 A B K x f k s) = (term1127 A B K x f k s).
Proof. exact (TRANS (@lem4462397 A B K x f k s) (@lem4462427 A B K x f k s)). Qed.
Lemma lem4462430 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term988 A B K x f k s) = (term1127 A B K x f k s).
Proof. exact (TRANS (@lem4462248 A B K x f k s) (@lem4462429 A B K x f k s)). Qed.
Lemma lem4462431 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term988 A B K x f k s) : term1127 A B K x f k s.
Proof. exact (EQ_MP (@lem4462430 A B K x f k s) (@lem4461993 A B K x f k s h1)). Qed.
Lemma lem4462432 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term1124 A B K x f k s i.
Proof. exact (h1). Qed.
Lemma lem4462433 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term1049 A B K f s x' g k x.
Proof. exact (h1). Qed.
Lemma lem4462434 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4462435 {A K : Type'} (s : type1470 A K) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4462440 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462441 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4462440 (K -> A) K f x). Qed.
Lemma lem4462443 {A K : Type'} (i : type803 A K) (x : K -> A) : (i x) = (@I ((K -> A) -> K) i x).
Proof. exact (@lem4462441 A K i x). Qed.
Lemma lem4462444 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4462449 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462450 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4462449 (K -> A) K f x). Qed.
Lemma lem4462452 {A K : Type'} (i : type803 A K) (x : K -> A) : (i x) = (@I ((K -> A) -> K) i x).
Proof. exact (@lem4462450 A K i x). Qed.
Lemma lem4462453 {A K : Type'} (i : type803 A K) (x : K -> A) : (term739 A K i x) = (term740 A K i x).
Proof. exact (MK_COMB (@lem4462444 A K x) (@lem4462452 A K i x)). Qed.
Lemma lem4462455 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462456 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4462455 K A f x). Qed.
Lemma lem4462457 {A K : Type'} (i : type803 A K) (x : K -> A) : (term740 A K i x) = (term741 A K i x).
Proof. exact (@lem4462456 A K x (@I ((K -> A) -> K) i x)). Qed.
Lemma lem4462458 {A K : Type'} (i : type803 A K) (x : K -> A) : (term739 A K i x) = (term741 A K i x).
Proof. exact (TRANS (@lem4462453 A K i x) (@lem4462457 A K i x)). Qed.
Lemma lem4462459 {A K : Type'} (s : type1470 A K) (i : type803 A K) (x : K -> A) : (term1128 A K s i x) = (term1129 A K s i x).
Proof. exact (MK_COMB (@lem4462435 A K s) (@lem4462443 A K i x)). Qed.
Lemma lem4462460 {A K : Type'} (s : type1470 A K) (i : type803 A K) (x : K -> A) : (term1130 A K s i x) = (term1131 A K s i x).
Proof. exact (MK_COMB (@lem4462459 A K s i x) (@lem4462458 A K i x)). Qed.
Lemma lem4462462 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462463 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4462462 K (A -> Prop) f x). Qed.
Lemma lem4462464 {A K : Type'} (s : type1470 A K) (i : type803 A K) (x : K -> A) : (term1129 A K s i x) = (term1132 A K s i x).
Proof. exact (@lem4462463 A K s (@I ((K -> A) -> K) i x)). Qed.
Lemma lem4462465 {A K : Type'} (i : type803 A K) (x : K -> A) : (term741 A K i x) = (term741 A K i x).
Proof. exact (eq_refl (term741 A K i x)). Qed.
Lemma lem4462466 {A K : Type'} (s : type1470 A K) (i : type803 A K) (x : K -> A) : (term1131 A K s i x) = (term1133 A K s i x).
Proof. exact (MK_COMB (@lem4462464 A K s i x) (@lem4462465 A K i x)). Qed.
Lemma lem4462468 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462469 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4462468 A Prop f x). Qed.
Lemma lem4462470 {A K : Type'} (s : type1470 A K) (i : type803 A K) (x : K -> A) : (term1133 A K s i x) = (term1134 A K s i x).
Proof. exact (@lem4462469 A (term1132 A K s i x) (term741 A K i x)). Qed.
Lemma lem4462471 {A K : Type'} (s : type1470 A K) (i : type803 A K) (x : K -> A) : (term1131 A K s i x) = (term1134 A K s i x).
Proof. exact (TRANS (@lem4462466 A K s i x) (@lem4462470 A K s i x)). Qed.
Lemma lem4462472 {A K : Type'} (s : type1470 A K) (i : type803 A K) (x : K -> A) : (term1130 A K s i x) = (term1134 A K s i x).
Proof. exact (TRANS (@lem4462460 A K s i x) (@lem4462471 A K s i x)). Qed.
Lemma lem4462473 {A K : Type'} (s : type1470 A K) (i : type803 A K) (x : K -> A) : (term1135 A K s i x) = (term1136 A K s i x).
Proof. exact (MK_COMB (@lem4462434) (@lem4462472 A K s i x)). Qed.
Lemma lem4462474 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4462479 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462480 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4462479 (K -> A) K f x). Qed.
Lemma lem4462482 {A K : Type'} (i : type803 A K) (x : K -> A) : (i x) = (@I ((K -> A) -> K) i x).
Proof. exact (@lem4462480 A K i x). Qed.
Lemma lem4462483 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x : K -> A) : (term761 A K k i x) = (term762 A K k i x).
Proof. exact (MK_COMB (@lem4462474 K k) (@lem4462482 A K i x)). Qed.
Lemma lem4462485 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462486 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4462485 K Prop f x). Qed.
Lemma lem4462487 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x : K -> A) : (term762 A K k i x) = (term763 A K k i x).
Proof. exact (@lem4462486 K k (@I ((K -> A) -> K) i x)). Qed.
Lemma lem4462488 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x : K -> A) : (term761 A K k i x) = (term763 A K k i x).
Proof. exact (TRANS (@lem4462483 A K k i x) (@lem4462487 A K k i x)). Qed.
Lemma lem4462489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4462490 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x : K -> A) : (term764 A K k i x) = (term765 A K k i x).
Proof. exact (MK_COMB (@lem4462489) (@lem4462488 A K k i x)). Qed.
Lemma lem4462491 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (x : K -> A) : (term1137 A K k s i x) = (term1138 A K k s i x).
Proof. exact (MK_COMB (@lem4462490 A K k i x) (@lem4462473 A K s i x)). Qed.
Lemma lem4462492 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4462493 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4462494 {B K : Type'} (x : K -> B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4462499 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462500 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4462499 (K -> A) K f x). Qed.
Lemma lem4462502 {A K : Type'} (i : type803 A K) (x : K -> A) : (i x) = (@I ((K -> A) -> K) i x).
Proof. exact (@lem4462500 A K i x). Qed.
Lemma lem4462503 {A B K : Type'} (x : K -> B) (i : type803 A K) (x' : K -> A) : (term1139 A B K x i x') = (term1140 A B K x i x').
Proof. exact (MK_COMB (@lem4462494 B K x) (@lem4462502 A K i x')). Qed.
Lemma lem4462505 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462506 {B K : Type'} (f : K -> B) (x : K) : (f x) = (@I (K -> B) f x).
Proof. exact (@lem4462505 K B f x). Qed.
Lemma lem4462507 {A B K : Type'} (x : K -> B) (i : type803 A K) (x' : K -> A) : (term1140 A B K x i x') = (term1141 A B K x i x').
Proof. exact (@lem4462506 B K x (@I ((K -> A) -> K) i x')). Qed.
Lemma lem4462508 {A B K : Type'} (x : K -> B) (i : type803 A K) (x' : K -> A) : (term1139 A B K x i x') = (term1141 A B K x i x').
Proof. exact (TRANS (@lem4462503 A B K x i x') (@lem4462507 A B K x i x')). Qed.
Lemma lem4462509 {A B K : Type'} (f : type1514 A B K) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4462514 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462515 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4462514 (K -> A) K f x). Qed.
Lemma lem4462517 {A K : Type'} (i : type803 A K) (x : K -> A) : (i x) = (@I ((K -> A) -> K) i x).
Proof. exact (@lem4462515 A K i x). Qed.
Lemma lem4462518 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4462523 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462524 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4462523 (K -> A) K f x). Qed.
Lemma lem4462526 {A K : Type'} (i : type803 A K) (x : K -> A) : (i x) = (@I ((K -> A) -> K) i x).
Proof. exact (@lem4462524 A K i x). Qed.
Lemma lem4462527 {A K : Type'} (i : type803 A K) (x : K -> A) : (term739 A K i x) = (term740 A K i x).
Proof. exact (MK_COMB (@lem4462518 A K x) (@lem4462526 A K i x)). Qed.
Lemma lem4462529 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462530 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4462529 K A f x). Qed.
Lemma lem4462531 {A K : Type'} (i : type803 A K) (x : K -> A) : (term740 A K i x) = (term741 A K i x).
Proof. exact (@lem4462530 A K x (@I ((K -> A) -> K) i x)). Qed.
Lemma lem4462532 {A K : Type'} (i : type803 A K) (x : K -> A) : (term739 A K i x) = (term741 A K i x).
Proof. exact (TRANS (@lem4462527 A K i x) (@lem4462531 A K i x)). Qed.
Lemma lem4462533 {A B K : Type'} (f : type1514 A B K) (i : type803 A K) (x : K -> A) : (term1142 A B K f i x) = (term1143 A B K f i x).
Proof. exact (MK_COMB (@lem4462509 A B K f) (@lem4462517 A K i x)). Qed.
Lemma lem4462534 {A B K : Type'} (f : type1514 A B K) (i : type803 A K) (x : K -> A) : (term1144 A B K f i x) = (term1145 A B K f i x).
Proof. exact (MK_COMB (@lem4462533 A B K f i x) (@lem4462532 A K i x)). Qed.
Lemma lem4462536 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462537 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (@I (K -> A -> B) f x).
Proof. exact (@lem4462536 K (A -> B) f x). Qed.
Lemma lem4462538 {A B K : Type'} (f : type1514 A B K) (i : type803 A K) (x : K -> A) : (term1143 A B K f i x) = (term1146 A B K f i x).
Proof. exact (@lem4462537 A B K f (@I ((K -> A) -> K) i x)). Qed.
Lemma lem4462539 {A K : Type'} (i : type803 A K) (x : K -> A) : (term741 A K i x) = (term741 A K i x).
Proof. exact (eq_refl (term741 A K i x)). Qed.
Lemma lem4462540 {A B K : Type'} (f : type1514 A B K) (i : type803 A K) (x : K -> A) : (term1145 A B K f i x) = (term1147 A B K f i x).
Proof. exact (MK_COMB (@lem4462538 A B K f i x) (@lem4462539 A K i x)). Qed.
Lemma lem4462542 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462543 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4462542 A B f x). Qed.
Lemma lem4462544 {A B K : Type'} (f : type1514 A B K) (i : type803 A K) (x : K -> A) : (term1147 A B K f i x) = (term1148 A B K f i x).
Proof. exact (@lem4462543 A B (term1146 A B K f i x) (term741 A K i x)). Qed.
Lemma lem4462545 {A B K : Type'} (f : type1514 A B K) (i : type803 A K) (x : K -> A) : (term1145 A B K f i x) = (term1148 A B K f i x).
Proof. exact (TRANS (@lem4462540 A B K f i x) (@lem4462544 A B K f i x)). Qed.
Lemma lem4462546 {A B K : Type'} (f : type1514 A B K) (i : type803 A K) (x : K -> A) : (term1144 A B K f i x) = (term1148 A B K f i x).
Proof. exact (TRANS (@lem4462534 A B K f i x) (@lem4462545 A B K f i x)). Qed.
Lemma lem4462547 {A B K : Type'} (x : K -> B) (i : type803 A K) (x' : K -> A) : (term1149 A B K x i x') = (term1150 A B K x i x').
Proof. exact (MK_COMB (@lem4462493 B) (@lem4462508 A B K x i x')). Qed.
Lemma lem4462548 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (i : type803 A K) (x' : K -> A) : ((term1139 A B K x i x') = (term1144 A B K f i x')) = ((term1141 A B K x i x') = (term1148 A B K f i x')).
Proof. exact (MK_COMB (@lem4462547 A B K x i x') (@lem4462546 A B K f i x')). Qed.
Lemma lem4462549 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (i : type803 A K) (x' : K -> A) : (term1151 A B K x f i x') = (term1152 A B K x f i x').
Proof. exact (MK_COMB (@lem4462492) (@lem4462548 A B K x f i x')). Qed.
Lemma lem4462550 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem4462555 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462556 {A K : Type'} (f : type803 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> K) f x).
Proof. exact (@lem4462555 (K -> A) K f x). Qed.
Lemma lem4462558 {A K : Type'} (i : type803 A K) (x : K -> A) : (i x) = (@I ((K -> A) -> K) i x).
Proof. exact (@lem4462556 A K i x). Qed.
Lemma lem4462559 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x : K -> A) : (term761 A K k i x) = (term762 A K k i x).
Proof. exact (MK_COMB (@lem4462550 K k) (@lem4462558 A K i x)). Qed.
Lemma lem4462561 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462562 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4462561 K Prop f x). Qed.
Lemma lem4462563 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x : K -> A) : (term762 A K k i x) = (term763 A K k i x).
Proof. exact (@lem4462562 K k (@I ((K -> A) -> K) i x)). Qed.
Lemma lem4462564 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x : K -> A) : (term761 A K k i x) = (term763 A K k i x).
Proof. exact (TRANS (@lem4462559 A K k i x) (@lem4462563 A K k i x)). Qed.
Lemma lem4462565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4462566 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x : K -> A) : (term764 A K k i x) = (term765 A K k i x).
Proof. exact (MK_COMB (@lem4462565) (@lem4462564 A K k i x)). Qed.
Lemma lem4462567 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (i : type803 A K) (x' : K -> A) : (term1153 A B K k x f i x') = (term1154 A B K k x f i x').
Proof. exact (MK_COMB (@lem4462566 A K k i x') (@lem4462549 A B K x f i x')). Qed.
Lemma lem4462568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4462569 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (i : type803 A K) (x' : K -> A) : (term1155 A B K k x f i x') = (term1156 A B K k x f i x').
Proof. exact (MK_COMB (@lem4462568) (@lem4462567 A B K k x f i x')). Qed.
Lemma lem4462570 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (x' : K -> A) : (term1120 A B K x f k s i x') = (term1157 A B K x f k s i x').
Proof. exact (MK_COMB (@lem4462569 A B K k x f i x') (@lem4462491 A K k s i x')). Qed.
Lemma lem4462571 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) : (term1122 A B K x f k s i) = (term1158 A B K x f k s i).
Proof. exact (fun_ext (fun x' : K -> A => @lem4462570 A B K x f k s i x')). Qed.
Lemma lem4462572 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4462573 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) : (term1124 A B K x f k s i) = (term1159 A B K x f k s i).
Proof. exact (MK_COMB (@lem4462572 A K) (@lem4462571 A B K x f k s i)). Qed.
Lemma lem4462574 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term1159 A B K x f k s i.
Proof. exact (EQ_MP (@lem4462573 A B K x f k s i) (@lem4462432 A B K x f k s i h1)). Qed.
Lemma lem4462583 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462584 {B K : Type'} (f : type853 B K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> B) -> K -> B) f x).
Proof. exact (@lem4462583 (K -> Prop) (type796 B K) f x). Qed.
Lemma lem4462585 {B K : Type'} (k : K -> Prop) : (@RESTRICTION K B k) = (@I ((K -> Prop) -> (K -> B) -> K -> B) (@RESTRICTION K B) k).
Proof. exact (@lem4462584 B K (@RESTRICTION K B) k). Qed.
Lemma lem4462586 {B K : Type'} (x : K -> B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4462587 {B K : Type'} (k : K -> Prop) (x : K -> B) : (@RESTRICTION K B k x) = (@I ((K -> Prop) -> (K -> B) -> K -> B) (@RESTRICTION K B) k x).
Proof. exact (MK_COMB (@lem4462585 B K k) (@lem4462586 B K x)). Qed.
Lemma lem4462589 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462590 {B K : Type'} (f : type796 B K) (x : K -> B) : (f x) = (@I ((K -> B) -> K -> B) f x).
Proof. exact (@lem4462589 (K -> B) (K -> B) f x). Qed.
Lemma lem4462591 {B K : Type'} (k : K -> Prop) (x : K -> B) : (@I ((K -> Prop) -> (K -> B) -> K -> B) (@RESTRICTION K B) k x) = (term1160 B K k x).
Proof. exact (@lem4462590 B K (@I ((K -> Prop) -> (K -> B) -> K -> B) (@RESTRICTION K B) k) x). Qed.
Lemma lem4462593 {B K : Type'} (k : K -> Prop) (x : K -> B) : (@RESTRICTION K B k x) = (term1160 B K k x).
Proof. exact (TRANS (@lem4462587 B K k x) (@lem4462591 B K k x)). Qed.
Lemma lem4462594 {B K : Type'} (g : K -> B) : (@eq (K -> B) g) = (@eq (K -> B) g).
Proof. exact (eq_refl (@eq (K -> B) g)). Qed.
Lemma lem4462595 {B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) : (g = (@RESTRICTION K B k x)) = (g = (term1160 B K k x)).
Proof. exact (MK_COMB (@lem4462594 B K g) (@lem4462593 B K k x)). Qed.
Lemma lem4462602 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462603 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4462602 K A f x). Qed.
Lemma lem4462605 {A K : Type'} (x' : K -> A) (i : K) : (x' i) = (@I (K -> A) x' i).
Proof. exact (@lem4462603 A K x' i). Qed.
Lemma lem4462606 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4462607 {A K : Type'} (s : type1470 A K) (x' : K -> A) (i : K) : (term266 A K s x' i) = (term722 A K s x' i).
Proof. exact (MK_COMB (@lem4462606 A K s i) (@lem4462605 A K x' i)). Qed.
Lemma lem4462609 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462610 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4462609 K (A -> Prop) f x). Qed.
Lemma lem4462611 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4462610 A K s i). Qed.
Lemma lem4462612 {A K : Type'} (x' : K -> A) (i : K) : (@I (K -> A) x' i) = (@I (K -> A) x' i).
Proof. exact (eq_refl (@I (K -> A) x' i)). Qed.
Lemma lem4462613 {A K : Type'} (s : type1470 A K) (x' : K -> A) (i : K) : (term722 A K s x' i) = (term723 A K s x' i).
Proof. exact (MK_COMB (@lem4462611 A K s i) (@lem4462612 A K x' i)). Qed.
Lemma lem4462615 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462616 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4462615 A Prop f x). Qed.
Lemma lem4462617 {A K : Type'} (s : type1470 A K) (x' : K -> A) (i : K) : (term723 A K s x' i) = (term724 A K s x' i).
Proof. exact (@lem4462616 A (@I (K -> A -> Prop) s i) (@I (K -> A) x' i)). Qed.
Lemma lem4462618 {A K : Type'} (s : type1470 A K) (x' : K -> A) (i : K) : (term722 A K s x' i) = (term724 A K s x' i).
Proof. exact (TRANS (@lem4462613 A K s x' i) (@lem4462617 A K s x' i)). Qed.
Lemma lem4462619 {A K : Type'} (s : type1470 A K) (x' : K -> A) (i : K) : (term266 A K s x' i) = (term724 A K s x' i).
Proof. exact (TRANS (@lem4462607 A K s x' i) (@lem4462618 A K s x' i)). Qed.
Lemma lem4462620 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4462625 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462626 {B K : Type'} (f : K -> B) (x : K) : (f x) = (@I (K -> B) f x).
Proof. exact (@lem4462625 K B f x). Qed.
Lemma lem4462628 {B K : Type'} (x : K -> B) (i : K) : (x i) = (@I (K -> B) x i).
Proof. exact (@lem4462626 B K x i). Qed.
Lemma lem4462635 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462636 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4462635 K A f x). Qed.
Lemma lem4462638 {A K : Type'} (x' : K -> A) (i : K) : (x' i) = (@I (K -> A) x' i).
Proof. exact (@lem4462636 A K x' i). Qed.
Lemma lem4462639 {A B K : Type'} (f : type1514 A B K) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4462640 {A B K : Type'} (f : type1514 A B K) (x' : K -> A) (i : K) : (term433 A B K f x' i) = (term702 A B K f x' i).
Proof. exact (MK_COMB (@lem4462639 A B K f i) (@lem4462638 A K x' i)). Qed.
Lemma lem4462642 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462643 {A B K : Type'} (f : type1514 A B K) (x : K) : (f x) = (@I (K -> A -> B) f x).
Proof. exact (@lem4462642 K (A -> B) f x). Qed.
Lemma lem4462644 {A B K : Type'} (f : type1514 A B K) (i : K) : (f i) = (@I (K -> A -> B) f i).
Proof. exact (@lem4462643 A B K f i). Qed.
Lemma lem4462645 {A K : Type'} (x' : K -> A) (i : K) : (@I (K -> A) x' i) = (@I (K -> A) x' i).
Proof. exact (eq_refl (@I (K -> A) x' i)). Qed.
Lemma lem4462646 {A B K : Type'} (f : type1514 A B K) (x' : K -> A) (i : K) : (term702 A B K f x' i) = (term703 A B K f x' i).
Proof. exact (MK_COMB (@lem4462644 A B K f i) (@lem4462645 A K x' i)). Qed.
Lemma lem4462648 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462649 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem4462648 A B f x). Qed.
Lemma lem4462650 {A B K : Type'} (f : type1514 A B K) (x' : K -> A) (i : K) : (term703 A B K f x' i) = (term704 A B K f x' i).
Proof. exact (@lem4462649 A B (@I (K -> A -> B) f i) (@I (K -> A) x' i)). Qed.
Lemma lem4462651 {A B K : Type'} (f : type1514 A B K) (x' : K -> A) (i : K) : (term702 A B K f x' i) = (term704 A B K f x' i).
Proof. exact (TRANS (@lem4462646 A B K f x' i) (@lem4462650 A B K f x' i)). Qed.
Lemma lem4462652 {A B K : Type'} (f : type1514 A B K) (x' : K -> A) (i : K) : (term433 A B K f x' i) = (term704 A B K f x' i).
Proof. exact (TRANS (@lem4462640 A B K f x' i) (@lem4462651 A B K f x' i)). Qed.
Lemma lem4462653 {B K : Type'} (x : K -> B) (i : K) : (term253 B K x i) = (term1161 B K x i).
Proof. exact (MK_COMB (@lem4462620 B) (@lem4462628 B K x i)). Qed.
Lemma lem4462654 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (i : K) : ((x i) = (term433 A B K f x' i)) = ((@I (K -> B) x i) = (term704 A B K f x' i)).
Proof. exact (MK_COMB (@lem4462653 B K x i) (@lem4462652 A B K f x' i)). Qed.
Lemma lem4462655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4462656 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (i : K) : (term1162 A B K x f x' i) = (term1163 A B K x f x' i).
Proof. exact (MK_COMB (@lem4462655) (@lem4462654 A B K x f x' i)). Qed.
Lemma lem4462657 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (i : K) : (term1164 A B K x f s x' i) = (term1165 A B K x f s x' i).
Proof. exact (MK_COMB (@lem4462656 A B K x f x' i) (@lem4462619 A K s x' i)). Qed.
Lemma lem4462658 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4462663 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4462664 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4462663 K Prop f x). Qed.
Lemma lem4462666 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4462664 K k i). Qed.
Lemma lem4462667 {K : Type'} (k : K -> Prop) (i : K) : (term590 K k i) = (term705 K k i).
Proof. exact (MK_COMB (@lem4462658) (@lem4462666 K k i)). Qed.
Lemma lem4462668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4462669 {K : Type'} (k : K -> Prop) (i : K) : (term706 K k i) = (term707 K k i).
Proof. exact (MK_COMB (@lem4462668) (@lem4462667 K k i)). Qed.
Lemma lem4462670 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (i : K) : (term1024 A B K k x f s x' i) = (term1166 A B K k x f s x' i).
Proof. exact (MK_COMB (@lem4462669 K k i) (@lem4462657 A B K x f s x' i)). Qed.
Lemma lem4462671 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) : (term1026 A B K k x f s x') = (term1167 A B K k x f s x').
Proof. exact (fun_ext (fun i : K => @lem4462670 A B K k x f s x' i)). Qed.
Lemma lem4462672 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4462673 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) : (term1028 A B K k x f s x') = (term1168 A B K k x f s x').
Proof. exact (MK_COMB (@lem4462672 K) (@lem4462671 A B K k x f s x')). Qed.
Lemma lem4462674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4462675 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) : (term1047 A B K k x f s x') = (term1169 A B K k x f s x').
Proof. exact (MK_COMB (@lem4462674) (@lem4462673 A B K k x f s x')). Qed.
Lemma lem4462676 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) : (term1049 A B K f s x' g k x) = (term1170 A B K f s x' g k x).
Proof. exact (MK_COMB (@lem4462675 A B K k x f s x') (@lem4462595 B K g k x)). Qed.
Lemma lem4462677 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term1170 A B K f s x' g k x.
Proof. exact (EQ_MP (@lem4462676 A B K f s x' g k x) (@lem4462433 A B K f s x' g k x h1)). Qed.
Lemma lem4462679 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term1168 A B K k x f s x'.
Proof. exact (proj1 (@lem4462677 A B K f s x' g k x h1)). Qed.
Lemma lem4462694 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : type803 A K) (x' : K -> A) : (term1157 A B K x f k s i x') = (term1171 A B K k x f s i x').
Proof. exact (@lem19490 (term763 A K k i x') (term1154 A B K k x f i x') (term1136 A K s i x')). Qed.
Lemma lem4462701 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : type803 A K) (x' : K -> A) : (term1172 A B K k x f s i x') = (term1173 A B K k x f s i x').
Proof. exact (@lem19699 (term763 A K k i x') (term1152 A B K x f i x') (term1136 A K s i x')). Qed.
Lemma lem4462708 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (i : type803 A K) (x' : K -> A) : (term1174 A B K x f k i x') = (term1175 A B K x f k i x').
Proof. exact (@lem19699 (term763 A K k i x') (term1152 A B K x f i x') (term763 A K k i x')). Qed.
Lemma lem4462709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4462710 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (i : type803 A K) (x' : K -> A) : (term1176 A B K x f k i x') = (term1177 A B K x f k i x').
Proof. exact (MK_COMB (@lem4462709) (@lem4462708 A B K x f k i x')). Qed.
Lemma lem4462711 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : type803 A K) (x' : K -> A) : (term1171 A B K k x f s i x') = (term1178 A B K k x f s i x').
Proof. exact (MK_COMB (@lem4462710 A B K x f k i x') (@lem4462701 A B K k x f s i x')). Qed.
Lemma lem4462713 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : type803 A K) (x' : K -> A) : (term1157 A B K x f k s i x') = (term1178 A B K k x f s i x').
Proof. exact (TRANS (@lem4462694 A B K k x f s i x') (@lem4462711 A B K k x f s i x')). Qed.
Lemma lem4462714 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : type803 A K) : (term1158 A B K x f k s i) = (term1179 A B K k x f s i).
Proof. exact (fun_ext (fun x' : K -> A => @lem4462713 A B K k x f s i x')). Qed.
Lemma lem4462715 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4462717 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : type803 A K) : (term1159 A B K x f k s i) = (term1180 A B K k x f s i).
Proof. exact (MK_COMB (@lem4462715 A K) (@lem4462714 A B K k x f s i)). Qed.
Lemma lem4462718 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term1180 A B K k x f s i.
Proof. exact (EQ_MP (@lem4462717 A B K k x f s i) (@lem4462574 A B K x f k s i h1)). Qed.
Lemma lem4462736 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) (i : K) : (term1166 A B K k x f s x' i) = (term1181 A B K x f k s x' i).
Proof. exact (@lem19490 ((@I (K -> B) x i) = (term704 A B K f x' i)) (term705 K k i) (term724 A K s x' i)). Qed.
Lemma lem4462737 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1167 A B K k x f s x') = (term1182 A B K x f k s x').
Proof. exact (fun_ext (fun i : K => @lem4462736 A B K x f k s x' i)). Qed.
Lemma lem4462738 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4462740 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) : (term1168 A B K k x f s x') = (term1183 A B K x f k s x').
Proof. exact (MK_COMB (@lem4462738 K) (@lem4462737 A B K x f k s x')). Qed.
Lemma lem4462741 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term1183 A B K x f k s x'.
Proof. exact (EQ_MP (@lem4462740 A B K x f k s x') (@lem4462679 A B K f s x' g k x h1)). Qed.
Lemma lem4462746 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term1184 A B K k x f s i _51614.
Proof. exact (@lem4462718 A B K x f k s i h1 _51614). Qed.
Lemma lem4462747 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : type803 A K) (_51614 : K -> A) : (term1184 A B K k x f s i _51614) = (term1178 A B K k x f s i _51614).
Proof. exact (eq_refl (term1184 A B K k x f s i _51614)). Qed.
Lemma lem4462748 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term1178 A B K k x f s i _51614.
Proof. exact (EQ_MP (@lem4462747 A B K k x f s i _51614) (@lem4462746 A B K _51614 x f k s i h1)). Qed.
Lemma lem4462749 {A B K : Type'} (_51615 : K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term1185 A B K x f k s x' _51615.
Proof. exact (@lem4462741 A B K f s x' g k x h1 _51615). Qed.
Lemma lem4462750 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x' : K -> A) (_51615 : K) : (term1185 A B K x f k s x' _51615) = (term1181 A B K x f k s x' _51615).
Proof. exact (eq_refl (term1185 A B K x f k s x' _51615)). Qed.
Lemma lem4462751 {A B K : Type'} (_51615 : K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term1181 A B K x f k s x' _51615.
Proof. exact (EQ_MP (@lem4462750 A B K x f k s x' _51615) (@lem4462749 A B K _51615 f s x' g k x h1)). Qed.
Lemma lem4462754 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term1173 A B K k x f s i _51614.
Proof. exact (proj2 (@lem4462748 A B K _51614 x f k s i h1)). Qed.
Lemma lem4462755 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term1175 A B K x f k i _51614.
Proof. exact (proj1 (@lem4462748 A B K _51614 x f k s i h1)). Qed.
Lemma lem4462825 {A B K : Type'} (_51615 : K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term1186 A B K k x f x' _51615.
Proof. exact (proj1 (@lem4462751 A B K _51615 f s x' g k x h1)). Qed.
Lemma lem4462839 {A B K : Type'} (_51615 : K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term725 A K k s x' _51615.
Proof. exact (proj2 (@lem4462751 A B K _51615 f s x' g k x h1)). Qed.
Lemma lem4462867 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term1187 A B K x f s i _51614.
Proof. exact (proj2 (@lem4462754 A B K _51614 x f k s i h1)). Qed.
Lemma lem4462881 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term837 A K k i _51614.
Proof. exact (proj1 (@lem4462755 A B K _51614 x f k s i h1)). Qed.
Lemma lem4463048 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x' : K -> A) (h1 : term1188 A K k i x') : term1188 A K k i x'.
Proof. exact (h1). Qed.
Lemma lem4463049 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x' : K -> A) (h1 : term1188 A K k i x') : term1189 A K k i x'.
Proof. exact (fun h0 : term763 A K k i x' => @lem4463048 A K k i x' h1). Qed.
Lemma lem4463051 (p : Prop) : (term842 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4463052 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x' : K -> A) : (term1189 A K k i x') = (term1188 A K k i x').
Proof. exact (@lem4463051 (term763 A K k i x')). Qed.
Lemma lem4463053 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x' : K -> A) (h1 : term1188 A K k i x') : term1188 A K k i x'.
Proof. exact (EQ_MP (@lem4463052 A K k i x') (@lem4463049 A K k i x' h1)). Qed.
Lemma lem4463055 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4463056 (x : Prop) : (x = x) = True.
Proof. exact (@lem4463055 Prop x). Qed.
Lemma lem4463057 {A K : Type'} (k : K -> Prop) (i : type803 A K) (_51614 : K -> A) : ((term837 A K k i _51614) = (term837 A K k i _51614)) = True.
Proof. exact (@lem4463056 (term837 A K k i _51614)). Qed.
Lemma lem4463058 {A K : Type'} (k : K -> Prop) (i : type803 A K) (_51614 : K -> A) : True = ((term837 A K k i _51614) = (term837 A K k i _51614)).
Proof. exact (SYM (@lem4463057 A K k i _51614)). Qed.
Lemma lem4463059 {A K : Type'} (k : K -> Prop) (i : type803 A K) (_51614 : K -> A) : (term837 A K k i _51614) = (term837 A K k i _51614).
Proof. exact (EQ_MP (@lem4463058 A K k i _51614) (@lem0)). Qed.
Lemma lem4463060 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term837 A K k i _51614.
Proof. exact (EQ_MP (@lem4463059 A K k i _51614) (@lem4462881 A B K _51614 x f k s i h1)). Qed.
Lemma lem4463062 (b : Prop) (a : Prop) : (a \/ b) = (term843 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4463065 {A K : Type'} (k : K -> Prop) (i : type803 A K) (_51614 : K -> A) : (term837 A K k i _51614) = (term844 A K k i _51614).
Proof. exact (@lem4463062 (term763 A K k i _51614) (term763 A K k i _51614)). Qed.
Lemma lem4463068 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term844 A K k i _51614.
Proof. exact (EQ_MP (@lem4463065 A K k i _51614) (@lem4463060 A B K _51614 x f k s i h1)). Qed.
Lemma lem4463069 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term844 A K k i _51614.
Proof. exact (@lem4463068 A B K _51614 x f k s i h1). Qed.
Lemma lem4463070 {A B K : Type'} (x' : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term844 A K k i x'.
Proof. exact (@lem4463069 A B K x' x f k s i h1). Qed.
Lemma lem4463073 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) (i : type803 A K) (x' : K -> A) (h1 : term1124 A B K x f k s i) (h2 : term1188 A K k i x') : term763 A K k i x'.
Proof. exact (@lem4463070 A B K x' x f k s i h1 (@lem4463053 A K k i x' h2)). Qed.
Lemma lem4463074 {A B K : Type'} (x' : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term844 A K k i x'.
Proof. exact (fun h0 : term1188 A K k i x' => @lem4463073 A B K x f s k i x' h1 h0). Qed.
Lemma lem4463076 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4463077 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x' : K -> A) : (term844 A K k i x') = (term763 A K k i x').
Proof. exact (@lem4463076 (term763 A K k i x')). Qed.
Lemma lem4463078 {A B K : Type'} (x' : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term763 A K k i x'.
Proof. exact (EQ_MP (@lem4463077 A K k i x') (@lem4463074 A B K x' x f k s i h1)). Qed.
Lemma lem4463084 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4463085 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : (term1186 A B K k x f x' _51615) = (term1190 A B K x f x' k _51615).
Proof. exact (@lem4463084 ((@I (K -> B) x _51615) = (term704 A B K f x' _51615)) (term705 K k _51615)). Qed.
Lemma lem4463093 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4463094 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : (term1191 A B K k x f x' _51615) = (term1192 A B K x f x' k _51615).
Proof. exact (MK_COMB (@lem4463093) (@lem4463085 A B K x f x' k _51615)). Qed.
Lemma lem4463102 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : (term1190 A B K x f x' k _51615) = (term1190 A B K x f x' k _51615).
Proof. exact (eq_refl (term1190 A B K x f x' k _51615)). Qed.
Lemma lem4463103 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : ((term1186 A B K k x f x' _51615) = (term1190 A B K x f x' k _51615)) = ((term1190 A B K x f x' k _51615) = (term1190 A B K x f x' k _51615)).
Proof. exact (MK_COMB (@lem4463094 A B K x f x' k _51615) (@lem4463102 A B K x f x' k _51615)). Qed.
Lemma lem4463105 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4463106 (x : Prop) : (x = x) = True.
Proof. exact (@lem4463105 Prop x). Qed.
Lemma lem4463107 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : ((term1190 A B K x f x' k _51615) = (term1190 A B K x f x' k _51615)) = True.
Proof. exact (@lem4463106 (term1190 A B K x f x' k _51615)). Qed.
Lemma lem4463108 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : ((term1186 A B K k x f x' _51615) = (term1190 A B K x f x' k _51615)) = True.
Proof. exact (TRANS (@lem4463103 A B K x f x' k _51615) (@lem4463107 A B K x f x' k _51615)). Qed.
Lemma lem4463109 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : True = ((term1186 A B K k x f x' _51615) = (term1190 A B K x f x' k _51615)).
Proof. exact (SYM (@lem4463108 A B K x f x' k _51615)). Qed.
Lemma lem4463110 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : (term1186 A B K k x f x' _51615) = (term1190 A B K x f x' k _51615).
Proof. exact (EQ_MP (@lem4463109 A B K x f x' k _51615) (@lem0)). Qed.
Lemma lem4463111 {A B K : Type'} (_51615 : K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term1190 A B K x f x' k _51615.
Proof. exact (EQ_MP (@lem4463110 A B K x f x' k _51615) (@lem4462825 A B K _51615 f s x' g k x h1)). Qed.
Lemma lem4463113 (b : Prop) (a : Prop) : (a \/ b) = (term843 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4463114 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (_51615 : K) : (term1190 A B K x f x' k _51615) = (term1193 A B K k x f x' _51615).
Proof. exact (@lem4463113 (term705 K k _51615) ((@I (K -> B) x _51615) = (term704 A B K f x' _51615))). Qed.
Lemma lem4463116 (a : Prop) : (term312 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4463117 {K : Type'} (k : K -> Prop) (_51615 : K) : (term851 K k _51615) = (@I (K -> Prop) k _51615).
Proof. exact (@lem4463116 (@I (K -> Prop) k _51615)). Qed.
Lemma lem4463118 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4463119 {K : Type'} (k : K -> Prop) (_51615 : K) : (term852 K k _51615) = (term853 K k _51615).
Proof. exact (MK_COMB (@lem4463118) (@lem4463117 K k _51615)). Qed.
Lemma lem4463120 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (x' : K -> A) (_51615 : K) : ((@I (K -> B) x _51615) = (term704 A B K f x' _51615)) = ((@I (K -> B) x _51615) = (term704 A B K f x' _51615)).
Proof. exact (eq_refl ((@I (K -> B) x _51615) = (term704 A B K f x' _51615))). Qed.
Lemma lem4463121 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (_51615 : K) : (term1193 A B K k x f x' _51615) = (term1194 A B K k x f x' _51615).
Proof. exact (MK_COMB (@lem4463119 K k _51615) (@lem4463120 A B K x f x' _51615)). Qed.
Lemma lem4463122 {A B K : Type'} (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (x' : K -> A) (_51615 : K) : (term1190 A B K x f x' k _51615) = (term1194 A B K k x f x' _51615).
Proof. exact (TRANS (@lem4463114 A B K k x f x' _51615) (@lem4463121 A B K k x f x' _51615)). Qed.
Lemma lem4463125 {A B K : Type'} (_51615 : K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term1194 A B K k x f x' _51615.
Proof. exact (EQ_MP (@lem4463122 A B K k x f x' _51615) (@lem4463111 A B K _51615 f s x' g k x h1)). Qed.
Lemma lem4463126 {A B K : Type'} (_51615 : K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term1194 A B K k x f x' _51615.
Proof. exact (@lem4463125 A B K _51615 f s x' g k x h1). Qed.
Lemma lem4463127 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term1195 A B K k x f i x'.
Proof. exact (@lem4463126 A B K (@I ((K -> A) -> K) i x') f s x' g k x h1). Qed.
Lemma lem4463130 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1124 A B K x f k s i) (h2 : term1049 A B K f s x' g k x) : (term1141 A B K x i x') = (term1148 A B K f i x').
Proof. exact (@lem4463127 A B K i f s x' g k x h2 (@lem4463078 A B K x' x f k s i h1)). Qed.
Lemma lem4463131 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1124 A B K x f k s i) (h2 : term1049 A B K f s x' g k x) : term1196 A B K x f i x'.
Proof. exact (fun h0 : term1152 A B K x f i x' => @lem4463130 A B K i f s x' g k x h1 h2). Qed.
Lemma lem4463133 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4463134 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (i : type803 A K) (x' : K -> A) : (term1196 A B K x f i x') = ((term1141 A B K x i x') = (term1148 A B K f i x')).
Proof. exact (@lem4463133 ((term1141 A B K x i x') = (term1148 A B K f i x'))). Qed.
Lemma lem4463135 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1124 A B K x f k s i) (h2 : term1049 A B K f s x' g k x) : (term1141 A B K x i x') = (term1148 A B K f i x').
Proof. exact (EQ_MP (@lem4463134 A B K x f i x') (@lem4463131 A B K i f s x' g k x h1 h2)). Qed.
Lemma lem4463138 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x' : K -> A) (h1 : term1188 A K k i x') : term1188 A K k i x'.
Proof. exact (h1). Qed.
Lemma lem4463139 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x' : K -> A) (h1 : term1188 A K k i x') : term1189 A K k i x'.
Proof. exact (fun h0 : term763 A K k i x' => @lem4463138 A K k i x' h1). Qed.
Lemma lem4463141 (p : Prop) : (term842 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4463142 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x' : K -> A) : (term1189 A K k i x') = (term1188 A K k i x').
Proof. exact (@lem4463141 (term763 A K k i x')). Qed.
Lemma lem4463143 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x' : K -> A) (h1 : term1188 A K k i x') : term1188 A K k i x'.
Proof. exact (EQ_MP (@lem4463142 A K k i x') (@lem4463139 A K k i x' h1)). Qed.
Lemma lem4463145 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term844 A K k i _51614.
Proof. exact (EQ_MP (@lem4463065 A K k i _51614) (@lem4463060 A B K _51614 x f k s i h1)). Qed.
Lemma lem4463146 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term844 A K k i _51614.
Proof. exact (@lem4463145 A B K _51614 x f k s i h1). Qed.
Lemma lem4463147 {A B K : Type'} (x' : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term844 A K k i x'.
Proof. exact (@lem4463146 A B K x' x f k s i h1). Qed.
Lemma lem4463150 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) (i : type803 A K) (x' : K -> A) (h1 : term1124 A B K x f k s i) (h2 : term1188 A K k i x') : term763 A K k i x'.
Proof. exact (@lem4463147 A B K x' x f k s i h1 (@lem4463143 A K k i x' h2)). Qed.
Lemma lem4463151 {A B K : Type'} (x' : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term844 A K k i x'.
Proof. exact (fun h0 : term1188 A K k i x' => @lem4463150 A B K x f s k i x' h1 h0). Qed.
Lemma lem4463153 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4463154 {A K : Type'} (k : K -> Prop) (i : type803 A K) (x' : K -> A) : (term844 A K k i x') = (term763 A K k i x').
Proof. exact (@lem4463153 (term763 A K k i x')). Qed.
Lemma lem4463155 {A B K : Type'} (x' : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term763 A K k i x'.
Proof. exact (EQ_MP (@lem4463154 A K k i x') (@lem4463151 A B K x' x f k s i h1)). Qed.
Lemma lem4463161 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4463162 {A K : Type'} (s : type1470 A K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : (term725 A K k s x' _51615) = (term891 A K s x' k _51615).
Proof. exact (@lem4463161 (term724 A K s x' _51615) (term705 K k _51615)). Qed.
Lemma lem4463168 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4463169 {A K : Type'} (s : type1470 A K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : (term892 A K k s x' _51615) = (term893 A K s x' k _51615).
Proof. exact (MK_COMB (@lem4463168) (@lem4463162 A K s x' k _51615)). Qed.
Lemma lem4463175 {A K : Type'} (s : type1470 A K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : (term891 A K s x' k _51615) = (term891 A K s x' k _51615).
Proof. exact (eq_refl (term891 A K s x' k _51615)). Qed.
Lemma lem4463176 {A K : Type'} (s : type1470 A K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : ((term725 A K k s x' _51615) = (term891 A K s x' k _51615)) = ((term891 A K s x' k _51615) = (term891 A K s x' k _51615)).
Proof. exact (MK_COMB (@lem4463169 A K s x' k _51615) (@lem4463175 A K s x' k _51615)). Qed.
Lemma lem4463178 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4463179 (x : Prop) : (x = x) = True.
Proof. exact (@lem4463178 Prop x). Qed.
Lemma lem4463180 {A K : Type'} (s : type1470 A K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : ((term891 A K s x' k _51615) = (term891 A K s x' k _51615)) = True.
Proof. exact (@lem4463179 (term891 A K s x' k _51615)). Qed.
Lemma lem4463181 {A K : Type'} (s : type1470 A K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : ((term725 A K k s x' _51615) = (term891 A K s x' k _51615)) = True.
Proof. exact (TRANS (@lem4463176 A K s x' k _51615) (@lem4463180 A K s x' k _51615)). Qed.
Lemma lem4463182 {A K : Type'} (s : type1470 A K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : True = ((term725 A K k s x' _51615) = (term891 A K s x' k _51615)).
Proof. exact (SYM (@lem4463181 A K s x' k _51615)). Qed.
Lemma lem4463183 {A K : Type'} (s : type1470 A K) (x' : K -> A) (k : K -> Prop) (_51615 : K) : (term725 A K k s x' _51615) = (term891 A K s x' k _51615).
Proof. exact (EQ_MP (@lem4463182 A K s x' k _51615) (@lem0)). Qed.
Lemma lem4463184 {A B K : Type'} (_51615 : K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term891 A K s x' k _51615.
Proof. exact (EQ_MP (@lem4463183 A K s x' k _51615) (@lem4462839 A B K _51615 f s x' g k x h1)). Qed.
Lemma lem4463186 (b : Prop) (a : Prop) : (a \/ b) = (term843 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4463187 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x' : K -> A) (_51615 : K) : (term891 A K s x' k _51615) = (term894 A K k s x' _51615).
Proof. exact (@lem4463186 (term705 K k _51615) (term724 A K s x' _51615)). Qed.
Lemma lem4463189 (a : Prop) : (term312 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4463190 {K : Type'} (k : K -> Prop) (_51615 : K) : (term851 K k _51615) = (@I (K -> Prop) k _51615).
Proof. exact (@lem4463189 (@I (K -> Prop) k _51615)). Qed.
Lemma lem4463191 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4463192 {K : Type'} (k : K -> Prop) (_51615 : K) : (term852 K k _51615) = (term853 K k _51615).
Proof. exact (MK_COMB (@lem4463191) (@lem4463190 K k _51615)). Qed.
Lemma lem4463193 {A K : Type'} (s : type1470 A K) (x' : K -> A) (_51615 : K) : (term724 A K s x' _51615) = (term724 A K s x' _51615).
Proof. exact (eq_refl (term724 A K s x' _51615)). Qed.
Lemma lem4463194 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x' : K -> A) (_51615 : K) : (term894 A K k s x' _51615) = (term895 A K k s x' _51615).
Proof. exact (MK_COMB (@lem4463192 K k _51615) (@lem4463193 A K s x' _51615)). Qed.
Lemma lem4463195 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x' : K -> A) (_51615 : K) : (term891 A K s x' k _51615) = (term895 A K k s x' _51615).
Proof. exact (TRANS (@lem4463187 A K k s x' _51615) (@lem4463194 A K k s x' _51615)). Qed.
Lemma lem4463198 {A B K : Type'} (_51615 : K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term895 A K k s x' _51615.
Proof. exact (EQ_MP (@lem4463195 A K k s x' _51615) (@lem4463184 A B K _51615 f s x' g k x h1)). Qed.
Lemma lem4463199 {A B K : Type'} (_51615 : K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term895 A K k s x' _51615.
Proof. exact (@lem4463198 A B K _51615 f s x' g k x h1). Qed.
Lemma lem4463200 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1049 A B K f s x' g k x) : term1197 A K k s i x'.
Proof. exact (@lem4463199 A B K (@I ((K -> A) -> K) i x') f s x' g k x h1). Qed.
Lemma lem4463203 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1124 A B K x f k s i) (h2 : term1049 A B K f s x' g k x) : term1134 A K s i x'.
Proof. exact (@lem4463200 A B K i f s x' g k x h2 (@lem4463155 A B K x' x f k s i h1)). Qed.
Lemma lem4463204 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1124 A B K x f k s i) (h2 : term1049 A B K f s x' g k x) : term1198 A K s i x'.
Proof. exact (fun h0 : term1136 A K s i x' => @lem4463203 A B K i f s x' g k x h1 h2). Qed.
Lemma lem4463206 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4463207 {A K : Type'} (s : type1470 A K) (i : type803 A K) (x' : K -> A) : (term1198 A K s i x') = (term1134 A K s i x').
Proof. exact (@lem4463206 (term1134 A K s i x')). Qed.
Lemma lem4463208 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1124 A B K x f k s i) (h2 : term1049 A B K f s x' g k x) : term1134 A K s i x'.
Proof. exact (EQ_MP (@lem4463207 A K s i x') (@lem4463204 A B K i f s x' g k x h1 h2)). Qed.
Lemma lem4463210 (a : Prop) (b : Prop) : (term900 a b) = (term901 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4463211 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : type803 A K) (_51614 : K -> A) : (term1187 A B K x f s i _51614) = (term1199 A B K x f s i _51614).
Proof. exact (@lem4463210 ((term1141 A B K x i _51614) = (term1148 A B K f i _51614)) (term1134 A K s i _51614)). Qed.
Lemma lem4463213 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4463214 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : type803 A K) (_51614 : K -> A) : (term1199 A B K x f s i _51614) = (term1200 A B K x f s i _51614).
Proof. exact (@lem4463213 (term1201 A B K x f s i _51614)). Qed.
Lemma lem4463215 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (i : type803 A K) (_51614 : K -> A) : (term1187 A B K x f s i _51614) = (term1200 A B K x f s i _51614).
Proof. exact (TRANS (@lem4463211 A B K x f s i _51614) (@lem4463214 A B K x f s i _51614)). Qed.
Lemma lem4463217 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1124 A B K x f k s i) (h2 : term1049 A B K f s x' g k x) : term1201 A B K x f s i x'.
Proof. exact (conj (@lem4463135 A B K i f s x' g k x h1 h2) (@lem4463208 A B K i f s x' g k x h1 h2)). Qed.
Lemma lem4463219 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term1200 A B K x f s i _51614.
Proof. exact (EQ_MP (@lem4463215 A B K x f s i _51614) (@lem4462867 A B K _51614 x f k s i h1)). Qed.
Lemma lem4463220 {A B K : Type'} (_51614 : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term1200 A B K x f s i _51614.
Proof. exact (@lem4463219 A B K _51614 x f k s i h1). Qed.
Lemma lem4463221 {A B K : Type'} (x' : K -> A) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (i : type803 A K) (h1 : term1124 A B K x f k s i) : term1200 A B K x f s i x'.
Proof. exact (@lem4463220 A B K x' x f k s i h1). Qed.
Lemma lem4463224 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1124 A B K x f k s i) (h2 : term1049 A B K f s x' g k x) : False.
Proof. exact (@lem4463221 A B K x' x f k s i h1 (@lem4463217 A B K i f s x' g k x h1 h2)). Qed.
Lemma lem4463225 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1124 A B K x f k s i) (h2 : term1049 A B K f s x' g k x) : term913.
Proof. exact (fun h0 : ~ False => @lem4463224 A B K i f s x' g k x h1 h2). Qed.
Lemma lem4463227 (p : Prop) : (term846 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4463228 : term913 = False.
Proof. exact (@lem4463227 False). Qed.
Lemma lem4463230 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (x' : K -> A) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1124 A B K x f k s i) (h2 : term1049 A B K f s x' g k x) : False.
Proof. exact (EQ_MP (@lem4463228) (@lem4463225 A B K i f s x' g k x h1 h2)). Qed.
Lemma lem4463231 {A B K : Type'} (i : type803 A K) (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term1124 A B K x f k s i) (h2 : term922 A B K f s g k x) : False.
Proof. exact (ex_elim (@lem4462197 A B K f s g k x h2) (fun x' : K -> A => fun h0 : term1051 A B K f s g k x x' => @lem4463230 A B K i f s x' g k x h1 h0)). Qed.
Lemma lem4463232 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term988 A B K x f k s) (h2 : term922 A B K f s g k x) : False.
Proof. exact (ex_elim (@lem4462431 A B K x f k s h1) (fun i : type803 A K => fun h0 : term1126 A B K x f k s i => @lem4463231 A B K i f s g k x h0 h2)). Qed.
Lemma lem4463233 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term988 A B K x f k s) (h2 : term922 A B K f s g k x) : (term988 A B K x f k s) = False.
Proof. exact (prop_ext (fun h3 : term988 A B K x f k s => @lem4463232 A B K f s g k x h1 h2) (fun h3 : False => @lem4461993 A B K x f k s h1)). Qed.
Lemma lem4463234 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term988 A B K x f k s) (h2 : term922 A B K f s g k x) : False.
Proof. exact (EQ_MP (@lem4463233 A B K f s g k x h1 h2) (@lem4461993 A B K x f k s h1)). Qed.
Lemma lem4463235 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term922 A B K f s g k x) : term987 A B K x f k s.
Proof. exact (fun h0 : term988 A B K x f k s => @lem4463234 A B K f s g k x h0 h1). Qed.
Lemma lem4463236 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term922 A B K f s g k x) : term975 A B K x f k s.
Proof. exact (EQ_MP (@lem4461992 A B K x f k s) (@lem4463235 A B K f s g k x h1)). Qed.
Lemma lem4463237 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term976 A B K g x f k s.
Proof. exact (fun h0 : term922 A B K f s g k x => @lem4463236 A B K f s g k x h0). Qed.
Lemma lem4463242 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term978 A B K x f k s.
Proof. exact (fun g : K -> B => @lem4463237 A B K g x f k s). Qed.
Lemma lem4463247 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term980 A B K f k s.
Proof. exact (fun x : K -> B => @lem4463242 A B K x f k s). Qed.
Lemma lem4463252 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) : term982 A B K k s.
Proof. exact (fun f : type1514 A B K => @lem4463247 A B K f k s). Qed.
Lemma lem4463257 {A B K : Type'} (s : type1470 A K) : term984 A B K s.
Proof. exact (fun k : K -> Prop => @lem4463252 A B K k s). Qed.
Lemma lem4463262 {A B K : Type'} : term986 A B K.
Proof. exact (fun s : type1470 A K => @lem4463257 A B K s). Qed.
Lemma lem4463263 {A B K : Type'} : term958 A B K.
Proof. exact (EQ_MP (@lem4461987 A B K) (@lem4463262 A B K)). Qed.
Lemma lem4463264 {A B K : Type'} (s : type1470 A K) : term1202 A B K s.
Proof. exact (@lem4463263 A B K s). Qed.
Lemma lem4463265 {A B K : Type'} (s : type1470 A K) : (term1202 A B K s) = (term954 A B K s).
Proof. exact (eq_refl (term1202 A B K s)). Qed.
Lemma lem4463266 {A B K : Type'} (s : type1470 A K) : term954 A B K s.
Proof. exact (EQ_MP (@lem4463265 A B K s) (@lem4463264 A B K s)). Qed.
Lemma lem4463267 {A B K : Type'} (s : type1470 A K) (k : K -> Prop) : term1203 A B K s k.
Proof. exact (@lem4463266 A B K s k). Qed.
Lemma lem4463268 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) : (term1203 A B K s k) = (term950 A B K k s).
Proof. exact (eq_refl (term1203 A B K s k)). Qed.
Lemma lem4463269 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) : term950 A B K k s.
Proof. exact (EQ_MP (@lem4463268 A B K k s) (@lem4463267 A B K s k)). Qed.
Lemma lem4463270 {A B K : Type'} (k : K -> Prop) (s : type1470 A K) (f : type1514 A B K) : term1204 A B K k s f.
Proof. exact (@lem4463269 A B K k s f). Qed.
Lemma lem4463271 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1204 A B K k s f) = (term946 A B K f k s).
Proof. exact (eq_refl (term1204 A B K k s f)). Qed.
Lemma lem4463272 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term946 A B K f k s.
Proof. exact (EQ_MP (@lem4463271 A B K f k s) (@lem4463270 A B K k s f)). Qed.
Lemma lem4463273 {A B K : Type'} (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (x : K -> B) : term1205 A B K f k s x.
Proof. exact (@lem4463272 A B K f k s x). Qed.
Lemma lem4463274 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1205 A B K f k s x) = (term942 A B K x f k s).
Proof. exact (eq_refl (term1205 A B K f k s x)). Qed.
Lemma lem4463275 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term942 A B K x f k s.
Proof. exact (EQ_MP (@lem4463274 A B K x f k s) (@lem4463273 A B K f k s x)). Qed.
Lemma lem4463276 {A B K : Type'} (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (g : K -> B) : term1206 A B K x f k s g.
Proof. exact (@lem4463275 A B K x f k s g). Qed.
Lemma lem4463277 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : (term1206 A B K x f k s g) = (term934 A B K g x f k s).
Proof. exact (eq_refl (term1206 A B K x f k s g)). Qed.
Lemma lem4463278 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term934 A B K g x f k s.
Proof. exact (EQ_MP (@lem4463277 A B K g x f k s) (@lem4463276 A B K x f k s g)). Qed.
Lemma lem4463280 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term934 A B K g x f k s.
Proof. exact (@lem4461576 A B K g x f k s (@lem4463278 A B K g x f k s)). Qed.
Lemma lem4463281 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term935 A B K g x f k s) : False.
Proof. exact (@lem4463280 A B K g x f k s (@lem4461560 A B K g x f k s h1)). Qed.
Lemma lem4463282 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term935 A B K g x f k s) : (term935 A B K g x f k s) = False.
Proof. exact (prop_ext (fun h2 : term935 A B K g x f k s => @lem4463281 A B K g x f k s h1) (fun h2 : False => @lem4461560 A B K g x f k s h1)). Qed.
Lemma lem4463283 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term935 A B K g x f k s) : False.
Proof. exact (EQ_MP (@lem4463282 A B K g x f k s h1) (@lem4461560 A B K g x f k s h1)). Qed.
Lemma lem4463284 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term934 A B K g x f k s.
Proof. exact (fun h0 : term935 A B K g x f k s => @lem4463283 A B K g x f k s h0). Qed.
Lemma lem4463285 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term933 A B K g x f k s.
Proof. exact (EQ_MP (@lem4461559 A B K g x f k s) (@lem4463284 A B K g x f k s)). Qed.
Lemma lem4463287 {A B K : Type'} (g : K -> B) (x : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term932 A B K g x f k s.
Proof. exact (EQ_MP (@lem4461555 A B K g x f k s) (@lem4463285 A B K g x f k s)). Qed.
Lemma lem4463288 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term220 A B K k x f s) (h2 : g = (@RESTRICTION K B k x)) : term262 A B K x f k s.
Proof. exact (@lem4463287 A B K g x f k s (@lem4461360 A B K f s g k x h1 h2)). Qed.
Lemma lem4463289 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term220 A B K k x f s) (h2 : g = (@RESTRICTION K B k x)) : term204 A B K g f k s.
Proof. exact (EQ_MP (@lem4457981 A B K f s g k x h2) (@lem4463288 A B K f s g k x h1 h2)). Qed.
Lemma lem4463290 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term100 A K k x s) (h2 : g = (term192 A B K f k x)) : term225 A B K g k f s.
Proof. exact (EQ_MP (@lem4457891 A B K s g f k x h2) (@lem4461349 A B K s g f k x h1 h2)). Qed.
Lemma lem4463291 {A B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (h1 : term222 A B K g k x f s) : term220 A B K k x f s.
Proof. exact (proj2 (@lem4457789 A B K g k x f s h1)). Qed.
Lemma lem4463292 {A B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (h1 : term222 A B K g k x f s) : g = (@RESTRICTION K B k x).
Proof. exact (proj1 (@lem4457789 A B K g k x f s h1)). Qed.
Lemma lem4463293 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term220 A B K k x f s) (h2 : g = (@RESTRICTION K B k x)) : (term220 A B K k x f s) = (term204 A B K g f k s).
Proof. exact (prop_ext (fun h3 : term220 A B K k x f s => @lem4463289 A B K f s g k x h1 h2) (fun h3 : term204 A B K g f k s => @lem4457790 A B K k x f s h1)). Qed.
Lemma lem4463294 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term220 A B K k x f s) (h2 : g = (@RESTRICTION K B k x)) : term204 A B K g f k s.
Proof. exact (EQ_MP (@lem4463293 A B K f s g k x h1 h2) (@lem4457790 A B K k x f s h1)). Qed.
Lemma lem4463295 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term220 A B K k x f s) (h2 : g = (@RESTRICTION K B k x)) : (g = (@RESTRICTION K B k x)) = (term204 A B K g f k s).
Proof. exact (prop_ext (fun h3 : g = (@RESTRICTION K B k x) => @lem4463294 A B K f s g k x h1 h2) (fun h3 : term204 A B K g f k s => @lem4457791 B K g k x h2)). Qed.
Lemma lem4463296 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term220 A B K k x f s) (h2 : g = (@RESTRICTION K B k x)) : term204 A B K g f k s.
Proof. exact (EQ_MP (@lem4463295 A B K f s g k x h1 h2) (@lem4457791 B K g k x h2)). Qed.
Lemma lem4463297 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term222 A B K g k x f s) (h2 : g = (@RESTRICTION K B k x)) : (term220 A B K k x f s) = (term204 A B K g f k s).
Proof. exact (prop_ext (fun h3 : term220 A B K k x f s => @lem4463296 A B K f s g k x h3 h2) (fun h3 : term204 A B K g f k s => @lem4463291 A B K g k x f s h1)). Qed.
Lemma lem4463298 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (g : K -> B) (k : K -> Prop) (x : K -> B) (h1 : term222 A B K g k x f s) (h2 : g = (@RESTRICTION K B k x)) : term204 A B K g f k s.
Proof. exact (EQ_MP (@lem4463297 A B K f s g k x h1 h2) (@lem4463291 A B K g k x f s h1)). Qed.
Lemma lem4463299 {A B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (h1 : term222 A B K g k x f s) : (g = (@RESTRICTION K B k x)) = (term204 A B K g f k s).
Proof. exact (prop_ext (fun h2 : g = (@RESTRICTION K B k x) => @lem4463298 A B K f s g k x h1 h2) (fun h2 : term204 A B K g f k s => @lem4463292 A B K g k x f s h1)). Qed.
Lemma lem4463300 {A B K : Type'} (g : K -> B) (k : K -> Prop) (x : K -> B) (f : type1514 A B K) (s : type1470 A K) (h1 : term222 A B K g k x f s) : term204 A B K g f k s.
Proof. exact (EQ_MP (@lem4463299 A B K g k x f s h1) (@lem4463292 A B K g k x f s h1)). Qed.
Lemma lem4463301 {A B K : Type'} (g : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) (h1 : term225 A B K g k f s) : term204 A B K g f k s.
Proof. exact (ex_elim (@lem4457788 A B K g k f s h1) (fun x : K -> B => fun h0 : term224 A B K g k f s x => @lem4463300 A B K g k x f s h0)). Qed.
Lemma lem4463302 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term1207 A B K g f k s.
Proof. exact (fun h0 : term225 A B K g k f s => @lem4463301 A B K g k f s h0). Qed.
Lemma lem4463303 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term201 A B K g f k x s) : term100 A K k x s.
Proof. exact (proj2 (@lem4457785 A B K g f k x s h1)). Qed.
Lemma lem4463304 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term201 A B K g f k x s) : g = (term192 A B K f k x).
Proof. exact (proj1 (@lem4457785 A B K g f k x s h1)). Qed.
Lemma lem4463305 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term100 A K k x s) (h2 : g = (term192 A B K f k x)) : (term100 A K k x s) = (term225 A B K g k f s).
Proof. exact (prop_ext (fun h3 : term100 A K k x s => @lem4463290 A B K s g f k x h1 h2) (fun h3 : term225 A B K g k f s => @lem4457786 A K k x s h1)). Qed.
Lemma lem4463306 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term100 A K k x s) (h2 : g = (term192 A B K f k x)) : term225 A B K g k f s.
Proof. exact (EQ_MP (@lem4463305 A B K s g f k x h1 h2) (@lem4457786 A K k x s h1)). Qed.
Lemma lem4463307 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term100 A K k x s) (h2 : g = (term192 A B K f k x)) : (g = (term192 A B K f k x)) = (term225 A B K g k f s).
Proof. exact (prop_ext (fun h3 : g = (term192 A B K f k x) => @lem4463306 A B K s g f k x h1 h2) (fun h3 : term225 A B K g k f s => @lem4457787 A B K g f k x h2)). Qed.
Lemma lem4463308 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term100 A K k x s) (h2 : g = (term192 A B K f k x)) : term225 A B K g k f s.
Proof. exact (EQ_MP (@lem4463307 A B K s g f k x h1 h2) (@lem4457787 A B K g f k x h2)). Qed.
Lemma lem4463309 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term201 A B K g f k x s) (h2 : g = (term192 A B K f k x)) : (term100 A K k x s) = (term225 A B K g k f s).
Proof. exact (prop_ext (fun h3 : term100 A K k x s => @lem4463308 A B K s g f k x h3 h2) (fun h3 : term225 A B K g k f s => @lem4463303 A B K g f k x s h1)). Qed.
Lemma lem4463310 {A B K : Type'} (s : type1470 A K) (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (h1 : term201 A B K g f k x s) (h2 : g = (term192 A B K f k x)) : term225 A B K g k f s.
Proof. exact (EQ_MP (@lem4463309 A B K s g f k x h1 h2) (@lem4463303 A B K g f k x s h1)). Qed.
Lemma lem4463311 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term201 A B K g f k x s) : (g = (term192 A B K f k x)) = (term225 A B K g k f s).
Proof. exact (prop_ext (fun h2 : g = (term192 A B K f k x) => @lem4463310 A B K s g f k x h1 h2) (fun h2 : term225 A B K g k f s => @lem4463304 A B K g f k x s h1)). Qed.
Lemma lem4463312 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (x : K -> A) (s : type1470 A K) (h1 : term201 A B K g f k x s) : term225 A B K g k f s.
Proof. exact (EQ_MP (@lem4463311 A B K g f k x s h1) (@lem4463304 A B K g f k x s h1)). Qed.
Lemma lem4463313 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) (h1 : term204 A B K g f k s) : term225 A B K g k f s.
Proof. exact (ex_elim (@lem4457784 A B K g f k s h1) (fun x : K -> A => fun h0 : term203 A B K g f k s x => @lem4463312 A B K g f k x s h0)). Qed.
Lemma lem4463314 {A B K : Type'} (g : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term1208 A B K g k f s.
Proof. exact (fun h0 : term204 A B K g f k s => @lem4463313 A B K g f k s h0). Qed.
Lemma lem4463315 {A B K : Type'} (g : K -> B) (f : type1514 A B K) (k : K -> Prop) (s : type1470 A K) : term1209 A B K g f k s.
Proof. exact (conj (@lem4463314 A B K g k f s) (@lem4463302 A B K g f k s)). Qed.
Lemma lem4463316 {A B K : Type'} (g : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term1209 A B K g f k s) = ((term204 A B K g f k s) = (term225 A B K g k f s)).
Proof. exact (@lem32 (term204 A B K g f k s) (term225 A B K g k f s)). Qed.
Lemma lem4463317 {A B K : Type'} (g : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term204 A B K g f k s) = (term225 A B K g k f s).
Proof. exact (EQ_MP (@lem4463316 A B K g k f s) (@lem4463315 A B K g f k s)). Qed.
Lemma lem4463318 {A B K : Type'} (g : K -> B) (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term180 A B K g f k s) = (term209 A B K g k f s).
Proof. exact (EQ_MP (@lem4457783 A B K g k f s) (@lem4463317 A B K g k f s)). Qed.
Lemma lem4463323 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : term177 A B K k f s.
Proof. exact (fun g : K -> B => @lem4463318 A B K g k f s). Qed.
Lemma lem4463324 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term174 A B K f k s) = (term149 A B K k f s).
Proof. exact (EQ_MP (@lem4457601 A B K k f s) (@lem4463323 A B K k f s)). Qed.
Lemma lem4463325 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term126 A B K f k s) = (term149 A B K k f s).
Proof. exact (EQ_MP (@lem4457596 A B K k f s) (@lem4463324 A B K k f s)). Qed.
Lemma lem4463326 {A B K : Type'} (f : type1514 A B K) (s : type1470 A K) (k : K -> Prop) : (term58 A B K f s k) = (term92 A B K f s k).
Proof. exact (EQ_MP (@lem4457521 A B K f s k) (@lem4463325 A B K k f s)). Qed.
Lemma lem4463327 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) (s : type1470 A K) : (term57 A B K f k s) = (term61 A B K k f s).
Proof. exact (EQ_MP (@lem4457449 A B K k f s) (@lem4463326 A B K f s k)). Qed.
Lemma lem4463332 {A B K : Type'} (k : K -> Prop) (f : type1514 A B K) : term1210 A B K k f.
Proof. exact (fun s : type1470 A K => @lem4463327 A B K k f s). Qed.
Lemma lem4463337 {A B K : Type'} (f : type1514 A B K) : term1211 A B K f.
Proof. exact (fun k : K -> Prop => @lem4463332 A B K k f). Qed.
Lemma lem4463342 {A B K : Type'} : term1212 A B K.
Proof. exact (fun f : type1514 A B K => @lem4463337 A B K f). Qed.
