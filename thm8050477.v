Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8050477_term_abbrevs.
Require Import EXTENSION_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8050203 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term0 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8050204 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term0 _141927 _141928 _141929 s) = (term1 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term0 _141927 _141928 _141929 s)). Qed.
Lemma lem8050205 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term1 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8050204 _141927 _141928 _141929 s) (@lem8050203 _141927 _141928 _141929 s)). Qed.
Lemma lem8050206 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term2 _141927 _141928 _141929 s t.
Proof. exact (@lem8050205 _141927 _141928 _141929 s t). Qed.
Lemma lem8050207 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term2 _141927 _141928 _141929 s t) = (term3 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term2 _141927 _141928 _141929 s t)). Qed.
Lemma lem8050208 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term3 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8050207 _141927 _141928 _141929 s t) (@lem8050206 _141927 _141928 _141929 s t)). Qed.
Lemma lem8050209 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term4 _141927 _141928 _141929 s t x.
Proof. exact (@lem8050208 _141927 _141928 _141929 s t x). Qed.
Lemma lem8050210 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term4 _141927 _141928 _141929 s t x) = (term5 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term4 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8050211 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term5 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8050210 _141927 _141928 _141929 x s t) (@lem8050209 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8050212 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term6 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8050211 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8050213 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term6 _141927 _141928 _141929 x s t y) = ((term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term6 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8050239 {_83095 : Type'} : term9 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem8050240 {_83095 : Type'} (p : _83095 -> Prop) : term10 _83095 p.
Proof. exact (@lem8050239 _83095 p). Qed.
Lemma lem8050241 {_83095 : Type'} (p : _83095 -> Prop) : (term10 _83095 p) = (term11 _83095 p).
Proof. exact (eq_refl (term10 _83095 p)). Qed.
Lemma lem8050242 {_83095 : Type'} (p : _83095 -> Prop) : term11 _83095 p.
Proof. exact (EQ_MP (@lem8050241 _83095 p) (@lem8050240 _83095 p)). Qed.
Lemma lem8050243 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term12 _83095 p x.
Proof. exact (@lem8050242 _83095 p x). Qed.
Lemma lem8050244 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 p x) = ((term13 _83095 x p) = (p x)).
Proof. exact (eq_refl (term12 _83095 p x)). Qed.
Lemma lem8050253 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8050254 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem8050255 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem8050254 A s) (@lem8050253 A s)). Qed.
Lemma lem8050256 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem8050255 A s t). Qed.
Lemma lem8050257 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem8050274 {_89711 _89725 : Type'} : term18 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem8050275 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term19 _89711 _89725 P.
Proof. exact (@lem8050274 _89711 _89725 P). Qed.
Lemma lem8050276 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term19 _89711 _89725 P) = (term20 _89711 _89725 P).
Proof. exact (eq_refl (term19 _89711 _89725 P)). Qed.
Lemma lem8050277 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term20 _89711 _89725 P.
Proof. exact (EQ_MP (@lem8050276 _89711 _89725 P) (@lem8050275 _89711 _89725 P)). Qed.
Lemma lem8050278 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term21 _89711 _89725 P f.
Proof. exact (@lem8050277 _89711 _89725 P f). Qed.
Lemma lem8050279 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term21 _89711 _89725 P f) = ((term22 _89711 _89725 P f) = (term23 _89711 _89725 P f)).
Proof. exact (eq_refl (term21 _89711 _89725 P f)). Qed.
Lemma lem8050297 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem8050257 A s t) (@lem8050256 A s t)). Qed.
Lemma lem8050298 {_143007 _143008 _143009 : Type'} (s : type16 _143007 _143008 _143009) (t : type16 _143007 _143008 _143009) : (s = t) = (term24 _143007 _143008 _143009 s t).
Proof. exact (@lem8050297 (type2 _143007 _143008 _143009) s t). Qed.
Lemma lem8050299 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : ((term25 _143007 _143008 _143009 s f) = (term26 _143007 _143008 _143009 f s)) = (term27 _143007 _143008 _143009 f s).
Proof. exact (@lem8050298 _143007 _143008 _143009 (term25 _143007 _143008 _143009 s f) (term26 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050305 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term28 _140454 _140455 _140456 P) = (term29 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8050306 {_143007 _143008 _143009 : Type'} (P : type16 _143007 _143008 _143009) : (term28 _143007 _143008 _143009 P) = (term29 _143007 _143008 _143009 P).
Proof. exact (@lem8050305 _143007 _143008 _143009 P). Qed.
Lemma lem8050307 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term30 _143007 _143008 _143009 f s) = (term31 _143007 _143008 _143009 f s).
Proof. exact (@lem8050306 _143007 _143008 _143009 (term32 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050308 {_143007 _143008 _143009 : Type'} (x : type2 _143007 _143008 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term33 _143007 _143008 _143009 f s x) = ((term34 _143007 _143008 _143009 x s f) = (term35 _143007 _143008 _143009 x f s)).
Proof. exact (eq_refl (term33 _143007 _143008 _143009 f s x)). Qed.
Lemma lem8050309 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term36 _143007 _143008 _143009 f s) = (term32 _143007 _143008 _143009 f s).
Proof. exact (fun_ext (fun x : type2 _143007 _143008 _143009 => @lem8050308 _143007 _143008 _143009 x f s)). Qed.
Lemma lem8050310 {_143007 _143008 _143009 : Type'} : (@all (cart _143007 (finite_sum _143008 _143009))) = (@all (cart _143007 (finite_sum _143008 _143009))).
Proof. exact (eq_refl (@all (cart _143007 (finite_sum _143008 _143009)))). Qed.
Lemma lem8050311 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term30 _143007 _143008 _143009 f s) = (term27 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8050310 _143007 _143008 _143009) (@lem8050309 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8050313 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term37 _143007 _143008 _143009 f s) = (term38 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8050312) (@lem8050311 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050314 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term39 _143007 _143008 _143009 f s x y) = ((term40 _143007 _143008 _143009 x y s f) = (term41 _143007 _143008 _143009 x y f s)).
Proof. exact (eq_refl (term39 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8050315 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term42 _143007 _143008 _143009 f s x) = (term43 _143007 _143008 _143009 x f s).
Proof. exact (fun_ext (fun y : cart _143007 _143009 => @lem8050314 _143007 _143008 _143009 x y f s)). Qed.
Lemma lem8050316 {_143007 _143009 : Type'} : (@all (cart _143007 _143009)) = (@all (cart _143007 _143009)).
Proof. exact (eq_refl (@all (cart _143007 _143009))). Qed.
Lemma lem8050317 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term44 _143007 _143008 _143009 f s x) = (term45 _143007 _143008 _143009 x f s).
Proof. exact (MK_COMB (@lem8050316 _143007 _143009) (@lem8050315 _143007 _143008 _143009 x f s)). Qed.
Lemma lem8050318 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term46 _143007 _143008 _143009 f s) = (term47 _143007 _143008 _143009 f s).
Proof. exact (fun_ext (fun x : cart _143007 _143008 => @lem8050317 _143007 _143008 _143009 x f s)). Qed.
Lemma lem8050319 {_143007 _143008 : Type'} : (@all (cart _143007 _143008)) = (@all (cart _143007 _143008)).
Proof. exact (eq_refl (@all (cart _143007 _143008))). Qed.
Lemma lem8050320 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term31 _143007 _143008 _143009 f s) = (term48 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8050319 _143007 _143008) (@lem8050318 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050321 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : ((term30 _143007 _143008 _143009 f s) = (term31 _143007 _143008 _143009 f s)) = ((term27 _143007 _143008 _143009 f s) = (term48 _143007 _143008 _143009 f s)).
Proof. exact (MK_COMB (@lem8050313 _143007 _143008 _143009 f s) (@lem8050320 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050322 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term27 _143007 _143008 _143009 f s) = (term48 _143007 _143008 _143009 f s).
Proof. exact (EQ_MP (@lem8050321 _143007 _143008 _143009 f s) (@lem8050307 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050329 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : ((term25 _143007 _143008 _143009 s f) = (term26 _143007 _143008 _143009 f s)) = (term48 _143007 _143008 _143009 f s).
Proof. exact (TRANS (@lem8050299 _143007 _143008 _143009 f s) (@lem8050322 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050341 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8050213 _141927 _141928 _141929 x s y t) (@lem8050212 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8050342 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) (t : type24 _143007 _143009) : (term7 _143007 _143008 _143009 x y s t) = (term8 _143007 _143008 _143009 x s y t).
Proof. exact (@lem8050341 _143007 _143008 _143009 x s y t). Qed.
Lemma lem8050343 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) : (term40 _143007 _143008 _143009 x y s f) = (term49 _143007 _143008 _143009 x s y f).
Proof. exact (@lem8050342 _143007 _143008 _143009 x s y (@INTERS (cart _143007 _143009) f)). Qed.
Lemma lem8050346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8050347 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) : (term50 _143007 _143008 _143009 x y s f) = (term51 _143007 _143008 _143009 x s y f).
Proof. exact (MK_COMB (@lem8050346) (@lem8050343 _143007 _143008 _143009 x s y f)). Qed.
Lemma lem8050349 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term22 _89711 _89725 P f) = (term23 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem8050279 _89711 _89725 P f) (@lem8050278 _89711 _89725 P f)). Qed.
Lemma lem8050350 {_143007 _143008 _143009 : Type'} (P : type56 _143007 _143009) (f : type57 _143007 _143008 _143009) : (term52 _143007 _143008 _143009 P f) = (term53 _143007 _143008 _143009 P f).
Proof. exact (@lem8050349 (type2 _143007 _143008 _143009) (type24 _143007 _143009) P f). Qed.
Lemma lem8050351 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term54 _143007 _143008 _143009 f s) = (term55 _143007 _143008 _143009 f s).
Proof. exact (@lem8050350 _143007 _143008 _143009 (term56 _143007 _143009 f) (term57 _143007 _143008 _143009 s)). Qed.
Lemma lem8050352 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) : (term58 _143007 _143009 f t) = (@IN ((cart _143007 _143009) -> Prop) t f).
Proof. exact (eq_refl (term58 _143007 _143009 f t)). Qed.
Lemma lem8050353 {_143007 _143008 _143009 : Type'} (GEN_PVAR_368 : type16 _143007 _143008 _143009) : (@SETSPEC ((cart _143007 (finite_sum _143008 _143009)) -> Prop) GEN_PVAR_368) = (@SETSPEC ((cart _143007 (finite_sum _143008 _143009)) -> Prop) GEN_PVAR_368).
Proof. exact (eq_refl (@SETSPEC ((cart _143007 (finite_sum _143008 _143009)) -> Prop) GEN_PVAR_368)). Qed.
Lemma lem8050354 {_143007 _143008 _143009 : Type'} (GEN_PVAR_368 : type16 _143007 _143008 _143009) (t : type24 _143007 _143009) (f : type56 _143007 _143009) : (term59 _143007 _143008 _143009 GEN_PVAR_368 f t) = (term60 _143007 _143008 _143009 GEN_PVAR_368 t f).
Proof. exact (MK_COMB (@lem8050353 _143007 _143008 _143009 GEN_PVAR_368) (@lem8050352 _143007 _143009 t f)). Qed.
Lemma lem8050355 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (t : type24 _143007 _143009) : (term61 _143007 _143008 _143009 s t) = (@PCROSS _143007 _143008 _143009 s t).
Proof. exact (eq_refl (term61 _143007 _143008 _143009 s t)). Qed.
Lemma lem8050356 {_143007 _143008 _143009 : Type'} (GEN_PVAR_368 : type16 _143007 _143008 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (t : type24 _143007 _143009) : (term62 _143007 _143008 _143009 GEN_PVAR_368 f s t) = (term63 _143007 _143008 _143009 GEN_PVAR_368 f s t).
Proof. exact (MK_COMB (@lem8050354 _143007 _143008 _143009 GEN_PVAR_368 t f) (@lem8050355 _143007 _143008 _143009 s t)). Qed.
Lemma lem8050357 {_143007 _143008 _143009 : Type'} (GEN_PVAR_368 : type16 _143007 _143008 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term64 _143007 _143008 _143009 GEN_PVAR_368 f s) = (term65 _143007 _143008 _143009 GEN_PVAR_368 f s).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8050356 _143007 _143008 _143009 GEN_PVAR_368 f s t)). Qed.
Lemma lem8050358 {_143007 _143009 : Type'} : (@ex ((cart _143007 _143009) -> Prop)) = (@ex ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8050359 {_143007 _143008 _143009 : Type'} (GEN_PVAR_368 : type16 _143007 _143008 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term66 _143007 _143008 _143009 GEN_PVAR_368 f s) = (term67 _143007 _143008 _143009 GEN_PVAR_368 f s).
Proof. exact (MK_COMB (@lem8050358 _143007 _143009) (@lem8050357 _143007 _143008 _143009 GEN_PVAR_368 f s)). Qed.
Lemma lem8050360 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term68 _143007 _143008 _143009 f s) = (term69 _143007 _143008 _143009 f s).
Proof. exact (fun_ext (fun GEN_PVAR_368 : type16 _143007 _143008 _143009 => @lem8050359 _143007 _143008 _143009 GEN_PVAR_368 f s)). Qed.
Lemma lem8050361 {_143007 _143008 _143009 : Type'} : (@GSPEC ((cart _143007 (finite_sum _143008 _143009)) -> Prop)) = (@GSPEC ((cart _143007 (finite_sum _143008 _143009)) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((cart _143007 (finite_sum _143008 _143009)) -> Prop))). Qed.
Lemma lem8050362 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term70 _143007 _143008 _143009 f s) = (term71 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8050361 _143007 _143008 _143009) (@lem8050360 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050363 {_143007 _143008 _143009 : Type'} : (@INTERS (cart _143007 (finite_sum _143008 _143009))) = (@INTERS (cart _143007 (finite_sum _143008 _143009))).
Proof. exact (eq_refl (@INTERS (cart _143007 (finite_sum _143008 _143009)))). Qed.
Lemma lem8050364 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term54 _143007 _143008 _143009 f s) = (term26 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8050363 _143007 _143008 _143009) (@lem8050362 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050365 {_143007 _143008 _143009 : Type'} : (@eq ((cart _143007 (finite_sum _143008 _143009)) -> Prop)) = (@eq ((cart _143007 (finite_sum _143008 _143009)) -> Prop)).
Proof. exact (eq_refl (@eq ((cart _143007 (finite_sum _143008 _143009)) -> Prop))). Qed.
Lemma lem8050366 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term72 _143007 _143008 _143009 f s) = (term73 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8050365 _143007 _143008 _143009) (@lem8050364 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050367 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) : (term58 _143007 _143009 f t) = (@IN ((cart _143007 _143009) -> Prop) t f).
Proof. exact (eq_refl (term58 _143007 _143009 f t)). Qed.
Lemma lem8050368 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8050369 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) : (term74 _143007 _143009 f t) = (term75 _143007 _143009 t f).
Proof. exact (MK_COMB (@lem8050368) (@lem8050367 _143007 _143009 t f)). Qed.
Lemma lem8050370 {_143007 _143008 _143009 : Type'} (s : type24 _143007 _143008) (t : type24 _143007 _143009) : (term61 _143007 _143008 _143009 s t) = (@PCROSS _143007 _143008 _143009 s t).
Proof. exact (eq_refl (term61 _143007 _143008 _143009 s t)). Qed.
Lemma lem8050371 {_143007 _143008 _143009 : Type'} (a : type2 _143007 _143008 _143009) : (@IN (cart _143007 (finite_sum _143008 _143009)) a) = (@IN (cart _143007 (finite_sum _143008 _143009)) a).
Proof. exact (eq_refl (@IN (cart _143007 (finite_sum _143008 _143009)) a)). Qed.
Lemma lem8050372 {_143007 _143008 _143009 : Type'} (a : type2 _143007 _143008 _143009) (s : type24 _143007 _143008) (t : type24 _143007 _143009) : (term76 _143007 _143008 _143009 a s t) = (term77 _143007 _143008 _143009 a s t).
Proof. exact (MK_COMB (@lem8050371 _143007 _143008 _143009 a) (@lem8050370 _143007 _143008 _143009 s t)). Qed.
Lemma lem8050373 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (a : type2 _143007 _143008 _143009) (s : type24 _143007 _143008) (t : type24 _143007 _143009) : (term78 _143007 _143008 _143009 f a s t) = (term79 _143007 _143008 _143009 f a s t).
Proof. exact (MK_COMB (@lem8050369 _143007 _143009 t f) (@lem8050372 _143007 _143008 _143009 a s t)). Qed.
Lemma lem8050374 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (a : type2 _143007 _143008 _143009) (s : type24 _143007 _143008) : (term80 _143007 _143008 _143009 f a s) = (term81 _143007 _143008 _143009 f a s).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8050373 _143007 _143008 _143009 f a s t)). Qed.
Lemma lem8050375 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8050376 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (a : type2 _143007 _143008 _143009) (s : type24 _143007 _143008) : (term82 _143007 _143008 _143009 f a s) = (term83 _143007 _143008 _143009 f a s).
Proof. exact (MK_COMB (@lem8050375 _143007 _143009) (@lem8050374 _143007 _143008 _143009 f a s)). Qed.
Lemma lem8050377 {_143007 _143008 _143009 : Type'} (GEN_PVAR_56 : type2 _143007 _143008 _143009) : (@SETSPEC (cart _143007 (finite_sum _143008 _143009)) GEN_PVAR_56) = (@SETSPEC (cart _143007 (finite_sum _143008 _143009)) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (cart _143007 (finite_sum _143008 _143009)) GEN_PVAR_56)). Qed.
Lemma lem8050378 {_143007 _143008 _143009 : Type'} (GEN_PVAR_56 : type2 _143007 _143008 _143009) (f : type56 _143007 _143009) (a : type2 _143007 _143008 _143009) (s : type24 _143007 _143008) : (term84 _143007 _143008 _143009 GEN_PVAR_56 f a s) = (term85 _143007 _143008 _143009 GEN_PVAR_56 f a s).
Proof. exact (MK_COMB (@lem8050377 _143007 _143008 _143009 GEN_PVAR_56) (@lem8050376 _143007 _143008 _143009 f a s)). Qed.
Lemma lem8050379 {_143007 _143008 _143009 : Type'} (a : type2 _143007 _143008 _143009) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8050380 {_143007 _143008 _143009 : Type'} (GEN_PVAR_56 : type2 _143007 _143008 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (a : type2 _143007 _143008 _143009) : (term86 _143007 _143008 _143009 GEN_PVAR_56 f s a) = (term87 _143007 _143008 _143009 GEN_PVAR_56 f s a).
Proof. exact (MK_COMB (@lem8050378 _143007 _143008 _143009 GEN_PVAR_56 f a s) (@lem8050379 _143007 _143008 _143009 a)). Qed.
Lemma lem8050381 {_143007 _143008 _143009 : Type'} (GEN_PVAR_56 : type2 _143007 _143008 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term88 _143007 _143008 _143009 GEN_PVAR_56 f s) = (term89 _143007 _143008 _143009 GEN_PVAR_56 f s).
Proof. exact (fun_ext (fun a : type2 _143007 _143008 _143009 => @lem8050380 _143007 _143008 _143009 GEN_PVAR_56 f s a)). Qed.
Lemma lem8050382 {_143007 _143008 _143009 : Type'} : (@ex (cart _143007 (finite_sum _143008 _143009))) = (@ex (cart _143007 (finite_sum _143008 _143009))).
Proof. exact (eq_refl (@ex (cart _143007 (finite_sum _143008 _143009)))). Qed.
Lemma lem8050383 {_143007 _143008 _143009 : Type'} (GEN_PVAR_56 : type2 _143007 _143008 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term90 _143007 _143008 _143009 GEN_PVAR_56 f s) = (term91 _143007 _143008 _143009 GEN_PVAR_56 f s).
Proof. exact (MK_COMB (@lem8050382 _143007 _143008 _143009) (@lem8050381 _143007 _143008 _143009 GEN_PVAR_56 f s)). Qed.
Lemma lem8050384 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term92 _143007 _143008 _143009 f s) = (term93 _143007 _143008 _143009 f s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : type2 _143007 _143008 _143009 => @lem8050383 _143007 _143008 _143009 GEN_PVAR_56 f s)). Qed.
Lemma lem8050385 {_143007 _143008 _143009 : Type'} : (@GSPEC (cart _143007 (finite_sum _143008 _143009))) = (@GSPEC (cart _143007 (finite_sum _143008 _143009))).
Proof. exact (eq_refl (@GSPEC (cart _143007 (finite_sum _143008 _143009)))). Qed.
Lemma lem8050386 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term55 _143007 _143008 _143009 f s) = (term94 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8050385 _143007 _143008 _143009) (@lem8050384 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050387 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : ((term54 _143007 _143008 _143009 f s) = (term55 _143007 _143008 _143009 f s)) = ((term26 _143007 _143008 _143009 f s) = (term94 _143007 _143008 _143009 f s)).
Proof. exact (MK_COMB (@lem8050366 _143007 _143008 _143009 f s) (@lem8050386 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050388 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term26 _143007 _143008 _143009 f s) = (term94 _143007 _143008 _143009 f s).
Proof. exact (EQ_MP (@lem8050387 _143007 _143008 _143009 f s) (@lem8050351 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050401 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (y : cart _143007 _143009) : (term95 _143007 _143008 _143009 x y) = (term95 _143007 _143008 _143009 x y).
Proof. exact (eq_refl (term95 _143007 _143008 _143009 x y)). Qed.
Lemma lem8050402 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term41 _143007 _143008 _143009 x y f s) = (term96 _143007 _143008 _143009 x y f s).
Proof. exact (MK_COMB (@lem8050401 _143007 _143008 _143009 x y) (@lem8050388 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050404 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term13 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem8050244 _83095 p x) (@lem8050243 _83095 p x)). Qed.
Lemma lem8050405 {_143007 _143008 _143009 : Type'} (p : type16 _143007 _143008 _143009) (x : type2 _143007 _143008 _143009) : (term97 _143007 _143008 _143009 x p) = (p x).
Proof. exact (@lem8050404 (type2 _143007 _143008 _143009) p x). Qed.
Lemma lem8050406 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) (x : cart _143007 _143008) (y : cart _143007 _143009) : (term98 _143007 _143008 _143009 x y f s) = (term99 _143007 _143008 _143009 f s x y).
Proof. exact (@lem8050405 _143007 _143008 _143009 (term100 _143007 _143008 _143009 f s) (@pastecart _143007 _143008 _143009 x y)). Qed.
Lemma lem8050407 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (a : type2 _143007 _143008 _143009) (s : type24 _143007 _143008) : (term101 _143007 _143008 _143009 f s a) = (term83 _143007 _143008 _143009 f a s).
Proof. exact (eq_refl (term101 _143007 _143008 _143009 f s a)). Qed.
Lemma lem8050408 {_143007 _143008 _143009 : Type'} (GEN_PVAR_56 : type2 _143007 _143008 _143009) : (@SETSPEC (cart _143007 (finite_sum _143008 _143009)) GEN_PVAR_56) = (@SETSPEC (cart _143007 (finite_sum _143008 _143009)) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (cart _143007 (finite_sum _143008 _143009)) GEN_PVAR_56)). Qed.
Lemma lem8050409 {_143007 _143008 _143009 : Type'} (GEN_PVAR_56 : type2 _143007 _143008 _143009) (f : type56 _143007 _143009) (a : type2 _143007 _143008 _143009) (s : type24 _143007 _143008) : (term102 _143007 _143008 _143009 GEN_PVAR_56 f s a) = (term85 _143007 _143008 _143009 GEN_PVAR_56 f a s).
Proof. exact (MK_COMB (@lem8050408 _143007 _143008 _143009 GEN_PVAR_56) (@lem8050407 _143007 _143008 _143009 f a s)). Qed.
Lemma lem8050410 {_143007 _143008 _143009 : Type'} (a : type2 _143007 _143008 _143009) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8050411 {_143007 _143008 _143009 : Type'} (GEN_PVAR_56 : type2 _143007 _143008 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) (a : type2 _143007 _143008 _143009) : (term103 _143007 _143008 _143009 GEN_PVAR_56 f s a) = (term87 _143007 _143008 _143009 GEN_PVAR_56 f s a).
Proof. exact (MK_COMB (@lem8050409 _143007 _143008 _143009 GEN_PVAR_56 f a s) (@lem8050410 _143007 _143008 _143009 a)). Qed.
Lemma lem8050412 {_143007 _143008 _143009 : Type'} (GEN_PVAR_56 : type2 _143007 _143008 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term104 _143007 _143008 _143009 GEN_PVAR_56 f s) = (term89 _143007 _143008 _143009 GEN_PVAR_56 f s).
Proof. exact (fun_ext (fun a : type2 _143007 _143008 _143009 => @lem8050411 _143007 _143008 _143009 GEN_PVAR_56 f s a)). Qed.
Lemma lem8050413 {_143007 _143008 _143009 : Type'} : (@ex (cart _143007 (finite_sum _143008 _143009))) = (@ex (cart _143007 (finite_sum _143008 _143009))).
Proof. exact (eq_refl (@ex (cart _143007 (finite_sum _143008 _143009)))). Qed.
Lemma lem8050414 {_143007 _143008 _143009 : Type'} (GEN_PVAR_56 : type2 _143007 _143008 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term105 _143007 _143008 _143009 GEN_PVAR_56 f s) = (term91 _143007 _143008 _143009 GEN_PVAR_56 f s).
Proof. exact (MK_COMB (@lem8050413 _143007 _143008 _143009) (@lem8050412 _143007 _143008 _143009 GEN_PVAR_56 f s)). Qed.
Lemma lem8050415 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term106 _143007 _143008 _143009 f s) = (term93 _143007 _143008 _143009 f s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : type2 _143007 _143008 _143009 => @lem8050414 _143007 _143008 _143009 GEN_PVAR_56 f s)). Qed.
Lemma lem8050416 {_143007 _143008 _143009 : Type'} : (@GSPEC (cart _143007 (finite_sum _143008 _143009))) = (@GSPEC (cart _143007 (finite_sum _143008 _143009))).
Proof. exact (eq_refl (@GSPEC (cart _143007 (finite_sum _143008 _143009)))). Qed.
Lemma lem8050417 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term107 _143007 _143008 _143009 f s) = (term94 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8050416 _143007 _143008 _143009) (@lem8050415 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050418 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (y : cart _143007 _143009) : (term95 _143007 _143008 _143009 x y) = (term95 _143007 _143008 _143009 x y).
Proof. exact (eq_refl (term95 _143007 _143008 _143009 x y)). Qed.
Lemma lem8050419 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term98 _143007 _143008 _143009 x y f s) = (term96 _143007 _143008 _143009 x y f s).
Proof. exact (MK_COMB (@lem8050418 _143007 _143008 _143009 x y) (@lem8050417 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8050421 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (y : cart _143007 _143009) (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term108 _143007 _143008 _143009 x y f s) = (term109 _143007 _143008 _143009 x y f s).
Proof. exact (MK_COMB (@lem8050420) (@lem8050419 _143007 _143008 _143009 x y f s)). Qed.
Lemma lem8050422 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (y : cart _143007 _143009) (s : type24 _143007 _143008) : (term99 _143007 _143008 _143009 f s x y) = (term110 _143007 _143008 _143009 f x y s).
Proof. exact (eq_refl (term99 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8050423 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (y : cart _143007 _143009) (s : type24 _143007 _143008) : ((term98 _143007 _143008 _143009 x y f s) = (term99 _143007 _143008 _143009 f s x y)) = ((term96 _143007 _143008 _143009 x y f s) = (term110 _143007 _143008 _143009 f x y s)).
Proof. exact (MK_COMB (@lem8050421 _143007 _143008 _143009 x y f s) (@lem8050422 _143007 _143008 _143009 f x y s)). Qed.
Lemma lem8050424 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (y : cart _143007 _143009) (s : type24 _143007 _143008) : (term96 _143007 _143008 _143009 x y f s) = (term110 _143007 _143008 _143009 f x y s).
Proof. exact (EQ_MP (@lem8050423 _143007 _143008 _143009 f x y s) (@lem8050406 _143007 _143008 _143009 f s x y)). Qed.
Lemma lem8050434 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8050213 _141927 _141928 _141929 x s y t) (@lem8050212 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8050435 {_143007 _143008 _143009 : Type'} (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) (t : type24 _143007 _143009) : (term7 _143007 _143008 _143009 x y s t) = (term8 _143007 _143008 _143009 x s y t).
Proof. exact (@lem8050434 _143007 _143008 _143009 x s y t). Qed.
Lemma lem8050438 {_143007 _143009 : Type'} (t : type24 _143007 _143009) (f : type56 _143007 _143009) : (term75 _143007 _143009 t f) = (term75 _143007 _143009 t f).
Proof. exact (eq_refl (term75 _143007 _143009 t f)). Qed.
Lemma lem8050439 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) (t : type24 _143007 _143009) : (term111 _143007 _143008 _143009 f x y s t) = (term112 _143007 _143008 _143009 f x s y t).
Proof. exact (MK_COMB (@lem8050438 _143007 _143009 t f) (@lem8050435 _143007 _143008 _143009 x s y t)). Qed.
Lemma lem8050442 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) : (term113 _143007 _143008 _143009 f x y s) = (term114 _143007 _143008 _143009 f x s y).
Proof. exact (fun_ext (fun t : type24 _143007 _143009 => @lem8050439 _143007 _143008 _143009 f x s y t)). Qed.
Lemma lem8050443 {_143007 _143009 : Type'} : (@all ((cart _143007 _143009) -> Prop)) = (@all ((cart _143007 _143009) -> Prop)).
Proof. exact (eq_refl (@all ((cart _143007 _143009) -> Prop))). Qed.
Lemma lem8050444 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) : (term110 _143007 _143008 _143009 f x y s) = (term115 _143007 _143008 _143009 f x s y).
Proof. exact (MK_COMB (@lem8050443 _143007 _143009) (@lem8050442 _143007 _143008 _143009 f x s y)). Qed.
Lemma lem8050451 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) : (term96 _143007 _143008 _143009 x y f s) = (term115 _143007 _143008 _143009 f x s y).
Proof. exact (TRANS (@lem8050424 _143007 _143008 _143009 f x y s) (@lem8050444 _143007 _143008 _143009 f x s y)). Qed.
Lemma lem8050452 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) : (term41 _143007 _143008 _143009 x y f s) = (term115 _143007 _143008 _143009 f x s y).
Proof. exact (TRANS (@lem8050402 _143007 _143008 _143009 x y f s) (@lem8050451 _143007 _143008 _143009 f x s y)). Qed.
Lemma lem8050453 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (s : type24 _143007 _143008) (y : cart _143007 _143009) : ((term40 _143007 _143008 _143009 x y s f) = (term41 _143007 _143008 _143009 x y f s)) = ((term49 _143007 _143008 _143009 x s y f) = (term115 _143007 _143008 _143009 f x s y)).
Proof. exact (MK_COMB (@lem8050347 _143007 _143008 _143009 x s y f) (@lem8050452 _143007 _143008 _143009 f x s y)). Qed.
Lemma lem8050458 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (s : type24 _143007 _143008) : (term43 _143007 _143008 _143009 x f s) = (term116 _143007 _143008 _143009 f x s).
Proof. exact (fun_ext (fun y : cart _143007 _143009 => @lem8050453 _143007 _143008 _143009 f x s y)). Qed.
Lemma lem8050459 {_143007 _143009 : Type'} : (@all (cart _143007 _143009)) = (@all (cart _143007 _143009)).
Proof. exact (eq_refl (@all (cart _143007 _143009))). Qed.
Lemma lem8050460 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (x : cart _143007 _143008) (s : type24 _143007 _143008) : (term45 _143007 _143008 _143009 x f s) = (term117 _143007 _143008 _143009 f x s).
Proof. exact (MK_COMB (@lem8050459 _143007 _143009) (@lem8050458 _143007 _143008 _143009 f x s)). Qed.
Lemma lem8050467 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term47 _143007 _143008 _143009 f s) = (term118 _143007 _143008 _143009 f s).
Proof. exact (fun_ext (fun x : cart _143007 _143008 => @lem8050460 _143007 _143008 _143009 f x s)). Qed.
Lemma lem8050468 {_143007 _143008 : Type'} : (@all (cart _143007 _143008)) = (@all (cart _143007 _143008)).
Proof. exact (eq_refl (@all (cart _143007 _143008))). Qed.
Lemma lem8050469 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term48 _143007 _143008 _143009 f s) = (term119 _143007 _143008 _143009 f s).
Proof. exact (MK_COMB (@lem8050468 _143007 _143008) (@lem8050467 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050476 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : ((term25 _143007 _143008 _143009 s f) = (term26 _143007 _143008 _143009 f s)) = (term119 _143007 _143008 _143009 f s).
Proof. exact (TRANS (@lem8050329 _143007 _143008 _143009 f s) (@lem8050469 _143007 _143008 _143009 f s)). Qed.
Lemma lem8050477 {_143007 _143008 _143009 : Type'} (f : type56 _143007 _143009) (s : type24 _143007 _143008) : (term119 _143007 _143008 _143009 f s) = ((term25 _143007 _143008 _143009 s f) = (term26 _143007 _143008 _143009 f s)).
Proof. exact (SYM (@lem8050476 _143007 _143008 _143009 f s)). Qed.
