Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_INTERS_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_DIFF_spec.
Require Import IN_UNIONS_spec.
Require Import IN_UNIV_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Require Import thm7_spec.
Lemma lem3472234 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3472235 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem3472234 _83095 p). Qed.
Lemma lem3472236 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem3472237 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem3472236 _83095 p) (@lem3472235 _83095 p)). Qed.
Lemma lem3472238 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem3472237 _83095 p x). Qed.
Lemma lem3472239 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem3472263 {_89711 _89725 : Type'} : term5 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem3472264 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term6 _89711 _89725 P.
Proof. exact (@lem3472263 _89711 _89725 P). Qed.
Lemma lem3472265 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term6 _89711 _89725 P) = (term7 _89711 _89725 P).
Proof. exact (eq_refl (term6 _89711 _89725 P)). Qed.
Lemma lem3472266 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term7 _89711 _89725 P.
Proof. exact (EQ_MP (@lem3472265 _89711 _89725 P) (@lem3472264 _89711 _89725 P)). Qed.
Lemma lem3472267 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term8 _89711 _89725 P f.
Proof. exact (@lem3472266 _89711 _89725 P f). Qed.
Lemma lem3472268 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term8 _89711 _89725 P f) = ((term9 _89711 _89725 P f) = (term10 _89711 _89725 P f)).
Proof. exact (eq_refl (term8 _89711 _89725 P f)). Qed.
Lemma lem3472270 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (@lem3205495 A s). Qed.
Lemma lem3472271 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem3472272 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (EQ_MP (@lem3472271 A s) (@lem3472270 A s)). Qed.
Lemma lem3472273 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term13 A s t.
Proof. exact (@lem3472272 A s t). Qed.
Lemma lem3472274 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term13 A s t) = (term14 A s t).
Proof. exact (eq_refl (term13 A s t)). Qed.
Lemma lem3472275 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term14 A s t.
Proof. exact (EQ_MP (@lem3472274 A s t) (@lem3472273 A s t)). Qed.
Lemma lem3472276 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term15 A s t x.
Proof. exact (@lem3472275 A s t x). Qed.
Lemma lem3472277 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A s t x) = ((term16 A x s t) = (term17 A s x t)).
Proof. exact (eq_refl (term15 A s t x)). Qed.
Lemma lem3472279 {A : Type'} (x : A) : term18 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem3472280 {A : Type'} (x : A) : (term18 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term18 A x)). Qed.
Lemma lem3472281 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem3472280 A x) (@lem3472279 A x)). Qed.
Lemma lem3472282 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem3472284 {A : Type'} (s : type686 A) : term19 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem3472285 {A : Type'} (s : type686 A) : (term19 A s) = (term20 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem3472286 {A : Type'} (s : type686 A) : term20 A s.
Proof. exact (EQ_MP (@lem3472285 A s) (@lem3472284 A s)). Qed.
Lemma lem3472287 {A : Type'} (s : type686 A) (x : A) : term21 A s x.
Proof. exact (@lem3472286 A s x). Qed.
Lemma lem3472288 {A : Type'} (s : type686 A) (x : A) : (term21 A s x) = ((term22 A x s) = (term23 A s x)).
Proof. exact (eq_refl (term21 A s x)). Qed.
Lemma lem3472290 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3472291 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem3472292 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (EQ_MP (@lem3472291 A s) (@lem3472290 A s)). Qed.
Lemma lem3472293 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term26 A s t.
Proof. exact (@lem3472292 A s t). Qed.
Lemma lem3472294 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = ((s = t) = (term27 A s t)).
Proof. exact (eq_refl (term26 A s t)). Qed.
Lemma lem3472297 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term27 A s t).
Proof. exact (EQ_MP (@lem3472294 A s t) (@lem3472293 A s t)). Qed.
Lemma lem3472298 {_90107 : Type'} (s : _90107 -> Prop) (t : _90107 -> Prop) : (s = t) = (term27 _90107 s t).
Proof. exact (@lem3472297 _90107 s t). Qed.
Lemma lem3472299 {_90107 : Type'} (s : type686 _90107) : ((@UNIONS _90107 s) = (term28 _90107 s)) = (term29 _90107 s).
Proof. exact (@lem3472298 _90107 (@UNIONS _90107 s) (term28 _90107 s)). Qed.
Lemma lem3472300 {_90107 : Type'} (s : type686 _90107) : (term29 _90107 s) = ((@UNIONS _90107 s) = (term28 _90107 s)).
Proof. exact (SYM (@lem3472299 _90107 s)). Qed.
Lemma lem3472308 {A : Type'} (s : type686 A) (x : A) : (term22 A x s) = (term23 A s x).
Proof. exact (EQ_MP (@lem3472288 A s x) (@lem3472287 A s x)). Qed.
Lemma lem3472309 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term22 _90107 x s) = (term23 _90107 s x).
Proof. exact (@lem3472308 _90107 s x). Qed.
Lemma lem3472316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3472317 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term30 _90107 x s) = (term31 _90107 s x).
Proof. exact (MK_COMB (@lem3472316) (@lem3472309 _90107 s x)). Qed.
Lemma lem3472319 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3472277 A s x t) (@lem3472276 A s t x)). Qed.
Lemma lem3472320 {_90107 : Type'} (s : _90107 -> Prop) (x : _90107) (t : _90107 -> Prop) : (term16 _90107 x s t) = (term17 _90107 s x t).
Proof. exact (@lem3472319 _90107 s x t). Qed.
Lemma lem3472321 {_90107 : Type'} (x : _90107) (s : type686 _90107) : (term32 _90107 x s) = (term33 _90107 x s).
Proof. exact (@lem3472320 _90107 (@UNIV _90107) x (term34 _90107 s)). Qed.
Lemma lem3472325 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3472282 A x) (@lem3472281 A x)). Qed.
Lemma lem3472326 {_90107 : Type'} (x : _90107) : (@IN _90107 x (@UNIV _90107)) = True.
Proof. exact (@lem3472325 _90107 x). Qed.
Lemma lem3472327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3472328 {_90107 : Type'} (x : _90107) : (term35 _90107 x) = (and True).
Proof. exact (MK_COMB (@lem3472327) (@lem3472326 _90107 x)). Qed.
Lemma lem3472330 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term9 _89711 _89725 P f) = (term10 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem3472268 _89711 _89725 P f) (@lem3472267 _89711 _89725 P f)). Qed.
Lemma lem3472331 {_90107 : Type'} (P : type686 _90107) (f : type672 _90107) : (term36 _90107 P f) = (term37 _90107 P f).
Proof. exact (@lem3472330 _90107 (_90107 -> Prop) P f). Qed.
Lemma lem3472332 {_90107 : Type'} (s : type686 _90107) : (term38 _90107 s) = (term39 _90107 s).
Proof. exact (@lem3472331 _90107 (term40 _90107 s) (term41 _90107)). Qed.
Lemma lem3472333 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) : (term42 _90107 s t) = (@IN (_90107 -> Prop) t s).
Proof. exact (eq_refl (term42 _90107 s t)). Qed.
Lemma lem3472334 {_90107 : Type'} (GEN_PVAR_66 : _90107 -> Prop) : (@SETSPEC (_90107 -> Prop) GEN_PVAR_66) = (@SETSPEC (_90107 -> Prop) GEN_PVAR_66).
Proof. exact (eq_refl (@SETSPEC (_90107 -> Prop) GEN_PVAR_66)). Qed.
Lemma lem3472335 {_90107 : Type'} (GEN_PVAR_66 : _90107 -> Prop) (t : _90107 -> Prop) (s : type686 _90107) : (term43 _90107 GEN_PVAR_66 s t) = (term44 _90107 GEN_PVAR_66 t s).
Proof. exact (MK_COMB (@lem3472334 _90107 GEN_PVAR_66) (@lem3472333 _90107 t s)). Qed.
Lemma lem3472336 {_90107 : Type'} (t : _90107 -> Prop) : (term45 _90107 t) = (@DIFF _90107 (@UNIV _90107) t).
Proof. exact (eq_refl (term45 _90107 t)). Qed.
Lemma lem3472337 {_90107 : Type'} (GEN_PVAR_66 : _90107 -> Prop) (s : type686 _90107) (t : _90107 -> Prop) : (term46 _90107 GEN_PVAR_66 s t) = (term47 _90107 GEN_PVAR_66 s t).
Proof. exact (MK_COMB (@lem3472335 _90107 GEN_PVAR_66 t s) (@lem3472336 _90107 t)). Qed.
Lemma lem3472338 {_90107 : Type'} (GEN_PVAR_66 : _90107 -> Prop) (s : type686 _90107) : (term48 _90107 GEN_PVAR_66 s) = (term49 _90107 GEN_PVAR_66 s).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472337 _90107 GEN_PVAR_66 s t)). Qed.
Lemma lem3472339 {_90107 : Type'} : (@ex (_90107 -> Prop)) = (@ex (_90107 -> Prop)).
Proof. exact (eq_refl (@ex (_90107 -> Prop))). Qed.
Lemma lem3472340 {_90107 : Type'} (GEN_PVAR_66 : _90107 -> Prop) (s : type686 _90107) : (term50 _90107 GEN_PVAR_66 s) = (term51 _90107 GEN_PVAR_66 s).
Proof. exact (MK_COMB (@lem3472339 _90107) (@lem3472338 _90107 GEN_PVAR_66 s)). Qed.
Lemma lem3472341 {_90107 : Type'} (s : type686 _90107) : (term52 _90107 s) = (term53 _90107 s).
Proof. exact (fun_ext (fun GEN_PVAR_66 : _90107 -> Prop => @lem3472340 _90107 GEN_PVAR_66 s)). Qed.
Lemma lem3472342 {_90107 : Type'} : (@GSPEC (_90107 -> Prop)) = (@GSPEC (_90107 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_90107 -> Prop))). Qed.
Lemma lem3472343 {_90107 : Type'} (s : type686 _90107) : (term54 _90107 s) = (term55 _90107 s).
Proof. exact (MK_COMB (@lem3472342 _90107) (@lem3472341 _90107 s)). Qed.
Lemma lem3472344 {_90107 : Type'} : (@INTERS _90107) = (@INTERS _90107).
Proof. exact (eq_refl (@INTERS _90107)). Qed.
Lemma lem3472345 {_90107 : Type'} (s : type686 _90107) : (term38 _90107 s) = (term34 _90107 s).
Proof. exact (MK_COMB (@lem3472344 _90107) (@lem3472343 _90107 s)). Qed.
Lemma lem3472346 {_90107 : Type'} : (@eq (_90107 -> Prop)) = (@eq (_90107 -> Prop)).
Proof. exact (eq_refl (@eq (_90107 -> Prop))). Qed.
Lemma lem3472347 {_90107 : Type'} (s : type686 _90107) : (term56 _90107 s) = (term57 _90107 s).
Proof. exact (MK_COMB (@lem3472346 _90107) (@lem3472345 _90107 s)). Qed.
Lemma lem3472348 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) : (term42 _90107 s t) = (@IN (_90107 -> Prop) t s).
Proof. exact (eq_refl (term42 _90107 s t)). Qed.
Lemma lem3472349 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3472350 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) : (term58 _90107 s t) = (term59 _90107 t s).
Proof. exact (MK_COMB (@lem3472349) (@lem3472348 _90107 t s)). Qed.
Lemma lem3472351 {_90107 : Type'} (t : _90107 -> Prop) : (term45 _90107 t) = (@DIFF _90107 (@UNIV _90107) t).
Proof. exact (eq_refl (term45 _90107 t)). Qed.
Lemma lem3472352 {_90107 : Type'} (a : _90107) : (@IN _90107 a) = (@IN _90107 a).
Proof. exact (eq_refl (@IN _90107 a)). Qed.
Lemma lem3472353 {_90107 : Type'} (a : _90107) (t : _90107 -> Prop) : (term60 _90107 a t) = (term61 _90107 a t).
Proof. exact (MK_COMB (@lem3472352 _90107 a) (@lem3472351 _90107 t)). Qed.
Lemma lem3472354 {_90107 : Type'} (s : type686 _90107) (a : _90107) (t : _90107 -> Prop) : (term62 _90107 s a t) = (term63 _90107 s a t).
Proof. exact (MK_COMB (@lem3472350 _90107 t s) (@lem3472353 _90107 a t)). Qed.
Lemma lem3472355 {_90107 : Type'} (s : type686 _90107) (a : _90107) : (term64 _90107 s a) = (term65 _90107 s a).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472354 _90107 s a t)). Qed.
Lemma lem3472356 {_90107 : Type'} : (@all (_90107 -> Prop)) = (@all (_90107 -> Prop)).
Proof. exact (eq_refl (@all (_90107 -> Prop))). Qed.
Lemma lem3472357 {_90107 : Type'} (s : type686 _90107) (a : _90107) : (term66 _90107 s a) = (term67 _90107 s a).
Proof. exact (MK_COMB (@lem3472356 _90107) (@lem3472355 _90107 s a)). Qed.
Lemma lem3472358 {_90107 : Type'} (GEN_PVAR_56 : _90107) : (@SETSPEC _90107 GEN_PVAR_56) = (@SETSPEC _90107 GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC _90107 GEN_PVAR_56)). Qed.
Lemma lem3472359 {_90107 : Type'} (GEN_PVAR_56 : _90107) (s : type686 _90107) (a : _90107) : (term68 _90107 GEN_PVAR_56 s a) = (term69 _90107 GEN_PVAR_56 s a).
Proof. exact (MK_COMB (@lem3472358 _90107 GEN_PVAR_56) (@lem3472357 _90107 s a)). Qed.
Lemma lem3472360 {_90107 : Type'} (a : _90107) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3472361 {_90107 : Type'} (GEN_PVAR_56 : _90107) (s : type686 _90107) (a : _90107) : (term70 _90107 GEN_PVAR_56 s a) = (term71 _90107 GEN_PVAR_56 s a).
Proof. exact (MK_COMB (@lem3472359 _90107 GEN_PVAR_56 s a) (@lem3472360 _90107 a)). Qed.
Lemma lem3472362 {_90107 : Type'} (GEN_PVAR_56 : _90107) (s : type686 _90107) : (term72 _90107 GEN_PVAR_56 s) = (term73 _90107 GEN_PVAR_56 s).
Proof. exact (fun_ext (fun a : _90107 => @lem3472361 _90107 GEN_PVAR_56 s a)). Qed.
Lemma lem3472363 {_90107 : Type'} : (@ex _90107) = (@ex _90107).
Proof. exact (eq_refl (@ex _90107)). Qed.
Lemma lem3472364 {_90107 : Type'} (GEN_PVAR_56 : _90107) (s : type686 _90107) : (term74 _90107 GEN_PVAR_56 s) = (term75 _90107 GEN_PVAR_56 s).
Proof. exact (MK_COMB (@lem3472363 _90107) (@lem3472362 _90107 GEN_PVAR_56 s)). Qed.
Lemma lem3472365 {_90107 : Type'} (s : type686 _90107) : (term76 _90107 s) = (term77 _90107 s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : _90107 => @lem3472364 _90107 GEN_PVAR_56 s)). Qed.
Lemma lem3472366 {_90107 : Type'} : (@GSPEC _90107) = (@GSPEC _90107).
Proof. exact (eq_refl (@GSPEC _90107)). Qed.
Lemma lem3472367 {_90107 : Type'} (s : type686 _90107) : (term39 _90107 s) = (term78 _90107 s).
Proof. exact (MK_COMB (@lem3472366 _90107) (@lem3472365 _90107 s)). Qed.
Lemma lem3472368 {_90107 : Type'} (s : type686 _90107) : ((term38 _90107 s) = (term39 _90107 s)) = ((term34 _90107 s) = (term78 _90107 s)).
Proof. exact (MK_COMB (@lem3472347 _90107 s) (@lem3472367 _90107 s)). Qed.
Lemma lem3472369 {_90107 : Type'} (s : type686 _90107) : (term34 _90107 s) = (term78 _90107 s).
Proof. exact (EQ_MP (@lem3472368 _90107 s) (@lem3472332 _90107 s)). Qed.
Lemma lem3472381 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3472277 A s x t) (@lem3472276 A s t x)). Qed.
Lemma lem3472382 {_90107 : Type'} (s : _90107 -> Prop) (x : _90107) (t : _90107 -> Prop) : (term16 _90107 x s t) = (term17 _90107 s x t).
Proof. exact (@lem3472381 _90107 s x t). Qed.
Lemma lem3472383 {_90107 : Type'} (a : _90107) (t : _90107 -> Prop) : (term61 _90107 a t) = (term79 _90107 a t).
Proof. exact (@lem3472382 _90107 (@UNIV _90107) a t). Qed.
Lemma lem3472387 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3472282 A x) (@lem3472281 A x)). Qed.
Lemma lem3472388 {_90107 : Type'} (x : _90107) : (@IN _90107 x (@UNIV _90107)) = True.
Proof. exact (@lem3472387 _90107 x). Qed.
Lemma lem3472389 {_90107 : Type'} (a : _90107) : (@IN _90107 a (@UNIV _90107)) = True.
Proof. exact (@lem3472388 _90107 a). Qed.
Lemma lem3472390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3472391 {_90107 : Type'} (a : _90107) : (term35 _90107 a) = (and True).
Proof. exact (MK_COMB (@lem3472390) (@lem3472389 _90107 a)). Qed.
Lemma lem3472392 {_90107 : Type'} (a : _90107) (t : _90107 -> Prop) : (term80 _90107 a t) = (term80 _90107 a t).
Proof. exact (eq_refl (term80 _90107 a t)). Qed.
Lemma lem3472393 {_90107 : Type'} (a : _90107) (t : _90107 -> Prop) : (term79 _90107 a t) = (term81 _90107 a t).
Proof. exact (MK_COMB (@lem3472391 _90107 a) (@lem3472392 _90107 a t)). Qed.
Lemma lem3472395 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3472396 {_90107 : Type'} (a : _90107) (t : _90107 -> Prop) : (term81 _90107 a t) = (term80 _90107 a t).
Proof. exact (@lem3472395 (term80 _90107 a t)). Qed.
Lemma lem3472397 {_90107 : Type'} (a : _90107) (t : _90107 -> Prop) : (term79 _90107 a t) = (term80 _90107 a t).
Proof. exact (TRANS (@lem3472393 _90107 a t) (@lem3472396 _90107 a t)). Qed.
Lemma lem3472398 {_90107 : Type'} (a : _90107) (t : _90107 -> Prop) : (term61 _90107 a t) = (term80 _90107 a t).
Proof. exact (TRANS (@lem3472383 _90107 a t) (@lem3472397 _90107 a t)). Qed.
Lemma lem3472399 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) : (term59 _90107 t s) = (term59 _90107 t s).
Proof. exact (eq_refl (term59 _90107 t s)). Qed.
Lemma lem3472400 {_90107 : Type'} (s : type686 _90107) (a : _90107) (t : _90107 -> Prop) : (term63 _90107 s a t) = (term82 _90107 s a t).
Proof. exact (MK_COMB (@lem3472399 _90107 t s) (@lem3472398 _90107 a t)). Qed.
Lemma lem3472403 {_90107 : Type'} (s : type686 _90107) (a : _90107) : (term65 _90107 s a) = (term83 _90107 s a).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472400 _90107 s a t)). Qed.
Lemma lem3472404 {_90107 : Type'} : (@all (_90107 -> Prop)) = (@all (_90107 -> Prop)).
Proof. exact (eq_refl (@all (_90107 -> Prop))). Qed.
Lemma lem3472405 {_90107 : Type'} (s : type686 _90107) (a : _90107) : (term67 _90107 s a) = (term84 _90107 s a).
Proof. exact (MK_COMB (@lem3472404 _90107) (@lem3472403 _90107 s a)). Qed.
Lemma lem3472410 {_90107 : Type'} (GEN_PVAR_56 : _90107) : (@SETSPEC _90107 GEN_PVAR_56) = (@SETSPEC _90107 GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC _90107 GEN_PVAR_56)). Qed.
Lemma lem3472411 {_90107 : Type'} (GEN_PVAR_56 : _90107) (s : type686 _90107) (a : _90107) : (term69 _90107 GEN_PVAR_56 s a) = (term85 _90107 GEN_PVAR_56 s a).
Proof. exact (MK_COMB (@lem3472410 _90107 GEN_PVAR_56) (@lem3472405 _90107 s a)). Qed.
Lemma lem3472412 {_90107 : Type'} (a : _90107) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3472413 {_90107 : Type'} (GEN_PVAR_56 : _90107) (s : type686 _90107) (a : _90107) : (term71 _90107 GEN_PVAR_56 s a) = (term86 _90107 GEN_PVAR_56 s a).
Proof. exact (MK_COMB (@lem3472411 _90107 GEN_PVAR_56 s a) (@lem3472412 _90107 a)). Qed.
Lemma lem3472414 {_90107 : Type'} (GEN_PVAR_56 : _90107) (s : type686 _90107) : (term73 _90107 GEN_PVAR_56 s) = (term87 _90107 GEN_PVAR_56 s).
Proof. exact (fun_ext (fun a : _90107 => @lem3472413 _90107 GEN_PVAR_56 s a)). Qed.
Lemma lem3472415 {_90107 : Type'} : (@ex _90107) = (@ex _90107).
Proof. exact (eq_refl (@ex _90107)). Qed.
Lemma lem3472416 {_90107 : Type'} (GEN_PVAR_56 : _90107) (s : type686 _90107) : (term75 _90107 GEN_PVAR_56 s) = (term88 _90107 GEN_PVAR_56 s).
Proof. exact (MK_COMB (@lem3472415 _90107) (@lem3472414 _90107 GEN_PVAR_56 s)). Qed.
Lemma lem3472421 {_90107 : Type'} (s : type686 _90107) : (term77 _90107 s) = (term89 _90107 s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : _90107 => @lem3472416 _90107 GEN_PVAR_56 s)). Qed.
Lemma lem3472422 {_90107 : Type'} : (@GSPEC _90107) = (@GSPEC _90107).
Proof. exact (eq_refl (@GSPEC _90107)). Qed.
Lemma lem3472423 {_90107 : Type'} (s : type686 _90107) : (term78 _90107 s) = (term90 _90107 s).
Proof. exact (MK_COMB (@lem3472422 _90107) (@lem3472421 _90107 s)). Qed.
Lemma lem3472424 {_90107 : Type'} (s : type686 _90107) : (term34 _90107 s) = (term90 _90107 s).
Proof. exact (TRANS (@lem3472369 _90107 s) (@lem3472423 _90107 s)). Qed.
Lemma lem3472425 {_90107 : Type'} (x : _90107) : (@IN _90107 x) = (@IN _90107 x).
Proof. exact (eq_refl (@IN _90107 x)). Qed.
Lemma lem3472426 {_90107 : Type'} (x : _90107) (s : type686 _90107) : (term91 _90107 x s) = (term92 _90107 x s).
Proof. exact (MK_COMB (@lem3472425 _90107 x) (@lem3472424 _90107 s)). Qed.
Lemma lem3472428 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3472239 _83095 p x) (@lem3472238 _83095 p x)). Qed.
Lemma lem3472429 {_90107 : Type'} (p : _90107 -> Prop) (x : _90107) : (term4 _90107 x p) = (p x).
Proof. exact (@lem3472428 _90107 p x). Qed.
Lemma lem3472430 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term93 _90107 x s) = (term94 _90107 s x).
Proof. exact (@lem3472429 _90107 (term95 _90107 s) x). Qed.
Lemma lem3472431 {_90107 : Type'} (s : type686 _90107) (a : _90107) : (term94 _90107 s a) = (term84 _90107 s a).
Proof. exact (eq_refl (term94 _90107 s a)). Qed.
Lemma lem3472432 {_90107 : Type'} (GEN_PVAR_56 : _90107) : (@SETSPEC _90107 GEN_PVAR_56) = (@SETSPEC _90107 GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC _90107 GEN_PVAR_56)). Qed.
Lemma lem3472433 {_90107 : Type'} (GEN_PVAR_56 : _90107) (s : type686 _90107) (a : _90107) : (term96 _90107 GEN_PVAR_56 s a) = (term85 _90107 GEN_PVAR_56 s a).
Proof. exact (MK_COMB (@lem3472432 _90107 GEN_PVAR_56) (@lem3472431 _90107 s a)). Qed.
Lemma lem3472434 {_90107 : Type'} (a : _90107) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3472435 {_90107 : Type'} (GEN_PVAR_56 : _90107) (s : type686 _90107) (a : _90107) : (term97 _90107 GEN_PVAR_56 s a) = (term86 _90107 GEN_PVAR_56 s a).
Proof. exact (MK_COMB (@lem3472433 _90107 GEN_PVAR_56 s a) (@lem3472434 _90107 a)). Qed.
Lemma lem3472436 {_90107 : Type'} (GEN_PVAR_56 : _90107) (s : type686 _90107) : (term98 _90107 GEN_PVAR_56 s) = (term87 _90107 GEN_PVAR_56 s).
Proof. exact (fun_ext (fun a : _90107 => @lem3472435 _90107 GEN_PVAR_56 s a)). Qed.
Lemma lem3472437 {_90107 : Type'} : (@ex _90107) = (@ex _90107).
Proof. exact (eq_refl (@ex _90107)). Qed.
Lemma lem3472438 {_90107 : Type'} (GEN_PVAR_56 : _90107) (s : type686 _90107) : (term99 _90107 GEN_PVAR_56 s) = (term88 _90107 GEN_PVAR_56 s).
Proof. exact (MK_COMB (@lem3472437 _90107) (@lem3472436 _90107 GEN_PVAR_56 s)). Qed.
Lemma lem3472439 {_90107 : Type'} (s : type686 _90107) : (term100 _90107 s) = (term89 _90107 s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : _90107 => @lem3472438 _90107 GEN_PVAR_56 s)). Qed.
Lemma lem3472440 {_90107 : Type'} : (@GSPEC _90107) = (@GSPEC _90107).
Proof. exact (eq_refl (@GSPEC _90107)). Qed.
Lemma lem3472441 {_90107 : Type'} (s : type686 _90107) : (term101 _90107 s) = (term90 _90107 s).
Proof. exact (MK_COMB (@lem3472440 _90107) (@lem3472439 _90107 s)). Qed.
Lemma lem3472442 {_90107 : Type'} (x : _90107) : (@IN _90107 x) = (@IN _90107 x).
Proof. exact (eq_refl (@IN _90107 x)). Qed.
Lemma lem3472443 {_90107 : Type'} (x : _90107) (s : type686 _90107) : (term93 _90107 x s) = (term92 _90107 x s).
Proof. exact (MK_COMB (@lem3472442 _90107 x) (@lem3472441 _90107 s)). Qed.
Lemma lem3472444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3472445 {_90107 : Type'} (x : _90107) (s : type686 _90107) : (term102 _90107 x s) = (term103 _90107 x s).
Proof. exact (MK_COMB (@lem3472444) (@lem3472443 _90107 x s)). Qed.
Lemma lem3472446 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term94 _90107 s x) = (term84 _90107 s x).
Proof. exact (eq_refl (term94 _90107 s x)). Qed.
Lemma lem3472447 {_90107 : Type'} (s : type686 _90107) (x : _90107) : ((term93 _90107 x s) = (term94 _90107 s x)) = ((term92 _90107 x s) = (term84 _90107 s x)).
Proof. exact (MK_COMB (@lem3472445 _90107 x s) (@lem3472446 _90107 s x)). Qed.
Lemma lem3472448 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term92 _90107 x s) = (term84 _90107 s x).
Proof. exact (EQ_MP (@lem3472447 _90107 s x) (@lem3472430 _90107 s x)). Qed.
Lemma lem3472455 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term91 _90107 x s) = (term84 _90107 s x).
Proof. exact (TRANS (@lem3472426 _90107 x s) (@lem3472448 _90107 s x)). Qed.
Lemma lem3472456 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3472457 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term104 _90107 x s) = (term105 _90107 s x).
Proof. exact (MK_COMB (@lem3472456) (@lem3472455 _90107 s x)). Qed.
Lemma lem3472458 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term33 _90107 x s) = (term106 _90107 s x).
Proof. exact (MK_COMB (@lem3472328 _90107 x) (@lem3472457 _90107 s x)). Qed.
Lemma lem3472460 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3472461 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term106 _90107 s x) = (term105 _90107 s x).
Proof. exact (@lem3472460 (term105 _90107 s x)). Qed.
Lemma lem3472468 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term33 _90107 x s) = (term105 _90107 s x).
Proof. exact (TRANS (@lem3472458 _90107 s x) (@lem3472461 _90107 s x)). Qed.
Lemma lem3472469 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term32 _90107 x s) = (term105 _90107 s x).
Proof. exact (TRANS (@lem3472321 _90107 x s) (@lem3472468 _90107 s x)). Qed.
Lemma lem3472470 {_90107 : Type'} (s : type686 _90107) (x : _90107) : ((term22 _90107 x s) = (term32 _90107 x s)) = ((term23 _90107 s x) = (term105 _90107 s x)).
Proof. exact (MK_COMB (@lem3472317 _90107 s x) (@lem3472469 _90107 s x)). Qed.
Lemma lem3472473 {_90107 : Type'} (s : type686 _90107) : (term107 _90107 s) = (term108 _90107 s).
Proof. exact (fun_ext (fun x : _90107 => @lem3472470 _90107 s x)). Qed.
Lemma lem3472474 {_90107 : Type'} : (@all _90107) = (@all _90107).
Proof. exact (eq_refl (@all _90107)). Qed.
Lemma lem3472475 {_90107 : Type'} (s : type686 _90107) : (term29 _90107 s) = (term109 _90107 s).
Proof. exact (MK_COMB (@lem3472474 _90107) (@lem3472473 _90107 s)). Qed.
Lemma lem3472480 {_90107 : Type'} (s : type686 _90107) : (term109 _90107 s) = (term29 _90107 s).
Proof. exact (SYM (@lem3472475 _90107 s)). Qed.
Lemma lem3472482 (p : Prop) : p = (term110 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3472483 {_90107 : Type'} (s : type686 _90107) : (term109 _90107 s) = (term111 _90107 s).
Proof. exact (@lem3472482 (term109 _90107 s)). Qed.
Lemma lem3472484 {_90107 : Type'} (s : type686 _90107) : (term111 _90107 s) = (term109 _90107 s).
Proof. exact (SYM (@lem3472483 _90107 s)). Qed.
Lemma lem3472485 {_90107 : Type'} (s : type686 _90107) (h1 : term112 _90107 s) : term112 _90107 s.
Proof. exact (h1). Qed.
Lemma lem3472488 {_90107 : Type'} (s : type686 _90107) (h1 : term111 _90107 s) : term111 _90107 s.
Proof. exact (h1). Qed.
Lemma lem3472489 {_90107 : Type'} (s : type686 _90107) : term113 _90107 s.
Proof. exact (fun h0 : term111 _90107 s => @lem3472488 _90107 s h0). Qed.
Lemma lem3472490 {_90107 : Type'} (s : type686 _90107) (h1 : term113 _90107 s) : term113 _90107 s.
Proof. exact (h1). Qed.
Lemma lem3472491 {_90107 : Type'} (s : type686 _90107) (h1 : term111 _90107 s) : term111 _90107 s.
Proof. exact (h1). Qed.
Lemma lem3472492 {_90107 : Type'} (s : type686 _90107) (h1 : term111 _90107 s) (h2 : term113 _90107 s) : term111 _90107 s.
Proof. exact (@lem3472490 _90107 s h2 (@lem3472491 _90107 s h1)). Qed.
Lemma lem3472493 {_90107 : Type'} (s : type686 _90107) (h1 : term111 _90107 s) : term114 _90107 s.
Proof. exact (fun h0 : term113 _90107 s => @lem3472492 _90107 s h1 h0). Qed.
Lemma lem3472494 {_90107 : Type'} (s : type686 _90107) (h1 : term113 _90107 s) : term113 _90107 s.
Proof. exact (h1). Qed.
Lemma lem3472495 {_90107 : Type'} (s : type686 _90107) (h1 : term111 _90107 s) (h2 : term113 _90107 s) : term111 _90107 s.
Proof. exact (@lem3472493 _90107 s h1 (@lem3472494 _90107 s h2)). Qed.
Lemma lem3472496 {_90107 : Type'} (s : type686 _90107) (h1 : term113 _90107 s) : term113 _90107 s.
Proof. exact (fun h0 : term111 _90107 s => @lem3472495 _90107 s h0 h1). Qed.
Lemma lem3472497 {_90107 : Type'} (s : type686 _90107) : term115 _90107 s.
Proof. exact (fun h0 : term113 _90107 s => @lem3472496 _90107 s h0). Qed.
Lemma lem3472500 {_90107 : Type'} (s : type686 _90107) : term113 _90107 s.
Proof. exact (@lem3472497 _90107 s (@lem3472489 _90107 s)). Qed.
Lemma lem3472501 {_90107 : Type'} (s : type686 _90107) : term113 _90107 s.
Proof. exact (@lem3472500 _90107 s). Qed.
Lemma lem3472507 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3472508 {_90107 : Type'} (s : type686 _90107) : (term111 _90107 s) = (term116 _90107 s).
Proof. exact (@lem3472507 (term112 _90107 s)). Qed.
Lemma lem3472510 (t : Prop) : (term117 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3472511 {_90107 : Type'} (s : type686 _90107) : (term116 _90107 s) = (term109 _90107 s).
Proof. exact (@lem3472510 (term109 _90107 s)). Qed.
Lemma lem3472516 {_90107 : Type'} (s : type686 _90107) : (term111 _90107 s) = (term109 _90107 s).
Proof. exact (TRANS (@lem3472508 _90107 s) (@lem3472511 _90107 s)). Qed.
Lemma lem3472573 {_90107 : Type'} : (term118 _90107) = (term119 _90107).
Proof. exact (fun_ext (fun s : type686 _90107 => @lem3472516 _90107 s)). Qed.
Lemma lem3472574 {_90107 : Type'} : (@all ((_90107 -> Prop) -> Prop)) = (@all ((_90107 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90107 -> Prop) -> Prop))). Qed.
Lemma lem3472583 {_90107 : Type'} : (term120 _90107) = (term121 _90107).
Proof. exact (MK_COMB (@lem3472574 _90107) (@lem3472573 _90107)). Qed.
Lemma lem3472590 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term82 _90107 s x t) = (term82 _90107 s x t).
Proof. exact (eq_refl (term82 _90107 s x t)). Qed.
Lemma lem3472591 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term83 _90107 s x) = (term83 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472590 _90107 s x t)). Qed.
Lemma lem3472592 {_90107 : Type'} : (@all (_90107 -> Prop)) = (@all (_90107 -> Prop)).
Proof. exact (eq_refl (@all (_90107 -> Prop))). Qed.
Lemma lem3472593 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term84 _90107 s x) = (term84 _90107 s x).
Proof. exact (MK_COMB (@lem3472592 _90107) (@lem3472591 _90107 s x)). Qed.
Lemma lem3472594 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3472595 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term105 _90107 s x) = (term105 _90107 s x).
Proof. exact (MK_COMB (@lem3472594) (@lem3472593 _90107 s x)). Qed.
Lemma lem3472600 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term122 _90107 s x t) = (term122 _90107 s x t).
Proof. exact (eq_refl (term122 _90107 s x t)). Qed.
Lemma lem3472601 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term123 _90107 s x) = (term123 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472600 _90107 s x t)). Qed.
Lemma lem3472602 {_90107 : Type'} : (@ex (_90107 -> Prop)) = (@ex (_90107 -> Prop)).
Proof. exact (eq_refl (@ex (_90107 -> Prop))). Qed.
Lemma lem3472603 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term23 _90107 s x) = (term23 _90107 s x).
Proof. exact (MK_COMB (@lem3472602 _90107) (@lem3472601 _90107 s x)). Qed.
Lemma lem3472604 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3472605 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term31 _90107 s x) = (term31 _90107 s x).
Proof. exact (MK_COMB (@lem3472604) (@lem3472603 _90107 s x)). Qed.
Lemma lem3472606 {_90107 : Type'} (s : type686 _90107) (x : _90107) : ((term23 _90107 s x) = (term105 _90107 s x)) = ((term23 _90107 s x) = (term105 _90107 s x)).
Proof. exact (MK_COMB (@lem3472605 _90107 s x) (@lem3472595 _90107 s x)). Qed.
Lemma lem3472607 {_90107 : Type'} (s : type686 _90107) : (term108 _90107 s) = (term108 _90107 s).
Proof. exact (fun_ext (fun x : _90107 => @lem3472606 _90107 s x)). Qed.
Lemma lem3472608 {_90107 : Type'} : (@all _90107) = (@all _90107).
Proof. exact (eq_refl (@all _90107)). Qed.
Lemma lem3472609 {_90107 : Type'} (s : type686 _90107) : (term109 _90107 s) = (term109 _90107 s).
Proof. exact (MK_COMB (@lem3472608 _90107) (@lem3472607 _90107 s)). Qed.
Lemma lem3472610 {_90107 : Type'} : (term119 _90107) = (term119 _90107).
Proof. exact (fun_ext (fun s : type686 _90107 => @lem3472609 _90107 s)). Qed.
Lemma lem3472611 {_90107 : Type'} : (@all ((_90107 -> Prop) -> Prop)) = (@all ((_90107 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90107 -> Prop) -> Prop))). Qed.
Lemma lem3472612 {_90107 : Type'} : (term121 _90107) = (term121 _90107).
Proof. exact (MK_COMB (@lem3472611 _90107) (@lem3472610 _90107)). Qed.
Lemma lem3472643 {_90107 : Type'} : (term120 _90107) = (term121 _90107).
Proof. exact (TRANS (@lem3472583 _90107) (@lem3472612 _90107)). Qed.
Lemma lem3472644 {_90107 : Type'} : (term121 _90107) = (term120 _90107).
Proof. exact (SYM (@lem3472643 _90107)). Qed.
Lemma lem3472646 (p : Prop) : p = (term110 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3472647 {_90107 : Type'} (s : type686 _90107) (x : _90107) : ((term23 _90107 s x) = (term105 _90107 s x)) = (term124 _90107 s x).
Proof. exact (@lem3472646 ((term23 _90107 s x) = (term105 _90107 s x))). Qed.
Lemma lem3472648 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term124 _90107 s x) = ((term23 _90107 s x) = (term105 _90107 s x)).
Proof. exact (SYM (@lem3472647 _90107 s x)). Qed.
Lemma lem3472649 {_90107 : Type'} (s : type686 _90107) (x : _90107) (h1 : term125 _90107 s x) : term125 _90107 s x.
Proof. exact (h1). Qed.
Lemma lem3472658 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term126 _90107 s x t) = (term127 _90107 s x t).
Proof. exact (@lem17045 (@IN (_90107 -> Prop) t s) (@IN _90107 x t)). Qed.
Lemma lem3472661 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term122 _90107 s x t) = (term122 _90107 s x t).
Proof. exact (eq_refl (term122 _90107 s x t)). Qed.
Lemma lem3472662 {_90107 : Type'} (P : type686 _90107) : (term128 _90107 P) = (term129 _90107 P).
Proof. exact (@lem18394 (_90107 -> Prop) P). Qed.
Lemma lem3472663 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term130 _90107 s x) = (term131 _90107 s x).
Proof. exact (@lem3472662 _90107 (term123 _90107 s x)). Qed.
Lemma lem3472664 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term132 _90107 s x t) = (term122 _90107 s x t).
Proof. exact (eq_refl (term132 _90107 s x t)). Qed.
Lemma lem3472665 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3472666 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term133 _90107 s x t) = (term126 _90107 s x t).
Proof. exact (MK_COMB (@lem3472665) (@lem3472664 _90107 s x t)). Qed.
Lemma lem3472667 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term133 _90107 s x t) = (term127 _90107 s x t).
Proof. exact (TRANS (@lem3472666 _90107 s x t) (@lem3472658 _90107 s x t)). Qed.
Lemma lem3472668 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term134 _90107 s x) = (term135 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472667 _90107 s x t)). Qed.
Lemma lem3472669 {_90107 : Type'} : (@all (_90107 -> Prop)) = (@all (_90107 -> Prop)).
Proof. exact (eq_refl (@all (_90107 -> Prop))). Qed.
Lemma lem3472670 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term131 _90107 s x) = (term136 _90107 s x).
Proof. exact (MK_COMB (@lem3472669 _90107) (@lem3472668 _90107 s x)). Qed.
Lemma lem3472671 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term130 _90107 s x) = (term136 _90107 s x).
Proof. exact (TRANS (@lem3472663 _90107 s x) (@lem3472670 _90107 s x)). Qed.
Lemma lem3472672 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term123 _90107 s x) = (term123 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472661 _90107 s x t)). Qed.
Lemma lem3472673 {_90107 : Type'} : (@ex (_90107 -> Prop)) = (@ex (_90107 -> Prop)).
Proof. exact (eq_refl (@ex (_90107 -> Prop))). Qed.
Lemma lem3472674 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term23 _90107 s x) = (term23 _90107 s x).
Proof. exact (MK_COMB (@lem3472673 _90107) (@lem3472672 _90107 s x)). Qed.
Lemma lem3472680 {_90107 : Type'} (x : _90107) (t : _90107 -> Prop) : (term137 _90107 x t) = (@IN _90107 x t).
Proof. exact (@lem16933 (@IN _90107 x t)). Qed.
Lemma lem3472682 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) : (term138 _90107 t s) = (term138 _90107 t s).
Proof. exact (eq_refl (term138 _90107 t s)). Qed.
Lemma lem3472683 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term139 _90107 s x t) = (term122 _90107 s x t).
Proof. exact (MK_COMB (@lem3472682 _90107 t s) (@lem3472680 _90107 x t)). Qed.
Lemma lem3472684 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term140 _90107 s x t) = (term139 _90107 s x t).
Proof. exact (@lem17362 (@IN (_90107 -> Prop) t s) (term80 _90107 x t)). Qed.
Lemma lem3472685 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term140 _90107 s x t) = (term122 _90107 s x t).
Proof. exact (TRANS (@lem3472684 _90107 s x t) (@lem3472683 _90107 s x t)). Qed.
Lemma lem3472690 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term82 _90107 s x t) = (term127 _90107 s x t).
Proof. exact (@lem17265 (@IN (_90107 -> Prop) t s) (term80 _90107 x t)). Qed.
Lemma lem3472691 {_90107 : Type'} (P : type686 _90107) : (term141 _90107 P) = (term142 _90107 P).
Proof. exact (@lem18392 (_90107 -> Prop) P). Qed.
Lemma lem3472692 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term105 _90107 s x) = (term143 _90107 s x).
Proof. exact (@lem3472691 _90107 (term83 _90107 s x)). Qed.
Lemma lem3472693 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term144 _90107 s x t) = (term82 _90107 s x t).
Proof. exact (eq_refl (term144 _90107 s x t)). Qed.
Lemma lem3472694 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3472695 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term145 _90107 s x t) = (term140 _90107 s x t).
Proof. exact (MK_COMB (@lem3472694) (@lem3472693 _90107 s x t)). Qed.
Lemma lem3472696 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term145 _90107 s x t) = (term122 _90107 s x t).
Proof. exact (TRANS (@lem3472695 _90107 s x t) (@lem3472685 _90107 s x t)). Qed.
Lemma lem3472697 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term146 _90107 s x) = (term123 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472696 _90107 s x t)). Qed.
Lemma lem3472698 {_90107 : Type'} : (@ex (_90107 -> Prop)) = (@ex (_90107 -> Prop)).
Proof. exact (eq_refl (@ex (_90107 -> Prop))). Qed.
Lemma lem3472699 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term143 _90107 s x) = (term23 _90107 s x).
Proof. exact (MK_COMB (@lem3472698 _90107) (@lem3472697 _90107 s x)). Qed.
Lemma lem3472700 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term105 _90107 s x) = (term23 _90107 s x).
Proof. exact (TRANS (@lem3472692 _90107 s x) (@lem3472699 _90107 s x)). Qed.
Lemma lem3472701 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term83 _90107 s x) = (term135 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472690 _90107 s x t)). Qed.
Lemma lem3472702 {_90107 : Type'} : (@all (_90107 -> Prop)) = (@all (_90107 -> Prop)).
Proof. exact (eq_refl (@all (_90107 -> Prop))). Qed.
Lemma lem3472703 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term84 _90107 s x) = (term136 _90107 s x).
Proof. exact (MK_COMB (@lem3472702 _90107) (@lem3472701 _90107 s x)). Qed.
Lemma lem3472704 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term147 _90107 s x) = (term84 _90107 s x).
Proof. exact (@lem16933 (term84 _90107 s x)). Qed.
Lemma lem3472705 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term147 _90107 s x) = (term136 _90107 s x).
Proof. exact (TRANS (@lem3472704 _90107 s x) (@lem3472703 _90107 s x)). Qed.
Lemma lem3472706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3472707 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term148 _90107 s x) = (term149 _90107 s x).
Proof. exact (MK_COMB (@lem3472706) (@lem3472671 _90107 s x)). Qed.
Lemma lem3472708 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term150 _90107 s x) = (term151 _90107 s x).
Proof. exact (MK_COMB (@lem3472707 _90107 s x) (@lem3472700 _90107 s x)). Qed.
Lemma lem3472709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3472710 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term152 _90107 s x) = (term152 _90107 s x).
Proof. exact (MK_COMB (@lem3472709) (@lem3472674 _90107 s x)). Qed.
Lemma lem3472711 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term153 _90107 s x) = (term154 _90107 s x).
Proof. exact (MK_COMB (@lem3472710 _90107 s x) (@lem3472705 _90107 s x)). Qed.
Lemma lem3472712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3472713 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term155 _90107 s x) = (term156 _90107 s x).
Proof. exact (MK_COMB (@lem3472712) (@lem3472711 _90107 s x)). Qed.
Lemma lem3472714 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term157 _90107 s x) = (term158 _90107 s x).
Proof. exact (MK_COMB (@lem3472713 _90107 s x) (@lem3472708 _90107 s x)). Qed.
Lemma lem3472715 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term125 _90107 s x) = (term157 _90107 s x).
Proof. exact (@lem17646 (term23 _90107 s x) (term105 _90107 s x)). Qed.
Lemma lem3472716 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term125 _90107 s x) = (term158 _90107 s x).
Proof. exact (TRANS (@lem3472715 _90107 s x) (@lem3472714 _90107 s x)). Qed.
Lemma lem3472911 {A : Type'} (P : A -> Prop) (Q : Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3472912 {_90107 : Type'} (P : type686 _90107) (Q : Prop) : (term161 _90107 P Q) = (term162 _90107 P Q).
Proof. exact (@lem3472911 (_90107 -> Prop) P Q). Qed.
Lemma lem3472913 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term163 _90107 s x) = (term164 _90107 s x).
Proof. exact (@lem3472912 _90107 (term123 _90107 s x) (term136 _90107 s x)). Qed.
Lemma lem3472914 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term132 _90107 s x t) = (term122 _90107 s x t).
Proof. exact (eq_refl (term132 _90107 s x t)). Qed.
Lemma lem3472915 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term165 _90107 s x) = (term123 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472914 _90107 s x t)). Qed.
Lemma lem3472916 {_90107 : Type'} : (@ex (_90107 -> Prop)) = (@ex (_90107 -> Prop)).
Proof. exact (eq_refl (@ex (_90107 -> Prop))). Qed.
Lemma lem3472917 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term166 _90107 s x) = (term23 _90107 s x).
Proof. exact (MK_COMB (@lem3472916 _90107) (@lem3472915 _90107 s x)). Qed.
Lemma lem3472918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3472919 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term167 _90107 s x) = (term152 _90107 s x).
Proof. exact (MK_COMB (@lem3472918) (@lem3472917 _90107 s x)). Qed.
Lemma lem3472920 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term136 _90107 s x) = (term136 _90107 s x).
Proof. exact (eq_refl (term136 _90107 s x)). Qed.
Lemma lem3472921 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term163 _90107 s x) = (term154 _90107 s x).
Proof. exact (MK_COMB (@lem3472919 _90107 s x) (@lem3472920 _90107 s x)). Qed.
Lemma lem3472922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3472923 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term168 _90107 s x) = (term169 _90107 s x).
Proof. exact (MK_COMB (@lem3472922) (@lem3472921 _90107 s x)). Qed.
Lemma lem3472924 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term132 _90107 s x t) = (term122 _90107 s x t).
Proof. exact (eq_refl (term132 _90107 s x t)). Qed.
Lemma lem3472925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3472926 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term170 _90107 s x t) = (term171 _90107 s x t).
Proof. exact (MK_COMB (@lem3472925) (@lem3472924 _90107 s x t)). Qed.
Lemma lem3472927 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term136 _90107 s x) = (term136 _90107 s x).
Proof. exact (eq_refl (term136 _90107 s x)). Qed.
Lemma lem3472928 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) : (term172 _90107 t s x) = (term173 _90107 t s x).
Proof. exact (MK_COMB (@lem3472926 _90107 s x t) (@lem3472927 _90107 s x)). Qed.
Lemma lem3472929 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term174 _90107 s x) = (term175 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472928 _90107 t s x)). Qed.
Lemma lem3472930 {_90107 : Type'} : (@ex (_90107 -> Prop)) = (@ex (_90107 -> Prop)).
Proof. exact (eq_refl (@ex (_90107 -> Prop))). Qed.
Lemma lem3472931 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term164 _90107 s x) = (term176 _90107 s x).
Proof. exact (MK_COMB (@lem3472930 _90107) (@lem3472929 _90107 s x)). Qed.
Lemma lem3472932 {_90107 : Type'} (s : type686 _90107) (x : _90107) : ((term163 _90107 s x) = (term164 _90107 s x)) = ((term154 _90107 s x) = (term176 _90107 s x)).
Proof. exact (MK_COMB (@lem3472923 _90107 s x) (@lem3472931 _90107 s x)). Qed.
Lemma lem3472933 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term154 _90107 s x) = (term176 _90107 s x).
Proof. exact (EQ_MP (@lem3472932 _90107 s x) (@lem3472913 _90107 s x)). Qed.
Lemma lem3472934 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3472935 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term156 _90107 s x) = (term177 _90107 s x).
Proof. exact (MK_COMB (@lem3472934) (@lem3472933 _90107 s x)). Qed.
Lemma lem3472937 {A : Type'} (P : Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3472938 {_90107 : Type'} (P : Prop) (Q : type686 _90107) : (term180 _90107 P Q) = (term181 _90107 P Q).
Proof. exact (@lem3472937 (_90107 -> Prop) P Q). Qed.
Lemma lem3472939 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term182 _90107 s x) = (term183 _90107 s x).
Proof. exact (@lem3472938 _90107 (term136 _90107 s x) (term123 _90107 s x)). Qed.
Lemma lem3472940 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term132 _90107 s x t) = (term122 _90107 s x t).
Proof. exact (eq_refl (term132 _90107 s x t)). Qed.
Lemma lem3472941 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term165 _90107 s x) = (term123 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472940 _90107 s x t)). Qed.
Lemma lem3472942 {_90107 : Type'} : (@ex (_90107 -> Prop)) = (@ex (_90107 -> Prop)).
Proof. exact (eq_refl (@ex (_90107 -> Prop))). Qed.
Lemma lem3472943 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term166 _90107 s x) = (term23 _90107 s x).
Proof. exact (MK_COMB (@lem3472942 _90107) (@lem3472941 _90107 s x)). Qed.
Lemma lem3472944 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term149 _90107 s x) = (term149 _90107 s x).
Proof. exact (eq_refl (term149 _90107 s x)). Qed.
Lemma lem3472945 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term182 _90107 s x) = (term151 _90107 s x).
Proof. exact (MK_COMB (@lem3472944 _90107 s x) (@lem3472943 _90107 s x)). Qed.
Lemma lem3472946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3472947 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term184 _90107 s x) = (term185 _90107 s x).
Proof. exact (MK_COMB (@lem3472946) (@lem3472945 _90107 s x)). Qed.
Lemma lem3472948 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term132 _90107 s x t) = (term122 _90107 s x t).
Proof. exact (eq_refl (term132 _90107 s x t)). Qed.
Lemma lem3472949 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term149 _90107 s x) = (term149 _90107 s x).
Proof. exact (eq_refl (term149 _90107 s x)). Qed.
Lemma lem3472950 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term186 _90107 s x t) = (term187 _90107 s x t).
Proof. exact (MK_COMB (@lem3472949 _90107 s x) (@lem3472948 _90107 s x t)). Qed.
Lemma lem3472951 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term188 _90107 s x) = (term189 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472950 _90107 s x t)). Qed.
Lemma lem3472952 {_90107 : Type'} : (@ex (_90107 -> Prop)) = (@ex (_90107 -> Prop)).
Proof. exact (eq_refl (@ex (_90107 -> Prop))). Qed.
Lemma lem3472953 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term183 _90107 s x) = (term190 _90107 s x).
Proof. exact (MK_COMB (@lem3472952 _90107) (@lem3472951 _90107 s x)). Qed.
Lemma lem3472954 {_90107 : Type'} (s : type686 _90107) (x : _90107) : ((term182 _90107 s x) = (term183 _90107 s x)) = ((term151 _90107 s x) = (term190 _90107 s x)).
Proof. exact (MK_COMB (@lem3472947 _90107 s x) (@lem3472953 _90107 s x)). Qed.
Lemma lem3472955 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term151 _90107 s x) = (term190 _90107 s x).
Proof. exact (EQ_MP (@lem3472954 _90107 s x) (@lem3472939 _90107 s x)). Qed.
Lemma lem3472956 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term158 _90107 s x) = (term191 _90107 s x).
Proof. exact (MK_COMB (@lem3472935 _90107 s x) (@lem3472955 _90107 s x)). Qed.
Lemma lem3472958 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3472959 {_90107 : Type'} (P : type686 _90107) (Q : type686 _90107) : (term194 _90107 P Q) = (term195 _90107 P Q).
Proof. exact (@lem3472958 (_90107 -> Prop) P Q). Qed.
Lemma lem3472960 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term196 _90107 s x) = (term197 _90107 s x).
Proof. exact (@lem3472959 _90107 (term175 _90107 s x) (term189 _90107 s x)). Qed.
Lemma lem3472961 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) : (term198 _90107 s x t) = (term173 _90107 t s x).
Proof. exact (eq_refl (term198 _90107 s x t)). Qed.
Lemma lem3472962 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term199 _90107 s x) = (term175 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472961 _90107 t s x)). Qed.
Lemma lem3472963 {_90107 : Type'} : (@ex (_90107 -> Prop)) = (@ex (_90107 -> Prop)).
Proof. exact (eq_refl (@ex (_90107 -> Prop))). Qed.
Lemma lem3472964 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term200 _90107 s x) = (term176 _90107 s x).
Proof. exact (MK_COMB (@lem3472963 _90107) (@lem3472962 _90107 s x)). Qed.
Lemma lem3472965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3472966 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term201 _90107 s x) = (term177 _90107 s x).
Proof. exact (MK_COMB (@lem3472965) (@lem3472964 _90107 s x)). Qed.
Lemma lem3472967 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term202 _90107 s x t) = (term187 _90107 s x t).
Proof. exact (eq_refl (term202 _90107 s x t)). Qed.
Lemma lem3472968 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term203 _90107 s x) = (term189 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472967 _90107 s x t)). Qed.
Lemma lem3472969 {_90107 : Type'} : (@ex (_90107 -> Prop)) = (@ex (_90107 -> Prop)).
Proof. exact (eq_refl (@ex (_90107 -> Prop))). Qed.
Lemma lem3472970 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term204 _90107 s x) = (term190 _90107 s x).
Proof. exact (MK_COMB (@lem3472969 _90107) (@lem3472968 _90107 s x)). Qed.
Lemma lem3472971 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term196 _90107 s x) = (term191 _90107 s x).
Proof. exact (MK_COMB (@lem3472966 _90107 s x) (@lem3472970 _90107 s x)). Qed.
Lemma lem3472972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3472973 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term205 _90107 s x) = (term206 _90107 s x).
Proof. exact (MK_COMB (@lem3472972) (@lem3472971 _90107 s x)). Qed.
Lemma lem3472974 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) : (term198 _90107 s x t) = (term173 _90107 t s x).
Proof. exact (eq_refl (term198 _90107 s x t)). Qed.
Lemma lem3472975 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3472976 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) : (term207 _90107 s x t) = (term208 _90107 t s x).
Proof. exact (MK_COMB (@lem3472975) (@lem3472974 _90107 t s x)). Qed.
Lemma lem3472977 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term202 _90107 s x t) = (term187 _90107 s x t).
Proof. exact (eq_refl (term202 _90107 s x t)). Qed.
Lemma lem3472978 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term209 _90107 s x t) = (term210 _90107 s x t).
Proof. exact (MK_COMB (@lem3472976 _90107 t s x) (@lem3472977 _90107 s x t)). Qed.
Lemma lem3472979 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term211 _90107 s x) = (term212 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3472978 _90107 s x t)). Qed.
Lemma lem3472980 {_90107 : Type'} : (@ex (_90107 -> Prop)) = (@ex (_90107 -> Prop)).
Proof. exact (eq_refl (@ex (_90107 -> Prop))). Qed.
Lemma lem3472981 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term197 _90107 s x) = (term213 _90107 s x).
Proof. exact (MK_COMB (@lem3472980 _90107) (@lem3472979 _90107 s x)). Qed.
Lemma lem3472982 {_90107 : Type'} (s : type686 _90107) (x : _90107) : ((term196 _90107 s x) = (term197 _90107 s x)) = ((term191 _90107 s x) = (term213 _90107 s x)).
Proof. exact (MK_COMB (@lem3472973 _90107 s x) (@lem3472981 _90107 s x)). Qed.
Lemma lem3472983 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term191 _90107 s x) = (term213 _90107 s x).
Proof. exact (EQ_MP (@lem3472982 _90107 s x) (@lem3472960 _90107 s x)). Qed.
Lemma lem3472985 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term158 _90107 s x) = (term213 _90107 s x).
Proof. exact (TRANS (@lem3472956 _90107 s x) (@lem3472983 _90107 s x)). Qed.
Lemma lem3472986 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term125 _90107 s x) = (term213 _90107 s x).
Proof. exact (TRANS (@lem3472716 _90107 s x) (@lem3472985 _90107 s x)). Qed.
Lemma lem3472987 {_90107 : Type'} (s : type686 _90107) (x : _90107) (h1 : term125 _90107 s x) : term213 _90107 s x.
Proof. exact (EQ_MP (@lem3472986 _90107 s x) (@lem3472649 _90107 s x h1)). Qed.
Lemma lem3472988 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term210 _90107 s x t) : term210 _90107 s x t.
Proof. exact (h1). Qed.
Lemma lem3473001 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term122 _90107 s x t) = (term122 _90107 s x t).
Proof. exact (eq_refl (term122 _90107 s x t)). Qed.
Lemma lem3473018 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term127 _90107 s x t) = (term127 _90107 s x t).
Proof. exact (eq_refl (term127 _90107 s x t)). Qed.
Lemma lem3473019 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term135 _90107 s x) = (term135 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3473018 _90107 s x t)). Qed.
Lemma lem3473020 {_90107 : Type'} : (@all (_90107 -> Prop)) = (@all (_90107 -> Prop)).
Proof. exact (eq_refl (@all (_90107 -> Prop))). Qed.
Lemma lem3473021 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term136 _90107 s x) = (term136 _90107 s x).
Proof. exact (MK_COMB (@lem3473020 _90107) (@lem3473019 _90107 s x)). Qed.
Lemma lem3473022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3473023 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term149 _90107 s x) = (term149 _90107 s x).
Proof. exact (MK_COMB (@lem3473022) (@lem3473021 _90107 s x)). Qed.
Lemma lem3473024 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term187 _90107 s x t) = (term187 _90107 s x t).
Proof. exact (MK_COMB (@lem3473023 _90107 s x) (@lem3473001 _90107 s x t)). Qed.
Lemma lem3473041 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term127 _90107 s x t) = (term127 _90107 s x t).
Proof. exact (eq_refl (term127 _90107 s x t)). Qed.
Lemma lem3473042 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term135 _90107 s x) = (term135 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3473041 _90107 s x t)). Qed.
Lemma lem3473043 {_90107 : Type'} : (@all (_90107 -> Prop)) = (@all (_90107 -> Prop)).
Proof. exact (eq_refl (@all (_90107 -> Prop))). Qed.
Lemma lem3473044 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term136 _90107 s x) = (term136 _90107 s x).
Proof. exact (MK_COMB (@lem3473043 _90107) (@lem3473042 _90107 s x)). Qed.
Lemma lem3473059 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term171 _90107 s x t) = (term171 _90107 s x t).
Proof. exact (eq_refl (term171 _90107 s x t)). Qed.
Lemma lem3473060 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) : (term173 _90107 t s x) = (term173 _90107 t s x).
Proof. exact (MK_COMB (@lem3473059 _90107 s x t) (@lem3473044 _90107 s x)). Qed.
Lemma lem3473061 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3473062 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) : (term208 _90107 t s x) = (term208 _90107 t s x).
Proof. exact (MK_COMB (@lem3473061) (@lem3473060 _90107 t s x)). Qed.
Lemma lem3473063 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term210 _90107 s x t) = (term210 _90107 s x t).
Proof. exact (MK_COMB (@lem3473062 _90107 t s x) (@lem3473024 _90107 s x t)). Qed.
Lemma lem3473064 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term210 _90107 s x t) : term210 _90107 s x t.
Proof. exact (EQ_MP (@lem3473063 _90107 s x t) (@lem3472988 _90107 s x t h1)). Qed.
Lemma lem3473065 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term173 _90107 t s x.
Proof. exact (h1). Qed.
Lemma lem3473066 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term187 _90107 s x t.
Proof. exact (h1). Qed.
Lemma lem3473067 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term136 _90107 s x.
Proof. exact (proj2 (@lem3473065 _90107 t s x h1)). Qed.
Lemma lem3473068 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term122 _90107 s x t.
Proof. exact (proj1 (@lem3473065 _90107 t s x h1)). Qed.
Lemma lem3473071 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term122 _90107 s x t.
Proof. exact (proj2 (@lem3473066 _90107 s x t h1)). Qed.
Lemma lem3473072 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term136 _90107 s x.
Proof. exact (proj1 (@lem3473066 _90107 s x t h1)). Qed.
Lemma lem3473082 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term127 _90107 s x t) = (term127 _90107 s x t).
Proof. exact (eq_refl (term127 _90107 s x t)). Qed.
Lemma lem3473083 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term135 _90107 s x) = (term135 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3473082 _90107 s x t)). Qed.
Lemma lem3473084 {_90107 : Type'} : (@all (_90107 -> Prop)) = (@all (_90107 -> Prop)).
Proof. exact (eq_refl (@all (_90107 -> Prop))). Qed.
Lemma lem3473086 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term136 _90107 s x) = (term136 _90107 s x).
Proof. exact (MK_COMB (@lem3473084 _90107) (@lem3473083 _90107 s x)). Qed.
Lemma lem3473087 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term136 _90107 s x.
Proof. exact (EQ_MP (@lem3473086 _90107 s x) (@lem3473067 _90107 t s x h1)). Qed.
Lemma lem3473103 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) : (term127 _90107 s x t) = (term127 _90107 s x t).
Proof. exact (eq_refl (term127 _90107 s x t)). Qed.
Lemma lem3473104 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term135 _90107 s x) = (term135 _90107 s x).
Proof. exact (fun_ext (fun t : _90107 -> Prop => @lem3473103 _90107 s x t)). Qed.
Lemma lem3473105 {_90107 : Type'} : (@all (_90107 -> Prop)) = (@all (_90107 -> Prop)).
Proof. exact (eq_refl (@all (_90107 -> Prop))). Qed.
Lemma lem3473107 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term136 _90107 s x) = (term136 _90107 s x).
Proof. exact (MK_COMB (@lem3473105 _90107) (@lem3473104 _90107 s x)). Qed.
Lemma lem3473108 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term136 _90107 s x.
Proof. exact (EQ_MP (@lem3473107 _90107 s x) (@lem3473072 _90107 s x t h1)). Qed.
Lemma lem3473117 {_90107 : Type'} (_36671 : _90107 -> Prop) (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term214 _90107 s x _36671.
Proof. exact (@lem3473087 _90107 t s x h1 _36671). Qed.
Lemma lem3473118 {_90107 : Type'} (s : type686 _90107) (x : _90107) (_36671 : _90107 -> Prop) : (term214 _90107 s x _36671) = (term127 _90107 s x _36671).
Proof. exact (eq_refl (term214 _90107 s x _36671)). Qed.
Lemma lem3473120 {_90107 : Type'} (_36672 : _90107 -> Prop) (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term214 _90107 s x _36672.
Proof. exact (@lem3473108 _90107 s x t h1 _36672). Qed.
Lemma lem3473121 {_90107 : Type'} (s : type686 _90107) (x : _90107) (_36672 : _90107 -> Prop) : (term214 _90107 s x _36672) = (term127 _90107 s x _36672).
Proof. exact (eq_refl (term214 _90107 s x _36672)). Qed.
Lemma lem3473128 {_90107 : Type'} (_36671 : _90107 -> Prop) (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term127 _90107 s x _36671.
Proof. exact (EQ_MP (@lem3473118 _90107 s x _36671) (@lem3473117 _90107 _36671 t s x h1)). Qed.
Lemma lem3473138 {_90107 : Type'} (_36672 : _90107 -> Prop) (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term127 _90107 s x _36672.
Proof. exact (EQ_MP (@lem3473121 _90107 s x _36672) (@lem3473120 _90107 _36672 s x t h1)). Qed.
Lemma lem3473144 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : @IN (_90107 -> Prop) t s.
Proof. exact (proj1 (@lem3473068 _90107 t s x h1)). Qed.
Lemma lem3473145 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term215 _90107 t s.
Proof. exact (fun h0 : term216 _90107 t s => @lem3473144 _90107 t s x h1). Qed.
Lemma lem3473147 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3473148 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) : (term215 _90107 t s) = (@IN (_90107 -> Prop) t s).
Proof. exact (@lem3473147 (@IN (_90107 -> Prop) t s)). Qed.
Lemma lem3473149 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : @IN (_90107 -> Prop) t s.
Proof. exact (EQ_MP (@lem3473148 _90107 t s) (@lem3473145 _90107 t s x h1)). Qed.
Lemma lem3473151 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : @IN _90107 x t.
Proof. exact (proj2 (@lem3473068 _90107 t s x h1)). Qed.
Lemma lem3473152 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term218 _90107 x t.
Proof. exact (fun h0 : term80 _90107 x t => @lem3473151 _90107 t s x h1). Qed.
Lemma lem3473154 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3473155 {_90107 : Type'} (x : _90107) (t : _90107 -> Prop) : (term218 _90107 x t) = (@IN _90107 x t).
Proof. exact (@lem3473154 (@IN _90107 x t)). Qed.
Lemma lem3473156 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : @IN _90107 x t.
Proof. exact (EQ_MP (@lem3473155 _90107 x t) (@lem3473152 _90107 t s x h1)). Qed.
Lemma lem3473158 (a : Prop) (b : Prop) : (term219 a b) = (term220 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3473159 {_90107 : Type'} (s : type686 _90107) (x : _90107) (_36671 : _90107 -> Prop) : (term127 _90107 s x _36671) = (term126 _90107 s x _36671).
Proof. exact (@lem3473158 (@IN (_90107 -> Prop) _36671 s) (@IN _90107 x _36671)). Qed.
Lemma lem3473161 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3473162 {_90107 : Type'} (s : type686 _90107) (x : _90107) (_36671 : _90107 -> Prop) : (term126 _90107 s x _36671) = (term221 _90107 s x _36671).
Proof. exact (@lem3473161 (term122 _90107 s x _36671)). Qed.
Lemma lem3473163 {_90107 : Type'} (s : type686 _90107) (x : _90107) (_36671 : _90107 -> Prop) : (term127 _90107 s x _36671) = (term221 _90107 s x _36671).
Proof. exact (TRANS (@lem3473159 _90107 s x _36671) (@lem3473162 _90107 s x _36671)). Qed.
Lemma lem3473165 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term122 _90107 s x t.
Proof. exact (conj (@lem3473149 _90107 t s x h1) (@lem3473156 _90107 t s x h1)). Qed.
Lemma lem3473167 {_90107 : Type'} (_36671 : _90107 -> Prop) (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term221 _90107 s x _36671.
Proof. exact (EQ_MP (@lem3473163 _90107 s x _36671) (@lem3473128 _90107 _36671 t s x h1)). Qed.
Lemma lem3473168 {_90107 : Type'} (_36671 : _90107 -> Prop) (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term221 _90107 s x _36671.
Proof. exact (@lem3473167 _90107 _36671 t s x h1). Qed.
Lemma lem3473169 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term221 _90107 s x t.
Proof. exact (@lem3473168 _90107 t t s x h1). Qed.
Lemma lem3473172 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : False.
Proof. exact (@lem3473169 _90107 t s x h1 (@lem3473165 _90107 t s x h1)). Qed.
Lemma lem3473173 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : term222.
Proof. exact (fun h0 : ~ False => @lem3473172 _90107 t s x h1). Qed.
Lemma lem3473175 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3473176 : term222 = False.
Proof. exact (@lem3473175 False). Qed.
Lemma lem3473177 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) (x : _90107) (h1 : term173 _90107 t s x) : False.
Proof. exact (EQ_MP (@lem3473176) (@lem3473173 _90107 t s x h1)). Qed.
Lemma lem3473179 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : @IN (_90107 -> Prop) t s.
Proof. exact (proj1 (@lem3473071 _90107 s x t h1)). Qed.
Lemma lem3473180 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term215 _90107 t s.
Proof. exact (fun h0 : term216 _90107 t s => @lem3473179 _90107 s x t h1). Qed.
Lemma lem3473182 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3473183 {_90107 : Type'} (t : _90107 -> Prop) (s : type686 _90107) : (term215 _90107 t s) = (@IN (_90107 -> Prop) t s).
Proof. exact (@lem3473182 (@IN (_90107 -> Prop) t s)). Qed.
Lemma lem3473184 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : @IN (_90107 -> Prop) t s.
Proof. exact (EQ_MP (@lem3473183 _90107 t s) (@lem3473180 _90107 s x t h1)). Qed.
Lemma lem3473186 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : @IN _90107 x t.
Proof. exact (proj2 (@lem3473071 _90107 s x t h1)). Qed.
Lemma lem3473187 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term218 _90107 x t.
Proof. exact (fun h0 : term80 _90107 x t => @lem3473186 _90107 s x t h1). Qed.
Lemma lem3473189 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3473190 {_90107 : Type'} (x : _90107) (t : _90107 -> Prop) : (term218 _90107 x t) = (@IN _90107 x t).
Proof. exact (@lem3473189 (@IN _90107 x t)). Qed.
Lemma lem3473191 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : @IN _90107 x t.
Proof. exact (EQ_MP (@lem3473190 _90107 x t) (@lem3473187 _90107 s x t h1)). Qed.
Lemma lem3473193 (a : Prop) (b : Prop) : (term219 a b) = (term220 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3473194 {_90107 : Type'} (s : type686 _90107) (x : _90107) (_36672 : _90107 -> Prop) : (term127 _90107 s x _36672) = (term126 _90107 s x _36672).
Proof. exact (@lem3473193 (@IN (_90107 -> Prop) _36672 s) (@IN _90107 x _36672)). Qed.
Lemma lem3473196 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3473197 {_90107 : Type'} (s : type686 _90107) (x : _90107) (_36672 : _90107 -> Prop) : (term126 _90107 s x _36672) = (term221 _90107 s x _36672).
Proof. exact (@lem3473196 (term122 _90107 s x _36672)). Qed.
Lemma lem3473198 {_90107 : Type'} (s : type686 _90107) (x : _90107) (_36672 : _90107 -> Prop) : (term127 _90107 s x _36672) = (term221 _90107 s x _36672).
Proof. exact (TRANS (@lem3473194 _90107 s x _36672) (@lem3473197 _90107 s x _36672)). Qed.
Lemma lem3473200 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term122 _90107 s x t.
Proof. exact (conj (@lem3473184 _90107 s x t h1) (@lem3473191 _90107 s x t h1)). Qed.
Lemma lem3473202 {_90107 : Type'} (_36672 : _90107 -> Prop) (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term221 _90107 s x _36672.
Proof. exact (EQ_MP (@lem3473198 _90107 s x _36672) (@lem3473138 _90107 _36672 s x t h1)). Qed.
Lemma lem3473203 {_90107 : Type'} (_36672 : _90107 -> Prop) (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term221 _90107 s x _36672.
Proof. exact (@lem3473202 _90107 _36672 s x t h1). Qed.
Lemma lem3473204 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term221 _90107 s x t.
Proof. exact (@lem3473203 _90107 t s x t h1). Qed.
Lemma lem3473207 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : False.
Proof. exact (@lem3473204 _90107 s x t h1 (@lem3473200 _90107 s x t h1)). Qed.
Lemma lem3473208 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : term222.
Proof. exact (fun h0 : ~ False => @lem3473207 _90107 s x t h1). Qed.
Lemma lem3473210 (p : Prop) : (term217 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3473211 : term222 = False.
Proof. exact (@lem3473210 False). Qed.
Lemma lem3473212 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term187 _90107 s x t) : False.
Proof. exact (EQ_MP (@lem3473211) (@lem3473208 _90107 s x t h1)). Qed.
Lemma lem3473213 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term210 _90107 s x t) : False.
Proof. exact (or_elim (@lem3473064 _90107 s x t h1) (fun h0 : term173 _90107 t s x => @lem3473177 _90107 t s x h0) (fun h0 : term187 _90107 s x t => @lem3473212 _90107 s x t h0)). Qed.
Lemma lem3473214 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term210 _90107 s x t) : (term210 _90107 s x t) = False.
Proof. exact (prop_ext (fun h2 : term210 _90107 s x t => @lem3473213 _90107 s x t h1) (fun h2 : False => @lem3473064 _90107 s x t h1)). Qed.
Lemma lem3473215 {_90107 : Type'} (s : type686 _90107) (x : _90107) (t : _90107 -> Prop) (h1 : term210 _90107 s x t) : False.
Proof. exact (EQ_MP (@lem3473214 _90107 s x t h1) (@lem3473064 _90107 s x t h1)). Qed.
Lemma lem3473216 {_90107 : Type'} (s : type686 _90107) (x : _90107) (h1 : term125 _90107 s x) : False.
Proof. exact (ex_elim (@lem3472987 _90107 s x h1) (fun t : _90107 -> Prop => fun h0 : term212 _90107 s x t => @lem3473215 _90107 s x t h0)). Qed.
Lemma lem3473217 {_90107 : Type'} (s : type686 _90107) (x : _90107) (h1 : term125 _90107 s x) : (term125 _90107 s x) = False.
Proof. exact (prop_ext (fun h2 : term125 _90107 s x => @lem3473216 _90107 s x h1) (fun h2 : False => @lem3472649 _90107 s x h1)). Qed.
Lemma lem3473218 {_90107 : Type'} (s : type686 _90107) (x : _90107) (h1 : term125 _90107 s x) : False.
Proof. exact (EQ_MP (@lem3473217 _90107 s x h1) (@lem3472649 _90107 s x h1)). Qed.
Lemma lem3473219 {_90107 : Type'} (s : type686 _90107) (x : _90107) : term124 _90107 s x.
Proof. exact (fun h0 : term125 _90107 s x => @lem3473218 _90107 s x h0). Qed.
Lemma lem3473220 {_90107 : Type'} (s : type686 _90107) (x : _90107) : (term23 _90107 s x) = (term105 _90107 s x).
Proof. exact (EQ_MP (@lem3472648 _90107 s x) (@lem3473219 _90107 s x)). Qed.
Lemma lem3473225 {_90107 : Type'} (s : type686 _90107) : term109 _90107 s.
Proof. exact (fun x : _90107 => @lem3473220 _90107 s x). Qed.
Lemma lem3473230 {_90107 : Type'} : term121 _90107.
Proof. exact (fun s : type686 _90107 => @lem3473225 _90107 s). Qed.
Lemma lem3473231 {_90107 : Type'} : term120 _90107.
Proof. exact (EQ_MP (@lem3472644 _90107) (@lem3473230 _90107)). Qed.
Lemma lem3473232 {_90107 : Type'} (s : type686 _90107) : term223 _90107 s.
Proof. exact (@lem3473231 _90107 s). Qed.
Lemma lem3473233 {_90107 : Type'} (s : type686 _90107) : (term223 _90107 s) = (term111 _90107 s).
Proof. exact (eq_refl (term223 _90107 s)). Qed.
Lemma lem3473234 {_90107 : Type'} (s : type686 _90107) : term111 _90107 s.
Proof. exact (EQ_MP (@lem3473233 _90107 s) (@lem3473232 _90107 s)). Qed.
Lemma lem3473236 {_90107 : Type'} (s : type686 _90107) : term111 _90107 s.
Proof. exact (@lem3472501 _90107 s (@lem3473234 _90107 s)). Qed.
Lemma lem3473237 {_90107 : Type'} (s : type686 _90107) (h1 : term112 _90107 s) : False.
Proof. exact (@lem3473236 _90107 s (@lem3472485 _90107 s h1)). Qed.
Lemma lem3473238 {_90107 : Type'} (s : type686 _90107) (h1 : term112 _90107 s) : (term112 _90107 s) = False.
Proof. exact (prop_ext (fun h2 : term112 _90107 s => @lem3473237 _90107 s h1) (fun h2 : False => @lem3472485 _90107 s h1)). Qed.
Lemma lem3473239 {_90107 : Type'} (s : type686 _90107) (h1 : term112 _90107 s) : False.
Proof. exact (EQ_MP (@lem3473238 _90107 s h1) (@lem3472485 _90107 s h1)). Qed.
Lemma lem3473240 {_90107 : Type'} (s : type686 _90107) : term111 _90107 s.
Proof. exact (fun h0 : term112 _90107 s => @lem3473239 _90107 s h0). Qed.
Lemma lem3473241 {_90107 : Type'} (s : type686 _90107) : term109 _90107 s.
Proof. exact (EQ_MP (@lem3472484 _90107 s) (@lem3473240 _90107 s)). Qed.
Lemma lem3473242 {_90107 : Type'} (s : type686 _90107) : term29 _90107 s.
Proof. exact (EQ_MP (@lem3472480 _90107 s) (@lem3473241 _90107 s)). Qed.
Lemma lem3473243 {_90107 : Type'} (s : type686 _90107) : (@UNIONS _90107 s) = (term28 _90107 s).
Proof. exact (EQ_MP (@lem3472300 _90107 s) (@lem3473242 _90107 s)). Qed.
Lemma lem3473248 {_90107 : Type'} : term224 _90107.
Proof. exact (fun s : type686 _90107 => @lem3473243 _90107 s). Qed.
