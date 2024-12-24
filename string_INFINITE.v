Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import string_INFINITE_term_abbrevs.
Require Import CONTRAPOS_THM_spec.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import FINITE_IMAGE_spec.
Require Import INFINITE_spec.
Require Import IN_IMAGE_spec.
Require Import IN_UNIV_spec.
Require Import LENGTH_REPLICATE_spec.
Require Import num_INFINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1157_spec.
Require Import thm16474_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1843_spec.
Require Import thm1856_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem4629205 {A B : Type'} (y : B) : term0 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4629206 {A B : Type'} (y : B) : (term0 A B y) = (term1 A B y).
Proof. exact (eq_refl (term0 A B y)). Qed.
Lemma lem4629207 {A B : Type'} (y : B) : term1 A B y.
Proof. exact (EQ_MP (@lem4629206 A B y) (@lem4629205 A B y)). Qed.
Lemma lem4629208 {A B : Type'} (y : B) (s : A -> Prop) : term2 A B y s.
Proof. exact (@lem4629207 A B y s). Qed.
Lemma lem4629209 {A B : Type'} (y : B) (s : A -> Prop) : (term2 A B y s) = (term3 A B y s).
Proof. exact (eq_refl (term2 A B y s)). Qed.
Lemma lem4629210 {A B : Type'} (y : B) (s : A -> Prop) : term3 A B y s.
Proof. exact (EQ_MP (@lem4629209 A B y s) (@lem4629208 A B y s)). Qed.
Lemma lem4629211 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term4 A B y s f.
Proof. exact (@lem4629210 A B y s f). Qed.
Lemma lem4629212 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term4 A B y s f) = ((term5 A B y f s) = (term6 A B y f s)).
Proof. exact (eq_refl (term4 A B y s f)). Qed.
Lemma lem4629214 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem4629215 {A : Type'} (x : A) : (term7 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem4629216 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem4629215 A x) (@lem4629214 A x)). Qed.
Lemma lem4629217 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem4629219 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4629220 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (eq_refl (term8 A s)). Qed.
Lemma lem4629221 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem4629220 A s) (@lem4629219 A s)). Qed.
Lemma lem4629222 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term10 A s t.
Proof. exact (@lem4629221 A s t). Qed.
Lemma lem4629223 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term10 A s t) = ((s = t) = (term11 A s t)).
Proof. exact (eq_refl (term10 A s t)). Qed.
Lemma lem4629225 (a : Prop) (b : Prop) (h1 : term12 a b) : term12 a b.
Proof. exact (h1). Qed.
Lemma lem4629226 (a : Prop) (b : Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem4629227 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term12 a b) : a -> b.
Proof. exact (@lem4629225 a b h2 (@lem4629226 a b h1)). Qed.
Lemma lem4629228 (a : Prop) (b : Prop) (h1 : a = b) : term13 a b.
Proof. exact (fun h0 : term12 a b => @lem4629227 a b h1 h0). Qed.
Lemma lem4629229 (a : Prop) (b : Prop) (h1 : term12 a b) : term12 a b.
Proof. exact (h1). Qed.
Lemma lem4629230 (a : Prop) (b : Prop) (h1 : a = b) (h2 : term12 a b) : a -> b.
Proof. exact (@lem4629228 a b h1 (@lem4629229 a b h2)). Qed.
Lemma lem4629231 (a : Prop) (b : Prop) (h1 : term12 a b) : term12 a b.
Proof. exact (fun h0 : a = b => @lem4629230 a b h0 h1). Qed.
Lemma lem4629232 (a : Prop) (b : Prop) : term14 a b.
Proof. exact (fun h0 : term12 a b => @lem4629231 a b h0). Qed.
Lemma lem4629234 {A B : Type'} (h1 : term15 A B) : term15 A B.
Proof. exact (h1). Qed.
Lemma lem4629235 {A B : Type'} (f : A -> B) (h1 : term15 A B) : term16 A B f.
Proof. exact (@lem4629234 A B h1 f). Qed.
Lemma lem4629236 {A B : Type'} (f : A -> B) : (term16 A B f) = (term17 A B f).
Proof. exact (eq_refl (term16 A B f)). Qed.
Lemma lem4629237 {A B : Type'} (f : A -> B) (h1 : term15 A B) : term17 A B f.
Proof. exact (EQ_MP (@lem4629236 A B f) (@lem4629235 A B f h1)). Qed.
Lemma lem4629238 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term15 A B) : term18 A B f s.
Proof. exact (@lem4629237 A B f h1 s). Qed.
Lemma lem4629239 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term18 A B f s) = (term19 A B f s).
Proof. exact (eq_refl (term18 A B f s)). Qed.
Lemma lem4629240 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term15 A B) : term19 A B f s.
Proof. exact (EQ_MP (@lem4629239 A B f s) (@lem4629238 A B f s h1)). Qed.
Lemma lem4629241 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4629242 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term15 A B) (h2 : @FINITE A s) : term20 A B f s.
Proof. exact (@lem4629240 A B f s h1 (@lem4629241 A s h2)). Qed.
Lemma lem4629243 {A B : Type'} (s : A -> Prop) (h1 : term15 A B) (h2 : @FINITE A s) : term21 A B s.
Proof. exact (fun f : A -> B => @lem4629242 A B f s h1 h2). Qed.
Lemma lem4629244 {A B : Type'} (s : A -> Prop) (h1 : term15 A B) : term22 A B s.
Proof. exact (fun h0 : @FINITE A s => @lem4629243 A B s h1 h0). Qed.
Lemma lem4629245 {A B : Type'} (h1 : term15 A B) : term23 A B.
Proof. exact (fun s : A -> Prop => @lem4629244 A B s h1). Qed.
Lemma lem4629246 {A B : Type'} : term24 A B.
Proof. exact (fun h0 : term15 A B => @lem4629245 A B h0). Qed.
Lemma lem4629247 {A B : Type'} : term23 A B.
Proof. exact (@lem4629246 A B (@lem3615104 A B)). Qed.
Lemma lem4629248 {A B : Type'} (s : A -> Prop) : term25 A B s.
Proof. exact (@lem4629247 A B s). Qed.
Lemma lem4629249 {A B : Type'} (s : A -> Prop) : (term25 A B s) = (term22 A B s).
Proof. exact (eq_refl (term25 A B s)). Qed.
Lemma lem4629251 (t1 : Prop) : term26 t1.
Proof. exact (@lem10414 t1). Qed.
Lemma lem4629252 (t1 : Prop) : (term26 t1) = (term27 t1).
Proof. exact (eq_refl (term26 t1)). Qed.
Lemma lem4629253 (t1 : Prop) : term27 t1.
Proof. exact (EQ_MP (@lem4629252 t1) (@lem4629251 t1)). Qed.
Lemma lem4629254 (t1 : Prop) (t2 : Prop) : term28 t1 t2.
Proof. exact (@lem4629253 t1 t2). Qed.
Lemma lem4629255 (t2 : Prop) (t1 : Prop) : (term28 t1 t2) = ((term29 t1 t2) = (t2 -> t1)).
Proof. exact (eq_refl (term28 t1 t2)). Qed.
Lemma lem4629257 {A : Type'} (s : A -> Prop) : term30 A s.
Proof. exact (@lem3198543 A s). Qed.
Lemma lem4629258 {A : Type'} (s : A -> Prop) : (term30 A s) = ((@INFINITE A s) = (term31 A s)).
Proof. exact (eq_refl (term30 A s)). Qed.
Lemma lem4629263 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term31 A s).
Proof. exact (EQ_MP (@lem4629258 A s) (@lem4629257 A s)). Qed.
Lemma lem4629264 (s : nat -> Prop) : (@INFINITE nat s) = (term32 s).
Proof. exact (@lem4629263 nat s). Qed.
Lemma lem4629265 : (@INFINITE nat (@UNIV nat)) = term33.
Proof. exact (@lem4629264 (@UNIV nat)). Qed.
Lemma lem4629266 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4629267 : term34 = term35.
Proof. exact (MK_COMB (@lem4629266) (@lem4629265)). Qed.
Lemma lem4629269 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term31 A s).
Proof. exact (EQ_MP (@lem4629258 A s) (@lem4629257 A s)). Qed.
Lemma lem4629270 (s : type1156) : (@INFINITE (list Ascii.ascii) s) = (term36 s).
Proof. exact (@lem4629269 (list Ascii.ascii) s). Qed.
Lemma lem4629271 : (@INFINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii))) = term37.
Proof. exact (@lem4629270 (@UNIV (list Ascii.ascii))). Qed.
Lemma lem4629272 : term38 = term39.
Proof. exact (MK_COMB (@lem4629267) (@lem4629271)). Qed.
Lemma lem4629274 (t2 : Prop) (t1 : Prop) : (term29 t1 t2) = (t2 -> t1).
Proof. exact (EQ_MP (@lem4629255 t2 t1) (@lem4629254 t1 t2)). Qed.
Lemma lem4629275 : term39 = term40.
Proof. exact (@lem4629274 (@FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii))) (@FINITE nat (@UNIV nat))). Qed.
Lemma lem4629278 : term38 = term40.
Proof. exact (TRANS (@lem4629272) (@lem4629275)). Qed.
Lemma lem4629279 : term40 = term38.
Proof. exact (SYM (@lem4629278)). Qed.
Lemma lem4629280 (h1 : @FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii))) : @FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii)).
Proof. exact (h1). Qed.
Lemma lem4629282 {A B : Type'} (s : A -> Prop) : term22 A B s.
Proof. exact (EQ_MP (@lem4629249 A B s) (@lem4629248 A B s)). Qed.
Lemma lem4629283 {B : Type'} (s : type1156) : term41 B s.
Proof. exact (@lem4629282 (list Ascii.ascii) B s). Qed.
Lemma lem4629284 {B : Type'} : term42 B.
Proof. exact (@lem4629283 B (@UNIV (list Ascii.ascii))). Qed.
Lemma lem4629285 {B : Type'} (h1 : @FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii))) : term43 B.
Proof. exact (@lem4629284 B (@lem4629280 h1)). Qed.
Lemma lem4629286 (h1 : @FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii))) : term44.
Proof. exact (@lem4629285 nat h1). Qed.
Lemma lem4629287 (h1 : @FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii))) : term45.
Proof. exact (@lem4629286 h1 (@List.length Ascii.ascii)). Qed.
Lemma lem4629288 : term45 = term46.
Proof. exact (eq_refl term45). Qed.
Lemma lem4629289 (h1 : @FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii))) : term46.
Proof. exact (EQ_MP (@lem4629288) (@lem4629287 h1)). Qed.
Lemma lem4629291 (a : Prop) (b : Prop) : term12 a b.
Proof. exact (@lem4629232 a b (@lem1157 a b)). Qed.
Lemma lem4629292 : term47.
Proof. exact (@lem4629291 term46 (@FINITE nat (@UNIV nat))). Qed.
Lemma lem4629293 : (@FINITE nat) = (@FINITE nat).
Proof. exact (eq_refl (@FINITE nat)). Qed.
Lemma lem4629297 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term11 A s t).
Proof. exact (EQ_MP (@lem4629223 A s t) (@lem4629222 A s t)). Qed.
Lemma lem4629298 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term48 s t).
Proof. exact (@lem4629297 nat s t). Qed.
Lemma lem4629299 : ((@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii))) = (@UNIV nat)) = term49.
Proof. exact (@lem4629298 (@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii))) (@UNIV nat)). Qed.
Lemma lem4629309 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term6 A B y f s).
Proof. exact (EQ_MP (@lem4629212 A B y f s) (@lem4629211 A B y s f)). Qed.
Lemma lem4629310 (y : nat) (f : type1157) (s : type1156) : (term50 y f s) = (term51 y f s).
Proof. exact (@lem4629309 (list Ascii.ascii) nat y f s). Qed.
Lemma lem4629311 (x : nat) : (term52 x) = (term53 x).
Proof. exact (@lem4629310 x (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii))). Qed.
Lemma lem4629323 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4629217 A x) (@lem4629216 A x)). Qed.
Lemma lem4629324 (x : list Ascii.ascii) : (@IN (list Ascii.ascii) x (@UNIV (list Ascii.ascii))) = True.
Proof. exact (@lem4629323 (list Ascii.ascii) x). Qed.
Lemma lem4629325 (x : nat) (x' : list Ascii.ascii) : (term54 x x') = (term54 x x').
Proof. exact (eq_refl (term54 x x')). Qed.
Lemma lem4629326 (x : nat) (x' : list Ascii.ascii) : (term55 x x') = (term56 x x').
Proof. exact (MK_COMB (@lem4629325 x x') (@lem4629324 x')). Qed.
Lemma lem4629328 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4629329 (x : nat) (x' : list Ascii.ascii) : (term56 x x') = (x = (@List.length Ascii.ascii x')).
Proof. exact (@lem4629328 (x = (@List.length Ascii.ascii x'))). Qed.
Lemma lem4629334 (x : nat) (x' : list Ascii.ascii) : (term55 x x') = (x = (@List.length Ascii.ascii x')).
Proof. exact (TRANS (@lem4629326 x x') (@lem4629329 x x')). Qed.
Lemma lem4629335 (x : nat) : (term57 x) = (term58 x).
Proof. exact (fun_ext (fun x' : list Ascii.ascii => @lem4629334 x x')). Qed.
Lemma lem4629336 : (@ex (list Ascii.ascii)) = (@ex (list Ascii.ascii)).
Proof. exact (eq_refl (@ex (list Ascii.ascii))). Qed.
Lemma lem4629337 (x : nat) : (term53 x) = (term59 x).
Proof. exact (MK_COMB (@lem4629336) (@lem4629335 x)). Qed.
Lemma lem4629342 (x : nat) : (term52 x) = (term59 x).
Proof. exact (TRANS (@lem4629311 x) (@lem4629337 x)). Qed.
Lemma lem4629343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4629344 (x : nat) : (term60 x) = (term61 x).
Proof. exact (MK_COMB (@lem4629343) (@lem4629342 x)). Qed.
Lemma lem4629346 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4629217 A x) (@lem4629216 A x)). Qed.
Lemma lem4629347 (x : nat) : (@IN nat x (@UNIV nat)) = True.
Proof. exact (@lem4629346 nat x). Qed.
Lemma lem4629348 (x : nat) : ((term52 x) = (@IN nat x (@UNIV nat))) = ((term59 x) = True).
Proof. exact (MK_COMB (@lem4629344 x) (@lem4629347 x)). Qed.
Lemma lem4629350 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem4629351 (x : nat) : ((term59 x) = True) = (term59 x).
Proof. exact (@lem4629350 (term59 x)). Qed.
Lemma lem4629360 (x : nat) : ((term52 x) = (@IN nat x (@UNIV nat))) = (term59 x).
Proof. exact (TRANS (@lem4629348 x) (@lem4629351 x)). Qed.
Lemma lem4629361 : term62 = term63.
Proof. exact (fun_ext (fun x : nat => @lem4629360 x)). Qed.
Lemma lem4629362 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4629363 : term49 = term64.
Proof. exact (MK_COMB (@lem4629362) (@lem4629361)). Qed.
Lemma lem4629368 : ((@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii))) = (@UNIV nat)) = term64.
Proof. exact (TRANS (@lem4629299) (@lem4629363)). Qed.
Lemma lem4629369 : term64 = ((@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii))) = (@UNIV nat)).
Proof. exact (SYM (@lem4629368)). Qed.
Lemma lem4629371 (p : Prop) : p = (term65 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4629372 : term64 = term66.
Proof. exact (@lem4629371 term64). Qed.
Lemma lem4629373 : term66 = term64.
Proof. exact (SYM (@lem4629372)). Qed.
Lemma lem4629374 (h1 : term67) : term67.
Proof. exact (h1). Qed.
Lemma lem4629375 : term68.
Proof. exact (@lem1138200 Ascii.ascii). Qed.
Lemma lem4629378 {_26795 : Type'} (h1 : term69 _26795) : term69 _26795.
Proof. exact (h1). Qed.
Lemma lem4629379 {_26795 : Type'} : term70 _26795.
Proof. exact (fun h0 : term69 _26795 => @lem4629378 _26795 h0). Qed.
Lemma lem4629380 {_26795 : Type'} (h1 : term70 _26795) : term70 _26795.
Proof. exact (h1). Qed.
Lemma lem4629381 {_26795 : Type'} (h1 : term69 _26795) : term69 _26795.
Proof. exact (h1). Qed.
Lemma lem4629382 {_26795 : Type'} (h1 : term69 _26795) (h2 : term70 _26795) : term69 _26795.
Proof. exact (@lem4629380 _26795 h2 (@lem4629381 _26795 h1)). Qed.
Lemma lem4629383 {_26795 : Type'} (h1 : term69 _26795) : term71 _26795.
Proof. exact (fun h0 : term70 _26795 => @lem4629382 _26795 h1 h0). Qed.
Lemma lem4629384 {_26795 : Type'} (h1 : term70 _26795) : term70 _26795.
Proof. exact (h1). Qed.
Lemma lem4629385 {_26795 : Type'} (h1 : term69 _26795) (h2 : term70 _26795) : term69 _26795.
Proof. exact (@lem4629383 _26795 h1 (@lem4629384 _26795 h2)). Qed.
Lemma lem4629386 {_26795 : Type'} (h1 : term70 _26795) : term70 _26795.
Proof. exact (fun h0 : term69 _26795 => @lem4629385 _26795 h0 h1). Qed.
Lemma lem4629387 {_26795 : Type'} : term72 _26795.
Proof. exact (fun h0 : term70 _26795 => @lem4629386 _26795 h0). Qed.
Lemma lem4629390 {_26795 : Type'} : term70 _26795.
Proof. exact (@lem4629387 _26795 (@lem4629379 _26795)). Qed.
Lemma lem4629391 {_26795 : Type'} : term70 _26795.
Proof. exact (@lem4629390 _26795). Qed.
Lemma lem4629413 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4629414 : term73 = term74.
Proof. exact (@lem4629413 term68). Qed.
Lemma lem4629423 {_26795 : Type'} : (term75 _26795) = (term75 _26795).
Proof. exact (eq_refl (term75 _26795)). Qed.
Lemma lem4629424 {_26795 : Type'} : (term76 _26795) = (term77 _26795).
Proof. exact (MK_COMB (@lem4629423 _26795) (@lem4629414)). Qed.
Lemma lem4629427 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem4629434 {_26795 : Type'} : (term69 _26795) = (term79 _26795).
Proof. exact (MK_COMB (@lem4629427) (@lem4629424 _26795)). Qed.
Lemma lem4629435 (x : Ascii.ascii) (n : nat) : ((term80 n x) = n) = ((term80 n x) = n).
Proof. exact (eq_refl ((term80 n x) = n)). Qed.
Lemma lem4629436 (n : nat) : (term81 n) = (term81 n).
Proof. exact (fun_ext (fun x : Ascii.ascii => @lem4629435 x n)). Qed.
Lemma lem4629437 : (@all Ascii.ascii) = (@all Ascii.ascii).
Proof. exact (eq_refl (@all Ascii.ascii)). Qed.
Lemma lem4629438 (n : nat) : (term82 n) = (term82 n).
Proof. exact (MK_COMB (@lem4629437) (@lem4629436 n)). Qed.
Lemma lem4629439 : term83 = term83.
Proof. exact (fun_ext (fun n : nat => @lem4629438 n)). Qed.
Lemma lem4629440 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4629441 : term68 = term68.
Proof. exact (MK_COMB (@lem4629440) (@lem4629439)). Qed.
Lemma lem4629442 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4629443 : term74 = term74.
Proof. exact (MK_COMB (@lem4629442) (@lem4629441)). Qed.
Lemma lem4629444 {_26795 : Type'} (x : _26795) (n : nat) : ((term84 _26795 n x) = n) = ((term84 _26795 n x) = n).
Proof. exact (eq_refl ((term84 _26795 n x) = n)). Qed.
Lemma lem4629445 {_26795 : Type'} (n : nat) : (term85 _26795 n) = (term85 _26795 n).
Proof. exact (fun_ext (fun x : _26795 => @lem4629444 _26795 x n)). Qed.
Lemma lem4629446 {_26795 : Type'} : (@all _26795) = (@all _26795).
Proof. exact (eq_refl (@all _26795)). Qed.
Lemma lem4629447 {_26795 : Type'} (n : nat) : (term86 _26795 n) = (term86 _26795 n).
Proof. exact (MK_COMB (@lem4629446 _26795) (@lem4629445 _26795 n)). Qed.
Lemma lem4629448 {_26795 : Type'} : (term87 _26795) = (term87 _26795).
Proof. exact (fun_ext (fun n : nat => @lem4629447 _26795 n)). Qed.
Lemma lem4629449 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4629450 {_26795 : Type'} : (term88 _26795) = (term88 _26795).
Proof. exact (MK_COMB (@lem4629449) (@lem4629448 _26795)). Qed.
Lemma lem4629451 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4629452 {_26795 : Type'} : (term75 _26795) = (term75 _26795).
Proof. exact (MK_COMB (@lem4629451) (@lem4629450 _26795)). Qed.
Lemma lem4629453 {_26795 : Type'} : (term77 _26795) = (term77 _26795).
Proof. exact (MK_COMB (@lem4629452 _26795) (@lem4629443)). Qed.
Lemma lem4629454 (x : nat) (x' : list Ascii.ascii) : (x = (@List.length Ascii.ascii x')) = (x = (@List.length Ascii.ascii x')).
Proof. exact (eq_refl (x = (@List.length Ascii.ascii x'))). Qed.
Lemma lem4629455 (x : nat) : (term58 x) = (term58 x).
Proof. exact (fun_ext (fun x' : list Ascii.ascii => @lem4629454 x x')). Qed.
Lemma lem4629456 : (@ex (list Ascii.ascii)) = (@ex (list Ascii.ascii)).
Proof. exact (eq_refl (@ex (list Ascii.ascii))). Qed.
Lemma lem4629457 (x : nat) : (term59 x) = (term59 x).
Proof. exact (MK_COMB (@lem4629456) (@lem4629455 x)). Qed.
Lemma lem4629458 : term63 = term63.
Proof. exact (fun_ext (fun x : nat => @lem4629457 x)). Qed.
Lemma lem4629459 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4629460 : term64 = term64.
Proof. exact (MK_COMB (@lem4629459) (@lem4629458)). Qed.
Lemma lem4629461 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4629462 : term67 = term67.
Proof. exact (MK_COMB (@lem4629461) (@lem4629460)). Qed.
Lemma lem4629463 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4629464 : term78 = term78.
Proof. exact (MK_COMB (@lem4629463) (@lem4629462)). Qed.
Lemma lem4629465 {_26795 : Type'} : (term79 _26795) = (term79 _26795).
Proof. exact (MK_COMB (@lem4629464) (@lem4629453 _26795)). Qed.
Lemma lem4629508 {_26795 : Type'} : (term69 _26795) = (term79 _26795).
Proof. exact (TRANS (@lem4629434 _26795) (@lem4629465 _26795)). Qed.
Lemma lem4629509 {_26795 : Type'} : (term79 _26795) = (term69 _26795).
Proof. exact (SYM (@lem4629508 _26795)). Qed.
Lemma lem4629510 (h1 : term67) : term67.
Proof. exact (h1). Qed.
Lemma lem4629512 (h1 : term68) : term68.
Proof. exact (h1). Qed.
Lemma lem4629514 (P : type1156) : (term89 P) = (term90 P).
Proof. exact (@lem18394 (list Ascii.ascii) P). Qed.
Lemma lem4629515 (x : nat) : (term91 x) = (term92 x).
Proof. exact (@lem4629514 (term58 x)). Qed.
Lemma lem4629516 (x : nat) (x' : list Ascii.ascii) : (term93 x x') = (x = (@List.length Ascii.ascii x')).
Proof. exact (eq_refl (term93 x x')). Qed.
Lemma lem4629517 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4629519 (x : nat) (x' : list Ascii.ascii) : (term94 x x') = (term95 x x').
Proof. exact (MK_COMB (@lem4629517) (@lem4629516 x x')). Qed.
Lemma lem4629520 (x : nat) : (term96 x) = (term97 x).
Proof. exact (fun_ext (fun x' : list Ascii.ascii => @lem4629519 x x')). Qed.
Lemma lem4629521 : (@all (list Ascii.ascii)) = (@all (list Ascii.ascii)).
Proof. exact (eq_refl (@all (list Ascii.ascii))). Qed.
Lemma lem4629522 (x : nat) : (term92 x) = (term98 x).
Proof. exact (MK_COMB (@lem4629521) (@lem4629520 x)). Qed.
Lemma lem4629523 (x : nat) : (term91 x) = (term98 x).
Proof. exact (TRANS (@lem4629515 x) (@lem4629522 x)). Qed.
Lemma lem4629524 (P : nat -> Prop) : (term99 P) = (term100 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem4629525 : term67 = term101.
Proof. exact (@lem4629524 term63). Qed.
Lemma lem4629526 (x : nat) : (term102 x) = (term59 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem4629527 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4629528 (x : nat) : (term103 x) = (term91 x).
Proof. exact (MK_COMB (@lem4629527) (@lem4629526 x)). Qed.
Lemma lem4629529 (x : nat) : (term103 x) = (term98 x).
Proof. exact (TRANS (@lem4629528 x) (@lem4629523 x)). Qed.
Lemma lem4629530 : term104 = term105.
Proof. exact (fun_ext (fun x : nat => @lem4629529 x)). Qed.
Lemma lem4629531 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4629532 : term101 = term106.
Proof. exact (MK_COMB (@lem4629531) (@lem4629530)). Qed.
Lemma lem4629545 : term67 = term106.
Proof. exact (TRANS (@lem4629525) (@lem4629532)). Qed.
Lemma lem4629546 (h1 : term67) : term106.
Proof. exact (EQ_MP (@lem4629545) (@lem4629510 h1)). Qed.
Lemma lem4629567 (x : Ascii.ascii) (n : nat) : ((term80 n x) = n) = ((term80 n x) = n).
Proof. exact (eq_refl ((term80 n x) = n)). Qed.
Lemma lem4629568 (n : nat) : (term81 n) = (term81 n).
Proof. exact (fun_ext (fun x : Ascii.ascii => @lem4629567 x n)). Qed.
Lemma lem4629569 : (@all Ascii.ascii) = (@all Ascii.ascii).
Proof. exact (eq_refl (@all Ascii.ascii)). Qed.
Lemma lem4629570 (n : nat) : (term82 n) = (term82 n).
Proof. exact (MK_COMB (@lem4629569) (@lem4629568 n)). Qed.
Lemma lem4629571 : term83 = term83.
Proof. exact (fun_ext (fun n : nat => @lem4629570 n)). Qed.
Lemma lem4629572 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4629585 : term68 = term68.
Proof. exact (MK_COMB (@lem4629572) (@lem4629571)). Qed.
Lemma lem4629586 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem4629585) (@lem4629512 h1)). Qed.
Lemma lem4629587 (x : nat) (h1 : term98 x) : term98 x.
Proof. exact (h1). Qed.
Lemma lem4629616 (x : Ascii.ascii) (n : nat) : ((term80 n x) = n) = ((term80 n x) = n).
Proof. exact (eq_refl ((term80 n x) = n)). Qed.
Lemma lem4629617 (n : nat) : (term81 n) = (term81 n).
Proof. exact (fun_ext (fun x : Ascii.ascii => @lem4629616 x n)). Qed.
Lemma lem4629618 : (@all Ascii.ascii) = (@all Ascii.ascii).
Proof. exact (eq_refl (@all Ascii.ascii)). Qed.
Lemma lem4629619 (n : nat) : (term82 n) = (term82 n).
Proof. exact (MK_COMB (@lem4629618) (@lem4629617 n)). Qed.
Lemma lem4629620 : term83 = term83.
Proof. exact (fun_ext (fun n : nat => @lem4629619 n)). Qed.
Lemma lem4629621 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4629622 : term68 = term68.
Proof. exact (MK_COMB (@lem4629621) (@lem4629620)). Qed.
Lemma lem4629623 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem4629622) (@lem4629586 h1)). Qed.
Lemma lem4629632 (x : nat) (x' : list Ascii.ascii) : (term95 x x') = (term95 x x').
Proof. exact (eq_refl (term95 x x')). Qed.
Lemma lem4629633 (x : nat) : (term97 x) = (term97 x).
Proof. exact (fun_ext (fun x' : list Ascii.ascii => @lem4629632 x x')). Qed.
Lemma lem4629634 : (@all (list Ascii.ascii)) = (@all (list Ascii.ascii)).
Proof. exact (eq_refl (@all (list Ascii.ascii))). Qed.
Lemma lem4629635 (x : nat) : (term98 x) = (term98 x).
Proof. exact (MK_COMB (@lem4629634) (@lem4629633 x)). Qed.
Lemma lem4629636 (x : nat) (h1 : term98 x) : term98 x.
Proof. exact (EQ_MP (@lem4629635 x) (@lem4629587 x h1)). Qed.
Lemma lem4629648 (x : Ascii.ascii) (n : nat) : ((term80 n x) = n) = ((term80 n x) = n).
Proof. exact (eq_refl ((term80 n x) = n)). Qed.
Lemma lem4629649 (n : nat) : (term81 n) = (term81 n).
Proof. exact (fun_ext (fun x : Ascii.ascii => @lem4629648 x n)). Qed.
Lemma lem4629650 : (@all Ascii.ascii) = (@all Ascii.ascii).
Proof. exact (eq_refl (@all Ascii.ascii)). Qed.
Lemma lem4629651 (n : nat) : (term82 n) = (term82 n).
Proof. exact (MK_COMB (@lem4629650) (@lem4629649 n)). Qed.
Lemma lem4629652 : term83 = term83.
Proof. exact (fun_ext (fun n : nat => @lem4629651 n)). Qed.
Lemma lem4629653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4629655 : term68 = term68.
Proof. exact (MK_COMB (@lem4629653) (@lem4629652)). Qed.
Lemma lem4629656 (h1 : term68) : term68.
Proof. exact (EQ_MP (@lem4629655) (@lem4629623 h1)). Qed.
Lemma lem4629658 (x : nat) (x' : list Ascii.ascii) : (term95 x x') = (term95 x x').
Proof. exact (eq_refl (term95 x x')). Qed.
Lemma lem4629659 (x : nat) : (term97 x) = (term97 x).
Proof. exact (fun_ext (fun x' : list Ascii.ascii => @lem4629658 x x')). Qed.
Lemma lem4629660 : (@all (list Ascii.ascii)) = (@all (list Ascii.ascii)).
Proof. exact (eq_refl (@all (list Ascii.ascii))). Qed.
Lemma lem4629662 (x : nat) : (term98 x) = (term98 x).
Proof. exact (MK_COMB (@lem4629660) (@lem4629659 x)). Qed.
Lemma lem4629663 (x : nat) (h1 : term98 x) : term98 x.
Proof. exact (EQ_MP (@lem4629662 x) (@lem4629636 x h1)). Qed.
Lemma lem4629670 (_55605 : nat) (h1 : term68) : term107 _55605.
Proof. exact (@lem4629656 h1 _55605). Qed.
Lemma lem4629671 (_55605 : nat) : (term107 _55605) = (term82 _55605).
Proof. exact (eq_refl (term107 _55605)). Qed.
Lemma lem4629672 (_55605 : nat) (h1 : term68) : term82 _55605.
Proof. exact (EQ_MP (@lem4629671 _55605) (@lem4629670 _55605 h1)). Qed.
Lemma lem4629673 (_55605 : nat) (_55606 : Ascii.ascii) (h1 : term68) : term108 _55605 _55606.
Proof. exact (@lem4629672 _55605 h1 _55606). Qed.
Lemma lem4629674 (_55606 : Ascii.ascii) (_55605 : nat) : (term108 _55605 _55606) = ((term80 _55605 _55606) = _55605).
Proof. exact (eq_refl (term108 _55605 _55606)). Qed.
Lemma lem4629676 (_55607 : list Ascii.ascii) (x : nat) (h1 : term98 x) : term109 x _55607.
Proof. exact (@lem4629663 x h1 _55607). Qed.
Lemma lem4629677 (x : nat) (_55607 : list Ascii.ascii) : (term109 x _55607) = (term95 x _55607).
Proof. exact (eq_refl (term109 x _55607)). Qed.
Lemma lem4629684 (_55607 : list Ascii.ascii) (x : nat) (h1 : term98 x) : term95 x _55607.
Proof. exact (EQ_MP (@lem4629677 x _55607) (@lem4629676 _55607 x h1)). Qed.
Lemma lem4629732 (x : nat) (y : nat) (z : nat) : term110 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem4629742 (_55606 : Ascii.ascii) (_55605 : nat) (h1 : term68) : (term80 _55605 _55606) = _55605.
Proof. exact (EQ_MP (@lem4629674 _55606 _55605) (@lem4629673 _55605 _55606 h1)). Qed.
Lemma lem4629743 (_55620 : Ascii.ascii) (x : nat) (h1 : term68) : (term80 x _55620) = x.
Proof. exact (@lem4629742 _55620 x h1). Qed.
Lemma lem4629744 (_55620 : Ascii.ascii) (x : nat) (h1 : term68) : term111 _55620 x.
Proof. exact (fun h0 : term112 _55620 x => @lem4629743 _55620 x h1). Qed.
Lemma lem4629746 (p : Prop) : (term113 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4629747 (_55620 : Ascii.ascii) (x : nat) : (term111 _55620 x) = ((term80 x _55620) = x).
Proof. exact (@lem4629746 ((term80 x _55620) = x)). Qed.
Lemma lem4629748 (_55620 : Ascii.ascii) (x : nat) (h1 : term68) : (term80 x _55620) = x.
Proof. exact (EQ_MP (@lem4629747 _55620 x) (@lem4629744 _55620 x h1)). Qed.
Lemma lem4629750 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4629751 (x : nat) (_55620 : Ascii.ascii) : (term80 x _55620) = (term80 x _55620).
Proof. exact (@lem4629750 (term80 x _55620)). Qed.
Lemma lem4629752 (x : nat) (_55620 : Ascii.ascii) : term114 x _55620.
Proof. exact (fun h0 : term115 x _55620 => @lem4629751 x _55620). Qed.
Lemma lem4629754 (p : Prop) : (term113 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4629755 (x : nat) (_55620 : Ascii.ascii) : (term114 x _55620) = ((term80 x _55620) = (term80 x _55620)).
Proof. exact (@lem4629754 ((term80 x _55620) = (term80 x _55620))). Qed.
Lemma lem4629756 (x : nat) (_55620 : Ascii.ascii) : (term80 x _55620) = (term80 x _55620).
Proof. exact (EQ_MP (@lem4629755 x _55620) (@lem4629752 x _55620)). Qed.
Lemma lem4629774 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4629775 (y : nat) (x : nat) (z : nat) : (term116 x y z) = (term117 y x z).
Proof. exact (@lem4629774 (y = z) (term118 x z)). Qed.
Lemma lem4629785 (x : nat) (y : nat) : (term119 x y) = (term119 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem4629786 (y : nat) (x : nat) (z : nat) : (term110 x y z) = (term120 y x z).
Proof. exact (MK_COMB (@lem4629785 x y) (@lem4629775 y x z)). Qed.
Lemma lem4629790 (q : Prop) (p : Prop) (r : Prop) : (term121 p q r) = (term121 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4629791 (y : nat) (x : nat) (z : nat) : (term120 y x z) = (term122 y x z).
Proof. exact (@lem4629790 (y = z) (term118 x y) (term118 x z)). Qed.
Lemma lem4629813 (y : nat) (x : nat) (z : nat) : (term110 x y z) = (term122 y x z).
Proof. exact (TRANS (@lem4629786 y x z) (@lem4629791 y x z)). Qed.
Lemma lem4629814 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4629815 (y : nat) (x : nat) (z : nat) : (term123 x y z) = (term124 y x z).
Proof. exact (MK_COMB (@lem4629814) (@lem4629813 y x z)). Qed.
Lemma lem4629837 (y : nat) (x : nat) (z : nat) : (term122 y x z) = (term122 y x z).
Proof. exact (eq_refl (term122 y x z)). Qed.
Lemma lem4629838 (y : nat) (x : nat) (z : nat) : ((term110 x y z) = (term122 y x z)) = ((term122 y x z) = (term122 y x z)).
Proof. exact (MK_COMB (@lem4629815 y x z) (@lem4629837 y x z)). Qed.
Lemma lem4629840 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4629841 (x : Prop) : (x = x) = True.
Proof. exact (@lem4629840 Prop x). Qed.
Lemma lem4629842 (y : nat) (x : nat) (z : nat) : ((term122 y x z) = (term122 y x z)) = True.
Proof. exact (@lem4629841 (term122 y x z)). Qed.
Lemma lem4629843 (y : nat) (x : nat) (z : nat) : ((term110 x y z) = (term122 y x z)) = True.
Proof. exact (TRANS (@lem4629838 y x z) (@lem4629842 y x z)). Qed.
Lemma lem4629844 (y : nat) (x : nat) (z : nat) : True = ((term110 x y z) = (term122 y x z)).
Proof. exact (SYM (@lem4629843 y x z)). Qed.
Lemma lem4629845 (y : nat) (x : nat) (z : nat) : (term110 x y z) = (term122 y x z).
Proof. exact (EQ_MP (@lem4629844 y x z) (@lem0)). Qed.
Lemma lem4629846 (y : nat) (x : nat) (z : nat) : term122 y x z.
Proof. exact (EQ_MP (@lem4629845 y x z) (@lem4629732 x y z)). Qed.
Lemma lem4629848 (b : Prop) (a : Prop) : (a \/ b) = (term125 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4629849 (x : nat) (y : nat) (z : nat) : (term122 y x z) = (term126 x y z).
Proof. exact (@lem4629848 (term127 y x z) (y = z)). Qed.
Lemma lem4629851 (a : Prop) (b : Prop) : (term128 a b) = (term129 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4629852 (y : nat) (x : nat) (z : nat) : (term130 y x z) = (term131 y x z).
Proof. exact (@lem4629851 (term118 x y) (term118 x z)). Qed.
Lemma lem4629854 (a : Prop) : (term132 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4629855 (x : nat) (y : nat) : (term133 x y) = (x = y).
Proof. exact (@lem4629854 (x = y)). Qed.
Lemma lem4629856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4629857 (x : nat) (y : nat) : (term134 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem4629856) (@lem4629855 x y)). Qed.
Lemma lem4629859 (a : Prop) : (term132 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4629860 (x : nat) (z : nat) : (term133 x z) = (x = z).
Proof. exact (@lem4629859 (x = z)). Qed.
Lemma lem4629861 (y : nat) (x : nat) (z : nat) : (term131 y x z) = (term136 y x z).
Proof. exact (MK_COMB (@lem4629857 x y) (@lem4629860 x z)). Qed.
Lemma lem4629862 (y : nat) (x : nat) (z : nat) : (term130 y x z) = (term136 y x z).
Proof. exact (TRANS (@lem4629852 y x z) (@lem4629861 y x z)). Qed.
Lemma lem4629863 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4629864 (y : nat) (x : nat) (z : nat) : (term137 y x z) = (term138 y x z).
Proof. exact (MK_COMB (@lem4629863) (@lem4629862 y x z)). Qed.
Lemma lem4629865 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4629866 (x : nat) (y : nat) (z : nat) : (term126 x y z) = (term139 x y z).
Proof. exact (MK_COMB (@lem4629864 y x z) (@lem4629865 y z)). Qed.
Lemma lem4629867 (x : nat) (y : nat) (z : nat) : (term122 y x z) = (term139 x y z).
Proof. exact (TRANS (@lem4629849 x y z) (@lem4629866 x y z)). Qed.
Lemma lem4629869 (x : nat) (_55620 : Ascii.ascii) (h1 : term68) : term140 x _55620.
Proof. exact (conj (@lem4629748 _55620 x h1) (@lem4629756 x _55620)). Qed.
Lemma lem4629871 (x : nat) (y : nat) (z : nat) : term139 x y z.
Proof. exact (EQ_MP (@lem4629867 x y z) (@lem4629846 y x z)). Qed.
Lemma lem4629872 (x : nat) (_55620 : Ascii.ascii) : term141 x _55620.
Proof. exact (@lem4629871 (term80 x _55620) x (term80 x _55620)). Qed.
Lemma lem4629875 (x : nat) (_55620 : Ascii.ascii) (h1 : term68) : x = (term80 x _55620).
Proof. exact (@lem4629872 x _55620 (@lem4629869 x _55620 h1)). Qed.
Lemma lem4629876 (x : nat) (_55620 : Ascii.ascii) (h1 : term68) : term142 x _55620.
Proof. exact (fun h0 : term143 x _55620 => @lem4629875 x _55620 h1). Qed.
Lemma lem4629878 (p : Prop) : (term113 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4629879 (x : nat) (_55620 : Ascii.ascii) : (term142 x _55620) = (x = (term80 x _55620)).
Proof. exact (@lem4629878 (x = (term80 x _55620))). Qed.
Lemma lem4629880 (x : nat) (_55620 : Ascii.ascii) (h1 : term68) : x = (term80 x _55620).
Proof. exact (EQ_MP (@lem4629879 x _55620) (@lem4629876 x _55620 h1)). Qed.
Lemma lem4629883 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4629885 (x : nat) (_55607 : list Ascii.ascii) : (term95 x _55607) = (term144 x _55607).
Proof. exact (@lem4629883 (x = (@List.length Ascii.ascii _55607))). Qed.
Lemma lem4629888 (_55607 : list Ascii.ascii) (x : nat) (h1 : term98 x) : term144 x _55607.
Proof. exact (EQ_MP (@lem4629885 x _55607) (@lem4629684 _55607 x h1)). Qed.
Lemma lem4629889 (_55620 : Ascii.ascii) (x : nat) (h1 : term98 x) : term145 x _55620.
Proof. exact (@lem4629888 (@repeat_with_perm_args Ascii.ascii x _55620) x h1). Qed.
Lemma lem4629892 (x : nat) (h1 : term98 x) (h2 : term68) : False.
Proof. exact (@lem4629889 (@el Ascii.ascii) x h1 (@lem4629880 x (@el Ascii.ascii) h2)). Qed.
Lemma lem4629893 (x : nat) (h1 : term98 x) (h2 : term68) : term146.
Proof. exact (fun h0 : ~ False => @lem4629892 x h1 h2). Qed.
Lemma lem4629895 (p : Prop) : (term113 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4629896 : term146 = False.
Proof. exact (@lem4629895 False). Qed.
Lemma lem4629897 (x : nat) (h1 : term98 x) (h2 : term68) : False.
Proof. exact (EQ_MP (@lem4629896) (@lem4629893 x h1 h2)). Qed.
Lemma lem4629898 (x : nat) (h1 : term98 x) (h2 : term68) : (term98 x) = False.
Proof. exact (prop_ext (fun h3 : term98 x => @lem4629897 x h1 h2) (fun h3 : False => @lem4629663 x h1)). Qed.
Lemma lem4629899 (x : nat) (h1 : term98 x) (h2 : term68) : False.
Proof. exact (EQ_MP (@lem4629898 x h1 h2) (@lem4629663 x h1)). Qed.
Lemma lem4629900 (x : nat) (h1 : term98 x) (h2 : term68) : term68 = False.
Proof. exact (prop_ext (fun h3 : term68 => @lem4629899 x h1 h2) (fun h3 : False => @lem4629656 h2)). Qed.
Lemma lem4629901 (x : nat) (h1 : term98 x) (h2 : term68) : False.
Proof. exact (EQ_MP (@lem4629900 x h1 h2) (@lem4629656 h2)). Qed.
Lemma lem4629902 (x : nat) (h1 : term98 x) (h2 : term68) : (term98 x) = False.
Proof. exact (prop_ext (fun h3 : term98 x => @lem4629901 x h1 h2) (fun h3 : False => @lem4629636 x h1)). Qed.
Lemma lem4629903 (x : nat) (h1 : term98 x) (h2 : term68) : False.
Proof. exact (EQ_MP (@lem4629902 x h1 h2) (@lem4629636 x h1)). Qed.
Lemma lem4629904 (x : nat) (h1 : term98 x) (h2 : term68) : term68 = False.
Proof. exact (prop_ext (fun h3 : term68 => @lem4629903 x h1 h2) (fun h3 : False => @lem4629623 h2)). Qed.
Lemma lem4629905 (x : nat) (h1 : term98 x) (h2 : term68) : False.
Proof. exact (EQ_MP (@lem4629904 x h1 h2) (@lem4629623 h2)). Qed.
Lemma lem4629906 (h1 : term68) (h2 : term67) : False.
Proof. exact (ex_elim (@lem4629546 h2) (fun x : nat => fun h0 : term105 x => @lem4629905 x h0 h1)). Qed.
Lemma lem4629907 (h1 : term68) (h2 : term67) : term68 = False.
Proof. exact (prop_ext (fun h3 : term68 => @lem4629906 h1 h2) (fun h3 : False => @lem4629586 h1)). Qed.
Lemma lem4629908 (h1 : term68) (h2 : term67) : False.
Proof. exact (EQ_MP (@lem4629907 h1 h2) (@lem4629586 h1)). Qed.
Lemma lem4629909 (h1 : term67) : term73.
Proof. exact (fun h0 : term68 => @lem4629908 h0 h1). Qed.
Lemma lem4629910 : term73 = term74.
Proof. exact (@lem69 term68). Qed.
Lemma lem4629911 (h1 : term67) : term74.
Proof. exact (EQ_MP (@lem4629910) (@lem4629909 h1)). Qed.
Lemma lem4629912 {_26795 : Type'} (h1 : term67) : term77 _26795.
Proof. exact (fun h0 : term88 _26795 => @lem4629911 h1). Qed.
Lemma lem4629913 {_26795 : Type'} : term79 _26795.
Proof. exact (fun h0 : term67 => @lem4629912 _26795 h0). Qed.
Lemma lem4629914 {_26795 : Type'} : term69 _26795.
Proof. exact (EQ_MP (@lem4629509 _26795) (@lem4629913 _26795)). Qed.
Lemma lem4629916 {_26795 : Type'} : term69 _26795.
Proof. exact (@lem4629391 _26795 (@lem4629914 _26795)). Qed.
Lemma lem4629917 {_26795 : Type'} (h1 : term67) : term76 _26795.
Proof. exact (@lem4629916 _26795 (@lem4629374 h1)). Qed.
Lemma lem4629918 (h1 : term67) : term73.
Proof. exact (@lem4629917 Prop h1 (@lem1138200 Prop)). Qed.
Lemma lem4629919 (h1 : term67) : False.
Proof. exact (@lem4629918 h1 (@lem4629375)). Qed.
Lemma lem4629920 (h1 : term67) : term67 = False.
Proof. exact (prop_ext (fun h2 : term67 => @lem4629919 h1) (fun h2 : False => @lem4629374 h1)). Qed.
Lemma lem4629921 (h1 : term67) : False.
Proof. exact (EQ_MP (@lem4629920 h1) (@lem4629374 h1)). Qed.
Lemma lem4629922 : term66.
Proof. exact (fun h0 : term67 => @lem4629921 h0). Qed.
Lemma lem4629923 : term64.
Proof. exact (EQ_MP (@lem4629373) (@lem4629922)). Qed.
Lemma lem4629924 : (@IMAGE (list Ascii.ascii) nat (@List.length Ascii.ascii) (@UNIV (list Ascii.ascii))) = (@UNIV nat).
Proof. exact (EQ_MP (@lem4629369) (@lem4629923)). Qed.
Lemma lem4629925 : term46 = (@FINITE nat (@UNIV nat)).
Proof. exact (MK_COMB (@lem4629293) (@lem4629924)). Qed.
Lemma lem4629926 : term147.
Proof. exact (@lem4629292 (@lem4629925)). Qed.
Lemma lem4629927 (h1 : @FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii))) : @FINITE nat (@UNIV nat).
Proof. exact (@lem4629926 (@lem4629289 h1)). Qed.
Lemma lem4629928 : term40.
Proof. exact (fun h0 : @FINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii)) => @lem4629927 h0). Qed.
Lemma lem4629929 : term38.
Proof. exact (EQ_MP (@lem4629279) (@lem4629928)). Qed.
Lemma lem4629930 : @INFINITE (list Ascii.ascii) (@UNIV (list Ascii.ascii)).
Proof. exact (@lem4629929 (@lem4629194)). Qed.
