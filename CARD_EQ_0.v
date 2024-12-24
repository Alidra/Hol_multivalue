Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_EQ_0_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3854224 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem3854225 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem3854226 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem3854225 n) (@lem3854224 n)). Qed.
Lemma lem3854227 (n : nat) : term2 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem3854240 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem3854241 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem3854242 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem3854241 A x) (@lem3854240 A x)). Qed.
Lemma lem3854243 {A : Type'} (x : A) (s : A -> Prop) : term5 A x s.
Proof. exact (@lem3854242 A x s). Qed.
Lemma lem3854244 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = (term6 A x s).
Proof. exact (eq_refl (term5 A x s)). Qed.
Lemma lem3854245 {A : Type'} (x : A) (s : A -> Prop) : term6 A x s.
Proof. exact (EQ_MP (@lem3854244 A x s) (@lem3854243 A x s)). Qed.
Lemma lem3854246 {A : Type'} (x : A) (s : A -> Prop) : term7 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem3854259 {A : Type'} : term8 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem3854260 {A : Type'} (x : A) : term9 A x.
Proof. exact (@lem3854259 A x). Qed.
Lemma lem3854261 {A : Type'} (x : A) : (term9 A x) = (term10 A x).
Proof. exact (eq_refl (term9 A x)). Qed.
Lemma lem3854262 {A : Type'} (x : A) : term10 A x.
Proof. exact (EQ_MP (@lem3854261 A x) (@lem3854260 A x)). Qed.
Lemma lem3854263 {A : Type'} (x : A) (s : A -> Prop) : term11 A x s.
Proof. exact (@lem3854262 A x s). Qed.
Lemma lem3854264 {A : Type'} (x : A) (s : A -> Prop) : (term11 A x s) = (term12 A x s).
Proof. exact (eq_refl (term11 A x s)). Qed.
Lemma lem3854265 {A : Type'} (x : A) (s : A -> Prop) : term12 A x s.
Proof. exact (EQ_MP (@lem3854264 A x s) (@lem3854263 A x s)). Qed.
Lemma lem3854266 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3854267 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term13 A x s) = (term14 A x s).
Proof. exact (@lem3854265 A x s (@lem3854266 A s h1)). Qed.
Lemma lem3854274 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem3854275 {A : Type'} (P : type686 A) (h1 : term15 A) : term16 A P.
Proof. exact (@lem3854274 A h1 P). Qed.
Lemma lem3854276 {A : Type'} (P : type686 A) : (term16 A P) = (term17 A P).
Proof. exact (eq_refl (term16 A P)). Qed.
Lemma lem3854277 {A : Type'} (P : type686 A) (h1 : term15 A) : term17 A P.
Proof. exact (EQ_MP (@lem3854276 A P) (@lem3854275 A P h1)). Qed.
Lemma lem3854278 {A : Type'} (P : type686 A) (h1 : term18 A P) : term18 A P.
Proof. exact (h1). Qed.
Lemma lem3854279 {A : Type'} (P : type686 A) (h1 : term15 A) (h2 : term18 A P) : term19 A P.
Proof. exact (@lem3854277 A P h1 (@lem3854278 A P h2)). Qed.
Lemma lem3854280 {A : Type'} (P : type686 A) (h1 : term18 A P) : term20 A P.
Proof. exact (fun h0 : term15 A => @lem3854279 A P h0 h1). Qed.
Lemma lem3854281 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (h1). Qed.
Lemma lem3854282 {A : Type'} (P : type686 A) (h1 : term15 A) (h2 : term18 A P) : term19 A P.
Proof. exact (@lem3854280 A P h2 (@lem3854281 A h1)). Qed.
Lemma lem3854283 {A : Type'} (P : type686 A) (h1 : term15 A) : term17 A P.
Proof. exact (fun h0 : term18 A P => @lem3854282 A P h1 h0). Qed.
Lemma lem3854284 {A : Type'} (h1 : term15 A) : term15 A.
Proof. exact (fun P : type686 A => @lem3854283 A P h1). Qed.
Lemma lem3854285 {A : Type'} : term21 A.
Proof. exact (fun h0 : term15 A => @lem3854284 A h0). Qed.
Lemma lem3854286 {A : Type'} : term15 A.
Proof. exact (@lem3854285 A (@lem3558722 A)). Qed.
Lemma lem3854287 {A : Type'} (P : type686 A) : term16 A P.
Proof. exact (@lem3854286 A P). Qed.
Lemma lem3854288 {A : Type'} (P : type686 A) : (term16 A P) = (term17 A P).
Proof. exact (eq_refl (term16 A P)). Qed.
Lemma lem3854291 {A : Type'} (P : type686 A) : term17 A P.
Proof. exact (EQ_MP (@lem3854288 A P) (@lem3854287 A P)). Qed.
Lemma lem3854292 {_99911 : Type'} (P : type686 _99911) : term17 _99911 P.
Proof. exact (@lem3854291 _99911 P). Qed.
Lemma lem3854293 {_99911 : Type'} : term22 _99911.
Proof. exact (@lem3854292 _99911 (term23 _99911)). Qed.
Lemma lem3854294 {_99911 : Type'} : (term24 _99911) = (((@CARD _99911 (@EMPTY _99911)) = (NUMERAL 0)) = ((@EMPTY _99911) = (@EMPTY _99911))).
Proof. exact (eq_refl (term24 _99911)). Qed.
Lemma lem3854295 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3854296 {_99911 : Type'} : (term25 _99911) = (term26 _99911).
Proof. exact (MK_COMB (@lem3854295) (@lem3854294 _99911)). Qed.
Lemma lem3854297 {_99911 : Type'} (s : _99911 -> Prop) : (term27 _99911 s) = (((@CARD _99911 s) = (NUMERAL 0)) = (s = (@EMPTY _99911))).
Proof. exact (eq_refl (term27 _99911 s)). Qed.
Lemma lem3854298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3854299 {_99911 : Type'} (s : _99911 -> Prop) : (term28 _99911 s) = (term29 _99911 s).
Proof. exact (MK_COMB (@lem3854298) (@lem3854297 _99911 s)). Qed.
Lemma lem3854300 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term30 _99911 x s) = (term30 _99911 x s).
Proof. exact (eq_refl (term30 _99911 x s)). Qed.
Lemma lem3854301 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term31 _99911 x s) = (term32 _99911 x s).
Proof. exact (MK_COMB (@lem3854299 _99911 s) (@lem3854300 _99911 x s)). Qed.
Lemma lem3854302 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3854303 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term33 _99911 x s) = (term34 _99911 x s).
Proof. exact (MK_COMB (@lem3854302) (@lem3854301 _99911 x s)). Qed.
Lemma lem3854304 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term35 _99911 x s) = (((term13 _99911 x s) = (NUMERAL 0)) = ((@INSERT _99911 x s) = (@EMPTY _99911))).
Proof. exact (eq_refl (term35 _99911 x s)). Qed.
Lemma lem3854305 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term36 _99911 x s) = (term37 _99911 x s).
Proof. exact (MK_COMB (@lem3854303 _99911 x s) (@lem3854304 _99911 x s)). Qed.
Lemma lem3854306 {_99911 : Type'} (x : _99911) : (term38 _99911 x) = (term39 _99911 x).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem3854305 _99911 x s)). Qed.
Lemma lem3854307 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem3854308 {_99911 : Type'} (x : _99911) : (term40 _99911 x) = (term41 _99911 x).
Proof. exact (MK_COMB (@lem3854307 _99911) (@lem3854306 _99911 x)). Qed.
Lemma lem3854309 {_99911 : Type'} : (term42 _99911) = (term43 _99911).
Proof. exact (fun_ext (fun x : _99911 => @lem3854308 _99911 x)). Qed.
Lemma lem3854310 {_99911 : Type'} : (@all _99911) = (@all _99911).
Proof. exact (eq_refl (@all _99911)). Qed.
Lemma lem3854311 {_99911 : Type'} : (term44 _99911) = (term45 _99911).
Proof. exact (MK_COMB (@lem3854310 _99911) (@lem3854309 _99911)). Qed.
Lemma lem3854312 {_99911 : Type'} : (term46 _99911) = (term47 _99911).
Proof. exact (MK_COMB (@lem3854296 _99911) (@lem3854311 _99911)). Qed.
Lemma lem3854313 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3854314 {_99911 : Type'} : (term48 _99911) = (term49 _99911).
Proof. exact (MK_COMB (@lem3854313) (@lem3854312 _99911)). Qed.
Lemma lem3854315 {_99911 : Type'} (s : _99911 -> Prop) : (term27 _99911 s) = (((@CARD _99911 s) = (NUMERAL 0)) = (s = (@EMPTY _99911))).
Proof. exact (eq_refl (term27 _99911 s)). Qed.
Lemma lem3854316 {_99911 : Type'} (s : _99911 -> Prop) : (term50 _99911 s) = (term50 _99911 s).
Proof. exact (eq_refl (term50 _99911 s)). Qed.
Lemma lem3854317 {_99911 : Type'} (s : _99911 -> Prop) : (term51 _99911 s) = (term52 _99911 s).
Proof. exact (MK_COMB (@lem3854316 _99911 s) (@lem3854315 _99911 s)). Qed.
Lemma lem3854318 {_99911 : Type'} : (term53 _99911) = (term54 _99911).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem3854317 _99911 s)). Qed.
Lemma lem3854319 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem3854320 {_99911 : Type'} : (term55 _99911) = (term56 _99911).
Proof. exact (MK_COMB (@lem3854319 _99911) (@lem3854318 _99911)). Qed.
Lemma lem3854321 {_99911 : Type'} : (term22 _99911) = (term57 _99911).
Proof. exact (MK_COMB (@lem3854314 _99911) (@lem3854320 _99911)). Qed.
Lemma lem3854322 {_99911 : Type'} : term57 _99911.
Proof. exact (EQ_MP (@lem3854321 _99911) (@lem3854293 _99911)). Qed.
Lemma lem3854330 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem3854331 {_99911 : Type'} : (@CARD _99911 (@EMPTY _99911)) = (NUMERAL 0).
Proof. exact (@lem3854330 _99911). Qed.
Lemma lem3854332 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3854333 {_99911 : Type'} : (term58 _99911) = term59.
Proof. exact (MK_COMB (@lem3854332) (@lem3854331 _99911)). Qed.
Lemma lem3854334 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem3854335 {_99911 : Type'} : ((@CARD _99911 (@EMPTY _99911)) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem3854333 _99911) (@lem3854334)). Qed.
Lemma lem3854337 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3854338 (x : nat) : (x = x) = True.
Proof. exact (@lem3854337 nat x). Qed.
Lemma lem3854339 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem3854338 (NUMERAL 0)). Qed.
Lemma lem3854340 {_99911 : Type'} : ((@CARD _99911 (@EMPTY _99911)) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem3854335 _99911) (@lem3854339)). Qed.
Lemma lem3854341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3854342 {_99911 : Type'} : (term60 _99911) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3854341) (@lem3854340 _99911)). Qed.
Lemma lem3854344 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3854345 {_99911 : Type'} (x : _99911 -> Prop) : (x = x) = True.
Proof. exact (@lem3854344 (_99911 -> Prop) x). Qed.
Lemma lem3854346 {_99911 : Type'} : ((@EMPTY _99911) = (@EMPTY _99911)) = True.
Proof. exact (@lem3854345 _99911 (@EMPTY _99911)). Qed.
Lemma lem3854347 {_99911 : Type'} : (((@CARD _99911 (@EMPTY _99911)) = (NUMERAL 0)) = ((@EMPTY _99911) = (@EMPTY _99911))) = (True = True).
Proof. exact (MK_COMB (@lem3854342 _99911) (@lem3854346 _99911)). Qed.
Lemma lem3854349 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3854350 : (True = True) = True.
Proof. exact (@lem3854349 True). Qed.
Lemma lem3854351 {_99911 : Type'} : (((@CARD _99911 (@EMPTY _99911)) = (NUMERAL 0)) = ((@EMPTY _99911) = (@EMPTY _99911))) = True.
Proof. exact (TRANS (@lem3854347 _99911) (@lem3854350)). Qed.
Lemma lem3854352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3854353 {_99911 : Type'} : (term26 _99911) = (and True).
Proof. exact (MK_COMB (@lem3854352) (@lem3854351 _99911)). Qed.
Lemma lem3854365 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term61 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3854366 (p : Prop) (q : Prop) (p' : Prop) : term62 p q p'.
Proof. exact (fun q' : Prop => @lem3854365 p q p' q'). Qed.
Lemma lem3854367 (p : Prop) (q : Prop) : term63 p q.
Proof. exact (fun p' : Prop => @lem3854366 p q p'). Qed.
Lemma lem3854368 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : term64 _99911 x s.
Proof. exact (@lem3854367 (term32 _99911 x s) (((term13 _99911 x s) = (NUMERAL 0)) = ((@INSERT _99911 x s) = (@EMPTY _99911)))). Qed.
Lemma lem3854369 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (p' : Prop) : term65 _99911 x s p'.
Proof. exact (@lem3854368 _99911 x s p'). Qed.
Lemma lem3854370 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (p' : Prop) : (term65 _99911 x s p') = (term66 _99911 x s p').
Proof. exact (eq_refl (term65 _99911 x s p')). Qed.
Lemma lem3854371 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (p' : Prop) : term66 _99911 x s p'.
Proof. exact (EQ_MP (@lem3854370 _99911 x s p') (@lem3854369 _99911 x s p')). Qed.
Lemma lem3854372 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (p' : Prop) (q' : Prop) : term67 _99911 x s p' q'.
Proof. exact (@lem3854371 _99911 x s p' q'). Qed.
Lemma lem3854373 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (p' : Prop) (q' : Prop) : (term67 _99911 x s p' q') = (term68 _99911 x s p' q').
Proof. exact (eq_refl (term67 _99911 x s p' q')). Qed.
Lemma lem3854374 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (p' : Prop) (q' : Prop) : term68 _99911 x s p' q'.
Proof. exact (EQ_MP (@lem3854373 _99911 x s p' q') (@lem3854372 _99911 x s p' q')). Qed.
Lemma lem3854385 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term32 _99911 x s) = (term32 _99911 x s).
Proof. exact (eq_refl (term32 _99911 x s)). Qed.
Lemma lem3854386 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (q' : Prop) : term69 _99911 x s q'.
Proof. exact (@lem3854374 _99911 x s (term32 _99911 x s) q'). Qed.
Lemma lem3854387 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (q' : Prop) : term70 _99911 x s q'.
Proof. exact (@lem3854386 _99911 x s q' (@lem3854385 _99911 x s)). Qed.
Lemma lem3854388 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : term32 _99911 x s.
Proof. exact (h1). Qed.
Lemma lem3854389 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : term30 _99911 x s.
Proof. exact (proj2 (@lem3854388 _99911 x s h1)). Qed.
Lemma lem3854390 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : @FINITE _99911 s.
Proof. exact (proj2 (@lem3854389 _99911 x s h1)). Qed.
Lemma lem3854391 {_99911 : Type'} (s : _99911 -> Prop) : (@FINITE _99911 s) = ((@FINITE _99911 s) = True).
Proof. exact (@lem7 (@FINITE _99911 s)). Qed.
Lemma lem3854393 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : term71 _99911 x s.
Proof. exact (proj1 (@lem3854389 _99911 x s h1)). Qed.
Lemma lem3854394 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : term72 _99911 x s.
Proof. exact (@lem82 (@IN _99911 x s)). Qed.
Lemma lem3854402 {A : Type'} (x : A) (s : A -> Prop) : term12 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3854267 A x s h0). Qed.
Lemma lem3854403 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : term12 _99911 x s.
Proof. exact (@lem3854402 _99911 x s). Qed.
Lemma lem3854405 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : (@FINITE _99911 s) = True.
Proof. exact (EQ_MP (@lem3854391 _99911 s) (@lem3854390 _99911 x s h1)). Qed.
Lemma lem3854406 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : True = (@FINITE _99911 s).
Proof. exact (SYM (@lem3854405 _99911 x s h1)). Qed.
Lemma lem3854407 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : @FINITE _99911 s.
Proof. exact (EQ_MP (@lem3854406 _99911 x s h1) (@lem0)). Qed.
Lemma lem3854408 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : (term13 _99911 x s) = (term14 _99911 x s).
Proof. exact (@lem3854403 _99911 x s (@lem3854407 _99911 x s h1)). Qed.
Lemma lem3854410 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term73 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem3854411 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term74 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem3854410 _2963 g t e g' t' e'). Qed.
Lemma lem3854412 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term75 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem3854411 _2963 g t e g' t'). Qed.
Lemma lem3854413 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term76 _2963 g t e.
Proof. exact (fun g' : Prop => @lem3854412 _2963 g t e g'). Qed.
Lemma lem3854414 (g : Prop) (t : nat) (e : nat) : term77 g t e.
Proof. exact (@lem3854413 nat g t e). Qed.
Lemma lem3854415 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : term78 _99911 x s.
Proof. exact (@lem3854414 (@IN _99911 x s) (@CARD _99911 s) (term79 _99911 s)). Qed.
Lemma lem3854416 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (g' : Prop) : term80 _99911 x s g'.
Proof. exact (@lem3854415 _99911 x s g'). Qed.
Lemma lem3854417 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (g' : Prop) : (term80 _99911 x s g') = (term81 _99911 x s g').
Proof. exact (eq_refl (term80 _99911 x s g')). Qed.
Lemma lem3854418 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (g' : Prop) : term81 _99911 x s g'.
Proof. exact (EQ_MP (@lem3854417 _99911 x s g') (@lem3854416 _99911 x s g')). Qed.
Lemma lem3854419 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (g' : Prop) (t' : nat) : term82 _99911 x s g' t'.
Proof. exact (@lem3854418 _99911 x s g' t'). Qed.
Lemma lem3854420 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (g' : Prop) (t' : nat) : (term82 _99911 x s g' t') = (term83 _99911 x s g' t').
Proof. exact (eq_refl (term82 _99911 x s g' t')). Qed.
Lemma lem3854421 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (g' : Prop) (t' : nat) : term83 _99911 x s g' t'.
Proof. exact (EQ_MP (@lem3854420 _99911 x s g' t') (@lem3854419 _99911 x s g' t')). Qed.
Lemma lem3854422 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term84 _99911 x s g' t' e'.
Proof. exact (@lem3854421 _99911 x s g' t' e'). Qed.
Lemma lem3854423 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term84 _99911 x s g' t' e') = (term85 _99911 x s g' t' e').
Proof. exact (eq_refl (term84 _99911 x s g' t' e')). Qed.
Lemma lem3854424 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term85 _99911 x s g' t' e'.
Proof. exact (EQ_MP (@lem3854423 _99911 x s g' t' e') (@lem3854422 _99911 x s g' t' e')). Qed.
Lemma lem3854426 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : (@IN _99911 x s) = False.
Proof. exact (@lem3854394 _99911 x s (@lem3854393 _99911 x s h1)). Qed.
Lemma lem3854427 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (t' : nat) (e' : nat) : term86 _99911 x s t' e'.
Proof. exact (@lem3854424 _99911 x s False t' e'). Qed.
Lemma lem3854428 {_99911 : Type'} (t' : nat) (e' : nat) (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : term87 _99911 x s t' e'.
Proof. exact (@lem3854427 _99911 x s t' e' (@lem3854426 _99911 x s h1)). Qed.
Lemma lem3854432 {_99911 : Type'} (s : _99911 -> Prop) : (@CARD _99911 s) = (@CARD _99911 s).
Proof. exact (eq_refl (@CARD _99911 s)). Qed.
Lemma lem3854433 {_99911 : Type'} (s : _99911 -> Prop) : term88 _99911 s.
Proof. exact (fun h0 : False => @lem3854432 _99911 s). Qed.
Lemma lem3854434 {_99911 : Type'} (e' : nat) (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : term89 _99911 x s e'.
Proof. exact (@lem3854428 _99911 (@CARD _99911 s) e' x s h1). Qed.
Lemma lem3854435 {_99911 : Type'} (e' : nat) (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : term90 _99911 x s e'.
Proof. exact (@lem3854434 _99911 e' x s h1 (@lem3854433 _99911 s)). Qed.
Lemma lem3854441 {_99911 : Type'} (s : _99911 -> Prop) : (term79 _99911 s) = (term79 _99911 s).
Proof. exact (eq_refl (term79 _99911 s)). Qed.
Lemma lem3854442 {_99911 : Type'} (s : _99911 -> Prop) : term91 _99911 s.
Proof. exact (fun h0 : ~ False => @lem3854441 _99911 s). Qed.
Lemma lem3854443 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : term92 _99911 x s.
Proof. exact (@lem3854435 _99911 (term79 _99911 s) x s h1). Qed.
Lemma lem3854444 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : (term14 _99911 x s) = (term93 _99911 s).
Proof. exact (@lem3854443 _99911 x s h1 (@lem3854442 _99911 s)). Qed.
Lemma lem3854446 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3854447 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem3854446 nat t1 t2). Qed.
Lemma lem3854448 {_99911 : Type'} (s : _99911 -> Prop) : (term93 _99911 s) = (term79 _99911 s).
Proof. exact (@lem3854447 (@CARD _99911 s) (term79 _99911 s)). Qed.
Lemma lem3854449 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : (term14 _99911 x s) = (term79 _99911 s).
Proof. exact (TRANS (@lem3854444 _99911 x s h1) (@lem3854448 _99911 s)). Qed.
Lemma lem3854450 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : (term13 _99911 x s) = (term79 _99911 s).
Proof. exact (TRANS (@lem3854408 _99911 x s h1) (@lem3854449 _99911 x s h1)). Qed.
Lemma lem3854451 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3854452 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : (term94 _99911 x s) = (term95 _99911 s).
Proof. exact (MK_COMB (@lem3854451) (@lem3854450 _99911 x s h1)). Qed.
Lemma lem3854453 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem3854454 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : ((term13 _99911 x s) = (NUMERAL 0)) = ((term79 _99911 s) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem3854452 _99911 x s h1) (@lem3854453)). Qed.
Lemma lem3854456 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem3854227 n (@lem3854226 n)). Qed.
Lemma lem3854457 {_99911 : Type'} (s : _99911 -> Prop) : ((term79 _99911 s) = (NUMERAL 0)) = False.
Proof. exact (@lem3854456 (@CARD _99911 s)). Qed.
Lemma lem3854458 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : ((term13 _99911 x s) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem3854454 _99911 x s h1) (@lem3854457 _99911 s)). Qed.
Lemma lem3854459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3854460 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : (term96 _99911 x s) = (@eq Prop False).
Proof. exact (MK_COMB (@lem3854459) (@lem3854458 _99911 x s h1)). Qed.
Lemma lem3854462 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem3854246 A x s (@lem3854245 A x s)). Qed.
Lemma lem3854463 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : ((@INSERT _99911 x s) = (@EMPTY _99911)) = False.
Proof. exact (@lem3854462 _99911 x s). Qed.
Lemma lem3854464 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : (((term13 _99911 x s) = (NUMERAL 0)) = ((@INSERT _99911 x s) = (@EMPTY _99911))) = (False = False).
Proof. exact (MK_COMB (@lem3854460 _99911 x s h1) (@lem3854463 _99911 x s)). Qed.
Lemma lem3854466 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3854467 : (False = False) = (~ False).
Proof. exact (@lem3854466 False). Qed.
Lemma lem3854469 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3854470 : (False = False) = True.
Proof. exact (TRANS (@lem3854467) (@lem3854469)). Qed.
Lemma lem3854471 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) (h1 : term32 _99911 x s) : (((term13 _99911 x s) = (NUMERAL 0)) = ((@INSERT _99911 x s) = (@EMPTY _99911))) = True.
Proof. exact (TRANS (@lem3854464 _99911 x s h1) (@lem3854470)). Qed.
Lemma lem3854472 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : term97 _99911 x s.
Proof. exact (fun h0 : term32 _99911 x s => @lem3854471 _99911 x s h0). Qed.
Lemma lem3854473 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : term98 _99911 x s.
Proof. exact (@lem3854387 _99911 x s True). Qed.
Lemma lem3854474 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term37 _99911 x s) = (term99 _99911 x s).
Proof. exact (@lem3854473 _99911 x s (@lem3854472 _99911 x s)). Qed.
Lemma lem3854476 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3854477 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term99 _99911 x s) = True.
Proof. exact (@lem3854476 (term32 _99911 x s)). Qed.
Lemma lem3854478 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term37 _99911 x s) = True.
Proof. exact (TRANS (@lem3854474 _99911 x s) (@lem3854477 _99911 x s)). Qed.
Lemma lem3854479 {_99911 : Type'} (x : _99911) : (term39 _99911 x) = (term100 _99911).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem3854478 _99911 x s)). Qed.
Lemma lem3854480 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem3854481 {_99911 : Type'} (x : _99911) : (term41 _99911 x) = (term101 _99911).
Proof. exact (MK_COMB (@lem3854480 _99911) (@lem3854479 _99911 x)). Qed.
Lemma lem3854483 {A : Type'} (t : Prop) : (term102 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3854484 {_99911 : Type'} (t : Prop) : (term103 _99911 t) = t.
Proof. exact (@lem3854483 (_99911 -> Prop) t). Qed.
Lemma lem3854485 {_99911 : Type'} : (term101 _99911) = True.
Proof. exact (@lem3854484 _99911 True). Qed.
Lemma lem3854486 {_99911 : Type'} (x : _99911) : (term41 _99911 x) = True.
Proof. exact (TRANS (@lem3854481 _99911 x) (@lem3854485 _99911)). Qed.
Lemma lem3854487 {_99911 : Type'} : (term43 _99911) = (term104 _99911).
Proof. exact (fun_ext (fun x : _99911 => @lem3854486 _99911 x)). Qed.
Lemma lem3854488 {_99911 : Type'} : (@all _99911) = (@all _99911).
Proof. exact (eq_refl (@all _99911)). Qed.
Lemma lem3854489 {_99911 : Type'} : (term45 _99911) = (term105 _99911).
Proof. exact (MK_COMB (@lem3854488 _99911) (@lem3854487 _99911)). Qed.
Lemma lem3854491 {A : Type'} (t : Prop) : (term102 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3854492 {_99911 : Type'} (t : Prop) : (term102 _99911 t) = t.
Proof. exact (@lem3854491 _99911 t). Qed.
Lemma lem3854493 {_99911 : Type'} : (term105 _99911) = True.
Proof. exact (@lem3854492 _99911 True). Qed.
Lemma lem3854494 {_99911 : Type'} : (term45 _99911) = True.
Proof. exact (TRANS (@lem3854489 _99911) (@lem3854493 _99911)). Qed.
Lemma lem3854495 {_99911 : Type'} : (term47 _99911) = (True /\ True).
Proof. exact (MK_COMB (@lem3854353 _99911) (@lem3854494 _99911)). Qed.
Lemma lem3854497 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3854498 : (True /\ True) = True.
Proof. exact (@lem3854497 True). Qed.
Lemma lem3854499 {_99911 : Type'} : (term47 _99911) = True.
Proof. exact (TRANS (@lem3854495 _99911) (@lem3854498)). Qed.
Lemma lem3854500 {_99911 : Type'} : True = (term47 _99911).
Proof. exact (SYM (@lem3854499 _99911)). Qed.
Lemma lem3854501 {_99911 : Type'} : term47 _99911.
Proof. exact (EQ_MP (@lem3854500 _99911) (@lem0)). Qed.
Lemma lem3854502 {_99911 : Type'} : term56 _99911.
Proof. exact (@lem3854322 _99911 (@lem3854501 _99911)). Qed.
