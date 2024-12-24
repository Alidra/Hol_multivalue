Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_ITERATE_PRODUCT_term_abbrevs.
Require Import DISJOINT_spec.
Require Import DISJ_ASSOC_spec.
Require Import ETA_AX_spec.
Require Import EXTENSION_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FINITE_PRODUCT_DEPENDENT_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_IMAGE_spec.
Require Import IN_INSERT_spec.
Require Import IN_INTER_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import ITERATE_IMAGE_spec.
Require Import ITERATE_UNION_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import PAIR_EQ_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import o_DEF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm129_spec.
Require Import thm137_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm196_spec.
Require Import thm19699_spec.
Require Import thm197_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211647_spec.
Require Import thm3211648_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem5947360 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem5947361 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem5947362 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem5947361 A B t) (@lem5947360 A B t)). Qed.
Lemma lem5947363 {A B C : Type'} (f : B -> C) : term2 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem5947364 {A B C : Type'} (f : B -> C) : (term2 A B C f) = (term3 A B C f).
Proof. exact (eq_refl (term2 A B C f)). Qed.
Lemma lem5947365 {A B C : Type'} (f : B -> C) : term3 A B C f.
Proof. exact (EQ_MP (@lem5947364 A B C f) (@lem5947363 A B C f)). Qed.
Lemma lem5947366 {A B C : Type'} (f : B -> C) (g : A -> B) : term4 A B C f g.
Proof. exact (@lem5947365 A B C f g). Qed.
Lemma lem5947367 {A B C : Type'} (f : B -> C) (g : A -> B) : (term4 A B C f g) = ((@o A B C f g) = (term5 A B C f g)).
Proof. exact (eq_refl (term4 A B C f g)). Qed.
Lemma lem5947382 {A B : Type'} (x : A) : term6 A B x.
Proof. exact (@lem47438 A B x). Qed.
Lemma lem5947383 {A B : Type'} (x : A) : (term6 A B x) = (term7 A B x).
Proof. exact (eq_refl (term6 A B x)). Qed.
Lemma lem5947384 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (EQ_MP (@lem5947383 A B x) (@lem5947382 A B x)). Qed.
Lemma lem5947385 {A B : Type'} (x : A) (y : B) : term8 A B x y.
Proof. exact (@lem5947384 A B x y). Qed.
Lemma lem5947386 {A B : Type'} (x : A) (y : B) : (term8 A B x y) = (term9 A B x y).
Proof. exact (eq_refl (term8 A B x y)). Qed.
Lemma lem5947387 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (EQ_MP (@lem5947386 A B x y) (@lem5947385 A B x y)). Qed.
Lemma lem5947388 {A B : Type'} (x : A) (y : B) (a : A) : term10 A B x y a.
Proof. exact (@lem5947387 A B x y a). Qed.
Lemma lem5947389 {A B : Type'} (x : A) (a : A) (y : B) : (term10 A B x y a) = (term11 A B x a y).
Proof. exact (eq_refl (term10 A B x y a)). Qed.
Lemma lem5947390 {A B : Type'} (x : A) (a : A) (y : B) : term11 A B x a y.
Proof. exact (EQ_MP (@lem5947389 A B x a y) (@lem5947388 A B x y a)). Qed.
Lemma lem5947391 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term12 A B x a y b.
Proof. exact (@lem5947390 A B x a y b). Qed.
Lemma lem5947392 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term12 A B x a y b) = (((@pair A B x y) = (@pair A B a b)) = (term13 A B x a y b)).
Proof. exact (eq_refl (term12 A B x a y b)). Qed.
Lemma lem5947394 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term14 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem5947395 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term14 _5106 _5107 P) = ((term15 _5106 _5107 P) = (term16 _5106 _5107 P)).
Proof. exact (eq_refl (term14 _5106 _5107 P)). Qed.
Lemma lem5947431 {_83064 : Type'} : term17 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem5947432 {_83064 : Type'} (P : type919 _83064) : term18 _83064 P.
Proof. exact (@lem5947431 _83064 P). Qed.
Lemma lem5947433 {_83064 : Type'} (P : type919 _83064) : (term18 _83064 P) = (term19 _83064 P).
Proof. exact (eq_refl (term18 _83064 P)). Qed.
Lemma lem5947434 {_83064 : Type'} (P : type919 _83064) : term19 _83064 P.
Proof. exact (EQ_MP (@lem5947433 _83064 P) (@lem5947432 _83064 P)). Qed.
Lemma lem5947435 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term20 _83064 P x.
Proof. exact (@lem5947434 _83064 P x). Qed.
Lemma lem5947436 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term20 _83064 P x) = ((term21 _83064 x P) = (term22 _83064 P x)).
Proof. exact (eq_refl (term20 _83064 P x)). Qed.
Lemma lem5947438 {A : Type'} (x : A) : term23 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5947439 {A : Type'} (x : A) : (term23 A x) = (term24 A x).
Proof. exact (eq_refl (term23 A x)). Qed.
Lemma lem5947440 {A : Type'} (x : A) : term24 A x.
Proof. exact (EQ_MP (@lem5947439 A x) (@lem5947438 A x)). Qed.
Lemma lem5947441 {A : Type'} (x : A) : term25 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5947443 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem5947444 {A : Type'} (s : A -> Prop) : (term26 A s) = (term27 A s).
Proof. exact (eq_refl (term26 A s)). Qed.
Lemma lem5947445 {A : Type'} (s : A -> Prop) : term27 A s.
Proof. exact (EQ_MP (@lem5947444 A s) (@lem5947443 A s)). Qed.
Lemma lem5947446 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term28 A s t.
Proof. exact (@lem5947445 A s t). Qed.
Lemma lem5947447 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term28 A s t) = (term29 A s t).
Proof. exact (eq_refl (term28 A s t)). Qed.
Lemma lem5947448 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term29 A s t.
Proof. exact (EQ_MP (@lem5947447 A s t) (@lem5947446 A s t)). Qed.
Lemma lem5947449 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term30 A s t x.
Proof. exact (@lem5947448 A s t x). Qed.
Lemma lem5947450 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term30 A s t x) = ((term31 A x s t) = (term32 A s x t)).
Proof. exact (eq_refl (term30 A s t x)). Qed.
Lemma lem5947452 {A B : Type'} (y : B) : term33 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem5947453 {A B : Type'} (y : B) : (term33 A B y) = (term34 A B y).
Proof. exact (eq_refl (term33 A B y)). Qed.
Lemma lem5947454 {A B : Type'} (y : B) : term34 A B y.
Proof. exact (EQ_MP (@lem5947453 A B y) (@lem5947452 A B y)). Qed.
Lemma lem5947455 {A B : Type'} (y : B) (s : A -> Prop) : term35 A B y s.
Proof. exact (@lem5947454 A B y s). Qed.
Lemma lem5947456 {A B : Type'} (y : B) (s : A -> Prop) : (term35 A B y s) = (term36 A B y s).
Proof. exact (eq_refl (term35 A B y s)). Qed.
Lemma lem5947457 {A B : Type'} (y : B) (s : A -> Prop) : term36 A B y s.
Proof. exact (EQ_MP (@lem5947456 A B y s) (@lem5947455 A B y s)). Qed.
Lemma lem5947458 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term37 A B y s f.
Proof. exact (@lem5947457 A B y s f). Qed.
Lemma lem5947459 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term37 A B y s f) = ((term38 A B y f s) = (term39 A B y f s)).
Proof. exact (eq_refl (term37 A B y s f)). Qed.
Lemma lem5947461 {A : Type'} (s : A -> Prop) : term40 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5947462 {A : Type'} (s : A -> Prop) : (term40 A s) = (term41 A s).
Proof. exact (eq_refl (term40 A s)). Qed.
Lemma lem5947463 {A : Type'} (s : A -> Prop) : term41 A s.
Proof. exact (EQ_MP (@lem5947462 A s) (@lem5947461 A s)). Qed.
Lemma lem5947464 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term42 A s t.
Proof. exact (@lem5947463 A s t). Qed.
Lemma lem5947465 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = ((s = t) = (term43 A s t)).
Proof. exact (eq_refl (term42 A s t)). Qed.
Lemma lem5947467 {A : Type'} (s : A -> Prop) : term44 A s.
Proof. exact (@lem3196110 A s). Qed.
Lemma lem5947468 {A : Type'} (s : A -> Prop) : (term44 A s) = (term45 A s).
Proof. exact (eq_refl (term44 A s)). Qed.
Lemma lem5947469 {A : Type'} (s : A -> Prop) : term45 A s.
Proof. exact (EQ_MP (@lem5947468 A s) (@lem5947467 A s)). Qed.
Lemma lem5947470 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term46 A s t.
Proof. exact (@lem5947469 A s t). Qed.
Lemma lem5947471 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term46 A s t) = ((@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A))).
Proof. exact (eq_refl (term46 A s t)). Qed.
Lemma lem5947473 (t1 : Prop) : term47 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5947474 (t1 : Prop) : (term47 t1) = (term48 t1).
Proof. exact (eq_refl (term47 t1)). Qed.
Lemma lem5947475 (t1 : Prop) : term48 t1.
Proof. exact (EQ_MP (@lem5947474 t1) (@lem5947473 t1)). Qed.
Lemma lem5947476 (t1 : Prop) (t2 : Prop) : term49 t1 t2.
Proof. exact (@lem5947475 t1 t2). Qed.
Lemma lem5947477 (t1 : Prop) (t2 : Prop) : (term49 t1 t2) = (term50 t1 t2).
Proof. exact (eq_refl (term49 t1 t2)). Qed.
Lemma lem5947478 (t1 : Prop) (t2 : Prop) : term50 t1 t2.
Proof. exact (EQ_MP (@lem5947477 t1 t2) (@lem5947476 t1 t2)). Qed.
Lemma lem5947479 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term51 t1 t2 t3.
Proof. exact (@lem5947478 t1 t2 t3). Qed.
Lemma lem5947480 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term51 t1 t2 t3) = ((term52 t1 t2 t3) = (term53 t1 t2 t3)).
Proof. exact (eq_refl (term51 t1 t2 t3)). Qed.
Lemma lem5947481 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term52 t1 t2 t3) = (term53 t1 t2 t3).
Proof. exact (EQ_MP (@lem5947480 t1 t2 t3) (@lem5947479 t1 t2 t3)). Qed.
Lemma lem5947482 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term53 t1 t2 t3) = (term52 t1 t2 t3).
Proof. exact (SYM (@lem5947481 t1 t2 t3)). Qed.
Lemma lem5947486 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term43 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5947487 {_121855 _121856 : Type'} (s : type1223 _121855 _121856) (t : type1223 _121855 _121856) : (s = t) = (term54 _121855 _121856 s t).
Proof. exact (@lem5947486 (prod _121856 _121855) s t). Qed.
Lemma lem5947488 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : ((term55 _121855 _121856 a s t) = (term56 _121855 _121856 a s t)) = (term57 _121855 _121856 a s t).
Proof. exact (@lem5947487 _121855 _121856 (term55 _121855 _121856 a s t) (term56 _121855 _121856 a s t)). Qed.
Lemma lem5947517 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term57 _121855 _121856 a s t) = ((term55 _121855 _121856 a s t) = (term56 _121855 _121856 a s t)).
Proof. exact (SYM (@lem5947488 _121855 _121856 a s t)). Qed.
Lemma lem5947525 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term21 _83064 x P) = (term22 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem5947526 {_121855 _121856 : Type'} (P : type916 _121855 _121856) (x : prod _121856 _121855) : (term58 _121855 _121856 x P) = (term59 _121855 _121856 P x).
Proof. exact (@lem5947525 (prod _121856 _121855) P x). Qed.
Lemma lem5947527 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term60 _121855 _121856 x a s t) = (term61 _121855 _121856 a s t x).
Proof. exact (@lem5947526 _121855 _121856 (term62 _121855 _121856 a s t) x). Qed.
Lemma lem5947528 {_121855 _121856 : Type'} (GEN_PVAR_238 : prod _121856 _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term63 _121855 _121856 a s t GEN_PVAR_238) = (term64 _121855 _121856 GEN_PVAR_238 a s t).
Proof. exact (eq_refl (term63 _121855 _121856 a s t GEN_PVAR_238)). Qed.
Lemma lem5947529 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term65 _121855 _121856 a s t) = (term66 _121855 _121856 a s t).
Proof. exact (fun_ext (fun GEN_PVAR_238 : prod _121856 _121855 => @lem5947528 _121855 _121856 GEN_PVAR_238 a s t)). Qed.
Lemma lem5947530 {_121855 _121856 : Type'} : (@GSPEC (prod _121856 _121855)) = (@GSPEC (prod _121856 _121855)).
Proof. exact (eq_refl (@GSPEC (prod _121856 _121855))). Qed.
Lemma lem5947531 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term67 _121855 _121856 a s t) = (term55 _121855 _121856 a s t).
Proof. exact (MK_COMB (@lem5947530 _121855 _121856) (@lem5947529 _121855 _121856 a s t)). Qed.
Lemma lem5947532 {_121855 _121856 : Type'} (x : prod _121856 _121855) : (@IN (prod _121856 _121855) x) = (@IN (prod _121856 _121855) x).
Proof. exact (eq_refl (@IN (prod _121856 _121855) x)). Qed.
Lemma lem5947533 {_121855 _121856 : Type'} (x : prod _121856 _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term60 _121855 _121856 x a s t) = (term68 _121855 _121856 x a s t).
Proof. exact (MK_COMB (@lem5947532 _121855 _121856 x) (@lem5947531 _121855 _121856 a s t)). Qed.
Lemma lem5947534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5947535 {_121855 _121856 : Type'} (x : prod _121856 _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term69 _121855 _121856 x a s t) = (term70 _121855 _121856 x a s t).
Proof. exact (MK_COMB (@lem5947534) (@lem5947533 _121855 _121856 x a s t)). Qed.
Lemma lem5947536 {_121855 _121856 : Type'} (x : prod _121856 _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term61 _121855 _121856 a s t x) = (term71 _121855 _121856 x a s t).
Proof. exact (eq_refl (term61 _121855 _121856 a s t x)). Qed.
Lemma lem5947537 {_121855 _121856 : Type'} (x : prod _121856 _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : ((term60 _121855 _121856 x a s t) = (term61 _121855 _121856 a s t x)) = ((term68 _121855 _121856 x a s t) = (term71 _121855 _121856 x a s t)).
Proof. exact (MK_COMB (@lem5947535 _121855 _121856 x a s t) (@lem5947536 _121855 _121856 x a s t)). Qed.
Lemma lem5947538 {_121855 _121856 : Type'} (x : prod _121856 _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term68 _121855 _121856 x a s t) = (term71 _121855 _121856 x a s t).
Proof. exact (EQ_MP (@lem5947537 _121855 _121856 x a s t) (@lem5947527 _121855 _121856 a s t x)). Qed.
Lemma lem5947548 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5947549 {_121855 _121856 : Type'} (f : type1534 _121855 _121856) (y : Prop) : (term73 _121855 _121856 f y) = (f y).
Proof. exact (@lem5947548 Prop (type1223 _121855 _121856) f y). Qed.
Lemma lem5947550 {_121855 _121856 : Type'} (x : prod _121856 _121855) (a : _121856) (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) : (term74 _121855 _121856 x a s j t i) = (term75 _121855 _121856 x a s j t i).
Proof. exact (@lem5947549 _121855 _121856 (term76 _121855 _121856 x) (term77 _121855 _121856 a s j t i)). Qed.
Lemma lem5947551 {_121855 _121856 : Type'} (p : Prop) (x : prod _121856 _121855) : (term78 _121855 _121856 x p) = (term79 _121855 _121856 p x).
Proof. exact (eq_refl (term78 _121855 _121856 x p)). Qed.
Lemma lem5947552 {_121855 _121856 : Type'} (x : prod _121856 _121855) : (term80 _121855 _121856 x) = (term76 _121855 _121856 x).
Proof. exact (fun_ext (fun p : Prop => @lem5947551 _121855 _121856 p x)). Qed.
Lemma lem5947553 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) : (term77 _121855 _121856 a s j t i) = (term77 _121855 _121856 a s j t i).
Proof. exact (eq_refl (term77 _121855 _121856 a s j t i)). Qed.
Lemma lem5947554 {_121855 _121856 : Type'} (x : prod _121856 _121855) (a : _121856) (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) : (term74 _121855 _121856 x a s j t i) = (term75 _121855 _121856 x a s j t i).
Proof. exact (MK_COMB (@lem5947552 _121855 _121856 x) (@lem5947553 _121855 _121856 a s j t i)). Qed.
Lemma lem5947555 {_121855 _121856 : Type'} : (@eq ((prod _121856 _121855) -> Prop)) = (@eq ((prod _121856 _121855) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _121856 _121855) -> Prop))). Qed.
Lemma lem5947556 {_121855 _121856 : Type'} (x : prod _121856 _121855) (a : _121856) (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) : (term81 _121855 _121856 x a s j t i) = (term82 _121855 _121856 x a s j t i).
Proof. exact (MK_COMB (@lem5947555 _121855 _121856) (@lem5947554 _121855 _121856 x a s j t i)). Qed.
Lemma lem5947557 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) (x : prod _121856 _121855) : (term75 _121855 _121856 x a s j t i) = (term83 _121855 _121856 a s j t i x).
Proof. exact (eq_refl (term75 _121855 _121856 x a s j t i)). Qed.
Lemma lem5947558 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) (x : prod _121856 _121855) : ((term74 _121855 _121856 x a s j t i) = (term75 _121855 _121856 x a s j t i)) = ((term75 _121855 _121856 x a s j t i) = (term83 _121855 _121856 a s j t i x)).
Proof. exact (MK_COMB (@lem5947556 _121855 _121856 x a s j t i) (@lem5947557 _121855 _121856 a s j t i x)). Qed.
Lemma lem5947559 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) (x : prod _121856 _121855) : (term75 _121855 _121856 x a s j t i) = (term83 _121855 _121856 a s j t i x).
Proof. exact (EQ_MP (@lem5947558 _121855 _121856 a s j t i x) (@lem5947550 _121855 _121856 x a s j t i)). Qed.
Lemma lem5947565 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term84 A x y s) = (term85 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5947566 {_121856 : Type'} (y : _121856) (x : _121856) (s : _121856 -> Prop) : (term84 _121856 x y s) = (term85 _121856 y x s).
Proof. exact (@lem5947565 _121856 y x s). Qed.
Lemma lem5947567 {_121856 : Type'} (a : _121856) (i : _121856) (s : _121856 -> Prop) : (term84 _121856 i a s) = (term85 _121856 a i s).
Proof. exact (@lem5947566 _121856 a i s). Qed.
Lemma lem5947573 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5947574 {_121856 : Type'} (P : _121856 -> Prop) (x : _121856) : (@IN _121856 x P) = (P x).
Proof. exact (@lem5947573 _121856 P x). Qed.
Lemma lem5947575 {_121856 : Type'} (s : _121856 -> Prop) (i : _121856) : (@IN _121856 i s) = (s i).
Proof. exact (@lem5947574 _121856 s i). Qed.
Lemma lem5947576 {_121856 : Type'} (i : _121856) (a : _121856) : (term86 _121856 i a) = (term86 _121856 i a).
Proof. exact (eq_refl (term86 _121856 i a)). Qed.
Lemma lem5947577 {_121856 : Type'} (a : _121856) (s : _121856 -> Prop) (i : _121856) : (term85 _121856 a i s) = (term87 _121856 a s i).
Proof. exact (MK_COMB (@lem5947576 _121856 i a) (@lem5947575 _121856 s i)). Qed.
Lemma lem5947580 {_121856 : Type'} (a : _121856) (s : _121856 -> Prop) (i : _121856) : (term84 _121856 i a s) = (term87 _121856 a s i).
Proof. exact (TRANS (@lem5947567 _121856 a i s) (@lem5947577 _121856 a s i)). Qed.
Lemma lem5947581 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5947582 {_121856 : Type'} (a : _121856) (s : _121856 -> Prop) (i : _121856) : (term88 _121856 i a s) = (term89 _121856 a s i).
Proof. exact (MK_COMB (@lem5947581) (@lem5947580 _121856 a s i)). Qed.
Lemma lem5947584 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5947585 {_121855 : Type'} (P : _121855 -> Prop) (x : _121855) : (@IN _121855 x P) = (P x).
Proof. exact (@lem5947584 _121855 P x). Qed.
Lemma lem5947586 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term90 _121855 _121856 j t i) = (t i j).
Proof. exact (@lem5947585 _121855 (t i) j). Qed.
Lemma lem5947587 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term77 _121855 _121856 a s j t i) = (term91 _121855 _121856 a s t i j).
Proof. exact (MK_COMB (@lem5947582 _121856 a s i) (@lem5947586 _121855 _121856 t i j)). Qed.
Lemma lem5947590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5947591 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term92 _121855 _121856 a s j t i) = (term93 _121855 _121856 a s t i j).
Proof. exact (MK_COMB (@lem5947590) (@lem5947587 _121855 _121856 a s t i j)). Qed.
Lemma lem5947594 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : prod _121856 _121855) : (x = t) = (x = t).
Proof. exact (eq_refl (x = t)). Qed.
Lemma lem5947595 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (x : prod _121856 _121855) (t' : prod _121856 _121855) : (term94 _121855 _121856 a s j t i x t') = (term95 _121855 _121856 a s t i j x t').
Proof. exact (MK_COMB (@lem5947591 _121855 _121856 a s t i j) (@lem5947594 _121855 _121856 x t')). Qed.
Lemma lem5947598 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (x : prod _121856 _121855) : (term83 _121855 _121856 a s j t i x) = (term96 _121855 _121856 a s t i j x).
Proof. exact (fun_ext (fun t' : prod _121856 _121855 => @lem5947595 _121855 _121856 a s t i j x t')). Qed.
Lemma lem5947599 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (x : prod _121856 _121855) : (term75 _121855 _121856 x a s j t i) = (term96 _121855 _121856 a s t i j x).
Proof. exact (TRANS (@lem5947559 _121855 _121856 a s j t i x) (@lem5947598 _121855 _121856 a s t i j x)). Qed.
Lemma lem5947600 {_121855 _121856 : Type'} (i : _121856) (j : _121855) : (@pair _121856 _121855 i j) = (@pair _121856 _121855 i j).
Proof. exact (eq_refl (@pair _121856 _121855 i j)). Qed.
Lemma lem5947601 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term97 _121855 _121856 x a s t i j) = (term98 _121855 _121856 a s t x i j).
Proof. exact (MK_COMB (@lem5947599 _121855 _121856 a s t i j x) (@lem5947600 _121855 _121856 i j)). Qed.
Lemma lem5947603 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5947604 {_121855 _121856 : Type'} (f : type1223 _121855 _121856) (y : prod _121856 _121855) : (term99 _121855 _121856 f y) = (f y).
Proof. exact (@lem5947603 (prod _121856 _121855) Prop f y). Qed.
Lemma lem5947605 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term100 _121855 _121856 a s t x i j) = (term98 _121855 _121856 a s t x i j).
Proof. exact (@lem5947604 _121855 _121856 (term96 _121855 _121856 a s t i j x) (@pair _121856 _121855 i j)). Qed.
Lemma lem5947606 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (x : prod _121856 _121855) (t' : prod _121856 _121855) : (term101 _121855 _121856 a s t i j x t') = (term95 _121855 _121856 a s t i j x t').
Proof. exact (eq_refl (term101 _121855 _121856 a s t i j x t')). Qed.
Lemma lem5947607 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (x : prod _121856 _121855) : (term102 _121855 _121856 a s t i j x) = (term96 _121855 _121856 a s t i j x).
Proof. exact (fun_ext (fun t' : prod _121856 _121855 => @lem5947606 _121855 _121856 a s t i j x t')). Qed.
Lemma lem5947608 {_121855 _121856 : Type'} (i : _121856) (j : _121855) : (@pair _121856 _121855 i j) = (@pair _121856 _121855 i j).
Proof. exact (eq_refl (@pair _121856 _121855 i j)). Qed.
Lemma lem5947609 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term100 _121855 _121856 a s t x i j) = (term98 _121855 _121856 a s t x i j).
Proof. exact (MK_COMB (@lem5947607 _121855 _121856 a s t i j x) (@lem5947608 _121855 _121856 i j)). Qed.
Lemma lem5947610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5947611 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term103 _121855 _121856 a s t x i j) = (term104 _121855 _121856 a s t x i j).
Proof. exact (MK_COMB (@lem5947610) (@lem5947609 _121855 _121856 a s t x i j)). Qed.
Lemma lem5947612 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term98 _121855 _121856 a s t x i j) = (term105 _121855 _121856 a s t x i j).
Proof. exact (eq_refl (term98 _121855 _121856 a s t x i j)). Qed.
Lemma lem5947613 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : ((term100 _121855 _121856 a s t x i j) = (term98 _121855 _121856 a s t x i j)) = ((term98 _121855 _121856 a s t x i j) = (term105 _121855 _121856 a s t x i j)).
Proof. exact (MK_COMB (@lem5947611 _121855 _121856 a s t x i j) (@lem5947612 _121855 _121856 a s t x i j)). Qed.
Lemma lem5947614 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term98 _121855 _121856 a s t x i j) = (term105 _121855 _121856 a s t x i j).
Proof. exact (EQ_MP (@lem5947613 _121855 _121856 a s t x i j) (@lem5947605 _121855 _121856 a s t x i j)). Qed.
Lemma lem5947625 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term97 _121855 _121856 x a s t i j) = (term105 _121855 _121856 a s t x i j).
Proof. exact (TRANS (@lem5947601 _121855 _121856 a s t x i j) (@lem5947614 _121855 _121856 a s t x i j)). Qed.
Lemma lem5947626 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term106 _121855 _121856 x a s t i) = (term107 _121855 _121856 a s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5947625 _121855 _121856 a s t x i j)). Qed.
Lemma lem5947627 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5947628 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term108 _121855 _121856 x a s t i) = (term109 _121855 _121856 a s t x i).
Proof. exact (MK_COMB (@lem5947627 _121855) (@lem5947626 _121855 _121856 a s t x i)). Qed.
Lemma lem5947633 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term110 _121855 _121856 x a s t) = (term111 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5947628 _121855 _121856 a s t x i)). Qed.
Lemma lem5947634 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5947635 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term71 _121855 _121856 x a s t) = (term112 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5947634 _121856) (@lem5947633 _121855 _121856 a s t x)). Qed.
Lemma lem5947640 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term68 _121855 _121856 x a s t) = (term112 _121855 _121856 a s t x).
Proof. exact (TRANS (@lem5947538 _121855 _121856 x a s t) (@lem5947635 _121855 _121856 a s t x)). Qed.
Lemma lem5947641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5947642 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term70 _121855 _121856 x a s t) = (term113 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5947641) (@lem5947640 _121855 _121856 a s t x)). Qed.
Lemma lem5947644 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term114 A x s t) = (term115 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem5947645 {_121855 _121856 : Type'} (s : type1223 _121855 _121856) (x : prod _121856 _121855) (t : type1223 _121855 _121856) : (term116 _121855 _121856 x s t) = (term117 _121855 _121856 s x t).
Proof. exact (@lem5947644 (prod _121856 _121855) s x t). Qed.
Lemma lem5947646 {_121855 _121856 : Type'} (a : _121856) (x : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term118 _121855 _121856 x a s t) = (term119 _121855 _121856 a x s t).
Proof. exact (@lem5947645 _121855 _121856 (term120 _121855 _121856 t a) x (term121 _121855 _121856 s t)). Qed.
Lemma lem5947650 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term38 A B y f s) = (term39 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5947651 {_121855 _121856 : Type'} (y : prod _121856 _121855) (f : type1429 _121855 _121856) (s : _121855 -> Prop) : (term122 _121855 _121856 y f s) = (term123 _121855 _121856 y f s).
Proof. exact (@lem5947650 _121855 (prod _121856 _121855) y f s). Qed.
Lemma lem5947652 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term124 _121855 _121856 x t a) = (term125 _121855 _121856 x t a).
Proof. exact (@lem5947651 _121855 _121856 x (term126 _121855 _121856 a) (t a)). Qed.
Lemma lem5947662 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5947663 {_121855 _121856 : Type'} (f : type1429 _121855 _121856) (y : _121855) : (term127 _121855 _121856 f y) = (f y).
Proof. exact (@lem5947662 _121855 (prod _121856 _121855) f y). Qed.
Lemma lem5947664 {_121855 _121856 : Type'} (a : _121856) (x : _121855) : (term128 _121855 _121856 a x) = (term129 _121855 _121856 a x).
Proof. exact (@lem5947663 _121855 _121856 (term126 _121855 _121856 a) x). Qed.
Lemma lem5947665 {_121855 _121856 : Type'} (a : _121856) (j : _121855) : (term129 _121855 _121856 a j) = (@pair _121856 _121855 a j).
Proof. exact (eq_refl (term129 _121855 _121856 a j)). Qed.
Lemma lem5947666 {_121855 _121856 : Type'} (a : _121856) : (term130 _121855 _121856 a) = (term126 _121855 _121856 a).
Proof. exact (fun_ext (fun j : _121855 => @lem5947665 _121855 _121856 a j)). Qed.
Lemma lem5947667 {_121855 : Type'} (x : _121855) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5947668 {_121855 _121856 : Type'} (a : _121856) (x : _121855) : (term128 _121855 _121856 a x) = (term129 _121855 _121856 a x).
Proof. exact (MK_COMB (@lem5947666 _121855 _121856 a) (@lem5947667 _121855 x)). Qed.
Lemma lem5947669 {_121855 _121856 : Type'} : (@eq (prod _121856 _121855)) = (@eq (prod _121856 _121855)).
Proof. exact (eq_refl (@eq (prod _121856 _121855))). Qed.
Lemma lem5947670 {_121855 _121856 : Type'} (a : _121856) (x : _121855) : (term131 _121855 _121856 a x) = (term132 _121855 _121856 a x).
Proof. exact (MK_COMB (@lem5947669 _121855 _121856) (@lem5947668 _121855 _121856 a x)). Qed.
Lemma lem5947671 {_121855 _121856 : Type'} (a : _121856) (x : _121855) : (term129 _121855 _121856 a x) = (@pair _121856 _121855 a x).
Proof. exact (eq_refl (term129 _121855 _121856 a x)). Qed.
Lemma lem5947672 {_121855 _121856 : Type'} (a : _121856) (x : _121855) : ((term128 _121855 _121856 a x) = (term129 _121855 _121856 a x)) = ((term129 _121855 _121856 a x) = (@pair _121856 _121855 a x)).
Proof. exact (MK_COMB (@lem5947670 _121855 _121856 a x) (@lem5947671 _121855 _121856 a x)). Qed.
Lemma lem5947673 {_121855 _121856 : Type'} (a : _121856) (x : _121855) : (term129 _121855 _121856 a x) = (@pair _121856 _121855 a x).
Proof. exact (EQ_MP (@lem5947672 _121855 _121856 a x) (@lem5947664 _121855 _121856 a x)). Qed.
Lemma lem5947674 {_121855 _121856 : Type'} (x : prod _121856 _121855) : (@eq (prod _121856 _121855) x) = (@eq (prod _121856 _121855) x).
Proof. exact (eq_refl (@eq (prod _121856 _121855) x)). Qed.
Lemma lem5947675 {_121855 _121856 : Type'} (x : prod _121856 _121855) (a : _121856) (x' : _121855) : (x = (term129 _121855 _121856 a x')) = (x = (@pair _121856 _121855 a x')).
Proof. exact (MK_COMB (@lem5947674 _121855 _121856 x) (@lem5947673 _121855 _121856 a x')). Qed.
Lemma lem5947678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5947679 {_121855 _121856 : Type'} (x : prod _121856 _121855) (a : _121856) (x' : _121855) : (term133 _121855 _121856 x a x') = (term134 _121855 _121856 x a x').
Proof. exact (MK_COMB (@lem5947678) (@lem5947675 _121855 _121856 x a x')). Qed.
Lemma lem5947681 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5947682 {_121855 : Type'} (P : _121855 -> Prop) (x : _121855) : (@IN _121855 x P) = (P x).
Proof. exact (@lem5947681 _121855 P x). Qed.
Lemma lem5947683 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (x : _121855) : (term90 _121855 _121856 x t a) = (t a x).
Proof. exact (@lem5947682 _121855 (t a) x). Qed.
Lemma lem5947684 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term135 _121855 _121856 x x' t a) = (term136 _121855 _121856 x t a x').
Proof. exact (MK_COMB (@lem5947679 _121855 _121856 x a x') (@lem5947683 _121855 _121856 t a x')). Qed.
Lemma lem5947687 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term137 _121855 _121856 x t a) = (term138 _121855 _121856 x t a).
Proof. exact (fun_ext (fun x' : _121855 => @lem5947684 _121855 _121856 x t a x')). Qed.
Lemma lem5947688 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5947689 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term125 _121855 _121856 x t a) = (term139 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5947688 _121855) (@lem5947687 _121855 _121856 x t a)). Qed.
Lemma lem5947694 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term124 _121855 _121856 x t a) = (term139 _121855 _121856 x t a).
Proof. exact (TRANS (@lem5947652 _121855 _121856 x t a) (@lem5947689 _121855 _121856 x t a)). Qed.
Lemma lem5947695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5947696 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term140 _121855 _121856 x t a) = (term141 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5947695) (@lem5947694 _121855 _121856 x t a)). Qed.
Lemma lem5947698 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term21 _83064 x P) = (term22 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem5947699 {_121855 _121856 : Type'} (P : type916 _121855 _121856) (x : prod _121856 _121855) : (term58 _121855 _121856 x P) = (term59 _121855 _121856 P x).
Proof. exact (@lem5947698 (prod _121856 _121855) P x). Qed.
Lemma lem5947700 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term142 _121855 _121856 x s t) = (term143 _121855 _121856 s t x).
Proof. exact (@lem5947699 _121855 _121856 (term144 _121855 _121856 s t) x). Qed.
Lemma lem5947701 {_121855 _121856 : Type'} (GEN_PVAR_239 : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term145 _121855 _121856 s t GEN_PVAR_239) = (term146 _121855 _121856 GEN_PVAR_239 s t).
Proof. exact (eq_refl (term145 _121855 _121856 s t GEN_PVAR_239)). Qed.
Lemma lem5947702 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term147 _121855 _121856 s t) = (term148 _121855 _121856 s t).
Proof. exact (fun_ext (fun GEN_PVAR_239 : prod _121856 _121855 => @lem5947701 _121855 _121856 GEN_PVAR_239 s t)). Qed.
Lemma lem5947703 {_121855 _121856 : Type'} : (@GSPEC (prod _121856 _121855)) = (@GSPEC (prod _121856 _121855)).
Proof. exact (eq_refl (@GSPEC (prod _121856 _121855))). Qed.
Lemma lem5947704 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term149 _121855 _121856 s t) = (term121 _121855 _121856 s t).
Proof. exact (MK_COMB (@lem5947703 _121855 _121856) (@lem5947702 _121855 _121856 s t)). Qed.
Lemma lem5947705 {_121855 _121856 : Type'} (x : prod _121856 _121855) : (@IN (prod _121856 _121855) x) = (@IN (prod _121856 _121855) x).
Proof. exact (eq_refl (@IN (prod _121856 _121855) x)). Qed.
Lemma lem5947706 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term142 _121855 _121856 x s t) = (term150 _121855 _121856 x s t).
Proof. exact (MK_COMB (@lem5947705 _121855 _121856 x) (@lem5947704 _121855 _121856 s t)). Qed.
Lemma lem5947707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5947708 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term151 _121855 _121856 x s t) = (term152 _121855 _121856 x s t).
Proof. exact (MK_COMB (@lem5947707) (@lem5947706 _121855 _121856 x s t)). Qed.
Lemma lem5947709 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term143 _121855 _121856 s t x) = (term153 _121855 _121856 x s t).
Proof. exact (eq_refl (term143 _121855 _121856 s t x)). Qed.
Lemma lem5947710 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : ((term142 _121855 _121856 x s t) = (term143 _121855 _121856 s t x)) = ((term150 _121855 _121856 x s t) = (term153 _121855 _121856 x s t)).
Proof. exact (MK_COMB (@lem5947708 _121855 _121856 x s t) (@lem5947709 _121855 _121856 x s t)). Qed.
Lemma lem5947711 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term150 _121855 _121856 x s t) = (term153 _121855 _121856 x s t).
Proof. exact (EQ_MP (@lem5947710 _121855 _121856 x s t) (@lem5947700 _121855 _121856 s t x)). Qed.
Lemma lem5947721 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5947722 {_121855 _121856 : Type'} (f : type1534 _121855 _121856) (y : Prop) : (term73 _121855 _121856 f y) = (f y).
Proof. exact (@lem5947721 Prop (type1223 _121855 _121856) f y). Qed.
Lemma lem5947723 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) : (term154 _121855 _121856 x s j t i) = (term155 _121855 _121856 x s j t i).
Proof. exact (@lem5947722 _121855 _121856 (term76 _121855 _121856 x) (term156 _121855 _121856 s j t i)). Qed.
Lemma lem5947724 {_121855 _121856 : Type'} (p : Prop) (x : prod _121856 _121855) : (term78 _121855 _121856 x p) = (term79 _121855 _121856 p x).
Proof. exact (eq_refl (term78 _121855 _121856 x p)). Qed.
Lemma lem5947725 {_121855 _121856 : Type'} (x : prod _121856 _121855) : (term80 _121855 _121856 x) = (term76 _121855 _121856 x).
Proof. exact (fun_ext (fun p : Prop => @lem5947724 _121855 _121856 p x)). Qed.
Lemma lem5947726 {_121855 _121856 : Type'} (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) : (term156 _121855 _121856 s j t i) = (term156 _121855 _121856 s j t i).
Proof. exact (eq_refl (term156 _121855 _121856 s j t i)). Qed.
Lemma lem5947727 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) : (term154 _121855 _121856 x s j t i) = (term155 _121855 _121856 x s j t i).
Proof. exact (MK_COMB (@lem5947725 _121855 _121856 x) (@lem5947726 _121855 _121856 s j t i)). Qed.
Lemma lem5947728 {_121855 _121856 : Type'} : (@eq ((prod _121856 _121855) -> Prop)) = (@eq ((prod _121856 _121855) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _121856 _121855) -> Prop))). Qed.
Lemma lem5947729 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) : (term157 _121855 _121856 x s j t i) = (term158 _121855 _121856 x s j t i).
Proof. exact (MK_COMB (@lem5947728 _121855 _121856) (@lem5947727 _121855 _121856 x s j t i)). Qed.
Lemma lem5947730 {_121855 _121856 : Type'} (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) (x : prod _121856 _121855) : (term155 _121855 _121856 x s j t i) = (term159 _121855 _121856 s j t i x).
Proof. exact (eq_refl (term155 _121855 _121856 x s j t i)). Qed.
Lemma lem5947731 {_121855 _121856 : Type'} (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) (x : prod _121856 _121855) : ((term154 _121855 _121856 x s j t i) = (term155 _121855 _121856 x s j t i)) = ((term155 _121855 _121856 x s j t i) = (term159 _121855 _121856 s j t i x)).
Proof. exact (MK_COMB (@lem5947729 _121855 _121856 x s j t i) (@lem5947730 _121855 _121856 s j t i x)). Qed.
Lemma lem5947732 {_121855 _121856 : Type'} (s : _121856 -> Prop) (j : _121855) (t : type1470 _121855 _121856) (i : _121856) (x : prod _121856 _121855) : (term155 _121855 _121856 x s j t i) = (term159 _121855 _121856 s j t i x).
Proof. exact (EQ_MP (@lem5947731 _121855 _121856 s j t i x) (@lem5947723 _121855 _121856 x s j t i)). Qed.
Lemma lem5947738 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5947739 {_121856 : Type'} (P : _121856 -> Prop) (x : _121856) : (@IN _121856 x P) = (P x).
Proof. exact (@lem5947738 _121856 P x). Qed.
Lemma lem5947740 {_121856 : Type'} (s : _121856 -> Prop) (i : _121856) : (@IN _121856 i s) = (s i).
Proof. exact (@lem5947739 _121856 s i). Qed.
Lemma lem5947741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5947742 {_121856 : Type'} (s : _121856 -> Prop) (i : _121856) : (term160 _121856 i s) = (term161 _121856 s i).
Proof. exact (MK_COMB (@lem5947741) (@lem5947740 _121856 s i)). Qed.
Lemma lem5947744 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5947745 {_121855 : Type'} (P : _121855 -> Prop) (x : _121855) : (@IN _121855 x P) = (P x).
Proof. exact (@lem5947744 _121855 P x). Qed.
Lemma lem5947746 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term90 _121855 _121856 j t i) = (t i j).
Proof. exact (@lem5947745 _121855 (t i) j). Qed.
Lemma lem5947747 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term156 _121855 _121856 s j t i) = (term162 _121855 _121856 s t i j).
Proof. exact (MK_COMB (@lem5947742 _121856 s i) (@lem5947746 _121855 _121856 t i j)). Qed.
Lemma lem5947750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5947751 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term163 _121855 _121856 s j t i) = (term164 _121855 _121856 s t i j).
Proof. exact (MK_COMB (@lem5947750) (@lem5947747 _121855 _121856 s t i j)). Qed.
Lemma lem5947754 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : prod _121856 _121855) : (x = t) = (x = t).
Proof. exact (eq_refl (x = t)). Qed.
Lemma lem5947755 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (x : prod _121856 _121855) (t' : prod _121856 _121855) : (term165 _121855 _121856 s j t i x t') = (term166 _121855 _121856 s t i j x t').
Proof. exact (MK_COMB (@lem5947751 _121855 _121856 s t i j) (@lem5947754 _121855 _121856 x t')). Qed.
Lemma lem5947758 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (x : prod _121856 _121855) : (term159 _121855 _121856 s j t i x) = (term167 _121855 _121856 s t i j x).
Proof. exact (fun_ext (fun t' : prod _121856 _121855 => @lem5947755 _121855 _121856 s t i j x t')). Qed.
Lemma lem5947759 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (x : prod _121856 _121855) : (term155 _121855 _121856 x s j t i) = (term167 _121855 _121856 s t i j x).
Proof. exact (TRANS (@lem5947732 _121855 _121856 s j t i x) (@lem5947758 _121855 _121856 s t i j x)). Qed.
Lemma lem5947760 {_121855 _121856 : Type'} (i : _121856) (j : _121855) : (@pair _121856 _121855 i j) = (@pair _121856 _121855 i j).
Proof. exact (eq_refl (@pair _121856 _121855 i j)). Qed.
Lemma lem5947761 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term168 _121855 _121856 x s t i j) = (term169 _121855 _121856 s t x i j).
Proof. exact (MK_COMB (@lem5947759 _121855 _121856 s t i j x) (@lem5947760 _121855 _121856 i j)). Qed.
Lemma lem5947763 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5947764 {_121855 _121856 : Type'} (f : type1223 _121855 _121856) (y : prod _121856 _121855) : (term99 _121855 _121856 f y) = (f y).
Proof. exact (@lem5947763 (prod _121856 _121855) Prop f y). Qed.
Lemma lem5947765 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term170 _121855 _121856 s t x i j) = (term169 _121855 _121856 s t x i j).
Proof. exact (@lem5947764 _121855 _121856 (term167 _121855 _121856 s t i j x) (@pair _121856 _121855 i j)). Qed.
Lemma lem5947766 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (x : prod _121856 _121855) (t' : prod _121856 _121855) : (term171 _121855 _121856 s t i j x t') = (term166 _121855 _121856 s t i j x t').
Proof. exact (eq_refl (term171 _121855 _121856 s t i j x t')). Qed.
Lemma lem5947767 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (x : prod _121856 _121855) : (term172 _121855 _121856 s t i j x) = (term167 _121855 _121856 s t i j x).
Proof. exact (fun_ext (fun t' : prod _121856 _121855 => @lem5947766 _121855 _121856 s t i j x t')). Qed.
Lemma lem5947768 {_121855 _121856 : Type'} (i : _121856) (j : _121855) : (@pair _121856 _121855 i j) = (@pair _121856 _121855 i j).
Proof. exact (eq_refl (@pair _121856 _121855 i j)). Qed.
Lemma lem5947769 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term170 _121855 _121856 s t x i j) = (term169 _121855 _121856 s t x i j).
Proof. exact (MK_COMB (@lem5947767 _121855 _121856 s t i j x) (@lem5947768 _121855 _121856 i j)). Qed.
Lemma lem5947770 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5947771 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term173 _121855 _121856 s t x i j) = (term174 _121855 _121856 s t x i j).
Proof. exact (MK_COMB (@lem5947770) (@lem5947769 _121855 _121856 s t x i j)). Qed.
Lemma lem5947772 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term169 _121855 _121856 s t x i j) = (term175 _121855 _121856 s t x i j).
Proof. exact (eq_refl (term169 _121855 _121856 s t x i j)). Qed.
Lemma lem5947773 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : ((term170 _121855 _121856 s t x i j) = (term169 _121855 _121856 s t x i j)) = ((term169 _121855 _121856 s t x i j) = (term175 _121855 _121856 s t x i j)).
Proof. exact (MK_COMB (@lem5947771 _121855 _121856 s t x i j) (@lem5947772 _121855 _121856 s t x i j)). Qed.
Lemma lem5947774 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term169 _121855 _121856 s t x i j) = (term175 _121855 _121856 s t x i j).
Proof. exact (EQ_MP (@lem5947773 _121855 _121856 s t x i j) (@lem5947765 _121855 _121856 s t x i j)). Qed.
Lemma lem5947781 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term168 _121855 _121856 x s t i j) = (term175 _121855 _121856 s t x i j).
Proof. exact (TRANS (@lem5947761 _121855 _121856 s t x i j) (@lem5947774 _121855 _121856 s t x i j)). Qed.
Lemma lem5947782 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term176 _121855 _121856 x s t i) = (term177 _121855 _121856 s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5947781 _121855 _121856 s t x i j)). Qed.
Lemma lem5947783 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5947784 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term178 _121855 _121856 x s t i) = (term179 _121855 _121856 s t x i).
Proof. exact (MK_COMB (@lem5947783 _121855) (@lem5947782 _121855 _121856 s t x i)). Qed.
Lemma lem5947789 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term180 _121855 _121856 x s t) = (term181 _121855 _121856 s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5947784 _121855 _121856 s t x i)). Qed.
Lemma lem5947790 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5947791 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term153 _121855 _121856 x s t) = (term182 _121855 _121856 s t x).
Proof. exact (MK_COMB (@lem5947790 _121856) (@lem5947789 _121855 _121856 s t x)). Qed.
Lemma lem5947796 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term150 _121855 _121856 x s t) = (term182 _121855 _121856 s t x).
Proof. exact (TRANS (@lem5947711 _121855 _121856 x s t) (@lem5947791 _121855 _121856 s t x)). Qed.
Lemma lem5947797 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term119 _121855 _121856 a x s t) = (term183 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5947696 _121855 _121856 x t a) (@lem5947796 _121855 _121856 s t x)). Qed.
Lemma lem5947800 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term118 _121855 _121856 x a s t) = (term183 _121855 _121856 a s t x).
Proof. exact (TRANS (@lem5947646 _121855 _121856 a x s t) (@lem5947797 _121855 _121856 a s t x)). Qed.
Lemma lem5947801 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term68 _121855 _121856 x a s t) = (term118 _121855 _121856 x a s t)) = ((term112 _121855 _121856 a s t x) = (term183 _121855 _121856 a s t x)).
Proof. exact (MK_COMB (@lem5947642 _121855 _121856 a s t x) (@lem5947800 _121855 _121856 a s t x)). Qed.
Lemma lem5947804 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term184 _121855 _121856 a s t) = (term185 _121855 _121856 a s t).
Proof. exact (fun_ext (fun x : prod _121856 _121855 => @lem5947801 _121855 _121856 a s t x)). Qed.
Lemma lem5947805 {_121855 _121856 : Type'} : (@all (prod _121856 _121855)) = (@all (prod _121856 _121855)).
Proof. exact (eq_refl (@all (prod _121856 _121855))). Qed.
Lemma lem5947806 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term57 _121855 _121856 a s t) = (term186 _121855 _121856 a s t).
Proof. exact (MK_COMB (@lem5947805 _121855 _121856) (@lem5947804 _121855 _121856 a s t)). Qed.
Lemma lem5947811 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term186 _121855 _121856 a s t) = (term57 _121855 _121856 a s t).
Proof. exact (SYM (@lem5947806 _121855 _121856 a s t)). Qed.
Lemma lem5947813 (p : Prop) : p = (term187 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5947814 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term186 _121855 _121856 a s t) = (term188 _121855 _121856 a s t).
Proof. exact (@lem5947813 (term186 _121855 _121856 a s t)). Qed.
Lemma lem5947815 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term188 _121855 _121856 a s t) = (term186 _121855 _121856 a s t).
Proof. exact (SYM (@lem5947814 _121855 _121856 a s t)). Qed.
Lemma lem5947816 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (h1 : term189 _121855 _121856 a s t) : term189 _121855 _121856 a s t.
Proof. exact (h1). Qed.
Lemma lem5947819 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (h1 : term188 _121855 _121856 a s t) : term188 _121855 _121856 a s t.
Proof. exact (h1). Qed.
Lemma lem5947820 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : term190 _121855 _121856 a s t.
Proof. exact (fun h0 : term188 _121855 _121856 a s t => @lem5947819 _121855 _121856 a s t h0). Qed.
Lemma lem5947821 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (h1 : term190 _121855 _121856 a s t) : term190 _121855 _121856 a s t.
Proof. exact (h1). Qed.
Lemma lem5947822 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (h1 : term188 _121855 _121856 a s t) : term188 _121855 _121856 a s t.
Proof. exact (h1). Qed.
Lemma lem5947823 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (h1 : term188 _121855 _121856 a s t) (h2 : term190 _121855 _121856 a s t) : term188 _121855 _121856 a s t.
Proof. exact (@lem5947821 _121855 _121856 a s t h2 (@lem5947822 _121855 _121856 a s t h1)). Qed.
Lemma lem5947824 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (h1 : term188 _121855 _121856 a s t) : term191 _121855 _121856 a s t.
Proof. exact (fun h0 : term190 _121855 _121856 a s t => @lem5947823 _121855 _121856 a s t h1 h0). Qed.
Lemma lem5947825 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (h1 : term190 _121855 _121856 a s t) : term190 _121855 _121856 a s t.
Proof. exact (h1). Qed.
Lemma lem5947826 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (h1 : term188 _121855 _121856 a s t) (h2 : term190 _121855 _121856 a s t) : term188 _121855 _121856 a s t.
Proof. exact (@lem5947824 _121855 _121856 a s t h1 (@lem5947825 _121855 _121856 a s t h2)). Qed.
Lemma lem5947827 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (h1 : term190 _121855 _121856 a s t) : term190 _121855 _121856 a s t.
Proof. exact (fun h0 : term188 _121855 _121856 a s t => @lem5947826 _121855 _121856 a s t h0 h1). Qed.
Lemma lem5947828 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : term192 _121855 _121856 a s t.
Proof. exact (fun h0 : term190 _121855 _121856 a s t => @lem5947827 _121855 _121856 a s t h0). Qed.
Lemma lem5947831 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : term190 _121855 _121856 a s t.
Proof. exact (@lem5947828 _121855 _121856 a s t (@lem5947820 _121855 _121856 a s t)). Qed.
Lemma lem5947832 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : term190 _121855 _121856 a s t.
Proof. exact (@lem5947831 _121855 _121856 a s t). Qed.
Lemma lem5947846 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5947847 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term188 _121855 _121856 a s t) = (term193 _121855 _121856 a s t).
Proof. exact (@lem5947846 (term189 _121855 _121856 a s t)). Qed.
Lemma lem5947849 (t : Prop) : (term194 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5947850 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term193 _121855 _121856 a s t) = (term186 _121855 _121856 a s t).
Proof. exact (@lem5947849 (term186 _121855 _121856 a s t)). Qed.
Lemma lem5947855 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term188 _121855 _121856 a s t) = (term186 _121855 _121856 a s t).
Proof. exact (TRANS (@lem5947847 _121855 _121856 a s t) (@lem5947850 _121855 _121856 a s t)). Qed.
Lemma lem5948022 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term195 _121855 _121856 s t) = (term196 _121855 _121856 s t).
Proof. exact (fun_ext (fun a : _121856 => @lem5947855 _121855 _121856 a s t)). Qed.
Lemma lem5948023 {_121856 : Type'} : (@all _121856) = (@all _121856).
Proof. exact (eq_refl (@all _121856)). Qed.
Lemma lem5948024 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term197 _121855 _121856 s t) = (term198 _121855 _121856 s t).
Proof. exact (MK_COMB (@lem5948023 _121856) (@lem5948022 _121855 _121856 s t)). Qed.
Lemma lem5948029 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) : (term199 _121855 _121856 t) = (term200 _121855 _121856 t).
Proof. exact (fun_ext (fun s : _121856 -> Prop => @lem5948024 _121855 _121856 s t)). Qed.
Lemma lem5948030 {_121856 : Type'} : (@all (_121856 -> Prop)) = (@all (_121856 -> Prop)).
Proof. exact (eq_refl (@all (_121856 -> Prop))). Qed.
Lemma lem5948031 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) : (term201 _121855 _121856 t) = (term202 _121855 _121856 t).
Proof. exact (MK_COMB (@lem5948030 _121856) (@lem5948029 _121855 _121856 t)). Qed.
Lemma lem5948036 {_121855 _121856 : Type'} : (term203 _121855 _121856) = (term204 _121855 _121856).
Proof. exact (fun_ext (fun t : type1470 _121855 _121856 => @lem5948031 _121855 _121856 t)). Qed.
Lemma lem5948037 {_121855 _121856 : Type'} : (@all (_121856 -> _121855 -> Prop)) = (@all (_121856 -> _121855 -> Prop)).
Proof. exact (eq_refl (@all (_121856 -> _121855 -> Prop))). Qed.
Lemma lem5948046 {_121855 _121856 : Type'} : (term205 _121855 _121856) = (term206 _121855 _121856).
Proof. exact (MK_COMB (@lem5948037 _121855 _121856) (@lem5948036 _121855 _121856)). Qed.
Lemma lem5948055 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term175 _121855 _121856 s t x i j) = (term175 _121855 _121856 s t x i j).
Proof. exact (eq_refl (term175 _121855 _121856 s t x i j)). Qed.
Lemma lem5948056 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term177 _121855 _121856 s t x i) = (term177 _121855 _121856 s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5948055 _121855 _121856 s t x i j)). Qed.
Lemma lem5948057 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948058 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term179 _121855 _121856 s t x i) = (term179 _121855 _121856 s t x i).
Proof. exact (MK_COMB (@lem5948057 _121855) (@lem5948056 _121855 _121856 s t x i)). Qed.
Lemma lem5948059 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term181 _121855 _121856 s t x) = (term181 _121855 _121856 s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948058 _121855 _121856 s t x i)). Qed.
Lemma lem5948060 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948061 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term182 _121855 _121856 s t x) = (term182 _121855 _121856 s t x).
Proof. exact (MK_COMB (@lem5948060 _121856) (@lem5948059 _121855 _121856 s t x)). Qed.
Lemma lem5948066 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term136 _121855 _121856 x t a x') = (term136 _121855 _121856 x t a x').
Proof. exact (eq_refl (term136 _121855 _121856 x t a x')). Qed.
Lemma lem5948067 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term138 _121855 _121856 x t a) = (term138 _121855 _121856 x t a).
Proof. exact (fun_ext (fun x' : _121855 => @lem5948066 _121855 _121856 x t a x')). Qed.
Lemma lem5948068 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948069 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term139 _121855 _121856 x t a) = (term139 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5948068 _121855) (@lem5948067 _121855 _121856 x t a)). Qed.
Lemma lem5948070 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948071 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term141 _121855 _121856 x t a) = (term141 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5948070) (@lem5948069 _121855 _121856 x t a)). Qed.
Lemma lem5948072 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term183 _121855 _121856 a s t x) = (term183 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948071 _121855 _121856 x t a) (@lem5948061 _121855 _121856 s t x)). Qed.
Lemma lem5948085 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term105 _121855 _121856 a s t x i j) = (term105 _121855 _121856 a s t x i j).
Proof. exact (eq_refl (term105 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948086 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term107 _121855 _121856 a s t x i) = (term107 _121855 _121856 a s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5948085 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948087 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948088 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term109 _121855 _121856 a s t x i) = (term109 _121855 _121856 a s t x i).
Proof. exact (MK_COMB (@lem5948087 _121855) (@lem5948086 _121855 _121856 a s t x i)). Qed.
Lemma lem5948089 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term111 _121855 _121856 a s t x) = (term111 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948088 _121855 _121856 a s t x i)). Qed.
Lemma lem5948090 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948091 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term112 _121855 _121856 a s t x) = (term112 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948090 _121856) (@lem5948089 _121855 _121856 a s t x)). Qed.
Lemma lem5948092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948093 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term113 _121855 _121856 a s t x) = (term113 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948092) (@lem5948091 _121855 _121856 a s t x)). Qed.
Lemma lem5948094 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term112 _121855 _121856 a s t x) = (term183 _121855 _121856 a s t x)) = ((term112 _121855 _121856 a s t x) = (term183 _121855 _121856 a s t x)).
Proof. exact (MK_COMB (@lem5948093 _121855 _121856 a s t x) (@lem5948072 _121855 _121856 a s t x)). Qed.
Lemma lem5948095 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term185 _121855 _121856 a s t) = (term185 _121855 _121856 a s t).
Proof. exact (fun_ext (fun x : prod _121856 _121855 => @lem5948094 _121855 _121856 a s t x)). Qed.
Lemma lem5948096 {_121855 _121856 : Type'} : (@all (prod _121856 _121855)) = (@all (prod _121856 _121855)).
Proof. exact (eq_refl (@all (prod _121856 _121855))). Qed.
Lemma lem5948097 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term186 _121855 _121856 a s t) = (term186 _121855 _121856 a s t).
Proof. exact (MK_COMB (@lem5948096 _121855 _121856) (@lem5948095 _121855 _121856 a s t)). Qed.
Lemma lem5948098 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term196 _121855 _121856 s t) = (term196 _121855 _121856 s t).
Proof. exact (fun_ext (fun a : _121856 => @lem5948097 _121855 _121856 a s t)). Qed.
Lemma lem5948099 {_121856 : Type'} : (@all _121856) = (@all _121856).
Proof. exact (eq_refl (@all _121856)). Qed.
Lemma lem5948100 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term198 _121855 _121856 s t) = (term198 _121855 _121856 s t).
Proof. exact (MK_COMB (@lem5948099 _121856) (@lem5948098 _121855 _121856 s t)). Qed.
Lemma lem5948101 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) : (term200 _121855 _121856 t) = (term200 _121855 _121856 t).
Proof. exact (fun_ext (fun s : _121856 -> Prop => @lem5948100 _121855 _121856 s t)). Qed.
Lemma lem5948102 {_121856 : Type'} : (@all (_121856 -> Prop)) = (@all (_121856 -> Prop)).
Proof. exact (eq_refl (@all (_121856 -> Prop))). Qed.
Lemma lem5948103 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) : (term202 _121855 _121856 t) = (term202 _121855 _121856 t).
Proof. exact (MK_COMB (@lem5948102 _121856) (@lem5948101 _121855 _121856 t)). Qed.
Lemma lem5948104 {_121855 _121856 : Type'} : (term204 _121855 _121856) = (term204 _121855 _121856).
Proof. exact (fun_ext (fun t : type1470 _121855 _121856 => @lem5948103 _121855 _121856 t)). Qed.
Lemma lem5948105 {_121855 _121856 : Type'} : (@all (_121856 -> _121855 -> Prop)) = (@all (_121856 -> _121855 -> Prop)).
Proof. exact (eq_refl (@all (_121856 -> _121855 -> Prop))). Qed.
Lemma lem5948106 {_121855 _121856 : Type'} : (term206 _121855 _121856) = (term206 _121855 _121856).
Proof. exact (MK_COMB (@lem5948105 _121855 _121856) (@lem5948104 _121855 _121856)). Qed.
Lemma lem5948177 {_121855 _121856 : Type'} : (term205 _121855 _121856) = (term206 _121855 _121856).
Proof. exact (TRANS (@lem5948046 _121855 _121856) (@lem5948106 _121855 _121856)). Qed.
Lemma lem5948178 {_121855 _121856 : Type'} : (term206 _121855 _121856) = (term205 _121855 _121856).
Proof. exact (SYM (@lem5948177 _121855 _121856)). Qed.
Lemma lem5948180 (p : Prop) : p = (term187 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5948181 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term112 _121855 _121856 a s t x) = (term183 _121855 _121856 a s t x)) = (term207 _121855 _121856 a s t x).
Proof. exact (@lem5948180 ((term112 _121855 _121856 a s t x) = (term183 _121855 _121856 a s t x))). Qed.
Lemma lem5948182 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term207 _121855 _121856 a s t x) = ((term112 _121855 _121856 a s t x) = (term183 _121855 _121856 a s t x)).
Proof. exact (SYM (@lem5948181 _121855 _121856 a s t x)). Qed.
Lemma lem5948183 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term208 _121855 _121856 a s t x) : term208 _121855 _121856 a s t x.
Proof. exact (h1). Qed.
Lemma lem5948192 {_121856 : Type'} (a : _121856) (s : _121856 -> Prop) (i : _121856) : (term209 _121856 a s i) = (term210 _121856 a s i).
Proof. exact (@lem17160 (i = a) (s i)). Qed.
Lemma lem5948196 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term211 _121855 _121856 t i j) = (term211 _121855 _121856 t i j).
Proof. exact (eq_refl (term211 _121855 _121856 t i j)). Qed.
Lemma lem5948198 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948199 {_121856 : Type'} (a : _121856) (s : _121856 -> Prop) (i : _121856) : (term212 _121856 a s i) = (term213 _121856 a s i).
Proof. exact (MK_COMB (@lem5948198) (@lem5948192 _121856 a s i)). Qed.
Lemma lem5948200 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term214 _121855 _121856 a s t i j) = (term215 _121855 _121856 a s t i j).
Proof. exact (MK_COMB (@lem5948199 _121856 a s i) (@lem5948196 _121855 _121856 t i j)). Qed.
Lemma lem5948201 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term216 _121855 _121856 a s t i j) = (term214 _121855 _121856 a s t i j).
Proof. exact (@lem17045 (term87 _121856 a s i) (t i j)). Qed.
Lemma lem5948202 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term216 _121855 _121856 a s t i j) = (term215 _121855 _121856 a s t i j).
Proof. exact (TRANS (@lem5948201 _121855 _121856 a s t i j) (@lem5948200 _121855 _121856 a s t i j)). Qed.
Lemma lem5948206 {_121855 _121856 : Type'} (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term217 _121855 _121856 x i j) = (term217 _121855 _121856 x i j).
Proof. exact (eq_refl (term217 _121855 _121856 x i j)). Qed.
Lemma lem5948208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948209 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term218 _121855 _121856 a s t i j) = (term219 _121855 _121856 a s t i j).
Proof. exact (MK_COMB (@lem5948208) (@lem5948202 _121855 _121856 a s t i j)). Qed.
Lemma lem5948210 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term220 _121855 _121856 a s t x i j) = (term221 _121855 _121856 a s t x i j).
Proof. exact (MK_COMB (@lem5948209 _121855 _121856 a s t i j) (@lem5948206 _121855 _121856 x i j)). Qed.
Lemma lem5948211 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term222 _121855 _121856 a s t x i j) = (term220 _121855 _121856 a s t x i j).
Proof. exact (@lem17045 (term91 _121855 _121856 a s t i j) (x = (@pair _121856 _121855 i j))). Qed.
Lemma lem5948212 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term222 _121855 _121856 a s t x i j) = (term221 _121855 _121856 a s t x i j).
Proof. exact (TRANS (@lem5948211 _121855 _121856 a s t x i j) (@lem5948210 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948215 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term105 _121855 _121856 a s t x i j) = (term105 _121855 _121856 a s t x i j).
Proof. exact (eq_refl (term105 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948216 {_121855 : Type'} (P : _121855 -> Prop) : (term223 _121855 P) = (term224 _121855 P).
Proof. exact (@lem18394 _121855 P). Qed.
Lemma lem5948217 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term225 _121855 _121856 a s t x i) = (term226 _121855 _121856 a s t x i).
Proof. exact (@lem5948216 _121855 (term107 _121855 _121856 a s t x i)). Qed.
Lemma lem5948218 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term227 _121855 _121856 a s t x i j) = (term105 _121855 _121856 a s t x i j).
Proof. exact (eq_refl (term227 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948219 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5948220 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term228 _121855 _121856 a s t x i j) = (term222 _121855 _121856 a s t x i j).
Proof. exact (MK_COMB (@lem5948219) (@lem5948218 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948221 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term228 _121855 _121856 a s t x i j) = (term221 _121855 _121856 a s t x i j).
Proof. exact (TRANS (@lem5948220 _121855 _121856 a s t x i j) (@lem5948212 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948222 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term229 _121855 _121856 a s t x i) = (term230 _121855 _121856 a s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5948221 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948223 {_121855 : Type'} : (@all _121855) = (@all _121855).
Proof. exact (eq_refl (@all _121855)). Qed.
Lemma lem5948224 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term226 _121855 _121856 a s t x i) = (term231 _121855 _121856 a s t x i).
Proof. exact (MK_COMB (@lem5948223 _121855) (@lem5948222 _121855 _121856 a s t x i)). Qed.
Lemma lem5948225 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term225 _121855 _121856 a s t x i) = (term231 _121855 _121856 a s t x i).
Proof. exact (TRANS (@lem5948217 _121855 _121856 a s t x i) (@lem5948224 _121855 _121856 a s t x i)). Qed.
Lemma lem5948226 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term107 _121855 _121856 a s t x i) = (term107 _121855 _121856 a s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5948215 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948227 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948228 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term109 _121855 _121856 a s t x i) = (term109 _121855 _121856 a s t x i).
Proof. exact (MK_COMB (@lem5948227 _121855) (@lem5948226 _121855 _121856 a s t x i)). Qed.
Lemma lem5948229 {_121856 : Type'} (P : _121856 -> Prop) : (term223 _121856 P) = (term224 _121856 P).
Proof. exact (@lem18394 _121856 P). Qed.
Lemma lem5948230 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term232 _121855 _121856 a s t x) = (term233 _121855 _121856 a s t x).
Proof. exact (@lem5948229 _121856 (term111 _121855 _121856 a s t x)). Qed.
Lemma lem5948231 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term234 _121855 _121856 a s t x i) = (term109 _121855 _121856 a s t x i).
Proof. exact (eq_refl (term234 _121855 _121856 a s t x i)). Qed.
Lemma lem5948232 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5948233 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term235 _121855 _121856 a s t x i) = (term225 _121855 _121856 a s t x i).
Proof. exact (MK_COMB (@lem5948232) (@lem5948231 _121855 _121856 a s t x i)). Qed.
Lemma lem5948234 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term235 _121855 _121856 a s t x i) = (term231 _121855 _121856 a s t x i).
Proof. exact (TRANS (@lem5948233 _121855 _121856 a s t x i) (@lem5948225 _121855 _121856 a s t x i)). Qed.
Lemma lem5948235 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term236 _121855 _121856 a s t x) = (term237 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948234 _121855 _121856 a s t x i)). Qed.
Lemma lem5948236 {_121856 : Type'} : (@all _121856) = (@all _121856).
Proof. exact (eq_refl (@all _121856)). Qed.
Lemma lem5948237 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term233 _121855 _121856 a s t x) = (term238 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948236 _121856) (@lem5948235 _121855 _121856 a s t x)). Qed.
Lemma lem5948238 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term232 _121855 _121856 a s t x) = (term238 _121855 _121856 a s t x).
Proof. exact (TRANS (@lem5948230 _121855 _121856 a s t x) (@lem5948237 _121855 _121856 a s t x)). Qed.
Lemma lem5948239 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term111 _121855 _121856 a s t x) = (term111 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948228 _121855 _121856 a s t x i)). Qed.
Lemma lem5948240 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948241 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term112 _121855 _121856 a s t x) = (term112 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948240 _121856) (@lem5948239 _121855 _121856 a s t x)). Qed.
Lemma lem5948250 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term239 _121855 _121856 x t a x') = (term240 _121855 _121856 x t a x').
Proof. exact (@lem17045 (x = (@pair _121856 _121855 a x')) (t a x')). Qed.
Lemma lem5948253 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term136 _121855 _121856 x t a x') = (term136 _121855 _121856 x t a x').
Proof. exact (eq_refl (term136 _121855 _121856 x t a x')). Qed.
Lemma lem5948254 {_121855 : Type'} (P : _121855 -> Prop) : (term223 _121855 P) = (term224 _121855 P).
Proof. exact (@lem18394 _121855 P). Qed.
Lemma lem5948255 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term241 _121855 _121856 x t a) = (term242 _121855 _121856 x t a).
Proof. exact (@lem5948254 _121855 (term138 _121855 _121856 x t a)). Qed.
Lemma lem5948256 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term243 _121855 _121856 x t a x') = (term136 _121855 _121856 x t a x').
Proof. exact (eq_refl (term243 _121855 _121856 x t a x')). Qed.
Lemma lem5948257 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5948258 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term244 _121855 _121856 x t a x') = (term239 _121855 _121856 x t a x').
Proof. exact (MK_COMB (@lem5948257) (@lem5948256 _121855 _121856 x t a x')). Qed.
Lemma lem5948259 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term244 _121855 _121856 x t a x') = (term240 _121855 _121856 x t a x').
Proof. exact (TRANS (@lem5948258 _121855 _121856 x t a x') (@lem5948250 _121855 _121856 x t a x')). Qed.
Lemma lem5948260 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term245 _121855 _121856 x t a) = (term246 _121855 _121856 x t a).
Proof. exact (fun_ext (fun x' : _121855 => @lem5948259 _121855 _121856 x t a x')). Qed.
Lemma lem5948261 {_121855 : Type'} : (@all _121855) = (@all _121855).
Proof. exact (eq_refl (@all _121855)). Qed.
Lemma lem5948262 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term242 _121855 _121856 x t a) = (term247 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5948261 _121855) (@lem5948260 _121855 _121856 x t a)). Qed.
Lemma lem5948263 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term241 _121855 _121856 x t a) = (term247 _121855 _121856 x t a).
Proof. exact (TRANS (@lem5948255 _121855 _121856 x t a) (@lem5948262 _121855 _121856 x t a)). Qed.
Lemma lem5948264 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term138 _121855 _121856 x t a) = (term138 _121855 _121856 x t a).
Proof. exact (fun_ext (fun x' : _121855 => @lem5948253 _121855 _121856 x t a x')). Qed.
Lemma lem5948265 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948266 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term139 _121855 _121856 x t a) = (term139 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5948265 _121855) (@lem5948264 _121855 _121856 x t a)). Qed.
Lemma lem5948275 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term248 _121855 _121856 s t i j) = (term249 _121855 _121856 s t i j).
Proof. exact (@lem17045 (s i) (t i j)). Qed.
Lemma lem5948279 {_121855 _121856 : Type'} (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term217 _121855 _121856 x i j) = (term217 _121855 _121856 x i j).
Proof. exact (eq_refl (term217 _121855 _121856 x i j)). Qed.
Lemma lem5948281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948282 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term250 _121855 _121856 s t i j) = (term251 _121855 _121856 s t i j).
Proof. exact (MK_COMB (@lem5948281) (@lem5948275 _121855 _121856 s t i j)). Qed.
Lemma lem5948283 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term252 _121855 _121856 s t x i j) = (term253 _121855 _121856 s t x i j).
Proof. exact (MK_COMB (@lem5948282 _121855 _121856 s t i j) (@lem5948279 _121855 _121856 x i j)). Qed.
Lemma lem5948284 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term254 _121855 _121856 s t x i j) = (term252 _121855 _121856 s t x i j).
Proof. exact (@lem17045 (term162 _121855 _121856 s t i j) (x = (@pair _121856 _121855 i j))). Qed.
Lemma lem5948285 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term254 _121855 _121856 s t x i j) = (term253 _121855 _121856 s t x i j).
Proof. exact (TRANS (@lem5948284 _121855 _121856 s t x i j) (@lem5948283 _121855 _121856 s t x i j)). Qed.
Lemma lem5948288 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term175 _121855 _121856 s t x i j) = (term175 _121855 _121856 s t x i j).
Proof. exact (eq_refl (term175 _121855 _121856 s t x i j)). Qed.
Lemma lem5948289 {_121855 : Type'} (P : _121855 -> Prop) : (term223 _121855 P) = (term224 _121855 P).
Proof. exact (@lem18394 _121855 P). Qed.
Lemma lem5948290 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term255 _121855 _121856 s t x i) = (term256 _121855 _121856 s t x i).
Proof. exact (@lem5948289 _121855 (term177 _121855 _121856 s t x i)). Qed.
Lemma lem5948291 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term257 _121855 _121856 s t x i j) = (term175 _121855 _121856 s t x i j).
Proof. exact (eq_refl (term257 _121855 _121856 s t x i j)). Qed.
Lemma lem5948292 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5948293 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term258 _121855 _121856 s t x i j) = (term254 _121855 _121856 s t x i j).
Proof. exact (MK_COMB (@lem5948292) (@lem5948291 _121855 _121856 s t x i j)). Qed.
Lemma lem5948294 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term258 _121855 _121856 s t x i j) = (term253 _121855 _121856 s t x i j).
Proof. exact (TRANS (@lem5948293 _121855 _121856 s t x i j) (@lem5948285 _121855 _121856 s t x i j)). Qed.
Lemma lem5948295 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term259 _121855 _121856 s t x i) = (term260 _121855 _121856 s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5948294 _121855 _121856 s t x i j)). Qed.
Lemma lem5948296 {_121855 : Type'} : (@all _121855) = (@all _121855).
Proof. exact (eq_refl (@all _121855)). Qed.
Lemma lem5948297 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term256 _121855 _121856 s t x i) = (term261 _121855 _121856 s t x i).
Proof. exact (MK_COMB (@lem5948296 _121855) (@lem5948295 _121855 _121856 s t x i)). Qed.
Lemma lem5948298 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term255 _121855 _121856 s t x i) = (term261 _121855 _121856 s t x i).
Proof. exact (TRANS (@lem5948290 _121855 _121856 s t x i) (@lem5948297 _121855 _121856 s t x i)). Qed.
Lemma lem5948299 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term177 _121855 _121856 s t x i) = (term177 _121855 _121856 s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5948288 _121855 _121856 s t x i j)). Qed.
Lemma lem5948300 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948301 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term179 _121855 _121856 s t x i) = (term179 _121855 _121856 s t x i).
Proof. exact (MK_COMB (@lem5948300 _121855) (@lem5948299 _121855 _121856 s t x i)). Qed.
Lemma lem5948302 {_121856 : Type'} (P : _121856 -> Prop) : (term223 _121856 P) = (term224 _121856 P).
Proof. exact (@lem18394 _121856 P). Qed.
Lemma lem5948303 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term262 _121855 _121856 s t x) = (term263 _121855 _121856 s t x).
Proof. exact (@lem5948302 _121856 (term181 _121855 _121856 s t x)). Qed.
Lemma lem5948304 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term264 _121855 _121856 s t x i) = (term179 _121855 _121856 s t x i).
Proof. exact (eq_refl (term264 _121855 _121856 s t x i)). Qed.
Lemma lem5948305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5948306 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term265 _121855 _121856 s t x i) = (term255 _121855 _121856 s t x i).
Proof. exact (MK_COMB (@lem5948305) (@lem5948304 _121855 _121856 s t x i)). Qed.
Lemma lem5948307 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term265 _121855 _121856 s t x i) = (term261 _121855 _121856 s t x i).
Proof. exact (TRANS (@lem5948306 _121855 _121856 s t x i) (@lem5948298 _121855 _121856 s t x i)). Qed.
Lemma lem5948308 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term266 _121855 _121856 s t x) = (term267 _121855 _121856 s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948307 _121855 _121856 s t x i)). Qed.
Lemma lem5948309 {_121856 : Type'} : (@all _121856) = (@all _121856).
Proof. exact (eq_refl (@all _121856)). Qed.
Lemma lem5948310 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term263 _121855 _121856 s t x) = (term268 _121855 _121856 s t x).
Proof. exact (MK_COMB (@lem5948309 _121856) (@lem5948308 _121855 _121856 s t x)). Qed.
Lemma lem5948311 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term262 _121855 _121856 s t x) = (term268 _121855 _121856 s t x).
Proof. exact (TRANS (@lem5948303 _121855 _121856 s t x) (@lem5948310 _121855 _121856 s t x)). Qed.
Lemma lem5948312 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term181 _121855 _121856 s t x) = (term181 _121855 _121856 s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948301 _121855 _121856 s t x i)). Qed.
Lemma lem5948313 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948314 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term182 _121855 _121856 s t x) = (term182 _121855 _121856 s t x).
Proof. exact (MK_COMB (@lem5948313 _121856) (@lem5948312 _121855 _121856 s t x)). Qed.
Lemma lem5948315 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5948316 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term269 _121855 _121856 x t a) = (term270 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5948315) (@lem5948263 _121855 _121856 x t a)). Qed.
Lemma lem5948317 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term271 _121855 _121856 a s t x) = (term272 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948316 _121855 _121856 x t a) (@lem5948311 _121855 _121856 s t x)). Qed.
Lemma lem5948318 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term273 _121855 _121856 a s t x) = (term271 _121855 _121856 a s t x).
Proof. exact (@lem17160 (term139 _121855 _121856 x t a) (term182 _121855 _121856 s t x)). Qed.
Lemma lem5948319 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term273 _121855 _121856 a s t x) = (term272 _121855 _121856 a s t x).
Proof. exact (TRANS (@lem5948318 _121855 _121856 a s t x) (@lem5948317 _121855 _121856 a s t x)). Qed.
Lemma lem5948320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948321 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term141 _121855 _121856 x t a) = (term141 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5948320) (@lem5948266 _121855 _121856 x t a)). Qed.
Lemma lem5948322 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term183 _121855 _121856 a s t x) = (term183 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948321 _121855 _121856 x t a) (@lem5948314 _121855 _121856 s t x)). Qed.
Lemma lem5948323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5948324 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term274 _121855 _121856 a s t x) = (term275 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948323) (@lem5948238 _121855 _121856 a s t x)). Qed.
Lemma lem5948325 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term276 _121855 _121856 a s t x) = (term277 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948324 _121855 _121856 a s t x) (@lem5948322 _121855 _121856 a s t x)). Qed.
Lemma lem5948326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5948327 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term278 _121855 _121856 a s t x) = (term278 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948326) (@lem5948241 _121855 _121856 a s t x)). Qed.
Lemma lem5948328 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term279 _121855 _121856 a s t x) = (term280 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948327 _121855 _121856 a s t x) (@lem5948319 _121855 _121856 a s t x)). Qed.
Lemma lem5948329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948330 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term281 _121855 _121856 a s t x) = (term282 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948329) (@lem5948328 _121855 _121856 a s t x)). Qed.
Lemma lem5948331 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term283 _121855 _121856 a s t x) = (term284 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948330 _121855 _121856 a s t x) (@lem5948325 _121855 _121856 a s t x)). Qed.
Lemma lem5948332 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term208 _121855 _121856 a s t x) = (term283 _121855 _121856 a s t x).
Proof. exact (@lem17646 (term112 _121855 _121856 a s t x) (term183 _121855 _121856 a s t x)). Qed.
Lemma lem5948333 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term208 _121855 _121856 a s t x) = (term284 _121855 _121856 a s t x).
Proof. exact (TRANS (@lem5948332 _121855 _121856 a s t x) (@lem5948331 _121855 _121856 a s t x)). Qed.
Lemma lem5948640 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5948641 {_121856 : Type'} (P : _121856 -> Prop) (Q : Prop) : (term285 _121856 P Q) = (term286 _121856 P Q).
Proof. exact (@lem5948640 _121856 P Q). Qed.
Lemma lem5948642 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term287 _121855 _121856 a s t x) = (term288 _121855 _121856 a s t x).
Proof. exact (@lem5948641 _121856 (term111 _121855 _121856 a s t x) (term272 _121855 _121856 a s t x)). Qed.
Lemma lem5948643 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term234 _121855 _121856 a s t x i) = (term109 _121855 _121856 a s t x i).
Proof. exact (eq_refl (term234 _121855 _121856 a s t x i)). Qed.
Lemma lem5948644 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term289 _121855 _121856 a s t x) = (term111 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948643 _121855 _121856 a s t x i)). Qed.
Lemma lem5948645 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948646 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term290 _121855 _121856 a s t x) = (term112 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948645 _121856) (@lem5948644 _121855 _121856 a s t x)). Qed.
Lemma lem5948647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5948648 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term291 _121855 _121856 a s t x) = (term278 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948647) (@lem5948646 _121855 _121856 a s t x)). Qed.
Lemma lem5948649 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term272 _121855 _121856 a s t x) = (term272 _121855 _121856 a s t x).
Proof. exact (eq_refl (term272 _121855 _121856 a s t x)). Qed.
Lemma lem5948650 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term287 _121855 _121856 a s t x) = (term280 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948648 _121855 _121856 a s t x) (@lem5948649 _121855 _121856 a s t x)). Qed.
Lemma lem5948651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948652 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term292 _121855 _121856 a s t x) = (term293 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948651) (@lem5948650 _121855 _121856 a s t x)). Qed.
Lemma lem5948653 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term234 _121855 _121856 a s t x i) = (term109 _121855 _121856 a s t x i).
Proof. exact (eq_refl (term234 _121855 _121856 a s t x i)). Qed.
Lemma lem5948654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5948655 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term294 _121855 _121856 a s t x i) = (term295 _121855 _121856 a s t x i).
Proof. exact (MK_COMB (@lem5948654) (@lem5948653 _121855 _121856 a s t x i)). Qed.
Lemma lem5948656 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term272 _121855 _121856 a s t x) = (term272 _121855 _121856 a s t x).
Proof. exact (eq_refl (term272 _121855 _121856 a s t x)). Qed.
Lemma lem5948657 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term296 _121855 _121856 i a s t x) = (term297 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948655 _121855 _121856 a s t x i) (@lem5948656 _121855 _121856 a s t x)). Qed.
Lemma lem5948658 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term298 _121855 _121856 a s t x) = (term299 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948657 _121855 _121856 i a s t x)). Qed.
Lemma lem5948659 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948660 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term288 _121855 _121856 a s t x) = (term300 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948659 _121856) (@lem5948658 _121855 _121856 a s t x)). Qed.
Lemma lem5948661 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term287 _121855 _121856 a s t x) = (term288 _121855 _121856 a s t x)) = ((term280 _121855 _121856 a s t x) = (term300 _121855 _121856 a s t x)).
Proof. exact (MK_COMB (@lem5948652 _121855 _121856 a s t x) (@lem5948660 _121855 _121856 a s t x)). Qed.
Lemma lem5948662 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term280 _121855 _121856 a s t x) = (term300 _121855 _121856 a s t x).
Proof. exact (EQ_MP (@lem5948661 _121855 _121856 a s t x) (@lem5948642 _121855 _121856 a s t x)). Qed.
Lemma lem5948664 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5948665 {_121855 : Type'} (P : _121855 -> Prop) (Q : Prop) : (term285 _121855 P Q) = (term286 _121855 P Q).
Proof. exact (@lem5948664 _121855 P Q). Qed.
Lemma lem5948666 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term301 _121855 _121856 i a s t x) = (term302 _121855 _121856 i a s t x).
Proof. exact (@lem5948665 _121855 (term107 _121855 _121856 a s t x i) (term272 _121855 _121856 a s t x)). Qed.
Lemma lem5948667 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term227 _121855 _121856 a s t x i j) = (term105 _121855 _121856 a s t x i j).
Proof. exact (eq_refl (term227 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948668 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term303 _121855 _121856 a s t x i) = (term107 _121855 _121856 a s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5948667 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948669 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948670 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term304 _121855 _121856 a s t x i) = (term109 _121855 _121856 a s t x i).
Proof. exact (MK_COMB (@lem5948669 _121855) (@lem5948668 _121855 _121856 a s t x i)). Qed.
Lemma lem5948671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5948672 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term305 _121855 _121856 a s t x i) = (term295 _121855 _121856 a s t x i).
Proof. exact (MK_COMB (@lem5948671) (@lem5948670 _121855 _121856 a s t x i)). Qed.
Lemma lem5948673 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term272 _121855 _121856 a s t x) = (term272 _121855 _121856 a s t x).
Proof. exact (eq_refl (term272 _121855 _121856 a s t x)). Qed.
Lemma lem5948674 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term301 _121855 _121856 i a s t x) = (term297 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948672 _121855 _121856 a s t x i) (@lem5948673 _121855 _121856 a s t x)). Qed.
Lemma lem5948675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948676 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term306 _121855 _121856 i a s t x) = (term307 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948675) (@lem5948674 _121855 _121856 i a s t x)). Qed.
Lemma lem5948677 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term227 _121855 _121856 a s t x i j) = (term105 _121855 _121856 a s t x i j).
Proof. exact (eq_refl (term227 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5948679 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term308 _121855 _121856 a s t x i j) = (term309 _121855 _121856 a s t x i j).
Proof. exact (MK_COMB (@lem5948678) (@lem5948677 _121855 _121856 a s t x i j)). Qed.
Lemma lem5948680 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term272 _121855 _121856 a s t x) = (term272 _121855 _121856 a s t x).
Proof. exact (eq_refl (term272 _121855 _121856 a s t x)). Qed.
Lemma lem5948681 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term310 _121855 _121856 i j a s t x) = (term311 _121855 _121856 i j a s t x).
Proof. exact (MK_COMB (@lem5948679 _121855 _121856 a s t x i j) (@lem5948680 _121855 _121856 a s t x)). Qed.
Lemma lem5948682 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term312 _121855 _121856 i a s t x) = (term313 _121855 _121856 i a s t x).
Proof. exact (fun_ext (fun j : _121855 => @lem5948681 _121855 _121856 i j a s t x)). Qed.
Lemma lem5948683 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948684 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term302 _121855 _121856 i a s t x) = (term314 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948683 _121855) (@lem5948682 _121855 _121856 i a s t x)). Qed.
Lemma lem5948685 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term301 _121855 _121856 i a s t x) = (term302 _121855 _121856 i a s t x)) = ((term297 _121855 _121856 i a s t x) = (term314 _121855 _121856 i a s t x)).
Proof. exact (MK_COMB (@lem5948676 _121855 _121856 i a s t x) (@lem5948684 _121855 _121856 i a s t x)). Qed.
Lemma lem5948686 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term297 _121855 _121856 i a s t x) = (term314 _121855 _121856 i a s t x).
Proof. exact (EQ_MP (@lem5948685 _121855 _121856 i a s t x) (@lem5948666 _121855 _121856 i a s t x)). Qed.
Lemma lem5948687 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term299 _121855 _121856 a s t x) = (term315 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948686 _121855 _121856 i a s t x)). Qed.
Lemma lem5948688 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948689 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term300 _121855 _121856 a s t x) = (term316 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948688 _121856) (@lem5948687 _121855 _121856 a s t x)). Qed.
Lemma lem5948690 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term280 _121855 _121856 a s t x) = (term316 _121855 _121856 a s t x).
Proof. exact (TRANS (@lem5948662 _121855 _121856 a s t x) (@lem5948689 _121855 _121856 a s t x)). Qed.
Lemma lem5948691 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948692 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term282 _121855 _121856 a s t x) = (term317 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948691) (@lem5948690 _121855 _121856 a s t x)). Qed.
Lemma lem5948696 {A : Type'} (P : A -> Prop) (Q : Prop) : (term318 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5948697 {_121855 : Type'} (P : _121855 -> Prop) (Q : Prop) : (term318 _121855 P Q) = (term319 _121855 P Q).
Proof. exact (@lem5948696 _121855 P Q). Qed.
Lemma lem5948698 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term320 _121855 _121856 a s t x) = (term321 _121855 _121856 a s t x).
Proof. exact (@lem5948697 _121855 (term138 _121855 _121856 x t a) (term182 _121855 _121856 s t x)). Qed.
Lemma lem5948699 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term243 _121855 _121856 x t a x') = (term136 _121855 _121856 x t a x').
Proof. exact (eq_refl (term243 _121855 _121856 x t a x')). Qed.
Lemma lem5948700 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term322 _121855 _121856 x t a) = (term138 _121855 _121856 x t a).
Proof. exact (fun_ext (fun x' : _121855 => @lem5948699 _121855 _121856 x t a x')). Qed.
Lemma lem5948701 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948702 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term323 _121855 _121856 x t a) = (term139 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5948701 _121855) (@lem5948700 _121855 _121856 x t a)). Qed.
Lemma lem5948703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948704 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term324 _121855 _121856 x t a) = (term141 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5948703) (@lem5948702 _121855 _121856 x t a)). Qed.
Lemma lem5948705 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term182 _121855 _121856 s t x) = (term182 _121855 _121856 s t x).
Proof. exact (eq_refl (term182 _121855 _121856 s t x)). Qed.
Lemma lem5948706 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term320 _121855 _121856 a s t x) = (term183 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948704 _121855 _121856 x t a) (@lem5948705 _121855 _121856 s t x)). Qed.
Lemma lem5948707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948708 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term325 _121855 _121856 a s t x) = (term326 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948707) (@lem5948706 _121855 _121856 a s t x)). Qed.
Lemma lem5948709 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term243 _121855 _121856 x t a x') = (term136 _121855 _121856 x t a x').
Proof. exact (eq_refl (term243 _121855 _121856 x t a x')). Qed.
Lemma lem5948710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948711 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term327 _121855 _121856 x t a x') = (term328 _121855 _121856 x t a x').
Proof. exact (MK_COMB (@lem5948710) (@lem5948709 _121855 _121856 x t a x')). Qed.
Lemma lem5948712 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term182 _121855 _121856 s t x) = (term182 _121855 _121856 s t x).
Proof. exact (eq_refl (term182 _121855 _121856 s t x)). Qed.
Lemma lem5948713 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term329 _121855 _121856 a x s t x') = (term330 _121855 _121856 a x s t x').
Proof. exact (MK_COMB (@lem5948711 _121855 _121856 x' t a x) (@lem5948712 _121855 _121856 s t x')). Qed.
Lemma lem5948714 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term331 _121855 _121856 a s t x) = (term332 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun x' : _121855 => @lem5948713 _121855 _121856 a x' s t x)). Qed.
Lemma lem5948715 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948716 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term321 _121855 _121856 a s t x) = (term333 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948715 _121855) (@lem5948714 _121855 _121856 a s t x)). Qed.
Lemma lem5948717 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term320 _121855 _121856 a s t x) = (term321 _121855 _121856 a s t x)) = ((term183 _121855 _121856 a s t x) = (term333 _121855 _121856 a s t x)).
Proof. exact (MK_COMB (@lem5948708 _121855 _121856 a s t x) (@lem5948716 _121855 _121856 a s t x)). Qed.
Lemma lem5948718 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term183 _121855 _121856 a s t x) = (term333 _121855 _121856 a s t x).
Proof. exact (EQ_MP (@lem5948717 _121855 _121856 a s t x) (@lem5948698 _121855 _121856 a s t x)). Qed.
Lemma lem5948720 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5948721 {_121856 : Type'} (P : Prop) (Q : _121856 -> Prop) : (term334 _121856 P Q) = (term335 _121856 P Q).
Proof. exact (@lem5948720 _121856 P Q). Qed.
Lemma lem5948722 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term336 _121855 _121856 a x s t x') = (term337 _121855 _121856 a x s t x').
Proof. exact (@lem5948721 _121856 (term136 _121855 _121856 x' t a x) (term181 _121855 _121856 s t x')). Qed.
Lemma lem5948723 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term264 _121855 _121856 s t x i) = (term179 _121855 _121856 s t x i).
Proof. exact (eq_refl (term264 _121855 _121856 s t x i)). Qed.
Lemma lem5948724 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term338 _121855 _121856 s t x) = (term181 _121855 _121856 s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948723 _121855 _121856 s t x i)). Qed.
Lemma lem5948725 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948726 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term339 _121855 _121856 s t x) = (term182 _121855 _121856 s t x).
Proof. exact (MK_COMB (@lem5948725 _121856) (@lem5948724 _121855 _121856 s t x)). Qed.
Lemma lem5948727 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term328 _121855 _121856 x t a x') = (term328 _121855 _121856 x t a x').
Proof. exact (eq_refl (term328 _121855 _121856 x t a x')). Qed.
Lemma lem5948728 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term336 _121855 _121856 a x s t x') = (term330 _121855 _121856 a x s t x').
Proof. exact (MK_COMB (@lem5948727 _121855 _121856 x' t a x) (@lem5948726 _121855 _121856 s t x')). Qed.
Lemma lem5948729 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948730 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term340 _121855 _121856 a x s t x') = (term341 _121855 _121856 a x s t x').
Proof. exact (MK_COMB (@lem5948729) (@lem5948728 _121855 _121856 a x s t x')). Qed.
Lemma lem5948731 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term264 _121855 _121856 s t x i) = (term179 _121855 _121856 s t x i).
Proof. exact (eq_refl (term264 _121855 _121856 s t x i)). Qed.
Lemma lem5948732 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term328 _121855 _121856 x t a x') = (term328 _121855 _121856 x t a x').
Proof. exact (eq_refl (term328 _121855 _121856 x t a x')). Qed.
Lemma lem5948733 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term342 _121855 _121856 a x s t x' i) = (term343 _121855 _121856 a x s t x' i).
Proof. exact (MK_COMB (@lem5948732 _121855 _121856 x' t a x) (@lem5948731 _121855 _121856 s t x' i)). Qed.
Lemma lem5948734 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term344 _121855 _121856 a x s t x') = (term345 _121855 _121856 a x s t x').
Proof. exact (fun_ext (fun i : _121856 => @lem5948733 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948735 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948736 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term337 _121855 _121856 a x s t x') = (term346 _121855 _121856 a x s t x').
Proof. exact (MK_COMB (@lem5948735 _121856) (@lem5948734 _121855 _121856 a x s t x')). Qed.
Lemma lem5948737 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : ((term336 _121855 _121856 a x s t x') = (term337 _121855 _121856 a x s t x')) = ((term330 _121855 _121856 a x s t x') = (term346 _121855 _121856 a x s t x')).
Proof. exact (MK_COMB (@lem5948730 _121855 _121856 a x s t x') (@lem5948736 _121855 _121856 a x s t x')). Qed.
Lemma lem5948738 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term330 _121855 _121856 a x s t x') = (term346 _121855 _121856 a x s t x').
Proof. exact (EQ_MP (@lem5948737 _121855 _121856 a x s t x') (@lem5948722 _121855 _121856 a x s t x')). Qed.
Lemma lem5948740 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5948741 {_121855 : Type'} (P : Prop) (Q : _121855 -> Prop) : (term334 _121855 P Q) = (term335 _121855 P Q).
Proof. exact (@lem5948740 _121855 P Q). Qed.
Lemma lem5948742 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term347 _121855 _121856 a x s t x' i) = (term348 _121855 _121856 a x s t x' i).
Proof. exact (@lem5948741 _121855 (term136 _121855 _121856 x' t a x) (term177 _121855 _121856 s t x' i)). Qed.
Lemma lem5948743 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term257 _121855 _121856 s t x i j) = (term175 _121855 _121856 s t x i j).
Proof. exact (eq_refl (term257 _121855 _121856 s t x i j)). Qed.
Lemma lem5948744 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term349 _121855 _121856 s t x i) = (term177 _121855 _121856 s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5948743 _121855 _121856 s t x i j)). Qed.
Lemma lem5948745 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948746 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term350 _121855 _121856 s t x i) = (term179 _121855 _121856 s t x i).
Proof. exact (MK_COMB (@lem5948745 _121855) (@lem5948744 _121855 _121856 s t x i)). Qed.
Lemma lem5948747 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term328 _121855 _121856 x t a x') = (term328 _121855 _121856 x t a x').
Proof. exact (eq_refl (term328 _121855 _121856 x t a x')). Qed.
Lemma lem5948748 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term347 _121855 _121856 a x s t x' i) = (term343 _121855 _121856 a x s t x' i).
Proof. exact (MK_COMB (@lem5948747 _121855 _121856 x' t a x) (@lem5948746 _121855 _121856 s t x' i)). Qed.
Lemma lem5948749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948750 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term351 _121855 _121856 a x s t x' i) = (term352 _121855 _121856 a x s t x' i).
Proof. exact (MK_COMB (@lem5948749) (@lem5948748 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948751 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term257 _121855 _121856 s t x i j) = (term175 _121855 _121856 s t x i j).
Proof. exact (eq_refl (term257 _121855 _121856 s t x i j)). Qed.
Lemma lem5948752 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term328 _121855 _121856 x t a x') = (term328 _121855 _121856 x t a x').
Proof. exact (eq_refl (term328 _121855 _121856 x t a x')). Qed.
Lemma lem5948753 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) (j : _121855) : (term353 _121855 _121856 a x s t x' i j) = (term354 _121855 _121856 a x s t x' i j).
Proof. exact (MK_COMB (@lem5948752 _121855 _121856 x' t a x) (@lem5948751 _121855 _121856 s t x' i j)). Qed.
Lemma lem5948754 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term355 _121855 _121856 a x s t x' i) = (term356 _121855 _121856 a x s t x' i).
Proof. exact (fun_ext (fun j : _121855 => @lem5948753 _121855 _121856 a x s t x' i j)). Qed.
Lemma lem5948755 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948756 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term348 _121855 _121856 a x s t x' i) = (term357 _121855 _121856 a x s t x' i).
Proof. exact (MK_COMB (@lem5948755 _121855) (@lem5948754 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948757 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : ((term347 _121855 _121856 a x s t x' i) = (term348 _121855 _121856 a x s t x' i)) = ((term343 _121855 _121856 a x s t x' i) = (term357 _121855 _121856 a x s t x' i)).
Proof. exact (MK_COMB (@lem5948750 _121855 _121856 a x s t x' i) (@lem5948756 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948758 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term343 _121855 _121856 a x s t x' i) = (term357 _121855 _121856 a x s t x' i).
Proof. exact (EQ_MP (@lem5948757 _121855 _121856 a x s t x' i) (@lem5948742 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948759 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term345 _121855 _121856 a x s t x') = (term358 _121855 _121856 a x s t x').
Proof. exact (fun_ext (fun i : _121856 => @lem5948758 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948760 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948761 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term346 _121855 _121856 a x s t x') = (term359 _121855 _121856 a x s t x').
Proof. exact (MK_COMB (@lem5948760 _121856) (@lem5948759 _121855 _121856 a x s t x')). Qed.
Lemma lem5948762 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term330 _121855 _121856 a x s t x') = (term359 _121855 _121856 a x s t x').
Proof. exact (TRANS (@lem5948738 _121855 _121856 a x s t x') (@lem5948761 _121855 _121856 a x s t x')). Qed.
Lemma lem5948763 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term332 _121855 _121856 a s t x) = (term360 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun x' : _121855 => @lem5948762 _121855 _121856 a x' s t x)). Qed.
Lemma lem5948764 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948765 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term333 _121855 _121856 a s t x) = (term361 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948764 _121855) (@lem5948763 _121855 _121856 a s t x)). Qed.
Lemma lem5948766 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term183 _121855 _121856 a s t x) = (term361 _121855 _121856 a s t x).
Proof. exact (TRANS (@lem5948718 _121855 _121856 a s t x) (@lem5948765 _121855 _121856 a s t x)). Qed.
Lemma lem5948767 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term275 _121855 _121856 a s t x) = (term275 _121855 _121856 a s t x).
Proof. exact (eq_refl (term275 _121855 _121856 a s t x)). Qed.
Lemma lem5948768 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term277 _121855 _121856 a s t x) = (term362 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948767 _121855 _121856 a s t x) (@lem5948766 _121855 _121856 a s t x)). Qed.
Lemma lem5948770 {A : Type'} (P : Prop) (Q : A -> Prop) : (term363 A P Q) = (term364 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5948771 {_121855 : Type'} (P : Prop) (Q : _121855 -> Prop) : (term363 _121855 P Q) = (term364 _121855 P Q).
Proof. exact (@lem5948770 _121855 P Q). Qed.
Lemma lem5948772 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term365 _121855 _121856 a s t x) = (term366 _121855 _121856 a s t x).
Proof. exact (@lem5948771 _121855 (term238 _121855 _121856 a s t x) (term360 _121855 _121856 a s t x)). Qed.
Lemma lem5948773 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term367 _121855 _121856 a s t x' x) = (term359 _121855 _121856 a x s t x').
Proof. exact (eq_refl (term367 _121855 _121856 a s t x' x)). Qed.
Lemma lem5948774 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term368 _121855 _121856 a s t x) = (term360 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun x' : _121855 => @lem5948773 _121855 _121856 a x' s t x)). Qed.
Lemma lem5948775 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948776 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term369 _121855 _121856 a s t x) = (term361 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948775 _121855) (@lem5948774 _121855 _121856 a s t x)). Qed.
Lemma lem5948777 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term275 _121855 _121856 a s t x) = (term275 _121855 _121856 a s t x).
Proof. exact (eq_refl (term275 _121855 _121856 a s t x)). Qed.
Lemma lem5948778 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term365 _121855 _121856 a s t x) = (term362 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948777 _121855 _121856 a s t x) (@lem5948776 _121855 _121856 a s t x)). Qed.
Lemma lem5948779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948780 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term370 _121855 _121856 a s t x) = (term371 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948779) (@lem5948778 _121855 _121856 a s t x)). Qed.
Lemma lem5948781 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term367 _121855 _121856 a s t x' x) = (term359 _121855 _121856 a x s t x').
Proof. exact (eq_refl (term367 _121855 _121856 a s t x' x)). Qed.
Lemma lem5948782 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term275 _121855 _121856 a s t x) = (term275 _121855 _121856 a s t x).
Proof. exact (eq_refl (term275 _121855 _121856 a s t x)). Qed.
Lemma lem5948783 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term372 _121855 _121856 a s t x' x) = (term373 _121855 _121856 a x s t x').
Proof. exact (MK_COMB (@lem5948782 _121855 _121856 a s t x') (@lem5948781 _121855 _121856 a x s t x')). Qed.
Lemma lem5948784 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term374 _121855 _121856 a s t x) = (term375 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun x' : _121855 => @lem5948783 _121855 _121856 a x' s t x)). Qed.
Lemma lem5948785 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948786 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term366 _121855 _121856 a s t x) = (term376 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948785 _121855) (@lem5948784 _121855 _121856 a s t x)). Qed.
Lemma lem5948787 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term365 _121855 _121856 a s t x) = (term366 _121855 _121856 a s t x)) = ((term362 _121855 _121856 a s t x) = (term376 _121855 _121856 a s t x)).
Proof. exact (MK_COMB (@lem5948780 _121855 _121856 a s t x) (@lem5948786 _121855 _121856 a s t x)). Qed.
Lemma lem5948788 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term362 _121855 _121856 a s t x) = (term376 _121855 _121856 a s t x).
Proof. exact (EQ_MP (@lem5948787 _121855 _121856 a s t x) (@lem5948772 _121855 _121856 a s t x)). Qed.
Lemma lem5948790 {A : Type'} (P : Prop) (Q : A -> Prop) : (term363 A P Q) = (term364 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5948791 {_121856 : Type'} (P : Prop) (Q : _121856 -> Prop) : (term363 _121856 P Q) = (term364 _121856 P Q).
Proof. exact (@lem5948790 _121856 P Q). Qed.
Lemma lem5948792 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term377 _121855 _121856 a x s t x') = (term378 _121855 _121856 a x s t x').
Proof. exact (@lem5948791 _121856 (term238 _121855 _121856 a s t x') (term358 _121855 _121856 a x s t x')). Qed.
Lemma lem5948793 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term379 _121855 _121856 a x s t x' i) = (term357 _121855 _121856 a x s t x' i).
Proof. exact (eq_refl (term379 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948794 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term380 _121855 _121856 a x s t x') = (term358 _121855 _121856 a x s t x').
Proof. exact (fun_ext (fun i : _121856 => @lem5948793 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948795 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948796 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term381 _121855 _121856 a x s t x') = (term359 _121855 _121856 a x s t x').
Proof. exact (MK_COMB (@lem5948795 _121856) (@lem5948794 _121855 _121856 a x s t x')). Qed.
Lemma lem5948797 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term275 _121855 _121856 a s t x) = (term275 _121855 _121856 a s t x).
Proof. exact (eq_refl (term275 _121855 _121856 a s t x)). Qed.
Lemma lem5948798 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term377 _121855 _121856 a x s t x') = (term373 _121855 _121856 a x s t x').
Proof. exact (MK_COMB (@lem5948797 _121855 _121856 a s t x') (@lem5948796 _121855 _121856 a x s t x')). Qed.
Lemma lem5948799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948800 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term382 _121855 _121856 a x s t x') = (term383 _121855 _121856 a x s t x').
Proof. exact (MK_COMB (@lem5948799) (@lem5948798 _121855 _121856 a x s t x')). Qed.
Lemma lem5948801 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term379 _121855 _121856 a x s t x' i) = (term357 _121855 _121856 a x s t x' i).
Proof. exact (eq_refl (term379 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948802 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term275 _121855 _121856 a s t x) = (term275 _121855 _121856 a s t x).
Proof. exact (eq_refl (term275 _121855 _121856 a s t x)). Qed.
Lemma lem5948803 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term384 _121855 _121856 a x s t x' i) = (term385 _121855 _121856 a x s t x' i).
Proof. exact (MK_COMB (@lem5948802 _121855 _121856 a s t x') (@lem5948801 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948804 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term386 _121855 _121856 a x s t x') = (term387 _121855 _121856 a x s t x').
Proof. exact (fun_ext (fun i : _121856 => @lem5948803 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948805 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948806 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term378 _121855 _121856 a x s t x') = (term388 _121855 _121856 a x s t x').
Proof. exact (MK_COMB (@lem5948805 _121856) (@lem5948804 _121855 _121856 a x s t x')). Qed.
Lemma lem5948807 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : ((term377 _121855 _121856 a x s t x') = (term378 _121855 _121856 a x s t x')) = ((term373 _121855 _121856 a x s t x') = (term388 _121855 _121856 a x s t x')).
Proof. exact (MK_COMB (@lem5948800 _121855 _121856 a x s t x') (@lem5948806 _121855 _121856 a x s t x')). Qed.
Lemma lem5948808 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term373 _121855 _121856 a x s t x') = (term388 _121855 _121856 a x s t x').
Proof. exact (EQ_MP (@lem5948807 _121855 _121856 a x s t x') (@lem5948792 _121855 _121856 a x s t x')). Qed.
Lemma lem5948810 {A : Type'} (P : Prop) (Q : A -> Prop) : (term363 A P Q) = (term364 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5948811 {_121855 : Type'} (P : Prop) (Q : _121855 -> Prop) : (term363 _121855 P Q) = (term364 _121855 P Q).
Proof. exact (@lem5948810 _121855 P Q). Qed.
Lemma lem5948812 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term389 _121855 _121856 a x s t x' i) = (term390 _121855 _121856 a x s t x' i).
Proof. exact (@lem5948811 _121855 (term238 _121855 _121856 a s t x') (term356 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948813 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) (j : _121855) : (term391 _121855 _121856 a x s t x' i j) = (term354 _121855 _121856 a x s t x' i j).
Proof. exact (eq_refl (term391 _121855 _121856 a x s t x' i j)). Qed.
Lemma lem5948814 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term392 _121855 _121856 a x s t x' i) = (term356 _121855 _121856 a x s t x' i).
Proof. exact (fun_ext (fun j : _121855 => @lem5948813 _121855 _121856 a x s t x' i j)). Qed.
Lemma lem5948815 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948816 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term393 _121855 _121856 a x s t x' i) = (term357 _121855 _121856 a x s t x' i).
Proof. exact (MK_COMB (@lem5948815 _121855) (@lem5948814 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948817 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term275 _121855 _121856 a s t x) = (term275 _121855 _121856 a s t x).
Proof. exact (eq_refl (term275 _121855 _121856 a s t x)). Qed.
Lemma lem5948818 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term389 _121855 _121856 a x s t x' i) = (term385 _121855 _121856 a x s t x' i).
Proof. exact (MK_COMB (@lem5948817 _121855 _121856 a s t x') (@lem5948816 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948820 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term394 _121855 _121856 a x s t x' i) = (term395 _121855 _121856 a x s t x' i).
Proof. exact (MK_COMB (@lem5948819) (@lem5948818 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948821 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) (j : _121855) : (term391 _121855 _121856 a x s t x' i j) = (term354 _121855 _121856 a x s t x' i j).
Proof. exact (eq_refl (term391 _121855 _121856 a x s t x' i j)). Qed.
Lemma lem5948822 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term275 _121855 _121856 a s t x) = (term275 _121855 _121856 a s t x).
Proof. exact (eq_refl (term275 _121855 _121856 a s t x)). Qed.
Lemma lem5948823 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) (j : _121855) : (term396 _121855 _121856 a x s t x' i j) = (term397 _121855 _121856 a x s t x' i j).
Proof. exact (MK_COMB (@lem5948822 _121855 _121856 a s t x') (@lem5948821 _121855 _121856 a x s t x' i j)). Qed.
Lemma lem5948824 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term398 _121855 _121856 a x s t x' i) = (term399 _121855 _121856 a x s t x' i).
Proof. exact (fun_ext (fun j : _121855 => @lem5948823 _121855 _121856 a x s t x' i j)). Qed.
Lemma lem5948825 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948826 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term390 _121855 _121856 a x s t x' i) = (term400 _121855 _121856 a x s t x' i).
Proof. exact (MK_COMB (@lem5948825 _121855) (@lem5948824 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948827 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : ((term389 _121855 _121856 a x s t x' i) = (term390 _121855 _121856 a x s t x' i)) = ((term385 _121855 _121856 a x s t x' i) = (term400 _121855 _121856 a x s t x' i)).
Proof. exact (MK_COMB (@lem5948820 _121855 _121856 a x s t x' i) (@lem5948826 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948828 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) (i : _121856) : (term385 _121855 _121856 a x s t x' i) = (term400 _121855 _121856 a x s t x' i).
Proof. exact (EQ_MP (@lem5948827 _121855 _121856 a x s t x' i) (@lem5948812 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948829 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term387 _121855 _121856 a x s t x') = (term401 _121855 _121856 a x s t x').
Proof. exact (fun_ext (fun i : _121856 => @lem5948828 _121855 _121856 a x s t x' i)). Qed.
Lemma lem5948830 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948831 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term388 _121855 _121856 a x s t x') = (term402 _121855 _121856 a x s t x').
Proof. exact (MK_COMB (@lem5948830 _121856) (@lem5948829 _121855 _121856 a x s t x')). Qed.
Lemma lem5948832 {_121855 _121856 : Type'} (a : _121856) (x : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x' : prod _121856 _121855) : (term373 _121855 _121856 a x s t x') = (term402 _121855 _121856 a x s t x').
Proof. exact (TRANS (@lem5948808 _121855 _121856 a x s t x') (@lem5948831 _121855 _121856 a x s t x')). Qed.
Lemma lem5948833 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term375 _121855 _121856 a s t x) = (term403 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun x' : _121855 => @lem5948832 _121855 _121856 a x' s t x)). Qed.
Lemma lem5948834 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948835 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term376 _121855 _121856 a s t x) = (term404 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948834 _121855) (@lem5948833 _121855 _121856 a s t x)). Qed.
Lemma lem5948836 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term362 _121855 _121856 a s t x) = (term404 _121855 _121856 a s t x).
Proof. exact (TRANS (@lem5948788 _121855 _121856 a s t x) (@lem5948835 _121855 _121856 a s t x)). Qed.
Lemma lem5948837 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term277 _121855 _121856 a s t x) = (term404 _121855 _121856 a s t x).
Proof. exact (TRANS (@lem5948768 _121855 _121856 a s t x) (@lem5948836 _121855 _121856 a s t x)). Qed.
Lemma lem5948838 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term284 _121855 _121856 a s t x) = (term405 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948692 _121855 _121856 a s t x) (@lem5948837 _121855 _121856 a s t x)). Qed.
Lemma lem5948842 {A : Type'} (P : A -> Prop) (Q : Prop) : (term318 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5948843 {_121856 : Type'} (P : _121856 -> Prop) (Q : Prop) : (term318 _121856 P Q) = (term319 _121856 P Q).
Proof. exact (@lem5948842 _121856 P Q). Qed.
Lemma lem5948844 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term406 _121855 _121856 a s t x) = (term407 _121855 _121856 a s t x).
Proof. exact (@lem5948843 _121856 (term315 _121855 _121856 a s t x) (term404 _121855 _121856 a s t x)). Qed.
Lemma lem5948845 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term408 _121855 _121856 a s t x i) = (term314 _121855 _121856 i a s t x).
Proof. exact (eq_refl (term408 _121855 _121856 a s t x i)). Qed.
Lemma lem5948846 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term409 _121855 _121856 a s t x) = (term315 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948845 _121855 _121856 i a s t x)). Qed.
Lemma lem5948847 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948848 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term410 _121855 _121856 a s t x) = (term316 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948847 _121856) (@lem5948846 _121855 _121856 a s t x)). Qed.
Lemma lem5948849 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948850 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term411 _121855 _121856 a s t x) = (term317 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948849) (@lem5948848 _121855 _121856 a s t x)). Qed.
Lemma lem5948851 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term404 _121855 _121856 a s t x) = (term404 _121855 _121856 a s t x).
Proof. exact (eq_refl (term404 _121855 _121856 a s t x)). Qed.
Lemma lem5948852 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term406 _121855 _121856 a s t x) = (term405 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948850 _121855 _121856 a s t x) (@lem5948851 _121855 _121856 a s t x)). Qed.
Lemma lem5948853 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948854 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term412 _121855 _121856 a s t x) = (term413 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948853) (@lem5948852 _121855 _121856 a s t x)). Qed.
Lemma lem5948855 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term408 _121855 _121856 a s t x i) = (term314 _121855 _121856 i a s t x).
Proof. exact (eq_refl (term408 _121855 _121856 a s t x i)). Qed.
Lemma lem5948856 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948857 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term414 _121855 _121856 a s t x i) = (term415 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948856) (@lem5948855 _121855 _121856 i a s t x)). Qed.
Lemma lem5948858 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term404 _121855 _121856 a s t x) = (term404 _121855 _121856 a s t x).
Proof. exact (eq_refl (term404 _121855 _121856 a s t x)). Qed.
Lemma lem5948859 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term416 _121855 _121856 i a s t x) = (term417 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948857 _121855 _121856 i a s t x) (@lem5948858 _121855 _121856 a s t x)). Qed.
Lemma lem5948860 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term418 _121855 _121856 a s t x) = (term419 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948859 _121855 _121856 i a s t x)). Qed.
Lemma lem5948861 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948862 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term407 _121855 _121856 a s t x) = (term420 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948861 _121856) (@lem5948860 _121855 _121856 a s t x)). Qed.
Lemma lem5948863 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term406 _121855 _121856 a s t x) = (term407 _121855 _121856 a s t x)) = ((term405 _121855 _121856 a s t x) = (term420 _121855 _121856 a s t x)).
Proof. exact (MK_COMB (@lem5948854 _121855 _121856 a s t x) (@lem5948862 _121855 _121856 a s t x)). Qed.
Lemma lem5948864 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term405 _121855 _121856 a s t x) = (term420 _121855 _121856 a s t x).
Proof. exact (EQ_MP (@lem5948863 _121855 _121856 a s t x) (@lem5948844 _121855 _121856 a s t x)). Qed.
Lemma lem5948866 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term421 A P Q) = (term422 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5948867 {_121855 : Type'} (P : _121855 -> Prop) (Q : _121855 -> Prop) : (term421 _121855 P Q) = (term422 _121855 P Q).
Proof. exact (@lem5948866 _121855 P Q). Qed.
Lemma lem5948868 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term423 _121855 _121856 i a s t x) = (term424 _121855 _121856 i a s t x).
Proof. exact (@lem5948867 _121855 (term313 _121855 _121856 i a s t x) (term403 _121855 _121856 a s t x)). Qed.
Lemma lem5948869 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term425 _121855 _121856 i a s t x j) = (term311 _121855 _121856 i j a s t x).
Proof. exact (eq_refl (term425 _121855 _121856 i a s t x j)). Qed.
Lemma lem5948870 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term426 _121855 _121856 i a s t x) = (term313 _121855 _121856 i a s t x).
Proof. exact (fun_ext (fun j : _121855 => @lem5948869 _121855 _121856 i j a s t x)). Qed.
Lemma lem5948871 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948872 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term427 _121855 _121856 i a s t x) = (term314 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948871 _121855) (@lem5948870 _121855 _121856 i a s t x)). Qed.
Lemma lem5948873 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948874 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term428 _121855 _121856 i a s t x) = (term415 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948873) (@lem5948872 _121855 _121856 i a s t x)). Qed.
Lemma lem5948875 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term429 _121855 _121856 a s t x j) = (term402 _121855 _121856 a j s t x).
Proof. exact (eq_refl (term429 _121855 _121856 a s t x j)). Qed.
Lemma lem5948876 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term430 _121855 _121856 a s t x) = (term403 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun j : _121855 => @lem5948875 _121855 _121856 a j s t x)). Qed.
Lemma lem5948877 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948878 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term431 _121855 _121856 a s t x) = (term404 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948877 _121855) (@lem5948876 _121855 _121856 a s t x)). Qed.
Lemma lem5948879 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term423 _121855 _121856 i a s t x) = (term417 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948874 _121855 _121856 i a s t x) (@lem5948878 _121855 _121856 a s t x)). Qed.
Lemma lem5948880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948881 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term432 _121855 _121856 i a s t x) = (term433 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948880) (@lem5948879 _121855 _121856 i a s t x)). Qed.
Lemma lem5948882 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term425 _121855 _121856 i a s t x j) = (term311 _121855 _121856 i j a s t x).
Proof. exact (eq_refl (term425 _121855 _121856 i a s t x j)). Qed.
Lemma lem5948883 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5948884 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term434 _121855 _121856 i a s t x j) = (term435 _121855 _121856 i j a s t x).
Proof. exact (MK_COMB (@lem5948883) (@lem5948882 _121855 _121856 i j a s t x)). Qed.
Lemma lem5948885 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term429 _121855 _121856 a s t x j) = (term402 _121855 _121856 a j s t x).
Proof. exact (eq_refl (term429 _121855 _121856 a s t x j)). Qed.
Lemma lem5948886 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term436 _121855 _121856 i a s t x j) = (term437 _121855 _121856 i a j s t x).
Proof. exact (MK_COMB (@lem5948884 _121855 _121856 i j a s t x) (@lem5948885 _121855 _121856 a j s t x)). Qed.
Lemma lem5948887 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term438 _121855 _121856 i a s t x) = (term439 _121855 _121856 i a s t x).
Proof. exact (fun_ext (fun j : _121855 => @lem5948886 _121855 _121856 i a j s t x)). Qed.
Lemma lem5948888 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948889 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term424 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948888 _121855) (@lem5948887 _121855 _121856 i a s t x)). Qed.
Lemma lem5948890 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term423 _121855 _121856 i a s t x) = (term424 _121855 _121856 i a s t x)) = ((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x)).
Proof. exact (MK_COMB (@lem5948881 _121855 _121856 i a s t x) (@lem5948889 _121855 _121856 i a s t x)). Qed.
Lemma lem5948891 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x).
Proof. exact (EQ_MP (@lem5948890 _121855 _121856 i a s t x) (@lem5948868 _121855 _121856 i a s t x)). Qed.
Lemma lem5948894 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term441 _121855 _121856 i a s t x) = (term441 _121855 _121856 i a s t x).
Proof. exact (eq_refl (term441 _121855 _121856 i a s t x)). Qed.
Lemma lem5948895 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term441 _121855 _121856 i a s t x) = ((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x)).
Proof. exact (eq_refl (term441 _121855 _121856 i a s t x)). Qed.
Lemma lem5948896 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term442 _121855 _121856 i a s t x) = (term442 _121855 _121856 i a s t x).
Proof. exact (eq_refl (term442 _121855 _121856 i a s t x)). Qed.
Lemma lem5948897 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term441 _121855 _121856 i a s t x) = (term441 _121855 _121856 i a s t x)) = ((term441 _121855 _121856 i a s t x) = ((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x))).
Proof. exact (MK_COMB (@lem5948896 _121855 _121856 i a s t x) (@lem5948895 _121855 _121856 i a s t x)). Qed.
Lemma lem5948898 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term441 _121855 _121856 i a s t x) = ((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x)).
Proof. exact (eq_refl (term441 _121855 _121856 i a s t x)). Qed.
Lemma lem5948899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948900 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term442 _121855 _121856 i a s t x) = (term443 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948899) (@lem5948898 _121855 _121856 i a s t x)). Qed.
Lemma lem5948901 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x)) = ((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x)).
Proof. exact (eq_refl ((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x))). Qed.
Lemma lem5948902 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term441 _121855 _121856 i a s t x) = ((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x))) = (((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x)) = ((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x))).
Proof. exact (MK_COMB (@lem5948900 _121855 _121856 i a s t x) (@lem5948901 _121855 _121856 i a s t x)). Qed.
Lemma lem5948903 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term441 _121855 _121856 i a s t x) = (term441 _121855 _121856 i a s t x)) = (((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x)) = ((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x))).
Proof. exact (TRANS (@lem5948897 _121855 _121856 i a s t x) (@lem5948902 _121855 _121856 i a s t x)). Qed.
Lemma lem5948904 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x)) = ((term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x)).
Proof. exact (EQ_MP (@lem5948903 _121855 _121856 i a s t x) (@lem5948894 _121855 _121856 i a s t x)). Qed.
Lemma lem5948905 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term417 _121855 _121856 i a s t x) = (term440 _121855 _121856 i a s t x).
Proof. exact (EQ_MP (@lem5948904 _121855 _121856 i a s t x) (@lem5948891 _121855 _121856 i a s t x)). Qed.
Lemma lem5948907 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5948908 {_121856 : Type'} (P : Prop) (Q : _121856 -> Prop) : (term334 _121856 P Q) = (term335 _121856 P Q).
Proof. exact (@lem5948907 _121856 P Q). Qed.
Lemma lem5948909 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term444 _121855 _121856 i a j s t x) = (term445 _121855 _121856 i a j s t x).
Proof. exact (@lem5948908 _121856 (term311 _121855 _121856 i j a s t x) (term401 _121855 _121856 a j s t x)). Qed.
Lemma lem5948910 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term446 _121855 _121856 a j s t x i) = (term400 _121855 _121856 a j s t x i).
Proof. exact (eq_refl (term446 _121855 _121856 a j s t x i)). Qed.
Lemma lem5948911 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term447 _121855 _121856 a j s t x) = (term401 _121855 _121856 a j s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948910 _121855 _121856 a j s t x i)). Qed.
Lemma lem5948912 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948913 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term448 _121855 _121856 a j s t x) = (term402 _121855 _121856 a j s t x).
Proof. exact (MK_COMB (@lem5948912 _121856) (@lem5948911 _121855 _121856 a j s t x)). Qed.
Lemma lem5948914 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term435 _121855 _121856 i j a s t x) = (term435 _121855 _121856 i j a s t x).
Proof. exact (eq_refl (term435 _121855 _121856 i j a s t x)). Qed.
Lemma lem5948915 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term444 _121855 _121856 i a j s t x) = (term437 _121855 _121856 i a j s t x).
Proof. exact (MK_COMB (@lem5948914 _121855 _121856 i j a s t x) (@lem5948913 _121855 _121856 a j s t x)). Qed.
Lemma lem5948916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948917 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term449 _121855 _121856 i a j s t x) = (term450 _121855 _121856 i a j s t x).
Proof. exact (MK_COMB (@lem5948916) (@lem5948915 _121855 _121856 i a j s t x)). Qed.
Lemma lem5948918 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) : (term446 _121855 _121856 a j s t x i') = (term400 _121855 _121856 a j s t x i').
Proof. exact (eq_refl (term446 _121855 _121856 a j s t x i')). Qed.
Lemma lem5948919 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term435 _121855 _121856 i j a s t x) = (term435 _121855 _121856 i j a s t x).
Proof. exact (eq_refl (term435 _121855 _121856 i j a s t x)). Qed.
Lemma lem5948920 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) : (term451 _121855 _121856 i a j s t x i') = (term452 _121855 _121856 i a j s t x i').
Proof. exact (MK_COMB (@lem5948919 _121855 _121856 i j a s t x) (@lem5948918 _121855 _121856 a j s t x i')). Qed.
Lemma lem5948921 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term453 _121855 _121856 i a j s t x) = (term454 _121855 _121856 i a j s t x).
Proof. exact (fun_ext (fun i' : _121856 => @lem5948920 _121855 _121856 i a j s t x i')). Qed.
Lemma lem5948922 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948923 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term445 _121855 _121856 i a j s t x) = (term455 _121855 _121856 i a j s t x).
Proof. exact (MK_COMB (@lem5948922 _121856) (@lem5948921 _121855 _121856 i a j s t x)). Qed.
Lemma lem5948924 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : ((term444 _121855 _121856 i a j s t x) = (term445 _121855 _121856 i a j s t x)) = ((term437 _121855 _121856 i a j s t x) = (term455 _121855 _121856 i a j s t x)).
Proof. exact (MK_COMB (@lem5948917 _121855 _121856 i a j s t x) (@lem5948923 _121855 _121856 i a j s t x)). Qed.
Lemma lem5948925 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term437 _121855 _121856 i a j s t x) = (term455 _121855 _121856 i a j s t x).
Proof. exact (EQ_MP (@lem5948924 _121855 _121856 i a j s t x) (@lem5948909 _121855 _121856 i a j s t x)). Qed.
Lemma lem5948927 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5948928 {_121855 : Type'} (P : Prop) (Q : _121855 -> Prop) : (term334 _121855 P Q) = (term335 _121855 P Q).
Proof. exact (@lem5948927 _121855 P Q). Qed.
Lemma lem5948929 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) : (term456 _121855 _121856 i a j s t x i') = (term457 _121855 _121856 i a j s t x i').
Proof. exact (@lem5948928 _121855 (term311 _121855 _121856 i j a s t x) (term399 _121855 _121856 a j s t x i')). Qed.
Lemma lem5948930 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) : (term458 _121855 _121856 a j s t x i' j') = (term397 _121855 _121856 a j s t x i' j').
Proof. exact (eq_refl (term458 _121855 _121856 a j s t x i' j')). Qed.
Lemma lem5948931 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) : (term459 _121855 _121856 a j s t x i') = (term399 _121855 _121856 a j s t x i').
Proof. exact (fun_ext (fun j' : _121855 => @lem5948930 _121855 _121856 a j s t x i' j')). Qed.
Lemma lem5948932 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948933 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) : (term460 _121855 _121856 a j s t x i') = (term400 _121855 _121856 a j s t x i').
Proof. exact (MK_COMB (@lem5948932 _121855) (@lem5948931 _121855 _121856 a j s t x i')). Qed.
Lemma lem5948934 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term435 _121855 _121856 i j a s t x) = (term435 _121855 _121856 i j a s t x).
Proof. exact (eq_refl (term435 _121855 _121856 i j a s t x)). Qed.
Lemma lem5948935 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) : (term456 _121855 _121856 i a j s t x i') = (term452 _121855 _121856 i a j s t x i').
Proof. exact (MK_COMB (@lem5948934 _121855 _121856 i j a s t x) (@lem5948933 _121855 _121856 a j s t x i')). Qed.
Lemma lem5948936 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5948937 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) : (term461 _121855 _121856 i a j s t x i') = (term462 _121855 _121856 i a j s t x i').
Proof. exact (MK_COMB (@lem5948936) (@lem5948935 _121855 _121856 i a j s t x i')). Qed.
Lemma lem5948938 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) : (term458 _121855 _121856 a j s t x i' j') = (term397 _121855 _121856 a j s t x i' j').
Proof. exact (eq_refl (term458 _121855 _121856 a j s t x i' j')). Qed.
Lemma lem5948939 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term435 _121855 _121856 i j a s t x) = (term435 _121855 _121856 i j a s t x).
Proof. exact (eq_refl (term435 _121855 _121856 i j a s t x)). Qed.
Lemma lem5948940 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) : (term463 _121855 _121856 i a j s t x i' j') = (term464 _121855 _121856 i a j s t x i' j').
Proof. exact (MK_COMB (@lem5948939 _121855 _121856 i j a s t x) (@lem5948938 _121855 _121856 a j s t x i' j')). Qed.
Lemma lem5948941 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) : (term465 _121855 _121856 i a j s t x i') = (term466 _121855 _121856 i a j s t x i').
Proof. exact (fun_ext (fun j' : _121855 => @lem5948940 _121855 _121856 i a j s t x i' j')). Qed.
Lemma lem5948942 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948943 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) : (term457 _121855 _121856 i a j s t x i') = (term467 _121855 _121856 i a j s t x i').
Proof. exact (MK_COMB (@lem5948942 _121855) (@lem5948941 _121855 _121856 i a j s t x i')). Qed.
Lemma lem5948944 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) : ((term456 _121855 _121856 i a j s t x i') = (term457 _121855 _121856 i a j s t x i')) = ((term452 _121855 _121856 i a j s t x i') = (term467 _121855 _121856 i a j s t x i')).
Proof. exact (MK_COMB (@lem5948937 _121855 _121856 i a j s t x i') (@lem5948943 _121855 _121856 i a j s t x i')). Qed.
Lemma lem5948945 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) : (term452 _121855 _121856 i a j s t x i') = (term467 _121855 _121856 i a j s t x i').
Proof. exact (EQ_MP (@lem5948944 _121855 _121856 i a j s t x i') (@lem5948929 _121855 _121856 i a j s t x i')). Qed.
Lemma lem5948946 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term454 _121855 _121856 i a j s t x) = (term468 _121855 _121856 i a j s t x).
Proof. exact (fun_ext (fun i' : _121856 => @lem5948945 _121855 _121856 i a j s t x i')). Qed.
Lemma lem5948947 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948948 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term455 _121855 _121856 i a j s t x) = (term469 _121855 _121856 i a j s t x).
Proof. exact (MK_COMB (@lem5948947 _121856) (@lem5948946 _121855 _121856 i a j s t x)). Qed.
Lemma lem5948949 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term437 _121855 _121856 i a j s t x) = (term469 _121855 _121856 i a j s t x).
Proof. exact (TRANS (@lem5948925 _121855 _121856 i a j s t x) (@lem5948948 _121855 _121856 i a j s t x)). Qed.
Lemma lem5948950 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term439 _121855 _121856 i a s t x) = (term470 _121855 _121856 i a s t x).
Proof. exact (fun_ext (fun j : _121855 => @lem5948949 _121855 _121856 i a j s t x)). Qed.
Lemma lem5948951 {_121855 : Type'} : (@ex _121855) = (@ex _121855).
Proof. exact (eq_refl (@ex _121855)). Qed.
Lemma lem5948952 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term440 _121855 _121856 i a s t x) = (term471 _121855 _121856 i a s t x).
Proof. exact (MK_COMB (@lem5948951 _121855) (@lem5948950 _121855 _121856 i a s t x)). Qed.
Lemma lem5948953 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term417 _121855 _121856 i a s t x) = (term471 _121855 _121856 i a s t x).
Proof. exact (TRANS (@lem5948905 _121855 _121856 i a s t x) (@lem5948952 _121855 _121856 i a s t x)). Qed.
Lemma lem5948954 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term419 _121855 _121856 a s t x) = (term472 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5948953 _121855 _121856 i a s t x)). Qed.
Lemma lem5948955 {_121856 : Type'} : (@ex _121856) = (@ex _121856).
Proof. exact (eq_refl (@ex _121856)). Qed.
Lemma lem5948956 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term420 _121855 _121856 a s t x) = (term473 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5948955 _121856) (@lem5948954 _121855 _121856 a s t x)). Qed.
Lemma lem5948957 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term405 _121855 _121856 a s t x) = (term473 _121855 _121856 a s t x).
Proof. exact (TRANS (@lem5948864 _121855 _121856 a s t x) (@lem5948956 _121855 _121856 a s t x)). Qed.
Lemma lem5948959 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term284 _121855 _121856 a s t x) = (term473 _121855 _121856 a s t x).
Proof. exact (TRANS (@lem5948838 _121855 _121856 a s t x) (@lem5948957 _121855 _121856 a s t x)). Qed.
Lemma lem5948960 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term208 _121855 _121856 a s t x) = (term473 _121855 _121856 a s t x).
Proof. exact (TRANS (@lem5948333 _121855 _121856 a s t x) (@lem5948959 _121855 _121856 a s t x)). Qed.
Lemma lem5948961 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term208 _121855 _121856 a s t x) : term473 _121855 _121856 a s t x.
Proof. exact (EQ_MP (@lem5948960 _121855 _121856 a s t x) (@lem5948183 _121855 _121856 a s t x h1)). Qed.
Lemma lem5948962 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term471 _121855 _121856 i a s t x) : term471 _121855 _121856 i a s t x.
Proof. exact (h1). Qed.
Lemma lem5948963 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term469 _121855 _121856 i a j s t x) : term469 _121855 _121856 i a j s t x.
Proof. exact (h1). Qed.
Lemma lem5948964 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (h1 : term467 _121855 _121856 i a j s t x i') : term467 _121855 _121856 i a j s t x i'.
Proof. exact (h1). Qed.
Lemma lem5948965 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term464 _121855 _121856 i a j s t x i' j') : term464 _121855 _121856 i a j s t x i' j'.
Proof. exact (h1). Qed.
Lemma lem5949008 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) : (term354 _121855 _121856 a j s t x i' j') = (term354 _121855 _121856 a j s t x i' j').
Proof. exact (eq_refl (term354 _121855 _121856 a j s t x i' j')). Qed.
Lemma lem5949047 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term221 _121855 _121856 a s t x i j) = (term221 _121855 _121856 a s t x i j).
Proof. exact (eq_refl (term221 _121855 _121856 a s t x i j)). Qed.
Lemma lem5949048 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term230 _121855 _121856 a s t x i) = (term230 _121855 _121856 a s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5949047 _121855 _121856 a s t x i j)). Qed.
Lemma lem5949049 {_121855 : Type'} : (@all _121855) = (@all _121855).
Proof. exact (eq_refl (@all _121855)). Qed.
Lemma lem5949050 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term231 _121855 _121856 a s t x i) = (term231 _121855 _121856 a s t x i).
Proof. exact (MK_COMB (@lem5949049 _121855) (@lem5949048 _121855 _121856 a s t x i)). Qed.
Lemma lem5949051 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term237 _121855 _121856 a s t x) = (term237 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5949050 _121855 _121856 a s t x i)). Qed.
Lemma lem5949052 {_121856 : Type'} : (@all _121856) = (@all _121856).
Proof. exact (eq_refl (@all _121856)). Qed.
Lemma lem5949053 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term238 _121855 _121856 a s t x) = (term238 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5949052 _121856) (@lem5949051 _121855 _121856 a s t x)). Qed.
Lemma lem5949054 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5949055 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term275 _121855 _121856 a s t x) = (term275 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5949054) (@lem5949053 _121855 _121856 a s t x)). Qed.
Lemma lem5949056 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) : (term397 _121855 _121856 a j s t x i' j') = (term397 _121855 _121856 a j s t x i' j').
Proof. exact (MK_COMB (@lem5949055 _121855 _121856 a s t x) (@lem5949008 _121855 _121856 a j s t x i' j')). Qed.
Lemma lem5949085 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term253 _121855 _121856 s t x i j) = (term253 _121855 _121856 s t x i j).
Proof. exact (eq_refl (term253 _121855 _121856 s t x i j)). Qed.
Lemma lem5949086 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term260 _121855 _121856 s t x i) = (term260 _121855 _121856 s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5949085 _121855 _121856 s t x i j)). Qed.
Lemma lem5949087 {_121855 : Type'} : (@all _121855) = (@all _121855).
Proof. exact (eq_refl (@all _121855)). Qed.
Lemma lem5949088 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term261 _121855 _121856 s t x i) = (term261 _121855 _121856 s t x i).
Proof. exact (MK_COMB (@lem5949087 _121855) (@lem5949086 _121855 _121856 s t x i)). Qed.
Lemma lem5949089 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term267 _121855 _121856 s t x) = (term267 _121855 _121856 s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5949088 _121855 _121856 s t x i)). Qed.
Lemma lem5949090 {_121856 : Type'} : (@all _121856) = (@all _121856).
Proof. exact (eq_refl (@all _121856)). Qed.
Lemma lem5949091 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term268 _121855 _121856 s t x) = (term268 _121855 _121856 s t x).
Proof. exact (MK_COMB (@lem5949090 _121856) (@lem5949089 _121855 _121856 s t x)). Qed.
Lemma lem5949112 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term240 _121855 _121856 x t a x') = (term240 _121855 _121856 x t a x').
Proof. exact (eq_refl (term240 _121855 _121856 x t a x')). Qed.
Lemma lem5949113 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term246 _121855 _121856 x t a) = (term246 _121855 _121856 x t a).
Proof. exact (fun_ext (fun x' : _121855 => @lem5949112 _121855 _121856 x t a x')). Qed.
Lemma lem5949114 {_121855 : Type'} : (@all _121855) = (@all _121855).
Proof. exact (eq_refl (@all _121855)). Qed.
Lemma lem5949115 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term247 _121855 _121856 x t a) = (term247 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5949114 _121855) (@lem5949113 _121855 _121856 x t a)). Qed.
Lemma lem5949116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5949117 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term270 _121855 _121856 x t a) = (term270 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5949116) (@lem5949115 _121855 _121856 x t a)). Qed.
Lemma lem5949118 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term272 _121855 _121856 a s t x) = (term272 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5949117 _121855 _121856 x t a) (@lem5949091 _121855 _121856 s t x)). Qed.
Lemma lem5949151 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term309 _121855 _121856 a s t x i j) = (term309 _121855 _121856 a s t x i j).
Proof. exact (eq_refl (term309 _121855 _121856 a s t x i j)). Qed.
Lemma lem5949152 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term311 _121855 _121856 i j a s t x) = (term311 _121855 _121856 i j a s t x).
Proof. exact (MK_COMB (@lem5949151 _121855 _121856 a s t x i j) (@lem5949118 _121855 _121856 a s t x)). Qed.
Lemma lem5949153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5949154 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term435 _121855 _121856 i j a s t x) = (term435 _121855 _121856 i j a s t x).
Proof. exact (MK_COMB (@lem5949153) (@lem5949152 _121855 _121856 i j a s t x)). Qed.
Lemma lem5949155 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) : (term464 _121855 _121856 i a j s t x i' j') = (term464 _121855 _121856 i a j s t x i' j').
Proof. exact (MK_COMB (@lem5949154 _121855 _121856 i j a s t x) (@lem5949056 _121855 _121856 a j s t x i' j')). Qed.
Lemma lem5949156 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term464 _121855 _121856 i a j s t x i' j') : term464 _121855 _121856 i a j s t x i' j'.
Proof. exact (EQ_MP (@lem5949155 _121855 _121856 i a j s t x i' j') (@lem5948965 _121855 _121856 i a j s t x i' j' h1)). Qed.
Lemma lem5949157 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term311 _121855 _121856 i j a s t x.
Proof. exact (h1). Qed.
Lemma lem5949158 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term397 _121855 _121856 a j s t x i' j'.
Proof. exact (h1). Qed.
Lemma lem5949159 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term272 _121855 _121856 a s t x.
Proof. exact (proj2 (@lem5949157 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949160 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term105 _121855 _121856 a s t x i j.
Proof. exact (proj1 (@lem5949157 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949161 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term268 _121855 _121856 s t x.
Proof. exact (proj2 (@lem5949159 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949162 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term247 _121855 _121856 x t a.
Proof. exact (proj1 (@lem5949159 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949164 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term91 _121855 _121856 a s t i j.
Proof. exact (proj1 (@lem5949160 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949166 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term87 _121856 a s i.
Proof. exact (proj1 (@lem5949164 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949169 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term354 _121855 _121856 a j s t x i' j'.
Proof. exact (proj2 (@lem5949158 _121855 _121856 a j s t x i' j' h1)). Qed.
Lemma lem5949170 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term238 _121855 _121856 a s t x.
Proof. exact (proj1 (@lem5949158 _121855 _121856 a j s t x i' j' h1)). Qed.
Lemma lem5949171 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term136 _121855 _121856 x t a j) : term136 _121855 _121856 x t a j.
Proof. exact (h1). Qed.
Lemma lem5949172 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : term175 _121855 _121856 s t x i' j'.
Proof. exact (h1). Qed.
Lemma lem5949176 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : term162 _121855 _121856 s t i' j'.
Proof. exact (proj1 (@lem5949172 _121855 _121856 s t x i' j' h1)). Qed.
Lemma lem5949186 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (x' : _121855) : (term240 _121855 _121856 x t a x') = (term240 _121855 _121856 x t a x').
Proof. exact (eq_refl (term240 _121855 _121856 x t a x')). Qed.
Lemma lem5949187 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term246 _121855 _121856 x t a) = (term246 _121855 _121856 x t a).
Proof. exact (fun_ext (fun x' : _121855 => @lem5949186 _121855 _121856 x t a x')). Qed.
Lemma lem5949188 {_121855 : Type'} : (@all _121855) = (@all _121855).
Proof. exact (eq_refl (@all _121855)). Qed.
Lemma lem5949190 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) : (term247 _121855 _121856 x t a) = (term247 _121855 _121856 x t a).
Proof. exact (MK_COMB (@lem5949188 _121855) (@lem5949187 _121855 _121856 x t a)). Qed.
Lemma lem5949191 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term247 _121855 _121856 x t a.
Proof. exact (EQ_MP (@lem5949190 _121855 _121856 x t a) (@lem5949162 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949225 {_121856 : Type'} (i : _121856) (a : _121856) (h1 : i = a) : i = a.
Proof. exact (h1). Qed.
Lemma lem5949252 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term253 _121855 _121856 s t x i j) = (term253 _121855 _121856 s t x i j).
Proof. exact (eq_refl (term253 _121855 _121856 s t x i j)). Qed.
Lemma lem5949253 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term260 _121855 _121856 s t x i) = (term260 _121855 _121856 s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5949252 _121855 _121856 s t x i j)). Qed.
Lemma lem5949254 {_121855 : Type'} : (@all _121855) = (@all _121855).
Proof. exact (eq_refl (@all _121855)). Qed.
Lemma lem5949255 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term261 _121855 _121856 s t x i) = (term261 _121855 _121856 s t x i).
Proof. exact (MK_COMB (@lem5949254 _121855) (@lem5949253 _121855 _121856 s t x i)). Qed.
Lemma lem5949256 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term267 _121855 _121856 s t x) = (term267 _121855 _121856 s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5949255 _121855 _121856 s t x i)). Qed.
Lemma lem5949257 {_121856 : Type'} : (@all _121856) = (@all _121856).
Proof. exact (eq_refl (@all _121856)). Qed.
Lemma lem5949259 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term268 _121855 _121856 s t x) = (term268 _121855 _121856 s t x).
Proof. exact (MK_COMB (@lem5949257 _121856) (@lem5949256 _121855 _121856 s t x)). Qed.
Lemma lem5949260 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term268 _121855 _121856 s t x.
Proof. exact (EQ_MP (@lem5949259 _121855 _121856 s t x) (@lem5949161 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949272 {_121856 : Type'} (s : _121856 -> Prop) (i : _121856) (h1 : s i) : s i.
Proof. exact (h1). Qed.
Lemma lem5949274 {_121855 _121856 : Type'} (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term217 _121855 _121856 x i j) = (term217 _121855 _121856 x i j).
Proof. exact (eq_refl (term217 _121855 _121856 x i j)). Qed.
Lemma lem5949291 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term215 _121855 _121856 a s t i j) = (term474 _121855 _121856 a s t i j).
Proof. exact (@lem19699 (term475 _121856 i a) (term476 _121856 s i) (term211 _121855 _121856 t i j)). Qed.
Lemma lem5949292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5949293 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term219 _121855 _121856 a s t i j) = (term477 _121855 _121856 a s t i j).
Proof. exact (MK_COMB (@lem5949292) (@lem5949291 _121855 _121856 a s t i j)). Qed.
Lemma lem5949294 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term221 _121855 _121856 a s t x i j) = (term478 _121855 _121856 a s t x i j).
Proof. exact (MK_COMB (@lem5949293 _121855 _121856 a s t i j) (@lem5949274 _121855 _121856 x i j)). Qed.
Lemma lem5949301 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term478 _121855 _121856 a s t x i j) = (term479 _121855 _121856 a s t x i j).
Proof. exact (@lem19699 (term480 _121855 _121856 a t i j) (term249 _121855 _121856 s t i j) (term217 _121855 _121856 x i j)). Qed.
Lemma lem5949302 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term221 _121855 _121856 a s t x i j) = (term479 _121855 _121856 a s t x i j).
Proof. exact (TRANS (@lem5949294 _121855 _121856 a s t x i j) (@lem5949301 _121855 _121856 a s t x i j)). Qed.
Lemma lem5949303 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term230 _121855 _121856 a s t x i) = (term481 _121855 _121856 a s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5949302 _121855 _121856 a s t x i j)). Qed.
Lemma lem5949304 {_121855 : Type'} : (@all _121855) = (@all _121855).
Proof. exact (eq_refl (@all _121855)). Qed.
Lemma lem5949305 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term231 _121855 _121856 a s t x i) = (term482 _121855 _121856 a s t x i).
Proof. exact (MK_COMB (@lem5949304 _121855) (@lem5949303 _121855 _121856 a s t x i)). Qed.
Lemma lem5949306 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term237 _121855 _121856 a s t x) = (term483 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5949305 _121855 _121856 a s t x i)). Qed.
Lemma lem5949307 {_121856 : Type'} : (@all _121856) = (@all _121856).
Proof. exact (eq_refl (@all _121856)). Qed.
Lemma lem5949309 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term238 _121855 _121856 a s t x) = (term484 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5949307 _121856) (@lem5949306 _121855 _121856 a s t x)). Qed.
Lemma lem5949310 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term484 _121855 _121856 a s t x.
Proof. exact (EQ_MP (@lem5949309 _121855 _121856 a s t x) (@lem5949170 _121855 _121856 a j s t x i' j' h1)). Qed.
Lemma lem5949320 {_121855 _121856 : Type'} (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term217 _121855 _121856 x i j) = (term217 _121855 _121856 x i j).
Proof. exact (eq_refl (term217 _121855 _121856 x i j)). Qed.
Lemma lem5949337 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term215 _121855 _121856 a s t i j) = (term474 _121855 _121856 a s t i j).
Proof. exact (@lem19699 (term475 _121856 i a) (term476 _121856 s i) (term211 _121855 _121856 t i j)). Qed.
Lemma lem5949338 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5949339 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term219 _121855 _121856 a s t i j) = (term477 _121855 _121856 a s t i j).
Proof. exact (MK_COMB (@lem5949338) (@lem5949337 _121855 _121856 a s t i j)). Qed.
Lemma lem5949340 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term221 _121855 _121856 a s t x i j) = (term478 _121855 _121856 a s t x i j).
Proof. exact (MK_COMB (@lem5949339 _121855 _121856 a s t i j) (@lem5949320 _121855 _121856 x i j)). Qed.
Lemma lem5949347 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term478 _121855 _121856 a s t x i j) = (term479 _121855 _121856 a s t x i j).
Proof. exact (@lem19699 (term480 _121855 _121856 a t i j) (term249 _121855 _121856 s t i j) (term217 _121855 _121856 x i j)). Qed.
Lemma lem5949348 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term221 _121855 _121856 a s t x i j) = (term479 _121855 _121856 a s t x i j).
Proof. exact (TRANS (@lem5949340 _121855 _121856 a s t x i j) (@lem5949347 _121855 _121856 a s t x i j)). Qed.
Lemma lem5949349 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term230 _121855 _121856 a s t x i) = (term481 _121855 _121856 a s t x i).
Proof. exact (fun_ext (fun j : _121855 => @lem5949348 _121855 _121856 a s t x i j)). Qed.
Lemma lem5949350 {_121855 : Type'} : (@all _121855) = (@all _121855).
Proof. exact (eq_refl (@all _121855)). Qed.
Lemma lem5949351 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) : (term231 _121855 _121856 a s t x i) = (term482 _121855 _121856 a s t x i).
Proof. exact (MK_COMB (@lem5949350 _121855) (@lem5949349 _121855 _121856 a s t x i)). Qed.
Lemma lem5949352 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term237 _121855 _121856 a s t x) = (term483 _121855 _121856 a s t x).
Proof. exact (fun_ext (fun i : _121856 => @lem5949351 _121855 _121856 a s t x i)). Qed.
Lemma lem5949353 {_121856 : Type'} : (@all _121856) = (@all _121856).
Proof. exact (eq_refl (@all _121856)). Qed.
Lemma lem5949355 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term238 _121855 _121856 a s t x) = (term484 _121855 _121856 a s t x).
Proof. exact (MK_COMB (@lem5949353 _121856) (@lem5949352 _121855 _121856 a s t x)). Qed.
Lemma lem5949356 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term484 _121855 _121856 a s t x.
Proof. exact (EQ_MP (@lem5949355 _121855 _121856 a s t x) (@lem5949170 _121855 _121856 a j s t x i' j' h1)). Qed.
Lemma lem5949369 {_121855 _121856 : Type'} (_75196 : _121855) (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term485 _121855 _121856 x t a _75196.
Proof. exact (@lem5949191 _121855 _121856 i j a s t x h1 _75196). Qed.
Lemma lem5949370 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) : (term485 _121855 _121856 x t a _75196) = (term240 _121855 _121856 x t a _75196).
Proof. exact (eq_refl (term485 _121855 _121856 x t a _75196)). Qed.
Lemma lem5949381 {_121855 _121856 : Type'} (_75200 : _121856) (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term486 _121855 _121856 s t x _75200.
Proof. exact (@lem5949260 _121855 _121856 i j a s t x h1 _75200). Qed.
Lemma lem5949382 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75200 : _121856) : (term486 _121855 _121856 s t x _75200) = (term261 _121855 _121856 s t x _75200).
Proof. exact (eq_refl (term486 _121855 _121856 s t x _75200)). Qed.
Lemma lem5949383 {_121855 _121856 : Type'} (_75200 : _121856) (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term261 _121855 _121856 s t x _75200.
Proof. exact (EQ_MP (@lem5949382 _121855 _121856 s t x _75200) (@lem5949381 _121855 _121856 _75200 i j a s t x h1)). Qed.
Lemma lem5949384 {_121855 _121856 : Type'} (_75200 : _121856) (_75201 : _121855) (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term487 _121855 _121856 s t x _75200 _75201.
Proof. exact (@lem5949383 _121855 _121856 _75200 i j a s t x h1 _75201). Qed.
Lemma lem5949385 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75200 : _121856) (_75201 : _121855) : (term487 _121855 _121856 s t x _75200 _75201) = (term253 _121855 _121856 s t x _75200 _75201).
Proof. exact (eq_refl (term487 _121855 _121856 s t x _75200 _75201)). Qed.
Lemma lem5949386 {_121855 _121856 : Type'} (_75200 : _121856) (_75201 : _121855) (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term253 _121855 _121856 s t x _75200 _75201.
Proof. exact (EQ_MP (@lem5949385 _121855 _121856 s t x _75200 _75201) (@lem5949384 _121855 _121856 _75200 _75201 i j a s t x h1)). Qed.
Lemma lem5949387 {_121855 _121856 : Type'} (_75202 : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term488 _121855 _121856 a s t x _75202.
Proof. exact (@lem5949310 _121855 _121856 a j s t x i' j' h1 _75202). Qed.
Lemma lem5949388 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75202 : _121856) : (term488 _121855 _121856 a s t x _75202) = (term482 _121855 _121856 a s t x _75202).
Proof. exact (eq_refl (term488 _121855 _121856 a s t x _75202)). Qed.
Lemma lem5949389 {_121855 _121856 : Type'} (_75202 : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term482 _121855 _121856 a s t x _75202.
Proof. exact (EQ_MP (@lem5949388 _121855 _121856 a s t x _75202) (@lem5949387 _121855 _121856 _75202 a j s t x i' j' h1)). Qed.
Lemma lem5949390 {_121855 _121856 : Type'} (_75202 : _121856) (_75203 : _121855) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term489 _121855 _121856 a s t x _75202 _75203.
Proof. exact (@lem5949389 _121855 _121856 _75202 a j s t x i' j' h1 _75203). Qed.
Lemma lem5949391 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75202 : _121856) (_75203 : _121855) : (term489 _121855 _121856 a s t x _75202 _75203) = (term479 _121855 _121856 a s t x _75202 _75203).
Proof. exact (eq_refl (term489 _121855 _121856 a s t x _75202 _75203)). Qed.
Lemma lem5949392 {_121855 _121856 : Type'} (_75202 : _121856) (_75203 : _121855) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term479 _121855 _121856 a s t x _75202 _75203.
Proof. exact (EQ_MP (@lem5949391 _121855 _121856 a s t x _75202 _75203) (@lem5949390 _121855 _121856 _75202 _75203 a j s t x i' j' h1)). Qed.
Lemma lem5949393 {_121855 _121856 : Type'} (_75204 : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term488 _121855 _121856 a s t x _75204.
Proof. exact (@lem5949356 _121855 _121856 a j s t x i' j' h1 _75204). Qed.
Lemma lem5949394 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75204 : _121856) : (term488 _121855 _121856 a s t x _75204) = (term482 _121855 _121856 a s t x _75204).
Proof. exact (eq_refl (term488 _121855 _121856 a s t x _75204)). Qed.
Lemma lem5949395 {_121855 _121856 : Type'} (_75204 : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term482 _121855 _121856 a s t x _75204.
Proof. exact (EQ_MP (@lem5949394 _121855 _121856 a s t x _75204) (@lem5949393 _121855 _121856 _75204 a j s t x i' j' h1)). Qed.
Lemma lem5949396 {_121855 _121856 : Type'} (_75204 : _121856) (_75205 : _121855) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term489 _121855 _121856 a s t x _75204 _75205.
Proof. exact (@lem5949395 _121855 _121856 _75204 a j s t x i' j' h1 _75205). Qed.
Lemma lem5949397 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75204 : _121856) (_75205 : _121855) : (term489 _121855 _121856 a s t x _75204 _75205) = (term479 _121855 _121856 a s t x _75204 _75205).
Proof. exact (eq_refl (term489 _121855 _121856 a s t x _75204 _75205)). Qed.
Lemma lem5949398 {_121855 _121856 : Type'} (_75204 : _121856) (_75205 : _121855) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term479 _121855 _121856 a s t x _75204 _75205.
Proof. exact (EQ_MP (@lem5949397 _121855 _121856 a s t x _75204 _75205) (@lem5949396 _121855 _121856 _75204 _75205 a j s t x i' j' h1)). Qed.
Lemma lem5949400 {_121855 _121856 : Type'} (_75202 : _121856) (_75203 : _121855) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term490 _121855 _121856 a t x _75202 _75203.
Proof. exact (proj1 (@lem5949392 _121855 _121856 _75202 _75203 a j s t x i' j' h1)). Qed.
Lemma lem5949401 {_121855 _121856 : Type'} (_75204 : _121856) (_75205 : _121855) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term253 _121855 _121856 s t x _75204 _75205.
Proof. exact (proj2 (@lem5949398 _121855 _121856 _75204 _75205 a j s t x i' j' h1)). Qed.
Lemma lem5949422 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : x = (@pair _121856 _121855 i j).
Proof. exact (proj2 (@lem5949160 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949424 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : t i j.
Proof. exact (proj2 (@lem5949164 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949426 {_121856 : Type'} (i : _121856) (a : _121856) (h1 : i = a) : i = a.
Proof. exact (h1). Qed.
Lemma lem5949443 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75200 : _121856) (_75201 : _121855) : (term253 _121855 _121856 s t x _75200 _75201) = (term491 _121855 _121856 s t x _75200 _75201).
Proof. exact (@lem5947482 (term476 _121856 s _75200) (term211 _121855 _121856 t _75200 _75201) (term217 _121855 _121856 x _75200 _75201)). Qed.
Lemma lem5949444 {_121855 _121856 : Type'} (_75200 : _121856) (_75201 : _121855) (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term491 _121855 _121856 s t x _75200 _75201.
Proof. exact (EQ_MP (@lem5949443 _121855 _121856 s t x _75200 _75201) (@lem5949386 _121855 _121856 _75200 _75201 i j a s t x h1)). Qed.
Lemma lem5949446 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : x = (@pair _121856 _121855 i j).
Proof. exact (proj2 (@lem5949160 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949450 {_121856 : Type'} (s : _121856 -> Prop) (i : _121856) (h1 : s i) : s i.
Proof. exact (h1). Qed.
Lemma lem5949452 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term136 _121855 _121856 x t a j) : x = (@pair _121856 _121855 a j).
Proof. exact (proj1 (@lem5949171 _121855 _121856 x t a j h1)). Qed.
Lemma lem5949465 {_121855 _121856 : Type'} (a : _121856) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75202 : _121856) (_75203 : _121855) : (term490 _121855 _121856 a t x _75202 _75203) = (term492 _121855 _121856 a t x _75202 _75203).
Proof. exact (@lem5947482 (term475 _121856 _75202 a) (term211 _121855 _121856 t _75202 _75203) (term217 _121855 _121856 x _75202 _75203)). Qed.
Lemma lem5949466 {_121855 _121856 : Type'} (_75202 : _121856) (_75203 : _121855) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term492 _121855 _121856 a t x _75202 _75203.
Proof. exact (EQ_MP (@lem5949465 _121855 _121856 a t x _75202 _75203) (@lem5949400 _121855 _121856 _75202 _75203 a j s t x i' j' h1)). Qed.
Lemma lem5949480 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : x = (@pair _121856 _121855 i' j').
Proof. exact (proj2 (@lem5949172 _121855 _121856 s t x i' j' h1)). Qed.
Lemma lem5949507 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75204 : _121856) (_75205 : _121855) : (term253 _121855 _121856 s t x _75204 _75205) = (term491 _121855 _121856 s t x _75204 _75205).
Proof. exact (@lem5947482 (term476 _121856 s _75204) (term211 _121855 _121856 t _75204 _75205) (term217 _121855 _121856 x _75204 _75205)). Qed.
Lemma lem5949508 {_121855 _121856 : Type'} (_75204 : _121856) (_75205 : _121855) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : term491 _121855 _121856 s t x _75204 _75205.
Proof. exact (EQ_MP (@lem5949507 _121855 _121856 s t x _75204 _75205) (@lem5949401 _121855 _121856 _75204 _75205 a j s t x i' j' h1)). Qed.
Lemma lem5949536 {_121855 _121856 : Type'} (_75196 : _121855) (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term240 _121855 _121856 x t a _75196.
Proof. exact (EQ_MP (@lem5949370 _121855 _121856 x t a _75196) (@lem5949369 _121855 _121856 _75196 i j a s t x h1)). Qed.
Lemma lem5949551 {_121855 _121856 : Type'} (x : prod _121856 _121855) (j : _121855) : (term493 _121855 _121856 x j) = (term493 _121855 _121856 x j).
Proof. exact (eq_refl (term493 _121855 _121856 x j)). Qed.
Lemma lem5949552 {_121855 _121856 : Type'} (x : prod _121856 _121855) (j : _121855) (i : _121856) (a : _121856) (h1 : i = a) : (term494 _121855 _121856 x j i) = (term494 _121855 _121856 x j a).
Proof. exact (MK_COMB (@lem5949551 _121855 _121856 x j) (@lem5949426 _121856 i a h1)). Qed.
Lemma lem5949553 {_121855 _121856 : Type'} (x : prod _121856 _121855) (a : _121856) (j : _121855) : (term494 _121855 _121856 x j a) = (x = (@pair _121856 _121855 a j)).
Proof. exact (eq_refl (term494 _121855 _121856 x j a)). Qed.
Lemma lem5949554 {_121855 _121856 : Type'} (x : prod _121856 _121855) (j : _121855) (i : _121856) : (term495 _121855 _121856 x j i) = (term495 _121855 _121856 x j i).
Proof. exact (eq_refl (term495 _121855 _121856 x j i)). Qed.
Lemma lem5949555 {_121855 _121856 : Type'} (i : _121856) (x : prod _121856 _121855) (a : _121856) (j : _121855) : ((term494 _121855 _121856 x j i) = (term494 _121855 _121856 x j a)) = ((term494 _121855 _121856 x j i) = (x = (@pair _121856 _121855 a j))).
Proof. exact (MK_COMB (@lem5949554 _121855 _121856 x j i) (@lem5949553 _121855 _121856 x a j)). Qed.
Lemma lem5949556 {_121855 _121856 : Type'} (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term494 _121855 _121856 x j i) = (x = (@pair _121856 _121855 i j)).
Proof. exact (eq_refl (term494 _121855 _121856 x j i)). Qed.
Lemma lem5949557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5949558 {_121855 _121856 : Type'} (x : prod _121856 _121855) (i : _121856) (j : _121855) : (term495 _121855 _121856 x j i) = (term496 _121855 _121856 x i j).
Proof. exact (MK_COMB (@lem5949557) (@lem5949556 _121855 _121856 x i j)). Qed.
Lemma lem5949559 {_121855 _121856 : Type'} (x : prod _121856 _121855) (a : _121856) (j : _121855) : (x = (@pair _121856 _121855 a j)) = (x = (@pair _121856 _121855 a j)).
Proof. exact (eq_refl (x = (@pair _121856 _121855 a j))). Qed.
Lemma lem5949560 {_121855 _121856 : Type'} (i : _121856) (x : prod _121856 _121855) (a : _121856) (j : _121855) : ((term494 _121855 _121856 x j i) = (x = (@pair _121856 _121855 a j))) = ((x = (@pair _121856 _121855 i j)) = (x = (@pair _121856 _121855 a j))).
Proof. exact (MK_COMB (@lem5949558 _121855 _121856 x i j) (@lem5949559 _121855 _121856 x a j)). Qed.
Lemma lem5949561 {_121855 _121856 : Type'} (i : _121856) (x : prod _121856 _121855) (a : _121856) (j : _121855) : ((term494 _121855 _121856 x j i) = (term494 _121855 _121856 x j a)) = ((x = (@pair _121856 _121855 i j)) = (x = (@pair _121856 _121855 a j))).
Proof. exact (TRANS (@lem5949555 _121855 _121856 i x a j) (@lem5949560 _121855 _121856 i x a j)). Qed.
Lemma lem5949562 {_121855 _121856 : Type'} (x : prod _121856 _121855) (j : _121855) (i : _121856) (a : _121856) (h1 : i = a) : (x = (@pair _121856 _121855 i j)) = (x = (@pair _121856 _121855 a j)).
Proof. exact (EQ_MP (@lem5949561 _121855 _121856 i x a j) (@lem5949552 _121855 _121856 x j i a h1)). Qed.
Lemma lem5949563 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : x = (@pair _121856 _121855 a j).
Proof. exact (EQ_MP (@lem5949562 _121855 _121856 x j i a h2) (@lem5949422 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949564 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (j : _121855) : (term497 _121855 _121856 t j) = (term497 _121855 _121856 t j).
Proof. exact (eq_refl (term497 _121855 _121856 t j)). Qed.
Lemma lem5949565 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (j : _121855) (i : _121856) (a : _121856) (h1 : i = a) : (term498 _121855 _121856 t j i) = (term498 _121855 _121856 t j a).
Proof. exact (MK_COMB (@lem5949564 _121855 _121856 t j) (@lem5949426 _121856 i a h1)). Qed.
Lemma lem5949566 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (j : _121855) : (term498 _121855 _121856 t j a) = (t a j).
Proof. exact (eq_refl (term498 _121855 _121856 t j a)). Qed.
Lemma lem5949567 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (j : _121855) (i : _121856) : (term499 _121855 _121856 t j i) = (term499 _121855 _121856 t j i).
Proof. exact (eq_refl (term499 _121855 _121856 t j i)). Qed.
Lemma lem5949568 {_121855 _121856 : Type'} (i : _121856) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) : ((term498 _121855 _121856 t j i) = (term498 _121855 _121856 t j a)) = ((term498 _121855 _121856 t j i) = (t a j)).
Proof. exact (MK_COMB (@lem5949567 _121855 _121856 t j i) (@lem5949566 _121855 _121856 t a j)). Qed.
Lemma lem5949569 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term498 _121855 _121856 t j i) = (t i j).
Proof. exact (eq_refl (term498 _121855 _121856 t j i)). Qed.
Lemma lem5949570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5949571 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term499 _121855 _121856 t j i) = (term500 _121855 _121856 t i j).
Proof. exact (MK_COMB (@lem5949570) (@lem5949569 _121855 _121856 t i j)). Qed.
Lemma lem5949572 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (j : _121855) : (t a j) = (t a j).
Proof. exact (eq_refl (t a j)). Qed.
Lemma lem5949573 {_121855 _121856 : Type'} (i : _121856) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) : ((term498 _121855 _121856 t j i) = (t a j)) = ((t i j) = (t a j)).
Proof. exact (MK_COMB (@lem5949571 _121855 _121856 t i j) (@lem5949572 _121855 _121856 t a j)). Qed.
Lemma lem5949574 {_121855 _121856 : Type'} (i : _121856) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) : ((term498 _121855 _121856 t j i) = (term498 _121855 _121856 t j a)) = ((t i j) = (t a j)).
Proof. exact (TRANS (@lem5949568 _121855 _121856 i t a j) (@lem5949573 _121855 _121856 i t a j)). Qed.
Lemma lem5949575 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (j : _121855) (i : _121856) (a : _121856) (h1 : i = a) : (t i j) = (t a j).
Proof. exact (EQ_MP (@lem5949574 _121855 _121856 i t a j) (@lem5949565 _121855 _121856 t j i a h1)). Qed.
Lemma lem5949591 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) : (term501 _121855 _121856 t a _75196) = (term501 _121855 _121856 t a _75196).
Proof. exact (eq_refl (term501 _121855 _121856 t a _75196)). Qed.
Lemma lem5949592 {_121855 _121856 : Type'} (_75196 : _121855) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : (term502 _121855 _121856 t a _75196 x) = (term503 _121855 _121856 t _75196 a j).
Proof. exact (MK_COMB (@lem5949591 _121855 _121856 t a _75196) (@lem5949563 _121855 _121856 j s t x i a h1 h2)). Qed.
Lemma lem5949593 {_121855 _121856 : Type'} (j : _121855) (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) : (term503 _121855 _121856 t _75196 a j) = (term504 _121855 _121856 j t a _75196).
Proof. exact (eq_refl (term503 _121855 _121856 t _75196 a j)). Qed.
Lemma lem5949594 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) (x : prod _121856 _121855) : (term505 _121855 _121856 t a _75196 x) = (term505 _121855 _121856 t a _75196 x).
Proof. exact (eq_refl (term505 _121855 _121856 t a _75196 x)). Qed.
Lemma lem5949595 {_121855 _121856 : Type'} (x : prod _121856 _121855) (j : _121855) (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) : ((term502 _121855 _121856 t a _75196 x) = (term503 _121855 _121856 t _75196 a j)) = ((term502 _121855 _121856 t a _75196 x) = (term504 _121855 _121856 j t a _75196)).
Proof. exact (MK_COMB (@lem5949594 _121855 _121856 t a _75196 x) (@lem5949593 _121855 _121856 j t a _75196)). Qed.
Lemma lem5949596 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) : (term502 _121855 _121856 t a _75196 x) = (term240 _121855 _121856 x t a _75196).
Proof. exact (eq_refl (term502 _121855 _121856 t a _75196 x)). Qed.
Lemma lem5949597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5949598 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) : (term505 _121855 _121856 t a _75196 x) = (term506 _121855 _121856 x t a _75196).
Proof. exact (MK_COMB (@lem5949597) (@lem5949596 _121855 _121856 x t a _75196)). Qed.
Lemma lem5949599 {_121855 _121856 : Type'} (j : _121855) (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) : (term504 _121855 _121856 j t a _75196) = (term504 _121855 _121856 j t a _75196).
Proof. exact (eq_refl (term504 _121855 _121856 j t a _75196)). Qed.
Lemma lem5949600 {_121855 _121856 : Type'} (x : prod _121856 _121855) (j : _121855) (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) : ((term502 _121855 _121856 t a _75196 x) = (term504 _121855 _121856 j t a _75196)) = ((term240 _121855 _121856 x t a _75196) = (term504 _121855 _121856 j t a _75196)).
Proof. exact (MK_COMB (@lem5949598 _121855 _121856 x t a _75196) (@lem5949599 _121855 _121856 j t a _75196)). Qed.
Lemma lem5949601 {_121855 _121856 : Type'} (x : prod _121856 _121855) (j : _121855) (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) : ((term502 _121855 _121856 t a _75196 x) = (term503 _121855 _121856 t _75196 a j)) = ((term240 _121855 _121856 x t a _75196) = (term504 _121855 _121856 j t a _75196)).
Proof. exact (TRANS (@lem5949595 _121855 _121856 x j t a _75196) (@lem5949600 _121855 _121856 x j t a _75196)). Qed.
Lemma lem5949602 {_121855 _121856 : Type'} (_75196 : _121855) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : (term240 _121855 _121856 x t a _75196) = (term504 _121855 _121856 j t a _75196).
Proof. exact (EQ_MP (@lem5949601 _121855 _121856 x j t a _75196) (@lem5949592 _121855 _121856 _75196 j s t x i a h1 h2)). Qed.
Lemma lem5949603 {_121855 _121856 : Type'} (_75196 : _121855) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : term504 _121855 _121856 j t a _75196.
Proof. exact (EQ_MP (@lem5949602 _121855 _121856 _75196 j s t x i a h1 h2) (@lem5949536 _121855 _121856 _75196 i j a s t x h1)). Qed.
Lemma lem5949658 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (_75200 : _121856) (_75201 : _121855) : (term507 _121855 _121856 s t _75200 _75201) = (term507 _121855 _121856 s t _75200 _75201).
Proof. exact (eq_refl (term507 _121855 _121856 s t _75200 _75201)). Qed.
Lemma lem5949659 {_121855 _121856 : Type'} (_75200 : _121856) (_75201 : _121855) (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : (term508 _121855 _121856 s t _75200 _75201 x) = (term509 _121855 _121856 s t _75200 _75201 i j).
Proof. exact (MK_COMB (@lem5949658 _121855 _121856 s t _75200 _75201) (@lem5949446 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949660 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (_75200 : _121856) (_75201 : _121855) : (term509 _121855 _121856 s t _75200 _75201 i j) = (term510 _121855 _121856 s t i j _75200 _75201).
Proof. exact (eq_refl (term509 _121855 _121856 s t _75200 _75201 i j)). Qed.
Lemma lem5949661 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (_75200 : _121856) (_75201 : _121855) (x : prod _121856 _121855) : (term511 _121855 _121856 s t _75200 _75201 x) = (term511 _121855 _121856 s t _75200 _75201 x).
Proof. exact (eq_refl (term511 _121855 _121856 s t _75200 _75201 x)). Qed.
Lemma lem5949662 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (_75200 : _121856) (_75201 : _121855) : ((term508 _121855 _121856 s t _75200 _75201 x) = (term509 _121855 _121856 s t _75200 _75201 i j)) = ((term508 _121855 _121856 s t _75200 _75201 x) = (term510 _121855 _121856 s t i j _75200 _75201)).
Proof. exact (MK_COMB (@lem5949661 _121855 _121856 s t _75200 _75201 x) (@lem5949660 _121855 _121856 s t i j _75200 _75201)). Qed.
Lemma lem5949663 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75200 : _121856) (_75201 : _121855) : (term508 _121855 _121856 s t _75200 _75201 x) = (term491 _121855 _121856 s t x _75200 _75201).
Proof. exact (eq_refl (term508 _121855 _121856 s t _75200 _75201 x)). Qed.
Lemma lem5949664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5949665 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75200 : _121856) (_75201 : _121855) : (term511 _121855 _121856 s t _75200 _75201 x) = (term512 _121855 _121856 s t x _75200 _75201).
Proof. exact (MK_COMB (@lem5949664) (@lem5949663 _121855 _121856 s t x _75200 _75201)). Qed.
Lemma lem5949666 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (_75200 : _121856) (_75201 : _121855) : (term510 _121855 _121856 s t i j _75200 _75201) = (term510 _121855 _121856 s t i j _75200 _75201).
Proof. exact (eq_refl (term510 _121855 _121856 s t i j _75200 _75201)). Qed.
Lemma lem5949667 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (_75200 : _121856) (_75201 : _121855) : ((term508 _121855 _121856 s t _75200 _75201 x) = (term510 _121855 _121856 s t i j _75200 _75201)) = ((term491 _121855 _121856 s t x _75200 _75201) = (term510 _121855 _121856 s t i j _75200 _75201)).
Proof. exact (MK_COMB (@lem5949665 _121855 _121856 s t x _75200 _75201) (@lem5949666 _121855 _121856 s t i j _75200 _75201)). Qed.
Lemma lem5949668 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (_75200 : _121856) (_75201 : _121855) : ((term508 _121855 _121856 s t _75200 _75201 x) = (term509 _121855 _121856 s t _75200 _75201 i j)) = ((term491 _121855 _121856 s t x _75200 _75201) = (term510 _121855 _121856 s t i j _75200 _75201)).
Proof. exact (TRANS (@lem5949662 _121855 _121856 x s t i j _75200 _75201) (@lem5949667 _121855 _121856 x s t i j _75200 _75201)). Qed.
Lemma lem5949669 {_121855 _121856 : Type'} (_75200 : _121856) (_75201 : _121855) (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : (term491 _121855 _121856 s t x _75200 _75201) = (term510 _121855 _121856 s t i j _75200 _75201).
Proof. exact (EQ_MP (@lem5949668 _121855 _121856 x s t i j _75200 _75201) (@lem5949659 _121855 _121856 _75200 _75201 i j a s t x h1)). Qed.
Lemma lem5949670 {_121855 _121856 : Type'} (_75200 : _121856) (_75201 : _121855) (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term510 _121855 _121856 s t i j _75200 _75201.
Proof. exact (EQ_MP (@lem5949669 _121855 _121856 _75200 _75201 i j a s t x h1) (@lem5949444 _121855 _121856 _75200 _75201 i j a s t x h1)). Qed.
Lemma lem5949698 {_121856 : Type'} (s : _121856 -> Prop) (i : _121856) (h1 : s i) : s i.
Proof. exact (h1). Qed.
Lemma lem5949727 {_121855 _121856 : Type'} (a : _121856) (t : type1470 _121855 _121856) (_75202 : _121856) (_75203 : _121855) : (term513 _121855 _121856 a t _75202 _75203) = (term513 _121855 _121856 a t _75202 _75203).
Proof. exact (eq_refl (term513 _121855 _121856 a t _75202 _75203)). Qed.
Lemma lem5949728 {_121855 _121856 : Type'} (_75202 : _121856) (_75203 : _121855) (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term136 _121855 _121856 x t a j) : (term514 _121855 _121856 a t _75202 _75203 x) = (term515 _121855 _121856 t _75202 _75203 a j).
Proof. exact (MK_COMB (@lem5949727 _121855 _121856 a t _75202 _75203) (@lem5949452 _121855 _121856 x t a j h1)). Qed.
Lemma lem5949729 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (_75202 : _121856) (_75203 : _121855) : (term515 _121855 _121856 t _75202 _75203 a j) = (term516 _121855 _121856 t a j _75202 _75203).
Proof. exact (eq_refl (term515 _121855 _121856 t _75202 _75203 a j)). Qed.
Lemma lem5949730 {_121855 _121856 : Type'} (a : _121856) (t : type1470 _121855 _121856) (_75202 : _121856) (_75203 : _121855) (x : prod _121856 _121855) : (term517 _121855 _121856 a t _75202 _75203 x) = (term517 _121855 _121856 a t _75202 _75203 x).
Proof. exact (eq_refl (term517 _121855 _121856 a t _75202 _75203 x)). Qed.
Lemma lem5949731 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (_75202 : _121856) (_75203 : _121855) : ((term514 _121855 _121856 a t _75202 _75203 x) = (term515 _121855 _121856 t _75202 _75203 a j)) = ((term514 _121855 _121856 a t _75202 _75203 x) = (term516 _121855 _121856 t a j _75202 _75203)).
Proof. exact (MK_COMB (@lem5949730 _121855 _121856 a t _75202 _75203 x) (@lem5949729 _121855 _121856 t a j _75202 _75203)). Qed.
Lemma lem5949732 {_121855 _121856 : Type'} (a : _121856) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75202 : _121856) (_75203 : _121855) : (term514 _121855 _121856 a t _75202 _75203 x) = (term492 _121855 _121856 a t x _75202 _75203).
Proof. exact (eq_refl (term514 _121855 _121856 a t _75202 _75203 x)). Qed.
Lemma lem5949733 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5949734 {_121855 _121856 : Type'} (a : _121856) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75202 : _121856) (_75203 : _121855) : (term517 _121855 _121856 a t _75202 _75203 x) = (term518 _121855 _121856 a t x _75202 _75203).
Proof. exact (MK_COMB (@lem5949733) (@lem5949732 _121855 _121856 a t x _75202 _75203)). Qed.
Lemma lem5949735 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (_75202 : _121856) (_75203 : _121855) : (term516 _121855 _121856 t a j _75202 _75203) = (term516 _121855 _121856 t a j _75202 _75203).
Proof. exact (eq_refl (term516 _121855 _121856 t a j _75202 _75203)). Qed.
Lemma lem5949736 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (_75202 : _121856) (_75203 : _121855) : ((term514 _121855 _121856 a t _75202 _75203 x) = (term516 _121855 _121856 t a j _75202 _75203)) = ((term492 _121855 _121856 a t x _75202 _75203) = (term516 _121855 _121856 t a j _75202 _75203)).
Proof. exact (MK_COMB (@lem5949734 _121855 _121856 a t x _75202 _75203) (@lem5949735 _121855 _121856 t a j _75202 _75203)). Qed.
Lemma lem5949737 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (_75202 : _121856) (_75203 : _121855) : ((term514 _121855 _121856 a t _75202 _75203 x) = (term515 _121855 _121856 t _75202 _75203 a j)) = ((term492 _121855 _121856 a t x _75202 _75203) = (term516 _121855 _121856 t a j _75202 _75203)).
Proof. exact (TRANS (@lem5949731 _121855 _121856 x t a j _75202 _75203) (@lem5949736 _121855 _121856 x t a j _75202 _75203)). Qed.
Lemma lem5949738 {_121855 _121856 : Type'} (_75202 : _121856) (_75203 : _121855) (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term136 _121855 _121856 x t a j) : (term492 _121855 _121856 a t x _75202 _75203) = (term516 _121855 _121856 t a j _75202 _75203).
Proof. exact (EQ_MP (@lem5949737 _121855 _121856 x t a j _75202 _75203) (@lem5949728 _121855 _121856 _75202 _75203 x t a j h1)). Qed.
Lemma lem5949739 {_121855 _121856 : Type'} (_75202 : _121856) (_75203 : _121855) (s : _121856 -> Prop) (i' : _121856) (j' : _121855) (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term136 _121855 _121856 x t a j) : term516 _121855 _121856 t a j _75202 _75203.
Proof. exact (EQ_MP (@lem5949738 _121855 _121856 _75202 _75203 x t a j h2) (@lem5949466 _121855 _121856 _75202 _75203 a j s t x i' j' h1)). Qed.
Lemma lem5949808 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (_75204 : _121856) (_75205 : _121855) : (term507 _121855 _121856 s t _75204 _75205) = (term507 _121855 _121856 s t _75204 _75205).
Proof. exact (eq_refl (term507 _121855 _121856 s t _75204 _75205)). Qed.
Lemma lem5949809 {_121855 _121856 : Type'} (_75204 : _121856) (_75205 : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : (term508 _121855 _121856 s t _75204 _75205 x) = (term509 _121855 _121856 s t _75204 _75205 i' j').
Proof. exact (MK_COMB (@lem5949808 _121855 _121856 s t _75204 _75205) (@lem5949480 _121855 _121856 s t x i' j' h1)). Qed.
Lemma lem5949810 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i' : _121856) (j' : _121855) (_75204 : _121856) (_75205 : _121855) : (term509 _121855 _121856 s t _75204 _75205 i' j') = (term510 _121855 _121856 s t i' j' _75204 _75205).
Proof. exact (eq_refl (term509 _121855 _121856 s t _75204 _75205 i' j')). Qed.
Lemma lem5949811 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (_75204 : _121856) (_75205 : _121855) (x : prod _121856 _121855) : (term511 _121855 _121856 s t _75204 _75205 x) = (term511 _121855 _121856 s t _75204 _75205 x).
Proof. exact (eq_refl (term511 _121855 _121856 s t _75204 _75205 x)). Qed.
Lemma lem5949812 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i' : _121856) (j' : _121855) (_75204 : _121856) (_75205 : _121855) : ((term508 _121855 _121856 s t _75204 _75205 x) = (term509 _121855 _121856 s t _75204 _75205 i' j')) = ((term508 _121855 _121856 s t _75204 _75205 x) = (term510 _121855 _121856 s t i' j' _75204 _75205)).
Proof. exact (MK_COMB (@lem5949811 _121855 _121856 s t _75204 _75205 x) (@lem5949810 _121855 _121856 s t i' j' _75204 _75205)). Qed.
Lemma lem5949813 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75204 : _121856) (_75205 : _121855) : (term508 _121855 _121856 s t _75204 _75205 x) = (term491 _121855 _121856 s t x _75204 _75205).
Proof. exact (eq_refl (term508 _121855 _121856 s t _75204 _75205 x)). Qed.
Lemma lem5949814 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5949815 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (_75204 : _121856) (_75205 : _121855) : (term511 _121855 _121856 s t _75204 _75205 x) = (term512 _121855 _121856 s t x _75204 _75205).
Proof. exact (MK_COMB (@lem5949814) (@lem5949813 _121855 _121856 s t x _75204 _75205)). Qed.
Lemma lem5949816 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i' : _121856) (j' : _121855) (_75204 : _121856) (_75205 : _121855) : (term510 _121855 _121856 s t i' j' _75204 _75205) = (term510 _121855 _121856 s t i' j' _75204 _75205).
Proof. exact (eq_refl (term510 _121855 _121856 s t i' j' _75204 _75205)). Qed.
Lemma lem5949817 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i' : _121856) (j' : _121855) (_75204 : _121856) (_75205 : _121855) : ((term508 _121855 _121856 s t _75204 _75205 x) = (term510 _121855 _121856 s t i' j' _75204 _75205)) = ((term491 _121855 _121856 s t x _75204 _75205) = (term510 _121855 _121856 s t i' j' _75204 _75205)).
Proof. exact (MK_COMB (@lem5949815 _121855 _121856 s t x _75204 _75205) (@lem5949816 _121855 _121856 s t i' j' _75204 _75205)). Qed.
Lemma lem5949818 {_121855 _121856 : Type'} (x : prod _121856 _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i' : _121856) (j' : _121855) (_75204 : _121856) (_75205 : _121855) : ((term508 _121855 _121856 s t _75204 _75205 x) = (term509 _121855 _121856 s t _75204 _75205 i' j')) = ((term491 _121855 _121856 s t x _75204 _75205) = (term510 _121855 _121856 s t i' j' _75204 _75205)).
Proof. exact (TRANS (@lem5949812 _121855 _121856 x s t i' j' _75204 _75205) (@lem5949817 _121855 _121856 x s t i' j' _75204 _75205)). Qed.
Lemma lem5949819 {_121855 _121856 : Type'} (_75204 : _121856) (_75205 : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : (term491 _121855 _121856 s t x _75204 _75205) = (term510 _121855 _121856 s t i' j' _75204 _75205).
Proof. exact (EQ_MP (@lem5949818 _121855 _121856 x s t i' j' _75204 _75205) (@lem5949809 _121855 _121856 _75204 _75205 s t x i' j' h1)). Qed.
Lemma lem5949820 {_121855 _121856 : Type'} (_75204 : _121856) (_75205 : _121855) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term175 _121855 _121856 s t x i' j') : term510 _121855 _121856 s t i' j' _75204 _75205.
Proof. exact (EQ_MP (@lem5949819 _121855 _121856 _75204 _75205 s t x i' j' h2) (@lem5949508 _121855 _121856 _75204 _75205 a j s t x i' j' h1)). Qed.
Lemma lem5949874 {_121855 _121856 : Type'} (x : prod _121856 _121855) : x = x.
Proof. exact (@lem21386 (prod _121856 _121855) x). Qed.
Lemma lem5949875 {_121855 _121856 : Type'} (x : prod _121856 _121855) : x = x.
Proof. exact (@lem5949874 _121855 _121856 x). Qed.
Lemma lem5949876 {_121855 _121856 : Type'} (a : _121856) (j : _121855) : (@pair _121856 _121855 a j) = (@pair _121856 _121855 a j).
Proof. exact (@lem5949875 _121855 _121856 (@pair _121856 _121855 a j)). Qed.
Lemma lem5949877 {_121855 _121856 : Type'} (a : _121856) (j : _121855) : term519 _121855 _121856 a j.
Proof. exact (fun h0 : term520 _121855 _121856 a j => @lem5949876 _121855 _121856 a j). Qed.
Lemma lem5949879 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5949880 {_121855 _121856 : Type'} (a : _121856) (j : _121855) : (term519 _121855 _121856 a j) = ((@pair _121856 _121855 a j) = (@pair _121856 _121855 a j)).
Proof. exact (@lem5949879 ((@pair _121856 _121855 a j) = (@pair _121856 _121855 a j))). Qed.
Lemma lem5949881 {_121855 _121856 : Type'} (a : _121856) (j : _121855) : (@pair _121856 _121855 a j) = (@pair _121856 _121855 a j).
Proof. exact (EQ_MP (@lem5949880 _121855 _121856 a j) (@lem5949877 _121855 _121856 a j)). Qed.
Lemma lem5949883 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : t a j.
Proof. exact (EQ_MP (@lem5949575 _121855 _121856 t j i a h2) (@lem5949424 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949884 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : term522 _121855 _121856 t a j.
Proof. exact (fun h0 : term211 _121855 _121856 t a j => @lem5949883 _121855 _121856 j s t x i a h1 h2). Qed.
Lemma lem5949886 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5949887 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (j : _121855) : (term522 _121855 _121856 t a j) = (t a j).
Proof. exact (@lem5949886 (t a j)). Qed.
Lemma lem5949888 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : t a j.
Proof. exact (EQ_MP (@lem5949887 _121855 _121856 t a j) (@lem5949884 _121855 _121856 j s t x i a h1 h2)). Qed.
Lemma lem5949890 (a : Prop) (b : Prop) : (term523 a b) = (term524 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5949891 {_121855 _121856 : Type'} (j : _121855) (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) : (term504 _121855 _121856 j t a _75196) = (term525 _121855 _121856 j t a _75196).
Proof. exact (@lem5949890 ((@pair _121856 _121855 a j) = (@pair _121856 _121855 a _75196)) (t a _75196)). Qed.
Lemma lem5949893 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5949894 {_121855 _121856 : Type'} (j : _121855) (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) : (term525 _121855 _121856 j t a _75196) = (term526 _121855 _121856 j t a _75196).
Proof. exact (@lem5949893 (term527 _121855 _121856 j t a _75196)). Qed.
Lemma lem5949895 {_121855 _121856 : Type'} (j : _121855) (t : type1470 _121855 _121856) (a : _121856) (_75196 : _121855) : (term504 _121855 _121856 j t a _75196) = (term526 _121855 _121856 j t a _75196).
Proof. exact (TRANS (@lem5949891 _121855 _121856 j t a _75196) (@lem5949894 _121855 _121856 j t a _75196)). Qed.
Lemma lem5949897 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : term528 _121855 _121856 t a j.
Proof. exact (conj (@lem5949881 _121855 _121856 a j) (@lem5949888 _121855 _121856 j s t x i a h1 h2)). Qed.
Lemma lem5949899 {_121855 _121856 : Type'} (_75196 : _121855) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : term526 _121855 _121856 j t a _75196.
Proof. exact (EQ_MP (@lem5949895 _121855 _121856 j t a _75196) (@lem5949603 _121855 _121856 _75196 j s t x i a h1 h2)). Qed.
Lemma lem5949900 {_121855 _121856 : Type'} (_75196 : _121855) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : term526 _121855 _121856 j t a _75196.
Proof. exact (@lem5949899 _121855 _121856 _75196 j s t x i a h1 h2). Qed.
Lemma lem5949901 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : term529 _121855 _121856 t a j.
Proof. exact (@lem5949900 _121855 _121856 j j s t x i a h1 h2). Qed.
Lemma lem5949904 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : False.
Proof. exact (@lem5949901 _121855 _121856 j s t x i a h1 h2 (@lem5949897 _121855 _121856 j s t x i a h1 h2)). Qed.
Lemma lem5949905 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : term530.
Proof. exact (fun h0 : ~ False => @lem5949904 _121855 _121856 j s t x i a h1 h2). Qed.
Lemma lem5949907 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5949908 : term530 = False.
Proof. exact (@lem5949907 False). Qed.
Lemma lem5949963 {_121856 : Type'} (s : _121856 -> Prop) (i : _121856) (h1 : s i) : s i.
Proof. exact (h1). Qed.
Lemma lem5949964 {_121856 : Type'} (s : _121856 -> Prop) (i : _121856) (h1 : s i) : term531 _121856 s i.
Proof. exact (fun h0 : term476 _121856 s i => @lem5949963 _121856 s i h1). Qed.
Lemma lem5949966 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5949967 {_121856 : Type'} (s : _121856 -> Prop) (i : _121856) : (term531 _121856 s i) = (s i).
Proof. exact (@lem5949966 (s i)). Qed.
Lemma lem5949968 {_121856 : Type'} (s : _121856 -> Prop) (i : _121856) (h1 : s i) : s i.
Proof. exact (EQ_MP (@lem5949967 _121856 s i) (@lem5949964 _121856 s i h1)). Qed.
Lemma lem5949970 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : t i j.
Proof. exact (proj2 (@lem5949164 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949971 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term522 _121855 _121856 t i j.
Proof. exact (fun h0 : term211 _121855 _121856 t i j => @lem5949970 _121855 _121856 i j a s t x h1). Qed.
Lemma lem5949973 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5949974 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (i : _121856) (j : _121855) : (term522 _121855 _121856 t i j) = (t i j).
Proof. exact (@lem5949973 (t i j)). Qed.
Lemma lem5949975 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : t i j.
Proof. exact (EQ_MP (@lem5949974 _121855 _121856 t i j) (@lem5949971 _121855 _121856 i j a s t x h1)). Qed.
Lemma lem5949977 {_121855 _121856 : Type'} (x : prod _121856 _121855) : x = x.
Proof. exact (@lem21386 (prod _121856 _121855) x). Qed.
Lemma lem5949978 {_121855 _121856 : Type'} (x : prod _121856 _121855) : x = x.
Proof. exact (@lem5949977 _121855 _121856 x). Qed.
Lemma lem5949979 {_121855 _121856 : Type'} (i : _121856) (j : _121855) : (@pair _121856 _121855 i j) = (@pair _121856 _121855 i j).
Proof. exact (@lem5949978 _121855 _121856 (@pair _121856 _121855 i j)). Qed.
Lemma lem5949980 {_121855 _121856 : Type'} (i : _121856) (j : _121855) : term519 _121855 _121856 i j.
Proof. exact (fun h0 : term520 _121855 _121856 i j => @lem5949979 _121855 _121856 i j). Qed.
Lemma lem5949982 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5949983 {_121855 _121856 : Type'} (i : _121856) (j : _121855) : (term519 _121855 _121856 i j) = ((@pair _121856 _121855 i j) = (@pair _121856 _121855 i j)).
Proof. exact (@lem5949982 ((@pair _121856 _121855 i j) = (@pair _121856 _121855 i j))). Qed.
Lemma lem5949984 {_121855 _121856 : Type'} (i : _121856) (j : _121855) : (@pair _121856 _121855 i j) = (@pair _121856 _121855 i j).
Proof. exact (EQ_MP (@lem5949983 _121855 _121856 i j) (@lem5949980 _121855 _121856 i j)). Qed.
Lemma lem5949986 (a : Prop) (b : Prop) : (term523 a b) = (term524 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5949987 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (_75200 : _121856) (_75201 : _121855) : (term532 _121855 _121856 t i j _75200 _75201) = (term533 _121855 _121856 t i j _75200 _75201).
Proof. exact (@lem5949986 (t _75200 _75201) ((@pair _121856 _121855 i j) = (@pair _121856 _121855 _75200 _75201))). Qed.
Lemma lem5949988 {_121856 : Type'} (s : _121856 -> Prop) (_75200 : _121856) : (term534 _121856 s _75200) = (term534 _121856 s _75200).
Proof. exact (eq_refl (term534 _121856 s _75200)). Qed.
Lemma lem5949989 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (_75200 : _121856) (_75201 : _121855) : (term510 _121855 _121856 s t i j _75200 _75201) = (term535 _121855 _121856 s t i j _75200 _75201).
Proof. exact (MK_COMB (@lem5949988 _121856 s _75200) (@lem5949987 _121855 _121856 t i j _75200 _75201)). Qed.
Lemma lem5949991 (a : Prop) (b : Prop) : (term523 a b) = (term524 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5949992 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (_75200 : _121856) (_75201 : _121855) : (term535 _121855 _121856 s t i j _75200 _75201) = (term536 _121855 _121856 s t i j _75200 _75201).
Proof. exact (@lem5949991 (s _75200) (term537 _121855 _121856 t i j _75200 _75201)). Qed.
Lemma lem5949993 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (_75200 : _121856) (_75201 : _121855) : (term510 _121855 _121856 s t i j _75200 _75201) = (term536 _121855 _121856 s t i j _75200 _75201).
Proof. exact (TRANS (@lem5949989 _121855 _121856 s t i j _75200 _75201) (@lem5949992 _121855 _121856 s t i j _75200 _75201)). Qed.
Lemma lem5949995 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5949996 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (_75200 : _121856) (_75201 : _121855) : (term536 _121855 _121856 s t i j _75200 _75201) = (term538 _121855 _121856 s t i j _75200 _75201).
Proof. exact (@lem5949995 (term539 _121855 _121856 s t i j _75200 _75201)). Qed.
Lemma lem5949997 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i : _121856) (j : _121855) (_75200 : _121856) (_75201 : _121855) : (term510 _121855 _121856 s t i j _75200 _75201) = (term538 _121855 _121856 s t i j _75200 _75201).
Proof. exact (TRANS (@lem5949993 _121855 _121856 s t i j _75200 _75201) (@lem5949996 _121855 _121856 s t i j _75200 _75201)). Qed.
Lemma lem5949999 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term540 _121855 _121856 t i j.
Proof. exact (conj (@lem5949975 _121855 _121856 i j a s t x h1) (@lem5949984 _121855 _121856 i j)). Qed.
Lemma lem5950000 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : s i) (h2 : term311 _121855 _121856 i j a s t x) : term541 _121855 _121856 s t i j.
Proof. exact (conj (@lem5949968 _121856 s i h1) (@lem5949999 _121855 _121856 i j a s t x h2)). Qed.
Lemma lem5950002 {_121855 _121856 : Type'} (_75200 : _121856) (_75201 : _121855) (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term538 _121855 _121856 s t i j _75200 _75201.
Proof. exact (EQ_MP (@lem5949997 _121855 _121856 s t i j _75200 _75201) (@lem5949670 _121855 _121856 _75200 _75201 i j a s t x h1)). Qed.
Lemma lem5950003 {_121855 _121856 : Type'} (_75200 : _121856) (_75201 : _121855) (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term538 _121855 _121856 s t i j _75200 _75201.
Proof. exact (@lem5950002 _121855 _121856 _75200 _75201 i j a s t x h1). Qed.
Lemma lem5950004 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : term542 _121855 _121856 s t i j.
Proof. exact (@lem5950003 _121855 _121856 i j i j a s t x h1). Qed.
Lemma lem5950007 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : s i) (h2 : term311 _121855 _121856 i j a s t x) : False.
Proof. exact (@lem5950004 _121855 _121856 i j a s t x h2 (@lem5950000 _121855 _121856 i j a s t x h1 h2)). Qed.
Lemma lem5950008 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : s i) (h2 : term311 _121855 _121856 i j a s t x) : term530.
Proof. exact (fun h0 : ~ False => @lem5950007 _121855 _121856 i j a s t x h1 h2). Qed.
Lemma lem5950010 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5950011 : term530 = False.
Proof. exact (@lem5950010 False). Qed.
Lemma lem5950012 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : s i) (h2 : term311 _121855 _121856 i j a s t x) : False.
Proof. exact (EQ_MP (@lem5950011) (@lem5950008 _121855 _121856 i j a s t x h1 h2)). Qed.
Lemma lem5950066 {_121856 : Type'} (x : _121856) : x = x.
Proof. exact (@lem21386 _121856 x). Qed.
Lemma lem5950067 {_121856 : Type'} (x : _121856) : x = x.
Proof. exact (@lem5950066 _121856 x). Qed.
Lemma lem5950068 {_121856 : Type'} (a : _121856) : a = a.
Proof. exact (@lem5950067 _121856 a). Qed.
Lemma lem5950069 {_121856 : Type'} (a : _121856) : term543 _121856 a.
Proof. exact (fun h0 : term544 _121856 a => @lem5950068 _121856 a). Qed.
Lemma lem5950071 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5950072 {_121856 : Type'} (a : _121856) : (term543 _121856 a) = (a = a).
Proof. exact (@lem5950071 (a = a)). Qed.
Lemma lem5950073 {_121856 : Type'} (a : _121856) : a = a.
Proof. exact (EQ_MP (@lem5950072 _121856 a) (@lem5950069 _121856 a)). Qed.
Lemma lem5950075 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term136 _121855 _121856 x t a j) : t a j.
Proof. exact (proj2 (@lem5949171 _121855 _121856 x t a j h1)). Qed.
Lemma lem5950076 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term136 _121855 _121856 x t a j) : term522 _121855 _121856 t a j.
Proof. exact (fun h0 : term211 _121855 _121856 t a j => @lem5950075 _121855 _121856 x t a j h1). Qed.
Lemma lem5950078 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5950079 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (j : _121855) : (term522 _121855 _121856 t a j) = (t a j).
Proof. exact (@lem5950078 (t a j)). Qed.
Lemma lem5950080 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term136 _121855 _121856 x t a j) : t a j.
Proof. exact (EQ_MP (@lem5950079 _121855 _121856 t a j) (@lem5950076 _121855 _121856 x t a j h1)). Qed.
Lemma lem5950082 {_121855 _121856 : Type'} (x : prod _121856 _121855) : x = x.
Proof. exact (@lem21386 (prod _121856 _121855) x). Qed.
Lemma lem5950083 {_121855 _121856 : Type'} (x : prod _121856 _121855) : x = x.
Proof. exact (@lem5950082 _121855 _121856 x). Qed.
Lemma lem5950084 {_121855 _121856 : Type'} (a : _121856) (j : _121855) : (@pair _121856 _121855 a j) = (@pair _121856 _121855 a j).
Proof. exact (@lem5950083 _121855 _121856 (@pair _121856 _121855 a j)). Qed.
Lemma lem5950085 {_121855 _121856 : Type'} (a : _121856) (j : _121855) : term519 _121855 _121856 a j.
Proof. exact (fun h0 : term520 _121855 _121856 a j => @lem5950084 _121855 _121856 a j). Qed.
Lemma lem5950087 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5950088 {_121855 _121856 : Type'} (a : _121856) (j : _121855) : (term519 _121855 _121856 a j) = ((@pair _121856 _121855 a j) = (@pair _121856 _121855 a j)).
Proof. exact (@lem5950087 ((@pair _121856 _121855 a j) = (@pair _121856 _121855 a j))). Qed.
Lemma lem5950089 {_121855 _121856 : Type'} (a : _121856) (j : _121855) : (@pair _121856 _121855 a j) = (@pair _121856 _121855 a j).
Proof. exact (EQ_MP (@lem5950088 _121855 _121856 a j) (@lem5950085 _121855 _121856 a j)). Qed.
Lemma lem5950091 (a : Prop) (b : Prop) : (term523 a b) = (term524 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5950092 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (_75202 : _121856) (_75203 : _121855) : (term532 _121855 _121856 t a j _75202 _75203) = (term533 _121855 _121856 t a j _75202 _75203).
Proof. exact (@lem5950091 (t _75202 _75203) ((@pair _121856 _121855 a j) = (@pair _121856 _121855 _75202 _75203))). Qed.
Lemma lem5950093 {_121856 : Type'} (_75202 : _121856) (a : _121856) : (term545 _121856 _75202 a) = (term545 _121856 _75202 a).
Proof. exact (eq_refl (term545 _121856 _75202 a)). Qed.
Lemma lem5950094 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (_75202 : _121856) (_75203 : _121855) : (term516 _121855 _121856 t a j _75202 _75203) = (term546 _121855 _121856 t a j _75202 _75203).
Proof. exact (MK_COMB (@lem5950093 _121856 _75202 a) (@lem5950092 _121855 _121856 t a j _75202 _75203)). Qed.
Lemma lem5950096 (a : Prop) (b : Prop) : (term523 a b) = (term524 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5950097 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (_75202 : _121856) (_75203 : _121855) : (term546 _121855 _121856 t a j _75202 _75203) = (term547 _121855 _121856 t a j _75202 _75203).
Proof. exact (@lem5950096 (_75202 = a) (term537 _121855 _121856 t a j _75202 _75203)). Qed.
Lemma lem5950098 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (_75202 : _121856) (_75203 : _121855) : (term516 _121855 _121856 t a j _75202 _75203) = (term547 _121855 _121856 t a j _75202 _75203).
Proof. exact (TRANS (@lem5950094 _121855 _121856 t a j _75202 _75203) (@lem5950097 _121855 _121856 t a j _75202 _75203)). Qed.
Lemma lem5950100 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5950101 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (_75202 : _121856) (_75203 : _121855) : (term547 _121855 _121856 t a j _75202 _75203) = (term548 _121855 _121856 t a j _75202 _75203).
Proof. exact (@lem5950100 (term549 _121855 _121856 t a j _75202 _75203)). Qed.
Lemma lem5950102 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (_75202 : _121856) (_75203 : _121855) : (term516 _121855 _121856 t a j _75202 _75203) = (term548 _121855 _121856 t a j _75202 _75203).
Proof. exact (TRANS (@lem5950098 _121855 _121856 t a j _75202 _75203) (@lem5950101 _121855 _121856 t a j _75202 _75203)). Qed.
Lemma lem5950104 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term136 _121855 _121856 x t a j) : term540 _121855 _121856 t a j.
Proof. exact (conj (@lem5950080 _121855 _121856 x t a j h1) (@lem5950089 _121855 _121856 a j)). Qed.
Lemma lem5950105 {_121855 _121856 : Type'} (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term136 _121855 _121856 x t a j) : term550 _121855 _121856 t a j.
Proof. exact (conj (@lem5950073 _121856 a) (@lem5950104 _121855 _121856 x t a j h1)). Qed.
Lemma lem5950107 {_121855 _121856 : Type'} (_75202 : _121856) (_75203 : _121855) (s : _121856 -> Prop) (i' : _121856) (j' : _121855) (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term136 _121855 _121856 x t a j) : term548 _121855 _121856 t a j _75202 _75203.
Proof. exact (EQ_MP (@lem5950102 _121855 _121856 t a j _75202 _75203) (@lem5949739 _121855 _121856 _75202 _75203 s i' j' x t a j h1 h2)). Qed.
Lemma lem5950108 {_121855 _121856 : Type'} (_75202 : _121856) (_75203 : _121855) (s : _121856 -> Prop) (i' : _121856) (j' : _121855) (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term136 _121855 _121856 x t a j) : term548 _121855 _121856 t a j _75202 _75203.
Proof. exact (@lem5950107 _121855 _121856 _75202 _75203 s i' j' x t a j h1 h2). Qed.
Lemma lem5950109 {_121855 _121856 : Type'} (s : _121856 -> Prop) (i' : _121856) (j' : _121855) (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term136 _121855 _121856 x t a j) : term551 _121855 _121856 t a j.
Proof. exact (@lem5950108 _121855 _121856 a j s i' j' x t a j h1 h2). Qed.
Lemma lem5950112 {_121855 _121856 : Type'} (s : _121856 -> Prop) (i' : _121856) (j' : _121855) (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term136 _121855 _121856 x t a j) : False.
Proof. exact (@lem5950109 _121855 _121856 s i' j' x t a j h1 h2 (@lem5950105 _121855 _121856 x t a j h2)). Qed.
Lemma lem5950113 {_121855 _121856 : Type'} (s : _121856 -> Prop) (i' : _121856) (j' : _121855) (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term136 _121855 _121856 x t a j) : term530.
Proof. exact (fun h0 : ~ False => @lem5950112 _121855 _121856 s i' j' x t a j h1 h2). Qed.
Lemma lem5950115 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5950116 : term530 = False.
Proof. exact (@lem5950115 False). Qed.
Lemma lem5950171 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : s i'.
Proof. exact (proj1 (@lem5949176 _121855 _121856 s t x i' j' h1)). Qed.
Lemma lem5950172 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : term531 _121856 s i'.
Proof. exact (fun h0 : term476 _121856 s i' => @lem5950171 _121855 _121856 s t x i' j' h1). Qed.
Lemma lem5950174 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5950175 {_121856 : Type'} (s : _121856 -> Prop) (i' : _121856) : (term531 _121856 s i') = (s i').
Proof. exact (@lem5950174 (s i')). Qed.
Lemma lem5950176 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : s i'.
Proof. exact (EQ_MP (@lem5950175 _121856 s i') (@lem5950172 _121855 _121856 s t x i' j' h1)). Qed.
Lemma lem5950178 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : t i' j'.
Proof. exact (proj2 (@lem5949176 _121855 _121856 s t x i' j' h1)). Qed.
Lemma lem5950179 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : term522 _121855 _121856 t i' j'.
Proof. exact (fun h0 : term211 _121855 _121856 t i' j' => @lem5950178 _121855 _121856 s t x i' j' h1). Qed.
Lemma lem5950181 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5950182 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (i' : _121856) (j' : _121855) : (term522 _121855 _121856 t i' j') = (t i' j').
Proof. exact (@lem5950181 (t i' j')). Qed.
Lemma lem5950183 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : t i' j'.
Proof. exact (EQ_MP (@lem5950182 _121855 _121856 t i' j') (@lem5950179 _121855 _121856 s t x i' j' h1)). Qed.
Lemma lem5950185 {_121855 _121856 : Type'} (x : prod _121856 _121855) : x = x.
Proof. exact (@lem21386 (prod _121856 _121855) x). Qed.
Lemma lem5950186 {_121855 _121856 : Type'} (x : prod _121856 _121855) : x = x.
Proof. exact (@lem5950185 _121855 _121856 x). Qed.
Lemma lem5950187 {_121855 _121856 : Type'} (i' : _121856) (j' : _121855) : (@pair _121856 _121855 i' j') = (@pair _121856 _121855 i' j').
Proof. exact (@lem5950186 _121855 _121856 (@pair _121856 _121855 i' j')). Qed.
Lemma lem5950188 {_121855 _121856 : Type'} (i' : _121856) (j' : _121855) : term519 _121855 _121856 i' j'.
Proof. exact (fun h0 : term520 _121855 _121856 i' j' => @lem5950187 _121855 _121856 i' j'). Qed.
Lemma lem5950190 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5950191 {_121855 _121856 : Type'} (i' : _121856) (j' : _121855) : (term519 _121855 _121856 i' j') = ((@pair _121856 _121855 i' j') = (@pair _121856 _121855 i' j')).
Proof. exact (@lem5950190 ((@pair _121856 _121855 i' j') = (@pair _121856 _121855 i' j'))). Qed.
Lemma lem5950192 {_121855 _121856 : Type'} (i' : _121856) (j' : _121855) : (@pair _121856 _121855 i' j') = (@pair _121856 _121855 i' j').
Proof. exact (EQ_MP (@lem5950191 _121855 _121856 i' j') (@lem5950188 _121855 _121856 i' j')). Qed.
Lemma lem5950194 (a : Prop) (b : Prop) : (term523 a b) = (term524 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5950195 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (i' : _121856) (j' : _121855) (_75204 : _121856) (_75205 : _121855) : (term532 _121855 _121856 t i' j' _75204 _75205) = (term533 _121855 _121856 t i' j' _75204 _75205).
Proof. exact (@lem5950194 (t _75204 _75205) ((@pair _121856 _121855 i' j') = (@pair _121856 _121855 _75204 _75205))). Qed.
Lemma lem5950196 {_121856 : Type'} (s : _121856 -> Prop) (_75204 : _121856) : (term534 _121856 s _75204) = (term534 _121856 s _75204).
Proof. exact (eq_refl (term534 _121856 s _75204)). Qed.
Lemma lem5950197 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i' : _121856) (j' : _121855) (_75204 : _121856) (_75205 : _121855) : (term510 _121855 _121856 s t i' j' _75204 _75205) = (term535 _121855 _121856 s t i' j' _75204 _75205).
Proof. exact (MK_COMB (@lem5950196 _121856 s _75204) (@lem5950195 _121855 _121856 t i' j' _75204 _75205)). Qed.
Lemma lem5950199 (a : Prop) (b : Prop) : (term523 a b) = (term524 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5950200 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i' : _121856) (j' : _121855) (_75204 : _121856) (_75205 : _121855) : (term535 _121855 _121856 s t i' j' _75204 _75205) = (term536 _121855 _121856 s t i' j' _75204 _75205).
Proof. exact (@lem5950199 (s _75204) (term537 _121855 _121856 t i' j' _75204 _75205)). Qed.
Lemma lem5950201 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i' : _121856) (j' : _121855) (_75204 : _121856) (_75205 : _121855) : (term510 _121855 _121856 s t i' j' _75204 _75205) = (term536 _121855 _121856 s t i' j' _75204 _75205).
Proof. exact (TRANS (@lem5950197 _121855 _121856 s t i' j' _75204 _75205) (@lem5950200 _121855 _121856 s t i' j' _75204 _75205)). Qed.
Lemma lem5950203 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5950204 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i' : _121856) (j' : _121855) (_75204 : _121856) (_75205 : _121855) : (term536 _121855 _121856 s t i' j' _75204 _75205) = (term538 _121855 _121856 s t i' j' _75204 _75205).
Proof. exact (@lem5950203 (term539 _121855 _121856 s t i' j' _75204 _75205)). Qed.
Lemma lem5950205 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (i' : _121856) (j' : _121855) (_75204 : _121856) (_75205 : _121855) : (term510 _121855 _121856 s t i' j' _75204 _75205) = (term538 _121855 _121856 s t i' j' _75204 _75205).
Proof. exact (TRANS (@lem5950201 _121855 _121856 s t i' j' _75204 _75205) (@lem5950204 _121855 _121856 s t i' j' _75204 _75205)). Qed.
Lemma lem5950207 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : term540 _121855 _121856 t i' j'.
Proof. exact (conj (@lem5950183 _121855 _121856 s t x i' j' h1) (@lem5950192 _121855 _121856 i' j')). Qed.
Lemma lem5950208 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term175 _121855 _121856 s t x i' j') : term541 _121855 _121856 s t i' j'.
Proof. exact (conj (@lem5950176 _121855 _121856 s t x i' j' h1) (@lem5950207 _121855 _121856 s t x i' j' h1)). Qed.
Lemma lem5950210 {_121855 _121856 : Type'} (_75204 : _121856) (_75205 : _121855) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term175 _121855 _121856 s t x i' j') : term538 _121855 _121856 s t i' j' _75204 _75205.
Proof. exact (EQ_MP (@lem5950205 _121855 _121856 s t i' j' _75204 _75205) (@lem5949820 _121855 _121856 _75204 _75205 a j s t x i' j' h1 h2)). Qed.
Lemma lem5950211 {_121855 _121856 : Type'} (_75204 : _121856) (_75205 : _121855) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term175 _121855 _121856 s t x i' j') : term538 _121855 _121856 s t i' j' _75204 _75205.
Proof. exact (@lem5950210 _121855 _121856 _75204 _75205 a j s t x i' j' h1 h2). Qed.
Lemma lem5950212 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term175 _121855 _121856 s t x i' j') : term542 _121855 _121856 s t i' j'.
Proof. exact (@lem5950211 _121855 _121856 i' j' a j s t x i' j' h1 h2). Qed.
Lemma lem5950215 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term175 _121855 _121856 s t x i' j') : False.
Proof. exact (@lem5950212 _121855 _121856 a j s t x i' j' h1 h2 (@lem5950208 _121855 _121856 s t x i' j' h2)). Qed.
Lemma lem5950216 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term175 _121855 _121856 s t x i' j') : term530.
Proof. exact (fun h0 : ~ False => @lem5950215 _121855 _121856 a j s t x i' j' h1 h2). Qed.
Lemma lem5950218 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5950219 : term530 = False.
Proof. exact (@lem5950218 False). Qed.
Lemma lem5950221 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term175 _121855 _121856 s t x i' j') : False.
Proof. exact (EQ_MP (@lem5950219) (@lem5950216 _121855 _121856 a j s t x i' j' h1 h2)). Qed.
Lemma lem5950222 {_121855 _121856 : Type'} (s : _121856 -> Prop) (i' : _121856) (j' : _121855) (x : prod _121856 _121855) (t : type1470 _121855 _121856) (a : _121856) (j : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') (h2 : term136 _121855 _121856 x t a j) : False.
Proof. exact (EQ_MP (@lem5950116) (@lem5950113 _121855 _121856 s i' j' x t a j h1 h2)). Qed.
Lemma lem5950223 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : s i) (h2 : term311 _121855 _121856 i j a s t x) : (s i) = False.
Proof. exact (prop_ext (fun h3 : s i => @lem5950012 _121855 _121856 i j a s t x h1 h2) (fun h3 : False => @lem5949698 _121856 s i h1)). Qed.
Lemma lem5950225 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : s i) (h2 : term311 _121855 _121856 i j a s t x) : False.
Proof. exact (EQ_MP (@lem5950223 _121855 _121856 i j a s t x h1 h2) (@lem5949698 _121856 s i h1)). Qed.
Lemma lem5950227 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : False.
Proof. exact (EQ_MP (@lem5949908) (@lem5949905 _121855 _121856 j s t x i a h1 h2)). Qed.
Lemma lem5950228 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : s i) (h2 : term311 _121855 _121856 i j a s t x) : (s i) = False.
Proof. exact (prop_ext (fun h3 : s i => @lem5950225 _121855 _121856 i j a s t x h1 h2) (fun h3 : False => @lem5949450 _121856 s i h1)). Qed.
Lemma lem5950229 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : s i) (h2 : term311 _121855 _121856 i j a s t x) : False.
Proof. exact (EQ_MP (@lem5950228 _121855 _121856 i j a s t x h1 h2) (@lem5949450 _121856 s i h1)). Qed.
Lemma lem5950230 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : (i = a) = False.
Proof. exact (prop_ext (fun h3 : i = a => @lem5950227 _121855 _121856 j s t x i a h1 h2) (fun h3 : False => @lem5949426 _121856 i a h2)). Qed.
Lemma lem5950231 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : False.
Proof. exact (EQ_MP (@lem5950230 _121855 _121856 j s t x i a h1 h2) (@lem5949426 _121856 i a h2)). Qed.
Lemma lem5950232 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : s i) (h2 : term311 _121855 _121856 i j a s t x) : (s i) = False.
Proof. exact (prop_ext (fun h3 : s i => @lem5950229 _121855 _121856 i j a s t x h1 h2) (fun h3 : False => @lem5949272 _121856 s i h1)). Qed.
Lemma lem5950233 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : s i) (h2 : term311 _121855 _121856 i j a s t x) : False.
Proof. exact (EQ_MP (@lem5950232 _121855 _121856 i j a s t x h1 h2) (@lem5949272 _121856 s i h1)). Qed.
Lemma lem5950234 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : (i = a) = False.
Proof. exact (prop_ext (fun h3 : i = a => @lem5950231 _121855 _121856 j s t x i a h1 h2) (fun h3 : False => @lem5949225 _121856 i a h2)). Qed.
Lemma lem5950235 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : False.
Proof. exact (EQ_MP (@lem5950234 _121855 _121856 j s t x i a h1 h2) (@lem5949225 _121856 i a h2)). Qed.
Lemma lem5950236 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : s i) (h2 : term311 _121855 _121856 i j a s t x) : (s i) = False.
Proof. exact (prop_ext (fun h3 : s i => @lem5950233 _121855 _121856 i j a s t x h1 h2) (fun h3 : False => @lem5949272 _121856 s i h1)). Qed.
Lemma lem5950237 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : s i) (h2 : term311 _121855 _121856 i j a s t x) : False.
Proof. exact (EQ_MP (@lem5950236 _121855 _121856 i j a s t x h1 h2) (@lem5949272 _121856 s i h1)). Qed.
Lemma lem5950238 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : (i = a) = False.
Proof. exact (prop_ext (fun h3 : i = a => @lem5950235 _121855 _121856 j s t x i a h1 h2) (fun h3 : False => @lem5949225 _121856 i a h2)). Qed.
Lemma lem5950239 {_121855 _121856 : Type'} (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i : _121856) (a : _121856) (h1 : term311 _121855 _121856 i j a s t x) (h2 : i = a) : False.
Proof. exact (EQ_MP (@lem5950238 _121855 _121856 j s t x i a h1 h2) (@lem5949225 _121856 i a h2)). Qed.
Lemma lem5950240 {_121855 _121856 : Type'} (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term397 _121855 _121856 a j s t x i' j') : False.
Proof. exact (or_elim (@lem5949169 _121855 _121856 a j s t x i' j' h1) (fun h0 : term136 _121855 _121856 x t a j => @lem5950222 _121855 _121856 s i' j' x t a j h1 h0) (fun h0 : term175 _121855 _121856 s t x i' j' => @lem5950221 _121855 _121856 a j s t x i' j' h1 h0)). Qed.
Lemma lem5950241 {_121855 _121856 : Type'} (i : _121856) (j : _121855) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term311 _121855 _121856 i j a s t x) : False.
Proof. exact (or_elim (@lem5949166 _121855 _121856 i j a s t x h1) (fun h0 : i = a => @lem5950239 _121855 _121856 j s t x i a h1 h0) (fun h0 : s i => @lem5950237 _121855 _121856 i j a s t x h0 h1)). Qed.
Lemma lem5950242 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term464 _121855 _121856 i a j s t x i' j') : False.
Proof. exact (or_elim (@lem5949156 _121855 _121856 i a j s t x i' j' h1) (fun h0 : term311 _121855 _121856 i j a s t x => @lem5950241 _121855 _121856 i j a s t x h0) (fun h0 : term397 _121855 _121856 a j s t x i' j' => @lem5950240 _121855 _121856 a j s t x i' j' h0)). Qed.
Lemma lem5950243 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term464 _121855 _121856 i a j s t x i' j') : (term464 _121855 _121856 i a j s t x i' j') = False.
Proof. exact (prop_ext (fun h2 : term464 _121855 _121856 i a j s t x i' j' => @lem5950242 _121855 _121856 i a j s t x i' j' h1) (fun h2 : False => @lem5949156 _121855 _121856 i a j s t x i' j' h1)). Qed.
Lemma lem5950244 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (j' : _121855) (h1 : term464 _121855 _121856 i a j s t x i' j') : False.
Proof. exact (EQ_MP (@lem5950243 _121855 _121856 i a j s t x i' j' h1) (@lem5949156 _121855 _121856 i a j s t x i' j' h1)). Qed.
Lemma lem5950245 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (i' : _121856) (h1 : term467 _121855 _121856 i a j s t x i') : False.
Proof. exact (ex_elim (@lem5948964 _121855 _121856 i a j s t x i' h1) (fun j' : _121855 => fun h0 : term466 _121855 _121856 i a j s t x i' j' => @lem5950244 _121855 _121856 i a j s t x i' j' h0)). Qed.
Lemma lem5950246 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (j : _121855) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term469 _121855 _121856 i a j s t x) : False.
Proof. exact (ex_elim (@lem5948963 _121855 _121856 i a j s t x h1) (fun i' : _121856 => fun h0 : term468 _121855 _121856 i a j s t x i' => @lem5950245 _121855 _121856 i a j s t x i' h0)). Qed.
Lemma lem5950247 {_121855 _121856 : Type'} (i : _121856) (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term471 _121855 _121856 i a s t x) : False.
Proof. exact (ex_elim (@lem5948962 _121855 _121856 i a s t x h1) (fun j : _121855 => fun h0 : term470 _121855 _121856 i a s t x j => @lem5950246 _121855 _121856 i a j s t x h0)). Qed.
Lemma lem5950248 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term208 _121855 _121856 a s t x) : False.
Proof. exact (ex_elim (@lem5948961 _121855 _121856 a s t x h1) (fun i : _121856 => fun h0 : term472 _121855 _121856 a s t x i => @lem5950247 _121855 _121856 i a s t x h0)). Qed.
Lemma lem5950249 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term208 _121855 _121856 a s t x) : (term208 _121855 _121856 a s t x) = False.
Proof. exact (prop_ext (fun h2 : term208 _121855 _121856 a s t x => @lem5950248 _121855 _121856 a s t x h1) (fun h2 : False => @lem5948183 _121855 _121856 a s t x h1)). Qed.
Lemma lem5950250 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) (h1 : term208 _121855 _121856 a s t x) : False.
Proof. exact (EQ_MP (@lem5950249 _121855 _121856 a s t x h1) (@lem5948183 _121855 _121856 a s t x h1)). Qed.
Lemma lem5950251 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : term207 _121855 _121856 a s t x.
Proof. exact (fun h0 : term208 _121855 _121856 a s t x => @lem5950250 _121855 _121856 a s t x h0). Qed.
Lemma lem5950252 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (x : prod _121856 _121855) : (term112 _121855 _121856 a s t x) = (term183 _121855 _121856 a s t x).
Proof. exact (EQ_MP (@lem5948182 _121855 _121856 a s t x) (@lem5950251 _121855 _121856 a s t x)). Qed.
Lemma lem5950257 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : term186 _121855 _121856 a s t.
Proof. exact (fun x : prod _121856 _121855 => @lem5950252 _121855 _121856 a s t x). Qed.
Lemma lem5950262 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) : term198 _121855 _121856 s t.
Proof. exact (fun a : _121856 => @lem5950257 _121855 _121856 a s t). Qed.
Lemma lem5950267 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) : term202 _121855 _121856 t.
Proof. exact (fun s : _121856 -> Prop => @lem5950262 _121855 _121856 s t). Qed.
Lemma lem5950272 {_121855 _121856 : Type'} : term206 _121855 _121856.
Proof. exact (fun t : type1470 _121855 _121856 => @lem5950267 _121855 _121856 t). Qed.
Lemma lem5950273 {_121855 _121856 : Type'} : term205 _121855 _121856.
Proof. exact (EQ_MP (@lem5948178 _121855 _121856) (@lem5950272 _121855 _121856)). Qed.
Lemma lem5950274 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) : term552 _121855 _121856 t.
Proof. exact (@lem5950273 _121855 _121856 t). Qed.
Lemma lem5950275 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) : (term552 _121855 _121856 t) = (term201 _121855 _121856 t).
Proof. exact (eq_refl (term552 _121855 _121856 t)). Qed.
Lemma lem5950276 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) : term201 _121855 _121856 t.
Proof. exact (EQ_MP (@lem5950275 _121855 _121856 t) (@lem5950274 _121855 _121856 t)). Qed.
Lemma lem5950277 {_121855 _121856 : Type'} (t : type1470 _121855 _121856) (s : _121856 -> Prop) : term553 _121855 _121856 t s.
Proof. exact (@lem5950276 _121855 _121856 t s). Qed.
Lemma lem5950278 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term553 _121855 _121856 t s) = (term197 _121855 _121856 s t).
Proof. exact (eq_refl (term553 _121855 _121856 t s)). Qed.
Lemma lem5950279 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) : term197 _121855 _121856 s t.
Proof. exact (EQ_MP (@lem5950278 _121855 _121856 s t) (@lem5950277 _121855 _121856 t s)). Qed.
Lemma lem5950280 {_121855 _121856 : Type'} (s : _121856 -> Prop) (t : type1470 _121855 _121856) (a : _121856) : term554 _121855 _121856 s t a.
Proof. exact (@lem5950279 _121855 _121856 s t a). Qed.
Lemma lem5950281 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term554 _121855 _121856 s t a) = (term188 _121855 _121856 a s t).
Proof. exact (eq_refl (term554 _121855 _121856 s t a)). Qed.
Lemma lem5950282 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : term188 _121855 _121856 a s t.
Proof. exact (EQ_MP (@lem5950281 _121855 _121856 a s t) (@lem5950280 _121855 _121856 s t a)). Qed.
Lemma lem5950284 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : term188 _121855 _121856 a s t.
Proof. exact (@lem5947832 _121855 _121856 a s t (@lem5950282 _121855 _121856 a s t)). Qed.
Lemma lem5950285 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (h1 : term189 _121855 _121856 a s t) : False.
Proof. exact (@lem5950284 _121855 _121856 a s t (@lem5947816 _121855 _121856 a s t h1)). Qed.
Lemma lem5950286 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (h1 : term189 _121855 _121856 a s t) : (term189 _121855 _121856 a s t) = False.
Proof. exact (prop_ext (fun h2 : term189 _121855 _121856 a s t => @lem5950285 _121855 _121856 a s t h1) (fun h2 : False => @lem5947816 _121855 _121856 a s t h1)). Qed.
Lemma lem5950287 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) (h1 : term189 _121855 _121856 a s t) : False.
Proof. exact (EQ_MP (@lem5950286 _121855 _121856 a s t h1) (@lem5947816 _121855 _121856 a s t h1)). Qed.
Lemma lem5950288 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : term188 _121855 _121856 a s t.
Proof. exact (fun h0 : term189 _121855 _121856 a s t => @lem5950287 _121855 _121856 a s t h0). Qed.
Lemma lem5950289 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : term186 _121855 _121856 a s t.
Proof. exact (EQ_MP (@lem5947815 _121855 _121856 a s t) (@lem5950288 _121855 _121856 a s t)). Qed.
Lemma lem5950290 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : term57 _121855 _121856 a s t.
Proof. exact (EQ_MP (@lem5947811 _121855 _121856 a s t) (@lem5950289 _121855 _121856 a s t)). Qed.
Lemma lem5950305 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term43 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5950306 {_121879 _121880 : Type'} (s : type1223 _121879 _121880) (t : type1223 _121879 _121880) : (s = t) = (term54 _121879 _121880 s t).
Proof. exact (@lem5950305 (prod _121880 _121879) s t). Qed.
Lemma lem5950307 {_121879 _121880 : Type'} : ((term555 _121879 _121880) = (@EMPTY (prod _121880 _121879))) = (term556 _121879 _121880).
Proof. exact (@lem5950306 _121879 _121880 (term555 _121879 _121880) (@EMPTY (prod _121880 _121879))). Qed.
Lemma lem5950324 {_121879 _121880 : Type'} : (term556 _121879 _121880) = ((term555 _121879 _121880) = (@EMPTY (prod _121880 _121879))).
Proof. exact (SYM (@lem5950307 _121879 _121880)). Qed.
Lemma lem5950332 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term21 _83064 x P) = (term22 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem5950333 {_121879 _121880 : Type'} (P : type916 _121879 _121880) (x : prod _121880 _121879) : (term58 _121879 _121880 x P) = (term59 _121879 _121880 P x).
Proof. exact (@lem5950332 (prod _121880 _121879) P x). Qed.
Lemma lem5950334 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term557 _121879 _121880 x) = (term558 _121879 _121880 x).
Proof. exact (@lem5950333 _121879 _121880 (term559 _121879 _121880) x). Qed.
Lemma lem5950335 {_121879 _121880 : Type'} (GEN_PVAR_240 : prod _121880 _121879) : (term560 _121879 _121880 GEN_PVAR_240) = (term561 _121879 _121880 GEN_PVAR_240).
Proof. exact (eq_refl (term560 _121879 _121880 GEN_PVAR_240)). Qed.
Lemma lem5950336 {_121879 _121880 : Type'} : (term562 _121879 _121880) = (term563 _121879 _121880).
Proof. exact (fun_ext (fun GEN_PVAR_240 : prod _121880 _121879 => @lem5950335 _121879 _121880 GEN_PVAR_240)). Qed.
Lemma lem5950337 {_121879 _121880 : Type'} : (@GSPEC (prod _121880 _121879)) = (@GSPEC (prod _121880 _121879)).
Proof. exact (eq_refl (@GSPEC (prod _121880 _121879))). Qed.
Lemma lem5950338 {_121879 _121880 : Type'} : (term564 _121879 _121880) = (term555 _121879 _121880).
Proof. exact (MK_COMB (@lem5950337 _121879 _121880) (@lem5950336 _121879 _121880)). Qed.
Lemma lem5950339 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (@IN (prod _121880 _121879) x) = (@IN (prod _121880 _121879) x).
Proof. exact (eq_refl (@IN (prod _121880 _121879) x)). Qed.
Lemma lem5950340 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term557 _121879 _121880 x) = (term565 _121879 _121880 x).
Proof. exact (MK_COMB (@lem5950339 _121879 _121880 x) (@lem5950338 _121879 _121880)). Qed.
Lemma lem5950341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5950342 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term566 _121879 _121880 x) = (term567 _121879 _121880 x).
Proof. exact (MK_COMB (@lem5950341) (@lem5950340 _121879 _121880 x)). Qed.
Lemma lem5950343 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term558 _121879 _121880 x) = (term568 _121879 _121880 x).
Proof. exact (eq_refl (term558 _121879 _121880 x)). Qed.
Lemma lem5950344 {_121879 _121880 : Type'} (x : prod _121880 _121879) : ((term557 _121879 _121880 x) = (term558 _121879 _121880 x)) = ((term565 _121879 _121880 x) = (term568 _121879 _121880 x)).
Proof. exact (MK_COMB (@lem5950342 _121879 _121880 x) (@lem5950343 _121879 _121880 x)). Qed.
Lemma lem5950345 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term565 _121879 _121880 x) = (term568 _121879 _121880 x).
Proof. exact (EQ_MP (@lem5950344 _121879 _121880 x) (@lem5950334 _121879 _121880 x)). Qed.
Lemma lem5950355 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5950356 {_121879 _121880 : Type'} (f : type1534 _121879 _121880) (y : Prop) : (term73 _121879 _121880 f y) = (f y).
Proof. exact (@lem5950355 Prop (type1223 _121879 _121880) f y). Qed.
Lemma lem5950357 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term569 _121879 _121880 x) = (term570 _121879 _121880 x).
Proof. exact (@lem5950356 _121879 _121880 (term76 _121879 _121880 x) False). Qed.
Lemma lem5950358 {_121879 _121880 : Type'} (p : Prop) (x : prod _121880 _121879) : (term78 _121879 _121880 x p) = (term79 _121879 _121880 p x).
Proof. exact (eq_refl (term78 _121879 _121880 x p)). Qed.
Lemma lem5950359 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term80 _121879 _121880 x) = (term76 _121879 _121880 x).
Proof. exact (fun_ext (fun p : Prop => @lem5950358 _121879 _121880 p x)). Qed.
Lemma lem5950360 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem5950361 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term569 _121879 _121880 x) = (term570 _121879 _121880 x).
Proof. exact (MK_COMB (@lem5950359 _121879 _121880 x) (@lem5950360)). Qed.
Lemma lem5950362 {_121879 _121880 : Type'} : (@eq ((prod _121880 _121879) -> Prop)) = (@eq ((prod _121880 _121879) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _121880 _121879) -> Prop))). Qed.
Lemma lem5950363 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term571 _121879 _121880 x) = (term572 _121879 _121880 x).
Proof. exact (MK_COMB (@lem5950362 _121879 _121880) (@lem5950361 _121879 _121880 x)). Qed.
Lemma lem5950364 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term570 _121879 _121880 x) = (term573 _121879 _121880 x).
Proof. exact (eq_refl (term570 _121879 _121880 x)). Qed.
Lemma lem5950365 {_121879 _121880 : Type'} (x : prod _121880 _121879) : ((term569 _121879 _121880 x) = (term570 _121879 _121880 x)) = ((term570 _121879 _121880 x) = (term573 _121879 _121880 x)).
Proof. exact (MK_COMB (@lem5950363 _121879 _121880 x) (@lem5950364 _121879 _121880 x)). Qed.
Lemma lem5950366 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term570 _121879 _121880 x) = (term573 _121879 _121880 x).
Proof. exact (EQ_MP (@lem5950365 _121879 _121880 x) (@lem5950357 _121879 _121880 x)). Qed.
Lemma lem5950368 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5950369 {_121879 _121880 : Type'} (x : prod _121880 _121879) (t : prod _121880 _121879) : (term574 _121879 _121880 x t) = False.
Proof. exact (@lem5950368 (x = t)). Qed.
Lemma lem5950370 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term573 _121879 _121880 x) = (term575 _121879 _121880).
Proof. exact (fun_ext (fun t : prod _121880 _121879 => @lem5950369 _121879 _121880 x t)). Qed.
Lemma lem5950371 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term570 _121879 _121880 x) = (term575 _121879 _121880).
Proof. exact (TRANS (@lem5950366 _121879 _121880 x) (@lem5950370 _121879 _121880 x)). Qed.
Lemma lem5950372 {_121879 _121880 : Type'} (a : _121880) (b : _121879) : (@pair _121880 _121879 a b) = (@pair _121880 _121879 a b).
Proof. exact (eq_refl (@pair _121880 _121879 a b)). Qed.
Lemma lem5950373 {_121879 _121880 : Type'} (x : prod _121880 _121879) (a : _121880) (b : _121879) : (term576 _121879 _121880 x a b) = (term577 _121879 _121880 a b).
Proof. exact (MK_COMB (@lem5950371 _121879 _121880 x) (@lem5950372 _121879 _121880 a b)). Qed.
Lemma lem5950375 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5950376 {_121879 _121880 : Type'} (f : type1223 _121879 _121880) (y : prod _121880 _121879) : (term99 _121879 _121880 f y) = (f y).
Proof. exact (@lem5950375 (prod _121880 _121879) Prop f y). Qed.
Lemma lem5950377 {_121879 _121880 : Type'} (a : _121880) (b : _121879) : (term578 _121879 _121880 a b) = (term577 _121879 _121880 a b).
Proof. exact (@lem5950376 _121879 _121880 (term575 _121879 _121880) (@pair _121880 _121879 a b)). Qed.
Lemma lem5950378 {_121879 _121880 : Type'} (t : prod _121880 _121879) : (term579 _121879 _121880 t) = False.
Proof. exact (eq_refl (term579 _121879 _121880 t)). Qed.
Lemma lem5950379 {_121879 _121880 : Type'} : (term580 _121879 _121880) = (term575 _121879 _121880).
Proof. exact (fun_ext (fun t : prod _121880 _121879 => @lem5950378 _121879 _121880 t)). Qed.
Lemma lem5950380 {_121879 _121880 : Type'} (a : _121880) (b : _121879) : (@pair _121880 _121879 a b) = (@pair _121880 _121879 a b).
Proof. exact (eq_refl (@pair _121880 _121879 a b)). Qed.
Lemma lem5950381 {_121879 _121880 : Type'} (a : _121880) (b : _121879) : (term578 _121879 _121880 a b) = (term577 _121879 _121880 a b).
Proof. exact (MK_COMB (@lem5950379 _121879 _121880) (@lem5950380 _121879 _121880 a b)). Qed.
Lemma lem5950382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5950383 {_121879 _121880 : Type'} (a : _121880) (b : _121879) : (term581 _121879 _121880 a b) = (term582 _121879 _121880 a b).
Proof. exact (MK_COMB (@lem5950382) (@lem5950381 _121879 _121880 a b)). Qed.
Lemma lem5950384 {_121879 _121880 : Type'} (a : _121880) (b : _121879) : (term577 _121879 _121880 a b) = False.
Proof. exact (eq_refl (term577 _121879 _121880 a b)). Qed.
Lemma lem5950385 {_121879 _121880 : Type'} (a : _121880) (b : _121879) : ((term578 _121879 _121880 a b) = (term577 _121879 _121880 a b)) = ((term577 _121879 _121880 a b) = False).
Proof. exact (MK_COMB (@lem5950383 _121879 _121880 a b) (@lem5950384 _121879 _121880 a b)). Qed.
Lemma lem5950386 {_121879 _121880 : Type'} (a : _121880) (b : _121879) : (term577 _121879 _121880 a b) = False.
Proof. exact (EQ_MP (@lem5950385 _121879 _121880 a b) (@lem5950377 _121879 _121880 a b)). Qed.
Lemma lem5950387 {_121879 _121880 : Type'} (x : prod _121880 _121879) (a : _121880) (b : _121879) : (term576 _121879 _121880 x a b) = False.
Proof. exact (TRANS (@lem5950373 _121879 _121880 x a b) (@lem5950386 _121879 _121880 a b)). Qed.
Lemma lem5950388 {_121879 _121880 : Type'} (x : prod _121880 _121879) (a : _121880) : (term583 _121879 _121880 x a) = (term584 _121879).
Proof. exact (fun_ext (fun b : _121879 => @lem5950387 _121879 _121880 x a b)). Qed.
Lemma lem5950389 {_121879 : Type'} : (@ex _121879) = (@ex _121879).
Proof. exact (eq_refl (@ex _121879)). Qed.
Lemma lem5950390 {_121879 _121880 : Type'} (x : prod _121880 _121879) (a : _121880) : (term585 _121879 _121880 x a) = (term586 _121879).
Proof. exact (MK_COMB (@lem5950389 _121879) (@lem5950388 _121879 _121880 x a)). Qed.
Lemma lem5950392 {A : Type'} (t : Prop) : (term587 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem5950393 {_121879 : Type'} (t : Prop) : (term587 _121879 t) = t.
Proof. exact (@lem5950392 _121879 t). Qed.
Lemma lem5950394 {_121879 : Type'} : (term586 _121879) = False.
Proof. exact (@lem5950393 _121879 False). Qed.
Lemma lem5950395 {_121879 _121880 : Type'} (x : prod _121880 _121879) (a : _121880) : (term585 _121879 _121880 x a) = False.
Proof. exact (TRANS (@lem5950390 _121879 _121880 x a) (@lem5950394 _121879)). Qed.
Lemma lem5950396 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term588 _121879 _121880 x) = (term584 _121880).
Proof. exact (fun_ext (fun a : _121880 => @lem5950395 _121879 _121880 x a)). Qed.
Lemma lem5950397 {_121880 : Type'} : (@ex _121880) = (@ex _121880).
Proof. exact (eq_refl (@ex _121880)). Qed.
Lemma lem5950398 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term568 _121879 _121880 x) = (term586 _121880).
Proof. exact (MK_COMB (@lem5950397 _121880) (@lem5950396 _121879 _121880 x)). Qed.
Lemma lem5950400 {A : Type'} (t : Prop) : (term587 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem5950401 {_121880 : Type'} (t : Prop) : (term587 _121880 t) = t.
Proof. exact (@lem5950400 _121880 t). Qed.
Lemma lem5950402 {_121880 : Type'} : (term586 _121880) = False.
Proof. exact (@lem5950401 _121880 False). Qed.
Lemma lem5950403 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term568 _121879 _121880 x) = False.
Proof. exact (TRANS (@lem5950398 _121879 _121880 x) (@lem5950402 _121880)). Qed.
Lemma lem5950404 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term565 _121879 _121880 x) = False.
Proof. exact (TRANS (@lem5950345 _121879 _121880 x) (@lem5950403 _121879 _121880 x)). Qed.
Lemma lem5950405 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5950406 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (term567 _121879 _121880 x) = (@eq Prop False).
Proof. exact (MK_COMB (@lem5950405) (@lem5950404 _121879 _121880 x)). Qed.
Lemma lem5950408 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5950409 {_121879 _121880 : Type'} (x : prod _121880 _121879) : (@IN (prod _121880 _121879) x (@EMPTY (prod _121880 _121879))) = False.
Proof. exact (@lem5950408 (prod _121880 _121879) x). Qed.
Lemma lem5950410 {_121879 _121880 : Type'} (x : prod _121880 _121879) : ((term565 _121879 _121880 x) = (@IN (prod _121880 _121879) x (@EMPTY (prod _121880 _121879)))) = (False = False).
Proof. exact (MK_COMB (@lem5950406 _121879 _121880 x) (@lem5950409 _121879 _121880 x)). Qed.
Lemma lem5950412 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem5950413 : (False = False) = (~ False).
Proof. exact (@lem5950412 False). Qed.
Lemma lem5950415 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5950416 : (False = False) = True.
Proof. exact (TRANS (@lem5950413) (@lem5950415)). Qed.
Lemma lem5950417 {_121879 _121880 : Type'} (x : prod _121880 _121879) : ((term565 _121879 _121880 x) = (@IN (prod _121880 _121879) x (@EMPTY (prod _121880 _121879)))) = True.
Proof. exact (TRANS (@lem5950410 _121879 _121880 x) (@lem5950416)). Qed.
Lemma lem5950418 {_121879 _121880 : Type'} : (term589 _121879 _121880) = (term590 _121879 _121880).
Proof. exact (fun_ext (fun x : prod _121880 _121879 => @lem5950417 _121879 _121880 x)). Qed.
Lemma lem5950419 {_121879 _121880 : Type'} : (@all (prod _121880 _121879)) = (@all (prod _121880 _121879)).
Proof. exact (eq_refl (@all (prod _121880 _121879))). Qed.
Lemma lem5950420 {_121879 _121880 : Type'} : (term556 _121879 _121880) = (term591 _121879 _121880).
Proof. exact (MK_COMB (@lem5950419 _121879 _121880) (@lem5950418 _121879 _121880)). Qed.
Lemma lem5950422 {A : Type'} (t : Prop) : (term592 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5950423 {_121879 _121880 : Type'} (t : Prop) : (term593 _121879 _121880 t) = t.
Proof. exact (@lem5950422 (prod _121880 _121879) t). Qed.
Lemma lem5950424 {_121879 _121880 : Type'} : (term591 _121879 _121880) = True.
Proof. exact (@lem5950423 _121879 _121880 True). Qed.
Lemma lem5950425 {_121879 _121880 : Type'} : (term556 _121879 _121880) = True.
Proof. exact (TRANS (@lem5950420 _121879 _121880) (@lem5950424 _121879 _121880)). Qed.
Lemma lem5950426 {_121879 _121880 : Type'} : True = (term556 _121879 _121880).
Proof. exact (SYM (@lem5950425 _121879 _121880)). Qed.
Lemma lem5950427 {_121879 _121880 : Type'} : term556 _121879 _121880.
Proof. exact (EQ_MP (@lem5950426 _121879 _121880) (@lem0)). Qed.
Lemma lem5950429 {A : Type'} (h1 : term594 A) : term594 A.
Proof. exact (h1). Qed.
Lemma lem5950430 {A : Type'} (P : type686 A) (h1 : term594 A) : term595 A P.
Proof. exact (@lem5950429 A h1 P). Qed.
Lemma lem5950431 {A : Type'} (P : type686 A) : (term595 A P) = (term596 A P).
Proof. exact (eq_refl (term595 A P)). Qed.
Lemma lem5950432 {A : Type'} (P : type686 A) (h1 : term594 A) : term596 A P.
Proof. exact (EQ_MP (@lem5950431 A P) (@lem5950430 A P h1)). Qed.
Lemma lem5950433 {A : Type'} (P : type686 A) (h1 : term597 A P) : term597 A P.
Proof. exact (h1). Qed.
Lemma lem5950434 {A : Type'} (P : type686 A) (h1 : term594 A) (h2 : term597 A P) : term598 A P.
Proof. exact (@lem5950432 A P h1 (@lem5950433 A P h2)). Qed.
Lemma lem5950435 {A : Type'} (P : type686 A) (h1 : term597 A P) : term599 A P.
Proof. exact (fun h0 : term594 A => @lem5950434 A P h0 h1). Qed.
Lemma lem5950436 {A : Type'} (h1 : term594 A) : term594 A.
Proof. exact (h1). Qed.
Lemma lem5950437 {A : Type'} (P : type686 A) (h1 : term594 A) (h2 : term597 A P) : term598 A P.
Proof. exact (@lem5950435 A P h2 (@lem5950436 A h1)). Qed.
Lemma lem5950438 {A : Type'} (P : type686 A) (h1 : term594 A) : term596 A P.
Proof. exact (fun h0 : term597 A P => @lem5950437 A P h1 h0). Qed.
Lemma lem5950439 {A : Type'} (h1 : term594 A) : term594 A.
Proof. exact (fun P : type686 A => @lem5950438 A P h1). Qed.
Lemma lem5950440 {A : Type'} : term600 A.
Proof. exact (fun h0 : term594 A => @lem5950439 A h0). Qed.
Lemma lem5950441 {A : Type'} : term594 A.
Proof. exact (@lem5950440 A (@lem3558722 A)). Qed.
Lemma lem5950442 {A : Type'} (P : type686 A) : term595 A P.
Proof. exact (@lem5950441 A P). Qed.
Lemma lem5950443 {A : Type'} (P : type686 A) : (term595 A P) = (term596 A P).
Proof. exact (eq_refl (term595 A P)). Qed.
Lemma lem5950445 {A : Type'} (P : Prop) : term601 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem5950446 {A : Type'} (P : Prop) : (term601 A P) = (term602 A P).
Proof. exact (eq_refl (term601 A P)). Qed.
Lemma lem5950447 {A : Type'} (P : Prop) : term602 A P.
Proof. exact (EQ_MP (@lem5950446 A P) (@lem5950445 A P)). Qed.
Lemma lem5950448 {A : Type'} (P : Prop) (Q : A -> Prop) : term603 A P Q.
Proof. exact (@lem5950447 A P Q). Qed.
Lemma lem5950449 {A : Type'} (P : Prop) (Q : A -> Prop) : (term603 A P Q) = ((term604 A P Q) = (term605 A P Q)).
Proof. exact (eq_refl (term603 A P Q)). Qed.
Lemma lem5950451 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem5950461 {A : Type'} (P : Prop) (Q : A -> Prop) : (term604 A P Q) = (term605 A P Q).
Proof. exact (EQ_MP (@lem5950449 A P Q) (@lem5950448 A P Q)). Qed.
Lemma lem5950462 {A B C : Type'} (P : Prop) (Q : type443 A B C) : (term606 A B C P Q) = (term607 A B C P Q).
Proof. exact (@lem5950461 (type1412 A B C) P Q). Qed.
Lemma lem5950463 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term608 A B C op s t) = (term609 A B C op s t).
Proof. exact (@lem5950462 A B C (term610 A B s t) (term611 A B C op s t)). Qed.
Lemma lem5950464 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x : type1412 A B C) : (term612 A B C op s t x) = ((term613 A B C s op t x) = (term614 A B C op s t x)).
Proof. exact (eq_refl (term612 A B C op s t x)). Qed.
Lemma lem5950465 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term615 A B s t) = (term615 A B s t).
Proof. exact (eq_refl (term615 A B s t)). Qed.
Lemma lem5950466 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x : type1412 A B C) : (term616 A B C op s t x) = (term617 A B C op s t x).
Proof. exact (MK_COMB (@lem5950465 A B s t) (@lem5950464 A B C op s t x)). Qed.
Lemma lem5950467 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term618 A B C op s t) = (term619 A B C op s t).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5950466 A B C op s t x)). Qed.
Lemma lem5950468 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5950469 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term608 A B C op s t) = (term620 A B C op s t).
Proof. exact (MK_COMB (@lem5950468 A B C) (@lem5950467 A B C op s t)). Qed.
Lemma lem5950470 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5950471 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term621 A B C op s t) = (term622 A B C op s t).
Proof. exact (MK_COMB (@lem5950470) (@lem5950469 A B C op s t)). Qed.
Lemma lem5950472 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x : type1412 A B C) : (term612 A B C op s t x) = ((term613 A B C s op t x) = (term614 A B C op s t x)).
Proof. exact (eq_refl (term612 A B C op s t x)). Qed.
Lemma lem5950473 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term623 A B C op s t) = (term611 A B C op s t).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5950472 A B C op s t x)). Qed.
Lemma lem5950474 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5950475 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term624 A B C op s t) = (term625 A B C op s t).
Proof. exact (MK_COMB (@lem5950474 A B C) (@lem5950473 A B C op s t)). Qed.
Lemma lem5950476 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term615 A B s t) = (term615 A B s t).
Proof. exact (eq_refl (term615 A B s t)). Qed.
Lemma lem5950477 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term609 A B C op s t) = (term626 A B C op s t).
Proof. exact (MK_COMB (@lem5950476 A B s t) (@lem5950475 A B C op s t)). Qed.
Lemma lem5950478 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : ((term608 A B C op s t) = (term609 A B C op s t)) = ((term620 A B C op s t) = (term626 A B C op s t)).
Proof. exact (MK_COMB (@lem5950471 A B C op s t) (@lem5950477 A B C op s t)). Qed.
Lemma lem5950479 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term620 A B C op s t) = (term626 A B C op s t).
Proof. exact (EQ_MP (@lem5950478 A B C op s t) (@lem5950463 A B C op s t)). Qed.
Lemma lem5950481 (p : Prop) (q : Prop) (r : Prop) : (term627 p q r) = (term628 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem5950482 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term626 A B C op s t) = (term629 A B C op s t).
Proof. exact (@lem5950481 (@FINITE A s) (term630 A B s t) (term625 A B C op s t)). Qed.
Lemma lem5950485 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term620 A B C op s t) = (term629 A B C op s t).
Proof. exact (TRANS (@lem5950479 A B C op s t) (@lem5950482 A B C op s t)). Qed.
Lemma lem5950538 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term631 A B C op s) = (term632 A B C op s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5950485 A B C op s t)). Qed.
Lemma lem5950539 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5950540 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term633 A B C op s) = (term634 A B C op s).
Proof. exact (MK_COMB (@lem5950539 A B) (@lem5950538 A B C op s)). Qed.
Lemma lem5950542 {A : Type'} (P : Prop) (Q : A -> Prop) : (term604 A P Q) = (term605 A P Q).
Proof. exact (EQ_MP (@lem5950449 A P Q) (@lem5950448 A P Q)). Qed.
Lemma lem5950543 {A B : Type'} (P : Prop) (Q : type475 A B) : (term635 A B P Q) = (term636 A B P Q).
Proof. exact (@lem5950542 (type1413 A B) P Q). Qed.
Lemma lem5950544 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term637 A B C op s) = (term638 A B C op s).
Proof. exact (@lem5950543 A B (@FINITE A s) (term639 A B C op s)). Qed.
Lemma lem5950545 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term640 A B C op s t) = (term641 A B C op s t).
Proof. exact (eq_refl (term640 A B C op s t)). Qed.
Lemma lem5950546 {A : Type'} (s : A -> Prop) : (term642 A s) = (term642 A s).
Proof. exact (eq_refl (term642 A s)). Qed.
Lemma lem5950547 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term643 A B C op s t) = (term629 A B C op s t).
Proof. exact (MK_COMB (@lem5950546 A s) (@lem5950545 A B C op s t)). Qed.
Lemma lem5950548 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term644 A B C op s) = (term632 A B C op s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5950547 A B C op s t)). Qed.
Lemma lem5950549 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5950550 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term637 A B C op s) = (term634 A B C op s).
Proof. exact (MK_COMB (@lem5950549 A B) (@lem5950548 A B C op s)). Qed.
Lemma lem5950551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5950552 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term645 A B C op s) = (term646 A B C op s).
Proof. exact (MK_COMB (@lem5950551) (@lem5950550 A B C op s)). Qed.
Lemma lem5950553 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term640 A B C op s t) = (term641 A B C op s t).
Proof. exact (eq_refl (term640 A B C op s t)). Qed.
Lemma lem5950554 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term647 A B C op s) = (term639 A B C op s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5950553 A B C op s t)). Qed.
Lemma lem5950555 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5950556 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term648 A B C op s) = (term649 A B C op s).
Proof. exact (MK_COMB (@lem5950555 A B) (@lem5950554 A B C op s)). Qed.
Lemma lem5950557 {A : Type'} (s : A -> Prop) : (term642 A s) = (term642 A s).
Proof. exact (eq_refl (term642 A s)). Qed.
Lemma lem5950558 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term638 A B C op s) = (term650 A B C op s).
Proof. exact (MK_COMB (@lem5950557 A s) (@lem5950556 A B C op s)). Qed.
Lemma lem5950559 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : ((term637 A B C op s) = (term638 A B C op s)) = ((term634 A B C op s) = (term650 A B C op s)).
Proof. exact (MK_COMB (@lem5950552 A B C op s) (@lem5950558 A B C op s)). Qed.
Lemma lem5950560 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term634 A B C op s) = (term650 A B C op s).
Proof. exact (EQ_MP (@lem5950559 A B C op s) (@lem5950544 A B C op s)). Qed.
Lemma lem5950639 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term633 A B C op s) = (term650 A B C op s).
Proof. exact (TRANS (@lem5950540 A B C op s) (@lem5950560 A B C op s)). Qed.
Lemma lem5950640 {A B C : Type'} (op : type1400 C) : (term651 A B C op) = (term652 A B C op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5950639 A B C op s)). Qed.
Lemma lem5950641 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5950642 {A B C : Type'} (op : type1400 C) : (term653 A B C op) = (term654 A B C op).
Proof. exact (MK_COMB (@lem5950641 A) (@lem5950640 A B C op)). Qed.
Lemma lem5950667 {A B C : Type'} (op : type1400 C) : (term654 A B C op) = (term653 A B C op).
Proof. exact (SYM (@lem5950642 A B C op)). Qed.
Lemma lem5950669 {A : Type'} (P : type686 A) : term596 A P.
Proof. exact (EQ_MP (@lem5950443 A P) (@lem5950442 A P)). Qed.
Lemma lem5950670 {A : Type'} (P : type686 A) : term596 A P.
Proof. exact (@lem5950669 A P). Qed.
Lemma lem5950671 {A B C : Type'} (op : type1400 C) : term655 A B C op.
Proof. exact (@lem5950670 A (term656 A B C op)). Qed.
Lemma lem5950672 {A B C : Type'} (op : type1400 C) : (term657 A B C op) = (term658 A B C op).
Proof. exact (eq_refl (term657 A B C op)). Qed.
Lemma lem5950673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5950674 {A B C : Type'} (op : type1400 C) : (term659 A B C op) = (term660 A B C op).
Proof. exact (MK_COMB (@lem5950673) (@lem5950672 A B C op)). Qed.
Lemma lem5950675 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term661 A B C op s) = (term649 A B C op s).
Proof. exact (eq_refl (term661 A B C op s)). Qed.
Lemma lem5950676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5950677 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term662 A B C op s) = (term663 A B C op s).
Proof. exact (MK_COMB (@lem5950676) (@lem5950675 A B C op s)). Qed.
Lemma lem5950678 {A : Type'} (x : A) (s : A -> Prop) : (term664 A x s) = (term664 A x s).
Proof. exact (eq_refl (term664 A x s)). Qed.
Lemma lem5950679 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : (term665 A B C op x s) = (term666 A B C op x s).
Proof. exact (MK_COMB (@lem5950677 A B C op s) (@lem5950678 A x s)). Qed.
Lemma lem5950680 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5950681 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : (term667 A B C op x s) = (term668 A B C op x s).
Proof. exact (MK_COMB (@lem5950680) (@lem5950679 A B C op x s)). Qed.
Lemma lem5950682 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : (term669 A B C op x s) = (term670 A B C op x s).
Proof. exact (eq_refl (term669 A B C op x s)). Qed.
Lemma lem5950683 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : (term671 A B C op x s) = (term672 A B C op x s).
Proof. exact (MK_COMB (@lem5950681 A B C op x s) (@lem5950682 A B C op x s)). Qed.
Lemma lem5950684 {A B C : Type'} (op : type1400 C) (x : A) : (term673 A B C op x) = (term674 A B C op x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5950683 A B C op x s)). Qed.
Lemma lem5950685 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5950686 {A B C : Type'} (op : type1400 C) (x : A) : (term675 A B C op x) = (term676 A B C op x).
Proof. exact (MK_COMB (@lem5950685 A) (@lem5950684 A B C op x)). Qed.
Lemma lem5950687 {A B C : Type'} (op : type1400 C) : (term677 A B C op) = (term678 A B C op).
Proof. exact (fun_ext (fun x : A => @lem5950686 A B C op x)). Qed.
Lemma lem5950688 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5950689 {A B C : Type'} (op : type1400 C) : (term679 A B C op) = (term680 A B C op).
Proof. exact (MK_COMB (@lem5950688 A) (@lem5950687 A B C op)). Qed.
Lemma lem5950690 {A B C : Type'} (op : type1400 C) : (term681 A B C op) = (term682 A B C op).
Proof. exact (MK_COMB (@lem5950674 A B C op) (@lem5950689 A B C op)). Qed.
Lemma lem5950691 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5950692 {A B C : Type'} (op : type1400 C) : (term683 A B C op) = (term684 A B C op).
Proof. exact (MK_COMB (@lem5950691) (@lem5950690 A B C op)). Qed.
Lemma lem5950693 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term661 A B C op s) = (term649 A B C op s).
Proof. exact (eq_refl (term661 A B C op s)). Qed.
Lemma lem5950694 {A : Type'} (s : A -> Prop) : (term642 A s) = (term642 A s).
Proof. exact (eq_refl (term642 A s)). Qed.
Lemma lem5950695 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term685 A B C op s) = (term650 A B C op s).
Proof. exact (MK_COMB (@lem5950694 A s) (@lem5950693 A B C op s)). Qed.
Lemma lem5950696 {A B C : Type'} (op : type1400 C) : (term686 A B C op) = (term652 A B C op).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5950695 A B C op s)). Qed.
Lemma lem5950697 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5950698 {A B C : Type'} (op : type1400 C) : (term687 A B C op) = (term654 A B C op).
Proof. exact (MK_COMB (@lem5950697 A) (@lem5950696 A B C op)). Qed.
Lemma lem5950699 {A B C : Type'} (op : type1400 C) : (term655 A B C op) = (term688 A B C op).
Proof. exact (MK_COMB (@lem5950692 A B C op) (@lem5950698 A B C op)). Qed.
Lemma lem5950700 {A B C : Type'} (op : type1400 C) : term688 A B C op.
Proof. exact (EQ_MP (@lem5950699 A B C op) (@lem5950671 A B C op)). Qed.
Lemma lem5950701 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term689 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem5950702 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term689 _120477 _120519 _120521 op) = (term690 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term689 _120477 _120519 _120521 op)). Qed.
Lemma lem5950703 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term690 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem5950702 _120477 _120519 _120521 op) (@lem5950701 _120477 _120519 _120521 op)). Qed.
Lemma lem5950704 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem5950705 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term691 _120477 _120519 _120521 op.
Proof. exact (@lem5950703 _120477 _120519 _120521 op (@lem5950704 _120519 op h1)). Qed.
Lemma lem5950706 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term692 _120519 _120521 op.
Proof. exact (proj2 (@lem5950705 Prop _120519 _120521 op h1)). Qed.
Lemma lem5950707 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term693 _120519 _120521 op f.
Proof. exact (@lem5950706 _120519 _120521 op h1 f). Qed.
Lemma lem5950708 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term693 _120519 _120521 op f) = (term694 _120519 _120521 op f).
Proof. exact (eq_refl (term693 _120519 _120521 op f)). Qed.
Lemma lem5950709 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term694 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem5950708 _120519 _120521 op f) (@lem5950707 _120519 _120521 f op h1)). Qed.
Lemma lem5950710 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term695 _120519 _120521 op f x.
Proof. exact (@lem5950709 _120519 _120521 f op h1 x). Qed.
Lemma lem5950711 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term695 _120519 _120521 op f x) = (term696 _120519 _120521 x op f).
Proof. exact (eq_refl (term695 _120519 _120521 op f x)). Qed.
Lemma lem5950712 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term696 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem5950711 _120519 _120521 x op f) (@lem5950710 _120519 _120521 f x op h1)). Qed.
Lemma lem5950713 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term697 _120519 _120521 x op f s.
Proof. exact (@lem5950712 _120519 _120521 x f op h1 s). Qed.
Lemma lem5950714 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term697 _120519 _120521 x op f s) = (term698 _120519 _120521 x op s f).
Proof. exact (eq_refl (term697 _120519 _120521 x op f s)). Qed.
Lemma lem5950715 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term698 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5950714 _120519 _120521 x op s f) (@lem5950713 _120519 _120521 x f s op h1)). Qed.
Lemma lem5950716 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem5950717 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term699 _120519 _120521 op x s f) = (term700 _120519 _120521 x op s f).
Proof. exact (@lem5950715 _120519 _120521 x s f op h2 (@lem5950716 _120521 s h1)). Qed.
Lemma lem5950718 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term701 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5950717 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem5950719 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term702 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem5950718 _120519 _120521 x op f s h0). Qed.
Lemma lem5950721 (p : Prop) (q : Prop) (r : Prop) : (term628 p q r) = (term627 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5950726 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term702 _120519 _120521 x op s f) = (term703 _120519 _120521 x op s f).
Proof. exact (@lem5950721 (@FINITE _120521 s) (@monoidal _120519 op) ((term699 _120519 _120521 op x s f) = (term700 _120519 _120521 x op s f))). Qed.
Lemma lem5950728 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term704 _120477 _120519 op.
Proof. exact (proj1 (@lem5950705 _120477 _120519 Prop op h1)). Qed.
Lemma lem5950729 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term705 _120477 _120519 op f.
Proof. exact (@lem5950728 _120477 _120519 op h1 f). Qed.
Lemma lem5950730 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term705 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term705 _120477 _120519 op f)). Qed.
Lemma lem5950731 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem5950730 _120477 _120519 f op) (@lem5950729 _120477 _120519 f op h1)). Qed.
Lemma lem5950737 {A : Type'} (x : A) : term23 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5950738 {A : Type'} (x : A) : (term23 A x) = (term24 A x).
Proof. exact (eq_refl (term23 A x)). Qed.
Lemma lem5950739 {A : Type'} (x : A) : term24 A x.
Proof. exact (EQ_MP (@lem5950738 A x) (@lem5950737 A x)). Qed.
Lemma lem5950740 {A : Type'} (x : A) : term25 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5950742 {C : Type'} (op : type1400 C) : (@monoidal C op) = ((@monoidal C op) = True).
Proof. exact (@lem7 (@monoidal C op)). Qed.
Lemma lem5950753 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term706 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5950754 (p : Prop) (q : Prop) (p' : Prop) : term707 p q p'.
Proof. exact (fun q' : Prop => @lem5950753 p q p' q'). Qed.
Lemma lem5950755 (p : Prop) (q : Prop) : term708 p q.
Proof. exact (fun p' : Prop => @lem5950754 p q p'). Qed.
Lemma lem5950756 {A B C : Type'} (op : type1400 C) (t : type1413 A B) : term709 A B C op t.
Proof. exact (@lem5950755 (term710 A B t) (term711 A B C op t)). Qed.
Lemma lem5950757 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (p' : Prop) : term712 A B C op t p'.
Proof. exact (@lem5950756 A B C op t p'). Qed.
Lemma lem5950758 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (p' : Prop) : (term712 A B C op t p') = (term713 A B C op t p').
Proof. exact (eq_refl (term712 A B C op t p')). Qed.
Lemma lem5950759 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (p' : Prop) : term713 A B C op t p'.
Proof. exact (EQ_MP (@lem5950758 A B C op t p') (@lem5950757 A B C op t p')). Qed.
Lemma lem5950760 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (p' : Prop) (q' : Prop) : term714 A B C op t p' q'.
Proof. exact (@lem5950759 A B C op t p' q'). Qed.
Lemma lem5950761 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (p' : Prop) (q' : Prop) : (term714 A B C op t p' q') = (term715 A B C op t p' q').
Proof. exact (eq_refl (term714 A B C op t p' q')). Qed.
Lemma lem5950762 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (p' : Prop) (q' : Prop) : term715 A B C op t p' q'.
Proof. exact (EQ_MP (@lem5950761 A B C op t p' q') (@lem5950760 A B C op t p' q')). Qed.
Lemma lem5950770 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term706 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5950771 (p : Prop) (q : Prop) (p' : Prop) : term707 p q p'.
Proof. exact (fun q' : Prop => @lem5950770 p q p' q'). Qed.
Lemma lem5950772 (p : Prop) (q : Prop) : term708 p q.
Proof. exact (fun p' : Prop => @lem5950771 p q p'). Qed.
Lemma lem5950773 {A B : Type'} (t : type1413 A B) (i : A) : term716 A B t i.
Proof. exact (@lem5950772 (@IN A i (@EMPTY A)) (term717 A B t i)). Qed.
Lemma lem5950774 {A B : Type'} (t : type1413 A B) (i : A) (p' : Prop) : term718 A B t i p'.
Proof. exact (@lem5950773 A B t i p'). Qed.
Lemma lem5950775 {A B : Type'} (t : type1413 A B) (i : A) (p' : Prop) : (term718 A B t i p') = (term719 A B t i p').
Proof. exact (eq_refl (term718 A B t i p')). Qed.
Lemma lem5950776 {A B : Type'} (t : type1413 A B) (i : A) (p' : Prop) : term719 A B t i p'.
Proof. exact (EQ_MP (@lem5950775 A B t i p') (@lem5950774 A B t i p')). Qed.
Lemma lem5950777 {A B : Type'} (t : type1413 A B) (i : A) (p' : Prop) (q' : Prop) : term720 A B t i p' q'.
Proof. exact (@lem5950776 A B t i p' q'). Qed.
Lemma lem5950778 {A B : Type'} (t : type1413 A B) (i : A) (p' : Prop) (q' : Prop) : (term720 A B t i p' q') = (term721 A B t i p' q').
Proof. exact (eq_refl (term720 A B t i p' q')). Qed.
Lemma lem5950779 {A B : Type'} (t : type1413 A B) (i : A) (p' : Prop) (q' : Prop) : term721 A B t i p' q'.
Proof. exact (EQ_MP (@lem5950778 A B t i p' q') (@lem5950777 A B t i p' q')). Qed.
Lemma lem5950781 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5950740 A x (@lem5950739 A x)). Qed.
Lemma lem5950782 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5950781 A x). Qed.
Lemma lem5950783 {A : Type'} (i : A) : (@IN A i (@EMPTY A)) = False.
Proof. exact (@lem5950782 A i). Qed.
Lemma lem5950784 {A B : Type'} (t : type1413 A B) (i : A) (q' : Prop) : term722 A B t i q'.
Proof. exact (@lem5950779 A B t i False q'). Qed.
Lemma lem5950785 {A B : Type'} (t : type1413 A B) (i : A) (q' : Prop) : term723 A B t i q'.
Proof. exact (@lem5950784 A B t i q' (@lem5950783 A i)). Qed.
Lemma lem5950789 {A B : Type'} (t : type1413 A B) (i : A) : (term717 A B t i) = (term717 A B t i).
Proof. exact (eq_refl (term717 A B t i)). Qed.
Lemma lem5950790 {A B : Type'} (t : type1413 A B) (i : A) : term724 A B t i.
Proof. exact (fun h0 : False => @lem5950789 A B t i). Qed.
Lemma lem5950791 {A B : Type'} (t : type1413 A B) (i : A) : term725 A B t i.
Proof. exact (@lem5950785 A B t i (term717 A B t i)). Qed.
Lemma lem5950792 {A B : Type'} (t : type1413 A B) (i : A) : (term726 A B t i) = (term727 A B t i).
Proof. exact (@lem5950791 A B t i (@lem5950790 A B t i)). Qed.
Lemma lem5950794 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5950795 {A B : Type'} (t : type1413 A B) (i : A) : (term727 A B t i) = True.
Proof. exact (@lem5950794 (term717 A B t i)). Qed.
Lemma lem5950796 {A B : Type'} (t : type1413 A B) (i : A) : (term726 A B t i) = True.
Proof. exact (TRANS (@lem5950792 A B t i) (@lem5950795 A B t i)). Qed.
Lemma lem5950797 {A B : Type'} (t : type1413 A B) : (term728 A B t) = (term729 A).
Proof. exact (fun_ext (fun i : A => @lem5950796 A B t i)). Qed.
Lemma lem5950798 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5950799 {A B : Type'} (t : type1413 A B) : (term710 A B t) = (term730 A).
Proof. exact (MK_COMB (@lem5950798 A) (@lem5950797 A B t)). Qed.
Lemma lem5950801 {A : Type'} (t : Prop) : (term592 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5950802 {A : Type'} (t : Prop) : (term592 A t) = t.
Proof. exact (@lem5950801 A t). Qed.
Lemma lem5950803 {A : Type'} : (term730 A) = True.
Proof. exact (@lem5950802 A True). Qed.
Lemma lem5950804 {A B : Type'} (t : type1413 A B) : (term710 A B t) = True.
Proof. exact (TRANS (@lem5950799 A B t) (@lem5950803 A)). Qed.
Lemma lem5950805 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (q' : Prop) : term731 A B C op t q'.
Proof. exact (@lem5950762 A B C op t True q'). Qed.
Lemma lem5950806 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (q' : Prop) : term732 A B C op t q'.
Proof. exact (@lem5950805 A B C op t q' (@lem5950804 A B t)). Qed.
Lemma lem5950819 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term733 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5950731 _120477 _120519 f op h0). Qed.
Lemma lem5950820 {A C : Type'} (f : A -> C) (op : type1400 C) : term733 A C f op.
Proof. exact (@lem5950819 A C f op). Qed.
Lemma lem5950821 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) : term734 A B C t x op.
Proof. exact (@lem5950820 A C (term735 A B C op t x) op). Qed.
Lemma lem5950823 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem5950742 C op) (@lem5950451 C op h1)). Qed.
Lemma lem5950826 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : True = (@monoidal C op).
Proof. exact (SYM (@lem5950823 C op h1)). Qed.
Lemma lem5950827 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (EQ_MP (@lem5950826 C op h1) (@lem0)). Qed.
Lemma lem5950828 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term736 A B C op t x) = (@neutral C op).
Proof. exact (@lem5950821 A B C t x op (@lem5950827 C op h1)). Qed.
Lemma lem5950829 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem5950830 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term737 A B C op t x) = (term738 C op).
Proof. exact (MK_COMB (@lem5950829 C) (@lem5950828 A B C t x op h1)). Qed.
Lemma lem5950842 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5950740 A x (@lem5950739 A x)). Qed.
Lemma lem5950843 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5950842 A x). Qed.
Lemma lem5950844 {A : Type'} (i : A) : (@IN A i (@EMPTY A)) = False.
Proof. exact (@lem5950843 A i). Qed.
Lemma lem5950845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5950846 {A : Type'} (i : A) : (term739 A i) = (and False).
Proof. exact (MK_COMB (@lem5950845) (@lem5950844 A i)). Qed.
Lemma lem5950847 {A B : Type'} (j : B) (t : type1413 A B) (i : A) : (term740 A B j t i) = (term740 A B j t i).
Proof. exact (eq_refl (term740 A B j t i)). Qed.
Lemma lem5950848 {A B : Type'} (j : B) (t : type1413 A B) (i : A) : (term741 A B j t i) = (term742 A B j t i).
Proof. exact (MK_COMB (@lem5950846 A i) (@lem5950847 A B j t i)). Qed.
Lemma lem5950850 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5950851 {A B : Type'} (j : B) (t : type1413 A B) (i : A) : (term742 A B j t i) = False.
Proof. exact (@lem5950850 (term740 A B j t i)). Qed.
Lemma lem5950852 {A B : Type'} (j : B) (t : type1413 A B) (i : A) : (term741 A B j t i) = False.
Proof. exact (TRANS (@lem5950848 A B j t i) (@lem5950851 A B j t i)). Qed.
Lemma lem5950853 {A B : Type'} (GEN_PVAR_241 : prod A B) : (@SETSPEC (prod A B) GEN_PVAR_241) = (@SETSPEC (prod A B) GEN_PVAR_241).
Proof. exact (eq_refl (@SETSPEC (prod A B) GEN_PVAR_241)). Qed.
Lemma lem5950854 {A B : Type'} (j : B) (t : type1413 A B) (i : A) (GEN_PVAR_241 : prod A B) : (term743 A B GEN_PVAR_241 j t i) = (@SETSPEC (prod A B) GEN_PVAR_241 False).
Proof. exact (MK_COMB (@lem5950853 A B GEN_PVAR_241) (@lem5950852 A B j t i)). Qed.
Lemma lem5950855 {A B : Type'} (i : A) (j : B) : (@pair A B i j) = (@pair A B i j).
Proof. exact (eq_refl (@pair A B i j)). Qed.
Lemma lem5950856 {A B : Type'} (t : type1413 A B) (GEN_PVAR_241 : prod A B) (i : A) (j : B) : (term744 A B GEN_PVAR_241 t i j) = (term745 A B GEN_PVAR_241 i j).
Proof. exact (MK_COMB (@lem5950854 A B j t i GEN_PVAR_241) (@lem5950855 A B i j)). Qed.
Lemma lem5950857 {A B : Type'} (t : type1413 A B) (GEN_PVAR_241 : prod A B) (i : A) : (term746 A B GEN_PVAR_241 t i) = (term747 A B GEN_PVAR_241 i).
Proof. exact (fun_ext (fun j : B => @lem5950856 A B t GEN_PVAR_241 i j)). Qed.
Lemma lem5950858 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5950859 {A B : Type'} (t : type1413 A B) (GEN_PVAR_241 : prod A B) (i : A) : (term748 A B GEN_PVAR_241 t i) = (term749 A B GEN_PVAR_241 i).
Proof. exact (MK_COMB (@lem5950858 B) (@lem5950857 A B t GEN_PVAR_241 i)). Qed.
Lemma lem5950864 {A B : Type'} (t : type1413 A B) (GEN_PVAR_241 : prod A B) : (term750 A B GEN_PVAR_241 t) = (term751 A B GEN_PVAR_241).
Proof. exact (fun_ext (fun i : A => @lem5950859 A B t GEN_PVAR_241 i)). Qed.
Lemma lem5950869 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5950870 {A B : Type'} (t : type1413 A B) (GEN_PVAR_241 : prod A B) : (term752 A B GEN_PVAR_241 t) = (term753 A B GEN_PVAR_241).
Proof. exact (MK_COMB (@lem5950869 A) (@lem5950864 A B t GEN_PVAR_241)). Qed.
Lemma lem5950879 {A B : Type'} (t : type1413 A B) : (term754 A B t) = (term755 A B).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5950870 A B t GEN_PVAR_241)). Qed.
Lemma lem5950888 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem5950889 {A B : Type'} (t : type1413 A B) : (term756 A B t) = (term757 A B).
Proof. exact (MK_COMB (@lem5950888 A B) (@lem5950879 A B t)). Qed.
Lemma lem5950891 {_121879 _121880 : Type'} : (term555 _121879 _121880) = (@EMPTY (prod _121880 _121879)).
Proof. exact (EQ_MP (@lem5950324 _121879 _121880) (@lem5950427 _121879 _121880)). Qed.
Lemma lem5950892 {A B : Type'} : (term757 A B) = (@EMPTY (prod A B)).
Proof. exact (@lem5950891 B A). Qed.
Lemma lem5950893 {A B : Type'} (t : type1413 A B) : (term756 A B t) = (@EMPTY (prod A B)).
Proof. exact (TRANS (@lem5950889 A B t) (@lem5950892 A B)). Qed.
Lemma lem5950894 {A B C : Type'} (op : type1400 C) : (@iterate C (prod A B) op) = (@iterate C (prod A B) op).
Proof. exact (eq_refl (@iterate C (prod A B) op)). Qed.
Lemma lem5950895 {A B C : Type'} (t : type1413 A B) (op : type1400 C) : (term758 A B C op t) = (@iterate C (prod A B) op (@EMPTY (prod A B))).
Proof. exact (MK_COMB (@lem5950894 A B C op) (@lem5950893 A B t)). Qed.
Lemma lem5950904 {A B C : Type'} (x : type1412 A B C) : (term759 A B C x) = (term759 A B C x).
Proof. exact (eq_refl (term759 A B C x)). Qed.
Lemma lem5950905 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : type1412 A B C) : (term760 A B C op t x) = (term761 A B C op x).
Proof. exact (MK_COMB (@lem5950895 A B C t op) (@lem5950904 A B C x)). Qed.
Lemma lem5950907 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term733 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5950731 _120477 _120519 f op h0). Qed.
Lemma lem5950908 {A B C : Type'} (f : type1209 A B C) (op : type1400 C) : term762 A B C f op.
Proof. exact (@lem5950907 (prod A B) C f op). Qed.
Lemma lem5950909 {A B C : Type'} (x : type1412 A B C) (op : type1400 C) : term763 A B C x op.
Proof. exact (@lem5950908 A B C (term759 A B C x) op). Qed.
Lemma lem5950911 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem5950742 C op) (@lem5950451 C op h1)). Qed.
Lemma lem5950914 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : True = (@monoidal C op).
Proof. exact (SYM (@lem5950911 C op h1)). Qed.
Lemma lem5950915 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (EQ_MP (@lem5950914 C op h1) (@lem0)). Qed.
Lemma lem5950916 {A B C : Type'} (x : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term761 A B C op x) = (@neutral C op).
Proof. exact (@lem5950909 A B C x op (@lem5950915 C op h1)). Qed.
Lemma lem5950917 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term760 A B C op t x) = (@neutral C op).
Proof. exact (TRANS (@lem5950905 A B C t op x) (@lem5950916 A B C x op h1)). Qed.
Lemma lem5950918 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : ((term736 A B C op t x) = (term760 A B C op t x)) = ((@neutral C op) = (@neutral C op)).
Proof. exact (MK_COMB (@lem5950830 A B C t x op h1) (@lem5950917 A B C t x op h1)). Qed.
Lemma lem5950920 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5950921 {C : Type'} (x : C) : (x = x) = True.
Proof. exact (@lem5950920 C x). Qed.
Lemma lem5950922 {C : Type'} (op : type1400 C) : ((@neutral C op) = (@neutral C op)) = True.
Proof. exact (@lem5950921 C (@neutral C op)). Qed.
Lemma lem5950925 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : ((term736 A B C op t x) = (term760 A B C op t x)) = True.
Proof. exact (TRANS (@lem5950918 A B C t x op h1) (@lem5950922 C op)). Qed.
Lemma lem5950926 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (h1 : @monoidal C op) : (term764 A B C op t) = (term765 A B C).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5950925 A B C t x op h1)). Qed.
Lemma lem5950929 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5950930 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (h1 : @monoidal C op) : (term711 A B C op t) = (term766 A B C).
Proof. exact (MK_COMB (@lem5950929 A B C) (@lem5950926 A B C t op h1)). Qed.
Lemma lem5950932 {A : Type'} (t : Prop) : (term592 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5950933 {A B C : Type'} (t : Prop) : (term767 A B C t) = t.
Proof. exact (@lem5950932 (type1412 A B C) t). Qed.
Lemma lem5950934 {A B C : Type'} : (term766 A B C) = True.
Proof. exact (@lem5950933 A B C True). Qed.
Lemma lem5950937 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (h1 : @monoidal C op) : (term711 A B C op t) = True.
Proof. exact (TRANS (@lem5950930 A B C t op h1) (@lem5950934 A B C)). Qed.
Lemma lem5950938 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (h1 : @monoidal C op) : term768 A B C op t.
Proof. exact (fun h0 : True => @lem5950937 A B C t op h1). Qed.
Lemma lem5950939 {A B C : Type'} (op : type1400 C) (t : type1413 A B) : term769 A B C op t.
Proof. exact (@lem5950806 A B C op t True). Qed.
Lemma lem5950940 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (h1 : @monoidal C op) : (term770 A B C op t) = (True -> True).
Proof. exact (@lem5950939 A B C op t (@lem5950938 A B C t op h1)). Qed.
Lemma lem5950942 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5950943 : (True -> True) = True.
Proof. exact (@lem5950942 True). Qed.
Lemma lem5950944 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (h1 : @monoidal C op) : (term770 A B C op t) = True.
Proof. exact (TRANS (@lem5950940 A B C t op h1) (@lem5950943)). Qed.
Lemma lem5950945 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term771 A B C op) = (term772 A B).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5950944 A B C t op h1)). Qed.
Lemma lem5950946 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5950947 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term658 A B C op) = (term773 A B).
Proof. exact (MK_COMB (@lem5950946 A B) (@lem5950945 A B C op h1)). Qed.
Lemma lem5950949 {A : Type'} (t : Prop) : (term592 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5950950 {A B : Type'} (t : Prop) : (term774 A B t) = t.
Proof. exact (@lem5950949 (type1413 A B) t). Qed.
Lemma lem5950951 {A B : Type'} : (term773 A B) = True.
Proof. exact (@lem5950950 A B True). Qed.
Lemma lem5950952 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term658 A B C op) = True.
Proof. exact (TRANS (@lem5950947 A B C op h1) (@lem5950951 A B)). Qed.
Lemma lem5950953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5950954 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term660 A B C op) = (and True).
Proof. exact (MK_COMB (@lem5950953) (@lem5950952 A B C op h1)). Qed.
Lemma lem5950966 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term706 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5950967 (p : Prop) (q : Prop) (p' : Prop) : term707 p q p'.
Proof. exact (fun q' : Prop => @lem5950966 p q p' q'). Qed.
Lemma lem5950968 (p : Prop) (q : Prop) : term708 p q.
Proof. exact (fun p' : Prop => @lem5950967 p q p'). Qed.
Lemma lem5950969 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : term775 A B C op x s.
Proof. exact (@lem5950968 (term666 A B C op x s) (term670 A B C op x s)). Qed.
Lemma lem5950970 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (p' : Prop) : term776 A B C op x s p'.
Proof. exact (@lem5950969 A B C op x s p'). Qed.
Lemma lem5950971 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (p' : Prop) : (term776 A B C op x s p') = (term777 A B C op x s p').
Proof. exact (eq_refl (term776 A B C op x s p')). Qed.
Lemma lem5950972 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (p' : Prop) : term777 A B C op x s p'.
Proof. exact (EQ_MP (@lem5950971 A B C op x s p') (@lem5950970 A B C op x s p')). Qed.
Lemma lem5950973 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term778 A B C op x s p' q'.
Proof. exact (@lem5950972 A B C op x s p' q'). Qed.
Lemma lem5950974 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term778 A B C op x s p' q') = (term779 A B C op x s p' q').
Proof. exact (eq_refl (term778 A B C op x s p' q')). Qed.
Lemma lem5950975 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term779 A B C op x s p' q'.
Proof. exact (EQ_MP (@lem5950974 A B C op x s p' q') (@lem5950973 A B C op x s p' q')). Qed.
Lemma lem5951119 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : (term666 A B C op x s) = (term666 A B C op x s).
Proof. exact (eq_refl (term666 A B C op x s)). Qed.
Lemma lem5951120 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (q' : Prop) : term780 A B C op x s q'.
Proof. exact (@lem5950975 A B C op x s (term666 A B C op x s) q'). Qed.
Lemma lem5951121 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (q' : Prop) : term781 A B C op x s q'.
Proof. exact (@lem5951120 A B C op x s q' (@lem5951119 A B C op x s)). Qed.
Lemma lem5951122 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : term666 A B C op x s.
Proof. exact (h1). Qed.
Lemma lem5951123 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : term664 A x s.
Proof. exact (proj2 (@lem5951122 A B C op x s h1)). Qed.
Lemma lem5951124 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : @FINITE A s.
Proof. exact (proj2 (@lem5951123 A B C op x s h1)). Qed.
Lemma lem5951125 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem5951127 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : term782 A x s.
Proof. exact (proj1 (@lem5951123 A B C op x s h1)). Qed.
Lemma lem5951128 {A : Type'} (x : A) (s : A -> Prop) : term783 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem5951151 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term706 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5951152 (p : Prop) (q : Prop) (p' : Prop) : term707 p q p'.
Proof. exact (fun q' : Prop => @lem5951151 p q p' q'). Qed.
Lemma lem5951153 (p : Prop) (q : Prop) : term708 p q.
Proof. exact (fun p' : Prop => @lem5951152 p q p'). Qed.
Lemma lem5951154 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : term784 A B C op x s t.
Proof. exact (@lem5951153 (term785 A B x s t) (term786 A B C op x s t)). Qed.
Lemma lem5951155 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) : term787 A B C op x s t p'.
Proof. exact (@lem5951154 A B C op x s t p'). Qed.
Lemma lem5951156 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) : (term787 A B C op x s t p') = (term788 A B C op x s t p').
Proof. exact (eq_refl (term787 A B C op x s t p')). Qed.
Lemma lem5951157 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) : term788 A B C op x s t p'.
Proof. exact (EQ_MP (@lem5951156 A B C op x s t p') (@lem5951155 A B C op x s t p')). Qed.
Lemma lem5951158 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) (q' : Prop) : term789 A B C op x s t p' q'.
Proof. exact (@lem5951157 A B C op x s t p' q'). Qed.
Lemma lem5951159 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) (q' : Prop) : (term789 A B C op x s t p' q') = (term790 A B C op x s t p' q').
Proof. exact (eq_refl (term789 A B C op x s t p' q')). Qed.
Lemma lem5951160 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) (q' : Prop) : term790 A B C op x s t p' q'.
Proof. exact (EQ_MP (@lem5951159 A B C op x s t p' q') (@lem5951158 A B C op x s t p' q')). Qed.
Lemma lem5951188 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term785 A B x s t) = (term785 A B x s t).
Proof. exact (eq_refl (term785 A B x s t)). Qed.
Lemma lem5951189 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (q' : Prop) : term791 A B C op x s t q'.
Proof. exact (@lem5951160 A B C op x s t (term785 A B x s t) q'). Qed.
Lemma lem5951190 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (q' : Prop) : term792 A B C op x s t q'.
Proof. exact (@lem5951189 A B C op x s t q' (@lem5951188 A B x s t)). Qed.
Lemma lem5951211 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term703 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5950726 _120519 _120521 x op s f) (@lem5950719 _120519 _120521 x op s f)). Qed.
Lemma lem5951212 {A C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : A -> C) : term793 A C x op s f.
Proof. exact (@lem5951211 C A x op s f). Qed.
Lemma lem5951213 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) : term794 A B C x s op t x'.
Proof. exact (@lem5951212 A C x op s (term735 A B C op t x')). Qed.
Lemma lem5951217 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem5951125 A s) (@lem5951124 A B C op x s h1)). Qed.
Lemma lem5951218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5951219 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : (term795 A s) = (and True).
Proof. exact (MK_COMB (@lem5951218) (@lem5951217 A B C op x s h1)). Qed.
Lemma lem5951221 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem5950742 C op) (@lem5950451 C op h1)). Qed.
Lemma lem5951222 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x s) : (term796 A C s op) = (True /\ True).
Proof. exact (MK_COMB (@lem5951219 A B C op x s h2) (@lem5951221 C op h1)). Qed.
Lemma lem5951224 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5951225 : (True /\ True) = True.
Proof. exact (@lem5951224 True). Qed.
Lemma lem5951226 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x s) : (term796 A C s op) = True.
Proof. exact (TRANS (@lem5951222 A B C op x s h1 h2) (@lem5951225)). Qed.
Lemma lem5951227 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x s) : True = (term796 A C s op).
Proof. exact (SYM (@lem5951226 A B C op x s h1 h2)). Qed.
Lemma lem5951228 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x s) : term796 A C s op.
Proof. exact (EQ_MP (@lem5951227 A B C op x s h1 h2) (@lem0)). Qed.
Lemma lem5951229 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x' s) : (term797 A B C x' s op t x) = (term798 A B C x' s op t x).
Proof. exact (@lem5951213 A B C x' s op t x (@lem5951228 A B C op x' s h1 h2)). Qed.
Lemma lem5951231 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term799 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5951232 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term800 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5951231 _2963 g t e g' t' e'). Qed.
Lemma lem5951233 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term801 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5951232 _2963 g t e g' t'). Qed.
Lemma lem5951234 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term802 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5951233 _2963 g t e g'). Qed.
Lemma lem5951235 {C : Type'} (g : Prop) (t : C) (e : C) : term802 C g t e.
Proof. exact (@lem5951234 C g t e). Qed.
Lemma lem5951236 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) : term803 A B C x s op t x'.
Proof. exact (@lem5951235 C (@IN A x s) (term613 A B C s op t x') (term804 A B C x s op t x')). Qed.
Lemma lem5951237 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (g' : Prop) : term805 A B C x s op t x' g'.
Proof. exact (@lem5951236 A B C x s op t x' g'). Qed.
Lemma lem5951238 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (g' : Prop) : (term805 A B C x s op t x' g') = (term806 A B C x s op t x' g').
Proof. exact (eq_refl (term805 A B C x s op t x' g')). Qed.
Lemma lem5951239 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (g' : Prop) : term806 A B C x s op t x' g'.
Proof. exact (EQ_MP (@lem5951238 A B C x s op t x' g') (@lem5951237 A B C x s op t x' g')). Qed.
Lemma lem5951240 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (g' : Prop) (t' : C) : term807 A B C x s op t x' g' t'.
Proof. exact (@lem5951239 A B C x s op t x' g' t'). Qed.
Lemma lem5951241 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (g' : Prop) (t' : C) : (term807 A B C x s op t x' g' t') = (term808 A B C x s op t x' g' t').
Proof. exact (eq_refl (term807 A B C x s op t x' g' t')). Qed.
Lemma lem5951242 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (g' : Prop) (t' : C) : term808 A B C x s op t x' g' t'.
Proof. exact (EQ_MP (@lem5951241 A B C x s op t x' g' t') (@lem5951240 A B C x s op t x' g' t')). Qed.
Lemma lem5951243 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (g' : Prop) (t' : C) (e' : C) : term809 A B C x s op t x' g' t' e'.
Proof. exact (@lem5951242 A B C x s op t x' g' t' e'). Qed.
Lemma lem5951244 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (g' : Prop) (t' : C) (e' : C) : (term809 A B C x s op t x' g' t' e') = (term810 A B C x s op t x' g' t' e').
Proof. exact (eq_refl (term809 A B C x s op t x' g' t' e')). Qed.
Lemma lem5951245 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (g' : Prop) (t' : C) (e' : C) : term810 A B C x s op t x' g' t' e'.
Proof. exact (EQ_MP (@lem5951244 A B C x s op t x' g' t' e') (@lem5951243 A B C x s op t x' g' t' e')). Qed.
Lemma lem5951247 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : (@IN A x s) = False.
Proof. exact (@lem5951128 A x s (@lem5951127 A B C op x s h1)). Qed.
Lemma lem5951248 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (t' : C) (e' : C) : term811 A B C x s op t x' t' e'.
Proof. exact (@lem5951245 A B C x s op t x' False t' e'). Qed.
Lemma lem5951249 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (t' : C) (e' : C) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term666 A B C op x' s) : term812 A B C x' s op t x t' e'.
Proof. exact (@lem5951248 A B C x' s op t x t' e' (@lem5951247 A B C op x' s h1)). Qed.
Lemma lem5951295 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term613 A B C s op t x) = (term613 A B C s op t x).
Proof. exact (eq_refl (term613 A B C s op t x)). Qed.
Lemma lem5951296 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : term813 A B C s op t x.
Proof. exact (fun h0 : False => @lem5951295 A B C s op t x). Qed.
Lemma lem5951297 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (e' : C) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term666 A B C op x' s) : term814 A B C x' s op t x e'.
Proof. exact (@lem5951249 A B C t x (term613 A B C s op t x) e' op x' s h1). Qed.
Lemma lem5951298 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (e' : C) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term666 A B C op x' s) : term815 A B C x' s op t x e'.
Proof. exact (@lem5951297 A B C t x e' op x' s h1 (@lem5951296 A B C s op t x)). Qed.
Lemma lem5951305 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5951306 {A C : Type'} (f : A -> C) (y : A) : (term72 A C f y) = (f y).
Proof. exact (@lem5951305 A C f y). Qed.
Lemma lem5951307 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (x' : A) : (term816 A B C op t x x') = (term817 A B C op t x x').
Proof. exact (@lem5951306 A C (term735 A B C op t x) x'). Qed.
Lemma lem5951308 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (i : A) : (term817 A B C op t x i) = (term818 A B C op t x i).
Proof. exact (eq_refl (term817 A B C op t x i)). Qed.
Lemma lem5951309 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term819 A B C op t x) = (term735 A B C op t x).
Proof. exact (fun_ext (fun i : A => @lem5951308 A B C op t x i)). Qed.
Lemma lem5951310 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5951311 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (x' : A) : (term816 A B C op t x x') = (term817 A B C op t x x').
Proof. exact (MK_COMB (@lem5951309 A B C op t x) (@lem5951310 A x')). Qed.
Lemma lem5951312 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem5951313 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (x' : A) : (term820 A B C op t x x') = (term821 A B C op t x x').
Proof. exact (MK_COMB (@lem5951312 C) (@lem5951311 A B C op t x x')). Qed.
Lemma lem5951314 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (x' : A) : (term817 A B C op t x x') = (term818 A B C op t x x').
Proof. exact (eq_refl (term817 A B C op t x x')). Qed.
Lemma lem5951315 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (x' : A) : ((term816 A B C op t x x') = (term817 A B C op t x x')) = ((term817 A B C op t x x') = (term818 A B C op t x x')).
Proof. exact (MK_COMB (@lem5951313 A B C op t x x') (@lem5951314 A B C op t x x')). Qed.
Lemma lem5951316 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (x' : A) : (term817 A B C op t x x') = (term818 A B C op t x x').
Proof. exact (EQ_MP (@lem5951315 A B C op t x x') (@lem5951307 A B C op t x x')). Qed.
Lemma lem5951317 {C : Type'} (op : type1400 C) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5951318 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (x' : A) : (term822 A B C op t x x') = (term823 A B C op t x x').
Proof. exact (MK_COMB (@lem5951317 C op) (@lem5951316 A B C op t x x')). Qed.
Lemma lem5951361 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term613 A B C s op t x) = (term613 A B C s op t x).
Proof. exact (eq_refl (term613 A B C s op t x)). Qed.
Lemma lem5951362 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) : (term804 A B C x s op t x') = (term824 A B C x s op t x').
Proof. exact (MK_COMB (@lem5951318 A B C op t x' x) (@lem5951361 A B C s op t x')). Qed.
Lemma lem5951405 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) : term825 A B C x s op t x'.
Proof. exact (fun h0 : ~ False => @lem5951362 A B C x s op t x'). Qed.
Lemma lem5951406 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term666 A B C op x' s) : term826 A B C x' s op t x.
Proof. exact (@lem5951298 A B C t x (term824 A B C x' s op t x) op x' s h1). Qed.
Lemma lem5951407 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term666 A B C op x' s) : (term798 A B C x' s op t x) = (term827 A B C x' s op t x).
Proof. exact (@lem5951406 A B C t x op x' s h1 (@lem5951405 A B C x' s op t x)). Qed.
Lemma lem5951409 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5951410 {C : Type'} (t1 : C) (t2 : C) : (@COND C False t1 t2) = t2.
Proof. exact (@lem5951409 C t1 t2). Qed.
Lemma lem5951411 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) : (term827 A B C x s op t x') = (term824 A B C x s op t x').
Proof. exact (@lem5951410 C (term613 A B C s op t x') (term824 A B C x s op t x')). Qed.
Lemma lem5951454 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term666 A B C op x' s) : (term798 A B C x' s op t x) = (term824 A B C x' s op t x).
Proof. exact (TRANS (@lem5951407 A B C t x op x' s h1) (@lem5951411 A B C x' s op t x)). Qed.
Lemma lem5951455 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x' s) : (term797 A B C x' s op t x) = (term824 A B C x' s op t x).
Proof. exact (TRANS (@lem5951229 A B C t x op x' s h1 h2) (@lem5951454 A B C t x op x' s h2)). Qed.
Lemma lem5951456 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem5951457 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x' s) : (term828 A B C x' s op t x) = (term829 A B C x' s op t x).
Proof. exact (MK_COMB (@lem5951456 C) (@lem5951455 A B C t x op x' s h1 h2)). Qed.
Lemma lem5951518 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : (term830 A B C op x s t x') = (term830 A B C op x s t x').
Proof. exact (eq_refl (term830 A B C op x s t x')). Qed.
Lemma lem5951519 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x' s) : ((term797 A B C x' s op t x) = (term830 A B C op x' s t x)) = ((term824 A B C x' s op t x) = (term830 A B C op x' s t x)).
Proof. exact (MK_COMB (@lem5951457 A B C t x op x' s h1 h2) (@lem5951518 A B C op x' s t x)). Qed.
Lemma lem5951582 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x s) : (term831 A B C op x s t) = (term832 A B C op x s t).
Proof. exact (fun_ext (fun x' : type1412 A B C => @lem5951519 A B C t x' op x s h1 h2)). Qed.
Lemma lem5951645 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5951646 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x s) : (term786 A B C op x s t) = (term833 A B C op x s t).
Proof. exact (MK_COMB (@lem5951645 A B C) (@lem5951582 A B C t op x s h1 h2)). Qed.
Lemma lem5951713 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x s) : term834 A B C op x s t.
Proof. exact (fun h0 : term785 A B x s t => @lem5951646 A B C t op x s h1 h2). Qed.
Lemma lem5951714 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : term835 A B C op x s t.
Proof. exact (@lem5951190 A B C op x s t (term833 A B C op x s t)). Qed.
Lemma lem5951715 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x s) : (term836 A B C op x s t) = (term837 A B C op x s t).
Proof. exact (@lem5951714 A B C op x s t (@lem5951713 A B C t op x s h1 h2)). Qed.
Lemma lem5951925 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x s) : (term838 A B C op x s) = (term839 A B C op x s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5951715 A B C t op x s h1 h2)). Qed.
Lemma lem5952135 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5952136 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x s) : (term670 A B C op x s) = (term840 A B C op x s).
Proof. exact (MK_COMB (@lem5952135 A B) (@lem5951925 A B C op x s h1 h2)). Qed.
Lemma lem5952350 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term841 A B C op x s.
Proof. exact (fun h0 : term666 A B C op x s => @lem5952136 A B C op x s h1 h0). Qed.
Lemma lem5952351 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : term842 A B C op x s.
Proof. exact (@lem5951121 A B C op x s (term840 A B C op x s)). Qed.
Lemma lem5952352 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : (term672 A B C op x s) = (term843 A B C op x s).
Proof. exact (@lem5952351 A B C op x s (@lem5952350 A B C x s op h1)). Qed.
Lemma lem5953033 {A B C : Type'} (x : A) (op : type1400 C) (h1 : @monoidal C op) : (term674 A B C op x) = (term844 A B C op x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5952352 A B C x s op h1)). Qed.
Lemma lem5953714 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5953715 {A B C : Type'} (x : A) (op : type1400 C) (h1 : @monoidal C op) : (term676 A B C op x) = (term845 A B C op x).
Proof. exact (MK_COMB (@lem5953714 A) (@lem5953033 A B C x op h1)). Qed.
Lemma lem5954400 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term678 A B C op) = (term846 A B C op).
Proof. exact (fun_ext (fun x : A => @lem5953715 A B C x op h1)). Qed.
Lemma lem5955085 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5955086 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term680 A B C op) = (term847 A B C op).
Proof. exact (MK_COMB (@lem5955085 A) (@lem5954400 A B C op h1)). Qed.
Lemma lem5955775 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term682 A B C op) = (term848 A B C op).
Proof. exact (MK_COMB (@lem5950954 A B C op h1) (@lem5955086 A B C op h1)). Qed.
Lemma lem5955777 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5955778 {A B C : Type'} (op : type1400 C) : (term848 A B C op) = (term847 A B C op).
Proof. exact (@lem5955777 (term847 A B C op)). Qed.
Lemma lem5956467 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term682 A B C op) = (term847 A B C op).
Proof. exact (TRANS (@lem5955775 A B C op h1) (@lem5955778 A B C op)). Qed.
Lemma lem5956468 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term847 A B C op) = (term682 A B C op).
Proof. exact (SYM (@lem5956467 A B C op h1)). Qed.
Lemma lem5956538 {_121855 _121856 : Type'} (a : _121856) (s : _121856 -> Prop) (t : type1470 _121855 _121856) : (term55 _121855 _121856 a s t) = (term56 _121855 _121856 a s t).
Proof. exact (EQ_MP (@lem5947517 _121855 _121856 a s t) (@lem5950290 _121855 _121856 a s t)). Qed.
Lemma lem5956539 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term849 A B a s t) = (term850 A B a s t).
Proof. exact (@lem5956538 B A a s t). Qed.
Lemma lem5956540 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term849 A B x s t) = (term850 A B x s t).
Proof. exact (@lem5956539 A B x s t). Qed.
Lemma lem5956551 {A B C : Type'} (op : type1400 C) : (@iterate C (prod A B) op) = (@iterate C (prod A B) op).
Proof. exact (eq_refl (@iterate C (prod A B) op)). Qed.
Lemma lem5956552 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : (term851 A B C op x s t) = (term852 A B C op x s t).
Proof. exact (MK_COMB (@lem5956551 A B C op) (@lem5956540 A B x s t)). Qed.
Lemma lem5956561 {A B C : Type'} (x : type1412 A B C) : (term759 A B C x) = (term759 A B C x).
Proof. exact (eq_refl (term759 A B C x)). Qed.
Lemma lem5956562 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : (term830 A B C op x s t x') = (term853 A B C op x s t x').
Proof. exact (MK_COMB (@lem5956552 A B C op x s t) (@lem5956561 A B C x')). Qed.
Lemma lem5956563 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) : (term829 A B C x s op t x') = (term829 A B C x s op t x').
Proof. exact (eq_refl (term829 A B C x s op t x')). Qed.
Lemma lem5956564 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : ((term824 A B C x s op t x') = (term830 A B C op x s t x')) = ((term824 A B C x s op t x') = (term853 A B C op x s t x')).
Proof. exact (MK_COMB (@lem5956563 A B C x s op t x') (@lem5956562 A B C op x s t x')). Qed.
Lemma lem5956567 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : (term832 A B C op x s t) = (term854 A B C op x s t).
Proof. exact (fun_ext (fun x' : type1412 A B C => @lem5956564 A B C op x s t x')). Qed.
Lemma lem5956568 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5956569 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : (term833 A B C op x s t) = (term855 A B C op x s t).
Proof. exact (MK_COMB (@lem5956568 A B C) (@lem5956567 A B C op x s t)). Qed.
Lemma lem5956574 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term856 A B x s t) = (term856 A B x s t).
Proof. exact (eq_refl (term856 A B x s t)). Qed.
Lemma lem5956575 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : (term837 A B C op x s t) = (term857 A B C op x s t).
Proof. exact (MK_COMB (@lem5956574 A B x s t) (@lem5956569 A B C op x s t)). Qed.
Lemma lem5956578 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : (term839 A B C op x s) = (term858 A B C op x s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5956575 A B C op x s t)). Qed.
Lemma lem5956579 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5956580 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : (term840 A B C op x s) = (term859 A B C op x s).
Proof. exact (MK_COMB (@lem5956579 A B) (@lem5956578 A B C op x s)). Qed.
Lemma lem5956585 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : (term668 A B C op x s) = (term668 A B C op x s).
Proof. exact (eq_refl (term668 A B C op x s)). Qed.
Lemma lem5956586 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : (term843 A B C op x s) = (term860 A B C op x s).
Proof. exact (MK_COMB (@lem5956585 A B C op x s) (@lem5956580 A B C op x s)). Qed.
Lemma lem5956589 {A B C : Type'} (op : type1400 C) (x : A) : (term844 A B C op x) = (term861 A B C op x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5956586 A B C op x s)). Qed.
Lemma lem5956590 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5956591 {A B C : Type'} (op : type1400 C) (x : A) : (term845 A B C op x) = (term862 A B C op x).
Proof. exact (MK_COMB (@lem5956590 A) (@lem5956589 A B C op x)). Qed.
Lemma lem5956596 {A B C : Type'} (op : type1400 C) : (term846 A B C op) = (term863 A B C op).
Proof. exact (fun_ext (fun x : A => @lem5956591 A B C op x)). Qed.
Lemma lem5956597 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5956598 {A B C : Type'} (op : type1400 C) : (term847 A B C op) = (term864 A B C op).
Proof. exact (MK_COMB (@lem5956597 A) (@lem5956596 A B C op)). Qed.
Lemma lem5956603 {A B C : Type'} (op : type1400 C) : (term864 A B C op) = (term847 A B C op).
Proof. exact (SYM (@lem5956598 A B C op)). Qed.
Lemma lem5956604 {A : Type'} (x : A) : term865 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5956605 {A : Type'} (x : A) : (term865 A x) = (term866 A x).
Proof. exact (eq_refl (term865 A x)). Qed.
Lemma lem5956606 {A : Type'} (x : A) : term866 A x.
Proof. exact (EQ_MP (@lem5956605 A x) (@lem5956604 A x)). Qed.
Lemma lem5956607 {A : Type'} (x : A) (y : A) : term867 A x y.
Proof. exact (@lem5956606 A x y). Qed.
Lemma lem5956608 {A : Type'} (y : A) (x : A) : (term867 A x y) = (term868 A y x).
Proof. exact (eq_refl (term867 A x y)). Qed.
Lemma lem5956609 {A : Type'} (y : A) (x : A) : term868 A y x.
Proof. exact (EQ_MP (@lem5956608 A y x) (@lem5956607 A x y)). Qed.
Lemma lem5956610 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term869 A y x s.
Proof. exact (@lem5956609 A y x s). Qed.
Lemma lem5956611 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term869 A y x s) = ((term84 A x y s) = (term85 A y x s)).
Proof. exact (eq_refl (term869 A y x s)). Qed.
Lemma lem5956668 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term706 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5956669 (p : Prop) (q : Prop) (p' : Prop) : term707 p q p'.
Proof. exact (fun q' : Prop => @lem5956668 p q p' q'). Qed.
Lemma lem5956670 (p : Prop) (q : Prop) : term708 p q.
Proof. exact (fun p' : Prop => @lem5956669 p q p'). Qed.
Lemma lem5956671 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : term870 A B C op x s.
Proof. exact (@lem5956670 (term666 A B C op x s) (term859 A B C op x s)). Qed.
Lemma lem5956672 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (p' : Prop) : term871 A B C op x s p'.
Proof. exact (@lem5956671 A B C op x s p'). Qed.
Lemma lem5956673 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (p' : Prop) : (term871 A B C op x s p') = (term872 A B C op x s p').
Proof. exact (eq_refl (term871 A B C op x s p')). Qed.
Lemma lem5956674 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (p' : Prop) : term872 A B C op x s p'.
Proof. exact (EQ_MP (@lem5956673 A B C op x s p') (@lem5956672 A B C op x s p')). Qed.
Lemma lem5956675 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term873 A B C op x s p' q'.
Proof. exact (@lem5956674 A B C op x s p' q'). Qed.
Lemma lem5956676 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term873 A B C op x s p' q') = (term874 A B C op x s p' q').
Proof. exact (eq_refl (term873 A B C op x s p' q')). Qed.
Lemma lem5956677 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term874 A B C op x s p' q'.
Proof. exact (EQ_MP (@lem5956676 A B C op x s p' q') (@lem5956675 A B C op x s p' q')). Qed.
Lemma lem5956821 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : (term666 A B C op x s) = (term666 A B C op x s).
Proof. exact (eq_refl (term666 A B C op x s)). Qed.
Lemma lem5956822 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (q' : Prop) : term875 A B C op x s q'.
Proof. exact (@lem5956677 A B C op x s (term666 A B C op x s) q'). Qed.
Lemma lem5956823 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (q' : Prop) : term876 A B C op x s q'.
Proof. exact (@lem5956822 A B C op x s q' (@lem5956821 A B C op x s)). Qed.
Lemma lem5956824 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : term666 A B C op x s.
Proof. exact (h1). Qed.
Lemma lem5956832 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : term649 A B C op s.
Proof. exact (proj1 (@lem5956824 A B C op x s h1)). Qed.
Lemma lem5956833 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : term640 A B C op s t.
Proof. exact (@lem5956832 A B C op x s h1 t). Qed.
Lemma lem5956834 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term640 A B C op s t) = (term641 A B C op s t).
Proof. exact (eq_refl (term640 A B C op s t)). Qed.
Lemma lem5956835 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : term641 A B C op s t.
Proof. exact (EQ_MP (@lem5956834 A B C op s t) (@lem5956833 A B C t op x s h1)). Qed.
Lemma lem5956836 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (h1 : term630 A B s t) : term630 A B s t.
Proof. exact (h1). Qed.
Lemma lem5956837 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term630 A B s t) (h2 : term666 A B C op x s) : term625 A B C op s t.
Proof. exact (@lem5956835 A B C t op x s h2 (@lem5956836 A B s t h1)). Qed.
Lemma lem5956838 {A B C : Type'} (x : type1412 A B C) (t : type1413 A B) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term630 A B s t) (h2 : term666 A B C op x' s) : term612 A B C op s t x.
Proof. exact (@lem5956837 A B C t op x' s h1 h2 x). Qed.
Lemma lem5956839 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x : type1412 A B C) : (term612 A B C op s t x) = ((term613 A B C s op t x) = (term614 A B C op s t x)).
Proof. exact (eq_refl (term612 A B C op s t x)). Qed.
Lemma lem5956840 {A B C : Type'} (x : type1412 A B C) (t : type1413 A B) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term630 A B s t) (h2 : term666 A B C op x' s) : (term613 A B C s op t x) = (term614 A B C op s t x).
Proof. exact (EQ_MP (@lem5956839 A B C op s t x) (@lem5956838 A B C x t op x' s h1 h2)). Qed.
Lemma lem5956853 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term706 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5956854 (p : Prop) (q : Prop) (p' : Prop) : term707 p q p'.
Proof. exact (fun q' : Prop => @lem5956853 p q p' q'). Qed.
Lemma lem5956855 (p : Prop) (q : Prop) : term708 p q.
Proof. exact (fun p' : Prop => @lem5956854 p q p'). Qed.
Lemma lem5956856 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : term877 A B C op x s t.
Proof. exact (@lem5956855 (term785 A B x s t) (term855 A B C op x s t)). Qed.
Lemma lem5956857 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) : term878 A B C op x s t p'.
Proof. exact (@lem5956856 A B C op x s t p'). Qed.
Lemma lem5956858 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) : (term878 A B C op x s t p') = (term879 A B C op x s t p').
Proof. exact (eq_refl (term878 A B C op x s t p')). Qed.
Lemma lem5956859 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) : term879 A B C op x s t p'.
Proof. exact (EQ_MP (@lem5956858 A B C op x s t p') (@lem5956857 A B C op x s t p')). Qed.
Lemma lem5956860 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) (q' : Prop) : term880 A B C op x s t p' q'.
Proof. exact (@lem5956859 A B C op x s t p' q'). Qed.
Lemma lem5956861 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) (q' : Prop) : (term880 A B C op x s t p' q') = (term881 A B C op x s t p' q').
Proof. exact (eq_refl (term880 A B C op x s t p' q')). Qed.
Lemma lem5956862 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) (q' : Prop) : term881 A B C op x s t p' q'.
Proof. exact (EQ_MP (@lem5956861 A B C op x s t p' q') (@lem5956860 A B C op x s t p' q')). Qed.
Lemma lem5956870 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term706 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5956871 (p : Prop) (q : Prop) (p' : Prop) : term707 p q p'.
Proof. exact (fun q' : Prop => @lem5956870 p q p' q'). Qed.
Lemma lem5956872 (p : Prop) (q : Prop) : term708 p q.
Proof. exact (fun p' : Prop => @lem5956871 p q p'). Qed.
Lemma lem5956873 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) : term882 A B x s t i.
Proof. exact (@lem5956872 (term84 A i x s) (term717 A B t i)). Qed.
Lemma lem5956874 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) : term883 A B x s t i p'.
Proof. exact (@lem5956873 A B x s t i p'). Qed.
Lemma lem5956875 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) : (term883 A B x s t i p') = (term884 A B x s t i p').
Proof. exact (eq_refl (term883 A B x s t i p')). Qed.
Lemma lem5956876 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) : term884 A B x s t i p'.
Proof. exact (EQ_MP (@lem5956875 A B x s t i p') (@lem5956874 A B x s t i p')). Qed.
Lemma lem5956877 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) (q' : Prop) : term885 A B x s t i p' q'.
Proof. exact (@lem5956876 A B x s t i p' q'). Qed.
Lemma lem5956878 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) (q' : Prop) : (term885 A B x s t i p' q') = (term886 A B x s t i p' q').
Proof. exact (eq_refl (term885 A B x s t i p' q')). Qed.
Lemma lem5956879 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) (q' : Prop) : term886 A B x s t i p' q'.
Proof. exact (EQ_MP (@lem5956878 A B x s t i p' q') (@lem5956877 A B x s t i p' q')). Qed.
Lemma lem5956881 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term84 A x y s) = (term85 A y x s).
Proof. exact (EQ_MP (@lem5956611 A y x s) (@lem5956610 A y x s)). Qed.
Lemma lem5956882 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term84 A x y s) = (term85 A y x s).
Proof. exact (@lem5956881 A y x s). Qed.
Lemma lem5956883 {A : Type'} (x : A) (i : A) (s : A -> Prop) : (term84 A i x s) = (term85 A x i s).
Proof. exact (@lem5956882 A x i s). Qed.
Lemma lem5956888 {A B : Type'} (t : type1413 A B) (x : A) (i : A) (s : A -> Prop) (q' : Prop) : term887 A B t x i s q'.
Proof. exact (@lem5956879 A B x s t i (term85 A x i s) q'). Qed.
Lemma lem5956889 {A B : Type'} (t : type1413 A B) (x : A) (i : A) (s : A -> Prop) (q' : Prop) : term888 A B t x i s q'.
Proof. exact (@lem5956888 A B t x i s q' (@lem5956883 A x i s)). Qed.
Lemma lem5956893 {A B : Type'} (t : type1413 A B) (i : A) : (term717 A B t i) = (term717 A B t i).
Proof. exact (eq_refl (term717 A B t i)). Qed.
Lemma lem5956894 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) : term889 A B x s t i.
Proof. exact (fun h0 : term85 A x i s => @lem5956893 A B t i). Qed.
Lemma lem5956895 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) : term890 A B x s t i.
Proof. exact (@lem5956889 A B t x i s (term717 A B t i)). Qed.
Lemma lem5956896 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) : (term891 A B x s t i) = (term892 A B x s t i).
Proof. exact (@lem5956895 A B x s t i (@lem5956894 A B x s t i)). Qed.
Lemma lem5956928 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term893 A B x s t) = (term894 A B x s t).
Proof. exact (fun_ext (fun i : A => @lem5956896 A B x s t i)). Qed.
Lemma lem5956960 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5956961 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term785 A B x s t) = (term895 A B x s t).
Proof. exact (MK_COMB (@lem5956960 A) (@lem5956928 A B x s t)). Qed.
Lemma lem5956997 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (q' : Prop) : term896 A B C op x s t q'.
Proof. exact (@lem5956862 A B C op x s t (term895 A B x s t) q'). Qed.
Lemma lem5956998 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (q' : Prop) : term897 A B C op x s t q'.
Proof. exact (@lem5956997 A B C op x s t q' (@lem5956961 A B x s t)). Qed.
Lemma lem5956999 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term895 A B x s t.
Proof. exact (h1). Qed.
Lemma lem5957000 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term898 A B x s t i.
Proof. exact (@lem5956999 A B x s t h1 i). Qed.
Lemma lem5957001 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) : (term898 A B x s t i) = (term892 A B x s t i).
Proof. exact (eq_refl (term898 A B x s t i)). Qed.
Lemma lem5957002 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term892 A B x s t i.
Proof. exact (EQ_MP (@lem5957001 A B x s t i) (@lem5957000 A B i x s t h1)). Qed.
Lemma lem5957003 {A : Type'} (x : A) (i : A) (s : A -> Prop) (h1 : term85 A x i s) : term85 A x i s.
Proof. exact (h1). Qed.
Lemma lem5957004 {A B : Type'} (t : type1413 A B) (x : A) (i : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term85 A x i s) : term717 A B t i.
Proof. exact (@lem5957002 A B i x s t h1 (@lem5957003 A x i s h2)). Qed.
Lemma lem5957005 {A B : Type'} (t : type1413 A B) (i : A) : (term717 A B t i) = ((term717 A B t i) = True).
Proof. exact (@lem7 (term717 A B t i)). Qed.
Lemma lem5957006 {A B : Type'} (t : type1413 A B) (x : A) (i : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term85 A x i s) : (term717 A B t i) = True.
Proof. exact (EQ_MP (@lem5957005 A B t i) (@lem5957004 A B t x i s h1 h2)). Qed.
Lemma lem5957019 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term666 A B C op x' s) : term899 A B C op s t x.
Proof. exact (fun h0 : term630 A B s t => @lem5956840 A B C x t op x' s h0 h1). Qed.
Lemma lem5957020 {A B C : Type'} (t : type1413 A B) (x : type1412 A B C) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term666 A B C op x' s) : term899 A B C op s t x.
Proof. exact (@lem5957019 A B C t x op x' s h1). Qed.
Lemma lem5957028 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term706 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5957029 (p : Prop) (q : Prop) (p' : Prop) : term707 p q p'.
Proof. exact (fun q' : Prop => @lem5957028 p q p' q'). Qed.
Lemma lem5957030 (p : Prop) (q : Prop) : term708 p q.
Proof. exact (fun p' : Prop => @lem5957029 p q p'). Qed.
Lemma lem5957031 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : term900 A B s t i.
Proof. exact (@lem5957030 (@IN A i s) (term717 A B t i)). Qed.
Lemma lem5957032 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) : term901 A B s t i p'.
Proof. exact (@lem5957031 A B s t i p'). Qed.
Lemma lem5957033 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) : (term901 A B s t i p') = (term902 A B s t i p').
Proof. exact (eq_refl (term901 A B s t i p')). Qed.
Lemma lem5957034 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) : term902 A B s t i p'.
Proof. exact (EQ_MP (@lem5957033 A B s t i p') (@lem5957032 A B s t i p')). Qed.
Lemma lem5957035 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) (q' : Prop) : term903 A B s t i p' q'.
Proof. exact (@lem5957034 A B s t i p' q'). Qed.
Lemma lem5957036 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) (q' : Prop) : (term903 A B s t i p' q') = (term904 A B s t i p' q').
Proof. exact (eq_refl (term903 A B s t i p' q')). Qed.
Lemma lem5957037 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) (q' : Prop) : term904 A B s t i p' q'.
Proof. exact (EQ_MP (@lem5957036 A B s t i p' q') (@lem5957035 A B s t i p' q')). Qed.
Lemma lem5957038 {A : Type'} (i : A) (s : A -> Prop) : (@IN A i s) = (@IN A i s).
Proof. exact (eq_refl (@IN A i s)). Qed.
Lemma lem5957039 {A B : Type'} (t : type1413 A B) (i : A) (s : A -> Prop) (q' : Prop) : term905 A B t i s q'.
Proof. exact (@lem5957037 A B s t i (@IN A i s) q'). Qed.
Lemma lem5957040 {A B : Type'} (t : type1413 A B) (i : A) (s : A -> Prop) (q' : Prop) : term906 A B t i s q'.
Proof. exact (@lem5957039 A B t i s q' (@lem5957038 A i s)). Qed.
Lemma lem5957041 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : @IN A i s.
Proof. exact (h1). Qed.
Lemma lem5957042 {A : Type'} (i : A) (s : A -> Prop) : (@IN A i s) = ((@IN A i s) = True).
Proof. exact (@lem7 (@IN A i s)). Qed.
Lemma lem5957045 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term907 A B x s t i.
Proof. exact (fun h0 : term85 A x i s => @lem5957006 A B t x i s h1 h0). Qed.
Lemma lem5957046 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term907 A B x s t i.
Proof. exact (@lem5957045 A B i x s t h1). Qed.
Lemma lem5957052 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : (@IN A i s) = True.
Proof. exact (EQ_MP (@lem5957042 A i s) (@lem5957041 A i s h1)). Qed.
Lemma lem5957053 {A : Type'} (i : A) (x : A) : (term86 A i x) = (term86 A i x).
Proof. exact (eq_refl (term86 A i x)). Qed.
Lemma lem5957054 {A : Type'} (x : A) (i : A) (s : A -> Prop) (h1 : @IN A i s) : (term85 A x i s) = (term908 A i x).
Proof. exact (MK_COMB (@lem5957053 A i x) (@lem5957052 A i s h1)). Qed.
Lemma lem5957056 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem5957057 {A : Type'} (i : A) (x : A) : (term908 A i x) = True.
Proof. exact (@lem5957056 (i = x)). Qed.
Lemma lem5957058 {A : Type'} (x : A) (i : A) (s : A -> Prop) (h1 : @IN A i s) : (term85 A x i s) = True.
Proof. exact (TRANS (@lem5957054 A x i s h1) (@lem5957057 A i x)). Qed.
Lemma lem5957059 {A : Type'} (x : A) (i : A) (s : A -> Prop) (h1 : @IN A i s) : True = (term85 A x i s).
Proof. exact (SYM (@lem5957058 A x i s h1)). Qed.
Lemma lem5957060 {A : Type'} (x : A) (i : A) (s : A -> Prop) (h1 : @IN A i s) : term85 A x i s.
Proof. exact (EQ_MP (@lem5957059 A x i s h1) (@lem0)). Qed.
Lemma lem5957061 {A B : Type'} (x : A) (t : type1413 A B) (i : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @IN A i s) : (term717 A B t i) = True.
Proof. exact (@lem5957046 A B i x s t h1 (@lem5957060 A x i s h2)). Qed.
Lemma lem5957062 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term909 A B s t i.
Proof. exact (fun h0 : @IN A i s => @lem5957061 A B x t i s h1 h0). Qed.
Lemma lem5957063 {A B : Type'} (t : type1413 A B) (i : A) (s : A -> Prop) : term910 A B t i s.
Proof. exact (@lem5957040 A B t i s True). Qed.
Lemma lem5957064 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : (term911 A B s t i) = (term912 A i s).
Proof. exact (@lem5957063 A B t i s (@lem5957062 A B i x s t h1)). Qed.
Lemma lem5957066 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5957067 {A : Type'} (i : A) (s : A -> Prop) : (term912 A i s) = True.
Proof. exact (@lem5957066 (@IN A i s)). Qed.
Lemma lem5957068 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : (term911 A B s t i) = True.
Proof. exact (TRANS (@lem5957064 A B i x s t h1) (@lem5957067 A i s)). Qed.
Lemma lem5957069 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : (term913 A B s t) = (term729 A).
Proof. exact (fun_ext (fun i : A => @lem5957068 A B i x s t h1)). Qed.
Lemma lem5957070 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5957071 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : (term630 A B s t) = (term730 A).
Proof. exact (MK_COMB (@lem5957070 A) (@lem5957069 A B x s t h1)). Qed.
Lemma lem5957073 {A : Type'} (t : Prop) : (term592 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5957074 {A : Type'} (t : Prop) : (term592 A t) = t.
Proof. exact (@lem5957073 A t). Qed.
Lemma lem5957075 {A : Type'} : (term730 A) = True.
Proof. exact (@lem5957074 A True). Qed.
Lemma lem5957076 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : (term630 A B s t) = True.
Proof. exact (TRANS (@lem5957071 A B x s t h1) (@lem5957075 A)). Qed.
Lemma lem5957077 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : True = (term630 A B s t).
Proof. exact (SYM (@lem5957076 A B x s t h1)). Qed.
Lemma lem5957078 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term630 A B s t.
Proof. exact (EQ_MP (@lem5957077 A B x s t h1) (@lem0)). Qed.
Lemma lem5957079 {A B C : Type'} (x : type1412 A B C) (t : type1413 A B) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term895 A B x' s t) (h2 : term666 A B C op x' s) : (term613 A B C s op t x) = (term614 A B C op s t x).
Proof. exact (@lem5957020 A B C t x op x' s h2 (@lem5957078 A B x' s t h1)). Qed.
Lemma lem5957098 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (x' : A) : (term823 A B C op t x x') = (term823 A B C op t x x').
Proof. exact (eq_refl (term823 A B C op t x x')). Qed.
Lemma lem5957099 {A B C : Type'} (x : type1412 A B C) (t : type1413 A B) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term895 A B x' s t) (h2 : term666 A B C op x' s) : (term824 A B C x' s op t x) = (term914 A B C x' op s t x).
Proof. exact (MK_COMB (@lem5957098 A B C op t x x') (@lem5957079 A B C x t op x' s h1 h2)). Qed.
Lemma lem5957118 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem5957119 {A B C : Type'} (x : type1412 A B C) (t : type1413 A B) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term895 A B x' s t) (h2 : term666 A B C op x' s) : (term829 A B C x' s op t x) = (term915 A B C x' op s t x).
Proof. exact (MK_COMB (@lem5957118 C) (@lem5957099 A B C x t op x' s h1 h2)). Qed.
Lemma lem5957156 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : (term853 A B C op x s t x') = (term853 A B C op x s t x').
Proof. exact (eq_refl (term853 A B C op x s t x')). Qed.
Lemma lem5957157 {A B C : Type'} (x : type1412 A B C) (t : type1413 A B) (op : type1400 C) (x' : A) (s : A -> Prop) (h1 : term895 A B x' s t) (h2 : term666 A B C op x' s) : ((term824 A B C x' s op t x) = (term853 A B C op x' s t x)) = ((term914 A B C x' op s t x) = (term853 A B C op x' s t x)).
Proof. exact (MK_COMB (@lem5957119 A B C x t op x' s h1 h2) (@lem5957156 A B C op x' s t x)). Qed.
Lemma lem5957196 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term666 A B C op x s) : (term854 A B C op x s t) = (term916 A B C op x s t).
Proof. exact (fun_ext (fun x' : type1412 A B C => @lem5957157 A B C x' t op x s h1 h2)). Qed.
Lemma lem5957235 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5957236 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term666 A B C op x s) : (term855 A B C op x s t) = (term917 A B C op x s t).
Proof. exact (MK_COMB (@lem5957235 A B C) (@lem5957196 A B C t op x s h1 h2)). Qed.
Lemma lem5957279 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : term918 A B C op x s t.
Proof. exact (fun h0 : term895 A B x s t => @lem5957236 A B C t op x s h0 h1). Qed.
Lemma lem5957280 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : term919 A B C op x s t.
Proof. exact (@lem5956998 A B C op x s t (term917 A B C op x s t)). Qed.
Lemma lem5957281 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : (term857 A B C op x s t) = (term920 A B C op x s t).
Proof. exact (@lem5957280 A B C op x s t (@lem5957279 A B C t op x s h1)). Qed.
Lemma lem5957469 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : (term858 A B C op x s) = (term921 A B C op x s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5957281 A B C t op x s h1)). Qed.
Lemma lem5957657 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5957658 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : (term859 A B C op x s) = (term922 A B C op x s).
Proof. exact (MK_COMB (@lem5957657 A B) (@lem5957469 A B C op x s h1)). Qed.
Lemma lem5957850 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : term923 A B C op x s.
Proof. exact (fun h0 : term666 A B C op x s => @lem5957658 A B C op x s h0). Qed.
Lemma lem5957851 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : term924 A B C op x s.
Proof. exact (@lem5956823 A B C op x s (term922 A B C op x s)). Qed.
Lemma lem5957852 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) : (term860 A B C op x s) = (term925 A B C op x s).
Proof. exact (@lem5957851 A B C op x s (@lem5957850 A B C op x s)). Qed.
Lemma lem5958563 {A B C : Type'} (op : type1400 C) (x : A) : (term861 A B C op x) = (term926 A B C op x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5957852 A B C op x s)). Qed.
Lemma lem5959274 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5959275 {A B C : Type'} (op : type1400 C) (x : A) : (term862 A B C op x) = (term927 A B C op x).
Proof. exact (MK_COMB (@lem5959274 A) (@lem5958563 A B C op x)). Qed.
Lemma lem5959990 {A B C : Type'} (op : type1400 C) : (term863 A B C op) = (term928 A B C op).
Proof. exact (fun_ext (fun x : A => @lem5959275 A B C op x)). Qed.
Lemma lem5960705 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5960706 {A B C : Type'} (op : type1400 C) : (term864 A B C op) = (term929 A B C op).
Proof. exact (MK_COMB (@lem5960705 A) (@lem5959990 A B C op)). Qed.
Lemma lem5961425 {A B C : Type'} (op : type1400 C) : (term929 A B C op) = (term864 A B C op).
Proof. exact (SYM (@lem5960706 A B C op)). Qed.
Lemma lem5961426 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : term666 A B C op x s.
Proof. exact (h1). Qed.
Lemma lem5961427 {A : Type'} (x : A) (s : A -> Prop) (h1 : term664 A x s) : term664 A x s.
Proof. exact (h1). Qed.
Lemma lem5961428 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (h1 : term649 A B C op s) : term649 A B C op s.
Proof. exact (h1). Qed.
Lemma lem5961429 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5961430 {A : Type'} (x : A) (s : A -> Prop) (h1 : term782 A x s) : term782 A x s.
Proof. exact (h1). Qed.
Lemma lem5961431 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term895 A B x s t.
Proof. exact (h1). Qed.
Lemma lem5961452 {_120592 _120607 : Type'} (op : type1400 _120607) : term930 _120592 _120607 op.
Proof. exact (@lem5764203 _120592 _120607 op). Qed.
Lemma lem5961453 {_120592 _120607 : Type'} (op : type1400 _120607) : (term930 _120592 _120607 op) = (term931 _120592 _120607 op).
Proof. exact (eq_refl (term930 _120592 _120607 op)). Qed.
Lemma lem5961456 {_120592 _120607 : Type'} (op : type1400 _120607) : term931 _120592 _120607 op.
Proof. exact (EQ_MP (@lem5961453 _120592 _120607 op) (@lem5961452 _120592 _120607 op)). Qed.
Lemma lem5961457 {_120592 C : Type'} (op : type1400 C) : term931 _120592 C op.
Proof. exact (@lem5961456 _120592 C op). Qed.
Lemma lem5961458 {_120592 C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term932 _120592 C op.
Proof. exact (@lem5961457 _120592 C op (@lem5950451 C op h1)). Qed.
Lemma lem5961459 {_120592 C : Type'} (f : _120592 -> C) (op : type1400 C) (h1 : @monoidal C op) : term933 _120592 C op f.
Proof. exact (@lem5961458 _120592 C op h1 f). Qed.
Lemma lem5961460 {_120592 C : Type'} (op : type1400 C) (f : _120592 -> C) : (term933 _120592 C op f) = (term934 _120592 C op f).
Proof. exact (eq_refl (term933 _120592 C op f)). Qed.
Lemma lem5961461 {_120592 C : Type'} (f : _120592 -> C) (op : type1400 C) (h1 : @monoidal C op) : term934 _120592 C op f.
Proof. exact (EQ_MP (@lem5961460 _120592 C op f) (@lem5961459 _120592 C f op h1)). Qed.
Lemma lem5961462 {_120592 C : Type'} (f : _120592 -> C) (s : _120592 -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term935 _120592 C op f s.
Proof. exact (@lem5961461 _120592 C f op h1 s). Qed.
Lemma lem5961463 {_120592 C : Type'} (s : _120592 -> Prop) (op : type1400 C) (f : _120592 -> C) : (term935 _120592 C op f s) = (term936 _120592 C s op f).
Proof. exact (eq_refl (term935 _120592 C op f s)). Qed.
Lemma lem5961464 {_120592 C : Type'} (s : _120592 -> Prop) (f : _120592 -> C) (op : type1400 C) (h1 : @monoidal C op) : term936 _120592 C s op f.
Proof. exact (EQ_MP (@lem5961463 _120592 C s op f) (@lem5961462 _120592 C f s op h1)). Qed.
Lemma lem5961465 {_120592 C : Type'} (s : _120592 -> Prop) (f : _120592 -> C) (t : _120592 -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term937 _120592 C s op f t.
Proof. exact (@lem5961464 _120592 C s f op h1 t). Qed.
Lemma lem5961466 {_120592 C : Type'} (s : _120592 -> Prop) (op : type1400 C) (t : _120592 -> Prop) (f : _120592 -> C) : (term937 _120592 C s op f t) = (term938 _120592 C s op t f).
Proof. exact (eq_refl (term937 _120592 C s op f t)). Qed.
Lemma lem5961469 {_120592 C : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> C) (op : type1400 C) (h1 : @monoidal C op) : term938 _120592 C s op t f.
Proof. exact (EQ_MP (@lem5961466 _120592 C s op t f) (@lem5961465 _120592 C s f t op h1)). Qed.
Lemma lem5961470 {A B C : Type'} (s : type1210 A B) (t : type1210 A B) (f : type1209 A B C) (op : type1400 C) (h1 : @monoidal C op) : term939 A B C s op t f.
Proof. exact (@lem5961469 (prod A B) C s t f op h1). Qed.
Lemma lem5961471 {A B C : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term940 A B C x op s t x'.
Proof. exact (@lem5961470 A B C (term941 A B t x) (term942 A B s t) (term759 A B C x') op h1). Qed.
Lemma lem5961473 (p : Prop) (q : Prop) (r : Prop) : term943 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem5961474 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : term944 A B C op x s t x'.
Proof. exact (@lem5961473 (term945 A B x s t) ((term853 A B C op x s t x') = (term946 A B C x op s t x')) ((term914 A B C x op s t x') = (term853 A B C op x s t x'))). Qed.
Lemma lem5961484 {A B C : Type'} (f : type1412 A B C) : term947 A B C f.
Proof. exact (@lem4323219 A B C f). Qed.
Lemma lem5961485 {A B C : Type'} (f : type1412 A B C) : (term947 A B C f) = (term948 A B C f).
Proof. exact (eq_refl (term947 A B C f)). Qed.
Lemma lem5961486 {A B C : Type'} (f : type1412 A B C) : term948 A B C f.
Proof. exact (EQ_MP (@lem5961485 A B C f) (@lem5961484 A B C f)). Qed.
Lemma lem5961487 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) : term949 A B C f s.
Proof. exact (@lem5961486 A B C f s). Qed.
Lemma lem5961488 {A B C : Type'} (s : A -> Prop) (f : type1412 A B C) : (term949 A B C f s) = (term950 A B C s f).
Proof. exact (eq_refl (term949 A B C f s)). Qed.
Lemma lem5961489 {A B C : Type'} (s : A -> Prop) (f : type1412 A B C) : term950 A B C s f.
Proof. exact (EQ_MP (@lem5961488 A B C s f) (@lem5961487 A B C f s)). Qed.
Lemma lem5961490 {A B C : Type'} (s : A -> Prop) (f : type1412 A B C) (t : type1413 A B) : term951 A B C s f t.
Proof. exact (@lem5961489 A B C s f t). Qed.
Lemma lem5961491 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term951 A B C s f t) = (term952 A B C s t f).
Proof. exact (eq_refl (term951 A B C s f t)). Qed.
Lemma lem5961492 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : term952 A B C s t f.
Proof. exact (EQ_MP (@lem5961491 A B C s t f) (@lem5961490 A B C s f t)). Qed.
Lemma lem5961493 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (h1 : term610 A B s t) : term610 A B s t.
Proof. exact (h1). Qed.
Lemma lem5961494 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term610 A B s t) : term953 A B C s t f.
Proof. exact (@lem5961492 A B C s t f (@lem5961493 A B s t h1)). Qed.
Lemma lem5961495 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term953 A B C s t f) = ((term953 A B C s t f) = True).
Proof. exact (@lem7 (term953 A B C s t f)). Qed.
Lemma lem5961496 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term610 A B s t) : (term953 A B C s t f) = True.
Proof. exact (EQ_MP (@lem5961495 A B C s t f) (@lem5961494 A B C f s t h1)). Qed.
Lemma lem5961502 {A B : Type'} (f : A -> B) : term954 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem5961503 {A B : Type'} (f : A -> B) : (term954 A B f) = (term955 A B f).
Proof. exact (eq_refl (term954 A B f)). Qed.
Lemma lem5961504 {A B : Type'} (f : A -> B) : term955 A B f.
Proof. exact (EQ_MP (@lem5961503 A B f) (@lem5961502 A B f)). Qed.
Lemma lem5961505 {A B : Type'} (f : A -> B) (s : A -> Prop) : term956 A B f s.
Proof. exact (@lem5961504 A B f s). Qed.
Lemma lem5961506 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term956 A B f s) = (term957 A B f s).
Proof. exact (eq_refl (term956 A B f s)). Qed.
Lemma lem5961507 {A B : Type'} (f : A -> B) (s : A -> Prop) : term957 A B f s.
Proof. exact (EQ_MP (@lem5961506 A B f s) (@lem5961505 A B f s)). Qed.
Lemma lem5961508 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5961509 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term958 A B f s.
Proof. exact (@lem5961507 A B f s (@lem5961508 A s h1)). Qed.
Lemma lem5961510 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term958 A B f s) = ((term958 A B f s) = True).
Proof. exact (@lem7 (term958 A B f s)). Qed.
Lemma lem5961511 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term958 A B f s) = True.
Proof. exact (EQ_MP (@lem5961510 A B f s) (@lem5961509 A B f s h1)). Qed.
Lemma lem5961532 {A : Type'} (x : A) (s : A -> Prop) : term783 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem5961534 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem5961536 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term898 A B x s t i.
Proof. exact (@lem5961431 A B x s t h1 i). Qed.
Lemma lem5961537 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) : (term898 A B x s t i) = (term892 A B x s t i).
Proof. exact (eq_refl (term898 A B x s t i)). Qed.
Lemma lem5961538 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term892 A B x s t i.
Proof. exact (EQ_MP (@lem5961537 A B x s t i) (@lem5961536 A B i x s t h1)). Qed.
Lemma lem5961539 {A : Type'} (x : A) (i : A) (s : A -> Prop) (h1 : term85 A x i s) : term85 A x i s.
Proof. exact (h1). Qed.
Lemma lem5961540 {A B : Type'} (t : type1413 A B) (x : A) (i : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term85 A x i s) : term717 A B t i.
Proof. exact (@lem5961538 A B i x s t h1 (@lem5961539 A x i s h2)). Qed.
Lemma lem5961541 {A B : Type'} (t : type1413 A B) (i : A) : (term717 A B t i) = ((term717 A B t i) = True).
Proof. exact (@lem7 (term717 A B t i)). Qed.
Lemma lem5961542 {A B : Type'} (t : type1413 A B) (x : A) (i : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term85 A x i s) : (term717 A B t i) = True.
Proof. exact (EQ_MP (@lem5961541 A B t i) (@lem5961540 A B t x i s h1 h2)). Qed.
Lemma lem5961551 {A B : Type'} (f : A -> B) (s : A -> Prop) : term959 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem5961511 A B f s h0). Qed.
Lemma lem5961552 {A B : Type'} (f : type1478 A B) (s : B -> Prop) : term960 A B f s.
Proof. exact (@lem5961551 B (prod A B) f s). Qed.
Lemma lem5961553 {A B : Type'} (t : type1413 A B) (x : A) : term961 A B t x.
Proof. exact (@lem5961552 A B (term962 A B x) (t x)). Qed.
Lemma lem5961555 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term907 A B x s t i.
Proof. exact (fun h0 : term85 A x i s => @lem5961542 A B t x i s h1 h0). Qed.
Lemma lem5961556 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term907 A B x s t i.
Proof. exact (@lem5961555 A B i x s t h1). Qed.
Lemma lem5961557 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term963 A B s t x.
Proof. exact (@lem5961556 A B x x s t h1). Qed.
Lemma lem5961561 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5961562 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem5961561 A x). Qed.
Lemma lem5961563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5961564 {A : Type'} (x : A) : (term964 A x) = (or True).
Proof. exact (MK_COMB (@lem5961563) (@lem5961562 A x)). Qed.
Lemma lem5961566 {A : Type'} (x : A) (s : A -> Prop) (h1 : term782 A x s) : (@IN A x s) = False.
Proof. exact (@lem5961532 A x s (@lem5961430 A x s h1)). Qed.
Lemma lem5961567 {A : Type'} (x : A) (s : A -> Prop) (h1 : term782 A x s) : (term965 A x s) = (True \/ False).
Proof. exact (MK_COMB (@lem5961564 A x) (@lem5961566 A x s h1)). Qed.
Lemma lem5961569 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem5961570 : (True \/ False) = True.
Proof. exact (@lem5961569 False). Qed.
Lemma lem5961571 {A : Type'} (x : A) (s : A -> Prop) (h1 : term782 A x s) : (term965 A x s) = True.
Proof. exact (TRANS (@lem5961567 A x s h1) (@lem5961570)). Qed.
Lemma lem5961572 {A : Type'} (x : A) (s : A -> Prop) (h1 : term782 A x s) : True = (term965 A x s).
Proof. exact (SYM (@lem5961571 A x s h1)). Qed.
Lemma lem5961573 {A : Type'} (x : A) (s : A -> Prop) (h1 : term782 A x s) : term965 A x s.
Proof. exact (EQ_MP (@lem5961572 A x s h1) (@lem0)). Qed.
Lemma lem5961574 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term782 A x s) : (term717 A B t x) = True.
Proof. exact (@lem5961557 A B x s t h1 (@lem5961573 A x s h2)). Qed.
Lemma lem5961575 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term782 A x s) : True = (term717 A B t x).
Proof. exact (SYM (@lem5961574 A B t x s h1 h2)). Qed.
Lemma lem5961576 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term782 A x s) : term717 A B t x.
Proof. exact (EQ_MP (@lem5961575 A B t x s h1 h2) (@lem0)). Qed.
Lemma lem5961577 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term782 A x s) : (term966 A B t x) = True.
Proof. exact (@lem5961553 A B t x (@lem5961576 A B t x s h1 h2)). Qed.
Lemma lem5961578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5961579 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term782 A x s) : (term967 A B t x) = (and True).
Proof. exact (MK_COMB (@lem5961578) (@lem5961577 A B t x s h1 h2)). Qed.
Lemma lem5961583 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : term968 A B C s t f.
Proof. exact (fun h0 : term610 A B s t => @lem5961496 A B C f s t h0). Qed.
Lemma lem5961584 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1409 A B) : term969 A B s t f.
Proof. exact (@lem5961583 A B (prod A B) s t f). Qed.
Lemma lem5961585 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : term970 A B s t.
Proof. exact (@lem5961584 A B s t (@pair A B)). Qed.
Lemma lem5961589 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem5961534 A s) (@lem5961429 A s h1)). Qed.
Lemma lem5961590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5961591 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term795 A s) = (and True).
Proof. exact (MK_COMB (@lem5961590) (@lem5961589 A s h1)). Qed.
Lemma lem5961599 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term706 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5961600 (p : Prop) (q : Prop) (p' : Prop) : term707 p q p'.
Proof. exact (fun q' : Prop => @lem5961599 p q p' q'). Qed.
Lemma lem5961601 (p : Prop) (q : Prop) : term708 p q.
Proof. exact (fun p' : Prop => @lem5961600 p q p'). Qed.
Lemma lem5961602 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : term900 A B s t i.
Proof. exact (@lem5961601 (@IN A i s) (term717 A B t i)). Qed.
Lemma lem5961603 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) : term901 A B s t i p'.
Proof. exact (@lem5961602 A B s t i p'). Qed.
Lemma lem5961604 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) : (term901 A B s t i p') = (term902 A B s t i p').
Proof. exact (eq_refl (term901 A B s t i p')). Qed.
Lemma lem5961605 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) : term902 A B s t i p'.
Proof. exact (EQ_MP (@lem5961604 A B s t i p') (@lem5961603 A B s t i p')). Qed.
Lemma lem5961606 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) (q' : Prop) : term903 A B s t i p' q'.
Proof. exact (@lem5961605 A B s t i p' q'). Qed.
Lemma lem5961607 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) (q' : Prop) : (term903 A B s t i p' q') = (term904 A B s t i p' q').
Proof. exact (eq_refl (term903 A B s t i p' q')). Qed.
Lemma lem5961608 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) (p' : Prop) (q' : Prop) : term904 A B s t i p' q'.
Proof. exact (EQ_MP (@lem5961607 A B s t i p' q') (@lem5961606 A B s t i p' q')). Qed.
Lemma lem5961609 {A : Type'} (i : A) (s : A -> Prop) : (@IN A i s) = (@IN A i s).
Proof. exact (eq_refl (@IN A i s)). Qed.
Lemma lem5961610 {A B : Type'} (t : type1413 A B) (i : A) (s : A -> Prop) (q' : Prop) : term905 A B t i s q'.
Proof. exact (@lem5961608 A B s t i (@IN A i s) q'). Qed.
Lemma lem5961611 {A B : Type'} (t : type1413 A B) (i : A) (s : A -> Prop) (q' : Prop) : term906 A B t i s q'.
Proof. exact (@lem5961610 A B t i s q' (@lem5961609 A i s)). Qed.
Lemma lem5961612 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : @IN A i s.
Proof. exact (h1). Qed.
Lemma lem5961613 {A : Type'} (i : A) (s : A -> Prop) : (@IN A i s) = ((@IN A i s) = True).
Proof. exact (@lem7 (@IN A i s)). Qed.
Lemma lem5961616 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term907 A B x s t i.
Proof. exact (fun h0 : term85 A x i s => @lem5961542 A B t x i s h1 h0). Qed.
Lemma lem5961617 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term907 A B x s t i.
Proof. exact (@lem5961616 A B i x s t h1). Qed.
Lemma lem5961623 {A : Type'} (i : A) (s : A -> Prop) (h1 : @IN A i s) : (@IN A i s) = True.
Proof. exact (EQ_MP (@lem5961613 A i s) (@lem5961612 A i s h1)). Qed.
Lemma lem5961624 {A : Type'} (i : A) (x : A) : (term86 A i x) = (term86 A i x).
Proof. exact (eq_refl (term86 A i x)). Qed.
Lemma lem5961625 {A : Type'} (x : A) (i : A) (s : A -> Prop) (h1 : @IN A i s) : (term85 A x i s) = (term908 A i x).
Proof. exact (MK_COMB (@lem5961624 A i x) (@lem5961623 A i s h1)). Qed.
Lemma lem5961627 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem5961628 {A : Type'} (i : A) (x : A) : (term908 A i x) = True.
Proof. exact (@lem5961627 (i = x)). Qed.
Lemma lem5961629 {A : Type'} (x : A) (i : A) (s : A -> Prop) (h1 : @IN A i s) : (term85 A x i s) = True.
Proof. exact (TRANS (@lem5961625 A x i s h1) (@lem5961628 A i x)). Qed.
Lemma lem5961630 {A : Type'} (x : A) (i : A) (s : A -> Prop) (h1 : @IN A i s) : True = (term85 A x i s).
Proof. exact (SYM (@lem5961629 A x i s h1)). Qed.
Lemma lem5961631 {A : Type'} (x : A) (i : A) (s : A -> Prop) (h1 : @IN A i s) : term85 A x i s.
Proof. exact (EQ_MP (@lem5961630 A x i s h1) (@lem0)). Qed.
Lemma lem5961632 {A B : Type'} (x : A) (t : type1413 A B) (i : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @IN A i s) : (term717 A B t i) = True.
Proof. exact (@lem5961617 A B i x s t h1 (@lem5961631 A x i s h2)). Qed.
Lemma lem5961633 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : term909 A B s t i.
Proof. exact (fun h0 : @IN A i s => @lem5961632 A B x t i s h1 h0). Qed.
Lemma lem5961634 {A B : Type'} (t : type1413 A B) (i : A) (s : A -> Prop) : term910 A B t i s.
Proof. exact (@lem5961611 A B t i s True). Qed.
Lemma lem5961635 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : (term911 A B s t i) = (term912 A i s).
Proof. exact (@lem5961634 A B t i s (@lem5961633 A B i x s t h1)). Qed.
Lemma lem5961637 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5961638 {A : Type'} (i : A) (s : A -> Prop) : (term912 A i s) = True.
Proof. exact (@lem5961637 (@IN A i s)). Qed.
Lemma lem5961639 {A B : Type'} (i : A) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : (term911 A B s t i) = True.
Proof. exact (TRANS (@lem5961635 A B i x s t h1) (@lem5961638 A i s)). Qed.
Lemma lem5961640 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : (term913 A B s t) = (term729 A).
Proof. exact (fun_ext (fun i : A => @lem5961639 A B i x s t h1)). Qed.
Lemma lem5961641 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5961642 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : (term630 A B s t) = (term730 A).
Proof. exact (MK_COMB (@lem5961641 A) (@lem5961640 A B x s t h1)). Qed.
Lemma lem5961644 {A : Type'} (t : Prop) : (term592 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5961645 {A : Type'} (t : Prop) : (term592 A t) = t.
Proof. exact (@lem5961644 A t). Qed.
Lemma lem5961646 {A : Type'} : (term730 A) = True.
Proof. exact (@lem5961645 A True). Qed.
Lemma lem5961647 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term895 A B x s t) : (term630 A B s t) = True.
Proof. exact (TRANS (@lem5961642 A B x s t h1) (@lem5961646 A)). Qed.
Lemma lem5961648 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @FINITE A s) : (term610 A B s t) = (True /\ True).
Proof. exact (MK_COMB (@lem5961591 A s h2) (@lem5961647 A B x s t h1)). Qed.
Lemma lem5961650 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5961651 : (True /\ True) = True.
Proof. exact (@lem5961650 True). Qed.
Lemma lem5961652 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @FINITE A s) : (term610 A B s t) = True.
Proof. exact (TRANS (@lem5961648 A B x t s h1 h2) (@lem5961651)). Qed.
Lemma lem5961653 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @FINITE A s) : True = (term610 A B s t).
Proof. exact (SYM (@lem5961652 A B x t s h1 h2)). Qed.
Lemma lem5961654 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @FINITE A s) : term610 A B s t.
Proof. exact (EQ_MP (@lem5961653 A B x t s h1 h2) (@lem0)). Qed.
Lemma lem5961655 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @FINITE A s) : (term971 A B s t) = True.
Proof. exact (@lem5961585 A B s t (@lem5961654 A B x t s h1 h2)). Qed.
Lemma lem5961656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5961657 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @FINITE A s) : (term972 A B s t) = (and True).
Proof. exact (MK_COMB (@lem5961656) (@lem5961655 A B x t s h1 h2)). Qed.
Lemma lem5961668 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term973 A B x s t) = (term973 A B x s t).
Proof. exact (eq_refl (term973 A B x s t)). Qed.
Lemma lem5961669 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @FINITE A s) : (term974 A B x s t) = (term975 A B x s t).
Proof. exact (MK_COMB (@lem5961657 A B x t s h1 h2) (@lem5961668 A B x s t)). Qed.
Lemma lem5961671 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5961672 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term975 A B x s t) = (term973 A B x s t).
Proof. exact (@lem5961671 (term973 A B x s t)). Qed.
Lemma lem5961683 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @FINITE A s) : (term974 A B x s t) = (term973 A B x s t).
Proof. exact (TRANS (@lem5961669 A B x t s h1 h2) (@lem5961672 A B x s t)). Qed.
Lemma lem5961684 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @FINITE A s) (h3 : term782 A x s) : (term945 A B x s t) = (term975 A B x s t).
Proof. exact (MK_COMB (@lem5961579 A B t x s h1 h3) (@lem5961683 A B x t s h1 h2)). Qed.
Lemma lem5961686 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5961687 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term975 A B x s t) = (term973 A B x s t).
Proof. exact (@lem5961686 (term973 A B x s t)). Qed.
Lemma lem5961698 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @FINITE A s) (h3 : term782 A x s) : (term945 A B x s t) = (term973 A B x s t).
Proof. exact (TRANS (@lem5961684 A B t x s h1 h2 h3) (@lem5961687 A B x s t)). Qed.
Lemma lem5961699 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : @FINITE A s) (h3 : term782 A x s) : (term973 A B x s t) = (term945 A B x s t).
Proof. exact (SYM (@lem5961698 A B t x s h1 h2 h3)). Qed.
Lemma lem5961701 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem5947471 A s t) (@lem5947470 A s t)). Qed.
Lemma lem5961702 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (@DISJOINT (prod A B) s t) = ((@INTER (prod A B) s t) = (@EMPTY (prod A B))).
Proof. exact (@lem5961701 (prod A B) s t). Qed.
Lemma lem5961703 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term973 A B x s t) = ((term976 A B x s t) = (@EMPTY (prod A B))).
Proof. exact (@lem5961702 A B (term941 A B t x) (term942 A B s t)). Qed.
Lemma lem5961707 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term43 A s t).
Proof. exact (EQ_MP (@lem5947465 A s t) (@lem5947464 A s t)). Qed.
Lemma lem5961708 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (s = t) = (term977 A B s t).
Proof. exact (@lem5961707 (prod A B) s t). Qed.
Lemma lem5961709 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : ((term976 A B x s t) = (@EMPTY (prod A B))) = (term978 A B x s t).
Proof. exact (@lem5961708 A B (term976 A B x s t) (@EMPTY (prod A B))). Qed.
Lemma lem5961715 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term15 _5106 _5107 P) = (term16 _5106 _5107 P).
Proof. exact (EQ_MP (@lem5947395 _5106 _5107 P) (@lem5947394 _5106 _5107 P)). Qed.
Lemma lem5961716 {A B : Type'} (P : type1210 A B) : (term979 A B P) = (term980 A B P).
Proof. exact (@lem5961715 B A P). Qed.
Lemma lem5961717 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term981 A B x s t) = (term982 A B x s t).
Proof. exact (@lem5961716 A B (term983 A B x s t)). Qed.
Lemma lem5961718 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term984 A B x s t x') = ((term985 A B x' x s t) = (@IN (prod A B) x' (@EMPTY (prod A B)))).
Proof. exact (eq_refl (term984 A B x s t x')). Qed.
Lemma lem5961719 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term986 A B x s t) = (term983 A B x s t).
Proof. exact (fun_ext (fun x' : prod A B => @lem5961718 A B x s t x')). Qed.
Lemma lem5961720 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5961721 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term981 A B x s t) = (term978 A B x s t).
Proof. exact (MK_COMB (@lem5961720 A B) (@lem5961719 A B x s t)). Qed.
Lemma lem5961722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5961723 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term987 A B x s t) = (term988 A B x s t).
Proof. exact (MK_COMB (@lem5961722) (@lem5961721 A B x s t)). Qed.
Lemma lem5961724 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term989 A B x s t p1 p2) = ((term990 A B p1 p2 x s t) = (term991 A B p1 p2)).
Proof. exact (eq_refl (term989 A B x s t p1 p2)). Qed.
Lemma lem5961725 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term992 A B x s t p1) = (term993 A B x s t p1).
Proof. exact (fun_ext (fun p2 : B => @lem5961724 A B x s t p1 p2)). Qed.
Lemma lem5961726 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5961727 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term994 A B x s t p1) = (term995 A B x s t p1).
Proof. exact (MK_COMB (@lem5961726 B) (@lem5961725 A B x s t p1)). Qed.
Lemma lem5961728 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term996 A B x s t) = (term997 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem5961727 A B x s t p1)). Qed.
Lemma lem5961729 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5961730 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term982 A B x s t) = (term998 A B x s t).
Proof. exact (MK_COMB (@lem5961729 A) (@lem5961728 A B x s t)). Qed.
Lemma lem5961731 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : ((term981 A B x s t) = (term982 A B x s t)) = ((term978 A B x s t) = (term998 A B x s t)).
Proof. exact (MK_COMB (@lem5961723 A B x s t) (@lem5961730 A B x s t)). Qed.
Lemma lem5961732 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term978 A B x s t) = (term998 A B x s t).
Proof. exact (EQ_MP (@lem5961731 A B x s t) (@lem5961717 A B x s t)). Qed.
Lemma lem5961739 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : ((term976 A B x s t) = (@EMPTY (prod A B))) = (term998 A B x s t).
Proof. exact (TRANS (@lem5961709 A B x s t) (@lem5961732 A B x s t)). Qed.
Lemma lem5961740 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term973 A B x s t) = (term998 A B x s t).
Proof. exact (TRANS (@lem5961703 A B x s t) (@lem5961739 A B x s t)). Qed.
Lemma lem5961752 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term31 A x s t) = (term32 A s x t).
Proof. exact (EQ_MP (@lem5947450 A s x t) (@lem5947449 A s t x)). Qed.
Lemma lem5961753 {A B : Type'} (s : type1210 A B) (x : prod A B) (t : type1210 A B) : (term999 A B x s t) = (term1000 A B s x t).
Proof. exact (@lem5961752 (prod A B) s x t). Qed.
Lemma lem5961754 {A B : Type'} (x : A) (p1 : A) (p2 : B) (s : A -> Prop) (t : type1413 A B) : (term990 A B p1 p2 x s t) = (term1001 A B x p1 p2 s t).
Proof. exact (@lem5961753 A B (term941 A B t x) (@pair A B p1 p2) (term942 A B s t)). Qed.
Lemma lem5961758 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term38 A B y f s) = (term39 A B y f s).
Proof. exact (EQ_MP (@lem5947459 A B y f s) (@lem5947458 A B y s f)). Qed.
Lemma lem5961759 {A B : Type'} (y : prod A B) (f : type1478 A B) (s : B -> Prop) : (term1002 A B y f s) = (term1003 A B y f s).
Proof. exact (@lem5961758 B (prod A B) y f s). Qed.
Lemma lem5961760 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1004 A B p1 p2 t x) = (term1005 A B p1 p2 t x).
Proof. exact (@lem5961759 A B (@pair A B p1 p2) (term962 A B x) (t x)). Qed.
Lemma lem5961774 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5961775 {A B : Type'} (f : type1478 A B) (y : B) : (term1006 A B f y) = (f y).
Proof. exact (@lem5961774 B (prod A B) f y). Qed.
Lemma lem5961776 {A B : Type'} (x : A) (x' : B) : (term1007 A B x x') = (term1008 A B x x').
Proof. exact (@lem5961775 A B (term962 A B x) x'). Qed.
Lemma lem5961777 {A B : Type'} (x : A) (j : B) : (term1008 A B x j) = (@pair A B x j).
Proof. exact (eq_refl (term1008 A B x j)). Qed.
Lemma lem5961778 {A B : Type'} (x : A) : (term1009 A B x) = (term962 A B x).
Proof. exact (fun_ext (fun j : B => @lem5961777 A B x j)). Qed.
Lemma lem5961779 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5961780 {A B : Type'} (x : A) (x' : B) : (term1007 A B x x') = (term1008 A B x x').
Proof. exact (MK_COMB (@lem5961778 A B x) (@lem5961779 B x')). Qed.
Lemma lem5961781 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem5961782 {A B : Type'} (x : A) (x' : B) : (term1010 A B x x') = (term1011 A B x x').
Proof. exact (MK_COMB (@lem5961781 A B) (@lem5961780 A B x x')). Qed.
Lemma lem5961783 {A B : Type'} (x : A) (x' : B) : (term1008 A B x x') = (@pair A B x x').
Proof. exact (eq_refl (term1008 A B x x')). Qed.
Lemma lem5961784 {A B : Type'} (x : A) (x' : B) : ((term1007 A B x x') = (term1008 A B x x')) = ((term1008 A B x x') = (@pair A B x x')).
Proof. exact (MK_COMB (@lem5961782 A B x x') (@lem5961783 A B x x')). Qed.
Lemma lem5961785 {A B : Type'} (x : A) (x' : B) : (term1008 A B x x') = (@pair A B x x').
Proof. exact (EQ_MP (@lem5961784 A B x x') (@lem5961776 A B x x')). Qed.
Lemma lem5961786 {A B : Type'} (p1 : A) (p2 : B) : (term1012 A B p1 p2) = (term1012 A B p1 p2).
Proof. exact (eq_refl (term1012 A B p1 p2)). Qed.
Lemma lem5961787 {A B : Type'} (p1 : A) (p2 : B) (x : A) (x' : B) : ((@pair A B p1 p2) = (term1008 A B x x')) = ((@pair A B p1 p2) = (@pair A B x x')).
Proof. exact (MK_COMB (@lem5961786 A B p1 p2) (@lem5961785 A B x x')). Qed.
Lemma lem5961789 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term13 A B x a y b).
Proof. exact (EQ_MP (@lem5947392 A B x a y b) (@lem5947391 A B x a y b)). Qed.
Lemma lem5961790 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term13 A B x a y b).
Proof. exact (@lem5961789 A B x a y b). Qed.
Lemma lem5961791 {A B : Type'} (p1 : A) (x : A) (p2 : B) (x' : B) : ((@pair A B p1 p2) = (@pair A B x x')) = (term13 A B p1 x p2 x').
Proof. exact (@lem5961790 A B p1 x p2 x'). Qed.
Lemma lem5961802 {A B : Type'} (p1 : A) (x : A) (p2 : B) (x' : B) : ((@pair A B p1 p2) = (term1008 A B x x')) = (term13 A B p1 x p2 x').
Proof. exact (TRANS (@lem5961787 A B p1 p2 x x') (@lem5961791 A B p1 x p2 x')). Qed.
Lemma lem5961803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5961804 {A B : Type'} (p1 : A) (x : A) (p2 : B) (x' : B) : (term1013 A B p1 p2 x x') = (term1014 A B p1 x p2 x').
Proof. exact (MK_COMB (@lem5961803) (@lem5961802 A B p1 x p2 x')). Qed.
Lemma lem5961805 {A B : Type'} (x : B) (t : type1413 A B) (x' : A) : (term740 A B x t x') = (term740 A B x t x').
Proof. exact (eq_refl (term740 A B x t x')). Qed.
Lemma lem5961806 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term1015 A B p1 p2 x t x') = (term1016 A B p1 p2 x t x').
Proof. exact (MK_COMB (@lem5961804 A B p1 x' p2 x) (@lem5961805 A B x t x')). Qed.
Lemma lem5961809 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1017 A B p1 p2 t x) = (term1018 A B p1 p2 t x).
Proof. exact (fun_ext (fun x' : B => @lem5961806 A B p1 p2 x' t x)). Qed.
Lemma lem5961810 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5961811 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1005 A B p1 p2 t x) = (term1019 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5961810 B) (@lem5961809 A B p1 p2 t x)). Qed.
Lemma lem5961818 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1004 A B p1 p2 t x) = (term1019 A B p1 p2 t x).
Proof. exact (TRANS (@lem5961760 A B p1 p2 t x) (@lem5961811 A B p1 p2 t x)). Qed.
Lemma lem5961819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5961820 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1020 A B p1 p2 t x) = (term1021 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5961819) (@lem5961818 A B p1 p2 t x)). Qed.
Lemma lem5961822 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term21 _83064 x P) = (term22 _83064 P x).
Proof. exact (EQ_MP (@lem5947436 _83064 P x) (@lem5947435 _83064 P x)). Qed.
Lemma lem5961823 {A B : Type'} (P : type914 A B) (x : prod A B) : (term1022 A B x P) = (term1023 A B P x).
Proof. exact (@lem5961822 (prod A B) P x). Qed.
Lemma lem5961824 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1024 A B p1 p2 s t) = (term1025 A B s t p1 p2).
Proof. exact (@lem5961823 A B (term1026 A B s t) (@pair A B p1 p2)). Qed.
Lemma lem5961825 {A B : Type'} (GEN_PVAR_239 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1027 A B s t GEN_PVAR_239) = (term1028 A B GEN_PVAR_239 s t).
Proof. exact (eq_refl (term1027 A B s t GEN_PVAR_239)). Qed.
Lemma lem5961826 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1029 A B s t) = (term1030 A B s t).
Proof. exact (fun_ext (fun GEN_PVAR_239 : prod A B => @lem5961825 A B GEN_PVAR_239 s t)). Qed.
Lemma lem5961827 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem5961828 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1031 A B s t) = (term942 A B s t).
Proof. exact (MK_COMB (@lem5961827 A B) (@lem5961826 A B s t)). Qed.
Lemma lem5961829 {A B : Type'} (p1 : A) (p2 : B) : (term1032 A B p1 p2) = (term1032 A B p1 p2).
Proof. exact (eq_refl (term1032 A B p1 p2)). Qed.
Lemma lem5961830 {A B : Type'} (p1 : A) (p2 : B) (s : A -> Prop) (t : type1413 A B) : (term1024 A B p1 p2 s t) = (term1033 A B p1 p2 s t).
Proof. exact (MK_COMB (@lem5961829 A B p1 p2) (@lem5961828 A B s t)). Qed.
Lemma lem5961831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5961832 {A B : Type'} (p1 : A) (p2 : B) (s : A -> Prop) (t : type1413 A B) : (term1034 A B p1 p2 s t) = (term1035 A B p1 p2 s t).
Proof. exact (MK_COMB (@lem5961831) (@lem5961830 A B p1 p2 s t)). Qed.
Lemma lem5961833 {A B : Type'} (p1 : A) (p2 : B) (s : A -> Prop) (t : type1413 A B) : (term1025 A B s t p1 p2) = (term1036 A B p1 p2 s t).
Proof. exact (eq_refl (term1025 A B s t p1 p2)). Qed.
Lemma lem5961834 {A B : Type'} (p1 : A) (p2 : B) (s : A -> Prop) (t : type1413 A B) : ((term1024 A B p1 p2 s t) = (term1025 A B s t p1 p2)) = ((term1033 A B p1 p2 s t) = (term1036 A B p1 p2 s t)).
Proof. exact (MK_COMB (@lem5961832 A B p1 p2 s t) (@lem5961833 A B p1 p2 s t)). Qed.
Lemma lem5961835 {A B : Type'} (p1 : A) (p2 : B) (s : A -> Prop) (t : type1413 A B) : (term1033 A B p1 p2 s t) = (term1036 A B p1 p2 s t).
Proof. exact (EQ_MP (@lem5961834 A B p1 p2 s t) (@lem5961824 A B s t p1 p2)). Qed.
Lemma lem5961849 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5961850 {A B : Type'} (f : type1532 A B) (y : Prop) : (term1037 A B f y) = (f y).
Proof. exact (@lem5961849 Prop (type1210 A B) f y). Qed.
Lemma lem5961851 {A B : Type'} (p1 : A) (p2 : B) (s : A -> Prop) (j : B) (t : type1413 A B) (i : A) : (term1038 A B p1 p2 s j t i) = (term1039 A B p1 p2 s j t i).
Proof. exact (@lem5961850 A B (term1040 A B p1 p2) (term1041 A B s j t i)). Qed.
Lemma lem5961852 {A B : Type'} (p : Prop) (p1 : A) (p2 : B) : (term1042 A B p1 p2 p) = (term1043 A B p p1 p2).
Proof. exact (eq_refl (term1042 A B p1 p2 p)). Qed.
Lemma lem5961853 {A B : Type'} (p1 : A) (p2 : B) : (term1044 A B p1 p2) = (term1040 A B p1 p2).
Proof. exact (fun_ext (fun p : Prop => @lem5961852 A B p p1 p2)). Qed.
Lemma lem5961854 {A B : Type'} (s : A -> Prop) (j : B) (t : type1413 A B) (i : A) : (term1041 A B s j t i) = (term1041 A B s j t i).
Proof. exact (eq_refl (term1041 A B s j t i)). Qed.
Lemma lem5961855 {A B : Type'} (p1 : A) (p2 : B) (s : A -> Prop) (j : B) (t : type1413 A B) (i : A) : (term1038 A B p1 p2 s j t i) = (term1039 A B p1 p2 s j t i).
Proof. exact (MK_COMB (@lem5961853 A B p1 p2) (@lem5961854 A B s j t i)). Qed.
Lemma lem5961856 {A B : Type'} : (@eq ((prod A B) -> Prop)) = (@eq ((prod A B) -> Prop)).
Proof. exact (eq_refl (@eq ((prod A B) -> Prop))). Qed.
Lemma lem5961857 {A B : Type'} (p1 : A) (p2 : B) (s : A -> Prop) (j : B) (t : type1413 A B) (i : A) : (term1045 A B p1 p2 s j t i) = (term1046 A B p1 p2 s j t i).
Proof. exact (MK_COMB (@lem5961856 A B) (@lem5961855 A B p1 p2 s j t i)). Qed.
Lemma lem5961858 {A B : Type'} (s : A -> Prop) (j : B) (t : type1413 A B) (i : A) (p1 : A) (p2 : B) : (term1039 A B p1 p2 s j t i) = (term1047 A B s j t i p1 p2).
Proof. exact (eq_refl (term1039 A B p1 p2 s j t i)). Qed.
Lemma lem5961859 {A B : Type'} (s : A -> Prop) (j : B) (t : type1413 A B) (i : A) (p1 : A) (p2 : B) : ((term1038 A B p1 p2 s j t i) = (term1039 A B p1 p2 s j t i)) = ((term1039 A B p1 p2 s j t i) = (term1047 A B s j t i p1 p2)).
Proof. exact (MK_COMB (@lem5961857 A B p1 p2 s j t i) (@lem5961858 A B s j t i p1 p2)). Qed.
Lemma lem5961860 {A B : Type'} (s : A -> Prop) (j : B) (t : type1413 A B) (i : A) (p1 : A) (p2 : B) : (term1039 A B p1 p2 s j t i) = (term1047 A B s j t i p1 p2).
Proof. exact (EQ_MP (@lem5961859 A B s j t i p1 p2) (@lem5961851 A B p1 p2 s j t i)). Qed.
Lemma lem5961869 {A B : Type'} (i : A) (j : B) : (@pair A B i j) = (@pair A B i j).
Proof. exact (eq_refl (@pair A B i j)). Qed.
Lemma lem5961870 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (i : A) (j : B) : (term1048 A B p1 p2 s t i j) = (term1049 A B s t p1 p2 i j).
Proof. exact (MK_COMB (@lem5961860 A B s j t i p1 p2) (@lem5961869 A B i j)). Qed.
Lemma lem5961872 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5961873 {A B : Type'} (f : type1210 A B) (y : prod A B) : (term1050 A B f y) = (f y).
Proof. exact (@lem5961872 (prod A B) Prop f y). Qed.
Lemma lem5961874 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (i : A) (j : B) : (term1051 A B s t p1 p2 i j) = (term1049 A B s t p1 p2 i j).
Proof. exact (@lem5961873 A B (term1047 A B s j t i p1 p2) (@pair A B i j)). Qed.
Lemma lem5961875 {A B : Type'} (s : A -> Prop) (j : B) (t : type1413 A B) (i : A) (p1 : A) (p2 : B) (t' : prod A B) : (term1052 A B s j t i p1 p2 t') = (term1053 A B s j t i p1 p2 t').
Proof. exact (eq_refl (term1052 A B s j t i p1 p2 t')). Qed.
Lemma lem5961876 {A B : Type'} (s : A -> Prop) (j : B) (t : type1413 A B) (i : A) (p1 : A) (p2 : B) : (term1054 A B s j t i p1 p2) = (term1047 A B s j t i p1 p2).
Proof. exact (fun_ext (fun t' : prod A B => @lem5961875 A B s j t i p1 p2 t')). Qed.
Lemma lem5961877 {A B : Type'} (i : A) (j : B) : (@pair A B i j) = (@pair A B i j).
Proof. exact (eq_refl (@pair A B i j)). Qed.
Lemma lem5961878 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (i : A) (j : B) : (term1051 A B s t p1 p2 i j) = (term1049 A B s t p1 p2 i j).
Proof. exact (MK_COMB (@lem5961876 A B s j t i p1 p2) (@lem5961877 A B i j)). Qed.
Lemma lem5961879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5961880 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (i : A) (j : B) : (term1055 A B s t p1 p2 i j) = (term1056 A B s t p1 p2 i j).
Proof. exact (MK_COMB (@lem5961879) (@lem5961878 A B s t p1 p2 i j)). Qed.
Lemma lem5961881 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (i : A) (j : B) : (term1049 A B s t p1 p2 i j) = (term1057 A B s t p1 p2 i j).
Proof. exact (eq_refl (term1049 A B s t p1 p2 i j)). Qed.
Lemma lem5961882 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (i : A) (j : B) : ((term1051 A B s t p1 p2 i j) = (term1049 A B s t p1 p2 i j)) = ((term1049 A B s t p1 p2 i j) = (term1057 A B s t p1 p2 i j)).
Proof. exact (MK_COMB (@lem5961880 A B s t p1 p2 i j) (@lem5961881 A B s t p1 p2 i j)). Qed.
Lemma lem5961883 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (i : A) (j : B) : (term1049 A B s t p1 p2 i j) = (term1057 A B s t p1 p2 i j).
Proof. exact (EQ_MP (@lem5961882 A B s t p1 p2 i j) (@lem5961874 A B s t p1 p2 i j)). Qed.
Lemma lem5961889 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term13 A B x a y b).
Proof. exact (EQ_MP (@lem5947392 A B x a y b) (@lem5947391 A B x a y b)). Qed.
Lemma lem5961890 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term13 A B x a y b).
Proof. exact (@lem5961889 A B x a y b). Qed.
Lemma lem5961891 {A B : Type'} (p1 : A) (i : A) (p2 : B) (j : B) : ((@pair A B p1 p2) = (@pair A B i j)) = (term13 A B p1 i p2 j).
Proof. exact (@lem5961890 A B p1 i p2 j). Qed.
Lemma lem5961902 {A B : Type'} (s : A -> Prop) (j : B) (t : type1413 A B) (i : A) : (term1058 A B s j t i) = (term1058 A B s j t i).
Proof. exact (eq_refl (term1058 A B s j t i)). Qed.
Lemma lem5961903 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term1057 A B s t p1 p2 i j) = (term1059 A B s t p1 i p2 j).
Proof. exact (MK_COMB (@lem5961902 A B s j t i) (@lem5961891 A B p1 i p2 j)). Qed.
Lemma lem5961906 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term1049 A B s t p1 p2 i j) = (term1059 A B s t p1 i p2 j).
Proof. exact (TRANS (@lem5961883 A B s t p1 p2 i j) (@lem5961903 A B s t p1 i p2 j)). Qed.
Lemma lem5961907 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term1048 A B p1 p2 s t i j) = (term1059 A B s t p1 i p2 j).
Proof. exact (TRANS (@lem5961870 A B s t p1 p2 i j) (@lem5961906 A B s t p1 i p2 j)). Qed.
Lemma lem5961908 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term1060 A B p1 p2 s t i) = (term1061 A B s t p1 i p2).
Proof. exact (fun_ext (fun j : B => @lem5961907 A B s t p1 i p2 j)). Qed.
Lemma lem5961909 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5961910 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term1062 A B p1 p2 s t i) = (term1063 A B s t p1 i p2).
Proof. exact (MK_COMB (@lem5961909 B) (@lem5961908 A B s t p1 i p2)). Qed.
Lemma lem5961917 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1064 A B p1 p2 s t) = (term1065 A B s t p1 p2).
Proof. exact (fun_ext (fun i : A => @lem5961910 A B s t p1 i p2)). Qed.
Lemma lem5961918 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5961919 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1036 A B p1 p2 s t) = (term1066 A B s t p1 p2).
Proof. exact (MK_COMB (@lem5961918 A) (@lem5961917 A B s t p1 p2)). Qed.
Lemma lem5961926 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1033 A B p1 p2 s t) = (term1066 A B s t p1 p2).
Proof. exact (TRANS (@lem5961835 A B p1 p2 s t) (@lem5961919 A B s t p1 p2)). Qed.
Lemma lem5961927 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1001 A B x p1 p2 s t) = (term1067 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5961820 A B p1 p2 t x) (@lem5961926 A B s t p1 p2)). Qed.
Lemma lem5961930 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term990 A B p1 p2 x s t) = (term1067 A B x s t p1 p2).
Proof. exact (TRANS (@lem5961754 A B x p1 p2 s t) (@lem5961927 A B x s t p1 p2)). Qed.
Lemma lem5961931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5961932 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1068 A B p1 p2 x s t) = (term1069 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5961931) (@lem5961930 A B x s t p1 p2)). Qed.
Lemma lem5961934 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5947441 A x (@lem5947440 A x)). Qed.
Lemma lem5961935 {A B : Type'} (x : prod A B) : (@IN (prod A B) x (@EMPTY (prod A B))) = False.
Proof. exact (@lem5961934 (prod A B) x). Qed.
Lemma lem5961936 {A B : Type'} (p1 : A) (p2 : B) : (term991 A B p1 p2) = False.
Proof. exact (@lem5961935 A B (@pair A B p1 p2)). Qed.
Lemma lem5961937 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : ((term990 A B p1 p2 x s t) = (term991 A B p1 p2)) = ((term1067 A B x s t p1 p2) = False).
Proof. exact (MK_COMB (@lem5961932 A B x s t p1 p2) (@lem5961936 A B p1 p2)). Qed.
Lemma lem5961939 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5961940 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : ((term1067 A B x s t p1 p2) = False) = (term1070 A B x s t p1 p2).
Proof. exact (@lem5961939 (term1067 A B x s t p1 p2)). Qed.
Lemma lem5961987 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : ((term990 A B p1 p2 x s t) = (term991 A B p1 p2)) = (term1070 A B x s t p1 p2).
Proof. exact (TRANS (@lem5961937 A B x s t p1 p2) (@lem5961940 A B x s t p1 p2)). Qed.
Lemma lem5961988 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term993 A B x s t p1) = (term1071 A B x s t p1).
Proof. exact (fun_ext (fun p2 : B => @lem5961987 A B x s t p1 p2)). Qed.
Lemma lem5961989 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5961990 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term995 A B x s t p1) = (term1072 A B x s t p1).
Proof. exact (MK_COMB (@lem5961989 B) (@lem5961988 A B x s t p1)). Qed.
Lemma lem5961997 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term997 A B x s t) = (term1073 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem5961990 A B x s t p1)). Qed.
Lemma lem5961998 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5961999 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term998 A B x s t) = (term1074 A B x s t).
Proof. exact (MK_COMB (@lem5961998 A) (@lem5961997 A B x s t)). Qed.
Lemma lem5962006 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term973 A B x s t) = (term1074 A B x s t).
Proof. exact (TRANS (@lem5961740 A B x s t) (@lem5961999 A B x s t)). Qed.
Lemma lem5962007 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1074 A B x s t) = (term973 A B x s t).
Proof. exact (SYM (@lem5962006 A B x s t)). Qed.
Lemma lem5962009 (p : Prop) : p = (term187 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5962010 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1074 A B x s t) = (term1075 A B x s t).
Proof. exact (@lem5962009 (term1074 A B x s t)). Qed.
Lemma lem5962011 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1075 A B x s t) = (term1074 A B x s t).
Proof. exact (SYM (@lem5962010 A B x s t)). Qed.
Lemma lem5962012 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term1076 A B x s t) : term1076 A B x s t.
Proof. exact (h1). Qed.
Lemma lem5962015 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term1077 A B C op x s t) : term1077 A B C op x s t.
Proof. exact (h1). Qed.
Lemma lem5962016 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : term1078 A B C op x s t.
Proof. exact (fun h0 : term1077 A B C op x s t => @lem5962015 A B C op x s t h0). Qed.
Lemma lem5962017 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term1078 A B C op x s t) : term1078 A B C op x s t.
Proof. exact (h1). Qed.
Lemma lem5962018 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term1077 A B C op x s t) : term1077 A B C op x s t.
Proof. exact (h1). Qed.
Lemma lem5962019 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term1077 A B C op x s t) (h2 : term1078 A B C op x s t) : term1077 A B C op x s t.
Proof. exact (@lem5962017 A B C op x s t h2 (@lem5962018 A B C op x s t h1)). Qed.
Lemma lem5962020 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term1077 A B C op x s t) : term1079 A B C op x s t.
Proof. exact (fun h0 : term1078 A B C op x s t => @lem5962019 A B C op x s t h1 h0). Qed.
Lemma lem5962021 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term1078 A B C op x s t) : term1078 A B C op x s t.
Proof. exact (h1). Qed.
Lemma lem5962022 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term1077 A B C op x s t) (h2 : term1078 A B C op x s t) : term1077 A B C op x s t.
Proof. exact (@lem5962020 A B C op x s t h1 (@lem5962021 A B C op x s t h2)). Qed.
Lemma lem5962023 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (h1 : term1078 A B C op x s t) : term1078 A B C op x s t.
Proof. exact (fun h0 : term1077 A B C op x s t => @lem5962022 A B C op x s t h0 h1). Qed.
Lemma lem5962024 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : term1080 A B C op x s t.
Proof. exact (fun h0 : term1078 A B C op x s t => @lem5962023 A B C op x s t h0). Qed.
Lemma lem5962027 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : term1078 A B C op x s t.
Proof. exact (@lem5962024 A B C op x s t (@lem5962016 A B C op x s t)). Qed.
Lemma lem5962028 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : term1078 A B C op x s t.
Proof. exact (@lem5962027 A B C op x s t). Qed.
Lemma lem5962098 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5962099 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1075 A B x s t) = (term1081 A B x s t).
Proof. exact (@lem5962098 (term1076 A B x s t)). Qed.
Lemma lem5962101 (t : Prop) : (term194 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5962102 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1081 A B x s t) = (term1074 A B x s t).
Proof. exact (@lem5962101 (term1074 A B x s t)). Qed.
Lemma lem5962107 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1075 A B x s t) = (term1074 A B x s t).
Proof. exact (TRANS (@lem5962099 A B x s t) (@lem5962102 A B x s t)). Qed.
Lemma lem5962224 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1082 A B x s t) = (term1082 A B x s t).
Proof. exact (eq_refl (term1082 A B x s t)). Qed.
Lemma lem5962225 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1083 A B x s t) = (term1084 A B x s t).
Proof. exact (MK_COMB (@lem5962224 A B x s t) (@lem5962107 A B x s t)). Qed.
Lemma lem5962228 {A : Type'} (s : A -> Prop) : (term642 A s) = (term642 A s).
Proof. exact (eq_refl (term642 A s)). Qed.
Lemma lem5962229 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1085 A B x s t) = (term1086 A B x s t).
Proof. exact (MK_COMB (@lem5962228 A s) (@lem5962225 A B x s t)). Qed.
Lemma lem5962232 {A : Type'} (x : A) (s : A -> Prop) : (term1087 A x s) = (term1087 A x s).
Proof. exact (eq_refl (term1087 A x s)). Qed.
Lemma lem5962233 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1088 A B x s t) = (term1089 A B x s t).
Proof. exact (MK_COMB (@lem5962232 A x s) (@lem5962229 A B x s t)). Qed.
Lemma lem5962236 {A B C : Type'} (op : type1400 C) (s : A -> Prop) : (term1090 A B C op s) = (term1090 A B C op s).
Proof. exact (eq_refl (term1090 A B C op s)). Qed.
Lemma lem5962237 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : (term1091 A B C op x s t) = (term1092 A B C op x s t).
Proof. exact (MK_COMB (@lem5962236 A B C op s) (@lem5962233 A B x s t)). Qed.
Lemma lem5962240 {C : Type'} (op : type1400 C) : (term1093 C op) = (term1093 C op).
Proof. exact (eq_refl (term1093 C op)). Qed.
Lemma lem5962241 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : (term1077 A B C op x s t) = (term1094 A B C op x s t).
Proof. exact (MK_COMB (@lem5962240 C op) (@lem5962237 A B C op x s t)). Qed.
Lemma lem5962244 {A B C : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1095 A B C x s t) = (term1096 A B C x s t).
Proof. exact (fun_ext (fun op : type1400 C => @lem5962241 A B C op x s t)). Qed.
Lemma lem5962245 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5962246 {A B C : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1097 A B C x s t) = (term1098 A B C x s t).
Proof. exact (MK_COMB (@lem5962245 C) (@lem5962244 A B C x s t)). Qed.
Lemma lem5962251 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) : (term1099 A B C s t) = (term1100 A B C s t).
Proof. exact (fun_ext (fun x : A => @lem5962246 A B C x s t)). Qed.
Lemma lem5962252 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962253 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) : (term1101 A B C s t) = (term1102 A B C s t).
Proof. exact (MK_COMB (@lem5962252 A) (@lem5962251 A B C s t)). Qed.
Lemma lem5962258 {A B C : Type'} (t : type1413 A B) : (term1103 A B C t) = (term1104 A B C t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5962253 A B C s t)). Qed.
Lemma lem5962259 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5962260 {A B C : Type'} (t : type1413 A B) : (term1105 A B C t) = (term1106 A B C t).
Proof. exact (MK_COMB (@lem5962259 A) (@lem5962258 A B C t)). Qed.
Lemma lem5962265 {A B C : Type'} : (term1107 A B C) = (term1108 A B C).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5962260 A B C t)). Qed.
Lemma lem5962266 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5962273 {A B C : Type'} : (term1109 A B C) = (term1110 A B C).
Proof. exact (MK_COMB (@lem5962266 A B) (@lem5962265 A B C)). Qed.
Lemma lem5962274 {A B C : Type'} (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : _75296 = (term1111 A B C).
Proof. exact (h1). Qed.
Lemma lem5962275 {C : Type'} (op : type1400 C) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5962276 {A B C : Type'} (op : type1400 C) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (_75296 op) = (term1112 A B C op).
Proof. exact (MK_COMB (@lem5962274 A B C _75296 h1) (@lem5962275 C op)). Qed.
Lemma lem5962277 {A B C : Type'} (op : type1400 C) : (term1112 A B C op) = (term1113 A B C op).
Proof. exact (eq_refl (term1112 A B C op)). Qed.
Lemma lem5962278 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1114 A B C _75296 op) = (term1114 A B C _75296 op).
Proof. exact (eq_refl (term1114 A B C _75296 op)). Qed.
Lemma lem5962279 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : ((_75296 op) = (term1112 A B C op)) = ((_75296 op) = (term1113 A B C op)).
Proof. exact (MK_COMB (@lem5962278 A B C _75296 op) (@lem5962277 A B C op)). Qed.
Lemma lem5962280 {A B C : Type'} (op : type1400 C) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (_75296 op) = (term1113 A B C op).
Proof. exact (EQ_MP (@lem5962279 A B C _75296 op) (@lem5962276 A B C op _75296 h1)). Qed.
Lemma lem5962281 {A B : Type'} (t : type1413 A B) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5962282 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (_75296 op t) = (term1115 A B C op t).
Proof. exact (MK_COMB (@lem5962280 A B C op _75296 h1) (@lem5962281 A B t)). Qed.
Lemma lem5962283 {A B C : Type'} (op : type1400 C) (t : type1413 A B) : (term1115 A B C op t) = (term1116 A B C op t).
Proof. exact (eq_refl (term1115 A B C op t)). Qed.
Lemma lem5962284 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1117 A B C _75296 op t) = (term1117 A B C _75296 op t).
Proof. exact (eq_refl (term1117 A B C _75296 op t)). Qed.
Lemma lem5962285 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : ((_75296 op t) = (term1115 A B C op t)) = ((_75296 op t) = (term1116 A B C op t)).
Proof. exact (MK_COMB (@lem5962284 A B C _75296 op t) (@lem5962283 A B C op t)). Qed.
Lemma lem5962286 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (_75296 op t) = (term1116 A B C op t).
Proof. exact (EQ_MP (@lem5962285 A B C _75296 op t) (@lem5962282 A B C op t _75296 h1)). Qed.
Lemma lem5962287 {A B C : Type'} (x : type1412 A B C) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5962288 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (_75296 op t x) = (term1118 A B C op t x).
Proof. exact (MK_COMB (@lem5962286 A B C op t _75296 h1) (@lem5962287 A B C x)). Qed.
Lemma lem5962289 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1118 A B C op t x) = (term735 A B C op t x).
Proof. exact (eq_refl (term1118 A B C op t x)). Qed.
Lemma lem5962290 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1119 A B C _75296 op t x) = (term1119 A B C _75296 op t x).
Proof. exact (eq_refl (term1119 A B C _75296 op t x)). Qed.
Lemma lem5962291 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : ((_75296 op t x) = (term1118 A B C op t x)) = ((_75296 op t x) = (term735 A B C op t x)).
Proof. exact (MK_COMB (@lem5962290 A B C _75296 op t x) (@lem5962289 A B C op t x)). Qed.
Lemma lem5962292 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (_75296 op t x) = (term735 A B C op t x).
Proof. exact (EQ_MP (@lem5962291 A B C _75296 op t x) (@lem5962288 A B C op t x _75296 h1)). Qed.
Lemma lem5962324 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term1059 A B s t p1 i p2 j) = (term1059 A B s t p1 i p2 j).
Proof. exact (eq_refl (term1059 A B s t p1 i p2 j)). Qed.
Lemma lem5962325 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term1061 A B s t p1 i p2) = (term1061 A B s t p1 i p2).
Proof. exact (fun_ext (fun j : B => @lem5962324 A B s t p1 i p2 j)). Qed.
Lemma lem5962326 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5962327 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term1063 A B s t p1 i p2) = (term1063 A B s t p1 i p2).
Proof. exact (MK_COMB (@lem5962326 B) (@lem5962325 A B s t p1 i p2)). Qed.
Lemma lem5962328 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1065 A B s t p1 p2) = (term1065 A B s t p1 p2).
Proof. exact (fun_ext (fun i : A => @lem5962327 A B s t p1 i p2)). Qed.
Lemma lem5962329 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5962330 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1066 A B s t p1 p2) = (term1066 A B s t p1 p2).
Proof. exact (MK_COMB (@lem5962329 A) (@lem5962328 A B s t p1 p2)). Qed.
Lemma lem5962353 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term1016 A B p1 p2 x t x') = (term1016 A B p1 p2 x t x').
Proof. exact (eq_refl (term1016 A B p1 p2 x t x')). Qed.
Lemma lem5962354 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1018 A B p1 p2 t x) = (term1018 A B p1 p2 t x).
Proof. exact (fun_ext (fun x' : B => @lem5962353 A B p1 p2 x' t x)). Qed.
Lemma lem5962355 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5962356 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1019 A B p1 p2 t x) = (term1019 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5962355 B) (@lem5962354 A B p1 p2 t x)). Qed.
Lemma lem5962357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5962358 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1021 A B p1 p2 t x) = (term1021 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5962357) (@lem5962356 A B p1 p2 t x)). Qed.
Lemma lem5962359 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1067 A B x s t p1 p2) = (term1067 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5962358 A B p1 p2 t x) (@lem5962330 A B s t p1 p2)). Qed.
Lemma lem5962360 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5962361 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1070 A B x s t p1 p2) = (term1070 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5962360) (@lem5962359 A B x s t p1 p2)). Qed.
Lemma lem5962362 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term1071 A B x s t p1) = (term1071 A B x s t p1).
Proof. exact (fun_ext (fun p2 : B => @lem5962361 A B x s t p1 p2)). Qed.
Lemma lem5962363 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5962364 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term1072 A B x s t p1) = (term1072 A B x s t p1).
Proof. exact (MK_COMB (@lem5962363 B) (@lem5962362 A B x s t p1)). Qed.
Lemma lem5962365 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1073 A B x s t) = (term1073 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem5962364 A B x s t p1)). Qed.
Lemma lem5962366 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962367 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1074 A B x s t) = (term1074 A B x s t).
Proof. exact (MK_COMB (@lem5962366 A) (@lem5962365 A B x s t)). Qed.
Lemma lem5962388 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) : (term892 A B x s t i) = (term892 A B x s t i).
Proof. exact (eq_refl (term892 A B x s t i)). Qed.
Lemma lem5962389 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term894 A B x s t) = (term894 A B x s t).
Proof. exact (fun_ext (fun i : A => @lem5962388 A B x s t i)). Qed.
Lemma lem5962390 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962391 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term895 A B x s t) = (term895 A B x s t).
Proof. exact (MK_COMB (@lem5962390 A) (@lem5962389 A B x s t)). Qed.
Lemma lem5962392 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5962393 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1082 A B x s t) = (term1082 A B x s t).
Proof. exact (MK_COMB (@lem5962392) (@lem5962391 A B x s t)). Qed.
Lemma lem5962394 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1084 A B x s t) = (term1084 A B x s t).
Proof. exact (MK_COMB (@lem5962393 A B x s t) (@lem5962367 A B x s t)). Qed.
Lemma lem5962399 {A : Type'} (s : A -> Prop) : (term642 A s) = (term642 A s).
Proof. exact (eq_refl (term642 A s)). Qed.
Lemma lem5962400 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1086 A B x s t) = (term1086 A B x s t).
Proof. exact (MK_COMB (@lem5962399 A s) (@lem5962394 A B x s t)). Qed.
Lemma lem5962409 {A : Type'} (x : A) (s : A -> Prop) : (term1087 A x s) = (term1087 A x s).
Proof. exact (eq_refl (term1087 A x s)). Qed.
Lemma lem5962410 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1089 A B x s t) = (term1089 A B x s t).
Proof. exact (MK_COMB (@lem5962409 A x s) (@lem5962400 A B x s t)). Qed.
Lemma lem5962425 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) (j : B) : (term1120 A B C f x i j) = (term1120 A B C f x i j).
Proof. exact (eq_refl (term1120 A B C f x i j)). Qed.
Lemma lem5962426 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1121 A B C f x i) = (term1121 A B C f x i).
Proof. exact (fun_ext (fun j : B => @lem5962425 A B C f x i j)). Qed.
Lemma lem5962427 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5962428 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1122 A B C f x i) = (term1122 A B C f x i).
Proof. exact (MK_COMB (@lem5962427 B) (@lem5962426 A B C f x i)). Qed.
Lemma lem5962429 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1123 A B C f x) = (term1123 A B C f x).
Proof. exact (fun_ext (fun i : A => @lem5962428 A B C f x i)). Qed.
Lemma lem5962430 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962431 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1124 A B C f x) = (term1124 A B C f x).
Proof. exact (MK_COMB (@lem5962430 A) (@lem5962429 A B C f x)). Qed.
Lemma lem5962432 {A B C : Type'} (x : type1412 A B C) : (term1125 A B C x) = (term1125 A B C x).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5962431 A B C f x)). Qed.
Lemma lem5962433 {A B C : Type'} : (@GABS ((prod A B) -> C)) = (@GABS ((prod A B) -> C)).
Proof. exact (eq_refl (@GABS ((prod A B) -> C))). Qed.
Lemma lem5962434 {A B C : Type'} (x : type1412 A B C) : (term759 A B C x) = (term759 A B C x).
Proof. exact (MK_COMB (@lem5962433 A B C) (@lem5962432 A B C x)). Qed.
Lemma lem5962459 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) (j : B) : (term1126 A B GEN_PVAR_241 s t i j) = (term1126 A B GEN_PVAR_241 s t i j).
Proof. exact (eq_refl (term1126 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5962460 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1127 A B GEN_PVAR_241 s t i) = (term1127 A B GEN_PVAR_241 s t i).
Proof. exact (fun_ext (fun j : B => @lem5962459 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5962461 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5962462 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1128 A B GEN_PVAR_241 s t i) = (term1128 A B GEN_PVAR_241 s t i).
Proof. exact (MK_COMB (@lem5962461 B) (@lem5962460 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5962463 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1129 A B GEN_PVAR_241 s t) = (term1129 A B GEN_PVAR_241 s t).
Proof. exact (fun_ext (fun i : A => @lem5962462 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5962464 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5962465 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1028 A B GEN_PVAR_241 s t) = (term1028 A B GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5962464 A) (@lem5962463 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5962466 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1030 A B s t) = (term1030 A B s t).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5962465 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5962467 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem5962468 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term942 A B s t) = (term942 A B s t).
Proof. exact (MK_COMB (@lem5962467 A B) (@lem5962466 A B s t)). Qed.
Lemma lem5962471 {A B C : Type'} (op : type1400 C) : (@iterate C (prod A B) op) = (@iterate C (prod A B) op).
Proof. exact (eq_refl (@iterate C (prod A B) op)). Qed.
Lemma lem5962472 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) : (term1130 A B C op s t) = (term1130 A B C op s t).
Proof. exact (MK_COMB (@lem5962471 A B C op) (@lem5962468 A B s t)). Qed.
Lemma lem5962473 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x : type1412 A B C) : (term614 A B C op s t x) = (term614 A B C op s t x).
Proof. exact (MK_COMB (@lem5962472 A B C op s t) (@lem5962434 A B C x)). Qed.
Lemma lem5962475 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term735 A B C op t x) = (_75296 op t x).
Proof. exact (SYM (@lem5962292 A B C op t x _75296 h1)). Qed.
Lemma lem5962476 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term735 A B C op t x) = (_75296 op t x).
Proof. exact (@lem5962475 A B C op t x _75296 h1). Qed.
Lemma lem5962481 {A C : Type'} (op : type1400 C) (s : A -> Prop) : (@iterate C A op s) = (@iterate C A op s).
Proof. exact (eq_refl (@iterate C A op s)). Qed.
Lemma lem5962482 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term613 A B C s op t x) = (term1131 A B C s _75296 op t x).
Proof. exact (MK_COMB (@lem5962481 A C op s) (@lem5962476 A B C op t x _75296 h1)). Qed.
Lemma lem5962483 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem5962484 {A B C : Type'} (s : A -> Prop) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term1132 A B C s op t x) = (term1133 A B C s _75296 op t x).
Proof. exact (MK_COMB (@lem5962483 C) (@lem5962482 A B C s op t x _75296 h1)). Qed.
Lemma lem5962485 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x : type1412 A B C) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : ((term613 A B C s op t x) = (term614 A B C op s t x)) = ((term1131 A B C s _75296 op t x) = (term614 A B C op s t x)).
Proof. exact (MK_COMB (@lem5962484 A B C s op t x _75296 h1) (@lem5962473 A B C op s t x)). Qed.
Lemma lem5962486 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term611 A B C op s t) = (term1134 A B C _75296 op s t).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5962485 A B C op s t x _75296 h1)). Qed.
Lemma lem5962487 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5962488 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term625 A B C op s t) = (term1135 A B C _75296 op s t).
Proof. exact (MK_COMB (@lem5962487 A B C) (@lem5962486 A B C op s t _75296 h1)). Qed.
Lemma lem5962501 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : (term911 A B s t i) = (term911 A B s t i).
Proof. exact (eq_refl (term911 A B s t i)). Qed.
Lemma lem5962502 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term913 A B s t) = (term913 A B s t).
Proof. exact (fun_ext (fun i : A => @lem5962501 A B s t i)). Qed.
Lemma lem5962503 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962504 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term630 A B s t) = (term630 A B s t).
Proof. exact (MK_COMB (@lem5962503 A) (@lem5962502 A B s t)). Qed.
Lemma lem5962505 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5962506 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1136 A B s t) = (term1136 A B s t).
Proof. exact (MK_COMB (@lem5962505) (@lem5962504 A B s t)). Qed.
Lemma lem5962507 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term641 A B C op s t) = (term1137 A B C _75296 op s t).
Proof. exact (MK_COMB (@lem5962506 A B s t) (@lem5962488 A B C op s t _75296 h1)). Qed.
Lemma lem5962508 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term639 A B C op s) = (term1138 A B C _75296 op s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5962507 A B C op s t _75296 h1)). Qed.
Lemma lem5962509 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5962510 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term649 A B C op s) = (term1139 A B C _75296 op s).
Proof. exact (MK_COMB (@lem5962509 A B) (@lem5962508 A B C op s _75296 h1)). Qed.
Lemma lem5962511 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5962512 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term1090 A B C op s) = (term1140 A B C _75296 op s).
Proof. exact (MK_COMB (@lem5962511) (@lem5962510 A B C op s _75296 h1)). Qed.
Lemma lem5962513 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term1092 A B C op x s t) = (term1141 A B C _75296 op x s t).
Proof. exact (MK_COMB (@lem5962512 A B C op s _75296 h1) (@lem5962410 A B x s t)). Qed.
Lemma lem5962518 {C : Type'} (op : type1400 C) : (term1093 C op) = (term1093 C op).
Proof. exact (eq_refl (term1093 C op)). Qed.
Lemma lem5962519 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term1094 A B C op x s t) = (term1142 A B C _75296 op x s t).
Proof. exact (MK_COMB (@lem5962518 C op) (@lem5962513 A B C op x s t _75296 h1)). Qed.
Lemma lem5962520 {A B C : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term1096 A B C x s t) = (term1143 A B C _75296 x s t).
Proof. exact (fun_ext (fun op : type1400 C => @lem5962519 A B C op x s t _75296 h1)). Qed.
Lemma lem5962521 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5962522 {A B C : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term1098 A B C x s t) = (term1144 A B C _75296 x s t).
Proof. exact (MK_COMB (@lem5962521 C) (@lem5962520 A B C x s t _75296 h1)). Qed.
Lemma lem5962523 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term1100 A B C s t) = (term1145 A B C _75296 s t).
Proof. exact (fun_ext (fun x : A => @lem5962522 A B C x s t _75296 h1)). Qed.
Lemma lem5962524 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962525 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term1102 A B C s t) = (term1146 A B C _75296 s t).
Proof. exact (MK_COMB (@lem5962524 A) (@lem5962523 A B C s t _75296 h1)). Qed.
Lemma lem5962526 {A B C : Type'} (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term1104 A B C t) = (term1147 A B C _75296 t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5962525 A B C s t _75296 h1)). Qed.
Lemma lem5962527 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5962528 {A B C : Type'} (t : type1413 A B) (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term1106 A B C t) = (term1148 A B C _75296 t).
Proof. exact (MK_COMB (@lem5962527 A) (@lem5962526 A B C t _75296 h1)). Qed.
Lemma lem5962529 {A B C : Type'} (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term1108 A B C) = (term1149 A B C _75296).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5962528 A B C t _75296 h1)). Qed.
Lemma lem5962530 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5962531 {A B C : Type'} (_75296 : type877 A B C) (h1 : _75296 = (term1111 A B C)) : (term1110 A B C) = (term1150 A B C _75296).
Proof. exact (MK_COMB (@lem5962530 A B) (@lem5962529 A B C _75296 h1)). Qed.
Lemma lem5962532 {A B C : Type'} (_75296 : type877 A B C) : term1151 A B C _75296.
Proof. exact (fun h0 : _75296 = (term1111 A B C) => @lem5962531 A B C _75296 h0). Qed.
Lemma lem5962533 {A B C : Type'} : term1152 A B C.
Proof. exact (fun _75296 : type877 A B C => @lem5962532 A B C _75296). Qed.
Lemma lem5962535 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term1153 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem5962536 {A B C : Type'} (P : Prop) (c : type877 A B C) (Q : type237 A B C) : term1154 A B C P c Q.
Proof. exact (@lem5962535 (type877 A B C) P c Q). Qed.
Lemma lem5962537 {A B C : Type'} : term1155 A B C.
Proof. exact (@lem5962536 A B C (term1110 A B C) (term1111 A B C) (term1156 A B C)). Qed.
Lemma lem5962538 {A B C : Type'} (_75296 : type877 A B C) : (term1157 A B C _75296) = (term1150 A B C _75296).
Proof. exact (eq_refl (term1157 A B C _75296)). Qed.
Lemma lem5962539 {A B C : Type'} : (term1158 A B C) = (term1158 A B C).
Proof. exact (eq_refl (term1158 A B C)). Qed.
Lemma lem5962540 {A B C : Type'} (_75296 : type877 A B C) : ((term1110 A B C) = (term1157 A B C _75296)) = ((term1110 A B C) = (term1150 A B C _75296)).
Proof. exact (MK_COMB (@lem5962539 A B C) (@lem5962538 A B C _75296)). Qed.
Lemma lem5962541 {A B C : Type'} (_75296 : type877 A B C) : (term1159 A B C _75296) = (term1159 A B C _75296).
Proof. exact (eq_refl (term1159 A B C _75296)). Qed.
Lemma lem5962542 {A B C : Type'} (_75296 : type877 A B C) : (term1160 A B C _75296) = (term1151 A B C _75296).
Proof. exact (MK_COMB (@lem5962541 A B C _75296) (@lem5962540 A B C _75296)). Qed.
Lemma lem5962543 {A B C : Type'} : (term1161 A B C) = (term1162 A B C).
Proof. exact (fun_ext (fun _75296 : type877 A B C => @lem5962542 A B C _75296)). Qed.
Lemma lem5962544 {A B C : Type'} : (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C)) = (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C)).
Proof. exact (eq_refl (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C))). Qed.
Lemma lem5962545 {A B C : Type'} : (term1163 A B C) = (term1152 A B C).
Proof. exact (MK_COMB (@lem5962544 A B C) (@lem5962543 A B C)). Qed.
Lemma lem5962546 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5962547 {A B C : Type'} : (term1164 A B C) = (term1165 A B C).
Proof. exact (MK_COMB (@lem5962546) (@lem5962545 A B C)). Qed.
Lemma lem5962548 {A B C : Type'} (_75296 : type877 A B C) : (term1157 A B C _75296) = (term1150 A B C _75296).
Proof. exact (eq_refl (term1157 A B C _75296)). Qed.
Lemma lem5962549 {A B C : Type'} (_75296 : type877 A B C) : (term1159 A B C _75296) = (term1159 A B C _75296).
Proof. exact (eq_refl (term1159 A B C _75296)). Qed.
Lemma lem5962550 {A B C : Type'} (_75296 : type877 A B C) : (term1166 A B C _75296) = (term1167 A B C _75296).
Proof. exact (MK_COMB (@lem5962549 A B C _75296) (@lem5962548 A B C _75296)). Qed.
Lemma lem5962551 {A B C : Type'} : (term1168 A B C) = (term1169 A B C).
Proof. exact (fun_ext (fun _75296 : type877 A B C => @lem5962550 A B C _75296)). Qed.
Lemma lem5962552 {A B C : Type'} : (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C)) = (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C)).
Proof. exact (eq_refl (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C))). Qed.
Lemma lem5962553 {A B C : Type'} : (term1170 A B C) = (term1171 A B C).
Proof. exact (MK_COMB (@lem5962552 A B C) (@lem5962551 A B C)). Qed.
Lemma lem5962554 {A B C : Type'} : (term1158 A B C) = (term1158 A B C).
Proof. exact (eq_refl (term1158 A B C)). Qed.
Lemma lem5962555 {A B C : Type'} : ((term1110 A B C) = (term1170 A B C)) = ((term1110 A B C) = (term1171 A B C)).
Proof. exact (MK_COMB (@lem5962554 A B C) (@lem5962553 A B C)). Qed.
Lemma lem5962556 {A B C : Type'} : (term1155 A B C) = (term1172 A B C).
Proof. exact (MK_COMB (@lem5962547 A B C) (@lem5962555 A B C)). Qed.
Lemma lem5962557 {A B C : Type'} : term1172 A B C.
Proof. exact (EQ_MP (@lem5962556 A B C) (@lem5962537 A B C)). Qed.
Lemma lem5962558 {A B C : Type'} : (term1110 A B C) = (term1171 A B C).
Proof. exact (@lem5962557 A B C (@lem5962533 A B C)). Qed.
Lemma lem5962560 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term1173 _3571 _3575 t)) = (term1174 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5962561 {A B C : Type'} (s : type877 A B C) (t : type877 A B C) : (s = (term1175 A B C t)) = (term1176 A B C s t).
Proof. exact (@lem5962560 (type452 A B C) (type1400 C) s t). Qed.
Lemma lem5962562 {A B C : Type'} (_75296 : type877 A B C) : (_75296 = (term1177 A B C)) = (term1178 A B C _75296).
Proof. exact (@lem5962561 A B C _75296 (term1111 A B C)). Qed.
Lemma lem5962563 {A B C : Type'} (op : type1400 C) : (term1112 A B C op) = (term1113 A B C op).
Proof. exact (eq_refl (term1112 A B C op)). Qed.
Lemma lem5962564 {A B C : Type'} : (term1177 A B C) = (term1111 A B C).
Proof. exact (fun_ext (fun op : type1400 C => @lem5962563 A B C op)). Qed.
Lemma lem5962565 {A B C : Type'} (_75296 : type877 A B C) : (@eq ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C) _75296) = (@eq ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C) _75296).
Proof. exact (eq_refl (@eq ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C) _75296)). Qed.
Lemma lem5962566 {A B C : Type'} (_75296 : type877 A B C) : (_75296 = (term1177 A B C)) = (_75296 = (term1111 A B C)).
Proof. exact (MK_COMB (@lem5962565 A B C _75296) (@lem5962564 A B C)). Qed.
Lemma lem5962567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5962568 {A B C : Type'} (_75296 : type877 A B C) : (term1179 A B C _75296) = (term1180 A B C _75296).
Proof. exact (MK_COMB (@lem5962567) (@lem5962566 A B C _75296)). Qed.
Lemma lem5962569 {A B C : Type'} (op : type1400 C) : (term1112 A B C op) = (term1113 A B C op).
Proof. exact (eq_refl (term1112 A B C op)). Qed.
Lemma lem5962570 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1114 A B C _75296 op) = (term1114 A B C _75296 op).
Proof. exact (eq_refl (term1114 A B C _75296 op)). Qed.
Lemma lem5962571 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : ((_75296 op) = (term1112 A B C op)) = ((_75296 op) = (term1113 A B C op)).
Proof. exact (MK_COMB (@lem5962570 A B C _75296 op) (@lem5962569 A B C op)). Qed.
Lemma lem5962572 {A B C : Type'} (_75296 : type877 A B C) : (term1181 A B C _75296) = (term1182 A B C _75296).
Proof. exact (fun_ext (fun op : type1400 C => @lem5962571 A B C _75296 op)). Qed.
Lemma lem5962573 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5962574 {A B C : Type'} (_75296 : type877 A B C) : (term1178 A B C _75296) = (term1183 A B C _75296).
Proof. exact (MK_COMB (@lem5962573 C) (@lem5962572 A B C _75296)). Qed.
Lemma lem5962575 {A B C : Type'} (_75296 : type877 A B C) : ((_75296 = (term1177 A B C)) = (term1178 A B C _75296)) = ((_75296 = (term1111 A B C)) = (term1183 A B C _75296)).
Proof. exact (MK_COMB (@lem5962568 A B C _75296) (@lem5962574 A B C _75296)). Qed.
Lemma lem5962576 {A B C : Type'} (_75296 : type877 A B C) : (_75296 = (term1111 A B C)) = (term1183 A B C _75296).
Proof. exact (EQ_MP (@lem5962575 A B C _75296) (@lem5962562 A B C _75296)). Qed.
Lemma lem5962578 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term1173 _3571 _3575 t)) = (term1174 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5962579 {A B C : Type'} (s : type452 A B C) (t : type452 A B C) : (s = (term1184 A B C t)) = (term1185 A B C s t).
Proof. exact (@lem5962578 (type442 A B C) (type1413 A B) s t). Qed.
Lemma lem5962580 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : ((_75296 op) = (term1186 A B C op)) = (term1187 A B C _75296 op).
Proof. exact (@lem5962579 A B C (_75296 op) (term1113 A B C op)). Qed.
Lemma lem5962581 {A B C : Type'} (op : type1400 C) (t : type1413 A B) : (term1115 A B C op t) = (term1116 A B C op t).
Proof. exact (eq_refl (term1115 A B C op t)). Qed.
Lemma lem5962582 {A B C : Type'} (op : type1400 C) : (term1186 A B C op) = (term1113 A B C op).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5962581 A B C op t)). Qed.
Lemma lem5962583 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1114 A B C _75296 op) = (term1114 A B C _75296 op).
Proof. exact (eq_refl (term1114 A B C _75296 op)). Qed.
Lemma lem5962584 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : ((_75296 op) = (term1186 A B C op)) = ((_75296 op) = (term1113 A B C op)).
Proof. exact (MK_COMB (@lem5962583 A B C _75296 op) (@lem5962582 A B C op)). Qed.
Lemma lem5962585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5962586 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1188 A B C _75296 op) = (term1189 A B C _75296 op).
Proof. exact (MK_COMB (@lem5962585) (@lem5962584 A B C _75296 op)). Qed.
Lemma lem5962587 {A B C : Type'} (op : type1400 C) (t : type1413 A B) : (term1115 A B C op t) = (term1116 A B C op t).
Proof. exact (eq_refl (term1115 A B C op t)). Qed.
Lemma lem5962588 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1117 A B C _75296 op t) = (term1117 A B C _75296 op t).
Proof. exact (eq_refl (term1117 A B C _75296 op t)). Qed.
Lemma lem5962589 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : ((_75296 op t) = (term1115 A B C op t)) = ((_75296 op t) = (term1116 A B C op t)).
Proof. exact (MK_COMB (@lem5962588 A B C _75296 op t) (@lem5962587 A B C op t)). Qed.
Lemma lem5962590 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1190 A B C _75296 op) = (term1191 A B C _75296 op).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5962589 A B C _75296 op t)). Qed.
Lemma lem5962591 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5962592 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1187 A B C _75296 op) = (term1192 A B C _75296 op).
Proof. exact (MK_COMB (@lem5962591 A B) (@lem5962590 A B C _75296 op)). Qed.
Lemma lem5962593 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (((_75296 op) = (term1186 A B C op)) = (term1187 A B C _75296 op)) = (((_75296 op) = (term1113 A B C op)) = (term1192 A B C _75296 op)).
Proof. exact (MK_COMB (@lem5962586 A B C _75296 op) (@lem5962592 A B C _75296 op)). Qed.
Lemma lem5962594 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : ((_75296 op) = (term1113 A B C op)) = (term1192 A B C _75296 op).
Proof. exact (EQ_MP (@lem5962593 A B C _75296 op) (@lem5962580 A B C _75296 op)). Qed.
Lemma lem5962596 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term1173 _3571 _3575 t)) = (term1174 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5962597 {A B C : Type'} (s : type442 A B C) (t : type442 A B C) : (s = (term1193 A B C t)) = (term1194 A B C s t).
Proof. exact (@lem5962596 (A -> C) (type1412 A B C) s t). Qed.
Lemma lem5962598 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : ((_75296 op t) = (term1195 A B C op t)) = (term1196 A B C _75296 op t).
Proof. exact (@lem5962597 A B C (_75296 op t) (term1116 A B C op t)). Qed.
Lemma lem5962599 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1118 A B C op t x) = (term735 A B C op t x).
Proof. exact (eq_refl (term1118 A B C op t x)). Qed.
Lemma lem5962600 {A B C : Type'} (op : type1400 C) (t : type1413 A B) : (term1195 A B C op t) = (term1116 A B C op t).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5962599 A B C op t x)). Qed.
Lemma lem5962601 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1117 A B C _75296 op t) = (term1117 A B C _75296 op t).
Proof. exact (eq_refl (term1117 A B C _75296 op t)). Qed.
Lemma lem5962602 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : ((_75296 op t) = (term1195 A B C op t)) = ((_75296 op t) = (term1116 A B C op t)).
Proof. exact (MK_COMB (@lem5962601 A B C _75296 op t) (@lem5962600 A B C op t)). Qed.
Lemma lem5962603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5962604 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1197 A B C _75296 op t) = (term1198 A B C _75296 op t).
Proof. exact (MK_COMB (@lem5962603) (@lem5962602 A B C _75296 op t)). Qed.
Lemma lem5962605 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1118 A B C op t x) = (term735 A B C op t x).
Proof. exact (eq_refl (term1118 A B C op t x)). Qed.
Lemma lem5962606 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1119 A B C _75296 op t x) = (term1119 A B C _75296 op t x).
Proof. exact (eq_refl (term1119 A B C _75296 op t x)). Qed.
Lemma lem5962607 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : ((_75296 op t x) = (term1118 A B C op t x)) = ((_75296 op t x) = (term735 A B C op t x)).
Proof. exact (MK_COMB (@lem5962606 A B C _75296 op t x) (@lem5962605 A B C op t x)). Qed.
Lemma lem5962608 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1199 A B C _75296 op t) = (term1200 A B C _75296 op t).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5962607 A B C _75296 op t x)). Qed.
Lemma lem5962609 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5962610 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1196 A B C _75296 op t) = (term1201 A B C _75296 op t).
Proof. exact (MK_COMB (@lem5962609 A B C) (@lem5962608 A B C _75296 op t)). Qed.
Lemma lem5962611 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (((_75296 op t) = (term1195 A B C op t)) = (term1196 A B C _75296 op t)) = (((_75296 op t) = (term1116 A B C op t)) = (term1201 A B C _75296 op t)).
Proof. exact (MK_COMB (@lem5962604 A B C _75296 op t) (@lem5962610 A B C _75296 op t)). Qed.
Lemma lem5962612 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : ((_75296 op t) = (term1116 A B C op t)) = (term1201 A B C _75296 op t).
Proof. exact (EQ_MP (@lem5962611 A B C _75296 op t) (@lem5962598 A B C _75296 op t)). Qed.
Lemma lem5962614 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term1173 _3571 _3575 t)) = (term1174 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5962615 {A C : Type'} (s : A -> C) (t : A -> C) : (s = (term1 A C t)) = (term1202 A C s t).
Proof. exact (@lem5962614 C A s t). Qed.
Lemma lem5962616 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : ((_75296 op t x) = (term819 A B C op t x)) = (term1203 A B C _75296 op t x).
Proof. exact (@lem5962615 A C (_75296 op t x) (term735 A B C op t x)). Qed.
Lemma lem5962617 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (i : A) : (term817 A B C op t x i) = (term818 A B C op t x i).
Proof. exact (eq_refl (term817 A B C op t x i)). Qed.
Lemma lem5962618 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term819 A B C op t x) = (term735 A B C op t x).
Proof. exact (fun_ext (fun i : A => @lem5962617 A B C op t x i)). Qed.
Lemma lem5962619 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1119 A B C _75296 op t x) = (term1119 A B C _75296 op t x).
Proof. exact (eq_refl (term1119 A B C _75296 op t x)). Qed.
Lemma lem5962620 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : ((_75296 op t x) = (term819 A B C op t x)) = ((_75296 op t x) = (term735 A B C op t x)).
Proof. exact (MK_COMB (@lem5962619 A B C _75296 op t x) (@lem5962618 A B C op t x)). Qed.
Lemma lem5962621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5962622 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1204 A B C _75296 op t x) = (term1205 A B C _75296 op t x).
Proof. exact (MK_COMB (@lem5962621) (@lem5962620 A B C _75296 op t x)). Qed.
Lemma lem5962623 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (i : A) : (term817 A B C op t x i) = (term818 A B C op t x i).
Proof. exact (eq_refl (term817 A B C op t x i)). Qed.
Lemma lem5962624 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (i : A) : (term1206 A B C _75296 op t x i) = (term1206 A B C _75296 op t x i).
Proof. exact (eq_refl (term1206 A B C _75296 op t x i)). Qed.
Lemma lem5962625 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (i : A) : ((_75296 op t x i) = (term817 A B C op t x i)) = ((_75296 op t x i) = (term818 A B C op t x i)).
Proof. exact (MK_COMB (@lem5962624 A B C _75296 op t x i) (@lem5962623 A B C op t x i)). Qed.
Lemma lem5962626 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1207 A B C _75296 op t x) = (term1208 A B C _75296 op t x).
Proof. exact (fun_ext (fun i : A => @lem5962625 A B C _75296 op t x i)). Qed.
Lemma lem5962627 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962628 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1203 A B C _75296 op t x) = (term1209 A B C _75296 op t x).
Proof. exact (MK_COMB (@lem5962627 A) (@lem5962626 A B C _75296 op t x)). Qed.
Lemma lem5962629 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (((_75296 op t x) = (term819 A B C op t x)) = (term1203 A B C _75296 op t x)) = (((_75296 op t x) = (term735 A B C op t x)) = (term1209 A B C _75296 op t x)).
Proof. exact (MK_COMB (@lem5962622 A B C _75296 op t x) (@lem5962628 A B C _75296 op t x)). Qed.
Lemma lem5962630 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : ((_75296 op t x) = (term735 A B C op t x)) = (term1209 A B C _75296 op t x).
Proof. exact (EQ_MP (@lem5962629 A B C _75296 op t x) (@lem5962616 A B C _75296 op t x)). Qed.
Lemma lem5962631 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (i : A) : ((_75296 op t x i) = (term818 A B C op t x i)) = ((_75296 op t x i) = (term818 A B C op t x i)).
Proof. exact (eq_refl ((_75296 op t x i) = (term818 A B C op t x i))). Qed.
Lemma lem5962632 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1208 A B C _75296 op t x) = (term1208 A B C _75296 op t x).
Proof. exact (fun_ext (fun i : A => @lem5962631 A B C _75296 op t x i)). Qed.
Lemma lem5962633 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962634 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1209 A B C _75296 op t x) = (term1209 A B C _75296 op t x).
Proof. exact (MK_COMB (@lem5962633 A) (@lem5962632 A B C _75296 op t x)). Qed.
Lemma lem5962635 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : ((_75296 op t x) = (term735 A B C op t x)) = (term1209 A B C _75296 op t x).
Proof. exact (TRANS (@lem5962630 A B C _75296 op t x) (@lem5962634 A B C _75296 op t x)). Qed.
Lemma lem5962636 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1200 A B C _75296 op t) = (term1210 A B C _75296 op t).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5962635 A B C _75296 op t x)). Qed.
Lemma lem5962637 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5962638 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1201 A B C _75296 op t) = (term1211 A B C _75296 op t).
Proof. exact (MK_COMB (@lem5962637 A B C) (@lem5962636 A B C _75296 op t)). Qed.
Lemma lem5962639 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : ((_75296 op t) = (term1116 A B C op t)) = (term1211 A B C _75296 op t).
Proof. exact (TRANS (@lem5962612 A B C _75296 op t) (@lem5962638 A B C _75296 op t)). Qed.
Lemma lem5962640 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1191 A B C _75296 op) = (term1212 A B C _75296 op).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5962639 A B C _75296 op t)). Qed.
Lemma lem5962641 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5962642 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1192 A B C _75296 op) = (term1213 A B C _75296 op).
Proof. exact (MK_COMB (@lem5962641 A B) (@lem5962640 A B C _75296 op)). Qed.
Lemma lem5962643 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : ((_75296 op) = (term1113 A B C op)) = (term1213 A B C _75296 op).
Proof. exact (TRANS (@lem5962594 A B C _75296 op) (@lem5962642 A B C _75296 op)). Qed.
Lemma lem5962644 {A B C : Type'} (_75296 : type877 A B C) : (term1182 A B C _75296) = (term1214 A B C _75296).
Proof. exact (fun_ext (fun op : type1400 C => @lem5962643 A B C _75296 op)). Qed.
Lemma lem5962645 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5962646 {A B C : Type'} (_75296 : type877 A B C) : (term1183 A B C _75296) = (term1215 A B C _75296).
Proof. exact (MK_COMB (@lem5962645 C) (@lem5962644 A B C _75296)). Qed.
Lemma lem5962647 {A B C : Type'} (_75296 : type877 A B C) : (_75296 = (term1111 A B C)) = (term1215 A B C _75296).
Proof. exact (TRANS (@lem5962576 A B C _75296) (@lem5962646 A B C _75296)). Qed.
Lemma lem5962648 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5962649 {A B C : Type'} (_75296 : type877 A B C) : (term1159 A B C _75296) = (term1216 A B C _75296).
Proof. exact (MK_COMB (@lem5962648) (@lem5962647 A B C _75296)). Qed.
Lemma lem5962650 {A B C : Type'} (_75296 : type877 A B C) : (term1150 A B C _75296) = (term1150 A B C _75296).
Proof. exact (eq_refl (term1150 A B C _75296)). Qed.
Lemma lem5962651 {A B C : Type'} (_75296 : type877 A B C) : (term1167 A B C _75296) = (term1217 A B C _75296).
Proof. exact (MK_COMB (@lem5962649 A B C _75296) (@lem5962650 A B C _75296)). Qed.
Lemma lem5962652 {A B C : Type'} : (term1169 A B C) = (term1218 A B C).
Proof. exact (fun_ext (fun _75296 : type877 A B C => @lem5962651 A B C _75296)). Qed.
Lemma lem5962653 {A B C : Type'} : (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C)) = (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C)).
Proof. exact (eq_refl (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C))). Qed.
Lemma lem5962654 {A B C : Type'} : (term1171 A B C) = (term1219 A B C).
Proof. exact (MK_COMB (@lem5962653 A B C) (@lem5962652 A B C)). Qed.
Lemma lem5962655 {A B C : Type'} : (term1158 A B C) = (term1158 A B C).
Proof. exact (eq_refl (term1158 A B C)). Qed.
Lemma lem5962656 {A B C : Type'} : ((term1110 A B C) = (term1171 A B C)) = ((term1110 A B C) = (term1219 A B C)).
Proof. exact (MK_COMB (@lem5962655 A B C) (@lem5962654 A B C)). Qed.
Lemma lem5962657 {A B C : Type'} : (term1110 A B C) = (term1219 A B C).
Proof. exact (EQ_MP (@lem5962656 A B C) (@lem5962558 A B C)). Qed.
Lemma lem5962658 {A B : Type'} (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : _75297 = (term1220 A B).
Proof. exact (h1). Qed.
Lemma lem5962659 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5962660 {A B : Type'} (s : A -> Prop) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (_75297 s) = (term1221 A B s).
Proof. exact (MK_COMB (@lem5962658 A B _75297 h1) (@lem5962659 A s)). Qed.
Lemma lem5962661 {A B : Type'} (s : A -> Prop) : (term1221 A B s) = (term1222 A B s).
Proof. exact (eq_refl (term1221 A B s)). Qed.
Lemma lem5962662 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1223 A B _75297 s) = (term1223 A B _75297 s).
Proof. exact (eq_refl (term1223 A B _75297 s)). Qed.
Lemma lem5962663 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : ((_75297 s) = (term1221 A B s)) = ((_75297 s) = (term1222 A B s)).
Proof. exact (MK_COMB (@lem5962662 A B _75297 s) (@lem5962661 A B s)). Qed.
Lemma lem5962664 {A B : Type'} (s : A -> Prop) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (_75297 s) = (term1222 A B s).
Proof. exact (EQ_MP (@lem5962663 A B _75297 s) (@lem5962660 A B s _75297 h1)). Qed.
Lemma lem5962665 {A B : Type'} (t : type1413 A B) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5962666 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (_75297 s t) = (term1224 A B s t).
Proof. exact (MK_COMB (@lem5962664 A B s _75297 h1) (@lem5962665 A B t)). Qed.
Lemma lem5962667 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1224 A B s t) = (term1030 A B s t).
Proof. exact (eq_refl (term1224 A B s t)). Qed.
Lemma lem5962668 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1225 A B _75297 s t) = (term1225 A B _75297 s t).
Proof. exact (eq_refl (term1225 A B _75297 s t)). Qed.
Lemma lem5962669 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((_75297 s t) = (term1224 A B s t)) = ((_75297 s t) = (term1030 A B s t)).
Proof. exact (MK_COMB (@lem5962668 A B _75297 s t) (@lem5962667 A B s t)). Qed.
Lemma lem5962670 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (_75297 s t) = (term1030 A B s t).
Proof. exact (EQ_MP (@lem5962669 A B _75297 s t) (@lem5962666 A B s t _75297 h1)). Qed.
Lemma lem5962702 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term1059 A B s t p1 i p2 j) = (term1059 A B s t p1 i p2 j).
Proof. exact (eq_refl (term1059 A B s t p1 i p2 j)). Qed.
Lemma lem5962703 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term1061 A B s t p1 i p2) = (term1061 A B s t p1 i p2).
Proof. exact (fun_ext (fun j : B => @lem5962702 A B s t p1 i p2 j)). Qed.
Lemma lem5962704 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5962705 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term1063 A B s t p1 i p2) = (term1063 A B s t p1 i p2).
Proof. exact (MK_COMB (@lem5962704 B) (@lem5962703 A B s t p1 i p2)). Qed.
Lemma lem5962706 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1065 A B s t p1 p2) = (term1065 A B s t p1 p2).
Proof. exact (fun_ext (fun i : A => @lem5962705 A B s t p1 i p2)). Qed.
Lemma lem5962707 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5962708 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1066 A B s t p1 p2) = (term1066 A B s t p1 p2).
Proof. exact (MK_COMB (@lem5962707 A) (@lem5962706 A B s t p1 p2)). Qed.
Lemma lem5962731 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term1016 A B p1 p2 x t x') = (term1016 A B p1 p2 x t x').
Proof. exact (eq_refl (term1016 A B p1 p2 x t x')). Qed.
Lemma lem5962732 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1018 A B p1 p2 t x) = (term1018 A B p1 p2 t x).
Proof. exact (fun_ext (fun x' : B => @lem5962731 A B p1 p2 x' t x)). Qed.
Lemma lem5962733 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5962734 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1019 A B p1 p2 t x) = (term1019 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5962733 B) (@lem5962732 A B p1 p2 t x)). Qed.
Lemma lem5962735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5962736 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1021 A B p1 p2 t x) = (term1021 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5962735) (@lem5962734 A B p1 p2 t x)). Qed.
Lemma lem5962737 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1067 A B x s t p1 p2) = (term1067 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5962736 A B p1 p2 t x) (@lem5962708 A B s t p1 p2)). Qed.
Lemma lem5962738 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5962739 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1070 A B x s t p1 p2) = (term1070 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5962738) (@lem5962737 A B x s t p1 p2)). Qed.
Lemma lem5962740 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term1071 A B x s t p1) = (term1071 A B x s t p1).
Proof. exact (fun_ext (fun p2 : B => @lem5962739 A B x s t p1 p2)). Qed.
Lemma lem5962741 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5962742 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term1072 A B x s t p1) = (term1072 A B x s t p1).
Proof. exact (MK_COMB (@lem5962741 B) (@lem5962740 A B x s t p1)). Qed.
Lemma lem5962743 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1073 A B x s t) = (term1073 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem5962742 A B x s t p1)). Qed.
Lemma lem5962744 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962745 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1074 A B x s t) = (term1074 A B x s t).
Proof. exact (MK_COMB (@lem5962744 A) (@lem5962743 A B x s t)). Qed.
Lemma lem5962766 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) : (term892 A B x s t i) = (term892 A B x s t i).
Proof. exact (eq_refl (term892 A B x s t i)). Qed.
Lemma lem5962767 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term894 A B x s t) = (term894 A B x s t).
Proof. exact (fun_ext (fun i : A => @lem5962766 A B x s t i)). Qed.
Lemma lem5962768 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962769 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term895 A B x s t) = (term895 A B x s t).
Proof. exact (MK_COMB (@lem5962768 A) (@lem5962767 A B x s t)). Qed.
Lemma lem5962770 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5962771 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1082 A B x s t) = (term1082 A B x s t).
Proof. exact (MK_COMB (@lem5962770) (@lem5962769 A B x s t)). Qed.
Lemma lem5962772 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1084 A B x s t) = (term1084 A B x s t).
Proof. exact (MK_COMB (@lem5962771 A B x s t) (@lem5962745 A B x s t)). Qed.
Lemma lem5962777 {A : Type'} (s : A -> Prop) : (term642 A s) = (term642 A s).
Proof. exact (eq_refl (term642 A s)). Qed.
Lemma lem5962778 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1086 A B x s t) = (term1086 A B x s t).
Proof. exact (MK_COMB (@lem5962777 A s) (@lem5962772 A B x s t)). Qed.
Lemma lem5962787 {A : Type'} (x : A) (s : A -> Prop) : (term1087 A x s) = (term1087 A x s).
Proof. exact (eq_refl (term1087 A x s)). Qed.
Lemma lem5962788 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1089 A B x s t) = (term1089 A B x s t).
Proof. exact (MK_COMB (@lem5962787 A x s) (@lem5962778 A B x s t)). Qed.
Lemma lem5962803 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) (j : B) : (term1120 A B C f x i j) = (term1120 A B C f x i j).
Proof. exact (eq_refl (term1120 A B C f x i j)). Qed.
Lemma lem5962804 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1121 A B C f x i) = (term1121 A B C f x i).
Proof. exact (fun_ext (fun j : B => @lem5962803 A B C f x i j)). Qed.
Lemma lem5962805 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5962806 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1122 A B C f x i) = (term1122 A B C f x i).
Proof. exact (MK_COMB (@lem5962805 B) (@lem5962804 A B C f x i)). Qed.
Lemma lem5962807 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1123 A B C f x) = (term1123 A B C f x).
Proof. exact (fun_ext (fun i : A => @lem5962806 A B C f x i)). Qed.
Lemma lem5962808 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962809 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1124 A B C f x) = (term1124 A B C f x).
Proof. exact (MK_COMB (@lem5962808 A) (@lem5962807 A B C f x)). Qed.
Lemma lem5962810 {A B C : Type'} (x : type1412 A B C) : (term1125 A B C x) = (term1125 A B C x).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5962809 A B C f x)). Qed.
Lemma lem5962811 {A B C : Type'} : (@GABS ((prod A B) -> C)) = (@GABS ((prod A B) -> C)).
Proof. exact (eq_refl (@GABS ((prod A B) -> C))). Qed.
Lemma lem5962812 {A B C : Type'} (x : type1412 A B C) : (term759 A B C x) = (term759 A B C x).
Proof. exact (MK_COMB (@lem5962811 A B C) (@lem5962810 A B C x)). Qed.
Lemma lem5962814 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1030 A B s t) = (_75297 s t).
Proof. exact (SYM (@lem5962670 A B s t _75297 h1)). Qed.
Lemma lem5962815 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1030 A B s t) = (_75297 s t).
Proof. exact (@lem5962814 A B s t _75297 h1). Qed.
Lemma lem5962816 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem5962817 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term942 A B s t) = (term1226 A B _75297 s t).
Proof. exact (MK_COMB (@lem5962816 A B) (@lem5962815 A B s t _75297 h1)). Qed.
Lemma lem5962820 {A B C : Type'} (op : type1400 C) : (@iterate C (prod A B) op) = (@iterate C (prod A B) op).
Proof. exact (eq_refl (@iterate C (prod A B) op)). Qed.
Lemma lem5962821 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1130 A B C op s t) = (term1227 A B C op _75297 s t).
Proof. exact (MK_COMB (@lem5962820 A B C op) (@lem5962817 A B s t _75297 h1)). Qed.
Lemma lem5962822 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x : type1412 A B C) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term614 A B C op s t x) = (term1228 A B C op _75297 s t x).
Proof. exact (MK_COMB (@lem5962821 A B C op s t _75297 h1) (@lem5962812 A B C x)). Qed.
Lemma lem5962837 {A B C : Type'} (s : A -> Prop) (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1133 A B C s _75296 op t x) = (term1133 A B C s _75296 op t x).
Proof. exact (eq_refl (term1133 A B C s _75296 op t x)). Qed.
Lemma lem5962838 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x : type1412 A B C) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : ((term1131 A B C s _75296 op t x) = (term614 A B C op s t x)) = ((term1131 A B C s _75296 op t x) = (term1228 A B C op _75297 s t x)).
Proof. exact (MK_COMB (@lem5962837 A B C s _75296 op t x) (@lem5962822 A B C op s t x _75297 h1)). Qed.
Lemma lem5962839 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1134 A B C _75296 op s t) = (term1229 A B C _75296 op _75297 s t).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5962838 A B C _75296 op s t x _75297 h1)). Qed.
Lemma lem5962840 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5962841 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1135 A B C _75296 op s t) = (term1230 A B C _75296 op _75297 s t).
Proof. exact (MK_COMB (@lem5962840 A B C) (@lem5962839 A B C _75296 op s t _75297 h1)). Qed.
Lemma lem5962854 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : (term911 A B s t i) = (term911 A B s t i).
Proof. exact (eq_refl (term911 A B s t i)). Qed.
Lemma lem5962855 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term913 A B s t) = (term913 A B s t).
Proof. exact (fun_ext (fun i : A => @lem5962854 A B s t i)). Qed.
Lemma lem5962856 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962857 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term630 A B s t) = (term630 A B s t).
Proof. exact (MK_COMB (@lem5962856 A) (@lem5962855 A B s t)). Qed.
Lemma lem5962858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5962859 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1136 A B s t) = (term1136 A B s t).
Proof. exact (MK_COMB (@lem5962858) (@lem5962857 A B s t)). Qed.
Lemma lem5962860 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1137 A B C _75296 op s t) = (term1231 A B C _75296 op _75297 s t).
Proof. exact (MK_COMB (@lem5962859 A B s t) (@lem5962841 A B C _75296 op s t _75297 h1)). Qed.
Lemma lem5962861 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (s : A -> Prop) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1138 A B C _75296 op s) = (term1232 A B C _75296 op _75297 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5962860 A B C _75296 op s t _75297 h1)). Qed.
Lemma lem5962862 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5962863 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (s : A -> Prop) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1139 A B C _75296 op s) = (term1233 A B C _75296 op _75297 s).
Proof. exact (MK_COMB (@lem5962862 A B) (@lem5962861 A B C _75296 op s _75297 h1)). Qed.
Lemma lem5962864 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5962865 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (s : A -> Prop) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1140 A B C _75296 op s) = (term1234 A B C _75296 op _75297 s).
Proof. exact (MK_COMB (@lem5962864) (@lem5962863 A B C _75296 op s _75297 h1)). Qed.
Lemma lem5962866 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1141 A B C _75296 op x s t) = (term1235 A B C _75296 op _75297 x s t).
Proof. exact (MK_COMB (@lem5962865 A B C _75296 op s _75297 h1) (@lem5962788 A B x s t)). Qed.
Lemma lem5962871 {C : Type'} (op : type1400 C) : (term1093 C op) = (term1093 C op).
Proof. exact (eq_refl (term1093 C op)). Qed.
Lemma lem5962872 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1142 A B C _75296 op x s t) = (term1236 A B C _75296 op _75297 x s t).
Proof. exact (MK_COMB (@lem5962871 C op) (@lem5962866 A B C _75296 op x s t _75297 h1)). Qed.
Lemma lem5962873 {A B C : Type'} (_75296 : type877 A B C) (x : A) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1143 A B C _75296 x s t) = (term1237 A B C _75296 _75297 x s t).
Proof. exact (fun_ext (fun op : type1400 C => @lem5962872 A B C _75296 op x s t _75297 h1)). Qed.
Lemma lem5962874 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5962875 {A B C : Type'} (_75296 : type877 A B C) (x : A) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1144 A B C _75296 x s t) = (term1238 A B C _75296 _75297 x s t).
Proof. exact (MK_COMB (@lem5962874 C) (@lem5962873 A B C _75296 x s t _75297 h1)). Qed.
Lemma lem5962876 {A B C : Type'} (_75296 : type877 A B C) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1145 A B C _75296 s t) = (term1239 A B C _75296 _75297 s t).
Proof. exact (fun_ext (fun x : A => @lem5962875 A B C _75296 x s t _75297 h1)). Qed.
Lemma lem5962877 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962878 {A B C : Type'} (_75296 : type877 A B C) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1146 A B C _75296 s t) = (term1240 A B C _75296 _75297 s t).
Proof. exact (MK_COMB (@lem5962877 A) (@lem5962876 A B C _75296 s t _75297 h1)). Qed.
Lemma lem5962879 {A B C : Type'} (_75296 : type877 A B C) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1147 A B C _75296 t) = (term1241 A B C _75296 _75297 t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5962878 A B C _75296 s t _75297 h1)). Qed.
Lemma lem5962880 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5962881 {A B C : Type'} (_75296 : type877 A B C) (t : type1413 A B) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1148 A B C _75296 t) = (term1242 A B C _75296 _75297 t).
Proof. exact (MK_COMB (@lem5962880 A) (@lem5962879 A B C _75296 t _75297 h1)). Qed.
Lemma lem5962882 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1149 A B C _75296) = (term1243 A B C _75296 _75297).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5962881 A B C _75296 t _75297 h1)). Qed.
Lemma lem5962883 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5962884 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1150 A B C _75296) = (term1244 A B C _75296 _75297).
Proof. exact (MK_COMB (@lem5962883 A B) (@lem5962882 A B C _75296 _75297 h1)). Qed.
Lemma lem5962907 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (i : A) : ((_75296 op t x i) = (term818 A B C op t x i)) = ((_75296 op t x i) = (term818 A B C op t x i)).
Proof. exact (eq_refl ((_75296 op t x i) = (term818 A B C op t x i))). Qed.
Lemma lem5962908 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1208 A B C _75296 op t x) = (term1208 A B C _75296 op t x).
Proof. exact (fun_ext (fun i : A => @lem5962907 A B C _75296 op t x i)). Qed.
Lemma lem5962909 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5962910 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1209 A B C _75296 op t x) = (term1209 A B C _75296 op t x).
Proof. exact (MK_COMB (@lem5962909 A) (@lem5962908 A B C _75296 op t x)). Qed.
Lemma lem5962911 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1210 A B C _75296 op t) = (term1210 A B C _75296 op t).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5962910 A B C _75296 op t x)). Qed.
Lemma lem5962912 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5962913 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1211 A B C _75296 op t) = (term1211 A B C _75296 op t).
Proof. exact (MK_COMB (@lem5962912 A B C) (@lem5962911 A B C _75296 op t)). Qed.
Lemma lem5962914 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1212 A B C _75296 op) = (term1212 A B C _75296 op).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5962913 A B C _75296 op t)). Qed.
Lemma lem5962915 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5962916 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1213 A B C _75296 op) = (term1213 A B C _75296 op).
Proof. exact (MK_COMB (@lem5962915 A B) (@lem5962914 A B C _75296 op)). Qed.
Lemma lem5962917 {A B C : Type'} (_75296 : type877 A B C) : (term1214 A B C _75296) = (term1214 A B C _75296).
Proof. exact (fun_ext (fun op : type1400 C => @lem5962916 A B C _75296 op)). Qed.
Lemma lem5962918 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5962919 {A B C : Type'} (_75296 : type877 A B C) : (term1215 A B C _75296) = (term1215 A B C _75296).
Proof. exact (MK_COMB (@lem5962918 C) (@lem5962917 A B C _75296)). Qed.
Lemma lem5962920 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5962921 {A B C : Type'} (_75296 : type877 A B C) : (term1216 A B C _75296) = (term1216 A B C _75296).
Proof. exact (MK_COMB (@lem5962920) (@lem5962919 A B C _75296)). Qed.
Lemma lem5962922 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1217 A B C _75296) = (term1245 A B C _75296 _75297).
Proof. exact (MK_COMB (@lem5962921 A B C _75296) (@lem5962884 A B C _75296 _75297 h1)). Qed.
Lemma lem5962923 {A B C : Type'} (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1218 A B C) = (term1246 A B C _75297).
Proof. exact (fun_ext (fun _75296 : type877 A B C => @lem5962922 A B C _75296 _75297 h1)). Qed.
Lemma lem5962924 {A B C : Type'} : (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C)) = (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C)).
Proof. exact (eq_refl (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C))). Qed.
Lemma lem5962925 {A B C : Type'} (_75297 : type621 A B) (h1 : _75297 = (term1220 A B)) : (term1219 A B C) = (term1247 A B C _75297).
Proof. exact (MK_COMB (@lem5962924 A B C) (@lem5962923 A B C _75297 h1)). Qed.
Lemma lem5962926 {A B C : Type'} (_75297 : type621 A B) : term1248 A B C _75297.
Proof. exact (fun h0 : _75297 = (term1220 A B) => @lem5962925 A B C _75297 h0). Qed.
Lemma lem5962927 {A B C : Type'} : term1249 A B C.
Proof. exact (fun _75297 : type621 A B => @lem5962926 A B C _75297). Qed.
Lemma lem5962929 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term1153 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem5962930 {A B : Type'} (P : Prop) (c : type621 A B) (Q : type130 A B) : term1250 A B P c Q.
Proof. exact (@lem5962929 (type621 A B) P c Q). Qed.
Lemma lem5962931 {A B C : Type'} : term1251 A B C.
Proof. exact (@lem5962930 A B (term1219 A B C) (term1220 A B) (term1252 A B C)). Qed.
Lemma lem5962932 {A B C : Type'} (_75297 : type621 A B) : (term1253 A B C _75297) = (term1247 A B C _75297).
Proof. exact (eq_refl (term1253 A B C _75297)). Qed.
Lemma lem5962933 {A B C : Type'} : (term1254 A B C) = (term1254 A B C).
Proof. exact (eq_refl (term1254 A B C)). Qed.
Lemma lem5962934 {A B C : Type'} (_75297 : type621 A B) : ((term1219 A B C) = (term1253 A B C _75297)) = ((term1219 A B C) = (term1247 A B C _75297)).
Proof. exact (MK_COMB (@lem5962933 A B C) (@lem5962932 A B C _75297)). Qed.
Lemma lem5962935 {A B : Type'} (_75297 : type621 A B) : (term1255 A B _75297) = (term1255 A B _75297).
Proof. exact (eq_refl (term1255 A B _75297)). Qed.
Lemma lem5962936 {A B C : Type'} (_75297 : type621 A B) : (term1256 A B C _75297) = (term1248 A B C _75297).
Proof. exact (MK_COMB (@lem5962935 A B _75297) (@lem5962934 A B C _75297)). Qed.
Lemma lem5962937 {A B C : Type'} : (term1257 A B C) = (term1258 A B C).
Proof. exact (fun_ext (fun _75297 : type621 A B => @lem5962936 A B C _75297)). Qed.
Lemma lem5962938 {A B : Type'} : (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)) = (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop))). Qed.
Lemma lem5962939 {A B C : Type'} : (term1259 A B C) = (term1249 A B C).
Proof. exact (MK_COMB (@lem5962938 A B) (@lem5962937 A B C)). Qed.
Lemma lem5962940 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5962941 {A B C : Type'} : (term1260 A B C) = (term1261 A B C).
Proof. exact (MK_COMB (@lem5962940) (@lem5962939 A B C)). Qed.
Lemma lem5962942 {A B C : Type'} (_75297 : type621 A B) : (term1253 A B C _75297) = (term1247 A B C _75297).
Proof. exact (eq_refl (term1253 A B C _75297)). Qed.
Lemma lem5962943 {A B : Type'} (_75297 : type621 A B) : (term1255 A B _75297) = (term1255 A B _75297).
Proof. exact (eq_refl (term1255 A B _75297)). Qed.
Lemma lem5962944 {A B C : Type'} (_75297 : type621 A B) : (term1262 A B C _75297) = (term1263 A B C _75297).
Proof. exact (MK_COMB (@lem5962943 A B _75297) (@lem5962942 A B C _75297)). Qed.
Lemma lem5962945 {A B C : Type'} : (term1264 A B C) = (term1265 A B C).
Proof. exact (fun_ext (fun _75297 : type621 A B => @lem5962944 A B C _75297)). Qed.
Lemma lem5962946 {A B : Type'} : (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)) = (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop))). Qed.
Lemma lem5962947 {A B C : Type'} : (term1266 A B C) = (term1267 A B C).
Proof. exact (MK_COMB (@lem5962946 A B) (@lem5962945 A B C)). Qed.
Lemma lem5962948 {A B C : Type'} : (term1254 A B C) = (term1254 A B C).
Proof. exact (eq_refl (term1254 A B C)). Qed.
Lemma lem5962949 {A B C : Type'} : ((term1219 A B C) = (term1266 A B C)) = ((term1219 A B C) = (term1267 A B C)).
Proof. exact (MK_COMB (@lem5962948 A B C) (@lem5962947 A B C)). Qed.
Lemma lem5962950 {A B C : Type'} : (term1251 A B C) = (term1268 A B C).
Proof. exact (MK_COMB (@lem5962941 A B C) (@lem5962949 A B C)). Qed.
Lemma lem5962951 {A B C : Type'} : term1268 A B C.
Proof. exact (EQ_MP (@lem5962950 A B C) (@lem5962931 A B C)). Qed.
Lemma lem5962952 {A B C : Type'} : (term1219 A B C) = (term1267 A B C).
Proof. exact (@lem5962951 A B C (@lem5962927 A B C)). Qed.
Lemma lem5962954 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term1173 _3571 _3575 t)) = (term1174 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5962955 {A B : Type'} (s : type621 A B) (t : type621 A B) : (s = (term1269 A B t)) = (term1270 A B s t).
Proof. exact (@lem5962954 (type466 A B) (A -> Prop) s t). Qed.
Lemma lem5962956 {A B : Type'} (_75297 : type621 A B) : (_75297 = (term1271 A B)) = (term1272 A B _75297).
Proof. exact (@lem5962955 A B _75297 (term1220 A B)). Qed.
Lemma lem5962957 {A B : Type'} (s : A -> Prop) : (term1221 A B s) = (term1222 A B s).
Proof. exact (eq_refl (term1221 A B s)). Qed.
Lemma lem5962958 {A B : Type'} : (term1271 A B) = (term1220 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5962957 A B s)). Qed.
Lemma lem5962959 {A B : Type'} (_75297 : type621 A B) : (@eq ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop) _75297) = (@eq ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop) _75297).
Proof. exact (eq_refl (@eq ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop) _75297)). Qed.
Lemma lem5962960 {A B : Type'} (_75297 : type621 A B) : (_75297 = (term1271 A B)) = (_75297 = (term1220 A B)).
Proof. exact (MK_COMB (@lem5962959 A B _75297) (@lem5962958 A B)). Qed.
Lemma lem5962961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5962962 {A B : Type'} (_75297 : type621 A B) : (term1273 A B _75297) = (term1274 A B _75297).
Proof. exact (MK_COMB (@lem5962961) (@lem5962960 A B _75297)). Qed.
Lemma lem5962963 {A B : Type'} (s : A -> Prop) : (term1221 A B s) = (term1222 A B s).
Proof. exact (eq_refl (term1221 A B s)). Qed.
Lemma lem5962964 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1223 A B _75297 s) = (term1223 A B _75297 s).
Proof. exact (eq_refl (term1223 A B _75297 s)). Qed.
Lemma lem5962965 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : ((_75297 s) = (term1221 A B s)) = ((_75297 s) = (term1222 A B s)).
Proof. exact (MK_COMB (@lem5962964 A B _75297 s) (@lem5962963 A B s)). Qed.
Lemma lem5962966 {A B : Type'} (_75297 : type621 A B) : (term1275 A B _75297) = (term1276 A B _75297).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5962965 A B _75297 s)). Qed.
Lemma lem5962967 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5962968 {A B : Type'} (_75297 : type621 A B) : (term1272 A B _75297) = (term1277 A B _75297).
Proof. exact (MK_COMB (@lem5962967 A) (@lem5962966 A B _75297)). Qed.
Lemma lem5962969 {A B : Type'} (_75297 : type621 A B) : ((_75297 = (term1271 A B)) = (term1272 A B _75297)) = ((_75297 = (term1220 A B)) = (term1277 A B _75297)).
Proof. exact (MK_COMB (@lem5962962 A B _75297) (@lem5962968 A B _75297)). Qed.
Lemma lem5962970 {A B : Type'} (_75297 : type621 A B) : (_75297 = (term1220 A B)) = (term1277 A B _75297).
Proof. exact (EQ_MP (@lem5962969 A B _75297) (@lem5962956 A B _75297)). Qed.
Lemma lem5962972 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term1173 _3571 _3575 t)) = (term1174 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5962973 {A B : Type'} (s : type466 A B) (t : type466 A B) : (s = (term1278 A B t)) = (term1279 A B s t).
Proof. exact (@lem5962972 (type1210 A B) (type1413 A B) s t). Qed.
Lemma lem5962974 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : ((_75297 s) = (term1280 A B s)) = (term1281 A B _75297 s).
Proof. exact (@lem5962973 A B (_75297 s) (term1222 A B s)). Qed.
Lemma lem5962975 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1224 A B s t) = (term1030 A B s t).
Proof. exact (eq_refl (term1224 A B s t)). Qed.
Lemma lem5962976 {A B : Type'} (s : A -> Prop) : (term1280 A B s) = (term1222 A B s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5962975 A B s t)). Qed.
Lemma lem5962977 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1223 A B _75297 s) = (term1223 A B _75297 s).
Proof. exact (eq_refl (term1223 A B _75297 s)). Qed.
Lemma lem5962978 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : ((_75297 s) = (term1280 A B s)) = ((_75297 s) = (term1222 A B s)).
Proof. exact (MK_COMB (@lem5962977 A B _75297 s) (@lem5962976 A B s)). Qed.
Lemma lem5962979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5962980 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1282 A B _75297 s) = (term1283 A B _75297 s).
Proof. exact (MK_COMB (@lem5962979) (@lem5962978 A B _75297 s)). Qed.
Lemma lem5962981 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1224 A B s t) = (term1030 A B s t).
Proof. exact (eq_refl (term1224 A B s t)). Qed.
Lemma lem5962982 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1225 A B _75297 s t) = (term1225 A B _75297 s t).
Proof. exact (eq_refl (term1225 A B _75297 s t)). Qed.
Lemma lem5962983 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((_75297 s t) = (term1224 A B s t)) = ((_75297 s t) = (term1030 A B s t)).
Proof. exact (MK_COMB (@lem5962982 A B _75297 s t) (@lem5962981 A B s t)). Qed.
Lemma lem5962984 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1284 A B _75297 s) = (term1285 A B _75297 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5962983 A B _75297 s t)). Qed.
Lemma lem5962985 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5962986 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1281 A B _75297 s) = (term1286 A B _75297 s).
Proof. exact (MK_COMB (@lem5962985 A B) (@lem5962984 A B _75297 s)). Qed.
Lemma lem5962987 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (((_75297 s) = (term1280 A B s)) = (term1281 A B _75297 s)) = (((_75297 s) = (term1222 A B s)) = (term1286 A B _75297 s)).
Proof. exact (MK_COMB (@lem5962980 A B _75297 s) (@lem5962986 A B _75297 s)). Qed.
Lemma lem5962988 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : ((_75297 s) = (term1222 A B s)) = (term1286 A B _75297 s).
Proof. exact (EQ_MP (@lem5962987 A B _75297 s) (@lem5962974 A B _75297 s)). Qed.
Lemma lem5962990 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term1173 _3571 _3575 t)) = (term1174 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5962991 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (s = (term1287 A B t)) = (term1288 A B s t).
Proof. exact (@lem5962990 Prop (prod A B) s t). Qed.
Lemma lem5962992 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((_75297 s t) = (term1289 A B s t)) = (term1290 A B _75297 s t).
Proof. exact (@lem5962991 A B (_75297 s t) (term1030 A B s t)). Qed.
Lemma lem5962993 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1291 A B s t GEN_PVAR_241) = (term1028 A B GEN_PVAR_241 s t).
Proof. exact (eq_refl (term1291 A B s t GEN_PVAR_241)). Qed.
Lemma lem5962994 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1289 A B s t) = (term1030 A B s t).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5962993 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5962995 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1225 A B _75297 s t) = (term1225 A B _75297 s t).
Proof. exact (eq_refl (term1225 A B _75297 s t)). Qed.
Lemma lem5962996 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((_75297 s t) = (term1289 A B s t)) = ((_75297 s t) = (term1030 A B s t)).
Proof. exact (MK_COMB (@lem5962995 A B _75297 s t) (@lem5962994 A B s t)). Qed.
Lemma lem5962997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5962998 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1292 A B _75297 s t) = (term1293 A B _75297 s t).
Proof. exact (MK_COMB (@lem5962997) (@lem5962996 A B _75297 s t)). Qed.
Lemma lem5962999 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1291 A B s t GEN_PVAR_241) = (term1028 A B GEN_PVAR_241 s t).
Proof. exact (eq_refl (term1291 A B s t GEN_PVAR_241)). Qed.
Lemma lem5963000 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_241 : prod A B) : (term1294 A B _75297 s t GEN_PVAR_241) = (term1294 A B _75297 s t GEN_PVAR_241).
Proof. exact (eq_refl (term1294 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5963001 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((_75297 s t GEN_PVAR_241) = (term1291 A B s t GEN_PVAR_241)) = ((_75297 s t GEN_PVAR_241) = (term1028 A B GEN_PVAR_241 s t)).
Proof. exact (MK_COMB (@lem5963000 A B _75297 s t GEN_PVAR_241) (@lem5962999 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5963002 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1295 A B _75297 s t) = (term1296 A B _75297 s t).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5963001 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5963003 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5963004 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1290 A B _75297 s t) = (term1297 A B _75297 s t).
Proof. exact (MK_COMB (@lem5963003 A B) (@lem5963002 A B _75297 s t)). Qed.
Lemma lem5963005 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (((_75297 s t) = (term1289 A B s t)) = (term1290 A B _75297 s t)) = (((_75297 s t) = (term1030 A B s t)) = (term1297 A B _75297 s t)).
Proof. exact (MK_COMB (@lem5962998 A B _75297 s t) (@lem5963004 A B _75297 s t)). Qed.
Lemma lem5963006 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((_75297 s t) = (term1030 A B s t)) = (term1297 A B _75297 s t).
Proof. exact (EQ_MP (@lem5963005 A B _75297 s t) (@lem5962992 A B _75297 s t)). Qed.
Lemma lem5963007 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((_75297 s t GEN_PVAR_241) = (term1028 A B GEN_PVAR_241 s t)) = ((_75297 s t GEN_PVAR_241) = (term1028 A B GEN_PVAR_241 s t)).
Proof. exact (eq_refl ((_75297 s t GEN_PVAR_241) = (term1028 A B GEN_PVAR_241 s t))). Qed.
Lemma lem5963008 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1296 A B _75297 s t) = (term1296 A B _75297 s t).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5963007 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5963009 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5963010 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1297 A B _75297 s t) = (term1297 A B _75297 s t).
Proof. exact (MK_COMB (@lem5963009 A B) (@lem5963008 A B _75297 s t)). Qed.
Lemma lem5963011 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((_75297 s t) = (term1030 A B s t)) = (term1297 A B _75297 s t).
Proof. exact (TRANS (@lem5963006 A B _75297 s t) (@lem5963010 A B _75297 s t)). Qed.
Lemma lem5963012 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1285 A B _75297 s) = (term1298 A B _75297 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5963011 A B _75297 s t)). Qed.
Lemma lem5963013 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5963014 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1286 A B _75297 s) = (term1299 A B _75297 s).
Proof. exact (MK_COMB (@lem5963013 A B) (@lem5963012 A B _75297 s)). Qed.
Lemma lem5963015 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : ((_75297 s) = (term1222 A B s)) = (term1299 A B _75297 s).
Proof. exact (TRANS (@lem5962988 A B _75297 s) (@lem5963014 A B _75297 s)). Qed.
Lemma lem5963016 {A B : Type'} (_75297 : type621 A B) : (term1276 A B _75297) = (term1300 A B _75297).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5963015 A B _75297 s)). Qed.
Lemma lem5963017 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5963018 {A B : Type'} (_75297 : type621 A B) : (term1277 A B _75297) = (term1301 A B _75297).
Proof. exact (MK_COMB (@lem5963017 A) (@lem5963016 A B _75297)). Qed.
Lemma lem5963019 {A B : Type'} (_75297 : type621 A B) : (_75297 = (term1220 A B)) = (term1301 A B _75297).
Proof. exact (TRANS (@lem5962970 A B _75297) (@lem5963018 A B _75297)). Qed.
Lemma lem5963020 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963021 {A B : Type'} (_75297 : type621 A B) : (term1255 A B _75297) = (term1302 A B _75297).
Proof. exact (MK_COMB (@lem5963020) (@lem5963019 A B _75297)). Qed.
Lemma lem5963022 {A B C : Type'} (_75297 : type621 A B) : (term1247 A B C _75297) = (term1247 A B C _75297).
Proof. exact (eq_refl (term1247 A B C _75297)). Qed.
Lemma lem5963023 {A B C : Type'} (_75297 : type621 A B) : (term1263 A B C _75297) = (term1303 A B C _75297).
Proof. exact (MK_COMB (@lem5963021 A B _75297) (@lem5963022 A B C _75297)). Qed.
Lemma lem5963024 {A B C : Type'} : (term1265 A B C) = (term1304 A B C).
Proof. exact (fun_ext (fun _75297 : type621 A B => @lem5963023 A B C _75297)). Qed.
Lemma lem5963025 {A B : Type'} : (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)) = (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop))). Qed.
Lemma lem5963026 {A B C : Type'} : (term1267 A B C) = (term1305 A B C).
Proof. exact (MK_COMB (@lem5963025 A B) (@lem5963024 A B C)). Qed.
Lemma lem5963027 {A B C : Type'} : (term1254 A B C) = (term1254 A B C).
Proof. exact (eq_refl (term1254 A B C)). Qed.
Lemma lem5963028 {A B C : Type'} : ((term1219 A B C) = (term1267 A B C)) = ((term1219 A B C) = (term1305 A B C)).
Proof. exact (MK_COMB (@lem5963027 A B C) (@lem5963026 A B C)). Qed.
Lemma lem5963029 {A B C : Type'} : (term1219 A B C) = (term1305 A B C).
Proof. exact (EQ_MP (@lem5963028 A B C) (@lem5962952 A B C)). Qed.
Lemma lem5963030 {A B C : Type'} (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : _75298 = (term1306 A B C).
Proof. exact (h1). Qed.
Lemma lem5963031 {A B C : Type'} (x : type1412 A B C) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5963032 {A B C : Type'} (x : type1412 A B C) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (_75298 x) = (term1307 A B C x).
Proof. exact (MK_COMB (@lem5963030 A B C _75298 h1) (@lem5963031 A B C x)). Qed.
Lemma lem5963033 {A B C : Type'} (x : type1412 A B C) : (term1307 A B C x) = (term1125 A B C x).
Proof. exact (eq_refl (term1307 A B C x)). Qed.
Lemma lem5963034 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1308 A B C _75298 x) = (term1308 A B C _75298 x).
Proof. exact (eq_refl (term1308 A B C _75298 x)). Qed.
Lemma lem5963035 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : ((_75298 x) = (term1307 A B C x)) = ((_75298 x) = (term1125 A B C x)).
Proof. exact (MK_COMB (@lem5963034 A B C _75298 x) (@lem5963033 A B C x)). Qed.
Lemma lem5963036 {A B C : Type'} (x : type1412 A B C) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (_75298 x) = (term1125 A B C x).
Proof. exact (EQ_MP (@lem5963035 A B C _75298 x) (@lem5963032 A B C x _75298 h1)). Qed.
Lemma lem5963068 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term1059 A B s t p1 i p2 j) = (term1059 A B s t p1 i p2 j).
Proof. exact (eq_refl (term1059 A B s t p1 i p2 j)). Qed.
Lemma lem5963069 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term1061 A B s t p1 i p2) = (term1061 A B s t p1 i p2).
Proof. exact (fun_ext (fun j : B => @lem5963068 A B s t p1 i p2 j)). Qed.
Lemma lem5963070 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5963071 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term1063 A B s t p1 i p2) = (term1063 A B s t p1 i p2).
Proof. exact (MK_COMB (@lem5963070 B) (@lem5963069 A B s t p1 i p2)). Qed.
Lemma lem5963072 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1065 A B s t p1 p2) = (term1065 A B s t p1 p2).
Proof. exact (fun_ext (fun i : A => @lem5963071 A B s t p1 i p2)). Qed.
Lemma lem5963073 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5963074 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1066 A B s t p1 p2) = (term1066 A B s t p1 p2).
Proof. exact (MK_COMB (@lem5963073 A) (@lem5963072 A B s t p1 p2)). Qed.
Lemma lem5963097 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term1016 A B p1 p2 x t x') = (term1016 A B p1 p2 x t x').
Proof. exact (eq_refl (term1016 A B p1 p2 x t x')). Qed.
Lemma lem5963098 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1018 A B p1 p2 t x) = (term1018 A B p1 p2 t x).
Proof. exact (fun_ext (fun x' : B => @lem5963097 A B p1 p2 x' t x)). Qed.
Lemma lem5963099 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5963100 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1019 A B p1 p2 t x) = (term1019 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5963099 B) (@lem5963098 A B p1 p2 t x)). Qed.
Lemma lem5963101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5963102 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1021 A B p1 p2 t x) = (term1021 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5963101) (@lem5963100 A B p1 p2 t x)). Qed.
Lemma lem5963103 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1067 A B x s t p1 p2) = (term1067 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5963102 A B p1 p2 t x) (@lem5963074 A B s t p1 p2)). Qed.
Lemma lem5963104 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5963105 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1070 A B x s t p1 p2) = (term1070 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5963104) (@lem5963103 A B x s t p1 p2)). Qed.
Lemma lem5963106 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term1071 A B x s t p1) = (term1071 A B x s t p1).
Proof. exact (fun_ext (fun p2 : B => @lem5963105 A B x s t p1 p2)). Qed.
Lemma lem5963107 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5963108 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term1072 A B x s t p1) = (term1072 A B x s t p1).
Proof. exact (MK_COMB (@lem5963107 B) (@lem5963106 A B x s t p1)). Qed.
Lemma lem5963109 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1073 A B x s t) = (term1073 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem5963108 A B x s t p1)). Qed.
Lemma lem5963110 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5963111 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1074 A B x s t) = (term1074 A B x s t).
Proof. exact (MK_COMB (@lem5963110 A) (@lem5963109 A B x s t)). Qed.
Lemma lem5963132 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) : (term892 A B x s t i) = (term892 A B x s t i).
Proof. exact (eq_refl (term892 A B x s t i)). Qed.
Lemma lem5963133 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term894 A B x s t) = (term894 A B x s t).
Proof. exact (fun_ext (fun i : A => @lem5963132 A B x s t i)). Qed.
Lemma lem5963134 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5963135 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term895 A B x s t) = (term895 A B x s t).
Proof. exact (MK_COMB (@lem5963134 A) (@lem5963133 A B x s t)). Qed.
Lemma lem5963136 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963137 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1082 A B x s t) = (term1082 A B x s t).
Proof. exact (MK_COMB (@lem5963136) (@lem5963135 A B x s t)). Qed.
Lemma lem5963138 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1084 A B x s t) = (term1084 A B x s t).
Proof. exact (MK_COMB (@lem5963137 A B x s t) (@lem5963111 A B x s t)). Qed.
Lemma lem5963143 {A : Type'} (s : A -> Prop) : (term642 A s) = (term642 A s).
Proof. exact (eq_refl (term642 A s)). Qed.
Lemma lem5963144 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1086 A B x s t) = (term1086 A B x s t).
Proof. exact (MK_COMB (@lem5963143 A s) (@lem5963138 A B x s t)). Qed.
Lemma lem5963153 {A : Type'} (x : A) (s : A -> Prop) : (term1087 A x s) = (term1087 A x s).
Proof. exact (eq_refl (term1087 A x s)). Qed.
Lemma lem5963154 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1089 A B x s t) = (term1089 A B x s t).
Proof. exact (MK_COMB (@lem5963153 A x s) (@lem5963144 A B x s t)). Qed.
Lemma lem5963156 {A B C : Type'} (x : type1412 A B C) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1125 A B C x) = (_75298 x).
Proof. exact (SYM (@lem5963036 A B C x _75298 h1)). Qed.
Lemma lem5963157 {A B C : Type'} (x : type1412 A B C) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1125 A B C x) = (_75298 x).
Proof. exact (@lem5963156 A B C x _75298 h1). Qed.
Lemma lem5963158 {A B C : Type'} : (@GABS ((prod A B) -> C)) = (@GABS ((prod A B) -> C)).
Proof. exact (eq_refl (@GABS ((prod A B) -> C))). Qed.
Lemma lem5963159 {A B C : Type'} (x : type1412 A B C) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term759 A B C x) = (term1309 A B C _75298 x).
Proof. exact (MK_COMB (@lem5963158 A B C) (@lem5963157 A B C x _75298 h1)). Qed.
Lemma lem5963170 {A B C : Type'} (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1227 A B C op _75297 s t) = (term1227 A B C op _75297 s t).
Proof. exact (eq_refl (term1227 A B C op _75297 s t)). Qed.
Lemma lem5963171 {A B C : Type'} (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1412 A B C) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1228 A B C op _75297 s t x) = (term1310 A B C op _75297 s t _75298 x).
Proof. exact (MK_COMB (@lem5963170 A B C op _75297 s t) (@lem5963159 A B C x _75298 h1)). Qed.
Lemma lem5963186 {A B C : Type'} (s : A -> Prop) (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1133 A B C s _75296 op t x) = (term1133 A B C s _75296 op t x).
Proof. exact (eq_refl (term1133 A B C s _75296 op t x)). Qed.
Lemma lem5963187 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1412 A B C) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : ((term1131 A B C s _75296 op t x) = (term1228 A B C op _75297 s t x)) = ((term1131 A B C s _75296 op t x) = (term1310 A B C op _75297 s t _75298 x)).
Proof. exact (MK_COMB (@lem5963186 A B C s _75296 op t x) (@lem5963171 A B C op _75297 s t x _75298 h1)). Qed.
Lemma lem5963188 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1229 A B C _75296 op _75297 s t) = (term1311 A B C _75296 op _75297 s t _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5963187 A B C _75296 op _75297 s t x _75298 h1)). Qed.
Lemma lem5963189 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5963190 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1230 A B C _75296 op _75297 s t) = (term1312 A B C _75296 op _75297 s t _75298).
Proof. exact (MK_COMB (@lem5963189 A B C) (@lem5963188 A B C _75296 op _75297 s t _75298 h1)). Qed.
Lemma lem5963203 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : (term911 A B s t i) = (term911 A B s t i).
Proof. exact (eq_refl (term911 A B s t i)). Qed.
Lemma lem5963204 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term913 A B s t) = (term913 A B s t).
Proof. exact (fun_ext (fun i : A => @lem5963203 A B s t i)). Qed.
Lemma lem5963205 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5963206 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term630 A B s t) = (term630 A B s t).
Proof. exact (MK_COMB (@lem5963205 A) (@lem5963204 A B s t)). Qed.
Lemma lem5963207 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963208 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1136 A B s t) = (term1136 A B s t).
Proof. exact (MK_COMB (@lem5963207) (@lem5963206 A B s t)). Qed.
Lemma lem5963209 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1231 A B C _75296 op _75297 s t) = (term1313 A B C _75296 op _75297 s t _75298).
Proof. exact (MK_COMB (@lem5963208 A B s t) (@lem5963190 A B C _75296 op _75297 s t _75298 h1)). Qed.
Lemma lem5963210 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1232 A B C _75296 op _75297 s) = (term1314 A B C _75296 op _75297 s _75298).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5963209 A B C _75296 op _75297 s t _75298 h1)). Qed.
Lemma lem5963211 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5963212 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1233 A B C _75296 op _75297 s) = (term1315 A B C _75296 op _75297 s _75298).
Proof. exact (MK_COMB (@lem5963211 A B) (@lem5963210 A B C _75296 op _75297 s _75298 h1)). Qed.
Lemma lem5963213 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963214 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1234 A B C _75296 op _75297 s) = (term1316 A B C _75296 op _75297 s _75298).
Proof. exact (MK_COMB (@lem5963213) (@lem5963212 A B C _75296 op _75297 s _75298 h1)). Qed.
Lemma lem5963215 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (x : A) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1235 A B C _75296 op _75297 x s t) = (term1317 A B C _75296 op _75297 _75298 x s t).
Proof. exact (MK_COMB (@lem5963214 A B C _75296 op _75297 s _75298 h1) (@lem5963154 A B x s t)). Qed.
Lemma lem5963220 {C : Type'} (op : type1400 C) : (term1093 C op) = (term1093 C op).
Proof. exact (eq_refl (term1093 C op)). Qed.
Lemma lem5963221 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (x : A) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1236 A B C _75296 op _75297 x s t) = (term1318 A B C _75296 op _75297 _75298 x s t).
Proof. exact (MK_COMB (@lem5963220 C op) (@lem5963215 A B C _75296 op _75297 x s t _75298 h1)). Qed.
Lemma lem5963222 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (x : A) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1237 A B C _75296 _75297 x s t) = (term1319 A B C _75296 _75297 _75298 x s t).
Proof. exact (fun_ext (fun op : type1400 C => @lem5963221 A B C _75296 op _75297 x s t _75298 h1)). Qed.
Lemma lem5963223 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5963224 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (x : A) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1238 A B C _75296 _75297 x s t) = (term1320 A B C _75296 _75297 _75298 x s t).
Proof. exact (MK_COMB (@lem5963223 C) (@lem5963222 A B C _75296 _75297 x s t _75298 h1)). Qed.
Lemma lem5963225 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1239 A B C _75296 _75297 s t) = (term1321 A B C _75296 _75297 _75298 s t).
Proof. exact (fun_ext (fun x : A => @lem5963224 A B C _75296 _75297 x s t _75298 h1)). Qed.
Lemma lem5963226 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5963227 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1240 A B C _75296 _75297 s t) = (term1322 A B C _75296 _75297 _75298 s t).
Proof. exact (MK_COMB (@lem5963226 A) (@lem5963225 A B C _75296 _75297 s t _75298 h1)). Qed.
Lemma lem5963228 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (t : type1413 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1241 A B C _75296 _75297 t) = (term1323 A B C _75296 _75297 _75298 t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5963227 A B C _75296 _75297 s t _75298 h1)). Qed.
Lemma lem5963229 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5963230 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (t : type1413 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1242 A B C _75296 _75297 t) = (term1324 A B C _75296 _75297 _75298 t).
Proof. exact (MK_COMB (@lem5963229 A) (@lem5963228 A B C _75296 _75297 t _75298 h1)). Qed.
Lemma lem5963231 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1243 A B C _75296 _75297) = (term1325 A B C _75296 _75297 _75298).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5963230 A B C _75296 _75297 t _75298 h1)). Qed.
Lemma lem5963232 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5963233 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1244 A B C _75296 _75297) = (term1326 A B C _75296 _75297 _75298).
Proof. exact (MK_COMB (@lem5963232 A B) (@lem5963231 A B C _75296 _75297 _75298 h1)). Qed.
Lemma lem5963256 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (i : A) : ((_75296 op t x i) = (term818 A B C op t x i)) = ((_75296 op t x i) = (term818 A B C op t x i)).
Proof. exact (eq_refl ((_75296 op t x i) = (term818 A B C op t x i))). Qed.
Lemma lem5963257 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1208 A B C _75296 op t x) = (term1208 A B C _75296 op t x).
Proof. exact (fun_ext (fun i : A => @lem5963256 A B C _75296 op t x i)). Qed.
Lemma lem5963258 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5963259 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1209 A B C _75296 op t x) = (term1209 A B C _75296 op t x).
Proof. exact (MK_COMB (@lem5963258 A) (@lem5963257 A B C _75296 op t x)). Qed.
Lemma lem5963260 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1210 A B C _75296 op t) = (term1210 A B C _75296 op t).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5963259 A B C _75296 op t x)). Qed.
Lemma lem5963261 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5963262 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1211 A B C _75296 op t) = (term1211 A B C _75296 op t).
Proof. exact (MK_COMB (@lem5963261 A B C) (@lem5963260 A B C _75296 op t)). Qed.
Lemma lem5963263 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1212 A B C _75296 op) = (term1212 A B C _75296 op).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5963262 A B C _75296 op t)). Qed.
Lemma lem5963264 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5963265 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1213 A B C _75296 op) = (term1213 A B C _75296 op).
Proof. exact (MK_COMB (@lem5963264 A B) (@lem5963263 A B C _75296 op)). Qed.
Lemma lem5963266 {A B C : Type'} (_75296 : type877 A B C) : (term1214 A B C _75296) = (term1214 A B C _75296).
Proof. exact (fun_ext (fun op : type1400 C => @lem5963265 A B C _75296 op)). Qed.
Lemma lem5963267 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5963268 {A B C : Type'} (_75296 : type877 A B C) : (term1215 A B C _75296) = (term1215 A B C _75296).
Proof. exact (MK_COMB (@lem5963267 C) (@lem5963266 A B C _75296)). Qed.
Lemma lem5963269 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963270 {A B C : Type'} (_75296 : type877 A B C) : (term1216 A B C _75296) = (term1216 A B C _75296).
Proof. exact (MK_COMB (@lem5963269) (@lem5963268 A B C _75296)). Qed.
Lemma lem5963271 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1245 A B C _75296 _75297) = (term1327 A B C _75296 _75297 _75298).
Proof. exact (MK_COMB (@lem5963270 A B C _75296) (@lem5963233 A B C _75296 _75297 _75298 h1)). Qed.
Lemma lem5963272 {A B C : Type'} (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1246 A B C _75297) = (term1328 A B C _75297 _75298).
Proof. exact (fun_ext (fun _75296 : type877 A B C => @lem5963271 A B C _75296 _75297 _75298 h1)). Qed.
Lemma lem5963273 {A B C : Type'} : (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C)) = (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C)).
Proof. exact (eq_refl (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C))). Qed.
Lemma lem5963274 {A B C : Type'} (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1247 A B C _75297) = (term1329 A B C _75297 _75298).
Proof. exact (MK_COMB (@lem5963273 A B C) (@lem5963272 A B C _75297 _75298 h1)). Qed.
Lemma lem5963299 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) (j : B) : (term1126 A B GEN_PVAR_241 s t i j) = (term1126 A B GEN_PVAR_241 s t i j).
Proof. exact (eq_refl (term1126 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5963300 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1127 A B GEN_PVAR_241 s t i) = (term1127 A B GEN_PVAR_241 s t i).
Proof. exact (fun_ext (fun j : B => @lem5963299 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5963301 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5963302 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1128 A B GEN_PVAR_241 s t i) = (term1128 A B GEN_PVAR_241 s t i).
Proof. exact (MK_COMB (@lem5963301 B) (@lem5963300 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5963303 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1129 A B GEN_PVAR_241 s t) = (term1129 A B GEN_PVAR_241 s t).
Proof. exact (fun_ext (fun i : A => @lem5963302 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5963304 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5963305 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1028 A B GEN_PVAR_241 s t) = (term1028 A B GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5963304 A) (@lem5963303 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5963314 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_241 : prod A B) : (term1294 A B _75297 s t GEN_PVAR_241) = (term1294 A B _75297 s t GEN_PVAR_241).
Proof. exact (eq_refl (term1294 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5963315 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((_75297 s t GEN_PVAR_241) = (term1028 A B GEN_PVAR_241 s t)) = ((_75297 s t GEN_PVAR_241) = (term1028 A B GEN_PVAR_241 s t)).
Proof. exact (MK_COMB (@lem5963314 A B _75297 s t GEN_PVAR_241) (@lem5963305 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5963316 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1296 A B _75297 s t) = (term1296 A B _75297 s t).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5963315 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5963317 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5963318 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1297 A B _75297 s t) = (term1297 A B _75297 s t).
Proof. exact (MK_COMB (@lem5963317 A B) (@lem5963316 A B _75297 s t)). Qed.
Lemma lem5963319 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1298 A B _75297 s) = (term1298 A B _75297 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5963318 A B _75297 s t)). Qed.
Lemma lem5963320 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5963321 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1299 A B _75297 s) = (term1299 A B _75297 s).
Proof. exact (MK_COMB (@lem5963320 A B) (@lem5963319 A B _75297 s)). Qed.
Lemma lem5963322 {A B : Type'} (_75297 : type621 A B) : (term1300 A B _75297) = (term1300 A B _75297).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5963321 A B _75297 s)). Qed.
Lemma lem5963323 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5963324 {A B : Type'} (_75297 : type621 A B) : (term1301 A B _75297) = (term1301 A B _75297).
Proof. exact (MK_COMB (@lem5963323 A) (@lem5963322 A B _75297)). Qed.
Lemma lem5963325 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963326 {A B : Type'} (_75297 : type621 A B) : (term1302 A B _75297) = (term1302 A B _75297).
Proof. exact (MK_COMB (@lem5963325) (@lem5963324 A B _75297)). Qed.
Lemma lem5963327 {A B C : Type'} (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1303 A B C _75297) = (term1330 A B C _75297 _75298).
Proof. exact (MK_COMB (@lem5963326 A B _75297) (@lem5963274 A B C _75297 _75298 h1)). Qed.
Lemma lem5963328 {A B C : Type'} (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1304 A B C) = (term1331 A B C _75298).
Proof. exact (fun_ext (fun _75297 : type621 A B => @lem5963327 A B C _75297 _75298 h1)). Qed.
Lemma lem5963329 {A B : Type'} : (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)) = (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop))). Qed.
Lemma lem5963330 {A B C : Type'} (_75298 : type441 A B C) (h1 : _75298 = (term1306 A B C)) : (term1305 A B C) = (term1332 A B C _75298).
Proof. exact (MK_COMB (@lem5963329 A B) (@lem5963328 A B C _75298 h1)). Qed.
Lemma lem5963331 {A B C : Type'} (_75298 : type441 A B C) : term1333 A B C _75298.
Proof. exact (fun h0 : _75298 = (term1306 A B C) => @lem5963330 A B C _75298 h0). Qed.
Lemma lem5963332 {A B C : Type'} : term1334 A B C.
Proof. exact (fun _75298 : type441 A B C => @lem5963331 A B C _75298). Qed.
Lemma lem5963334 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term1153 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem5963335 {A B C : Type'} (P : Prop) (c : type441 A B C) (Q : type88 A B C) : term1335 A B C P c Q.
Proof. exact (@lem5963334 (type441 A B C) P c Q). Qed.
Lemma lem5963336 {A B C : Type'} : term1336 A B C.
Proof. exact (@lem5963335 A B C (term1305 A B C) (term1306 A B C) (term1337 A B C)). Qed.
Lemma lem5963337 {A B C : Type'} (_75298 : type441 A B C) : (term1338 A B C _75298) = (term1332 A B C _75298).
Proof. exact (eq_refl (term1338 A B C _75298)). Qed.
Lemma lem5963338 {A B C : Type'} : (term1339 A B C) = (term1339 A B C).
Proof. exact (eq_refl (term1339 A B C)). Qed.
Lemma lem5963339 {A B C : Type'} (_75298 : type441 A B C) : ((term1305 A B C) = (term1338 A B C _75298)) = ((term1305 A B C) = (term1332 A B C _75298)).
Proof. exact (MK_COMB (@lem5963338 A B C) (@lem5963337 A B C _75298)). Qed.
Lemma lem5963340 {A B C : Type'} (_75298 : type441 A B C) : (term1340 A B C _75298) = (term1340 A B C _75298).
Proof. exact (eq_refl (term1340 A B C _75298)). Qed.
Lemma lem5963341 {A B C : Type'} (_75298 : type441 A B C) : (term1341 A B C _75298) = (term1333 A B C _75298).
Proof. exact (MK_COMB (@lem5963340 A B C _75298) (@lem5963339 A B C _75298)). Qed.
Lemma lem5963342 {A B C : Type'} : (term1342 A B C) = (term1343 A B C).
Proof. exact (fun_ext (fun _75298 : type441 A B C => @lem5963341 A B C _75298)). Qed.
Lemma lem5963343 {A B C : Type'} : (@all ((A -> B -> C) -> ((prod A B) -> C) -> Prop)) = (@all ((A -> B -> C) -> ((prod A B) -> C) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B -> C) -> ((prod A B) -> C) -> Prop))). Qed.
Lemma lem5963344 {A B C : Type'} : (term1344 A B C) = (term1334 A B C).
Proof. exact (MK_COMB (@lem5963343 A B C) (@lem5963342 A B C)). Qed.
Lemma lem5963345 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963346 {A B C : Type'} : (term1345 A B C) = (term1346 A B C).
Proof. exact (MK_COMB (@lem5963345) (@lem5963344 A B C)). Qed.
Lemma lem5963347 {A B C : Type'} (_75298 : type441 A B C) : (term1338 A B C _75298) = (term1332 A B C _75298).
Proof. exact (eq_refl (term1338 A B C _75298)). Qed.
Lemma lem5963348 {A B C : Type'} (_75298 : type441 A B C) : (term1340 A B C _75298) = (term1340 A B C _75298).
Proof. exact (eq_refl (term1340 A B C _75298)). Qed.
Lemma lem5963349 {A B C : Type'} (_75298 : type441 A B C) : (term1347 A B C _75298) = (term1348 A B C _75298).
Proof. exact (MK_COMB (@lem5963348 A B C _75298) (@lem5963347 A B C _75298)). Qed.
Lemma lem5963350 {A B C : Type'} : (term1349 A B C) = (term1350 A B C).
Proof. exact (fun_ext (fun _75298 : type441 A B C => @lem5963349 A B C _75298)). Qed.
Lemma lem5963351 {A B C : Type'} : (@all ((A -> B -> C) -> ((prod A B) -> C) -> Prop)) = (@all ((A -> B -> C) -> ((prod A B) -> C) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B -> C) -> ((prod A B) -> C) -> Prop))). Qed.
Lemma lem5963352 {A B C : Type'} : (term1351 A B C) = (term1352 A B C).
Proof. exact (MK_COMB (@lem5963351 A B C) (@lem5963350 A B C)). Qed.
Lemma lem5963353 {A B C : Type'} : (term1339 A B C) = (term1339 A B C).
Proof. exact (eq_refl (term1339 A B C)). Qed.
Lemma lem5963354 {A B C : Type'} : ((term1305 A B C) = (term1351 A B C)) = ((term1305 A B C) = (term1352 A B C)).
Proof. exact (MK_COMB (@lem5963353 A B C) (@lem5963352 A B C)). Qed.
Lemma lem5963355 {A B C : Type'} : (term1336 A B C) = (term1353 A B C).
Proof. exact (MK_COMB (@lem5963346 A B C) (@lem5963354 A B C)). Qed.
Lemma lem5963356 {A B C : Type'} : term1353 A B C.
Proof. exact (EQ_MP (@lem5963355 A B C) (@lem5963336 A B C)). Qed.
Lemma lem5963357 {A B C : Type'} : (term1305 A B C) = (term1352 A B C).
Proof. exact (@lem5963356 A B C (@lem5963332 A B C)). Qed.
Lemma lem5963359 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term1173 _3571 _3575 t)) = (term1174 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5963360 {A B C : Type'} (s : type441 A B C) (t : type441 A B C) : (s = (term1354 A B C t)) = (term1355 A B C s t).
Proof. exact (@lem5963359 (type322 A B C) (type1412 A B C) s t). Qed.
Lemma lem5963361 {A B C : Type'} (_75298 : type441 A B C) : (_75298 = (term1356 A B C)) = (term1357 A B C _75298).
Proof. exact (@lem5963360 A B C _75298 (term1306 A B C)). Qed.
Lemma lem5963362 {A B C : Type'} (x : type1412 A B C) : (term1307 A B C x) = (term1125 A B C x).
Proof. exact (eq_refl (term1307 A B C x)). Qed.
Lemma lem5963363 {A B C : Type'} : (term1356 A B C) = (term1306 A B C).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5963362 A B C x)). Qed.
Lemma lem5963364 {A B C : Type'} (_75298 : type441 A B C) : (@eq ((A -> B -> C) -> ((prod A B) -> C) -> Prop) _75298) = (@eq ((A -> B -> C) -> ((prod A B) -> C) -> Prop) _75298).
Proof. exact (eq_refl (@eq ((A -> B -> C) -> ((prod A B) -> C) -> Prop) _75298)). Qed.
Lemma lem5963365 {A B C : Type'} (_75298 : type441 A B C) : (_75298 = (term1356 A B C)) = (_75298 = (term1306 A B C)).
Proof. exact (MK_COMB (@lem5963364 A B C _75298) (@lem5963363 A B C)). Qed.
Lemma lem5963366 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5963367 {A B C : Type'} (_75298 : type441 A B C) : (term1358 A B C _75298) = (term1359 A B C _75298).
Proof. exact (MK_COMB (@lem5963366) (@lem5963365 A B C _75298)). Qed.
Lemma lem5963368 {A B C : Type'} (x : type1412 A B C) : (term1307 A B C x) = (term1125 A B C x).
Proof. exact (eq_refl (term1307 A B C x)). Qed.
Lemma lem5963369 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1308 A B C _75298 x) = (term1308 A B C _75298 x).
Proof. exact (eq_refl (term1308 A B C _75298 x)). Qed.
Lemma lem5963370 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : ((_75298 x) = (term1307 A B C x)) = ((_75298 x) = (term1125 A B C x)).
Proof. exact (MK_COMB (@lem5963369 A B C _75298 x) (@lem5963368 A B C x)). Qed.
Lemma lem5963371 {A B C : Type'} (_75298 : type441 A B C) : (term1360 A B C _75298) = (term1361 A B C _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5963370 A B C _75298 x)). Qed.
Lemma lem5963372 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5963373 {A B C : Type'} (_75298 : type441 A B C) : (term1357 A B C _75298) = (term1362 A B C _75298).
Proof. exact (MK_COMB (@lem5963372 A B C) (@lem5963371 A B C _75298)). Qed.
Lemma lem5963374 {A B C : Type'} (_75298 : type441 A B C) : ((_75298 = (term1356 A B C)) = (term1357 A B C _75298)) = ((_75298 = (term1306 A B C)) = (term1362 A B C _75298)).
Proof. exact (MK_COMB (@lem5963367 A B C _75298) (@lem5963373 A B C _75298)). Qed.
Lemma lem5963375 {A B C : Type'} (_75298 : type441 A B C) : (_75298 = (term1306 A B C)) = (term1362 A B C _75298).
Proof. exact (EQ_MP (@lem5963374 A B C _75298) (@lem5963361 A B C _75298)). Qed.
Lemma lem5963377 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term1173 _3571 _3575 t)) = (term1174 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5963378 {A B C : Type'} (s : type322 A B C) (t : type322 A B C) : (s = (term1363 A B C t)) = (term1364 A B C s t).
Proof. exact (@lem5963377 Prop (type1209 A B C) s t). Qed.
Lemma lem5963379 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : ((_75298 x) = (term1365 A B C x)) = (term1366 A B C _75298 x).
Proof. exact (@lem5963378 A B C (_75298 x) (term1125 A B C x)). Qed.
Lemma lem5963380 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1367 A B C x f) = (term1124 A B C f x).
Proof. exact (eq_refl (term1367 A B C x f)). Qed.
Lemma lem5963381 {A B C : Type'} (x : type1412 A B C) : (term1365 A B C x) = (term1125 A B C x).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5963380 A B C f x)). Qed.
Lemma lem5963382 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1308 A B C _75298 x) = (term1308 A B C _75298 x).
Proof. exact (eq_refl (term1308 A B C _75298 x)). Qed.
Lemma lem5963383 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : ((_75298 x) = (term1365 A B C x)) = ((_75298 x) = (term1125 A B C x)).
Proof. exact (MK_COMB (@lem5963382 A B C _75298 x) (@lem5963381 A B C x)). Qed.
Lemma lem5963384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5963385 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1368 A B C _75298 x) = (term1369 A B C _75298 x).
Proof. exact (MK_COMB (@lem5963384) (@lem5963383 A B C _75298 x)). Qed.
Lemma lem5963386 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1367 A B C x f) = (term1124 A B C f x).
Proof. exact (eq_refl (term1367 A B C x f)). Qed.
Lemma lem5963387 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (f : type1209 A B C) : (term1370 A B C _75298 x f) = (term1370 A B C _75298 x f).
Proof. exact (eq_refl (term1370 A B C _75298 x f)). Qed.
Lemma lem5963388 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : ((_75298 x f) = (term1367 A B C x f)) = ((_75298 x f) = (term1124 A B C f x)).
Proof. exact (MK_COMB (@lem5963387 A B C _75298 x f) (@lem5963386 A B C f x)). Qed.
Lemma lem5963389 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1371 A B C _75298 x) = (term1372 A B C _75298 x).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5963388 A B C _75298 f x)). Qed.
Lemma lem5963390 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem5963391 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1366 A B C _75298 x) = (term1373 A B C _75298 x).
Proof. exact (MK_COMB (@lem5963390 A B C) (@lem5963389 A B C _75298 x)). Qed.
Lemma lem5963392 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (((_75298 x) = (term1365 A B C x)) = (term1366 A B C _75298 x)) = (((_75298 x) = (term1125 A B C x)) = (term1373 A B C _75298 x)).
Proof. exact (MK_COMB (@lem5963385 A B C _75298 x) (@lem5963391 A B C _75298 x)). Qed.
Lemma lem5963393 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : ((_75298 x) = (term1125 A B C x)) = (term1373 A B C _75298 x).
Proof. exact (EQ_MP (@lem5963392 A B C _75298 x) (@lem5963379 A B C _75298 x)). Qed.
Lemma lem5963394 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : ((_75298 x f) = (term1124 A B C f x)) = ((_75298 x f) = (term1124 A B C f x)).
Proof. exact (eq_refl ((_75298 x f) = (term1124 A B C f x))). Qed.
Lemma lem5963395 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1372 A B C _75298 x) = (term1372 A B C _75298 x).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5963394 A B C _75298 f x)). Qed.
Lemma lem5963396 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem5963397 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1373 A B C _75298 x) = (term1373 A B C _75298 x).
Proof. exact (MK_COMB (@lem5963396 A B C) (@lem5963395 A B C _75298 x)). Qed.
Lemma lem5963398 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : ((_75298 x) = (term1125 A B C x)) = (term1373 A B C _75298 x).
Proof. exact (TRANS (@lem5963393 A B C _75298 x) (@lem5963397 A B C _75298 x)). Qed.
Lemma lem5963399 {A B C : Type'} (_75298 : type441 A B C) : (term1361 A B C _75298) = (term1374 A B C _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5963398 A B C _75298 x)). Qed.
Lemma lem5963400 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5963401 {A B C : Type'} (_75298 : type441 A B C) : (term1362 A B C _75298) = (term1375 A B C _75298).
Proof. exact (MK_COMB (@lem5963400 A B C) (@lem5963399 A B C _75298)). Qed.
Lemma lem5963402 {A B C : Type'} (_75298 : type441 A B C) : (_75298 = (term1306 A B C)) = (term1375 A B C _75298).
Proof. exact (TRANS (@lem5963375 A B C _75298) (@lem5963401 A B C _75298)). Qed.
Lemma lem5963403 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963404 {A B C : Type'} (_75298 : type441 A B C) : (term1340 A B C _75298) = (term1376 A B C _75298).
Proof. exact (MK_COMB (@lem5963403) (@lem5963402 A B C _75298)). Qed.
Lemma lem5963405 {A B C : Type'} (_75298 : type441 A B C) : (term1332 A B C _75298) = (term1332 A B C _75298).
Proof. exact (eq_refl (term1332 A B C _75298)). Qed.
Lemma lem5963406 {A B C : Type'} (_75298 : type441 A B C) : (term1348 A B C _75298) = (term1377 A B C _75298).
Proof. exact (MK_COMB (@lem5963404 A B C _75298) (@lem5963405 A B C _75298)). Qed.
Lemma lem5963407 {A B C : Type'} : (term1350 A B C) = (term1378 A B C).
Proof. exact (fun_ext (fun _75298 : type441 A B C => @lem5963406 A B C _75298)). Qed.
Lemma lem5963408 {A B C : Type'} : (@all ((A -> B -> C) -> ((prod A B) -> C) -> Prop)) = (@all ((A -> B -> C) -> ((prod A B) -> C) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B -> C) -> ((prod A B) -> C) -> Prop))). Qed.
Lemma lem5963409 {A B C : Type'} : (term1352 A B C) = (term1379 A B C).
Proof. exact (MK_COMB (@lem5963408 A B C) (@lem5963407 A B C)). Qed.
Lemma lem5963410 {A B C : Type'} : (term1339 A B C) = (term1339 A B C).
Proof. exact (eq_refl (term1339 A B C)). Qed.
Lemma lem5963411 {A B C : Type'} : ((term1305 A B C) = (term1352 A B C)) = ((term1305 A B C) = (term1379 A B C)).
Proof. exact (MK_COMB (@lem5963410 A B C) (@lem5963409 A B C)). Qed.
Lemma lem5963414 {A B C : Type'} : (term1305 A B C) = (term1379 A B C).
Proof. exact (EQ_MP (@lem5963411 A B C) (@lem5963357 A B C)). Qed.
Lemma lem5963415 {A B C : Type'} : (term1219 A B C) = (term1379 A B C).
Proof. exact (TRANS (@lem5963029 A B C) (@lem5963414 A B C)). Qed.
Lemma lem5963416 {A B C : Type'} : (term1110 A B C) = (term1379 A B C).
Proof. exact (TRANS (@lem5962657 A B C) (@lem5963415 A B C)). Qed.
Lemma lem5963417 {A B C : Type'} : (term1109 A B C) = (term1379 A B C).
Proof. exact (TRANS (@lem5962273 A B C) (@lem5963416 A B C)). Qed.
Lemma lem5963430 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term1059 A B s t p1 i p2 j) = (term1059 A B s t p1 i p2 j).
Proof. exact (eq_refl (term1059 A B s t p1 i p2 j)). Qed.
Lemma lem5963431 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term1061 A B s t p1 i p2) = (term1061 A B s t p1 i p2).
Proof. exact (fun_ext (fun j : B => @lem5963430 A B s t p1 i p2 j)). Qed.
Lemma lem5963432 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5963433 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term1063 A B s t p1 i p2) = (term1063 A B s t p1 i p2).
Proof. exact (MK_COMB (@lem5963432 B) (@lem5963431 A B s t p1 i p2)). Qed.
Lemma lem5963434 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1065 A B s t p1 p2) = (term1065 A B s t p1 p2).
Proof. exact (fun_ext (fun i : A => @lem5963433 A B s t p1 i p2)). Qed.
Lemma lem5963435 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5963436 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1066 A B s t p1 p2) = (term1066 A B s t p1 p2).
Proof. exact (MK_COMB (@lem5963435 A) (@lem5963434 A B s t p1 p2)). Qed.
Lemma lem5963445 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term1016 A B p1 p2 x t x') = (term1016 A B p1 p2 x t x').
Proof. exact (eq_refl (term1016 A B p1 p2 x t x')). Qed.
Lemma lem5963446 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1018 A B p1 p2 t x) = (term1018 A B p1 p2 t x).
Proof. exact (fun_ext (fun x' : B => @lem5963445 A B p1 p2 x' t x)). Qed.
Lemma lem5963447 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5963448 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1019 A B p1 p2 t x) = (term1019 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5963447 B) (@lem5963446 A B p1 p2 t x)). Qed.
Lemma lem5963449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5963450 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1021 A B p1 p2 t x) = (term1021 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5963449) (@lem5963448 A B p1 p2 t x)). Qed.
Lemma lem5963451 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1067 A B x s t p1 p2) = (term1067 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5963450 A B p1 p2 t x) (@lem5963436 A B s t p1 p2)). Qed.
Lemma lem5963452 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5963453 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1070 A B x s t p1 p2) = (term1070 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5963452) (@lem5963451 A B x s t p1 p2)). Qed.
Lemma lem5963454 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term1071 A B x s t p1) = (term1071 A B x s t p1).
Proof. exact (fun_ext (fun p2 : B => @lem5963453 A B x s t p1 p2)). Qed.
Lemma lem5963455 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5963456 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term1072 A B x s t p1) = (term1072 A B x s t p1).
Proof. exact (MK_COMB (@lem5963455 B) (@lem5963454 A B x s t p1)). Qed.
Lemma lem5963457 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1073 A B x s t) = (term1073 A B x s t).
Proof. exact (fun_ext (fun p1 : A => @lem5963456 A B x s t p1)). Qed.
Lemma lem5963458 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5963459 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1074 A B x s t) = (term1074 A B x s t).
Proof. exact (MK_COMB (@lem5963458 A) (@lem5963457 A B x s t)). Qed.
Lemma lem5963468 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (i : A) : (term892 A B x s t i) = (term892 A B x s t i).
Proof. exact (eq_refl (term892 A B x s t i)). Qed.
Lemma lem5963469 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term894 A B x s t) = (term894 A B x s t).
Proof. exact (fun_ext (fun i : A => @lem5963468 A B x s t i)). Qed.
Lemma lem5963470 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5963471 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term895 A B x s t) = (term895 A B x s t).
Proof. exact (MK_COMB (@lem5963470 A) (@lem5963469 A B x s t)). Qed.
Lemma lem5963472 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963473 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1082 A B x s t) = (term1082 A B x s t).
Proof. exact (MK_COMB (@lem5963472) (@lem5963471 A B x s t)). Qed.
Lemma lem5963474 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1084 A B x s t) = (term1084 A B x s t).
Proof. exact (MK_COMB (@lem5963473 A B x s t) (@lem5963459 A B x s t)). Qed.
Lemma lem5963477 {A : Type'} (s : A -> Prop) : (term642 A s) = (term642 A s).
Proof. exact (eq_refl (term642 A s)). Qed.
Lemma lem5963478 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1086 A B x s t) = (term1086 A B x s t).
Proof. exact (MK_COMB (@lem5963477 A s) (@lem5963474 A B x s t)). Qed.
Lemma lem5963483 {A : Type'} (x : A) (s : A -> Prop) : (term1087 A x s) = (term1087 A x s).
Proof. exact (eq_refl (term1087 A x s)). Qed.
Lemma lem5963484 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term1089 A B x s t) = (term1089 A B x s t).
Proof. exact (MK_COMB (@lem5963483 A x s) (@lem5963478 A B x s t)). Qed.
Lemma lem5963485 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) (x : type1412 A B C) : ((term1131 A B C s _75296 op t x) = (term1310 A B C op _75297 s t _75298 x)) = ((term1131 A B C s _75296 op t x) = (term1310 A B C op _75297 s t _75298 x)).
Proof. exact (eq_refl ((term1131 A B C s _75296 op t x) = (term1310 A B C op _75297 s t _75298 x))). Qed.
Lemma lem5963486 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1311 A B C _75296 op _75297 s t _75298) = (term1311 A B C _75296 op _75297 s t _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5963485 A B C _75296 op _75297 s t _75298 x)). Qed.
Lemma lem5963487 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5963488 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1312 A B C _75296 op _75297 s t _75298) = (term1312 A B C _75296 op _75297 s t _75298).
Proof. exact (MK_COMB (@lem5963487 A B C) (@lem5963486 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5963493 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : (term911 A B s t i) = (term911 A B s t i).
Proof. exact (eq_refl (term911 A B s t i)). Qed.
Lemma lem5963494 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term913 A B s t) = (term913 A B s t).
Proof. exact (fun_ext (fun i : A => @lem5963493 A B s t i)). Qed.
Lemma lem5963495 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5963496 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term630 A B s t) = (term630 A B s t).
Proof. exact (MK_COMB (@lem5963495 A) (@lem5963494 A B s t)). Qed.
Lemma lem5963497 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963498 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1136 A B s t) = (term1136 A B s t).
Proof. exact (MK_COMB (@lem5963497) (@lem5963496 A B s t)). Qed.
Lemma lem5963499 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1313 A B C _75296 op _75297 s t _75298) = (term1313 A B C _75296 op _75297 s t _75298).
Proof. exact (MK_COMB (@lem5963498 A B s t) (@lem5963488 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5963500 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1314 A B C _75296 op _75297 s _75298) = (term1314 A B C _75296 op _75297 s _75298).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5963499 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5963501 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5963502 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1315 A B C _75296 op _75297 s _75298) = (term1315 A B C _75296 op _75297 s _75298).
Proof. exact (MK_COMB (@lem5963501 A B) (@lem5963500 A B C _75296 op _75297 s _75298)). Qed.
Lemma lem5963503 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963504 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1316 A B C _75296 op _75297 s _75298) = (term1316 A B C _75296 op _75297 s _75298).
Proof. exact (MK_COMB (@lem5963503) (@lem5963502 A B C _75296 op _75297 s _75298)). Qed.
Lemma lem5963505 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (t : type1413 A B) : (term1317 A B C _75296 op _75297 _75298 x s t) = (term1317 A B C _75296 op _75297 _75298 x s t).
Proof. exact (MK_COMB (@lem5963504 A B C _75296 op _75297 s _75298) (@lem5963484 A B x s t)). Qed.
Lemma lem5963508 {C : Type'} (op : type1400 C) : (term1093 C op) = (term1093 C op).
Proof. exact (eq_refl (term1093 C op)). Qed.
Lemma lem5963509 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (t : type1413 A B) : (term1318 A B C _75296 op _75297 _75298 x s t) = (term1318 A B C _75296 op _75297 _75298 x s t).
Proof. exact (MK_COMB (@lem5963508 C op) (@lem5963505 A B C _75296 op _75297 _75298 x s t)). Qed.
Lemma lem5963510 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (t : type1413 A B) : (term1319 A B C _75296 _75297 _75298 x s t) = (term1319 A B C _75296 _75297 _75298 x s t).
Proof. exact (fun_ext (fun op : type1400 C => @lem5963509 A B C _75296 op _75297 _75298 x s t)). Qed.
Lemma lem5963511 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5963512 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (t : type1413 A B) : (term1320 A B C _75296 _75297 _75298 x s t) = (term1320 A B C _75296 _75297 _75298 x s t).
Proof. exact (MK_COMB (@lem5963511 C) (@lem5963510 A B C _75296 _75297 _75298 x s t)). Qed.
Lemma lem5963513 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) (s : A -> Prop) (t : type1413 A B) : (term1321 A B C _75296 _75297 _75298 s t) = (term1321 A B C _75296 _75297 _75298 s t).
Proof. exact (fun_ext (fun x : A => @lem5963512 A B C _75296 _75297 _75298 x s t)). Qed.
Lemma lem5963514 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5963515 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) (s : A -> Prop) (t : type1413 A B) : (term1322 A B C _75296 _75297 _75298 s t) = (term1322 A B C _75296 _75297 _75298 s t).
Proof. exact (MK_COMB (@lem5963514 A) (@lem5963513 A B C _75296 _75297 _75298 s t)). Qed.
Lemma lem5963516 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) (t : type1413 A B) : (term1323 A B C _75296 _75297 _75298 t) = (term1323 A B C _75296 _75297 _75298 t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5963515 A B C _75296 _75297 _75298 s t)). Qed.
Lemma lem5963517 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5963518 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) (t : type1413 A B) : (term1324 A B C _75296 _75297 _75298 t) = (term1324 A B C _75296 _75297 _75298 t).
Proof. exact (MK_COMB (@lem5963517 A) (@lem5963516 A B C _75296 _75297 _75298 t)). Qed.
Lemma lem5963519 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) : (term1325 A B C _75296 _75297 _75298) = (term1325 A B C _75296 _75297 _75298).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5963518 A B C _75296 _75297 _75298 t)). Qed.
Lemma lem5963520 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5963521 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) : (term1326 A B C _75296 _75297 _75298) = (term1326 A B C _75296 _75297 _75298).
Proof. exact (MK_COMB (@lem5963520 A B) (@lem5963519 A B C _75296 _75297 _75298)). Qed.
Lemma lem5963522 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) (i : A) : ((_75296 op t x i) = (term818 A B C op t x i)) = ((_75296 op t x i) = (term818 A B C op t x i)).
Proof. exact (eq_refl ((_75296 op t x i) = (term818 A B C op t x i))). Qed.
Lemma lem5963523 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1208 A B C _75296 op t x) = (term1208 A B C _75296 op t x).
Proof. exact (fun_ext (fun i : A => @lem5963522 A B C _75296 op t x i)). Qed.
Lemma lem5963524 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5963525 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) (x : type1412 A B C) : (term1209 A B C _75296 op t x) = (term1209 A B C _75296 op t x).
Proof. exact (MK_COMB (@lem5963524 A) (@lem5963523 A B C _75296 op t x)). Qed.
Lemma lem5963526 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1210 A B C _75296 op t) = (term1210 A B C _75296 op t).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5963525 A B C _75296 op t x)). Qed.
Lemma lem5963527 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5963528 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (t : type1413 A B) : (term1211 A B C _75296 op t) = (term1211 A B C _75296 op t).
Proof. exact (MK_COMB (@lem5963527 A B C) (@lem5963526 A B C _75296 op t)). Qed.
Lemma lem5963529 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1212 A B C _75296 op) = (term1212 A B C _75296 op).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5963528 A B C _75296 op t)). Qed.
Lemma lem5963530 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5963531 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) : (term1213 A B C _75296 op) = (term1213 A B C _75296 op).
Proof. exact (MK_COMB (@lem5963530 A B) (@lem5963529 A B C _75296 op)). Qed.
Lemma lem5963532 {A B C : Type'} (_75296 : type877 A B C) : (term1214 A B C _75296) = (term1214 A B C _75296).
Proof. exact (fun_ext (fun op : type1400 C => @lem5963531 A B C _75296 op)). Qed.
Lemma lem5963533 {C : Type'} : (@all (C -> C -> C)) = (@all (C -> C -> C)).
Proof. exact (eq_refl (@all (C -> C -> C))). Qed.
Lemma lem5963534 {A B C : Type'} (_75296 : type877 A B C) : (term1215 A B C _75296) = (term1215 A B C _75296).
Proof. exact (MK_COMB (@lem5963533 C) (@lem5963532 A B C _75296)). Qed.
Lemma lem5963535 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963536 {A B C : Type'} (_75296 : type877 A B C) : (term1216 A B C _75296) = (term1216 A B C _75296).
Proof. exact (MK_COMB (@lem5963535) (@lem5963534 A B C _75296)). Qed.
Lemma lem5963537 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) : (term1327 A B C _75296 _75297 _75298) = (term1327 A B C _75296 _75297 _75298).
Proof. exact (MK_COMB (@lem5963536 A B C _75296) (@lem5963521 A B C _75296 _75297 _75298)). Qed.
Lemma lem5963538 {A B C : Type'} (_75297 : type621 A B) (_75298 : type441 A B C) : (term1328 A B C _75297 _75298) = (term1328 A B C _75297 _75298).
Proof. exact (fun_ext (fun _75296 : type877 A B C => @lem5963537 A B C _75296 _75297 _75298)). Qed.
Lemma lem5963539 {A B C : Type'} : (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C)) = (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C)).
Proof. exact (eq_refl (@all ((C -> C -> C) -> (A -> B -> Prop) -> (A -> B -> C) -> A -> C))). Qed.
Lemma lem5963540 {A B C : Type'} (_75297 : type621 A B) (_75298 : type441 A B C) : (term1329 A B C _75297 _75298) = (term1329 A B C _75297 _75298).
Proof. exact (MK_COMB (@lem5963539 A B C) (@lem5963538 A B C _75297 _75298)). Qed.
Lemma lem5963541 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) (j : B) : (term1126 A B GEN_PVAR_241 s t i j) = (term1126 A B GEN_PVAR_241 s t i j).
Proof. exact (eq_refl (term1126 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5963542 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1127 A B GEN_PVAR_241 s t i) = (term1127 A B GEN_PVAR_241 s t i).
Proof. exact (fun_ext (fun j : B => @lem5963541 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5963543 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5963544 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1128 A B GEN_PVAR_241 s t i) = (term1128 A B GEN_PVAR_241 s t i).
Proof. exact (MK_COMB (@lem5963543 B) (@lem5963542 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5963545 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1129 A B GEN_PVAR_241 s t) = (term1129 A B GEN_PVAR_241 s t).
Proof. exact (fun_ext (fun i : A => @lem5963544 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5963546 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5963547 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1028 A B GEN_PVAR_241 s t) = (term1028 A B GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5963546 A) (@lem5963545 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5963550 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_241 : prod A B) : (term1294 A B _75297 s t GEN_PVAR_241) = (term1294 A B _75297 s t GEN_PVAR_241).
Proof. exact (eq_refl (term1294 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5963551 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((_75297 s t GEN_PVAR_241) = (term1028 A B GEN_PVAR_241 s t)) = ((_75297 s t GEN_PVAR_241) = (term1028 A B GEN_PVAR_241 s t)).
Proof. exact (MK_COMB (@lem5963550 A B _75297 s t GEN_PVAR_241) (@lem5963547 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5963552 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1296 A B _75297 s t) = (term1296 A B _75297 s t).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5963551 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5963553 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5963554 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1297 A B _75297 s t) = (term1297 A B _75297 s t).
Proof. exact (MK_COMB (@lem5963553 A B) (@lem5963552 A B _75297 s t)). Qed.
Lemma lem5963555 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1298 A B _75297 s) = (term1298 A B _75297 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5963554 A B _75297 s t)). Qed.
Lemma lem5963556 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5963557 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1299 A B _75297 s) = (term1299 A B _75297 s).
Proof. exact (MK_COMB (@lem5963556 A B) (@lem5963555 A B _75297 s)). Qed.
Lemma lem5963558 {A B : Type'} (_75297 : type621 A B) : (term1300 A B _75297) = (term1300 A B _75297).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5963557 A B _75297 s)). Qed.
Lemma lem5963559 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5963560 {A B : Type'} (_75297 : type621 A B) : (term1301 A B _75297) = (term1301 A B _75297).
Proof. exact (MK_COMB (@lem5963559 A) (@lem5963558 A B _75297)). Qed.
Lemma lem5963561 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963562 {A B : Type'} (_75297 : type621 A B) : (term1302 A B _75297) = (term1302 A B _75297).
Proof. exact (MK_COMB (@lem5963561) (@lem5963560 A B _75297)). Qed.
Lemma lem5963563 {A B C : Type'} (_75297 : type621 A B) (_75298 : type441 A B C) : (term1330 A B C _75297 _75298) = (term1330 A B C _75297 _75298).
Proof. exact (MK_COMB (@lem5963562 A B _75297) (@lem5963540 A B C _75297 _75298)). Qed.
Lemma lem5963564 {A B C : Type'} (_75298 : type441 A B C) : (term1331 A B C _75298) = (term1331 A B C _75298).
Proof. exact (fun_ext (fun _75297 : type621 A B => @lem5963563 A B C _75297 _75298)). Qed.
Lemma lem5963565 {A B : Type'} : (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)) = (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop))). Qed.
Lemma lem5963566 {A B C : Type'} (_75298 : type441 A B C) : (term1332 A B C _75298) = (term1332 A B C _75298).
Proof. exact (MK_COMB (@lem5963565 A B) (@lem5963564 A B C _75298)). Qed.
Lemma lem5963567 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) (j : B) : (term1120 A B C f x i j) = (term1120 A B C f x i j).
Proof. exact (eq_refl (term1120 A B C f x i j)). Qed.
Lemma lem5963568 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1121 A B C f x i) = (term1121 A B C f x i).
Proof. exact (fun_ext (fun j : B => @lem5963567 A B C f x i j)). Qed.
Lemma lem5963569 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5963570 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1122 A B C f x i) = (term1122 A B C f x i).
Proof. exact (MK_COMB (@lem5963569 B) (@lem5963568 A B C f x i)). Qed.
Lemma lem5963571 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1123 A B C f x) = (term1123 A B C f x).
Proof. exact (fun_ext (fun i : A => @lem5963570 A B C f x i)). Qed.
Lemma lem5963572 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5963573 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1124 A B C f x) = (term1124 A B C f x).
Proof. exact (MK_COMB (@lem5963572 A) (@lem5963571 A B C f x)). Qed.
Lemma lem5963576 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (f : type1209 A B C) : (term1370 A B C _75298 x f) = (term1370 A B C _75298 x f).
Proof. exact (eq_refl (term1370 A B C _75298 x f)). Qed.
Lemma lem5963577 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : ((_75298 x f) = (term1124 A B C f x)) = ((_75298 x f) = (term1124 A B C f x)).
Proof. exact (MK_COMB (@lem5963576 A B C _75298 x f) (@lem5963573 A B C f x)). Qed.
Lemma lem5963578 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1372 A B C _75298 x) = (term1372 A B C _75298 x).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5963577 A B C _75298 f x)). Qed.
Lemma lem5963579 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem5963580 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1373 A B C _75298 x) = (term1373 A B C _75298 x).
Proof. exact (MK_COMB (@lem5963579 A B C) (@lem5963578 A B C _75298 x)). Qed.
Lemma lem5963581 {A B C : Type'} (_75298 : type441 A B C) : (term1374 A B C _75298) = (term1374 A B C _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5963580 A B C _75298 x)). Qed.
Lemma lem5963582 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5963583 {A B C : Type'} (_75298 : type441 A B C) : (term1375 A B C _75298) = (term1375 A B C _75298).
Proof. exact (MK_COMB (@lem5963582 A B C) (@lem5963581 A B C _75298)). Qed.
Lemma lem5963584 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5963585 {A B C : Type'} (_75298 : type441 A B C) : (term1376 A B C _75298) = (term1376 A B C _75298).
Proof. exact (MK_COMB (@lem5963584) (@lem5963583 A B C _75298)). Qed.
Lemma lem5963586 {A B C : Type'} (_75298 : type441 A B C) : (term1377 A B C _75298) = (term1377 A B C _75298).
Proof. exact (MK_COMB (@lem5963585 A B C _75298) (@lem5963566 A B C _75298)). Qed.
Lemma lem5963587 {A B C : Type'} : (term1378 A B C) = (term1378 A B C).
Proof. exact (fun_ext (fun _75298 : type441 A B C => @lem5963586 A B C _75298)). Qed.
Lemma lem5963588 {A B C : Type'} : (@all ((A -> B -> C) -> ((prod A B) -> C) -> Prop)) = (@all ((A -> B -> C) -> ((prod A B) -> C) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B -> C) -> ((prod A B) -> C) -> Prop))). Qed.
Lemma lem5963589 {A B C : Type'} : (term1379 A B C) = (term1379 A B C).
Proof. exact (MK_COMB (@lem5963588 A B C) (@lem5963587 A B C)). Qed.
Lemma lem5963804 {A B C : Type'} : (term1109 A B C) = (term1379 A B C).
Proof. exact (TRANS (@lem5963417 A B C) (@lem5963589 A B C)). Qed.
Lemma lem5963805 {A B C : Type'} : (term1379 A B C) = (term1109 A B C).
Proof. exact (SYM (@lem5963804 A B C)). Qed.
Lemma lem5963806 {A B C : Type'} (_75298 : type441 A B C) (h1 : term1375 A B C _75298) : term1375 A B C _75298.
Proof. exact (h1). Qed.
Lemma lem5963807 {A B : Type'} (_75297 : type621 A B) (h1 : term1301 A B _75297) : term1301 A B _75297.
Proof. exact (h1). Qed.
Lemma lem5963810 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) (h1 : term1315 A B C _75296 op _75297 s _75298) : term1315 A B C _75296 op _75297 s _75298.
Proof. exact (h1). Qed.
Lemma lem5963814 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (h1 : term1067 A B x s t p1 p2) : term1067 A B x s t p1 p2.
Proof. exact (h1). Qed.
Lemma lem5963818 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) (j : B) : (term1120 A B C f x i j) = (term1120 A B C f x i j).
Proof. exact (eq_refl (term1120 A B C f x i j)). Qed.
Lemma lem5963819 {B : Type'} (P : B -> Prop) : (term1380 B P) = (term1381 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5963820 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1382 A B C f x i) = (term1383 A B C f x i).
Proof. exact (@lem5963819 B (term1121 A B C f x i)). Qed.
Lemma lem5963821 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) (j : B) : (term1384 A B C f x i j) = (term1120 A B C f x i j).
Proof. exact (eq_refl (term1384 A B C f x i j)). Qed.
Lemma lem5963822 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5963824 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) (j : B) : (term1385 A B C f x i j) = (term1386 A B C f x i j).
Proof. exact (MK_COMB (@lem5963822) (@lem5963821 A B C f x i j)). Qed.
Lemma lem5963825 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1387 A B C f x i) = (term1388 A B C f x i).
Proof. exact (fun_ext (fun j : B => @lem5963824 A B C f x i j)). Qed.
Lemma lem5963826 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5963827 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1383 A B C f x i) = (term1389 A B C f x i).
Proof. exact (MK_COMB (@lem5963826 B) (@lem5963825 A B C f x i)). Qed.
Lemma lem5963828 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1382 A B C f x i) = (term1389 A B C f x i).
Proof. exact (TRANS (@lem5963820 A B C f x i) (@lem5963827 A B C f x i)). Qed.
Lemma lem5963829 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1121 A B C f x i) = (term1121 A B C f x i).
Proof. exact (fun_ext (fun j : B => @lem5963818 A B C f x i j)). Qed.
Lemma lem5963830 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5963831 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1122 A B C f x i) = (term1122 A B C f x i).
Proof. exact (MK_COMB (@lem5963830 B) (@lem5963829 A B C f x i)). Qed.
Lemma lem5963832 {A : Type'} (P : A -> Prop) : (term1380 A P) = (term1381 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5963833 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1390 A B C f x) = (term1391 A B C f x).
Proof. exact (@lem5963832 A (term1123 A B C f x)). Qed.
Lemma lem5963834 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1392 A B C f x i) = (term1122 A B C f x i).
Proof. exact (eq_refl (term1392 A B C f x i)). Qed.
Lemma lem5963835 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5963836 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1393 A B C f x i) = (term1382 A B C f x i).
Proof. exact (MK_COMB (@lem5963835) (@lem5963834 A B C f x i)). Qed.
Lemma lem5963837 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1393 A B C f x i) = (term1389 A B C f x i).
Proof. exact (TRANS (@lem5963836 A B C f x i) (@lem5963828 A B C f x i)). Qed.
Lemma lem5963838 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1394 A B C f x) = (term1395 A B C f x).
Proof. exact (fun_ext (fun i : A => @lem5963837 A B C f x i)). Qed.
Lemma lem5963839 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5963840 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1391 A B C f x) = (term1396 A B C f x).
Proof. exact (MK_COMB (@lem5963839 A) (@lem5963838 A B C f x)). Qed.
Lemma lem5963841 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1390 A B C f x) = (term1396 A B C f x).
Proof. exact (TRANS (@lem5963833 A B C f x) (@lem5963840 A B C f x)). Qed.
Lemma lem5963842 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1123 A B C f x) = (term1123 A B C f x).
Proof. exact (fun_ext (fun i : A => @lem5963831 A B C f x i)). Qed.
Lemma lem5963843 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5963844 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1124 A B C f x) = (term1124 A B C f x).
Proof. exact (MK_COMB (@lem5963843 A) (@lem5963842 A B C f x)). Qed.
Lemma lem5963846 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (f : type1209 A B C) : (term1397 A B C _75298 x f) = (term1397 A B C _75298 x f).
Proof. exact (eq_refl (term1397 A B C _75298 x f)). Qed.
Lemma lem5963847 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1398 A B C _75298 f x) = (term1398 A B C _75298 f x).
Proof. exact (MK_COMB (@lem5963846 A B C _75298 x f) (@lem5963844 A B C f x)). Qed.
Lemma lem5963849 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (f : type1209 A B C) : (term1399 A B C _75298 x f) = (term1399 A B C _75298 x f).
Proof. exact (eq_refl (term1399 A B C _75298 x f)). Qed.
Lemma lem5963850 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1400 A B C _75298 f x) = (term1401 A B C _75298 f x).
Proof. exact (MK_COMB (@lem5963849 A B C _75298 x f) (@lem5963841 A B C f x)). Qed.
Lemma lem5963851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5963852 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1402 A B C _75298 f x) = (term1403 A B C _75298 f x).
Proof. exact (MK_COMB (@lem5963851) (@lem5963850 A B C _75298 f x)). Qed.
Lemma lem5963853 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1404 A B C _75298 f x) = (term1405 A B C _75298 f x).
Proof. exact (MK_COMB (@lem5963852 A B C _75298 f x) (@lem5963847 A B C _75298 f x)). Qed.
Lemma lem5963854 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : ((_75298 x f) = (term1124 A B C f x)) = (term1404 A B C _75298 f x).
Proof. exact (@lem17784 (_75298 x f) (term1124 A B C f x)). Qed.
Lemma lem5963855 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : ((_75298 x f) = (term1124 A B C f x)) = (term1405 A B C _75298 f x).
Proof. exact (TRANS (@lem5963854 A B C _75298 f x) (@lem5963853 A B C _75298 f x)). Qed.
Lemma lem5963856 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1372 A B C _75298 x) = (term1406 A B C _75298 x).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5963855 A B C _75298 f x)). Qed.
Lemma lem5963857 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem5963858 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1373 A B C _75298 x) = (term1407 A B C _75298 x).
Proof. exact (MK_COMB (@lem5963857 A B C) (@lem5963856 A B C _75298 x)). Qed.
Lemma lem5963859 {A B C : Type'} (_75298 : type441 A B C) : (term1374 A B C _75298) = (term1408 A B C _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5963858 A B C _75298 x)). Qed.
Lemma lem5963860 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5963861 {A B C : Type'} (_75298 : type441 A B C) : (term1375 A B C _75298) = (term1409 A B C _75298).
Proof. exact (MK_COMB (@lem5963860 A B C) (@lem5963859 A B C _75298)). Qed.
Lemma lem5963867 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1410 A P Q) = (term1411 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5963868 {A B C : Type'} (P : type322 A B C) (Q : type322 A B C) : (term1412 A B C P Q) = (term1413 A B C P Q).
Proof. exact (@lem5963867 (type1209 A B C) P Q). Qed.
Lemma lem5963869 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1414 A B C _75298 x) = (term1415 A B C _75298 x).
Proof. exact (@lem5963868 A B C (term1416 A B C _75298 x) (term1417 A B C _75298 x)). Qed.
Lemma lem5963870 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1418 A B C _75298 x f) = (term1401 A B C _75298 f x).
Proof. exact (eq_refl (term1418 A B C _75298 x f)). Qed.
Lemma lem5963871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5963872 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1419 A B C _75298 x f) = (term1403 A B C _75298 f x).
Proof. exact (MK_COMB (@lem5963871) (@lem5963870 A B C _75298 f x)). Qed.
Lemma lem5963873 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1420 A B C _75298 x f) = (term1398 A B C _75298 f x).
Proof. exact (eq_refl (term1420 A B C _75298 x f)). Qed.
Lemma lem5963874 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1421 A B C _75298 x f) = (term1405 A B C _75298 f x).
Proof. exact (MK_COMB (@lem5963872 A B C _75298 f x) (@lem5963873 A B C _75298 f x)). Qed.
Lemma lem5963875 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1422 A B C _75298 x) = (term1406 A B C _75298 x).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5963874 A B C _75298 f x)). Qed.
Lemma lem5963876 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem5963877 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1414 A B C _75298 x) = (term1407 A B C _75298 x).
Proof. exact (MK_COMB (@lem5963876 A B C) (@lem5963875 A B C _75298 x)). Qed.
Lemma lem5963878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5963879 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1423 A B C _75298 x) = (term1424 A B C _75298 x).
Proof. exact (MK_COMB (@lem5963878) (@lem5963877 A B C _75298 x)). Qed.
Lemma lem5963880 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1418 A B C _75298 x f) = (term1401 A B C _75298 f x).
Proof. exact (eq_refl (term1418 A B C _75298 x f)). Qed.
Lemma lem5963881 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1425 A B C _75298 x) = (term1416 A B C _75298 x).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5963880 A B C _75298 f x)). Qed.
Lemma lem5963882 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem5963883 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1426 A B C _75298 x) = (term1427 A B C _75298 x).
Proof. exact (MK_COMB (@lem5963882 A B C) (@lem5963881 A B C _75298 x)). Qed.
Lemma lem5963884 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5963885 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1428 A B C _75298 x) = (term1429 A B C _75298 x).
Proof. exact (MK_COMB (@lem5963884) (@lem5963883 A B C _75298 x)). Qed.
Lemma lem5963886 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1420 A B C _75298 x f) = (term1398 A B C _75298 f x).
Proof. exact (eq_refl (term1420 A B C _75298 x f)). Qed.
Lemma lem5963887 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1430 A B C _75298 x) = (term1417 A B C _75298 x).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5963886 A B C _75298 f x)). Qed.
Lemma lem5963888 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem5963889 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1431 A B C _75298 x) = (term1432 A B C _75298 x).
Proof. exact (MK_COMB (@lem5963888 A B C) (@lem5963887 A B C _75298 x)). Qed.
Lemma lem5963890 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1415 A B C _75298 x) = (term1433 A B C _75298 x).
Proof. exact (MK_COMB (@lem5963885 A B C _75298 x) (@lem5963889 A B C _75298 x)). Qed.
Lemma lem5963891 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : ((term1414 A B C _75298 x) = (term1415 A B C _75298 x)) = ((term1407 A B C _75298 x) = (term1433 A B C _75298 x)).
Proof. exact (MK_COMB (@lem5963879 A B C _75298 x) (@lem5963890 A B C _75298 x)). Qed.
Lemma lem5963892 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1407 A B C _75298 x) = (term1433 A B C _75298 x).
Proof. exact (EQ_MP (@lem5963891 A B C _75298 x) (@lem5963869 A B C _75298 x)). Qed.
Lemma lem5964005 {A B C : Type'} (_75298 : type441 A B C) : (term1408 A B C _75298) = (term1434 A B C _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5963892 A B C _75298 x)). Qed.
Lemma lem5964006 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5964007 {A B C : Type'} (_75298 : type441 A B C) : (term1409 A B C _75298) = (term1435 A B C _75298).
Proof. exact (MK_COMB (@lem5964006 A B C) (@lem5964005 A B C _75298)). Qed.
Lemma lem5964009 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1410 A P Q) = (term1411 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5964010 {A B C : Type'} (P : type443 A B C) (Q : type443 A B C) : (term1436 A B C P Q) = (term1437 A B C P Q).
Proof. exact (@lem5964009 (type1412 A B C) P Q). Qed.
Lemma lem5964011 {A B C : Type'} (_75298 : type441 A B C) : (term1438 A B C _75298) = (term1439 A B C _75298).
Proof. exact (@lem5964010 A B C (term1440 A B C _75298) (term1441 A B C _75298)). Qed.
Lemma lem5964012 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1442 A B C _75298 x) = (term1427 A B C _75298 x).
Proof. exact (eq_refl (term1442 A B C _75298 x)). Qed.
Lemma lem5964013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964014 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1443 A B C _75298 x) = (term1429 A B C _75298 x).
Proof. exact (MK_COMB (@lem5964013) (@lem5964012 A B C _75298 x)). Qed.
Lemma lem5964015 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1444 A B C _75298 x) = (term1432 A B C _75298 x).
Proof. exact (eq_refl (term1444 A B C _75298 x)). Qed.
Lemma lem5964016 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1445 A B C _75298 x) = (term1433 A B C _75298 x).
Proof. exact (MK_COMB (@lem5964014 A B C _75298 x) (@lem5964015 A B C _75298 x)). Qed.
Lemma lem5964017 {A B C : Type'} (_75298 : type441 A B C) : (term1446 A B C _75298) = (term1434 A B C _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5964016 A B C _75298 x)). Qed.
Lemma lem5964018 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5964019 {A B C : Type'} (_75298 : type441 A B C) : (term1438 A B C _75298) = (term1435 A B C _75298).
Proof. exact (MK_COMB (@lem5964018 A B C) (@lem5964017 A B C _75298)). Qed.
Lemma lem5964020 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964021 {A B C : Type'} (_75298 : type441 A B C) : (term1447 A B C _75298) = (term1448 A B C _75298).
Proof. exact (MK_COMB (@lem5964020) (@lem5964019 A B C _75298)). Qed.
Lemma lem5964022 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1442 A B C _75298 x) = (term1427 A B C _75298 x).
Proof. exact (eq_refl (term1442 A B C _75298 x)). Qed.
Lemma lem5964023 {A B C : Type'} (_75298 : type441 A B C) : (term1449 A B C _75298) = (term1440 A B C _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5964022 A B C _75298 x)). Qed.
Lemma lem5964024 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5964025 {A B C : Type'} (_75298 : type441 A B C) : (term1450 A B C _75298) = (term1451 A B C _75298).
Proof. exact (MK_COMB (@lem5964024 A B C) (@lem5964023 A B C _75298)). Qed.
Lemma lem5964026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964027 {A B C : Type'} (_75298 : type441 A B C) : (term1452 A B C _75298) = (term1453 A B C _75298).
Proof. exact (MK_COMB (@lem5964026) (@lem5964025 A B C _75298)). Qed.
Lemma lem5964028 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1444 A B C _75298 x) = (term1432 A B C _75298 x).
Proof. exact (eq_refl (term1444 A B C _75298 x)). Qed.
Lemma lem5964029 {A B C : Type'} (_75298 : type441 A B C) : (term1454 A B C _75298) = (term1441 A B C _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5964028 A B C _75298 x)). Qed.
Lemma lem5964030 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5964031 {A B C : Type'} (_75298 : type441 A B C) : (term1455 A B C _75298) = (term1456 A B C _75298).
Proof. exact (MK_COMB (@lem5964030 A B C) (@lem5964029 A B C _75298)). Qed.
Lemma lem5964032 {A B C : Type'} (_75298 : type441 A B C) : (term1439 A B C _75298) = (term1457 A B C _75298).
Proof. exact (MK_COMB (@lem5964027 A B C _75298) (@lem5964031 A B C _75298)). Qed.
Lemma lem5964033 {A B C : Type'} (_75298 : type441 A B C) : ((term1438 A B C _75298) = (term1439 A B C _75298)) = ((term1435 A B C _75298) = (term1457 A B C _75298)).
Proof. exact (MK_COMB (@lem5964021 A B C _75298) (@lem5964032 A B C _75298)). Qed.
Lemma lem5964034 {A B C : Type'} (_75298 : type441 A B C) : (term1435 A B C _75298) = (term1457 A B C _75298).
Proof. exact (EQ_MP (@lem5964033 A B C _75298) (@lem5964011 A B C _75298)). Qed.
Lemma lem5964155 {A B C : Type'} (_75298 : type441 A B C) : (term1409 A B C _75298) = (term1457 A B C _75298).
Proof. exact (TRANS (@lem5964007 A B C _75298) (@lem5964034 A B C _75298)). Qed.
Lemma lem5964157 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5964158 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (@lem5964157 A P Q). Qed.
Lemma lem5964159 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1458 A B C _75298 f x) = (term1459 A B C _75298 f x).
Proof. exact (@lem5964158 A (_75298 x f) (term1395 A B C f x)). Qed.
Lemma lem5964160 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1460 A B C f x i) = (term1389 A B C f x i).
Proof. exact (eq_refl (term1460 A B C f x i)). Qed.
Lemma lem5964161 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1461 A B C f x) = (term1395 A B C f x).
Proof. exact (fun_ext (fun i : A => @lem5964160 A B C f x i)). Qed.
Lemma lem5964162 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5964163 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) : (term1462 A B C f x) = (term1396 A B C f x).
Proof. exact (MK_COMB (@lem5964162 A) (@lem5964161 A B C f x)). Qed.
Lemma lem5964164 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (f : type1209 A B C) : (term1399 A B C _75298 x f) = (term1399 A B C _75298 x f).
Proof. exact (eq_refl (term1399 A B C _75298 x f)). Qed.
Lemma lem5964165 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1458 A B C _75298 f x) = (term1401 A B C _75298 f x).
Proof. exact (MK_COMB (@lem5964164 A B C _75298 x f) (@lem5964163 A B C f x)). Qed.
Lemma lem5964166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964167 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1463 A B C _75298 f x) = (term1464 A B C _75298 f x).
Proof. exact (MK_COMB (@lem5964166) (@lem5964165 A B C _75298 f x)). Qed.
Lemma lem5964168 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1460 A B C f x i) = (term1389 A B C f x i).
Proof. exact (eq_refl (term1460 A B C f x i)). Qed.
Lemma lem5964169 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (f : type1209 A B C) : (term1399 A B C _75298 x f) = (term1399 A B C _75298 x f).
Proof. exact (eq_refl (term1399 A B C _75298 x f)). Qed.
Lemma lem5964170 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1465 A B C _75298 f x i) = (term1466 A B C _75298 f x i).
Proof. exact (MK_COMB (@lem5964169 A B C _75298 x f) (@lem5964168 A B C f x i)). Qed.
Lemma lem5964171 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1467 A B C _75298 f x) = (term1468 A B C _75298 f x).
Proof. exact (fun_ext (fun i : A => @lem5964170 A B C _75298 f x i)). Qed.
Lemma lem5964172 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5964173 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1459 A B C _75298 f x) = (term1469 A B C _75298 f x).
Proof. exact (MK_COMB (@lem5964172 A) (@lem5964171 A B C _75298 f x)). Qed.
Lemma lem5964174 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : ((term1458 A B C _75298 f x) = (term1459 A B C _75298 f x)) = ((term1401 A B C _75298 f x) = (term1469 A B C _75298 f x)).
Proof. exact (MK_COMB (@lem5964167 A B C _75298 f x) (@lem5964173 A B C _75298 f x)). Qed.
Lemma lem5964175 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1401 A B C _75298 f x) = (term1469 A B C _75298 f x).
Proof. exact (EQ_MP (@lem5964174 A B C _75298 f x) (@lem5964159 A B C _75298 f x)). Qed.
Lemma lem5964177 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5964178 {B : Type'} (P : Prop) (Q : B -> Prop) : (term334 B P Q) = (term335 B P Q).
Proof. exact (@lem5964177 B P Q). Qed.
Lemma lem5964179 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1470 A B C _75298 f x i) = (term1471 A B C _75298 f x i).
Proof. exact (@lem5964178 B (_75298 x f) (term1388 A B C f x i)). Qed.
Lemma lem5964180 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) (j : B) : (term1472 A B C f x i j) = (term1386 A B C f x i j).
Proof. exact (eq_refl (term1472 A B C f x i j)). Qed.
Lemma lem5964181 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1473 A B C f x i) = (term1388 A B C f x i).
Proof. exact (fun_ext (fun j : B => @lem5964180 A B C f x i j)). Qed.
Lemma lem5964182 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5964183 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1474 A B C f x i) = (term1389 A B C f x i).
Proof. exact (MK_COMB (@lem5964182 B) (@lem5964181 A B C f x i)). Qed.
Lemma lem5964184 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (f : type1209 A B C) : (term1399 A B C _75298 x f) = (term1399 A B C _75298 x f).
Proof. exact (eq_refl (term1399 A B C _75298 x f)). Qed.
Lemma lem5964185 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1470 A B C _75298 f x i) = (term1466 A B C _75298 f x i).
Proof. exact (MK_COMB (@lem5964184 A B C _75298 x f) (@lem5964183 A B C f x i)). Qed.
Lemma lem5964186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964187 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1475 A B C _75298 f x i) = (term1476 A B C _75298 f x i).
Proof. exact (MK_COMB (@lem5964186) (@lem5964185 A B C _75298 f x i)). Qed.
Lemma lem5964188 {A B C : Type'} (f : type1209 A B C) (x : type1412 A B C) (i : A) (j : B) : (term1472 A B C f x i j) = (term1386 A B C f x i j).
Proof. exact (eq_refl (term1472 A B C f x i j)). Qed.
Lemma lem5964189 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (f : type1209 A B C) : (term1399 A B C _75298 x f) = (term1399 A B C _75298 x f).
Proof. exact (eq_refl (term1399 A B C _75298 x f)). Qed.
Lemma lem5964190 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) (i : A) (j : B) : (term1477 A B C _75298 f x i j) = (term1478 A B C _75298 f x i j).
Proof. exact (MK_COMB (@lem5964189 A B C _75298 x f) (@lem5964188 A B C f x i j)). Qed.
Lemma lem5964191 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1479 A B C _75298 f x i) = (term1480 A B C _75298 f x i).
Proof. exact (fun_ext (fun j : B => @lem5964190 A B C _75298 f x i j)). Qed.
Lemma lem5964192 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5964193 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1471 A B C _75298 f x i) = (term1481 A B C _75298 f x i).
Proof. exact (MK_COMB (@lem5964192 B) (@lem5964191 A B C _75298 f x i)). Qed.
Lemma lem5964194 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) (i : A) : ((term1470 A B C _75298 f x i) = (term1471 A B C _75298 f x i)) = ((term1466 A B C _75298 f x i) = (term1481 A B C _75298 f x i)).
Proof. exact (MK_COMB (@lem5964187 A B C _75298 f x i) (@lem5964193 A B C _75298 f x i)). Qed.
Lemma lem5964195 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1466 A B C _75298 f x i) = (term1481 A B C _75298 f x i).
Proof. exact (EQ_MP (@lem5964194 A B C _75298 f x i) (@lem5964179 A B C _75298 f x i)). Qed.
Lemma lem5964196 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1468 A B C _75298 f x) = (term1482 A B C _75298 f x).
Proof. exact (fun_ext (fun i : A => @lem5964195 A B C _75298 f x i)). Qed.
Lemma lem5964197 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5964198 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1469 A B C _75298 f x) = (term1483 A B C _75298 f x).
Proof. exact (MK_COMB (@lem5964197 A) (@lem5964196 A B C _75298 f x)). Qed.
Lemma lem5964199 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1401 A B C _75298 f x) = (term1483 A B C _75298 f x).
Proof. exact (TRANS (@lem5964175 A B C _75298 f x) (@lem5964198 A B C _75298 f x)). Qed.
Lemma lem5964200 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1416 A B C _75298 x) = (term1484 A B C _75298 x).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5964199 A B C _75298 f x)). Qed.
Lemma lem5964201 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem5964202 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1427 A B C _75298 x) = (term1485 A B C _75298 x).
Proof. exact (MK_COMB (@lem5964201 A B C) (@lem5964200 A B C _75298 x)). Qed.
Lemma lem5964204 {A B : Type'} (P : type1413 A B) : (term1486 A B P) = (term1487 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5964205 {A B C : Type'} (P : type318 A B C) : (term1488 A B C P) = (term1489 A B C P).
Proof. exact (@lem5964204 (type1209 A B C) A P). Qed.
Lemma lem5964206 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1490 A B C _75298 x) = (term1491 A B C _75298 x).
Proof. exact (@lem5964205 A B C (term1492 A B C _75298 x)). Qed.
Lemma lem5964207 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1493 A B C _75298 x f) = (term1482 A B C _75298 f x).
Proof. exact (eq_refl (term1493 A B C _75298 x f)). Qed.
Lemma lem5964208 {A : Type'} (i : A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5964209 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1494 A B C _75298 x f i) = (term1495 A B C _75298 f x i).
Proof. exact (MK_COMB (@lem5964207 A B C _75298 f x) (@lem5964208 A i)). Qed.
Lemma lem5964210 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1495 A B C _75298 f x i) = (term1481 A B C _75298 f x i).
Proof. exact (eq_refl (term1495 A B C _75298 f x i)). Qed.
Lemma lem5964211 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) (i : A) : (term1494 A B C _75298 x f i) = (term1481 A B C _75298 f x i).
Proof. exact (TRANS (@lem5964209 A B C _75298 f x i) (@lem5964210 A B C _75298 f x i)). Qed.
Lemma lem5964212 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1496 A B C _75298 x f) = (term1482 A B C _75298 f x).
Proof. exact (fun_ext (fun i : A => @lem5964211 A B C _75298 f x i)). Qed.
Lemma lem5964213 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5964214 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1497 A B C _75298 x f) = (term1483 A B C _75298 f x).
Proof. exact (MK_COMB (@lem5964213 A) (@lem5964212 A B C _75298 f x)). Qed.
Lemma lem5964215 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1498 A B C _75298 x) = (term1484 A B C _75298 x).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5964214 A B C _75298 f x)). Qed.
Lemma lem5964216 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem5964217 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1490 A B C _75298 x) = (term1485 A B C _75298 x).
Proof. exact (MK_COMB (@lem5964216 A B C) (@lem5964215 A B C _75298 x)). Qed.
Lemma lem5964218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964219 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1499 A B C _75298 x) = (term1500 A B C _75298 x).
Proof. exact (MK_COMB (@lem5964218) (@lem5964217 A B C _75298 x)). Qed.
Lemma lem5964220 {A B C : Type'} (_75298 : type441 A B C) (f : type1209 A B C) (x : type1412 A B C) : (term1493 A B C _75298 x f) = (term1482 A B C _75298 f x).
Proof. exact (eq_refl (term1493 A B C _75298 x f)). Qed.
Lemma lem5964221 {A B C : Type'} (i : type320 A B C) (f : type1209 A B C) : (i f) = (i f).
Proof. exact (eq_refl (i f)). Qed.
Lemma lem5964222 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (f : type1209 A B C) : (term1501 A B C _75298 x i f) = (term1502 A B C _75298 x i f).
Proof. exact (MK_COMB (@lem5964220 A B C _75298 f x) (@lem5964221 A B C i f)). Qed.
Lemma lem5964223 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (f : type1209 A B C) : (term1502 A B C _75298 x i f) = (term1503 A B C _75298 x i f).
Proof. exact (eq_refl (term1502 A B C _75298 x i f)). Qed.
Lemma lem5964224 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (f : type1209 A B C) : (term1501 A B C _75298 x i f) = (term1503 A B C _75298 x i f).
Proof. exact (TRANS (@lem5964222 A B C _75298 x i f) (@lem5964223 A B C _75298 x i f)). Qed.
Lemma lem5964225 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : (term1504 A B C _75298 x i) = (term1505 A B C _75298 x i).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5964224 A B C _75298 x i f)). Qed.
Lemma lem5964226 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem5964227 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : (term1506 A B C _75298 x i) = (term1507 A B C _75298 x i).
Proof. exact (MK_COMB (@lem5964226 A B C) (@lem5964225 A B C _75298 x i)). Qed.
Lemma lem5964228 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1508 A B C _75298 x) = (term1509 A B C _75298 x).
Proof. exact (fun_ext (fun i : type320 A B C => @lem5964227 A B C _75298 x i)). Qed.
Lemma lem5964229 {A B C : Type'} : (@ex (((prod A B) -> C) -> A)) = (@ex (((prod A B) -> C) -> A)).
Proof. exact (eq_refl (@ex (((prod A B) -> C) -> A))). Qed.
Lemma lem5964230 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1491 A B C _75298 x) = (term1510 A B C _75298 x).
Proof. exact (MK_COMB (@lem5964229 A B C) (@lem5964228 A B C _75298 x)). Qed.
Lemma lem5964231 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : ((term1490 A B C _75298 x) = (term1491 A B C _75298 x)) = ((term1485 A B C _75298 x) = (term1510 A B C _75298 x)).
Proof. exact (MK_COMB (@lem5964219 A B C _75298 x) (@lem5964230 A B C _75298 x)). Qed.
Lemma lem5964232 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1485 A B C _75298 x) = (term1510 A B C _75298 x).
Proof. exact (EQ_MP (@lem5964231 A B C _75298 x) (@lem5964206 A B C _75298 x)). Qed.
Lemma lem5964234 {A B : Type'} (P : type1413 A B) : (term1486 A B P) = (term1487 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5964235 {A B C : Type'} (P : type319 A B C) : (term1511 A B C P) = (term1512 A B C P).
Proof. exact (@lem5964234 (type1209 A B C) B P). Qed.
Lemma lem5964236 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : (term1513 A B C _75298 x i) = (term1514 A B C _75298 x i).
Proof. exact (@lem5964235 A B C (term1515 A B C _75298 x i)). Qed.
Lemma lem5964237 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (f : type1209 A B C) : (term1516 A B C _75298 x i f) = (term1517 A B C _75298 x i f).
Proof. exact (eq_refl (term1516 A B C _75298 x i f)). Qed.
Lemma lem5964238 {B : Type'} (j : B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5964239 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (f : type1209 A B C) (j : B) : (term1518 A B C _75298 x i f j) = (term1519 A B C _75298 x i f j).
Proof. exact (MK_COMB (@lem5964237 A B C _75298 x i f) (@lem5964238 B j)). Qed.
Lemma lem5964240 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (f : type1209 A B C) (j : B) : (term1519 A B C _75298 x i f j) = (term1520 A B C _75298 x i f j).
Proof. exact (eq_refl (term1519 A B C _75298 x i f j)). Qed.
Lemma lem5964241 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (f : type1209 A B C) (j : B) : (term1518 A B C _75298 x i f j) = (term1520 A B C _75298 x i f j).
Proof. exact (TRANS (@lem5964239 A B C _75298 x i f j) (@lem5964240 A B C _75298 x i f j)). Qed.
Lemma lem5964242 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (f : type1209 A B C) : (term1521 A B C _75298 x i f) = (term1517 A B C _75298 x i f).
Proof. exact (fun_ext (fun j : B => @lem5964241 A B C _75298 x i f j)). Qed.
Lemma lem5964243 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5964244 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (f : type1209 A B C) : (term1522 A B C _75298 x i f) = (term1503 A B C _75298 x i f).
Proof. exact (MK_COMB (@lem5964243 B) (@lem5964242 A B C _75298 x i f)). Qed.
Lemma lem5964245 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : (term1523 A B C _75298 x i) = (term1505 A B C _75298 x i).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5964244 A B C _75298 x i f)). Qed.
Lemma lem5964246 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem5964247 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : (term1513 A B C _75298 x i) = (term1507 A B C _75298 x i).
Proof. exact (MK_COMB (@lem5964246 A B C) (@lem5964245 A B C _75298 x i)). Qed.
Lemma lem5964248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964249 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : (term1524 A B C _75298 x i) = (term1525 A B C _75298 x i).
Proof. exact (MK_COMB (@lem5964248) (@lem5964247 A B C _75298 x i)). Qed.
Lemma lem5964250 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (f : type1209 A B C) : (term1516 A B C _75298 x i f) = (term1517 A B C _75298 x i f).
Proof. exact (eq_refl (term1516 A B C _75298 x i f)). Qed.
Lemma lem5964251 {A B C : Type'} (j : type321 A B C) (f : type1209 A B C) : (j f) = (j f).
Proof. exact (eq_refl (j f)). Qed.
Lemma lem5964252 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (j : type321 A B C) (f : type1209 A B C) : (term1526 A B C _75298 x i j f) = (term1527 A B C _75298 x i j f).
Proof. exact (MK_COMB (@lem5964250 A B C _75298 x i f) (@lem5964251 A B C j f)). Qed.
Lemma lem5964253 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (j : type321 A B C) (f : type1209 A B C) : (term1527 A B C _75298 x i j f) = (term1528 A B C _75298 x i j f).
Proof. exact (eq_refl (term1527 A B C _75298 x i j f)). Qed.
Lemma lem5964254 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (j : type321 A B C) (f : type1209 A B C) : (term1526 A B C _75298 x i j f) = (term1528 A B C _75298 x i j f).
Proof. exact (TRANS (@lem5964252 A B C _75298 x i j f) (@lem5964253 A B C _75298 x i j f)). Qed.
Lemma lem5964255 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (j : type321 A B C) : (term1529 A B C _75298 x i j) = (term1530 A B C _75298 x i j).
Proof. exact (fun_ext (fun f : type1209 A B C => @lem5964254 A B C _75298 x i j f)). Qed.
Lemma lem5964256 {A B C : Type'} : (@all ((prod A B) -> C)) = (@all ((prod A B) -> C)).
Proof. exact (eq_refl (@all ((prod A B) -> C))). Qed.
Lemma lem5964257 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) (j : type321 A B C) : (term1531 A B C _75298 x i j) = (term1532 A B C _75298 x i j).
Proof. exact (MK_COMB (@lem5964256 A B C) (@lem5964255 A B C _75298 x i j)). Qed.
Lemma lem5964258 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : (term1533 A B C _75298 x i) = (term1534 A B C _75298 x i).
Proof. exact (fun_ext (fun j : type321 A B C => @lem5964257 A B C _75298 x i j)). Qed.
Lemma lem5964259 {A B C : Type'} : (@ex (((prod A B) -> C) -> B)) = (@ex (((prod A B) -> C) -> B)).
Proof. exact (eq_refl (@ex (((prod A B) -> C) -> B))). Qed.
Lemma lem5964260 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : (term1514 A B C _75298 x i) = (term1535 A B C _75298 x i).
Proof. exact (MK_COMB (@lem5964259 A B C) (@lem5964258 A B C _75298 x i)). Qed.
Lemma lem5964261 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : ((term1513 A B C _75298 x i) = (term1514 A B C _75298 x i)) = ((term1507 A B C _75298 x i) = (term1535 A B C _75298 x i)).
Proof. exact (MK_COMB (@lem5964249 A B C _75298 x i) (@lem5964260 A B C _75298 x i)). Qed.
Lemma lem5964262 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : (term1507 A B C _75298 x i) = (term1535 A B C _75298 x i).
Proof. exact (EQ_MP (@lem5964261 A B C _75298 x i) (@lem5964236 A B C _75298 x i)). Qed.
Lemma lem5964263 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1509 A B C _75298 x) = (term1536 A B C _75298 x).
Proof. exact (fun_ext (fun i : type320 A B C => @lem5964262 A B C _75298 x i)). Qed.
Lemma lem5964264 {A B C : Type'} : (@ex (((prod A B) -> C) -> A)) = (@ex (((prod A B) -> C) -> A)).
Proof. exact (eq_refl (@ex (((prod A B) -> C) -> A))). Qed.
Lemma lem5964265 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1510 A B C _75298 x) = (term1537 A B C _75298 x).
Proof. exact (MK_COMB (@lem5964264 A B C) (@lem5964263 A B C _75298 x)). Qed.
Lemma lem5964266 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1485 A B C _75298 x) = (term1537 A B C _75298 x).
Proof. exact (TRANS (@lem5964232 A B C _75298 x) (@lem5964265 A B C _75298 x)). Qed.
Lemma lem5964267 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1427 A B C _75298 x) = (term1537 A B C _75298 x).
Proof. exact (TRANS (@lem5964202 A B C _75298 x) (@lem5964266 A B C _75298 x)). Qed.
Lemma lem5964268 {A B C : Type'} (_75298 : type441 A B C) : (term1440 A B C _75298) = (term1538 A B C _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5964267 A B C _75298 x)). Qed.
Lemma lem5964269 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5964270 {A B C : Type'} (_75298 : type441 A B C) : (term1451 A B C _75298) = (term1539 A B C _75298).
Proof. exact (MK_COMB (@lem5964269 A B C) (@lem5964268 A B C _75298)). Qed.
Lemma lem5964272 {A B : Type'} (P : type1413 A B) : (term1486 A B P) = (term1487 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5964273 {A B C : Type'} (P : type437 A B C) : (term1540 A B C P) = (term1541 A B C P).
Proof. exact (@lem5964272 (type1412 A B C) (type320 A B C) P). Qed.
Lemma lem5964274 {A B C : Type'} (_75298 : type441 A B C) : (term1542 A B C _75298) = (term1543 A B C _75298).
Proof. exact (@lem5964273 A B C (term1544 A B C _75298)). Qed.
Lemma lem5964275 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1545 A B C _75298 x) = (term1536 A B C _75298 x).
Proof. exact (eq_refl (term1545 A B C _75298 x)). Qed.
Lemma lem5964276 {A B C : Type'} (i : type320 A B C) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5964277 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : (term1546 A B C _75298 x i) = (term1547 A B C _75298 x i).
Proof. exact (MK_COMB (@lem5964275 A B C _75298 x) (@lem5964276 A B C i)). Qed.
Lemma lem5964278 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : (term1547 A B C _75298 x i) = (term1535 A B C _75298 x i).
Proof. exact (eq_refl (term1547 A B C _75298 x i)). Qed.
Lemma lem5964279 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) (i : type320 A B C) : (term1546 A B C _75298 x i) = (term1535 A B C _75298 x i).
Proof. exact (TRANS (@lem5964277 A B C _75298 x i) (@lem5964278 A B C _75298 x i)). Qed.
Lemma lem5964280 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1548 A B C _75298 x) = (term1536 A B C _75298 x).
Proof. exact (fun_ext (fun i : type320 A B C => @lem5964279 A B C _75298 x i)). Qed.
Lemma lem5964281 {A B C : Type'} : (@ex (((prod A B) -> C) -> A)) = (@ex (((prod A B) -> C) -> A)).
Proof. exact (eq_refl (@ex (((prod A B) -> C) -> A))). Qed.
Lemma lem5964282 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1549 A B C _75298 x) = (term1537 A B C _75298 x).
Proof. exact (MK_COMB (@lem5964281 A B C) (@lem5964280 A B C _75298 x)). Qed.
Lemma lem5964283 {A B C : Type'} (_75298 : type441 A B C) : (term1550 A B C _75298) = (term1538 A B C _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5964282 A B C _75298 x)). Qed.
Lemma lem5964284 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5964285 {A B C : Type'} (_75298 : type441 A B C) : (term1542 A B C _75298) = (term1539 A B C _75298).
Proof. exact (MK_COMB (@lem5964284 A B C) (@lem5964283 A B C _75298)). Qed.
Lemma lem5964286 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964287 {A B C : Type'} (_75298 : type441 A B C) : (term1551 A B C _75298) = (term1552 A B C _75298).
Proof. exact (MK_COMB (@lem5964286) (@lem5964285 A B C _75298)). Qed.
Lemma lem5964288 {A B C : Type'} (_75298 : type441 A B C) (x : type1412 A B C) : (term1545 A B C _75298 x) = (term1536 A B C _75298 x).
Proof. exact (eq_refl (term1545 A B C _75298 x)). Qed.
Lemma lem5964289 {A B C : Type'} (i : type439 A B C) (x : type1412 A B C) : (i x) = (i x).
Proof. exact (eq_refl (i x)). Qed.
Lemma lem5964290 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (x : type1412 A B C) : (term1553 A B C _75298 i x) = (term1554 A B C _75298 i x).
Proof. exact (MK_COMB (@lem5964288 A B C _75298 x) (@lem5964289 A B C i x)). Qed.
Lemma lem5964291 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (x : type1412 A B C) : (term1554 A B C _75298 i x) = (term1555 A B C _75298 i x).
Proof. exact (eq_refl (term1554 A B C _75298 i x)). Qed.
Lemma lem5964292 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (x : type1412 A B C) : (term1553 A B C _75298 i x) = (term1555 A B C _75298 i x).
Proof. exact (TRANS (@lem5964290 A B C _75298 i x) (@lem5964291 A B C _75298 i x)). Qed.
Lemma lem5964293 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1556 A B C _75298 i) = (term1557 A B C _75298 i).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5964292 A B C _75298 i x)). Qed.
Lemma lem5964294 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5964295 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1558 A B C _75298 i) = (term1559 A B C _75298 i).
Proof. exact (MK_COMB (@lem5964294 A B C) (@lem5964293 A B C _75298 i)). Qed.
Lemma lem5964296 {A B C : Type'} (_75298 : type441 A B C) : (term1560 A B C _75298) = (term1561 A B C _75298).
Proof. exact (fun_ext (fun i : type439 A B C => @lem5964295 A B C _75298 i)). Qed.
Lemma lem5964297 {A B C : Type'} : (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A)) = (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A))). Qed.
Lemma lem5964298 {A B C : Type'} (_75298 : type441 A B C) : (term1543 A B C _75298) = (term1562 A B C _75298).
Proof. exact (MK_COMB (@lem5964297 A B C) (@lem5964296 A B C _75298)). Qed.
Lemma lem5964299 {A B C : Type'} (_75298 : type441 A B C) : ((term1542 A B C _75298) = (term1543 A B C _75298)) = ((term1539 A B C _75298) = (term1562 A B C _75298)).
Proof. exact (MK_COMB (@lem5964287 A B C _75298) (@lem5964298 A B C _75298)). Qed.
Lemma lem5964300 {A B C : Type'} (_75298 : type441 A B C) : (term1539 A B C _75298) = (term1562 A B C _75298).
Proof. exact (EQ_MP (@lem5964299 A B C _75298) (@lem5964274 A B C _75298)). Qed.
Lemma lem5964302 {A B : Type'} (P : type1413 A B) : (term1486 A B P) = (term1487 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5964303 {A B C : Type'} (P : type438 A B C) : (term1563 A B C P) = (term1564 A B C P).
Proof. exact (@lem5964302 (type1412 A B C) (type321 A B C) P). Qed.
Lemma lem5964304 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1565 A B C _75298 i) = (term1566 A B C _75298 i).
Proof. exact (@lem5964303 A B C (term1567 A B C _75298 i)). Qed.
Lemma lem5964305 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (x : type1412 A B C) : (term1568 A B C _75298 i x) = (term1569 A B C _75298 i x).
Proof. exact (eq_refl (term1568 A B C _75298 i x)). Qed.
Lemma lem5964306 {A B C : Type'} (j : type321 A B C) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5964307 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (x : type1412 A B C) (j : type321 A B C) : (term1570 A B C _75298 i x j) = (term1571 A B C _75298 i x j).
Proof. exact (MK_COMB (@lem5964305 A B C _75298 i x) (@lem5964306 A B C j)). Qed.
Lemma lem5964308 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (x : type1412 A B C) (j : type321 A B C) : (term1571 A B C _75298 i x j) = (term1572 A B C _75298 i x j).
Proof. exact (eq_refl (term1571 A B C _75298 i x j)). Qed.
Lemma lem5964309 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (x : type1412 A B C) (j : type321 A B C) : (term1570 A B C _75298 i x j) = (term1572 A B C _75298 i x j).
Proof. exact (TRANS (@lem5964307 A B C _75298 i x j) (@lem5964308 A B C _75298 i x j)). Qed.
Lemma lem5964310 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (x : type1412 A B C) : (term1573 A B C _75298 i x) = (term1569 A B C _75298 i x).
Proof. exact (fun_ext (fun j : type321 A B C => @lem5964309 A B C _75298 i x j)). Qed.
Lemma lem5964311 {A B C : Type'} : (@ex (((prod A B) -> C) -> B)) = (@ex (((prod A B) -> C) -> B)).
Proof. exact (eq_refl (@ex (((prod A B) -> C) -> B))). Qed.
Lemma lem5964312 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (x : type1412 A B C) : (term1574 A B C _75298 i x) = (term1555 A B C _75298 i x).
Proof. exact (MK_COMB (@lem5964311 A B C) (@lem5964310 A B C _75298 i x)). Qed.
Lemma lem5964313 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1575 A B C _75298 i) = (term1557 A B C _75298 i).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5964312 A B C _75298 i x)). Qed.
Lemma lem5964314 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5964315 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1565 A B C _75298 i) = (term1559 A B C _75298 i).
Proof. exact (MK_COMB (@lem5964314 A B C) (@lem5964313 A B C _75298 i)). Qed.
Lemma lem5964316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964317 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1576 A B C _75298 i) = (term1577 A B C _75298 i).
Proof. exact (MK_COMB (@lem5964316) (@lem5964315 A B C _75298 i)). Qed.
Lemma lem5964318 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (x : type1412 A B C) : (term1568 A B C _75298 i x) = (term1569 A B C _75298 i x).
Proof. exact (eq_refl (term1568 A B C _75298 i x)). Qed.
Lemma lem5964319 {A B C : Type'} (j : type440 A B C) (x : type1412 A B C) : (j x) = (j x).
Proof. exact (eq_refl (j x)). Qed.
Lemma lem5964320 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (j : type440 A B C) (x : type1412 A B C) : (term1578 A B C _75298 i j x) = (term1579 A B C _75298 i j x).
Proof. exact (MK_COMB (@lem5964318 A B C _75298 i x) (@lem5964319 A B C j x)). Qed.
Lemma lem5964321 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (j : type440 A B C) (x : type1412 A B C) : (term1579 A B C _75298 i j x) = (term1580 A B C _75298 i j x).
Proof. exact (eq_refl (term1579 A B C _75298 i j x)). Qed.
Lemma lem5964322 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (j : type440 A B C) (x : type1412 A B C) : (term1578 A B C _75298 i j x) = (term1580 A B C _75298 i j x).
Proof. exact (TRANS (@lem5964320 A B C _75298 i j x) (@lem5964321 A B C _75298 i j x)). Qed.
Lemma lem5964323 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (j : type440 A B C) : (term1581 A B C _75298 i j) = (term1582 A B C _75298 i j).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5964322 A B C _75298 i j x)). Qed.
Lemma lem5964324 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5964325 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (j : type440 A B C) : (term1583 A B C _75298 i j) = (term1584 A B C _75298 i j).
Proof. exact (MK_COMB (@lem5964324 A B C) (@lem5964323 A B C _75298 i j)). Qed.
Lemma lem5964326 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1585 A B C _75298 i) = (term1586 A B C _75298 i).
Proof. exact (fun_ext (fun j : type440 A B C => @lem5964325 A B C _75298 i j)). Qed.
Lemma lem5964327 {A B C : Type'} : (@ex ((A -> B -> C) -> ((prod A B) -> C) -> B)) = (@ex ((A -> B -> C) -> ((prod A B) -> C) -> B)).
Proof. exact (eq_refl (@ex ((A -> B -> C) -> ((prod A B) -> C) -> B))). Qed.
Lemma lem5964328 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1566 A B C _75298 i) = (term1587 A B C _75298 i).
Proof. exact (MK_COMB (@lem5964327 A B C) (@lem5964326 A B C _75298 i)). Qed.
Lemma lem5964329 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : ((term1565 A B C _75298 i) = (term1566 A B C _75298 i)) = ((term1559 A B C _75298 i) = (term1587 A B C _75298 i)).
Proof. exact (MK_COMB (@lem5964317 A B C _75298 i) (@lem5964328 A B C _75298 i)). Qed.
Lemma lem5964330 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1559 A B C _75298 i) = (term1587 A B C _75298 i).
Proof. exact (EQ_MP (@lem5964329 A B C _75298 i) (@lem5964304 A B C _75298 i)). Qed.
Lemma lem5964331 {A B C : Type'} (_75298 : type441 A B C) : (term1561 A B C _75298) = (term1588 A B C _75298).
Proof. exact (fun_ext (fun i : type439 A B C => @lem5964330 A B C _75298 i)). Qed.
Lemma lem5964332 {A B C : Type'} : (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A)) = (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A))). Qed.
Lemma lem5964333 {A B C : Type'} (_75298 : type441 A B C) : (term1562 A B C _75298) = (term1589 A B C _75298).
Proof. exact (MK_COMB (@lem5964332 A B C) (@lem5964331 A B C _75298)). Qed.
Lemma lem5964334 {A B C : Type'} (_75298 : type441 A B C) : (term1539 A B C _75298) = (term1589 A B C _75298).
Proof. exact (TRANS (@lem5964300 A B C _75298) (@lem5964333 A B C _75298)). Qed.
Lemma lem5964335 {A B C : Type'} (_75298 : type441 A B C) : (term1451 A B C _75298) = (term1589 A B C _75298).
Proof. exact (TRANS (@lem5964270 A B C _75298) (@lem5964334 A B C _75298)). Qed.
Lemma lem5964336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964337 {A B C : Type'} (_75298 : type441 A B C) : (term1453 A B C _75298) = (term1590 A B C _75298).
Proof. exact (MK_COMB (@lem5964336) (@lem5964335 A B C _75298)). Qed.
Lemma lem5964338 {A B C : Type'} (_75298 : type441 A B C) : (term1456 A B C _75298) = (term1456 A B C _75298).
Proof. exact (eq_refl (term1456 A B C _75298)). Qed.
Lemma lem5964339 {A B C : Type'} (_75298 : type441 A B C) : (term1457 A B C _75298) = (term1591 A B C _75298).
Proof. exact (MK_COMB (@lem5964337 A B C _75298) (@lem5964338 A B C _75298)). Qed.
Lemma lem5964341 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5964342 {A B C : Type'} (P : type86 A B C) (Q : Prop) : (term1592 A B C P Q) = (term1593 A B C P Q).
Proof. exact (@lem5964341 (type439 A B C) P Q). Qed.
Lemma lem5964343 {A B C : Type'} (_75298 : type441 A B C) : (term1594 A B C _75298) = (term1595 A B C _75298).
Proof. exact (@lem5964342 A B C (term1588 A B C _75298) (term1456 A B C _75298)). Qed.
Lemma lem5964344 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1596 A B C _75298 i) = (term1587 A B C _75298 i).
Proof. exact (eq_refl (term1596 A B C _75298 i)). Qed.
Lemma lem5964345 {A B C : Type'} (_75298 : type441 A B C) : (term1597 A B C _75298) = (term1588 A B C _75298).
Proof. exact (fun_ext (fun i : type439 A B C => @lem5964344 A B C _75298 i)). Qed.
Lemma lem5964346 {A B C : Type'} : (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A)) = (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A))). Qed.
Lemma lem5964347 {A B C : Type'} (_75298 : type441 A B C) : (term1598 A B C _75298) = (term1589 A B C _75298).
Proof. exact (MK_COMB (@lem5964346 A B C) (@lem5964345 A B C _75298)). Qed.
Lemma lem5964348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964349 {A B C : Type'} (_75298 : type441 A B C) : (term1599 A B C _75298) = (term1590 A B C _75298).
Proof. exact (MK_COMB (@lem5964348) (@lem5964347 A B C _75298)). Qed.
Lemma lem5964350 {A B C : Type'} (_75298 : type441 A B C) : (term1456 A B C _75298) = (term1456 A B C _75298).
Proof. exact (eq_refl (term1456 A B C _75298)). Qed.
Lemma lem5964351 {A B C : Type'} (_75298 : type441 A B C) : (term1594 A B C _75298) = (term1591 A B C _75298).
Proof. exact (MK_COMB (@lem5964349 A B C _75298) (@lem5964350 A B C _75298)). Qed.
Lemma lem5964352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964353 {A B C : Type'} (_75298 : type441 A B C) : (term1600 A B C _75298) = (term1601 A B C _75298).
Proof. exact (MK_COMB (@lem5964352) (@lem5964351 A B C _75298)). Qed.
Lemma lem5964354 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1596 A B C _75298 i) = (term1587 A B C _75298 i).
Proof. exact (eq_refl (term1596 A B C _75298 i)). Qed.
Lemma lem5964355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964356 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1602 A B C _75298 i) = (term1603 A B C _75298 i).
Proof. exact (MK_COMB (@lem5964355) (@lem5964354 A B C _75298 i)). Qed.
Lemma lem5964357 {A B C : Type'} (_75298 : type441 A B C) : (term1456 A B C _75298) = (term1456 A B C _75298).
Proof. exact (eq_refl (term1456 A B C _75298)). Qed.
Lemma lem5964358 {A B C : Type'} (i : type439 A B C) (_75298 : type441 A B C) : (term1604 A B C i _75298) = (term1605 A B C i _75298).
Proof. exact (MK_COMB (@lem5964356 A B C _75298 i) (@lem5964357 A B C _75298)). Qed.
Lemma lem5964359 {A B C : Type'} (_75298 : type441 A B C) : (term1606 A B C _75298) = (term1607 A B C _75298).
Proof. exact (fun_ext (fun i : type439 A B C => @lem5964358 A B C i _75298)). Qed.
Lemma lem5964360 {A B C : Type'} : (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A)) = (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A))). Qed.
Lemma lem5964361 {A B C : Type'} (_75298 : type441 A B C) : (term1595 A B C _75298) = (term1608 A B C _75298).
Proof. exact (MK_COMB (@lem5964360 A B C) (@lem5964359 A B C _75298)). Qed.
Lemma lem5964362 {A B C : Type'} (_75298 : type441 A B C) : ((term1594 A B C _75298) = (term1595 A B C _75298)) = ((term1591 A B C _75298) = (term1608 A B C _75298)).
Proof. exact (MK_COMB (@lem5964353 A B C _75298) (@lem5964361 A B C _75298)). Qed.
Lemma lem5964363 {A B C : Type'} (_75298 : type441 A B C) : (term1591 A B C _75298) = (term1608 A B C _75298).
Proof. exact (EQ_MP (@lem5964362 A B C _75298) (@lem5964343 A B C _75298)). Qed.
Lemma lem5964365 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5964366 {A B C : Type'} (P : type87 A B C) (Q : Prop) : (term1609 A B C P Q) = (term1610 A B C P Q).
Proof. exact (@lem5964365 (type440 A B C) P Q). Qed.
Lemma lem5964367 {A B C : Type'} (i : type439 A B C) (_75298 : type441 A B C) : (term1611 A B C i _75298) = (term1612 A B C i _75298).
Proof. exact (@lem5964366 A B C (term1586 A B C _75298 i) (term1456 A B C _75298)). Qed.
Lemma lem5964368 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (j : type440 A B C) : (term1613 A B C _75298 i j) = (term1584 A B C _75298 i j).
Proof. exact (eq_refl (term1613 A B C _75298 i j)). Qed.
Lemma lem5964369 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1614 A B C _75298 i) = (term1586 A B C _75298 i).
Proof. exact (fun_ext (fun j : type440 A B C => @lem5964368 A B C _75298 i j)). Qed.
Lemma lem5964370 {A B C : Type'} : (@ex ((A -> B -> C) -> ((prod A B) -> C) -> B)) = (@ex ((A -> B -> C) -> ((prod A B) -> C) -> B)).
Proof. exact (eq_refl (@ex ((A -> B -> C) -> ((prod A B) -> C) -> B))). Qed.
Lemma lem5964371 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1615 A B C _75298 i) = (term1587 A B C _75298 i).
Proof. exact (MK_COMB (@lem5964370 A B C) (@lem5964369 A B C _75298 i)). Qed.
Lemma lem5964372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964373 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) : (term1616 A B C _75298 i) = (term1603 A B C _75298 i).
Proof. exact (MK_COMB (@lem5964372) (@lem5964371 A B C _75298 i)). Qed.
Lemma lem5964374 {A B C : Type'} (_75298 : type441 A B C) : (term1456 A B C _75298) = (term1456 A B C _75298).
Proof. exact (eq_refl (term1456 A B C _75298)). Qed.
Lemma lem5964375 {A B C : Type'} (i : type439 A B C) (_75298 : type441 A B C) : (term1611 A B C i _75298) = (term1605 A B C i _75298).
Proof. exact (MK_COMB (@lem5964373 A B C _75298 i) (@lem5964374 A B C _75298)). Qed.
Lemma lem5964376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964377 {A B C : Type'} (i : type439 A B C) (_75298 : type441 A B C) : (term1617 A B C i _75298) = (term1618 A B C i _75298).
Proof. exact (MK_COMB (@lem5964376) (@lem5964375 A B C i _75298)). Qed.
Lemma lem5964378 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (j : type440 A B C) : (term1613 A B C _75298 i j) = (term1584 A B C _75298 i j).
Proof. exact (eq_refl (term1613 A B C _75298 i j)). Qed.
Lemma lem5964379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964380 {A B C : Type'} (_75298 : type441 A B C) (i : type439 A B C) (j : type440 A B C) : (term1619 A B C _75298 i j) = (term1620 A B C _75298 i j).
Proof. exact (MK_COMB (@lem5964379) (@lem5964378 A B C _75298 i j)). Qed.
Lemma lem5964381 {A B C : Type'} (_75298 : type441 A B C) : (term1456 A B C _75298) = (term1456 A B C _75298).
Proof. exact (eq_refl (term1456 A B C _75298)). Qed.
Lemma lem5964382 {A B C : Type'} (i : type439 A B C) (j : type440 A B C) (_75298 : type441 A B C) : (term1621 A B C i j _75298) = (term1622 A B C i j _75298).
Proof. exact (MK_COMB (@lem5964380 A B C _75298 i j) (@lem5964381 A B C _75298)). Qed.
Lemma lem5964383 {A B C : Type'} (i : type439 A B C) (_75298 : type441 A B C) : (term1623 A B C i _75298) = (term1624 A B C i _75298).
Proof. exact (fun_ext (fun j : type440 A B C => @lem5964382 A B C i j _75298)). Qed.
Lemma lem5964384 {A B C : Type'} : (@ex ((A -> B -> C) -> ((prod A B) -> C) -> B)) = (@ex ((A -> B -> C) -> ((prod A B) -> C) -> B)).
Proof. exact (eq_refl (@ex ((A -> B -> C) -> ((prod A B) -> C) -> B))). Qed.
Lemma lem5964385 {A B C : Type'} (i : type439 A B C) (_75298 : type441 A B C) : (term1612 A B C i _75298) = (term1625 A B C i _75298).
Proof. exact (MK_COMB (@lem5964384 A B C) (@lem5964383 A B C i _75298)). Qed.
Lemma lem5964386 {A B C : Type'} (i : type439 A B C) (_75298 : type441 A B C) : ((term1611 A B C i _75298) = (term1612 A B C i _75298)) = ((term1605 A B C i _75298) = (term1625 A B C i _75298)).
Proof. exact (MK_COMB (@lem5964377 A B C i _75298) (@lem5964385 A B C i _75298)). Qed.
Lemma lem5964387 {A B C : Type'} (i : type439 A B C) (_75298 : type441 A B C) : (term1605 A B C i _75298) = (term1625 A B C i _75298).
Proof. exact (EQ_MP (@lem5964386 A B C i _75298) (@lem5964367 A B C i _75298)). Qed.
Lemma lem5964388 {A B C : Type'} (_75298 : type441 A B C) : (term1607 A B C _75298) = (term1626 A B C _75298).
Proof. exact (fun_ext (fun i : type439 A B C => @lem5964387 A B C i _75298)). Qed.
Lemma lem5964389 {A B C : Type'} : (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A)) = (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> C) -> ((prod A B) -> C) -> A))). Qed.
Lemma lem5964390 {A B C : Type'} (_75298 : type441 A B C) : (term1608 A B C _75298) = (term1627 A B C _75298).
Proof. exact (MK_COMB (@lem5964389 A B C) (@lem5964388 A B C _75298)). Qed.
Lemma lem5964391 {A B C : Type'} (_75298 : type441 A B C) : (term1591 A B C _75298) = (term1627 A B C _75298).
Proof. exact (TRANS (@lem5964363 A B C _75298) (@lem5964390 A B C _75298)). Qed.
Lemma lem5964392 {A B C : Type'} (_75298 : type441 A B C) : (term1457 A B C _75298) = (term1627 A B C _75298).
Proof. exact (TRANS (@lem5964339 A B C _75298) (@lem5964391 A B C _75298)). Qed.
Lemma lem5964393 {A B C : Type'} (_75298 : type441 A B C) : (term1409 A B C _75298) = (term1627 A B C _75298).
Proof. exact (TRANS (@lem5964155 A B C _75298) (@lem5964392 A B C _75298)). Qed.
Lemma lem5964394 {A B C : Type'} (_75298 : type441 A B C) : (term1375 A B C _75298) = (term1627 A B C _75298).
Proof. exact (TRANS (@lem5963861 A B C _75298) (@lem5964393 A B C _75298)). Qed.
Lemma lem5964395 {A B C : Type'} (_75298 : type441 A B C) (h1 : term1375 A B C _75298) : term1627 A B C _75298.
Proof. exact (EQ_MP (@lem5964394 A B C _75298) (@lem5963806 A B C _75298 h1)). Qed.
Lemma lem5964399 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) (j : B) : (term1126 A B GEN_PVAR_241 s t i j) = (term1126 A B GEN_PVAR_241 s t i j).
Proof. exact (eq_refl (term1126 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5964400 {B : Type'} (P : B -> Prop) : (term223 B P) = (term224 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem5964401 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1628 A B GEN_PVAR_241 s t i) = (term1629 A B GEN_PVAR_241 s t i).
Proof. exact (@lem5964400 B (term1127 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964402 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) (j : B) : (term1630 A B GEN_PVAR_241 s t i j) = (term1126 A B GEN_PVAR_241 s t i j).
Proof. exact (eq_refl (term1630 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5964403 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5964405 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) (j : B) : (term1631 A B GEN_PVAR_241 s t i j) = (term1632 A B GEN_PVAR_241 s t i j).
Proof. exact (MK_COMB (@lem5964403) (@lem5964402 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5964406 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1633 A B GEN_PVAR_241 s t i) = (term1634 A B GEN_PVAR_241 s t i).
Proof. exact (fun_ext (fun j : B => @lem5964405 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5964407 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5964408 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1629 A B GEN_PVAR_241 s t i) = (term1635 A B GEN_PVAR_241 s t i).
Proof. exact (MK_COMB (@lem5964407 B) (@lem5964406 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964409 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1628 A B GEN_PVAR_241 s t i) = (term1635 A B GEN_PVAR_241 s t i).
Proof. exact (TRANS (@lem5964401 A B GEN_PVAR_241 s t i) (@lem5964408 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964410 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1127 A B GEN_PVAR_241 s t i) = (term1127 A B GEN_PVAR_241 s t i).
Proof. exact (fun_ext (fun j : B => @lem5964399 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5964411 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5964412 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1128 A B GEN_PVAR_241 s t i) = (term1128 A B GEN_PVAR_241 s t i).
Proof. exact (MK_COMB (@lem5964411 B) (@lem5964410 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964413 {A : Type'} (P : A -> Prop) : (term223 A P) = (term224 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5964414 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1636 A B GEN_PVAR_241 s t) = (term1637 A B GEN_PVAR_241 s t).
Proof. exact (@lem5964413 A (term1129 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5964415 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1638 A B GEN_PVAR_241 s t i) = (term1128 A B GEN_PVAR_241 s t i).
Proof. exact (eq_refl (term1638 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964416 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5964417 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1639 A B GEN_PVAR_241 s t i) = (term1628 A B GEN_PVAR_241 s t i).
Proof. exact (MK_COMB (@lem5964416) (@lem5964415 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964418 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1639 A B GEN_PVAR_241 s t i) = (term1635 A B GEN_PVAR_241 s t i).
Proof. exact (TRANS (@lem5964417 A B GEN_PVAR_241 s t i) (@lem5964409 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964419 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1640 A B GEN_PVAR_241 s t) = (term1641 A B GEN_PVAR_241 s t).
Proof. exact (fun_ext (fun i : A => @lem5964418 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964420 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5964421 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1637 A B GEN_PVAR_241 s t) = (term1642 A B GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964420 A) (@lem5964419 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5964422 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1636 A B GEN_PVAR_241 s t) = (term1642 A B GEN_PVAR_241 s t).
Proof. exact (TRANS (@lem5964414 A B GEN_PVAR_241 s t) (@lem5964421 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5964423 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1129 A B GEN_PVAR_241 s t) = (term1129 A B GEN_PVAR_241 s t).
Proof. exact (fun_ext (fun i : A => @lem5964412 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964424 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5964425 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1028 A B GEN_PVAR_241 s t) = (term1028 A B GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964424 A) (@lem5964423 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5964427 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_241 : prod A B) : (term1643 A B _75297 s t GEN_PVAR_241) = (term1643 A B _75297 s t GEN_PVAR_241).
Proof. exact (eq_refl (term1643 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5964428 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1644 A B _75297 GEN_PVAR_241 s t) = (term1644 A B _75297 GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964427 A B _75297 s t GEN_PVAR_241) (@lem5964425 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5964430 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_241 : prod A B) : (term1645 A B _75297 s t GEN_PVAR_241) = (term1645 A B _75297 s t GEN_PVAR_241).
Proof. exact (eq_refl (term1645 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5964431 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1646 A B _75297 GEN_PVAR_241 s t) = (term1647 A B _75297 GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964430 A B _75297 s t GEN_PVAR_241) (@lem5964422 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5964432 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964433 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1648 A B _75297 GEN_PVAR_241 s t) = (term1649 A B _75297 GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964432) (@lem5964431 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964434 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1650 A B _75297 GEN_PVAR_241 s t) = (term1651 A B _75297 GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964433 A B _75297 GEN_PVAR_241 s t) (@lem5964428 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964435 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((_75297 s t GEN_PVAR_241) = (term1028 A B GEN_PVAR_241 s t)) = (term1650 A B _75297 GEN_PVAR_241 s t).
Proof. exact (@lem17784 (_75297 s t GEN_PVAR_241) (term1028 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5964436 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((_75297 s t GEN_PVAR_241) = (term1028 A B GEN_PVAR_241 s t)) = (term1651 A B _75297 GEN_PVAR_241 s t).
Proof. exact (TRANS (@lem5964435 A B _75297 GEN_PVAR_241 s t) (@lem5964434 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964437 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1296 A B _75297 s t) = (term1652 A B _75297 s t).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5964436 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964438 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5964439 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1297 A B _75297 s t) = (term1653 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964438 A B) (@lem5964437 A B _75297 s t)). Qed.
Lemma lem5964440 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1298 A B _75297 s) = (term1654 A B _75297 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5964439 A B _75297 s t)). Qed.
Lemma lem5964441 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5964442 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1299 A B _75297 s) = (term1655 A B _75297 s).
Proof. exact (MK_COMB (@lem5964441 A B) (@lem5964440 A B _75297 s)). Qed.
Lemma lem5964443 {A B : Type'} (_75297 : type621 A B) : (term1300 A B _75297) = (term1656 A B _75297).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5964442 A B _75297 s)). Qed.
Lemma lem5964444 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5964445 {A B : Type'} (_75297 : type621 A B) : (term1301 A B _75297) = (term1657 A B _75297).
Proof. exact (MK_COMB (@lem5964444 A) (@lem5964443 A B _75297)). Qed.
Lemma lem5964455 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1410 A P Q) = (term1411 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5964456 {A B : Type'} (P : type1210 A B) (Q : type1210 A B) : (term1658 A B P Q) = (term1659 A B P Q).
Proof. exact (@lem5964455 (prod A B) P Q). Qed.
Lemma lem5964457 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1660 A B _75297 s t) = (term1661 A B _75297 s t).
Proof. exact (@lem5964456 A B (term1662 A B _75297 s t) (term1663 A B _75297 s t)). Qed.
Lemma lem5964458 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1664 A B _75297 s t GEN_PVAR_241) = (term1647 A B _75297 GEN_PVAR_241 s t).
Proof. exact (eq_refl (term1664 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5964459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964460 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1665 A B _75297 s t GEN_PVAR_241) = (term1649 A B _75297 GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964459) (@lem5964458 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964461 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1666 A B _75297 s t GEN_PVAR_241) = (term1644 A B _75297 GEN_PVAR_241 s t).
Proof. exact (eq_refl (term1666 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5964462 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1667 A B _75297 s t GEN_PVAR_241) = (term1651 A B _75297 GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964460 A B _75297 GEN_PVAR_241 s t) (@lem5964461 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964463 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1668 A B _75297 s t) = (term1652 A B _75297 s t).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5964462 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964464 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5964465 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1660 A B _75297 s t) = (term1653 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964464 A B) (@lem5964463 A B _75297 s t)). Qed.
Lemma lem5964466 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964467 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1669 A B _75297 s t) = (term1670 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964466) (@lem5964465 A B _75297 s t)). Qed.
Lemma lem5964468 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1664 A B _75297 s t GEN_PVAR_241) = (term1647 A B _75297 GEN_PVAR_241 s t).
Proof. exact (eq_refl (term1664 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5964469 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1671 A B _75297 s t) = (term1662 A B _75297 s t).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5964468 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964470 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5964471 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1672 A B _75297 s t) = (term1673 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964470 A B) (@lem5964469 A B _75297 s t)). Qed.
Lemma lem5964472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964473 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1674 A B _75297 s t) = (term1675 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964472) (@lem5964471 A B _75297 s t)). Qed.
Lemma lem5964474 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1666 A B _75297 s t GEN_PVAR_241) = (term1644 A B _75297 GEN_PVAR_241 s t).
Proof. exact (eq_refl (term1666 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5964475 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1676 A B _75297 s t) = (term1663 A B _75297 s t).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5964474 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964476 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5964477 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1677 A B _75297 s t) = (term1678 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964476 A B) (@lem5964475 A B _75297 s t)). Qed.
Lemma lem5964478 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1661 A B _75297 s t) = (term1679 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964473 A B _75297 s t) (@lem5964477 A B _75297 s t)). Qed.
Lemma lem5964479 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((term1660 A B _75297 s t) = (term1661 A B _75297 s t)) = ((term1653 A B _75297 s t) = (term1679 A B _75297 s t)).
Proof. exact (MK_COMB (@lem5964467 A B _75297 s t) (@lem5964478 A B _75297 s t)). Qed.
Lemma lem5964480 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1653 A B _75297 s t) = (term1679 A B _75297 s t).
Proof. exact (EQ_MP (@lem5964479 A B _75297 s t) (@lem5964457 A B _75297 s t)). Qed.
Lemma lem5964593 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1654 A B _75297 s) = (term1680 A B _75297 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5964480 A B _75297 s t)). Qed.
Lemma lem5964594 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5964595 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1655 A B _75297 s) = (term1681 A B _75297 s).
Proof. exact (MK_COMB (@lem5964594 A B) (@lem5964593 A B _75297 s)). Qed.
Lemma lem5964597 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1410 A P Q) = (term1411 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5964598 {A B : Type'} (P : type475 A B) (Q : type475 A B) : (term1682 A B P Q) = (term1683 A B P Q).
Proof. exact (@lem5964597 (type1413 A B) P Q). Qed.
Lemma lem5964599 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1684 A B _75297 s) = (term1685 A B _75297 s).
Proof. exact (@lem5964598 A B (term1686 A B _75297 s) (term1687 A B _75297 s)). Qed.
Lemma lem5964600 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1688 A B _75297 s t) = (term1673 A B _75297 s t).
Proof. exact (eq_refl (term1688 A B _75297 s t)). Qed.
Lemma lem5964601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964602 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1689 A B _75297 s t) = (term1675 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964601) (@lem5964600 A B _75297 s t)). Qed.
Lemma lem5964603 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1690 A B _75297 s t) = (term1678 A B _75297 s t).
Proof. exact (eq_refl (term1690 A B _75297 s t)). Qed.
Lemma lem5964604 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1691 A B _75297 s t) = (term1679 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964602 A B _75297 s t) (@lem5964603 A B _75297 s t)). Qed.
Lemma lem5964605 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1692 A B _75297 s) = (term1680 A B _75297 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5964604 A B _75297 s t)). Qed.
Lemma lem5964606 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5964607 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1684 A B _75297 s) = (term1681 A B _75297 s).
Proof. exact (MK_COMB (@lem5964606 A B) (@lem5964605 A B _75297 s)). Qed.
Lemma lem5964608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964609 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1693 A B _75297 s) = (term1694 A B _75297 s).
Proof. exact (MK_COMB (@lem5964608) (@lem5964607 A B _75297 s)). Qed.
Lemma lem5964610 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1688 A B _75297 s t) = (term1673 A B _75297 s t).
Proof. exact (eq_refl (term1688 A B _75297 s t)). Qed.
Lemma lem5964611 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1695 A B _75297 s) = (term1686 A B _75297 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5964610 A B _75297 s t)). Qed.
Lemma lem5964612 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5964613 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1696 A B _75297 s) = (term1697 A B _75297 s).
Proof. exact (MK_COMB (@lem5964612 A B) (@lem5964611 A B _75297 s)). Qed.
Lemma lem5964614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964615 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1698 A B _75297 s) = (term1699 A B _75297 s).
Proof. exact (MK_COMB (@lem5964614) (@lem5964613 A B _75297 s)). Qed.
Lemma lem5964616 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1690 A B _75297 s t) = (term1678 A B _75297 s t).
Proof. exact (eq_refl (term1690 A B _75297 s t)). Qed.
Lemma lem5964617 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1700 A B _75297 s) = (term1687 A B _75297 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5964616 A B _75297 s t)). Qed.
Lemma lem5964618 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5964619 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1701 A B _75297 s) = (term1702 A B _75297 s).
Proof. exact (MK_COMB (@lem5964618 A B) (@lem5964617 A B _75297 s)). Qed.
Lemma lem5964620 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1685 A B _75297 s) = (term1703 A B _75297 s).
Proof. exact (MK_COMB (@lem5964615 A B _75297 s) (@lem5964619 A B _75297 s)). Qed.
Lemma lem5964621 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : ((term1684 A B _75297 s) = (term1685 A B _75297 s)) = ((term1681 A B _75297 s) = (term1703 A B _75297 s)).
Proof. exact (MK_COMB (@lem5964609 A B _75297 s) (@lem5964620 A B _75297 s)). Qed.
Lemma lem5964622 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1681 A B _75297 s) = (term1703 A B _75297 s).
Proof. exact (EQ_MP (@lem5964621 A B _75297 s) (@lem5964599 A B _75297 s)). Qed.
Lemma lem5964743 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1655 A B _75297 s) = (term1703 A B _75297 s).
Proof. exact (TRANS (@lem5964595 A B _75297 s) (@lem5964622 A B _75297 s)). Qed.
Lemma lem5964744 {A B : Type'} (_75297 : type621 A B) : (term1656 A B _75297) = (term1704 A B _75297).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5964743 A B _75297 s)). Qed.
Lemma lem5964745 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5964746 {A B : Type'} (_75297 : type621 A B) : (term1657 A B _75297) = (term1705 A B _75297).
Proof. exact (MK_COMB (@lem5964745 A) (@lem5964744 A B _75297)). Qed.
Lemma lem5964748 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1410 A P Q) = (term1411 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5964749 {A : Type'} (P : type686 A) (Q : type686 A) : (term1706 A P Q) = (term1707 A P Q).
Proof. exact (@lem5964748 (A -> Prop) P Q). Qed.
Lemma lem5964750 {A B : Type'} (_75297 : type621 A B) : (term1708 A B _75297) = (term1709 A B _75297).
Proof. exact (@lem5964749 A (term1710 A B _75297) (term1711 A B _75297)). Qed.
Lemma lem5964751 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1712 A B _75297 s) = (term1697 A B _75297 s).
Proof. exact (eq_refl (term1712 A B _75297 s)). Qed.
Lemma lem5964752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964753 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1713 A B _75297 s) = (term1699 A B _75297 s).
Proof. exact (MK_COMB (@lem5964752) (@lem5964751 A B _75297 s)). Qed.
Lemma lem5964754 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1714 A B _75297 s) = (term1702 A B _75297 s).
Proof. exact (eq_refl (term1714 A B _75297 s)). Qed.
Lemma lem5964755 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1715 A B _75297 s) = (term1703 A B _75297 s).
Proof. exact (MK_COMB (@lem5964753 A B _75297 s) (@lem5964754 A B _75297 s)). Qed.
Lemma lem5964756 {A B : Type'} (_75297 : type621 A B) : (term1716 A B _75297) = (term1704 A B _75297).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5964755 A B _75297 s)). Qed.
Lemma lem5964757 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5964758 {A B : Type'} (_75297 : type621 A B) : (term1708 A B _75297) = (term1705 A B _75297).
Proof. exact (MK_COMB (@lem5964757 A) (@lem5964756 A B _75297)). Qed.
Lemma lem5964759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964760 {A B : Type'} (_75297 : type621 A B) : (term1717 A B _75297) = (term1718 A B _75297).
Proof. exact (MK_COMB (@lem5964759) (@lem5964758 A B _75297)). Qed.
Lemma lem5964761 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1712 A B _75297 s) = (term1697 A B _75297 s).
Proof. exact (eq_refl (term1712 A B _75297 s)). Qed.
Lemma lem5964762 {A B : Type'} (_75297 : type621 A B) : (term1719 A B _75297) = (term1710 A B _75297).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5964761 A B _75297 s)). Qed.
Lemma lem5964763 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5964764 {A B : Type'} (_75297 : type621 A B) : (term1720 A B _75297) = (term1721 A B _75297).
Proof. exact (MK_COMB (@lem5964763 A) (@lem5964762 A B _75297)). Qed.
Lemma lem5964765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5964766 {A B : Type'} (_75297 : type621 A B) : (term1722 A B _75297) = (term1723 A B _75297).
Proof. exact (MK_COMB (@lem5964765) (@lem5964764 A B _75297)). Qed.
Lemma lem5964767 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1714 A B _75297 s) = (term1702 A B _75297 s).
Proof. exact (eq_refl (term1714 A B _75297 s)). Qed.
Lemma lem5964768 {A B : Type'} (_75297 : type621 A B) : (term1724 A B _75297) = (term1711 A B _75297).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5964767 A B _75297 s)). Qed.
Lemma lem5964769 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5964770 {A B : Type'} (_75297 : type621 A B) : (term1725 A B _75297) = (term1726 A B _75297).
Proof. exact (MK_COMB (@lem5964769 A) (@lem5964768 A B _75297)). Qed.
Lemma lem5964771 {A B : Type'} (_75297 : type621 A B) : (term1709 A B _75297) = (term1727 A B _75297).
Proof. exact (MK_COMB (@lem5964766 A B _75297) (@lem5964770 A B _75297)). Qed.
Lemma lem5964772 {A B : Type'} (_75297 : type621 A B) : ((term1708 A B _75297) = (term1709 A B _75297)) = ((term1705 A B _75297) = (term1727 A B _75297)).
Proof. exact (MK_COMB (@lem5964760 A B _75297) (@lem5964771 A B _75297)). Qed.
Lemma lem5964773 {A B : Type'} (_75297 : type621 A B) : (term1705 A B _75297) = (term1727 A B _75297).
Proof. exact (EQ_MP (@lem5964772 A B _75297) (@lem5964750 A B _75297)). Qed.
Lemma lem5964902 {A B : Type'} (_75297 : type621 A B) : (term1657 A B _75297) = (term1727 A B _75297).
Proof. exact (TRANS (@lem5964746 A B _75297) (@lem5964773 A B _75297)). Qed.
Lemma lem5964904 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5964905 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (@lem5964904 A P Q). Qed.
Lemma lem5964906 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1728 A B _75297 GEN_PVAR_241 s t) = (term1729 A B _75297 GEN_PVAR_241 s t).
Proof. exact (@lem5964905 A (term1730 A B _75297 s t GEN_PVAR_241) (term1129 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5964907 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1638 A B GEN_PVAR_241 s t i) = (term1128 A B GEN_PVAR_241 s t i).
Proof. exact (eq_refl (term1638 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964908 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1731 A B GEN_PVAR_241 s t) = (term1129 A B GEN_PVAR_241 s t).
Proof. exact (fun_ext (fun i : A => @lem5964907 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964909 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5964910 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1732 A B GEN_PVAR_241 s t) = (term1028 A B GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964909 A) (@lem5964908 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5964911 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_241 : prod A B) : (term1643 A B _75297 s t GEN_PVAR_241) = (term1643 A B _75297 s t GEN_PVAR_241).
Proof. exact (eq_refl (term1643 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5964912 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1728 A B _75297 GEN_PVAR_241 s t) = (term1644 A B _75297 GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964911 A B _75297 s t GEN_PVAR_241) (@lem5964910 A B GEN_PVAR_241 s t)). Qed.
Lemma lem5964913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964914 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1733 A B _75297 GEN_PVAR_241 s t) = (term1734 A B _75297 GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964913) (@lem5964912 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964915 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1638 A B GEN_PVAR_241 s t i) = (term1128 A B GEN_PVAR_241 s t i).
Proof. exact (eq_refl (term1638 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964916 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_241 : prod A B) : (term1643 A B _75297 s t GEN_PVAR_241) = (term1643 A B _75297 s t GEN_PVAR_241).
Proof. exact (eq_refl (term1643 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5964917 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1735 A B _75297 GEN_PVAR_241 s t i) = (term1736 A B _75297 GEN_PVAR_241 s t i).
Proof. exact (MK_COMB (@lem5964916 A B _75297 s t GEN_PVAR_241) (@lem5964915 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964918 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1737 A B _75297 GEN_PVAR_241 s t) = (term1738 A B _75297 GEN_PVAR_241 s t).
Proof. exact (fun_ext (fun i : A => @lem5964917 A B _75297 GEN_PVAR_241 s t i)). Qed.
Lemma lem5964919 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5964920 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1729 A B _75297 GEN_PVAR_241 s t) = (term1739 A B _75297 GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964919 A) (@lem5964918 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964921 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((term1728 A B _75297 GEN_PVAR_241 s t) = (term1729 A B _75297 GEN_PVAR_241 s t)) = ((term1644 A B _75297 GEN_PVAR_241 s t) = (term1739 A B _75297 GEN_PVAR_241 s t)).
Proof. exact (MK_COMB (@lem5964914 A B _75297 GEN_PVAR_241 s t) (@lem5964920 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964922 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1644 A B _75297 GEN_PVAR_241 s t) = (term1739 A B _75297 GEN_PVAR_241 s t).
Proof. exact (EQ_MP (@lem5964921 A B _75297 GEN_PVAR_241 s t) (@lem5964906 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964924 {A : Type'} (P : Prop) (Q : A -> Prop) : (term334 A P Q) = (term335 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5964925 {B : Type'} (P : Prop) (Q : B -> Prop) : (term334 B P Q) = (term335 B P Q).
Proof. exact (@lem5964924 B P Q). Qed.
Lemma lem5964926 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1740 A B _75297 GEN_PVAR_241 s t i) = (term1741 A B _75297 GEN_PVAR_241 s t i).
Proof. exact (@lem5964925 B (term1730 A B _75297 s t GEN_PVAR_241) (term1127 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964927 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) (j : B) : (term1630 A B GEN_PVAR_241 s t i j) = (term1126 A B GEN_PVAR_241 s t i j).
Proof. exact (eq_refl (term1630 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5964928 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1742 A B GEN_PVAR_241 s t i) = (term1127 A B GEN_PVAR_241 s t i).
Proof. exact (fun_ext (fun j : B => @lem5964927 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5964929 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5964930 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1743 A B GEN_PVAR_241 s t i) = (term1128 A B GEN_PVAR_241 s t i).
Proof. exact (MK_COMB (@lem5964929 B) (@lem5964928 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964931 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_241 : prod A B) : (term1643 A B _75297 s t GEN_PVAR_241) = (term1643 A B _75297 s t GEN_PVAR_241).
Proof. exact (eq_refl (term1643 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5964932 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1740 A B _75297 GEN_PVAR_241 s t i) = (term1736 A B _75297 GEN_PVAR_241 s t i).
Proof. exact (MK_COMB (@lem5964931 A B _75297 s t GEN_PVAR_241) (@lem5964930 A B GEN_PVAR_241 s t i)). Qed.
Lemma lem5964933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964934 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1744 A B _75297 GEN_PVAR_241 s t i) = (term1745 A B _75297 GEN_PVAR_241 s t i).
Proof. exact (MK_COMB (@lem5964933) (@lem5964932 A B _75297 GEN_PVAR_241 s t i)). Qed.
Lemma lem5964935 {A B : Type'} (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) (j : B) : (term1630 A B GEN_PVAR_241 s t i j) = (term1126 A B GEN_PVAR_241 s t i j).
Proof. exact (eq_refl (term1630 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5964936 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_241 : prod A B) : (term1643 A B _75297 s t GEN_PVAR_241) = (term1643 A B _75297 s t GEN_PVAR_241).
Proof. exact (eq_refl (term1643 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5964937 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) (j : B) : (term1746 A B _75297 GEN_PVAR_241 s t i j) = (term1747 A B _75297 GEN_PVAR_241 s t i j).
Proof. exact (MK_COMB (@lem5964936 A B _75297 s t GEN_PVAR_241) (@lem5964935 A B GEN_PVAR_241 s t i j)). Qed.
Lemma lem5964938 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1748 A B _75297 GEN_PVAR_241 s t i) = (term1749 A B _75297 GEN_PVAR_241 s t i).
Proof. exact (fun_ext (fun j : B => @lem5964937 A B _75297 GEN_PVAR_241 s t i j)). Qed.
Lemma lem5964939 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5964940 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1741 A B _75297 GEN_PVAR_241 s t i) = (term1750 A B _75297 GEN_PVAR_241 s t i).
Proof. exact (MK_COMB (@lem5964939 B) (@lem5964938 A B _75297 GEN_PVAR_241 s t i)). Qed.
Lemma lem5964941 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : ((term1740 A B _75297 GEN_PVAR_241 s t i) = (term1741 A B _75297 GEN_PVAR_241 s t i)) = ((term1736 A B _75297 GEN_PVAR_241 s t i) = (term1750 A B _75297 GEN_PVAR_241 s t i)).
Proof. exact (MK_COMB (@lem5964934 A B _75297 GEN_PVAR_241 s t i) (@lem5964940 A B _75297 GEN_PVAR_241 s t i)). Qed.
Lemma lem5964942 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1736 A B _75297 GEN_PVAR_241 s t i) = (term1750 A B _75297 GEN_PVAR_241 s t i).
Proof. exact (EQ_MP (@lem5964941 A B _75297 GEN_PVAR_241 s t i) (@lem5964926 A B _75297 GEN_PVAR_241 s t i)). Qed.
Lemma lem5964943 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1738 A B _75297 GEN_PVAR_241 s t) = (term1751 A B _75297 GEN_PVAR_241 s t).
Proof. exact (fun_ext (fun i : A => @lem5964942 A B _75297 GEN_PVAR_241 s t i)). Qed.
Lemma lem5964944 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5964945 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1739 A B _75297 GEN_PVAR_241 s t) = (term1752 A B _75297 GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964944 A) (@lem5964943 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964946 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1644 A B _75297 GEN_PVAR_241 s t) = (term1752 A B _75297 GEN_PVAR_241 s t).
Proof. exact (TRANS (@lem5964922 A B _75297 GEN_PVAR_241 s t) (@lem5964945 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964947 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1663 A B _75297 s t) = (term1753 A B _75297 s t).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5964946 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964948 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5964949 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1678 A B _75297 s t) = (term1754 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964948 A B) (@lem5964947 A B _75297 s t)). Qed.
Lemma lem5964951 {A B : Type'} (P : type1413 A B) : (term1486 A B P) = (term1487 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5964952 {A B : Type'} (P : type1205 A B) : (term1755 A B P) = (term1756 A B P).
Proof. exact (@lem5964951 (prod A B) A P). Qed.
Lemma lem5964953 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1757 A B _75297 s t) = (term1758 A B _75297 s t).
Proof. exact (@lem5964952 A B (term1759 A B _75297 s t)). Qed.
Lemma lem5964954 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1760 A B _75297 s t GEN_PVAR_241) = (term1751 A B _75297 GEN_PVAR_241 s t).
Proof. exact (eq_refl (term1760 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5964955 {A : Type'} (i : A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5964956 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1761 A B _75297 s t GEN_PVAR_241 i) = (term1762 A B _75297 GEN_PVAR_241 s t i).
Proof. exact (MK_COMB (@lem5964954 A B _75297 GEN_PVAR_241 s t) (@lem5964955 A i)). Qed.
Lemma lem5964957 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1762 A B _75297 GEN_PVAR_241 s t i) = (term1750 A B _75297 GEN_PVAR_241 s t i).
Proof. exact (eq_refl (term1762 A B _75297 GEN_PVAR_241 s t i)). Qed.
Lemma lem5964958 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) (i : A) : (term1761 A B _75297 s t GEN_PVAR_241 i) = (term1750 A B _75297 GEN_PVAR_241 s t i).
Proof. exact (TRANS (@lem5964956 A B _75297 GEN_PVAR_241 s t i) (@lem5964957 A B _75297 GEN_PVAR_241 s t i)). Qed.
Lemma lem5964959 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1763 A B _75297 s t GEN_PVAR_241) = (term1751 A B _75297 GEN_PVAR_241 s t).
Proof. exact (fun_ext (fun i : A => @lem5964958 A B _75297 GEN_PVAR_241 s t i)). Qed.
Lemma lem5964960 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5964961 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1764 A B _75297 s t GEN_PVAR_241) = (term1752 A B _75297 GEN_PVAR_241 s t).
Proof. exact (MK_COMB (@lem5964960 A) (@lem5964959 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964962 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1765 A B _75297 s t) = (term1753 A B _75297 s t).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5964961 A B _75297 GEN_PVAR_241 s t)). Qed.
Lemma lem5964963 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5964964 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1757 A B _75297 s t) = (term1754 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964963 A B) (@lem5964962 A B _75297 s t)). Qed.
Lemma lem5964965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964966 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1766 A B _75297 s t) = (term1767 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964965) (@lem5964964 A B _75297 s t)). Qed.
Lemma lem5964967 {A B : Type'} (_75297 : type621 A B) (GEN_PVAR_241 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1760 A B _75297 s t GEN_PVAR_241) = (term1751 A B _75297 GEN_PVAR_241 s t).
Proof. exact (eq_refl (term1760 A B _75297 s t GEN_PVAR_241)). Qed.
Lemma lem5964968 {A B : Type'} (i : type1207 A B) (GEN_PVAR_241 : prod A B) : (i GEN_PVAR_241) = (i GEN_PVAR_241).
Proof. exact (eq_refl (i GEN_PVAR_241)). Qed.
Lemma lem5964969 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (GEN_PVAR_241 : prod A B) : (term1768 A B _75297 s t i GEN_PVAR_241) = (term1769 A B _75297 s t i GEN_PVAR_241).
Proof. exact (MK_COMB (@lem5964967 A B _75297 GEN_PVAR_241 s t) (@lem5964968 A B i GEN_PVAR_241)). Qed.
Lemma lem5964970 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (GEN_PVAR_241 : prod A B) : (term1769 A B _75297 s t i GEN_PVAR_241) = (term1770 A B _75297 s t i GEN_PVAR_241).
Proof. exact (eq_refl (term1769 A B _75297 s t i GEN_PVAR_241)). Qed.
Lemma lem5964971 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (GEN_PVAR_241 : prod A B) : (term1768 A B _75297 s t i GEN_PVAR_241) = (term1770 A B _75297 s t i GEN_PVAR_241).
Proof. exact (TRANS (@lem5964969 A B _75297 s t i GEN_PVAR_241) (@lem5964970 A B _75297 s t i GEN_PVAR_241)). Qed.
Lemma lem5964972 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : (term1771 A B _75297 s t i) = (term1772 A B _75297 s t i).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5964971 A B _75297 s t i GEN_PVAR_241)). Qed.
Lemma lem5964973 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5964974 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : (term1773 A B _75297 s t i) = (term1774 A B _75297 s t i).
Proof. exact (MK_COMB (@lem5964973 A B) (@lem5964972 A B _75297 s t i)). Qed.
Lemma lem5964975 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1775 A B _75297 s t) = (term1776 A B _75297 s t).
Proof. exact (fun_ext (fun i : type1207 A B => @lem5964974 A B _75297 s t i)). Qed.
Lemma lem5964976 {A B : Type'} : (@ex ((prod A B) -> A)) = (@ex ((prod A B) -> A)).
Proof. exact (eq_refl (@ex ((prod A B) -> A))). Qed.
Lemma lem5964977 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1758 A B _75297 s t) = (term1777 A B _75297 s t).
Proof. exact (MK_COMB (@lem5964976 A B) (@lem5964975 A B _75297 s t)). Qed.
Lemma lem5964978 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((term1757 A B _75297 s t) = (term1758 A B _75297 s t)) = ((term1754 A B _75297 s t) = (term1777 A B _75297 s t)).
Proof. exact (MK_COMB (@lem5964966 A B _75297 s t) (@lem5964977 A B _75297 s t)). Qed.
Lemma lem5964979 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1754 A B _75297 s t) = (term1777 A B _75297 s t).
Proof. exact (EQ_MP (@lem5964978 A B _75297 s t) (@lem5964953 A B _75297 s t)). Qed.
Lemma lem5964981 {A B : Type'} (P : type1413 A B) : (term1486 A B P) = (term1487 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5964982 {A B : Type'} (P : type1206 A B) : (term1778 A B P) = (term1779 A B P).
Proof. exact (@lem5964981 (prod A B) B P). Qed.
Lemma lem5964983 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : (term1780 A B _75297 s t i) = (term1781 A B _75297 s t i).
Proof. exact (@lem5964982 A B (term1782 A B _75297 s t i)). Qed.
Lemma lem5964984 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (GEN_PVAR_241 : prod A B) : (term1783 A B _75297 s t i GEN_PVAR_241) = (term1784 A B _75297 s t i GEN_PVAR_241).
Proof. exact (eq_refl (term1783 A B _75297 s t i GEN_PVAR_241)). Qed.
Lemma lem5964985 {B : Type'} (j : B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5964986 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (GEN_PVAR_241 : prod A B) (j : B) : (term1785 A B _75297 s t i GEN_PVAR_241 j) = (term1786 A B _75297 s t i GEN_PVAR_241 j).
Proof. exact (MK_COMB (@lem5964984 A B _75297 s t i GEN_PVAR_241) (@lem5964985 B j)). Qed.
Lemma lem5964987 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (GEN_PVAR_241 : prod A B) (j : B) : (term1786 A B _75297 s t i GEN_PVAR_241 j) = (term1787 A B _75297 s t i GEN_PVAR_241 j).
Proof. exact (eq_refl (term1786 A B _75297 s t i GEN_PVAR_241 j)). Qed.
Lemma lem5964988 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (GEN_PVAR_241 : prod A B) (j : B) : (term1785 A B _75297 s t i GEN_PVAR_241 j) = (term1787 A B _75297 s t i GEN_PVAR_241 j).
Proof. exact (TRANS (@lem5964986 A B _75297 s t i GEN_PVAR_241 j) (@lem5964987 A B _75297 s t i GEN_PVAR_241 j)). Qed.
Lemma lem5964989 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (GEN_PVAR_241 : prod A B) : (term1788 A B _75297 s t i GEN_PVAR_241) = (term1784 A B _75297 s t i GEN_PVAR_241).
Proof. exact (fun_ext (fun j : B => @lem5964988 A B _75297 s t i GEN_PVAR_241 j)). Qed.
Lemma lem5964990 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5964991 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (GEN_PVAR_241 : prod A B) : (term1789 A B _75297 s t i GEN_PVAR_241) = (term1770 A B _75297 s t i GEN_PVAR_241).
Proof. exact (MK_COMB (@lem5964990 B) (@lem5964989 A B _75297 s t i GEN_PVAR_241)). Qed.
Lemma lem5964992 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : (term1790 A B _75297 s t i) = (term1772 A B _75297 s t i).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5964991 A B _75297 s t i GEN_PVAR_241)). Qed.
Lemma lem5964993 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5964994 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : (term1780 A B _75297 s t i) = (term1774 A B _75297 s t i).
Proof. exact (MK_COMB (@lem5964993 A B) (@lem5964992 A B _75297 s t i)). Qed.
Lemma lem5964995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5964996 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : (term1791 A B _75297 s t i) = (term1792 A B _75297 s t i).
Proof. exact (MK_COMB (@lem5964995) (@lem5964994 A B _75297 s t i)). Qed.
Lemma lem5964997 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (GEN_PVAR_241 : prod A B) : (term1783 A B _75297 s t i GEN_PVAR_241) = (term1784 A B _75297 s t i GEN_PVAR_241).
Proof. exact (eq_refl (term1783 A B _75297 s t i GEN_PVAR_241)). Qed.
Lemma lem5964998 {A B : Type'} (j : type1208 A B) (GEN_PVAR_241 : prod A B) : (j GEN_PVAR_241) = (j GEN_PVAR_241).
Proof. exact (eq_refl (j GEN_PVAR_241)). Qed.
Lemma lem5964999 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (j : type1208 A B) (GEN_PVAR_241 : prod A B) : (term1793 A B _75297 s t i j GEN_PVAR_241) = (term1794 A B _75297 s t i j GEN_PVAR_241).
Proof. exact (MK_COMB (@lem5964997 A B _75297 s t i GEN_PVAR_241) (@lem5964998 A B j GEN_PVAR_241)). Qed.
Lemma lem5965000 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (j : type1208 A B) (GEN_PVAR_241 : prod A B) : (term1794 A B _75297 s t i j GEN_PVAR_241) = (term1795 A B _75297 s t i j GEN_PVAR_241).
Proof. exact (eq_refl (term1794 A B _75297 s t i j GEN_PVAR_241)). Qed.
Lemma lem5965001 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (j : type1208 A B) (GEN_PVAR_241 : prod A B) : (term1793 A B _75297 s t i j GEN_PVAR_241) = (term1795 A B _75297 s t i j GEN_PVAR_241).
Proof. exact (TRANS (@lem5964999 A B _75297 s t i j GEN_PVAR_241) (@lem5965000 A B _75297 s t i j GEN_PVAR_241)). Qed.
Lemma lem5965002 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (j : type1208 A B) : (term1796 A B _75297 s t i j) = (term1797 A B _75297 s t i j).
Proof. exact (fun_ext (fun GEN_PVAR_241 : prod A B => @lem5965001 A B _75297 s t i j GEN_PVAR_241)). Qed.
Lemma lem5965003 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem5965004 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) (j : type1208 A B) : (term1798 A B _75297 s t i j) = (term1799 A B _75297 s t i j).
Proof. exact (MK_COMB (@lem5965003 A B) (@lem5965002 A B _75297 s t i j)). Qed.
Lemma lem5965005 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : (term1800 A B _75297 s t i) = (term1801 A B _75297 s t i).
Proof. exact (fun_ext (fun j : type1208 A B => @lem5965004 A B _75297 s t i j)). Qed.
Lemma lem5965006 {A B : Type'} : (@ex ((prod A B) -> B)) = (@ex ((prod A B) -> B)).
Proof. exact (eq_refl (@ex ((prod A B) -> B))). Qed.
Lemma lem5965007 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : (term1781 A B _75297 s t i) = (term1802 A B _75297 s t i).
Proof. exact (MK_COMB (@lem5965006 A B) (@lem5965005 A B _75297 s t i)). Qed.
Lemma lem5965008 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : ((term1780 A B _75297 s t i) = (term1781 A B _75297 s t i)) = ((term1774 A B _75297 s t i) = (term1802 A B _75297 s t i)).
Proof. exact (MK_COMB (@lem5964996 A B _75297 s t i) (@lem5965007 A B _75297 s t i)). Qed.
Lemma lem5965009 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : (term1774 A B _75297 s t i) = (term1802 A B _75297 s t i).
Proof. exact (EQ_MP (@lem5965008 A B _75297 s t i) (@lem5964983 A B _75297 s t i)). Qed.
Lemma lem5965010 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1776 A B _75297 s t) = (term1803 A B _75297 s t).
Proof. exact (fun_ext (fun i : type1207 A B => @lem5965009 A B _75297 s t i)). Qed.
Lemma lem5965011 {A B : Type'} : (@ex ((prod A B) -> A)) = (@ex ((prod A B) -> A)).
Proof. exact (eq_refl (@ex ((prod A B) -> A))). Qed.
Lemma lem5965012 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1777 A B _75297 s t) = (term1804 A B _75297 s t).
Proof. exact (MK_COMB (@lem5965011 A B) (@lem5965010 A B _75297 s t)). Qed.
Lemma lem5965013 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1754 A B _75297 s t) = (term1804 A B _75297 s t).
Proof. exact (TRANS (@lem5964979 A B _75297 s t) (@lem5965012 A B _75297 s t)). Qed.
Lemma lem5965014 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1678 A B _75297 s t) = (term1804 A B _75297 s t).
Proof. exact (TRANS (@lem5964949 A B _75297 s t) (@lem5965013 A B _75297 s t)). Qed.
Lemma lem5965015 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1687 A B _75297 s) = (term1805 A B _75297 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5965014 A B _75297 s t)). Qed.
Lemma lem5965016 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5965017 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1702 A B _75297 s) = (term1806 A B _75297 s).
Proof. exact (MK_COMB (@lem5965016 A B) (@lem5965015 A B _75297 s)). Qed.
Lemma lem5965019 {A B : Type'} (P : type1413 A B) : (term1486 A B P) = (term1487 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5965020 {A B : Type'} (P : type450 A B) : (term1807 A B P) = (term1808 A B P).
Proof. exact (@lem5965019 (type1413 A B) (type1207 A B) P). Qed.
Lemma lem5965021 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1809 A B _75297 s) = (term1810 A B _75297 s).
Proof. exact (@lem5965020 A B (term1811 A B _75297 s)). Qed.
Lemma lem5965022 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1812 A B _75297 s t) = (term1803 A B _75297 s t).
Proof. exact (eq_refl (term1812 A B _75297 s t)). Qed.
Lemma lem5965023 {A B : Type'} (i : type1207 A B) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5965024 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : (term1813 A B _75297 s t i) = (term1814 A B _75297 s t i).
Proof. exact (MK_COMB (@lem5965022 A B _75297 s t) (@lem5965023 A B i)). Qed.
Lemma lem5965025 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : (term1814 A B _75297 s t i) = (term1802 A B _75297 s t i).
Proof. exact (eq_refl (term1814 A B _75297 s t i)). Qed.
Lemma lem5965026 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (i : type1207 A B) : (term1813 A B _75297 s t i) = (term1802 A B _75297 s t i).
Proof. exact (TRANS (@lem5965024 A B _75297 s t i) (@lem5965025 A B _75297 s t i)). Qed.
Lemma lem5965027 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1815 A B _75297 s t) = (term1803 A B _75297 s t).
Proof. exact (fun_ext (fun i : type1207 A B => @lem5965026 A B _75297 s t i)). Qed.
Lemma lem5965028 {A B : Type'} : (@ex ((prod A B) -> A)) = (@ex ((prod A B) -> A)).
Proof. exact (eq_refl (@ex ((prod A B) -> A))). Qed.
Lemma lem5965029 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1816 A B _75297 s t) = (term1804 A B _75297 s t).
Proof. exact (MK_COMB (@lem5965028 A B) (@lem5965027 A B _75297 s t)). Qed.
Lemma lem5965030 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1817 A B _75297 s) = (term1805 A B _75297 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5965029 A B _75297 s t)). Qed.
Lemma lem5965031 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5965032 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1809 A B _75297 s) = (term1806 A B _75297 s).
Proof. exact (MK_COMB (@lem5965031 A B) (@lem5965030 A B _75297 s)). Qed.
Lemma lem5965033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5965034 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1818 A B _75297 s) = (term1819 A B _75297 s).
Proof. exact (MK_COMB (@lem5965033) (@lem5965032 A B _75297 s)). Qed.
Lemma lem5965035 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1812 A B _75297 s t) = (term1803 A B _75297 s t).
Proof. exact (eq_refl (term1812 A B _75297 s t)). Qed.
Lemma lem5965036 {A B : Type'} (i : type464 A B) (t : type1413 A B) : (i t) = (i t).
Proof. exact (eq_refl (i t)). Qed.
Lemma lem5965037 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (t : type1413 A B) : (term1820 A B _75297 s i t) = (term1821 A B _75297 s i t).
Proof. exact (MK_COMB (@lem5965035 A B _75297 s t) (@lem5965036 A B i t)). Qed.
Lemma lem5965038 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (t : type1413 A B) : (term1821 A B _75297 s i t) = (term1822 A B _75297 s i t).
Proof. exact (eq_refl (term1821 A B _75297 s i t)). Qed.
Lemma lem5965039 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (t : type1413 A B) : (term1820 A B _75297 s i t) = (term1822 A B _75297 s i t).
Proof. exact (TRANS (@lem5965037 A B _75297 s i t) (@lem5965038 A B _75297 s i t)). Qed.
Lemma lem5965040 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : (term1823 A B _75297 s i) = (term1824 A B _75297 s i).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5965039 A B _75297 s i t)). Qed.
Lemma lem5965041 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5965042 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : (term1825 A B _75297 s i) = (term1826 A B _75297 s i).
Proof. exact (MK_COMB (@lem5965041 A B) (@lem5965040 A B _75297 s i)). Qed.
Lemma lem5965043 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1827 A B _75297 s) = (term1828 A B _75297 s).
Proof. exact (fun_ext (fun i : type464 A B => @lem5965042 A B _75297 s i)). Qed.
Lemma lem5965044 {A B : Type'} : (@ex ((A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem5965045 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1810 A B _75297 s) = (term1829 A B _75297 s).
Proof. exact (MK_COMB (@lem5965044 A B) (@lem5965043 A B _75297 s)). Qed.
Lemma lem5965046 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : ((term1809 A B _75297 s) = (term1810 A B _75297 s)) = ((term1806 A B _75297 s) = (term1829 A B _75297 s)).
Proof. exact (MK_COMB (@lem5965034 A B _75297 s) (@lem5965045 A B _75297 s)). Qed.
Lemma lem5965047 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1806 A B _75297 s) = (term1829 A B _75297 s).
Proof. exact (EQ_MP (@lem5965046 A B _75297 s) (@lem5965021 A B _75297 s)). Qed.
Lemma lem5965049 {A B : Type'} (P : type1413 A B) : (term1486 A B P) = (term1487 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5965050 {A B : Type'} (P : type451 A B) : (term1830 A B P) = (term1831 A B P).
Proof. exact (@lem5965049 (type1413 A B) (type1208 A B) P). Qed.
Lemma lem5965051 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : (term1832 A B _75297 s i) = (term1833 A B _75297 s i).
Proof. exact (@lem5965050 A B (term1834 A B _75297 s i)). Qed.
Lemma lem5965052 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (t : type1413 A B) : (term1835 A B _75297 s i t) = (term1836 A B _75297 s i t).
Proof. exact (eq_refl (term1835 A B _75297 s i t)). Qed.
Lemma lem5965053 {A B : Type'} (j : type1208 A B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5965054 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (t : type1413 A B) (j : type1208 A B) : (term1837 A B _75297 s i t j) = (term1838 A B _75297 s i t j).
Proof. exact (MK_COMB (@lem5965052 A B _75297 s i t) (@lem5965053 A B j)). Qed.
Lemma lem5965055 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (t : type1413 A B) (j : type1208 A B) : (term1838 A B _75297 s i t j) = (term1839 A B _75297 s i t j).
Proof. exact (eq_refl (term1838 A B _75297 s i t j)). Qed.
Lemma lem5965056 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (t : type1413 A B) (j : type1208 A B) : (term1837 A B _75297 s i t j) = (term1839 A B _75297 s i t j).
Proof. exact (TRANS (@lem5965054 A B _75297 s i t j) (@lem5965055 A B _75297 s i t j)). Qed.
Lemma lem5965057 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (t : type1413 A B) : (term1840 A B _75297 s i t) = (term1836 A B _75297 s i t).
Proof. exact (fun_ext (fun j : type1208 A B => @lem5965056 A B _75297 s i t j)). Qed.
Lemma lem5965058 {A B : Type'} : (@ex ((prod A B) -> B)) = (@ex ((prod A B) -> B)).
Proof. exact (eq_refl (@ex ((prod A B) -> B))). Qed.
Lemma lem5965059 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (t : type1413 A B) : (term1841 A B _75297 s i t) = (term1822 A B _75297 s i t).
Proof. exact (MK_COMB (@lem5965058 A B) (@lem5965057 A B _75297 s i t)). Qed.
Lemma lem5965060 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : (term1842 A B _75297 s i) = (term1824 A B _75297 s i).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5965059 A B _75297 s i t)). Qed.
Lemma lem5965061 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5965062 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : (term1832 A B _75297 s i) = (term1826 A B _75297 s i).
Proof. exact (MK_COMB (@lem5965061 A B) (@lem5965060 A B _75297 s i)). Qed.
Lemma lem5965063 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5965064 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : (term1843 A B _75297 s i) = (term1844 A B _75297 s i).
Proof. exact (MK_COMB (@lem5965063) (@lem5965062 A B _75297 s i)). Qed.
Lemma lem5965065 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (t : type1413 A B) : (term1835 A B _75297 s i t) = (term1836 A B _75297 s i t).
Proof. exact (eq_refl (term1835 A B _75297 s i t)). Qed.
Lemma lem5965066 {A B : Type'} (j : type465 A B) (t : type1413 A B) : (j t) = (j t).
Proof. exact (eq_refl (j t)). Qed.
Lemma lem5965067 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (j : type465 A B) (t : type1413 A B) : (term1845 A B _75297 s i j t) = (term1846 A B _75297 s i j t).
Proof. exact (MK_COMB (@lem5965065 A B _75297 s i t) (@lem5965066 A B j t)). Qed.
Lemma lem5965068 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (j : type465 A B) (t : type1413 A B) : (term1846 A B _75297 s i j t) = (term1847 A B _75297 s i j t).
Proof. exact (eq_refl (term1846 A B _75297 s i j t)). Qed.
Lemma lem5965069 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (j : type465 A B) (t : type1413 A B) : (term1845 A B _75297 s i j t) = (term1847 A B _75297 s i j t).
Proof. exact (TRANS (@lem5965067 A B _75297 s i j t) (@lem5965068 A B _75297 s i j t)). Qed.
Lemma lem5965070 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (j : type465 A B) : (term1848 A B _75297 s i j) = (term1849 A B _75297 s i j).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5965069 A B _75297 s i j t)). Qed.
Lemma lem5965071 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5965072 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) (j : type465 A B) : (term1850 A B _75297 s i j) = (term1851 A B _75297 s i j).
Proof. exact (MK_COMB (@lem5965071 A B) (@lem5965070 A B _75297 s i j)). Qed.
Lemma lem5965073 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : (term1852 A B _75297 s i) = (term1853 A B _75297 s i).
Proof. exact (fun_ext (fun j : type465 A B => @lem5965072 A B _75297 s i j)). Qed.
Lemma lem5965074 {A B : Type'} : (@ex ((A -> B -> Prop) -> (prod A B) -> B)) = (@ex ((A -> B -> Prop) -> (prod A B) -> B)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> (prod A B) -> B))). Qed.
Lemma lem5965075 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : (term1833 A B _75297 s i) = (term1854 A B _75297 s i).
Proof. exact (MK_COMB (@lem5965074 A B) (@lem5965073 A B _75297 s i)). Qed.
Lemma lem5965076 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : ((term1832 A B _75297 s i) = (term1833 A B _75297 s i)) = ((term1826 A B _75297 s i) = (term1854 A B _75297 s i)).
Proof. exact (MK_COMB (@lem5965064 A B _75297 s i) (@lem5965075 A B _75297 s i)). Qed.
Lemma lem5965077 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : (term1826 A B _75297 s i) = (term1854 A B _75297 s i).
Proof. exact (EQ_MP (@lem5965076 A B _75297 s i) (@lem5965051 A B _75297 s i)). Qed.
Lemma lem5965078 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1828 A B _75297 s) = (term1855 A B _75297 s).
Proof. exact (fun_ext (fun i : type464 A B => @lem5965077 A B _75297 s i)). Qed.
Lemma lem5965079 {A B : Type'} : (@ex ((A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem5965080 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1829 A B _75297 s) = (term1856 A B _75297 s).
Proof. exact (MK_COMB (@lem5965079 A B) (@lem5965078 A B _75297 s)). Qed.
Lemma lem5965081 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1806 A B _75297 s) = (term1856 A B _75297 s).
Proof. exact (TRANS (@lem5965047 A B _75297 s) (@lem5965080 A B _75297 s)). Qed.
Lemma lem5965082 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1702 A B _75297 s) = (term1856 A B _75297 s).
Proof. exact (TRANS (@lem5965017 A B _75297 s) (@lem5965081 A B _75297 s)). Qed.
Lemma lem5965083 {A B : Type'} (_75297 : type621 A B) : (term1711 A B _75297) = (term1857 A B _75297).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5965082 A B _75297 s)). Qed.
Lemma lem5965084 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5965085 {A B : Type'} (_75297 : type621 A B) : (term1726 A B _75297) = (term1858 A B _75297).
Proof. exact (MK_COMB (@lem5965084 A) (@lem5965083 A B _75297)). Qed.
Lemma lem5965087 {A B : Type'} (P : type1413 A B) : (term1486 A B P) = (term1487 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5965088 {A B : Type'} (P : type584 A B) : (term1859 A B P) = (term1860 A B P).
Proof. exact (@lem5965087 (A -> Prop) (type464 A B) P). Qed.
Lemma lem5965089 {A B : Type'} (_75297 : type621 A B) : (term1861 A B _75297) = (term1862 A B _75297).
Proof. exact (@lem5965088 A B (term1863 A B _75297)). Qed.
Lemma lem5965090 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1864 A B _75297 s) = (term1855 A B _75297 s).
Proof. exact (eq_refl (term1864 A B _75297 s)). Qed.
Lemma lem5965091 {A B : Type'} (i : type464 A B) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5965092 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : (term1865 A B _75297 s i) = (term1866 A B _75297 s i).
Proof. exact (MK_COMB (@lem5965090 A B _75297 s) (@lem5965091 A B i)). Qed.
Lemma lem5965093 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : (term1866 A B _75297 s i) = (term1854 A B _75297 s i).
Proof. exact (eq_refl (term1866 A B _75297 s i)). Qed.
Lemma lem5965094 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) (i : type464 A B) : (term1865 A B _75297 s i) = (term1854 A B _75297 s i).
Proof. exact (TRANS (@lem5965092 A B _75297 s i) (@lem5965093 A B _75297 s i)). Qed.
Lemma lem5965095 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1867 A B _75297 s) = (term1855 A B _75297 s).
Proof. exact (fun_ext (fun i : type464 A B => @lem5965094 A B _75297 s i)). Qed.
Lemma lem5965096 {A B : Type'} : (@ex ((A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem5965097 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1868 A B _75297 s) = (term1856 A B _75297 s).
Proof. exact (MK_COMB (@lem5965096 A B) (@lem5965095 A B _75297 s)). Qed.
Lemma lem5965098 {A B : Type'} (_75297 : type621 A B) : (term1869 A B _75297) = (term1857 A B _75297).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5965097 A B _75297 s)). Qed.
Lemma lem5965099 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5965100 {A B : Type'} (_75297 : type621 A B) : (term1861 A B _75297) = (term1858 A B _75297).
Proof. exact (MK_COMB (@lem5965099 A) (@lem5965098 A B _75297)). Qed.
Lemma lem5965101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5965102 {A B : Type'} (_75297 : type621 A B) : (term1870 A B _75297) = (term1871 A B _75297).
Proof. exact (MK_COMB (@lem5965101) (@lem5965100 A B _75297)). Qed.
Lemma lem5965103 {A B : Type'} (_75297 : type621 A B) (s : A -> Prop) : (term1864 A B _75297 s) = (term1855 A B _75297 s).
Proof. exact (eq_refl (term1864 A B _75297 s)). Qed.
Lemma lem5965104 {A B : Type'} (i : type619 A B) (s : A -> Prop) : (i s) = (i s).
Proof. exact (eq_refl (i s)). Qed.
Lemma lem5965105 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (s : A -> Prop) : (term1872 A B _75297 i s) = (term1873 A B _75297 i s).
Proof. exact (MK_COMB (@lem5965103 A B _75297 s) (@lem5965104 A B i s)). Qed.
Lemma lem5965106 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (s : A -> Prop) : (term1873 A B _75297 i s) = (term1874 A B _75297 i s).
Proof. exact (eq_refl (term1873 A B _75297 i s)). Qed.
Lemma lem5965107 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (s : A -> Prop) : (term1872 A B _75297 i s) = (term1874 A B _75297 i s).
Proof. exact (TRANS (@lem5965105 A B _75297 i s) (@lem5965106 A B _75297 i s)). Qed.
Lemma lem5965108 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1875 A B _75297 i) = (term1876 A B _75297 i).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5965107 A B _75297 i s)). Qed.
Lemma lem5965109 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5965110 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1877 A B _75297 i) = (term1878 A B _75297 i).
Proof. exact (MK_COMB (@lem5965109 A) (@lem5965108 A B _75297 i)). Qed.
Lemma lem5965111 {A B : Type'} (_75297 : type621 A B) : (term1879 A B _75297) = (term1880 A B _75297).
Proof. exact (fun_ext (fun i : type619 A B => @lem5965110 A B _75297 i)). Qed.
Lemma lem5965112 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem5965113 {A B : Type'} (_75297 : type621 A B) : (term1862 A B _75297) = (term1881 A B _75297).
Proof. exact (MK_COMB (@lem5965112 A B) (@lem5965111 A B _75297)). Qed.
Lemma lem5965114 {A B : Type'} (_75297 : type621 A B) : ((term1861 A B _75297) = (term1862 A B _75297)) = ((term1858 A B _75297) = (term1881 A B _75297)).
Proof. exact (MK_COMB (@lem5965102 A B _75297) (@lem5965113 A B _75297)). Qed.
Lemma lem5965115 {A B : Type'} (_75297 : type621 A B) : (term1858 A B _75297) = (term1881 A B _75297).
Proof. exact (EQ_MP (@lem5965114 A B _75297) (@lem5965089 A B _75297)). Qed.
Lemma lem5965117 {A B : Type'} (P : type1413 A B) : (term1486 A B P) = (term1487 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5965118 {A B : Type'} (P : type585 A B) : (term1882 A B P) = (term1883 A B P).
Proof. exact (@lem5965117 (A -> Prop) (type465 A B) P). Qed.
Lemma lem5965119 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1884 A B _75297 i) = (term1885 A B _75297 i).
Proof. exact (@lem5965118 A B (term1886 A B _75297 i)). Qed.
Lemma lem5965120 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (s : A -> Prop) : (term1887 A B _75297 i s) = (term1888 A B _75297 i s).
Proof. exact (eq_refl (term1887 A B _75297 i s)). Qed.
Lemma lem5965121 {A B : Type'} (j : type465 A B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5965122 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (s : A -> Prop) (j : type465 A B) : (term1889 A B _75297 i s j) = (term1890 A B _75297 i s j).
Proof. exact (MK_COMB (@lem5965120 A B _75297 i s) (@lem5965121 A B j)). Qed.
Lemma lem5965123 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (s : A -> Prop) (j : type465 A B) : (term1890 A B _75297 i s j) = (term1891 A B _75297 i s j).
Proof. exact (eq_refl (term1890 A B _75297 i s j)). Qed.
Lemma lem5965124 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (s : A -> Prop) (j : type465 A B) : (term1889 A B _75297 i s j) = (term1891 A B _75297 i s j).
Proof. exact (TRANS (@lem5965122 A B _75297 i s j) (@lem5965123 A B _75297 i s j)). Qed.
Lemma lem5965125 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (s : A -> Prop) : (term1892 A B _75297 i s) = (term1888 A B _75297 i s).
Proof. exact (fun_ext (fun j : type465 A B => @lem5965124 A B _75297 i s j)). Qed.
Lemma lem5965126 {A B : Type'} : (@ex ((A -> B -> Prop) -> (prod A B) -> B)) = (@ex ((A -> B -> Prop) -> (prod A B) -> B)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> (prod A B) -> B))). Qed.
Lemma lem5965127 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (s : A -> Prop) : (term1893 A B _75297 i s) = (term1874 A B _75297 i s).
Proof. exact (MK_COMB (@lem5965126 A B) (@lem5965125 A B _75297 i s)). Qed.
Lemma lem5965128 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1894 A B _75297 i) = (term1876 A B _75297 i).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5965127 A B _75297 i s)). Qed.
Lemma lem5965129 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5965130 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1884 A B _75297 i) = (term1878 A B _75297 i).
Proof. exact (MK_COMB (@lem5965129 A) (@lem5965128 A B _75297 i)). Qed.
Lemma lem5965131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5965132 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1895 A B _75297 i) = (term1896 A B _75297 i).
Proof. exact (MK_COMB (@lem5965131) (@lem5965130 A B _75297 i)). Qed.
Lemma lem5965133 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (s : A -> Prop) : (term1887 A B _75297 i s) = (term1888 A B _75297 i s).
Proof. exact (eq_refl (term1887 A B _75297 i s)). Qed.
Lemma lem5965134 {A B : Type'} (j : type620 A B) (s : A -> Prop) : (j s) = (j s).
Proof. exact (eq_refl (j s)). Qed.
Lemma lem5965135 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (j : type620 A B) (s : A -> Prop) : (term1897 A B _75297 i j s) = (term1898 A B _75297 i j s).
Proof. exact (MK_COMB (@lem5965133 A B _75297 i s) (@lem5965134 A B j s)). Qed.
Lemma lem5965136 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (j : type620 A B) (s : A -> Prop) : (term1898 A B _75297 i j s) = (term1899 A B _75297 i j s).
Proof. exact (eq_refl (term1898 A B _75297 i j s)). Qed.
Lemma lem5965137 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (j : type620 A B) (s : A -> Prop) : (term1897 A B _75297 i j s) = (term1899 A B _75297 i j s).
Proof. exact (TRANS (@lem5965135 A B _75297 i j s) (@lem5965136 A B _75297 i j s)). Qed.
Lemma lem5965138 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (j : type620 A B) : (term1900 A B _75297 i j) = (term1901 A B _75297 i j).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5965137 A B _75297 i j s)). Qed.
Lemma lem5965139 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5965140 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (j : type620 A B) : (term1902 A B _75297 i j) = (term1903 A B _75297 i j).
Proof. exact (MK_COMB (@lem5965139 A) (@lem5965138 A B _75297 i j)). Qed.
Lemma lem5965141 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1904 A B _75297 i) = (term1905 A B _75297 i).
Proof. exact (fun_ext (fun j : type620 A B => @lem5965140 A B _75297 i j)). Qed.
Lemma lem5965142 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B))). Qed.
Lemma lem5965143 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1885 A B _75297 i) = (term1906 A B _75297 i).
Proof. exact (MK_COMB (@lem5965142 A B) (@lem5965141 A B _75297 i)). Qed.
Lemma lem5965144 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : ((term1884 A B _75297 i) = (term1885 A B _75297 i)) = ((term1878 A B _75297 i) = (term1906 A B _75297 i)).
Proof. exact (MK_COMB (@lem5965132 A B _75297 i) (@lem5965143 A B _75297 i)). Qed.
Lemma lem5965145 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1878 A B _75297 i) = (term1906 A B _75297 i).
Proof. exact (EQ_MP (@lem5965144 A B _75297 i) (@lem5965119 A B _75297 i)). Qed.
Lemma lem5965146 {A B : Type'} (_75297 : type621 A B) : (term1880 A B _75297) = (term1907 A B _75297).
Proof. exact (fun_ext (fun i : type619 A B => @lem5965145 A B _75297 i)). Qed.
Lemma lem5965147 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem5965148 {A B : Type'} (_75297 : type621 A B) : (term1881 A B _75297) = (term1908 A B _75297).
Proof. exact (MK_COMB (@lem5965147 A B) (@lem5965146 A B _75297)). Qed.
Lemma lem5965149 {A B : Type'} (_75297 : type621 A B) : (term1858 A B _75297) = (term1908 A B _75297).
Proof. exact (TRANS (@lem5965115 A B _75297) (@lem5965148 A B _75297)). Qed.
Lemma lem5965150 {A B : Type'} (_75297 : type621 A B) : (term1726 A B _75297) = (term1908 A B _75297).
Proof. exact (TRANS (@lem5965085 A B _75297) (@lem5965149 A B _75297)). Qed.
Lemma lem5965151 {A B : Type'} (_75297 : type621 A B) : (term1723 A B _75297) = (term1723 A B _75297).
Proof. exact (eq_refl (term1723 A B _75297)). Qed.
Lemma lem5965152 {A B : Type'} (_75297 : type621 A B) : (term1727 A B _75297) = (term1909 A B _75297).
Proof. exact (MK_COMB (@lem5965151 A B _75297) (@lem5965150 A B _75297)). Qed.
Lemma lem5965154 {A : Type'} (P : Prop) (Q : A -> Prop) : (term363 A P Q) = (term364 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5965155 {A B : Type'} (P : Prop) (Q : type128 A B) : (term1910 A B P Q) = (term1911 A B P Q).
Proof. exact (@lem5965154 (type619 A B) P Q). Qed.
Lemma lem5965156 {A B : Type'} (_75297 : type621 A B) : (term1912 A B _75297) = (term1913 A B _75297).
Proof. exact (@lem5965155 A B (term1721 A B _75297) (term1907 A B _75297)). Qed.
Lemma lem5965157 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1914 A B _75297 i) = (term1906 A B _75297 i).
Proof. exact (eq_refl (term1914 A B _75297 i)). Qed.
Lemma lem5965158 {A B : Type'} (_75297 : type621 A B) : (term1915 A B _75297) = (term1907 A B _75297).
Proof. exact (fun_ext (fun i : type619 A B => @lem5965157 A B _75297 i)). Qed.
Lemma lem5965159 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem5965160 {A B : Type'} (_75297 : type621 A B) : (term1916 A B _75297) = (term1908 A B _75297).
Proof. exact (MK_COMB (@lem5965159 A B) (@lem5965158 A B _75297)). Qed.
Lemma lem5965161 {A B : Type'} (_75297 : type621 A B) : (term1723 A B _75297) = (term1723 A B _75297).
Proof. exact (eq_refl (term1723 A B _75297)). Qed.
Lemma lem5965162 {A B : Type'} (_75297 : type621 A B) : (term1912 A B _75297) = (term1909 A B _75297).
Proof. exact (MK_COMB (@lem5965161 A B _75297) (@lem5965160 A B _75297)). Qed.
Lemma lem5965163 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5965164 {A B : Type'} (_75297 : type621 A B) : (term1917 A B _75297) = (term1918 A B _75297).
Proof. exact (MK_COMB (@lem5965163) (@lem5965162 A B _75297)). Qed.
Lemma lem5965165 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1914 A B _75297 i) = (term1906 A B _75297 i).
Proof. exact (eq_refl (term1914 A B _75297 i)). Qed.
Lemma lem5965166 {A B : Type'} (_75297 : type621 A B) : (term1723 A B _75297) = (term1723 A B _75297).
Proof. exact (eq_refl (term1723 A B _75297)). Qed.
Lemma lem5965167 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1919 A B _75297 i) = (term1920 A B _75297 i).
Proof. exact (MK_COMB (@lem5965166 A B _75297) (@lem5965165 A B _75297 i)). Qed.
Lemma lem5965168 {A B : Type'} (_75297 : type621 A B) : (term1921 A B _75297) = (term1922 A B _75297).
Proof. exact (fun_ext (fun i : type619 A B => @lem5965167 A B _75297 i)). Qed.
Lemma lem5965169 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem5965170 {A B : Type'} (_75297 : type621 A B) : (term1913 A B _75297) = (term1923 A B _75297).
Proof. exact (MK_COMB (@lem5965169 A B) (@lem5965168 A B _75297)). Qed.
Lemma lem5965171 {A B : Type'} (_75297 : type621 A B) : ((term1912 A B _75297) = (term1913 A B _75297)) = ((term1909 A B _75297) = (term1923 A B _75297)).
Proof. exact (MK_COMB (@lem5965164 A B _75297) (@lem5965170 A B _75297)). Qed.
Lemma lem5965172 {A B : Type'} (_75297 : type621 A B) : (term1909 A B _75297) = (term1923 A B _75297).
Proof. exact (EQ_MP (@lem5965171 A B _75297) (@lem5965156 A B _75297)). Qed.
Lemma lem5965174 {A : Type'} (P : Prop) (Q : A -> Prop) : (term363 A P Q) = (term364 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5965175 {A B : Type'} (P : Prop) (Q : type129 A B) : (term1924 A B P Q) = (term1925 A B P Q).
Proof. exact (@lem5965174 (type620 A B) P Q). Qed.
Lemma lem5965176 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1926 A B _75297 i) = (term1927 A B _75297 i).
Proof. exact (@lem5965175 A B (term1721 A B _75297) (term1905 A B _75297 i)). Qed.
Lemma lem5965177 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (j : type620 A B) : (term1928 A B _75297 i j) = (term1903 A B _75297 i j).
Proof. exact (eq_refl (term1928 A B _75297 i j)). Qed.
Lemma lem5965178 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1929 A B _75297 i) = (term1905 A B _75297 i).
Proof. exact (fun_ext (fun j : type620 A B => @lem5965177 A B _75297 i j)). Qed.
Lemma lem5965179 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B))). Qed.
Lemma lem5965180 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1930 A B _75297 i) = (term1906 A B _75297 i).
Proof. exact (MK_COMB (@lem5965179 A B) (@lem5965178 A B _75297 i)). Qed.
Lemma lem5965181 {A B : Type'} (_75297 : type621 A B) : (term1723 A B _75297) = (term1723 A B _75297).
Proof. exact (eq_refl (term1723 A B _75297)). Qed.
Lemma lem5965182 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1926 A B _75297 i) = (term1920 A B _75297 i).
Proof. exact (MK_COMB (@lem5965181 A B _75297) (@lem5965180 A B _75297 i)). Qed.
Lemma lem5965183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5965184 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1931 A B _75297 i) = (term1932 A B _75297 i).
Proof. exact (MK_COMB (@lem5965183) (@lem5965182 A B _75297 i)). Qed.
Lemma lem5965185 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (j : type620 A B) : (term1928 A B _75297 i j) = (term1903 A B _75297 i j).
Proof. exact (eq_refl (term1928 A B _75297 i j)). Qed.
Lemma lem5965186 {A B : Type'} (_75297 : type621 A B) : (term1723 A B _75297) = (term1723 A B _75297).
Proof. exact (eq_refl (term1723 A B _75297)). Qed.
Lemma lem5965187 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) (j : type620 A B) : (term1933 A B _75297 i j) = (term1934 A B _75297 i j).
Proof. exact (MK_COMB (@lem5965186 A B _75297) (@lem5965185 A B _75297 i j)). Qed.
Lemma lem5965188 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1935 A B _75297 i) = (term1936 A B _75297 i).
Proof. exact (fun_ext (fun j : type620 A B => @lem5965187 A B _75297 i j)). Qed.
Lemma lem5965189 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B))). Qed.
Lemma lem5965190 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1927 A B _75297 i) = (term1937 A B _75297 i).
Proof. exact (MK_COMB (@lem5965189 A B) (@lem5965188 A B _75297 i)). Qed.
Lemma lem5965191 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : ((term1926 A B _75297 i) = (term1927 A B _75297 i)) = ((term1920 A B _75297 i) = (term1937 A B _75297 i)).
Proof. exact (MK_COMB (@lem5965184 A B _75297 i) (@lem5965190 A B _75297 i)). Qed.
Lemma lem5965192 {A B : Type'} (_75297 : type621 A B) (i : type619 A B) : (term1920 A B _75297 i) = (term1937 A B _75297 i).
Proof. exact (EQ_MP (@lem5965191 A B _75297 i) (@lem5965176 A B _75297 i)). Qed.
Lemma lem5965193 {A B : Type'} (_75297 : type621 A B) : (term1922 A B _75297) = (term1938 A B _75297).
Proof. exact (fun_ext (fun i : type619 A B => @lem5965192 A B _75297 i)). Qed.
Lemma lem5965194 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem5965195 {A B : Type'} (_75297 : type621 A B) : (term1923 A B _75297) = (term1939 A B _75297).
Proof. exact (MK_COMB (@lem5965194 A B) (@lem5965193 A B _75297)). Qed.
Lemma lem5965196 {A B : Type'} (_75297 : type621 A B) : (term1909 A B _75297) = (term1939 A B _75297).
Proof. exact (TRANS (@lem5965172 A B _75297) (@lem5965195 A B _75297)). Qed.
Lemma lem5965197 {A B : Type'} (_75297 : type621 A B) : (term1727 A B _75297) = (term1939 A B _75297).
Proof. exact (TRANS (@lem5965152 A B _75297) (@lem5965196 A B _75297)). Qed.
Lemma lem5965198 {A B : Type'} (_75297 : type621 A B) : (term1657 A B _75297) = (term1939 A B _75297).
Proof. exact (TRANS (@lem5964902 A B _75297) (@lem5965197 A B _75297)). Qed.
Lemma lem5965199 {A B : Type'} (_75297 : type621 A B) : (term1301 A B _75297) = (term1939 A B _75297).
Proof. exact (TRANS (@lem5964445 A B _75297) (@lem5965198 A B _75297)). Qed.
Lemma lem5965200 {A B : Type'} (_75297 : type621 A B) (h1 : term1301 A B _75297) : term1939 A B _75297.
Proof. exact (EQ_MP (@lem5965199 A B _75297) (@lem5963807 A B _75297 h1)). Qed.
Lemma lem5965247 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : (term1940 A B s t i) = (term1941 A B s t i).
Proof. exact (@lem17362 (@IN A i s) (term717 A B t i)). Qed.
Lemma lem5965248 {A : Type'} (P : A -> Prop) : (term1380 A P) = (term1381 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5965249 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1942 A B s t) = (term1943 A B s t).
Proof. exact (@lem5965248 A (term913 A B s t)). Qed.
Lemma lem5965250 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : (term1944 A B s t i) = (term911 A B s t i).
Proof. exact (eq_refl (term1944 A B s t i)). Qed.
Lemma lem5965251 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5965252 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : (term1945 A B s t i) = (term1940 A B s t i).
Proof. exact (MK_COMB (@lem5965251) (@lem5965250 A B s t i)). Qed.
Lemma lem5965253 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : (term1945 A B s t i) = (term1941 A B s t i).
Proof. exact (TRANS (@lem5965252 A B s t i) (@lem5965247 A B s t i)). Qed.
Lemma lem5965254 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1946 A B s t) = (term1947 A B s t).
Proof. exact (fun_ext (fun i : A => @lem5965253 A B s t i)). Qed.
Lemma lem5965255 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5965256 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1943 A B s t) = (term1948 A B s t).
Proof. exact (MK_COMB (@lem5965255 A) (@lem5965254 A B s t)). Qed.
Lemma lem5965257 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1942 A B s t) = (term1948 A B s t).
Proof. exact (TRANS (@lem5965249 A B s t) (@lem5965256 A B s t)). Qed.
Lemma lem5965258 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) (x : type1412 A B C) : ((term1131 A B C s _75296 op t x) = (term1310 A B C op _75297 s t _75298 x)) = ((term1131 A B C s _75296 op t x) = (term1310 A B C op _75297 s t _75298 x)).
Proof. exact (eq_refl ((term1131 A B C s _75296 op t x) = (term1310 A B C op _75297 s t _75298 x))). Qed.
Lemma lem5965259 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1311 A B C _75296 op _75297 s t _75298) = (term1311 A B C _75296 op _75297 s t _75298).
Proof. exact (fun_ext (fun x : type1412 A B C => @lem5965258 A B C _75296 op _75297 s t _75298 x)). Qed.
Lemma lem5965260 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem5965261 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1312 A B C _75296 op _75297 s t _75298) = (term1312 A B C _75296 op _75297 s t _75298).
Proof. exact (MK_COMB (@lem5965260 A B C) (@lem5965259 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965262 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5965263 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1949 A B s t) = (term1950 A B s t).
Proof. exact (MK_COMB (@lem5965262) (@lem5965257 A B s t)). Qed.
Lemma lem5965264 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1951 A B C _75296 op _75297 s t _75298) = (term1952 A B C _75296 op _75297 s t _75298).
Proof. exact (MK_COMB (@lem5965263 A B s t) (@lem5965261 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965265 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1313 A B C _75296 op _75297 s t _75298) = (term1951 A B C _75296 op _75297 s t _75298).
Proof. exact (@lem17265 (term630 A B s t) (term1312 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965266 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1313 A B C _75296 op _75297 s t _75298) = (term1952 A B C _75296 op _75297 s t _75298).
Proof. exact (TRANS (@lem5965265 A B C _75296 op _75297 s t _75298) (@lem5965264 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965267 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1314 A B C _75296 op _75297 s _75298) = (term1953 A B C _75296 op _75297 s _75298).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5965266 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965268 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5965269 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1315 A B C _75296 op _75297 s _75298) = (term1954 A B C _75296 op _75297 s _75298).
Proof. exact (MK_COMB (@lem5965268 A B) (@lem5965267 A B C _75296 op _75297 s _75298)). Qed.
Lemma lem5965372 {A : Type'} (P : A -> Prop) (Q : Prop) : (term318 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5965373 {A : Type'} (P : A -> Prop) (Q : Prop) : (term318 A P Q) = (term319 A P Q).
Proof. exact (@lem5965372 A P Q). Qed.
Lemma lem5965374 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1955 A B C _75296 op _75297 s t _75298) = (term1956 A B C _75296 op _75297 s t _75298).
Proof. exact (@lem5965373 A (term1947 A B s t) (term1312 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965375 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : (term1957 A B s t i) = (term1941 A B s t i).
Proof. exact (eq_refl (term1957 A B s t i)). Qed.
Lemma lem5965376 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1958 A B s t) = (term1947 A B s t).
Proof. exact (fun_ext (fun i : A => @lem5965375 A B s t i)). Qed.
Lemma lem5965377 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5965378 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1959 A B s t) = (term1948 A B s t).
Proof. exact (MK_COMB (@lem5965377 A) (@lem5965376 A B s t)). Qed.
Lemma lem5965379 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5965380 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1960 A B s t) = (term1950 A B s t).
Proof. exact (MK_COMB (@lem5965379) (@lem5965378 A B s t)). Qed.
Lemma lem5965381 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1312 A B C _75296 op _75297 s t _75298) = (term1312 A B C _75296 op _75297 s t _75298).
Proof. exact (eq_refl (term1312 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965382 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1955 A B C _75296 op _75297 s t _75298) = (term1952 A B C _75296 op _75297 s t _75298).
Proof. exact (MK_COMB (@lem5965380 A B s t) (@lem5965381 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5965384 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1961 A B C _75296 op _75297 s t _75298) = (term1962 A B C _75296 op _75297 s t _75298).
Proof. exact (MK_COMB (@lem5965383) (@lem5965382 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965385 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : (term1957 A B s t i) = (term1941 A B s t i).
Proof. exact (eq_refl (term1957 A B s t i)). Qed.
Lemma lem5965386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5965387 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (i : A) : (term1963 A B s t i) = (term1964 A B s t i).
Proof. exact (MK_COMB (@lem5965386) (@lem5965385 A B s t i)). Qed.
Lemma lem5965388 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1312 A B C _75296 op _75297 s t _75298) = (term1312 A B C _75296 op _75297 s t _75298).
Proof. exact (eq_refl (term1312 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965389 {A B C : Type'} (i : A) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1965 A B C i _75296 op _75297 s t _75298) = (term1966 A B C i _75296 op _75297 s t _75298).
Proof. exact (MK_COMB (@lem5965387 A B s t i) (@lem5965388 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965390 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1967 A B C _75296 op _75297 s t _75298) = (term1968 A B C _75296 op _75297 s t _75298).
Proof. exact (fun_ext (fun i : A => @lem5965389 A B C i _75296 op _75297 s t _75298)). Qed.
Lemma lem5965391 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5965392 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1956 A B C _75296 op _75297 s t _75298) = (term1969 A B C _75296 op _75297 s t _75298).
Proof. exact (MK_COMB (@lem5965391 A) (@lem5965390 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965393 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : ((term1955 A B C _75296 op _75297 s t _75298) = (term1956 A B C _75296 op _75297 s t _75298)) = ((term1952 A B C _75296 op _75297 s t _75298) = (term1969 A B C _75296 op _75297 s t _75298)).
Proof. exact (MK_COMB (@lem5965384 A B C _75296 op _75297 s t _75298) (@lem5965392 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965394 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1952 A B C _75296 op _75297 s t _75298) = (term1969 A B C _75296 op _75297 s t _75298).
Proof. exact (EQ_MP (@lem5965393 A B C _75296 op _75297 s t _75298) (@lem5965374 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965395 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1953 A B C _75296 op _75297 s _75298) = (term1970 A B C _75296 op _75297 s _75298).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5965394 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965396 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5965397 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1954 A B C _75296 op _75297 s _75298) = (term1971 A B C _75296 op _75297 s _75298).
Proof. exact (MK_COMB (@lem5965396 A B) (@lem5965395 A B C _75296 op _75297 s _75298)). Qed.
Lemma lem5965399 {A B : Type'} (P : type1413 A B) : (term1486 A B P) = (term1487 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5965400 {A B : Type'} (P : type468 A B) : (term1972 A B P) = (term1973 A B P).
Proof. exact (@lem5965399 (type1413 A B) A P). Qed.
Lemma lem5965401 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1974 A B C _75296 op _75297 s _75298) = (term1975 A B C _75296 op _75297 s _75298).
Proof. exact (@lem5965400 A B (term1976 A B C _75296 op _75297 s _75298)). Qed.
Lemma lem5965402 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1977 A B C _75296 op _75297 s _75298 t) = (term1968 A B C _75296 op _75297 s t _75298).
Proof. exact (eq_refl (term1977 A B C _75296 op _75297 s _75298 t)). Qed.
Lemma lem5965403 {A : Type'} (i : A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5965404 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) (i : A) : (term1978 A B C _75296 op _75297 s _75298 t i) = (term1979 A B C _75296 op _75297 s t _75298 i).
Proof. exact (MK_COMB (@lem5965402 A B C _75296 op _75297 s t _75298) (@lem5965403 A i)). Qed.
Lemma lem5965405 {A B C : Type'} (i : A) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1979 A B C _75296 op _75297 s t _75298 i) = (term1966 A B C i _75296 op _75297 s t _75298).
Proof. exact (eq_refl (term1979 A B C _75296 op _75297 s t _75298 i)). Qed.
Lemma lem5965406 {A B C : Type'} (i : A) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1978 A B C _75296 op _75297 s _75298 t i) = (term1966 A B C i _75296 op _75297 s t _75298).
Proof. exact (TRANS (@lem5965404 A B C _75296 op _75297 s t _75298 i) (@lem5965405 A B C i _75296 op _75297 s t _75298)). Qed.
Lemma lem5965407 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1980 A B C _75296 op _75297 s _75298 t) = (term1968 A B C _75296 op _75297 s t _75298).
Proof. exact (fun_ext (fun i : A => @lem5965406 A B C i _75296 op _75297 s t _75298)). Qed.
Lemma lem5965408 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5965409 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1981 A B C _75296 op _75297 s _75298 t) = (term1969 A B C _75296 op _75297 s t _75298).
Proof. exact (MK_COMB (@lem5965408 A) (@lem5965407 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965410 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1982 A B C _75296 op _75297 s _75298) = (term1970 A B C _75296 op _75297 s _75298).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5965409 A B C _75296 op _75297 s t _75298)). Qed.
Lemma lem5965411 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5965412 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1974 A B C _75296 op _75297 s _75298) = (term1971 A B C _75296 op _75297 s _75298).
Proof. exact (MK_COMB (@lem5965411 A B) (@lem5965410 A B C _75296 op _75297 s _75298)). Qed.
Lemma lem5965413 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5965414 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1983 A B C _75296 op _75297 s _75298) = (term1984 A B C _75296 op _75297 s _75298).
Proof. exact (MK_COMB (@lem5965413) (@lem5965412 A B C _75296 op _75297 s _75298)). Qed.
Lemma lem5965415 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1977 A B C _75296 op _75297 s _75298 t) = (term1968 A B C _75296 op _75297 s t _75298).
Proof. exact (eq_refl (term1977 A B C _75296 op _75297 s _75298 t)). Qed.
Lemma lem5965416 {A B : Type'} (i : type473 A B) (t : type1413 A B) : (i t) = (i t).
Proof. exact (eq_refl (i t)). Qed.
Lemma lem5965417 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) (i : type473 A B) (t : type1413 A B) : (term1985 A B C _75296 op _75297 s _75298 i t) = (term1986 A B C _75296 op _75297 s _75298 i t).
Proof. exact (MK_COMB (@lem5965415 A B C _75296 op _75297 s t _75298) (@lem5965416 A B i t)). Qed.
Lemma lem5965418 {A B C : Type'} (i : type473 A B) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1986 A B C _75296 op _75297 s _75298 i t) = (term1987 A B C i _75296 op _75297 s t _75298).
Proof. exact (eq_refl (term1986 A B C _75296 op _75297 s _75298 i t)). Qed.
Lemma lem5965419 {A B C : Type'} (i : type473 A B) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (t : type1413 A B) (_75298 : type441 A B C) : (term1985 A B C _75296 op _75297 s _75298 i t) = (term1987 A B C i _75296 op _75297 s t _75298).
Proof. exact (TRANS (@lem5965417 A B C _75296 op _75297 s _75298 i t) (@lem5965418 A B C i _75296 op _75297 s t _75298)). Qed.
Lemma lem5965420 {A B C : Type'} (i : type473 A B) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1988 A B C _75296 op _75297 s _75298 i) = (term1989 A B C i _75296 op _75297 s _75298).
Proof. exact (fun_ext (fun t : type1413 A B => @lem5965419 A B C i _75296 op _75297 s t _75298)). Qed.
Lemma lem5965421 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem5965422 {A B C : Type'} (i : type473 A B) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1990 A B C _75296 op _75297 s _75298 i) = (term1991 A B C i _75296 op _75297 s _75298).
Proof. exact (MK_COMB (@lem5965421 A B) (@lem5965420 A B C i _75296 op _75297 s _75298)). Qed.
Lemma lem5965423 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1992 A B C _75296 op _75297 s _75298) = (term1993 A B C _75296 op _75297 s _75298).
Proof. exact (fun_ext (fun i : type473 A B => @lem5965422 A B C i _75296 op _75297 s _75298)). Qed.
Lemma lem5965424 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem5965425 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1975 A B C _75296 op _75297 s _75298) = (term1994 A B C _75296 op _75297 s _75298).
Proof. exact (MK_COMB (@lem5965424 A B) (@lem5965423 A B C _75296 op _75297 s _75298)). Qed.
Lemma lem5965426 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : ((term1974 A B C _75296 op _75297 s _75298) = (term1975 A B C _75296 op _75297 s _75298)) = ((term1971 A B C _75296 op _75297 s _75298) = (term1994 A B C _75296 op _75297 s _75298)).
Proof. exact (MK_COMB (@lem5965414 A B C _75296 op _75297 s _75298) (@lem5965425 A B C _75296 op _75297 s _75298)). Qed.
Lemma lem5965427 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1971 A B C _75296 op _75297 s _75298) = (term1994 A B C _75296 op _75297 s _75298).
Proof. exact (EQ_MP (@lem5965426 A B C _75296 op _75297 s _75298) (@lem5965401 A B C _75296 op _75297 s _75298)). Qed.
Lemma lem5965429 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1954 A B C _75296 op _75297 s _75298) = (term1994 A B C _75296 op _75297 s _75298).
Proof. exact (TRANS (@lem5965397 A B C _75296 op _75297 s _75298) (@lem5965427 A B C _75296 op _75297 s _75298)). Qed.
Lemma lem5965430 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) : (term1315 A B C _75296 op _75297 s _75298) = (term1994 A B C _75296 op _75297 s _75298).
Proof. exact (TRANS (@lem5965269 A B C _75296 op _75297 s _75298) (@lem5965429 A B C _75296 op _75297 s _75298)). Qed.
Lemma lem5965431 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) (h1 : term1315 A B C _75296 op _75297 s _75298) : term1994 A B C _75296 op _75297 s _75298.
Proof. exact (EQ_MP (@lem5965430 A B C _75296 op _75297 s _75298) (@lem5963810 A B C _75296 op _75297 s _75298 h1)). Qed.
Lemma lem5965437 {A : Type'} (x : A) (s : A -> Prop) (h1 : term782 A x s) : term782 A x s.
Proof. exact (h1). Qed.
Lemma lem5965521 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term1016 A B p1 p2 x t x') = (term1016 A B p1 p2 x t x').
Proof. exact (eq_refl (term1016 A B p1 p2 x t x')). Qed.
Lemma lem5965522 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1018 A B p1 p2 t x) = (term1018 A B p1 p2 t x).
Proof. exact (fun_ext (fun x' : B => @lem5965521 A B p1 p2 x' t x)). Qed.
Lemma lem5965523 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5965524 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1019 A B p1 p2 t x) = (term1019 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5965523 B) (@lem5965522 A B p1 p2 t x)). Qed.
Lemma lem5965537 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term1059 A B s t p1 i p2 j) = (term1059 A B s t p1 i p2 j).
Proof. exact (eq_refl (term1059 A B s t p1 i p2 j)). Qed.
Lemma lem5965538 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term1061 A B s t p1 i p2) = (term1061 A B s t p1 i p2).
Proof. exact (fun_ext (fun j : B => @lem5965537 A B s t p1 i p2 j)). Qed.
Lemma lem5965539 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5965540 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term1063 A B s t p1 i p2) = (term1063 A B s t p1 i p2).
Proof. exact (MK_COMB (@lem5965539 B) (@lem5965538 A B s t p1 i p2)). Qed.
Lemma lem5965541 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1065 A B s t p1 p2) = (term1065 A B s t p1 p2).
Proof. exact (fun_ext (fun i : A => @lem5965540 A B s t p1 i p2)). Qed.
Lemma lem5965542 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5965543 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1066 A B s t p1 p2) = (term1066 A B s t p1 p2).
Proof. exact (MK_COMB (@lem5965542 A) (@lem5965541 A B s t p1 p2)). Qed.
Lemma lem5965544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5965545 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1021 A B p1 p2 t x) = (term1021 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5965544) (@lem5965524 A B p1 p2 t x)). Qed.
Lemma lem5965546 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1067 A B x s t p1 p2) = (term1067 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5965545 A B p1 p2 t x) (@lem5965543 A B s t p1 p2)). Qed.
Lemma lem5965649 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5965650 {B : Type'} (P : B -> Prop) (Q : Prop) : (term285 B P Q) = (term286 B P Q).
Proof. exact (@lem5965649 B P Q). Qed.
Lemma lem5965651 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1995 A B x s t p1 p2) = (term1996 A B x s t p1 p2).
Proof. exact (@lem5965650 B (term1018 A B p1 p2 t x) (term1066 A B s t p1 p2)). Qed.
Lemma lem5965652 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term1997 A B p1 p2 t x' x) = (term1016 A B p1 p2 x t x').
Proof. exact (eq_refl (term1997 A B p1 p2 t x' x)). Qed.
Lemma lem5965653 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1998 A B p1 p2 t x) = (term1018 A B p1 p2 t x).
Proof. exact (fun_ext (fun x' : B => @lem5965652 A B p1 p2 x' t x)). Qed.
Lemma lem5965654 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5965655 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term1999 A B p1 p2 t x) = (term1019 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5965654 B) (@lem5965653 A B p1 p2 t x)). Qed.
Lemma lem5965656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5965657 {A B : Type'} (p1 : A) (p2 : B) (t : type1413 A B) (x : A) : (term2000 A B p1 p2 t x) = (term1021 A B p1 p2 t x).
Proof. exact (MK_COMB (@lem5965656) (@lem5965655 A B p1 p2 t x)). Qed.
Lemma lem5965658 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1066 A B s t p1 p2) = (term1066 A B s t p1 p2).
Proof. exact (eq_refl (term1066 A B s t p1 p2)). Qed.
Lemma lem5965659 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1995 A B x s t p1 p2) = (term1067 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5965657 A B p1 p2 t x) (@lem5965658 A B s t p1 p2)). Qed.
Lemma lem5965660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5965661 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2001 A B x s t p1 p2) = (term1069 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5965660) (@lem5965659 A B x s t p1 p2)). Qed.
Lemma lem5965662 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term1997 A B p1 p2 t x' x) = (term1016 A B p1 p2 x t x').
Proof. exact (eq_refl (term1997 A B p1 p2 t x' x)). Qed.
Lemma lem5965663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5965664 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term2002 A B p1 p2 t x' x) = (term2003 A B p1 p2 x t x').
Proof. exact (MK_COMB (@lem5965663) (@lem5965662 A B p1 p2 x t x')). Qed.
Lemma lem5965665 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1066 A B s t p1 p2) = (term1066 A B s t p1 p2).
Proof. exact (eq_refl (term1066 A B s t p1 p2)). Qed.
Lemma lem5965666 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2004 A B x' x s t p1 p2) = (term2005 A B x x' s t p1 p2).
Proof. exact (MK_COMB (@lem5965664 A B p1 p2 x t x') (@lem5965665 A B s t p1 p2)). Qed.
Lemma lem5965667 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2006 A B x s t p1 p2) = (term2007 A B x s t p1 p2).
Proof. exact (fun_ext (fun x' : B => @lem5965666 A B x' x s t p1 p2)). Qed.
Lemma lem5965668 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5965669 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1996 A B x s t p1 p2) = (term2008 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5965668 B) (@lem5965667 A B x s t p1 p2)). Qed.
Lemma lem5965670 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : ((term1995 A B x s t p1 p2) = (term1996 A B x s t p1 p2)) = ((term1067 A B x s t p1 p2) = (term2008 A B x s t p1 p2)).
Proof. exact (MK_COMB (@lem5965661 A B x s t p1 p2) (@lem5965669 A B x s t p1 p2)). Qed.
Lemma lem5965671 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1067 A B x s t p1 p2) = (term2008 A B x s t p1 p2).
Proof. exact (EQ_MP (@lem5965670 A B x s t p1 p2) (@lem5965651 A B x s t p1 p2)). Qed.
Lemma lem5965673 {A : Type'} (P : Prop) (Q : A -> Prop) : (term363 A P Q) = (term364 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5965674 {A : Type'} (P : Prop) (Q : A -> Prop) : (term363 A P Q) = (term364 A P Q).
Proof. exact (@lem5965673 A P Q). Qed.
Lemma lem5965675 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2009 A B x x' s t p1 p2) = (term2010 A B x x' s t p1 p2).
Proof. exact (@lem5965674 A (term1016 A B p1 p2 x t x') (term1065 A B s t p1 p2)). Qed.
Lemma lem5965676 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term2011 A B s t p1 p2 i) = (term1063 A B s t p1 i p2).
Proof. exact (eq_refl (term2011 A B s t p1 p2 i)). Qed.
Lemma lem5965677 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2012 A B s t p1 p2) = (term1065 A B s t p1 p2).
Proof. exact (fun_ext (fun i : A => @lem5965676 A B s t p1 i p2)). Qed.
Lemma lem5965678 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5965679 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2013 A B s t p1 p2) = (term1066 A B s t p1 p2).
Proof. exact (MK_COMB (@lem5965678 A) (@lem5965677 A B s t p1 p2)). Qed.
Lemma lem5965680 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term2003 A B p1 p2 x t x') = (term2003 A B p1 p2 x t x').
Proof. exact (eq_refl (term2003 A B p1 p2 x t x')). Qed.
Lemma lem5965681 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2009 A B x x' s t p1 p2) = (term2005 A B x x' s t p1 p2).
Proof. exact (MK_COMB (@lem5965680 A B p1 p2 x t x') (@lem5965679 A B s t p1 p2)). Qed.
Lemma lem5965682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5965683 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2014 A B x x' s t p1 p2) = (term2015 A B x x' s t p1 p2).
Proof. exact (MK_COMB (@lem5965682) (@lem5965681 A B x x' s t p1 p2)). Qed.
Lemma lem5965684 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term2011 A B s t p1 p2 i) = (term1063 A B s t p1 i p2).
Proof. exact (eq_refl (term2011 A B s t p1 p2 i)). Qed.
Lemma lem5965685 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term2003 A B p1 p2 x t x') = (term2003 A B p1 p2 x t x').
Proof. exact (eq_refl (term2003 A B p1 p2 x t x')). Qed.
Lemma lem5965686 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term2016 A B x x' s t p1 p2 i) = (term2017 A B x x' s t p1 i p2).
Proof. exact (MK_COMB (@lem5965685 A B p1 p2 x t x') (@lem5965684 A B s t p1 i p2)). Qed.
Lemma lem5965687 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2018 A B x x' s t p1 p2) = (term2019 A B x x' s t p1 p2).
Proof. exact (fun_ext (fun i : A => @lem5965686 A B x x' s t p1 i p2)). Qed.
Lemma lem5965688 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5965689 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2010 A B x x' s t p1 p2) = (term2020 A B x x' s t p1 p2).
Proof. exact (MK_COMB (@lem5965688 A) (@lem5965687 A B x x' s t p1 p2)). Qed.
Lemma lem5965690 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : ((term2009 A B x x' s t p1 p2) = (term2010 A B x x' s t p1 p2)) = ((term2005 A B x x' s t p1 p2) = (term2020 A B x x' s t p1 p2)).
Proof. exact (MK_COMB (@lem5965683 A B x x' s t p1 p2) (@lem5965689 A B x x' s t p1 p2)). Qed.
Lemma lem5965691 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2005 A B x x' s t p1 p2) = (term2020 A B x x' s t p1 p2).
Proof. exact (EQ_MP (@lem5965690 A B x x' s t p1 p2) (@lem5965675 A B x x' s t p1 p2)). Qed.
Lemma lem5965693 {A : Type'} (P : Prop) (Q : A -> Prop) : (term363 A P Q) = (term364 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5965694 {B : Type'} (P : Prop) (Q : B -> Prop) : (term363 B P Q) = (term364 B P Q).
Proof. exact (@lem5965693 B P Q). Qed.
Lemma lem5965695 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term2021 A B x x' s t p1 i p2) = (term2022 A B x x' s t p1 i p2).
Proof. exact (@lem5965694 B (term1016 A B p1 p2 x t x') (term1061 A B s t p1 i p2)). Qed.
Lemma lem5965696 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term2023 A B s t p1 i p2 j) = (term1059 A B s t p1 i p2 j).
Proof. exact (eq_refl (term2023 A B s t p1 i p2 j)). Qed.
Lemma lem5965697 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term2024 A B s t p1 i p2) = (term1061 A B s t p1 i p2).
Proof. exact (fun_ext (fun j : B => @lem5965696 A B s t p1 i p2 j)). Qed.
Lemma lem5965698 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5965699 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term2025 A B s t p1 i p2) = (term1063 A B s t p1 i p2).
Proof. exact (MK_COMB (@lem5965698 B) (@lem5965697 A B s t p1 i p2)). Qed.
Lemma lem5965700 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term2003 A B p1 p2 x t x') = (term2003 A B p1 p2 x t x').
Proof. exact (eq_refl (term2003 A B p1 p2 x t x')). Qed.
Lemma lem5965701 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term2021 A B x x' s t p1 i p2) = (term2017 A B x x' s t p1 i p2).
Proof. exact (MK_COMB (@lem5965700 A B p1 p2 x t x') (@lem5965699 A B s t p1 i p2)). Qed.
Lemma lem5965702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5965703 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term2026 A B x x' s t p1 i p2) = (term2027 A B x x' s t p1 i p2).
Proof. exact (MK_COMB (@lem5965702) (@lem5965701 A B x x' s t p1 i p2)). Qed.
Lemma lem5965704 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term2023 A B s t p1 i p2 j) = (term1059 A B s t p1 i p2 j).
Proof. exact (eq_refl (term2023 A B s t p1 i p2 j)). Qed.
Lemma lem5965705 {A B : Type'} (p1 : A) (p2 : B) (x : B) (t : type1413 A B) (x' : A) : (term2003 A B p1 p2 x t x') = (term2003 A B p1 p2 x t x').
Proof. exact (eq_refl (term2003 A B p1 p2 x t x')). Qed.
Lemma lem5965706 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term2028 A B x x' s t p1 i p2 j) = (term2029 A B x x' s t p1 i p2 j).
Proof. exact (MK_COMB (@lem5965705 A B p1 p2 x t x') (@lem5965704 A B s t p1 i p2 j)). Qed.
Lemma lem5965707 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term2030 A B x x' s t p1 i p2) = (term2031 A B x x' s t p1 i p2).
Proof. exact (fun_ext (fun j : B => @lem5965706 A B x x' s t p1 i p2 j)). Qed.
Lemma lem5965708 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5965709 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term2022 A B x x' s t p1 i p2) = (term2032 A B x x' s t p1 i p2).
Proof. exact (MK_COMB (@lem5965708 B) (@lem5965707 A B x x' s t p1 i p2)). Qed.
Lemma lem5965710 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : ((term2021 A B x x' s t p1 i p2) = (term2022 A B x x' s t p1 i p2)) = ((term2017 A B x x' s t p1 i p2) = (term2032 A B x x' s t p1 i p2)).
Proof. exact (MK_COMB (@lem5965703 A B x x' s t p1 i p2) (@lem5965709 A B x x' s t p1 i p2)). Qed.
Lemma lem5965711 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) : (term2017 A B x x' s t p1 i p2) = (term2032 A B x x' s t p1 i p2).
Proof. exact (EQ_MP (@lem5965710 A B x x' s t p1 i p2) (@lem5965695 A B x x' s t p1 i p2)). Qed.
Lemma lem5965712 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2019 A B x x' s t p1 p2) = (term2033 A B x x' s t p1 p2).
Proof. exact (fun_ext (fun i : A => @lem5965711 A B x x' s t p1 i p2)). Qed.
Lemma lem5965713 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5965714 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2020 A B x x' s t p1 p2) = (term2034 A B x x' s t p1 p2).
Proof. exact (MK_COMB (@lem5965713 A) (@lem5965712 A B x x' s t p1 p2)). Qed.
Lemma lem5965715 {A B : Type'} (x : B) (x' : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2005 A B x x' s t p1 p2) = (term2034 A B x x' s t p1 p2).
Proof. exact (TRANS (@lem5965691 A B x x' s t p1 p2) (@lem5965714 A B x x' s t p1 p2)). Qed.
Lemma lem5965716 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2007 A B x s t p1 p2) = (term2035 A B x s t p1 p2).
Proof. exact (fun_ext (fun x' : B => @lem5965715 A B x' x s t p1 p2)). Qed.
Lemma lem5965717 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5965718 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2008 A B x s t p1 p2) = (term2036 A B x s t p1 p2).
Proof. exact (MK_COMB (@lem5965717 B) (@lem5965716 A B x s t p1 p2)). Qed.
Lemma lem5965720 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1067 A B x s t p1 p2) = (term2036 A B x s t p1 p2).
Proof. exact (TRANS (@lem5965671 A B x s t p1 p2) (@lem5965718 A B x s t p1 p2)). Qed.
Lemma lem5965721 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term1067 A B x s t p1 p2) = (term2036 A B x s t p1 p2).
Proof. exact (TRANS (@lem5965546 A B x s t p1 p2) (@lem5965720 A B x s t p1 p2)). Qed.
Lemma lem5965722 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (h1 : term1067 A B x s t p1 p2) : term2036 A B x s t p1 p2.
Proof. exact (EQ_MP (@lem5965721 A B x s t p1 p2) (@lem5963814 A B x s t p1 p2 h1)). Qed.
Lemma lem5965723 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (h1 : term2034 A B x' x s t p1 p2) : term2034 A B x' x s t p1 p2.
Proof. exact (h1). Qed.
Lemma lem5965724 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (h1 : term2032 A B x' x s t p1 i p2) : term2032 A B x' x s t p1 i p2.
Proof. exact (h1). Qed.
Lemma lem5965725 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : term2029 A B x' x s t p1 i p2 j.
Proof. exact (h1). Qed.
Lemma lem5965727 {A B : Type'} (_75297 : type621 A B) (i'' : type619 A B) (h1 : term1937 A B _75297 i'') : term1937 A B _75297 i''.
Proof. exact (h1). Qed.
Lemma lem5965729 {A B C : Type'} (i''' : type439 A B C) (_75298 : type441 A B C) (h1 : term1625 A B C i''' _75298) : term1625 A B C i''' _75298.
Proof. exact (h1). Qed.
Lemma lem5965831 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5965838 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5965839 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5965838 A (type686 A) f x). Qed.
Lemma lem5965840 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem5965839 A (@IN A) x). Qed.
Lemma lem5965841 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5965842 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem5965840 A x) (@lem5965841 A s)). Qed.
Lemma lem5965844 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5965845 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5965844 (A -> Prop) Prop f x). Qed.
Lemma lem5965846 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term2037 A x s).
Proof. exact (@lem5965845 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem5965848 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term2037 A x s).
Proof. exact (TRANS (@lem5965842 A x s) (@lem5965846 A x s)). Qed.
Lemma lem5965849 {A : Type'} (x : A) (s : A -> Prop) : (term782 A x s) = (term2038 A x s).
Proof. exact (MK_COMB (@lem5965831) (@lem5965848 A x s)). Qed.
Lemma lem5965923 {A B : Type'} (p1 : A) (i : A) (p2 : B) (j : B) : (term13 A B p1 i p2 j) = (term13 A B p1 i p2 j).
Proof. exact (eq_refl (term13 A B p1 i p2 j)). Qed.
Lemma lem5965930 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5965931 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem5965930 A (B -> Prop) f x). Qed.
Lemma lem5965933 {A B : Type'} (t : type1413 A B) (i : A) : (t i) = (@I (A -> B -> Prop) t i).
Proof. exact (@lem5965931 A B t i). Qed.
Lemma lem5965934 {B : Type'} (j : B) : (@IN B j) = (@IN B j).
Proof. exact (eq_refl (@IN B j)). Qed.
Lemma lem5965935 {A B : Type'} (j : B) (t : type1413 A B) (i : A) : (term740 A B j t i) = (term2039 A B j t i).
Proof. exact (MK_COMB (@lem5965934 B j) (@lem5965933 A B t i)). Qed.
Lemma lem5965937 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5965938 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5965937 B (type686 B) f x). Qed.
Lemma lem5965939 {B : Type'} (j : B) : (@IN B j) = (@I (B -> (B -> Prop) -> Prop) (@IN B) j).
Proof. exact (@lem5965938 B (@IN B) j). Qed.
Lemma lem5965940 {A B : Type'} (t : type1413 A B) (i : A) : (@I (A -> B -> Prop) t i) = (@I (A -> B -> Prop) t i).
Proof. exact (eq_refl (@I (A -> B -> Prop) t i)). Qed.
Lemma lem5965941 {A B : Type'} (j : B) (t : type1413 A B) (i : A) : (term2039 A B j t i) = (term2040 A B j t i).
Proof. exact (MK_COMB (@lem5965939 B j) (@lem5965940 A B t i)). Qed.
Lemma lem5965943 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5965944 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5965943 (B -> Prop) Prop f x). Qed.
Lemma lem5965945 {A B : Type'} (j : B) (t : type1413 A B) (i : A) : (term2040 A B j t i) = (term2041 A B j t i).
Proof. exact (@lem5965944 B (@I (B -> (B -> Prop) -> Prop) (@IN B) j) (@I (A -> B -> Prop) t i)). Qed.
Lemma lem5965946 {A B : Type'} (j : B) (t : type1413 A B) (i : A) : (term2039 A B j t i) = (term2041 A B j t i).
Proof. exact (TRANS (@lem5965941 A B j t i) (@lem5965945 A B j t i)). Qed.
Lemma lem5965947 {A B : Type'} (j : B) (t : type1413 A B) (i : A) : (term740 A B j t i) = (term2041 A B j t i).
Proof. exact (TRANS (@lem5965935 A B j t i) (@lem5965946 A B j t i)). Qed.
Lemma lem5965954 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5965955 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5965954 A (type686 A) f x). Qed.
Lemma lem5965956 {A : Type'} (i : A) : (@IN A i) = (@I (A -> (A -> Prop) -> Prop) (@IN A) i).
Proof. exact (@lem5965955 A (@IN A) i). Qed.
Lemma lem5965957 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5965958 {A : Type'} (i : A) (s : A -> Prop) : (@IN A i s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) i s).
Proof. exact (MK_COMB (@lem5965956 A i) (@lem5965957 A s)). Qed.
Lemma lem5965960 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5965961 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5965960 (A -> Prop) Prop f x). Qed.
Lemma lem5965962 {A : Type'} (i : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) i s) = (term2037 A i s).
Proof. exact (@lem5965961 A (@I (A -> (A -> Prop) -> Prop) (@IN A) i) s). Qed.
Lemma lem5965964 {A : Type'} (i : A) (s : A -> Prop) : (@IN A i s) = (term2037 A i s).
Proof. exact (TRANS (@lem5965958 A i s) (@lem5965962 A i s)). Qed.
Lemma lem5965965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5965966 {A : Type'} (i : A) (s : A -> Prop) : (term160 A i s) = (term2042 A i s).
Proof. exact (MK_COMB (@lem5965965) (@lem5965964 A i s)). Qed.
Lemma lem5965967 {A B : Type'} (s : A -> Prop) (j : B) (t : type1413 A B) (i : A) : (term1041 A B s j t i) = (term2043 A B s j t i).
Proof. exact (MK_COMB (@lem5965966 A i s) (@lem5965947 A B j t i)). Qed.
Lemma lem5965968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5965969 {A B : Type'} (s : A -> Prop) (j : B) (t : type1413 A B) (i : A) : (term1058 A B s j t i) = (term2044 A B s j t i).
Proof. exact (MK_COMB (@lem5965968) (@lem5965967 A B s j t i)). Qed.
Lemma lem5965970 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term1059 A B s t p1 i p2 j) = (term2045 A B s t p1 i p2 j).
Proof. exact (MK_COMB (@lem5965969 A B s j t i) (@lem5965923 A B p1 i p2 j)). Qed.
Lemma lem5965977 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5965978 {A B : Type'} (f : type1413 A B) (x : A) : (f x) = (@I (A -> B -> Prop) f x).
Proof. exact (@lem5965977 A (B -> Prop) f x). Qed.
Lemma lem5965980 {A B : Type'} (t : type1413 A B) (x : A) : (t x) = (@I (A -> B -> Prop) t x).
Proof. exact (@lem5965978 A B t x). Qed.
Lemma lem5965981 {B : Type'} (x' : B) : (@IN B x') = (@IN B x').
Proof. exact (eq_refl (@IN B x')). Qed.
Lemma lem5965982 {A B : Type'} (x' : B) (t : type1413 A B) (x : A) : (term740 A B x' t x) = (term2039 A B x' t x).
Proof. exact (MK_COMB (@lem5965981 B x') (@lem5965980 A B t x)). Qed.
Lemma lem5965984 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5965985 {B : Type'} (f : type1364 B) (x : B) : (f x) = (@I (B -> (B -> Prop) -> Prop) f x).
Proof. exact (@lem5965984 B (type686 B) f x). Qed.
Lemma lem5965986 {B : Type'} (x' : B) : (@IN B x') = (@I (B -> (B -> Prop) -> Prop) (@IN B) x').
Proof. exact (@lem5965985 B (@IN B) x'). Qed.
Lemma lem5965987 {A B : Type'} (t : type1413 A B) (x : A) : (@I (A -> B -> Prop) t x) = (@I (A -> B -> Prop) t x).
Proof. exact (eq_refl (@I (A -> B -> Prop) t x)). Qed.
Lemma lem5965988 {A B : Type'} (x' : B) (t : type1413 A B) (x : A) : (term2039 A B x' t x) = (term2040 A B x' t x).
Proof. exact (MK_COMB (@lem5965986 B x') (@lem5965987 A B t x)). Qed.
Lemma lem5965990 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5965991 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem5965990 (B -> Prop) Prop f x). Qed.
Lemma lem5965992 {A B : Type'} (x' : B) (t : type1413 A B) (x : A) : (term2040 A B x' t x) = (term2041 A B x' t x).
Proof. exact (@lem5965991 B (@I (B -> (B -> Prop) -> Prop) (@IN B) x') (@I (A -> B -> Prop) t x)). Qed.
Lemma lem5965993 {A B : Type'} (x' : B) (t : type1413 A B) (x : A) : (term2039 A B x' t x) = (term2041 A B x' t x).
Proof. exact (TRANS (@lem5965988 A B x' t x) (@lem5965992 A B x' t x)). Qed.
Lemma lem5965994 {A B : Type'} (x' : B) (t : type1413 A B) (x : A) : (term740 A B x' t x) = (term2041 A B x' t x).
Proof. exact (TRANS (@lem5965982 A B x' t x) (@lem5965993 A B x' t x)). Qed.
Lemma lem5966009 {A B : Type'} (p1 : A) (x : A) (p2 : B) (x' : B) : (term1014 A B p1 x p2 x') = (term1014 A B p1 x p2 x').
Proof. exact (eq_refl (term1014 A B p1 x p2 x')). Qed.
Lemma lem5966010 {A B : Type'} (p1 : A) (p2 : B) (x' : B) (t : type1413 A B) (x : A) : (term1016 A B p1 p2 x' t x) = (term2046 A B p1 p2 x' t x).
Proof. exact (MK_COMB (@lem5966009 A B p1 x p2 x') (@lem5965994 A B x' t x)). Qed.
Lemma lem5966011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5966012 {A B : Type'} (p1 : A) (p2 : B) (x' : B) (t : type1413 A B) (x : A) : (term2003 A B p1 p2 x' t x) = (term2047 A B p1 p2 x' t x).
Proof. exact (MK_COMB (@lem5966011) (@lem5966010 A B p1 p2 x' t x)). Qed.
Lemma lem5966013 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) : (term2029 A B x' x s t p1 i p2 j) = (term2048 A B x' x s t p1 i p2 j).
Proof. exact (MK_COMB (@lem5966012 A B p1 p2 x' t x) (@lem5965970 A B s t p1 i p2 j)). Qed.
Lemma lem5966014 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : term2048 A B x' x s t p1 i p2 j.
Proof. exact (EQ_MP (@lem5966013 A B x' x s t p1 i p2 j) (@lem5965725 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5966824 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : term2045 A B s t p1 i p2 j.
Proof. exact (proj2 (@lem5966014 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5966825 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : term2046 A B p1 p2 x' t x.
Proof. exact (proj1 (@lem5966014 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5966826 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : term13 A B p1 i p2 j.
Proof. exact (proj2 (@lem5966824 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5966827 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : term2043 A B s j t i.
Proof. exact (proj1 (@lem5966824 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5966833 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : term13 A B p1 x p2 x'.
Proof. exact (proj1 (@lem5966825 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5967422 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : p1 = i.
Proof. exact (proj1 (@lem5966826 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5967491 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : p1 = x.
Proof. exact (proj1 (@lem5966833 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5967674 {A : Type'} (i : A) : (term2049 A i) = (term2049 A i).
Proof. exact (eq_refl (term2049 A i)). Qed.
Lemma lem5967675 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : (term2050 A i p1) = (term2050 A i x).
Proof. exact (MK_COMB (@lem5967674 A i) (@lem5967491 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5967676 {A : Type'} (x : A) (i : A) : (term2050 A i x) = (x = i).
Proof. exact (eq_refl (term2050 A i x)). Qed.
Lemma lem5967677 {A : Type'} (i : A) (p1 : A) : (term2051 A i p1) = (term2051 A i p1).
Proof. exact (eq_refl (term2051 A i p1)). Qed.
Lemma lem5967678 {A : Type'} (p1 : A) (x : A) (i : A) : ((term2050 A i p1) = (term2050 A i x)) = ((term2050 A i p1) = (x = i)).
Proof. exact (MK_COMB (@lem5967677 A i p1) (@lem5967676 A x i)). Qed.
Lemma lem5967679 {A : Type'} (p1 : A) (i : A) : (term2050 A i p1) = (p1 = i).
Proof. exact (eq_refl (term2050 A i p1)). Qed.
Lemma lem5967680 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5967681 {A : Type'} (p1 : A) (i : A) : (term2051 A i p1) = (term2052 A p1 i).
Proof. exact (MK_COMB (@lem5967680) (@lem5967679 A p1 i)). Qed.
Lemma lem5967682 {A : Type'} (x : A) (i : A) : (x = i) = (x = i).
Proof. exact (eq_refl (x = i)). Qed.
Lemma lem5967683 {A : Type'} (p1 : A) (x : A) (i : A) : ((term2050 A i p1) = (x = i)) = ((p1 = i) = (x = i)).
Proof. exact (MK_COMB (@lem5967681 A p1 i) (@lem5967682 A x i)). Qed.
Lemma lem5967684 {A : Type'} (p1 : A) (x : A) (i : A) : ((term2050 A i p1) = (term2050 A i x)) = ((p1 = i) = (x = i)).
Proof. exact (TRANS (@lem5967678 A p1 x i) (@lem5967683 A p1 x i)). Qed.
Lemma lem5967685 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : (p1 = i) = (x = i).
Proof. exact (EQ_MP (@lem5967684 A p1 x i) (@lem5967675 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5967854 {A : Type'} (x : A) (s : A -> Prop) (h1 : term782 A x s) : term2038 A x s.
Proof. exact (EQ_MP (@lem5965849 A x s) (@lem5965437 A x s h1)). Qed.
Lemma lem5967938 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : x = i.
Proof. exact (EQ_MP (@lem5967685 A B x' x s t p1 i p2 j h1) (@lem5967422 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5968078 {A : Type'} (s : A -> Prop) : (term2053 A s) = (term2053 A s).
Proof. exact (eq_refl (term2053 A s)). Qed.
Lemma lem5968079 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : (term2054 A s x) = (term2054 A s i).
Proof. exact (MK_COMB (@lem5968078 A s) (@lem5967938 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5968080 {A : Type'} (i : A) (s : A -> Prop) : (term2054 A s i) = (term2038 A i s).
Proof. exact (eq_refl (term2054 A s i)). Qed.
Lemma lem5968081 {A : Type'} (s : A -> Prop) (x : A) : (term2055 A s x) = (term2055 A s x).
Proof. exact (eq_refl (term2055 A s x)). Qed.
Lemma lem5968082 {A : Type'} (x : A) (i : A) (s : A -> Prop) : ((term2054 A s x) = (term2054 A s i)) = ((term2054 A s x) = (term2038 A i s)).
Proof. exact (MK_COMB (@lem5968081 A s x) (@lem5968080 A i s)). Qed.
Lemma lem5968083 {A : Type'} (x : A) (s : A -> Prop) : (term2054 A s x) = (term2038 A x s).
Proof. exact (eq_refl (term2054 A s x)). Qed.
Lemma lem5968084 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5968085 {A : Type'} (x : A) (s : A -> Prop) : (term2055 A s x) = (term2056 A x s).
Proof. exact (MK_COMB (@lem5968084) (@lem5968083 A x s)). Qed.
Lemma lem5968086 {A : Type'} (i : A) (s : A -> Prop) : (term2038 A i s) = (term2038 A i s).
Proof. exact (eq_refl (term2038 A i s)). Qed.
Lemma lem5968087 {A : Type'} (x : A) (i : A) (s : A -> Prop) : ((term2054 A s x) = (term2038 A i s)) = ((term2038 A x s) = (term2038 A i s)).
Proof. exact (MK_COMB (@lem5968085 A x s) (@lem5968086 A i s)). Qed.
Lemma lem5968088 {A : Type'} (x : A) (i : A) (s : A -> Prop) : ((term2054 A s x) = (term2054 A s i)) = ((term2038 A x s) = (term2038 A i s)).
Proof. exact (TRANS (@lem5968082 A x i s) (@lem5968087 A x i s)). Qed.
Lemma lem5968089 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : (term2038 A x s) = (term2038 A i s).
Proof. exact (EQ_MP (@lem5968088 A x i s) (@lem5968079 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5968090 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term782 A x s) (h2 : term2029 A B x' x s t p1 i p2 j) : term2038 A i s.
Proof. exact (EQ_MP (@lem5968089 A B x' x s t p1 i p2 j h2) (@lem5967854 A x s h1)). Qed.
Lemma lem5969123 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : term2037 A i s.
Proof. exact (proj1 (@lem5966827 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5969124 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : term2057 A i s.
Proof. exact (fun h0 : term2038 A i s => @lem5969123 A B x' x s t p1 i p2 j h1). Qed.
Lemma lem5969126 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5969127 {A : Type'} (i : A) (s : A -> Prop) : (term2057 A i s) = (term2037 A i s).
Proof. exact (@lem5969126 (term2037 A i s)). Qed.
Lemma lem5969128 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term2029 A B x' x s t p1 i p2 j) : term2037 A i s.
Proof. exact (EQ_MP (@lem5969127 A i s) (@lem5969124 A B x' x s t p1 i p2 j h1)). Qed.
Lemma lem5969131 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5969133 {A : Type'} (i : A) (s : A -> Prop) : (term2038 A i s) = (term2058 A i s).
Proof. exact (@lem5969131 (term2037 A i s)). Qed.
Lemma lem5969136 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term782 A x s) (h2 : term2029 A B x' x s t p1 i p2 j) : term2058 A i s.
Proof. exact (EQ_MP (@lem5969133 A i s) (@lem5968090 A B x' x s t p1 i p2 j h1 h2)). Qed.
Lemma lem5969139 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term782 A x s) (h2 : term2029 A B x' x s t p1 i p2 j) : False.
Proof. exact (@lem5969136 A B x' x s t p1 i p2 j h1 h2 (@lem5969128 A B x' x s t p1 i p2 j h2)). Qed.
Lemma lem5969140 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term782 A x s) (h2 : term2029 A B x' x s t p1 i p2 j) : term530.
Proof. exact (fun h0 : ~ False => @lem5969139 A B x' x s t p1 i p2 j h1 h2). Qed.
Lemma lem5969142 (p : Prop) : (term521 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5969143 : term530 = False.
Proof. exact (@lem5969142 False). Qed.
Lemma lem5969148 {A B : Type'} (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term782 A x s) (h2 : term2029 A B x' x s t p1 i p2 j) : False.
Proof. exact (EQ_MP (@lem5969143) (@lem5969140 A B x' x s t p1 i p2 j h1 h2)). Qed.
Lemma lem5969149 {A B C : Type'} (i''' : type439 A B C) (_75298 : type441 A B C) (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term1625 A B C i''' _75298) (h2 : term782 A x s) (h3 : term2029 A B x' x s t p1 i p2 j) : False.
Proof. exact (ex_elim (@lem5965729 A B C i''' _75298 h1) (fun j'' : type440 A B C => fun h0 : term1624 A B C i''' _75298 j'' => @lem5969148 A B x' x s t p1 i p2 j h2 h3)). Qed.
Lemma lem5969150 {A B C : Type'} (_75298 : type441 A B C) (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term1375 A B C _75298) (h2 : term782 A x s) (h3 : term2029 A B x' x s t p1 i p2 j) : False.
Proof. exact (ex_elim (@lem5964395 A B C _75298 h1) (fun i''' : type439 A B C => fun h0 : term1626 A B C _75298 i''' => @lem5969149 A B C i''' _75298 x' x s t p1 i p2 j h0 h2 h3)). Qed.
Lemma lem5969151 {A B C : Type'} (_75298 : type441 A B C) (_75297 : type621 A B) (i'' : type619 A B) (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term1375 A B C _75298) (h2 : term1937 A B _75297 i'') (h3 : term782 A x s) (h4 : term2029 A B x' x s t p1 i p2 j) : False.
Proof. exact (ex_elim (@lem5965727 A B _75297 i'' h2) (fun j' : type620 A B => fun h0 : term1936 A B _75297 i'' j' => @lem5969150 A B C _75298 x' x s t p1 i p2 j h1 h3 h4)). Qed.
Lemma lem5969152 {A B C : Type'} (_75297 : type621 A B) (_75298 : type441 A B C) (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term782 A x s) (h4 : term2029 A B x' x s t p1 i p2 j) : False.
Proof. exact (ex_elim (@lem5965200 A B _75297 h1) (fun i'' : type619 A B => fun h0 : term1938 A B _75297 i'' => @lem5969151 A B C _75298 _75297 i'' x' x s t p1 i p2 j h2 h0 h3 h4)). Qed.
Lemma lem5969153 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x' : B) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (j : B) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) (h4 : term782 A x s) (h5 : term2029 A B x' x s t p1 i p2 j) : False.
Proof. exact (ex_elim (@lem5965431 A B C _75296 op _75297 s _75298 h3) (fun i' : type473 A B => fun h0 : term1993 A B C _75296 op _75297 s _75298 i' => @lem5969152 A B C _75297 _75298 x' x s t p1 i p2 j h1 h2 h4 h5)). Qed.
Lemma lem5969154 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x' : B) (t : type1413 A B) (p1 : A) (i : A) (p2 : B) (x : A) (s : A -> Prop) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) (h4 : term2032 A B x' x s t p1 i p2) (h5 : term782 A x s) : False.
Proof. exact (ex_elim (@lem5965724 A B x' x s t p1 i p2 h4) (fun j : B => fun h0 : term2031 A B x' x s t p1 i p2 j => @lem5969153 A B C _75296 op _75297 _75298 x' x s t p1 i p2 j h1 h2 h3 h5 h0)). Qed.
Lemma lem5969155 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x' : B) (t : type1413 A B) (p1 : A) (p2 : B) (x : A) (s : A -> Prop) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) (h4 : term2034 A B x' x s t p1 p2) (h5 : term782 A x s) : False.
Proof. exact (ex_elim (@lem5965723 A B x' x s t p1 p2 h4) (fun i : A => fun h0 : term2033 A B x' x s t p1 p2 i => @lem5969154 A B C _75296 op _75297 _75298 x' t p1 i p2 x s h1 h2 h3 h0 h5)). Qed.
Lemma lem5969156 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) (h4 : term782 A x s) (h5 : term1067 A B x s t p1 p2) : False.
Proof. exact (ex_elim (@lem5965722 A B x s t p1 p2 h5) (fun x' : B => fun h0 : term2035 A B x s t p1 p2 x' => @lem5969155 A B C _75296 op _75297 _75298 x' t p1 p2 x s h1 h2 h3 h0 h4)). Qed.
Lemma lem5969157 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) (h4 : term782 A x s) (h5 : term1067 A B x s t p1 p2) : (term782 A x s) = False.
Proof. exact (prop_ext (fun h6 : term782 A x s => @lem5969156 A B C _75296 op _75297 _75298 x s t p1 p2 h1 h2 h3 h4 h5) (fun h6 : False => @lem5965437 A x s h4)). Qed.
Lemma lem5969158 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) (h4 : term782 A x s) (h5 : term1067 A B x s t p1 p2) : False.
Proof. exact (EQ_MP (@lem5969157 A B C _75296 op _75297 _75298 x s t p1 p2 h1 h2 h3 h4 h5) (@lem5965437 A x s h4)). Qed.
Lemma lem5969159 {A B C : Type'} (t : type1413 A B) (p1 : A) (p2 : B) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) (h4 : term782 A x s) : term2059 A B x s t p1 p2.
Proof. exact (fun h0 : term1067 A B x s t p1 p2 => @lem5969158 A B C _75296 op _75297 _75298 x s t p1 p2 h1 h2 h3 h4 h0). Qed.
Lemma lem5969160 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term2059 A B x s t p1 p2) = (term1070 A B x s t p1 p2).
Proof. exact (@lem69 (term1067 A B x s t p1 p2)). Qed.
Lemma lem5969161 {A B C : Type'} (t : type1413 A B) (p1 : A) (p2 : B) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) (h4 : term782 A x s) : term1070 A B x s t p1 p2.
Proof. exact (EQ_MP (@lem5969160 A B x s t p1 p2) (@lem5969159 A B C t p1 p2 _75296 op _75297 _75298 x s h1 h2 h3 h4)). Qed.
Lemma lem5969166 {A B C : Type'} (t : type1413 A B) (p1 : A) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) (h4 : term782 A x s) : term1072 A B x s t p1.
Proof. exact (fun p2 : B => @lem5969161 A B C t p1 p2 _75296 op _75297 _75298 x s h1 h2 h3 h4). Qed.
Lemma lem5969171 {A B C : Type'} (t : type1413 A B) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) (h4 : term782 A x s) : term1074 A B x s t.
Proof. exact (fun p1 : A => @lem5969166 A B C t p1 _75296 op _75297 _75298 x s h1 h2 h3 h4). Qed.
Lemma lem5969172 {A B C : Type'} (t : type1413 A B) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) (h4 : term782 A x s) : term1084 A B x s t.
Proof. exact (fun h0 : term895 A B x s t => @lem5969171 A B C t _75296 op _75297 _75298 x s h1 h2 h3 h4). Qed.
Lemma lem5969173 {A B C : Type'} (t : type1413 A B) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (_75298 : type441 A B C) (x : A) (s : A -> Prop) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) (h4 : term782 A x s) : term1086 A B x s t.
Proof. exact (fun h0 : @FINITE A s => @lem5969172 A B C t _75296 op _75297 _75298 x s h1 h2 h3 h4). Qed.
Lemma lem5969174 {A B C : Type'} (x : A) (t : type1413 A B) (_75296 : type877 A B C) (op : type1400 C) (_75297 : type621 A B) (s : A -> Prop) (_75298 : type441 A B C) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) (h3 : term1315 A B C _75296 op _75297 s _75298) : term1089 A B x s t.
Proof. exact (fun h0 : term782 A x s => @lem5969173 A B C t _75296 op _75297 _75298 x s h1 h2 h3 h0). Qed.
Lemma lem5969175 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) : term1317 A B C _75296 op _75297 _75298 x s t.
Proof. exact (fun h0 : term1315 A B C _75296 op _75297 s _75298 => @lem5969174 A B C x t _75296 op _75297 s _75298 h1 h2 h0). Qed.
Lemma lem5969176 {A B C : Type'} (_75296 : type877 A B C) (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) : term1318 A B C _75296 op _75297 _75298 x s t.
Proof. exact (fun h0 : @monoidal C op => @lem5969175 A B C _75296 op x s t _75297 _75298 h1 h2). Qed.
Lemma lem5969181 {A B C : Type'} (_75296 : type877 A B C) (x : A) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) : term1320 A B C _75296 _75297 _75298 x s t.
Proof. exact (fun op : type1400 C => @lem5969176 A B C _75296 op x s t _75297 _75298 h1 h2). Qed.
Lemma lem5969186 {A B C : Type'} (_75296 : type877 A B C) (s : A -> Prop) (t : type1413 A B) (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) : term1322 A B C _75296 _75297 _75298 s t.
Proof. exact (fun x : A => @lem5969181 A B C _75296 x s t _75297 _75298 h1 h2). Qed.
Lemma lem5969191 {A B C : Type'} (_75296 : type877 A B C) (t : type1413 A B) (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) : term1324 A B C _75296 _75297 _75298 t.
Proof. exact (fun s : A -> Prop => @lem5969186 A B C _75296 s t _75297 _75298 h1 h2). Qed.
Lemma lem5969196 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) : term1326 A B C _75296 _75297 _75298.
Proof. exact (fun t : type1413 A B => @lem5969191 A B C _75296 t _75297 _75298 h1 h2). Qed.
Lemma lem5969197 {A B C : Type'} (_75296 : type877 A B C) (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) : term1327 A B C _75296 _75297 _75298.
Proof. exact (fun h0 : term1215 A B C _75296 => @lem5969196 A B C _75296 _75297 _75298 h1 h2). Qed.
Lemma lem5969202 {A B C : Type'} (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : term1301 A B _75297) (h2 : term1375 A B C _75298) : term1329 A B C _75297 _75298.
Proof. exact (fun _75296 : type877 A B C => @lem5969197 A B C _75296 _75297 _75298 h1 h2). Qed.
Lemma lem5969203 {A B C : Type'} (_75297 : type621 A B) (_75298 : type441 A B C) (h1 : term1375 A B C _75298) : term1330 A B C _75297 _75298.
Proof. exact (fun h0 : term1301 A B _75297 => @lem5969202 A B C _75297 _75298 h0 h1). Qed.
Lemma lem5969208 {A B C : Type'} (_75298 : type441 A B C) (h1 : term1375 A B C _75298) : term1332 A B C _75298.
Proof. exact (fun _75297 : type621 A B => @lem5969203 A B C _75297 _75298 h1). Qed.
Lemma lem5969209 {A B C : Type'} (_75298 : type441 A B C) : term1377 A B C _75298.
Proof. exact (fun h0 : term1375 A B C _75298 => @lem5969208 A B C _75298 h0). Qed.
Lemma lem5969214 {A B C : Type'} : term1379 A B C.
Proof. exact (fun _75298 : type441 A B C => @lem5969209 A B C _75298). Qed.
Lemma lem5969215 {A B C : Type'} : term1109 A B C.
Proof. exact (EQ_MP (@lem5963805 A B C) (@lem5969214 A B C)). Qed.
Lemma lem5969216 {A B C : Type'} (t : type1413 A B) : term2060 A B C t.
Proof. exact (@lem5969215 A B C t). Qed.
Lemma lem5969217 {A B C : Type'} (t : type1413 A B) : (term2060 A B C t) = (term1105 A B C t).
Proof. exact (eq_refl (term2060 A B C t)). Qed.
Lemma lem5969218 {A B C : Type'} (t : type1413 A B) : term1105 A B C t.
Proof. exact (EQ_MP (@lem5969217 A B C t) (@lem5969216 A B C t)). Qed.
Lemma lem5969219 {A B C : Type'} (t : type1413 A B) (s : A -> Prop) : term2061 A B C t s.
Proof. exact (@lem5969218 A B C t s). Qed.
Lemma lem5969220 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) : (term2061 A B C t s) = (term1101 A B C s t).
Proof. exact (eq_refl (term2061 A B C t s)). Qed.
Lemma lem5969221 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) : term1101 A B C s t.
Proof. exact (EQ_MP (@lem5969220 A B C s t) (@lem5969219 A B C t s)). Qed.
Lemma lem5969222 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : term2062 A B C s t x.
Proof. exact (@lem5969221 A B C s t x). Qed.
Lemma lem5969223 {A B C : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term2062 A B C s t x) = (term1097 A B C x s t).
Proof. exact (eq_refl (term2062 A B C s t x)). Qed.
Lemma lem5969224 {A B C : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : term1097 A B C x s t.
Proof. exact (EQ_MP (@lem5969223 A B C x s t) (@lem5969222 A B C s t x)). Qed.
Lemma lem5969225 {A B C : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (op : type1400 C) : term2063 A B C x s t op.
Proof. exact (@lem5969224 A B C x s t op). Qed.
Lemma lem5969226 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : (term2063 A B C x s t op) = (term1077 A B C op x s t).
Proof. exact (eq_refl (term2063 A B C x s t op)). Qed.
Lemma lem5969227 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : term1077 A B C op x s t.
Proof. exact (EQ_MP (@lem5969226 A B C op x s t) (@lem5969225 A B C x s t op)). Qed.
Lemma lem5969229 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) : term1077 A B C op x s t.
Proof. exact (@lem5962028 A B C op x s t (@lem5969227 A B C op x s t)). Qed.
Lemma lem5969230 {A B C : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (op : type1400 C) (h1 : @monoidal C op) : term1091 A B C op x s t.
Proof. exact (@lem5969229 A B C op x s t (@lem5950451 C op h1)). Qed.
Lemma lem5969231 {A B C : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (op : type1400 C) (h1 : term649 A B C op s) (h2 : @monoidal C op) : term1088 A B x s t.
Proof. exact (@lem5969230 A B C x s t op h2 (@lem5961428 A B C op s h1)). Qed.
Lemma lem5969232 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @monoidal C op) (h3 : term782 A x s) : term1085 A B x s t.
Proof. exact (@lem5969231 A B C x t s op h1 h2 (@lem5961430 A x s h3)). Qed.
Lemma lem5969233 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term782 A x s) : term1083 A B x s t.
Proof. exact (@lem5969232 A B C t op x s h1 h3 h4 (@lem5961429 A s h2)). Qed.
Lemma lem5969234 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term782 A x s) : term1075 A B x s t.
Proof. exact (@lem5969233 A B C t op x s h2 h3 h4 h5 (@lem5961431 A B x s t h1)). Qed.
Lemma lem5969235 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term1076 A B x s t) (h6 : term782 A x s) : False.
Proof. exact (@lem5969234 A B C t op x s h1 h2 h3 h4 h6 (@lem5962012 A B x s t h5)). Qed.
Lemma lem5969236 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term1076 A B x s t) (h6 : term782 A x s) : (term1076 A B x s t) = False.
Proof. exact (prop_ext (fun h7 : term1076 A B x s t => @lem5969235 A B C op t x s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5962012 A B x s t h5)). Qed.
Lemma lem5969237 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term1076 A B x s t) (h6 : term782 A x s) : False.
Proof. exact (EQ_MP (@lem5969236 A B C op t x s h1 h2 h3 h4 h5 h6) (@lem5962012 A B x s t h5)). Qed.
Lemma lem5969238 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term782 A x s) : term1075 A B x s t.
Proof. exact (fun h0 : term1076 A B x s t => @lem5969237 A B C op t x s h1 h2 h3 h4 h0 h5). Qed.
Lemma lem5969239 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term782 A x s) : term1074 A B x s t.
Proof. exact (EQ_MP (@lem5962011 A B x s t) (@lem5969238 A B C t op x s h1 h2 h3 h4 h5)). Qed.
Lemma lem5969240 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term782 A x s) : term973 A B x s t.
Proof. exact (EQ_MP (@lem5962007 A B x s t) (@lem5969239 A B C t op x s h1 h2 h3 h4 h5)). Qed.
Lemma lem5969241 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term782 A x s) : term945 A B x s t.
Proof. exact (EQ_MP (@lem5961699 A B t x s h1 h3 h5) (@lem5969240 A B C t op x s h1 h2 h3 h4 h5)). Qed.
Lemma lem5969242 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) (h1 : (term853 A B C op x s t x') = (term946 A B C x op s t x')) : (term853 A B C op x s t x') = (term946 A B C x op s t x').
Proof. exact (h1). Qed.
Lemma lem5969243 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : (term2064 A B C x op s t x') = (term2064 A B C x op s t x').
Proof. exact (eq_refl (term2064 A B C x op s t x')). Qed.
Lemma lem5969244 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) (h1 : (term853 A B C op x s t x') = (term946 A B C x op s t x')) : (term2065 A B C op x s t x') = (term2066 A B C x op s t x').
Proof. exact (MK_COMB (@lem5969243 A B C x op s t x') (@lem5969242 A B C x op s t x' h1)). Qed.
Lemma lem5969245 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : (term2066 A B C x op s t x') = ((term914 A B C x op s t x') = (term946 A B C x op s t x')).
Proof. exact (eq_refl (term2066 A B C x op s t x')). Qed.
Lemma lem5969246 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : (term2067 A B C op x s t x') = (term2067 A B C op x s t x').
Proof. exact (eq_refl (term2067 A B C op x s t x')). Qed.
Lemma lem5969247 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : ((term2065 A B C op x s t x') = (term2066 A B C x op s t x')) = ((term2065 A B C op x s t x') = ((term914 A B C x op s t x') = (term946 A B C x op s t x'))).
Proof. exact (MK_COMB (@lem5969246 A B C op x s t x') (@lem5969245 A B C x op s t x')). Qed.
Lemma lem5969248 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : (term2065 A B C op x s t x') = ((term914 A B C x op s t x') = (term853 A B C op x s t x')).
Proof. exact (eq_refl (term2065 A B C op x s t x')). Qed.
Lemma lem5969249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5969250 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : (term2067 A B C op x s t x') = (term2068 A B C op x s t x').
Proof. exact (MK_COMB (@lem5969249) (@lem5969248 A B C op x s t x')). Qed.
Lemma lem5969251 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : ((term914 A B C x op s t x') = (term946 A B C x op s t x')) = ((term914 A B C x op s t x') = (term946 A B C x op s t x')).
Proof. exact (eq_refl ((term914 A B C x op s t x') = (term946 A B C x op s t x'))). Qed.
Lemma lem5969252 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : ((term2065 A B C op x s t x') = ((term914 A B C x op s t x') = (term946 A B C x op s t x'))) = (((term914 A B C x op s t x') = (term853 A B C op x s t x')) = ((term914 A B C x op s t x') = (term946 A B C x op s t x'))).
Proof. exact (MK_COMB (@lem5969250 A B C op x s t x') (@lem5969251 A B C x op s t x')). Qed.
Lemma lem5969253 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : ((term2065 A B C op x s t x') = (term2066 A B C x op s t x')) = (((term914 A B C x op s t x') = (term853 A B C op x s t x')) = ((term914 A B C x op s t x') = (term946 A B C x op s t x'))).
Proof. exact (TRANS (@lem5969247 A B C x op s t x') (@lem5969252 A B C x op s t x')). Qed.
Lemma lem5969254 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) (h1 : (term853 A B C op x s t x') = (term946 A B C x op s t x')) : ((term914 A B C x op s t x') = (term853 A B C op x s t x')) = ((term914 A B C x op s t x') = (term946 A B C x op s t x')).
Proof. exact (EQ_MP (@lem5969253 A B C x op s t x') (@lem5969244 A B C x op s t x' h1)). Qed.
Lemma lem5969255 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) (h1 : (term853 A B C op x s t x') = (term946 A B C x op s t x')) : ((term914 A B C x op s t x') = (term946 A B C x op s t x')) = ((term914 A B C x op s t x') = (term853 A B C op x s t x')).
Proof. exact (SYM (@lem5969254 A B C x op s t x' h1)). Qed.
Lemma lem5969256 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) : (term614 A B C op s t x') = (term614 A B C op s t x').
Proof. exact (eq_refl (term614 A B C op s t x')). Qed.
Lemma lem5969257 {C : Type'} (op : type1400 C) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5969278 {A B C : Type'} (op : type1400 C) : term2069 A B C op.
Proof. exact (@lem5942955 A B C op). Qed.
Lemma lem5969279 {A B C : Type'} (op : type1400 C) : (term2069 A B C op) = (term2070 A B C op).
Proof. exact (eq_refl (term2069 A B C op)). Qed.
Lemma lem5969282 {A B C : Type'} (op : type1400 C) : term2070 A B C op.
Proof. exact (EQ_MP (@lem5969279 A B C op) (@lem5969278 A B C op)). Qed.
Lemma lem5969283 {A B C : Type'} (op : type1400 C) : term2070 A B C op.
Proof. exact (@lem5969282 A B C op). Qed.
Lemma lem5969284 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term2071 A B C op.
Proof. exact (@lem5969283 A B C op (@lem5950451 C op h1)). Qed.
Lemma lem5969285 {A B C : Type'} (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term2072 A B C op f.
Proof. exact (@lem5969284 A B C op h1 f). Qed.
Lemma lem5969286 {A B C : Type'} (op : type1400 C) (f : A -> B) : (term2072 A B C op f) = (term2073 A B C op f).
Proof. exact (eq_refl (term2072 A B C op f)). Qed.
Lemma lem5969287 {A B C : Type'} (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term2073 A B C op f.
Proof. exact (EQ_MP (@lem5969286 A B C op f) (@lem5969285 A B C f op h1)). Qed.
Lemma lem5969288 {A B C : Type'} (f : A -> B) (g : B -> C) (op : type1400 C) (h1 : @monoidal C op) : term2074 A B C op f g.
Proof. exact (@lem5969287 A B C f op h1 g). Qed.
Lemma lem5969289 {A B C : Type'} (op : type1400 C) (g : B -> C) (f : A -> B) : (term2074 A B C op f g) = (term2075 A B C op g f).
Proof. exact (eq_refl (term2074 A B C op f g)). Qed.
Lemma lem5969290 {A B C : Type'} (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term2075 A B C op g f.
Proof. exact (EQ_MP (@lem5969289 A B C op g f) (@lem5969288 A B C f g op h1)). Qed.
Lemma lem5969291 {A B C : Type'} (g : B -> C) (f : A -> B) (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term2076 A B C op g f s.
Proof. exact (@lem5969290 A B C g f op h1 s). Qed.
Lemma lem5969292 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (g : B -> C) (f : A -> B) : (term2076 A B C op g f s) = (term2077 A B C op s g f).
Proof. exact (eq_refl (term2076 A B C op g f s)). Qed.
Lemma lem5969295 {A B C : Type'} (s : A -> Prop) (g : B -> C) (f : A -> B) (op : type1400 C) (h1 : @monoidal C op) : term2077 A B C op s g f.
Proof. exact (EQ_MP (@lem5969292 A B C op s g f) (@lem5969291 A B C g f s op h1)). Qed.
Lemma lem5969296 {A B C : Type'} (s : B -> Prop) (g : type1209 A B C) (f : type1478 A B) (op : type1400 C) (h1 : @monoidal C op) : term2078 A B C op s g f.
Proof. exact (@lem5969295 B (prod A B) C s g f op h1). Qed.
Lemma lem5969297 {A B C : Type'} (t : type1413 A B) (x' : type1412 A B C) (x : A) (op : type1400 C) (h1 : @monoidal C op) : term2079 A B C op t x' x.
Proof. exact (@lem5969296 A B C (t x) (term759 A B C x') (term962 A B x) op h1). Qed.
Lemma lem5969299 (p : Prop) (q : Prop) (r : Prop) : term943 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem5969300 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : A) (x' : type1412 A B C) : term2080 A B C op t x x'.
Proof. exact (@lem5969299 (term2081 A B t x) ((term2082 A B C op t x x') = (term2083 A B C op t x' x)) ((term818 A B C op t x' x) = (term2082 A B C op t x x'))). Qed.
Lemma lem5969316 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term706 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5969317 (p : Prop) (q : Prop) (p' : Prop) : term707 p q p'.
Proof. exact (fun q' : Prop => @lem5969316 p q p' q'). Qed.
Lemma lem5969318 (p : Prop) (q : Prop) : term708 p q.
Proof. exact (fun p' : Prop => @lem5969317 p q p'). Qed.
Lemma lem5969319 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : term2084 A B t x x' y.
Proof. exact (@lem5969318 (term2085 A B t x' x y) (x' = y)). Qed.
Lemma lem5969320 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) : term2086 A B t x x' y p'.
Proof. exact (@lem5969319 A B t x x' y p'). Qed.
Lemma lem5969321 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) : (term2086 A B t x x' y p') = (term2087 A B t x x' y p').
Proof. exact (eq_refl (term2086 A B t x x' y p')). Qed.
Lemma lem5969322 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) : term2087 A B t x x' y p'.
Proof. exact (EQ_MP (@lem5969321 A B t x x' y p') (@lem5969320 A B t x x' y p')). Qed.
Lemma lem5969323 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) (q' : Prop) : term2088 A B t x x' y p' q'.
Proof. exact (@lem5969322 A B t x x' y p' q'). Qed.
Lemma lem5969324 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) (q' : Prop) : (term2088 A B t x x' y p' q') = (term2089 A B t x x' y p' q').
Proof. exact (eq_refl (term2088 A B t x x' y p' q')). Qed.
Lemma lem5969325 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) (q' : Prop) : term2089 A B t x x' y p' q'.
Proof. exact (EQ_MP (@lem5969324 A B t x x' y p' q') (@lem5969323 A B t x x' y p' q')). Qed.
Lemma lem5969333 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5969334 {A B : Type'} (f : type1478 A B) (y : B) : (term1006 A B f y) = (f y).
Proof. exact (@lem5969333 B (prod A B) f y). Qed.
Lemma lem5969335 {A B : Type'} (x : A) (x' : B) : (term1007 A B x x') = (term1008 A B x x').
Proof. exact (@lem5969334 A B (term962 A B x) x'). Qed.
Lemma lem5969336 {A B : Type'} (x : A) (j : B) : (term1008 A B x j) = (@pair A B x j).
Proof. exact (eq_refl (term1008 A B x j)). Qed.
Lemma lem5969337 {A B : Type'} (x : A) : (term1009 A B x) = (term962 A B x).
Proof. exact (fun_ext (fun j : B => @lem5969336 A B x j)). Qed.
Lemma lem5969338 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5969339 {A B : Type'} (x : A) (x' : B) : (term1007 A B x x') = (term1008 A B x x').
Proof. exact (MK_COMB (@lem5969337 A B x) (@lem5969338 B x')). Qed.
Lemma lem5969340 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem5969341 {A B : Type'} (x : A) (x' : B) : (term1010 A B x x') = (term1011 A B x x').
Proof. exact (MK_COMB (@lem5969340 A B) (@lem5969339 A B x x')). Qed.
Lemma lem5969342 {A B : Type'} (x : A) (x' : B) : (term1008 A B x x') = (@pair A B x x').
Proof. exact (eq_refl (term1008 A B x x')). Qed.
Lemma lem5969343 {A B : Type'} (x : A) (x' : B) : ((term1007 A B x x') = (term1008 A B x x')) = ((term1008 A B x x') = (@pair A B x x')).
Proof. exact (MK_COMB (@lem5969341 A B x x') (@lem5969342 A B x x')). Qed.
Lemma lem5969344 {A B : Type'} (x : A) (x' : B) : (term1008 A B x x') = (@pair A B x x').
Proof. exact (EQ_MP (@lem5969343 A B x x') (@lem5969335 A B x x')). Qed.
Lemma lem5969345 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem5969346 {A B : Type'} (x : A) (x' : B) : (term1011 A B x x') = (term1012 A B x x').
Proof. exact (MK_COMB (@lem5969345 A B) (@lem5969344 A B x x')). Qed.
Lemma lem5969348 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5969349 {A B : Type'} (f : type1478 A B) (y : B) : (term1006 A B f y) = (f y).
Proof. exact (@lem5969348 B (prod A B) f y). Qed.
Lemma lem5969350 {A B : Type'} (x : A) (y : B) : (term1007 A B x y) = (term1008 A B x y).
Proof. exact (@lem5969349 A B (term962 A B x) y). Qed.
Lemma lem5969351 {A B : Type'} (x : A) (j : B) : (term1008 A B x j) = (@pair A B x j).
Proof. exact (eq_refl (term1008 A B x j)). Qed.
Lemma lem5969352 {A B : Type'} (x : A) : (term1009 A B x) = (term962 A B x).
Proof. exact (fun_ext (fun j : B => @lem5969351 A B x j)). Qed.
Lemma lem5969353 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5969354 {A B : Type'} (x : A) (y : B) : (term1007 A B x y) = (term1008 A B x y).
Proof. exact (MK_COMB (@lem5969352 A B x) (@lem5969353 B y)). Qed.
Lemma lem5969355 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem5969356 {A B : Type'} (x : A) (y : B) : (term1010 A B x y) = (term1011 A B x y).
Proof. exact (MK_COMB (@lem5969355 A B) (@lem5969354 A B x y)). Qed.
Lemma lem5969357 {A B : Type'} (x : A) (y : B) : (term1008 A B x y) = (@pair A B x y).
Proof. exact (eq_refl (term1008 A B x y)). Qed.
Lemma lem5969358 {A B : Type'} (x : A) (y : B) : ((term1007 A B x y) = (term1008 A B x y)) = ((term1008 A B x y) = (@pair A B x y)).
Proof. exact (MK_COMB (@lem5969356 A B x y) (@lem5969357 A B x y)). Qed.
Lemma lem5969359 {A B : Type'} (x : A) (y : B) : (term1008 A B x y) = (@pair A B x y).
Proof. exact (EQ_MP (@lem5969358 A B x y) (@lem5969350 A B x y)). Qed.
Lemma lem5969360 {A B : Type'} (x : B) (x' : A) (y : B) : ((term1008 A B x' x) = (term1008 A B x' y)) = ((@pair A B x' x) = (@pair A B x' y)).
Proof. exact (MK_COMB (@lem5969346 A B x' x) (@lem5969359 A B x' y)). Qed.
Lemma lem5969363 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term2090 A B y t x) = (term2090 A B y t x).
Proof. exact (eq_refl (term2090 A B y t x)). Qed.
Lemma lem5969364 {A B : Type'} (t : type1413 A B) (x : B) (x' : A) (y : B) : (term2091 A B t x x' y) = (term2092 A B t x x' y).
Proof. exact (MK_COMB (@lem5969363 A B y t x') (@lem5969360 A B x x' y)). Qed.
Lemma lem5969369 {A B : Type'} (x : B) (t : type1413 A B) (x' : A) : (term2090 A B x t x') = (term2090 A B x t x').
Proof. exact (eq_refl (term2090 A B x t x')). Qed.
Lemma lem5969370 {A B : Type'} (t : type1413 A B) (x : B) (x' : A) (y : B) : (term2085 A B t x x' y) = (term2093 A B t x x' y).
Proof. exact (MK_COMB (@lem5969369 A B x t x') (@lem5969364 A B t x x' y)). Qed.
Lemma lem5969377 {A B : Type'} (t : type1413 A B) (x : B) (x' : A) (y : B) (q' : Prop) : term2094 A B t x x' y q'.
Proof. exact (@lem5969325 A B t x' x y (term2093 A B t x x' y) q'). Qed.
Lemma lem5969378 {A B : Type'} (t : type1413 A B) (x : B) (x' : A) (y : B) (q' : Prop) : term2095 A B t x x' y q'.
Proof. exact (@lem5969377 A B t x x' y q' (@lem5969370 A B t x x' y)). Qed.
Lemma lem5969390 {B : Type'} (x : B) (y : B) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5969391 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : term2096 A B t x x' y.
Proof. exact (fun h0 : term2093 A B t x' x y => @lem5969390 B x' y). Qed.
Lemma lem5969392 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : term2097 A B t x x' y.
Proof. exact (@lem5969378 A B t x' x y (x' = y)). Qed.
Lemma lem5969393 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : (term2098 A B t x x' y) = (term2099 A B t x x' y).
Proof. exact (@lem5969392 A B t x x' y (@lem5969391 A B t x x' y)). Qed.
Lemma lem5969439 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) : (term2100 A B t x x') = (term2101 A B t x x').
Proof. exact (fun_ext (fun y : B => @lem5969393 A B t x x' y)). Qed.
Lemma lem5969485 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5969486 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) : (term2102 A B t x x') = (term2103 A B t x x').
Proof. exact (MK_COMB (@lem5969485 B) (@lem5969439 A B t x x')). Qed.
Lemma lem5969538 {A B : Type'} (t : type1413 A B) (x : A) : (term2104 A B t x) = (term2105 A B t x).
Proof. exact (fun_ext (fun x' : B => @lem5969486 A B t x x')). Qed.
Lemma lem5969590 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5969591 {A B : Type'} (t : type1413 A B) (x : A) : (term2081 A B t x) = (term2106 A B t x).
Proof. exact (MK_COMB (@lem5969590 B) (@lem5969538 A B t x)). Qed.
Lemma lem5969649 {A B : Type'} (t : type1413 A B) (x : A) : (term2106 A B t x) = (term2081 A B t x).
Proof. exact (SYM (@lem5969591 A B t x)). Qed.
Lemma lem5969652 {A B : Type'} (x : A) : term6 A B x.
Proof. exact (@lem47438 A B x). Qed.
Lemma lem5969653 {A B : Type'} (x : A) : (term6 A B x) = (term7 A B x).
Proof. exact (eq_refl (term6 A B x)). Qed.
Lemma lem5969654 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (EQ_MP (@lem5969653 A B x) (@lem5969652 A B x)). Qed.
Lemma lem5969655 {A B : Type'} (x : A) (y : B) : term8 A B x y.
Proof. exact (@lem5969654 A B x y). Qed.
Lemma lem5969656 {A B : Type'} (x : A) (y : B) : (term8 A B x y) = (term9 A B x y).
Proof. exact (eq_refl (term8 A B x y)). Qed.
Lemma lem5969657 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (EQ_MP (@lem5969656 A B x y) (@lem5969655 A B x y)). Qed.
Lemma lem5969658 {A B : Type'} (x : A) (y : B) (a : A) : term10 A B x y a.
Proof. exact (@lem5969657 A B x y a). Qed.
Lemma lem5969659 {A B : Type'} (x : A) (a : A) (y : B) : (term10 A B x y a) = (term11 A B x a y).
Proof. exact (eq_refl (term10 A B x y a)). Qed.
Lemma lem5969660 {A B : Type'} (x : A) (a : A) (y : B) : term11 A B x a y.
Proof. exact (EQ_MP (@lem5969659 A B x a y) (@lem5969658 A B x y a)). Qed.
Lemma lem5969661 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term12 A B x a y b.
Proof. exact (@lem5969660 A B x a y b). Qed.
Lemma lem5969662 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term12 A B x a y b) = (((@pair A B x y) = (@pair A B a b)) = (term13 A B x a y b)).
Proof. exact (eq_refl (term12 A B x a y b)). Qed.
Lemma lem5969706 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term706 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5969707 (p : Prop) (q : Prop) (p' : Prop) : term707 p q p'.
Proof. exact (fun q' : Prop => @lem5969706 p q p' q'). Qed.
Lemma lem5969708 (p : Prop) (q : Prop) : term708 p q.
Proof. exact (fun p' : Prop => @lem5969707 p q p'). Qed.
Lemma lem5969709 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : term2107 A B t x x' y.
Proof. exact (@lem5969708 (term2093 A B t x' x y) (x' = y)). Qed.
Lemma lem5969710 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) : term2108 A B t x x' y p'.
Proof. exact (@lem5969709 A B t x x' y p'). Qed.
Lemma lem5969711 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) : (term2108 A B t x x' y p') = (term2109 A B t x x' y p').
Proof. exact (eq_refl (term2108 A B t x x' y p')). Qed.
Lemma lem5969712 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) : term2109 A B t x x' y p'.
Proof. exact (EQ_MP (@lem5969711 A B t x x' y p') (@lem5969710 A B t x x' y p')). Qed.
Lemma lem5969713 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) (q' : Prop) : term2110 A B t x x' y p' q'.
Proof. exact (@lem5969712 A B t x x' y p' q'). Qed.
Lemma lem5969714 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) (q' : Prop) : (term2110 A B t x x' y p' q') = (term2111 A B t x x' y p' q').
Proof. exact (eq_refl (term2110 A B t x x' y p' q')). Qed.
Lemma lem5969715 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) (q' : Prop) : term2111 A B t x x' y p' q'.
Proof. exact (EQ_MP (@lem5969714 A B t x x' y p' q') (@lem5969713 A B t x x' y p' q')). Qed.
Lemma lem5969721 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term13 A B x a y b).
Proof. exact (EQ_MP (@lem5969662 A B x a y b) (@lem5969661 A B x a y b)). Qed.
Lemma lem5969722 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term13 A B x a y b).
Proof. exact (@lem5969721 A B x a y b). Qed.
Lemma lem5969723 {A B : Type'} (x : A) (x' : B) (y : B) : ((@pair A B x x') = (@pair A B x y)) = (term2112 A B x x' y).
Proof. exact (@lem5969722 A B x x x' y). Qed.
Lemma lem5969727 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5969728 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem5969727 A x). Qed.
Lemma lem5969729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5969730 {A : Type'} (x : A) : (term2113 A x) = (and True).
Proof. exact (MK_COMB (@lem5969729) (@lem5969728 A x)). Qed.
Lemma lem5969733 {B : Type'} (x : B) (y : B) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5969734 {A B : Type'} (x : A) (x' : B) (y : B) : (term2112 A B x x' y) = (term2114 B x' y).
Proof. exact (MK_COMB (@lem5969730 A x) (@lem5969733 B x' y)). Qed.
Lemma lem5969736 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5969737 {B : Type'} (x : B) (y : B) : (term2114 B x y) = (x = y).
Proof. exact (@lem5969736 (x = y)). Qed.
Lemma lem5969740 {A B : Type'} (x : A) (x' : B) (y : B) : (term2112 A B x x' y) = (x' = y).
Proof. exact (TRANS (@lem5969734 A B x x' y) (@lem5969737 B x' y)). Qed.
Lemma lem5969741 {A B : Type'} (x : A) (x' : B) (y : B) : ((@pair A B x x') = (@pair A B x y)) = (x' = y).
Proof. exact (TRANS (@lem5969723 A B x x' y) (@lem5969740 A B x x' y)). Qed.
Lemma lem5969742 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term2090 A B y t x) = (term2090 A B y t x).
Proof. exact (eq_refl (term2090 A B y t x)). Qed.
Lemma lem5969743 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : (term2092 A B t x' x y) = (term2115 A B t x x' y).
Proof. exact (MK_COMB (@lem5969742 A B y t x) (@lem5969741 A B x x' y)). Qed.
Lemma lem5969748 {A B : Type'} (x : B) (t : type1413 A B) (x' : A) : (term2090 A B x t x') = (term2090 A B x t x').
Proof. exact (eq_refl (term2090 A B x t x')). Qed.
Lemma lem5969749 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : (term2093 A B t x' x y) = (term2116 A B t x x' y).
Proof. exact (MK_COMB (@lem5969748 A B x' t x) (@lem5969743 A B t x x' y)). Qed.
Lemma lem5969756 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (q' : Prop) : term2117 A B t x x' y q'.
Proof. exact (@lem5969715 A B t x x' y (term2116 A B t x x' y) q'). Qed.
Lemma lem5969757 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (q' : Prop) : term2118 A B t x x' y q'.
Proof. exact (@lem5969756 A B t x x' y q' (@lem5969749 A B t x x' y)). Qed.
Lemma lem5969758 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (h1 : term2116 A B t x x' y) : term2116 A B t x x' y.
Proof. exact (h1). Qed.
Lemma lem5969759 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (h1 : term2116 A B t x x' y) : term2115 A B t x x' y.
Proof. exact (proj2 (@lem5969758 A B t x x' y h1)). Qed.
Lemma lem5969770 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (h1 : term2116 A B t x x' y) : x' = y.
Proof. exact (proj2 (@lem5969759 A B t x x' y h1)). Qed.
Lemma lem5969771 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5969772 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (h1 : term2116 A B t x x' y) : (@eq B x') = (@eq B y).
Proof. exact (MK_COMB (@lem5969771 B) (@lem5969770 A B t x x' y h1)). Qed.
Lemma lem5969773 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5969774 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (h1 : term2116 A B t x x' y) : (x' = y) = (y = y).
Proof. exact (MK_COMB (@lem5969772 A B t x x' y h1) (@lem5969773 B y)). Qed.
Lemma lem5969776 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5969777 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem5969776 B x). Qed.
Lemma lem5969778 {B : Type'} (y : B) : (y = y) = True.
Proof. exact (@lem5969777 B y). Qed.
Lemma lem5969779 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (h1 : term2116 A B t x x' y) : (x' = y) = True.
Proof. exact (TRANS (@lem5969774 A B t x x' y h1) (@lem5969778 B y)). Qed.
Lemma lem5969780 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : term2119 A B t x x' y.
Proof. exact (fun h0 : term2116 A B t x x' y => @lem5969779 A B t x x' y h0). Qed.
Lemma lem5969781 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : term2120 A B t x x' y.
Proof. exact (@lem5969757 A B t x x' y True). Qed.
Lemma lem5969782 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : (term2099 A B t x x' y) = (term2121 A B t x x' y).
Proof. exact (@lem5969781 A B t x x' y (@lem5969780 A B t x x' y)). Qed.
Lemma lem5969784 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5969785 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : (term2121 A B t x x' y) = True.
Proof. exact (@lem5969784 (term2116 A B t x x' y)). Qed.
Lemma lem5969786 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : (term2099 A B t x x' y) = True.
Proof. exact (TRANS (@lem5969782 A B t x x' y) (@lem5969785 A B t x x' y)). Qed.
Lemma lem5969787 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) : (term2101 A B t x x') = (term729 B).
Proof. exact (fun_ext (fun y : B => @lem5969786 A B t x x' y)). Qed.
Lemma lem5969788 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5969789 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) : (term2103 A B t x x') = (term730 B).
Proof. exact (MK_COMB (@lem5969788 B) (@lem5969787 A B t x x')). Qed.
Lemma lem5969791 {A : Type'} (t : Prop) : (term592 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5969792 {B : Type'} (t : Prop) : (term592 B t) = t.
Proof. exact (@lem5969791 B t). Qed.
Lemma lem5969793 {B : Type'} : (term730 B) = True.
Proof. exact (@lem5969792 B True). Qed.
Lemma lem5969794 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) : (term2103 A B t x x') = True.
Proof. exact (TRANS (@lem5969789 A B t x x') (@lem5969793 B)). Qed.
Lemma lem5969795 {A B : Type'} (t : type1413 A B) (x : A) : (term2105 A B t x) = (term729 B).
Proof. exact (fun_ext (fun x' : B => @lem5969794 A B t x x')). Qed.
Lemma lem5969796 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5969797 {A B : Type'} (t : type1413 A B) (x : A) : (term2106 A B t x) = (term730 B).
Proof. exact (MK_COMB (@lem5969796 B) (@lem5969795 A B t x)). Qed.
Lemma lem5969799 {A : Type'} (t : Prop) : (term592 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5969800 {B : Type'} (t : Prop) : (term592 B t) = t.
Proof. exact (@lem5969799 B t). Qed.
Lemma lem5969801 {B : Type'} : (term730 B) = True.
Proof. exact (@lem5969800 B True). Qed.
Lemma lem5969802 {A B : Type'} (t : type1413 A B) (x : A) : (term2106 A B t x) = True.
Proof. exact (TRANS (@lem5969797 A B t x) (@lem5969801 B)). Qed.
Lemma lem5969803 {A B : Type'} (t : type1413 A B) (x : A) : True = (term2106 A B t x).
Proof. exact (SYM (@lem5969802 A B t x)). Qed.
Lemma lem5969805 {A B : Type'} (t : type1413 A B) (x : A) : term2106 A B t x.
Proof. exact (EQ_MP (@lem5969803 A B t x) (@lem0)). Qed.
Lemma lem5969806 {A B : Type'} (t : type1413 A B) (x : A) : term2081 A B t x.
Proof. exact (EQ_MP (@lem5969649 A B t x) (@lem5969805 A B t x)). Qed.
Lemma lem5969807 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) (h1 : (term2082 A B C op t x x') = (term2083 A B C op t x' x)) : (term2082 A B C op t x x') = (term2083 A B C op t x' x).
Proof. exact (h1). Qed.
Lemma lem5969808 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : (term2122 A B C op t x' x) = (term2122 A B C op t x' x).
Proof. exact (eq_refl (term2122 A B C op t x' x)). Qed.
Lemma lem5969809 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) (h1 : (term2082 A B C op t x x') = (term2083 A B C op t x' x)) : (term2123 A B C op t x x') = (term2124 A B C op t x' x).
Proof. exact (MK_COMB (@lem5969808 A B C op t x' x) (@lem5969807 A B C op t x' x h1)). Qed.
Lemma lem5969810 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : (term2124 A B C op t x' x) = ((term818 A B C op t x' x) = (term2083 A B C op t x' x)).
Proof. exact (eq_refl (term2124 A B C op t x' x)). Qed.
Lemma lem5969811 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : A) (x' : type1412 A B C) : (term2125 A B C op t x x') = (term2125 A B C op t x x').
Proof. exact (eq_refl (term2125 A B C op t x x')). Qed.
Lemma lem5969812 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : ((term2123 A B C op t x x') = (term2124 A B C op t x' x)) = ((term2123 A B C op t x x') = ((term818 A B C op t x' x) = (term2083 A B C op t x' x))).
Proof. exact (MK_COMB (@lem5969811 A B C op t x x') (@lem5969810 A B C op t x' x)). Qed.
Lemma lem5969813 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : A) (x' : type1412 A B C) : (term2123 A B C op t x x') = ((term818 A B C op t x' x) = (term2082 A B C op t x x')).
Proof. exact (eq_refl (term2123 A B C op t x x')). Qed.
Lemma lem5969814 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5969815 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : A) (x' : type1412 A B C) : (term2125 A B C op t x x') = (term2126 A B C op t x x').
Proof. exact (MK_COMB (@lem5969814) (@lem5969813 A B C op t x x')). Qed.
Lemma lem5969816 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : ((term818 A B C op t x' x) = (term2083 A B C op t x' x)) = ((term818 A B C op t x' x) = (term2083 A B C op t x' x)).
Proof. exact (eq_refl ((term818 A B C op t x' x) = (term2083 A B C op t x' x))). Qed.
Lemma lem5969817 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : ((term2123 A B C op t x x') = ((term818 A B C op t x' x) = (term2083 A B C op t x' x))) = (((term818 A B C op t x' x) = (term2082 A B C op t x x')) = ((term818 A B C op t x' x) = (term2083 A B C op t x' x))).
Proof. exact (MK_COMB (@lem5969815 A B C op t x x') (@lem5969816 A B C op t x' x)). Qed.
Lemma lem5969818 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : ((term2123 A B C op t x x') = (term2124 A B C op t x' x)) = (((term818 A B C op t x' x) = (term2082 A B C op t x x')) = ((term818 A B C op t x' x) = (term2083 A B C op t x' x))).
Proof. exact (TRANS (@lem5969812 A B C op t x' x) (@lem5969817 A B C op t x' x)). Qed.
Lemma lem5969819 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) (h1 : (term2082 A B C op t x x') = (term2083 A B C op t x' x)) : ((term818 A B C op t x' x) = (term2082 A B C op t x x')) = ((term818 A B C op t x' x) = (term2083 A B C op t x' x)).
Proof. exact (EQ_MP (@lem5969818 A B C op t x' x) (@lem5969809 A B C op t x' x h1)). Qed.
Lemma lem5969820 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) (h1 : (term2082 A B C op t x x') = (term2083 A B C op t x' x)) : ((term818 A B C op t x' x) = (term2083 A B C op t x' x)) = ((term818 A B C op t x' x) = (term2082 A B C op t x x')).
Proof. exact (SYM (@lem5969819 A B C op t x' x h1)). Qed.
Lemma lem5969824 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term5 A B C f g).
Proof. exact (EQ_MP (@lem5947367 A B C f g) (@lem5947366 A B C f g)). Qed.
Lemma lem5969825 {A B C : Type'} (f : type1209 A B C) (g : type1478 A B) : (@o B (prod A B) C f g) = (term2127 A B C f g).
Proof. exact (@lem5969824 B (prod A B) C f g). Qed.
Lemma lem5969826 {A B C : Type'} (x' : type1412 A B C) (x : A) : (term2128 A B C x' x) = (term2129 A B C x' x).
Proof. exact (@lem5969825 A B C (term759 A B C x') (term962 A B x)). Qed.
Lemma lem5969836 {A B : Type'} (f : A -> B) (y : A) : (term72 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5969837 {A B : Type'} (f : type1478 A B) (y : B) : (term1006 A B f y) = (f y).
Proof. exact (@lem5969836 B (prod A B) f y). Qed.
Lemma lem5969838 {A B : Type'} (x : A) (x' : B) : (term1007 A B x x') = (term1008 A B x x').
Proof. exact (@lem5969837 A B (term962 A B x) x'). Qed.
Lemma lem5969839 {A B : Type'} (x : A) (j : B) : (term1008 A B x j) = (@pair A B x j).
Proof. exact (eq_refl (term1008 A B x j)). Qed.
Lemma lem5969840 {A B : Type'} (x : A) : (term1009 A B x) = (term962 A B x).
Proof. exact (fun_ext (fun j : B => @lem5969839 A B x j)). Qed.
Lemma lem5969841 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5969842 {A B : Type'} (x : A) (x' : B) : (term1007 A B x x') = (term1008 A B x x').
Proof. exact (MK_COMB (@lem5969840 A B x) (@lem5969841 B x')). Qed.
Lemma lem5969843 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem5969844 {A B : Type'} (x : A) (x' : B) : (term1010 A B x x') = (term1011 A B x x').
Proof. exact (MK_COMB (@lem5969843 A B) (@lem5969842 A B x x')). Qed.
Lemma lem5969845 {A B : Type'} (x : A) (x' : B) : (term1008 A B x x') = (@pair A B x x').
Proof. exact (eq_refl (term1008 A B x x')). Qed.
Lemma lem5969846 {A B : Type'} (x : A) (x' : B) : ((term1007 A B x x') = (term1008 A B x x')) = ((term1008 A B x x') = (@pair A B x x')).
Proof. exact (MK_COMB (@lem5969844 A B x x') (@lem5969845 A B x x')). Qed.
Lemma lem5969847 {A B : Type'} (x : A) (x' : B) : (term1008 A B x x') = (@pair A B x x').
Proof. exact (EQ_MP (@lem5969846 A B x x') (@lem5969838 A B x x')). Qed.
Lemma lem5969848 {A B C : Type'} (x' : type1412 A B C) : (term759 A B C x') = (term759 A B C x').
Proof. exact (eq_refl (term759 A B C x')). Qed.
Lemma lem5969849 {A B C : Type'} (x' : type1412 A B C) (x : A) (x'' : B) : (term2130 A B C x' x x'') = (term2131 A B C x' x x'').
Proof. exact (MK_COMB (@lem5969848 A B C x') (@lem5969847 A B x x'')). Qed.
Lemma lem5969850 {A B : Type'} (a0 : A) (a1 : B) : a0 = (term2132 A B a0 a1).
Proof. exact (@lem51128 A B a0 a1). Qed.
Lemma lem5969851 {A B : Type'} (i : A) (j : B) : i = (term2132 A B i j).
Proof. exact (@lem5969850 A B i j). Qed.
Lemma lem5969852 {A B : Type'} (a0 : A) (a1 : B) : a1 = (term2133 A B a0 a1).
Proof. exact (@lem51159 A B a0 a1). Qed.
Lemma lem5969853 {A B : Type'} (i : A) (j : B) : j = (term2133 A B i j).
Proof. exact (@lem5969852 A B i j). Qed.
Lemma lem5969854 {A : Type'} (i : A) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem5969855 {A : Type'} : (term2134 A) = (term2134 A).
Proof. exact (eq_refl (term2134 A)). Qed.
Lemma lem5969856 {A B : Type'} (i : A) (j : B) : (term2135 A i) = (term2136 A B i j).
Proof. exact (MK_COMB (@lem5969855 A) (@lem5969851 A B i j)). Qed.
Lemma lem5969857 {A B : Type'} (i : A) (j : B) : (term2136 A B i j) = (term2132 A B i j).
Proof. exact (eq_refl (term2136 A B i j)). Qed.
Lemma lem5969858 {A : Type'} (i : A) : (term2137 A i) = (term2137 A i).
Proof. exact (eq_refl (term2137 A i)). Qed.
Lemma lem5969859 {A B : Type'} (i : A) (j : B) : ((term2135 A i) = (term2136 A B i j)) = ((term2135 A i) = (term2132 A B i j)).
Proof. exact (MK_COMB (@lem5969858 A i) (@lem5969857 A B i j)). Qed.
Lemma lem5969860 {A : Type'} (i : A) : (term2135 A i) = i.
Proof. exact (eq_refl (term2135 A i)). Qed.
Lemma lem5969861 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5969862 {A : Type'} (i : A) : (term2137 A i) = (@eq A i).
Proof. exact (MK_COMB (@lem5969861 A) (@lem5969860 A i)). Qed.
Lemma lem5969863 {A B : Type'} (i : A) (j : B) : (term2132 A B i j) = (term2132 A B i j).
Proof. exact (eq_refl (term2132 A B i j)). Qed.
Lemma lem5969864 {A B : Type'} (i : A) (j : B) : ((term2135 A i) = (term2132 A B i j)) = (i = (term2132 A B i j)).
Proof. exact (MK_COMB (@lem5969862 A i) (@lem5969863 A B i j)). Qed.
Lemma lem5969865 {A B : Type'} (i : A) (j : B) : ((term2135 A i) = (term2136 A B i j)) = (i = (term2132 A B i j)).
Proof. exact (TRANS (@lem5969859 A B i j) (@lem5969864 A B i j)). Qed.
Lemma lem5969866 {A B : Type'} (i : A) (j : B) : i = (term2132 A B i j).
Proof. exact (EQ_MP (@lem5969865 A B i j) (@lem5969856 A B i j)). Qed.
Lemma lem5969867 {A : Type'} (i : A) : (@eq A i) = (@eq A i).
Proof. exact (eq_refl (@eq A i)). Qed.
Lemma lem5969868 {A B : Type'} (i : A) (j : B) : (i = i) = (i = (term2132 A B i j)).
Proof. exact (MK_COMB (@lem5969867 A i) (@lem5969866 A B i j)). Qed.
Lemma lem5969869 {A B : Type'} (i : A) (j : B) : i = (term2132 A B i j).
Proof. exact (EQ_MP (@lem5969868 A B i j) (@lem5969854 A i)). Qed.
Lemma lem5969870 {B : Type'} (j : B) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem5969871 {B : Type'} : (term2134 B) = (term2134 B).
Proof. exact (eq_refl (term2134 B)). Qed.
Lemma lem5969872 {A B : Type'} (i : A) (j : B) : (term2135 B j) = (term2138 A B i j).
Proof. exact (MK_COMB (@lem5969871 B) (@lem5969853 A B i j)). Qed.
Lemma lem5969873 {A B : Type'} (i : A) (j : B) : (term2138 A B i j) = (term2133 A B i j).
Proof. exact (eq_refl (term2138 A B i j)). Qed.
Lemma lem5969874 {B : Type'} (j : B) : (term2137 B j) = (term2137 B j).
Proof. exact (eq_refl (term2137 B j)). Qed.
Lemma lem5969875 {A B : Type'} (i : A) (j : B) : ((term2135 B j) = (term2138 A B i j)) = ((term2135 B j) = (term2133 A B i j)).
Proof. exact (MK_COMB (@lem5969874 B j) (@lem5969873 A B i j)). Qed.
Lemma lem5969876 {B : Type'} (j : B) : (term2135 B j) = j.
Proof. exact (eq_refl (term2135 B j)). Qed.
Lemma lem5969877 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5969878 {B : Type'} (j : B) : (term2137 B j) = (@eq B j).
Proof. exact (MK_COMB (@lem5969877 B) (@lem5969876 B j)). Qed.
Lemma lem5969879 {A B : Type'} (i : A) (j : B) : (term2133 A B i j) = (term2133 A B i j).
Proof. exact (eq_refl (term2133 A B i j)). Qed.
Lemma lem5969880 {A B : Type'} (i : A) (j : B) : ((term2135 B j) = (term2133 A B i j)) = (j = (term2133 A B i j)).
Proof. exact (MK_COMB (@lem5969878 B j) (@lem5969879 A B i j)). Qed.
Lemma lem5969881 {A B : Type'} (i : A) (j : B) : ((term2135 B j) = (term2138 A B i j)) = (j = (term2133 A B i j)).
Proof. exact (TRANS (@lem5969875 A B i j) (@lem5969880 A B i j)). Qed.
Lemma lem5969882 {A B : Type'} (i : A) (j : B) : j = (term2133 A B i j).
Proof. exact (EQ_MP (@lem5969881 A B i j) (@lem5969872 A B i j)). Qed.
Lemma lem5969883 {B : Type'} (j : B) : (@eq B j) = (@eq B j).
Proof. exact (eq_refl (@eq B j)). Qed.
Lemma lem5969884 {A B : Type'} (i : A) (j : B) : (j = j) = (j = (term2133 A B i j)).
Proof. exact (MK_COMB (@lem5969883 B j) (@lem5969882 A B i j)). Qed.
Lemma lem5969885 {A B : Type'} (i : A) (j : B) : j = (term2133 A B i j).
Proof. exact (EQ_MP (@lem5969884 A B i j) (@lem5969870 B j)). Qed.
Lemma lem5969886 {A B C : Type'} (x' : type1412 A B C) : (term2139 A B C x') = (term2139 A B C x').
Proof. exact (eq_refl (term2139 A B C x')). Qed.
Lemma lem5969887 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2140 A B C x' i) = (term2141 A B C x' i j).
Proof. exact (MK_COMB (@lem5969886 A B C x') (@lem5969869 A B i j)). Qed.
Lemma lem5969888 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2141 A B C x' i j) = (term2142 A B C x' i j).
Proof. exact (eq_refl (term2141 A B C x' i j)). Qed.
Lemma lem5969889 {A B C : Type'} (x' : type1412 A B C) (i : A) : (term2143 A B C x' i) = (term2143 A B C x' i).
Proof. exact (eq_refl (term2143 A B C x' i)). Qed.
Lemma lem5969890 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : ((term2140 A B C x' i) = (term2141 A B C x' i j)) = ((term2140 A B C x' i) = (term2142 A B C x' i j)).
Proof. exact (MK_COMB (@lem5969889 A B C x' i) (@lem5969888 A B C x' i j)). Qed.
Lemma lem5969891 {A B C : Type'} (x' : type1412 A B C) (i : A) : (term2140 A B C x' i) = (term2144 A B C x' i).
Proof. exact (eq_refl (term2140 A B C x' i)). Qed.
Lemma lem5969892 {B C : Type'} : (@eq (B -> C)) = (@eq (B -> C)).
Proof. exact (eq_refl (@eq (B -> C))). Qed.
Lemma lem5969893 {A B C : Type'} (x' : type1412 A B C) (i : A) : (term2143 A B C x' i) = (term2145 A B C x' i).
Proof. exact (MK_COMB (@lem5969892 B C) (@lem5969891 A B C x' i)). Qed.
Lemma lem5969894 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2142 A B C x' i j) = (term2142 A B C x' i j).
Proof. exact (eq_refl (term2142 A B C x' i j)). Qed.
Lemma lem5969895 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : ((term2140 A B C x' i) = (term2142 A B C x' i j)) = ((term2144 A B C x' i) = (term2142 A B C x' i j)).
Proof. exact (MK_COMB (@lem5969893 A B C x' i) (@lem5969894 A B C x' i j)). Qed.
Lemma lem5969896 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : ((term2140 A B C x' i) = (term2141 A B C x' i j)) = ((term2144 A B C x' i) = (term2142 A B C x' i j)).
Proof. exact (TRANS (@lem5969890 A B C x' i j) (@lem5969895 A B C x' i j)). Qed.
Lemma lem5969897 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2144 A B C x' i) = (term2142 A B C x' i j).
Proof. exact (EQ_MP (@lem5969896 A B C x' i j) (@lem5969887 A B C x' i j)). Qed.
Lemma lem5969898 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2146 A B C x' i j) = (term2147 A B C x' i j).
Proof. exact (MK_COMB (@lem5969897 A B C x' i j) (@lem5969885 A B i j)). Qed.
Lemma lem5969899 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2147 A B C x' i j) = (term2148 A B C x' i j).
Proof. exact (eq_refl (term2147 A B C x' i j)). Qed.
Lemma lem5969900 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2149 A B C x' i j) = (term2149 A B C x' i j).
Proof. exact (eq_refl (term2149 A B C x' i j)). Qed.
Lemma lem5969901 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : ((term2146 A B C x' i j) = (term2147 A B C x' i j)) = ((term2146 A B C x' i j) = (term2148 A B C x' i j)).
Proof. exact (MK_COMB (@lem5969900 A B C x' i j) (@lem5969899 A B C x' i j)). Qed.
Lemma lem5969902 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2146 A B C x' i j) = (x' i j).
Proof. exact (eq_refl (term2146 A B C x' i j)). Qed.
Lemma lem5969903 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem5969904 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2149 A B C x' i j) = (term2150 A B C x' i j).
Proof. exact (MK_COMB (@lem5969903 C) (@lem5969902 A B C x' i j)). Qed.
Lemma lem5969905 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2148 A B C x' i j) = (term2148 A B C x' i j).
Proof. exact (eq_refl (term2148 A B C x' i j)). Qed.
Lemma lem5969906 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : ((term2146 A B C x' i j) = (term2148 A B C x' i j)) = ((x' i j) = (term2148 A B C x' i j)).
Proof. exact (MK_COMB (@lem5969904 A B C x' i j) (@lem5969905 A B C x' i j)). Qed.
Lemma lem5969907 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : ((term2146 A B C x' i j) = (term2147 A B C x' i j)) = ((x' i j) = (term2148 A B C x' i j)).
Proof. exact (TRANS (@lem5969901 A B C x' i j) (@lem5969906 A B C x' i j)). Qed.
Lemma lem5969908 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (x' i j) = (term2148 A B C x' i j).
Proof. exact (EQ_MP (@lem5969907 A B C x' i j) (@lem5969898 A B C x' i j)). Qed.
Lemma lem5969909 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2148 A B C x' i j) = (x' i j).
Proof. exact (SYM (@lem5969908 A B C x' i j)). Qed.
Lemma lem5969910 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2151 A B C x' i j) = (term2148 A B C x' i j).
Proof. exact (eq_refl (term2151 A B C x' i j)). Qed.
Lemma lem5969911 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2151 A B C x' i j) = (x' i j).
Proof. exact (TRANS (@lem5969910 A B C x' i j) (@lem5969909 A B C x' i j)). Qed.
Lemma lem5969912 {A B C : Type'} (x' : type1412 A B C) (i : A) : term2152 A B C x' i.
Proof. exact (fun j : B => @lem5969911 A B C x' i j). Qed.
Lemma lem5969913 {A B C : Type'} (x' : type1412 A B C) : term2153 A B C x'.
Proof. exact (fun i : A => @lem5969912 A B C x' i). Qed.
Lemma lem5969914 {A B C : Type'} (x' : type1412 A B C) : term2154 A B C x'.
Proof. exact (ex_intro (term2155 A B C x') (term2156 A B C x') (@lem5969913 A B C x')). Qed.
Lemma lem5969916 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem5969917 {C : Type'} (a : C) (b : C) : (a = b) = (@GEQ C a b).
Proof. exact (@lem5969916 C a b). Qed.
Lemma lem5969918 {A B C : Type'} (_75670 : type1209 A B C) (x' : type1412 A B C) (i : A) (j : B) : ((term2157 A B C _75670 i j) = (x' i j)) = (term1120 A B C _75670 x' i j).
Proof. exact (@lem5969917 C (term2157 A B C _75670 i j) (x' i j)). Qed.
Lemma lem5969919 {A B C : Type'} (_75670 : type1209 A B C) (x' : type1412 A B C) (i : A) : (term2158 A B C _75670 x' i) = (term1121 A B C _75670 x' i).
Proof. exact (fun_ext (fun j : B => @lem5969918 A B C _75670 x' i j)). Qed.
Lemma lem5969920 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5969921 {A B C : Type'} (_75670 : type1209 A B C) (x' : type1412 A B C) (i : A) : (term2159 A B C _75670 x' i) = (term1122 A B C _75670 x' i).
Proof. exact (MK_COMB (@lem5969920 B) (@lem5969919 A B C _75670 x' i)). Qed.
Lemma lem5969922 {A B C : Type'} (_75670 : type1209 A B C) (x' : type1412 A B C) : (term2160 A B C _75670 x') = (term1123 A B C _75670 x').
Proof. exact (fun_ext (fun i : A => @lem5969921 A B C _75670 x' i)). Qed.
Lemma lem5969923 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5969924 {A B C : Type'} (_75670 : type1209 A B C) (x' : type1412 A B C) : (term2161 A B C _75670 x') = (term1124 A B C _75670 x').
Proof. exact (MK_COMB (@lem5969923 A) (@lem5969922 A B C _75670 x')). Qed.
Lemma lem5969925 {A B C : Type'} (x' : type1412 A B C) : (term2155 A B C x') = (term1125 A B C x').
Proof. exact (fun_ext (fun _75670 : type1209 A B C => @lem5969924 A B C _75670 x')). Qed.
Lemma lem5969926 {A B C : Type'} : (@ex ((prod A B) -> C)) = (@ex ((prod A B) -> C)).
Proof. exact (eq_refl (@ex ((prod A B) -> C))). Qed.
Lemma lem5969927 {A B C : Type'} (x' : type1412 A B C) : (term2154 A B C x') = (term2162 A B C x').
Proof. exact (MK_COMB (@lem5969926 A B C) (@lem5969925 A B C x')). Qed.
Lemma lem5969928 {A B C : Type'} (x' : type1412 A B C) : term2162 A B C x'.
Proof. exact (EQ_MP (@lem5969927 A B C x') (@lem5969914 A B C x')). Qed.
Lemma lem5969930 {_5076 : Type'} (P : _5076 -> Prop) : term2163 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem5969931 {A B C : Type'} (P : type322 A B C) : term2164 A B C P.
Proof. exact (@lem5969930 (type1209 A B C) P). Qed.
Lemma lem5969932 {A B C : Type'} (x' : type1412 A B C) : term2165 A B C x'.
Proof. exact (@lem5969931 A B C (term1125 A B C x')). Qed.
Lemma lem5969933 {A B C : Type'} (x' : type1412 A B C) : term2166 A B C x'.
Proof. exact (@lem5969932 A B C x' (@lem5969928 A B C x')). Qed.
Lemma lem5969934 {A B C : Type'} (x' : type1412 A B C) : (term2166 A B C x') = (term2167 A B C x').
Proof. exact (eq_refl (term2166 A B C x')). Qed.
Lemma lem5969935 {A B C : Type'} (x' : type1412 A B C) : term2167 A B C x'.
Proof. exact (EQ_MP (@lem5969934 A B C x') (@lem5969933 A B C x')). Qed.
Lemma lem5969936 {A B C : Type'} (x' : type1412 A B C) (i : A) : term2168 A B C x' i.
Proof. exact (@lem5969935 A B C x' i). Qed.
Lemma lem5969937 {A B C : Type'} (x' : type1412 A B C) (i : A) : (term2168 A B C x' i) = (term2169 A B C x' i).
Proof. exact (eq_refl (term2168 A B C x' i)). Qed.
Lemma lem5969938 {A B C : Type'} (x' : type1412 A B C) (i : A) : term2169 A B C x' i.
Proof. exact (EQ_MP (@lem5969937 A B C x' i) (@lem5969936 A B C x' i)). Qed.
Lemma lem5969939 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : term2170 A B C x' i j.
Proof. exact (@lem5969938 A B C x' i j). Qed.
Lemma lem5969940 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2170 A B C x' i j) = (term2171 A B C x' i j).
Proof. exact (eq_refl (term2170 A B C x' i j)). Qed.
Lemma lem5969941 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : term2171 A B C x' i j.
Proof. exact (EQ_MP (@lem5969940 A B C x' i j) (@lem5969939 A B C x' i j)). Qed.
Lemma lem5969943 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem5969944 {C : Type'} (a : C) (b : C) : (@GEQ C a b) = (a = b).
Proof. exact (@lem5969943 C a b). Qed.
Lemma lem5969945 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2171 A B C x' i j) = ((term2131 A B C x' i j) = (x' i j)).
Proof. exact (@lem5969944 C (term2131 A B C x' i j) (x' i j)). Qed.
Lemma lem5969946 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2131 A B C x' i j) = (x' i j).
Proof. exact (EQ_MP (@lem5969945 A B C x' i j) (@lem5969941 A B C x' i j)). Qed.
Lemma lem5969947 {A B C : Type'} (x' : type1412 A B C) (i : A) (j : B) : (term2131 A B C x' i j) = (x' i j).
Proof. exact (@lem5969946 A B C x' i j). Qed.
Lemma lem5969948 {A B C : Type'} (x' : type1412 A B C) (x : A) (x'' : B) : (term2131 A B C x' x x'') = (x' x x'').
Proof. exact (@lem5969947 A B C x' x x''). Qed.
Lemma lem5969949 {A B C : Type'} (x' : type1412 A B C) (x : A) (x'' : B) : (term2130 A B C x' x x'') = (x' x x'').
Proof. exact (TRANS (@lem5969849 A B C x' x x'') (@lem5969948 A B C x' x x'')). Qed.
Lemma lem5969950 {A B C : Type'} (x' : type1412 A B C) (x : A) : (term2129 A B C x' x) = (term2144 A B C x' x).
Proof. exact (fun_ext (fun x'' : B => @lem5969949 A B C x' x x'')). Qed.
Lemma lem5969951 {A B C : Type'} (x' : type1412 A B C) (x : A) : (term2128 A B C x' x) = (term2144 A B C x' x).
Proof. exact (TRANS (@lem5969826 A B C x' x) (@lem5969950 A B C x' x)). Qed.
Lemma lem5969952 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : A) : (term2172 A B C op t x) = (term2172 A B C op t x).
Proof. exact (eq_refl (term2172 A B C op t x)). Qed.
Lemma lem5969953 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : (term2083 A B C op t x' x) = (term2173 A B C op t x' x).
Proof. exact (MK_COMB (@lem5969952 A B C op t x) (@lem5969951 A B C x' x)). Qed.
Lemma lem5969954 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : (term2174 A B C op t x' x) = (term2174 A B C op t x' x).
Proof. exact (eq_refl (term2174 A B C op t x' x)). Qed.
Lemma lem5969955 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : ((term818 A B C op t x' x) = (term2083 A B C op t x' x)) = ((term818 A B C op t x' x) = (term2173 A B C op t x' x)).
Proof. exact (MK_COMB (@lem5969954 A B C op t x' x) (@lem5969953 A B C op t x' x)). Qed.
Lemma lem5969958 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : ((term818 A B C op t x' x) = (term2173 A B C op t x' x)) = ((term818 A B C op t x' x) = (term2083 A B C op t x' x)).
Proof. exact (SYM (@lem5969955 A B C op t x' x)). Qed.
Lemma lem5969963 {B C : Type'} (t : B -> C) : (term1 B C t) = t.
Proof. exact (@lem5947362 B C t). Qed.
Lemma lem5969964 {A B C : Type'} (x' : type1412 A B C) (x : A) : (term2144 A B C x' x) = (x' x).
Proof. exact (@lem5969963 B C (x' x)). Qed.
Lemma lem5969965 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : A) : (term2172 A B C op t x) = (term2172 A B C op t x).
Proof. exact (eq_refl (term2172 A B C op t x)). Qed.
Lemma lem5969966 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : (term2173 A B C op t x' x) = (term818 A B C op t x' x).
Proof. exact (MK_COMB (@lem5969965 A B C op t x) (@lem5969964 A B C x' x)). Qed.
Lemma lem5969967 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : (term2174 A B C op t x' x) = (term2174 A B C op t x' x).
Proof. exact (eq_refl (term2174 A B C op t x' x)). Qed.
Lemma lem5969968 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : ((term818 A B C op t x' x) = (term2173 A B C op t x' x)) = ((term818 A B C op t x' x) = (term818 A B C op t x' x)).
Proof. exact (MK_COMB (@lem5969967 A B C op t x' x) (@lem5969966 A B C op t x' x)). Qed.
Lemma lem5969970 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5969971 {C : Type'} (x : C) : (x = x) = True.
Proof. exact (@lem5969970 C x). Qed.
Lemma lem5969972 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : ((term818 A B C op t x' x) = (term818 A B C op t x' x)) = True.
Proof. exact (@lem5969971 C (term818 A B C op t x' x)). Qed.
Lemma lem5969973 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : ((term818 A B C op t x' x) = (term2173 A B C op t x' x)) = True.
Proof. exact (TRANS (@lem5969968 A B C op t x' x) (@lem5969972 A B C op t x' x)). Qed.
Lemma lem5969974 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : True = ((term818 A B C op t x' x) = (term2173 A B C op t x' x)).
Proof. exact (SYM (@lem5969973 A B C op t x' x)). Qed.
Lemma lem5969976 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : (term818 A B C op t x' x) = (term2173 A B C op t x' x).
Proof. exact (EQ_MP (@lem5969974 A B C op t x' x) (@lem0)). Qed.
Lemma lem5969977 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) : (term818 A B C op t x' x) = (term2083 A B C op t x' x).
Proof. exact (EQ_MP (@lem5969958 A B C op t x' x) (@lem5969976 A B C op t x' x)). Qed.
Lemma lem5969978 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x' : type1412 A B C) (x : A) (h1 : (term2082 A B C op t x x') = (term2083 A B C op t x' x)) : (term818 A B C op t x' x) = (term2082 A B C op t x x').
Proof. exact (EQ_MP (@lem5969820 A B C op t x' x h1) (@lem5969977 A B C op t x' x)). Qed.
Lemma lem5969979 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : A) (x' : type1412 A B C) : term2175 A B C op t x x'.
Proof. exact (fun h0 : (term2082 A B C op t x x') = (term2083 A B C op t x' x) => @lem5969978 A B C op t x' x h0). Qed.
Lemma lem5969980 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : A) (x' : type1412 A B C) : term2176 A B C op t x x'.
Proof. exact (conj (@lem5969806 A B t x) (@lem5969979 A B C op t x x')). Qed.
Lemma lem5969981 {A B C : Type'} (op : type1400 C) (t : type1413 A B) (x : A) (x' : type1412 A B C) : term2177 A B C op t x x'.
Proof. exact (@lem5969300 A B C op t x x' (@lem5969980 A B C op t x x')). Qed.
Lemma lem5969982 {A B C : Type'} (t : type1413 A B) (x : A) (x' : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term818 A B C op t x' x) = (term2082 A B C op t x x').
Proof. exact (@lem5969981 A B C op t x x' (@lem5969297 A B C t x' x op h1)). Qed.
Lemma lem5969983 {A B C : Type'} (t : type1413 A B) (x : A) (x' : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term823 A B C op t x' x) = (term2178 A B C op t x x').
Proof. exact (MK_COMB (@lem5969257 C op) (@lem5969982 A B C t x x' op h1)). Qed.
Lemma lem5969984 {A B C : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term914 A B C x op s t x') = (term946 A B C x op s t x').
Proof. exact (MK_COMB (@lem5969983 A B C t x x' op h1) (@lem5969256 A B C op s t x')). Qed.
Lemma lem5969985 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) (h1 : @monoidal C op) (h2 : (term853 A B C op x s t x') = (term946 A B C x op s t x')) : (term914 A B C x op s t x') = (term853 A B C op x s t x').
Proof. exact (EQ_MP (@lem5969255 A B C x op s t x' h2) (@lem5969984 A B C x s t x' op h1)). Qed.
Lemma lem5969986 {A B C : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term2179 A B C op x s t x'.
Proof. exact (fun h0 : (term853 A B C op x s t x') = (term946 A B C x op s t x') => @lem5969985 A B C x op s t x' h1 h0). Qed.
Lemma lem5969987 {A B C : Type'} (x' : type1412 A B C) (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term782 A x s) : term2180 A B C op x s t x'.
Proof. exact (conj (@lem5969241 A B C t op x s h1 h2 h3 h4 h5) (@lem5969986 A B C x s t x' op h4)). Qed.
Lemma lem5969988 {A B C : Type'} (x' : type1412 A B C) (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term782 A x s) : term2181 A B C op x s t x'.
Proof. exact (@lem5961474 A B C op x s t x' (@lem5969987 A B C x' t op x s h1 h2 h3 h4 h5)). Qed.
Lemma lem5969989 {A B C : Type'} (x' : type1412 A B C) (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term782 A x s) : (term914 A B C x op s t x') = (term853 A B C op x s t x').
Proof. exact (@lem5969988 A B C x' t op x s h1 h2 h3 h4 h5 (@lem5961471 A B C x s t x' op h4)). Qed.
Lemma lem5969994 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term782 A x s) : term917 A B C op x s t.
Proof. exact (fun x' : type1412 A B C => @lem5969989 A B C x' t op x s h1 h2 h3 h4 h5). Qed.
Lemma lem5969995 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term782 A x s) : (term895 A B x s t) = (term917 A B C op x s t).
Proof. exact (prop_ext (fun h6 : term895 A B x s t => @lem5969994 A B C t op x s h1 h2 h3 h4 h5) (fun h6 : term917 A B C op x s t => @lem5961431 A B x s t h1)). Qed.
Lemma lem5969996 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term895 A B x s t) (h2 : term649 A B C op s) (h3 : @FINITE A s) (h4 : @monoidal C op) (h5 : term782 A x s) : term917 A B C op x s t.
Proof. exact (EQ_MP (@lem5969995 A B C t op x s h1 h2 h3 h4 h5) (@lem5961431 A B x s t h1)). Qed.
Lemma lem5969997 {A B C : Type'} (t : type1413 A B) (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term782 A x s) : term920 A B C op x s t.
Proof. exact (fun h0 : term895 A B x s t => @lem5969996 A B C t op x s h0 h1 h2 h3 h4). Qed.
Lemma lem5970002 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term782 A x s) : term922 A B C op x s.
Proof. exact (fun t : type1413 A B => @lem5969997 A B C t op x s h1 h2 h3 h4). Qed.
Lemma lem5970003 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : term664 A x s.
Proof. exact (proj2 (@lem5961426 A B C op x s h1)). Qed.
Lemma lem5970004 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term666 A B C op x s) : term649 A B C op s.
Proof. exact (proj1 (@lem5961426 A B C op x s h1)). Qed.
Lemma lem5970005 {A : Type'} (x : A) (s : A -> Prop) (h1 : term664 A x s) : @FINITE A s.
Proof. exact (proj2 (@lem5961427 A x s h1)). Qed.
Lemma lem5970006 {A : Type'} (x : A) (s : A -> Prop) (h1 : term664 A x s) : term782 A x s.
Proof. exact (proj1 (@lem5961427 A x s h1)). Qed.
Lemma lem5970007 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term782 A x s) : (@FINITE A s) = (term922 A B C op x s).
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem5970002 A B C op x s h1 h2 h3 h4) (fun h5 : term922 A B C op x s => @lem5961429 A s h2)). Qed.
Lemma lem5970008 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term782 A x s) : term922 A B C op x s.
Proof. exact (EQ_MP (@lem5970007 A B C op x s h1 h2 h3 h4) (@lem5961429 A s h2)). Qed.
Lemma lem5970009 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term782 A x s) : (term782 A x s) = (term922 A B C op x s).
Proof. exact (prop_ext (fun h5 : term782 A x s => @lem5970008 A B C op x s h1 h2 h3 h4) (fun h5 : term922 A B C op x s => @lem5961430 A x s h4)). Qed.
Lemma lem5970010 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @FINITE A s) (h3 : @monoidal C op) (h4 : term782 A x s) : term922 A B C op x s.
Proof. exact (EQ_MP (@lem5970009 A B C op x s h1 h2 h3 h4) (@lem5961430 A x s h4)). Qed.
Lemma lem5970011 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @monoidal C op) (h3 : term782 A x s) (h4 : term664 A x s) : (@FINITE A s) = (term922 A B C op x s).
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem5970010 A B C op x s h1 h5 h2 h3) (fun h5 : term922 A B C op x s => @lem5970005 A x s h4)). Qed.
Lemma lem5970012 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @monoidal C op) (h3 : term782 A x s) (h4 : term664 A x s) : term922 A B C op x s.
Proof. exact (EQ_MP (@lem5970011 A B C op x s h1 h2 h3 h4) (@lem5970005 A x s h4)). Qed.
Lemma lem5970013 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @monoidal C op) (h3 : term664 A x s) : (term782 A x s) = (term922 A B C op x s).
Proof. exact (prop_ext (fun h4 : term782 A x s => @lem5970012 A B C op x s h1 h2 h4 h3) (fun h4 : term922 A B C op x s => @lem5970006 A x s h3)). Qed.
Lemma lem5970014 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @monoidal C op) (h3 : term664 A x s) : term922 A B C op x s.
Proof. exact (EQ_MP (@lem5970013 A B C op x s h1 h2 h3) (@lem5970006 A x s h3)). Qed.
Lemma lem5970015 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @monoidal C op) (h3 : term664 A x s) : (term649 A B C op s) = (term922 A B C op x s).
Proof. exact (prop_ext (fun h4 : term649 A B C op s => @lem5970014 A B C op x s h1 h2 h3) (fun h4 : term922 A B C op x s => @lem5961428 A B C op s h1)). Qed.
Lemma lem5970016 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @monoidal C op) (h3 : term664 A x s) : term922 A B C op x s.
Proof. exact (EQ_MP (@lem5970015 A B C op x s h1 h2 h3) (@lem5961428 A B C op s h1)). Qed.
Lemma lem5970017 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @monoidal C op) (h3 : term666 A B C op x s) : (term664 A x s) = (term922 A B C op x s).
Proof. exact (prop_ext (fun h4 : term664 A x s => @lem5970016 A B C op x s h1 h2 h4) (fun h4 : term922 A B C op x s => @lem5970003 A B C op x s h3)). Qed.
Lemma lem5970018 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : term649 A B C op s) (h2 : @monoidal C op) (h3 : term666 A B C op x s) : term922 A B C op x s.
Proof. exact (EQ_MP (@lem5970017 A B C op x s h1 h2 h3) (@lem5970003 A B C op x s h3)). Qed.
Lemma lem5970019 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x s) : (term649 A B C op s) = (term922 A B C op x s).
Proof. exact (prop_ext (fun h3 : term649 A B C op s => @lem5970018 A B C op x s h3 h1 h2) (fun h3 : term922 A B C op x s => @lem5970004 A B C op x s h2)). Qed.
Lemma lem5970020 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term666 A B C op x s) : term922 A B C op x s.
Proof. exact (EQ_MP (@lem5970019 A B C op x s h1 h2) (@lem5970004 A B C op x s h2)). Qed.
Lemma lem5970021 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term925 A B C op x s.
Proof. exact (fun h0 : term666 A B C op x s => @lem5970020 A B C op x s h1 h0). Qed.
Lemma lem5970026 {A B C : Type'} (x : A) (op : type1400 C) (h1 : @monoidal C op) : term927 A B C op x.
Proof. exact (fun s : A -> Prop => @lem5970021 A B C x s op h1). Qed.
Lemma lem5970031 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term929 A B C op.
Proof. exact (fun x : A => @lem5970026 A B C x op h1). Qed.
Lemma lem5970032 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term864 A B C op.
Proof. exact (EQ_MP (@lem5961425 A B C op) (@lem5970031 A B C op h1)). Qed.
Lemma lem5970033 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term847 A B C op.
Proof. exact (EQ_MP (@lem5956603 A B C op) (@lem5970032 A B C op h1)). Qed.
Lemma lem5970034 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term682 A B C op.
Proof. exact (EQ_MP (@lem5956468 A B C op h1) (@lem5970033 A B C op h1)). Qed.
Lemma lem5970035 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term654 A B C op.
Proof. exact (@lem5950700 A B C op (@lem5970034 A B C op h1)). Qed.
Lemma lem5970036 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term653 A B C op.
Proof. exact (EQ_MP (@lem5950667 A B C op) (@lem5970035 A B C op h1)). Qed.
Lemma lem5970037 {A B C : Type'} (op : type1400 C) : term2182 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem5970036 A B C op h0). Qed.
Lemma lem5970042 {A B C : Type'} : term2183 A B C.
Proof. exact (fun op : type1400 C => @lem5970037 A B C op). Qed.
