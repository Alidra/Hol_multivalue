Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARTESIAN_PRODUCT_EQ_EMPTY_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import EXTENSIONAL_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import SKOLEM_THM_spec.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
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
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18934_spec.
Require Import thm18935_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184714_spec.
Require Import thm3184717_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4406358 {_83152 : Type'} : term0 _83152.
Proof. exact (EQ_MP (@lem3184717 _83152) (@lem3184714 _83152)). Qed.
Lemma lem4406359 {_83152 : Type'} (p : _83152 -> Prop) : term1 _83152 p.
Proof. exact (@lem4406358 _83152 p). Qed.
Lemma lem4406360 {_83152 : Type'} (p : _83152 -> Prop) : (term1 _83152 p) = (term2 _83152 p).
Proof. exact (eq_refl (term1 _83152 p)). Qed.
Lemma lem4406361 {_83152 : Type'} (p : _83152 -> Prop) : term2 _83152 p.
Proof. exact (EQ_MP (@lem4406360 _83152 p) (@lem4406359 _83152 p)). Qed.
Lemma lem4406362 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term3 _83152 p x.
Proof. exact (@lem4406361 _83152 p x). Qed.
Lemma lem4406363 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term3 _83152 p x) = ((term4 _83152 p x) = (p x)).
Proof. exact (eq_refl (term3 _83152 p x)). Qed.
Lemma lem4406386 {A B : Type'} (s : A -> Prop) : term5 A B s.
Proof. exact (@lem4382798 A B s). Qed.
Lemma lem4406387 {A B : Type'} (s : A -> Prop) : (term5 A B s) = ((@EXTENSIONAL A B s) = (term6 A B s)).
Proof. exact (eq_refl (term5 A B s)). Qed.
Lemma lem4406389 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4406390 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem4406391 {A : Type'} (x : A) : term8 A x.
Proof. exact (EQ_MP (@lem4406390 A x) (@lem4406389 A x)). Qed.
Lemma lem4406392 {A : Type'} (x : A) : term9 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4406418 {_83095 : Type'} : term10 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4406419 {_83095 : Type'} (p : _83095 -> Prop) : term11 _83095 p.
Proof. exact (@lem4406418 _83095 p). Qed.
Lemma lem4406420 {_83095 : Type'} (p : _83095 -> Prop) : (term11 _83095 p) = (term12 _83095 p).
Proof. exact (eq_refl (term11 _83095 p)). Qed.
Lemma lem4406421 {_83095 : Type'} (p : _83095 -> Prop) : term12 _83095 p.
Proof. exact (EQ_MP (@lem4406420 _83095 p) (@lem4406419 _83095 p)). Qed.
Lemma lem4406422 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term13 _83095 p x.
Proof. exact (@lem4406421 _83095 p x). Qed.
Lemma lem4406423 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term13 _83095 p x) = ((term14 _83095 x p) = (p x)).
Proof. exact (eq_refl (term13 _83095 p x)). Qed.
Lemma lem4406432 {A K : Type'} (k : K -> Prop) : term15 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4406433 {A K : Type'} (k : K -> Prop) : (term15 A K k) = (term16 A K k).
Proof. exact (eq_refl (term15 A K k)). Qed.
Lemma lem4406434 {A K : Type'} (k : K -> Prop) : term16 A K k.
Proof. exact (EQ_MP (@lem4406433 A K k) (@lem4406432 A K k)). Qed.
Lemma lem4406435 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term17 A K k s.
Proof. exact (@lem4406434 A K k s). Qed.
Lemma lem4406436 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term17 A K k s) = ((@cartesian_product A K k s) = (term18 A K k s)).
Proof. exact (eq_refl (term17 A K k s)). Qed.
Lemma lem4406438 {A : Type'} (P : A -> Prop) : term19 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem4406439 {A : Type'} (P : A -> Prop) : (term19 A P) = ((term20 A P) = (term21 A P)).
Proof. exact (eq_refl (term19 A P)). Qed.
Lemma lem4406441 {A B : Type'} (P : type1413 A B) : term22 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem4406442 {A B : Type'} (P : type1413 A B) : (term22 A B P) = ((term23 A B P) = (term24 A B P)).
Proof. exact (eq_refl (term22 A B P)). Qed.
Lemma lem4406467 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term25 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4406468 {_106013 : Type'} (s : _106013 -> Prop) (t : _106013 -> Prop) : (s = t) = (term25 _106013 s t).
Proof. exact (@lem4406467 _106013 s t). Qed.
Lemma lem4406469 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : ((s i) = (@EMPTY _106013)) = (term26 _106013 _106031 s i).
Proof. exact (@lem4406468 _106013 (s i) (@EMPTY _106013)). Qed.
Lemma lem4406478 {_106031 : Type'} (i : _106031) (k : _106031 -> Prop) : (term27 _106031 i k) = (term27 _106031 i k).
Proof. exact (eq_refl (term27 _106031 i k)). Qed.
Lemma lem4406479 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term28 _106013 _106031 k s i) = (term29 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406478 _106031 i k) (@lem4406469 _106013 _106031 s i)). Qed.
Lemma lem4406482 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term30 _106013 _106031 k s) = (term31 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4406479 _106013 _106031 k s i)). Qed.
Lemma lem4406483 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4406484 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term32 _106013 _106031 k s) = (term33 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406483 _106031) (@lem4406482 _106013 _106031 k s)). Qed.
Lemma lem4406489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4406490 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term34 _106013 _106031 k s) = (term35 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406489) (@lem4406484 _106013 _106031 k s)). Qed.
Lemma lem4406501 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term36 _106013 _106031 k s) = (term36 _106013 _106031 k s).
Proof. exact (eq_refl (term36 _106013 _106031 k s)). Qed.
Lemma lem4406502 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term32 _106013 _106031 k s) = (term36 _106013 _106031 k s)) = ((term33 _106013 _106031 k s) = (term36 _106013 _106031 k s)).
Proof. exact (MK_COMB (@lem4406490 _106013 _106031 k s) (@lem4406501 _106013 _106031 k s)). Qed.
Lemma lem4406507 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term33 _106013 _106031 k s) = (term36 _106013 _106031 k s)) = ((term32 _106013 _106031 k s) = (term36 _106013 _106031 k s)).
Proof. exact (SYM (@lem4406502 _106013 _106031 k s)). Qed.
Lemma lem4406517 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4406518 {_106031 : Type'} (P : _106031 -> Prop) (x : _106031) : (@IN _106031 x P) = (P x).
Proof. exact (@lem4406517 _106031 P x). Qed.
Lemma lem4406519 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (@IN _106031 i k) = (k i).
Proof. exact (@lem4406518 _106031 k i). Qed.
Lemma lem4406520 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4406521 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term27 _106031 i k) = (term37 _106031 k i).
Proof. exact (MK_COMB (@lem4406520) (@lem4406519 _106031 k i)). Qed.
Lemma lem4406529 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4406530 {_106013 : Type'} (P : _106013 -> Prop) (x : _106013) : (@IN _106013 x P) = (P x).
Proof. exact (@lem4406529 _106013 P x). Qed.
Lemma lem4406531 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term38 _106013 _106031 x s i) = (s i x).
Proof. exact (@lem4406530 _106013 (s i) x). Qed.
Lemma lem4406532 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4406533 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term39 _106013 _106031 x s i) = (term40 _106013 _106031 s i x).
Proof. exact (MK_COMB (@lem4406532) (@lem4406531 _106013 _106031 s i x)). Qed.
Lemma lem4406535 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4406536 {_106013 : Type'} (x : _106013) : (@IN _106013 x (@EMPTY _106013)) = False.
Proof. exact (@lem4406535 _106013 x). Qed.
Lemma lem4406537 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : ((term38 _106013 _106031 x s i) = (@IN _106013 x (@EMPTY _106013))) = ((s i x) = False).
Proof. exact (MK_COMB (@lem4406533 _106013 _106031 s i x) (@lem4406536 _106013 x)). Qed.
Lemma lem4406539 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4406540 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : ((s i x) = False) = (term41 _106013 _106031 s i x).
Proof. exact (@lem4406539 (s i x)). Qed.
Lemma lem4406541 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : ((term38 _106013 _106031 x s i) = (@IN _106013 x (@EMPTY _106013))) = (term41 _106013 _106031 s i x).
Proof. exact (TRANS (@lem4406537 _106013 _106031 s i x) (@lem4406540 _106013 _106031 s i x)). Qed.
Lemma lem4406542 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term42 _106013 _106031 s i) = (term43 _106013 _106031 s i).
Proof. exact (fun_ext (fun x : _106013 => @lem4406541 _106013 _106031 s i x)). Qed.
Lemma lem4406543 {_106013 : Type'} : (@all _106013) = (@all _106013).
Proof. exact (eq_refl (@all _106013)). Qed.
Lemma lem4406544 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term26 _106013 _106031 s i) = (term44 _106013 _106031 s i).
Proof. exact (MK_COMB (@lem4406543 _106013) (@lem4406542 _106013 _106031 s i)). Qed.
Lemma lem4406549 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term29 _106013 _106031 k s i) = (term45 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406521 _106031 k i) (@lem4406544 _106013 _106031 s i)). Qed.
Lemma lem4406552 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term31 _106013 _106031 k s) = (term46 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4406549 _106013 _106031 k s i)). Qed.
Lemma lem4406553 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4406554 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term33 _106013 _106031 k s) = (term47 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406553 _106031) (@lem4406552 _106013 _106031 k s)). Qed.
Lemma lem4406559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4406560 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term35 _106013 _106031 k s) = (term48 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406559) (@lem4406554 _106013 _106031 k s)). Qed.
Lemma lem4406572 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4406573 {_106031 : Type'} (P : _106031 -> Prop) (x : _106031) : (@IN _106031 x P) = (P x).
Proof. exact (@lem4406572 _106031 P x). Qed.
Lemma lem4406574 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (@IN _106031 i k) = (k i).
Proof. exact (@lem4406573 _106031 k i). Qed.
Lemma lem4406575 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4406576 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term49 _106031 i k) = (term50 _106031 k i).
Proof. exact (MK_COMB (@lem4406575) (@lem4406574 _106031 k i)). Qed.
Lemma lem4406578 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4406579 {_106013 : Type'} (P : _106013 -> Prop) (x : _106013) : (@IN _106013 x P) = (P x).
Proof. exact (@lem4406578 _106013 P x). Qed.
Lemma lem4406580 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term38 _106013 _106031 a s i) = (s i a).
Proof. exact (@lem4406579 _106013 (s i) a). Qed.
Lemma lem4406581 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term51 _106013 _106031 k a s i) = (term52 _106013 _106031 k s i a).
Proof. exact (MK_COMB (@lem4406576 _106031 k i) (@lem4406580 _106013 _106031 s i a)). Qed.
Lemma lem4406584 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term53 _106013 _106031 k s i) = (term54 _106013 _106031 k s i).
Proof. exact (fun_ext (fun a : _106013 => @lem4406581 _106013 _106031 k s i a)). Qed.
Lemma lem4406585 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4406586 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term55 _106013 _106031 k s i) = (term56 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406585 _106013) (@lem4406584 _106013 _106031 k s i)). Qed.
Lemma lem4406591 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term57 _106013 _106031 k s) = (term58 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4406586 _106013 _106031 k s i)). Qed.
Lemma lem4406592 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4406593 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term59 _106013 _106031 k s) = (term60 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406592 _106031) (@lem4406591 _106013 _106031 k s)). Qed.
Lemma lem4406598 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4406599 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term36 _106013 _106031 k s) = (term61 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406598) (@lem4406593 _106013 _106031 k s)). Qed.
Lemma lem4406600 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term33 _106013 _106031 k s) = (term36 _106013 _106031 k s)) = ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s)).
Proof. exact (MK_COMB (@lem4406560 _106013 _106031 k s) (@lem4406599 _106013 _106031 k s)). Qed.
Lemma lem4406603 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s)) = ((term33 _106013 _106031 k s) = (term36 _106013 _106031 k s)).
Proof. exact (SYM (@lem4406600 _106013 _106031 k s)). Qed.
Lemma lem4406605 (p : Prop) : p = (term62 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4406606 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s)) = (term63 _106013 _106031 k s).
Proof. exact (@lem4406605 ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s))). Qed.
Lemma lem4406607 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term63 _106013 _106031 k s) = ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s)).
Proof. exact (SYM (@lem4406606 _106013 _106031 k s)). Qed.
Lemma lem4406608 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term64 _106013 _106031 k s) : term64 _106013 _106031 k s.
Proof. exact (h1). Qed.
Lemma lem4406611 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term63 _106013 _106031 k s) : term63 _106013 _106031 k s.
Proof. exact (h1). Qed.
Lemma lem4406612 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : term65 _106013 _106031 k s.
Proof. exact (fun h0 : term63 _106013 _106031 k s => @lem4406611 _106013 _106031 k s h0). Qed.
Lemma lem4406613 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term65 _106013 _106031 k s) : term65 _106013 _106031 k s.
Proof. exact (h1). Qed.
Lemma lem4406614 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term63 _106013 _106031 k s) : term63 _106013 _106031 k s.
Proof. exact (h1). Qed.
Lemma lem4406615 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term63 _106013 _106031 k s) (h2 : term65 _106013 _106031 k s) : term63 _106013 _106031 k s.
Proof. exact (@lem4406613 _106013 _106031 k s h2 (@lem4406614 _106013 _106031 k s h1)). Qed.
Lemma lem4406616 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term63 _106013 _106031 k s) : term66 _106013 _106031 k s.
Proof. exact (fun h0 : term65 _106013 _106031 k s => @lem4406615 _106013 _106031 k s h1 h0). Qed.
Lemma lem4406617 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term65 _106013 _106031 k s) : term65 _106013 _106031 k s.
Proof. exact (h1). Qed.
Lemma lem4406618 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term63 _106013 _106031 k s) (h2 : term65 _106013 _106031 k s) : term63 _106013 _106031 k s.
Proof. exact (@lem4406616 _106013 _106031 k s h1 (@lem4406617 _106013 _106031 k s h2)). Qed.
Lemma lem4406619 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term65 _106013 _106031 k s) : term65 _106013 _106031 k s.
Proof. exact (fun h0 : term63 _106013 _106031 k s => @lem4406618 _106013 _106031 k s h0 h1). Qed.
Lemma lem4406620 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : term67 _106013 _106031 k s.
Proof. exact (fun h0 : term65 _106013 _106031 k s => @lem4406619 _106013 _106031 k s h0). Qed.
Lemma lem4406623 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : term65 _106013 _106031 k s.
Proof. exact (@lem4406620 _106013 _106031 k s (@lem4406612 _106013 _106031 k s)). Qed.
Lemma lem4406624 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : term65 _106013 _106031 k s.
Proof. exact (@lem4406623 _106013 _106031 k s). Qed.
Lemma lem4406634 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4406635 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term63 _106013 _106031 k s) = (term68 _106013 _106031 k s).
Proof. exact (@lem4406634 (term64 _106013 _106031 k s)). Qed.
Lemma lem4406637 (t : Prop) : (term69 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4406638 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term68 _106013 _106031 k s) = ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s)).
Proof. exact (@lem4406637 ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s))). Qed.
Lemma lem4406639 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term63 _106013 _106031 k s) = ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s)).
Proof. exact (TRANS (@lem4406635 _106013 _106031 k s) (@lem4406638 _106013 _106031 k s)). Qed.
Lemma lem4406684 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) : (term70 _106013 _106031 s) = (term71 _106013 _106031 s).
Proof. exact (fun_ext (fun k : _106031 -> Prop => @lem4406639 _106013 _106031 k s)). Qed.
Lemma lem4406685 {_106031 : Type'} : (@all (_106031 -> Prop)) = (@all (_106031 -> Prop)).
Proof. exact (eq_refl (@all (_106031 -> Prop))). Qed.
Lemma lem4406686 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) : (term72 _106013 _106031 s) = (term73 _106013 _106031 s).
Proof. exact (MK_COMB (@lem4406685 _106031) (@lem4406684 _106013 _106031 s)). Qed.
Lemma lem4406691 {_106013 _106031 : Type'} : (term74 _106013 _106031) = (term75 _106013 _106031).
Proof. exact (fun_ext (fun s : type1470 _106013 _106031 => @lem4406686 _106013 _106031 s)). Qed.
Lemma lem4406692 {_106013 _106031 : Type'} : (@all (_106031 -> _106013 -> Prop)) = (@all (_106031 -> _106013 -> Prop)).
Proof. exact (eq_refl (@all (_106031 -> _106013 -> Prop))). Qed.
Lemma lem4406701 {_106013 _106031 : Type'} : (term76 _106013 _106031) = (term77 _106013 _106031).
Proof. exact (MK_COMB (@lem4406692 _106013 _106031) (@lem4406691 _106013 _106031)). Qed.
Lemma lem4406706 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term52 _106013 _106031 k s i a) = (term52 _106013 _106031 k s i a).
Proof. exact (eq_refl (term52 _106013 _106031 k s i a)). Qed.
Lemma lem4406707 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term54 _106013 _106031 k s i) = (term54 _106013 _106031 k s i).
Proof. exact (fun_ext (fun a : _106013 => @lem4406706 _106013 _106031 k s i a)). Qed.
Lemma lem4406708 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4406709 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term56 _106013 _106031 k s i) = (term56 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406708 _106013) (@lem4406707 _106013 _106031 k s i)). Qed.
Lemma lem4406710 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term58 _106013 _106031 k s) = (term58 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4406709 _106013 _106031 k s i)). Qed.
Lemma lem4406711 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4406712 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term60 _106013 _106031 k s) = (term60 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406711 _106031) (@lem4406710 _106013 _106031 k s)). Qed.
Lemma lem4406713 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4406714 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term61 _106013 _106031 k s) = (term61 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406713) (@lem4406712 _106013 _106031 k s)). Qed.
Lemma lem4406717 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term41 _106013 _106031 s i x) = (term41 _106013 _106031 s i x).
Proof. exact (eq_refl (term41 _106013 _106031 s i x)). Qed.
Lemma lem4406718 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term43 _106013 _106031 s i) = (term43 _106013 _106031 s i).
Proof. exact (fun_ext (fun x : _106013 => @lem4406717 _106013 _106031 s i x)). Qed.
Lemma lem4406719 {_106013 : Type'} : (@all _106013) = (@all _106013).
Proof. exact (eq_refl (@all _106013)). Qed.
Lemma lem4406720 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term44 _106013 _106031 s i) = (term44 _106013 _106031 s i).
Proof. exact (MK_COMB (@lem4406719 _106013) (@lem4406718 _106013 _106031 s i)). Qed.
Lemma lem4406723 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term37 _106031 k i) = (term37 _106031 k i).
Proof. exact (eq_refl (term37 _106031 k i)). Qed.
Lemma lem4406724 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term45 _106013 _106031 k s i) = (term45 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406723 _106031 k i) (@lem4406720 _106013 _106031 s i)). Qed.
Lemma lem4406725 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term46 _106013 _106031 k s) = (term46 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4406724 _106013 _106031 k s i)). Qed.
Lemma lem4406726 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4406727 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term47 _106013 _106031 k s) = (term47 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406726 _106031) (@lem4406725 _106013 _106031 k s)). Qed.
Lemma lem4406728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4406729 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term48 _106013 _106031 k s) = (term48 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406728) (@lem4406727 _106013 _106031 k s)). Qed.
Lemma lem4406730 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s)) = ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s)).
Proof. exact (MK_COMB (@lem4406729 _106013 _106031 k s) (@lem4406714 _106013 _106031 k s)). Qed.
Lemma lem4406731 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) : (term71 _106013 _106031 s) = (term71 _106013 _106031 s).
Proof. exact (fun_ext (fun k : _106031 -> Prop => @lem4406730 _106013 _106031 k s)). Qed.
Lemma lem4406732 {_106031 : Type'} : (@all (_106031 -> Prop)) = (@all (_106031 -> Prop)).
Proof. exact (eq_refl (@all (_106031 -> Prop))). Qed.
Lemma lem4406733 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) : (term73 _106013 _106031 s) = (term73 _106013 _106031 s).
Proof. exact (MK_COMB (@lem4406732 _106031) (@lem4406731 _106013 _106031 s)). Qed.
Lemma lem4406734 {_106013 _106031 : Type'} : (term75 _106013 _106031) = (term75 _106013 _106031).
Proof. exact (fun_ext (fun s : type1470 _106013 _106031 => @lem4406733 _106013 _106031 s)). Qed.
Lemma lem4406735 {_106013 _106031 : Type'} : (@all (_106031 -> _106013 -> Prop)) = (@all (_106031 -> _106013 -> Prop)).
Proof. exact (eq_refl (@all (_106031 -> _106013 -> Prop))). Qed.
Lemma lem4406736 {_106013 _106031 : Type'} : (term77 _106013 _106031) = (term77 _106013 _106031).
Proof. exact (MK_COMB (@lem4406735 _106013 _106031) (@lem4406734 _106013 _106031)). Qed.
Lemma lem4406779 {_106013 _106031 : Type'} : (term76 _106013 _106031) = (term77 _106013 _106031).
Proof. exact (TRANS (@lem4406701 _106013 _106031) (@lem4406736 _106013 _106031)). Qed.
Lemma lem4406780 {_106013 _106031 : Type'} : (term77 _106013 _106031) = (term76 _106013 _106031).
Proof. exact (SYM (@lem4406779 _106013 _106031)). Qed.
Lemma lem4406782 (p : Prop) : p = (term62 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4406783 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s)) = (term63 _106013 _106031 k s).
Proof. exact (@lem4406782 ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s))). Qed.
Lemma lem4406784 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term63 _106013 _106031 k s) = ((term47 _106013 _106031 k s) = (term61 _106013 _106031 k s)).
Proof. exact (SYM (@lem4406783 _106013 _106031 k s)). Qed.
Lemma lem4406785 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term64 _106013 _106031 k s) : term64 _106013 _106031 k s.
Proof. exact (h1). Qed.
Lemma lem4406788 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term41 _106013 _106031 s i x) = (term41 _106013 _106031 s i x).
Proof. exact (eq_refl (term41 _106013 _106031 s i x)). Qed.
Lemma lem4406791 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term78 _106013 _106031 s i x) = (s i x).
Proof. exact (@lem16933 (s i x)). Qed.
Lemma lem4406792 {_106013 : Type'} (P : _106013 -> Prop) : (term79 _106013 P) = (term80 _106013 P).
Proof. exact (@lem18392 _106013 P). Qed.
Lemma lem4406793 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term81 _106013 _106031 s i) = (term82 _106013 _106031 s i).
Proof. exact (@lem4406792 _106013 (term43 _106013 _106031 s i)). Qed.
Lemma lem4406794 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term83 _106013 _106031 s i x) = (term41 _106013 _106031 s i x).
Proof. exact (eq_refl (term83 _106013 _106031 s i x)). Qed.
Lemma lem4406795 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4406796 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term84 _106013 _106031 s i x) = (term78 _106013 _106031 s i x).
Proof. exact (MK_COMB (@lem4406795) (@lem4406794 _106013 _106031 s i x)). Qed.
Lemma lem4406797 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term84 _106013 _106031 s i x) = (s i x).
Proof. exact (TRANS (@lem4406796 _106013 _106031 s i x) (@lem4406791 _106013 _106031 s i x)). Qed.
Lemma lem4406798 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term85 _106013 _106031 s i) = (term86 _106013 _106031 s i).
Proof. exact (fun_ext (fun x : _106013 => @lem4406797 _106013 _106031 s i x)). Qed.
Lemma lem4406799 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4406800 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term82 _106013 _106031 s i) = (term87 _106013 _106031 s i).
Proof. exact (MK_COMB (@lem4406799 _106013) (@lem4406798 _106013 _106031 s i)). Qed.
Lemma lem4406801 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term81 _106013 _106031 s i) = (term87 _106013 _106031 s i).
Proof. exact (TRANS (@lem4406793 _106013 _106031 s i) (@lem4406800 _106013 _106031 s i)). Qed.
Lemma lem4406802 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term43 _106013 _106031 s i) = (term43 _106013 _106031 s i).
Proof. exact (fun_ext (fun x : _106013 => @lem4406788 _106013 _106031 s i x)). Qed.
Lemma lem4406803 {_106013 : Type'} : (@all _106013) = (@all _106013).
Proof. exact (eq_refl (@all _106013)). Qed.
Lemma lem4406804 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term44 _106013 _106031 s i) = (term44 _106013 _106031 s i).
Proof. exact (MK_COMB (@lem4406803 _106013) (@lem4406802 _106013 _106031 s i)). Qed.
Lemma lem4406806 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term88 _106031 k i) = (term88 _106031 k i).
Proof. exact (eq_refl (term88 _106031 k i)). Qed.
Lemma lem4406807 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term89 _106013 _106031 k s i) = (term90 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406806 _106031 k i) (@lem4406801 _106013 _106031 s i)). Qed.
Lemma lem4406808 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term91 _106013 _106031 k s i) = (term89 _106013 _106031 k s i).
Proof. exact (@lem17045 (k i) (term44 _106013 _106031 s i)). Qed.
Lemma lem4406809 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term91 _106013 _106031 k s i) = (term90 _106013 _106031 k s i).
Proof. exact (TRANS (@lem4406808 _106013 _106031 k s i) (@lem4406807 _106013 _106031 k s i)). Qed.
Lemma lem4406811 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term37 _106031 k i) = (term37 _106031 k i).
Proof. exact (eq_refl (term37 _106031 k i)). Qed.
Lemma lem4406812 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term45 _106013 _106031 k s i) = (term45 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406811 _106031 k i) (@lem4406804 _106013 _106031 s i)). Qed.
Lemma lem4406813 {_106031 : Type'} (P : _106031 -> Prop) : (term92 _106031 P) = (term21 _106031 P).
Proof. exact (@lem18394 _106031 P). Qed.
Lemma lem4406814 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term93 _106013 _106031 k s) = (term94 _106013 _106031 k s).
Proof. exact (@lem4406813 _106031 (term46 _106013 _106031 k s)). Qed.
Lemma lem4406815 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term95 _106013 _106031 k s i) = (term45 _106013 _106031 k s i).
Proof. exact (eq_refl (term95 _106013 _106031 k s i)). Qed.
Lemma lem4406816 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4406817 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term96 _106013 _106031 k s i) = (term91 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406816) (@lem4406815 _106013 _106031 k s i)). Qed.
Lemma lem4406818 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term96 _106013 _106031 k s i) = (term90 _106013 _106031 k s i).
Proof. exact (TRANS (@lem4406817 _106013 _106031 k s i) (@lem4406809 _106013 _106031 k s i)). Qed.
Lemma lem4406819 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term97 _106013 _106031 k s) = (term98 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4406818 _106013 _106031 k s i)). Qed.
Lemma lem4406820 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4406821 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term94 _106013 _106031 k s) = (term99 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406820 _106031) (@lem4406819 _106013 _106031 k s)). Qed.
Lemma lem4406822 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term93 _106013 _106031 k s) = (term99 _106013 _106031 k s).
Proof. exact (TRANS (@lem4406814 _106013 _106031 k s) (@lem4406821 _106013 _106031 k s)). Qed.
Lemma lem4406823 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term46 _106013 _106031 k s) = (term46 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4406812 _106013 _106031 k s i)). Qed.
Lemma lem4406824 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4406825 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term47 _106013 _106031 k s) = (term47 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406824 _106031) (@lem4406823 _106013 _106031 k s)). Qed.
Lemma lem4406834 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term100 _106013 _106031 k s i a) = (term101 _106013 _106031 k s i a).
Proof. exact (@lem17362 (k i) (s i a)). Qed.
Lemma lem4406839 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term52 _106013 _106031 k s i a) = (term102 _106013 _106031 k s i a).
Proof. exact (@lem17265 (k i) (s i a)). Qed.
Lemma lem4406840 {_106013 : Type'} (P : _106013 -> Prop) : (term92 _106013 P) = (term21 _106013 P).
Proof. exact (@lem18394 _106013 P). Qed.
Lemma lem4406841 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term103 _106013 _106031 k s i) = (term104 _106013 _106031 k s i).
Proof. exact (@lem4406840 _106013 (term54 _106013 _106031 k s i)). Qed.
Lemma lem4406842 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term105 _106013 _106031 k s i a) = (term52 _106013 _106031 k s i a).
Proof. exact (eq_refl (term105 _106013 _106031 k s i a)). Qed.
Lemma lem4406843 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4406844 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term106 _106013 _106031 k s i a) = (term100 _106013 _106031 k s i a).
Proof. exact (MK_COMB (@lem4406843) (@lem4406842 _106013 _106031 k s i a)). Qed.
Lemma lem4406845 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term106 _106013 _106031 k s i a) = (term101 _106013 _106031 k s i a).
Proof. exact (TRANS (@lem4406844 _106013 _106031 k s i a) (@lem4406834 _106013 _106031 k s i a)). Qed.
Lemma lem4406846 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term107 _106013 _106031 k s i) = (term108 _106013 _106031 k s i).
Proof. exact (fun_ext (fun a : _106013 => @lem4406845 _106013 _106031 k s i a)). Qed.
Lemma lem4406847 {_106013 : Type'} : (@all _106013) = (@all _106013).
Proof. exact (eq_refl (@all _106013)). Qed.
Lemma lem4406848 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term104 _106013 _106031 k s i) = (term109 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406847 _106013) (@lem4406846 _106013 _106031 k s i)). Qed.
Lemma lem4406849 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term103 _106013 _106031 k s i) = (term109 _106013 _106031 k s i).
Proof. exact (TRANS (@lem4406841 _106013 _106031 k s i) (@lem4406848 _106013 _106031 k s i)). Qed.
Lemma lem4406850 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term54 _106013 _106031 k s i) = (term110 _106013 _106031 k s i).
Proof. exact (fun_ext (fun a : _106013 => @lem4406839 _106013 _106031 k s i a)). Qed.
Lemma lem4406851 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4406852 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term56 _106013 _106031 k s i) = (term111 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406851 _106013) (@lem4406850 _106013 _106031 k s i)). Qed.
Lemma lem4406853 {_106031 : Type'} (P : _106031 -> Prop) : (term79 _106031 P) = (term80 _106031 P).
Proof. exact (@lem18392 _106031 P). Qed.
Lemma lem4406854 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term61 _106013 _106031 k s) = (term112 _106013 _106031 k s).
Proof. exact (@lem4406853 _106031 (term58 _106013 _106031 k s)). Qed.
Lemma lem4406855 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term113 _106013 _106031 k s i) = (term56 _106013 _106031 k s i).
Proof. exact (eq_refl (term113 _106013 _106031 k s i)). Qed.
Lemma lem4406856 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4406857 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term114 _106013 _106031 k s i) = (term103 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406856) (@lem4406855 _106013 _106031 k s i)). Qed.
Lemma lem4406858 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term114 _106013 _106031 k s i) = (term109 _106013 _106031 k s i).
Proof. exact (TRANS (@lem4406857 _106013 _106031 k s i) (@lem4406849 _106013 _106031 k s i)). Qed.
Lemma lem4406859 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term115 _106013 _106031 k s) = (term116 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4406858 _106013 _106031 k s i)). Qed.
Lemma lem4406860 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4406861 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term112 _106013 _106031 k s) = (term117 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406860 _106031) (@lem4406859 _106013 _106031 k s)). Qed.
Lemma lem4406862 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term61 _106013 _106031 k s) = (term117 _106013 _106031 k s).
Proof. exact (TRANS (@lem4406854 _106013 _106031 k s) (@lem4406861 _106013 _106031 k s)). Qed.
Lemma lem4406863 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term58 _106013 _106031 k s) = (term118 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4406852 _106013 _106031 k s i)). Qed.
Lemma lem4406864 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4406865 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term60 _106013 _106031 k s) = (term119 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406864 _106031) (@lem4406863 _106013 _106031 k s)). Qed.
Lemma lem4406866 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term120 _106013 _106031 k s) = (term60 _106013 _106031 k s).
Proof. exact (@lem16933 (term60 _106013 _106031 k s)). Qed.
Lemma lem4406867 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term120 _106013 _106031 k s) = (term119 _106013 _106031 k s).
Proof. exact (TRANS (@lem4406866 _106013 _106031 k s) (@lem4406865 _106013 _106031 k s)). Qed.
Lemma lem4406868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4406869 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term121 _106013 _106031 k s) = (term122 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406868) (@lem4406822 _106013 _106031 k s)). Qed.
Lemma lem4406870 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term123 _106013 _106031 k s) = (term124 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406869 _106013 _106031 k s) (@lem4406862 _106013 _106031 k s)). Qed.
Lemma lem4406871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4406872 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term125 _106013 _106031 k s) = (term125 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406871) (@lem4406825 _106013 _106031 k s)). Qed.
Lemma lem4406873 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term126 _106013 _106031 k s) = (term127 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406872 _106013 _106031 k s) (@lem4406867 _106013 _106031 k s)). Qed.
Lemma lem4406874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4406875 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term128 _106013 _106031 k s) = (term129 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406874) (@lem4406873 _106013 _106031 k s)). Qed.
Lemma lem4406876 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term130 _106013 _106031 k s) = (term131 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406875 _106013 _106031 k s) (@lem4406870 _106013 _106031 k s)). Qed.
Lemma lem4406877 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term64 _106013 _106031 k s) = (term130 _106013 _106031 k s).
Proof. exact (@lem17646 (term47 _106013 _106031 k s) (term61 _106013 _106031 k s)). Qed.
Lemma lem4406878 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term64 _106013 _106031 k s) = (term131 _106013 _106031 k s).
Proof. exact (TRANS (@lem4406877 _106013 _106031 k s) (@lem4406876 _106013 _106031 k s)). Qed.
Lemma lem4406916 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4406917 {_106013 : Type'} (P : _106013 -> Prop) (Q : _106013 -> Prop) : (term132 _106013 P Q) = (term133 _106013 P Q).
Proof. exact (@lem4406916 _106013 P Q). Qed.
Lemma lem4406918 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term134 _106013 _106031 k s i) = (term135 _106013 _106031 k s i).
Proof. exact (@lem4406917 _106013 (term136 _106013 _106031 k i) (term86 _106013 _106031 s i)). Qed.
Lemma lem4406919 {_106013 _106031 : Type'} (a : _106013) (k : _106031 -> Prop) (i : _106031) : (term137 _106013 _106031 k i a) = (term138 _106031 k i).
Proof. exact (eq_refl (term137 _106013 _106031 k i a)). Qed.
Lemma lem4406920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4406921 {_106013 _106031 : Type'} (a : _106013) (k : _106031 -> Prop) (i : _106031) : (term139 _106013 _106031 k i a) = (term88 _106031 k i).
Proof. exact (MK_COMB (@lem4406920) (@lem4406919 _106013 _106031 a k i)). Qed.
Lemma lem4406922 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term140 _106013 _106031 s i a) = (s i a).
Proof. exact (eq_refl (term140 _106013 _106031 s i a)). Qed.
Lemma lem4406923 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term141 _106013 _106031 k s i a) = (term102 _106013 _106031 k s i a).
Proof. exact (MK_COMB (@lem4406921 _106013 _106031 a k i) (@lem4406922 _106013 _106031 s i a)). Qed.
Lemma lem4406924 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term142 _106013 _106031 k s i) = (term110 _106013 _106031 k s i).
Proof. exact (fun_ext (fun a : _106013 => @lem4406923 _106013 _106031 k s i a)). Qed.
Lemma lem4406925 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4406926 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term134 _106013 _106031 k s i) = (term111 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406925 _106013) (@lem4406924 _106013 _106031 k s i)). Qed.
Lemma lem4406927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4406928 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term143 _106013 _106031 k s i) = (term144 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406927) (@lem4406926 _106013 _106031 k s i)). Qed.
Lemma lem4406929 {_106013 _106031 : Type'} (a : _106013) (k : _106031 -> Prop) (i : _106031) : (term137 _106013 _106031 k i a) = (term138 _106031 k i).
Proof. exact (eq_refl (term137 _106013 _106031 k i a)). Qed.
Lemma lem4406930 {_106013 _106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term145 _106013 _106031 k i) = (term136 _106013 _106031 k i).
Proof. exact (fun_ext (fun a : _106013 => @lem4406929 _106013 _106031 a k i)). Qed.
Lemma lem4406931 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4406932 {_106013 _106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term146 _106013 _106031 k i) = (term147 _106013 _106031 k i).
Proof. exact (MK_COMB (@lem4406931 _106013) (@lem4406930 _106013 _106031 k i)). Qed.
Lemma lem4406933 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4406934 {_106013 _106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term148 _106013 _106031 k i) = (term149 _106013 _106031 k i).
Proof. exact (MK_COMB (@lem4406933) (@lem4406932 _106013 _106031 k i)). Qed.
Lemma lem4406935 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term140 _106013 _106031 s i a) = (s i a).
Proof. exact (eq_refl (term140 _106013 _106031 s i a)). Qed.
Lemma lem4406936 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term150 _106013 _106031 s i) = (term86 _106013 _106031 s i).
Proof. exact (fun_ext (fun a : _106013 => @lem4406935 _106013 _106031 s i a)). Qed.
Lemma lem4406937 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4406938 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term151 _106013 _106031 s i) = (term87 _106013 _106031 s i).
Proof. exact (MK_COMB (@lem4406937 _106013) (@lem4406936 _106013 _106031 s i)). Qed.
Lemma lem4406939 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term135 _106013 _106031 k s i) = (term152 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406934 _106013 _106031 k i) (@lem4406938 _106013 _106031 s i)). Qed.
Lemma lem4406940 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : ((term134 _106013 _106031 k s i) = (term135 _106013 _106031 k s i)) = ((term111 _106013 _106031 k s i) = (term152 _106013 _106031 k s i)).
Proof. exact (MK_COMB (@lem4406928 _106013 _106031 k s i) (@lem4406939 _106013 _106031 k s i)). Qed.
Lemma lem4406941 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term111 _106013 _106031 k s i) = (term152 _106013 _106031 k s i).
Proof. exact (EQ_MP (@lem4406940 _106013 _106031 k s i) (@lem4406918 _106013 _106031 k s i)). Qed.
Lemma lem4406943 {A : Type'} (t : Prop) : (term153 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem4406944 {_106013 : Type'} (t : Prop) : (term153 _106013 t) = t.
Proof. exact (@lem4406943 _106013 t). Qed.
Lemma lem4406945 {_106013 _106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term147 _106013 _106031 k i) = (term138 _106031 k i).
Proof. exact (@lem4406944 _106013 (term138 _106031 k i)). Qed.
Lemma lem4406946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4406947 {_106013 _106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term149 _106013 _106031 k i) = (term88 _106031 k i).
Proof. exact (MK_COMB (@lem4406946) (@lem4406945 _106013 _106031 k i)). Qed.
Lemma lem4406952 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term87 _106013 _106031 s i) = (term87 _106013 _106031 s i).
Proof. exact (eq_refl (term87 _106013 _106031 s i)). Qed.
Lemma lem4406953 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term152 _106013 _106031 k s i) = (term90 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4406947 _106013 _106031 k i) (@lem4406952 _106013 _106031 s i)). Qed.
Lemma lem4406954 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term111 _106013 _106031 k s i) = (term90 _106013 _106031 k s i).
Proof. exact (TRANS (@lem4406941 _106013 _106031 k s i) (@lem4406953 _106013 _106031 k s i)). Qed.
Lemma lem4406955 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term118 _106013 _106031 k s) = (term98 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4406954 _106013 _106031 k s i)). Qed.
Lemma lem4406956 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4406957 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term119 _106013 _106031 k s) = (term99 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4406956 _106031) (@lem4406955 _106013 _106031 k s)). Qed.
Lemma lem4407006 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term125 _106013 _106031 k s) = (term125 _106013 _106031 k s).
Proof. exact (eq_refl (term125 _106013 _106031 k s)). Qed.
Lemma lem4407007 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term127 _106013 _106031 k s) = (term154 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407006 _106013 _106031 k s) (@lem4406957 _106013 _106031 k s)). Qed.
Lemma lem4407008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4407009 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term129 _106013 _106031 k s) = (term155 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407008) (@lem4407007 _106013 _106031 k s)). Qed.
Lemma lem4407067 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4407068 {_106013 : Type'} (P : _106013 -> Prop) (Q : _106013 -> Prop) : (term156 _106013 P Q) = (term157 _106013 P Q).
Proof. exact (@lem4407067 _106013 P Q). Qed.
Lemma lem4407069 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term158 _106013 _106031 k s i) = (term159 _106013 _106031 k s i).
Proof. exact (@lem4407068 _106013 (term160 _106013 _106031 k i) (term43 _106013 _106031 s i)). Qed.
Lemma lem4407070 {_106013 _106031 : Type'} (a : _106013) (k : _106031 -> Prop) (i : _106031) : (term161 _106013 _106031 k i a) = (k i).
Proof. exact (eq_refl (term161 _106013 _106031 k i a)). Qed.
Lemma lem4407071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4407072 {_106013 _106031 : Type'} (a : _106013) (k : _106031 -> Prop) (i : _106031) : (term162 _106013 _106031 k i a) = (term37 _106031 k i).
Proof. exact (MK_COMB (@lem4407071) (@lem4407070 _106013 _106031 a k i)). Qed.
Lemma lem4407073 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term83 _106013 _106031 s i a) = (term41 _106013 _106031 s i a).
Proof. exact (eq_refl (term83 _106013 _106031 s i a)). Qed.
Lemma lem4407074 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term163 _106013 _106031 k s i a) = (term101 _106013 _106031 k s i a).
Proof. exact (MK_COMB (@lem4407072 _106013 _106031 a k i) (@lem4407073 _106013 _106031 s i a)). Qed.
Lemma lem4407075 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term164 _106013 _106031 k s i) = (term108 _106013 _106031 k s i).
Proof. exact (fun_ext (fun a : _106013 => @lem4407074 _106013 _106031 k s i a)). Qed.
Lemma lem4407076 {_106013 : Type'} : (@all _106013) = (@all _106013).
Proof. exact (eq_refl (@all _106013)). Qed.
Lemma lem4407077 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term158 _106013 _106031 k s i) = (term109 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407076 _106013) (@lem4407075 _106013 _106031 k s i)). Qed.
Lemma lem4407078 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407079 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term165 _106013 _106031 k s i) = (term166 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407078) (@lem4407077 _106013 _106031 k s i)). Qed.
Lemma lem4407080 {_106013 _106031 : Type'} (a : _106013) (k : _106031 -> Prop) (i : _106031) : (term161 _106013 _106031 k i a) = (k i).
Proof. exact (eq_refl (term161 _106013 _106031 k i a)). Qed.
Lemma lem4407081 {_106013 _106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term167 _106013 _106031 k i) = (term160 _106013 _106031 k i).
Proof. exact (fun_ext (fun a : _106013 => @lem4407080 _106013 _106031 a k i)). Qed.
Lemma lem4407082 {_106013 : Type'} : (@all _106013) = (@all _106013).
Proof. exact (eq_refl (@all _106013)). Qed.
Lemma lem4407083 {_106013 _106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term168 _106013 _106031 k i) = (term169 _106013 _106031 k i).
Proof. exact (MK_COMB (@lem4407082 _106013) (@lem4407081 _106013 _106031 k i)). Qed.
Lemma lem4407084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4407085 {_106013 _106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term170 _106013 _106031 k i) = (term171 _106013 _106031 k i).
Proof. exact (MK_COMB (@lem4407084) (@lem4407083 _106013 _106031 k i)). Qed.
Lemma lem4407086 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term83 _106013 _106031 s i a) = (term41 _106013 _106031 s i a).
Proof. exact (eq_refl (term83 _106013 _106031 s i a)). Qed.
Lemma lem4407087 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term172 _106013 _106031 s i) = (term43 _106013 _106031 s i).
Proof. exact (fun_ext (fun a : _106013 => @lem4407086 _106013 _106031 s i a)). Qed.
Lemma lem4407088 {_106013 : Type'} : (@all _106013) = (@all _106013).
Proof. exact (eq_refl (@all _106013)). Qed.
Lemma lem4407089 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term173 _106013 _106031 s i) = (term44 _106013 _106031 s i).
Proof. exact (MK_COMB (@lem4407088 _106013) (@lem4407087 _106013 _106031 s i)). Qed.
Lemma lem4407090 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term159 _106013 _106031 k s i) = (term174 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407085 _106013 _106031 k i) (@lem4407089 _106013 _106031 s i)). Qed.
Lemma lem4407091 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : ((term158 _106013 _106031 k s i) = (term159 _106013 _106031 k s i)) = ((term109 _106013 _106031 k s i) = (term174 _106013 _106031 k s i)).
Proof. exact (MK_COMB (@lem4407079 _106013 _106031 k s i) (@lem4407090 _106013 _106031 k s i)). Qed.
Lemma lem4407092 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term109 _106013 _106031 k s i) = (term174 _106013 _106031 k s i).
Proof. exact (EQ_MP (@lem4407091 _106013 _106031 k s i) (@lem4407069 _106013 _106031 k s i)). Qed.
Lemma lem4407094 {A : Type'} (t : Prop) : (term175 A t) = t.
Proof. exact (EQ_MP (@lem18935 A t) (@lem18934 A t)). Qed.
Lemma lem4407095 {_106013 : Type'} (t : Prop) : (term175 _106013 t) = t.
Proof. exact (@lem4407094 _106013 t). Qed.
Lemma lem4407096 {_106013 _106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term169 _106013 _106031 k i) = (k i).
Proof. exact (@lem4407095 _106013 (k i)). Qed.
Lemma lem4407097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4407098 {_106013 _106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term171 _106013 _106031 k i) = (term37 _106031 k i).
Proof. exact (MK_COMB (@lem4407097) (@lem4407096 _106013 _106031 k i)). Qed.
Lemma lem4407103 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term44 _106013 _106031 s i) = (term44 _106013 _106031 s i).
Proof. exact (eq_refl (term44 _106013 _106031 s i)). Qed.
Lemma lem4407104 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term174 _106013 _106031 k s i) = (term45 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407098 _106013 _106031 k i) (@lem4407103 _106013 _106031 s i)). Qed.
Lemma lem4407105 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term109 _106013 _106031 k s i) = (term45 _106013 _106031 k s i).
Proof. exact (TRANS (@lem4407092 _106013 _106031 k s i) (@lem4407104 _106013 _106031 k s i)). Qed.
Lemma lem4407106 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term116 _106013 _106031 k s) = (term46 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407105 _106013 _106031 k s i)). Qed.
Lemma lem4407107 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4407108 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term117 _106013 _106031 k s) = (term47 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407107 _106031) (@lem4407106 _106013 _106031 k s)). Qed.
Lemma lem4407137 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term122 _106013 _106031 k s) = (term122 _106013 _106031 k s).
Proof. exact (eq_refl (term122 _106013 _106031 k s)). Qed.
Lemma lem4407138 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term124 _106013 _106031 k s) = (term176 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407137 _106013 _106031 k s) (@lem4407108 _106013 _106031 k s)). Qed.
Lemma lem4407139 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term131 _106013 _106031 k s) = (term177 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407009 _106013 _106031 k s) (@lem4407138 _106013 _106031 k s)). Qed.
Lemma lem4407141 {A : Type'} (P : Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4407142 {_106013 : Type'} (P : Prop) (Q : _106013 -> Prop) : (term178 _106013 P Q) = (term179 _106013 P Q).
Proof. exact (@lem4407141 _106013 P Q). Qed.
Lemma lem4407143 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term180 _106013 _106031 k s i) = (term181 _106013 _106031 k s i).
Proof. exact (@lem4407142 _106013 (term138 _106031 k i) (term86 _106013 _106031 s i)). Qed.
Lemma lem4407144 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term140 _106013 _106031 s i a) = (s i a).
Proof. exact (eq_refl (term140 _106013 _106031 s i a)). Qed.
Lemma lem4407145 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term150 _106013 _106031 s i) = (term86 _106013 _106031 s i).
Proof. exact (fun_ext (fun a : _106013 => @lem4407144 _106013 _106031 s i a)). Qed.
Lemma lem4407146 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4407147 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term151 _106013 _106031 s i) = (term87 _106013 _106031 s i).
Proof. exact (MK_COMB (@lem4407146 _106013) (@lem4407145 _106013 _106031 s i)). Qed.
Lemma lem4407148 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term88 _106031 k i) = (term88 _106031 k i).
Proof. exact (eq_refl (term88 _106031 k i)). Qed.
Lemma lem4407149 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term180 _106013 _106031 k s i) = (term90 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407148 _106031 k i) (@lem4407147 _106013 _106031 s i)). Qed.
Lemma lem4407150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407151 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term182 _106013 _106031 k s i) = (term183 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407150) (@lem4407149 _106013 _106031 k s i)). Qed.
Lemma lem4407152 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term140 _106013 _106031 s i a) = (s i a).
Proof. exact (eq_refl (term140 _106013 _106031 s i a)). Qed.
Lemma lem4407153 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term88 _106031 k i) = (term88 _106031 k i).
Proof. exact (eq_refl (term88 _106031 k i)). Qed.
Lemma lem4407154 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term184 _106013 _106031 k s i a) = (term102 _106013 _106031 k s i a).
Proof. exact (MK_COMB (@lem4407153 _106031 k i) (@lem4407152 _106013 _106031 s i a)). Qed.
Lemma lem4407155 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term185 _106013 _106031 k s i) = (term110 _106013 _106031 k s i).
Proof. exact (fun_ext (fun a : _106013 => @lem4407154 _106013 _106031 k s i a)). Qed.
Lemma lem4407156 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4407157 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term181 _106013 _106031 k s i) = (term111 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407156 _106013) (@lem4407155 _106013 _106031 k s i)). Qed.
Lemma lem4407158 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : ((term180 _106013 _106031 k s i) = (term181 _106013 _106031 k s i)) = ((term90 _106013 _106031 k s i) = (term111 _106013 _106031 k s i)).
Proof. exact (MK_COMB (@lem4407151 _106013 _106031 k s i) (@lem4407157 _106013 _106031 k s i)). Qed.
Lemma lem4407159 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term90 _106013 _106031 k s i) = (term111 _106013 _106031 k s i).
Proof. exact (EQ_MP (@lem4407158 _106013 _106031 k s i) (@lem4407143 _106013 _106031 k s i)). Qed.
Lemma lem4407160 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term98 _106013 _106031 k s) = (term118 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407159 _106013 _106031 k s i)). Qed.
Lemma lem4407161 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4407162 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term99 _106013 _106031 k s) = (term119 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407161 _106031) (@lem4407160 _106013 _106031 k s)). Qed.
Lemma lem4407164 {A B : Type'} (P : type1413 A B) : (term23 A B P) = (term24 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4407165 {_106013 _106031 : Type'} (P : type1470 _106013 _106031) : (term186 _106013 _106031 P) = (term187 _106013 _106031 P).
Proof. exact (@lem4407164 _106031 _106013 P). Qed.
Lemma lem4407166 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term188 _106013 _106031 k s) = (term189 _106013 _106031 k s).
Proof. exact (@lem4407165 _106013 _106031 (term190 _106013 _106031 k s)). Qed.
Lemma lem4407167 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term191 _106013 _106031 k s i) = (term110 _106013 _106031 k s i).
Proof. exact (eq_refl (term191 _106013 _106031 k s i)). Qed.
Lemma lem4407168 {_106013 : Type'} (a : _106013) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4407169 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term192 _106013 _106031 k s i a) = (term193 _106013 _106031 k s i a).
Proof. exact (MK_COMB (@lem4407167 _106013 _106031 k s i) (@lem4407168 _106013 a)). Qed.
Lemma lem4407170 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term193 _106013 _106031 k s i a) = (term102 _106013 _106031 k s i a).
Proof. exact (eq_refl (term193 _106013 _106031 k s i a)). Qed.
Lemma lem4407171 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (a : _106013) : (term192 _106013 _106031 k s i a) = (term102 _106013 _106031 k s i a).
Proof. exact (TRANS (@lem4407169 _106013 _106031 k s i a) (@lem4407170 _106013 _106031 k s i a)). Qed.
Lemma lem4407172 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term194 _106013 _106031 k s i) = (term110 _106013 _106031 k s i).
Proof. exact (fun_ext (fun a : _106013 => @lem4407171 _106013 _106031 k s i a)). Qed.
Lemma lem4407173 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4407174 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term195 _106013 _106031 k s i) = (term111 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407173 _106013) (@lem4407172 _106013 _106031 k s i)). Qed.
Lemma lem4407175 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term196 _106013 _106031 k s) = (term118 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407174 _106013 _106031 k s i)). Qed.
Lemma lem4407176 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4407177 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term188 _106013 _106031 k s) = (term119 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407176 _106031) (@lem4407175 _106013 _106031 k s)). Qed.
Lemma lem4407178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407179 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term197 _106013 _106031 k s) = (term198 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407178) (@lem4407177 _106013 _106031 k s)). Qed.
Lemma lem4407180 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term191 _106013 _106031 k s i) = (term110 _106013 _106031 k s i).
Proof. exact (eq_refl (term191 _106013 _106031 k s i)). Qed.
Lemma lem4407181 {_106013 _106031 : Type'} (a : _106031 -> _106013) (i : _106031) : (a i) = (a i).
Proof. exact (eq_refl (a i)). Qed.
Lemma lem4407182 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (i : _106031) : (term199 _106013 _106031 k s a i) = (term200 _106013 _106031 k s a i).
Proof. exact (MK_COMB (@lem4407180 _106013 _106031 k s i) (@lem4407181 _106013 _106031 a i)). Qed.
Lemma lem4407183 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (i : _106031) : (term200 _106013 _106031 k s a i) = (term201 _106013 _106031 k s a i).
Proof. exact (eq_refl (term200 _106013 _106031 k s a i)). Qed.
Lemma lem4407184 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (i : _106031) : (term199 _106013 _106031 k s a i) = (term201 _106013 _106031 k s a i).
Proof. exact (TRANS (@lem4407182 _106013 _106031 k s a i) (@lem4407183 _106013 _106031 k s a i)). Qed.
Lemma lem4407185 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term202 _106013 _106031 k s a) = (term203 _106013 _106031 k s a).
Proof. exact (fun_ext (fun i : _106031 => @lem4407184 _106013 _106031 k s a i)). Qed.
Lemma lem4407186 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4407187 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term204 _106013 _106031 k s a) = (term205 _106013 _106031 k s a).
Proof. exact (MK_COMB (@lem4407186 _106031) (@lem4407185 _106013 _106031 k s a)). Qed.
Lemma lem4407188 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term206 _106013 _106031 k s) = (term207 _106013 _106031 k s).
Proof. exact (fun_ext (fun a : _106031 -> _106013 => @lem4407187 _106013 _106031 k s a)). Qed.
Lemma lem4407189 {_106013 _106031 : Type'} : (@ex (_106031 -> _106013)) = (@ex (_106031 -> _106013)).
Proof. exact (eq_refl (@ex (_106031 -> _106013))). Qed.
Lemma lem4407190 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term189 _106013 _106031 k s) = (term208 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407189 _106013 _106031) (@lem4407188 _106013 _106031 k s)). Qed.
Lemma lem4407191 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term188 _106013 _106031 k s) = (term189 _106013 _106031 k s)) = ((term119 _106013 _106031 k s) = (term208 _106013 _106031 k s)).
Proof. exact (MK_COMB (@lem4407179 _106013 _106031 k s) (@lem4407190 _106013 _106031 k s)). Qed.
Lemma lem4407192 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term119 _106013 _106031 k s) = (term208 _106013 _106031 k s).
Proof. exact (EQ_MP (@lem4407191 _106013 _106031 k s) (@lem4407166 _106013 _106031 k s)). Qed.
Lemma lem4407193 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term99 _106013 _106031 k s) = (term208 _106013 _106031 k s).
Proof. exact (TRANS (@lem4407162 _106013 _106031 k s) (@lem4407192 _106013 _106031 k s)). Qed.
Lemma lem4407194 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term125 _106013 _106031 k s) = (term125 _106013 _106031 k s).
Proof. exact (eq_refl (term125 _106013 _106031 k s)). Qed.
Lemma lem4407195 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term154 _106013 _106031 k s) = (term209 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407194 _106013 _106031 k s) (@lem4407193 _106013 _106031 k s)). Qed.
Lemma lem4407197 {A : Type'} (P : A -> Prop) (Q : Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4407198 {_106031 : Type'} (P : _106031 -> Prop) (Q : Prop) : (term210 _106031 P Q) = (term211 _106031 P Q).
Proof. exact (@lem4407197 _106031 P Q). Qed.
Lemma lem4407199 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term212 _106013 _106031 k s) = (term213 _106013 _106031 k s).
Proof. exact (@lem4407198 _106031 (term46 _106013 _106031 k s) (term208 _106013 _106031 k s)). Qed.
Lemma lem4407200 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term95 _106013 _106031 k s i) = (term45 _106013 _106031 k s i).
Proof. exact (eq_refl (term95 _106013 _106031 k s i)). Qed.
Lemma lem4407201 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term214 _106013 _106031 k s) = (term46 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407200 _106013 _106031 k s i)). Qed.
Lemma lem4407202 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4407203 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term215 _106013 _106031 k s) = (term47 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407202 _106031) (@lem4407201 _106013 _106031 k s)). Qed.
Lemma lem4407204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4407205 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term216 _106013 _106031 k s) = (term125 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407204) (@lem4407203 _106013 _106031 k s)). Qed.
Lemma lem4407206 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term208 _106013 _106031 k s) = (term208 _106013 _106031 k s).
Proof. exact (eq_refl (term208 _106013 _106031 k s)). Qed.
Lemma lem4407207 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term212 _106013 _106031 k s) = (term209 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407205 _106013 _106031 k s) (@lem4407206 _106013 _106031 k s)). Qed.
Lemma lem4407208 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407209 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term217 _106013 _106031 k s) = (term218 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407208) (@lem4407207 _106013 _106031 k s)). Qed.
Lemma lem4407210 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term95 _106013 _106031 k s i) = (term45 _106013 _106031 k s i).
Proof. exact (eq_refl (term95 _106013 _106031 k s i)). Qed.
Lemma lem4407211 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4407212 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term219 _106013 _106031 k s i) = (term220 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407211) (@lem4407210 _106013 _106031 k s i)). Qed.
Lemma lem4407213 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term208 _106013 _106031 k s) = (term208 _106013 _106031 k s).
Proof. exact (eq_refl (term208 _106013 _106031 k s)). Qed.
Lemma lem4407214 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term221 _106013 _106031 i k s) = (term222 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407212 _106013 _106031 k s i) (@lem4407213 _106013 _106031 k s)). Qed.
Lemma lem4407215 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term223 _106013 _106031 k s) = (term224 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407214 _106013 _106031 i k s)). Qed.
Lemma lem4407216 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4407217 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term213 _106013 _106031 k s) = (term225 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407216 _106031) (@lem4407215 _106013 _106031 k s)). Qed.
Lemma lem4407218 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term212 _106013 _106031 k s) = (term213 _106013 _106031 k s)) = ((term209 _106013 _106031 k s) = (term225 _106013 _106031 k s)).
Proof. exact (MK_COMB (@lem4407209 _106013 _106031 k s) (@lem4407217 _106013 _106031 k s)). Qed.
Lemma lem4407219 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term209 _106013 _106031 k s) = (term225 _106013 _106031 k s).
Proof. exact (EQ_MP (@lem4407218 _106013 _106031 k s) (@lem4407199 _106013 _106031 k s)). Qed.
Lemma lem4407221 {A : Type'} (P : Prop) (Q : A -> Prop) : (term226 A P Q) = (term227 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4407222 {_106013 _106031 : Type'} (P : Prop) (Q : type805 _106013 _106031) : (term228 _106013 _106031 P Q) = (term229 _106013 _106031 P Q).
Proof. exact (@lem4407221 (_106031 -> _106013) P Q). Qed.
Lemma lem4407223 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term230 _106013 _106031 i k s) = (term231 _106013 _106031 i k s).
Proof. exact (@lem4407222 _106013 _106031 (term45 _106013 _106031 k s i) (term207 _106013 _106031 k s)). Qed.
Lemma lem4407224 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term232 _106013 _106031 k s a) = (term205 _106013 _106031 k s a).
Proof. exact (eq_refl (term232 _106013 _106031 k s a)). Qed.
Lemma lem4407225 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term233 _106013 _106031 k s) = (term207 _106013 _106031 k s).
Proof. exact (fun_ext (fun a : _106031 -> _106013 => @lem4407224 _106013 _106031 k s a)). Qed.
Lemma lem4407226 {_106013 _106031 : Type'} : (@ex (_106031 -> _106013)) = (@ex (_106031 -> _106013)).
Proof. exact (eq_refl (@ex (_106031 -> _106013))). Qed.
Lemma lem4407227 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term234 _106013 _106031 k s) = (term208 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407226 _106013 _106031) (@lem4407225 _106013 _106031 k s)). Qed.
Lemma lem4407228 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term220 _106013 _106031 k s i) = (term220 _106013 _106031 k s i).
Proof. exact (eq_refl (term220 _106013 _106031 k s i)). Qed.
Lemma lem4407229 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term230 _106013 _106031 i k s) = (term222 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407228 _106013 _106031 k s i) (@lem4407227 _106013 _106031 k s)). Qed.
Lemma lem4407230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407231 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term235 _106013 _106031 i k s) = (term236 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407230) (@lem4407229 _106013 _106031 i k s)). Qed.
Lemma lem4407232 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term232 _106013 _106031 k s a) = (term205 _106013 _106031 k s a).
Proof. exact (eq_refl (term232 _106013 _106031 k s a)). Qed.
Lemma lem4407233 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term220 _106013 _106031 k s i) = (term220 _106013 _106031 k s i).
Proof. exact (eq_refl (term220 _106013 _106031 k s i)). Qed.
Lemma lem4407234 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term237 _106013 _106031 i k s a) = (term238 _106013 _106031 i k s a).
Proof. exact (MK_COMB (@lem4407233 _106013 _106031 k s i) (@lem4407232 _106013 _106031 k s a)). Qed.
Lemma lem4407235 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term239 _106013 _106031 i k s) = (term240 _106013 _106031 i k s).
Proof. exact (fun_ext (fun a : _106031 -> _106013 => @lem4407234 _106013 _106031 i k s a)). Qed.
Lemma lem4407236 {_106013 _106031 : Type'} : (@ex (_106031 -> _106013)) = (@ex (_106031 -> _106013)).
Proof. exact (eq_refl (@ex (_106031 -> _106013))). Qed.
Lemma lem4407237 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term231 _106013 _106031 i k s) = (term241 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407236 _106013 _106031) (@lem4407235 _106013 _106031 i k s)). Qed.
Lemma lem4407238 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term230 _106013 _106031 i k s) = (term231 _106013 _106031 i k s)) = ((term222 _106013 _106031 i k s) = (term241 _106013 _106031 i k s)).
Proof. exact (MK_COMB (@lem4407231 _106013 _106031 i k s) (@lem4407237 _106013 _106031 i k s)). Qed.
Lemma lem4407239 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term222 _106013 _106031 i k s) = (term241 _106013 _106031 i k s).
Proof. exact (EQ_MP (@lem4407238 _106013 _106031 i k s) (@lem4407223 _106013 _106031 i k s)). Qed.
Lemma lem4407240 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term224 _106013 _106031 k s) = (term242 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407239 _106013 _106031 i k s)). Qed.
Lemma lem4407241 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4407242 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term225 _106013 _106031 k s) = (term243 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407241 _106031) (@lem4407240 _106013 _106031 k s)). Qed.
Lemma lem4407243 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term209 _106013 _106031 k s) = (term243 _106013 _106031 k s).
Proof. exact (TRANS (@lem4407219 _106013 _106031 k s) (@lem4407242 _106013 _106031 k s)). Qed.
Lemma lem4407244 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term154 _106013 _106031 k s) = (term243 _106013 _106031 k s).
Proof. exact (TRANS (@lem4407195 _106013 _106031 k s) (@lem4407243 _106013 _106031 k s)). Qed.
Lemma lem4407245 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4407246 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term155 _106013 _106031 k s) = (term244 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407245) (@lem4407244 _106013 _106031 k s)). Qed.
Lemma lem4407248 {A : Type'} (P : Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4407249 {_106013 : Type'} (P : Prop) (Q : _106013 -> Prop) : (term178 _106013 P Q) = (term179 _106013 P Q).
Proof. exact (@lem4407248 _106013 P Q). Qed.
Lemma lem4407250 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term180 _106013 _106031 k s i) = (term181 _106013 _106031 k s i).
Proof. exact (@lem4407249 _106013 (term138 _106031 k i) (term86 _106013 _106031 s i)). Qed.
Lemma lem4407251 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term140 _106013 _106031 s i x) = (s i x).
Proof. exact (eq_refl (term140 _106013 _106031 s i x)). Qed.
Lemma lem4407252 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term150 _106013 _106031 s i) = (term86 _106013 _106031 s i).
Proof. exact (fun_ext (fun x : _106013 => @lem4407251 _106013 _106031 s i x)). Qed.
Lemma lem4407253 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4407254 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term151 _106013 _106031 s i) = (term87 _106013 _106031 s i).
Proof. exact (MK_COMB (@lem4407253 _106013) (@lem4407252 _106013 _106031 s i)). Qed.
Lemma lem4407255 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term88 _106031 k i) = (term88 _106031 k i).
Proof. exact (eq_refl (term88 _106031 k i)). Qed.
Lemma lem4407256 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term180 _106013 _106031 k s i) = (term90 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407255 _106031 k i) (@lem4407254 _106013 _106031 s i)). Qed.
Lemma lem4407257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407258 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term182 _106013 _106031 k s i) = (term183 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407257) (@lem4407256 _106013 _106031 k s i)). Qed.
Lemma lem4407259 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term140 _106013 _106031 s i x) = (s i x).
Proof. exact (eq_refl (term140 _106013 _106031 s i x)). Qed.
Lemma lem4407260 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term88 _106031 k i) = (term88 _106031 k i).
Proof. exact (eq_refl (term88 _106031 k i)). Qed.
Lemma lem4407261 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term184 _106013 _106031 k s i x) = (term102 _106013 _106031 k s i x).
Proof. exact (MK_COMB (@lem4407260 _106031 k i) (@lem4407259 _106013 _106031 s i x)). Qed.
Lemma lem4407262 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term185 _106013 _106031 k s i) = (term110 _106013 _106031 k s i).
Proof. exact (fun_ext (fun x : _106013 => @lem4407261 _106013 _106031 k s i x)). Qed.
Lemma lem4407263 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4407264 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term181 _106013 _106031 k s i) = (term111 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407263 _106013) (@lem4407262 _106013 _106031 k s i)). Qed.
Lemma lem4407265 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : ((term180 _106013 _106031 k s i) = (term181 _106013 _106031 k s i)) = ((term90 _106013 _106031 k s i) = (term111 _106013 _106031 k s i)).
Proof. exact (MK_COMB (@lem4407258 _106013 _106031 k s i) (@lem4407264 _106013 _106031 k s i)). Qed.
Lemma lem4407266 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term90 _106013 _106031 k s i) = (term111 _106013 _106031 k s i).
Proof. exact (EQ_MP (@lem4407265 _106013 _106031 k s i) (@lem4407250 _106013 _106031 k s i)). Qed.
Lemma lem4407267 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term98 _106013 _106031 k s) = (term118 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407266 _106013 _106031 k s i)). Qed.
Lemma lem4407268 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4407269 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term99 _106013 _106031 k s) = (term119 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407268 _106031) (@lem4407267 _106013 _106031 k s)). Qed.
Lemma lem4407271 {A B : Type'} (P : type1413 A B) : (term23 A B P) = (term24 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4407272 {_106013 _106031 : Type'} (P : type1470 _106013 _106031) : (term186 _106013 _106031 P) = (term187 _106013 _106031 P).
Proof. exact (@lem4407271 _106031 _106013 P). Qed.
Lemma lem4407273 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term188 _106013 _106031 k s) = (term189 _106013 _106031 k s).
Proof. exact (@lem4407272 _106013 _106031 (term190 _106013 _106031 k s)). Qed.
Lemma lem4407274 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term191 _106013 _106031 k s i) = (term110 _106013 _106031 k s i).
Proof. exact (eq_refl (term191 _106013 _106031 k s i)). Qed.
Lemma lem4407275 {_106013 : Type'} (x : _106013) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4407276 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term192 _106013 _106031 k s i x) = (term193 _106013 _106031 k s i x).
Proof. exact (MK_COMB (@lem4407274 _106013 _106031 k s i) (@lem4407275 _106013 x)). Qed.
Lemma lem4407277 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term193 _106013 _106031 k s i x) = (term102 _106013 _106031 k s i x).
Proof. exact (eq_refl (term193 _106013 _106031 k s i x)). Qed.
Lemma lem4407278 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term192 _106013 _106031 k s i x) = (term102 _106013 _106031 k s i x).
Proof. exact (TRANS (@lem4407276 _106013 _106031 k s i x) (@lem4407277 _106013 _106031 k s i x)). Qed.
Lemma lem4407279 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term194 _106013 _106031 k s i) = (term110 _106013 _106031 k s i).
Proof. exact (fun_ext (fun x : _106013 => @lem4407278 _106013 _106031 k s i x)). Qed.
Lemma lem4407280 {_106013 : Type'} : (@ex _106013) = (@ex _106013).
Proof. exact (eq_refl (@ex _106013)). Qed.
Lemma lem4407281 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term195 _106013 _106031 k s i) = (term111 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407280 _106013) (@lem4407279 _106013 _106031 k s i)). Qed.
Lemma lem4407282 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term196 _106013 _106031 k s) = (term118 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407281 _106013 _106031 k s i)). Qed.
Lemma lem4407283 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4407284 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term188 _106013 _106031 k s) = (term119 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407283 _106031) (@lem4407282 _106013 _106031 k s)). Qed.
Lemma lem4407285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407286 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term197 _106013 _106031 k s) = (term198 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407285) (@lem4407284 _106013 _106031 k s)). Qed.
Lemma lem4407287 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term191 _106013 _106031 k s i) = (term110 _106013 _106031 k s i).
Proof. exact (eq_refl (term191 _106013 _106031 k s i)). Qed.
Lemma lem4407288 {_106013 _106031 : Type'} (x : _106031 -> _106013) (i : _106031) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem4407289 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (x : _106031 -> _106013) (i : _106031) : (term199 _106013 _106031 k s x i) = (term200 _106013 _106031 k s x i).
Proof. exact (MK_COMB (@lem4407287 _106013 _106031 k s i) (@lem4407288 _106013 _106031 x i)). Qed.
Lemma lem4407290 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (x : _106031 -> _106013) (i : _106031) : (term200 _106013 _106031 k s x i) = (term201 _106013 _106031 k s x i).
Proof. exact (eq_refl (term200 _106013 _106031 k s x i)). Qed.
Lemma lem4407291 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (x : _106031 -> _106013) (i : _106031) : (term199 _106013 _106031 k s x i) = (term201 _106013 _106031 k s x i).
Proof. exact (TRANS (@lem4407289 _106013 _106031 k s x i) (@lem4407290 _106013 _106031 k s x i)). Qed.
Lemma lem4407292 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (x : _106031 -> _106013) : (term202 _106013 _106031 k s x) = (term203 _106013 _106031 k s x).
Proof. exact (fun_ext (fun i : _106031 => @lem4407291 _106013 _106031 k s x i)). Qed.
Lemma lem4407293 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4407294 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (x : _106031 -> _106013) : (term204 _106013 _106031 k s x) = (term205 _106013 _106031 k s x).
Proof. exact (MK_COMB (@lem4407293 _106031) (@lem4407292 _106013 _106031 k s x)). Qed.
Lemma lem4407295 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term206 _106013 _106031 k s) = (term207 _106013 _106031 k s).
Proof. exact (fun_ext (fun x : _106031 -> _106013 => @lem4407294 _106013 _106031 k s x)). Qed.
Lemma lem4407296 {_106013 _106031 : Type'} : (@ex (_106031 -> _106013)) = (@ex (_106031 -> _106013)).
Proof. exact (eq_refl (@ex (_106031 -> _106013))). Qed.
Lemma lem4407297 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term189 _106013 _106031 k s) = (term208 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407296 _106013 _106031) (@lem4407295 _106013 _106031 k s)). Qed.
Lemma lem4407298 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term188 _106013 _106031 k s) = (term189 _106013 _106031 k s)) = ((term119 _106013 _106031 k s) = (term208 _106013 _106031 k s)).
Proof. exact (MK_COMB (@lem4407286 _106013 _106031 k s) (@lem4407297 _106013 _106031 k s)). Qed.
Lemma lem4407299 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term119 _106013 _106031 k s) = (term208 _106013 _106031 k s).
Proof. exact (EQ_MP (@lem4407298 _106013 _106031 k s) (@lem4407273 _106013 _106031 k s)). Qed.
Lemma lem4407300 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term99 _106013 _106031 k s) = (term208 _106013 _106031 k s).
Proof. exact (TRANS (@lem4407269 _106013 _106031 k s) (@lem4407299 _106013 _106031 k s)). Qed.
Lemma lem4407301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4407302 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term122 _106013 _106031 k s) = (term245 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407301) (@lem4407300 _106013 _106031 k s)). Qed.
Lemma lem4407303 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term47 _106013 _106031 k s) = (term47 _106013 _106031 k s).
Proof. exact (eq_refl (term47 _106013 _106031 k s)). Qed.
Lemma lem4407304 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term176 _106013 _106031 k s) = (term246 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407302 _106013 _106031 k s) (@lem4407303 _106013 _106031 k s)). Qed.
Lemma lem4407306 {A : Type'} (P : A -> Prop) (Q : Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4407307 {_106013 _106031 : Type'} (P : type805 _106013 _106031) (Q : Prop) : (term247 _106013 _106031 P Q) = (term248 _106013 _106031 P Q).
Proof. exact (@lem4407306 (_106031 -> _106013) P Q). Qed.
Lemma lem4407308 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term249 _106013 _106031 k s) = (term250 _106013 _106031 k s).
Proof. exact (@lem4407307 _106013 _106031 (term207 _106013 _106031 k s) (term47 _106013 _106031 k s)). Qed.
Lemma lem4407309 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (x : _106031 -> _106013) : (term232 _106013 _106031 k s x) = (term205 _106013 _106031 k s x).
Proof. exact (eq_refl (term232 _106013 _106031 k s x)). Qed.
Lemma lem4407310 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term233 _106013 _106031 k s) = (term207 _106013 _106031 k s).
Proof. exact (fun_ext (fun x : _106031 -> _106013 => @lem4407309 _106013 _106031 k s x)). Qed.
Lemma lem4407311 {_106013 _106031 : Type'} : (@ex (_106031 -> _106013)) = (@ex (_106031 -> _106013)).
Proof. exact (eq_refl (@ex (_106031 -> _106013))). Qed.
Lemma lem4407312 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term234 _106013 _106031 k s) = (term208 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407311 _106013 _106031) (@lem4407310 _106013 _106031 k s)). Qed.
Lemma lem4407313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4407314 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term251 _106013 _106031 k s) = (term245 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407313) (@lem4407312 _106013 _106031 k s)). Qed.
Lemma lem4407315 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term47 _106013 _106031 k s) = (term47 _106013 _106031 k s).
Proof. exact (eq_refl (term47 _106013 _106031 k s)). Qed.
Lemma lem4407316 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term249 _106013 _106031 k s) = (term246 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407314 _106013 _106031 k s) (@lem4407315 _106013 _106031 k s)). Qed.
Lemma lem4407317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407318 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term252 _106013 _106031 k s) = (term253 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407317) (@lem4407316 _106013 _106031 k s)). Qed.
Lemma lem4407319 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (x : _106031 -> _106013) : (term232 _106013 _106031 k s x) = (term205 _106013 _106031 k s x).
Proof. exact (eq_refl (term232 _106013 _106031 k s x)). Qed.
Lemma lem4407320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4407321 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (x : _106031 -> _106013) : (term254 _106013 _106031 k s x) = (term255 _106013 _106031 k s x).
Proof. exact (MK_COMB (@lem4407320) (@lem4407319 _106013 _106031 k s x)). Qed.
Lemma lem4407322 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term47 _106013 _106031 k s) = (term47 _106013 _106031 k s).
Proof. exact (eq_refl (term47 _106013 _106031 k s)). Qed.
Lemma lem4407323 {_106013 _106031 : Type'} (x : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term256 _106013 _106031 x k s) = (term257 _106013 _106031 x k s).
Proof. exact (MK_COMB (@lem4407321 _106013 _106031 k s x) (@lem4407322 _106013 _106031 k s)). Qed.
Lemma lem4407324 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term258 _106013 _106031 k s) = (term259 _106013 _106031 k s).
Proof. exact (fun_ext (fun x : _106031 -> _106013 => @lem4407323 _106013 _106031 x k s)). Qed.
Lemma lem4407325 {_106013 _106031 : Type'} : (@ex (_106031 -> _106013)) = (@ex (_106031 -> _106013)).
Proof. exact (eq_refl (@ex (_106031 -> _106013))). Qed.
Lemma lem4407326 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term250 _106013 _106031 k s) = (term260 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407325 _106013 _106031) (@lem4407324 _106013 _106031 k s)). Qed.
Lemma lem4407327 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term249 _106013 _106031 k s) = (term250 _106013 _106031 k s)) = ((term246 _106013 _106031 k s) = (term260 _106013 _106031 k s)).
Proof. exact (MK_COMB (@lem4407318 _106013 _106031 k s) (@lem4407326 _106013 _106031 k s)). Qed.
Lemma lem4407328 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term246 _106013 _106031 k s) = (term260 _106013 _106031 k s).
Proof. exact (EQ_MP (@lem4407327 _106013 _106031 k s) (@lem4407308 _106013 _106031 k s)). Qed.
Lemma lem4407330 {A : Type'} (P : Prop) (Q : A -> Prop) : (term226 A P Q) = (term227 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4407331 {_106031 : Type'} (P : Prop) (Q : _106031 -> Prop) : (term226 _106031 P Q) = (term227 _106031 P Q).
Proof. exact (@lem4407330 _106031 P Q). Qed.
Lemma lem4407332 {_106013 _106031 : Type'} (x : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term261 _106013 _106031 x k s) = (term262 _106013 _106031 x k s).
Proof. exact (@lem4407331 _106031 (term205 _106013 _106031 k s x) (term46 _106013 _106031 k s)). Qed.
Lemma lem4407333 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term95 _106013 _106031 k s i) = (term45 _106013 _106031 k s i).
Proof. exact (eq_refl (term95 _106013 _106031 k s i)). Qed.
Lemma lem4407334 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term214 _106013 _106031 k s) = (term46 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407333 _106013 _106031 k s i)). Qed.
Lemma lem4407335 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4407336 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term215 _106013 _106031 k s) = (term47 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407335 _106031) (@lem4407334 _106013 _106031 k s)). Qed.
Lemma lem4407337 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (x : _106031 -> _106013) : (term255 _106013 _106031 k s x) = (term255 _106013 _106031 k s x).
Proof. exact (eq_refl (term255 _106013 _106031 k s x)). Qed.
Lemma lem4407338 {_106013 _106031 : Type'} (x : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term261 _106013 _106031 x k s) = (term257 _106013 _106031 x k s).
Proof. exact (MK_COMB (@lem4407337 _106013 _106031 k s x) (@lem4407336 _106013 _106031 k s)). Qed.
Lemma lem4407339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407340 {_106013 _106031 : Type'} (x : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term263 _106013 _106031 x k s) = (term264 _106013 _106031 x k s).
Proof. exact (MK_COMB (@lem4407339) (@lem4407338 _106013 _106031 x k s)). Qed.
Lemma lem4407341 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term95 _106013 _106031 k s i) = (term45 _106013 _106031 k s i).
Proof. exact (eq_refl (term95 _106013 _106031 k s i)). Qed.
Lemma lem4407342 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (x : _106031 -> _106013) : (term255 _106013 _106031 k s x) = (term255 _106013 _106031 k s x).
Proof. exact (eq_refl (term255 _106013 _106031 k s x)). Qed.
Lemma lem4407343 {_106013 _106031 : Type'} (x : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term265 _106013 _106031 x k s i) = (term266 _106013 _106031 x k s i).
Proof. exact (MK_COMB (@lem4407342 _106013 _106031 k s x) (@lem4407341 _106013 _106031 k s i)). Qed.
Lemma lem4407344 {_106013 _106031 : Type'} (x : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term267 _106013 _106031 x k s) = (term268 _106013 _106031 x k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407343 _106013 _106031 x k s i)). Qed.
Lemma lem4407345 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4407346 {_106013 _106031 : Type'} (x : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term262 _106013 _106031 x k s) = (term269 _106013 _106031 x k s).
Proof. exact (MK_COMB (@lem4407345 _106031) (@lem4407344 _106013 _106031 x k s)). Qed.
Lemma lem4407347 {_106013 _106031 : Type'} (x : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term261 _106013 _106031 x k s) = (term262 _106013 _106031 x k s)) = ((term257 _106013 _106031 x k s) = (term269 _106013 _106031 x k s)).
Proof. exact (MK_COMB (@lem4407340 _106013 _106031 x k s) (@lem4407346 _106013 _106031 x k s)). Qed.
Lemma lem4407348 {_106013 _106031 : Type'} (x : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term257 _106013 _106031 x k s) = (term269 _106013 _106031 x k s).
Proof. exact (EQ_MP (@lem4407347 _106013 _106031 x k s) (@lem4407332 _106013 _106031 x k s)). Qed.
Lemma lem4407349 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term259 _106013 _106031 k s) = (term270 _106013 _106031 k s).
Proof. exact (fun_ext (fun x : _106031 -> _106013 => @lem4407348 _106013 _106031 x k s)). Qed.
Lemma lem4407350 {_106013 _106031 : Type'} : (@ex (_106031 -> _106013)) = (@ex (_106031 -> _106013)).
Proof. exact (eq_refl (@ex (_106031 -> _106013))). Qed.
Lemma lem4407351 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term260 _106013 _106031 k s) = (term271 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407350 _106013 _106031) (@lem4407349 _106013 _106031 k s)). Qed.
Lemma lem4407352 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term246 _106013 _106031 k s) = (term271 _106013 _106031 k s).
Proof. exact (TRANS (@lem4407328 _106013 _106031 k s) (@lem4407351 _106013 _106031 k s)). Qed.
Lemma lem4407353 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term176 _106013 _106031 k s) = (term271 _106013 _106031 k s).
Proof. exact (TRANS (@lem4407304 _106013 _106031 k s) (@lem4407352 _106013 _106031 k s)). Qed.
Lemma lem4407354 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term177 _106013 _106031 k s) = (term272 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407246 _106013 _106031 k s) (@lem4407353 _106013 _106031 k s)). Qed.
Lemma lem4407358 {A : Type'} (P : A -> Prop) (Q : Prop) : (term273 A P Q) = (term274 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4407359 {_106031 : Type'} (P : _106031 -> Prop) (Q : Prop) : (term273 _106031 P Q) = (term274 _106031 P Q).
Proof. exact (@lem4407358 _106031 P Q). Qed.
Lemma lem4407360 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term275 _106013 _106031 k s) = (term276 _106013 _106031 k s).
Proof. exact (@lem4407359 _106031 (term242 _106013 _106031 k s) (term271 _106013 _106031 k s)). Qed.
Lemma lem4407361 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term277 _106013 _106031 k s i) = (term241 _106013 _106031 i k s).
Proof. exact (eq_refl (term277 _106013 _106031 k s i)). Qed.
Lemma lem4407362 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term278 _106013 _106031 k s) = (term242 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407361 _106013 _106031 i k s)). Qed.
Lemma lem4407363 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4407364 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term279 _106013 _106031 k s) = (term243 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407363 _106031) (@lem4407362 _106013 _106031 k s)). Qed.
Lemma lem4407365 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4407366 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term280 _106013 _106031 k s) = (term244 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407365) (@lem4407364 _106013 _106031 k s)). Qed.
Lemma lem4407367 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term271 _106013 _106031 k s) = (term271 _106013 _106031 k s).
Proof. exact (eq_refl (term271 _106013 _106031 k s)). Qed.
Lemma lem4407368 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term275 _106013 _106031 k s) = (term272 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407366 _106013 _106031 k s) (@lem4407367 _106013 _106031 k s)). Qed.
Lemma lem4407369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407370 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term281 _106013 _106031 k s) = (term282 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407369) (@lem4407368 _106013 _106031 k s)). Qed.
Lemma lem4407371 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term277 _106013 _106031 k s i) = (term241 _106013 _106031 i k s).
Proof. exact (eq_refl (term277 _106013 _106031 k s i)). Qed.
Lemma lem4407372 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4407373 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term283 _106013 _106031 k s i) = (term284 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407372) (@lem4407371 _106013 _106031 i k s)). Qed.
Lemma lem4407374 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term271 _106013 _106031 k s) = (term271 _106013 _106031 k s).
Proof. exact (eq_refl (term271 _106013 _106031 k s)). Qed.
Lemma lem4407375 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term285 _106013 _106031 i k s) = (term286 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407373 _106013 _106031 i k s) (@lem4407374 _106013 _106031 k s)). Qed.
Lemma lem4407376 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term287 _106013 _106031 k s) = (term288 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407375 _106013 _106031 i k s)). Qed.
Lemma lem4407377 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4407378 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term276 _106013 _106031 k s) = (term289 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407377 _106031) (@lem4407376 _106013 _106031 k s)). Qed.
Lemma lem4407379 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term275 _106013 _106031 k s) = (term276 _106013 _106031 k s)) = ((term272 _106013 _106031 k s) = (term289 _106013 _106031 k s)).
Proof. exact (MK_COMB (@lem4407370 _106013 _106031 k s) (@lem4407378 _106013 _106031 k s)). Qed.
Lemma lem4407380 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term272 _106013 _106031 k s) = (term289 _106013 _106031 k s).
Proof. exact (EQ_MP (@lem4407379 _106013 _106031 k s) (@lem4407360 _106013 _106031 k s)). Qed.
Lemma lem4407382 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term133 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4407383 {_106013 _106031 : Type'} (P : type805 _106013 _106031) (Q : type805 _106013 _106031) : (term290 _106013 _106031 P Q) = (term291 _106013 _106031 P Q).
Proof. exact (@lem4407382 (_106031 -> _106013) P Q). Qed.
Lemma lem4407384 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term292 _106013 _106031 i k s) = (term293 _106013 _106031 i k s).
Proof. exact (@lem4407383 _106013 _106031 (term240 _106013 _106031 i k s) (term270 _106013 _106031 k s)). Qed.
Lemma lem4407385 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term294 _106013 _106031 i k s a) = (term238 _106013 _106031 i k s a).
Proof. exact (eq_refl (term294 _106013 _106031 i k s a)). Qed.
Lemma lem4407386 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term295 _106013 _106031 i k s) = (term240 _106013 _106031 i k s).
Proof. exact (fun_ext (fun a : _106031 -> _106013 => @lem4407385 _106013 _106031 i k s a)). Qed.
Lemma lem4407387 {_106013 _106031 : Type'} : (@ex (_106031 -> _106013)) = (@ex (_106031 -> _106013)).
Proof. exact (eq_refl (@ex (_106031 -> _106013))). Qed.
Lemma lem4407388 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term296 _106013 _106031 i k s) = (term241 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407387 _106013 _106031) (@lem4407386 _106013 _106031 i k s)). Qed.
Lemma lem4407389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4407390 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term297 _106013 _106031 i k s) = (term284 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407389) (@lem4407388 _106013 _106031 i k s)). Qed.
Lemma lem4407391 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term298 _106013 _106031 k s a) = (term269 _106013 _106031 a k s).
Proof. exact (eq_refl (term298 _106013 _106031 k s a)). Qed.
Lemma lem4407392 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term299 _106013 _106031 k s) = (term270 _106013 _106031 k s).
Proof. exact (fun_ext (fun a : _106031 -> _106013 => @lem4407391 _106013 _106031 a k s)). Qed.
Lemma lem4407393 {_106013 _106031 : Type'} : (@ex (_106031 -> _106013)) = (@ex (_106031 -> _106013)).
Proof. exact (eq_refl (@ex (_106031 -> _106013))). Qed.
Lemma lem4407394 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term300 _106013 _106031 k s) = (term271 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407393 _106013 _106031) (@lem4407392 _106013 _106031 k s)). Qed.
Lemma lem4407395 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term292 _106013 _106031 i k s) = (term286 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407390 _106013 _106031 i k s) (@lem4407394 _106013 _106031 k s)). Qed.
Lemma lem4407396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407397 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term301 _106013 _106031 i k s) = (term302 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407396) (@lem4407395 _106013 _106031 i k s)). Qed.
Lemma lem4407398 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term294 _106013 _106031 i k s a) = (term238 _106013 _106031 i k s a).
Proof. exact (eq_refl (term294 _106013 _106031 i k s a)). Qed.
Lemma lem4407399 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4407400 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term303 _106013 _106031 i k s a) = (term304 _106013 _106031 i k s a).
Proof. exact (MK_COMB (@lem4407399) (@lem4407398 _106013 _106031 i k s a)). Qed.
Lemma lem4407401 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term298 _106013 _106031 k s a) = (term269 _106013 _106031 a k s).
Proof. exact (eq_refl (term298 _106013 _106031 k s a)). Qed.
Lemma lem4407402 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term305 _106013 _106031 i k s a) = (term306 _106013 _106031 i a k s).
Proof. exact (MK_COMB (@lem4407400 _106013 _106031 i k s a) (@lem4407401 _106013 _106031 a k s)). Qed.
Lemma lem4407403 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term307 _106013 _106031 i k s) = (term308 _106013 _106031 i k s).
Proof. exact (fun_ext (fun a : _106031 -> _106013 => @lem4407402 _106013 _106031 i a k s)). Qed.
Lemma lem4407404 {_106013 _106031 : Type'} : (@ex (_106031 -> _106013)) = (@ex (_106031 -> _106013)).
Proof. exact (eq_refl (@ex (_106031 -> _106013))). Qed.
Lemma lem4407405 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term293 _106013 _106031 i k s) = (term309 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407404 _106013 _106031) (@lem4407403 _106013 _106031 i k s)). Qed.
Lemma lem4407406 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term292 _106013 _106031 i k s) = (term293 _106013 _106031 i k s)) = ((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s)).
Proof. exact (MK_COMB (@lem4407397 _106013 _106031 i k s) (@lem4407405 _106013 _106031 i k s)). Qed.
Lemma lem4407407 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s).
Proof. exact (EQ_MP (@lem4407406 _106013 _106031 i k s) (@lem4407384 _106013 _106031 i k s)). Qed.
Lemma lem4407410 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term310 _106013 _106031 i k s) = (term310 _106013 _106031 i k s).
Proof. exact (eq_refl (term310 _106013 _106031 i k s)). Qed.
Lemma lem4407411 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term310 _106013 _106031 i k s) = ((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s)).
Proof. exact (eq_refl (term310 _106013 _106031 i k s)). Qed.
Lemma lem4407412 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term311 _106013 _106031 i k s) = (term311 _106013 _106031 i k s).
Proof. exact (eq_refl (term311 _106013 _106031 i k s)). Qed.
Lemma lem4407413 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term310 _106013 _106031 i k s) = (term310 _106013 _106031 i k s)) = ((term310 _106013 _106031 i k s) = ((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s))).
Proof. exact (MK_COMB (@lem4407412 _106013 _106031 i k s) (@lem4407411 _106013 _106031 i k s)). Qed.
Lemma lem4407414 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term310 _106013 _106031 i k s) = ((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s)).
Proof. exact (eq_refl (term310 _106013 _106031 i k s)). Qed.
Lemma lem4407415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407416 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term311 _106013 _106031 i k s) = (term312 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407415) (@lem4407414 _106013 _106031 i k s)). Qed.
Lemma lem4407417 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s)) = ((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s)).
Proof. exact (eq_refl ((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s))). Qed.
Lemma lem4407418 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term310 _106013 _106031 i k s) = ((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s))) = (((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s)) = ((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s))).
Proof. exact (MK_COMB (@lem4407416 _106013 _106031 i k s) (@lem4407417 _106013 _106031 i k s)). Qed.
Lemma lem4407419 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term310 _106013 _106031 i k s) = (term310 _106013 _106031 i k s)) = (((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s)) = ((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s))).
Proof. exact (TRANS (@lem4407413 _106013 _106031 i k s) (@lem4407418 _106013 _106031 i k s)). Qed.
Lemma lem4407420 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s)) = ((term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s)).
Proof. exact (EQ_MP (@lem4407419 _106013 _106031 i k s) (@lem4407410 _106013 _106031 i k s)). Qed.
Lemma lem4407421 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term286 _106013 _106031 i k s) = (term309 _106013 _106031 i k s).
Proof. exact (EQ_MP (@lem4407420 _106013 _106031 i k s) (@lem4407407 _106013 _106031 i k s)). Qed.
Lemma lem4407423 {A : Type'} (P : Prop) (Q : A -> Prop) : (term178 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4407424 {_106031 : Type'} (P : Prop) (Q : _106031 -> Prop) : (term178 _106031 P Q) = (term179 _106031 P Q).
Proof. exact (@lem4407423 _106031 P Q). Qed.
Lemma lem4407425 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term313 _106013 _106031 i a k s) = (term314 _106013 _106031 i a k s).
Proof. exact (@lem4407424 _106031 (term238 _106013 _106031 i k s a) (term268 _106013 _106031 a k s)). Qed.
Lemma lem4407426 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term315 _106013 _106031 a k s i) = (term266 _106013 _106031 a k s i).
Proof. exact (eq_refl (term315 _106013 _106031 a k s i)). Qed.
Lemma lem4407427 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term316 _106013 _106031 a k s) = (term268 _106013 _106031 a k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407426 _106013 _106031 a k s i)). Qed.
Lemma lem4407428 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4407429 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term317 _106013 _106031 a k s) = (term269 _106013 _106031 a k s).
Proof. exact (MK_COMB (@lem4407428 _106031) (@lem4407427 _106013 _106031 a k s)). Qed.
Lemma lem4407430 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term304 _106013 _106031 i k s a) = (term304 _106013 _106031 i k s a).
Proof. exact (eq_refl (term304 _106013 _106031 i k s a)). Qed.
Lemma lem4407431 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term313 _106013 _106031 i a k s) = (term306 _106013 _106031 i a k s).
Proof. exact (MK_COMB (@lem4407430 _106013 _106031 i k s a) (@lem4407429 _106013 _106031 a k s)). Qed.
Lemma lem4407432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407433 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term318 _106013 _106031 i a k s) = (term319 _106013 _106031 i a k s).
Proof. exact (MK_COMB (@lem4407432) (@lem4407431 _106013 _106031 i a k s)). Qed.
Lemma lem4407434 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) : (term315 _106013 _106031 a k s i') = (term266 _106013 _106031 a k s i').
Proof. exact (eq_refl (term315 _106013 _106031 a k s i')). Qed.
Lemma lem4407435 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term304 _106013 _106031 i k s a) = (term304 _106013 _106031 i k s a).
Proof. exact (eq_refl (term304 _106013 _106031 i k s a)). Qed.
Lemma lem4407436 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) : (term320 _106013 _106031 i a k s i') = (term321 _106013 _106031 i a k s i').
Proof. exact (MK_COMB (@lem4407435 _106013 _106031 i k s a) (@lem4407434 _106013 _106031 a k s i')). Qed.
Lemma lem4407437 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term322 _106013 _106031 i a k s) = (term323 _106013 _106031 i a k s).
Proof. exact (fun_ext (fun i' : _106031 => @lem4407436 _106013 _106031 i a k s i')). Qed.
Lemma lem4407438 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4407439 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term314 _106013 _106031 i a k s) = (term324 _106013 _106031 i a k s).
Proof. exact (MK_COMB (@lem4407438 _106031) (@lem4407437 _106013 _106031 i a k s)). Qed.
Lemma lem4407440 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : ((term313 _106013 _106031 i a k s) = (term314 _106013 _106031 i a k s)) = ((term306 _106013 _106031 i a k s) = (term324 _106013 _106031 i a k s)).
Proof. exact (MK_COMB (@lem4407433 _106013 _106031 i a k s) (@lem4407439 _106013 _106031 i a k s)). Qed.
Lemma lem4407441 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term306 _106013 _106031 i a k s) = (term324 _106013 _106031 i a k s).
Proof. exact (EQ_MP (@lem4407440 _106013 _106031 i a k s) (@lem4407425 _106013 _106031 i a k s)). Qed.
Lemma lem4407442 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term308 _106013 _106031 i k s) = (term325 _106013 _106031 i k s).
Proof. exact (fun_ext (fun a : _106031 -> _106013 => @lem4407441 _106013 _106031 i a k s)). Qed.
Lemma lem4407443 {_106013 _106031 : Type'} : (@ex (_106031 -> _106013)) = (@ex (_106031 -> _106013)).
Proof. exact (eq_refl (@ex (_106031 -> _106013))). Qed.
Lemma lem4407444 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term309 _106013 _106031 i k s) = (term326 _106013 _106031 i k s).
Proof. exact (MK_COMB (@lem4407443 _106013 _106031) (@lem4407442 _106013 _106031 i k s)). Qed.
Lemma lem4407445 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term286 _106013 _106031 i k s) = (term326 _106013 _106031 i k s).
Proof. exact (TRANS (@lem4407421 _106013 _106031 i k s) (@lem4407444 _106013 _106031 i k s)). Qed.
Lemma lem4407446 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term288 _106013 _106031 k s) = (term327 _106013 _106031 k s).
Proof. exact (fun_ext (fun i : _106031 => @lem4407445 _106013 _106031 i k s)). Qed.
Lemma lem4407447 {_106031 : Type'} : (@ex _106031) = (@ex _106031).
Proof. exact (eq_refl (@ex _106031)). Qed.
Lemma lem4407448 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term289 _106013 _106031 k s) = (term328 _106013 _106031 k s).
Proof. exact (MK_COMB (@lem4407447 _106031) (@lem4407446 _106013 _106031 k s)). Qed.
Lemma lem4407449 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term272 _106013 _106031 k s) = (term328 _106013 _106031 k s).
Proof. exact (TRANS (@lem4407380 _106013 _106031 k s) (@lem4407448 _106013 _106031 k s)). Qed.
Lemma lem4407450 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term177 _106013 _106031 k s) = (term328 _106013 _106031 k s).
Proof. exact (TRANS (@lem4407354 _106013 _106031 k s) (@lem4407449 _106013 _106031 k s)). Qed.
Lemma lem4407451 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term131 _106013 _106031 k s) = (term328 _106013 _106031 k s).
Proof. exact (TRANS (@lem4407139 _106013 _106031 k s) (@lem4407450 _106013 _106031 k s)). Qed.
Lemma lem4407452 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term64 _106013 _106031 k s) = (term328 _106013 _106031 k s).
Proof. exact (TRANS (@lem4406878 _106013 _106031 k s) (@lem4407451 _106013 _106031 k s)). Qed.
Lemma lem4407453 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term64 _106013 _106031 k s) : term328 _106013 _106031 k s.
Proof. exact (EQ_MP (@lem4407452 _106013 _106031 k s) (@lem4406785 _106013 _106031 k s h1)). Qed.
Lemma lem4407454 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term326 _106013 _106031 i k s) : term326 _106013 _106031 i k s.
Proof. exact (h1). Qed.
Lemma lem4407455 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term324 _106013 _106031 i a k s) : term324 _106013 _106031 i a k s.
Proof. exact (h1). Qed.
Lemma lem4407456 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term321 _106013 _106031 i a k s i') : term321 _106013 _106031 i a k s i'.
Proof. exact (h1). Qed.
Lemma lem4407463 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i' : _106031) (a : _106013) : (term41 _106013 _106031 s i' a) = (term41 _106013 _106031 s i' a).
Proof. exact (eq_refl (term41 _106013 _106031 s i' a)). Qed.
Lemma lem4407464 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i' : _106031) : (term43 _106013 _106031 s i') = (term43 _106013 _106031 s i').
Proof. exact (fun_ext (fun a : _106013 => @lem4407463 _106013 _106031 s i' a)). Qed.
Lemma lem4407465 {_106013 : Type'} : (@all _106013) = (@all _106013).
Proof. exact (eq_refl (@all _106013)). Qed.
Lemma lem4407466 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i' : _106031) : (term44 _106013 _106031 s i') = (term44 _106013 _106031 s i').
Proof. exact (MK_COMB (@lem4407465 _106013) (@lem4407464 _106013 _106031 s i')). Qed.
Lemma lem4407471 {_106031 : Type'} (k : _106031 -> Prop) (i' : _106031) : (term37 _106031 k i') = (term37 _106031 k i').
Proof. exact (eq_refl (term37 _106031 k i')). Qed.
Lemma lem4407472 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) : (term45 _106013 _106031 k s i') = (term45 _106013 _106031 k s i').
Proof. exact (MK_COMB (@lem4407471 _106031 k i') (@lem4407466 _106013 _106031 s i')). Qed.
Lemma lem4407487 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (i : _106031) : (term201 _106013 _106031 k s a i) = (term201 _106013 _106031 k s a i).
Proof. exact (eq_refl (term201 _106013 _106031 k s a i)). Qed.
Lemma lem4407488 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term203 _106013 _106031 k s a) = (term203 _106013 _106031 k s a).
Proof. exact (fun_ext (fun i : _106031 => @lem4407487 _106013 _106031 k s a i)). Qed.
Lemma lem4407489 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4407490 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term205 _106013 _106031 k s a) = (term205 _106013 _106031 k s a).
Proof. exact (MK_COMB (@lem4407489 _106031) (@lem4407488 _106013 _106031 k s a)). Qed.
Lemma lem4407491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4407492 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term255 _106013 _106031 k s a) = (term255 _106013 _106031 k s a).
Proof. exact (MK_COMB (@lem4407491) (@lem4407490 _106013 _106031 k s a)). Qed.
Lemma lem4407493 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) : (term266 _106013 _106031 a k s i') = (term266 _106013 _106031 a k s i').
Proof. exact (MK_COMB (@lem4407492 _106013 _106031 k s a) (@lem4407472 _106013 _106031 k s i')). Qed.
Lemma lem4407508 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (i : _106031) : (term201 _106013 _106031 k s a i) = (term201 _106013 _106031 k s a i).
Proof. exact (eq_refl (term201 _106013 _106031 k s a i)). Qed.
Lemma lem4407509 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term203 _106013 _106031 k s a) = (term203 _106013 _106031 k s a).
Proof. exact (fun_ext (fun i : _106031 => @lem4407508 _106013 _106031 k s a i)). Qed.
Lemma lem4407510 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4407511 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term205 _106013 _106031 k s a) = (term205 _106013 _106031 k s a).
Proof. exact (MK_COMB (@lem4407510 _106031) (@lem4407509 _106013 _106031 k s a)). Qed.
Lemma lem4407518 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term41 _106013 _106031 s i x) = (term41 _106013 _106031 s i x).
Proof. exact (eq_refl (term41 _106013 _106031 s i x)). Qed.
Lemma lem4407519 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term43 _106013 _106031 s i) = (term43 _106013 _106031 s i).
Proof. exact (fun_ext (fun x : _106013 => @lem4407518 _106013 _106031 s i x)). Qed.
Lemma lem4407520 {_106013 : Type'} : (@all _106013) = (@all _106013).
Proof. exact (eq_refl (@all _106013)). Qed.
Lemma lem4407521 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term44 _106013 _106031 s i) = (term44 _106013 _106031 s i).
Proof. exact (MK_COMB (@lem4407520 _106013) (@lem4407519 _106013 _106031 s i)). Qed.
Lemma lem4407526 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term37 _106031 k i) = (term37 _106031 k i).
Proof. exact (eq_refl (term37 _106031 k i)). Qed.
Lemma lem4407527 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term45 _106013 _106031 k s i) = (term45 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407526 _106031 k i) (@lem4407521 _106013 _106031 s i)). Qed.
Lemma lem4407528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4407529 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i : _106031) : (term220 _106013 _106031 k s i) = (term220 _106013 _106031 k s i).
Proof. exact (MK_COMB (@lem4407528) (@lem4407527 _106013 _106031 k s i)). Qed.
Lemma lem4407530 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term238 _106013 _106031 i k s a) = (term238 _106013 _106031 i k s a).
Proof. exact (MK_COMB (@lem4407529 _106013 _106031 k s i) (@lem4407511 _106013 _106031 k s a)). Qed.
Lemma lem4407531 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4407532 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term304 _106013 _106031 i k s a) = (term304 _106013 _106031 i k s a).
Proof. exact (MK_COMB (@lem4407531) (@lem4407530 _106013 _106031 i k s a)). Qed.
Lemma lem4407533 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) : (term321 _106013 _106031 i a k s i') = (term321 _106013 _106031 i a k s i').
Proof. exact (MK_COMB (@lem4407532 _106013 _106031 i k s a) (@lem4407493 _106013 _106031 a k s i')). Qed.
Lemma lem4407534 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term321 _106013 _106031 i a k s i') : term321 _106013 _106031 i a k s i'.
Proof. exact (EQ_MP (@lem4407533 _106013 _106031 i a k s i') (@lem4407456 _106013 _106031 i a k s i' h1)). Qed.
Lemma lem4407535 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term238 _106013 _106031 i k s a.
Proof. exact (h1). Qed.
Lemma lem4407536 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term266 _106013 _106031 a k s i'.
Proof. exact (h1). Qed.
Lemma lem4407537 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term205 _106013 _106031 k s a.
Proof. exact (proj2 (@lem4407535 _106013 _106031 i k s a h1)). Qed.
Lemma lem4407538 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term45 _106013 _106031 k s i.
Proof. exact (proj1 (@lem4407535 _106013 _106031 i k s a h1)). Qed.
Lemma lem4407539 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term44 _106013 _106031 s i.
Proof. exact (proj2 (@lem4407538 _106013 _106031 i k s a h1)). Qed.
Lemma lem4407541 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term45 _106013 _106031 k s i'.
Proof. exact (proj2 (@lem4407536 _106013 _106031 a k s i' h1)). Qed.
Lemma lem4407542 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term205 _106013 _106031 k s a.
Proof. exact (proj1 (@lem4407536 _106013 _106031 a k s i' h1)). Qed.
Lemma lem4407543 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term44 _106013 _106031 s i'.
Proof. exact (proj2 (@lem4407541 _106013 _106031 a k s i' h1)). Qed.
Lemma lem4407552 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (i : _106031) : (term201 _106013 _106031 k s a i) = (term201 _106013 _106031 k s a i).
Proof. exact (eq_refl (term201 _106013 _106031 k s a i)). Qed.
Lemma lem4407553 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term203 _106013 _106031 k s a) = (term203 _106013 _106031 k s a).
Proof. exact (fun_ext (fun i : _106031 => @lem4407552 _106013 _106031 k s a i)). Qed.
Lemma lem4407554 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4407556 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term205 _106013 _106031 k s a) = (term205 _106013 _106031 k s a).
Proof. exact (MK_COMB (@lem4407554 _106031) (@lem4407553 _106013 _106031 k s a)). Qed.
Lemma lem4407557 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term205 _106013 _106031 k s a.
Proof. exact (EQ_MP (@lem4407556 _106013 _106031 k s a) (@lem4407537 _106013 _106031 i k s a h1)). Qed.
Lemma lem4407563 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (x : _106013) : (term41 _106013 _106031 s i x) = (term41 _106013 _106031 s i x).
Proof. exact (eq_refl (term41 _106013 _106031 s i x)). Qed.
Lemma lem4407564 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term43 _106013 _106031 s i) = (term43 _106013 _106031 s i).
Proof. exact (fun_ext (fun x : _106013 => @lem4407563 _106013 _106031 s i x)). Qed.
Lemma lem4407565 {_106013 : Type'} : (@all _106013) = (@all _106013).
Proof. exact (eq_refl (@all _106013)). Qed.
Lemma lem4407567 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) : (term44 _106013 _106031 s i) = (term44 _106013 _106031 s i).
Proof. exact (MK_COMB (@lem4407565 _106013) (@lem4407564 _106013 _106031 s i)). Qed.
Lemma lem4407568 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term44 _106013 _106031 s i.
Proof. exact (EQ_MP (@lem4407567 _106013 _106031 s i) (@lem4407539 _106013 _106031 i k s a h1)). Qed.
Lemma lem4407576 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (i : _106031) : (term201 _106013 _106031 k s a i) = (term201 _106013 _106031 k s a i).
Proof. exact (eq_refl (term201 _106013 _106031 k s a i)). Qed.
Lemma lem4407577 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term203 _106013 _106031 k s a) = (term203 _106013 _106031 k s a).
Proof. exact (fun_ext (fun i : _106031 => @lem4407576 _106013 _106031 k s a i)). Qed.
Lemma lem4407578 {_106031 : Type'} : (@all _106031) = (@all _106031).
Proof. exact (eq_refl (@all _106031)). Qed.
Lemma lem4407580 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) : (term205 _106013 _106031 k s a) = (term205 _106013 _106031 k s a).
Proof. exact (MK_COMB (@lem4407578 _106031) (@lem4407577 _106013 _106031 k s a)). Qed.
Lemma lem4407581 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term205 _106013 _106031 k s a.
Proof. exact (EQ_MP (@lem4407580 _106013 _106031 k s a) (@lem4407542 _106013 _106031 a k s i' h1)). Qed.
Lemma lem4407587 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i' : _106031) (a : _106013) : (term41 _106013 _106031 s i' a) = (term41 _106013 _106031 s i' a).
Proof. exact (eq_refl (term41 _106013 _106031 s i' a)). Qed.
Lemma lem4407588 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i' : _106031) : (term43 _106013 _106031 s i') = (term43 _106013 _106031 s i').
Proof. exact (fun_ext (fun a : _106013 => @lem4407587 _106013 _106031 s i' a)). Qed.
Lemma lem4407589 {_106013 : Type'} : (@all _106013) = (@all _106013).
Proof. exact (eq_refl (@all _106013)). Qed.
Lemma lem4407591 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i' : _106031) : (term44 _106013 _106031 s i') = (term44 _106013 _106031 s i').
Proof. exact (MK_COMB (@lem4407589 _106013) (@lem4407588 _106013 _106031 s i')). Qed.
Lemma lem4407592 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term44 _106013 _106031 s i'.
Proof. exact (EQ_MP (@lem4407591 _106013 _106031 s i') (@lem4407543 _106013 _106031 a k s i' h1)). Qed.
Lemma lem4407593 {_106013 _106031 : Type'} (_50447 : _106031) (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term329 _106013 _106031 k s a _50447.
Proof. exact (@lem4407557 _106013 _106031 i k s a h1 _50447). Qed.
Lemma lem4407594 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (_50447 : _106031) : (term329 _106013 _106031 k s a _50447) = (term201 _106013 _106031 k s a _50447).
Proof. exact (eq_refl (term329 _106013 _106031 k s a _50447)). Qed.
Lemma lem4407596 {_106013 _106031 : Type'} (_50448 : _106013) (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term83 _106013 _106031 s i _50448.
Proof. exact (@lem4407568 _106013 _106031 i k s a h1 _50448). Qed.
Lemma lem4407597 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (_50448 : _106013) : (term83 _106013 _106031 s i _50448) = (term41 _106013 _106031 s i _50448).
Proof. exact (eq_refl (term83 _106013 _106031 s i _50448)). Qed.
Lemma lem4407599 {_106013 _106031 : Type'} (_50449 : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term329 _106013 _106031 k s a _50449.
Proof. exact (@lem4407581 _106013 _106031 a k s i' h1 _50449). Qed.
Lemma lem4407600 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (_50449 : _106031) : (term329 _106013 _106031 k s a _50449) = (term201 _106013 _106031 k s a _50449).
Proof. exact (eq_refl (term329 _106013 _106031 k s a _50449)). Qed.
Lemma lem4407602 {_106013 _106031 : Type'} (_50450 : _106013) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term83 _106013 _106031 s i' _50450.
Proof. exact (@lem4407592 _106013 _106031 a k s i' h1 _50450). Qed.
Lemma lem4407603 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i' : _106031) (_50450 : _106013) : (term83 _106013 _106031 s i' _50450) = (term41 _106013 _106031 s i' _50450).
Proof. exact (eq_refl (term83 _106013 _106031 s i' _50450)). Qed.
Lemma lem4407610 {_106013 _106031 : Type'} (_50447 : _106031) (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term201 _106013 _106031 k s a _50447.
Proof. exact (EQ_MP (@lem4407594 _106013 _106031 k s a _50447) (@lem4407593 _106013 _106031 _50447 i k s a h1)). Qed.
Lemma lem4407614 {_106013 _106031 : Type'} (_50448 : _106013) (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term41 _106013 _106031 s i _50448.
Proof. exact (EQ_MP (@lem4407597 _106013 _106031 s i _50448) (@lem4407596 _106013 _106031 _50448 i k s a h1)). Qed.
Lemma lem4407620 {_106013 _106031 : Type'} (_50449 : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term201 _106013 _106031 k s a _50449.
Proof. exact (EQ_MP (@lem4407600 _106013 _106031 k s a _50449) (@lem4407599 _106013 _106031 _50449 a k s i' h1)). Qed.
Lemma lem4407624 {_106013 _106031 : Type'} (_50450 : _106013) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term41 _106013 _106031 s i' _50450.
Proof. exact (EQ_MP (@lem4407603 _106013 _106031 s i' _50450) (@lem4407602 _106013 _106031 _50450 a k s i' h1)). Qed.
Lemma lem4407626 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : k i.
Proof. exact (proj1 (@lem4407538 _106013 _106031 i k s a h1)). Qed.
Lemma lem4407627 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term330 _106031 k i.
Proof. exact (fun h0 : term138 _106031 k i => @lem4407626 _106013 _106031 i k s a h1). Qed.
Lemma lem4407629 (p : Prop) : (term331 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4407630 {_106031 : Type'} (k : _106031 -> Prop) (i : _106031) : (term330 _106031 k i) = (k i).
Proof. exact (@lem4407629 (k i)). Qed.
Lemma lem4407631 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : k i.
Proof. exact (EQ_MP (@lem4407630 _106031 k i) (@lem4407627 _106013 _106031 i k s a h1)). Qed.
Lemma lem4407637 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4407638 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50447 : _106031) : (term201 _106013 _106031 k s a _50447) = (term332 _106013 _106031 s a k _50447).
Proof. exact (@lem4407637 (term333 _106013 _106031 s a _50447) (term138 _106031 k _50447)). Qed.
Lemma lem4407644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407645 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50447 : _106031) : (term334 _106013 _106031 k s a _50447) = (term335 _106013 _106031 s a k _50447).
Proof. exact (MK_COMB (@lem4407644) (@lem4407638 _106013 _106031 s a k _50447)). Qed.
Lemma lem4407651 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50447 : _106031) : (term332 _106013 _106031 s a k _50447) = (term332 _106013 _106031 s a k _50447).
Proof. exact (eq_refl (term332 _106013 _106031 s a k _50447)). Qed.
Lemma lem4407652 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50447 : _106031) : ((term201 _106013 _106031 k s a _50447) = (term332 _106013 _106031 s a k _50447)) = ((term332 _106013 _106031 s a k _50447) = (term332 _106013 _106031 s a k _50447)).
Proof. exact (MK_COMB (@lem4407645 _106013 _106031 s a k _50447) (@lem4407651 _106013 _106031 s a k _50447)). Qed.
Lemma lem4407654 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4407655 (x : Prop) : (x = x) = True.
Proof. exact (@lem4407654 Prop x). Qed.
Lemma lem4407656 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50447 : _106031) : ((term332 _106013 _106031 s a k _50447) = (term332 _106013 _106031 s a k _50447)) = True.
Proof. exact (@lem4407655 (term332 _106013 _106031 s a k _50447)). Qed.
Lemma lem4407657 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50447 : _106031) : ((term201 _106013 _106031 k s a _50447) = (term332 _106013 _106031 s a k _50447)) = True.
Proof. exact (TRANS (@lem4407652 _106013 _106031 s a k _50447) (@lem4407656 _106013 _106031 s a k _50447)). Qed.
Lemma lem4407658 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50447 : _106031) : True = ((term201 _106013 _106031 k s a _50447) = (term332 _106013 _106031 s a k _50447)).
Proof. exact (SYM (@lem4407657 _106013 _106031 s a k _50447)). Qed.
Lemma lem4407659 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50447 : _106031) : (term201 _106013 _106031 k s a _50447) = (term332 _106013 _106031 s a k _50447).
Proof. exact (EQ_MP (@lem4407658 _106013 _106031 s a k _50447) (@lem0)). Qed.
Lemma lem4407660 {_106013 _106031 : Type'} (_50447 : _106031) (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term332 _106013 _106031 s a k _50447.
Proof. exact (EQ_MP (@lem4407659 _106013 _106031 s a k _50447) (@lem4407610 _106013 _106031 _50447 i k s a h1)). Qed.
Lemma lem4407662 (b : Prop) (a : Prop) : (a \/ b) = (term336 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4407663 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (_50447 : _106031) : (term332 _106013 _106031 s a k _50447) = (term337 _106013 _106031 k s a _50447).
Proof. exact (@lem4407662 (term138 _106031 k _50447) (term333 _106013 _106031 s a _50447)). Qed.
Lemma lem4407665 (a : Prop) : (term69 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4407666 {_106031 : Type'} (k : _106031 -> Prop) (_50447 : _106031) : (term338 _106031 k _50447) = (k _50447).
Proof. exact (@lem4407665 (k _50447)). Qed.
Lemma lem4407667 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4407668 {_106031 : Type'} (k : _106031 -> Prop) (_50447 : _106031) : (term339 _106031 k _50447) = (term50 _106031 k _50447).
Proof. exact (MK_COMB (@lem4407667) (@lem4407666 _106031 k _50447)). Qed.
Lemma lem4407669 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (_50447 : _106031) : (term333 _106013 _106031 s a _50447) = (term333 _106013 _106031 s a _50447).
Proof. exact (eq_refl (term333 _106013 _106031 s a _50447)). Qed.
Lemma lem4407670 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (_50447 : _106031) : (term337 _106013 _106031 k s a _50447) = (term340 _106013 _106031 k s a _50447).
Proof. exact (MK_COMB (@lem4407668 _106031 k _50447) (@lem4407669 _106013 _106031 s a _50447)). Qed.
Lemma lem4407671 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (_50447 : _106031) : (term332 _106013 _106031 s a k _50447) = (term340 _106013 _106031 k s a _50447).
Proof. exact (TRANS (@lem4407663 _106013 _106031 k s a _50447) (@lem4407670 _106013 _106031 k s a _50447)). Qed.
Lemma lem4407674 {_106013 _106031 : Type'} (_50447 : _106031) (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term340 _106013 _106031 k s a _50447.
Proof. exact (EQ_MP (@lem4407671 _106013 _106031 k s a _50447) (@lem4407660 _106013 _106031 _50447 i k s a h1)). Qed.
Lemma lem4407675 {_106013 _106031 : Type'} (_50447 : _106031) (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term340 _106013 _106031 k s a _50447.
Proof. exact (@lem4407674 _106013 _106031 _50447 i k s a h1). Qed.
Lemma lem4407676 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term340 _106013 _106031 k s a i.
Proof. exact (@lem4407675 _106013 _106031 i i k s a h1). Qed.
Lemma lem4407679 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term333 _106013 _106031 s a i.
Proof. exact (@lem4407676 _106013 _106031 i k s a h1 (@lem4407631 _106013 _106031 i k s a h1)). Qed.
Lemma lem4407680 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term341 _106013 _106031 s a i.
Proof. exact (fun h0 : term342 _106013 _106031 s a i => @lem4407679 _106013 _106031 i k s a h1). Qed.
Lemma lem4407682 (p : Prop) : (term331 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4407683 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (i : _106031) : (term341 _106013 _106031 s a i) = (term333 _106013 _106031 s a i).
Proof. exact (@lem4407682 (term333 _106013 _106031 s a i)). Qed.
Lemma lem4407684 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term333 _106013 _106031 s a i.
Proof. exact (EQ_MP (@lem4407683 _106013 _106031 s a i) (@lem4407680 _106013 _106031 i k s a h1)). Qed.
Lemma lem4407687 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4407689 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i : _106031) (_50448 : _106013) : (term41 _106013 _106031 s i _50448) = (term343 _106013 _106031 s i _50448).
Proof. exact (@lem4407687 (s i _50448)). Qed.
Lemma lem4407692 {_106013 _106031 : Type'} (_50448 : _106013) (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term343 _106013 _106031 s i _50448.
Proof. exact (EQ_MP (@lem4407689 _106013 _106031 s i _50448) (@lem4407614 _106013 _106031 _50448 i k s a h1)). Qed.
Lemma lem4407693 {_106013 _106031 : Type'} (_50448 : _106013) (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term343 _106013 _106031 s i _50448.
Proof. exact (@lem4407692 _106013 _106031 _50448 i k s a h1). Qed.
Lemma lem4407694 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term344 _106013 _106031 s a i.
Proof. exact (@lem4407693 _106013 _106031 (a i) i k s a h1). Qed.
Lemma lem4407697 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : False.
Proof. exact (@lem4407694 _106013 _106031 i k s a h1 (@lem4407684 _106013 _106031 i k s a h1)). Qed.
Lemma lem4407698 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : term345.
Proof. exact (fun h0 : ~ False => @lem4407697 _106013 _106031 i k s a h1). Qed.
Lemma lem4407700 (p : Prop) : (term331 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4407701 : term345 = False.
Proof. exact (@lem4407700 False). Qed.
Lemma lem4407702 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (h1 : term238 _106013 _106031 i k s a) : False.
Proof. exact (EQ_MP (@lem4407701) (@lem4407698 _106013 _106031 i k s a h1)). Qed.
Lemma lem4407704 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : k i'.
Proof. exact (proj1 (@lem4407541 _106013 _106031 a k s i' h1)). Qed.
Lemma lem4407705 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term330 _106031 k i'.
Proof. exact (fun h0 : term138 _106031 k i' => @lem4407704 _106013 _106031 a k s i' h1). Qed.
Lemma lem4407707 (p : Prop) : (term331 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4407708 {_106031 : Type'} (k : _106031 -> Prop) (i' : _106031) : (term330 _106031 k i') = (k i').
Proof. exact (@lem4407707 (k i')). Qed.
Lemma lem4407709 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : k i'.
Proof. exact (EQ_MP (@lem4407708 _106031 k i') (@lem4407705 _106013 _106031 a k s i' h1)). Qed.
Lemma lem4407715 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4407716 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50449 : _106031) : (term201 _106013 _106031 k s a _50449) = (term332 _106013 _106031 s a k _50449).
Proof. exact (@lem4407715 (term333 _106013 _106031 s a _50449) (term138 _106031 k _50449)). Qed.
Lemma lem4407722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407723 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50449 : _106031) : (term334 _106013 _106031 k s a _50449) = (term335 _106013 _106031 s a k _50449).
Proof. exact (MK_COMB (@lem4407722) (@lem4407716 _106013 _106031 s a k _50449)). Qed.
Lemma lem4407729 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50449 : _106031) : (term332 _106013 _106031 s a k _50449) = (term332 _106013 _106031 s a k _50449).
Proof. exact (eq_refl (term332 _106013 _106031 s a k _50449)). Qed.
Lemma lem4407730 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50449 : _106031) : ((term201 _106013 _106031 k s a _50449) = (term332 _106013 _106031 s a k _50449)) = ((term332 _106013 _106031 s a k _50449) = (term332 _106013 _106031 s a k _50449)).
Proof. exact (MK_COMB (@lem4407723 _106013 _106031 s a k _50449) (@lem4407729 _106013 _106031 s a k _50449)). Qed.
Lemma lem4407732 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4407733 (x : Prop) : (x = x) = True.
Proof. exact (@lem4407732 Prop x). Qed.
Lemma lem4407734 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50449 : _106031) : ((term332 _106013 _106031 s a k _50449) = (term332 _106013 _106031 s a k _50449)) = True.
Proof. exact (@lem4407733 (term332 _106013 _106031 s a k _50449)). Qed.
Lemma lem4407735 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50449 : _106031) : ((term201 _106013 _106031 k s a _50449) = (term332 _106013 _106031 s a k _50449)) = True.
Proof. exact (TRANS (@lem4407730 _106013 _106031 s a k _50449) (@lem4407734 _106013 _106031 s a k _50449)). Qed.
Lemma lem4407736 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50449 : _106031) : True = ((term201 _106013 _106031 k s a _50449) = (term332 _106013 _106031 s a k _50449)).
Proof. exact (SYM (@lem4407735 _106013 _106031 s a k _50449)). Qed.
Lemma lem4407737 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (_50449 : _106031) : (term201 _106013 _106031 k s a _50449) = (term332 _106013 _106031 s a k _50449).
Proof. exact (EQ_MP (@lem4407736 _106013 _106031 s a k _50449) (@lem0)). Qed.
Lemma lem4407738 {_106013 _106031 : Type'} (_50449 : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term332 _106013 _106031 s a k _50449.
Proof. exact (EQ_MP (@lem4407737 _106013 _106031 s a k _50449) (@lem4407620 _106013 _106031 _50449 a k s i' h1)). Qed.
Lemma lem4407740 (b : Prop) (a : Prop) : (a \/ b) = (term336 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4407741 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (_50449 : _106031) : (term332 _106013 _106031 s a k _50449) = (term337 _106013 _106031 k s a _50449).
Proof. exact (@lem4407740 (term138 _106031 k _50449) (term333 _106013 _106031 s a _50449)). Qed.
Lemma lem4407743 (a : Prop) : (term69 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4407744 {_106031 : Type'} (k : _106031 -> Prop) (_50449 : _106031) : (term338 _106031 k _50449) = (k _50449).
Proof. exact (@lem4407743 (k _50449)). Qed.
Lemma lem4407745 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4407746 {_106031 : Type'} (k : _106031 -> Prop) (_50449 : _106031) : (term339 _106031 k _50449) = (term50 _106031 k _50449).
Proof. exact (MK_COMB (@lem4407745) (@lem4407744 _106031 k _50449)). Qed.
Lemma lem4407747 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (_50449 : _106031) : (term333 _106013 _106031 s a _50449) = (term333 _106013 _106031 s a _50449).
Proof. exact (eq_refl (term333 _106013 _106031 s a _50449)). Qed.
Lemma lem4407748 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (_50449 : _106031) : (term337 _106013 _106031 k s a _50449) = (term340 _106013 _106031 k s a _50449).
Proof. exact (MK_COMB (@lem4407746 _106031 k _50449) (@lem4407747 _106013 _106031 s a _50449)). Qed.
Lemma lem4407749 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (a : _106031 -> _106013) (_50449 : _106031) : (term332 _106013 _106031 s a k _50449) = (term340 _106013 _106031 k s a _50449).
Proof. exact (TRANS (@lem4407741 _106013 _106031 k s a _50449) (@lem4407748 _106013 _106031 k s a _50449)). Qed.
Lemma lem4407752 {_106013 _106031 : Type'} (_50449 : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term340 _106013 _106031 k s a _50449.
Proof. exact (EQ_MP (@lem4407749 _106013 _106031 k s a _50449) (@lem4407738 _106013 _106031 _50449 a k s i' h1)). Qed.
Lemma lem4407753 {_106013 _106031 : Type'} (_50449 : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term340 _106013 _106031 k s a _50449.
Proof. exact (@lem4407752 _106013 _106031 _50449 a k s i' h1). Qed.
Lemma lem4407754 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term340 _106013 _106031 k s a i'.
Proof. exact (@lem4407753 _106013 _106031 i' a k s i' h1). Qed.
Lemma lem4407757 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term333 _106013 _106031 s a i'.
Proof. exact (@lem4407754 _106013 _106031 a k s i' h1 (@lem4407709 _106013 _106031 a k s i' h1)). Qed.
Lemma lem4407758 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term341 _106013 _106031 s a i'.
Proof. exact (fun h0 : term342 _106013 _106031 s a i' => @lem4407757 _106013 _106031 a k s i' h1). Qed.
Lemma lem4407760 (p : Prop) : (term331 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4407761 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (a : _106031 -> _106013) (i' : _106031) : (term341 _106013 _106031 s a i') = (term333 _106013 _106031 s a i').
Proof. exact (@lem4407760 (term333 _106013 _106031 s a i')). Qed.
Lemma lem4407762 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term333 _106013 _106031 s a i'.
Proof. exact (EQ_MP (@lem4407761 _106013 _106031 s a i') (@lem4407758 _106013 _106031 a k s i' h1)). Qed.
Lemma lem4407765 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4407767 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (i' : _106031) (_50450 : _106013) : (term41 _106013 _106031 s i' _50450) = (term343 _106013 _106031 s i' _50450).
Proof. exact (@lem4407765 (s i' _50450)). Qed.
Lemma lem4407770 {_106013 _106031 : Type'} (_50450 : _106013) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term343 _106013 _106031 s i' _50450.
Proof. exact (EQ_MP (@lem4407767 _106013 _106031 s i' _50450) (@lem4407624 _106013 _106031 _50450 a k s i' h1)). Qed.
Lemma lem4407771 {_106013 _106031 : Type'} (_50450 : _106013) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term343 _106013 _106031 s i' _50450.
Proof. exact (@lem4407770 _106013 _106031 _50450 a k s i' h1). Qed.
Lemma lem4407772 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term344 _106013 _106031 s a i'.
Proof. exact (@lem4407771 _106013 _106031 (a i') a k s i' h1). Qed.
Lemma lem4407775 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : False.
Proof. exact (@lem4407772 _106013 _106031 a k s i' h1 (@lem4407762 _106013 _106031 a k s i' h1)). Qed.
Lemma lem4407776 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : term345.
Proof. exact (fun h0 : ~ False => @lem4407775 _106013 _106031 a k s i' h1). Qed.
Lemma lem4407778 (p : Prop) : (term331 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4407779 : term345 = False.
Proof. exact (@lem4407778 False). Qed.
Lemma lem4407780 {_106013 _106031 : Type'} (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term266 _106013 _106031 a k s i') : False.
Proof. exact (EQ_MP (@lem4407779) (@lem4407776 _106013 _106031 a k s i' h1)). Qed.
Lemma lem4407781 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term321 _106013 _106031 i a k s i') : False.
Proof. exact (or_elim (@lem4407534 _106013 _106031 i a k s i' h1) (fun h0 : term238 _106013 _106031 i k s a => @lem4407702 _106013 _106031 i k s a h0) (fun h0 : term266 _106013 _106031 a k s i' => @lem4407780 _106013 _106031 a k s i' h0)). Qed.
Lemma lem4407782 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term321 _106013 _106031 i a k s i') : (term321 _106013 _106031 i a k s i') = False.
Proof. exact (prop_ext (fun h2 : term321 _106013 _106031 i a k s i' => @lem4407781 _106013 _106031 i a k s i' h1) (fun h2 : False => @lem4407534 _106013 _106031 i a k s i' h1)). Qed.
Lemma lem4407783 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (i' : _106031) (h1 : term321 _106013 _106031 i a k s i') : False.
Proof. exact (EQ_MP (@lem4407782 _106013 _106031 i a k s i' h1) (@lem4407534 _106013 _106031 i a k s i' h1)). Qed.
Lemma lem4407784 {_106013 _106031 : Type'} (i : _106031) (a : _106031 -> _106013) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term324 _106013 _106031 i a k s) : False.
Proof. exact (ex_elim (@lem4407455 _106013 _106031 i a k s h1) (fun i' : _106031 => fun h0 : term323 _106013 _106031 i a k s i' => @lem4407783 _106013 _106031 i a k s i' h0)). Qed.
Lemma lem4407785 {_106013 _106031 : Type'} (i : _106031) (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term326 _106013 _106031 i k s) : False.
Proof. exact (ex_elim (@lem4407454 _106013 _106031 i k s h1) (fun a : _106031 -> _106013 => fun h0 : term325 _106013 _106031 i k s a => @lem4407784 _106013 _106031 i a k s h0)). Qed.
Lemma lem4407786 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term64 _106013 _106031 k s) : False.
Proof. exact (ex_elim (@lem4407453 _106013 _106031 k s h1) (fun i : _106031 => fun h0 : term327 _106013 _106031 k s i => @lem4407785 _106013 _106031 i k s h0)). Qed.
Lemma lem4407787 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term64 _106013 _106031 k s) : (term64 _106013 _106031 k s) = False.
Proof. exact (prop_ext (fun h2 : term64 _106013 _106031 k s => @lem4407786 _106013 _106031 k s h1) (fun h2 : False => @lem4406785 _106013 _106031 k s h1)). Qed.
Lemma lem4407788 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term64 _106013 _106031 k s) : False.
Proof. exact (EQ_MP (@lem4407787 _106013 _106031 k s h1) (@lem4406785 _106013 _106031 k s h1)). Qed.
Lemma lem4407789 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : term63 _106013 _106031 k s.
Proof. exact (fun h0 : term64 _106013 _106031 k s => @lem4407788 _106013 _106031 k s h0). Qed.
Lemma lem4407790 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term47 _106013 _106031 k s) = (term61 _106013 _106031 k s).
Proof. exact (EQ_MP (@lem4406784 _106013 _106031 k s) (@lem4407789 _106013 _106031 k s)). Qed.
Lemma lem4407795 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) : term73 _106013 _106031 s.
Proof. exact (fun k : _106031 -> Prop => @lem4407790 _106013 _106031 k s). Qed.
Lemma lem4407800 {_106013 _106031 : Type'} : term77 _106013 _106031.
Proof. exact (fun s : type1470 _106013 _106031 => @lem4407795 _106013 _106031 s). Qed.
Lemma lem4407801 {_106013 _106031 : Type'} : term76 _106013 _106031.
Proof. exact (EQ_MP (@lem4406780 _106013 _106031) (@lem4407800 _106013 _106031)). Qed.
Lemma lem4407802 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) : term346 _106013 _106031 s.
Proof. exact (@lem4407801 _106013 _106031 s). Qed.
Lemma lem4407803 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) : (term346 _106013 _106031 s) = (term72 _106013 _106031 s).
Proof. exact (eq_refl (term346 _106013 _106031 s)). Qed.
Lemma lem4407804 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) : term72 _106013 _106031 s.
Proof. exact (EQ_MP (@lem4407803 _106013 _106031 s) (@lem4407802 _106013 _106031 s)). Qed.
Lemma lem4407805 {_106013 _106031 : Type'} (s : type1470 _106013 _106031) (k : _106031 -> Prop) : term347 _106013 _106031 s k.
Proof. exact (@lem4407804 _106013 _106031 s k). Qed.
Lemma lem4407806 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term347 _106013 _106031 s k) = (term63 _106013 _106031 k s).
Proof. exact (eq_refl (term347 _106013 _106031 s k)). Qed.
Lemma lem4407807 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : term63 _106013 _106031 k s.
Proof. exact (EQ_MP (@lem4407806 _106013 _106031 k s) (@lem4407805 _106013 _106031 s k)). Qed.
Lemma lem4407809 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : term63 _106013 _106031 k s.
Proof. exact (@lem4406624 _106013 _106031 k s (@lem4407807 _106013 _106031 k s)). Qed.
Lemma lem4407810 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term64 _106013 _106031 k s) : False.
Proof. exact (@lem4407809 _106013 _106031 k s (@lem4406608 _106013 _106031 k s h1)). Qed.
Lemma lem4407811 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term64 _106013 _106031 k s) : (term64 _106013 _106031 k s) = False.
Proof. exact (prop_ext (fun h2 : term64 _106013 _106031 k s => @lem4407810 _106013 _106031 k s h1) (fun h2 : False => @lem4406608 _106013 _106031 k s h1)). Qed.
Lemma lem4407812 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) (h1 : term64 _106013 _106031 k s) : False.
Proof. exact (EQ_MP (@lem4407811 _106013 _106031 k s h1) (@lem4406608 _106013 _106031 k s h1)). Qed.
Lemma lem4407813 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : term63 _106013 _106031 k s.
Proof. exact (fun h0 : term64 _106013 _106031 k s => @lem4407812 _106013 _106031 k s h0). Qed.
Lemma lem4407814 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term47 _106013 _106031 k s) = (term61 _106013 _106031 k s).
Proof. exact (EQ_MP (@lem4406607 _106013 _106031 k s) (@lem4407813 _106013 _106031 k s)). Qed.
Lemma lem4407815 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term33 _106013 _106031 k s) = (term36 _106013 _106031 k s).
Proof. exact (EQ_MP (@lem4406603 _106013 _106031 k s) (@lem4407814 _106013 _106031 k s)). Qed.
Lemma lem4407817 {A : Type'} (s : A -> Prop) : term348 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4407818 {A : Type'} (s : A -> Prop) : (term348 A s) = (term349 A s).
Proof. exact (eq_refl (term348 A s)). Qed.
Lemma lem4407819 {A : Type'} (s : A -> Prop) : term349 A s.
Proof. exact (EQ_MP (@lem4407818 A s) (@lem4407817 A s)). Qed.
Lemma lem4407820 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term350 A s t.
Proof. exact (@lem4407819 A s t). Qed.
Lemma lem4407821 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term350 A s t) = ((s = t) = (term25 A s t)).
Proof. exact (eq_refl (term350 A s t)). Qed.
Lemma lem4407824 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term25 A s t).
Proof. exact (EQ_MP (@lem4407821 A s t) (@lem4407820 A s t)). Qed.
Lemma lem4407825 {A K : Type'} (s : type805 A K) (t : type805 A K) : (s = t) = (term351 A K s t).
Proof. exact (@lem4407824 (K -> A) s t). Qed.
Lemma lem4407826 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term352 A K k s).
Proof. exact (@lem4407825 A K (@cartesian_product A K k s) (@EMPTY (K -> A))). Qed.
Lemma lem4407827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407828 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term353 A K k s) = (term354 A K k s).
Proof. exact (MK_COMB (@lem4407827) (@lem4407826 A K k s)). Qed.
Lemma lem4407829 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term32 A K k s) = (term32 A K k s).
Proof. exact (eq_refl (term32 A K k s)). Qed.
Lemma lem4407830 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term32 A K k s)) = ((term352 A K k s) = (term32 A K k s)).
Proof. exact (MK_COMB (@lem4407828 A K k s) (@lem4407829 A K k s)). Qed.
Lemma lem4407831 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term352 A K k s) = (term32 A K k s)) = (((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term32 A K k s)).
Proof. exact (SYM (@lem4407830 A K k s)). Qed.
Lemma lem4407841 {_106013 _106031 : Type'} (k : _106031 -> Prop) (s : type1470 _106013 _106031) : (term32 _106013 _106031 k s) = (term36 _106013 _106031 k s).
Proof. exact (EQ_MP (@lem4406507 _106013 _106031 k s) (@lem4407815 _106013 _106031 k s)). Qed.
Lemma lem4407842 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term32 A K k s) = (term36 A K k s).
Proof. exact (@lem4407841 A K k s). Qed.
Lemma lem4407853 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term354 A K k s) = (term354 A K k s).
Proof. exact (eq_refl (term354 A K k s)). Qed.
Lemma lem4407854 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term352 A K k s) = (term32 A K k s)) = ((term352 A K k s) = (term36 A K k s)).
Proof. exact (MK_COMB (@lem4407853 A K k s) (@lem4407842 A K k s)). Qed.
Lemma lem4407857 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term352 A K k s) = (term36 A K k s)) = ((term352 A K k s) = (term32 A K k s)).
Proof. exact (SYM (@lem4407854 A K k s)). Qed.
Lemma lem4407867 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term18 A K k s).
Proof. exact (EQ_MP (@lem4406436 A K k s) (@lem4406435 A K k s)). Qed.
Lemma lem4407868 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term18 A K k s).
Proof. exact (@lem4407867 A K k s). Qed.
Lemma lem4407881 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4407882 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term355 A K x k s) = (term356 A K x k s).
Proof. exact (MK_COMB (@lem4407881 A K x) (@lem4407868 A K k s)). Qed.
Lemma lem4407883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407884 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term357 A K x k s) = (term358 A K x k s).
Proof. exact (MK_COMB (@lem4407883) (@lem4407882 A K x k s)). Qed.
Lemma lem4407885 {A K : Type'} (x : K -> A) : (@IN (K -> A) x (@EMPTY (K -> A))) = (@IN (K -> A) x (@EMPTY (K -> A))).
Proof. exact (eq_refl (@IN (K -> A) x (@EMPTY (K -> A)))). Qed.
Lemma lem4407886 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : ((term355 A K x k s) = (@IN (K -> A) x (@EMPTY (K -> A)))) = ((term356 A K x k s) = (@IN (K -> A) x (@EMPTY (K -> A)))).
Proof. exact (MK_COMB (@lem4407884 A K x k s) (@lem4407885 A K x)). Qed.
Lemma lem4407889 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term359 A K k s) = (term360 A K k s).
Proof. exact (fun_ext (fun x : K -> A => @lem4407886 A K k s x)). Qed.
Lemma lem4407890 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4407891 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term352 A K k s) = (term361 A K k s).
Proof. exact (MK_COMB (@lem4407890 A K) (@lem4407889 A K k s)). Qed.
Lemma lem4407896 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407897 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term354 A K k s) = (term362 A K k s).
Proof. exact (MK_COMB (@lem4407896) (@lem4407891 A K k s)). Qed.
Lemma lem4407899 {A B : Type'} (P : type1413 A B) : (term23 A B P) = (term24 A B P).
Proof. exact (EQ_MP (@lem4406442 A B P) (@lem4406441 A B P)). Qed.
Lemma lem4407900 {A K : Type'} (P : type1470 A K) : (term186 A K P) = (term187 A K P).
Proof. exact (@lem4407899 K A P). Qed.
Lemma lem4407901 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term363 A K k s) = (term364 A K k s).
Proof. exact (@lem4407900 A K (term365 A K k s)). Qed.
Lemma lem4407902 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term366 A K k s i) = (term53 A K k s i).
Proof. exact (eq_refl (term366 A K k s i)). Qed.
Lemma lem4407903 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4407904 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (a : A) : (term367 A K k s i a) = (term368 A K k s i a).
Proof. exact (MK_COMB (@lem4407902 A K k s i) (@lem4407903 A a)). Qed.
Lemma lem4407905 {A K : Type'} (k : K -> Prop) (a : A) (s : type1470 A K) (i : K) : (term368 A K k s i a) = (term51 A K k a s i).
Proof. exact (eq_refl (term368 A K k s i a)). Qed.
Lemma lem4407906 {A K : Type'} (k : K -> Prop) (a : A) (s : type1470 A K) (i : K) : (term367 A K k s i a) = (term51 A K k a s i).
Proof. exact (TRANS (@lem4407904 A K k s i a) (@lem4407905 A K k a s i)). Qed.
Lemma lem4407907 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term369 A K k s i) = (term53 A K k s i).
Proof. exact (fun_ext (fun a : A => @lem4407906 A K k a s i)). Qed.
Lemma lem4407908 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4407909 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term370 A K k s i) = (term55 A K k s i).
Proof. exact (MK_COMB (@lem4407908 A) (@lem4407907 A K k s i)). Qed.
Lemma lem4407910 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term371 A K k s) = (term57 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4407909 A K k s i)). Qed.
Lemma lem4407911 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4407912 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term363 A K k s) = (term59 A K k s).
Proof. exact (MK_COMB (@lem4407911 K) (@lem4407910 A K k s)). Qed.
Lemma lem4407913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407914 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term372 A K k s) = (term373 A K k s).
Proof. exact (MK_COMB (@lem4407913) (@lem4407912 A K k s)). Qed.
Lemma lem4407915 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term366 A K k s i) = (term53 A K k s i).
Proof. exact (eq_refl (term366 A K k s i)). Qed.
Lemma lem4407916 {A K : Type'} (a : K -> A) (i : K) : (a i) = (a i).
Proof. exact (eq_refl (a i)). Qed.
Lemma lem4407917 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (a : K -> A) (i : K) : (term374 A K k s a i) = (term375 A K k s a i).
Proof. exact (MK_COMB (@lem4407915 A K k s i) (@lem4407916 A K a i)). Qed.
Lemma lem4407918 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) (i : K) : (term375 A K k s a i) = (term376 A K k a s i).
Proof. exact (eq_refl (term375 A K k s a i)). Qed.
Lemma lem4407919 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) (i : K) : (term374 A K k s a i) = (term376 A K k a s i).
Proof. exact (TRANS (@lem4407917 A K k s a i) (@lem4407918 A K k a s i)). Qed.
Lemma lem4407920 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term377 A K k s a) = (term378 A K k a s).
Proof. exact (fun_ext (fun i : K => @lem4407919 A K k a s i)). Qed.
Lemma lem4407921 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4407922 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term379 A K k s a) = (term380 A K k a s).
Proof. exact (MK_COMB (@lem4407921 K) (@lem4407920 A K k a s)). Qed.
Lemma lem4407923 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term381 A K k s) = (term382 A K k s).
Proof. exact (fun_ext (fun a : K -> A => @lem4407922 A K k a s)). Qed.
Lemma lem4407924 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4407925 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term364 A K k s) = (term383 A K k s).
Proof. exact (MK_COMB (@lem4407924 A K) (@lem4407923 A K k s)). Qed.
Lemma lem4407926 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term363 A K k s) = (term364 A K k s)) = ((term59 A K k s) = (term383 A K k s)).
Proof. exact (MK_COMB (@lem4407914 A K k s) (@lem4407925 A K k s)). Qed.
Lemma lem4407927 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term59 A K k s) = (term383 A K k s).
Proof. exact (EQ_MP (@lem4407926 A K k s) (@lem4407901 A K k s)). Qed.
Lemma lem4407938 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4407939 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term36 A K k s) = (term384 A K k s).
Proof. exact (MK_COMB (@lem4407938) (@lem4407927 A K k s)). Qed.
Lemma lem4407941 {A : Type'} (P : A -> Prop) : (term20 A P) = (term21 A P).
Proof. exact (EQ_MP (@lem4406439 A P) (@lem4406438 A P)). Qed.
Lemma lem4407942 {A K : Type'} (P : type805 A K) : (term385 A K P) = (term386 A K P).
Proof. exact (@lem4407941 (K -> A) P). Qed.
Lemma lem4407943 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term387 A K k s) = (term388 A K k s).
Proof. exact (@lem4407942 A K (term382 A K k s)). Qed.
Lemma lem4407944 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term389 A K k s a) = (term380 A K k a s).
Proof. exact (eq_refl (term389 A K k s a)). Qed.
Lemma lem4407945 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term390 A K k s) = (term382 A K k s).
Proof. exact (fun_ext (fun a : K -> A => @lem4407944 A K k a s)). Qed.
Lemma lem4407946 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4407947 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term391 A K k s) = (term383 A K k s).
Proof. exact (MK_COMB (@lem4407946 A K) (@lem4407945 A K k s)). Qed.
Lemma lem4407948 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4407949 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term387 A K k s) = (term384 A K k s).
Proof. exact (MK_COMB (@lem4407948) (@lem4407947 A K k s)). Qed.
Lemma lem4407950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4407951 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term392 A K k s) = (term393 A K k s).
Proof. exact (MK_COMB (@lem4407950) (@lem4407949 A K k s)). Qed.
Lemma lem4407952 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term389 A K k s a) = (term380 A K k a s).
Proof. exact (eq_refl (term389 A K k s a)). Qed.
Lemma lem4407953 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4407954 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term394 A K k s a) = (term395 A K k a s).
Proof. exact (MK_COMB (@lem4407953) (@lem4407952 A K k a s)). Qed.
Lemma lem4407955 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term396 A K k s) = (term397 A K k s).
Proof. exact (fun_ext (fun a : K -> A => @lem4407954 A K k a s)). Qed.
Lemma lem4407956 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4407957 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term388 A K k s) = (term398 A K k s).
Proof. exact (MK_COMB (@lem4407956 A K) (@lem4407955 A K k s)). Qed.
Lemma lem4407958 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term387 A K k s) = (term388 A K k s)) = ((term384 A K k s) = (term398 A K k s)).
Proof. exact (MK_COMB (@lem4407951 A K k s) (@lem4407957 A K k s)). Qed.
Lemma lem4407959 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term384 A K k s) = (term398 A K k s).
Proof. exact (EQ_MP (@lem4407958 A K k s) (@lem4407943 A K k s)). Qed.
Lemma lem4407970 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term36 A K k s) = (term398 A K k s).
Proof. exact (TRANS (@lem4407939 A K k s) (@lem4407959 A K k s)). Qed.
Lemma lem4407971 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term352 A K k s) = (term36 A K k s)) = ((term361 A K k s) = (term398 A K k s)).
Proof. exact (MK_COMB (@lem4407897 A K k s) (@lem4407970 A K k s)). Qed.
Lemma lem4407974 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term361 A K k s) = (term398 A K k s)) = ((term352 A K k s) = (term36 A K k s)).
Proof. exact (SYM (@lem4407971 A K k s)). Qed.
Lemma lem4407984 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term14 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4406423 _83095 p x) (@lem4406422 _83095 p x)). Qed.
Lemma lem4407985 {A K : Type'} (p : type805 A K) (x : K -> A) : (term399 A K x p) = (p x).
Proof. exact (@lem4407984 (K -> A) p x). Qed.
Lemma lem4407986 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term400 A K x k s) = (term401 A K k s x).
Proof. exact (@lem4407985 A K (term402 A K k s) x). Qed.
Lemma lem4407987 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term401 A K k s f) = (term403 A K k f s).
Proof. exact (eq_refl (term401 A K k s f)). Qed.
Lemma lem4407988 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4407989 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term404 A K GEN_PVAR_140 k s f) = (term405 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4407988 A K GEN_PVAR_140) (@lem4407987 A K k f s)). Qed.
Lemma lem4407990 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4407991 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term406 A K GEN_PVAR_140 k s f) = (term407 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4407989 A K GEN_PVAR_140 k f s) (@lem4407990 A K f)). Qed.
Lemma lem4407992 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term408 A K GEN_PVAR_140 k s) = (term409 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4407991 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4407993 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4407994 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term410 A K GEN_PVAR_140 k s) = (term411 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4407993 A K) (@lem4407992 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4407995 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term412 A K k s) = (term413 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4407994 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4407996 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4407997 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term414 A K k s) = (term18 A K k s).
Proof. exact (MK_COMB (@lem4407996 A K) (@lem4407995 A K k s)). Qed.
Lemma lem4407998 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4407999 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term400 A K x k s) = (term356 A K x k s).
Proof. exact (MK_COMB (@lem4407998 A K x) (@lem4407997 A K k s)). Qed.
Lemma lem4408000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4408001 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term415 A K x k s) = (term358 A K x k s).
Proof. exact (MK_COMB (@lem4408000) (@lem4407999 A K x k s)). Qed.
Lemma lem4408002 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term401 A K k s x) = (term403 A K k x s).
Proof. exact (eq_refl (term401 A K k s x)). Qed.
Lemma lem4408003 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term400 A K x k s) = (term401 A K k s x)) = ((term356 A K x k s) = (term403 A K k x s)).
Proof. exact (MK_COMB (@lem4408001 A K x k s) (@lem4408002 A K k x s)). Qed.
Lemma lem4408004 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term356 A K x k s) = (term403 A K k x s).
Proof. exact (EQ_MP (@lem4408003 A K k x s) (@lem4407986 A K k s x)). Qed.
Lemma lem4408013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4408014 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term358 A K x k s) = (term416 A K k x s).
Proof. exact (MK_COMB (@lem4408013) (@lem4408004 A K k x s)). Qed.
Lemma lem4408016 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4406392 A x (@lem4406391 A x)). Qed.
Lemma lem4408017 {A K : Type'} (x : K -> A) : (@IN (K -> A) x (@EMPTY (K -> A))) = False.
Proof. exact (@lem4408016 (K -> A) x). Qed.
Lemma lem4408018 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term356 A K x k s) = (@IN (K -> A) x (@EMPTY (K -> A)))) = ((term403 A K k x s) = False).
Proof. exact (MK_COMB (@lem4408014 A K k x s) (@lem4408017 A K x)). Qed.
Lemma lem4408020 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4408021 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term403 A K k x s) = False) = (term417 A K k x s).
Proof. exact (@lem4408020 (term403 A K k x s)). Qed.
Lemma lem4408030 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term356 A K x k s) = (@IN (K -> A) x (@EMPTY (K -> A)))) = (term417 A K k x s).
Proof. exact (TRANS (@lem4408018 A K k x s) (@lem4408021 A K k x s)). Qed.
Lemma lem4408031 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term360 A K k s) = (term418 A K k s).
Proof. exact (fun_ext (fun x : K -> A => @lem4408030 A K k x s)). Qed.
Lemma lem4408032 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4408033 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term361 A K k s) = (term419 A K k s).
Proof. exact (MK_COMB (@lem4408032 A K) (@lem4408031 A K k s)). Qed.
Lemma lem4408038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4408039 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term362 A K k s) = (term420 A K k s).
Proof. exact (MK_COMB (@lem4408038) (@lem4408033 A K k s)). Qed.
Lemma lem4408050 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term398 A K k s) = (term398 A K k s).
Proof. exact (eq_refl (term398 A K k s)). Qed.
Lemma lem4408051 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term361 A K k s) = (term398 A K k s)) = ((term419 A K k s) = (term398 A K k s)).
Proof. exact (MK_COMB (@lem4408039 A K k s) (@lem4408050 A K k s)). Qed.
Lemma lem4408054 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term419 A K k s) = (term398 A K k s)) = ((term361 A K k s) = (term398 A K k s)).
Proof. exact (SYM (@lem4408051 A K k s)). Qed.
Lemma lem4408055 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term419 A K k s) : term419 A K k s.
Proof. exact (h1). Qed.
Lemma lem4408056 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term398 A K k s) : term398 A K k s.
Proof. exact (h1). Qed.
Lemma lem4408057 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term419 A K k s) : term421 A K s k f.
Proof. exact (@lem4408055 A K k s h1 (term422 A K k f)). Qed.
Lemma lem4408058 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term421 A K s k f) = (term423 A K k f s).
Proof. exact (eq_refl (term421 A K s k f)). Qed.
Lemma lem4408059 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term419 A K k s) : term423 A K k f s.
Proof. exact (EQ_MP (@lem4408058 A K k f s) (@lem4408057 A K f k s h1)). Qed.
Lemma lem4408060 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term398 A K k s) : term424 A K s k f.
Proof. exact (@lem4408056 A K k s h1 (term422 A K k f)). Qed.
Lemma lem4408061 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term424 A K s k f) = (term425 A K k f s).
Proof. exact (eq_refl (term424 A K s k f)). Qed.
Lemma lem4408062 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term398 A K k s) : term425 A K k f s.
Proof. exact (EQ_MP (@lem4408061 A K k f s) (@lem4408060 A K f k s h1)). Qed.
Lemma lem4408068 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term6 A B s).
Proof. exact (EQ_MP (@lem4406387 A B s) (@lem4406386 A B s)). Qed.
Lemma lem4408069 {A K : Type'} (s : K -> Prop) : (@EXTENSIONAL K A s) = (term426 A K s).
Proof. exact (@lem4408068 K A s). Qed.
Lemma lem4408070 {A K : Type'} (k : K -> Prop) : (@EXTENSIONAL K A k) = (term426 A K k).
Proof. exact (@lem4408069 A K k). Qed.
Lemma lem4408083 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term422 A K k f) = (term422 A K k f).
Proof. exact (eq_refl (term422 A K k f)). Qed.
Lemma lem4408084 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term427 A K k f) = (term428 A K k f).
Proof. exact (MK_COMB (@lem4408070 A K k) (@lem4408083 A K k f)). Qed.
Lemma lem4408086 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term4 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4406363 _83152 p x) (@lem4406362 _83152 p x)). Qed.
Lemma lem4408087 {A K : Type'} (p : type805 A K) (x : K -> A) : (term429 A K p x) = (p x).
Proof. exact (@lem4408086 (K -> A) p x). Qed.
Lemma lem4408088 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term430 A K k f) = (term431 A K k f).
Proof. exact (@lem4408087 A K (term432 A K k) (term422 A K k f)). Qed.
Lemma lem4408089 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term433 A K k f) = (term434 A K k f).
Proof. exact (eq_refl (term433 A K k f)). Qed.
Lemma lem4408090 {A K : Type'} (GEN_PVAR_139 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_139) = (@SETSPEC (K -> A) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_139)). Qed.
Lemma lem4408091 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term435 A K GEN_PVAR_139 k f) = (term436 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4408090 A K GEN_PVAR_139) (@lem4408089 A K k f)). Qed.
Lemma lem4408092 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4408093 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term437 A K GEN_PVAR_139 k f) = (term438 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4408091 A K GEN_PVAR_139 k f) (@lem4408092 A K f)). Qed.
Lemma lem4408094 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term439 A K GEN_PVAR_139 k) = (term440 A K GEN_PVAR_139 k).
Proof. exact (fun_ext (fun f : K -> A => @lem4408093 A K GEN_PVAR_139 k f)). Qed.
Lemma lem4408095 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4408096 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term441 A K GEN_PVAR_139 k) = (term442 A K GEN_PVAR_139 k).
Proof. exact (MK_COMB (@lem4408095 A K) (@lem4408094 A K GEN_PVAR_139 k)). Qed.
Lemma lem4408097 {A K : Type'} (k : K -> Prop) : (term443 A K k) = (term444 A K k).
Proof. exact (fun_ext (fun GEN_PVAR_139 : K -> A => @lem4408096 A K GEN_PVAR_139 k)). Qed.
Lemma lem4408098 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4408099 {A K : Type'} (k : K -> Prop) : (term445 A K k) = (term426 A K k).
Proof. exact (MK_COMB (@lem4408098 A K) (@lem4408097 A K k)). Qed.
Lemma lem4408100 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term422 A K k f) = (term422 A K k f).
Proof. exact (eq_refl (term422 A K k f)). Qed.
Lemma lem4408101 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term430 A K k f) = (term428 A K k f).
Proof. exact (MK_COMB (@lem4408099 A K k) (@lem4408100 A K k f)). Qed.
Lemma lem4408102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4408103 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term446 A K k f) = (term447 A K k f).
Proof. exact (MK_COMB (@lem4408102) (@lem4408101 A K k f)). Qed.
Lemma lem4408104 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term431 A K k f) = (term448 A K k f).
Proof. exact (eq_refl (term431 A K k f)). Qed.
Lemma lem4408105 {A K : Type'} (k : K -> Prop) (f : K -> A) : ((term430 A K k f) = (term431 A K k f)) = ((term428 A K k f) = (term448 A K k f)).
Proof. exact (MK_COMB (@lem4408103 A K k f) (@lem4408104 A K k f)). Qed.
Lemma lem4408106 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term428 A K k f) = (term448 A K k f).
Proof. exact (EQ_MP (@lem4408105 A K k f) (@lem4408088 A K k f)). Qed.
Lemma lem4408116 {A B : Type'} (f : A -> B) (y : A) : (term449 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4408117 {A K : Type'} (f : K -> A) (y : K) : (term450 A K f y) = (f y).
Proof. exact (@lem4408116 K A f y). Qed.
Lemma lem4408118 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term451 A K k f x) = (term452 A K k f x).
Proof. exact (@lem4408117 A K (term422 A K k f) x). Qed.
Lemma lem4408119 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term452 A K k f i) = (term453 A K k f i).
Proof. exact (eq_refl (term452 A K k f i)). Qed.
Lemma lem4408120 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term454 A K k f) = (term422 A K k f).
Proof. exact (fun_ext (fun i : K => @lem4408119 A K k f i)). Qed.
Lemma lem4408121 {K : Type'} (x : K) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4408122 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term451 A K k f x) = (term452 A K k f x).
Proof. exact (MK_COMB (@lem4408120 A K k f) (@lem4408121 K x)). Qed.
Lemma lem4408123 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4408124 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term455 A K k f x) = (term456 A K k f x).
Proof. exact (MK_COMB (@lem4408123 A) (@lem4408122 A K k f x)). Qed.
Lemma lem4408125 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term452 A K k f x) = (term453 A K k f x).
Proof. exact (eq_refl (term452 A K k f x)). Qed.
Lemma lem4408126 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : ((term451 A K k f x) = (term452 A K k f x)) = ((term452 A K k f x) = (term453 A K k f x)).
Proof. exact (MK_COMB (@lem4408124 A K k f x) (@lem4408125 A K k f x)). Qed.
Lemma lem4408127 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term452 A K k f x) = (term453 A K k f x).
Proof. exact (EQ_MP (@lem4408126 A K k f x) (@lem4408118 A K k f x)). Qed.
Lemma lem4408128 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4408129 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term456 A K k f x) = (term457 A K k f x).
Proof. exact (MK_COMB (@lem4408128 A) (@lem4408127 A K k f x)). Qed.
Lemma lem4408130 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4408131 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : ((term452 A K k f x) = (@ARB A)) = ((term453 A K k f x) = (@ARB A)).
Proof. exact (MK_COMB (@lem4408129 A K k f x) (@lem4408130 A)). Qed.
Lemma lem4408134 {K : Type'} (x : K) (k : K -> Prop) : (term458 K x k) = (term458 K x k).
Proof. exact (eq_refl (term458 K x k)). Qed.
Lemma lem4408135 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term459 A K k f x) = (term460 A K k f x).
Proof. exact (MK_COMB (@lem4408134 K x k) (@lem4408131 A K k f x)). Qed.
Lemma lem4408138 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term461 A K k f) = (term462 A K k f).
Proof. exact (fun_ext (fun x : K => @lem4408135 A K k f x)). Qed.
Lemma lem4408139 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4408140 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term448 A K k f) = (term463 A K k f).
Proof. exact (MK_COMB (@lem4408139 K) (@lem4408138 A K k f)). Qed.
Lemma lem4408145 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term428 A K k f) = (term463 A K k f).
Proof. exact (TRANS (@lem4408106 A K k f) (@lem4408140 A K k f)). Qed.
Lemma lem4408146 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term427 A K k f) = (term463 A K k f).
Proof. exact (TRANS (@lem4408084 A K k f) (@lem4408145 A K k f)). Qed.
Lemma lem4408147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4408148 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term464 A K k f) = (term465 A K k f).
Proof. exact (MK_COMB (@lem4408147) (@lem4408146 A K k f)). Qed.
Lemma lem4408156 {A B : Type'} (f : A -> B) (y : A) : (term449 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4408157 {A K : Type'} (f : K -> A) (y : K) : (term450 A K f y) = (f y).
Proof. exact (@lem4408156 K A f y). Qed.
Lemma lem4408158 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term451 A K k f i) = (term452 A K k f i).
Proof. exact (@lem4408157 A K (term422 A K k f) i). Qed.
Lemma lem4408159 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term452 A K k f i) = (term453 A K k f i).
Proof. exact (eq_refl (term452 A K k f i)). Qed.
Lemma lem4408160 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term454 A K k f) = (term422 A K k f).
Proof. exact (fun_ext (fun i : K => @lem4408159 A K k f i)). Qed.
Lemma lem4408161 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4408162 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term451 A K k f i) = (term452 A K k f i).
Proof. exact (MK_COMB (@lem4408160 A K k f) (@lem4408161 K i)). Qed.
Lemma lem4408163 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4408164 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term455 A K k f i) = (term456 A K k f i).
Proof. exact (MK_COMB (@lem4408163 A) (@lem4408162 A K k f i)). Qed.
Lemma lem4408165 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term452 A K k f i) = (term453 A K k f i).
Proof. exact (eq_refl (term452 A K k f i)). Qed.
Lemma lem4408166 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : ((term451 A K k f i) = (term452 A K k f i)) = ((term452 A K k f i) = (term453 A K k f i)).
Proof. exact (MK_COMB (@lem4408164 A K k f i) (@lem4408165 A K k f i)). Qed.
Lemma lem4408167 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term452 A K k f i) = (term453 A K k f i).
Proof. exact (EQ_MP (@lem4408166 A K k f i) (@lem4408158 A K k f i)). Qed.
Lemma lem4408168 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4408169 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term466 A K k f i) = (term467 A K k f i).
Proof. exact (MK_COMB (@lem4408168 A) (@lem4408167 A K k f i)). Qed.
Lemma lem4408170 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4408171 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term468 A K k f s i) = (term469 A K k f s i).
Proof. exact (MK_COMB (@lem4408169 A K k f i) (@lem4408170 A K s i)). Qed.
Lemma lem4408172 {K : Type'} (i : K) (k : K -> Prop) : (term49 K i k) = (term49 K i k).
Proof. exact (eq_refl (term49 K i k)). Qed.
Lemma lem4408173 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term470 A K k f s i) = (term471 A K k f s i).
Proof. exact (MK_COMB (@lem4408172 K i k) (@lem4408171 A K k f s i)). Qed.
Lemma lem4408176 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term472 A K k f s) = (term473 A K k f s).
Proof. exact (fun_ext (fun i : K => @lem4408173 A K k f s i)). Qed.
Lemma lem4408177 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4408178 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term474 A K k f s) = (term475 A K k f s).
Proof. exact (MK_COMB (@lem4408177 K) (@lem4408176 A K k f s)). Qed.
Lemma lem4408183 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term476 A K k f s) = (term477 A K k f s).
Proof. exact (MK_COMB (@lem4408148 A K k f) (@lem4408178 A K k f s)). Qed.
Lemma lem4408186 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4408187 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term423 A K k f s) = (term478 A K k f s).
Proof. exact (MK_COMB (@lem4408186) (@lem4408183 A K k f s)). Qed.
Lemma lem4408188 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4408189 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term479 A K k f s) = (term480 A K k f s).
Proof. exact (MK_COMB (@lem4408188) (@lem4408187 A K k f s)). Qed.
Lemma lem4408196 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term395 A K k f s) = (term395 A K k f s).
Proof. exact (eq_refl (term395 A K k f s)). Qed.
Lemma lem4408197 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term481 A K k f s) = (term482 A K k f s).
Proof. exact (MK_COMB (@lem4408189 A K k f s) (@lem4408196 A K k f s)). Qed.
Lemma lem4408200 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term482 A K k f s) = (term481 A K k f s).
Proof. exact (SYM (@lem4408197 A K k f s)). Qed.
Lemma lem4408210 {A B : Type'} (f : A -> B) (y : A) : (term449 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4408211 {A K : Type'} (f : K -> A) (y : K) : (term450 A K f y) = (f y).
Proof. exact (@lem4408210 K A f y). Qed.
Lemma lem4408212 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term451 A K k f i) = (term452 A K k f i).
Proof. exact (@lem4408211 A K (term422 A K k f) i). Qed.
Lemma lem4408213 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term452 A K k f i) = (term453 A K k f i).
Proof. exact (eq_refl (term452 A K k f i)). Qed.
Lemma lem4408214 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term454 A K k f) = (term422 A K k f).
Proof. exact (fun_ext (fun i : K => @lem4408213 A K k f i)). Qed.
Lemma lem4408215 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4408216 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term451 A K k f i) = (term452 A K k f i).
Proof. exact (MK_COMB (@lem4408214 A K k f) (@lem4408215 K i)). Qed.
Lemma lem4408217 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4408218 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term455 A K k f i) = (term456 A K k f i).
Proof. exact (MK_COMB (@lem4408217 A) (@lem4408216 A K k f i)). Qed.
Lemma lem4408219 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term452 A K k f i) = (term453 A K k f i).
Proof. exact (eq_refl (term452 A K k f i)). Qed.
Lemma lem4408220 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : ((term451 A K k f i) = (term452 A K k f i)) = ((term452 A K k f i) = (term453 A K k f i)).
Proof. exact (MK_COMB (@lem4408218 A K k f i) (@lem4408219 A K k f i)). Qed.
Lemma lem4408221 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term452 A K k f i) = (term453 A K k f i).
Proof. exact (EQ_MP (@lem4408220 A K k f i) (@lem4408212 A K k f i)). Qed.
Lemma lem4408222 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4408223 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term466 A K k f i) = (term467 A K k f i).
Proof. exact (MK_COMB (@lem4408222 A) (@lem4408221 A K k f i)). Qed.
Lemma lem4408224 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4408225 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term468 A K k f s i) = (term469 A K k f s i).
Proof. exact (MK_COMB (@lem4408223 A K k f i) (@lem4408224 A K s i)). Qed.
Lemma lem4408226 {K : Type'} (i : K) (k : K -> Prop) : (term49 K i k) = (term49 K i k).
Proof. exact (eq_refl (term49 K i k)). Qed.
Lemma lem4408227 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term470 A K k f s i) = (term471 A K k f s i).
Proof. exact (MK_COMB (@lem4408226 K i k) (@lem4408225 A K k f s i)). Qed.
Lemma lem4408230 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term472 A K k f s) = (term473 A K k f s).
Proof. exact (fun_ext (fun i : K => @lem4408227 A K k f s i)). Qed.
Lemma lem4408231 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4408232 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term474 A K k f s) = (term475 A K k f s).
Proof. exact (MK_COMB (@lem4408231 K) (@lem4408230 A K k f s)). Qed.
Lemma lem4408237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4408238 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term425 A K k f s) = (term483 A K k f s).
Proof. exact (MK_COMB (@lem4408237) (@lem4408232 A K k f s)). Qed.
Lemma lem4408239 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4408240 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term484 A K k f s) = (term485 A K k f s).
Proof. exact (MK_COMB (@lem4408239) (@lem4408238 A K k f s)). Qed.
Lemma lem4408244 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term6 A B s).
Proof. exact (EQ_MP (@lem4406387 A B s) (@lem4406386 A B s)). Qed.
Lemma lem4408245 {A K : Type'} (s : K -> Prop) : (@EXTENSIONAL K A s) = (term426 A K s).
Proof. exact (@lem4408244 K A s). Qed.
Lemma lem4408246 {A K : Type'} (k : K -> Prop) : (@EXTENSIONAL K A k) = (term426 A K k).
Proof. exact (@lem4408245 A K k). Qed.
Lemma lem4408259 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4408260 {A K : Type'} (k : K -> Prop) (f : K -> A) : (@EXTENSIONAL K A k f) = (term486 A K k f).
Proof. exact (MK_COMB (@lem4408246 A K k) (@lem4408259 A K f)). Qed.
Lemma lem4408262 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term4 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4406363 _83152 p x) (@lem4406362 _83152 p x)). Qed.
Lemma lem4408263 {A K : Type'} (p : type805 A K) (x : K -> A) : (term429 A K p x) = (p x).
Proof. exact (@lem4408262 (K -> A) p x). Qed.
Lemma lem4408264 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term487 A K k f) = (term433 A K k f).
Proof. exact (@lem4408263 A K (term432 A K k) f). Qed.
Lemma lem4408265 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term433 A K k f) = (term434 A K k f).
Proof. exact (eq_refl (term433 A K k f)). Qed.
Lemma lem4408266 {A K : Type'} (GEN_PVAR_139 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_139) = (@SETSPEC (K -> A) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_139)). Qed.
Lemma lem4408267 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term435 A K GEN_PVAR_139 k f) = (term436 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4408266 A K GEN_PVAR_139) (@lem4408265 A K k f)). Qed.
Lemma lem4408268 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4408269 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term437 A K GEN_PVAR_139 k f) = (term438 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4408267 A K GEN_PVAR_139 k f) (@lem4408268 A K f)). Qed.
Lemma lem4408270 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term439 A K GEN_PVAR_139 k) = (term440 A K GEN_PVAR_139 k).
Proof. exact (fun_ext (fun f : K -> A => @lem4408269 A K GEN_PVAR_139 k f)). Qed.
Lemma lem4408271 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4408272 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term441 A K GEN_PVAR_139 k) = (term442 A K GEN_PVAR_139 k).
Proof. exact (MK_COMB (@lem4408271 A K) (@lem4408270 A K GEN_PVAR_139 k)). Qed.
Lemma lem4408273 {A K : Type'} (k : K -> Prop) : (term443 A K k) = (term444 A K k).
Proof. exact (fun_ext (fun GEN_PVAR_139 : K -> A => @lem4408272 A K GEN_PVAR_139 k)). Qed.
Lemma lem4408274 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4408275 {A K : Type'} (k : K -> Prop) : (term445 A K k) = (term426 A K k).
Proof. exact (MK_COMB (@lem4408274 A K) (@lem4408273 A K k)). Qed.
Lemma lem4408276 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4408277 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term487 A K k f) = (term486 A K k f).
Proof. exact (MK_COMB (@lem4408275 A K k) (@lem4408276 A K f)). Qed.
Lemma lem4408278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4408279 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term488 A K k f) = (term489 A K k f).
Proof. exact (MK_COMB (@lem4408278) (@lem4408277 A K k f)). Qed.
Lemma lem4408280 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term433 A K k f) = (term434 A K k f).
Proof. exact (eq_refl (term433 A K k f)). Qed.
Lemma lem4408281 {A K : Type'} (k : K -> Prop) (f : K -> A) : ((term487 A K k f) = (term433 A K k f)) = ((term486 A K k f) = (term434 A K k f)).
Proof. exact (MK_COMB (@lem4408279 A K k f) (@lem4408280 A K k f)). Qed.
Lemma lem4408282 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term486 A K k f) = (term434 A K k f).
Proof. exact (EQ_MP (@lem4408281 A K k f) (@lem4408264 A K k f)). Qed.
Lemma lem4408291 {A K : Type'} (k : K -> Prop) (f : K -> A) : (@EXTENSIONAL K A k f) = (term434 A K k f).
Proof. exact (TRANS (@lem4408260 A K k f) (@lem4408282 A K k f)). Qed.
Lemma lem4408292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4408293 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term490 A K k f) = (term491 A K k f).
Proof. exact (MK_COMB (@lem4408292) (@lem4408291 A K k f)). Qed.
Lemma lem4408300 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term380 A K k f s) = (term380 A K k f s).
Proof. exact (eq_refl (term380 A K k f s)). Qed.
Lemma lem4408301 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term403 A K k f s) = (term492 A K k f s).
Proof. exact (MK_COMB (@lem4408293 A K k f) (@lem4408300 A K k f s)). Qed.
Lemma lem4408304 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4408305 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term417 A K k f s) = (term493 A K k f s).
Proof. exact (MK_COMB (@lem4408304) (@lem4408301 A K k f s)). Qed.
Lemma lem4408306 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term494 A K k f s) = (term495 A K k f s).
Proof. exact (MK_COMB (@lem4408240 A K k f s) (@lem4408305 A K k f s)). Qed.
Lemma lem4408309 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term495 A K k f s) = (term494 A K k f s).
Proof. exact (SYM (@lem4408306 A K k f s)). Qed.
Lemma lem4408313 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term496 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4408314 (p : Prop) (q : Prop) (p' : Prop) : term497 p q p'.
Proof. exact (fun q' : Prop => @lem4408313 p q p' q'). Qed.
Lemma lem4408315 (p : Prop) (q : Prop) : term498 p q.
Proof. exact (fun p' : Prop => @lem4408314 p q p'). Qed.
Lemma lem4408316 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : term499 A K k f s.
Proof. exact (@lem4408315 (term478 A K k f s) (term395 A K k f s)). Qed.
Lemma lem4408317 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (p' : Prop) : term500 A K k f s p'.
Proof. exact (@lem4408316 A K k f s p'). Qed.
Lemma lem4408318 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (p' : Prop) : (term500 A K k f s p') = (term501 A K k f s p').
Proof. exact (eq_refl (term500 A K k f s p')). Qed.
Lemma lem4408319 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (p' : Prop) : term501 A K k f s p'.
Proof. exact (EQ_MP (@lem4408318 A K k f s p') (@lem4408317 A K k f s p')). Qed.
Lemma lem4408320 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (p' : Prop) (q' : Prop) : term502 A K k f s p' q'.
Proof. exact (@lem4408319 A K k f s p' q'). Qed.
Lemma lem4408321 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (p' : Prop) (q' : Prop) : (term502 A K k f s p' q') = (term503 A K k f s p' q').
Proof. exact (eq_refl (term502 A K k f s p' q')). Qed.
Lemma lem4408322 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (p' : Prop) (q' : Prop) : term503 A K k f s p' q'.
Proof. exact (EQ_MP (@lem4408321 A K k f s p' q') (@lem4408320 A K k f s p' q')). Qed.
Lemma lem4408332 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term496 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4408333 (p : Prop) (q : Prop) (p' : Prop) : term497 p q p'.
Proof. exact (fun q' : Prop => @lem4408332 p q p' q'). Qed.
Lemma lem4408334 (p : Prop) (q : Prop) : term498 p q.
Proof. exact (fun p' : Prop => @lem4408333 p q p'). Qed.
Lemma lem4408335 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : term504 A K k f x.
Proof. exact (@lem4408334 (term505 K x k) ((term453 A K k f x) = (@ARB A))). Qed.
Lemma lem4408336 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (p' : Prop) : term506 A K k f x p'.
Proof. exact (@lem4408335 A K k f x p'). Qed.
Lemma lem4408337 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (p' : Prop) : (term506 A K k f x p') = (term507 A K k f x p').
Proof. exact (eq_refl (term506 A K k f x p')). Qed.
Lemma lem4408338 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (p' : Prop) : term507 A K k f x p'.
Proof. exact (EQ_MP (@lem4408337 A K k f x p') (@lem4408336 A K k f x p')). Qed.
Lemma lem4408339 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (p' : Prop) (q' : Prop) : term508 A K k f x p' q'.
Proof. exact (@lem4408338 A K k f x p' q'). Qed.
Lemma lem4408340 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (p' : Prop) (q' : Prop) : (term508 A K k f x p' q') = (term509 A K k f x p' q').
Proof. exact (eq_refl (term508 A K k f x p' q')). Qed.
Lemma lem4408341 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (p' : Prop) (q' : Prop) : term509 A K k f x p' q'.
Proof. exact (EQ_MP (@lem4408340 A K k f x p' q') (@lem4408339 A K k f x p' q')). Qed.
Lemma lem4408342 {K : Type'} (x : K) (k : K -> Prop) : (term505 K x k) = (term505 K x k).
Proof. exact (eq_refl (term505 K x k)). Qed.
Lemma lem4408343 {A K : Type'} (f : K -> A) (x : K) (k : K -> Prop) (q' : Prop) : term510 A K f x k q'.
Proof. exact (@lem4408341 A K k f x (term505 K x k) q'). Qed.
Lemma lem4408344 {A K : Type'} (f : K -> A) (x : K) (k : K -> Prop) (q' : Prop) : term511 A K f x k q'.
Proof. exact (@lem4408343 A K f x k q' (@lem4408342 K x k)). Qed.
Lemma lem4408345 {K : Type'} (x : K) (k : K -> Prop) (h1 : term505 K x k) : term505 K x k.
Proof. exact (h1). Qed.
Lemma lem4408346 {K : Type'} (x : K) (k : K -> Prop) : term512 K x k.
Proof. exact (@lem82 (@IN K x k)). Qed.
Lemma lem4408351 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term513 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4408352 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term514 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4408351 _2963 g t e g' t' e'). Qed.
Lemma lem4408353 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term515 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4408352 _2963 g t e g' t'). Qed.
Lemma lem4408354 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term516 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4408353 _2963 g t e g'). Qed.
Lemma lem4408355 {A : Type'} (g : Prop) (t : A) (e : A) : term516 A g t e.
Proof. exact (@lem4408354 A g t e). Qed.
Lemma lem4408356 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : term517 A K k f x.
Proof. exact (@lem4408355 A (@IN K x k) (f x) (@ARB A)). Qed.
Lemma lem4408357 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (g' : Prop) : term518 A K k f x g'.
Proof. exact (@lem4408356 A K k f x g'). Qed.
Lemma lem4408358 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (g' : Prop) : (term518 A K k f x g') = (term519 A K k f x g').
Proof. exact (eq_refl (term518 A K k f x g')). Qed.
Lemma lem4408359 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (g' : Prop) : term519 A K k f x g'.
Proof. exact (EQ_MP (@lem4408358 A K k f x g') (@lem4408357 A K k f x g')). Qed.
Lemma lem4408360 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (g' : Prop) (t' : A) : term520 A K k f x g' t'.
Proof. exact (@lem4408359 A K k f x g' t'). Qed.
Lemma lem4408361 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (g' : Prop) (t' : A) : (term520 A K k f x g' t') = (term521 A K k f x g' t').
Proof. exact (eq_refl (term520 A K k f x g' t')). Qed.
Lemma lem4408362 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (g' : Prop) (t' : A) : term521 A K k f x g' t'.
Proof. exact (EQ_MP (@lem4408361 A K k f x g' t') (@lem4408360 A K k f x g' t')). Qed.
Lemma lem4408363 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (g' : Prop) (t' : A) (e' : A) : term522 A K k f x g' t' e'.
Proof. exact (@lem4408362 A K k f x g' t' e'). Qed.
Lemma lem4408364 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (g' : Prop) (t' : A) (e' : A) : (term522 A K k f x g' t' e') = (term523 A K k f x g' t' e').
Proof. exact (eq_refl (term522 A K k f x g' t' e')). Qed.
Lemma lem4408365 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (g' : Prop) (t' : A) (e' : A) : term523 A K k f x g' t' e'.
Proof. exact (EQ_MP (@lem4408364 A K k f x g' t' e') (@lem4408363 A K k f x g' t' e')). Qed.
Lemma lem4408367 {K : Type'} (x : K) (k : K -> Prop) (h1 : term505 K x k) : (@IN K x k) = False.
Proof. exact (@lem4408346 K x k (@lem4408345 K x k h1)). Qed.
Lemma lem4408368 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) (t' : A) (e' : A) : term524 A K k f x t' e'.
Proof. exact (@lem4408365 A K k f x False t' e'). Qed.
Lemma lem4408369 {A K : Type'} (f : K -> A) (t' : A) (e' : A) (x : K) (k : K -> Prop) (h1 : term505 K x k) : term525 A K k f x t' e'.
Proof. exact (@lem4408368 A K k f x t' e' (@lem4408367 K x k h1)). Qed.
Lemma lem4408373 {A K : Type'} (f : K -> A) (x : K) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4408374 {A K : Type'} (f : K -> A) (x : K) : term526 A K f x.
Proof. exact (fun h0 : False => @lem4408373 A K f x). Qed.
Lemma lem4408375 {A K : Type'} (f : K -> A) (e' : A) (x : K) (k : K -> Prop) (h1 : term505 K x k) : term527 A K k f x e'.
Proof. exact (@lem4408369 A K f (f x) e' x k h1). Qed.
Lemma lem4408376 {A K : Type'} (f : K -> A) (e' : A) (x : K) (k : K -> Prop) (h1 : term505 K x k) : term528 A K k f x e'.
Proof. exact (@lem4408375 A K f e' x k h1 (@lem4408374 A K f x)). Qed.
Lemma lem4408382 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4408383 {A : Type'} : term529 A.
Proof. exact (fun h0 : ~ False => @lem4408382 A). Qed.
Lemma lem4408384 {A K : Type'} (f : K -> A) (x : K) (k : K -> Prop) (h1 : term505 K x k) : term530 A K k f x.
Proof. exact (@lem4408376 A K f (@ARB A) x k h1). Qed.
Lemma lem4408385 {A K : Type'} (f : K -> A) (x : K) (k : K -> Prop) (h1 : term505 K x k) : (term453 A K k f x) = (term531 A K f x).
Proof. exact (@lem4408384 A K f x k h1 (@lem4408383 A)). Qed.
Lemma lem4408387 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4408388 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4408387 A t1 t2). Qed.
Lemma lem4408389 {A K : Type'} (f : K -> A) (x : K) : (term531 A K f x) = (@ARB A).
Proof. exact (@lem4408388 A (f x) (@ARB A)). Qed.
Lemma lem4408390 {A K : Type'} (f : K -> A) (x : K) (k : K -> Prop) (h1 : term505 K x k) : (term453 A K k f x) = (@ARB A).
Proof. exact (TRANS (@lem4408385 A K f x k h1) (@lem4408389 A K f x)). Qed.
Lemma lem4408391 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4408392 {A K : Type'} (f : K -> A) (x : K) (k : K -> Prop) (h1 : term505 K x k) : (term457 A K k f x) = (@eq A (@ARB A)).
Proof. exact (MK_COMB (@lem4408391 A) (@lem4408390 A K f x k h1)). Qed.
Lemma lem4408393 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4408394 {A K : Type'} (f : K -> A) (x : K) (k : K -> Prop) (h1 : term505 K x k) : ((term453 A K k f x) = (@ARB A)) = ((@ARB A) = (@ARB A)).
Proof. exact (MK_COMB (@lem4408392 A K f x k h1) (@lem4408393 A)). Qed.
Lemma lem4408396 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4408397 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem4408396 A x). Qed.
Lemma lem4408398 {A : Type'} : ((@ARB A) = (@ARB A)) = True.
Proof. exact (@lem4408397 A (@ARB A)). Qed.
Lemma lem4408399 {A K : Type'} (f : K -> A) (x : K) (k : K -> Prop) (h1 : term505 K x k) : ((term453 A K k f x) = (@ARB A)) = True.
Proof. exact (TRANS (@lem4408394 A K f x k h1) (@lem4408398 A)). Qed.
Lemma lem4408400 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : term532 A K k f x.
Proof. exact (fun h0 : term505 K x k => @lem4408399 A K f x k h0). Qed.
Lemma lem4408401 {A K : Type'} (f : K -> A) (x : K) (k : K -> Prop) : term533 A K f x k.
Proof. exact (@lem4408344 A K f x k True). Qed.
Lemma lem4408402 {A K : Type'} (f : K -> A) (x : K) (k : K -> Prop) : (term460 A K k f x) = (term534 K x k).
Proof. exact (@lem4408401 A K f x k (@lem4408400 A K k f x)). Qed.
Lemma lem4408404 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4408405 {K : Type'} (x : K) (k : K -> Prop) : (term534 K x k) = True.
Proof. exact (@lem4408404 (term505 K x k)). Qed.
Lemma lem4408406 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term460 A K k f x) = True.
Proof. exact (TRANS (@lem4408402 A K f x k) (@lem4408405 K x k)). Qed.
Lemma lem4408407 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term462 A K k f) = (term535 K).
Proof. exact (fun_ext (fun x : K => @lem4408406 A K k f x)). Qed.
Lemma lem4408408 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4408409 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term463 A K k f) = (term536 K).
Proof. exact (MK_COMB (@lem4408408 K) (@lem4408407 A K k f)). Qed.
Lemma lem4408411 {A : Type'} (t : Prop) : (term175 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4408412 {K : Type'} (t : Prop) : (term175 K t) = t.
Proof. exact (@lem4408411 K t). Qed.
Lemma lem4408413 {K : Type'} : (term536 K) = True.
Proof. exact (@lem4408412 K True). Qed.
Lemma lem4408414 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term463 A K k f) = True.
Proof. exact (TRANS (@lem4408409 A K k f) (@lem4408413 K)). Qed.
Lemma lem4408415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4408416 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term465 A K k f) = (and True).
Proof. exact (MK_COMB (@lem4408415) (@lem4408414 A K k f)). Qed.
Lemma lem4408424 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term496 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4408425 (p : Prop) (q : Prop) (p' : Prop) : term497 p q p'.
Proof. exact (fun q' : Prop => @lem4408424 p q p' q'). Qed.
Lemma lem4408426 (p : Prop) (q : Prop) : term498 p q.
Proof. exact (fun p' : Prop => @lem4408425 p q p'). Qed.
Lemma lem4408427 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : term537 A K k f s i.
Proof. exact (@lem4408426 (@IN K i k) (term469 A K k f s i)). Qed.
Lemma lem4408428 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) : term538 A K k f s i p'.
Proof. exact (@lem4408427 A K k f s i p'). Qed.
Lemma lem4408429 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) : (term538 A K k f s i p') = (term539 A K k f s i p').
Proof. exact (eq_refl (term538 A K k f s i p')). Qed.
Lemma lem4408430 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) : term539 A K k f s i p'.
Proof. exact (EQ_MP (@lem4408429 A K k f s i p') (@lem4408428 A K k f s i p')). Qed.
Lemma lem4408431 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : term540 A K k f s i p' q'.
Proof. exact (@lem4408430 A K k f s i p' q'). Qed.
Lemma lem4408432 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : (term540 A K k f s i p' q') = (term541 A K k f s i p' q').
Proof. exact (eq_refl (term540 A K k f s i p' q')). Qed.
Lemma lem4408433 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : term541 A K k f s i p' q'.
Proof. exact (EQ_MP (@lem4408432 A K k f s i p' q') (@lem4408431 A K k f s i p' q')). Qed.
Lemma lem4408434 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@IN K i k).
Proof. exact (eq_refl (@IN K i k)). Qed.
Lemma lem4408435 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (q' : Prop) : term542 A K f s i k q'.
Proof. exact (@lem4408433 A K k f s i (@IN K i k) q'). Qed.
Lemma lem4408436 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (q' : Prop) : term543 A K f s i k q'.
Proof. exact (@lem4408435 A K f s i k q' (@lem4408434 K i k)). Qed.
Lemma lem4408437 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4408438 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = ((@IN K i k) = True).
Proof. exact (@lem7 (@IN K i k)). Qed.
Lemma lem4408441 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term513 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4408442 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term514 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4408441 _2963 g t e g' t' e'). Qed.
Lemma lem4408443 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term515 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4408442 _2963 g t e g' t'). Qed.
Lemma lem4408444 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term516 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4408443 _2963 g t e g'). Qed.
Lemma lem4408445 {A : Type'} (g : Prop) (t : A) (e : A) : term516 A g t e.
Proof. exact (@lem4408444 A g t e). Qed.
Lemma lem4408446 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : term517 A K k f i.
Proof. exact (@lem4408445 A (@IN K i k) (f i) (@ARB A)). Qed.
Lemma lem4408447 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) : term518 A K k f i g'.
Proof. exact (@lem4408446 A K k f i g'). Qed.
Lemma lem4408448 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) : (term518 A K k f i g') = (term519 A K k f i g').
Proof. exact (eq_refl (term518 A K k f i g')). Qed.
Lemma lem4408449 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) : term519 A K k f i g'.
Proof. exact (EQ_MP (@lem4408448 A K k f i g') (@lem4408447 A K k f i g')). Qed.
Lemma lem4408450 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) : term520 A K k f i g' t'.
Proof. exact (@lem4408449 A K k f i g' t'). Qed.
Lemma lem4408451 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) : (term520 A K k f i g' t') = (term521 A K k f i g' t').
Proof. exact (eq_refl (term520 A K k f i g' t')). Qed.
Lemma lem4408452 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) : term521 A K k f i g' t'.
Proof. exact (EQ_MP (@lem4408451 A K k f i g' t') (@lem4408450 A K k f i g' t')). Qed.
Lemma lem4408453 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) (e' : A) : term522 A K k f i g' t' e'.
Proof. exact (@lem4408452 A K k f i g' t' e'). Qed.
Lemma lem4408454 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) (e' : A) : (term522 A K k f i g' t' e') = (term523 A K k f i g' t' e').
Proof. exact (eq_refl (term522 A K k f i g' t' e')). Qed.
Lemma lem4408455 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) (e' : A) : term523 A K k f i g' t' e'.
Proof. exact (EQ_MP (@lem4408454 A K k f i g' t' e') (@lem4408453 A K k f i g' t' e')). Qed.
Lemma lem4408457 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (@IN K i k) = True.
Proof. exact (EQ_MP (@lem4408438 K i k) (@lem4408437 K i k h1)). Qed.
Lemma lem4408458 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (t' : A) (e' : A) : term544 A K k f i t' e'.
Proof. exact (@lem4408455 A K k f i True t' e'). Qed.
Lemma lem4408459 {A K : Type'} (f : K -> A) (t' : A) (e' : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term545 A K k f i t' e'.
Proof. exact (@lem4408458 A K k f i t' e' (@lem4408457 K i k h1)). Qed.
Lemma lem4408465 {A K : Type'} (f : K -> A) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4408466 {A K : Type'} (f : K -> A) (i : K) : term546 A K f i.
Proof. exact (fun h0 : True => @lem4408465 A K f i). Qed.
Lemma lem4408467 {A K : Type'} (f : K -> A) (e' : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term547 A K k f i e'.
Proof. exact (@lem4408459 A K f (f i) e' i k h1). Qed.
Lemma lem4408468 {A K : Type'} (f : K -> A) (e' : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term548 A K k f i e'.
Proof. exact (@lem4408467 A K f e' i k h1 (@lem4408466 A K f i)). Qed.
Lemma lem4408472 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4408473 {A : Type'} : term549 A.
Proof. exact (fun h0 : ~ True => @lem4408472 A). Qed.
Lemma lem4408474 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term550 A K k f i.
Proof. exact (@lem4408468 A K f (@ARB A) i k h1). Qed.
Lemma lem4408475 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term453 A K k f i) = (term551 A K f i).
Proof. exact (@lem4408474 A K f i k h1 (@lem4408473 A)). Qed.
Lemma lem4408477 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4408478 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4408477 A t2 t1). Qed.
Lemma lem4408479 {A K : Type'} (f : K -> A) (i : K) : (term551 A K f i) = (f i).
Proof. exact (@lem4408478 A (@ARB A) (f i)). Qed.
Lemma lem4408480 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term453 A K k f i) = (f i).
Proof. exact (TRANS (@lem4408475 A K f i k h1) (@lem4408479 A K f i)). Qed.
Lemma lem4408481 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4408482 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term467 A K k f i) = (term552 A K f i).
Proof. exact (MK_COMB (@lem4408481 A) (@lem4408480 A K f i k h1)). Qed.
Lemma lem4408483 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4408484 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term469 A K k f s i) = (term553 A K f s i).
Proof. exact (MK_COMB (@lem4408482 A K f i k h1) (@lem4408483 A K s i)). Qed.
Lemma lem4408485 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : term554 A K k f s i.
Proof. exact (fun h0 : @IN K i k => @lem4408484 A K f s i k h0). Qed.
Lemma lem4408486 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : term555 A K k f s i.
Proof. exact (@lem4408436 A K f s i k (term553 A K f s i)). Qed.
Lemma lem4408487 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term471 A K k f s i) = (term376 A K k f s i).
Proof. exact (@lem4408486 A K k f s i (@lem4408485 A K k f s i)). Qed.
Lemma lem4408511 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term473 A K k f s) = (term378 A K k f s).
Proof. exact (fun_ext (fun i : K => @lem4408487 A K k f s i)). Qed.
Lemma lem4408535 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4408536 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term475 A K k f s) = (term380 A K k f s).
Proof. exact (MK_COMB (@lem4408535 K) (@lem4408511 A K k f s)). Qed.
Lemma lem4408564 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term477 A K k f s) = (term556 A K k f s).
Proof. exact (MK_COMB (@lem4408416 A K k f) (@lem4408536 A K k f s)). Qed.
Lemma lem4408566 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4408567 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term556 A K k f s) = (term380 A K k f s).
Proof. exact (@lem4408566 (term380 A K k f s)). Qed.
Lemma lem4408595 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term477 A K k f s) = (term380 A K k f s).
Proof. exact (TRANS (@lem4408564 A K k f s) (@lem4408567 A K k f s)). Qed.
Lemma lem4408596 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4408597 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term478 A K k f s) = (term395 A K k f s).
Proof. exact (MK_COMB (@lem4408596) (@lem4408595 A K k f s)). Qed.
Lemma lem4408625 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (q' : Prop) : term557 A K k f s q'.
Proof. exact (@lem4408322 A K k f s (term395 A K k f s) q'). Qed.
Lemma lem4408626 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (q' : Prop) : term558 A K k f s q'.
Proof. exact (@lem4408625 A K k f s q' (@lem4408597 A K k f s)). Qed.
Lemma lem4408627 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (h1 : term395 A K k f s) : term395 A K k f s.
Proof. exact (h1). Qed.
Lemma lem4408628 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : term559 A K k f s.
Proof. exact (@lem82 (term380 A K k f s)). Qed.
Lemma lem4408631 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (h1 : term395 A K k f s) : (term380 A K k f s) = False.
Proof. exact (@lem4408628 A K k f s (@lem4408627 A K k f s h1)). Qed.
Lemma lem4408632 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (h1 : term395 A K k f s) : (term380 A K k f s) = False.
Proof. exact (@lem4408631 A K k f s h1). Qed.
Lemma lem4408633 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4408634 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (h1 : term395 A K k f s) : (term395 A K k f s) = (~ False).
Proof. exact (MK_COMB (@lem4408633) (@lem4408632 A K k f s h1)). Qed.
Lemma lem4408636 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4408637 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (h1 : term395 A K k f s) : (term395 A K k f s) = True.
Proof. exact (TRANS (@lem4408634 A K k f s h1) (@lem4408636)). Qed.
Lemma lem4408638 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : term560 A K k f s.
Proof. exact (fun h0 : term395 A K k f s => @lem4408637 A K k f s h0). Qed.
Lemma lem4408639 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : term561 A K k f s.
Proof. exact (@lem4408626 A K k f s True). Qed.
Lemma lem4408640 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term482 A K k f s) = (term562 A K k f s).
Proof. exact (@lem4408639 A K k f s (@lem4408638 A K k f s)). Qed.
Lemma lem4408642 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4408643 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term562 A K k f s) = True.
Proof. exact (@lem4408642 (term395 A K k f s)). Qed.
Lemma lem4408644 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term482 A K k f s) = True.
Proof. exact (TRANS (@lem4408640 A K k f s) (@lem4408643 A K k f s)). Qed.
Lemma lem4408645 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : True = (term482 A K k f s).
Proof. exact (SYM (@lem4408644 A K k f s)). Qed.
Lemma lem4408646 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : term482 A K k f s.
Proof. exact (EQ_MP (@lem4408645 A K k f s) (@lem0)). Qed.
Lemma lem4408650 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term496 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4408651 (p : Prop) (q : Prop) (p' : Prop) : term497 p q p'.
Proof. exact (fun q' : Prop => @lem4408650 p q p' q'). Qed.
Lemma lem4408652 (p : Prop) (q : Prop) : term498 p q.
Proof. exact (fun p' : Prop => @lem4408651 p q p'). Qed.
Lemma lem4408653 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : term563 A K k f s.
Proof. exact (@lem4408652 (term483 A K k f s) (term493 A K k f s)). Qed.
Lemma lem4408654 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (p' : Prop) : term564 A K k f s p'.
Proof. exact (@lem4408653 A K k f s p'). Qed.
Lemma lem4408655 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (p' : Prop) : (term564 A K k f s p') = (term565 A K k f s p').
Proof. exact (eq_refl (term564 A K k f s p')). Qed.
Lemma lem4408656 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (p' : Prop) : term565 A K k f s p'.
Proof. exact (EQ_MP (@lem4408655 A K k f s p') (@lem4408654 A K k f s p')). Qed.
Lemma lem4408657 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (p' : Prop) (q' : Prop) : term566 A K k f s p' q'.
Proof. exact (@lem4408656 A K k f s p' q'). Qed.
Lemma lem4408658 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (p' : Prop) (q' : Prop) : (term566 A K k f s p' q') = (term567 A K k f s p' q').
Proof. exact (eq_refl (term566 A K k f s p' q')). Qed.
Lemma lem4408659 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (p' : Prop) (q' : Prop) : term567 A K k f s p' q'.
Proof. exact (EQ_MP (@lem4408658 A K k f s p' q') (@lem4408657 A K k f s p' q')). Qed.
Lemma lem4408667 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term496 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4408668 (p : Prop) (q : Prop) (p' : Prop) : term497 p q p'.
Proof. exact (fun q' : Prop => @lem4408667 p q p' q'). Qed.
Lemma lem4408669 (p : Prop) (q : Prop) : term498 p q.
Proof. exact (fun p' : Prop => @lem4408668 p q p'). Qed.
Lemma lem4408670 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : term537 A K k f s i.
Proof. exact (@lem4408669 (@IN K i k) (term469 A K k f s i)). Qed.
Lemma lem4408671 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) : term538 A K k f s i p'.
Proof. exact (@lem4408670 A K k f s i p'). Qed.
Lemma lem4408672 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) : (term538 A K k f s i p') = (term539 A K k f s i p').
Proof. exact (eq_refl (term538 A K k f s i p')). Qed.
Lemma lem4408673 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) : term539 A K k f s i p'.
Proof. exact (EQ_MP (@lem4408672 A K k f s i p') (@lem4408671 A K k f s i p')). Qed.
Lemma lem4408674 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : term540 A K k f s i p' q'.
Proof. exact (@lem4408673 A K k f s i p' q'). Qed.
Lemma lem4408675 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : (term540 A K k f s i p' q') = (term541 A K k f s i p' q').
Proof. exact (eq_refl (term540 A K k f s i p' q')). Qed.
Lemma lem4408676 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : term541 A K k f s i p' q'.
Proof. exact (EQ_MP (@lem4408675 A K k f s i p' q') (@lem4408674 A K k f s i p' q')). Qed.
Lemma lem4408677 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@IN K i k).
Proof. exact (eq_refl (@IN K i k)). Qed.
Lemma lem4408678 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (q' : Prop) : term542 A K f s i k q'.
Proof. exact (@lem4408676 A K k f s i (@IN K i k) q'). Qed.
Lemma lem4408679 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (q' : Prop) : term543 A K f s i k q'.
Proof. exact (@lem4408678 A K f s i k q' (@lem4408677 K i k)). Qed.
Lemma lem4408680 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4408681 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = ((@IN K i k) = True).
Proof. exact (@lem7 (@IN K i k)). Qed.
Lemma lem4408684 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term513 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4408685 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term514 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4408684 _2963 g t e g' t' e'). Qed.
Lemma lem4408686 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term515 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4408685 _2963 g t e g' t'). Qed.
Lemma lem4408687 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term516 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4408686 _2963 g t e g'). Qed.
Lemma lem4408688 {A : Type'} (g : Prop) (t : A) (e : A) : term516 A g t e.
Proof. exact (@lem4408687 A g t e). Qed.
Lemma lem4408689 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : term517 A K k f i.
Proof. exact (@lem4408688 A (@IN K i k) (f i) (@ARB A)). Qed.
Lemma lem4408690 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) : term518 A K k f i g'.
Proof. exact (@lem4408689 A K k f i g'). Qed.
Lemma lem4408691 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) : (term518 A K k f i g') = (term519 A K k f i g').
Proof. exact (eq_refl (term518 A K k f i g')). Qed.
Lemma lem4408692 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) : term519 A K k f i g'.
Proof. exact (EQ_MP (@lem4408691 A K k f i g') (@lem4408690 A K k f i g')). Qed.
Lemma lem4408693 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) : term520 A K k f i g' t'.
Proof. exact (@lem4408692 A K k f i g' t'). Qed.
Lemma lem4408694 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) : (term520 A K k f i g' t') = (term521 A K k f i g' t').
Proof. exact (eq_refl (term520 A K k f i g' t')). Qed.
Lemma lem4408695 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) : term521 A K k f i g' t'.
Proof. exact (EQ_MP (@lem4408694 A K k f i g' t') (@lem4408693 A K k f i g' t')). Qed.
Lemma lem4408696 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) (e' : A) : term522 A K k f i g' t' e'.
Proof. exact (@lem4408695 A K k f i g' t' e'). Qed.
Lemma lem4408697 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) (e' : A) : (term522 A K k f i g' t' e') = (term523 A K k f i g' t' e').
Proof. exact (eq_refl (term522 A K k f i g' t' e')). Qed.
Lemma lem4408698 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (g' : Prop) (t' : A) (e' : A) : term523 A K k f i g' t' e'.
Proof. exact (EQ_MP (@lem4408697 A K k f i g' t' e') (@lem4408696 A K k f i g' t' e')). Qed.
Lemma lem4408700 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (@IN K i k) = True.
Proof. exact (EQ_MP (@lem4408681 K i k) (@lem4408680 K i k h1)). Qed.
Lemma lem4408701 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (t' : A) (e' : A) : term544 A K k f i t' e'.
Proof. exact (@lem4408698 A K k f i True t' e'). Qed.
Lemma lem4408702 {A K : Type'} (f : K -> A) (t' : A) (e' : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term545 A K k f i t' e'.
Proof. exact (@lem4408701 A K k f i t' e' (@lem4408700 K i k h1)). Qed.
Lemma lem4408708 {A K : Type'} (f : K -> A) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4408709 {A K : Type'} (f : K -> A) (i : K) : term546 A K f i.
Proof. exact (fun h0 : True => @lem4408708 A K f i). Qed.
Lemma lem4408710 {A K : Type'} (f : K -> A) (e' : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term547 A K k f i e'.
Proof. exact (@lem4408702 A K f (f i) e' i k h1). Qed.
Lemma lem4408711 {A K : Type'} (f : K -> A) (e' : A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term548 A K k f i e'.
Proof. exact (@lem4408710 A K f e' i k h1 (@lem4408709 A K f i)). Qed.
Lemma lem4408715 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4408716 {A : Type'} : term549 A.
Proof. exact (fun h0 : ~ True => @lem4408715 A). Qed.
Lemma lem4408717 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term550 A K k f i.
Proof. exact (@lem4408711 A K f (@ARB A) i k h1). Qed.
Lemma lem4408718 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term453 A K k f i) = (term551 A K f i).
Proof. exact (@lem4408717 A K f i k h1 (@lem4408716 A)). Qed.
Lemma lem4408720 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4408721 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4408720 A t2 t1). Qed.
Lemma lem4408722 {A K : Type'} (f : K -> A) (i : K) : (term551 A K f i) = (f i).
Proof. exact (@lem4408721 A (@ARB A) (f i)). Qed.
Lemma lem4408723 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term453 A K k f i) = (f i).
Proof. exact (TRANS (@lem4408718 A K f i k h1) (@lem4408722 A K f i)). Qed.
Lemma lem4408724 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4408725 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term467 A K k f i) = (term552 A K f i).
Proof. exact (MK_COMB (@lem4408724 A) (@lem4408723 A K f i k h1)). Qed.
Lemma lem4408726 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4408727 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term469 A K k f s i) = (term553 A K f s i).
Proof. exact (MK_COMB (@lem4408725 A K f i k h1) (@lem4408726 A K s i)). Qed.
Lemma lem4408728 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : term554 A K k f s i.
Proof. exact (fun h0 : @IN K i k => @lem4408727 A K f s i k h0). Qed.
Lemma lem4408729 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : term555 A K k f s i.
Proof. exact (@lem4408679 A K f s i k (term553 A K f s i)). Qed.
Lemma lem4408730 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term471 A K k f s i) = (term376 A K k f s i).
Proof. exact (@lem4408729 A K k f s i (@lem4408728 A K k f s i)). Qed.
Lemma lem4408754 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term473 A K k f s) = (term378 A K k f s).
Proof. exact (fun_ext (fun i : K => @lem4408730 A K k f s i)). Qed.
Lemma lem4408778 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4408779 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term475 A K k f s) = (term380 A K k f s).
Proof. exact (MK_COMB (@lem4408778 K) (@lem4408754 A K k f s)). Qed.
Lemma lem4408807 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4408808 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term483 A K k f s) = (term395 A K k f s).
Proof. exact (MK_COMB (@lem4408807) (@lem4408779 A K k f s)). Qed.
Lemma lem4408836 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (q' : Prop) : term568 A K k f s q'.
Proof. exact (@lem4408659 A K k f s (term395 A K k f s) q'). Qed.
Lemma lem4408837 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (q' : Prop) : term569 A K k f s q'.
Proof. exact (@lem4408836 A K k f s q' (@lem4408808 A K k f s)). Qed.
Lemma lem4408838 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (h1 : term395 A K k f s) : term395 A K k f s.
Proof. exact (h1). Qed.
Lemma lem4408839 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : term559 A K k f s.
Proof. exact (@lem82 (term380 A K k f s)). Qed.
Lemma lem4408875 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (h1 : term395 A K k f s) : (term380 A K k f s) = False.
Proof. exact (@lem4408839 A K k f s (@lem4408838 A K k f s h1)). Qed.
Lemma lem4408876 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (h1 : term395 A K k f s) : (term380 A K k f s) = False.
Proof. exact (@lem4408875 A K k f s h1). Qed.
Lemma lem4408877 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term491 A K k f) = (term491 A K k f).
Proof. exact (eq_refl (term491 A K k f)). Qed.
Lemma lem4408878 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (h1 : term395 A K k f s) : (term492 A K k f s) = (term570 A K k f).
Proof. exact (MK_COMB (@lem4408877 A K k f) (@lem4408876 A K k f s h1)). Qed.
Lemma lem4408880 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem4408881 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term570 A K k f) = False.
Proof. exact (@lem4408880 (term434 A K k f)). Qed.
Lemma lem4408882 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (h1 : term395 A K k f s) : (term492 A K k f s) = False.
Proof. exact (TRANS (@lem4408878 A K k f s h1) (@lem4408881 A K k f)). Qed.
Lemma lem4408883 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4408884 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (h1 : term395 A K k f s) : (term493 A K k f s) = (~ False).
Proof. exact (MK_COMB (@lem4408883) (@lem4408882 A K k f s h1)). Qed.
Lemma lem4408886 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4408887 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (h1 : term395 A K k f s) : (term493 A K k f s) = True.
Proof. exact (TRANS (@lem4408884 A K k f s h1) (@lem4408886)). Qed.
Lemma lem4408888 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : term571 A K k f s.
Proof. exact (fun h0 : term395 A K k f s => @lem4408887 A K k f s h0). Qed.
Lemma lem4408889 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : term572 A K k f s.
Proof. exact (@lem4408837 A K k f s True). Qed.
Lemma lem4408890 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term495 A K k f s) = (term562 A K k f s).
Proof. exact (@lem4408889 A K k f s (@lem4408888 A K k f s)). Qed.
Lemma lem4408892 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4408893 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term562 A K k f s) = True.
Proof. exact (@lem4408892 (term395 A K k f s)). Qed.
Lemma lem4408894 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term495 A K k f s) = True.
Proof. exact (TRANS (@lem4408890 A K k f s) (@lem4408893 A K k f s)). Qed.
Lemma lem4408895 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : True = (term495 A K k f s).
Proof. exact (SYM (@lem4408894 A K k f s)). Qed.
Lemma lem4408896 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : term495 A K k f s.
Proof. exact (EQ_MP (@lem4408895 A K k f s) (@lem0)). Qed.
Lemma lem4408897 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : term494 A K k f s.
Proof. exact (EQ_MP (@lem4408309 A K k f s) (@lem4408896 A K k f s)). Qed.
Lemma lem4408898 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : term481 A K k f s.
Proof. exact (EQ_MP (@lem4408200 A K k f s) (@lem4408646 A K k f s)). Qed.
Lemma lem4408899 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term398 A K k s) : term417 A K k f s.
Proof. exact (@lem4408897 A K k f s (@lem4408062 A K f k s h1)). Qed.
Lemma lem4408900 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term419 A K k s) : term395 A K k f s.
Proof. exact (@lem4408898 A K k f s (@lem4408059 A K f k s h1)). Qed.
Lemma lem4408905 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term398 A K k s) : term419 A K k s.
Proof. exact (fun f : K -> A => @lem4408899 A K f k s h1). Qed.
Lemma lem4408910 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term419 A K k s) : term398 A K k s.
Proof. exact (fun f : K -> A => @lem4408900 A K f k s h1). Qed.
Lemma lem4408911 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term573 A K k s.
Proof. exact (fun h0 : term398 A K k s => @lem4408905 A K k s h0). Qed.
Lemma lem4408912 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term574 A K k s.
Proof. exact (fun h0 : term419 A K k s => @lem4408910 A K k s h0). Qed.
Lemma lem4408913 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term575 A K k s.
Proof. exact (conj (@lem4408912 A K k s) (@lem4408911 A K k s)). Qed.
Lemma lem4408914 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term575 A K k s) = ((term419 A K k s) = (term398 A K k s)).
Proof. exact (@lem32 (term419 A K k s) (term398 A K k s)). Qed.
Lemma lem4408915 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term419 A K k s) = (term398 A K k s).
Proof. exact (EQ_MP (@lem4408914 A K k s) (@lem4408913 A K k s)). Qed.
Lemma lem4408916 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term361 A K k s) = (term398 A K k s).
Proof. exact (EQ_MP (@lem4408054 A K k s) (@lem4408915 A K k s)). Qed.
Lemma lem4408917 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term352 A K k s) = (term36 A K k s).
Proof. exact (EQ_MP (@lem4407974 A K k s) (@lem4408916 A K k s)). Qed.
Lemma lem4408918 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term352 A K k s) = (term32 A K k s).
Proof. exact (EQ_MP (@lem4407857 A K k s) (@lem4408917 A K k s)). Qed.
Lemma lem4408919 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term32 A K k s).
Proof. exact (EQ_MP (@lem4407831 A K k s) (@lem4408918 A K k s)). Qed.
Lemma lem4408924 {A K : Type'} (k : K -> Prop) : term576 A K k.
Proof. exact (fun s : type1470 A K => @lem4408919 A K k s). Qed.
Lemma lem4408929 {A K : Type'} : term577 A K.
Proof. exact (fun k : K -> Prop => @lem4408924 A K k). Qed.
