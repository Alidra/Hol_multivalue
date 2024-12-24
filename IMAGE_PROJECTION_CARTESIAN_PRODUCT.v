Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_PROJECTION_CARTESIAN_PRODUCT_term_abbrevs.
Require Import CARTESIAN_PRODUCT_spec.
Require Import CARTESIAN_PRODUCT_EQ_EMPTY_spec.
Require Import DISJ_ACI_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import IMAGE_CLAUSES_spec.
Require Import IN_IMAGE_spec.
Require Import IN_SING_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import SUBSET_spec.
Require Import SUBSET_ANTISYM_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm15249_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
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
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4437201 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4437202 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem4437201 _83095 p). Qed.
Lemma lem4437203 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem4437204 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem4437203 _83095 p) (@lem4437202 _83095 p)). Qed.
Lemma lem4437205 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem4437204 _83095 p x). Qed.
Lemma lem4437206 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem4437215 {A B : Type'} (y : B) : term5 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4437216 {A B : Type'} (y : B) : (term5 A B y) = (term6 A B y).
Proof. exact (eq_refl (term5 A B y)). Qed.
Lemma lem4437217 {A B : Type'} (y : B) : term6 A B y.
Proof. exact (EQ_MP (@lem4437216 A B y) (@lem4437215 A B y)). Qed.
Lemma lem4437218 {A B : Type'} (y : B) (s : A -> Prop) : term7 A B y s.
Proof. exact (@lem4437217 A B y s). Qed.
Lemma lem4437219 {A B : Type'} (y : B) (s : A -> Prop) : (term7 A B y s) = (term8 A B y s).
Proof. exact (eq_refl (term7 A B y s)). Qed.
Lemma lem4437220 {A B : Type'} (y : B) (s : A -> Prop) : term8 A B y s.
Proof. exact (EQ_MP (@lem4437219 A B y s) (@lem4437218 A B y s)). Qed.
Lemma lem4437221 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term9 A B y s f.
Proof. exact (@lem4437220 A B y s f). Qed.
Lemma lem4437222 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term9 A B y s f) = ((term10 A B y f s) = (term11 A B y f s)).
Proof. exact (eq_refl (term9 A B y s f)). Qed.
Lemma lem4437224 {A : Type'} (P : A -> Prop) : term12 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem4437225 {A : Type'} (P : A -> Prop) : (term12 A P) = (term13 A P).
Proof. exact (eq_refl (term12 A P)). Qed.
Lemma lem4437226 {A : Type'} (P : A -> Prop) : term13 A P.
Proof. exact (EQ_MP (@lem4437225 A P) (@lem4437224 A P)). Qed.
Lemma lem4437227 {A : Type'} (P : A -> Prop) (Q : Prop) : term14 A P Q.
Proof. exact (@lem4437226 A P Q). Qed.
Lemma lem4437228 {A : Type'} (P : A -> Prop) (Q : Prop) : (term14 A P Q) = ((term15 A P Q) = (term16 A P Q)).
Proof. exact (eq_refl (term14 A P Q)). Qed.
Lemma lem4437230 {A B : Type'} (P : type1413 A B) : term17 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem4437231 {A B : Type'} (P : type1413 A B) : (term17 A B P) = ((term18 A B P) = (term19 A B P)).
Proof. exact (eq_refl (term17 A B P)). Qed.
Lemma lem4437256 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4437257 {_106555 : Type'} (s : _106555 -> Prop) (t : _106555 -> Prop) : (s = t) = (term20 _106555 s t).
Proof. exact (@lem4437256 _106555 s t). Qed.
Lemma lem4437258 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : ((s i) = (@EMPTY _106555)) = (term21 _106555 _106572 s i).
Proof. exact (@lem4437257 _106555 (s i) (@EMPTY _106555)). Qed.
Lemma lem4437267 {_106572 : Type'} (i : _106572) (k : _106572 -> Prop) : (term22 _106572 i k) = (term22 _106572 i k).
Proof. exact (eq_refl (term22 _106572 i k)). Qed.
Lemma lem4437268 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term23 _106555 _106572 k s i) = (term24 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437267 _106572 i k) (@lem4437258 _106555 _106572 s i)). Qed.
Lemma lem4437271 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term25 _106555 _106572 k s) = (term26 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437268 _106555 _106572 k s i)). Qed.
Lemma lem4437272 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4437273 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term27 _106555 _106572 k s) = (term28 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437272 _106572) (@lem4437271 _106555 _106572 k s)). Qed.
Lemma lem4437278 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4437279 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term29 _106555 _106572 k s) = (term30 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437278) (@lem4437273 _106555 _106572 k s)). Qed.
Lemma lem4437280 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4437281 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term31 _106555 _106572 k s) = (term32 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437280) (@lem4437279 _106555 _106572 k s)). Qed.
Lemma lem4437292 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term33 _106555 _106572 k s) = (term33 _106555 _106572 k s).
Proof. exact (eq_refl (term33 _106555 _106572 k s)). Qed.
Lemma lem4437293 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term29 _106555 _106572 k s) = (term33 _106555 _106572 k s)) = ((term30 _106555 _106572 k s) = (term33 _106555 _106572 k s)).
Proof. exact (MK_COMB (@lem4437281 _106555 _106572 k s) (@lem4437292 _106555 _106572 k s)). Qed.
Lemma lem4437298 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term30 _106555 _106572 k s) = (term33 _106555 _106572 k s)) = ((term29 _106555 _106572 k s) = (term33 _106555 _106572 k s)).
Proof. exact (SYM (@lem4437293 _106555 _106572 k s)). Qed.
Lemma lem4437308 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4437309 {_106572 : Type'} (P : _106572 -> Prop) (x : _106572) : (@IN _106572 x P) = (P x).
Proof. exact (@lem4437308 _106572 P x). Qed.
Lemma lem4437310 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (@IN _106572 i k) = (k i).
Proof. exact (@lem4437309 _106572 k i). Qed.
Lemma lem4437311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4437312 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term22 _106572 i k) = (term34 _106572 k i).
Proof. exact (MK_COMB (@lem4437311) (@lem4437310 _106572 k i)). Qed.
Lemma lem4437320 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4437321 {_106555 : Type'} (P : _106555 -> Prop) (x : _106555) : (@IN _106555 x P) = (P x).
Proof. exact (@lem4437320 _106555 P x). Qed.
Lemma lem4437322 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term35 _106555 _106572 x s i) = (s i x).
Proof. exact (@lem4437321 _106555 (s i) x). Qed.
Lemma lem4437323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4437324 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term36 _106555 _106572 x s i) = (term37 _106555 _106572 s i x).
Proof. exact (MK_COMB (@lem4437323) (@lem4437322 _106555 _106572 s i x)). Qed.
Lemma lem4437326 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4437327 {_106555 : Type'} (x : _106555) : (@IN _106555 x (@EMPTY _106555)) = False.
Proof. exact (@lem4437326 _106555 x). Qed.
Lemma lem4437328 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : ((term35 _106555 _106572 x s i) = (@IN _106555 x (@EMPTY _106555))) = ((s i x) = False).
Proof. exact (MK_COMB (@lem4437324 _106555 _106572 s i x) (@lem4437327 _106555 x)). Qed.
Lemma lem4437330 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4437331 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : ((s i x) = False) = (term38 _106555 _106572 s i x).
Proof. exact (@lem4437330 (s i x)). Qed.
Lemma lem4437332 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : ((term35 _106555 _106572 x s i) = (@IN _106555 x (@EMPTY _106555))) = (term38 _106555 _106572 s i x).
Proof. exact (TRANS (@lem4437328 _106555 _106572 s i x) (@lem4437331 _106555 _106572 s i x)). Qed.
Lemma lem4437333 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term39 _106555 _106572 s i) = (term40 _106555 _106572 s i).
Proof. exact (fun_ext (fun x : _106555 => @lem4437332 _106555 _106572 s i x)). Qed.
Lemma lem4437334 {_106555 : Type'} : (@all _106555) = (@all _106555).
Proof. exact (eq_refl (@all _106555)). Qed.
Lemma lem4437335 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term21 _106555 _106572 s i) = (term41 _106555 _106572 s i).
Proof. exact (MK_COMB (@lem4437334 _106555) (@lem4437333 _106555 _106572 s i)). Qed.
Lemma lem4437340 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term24 _106555 _106572 k s i) = (term42 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437312 _106572 k i) (@lem4437335 _106555 _106572 s i)). Qed.
Lemma lem4437343 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term26 _106555 _106572 k s) = (term43 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437340 _106555 _106572 k s i)). Qed.
Lemma lem4437344 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4437345 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term28 _106555 _106572 k s) = (term44 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437344 _106572) (@lem4437343 _106555 _106572 k s)). Qed.
Lemma lem4437350 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4437351 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term30 _106555 _106572 k s) = (term45 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437350) (@lem4437345 _106555 _106572 k s)). Qed.
Lemma lem4437352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4437353 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term32 _106555 _106572 k s) = (term46 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437352) (@lem4437351 _106555 _106572 k s)). Qed.
Lemma lem4437365 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4437366 {_106572 : Type'} (P : _106572 -> Prop) (x : _106572) : (@IN _106572 x P) = (P x).
Proof. exact (@lem4437365 _106572 P x). Qed.
Lemma lem4437367 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (@IN _106572 i k) = (k i).
Proof. exact (@lem4437366 _106572 k i). Qed.
Lemma lem4437368 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4437369 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term47 _106572 i k) = (term48 _106572 k i).
Proof. exact (MK_COMB (@lem4437368) (@lem4437367 _106572 k i)). Qed.
Lemma lem4437371 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4437372 {_106555 : Type'} (P : _106555 -> Prop) (x : _106555) : (@IN _106555 x P) = (P x).
Proof. exact (@lem4437371 _106555 P x). Qed.
Lemma lem4437373 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term35 _106555 _106572 a s i) = (s i a).
Proof. exact (@lem4437372 _106555 (s i) a). Qed.
Lemma lem4437374 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term49 _106555 _106572 k a s i) = (term50 _106555 _106572 k s i a).
Proof. exact (MK_COMB (@lem4437369 _106572 k i) (@lem4437373 _106555 _106572 s i a)). Qed.
Lemma lem4437377 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term51 _106555 _106572 k s i) = (term52 _106555 _106572 k s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4437374 _106555 _106572 k s i a)). Qed.
Lemma lem4437378 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4437379 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term53 _106555 _106572 k s i) = (term54 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437378 _106555) (@lem4437377 _106555 _106572 k s i)). Qed.
Lemma lem4437384 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term55 _106555 _106572 k s) = (term56 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437379 _106555 _106572 k s i)). Qed.
Lemma lem4437385 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4437386 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term33 _106555 _106572 k s) = (term57 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437385 _106572) (@lem4437384 _106555 _106572 k s)). Qed.
Lemma lem4437391 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term30 _106555 _106572 k s) = (term33 _106555 _106572 k s)) = ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s)).
Proof. exact (MK_COMB (@lem4437353 _106555 _106572 k s) (@lem4437386 _106555 _106572 k s)). Qed.
Lemma lem4437394 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s)) = ((term30 _106555 _106572 k s) = (term33 _106555 _106572 k s)).
Proof. exact (SYM (@lem4437391 _106555 _106572 k s)). Qed.
Lemma lem4437396 (p : Prop) : p = (term58 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4437397 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s)) = (term59 _106555 _106572 k s).
Proof. exact (@lem4437396 ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s))). Qed.
Lemma lem4437398 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term59 _106555 _106572 k s) = ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s)).
Proof. exact (SYM (@lem4437397 _106555 _106572 k s)). Qed.
Lemma lem4437399 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term60 _106555 _106572 k s) : term60 _106555 _106572 k s.
Proof. exact (h1). Qed.
Lemma lem4437402 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term59 _106555 _106572 k s) : term59 _106555 _106572 k s.
Proof. exact (h1). Qed.
Lemma lem4437403 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : term61 _106555 _106572 k s.
Proof. exact (fun h0 : term59 _106555 _106572 k s => @lem4437402 _106555 _106572 k s h0). Qed.
Lemma lem4437404 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term61 _106555 _106572 k s) : term61 _106555 _106572 k s.
Proof. exact (h1). Qed.
Lemma lem4437405 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term59 _106555 _106572 k s) : term59 _106555 _106572 k s.
Proof. exact (h1). Qed.
Lemma lem4437406 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term59 _106555 _106572 k s) (h2 : term61 _106555 _106572 k s) : term59 _106555 _106572 k s.
Proof. exact (@lem4437404 _106555 _106572 k s h2 (@lem4437405 _106555 _106572 k s h1)). Qed.
Lemma lem4437407 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term59 _106555 _106572 k s) : term62 _106555 _106572 k s.
Proof. exact (fun h0 : term61 _106555 _106572 k s => @lem4437406 _106555 _106572 k s h1 h0). Qed.
Lemma lem4437408 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term61 _106555 _106572 k s) : term61 _106555 _106572 k s.
Proof. exact (h1). Qed.
Lemma lem4437409 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term59 _106555 _106572 k s) (h2 : term61 _106555 _106572 k s) : term59 _106555 _106572 k s.
Proof. exact (@lem4437407 _106555 _106572 k s h1 (@lem4437408 _106555 _106572 k s h2)). Qed.
Lemma lem4437410 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term61 _106555 _106572 k s) : term61 _106555 _106572 k s.
Proof. exact (fun h0 : term59 _106555 _106572 k s => @lem4437409 _106555 _106572 k s h0 h1). Qed.
Lemma lem4437411 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : term63 _106555 _106572 k s.
Proof. exact (fun h0 : term61 _106555 _106572 k s => @lem4437410 _106555 _106572 k s h0). Qed.
Lemma lem4437414 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : term61 _106555 _106572 k s.
Proof. exact (@lem4437411 _106555 _106572 k s (@lem4437403 _106555 _106572 k s)). Qed.
Lemma lem4437415 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : term61 _106555 _106572 k s.
Proof. exact (@lem4437414 _106555 _106572 k s). Qed.
Lemma lem4437425 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4437426 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term59 _106555 _106572 k s) = (term64 _106555 _106572 k s).
Proof. exact (@lem4437425 (term60 _106555 _106572 k s)). Qed.
Lemma lem4437428 (t : Prop) : (term65 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4437429 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term64 _106555 _106572 k s) = ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s)).
Proof. exact (@lem4437428 ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s))). Qed.
Lemma lem4437430 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term59 _106555 _106572 k s) = ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s)).
Proof. exact (TRANS (@lem4437426 _106555 _106572 k s) (@lem4437429 _106555 _106572 k s)). Qed.
Lemma lem4437475 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) : (term66 _106555 _106572 s) = (term67 _106555 _106572 s).
Proof. exact (fun_ext (fun k : _106572 -> Prop => @lem4437430 _106555 _106572 k s)). Qed.
Lemma lem4437476 {_106572 : Type'} : (@all (_106572 -> Prop)) = (@all (_106572 -> Prop)).
Proof. exact (eq_refl (@all (_106572 -> Prop))). Qed.
Lemma lem4437477 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) : (term68 _106555 _106572 s) = (term69 _106555 _106572 s).
Proof. exact (MK_COMB (@lem4437476 _106572) (@lem4437475 _106555 _106572 s)). Qed.
Lemma lem4437482 {_106555 _106572 : Type'} : (term70 _106555 _106572) = (term71 _106555 _106572).
Proof. exact (fun_ext (fun s : type1470 _106555 _106572 => @lem4437477 _106555 _106572 s)). Qed.
Lemma lem4437483 {_106555 _106572 : Type'} : (@all (_106572 -> _106555 -> Prop)) = (@all (_106572 -> _106555 -> Prop)).
Proof. exact (eq_refl (@all (_106572 -> _106555 -> Prop))). Qed.
Lemma lem4437492 {_106555 _106572 : Type'} : (term72 _106555 _106572) = (term73 _106555 _106572).
Proof. exact (MK_COMB (@lem4437483 _106555 _106572) (@lem4437482 _106555 _106572)). Qed.
Lemma lem4437497 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term50 _106555 _106572 k s i a) = (term50 _106555 _106572 k s i a).
Proof. exact (eq_refl (term50 _106555 _106572 k s i a)). Qed.
Lemma lem4437498 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term52 _106555 _106572 k s i) = (term52 _106555 _106572 k s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4437497 _106555 _106572 k s i a)). Qed.
Lemma lem4437499 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4437500 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term54 _106555 _106572 k s i) = (term54 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437499 _106555) (@lem4437498 _106555 _106572 k s i)). Qed.
Lemma lem4437501 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term56 _106555 _106572 k s) = (term56 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437500 _106555 _106572 k s i)). Qed.
Lemma lem4437502 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4437503 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term57 _106555 _106572 k s) = (term57 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437502 _106572) (@lem4437501 _106555 _106572 k s)). Qed.
Lemma lem4437506 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term38 _106555 _106572 s i x) = (term38 _106555 _106572 s i x).
Proof. exact (eq_refl (term38 _106555 _106572 s i x)). Qed.
Lemma lem4437507 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term40 _106555 _106572 s i) = (term40 _106555 _106572 s i).
Proof. exact (fun_ext (fun x : _106555 => @lem4437506 _106555 _106572 s i x)). Qed.
Lemma lem4437508 {_106555 : Type'} : (@all _106555) = (@all _106555).
Proof. exact (eq_refl (@all _106555)). Qed.
Lemma lem4437509 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term41 _106555 _106572 s i) = (term41 _106555 _106572 s i).
Proof. exact (MK_COMB (@lem4437508 _106555) (@lem4437507 _106555 _106572 s i)). Qed.
Lemma lem4437512 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term34 _106572 k i) = (term34 _106572 k i).
Proof. exact (eq_refl (term34 _106572 k i)). Qed.
Lemma lem4437513 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term42 _106555 _106572 k s i) = (term42 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437512 _106572 k i) (@lem4437509 _106555 _106572 s i)). Qed.
Lemma lem4437514 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term43 _106555 _106572 k s) = (term43 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437513 _106555 _106572 k s i)). Qed.
Lemma lem4437515 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4437516 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term44 _106555 _106572 k s) = (term44 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437515 _106572) (@lem4437514 _106555 _106572 k s)). Qed.
Lemma lem4437517 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4437518 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term45 _106555 _106572 k s) = (term45 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437517) (@lem4437516 _106555 _106572 k s)). Qed.
Lemma lem4437519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4437520 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term46 _106555 _106572 k s) = (term46 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437519) (@lem4437518 _106555 _106572 k s)). Qed.
Lemma lem4437521 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s)) = ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s)).
Proof. exact (MK_COMB (@lem4437520 _106555 _106572 k s) (@lem4437503 _106555 _106572 k s)). Qed.
Lemma lem4437522 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) : (term67 _106555 _106572 s) = (term67 _106555 _106572 s).
Proof. exact (fun_ext (fun k : _106572 -> Prop => @lem4437521 _106555 _106572 k s)). Qed.
Lemma lem4437523 {_106572 : Type'} : (@all (_106572 -> Prop)) = (@all (_106572 -> Prop)).
Proof. exact (eq_refl (@all (_106572 -> Prop))). Qed.
Lemma lem4437524 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) : (term69 _106555 _106572 s) = (term69 _106555 _106572 s).
Proof. exact (MK_COMB (@lem4437523 _106572) (@lem4437522 _106555 _106572 s)). Qed.
Lemma lem4437525 {_106555 _106572 : Type'} : (term71 _106555 _106572) = (term71 _106555 _106572).
Proof. exact (fun_ext (fun s : type1470 _106555 _106572 => @lem4437524 _106555 _106572 s)). Qed.
Lemma lem4437526 {_106555 _106572 : Type'} : (@all (_106572 -> _106555 -> Prop)) = (@all (_106572 -> _106555 -> Prop)).
Proof. exact (eq_refl (@all (_106572 -> _106555 -> Prop))). Qed.
Lemma lem4437527 {_106555 _106572 : Type'} : (term73 _106555 _106572) = (term73 _106555 _106572).
Proof. exact (MK_COMB (@lem4437526 _106555 _106572) (@lem4437525 _106555 _106572)). Qed.
Lemma lem4437570 {_106555 _106572 : Type'} : (term72 _106555 _106572) = (term73 _106555 _106572).
Proof. exact (TRANS (@lem4437492 _106555 _106572) (@lem4437527 _106555 _106572)). Qed.
Lemma lem4437571 {_106555 _106572 : Type'} : (term73 _106555 _106572) = (term72 _106555 _106572).
Proof. exact (SYM (@lem4437570 _106555 _106572)). Qed.
Lemma lem4437573 (p : Prop) : p = (term58 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4437574 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s)) = (term59 _106555 _106572 k s).
Proof. exact (@lem4437573 ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s))). Qed.
Lemma lem4437575 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term59 _106555 _106572 k s) = ((term45 _106555 _106572 k s) = (term57 _106555 _106572 k s)).
Proof. exact (SYM (@lem4437574 _106555 _106572 k s)). Qed.
Lemma lem4437576 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term60 _106555 _106572 k s) : term60 _106555 _106572 k s.
Proof. exact (h1). Qed.
Lemma lem4437579 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term38 _106555 _106572 s i x) = (term38 _106555 _106572 s i x).
Proof. exact (eq_refl (term38 _106555 _106572 s i x)). Qed.
Lemma lem4437582 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term74 _106555 _106572 s i x) = (s i x).
Proof. exact (@lem16933 (s i x)). Qed.
Lemma lem4437583 {_106555 : Type'} (P : _106555 -> Prop) : (term75 _106555 P) = (term76 _106555 P).
Proof. exact (@lem18392 _106555 P). Qed.
Lemma lem4437584 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term77 _106555 _106572 s i) = (term78 _106555 _106572 s i).
Proof. exact (@lem4437583 _106555 (term40 _106555 _106572 s i)). Qed.
Lemma lem4437585 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term79 _106555 _106572 s i x) = (term38 _106555 _106572 s i x).
Proof. exact (eq_refl (term79 _106555 _106572 s i x)). Qed.
Lemma lem4437586 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4437587 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term80 _106555 _106572 s i x) = (term74 _106555 _106572 s i x).
Proof. exact (MK_COMB (@lem4437586) (@lem4437585 _106555 _106572 s i x)). Qed.
Lemma lem4437588 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term80 _106555 _106572 s i x) = (s i x).
Proof. exact (TRANS (@lem4437587 _106555 _106572 s i x) (@lem4437582 _106555 _106572 s i x)). Qed.
Lemma lem4437589 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term81 _106555 _106572 s i) = (term82 _106555 _106572 s i).
Proof. exact (fun_ext (fun x : _106555 => @lem4437588 _106555 _106572 s i x)). Qed.
Lemma lem4437590 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4437591 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term78 _106555 _106572 s i) = (term83 _106555 _106572 s i).
Proof. exact (MK_COMB (@lem4437590 _106555) (@lem4437589 _106555 _106572 s i)). Qed.
Lemma lem4437592 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term77 _106555 _106572 s i) = (term83 _106555 _106572 s i).
Proof. exact (TRANS (@lem4437584 _106555 _106572 s i) (@lem4437591 _106555 _106572 s i)). Qed.
Lemma lem4437593 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term40 _106555 _106572 s i) = (term40 _106555 _106572 s i).
Proof. exact (fun_ext (fun x : _106555 => @lem4437579 _106555 _106572 s i x)). Qed.
Lemma lem4437594 {_106555 : Type'} : (@all _106555) = (@all _106555).
Proof. exact (eq_refl (@all _106555)). Qed.
Lemma lem4437595 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term41 _106555 _106572 s i) = (term41 _106555 _106572 s i).
Proof. exact (MK_COMB (@lem4437594 _106555) (@lem4437593 _106555 _106572 s i)). Qed.
Lemma lem4437597 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term84 _106572 k i) = (term84 _106572 k i).
Proof. exact (eq_refl (term84 _106572 k i)). Qed.
Lemma lem4437598 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term85 _106555 _106572 k s i) = (term86 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437597 _106572 k i) (@lem4437592 _106555 _106572 s i)). Qed.
Lemma lem4437599 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term87 _106555 _106572 k s i) = (term85 _106555 _106572 k s i).
Proof. exact (@lem17045 (k i) (term41 _106555 _106572 s i)). Qed.
Lemma lem4437600 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term87 _106555 _106572 k s i) = (term86 _106555 _106572 k s i).
Proof. exact (TRANS (@lem4437599 _106555 _106572 k s i) (@lem4437598 _106555 _106572 k s i)). Qed.
Lemma lem4437602 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term34 _106572 k i) = (term34 _106572 k i).
Proof. exact (eq_refl (term34 _106572 k i)). Qed.
Lemma lem4437603 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term42 _106555 _106572 k s i) = (term42 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437602 _106572 k i) (@lem4437595 _106555 _106572 s i)). Qed.
Lemma lem4437604 {_106572 : Type'} (P : _106572 -> Prop) : (term88 _106572 P) = (term89 _106572 P).
Proof. exact (@lem18394 _106572 P). Qed.
Lemma lem4437605 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term45 _106555 _106572 k s) = (term90 _106555 _106572 k s).
Proof. exact (@lem4437604 _106572 (term43 _106555 _106572 k s)). Qed.
Lemma lem4437606 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term91 _106555 _106572 k s i) = (term42 _106555 _106572 k s i).
Proof. exact (eq_refl (term91 _106555 _106572 k s i)). Qed.
Lemma lem4437607 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4437608 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term92 _106555 _106572 k s i) = (term87 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437607) (@lem4437606 _106555 _106572 k s i)). Qed.
Lemma lem4437609 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term92 _106555 _106572 k s i) = (term86 _106555 _106572 k s i).
Proof. exact (TRANS (@lem4437608 _106555 _106572 k s i) (@lem4437600 _106555 _106572 k s i)). Qed.
Lemma lem4437610 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term93 _106555 _106572 k s) = (term94 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437609 _106555 _106572 k s i)). Qed.
Lemma lem4437611 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4437612 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term90 _106555 _106572 k s) = (term95 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437611 _106572) (@lem4437610 _106555 _106572 k s)). Qed.
Lemma lem4437613 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term45 _106555 _106572 k s) = (term95 _106555 _106572 k s).
Proof. exact (TRANS (@lem4437605 _106555 _106572 k s) (@lem4437612 _106555 _106572 k s)). Qed.
Lemma lem4437614 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term43 _106555 _106572 k s) = (term43 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437603 _106555 _106572 k s i)). Qed.
Lemma lem4437615 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4437616 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term44 _106555 _106572 k s) = (term44 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437615 _106572) (@lem4437614 _106555 _106572 k s)). Qed.
Lemma lem4437617 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term96 _106555 _106572 k s) = (term44 _106555 _106572 k s).
Proof. exact (@lem16933 (term44 _106555 _106572 k s)). Qed.
Lemma lem4437618 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term96 _106555 _106572 k s) = (term44 _106555 _106572 k s).
Proof. exact (TRANS (@lem4437617 _106555 _106572 k s) (@lem4437616 _106555 _106572 k s)). Qed.
Lemma lem4437627 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term97 _106555 _106572 k s i a) = (term98 _106555 _106572 k s i a).
Proof. exact (@lem17362 (k i) (s i a)). Qed.
Lemma lem4437632 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term50 _106555 _106572 k s i a) = (term99 _106555 _106572 k s i a).
Proof. exact (@lem17265 (k i) (s i a)). Qed.
Lemma lem4437633 {_106555 : Type'} (P : _106555 -> Prop) : (term88 _106555 P) = (term89 _106555 P).
Proof. exact (@lem18394 _106555 P). Qed.
Lemma lem4437634 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term100 _106555 _106572 k s i) = (term101 _106555 _106572 k s i).
Proof. exact (@lem4437633 _106555 (term52 _106555 _106572 k s i)). Qed.
Lemma lem4437635 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term102 _106555 _106572 k s i a) = (term50 _106555 _106572 k s i a).
Proof. exact (eq_refl (term102 _106555 _106572 k s i a)). Qed.
Lemma lem4437636 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4437637 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term103 _106555 _106572 k s i a) = (term97 _106555 _106572 k s i a).
Proof. exact (MK_COMB (@lem4437636) (@lem4437635 _106555 _106572 k s i a)). Qed.
Lemma lem4437638 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term103 _106555 _106572 k s i a) = (term98 _106555 _106572 k s i a).
Proof. exact (TRANS (@lem4437637 _106555 _106572 k s i a) (@lem4437627 _106555 _106572 k s i a)). Qed.
Lemma lem4437639 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term104 _106555 _106572 k s i) = (term105 _106555 _106572 k s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4437638 _106555 _106572 k s i a)). Qed.
Lemma lem4437640 {_106555 : Type'} : (@all _106555) = (@all _106555).
Proof. exact (eq_refl (@all _106555)). Qed.
Lemma lem4437641 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term101 _106555 _106572 k s i) = (term106 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437640 _106555) (@lem4437639 _106555 _106572 k s i)). Qed.
Lemma lem4437642 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term100 _106555 _106572 k s i) = (term106 _106555 _106572 k s i).
Proof. exact (TRANS (@lem4437634 _106555 _106572 k s i) (@lem4437641 _106555 _106572 k s i)). Qed.
Lemma lem4437643 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term52 _106555 _106572 k s i) = (term107 _106555 _106572 k s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4437632 _106555 _106572 k s i a)). Qed.
Lemma lem4437644 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4437645 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term54 _106555 _106572 k s i) = (term108 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437644 _106555) (@lem4437643 _106555 _106572 k s i)). Qed.
Lemma lem4437646 {_106572 : Type'} (P : _106572 -> Prop) : (term75 _106572 P) = (term76 _106572 P).
Proof. exact (@lem18392 _106572 P). Qed.
Lemma lem4437647 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term109 _106555 _106572 k s) = (term110 _106555 _106572 k s).
Proof. exact (@lem4437646 _106572 (term56 _106555 _106572 k s)). Qed.
Lemma lem4437648 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term111 _106555 _106572 k s i) = (term54 _106555 _106572 k s i).
Proof. exact (eq_refl (term111 _106555 _106572 k s i)). Qed.
Lemma lem4437649 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4437650 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term112 _106555 _106572 k s i) = (term100 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437649) (@lem4437648 _106555 _106572 k s i)). Qed.
Lemma lem4437651 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term112 _106555 _106572 k s i) = (term106 _106555 _106572 k s i).
Proof. exact (TRANS (@lem4437650 _106555 _106572 k s i) (@lem4437642 _106555 _106572 k s i)). Qed.
Lemma lem4437652 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term113 _106555 _106572 k s) = (term114 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437651 _106555 _106572 k s i)). Qed.
Lemma lem4437653 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4437654 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term110 _106555 _106572 k s) = (term115 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437653 _106572) (@lem4437652 _106555 _106572 k s)). Qed.
Lemma lem4437655 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term109 _106555 _106572 k s) = (term115 _106555 _106572 k s).
Proof. exact (TRANS (@lem4437647 _106555 _106572 k s) (@lem4437654 _106555 _106572 k s)). Qed.
Lemma lem4437656 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term56 _106555 _106572 k s) = (term116 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437645 _106555 _106572 k s i)). Qed.
Lemma lem4437657 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4437658 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term57 _106555 _106572 k s) = (term117 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437657 _106572) (@lem4437656 _106555 _106572 k s)). Qed.
Lemma lem4437659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4437660 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term118 _106555 _106572 k s) = (term119 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437659) (@lem4437618 _106555 _106572 k s)). Qed.
Lemma lem4437661 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term120 _106555 _106572 k s) = (term121 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437660 _106555 _106572 k s) (@lem4437658 _106555 _106572 k s)). Qed.
Lemma lem4437662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4437663 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term122 _106555 _106572 k s) = (term123 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437662) (@lem4437613 _106555 _106572 k s)). Qed.
Lemma lem4437664 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term124 _106555 _106572 k s) = (term125 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437663 _106555 _106572 k s) (@lem4437655 _106555 _106572 k s)). Qed.
Lemma lem4437665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4437666 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term126 _106555 _106572 k s) = (term127 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437665) (@lem4437664 _106555 _106572 k s)). Qed.
Lemma lem4437667 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term128 _106555 _106572 k s) = (term129 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437666 _106555 _106572 k s) (@lem4437661 _106555 _106572 k s)). Qed.
Lemma lem4437668 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term60 _106555 _106572 k s) = (term128 _106555 _106572 k s).
Proof. exact (@lem17646 (term45 _106555 _106572 k s) (term57 _106555 _106572 k s)). Qed.
Lemma lem4437669 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term60 _106555 _106572 k s) = (term129 _106555 _106572 k s).
Proof. exact (TRANS (@lem4437668 _106555 _106572 k s) (@lem4437667 _106555 _106572 k s)). Qed.
Lemma lem4437727 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4437728 {_106555 : Type'} (P : _106555 -> Prop) (Q : _106555 -> Prop) : (term130 _106555 P Q) = (term131 _106555 P Q).
Proof. exact (@lem4437727 _106555 P Q). Qed.
Lemma lem4437729 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term132 _106555 _106572 k s i) = (term133 _106555 _106572 k s i).
Proof. exact (@lem4437728 _106555 (term134 _106555 _106572 k i) (term40 _106555 _106572 s i)). Qed.
Lemma lem4437730 {_106555 _106572 : Type'} (a : _106555) (k : _106572 -> Prop) (i : _106572) : (term135 _106555 _106572 k i a) = (k i).
Proof. exact (eq_refl (term135 _106555 _106572 k i a)). Qed.
Lemma lem4437731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4437732 {_106555 _106572 : Type'} (a : _106555) (k : _106572 -> Prop) (i : _106572) : (term136 _106555 _106572 k i a) = (term34 _106572 k i).
Proof. exact (MK_COMB (@lem4437731) (@lem4437730 _106555 _106572 a k i)). Qed.
Lemma lem4437733 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term79 _106555 _106572 s i a) = (term38 _106555 _106572 s i a).
Proof. exact (eq_refl (term79 _106555 _106572 s i a)). Qed.
Lemma lem4437734 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term137 _106555 _106572 k s i a) = (term98 _106555 _106572 k s i a).
Proof. exact (MK_COMB (@lem4437732 _106555 _106572 a k i) (@lem4437733 _106555 _106572 s i a)). Qed.
Lemma lem4437735 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term138 _106555 _106572 k s i) = (term105 _106555 _106572 k s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4437734 _106555 _106572 k s i a)). Qed.
Lemma lem4437736 {_106555 : Type'} : (@all _106555) = (@all _106555).
Proof. exact (eq_refl (@all _106555)). Qed.
Lemma lem4437737 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term132 _106555 _106572 k s i) = (term106 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437736 _106555) (@lem4437735 _106555 _106572 k s i)). Qed.
Lemma lem4437738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4437739 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term139 _106555 _106572 k s i) = (term140 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437738) (@lem4437737 _106555 _106572 k s i)). Qed.
Lemma lem4437740 {_106555 _106572 : Type'} (a : _106555) (k : _106572 -> Prop) (i : _106572) : (term135 _106555 _106572 k i a) = (k i).
Proof. exact (eq_refl (term135 _106555 _106572 k i a)). Qed.
Lemma lem4437741 {_106555 _106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term141 _106555 _106572 k i) = (term134 _106555 _106572 k i).
Proof. exact (fun_ext (fun a : _106555 => @lem4437740 _106555 _106572 a k i)). Qed.
Lemma lem4437742 {_106555 : Type'} : (@all _106555) = (@all _106555).
Proof. exact (eq_refl (@all _106555)). Qed.
Lemma lem4437743 {_106555 _106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term142 _106555 _106572 k i) = (term143 _106555 _106572 k i).
Proof. exact (MK_COMB (@lem4437742 _106555) (@lem4437741 _106555 _106572 k i)). Qed.
Lemma lem4437744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4437745 {_106555 _106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term144 _106555 _106572 k i) = (term145 _106555 _106572 k i).
Proof. exact (MK_COMB (@lem4437744) (@lem4437743 _106555 _106572 k i)). Qed.
Lemma lem4437746 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term79 _106555 _106572 s i a) = (term38 _106555 _106572 s i a).
Proof. exact (eq_refl (term79 _106555 _106572 s i a)). Qed.
Lemma lem4437747 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term146 _106555 _106572 s i) = (term40 _106555 _106572 s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4437746 _106555 _106572 s i a)). Qed.
Lemma lem4437748 {_106555 : Type'} : (@all _106555) = (@all _106555).
Proof. exact (eq_refl (@all _106555)). Qed.
Lemma lem4437749 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term147 _106555 _106572 s i) = (term41 _106555 _106572 s i).
Proof. exact (MK_COMB (@lem4437748 _106555) (@lem4437747 _106555 _106572 s i)). Qed.
Lemma lem4437750 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term133 _106555 _106572 k s i) = (term148 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437745 _106555 _106572 k i) (@lem4437749 _106555 _106572 s i)). Qed.
Lemma lem4437751 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : ((term132 _106555 _106572 k s i) = (term133 _106555 _106572 k s i)) = ((term106 _106555 _106572 k s i) = (term148 _106555 _106572 k s i)).
Proof. exact (MK_COMB (@lem4437739 _106555 _106572 k s i) (@lem4437750 _106555 _106572 k s i)). Qed.
Lemma lem4437752 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term106 _106555 _106572 k s i) = (term148 _106555 _106572 k s i).
Proof. exact (EQ_MP (@lem4437751 _106555 _106572 k s i) (@lem4437729 _106555 _106572 k s i)). Qed.
Lemma lem4437754 {A : Type'} (t : Prop) : (term149 A t) = t.
Proof. exact (EQ_MP (@lem18935 A t) (@lem18934 A t)). Qed.
Lemma lem4437755 {_106555 : Type'} (t : Prop) : (term149 _106555 t) = t.
Proof. exact (@lem4437754 _106555 t). Qed.
Lemma lem4437756 {_106555 _106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term143 _106555 _106572 k i) = (k i).
Proof. exact (@lem4437755 _106555 (k i)). Qed.
Lemma lem4437757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4437758 {_106555 _106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term145 _106555 _106572 k i) = (term34 _106572 k i).
Proof. exact (MK_COMB (@lem4437757) (@lem4437756 _106555 _106572 k i)). Qed.
Lemma lem4437763 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term41 _106555 _106572 s i) = (term41 _106555 _106572 s i).
Proof. exact (eq_refl (term41 _106555 _106572 s i)). Qed.
Lemma lem4437764 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term148 _106555 _106572 k s i) = (term42 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437758 _106555 _106572 k i) (@lem4437763 _106555 _106572 s i)). Qed.
Lemma lem4437765 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term106 _106555 _106572 k s i) = (term42 _106555 _106572 k s i).
Proof. exact (TRANS (@lem4437752 _106555 _106572 k s i) (@lem4437764 _106555 _106572 k s i)). Qed.
Lemma lem4437766 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term114 _106555 _106572 k s) = (term43 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437765 _106555 _106572 k s i)). Qed.
Lemma lem4437767 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4437768 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term115 _106555 _106572 k s) = (term44 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437767 _106572) (@lem4437766 _106555 _106572 k s)). Qed.
Lemma lem4437797 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term123 _106555 _106572 k s) = (term123 _106555 _106572 k s).
Proof. exact (eq_refl (term123 _106555 _106572 k s)). Qed.
Lemma lem4437798 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term125 _106555 _106572 k s) = (term150 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437797 _106555 _106572 k s) (@lem4437768 _106555 _106572 k s)). Qed.
Lemma lem4437799 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4437800 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term127 _106555 _106572 k s) = (term151 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437799) (@lem4437798 _106555 _106572 k s)). Qed.
Lemma lem4437838 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4437839 {_106555 : Type'} (P : _106555 -> Prop) (Q : _106555 -> Prop) : (term152 _106555 P Q) = (term153 _106555 P Q).
Proof. exact (@lem4437838 _106555 P Q). Qed.
Lemma lem4437840 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term154 _106555 _106572 k s i) = (term155 _106555 _106572 k s i).
Proof. exact (@lem4437839 _106555 (term156 _106555 _106572 k i) (term82 _106555 _106572 s i)). Qed.
Lemma lem4437841 {_106555 _106572 : Type'} (a : _106555) (k : _106572 -> Prop) (i : _106572) : (term157 _106555 _106572 k i a) = (term158 _106572 k i).
Proof. exact (eq_refl (term157 _106555 _106572 k i a)). Qed.
Lemma lem4437842 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4437843 {_106555 _106572 : Type'} (a : _106555) (k : _106572 -> Prop) (i : _106572) : (term159 _106555 _106572 k i a) = (term84 _106572 k i).
Proof. exact (MK_COMB (@lem4437842) (@lem4437841 _106555 _106572 a k i)). Qed.
Lemma lem4437844 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term160 _106555 _106572 s i a) = (s i a).
Proof. exact (eq_refl (term160 _106555 _106572 s i a)). Qed.
Lemma lem4437845 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term161 _106555 _106572 k s i a) = (term99 _106555 _106572 k s i a).
Proof. exact (MK_COMB (@lem4437843 _106555 _106572 a k i) (@lem4437844 _106555 _106572 s i a)). Qed.
Lemma lem4437846 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term162 _106555 _106572 k s i) = (term107 _106555 _106572 k s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4437845 _106555 _106572 k s i a)). Qed.
Lemma lem4437847 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4437848 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term154 _106555 _106572 k s i) = (term108 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437847 _106555) (@lem4437846 _106555 _106572 k s i)). Qed.
Lemma lem4437849 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4437850 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term163 _106555 _106572 k s i) = (term164 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437849) (@lem4437848 _106555 _106572 k s i)). Qed.
Lemma lem4437851 {_106555 _106572 : Type'} (a : _106555) (k : _106572 -> Prop) (i : _106572) : (term157 _106555 _106572 k i a) = (term158 _106572 k i).
Proof. exact (eq_refl (term157 _106555 _106572 k i a)). Qed.
Lemma lem4437852 {_106555 _106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term165 _106555 _106572 k i) = (term156 _106555 _106572 k i).
Proof. exact (fun_ext (fun a : _106555 => @lem4437851 _106555 _106572 a k i)). Qed.
Lemma lem4437853 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4437854 {_106555 _106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term166 _106555 _106572 k i) = (term167 _106555 _106572 k i).
Proof. exact (MK_COMB (@lem4437853 _106555) (@lem4437852 _106555 _106572 k i)). Qed.
Lemma lem4437855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4437856 {_106555 _106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term168 _106555 _106572 k i) = (term169 _106555 _106572 k i).
Proof. exact (MK_COMB (@lem4437855) (@lem4437854 _106555 _106572 k i)). Qed.
Lemma lem4437857 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term160 _106555 _106572 s i a) = (s i a).
Proof. exact (eq_refl (term160 _106555 _106572 s i a)). Qed.
Lemma lem4437858 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term170 _106555 _106572 s i) = (term82 _106555 _106572 s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4437857 _106555 _106572 s i a)). Qed.
Lemma lem4437859 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4437860 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term171 _106555 _106572 s i) = (term83 _106555 _106572 s i).
Proof. exact (MK_COMB (@lem4437859 _106555) (@lem4437858 _106555 _106572 s i)). Qed.
Lemma lem4437861 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term155 _106555 _106572 k s i) = (term172 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437856 _106555 _106572 k i) (@lem4437860 _106555 _106572 s i)). Qed.
Lemma lem4437862 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : ((term154 _106555 _106572 k s i) = (term155 _106555 _106572 k s i)) = ((term108 _106555 _106572 k s i) = (term172 _106555 _106572 k s i)).
Proof. exact (MK_COMB (@lem4437850 _106555 _106572 k s i) (@lem4437861 _106555 _106572 k s i)). Qed.
Lemma lem4437863 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term108 _106555 _106572 k s i) = (term172 _106555 _106572 k s i).
Proof. exact (EQ_MP (@lem4437862 _106555 _106572 k s i) (@lem4437840 _106555 _106572 k s i)). Qed.
Lemma lem4437865 {A : Type'} (t : Prop) : (term173 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem4437866 {_106555 : Type'} (t : Prop) : (term173 _106555 t) = t.
Proof. exact (@lem4437865 _106555 t). Qed.
Lemma lem4437867 {_106555 _106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term167 _106555 _106572 k i) = (term158 _106572 k i).
Proof. exact (@lem4437866 _106555 (term158 _106572 k i)). Qed.
Lemma lem4437868 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4437869 {_106555 _106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term169 _106555 _106572 k i) = (term84 _106572 k i).
Proof. exact (MK_COMB (@lem4437868) (@lem4437867 _106555 _106572 k i)). Qed.
Lemma lem4437874 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term83 _106555 _106572 s i) = (term83 _106555 _106572 s i).
Proof. exact (eq_refl (term83 _106555 _106572 s i)). Qed.
Lemma lem4437875 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term172 _106555 _106572 k s i) = (term86 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437869 _106555 _106572 k i) (@lem4437874 _106555 _106572 s i)). Qed.
Lemma lem4437876 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term108 _106555 _106572 k s i) = (term86 _106555 _106572 k s i).
Proof. exact (TRANS (@lem4437863 _106555 _106572 k s i) (@lem4437875 _106555 _106572 k s i)). Qed.
Lemma lem4437877 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term116 _106555 _106572 k s) = (term94 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437876 _106555 _106572 k s i)). Qed.
Lemma lem4437878 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4437879 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term117 _106555 _106572 k s) = (term95 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437878 _106572) (@lem4437877 _106555 _106572 k s)). Qed.
Lemma lem4437928 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term119 _106555 _106572 k s) = (term119 _106555 _106572 k s).
Proof. exact (eq_refl (term119 _106555 _106572 k s)). Qed.
Lemma lem4437929 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term121 _106555 _106572 k s) = (term174 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437928 _106555 _106572 k s) (@lem4437879 _106555 _106572 k s)). Qed.
Lemma lem4437930 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term129 _106555 _106572 k s) = (term175 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437800 _106555 _106572 k s) (@lem4437929 _106555 _106572 k s)). Qed.
Lemma lem4437932 {A : Type'} (P : Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4437933 {_106555 : Type'} (P : Prop) (Q : _106555 -> Prop) : (term176 _106555 P Q) = (term177 _106555 P Q).
Proof. exact (@lem4437932 _106555 P Q). Qed.
Lemma lem4437934 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term178 _106555 _106572 k s i) = (term179 _106555 _106572 k s i).
Proof. exact (@lem4437933 _106555 (term158 _106572 k i) (term82 _106555 _106572 s i)). Qed.
Lemma lem4437935 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term160 _106555 _106572 s i x) = (s i x).
Proof. exact (eq_refl (term160 _106555 _106572 s i x)). Qed.
Lemma lem4437936 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term170 _106555 _106572 s i) = (term82 _106555 _106572 s i).
Proof. exact (fun_ext (fun x : _106555 => @lem4437935 _106555 _106572 s i x)). Qed.
Lemma lem4437937 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4437938 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term171 _106555 _106572 s i) = (term83 _106555 _106572 s i).
Proof. exact (MK_COMB (@lem4437937 _106555) (@lem4437936 _106555 _106572 s i)). Qed.
Lemma lem4437939 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term84 _106572 k i) = (term84 _106572 k i).
Proof. exact (eq_refl (term84 _106572 k i)). Qed.
Lemma lem4437940 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term178 _106555 _106572 k s i) = (term86 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437939 _106572 k i) (@lem4437938 _106555 _106572 s i)). Qed.
Lemma lem4437941 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4437942 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term180 _106555 _106572 k s i) = (term181 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437941) (@lem4437940 _106555 _106572 k s i)). Qed.
Lemma lem4437943 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term160 _106555 _106572 s i x) = (s i x).
Proof. exact (eq_refl (term160 _106555 _106572 s i x)). Qed.
Lemma lem4437944 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term84 _106572 k i) = (term84 _106572 k i).
Proof. exact (eq_refl (term84 _106572 k i)). Qed.
Lemma lem4437945 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term182 _106555 _106572 k s i x) = (term99 _106555 _106572 k s i x).
Proof. exact (MK_COMB (@lem4437944 _106572 k i) (@lem4437943 _106555 _106572 s i x)). Qed.
Lemma lem4437946 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term183 _106555 _106572 k s i) = (term107 _106555 _106572 k s i).
Proof. exact (fun_ext (fun x : _106555 => @lem4437945 _106555 _106572 k s i x)). Qed.
Lemma lem4437947 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4437948 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term179 _106555 _106572 k s i) = (term108 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437947 _106555) (@lem4437946 _106555 _106572 k s i)). Qed.
Lemma lem4437949 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : ((term178 _106555 _106572 k s i) = (term179 _106555 _106572 k s i)) = ((term86 _106555 _106572 k s i) = (term108 _106555 _106572 k s i)).
Proof. exact (MK_COMB (@lem4437942 _106555 _106572 k s i) (@lem4437948 _106555 _106572 k s i)). Qed.
Lemma lem4437950 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term86 _106555 _106572 k s i) = (term108 _106555 _106572 k s i).
Proof. exact (EQ_MP (@lem4437949 _106555 _106572 k s i) (@lem4437934 _106555 _106572 k s i)). Qed.
Lemma lem4437951 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term94 _106555 _106572 k s) = (term116 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437950 _106555 _106572 k s i)). Qed.
Lemma lem4437952 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4437953 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term95 _106555 _106572 k s) = (term117 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437952 _106572) (@lem4437951 _106555 _106572 k s)). Qed.
Lemma lem4437955 {A B : Type'} (P : type1413 A B) : (term18 A B P) = (term19 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4437956 {_106555 _106572 : Type'} (P : type1470 _106555 _106572) : (term184 _106555 _106572 P) = (term185 _106555 _106572 P).
Proof. exact (@lem4437955 _106572 _106555 P). Qed.
Lemma lem4437957 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term186 _106555 _106572 k s) = (term187 _106555 _106572 k s).
Proof. exact (@lem4437956 _106555 _106572 (term188 _106555 _106572 k s)). Qed.
Lemma lem4437958 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term189 _106555 _106572 k s i) = (term107 _106555 _106572 k s i).
Proof. exact (eq_refl (term189 _106555 _106572 k s i)). Qed.
Lemma lem4437959 {_106555 : Type'} (x : _106555) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4437960 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term190 _106555 _106572 k s i x) = (term191 _106555 _106572 k s i x).
Proof. exact (MK_COMB (@lem4437958 _106555 _106572 k s i) (@lem4437959 _106555 x)). Qed.
Lemma lem4437961 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term191 _106555 _106572 k s i x) = (term99 _106555 _106572 k s i x).
Proof. exact (eq_refl (term191 _106555 _106572 k s i x)). Qed.
Lemma lem4437962 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term190 _106555 _106572 k s i x) = (term99 _106555 _106572 k s i x).
Proof. exact (TRANS (@lem4437960 _106555 _106572 k s i x) (@lem4437961 _106555 _106572 k s i x)). Qed.
Lemma lem4437963 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term192 _106555 _106572 k s i) = (term107 _106555 _106572 k s i).
Proof. exact (fun_ext (fun x : _106555 => @lem4437962 _106555 _106572 k s i x)). Qed.
Lemma lem4437964 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4437965 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term193 _106555 _106572 k s i) = (term108 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4437964 _106555) (@lem4437963 _106555 _106572 k s i)). Qed.
Lemma lem4437966 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term194 _106555 _106572 k s) = (term116 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4437965 _106555 _106572 k s i)). Qed.
Lemma lem4437967 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4437968 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term186 _106555 _106572 k s) = (term117 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437967 _106572) (@lem4437966 _106555 _106572 k s)). Qed.
Lemma lem4437969 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4437970 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term195 _106555 _106572 k s) = (term196 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437969) (@lem4437968 _106555 _106572 k s)). Qed.
Lemma lem4437971 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term189 _106555 _106572 k s i) = (term107 _106555 _106572 k s i).
Proof. exact (eq_refl (term189 _106555 _106572 k s i)). Qed.
Lemma lem4437972 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem4437973 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) (i : _106572) : (term197 _106555 _106572 k s x i) = (term198 _106555 _106572 k s x i).
Proof. exact (MK_COMB (@lem4437971 _106555 _106572 k s i) (@lem4437972 _106555 _106572 x i)). Qed.
Lemma lem4437974 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) (i : _106572) : (term198 _106555 _106572 k s x i) = (term199 _106555 _106572 k s x i).
Proof. exact (eq_refl (term198 _106555 _106572 k s x i)). Qed.
Lemma lem4437975 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) (i : _106572) : (term197 _106555 _106572 k s x i) = (term199 _106555 _106572 k s x i).
Proof. exact (TRANS (@lem4437973 _106555 _106572 k s x i) (@lem4437974 _106555 _106572 k s x i)). Qed.
Lemma lem4437976 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) : (term200 _106555 _106572 k s x) = (term201 _106555 _106572 k s x).
Proof. exact (fun_ext (fun i : _106572 => @lem4437975 _106555 _106572 k s x i)). Qed.
Lemma lem4437977 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4437978 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) : (term202 _106555 _106572 k s x) = (term203 _106555 _106572 k s x).
Proof. exact (MK_COMB (@lem4437977 _106572) (@lem4437976 _106555 _106572 k s x)). Qed.
Lemma lem4437979 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term204 _106555 _106572 k s) = (term205 _106555 _106572 k s).
Proof. exact (fun_ext (fun x : _106572 -> _106555 => @lem4437978 _106555 _106572 k s x)). Qed.
Lemma lem4437980 {_106555 _106572 : Type'} : (@ex (_106572 -> _106555)) = (@ex (_106572 -> _106555)).
Proof. exact (eq_refl (@ex (_106572 -> _106555))). Qed.
Lemma lem4437981 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term187 _106555 _106572 k s) = (term206 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437980 _106555 _106572) (@lem4437979 _106555 _106572 k s)). Qed.
Lemma lem4437982 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term186 _106555 _106572 k s) = (term187 _106555 _106572 k s)) = ((term117 _106555 _106572 k s) = (term206 _106555 _106572 k s)).
Proof. exact (MK_COMB (@lem4437970 _106555 _106572 k s) (@lem4437981 _106555 _106572 k s)). Qed.
Lemma lem4437983 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term117 _106555 _106572 k s) = (term206 _106555 _106572 k s).
Proof. exact (EQ_MP (@lem4437982 _106555 _106572 k s) (@lem4437957 _106555 _106572 k s)). Qed.
Lemma lem4437984 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term95 _106555 _106572 k s) = (term206 _106555 _106572 k s).
Proof. exact (TRANS (@lem4437953 _106555 _106572 k s) (@lem4437983 _106555 _106572 k s)). Qed.
Lemma lem4437985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4437986 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term123 _106555 _106572 k s) = (term207 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437985) (@lem4437984 _106555 _106572 k s)). Qed.
Lemma lem4437987 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term44 _106555 _106572 k s) = (term44 _106555 _106572 k s).
Proof. exact (eq_refl (term44 _106555 _106572 k s)). Qed.
Lemma lem4437988 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term150 _106555 _106572 k s) = (term208 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437986 _106555 _106572 k s) (@lem4437987 _106555 _106572 k s)). Qed.
Lemma lem4437990 {A : Type'} (P : A -> Prop) (Q : Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4437991 {_106555 _106572 : Type'} (P : type805 _106555 _106572) (Q : Prop) : (term211 _106555 _106572 P Q) = (term212 _106555 _106572 P Q).
Proof. exact (@lem4437990 (_106572 -> _106555) P Q). Qed.
Lemma lem4437992 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term213 _106555 _106572 k s) = (term214 _106555 _106572 k s).
Proof. exact (@lem4437991 _106555 _106572 (term205 _106555 _106572 k s) (term44 _106555 _106572 k s)). Qed.
Lemma lem4437993 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) : (term215 _106555 _106572 k s x) = (term203 _106555 _106572 k s x).
Proof. exact (eq_refl (term215 _106555 _106572 k s x)). Qed.
Lemma lem4437994 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term216 _106555 _106572 k s) = (term205 _106555 _106572 k s).
Proof. exact (fun_ext (fun x : _106572 -> _106555 => @lem4437993 _106555 _106572 k s x)). Qed.
Lemma lem4437995 {_106555 _106572 : Type'} : (@ex (_106572 -> _106555)) = (@ex (_106572 -> _106555)).
Proof. exact (eq_refl (@ex (_106572 -> _106555))). Qed.
Lemma lem4437996 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term217 _106555 _106572 k s) = (term206 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437995 _106555 _106572) (@lem4437994 _106555 _106572 k s)). Qed.
Lemma lem4437997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4437998 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term218 _106555 _106572 k s) = (term207 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437997) (@lem4437996 _106555 _106572 k s)). Qed.
Lemma lem4437999 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term44 _106555 _106572 k s) = (term44 _106555 _106572 k s).
Proof. exact (eq_refl (term44 _106555 _106572 k s)). Qed.
Lemma lem4438000 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term213 _106555 _106572 k s) = (term208 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4437998 _106555 _106572 k s) (@lem4437999 _106555 _106572 k s)). Qed.
Lemma lem4438001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438002 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term219 _106555 _106572 k s) = (term220 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438001) (@lem4438000 _106555 _106572 k s)). Qed.
Lemma lem4438003 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) : (term215 _106555 _106572 k s x) = (term203 _106555 _106572 k s x).
Proof. exact (eq_refl (term215 _106555 _106572 k s x)). Qed.
Lemma lem4438004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4438005 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) : (term221 _106555 _106572 k s x) = (term222 _106555 _106572 k s x).
Proof. exact (MK_COMB (@lem4438004) (@lem4438003 _106555 _106572 k s x)). Qed.
Lemma lem4438006 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term44 _106555 _106572 k s) = (term44 _106555 _106572 k s).
Proof. exact (eq_refl (term44 _106555 _106572 k s)). Qed.
Lemma lem4438007 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term223 _106555 _106572 x k s) = (term224 _106555 _106572 x k s).
Proof. exact (MK_COMB (@lem4438005 _106555 _106572 k s x) (@lem4438006 _106555 _106572 k s)). Qed.
Lemma lem4438008 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term225 _106555 _106572 k s) = (term226 _106555 _106572 k s).
Proof. exact (fun_ext (fun x : _106572 -> _106555 => @lem4438007 _106555 _106572 x k s)). Qed.
Lemma lem4438009 {_106555 _106572 : Type'} : (@ex (_106572 -> _106555)) = (@ex (_106572 -> _106555)).
Proof. exact (eq_refl (@ex (_106572 -> _106555))). Qed.
Lemma lem4438010 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term214 _106555 _106572 k s) = (term227 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438009 _106555 _106572) (@lem4438008 _106555 _106572 k s)). Qed.
Lemma lem4438011 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term213 _106555 _106572 k s) = (term214 _106555 _106572 k s)) = ((term208 _106555 _106572 k s) = (term227 _106555 _106572 k s)).
Proof. exact (MK_COMB (@lem4438002 _106555 _106572 k s) (@lem4438010 _106555 _106572 k s)). Qed.
Lemma lem4438012 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term208 _106555 _106572 k s) = (term227 _106555 _106572 k s).
Proof. exact (EQ_MP (@lem4438011 _106555 _106572 k s) (@lem4437992 _106555 _106572 k s)). Qed.
Lemma lem4438014 {A : Type'} (P : Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4438015 {_106572 : Type'} (P : Prop) (Q : _106572 -> Prop) : (term228 _106572 P Q) = (term229 _106572 P Q).
Proof. exact (@lem4438014 _106572 P Q). Qed.
Lemma lem4438016 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term230 _106555 _106572 x k s) = (term231 _106555 _106572 x k s).
Proof. exact (@lem4438015 _106572 (term203 _106555 _106572 k s x) (term43 _106555 _106572 k s)). Qed.
Lemma lem4438017 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term91 _106555 _106572 k s i) = (term42 _106555 _106572 k s i).
Proof. exact (eq_refl (term91 _106555 _106572 k s i)). Qed.
Lemma lem4438018 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term232 _106555 _106572 k s) = (term43 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4438017 _106555 _106572 k s i)). Qed.
Lemma lem4438019 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4438020 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term233 _106555 _106572 k s) = (term44 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438019 _106572) (@lem4438018 _106555 _106572 k s)). Qed.
Lemma lem4438021 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) : (term222 _106555 _106572 k s x) = (term222 _106555 _106572 k s x).
Proof. exact (eq_refl (term222 _106555 _106572 k s x)). Qed.
Lemma lem4438022 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term230 _106555 _106572 x k s) = (term224 _106555 _106572 x k s).
Proof. exact (MK_COMB (@lem4438021 _106555 _106572 k s x) (@lem4438020 _106555 _106572 k s)). Qed.
Lemma lem4438023 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438024 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term234 _106555 _106572 x k s) = (term235 _106555 _106572 x k s).
Proof. exact (MK_COMB (@lem4438023) (@lem4438022 _106555 _106572 x k s)). Qed.
Lemma lem4438025 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term91 _106555 _106572 k s i) = (term42 _106555 _106572 k s i).
Proof. exact (eq_refl (term91 _106555 _106572 k s i)). Qed.
Lemma lem4438026 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) : (term222 _106555 _106572 k s x) = (term222 _106555 _106572 k s x).
Proof. exact (eq_refl (term222 _106555 _106572 k s x)). Qed.
Lemma lem4438027 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term236 _106555 _106572 x k s i) = (term237 _106555 _106572 x k s i).
Proof. exact (MK_COMB (@lem4438026 _106555 _106572 k s x) (@lem4438025 _106555 _106572 k s i)). Qed.
Lemma lem4438028 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term238 _106555 _106572 x k s) = (term239 _106555 _106572 x k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4438027 _106555 _106572 x k s i)). Qed.
Lemma lem4438029 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4438030 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term231 _106555 _106572 x k s) = (term240 _106555 _106572 x k s).
Proof. exact (MK_COMB (@lem4438029 _106572) (@lem4438028 _106555 _106572 x k s)). Qed.
Lemma lem4438031 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term230 _106555 _106572 x k s) = (term231 _106555 _106572 x k s)) = ((term224 _106555 _106572 x k s) = (term240 _106555 _106572 x k s)).
Proof. exact (MK_COMB (@lem4438024 _106555 _106572 x k s) (@lem4438030 _106555 _106572 x k s)). Qed.
Lemma lem4438032 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term224 _106555 _106572 x k s) = (term240 _106555 _106572 x k s).
Proof. exact (EQ_MP (@lem4438031 _106555 _106572 x k s) (@lem4438016 _106555 _106572 x k s)). Qed.
Lemma lem4438033 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term226 _106555 _106572 k s) = (term241 _106555 _106572 k s).
Proof. exact (fun_ext (fun x : _106572 -> _106555 => @lem4438032 _106555 _106572 x k s)). Qed.
Lemma lem4438034 {_106555 _106572 : Type'} : (@ex (_106572 -> _106555)) = (@ex (_106572 -> _106555)).
Proof. exact (eq_refl (@ex (_106572 -> _106555))). Qed.
Lemma lem4438035 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term227 _106555 _106572 k s) = (term242 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438034 _106555 _106572) (@lem4438033 _106555 _106572 k s)). Qed.
Lemma lem4438036 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term208 _106555 _106572 k s) = (term242 _106555 _106572 k s).
Proof. exact (TRANS (@lem4438012 _106555 _106572 k s) (@lem4438035 _106555 _106572 k s)). Qed.
Lemma lem4438037 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term150 _106555 _106572 k s) = (term242 _106555 _106572 k s).
Proof. exact (TRANS (@lem4437988 _106555 _106572 k s) (@lem4438036 _106555 _106572 k s)). Qed.
Lemma lem4438038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4438039 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term151 _106555 _106572 k s) = (term243 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438038) (@lem4438037 _106555 _106572 k s)). Qed.
Lemma lem4438041 {A : Type'} (P : Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4438042 {_106555 : Type'} (P : Prop) (Q : _106555 -> Prop) : (term176 _106555 P Q) = (term177 _106555 P Q).
Proof. exact (@lem4438041 _106555 P Q). Qed.
Lemma lem4438043 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term178 _106555 _106572 k s i) = (term179 _106555 _106572 k s i).
Proof. exact (@lem4438042 _106555 (term158 _106572 k i) (term82 _106555 _106572 s i)). Qed.
Lemma lem4438044 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term160 _106555 _106572 s i a) = (s i a).
Proof. exact (eq_refl (term160 _106555 _106572 s i a)). Qed.
Lemma lem4438045 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term170 _106555 _106572 s i) = (term82 _106555 _106572 s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4438044 _106555 _106572 s i a)). Qed.
Lemma lem4438046 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4438047 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term171 _106555 _106572 s i) = (term83 _106555 _106572 s i).
Proof. exact (MK_COMB (@lem4438046 _106555) (@lem4438045 _106555 _106572 s i)). Qed.
Lemma lem4438048 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term84 _106572 k i) = (term84 _106572 k i).
Proof. exact (eq_refl (term84 _106572 k i)). Qed.
Lemma lem4438049 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term178 _106555 _106572 k s i) = (term86 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4438048 _106572 k i) (@lem4438047 _106555 _106572 s i)). Qed.
Lemma lem4438050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438051 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term180 _106555 _106572 k s i) = (term181 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4438050) (@lem4438049 _106555 _106572 k s i)). Qed.
Lemma lem4438052 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term160 _106555 _106572 s i a) = (s i a).
Proof. exact (eq_refl (term160 _106555 _106572 s i a)). Qed.
Lemma lem4438053 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term84 _106572 k i) = (term84 _106572 k i).
Proof. exact (eq_refl (term84 _106572 k i)). Qed.
Lemma lem4438054 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term182 _106555 _106572 k s i a) = (term99 _106555 _106572 k s i a).
Proof. exact (MK_COMB (@lem4438053 _106572 k i) (@lem4438052 _106555 _106572 s i a)). Qed.
Lemma lem4438055 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term183 _106555 _106572 k s i) = (term107 _106555 _106572 k s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4438054 _106555 _106572 k s i a)). Qed.
Lemma lem4438056 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4438057 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term179 _106555 _106572 k s i) = (term108 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4438056 _106555) (@lem4438055 _106555 _106572 k s i)). Qed.
Lemma lem4438058 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : ((term178 _106555 _106572 k s i) = (term179 _106555 _106572 k s i)) = ((term86 _106555 _106572 k s i) = (term108 _106555 _106572 k s i)).
Proof. exact (MK_COMB (@lem4438051 _106555 _106572 k s i) (@lem4438057 _106555 _106572 k s i)). Qed.
Lemma lem4438059 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term86 _106555 _106572 k s i) = (term108 _106555 _106572 k s i).
Proof. exact (EQ_MP (@lem4438058 _106555 _106572 k s i) (@lem4438043 _106555 _106572 k s i)). Qed.
Lemma lem4438060 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term94 _106555 _106572 k s) = (term116 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4438059 _106555 _106572 k s i)). Qed.
Lemma lem4438061 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4438062 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term95 _106555 _106572 k s) = (term117 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438061 _106572) (@lem4438060 _106555 _106572 k s)). Qed.
Lemma lem4438064 {A B : Type'} (P : type1413 A B) : (term18 A B P) = (term19 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4438065 {_106555 _106572 : Type'} (P : type1470 _106555 _106572) : (term184 _106555 _106572 P) = (term185 _106555 _106572 P).
Proof. exact (@lem4438064 _106572 _106555 P). Qed.
Lemma lem4438066 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term186 _106555 _106572 k s) = (term187 _106555 _106572 k s).
Proof. exact (@lem4438065 _106555 _106572 (term188 _106555 _106572 k s)). Qed.
Lemma lem4438067 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term189 _106555 _106572 k s i) = (term107 _106555 _106572 k s i).
Proof. exact (eq_refl (term189 _106555 _106572 k s i)). Qed.
Lemma lem4438068 {_106555 : Type'} (a : _106555) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4438069 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term190 _106555 _106572 k s i a) = (term191 _106555 _106572 k s i a).
Proof. exact (MK_COMB (@lem4438067 _106555 _106572 k s i) (@lem4438068 _106555 a)). Qed.
Lemma lem4438070 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term191 _106555 _106572 k s i a) = (term99 _106555 _106572 k s i a).
Proof. exact (eq_refl (term191 _106555 _106572 k s i a)). Qed.
Lemma lem4438071 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term190 _106555 _106572 k s i a) = (term99 _106555 _106572 k s i a).
Proof. exact (TRANS (@lem4438069 _106555 _106572 k s i a) (@lem4438070 _106555 _106572 k s i a)). Qed.
Lemma lem4438072 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term192 _106555 _106572 k s i) = (term107 _106555 _106572 k s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4438071 _106555 _106572 k s i a)). Qed.
Lemma lem4438073 {_106555 : Type'} : (@ex _106555) = (@ex _106555).
Proof. exact (eq_refl (@ex _106555)). Qed.
Lemma lem4438074 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term193 _106555 _106572 k s i) = (term108 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4438073 _106555) (@lem4438072 _106555 _106572 k s i)). Qed.
Lemma lem4438075 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term194 _106555 _106572 k s) = (term116 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4438074 _106555 _106572 k s i)). Qed.
Lemma lem4438076 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4438077 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term186 _106555 _106572 k s) = (term117 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438076 _106572) (@lem4438075 _106555 _106572 k s)). Qed.
Lemma lem4438078 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438079 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term195 _106555 _106572 k s) = (term196 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438078) (@lem4438077 _106555 _106572 k s)). Qed.
Lemma lem4438080 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term189 _106555 _106572 k s i) = (term107 _106555 _106572 k s i).
Proof. exact (eq_refl (term189 _106555 _106572 k s i)). Qed.
Lemma lem4438081 {_106555 _106572 : Type'} (a : _106572 -> _106555) (i : _106572) : (a i) = (a i).
Proof. exact (eq_refl (a i)). Qed.
Lemma lem4438082 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (i : _106572) : (term197 _106555 _106572 k s a i) = (term198 _106555 _106572 k s a i).
Proof. exact (MK_COMB (@lem4438080 _106555 _106572 k s i) (@lem4438081 _106555 _106572 a i)). Qed.
Lemma lem4438083 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (i : _106572) : (term198 _106555 _106572 k s a i) = (term199 _106555 _106572 k s a i).
Proof. exact (eq_refl (term198 _106555 _106572 k s a i)). Qed.
Lemma lem4438084 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (i : _106572) : (term197 _106555 _106572 k s a i) = (term199 _106555 _106572 k s a i).
Proof. exact (TRANS (@lem4438082 _106555 _106572 k s a i) (@lem4438083 _106555 _106572 k s a i)). Qed.
Lemma lem4438085 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term200 _106555 _106572 k s a) = (term201 _106555 _106572 k s a).
Proof. exact (fun_ext (fun i : _106572 => @lem4438084 _106555 _106572 k s a i)). Qed.
Lemma lem4438086 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4438087 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term202 _106555 _106572 k s a) = (term203 _106555 _106572 k s a).
Proof. exact (MK_COMB (@lem4438086 _106572) (@lem4438085 _106555 _106572 k s a)). Qed.
Lemma lem4438088 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term204 _106555 _106572 k s) = (term205 _106555 _106572 k s).
Proof. exact (fun_ext (fun a : _106572 -> _106555 => @lem4438087 _106555 _106572 k s a)). Qed.
Lemma lem4438089 {_106555 _106572 : Type'} : (@ex (_106572 -> _106555)) = (@ex (_106572 -> _106555)).
Proof. exact (eq_refl (@ex (_106572 -> _106555))). Qed.
Lemma lem4438090 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term187 _106555 _106572 k s) = (term206 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438089 _106555 _106572) (@lem4438088 _106555 _106572 k s)). Qed.
Lemma lem4438091 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term186 _106555 _106572 k s) = (term187 _106555 _106572 k s)) = ((term117 _106555 _106572 k s) = (term206 _106555 _106572 k s)).
Proof. exact (MK_COMB (@lem4438079 _106555 _106572 k s) (@lem4438090 _106555 _106572 k s)). Qed.
Lemma lem4438092 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term117 _106555 _106572 k s) = (term206 _106555 _106572 k s).
Proof. exact (EQ_MP (@lem4438091 _106555 _106572 k s) (@lem4438066 _106555 _106572 k s)). Qed.
Lemma lem4438093 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term95 _106555 _106572 k s) = (term206 _106555 _106572 k s).
Proof. exact (TRANS (@lem4438062 _106555 _106572 k s) (@lem4438092 _106555 _106572 k s)). Qed.
Lemma lem4438094 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term119 _106555 _106572 k s) = (term119 _106555 _106572 k s).
Proof. exact (eq_refl (term119 _106555 _106572 k s)). Qed.
Lemma lem4438095 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term174 _106555 _106572 k s) = (term244 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438094 _106555 _106572 k s) (@lem4438093 _106555 _106572 k s)). Qed.
Lemma lem4438097 {A : Type'} (P : A -> Prop) (Q : Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4438098 {_106572 : Type'} (P : _106572 -> Prop) (Q : Prop) : (term209 _106572 P Q) = (term210 _106572 P Q).
Proof. exact (@lem4438097 _106572 P Q). Qed.
Lemma lem4438099 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term245 _106555 _106572 k s) = (term246 _106555 _106572 k s).
Proof. exact (@lem4438098 _106572 (term43 _106555 _106572 k s) (term206 _106555 _106572 k s)). Qed.
Lemma lem4438100 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term91 _106555 _106572 k s i) = (term42 _106555 _106572 k s i).
Proof. exact (eq_refl (term91 _106555 _106572 k s i)). Qed.
Lemma lem4438101 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term232 _106555 _106572 k s) = (term43 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4438100 _106555 _106572 k s i)). Qed.
Lemma lem4438102 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4438103 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term233 _106555 _106572 k s) = (term44 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438102 _106572) (@lem4438101 _106555 _106572 k s)). Qed.
Lemma lem4438104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4438105 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term247 _106555 _106572 k s) = (term119 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438104) (@lem4438103 _106555 _106572 k s)). Qed.
Lemma lem4438106 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term206 _106555 _106572 k s) = (term206 _106555 _106572 k s).
Proof. exact (eq_refl (term206 _106555 _106572 k s)). Qed.
Lemma lem4438107 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term245 _106555 _106572 k s) = (term244 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438105 _106555 _106572 k s) (@lem4438106 _106555 _106572 k s)). Qed.
Lemma lem4438108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438109 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term248 _106555 _106572 k s) = (term249 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438108) (@lem4438107 _106555 _106572 k s)). Qed.
Lemma lem4438110 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term91 _106555 _106572 k s i) = (term42 _106555 _106572 k s i).
Proof. exact (eq_refl (term91 _106555 _106572 k s i)). Qed.
Lemma lem4438111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4438112 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term250 _106555 _106572 k s i) = (term251 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4438111) (@lem4438110 _106555 _106572 k s i)). Qed.
Lemma lem4438113 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term206 _106555 _106572 k s) = (term206 _106555 _106572 k s).
Proof. exact (eq_refl (term206 _106555 _106572 k s)). Qed.
Lemma lem4438114 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term252 _106555 _106572 i k s) = (term253 _106555 _106572 i k s).
Proof. exact (MK_COMB (@lem4438112 _106555 _106572 k s i) (@lem4438113 _106555 _106572 k s)). Qed.
Lemma lem4438115 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term254 _106555 _106572 k s) = (term255 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4438114 _106555 _106572 i k s)). Qed.
Lemma lem4438116 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4438117 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term246 _106555 _106572 k s) = (term256 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438116 _106572) (@lem4438115 _106555 _106572 k s)). Qed.
Lemma lem4438118 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term245 _106555 _106572 k s) = (term246 _106555 _106572 k s)) = ((term244 _106555 _106572 k s) = (term256 _106555 _106572 k s)).
Proof. exact (MK_COMB (@lem4438109 _106555 _106572 k s) (@lem4438117 _106555 _106572 k s)). Qed.
Lemma lem4438119 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term244 _106555 _106572 k s) = (term256 _106555 _106572 k s).
Proof. exact (EQ_MP (@lem4438118 _106555 _106572 k s) (@lem4438099 _106555 _106572 k s)). Qed.
Lemma lem4438121 {A : Type'} (P : Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4438122 {_106555 _106572 : Type'} (P : Prop) (Q : type805 _106555 _106572) : (term257 _106555 _106572 P Q) = (term258 _106555 _106572 P Q).
Proof. exact (@lem4438121 (_106572 -> _106555) P Q). Qed.
Lemma lem4438123 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term259 _106555 _106572 i k s) = (term260 _106555 _106572 i k s).
Proof. exact (@lem4438122 _106555 _106572 (term42 _106555 _106572 k s i) (term205 _106555 _106572 k s)). Qed.
Lemma lem4438124 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term215 _106555 _106572 k s a) = (term203 _106555 _106572 k s a).
Proof. exact (eq_refl (term215 _106555 _106572 k s a)). Qed.
Lemma lem4438125 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term216 _106555 _106572 k s) = (term205 _106555 _106572 k s).
Proof. exact (fun_ext (fun a : _106572 -> _106555 => @lem4438124 _106555 _106572 k s a)). Qed.
Lemma lem4438126 {_106555 _106572 : Type'} : (@ex (_106572 -> _106555)) = (@ex (_106572 -> _106555)).
Proof. exact (eq_refl (@ex (_106572 -> _106555))). Qed.
Lemma lem4438127 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term217 _106555 _106572 k s) = (term206 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438126 _106555 _106572) (@lem4438125 _106555 _106572 k s)). Qed.
Lemma lem4438128 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term251 _106555 _106572 k s i) = (term251 _106555 _106572 k s i).
Proof. exact (eq_refl (term251 _106555 _106572 k s i)). Qed.
Lemma lem4438129 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term259 _106555 _106572 i k s) = (term253 _106555 _106572 i k s).
Proof. exact (MK_COMB (@lem4438128 _106555 _106572 k s i) (@lem4438127 _106555 _106572 k s)). Qed.
Lemma lem4438130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438131 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term261 _106555 _106572 i k s) = (term262 _106555 _106572 i k s).
Proof. exact (MK_COMB (@lem4438130) (@lem4438129 _106555 _106572 i k s)). Qed.
Lemma lem4438132 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term215 _106555 _106572 k s a) = (term203 _106555 _106572 k s a).
Proof. exact (eq_refl (term215 _106555 _106572 k s a)). Qed.
Lemma lem4438133 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term251 _106555 _106572 k s i) = (term251 _106555 _106572 k s i).
Proof. exact (eq_refl (term251 _106555 _106572 k s i)). Qed.
Lemma lem4438134 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term263 _106555 _106572 i k s a) = (term264 _106555 _106572 i k s a).
Proof. exact (MK_COMB (@lem4438133 _106555 _106572 k s i) (@lem4438132 _106555 _106572 k s a)). Qed.
Lemma lem4438135 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term265 _106555 _106572 i k s) = (term266 _106555 _106572 i k s).
Proof. exact (fun_ext (fun a : _106572 -> _106555 => @lem4438134 _106555 _106572 i k s a)). Qed.
Lemma lem4438136 {_106555 _106572 : Type'} : (@ex (_106572 -> _106555)) = (@ex (_106572 -> _106555)).
Proof. exact (eq_refl (@ex (_106572 -> _106555))). Qed.
Lemma lem4438137 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term260 _106555 _106572 i k s) = (term267 _106555 _106572 i k s).
Proof. exact (MK_COMB (@lem4438136 _106555 _106572) (@lem4438135 _106555 _106572 i k s)). Qed.
Lemma lem4438138 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term259 _106555 _106572 i k s) = (term260 _106555 _106572 i k s)) = ((term253 _106555 _106572 i k s) = (term267 _106555 _106572 i k s)).
Proof. exact (MK_COMB (@lem4438131 _106555 _106572 i k s) (@lem4438137 _106555 _106572 i k s)). Qed.
Lemma lem4438139 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term253 _106555 _106572 i k s) = (term267 _106555 _106572 i k s).
Proof. exact (EQ_MP (@lem4438138 _106555 _106572 i k s) (@lem4438123 _106555 _106572 i k s)). Qed.
Lemma lem4438140 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term255 _106555 _106572 k s) = (term268 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4438139 _106555 _106572 i k s)). Qed.
Lemma lem4438141 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4438142 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term256 _106555 _106572 k s) = (term269 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438141 _106572) (@lem4438140 _106555 _106572 k s)). Qed.
Lemma lem4438143 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term244 _106555 _106572 k s) = (term269 _106555 _106572 k s).
Proof. exact (TRANS (@lem4438119 _106555 _106572 k s) (@lem4438142 _106555 _106572 k s)). Qed.
Lemma lem4438144 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term174 _106555 _106572 k s) = (term269 _106555 _106572 k s).
Proof. exact (TRANS (@lem4438095 _106555 _106572 k s) (@lem4438143 _106555 _106572 k s)). Qed.
Lemma lem4438145 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term175 _106555 _106572 k s) = (term270 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438039 _106555 _106572 k s) (@lem4438144 _106555 _106572 k s)). Qed.
Lemma lem4438149 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4438150 {_106555 _106572 : Type'} (P : type805 _106555 _106572) (Q : Prop) : (term273 _106555 _106572 P Q) = (term274 _106555 _106572 P Q).
Proof. exact (@lem4438149 (_106572 -> _106555) P Q). Qed.
Lemma lem4438151 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term275 _106555 _106572 k s) = (term276 _106555 _106572 k s).
Proof. exact (@lem4438150 _106555 _106572 (term241 _106555 _106572 k s) (term269 _106555 _106572 k s)). Qed.
Lemma lem4438152 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term277 _106555 _106572 k s x) = (term240 _106555 _106572 x k s).
Proof. exact (eq_refl (term277 _106555 _106572 k s x)). Qed.
Lemma lem4438153 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term278 _106555 _106572 k s) = (term241 _106555 _106572 k s).
Proof. exact (fun_ext (fun x : _106572 -> _106555 => @lem4438152 _106555 _106572 x k s)). Qed.
Lemma lem4438154 {_106555 _106572 : Type'} : (@ex (_106572 -> _106555)) = (@ex (_106572 -> _106555)).
Proof. exact (eq_refl (@ex (_106572 -> _106555))). Qed.
Lemma lem4438155 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term279 _106555 _106572 k s) = (term242 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438154 _106555 _106572) (@lem4438153 _106555 _106572 k s)). Qed.
Lemma lem4438156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4438157 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term280 _106555 _106572 k s) = (term243 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438156) (@lem4438155 _106555 _106572 k s)). Qed.
Lemma lem4438158 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term269 _106555 _106572 k s) = (term269 _106555 _106572 k s).
Proof. exact (eq_refl (term269 _106555 _106572 k s)). Qed.
Lemma lem4438159 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term275 _106555 _106572 k s) = (term270 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438157 _106555 _106572 k s) (@lem4438158 _106555 _106572 k s)). Qed.
Lemma lem4438160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438161 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term281 _106555 _106572 k s) = (term282 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438160) (@lem4438159 _106555 _106572 k s)). Qed.
Lemma lem4438162 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term277 _106555 _106572 k s x) = (term240 _106555 _106572 x k s).
Proof. exact (eq_refl (term277 _106555 _106572 k s x)). Qed.
Lemma lem4438163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4438164 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term283 _106555 _106572 k s x) = (term284 _106555 _106572 x k s).
Proof. exact (MK_COMB (@lem4438163) (@lem4438162 _106555 _106572 x k s)). Qed.
Lemma lem4438165 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term269 _106555 _106572 k s) = (term269 _106555 _106572 k s).
Proof. exact (eq_refl (term269 _106555 _106572 k s)). Qed.
Lemma lem4438166 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term285 _106555 _106572 x k s) = (term286 _106555 _106572 x k s).
Proof. exact (MK_COMB (@lem4438164 _106555 _106572 x k s) (@lem4438165 _106555 _106572 k s)). Qed.
Lemma lem4438167 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term287 _106555 _106572 k s) = (term288 _106555 _106572 k s).
Proof. exact (fun_ext (fun x : _106572 -> _106555 => @lem4438166 _106555 _106572 x k s)). Qed.
Lemma lem4438168 {_106555 _106572 : Type'} : (@ex (_106572 -> _106555)) = (@ex (_106572 -> _106555)).
Proof. exact (eq_refl (@ex (_106572 -> _106555))). Qed.
Lemma lem4438169 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term276 _106555 _106572 k s) = (term289 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438168 _106555 _106572) (@lem4438167 _106555 _106572 k s)). Qed.
Lemma lem4438170 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term275 _106555 _106572 k s) = (term276 _106555 _106572 k s)) = ((term270 _106555 _106572 k s) = (term289 _106555 _106572 k s)).
Proof. exact (MK_COMB (@lem4438161 _106555 _106572 k s) (@lem4438169 _106555 _106572 k s)). Qed.
Lemma lem4438171 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term270 _106555 _106572 k s) = (term289 _106555 _106572 k s).
Proof. exact (EQ_MP (@lem4438170 _106555 _106572 k s) (@lem4438151 _106555 _106572 k s)). Qed.
Lemma lem4438173 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term153 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4438174 {_106572 : Type'} (P : _106572 -> Prop) (Q : _106572 -> Prop) : (term153 _106572 P Q) = (term152 _106572 P Q).
Proof. exact (@lem4438173 _106572 P Q). Qed.
Lemma lem4438175 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term290 _106555 _106572 x k s) = (term291 _106555 _106572 x k s).
Proof. exact (@lem4438174 _106572 (term239 _106555 _106572 x k s) (term268 _106555 _106572 k s)). Qed.
Lemma lem4438176 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term292 _106555 _106572 x k s i) = (term237 _106555 _106572 x k s i).
Proof. exact (eq_refl (term292 _106555 _106572 x k s i)). Qed.
Lemma lem4438177 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term293 _106555 _106572 x k s) = (term239 _106555 _106572 x k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4438176 _106555 _106572 x k s i)). Qed.
Lemma lem4438178 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4438179 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term294 _106555 _106572 x k s) = (term240 _106555 _106572 x k s).
Proof. exact (MK_COMB (@lem4438178 _106572) (@lem4438177 _106555 _106572 x k s)). Qed.
Lemma lem4438180 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4438181 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term295 _106555 _106572 x k s) = (term284 _106555 _106572 x k s).
Proof. exact (MK_COMB (@lem4438180) (@lem4438179 _106555 _106572 x k s)). Qed.
Lemma lem4438182 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term296 _106555 _106572 k s i) = (term267 _106555 _106572 i k s).
Proof. exact (eq_refl (term296 _106555 _106572 k s i)). Qed.
Lemma lem4438183 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term297 _106555 _106572 k s) = (term268 _106555 _106572 k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4438182 _106555 _106572 i k s)). Qed.
Lemma lem4438184 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4438185 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term298 _106555 _106572 k s) = (term269 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438184 _106572) (@lem4438183 _106555 _106572 k s)). Qed.
Lemma lem4438186 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term290 _106555 _106572 x k s) = (term286 _106555 _106572 x k s).
Proof. exact (MK_COMB (@lem4438181 _106555 _106572 x k s) (@lem4438185 _106555 _106572 k s)). Qed.
Lemma lem4438187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438188 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term299 _106555 _106572 x k s) = (term300 _106555 _106572 x k s).
Proof. exact (MK_COMB (@lem4438187) (@lem4438186 _106555 _106572 x k s)). Qed.
Lemma lem4438189 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term292 _106555 _106572 x k s i) = (term237 _106555 _106572 x k s i).
Proof. exact (eq_refl (term292 _106555 _106572 x k s i)). Qed.
Lemma lem4438190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4438191 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term301 _106555 _106572 x k s i) = (term302 _106555 _106572 x k s i).
Proof. exact (MK_COMB (@lem4438190) (@lem4438189 _106555 _106572 x k s i)). Qed.
Lemma lem4438192 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term296 _106555 _106572 k s i) = (term267 _106555 _106572 i k s).
Proof. exact (eq_refl (term296 _106555 _106572 k s i)). Qed.
Lemma lem4438193 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term303 _106555 _106572 x k s i) = (term304 _106555 _106572 x i k s).
Proof. exact (MK_COMB (@lem4438191 _106555 _106572 x k s i) (@lem4438192 _106555 _106572 i k s)). Qed.
Lemma lem4438194 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term305 _106555 _106572 x k s) = (term306 _106555 _106572 x k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4438193 _106555 _106572 x i k s)). Qed.
Lemma lem4438195 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4438196 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term291 _106555 _106572 x k s) = (term307 _106555 _106572 x k s).
Proof. exact (MK_COMB (@lem4438195 _106572) (@lem4438194 _106555 _106572 x k s)). Qed.
Lemma lem4438197 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term290 _106555 _106572 x k s) = (term291 _106555 _106572 x k s)) = ((term286 _106555 _106572 x k s) = (term307 _106555 _106572 x k s)).
Proof. exact (MK_COMB (@lem4438188 _106555 _106572 x k s) (@lem4438196 _106555 _106572 x k s)). Qed.
Lemma lem4438198 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term286 _106555 _106572 x k s) = (term307 _106555 _106572 x k s).
Proof. exact (EQ_MP (@lem4438197 _106555 _106572 x k s) (@lem4438175 _106555 _106572 x k s)). Qed.
Lemma lem4438200 {A : Type'} (P : Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4438201 {_106555 _106572 : Type'} (P : Prop) (Q : type805 _106555 _106572) : (term308 _106555 _106572 P Q) = (term309 _106555 _106572 P Q).
Proof. exact (@lem4438200 (_106572 -> _106555) P Q). Qed.
Lemma lem4438202 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term310 _106555 _106572 x i k s) = (term311 _106555 _106572 x i k s).
Proof. exact (@lem4438201 _106555 _106572 (term237 _106555 _106572 x k s i) (term266 _106555 _106572 i k s)). Qed.
Lemma lem4438203 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term312 _106555 _106572 i k s a) = (term264 _106555 _106572 i k s a).
Proof. exact (eq_refl (term312 _106555 _106572 i k s a)). Qed.
Lemma lem4438204 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term313 _106555 _106572 i k s) = (term266 _106555 _106572 i k s).
Proof. exact (fun_ext (fun a : _106572 -> _106555 => @lem4438203 _106555 _106572 i k s a)). Qed.
Lemma lem4438205 {_106555 _106572 : Type'} : (@ex (_106572 -> _106555)) = (@ex (_106572 -> _106555)).
Proof. exact (eq_refl (@ex (_106572 -> _106555))). Qed.
Lemma lem4438206 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term314 _106555 _106572 i k s) = (term267 _106555 _106572 i k s).
Proof. exact (MK_COMB (@lem4438205 _106555 _106572) (@lem4438204 _106555 _106572 i k s)). Qed.
Lemma lem4438207 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term302 _106555 _106572 x k s i) = (term302 _106555 _106572 x k s i).
Proof. exact (eq_refl (term302 _106555 _106572 x k s i)). Qed.
Lemma lem4438208 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term310 _106555 _106572 x i k s) = (term304 _106555 _106572 x i k s).
Proof. exact (MK_COMB (@lem4438207 _106555 _106572 x k s i) (@lem4438206 _106555 _106572 i k s)). Qed.
Lemma lem4438209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438210 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term315 _106555 _106572 x i k s) = (term316 _106555 _106572 x i k s).
Proof. exact (MK_COMB (@lem4438209) (@lem4438208 _106555 _106572 x i k s)). Qed.
Lemma lem4438211 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term312 _106555 _106572 i k s a) = (term264 _106555 _106572 i k s a).
Proof. exact (eq_refl (term312 _106555 _106572 i k s a)). Qed.
Lemma lem4438212 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term302 _106555 _106572 x k s i) = (term302 _106555 _106572 x k s i).
Proof. exact (eq_refl (term302 _106555 _106572 x k s i)). Qed.
Lemma lem4438213 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term317 _106555 _106572 x i k s a) = (term318 _106555 _106572 x i k s a).
Proof. exact (MK_COMB (@lem4438212 _106555 _106572 x k s i) (@lem4438211 _106555 _106572 i k s a)). Qed.
Lemma lem4438214 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term319 _106555 _106572 x i k s) = (term320 _106555 _106572 x i k s).
Proof. exact (fun_ext (fun a : _106572 -> _106555 => @lem4438213 _106555 _106572 x i k s a)). Qed.
Lemma lem4438215 {_106555 _106572 : Type'} : (@ex (_106572 -> _106555)) = (@ex (_106572 -> _106555)).
Proof. exact (eq_refl (@ex (_106572 -> _106555))). Qed.
Lemma lem4438216 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term311 _106555 _106572 x i k s) = (term321 _106555 _106572 x i k s).
Proof. exact (MK_COMB (@lem4438215 _106555 _106572) (@lem4438214 _106555 _106572 x i k s)). Qed.
Lemma lem4438217 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : ((term310 _106555 _106572 x i k s) = (term311 _106555 _106572 x i k s)) = ((term304 _106555 _106572 x i k s) = (term321 _106555 _106572 x i k s)).
Proof. exact (MK_COMB (@lem4438210 _106555 _106572 x i k s) (@lem4438216 _106555 _106572 x i k s)). Qed.
Lemma lem4438218 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term304 _106555 _106572 x i k s) = (term321 _106555 _106572 x i k s).
Proof. exact (EQ_MP (@lem4438217 _106555 _106572 x i k s) (@lem4438202 _106555 _106572 x i k s)). Qed.
Lemma lem4438219 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term306 _106555 _106572 x k s) = (term322 _106555 _106572 x k s).
Proof. exact (fun_ext (fun i : _106572 => @lem4438218 _106555 _106572 x i k s)). Qed.
Lemma lem4438220 {_106572 : Type'} : (@ex _106572) = (@ex _106572).
Proof. exact (eq_refl (@ex _106572)). Qed.
Lemma lem4438221 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term307 _106555 _106572 x k s) = (term323 _106555 _106572 x k s).
Proof. exact (MK_COMB (@lem4438220 _106572) (@lem4438219 _106555 _106572 x k s)). Qed.
Lemma lem4438222 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term286 _106555 _106572 x k s) = (term323 _106555 _106572 x k s).
Proof. exact (TRANS (@lem4438198 _106555 _106572 x k s) (@lem4438221 _106555 _106572 x k s)). Qed.
Lemma lem4438223 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term288 _106555 _106572 k s) = (term324 _106555 _106572 k s).
Proof. exact (fun_ext (fun x : _106572 -> _106555 => @lem4438222 _106555 _106572 x k s)). Qed.
Lemma lem4438224 {_106555 _106572 : Type'} : (@ex (_106572 -> _106555)) = (@ex (_106572 -> _106555)).
Proof. exact (eq_refl (@ex (_106572 -> _106555))). Qed.
Lemma lem4438225 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term289 _106555 _106572 k s) = (term325 _106555 _106572 k s).
Proof. exact (MK_COMB (@lem4438224 _106555 _106572) (@lem4438223 _106555 _106572 k s)). Qed.
Lemma lem4438226 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term270 _106555 _106572 k s) = (term325 _106555 _106572 k s).
Proof. exact (TRANS (@lem4438171 _106555 _106572 k s) (@lem4438225 _106555 _106572 k s)). Qed.
Lemma lem4438227 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term175 _106555 _106572 k s) = (term325 _106555 _106572 k s).
Proof. exact (TRANS (@lem4438145 _106555 _106572 k s) (@lem4438226 _106555 _106572 k s)). Qed.
Lemma lem4438228 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term129 _106555 _106572 k s) = (term325 _106555 _106572 k s).
Proof. exact (TRANS (@lem4437930 _106555 _106572 k s) (@lem4438227 _106555 _106572 k s)). Qed.
Lemma lem4438229 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term60 _106555 _106572 k s) = (term325 _106555 _106572 k s).
Proof. exact (TRANS (@lem4437669 _106555 _106572 k s) (@lem4438228 _106555 _106572 k s)). Qed.
Lemma lem4438230 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term60 _106555 _106572 k s) : term325 _106555 _106572 k s.
Proof. exact (EQ_MP (@lem4438229 _106555 _106572 k s) (@lem4437576 _106555 _106572 k s h1)). Qed.
Lemma lem4438231 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term323 _106555 _106572 x k s) : term323 _106555 _106572 x k s.
Proof. exact (h1). Qed.
Lemma lem4438232 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term321 _106555 _106572 x i k s) : term321 _106555 _106572 x i k s.
Proof. exact (h1). Qed.
Lemma lem4438233 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term318 _106555 _106572 x i k s a) : term318 _106555 _106572 x i k s a.
Proof. exact (h1). Qed.
Lemma lem4438248 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (i : _106572) : (term199 _106555 _106572 k s a i) = (term199 _106555 _106572 k s a i).
Proof. exact (eq_refl (term199 _106555 _106572 k s a i)). Qed.
Lemma lem4438249 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term201 _106555 _106572 k s a) = (term201 _106555 _106572 k s a).
Proof. exact (fun_ext (fun i : _106572 => @lem4438248 _106555 _106572 k s a i)). Qed.
Lemma lem4438250 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4438251 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term203 _106555 _106572 k s a) = (term203 _106555 _106572 k s a).
Proof. exact (MK_COMB (@lem4438250 _106572) (@lem4438249 _106555 _106572 k s a)). Qed.
Lemma lem4438258 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term38 _106555 _106572 s i x) = (term38 _106555 _106572 s i x).
Proof. exact (eq_refl (term38 _106555 _106572 s i x)). Qed.
Lemma lem4438259 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term40 _106555 _106572 s i) = (term40 _106555 _106572 s i).
Proof. exact (fun_ext (fun x : _106555 => @lem4438258 _106555 _106572 s i x)). Qed.
Lemma lem4438260 {_106555 : Type'} : (@all _106555) = (@all _106555).
Proof. exact (eq_refl (@all _106555)). Qed.
Lemma lem4438261 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term41 _106555 _106572 s i) = (term41 _106555 _106572 s i).
Proof. exact (MK_COMB (@lem4438260 _106555) (@lem4438259 _106555 _106572 s i)). Qed.
Lemma lem4438266 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term34 _106572 k i) = (term34 _106572 k i).
Proof. exact (eq_refl (term34 _106572 k i)). Qed.
Lemma lem4438267 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term42 _106555 _106572 k s i) = (term42 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4438266 _106572 k i) (@lem4438261 _106555 _106572 s i)). Qed.
Lemma lem4438268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4438269 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term251 _106555 _106572 k s i) = (term251 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4438268) (@lem4438267 _106555 _106572 k s i)). Qed.
Lemma lem4438270 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term264 _106555 _106572 i k s a) = (term264 _106555 _106572 i k s a).
Proof. exact (MK_COMB (@lem4438269 _106555 _106572 k s i) (@lem4438251 _106555 _106572 k s a)). Qed.
Lemma lem4438277 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term38 _106555 _106572 s i a) = (term38 _106555 _106572 s i a).
Proof. exact (eq_refl (term38 _106555 _106572 s i a)). Qed.
Lemma lem4438278 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term40 _106555 _106572 s i) = (term40 _106555 _106572 s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4438277 _106555 _106572 s i a)). Qed.
Lemma lem4438279 {_106555 : Type'} : (@all _106555) = (@all _106555).
Proof. exact (eq_refl (@all _106555)). Qed.
Lemma lem4438280 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term41 _106555 _106572 s i) = (term41 _106555 _106572 s i).
Proof. exact (MK_COMB (@lem4438279 _106555) (@lem4438278 _106555 _106572 s i)). Qed.
Lemma lem4438285 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term34 _106572 k i) = (term34 _106572 k i).
Proof. exact (eq_refl (term34 _106572 k i)). Qed.
Lemma lem4438286 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term42 _106555 _106572 k s i) = (term42 _106555 _106572 k s i).
Proof. exact (MK_COMB (@lem4438285 _106572 k i) (@lem4438280 _106555 _106572 s i)). Qed.
Lemma lem4438301 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) (i : _106572) : (term199 _106555 _106572 k s x i) = (term199 _106555 _106572 k s x i).
Proof. exact (eq_refl (term199 _106555 _106572 k s x i)). Qed.
Lemma lem4438302 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) : (term201 _106555 _106572 k s x) = (term201 _106555 _106572 k s x).
Proof. exact (fun_ext (fun i : _106572 => @lem4438301 _106555 _106572 k s x i)). Qed.
Lemma lem4438303 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4438304 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) : (term203 _106555 _106572 k s x) = (term203 _106555 _106572 k s x).
Proof. exact (MK_COMB (@lem4438303 _106572) (@lem4438302 _106555 _106572 k s x)). Qed.
Lemma lem4438305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4438306 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) : (term222 _106555 _106572 k s x) = (term222 _106555 _106572 k s x).
Proof. exact (MK_COMB (@lem4438305) (@lem4438304 _106555 _106572 k s x)). Qed.
Lemma lem4438307 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term237 _106555 _106572 x k s i) = (term237 _106555 _106572 x k s i).
Proof. exact (MK_COMB (@lem4438306 _106555 _106572 k s x) (@lem4438286 _106555 _106572 k s i)). Qed.
Lemma lem4438308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4438309 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) : (term302 _106555 _106572 x k s i) = (term302 _106555 _106572 x k s i).
Proof. exact (MK_COMB (@lem4438308) (@lem4438307 _106555 _106572 x k s i)). Qed.
Lemma lem4438310 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term318 _106555 _106572 x i k s a) = (term318 _106555 _106572 x i k s a).
Proof. exact (MK_COMB (@lem4438309 _106555 _106572 x k s i) (@lem4438270 _106555 _106572 i k s a)). Qed.
Lemma lem4438311 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term318 _106555 _106572 x i k s a) : term318 _106555 _106572 x i k s a.
Proof. exact (EQ_MP (@lem4438310 _106555 _106572 x i k s a) (@lem4438233 _106555 _106572 x i k s a h1)). Qed.
Lemma lem4438312 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term237 _106555 _106572 x k s i.
Proof. exact (h1). Qed.
Lemma lem4438313 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term264 _106555 _106572 i k s a.
Proof. exact (h1). Qed.
Lemma lem4438314 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term42 _106555 _106572 k s i.
Proof. exact (proj2 (@lem4438312 _106555 _106572 x k s i h1)). Qed.
Lemma lem4438315 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term203 _106555 _106572 k s x.
Proof. exact (proj1 (@lem4438312 _106555 _106572 x k s i h1)). Qed.
Lemma lem4438316 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term41 _106555 _106572 s i.
Proof. exact (proj2 (@lem4438314 _106555 _106572 x k s i h1)). Qed.
Lemma lem4438318 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term203 _106555 _106572 k s a.
Proof. exact (proj2 (@lem4438313 _106555 _106572 i k s a h1)). Qed.
Lemma lem4438319 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term42 _106555 _106572 k s i.
Proof. exact (proj1 (@lem4438313 _106555 _106572 i k s a h1)). Qed.
Lemma lem4438320 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term41 _106555 _106572 s i.
Proof. exact (proj2 (@lem4438319 _106555 _106572 i k s a h1)). Qed.
Lemma lem4438329 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) (i : _106572) : (term199 _106555 _106572 k s x i) = (term199 _106555 _106572 k s x i).
Proof. exact (eq_refl (term199 _106555 _106572 k s x i)). Qed.
Lemma lem4438330 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) : (term201 _106555 _106572 k s x) = (term201 _106555 _106572 k s x).
Proof. exact (fun_ext (fun i : _106572 => @lem4438329 _106555 _106572 k s x i)). Qed.
Lemma lem4438331 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4438333 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) : (term203 _106555 _106572 k s x) = (term203 _106555 _106572 k s x).
Proof. exact (MK_COMB (@lem4438331 _106572) (@lem4438330 _106555 _106572 k s x)). Qed.
Lemma lem4438334 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term203 _106555 _106572 k s x.
Proof. exact (EQ_MP (@lem4438333 _106555 _106572 k s x) (@lem4438315 _106555 _106572 x k s i h1)). Qed.
Lemma lem4438340 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (a : _106555) : (term38 _106555 _106572 s i a) = (term38 _106555 _106572 s i a).
Proof. exact (eq_refl (term38 _106555 _106572 s i a)). Qed.
Lemma lem4438341 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term40 _106555 _106572 s i) = (term40 _106555 _106572 s i).
Proof. exact (fun_ext (fun a : _106555 => @lem4438340 _106555 _106572 s i a)). Qed.
Lemma lem4438342 {_106555 : Type'} : (@all _106555) = (@all _106555).
Proof. exact (eq_refl (@all _106555)). Qed.
Lemma lem4438344 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term41 _106555 _106572 s i) = (term41 _106555 _106572 s i).
Proof. exact (MK_COMB (@lem4438342 _106555) (@lem4438341 _106555 _106572 s i)). Qed.
Lemma lem4438345 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term41 _106555 _106572 s i.
Proof. exact (EQ_MP (@lem4438344 _106555 _106572 s i) (@lem4438316 _106555 _106572 x k s i h1)). Qed.
Lemma lem4438353 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (i : _106572) : (term199 _106555 _106572 k s a i) = (term199 _106555 _106572 k s a i).
Proof. exact (eq_refl (term199 _106555 _106572 k s a i)). Qed.
Lemma lem4438354 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term201 _106555 _106572 k s a) = (term201 _106555 _106572 k s a).
Proof. exact (fun_ext (fun i : _106572 => @lem4438353 _106555 _106572 k s a i)). Qed.
Lemma lem4438355 {_106572 : Type'} : (@all _106572) = (@all _106572).
Proof. exact (eq_refl (@all _106572)). Qed.
Lemma lem4438357 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) : (term203 _106555 _106572 k s a) = (term203 _106555 _106572 k s a).
Proof. exact (MK_COMB (@lem4438355 _106572) (@lem4438354 _106555 _106572 k s a)). Qed.
Lemma lem4438358 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term203 _106555 _106572 k s a.
Proof. exact (EQ_MP (@lem4438357 _106555 _106572 k s a) (@lem4438318 _106555 _106572 i k s a h1)). Qed.
Lemma lem4438364 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (x : _106555) : (term38 _106555 _106572 s i x) = (term38 _106555 _106572 s i x).
Proof. exact (eq_refl (term38 _106555 _106572 s i x)). Qed.
Lemma lem4438365 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term40 _106555 _106572 s i) = (term40 _106555 _106572 s i).
Proof. exact (fun_ext (fun x : _106555 => @lem4438364 _106555 _106572 s i x)). Qed.
Lemma lem4438366 {_106555 : Type'} : (@all _106555) = (@all _106555).
Proof. exact (eq_refl (@all _106555)). Qed.
Lemma lem4438368 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) : (term41 _106555 _106572 s i) = (term41 _106555 _106572 s i).
Proof. exact (MK_COMB (@lem4438366 _106555) (@lem4438365 _106555 _106572 s i)). Qed.
Lemma lem4438369 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term41 _106555 _106572 s i.
Proof. exact (EQ_MP (@lem4438368 _106555 _106572 s i) (@lem4438320 _106555 _106572 i k s a h1)). Qed.
Lemma lem4438370 {_106555 _106572 : Type'} (_51070 : _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term326 _106555 _106572 k s x _51070.
Proof. exact (@lem4438334 _106555 _106572 x k s i h1 _51070). Qed.
Lemma lem4438371 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) (_51070 : _106572) : (term326 _106555 _106572 k s x _51070) = (term199 _106555 _106572 k s x _51070).
Proof. exact (eq_refl (term326 _106555 _106572 k s x _51070)). Qed.
Lemma lem4438373 {_106555 _106572 : Type'} (_51071 : _106555) (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term79 _106555 _106572 s i _51071.
Proof. exact (@lem4438345 _106555 _106572 x k s i h1 _51071). Qed.
Lemma lem4438374 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (_51071 : _106555) : (term79 _106555 _106572 s i _51071) = (term38 _106555 _106572 s i _51071).
Proof. exact (eq_refl (term79 _106555 _106572 s i _51071)). Qed.
Lemma lem4438376 {_106555 _106572 : Type'} (_51072 : _106572) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term326 _106555 _106572 k s a _51072.
Proof. exact (@lem4438358 _106555 _106572 i k s a h1 _51072). Qed.
Lemma lem4438377 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (_51072 : _106572) : (term326 _106555 _106572 k s a _51072) = (term199 _106555 _106572 k s a _51072).
Proof. exact (eq_refl (term326 _106555 _106572 k s a _51072)). Qed.
Lemma lem4438379 {_106555 _106572 : Type'} (_51073 : _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term79 _106555 _106572 s i _51073.
Proof. exact (@lem4438369 _106555 _106572 i k s a h1 _51073). Qed.
Lemma lem4438380 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (_51073 : _106555) : (term79 _106555 _106572 s i _51073) = (term38 _106555 _106572 s i _51073).
Proof. exact (eq_refl (term79 _106555 _106572 s i _51073)). Qed.
Lemma lem4438387 {_106555 _106572 : Type'} (_51070 : _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term199 _106555 _106572 k s x _51070.
Proof. exact (EQ_MP (@lem4438371 _106555 _106572 k s x _51070) (@lem4438370 _106555 _106572 _51070 x k s i h1)). Qed.
Lemma lem4438391 {_106555 _106572 : Type'} (_51071 : _106555) (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term38 _106555 _106572 s i _51071.
Proof. exact (EQ_MP (@lem4438374 _106555 _106572 s i _51071) (@lem4438373 _106555 _106572 _51071 x k s i h1)). Qed.
Lemma lem4438397 {_106555 _106572 : Type'} (_51072 : _106572) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term199 _106555 _106572 k s a _51072.
Proof. exact (EQ_MP (@lem4438377 _106555 _106572 k s a _51072) (@lem4438376 _106555 _106572 _51072 i k s a h1)). Qed.
Lemma lem4438401 {_106555 _106572 : Type'} (_51073 : _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term38 _106555 _106572 s i _51073.
Proof. exact (EQ_MP (@lem4438380 _106555 _106572 s i _51073) (@lem4438379 _106555 _106572 _51073 i k s a h1)). Qed.
Lemma lem4438403 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : k i.
Proof. exact (proj1 (@lem4438314 _106555 _106572 x k s i h1)). Qed.
Lemma lem4438404 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term327 _106572 k i.
Proof. exact (fun h0 : term158 _106572 k i => @lem4438403 _106555 _106572 x k s i h1). Qed.
Lemma lem4438406 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4438407 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term327 _106572 k i) = (k i).
Proof. exact (@lem4438406 (k i)). Qed.
Lemma lem4438408 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : k i.
Proof. exact (EQ_MP (@lem4438407 _106572 k i) (@lem4438404 _106555 _106572 x k s i h1)). Qed.
Lemma lem4438414 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4438415 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (_51070 : _106572) : (term199 _106555 _106572 k s x _51070) = (term329 _106555 _106572 s x k _51070).
Proof. exact (@lem4438414 (term330 _106555 _106572 s x _51070) (term158 _106572 k _51070)). Qed.
Lemma lem4438421 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438422 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (_51070 : _106572) : (term331 _106555 _106572 k s x _51070) = (term332 _106555 _106572 s x k _51070).
Proof. exact (MK_COMB (@lem4438421) (@lem4438415 _106555 _106572 s x k _51070)). Qed.
Lemma lem4438428 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (_51070 : _106572) : (term329 _106555 _106572 s x k _51070) = (term329 _106555 _106572 s x k _51070).
Proof. exact (eq_refl (term329 _106555 _106572 s x k _51070)). Qed.
Lemma lem4438429 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (_51070 : _106572) : ((term199 _106555 _106572 k s x _51070) = (term329 _106555 _106572 s x k _51070)) = ((term329 _106555 _106572 s x k _51070) = (term329 _106555 _106572 s x k _51070)).
Proof. exact (MK_COMB (@lem4438422 _106555 _106572 s x k _51070) (@lem4438428 _106555 _106572 s x k _51070)). Qed.
Lemma lem4438431 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4438432 (x : Prop) : (x = x) = True.
Proof. exact (@lem4438431 Prop x). Qed.
Lemma lem4438433 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (_51070 : _106572) : ((term329 _106555 _106572 s x k _51070) = (term329 _106555 _106572 s x k _51070)) = True.
Proof. exact (@lem4438432 (term329 _106555 _106572 s x k _51070)). Qed.
Lemma lem4438434 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (_51070 : _106572) : ((term199 _106555 _106572 k s x _51070) = (term329 _106555 _106572 s x k _51070)) = True.
Proof. exact (TRANS (@lem4438429 _106555 _106572 s x k _51070) (@lem4438433 _106555 _106572 s x k _51070)). Qed.
Lemma lem4438435 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (_51070 : _106572) : True = ((term199 _106555 _106572 k s x _51070) = (term329 _106555 _106572 s x k _51070)).
Proof. exact (SYM (@lem4438434 _106555 _106572 s x k _51070)). Qed.
Lemma lem4438436 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (_51070 : _106572) : (term199 _106555 _106572 k s x _51070) = (term329 _106555 _106572 s x k _51070).
Proof. exact (EQ_MP (@lem4438435 _106555 _106572 s x k _51070) (@lem0)). Qed.
Lemma lem4438437 {_106555 _106572 : Type'} (_51070 : _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term329 _106555 _106572 s x k _51070.
Proof. exact (EQ_MP (@lem4438436 _106555 _106572 s x k _51070) (@lem4438387 _106555 _106572 _51070 x k s i h1)). Qed.
Lemma lem4438439 (b : Prop) (a : Prop) : (a \/ b) = (term333 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4438440 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) (_51070 : _106572) : (term329 _106555 _106572 s x k _51070) = (term334 _106555 _106572 k s x _51070).
Proof. exact (@lem4438439 (term158 _106572 k _51070) (term330 _106555 _106572 s x _51070)). Qed.
Lemma lem4438442 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4438443 {_106572 : Type'} (k : _106572 -> Prop) (_51070 : _106572) : (term335 _106572 k _51070) = (k _51070).
Proof. exact (@lem4438442 (k _51070)). Qed.
Lemma lem4438444 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4438445 {_106572 : Type'} (k : _106572 -> Prop) (_51070 : _106572) : (term336 _106572 k _51070) = (term48 _106572 k _51070).
Proof. exact (MK_COMB (@lem4438444) (@lem4438443 _106572 k _51070)). Qed.
Lemma lem4438446 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (x : _106572 -> _106555) (_51070 : _106572) : (term330 _106555 _106572 s x _51070) = (term330 _106555 _106572 s x _51070).
Proof. exact (eq_refl (term330 _106555 _106572 s x _51070)). Qed.
Lemma lem4438447 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) (_51070 : _106572) : (term334 _106555 _106572 k s x _51070) = (term337 _106555 _106572 k s x _51070).
Proof. exact (MK_COMB (@lem4438445 _106572 k _51070) (@lem4438446 _106555 _106572 s x _51070)). Qed.
Lemma lem4438448 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (x : _106572 -> _106555) (_51070 : _106572) : (term329 _106555 _106572 s x k _51070) = (term337 _106555 _106572 k s x _51070).
Proof. exact (TRANS (@lem4438440 _106555 _106572 k s x _51070) (@lem4438447 _106555 _106572 k s x _51070)). Qed.
Lemma lem4438451 {_106555 _106572 : Type'} (_51070 : _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term337 _106555 _106572 k s x _51070.
Proof. exact (EQ_MP (@lem4438448 _106555 _106572 k s x _51070) (@lem4438437 _106555 _106572 _51070 x k s i h1)). Qed.
Lemma lem4438452 {_106555 _106572 : Type'} (_51070 : _106572) (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term337 _106555 _106572 k s x _51070.
Proof. exact (@lem4438451 _106555 _106572 _51070 x k s i h1). Qed.
Lemma lem4438453 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term337 _106555 _106572 k s x i.
Proof. exact (@lem4438452 _106555 _106572 i x k s i h1). Qed.
Lemma lem4438456 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term330 _106555 _106572 s x i.
Proof. exact (@lem4438453 _106555 _106572 x k s i h1 (@lem4438408 _106555 _106572 x k s i h1)). Qed.
Lemma lem4438457 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term338 _106555 _106572 s x i.
Proof. exact (fun h0 : term339 _106555 _106572 s x i => @lem4438456 _106555 _106572 x k s i h1). Qed.
Lemma lem4438459 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4438460 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (x : _106572 -> _106555) (i : _106572) : (term338 _106555 _106572 s x i) = (term330 _106555 _106572 s x i).
Proof. exact (@lem4438459 (term330 _106555 _106572 s x i)). Qed.
Lemma lem4438461 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term330 _106555 _106572 s x i.
Proof. exact (EQ_MP (@lem4438460 _106555 _106572 s x i) (@lem4438457 _106555 _106572 x k s i h1)). Qed.
Lemma lem4438464 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4438466 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (_51071 : _106555) : (term38 _106555 _106572 s i _51071) = (term340 _106555 _106572 s i _51071).
Proof. exact (@lem4438464 (s i _51071)). Qed.
Lemma lem4438469 {_106555 _106572 : Type'} (_51071 : _106555) (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term340 _106555 _106572 s i _51071.
Proof. exact (EQ_MP (@lem4438466 _106555 _106572 s i _51071) (@lem4438391 _106555 _106572 _51071 x k s i h1)). Qed.
Lemma lem4438470 {_106555 _106572 : Type'} (_51071 : _106555) (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term340 _106555 _106572 s i _51071.
Proof. exact (@lem4438469 _106555 _106572 _51071 x k s i h1). Qed.
Lemma lem4438471 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term341 _106555 _106572 s x i.
Proof. exact (@lem4438470 _106555 _106572 (x i) x k s i h1). Qed.
Lemma lem4438474 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : False.
Proof. exact (@lem4438471 _106555 _106572 x k s i h1 (@lem4438461 _106555 _106572 x k s i h1)). Qed.
Lemma lem4438475 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : term342.
Proof. exact (fun h0 : ~ False => @lem4438474 _106555 _106572 x k s i h1). Qed.
Lemma lem4438477 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4438478 : term342 = False.
Proof. exact (@lem4438477 False). Qed.
Lemma lem4438479 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (i : _106572) (h1 : term237 _106555 _106572 x k s i) : False.
Proof. exact (EQ_MP (@lem4438478) (@lem4438475 _106555 _106572 x k s i h1)). Qed.
Lemma lem4438481 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : k i.
Proof. exact (proj1 (@lem4438319 _106555 _106572 i k s a h1)). Qed.
Lemma lem4438482 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term327 _106572 k i.
Proof. exact (fun h0 : term158 _106572 k i => @lem4438481 _106555 _106572 i k s a h1). Qed.
Lemma lem4438484 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4438485 {_106572 : Type'} (k : _106572 -> Prop) (i : _106572) : (term327 _106572 k i) = (k i).
Proof. exact (@lem4438484 (k i)). Qed.
Lemma lem4438486 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : k i.
Proof. exact (EQ_MP (@lem4438485 _106572 k i) (@lem4438482 _106555 _106572 i k s a h1)). Qed.
Lemma lem4438492 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4438493 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (a : _106572 -> _106555) (k : _106572 -> Prop) (_51072 : _106572) : (term199 _106555 _106572 k s a _51072) = (term329 _106555 _106572 s a k _51072).
Proof. exact (@lem4438492 (term330 _106555 _106572 s a _51072) (term158 _106572 k _51072)). Qed.
Lemma lem4438499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438500 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (a : _106572 -> _106555) (k : _106572 -> Prop) (_51072 : _106572) : (term331 _106555 _106572 k s a _51072) = (term332 _106555 _106572 s a k _51072).
Proof. exact (MK_COMB (@lem4438499) (@lem4438493 _106555 _106572 s a k _51072)). Qed.
Lemma lem4438506 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (a : _106572 -> _106555) (k : _106572 -> Prop) (_51072 : _106572) : (term329 _106555 _106572 s a k _51072) = (term329 _106555 _106572 s a k _51072).
Proof. exact (eq_refl (term329 _106555 _106572 s a k _51072)). Qed.
Lemma lem4438507 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (a : _106572 -> _106555) (k : _106572 -> Prop) (_51072 : _106572) : ((term199 _106555 _106572 k s a _51072) = (term329 _106555 _106572 s a k _51072)) = ((term329 _106555 _106572 s a k _51072) = (term329 _106555 _106572 s a k _51072)).
Proof. exact (MK_COMB (@lem4438500 _106555 _106572 s a k _51072) (@lem4438506 _106555 _106572 s a k _51072)). Qed.
Lemma lem4438509 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4438510 (x : Prop) : (x = x) = True.
Proof. exact (@lem4438509 Prop x). Qed.
Lemma lem4438511 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (a : _106572 -> _106555) (k : _106572 -> Prop) (_51072 : _106572) : ((term329 _106555 _106572 s a k _51072) = (term329 _106555 _106572 s a k _51072)) = True.
Proof. exact (@lem4438510 (term329 _106555 _106572 s a k _51072)). Qed.
Lemma lem4438512 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (a : _106572 -> _106555) (k : _106572 -> Prop) (_51072 : _106572) : ((term199 _106555 _106572 k s a _51072) = (term329 _106555 _106572 s a k _51072)) = True.
Proof. exact (TRANS (@lem4438507 _106555 _106572 s a k _51072) (@lem4438511 _106555 _106572 s a k _51072)). Qed.
Lemma lem4438513 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (a : _106572 -> _106555) (k : _106572 -> Prop) (_51072 : _106572) : True = ((term199 _106555 _106572 k s a _51072) = (term329 _106555 _106572 s a k _51072)).
Proof. exact (SYM (@lem4438512 _106555 _106572 s a k _51072)). Qed.
Lemma lem4438514 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (a : _106572 -> _106555) (k : _106572 -> Prop) (_51072 : _106572) : (term199 _106555 _106572 k s a _51072) = (term329 _106555 _106572 s a k _51072).
Proof. exact (EQ_MP (@lem4438513 _106555 _106572 s a k _51072) (@lem0)). Qed.
Lemma lem4438515 {_106555 _106572 : Type'} (_51072 : _106572) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term329 _106555 _106572 s a k _51072.
Proof. exact (EQ_MP (@lem4438514 _106555 _106572 s a k _51072) (@lem4438397 _106555 _106572 _51072 i k s a h1)). Qed.
Lemma lem4438517 (b : Prop) (a : Prop) : (a \/ b) = (term333 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4438518 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (_51072 : _106572) : (term329 _106555 _106572 s a k _51072) = (term334 _106555 _106572 k s a _51072).
Proof. exact (@lem4438517 (term158 _106572 k _51072) (term330 _106555 _106572 s a _51072)). Qed.
Lemma lem4438520 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4438521 {_106572 : Type'} (k : _106572 -> Prop) (_51072 : _106572) : (term335 _106572 k _51072) = (k _51072).
Proof. exact (@lem4438520 (k _51072)). Qed.
Lemma lem4438522 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4438523 {_106572 : Type'} (k : _106572 -> Prop) (_51072 : _106572) : (term336 _106572 k _51072) = (term48 _106572 k _51072).
Proof. exact (MK_COMB (@lem4438522) (@lem4438521 _106572 k _51072)). Qed.
Lemma lem4438524 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (a : _106572 -> _106555) (_51072 : _106572) : (term330 _106555 _106572 s a _51072) = (term330 _106555 _106572 s a _51072).
Proof. exact (eq_refl (term330 _106555 _106572 s a _51072)). Qed.
Lemma lem4438525 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (_51072 : _106572) : (term334 _106555 _106572 k s a _51072) = (term337 _106555 _106572 k s a _51072).
Proof. exact (MK_COMB (@lem4438523 _106572 k _51072) (@lem4438524 _106555 _106572 s a _51072)). Qed.
Lemma lem4438526 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (_51072 : _106572) : (term329 _106555 _106572 s a k _51072) = (term337 _106555 _106572 k s a _51072).
Proof. exact (TRANS (@lem4438518 _106555 _106572 k s a _51072) (@lem4438525 _106555 _106572 k s a _51072)). Qed.
Lemma lem4438529 {_106555 _106572 : Type'} (_51072 : _106572) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term337 _106555 _106572 k s a _51072.
Proof. exact (EQ_MP (@lem4438526 _106555 _106572 k s a _51072) (@lem4438515 _106555 _106572 _51072 i k s a h1)). Qed.
Lemma lem4438530 {_106555 _106572 : Type'} (_51072 : _106572) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term337 _106555 _106572 k s a _51072.
Proof. exact (@lem4438529 _106555 _106572 _51072 i k s a h1). Qed.
Lemma lem4438531 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term337 _106555 _106572 k s a i.
Proof. exact (@lem4438530 _106555 _106572 i i k s a h1). Qed.
Lemma lem4438534 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term330 _106555 _106572 s a i.
Proof. exact (@lem4438531 _106555 _106572 i k s a h1 (@lem4438486 _106555 _106572 i k s a h1)). Qed.
Lemma lem4438535 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term338 _106555 _106572 s a i.
Proof. exact (fun h0 : term339 _106555 _106572 s a i => @lem4438534 _106555 _106572 i k s a h1). Qed.
Lemma lem4438537 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4438538 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (a : _106572 -> _106555) (i : _106572) : (term338 _106555 _106572 s a i) = (term330 _106555 _106572 s a i).
Proof. exact (@lem4438537 (term330 _106555 _106572 s a i)). Qed.
Lemma lem4438539 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term330 _106555 _106572 s a i.
Proof. exact (EQ_MP (@lem4438538 _106555 _106572 s a i) (@lem4438535 _106555 _106572 i k s a h1)). Qed.
Lemma lem4438542 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4438544 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (i : _106572) (_51073 : _106555) : (term38 _106555 _106572 s i _51073) = (term340 _106555 _106572 s i _51073).
Proof. exact (@lem4438542 (s i _51073)). Qed.
Lemma lem4438547 {_106555 _106572 : Type'} (_51073 : _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term340 _106555 _106572 s i _51073.
Proof. exact (EQ_MP (@lem4438544 _106555 _106572 s i _51073) (@lem4438401 _106555 _106572 _51073 i k s a h1)). Qed.
Lemma lem4438548 {_106555 _106572 : Type'} (_51073 : _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term340 _106555 _106572 s i _51073.
Proof. exact (@lem4438547 _106555 _106572 _51073 i k s a h1). Qed.
Lemma lem4438549 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term341 _106555 _106572 s a i.
Proof. exact (@lem4438548 _106555 _106572 (a i) i k s a h1). Qed.
Lemma lem4438552 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : False.
Proof. exact (@lem4438549 _106555 _106572 i k s a h1 (@lem4438539 _106555 _106572 i k s a h1)). Qed.
Lemma lem4438553 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : term342.
Proof. exact (fun h0 : ~ False => @lem4438552 _106555 _106572 i k s a h1). Qed.
Lemma lem4438555 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4438556 : term342 = False.
Proof. exact (@lem4438555 False). Qed.
Lemma lem4438557 {_106555 _106572 : Type'} (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term264 _106555 _106572 i k s a) : False.
Proof. exact (EQ_MP (@lem4438556) (@lem4438553 _106555 _106572 i k s a h1)). Qed.
Lemma lem4438558 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term318 _106555 _106572 x i k s a) : False.
Proof. exact (or_elim (@lem4438311 _106555 _106572 x i k s a h1) (fun h0 : term237 _106555 _106572 x k s i => @lem4438479 _106555 _106572 x k s i h0) (fun h0 : term264 _106555 _106572 i k s a => @lem4438557 _106555 _106572 i k s a h0)). Qed.
Lemma lem4438559 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term318 _106555 _106572 x i k s a) : (term318 _106555 _106572 x i k s a) = False.
Proof. exact (prop_ext (fun h2 : term318 _106555 _106572 x i k s a => @lem4438558 _106555 _106572 x i k s a h1) (fun h2 : False => @lem4438311 _106555 _106572 x i k s a h1)). Qed.
Lemma lem4438560 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (a : _106572 -> _106555) (h1 : term318 _106555 _106572 x i k s a) : False.
Proof. exact (EQ_MP (@lem4438559 _106555 _106572 x i k s a h1) (@lem4438311 _106555 _106572 x i k s a h1)). Qed.
Lemma lem4438561 {_106555 _106572 : Type'} (x : _106572 -> _106555) (i : _106572) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term321 _106555 _106572 x i k s) : False.
Proof. exact (ex_elim (@lem4438232 _106555 _106572 x i k s h1) (fun a : _106572 -> _106555 => fun h0 : term320 _106555 _106572 x i k s a => @lem4438560 _106555 _106572 x i k s a h0)). Qed.
Lemma lem4438562 {_106555 _106572 : Type'} (x : _106572 -> _106555) (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term323 _106555 _106572 x k s) : False.
Proof. exact (ex_elim (@lem4438231 _106555 _106572 x k s h1) (fun i : _106572 => fun h0 : term322 _106555 _106572 x k s i => @lem4438561 _106555 _106572 x i k s h0)). Qed.
Lemma lem4438563 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term60 _106555 _106572 k s) : False.
Proof. exact (ex_elim (@lem4438230 _106555 _106572 k s h1) (fun x : _106572 -> _106555 => fun h0 : term324 _106555 _106572 k s x => @lem4438562 _106555 _106572 x k s h0)). Qed.
Lemma lem4438564 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term60 _106555 _106572 k s) : (term60 _106555 _106572 k s) = False.
Proof. exact (prop_ext (fun h2 : term60 _106555 _106572 k s => @lem4438563 _106555 _106572 k s h1) (fun h2 : False => @lem4437576 _106555 _106572 k s h1)). Qed.
Lemma lem4438565 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term60 _106555 _106572 k s) : False.
Proof. exact (EQ_MP (@lem4438564 _106555 _106572 k s h1) (@lem4437576 _106555 _106572 k s h1)). Qed.
Lemma lem4438566 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : term59 _106555 _106572 k s.
Proof. exact (fun h0 : term60 _106555 _106572 k s => @lem4438565 _106555 _106572 k s h0). Qed.
Lemma lem4438567 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term45 _106555 _106572 k s) = (term57 _106555 _106572 k s).
Proof. exact (EQ_MP (@lem4437575 _106555 _106572 k s) (@lem4438566 _106555 _106572 k s)). Qed.
Lemma lem4438572 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) : term69 _106555 _106572 s.
Proof. exact (fun k : _106572 -> Prop => @lem4438567 _106555 _106572 k s). Qed.
Lemma lem4438577 {_106555 _106572 : Type'} : term73 _106555 _106572.
Proof. exact (fun s : type1470 _106555 _106572 => @lem4438572 _106555 _106572 s). Qed.
Lemma lem4438578 {_106555 _106572 : Type'} : term72 _106555 _106572.
Proof. exact (EQ_MP (@lem4437571 _106555 _106572) (@lem4438577 _106555 _106572)). Qed.
Lemma lem4438579 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) : term343 _106555 _106572 s.
Proof. exact (@lem4438578 _106555 _106572 s). Qed.
Lemma lem4438580 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) : (term343 _106555 _106572 s) = (term68 _106555 _106572 s).
Proof. exact (eq_refl (term343 _106555 _106572 s)). Qed.
Lemma lem4438581 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) : term68 _106555 _106572 s.
Proof. exact (EQ_MP (@lem4438580 _106555 _106572 s) (@lem4438579 _106555 _106572 s)). Qed.
Lemma lem4438582 {_106555 _106572 : Type'} (s : type1470 _106555 _106572) (k : _106572 -> Prop) : term344 _106555 _106572 s k.
Proof. exact (@lem4438581 _106555 _106572 s k). Qed.
Lemma lem4438583 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term344 _106555 _106572 s k) = (term59 _106555 _106572 k s).
Proof. exact (eq_refl (term344 _106555 _106572 s k)). Qed.
Lemma lem4438584 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : term59 _106555 _106572 k s.
Proof. exact (EQ_MP (@lem4438583 _106555 _106572 k s) (@lem4438582 _106555 _106572 s k)). Qed.
Lemma lem4438586 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : term59 _106555 _106572 k s.
Proof. exact (@lem4437415 _106555 _106572 k s (@lem4438584 _106555 _106572 k s)). Qed.
Lemma lem4438587 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term60 _106555 _106572 k s) : False.
Proof. exact (@lem4438586 _106555 _106572 k s (@lem4437399 _106555 _106572 k s h1)). Qed.
Lemma lem4438588 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term60 _106555 _106572 k s) : (term60 _106555 _106572 k s) = False.
Proof. exact (prop_ext (fun h2 : term60 _106555 _106572 k s => @lem4438587 _106555 _106572 k s h1) (fun h2 : False => @lem4437399 _106555 _106572 k s h1)). Qed.
Lemma lem4438589 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) (h1 : term60 _106555 _106572 k s) : False.
Proof. exact (EQ_MP (@lem4438588 _106555 _106572 k s h1) (@lem4437399 _106555 _106572 k s h1)). Qed.
Lemma lem4438590 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : term59 _106555 _106572 k s.
Proof. exact (fun h0 : term60 _106555 _106572 k s => @lem4438589 _106555 _106572 k s h0). Qed.
Lemma lem4438591 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term45 _106555 _106572 k s) = (term57 _106555 _106572 k s).
Proof. exact (EQ_MP (@lem4437398 _106555 _106572 k s) (@lem4438590 _106555 _106572 k s)). Qed.
Lemma lem4438592 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term30 _106555 _106572 k s) = (term33 _106555 _106572 k s).
Proof. exact (EQ_MP (@lem4437394 _106555 _106572 k s) (@lem4438591 _106555 _106572 k s)). Qed.
Lemma lem4438594 {A K : Type'} (k : K -> Prop) : term345 A K k.
Proof. exact (@lem4408929 A K k). Qed.
Lemma lem4438595 {A K : Type'} (k : K -> Prop) : (term345 A K k) = (term346 A K k).
Proof. exact (eq_refl (term345 A K k)). Qed.
Lemma lem4438596 {A K : Type'} (k : K -> Prop) : term346 A K k.
Proof. exact (EQ_MP (@lem4438595 A K k) (@lem4438594 A K k)). Qed.
Lemma lem4438597 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term347 A K k s.
Proof. exact (@lem4438596 A K k s). Qed.
Lemma lem4438598 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term347 A K k s) = (((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term27 A K k s)).
Proof. exact (eq_refl (term347 A K k s)). Qed.
Lemma lem4438624 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4438625 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem4438624 _83095 p). Qed.
Lemma lem4438626 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem4438627 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem4438626 _83095 p) (@lem4438625 _83095 p)). Qed.
Lemma lem4438628 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem4438627 _83095 p x). Qed.
Lemma lem4438629 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem4438638 {A K : Type'} (k : K -> Prop) : term348 A K k.
Proof. exact (@lem4403516 A K k). Qed.
Lemma lem4438639 {A K : Type'} (k : K -> Prop) : (term348 A K k) = (term349 A K k).
Proof. exact (eq_refl (term348 A K k)). Qed.
Lemma lem4438640 {A K : Type'} (k : K -> Prop) : term349 A K k.
Proof. exact (EQ_MP (@lem4438639 A K k) (@lem4438638 A K k)). Qed.
Lemma lem4438641 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term350 A K k s.
Proof. exact (@lem4438640 A K k s). Qed.
Lemma lem4438642 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term350 A K k s) = ((@cartesian_product A K k s) = (term351 A K k s)).
Proof. exact (eq_refl (term350 A K k s)). Qed.
Lemma lem4438646 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : (term352 A t s) = (s = t)) : (term352 A t s) = (s = t).
Proof. exact (h1). Qed.
Lemma lem4438647 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : (term352 A t s) = (s = t)) : (s = t) = (term352 A t s).
Proof. exact (SYM (@lem4438646 A s t h1)). Qed.
Lemma lem4438648 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : (s = t) = (term352 A t s)) : (s = t) = (term352 A t s).
Proof. exact (h1). Qed.
Lemma lem4438649 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : (s = t) = (term352 A t s)) : (term352 A t s) = (s = t).
Proof. exact (SYM (@lem4438648 A t s h1)). Qed.
Lemma lem4438650 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term352 A t s) = (s = t)) = ((s = t) = (term352 A t s)).
Proof. exact (prop_ext (fun h1 : (term352 A t s) = (s = t) => @lem4438647 A s t h1) (fun h1 : (s = t) = (term352 A t s) => @lem4438649 A t s h1)). Qed.
Lemma lem4438651 {A : Type'} (s : A -> Prop) : (term353 A s) = (term354 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4438650 A t s)). Qed.
Lemma lem4438652 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4438653 {A : Type'} (s : A -> Prop) : (term355 A s) = (term356 A s).
Proof. exact (MK_COMB (@lem4438652 A) (@lem4438651 A s)). Qed.
Lemma lem4438654 {A : Type'} : (term357 A) = (term358 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4438653 A s)). Qed.
Lemma lem4438655 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4438656 {A : Type'} : (term359 A) = (term360 A).
Proof. exact (MK_COMB (@lem4438655 A) (@lem4438654 A)). Qed.
Lemma lem4438657 {A : Type'} : term360 A.
Proof. exact (EQ_MP (@lem4438656 A) (@lem3219910 A)). Qed.
Lemma lem4438658 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term361 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4438659 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term361 _87967 _87968 P f) = (term362 _87967 _87968 P f).
Proof. exact (eq_refl (term361 _87967 _87968 P f)). Qed.
Lemma lem4438660 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term362 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4438659 _87967 _87968 P f) (@lem4438658 _87967 _87968 P f)). Qed.
Lemma lem4438661 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term363 _87967 _87968 P f s.
Proof. exact (@lem4438660 _87967 _87968 P f s). Qed.
Lemma lem4438662 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term363 _87967 _87968 P f s) = ((term364 _87967 _87968 f s P) = (term365 _87967 _87968 s P f)).
Proof. exact (eq_refl (term363 _87967 _87968 P f s)). Qed.
Lemma lem4438664 {A : Type'} (s : A -> Prop) : term366 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4438665 {A : Type'} (s : A -> Prop) : (term366 A s) = (term367 A s).
Proof. exact (eq_refl (term366 A s)). Qed.
Lemma lem4438666 {A : Type'} (s : A -> Prop) : term367 A s.
Proof. exact (EQ_MP (@lem4438665 A s) (@lem4438664 A s)). Qed.
Lemma lem4438667 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term368 A s t.
Proof. exact (@lem4438666 A s t). Qed.
Lemma lem4438668 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term368 A s t) = ((@SUBSET A s t) = (term369 A s t)).
Proof. exact (eq_refl (term368 A s t)). Qed.
Lemma lem4438670 {A : Type'} (s : A -> Prop) : term370 A s.
Proof. exact (@lem4438657 A s). Qed.
Lemma lem4438671 {A : Type'} (s : A -> Prop) : (term370 A s) = (term356 A s).
Proof. exact (eq_refl (term370 A s)). Qed.
Lemma lem4438672 {A : Type'} (s : A -> Prop) : term356 A s.
Proof. exact (EQ_MP (@lem4438671 A s) (@lem4438670 A s)). Qed.
Lemma lem4438673 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term371 A s t.
Proof. exact (@lem4438672 A s t). Qed.
Lemma lem4438674 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term371 A s t) = ((s = t) = (term352 A t s)).
Proof. exact (eq_refl (term371 A s t)). Qed.
Lemma lem4438676 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term372 A K k s.
Proof. exact (@lem9784 ((@cartesian_product A K k s) = (@EMPTY (K -> A)))). Qed.
Lemma lem4438677 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term372 A K k s) = (term373 A K k s).
Proof. exact (eq_refl (term372 A K k s)). Qed.
Lemma lem4438678 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term373 A K k s.
Proof. exact (EQ_MP (@lem4438677 A K k s) (@lem4438676 A K k s)). Qed.
Lemma lem4438680 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : term374 A K k s.
Proof. exact (h1). Qed.
Lemma lem4438686 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (@cartesian_product A K k s) = (@EMPTY (K -> A)).
Proof. exact (h1). Qed.
Lemma lem4438687 {A K : Type'} (i : K) : (term375 A K i) = (term375 A K i).
Proof. exact (eq_refl (term375 A K i)). Qed.
Lemma lem4438688 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term376 A K i k s) = (term377 A K i).
Proof. exact (MK_COMB (@lem4438687 A K i) (@lem4438686 A K k s h1)). Qed.
Lemma lem4438690 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem4438691 {A K : Type'} (f : type802 A K) : (@IMAGE (K -> A) A f (@EMPTY (K -> A))) = (@EMPTY A).
Proof. exact (@lem4438690 (K -> A) A f). Qed.
Lemma lem4438692 {A K : Type'} (i : K) : (term377 A K i) = (@EMPTY A).
Proof. exact (@lem4438691 A K (term378 A K i)). Qed.
Lemma lem4438693 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term376 A K i k s) = (@EMPTY A).
Proof. exact (TRANS (@lem4438688 A K i k s h1) (@lem4438692 A K i)). Qed.
Lemma lem4438694 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4438695 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term379 A K i k s) = (@eq (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem4438694 A) (@lem4438693 A K i k s h1)). Qed.
Lemma lem4438701 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (@cartesian_product A K k s) = (@EMPTY (K -> A)).
Proof. exact (h1). Qed.
Lemma lem4438702 {A K : Type'} : (@eq ((K -> A) -> Prop)) = (@eq ((K -> A) -> Prop)).
Proof. exact (eq_refl (@eq ((K -> A) -> Prop))). Qed.
Lemma lem4438703 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term380 A K k s) = (@eq ((K -> A) -> Prop) (@EMPTY (K -> A))).
Proof. exact (MK_COMB (@lem4438702 A K) (@lem4438701 A K k s h1)). Qed.
Lemma lem4438704 {A K : Type'} : (@EMPTY (K -> A)) = (@EMPTY (K -> A)).
Proof. exact (eq_refl (@EMPTY (K -> A))). Qed.
Lemma lem4438705 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = ((@EMPTY (K -> A)) = (@EMPTY (K -> A))).
Proof. exact (MK_COMB (@lem4438703 A K k s h1) (@lem4438704 A K)). Qed.
Lemma lem4438707 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4438708 {A K : Type'} (x : type805 A K) : (x = x) = True.
Proof. exact (@lem4438707 (type805 A K) x). Qed.
Lemma lem4438709 {A K : Type'} : ((@EMPTY (K -> A)) = (@EMPTY (K -> A))) = True.
Proof. exact (@lem4438708 A K (@EMPTY (K -> A))). Qed.
Lemma lem4438710 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = True.
Proof. exact (TRANS (@lem4438705 A K k s h1) (@lem4438709 A K)). Qed.
Lemma lem4438711 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4438712 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term381 A K k s) = (@COND (A -> Prop) True).
Proof. exact (MK_COMB (@lem4438711 A) (@lem4438710 A K k s h1)). Qed.
Lemma lem4438713 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4438714 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term382 A K k s) = (@COND (A -> Prop) True (@EMPTY A)).
Proof. exact (MK_COMB (@lem4438712 A K k s h1) (@lem4438713 A)). Qed.
Lemma lem4438715 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term383 A K k s i) = (term383 A K k s i).
Proof. exact (eq_refl (term383 A K k s i)). Qed.
Lemma lem4438716 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term384 A K k s i) = (term385 A K k s i).
Proof. exact (MK_COMB (@lem4438714 A K k s h1) (@lem4438715 A K k s i)). Qed.
Lemma lem4438718 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4438719 {A : Type'} (t2 : A -> Prop) (t1 : A -> Prop) : (@COND (A -> Prop) True t1 t2) = t1.
Proof. exact (@lem4438718 (A -> Prop) t2 t1). Qed.
Lemma lem4438720 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term385 A K k s i) = (@EMPTY A).
Proof. exact (@lem4438719 A (term383 A K k s i) (@EMPTY A)). Qed.
Lemma lem4438721 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term384 A K k s i) = (@EMPTY A).
Proof. exact (TRANS (@lem4438716 A K i k s h1) (@lem4438720 A K k s i)). Qed.
Lemma lem4438722 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((term376 A K i k s) = (term384 A K k s i)) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem4438695 A K i k s h1) (@lem4438721 A K i k s h1)). Qed.
Lemma lem4438724 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4438725 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4438724 (A -> Prop) x). Qed.
Lemma lem4438726 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem4438725 A (@EMPTY A)). Qed.
Lemma lem4438727 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((term376 A K i k s) = (term384 A K k s i)) = True.
Proof. exact (TRANS (@lem4438722 A K i k s h1) (@lem4438726 A)). Qed.
Lemma lem4438728 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : True = ((term376 A K i k s) = (term384 A K k s i)).
Proof. exact (SYM (@lem4438727 A K i k s h1)). Qed.
Lemma lem4438729 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term376 A K i k s) = (term384 A K k s i).
Proof. exact (EQ_MP (@lem4438728 A K i k s h1) (@lem0)). Qed.
Lemma lem4438732 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term386 A K k s.
Proof. exact (@lem82 ((@cartesian_product A K k s) = (@EMPTY (K -> A)))). Qed.
Lemma lem4438750 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = False.
Proof. exact (@lem4438732 A K k s (@lem4438680 A K k s h1)). Qed.
Lemma lem4438751 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4438752 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : (term381 A K k s) = (@COND (A -> Prop) False).
Proof. exact (MK_COMB (@lem4438751 A) (@lem4438750 A K k s h1)). Qed.
Lemma lem4438753 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4438754 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : (term382 A K k s) = (@COND (A -> Prop) False (@EMPTY A)).
Proof. exact (MK_COMB (@lem4438752 A K k s h1) (@lem4438753 A)). Qed.
Lemma lem4438755 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term383 A K k s i) = (term383 A K k s i).
Proof. exact (eq_refl (term383 A K k s i)). Qed.
Lemma lem4438756 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : (term384 A K k s i) = (term387 A K k s i).
Proof. exact (MK_COMB (@lem4438754 A K k s h1) (@lem4438755 A K k s i)). Qed.
Lemma lem4438758 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4438759 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (@COND (A -> Prop) False t1 t2) = t2.
Proof. exact (@lem4438758 (A -> Prop) t1 t2). Qed.
Lemma lem4438760 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term387 A K k s i) = (term383 A K k s i).
Proof. exact (@lem4438759 A (@EMPTY A) (term383 A K k s i)). Qed.
Lemma lem4438761 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : (term384 A K k s i) = (term383 A K k s i).
Proof. exact (TRANS (@lem4438756 A K i k s h1) (@lem4438760 A K k s i)). Qed.
Lemma lem4438762 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term379 A K i k s) = (term379 A K i k s).
Proof. exact (eq_refl (term379 A K i k s)). Qed.
Lemma lem4438763 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : ((term376 A K i k s) = (term384 A K k s i)) = ((term376 A K i k s) = (term383 A K k s i)).
Proof. exact (MK_COMB (@lem4438762 A K i k s) (@lem4438761 A K i k s h1)). Qed.
Lemma lem4438766 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : ((term376 A K i k s) = (term383 A K k s i)) = ((term376 A K i k s) = (term384 A K k s i)).
Proof. exact (SYM (@lem4438763 A K i k s h1)). Qed.
Lemma lem4438770 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term352 A t s).
Proof. exact (EQ_MP (@lem4438674 A t s) (@lem4438673 A s t)). Qed.
Lemma lem4438771 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term352 A t s).
Proof. exact (@lem4438770 A t s). Qed.
Lemma lem4438772 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : ((term376 A K i k s) = (term383 A K k s i)) = (term388 A K i k s).
Proof. exact (@lem4438771 A (term383 A K k s i) (term376 A K i k s)). Qed.
Lemma lem4438776 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term369 A s t).
Proof. exact (EQ_MP (@lem4438668 A s t) (@lem4438667 A s t)). Qed.
Lemma lem4438777 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term369 A s t).
Proof. exact (@lem4438776 A s t). Qed.
Lemma lem4438778 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term389 A K k s i) = (term390 A K k s i).
Proof. exact (@lem4438777 A (term376 A K i k s) (term383 A K k s i)). Qed.
Lemma lem4438780 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term364 _87967 _87968 f s P) = (term365 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4438662 _87967 _87968 s P f) (@lem4438661 _87967 _87968 P f s)). Qed.
Lemma lem4438781 {A K : Type'} (s : type805 A K) (P : A -> Prop) (f : type802 A K) : (term391 A K f s P) = (term392 A K s P f).
Proof. exact (@lem4438780 A (K -> A) s P f). Qed.
Lemma lem4438782 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term393 A K k s i) = (term394 A K k s i).
Proof. exact (@lem4438781 A K (@cartesian_product A K k s) (term395 A K k s i) (term378 A K i)). Qed.
Lemma lem4438783 {A K : Type'} (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term396 A K k s i x) = (term397 A K x k s i).
Proof. exact (eq_refl (term396 A K k s i x)). Qed.
Lemma lem4438784 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term398 A K x i k s) = (term398 A K x i k s).
Proof. exact (eq_refl (term398 A K x i k s)). Qed.
Lemma lem4438785 {A K : Type'} (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term399 A K k s i x) = (term400 A K x k s i).
Proof. exact (MK_COMB (@lem4438784 A K x i k s) (@lem4438783 A K x k s i)). Qed.
Lemma lem4438786 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term401 A K k s i) = (term402 A K k s i).
Proof. exact (fun_ext (fun x : A => @lem4438785 A K x k s i)). Qed.
Lemma lem4438787 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4438788 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term393 A K k s i) = (term390 A K k s i).
Proof. exact (MK_COMB (@lem4438787 A) (@lem4438786 A K k s i)). Qed.
Lemma lem4438789 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438790 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term403 A K k s i) = (term404 A K k s i).
Proof. exact (MK_COMB (@lem4438789) (@lem4438788 A K k s i)). Qed.
Lemma lem4438791 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term405 A K k s i x) = (term406 A K x k s i).
Proof. exact (eq_refl (term405 A K k s i x)). Qed.
Lemma lem4438792 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term407 A K x k s) = (term407 A K x k s).
Proof. exact (eq_refl (term407 A K x k s)). Qed.
Lemma lem4438793 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term408 A K k s i x) = (term409 A K x k s i).
Proof. exact (MK_COMB (@lem4438792 A K x k s) (@lem4438791 A K x k s i)). Qed.
Lemma lem4438794 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term410 A K k s i) = (term411 A K k s i).
Proof. exact (fun_ext (fun x : K -> A => @lem4438793 A K x k s i)). Qed.
Lemma lem4438795 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4438796 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term394 A K k s i) = (term412 A K k s i).
Proof. exact (MK_COMB (@lem4438795 A K) (@lem4438794 A K k s i)). Qed.
Lemma lem4438797 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : ((term393 A K k s i) = (term394 A K k s i)) = ((term390 A K k s i) = (term412 A K k s i)).
Proof. exact (MK_COMB (@lem4438790 A K k s i) (@lem4438796 A K k s i)). Qed.
Lemma lem4438798 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term390 A K k s i) = (term412 A K k s i).
Proof. exact (EQ_MP (@lem4438797 A K k s i) (@lem4438782 A K k s i)). Qed.
Lemma lem4438803 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term389 A K k s i) = (term412 A K k s i).
Proof. exact (TRANS (@lem4438778 A K k s i) (@lem4438798 A K k s i)). Qed.
Lemma lem4438807 {A B : Type'} (f : A -> B) (y : A) : (term413 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4438808 {A K : Type'} (f : type802 A K) (y : K -> A) : (term414 A K f y) = (f y).
Proof. exact (@lem4438807 (K -> A) A f y). Qed.
Lemma lem4438809 {A K : Type'} (i : K) (x : K -> A) : (term415 A K i x) = (term416 A K i x).
Proof. exact (@lem4438808 A K (term378 A K i) x). Qed.
Lemma lem4438810 {A K : Type'} (x : K -> A) (i : K) : (term416 A K i x) = (x i).
Proof. exact (eq_refl (term416 A K i x)). Qed.
Lemma lem4438811 {A K : Type'} (i : K) : (term417 A K i) = (term378 A K i).
Proof. exact (fun_ext (fun x : K -> A => @lem4438810 A K x i)). Qed.
Lemma lem4438812 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4438813 {A K : Type'} (i : K) (x : K -> A) : (term415 A K i x) = (term416 A K i x).
Proof. exact (MK_COMB (@lem4438811 A K i) (@lem4438812 A K x)). Qed.
Lemma lem4438814 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4438815 {A K : Type'} (i : K) (x : K -> A) : (term418 A K i x) = (term419 A K i x).
Proof. exact (MK_COMB (@lem4438814 A) (@lem4438813 A K i x)). Qed.
Lemma lem4438816 {A K : Type'} (x : K -> A) (i : K) : (term416 A K i x) = (x i).
Proof. exact (eq_refl (term416 A K i x)). Qed.
Lemma lem4438817 {A K : Type'} (x : K -> A) (i : K) : ((term415 A K i x) = (term416 A K i x)) = ((term416 A K i x) = (x i)).
Proof. exact (MK_COMB (@lem4438815 A K i x) (@lem4438816 A K x i)). Qed.
Lemma lem4438818 {A K : Type'} (x : K -> A) (i : K) : (term416 A K i x) = (x i).
Proof. exact (EQ_MP (@lem4438817 A K x i) (@lem4438809 A K i x)). Qed.
Lemma lem4438819 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4438820 {A K : Type'} (x : K -> A) (i : K) : (term420 A K i x) = (term421 A K x i).
Proof. exact (MK_COMB (@lem4438819 A) (@lem4438818 A K x i)). Qed.
Lemma lem4438821 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term383 A K k s i) = (term383 A K k s i).
Proof. exact (eq_refl (term383 A K k s i)). Qed.
Lemma lem4438822 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term406 A K x k s i) = (term422 A K x k s i).
Proof. exact (MK_COMB (@lem4438820 A K x i) (@lem4438821 A K k s i)). Qed.
Lemma lem4438823 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term407 A K x k s) = (term407 A K x k s).
Proof. exact (eq_refl (term407 A K x k s)). Qed.
Lemma lem4438824 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term409 A K x k s i) = (term423 A K x k s i).
Proof. exact (MK_COMB (@lem4438823 A K x k s) (@lem4438822 A K x k s i)). Qed.
Lemma lem4438827 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term411 A K k s i) = (term424 A K k s i).
Proof. exact (fun_ext (fun x : K -> A => @lem4438824 A K x k s i)). Qed.
Lemma lem4438828 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4438829 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term412 A K k s i) = (term425 A K k s i).
Proof. exact (MK_COMB (@lem4438828 A K) (@lem4438827 A K k s i)). Qed.
Lemma lem4438834 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term389 A K k s i) = (term425 A K k s i).
Proof. exact (TRANS (@lem4438803 A K k s i) (@lem4438829 A K k s i)). Qed.
Lemma lem4438835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4438836 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term426 A K k s i) = (term427 A K k s i).
Proof. exact (MK_COMB (@lem4438835) (@lem4438834 A K k s i)). Qed.
Lemma lem4438838 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term369 A s t).
Proof. exact (EQ_MP (@lem4438668 A s t) (@lem4438667 A s t)). Qed.
Lemma lem4438839 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term369 A s t).
Proof. exact (@lem4438838 A s t). Qed.
Lemma lem4438840 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term428 A K i k s) = (term429 A K i k s).
Proof. exact (@lem4438839 A (term383 A K k s i) (term376 A K i k s)). Qed.
Lemma lem4438847 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term388 A K i k s) = (term430 A K i k s).
Proof. exact (MK_COMB (@lem4438836 A K k s i) (@lem4438840 A K i k s)). Qed.
Lemma lem4438850 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : ((term376 A K i k s) = (term383 A K k s i)) = (term430 A K i k s).
Proof. exact (TRANS (@lem4438772 A K i k s) (@lem4438847 A K i k s)). Qed.
Lemma lem4438851 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term430 A K i k s) = ((term376 A K i k s) = (term383 A K k s i)).
Proof. exact (SYM (@lem4438850 A K i k s)). Qed.
Lemma lem4438861 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term431 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4438862 (p : Prop) (q : Prop) (p' : Prop) : term432 p q p'.
Proof. exact (fun q' : Prop => @lem4438861 p q p' q'). Qed.
Lemma lem4438863 (p : Prop) (q : Prop) : term433 p q.
Proof. exact (fun p' : Prop => @lem4438862 p q p'). Qed.
Lemma lem4438864 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) : term434 A K x k s i.
Proof. exact (@lem4438863 (term435 A K x k s) (term422 A K x k s i)). Qed.
Lemma lem4438865 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) (p' : Prop) : term436 A K x k s i p'.
Proof. exact (@lem4438864 A K x k s i p'). Qed.
Lemma lem4438866 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) (p' : Prop) : (term436 A K x k s i p') = (term437 A K x k s i p').
Proof. exact (eq_refl (term436 A K x k s i p')). Qed.
Lemma lem4438867 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) (p' : Prop) : term437 A K x k s i p'.
Proof. exact (EQ_MP (@lem4438866 A K x k s i p') (@lem4438865 A K x k s i p')). Qed.
Lemma lem4438868 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : term438 A K x k s i p' q'.
Proof. exact (@lem4438867 A K x k s i p' q'). Qed.
Lemma lem4438869 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : (term438 A K x k s i p' q') = (term439 A K x k s i p' q').
Proof. exact (eq_refl (term438 A K x k s i p' q')). Qed.
Lemma lem4438870 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : term439 A K x k s i p' q'.
Proof. exact (EQ_MP (@lem4438869 A K x k s i p' q') (@lem4438868 A K x k s i p' q')). Qed.
Lemma lem4438872 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term351 A K k s).
Proof. exact (EQ_MP (@lem4438642 A K k s) (@lem4438641 A K k s)). Qed.
Lemma lem4438873 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term351 A K k s).
Proof. exact (@lem4438872 A K k s). Qed.
Lemma lem4438915 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4438916 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term435 A K x k s) = (term440 A K x k s).
Proof. exact (MK_COMB (@lem4438915 A K x) (@lem4438873 A K k s)). Qed.
Lemma lem4438918 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4438629 _83095 p x) (@lem4438628 _83095 p x)). Qed.
Lemma lem4438919 {A K : Type'} (p : type805 A K) (x : K -> A) : (term441 A K x p) = (p x).
Proof. exact (@lem4438918 (K -> A) p x). Qed.
Lemma lem4438920 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term442 A K x k s) = (term443 A K k s x).
Proof. exact (@lem4438919 A K (term444 A K k s) x). Qed.
Lemma lem4438921 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term443 A K k s f) = (term445 A K f k s).
Proof. exact (eq_refl (term443 A K k s f)). Qed.
Lemma lem4438922 {A K : Type'} (GEN_PVAR_141 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_141) = (@SETSPEC (K -> A) GEN_PVAR_141).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_141)). Qed.
Lemma lem4438923 {A K : Type'} (GEN_PVAR_141 : K -> A) (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term446 A K GEN_PVAR_141 k s f) = (term447 A K GEN_PVAR_141 f k s).
Proof. exact (MK_COMB (@lem4438922 A K GEN_PVAR_141) (@lem4438921 A K f k s)). Qed.
Lemma lem4438924 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4438925 {A K : Type'} (GEN_PVAR_141 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term448 A K GEN_PVAR_141 k s f) = (term449 A K GEN_PVAR_141 k s f).
Proof. exact (MK_COMB (@lem4438923 A K GEN_PVAR_141 f k s) (@lem4438924 A K f)). Qed.
Lemma lem4438926 {A K : Type'} (GEN_PVAR_141 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term450 A K GEN_PVAR_141 k s) = (term451 A K GEN_PVAR_141 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4438925 A K GEN_PVAR_141 k s f)). Qed.
Lemma lem4438927 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4438928 {A K : Type'} (GEN_PVAR_141 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term452 A K GEN_PVAR_141 k s) = (term453 A K GEN_PVAR_141 k s).
Proof. exact (MK_COMB (@lem4438927 A K) (@lem4438926 A K GEN_PVAR_141 k s)). Qed.
Lemma lem4438929 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term454 A K k s) = (term455 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_141 : K -> A => @lem4438928 A K GEN_PVAR_141 k s)). Qed.
Lemma lem4438930 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4438931 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term456 A K k s) = (term351 A K k s).
Proof. exact (MK_COMB (@lem4438930 A K) (@lem4438929 A K k s)). Qed.
Lemma lem4438932 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4438933 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term442 A K x k s) = (term440 A K x k s).
Proof. exact (MK_COMB (@lem4438932 A K x) (@lem4438931 A K k s)). Qed.
Lemma lem4438934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4438935 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term457 A K x k s) = (term458 A K x k s).
Proof. exact (MK_COMB (@lem4438934) (@lem4438933 A K x k s)). Qed.
Lemma lem4438936 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term443 A K k s x) = (term445 A K x k s).
Proof. exact (eq_refl (term443 A K k s x)). Qed.
Lemma lem4438937 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : ((term442 A K x k s) = (term443 A K k s x)) = ((term440 A K x k s) = (term445 A K x k s)).
Proof. exact (MK_COMB (@lem4438935 A K x k s) (@lem4438936 A K x k s)). Qed.
Lemma lem4438938 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term440 A K x k s) = (term445 A K x k s).
Proof. exact (EQ_MP (@lem4438937 A K x k s) (@lem4438920 A K k s x)). Qed.
Lemma lem4438976 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term435 A K x k s) = (term445 A K x k s).
Proof. exact (TRANS (@lem4438916 A K x k s) (@lem4438938 A K x k s)). Qed.
Lemma lem4438977 {A K : Type'} (i : K) (x : K -> A) (k : K -> Prop) (s : type1470 A K) (q' : Prop) : term459 A K i x k s q'.
Proof. exact (@lem4438870 A K x k s i (term445 A K x k s) q'). Qed.
Lemma lem4438978 {A K : Type'} (i : K) (x : K -> A) (k : K -> Prop) (s : type1470 A K) (q' : Prop) : term460 A K i x k s q'.
Proof. exact (@lem4438977 A K i x k s q' (@lem4438976 A K x k s)). Qed.
Lemma lem4438979 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term445 A K x k s) : term445 A K x k s.
Proof. exact (h1). Qed.
Lemma lem4438980 {A K : Type'} (i : K) (x : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term445 A K x k s) : term461 A K x k s i.
Proof. exact (@lem4438979 A K x k s h1 i). Qed.
Lemma lem4438981 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term461 A K x k s i) = (term422 A K x k s i).
Proof. exact (eq_refl (term461 A K x k s i)). Qed.
Lemma lem4438982 {A K : Type'} (i : K) (x : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term445 A K x k s) : term422 A K x k s i.
Proof. exact (EQ_MP (@lem4438981 A K x k s i) (@lem4438980 A K i x k s h1)). Qed.
Lemma lem4438983 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term422 A K x k s i) = ((term422 A K x k s i) = True).
Proof. exact (@lem7 (term422 A K x k s i)). Qed.
Lemma lem4438986 {A K : Type'} (i : K) (x : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term445 A K x k s) : (term422 A K x k s i) = True.
Proof. exact (EQ_MP (@lem4438983 A K x k s i) (@lem4438982 A K i x k s h1)). Qed.
Lemma lem4438987 {A K : Type'} (i : K) (x : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term445 A K x k s) : (term422 A K x k s i) = True.
Proof. exact (@lem4438986 A K i x k s h1). Qed.
Lemma lem4438988 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) : term462 A K x k s i.
Proof. exact (fun h0 : term445 A K x k s => @lem4438987 A K i x k s h0). Qed.
Lemma lem4438989 {A K : Type'} (i : K) (x : K -> A) (k : K -> Prop) (s : type1470 A K) : term463 A K i x k s.
Proof. exact (@lem4438978 A K i x k s True). Qed.
Lemma lem4438990 {A K : Type'} (i : K) (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term423 A K x k s i) = (term464 A K x k s).
Proof. exact (@lem4438989 A K i x k s (@lem4438988 A K x k s i)). Qed.
Lemma lem4438992 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4438993 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term464 A K x k s) = True.
Proof. exact (@lem4438992 (term445 A K x k s)). Qed.
Lemma lem4438994 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term423 A K x k s i) = True.
Proof. exact (TRANS (@lem4438990 A K i x k s) (@lem4438993 A K x k s)). Qed.
Lemma lem4438995 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term424 A K k s i) = (term465 A K).
Proof. exact (fun_ext (fun x : K -> A => @lem4438994 A K x k s i)). Qed.
Lemma lem4438996 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4438997 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term425 A K k s i) = (term466 A K).
Proof. exact (MK_COMB (@lem4438996 A K) (@lem4438995 A K k s i)). Qed.
Lemma lem4438999 {A : Type'} (t : Prop) : (term149 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4439000 {A K : Type'} (t : Prop) : (term467 A K t) = t.
Proof. exact (@lem4438999 (K -> A) t). Qed.
Lemma lem4439001 {A K : Type'} : (term466 A K) = True.
Proof. exact (@lem4439000 A K True). Qed.
Lemma lem4439002 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term425 A K k s i) = True.
Proof. exact (TRANS (@lem4438997 A K k s i) (@lem4439001 A K)). Qed.
Lemma lem4439003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4439004 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term427 A K k s i) = (and True).
Proof. exact (MK_COMB (@lem4439003) (@lem4439002 A K k s i)). Qed.
Lemma lem4439012 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term431 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4439013 (p : Prop) (q : Prop) (p' : Prop) : term432 p q p'.
Proof. exact (fun q' : Prop => @lem4439012 p q p' q'). Qed.
Lemma lem4439014 (p : Prop) (q : Prop) : term433 p q.
Proof. exact (fun p' : Prop => @lem4439013 p q p'). Qed.
Lemma lem4439015 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : term468 A K x i k s.
Proof. exact (@lem4439014 (term397 A K x k s i) (term469 A K x i k s)). Qed.
Lemma lem4439016 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) (p' : Prop) : term470 A K x i k s p'.
Proof. exact (@lem4439015 A K x i k s p'). Qed.
Lemma lem4439017 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) (p' : Prop) : (term470 A K x i k s p') = (term471 A K x i k s p').
Proof. exact (eq_refl (term470 A K x i k s p')). Qed.
Lemma lem4439018 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) (p' : Prop) : term471 A K x i k s p'.
Proof. exact (EQ_MP (@lem4439017 A K x i k s p') (@lem4439016 A K x i k s p')). Qed.
Lemma lem4439019 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) (p' : Prop) (q' : Prop) : term472 A K x i k s p' q'.
Proof. exact (@lem4439018 A K x i k s p' q'). Qed.
Lemma lem4439020 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) (p' : Prop) (q' : Prop) : (term472 A K x i k s p' q') = (term473 A K x i k s p' q').
Proof. exact (eq_refl (term472 A K x i k s p' q')). Qed.
Lemma lem4439021 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) (p' : Prop) (q' : Prop) : term473 A K x i k s p' q'.
Proof. exact (EQ_MP (@lem4439020 A K x i k s p' q') (@lem4439019 A K x i k s p' q')). Qed.
Lemma lem4439055 {A K : Type'} (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term397 A K x k s i) = (term397 A K x k s i).
Proof. exact (eq_refl (term397 A K x k s i)). Qed.
Lemma lem4439056 {A K : Type'} (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (q' : Prop) : term474 A K x k s i q'.
Proof. exact (@lem4439021 A K x i k s (term397 A K x k s i) q'). Qed.
Lemma lem4439057 {A K : Type'} (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (q' : Prop) : term475 A K x k s i q'.
Proof. exact (@lem4439056 A K x k s i q' (@lem4439055 A K x k s i)). Qed.
Lemma lem4439062 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term351 A K k s).
Proof. exact (EQ_MP (@lem4438642 A K k s) (@lem4438641 A K k s)). Qed.
Lemma lem4439063 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term351 A K k s).
Proof. exact (@lem4439062 A K k s). Qed.
Lemma lem4439105 {A K : Type'} (i : K) : (term375 A K i) = (term375 A K i).
Proof. exact (eq_refl (term375 A K i)). Qed.
Lemma lem4439106 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term376 A K i k s) = (term476 A K i k s).
Proof. exact (MK_COMB (@lem4439105 A K i) (@lem4439063 A K k s)). Qed.
Lemma lem4439148 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4439149 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term469 A K x i k s) = (term477 A K x i k s).
Proof. exact (MK_COMB (@lem4439148 A x) (@lem4439106 A K i k s)). Qed.
Lemma lem4439191 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : term478 A K x i k s.
Proof. exact (fun h0 : term397 A K x k s i => @lem4439149 A K x i k s). Qed.
Lemma lem4439192 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : term479 A K x i k s.
Proof. exact (@lem4439057 A K x k s i (term477 A K x i k s)). Qed.
Lemma lem4439193 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term480 A K x i k s) = (term481 A K x i k s).
Proof. exact (@lem4439192 A K x i k s (@lem4439191 A K x i k s)). Qed.
Lemma lem4439365 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term482 A K i k s) = (term483 A K i k s).
Proof. exact (fun_ext (fun x : A => @lem4439193 A K x i k s)). Qed.
Lemma lem4439537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4439538 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term429 A K i k s) = (term484 A K i k s).
Proof. exact (MK_COMB (@lem4439537 A) (@lem4439365 A K i k s)). Qed.
Lemma lem4439714 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term430 A K i k s) = (term485 A K i k s).
Proof. exact (MK_COMB (@lem4439004 A K k s i) (@lem4439538 A K i k s)). Qed.
Lemma lem4439716 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4439717 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term485 A K i k s) = (term484 A K i k s).
Proof. exact (@lem4439716 (term484 A K i k s)). Qed.
Lemma lem4439893 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term430 A K i k s) = (term484 A K i k s).
Proof. exact (TRANS (@lem4439714 A K i k s) (@lem4439717 A K i k s)). Qed.
Lemma lem4439894 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) : (term484 A K i k s) = (term430 A K i k s).
Proof. exact (SYM (@lem4439893 A K i k s)). Qed.
Lemma lem4439895 {A K : Type'} (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term397 A K x k s i) : term397 A K x k s i.
Proof. exact (h1). Qed.
Lemma lem4439897 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term27 A K k s).
Proof. exact (EQ_MP (@lem4438598 A K k s) (@lem4438597 A K k s)). Qed.
Lemma lem4439898 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term27 A K k s).
Proof. exact (@lem4439897 A K k s). Qed.
Lemma lem4439899 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4439900 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term374 A K k s) = (term29 A K k s).
Proof. exact (MK_COMB (@lem4439899) (@lem4439898 A K k s)). Qed.
Lemma lem4439901 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : term29 A K k s.
Proof. exact (EQ_MP (@lem4439900 A K k s) (@lem4438680 A K k s h1)). Qed.
Lemma lem4439905 {_106555 _106572 : Type'} (k : _106572 -> Prop) (s : type1470 _106555 _106572) : (term29 _106555 _106572 k s) = (term33 _106555 _106572 k s).
Proof. exact (EQ_MP (@lem4437298 _106555 _106572 k s) (@lem4438592 _106555 _106572 k s)). Qed.
Lemma lem4439906 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term29 A K k s) = (term33 A K k s).
Proof. exact (@lem4439905 A K k s). Qed.
Lemma lem4439917 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4439918 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term486 A K k s) = (term487 A K k s).
Proof. exact (MK_COMB (@lem4439917) (@lem4439906 A K k s)). Qed.
Lemma lem4439927 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term477 A K x i k s) = (term477 A K x i k s).
Proof. exact (eq_refl (term477 A K x i k s)). Qed.
Lemma lem4439928 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term488 A K x i k s) = (term489 A K x i k s).
Proof. exact (MK_COMB (@lem4439918 A K k s) (@lem4439927 A K x i k s)). Qed.
Lemma lem4439931 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term489 A K x i k s) = (term488 A K x i k s).
Proof. exact (SYM (@lem4439928 A K x i k s)). Qed.
Lemma lem4439935 {A B : Type'} (P : type1413 A B) : (term18 A B P) = (term19 A B P).
Proof. exact (EQ_MP (@lem4437231 A B P) (@lem4437230 A B P)). Qed.
Lemma lem4439936 {A K : Type'} (P : type1470 A K) : (term184 A K P) = (term185 A K P).
Proof. exact (@lem4439935 K A P). Qed.
Lemma lem4439937 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term490 A K k s) = (term491 A K k s).
Proof. exact (@lem4439936 A K (term492 A K k s)). Qed.
Lemma lem4439938 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term493 A K k s i) = (term51 A K k s i).
Proof. exact (eq_refl (term493 A K k s i)). Qed.
Lemma lem4439939 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4439940 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) (a : A) : (term494 A K k s i a) = (term495 A K k s i a).
Proof. exact (MK_COMB (@lem4439938 A K k s i) (@lem4439939 A a)). Qed.
Lemma lem4439941 {A K : Type'} (k : K -> Prop) (a : A) (s : type1470 A K) (i : K) : (term495 A K k s i a) = (term49 A K k a s i).
Proof. exact (eq_refl (term495 A K k s i a)). Qed.
Lemma lem4439942 {A K : Type'} (k : K -> Prop) (a : A) (s : type1470 A K) (i : K) : (term494 A K k s i a) = (term49 A K k a s i).
Proof. exact (TRANS (@lem4439940 A K k s i a) (@lem4439941 A K k a s i)). Qed.
Lemma lem4439943 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term496 A K k s i) = (term51 A K k s i).
Proof. exact (fun_ext (fun a : A => @lem4439942 A K k a s i)). Qed.
Lemma lem4439944 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4439945 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term497 A K k s i) = (term53 A K k s i).
Proof. exact (MK_COMB (@lem4439944 A) (@lem4439943 A K k s i)). Qed.
Lemma lem4439946 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term498 A K k s) = (term55 A K k s).
Proof. exact (fun_ext (fun i : K => @lem4439945 A K k s i)). Qed.
Lemma lem4439947 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4439948 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term490 A K k s) = (term33 A K k s).
Proof. exact (MK_COMB (@lem4439947 K) (@lem4439946 A K k s)). Qed.
Lemma lem4439949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4439950 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term499 A K k s) = (term500 A K k s).
Proof. exact (MK_COMB (@lem4439949) (@lem4439948 A K k s)). Qed.
Lemma lem4439951 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term493 A K k s i) = (term51 A K k s i).
Proof. exact (eq_refl (term493 A K k s i)). Qed.
Lemma lem4439952 {A K : Type'} (a : K -> A) (i : K) : (a i) = (a i).
Proof. exact (eq_refl (a i)). Qed.
Lemma lem4439953 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (a : K -> A) (i : K) : (term501 A K k s a i) = (term502 A K k s a i).
Proof. exact (MK_COMB (@lem4439951 A K k s i) (@lem4439952 A K a i)). Qed.
Lemma lem4439954 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) (i : K) : (term502 A K k s a i) = (term503 A K k a s i).
Proof. exact (eq_refl (term502 A K k s a i)). Qed.
Lemma lem4439955 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) (i : K) : (term501 A K k s a i) = (term503 A K k a s i).
Proof. exact (TRANS (@lem4439953 A K k s a i) (@lem4439954 A K k a s i)). Qed.
Lemma lem4439956 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term504 A K k s a) = (term505 A K k a s).
Proof. exact (fun_ext (fun i : K => @lem4439955 A K k a s i)). Qed.
Lemma lem4439957 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4439958 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term506 A K k s a) = (term507 A K k a s).
Proof. exact (MK_COMB (@lem4439957 K) (@lem4439956 A K k a s)). Qed.
Lemma lem4439959 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term508 A K k s) = (term509 A K k s).
Proof. exact (fun_ext (fun a : K -> A => @lem4439958 A K k a s)). Qed.
Lemma lem4439960 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4439961 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term491 A K k s) = (term510 A K k s).
Proof. exact (MK_COMB (@lem4439960 A K) (@lem4439959 A K k s)). Qed.
Lemma lem4439962 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((term490 A K k s) = (term491 A K k s)) = ((term33 A K k s) = (term510 A K k s)).
Proof. exact (MK_COMB (@lem4439950 A K k s) (@lem4439961 A K k s)). Qed.
Lemma lem4439963 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term33 A K k s) = (term510 A K k s).
Proof. exact (EQ_MP (@lem4439962 A K k s) (@lem4439937 A K k s)). Qed.
Lemma lem4439974 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4439975 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term487 A K k s) = (term511 A K k s).
Proof. exact (MK_COMB (@lem4439974) (@lem4439963 A K k s)). Qed.
Lemma lem4439984 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term477 A K x i k s) = (term477 A K x i k s).
Proof. exact (eq_refl (term477 A K x i k s)). Qed.
Lemma lem4439985 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term489 A K x i k s) = (term512 A K x i k s).
Proof. exact (MK_COMB (@lem4439975 A K k s) (@lem4439984 A K x i k s)). Qed.
Lemma lem4439987 {A : Type'} (P : A -> Prop) (Q : Prop) : (term15 A P Q) = (term16 A P Q).
Proof. exact (EQ_MP (@lem4437228 A P Q) (@lem4437227 A P Q)). Qed.
Lemma lem4439988 {A K : Type'} (P : type805 A K) (Q : Prop) : (term513 A K P Q) = (term514 A K P Q).
Proof. exact (@lem4439987 (K -> A) P Q). Qed.
Lemma lem4439989 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term515 A K x i k s) = (term516 A K x i k s).
Proof. exact (@lem4439988 A K (term509 A K k s) (term477 A K x i k s)). Qed.
Lemma lem4439990 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term517 A K k s a) = (term507 A K k a s).
Proof. exact (eq_refl (term517 A K k s a)). Qed.
Lemma lem4439991 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term518 A K k s) = (term509 A K k s).
Proof. exact (fun_ext (fun a : K -> A => @lem4439990 A K k a s)). Qed.
Lemma lem4439992 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4439993 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term519 A K k s) = (term510 A K k s).
Proof. exact (MK_COMB (@lem4439992 A K) (@lem4439991 A K k s)). Qed.
Lemma lem4439994 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4439995 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term520 A K k s) = (term511 A K k s).
Proof. exact (MK_COMB (@lem4439994) (@lem4439993 A K k s)). Qed.
Lemma lem4439996 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term477 A K x i k s) = (term477 A K x i k s).
Proof. exact (eq_refl (term477 A K x i k s)). Qed.
Lemma lem4439997 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term515 A K x i k s) = (term512 A K x i k s).
Proof. exact (MK_COMB (@lem4439995 A K k s) (@lem4439996 A K x i k s)). Qed.
Lemma lem4439998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4439999 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term521 A K x i k s) = (term522 A K x i k s).
Proof. exact (MK_COMB (@lem4439998) (@lem4439997 A K x i k s)). Qed.
Lemma lem4440000 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term517 A K k s a) = (term507 A K k a s).
Proof. exact (eq_refl (term517 A K k s a)). Qed.
Lemma lem4440001 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4440002 {A K : Type'} (k : K -> Prop) (a : K -> A) (s : type1470 A K) : (term523 A K k s a) = (term524 A K k a s).
Proof. exact (MK_COMB (@lem4440001) (@lem4440000 A K k a s)). Qed.
Lemma lem4440003 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term477 A K x i k s) = (term477 A K x i k s).
Proof. exact (eq_refl (term477 A K x i k s)). Qed.
Lemma lem4440004 {A K : Type'} (a : K -> A) (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term525 A K a x i k s) = (term526 A K a x i k s).
Proof. exact (MK_COMB (@lem4440002 A K k a s) (@lem4440003 A K x i k s)). Qed.
Lemma lem4440005 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term527 A K x i k s) = (term528 A K x i k s).
Proof. exact (fun_ext (fun a : K -> A => @lem4440004 A K a x i k s)). Qed.
Lemma lem4440006 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4440007 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term516 A K x i k s) = (term529 A K x i k s).
Proof. exact (MK_COMB (@lem4440006 A K) (@lem4440005 A K x i k s)). Qed.
Lemma lem4440008 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : ((term515 A K x i k s) = (term516 A K x i k s)) = ((term512 A K x i k s) = (term529 A K x i k s)).
Proof. exact (MK_COMB (@lem4439999 A K x i k s) (@lem4440007 A K x i k s)). Qed.
Lemma lem4440009 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term512 A K x i k s) = (term529 A K x i k s).
Proof. exact (EQ_MP (@lem4440008 A K x i k s) (@lem4439989 A K x i k s)). Qed.
Lemma lem4440030 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term489 A K x i k s) = (term529 A K x i k s).
Proof. exact (TRANS (@lem4439985 A K x i k s) (@lem4440009 A K x i k s)). Qed.
Lemma lem4440031 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term529 A K x i k s) = (term489 A K x i k s).
Proof. exact (SYM (@lem4440030 A K x i k s)). Qed.
Lemma lem4440032 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (h1 : term507 A K k z s) : term507 A K k z s.
Proof. exact (h1). Qed.
Lemma lem4440034 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term10 A B y f s) = (term11 A B y f s).
Proof. exact (EQ_MP (@lem4437222 A B y f s) (@lem4437221 A B y s f)). Qed.
Lemma lem4440035 {A K : Type'} (y : A) (f : type802 A K) (s : type805 A K) : (term530 A K y f s) = (term531 A K y f s).
Proof. exact (@lem4440034 (K -> A) A y f s). Qed.
Lemma lem4440036 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term477 A K x i k s) = (term532 A K x i k s).
Proof. exact (@lem4440035 A K x (term378 A K i) (term351 A K k s)). Qed.
Lemma lem4440046 {A B : Type'} (f : A -> B) (y : A) : (term413 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4440047 {A K : Type'} (f : type802 A K) (y : K -> A) : (term414 A K f y) = (f y).
Proof. exact (@lem4440046 (K -> A) A f y). Qed.
Lemma lem4440048 {A K : Type'} (i : K) (x : K -> A) : (term415 A K i x) = (term416 A K i x).
Proof. exact (@lem4440047 A K (term378 A K i) x). Qed.
Lemma lem4440049 {A K : Type'} (x : K -> A) (i : K) : (term416 A K i x) = (x i).
Proof. exact (eq_refl (term416 A K i x)). Qed.
Lemma lem4440050 {A K : Type'} (i : K) : (term417 A K i) = (term378 A K i).
Proof. exact (fun_ext (fun x : K -> A => @lem4440049 A K x i)). Qed.
Lemma lem4440051 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4440052 {A K : Type'} (i : K) (x : K -> A) : (term415 A K i x) = (term416 A K i x).
Proof. exact (MK_COMB (@lem4440050 A K i) (@lem4440051 A K x)). Qed.
Lemma lem4440053 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4440054 {A K : Type'} (i : K) (x : K -> A) : (term418 A K i x) = (term419 A K i x).
Proof. exact (MK_COMB (@lem4440053 A) (@lem4440052 A K i x)). Qed.
Lemma lem4440055 {A K : Type'} (x : K -> A) (i : K) : (term416 A K i x) = (x i).
Proof. exact (eq_refl (term416 A K i x)). Qed.
Lemma lem4440056 {A K : Type'} (x : K -> A) (i : K) : ((term415 A K i x) = (term416 A K i x)) = ((term416 A K i x) = (x i)).
Proof. exact (MK_COMB (@lem4440054 A K i x) (@lem4440055 A K x i)). Qed.
Lemma lem4440057 {A K : Type'} (x : K -> A) (i : K) : (term416 A K i x) = (x i).
Proof. exact (EQ_MP (@lem4440056 A K x i) (@lem4440048 A K i x)). Qed.
Lemma lem4440058 {A : Type'} (x : A) : (@eq A x) = (@eq A x).
Proof. exact (eq_refl (@eq A x)). Qed.
Lemma lem4440059 {A K : Type'} (x : A) (x' : K -> A) (i : K) : (x = (term416 A K i x')) = (x = (x' i)).
Proof. exact (MK_COMB (@lem4440058 A x) (@lem4440057 A K x' i)). Qed.
Lemma lem4440062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4440063 {A K : Type'} (x : A) (x' : K -> A) (i : K) : (term533 A K x i x') = (term534 A K x x' i).
Proof. exact (MK_COMB (@lem4440062) (@lem4440059 A K x x' i)). Qed.
Lemma lem4440065 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4437206 _83095 p x) (@lem4437205 _83095 p x)). Qed.
Lemma lem4440066 {A K : Type'} (p : type805 A K) (x : K -> A) : (term441 A K x p) = (p x).
Proof. exact (@lem4440065 (K -> A) p x). Qed.
Lemma lem4440067 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term442 A K x k s) = (term443 A K k s x).
Proof. exact (@lem4440066 A K (term444 A K k s) x). Qed.
Lemma lem4440068 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term443 A K k s f) = (term445 A K f k s).
Proof. exact (eq_refl (term443 A K k s f)). Qed.
Lemma lem4440069 {A K : Type'} (GEN_PVAR_141 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_141) = (@SETSPEC (K -> A) GEN_PVAR_141).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_141)). Qed.
Lemma lem4440070 {A K : Type'} (GEN_PVAR_141 : K -> A) (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term446 A K GEN_PVAR_141 k s f) = (term447 A K GEN_PVAR_141 f k s).
Proof. exact (MK_COMB (@lem4440069 A K GEN_PVAR_141) (@lem4440068 A K f k s)). Qed.
Lemma lem4440071 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4440072 {A K : Type'} (GEN_PVAR_141 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term448 A K GEN_PVAR_141 k s f) = (term449 A K GEN_PVAR_141 k s f).
Proof. exact (MK_COMB (@lem4440070 A K GEN_PVAR_141 f k s) (@lem4440071 A K f)). Qed.
Lemma lem4440073 {A K : Type'} (GEN_PVAR_141 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term450 A K GEN_PVAR_141 k s) = (term451 A K GEN_PVAR_141 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4440072 A K GEN_PVAR_141 k s f)). Qed.
Lemma lem4440074 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4440075 {A K : Type'} (GEN_PVAR_141 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term452 A K GEN_PVAR_141 k s) = (term453 A K GEN_PVAR_141 k s).
Proof. exact (MK_COMB (@lem4440074 A K) (@lem4440073 A K GEN_PVAR_141 k s)). Qed.
Lemma lem4440076 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term454 A K k s) = (term455 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_141 : K -> A => @lem4440075 A K GEN_PVAR_141 k s)). Qed.
Lemma lem4440077 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4440078 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term456 A K k s) = (term351 A K k s).
Proof. exact (MK_COMB (@lem4440077 A K) (@lem4440076 A K k s)). Qed.
Lemma lem4440079 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4440080 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term442 A K x k s) = (term440 A K x k s).
Proof. exact (MK_COMB (@lem4440079 A K x) (@lem4440078 A K k s)). Qed.
Lemma lem4440081 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4440082 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term457 A K x k s) = (term458 A K x k s).
Proof. exact (MK_COMB (@lem4440081) (@lem4440080 A K x k s)). Qed.
Lemma lem4440083 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term443 A K k s x) = (term445 A K x k s).
Proof. exact (eq_refl (term443 A K k s x)). Qed.
Lemma lem4440084 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : ((term442 A K x k s) = (term443 A K k s x)) = ((term440 A K x k s) = (term445 A K x k s)).
Proof. exact (MK_COMB (@lem4440082 A K x k s) (@lem4440083 A K x k s)). Qed.
Lemma lem4440085 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term440 A K x k s) = (term445 A K x k s).
Proof. exact (EQ_MP (@lem4440084 A K x k s) (@lem4440067 A K k s x)). Qed.
Lemma lem4440090 {A K : Type'} (x : A) (i : K) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) : (term535 A K x i x' k s) = (term536 A K x i x' k s).
Proof. exact (MK_COMB (@lem4440063 A K x x' i) (@lem4440085 A K x' k s)). Qed.
Lemma lem4440093 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term537 A K x i k s) = (term538 A K x i k s).
Proof. exact (fun_ext (fun x' : K -> A => @lem4440090 A K x i x' k s)). Qed.
Lemma lem4440094 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4440095 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term532 A K x i k s) = (term539 A K x i k s).
Proof. exact (MK_COMB (@lem4440094 A K) (@lem4440093 A K x i k s)). Qed.
Lemma lem4440100 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term477 A K x i k s) = (term539 A K x i k s).
Proof. exact (TRANS (@lem4440036 A K x i k s) (@lem4440095 A K x i k s)). Qed.
Lemma lem4440101 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) : (term539 A K x i k s) = (term477 A K x i k s).
Proof. exact (SYM (@lem4440100 A K x i k s)). Qed.
Lemma lem4440114 {A B : Type'} (f : A -> B) (y : A) : (term413 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4440115 {A K : Type'} (f : K -> A) (y : K) : (term540 A K f y) = (f y).
Proof. exact (@lem4440114 K A f y). Qed.
Lemma lem4440116 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (term541 A K x k z i) = (term542 A K x k z i).
Proof. exact (@lem4440115 A K (term543 A K i x k z) i). Qed.
Lemma lem4440117 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (j : K) : (term544 A K i x k z j) = (term545 A K i x k z j).
Proof. exact (eq_refl (term544 A K i x k z j)). Qed.
Lemma lem4440118 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term546 A K i x k z) = (term543 A K i x k z).
Proof. exact (fun_ext (fun j : K => @lem4440117 A K i x k z j)). Qed.
Lemma lem4440119 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4440120 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (term541 A K x k z i) = (term542 A K x k z i).
Proof. exact (MK_COMB (@lem4440118 A K i x k z) (@lem4440119 K i)). Qed.
Lemma lem4440121 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4440122 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (term547 A K x k z i) = (term548 A K x k z i).
Proof. exact (MK_COMB (@lem4440121 A) (@lem4440120 A K x k z i)). Qed.
Lemma lem4440123 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (term542 A K x k z i) = (term549 A K x k z i).
Proof. exact (eq_refl (term542 A K x k z i)). Qed.
Lemma lem4440124 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : ((term541 A K x k z i) = (term542 A K x k z i)) = ((term542 A K x k z i) = (term549 A K x k z i)).
Proof. exact (MK_COMB (@lem4440122 A K x k z i) (@lem4440123 A K x k z i)). Qed.
Lemma lem4440125 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (term542 A K x k z i) = (term549 A K x k z i).
Proof. exact (EQ_MP (@lem4440124 A K x k z i) (@lem4440116 A K x k z i)). Qed.
Lemma lem4440127 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term550 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem4440128 {A K : Type'} (x : K) (z : A) (y : A) : (term550 A K x y z) = y.
Proof. exact (@lem4440127 A K x z y). Qed.
Lemma lem4440129 {A K : Type'} (k : K -> Prop) (z : K -> A) (i : K) (x : A) : (term549 A K x k z i) = x.
Proof. exact (@lem4440128 A K i (term551 A K k z i) x). Qed.
Lemma lem4440130 {A K : Type'} (k : K -> Prop) (z : K -> A) (i : K) (x : A) : (term542 A K x k z i) = x.
Proof. exact (TRANS (@lem4440125 A K x k z i) (@lem4440129 A K k z i x)). Qed.
Lemma lem4440131 {A : Type'} (x : A) : (@eq A x) = (@eq A x).
Proof. exact (eq_refl (@eq A x)). Qed.
Lemma lem4440132 {A K : Type'} (k : K -> Prop) (z : K -> A) (i : K) (x : A) : (x = (term542 A K x k z i)) = (x = x).
Proof. exact (MK_COMB (@lem4440131 A x) (@lem4440130 A K k z i x)). Qed.
Lemma lem4440134 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4440135 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem4440134 A x). Qed.
Lemma lem4440136 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (x = (term542 A K x k z i)) = True.
Proof. exact (TRANS (@lem4440132 A K k z i x) (@lem4440135 A x)). Qed.
Lemma lem4440137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4440138 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i : K) : (term552 A K x k z i) = (and True).
Proof. exact (MK_COMB (@lem4440137) (@lem4440136 A K x k z i)). Qed.
Lemma lem4440144 {A B : Type'} (f : A -> B) (y : A) : (term413 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4440145 {A K : Type'} (f : K -> A) (y : K) : (term540 A K f y) = (f y).
Proof. exact (@lem4440144 K A f y). Qed.
Lemma lem4440146 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term553 A K i x k z i') = (term544 A K i x k z i').
Proof. exact (@lem4440145 A K (term543 A K i x k z) i'). Qed.
Lemma lem4440147 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (j : K) : (term544 A K i x k z j) = (term545 A K i x k z j).
Proof. exact (eq_refl (term544 A K i x k z j)). Qed.
Lemma lem4440148 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) : (term546 A K i x k z) = (term543 A K i x k z).
Proof. exact (fun_ext (fun j : K => @lem4440147 A K i x k z j)). Qed.
Lemma lem4440149 {K : Type'} (i' : K) : i' = i'.
Proof. exact (eq_refl i'). Qed.
Lemma lem4440150 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term553 A K i x k z i') = (term544 A K i x k z i').
Proof. exact (MK_COMB (@lem4440148 A K i x k z) (@lem4440149 K i')). Qed.
Lemma lem4440151 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4440152 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term554 A K i x k z i') = (term555 A K i x k z i').
Proof. exact (MK_COMB (@lem4440151 A) (@lem4440150 A K i x k z i')). Qed.
Lemma lem4440153 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term544 A K i x k z i') = (term545 A K i x k z i').
Proof. exact (eq_refl (term544 A K i x k z i')). Qed.
Lemma lem4440154 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : ((term553 A K i x k z i') = (term544 A K i x k z i')) = ((term544 A K i x k z i') = (term545 A K i x k z i')).
Proof. exact (MK_COMB (@lem4440152 A K i x k z i') (@lem4440153 A K i x k z i')). Qed.
Lemma lem4440155 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term544 A K i x k z i') = (term545 A K i x k z i').
Proof. exact (EQ_MP (@lem4440154 A K i x k z i') (@lem4440146 A K i x k z i')). Qed.
Lemma lem4440160 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4440161 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term556 A K i x k z i') = (term557 A K i x k z i').
Proof. exact (MK_COMB (@lem4440160 A) (@lem4440155 A K i x k z i')). Qed.
Lemma lem4440162 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i' : K) : (term383 A K k s i') = (term383 A K k s i').
Proof. exact (eq_refl (term383 A K k s i')). Qed.
Lemma lem4440163 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (i' : K) : (term558 A K i x z k s i') = (term559 A K i x z k s i').
Proof. exact (MK_COMB (@lem4440161 A K i x k z i') (@lem4440162 A K k s i')). Qed.
Lemma lem4440164 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term560 A K i x z k s) = (term561 A K i x z k s).
Proof. exact (fun_ext (fun i' : K => @lem4440163 A K i x z k s i')). Qed.
Lemma lem4440165 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4440166 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term562 A K i x z k s) = (term563 A K i x z k s).
Proof. exact (MK_COMB (@lem4440165 K) (@lem4440164 A K i x z k s)). Qed.
Lemma lem4440171 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term564 A K i x z k s) = (term565 A K i x z k s).
Proof. exact (MK_COMB (@lem4440138 A K x k z i) (@lem4440166 A K i x z k s)). Qed.
Lemma lem4440173 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4440174 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term565 A K i x z k s) = (term563 A K i x z k s).
Proof. exact (@lem4440173 (term563 A K i x z k s)). Qed.
Lemma lem4440183 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term564 A K i x z k s) = (term563 A K i x z k s).
Proof. exact (TRANS (@lem4440171 A K i x z k s) (@lem4440174 A K i x z k s)). Qed.
Lemma lem4440184 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term563 A K i x z k s) = (term564 A K i x z k s).
Proof. exact (SYM (@lem4440183 A K i x z k s)). Qed.
Lemma lem4440186 (p : Prop) : p = (term58 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4440187 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term563 A K i x z k s) = (term566 A K i x z k s).
Proof. exact (@lem4440186 (term563 A K i x z k s)). Qed.
Lemma lem4440188 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term566 A K i x z k s) = (term563 A K i x z k s).
Proof. exact (SYM (@lem4440187 A K i x z k s)). Qed.
Lemma lem4440189 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term567 A K i x z k s) : term567 A K i x z k s.
Proof. exact (h1). Qed.
Lemma lem4440190 {A : Type'} : term568 A.
Proof. exact (@lem3205876 A). Qed.
Lemma lem4440191 {K : Type'} : term568 K.
Proof. exact (@lem3205876 K). Qed.
Lemma lem4440197 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term569 A K i x z k s) : term569 A K i x z k s.
Proof. exact (h1). Qed.
Lemma lem4440198 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : term570 A K i x z k s.
Proof. exact (fun h0 : term569 A K i x z k s => @lem4440197 A K i x z k s h0). Qed.
Lemma lem4440199 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term570 A K i x z k s) : term570 A K i x z k s.
Proof. exact (h1). Qed.
Lemma lem4440200 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term569 A K i x z k s) : term569 A K i x z k s.
Proof. exact (h1). Qed.
Lemma lem4440201 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term570 A K i x z k s) (h2 : term569 A K i x z k s) : term569 A K i x z k s.
Proof. exact (@lem4440199 A K i x z k s h1 (@lem4440200 A K i x z k s h2)). Qed.
Lemma lem4440202 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term569 A K i x z k s) : term571 A K i x z k s.
Proof. exact (fun h0 : term570 A K i x z k s => @lem4440201 A K i x z k s h0 h1). Qed.
Lemma lem4440203 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term570 A K i x z k s) : term570 A K i x z k s.
Proof. exact (h1). Qed.
Lemma lem4440204 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term570 A K i x z k s) (h2 : term569 A K i x z k s) : term569 A K i x z k s.
Proof. exact (@lem4440202 A K i x z k s h2 (@lem4440203 A K i x z k s h1)). Qed.
Lemma lem4440205 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (h1 : term570 A K i x z k s) : term570 A K i x z k s.
Proof. exact (fun h0 : term569 A K i x z k s => @lem4440204 A K i x z k s h1 h0). Qed.
Lemma lem4440206 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : term572 A K i x z k s.
Proof. exact (fun h0 : term570 A K i x z k s => @lem4440205 A K i x z k s h0). Qed.
Lemma lem4440209 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : term570 A K i x z k s.
Proof. exact (@lem4440206 A K i x z k s (@lem4440198 A K i x z k s)). Qed.
Lemma lem4440210 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : term570 A K i x z k s.
Proof. exact (@lem4440209 A K i x z k s). Qed.
Lemma lem4440258 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4440259 {K : Type'} : (term573 K) = (term574 K).
Proof. exact (@lem4440258 (term568 K)). Qed.
Lemma lem4440268 {A : Type'} : (term575 A) = (term575 A).
Proof. exact (eq_refl (term575 A)). Qed.
Lemma lem4440269 {A K : Type'} : (term576 A K) = (term577 A K).
Proof. exact (MK_COMB (@lem4440268 A) (@lem4440259 K)). Qed.
Lemma lem4440272 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term578 A K i x z k s) = (term578 A K i x z k s).
Proof. exact (eq_refl (term578 A K i x z k s)). Qed.
Lemma lem4440273 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term579 A K i x z k s) = (term580 A K i x z k s).
Proof. exact (MK_COMB (@lem4440272 A K i x z k s) (@lem4440269 A K)). Qed.
Lemma lem4440276 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term524 A K k z s) = (term524 A K k z s).
Proof. exact (eq_refl (term524 A K k z s)). Qed.
Lemma lem4440277 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term581 A K i x z k s) = (term582 A K i x z k s).
Proof. exact (MK_COMB (@lem4440276 A K k z s) (@lem4440273 A K i x z k s)). Qed.
Lemma lem4440280 {A K : Type'} (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) : (term583 A K x k s i) = (term583 A K x k s i).
Proof. exact (eq_refl (term583 A K x k s i)). Qed.
Lemma lem4440281 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term569 A K i x z k s) = (term584 A K i x z k s).
Proof. exact (MK_COMB (@lem4440280 A K x k s i) (@lem4440277 A K i x z k s)). Qed.
Lemma lem4440284 {A K : Type'} (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term585 A K x z k s) = (term586 A K x z k s).
Proof. exact (fun_ext (fun i : K => @lem4440281 A K i x z k s)). Qed.
Lemma lem4440285 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4440286 {A K : Type'} (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term587 A K x z k s) = (term588 A K x z k s).
Proof. exact (MK_COMB (@lem4440285 K) (@lem4440284 A K x z k s)). Qed.
Lemma lem4440291 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term589 A K z k s) = (term590 A K z k s).
Proof. exact (fun_ext (fun x : A => @lem4440286 A K x z k s)). Qed.
Lemma lem4440292 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4440293 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term591 A K z k s) = (term592 A K z k s).
Proof. exact (MK_COMB (@lem4440292 A) (@lem4440291 A K z k s)). Qed.
Lemma lem4440298 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term593 A K k s) = (term594 A K k s).
Proof. exact (fun_ext (fun z : K -> A => @lem4440293 A K z k s)). Qed.
Lemma lem4440299 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4440300 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term595 A K k s) = (term596 A K k s).
Proof. exact (MK_COMB (@lem4440299 A K) (@lem4440298 A K k s)). Qed.
Lemma lem4440305 {A K : Type'} (s : type1470 A K) : (term597 A K s) = (term598 A K s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4440300 A K k s)). Qed.
Lemma lem4440306 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4440307 {A K : Type'} (s : type1470 A K) : (term599 A K s) = (term600 A K s).
Proof. exact (MK_COMB (@lem4440306 K) (@lem4440305 A K s)). Qed.
Lemma lem4440312 {A K : Type'} : (term601 A K) = (term602 A K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4440307 A K s)). Qed.
Lemma lem4440313 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4440322 {A K : Type'} : (term603 A K) = (term604 A K).
Proof. exact (MK_COMB (@lem4440313 A K) (@lem4440312 A K)). Qed.
Lemma lem4440326 {K : Type'} (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (@IN K i k) = False.
Proof. exact (h1). Qed.
Lemma lem4440327 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4440328 {A K : Type'} (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (term605 A K i k) = (@COND (A -> Prop) False).
Proof. exact (MK_COMB (@lem4440327 A) (@lem4440326 K i k h1)). Qed.
Lemma lem4440329 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4440330 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (term606 A K k s i) = (term607 A K s i).
Proof. exact (MK_COMB (@lem4440328 A K i k h1) (@lem4440329 A K s i)). Qed.
Lemma lem4440331 {A : Type'} : (@INSERT A (@ARB A) (@EMPTY A)) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440332 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (term383 A K k s i) = (term608 A K s i).
Proof. exact (MK_COMB (@lem4440330 A K s i k h1) (@lem4440331 A)). Qed.
Lemma lem4440334 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4440335 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (@COND (A -> Prop) False t1 t2) = t2.
Proof. exact (@lem4440334 (A -> Prop) t1 t2). Qed.
Lemma lem4440336 {A K : Type'} (s : type1470 A K) (i : K) : (term608 A K s i) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (@lem4440335 A (s i) (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440337 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (term383 A K k s i) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (TRANS (@lem4440332 A K s i k h1) (@lem4440336 A K s i)). Qed.
Lemma lem4440338 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4440339 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (term397 A K x k s i) = (term609 A x).
Proof. exact (MK_COMB (@lem4440338 A x) (@lem4440337 A K s i k h1)). Qed.
Lemma lem4440340 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4440341 {A K : Type'} (s : type1470 A K) (x : A) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (term583 A K x k s i) = (term610 A x).
Proof. exact (MK_COMB (@lem4440340) (@lem4440339 A K s x i k h1)). Qed.
Lemma lem4440396 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term582 A K i x z k s) = (term582 A K i x z k s).
Proof. exact (eq_refl (term582 A K i x z k s)). Qed.
Lemma lem4440397 {A K : Type'} (x : A) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (term584 A K i x z k s) = (term611 A K i x z k s).
Proof. exact (MK_COMB (@lem4440341 A K s x i k h1) (@lem4440396 A K i x z k s)). Qed.
Lemma lem4440400 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : term612 A K i x z k s.
Proof. exact (fun h0 : (@IN K i k) = False => @lem4440397 A K x z s i k h0). Qed.
Lemma lem4440402 {K : Type'} (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (@IN K i k) = True.
Proof. exact (h1). Qed.
Lemma lem4440403 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4440404 {A K : Type'} (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (term605 A K i k) = (@COND (A -> Prop) True).
Proof. exact (MK_COMB (@lem4440403 A) (@lem4440402 K i k h1)). Qed.
Lemma lem4440405 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4440406 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (term606 A K k s i) = (term613 A K s i).
Proof. exact (MK_COMB (@lem4440404 A K i k h1) (@lem4440405 A K s i)). Qed.
Lemma lem4440407 {A : Type'} : (@INSERT A (@ARB A) (@EMPTY A)) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440408 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (term383 A K k s i) = (term614 A K s i).
Proof. exact (MK_COMB (@lem4440406 A K s i k h1) (@lem4440407 A)). Qed.
Lemma lem4440410 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4440411 {A : Type'} (t2 : A -> Prop) (t1 : A -> Prop) : (@COND (A -> Prop) True t1 t2) = t1.
Proof. exact (@lem4440410 (A -> Prop) t2 t1). Qed.
Lemma lem4440412 {A K : Type'} (s : type1470 A K) (i : K) : (term614 A K s i) = (s i).
Proof. exact (@lem4440411 A (@INSERT A (@ARB A) (@EMPTY A)) (s i)). Qed.
Lemma lem4440413 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (term383 A K k s i) = (s i).
Proof. exact (TRANS (@lem4440408 A K s i k h1) (@lem4440412 A K s i)). Qed.
Lemma lem4440414 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4440415 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (term397 A K x k s i) = (term35 A K x s i).
Proof. exact (MK_COMB (@lem4440414 A x) (@lem4440413 A K s i k h1)). Qed.
Lemma lem4440416 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4440417 {A K : Type'} (x : A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (term583 A K x k s i) = (term615 A K x s i).
Proof. exact (MK_COMB (@lem4440416) (@lem4440415 A K x s i k h1)). Qed.
Lemma lem4440472 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term582 A K i x z k s) = (term582 A K i x z k s).
Proof. exact (eq_refl (term582 A K i x z k s)). Qed.
Lemma lem4440473 {A K : Type'} (x : A) (z : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (term584 A K i x z k s) = (term616 A K i x z k s).
Proof. exact (MK_COMB (@lem4440417 A K x s i k h1) (@lem4440472 A K i x z k s)). Qed.
Lemma lem4440476 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : term617 A K i x z k s.
Proof. exact (fun h0 : (@IN K i k) = True => @lem4440473 A K x z s i k h0). Qed.
Lemma lem4440477 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : term618 A K i x z k s.
Proof. exact (conj (@lem4440400 A K i x z k s) (@lem4440476 A K i x z k s)). Qed.
Lemma lem4440479 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term619 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4440480 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : term620 A K i x z k s.
Proof. exact (@lem4440479 (term584 A K i x z k s) (term616 A K i x z k s) (@IN K i k) (term611 A K i x z k s)). Qed.
Lemma lem4440495 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term584 A K i x z k s) = (term621 A K i x z k s).
Proof. exact (@lem4440480 A K i x z k s (@lem4440477 A K i x z k s)). Qed.
Lemma lem4440500 {K : Type'} (x : K) (y : K) : ((term622 K x y) = (x = y)) = ((term622 K x y) = (x = y)).
Proof. exact (eq_refl ((term622 K x y) = (x = y))). Qed.
Lemma lem4440501 {K : Type'} (x : K) : (term623 K x) = (term623 K x).
Proof. exact (fun_ext (fun y : K => @lem4440500 K x y)). Qed.
Lemma lem4440502 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4440503 {K : Type'} (x : K) : (term624 K x) = (term624 K x).
Proof. exact (MK_COMB (@lem4440502 K) (@lem4440501 K x)). Qed.
Lemma lem4440504 {K : Type'} : (term625 K) = (term625 K).
Proof. exact (fun_ext (fun x : K => @lem4440503 K x)). Qed.
Lemma lem4440505 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4440506 {K : Type'} : (term568 K) = (term568 K).
Proof. exact (MK_COMB (@lem4440505 K) (@lem4440504 K)). Qed.
Lemma lem4440507 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4440508 {K : Type'} : (term574 K) = (term574 K).
Proof. exact (MK_COMB (@lem4440507) (@lem4440506 K)). Qed.
Lemma lem4440513 {A : Type'} (x : A) (y : A) : ((term622 A x y) = (x = y)) = ((term622 A x y) = (x = y)).
Proof. exact (eq_refl ((term622 A x y) = (x = y))). Qed.
Lemma lem4440514 {A : Type'} (x : A) : (term623 A x) = (term623 A x).
Proof. exact (fun_ext (fun y : A => @lem4440513 A x y)). Qed.
Lemma lem4440515 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4440516 {A : Type'} (x : A) : (term624 A x) = (term624 A x).
Proof. exact (MK_COMB (@lem4440515 A) (@lem4440514 A x)). Qed.
Lemma lem4440517 {A : Type'} : (term625 A) = (term625 A).
Proof. exact (fun_ext (fun x : A => @lem4440516 A x)). Qed.
Lemma lem4440518 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4440519 {A : Type'} : (term568 A) = (term568 A).
Proof. exact (MK_COMB (@lem4440518 A) (@lem4440517 A)). Qed.
Lemma lem4440520 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4440521 {A : Type'} : (term575 A) = (term575 A).
Proof. exact (MK_COMB (@lem4440520) (@lem4440519 A)). Qed.
Lemma lem4440522 {A K : Type'} : (term577 A K) = (term577 A K).
Proof. exact (MK_COMB (@lem4440521 A) (@lem4440508 K)). Qed.
Lemma lem4440526 {K : Type'} (i' : K) (i : K) (h1 : (i' = i) = False) : (i' = i) = False.
Proof. exact (h1). Qed.
Lemma lem4440527 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4440528 {A K : Type'} (i' : K) (i : K) (h1 : (i' = i) = False) : (term626 A K i' i) = (@COND A False).
Proof. exact (MK_COMB (@lem4440527 A) (@lem4440526 K i' i h1)). Qed.
Lemma lem4440529 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4440530 {A K : Type'} (x : A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term627 A K i' i x) = (@COND A False x).
Proof. exact (MK_COMB (@lem4440528 A K i' i h1) (@lem4440529 A x)). Qed.
Lemma lem4440531 {A K : Type'} (k : K -> Prop) (z : K -> A) (i' : K) : (term551 A K k z i') = (term551 A K k z i').
Proof. exact (eq_refl (term551 A K k z i')). Qed.
Lemma lem4440532 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term545 A K i x k z i') = (term628 A K x k z i').
Proof. exact (MK_COMB (@lem4440530 A K x i' i h1) (@lem4440531 A K k z i')). Qed.
Lemma lem4440534 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4440535 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4440534 A t1 t2). Qed.
Lemma lem4440536 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term628 A K x k z i') = (term551 A K k z i').
Proof. exact (@lem4440535 A x (term551 A K k z i')). Qed.
Lemma lem4440537 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term545 A K i x k z i') = (term551 A K k z i').
Proof. exact (TRANS (@lem4440532 A K x k z i' i h1) (@lem4440536 A K x k z i')). Qed.
Lemma lem4440538 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4440539 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term557 A K i x k z i') = (term629 A K k z i').
Proof. exact (MK_COMB (@lem4440538 A) (@lem4440537 A K x k z i' i h1)). Qed.
Lemma lem4440540 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i' : K) : (term383 A K k s i') = (term383 A K k s i').
Proof. exact (eq_refl (term383 A K k s i')). Qed.
Lemma lem4440541 {A K : Type'} (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = False) : (term559 A K i x z k s i') = (term630 A K z k s i').
Proof. exact (MK_COMB (@lem4440539 A K x k z i' i h1) (@lem4440540 A K k s i')). Qed.
Lemma lem4440542 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (i' : K) : term631 A K i x z k s i'.
Proof. exact (fun h0 : (i' = i) = False => @lem4440541 A K x z k s i' i h0). Qed.
Lemma lem4440544 {K : Type'} (i' : K) (i : K) (h1 : (i' = i) = True) : (i' = i) = True.
Proof. exact (h1). Qed.
Lemma lem4440545 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4440546 {A K : Type'} (i' : K) (i : K) (h1 : (i' = i) = True) : (term626 A K i' i) = (@COND A True).
Proof. exact (MK_COMB (@lem4440545 A) (@lem4440544 K i' i h1)). Qed.
Lemma lem4440547 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4440548 {A K : Type'} (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term627 A K i' i x) = (@COND A True x).
Proof. exact (MK_COMB (@lem4440546 A K i' i h1) (@lem4440547 A x)). Qed.
Lemma lem4440549 {A K : Type'} (k : K -> Prop) (z : K -> A) (i' : K) : (term551 A K k z i') = (term551 A K k z i').
Proof. exact (eq_refl (term551 A K k z i')). Qed.
Lemma lem4440550 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term545 A K i x k z i') = (term632 A K x k z i').
Proof. exact (MK_COMB (@lem4440548 A K x i' i h1) (@lem4440549 A K k z i')). Qed.
Lemma lem4440552 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4440553 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4440552 A t2 t1). Qed.
Lemma lem4440554 {A K : Type'} (k : K -> Prop) (z : K -> A) (i' : K) (x : A) : (term632 A K x k z i') = x.
Proof. exact (@lem4440553 A (term551 A K k z i') x). Qed.
Lemma lem4440555 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term545 A K i x k z i') = x.
Proof. exact (TRANS (@lem4440550 A K x k z i' i h1) (@lem4440554 A K k z i' x)). Qed.
Lemma lem4440556 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4440557 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term557 A K i x k z i') = (@IN A x).
Proof. exact (MK_COMB (@lem4440556 A) (@lem4440555 A K k z x i' i h1)). Qed.
Lemma lem4440558 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i' : K) : (term383 A K k s i') = (term383 A K k s i').
Proof. exact (eq_refl (term383 A K k s i')). Qed.
Lemma lem4440559 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = True) : (term559 A K i x z k s i') = (term397 A K x k s i').
Proof. exact (MK_COMB (@lem4440557 A K k z x i' i h1) (@lem4440558 A K k s i')). Qed.
Lemma lem4440560 {A K : Type'} (i : K) (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i' : K) : term633 A K i z x k s i'.
Proof. exact (fun h0 : (i' = i) = True => @lem4440559 A K z x k s i' i h0). Qed.
Lemma lem4440561 {A K : Type'} (i : K) (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i' : K) : term634 A K i z x k s i'.
Proof. exact (conj (@lem4440542 A K i x z k s i') (@lem4440560 A K i z x k s i')). Qed.
Lemma lem4440563 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term619 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4440564 {A K : Type'} (x : A) (i : K) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (i' : K) : term635 A K x i z k s i'.
Proof. exact (@lem4440563 (term559 A K i x z k s i') (term397 A K x k s i') (i' = i) (term630 A K z k s i')). Qed.
Lemma lem4440579 {A K : Type'} (x : A) (i : K) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (i' : K) : (term559 A K i x z k s i') = (term636 A K x i z k s i').
Proof. exact (@lem4440564 A K x i z k s i' (@lem4440561 A K i z x k s i')). Qed.
Lemma lem4440585 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (@IN K i' k) = False.
Proof. exact (h1). Qed.
Lemma lem4440586 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4440587 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term605 A K i' k) = (@COND (A -> Prop) False).
Proof. exact (MK_COMB (@lem4440586 A) (@lem4440585 K i' k h1)). Qed.
Lemma lem4440588 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4440589 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term606 A K k s i') = (term607 A K s i').
Proof. exact (MK_COMB (@lem4440587 A K i' k h1) (@lem4440588 A K s i')). Qed.
Lemma lem4440590 {A : Type'} : (@INSERT A (@ARB A) (@EMPTY A)) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440591 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term383 A K k s i') = (term608 A K s i').
Proof. exact (MK_COMB (@lem4440589 A K s i' k h1) (@lem4440590 A)). Qed.
Lemma lem4440593 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4440594 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (@COND (A -> Prop) False t1 t2) = t2.
Proof. exact (@lem4440593 (A -> Prop) t1 t2). Qed.
Lemma lem4440595 {A K : Type'} (s : type1470 A K) (i' : K) : (term608 A K s i') = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (@lem4440594 A (s i') (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440596 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term383 A K k s i') = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (TRANS (@lem4440591 A K s i' k h1) (@lem4440595 A K s i')). Qed.
Lemma lem4440597 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4440598 {A K : Type'} (s : type1470 A K) (x : A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term397 A K x k s i') = (term609 A x).
Proof. exact (MK_COMB (@lem4440597 A x) (@lem4440596 A K s i' k h1)). Qed.
Lemma lem4440599 {K : Type'} (i' : K) (i : K) : (term637 K i' i) = (term637 K i' i).
Proof. exact (eq_refl (term637 K i' i)). Qed.
Lemma lem4440600 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term638 A K i x k s i') = (term639 A K i' i x).
Proof. exact (MK_COMB (@lem4440599 K i' i) (@lem4440598 A K s x i' k h1)). Qed.
Lemma lem4440603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4440604 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term640 A K i x k s i') = (term641 A K i' i x).
Proof. exact (MK_COMB (@lem4440603) (@lem4440600 A K s i x i' k h1)). Qed.
Lemma lem4440608 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (@IN K i' k) = False.
Proof. exact (h1). Qed.
Lemma lem4440609 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4440610 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term642 A K i' k) = (@COND A False).
Proof. exact (MK_COMB (@lem4440609 A) (@lem4440608 K i' k h1)). Qed.
Lemma lem4440611 {A K : Type'} (z : K -> A) (i' : K) : (z i') = (z i').
Proof. exact (eq_refl (z i')). Qed.
Lemma lem4440612 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term643 A K k z i') = (term644 A K z i').
Proof. exact (MK_COMB (@lem4440610 A K i' k h1) (@lem4440611 A K z i')). Qed.
Lemma lem4440613 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4440614 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term551 A K k z i') = (term645 A K z i').
Proof. exact (MK_COMB (@lem4440612 A K z i' k h1) (@lem4440613 A)). Qed.
Lemma lem4440616 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4440617 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4440616 A t1 t2). Qed.
Lemma lem4440618 {A K : Type'} (z : K -> A) (i' : K) : (term645 A K z i') = (@ARB A).
Proof. exact (@lem4440617 A (z i') (@ARB A)). Qed.
Lemma lem4440619 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term551 A K k z i') = (@ARB A).
Proof. exact (TRANS (@lem4440614 A K z i' k h1) (@lem4440618 A K z i')). Qed.
Lemma lem4440620 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4440621 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term629 A K k z i') = (@IN A (@ARB A)).
Proof. exact (MK_COMB (@lem4440620 A) (@lem4440619 A K z i' k h1)). Qed.
Lemma lem4440623 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (@IN K i' k) = False.
Proof. exact (h1). Qed.
Lemma lem4440624 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4440625 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term605 A K i' k) = (@COND (A -> Prop) False).
Proof. exact (MK_COMB (@lem4440624 A) (@lem4440623 K i' k h1)). Qed.
Lemma lem4440626 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4440627 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term606 A K k s i') = (term607 A K s i').
Proof. exact (MK_COMB (@lem4440625 A K i' k h1) (@lem4440626 A K s i')). Qed.
Lemma lem4440628 {A : Type'} : (@INSERT A (@ARB A) (@EMPTY A)) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440629 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term383 A K k s i') = (term608 A K s i').
Proof. exact (MK_COMB (@lem4440627 A K s i' k h1) (@lem4440628 A)). Qed.
Lemma lem4440631 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4440632 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (@COND (A -> Prop) False t1 t2) = t2.
Proof. exact (@lem4440631 (A -> Prop) t1 t2). Qed.
Lemma lem4440633 {A K : Type'} (s : type1470 A K) (i' : K) : (term608 A K s i') = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (@lem4440632 A (s i') (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440634 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term383 A K k s i') = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (TRANS (@lem4440629 A K s i' k h1) (@lem4440633 A K s i')). Qed.
Lemma lem4440635 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term630 A K z k s i') = (term646 A).
Proof. exact (MK_COMB (@lem4440621 A K z i' k h1) (@lem4440634 A K s i' k h1)). Qed.
Lemma lem4440636 {K : Type'} (i' : K) (i : K) : (term647 K i' i) = (term647 K i' i).
Proof. exact (eq_refl (term647 K i' i)). Qed.
Lemma lem4440637 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term648 A K i z k s i') = (term649 A K i' i).
Proof. exact (MK_COMB (@lem4440636 K i' i) (@lem4440635 A K z s i' k h1)). Qed.
Lemma lem4440640 {A K : Type'} (z : K -> A) (s : type1470 A K) (x : A) (i : K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term636 A K x i z k s i') = (term650 A K x i' i).
Proof. exact (MK_COMB (@lem4440604 A K s i x i' k h1) (@lem4440637 A K z s i i' k h1)). Qed.
Lemma lem4440643 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) (x : A) (i' : K) (i : K) : term651 A K z k s x i' i.
Proof. exact (fun h0 : (@IN K i' k) = False => @lem4440640 A K z s x i i' k h0). Qed.
Lemma lem4440647 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (@IN K i' k) = True.
Proof. exact (h1). Qed.
Lemma lem4440648 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4440649 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term605 A K i' k) = (@COND (A -> Prop) True).
Proof. exact (MK_COMB (@lem4440648 A) (@lem4440647 K i' k h1)). Qed.
Lemma lem4440650 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4440651 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term606 A K k s i') = (term613 A K s i').
Proof. exact (MK_COMB (@lem4440649 A K i' k h1) (@lem4440650 A K s i')). Qed.
Lemma lem4440652 {A : Type'} : (@INSERT A (@ARB A) (@EMPTY A)) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440653 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term383 A K k s i') = (term614 A K s i').
Proof. exact (MK_COMB (@lem4440651 A K s i' k h1) (@lem4440652 A)). Qed.
Lemma lem4440655 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4440656 {A : Type'} (t2 : A -> Prop) (t1 : A -> Prop) : (@COND (A -> Prop) True t1 t2) = t1.
Proof. exact (@lem4440655 (A -> Prop) t2 t1). Qed.
Lemma lem4440657 {A K : Type'} (s : type1470 A K) (i' : K) : (term614 A K s i') = (s i').
Proof. exact (@lem4440656 A (@INSERT A (@ARB A) (@EMPTY A)) (s i')). Qed.
Lemma lem4440658 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term383 A K k s i') = (s i').
Proof. exact (TRANS (@lem4440653 A K s i' k h1) (@lem4440657 A K s i')). Qed.
Lemma lem4440659 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4440660 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term397 A K x k s i') = (term35 A K x s i').
Proof. exact (MK_COMB (@lem4440659 A x) (@lem4440658 A K s i' k h1)). Qed.
Lemma lem4440661 {K : Type'} (i' : K) (i : K) : (term637 K i' i) = (term637 K i' i).
Proof. exact (eq_refl (term637 K i' i)). Qed.
Lemma lem4440662 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term638 A K i x k s i') = (term652 A K i x s i').
Proof. exact (MK_COMB (@lem4440661 K i' i) (@lem4440660 A K x s i' k h1)). Qed.
Lemma lem4440665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4440666 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term640 A K i x k s i') = (term653 A K i x s i').
Proof. exact (MK_COMB (@lem4440665) (@lem4440662 A K i x s i' k h1)). Qed.
Lemma lem4440670 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (@IN K i' k) = True.
Proof. exact (h1). Qed.
Lemma lem4440671 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4440672 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term642 A K i' k) = (@COND A True).
Proof. exact (MK_COMB (@lem4440671 A) (@lem4440670 K i' k h1)). Qed.
Lemma lem4440673 {A K : Type'} (z : K -> A) (i' : K) : (z i') = (z i').
Proof. exact (eq_refl (z i')). Qed.
Lemma lem4440674 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term643 A K k z i') = (term654 A K z i').
Proof. exact (MK_COMB (@lem4440672 A K i' k h1) (@lem4440673 A K z i')). Qed.
Lemma lem4440675 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4440676 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term551 A K k z i') = (term655 A K z i').
Proof. exact (MK_COMB (@lem4440674 A K z i' k h1) (@lem4440675 A)). Qed.
Lemma lem4440678 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4440679 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4440678 A t2 t1). Qed.
Lemma lem4440680 {A K : Type'} (z : K -> A) (i' : K) : (term655 A K z i') = (z i').
Proof. exact (@lem4440679 A (@ARB A) (z i')). Qed.
Lemma lem4440681 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term551 A K k z i') = (z i').
Proof. exact (TRANS (@lem4440676 A K z i' k h1) (@lem4440680 A K z i')). Qed.
Lemma lem4440682 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4440683 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term629 A K k z i') = (term421 A K z i').
Proof. exact (MK_COMB (@lem4440682 A) (@lem4440681 A K z i' k h1)). Qed.
Lemma lem4440685 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (@IN K i' k) = True.
Proof. exact (h1). Qed.
Lemma lem4440686 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4440687 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term605 A K i' k) = (@COND (A -> Prop) True).
Proof. exact (MK_COMB (@lem4440686 A) (@lem4440685 K i' k h1)). Qed.
Lemma lem4440688 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4440689 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term606 A K k s i') = (term613 A K s i').
Proof. exact (MK_COMB (@lem4440687 A K i' k h1) (@lem4440688 A K s i')). Qed.
Lemma lem4440690 {A : Type'} : (@INSERT A (@ARB A) (@EMPTY A)) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440691 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term383 A K k s i') = (term614 A K s i').
Proof. exact (MK_COMB (@lem4440689 A K s i' k h1) (@lem4440690 A)). Qed.
Lemma lem4440693 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4440694 {A : Type'} (t2 : A -> Prop) (t1 : A -> Prop) : (@COND (A -> Prop) True t1 t2) = t1.
Proof. exact (@lem4440693 (A -> Prop) t2 t1). Qed.
Lemma lem4440695 {A K : Type'} (s : type1470 A K) (i' : K) : (term614 A K s i') = (s i').
Proof. exact (@lem4440694 A (@INSERT A (@ARB A) (@EMPTY A)) (s i')). Qed.
Lemma lem4440696 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term383 A K k s i') = (s i').
Proof. exact (TRANS (@lem4440691 A K s i' k h1) (@lem4440695 A K s i')). Qed.
Lemma lem4440697 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term630 A K z k s i') = (term656 A K z s i').
Proof. exact (MK_COMB (@lem4440683 A K z i' k h1) (@lem4440696 A K s i' k h1)). Qed.
Lemma lem4440698 {K : Type'} (i' : K) (i : K) : (term647 K i' i) = (term647 K i' i).
Proof. exact (eq_refl (term647 K i' i)). Qed.
Lemma lem4440699 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term648 A K i z k s i') = (term657 A K i z s i').
Proof. exact (MK_COMB (@lem4440698 K i' i) (@lem4440697 A K z s i' k h1)). Qed.
Lemma lem4440702 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term636 A K x i z k s i') = (term658 A K x i z s i').
Proof. exact (MK_COMB (@lem4440666 A K i x s i' k h1) (@lem4440699 A K i z s i' k h1)). Qed.
Lemma lem4440705 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : term659 A K k x i z s i'.
Proof. exact (fun h0 : (@IN K i' k) = True => @lem4440702 A K x i z s i' k h0). Qed.
Lemma lem4440706 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : term660 A K k x i z s i'.
Proof. exact (conj (@lem4440643 A K z k s x i' i) (@lem4440705 A K k x i z s i')). Qed.
Lemma lem4440708 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term619 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4440709 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : term661 A K z s k x i' i.
Proof. exact (@lem4440708 (term636 A K x i z k s i') (term658 A K x i z s i') (@IN K i' k) (term650 A K x i' i)). Qed.
Lemma lem4440770 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term636 A K x i z k s i') = (term662 A K z s k x i' i).
Proof. exact (@lem4440709 A K z s k x i' i (@lem4440706 A K k x i z s i')). Qed.
Lemma lem4440771 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (i' : K) : (term663 A K i x z k s i') = (term663 A K i x z k s i').
Proof. exact (eq_refl (term663 A K i x z k s i')). Qed.
Lemma lem4440772 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : ((term559 A K i x z k s i') = (term636 A K x i z k s i')) = ((term559 A K i x z k s i') = (term662 A K z s k x i' i)).
Proof. exact (MK_COMB (@lem4440771 A K i x z k s i') (@lem4440770 A K z s k x i' i)). Qed.
Lemma lem4440773 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term559 A K i x z k s i') = (term662 A K z s k x i' i).
Proof. exact (EQ_MP (@lem4440772 A K z s k x i' i) (@lem4440579 A K x i z k s i')). Qed.
Lemma lem4440774 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term561 A K i x z k s) = (term664 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4440773 A K z s k x i' i)). Qed.
Lemma lem4440775 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4440776 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term563 A K i x z k s) = (term665 A K z s k x i).
Proof. exact (MK_COMB (@lem4440775 K) (@lem4440774 A K z s k x i)). Qed.
Lemma lem4440777 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4440778 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term567 A K i x z k s) = (term666 A K z s k x i).
Proof. exact (MK_COMB (@lem4440777) (@lem4440776 A K z s k x i)). Qed.
Lemma lem4440779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4440780 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term578 A K i x z k s) = (term667 A K z s k x i).
Proof. exact (MK_COMB (@lem4440779) (@lem4440778 A K z s k x i)). Qed.
Lemma lem4440781 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term580 A K i x z k s) = (term668 A K z s k x i).
Proof. exact (MK_COMB (@lem4440780 A K z s k x i) (@lem4440522 A K)). Qed.
Lemma lem4440786 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term503 A K k z s i) = (term503 A K k z s i).
Proof. exact (eq_refl (term503 A K k z s i)). Qed.
Lemma lem4440787 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term505 A K k z s) = (term505 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4440786 A K k z s i)). Qed.
Lemma lem4440788 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4440789 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term507 A K k z s) = (term507 A K k z s).
Proof. exact (MK_COMB (@lem4440788 K) (@lem4440787 A K k z s)). Qed.
Lemma lem4440790 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4440791 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term524 A K k z s) = (term524 A K k z s).
Proof. exact (MK_COMB (@lem4440790) (@lem4440789 A K k z s)). Qed.
Lemma lem4440792 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term582 A K i x z k s) = (term669 A K z s k x i).
Proof. exact (MK_COMB (@lem4440791 A K k z s) (@lem4440781 A K z s k x i)). Qed.
Lemma lem4440795 {A : Type'} (x : A) : (term610 A x) = (term610 A x).
Proof. exact (eq_refl (term610 A x)). Qed.
Lemma lem4440796 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term611 A K i x z k s) = (term670 A K z s k x i).
Proof. exact (MK_COMB (@lem4440795 A x) (@lem4440792 A K z s k x i)). Qed.
Lemma lem4440799 {K : Type'} (i : K) (k : K -> Prop) : (term671 K i k) = (term671 K i k).
Proof. exact (eq_refl (term671 K i k)). Qed.
Lemma lem4440800 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term672 A K i x z k s) = (term673 A K z s k x i).
Proof. exact (MK_COMB (@lem4440799 K i k) (@lem4440796 A K z s k x i)). Qed.
Lemma lem4440805 {K : Type'} (x : K) (y : K) : ((term622 K x y) = (x = y)) = ((term622 K x y) = (x = y)).
Proof. exact (eq_refl ((term622 K x y) = (x = y))). Qed.
Lemma lem4440806 {K : Type'} (x : K) : (term623 K x) = (term623 K x).
Proof. exact (fun_ext (fun y : K => @lem4440805 K x y)). Qed.
Lemma lem4440807 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4440808 {K : Type'} (x : K) : (term624 K x) = (term624 K x).
Proof. exact (MK_COMB (@lem4440807 K) (@lem4440806 K x)). Qed.
Lemma lem4440809 {K : Type'} : (term625 K) = (term625 K).
Proof. exact (fun_ext (fun x : K => @lem4440808 K x)). Qed.
Lemma lem4440810 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4440811 {K : Type'} : (term568 K) = (term568 K).
Proof. exact (MK_COMB (@lem4440810 K) (@lem4440809 K)). Qed.
Lemma lem4440812 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4440813 {K : Type'} : (term574 K) = (term574 K).
Proof. exact (MK_COMB (@lem4440812) (@lem4440811 K)). Qed.
Lemma lem4440818 {A : Type'} (x : A) (y : A) : ((term622 A x y) = (x = y)) = ((term622 A x y) = (x = y)).
Proof. exact (eq_refl ((term622 A x y) = (x = y))). Qed.
Lemma lem4440819 {A : Type'} (x : A) : (term623 A x) = (term623 A x).
Proof. exact (fun_ext (fun y : A => @lem4440818 A x y)). Qed.
Lemma lem4440820 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4440821 {A : Type'} (x : A) : (term624 A x) = (term624 A x).
Proof. exact (MK_COMB (@lem4440820 A) (@lem4440819 A x)). Qed.
Lemma lem4440822 {A : Type'} : (term625 A) = (term625 A).
Proof. exact (fun_ext (fun x : A => @lem4440821 A x)). Qed.
Lemma lem4440823 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4440824 {A : Type'} : (term568 A) = (term568 A).
Proof. exact (MK_COMB (@lem4440823 A) (@lem4440822 A)). Qed.
Lemma lem4440825 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4440826 {A : Type'} : (term575 A) = (term575 A).
Proof. exact (MK_COMB (@lem4440825) (@lem4440824 A)). Qed.
Lemma lem4440827 {A K : Type'} : (term577 A K) = (term577 A K).
Proof. exact (MK_COMB (@lem4440826 A) (@lem4440813 K)). Qed.
Lemma lem4440831 {K : Type'} (i' : K) (i : K) (h1 : (i' = i) = False) : (i' = i) = False.
Proof. exact (h1). Qed.
Lemma lem4440832 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4440833 {A K : Type'} (i' : K) (i : K) (h1 : (i' = i) = False) : (term626 A K i' i) = (@COND A False).
Proof. exact (MK_COMB (@lem4440832 A) (@lem4440831 K i' i h1)). Qed.
Lemma lem4440834 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4440835 {A K : Type'} (x : A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term627 A K i' i x) = (@COND A False x).
Proof. exact (MK_COMB (@lem4440833 A K i' i h1) (@lem4440834 A x)). Qed.
Lemma lem4440836 {A K : Type'} (k : K -> Prop) (z : K -> A) (i' : K) : (term551 A K k z i') = (term551 A K k z i').
Proof. exact (eq_refl (term551 A K k z i')). Qed.
Lemma lem4440837 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term545 A K i x k z i') = (term628 A K x k z i').
Proof. exact (MK_COMB (@lem4440835 A K x i' i h1) (@lem4440836 A K k z i')). Qed.
Lemma lem4440839 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4440840 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4440839 A t1 t2). Qed.
Lemma lem4440841 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) : (term628 A K x k z i') = (term551 A K k z i').
Proof. exact (@lem4440840 A x (term551 A K k z i')). Qed.
Lemma lem4440842 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term545 A K i x k z i') = (term551 A K k z i').
Proof. exact (TRANS (@lem4440837 A K x k z i' i h1) (@lem4440841 A K x k z i')). Qed.
Lemma lem4440843 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4440844 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = False) : (term557 A K i x k z i') = (term629 A K k z i').
Proof. exact (MK_COMB (@lem4440843 A) (@lem4440842 A K x k z i' i h1)). Qed.
Lemma lem4440845 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i' : K) : (term383 A K k s i') = (term383 A K k s i').
Proof. exact (eq_refl (term383 A K k s i')). Qed.
Lemma lem4440846 {A K : Type'} (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = False) : (term559 A K i x z k s i') = (term630 A K z k s i').
Proof. exact (MK_COMB (@lem4440844 A K x k z i' i h1) (@lem4440845 A K k s i')). Qed.
Lemma lem4440847 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (i' : K) : term631 A K i x z k s i'.
Proof. exact (fun h0 : (i' = i) = False => @lem4440846 A K x z k s i' i h0). Qed.
Lemma lem4440849 {K : Type'} (i' : K) (i : K) (h1 : (i' = i) = True) : (i' = i) = True.
Proof. exact (h1). Qed.
Lemma lem4440850 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4440851 {A K : Type'} (i' : K) (i : K) (h1 : (i' = i) = True) : (term626 A K i' i) = (@COND A True).
Proof. exact (MK_COMB (@lem4440850 A) (@lem4440849 K i' i h1)). Qed.
Lemma lem4440852 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4440853 {A K : Type'} (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term627 A K i' i x) = (@COND A True x).
Proof. exact (MK_COMB (@lem4440851 A K i' i h1) (@lem4440852 A x)). Qed.
Lemma lem4440854 {A K : Type'} (k : K -> Prop) (z : K -> A) (i' : K) : (term551 A K k z i') = (term551 A K k z i').
Proof. exact (eq_refl (term551 A K k z i')). Qed.
Lemma lem4440855 {A K : Type'} (x : A) (k : K -> Prop) (z : K -> A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term545 A K i x k z i') = (term632 A K x k z i').
Proof. exact (MK_COMB (@lem4440853 A K x i' i h1) (@lem4440854 A K k z i')). Qed.
Lemma lem4440857 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4440858 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4440857 A t2 t1). Qed.
Lemma lem4440859 {A K : Type'} (k : K -> Prop) (z : K -> A) (i' : K) (x : A) : (term632 A K x k z i') = x.
Proof. exact (@lem4440858 A (term551 A K k z i') x). Qed.
Lemma lem4440860 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term545 A K i x k z i') = x.
Proof. exact (TRANS (@lem4440855 A K x k z i' i h1) (@lem4440859 A K k z i' x)). Qed.
Lemma lem4440861 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4440862 {A K : Type'} (k : K -> Prop) (z : K -> A) (x : A) (i' : K) (i : K) (h1 : (i' = i) = True) : (term557 A K i x k z i') = (@IN A x).
Proof. exact (MK_COMB (@lem4440861 A) (@lem4440860 A K k z x i' i h1)). Qed.
Lemma lem4440863 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i' : K) : (term383 A K k s i') = (term383 A K k s i').
Proof. exact (eq_refl (term383 A K k s i')). Qed.
Lemma lem4440864 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i' : K) (i : K) (h1 : (i' = i) = True) : (term559 A K i x z k s i') = (term397 A K x k s i').
Proof. exact (MK_COMB (@lem4440862 A K k z x i' i h1) (@lem4440863 A K k s i')). Qed.
Lemma lem4440865 {A K : Type'} (i : K) (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i' : K) : term633 A K i z x k s i'.
Proof. exact (fun h0 : (i' = i) = True => @lem4440864 A K z x k s i' i h0). Qed.
Lemma lem4440866 {A K : Type'} (i : K) (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i' : K) : term634 A K i z x k s i'.
Proof. exact (conj (@lem4440847 A K i x z k s i') (@lem4440865 A K i z x k s i')). Qed.
Lemma lem4440868 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term619 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4440869 {A K : Type'} (x : A) (i : K) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (i' : K) : term635 A K x i z k s i'.
Proof. exact (@lem4440868 (term559 A K i x z k s i') (term397 A K x k s i') (i' = i) (term630 A K z k s i')). Qed.
Lemma lem4440884 {A K : Type'} (x : A) (i : K) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (i' : K) : (term559 A K i x z k s i') = (term636 A K x i z k s i').
Proof. exact (@lem4440869 A K x i z k s i' (@lem4440866 A K i z x k s i')). Qed.
Lemma lem4440890 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (@IN K i' k) = False.
Proof. exact (h1). Qed.
Lemma lem4440891 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4440892 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term605 A K i' k) = (@COND (A -> Prop) False).
Proof. exact (MK_COMB (@lem4440891 A) (@lem4440890 K i' k h1)). Qed.
Lemma lem4440893 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4440894 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term606 A K k s i') = (term607 A K s i').
Proof. exact (MK_COMB (@lem4440892 A K i' k h1) (@lem4440893 A K s i')). Qed.
Lemma lem4440895 {A : Type'} : (@INSERT A (@ARB A) (@EMPTY A)) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440896 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term383 A K k s i') = (term608 A K s i').
Proof. exact (MK_COMB (@lem4440894 A K s i' k h1) (@lem4440895 A)). Qed.
Lemma lem4440898 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4440899 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (@COND (A -> Prop) False t1 t2) = t2.
Proof. exact (@lem4440898 (A -> Prop) t1 t2). Qed.
Lemma lem4440900 {A K : Type'} (s : type1470 A K) (i' : K) : (term608 A K s i') = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (@lem4440899 A (s i') (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440901 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term383 A K k s i') = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (TRANS (@lem4440896 A K s i' k h1) (@lem4440900 A K s i')). Qed.
Lemma lem4440902 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4440903 {A K : Type'} (s : type1470 A K) (x : A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term397 A K x k s i') = (term609 A x).
Proof. exact (MK_COMB (@lem4440902 A x) (@lem4440901 A K s i' k h1)). Qed.
Lemma lem4440904 {K : Type'} (i' : K) (i : K) : (term637 K i' i) = (term637 K i' i).
Proof. exact (eq_refl (term637 K i' i)). Qed.
Lemma lem4440905 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term638 A K i x k s i') = (term639 A K i' i x).
Proof. exact (MK_COMB (@lem4440904 K i' i) (@lem4440903 A K s x i' k h1)). Qed.
Lemma lem4440908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4440909 {A K : Type'} (s : type1470 A K) (i : K) (x : A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term640 A K i x k s i') = (term641 A K i' i x).
Proof. exact (MK_COMB (@lem4440908) (@lem4440905 A K s i x i' k h1)). Qed.
Lemma lem4440913 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (@IN K i' k) = False.
Proof. exact (h1). Qed.
Lemma lem4440914 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4440915 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term642 A K i' k) = (@COND A False).
Proof. exact (MK_COMB (@lem4440914 A) (@lem4440913 K i' k h1)). Qed.
Lemma lem4440916 {A K : Type'} (z : K -> A) (i' : K) : (z i') = (z i').
Proof. exact (eq_refl (z i')). Qed.
Lemma lem4440917 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term643 A K k z i') = (term644 A K z i').
Proof. exact (MK_COMB (@lem4440915 A K i' k h1) (@lem4440916 A K z i')). Qed.
Lemma lem4440918 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4440919 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term551 A K k z i') = (term645 A K z i').
Proof. exact (MK_COMB (@lem4440917 A K z i' k h1) (@lem4440918 A)). Qed.
Lemma lem4440921 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4440922 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4440921 A t1 t2). Qed.
Lemma lem4440923 {A K : Type'} (z : K -> A) (i' : K) : (term645 A K z i') = (@ARB A).
Proof. exact (@lem4440922 A (z i') (@ARB A)). Qed.
Lemma lem4440924 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term551 A K k z i') = (@ARB A).
Proof. exact (TRANS (@lem4440919 A K z i' k h1) (@lem4440923 A K z i')). Qed.
Lemma lem4440925 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4440926 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term629 A K k z i') = (@IN A (@ARB A)).
Proof. exact (MK_COMB (@lem4440925 A) (@lem4440924 A K z i' k h1)). Qed.
Lemma lem4440928 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (@IN K i' k) = False.
Proof. exact (h1). Qed.
Lemma lem4440929 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4440930 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term605 A K i' k) = (@COND (A -> Prop) False).
Proof. exact (MK_COMB (@lem4440929 A) (@lem4440928 K i' k h1)). Qed.
Lemma lem4440931 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4440932 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term606 A K k s i') = (term607 A K s i').
Proof. exact (MK_COMB (@lem4440930 A K i' k h1) (@lem4440931 A K s i')). Qed.
Lemma lem4440933 {A : Type'} : (@INSERT A (@ARB A) (@EMPTY A)) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440934 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term383 A K k s i') = (term608 A K s i').
Proof. exact (MK_COMB (@lem4440932 A K s i' k h1) (@lem4440933 A)). Qed.
Lemma lem4440936 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4440937 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (@COND (A -> Prop) False t1 t2) = t2.
Proof. exact (@lem4440936 (A -> Prop) t1 t2). Qed.
Lemma lem4440938 {A K : Type'} (s : type1470 A K) (i' : K) : (term608 A K s i') = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (@lem4440937 A (s i') (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440939 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term383 A K k s i') = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (TRANS (@lem4440934 A K s i' k h1) (@lem4440938 A K s i')). Qed.
Lemma lem4440940 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term630 A K z k s i') = (term646 A).
Proof. exact (MK_COMB (@lem4440926 A K z i' k h1) (@lem4440939 A K s i' k h1)). Qed.
Lemma lem4440941 {K : Type'} (i' : K) (i : K) : (term647 K i' i) = (term647 K i' i).
Proof. exact (eq_refl (term647 K i' i)). Qed.
Lemma lem4440942 {A K : Type'} (z : K -> A) (s : type1470 A K) (i : K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term648 A K i z k s i') = (term649 A K i' i).
Proof. exact (MK_COMB (@lem4440941 K i' i) (@lem4440940 A K z s i' k h1)). Qed.
Lemma lem4440945 {A K : Type'} (z : K -> A) (s : type1470 A K) (x : A) (i : K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = False) : (term636 A K x i z k s i') = (term650 A K x i' i).
Proof. exact (MK_COMB (@lem4440909 A K s i x i' k h1) (@lem4440942 A K z s i i' k h1)). Qed.
Lemma lem4440948 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) (x : A) (i' : K) (i : K) : term651 A K z k s x i' i.
Proof. exact (fun h0 : (@IN K i' k) = False => @lem4440945 A K z s x i i' k h0). Qed.
Lemma lem4440952 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (@IN K i' k) = True.
Proof. exact (h1). Qed.
Lemma lem4440953 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4440954 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term605 A K i' k) = (@COND (A -> Prop) True).
Proof. exact (MK_COMB (@lem4440953 A) (@lem4440952 K i' k h1)). Qed.
Lemma lem4440955 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4440956 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term606 A K k s i') = (term613 A K s i').
Proof. exact (MK_COMB (@lem4440954 A K i' k h1) (@lem4440955 A K s i')). Qed.
Lemma lem4440957 {A : Type'} : (@INSERT A (@ARB A) (@EMPTY A)) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440958 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term383 A K k s i') = (term614 A K s i').
Proof. exact (MK_COMB (@lem4440956 A K s i' k h1) (@lem4440957 A)). Qed.
Lemma lem4440960 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4440961 {A : Type'} (t2 : A -> Prop) (t1 : A -> Prop) : (@COND (A -> Prop) True t1 t2) = t1.
Proof. exact (@lem4440960 (A -> Prop) t2 t1). Qed.
Lemma lem4440962 {A K : Type'} (s : type1470 A K) (i' : K) : (term614 A K s i') = (s i').
Proof. exact (@lem4440961 A (@INSERT A (@ARB A) (@EMPTY A)) (s i')). Qed.
Lemma lem4440963 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term383 A K k s i') = (s i').
Proof. exact (TRANS (@lem4440958 A K s i' k h1) (@lem4440962 A K s i')). Qed.
Lemma lem4440964 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4440965 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term397 A K x k s i') = (term35 A K x s i').
Proof. exact (MK_COMB (@lem4440964 A x) (@lem4440963 A K s i' k h1)). Qed.
Lemma lem4440966 {K : Type'} (i' : K) (i : K) : (term637 K i' i) = (term637 K i' i).
Proof. exact (eq_refl (term637 K i' i)). Qed.
Lemma lem4440967 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term638 A K i x k s i') = (term652 A K i x s i').
Proof. exact (MK_COMB (@lem4440966 K i' i) (@lem4440965 A K x s i' k h1)). Qed.
Lemma lem4440970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4440971 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term640 A K i x k s i') = (term653 A K i x s i').
Proof. exact (MK_COMB (@lem4440970) (@lem4440967 A K i x s i' k h1)). Qed.
Lemma lem4440975 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (@IN K i' k) = True.
Proof. exact (h1). Qed.
Lemma lem4440976 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4440977 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term642 A K i' k) = (@COND A True).
Proof. exact (MK_COMB (@lem4440976 A) (@lem4440975 K i' k h1)). Qed.
Lemma lem4440978 {A K : Type'} (z : K -> A) (i' : K) : (z i') = (z i').
Proof. exact (eq_refl (z i')). Qed.
Lemma lem4440979 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term643 A K k z i') = (term654 A K z i').
Proof. exact (MK_COMB (@lem4440977 A K i' k h1) (@lem4440978 A K z i')). Qed.
Lemma lem4440980 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4440981 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term551 A K k z i') = (term655 A K z i').
Proof. exact (MK_COMB (@lem4440979 A K z i' k h1) (@lem4440980 A)). Qed.
Lemma lem4440983 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4440984 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4440983 A t2 t1). Qed.
Lemma lem4440985 {A K : Type'} (z : K -> A) (i' : K) : (term655 A K z i') = (z i').
Proof. exact (@lem4440984 A (@ARB A) (z i')). Qed.
Lemma lem4440986 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term551 A K k z i') = (z i').
Proof. exact (TRANS (@lem4440981 A K z i' k h1) (@lem4440985 A K z i')). Qed.
Lemma lem4440987 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4440988 {A K : Type'} (z : K -> A) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term629 A K k z i') = (term421 A K z i').
Proof. exact (MK_COMB (@lem4440987 A) (@lem4440986 A K z i' k h1)). Qed.
Lemma lem4440990 {K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (@IN K i' k) = True.
Proof. exact (h1). Qed.
Lemma lem4440991 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4440992 {A K : Type'} (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term605 A K i' k) = (@COND (A -> Prop) True).
Proof. exact (MK_COMB (@lem4440991 A) (@lem4440990 K i' k h1)). Qed.
Lemma lem4440993 {A K : Type'} (s : type1470 A K) (i' : K) : (s i') = (s i').
Proof. exact (eq_refl (s i')). Qed.
Lemma lem4440994 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term606 A K k s i') = (term613 A K s i').
Proof. exact (MK_COMB (@lem4440992 A K i' k h1) (@lem4440993 A K s i')). Qed.
Lemma lem4440995 {A : Type'} : (@INSERT A (@ARB A) (@EMPTY A)) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4440996 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term383 A K k s i') = (term614 A K s i').
Proof. exact (MK_COMB (@lem4440994 A K s i' k h1) (@lem4440995 A)). Qed.
Lemma lem4440998 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4440999 {A : Type'} (t2 : A -> Prop) (t1 : A -> Prop) : (@COND (A -> Prop) True t1 t2) = t1.
Proof. exact (@lem4440998 (A -> Prop) t2 t1). Qed.
Lemma lem4441000 {A K : Type'} (s : type1470 A K) (i' : K) : (term614 A K s i') = (s i').
Proof. exact (@lem4440999 A (@INSERT A (@ARB A) (@EMPTY A)) (s i')). Qed.
Lemma lem4441001 {A K : Type'} (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term383 A K k s i') = (s i').
Proof. exact (TRANS (@lem4440996 A K s i' k h1) (@lem4441000 A K s i')). Qed.
Lemma lem4441002 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term630 A K z k s i') = (term656 A K z s i').
Proof. exact (MK_COMB (@lem4440988 A K z i' k h1) (@lem4441001 A K s i' k h1)). Qed.
Lemma lem4441003 {K : Type'} (i' : K) (i : K) : (term647 K i' i) = (term647 K i' i).
Proof. exact (eq_refl (term647 K i' i)). Qed.
Lemma lem4441004 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term648 A K i z k s i') = (term657 A K i z s i').
Proof. exact (MK_COMB (@lem4441003 K i' i) (@lem4441002 A K z s i' k h1)). Qed.
Lemma lem4441007 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (k : K -> Prop) (h1 : (@IN K i' k) = True) : (term636 A K x i z k s i') = (term658 A K x i z s i').
Proof. exact (MK_COMB (@lem4440971 A K i x s i' k h1) (@lem4441004 A K i z s i' k h1)). Qed.
Lemma lem4441010 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : term659 A K k x i z s i'.
Proof. exact (fun h0 : (@IN K i' k) = True => @lem4441007 A K x i z s i' k h0). Qed.
Lemma lem4441011 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : term660 A K k x i z s i'.
Proof. exact (conj (@lem4440948 A K z k s x i' i) (@lem4441010 A K k x i z s i')). Qed.
Lemma lem4441013 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term619 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4441014 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : term661 A K z s k x i' i.
Proof. exact (@lem4441013 (term636 A K x i z k s i') (term658 A K x i z s i') (@IN K i' k) (term650 A K x i' i)). Qed.
Lemma lem4441075 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term636 A K x i z k s i') = (term662 A K z s k x i' i).
Proof. exact (@lem4441014 A K z s k x i' i (@lem4441011 A K k x i z s i')). Qed.
Lemma lem4441076 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (i' : K) : (term663 A K i x z k s i') = (term663 A K i x z k s i').
Proof. exact (eq_refl (term663 A K i x z k s i')). Qed.
Lemma lem4441077 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : ((term559 A K i x z k s i') = (term636 A K x i z k s i')) = ((term559 A K i x z k s i') = (term662 A K z s k x i' i)).
Proof. exact (MK_COMB (@lem4441076 A K i x z k s i') (@lem4441075 A K z s k x i' i)). Qed.
Lemma lem4441078 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term559 A K i x z k s i') = (term662 A K z s k x i' i).
Proof. exact (EQ_MP (@lem4441077 A K z s k x i' i) (@lem4440884 A K x i z k s i')). Qed.
Lemma lem4441079 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term561 A K i x z k s) = (term664 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4441078 A K z s k x i' i)). Qed.
Lemma lem4441080 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4441081 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term563 A K i x z k s) = (term665 A K z s k x i).
Proof. exact (MK_COMB (@lem4441080 K) (@lem4441079 A K z s k x i)). Qed.
Lemma lem4441082 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4441083 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term567 A K i x z k s) = (term666 A K z s k x i).
Proof. exact (MK_COMB (@lem4441082) (@lem4441081 A K z s k x i)). Qed.
Lemma lem4441084 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4441085 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term578 A K i x z k s) = (term667 A K z s k x i).
Proof. exact (MK_COMB (@lem4441084) (@lem4441083 A K z s k x i)). Qed.
Lemma lem4441086 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term580 A K i x z k s) = (term668 A K z s k x i).
Proof. exact (MK_COMB (@lem4441085 A K z s k x i) (@lem4440827 A K)). Qed.
Lemma lem4441091 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term503 A K k z s i) = (term503 A K k z s i).
Proof. exact (eq_refl (term503 A K k z s i)). Qed.
Lemma lem4441092 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term505 A K k z s) = (term505 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4441091 A K k z s i)). Qed.
Lemma lem4441093 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4441094 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term507 A K k z s) = (term507 A K k z s).
Proof. exact (MK_COMB (@lem4441093 K) (@lem4441092 A K k z s)). Qed.
Lemma lem4441095 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4441096 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term524 A K k z s) = (term524 A K k z s).
Proof. exact (MK_COMB (@lem4441095) (@lem4441094 A K k z s)). Qed.
Lemma lem4441097 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term582 A K i x z k s) = (term669 A K z s k x i).
Proof. exact (MK_COMB (@lem4441096 A K k z s) (@lem4441086 A K z s k x i)). Qed.
Lemma lem4441100 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term615 A K x s i) = (term615 A K x s i).
Proof. exact (eq_refl (term615 A K x s i)). Qed.
Lemma lem4441101 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term616 A K i x z k s) = (term674 A K z s k x i).
Proof. exact (MK_COMB (@lem4441100 A K x s i) (@lem4441097 A K z s k x i)). Qed.
Lemma lem4441106 {K : Type'} (i : K) (k : K -> Prop) : (term675 K i k) = (term675 K i k).
Proof. exact (eq_refl (term675 K i k)). Qed.
Lemma lem4441107 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term676 A K i x z k s) = (term677 A K z s k x i).
Proof. exact (MK_COMB (@lem4441106 K i k) (@lem4441101 A K z s k x i)). Qed.
Lemma lem4441108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441109 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term678 A K i x z k s) = (term679 A K z s k x i).
Proof. exact (MK_COMB (@lem4441108) (@lem4441107 A K z s k x i)). Qed.
Lemma lem4441110 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term621 A K i x z k s) = (term680 A K z s k x i).
Proof. exact (MK_COMB (@lem4441109 A K z s k x i) (@lem4440800 A K z s k x i)). Qed.
Lemma lem4441111 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term681 A K i x z k s) = (term681 A K i x z k s).
Proof. exact (eq_refl (term681 A K i x z k s)). Qed.
Lemma lem4441112 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term584 A K i x z k s) = (term621 A K i x z k s)) = ((term584 A K i x z k s) = (term680 A K z s k x i)).
Proof. exact (MK_COMB (@lem4441111 A K i x z k s) (@lem4441110 A K z s k x i)). Qed.
Lemma lem4441113 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term584 A K i x z k s) = (term680 A K z s k x i).
Proof. exact (EQ_MP (@lem4441112 A K z s k x i) (@lem4440495 A K i x z k s)). Qed.
Lemma lem4441114 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) : (term586 A K x z k s) = (term682 A K z s k x).
Proof. exact (fun_ext (fun i : K => @lem4441113 A K z s k x i)). Qed.
Lemma lem4441115 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4441116 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) : (term588 A K x z k s) = (term683 A K z s k x).
Proof. exact (MK_COMB (@lem4441115 K) (@lem4441114 A K z s k x)). Qed.
Lemma lem4441117 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) : (term590 A K z k s) = (term684 A K z s k).
Proof. exact (fun_ext (fun x : A => @lem4441116 A K z s k x)). Qed.
Lemma lem4441118 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4441119 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) : (term592 A K z k s) = (term685 A K z s k).
Proof. exact (MK_COMB (@lem4441118 A) (@lem4441117 A K z s k)). Qed.
Lemma lem4441120 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term594 A K k s) = (term686 A K s k).
Proof. exact (fun_ext (fun z : K -> A => @lem4441119 A K z s k)). Qed.
Lemma lem4441121 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4441122 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term596 A K k s) = (term687 A K s k).
Proof. exact (MK_COMB (@lem4441121 A K) (@lem4441120 A K s k)). Qed.
Lemma lem4441123 {A K : Type'} (s : type1470 A K) : (term598 A K s) = (term688 A K s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4441122 A K s k)). Qed.
Lemma lem4441124 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4441125 {A K : Type'} (s : type1470 A K) : (term600 A K s) = (term689 A K s).
Proof. exact (MK_COMB (@lem4441124 K) (@lem4441123 A K s)). Qed.
Lemma lem4441126 {A K : Type'} : (term602 A K) = (term690 A K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4441125 A K s)). Qed.
Lemma lem4441127 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4441128 {A K : Type'} : (term604 A K) = (term691 A K).
Proof. exact (MK_COMB (@lem4441127 A K) (@lem4441126 A K)). Qed.
Lemma lem4441295 {A K : Type'} : (term603 A K) = (term691 A K).
Proof. exact (TRANS (@lem4440322 A K) (@lem4441128 A K)). Qed.
Lemma lem4441296 {A K : Type'} : (term691 A K) = (term603 A K).
Proof. exact (SYM (@lem4441295 A K)). Qed.
Lemma lem4441298 (p : Prop) : p = (term58 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4441299 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term680 A K z s k x i) = (term692 A K z s k x i).
Proof. exact (@lem4441298 (term680 A K z s k x i)). Qed.
Lemma lem4441300 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term692 A K z s k x i) = (term680 A K z s k x i).
Proof. exact (SYM (@lem4441299 A K z s k x i)). Qed.
Lemma lem4441301 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) (h1 : term693 A K z s k x i) : term693 A K z s k x i.
Proof. exact (h1). Qed.
Lemma lem4441304 {K : Type'} (i : K) (k : K -> Prop) : (term694 K i k) = (@IN K i k).
Proof. exact (@lem16933 (@IN K i k)). Qed.
Lemma lem4441312 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term503 A K k z s i) = (term695 A K k z s i).
Proof. exact (@lem17265 (@IN K i k) (term656 A K z s i)). Qed.
Lemma lem4441313 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term505 A K k z s) = (term696 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4441312 A K k z s i)). Qed.
Lemma lem4441314 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4441315 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term507 A K k z s) = (term697 A K k z s).
Proof. exact (MK_COMB (@lem4441314 K) (@lem4441313 A K k z s)). Qed.
Lemma lem4441318 {K : Type'} (i' : K) (k : K -> Prop) : (term694 K i' k) = (@IN K i' k).
Proof. exact (@lem16933 (@IN K i' k)). Qed.
Lemma lem4441321 {K : Type'} (i' : K) (i : K) : (term698 K i' i) = (i' = i).
Proof. exact (@lem16933 (i' = i)). Qed.
Lemma lem4441322 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term699 A K x s i') = (term699 A K x s i').
Proof. exact (eq_refl (term699 A K x s i')). Qed.
Lemma lem4441323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441324 {K : Type'} (i' : K) (i : K) : (term700 K i' i) = (term701 K i' i).
Proof. exact (MK_COMB (@lem4441323) (@lem4441321 K i' i)). Qed.
Lemma lem4441325 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term702 A K i x s i') = (term703 A K i x s i').
Proof. exact (MK_COMB (@lem4441324 K i' i) (@lem4441322 A K x s i')). Qed.
Lemma lem4441326 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term704 A K i x s i') = (term702 A K i x s i').
Proof. exact (@lem17160 (term705 K i' i) (term35 A K x s i')). Qed.
Lemma lem4441327 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term704 A K i x s i') = (term703 A K i x s i').
Proof. exact (TRANS (@lem4441326 A K i x s i') (@lem4441325 A K i x s i')). Qed.
Lemma lem4441334 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term706 A K i z s i') = (term707 A K i z s i').
Proof. exact (@lem17160 (i' = i) (term656 A K z s i')). Qed.
Lemma lem4441335 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4441336 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term708 A K i x s i') = (term709 A K i x s i').
Proof. exact (MK_COMB (@lem4441335) (@lem4441327 A K i x s i')). Qed.
Lemma lem4441337 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term710 A K x i z s i') = (term711 A K x i z s i').
Proof. exact (MK_COMB (@lem4441336 A K i x s i') (@lem4441334 A K i z s i')). Qed.
Lemma lem4441338 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term712 A K x i z s i') = (term710 A K x i z s i').
Proof. exact (@lem17045 (term652 A K i x s i') (term657 A K i z s i')). Qed.
Lemma lem4441339 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term712 A K x i z s i') = (term711 A K x i z s i').
Proof. exact (TRANS (@lem4441338 A K x i z s i') (@lem4441337 A K x i z s i')). Qed.
Lemma lem4441340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441341 {K : Type'} (i' : K) (k : K -> Prop) : (term713 K i' k) = (term22 K i' k).
Proof. exact (MK_COMB (@lem4441340) (@lem4441318 K i' k)). Qed.
Lemma lem4441342 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term714 A K k x i z s i') = (term715 A K k x i z s i').
Proof. exact (MK_COMB (@lem4441341 K i' k) (@lem4441339 A K x i z s i')). Qed.
Lemma lem4441343 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term716 A K k x i z s i') = (term714 A K k x i z s i').
Proof. exact (@lem17160 (term717 K i' k) (term658 A K x i z s i')). Qed.
Lemma lem4441344 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term716 A K k x i z s i') = (term715 A K k x i z s i').
Proof. exact (TRANS (@lem4441343 A K k x i z s i') (@lem4441342 A K k x i z s i')). Qed.
Lemma lem4441348 {K : Type'} (i' : K) (i : K) : (term698 K i' i) = (i' = i).
Proof. exact (@lem16933 (i' = i)). Qed.
Lemma lem4441349 {A : Type'} (x : A) : (term718 A x) = (term718 A x).
Proof. exact (eq_refl (term718 A x)). Qed.
Lemma lem4441350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441351 {K : Type'} (i' : K) (i : K) : (term700 K i' i) = (term701 K i' i).
Proof. exact (MK_COMB (@lem4441350) (@lem4441348 K i' i)). Qed.
Lemma lem4441352 {A K : Type'} (i' : K) (i : K) (x : A) : (term719 A K i' i x) = (term720 A K i' i x).
Proof. exact (MK_COMB (@lem4441351 K i' i) (@lem4441349 A x)). Qed.
Lemma lem4441353 {A K : Type'} (i' : K) (i : K) (x : A) : (term721 A K i' i x) = (term719 A K i' i x).
Proof. exact (@lem17160 (term705 K i' i) (term609 A x)). Qed.
Lemma lem4441354 {A K : Type'} (i' : K) (i : K) (x : A) : (term721 A K i' i x) = (term720 A K i' i x).
Proof. exact (TRANS (@lem4441353 A K i' i x) (@lem4441352 A K i' i x)). Qed.
Lemma lem4441361 {A K : Type'} (i' : K) (i : K) : (term722 A K i' i) = (term723 A K i' i).
Proof. exact (@lem17160 (i' = i) (term646 A)). Qed.
Lemma lem4441362 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4441363 {A K : Type'} (i' : K) (i : K) (x : A) : (term724 A K i' i x) = (term725 A K i' i x).
Proof. exact (MK_COMB (@lem4441362) (@lem4441354 A K i' i x)). Qed.
Lemma lem4441364 {A K : Type'} (x : A) (i' : K) (i : K) : (term726 A K x i' i) = (term727 A K x i' i).
Proof. exact (MK_COMB (@lem4441363 A K i' i x) (@lem4441361 A K i' i)). Qed.
Lemma lem4441365 {A K : Type'} (x : A) (i' : K) (i : K) : (term728 A K x i' i) = (term726 A K x i' i).
Proof. exact (@lem17045 (term639 A K i' i x) (term649 A K i' i)). Qed.
Lemma lem4441366 {A K : Type'} (x : A) (i' : K) (i : K) : (term728 A K x i' i) = (term727 A K x i' i).
Proof. exact (TRANS (@lem4441365 A K x i' i) (@lem4441364 A K x i' i)). Qed.
Lemma lem4441368 {K : Type'} (i' : K) (k : K -> Prop) : (term729 K i' k) = (term729 K i' k).
Proof. exact (eq_refl (term729 K i' k)). Qed.
Lemma lem4441369 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term730 A K k x i' i) = (term731 A K k x i' i).
Proof. exact (MK_COMB (@lem4441368 K i' k) (@lem4441366 A K x i' i)). Qed.
Lemma lem4441370 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term732 A K k x i' i) = (term730 A K k x i' i).
Proof. exact (@lem17160 (@IN K i' k) (term650 A K x i' i)). Qed.
Lemma lem4441371 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term732 A K k x i' i) = (term731 A K k x i' i).
Proof. exact (TRANS (@lem4441370 A K k x i' i) (@lem4441369 A K k x i' i)). Qed.
Lemma lem4441372 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4441373 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term733 A K k x i z s i') = (term734 A K k x i z s i').
Proof. exact (MK_COMB (@lem4441372) (@lem4441344 A K k x i z s i')). Qed.
Lemma lem4441374 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term735 A K z s k x i' i) = (term736 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4441373 A K k x i z s i') (@lem4441371 A K k x i' i)). Qed.
Lemma lem4441375 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term737 A K z s k x i' i) = (term735 A K z s k x i' i).
Proof. exact (@lem17045 (term738 A K k x i z s i') (term739 A K k x i' i)). Qed.
Lemma lem4441376 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term737 A K z s k x i' i) = (term736 A K z s k x i' i).
Proof. exact (TRANS (@lem4441375 A K z s k x i' i) (@lem4441374 A K z s k x i' i)). Qed.
Lemma lem4441377 {K : Type'} (P : K -> Prop) : (term75 K P) = (term76 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4441378 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term666 A K z s k x i) = (term740 A K z s k x i).
Proof. exact (@lem4441377 K (term664 A K z s k x i)). Qed.
Lemma lem4441379 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term741 A K z s k x i i') = (term662 A K z s k x i' i).
Proof. exact (eq_refl (term741 A K z s k x i i')). Qed.
Lemma lem4441380 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4441381 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term742 A K z s k x i i') = (term737 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4441380) (@lem4441379 A K z s k x i' i)). Qed.
Lemma lem4441382 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term742 A K z s k x i i') = (term736 A K z s k x i' i).
Proof. exact (TRANS (@lem4441381 A K z s k x i' i) (@lem4441376 A K z s k x i' i)). Qed.
Lemma lem4441383 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term743 A K z s k x i) = (term744 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4441382 A K z s k x i' i)). Qed.
Lemma lem4441384 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4441385 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term740 A K z s k x i) = (term745 A K z s k x i).
Proof. exact (MK_COMB (@lem4441384 K) (@lem4441383 A K z s k x i)). Qed.
Lemma lem4441386 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term666 A K z s k x i) = (term745 A K z s k x i).
Proof. exact (TRANS (@lem4441378 A K z s k x i) (@lem4441385 A K z s k x i)). Qed.
Lemma lem4441401 {A : Type'} (x : A) (y : A) : ((term622 A x y) = (x = y)) = (term746 A x y).
Proof. exact (@lem17784 (term622 A x y) (x = y)). Qed.
Lemma lem4441402 {A : Type'} (x : A) : (term623 A x) = (term747 A x).
Proof. exact (fun_ext (fun y : A => @lem4441401 A x y)). Qed.
Lemma lem4441403 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4441404 {A : Type'} (x : A) : (term624 A x) = (term748 A x).
Proof. exact (MK_COMB (@lem4441403 A) (@lem4441402 A x)). Qed.
Lemma lem4441405 {A : Type'} : (term625 A) = (term749 A).
Proof. exact (fun_ext (fun x : A => @lem4441404 A x)). Qed.
Lemma lem4441406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4441407 {A : Type'} : (term568 A) = (term750 A).
Proof. exact (MK_COMB (@lem4441406 A) (@lem4441405 A)). Qed.
Lemma lem4441422 {K : Type'} (x : K) (y : K) : ((term622 K x y) = (x = y)) = (term746 K x y).
Proof. exact (@lem17784 (term622 K x y) (x = y)). Qed.
Lemma lem4441423 {K : Type'} (x : K) : (term623 K x) = (term747 K x).
Proof. exact (fun_ext (fun y : K => @lem4441422 K x y)). Qed.
Lemma lem4441424 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4441425 {K : Type'} (x : K) : (term624 K x) = (term748 K x).
Proof. exact (MK_COMB (@lem4441424 K) (@lem4441423 K x)). Qed.
Lemma lem4441426 {K : Type'} : (term625 K) = (term749 K).
Proof. exact (fun_ext (fun x : K => @lem4441425 K x)). Qed.
Lemma lem4441427 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4441428 {K : Type'} : (term568 K) = (term750 K).
Proof. exact (MK_COMB (@lem4441427 K) (@lem4441426 K)). Qed.
Lemma lem4441429 {K : Type'} : (term751 K) = (term568 K).
Proof. exact (@lem16933 (term568 K)). Qed.
Lemma lem4441430 {K : Type'} : (term751 K) = (term750 K).
Proof. exact (TRANS (@lem4441429 K) (@lem4441428 K)). Qed.
Lemma lem4441431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441432 {A : Type'} : (term752 A) = (term753 A).
Proof. exact (MK_COMB (@lem4441431) (@lem4441407 A)). Qed.
Lemma lem4441433 {A K : Type'} : (term754 A K) = (term755 A K).
Proof. exact (MK_COMB (@lem4441432 A) (@lem4441430 K)). Qed.
Lemma lem4441434 {A K : Type'} : (term756 A K) = (term754 A K).
Proof. exact (@lem17362 (term568 A) (term574 K)). Qed.
Lemma lem4441435 {A K : Type'} : (term756 A K) = (term755 A K).
Proof. exact (TRANS (@lem4441434 A K) (@lem4441433 A K)). Qed.
Lemma lem4441436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441437 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term757 A K z s k x i) = (term758 A K z s k x i).
Proof. exact (MK_COMB (@lem4441436) (@lem4441386 A K z s k x i)). Qed.
Lemma lem4441438 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term759 A K z s k x i) = (term760 A K z s k x i).
Proof. exact (MK_COMB (@lem4441437 A K z s k x i) (@lem4441435 A K)). Qed.
Lemma lem4441439 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term761 A K z s k x i) = (term759 A K z s k x i).
Proof. exact (@lem17362 (term666 A K z s k x i) (term577 A K)). Qed.
Lemma lem4441440 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term761 A K z s k x i) = (term760 A K z s k x i).
Proof. exact (TRANS (@lem4441439 A K z s k x i) (@lem4441438 A K z s k x i)). Qed.
Lemma lem4441441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441442 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term762 A K k z s) = (term763 A K k z s).
Proof. exact (MK_COMB (@lem4441441) (@lem4441315 A K k z s)). Qed.
Lemma lem4441443 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term764 A K z s k x i) = (term765 A K z s k x i).
Proof. exact (MK_COMB (@lem4441442 A K k z s) (@lem4441440 A K z s k x i)). Qed.
Lemma lem4441444 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term766 A K z s k x i) = (term764 A K z s k x i).
Proof. exact (@lem17362 (term507 A K k z s) (term668 A K z s k x i)). Qed.
Lemma lem4441445 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term766 A K z s k x i) = (term765 A K z s k x i).
Proof. exact (TRANS (@lem4441444 A K z s k x i) (@lem4441443 A K z s k x i)). Qed.
Lemma lem4441447 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term767 A K x s i) = (term767 A K x s i).
Proof. exact (eq_refl (term767 A K x s i)). Qed.
Lemma lem4441448 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term768 A K z s k x i) = (term769 A K z s k x i).
Proof. exact (MK_COMB (@lem4441447 A K x s i) (@lem4441445 A K z s k x i)). Qed.
Lemma lem4441449 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term770 A K z s k x i) = (term768 A K z s k x i).
Proof. exact (@lem17362 (term35 A K x s i) (term669 A K z s k x i)). Qed.
Lemma lem4441450 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term770 A K z s k x i) = (term769 A K z s k x i).
Proof. exact (TRANS (@lem4441449 A K z s k x i) (@lem4441448 A K z s k x i)). Qed.
Lemma lem4441451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441452 {K : Type'} (i : K) (k : K -> Prop) : (term713 K i k) = (term22 K i k).
Proof. exact (MK_COMB (@lem4441451) (@lem4441304 K i k)). Qed.
Lemma lem4441453 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term771 A K z s k x i) = (term772 A K z s k x i).
Proof. exact (MK_COMB (@lem4441452 K i k) (@lem4441450 A K z s k x i)). Qed.
Lemma lem4441454 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term773 A K z s k x i) = (term771 A K z s k x i).
Proof. exact (@lem17160 (term717 K i k) (term674 A K z s k x i)). Qed.
Lemma lem4441455 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term773 A K z s k x i) = (term772 A K z s k x i).
Proof. exact (TRANS (@lem4441454 A K z s k x i) (@lem4441453 A K z s k x i)). Qed.
Lemma lem4441464 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term503 A K k z s i) = (term695 A K k z s i).
Proof. exact (@lem17265 (@IN K i k) (term656 A K z s i)). Qed.
Lemma lem4441465 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term505 A K k z s) = (term696 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4441464 A K k z s i)). Qed.
Lemma lem4441466 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4441467 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term507 A K k z s) = (term697 A K k z s).
Proof. exact (MK_COMB (@lem4441466 K) (@lem4441465 A K k z s)). Qed.
Lemma lem4441470 {K : Type'} (i' : K) (k : K -> Prop) : (term694 K i' k) = (@IN K i' k).
Proof. exact (@lem16933 (@IN K i' k)). Qed.
Lemma lem4441473 {K : Type'} (i' : K) (i : K) : (term698 K i' i) = (i' = i).
Proof. exact (@lem16933 (i' = i)). Qed.
Lemma lem4441474 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term699 A K x s i') = (term699 A K x s i').
Proof. exact (eq_refl (term699 A K x s i')). Qed.
Lemma lem4441475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441476 {K : Type'} (i' : K) (i : K) : (term700 K i' i) = (term701 K i' i).
Proof. exact (MK_COMB (@lem4441475) (@lem4441473 K i' i)). Qed.
Lemma lem4441477 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term702 A K i x s i') = (term703 A K i x s i').
Proof. exact (MK_COMB (@lem4441476 K i' i) (@lem4441474 A K x s i')). Qed.
Lemma lem4441478 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term704 A K i x s i') = (term702 A K i x s i').
Proof. exact (@lem17160 (term705 K i' i) (term35 A K x s i')). Qed.
Lemma lem4441479 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term704 A K i x s i') = (term703 A K i x s i').
Proof. exact (TRANS (@lem4441478 A K i x s i') (@lem4441477 A K i x s i')). Qed.
Lemma lem4441486 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term706 A K i z s i') = (term707 A K i z s i').
Proof. exact (@lem17160 (i' = i) (term656 A K z s i')). Qed.
Lemma lem4441487 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4441488 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) : (term708 A K i x s i') = (term709 A K i x s i').
Proof. exact (MK_COMB (@lem4441487) (@lem4441479 A K i x s i')). Qed.
Lemma lem4441489 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term710 A K x i z s i') = (term711 A K x i z s i').
Proof. exact (MK_COMB (@lem4441488 A K i x s i') (@lem4441486 A K i z s i')). Qed.
Lemma lem4441490 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term712 A K x i z s i') = (term710 A K x i z s i').
Proof. exact (@lem17045 (term652 A K i x s i') (term657 A K i z s i')). Qed.
Lemma lem4441491 {A K : Type'} (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term712 A K x i z s i') = (term711 A K x i z s i').
Proof. exact (TRANS (@lem4441490 A K x i z s i') (@lem4441489 A K x i z s i')). Qed.
Lemma lem4441492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441493 {K : Type'} (i' : K) (k : K -> Prop) : (term713 K i' k) = (term22 K i' k).
Proof. exact (MK_COMB (@lem4441492) (@lem4441470 K i' k)). Qed.
Lemma lem4441494 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term714 A K k x i z s i') = (term715 A K k x i z s i').
Proof. exact (MK_COMB (@lem4441493 K i' k) (@lem4441491 A K x i z s i')). Qed.
Lemma lem4441495 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term716 A K k x i z s i') = (term714 A K k x i z s i').
Proof. exact (@lem17160 (term717 K i' k) (term658 A K x i z s i')). Qed.
Lemma lem4441496 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term716 A K k x i z s i') = (term715 A K k x i z s i').
Proof. exact (TRANS (@lem4441495 A K k x i z s i') (@lem4441494 A K k x i z s i')). Qed.
Lemma lem4441500 {K : Type'} (i' : K) (i : K) : (term698 K i' i) = (i' = i).
Proof. exact (@lem16933 (i' = i)). Qed.
Lemma lem4441501 {A : Type'} (x : A) : (term718 A x) = (term718 A x).
Proof. exact (eq_refl (term718 A x)). Qed.
Lemma lem4441502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441503 {K : Type'} (i' : K) (i : K) : (term700 K i' i) = (term701 K i' i).
Proof. exact (MK_COMB (@lem4441502) (@lem4441500 K i' i)). Qed.
Lemma lem4441504 {A K : Type'} (i' : K) (i : K) (x : A) : (term719 A K i' i x) = (term720 A K i' i x).
Proof. exact (MK_COMB (@lem4441503 K i' i) (@lem4441501 A x)). Qed.
Lemma lem4441505 {A K : Type'} (i' : K) (i : K) (x : A) : (term721 A K i' i x) = (term719 A K i' i x).
Proof. exact (@lem17160 (term705 K i' i) (term609 A x)). Qed.
Lemma lem4441506 {A K : Type'} (i' : K) (i : K) (x : A) : (term721 A K i' i x) = (term720 A K i' i x).
Proof. exact (TRANS (@lem4441505 A K i' i x) (@lem4441504 A K i' i x)). Qed.
Lemma lem4441513 {A K : Type'} (i' : K) (i : K) : (term722 A K i' i) = (term723 A K i' i).
Proof. exact (@lem17160 (i' = i) (term646 A)). Qed.
Lemma lem4441514 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4441515 {A K : Type'} (i' : K) (i : K) (x : A) : (term724 A K i' i x) = (term725 A K i' i x).
Proof. exact (MK_COMB (@lem4441514) (@lem4441506 A K i' i x)). Qed.
Lemma lem4441516 {A K : Type'} (x : A) (i' : K) (i : K) : (term726 A K x i' i) = (term727 A K x i' i).
Proof. exact (MK_COMB (@lem4441515 A K i' i x) (@lem4441513 A K i' i)). Qed.
Lemma lem4441517 {A K : Type'} (x : A) (i' : K) (i : K) : (term728 A K x i' i) = (term726 A K x i' i).
Proof. exact (@lem17045 (term639 A K i' i x) (term649 A K i' i)). Qed.
Lemma lem4441518 {A K : Type'} (x : A) (i' : K) (i : K) : (term728 A K x i' i) = (term727 A K x i' i).
Proof. exact (TRANS (@lem4441517 A K x i' i) (@lem4441516 A K x i' i)). Qed.
Lemma lem4441520 {K : Type'} (i' : K) (k : K -> Prop) : (term729 K i' k) = (term729 K i' k).
Proof. exact (eq_refl (term729 K i' k)). Qed.
Lemma lem4441521 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term730 A K k x i' i) = (term731 A K k x i' i).
Proof. exact (MK_COMB (@lem4441520 K i' k) (@lem4441518 A K x i' i)). Qed.
Lemma lem4441522 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term732 A K k x i' i) = (term730 A K k x i' i).
Proof. exact (@lem17160 (@IN K i' k) (term650 A K x i' i)). Qed.
Lemma lem4441523 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term732 A K k x i' i) = (term731 A K k x i' i).
Proof. exact (TRANS (@lem4441522 A K k x i' i) (@lem4441521 A K k x i' i)). Qed.
Lemma lem4441524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4441525 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term733 A K k x i z s i') = (term734 A K k x i z s i').
Proof. exact (MK_COMB (@lem4441524) (@lem4441496 A K k x i z s i')). Qed.
Lemma lem4441526 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term735 A K z s k x i' i) = (term736 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4441525 A K k x i z s i') (@lem4441523 A K k x i' i)). Qed.
Lemma lem4441527 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term737 A K z s k x i' i) = (term735 A K z s k x i' i).
Proof. exact (@lem17045 (term738 A K k x i z s i') (term739 A K k x i' i)). Qed.
Lemma lem4441528 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term737 A K z s k x i' i) = (term736 A K z s k x i' i).
Proof. exact (TRANS (@lem4441527 A K z s k x i' i) (@lem4441526 A K z s k x i' i)). Qed.
Lemma lem4441529 {K : Type'} (P : K -> Prop) : (term75 K P) = (term76 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4441530 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term666 A K z s k x i) = (term740 A K z s k x i).
Proof. exact (@lem4441529 K (term664 A K z s k x i)). Qed.
Lemma lem4441531 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term741 A K z s k x i i') = (term662 A K z s k x i' i).
Proof. exact (eq_refl (term741 A K z s k x i i')). Qed.
Lemma lem4441532 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4441533 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term742 A K z s k x i i') = (term737 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4441532) (@lem4441531 A K z s k x i' i)). Qed.
Lemma lem4441534 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term742 A K z s k x i i') = (term736 A K z s k x i' i).
Proof. exact (TRANS (@lem4441533 A K z s k x i' i) (@lem4441528 A K z s k x i' i)). Qed.
Lemma lem4441535 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term743 A K z s k x i) = (term744 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4441534 A K z s k x i' i)). Qed.
Lemma lem4441536 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4441537 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term740 A K z s k x i) = (term745 A K z s k x i).
Proof. exact (MK_COMB (@lem4441536 K) (@lem4441535 A K z s k x i)). Qed.
Lemma lem4441538 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term666 A K z s k x i) = (term745 A K z s k x i).
Proof. exact (TRANS (@lem4441530 A K z s k x i) (@lem4441537 A K z s k x i)). Qed.
Lemma lem4441553 {A : Type'} (x : A) (y : A) : ((term622 A x y) = (x = y)) = (term746 A x y).
Proof. exact (@lem17784 (term622 A x y) (x = y)). Qed.
Lemma lem4441554 {A : Type'} (x : A) : (term623 A x) = (term747 A x).
Proof. exact (fun_ext (fun y : A => @lem4441553 A x y)). Qed.
Lemma lem4441555 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4441556 {A : Type'} (x : A) : (term624 A x) = (term748 A x).
Proof. exact (MK_COMB (@lem4441555 A) (@lem4441554 A x)). Qed.
Lemma lem4441557 {A : Type'} : (term625 A) = (term749 A).
Proof. exact (fun_ext (fun x : A => @lem4441556 A x)). Qed.
Lemma lem4441558 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4441559 {A : Type'} : (term568 A) = (term750 A).
Proof. exact (MK_COMB (@lem4441558 A) (@lem4441557 A)). Qed.
Lemma lem4441574 {K : Type'} (x : K) (y : K) : ((term622 K x y) = (x = y)) = (term746 K x y).
Proof. exact (@lem17784 (term622 K x y) (x = y)). Qed.
Lemma lem4441575 {K : Type'} (x : K) : (term623 K x) = (term747 K x).
Proof. exact (fun_ext (fun y : K => @lem4441574 K x y)). Qed.
Lemma lem4441576 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4441577 {K : Type'} (x : K) : (term624 K x) = (term748 K x).
Proof. exact (MK_COMB (@lem4441576 K) (@lem4441575 K x)). Qed.
Lemma lem4441578 {K : Type'} : (term625 K) = (term749 K).
Proof. exact (fun_ext (fun x : K => @lem4441577 K x)). Qed.
Lemma lem4441579 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4441580 {K : Type'} : (term568 K) = (term750 K).
Proof. exact (MK_COMB (@lem4441579 K) (@lem4441578 K)). Qed.
Lemma lem4441581 {K : Type'} : (term751 K) = (term568 K).
Proof. exact (@lem16933 (term568 K)). Qed.
Lemma lem4441582 {K : Type'} : (term751 K) = (term750 K).
Proof. exact (TRANS (@lem4441581 K) (@lem4441580 K)). Qed.
Lemma lem4441583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441584 {A : Type'} : (term752 A) = (term753 A).
Proof. exact (MK_COMB (@lem4441583) (@lem4441559 A)). Qed.
Lemma lem4441585 {A K : Type'} : (term754 A K) = (term755 A K).
Proof. exact (MK_COMB (@lem4441584 A) (@lem4441582 K)). Qed.
Lemma lem4441586 {A K : Type'} : (term756 A K) = (term754 A K).
Proof. exact (@lem17362 (term568 A) (term574 K)). Qed.
Lemma lem4441587 {A K : Type'} : (term756 A K) = (term755 A K).
Proof. exact (TRANS (@lem4441586 A K) (@lem4441585 A K)). Qed.
Lemma lem4441588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441589 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term757 A K z s k x i) = (term758 A K z s k x i).
Proof. exact (MK_COMB (@lem4441588) (@lem4441538 A K z s k x i)). Qed.
Lemma lem4441590 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term759 A K z s k x i) = (term760 A K z s k x i).
Proof. exact (MK_COMB (@lem4441589 A K z s k x i) (@lem4441587 A K)). Qed.
Lemma lem4441591 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term761 A K z s k x i) = (term759 A K z s k x i).
Proof. exact (@lem17362 (term666 A K z s k x i) (term577 A K)). Qed.
Lemma lem4441592 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term761 A K z s k x i) = (term760 A K z s k x i).
Proof. exact (TRANS (@lem4441591 A K z s k x i) (@lem4441590 A K z s k x i)). Qed.
Lemma lem4441593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441594 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term762 A K k z s) = (term763 A K k z s).
Proof. exact (MK_COMB (@lem4441593) (@lem4441467 A K k z s)). Qed.
Lemma lem4441595 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term764 A K z s k x i) = (term765 A K z s k x i).
Proof. exact (MK_COMB (@lem4441594 A K k z s) (@lem4441592 A K z s k x i)). Qed.
Lemma lem4441596 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term766 A K z s k x i) = (term764 A K z s k x i).
Proof. exact (@lem17362 (term507 A K k z s) (term668 A K z s k x i)). Qed.
Lemma lem4441597 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term766 A K z s k x i) = (term765 A K z s k x i).
Proof. exact (TRANS (@lem4441596 A K z s k x i) (@lem4441595 A K z s k x i)). Qed.
Lemma lem4441599 {A : Type'} (x : A) : (term774 A x) = (term774 A x).
Proof. exact (eq_refl (term774 A x)). Qed.
Lemma lem4441600 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term775 A K z s k x i) = (term776 A K z s k x i).
Proof. exact (MK_COMB (@lem4441599 A x) (@lem4441597 A K z s k x i)). Qed.
Lemma lem4441601 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term777 A K z s k x i) = (term775 A K z s k x i).
Proof. exact (@lem17362 (term609 A x) (term669 A K z s k x i)). Qed.
Lemma lem4441602 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term777 A K z s k x i) = (term776 A K z s k x i).
Proof. exact (TRANS (@lem4441601 A K z s k x i) (@lem4441600 A K z s k x i)). Qed.
Lemma lem4441604 {K : Type'} (i : K) (k : K -> Prop) : (term729 K i k) = (term729 K i k).
Proof. exact (eq_refl (term729 K i k)). Qed.
Lemma lem4441605 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term778 A K z s k x i) = (term779 A K z s k x i).
Proof. exact (MK_COMB (@lem4441604 K i k) (@lem4441602 A K z s k x i)). Qed.
Lemma lem4441606 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term780 A K z s k x i) = (term778 A K z s k x i).
Proof. exact (@lem17160 (@IN K i k) (term670 A K z s k x i)). Qed.
Lemma lem4441607 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term780 A K z s k x i) = (term779 A K z s k x i).
Proof. exact (TRANS (@lem4441606 A K z s k x i) (@lem4441605 A K z s k x i)). Qed.
Lemma lem4441608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4441609 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term781 A K z s k x i) = (term782 A K z s k x i).
Proof. exact (MK_COMB (@lem4441608) (@lem4441455 A K z s k x i)). Qed.
Lemma lem4441610 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term783 A K z s k x i) = (term784 A K z s k x i).
Proof. exact (MK_COMB (@lem4441609 A K z s k x i) (@lem4441607 A K z s k x i)). Qed.
Lemma lem4441611 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term693 A K z s k x i) = (term783 A K z s k x i).
Proof. exact (@lem17045 (term677 A K z s k x i) (term673 A K z s k x i)). Qed.
Lemma lem4441612 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term693 A K z s k x i) = (term784 A K z s k x i).
Proof. exact (TRANS (@lem4441611 A K z s k x i) (@lem4441610 A K z s k x i)). Qed.
Lemma lem4441662 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4441663 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term152 K P Q) = (term153 K P Q).
Proof. exact (@lem4441662 K P Q). Qed.
Lemma lem4441664 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term785 A K z s k x i) = (term786 A K z s k x i).
Proof. exact (@lem4441663 K (term787 A K k x i z s) (term788 A K k x i)). Qed.
Lemma lem4441665 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term789 A K k x i z s i') = (term715 A K k x i z s i').
Proof. exact (eq_refl (term789 A K k x i z s i')). Qed.
Lemma lem4441666 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4441667 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term790 A K k x i z s i') = (term734 A K k x i z s i').
Proof. exact (MK_COMB (@lem4441666) (@lem4441665 A K k x i z s i')). Qed.
Lemma lem4441668 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term791 A K k x i i') = (term731 A K k x i' i).
Proof. exact (eq_refl (term791 A K k x i i')). Qed.
Lemma lem4441669 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term792 A K z s k x i i') = (term736 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4441667 A K k x i z s i') (@lem4441668 A K k x i' i)). Qed.
Lemma lem4441670 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term793 A K z s k x i) = (term744 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4441669 A K z s k x i' i)). Qed.
Lemma lem4441671 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4441672 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term785 A K z s k x i) = (term745 A K z s k x i).
Proof. exact (MK_COMB (@lem4441671 K) (@lem4441670 A K z s k x i)). Qed.
Lemma lem4441673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4441674 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term794 A K z s k x i) = (term795 A K z s k x i).
Proof. exact (MK_COMB (@lem4441673) (@lem4441672 A K z s k x i)). Qed.
Lemma lem4441675 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term789 A K k x i z s i') = (term715 A K k x i z s i').
Proof. exact (eq_refl (term789 A K k x i z s i')). Qed.
Lemma lem4441676 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term796 A K k x i z s) = (term787 A K k x i z s).
Proof. exact (fun_ext (fun i' : K => @lem4441675 A K k x i z s i')). Qed.
Lemma lem4441677 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4441678 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term797 A K k x i z s) = (term798 A K k x i z s).
Proof. exact (MK_COMB (@lem4441677 K) (@lem4441676 A K k x i z s)). Qed.
Lemma lem4441679 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4441680 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term799 A K k x i z s) = (term800 A K k x i z s).
Proof. exact (MK_COMB (@lem4441679) (@lem4441678 A K k x i z s)). Qed.
Lemma lem4441681 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term791 A K k x i i') = (term731 A K k x i' i).
Proof. exact (eq_refl (term791 A K k x i i')). Qed.
Lemma lem4441682 {A K : Type'} (k : K -> Prop) (x : A) (i : K) : (term801 A K k x i) = (term788 A K k x i).
Proof. exact (fun_ext (fun i' : K => @lem4441681 A K k x i' i)). Qed.
Lemma lem4441683 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4441684 {A K : Type'} (k : K -> Prop) (x : A) (i : K) : (term802 A K k x i) = (term803 A K k x i).
Proof. exact (MK_COMB (@lem4441683 K) (@lem4441682 A K k x i)). Qed.
Lemma lem4441685 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term786 A K z s k x i) = (term804 A K z s k x i).
Proof. exact (MK_COMB (@lem4441680 A K k x i z s) (@lem4441684 A K k x i)). Qed.
Lemma lem4441686 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term785 A K z s k x i) = (term786 A K z s k x i)) = ((term745 A K z s k x i) = (term804 A K z s k x i)).
Proof. exact (MK_COMB (@lem4441674 A K z s k x i) (@lem4441685 A K z s k x i)). Qed.
Lemma lem4441687 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term745 A K z s k x i) = (term804 A K z s k x i).
Proof. exact (EQ_MP (@lem4441686 A K z s k x i) (@lem4441664 A K z s k x i)). Qed.
Lemma lem4441784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441785 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term758 A K z s k x i) = (term805 A K z s k x i).
Proof. exact (MK_COMB (@lem4441784) (@lem4441687 A K z s k x i)). Qed.
Lemma lem4441791 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4441792 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (@lem4441791 A P Q). Qed.
Lemma lem4441793 {A : Type'} (x : A) : (term806 A x) = (term807 A x).
Proof. exact (@lem4441792 A (term808 A x) (term809 A x)). Qed.
Lemma lem4441794 {A : Type'} (x : A) (y : A) : (term810 A x y) = (term811 A x y).
Proof. exact (eq_refl (term810 A x y)). Qed.
Lemma lem4441795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441796 {A : Type'} (x : A) (y : A) : (term812 A x y) = (term813 A x y).
Proof. exact (MK_COMB (@lem4441795) (@lem4441794 A x y)). Qed.
Lemma lem4441797 {A : Type'} (x : A) (y : A) : (term814 A x y) = (term815 A x y).
Proof. exact (eq_refl (term814 A x y)). Qed.
Lemma lem4441798 {A : Type'} (x : A) (y : A) : (term816 A x y) = (term746 A x y).
Proof. exact (MK_COMB (@lem4441796 A x y) (@lem4441797 A x y)). Qed.
Lemma lem4441799 {A : Type'} (x : A) : (term817 A x) = (term747 A x).
Proof. exact (fun_ext (fun y : A => @lem4441798 A x y)). Qed.
Lemma lem4441800 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4441801 {A : Type'} (x : A) : (term806 A x) = (term748 A x).
Proof. exact (MK_COMB (@lem4441800 A) (@lem4441799 A x)). Qed.
Lemma lem4441802 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4441803 {A : Type'} (x : A) : (term818 A x) = (term819 A x).
Proof. exact (MK_COMB (@lem4441802) (@lem4441801 A x)). Qed.
Lemma lem4441804 {A : Type'} (x : A) (y : A) : (term810 A x y) = (term811 A x y).
Proof. exact (eq_refl (term810 A x y)). Qed.
Lemma lem4441805 {A : Type'} (x : A) : (term820 A x) = (term808 A x).
Proof. exact (fun_ext (fun y : A => @lem4441804 A x y)). Qed.
Lemma lem4441806 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4441807 {A : Type'} (x : A) : (term821 A x) = (term822 A x).
Proof. exact (MK_COMB (@lem4441806 A) (@lem4441805 A x)). Qed.
Lemma lem4441808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441809 {A : Type'} (x : A) : (term823 A x) = (term824 A x).
Proof. exact (MK_COMB (@lem4441808) (@lem4441807 A x)). Qed.
Lemma lem4441810 {A : Type'} (x : A) (y : A) : (term814 A x y) = (term815 A x y).
Proof. exact (eq_refl (term814 A x y)). Qed.
Lemma lem4441811 {A : Type'} (x : A) : (term825 A x) = (term809 A x).
Proof. exact (fun_ext (fun y : A => @lem4441810 A x y)). Qed.
Lemma lem4441812 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4441813 {A : Type'} (x : A) : (term826 A x) = (term827 A x).
Proof. exact (MK_COMB (@lem4441812 A) (@lem4441811 A x)). Qed.
Lemma lem4441814 {A : Type'} (x : A) : (term807 A x) = (term828 A x).
Proof. exact (MK_COMB (@lem4441809 A x) (@lem4441813 A x)). Qed.
Lemma lem4441815 {A : Type'} (x : A) : ((term806 A x) = (term807 A x)) = ((term748 A x) = (term828 A x)).
Proof. exact (MK_COMB (@lem4441803 A x) (@lem4441814 A x)). Qed.
Lemma lem4441816 {A : Type'} (x : A) : (term748 A x) = (term828 A x).
Proof. exact (EQ_MP (@lem4441815 A x) (@lem4441793 A x)). Qed.
Lemma lem4441913 {A : Type'} : (term749 A) = (term829 A).
Proof. exact (fun_ext (fun x : A => @lem4441816 A x)). Qed.
Lemma lem4441914 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4441915 {A : Type'} : (term750 A) = (term830 A).
Proof. exact (MK_COMB (@lem4441914 A) (@lem4441913 A)). Qed.
Lemma lem4441917 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4441918 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (@lem4441917 A P Q). Qed.
Lemma lem4441919 {A : Type'} : (term831 A) = (term832 A).
Proof. exact (@lem4441918 A (term833 A) (term834 A)). Qed.
Lemma lem4441920 {A : Type'} (x : A) : (term835 A x) = (term822 A x).
Proof. exact (eq_refl (term835 A x)). Qed.
Lemma lem4441921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441922 {A : Type'} (x : A) : (term836 A x) = (term824 A x).
Proof. exact (MK_COMB (@lem4441921) (@lem4441920 A x)). Qed.
Lemma lem4441923 {A : Type'} (x : A) : (term837 A x) = (term827 A x).
Proof. exact (eq_refl (term837 A x)). Qed.
Lemma lem4441924 {A : Type'} (x : A) : (term838 A x) = (term828 A x).
Proof. exact (MK_COMB (@lem4441922 A x) (@lem4441923 A x)). Qed.
Lemma lem4441925 {A : Type'} : (term839 A) = (term829 A).
Proof. exact (fun_ext (fun x : A => @lem4441924 A x)). Qed.
Lemma lem4441926 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4441927 {A : Type'} : (term831 A) = (term830 A).
Proof. exact (MK_COMB (@lem4441926 A) (@lem4441925 A)). Qed.
Lemma lem4441928 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4441929 {A : Type'} : (term840 A) = (term841 A).
Proof. exact (MK_COMB (@lem4441928) (@lem4441927 A)). Qed.
Lemma lem4441930 {A : Type'} (x : A) : (term835 A x) = (term822 A x).
Proof. exact (eq_refl (term835 A x)). Qed.
Lemma lem4441931 {A : Type'} : (term842 A) = (term833 A).
Proof. exact (fun_ext (fun x : A => @lem4441930 A x)). Qed.
Lemma lem4441932 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4441933 {A : Type'} : (term843 A) = (term844 A).
Proof. exact (MK_COMB (@lem4441932 A) (@lem4441931 A)). Qed.
Lemma lem4441934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4441935 {A : Type'} : (term845 A) = (term846 A).
Proof. exact (MK_COMB (@lem4441934) (@lem4441933 A)). Qed.
Lemma lem4441936 {A : Type'} (x : A) : (term837 A x) = (term827 A x).
Proof. exact (eq_refl (term837 A x)). Qed.
Lemma lem4441937 {A : Type'} : (term847 A) = (term834 A).
Proof. exact (fun_ext (fun x : A => @lem4441936 A x)). Qed.
Lemma lem4441938 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4441939 {A : Type'} : (term848 A) = (term849 A).
Proof. exact (MK_COMB (@lem4441938 A) (@lem4441937 A)). Qed.
Lemma lem4441940 {A : Type'} : (term832 A) = (term850 A).
Proof. exact (MK_COMB (@lem4441935 A) (@lem4441939 A)). Qed.
Lemma lem4441941 {A : Type'} : ((term831 A) = (term832 A)) = ((term830 A) = (term850 A)).
Proof. exact (MK_COMB (@lem4441929 A) (@lem4441940 A)). Qed.
Lemma lem4441942 {A : Type'} : (term830 A) = (term850 A).
Proof. exact (EQ_MP (@lem4441941 A) (@lem4441919 A)). Qed.
Lemma lem4442047 {A : Type'} : (term750 A) = (term850 A).
Proof. exact (TRANS (@lem4441915 A) (@lem4441942 A)). Qed.
Lemma lem4442048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442049 {A : Type'} : (term753 A) = (term851 A).
Proof. exact (MK_COMB (@lem4442048) (@lem4442047 A)). Qed.
Lemma lem4442055 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4442056 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term130 K P Q) = (term131 K P Q).
Proof. exact (@lem4442055 K P Q). Qed.
Lemma lem4442057 {K : Type'} (x : K) : (term806 K x) = (term807 K x).
Proof. exact (@lem4442056 K (term808 K x) (term809 K x)). Qed.
Lemma lem4442058 {K : Type'} (x : K) (y : K) : (term810 K x y) = (term811 K x y).
Proof. exact (eq_refl (term810 K x y)). Qed.
Lemma lem4442059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442060 {K : Type'} (x : K) (y : K) : (term812 K x y) = (term813 K x y).
Proof. exact (MK_COMB (@lem4442059) (@lem4442058 K x y)). Qed.
Lemma lem4442061 {K : Type'} (x : K) (y : K) : (term814 K x y) = (term815 K x y).
Proof. exact (eq_refl (term814 K x y)). Qed.
Lemma lem4442062 {K : Type'} (x : K) (y : K) : (term816 K x y) = (term746 K x y).
Proof. exact (MK_COMB (@lem4442060 K x y) (@lem4442061 K x y)). Qed.
Lemma lem4442063 {K : Type'} (x : K) : (term817 K x) = (term747 K x).
Proof. exact (fun_ext (fun y : K => @lem4442062 K x y)). Qed.
Lemma lem4442064 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442065 {K : Type'} (x : K) : (term806 K x) = (term748 K x).
Proof. exact (MK_COMB (@lem4442064 K) (@lem4442063 K x)). Qed.
Lemma lem4442066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4442067 {K : Type'} (x : K) : (term818 K x) = (term819 K x).
Proof. exact (MK_COMB (@lem4442066) (@lem4442065 K x)). Qed.
Lemma lem4442068 {K : Type'} (x : K) (y : K) : (term810 K x y) = (term811 K x y).
Proof. exact (eq_refl (term810 K x y)). Qed.
Lemma lem4442069 {K : Type'} (x : K) : (term820 K x) = (term808 K x).
Proof. exact (fun_ext (fun y : K => @lem4442068 K x y)). Qed.
Lemma lem4442070 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442071 {K : Type'} (x : K) : (term821 K x) = (term822 K x).
Proof. exact (MK_COMB (@lem4442070 K) (@lem4442069 K x)). Qed.
Lemma lem4442072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442073 {K : Type'} (x : K) : (term823 K x) = (term824 K x).
Proof. exact (MK_COMB (@lem4442072) (@lem4442071 K x)). Qed.
Lemma lem4442074 {K : Type'} (x : K) (y : K) : (term814 K x y) = (term815 K x y).
Proof. exact (eq_refl (term814 K x y)). Qed.
Lemma lem4442075 {K : Type'} (x : K) : (term825 K x) = (term809 K x).
Proof. exact (fun_ext (fun y : K => @lem4442074 K x y)). Qed.
Lemma lem4442076 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442077 {K : Type'} (x : K) : (term826 K x) = (term827 K x).
Proof. exact (MK_COMB (@lem4442076 K) (@lem4442075 K x)). Qed.
Lemma lem4442078 {K : Type'} (x : K) : (term807 K x) = (term828 K x).
Proof. exact (MK_COMB (@lem4442073 K x) (@lem4442077 K x)). Qed.
Lemma lem4442079 {K : Type'} (x : K) : ((term806 K x) = (term807 K x)) = ((term748 K x) = (term828 K x)).
Proof. exact (MK_COMB (@lem4442067 K x) (@lem4442078 K x)). Qed.
Lemma lem4442080 {K : Type'} (x : K) : (term748 K x) = (term828 K x).
Proof. exact (EQ_MP (@lem4442079 K x) (@lem4442057 K x)). Qed.
Lemma lem4442177 {K : Type'} : (term749 K) = (term829 K).
Proof. exact (fun_ext (fun x : K => @lem4442080 K x)). Qed.
Lemma lem4442178 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442179 {K : Type'} : (term750 K) = (term830 K).
Proof. exact (MK_COMB (@lem4442178 K) (@lem4442177 K)). Qed.
Lemma lem4442181 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4442182 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term130 K P Q) = (term131 K P Q).
Proof. exact (@lem4442181 K P Q). Qed.
Lemma lem4442183 {K : Type'} : (term831 K) = (term832 K).
Proof. exact (@lem4442182 K (term833 K) (term834 K)). Qed.
Lemma lem4442184 {K : Type'} (x : K) : (term835 K x) = (term822 K x).
Proof. exact (eq_refl (term835 K x)). Qed.
Lemma lem4442185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442186 {K : Type'} (x : K) : (term836 K x) = (term824 K x).
Proof. exact (MK_COMB (@lem4442185) (@lem4442184 K x)). Qed.
Lemma lem4442187 {K : Type'} (x : K) : (term837 K x) = (term827 K x).
Proof. exact (eq_refl (term837 K x)). Qed.
Lemma lem4442188 {K : Type'} (x : K) : (term838 K x) = (term828 K x).
Proof. exact (MK_COMB (@lem4442186 K x) (@lem4442187 K x)). Qed.
Lemma lem4442189 {K : Type'} : (term839 K) = (term829 K).
Proof. exact (fun_ext (fun x : K => @lem4442188 K x)). Qed.
Lemma lem4442190 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442191 {K : Type'} : (term831 K) = (term830 K).
Proof. exact (MK_COMB (@lem4442190 K) (@lem4442189 K)). Qed.
Lemma lem4442192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4442193 {K : Type'} : (term840 K) = (term841 K).
Proof. exact (MK_COMB (@lem4442192) (@lem4442191 K)). Qed.
Lemma lem4442194 {K : Type'} (x : K) : (term835 K x) = (term822 K x).
Proof. exact (eq_refl (term835 K x)). Qed.
Lemma lem4442195 {K : Type'} : (term842 K) = (term833 K).
Proof. exact (fun_ext (fun x : K => @lem4442194 K x)). Qed.
Lemma lem4442196 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442197 {K : Type'} : (term843 K) = (term844 K).
Proof. exact (MK_COMB (@lem4442196 K) (@lem4442195 K)). Qed.
Lemma lem4442198 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442199 {K : Type'} : (term845 K) = (term846 K).
Proof. exact (MK_COMB (@lem4442198) (@lem4442197 K)). Qed.
Lemma lem4442200 {K : Type'} (x : K) : (term837 K x) = (term827 K x).
Proof. exact (eq_refl (term837 K x)). Qed.
Lemma lem4442201 {K : Type'} : (term847 K) = (term834 K).
Proof. exact (fun_ext (fun x : K => @lem4442200 K x)). Qed.
Lemma lem4442202 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442203 {K : Type'} : (term848 K) = (term849 K).
Proof. exact (MK_COMB (@lem4442202 K) (@lem4442201 K)). Qed.
Lemma lem4442204 {K : Type'} : (term832 K) = (term850 K).
Proof. exact (MK_COMB (@lem4442199 K) (@lem4442203 K)). Qed.
Lemma lem4442205 {K : Type'} : ((term831 K) = (term832 K)) = ((term830 K) = (term850 K)).
Proof. exact (MK_COMB (@lem4442193 K) (@lem4442204 K)). Qed.
Lemma lem4442206 {K : Type'} : (term830 K) = (term850 K).
Proof. exact (EQ_MP (@lem4442205 K) (@lem4442183 K)). Qed.
Lemma lem4442311 {K : Type'} : (term750 K) = (term850 K).
Proof. exact (TRANS (@lem4442179 K) (@lem4442206 K)). Qed.
Lemma lem4442312 {A K : Type'} : (term755 A K) = (term852 A K).
Proof. exact (MK_COMB (@lem4442049 A) (@lem4442311 K)). Qed.
Lemma lem4442313 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term760 A K z s k x i) = (term853 A K z s k x i).
Proof. exact (MK_COMB (@lem4441785 A K z s k x i) (@lem4442312 A K)). Qed.
Lemma lem4442314 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term763 A K k z s) = (term763 A K k z s).
Proof. exact (eq_refl (term763 A K k z s)). Qed.
Lemma lem4442315 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term765 A K z s k x i) = (term854 A K z s k x i).
Proof. exact (MK_COMB (@lem4442314 A K k z s) (@lem4442313 A K z s k x i)). Qed.
Lemma lem4442316 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term767 A K x s i) = (term767 A K x s i).
Proof. exact (eq_refl (term767 A K x s i)). Qed.
Lemma lem4442317 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term769 A K z s k x i) = (term855 A K z s k x i).
Proof. exact (MK_COMB (@lem4442316 A K x s i) (@lem4442315 A K z s k x i)). Qed.
Lemma lem4442318 {K : Type'} (i : K) (k : K -> Prop) : (term22 K i k) = (term22 K i k).
Proof. exact (eq_refl (term22 K i k)). Qed.
Lemma lem4442319 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term772 A K z s k x i) = (term856 A K z s k x i).
Proof. exact (MK_COMB (@lem4442318 K i k) (@lem4442317 A K z s k x i)). Qed.
Lemma lem4442320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4442321 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term782 A K z s k x i) = (term857 A K z s k x i).
Proof. exact (MK_COMB (@lem4442320) (@lem4442319 A K z s k x i)). Qed.
Lemma lem4442371 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4442372 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term152 K P Q) = (term153 K P Q).
Proof. exact (@lem4442371 K P Q). Qed.
Lemma lem4442373 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term785 A K z s k x i) = (term786 A K z s k x i).
Proof. exact (@lem4442372 K (term787 A K k x i z s) (term788 A K k x i)). Qed.
Lemma lem4442374 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term789 A K k x i z s i') = (term715 A K k x i z s i').
Proof. exact (eq_refl (term789 A K k x i z s i')). Qed.
Lemma lem4442375 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4442376 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term790 A K k x i z s i') = (term734 A K k x i z s i').
Proof. exact (MK_COMB (@lem4442375) (@lem4442374 A K k x i z s i')). Qed.
Lemma lem4442377 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term791 A K k x i i') = (term731 A K k x i' i).
Proof. exact (eq_refl (term791 A K k x i i')). Qed.
Lemma lem4442378 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term792 A K z s k x i i') = (term736 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4442376 A K k x i z s i') (@lem4442377 A K k x i' i)). Qed.
Lemma lem4442379 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term793 A K z s k x i) = (term744 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4442378 A K z s k x i' i)). Qed.
Lemma lem4442380 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4442381 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term785 A K z s k x i) = (term745 A K z s k x i).
Proof. exact (MK_COMB (@lem4442380 K) (@lem4442379 A K z s k x i)). Qed.
Lemma lem4442382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4442383 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term794 A K z s k x i) = (term795 A K z s k x i).
Proof. exact (MK_COMB (@lem4442382) (@lem4442381 A K z s k x i)). Qed.
Lemma lem4442384 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term789 A K k x i z s i') = (term715 A K k x i z s i').
Proof. exact (eq_refl (term789 A K k x i z s i')). Qed.
Lemma lem4442385 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term796 A K k x i z s) = (term787 A K k x i z s).
Proof. exact (fun_ext (fun i' : K => @lem4442384 A K k x i z s i')). Qed.
Lemma lem4442386 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4442387 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term797 A K k x i z s) = (term798 A K k x i z s).
Proof. exact (MK_COMB (@lem4442386 K) (@lem4442385 A K k x i z s)). Qed.
Lemma lem4442388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4442389 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term799 A K k x i z s) = (term800 A K k x i z s).
Proof. exact (MK_COMB (@lem4442388) (@lem4442387 A K k x i z s)). Qed.
Lemma lem4442390 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term791 A K k x i i') = (term731 A K k x i' i).
Proof. exact (eq_refl (term791 A K k x i i')). Qed.
Lemma lem4442391 {A K : Type'} (k : K -> Prop) (x : A) (i : K) : (term801 A K k x i) = (term788 A K k x i).
Proof. exact (fun_ext (fun i' : K => @lem4442390 A K k x i' i)). Qed.
Lemma lem4442392 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4442393 {A K : Type'} (k : K -> Prop) (x : A) (i : K) : (term802 A K k x i) = (term803 A K k x i).
Proof. exact (MK_COMB (@lem4442392 K) (@lem4442391 A K k x i)). Qed.
Lemma lem4442394 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term786 A K z s k x i) = (term804 A K z s k x i).
Proof. exact (MK_COMB (@lem4442389 A K k x i z s) (@lem4442393 A K k x i)). Qed.
Lemma lem4442395 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term785 A K z s k x i) = (term786 A K z s k x i)) = ((term745 A K z s k x i) = (term804 A K z s k x i)).
Proof. exact (MK_COMB (@lem4442383 A K z s k x i) (@lem4442394 A K z s k x i)). Qed.
Lemma lem4442396 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term745 A K z s k x i) = (term804 A K z s k x i).
Proof. exact (EQ_MP (@lem4442395 A K z s k x i) (@lem4442373 A K z s k x i)). Qed.
Lemma lem4442493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442494 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term758 A K z s k x i) = (term805 A K z s k x i).
Proof. exact (MK_COMB (@lem4442493) (@lem4442396 A K z s k x i)). Qed.
Lemma lem4442500 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4442501 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (@lem4442500 A P Q). Qed.
Lemma lem4442502 {A : Type'} (x : A) : (term806 A x) = (term807 A x).
Proof. exact (@lem4442501 A (term808 A x) (term809 A x)). Qed.
Lemma lem4442503 {A : Type'} (x : A) (y : A) : (term810 A x y) = (term811 A x y).
Proof. exact (eq_refl (term810 A x y)). Qed.
Lemma lem4442504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442505 {A : Type'} (x : A) (y : A) : (term812 A x y) = (term813 A x y).
Proof. exact (MK_COMB (@lem4442504) (@lem4442503 A x y)). Qed.
Lemma lem4442506 {A : Type'} (x : A) (y : A) : (term814 A x y) = (term815 A x y).
Proof. exact (eq_refl (term814 A x y)). Qed.
Lemma lem4442507 {A : Type'} (x : A) (y : A) : (term816 A x y) = (term746 A x y).
Proof. exact (MK_COMB (@lem4442505 A x y) (@lem4442506 A x y)). Qed.
Lemma lem4442508 {A : Type'} (x : A) : (term817 A x) = (term747 A x).
Proof. exact (fun_ext (fun y : A => @lem4442507 A x y)). Qed.
Lemma lem4442509 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4442510 {A : Type'} (x : A) : (term806 A x) = (term748 A x).
Proof. exact (MK_COMB (@lem4442509 A) (@lem4442508 A x)). Qed.
Lemma lem4442511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4442512 {A : Type'} (x : A) : (term818 A x) = (term819 A x).
Proof. exact (MK_COMB (@lem4442511) (@lem4442510 A x)). Qed.
Lemma lem4442513 {A : Type'} (x : A) (y : A) : (term810 A x y) = (term811 A x y).
Proof. exact (eq_refl (term810 A x y)). Qed.
Lemma lem4442514 {A : Type'} (x : A) : (term820 A x) = (term808 A x).
Proof. exact (fun_ext (fun y : A => @lem4442513 A x y)). Qed.
Lemma lem4442515 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4442516 {A : Type'} (x : A) : (term821 A x) = (term822 A x).
Proof. exact (MK_COMB (@lem4442515 A) (@lem4442514 A x)). Qed.
Lemma lem4442517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442518 {A : Type'} (x : A) : (term823 A x) = (term824 A x).
Proof. exact (MK_COMB (@lem4442517) (@lem4442516 A x)). Qed.
Lemma lem4442519 {A : Type'} (x : A) (y : A) : (term814 A x y) = (term815 A x y).
Proof. exact (eq_refl (term814 A x y)). Qed.
Lemma lem4442520 {A : Type'} (x : A) : (term825 A x) = (term809 A x).
Proof. exact (fun_ext (fun y : A => @lem4442519 A x y)). Qed.
Lemma lem4442521 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4442522 {A : Type'} (x : A) : (term826 A x) = (term827 A x).
Proof. exact (MK_COMB (@lem4442521 A) (@lem4442520 A x)). Qed.
Lemma lem4442523 {A : Type'} (x : A) : (term807 A x) = (term828 A x).
Proof. exact (MK_COMB (@lem4442518 A x) (@lem4442522 A x)). Qed.
Lemma lem4442524 {A : Type'} (x : A) : ((term806 A x) = (term807 A x)) = ((term748 A x) = (term828 A x)).
Proof. exact (MK_COMB (@lem4442512 A x) (@lem4442523 A x)). Qed.
Lemma lem4442525 {A : Type'} (x : A) : (term748 A x) = (term828 A x).
Proof. exact (EQ_MP (@lem4442524 A x) (@lem4442502 A x)). Qed.
Lemma lem4442622 {A : Type'} : (term749 A) = (term829 A).
Proof. exact (fun_ext (fun x : A => @lem4442525 A x)). Qed.
Lemma lem4442623 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4442624 {A : Type'} : (term750 A) = (term830 A).
Proof. exact (MK_COMB (@lem4442623 A) (@lem4442622 A)). Qed.
Lemma lem4442626 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4442627 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (@lem4442626 A P Q). Qed.
Lemma lem4442628 {A : Type'} : (term831 A) = (term832 A).
Proof. exact (@lem4442627 A (term833 A) (term834 A)). Qed.
Lemma lem4442629 {A : Type'} (x : A) : (term835 A x) = (term822 A x).
Proof. exact (eq_refl (term835 A x)). Qed.
Lemma lem4442630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442631 {A : Type'} (x : A) : (term836 A x) = (term824 A x).
Proof. exact (MK_COMB (@lem4442630) (@lem4442629 A x)). Qed.
Lemma lem4442632 {A : Type'} (x : A) : (term837 A x) = (term827 A x).
Proof. exact (eq_refl (term837 A x)). Qed.
Lemma lem4442633 {A : Type'} (x : A) : (term838 A x) = (term828 A x).
Proof. exact (MK_COMB (@lem4442631 A x) (@lem4442632 A x)). Qed.
Lemma lem4442634 {A : Type'} : (term839 A) = (term829 A).
Proof. exact (fun_ext (fun x : A => @lem4442633 A x)). Qed.
Lemma lem4442635 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4442636 {A : Type'} : (term831 A) = (term830 A).
Proof. exact (MK_COMB (@lem4442635 A) (@lem4442634 A)). Qed.
Lemma lem4442637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4442638 {A : Type'} : (term840 A) = (term841 A).
Proof. exact (MK_COMB (@lem4442637) (@lem4442636 A)). Qed.
Lemma lem4442639 {A : Type'} (x : A) : (term835 A x) = (term822 A x).
Proof. exact (eq_refl (term835 A x)). Qed.
Lemma lem4442640 {A : Type'} : (term842 A) = (term833 A).
Proof. exact (fun_ext (fun x : A => @lem4442639 A x)). Qed.
Lemma lem4442641 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4442642 {A : Type'} : (term843 A) = (term844 A).
Proof. exact (MK_COMB (@lem4442641 A) (@lem4442640 A)). Qed.
Lemma lem4442643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442644 {A : Type'} : (term845 A) = (term846 A).
Proof. exact (MK_COMB (@lem4442643) (@lem4442642 A)). Qed.
Lemma lem4442645 {A : Type'} (x : A) : (term837 A x) = (term827 A x).
Proof. exact (eq_refl (term837 A x)). Qed.
Lemma lem4442646 {A : Type'} : (term847 A) = (term834 A).
Proof. exact (fun_ext (fun x : A => @lem4442645 A x)). Qed.
Lemma lem4442647 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4442648 {A : Type'} : (term848 A) = (term849 A).
Proof. exact (MK_COMB (@lem4442647 A) (@lem4442646 A)). Qed.
Lemma lem4442649 {A : Type'} : (term832 A) = (term850 A).
Proof. exact (MK_COMB (@lem4442644 A) (@lem4442648 A)). Qed.
Lemma lem4442650 {A : Type'} : ((term831 A) = (term832 A)) = ((term830 A) = (term850 A)).
Proof. exact (MK_COMB (@lem4442638 A) (@lem4442649 A)). Qed.
Lemma lem4442651 {A : Type'} : (term830 A) = (term850 A).
Proof. exact (EQ_MP (@lem4442650 A) (@lem4442628 A)). Qed.
Lemma lem4442756 {A : Type'} : (term750 A) = (term850 A).
Proof. exact (TRANS (@lem4442624 A) (@lem4442651 A)). Qed.
Lemma lem4442757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442758 {A : Type'} : (term753 A) = (term851 A).
Proof. exact (MK_COMB (@lem4442757) (@lem4442756 A)). Qed.
Lemma lem4442764 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4442765 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term130 K P Q) = (term131 K P Q).
Proof. exact (@lem4442764 K P Q). Qed.
Lemma lem4442766 {K : Type'} (x : K) : (term806 K x) = (term807 K x).
Proof. exact (@lem4442765 K (term808 K x) (term809 K x)). Qed.
Lemma lem4442767 {K : Type'} (x : K) (y : K) : (term810 K x y) = (term811 K x y).
Proof. exact (eq_refl (term810 K x y)). Qed.
Lemma lem4442768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442769 {K : Type'} (x : K) (y : K) : (term812 K x y) = (term813 K x y).
Proof. exact (MK_COMB (@lem4442768) (@lem4442767 K x y)). Qed.
Lemma lem4442770 {K : Type'} (x : K) (y : K) : (term814 K x y) = (term815 K x y).
Proof. exact (eq_refl (term814 K x y)). Qed.
Lemma lem4442771 {K : Type'} (x : K) (y : K) : (term816 K x y) = (term746 K x y).
Proof. exact (MK_COMB (@lem4442769 K x y) (@lem4442770 K x y)). Qed.
Lemma lem4442772 {K : Type'} (x : K) : (term817 K x) = (term747 K x).
Proof. exact (fun_ext (fun y : K => @lem4442771 K x y)). Qed.
Lemma lem4442773 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442774 {K : Type'} (x : K) : (term806 K x) = (term748 K x).
Proof. exact (MK_COMB (@lem4442773 K) (@lem4442772 K x)). Qed.
Lemma lem4442775 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4442776 {K : Type'} (x : K) : (term818 K x) = (term819 K x).
Proof. exact (MK_COMB (@lem4442775) (@lem4442774 K x)). Qed.
Lemma lem4442777 {K : Type'} (x : K) (y : K) : (term810 K x y) = (term811 K x y).
Proof. exact (eq_refl (term810 K x y)). Qed.
Lemma lem4442778 {K : Type'} (x : K) : (term820 K x) = (term808 K x).
Proof. exact (fun_ext (fun y : K => @lem4442777 K x y)). Qed.
Lemma lem4442779 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442780 {K : Type'} (x : K) : (term821 K x) = (term822 K x).
Proof. exact (MK_COMB (@lem4442779 K) (@lem4442778 K x)). Qed.
Lemma lem4442781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442782 {K : Type'} (x : K) : (term823 K x) = (term824 K x).
Proof. exact (MK_COMB (@lem4442781) (@lem4442780 K x)). Qed.
Lemma lem4442783 {K : Type'} (x : K) (y : K) : (term814 K x y) = (term815 K x y).
Proof. exact (eq_refl (term814 K x y)). Qed.
Lemma lem4442784 {K : Type'} (x : K) : (term825 K x) = (term809 K x).
Proof. exact (fun_ext (fun y : K => @lem4442783 K x y)). Qed.
Lemma lem4442785 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442786 {K : Type'} (x : K) : (term826 K x) = (term827 K x).
Proof. exact (MK_COMB (@lem4442785 K) (@lem4442784 K x)). Qed.
Lemma lem4442787 {K : Type'} (x : K) : (term807 K x) = (term828 K x).
Proof. exact (MK_COMB (@lem4442782 K x) (@lem4442786 K x)). Qed.
Lemma lem4442788 {K : Type'} (x : K) : ((term806 K x) = (term807 K x)) = ((term748 K x) = (term828 K x)).
Proof. exact (MK_COMB (@lem4442776 K x) (@lem4442787 K x)). Qed.
Lemma lem4442789 {K : Type'} (x : K) : (term748 K x) = (term828 K x).
Proof. exact (EQ_MP (@lem4442788 K x) (@lem4442766 K x)). Qed.
Lemma lem4442886 {K : Type'} : (term749 K) = (term829 K).
Proof. exact (fun_ext (fun x : K => @lem4442789 K x)). Qed.
Lemma lem4442887 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442888 {K : Type'} : (term750 K) = (term830 K).
Proof. exact (MK_COMB (@lem4442887 K) (@lem4442886 K)). Qed.
Lemma lem4442890 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4442891 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term130 K P Q) = (term131 K P Q).
Proof. exact (@lem4442890 K P Q). Qed.
Lemma lem4442892 {K : Type'} : (term831 K) = (term832 K).
Proof. exact (@lem4442891 K (term833 K) (term834 K)). Qed.
Lemma lem4442893 {K : Type'} (x : K) : (term835 K x) = (term822 K x).
Proof. exact (eq_refl (term835 K x)). Qed.
Lemma lem4442894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442895 {K : Type'} (x : K) : (term836 K x) = (term824 K x).
Proof. exact (MK_COMB (@lem4442894) (@lem4442893 K x)). Qed.
Lemma lem4442896 {K : Type'} (x : K) : (term837 K x) = (term827 K x).
Proof. exact (eq_refl (term837 K x)). Qed.
Lemma lem4442897 {K : Type'} (x : K) : (term838 K x) = (term828 K x).
Proof. exact (MK_COMB (@lem4442895 K x) (@lem4442896 K x)). Qed.
Lemma lem4442898 {K : Type'} : (term839 K) = (term829 K).
Proof. exact (fun_ext (fun x : K => @lem4442897 K x)). Qed.
Lemma lem4442899 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442900 {K : Type'} : (term831 K) = (term830 K).
Proof. exact (MK_COMB (@lem4442899 K) (@lem4442898 K)). Qed.
Lemma lem4442901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4442902 {K : Type'} : (term840 K) = (term841 K).
Proof. exact (MK_COMB (@lem4442901) (@lem4442900 K)). Qed.
Lemma lem4442903 {K : Type'} (x : K) : (term835 K x) = (term822 K x).
Proof. exact (eq_refl (term835 K x)). Qed.
Lemma lem4442904 {K : Type'} : (term842 K) = (term833 K).
Proof. exact (fun_ext (fun x : K => @lem4442903 K x)). Qed.
Lemma lem4442905 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442906 {K : Type'} : (term843 K) = (term844 K).
Proof. exact (MK_COMB (@lem4442905 K) (@lem4442904 K)). Qed.
Lemma lem4442907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4442908 {K : Type'} : (term845 K) = (term846 K).
Proof. exact (MK_COMB (@lem4442907) (@lem4442906 K)). Qed.
Lemma lem4442909 {K : Type'} (x : K) : (term837 K x) = (term827 K x).
Proof. exact (eq_refl (term837 K x)). Qed.
Lemma lem4442910 {K : Type'} : (term847 K) = (term834 K).
Proof. exact (fun_ext (fun x : K => @lem4442909 K x)). Qed.
Lemma lem4442911 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4442912 {K : Type'} : (term848 K) = (term849 K).
Proof. exact (MK_COMB (@lem4442911 K) (@lem4442910 K)). Qed.
Lemma lem4442913 {K : Type'} : (term832 K) = (term850 K).
Proof. exact (MK_COMB (@lem4442908 K) (@lem4442912 K)). Qed.
Lemma lem4442914 {K : Type'} : ((term831 K) = (term832 K)) = ((term830 K) = (term850 K)).
Proof. exact (MK_COMB (@lem4442902 K) (@lem4442913 K)). Qed.
Lemma lem4442915 {K : Type'} : (term830 K) = (term850 K).
Proof. exact (EQ_MP (@lem4442914 K) (@lem4442892 K)). Qed.
Lemma lem4443020 {K : Type'} : (term750 K) = (term850 K).
Proof. exact (TRANS (@lem4442888 K) (@lem4442915 K)). Qed.
Lemma lem4443021 {A K : Type'} : (term755 A K) = (term852 A K).
Proof. exact (MK_COMB (@lem4442758 A) (@lem4443020 K)). Qed.
Lemma lem4443022 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term760 A K z s k x i) = (term853 A K z s k x i).
Proof. exact (MK_COMB (@lem4442494 A K z s k x i) (@lem4443021 A K)). Qed.
Lemma lem4443023 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term763 A K k z s) = (term763 A K k z s).
Proof. exact (eq_refl (term763 A K k z s)). Qed.
Lemma lem4443024 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term765 A K z s k x i) = (term854 A K z s k x i).
Proof. exact (MK_COMB (@lem4443023 A K k z s) (@lem4443022 A K z s k x i)). Qed.
Lemma lem4443025 {A : Type'} (x : A) : (term774 A x) = (term774 A x).
Proof. exact (eq_refl (term774 A x)). Qed.
Lemma lem4443026 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term776 A K z s k x i) = (term858 A K z s k x i).
Proof. exact (MK_COMB (@lem4443025 A x) (@lem4443024 A K z s k x i)). Qed.
Lemma lem4443027 {K : Type'} (i : K) (k : K -> Prop) : (term729 K i k) = (term729 K i k).
Proof. exact (eq_refl (term729 K i k)). Qed.
Lemma lem4443028 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term779 A K z s k x i) = (term859 A K z s k x i).
Proof. exact (MK_COMB (@lem4443027 K i k) (@lem4443026 A K z s k x i)). Qed.
Lemma lem4443029 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term784 A K z s k x i) = (term860 A K z s k x i).
Proof. exact (MK_COMB (@lem4442321 A K z s k x i) (@lem4443028 A K z s k x i)). Qed.
Lemma lem4443031 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term153 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4443032 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term153 K P Q) = (term152 K P Q).
Proof. exact (@lem4443031 K P Q). Qed.
Lemma lem4443033 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term786 A K z s k x i) = (term785 A K z s k x i).
Proof. exact (@lem4443032 K (term787 A K k x i z s) (term788 A K k x i)). Qed.
Lemma lem4443034 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term789 A K k x i z s i') = (term715 A K k x i z s i').
Proof. exact (eq_refl (term789 A K k x i z s i')). Qed.
Lemma lem4443035 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term796 A K k x i z s) = (term787 A K k x i z s).
Proof. exact (fun_ext (fun i' : K => @lem4443034 A K k x i z s i')). Qed.
Lemma lem4443036 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443037 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term797 A K k x i z s) = (term798 A K k x i z s).
Proof. exact (MK_COMB (@lem4443036 K) (@lem4443035 A K k x i z s)). Qed.
Lemma lem4443038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4443039 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term799 A K k x i z s) = (term800 A K k x i z s).
Proof. exact (MK_COMB (@lem4443038) (@lem4443037 A K k x i z s)). Qed.
Lemma lem4443040 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term791 A K k x i i') = (term731 A K k x i' i).
Proof. exact (eq_refl (term791 A K k x i i')). Qed.
Lemma lem4443041 {A K : Type'} (k : K -> Prop) (x : A) (i : K) : (term801 A K k x i) = (term788 A K k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443040 A K k x i' i)). Qed.
Lemma lem4443042 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443043 {A K : Type'} (k : K -> Prop) (x : A) (i : K) : (term802 A K k x i) = (term803 A K k x i).
Proof. exact (MK_COMB (@lem4443042 K) (@lem4443041 A K k x i)). Qed.
Lemma lem4443044 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term786 A K z s k x i) = (term804 A K z s k x i).
Proof. exact (MK_COMB (@lem4443039 A K k x i z s) (@lem4443043 A K k x i)). Qed.
Lemma lem4443045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4443046 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term861 A K z s k x i) = (term862 A K z s k x i).
Proof. exact (MK_COMB (@lem4443045) (@lem4443044 A K z s k x i)). Qed.
Lemma lem4443047 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term789 A K k x i z s i') = (term715 A K k x i z s i').
Proof. exact (eq_refl (term789 A K k x i z s i')). Qed.
Lemma lem4443048 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4443049 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term790 A K k x i z s i') = (term734 A K k x i z s i').
Proof. exact (MK_COMB (@lem4443048) (@lem4443047 A K k x i z s i')). Qed.
Lemma lem4443050 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term791 A K k x i i') = (term731 A K k x i' i).
Proof. exact (eq_refl (term791 A K k x i i')). Qed.
Lemma lem4443051 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term792 A K z s k x i i') = (term736 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443049 A K k x i z s i') (@lem4443050 A K k x i' i)). Qed.
Lemma lem4443052 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term793 A K z s k x i) = (term744 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443051 A K z s k x i' i)). Qed.
Lemma lem4443053 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443054 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term785 A K z s k x i) = (term745 A K z s k x i).
Proof. exact (MK_COMB (@lem4443053 K) (@lem4443052 A K z s k x i)). Qed.
Lemma lem4443055 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term786 A K z s k x i) = (term785 A K z s k x i)) = ((term804 A K z s k x i) = (term745 A K z s k x i)).
Proof. exact (MK_COMB (@lem4443046 A K z s k x i) (@lem4443054 A K z s k x i)). Qed.
Lemma lem4443056 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term804 A K z s k x i) = (term745 A K z s k x i).
Proof. exact (EQ_MP (@lem4443055 A K z s k x i) (@lem4443033 A K z s k x i)). Qed.
Lemma lem4443057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443058 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term805 A K z s k x i) = (term758 A K z s k x i).
Proof. exact (MK_COMB (@lem4443057) (@lem4443056 A K z s k x i)). Qed.
Lemma lem4443059 {A K : Type'} : (term852 A K) = (term852 A K).
Proof. exact (eq_refl (term852 A K)). Qed.
Lemma lem4443060 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term853 A K z s k x i) = (term863 A K z s k x i).
Proof. exact (MK_COMB (@lem4443058 A K z s k x i) (@lem4443059 A K)). Qed.
Lemma lem4443062 {A : Type'} (P : A -> Prop) (Q : Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4443063 {K : Type'} (P : K -> Prop) (Q : Prop) : (term209 K P Q) = (term210 K P Q).
Proof. exact (@lem4443062 K P Q). Qed.
Lemma lem4443064 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term864 A K z s k x i) = (term865 A K z s k x i).
Proof. exact (@lem4443063 K (term744 A K z s k x i) (term852 A K)). Qed.
Lemma lem4443065 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term866 A K z s k x i i') = (term736 A K z s k x i' i).
Proof. exact (eq_refl (term866 A K z s k x i i')). Qed.
Lemma lem4443066 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term867 A K z s k x i) = (term744 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443065 A K z s k x i' i)). Qed.
Lemma lem4443067 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443068 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term868 A K z s k x i) = (term745 A K z s k x i).
Proof. exact (MK_COMB (@lem4443067 K) (@lem4443066 A K z s k x i)). Qed.
Lemma lem4443069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443070 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term869 A K z s k x i) = (term758 A K z s k x i).
Proof. exact (MK_COMB (@lem4443069) (@lem4443068 A K z s k x i)). Qed.
Lemma lem4443071 {A K : Type'} : (term852 A K) = (term852 A K).
Proof. exact (eq_refl (term852 A K)). Qed.
Lemma lem4443072 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term864 A K z s k x i) = (term863 A K z s k x i).
Proof. exact (MK_COMB (@lem4443070 A K z s k x i) (@lem4443071 A K)). Qed.
Lemma lem4443073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4443074 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term870 A K z s k x i) = (term871 A K z s k x i).
Proof. exact (MK_COMB (@lem4443073) (@lem4443072 A K z s k x i)). Qed.
Lemma lem4443075 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term866 A K z s k x i i') = (term736 A K z s k x i' i).
Proof. exact (eq_refl (term866 A K z s k x i i')). Qed.
Lemma lem4443076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443077 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term872 A K z s k x i i') = (term873 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443076) (@lem4443075 A K z s k x i' i)). Qed.
Lemma lem4443078 {A K : Type'} : (term852 A K) = (term852 A K).
Proof. exact (eq_refl (term852 A K)). Qed.
Lemma lem4443079 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term874 A K z s k x i i') = (term875 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443077 A K z s k x i' i) (@lem4443078 A K)). Qed.
Lemma lem4443080 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term876 A K z s k x i) = (term877 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443079 A K z s k x i' i)). Qed.
Lemma lem4443081 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443082 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term865 A K z s k x i) = (term878 A K z s k x i).
Proof. exact (MK_COMB (@lem4443081 K) (@lem4443080 A K z s k x i)). Qed.
Lemma lem4443083 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term864 A K z s k x i) = (term865 A K z s k x i)) = ((term863 A K z s k x i) = (term878 A K z s k x i)).
Proof. exact (MK_COMB (@lem4443074 A K z s k x i) (@lem4443082 A K z s k x i)). Qed.
Lemma lem4443084 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term863 A K z s k x i) = (term878 A K z s k x i).
Proof. exact (EQ_MP (@lem4443083 A K z s k x i) (@lem4443064 A K z s k x i)). Qed.
Lemma lem4443085 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term853 A K z s k x i) = (term878 A K z s k x i).
Proof. exact (TRANS (@lem4443060 A K z s k x i) (@lem4443084 A K z s k x i)). Qed.
Lemma lem4443086 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term763 A K k z s) = (term763 A K k z s).
Proof. exact (eq_refl (term763 A K k z s)). Qed.
Lemma lem4443087 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term854 A K z s k x i) = (term879 A K z s k x i).
Proof. exact (MK_COMB (@lem4443086 A K k z s) (@lem4443085 A K z s k x i)). Qed.
Lemma lem4443089 {A : Type'} (P : Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4443090 {K : Type'} (P : Prop) (Q : K -> Prop) : (term228 K P Q) = (term229 K P Q).
Proof. exact (@lem4443089 K P Q). Qed.
Lemma lem4443091 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term880 A K z s k x i) = (term881 A K z s k x i).
Proof. exact (@lem4443090 K (term697 A K k z s) (term877 A K z s k x i)). Qed.
Lemma lem4443092 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term882 A K z s k x i i') = (term875 A K z s k x i' i).
Proof. exact (eq_refl (term882 A K z s k x i i')). Qed.
Lemma lem4443093 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term883 A K z s k x i) = (term877 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443092 A K z s k x i' i)). Qed.
Lemma lem4443094 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443095 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term884 A K z s k x i) = (term878 A K z s k x i).
Proof. exact (MK_COMB (@lem4443094 K) (@lem4443093 A K z s k x i)). Qed.
Lemma lem4443096 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term763 A K k z s) = (term763 A K k z s).
Proof. exact (eq_refl (term763 A K k z s)). Qed.
Lemma lem4443097 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term880 A K z s k x i) = (term879 A K z s k x i).
Proof. exact (MK_COMB (@lem4443096 A K k z s) (@lem4443095 A K z s k x i)). Qed.
Lemma lem4443098 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4443099 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term885 A K z s k x i) = (term886 A K z s k x i).
Proof. exact (MK_COMB (@lem4443098) (@lem4443097 A K z s k x i)). Qed.
Lemma lem4443100 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term882 A K z s k x i i') = (term875 A K z s k x i' i).
Proof. exact (eq_refl (term882 A K z s k x i i')). Qed.
Lemma lem4443101 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term763 A K k z s) = (term763 A K k z s).
Proof. exact (eq_refl (term763 A K k z s)). Qed.
Lemma lem4443102 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term887 A K z s k x i i') = (term888 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443101 A K k z s) (@lem4443100 A K z s k x i' i)). Qed.
Lemma lem4443103 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term889 A K z s k x i) = (term890 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443102 A K z s k x i' i)). Qed.
Lemma lem4443104 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443105 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term881 A K z s k x i) = (term891 A K z s k x i).
Proof. exact (MK_COMB (@lem4443104 K) (@lem4443103 A K z s k x i)). Qed.
Lemma lem4443106 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term880 A K z s k x i) = (term881 A K z s k x i)) = ((term879 A K z s k x i) = (term891 A K z s k x i)).
Proof. exact (MK_COMB (@lem4443099 A K z s k x i) (@lem4443105 A K z s k x i)). Qed.
Lemma lem4443107 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term879 A K z s k x i) = (term891 A K z s k x i).
Proof. exact (EQ_MP (@lem4443106 A K z s k x i) (@lem4443091 A K z s k x i)). Qed.
Lemma lem4443108 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term854 A K z s k x i) = (term891 A K z s k x i).
Proof. exact (TRANS (@lem4443087 A K z s k x i) (@lem4443107 A K z s k x i)). Qed.
Lemma lem4443109 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term767 A K x s i) = (term767 A K x s i).
Proof. exact (eq_refl (term767 A K x s i)). Qed.
Lemma lem4443110 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term855 A K z s k x i) = (term892 A K z s k x i).
Proof. exact (MK_COMB (@lem4443109 A K x s i) (@lem4443108 A K z s k x i)). Qed.
Lemma lem4443112 {A : Type'} (P : Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4443113 {K : Type'} (P : Prop) (Q : K -> Prop) : (term228 K P Q) = (term229 K P Q).
Proof. exact (@lem4443112 K P Q). Qed.
Lemma lem4443114 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term893 A K z s k x i) = (term894 A K z s k x i).
Proof. exact (@lem4443113 K (term35 A K x s i) (term890 A K z s k x i)). Qed.
Lemma lem4443115 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term895 A K z s k x i i') = (term888 A K z s k x i' i).
Proof. exact (eq_refl (term895 A K z s k x i i')). Qed.
Lemma lem4443116 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term896 A K z s k x i) = (term890 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443115 A K z s k x i' i)). Qed.
Lemma lem4443117 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443118 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term897 A K z s k x i) = (term891 A K z s k x i).
Proof. exact (MK_COMB (@lem4443117 K) (@lem4443116 A K z s k x i)). Qed.
Lemma lem4443119 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term767 A K x s i) = (term767 A K x s i).
Proof. exact (eq_refl (term767 A K x s i)). Qed.
Lemma lem4443120 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term893 A K z s k x i) = (term892 A K z s k x i).
Proof. exact (MK_COMB (@lem4443119 A K x s i) (@lem4443118 A K z s k x i)). Qed.
Lemma lem4443121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4443122 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term898 A K z s k x i) = (term899 A K z s k x i).
Proof. exact (MK_COMB (@lem4443121) (@lem4443120 A K z s k x i)). Qed.
Lemma lem4443123 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term895 A K z s k x i i') = (term888 A K z s k x i' i).
Proof. exact (eq_refl (term895 A K z s k x i i')). Qed.
Lemma lem4443124 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term767 A K x s i) = (term767 A K x s i).
Proof. exact (eq_refl (term767 A K x s i)). Qed.
Lemma lem4443125 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term900 A K z s k x i i') = (term901 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443124 A K x s i) (@lem4443123 A K z s k x i' i)). Qed.
Lemma lem4443126 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term902 A K z s k x i) = (term903 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443125 A K z s k x i' i)). Qed.
Lemma lem4443127 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443128 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term894 A K z s k x i) = (term904 A K z s k x i).
Proof. exact (MK_COMB (@lem4443127 K) (@lem4443126 A K z s k x i)). Qed.
Lemma lem4443129 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term893 A K z s k x i) = (term894 A K z s k x i)) = ((term892 A K z s k x i) = (term904 A K z s k x i)).
Proof. exact (MK_COMB (@lem4443122 A K z s k x i) (@lem4443128 A K z s k x i)). Qed.
Lemma lem4443130 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term892 A K z s k x i) = (term904 A K z s k x i).
Proof. exact (EQ_MP (@lem4443129 A K z s k x i) (@lem4443114 A K z s k x i)). Qed.
Lemma lem4443131 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term855 A K z s k x i) = (term904 A K z s k x i).
Proof. exact (TRANS (@lem4443110 A K z s k x i) (@lem4443130 A K z s k x i)). Qed.
Lemma lem4443132 {K : Type'} (i : K) (k : K -> Prop) : (term22 K i k) = (term22 K i k).
Proof. exact (eq_refl (term22 K i k)). Qed.
Lemma lem4443133 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term856 A K z s k x i) = (term905 A K z s k x i).
Proof. exact (MK_COMB (@lem4443132 K i k) (@lem4443131 A K z s k x i)). Qed.
Lemma lem4443135 {A : Type'} (P : Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4443136 {K : Type'} (P : Prop) (Q : K -> Prop) : (term228 K P Q) = (term229 K P Q).
Proof. exact (@lem4443135 K P Q). Qed.
Lemma lem4443137 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term906 A K z s k x i) = (term907 A K z s k x i).
Proof. exact (@lem4443136 K (@IN K i k) (term903 A K z s k x i)). Qed.
Lemma lem4443138 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term908 A K z s k x i i') = (term901 A K z s k x i' i).
Proof. exact (eq_refl (term908 A K z s k x i i')). Qed.
Lemma lem4443139 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term909 A K z s k x i) = (term903 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443138 A K z s k x i' i)). Qed.
Lemma lem4443140 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443141 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term910 A K z s k x i) = (term904 A K z s k x i).
Proof. exact (MK_COMB (@lem4443140 K) (@lem4443139 A K z s k x i)). Qed.
Lemma lem4443142 {K : Type'} (i : K) (k : K -> Prop) : (term22 K i k) = (term22 K i k).
Proof. exact (eq_refl (term22 K i k)). Qed.
Lemma lem4443143 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term906 A K z s k x i) = (term905 A K z s k x i).
Proof. exact (MK_COMB (@lem4443142 K i k) (@lem4443141 A K z s k x i)). Qed.
Lemma lem4443144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4443145 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term911 A K z s k x i) = (term912 A K z s k x i).
Proof. exact (MK_COMB (@lem4443144) (@lem4443143 A K z s k x i)). Qed.
Lemma lem4443146 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term908 A K z s k x i i') = (term901 A K z s k x i' i).
Proof. exact (eq_refl (term908 A K z s k x i i')). Qed.
Lemma lem4443147 {K : Type'} (i : K) (k : K -> Prop) : (term22 K i k) = (term22 K i k).
Proof. exact (eq_refl (term22 K i k)). Qed.
Lemma lem4443148 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term913 A K z s k x i i') = (term914 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443147 K i k) (@lem4443146 A K z s k x i' i)). Qed.
Lemma lem4443149 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term915 A K z s k x i) = (term916 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443148 A K z s k x i' i)). Qed.
Lemma lem4443150 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443151 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term907 A K z s k x i) = (term917 A K z s k x i).
Proof. exact (MK_COMB (@lem4443150 K) (@lem4443149 A K z s k x i)). Qed.
Lemma lem4443152 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term906 A K z s k x i) = (term907 A K z s k x i)) = ((term905 A K z s k x i) = (term917 A K z s k x i)).
Proof. exact (MK_COMB (@lem4443145 A K z s k x i) (@lem4443151 A K z s k x i)). Qed.
Lemma lem4443153 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term905 A K z s k x i) = (term917 A K z s k x i).
Proof. exact (EQ_MP (@lem4443152 A K z s k x i) (@lem4443137 A K z s k x i)). Qed.
Lemma lem4443154 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term856 A K z s k x i) = (term917 A K z s k x i).
Proof. exact (TRANS (@lem4443133 A K z s k x i) (@lem4443153 A K z s k x i)). Qed.
Lemma lem4443155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4443156 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term857 A K z s k x i) = (term918 A K z s k x i).
Proof. exact (MK_COMB (@lem4443155) (@lem4443154 A K z s k x i)). Qed.
Lemma lem4443158 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term153 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4443159 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term153 K P Q) = (term152 K P Q).
Proof. exact (@lem4443158 K P Q). Qed.
Lemma lem4443160 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term786 A K z s k x i) = (term785 A K z s k x i).
Proof. exact (@lem4443159 K (term787 A K k x i z s) (term788 A K k x i)). Qed.
Lemma lem4443161 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term789 A K k x i z s i') = (term715 A K k x i z s i').
Proof. exact (eq_refl (term789 A K k x i z s i')). Qed.
Lemma lem4443162 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term796 A K k x i z s) = (term787 A K k x i z s).
Proof. exact (fun_ext (fun i' : K => @lem4443161 A K k x i z s i')). Qed.
Lemma lem4443163 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443164 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term797 A K k x i z s) = (term798 A K k x i z s).
Proof. exact (MK_COMB (@lem4443163 K) (@lem4443162 A K k x i z s)). Qed.
Lemma lem4443165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4443166 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) : (term799 A K k x i z s) = (term800 A K k x i z s).
Proof. exact (MK_COMB (@lem4443165) (@lem4443164 A K k x i z s)). Qed.
Lemma lem4443167 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term791 A K k x i i') = (term731 A K k x i' i).
Proof. exact (eq_refl (term791 A K k x i i')). Qed.
Lemma lem4443168 {A K : Type'} (k : K -> Prop) (x : A) (i : K) : (term801 A K k x i) = (term788 A K k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443167 A K k x i' i)). Qed.
Lemma lem4443169 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443170 {A K : Type'} (k : K -> Prop) (x : A) (i : K) : (term802 A K k x i) = (term803 A K k x i).
Proof. exact (MK_COMB (@lem4443169 K) (@lem4443168 A K k x i)). Qed.
Lemma lem4443171 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term786 A K z s k x i) = (term804 A K z s k x i).
Proof. exact (MK_COMB (@lem4443166 A K k x i z s) (@lem4443170 A K k x i)). Qed.
Lemma lem4443172 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4443173 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term861 A K z s k x i) = (term862 A K z s k x i).
Proof. exact (MK_COMB (@lem4443172) (@lem4443171 A K z s k x i)). Qed.
Lemma lem4443174 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term789 A K k x i z s i') = (term715 A K k x i z s i').
Proof. exact (eq_refl (term789 A K k x i z s i')). Qed.
Lemma lem4443175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4443176 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) : (term790 A K k x i z s i') = (term734 A K k x i z s i').
Proof. exact (MK_COMB (@lem4443175) (@lem4443174 A K k x i z s i')). Qed.
Lemma lem4443177 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) : (term791 A K k x i i') = (term731 A K k x i' i).
Proof. exact (eq_refl (term791 A K k x i i')). Qed.
Lemma lem4443178 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term792 A K z s k x i i') = (term736 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443176 A K k x i z s i') (@lem4443177 A K k x i' i)). Qed.
Lemma lem4443179 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term793 A K z s k x i) = (term744 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443178 A K z s k x i' i)). Qed.
Lemma lem4443180 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443181 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term785 A K z s k x i) = (term745 A K z s k x i).
Proof. exact (MK_COMB (@lem4443180 K) (@lem4443179 A K z s k x i)). Qed.
Lemma lem4443182 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term786 A K z s k x i) = (term785 A K z s k x i)) = ((term804 A K z s k x i) = (term745 A K z s k x i)).
Proof. exact (MK_COMB (@lem4443173 A K z s k x i) (@lem4443181 A K z s k x i)). Qed.
Lemma lem4443183 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term804 A K z s k x i) = (term745 A K z s k x i).
Proof. exact (EQ_MP (@lem4443182 A K z s k x i) (@lem4443160 A K z s k x i)). Qed.
Lemma lem4443184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443185 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term805 A K z s k x i) = (term758 A K z s k x i).
Proof. exact (MK_COMB (@lem4443184) (@lem4443183 A K z s k x i)). Qed.
Lemma lem4443186 {A K : Type'} : (term852 A K) = (term852 A K).
Proof. exact (eq_refl (term852 A K)). Qed.
Lemma lem4443187 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term853 A K z s k x i) = (term863 A K z s k x i).
Proof. exact (MK_COMB (@lem4443185 A K z s k x i) (@lem4443186 A K)). Qed.
Lemma lem4443189 {A : Type'} (P : A -> Prop) (Q : Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4443190 {K : Type'} (P : K -> Prop) (Q : Prop) : (term209 K P Q) = (term210 K P Q).
Proof. exact (@lem4443189 K P Q). Qed.
Lemma lem4443191 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term864 A K z s k x i) = (term865 A K z s k x i).
Proof. exact (@lem4443190 K (term744 A K z s k x i) (term852 A K)). Qed.
Lemma lem4443192 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term866 A K z s k x i i') = (term736 A K z s k x i' i).
Proof. exact (eq_refl (term866 A K z s k x i i')). Qed.
Lemma lem4443193 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term867 A K z s k x i) = (term744 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443192 A K z s k x i' i)). Qed.
Lemma lem4443194 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443195 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term868 A K z s k x i) = (term745 A K z s k x i).
Proof. exact (MK_COMB (@lem4443194 K) (@lem4443193 A K z s k x i)). Qed.
Lemma lem4443196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443197 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term869 A K z s k x i) = (term758 A K z s k x i).
Proof. exact (MK_COMB (@lem4443196) (@lem4443195 A K z s k x i)). Qed.
Lemma lem4443198 {A K : Type'} : (term852 A K) = (term852 A K).
Proof. exact (eq_refl (term852 A K)). Qed.
Lemma lem4443199 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term864 A K z s k x i) = (term863 A K z s k x i).
Proof. exact (MK_COMB (@lem4443197 A K z s k x i) (@lem4443198 A K)). Qed.
Lemma lem4443200 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4443201 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term870 A K z s k x i) = (term871 A K z s k x i).
Proof. exact (MK_COMB (@lem4443200) (@lem4443199 A K z s k x i)). Qed.
Lemma lem4443202 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term866 A K z s k x i i') = (term736 A K z s k x i' i).
Proof. exact (eq_refl (term866 A K z s k x i i')). Qed.
Lemma lem4443203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443204 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term872 A K z s k x i i') = (term873 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443203) (@lem4443202 A K z s k x i' i)). Qed.
Lemma lem4443205 {A K : Type'} : (term852 A K) = (term852 A K).
Proof. exact (eq_refl (term852 A K)). Qed.
Lemma lem4443206 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term874 A K z s k x i i') = (term875 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443204 A K z s k x i' i) (@lem4443205 A K)). Qed.
Lemma lem4443207 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term876 A K z s k x i) = (term877 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443206 A K z s k x i' i)). Qed.
Lemma lem4443208 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443209 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term865 A K z s k x i) = (term878 A K z s k x i).
Proof. exact (MK_COMB (@lem4443208 K) (@lem4443207 A K z s k x i)). Qed.
Lemma lem4443210 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term864 A K z s k x i) = (term865 A K z s k x i)) = ((term863 A K z s k x i) = (term878 A K z s k x i)).
Proof. exact (MK_COMB (@lem4443201 A K z s k x i) (@lem4443209 A K z s k x i)). Qed.
Lemma lem4443211 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term863 A K z s k x i) = (term878 A K z s k x i).
Proof. exact (EQ_MP (@lem4443210 A K z s k x i) (@lem4443191 A K z s k x i)). Qed.
Lemma lem4443212 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term853 A K z s k x i) = (term878 A K z s k x i).
Proof. exact (TRANS (@lem4443187 A K z s k x i) (@lem4443211 A K z s k x i)). Qed.
Lemma lem4443213 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term763 A K k z s) = (term763 A K k z s).
Proof. exact (eq_refl (term763 A K k z s)). Qed.
Lemma lem4443214 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term854 A K z s k x i) = (term879 A K z s k x i).
Proof. exact (MK_COMB (@lem4443213 A K k z s) (@lem4443212 A K z s k x i)). Qed.
Lemma lem4443216 {A : Type'} (P : Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4443217 {K : Type'} (P : Prop) (Q : K -> Prop) : (term228 K P Q) = (term229 K P Q).
Proof. exact (@lem4443216 K P Q). Qed.
Lemma lem4443218 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term880 A K z s k x i) = (term881 A K z s k x i).
Proof. exact (@lem4443217 K (term697 A K k z s) (term877 A K z s k x i)). Qed.
Lemma lem4443219 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term882 A K z s k x i i') = (term875 A K z s k x i' i).
Proof. exact (eq_refl (term882 A K z s k x i i')). Qed.
Lemma lem4443220 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term883 A K z s k x i) = (term877 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443219 A K z s k x i' i)). Qed.
Lemma lem4443221 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443222 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term884 A K z s k x i) = (term878 A K z s k x i).
Proof. exact (MK_COMB (@lem4443221 K) (@lem4443220 A K z s k x i)). Qed.
Lemma lem4443223 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term763 A K k z s) = (term763 A K k z s).
Proof. exact (eq_refl (term763 A K k z s)). Qed.
Lemma lem4443224 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term880 A K z s k x i) = (term879 A K z s k x i).
Proof. exact (MK_COMB (@lem4443223 A K k z s) (@lem4443222 A K z s k x i)). Qed.
Lemma lem4443225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4443226 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term885 A K z s k x i) = (term886 A K z s k x i).
Proof. exact (MK_COMB (@lem4443225) (@lem4443224 A K z s k x i)). Qed.
Lemma lem4443227 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term882 A K z s k x i i') = (term875 A K z s k x i' i).
Proof. exact (eq_refl (term882 A K z s k x i i')). Qed.
Lemma lem4443228 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term763 A K k z s) = (term763 A K k z s).
Proof. exact (eq_refl (term763 A K k z s)). Qed.
Lemma lem4443229 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term887 A K z s k x i i') = (term888 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443228 A K k z s) (@lem4443227 A K z s k x i' i)). Qed.
Lemma lem4443230 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term889 A K z s k x i) = (term890 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443229 A K z s k x i' i)). Qed.
Lemma lem4443231 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443232 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term881 A K z s k x i) = (term891 A K z s k x i).
Proof. exact (MK_COMB (@lem4443231 K) (@lem4443230 A K z s k x i)). Qed.
Lemma lem4443233 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term880 A K z s k x i) = (term881 A K z s k x i)) = ((term879 A K z s k x i) = (term891 A K z s k x i)).
Proof. exact (MK_COMB (@lem4443226 A K z s k x i) (@lem4443232 A K z s k x i)). Qed.
Lemma lem4443234 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term879 A K z s k x i) = (term891 A K z s k x i).
Proof. exact (EQ_MP (@lem4443233 A K z s k x i) (@lem4443218 A K z s k x i)). Qed.
Lemma lem4443235 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term854 A K z s k x i) = (term891 A K z s k x i).
Proof. exact (TRANS (@lem4443214 A K z s k x i) (@lem4443234 A K z s k x i)). Qed.
Lemma lem4443236 {A : Type'} (x : A) : (term774 A x) = (term774 A x).
Proof. exact (eq_refl (term774 A x)). Qed.
Lemma lem4443237 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term858 A K z s k x i) = (term919 A K z s k x i).
Proof. exact (MK_COMB (@lem4443236 A x) (@lem4443235 A K z s k x i)). Qed.
Lemma lem4443239 {A : Type'} (P : Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4443240 {K : Type'} (P : Prop) (Q : K -> Prop) : (term228 K P Q) = (term229 K P Q).
Proof. exact (@lem4443239 K P Q). Qed.
Lemma lem4443241 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term920 A K z s k x i) = (term921 A K z s k x i).
Proof. exact (@lem4443240 K (term609 A x) (term890 A K z s k x i)). Qed.
Lemma lem4443242 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term895 A K z s k x i i') = (term888 A K z s k x i' i).
Proof. exact (eq_refl (term895 A K z s k x i i')). Qed.
Lemma lem4443243 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term896 A K z s k x i) = (term890 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443242 A K z s k x i' i)). Qed.
Lemma lem4443244 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443245 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term897 A K z s k x i) = (term891 A K z s k x i).
Proof. exact (MK_COMB (@lem4443244 K) (@lem4443243 A K z s k x i)). Qed.
Lemma lem4443246 {A : Type'} (x : A) : (term774 A x) = (term774 A x).
Proof. exact (eq_refl (term774 A x)). Qed.
Lemma lem4443247 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term920 A K z s k x i) = (term919 A K z s k x i).
Proof. exact (MK_COMB (@lem4443246 A x) (@lem4443245 A K z s k x i)). Qed.
Lemma lem4443248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4443249 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term922 A K z s k x i) = (term923 A K z s k x i).
Proof. exact (MK_COMB (@lem4443248) (@lem4443247 A K z s k x i)). Qed.
Lemma lem4443250 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term895 A K z s k x i i') = (term888 A K z s k x i' i).
Proof. exact (eq_refl (term895 A K z s k x i i')). Qed.
Lemma lem4443251 {A : Type'} (x : A) : (term774 A x) = (term774 A x).
Proof. exact (eq_refl (term774 A x)). Qed.
Lemma lem4443252 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term924 A K z s k x i i') = (term925 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443251 A x) (@lem4443250 A K z s k x i' i)). Qed.
Lemma lem4443253 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term926 A K z s k x i) = (term927 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443252 A K z s k x i' i)). Qed.
Lemma lem4443254 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443255 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term921 A K z s k x i) = (term928 A K z s k x i).
Proof. exact (MK_COMB (@lem4443254 K) (@lem4443253 A K z s k x i)). Qed.
Lemma lem4443256 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term920 A K z s k x i) = (term921 A K z s k x i)) = ((term919 A K z s k x i) = (term928 A K z s k x i)).
Proof. exact (MK_COMB (@lem4443249 A K z s k x i) (@lem4443255 A K z s k x i)). Qed.
Lemma lem4443257 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term919 A K z s k x i) = (term928 A K z s k x i).
Proof. exact (EQ_MP (@lem4443256 A K z s k x i) (@lem4443241 A K z s k x i)). Qed.
Lemma lem4443258 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term858 A K z s k x i) = (term928 A K z s k x i).
Proof. exact (TRANS (@lem4443237 A K z s k x i) (@lem4443257 A K z s k x i)). Qed.
Lemma lem4443259 {K : Type'} (i : K) (k : K -> Prop) : (term729 K i k) = (term729 K i k).
Proof. exact (eq_refl (term729 K i k)). Qed.
Lemma lem4443260 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term859 A K z s k x i) = (term929 A K z s k x i).
Proof. exact (MK_COMB (@lem4443259 K i k) (@lem4443258 A K z s k x i)). Qed.
Lemma lem4443262 {A : Type'} (P : Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4443263 {K : Type'} (P : Prop) (Q : K -> Prop) : (term228 K P Q) = (term229 K P Q).
Proof. exact (@lem4443262 K P Q). Qed.
Lemma lem4443264 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term930 A K z s k x i) = (term931 A K z s k x i).
Proof. exact (@lem4443263 K (term717 K i k) (term927 A K z s k x i)). Qed.
Lemma lem4443265 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term932 A K z s k x i i') = (term925 A K z s k x i' i).
Proof. exact (eq_refl (term932 A K z s k x i i')). Qed.
Lemma lem4443266 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term933 A K z s k x i) = (term927 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443265 A K z s k x i' i)). Qed.
Lemma lem4443267 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443268 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term934 A K z s k x i) = (term928 A K z s k x i).
Proof. exact (MK_COMB (@lem4443267 K) (@lem4443266 A K z s k x i)). Qed.
Lemma lem4443269 {K : Type'} (i : K) (k : K -> Prop) : (term729 K i k) = (term729 K i k).
Proof. exact (eq_refl (term729 K i k)). Qed.
Lemma lem4443270 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term930 A K z s k x i) = (term929 A K z s k x i).
Proof. exact (MK_COMB (@lem4443269 K i k) (@lem4443268 A K z s k x i)). Qed.
Lemma lem4443271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4443272 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term935 A K z s k x i) = (term936 A K z s k x i).
Proof. exact (MK_COMB (@lem4443271) (@lem4443270 A K z s k x i)). Qed.
Lemma lem4443273 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term932 A K z s k x i i') = (term925 A K z s k x i' i).
Proof. exact (eq_refl (term932 A K z s k x i i')). Qed.
Lemma lem4443274 {K : Type'} (i : K) (k : K -> Prop) : (term729 K i k) = (term729 K i k).
Proof. exact (eq_refl (term729 K i k)). Qed.
Lemma lem4443275 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term937 A K z s k x i i') = (term938 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443274 K i k) (@lem4443273 A K z s k x i' i)). Qed.
Lemma lem4443276 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term939 A K z s k x i) = (term940 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443275 A K z s k x i' i)). Qed.
Lemma lem4443277 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443278 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term931 A K z s k x i) = (term941 A K z s k x i).
Proof. exact (MK_COMB (@lem4443277 K) (@lem4443276 A K z s k x i)). Qed.
Lemma lem4443279 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term930 A K z s k x i) = (term931 A K z s k x i)) = ((term929 A K z s k x i) = (term941 A K z s k x i)).
Proof. exact (MK_COMB (@lem4443272 A K z s k x i) (@lem4443278 A K z s k x i)). Qed.
Lemma lem4443280 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term929 A K z s k x i) = (term941 A K z s k x i).
Proof. exact (EQ_MP (@lem4443279 A K z s k x i) (@lem4443264 A K z s k x i)). Qed.
Lemma lem4443281 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term859 A K z s k x i) = (term941 A K z s k x i).
Proof. exact (TRANS (@lem4443260 A K z s k x i) (@lem4443280 A K z s k x i)). Qed.
Lemma lem4443282 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term860 A K z s k x i) = (term942 A K z s k x i).
Proof. exact (MK_COMB (@lem4443156 A K z s k x i) (@lem4443281 A K z s k x i)). Qed.
Lemma lem4443284 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term153 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4443285 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term153 K P Q) = (term152 K P Q).
Proof. exact (@lem4443284 K P Q). Qed.
Lemma lem4443286 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term943 A K z s k x i) = (term944 A K z s k x i).
Proof. exact (@lem4443285 K (term916 A K z s k x i) (term940 A K z s k x i)). Qed.
Lemma lem4443287 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term945 A K z s k x i i') = (term914 A K z s k x i' i).
Proof. exact (eq_refl (term945 A K z s k x i i')). Qed.
Lemma lem4443288 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term946 A K z s k x i) = (term916 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443287 A K z s k x i' i)). Qed.
Lemma lem4443289 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443290 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term947 A K z s k x i) = (term917 A K z s k x i).
Proof. exact (MK_COMB (@lem4443289 K) (@lem4443288 A K z s k x i)). Qed.
Lemma lem4443291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4443292 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term948 A K z s k x i) = (term918 A K z s k x i).
Proof. exact (MK_COMB (@lem4443291) (@lem4443290 A K z s k x i)). Qed.
Lemma lem4443293 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term949 A K z s k x i i') = (term938 A K z s k x i' i).
Proof. exact (eq_refl (term949 A K z s k x i i')). Qed.
Lemma lem4443294 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term950 A K z s k x i) = (term940 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443293 A K z s k x i' i)). Qed.
Lemma lem4443295 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443296 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term951 A K z s k x i) = (term941 A K z s k x i).
Proof. exact (MK_COMB (@lem4443295 K) (@lem4443294 A K z s k x i)). Qed.
Lemma lem4443297 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term943 A K z s k x i) = (term942 A K z s k x i).
Proof. exact (MK_COMB (@lem4443292 A K z s k x i) (@lem4443296 A K z s k x i)). Qed.
Lemma lem4443298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4443299 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term952 A K z s k x i) = (term953 A K z s k x i).
Proof. exact (MK_COMB (@lem4443298) (@lem4443297 A K z s k x i)). Qed.
Lemma lem4443300 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term945 A K z s k x i i') = (term914 A K z s k x i' i).
Proof. exact (eq_refl (term945 A K z s k x i i')). Qed.
Lemma lem4443301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4443302 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term954 A K z s k x i i') = (term955 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443301) (@lem4443300 A K z s k x i' i)). Qed.
Lemma lem4443303 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term949 A K z s k x i i') = (term938 A K z s k x i' i).
Proof. exact (eq_refl (term949 A K z s k x i i')). Qed.
Lemma lem4443304 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term956 A K z s k x i i') = (term957 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443302 A K z s k x i' i) (@lem4443303 A K z s k x i' i)). Qed.
Lemma lem4443305 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term958 A K z s k x i) = (term959 A K z s k x i).
Proof. exact (fun_ext (fun i' : K => @lem4443304 A K z s k x i' i)). Qed.
Lemma lem4443306 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4443307 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term944 A K z s k x i) = (term960 A K z s k x i).
Proof. exact (MK_COMB (@lem4443306 K) (@lem4443305 A K z s k x i)). Qed.
Lemma lem4443308 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : ((term943 A K z s k x i) = (term944 A K z s k x i)) = ((term942 A K z s k x i) = (term960 A K z s k x i)).
Proof. exact (MK_COMB (@lem4443299 A K z s k x i) (@lem4443307 A K z s k x i)). Qed.
Lemma lem4443309 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term942 A K z s k x i) = (term960 A K z s k x i).
Proof. exact (EQ_MP (@lem4443308 A K z s k x i) (@lem4443286 A K z s k x i)). Qed.
Lemma lem4443310 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term860 A K z s k x i) = (term960 A K z s k x i).
Proof. exact (TRANS (@lem4443282 A K z s k x i) (@lem4443309 A K z s k x i)). Qed.
Lemma lem4443311 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term784 A K z s k x i) = (term960 A K z s k x i).
Proof. exact (TRANS (@lem4443029 A K z s k x i) (@lem4443310 A K z s k x i)). Qed.
Lemma lem4443312 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : (term693 A K z s k x i) = (term960 A K z s k x i).
Proof. exact (TRANS (@lem4441612 A K z s k x i) (@lem4443311 A K z s k x i)). Qed.
Lemma lem4443313 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) (h1 : term693 A K z s k x i) : term960 A K z s k x i.
Proof. exact (EQ_MP (@lem4443312 A K z s k x i) (@lem4441301 A K z s k x i h1)). Qed.
Lemma lem4443314 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term957 A K z s k x i' i) : term957 A K z s k x i' i.
Proof. exact (h1). Qed.
Lemma lem4443333 {K : Type'} (x : K) (y : K) : (term815 K x y) = (term815 K x y).
Proof. exact (eq_refl (term815 K x y)). Qed.
Lemma lem4443334 {K : Type'} (x : K) : (term809 K x) = (term809 K x).
Proof. exact (fun_ext (fun y : K => @lem4443333 K x y)). Qed.
Lemma lem4443335 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4443336 {K : Type'} (x : K) : (term827 K x) = (term827 K x).
Proof. exact (MK_COMB (@lem4443335 K) (@lem4443334 K x)). Qed.
Lemma lem4443337 {K : Type'} : (term834 K) = (term834 K).
Proof. exact (fun_ext (fun x : K => @lem4443336 K x)). Qed.
Lemma lem4443338 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4443339 {K : Type'} : (term849 K) = (term849 K).
Proof. exact (MK_COMB (@lem4443338 K) (@lem4443337 K)). Qed.
Lemma lem4443358 {K : Type'} (x : K) (y : K) : (term811 K x y) = (term811 K x y).
Proof. exact (eq_refl (term811 K x y)). Qed.
Lemma lem4443359 {K : Type'} (x : K) : (term808 K x) = (term808 K x).
Proof. exact (fun_ext (fun y : K => @lem4443358 K x y)). Qed.
Lemma lem4443360 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4443361 {K : Type'} (x : K) : (term822 K x) = (term822 K x).
Proof. exact (MK_COMB (@lem4443360 K) (@lem4443359 K x)). Qed.
Lemma lem4443362 {K : Type'} : (term833 K) = (term833 K).
Proof. exact (fun_ext (fun x : K => @lem4443361 K x)). Qed.
Lemma lem4443363 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4443364 {K : Type'} : (term844 K) = (term844 K).
Proof. exact (MK_COMB (@lem4443363 K) (@lem4443362 K)). Qed.
Lemma lem4443365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443366 {K : Type'} : (term846 K) = (term846 K).
Proof. exact (MK_COMB (@lem4443365) (@lem4443364 K)). Qed.
Lemma lem4443367 {K : Type'} : (term850 K) = (term850 K).
Proof. exact (MK_COMB (@lem4443366 K) (@lem4443339 K)). Qed.
Lemma lem4443386 {A : Type'} (x : A) (y : A) : (term815 A x y) = (term815 A x y).
Proof. exact (eq_refl (term815 A x y)). Qed.
Lemma lem4443387 {A : Type'} (x : A) : (term809 A x) = (term809 A x).
Proof. exact (fun_ext (fun y : A => @lem4443386 A x y)). Qed.
Lemma lem4443388 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4443389 {A : Type'} (x : A) : (term827 A x) = (term827 A x).
Proof. exact (MK_COMB (@lem4443388 A) (@lem4443387 A x)). Qed.
Lemma lem4443390 {A : Type'} : (term834 A) = (term834 A).
Proof. exact (fun_ext (fun x : A => @lem4443389 A x)). Qed.
Lemma lem4443391 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4443392 {A : Type'} : (term849 A) = (term849 A).
Proof. exact (MK_COMB (@lem4443391 A) (@lem4443390 A)). Qed.
Lemma lem4443411 {A : Type'} (x : A) (y : A) : (term811 A x y) = (term811 A x y).
Proof. exact (eq_refl (term811 A x y)). Qed.
Lemma lem4443412 {A : Type'} (x : A) : (term808 A x) = (term808 A x).
Proof. exact (fun_ext (fun y : A => @lem4443411 A x y)). Qed.
Lemma lem4443413 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4443414 {A : Type'} (x : A) : (term822 A x) = (term822 A x).
Proof. exact (MK_COMB (@lem4443413 A) (@lem4443412 A x)). Qed.
Lemma lem4443415 {A : Type'} : (term833 A) = (term833 A).
Proof. exact (fun_ext (fun x : A => @lem4443414 A x)). Qed.
Lemma lem4443416 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4443417 {A : Type'} : (term844 A) = (term844 A).
Proof. exact (MK_COMB (@lem4443416 A) (@lem4443415 A)). Qed.
Lemma lem4443418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443419 {A : Type'} : (term846 A) = (term846 A).
Proof. exact (MK_COMB (@lem4443418) (@lem4443417 A)). Qed.
Lemma lem4443420 {A : Type'} : (term850 A) = (term850 A).
Proof. exact (MK_COMB (@lem4443419 A) (@lem4443392 A)). Qed.
Lemma lem4443421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443422 {A : Type'} : (term851 A) = (term851 A).
Proof. exact (MK_COMB (@lem4443421) (@lem4443420 A)). Qed.
Lemma lem4443423 {A K : Type'} : (term852 A K) = (term852 A K).
Proof. exact (MK_COMB (@lem4443422 A) (@lem4443367 K)). Qed.
Lemma lem4443530 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term873 A K z s k x i' i) = (term873 A K z s k x i' i).
Proof. exact (eq_refl (term873 A K z s k x i' i)). Qed.
Lemma lem4443531 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term875 A K z s k x i' i) = (term875 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443530 A K z s k x i' i) (@lem4443423 A K)). Qed.
Lemma lem4443550 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term695 A K k z s i) = (term695 A K k z s i).
Proof. exact (eq_refl (term695 A K k z s i)). Qed.
Lemma lem4443551 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term696 A K k z s) = (term696 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4443550 A K k z s i)). Qed.
Lemma lem4443552 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4443553 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term697 A K k z s) = (term697 A K k z s).
Proof. exact (MK_COMB (@lem4443552 K) (@lem4443551 A K k z s)). Qed.
Lemma lem4443554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443555 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term763 A K k z s) = (term763 A K k z s).
Proof. exact (MK_COMB (@lem4443554) (@lem4443553 A K k z s)). Qed.
Lemma lem4443556 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term888 A K z s k x i' i) = (term888 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443555 A K k z s) (@lem4443531 A K z s k x i' i)). Qed.
Lemma lem4443567 {A : Type'} (x : A) : (term774 A x) = (term774 A x).
Proof. exact (eq_refl (term774 A x)). Qed.
Lemma lem4443568 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term925 A K z s k x i' i) = (term925 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443567 A x) (@lem4443556 A K z s k x i' i)). Qed.
Lemma lem4443577 {K : Type'} (i : K) (k : K -> Prop) : (term729 K i k) = (term729 K i k).
Proof. exact (eq_refl (term729 K i k)). Qed.
Lemma lem4443578 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term938 A K z s k x i' i) = (term938 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443577 K i k) (@lem4443568 A K z s k x i' i)). Qed.
Lemma lem4443597 {K : Type'} (x : K) (y : K) : (term815 K x y) = (term815 K x y).
Proof. exact (eq_refl (term815 K x y)). Qed.
Lemma lem4443598 {K : Type'} (x : K) : (term809 K x) = (term809 K x).
Proof. exact (fun_ext (fun y : K => @lem4443597 K x y)). Qed.
Lemma lem4443599 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4443600 {K : Type'} (x : K) : (term827 K x) = (term827 K x).
Proof. exact (MK_COMB (@lem4443599 K) (@lem4443598 K x)). Qed.
Lemma lem4443601 {K : Type'} : (term834 K) = (term834 K).
Proof. exact (fun_ext (fun x : K => @lem4443600 K x)). Qed.
Lemma lem4443602 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4443603 {K : Type'} : (term849 K) = (term849 K).
Proof. exact (MK_COMB (@lem4443602 K) (@lem4443601 K)). Qed.
Lemma lem4443622 {K : Type'} (x : K) (y : K) : (term811 K x y) = (term811 K x y).
Proof. exact (eq_refl (term811 K x y)). Qed.
Lemma lem4443623 {K : Type'} (x : K) : (term808 K x) = (term808 K x).
Proof. exact (fun_ext (fun y : K => @lem4443622 K x y)). Qed.
Lemma lem4443624 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4443625 {K : Type'} (x : K) : (term822 K x) = (term822 K x).
Proof. exact (MK_COMB (@lem4443624 K) (@lem4443623 K x)). Qed.
Lemma lem4443626 {K : Type'} : (term833 K) = (term833 K).
Proof. exact (fun_ext (fun x : K => @lem4443625 K x)). Qed.
Lemma lem4443627 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4443628 {K : Type'} : (term844 K) = (term844 K).
Proof. exact (MK_COMB (@lem4443627 K) (@lem4443626 K)). Qed.
Lemma lem4443629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443630 {K : Type'} : (term846 K) = (term846 K).
Proof. exact (MK_COMB (@lem4443629) (@lem4443628 K)). Qed.
Lemma lem4443631 {K : Type'} : (term850 K) = (term850 K).
Proof. exact (MK_COMB (@lem4443630 K) (@lem4443603 K)). Qed.
Lemma lem4443650 {A : Type'} (x : A) (y : A) : (term815 A x y) = (term815 A x y).
Proof. exact (eq_refl (term815 A x y)). Qed.
Lemma lem4443651 {A : Type'} (x : A) : (term809 A x) = (term809 A x).
Proof. exact (fun_ext (fun y : A => @lem4443650 A x y)). Qed.
Lemma lem4443652 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4443653 {A : Type'} (x : A) : (term827 A x) = (term827 A x).
Proof. exact (MK_COMB (@lem4443652 A) (@lem4443651 A x)). Qed.
Lemma lem4443654 {A : Type'} : (term834 A) = (term834 A).
Proof. exact (fun_ext (fun x : A => @lem4443653 A x)). Qed.
Lemma lem4443655 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4443656 {A : Type'} : (term849 A) = (term849 A).
Proof. exact (MK_COMB (@lem4443655 A) (@lem4443654 A)). Qed.
Lemma lem4443675 {A : Type'} (x : A) (y : A) : (term811 A x y) = (term811 A x y).
Proof. exact (eq_refl (term811 A x y)). Qed.
Lemma lem4443676 {A : Type'} (x : A) : (term808 A x) = (term808 A x).
Proof. exact (fun_ext (fun y : A => @lem4443675 A x y)). Qed.
Lemma lem4443677 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4443678 {A : Type'} (x : A) : (term822 A x) = (term822 A x).
Proof. exact (MK_COMB (@lem4443677 A) (@lem4443676 A x)). Qed.
Lemma lem4443679 {A : Type'} : (term833 A) = (term833 A).
Proof. exact (fun_ext (fun x : A => @lem4443678 A x)). Qed.
Lemma lem4443680 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4443681 {A : Type'} : (term844 A) = (term844 A).
Proof. exact (MK_COMB (@lem4443680 A) (@lem4443679 A)). Qed.
Lemma lem4443682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443683 {A : Type'} : (term846 A) = (term846 A).
Proof. exact (MK_COMB (@lem4443682) (@lem4443681 A)). Qed.
Lemma lem4443684 {A : Type'} : (term850 A) = (term850 A).
Proof. exact (MK_COMB (@lem4443683 A) (@lem4443656 A)). Qed.
Lemma lem4443685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443686 {A : Type'} : (term851 A) = (term851 A).
Proof. exact (MK_COMB (@lem4443685) (@lem4443684 A)). Qed.
Lemma lem4443687 {A K : Type'} : (term852 A K) = (term852 A K).
Proof. exact (MK_COMB (@lem4443686 A) (@lem4443631 K)). Qed.
Lemma lem4443794 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term873 A K z s k x i' i) = (term873 A K z s k x i' i).
Proof. exact (eq_refl (term873 A K z s k x i' i)). Qed.
Lemma lem4443795 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term875 A K z s k x i' i) = (term875 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443794 A K z s k x i' i) (@lem4443687 A K)). Qed.
Lemma lem4443814 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term695 A K k z s i) = (term695 A K k z s i).
Proof. exact (eq_refl (term695 A K k z s i)). Qed.
Lemma lem4443815 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term696 A K k z s) = (term696 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4443814 A K k z s i)). Qed.
Lemma lem4443816 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4443817 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term697 A K k z s) = (term697 A K k z s).
Proof. exact (MK_COMB (@lem4443816 K) (@lem4443815 A K k z s)). Qed.
Lemma lem4443818 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4443819 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term763 A K k z s) = (term763 A K k z s).
Proof. exact (MK_COMB (@lem4443818) (@lem4443817 A K k z s)). Qed.
Lemma lem4443820 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term888 A K z s k x i' i) = (term888 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443819 A K k z s) (@lem4443795 A K z s k x i' i)). Qed.
Lemma lem4443829 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term767 A K x s i) = (term767 A K x s i).
Proof. exact (eq_refl (term767 A K x s i)). Qed.
Lemma lem4443830 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term901 A K z s k x i' i) = (term901 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443829 A K x s i) (@lem4443820 A K z s k x i' i)). Qed.
Lemma lem4443837 {K : Type'} (i : K) (k : K -> Prop) : (term22 K i k) = (term22 K i k).
Proof. exact (eq_refl (term22 K i k)). Qed.
Lemma lem4443838 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term914 A K z s k x i' i) = (term914 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443837 K i k) (@lem4443830 A K z s k x i' i)). Qed.
Lemma lem4443839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4443840 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term955 A K z s k x i' i) = (term955 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443839) (@lem4443838 A K z s k x i' i)). Qed.
Lemma lem4443841 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) : (term957 A K z s k x i' i) = (term957 A K z s k x i' i).
Proof. exact (MK_COMB (@lem4443840 A K z s k x i' i) (@lem4443578 A K z s k x i' i)). Qed.
Lemma lem4443842 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term957 A K z s k x i' i) : term957 A K z s k x i' i.
Proof. exact (EQ_MP (@lem4443841 A K z s k x i' i) (@lem4443314 A K z s k x i' i h1)). Qed.
Lemma lem4443843 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term914 A K z s k x i' i.
Proof. exact (h1). Qed.
Lemma lem4443844 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term938 A K z s k x i' i.
Proof. exact (h1). Qed.
Lemma lem4443845 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term901 A K z s k x i' i.
Proof. exact (proj2 (@lem4443843 A K z s k x i' i h1)). Qed.
Lemma lem4443847 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term888 A K z s k x i' i.
Proof. exact (proj2 (@lem4443845 A K z s k x i' i h1)). Qed.
Lemma lem4443849 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term875 A K z s k x i' i.
Proof. exact (proj2 (@lem4443847 A K z s k x i' i h1)). Qed.
Lemma lem4443850 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term697 A K k z s.
Proof. exact (proj1 (@lem4443847 A K z s k x i' i h1)). Qed.
Lemma lem4443851 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term852 A K.
Proof. exact (proj2 (@lem4443849 A K z s k x i' i h1)). Qed.
Lemma lem4443852 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term736 A K z s k x i' i.
Proof. exact (proj1 (@lem4443849 A K z s k x i' i h1)). Qed.
Lemma lem4443854 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term850 A.
Proof. exact (proj1 (@lem4443851 A K z s k x i' i h1)). Qed.
Lemma lem4443858 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term844 A.
Proof. exact (proj1 (@lem4443854 A K z s k x i' i h1)). Qed.
Lemma lem4443859 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term715 A K k x i z s i') : term715 A K k x i z s i'.
Proof. exact (h1). Qed.
Lemma lem4443860 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term731 A K k x i' i) : term731 A K k x i' i.
Proof. exact (h1). Qed.
Lemma lem4443861 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term715 A K k x i z s i') : term711 A K x i z s i'.
Proof. exact (proj2 (@lem4443859 A K k x i z s i' h1)). Qed.
Lemma lem4443863 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') : term703 A K i x s i'.
Proof. exact (h1). Qed.
Lemma lem4443864 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term707 A K i z s i') : term707 A K i z s i'.
Proof. exact (h1). Qed.
Lemma lem4443869 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term731 A K k x i' i) : term727 A K x i' i.
Proof. exact (proj2 (@lem4443860 A K k x i' i h1)). Qed.
Lemma lem4443871 {A K : Type'} (i' : K) (i : K) (x : A) (h1 : term720 A K i' i x) : term720 A K i' i x.
Proof. exact (h1). Qed.
Lemma lem4443872 {A K : Type'} (i' : K) (i : K) (h1 : term723 A K i' i) : term723 A K i' i.
Proof. exact (h1). Qed.
Lemma lem4443877 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term925 A K z s k x i' i.
Proof. exact (proj2 (@lem4443844 A K z s k x i' i h1)). Qed.
Lemma lem4443879 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term888 A K z s k x i' i.
Proof. exact (proj2 (@lem4443877 A K z s k x i' i h1)). Qed.
Lemma lem4443881 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term875 A K z s k x i' i.
Proof. exact (proj2 (@lem4443879 A K z s k x i' i h1)). Qed.
Lemma lem4443882 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term697 A K k z s.
Proof. exact (proj1 (@lem4443879 A K z s k x i' i h1)). Qed.
Lemma lem4443883 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term852 A K.
Proof. exact (proj2 (@lem4443881 A K z s k x i' i h1)). Qed.
Lemma lem4443884 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term736 A K z s k x i' i.
Proof. exact (proj1 (@lem4443881 A K z s k x i' i h1)). Qed.
Lemma lem4443886 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term850 A.
Proof. exact (proj1 (@lem4443883 A K z s k x i' i h1)). Qed.
Lemma lem4443890 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term844 A.
Proof. exact (proj1 (@lem4443886 A K z s k x i' i h1)). Qed.
Lemma lem4443891 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term715 A K k x i z s i') : term715 A K k x i z s i'.
Proof. exact (h1). Qed.
Lemma lem4443892 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term731 A K k x i' i) : term731 A K k x i' i.
Proof. exact (h1). Qed.
Lemma lem4443893 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term715 A K k x i z s i') : term711 A K x i z s i'.
Proof. exact (proj2 (@lem4443891 A K k x i z s i' h1)). Qed.
Lemma lem4443895 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') : term703 A K i x s i'.
Proof. exact (h1). Qed.
Lemma lem4443896 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term707 A K i z s i') : term707 A K i z s i'.
Proof. exact (h1). Qed.
Lemma lem4443901 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term731 A K k x i' i) : term727 A K x i' i.
Proof. exact (proj2 (@lem4443892 A K k x i' i h1)). Qed.
Lemma lem4443903 {A K : Type'} (i' : K) (i : K) (x : A) (h1 : term720 A K i' i x) : term720 A K i' i x.
Proof. exact (h1). Qed.
Lemma lem4443904 {A K : Type'} (i' : K) (i : K) (h1 : term723 A K i' i) : term723 A K i' i.
Proof. exact (h1). Qed.
Lemma lem4444021 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term695 A K k z s i) = (term695 A K k z s i).
Proof. exact (eq_refl (term695 A K k z s i)). Qed.
Lemma lem4444022 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term696 A K k z s) = (term696 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4444021 A K k z s i)). Qed.
Lemma lem4444023 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4444025 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term697 A K k z s) = (term697 A K k z s).
Proof. exact (MK_COMB (@lem4444023 K) (@lem4444022 A K k z s)). Qed.
Lemma lem4444026 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term697 A K k z s.
Proof. exact (EQ_MP (@lem4444025 A K k z s) (@lem4443850 A K z s k x i' i h1)). Qed.
Lemma lem4444260 {A : Type'} (x : A) (y : A) : (term811 A x y) = (term811 A x y).
Proof. exact (eq_refl (term811 A x y)). Qed.
Lemma lem4444261 {A : Type'} (x : A) : (term808 A x) = (term808 A x).
Proof. exact (fun_ext (fun y : A => @lem4444260 A x y)). Qed.
Lemma lem4444262 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4444263 {A : Type'} (x : A) : (term822 A x) = (term822 A x).
Proof. exact (MK_COMB (@lem4444262 A) (@lem4444261 A x)). Qed.
Lemma lem4444264 {A : Type'} : (term833 A) = (term833 A).
Proof. exact (fun_ext (fun x : A => @lem4444263 A x)). Qed.
Lemma lem4444265 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4444267 {A : Type'} : (term844 A) = (term844 A).
Proof. exact (MK_COMB (@lem4444265 A) (@lem4444264 A)). Qed.
Lemma lem4444268 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term844 A.
Proof. exact (EQ_MP (@lem4444267 A) (@lem4443858 A K z s k x i' i h1)). Qed.
Lemma lem4444409 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (i : K) : (term695 A K k z s i) = (term695 A K k z s i).
Proof. exact (eq_refl (term695 A K k z s i)). Qed.
Lemma lem4444410 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term696 A K k z s) = (term696 A K k z s).
Proof. exact (fun_ext (fun i : K => @lem4444409 A K k z s i)). Qed.
Lemma lem4444411 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4444413 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) : (term697 A K k z s) = (term697 A K k z s).
Proof. exact (MK_COMB (@lem4444411 K) (@lem4444410 A K k z s)). Qed.
Lemma lem4444414 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term697 A K k z s.
Proof. exact (EQ_MP (@lem4444413 A K k z s) (@lem4443882 A K z s k x i' i h1)). Qed.
Lemma lem4444648 {A : Type'} (x : A) (y : A) : (term811 A x y) = (term811 A x y).
Proof. exact (eq_refl (term811 A x y)). Qed.
Lemma lem4444649 {A : Type'} (x : A) : (term808 A x) = (term808 A x).
Proof. exact (fun_ext (fun y : A => @lem4444648 A x y)). Qed.
Lemma lem4444650 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4444651 {A : Type'} (x : A) : (term822 A x) = (term822 A x).
Proof. exact (MK_COMB (@lem4444650 A) (@lem4444649 A x)). Qed.
Lemma lem4444652 {A : Type'} : (term833 A) = (term833 A).
Proof. exact (fun_ext (fun x : A => @lem4444651 A x)). Qed.
Lemma lem4444653 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4444655 {A : Type'} : (term844 A) = (term844 A).
Proof. exact (MK_COMB (@lem4444653 A) (@lem4444652 A)). Qed.
Lemma lem4444656 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term844 A.
Proof. exact (EQ_MP (@lem4444655 A) (@lem4443890 A K z s k x i' i h1)). Qed.
Lemma lem4444712 {A K : Type'} (_51085 : K) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term961 A K k z s _51085.
Proof. exact (@lem4444026 A K z s k x i' i h1 _51085). Qed.
Lemma lem4444713 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51085 : K) : (term961 A K k z s _51085) = (term695 A K k z s _51085).
Proof. exact (eq_refl (term961 A K k z s _51085)). Qed.
Lemma lem4444781 {A K : Type'} (_51108 : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term835 A _51108.
Proof. exact (@lem4444268 A K z s k x i' i h1 _51108). Qed.
Lemma lem4444782 {A : Type'} (_51108 : A) : (term835 A _51108) = (term822 A _51108).
Proof. exact (eq_refl (term835 A _51108)). Qed.
Lemma lem4444783 {A K : Type'} (_51108 : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term822 A _51108.
Proof. exact (EQ_MP (@lem4444782 A _51108) (@lem4444781 A K _51108 z s k x i' i h1)). Qed.
Lemma lem4444784 {A K : Type'} (_51108 : A) (_51109 : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term810 A _51108 _51109.
Proof. exact (@lem4444783 A K _51108 z s k x i' i h1 _51109). Qed.
Lemma lem4444785 {A : Type'} (_51108 : A) (_51109 : A) : (term810 A _51108 _51109) = (term811 A _51108 _51109).
Proof. exact (eq_refl (term810 A _51108 _51109)). Qed.
Lemma lem4444820 {A K : Type'} (_51121 : K) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term961 A K k z s _51121.
Proof. exact (@lem4444414 A K z s k x i' i h1 _51121). Qed.
Lemma lem4444821 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51121 : K) : (term961 A K k z s _51121) = (term695 A K k z s _51121).
Proof. exact (eq_refl (term961 A K k z s _51121)). Qed.
Lemma lem4444889 {A K : Type'} (_51144 : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term835 A _51144.
Proof. exact (@lem4444656 A K z s k x i' i h1 _51144). Qed.
Lemma lem4444890 {A : Type'} (_51144 : A) : (term835 A _51144) = (term822 A _51144).
Proof. exact (eq_refl (term835 A _51144)). Qed.
Lemma lem4444891 {A K : Type'} (_51144 : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term822 A _51144.
Proof. exact (EQ_MP (@lem4444890 A _51144) (@lem4444889 A K _51144 z s k x i' i h1)). Qed.
Lemma lem4444892 {A K : Type'} (_51144 : A) (_51145 : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term810 A _51144 _51145.
Proof. exact (@lem4444891 A K _51144 z s k x i' i h1 _51145). Qed.
Lemma lem4444893 {A : Type'} (_51144 : A) (_51145 : A) : (term810 A _51144 _51145) = (term811 A _51144 _51145).
Proof. exact (eq_refl (term810 A _51144 _51145)). Qed.
Lemma lem4444938 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') : i' = i.
Proof. exact (proj1 (@lem4443863 A K i x s i' h1)). Qed.
Lemma lem4444940 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') : term699 A K x s i'.
Proof. exact (proj2 (@lem4443863 A K i x s i' h1)). Qed.
Lemma lem4444950 {A K : Type'} (_51085 : K) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term695 A K k z s _51085.
Proof. exact (EQ_MP (@lem4444713 A K k z s _51085) (@lem4444712 A K _51085 z s k x i' i h1)). Qed.
Lemma lem4444980 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term707 A K i z s i') : term962 A K z s i'.
Proof. exact (proj2 (@lem4443864 A K i z s i' h1)). Qed.
Lemma lem4445016 {A K : Type'} (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term731 A K k x i' i) : term717 K i' k.
Proof. exact (proj1 (@lem4443860 A K k x i' i h1)). Qed.
Lemma lem4445018 {A K : Type'} (i' : K) (i : K) (x : A) (h1 : term720 A K i' i x) : i' = i.
Proof. exact (proj1 (@lem4443871 A K i' i x h1)). Qed.
Lemma lem4445048 {A K : Type'} (_51108 : A) (_51109 : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term811 A _51108 _51109.
Proof. exact (EQ_MP (@lem4444785 A _51108 _51109) (@lem4444784 A K _51108 _51109 z s k x i' i h1)). Qed.
Lemma lem4445060 {A K : Type'} (i' : K) (i : K) (h1 : term723 A K i' i) : term963 A.
Proof. exact (proj2 (@lem4443872 A K i' i h1)). Qed.
Lemma lem4445096 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term715 A K k x i z s i') : @IN K i' k.
Proof. exact (proj1 (@lem4443891 A K k x i z s i' h1)). Qed.
Lemma lem4445098 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') : i' = i.
Proof. exact (proj1 (@lem4443895 A K i x s i' h1)). Qed.
Lemma lem4445110 {A K : Type'} (_51121 : K) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term695 A K k z s _51121.
Proof. exact (EQ_MP (@lem4444821 A K k z s _51121) (@lem4444820 A K _51121 z s k x i' i h1)). Qed.
Lemma lem4445140 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term707 A K i z s i') : term962 A K z s i'.
Proof. exact (proj2 (@lem4443896 A K i z s i' h1)). Qed.
Lemma lem4445208 {A K : Type'} (_51144 : A) (_51145 : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term811 A _51144 _51145.
Proof. exact (EQ_MP (@lem4444893 A _51144 _51145) (@lem4444892 A K _51144 _51145 z s k x i' i h1)). Qed.
Lemma lem4445220 {A K : Type'} (i' : K) (i : K) (h1 : term723 A K i' i) : term963 A.
Proof. exact (proj2 (@lem4443904 A K i' i h1)). Qed.
Lemma lem4445346 {A K : Type'} (x : A) (s : type1470 A K) : (term964 A K x s) = (term964 A K x s).
Proof. exact (eq_refl (term964 A K x s)). Qed.
Lemma lem4445347 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') : (term965 A K x s i') = (term965 A K x s i).
Proof. exact (MK_COMB (@lem4445346 A K x s) (@lem4444938 A K i x s i' h1)). Qed.
Lemma lem4445348 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term965 A K x s i) = (term699 A K x s i).
Proof. exact (eq_refl (term965 A K x s i)). Qed.
Lemma lem4445349 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term966 A K x s i') = (term966 A K x s i').
Proof. exact (eq_refl (term966 A K x s i')). Qed.
Lemma lem4445350 {A K : Type'} (i' : K) (x : A) (s : type1470 A K) (i : K) : ((term965 A K x s i') = (term965 A K x s i)) = ((term965 A K x s i') = (term699 A K x s i)).
Proof. exact (MK_COMB (@lem4445349 A K x s i') (@lem4445348 A K x s i)). Qed.
Lemma lem4445351 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term965 A K x s i') = (term699 A K x s i').
Proof. exact (eq_refl (term965 A K x s i')). Qed.
Lemma lem4445352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4445353 {A K : Type'} (x : A) (s : type1470 A K) (i' : K) : (term966 A K x s i') = (term967 A K x s i').
Proof. exact (MK_COMB (@lem4445352) (@lem4445351 A K x s i')). Qed.
Lemma lem4445354 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term699 A K x s i) = (term699 A K x s i).
Proof. exact (eq_refl (term699 A K x s i)). Qed.
Lemma lem4445355 {A K : Type'} (i' : K) (x : A) (s : type1470 A K) (i : K) : ((term965 A K x s i') = (term699 A K x s i)) = ((term699 A K x s i') = (term699 A K x s i)).
Proof. exact (MK_COMB (@lem4445353 A K x s i') (@lem4445354 A K x s i)). Qed.
Lemma lem4445356 {A K : Type'} (i' : K) (x : A) (s : type1470 A K) (i : K) : ((term965 A K x s i') = (term965 A K x s i)) = ((term699 A K x s i') = (term699 A K x s i)).
Proof. exact (TRANS (@lem4445350 A K i' x s i) (@lem4445355 A K i' x s i)). Qed.
Lemma lem4445357 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') : (term699 A K x s i') = (term699 A K x s i).
Proof. exact (EQ_MP (@lem4445356 A K i' x s i) (@lem4445347 A K i x s i' h1)). Qed.
Lemma lem4445358 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') : term699 A K x s i.
Proof. exact (EQ_MP (@lem4445357 A K i x s i' h1) (@lem4444940 A K i x s i' h1)). Qed.
Lemma lem4445471 {K : Type'} (k : K -> Prop) : (term968 K k) = (term968 K k).
Proof. exact (eq_refl (term968 K k)). Qed.
Lemma lem4445472 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term720 A K i' i x) : (term969 K k i') = (term969 K k i).
Proof. exact (MK_COMB (@lem4445471 K k) (@lem4445018 A K i' i x h1)). Qed.
Lemma lem4445473 {K : Type'} (i : K) (k : K -> Prop) : (term969 K k i) = (term717 K i k).
Proof. exact (eq_refl (term969 K k i)). Qed.
Lemma lem4445474 {K : Type'} (k : K -> Prop) (i' : K) : (term970 K k i') = (term970 K k i').
Proof. exact (eq_refl (term970 K k i')). Qed.
Lemma lem4445475 {K : Type'} (i' : K) (i : K) (k : K -> Prop) : ((term969 K k i') = (term969 K k i)) = ((term969 K k i') = (term717 K i k)).
Proof. exact (MK_COMB (@lem4445474 K k i') (@lem4445473 K i k)). Qed.
Lemma lem4445476 {K : Type'} (i' : K) (k : K -> Prop) : (term969 K k i') = (term717 K i' k).
Proof. exact (eq_refl (term969 K k i')). Qed.
Lemma lem4445477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4445478 {K : Type'} (i' : K) (k : K -> Prop) : (term970 K k i') = (term971 K i' k).
Proof. exact (MK_COMB (@lem4445477) (@lem4445476 K i' k)). Qed.
Lemma lem4445479 {K : Type'} (i : K) (k : K -> Prop) : (term717 K i k) = (term717 K i k).
Proof. exact (eq_refl (term717 K i k)). Qed.
Lemma lem4445480 {K : Type'} (i' : K) (i : K) (k : K -> Prop) : ((term969 K k i') = (term717 K i k)) = ((term717 K i' k) = (term717 K i k)).
Proof. exact (MK_COMB (@lem4445478 K i' k) (@lem4445479 K i k)). Qed.
Lemma lem4445481 {K : Type'} (i' : K) (i : K) (k : K -> Prop) : ((term969 K k i') = (term969 K k i)) = ((term717 K i' k) = (term717 K i k)).
Proof. exact (TRANS (@lem4445475 K i' i k) (@lem4445480 K i' i k)). Qed.
Lemma lem4445482 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term720 A K i' i x) : (term717 K i' k) = (term717 K i k).
Proof. exact (EQ_MP (@lem4445481 K i' i k) (@lem4445472 A K k i' i x h1)). Qed.
Lemma lem4445483 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term731 A K k x i' i) (h2 : term720 A K i' i x) : term717 K i k.
Proof. exact (EQ_MP (@lem4445482 A K k i' i x h2) (@lem4445016 A K k x i' i h1)). Qed.
Lemma lem4445525 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term717 K i k.
Proof. exact (proj1 (@lem4443844 A K z s k x i' i h1)). Qed.
Lemma lem4445610 {K : Type'} (k : K -> Prop) : (term972 K k) = (term972 K k).
Proof. exact (eq_refl (term972 K k)). Qed.
Lemma lem4445611 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') : (term973 K k i') = (term973 K k i).
Proof. exact (MK_COMB (@lem4445610 K k) (@lem4445098 A K i x s i' h1)). Qed.
Lemma lem4445612 {K : Type'} (i : K) (k : K -> Prop) : (term973 K k i) = (@IN K i k).
Proof. exact (eq_refl (term973 K k i)). Qed.
Lemma lem4445613 {K : Type'} (k : K -> Prop) (i' : K) : (term974 K k i') = (term974 K k i').
Proof. exact (eq_refl (term974 K k i')). Qed.
Lemma lem4445614 {K : Type'} (i' : K) (i : K) (k : K -> Prop) : ((term973 K k i') = (term973 K k i)) = ((term973 K k i') = (@IN K i k)).
Proof. exact (MK_COMB (@lem4445613 K k i') (@lem4445612 K i k)). Qed.
Lemma lem4445615 {K : Type'} (i' : K) (k : K -> Prop) : (term973 K k i') = (@IN K i' k).
Proof. exact (eq_refl (term973 K k i')). Qed.
Lemma lem4445616 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4445617 {K : Type'} (i' : K) (k : K -> Prop) : (term974 K k i') = (term975 K i' k).
Proof. exact (MK_COMB (@lem4445616) (@lem4445615 K i' k)). Qed.
Lemma lem4445618 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@IN K i k).
Proof. exact (eq_refl (@IN K i k)). Qed.
Lemma lem4445619 {K : Type'} (i' : K) (i : K) (k : K -> Prop) : ((term973 K k i') = (@IN K i k)) = ((@IN K i' k) = (@IN K i k)).
Proof. exact (MK_COMB (@lem4445617 K i' k) (@lem4445618 K i k)). Qed.
Lemma lem4445620 {K : Type'} (i' : K) (i : K) (k : K -> Prop) : ((term973 K k i') = (term973 K k i)) = ((@IN K i' k) = (@IN K i k)).
Proof. exact (TRANS (@lem4445614 K i' i k) (@lem4445619 K i' i k)). Qed.
Lemma lem4445621 {A K : Type'} (k : K -> Prop) (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') : (@IN K i' k) = (@IN K i k).
Proof. exact (EQ_MP (@lem4445620 K i' i k) (@lem4445611 A K k i x s i' h1)). Qed.
Lemma lem4445774 {A K : Type'} (i' : K) (i : K) (x : A) (h1 : term720 A K i' i x) : term718 A x.
Proof. exact (proj2 (@lem4443903 A K i' i x h1)). Qed.
Lemma lem4445868 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term35 A K x s i.
Proof. exact (proj1 (@lem4443845 A K z s k x i' i h1)). Qed.
Lemma lem4445869 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term976 A K x s i.
Proof. exact (fun h0 : term699 A K x s i => @lem4445868 A K z s k x i' i h1). Qed.
Lemma lem4445871 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4445872 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term976 A K x s i) = (term35 A K x s i).
Proof. exact (@lem4445871 (term35 A K x s i)). Qed.
Lemma lem4445873 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term35 A K x s i.
Proof. exact (EQ_MP (@lem4445872 A K x s i) (@lem4445869 A K z s k x i' i h1)). Qed.
Lemma lem4445876 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4445878 {A K : Type'} (x : A) (s : type1470 A K) (i : K) : (term699 A K x s i) = (term977 A K x s i).
Proof. exact (@lem4445876 (term35 A K x s i)). Qed.
Lemma lem4445881 {A K : Type'} (i : K) (x : A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') : term977 A K x s i.
Proof. exact (EQ_MP (@lem4445878 A K x s i) (@lem4445358 A K i x s i' h1)). Qed.
Lemma lem4445884 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term703 A K i x s i') (h2 : term914 A K z s k x i' i) : False.
Proof. exact (@lem4445881 A K i x s i' h1 (@lem4445873 A K z s k x i' i h2)). Qed.
Lemma lem4445885 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term703 A K i x s i') (h2 : term914 A K z s k x i' i) : term342.
Proof. exact (fun h0 : ~ False => @lem4445884 A K z s k x i' i h1 h2). Qed.
Lemma lem4445887 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4445888 : term342 = False.
Proof. exact (@lem4445887 False). Qed.
Lemma lem4445983 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term715 A K k x i z s i') : @IN K i' k.
Proof. exact (proj1 (@lem4443859 A K k x i z s i' h1)). Qed.
Lemma lem4445984 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term715 A K k x i z s i') : term978 K i' k.
Proof. exact (fun h0 : term717 K i' k => @lem4445983 A K k x i z s i' h1). Qed.
Lemma lem4445986 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4445987 {K : Type'} (i' : K) (k : K -> Prop) : (term978 K i' k) = (@IN K i' k).
Proof. exact (@lem4445986 (@IN K i' k)). Qed.
Lemma lem4445988 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term715 A K k x i z s i') : @IN K i' k.
Proof. exact (EQ_MP (@lem4445987 K i' k) (@lem4445984 A K k x i z s i' h1)). Qed.
Lemma lem4445994 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4445995 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51085 : K) (k : K -> Prop) : (term695 A K k z s _51085) = (term979 A K z s _51085 k).
Proof. exact (@lem4445994 (term656 A K z s _51085) (term717 K _51085 k)). Qed.
Lemma lem4446001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4446002 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51085 : K) (k : K -> Prop) : (term980 A K k z s _51085) = (term981 A K z s _51085 k).
Proof. exact (MK_COMB (@lem4446001) (@lem4445995 A K z s _51085 k)). Qed.
Lemma lem4446008 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51085 : K) (k : K -> Prop) : (term979 A K z s _51085 k) = (term979 A K z s _51085 k).
Proof. exact (eq_refl (term979 A K z s _51085 k)). Qed.
Lemma lem4446009 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51085 : K) (k : K -> Prop) : ((term695 A K k z s _51085) = (term979 A K z s _51085 k)) = ((term979 A K z s _51085 k) = (term979 A K z s _51085 k)).
Proof. exact (MK_COMB (@lem4446002 A K z s _51085 k) (@lem4446008 A K z s _51085 k)). Qed.
Lemma lem4446011 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4446012 (x : Prop) : (x = x) = True.
Proof. exact (@lem4446011 Prop x). Qed.
Lemma lem4446013 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51085 : K) (k : K -> Prop) : ((term979 A K z s _51085 k) = (term979 A K z s _51085 k)) = True.
Proof. exact (@lem4446012 (term979 A K z s _51085 k)). Qed.
Lemma lem4446014 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51085 : K) (k : K -> Prop) : ((term695 A K k z s _51085) = (term979 A K z s _51085 k)) = True.
Proof. exact (TRANS (@lem4446009 A K z s _51085 k) (@lem4446013 A K z s _51085 k)). Qed.
Lemma lem4446015 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51085 : K) (k : K -> Prop) : True = ((term695 A K k z s _51085) = (term979 A K z s _51085 k)).
Proof. exact (SYM (@lem4446014 A K z s _51085 k)). Qed.
Lemma lem4446016 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51085 : K) (k : K -> Prop) : (term695 A K k z s _51085) = (term979 A K z s _51085 k).
Proof. exact (EQ_MP (@lem4446015 A K z s _51085 k) (@lem0)). Qed.
Lemma lem4446017 {A K : Type'} (_51085 : K) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term979 A K z s _51085 k.
Proof. exact (EQ_MP (@lem4446016 A K z s _51085 k) (@lem4444950 A K _51085 z s k x i' i h1)). Qed.
Lemma lem4446019 (b : Prop) (a : Prop) : (a \/ b) = (term333 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4446020 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51085 : K) : (term979 A K z s _51085 k) = (term982 A K k z s _51085).
Proof. exact (@lem4446019 (term717 K _51085 k) (term656 A K z s _51085)). Qed.
Lemma lem4446022 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4446023 {K : Type'} (_51085 : K) (k : K -> Prop) : (term694 K _51085 k) = (@IN K _51085 k).
Proof. exact (@lem4446022 (@IN K _51085 k)). Qed.
Lemma lem4446024 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4446025 {K : Type'} (_51085 : K) (k : K -> Prop) : (term983 K _51085 k) = (term47 K _51085 k).
Proof. exact (MK_COMB (@lem4446024) (@lem4446023 K _51085 k)). Qed.
Lemma lem4446026 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51085 : K) : (term656 A K z s _51085) = (term656 A K z s _51085).
Proof. exact (eq_refl (term656 A K z s _51085)). Qed.
Lemma lem4446027 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51085 : K) : (term982 A K k z s _51085) = (term503 A K k z s _51085).
Proof. exact (MK_COMB (@lem4446025 K _51085 k) (@lem4446026 A K z s _51085)). Qed.
Lemma lem4446028 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51085 : K) : (term979 A K z s _51085 k) = (term503 A K k z s _51085).
Proof. exact (TRANS (@lem4446020 A K k z s _51085) (@lem4446027 A K k z s _51085)). Qed.
Lemma lem4446031 {A K : Type'} (_51085 : K) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term503 A K k z s _51085.
Proof. exact (EQ_MP (@lem4446028 A K k z s _51085) (@lem4446017 A K _51085 z s k x i' i h1)). Qed.
Lemma lem4446032 {A K : Type'} (_51085 : K) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term503 A K k z s _51085.
Proof. exact (@lem4446031 A K _51085 z s k x i' i h1). Qed.
Lemma lem4446033 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term503 A K k z s i'.
Proof. exact (@lem4446032 A K i' z s k x i' i h1). Qed.
Lemma lem4446036 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term914 A K z s k x i' i) (h2 : term715 A K k x i z s i') : term656 A K z s i'.
Proof. exact (@lem4446033 A K z s k x i' i h1 (@lem4445988 A K k x i z s i' h2)). Qed.
Lemma lem4446037 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term914 A K z s k x i' i) (h2 : term715 A K k x i z s i') : term984 A K z s i'.
Proof. exact (fun h0 : term962 A K z s i' => @lem4446036 A K k x i z s i' h1 h2). Qed.
Lemma lem4446039 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446040 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) : (term984 A K z s i') = (term656 A K z s i').
Proof. exact (@lem4446039 (term656 A K z s i')). Qed.
Lemma lem4446041 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term914 A K z s k x i' i) (h2 : term715 A K k x i z s i') : term656 A K z s i'.
Proof. exact (EQ_MP (@lem4446040 A K z s i') (@lem4446037 A K k x i z s i' h1 h2)). Qed.
Lemma lem4446044 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4446046 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) : (term962 A K z s i') = (term985 A K z s i').
Proof. exact (@lem4446044 (term656 A K z s i')). Qed.
Lemma lem4446049 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term707 A K i z s i') : term985 A K z s i'.
Proof. exact (EQ_MP (@lem4446046 A K z s i') (@lem4444980 A K i z s i' h1)). Qed.
Lemma lem4446052 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term707 A K i z s i') (h2 : term914 A K z s k x i' i) (h3 : term715 A K k x i z s i') : False.
Proof. exact (@lem4446049 A K i z s i' h1 (@lem4446041 A K k x i z s i' h2 h3)). Qed.
Lemma lem4446053 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term707 A K i z s i') (h2 : term914 A K z s k x i' i) (h3 : term715 A K k x i z s i') : term342.
Proof. exact (fun h0 : ~ False => @lem4446052 A K k x i z s i' h1 h2 h3). Qed.
Lemma lem4446055 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446056 : term342 = False.
Proof. exact (@lem4446055 False). Qed.
Lemma lem4446057 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term707 A K i z s i') (h2 : term914 A K z s k x i' i) (h3 : term715 A K k x i z s i') : False.
Proof. exact (EQ_MP (@lem4446056) (@lem4446053 A K k x i z s i' h1 h2 h3)). Qed.
Lemma lem4446151 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : @IN K i k.
Proof. exact (proj1 (@lem4443843 A K z s k x i' i h1)). Qed.
Lemma lem4446152 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term978 K i k.
Proof. exact (fun h0 : term717 K i k => @lem4446151 A K z s k x i' i h1). Qed.
Lemma lem4446154 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446155 {K : Type'} (i : K) (k : K -> Prop) : (term978 K i k) = (@IN K i k).
Proof. exact (@lem4446154 (@IN K i k)). Qed.
Lemma lem4446156 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : @IN K i k.
Proof. exact (EQ_MP (@lem4446155 K i k) (@lem4446152 A K z s k x i' i h1)). Qed.
Lemma lem4446159 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4446161 {K : Type'} (i : K) (k : K -> Prop) : (term717 K i k) = (term986 K i k).
Proof. exact (@lem4446159 (@IN K i k)). Qed.
Lemma lem4446164 {A K : Type'} (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term731 A K k x i' i) (h2 : term720 A K i' i x) : term986 K i k.
Proof. exact (EQ_MP (@lem4446161 K i k) (@lem4445483 A K k i' i x h1 h2)). Qed.
Lemma lem4446167 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term731 A K k x i' i) (h2 : term720 A K i' i x) (h3 : term914 A K z s k x i' i) : False.
Proof. exact (@lem4446164 A K k i' i x h1 h2 (@lem4446156 A K z s k x i' i h3)). Qed.
Lemma lem4446168 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term731 A K k x i' i) (h2 : term720 A K i' i x) (h3 : term914 A K z s k x i' i) : term342.
Proof. exact (fun h0 : ~ False => @lem4446167 A K z s k x i' i h1 h2 h3). Qed.
Lemma lem4446170 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446171 : term342 = False.
Proof. exact (@lem4446170 False). Qed.
Lemma lem4446266 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4446267 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4446266 A x). Qed.
Lemma lem4446268 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (@lem4446267 A (@ARB A)). Qed.
Lemma lem4446269 {A : Type'} : term987 A.
Proof. exact (fun h0 : term988 A => @lem4446268 A). Qed.
Lemma lem4446271 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446272 {A : Type'} : (term987 A) = ((@ARB A) = (@ARB A)).
Proof. exact (@lem4446271 ((@ARB A) = (@ARB A))). Qed.
Lemma lem4446273 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (EQ_MP (@lem4446272 A) (@lem4446269 A)). Qed.
Lemma lem4446275 (b : Prop) (a : Prop) : (a \/ b) = (term333 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4446276 {A : Type'} (_51108 : A) (_51109 : A) : (term811 A _51108 _51109) = (term989 A _51108 _51109).
Proof. exact (@lem4446275 (term705 A _51108 _51109) (term622 A _51108 _51109)). Qed.
Lemma lem4446278 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4446279 {A : Type'} (_51108 : A) (_51109 : A) : (term698 A _51108 _51109) = (_51108 = _51109).
Proof. exact (@lem4446278 (_51108 = _51109)). Qed.
Lemma lem4446280 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4446281 {A : Type'} (_51108 : A) (_51109 : A) : (term990 A _51108 _51109) = (term991 A _51108 _51109).
Proof. exact (MK_COMB (@lem4446280) (@lem4446279 A _51108 _51109)). Qed.
Lemma lem4446282 {A : Type'} (_51108 : A) (_51109 : A) : (term622 A _51108 _51109) = (term622 A _51108 _51109).
Proof. exact (eq_refl (term622 A _51108 _51109)). Qed.
Lemma lem4446283 {A : Type'} (_51108 : A) (_51109 : A) : (term989 A _51108 _51109) = (term992 A _51108 _51109).
Proof. exact (MK_COMB (@lem4446281 A _51108 _51109) (@lem4446282 A _51108 _51109)). Qed.
Lemma lem4446284 {A : Type'} (_51108 : A) (_51109 : A) : (term811 A _51108 _51109) = (term992 A _51108 _51109).
Proof. exact (TRANS (@lem4446276 A _51108 _51109) (@lem4446283 A _51108 _51109)). Qed.
Lemma lem4446287 {A K : Type'} (_51108 : A) (_51109 : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term992 A _51108 _51109.
Proof. exact (EQ_MP (@lem4446284 A _51108 _51109) (@lem4445048 A K _51108 _51109 z s k x i' i h1)). Qed.
Lemma lem4446288 {A K : Type'} (_51108 : A) (_51109 : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term992 A _51108 _51109.
Proof. exact (@lem4446287 A K _51108 _51109 z s k x i' i h1). Qed.
Lemma lem4446289 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term993 A.
Proof. exact (@lem4446288 A K (@ARB A) (@ARB A) z s k x i' i h1). Qed.
Lemma lem4446292 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term646 A.
Proof. exact (@lem4446289 A K z s k x i' i h1 (@lem4446273 A)). Qed.
Lemma lem4446293 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term994 A.
Proof. exact (fun h0 : term963 A => @lem4446292 A K z s k x i' i h1). Qed.
Lemma lem4446295 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446296 {A : Type'} : (term994 A) = (term646 A).
Proof. exact (@lem4446295 (term646 A)). Qed.
Lemma lem4446297 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : term646 A.
Proof. exact (EQ_MP (@lem4446296 A) (@lem4446293 A K z s k x i' i h1)). Qed.
Lemma lem4446300 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4446302 {A : Type'} : (term963 A) = (term995 A).
Proof. exact (@lem4446300 (term646 A)). Qed.
Lemma lem4446305 {A K : Type'} (i' : K) (i : K) (h1 : term723 A K i' i) : term995 A.
Proof. exact (EQ_MP (@lem4446302 A) (@lem4445060 A K i' i h1)). Qed.
Lemma lem4446308 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term723 A K i' i) (h2 : term914 A K z s k x i' i) : False.
Proof. exact (@lem4446305 A K i' i h1 (@lem4446297 A K z s k x i' i h2)). Qed.
Lemma lem4446309 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term723 A K i' i) (h2 : term914 A K z s k x i' i) : term342.
Proof. exact (fun h0 : ~ False => @lem4446308 A K z s k x i' i h1 h2). Qed.
Lemma lem4446311 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446312 : term342 = False.
Proof. exact (@lem4446311 False). Qed.
Lemma lem4446313 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term723 A K i' i) (h2 : term914 A K z s k x i' i) : False.
Proof. exact (EQ_MP (@lem4446312) (@lem4446309 A K z s k x i' i h1 h2)). Qed.
Lemma lem4446407 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') (h2 : term715 A K k x i z s i') : @IN K i k.
Proof. exact (EQ_MP (@lem4445621 A K k i x s i' h1) (@lem4445096 A K k x i z s i' h2)). Qed.
Lemma lem4446408 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') (h2 : term715 A K k x i z s i') : term978 K i k.
Proof. exact (fun h0 : term717 K i k => @lem4446407 A K k x i z s i' h1 h2). Qed.
Lemma lem4446410 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446411 {K : Type'} (i : K) (k : K -> Prop) : (term978 K i k) = (@IN K i k).
Proof. exact (@lem4446410 (@IN K i k)). Qed.
Lemma lem4446412 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term703 A K i x s i') (h2 : term715 A K k x i z s i') : @IN K i k.
Proof. exact (EQ_MP (@lem4446411 K i k) (@lem4446408 A K k x i z s i' h1 h2)). Qed.
Lemma lem4446415 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4446417 {K : Type'} (i : K) (k : K -> Prop) : (term717 K i k) = (term986 K i k).
Proof. exact (@lem4446415 (@IN K i k)). Qed.
Lemma lem4446420 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term986 K i k.
Proof. exact (EQ_MP (@lem4446417 K i k) (@lem4445525 A K z s k x i' i h1)). Qed.
Lemma lem4446423 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term938 A K z s k x i' i) (h2 : term703 A K i x s i') (h3 : term715 A K k x i z s i') : False.
Proof. exact (@lem4446420 A K z s k x i' i h1 (@lem4446412 A K k x i z s i' h2 h3)). Qed.
Lemma lem4446424 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term938 A K z s k x i' i) (h2 : term703 A K i x s i') (h3 : term715 A K k x i z s i') : term342.
Proof. exact (fun h0 : ~ False => @lem4446423 A K k x i z s i' h1 h2 h3). Qed.
Lemma lem4446426 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446427 : term342 = False.
Proof. exact (@lem4446426 False). Qed.
Lemma lem4446522 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term715 A K k x i z s i') : @IN K i' k.
Proof. exact (proj1 (@lem4443891 A K k x i z s i' h1)). Qed.
Lemma lem4446523 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term715 A K k x i z s i') : term978 K i' k.
Proof. exact (fun h0 : term717 K i' k => @lem4446522 A K k x i z s i' h1). Qed.
Lemma lem4446525 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446526 {K : Type'} (i' : K) (k : K -> Prop) : (term978 K i' k) = (@IN K i' k).
Proof. exact (@lem4446525 (@IN K i' k)). Qed.
Lemma lem4446527 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term715 A K k x i z s i') : @IN K i' k.
Proof. exact (EQ_MP (@lem4446526 K i' k) (@lem4446523 A K k x i z s i' h1)). Qed.
Lemma lem4446533 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4446534 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51121 : K) (k : K -> Prop) : (term695 A K k z s _51121) = (term979 A K z s _51121 k).
Proof. exact (@lem4446533 (term656 A K z s _51121) (term717 K _51121 k)). Qed.
Lemma lem4446540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4446541 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51121 : K) (k : K -> Prop) : (term980 A K k z s _51121) = (term981 A K z s _51121 k).
Proof. exact (MK_COMB (@lem4446540) (@lem4446534 A K z s _51121 k)). Qed.
Lemma lem4446547 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51121 : K) (k : K -> Prop) : (term979 A K z s _51121 k) = (term979 A K z s _51121 k).
Proof. exact (eq_refl (term979 A K z s _51121 k)). Qed.
Lemma lem4446548 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51121 : K) (k : K -> Prop) : ((term695 A K k z s _51121) = (term979 A K z s _51121 k)) = ((term979 A K z s _51121 k) = (term979 A K z s _51121 k)).
Proof. exact (MK_COMB (@lem4446541 A K z s _51121 k) (@lem4446547 A K z s _51121 k)). Qed.
Lemma lem4446550 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4446551 (x : Prop) : (x = x) = True.
Proof. exact (@lem4446550 Prop x). Qed.
Lemma lem4446552 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51121 : K) (k : K -> Prop) : ((term979 A K z s _51121 k) = (term979 A K z s _51121 k)) = True.
Proof. exact (@lem4446551 (term979 A K z s _51121 k)). Qed.
Lemma lem4446553 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51121 : K) (k : K -> Prop) : ((term695 A K k z s _51121) = (term979 A K z s _51121 k)) = True.
Proof. exact (TRANS (@lem4446548 A K z s _51121 k) (@lem4446552 A K z s _51121 k)). Qed.
Lemma lem4446554 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51121 : K) (k : K -> Prop) : True = ((term695 A K k z s _51121) = (term979 A K z s _51121 k)).
Proof. exact (SYM (@lem4446553 A K z s _51121 k)). Qed.
Lemma lem4446555 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51121 : K) (k : K -> Prop) : (term695 A K k z s _51121) = (term979 A K z s _51121 k).
Proof. exact (EQ_MP (@lem4446554 A K z s _51121 k) (@lem0)). Qed.
Lemma lem4446556 {A K : Type'} (_51121 : K) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term979 A K z s _51121 k.
Proof. exact (EQ_MP (@lem4446555 A K z s _51121 k) (@lem4445110 A K _51121 z s k x i' i h1)). Qed.
Lemma lem4446558 (b : Prop) (a : Prop) : (a \/ b) = (term333 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4446559 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51121 : K) : (term979 A K z s _51121 k) = (term982 A K k z s _51121).
Proof. exact (@lem4446558 (term717 K _51121 k) (term656 A K z s _51121)). Qed.
Lemma lem4446561 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4446562 {K : Type'} (_51121 : K) (k : K -> Prop) : (term694 K _51121 k) = (@IN K _51121 k).
Proof. exact (@lem4446561 (@IN K _51121 k)). Qed.
Lemma lem4446563 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4446564 {K : Type'} (_51121 : K) (k : K -> Prop) : (term983 K _51121 k) = (term47 K _51121 k).
Proof. exact (MK_COMB (@lem4446563) (@lem4446562 K _51121 k)). Qed.
Lemma lem4446565 {A K : Type'} (z : K -> A) (s : type1470 A K) (_51121 : K) : (term656 A K z s _51121) = (term656 A K z s _51121).
Proof. exact (eq_refl (term656 A K z s _51121)). Qed.
Lemma lem4446566 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51121 : K) : (term982 A K k z s _51121) = (term503 A K k z s _51121).
Proof. exact (MK_COMB (@lem4446564 K _51121 k) (@lem4446565 A K z s _51121)). Qed.
Lemma lem4446567 {A K : Type'} (k : K -> Prop) (z : K -> A) (s : type1470 A K) (_51121 : K) : (term979 A K z s _51121 k) = (term503 A K k z s _51121).
Proof. exact (TRANS (@lem4446559 A K k z s _51121) (@lem4446566 A K k z s _51121)). Qed.
Lemma lem4446570 {A K : Type'} (_51121 : K) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term503 A K k z s _51121.
Proof. exact (EQ_MP (@lem4446567 A K k z s _51121) (@lem4446556 A K _51121 z s k x i' i h1)). Qed.
Lemma lem4446571 {A K : Type'} (_51121 : K) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term503 A K k z s _51121.
Proof. exact (@lem4446570 A K _51121 z s k x i' i h1). Qed.
Lemma lem4446572 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term503 A K k z s i'.
Proof. exact (@lem4446571 A K i' z s k x i' i h1). Qed.
Lemma lem4446575 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term938 A K z s k x i' i) (h2 : term715 A K k x i z s i') : term656 A K z s i'.
Proof. exact (@lem4446572 A K z s k x i' i h1 (@lem4446527 A K k x i z s i' h2)). Qed.
Lemma lem4446576 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term938 A K z s k x i' i) (h2 : term715 A K k x i z s i') : term984 A K z s i'.
Proof. exact (fun h0 : term962 A K z s i' => @lem4446575 A K k x i z s i' h1 h2). Qed.
Lemma lem4446578 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446579 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) : (term984 A K z s i') = (term656 A K z s i').
Proof. exact (@lem4446578 (term656 A K z s i')). Qed.
Lemma lem4446580 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term938 A K z s k x i' i) (h2 : term715 A K k x i z s i') : term656 A K z s i'.
Proof. exact (EQ_MP (@lem4446579 A K z s i') (@lem4446576 A K k x i z s i' h1 h2)). Qed.
Lemma lem4446583 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4446585 {A K : Type'} (z : K -> A) (s : type1470 A K) (i' : K) : (term962 A K z s i') = (term985 A K z s i').
Proof. exact (@lem4446583 (term656 A K z s i')). Qed.
Lemma lem4446588 {A K : Type'} (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term707 A K i z s i') : term985 A K z s i'.
Proof. exact (EQ_MP (@lem4446585 A K z s i') (@lem4445140 A K i z s i' h1)). Qed.
Lemma lem4446591 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term707 A K i z s i') (h2 : term938 A K z s k x i' i) (h3 : term715 A K k x i z s i') : False.
Proof. exact (@lem4446588 A K i z s i' h1 (@lem4446580 A K k x i z s i' h2 h3)). Qed.
Lemma lem4446592 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term707 A K i z s i') (h2 : term938 A K z s k x i' i) (h3 : term715 A K k x i z s i') : term342.
Proof. exact (fun h0 : ~ False => @lem4446591 A K k x i z s i' h1 h2 h3). Qed.
Lemma lem4446594 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446595 : term342 = False.
Proof. exact (@lem4446594 False). Qed.
Lemma lem4446596 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term707 A K i z s i') (h2 : term938 A K z s k x i' i) (h3 : term715 A K k x i z s i') : False.
Proof. exact (EQ_MP (@lem4446595) (@lem4446592 A K k x i z s i' h1 h2 h3)). Qed.
Lemma lem4446690 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term609 A x.
Proof. exact (proj1 (@lem4443877 A K z s k x i' i h1)). Qed.
Lemma lem4446691 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term996 A x.
Proof. exact (fun h0 : term718 A x => @lem4446690 A K z s k x i' i h1). Qed.
Lemma lem4446693 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446694 {A : Type'} (x : A) : (term996 A x) = (term609 A x).
Proof. exact (@lem4446693 (term609 A x)). Qed.
Lemma lem4446695 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term609 A x.
Proof. exact (EQ_MP (@lem4446694 A x) (@lem4446691 A K z s k x i' i h1)). Qed.
Lemma lem4446698 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4446700 {A : Type'} (x : A) : (term718 A x) = (term997 A x).
Proof. exact (@lem4446698 (term609 A x)). Qed.
Lemma lem4446703 {A K : Type'} (i' : K) (i : K) (x : A) (h1 : term720 A K i' i x) : term997 A x.
Proof. exact (EQ_MP (@lem4446700 A x) (@lem4445774 A K i' i x h1)). Qed.
Lemma lem4446706 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term938 A K z s k x i' i) (h2 : term720 A K i' i x) : False.
Proof. exact (@lem4446703 A K i' i x h2 (@lem4446695 A K z s k x i' i h1)). Qed.
Lemma lem4446707 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term938 A K z s k x i' i) (h2 : term720 A K i' i x) : term342.
Proof. exact (fun h0 : ~ False => @lem4446706 A K z s k i' i x h1 h2). Qed.
Lemma lem4446709 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446710 : term342 = False.
Proof. exact (@lem4446709 False). Qed.
Lemma lem4446805 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4446806 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4446805 A x). Qed.
Lemma lem4446807 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (@lem4446806 A (@ARB A)). Qed.
Lemma lem4446808 {A : Type'} : term987 A.
Proof. exact (fun h0 : term988 A => @lem4446807 A). Qed.
Lemma lem4446810 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446811 {A : Type'} : (term987 A) = ((@ARB A) = (@ARB A)).
Proof. exact (@lem4446810 ((@ARB A) = (@ARB A))). Qed.
Lemma lem4446812 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (EQ_MP (@lem4446811 A) (@lem4446808 A)). Qed.
Lemma lem4446814 (b : Prop) (a : Prop) : (a \/ b) = (term333 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4446815 {A : Type'} (_51144 : A) (_51145 : A) : (term811 A _51144 _51145) = (term989 A _51144 _51145).
Proof. exact (@lem4446814 (term705 A _51144 _51145) (term622 A _51144 _51145)). Qed.
Lemma lem4446817 (a : Prop) : (term65 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4446818 {A : Type'} (_51144 : A) (_51145 : A) : (term698 A _51144 _51145) = (_51144 = _51145).
Proof. exact (@lem4446817 (_51144 = _51145)). Qed.
Lemma lem4446819 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4446820 {A : Type'} (_51144 : A) (_51145 : A) : (term990 A _51144 _51145) = (term991 A _51144 _51145).
Proof. exact (MK_COMB (@lem4446819) (@lem4446818 A _51144 _51145)). Qed.
Lemma lem4446821 {A : Type'} (_51144 : A) (_51145 : A) : (term622 A _51144 _51145) = (term622 A _51144 _51145).
Proof. exact (eq_refl (term622 A _51144 _51145)). Qed.
Lemma lem4446822 {A : Type'} (_51144 : A) (_51145 : A) : (term989 A _51144 _51145) = (term992 A _51144 _51145).
Proof. exact (MK_COMB (@lem4446820 A _51144 _51145) (@lem4446821 A _51144 _51145)). Qed.
Lemma lem4446823 {A : Type'} (_51144 : A) (_51145 : A) : (term811 A _51144 _51145) = (term992 A _51144 _51145).
Proof. exact (TRANS (@lem4446815 A _51144 _51145) (@lem4446822 A _51144 _51145)). Qed.
Lemma lem4446826 {A K : Type'} (_51144 : A) (_51145 : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term992 A _51144 _51145.
Proof. exact (EQ_MP (@lem4446823 A _51144 _51145) (@lem4445208 A K _51144 _51145 z s k x i' i h1)). Qed.
Lemma lem4446827 {A K : Type'} (_51144 : A) (_51145 : A) (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term992 A _51144 _51145.
Proof. exact (@lem4446826 A K _51144 _51145 z s k x i' i h1). Qed.
Lemma lem4446828 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term993 A.
Proof. exact (@lem4446827 A K (@ARB A) (@ARB A) z s k x i' i h1). Qed.
Lemma lem4446831 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term646 A.
Proof. exact (@lem4446828 A K z s k x i' i h1 (@lem4446812 A)). Qed.
Lemma lem4446832 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term994 A.
Proof. exact (fun h0 : term963 A => @lem4446831 A K z s k x i' i h1). Qed.
Lemma lem4446834 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446835 {A : Type'} : (term994 A) = (term646 A).
Proof. exact (@lem4446834 (term646 A)). Qed.
Lemma lem4446836 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : term646 A.
Proof. exact (EQ_MP (@lem4446835 A) (@lem4446832 A K z s k x i' i h1)). Qed.
Lemma lem4446839 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4446841 {A : Type'} : (term963 A) = (term995 A).
Proof. exact (@lem4446839 (term646 A)). Qed.
Lemma lem4446844 {A K : Type'} (i' : K) (i : K) (h1 : term723 A K i' i) : term995 A.
Proof. exact (EQ_MP (@lem4446841 A) (@lem4445220 A K i' i h1)). Qed.
Lemma lem4446847 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term723 A K i' i) (h2 : term938 A K z s k x i' i) : False.
Proof. exact (@lem4446844 A K i' i h1 (@lem4446836 A K z s k x i' i h2)). Qed.
Lemma lem4446848 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term723 A K i' i) (h2 : term938 A K z s k x i' i) : term342.
Proof. exact (fun h0 : ~ False => @lem4446847 A K z s k x i' i h1 h2). Qed.
Lemma lem4446850 (p : Prop) : (term328 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4446851 : term342 = False.
Proof. exact (@lem4446850 False). Qed.
Lemma lem4446852 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term723 A K i' i) (h2 : term938 A K z s k x i' i) : False.
Proof. exact (EQ_MP (@lem4446851) (@lem4446848 A K z s k x i' i h1 h2)). Qed.
Lemma lem4446853 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (i' : K) (i : K) (x : A) (h1 : term938 A K z s k x i' i) (h2 : term720 A K i' i x) : False.
Proof. exact (EQ_MP (@lem4446710) (@lem4446707 A K z s k i' i x h1 h2)). Qed.
Lemma lem4446854 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term938 A K z s k x i' i) (h2 : term703 A K i x s i') (h3 : term715 A K k x i z s i') : False.
Proof. exact (EQ_MP (@lem4446427) (@lem4446424 A K k x i z s i' h1 h2 h3)). Qed.
Lemma lem4446855 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term731 A K k x i' i) (h2 : term720 A K i' i x) (h3 : term914 A K z s k x i' i) : False.
Proof. exact (EQ_MP (@lem4446171) (@lem4446168 A K z s k x i' i h1 h2 h3)). Qed.
Lemma lem4446856 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term703 A K i x s i') (h2 : term914 A K z s k x i' i) : False.
Proof. exact (EQ_MP (@lem4445888) (@lem4445885 A K z s k x i' i h1 h2)). Qed.
Lemma lem4446857 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) (h2 : term731 A K k x i' i) : False.
Proof. exact (or_elim (@lem4443901 A K k x i' i h2) (fun h0 : term720 A K i' i x => @lem4446853 A K z s k i' i x h1 h0) (fun h0 : term723 A K i' i => @lem4446852 A K z s k x i' i h0 h1)). Qed.
Lemma lem4446858 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term938 A K z s k x i' i) (h2 : term715 A K k x i z s i') : False.
Proof. exact (or_elim (@lem4443893 A K k x i z s i' h2) (fun h0 : term703 A K i x s i' => @lem4446854 A K k x i z s i' h1 h0 h2) (fun h0 : term707 A K i z s i' => @lem4446596 A K k x i z s i' h0 h1 h2)). Qed.
Lemma lem4446859 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term938 A K z s k x i' i) : False.
Proof. exact (or_elim (@lem4443884 A K z s k x i' i h1) (fun h0 : term715 A K k x i z s i' => @lem4446858 A K k x i z s i' h1 h0) (fun h0 : term731 A K k x i' i => @lem4446857 A K z s k x i' i h1 h0)). Qed.
Lemma lem4446860 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term731 A K k x i' i) (h2 : term914 A K z s k x i' i) : False.
Proof. exact (or_elim (@lem4443869 A K k x i' i h1) (fun h0 : term720 A K i' i x => @lem4446855 A K z s k x i' i h1 h0 h2) (fun h0 : term723 A K i' i => @lem4446313 A K z s k x i' i h0 h2)). Qed.
Lemma lem4446861 {A K : Type'} (k : K -> Prop) (x : A) (i : K) (z : K -> A) (s : type1470 A K) (i' : K) (h1 : term914 A K z s k x i' i) (h2 : term715 A K k x i z s i') : False.
Proof. exact (or_elim (@lem4443861 A K k x i z s i' h2) (fun h0 : term703 A K i x s i' => @lem4446856 A K z s k x i' i h0 h1) (fun h0 : term707 A K i z s i' => @lem4446057 A K k x i z s i' h0 h1 h2)). Qed.
Lemma lem4446862 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term914 A K z s k x i' i) : False.
Proof. exact (or_elim (@lem4443852 A K z s k x i' i h1) (fun h0 : term715 A K k x i z s i' => @lem4446861 A K k x i z s i' h1 h0) (fun h0 : term731 A K k x i' i => @lem4446860 A K z s k x i' i h0 h1)). Qed.
Lemma lem4446863 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term957 A K z s k x i' i) : False.
Proof. exact (or_elim (@lem4443842 A K z s k x i' i h1) (fun h0 : term914 A K z s k x i' i => @lem4446862 A K z s k x i' i h0) (fun h0 : term938 A K z s k x i' i => @lem4446859 A K z s k x i' i h0)). Qed.
Lemma lem4446864 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term957 A K z s k x i' i) : (term957 A K z s k x i' i) = False.
Proof. exact (prop_ext (fun h2 : term957 A K z s k x i' i => @lem4446863 A K z s k x i' i h1) (fun h2 : False => @lem4443842 A K z s k x i' i h1)). Qed.
Lemma lem4446865 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i' : K) (i : K) (h1 : term957 A K z s k x i' i) : False.
Proof. exact (EQ_MP (@lem4446864 A K z s k x i' i h1) (@lem4443842 A K z s k x i' i h1)). Qed.
Lemma lem4446866 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) (h1 : term693 A K z s k x i) : False.
Proof. exact (ex_elim (@lem4443313 A K z s k x i h1) (fun i' : K => fun h0 : term959 A K z s k x i i' => @lem4446865 A K z s k x i' i h0)). Qed.
Lemma lem4446867 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) (h1 : term693 A K z s k x i) : (term693 A K z s k x i) = False.
Proof. exact (prop_ext (fun h2 : term693 A K z s k x i => @lem4446866 A K z s k x i h1) (fun h2 : False => @lem4441301 A K z s k x i h1)). Qed.
Lemma lem4446868 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) (h1 : term693 A K z s k x i) : False.
Proof. exact (EQ_MP (@lem4446867 A K z s k x i h1) (@lem4441301 A K z s k x i h1)). Qed.
Lemma lem4446869 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : term692 A K z s k x i.
Proof. exact (fun h0 : term693 A K z s k x i => @lem4446868 A K z s k x i h0). Qed.
Lemma lem4446870 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) (i : K) : term680 A K z s k x i.
Proof. exact (EQ_MP (@lem4441300 A K z s k x i) (@lem4446869 A K z s k x i)). Qed.
Lemma lem4446875 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) (x : A) : term683 A K z s k x.
Proof. exact (fun i : K => @lem4446870 A K z s k x i). Qed.
Lemma lem4446880 {A K : Type'} (z : K -> A) (s : type1470 A K) (k : K -> Prop) : term685 A K z s k.
Proof. exact (fun x : A => @lem4446875 A K z s k x). Qed.
Lemma lem4446885 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : term687 A K s k.
Proof. exact (fun z : K -> A => @lem4446880 A K z s k). Qed.
Lemma lem4446890 {A K : Type'} (s : type1470 A K) : term689 A K s.
Proof. exact (fun k : K -> Prop => @lem4446885 A K s k). Qed.
Lemma lem4446895 {A K : Type'} : term691 A K.
Proof. exact (fun s : type1470 A K => @lem4446890 A K s). Qed.
Lemma lem4446896 {A K : Type'} : term603 A K.
Proof. exact (EQ_MP (@lem4441296 A K) (@lem4446895 A K)). Qed.
Lemma lem4446897 {A K : Type'} (s : type1470 A K) : term998 A K s.
Proof. exact (@lem4446896 A K s). Qed.
Lemma lem4446898 {A K : Type'} (s : type1470 A K) : (term998 A K s) = (term599 A K s).
Proof. exact (eq_refl (term998 A K s)). Qed.
Lemma lem4446899 {A K : Type'} (s : type1470 A K) : term599 A K s.
Proof. exact (EQ_MP (@lem4446898 A K s) (@lem4446897 A K s)). Qed.
Lemma lem4446900 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : term999 A K s k.
Proof. exact (@lem4446899 A K s k). Qed.
Lemma lem4446901 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term999 A K s k) = (term595 A K k s).
Proof. exact (eq_refl (term999 A K s k)). Qed.
Lemma lem4446902 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term595 A K k s.
Proof. exact (EQ_MP (@lem4446901 A K k s) (@lem4446900 A K s k)). Qed.
Lemma lem4446903 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (z : K -> A) : term1000 A K k s z.
Proof. exact (@lem4446902 A K k s z). Qed.
Lemma lem4446904 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term1000 A K k s z) = (term591 A K z k s).
Proof. exact (eq_refl (term1000 A K k s z)). Qed.
Lemma lem4446905 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) : term591 A K z k s.
Proof. exact (EQ_MP (@lem4446904 A K z k s) (@lem4446903 A K k s z)). Qed.
Lemma lem4446906 {A K : Type'} (z : K -> A) (k : K -> Prop) (s : type1470 A K) (x : A) : term1001 A K z k s x.
Proof. exact (@lem4446905 A K z k s x). Qed.
Lemma lem4446907 {A K : Type'} (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term1001 A K z k s x) = (term587 A K x z k s).
Proof. exact (eq_refl (term1001 A K z k s x)). Qed.
Lemma lem4446908 {A K : Type'} (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : term587 A K x z k s.
Proof. exact (EQ_MP (@lem4446907 A K x z k s) (@lem4446906 A K z k s x)). Qed.
Lemma lem4446909 {A K : Type'} (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) (i : K) : term1002 A K x z k s i.
Proof. exact (@lem4446908 A K x z k s i). Qed.
Lemma lem4446910 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : (term1002 A K x z k s i) = (term569 A K i x z k s).
Proof. exact (eq_refl (term1002 A K x z k s i)). Qed.
Lemma lem4446911 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : term569 A K i x z k s.
Proof. exact (EQ_MP (@lem4446910 A K i x z k s) (@lem4446909 A K x z k s i)). Qed.
Lemma lem4446913 {A K : Type'} (i : K) (x : A) (z : K -> A) (k : K -> Prop) (s : type1470 A K) : term569 A K i x z k s.
Proof. exact (@lem4440210 A K i x z k s (@lem4446911 A K i x z k s)). Qed.
Lemma lem4446914 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term397 A K x k s i) : term581 A K i x z k s.
Proof. exact (@lem4446913 A K i x z k s (@lem4439895 A K x k s i h1)). Qed.
Lemma lem4446915 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term507 A K k z s) (h2 : term397 A K x k s i) : term579 A K i x z k s.
Proof. exact (@lem4446914 A K z x k s i h2 (@lem4440032 A K k z s h1)). Qed.
Lemma lem4446916 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term507 A K k z s) (h2 : term567 A K i x z k s) (h3 : term397 A K x k s i) : term576 A K.
Proof. exact (@lem4446915 A K z x k s i h1 h3 (@lem4440189 A K i x z k s h2)). Qed.
Lemma lem4446917 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term507 A K k z s) (h2 : term567 A K i x z k s) (h3 : term397 A K x k s i) : term573 K.
Proof. exact (@lem4446916 A K z x k s i h1 h2 h3 (@lem4440190 A)). Qed.
Lemma lem4446918 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term507 A K k z s) (h2 : term567 A K i x z k s) (h3 : term397 A K x k s i) : False.
Proof. exact (@lem4446917 A K z x k s i h1 h2 h3 (@lem4440191 K)). Qed.
Lemma lem4446919 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term507 A K k z s) (h2 : term567 A K i x z k s) (h3 : term397 A K x k s i) : (term567 A K i x z k s) = False.
Proof. exact (prop_ext (fun h4 : term567 A K i x z k s => @lem4446918 A K z x k s i h1 h2 h3) (fun h4 : False => @lem4440189 A K i x z k s h2)). Qed.
Lemma lem4446920 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term507 A K k z s) (h2 : term567 A K i x z k s) (h3 : term397 A K x k s i) : False.
Proof. exact (EQ_MP (@lem4446919 A K z x k s i h1 h2 h3) (@lem4440189 A K i x z k s h2)). Qed.
Lemma lem4446921 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term507 A K k z s) (h2 : term397 A K x k s i) : term566 A K i x z k s.
Proof. exact (fun h0 : term567 A K i x z k s => @lem4446920 A K z x k s i h1 h0 h2). Qed.
Lemma lem4446922 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term507 A K k z s) (h2 : term397 A K x k s i) : term563 A K i x z k s.
Proof. exact (EQ_MP (@lem4440188 A K i x z k s) (@lem4446921 A K z x k s i h1 h2)). Qed.
Lemma lem4446923 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term507 A K k z s) (h2 : term397 A K x k s i) : term564 A K i x z k s.
Proof. exact (EQ_MP (@lem4440184 A K i x z k s) (@lem4446922 A K z x k s i h1 h2)). Qed.
Lemma lem4446924 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term507 A K k z s) (h2 : term397 A K x k s i) : term539 A K x i k s.
Proof. exact (ex_intro (term538 A K x i k s) (term543 A K i x k z) (@lem4446923 A K z x k s i h1 h2)). Qed.
Lemma lem4446925 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term507 A K k z s) (h2 : term397 A K x k s i) : term477 A K x i k s.
Proof. exact (EQ_MP (@lem4440101 A K x i k s) (@lem4446924 A K z x k s i h1 h2)). Qed.
Lemma lem4446926 {A K : Type'} (z : K -> A) (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term397 A K x k s i) : term526 A K z x i k s.
Proof. exact (fun h0 : term507 A K k z s => @lem4446925 A K z x k s i h0 h1). Qed.
Lemma lem4446931 {A K : Type'} (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term397 A K x k s i) : term529 A K x i k s.
Proof. exact (fun z : K -> A => @lem4446926 A K z x k s i h1). Qed.
Lemma lem4446932 {A K : Type'} (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term397 A K x k s i) : term489 A K x i k s.
Proof. exact (EQ_MP (@lem4440031 A K x i k s) (@lem4446931 A K x k s i h1)). Qed.
Lemma lem4446933 {A K : Type'} (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term397 A K x k s i) : term488 A K x i k s.
Proof. exact (EQ_MP (@lem4439931 A K x i k s) (@lem4446932 A K x k s i h1)). Qed.
Lemma lem4446934 {A K : Type'} (x : A) (k : K -> Prop) (s : type1470 A K) (i : K) (h1 : term374 A K k s) (h2 : term397 A K x k s i) : term477 A K x i k s.
Proof. exact (@lem4446933 A K x k s i h2 (@lem4439901 A K k s h1)). Qed.
Lemma lem4446935 {A K : Type'} (x : A) (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : term481 A K x i k s.
Proof. exact (fun h0 : term397 A K x k s i => @lem4446934 A K x k s i h1 h0). Qed.
Lemma lem4446940 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : term484 A K i k s.
Proof. exact (fun x : A => @lem4446935 A K x i k s h1). Qed.
Lemma lem4446941 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : term430 A K i k s.
Proof. exact (EQ_MP (@lem4439894 A K i k s) (@lem4446940 A K i k s h1)). Qed.
Lemma lem4446942 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : (term376 A K i k s) = (term383 A K k s i).
Proof. exact (EQ_MP (@lem4438851 A K k s i) (@lem4446941 A K i k s h1)). Qed.
Lemma lem4446943 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (h1 : term374 A K k s) : (term376 A K i k s) = (term384 A K k s i).
Proof. exact (EQ_MP (@lem4438766 A K i k s h1) (@lem4446942 A K i k s h1)). Qed.
Lemma lem4446944 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (i : K) : (term376 A K i k s) = (term384 A K k s i).
Proof. exact (or_elim (@lem4438678 A K k s) (fun h0 : (@cartesian_product A K k s) = (@EMPTY (K -> A)) => @lem4438729 A K i k s h0) (fun h0 : term374 A K k s => @lem4446943 A K i k s h0)). Qed.
Lemma lem4446949 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term1003 A K k s.
Proof. exact (fun i : K => @lem4446944 A K k s i). Qed.
Lemma lem4446954 {A K : Type'} (k : K -> Prop) : term1004 A K k.
Proof. exact (fun s : type1470 A K => @lem4446949 A K k s). Qed.
Lemma lem4446959 {A K : Type'} : term1005 A K.
Proof. exact (fun k : K -> Prop => @lem4446954 A K k). Qed.
