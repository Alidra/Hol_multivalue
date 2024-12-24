Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_IMP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import pairwise_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Lemma lem4794991 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4794992 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4794993 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4794992 t1) (@lem4794991 t1)). Qed.
Lemma lem4794994 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4794993 t1 t2). Qed.
Lemma lem4794995 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4794996 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4794995 t1 t2) (@lem4794994 t1 t2)). Qed.
Lemma lem4794997 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4794996 t1 t2 t3). Qed.
Lemma lem4794998 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4794999 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4794998 t1 t2 t3) (@lem4794997 t1 t2 t3)). Qed.
Lemma lem4795000 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4794999 t1 t2 t3)). Qed.
Lemma lem4795001 {_110510 : Type'} (s : _110510 -> Prop) : term7 _110510 s.
Proof. exact (@lem4794393 _110510 s). Qed.
Lemma lem4795002 {_110510 : Type'} (s : _110510 -> Prop) : (term7 _110510 s) = (term8 _110510 s).
Proof. exact (eq_refl (term7 _110510 s)). Qed.
Lemma lem4795003 {_110510 : Type'} (s : _110510 -> Prop) : term8 _110510 s.
Proof. exact (EQ_MP (@lem4795002 _110510 s) (@lem4795001 _110510 s)). Qed.
Lemma lem4795004 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : term9 _110510 s r.
Proof. exact (@lem4795003 _110510 s r). Qed.
Lemma lem4795005 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (term9 _110510 s r) = ((@pairwise _110510 r s) = (term10 _110510 s r)).
Proof. exact (eq_refl (term9 _110510 s r)). Qed.
Lemma lem4795024 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term10 _110510 s r).
Proof. exact (EQ_MP (@lem4795005 _110510 s r) (@lem4795004 _110510 s r)). Qed.
Lemma lem4795025 {A : Type'} (s : A -> Prop) (r : type1402 A) : (@pairwise A r s) = (term10 A s r).
Proof. exact (@lem4795024 A s r). Qed.
Lemma lem4795026 {A : Type'} (s : A -> Prop) (P : type1402 A) : (@pairwise A P s) = (term10 A s P).
Proof. exact (@lem4795025 A s P). Qed.
Lemma lem4795043 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4795044 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term11 A P s) = (term12 A s P).
Proof. exact (MK_COMB (@lem4795043) (@lem4795026 A s P)). Qed.
Lemma lem4795063 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term13 A s P Q) = (term13 A s P Q).
Proof. exact (eq_refl (term13 A s P Q)). Qed.
Lemma lem4795064 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term14 A s P Q) = (term15 A s P Q).
Proof. exact (MK_COMB (@lem4795044 A s P) (@lem4795063 A s P Q)). Qed.
Lemma lem4795067 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4795068 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term16 A s P Q) = (term17 A s P Q).
Proof. exact (MK_COMB (@lem4795067) (@lem4795064 A s P Q)). Qed.
Lemma lem4795070 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term10 _110510 s r).
Proof. exact (EQ_MP (@lem4795005 _110510 s r) (@lem4795004 _110510 s r)). Qed.
Lemma lem4795071 {A : Type'} (s : A -> Prop) (r : type1402 A) : (@pairwise A r s) = (term10 A s r).
Proof. exact (@lem4795070 A s r). Qed.
Lemma lem4795072 {A : Type'} (s : A -> Prop) (Q : type1402 A) : (@pairwise A Q s) = (term10 A s Q).
Proof. exact (@lem4795071 A s Q). Qed.
Lemma lem4795089 {A : Type'} (P : type1402 A) (s : A -> Prop) (Q : type1402 A) : (term18 A P Q s) = (term19 A P s Q).
Proof. exact (MK_COMB (@lem4795068 A s P Q) (@lem4795072 A s Q)). Qed.
Lemma lem4795092 {A : Type'} (P : type1402 A) (Q : type1402 A) : (term20 A P Q) = (term21 A P Q).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4795089 A P s Q)). Qed.
Lemma lem4795093 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4795094 {A : Type'} (P : type1402 A) (Q : type1402 A) : (term22 A P Q) = (term23 A P Q).
Proof. exact (MK_COMB (@lem4795093 A) (@lem4795092 A P Q)). Qed.
Lemma lem4795099 {A : Type'} (P : type1402 A) : (term24 A P) = (term25 A P).
Proof. exact (fun_ext (fun Q : type1402 A => @lem4795094 A P Q)). Qed.
Lemma lem4795100 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4795101 {A : Type'} (P : type1402 A) : (term26 A P) = (term27 A P).
Proof. exact (MK_COMB (@lem4795100 A) (@lem4795099 A P)). Qed.
Lemma lem4795106 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (fun_ext (fun P : type1402 A => @lem4795101 A P)). Qed.
Lemma lem4795107 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4795108 {A : Type'} : (term30 A) = (term31 A).
Proof. exact (MK_COMB (@lem4795107 A) (@lem4795106 A)). Qed.
Lemma lem4795113 {A : Type'} : (term31 A) = (term30 A).
Proof. exact (SYM (@lem4795108 A)). Qed.
Lemma lem4795217 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4795218 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4795217 A P x). Qed.
Lemma lem4795219 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4795218 A s x). Qed.
Lemma lem4795220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4795221 {A : Type'} (s : A -> Prop) (x : A) : (term32 A x s) = (term33 A s x).
Proof. exact (MK_COMB (@lem4795220) (@lem4795219 A s x)). Qed.
Lemma lem4795225 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4795226 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4795225 A P x). Qed.
Lemma lem4795227 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem4795226 A s y). Qed.
Lemma lem4795228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4795229 {A : Type'} (s : A -> Prop) (y : A) : (term32 A y s) = (term33 A s y).
Proof. exact (MK_COMB (@lem4795228) (@lem4795227 A s y)). Qed.
Lemma lem4795232 {A : Type'} (x : A) (y : A) : (term34 A x y) = (term34 A x y).
Proof. exact (eq_refl (term34 A x y)). Qed.
Lemma lem4795233 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term35 A s x y) = (term36 A s x y).
Proof. exact (MK_COMB (@lem4795229 A s y) (@lem4795232 A x y)). Qed.
Lemma lem4795236 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term37 A s x y) = (term38 A s x y).
Proof. exact (MK_COMB (@lem4795221 A s x) (@lem4795233 A s x y)). Qed.
Lemma lem4795239 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4795240 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term39 A s x y) = (term40 A s x y).
Proof. exact (MK_COMB (@lem4795239) (@lem4795236 A s x y)). Qed.
Lemma lem4795241 {A : Type'} (P : type1402 A) (x : A) (y : A) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem4795242 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term41 A s P x y) = (term42 A s P x y).
Proof. exact (MK_COMB (@lem4795240 A s x y) (@lem4795241 A P x y)). Qed.
Lemma lem4795245 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) : (term43 A s P x) = (term44 A s P x).
Proof. exact (fun_ext (fun y : A => @lem4795242 A s P x y)). Qed.
Lemma lem4795246 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795247 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) : (term45 A s P x) = (term46 A s P x).
Proof. exact (MK_COMB (@lem4795246 A) (@lem4795245 A s P x)). Qed.
Lemma lem4795252 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term47 A s P) = (term48 A s P).
Proof. exact (fun_ext (fun x : A => @lem4795247 A s P x)). Qed.
Lemma lem4795253 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795254 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term10 A s P) = (term49 A s P).
Proof. exact (MK_COMB (@lem4795253 A) (@lem4795252 A s P)). Qed.
Lemma lem4795259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4795260 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term12 A s P) = (term50 A s P).
Proof. exact (MK_COMB (@lem4795259) (@lem4795254 A s P)). Qed.
Lemma lem4795274 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4795275 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4795274 A P x). Qed.
Lemma lem4795276 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4795275 A s x). Qed.
Lemma lem4795277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4795278 {A : Type'} (s : A -> Prop) (x : A) : (term32 A x s) = (term33 A s x).
Proof. exact (MK_COMB (@lem4795277) (@lem4795276 A s x)). Qed.
Lemma lem4795282 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4795283 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4795282 A P x). Qed.
Lemma lem4795284 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem4795283 A s y). Qed.
Lemma lem4795285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4795286 {A : Type'} (s : A -> Prop) (y : A) : (term32 A y s) = (term33 A s y).
Proof. exact (MK_COMB (@lem4795285) (@lem4795284 A s y)). Qed.
Lemma lem4795291 {A : Type'} (P : type1402 A) (x : A) (y : A) : (term51 A P x y) = (term51 A P x y).
Proof. exact (eq_refl (term51 A P x y)). Qed.
Lemma lem4795292 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term52 A s P x y) = (term53 A s P x y).
Proof. exact (MK_COMB (@lem4795286 A s y) (@lem4795291 A P x y)). Qed.
Lemma lem4795295 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term54 A s P x y) = (term55 A s P x y).
Proof. exact (MK_COMB (@lem4795278 A s x) (@lem4795292 A s P x y)). Qed.
Lemma lem4795298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4795299 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term56 A s P x y) = (term57 A s P x y).
Proof. exact (MK_COMB (@lem4795298) (@lem4795295 A s P x y)). Qed.
Lemma lem4795300 {A : Type'} (Q : type1402 A) (x : A) (y : A) : (Q x y) = (Q x y).
Proof. exact (eq_refl (Q x y)). Qed.
Lemma lem4795301 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) (y : A) : (term58 A s P Q x y) = (term59 A s P Q x y).
Proof. exact (MK_COMB (@lem4795299 A s P x y) (@lem4795300 A Q x y)). Qed.
Lemma lem4795304 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) : (term60 A s P Q x) = (term61 A s P Q x).
Proof. exact (fun_ext (fun y : A => @lem4795301 A s P Q x y)). Qed.
Lemma lem4795305 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795306 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) : (term62 A s P Q x) = (term63 A s P Q x).
Proof. exact (MK_COMB (@lem4795305 A) (@lem4795304 A s P Q x)). Qed.
Lemma lem4795311 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term64 A s P Q) = (term65 A s P Q).
Proof. exact (fun_ext (fun x : A => @lem4795306 A s P Q x)). Qed.
Lemma lem4795312 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795313 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term13 A s P Q) = (term66 A s P Q).
Proof. exact (MK_COMB (@lem4795312 A) (@lem4795311 A s P Q)). Qed.
Lemma lem4795318 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term15 A s P Q) = (term67 A s P Q).
Proof. exact (MK_COMB (@lem4795260 A s P) (@lem4795313 A s P Q)). Qed.
Lemma lem4795321 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4795322 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term17 A s P Q) = (term68 A s P Q).
Proof. exact (MK_COMB (@lem4795321) (@lem4795318 A s P Q)). Qed.
Lemma lem4795336 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4795337 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4795336 A P x). Qed.
Lemma lem4795338 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4795337 A s x). Qed.
Lemma lem4795339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4795340 {A : Type'} (s : A -> Prop) (x : A) : (term32 A x s) = (term33 A s x).
Proof. exact (MK_COMB (@lem4795339) (@lem4795338 A s x)). Qed.
Lemma lem4795344 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4795345 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4795344 A P x). Qed.
Lemma lem4795346 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem4795345 A s y). Qed.
Lemma lem4795347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4795348 {A : Type'} (s : A -> Prop) (y : A) : (term32 A y s) = (term33 A s y).
Proof. exact (MK_COMB (@lem4795347) (@lem4795346 A s y)). Qed.
Lemma lem4795351 {A : Type'} (x : A) (y : A) : (term34 A x y) = (term34 A x y).
Proof. exact (eq_refl (term34 A x y)). Qed.
Lemma lem4795352 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term35 A s x y) = (term36 A s x y).
Proof. exact (MK_COMB (@lem4795348 A s y) (@lem4795351 A x y)). Qed.
Lemma lem4795355 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term37 A s x y) = (term38 A s x y).
Proof. exact (MK_COMB (@lem4795340 A s x) (@lem4795352 A s x y)). Qed.
Lemma lem4795358 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4795359 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term39 A s x y) = (term40 A s x y).
Proof. exact (MK_COMB (@lem4795358) (@lem4795355 A s x y)). Qed.
Lemma lem4795360 {A : Type'} (Q : type1402 A) (x : A) (y : A) : (Q x y) = (Q x y).
Proof. exact (eq_refl (Q x y)). Qed.
Lemma lem4795361 {A : Type'} (s : A -> Prop) (Q : type1402 A) (x : A) (y : A) : (term41 A s Q x y) = (term42 A s Q x y).
Proof. exact (MK_COMB (@lem4795359 A s x y) (@lem4795360 A Q x y)). Qed.
Lemma lem4795364 {A : Type'} (s : A -> Prop) (Q : type1402 A) (x : A) : (term43 A s Q x) = (term44 A s Q x).
Proof. exact (fun_ext (fun y : A => @lem4795361 A s Q x y)). Qed.
Lemma lem4795365 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795366 {A : Type'} (s : A -> Prop) (Q : type1402 A) (x : A) : (term45 A s Q x) = (term46 A s Q x).
Proof. exact (MK_COMB (@lem4795365 A) (@lem4795364 A s Q x)). Qed.
Lemma lem4795371 {A : Type'} (s : A -> Prop) (Q : type1402 A) : (term47 A s Q) = (term48 A s Q).
Proof. exact (fun_ext (fun x : A => @lem4795366 A s Q x)). Qed.
Lemma lem4795372 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795373 {A : Type'} (s : A -> Prop) (Q : type1402 A) : (term10 A s Q) = (term49 A s Q).
Proof. exact (MK_COMB (@lem4795372 A) (@lem4795371 A s Q)). Qed.
Lemma lem4795378 {A : Type'} (P : type1402 A) (s : A -> Prop) (Q : type1402 A) : (term19 A P s Q) = (term69 A P s Q).
Proof. exact (MK_COMB (@lem4795322 A s P Q) (@lem4795373 A s Q)). Qed.
Lemma lem4795381 {A : Type'} (P : type1402 A) (Q : type1402 A) : (term21 A P Q) = (term70 A P Q).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4795378 A P s Q)). Qed.
Lemma lem4795382 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4795383 {A : Type'} (P : type1402 A) (Q : type1402 A) : (term23 A P Q) = (term71 A P Q).
Proof. exact (MK_COMB (@lem4795382 A) (@lem4795381 A P Q)). Qed.
Lemma lem4795388 {A : Type'} (P : type1402 A) : (term25 A P) = (term72 A P).
Proof. exact (fun_ext (fun Q : type1402 A => @lem4795383 A P Q)). Qed.
Lemma lem4795389 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4795390 {A : Type'} (P : type1402 A) : (term27 A P) = (term73 A P).
Proof. exact (MK_COMB (@lem4795389 A) (@lem4795388 A P)). Qed.
Lemma lem4795395 {A : Type'} : (term29 A) = (term74 A).
Proof. exact (fun_ext (fun P : type1402 A => @lem4795390 A P)). Qed.
Lemma lem4795396 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4795397 {A : Type'} : (term31 A) = (term75 A).
Proof. exact (MK_COMB (@lem4795396 A) (@lem4795395 A)). Qed.
Lemma lem4795402 {A : Type'} : (term75 A) = (term31 A).
Proof. exact (SYM (@lem4795397 A)). Qed.
Lemma lem4795404 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4795405 {A : Type'} : (term75 A) = (term77 A).
Proof. exact (@lem4795404 (term75 A)). Qed.
Lemma lem4795406 {A : Type'} : (term77 A) = (term75 A).
Proof. exact (SYM (@lem4795405 A)). Qed.
Lemma lem4795407 {A : Type'} (h1 : term78 A) : term78 A.
Proof. exact (h1). Qed.
Lemma lem4795410 {A : Type'} (h1 : term77 A) : term77 A.
Proof. exact (h1). Qed.
Lemma lem4795411 {A : Type'} : term79 A.
Proof. exact (fun h0 : term77 A => @lem4795410 A h0). Qed.
Lemma lem4795412 {A : Type'} (h1 : term79 A) : term79 A.
Proof. exact (h1). Qed.
Lemma lem4795413 {A : Type'} (h1 : term77 A) : term77 A.
Proof. exact (h1). Qed.
Lemma lem4795414 {A : Type'} (h1 : term77 A) (h2 : term79 A) : term77 A.
Proof. exact (@lem4795412 A h2 (@lem4795413 A h1)). Qed.
Lemma lem4795415 {A : Type'} (h1 : term77 A) : term80 A.
Proof. exact (fun h0 : term79 A => @lem4795414 A h1 h0). Qed.
Lemma lem4795416 {A : Type'} (h1 : term79 A) : term79 A.
Proof. exact (h1). Qed.
Lemma lem4795417 {A : Type'} (h1 : term77 A) (h2 : term79 A) : term77 A.
Proof. exact (@lem4795415 A h1 (@lem4795416 A h2)). Qed.
Lemma lem4795418 {A : Type'} (h1 : term79 A) : term79 A.
Proof. exact (fun h0 : term77 A => @lem4795417 A h0 h1). Qed.
Lemma lem4795419 {A : Type'} : term81 A.
Proof. exact (fun h0 : term79 A => @lem4795418 A h0). Qed.
Lemma lem4795422 {A : Type'} : term79 A.
Proof. exact (@lem4795419 A (@lem4795411 A)). Qed.
Lemma lem4795423 {A : Type'} : term79 A.
Proof. exact (@lem4795422 A). Qed.
Lemma lem4795425 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4795426 {A : Type'} : (term77 A) = (term82 A).
Proof. exact (@lem4795425 (term78 A)). Qed.
Lemma lem4795428 (t : Prop) : (term83 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4795429 {A : Type'} : (term82 A) = (term75 A).
Proof. exact (@lem4795428 (term75 A)). Qed.
Lemma lem4795494 {A : Type'} : (term77 A) = (term75 A).
Proof. exact (TRANS (@lem4795426 A) (@lem4795429 A)). Qed.
Lemma lem4795509 {A : Type'} (s : A -> Prop) (Q : type1402 A) (x : A) (y : A) : (term42 A s Q x y) = (term42 A s Q x y).
Proof. exact (eq_refl (term42 A s Q x y)). Qed.
Lemma lem4795510 {A : Type'} (s : A -> Prop) (Q : type1402 A) (x : A) : (term44 A s Q x) = (term44 A s Q x).
Proof. exact (fun_ext (fun y : A => @lem4795509 A s Q x y)). Qed.
Lemma lem4795511 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795512 {A : Type'} (s : A -> Prop) (Q : type1402 A) (x : A) : (term46 A s Q x) = (term46 A s Q x).
Proof. exact (MK_COMB (@lem4795511 A) (@lem4795510 A s Q x)). Qed.
Lemma lem4795513 {A : Type'} (s : A -> Prop) (Q : type1402 A) : (term48 A s Q) = (term48 A s Q).
Proof. exact (fun_ext (fun x : A => @lem4795512 A s Q x)). Qed.
Lemma lem4795514 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795515 {A : Type'} (s : A -> Prop) (Q : type1402 A) : (term49 A s Q) = (term49 A s Q).
Proof. exact (MK_COMB (@lem4795514 A) (@lem4795513 A s Q)). Qed.
Lemma lem4795534 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) (y : A) : (term59 A s P Q x y) = (term59 A s P Q x y).
Proof. exact (eq_refl (term59 A s P Q x y)). Qed.
Lemma lem4795535 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) : (term61 A s P Q x) = (term61 A s P Q x).
Proof. exact (fun_ext (fun y : A => @lem4795534 A s P Q x y)). Qed.
Lemma lem4795536 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795537 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) : (term63 A s P Q x) = (term63 A s P Q x).
Proof. exact (MK_COMB (@lem4795536 A) (@lem4795535 A s P Q x)). Qed.
Lemma lem4795538 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term65 A s P Q) = (term65 A s P Q).
Proof. exact (fun_ext (fun x : A => @lem4795537 A s P Q x)). Qed.
Lemma lem4795539 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795540 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term66 A s P Q) = (term66 A s P Q).
Proof. exact (MK_COMB (@lem4795539 A) (@lem4795538 A s P Q)). Qed.
Lemma lem4795555 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term42 A s P x y) = (term42 A s P x y).
Proof. exact (eq_refl (term42 A s P x y)). Qed.
Lemma lem4795556 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) : (term44 A s P x) = (term44 A s P x).
Proof. exact (fun_ext (fun y : A => @lem4795555 A s P x y)). Qed.
Lemma lem4795557 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795558 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) : (term46 A s P x) = (term46 A s P x).
Proof. exact (MK_COMB (@lem4795557 A) (@lem4795556 A s P x)). Qed.
Lemma lem4795559 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term48 A s P) = (term48 A s P).
Proof. exact (fun_ext (fun x : A => @lem4795558 A s P x)). Qed.
Lemma lem4795560 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795561 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term49 A s P) = (term49 A s P).
Proof. exact (MK_COMB (@lem4795560 A) (@lem4795559 A s P)). Qed.
Lemma lem4795562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4795563 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term50 A s P) = (term50 A s P).
Proof. exact (MK_COMB (@lem4795562) (@lem4795561 A s P)). Qed.
Lemma lem4795564 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term67 A s P Q) = (term67 A s P Q).
Proof. exact (MK_COMB (@lem4795563 A s P) (@lem4795540 A s P Q)). Qed.
Lemma lem4795565 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4795566 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term68 A s P Q) = (term68 A s P Q).
Proof. exact (MK_COMB (@lem4795565) (@lem4795564 A s P Q)). Qed.
Lemma lem4795567 {A : Type'} (P : type1402 A) (s : A -> Prop) (Q : type1402 A) : (term69 A P s Q) = (term69 A P s Q).
Proof. exact (MK_COMB (@lem4795566 A s P Q) (@lem4795515 A s Q)). Qed.
Lemma lem4795568 {A : Type'} (P : type1402 A) (Q : type1402 A) : (term70 A P Q) = (term70 A P Q).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4795567 A P s Q)). Qed.
Lemma lem4795569 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4795570 {A : Type'} (P : type1402 A) (Q : type1402 A) : (term71 A P Q) = (term71 A P Q).
Proof. exact (MK_COMB (@lem4795569 A) (@lem4795568 A P Q)). Qed.
Lemma lem4795571 {A : Type'} (P : type1402 A) : (term72 A P) = (term72 A P).
Proof. exact (fun_ext (fun Q : type1402 A => @lem4795570 A P Q)). Qed.
Lemma lem4795572 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4795573 {A : Type'} (P : type1402 A) : (term73 A P) = (term73 A P).
Proof. exact (MK_COMB (@lem4795572 A) (@lem4795571 A P)). Qed.
Lemma lem4795574 {A : Type'} : (term74 A) = (term74 A).
Proof. exact (fun_ext (fun P : type1402 A => @lem4795573 A P)). Qed.
Lemma lem4795575 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4795576 {A : Type'} : (term75 A) = (term75 A).
Proof. exact (MK_COMB (@lem4795575 A) (@lem4795574 A)). Qed.
Lemma lem4795657 {A : Type'} : (term77 A) = (term75 A).
Proof. exact (TRANS (@lem4795494 A) (@lem4795576 A)). Qed.
Lemma lem4795658 {A : Type'} : (term75 A) = (term77 A).
Proof. exact (SYM (@lem4795657 A)). Qed.
Lemma lem4795659 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term67 A s P Q.
Proof. exact (h1). Qed.
Lemma lem4795662 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4795663 {A : Type'} (Q : type1402 A) (x : A) (y : A) : (Q x y) = (term84 A Q x y).
Proof. exact (@lem4795662 (Q x y)). Qed.
Lemma lem4795664 {A : Type'} (Q : type1402 A) (x : A) (y : A) : (term84 A Q x y) = (Q x y).
Proof. exact (SYM (@lem4795663 A Q x y)). Qed.
Lemma lem4795665 {A : Type'} (Q : type1402 A) (x : A) (y : A) (h1 : term85 A Q x y) : term85 A Q x y.
Proof. exact (h1). Qed.
Lemma lem4795670 {A : Type'} (x : A) (y : A) : (term86 A x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4795672 {A : Type'} (s : A -> Prop) (y : A) : (term87 A s y) = (term87 A s y).
Proof. exact (eq_refl (term87 A s y)). Qed.
Lemma lem4795673 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term88 A s x y) = (term89 A s x y).
Proof. exact (MK_COMB (@lem4795672 A s y) (@lem4795670 A x y)). Qed.
Lemma lem4795674 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term90 A s x y) = (term88 A s x y).
Proof. exact (@lem17045 (s y) (term34 A x y)). Qed.
Lemma lem4795675 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term90 A s x y) = (term89 A s x y).
Proof. exact (TRANS (@lem4795674 A s x y) (@lem4795673 A s x y)). Qed.
Lemma lem4795677 {A : Type'} (s : A -> Prop) (x : A) : (term87 A s x) = (term87 A s x).
Proof. exact (eq_refl (term87 A s x)). Qed.
Lemma lem4795678 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term91 A s x y) = (term92 A s x y).
Proof. exact (MK_COMB (@lem4795677 A s x) (@lem4795675 A s x y)). Qed.
Lemma lem4795679 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term93 A s x y) = (term91 A s x y).
Proof. exact (@lem17045 (s x) (term36 A s x y)). Qed.
Lemma lem4795680 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term93 A s x y) = (term92 A s x y).
Proof. exact (TRANS (@lem4795679 A s x y) (@lem4795678 A s x y)). Qed.
Lemma lem4795681 {A : Type'} (P : type1402 A) (x : A) (y : A) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem4795682 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4795683 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term94 A s x y) = (term95 A s x y).
Proof. exact (MK_COMB (@lem4795682) (@lem4795680 A s x y)). Qed.
Lemma lem4795684 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term96 A s P x y) = (term97 A s P x y).
Proof. exact (MK_COMB (@lem4795683 A s x y) (@lem4795681 A P x y)). Qed.
Lemma lem4795685 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term42 A s P x y) = (term96 A s P x y).
Proof. exact (@lem17265 (term38 A s x y) (P x y)). Qed.
Lemma lem4795686 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term42 A s P x y) = (term97 A s P x y).
Proof. exact (TRANS (@lem4795685 A s P x y) (@lem4795684 A s P x y)). Qed.
Lemma lem4795687 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) : (term44 A s P x) = (term98 A s P x).
Proof. exact (fun_ext (fun y : A => @lem4795686 A s P x y)). Qed.
Lemma lem4795688 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795689 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) : (term46 A s P x) = (term99 A s P x).
Proof. exact (MK_COMB (@lem4795688 A) (@lem4795687 A s P x)). Qed.
Lemma lem4795690 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term48 A s P) = (term100 A s P).
Proof. exact (fun_ext (fun x : A => @lem4795689 A s P x)). Qed.
Lemma lem4795691 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795692 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term49 A s P) = (term101 A s P).
Proof. exact (MK_COMB (@lem4795691 A) (@lem4795690 A s P)). Qed.
Lemma lem4795698 {A : Type'} (x : A) (y : A) : (term86 A x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4795700 {A : Type'} (P : type1402 A) (x : A) (y : A) : (term102 A P x y) = (term102 A P x y).
Proof. exact (eq_refl (term102 A P x y)). Qed.
Lemma lem4795701 {A : Type'} (P : type1402 A) (x : A) (y : A) : (term103 A P x y) = (term104 A P x y).
Proof. exact (MK_COMB (@lem4795700 A P x y) (@lem4795698 A x y)). Qed.
Lemma lem4795702 {A : Type'} (P : type1402 A) (x : A) (y : A) : (term105 A P x y) = (term103 A P x y).
Proof. exact (@lem17045 (P x y) (term34 A x y)). Qed.
Lemma lem4795703 {A : Type'} (P : type1402 A) (x : A) (y : A) : (term105 A P x y) = (term104 A P x y).
Proof. exact (TRANS (@lem4795702 A P x y) (@lem4795701 A P x y)). Qed.
Lemma lem4795705 {A : Type'} (s : A -> Prop) (y : A) : (term87 A s y) = (term87 A s y).
Proof. exact (eq_refl (term87 A s y)). Qed.
Lemma lem4795706 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term106 A s P x y) = (term107 A s P x y).
Proof. exact (MK_COMB (@lem4795705 A s y) (@lem4795703 A P x y)). Qed.
Lemma lem4795707 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term108 A s P x y) = (term106 A s P x y).
Proof. exact (@lem17045 (s y) (term51 A P x y)). Qed.
Lemma lem4795708 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term108 A s P x y) = (term107 A s P x y).
Proof. exact (TRANS (@lem4795707 A s P x y) (@lem4795706 A s P x y)). Qed.
Lemma lem4795710 {A : Type'} (s : A -> Prop) (x : A) : (term87 A s x) = (term87 A s x).
Proof. exact (eq_refl (term87 A s x)). Qed.
Lemma lem4795711 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term109 A s P x y) = (term110 A s P x y).
Proof. exact (MK_COMB (@lem4795710 A s x) (@lem4795708 A s P x y)). Qed.
Lemma lem4795712 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term111 A s P x y) = (term109 A s P x y).
Proof. exact (@lem17045 (s x) (term53 A s P x y)). Qed.
Lemma lem4795713 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term111 A s P x y) = (term110 A s P x y).
Proof. exact (TRANS (@lem4795712 A s P x y) (@lem4795711 A s P x y)). Qed.
Lemma lem4795714 {A : Type'} (Q : type1402 A) (x : A) (y : A) : (Q x y) = (Q x y).
Proof. exact (eq_refl (Q x y)). Qed.
Lemma lem4795715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4795716 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term112 A s P x y) = (term113 A s P x y).
Proof. exact (MK_COMB (@lem4795715) (@lem4795713 A s P x y)). Qed.
Lemma lem4795717 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) (y : A) : (term114 A s P Q x y) = (term115 A s P Q x y).
Proof. exact (MK_COMB (@lem4795716 A s P x y) (@lem4795714 A Q x y)). Qed.
Lemma lem4795718 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) (y : A) : (term59 A s P Q x y) = (term114 A s P Q x y).
Proof. exact (@lem17265 (term55 A s P x y) (Q x y)). Qed.
Lemma lem4795719 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) (y : A) : (term59 A s P Q x y) = (term115 A s P Q x y).
Proof. exact (TRANS (@lem4795718 A s P Q x y) (@lem4795717 A s P Q x y)). Qed.
Lemma lem4795720 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) : (term61 A s P Q x) = (term116 A s P Q x).
Proof. exact (fun_ext (fun y : A => @lem4795719 A s P Q x y)). Qed.
Lemma lem4795721 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795722 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) : (term63 A s P Q x) = (term117 A s P Q x).
Proof. exact (MK_COMB (@lem4795721 A) (@lem4795720 A s P Q x)). Qed.
Lemma lem4795723 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term65 A s P Q) = (term118 A s P Q).
Proof. exact (fun_ext (fun x : A => @lem4795722 A s P Q x)). Qed.
Lemma lem4795724 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795725 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term66 A s P Q) = (term119 A s P Q).
Proof. exact (MK_COMB (@lem4795724 A) (@lem4795723 A s P Q)). Qed.
Lemma lem4795726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4795727 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term50 A s P) = (term120 A s P).
Proof. exact (MK_COMB (@lem4795726) (@lem4795692 A s P)). Qed.
Lemma lem4795836 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term67 A s P Q) = (term121 A s P Q).
Proof. exact (MK_COMB (@lem4795727 A s P) (@lem4795725 A s P Q)). Qed.
Lemma lem4795837 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term121 A s P Q.
Proof. exact (EQ_MP (@lem4795836 A s P Q) (@lem4795659 A s P Q h1)). Qed.
Lemma lem4795851 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : term38 A s x y.
Proof. exact (h1). Qed.
Lemma lem4795857 {A : Type'} (Q : type1402 A) (x : A) (y : A) (h1 : term85 A Q x y) : term85 A Q x y.
Proof. exact (h1). Qed.
Lemma lem4795896 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) (y : A) : (term115 A s P Q x y) = (term115 A s P Q x y).
Proof. exact (eq_refl (term115 A s P Q x y)). Qed.
Lemma lem4795897 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) : (term116 A s P Q x) = (term116 A s P Q x).
Proof. exact (fun_ext (fun y : A => @lem4795896 A s P Q x y)). Qed.
Lemma lem4795898 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795899 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) : (term117 A s P Q x) = (term117 A s P Q x).
Proof. exact (MK_COMB (@lem4795898 A) (@lem4795897 A s P Q x)). Qed.
Lemma lem4795900 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term118 A s P Q) = (term118 A s P Q).
Proof. exact (fun_ext (fun x : A => @lem4795899 A s P Q x)). Qed.
Lemma lem4795901 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795902 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term119 A s P Q) = (term119 A s P Q).
Proof. exact (MK_COMB (@lem4795901 A) (@lem4795900 A s P Q)). Qed.
Lemma lem4795931 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term97 A s P x y) = (term97 A s P x y).
Proof. exact (eq_refl (term97 A s P x y)). Qed.
Lemma lem4795932 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) : (term98 A s P x) = (term98 A s P x).
Proof. exact (fun_ext (fun y : A => @lem4795931 A s P x y)). Qed.
Lemma lem4795933 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795934 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) : (term99 A s P x) = (term99 A s P x).
Proof. exact (MK_COMB (@lem4795933 A) (@lem4795932 A s P x)). Qed.
Lemma lem4795935 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term100 A s P) = (term100 A s P).
Proof. exact (fun_ext (fun x : A => @lem4795934 A s P x)). Qed.
Lemma lem4795936 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4795937 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term101 A s P) = (term101 A s P).
Proof. exact (MK_COMB (@lem4795936 A) (@lem4795935 A s P)). Qed.
Lemma lem4795938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4795939 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term120 A s P) = (term120 A s P).
Proof. exact (MK_COMB (@lem4795938) (@lem4795937 A s P)). Qed.
Lemma lem4795940 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term121 A s P Q) = (term121 A s P Q).
Proof. exact (MK_COMB (@lem4795939 A s P) (@lem4795902 A s P Q)). Qed.
Lemma lem4795941 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term121 A s P Q.
Proof. exact (EQ_MP (@lem4795940 A s P Q) (@lem4795837 A s P Q h1)). Qed.
Lemma lem4795961 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : term38 A s x y.
Proof. exact (h1). Qed.
Lemma lem4795969 {A : Type'} (Q : type1402 A) (x : A) (y : A) (h1 : term85 A Q x y) : term85 A Q x y.
Proof. exact (h1). Qed.
Lemma lem4795970 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : term36 A s x y.
Proof. exact (proj2 (@lem4795961 A s x y h1)). Qed.
Lemma lem4795974 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term119 A s P Q.
Proof. exact (proj2 (@lem4795941 A s P Q h1)). Qed.
Lemma lem4795975 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term101 A s P.
Proof. exact (proj1 (@lem4795941 A s P Q h1)). Qed.
Lemma lem4795979 {A : Type'} (Q : type1402 A) (x : A) (y : A) (h1 : term85 A Q x y) : term85 A Q x y.
Proof. exact (h1). Qed.
Lemma lem4796011 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) (y : A) : (term97 A s P x y) = (term97 A s P x y).
Proof. exact (eq_refl (term97 A s P x y)). Qed.
Lemma lem4796012 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) : (term98 A s P x) = (term98 A s P x).
Proof. exact (fun_ext (fun y : A => @lem4796011 A s P x y)). Qed.
Lemma lem4796013 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4796014 {A : Type'} (s : A -> Prop) (P : type1402 A) (x : A) : (term99 A s P x) = (term99 A s P x).
Proof. exact (MK_COMB (@lem4796013 A) (@lem4796012 A s P x)). Qed.
Lemma lem4796015 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term100 A s P) = (term100 A s P).
Proof. exact (fun_ext (fun x : A => @lem4796014 A s P x)). Qed.
Lemma lem4796016 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4796018 {A : Type'} (s : A -> Prop) (P : type1402 A) : (term101 A s P) = (term101 A s P).
Proof. exact (MK_COMB (@lem4796016 A) (@lem4796015 A s P)). Qed.
Lemma lem4796019 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term101 A s P.
Proof. exact (EQ_MP (@lem4796018 A s P) (@lem4795975 A s P Q h1)). Qed.
Lemma lem4796045 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) (y : A) : (term115 A s P Q x y) = (term115 A s P Q x y).
Proof. exact (eq_refl (term115 A s P Q x y)). Qed.
Lemma lem4796046 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) : (term116 A s P Q x) = (term116 A s P Q x).
Proof. exact (fun_ext (fun y : A => @lem4796045 A s P Q x y)). Qed.
Lemma lem4796047 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4796048 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (x : A) : (term117 A s P Q x) = (term117 A s P Q x).
Proof. exact (MK_COMB (@lem4796047 A) (@lem4796046 A s P Q x)). Qed.
Lemma lem4796049 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term118 A s P Q) = (term118 A s P Q).
Proof. exact (fun_ext (fun x : A => @lem4796048 A s P Q x)). Qed.
Lemma lem4796050 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4796052 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) : (term119 A s P Q) = (term119 A s P Q).
Proof. exact (MK_COMB (@lem4796050 A) (@lem4796049 A s P Q)). Qed.
Lemma lem4796053 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term119 A s P Q.
Proof. exact (EQ_MP (@lem4796052 A s P Q) (@lem4795974 A s P Q h1)). Qed.
Lemma lem4796054 {A : Type'} (_59349 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term122 A s P _59349.
Proof. exact (@lem4796019 A s P Q h1 _59349). Qed.
Lemma lem4796055 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) : (term122 A s P _59349) = (term99 A s P _59349).
Proof. exact (eq_refl (term122 A s P _59349)). Qed.
Lemma lem4796056 {A : Type'} (_59349 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term99 A s P _59349.
Proof. exact (EQ_MP (@lem4796055 A s P _59349) (@lem4796054 A _59349 s P Q h1)). Qed.
Lemma lem4796057 {A : Type'} (_59349 : A) (_59350 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term123 A s P _59349 _59350.
Proof. exact (@lem4796056 A _59349 s P Q h1 _59350). Qed.
Lemma lem4796058 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term123 A s P _59349 _59350) = (term97 A s P _59349 _59350).
Proof. exact (eq_refl (term123 A s P _59349 _59350)). Qed.
Lemma lem4796059 {A : Type'} (_59349 : A) (_59350 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term97 A s P _59349 _59350.
Proof. exact (EQ_MP (@lem4796058 A s P _59349 _59350) (@lem4796057 A _59349 _59350 s P Q h1)). Qed.
Lemma lem4796060 {A : Type'} (_59351 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term124 A s P Q _59351.
Proof. exact (@lem4796053 A s P Q h1 _59351). Qed.
Lemma lem4796061 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (_59351 : A) : (term124 A s P Q _59351) = (term117 A s P Q _59351).
Proof. exact (eq_refl (term124 A s P Q _59351)). Qed.
Lemma lem4796062 {A : Type'} (_59351 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term117 A s P Q _59351.
Proof. exact (EQ_MP (@lem4796061 A s P Q _59351) (@lem4796060 A _59351 s P Q h1)). Qed.
Lemma lem4796063 {A : Type'} (_59351 : A) (_59352 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term125 A s P Q _59351 _59352.
Proof. exact (@lem4796062 A _59351 s P Q h1 _59352). Qed.
Lemma lem4796064 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term125 A s P Q _59351 _59352) = (term115 A s P Q _59351 _59352).
Proof. exact (eq_refl (term125 A s P Q _59351 _59352)). Qed.
Lemma lem4796065 {A : Type'} (_59351 : A) (_59352 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term115 A s P Q _59351 _59352.
Proof. exact (EQ_MP (@lem4796064 A s P Q _59351 _59352) (@lem4796063 A _59351 _59352 s P Q h1)). Qed.
Lemma lem4796067 {A : Type'} (Q : type1402 A) (x : A) (y : A) (h1 : term85 A Q x y) : term85 A Q x y.
Proof. exact (h1). Qed.
Lemma lem4796073 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : term34 A x y.
Proof. exact (proj2 (@lem4795970 A s x y h1)). Qed.
Lemma lem4796077 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term97 A s P _59349 _59350) = (term126 A s P _59349 _59350).
Proof. exact (@lem4795000 (term127 A s _59349) (term89 A s _59349 _59350) (P _59349 _59350)). Qed.
Lemma lem4796084 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term128 A s P _59349 _59350) = (term129 A s P _59349 _59350).
Proof. exact (@lem4795000 (term127 A s _59350) (_59349 = _59350) (P _59349 _59350)). Qed.
Lemma lem4796085 {A : Type'} (s : A -> Prop) (_59349 : A) : (term87 A s _59349) = (term87 A s _59349).
Proof. exact (eq_refl (term87 A s _59349)). Qed.
Lemma lem4796088 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term126 A s P _59349 _59350) = (term130 A s P _59349 _59350).
Proof. exact (MK_COMB (@lem4796085 A s _59349) (@lem4796084 A s P _59349 _59350)). Qed.
Lemma lem4796090 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term97 A s P _59349 _59350) = (term130 A s P _59349 _59350).
Proof. exact (TRANS (@lem4796077 A s P _59349 _59350) (@lem4796088 A s P _59349 _59350)). Qed.
Lemma lem4796091 {A : Type'} (_59349 : A) (_59350 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term130 A s P _59349 _59350.
Proof. exact (EQ_MP (@lem4796090 A s P _59349 _59350) (@lem4796059 A _59349 _59350 s P Q h1)). Qed.
Lemma lem4796095 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term115 A s P Q _59351 _59352) = (term131 A s P Q _59351 _59352).
Proof. exact (@lem4795000 (term127 A s _59351) (term107 A s P _59351 _59352) (Q _59351 _59352)). Qed.
Lemma lem4796096 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term132 A s P Q _59351 _59352) = (term133 A s P Q _59351 _59352).
Proof. exact (@lem4795000 (term127 A s _59352) (term104 A P _59351 _59352) (Q _59351 _59352)). Qed.
Lemma lem4796103 {A : Type'} (P : type1402 A) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term134 A P Q _59351 _59352) = (term135 A P Q _59351 _59352).
Proof. exact (@lem4795000 (term85 A P _59351 _59352) (_59351 = _59352) (Q _59351 _59352)). Qed.
Lemma lem4796104 {A : Type'} (s : A -> Prop) (_59352 : A) : (term87 A s _59352) = (term87 A s _59352).
Proof. exact (eq_refl (term87 A s _59352)). Qed.
Lemma lem4796107 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term133 A s P Q _59351 _59352) = (term136 A s P Q _59351 _59352).
Proof. exact (MK_COMB (@lem4796104 A s _59352) (@lem4796103 A P Q _59351 _59352)). Qed.
Lemma lem4796108 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term132 A s P Q _59351 _59352) = (term136 A s P Q _59351 _59352).
Proof. exact (TRANS (@lem4796096 A s P Q _59351 _59352) (@lem4796107 A s P Q _59351 _59352)). Qed.
Lemma lem4796109 {A : Type'} (s : A -> Prop) (_59351 : A) : (term87 A s _59351) = (term87 A s _59351).
Proof. exact (eq_refl (term87 A s _59351)). Qed.
Lemma lem4796112 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term131 A s P Q _59351 _59352) = (term137 A s P Q _59351 _59352).
Proof. exact (MK_COMB (@lem4796109 A s _59351) (@lem4796108 A s P Q _59351 _59352)). Qed.
Lemma lem4796114 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term115 A s P Q _59351 _59352) = (term137 A s P Q _59351 _59352).
Proof. exact (TRANS (@lem4796095 A s P Q _59351 _59352) (@lem4796112 A s P Q _59351 _59352)). Qed.
Lemma lem4796115 {A : Type'} (_59351 : A) (_59352 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term137 A s P Q _59351 _59352.
Proof. exact (EQ_MP (@lem4796114 A s P Q _59351 _59352) (@lem4796065 A _59351 _59352 s P Q h1)). Qed.
Lemma lem4796169 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : s x.
Proof. exact (proj1 (@lem4795961 A s x y h1)). Qed.
Lemma lem4796170 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : term138 A s x.
Proof. exact (fun h0 : term127 A s x => @lem4796169 A s x y h1). Qed.
Lemma lem4796172 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4796173 {A : Type'} (s : A -> Prop) (x : A) : (term138 A s x) = (s x).
Proof. exact (@lem4796172 (s x)). Qed.
Lemma lem4796174 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : s x.
Proof. exact (EQ_MP (@lem4796173 A s x) (@lem4796170 A s x y h1)). Qed.
Lemma lem4796176 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : s y.
Proof. exact (proj1 (@lem4795970 A s x y h1)). Qed.
Lemma lem4796177 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : term138 A s y.
Proof. exact (fun h0 : term127 A s y => @lem4796176 A s x y h1). Qed.
Lemma lem4796179 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4796180 {A : Type'} (s : A -> Prop) (y : A) : (term138 A s y) = (s y).
Proof. exact (@lem4796179 (s y)). Qed.
Lemma lem4796181 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : s y.
Proof. exact (EQ_MP (@lem4796180 A s y) (@lem4796177 A s x y h1)). Qed.
Lemma lem4796183 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : s x.
Proof. exact (proj1 (@lem4795961 A s x y h1)). Qed.
Lemma lem4796184 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : term138 A s x.
Proof. exact (fun h0 : term127 A s x => @lem4796183 A s x y h1). Qed.
Lemma lem4796186 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4796187 {A : Type'} (s : A -> Prop) (x : A) : (term138 A s x) = (s x).
Proof. exact (@lem4796186 (s x)). Qed.
Lemma lem4796188 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : s x.
Proof. exact (EQ_MP (@lem4796187 A s x) (@lem4796184 A s x y h1)). Qed.
Lemma lem4796190 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : s y.
Proof. exact (proj1 (@lem4795970 A s x y h1)). Qed.
Lemma lem4796191 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : term138 A s y.
Proof. exact (fun h0 : term127 A s y => @lem4796190 A s x y h1). Qed.
Lemma lem4796193 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4796194 {A : Type'} (s : A -> Prop) (y : A) : (term138 A s y) = (s y).
Proof. exact (@lem4796193 (s y)). Qed.
Lemma lem4796195 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : s y.
Proof. exact (EQ_MP (@lem4796194 A s y) (@lem4796191 A s x y h1)). Qed.
Lemma lem4796198 {A : Type'} (x : A) (y : A) (h1 : term34 A x y) : term34 A x y.
Proof. exact (h1). Qed.
Lemma lem4796199 {A : Type'} (x : A) (y : A) (h1 : term34 A x y) : term140 A x y.
Proof. exact (fun h0 : x = y => @lem4796198 A x y h1). Qed.
Lemma lem4796201 (p : Prop) : (term141 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4796202 {A : Type'} (x : A) (y : A) : (term140 A x y) = (term34 A x y).
Proof. exact (@lem4796201 (x = y)). Qed.
Lemma lem4796203 {A : Type'} (x : A) (y : A) (h1 : term34 A x y) : term34 A x y.
Proof. exact (EQ_MP (@lem4796202 A x y) (@lem4796199 A x y h1)). Qed.
Lemma lem4796205 {A : Type'} (Q : type1402 A) (x : A) (y : A) (h1 : term85 A Q x y) : term85 A Q x y.
Proof. exact (h1). Qed.
Lemma lem4796206 {A : Type'} (Q : type1402 A) (x : A) (y : A) (h1 : term85 A Q x y) : term142 A Q x y.
Proof. exact (fun h0 : Q x y => @lem4796205 A Q x y h1). Qed.
Lemma lem4796208 (p : Prop) : (term141 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4796209 {A : Type'} (Q : type1402 A) (x : A) (y : A) : (term142 A Q x y) = (term85 A Q x y).
Proof. exact (@lem4796208 (Q x y)). Qed.
Lemma lem4796210 {A : Type'} (Q : type1402 A) (x : A) (y : A) (h1 : term85 A Q x y) : term85 A Q x y.
Proof. exact (EQ_MP (@lem4796209 A Q x y) (@lem4796206 A Q x y h1)). Qed.
Lemma lem4796226 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796227 {A : Type'} (P : type1402 A) (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term136 A s P Q _59351 _59352) = (term143 A P s Q _59351 _59352).
Proof. exact (@lem4796226 (term85 A P _59351 _59352) (term127 A s _59352) (term144 A Q _59351 _59352)). Qed.
Lemma lem4796241 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796242 {A : Type'} (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term129 A s Q _59351 _59352) = (term145 A s Q _59351 _59352).
Proof. exact (@lem4796241 (_59351 = _59352) (term127 A s _59352) (Q _59351 _59352)). Qed.
Lemma lem4796258 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4796259 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term146 A s Q _59351 _59352) = (term147 A Q _59351 s _59352).
Proof. exact (@lem4796258 (Q _59351 _59352) (term127 A s _59352)). Qed.
Lemma lem4796265 {A : Type'} (_59351 : A) (_59352 : A) : (term148 A _59351 _59352) = (term148 A _59351 _59352).
Proof. exact (eq_refl (term148 A _59351 _59352)). Qed.
Lemma lem4796266 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term145 A s Q _59351 _59352) = (term149 A Q _59351 s _59352).
Proof. exact (MK_COMB (@lem4796265 A _59351 _59352) (@lem4796259 A Q _59351 s _59352)). Qed.
Lemma lem4796270 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796271 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term149 A Q _59351 s _59352) = (term150 A Q _59351 s _59352).
Proof. exact (@lem4796270 (Q _59351 _59352) (_59351 = _59352) (term127 A s _59352)). Qed.
Lemma lem4796289 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term145 A s Q _59351 _59352) = (term150 A Q _59351 s _59352).
Proof. exact (TRANS (@lem4796266 A Q _59351 s _59352) (@lem4796271 A Q _59351 s _59352)). Qed.
Lemma lem4796290 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term129 A s Q _59351 _59352) = (term150 A Q _59351 s _59352).
Proof. exact (TRANS (@lem4796242 A s Q _59351 _59352) (@lem4796289 A Q _59351 s _59352)). Qed.
Lemma lem4796291 {A : Type'} (P : type1402 A) (_59351 : A) (_59352 : A) : (term102 A P _59351 _59352) = (term102 A P _59351 _59352).
Proof. exact (eq_refl (term102 A P _59351 _59352)). Qed.
Lemma lem4796292 {A : Type'} (P : type1402 A) (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term143 A P s Q _59351 _59352) = (term151 A P Q _59351 s _59352).
Proof. exact (MK_COMB (@lem4796291 A P _59351 _59352) (@lem4796290 A Q _59351 s _59352)). Qed.
Lemma lem4796296 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796297 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term151 A P Q _59351 s _59352) = (term152 A Q P _59351 s _59352).
Proof. exact (@lem4796296 (Q _59351 _59352) (term85 A P _59351 _59352) (term153 A _59351 s _59352)). Qed.
Lemma lem4796311 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796312 {A : Type'} (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term154 A P _59351 s _59352) = (term155 A P _59351 s _59352).
Proof. exact (@lem4796311 (_59351 = _59352) (term85 A P _59351 _59352) (term127 A s _59352)). Qed.
Lemma lem4796330 {A : Type'} (Q : type1402 A) (_59351 : A) (_59352 : A) : (term156 A Q _59351 _59352) = (term156 A Q _59351 _59352).
Proof. exact (eq_refl (term156 A Q _59351 _59352)). Qed.
Lemma lem4796331 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term152 A Q P _59351 s _59352) = (term157 A Q P _59351 s _59352).
Proof. exact (MK_COMB (@lem4796330 A Q _59351 _59352) (@lem4796312 A P _59351 s _59352)). Qed.
Lemma lem4796342 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term151 A P Q _59351 s _59352) = (term157 A Q P _59351 s _59352).
Proof. exact (TRANS (@lem4796297 A Q P _59351 s _59352) (@lem4796331 A Q P _59351 s _59352)). Qed.
Lemma lem4796343 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term143 A P s Q _59351 _59352) = (term157 A Q P _59351 s _59352).
Proof. exact (TRANS (@lem4796292 A P Q _59351 s _59352) (@lem4796342 A Q P _59351 s _59352)). Qed.
Lemma lem4796344 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term136 A s P Q _59351 _59352) = (term157 A Q P _59351 s _59352).
Proof. exact (TRANS (@lem4796227 A P s Q _59351 _59352) (@lem4796343 A Q P _59351 s _59352)). Qed.
Lemma lem4796345 {A : Type'} (s : A -> Prop) (_59351 : A) : (term87 A s _59351) = (term87 A s _59351).
Proof. exact (eq_refl (term87 A s _59351)). Qed.
Lemma lem4796346 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term137 A s P Q _59351 _59352) = (term158 A Q P _59351 s _59352).
Proof. exact (MK_COMB (@lem4796345 A s _59351) (@lem4796344 A Q P _59351 s _59352)). Qed.
Lemma lem4796350 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796351 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term158 A Q P _59351 s _59352) = (term159 A Q P _59351 s _59352).
Proof. exact (@lem4796350 (Q _59351 _59352) (term127 A s _59351) (term155 A P _59351 s _59352)). Qed.
Lemma lem4796365 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796366 {A : Type'} (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term160 A P _59351 s _59352) = (term161 A P _59351 s _59352).
Proof. exact (@lem4796365 (_59351 = _59352) (term127 A s _59351) (term162 A P _59351 s _59352)). Qed.
Lemma lem4796382 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796383 {A : Type'} (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term163 A P _59351 s _59352) = (term164 A P _59351 s _59352).
Proof. exact (@lem4796382 (term85 A P _59351 _59352) (term127 A s _59351) (term127 A s _59352)). Qed.
Lemma lem4796399 {A : Type'} (_59351 : A) (_59352 : A) : (term148 A _59351 _59352) = (term148 A _59351 _59352).
Proof. exact (eq_refl (term148 A _59351 _59352)). Qed.
Lemma lem4796400 {A : Type'} (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term161 A P _59351 s _59352) = (term165 A P _59351 s _59352).
Proof. exact (MK_COMB (@lem4796399 A _59351 _59352) (@lem4796383 A P _59351 s _59352)). Qed.
Lemma lem4796411 {A : Type'} (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term160 A P _59351 s _59352) = (term165 A P _59351 s _59352).
Proof. exact (TRANS (@lem4796366 A P _59351 s _59352) (@lem4796400 A P _59351 s _59352)). Qed.
Lemma lem4796412 {A : Type'} (Q : type1402 A) (_59351 : A) (_59352 : A) : (term156 A Q _59351 _59352) = (term156 A Q _59351 _59352).
Proof. exact (eq_refl (term156 A Q _59351 _59352)). Qed.
Lemma lem4796413 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term159 A Q P _59351 s _59352) = (term166 A Q P _59351 s _59352).
Proof. exact (MK_COMB (@lem4796412 A Q _59351 _59352) (@lem4796411 A P _59351 s _59352)). Qed.
Lemma lem4796424 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term158 A Q P _59351 s _59352) = (term166 A Q P _59351 s _59352).
Proof. exact (TRANS (@lem4796351 A Q P _59351 s _59352) (@lem4796413 A Q P _59351 s _59352)). Qed.
Lemma lem4796425 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term137 A s P Q _59351 _59352) = (term166 A Q P _59351 s _59352).
Proof. exact (TRANS (@lem4796346 A Q P _59351 s _59352) (@lem4796424 A Q P _59351 s _59352)). Qed.
Lemma lem4796426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4796427 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term167 A s P Q _59351 _59352) = (term168 A Q P _59351 s _59352).
Proof. exact (MK_COMB (@lem4796426) (@lem4796425 A Q P _59351 s _59352)). Qed.
Lemma lem4796451 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796452 {A : Type'} (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term129 A s Q _59351 _59352) = (term145 A s Q _59351 _59352).
Proof. exact (@lem4796451 (_59351 = _59352) (term127 A s _59352) (Q _59351 _59352)). Qed.
Lemma lem4796468 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4796469 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term146 A s Q _59351 _59352) = (term147 A Q _59351 s _59352).
Proof. exact (@lem4796468 (Q _59351 _59352) (term127 A s _59352)). Qed.
Lemma lem4796475 {A : Type'} (_59351 : A) (_59352 : A) : (term148 A _59351 _59352) = (term148 A _59351 _59352).
Proof. exact (eq_refl (term148 A _59351 _59352)). Qed.
Lemma lem4796476 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term145 A s Q _59351 _59352) = (term149 A Q _59351 s _59352).
Proof. exact (MK_COMB (@lem4796475 A _59351 _59352) (@lem4796469 A Q _59351 s _59352)). Qed.
Lemma lem4796480 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796481 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term149 A Q _59351 s _59352) = (term150 A Q _59351 s _59352).
Proof. exact (@lem4796480 (Q _59351 _59352) (_59351 = _59352) (term127 A s _59352)). Qed.
Lemma lem4796499 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term145 A s Q _59351 _59352) = (term150 A Q _59351 s _59352).
Proof. exact (TRANS (@lem4796476 A Q _59351 s _59352) (@lem4796481 A Q _59351 s _59352)). Qed.
Lemma lem4796500 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term129 A s Q _59351 _59352) = (term150 A Q _59351 s _59352).
Proof. exact (TRANS (@lem4796452 A s Q _59351 _59352) (@lem4796499 A Q _59351 s _59352)). Qed.
Lemma lem4796501 {A : Type'} (s : A -> Prop) (_59351 : A) : (term87 A s _59351) = (term87 A s _59351).
Proof. exact (eq_refl (term87 A s _59351)). Qed.
Lemma lem4796502 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term130 A s Q _59351 _59352) = (term169 A Q _59351 s _59352).
Proof. exact (MK_COMB (@lem4796501 A s _59351) (@lem4796500 A Q _59351 s _59352)). Qed.
Lemma lem4796506 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796507 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term169 A Q _59351 s _59352) = (term170 A Q _59351 s _59352).
Proof. exact (@lem4796506 (Q _59351 _59352) (term127 A s _59351) (term153 A _59351 s _59352)). Qed.
Lemma lem4796521 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796522 {A : Type'} (_59351 : A) (s : A -> Prop) (_59352 : A) : (term171 A _59351 s _59352) = (term172 A _59351 s _59352).
Proof. exact (@lem4796521 (_59351 = _59352) (term127 A s _59351) (term127 A s _59352)). Qed.
Lemma lem4796540 {A : Type'} (Q : type1402 A) (_59351 : A) (_59352 : A) : (term156 A Q _59351 _59352) = (term156 A Q _59351 _59352).
Proof. exact (eq_refl (term156 A Q _59351 _59352)). Qed.
Lemma lem4796541 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term170 A Q _59351 s _59352) = (term173 A Q _59351 s _59352).
Proof. exact (MK_COMB (@lem4796540 A Q _59351 _59352) (@lem4796522 A _59351 s _59352)). Qed.
Lemma lem4796552 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term169 A Q _59351 s _59352) = (term173 A Q _59351 s _59352).
Proof. exact (TRANS (@lem4796507 A Q _59351 s _59352) (@lem4796541 A Q _59351 s _59352)). Qed.
Lemma lem4796553 {A : Type'} (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term130 A s Q _59351 _59352) = (term173 A Q _59351 s _59352).
Proof. exact (TRANS (@lem4796502 A Q _59351 s _59352) (@lem4796552 A Q _59351 s _59352)). Qed.
Lemma lem4796554 {A : Type'} (P : type1402 A) (_59351 : A) (_59352 : A) : (term102 A P _59351 _59352) = (term102 A P _59351 _59352).
Proof. exact (eq_refl (term102 A P _59351 _59352)). Qed.
Lemma lem4796555 {A : Type'} (P : type1402 A) (Q : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term174 A P s Q _59351 _59352) = (term175 A P Q _59351 s _59352).
Proof. exact (MK_COMB (@lem4796554 A P _59351 _59352) (@lem4796553 A Q _59351 s _59352)). Qed.
Lemma lem4796559 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796560 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term175 A P Q _59351 s _59352) = (term176 A Q P _59351 s _59352).
Proof. exact (@lem4796559 (Q _59351 _59352) (term85 A P _59351 _59352) (term172 A _59351 s _59352)). Qed.
Lemma lem4796574 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796575 {A : Type'} (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term177 A P _59351 s _59352) = (term165 A P _59351 s _59352).
Proof. exact (@lem4796574 (_59351 = _59352) (term85 A P _59351 _59352) (term178 A _59351 s _59352)). Qed.
Lemma lem4796603 {A : Type'} (Q : type1402 A) (_59351 : A) (_59352 : A) : (term156 A Q _59351 _59352) = (term156 A Q _59351 _59352).
Proof. exact (eq_refl (term156 A Q _59351 _59352)). Qed.
Lemma lem4796604 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term176 A Q P _59351 s _59352) = (term166 A Q P _59351 s _59352).
Proof. exact (MK_COMB (@lem4796603 A Q _59351 _59352) (@lem4796575 A P _59351 s _59352)). Qed.
Lemma lem4796615 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term175 A P Q _59351 s _59352) = (term166 A Q P _59351 s _59352).
Proof. exact (TRANS (@lem4796560 A Q P _59351 s _59352) (@lem4796604 A Q P _59351 s _59352)). Qed.
Lemma lem4796616 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : (term174 A P s Q _59351 _59352) = (term166 A Q P _59351 s _59352).
Proof. exact (TRANS (@lem4796555 A P Q _59351 s _59352) (@lem4796615 A Q P _59351 s _59352)). Qed.
Lemma lem4796617 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : ((term137 A s P Q _59351 _59352) = (term174 A P s Q _59351 _59352)) = ((term166 A Q P _59351 s _59352) = (term166 A Q P _59351 s _59352)).
Proof. exact (MK_COMB (@lem4796427 A Q P _59351 s _59352) (@lem4796616 A Q P _59351 s _59352)). Qed.
Lemma lem4796619 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4796620 (x : Prop) : (x = x) = True.
Proof. exact (@lem4796619 Prop x). Qed.
Lemma lem4796621 {A : Type'} (Q : type1402 A) (P : type1402 A) (_59351 : A) (s : A -> Prop) (_59352 : A) : ((term166 A Q P _59351 s _59352) = (term166 A Q P _59351 s _59352)) = True.
Proof. exact (@lem4796620 (term166 A Q P _59351 s _59352)). Qed.
Lemma lem4796622 {A : Type'} (P : type1402 A) (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : ((term137 A s P Q _59351 _59352) = (term174 A P s Q _59351 _59352)) = True.
Proof. exact (TRANS (@lem4796617 A Q P _59351 s _59352) (@lem4796621 A Q P _59351 s _59352)). Qed.
Lemma lem4796623 {A : Type'} (P : type1402 A) (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : True = ((term137 A s P Q _59351 _59352) = (term174 A P s Q _59351 _59352)).
Proof. exact (SYM (@lem4796622 A P s Q _59351 _59352)). Qed.
Lemma lem4796624 {A : Type'} (P : type1402 A) (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term137 A s P Q _59351 _59352) = (term174 A P s Q _59351 _59352).
Proof. exact (EQ_MP (@lem4796623 A P s Q _59351 _59352) (@lem0)). Qed.
Lemma lem4796625 {A : Type'} (_59351 : A) (_59352 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term174 A P s Q _59351 _59352.
Proof. exact (EQ_MP (@lem4796624 A P s Q _59351 _59352) (@lem4796115 A _59351 _59352 s P Q h1)). Qed.
Lemma lem4796627 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4796628 {A : Type'} (s : A -> Prop) (Q : type1402 A) (P : type1402 A) (_59351 : A) (_59352 : A) : (term174 A P s Q _59351 _59352) = (term180 A s Q P _59351 _59352).
Proof. exact (@lem4796627 (term130 A s Q _59351 _59352) (term85 A P _59351 _59352)). Qed.
Lemma lem4796630 (a : Prop) (b : Prop) : (term181 a b) = (term182 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4796631 {A : Type'} (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term183 A s Q _59351 _59352) = (term184 A s Q _59351 _59352).
Proof. exact (@lem4796630 (term127 A s _59351) (term129 A s Q _59351 _59352)). Qed.
Lemma lem4796633 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4796634 {A : Type'} (s : A -> Prop) (_59351 : A) : (term185 A s _59351) = (s _59351).
Proof. exact (@lem4796633 (s _59351)). Qed.
Lemma lem4796635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4796636 {A : Type'} (s : A -> Prop) (_59351 : A) : (term186 A s _59351) = (term33 A s _59351).
Proof. exact (MK_COMB (@lem4796635) (@lem4796634 A s _59351)). Qed.
Lemma lem4796638 (a : Prop) (b : Prop) : (term181 a b) = (term182 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4796639 {A : Type'} (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term187 A s Q _59351 _59352) = (term188 A s Q _59351 _59352).
Proof. exact (@lem4796638 (term127 A s _59352) (term144 A Q _59351 _59352)). Qed.
Lemma lem4796641 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4796642 {A : Type'} (s : A -> Prop) (_59352 : A) : (term185 A s _59352) = (s _59352).
Proof. exact (@lem4796641 (s _59352)). Qed.
Lemma lem4796643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4796644 {A : Type'} (s : A -> Prop) (_59352 : A) : (term186 A s _59352) = (term33 A s _59352).
Proof. exact (MK_COMB (@lem4796643) (@lem4796642 A s _59352)). Qed.
Lemma lem4796646 (a : Prop) (b : Prop) : (term181 a b) = (term182 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4796647 {A : Type'} (Q : type1402 A) (_59351 : A) (_59352 : A) : (term189 A Q _59351 _59352) = (term190 A Q _59351 _59352).
Proof. exact (@lem4796646 (_59351 = _59352) (Q _59351 _59352)). Qed.
Lemma lem4796648 {A : Type'} (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term188 A s Q _59351 _59352) = (term191 A s Q _59351 _59352).
Proof. exact (MK_COMB (@lem4796644 A s _59352) (@lem4796647 A Q _59351 _59352)). Qed.
Lemma lem4796649 {A : Type'} (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term187 A s Q _59351 _59352) = (term191 A s Q _59351 _59352).
Proof. exact (TRANS (@lem4796639 A s Q _59351 _59352) (@lem4796648 A s Q _59351 _59352)). Qed.
Lemma lem4796650 {A : Type'} (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term184 A s Q _59351 _59352) = (term192 A s Q _59351 _59352).
Proof. exact (MK_COMB (@lem4796636 A s _59351) (@lem4796649 A s Q _59351 _59352)). Qed.
Lemma lem4796651 {A : Type'} (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term183 A s Q _59351 _59352) = (term192 A s Q _59351 _59352).
Proof. exact (TRANS (@lem4796631 A s Q _59351 _59352) (@lem4796650 A s Q _59351 _59352)). Qed.
Lemma lem4796652 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4796653 {A : Type'} (s : A -> Prop) (Q : type1402 A) (_59351 : A) (_59352 : A) : (term193 A s Q _59351 _59352) = (term194 A s Q _59351 _59352).
Proof. exact (MK_COMB (@lem4796652) (@lem4796651 A s Q _59351 _59352)). Qed.
Lemma lem4796654 {A : Type'} (P : type1402 A) (_59351 : A) (_59352 : A) : (term85 A P _59351 _59352) = (term85 A P _59351 _59352).
Proof. exact (eq_refl (term85 A P _59351 _59352)). Qed.
Lemma lem4796655 {A : Type'} (s : A -> Prop) (Q : type1402 A) (P : type1402 A) (_59351 : A) (_59352 : A) : (term180 A s Q P _59351 _59352) = (term195 A s Q P _59351 _59352).
Proof. exact (MK_COMB (@lem4796653 A s Q _59351 _59352) (@lem4796654 A P _59351 _59352)). Qed.
Lemma lem4796656 {A : Type'} (s : A -> Prop) (Q : type1402 A) (P : type1402 A) (_59351 : A) (_59352 : A) : (term174 A P s Q _59351 _59352) = (term195 A s Q P _59351 _59352).
Proof. exact (TRANS (@lem4796628 A s Q P _59351 _59352) (@lem4796655 A s Q P _59351 _59352)). Qed.
Lemma lem4796658 {A : Type'} (Q : type1402 A) (x : A) (y : A) (h1 : term34 A x y) (h2 : term85 A Q x y) : term190 A Q x y.
Proof. exact (conj (@lem4796203 A x y h1) (@lem4796210 A Q x y h2)). Qed.
Lemma lem4796659 {A : Type'} (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term34 A x y) (h2 : term85 A Q x y) (h3 : term38 A s x y) : term191 A s Q x y.
Proof. exact (conj (@lem4796195 A s x y h3) (@lem4796658 A Q x y h1 h2)). Qed.
Lemma lem4796660 {A : Type'} (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term34 A x y) (h2 : term85 A Q x y) (h3 : term38 A s x y) : term192 A s Q x y.
Proof. exact (conj (@lem4796188 A s x y h3) (@lem4796659 A Q s x y h1 h2 h3)). Qed.
Lemma lem4796662 {A : Type'} (_59351 : A) (_59352 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term195 A s Q P _59351 _59352.
Proof. exact (EQ_MP (@lem4796656 A s Q P _59351 _59352) (@lem4796625 A _59351 _59352 s P Q h1)). Qed.
Lemma lem4796663 {A : Type'} (_59351 : A) (_59352 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term195 A s Q P _59351 _59352.
Proof. exact (@lem4796662 A _59351 _59352 s P Q h1). Qed.
Lemma lem4796664 {A : Type'} (x : A) (y : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term195 A s Q P x y.
Proof. exact (@lem4796663 A x y s P Q h1). Qed.
Lemma lem4796667 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term34 A x y) (h2 : term85 A Q x y) (h3 : term67 A s P Q) (h4 : term38 A s x y) : term85 A P x y.
Proof. exact (@lem4796664 A x y s P Q h3 (@lem4796660 A Q s x y h1 h2 h4)). Qed.
Lemma lem4796668 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term34 A x y) (h2 : term85 A Q x y) (h3 : term67 A s P Q) (h4 : term38 A s x y) : term142 A P x y.
Proof. exact (fun h0 : P x y => @lem4796667 A P Q s x y h1 h2 h3 h4). Qed.
Lemma lem4796670 (p : Prop) : (term141 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4796671 {A : Type'} (P : type1402 A) (x : A) (y : A) : (term142 A P x y) = (term85 A P x y).
Proof. exact (@lem4796670 (P x y)). Qed.
Lemma lem4796672 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term34 A x y) (h2 : term85 A Q x y) (h3 : term67 A s P Q) (h4 : term38 A s x y) : term85 A P x y.
Proof. exact (EQ_MP (@lem4796671 A P x y) (@lem4796668 A P Q s x y h1 h2 h3 h4)). Qed.
Lemma lem4796688 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796689 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term129 A s P _59349 _59350) = (term145 A s P _59349 _59350).
Proof. exact (@lem4796688 (_59349 = _59350) (term127 A s _59350) (P _59349 _59350)). Qed.
Lemma lem4796705 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4796706 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term146 A s P _59349 _59350) = (term147 A P _59349 s _59350).
Proof. exact (@lem4796705 (P _59349 _59350) (term127 A s _59350)). Qed.
Lemma lem4796712 {A : Type'} (_59349 : A) (_59350 : A) : (term148 A _59349 _59350) = (term148 A _59349 _59350).
Proof. exact (eq_refl (term148 A _59349 _59350)). Qed.
Lemma lem4796713 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term145 A s P _59349 _59350) = (term149 A P _59349 s _59350).
Proof. exact (MK_COMB (@lem4796712 A _59349 _59350) (@lem4796706 A P _59349 s _59350)). Qed.
Lemma lem4796717 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796718 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term149 A P _59349 s _59350) = (term150 A P _59349 s _59350).
Proof. exact (@lem4796717 (P _59349 _59350) (_59349 = _59350) (term127 A s _59350)). Qed.
Lemma lem4796736 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term145 A s P _59349 _59350) = (term150 A P _59349 s _59350).
Proof. exact (TRANS (@lem4796713 A P _59349 s _59350) (@lem4796718 A P _59349 s _59350)). Qed.
Lemma lem4796737 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term129 A s P _59349 _59350) = (term150 A P _59349 s _59350).
Proof. exact (TRANS (@lem4796689 A s P _59349 _59350) (@lem4796736 A P _59349 s _59350)). Qed.
Lemma lem4796738 {A : Type'} (s : A -> Prop) (_59349 : A) : (term87 A s _59349) = (term87 A s _59349).
Proof. exact (eq_refl (term87 A s _59349)). Qed.
Lemma lem4796739 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term130 A s P _59349 _59350) = (term169 A P _59349 s _59350).
Proof. exact (MK_COMB (@lem4796738 A s _59349) (@lem4796737 A P _59349 s _59350)). Qed.
Lemma lem4796743 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796744 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term169 A P _59349 s _59350) = (term170 A P _59349 s _59350).
Proof. exact (@lem4796743 (P _59349 _59350) (term127 A s _59349) (term153 A _59349 s _59350)). Qed.
Lemma lem4796758 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796759 {A : Type'} (_59349 : A) (s : A -> Prop) (_59350 : A) : (term171 A _59349 s _59350) = (term172 A _59349 s _59350).
Proof. exact (@lem4796758 (_59349 = _59350) (term127 A s _59349) (term127 A s _59350)). Qed.
Lemma lem4796777 {A : Type'} (P : type1402 A) (_59349 : A) (_59350 : A) : (term156 A P _59349 _59350) = (term156 A P _59349 _59350).
Proof. exact (eq_refl (term156 A P _59349 _59350)). Qed.
Lemma lem4796778 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term170 A P _59349 s _59350) = (term173 A P _59349 s _59350).
Proof. exact (MK_COMB (@lem4796777 A P _59349 _59350) (@lem4796759 A _59349 s _59350)). Qed.
Lemma lem4796789 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term169 A P _59349 s _59350) = (term173 A P _59349 s _59350).
Proof. exact (TRANS (@lem4796744 A P _59349 s _59350) (@lem4796778 A P _59349 s _59350)). Qed.
Lemma lem4796790 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term130 A s P _59349 _59350) = (term173 A P _59349 s _59350).
Proof. exact (TRANS (@lem4796739 A P _59349 s _59350) (@lem4796789 A P _59349 s _59350)). Qed.
Lemma lem4796791 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4796792 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term196 A s P _59349 _59350) = (term197 A P _59349 s _59350).
Proof. exact (MK_COMB (@lem4796791) (@lem4796790 A P _59349 s _59350)). Qed.
Lemma lem4796818 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4796819 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term146 A s P _59349 _59350) = (term147 A P _59349 s _59350).
Proof. exact (@lem4796818 (P _59349 _59350) (term127 A s _59350)). Qed.
Lemma lem4796825 {A : Type'} (s : A -> Prop) (_59349 : A) : (term87 A s _59349) = (term87 A s _59349).
Proof. exact (eq_refl (term87 A s _59349)). Qed.
Lemma lem4796826 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term198 A s P _59349 _59350) = (term199 A P _59349 s _59350).
Proof. exact (MK_COMB (@lem4796825 A s _59349) (@lem4796819 A P _59349 s _59350)). Qed.
Lemma lem4796830 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796831 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term199 A P _59349 s _59350) = (term200 A P _59349 s _59350).
Proof. exact (@lem4796830 (P _59349 _59350) (term127 A s _59349) (term127 A s _59350)). Qed.
Lemma lem4796847 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term198 A s P _59349 _59350) = (term200 A P _59349 s _59350).
Proof. exact (TRANS (@lem4796826 A P _59349 s _59350) (@lem4796831 A P _59349 s _59350)). Qed.
Lemma lem4796848 {A : Type'} (_59349 : A) (_59350 : A) : (term148 A _59349 _59350) = (term148 A _59349 _59350).
Proof. exact (eq_refl (term148 A _59349 _59350)). Qed.
Lemma lem4796849 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term201 A s P _59349 _59350) = (term202 A P _59349 s _59350).
Proof. exact (MK_COMB (@lem4796848 A _59349 _59350) (@lem4796847 A P _59349 s _59350)). Qed.
Lemma lem4796853 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4796854 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term202 A P _59349 s _59350) = (term173 A P _59349 s _59350).
Proof. exact (@lem4796853 (P _59349 _59350) (_59349 = _59350) (term178 A _59349 s _59350)). Qed.
Lemma lem4796882 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : (term201 A s P _59349 _59350) = (term173 A P _59349 s _59350).
Proof. exact (TRANS (@lem4796849 A P _59349 s _59350) (@lem4796854 A P _59349 s _59350)). Qed.
Lemma lem4796883 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : ((term130 A s P _59349 _59350) = (term201 A s P _59349 _59350)) = ((term173 A P _59349 s _59350) = (term173 A P _59349 s _59350)).
Proof. exact (MK_COMB (@lem4796792 A P _59349 s _59350) (@lem4796882 A P _59349 s _59350)). Qed.
Lemma lem4796885 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4796886 (x : Prop) : (x = x) = True.
Proof. exact (@lem4796885 Prop x). Qed.
Lemma lem4796887 {A : Type'} (P : type1402 A) (_59349 : A) (s : A -> Prop) (_59350 : A) : ((term173 A P _59349 s _59350) = (term173 A P _59349 s _59350)) = True.
Proof. exact (@lem4796886 (term173 A P _59349 s _59350)). Qed.
Lemma lem4796888 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : ((term130 A s P _59349 _59350) = (term201 A s P _59349 _59350)) = True.
Proof. exact (TRANS (@lem4796883 A P _59349 s _59350) (@lem4796887 A P _59349 s _59350)). Qed.
Lemma lem4796889 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : True = ((term130 A s P _59349 _59350) = (term201 A s P _59349 _59350)).
Proof. exact (SYM (@lem4796888 A s P _59349 _59350)). Qed.
Lemma lem4796890 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term130 A s P _59349 _59350) = (term201 A s P _59349 _59350).
Proof. exact (EQ_MP (@lem4796889 A s P _59349 _59350) (@lem0)). Qed.
Lemma lem4796891 {A : Type'} (_59349 : A) (_59350 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term201 A s P _59349 _59350.
Proof. exact (EQ_MP (@lem4796890 A s P _59349 _59350) (@lem4796091 A _59349 _59350 s P Q h1)). Qed.
Lemma lem4796893 (b : Prop) (a : Prop) : (a \/ b) = (term179 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4796894 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term201 A s P _59349 _59350) = (term203 A s P _59349 _59350).
Proof. exact (@lem4796893 (term198 A s P _59349 _59350) (_59349 = _59350)). Qed.
Lemma lem4796896 (a : Prop) (b : Prop) : (term181 a b) = (term182 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4796897 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term204 A s P _59349 _59350) = (term205 A s P _59349 _59350).
Proof. exact (@lem4796896 (term127 A s _59349) (term146 A s P _59349 _59350)). Qed.
Lemma lem4796899 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4796900 {A : Type'} (s : A -> Prop) (_59349 : A) : (term185 A s _59349) = (s _59349).
Proof. exact (@lem4796899 (s _59349)). Qed.
Lemma lem4796901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4796902 {A : Type'} (s : A -> Prop) (_59349 : A) : (term186 A s _59349) = (term33 A s _59349).
Proof. exact (MK_COMB (@lem4796901) (@lem4796900 A s _59349)). Qed.
Lemma lem4796904 (a : Prop) (b : Prop) : (term181 a b) = (term182 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4796905 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term206 A s P _59349 _59350) = (term207 A s P _59349 _59350).
Proof. exact (@lem4796904 (term127 A s _59350) (P _59349 _59350)). Qed.
Lemma lem4796907 (a : Prop) : (term83 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4796908 {A : Type'} (s : A -> Prop) (_59350 : A) : (term185 A s _59350) = (s _59350).
Proof. exact (@lem4796907 (s _59350)). Qed.
Lemma lem4796909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4796910 {A : Type'} (s : A -> Prop) (_59350 : A) : (term186 A s _59350) = (term33 A s _59350).
Proof. exact (MK_COMB (@lem4796909) (@lem4796908 A s _59350)). Qed.
Lemma lem4796911 {A : Type'} (P : type1402 A) (_59349 : A) (_59350 : A) : (term85 A P _59349 _59350) = (term85 A P _59349 _59350).
Proof. exact (eq_refl (term85 A P _59349 _59350)). Qed.
Lemma lem4796912 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term207 A s P _59349 _59350) = (term208 A s P _59349 _59350).
Proof. exact (MK_COMB (@lem4796910 A s _59350) (@lem4796911 A P _59349 _59350)). Qed.
Lemma lem4796913 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term206 A s P _59349 _59350) = (term208 A s P _59349 _59350).
Proof. exact (TRANS (@lem4796905 A s P _59349 _59350) (@lem4796912 A s P _59349 _59350)). Qed.
Lemma lem4796914 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term205 A s P _59349 _59350) = (term209 A s P _59349 _59350).
Proof. exact (MK_COMB (@lem4796902 A s _59349) (@lem4796913 A s P _59349 _59350)). Qed.
Lemma lem4796915 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term204 A s P _59349 _59350) = (term209 A s P _59349 _59350).
Proof. exact (TRANS (@lem4796897 A s P _59349 _59350) (@lem4796914 A s P _59349 _59350)). Qed.
Lemma lem4796916 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4796917 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term210 A s P _59349 _59350) = (term211 A s P _59349 _59350).
Proof. exact (MK_COMB (@lem4796916) (@lem4796915 A s P _59349 _59350)). Qed.
Lemma lem4796918 {A : Type'} (_59349 : A) (_59350 : A) : (_59349 = _59350) = (_59349 = _59350).
Proof. exact (eq_refl (_59349 = _59350)). Qed.
Lemma lem4796919 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term203 A s P _59349 _59350) = (term212 A s P _59349 _59350).
Proof. exact (MK_COMB (@lem4796917 A s P _59349 _59350) (@lem4796918 A _59349 _59350)). Qed.
Lemma lem4796920 {A : Type'} (s : A -> Prop) (P : type1402 A) (_59349 : A) (_59350 : A) : (term201 A s P _59349 _59350) = (term212 A s P _59349 _59350).
Proof. exact (TRANS (@lem4796894 A s P _59349 _59350) (@lem4796919 A s P _59349 _59350)). Qed.
Lemma lem4796922 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term34 A x y) (h2 : term85 A Q x y) (h3 : term67 A s P Q) (h4 : term38 A s x y) : term208 A s P x y.
Proof. exact (conj (@lem4796181 A s x y h4) (@lem4796672 A P Q s x y h1 h2 h3 h4)). Qed.
Lemma lem4796923 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term34 A x y) (h2 : term85 A Q x y) (h3 : term67 A s P Q) (h4 : term38 A s x y) : term209 A s P x y.
Proof. exact (conj (@lem4796174 A s x y h4) (@lem4796922 A P Q s x y h1 h2 h3 h4)). Qed.
Lemma lem4796925 {A : Type'} (_59349 : A) (_59350 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term212 A s P _59349 _59350.
Proof. exact (EQ_MP (@lem4796920 A s P _59349 _59350) (@lem4796891 A _59349 _59350 s P Q h1)). Qed.
Lemma lem4796926 {A : Type'} (_59349 : A) (_59350 : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term212 A s P _59349 _59350.
Proof. exact (@lem4796925 A _59349 _59350 s P Q h1). Qed.
Lemma lem4796927 {A : Type'} (x : A) (y : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term212 A s P x y.
Proof. exact (@lem4796926 A x y s P Q h1). Qed.
Lemma lem4796930 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term34 A x y) (h2 : term85 A Q x y) (h3 : term67 A s P Q) (h4 : term38 A s x y) : x = y.
Proof. exact (@lem4796927 A x y s P Q h3 (@lem4796923 A P Q s x y h1 h2 h3 h4)). Qed.
Lemma lem4796931 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : term213 A x y.
Proof. exact (fun h0 : term34 A x y => @lem4796930 A P Q s x y h0 h1 h2 h3). Qed.
Lemma lem4796933 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4796934 {A : Type'} (x : A) (y : A) : (term213 A x y) = (x = y).
Proof. exact (@lem4796933 (x = y)). Qed.
Lemma lem4796935 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : x = y.
Proof. exact (EQ_MP (@lem4796934 A x y) (@lem4796931 A P Q s x y h1 h2 h3)). Qed.
Lemma lem4796938 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4796940 {A : Type'} (x : A) (y : A) : (term34 A x y) = (term214 A x y).
Proof. exact (@lem4796938 (x = y)). Qed.
Lemma lem4796943 {A : Type'} (s : A -> Prop) (x : A) (y : A) (h1 : term38 A s x y) : term214 A x y.
Proof. exact (EQ_MP (@lem4796940 A x y) (@lem4796073 A s x y h1)). Qed.
Lemma lem4796946 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : False.
Proof. exact (@lem4796943 A s x y h3 (@lem4796935 A P Q s x y h1 h2 h3)). Qed.
Lemma lem4796947 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : term215.
Proof. exact (fun h0 : ~ False => @lem4796946 A P Q s x y h1 h2 h3). Qed.
Lemma lem4796949 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4796950 : term215 = False.
Proof. exact (@lem4796949 False). Qed.
Lemma lem4796951 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : False.
Proof. exact (EQ_MP (@lem4796950) (@lem4796947 A P Q s x y h1 h2 h3)). Qed.
Lemma lem4796952 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : (term85 A Q x y) = False.
Proof. exact (prop_ext (fun h4 : term85 A Q x y => @lem4796951 A P Q s x y h1 h2 h3) (fun h4 : False => @lem4796067 A Q x y h1)). Qed.
Lemma lem4796953 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : False.
Proof. exact (EQ_MP (@lem4796952 A P Q s x y h1 h2 h3) (@lem4796067 A Q x y h1)). Qed.
Lemma lem4796954 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : (term85 A Q x y) = False.
Proof. exact (prop_ext (fun h4 : term85 A Q x y => @lem4796953 A P Q s x y h1 h2 h3) (fun h4 : False => @lem4795979 A Q x y h1)). Qed.
Lemma lem4796955 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : False.
Proof. exact (EQ_MP (@lem4796954 A P Q s x y h1 h2 h3) (@lem4795979 A Q x y h1)). Qed.
Lemma lem4796956 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : (term85 A Q x y) = False.
Proof. exact (prop_ext (fun h4 : term85 A Q x y => @lem4796955 A P Q s x y h1 h2 h3) (fun h4 : False => @lem4795979 A Q x y h1)). Qed.
Lemma lem4796957 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : False.
Proof. exact (EQ_MP (@lem4796956 A P Q s x y h1 h2 h3) (@lem4795979 A Q x y h1)). Qed.
Lemma lem4796958 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : (term85 A Q x y) = False.
Proof. exact (prop_ext (fun h4 : term85 A Q x y => @lem4796957 A P Q s x y h1 h2 h3) (fun h4 : False => @lem4795969 A Q x y h1)). Qed.
Lemma lem4796959 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : False.
Proof. exact (EQ_MP (@lem4796958 A P Q s x y h1 h2 h3) (@lem4795969 A Q x y h1)). Qed.
Lemma lem4796960 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : (term38 A s x y) = False.
Proof. exact (prop_ext (fun h4 : term38 A s x y => @lem4796959 A P Q s x y h1 h2 h3) (fun h4 : False => @lem4795961 A s x y h3)). Qed.
Lemma lem4796961 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : False.
Proof. exact (EQ_MP (@lem4796960 A P Q s x y h1 h2 h3) (@lem4795961 A s x y h3)). Qed.
Lemma lem4796962 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : (term85 A Q x y) = False.
Proof. exact (prop_ext (fun h4 : term85 A Q x y => @lem4796961 A P Q s x y h1 h2 h3) (fun h4 : False => @lem4795857 A Q x y h1)). Qed.
Lemma lem4796963 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : False.
Proof. exact (EQ_MP (@lem4796962 A P Q s x y h1 h2 h3) (@lem4795857 A Q x y h1)). Qed.
Lemma lem4796964 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : (term38 A s x y) = False.
Proof. exact (prop_ext (fun h4 : term38 A s x y => @lem4796963 A P Q s x y h1 h2 h3) (fun h4 : False => @lem4795851 A s x y h3)). Qed.
Lemma lem4796965 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : False.
Proof. exact (EQ_MP (@lem4796964 A P Q s x y h1 h2 h3) (@lem4795851 A s x y h3)). Qed.
Lemma lem4796966 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : (term85 A Q x y) = False.
Proof. exact (prop_ext (fun h4 : term85 A Q x y => @lem4796965 A P Q s x y h1 h2 h3) (fun h4 : False => @lem4795665 A Q x y h1)). Qed.
Lemma lem4796967 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term85 A Q x y) (h2 : term67 A s P Q) (h3 : term38 A s x y) : False.
Proof. exact (EQ_MP (@lem4796966 A P Q s x y h1 h2 h3) (@lem4795665 A Q x y h1)). Qed.
Lemma lem4796968 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term67 A s P Q) (h2 : term38 A s x y) : term84 A Q x y.
Proof. exact (fun h0 : term85 A Q x y => @lem4796967 A P Q s x y h0 h1 h2). Qed.
Lemma lem4796969 {A : Type'} (P : type1402 A) (Q : type1402 A) (s : A -> Prop) (x : A) (y : A) (h1 : term67 A s P Q) (h2 : term38 A s x y) : Q x y.
Proof. exact (EQ_MP (@lem4795664 A Q x y) (@lem4796968 A P Q s x y h1 h2)). Qed.
Lemma lem4796970 {A : Type'} (x : A) (y : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term42 A s Q x y.
Proof. exact (fun h0 : term38 A s x y => @lem4796969 A P Q s x y h1 h0). Qed.
Lemma lem4796975 {A : Type'} (x : A) (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term46 A s Q x.
Proof. exact (fun y : A => @lem4796970 A x y s P Q h1). Qed.
Lemma lem4796980 {A : Type'} (s : A -> Prop) (P : type1402 A) (Q : type1402 A) (h1 : term67 A s P Q) : term49 A s Q.
Proof. exact (fun x : A => @lem4796975 A x s P Q h1). Qed.
Lemma lem4796981 {A : Type'} (P : type1402 A) (s : A -> Prop) (Q : type1402 A) : term69 A P s Q.
Proof. exact (fun h0 : term67 A s P Q => @lem4796980 A s P Q h0). Qed.
Lemma lem4796986 {A : Type'} (P : type1402 A) (Q : type1402 A) : term71 A P Q.
Proof. exact (fun s : A -> Prop => @lem4796981 A P s Q). Qed.
Lemma lem4796991 {A : Type'} (P : type1402 A) : term73 A P.
Proof. exact (fun Q : type1402 A => @lem4796986 A P Q). Qed.
Lemma lem4796996 {A : Type'} : term75 A.
Proof. exact (fun P : type1402 A => @lem4796991 A P). Qed.
Lemma lem4796997 {A : Type'} : term77 A.
Proof. exact (EQ_MP (@lem4795658 A) (@lem4796996 A)). Qed.
Lemma lem4796999 {A : Type'} : term77 A.
Proof. exact (@lem4795423 A (@lem4796997 A)). Qed.
Lemma lem4797000 {A : Type'} (h1 : term78 A) : False.
Proof. exact (@lem4796999 A (@lem4795407 A h1)). Qed.
Lemma lem4797001 {A : Type'} (h1 : term78 A) : (term78 A) = False.
Proof. exact (prop_ext (fun h2 : term78 A => @lem4797000 A h1) (fun h2 : False => @lem4795407 A h1)). Qed.
Lemma lem4797002 {A : Type'} (h1 : term78 A) : False.
Proof. exact (EQ_MP (@lem4797001 A h1) (@lem4795407 A h1)). Qed.
Lemma lem4797003 {A : Type'} : term77 A.
Proof. exact (fun h0 : term78 A => @lem4797002 A h0). Qed.
Lemma lem4797004 {A : Type'} : term75 A.
Proof. exact (EQ_MP (@lem4795406 A) (@lem4797003 A)). Qed.
Lemma lem4797006 {A : Type'} : term31 A.
Proof. exact (EQ_MP (@lem4795402 A) (@lem4797004 A)). Qed.
Lemma lem4797007 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem4795113 A) (@lem4797006 A)). Qed.
