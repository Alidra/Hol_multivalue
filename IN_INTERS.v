Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_INTERS_term_abbrevs.
Require Import INTERS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem3205223 {A : Type'} (s : type686 A) : term0 A s.
Proof. exact (@lem3191123 A s). Qed.
Lemma lem3205224 {A : Type'} (s : type686 A) : (term0 A s) = ((@INTERS A s) = (term1 A s)).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3205250 {_83095 : Type'} : term2 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3205251 {_83095 : Type'} (p : _83095 -> Prop) : term3 _83095 p.
Proof. exact (@lem3205250 _83095 p). Qed.
Lemma lem3205252 {_83095 : Type'} (p : _83095 -> Prop) : (term3 _83095 p) = (term4 _83095 p).
Proof. exact (eq_refl (term3 _83095 p)). Qed.
Lemma lem3205253 {_83095 : Type'} (p : _83095 -> Prop) : term4 _83095 p.
Proof. exact (EQ_MP (@lem3205252 _83095 p) (@lem3205251 _83095 p)). Qed.
Lemma lem3205254 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term5 _83095 p x.
Proof. exact (@lem3205253 _83095 p x). Qed.
Lemma lem3205255 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term5 _83095 p x) = ((term6 _83095 x p) = (p x)).
Proof. exact (eq_refl (term5 _83095 p x)). Qed.
Lemma lem3205275 {A : Type'} (s : type686 A) : (@INTERS A s) = (term1 A s).
Proof. exact (EQ_MP (@lem3205224 A s) (@lem3205223 A s)). Qed.
Lemma lem3205276 {A : Type'} (s : type686 A) : (@INTERS A s) = (term1 A s).
Proof. exact (@lem3205275 A s). Qed.
Lemma lem3205287 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3205288 {A : Type'} (x : A) (s : type686 A) : (term7 A x s) = (term8 A x s).
Proof. exact (MK_COMB (@lem3205287 A x) (@lem3205276 A s)). Qed.
Lemma lem3205290 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term6 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3205255 _83095 p x) (@lem3205254 _83095 p x)). Qed.
Lemma lem3205291 {A : Type'} (p : A -> Prop) (x : A) : (term6 A x p) = (p x).
Proof. exact (@lem3205290 A p x). Qed.
Lemma lem3205292 {A : Type'} (s : type686 A) (x : A) : (term9 A x s) = (term10 A s x).
Proof. exact (@lem3205291 A (term11 A s) x). Qed.
Lemma lem3205293 {A : Type'} (s : type686 A) (x : A) : (term10 A s x) = (term12 A s x).
Proof. exact (eq_refl (term10 A s x)). Qed.
Lemma lem3205294 {A : Type'} (GEN_PVAR_3 : A) : (@SETSPEC A GEN_PVAR_3) = (@SETSPEC A GEN_PVAR_3).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_3)). Qed.
Lemma lem3205295 {A : Type'} (GEN_PVAR_3 : A) (s : type686 A) (x : A) : (term13 A GEN_PVAR_3 s x) = (term14 A GEN_PVAR_3 s x).
Proof. exact (MK_COMB (@lem3205294 A GEN_PVAR_3) (@lem3205293 A s x)). Qed.
Lemma lem3205296 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3205297 {A : Type'} (GEN_PVAR_3 : A) (s : type686 A) (x : A) : (term15 A GEN_PVAR_3 s x) = (term16 A GEN_PVAR_3 s x).
Proof. exact (MK_COMB (@lem3205295 A GEN_PVAR_3 s x) (@lem3205296 A x)). Qed.
Lemma lem3205298 {A : Type'} (GEN_PVAR_3 : A) (s : type686 A) : (term17 A GEN_PVAR_3 s) = (term18 A GEN_PVAR_3 s).
Proof. exact (fun_ext (fun x : A => @lem3205297 A GEN_PVAR_3 s x)). Qed.
Lemma lem3205299 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3205300 {A : Type'} (GEN_PVAR_3 : A) (s : type686 A) : (term19 A GEN_PVAR_3 s) = (term20 A GEN_PVAR_3 s).
Proof. exact (MK_COMB (@lem3205299 A) (@lem3205298 A GEN_PVAR_3 s)). Qed.
Lemma lem3205301 {A : Type'} (s : type686 A) : (term21 A s) = (term22 A s).
Proof. exact (fun_ext (fun GEN_PVAR_3 : A => @lem3205300 A GEN_PVAR_3 s)). Qed.
Lemma lem3205302 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3205303 {A : Type'} (s : type686 A) : (term23 A s) = (term1 A s).
Proof. exact (MK_COMB (@lem3205302 A) (@lem3205301 A s)). Qed.
Lemma lem3205304 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3205305 {A : Type'} (x : A) (s : type686 A) : (term9 A x s) = (term8 A x s).
Proof. exact (MK_COMB (@lem3205304 A x) (@lem3205303 A s)). Qed.
Lemma lem3205306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205307 {A : Type'} (x : A) (s : type686 A) : (term24 A x s) = (term25 A x s).
Proof. exact (MK_COMB (@lem3205306) (@lem3205305 A x s)). Qed.
Lemma lem3205308 {A : Type'} (s : type686 A) (x : A) : (term10 A s x) = (term12 A s x).
Proof. exact (eq_refl (term10 A s x)). Qed.
Lemma lem3205309 {A : Type'} (s : type686 A) (x : A) : ((term9 A x s) = (term10 A s x)) = ((term8 A x s) = (term12 A s x)).
Proof. exact (MK_COMB (@lem3205307 A x s) (@lem3205308 A s x)). Qed.
Lemma lem3205310 {A : Type'} (s : type686 A) (x : A) : (term8 A x s) = (term12 A s x).
Proof. exact (EQ_MP (@lem3205309 A s x) (@lem3205292 A s x)). Qed.
Lemma lem3205317 {A : Type'} (s : type686 A) (x : A) : (term7 A x s) = (term12 A s x).
Proof. exact (TRANS (@lem3205288 A x s) (@lem3205310 A s x)). Qed.
Lemma lem3205318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205319 {A : Type'} (s : type686 A) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3205318) (@lem3205317 A s x)). Qed.
Lemma lem3205326 {A : Type'} (s : type686 A) (x : A) : (term12 A s x) = (term12 A s x).
Proof. exact (eq_refl (term12 A s x)). Qed.
Lemma lem3205327 {A : Type'} (s : type686 A) (x : A) : ((term7 A x s) = (term12 A s x)) = ((term12 A s x) = (term12 A s x)).
Proof. exact (MK_COMB (@lem3205319 A s x) (@lem3205326 A s x)). Qed.
Lemma lem3205329 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3205330 (x : Prop) : (x = x) = True.
Proof. exact (@lem3205329 Prop x). Qed.
Lemma lem3205331 {A : Type'} (s : type686 A) (x : A) : ((term12 A s x) = (term12 A s x)) = True.
Proof. exact (@lem3205330 (term12 A s x)). Qed.
Lemma lem3205334 {A : Type'} (s : type686 A) (x : A) : (term28 A s x) = (term28 A s x).
Proof. exact (eq_refl (term28 A s x)). Qed.
Lemma lem3205335 {A : Type'} (s : type686 A) (x : A) : (term28 A s x) = (((term12 A s x) = (term12 A s x)) = True).
Proof. exact (eq_refl (term28 A s x)). Qed.
Lemma lem3205336 {A : Type'} (s : type686 A) (x : A) : (term29 A s x) = (term29 A s x).
Proof. exact (eq_refl (term29 A s x)). Qed.
Lemma lem3205337 {A : Type'} (s : type686 A) (x : A) : ((term28 A s x) = (term28 A s x)) = ((term28 A s x) = (((term12 A s x) = (term12 A s x)) = True)).
Proof. exact (MK_COMB (@lem3205336 A s x) (@lem3205335 A s x)). Qed.
Lemma lem3205338 {A : Type'} (s : type686 A) (x : A) : (term28 A s x) = (((term12 A s x) = (term12 A s x)) = True).
Proof. exact (eq_refl (term28 A s x)). Qed.
Lemma lem3205339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3205340 {A : Type'} (s : type686 A) (x : A) : (term29 A s x) = (term30 A s x).
Proof. exact (MK_COMB (@lem3205339) (@lem3205338 A s x)). Qed.
Lemma lem3205341 {A : Type'} (s : type686 A) (x : A) : (((term12 A s x) = (term12 A s x)) = True) = (((term12 A s x) = (term12 A s x)) = True).
Proof. exact (eq_refl (((term12 A s x) = (term12 A s x)) = True)). Qed.
Lemma lem3205342 {A : Type'} (s : type686 A) (x : A) : ((term28 A s x) = (((term12 A s x) = (term12 A s x)) = True)) = ((((term12 A s x) = (term12 A s x)) = True) = (((term12 A s x) = (term12 A s x)) = True)).
Proof. exact (MK_COMB (@lem3205340 A s x) (@lem3205341 A s x)). Qed.
Lemma lem3205343 {A : Type'} (s : type686 A) (x : A) : ((term28 A s x) = (term28 A s x)) = ((((term12 A s x) = (term12 A s x)) = True) = (((term12 A s x) = (term12 A s x)) = True)).
Proof. exact (TRANS (@lem3205337 A s x) (@lem3205342 A s x)). Qed.
Lemma lem3205344 {A : Type'} (s : type686 A) (x : A) : (((term12 A s x) = (term12 A s x)) = True) = (((term12 A s x) = (term12 A s x)) = True).
Proof. exact (EQ_MP (@lem3205343 A s x) (@lem3205334 A s x)). Qed.
Lemma lem3205345 {A : Type'} (s : type686 A) (x : A) : ((term12 A s x) = (term12 A s x)) = True.
Proof. exact (EQ_MP (@lem3205344 A s x) (@lem3205331 A s x)). Qed.
Lemma lem3205346 {A : Type'} (s : type686 A) (x : A) : ((term7 A x s) = (term12 A s x)) = True.
Proof. exact (TRANS (@lem3205327 A s x) (@lem3205345 A s x)). Qed.
Lemma lem3205347 {A : Type'} (s : type686 A) : (term31 A s) = (term32 A).
Proof. exact (fun_ext (fun x : A => @lem3205346 A s x)). Qed.
Lemma lem3205348 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3205349 {A : Type'} (s : type686 A) : (term33 A s) = (term34 A).
Proof. exact (MK_COMB (@lem3205348 A) (@lem3205347 A s)). Qed.
Lemma lem3205351 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205352 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (@lem3205351 A t). Qed.
Lemma lem3205353 {A : Type'} : (term34 A) = True.
Proof. exact (@lem3205352 A True). Qed.
Lemma lem3205354 {A : Type'} (s : type686 A) : (term33 A s) = True.
Proof. exact (TRANS (@lem3205349 A s) (@lem3205353 A)). Qed.
Lemma lem3205355 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (fun_ext (fun s : type686 A => @lem3205354 A s)). Qed.
Lemma lem3205356 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3205357 {A : Type'} : (term38 A) = (term39 A).
Proof. exact (MK_COMB (@lem3205356 A) (@lem3205355 A)). Qed.
Lemma lem3205359 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3205360 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (@lem3205359 (type686 A) t). Qed.
Lemma lem3205361 {A : Type'} : (term39 A) = True.
Proof. exact (@lem3205360 A True). Qed.
Lemma lem3205362 {A : Type'} : (term38 A) = True.
Proof. exact (TRANS (@lem3205357 A) (@lem3205361 A)). Qed.
Lemma lem3205363 {A : Type'} : True = (term38 A).
Proof. exact (SYM (@lem3205362 A)). Qed.
Lemma lem3205364 {A : Type'} : term38 A.
Proof. exact (EQ_MP (@lem3205363 A) (@lem0)). Qed.
