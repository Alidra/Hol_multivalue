Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXTENSIONAL_UNIV_term_abbrevs.
Require Import EXTENSIONAL_spec.
Require Import IN_UNIV_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm3184714_spec.
Require Import thm3184717_spec.
Require Import thm7_spec.
Lemma lem4383337 {_83152 : Type'} : term0 _83152.
Proof. exact (EQ_MP (@lem3184717 _83152) (@lem3184714 _83152)). Qed.
Lemma lem4383338 {_83152 : Type'} (p : _83152 -> Prop) : term1 _83152 p.
Proof. exact (@lem4383337 _83152 p). Qed.
Lemma lem4383339 {_83152 : Type'} (p : _83152 -> Prop) : (term1 _83152 p) = (term2 _83152 p).
Proof. exact (eq_refl (term1 _83152 p)). Qed.
Lemma lem4383340 {_83152 : Type'} (p : _83152 -> Prop) : term2 _83152 p.
Proof. exact (EQ_MP (@lem4383339 _83152 p) (@lem4383338 _83152 p)). Qed.
Lemma lem4383341 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term3 _83152 p x.
Proof. exact (@lem4383340 _83152 p x). Qed.
Lemma lem4383342 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term3 _83152 p x) = ((term4 _83152 p x) = (p x)).
Proof. exact (eq_refl (term3 _83152 p x)). Qed.
Lemma lem4383365 {A : Type'} (x : A) : term5 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem4383366 {A : Type'} (x : A) : (term5 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term5 A x)). Qed.
Lemma lem4383367 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem4383366 A x) (@lem4383365 A x)). Qed.
Lemma lem4383368 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem4383370 {A B : Type'} (s : A -> Prop) : term6 A B s.
Proof. exact (@lem4382798 A B s). Qed.
Lemma lem4383371 {A B : Type'} (s : A -> Prop) : (term6 A B s) = ((@EXTENSIONAL A B s) = (term7 A B s)).
Proof. exact (eq_refl (term6 A B s)). Qed.
Lemma lem4383378 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term7 A B s).
Proof. exact (EQ_MP (@lem4383371 A B s) (@lem4383370 A B s)). Qed.
Lemma lem4383379 {_105178 A : Type'} (s : A -> Prop) : (@EXTENSIONAL A _105178 s) = (term8 _105178 A s).
Proof. exact (@lem4383378 A _105178 s). Qed.
Lemma lem4383380 {_105178 A : Type'} : (@EXTENSIONAL A _105178 (@UNIV A)) = (term9 _105178 A).
Proof. exact (@lem4383379 _105178 A (@UNIV A)). Qed.
Lemma lem4383392 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4383368 A x) (@lem4383367 A x)). Qed.
Lemma lem4383393 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem4383392 A x). Qed.
Lemma lem4383394 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4383395 {A : Type'} (x : A) : (term10 A x) = (~ True).
Proof. exact (MK_COMB (@lem4383394) (@lem4383393 A x)). Qed.
Lemma lem4383397 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4383398 {A : Type'} (x : A) : (term10 A x) = False.
Proof. exact (TRANS (@lem4383395 A x) (@lem4383397)). Qed.
Lemma lem4383399 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4383400 {A : Type'} (x : A) : (term11 A x) = (imp False).
Proof. exact (MK_COMB (@lem4383399) (@lem4383398 A x)). Qed.
Lemma lem4383403 {_105178 A : Type'} (f : A -> _105178) (x : A) : ((f x) = (@ARB _105178)) = ((f x) = (@ARB _105178)).
Proof. exact (eq_refl ((f x) = (@ARB _105178))). Qed.
Lemma lem4383404 {_105178 A : Type'} (f : A -> _105178) (x : A) : (term12 _105178 A f x) = (term13 _105178 A f x).
Proof. exact (MK_COMB (@lem4383400 A x) (@lem4383403 _105178 A f x)). Qed.
Lemma lem4383406 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4383407 {_105178 A : Type'} (f : A -> _105178) (x : A) : (term13 _105178 A f x) = True.
Proof. exact (@lem4383406 ((f x) = (@ARB _105178))). Qed.
Lemma lem4383408 {_105178 A : Type'} (f : A -> _105178) (x : A) : (term12 _105178 A f x) = True.
Proof. exact (TRANS (@lem4383404 _105178 A f x) (@lem4383407 _105178 A f x)). Qed.
Lemma lem4383409 {_105178 A : Type'} (f : A -> _105178) : (term14 _105178 A f) = (term15 A).
Proof. exact (fun_ext (fun x : A => @lem4383408 _105178 A f x)). Qed.
Lemma lem4383410 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4383411 {_105178 A : Type'} (f : A -> _105178) : (term16 _105178 A f) = (term17 A).
Proof. exact (MK_COMB (@lem4383410 A) (@lem4383409 _105178 A f)). Qed.
Lemma lem4383413 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4383414 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (@lem4383413 A t). Qed.
Lemma lem4383415 {A : Type'} : (term17 A) = True.
Proof. exact (@lem4383414 A True). Qed.
Lemma lem4383416 {_105178 A : Type'} (f : A -> _105178) : (term16 _105178 A f) = True.
Proof. exact (TRANS (@lem4383411 _105178 A f) (@lem4383415 A)). Qed.
Lemma lem4383417 {_105178 A : Type'} (GEN_PVAR_139 : A -> _105178) : (@SETSPEC (A -> _105178) GEN_PVAR_139) = (@SETSPEC (A -> _105178) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (A -> _105178) GEN_PVAR_139)). Qed.
Lemma lem4383418 {_105178 A : Type'} (f : A -> _105178) (GEN_PVAR_139 : A -> _105178) : (term19 _105178 A GEN_PVAR_139 f) = (@SETSPEC (A -> _105178) GEN_PVAR_139 True).
Proof. exact (MK_COMB (@lem4383417 _105178 A GEN_PVAR_139) (@lem4383416 _105178 A f)). Qed.
Lemma lem4383419 {_105178 A : Type'} (f : A -> _105178) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4383420 {_105178 A : Type'} (GEN_PVAR_139 : A -> _105178) (f : A -> _105178) : (term20 _105178 A GEN_PVAR_139 f) = (@SETSPEC (A -> _105178) GEN_PVAR_139 True f).
Proof. exact (MK_COMB (@lem4383418 _105178 A f GEN_PVAR_139) (@lem4383419 _105178 A f)). Qed.
Lemma lem4383421 {_105178 A : Type'} (GEN_PVAR_139 : A -> _105178) : (term21 _105178 A GEN_PVAR_139) = (term22 _105178 A GEN_PVAR_139).
Proof. exact (fun_ext (fun f : A -> _105178 => @lem4383420 _105178 A GEN_PVAR_139 f)). Qed.
Lemma lem4383422 {_105178 A : Type'} : (@ex (A -> _105178)) = (@ex (A -> _105178)).
Proof. exact (eq_refl (@ex (A -> _105178))). Qed.
Lemma lem4383423 {_105178 A : Type'} (GEN_PVAR_139 : A -> _105178) : (term23 _105178 A GEN_PVAR_139) = (term24 _105178 A GEN_PVAR_139).
Proof. exact (MK_COMB (@lem4383422 _105178 A) (@lem4383421 _105178 A GEN_PVAR_139)). Qed.
Lemma lem4383428 {_105178 A : Type'} : (term25 _105178 A) = (term26 _105178 A).
Proof. exact (fun_ext (fun GEN_PVAR_139 : A -> _105178 => @lem4383423 _105178 A GEN_PVAR_139)). Qed.
Lemma lem4383429 {_105178 A : Type'} : (@GSPEC (A -> _105178)) = (@GSPEC (A -> _105178)).
Proof. exact (eq_refl (@GSPEC (A -> _105178))). Qed.
Lemma lem4383430 {_105178 A : Type'} : (term9 _105178 A) = (term27 _105178 A).
Proof. exact (MK_COMB (@lem4383429 _105178 A) (@lem4383428 _105178 A)). Qed.
Lemma lem4383431 {_105178 A : Type'} : (@EXTENSIONAL A _105178 (@UNIV A)) = (term27 _105178 A).
Proof. exact (TRANS (@lem4383380 _105178 A) (@lem4383430 _105178 A)). Qed.
Lemma lem4383432 {_105178 A : Type'} (f : A -> _105178) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4383433 {_105178 A : Type'} (f : A -> _105178) : (@EXTENSIONAL A _105178 (@UNIV A) f) = (term28 _105178 A f).
Proof. exact (MK_COMB (@lem4383431 _105178 A) (@lem4383432 _105178 A f)). Qed.
Lemma lem4383435 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term4 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4383342 _83152 p x) (@lem4383341 _83152 p x)). Qed.
Lemma lem4383436 {_105178 A : Type'} (p : type805 _105178 A) (x : A -> _105178) : (term29 _105178 A p x) = (p x).
Proof. exact (@lem4383435 (A -> _105178) p x). Qed.
Lemma lem4383437 {_105178 A : Type'} (f : A -> _105178) : (term30 _105178 A f) = (term31 _105178 A f).
Proof. exact (@lem4383436 _105178 A (term32 _105178 A) f). Qed.
Lemma lem4383438 {_105178 A : Type'} (f : A -> _105178) : (term31 _105178 A f) = True.
Proof. exact (eq_refl (term31 _105178 A f)). Qed.
Lemma lem4383439 {_105178 A : Type'} (GEN_PVAR_139 : A -> _105178) : (@SETSPEC (A -> _105178) GEN_PVAR_139) = (@SETSPEC (A -> _105178) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (A -> _105178) GEN_PVAR_139)). Qed.
Lemma lem4383440 {_105178 A : Type'} (f : A -> _105178) (GEN_PVAR_139 : A -> _105178) : (term33 _105178 A GEN_PVAR_139 f) = (@SETSPEC (A -> _105178) GEN_PVAR_139 True).
Proof. exact (MK_COMB (@lem4383439 _105178 A GEN_PVAR_139) (@lem4383438 _105178 A f)). Qed.
Lemma lem4383441 {_105178 A : Type'} (f : A -> _105178) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4383442 {_105178 A : Type'} (GEN_PVAR_139 : A -> _105178) (f : A -> _105178) : (term34 _105178 A GEN_PVAR_139 f) = (@SETSPEC (A -> _105178) GEN_PVAR_139 True f).
Proof. exact (MK_COMB (@lem4383440 _105178 A f GEN_PVAR_139) (@lem4383441 _105178 A f)). Qed.
Lemma lem4383443 {_105178 A : Type'} (GEN_PVAR_139 : A -> _105178) : (term35 _105178 A GEN_PVAR_139) = (term22 _105178 A GEN_PVAR_139).
Proof. exact (fun_ext (fun f : A -> _105178 => @lem4383442 _105178 A GEN_PVAR_139 f)). Qed.
Lemma lem4383444 {_105178 A : Type'} : (@ex (A -> _105178)) = (@ex (A -> _105178)).
Proof. exact (eq_refl (@ex (A -> _105178))). Qed.
Lemma lem4383445 {_105178 A : Type'} (GEN_PVAR_139 : A -> _105178) : (term36 _105178 A GEN_PVAR_139) = (term24 _105178 A GEN_PVAR_139).
Proof. exact (MK_COMB (@lem4383444 _105178 A) (@lem4383443 _105178 A GEN_PVAR_139)). Qed.
Lemma lem4383446 {_105178 A : Type'} : (term37 _105178 A) = (term26 _105178 A).
Proof. exact (fun_ext (fun GEN_PVAR_139 : A -> _105178 => @lem4383445 _105178 A GEN_PVAR_139)). Qed.
Lemma lem4383447 {_105178 A : Type'} : (@GSPEC (A -> _105178)) = (@GSPEC (A -> _105178)).
Proof. exact (eq_refl (@GSPEC (A -> _105178))). Qed.
Lemma lem4383448 {_105178 A : Type'} : (term38 _105178 A) = (term27 _105178 A).
Proof. exact (MK_COMB (@lem4383447 _105178 A) (@lem4383446 _105178 A)). Qed.
Lemma lem4383449 {_105178 A : Type'} (f : A -> _105178) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4383450 {_105178 A : Type'} (f : A -> _105178) : (term30 _105178 A f) = (term28 _105178 A f).
Proof. exact (MK_COMB (@lem4383448 _105178 A) (@lem4383449 _105178 A f)). Qed.
Lemma lem4383451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4383452 {_105178 A : Type'} (f : A -> _105178) : (term39 _105178 A f) = (term40 _105178 A f).
Proof. exact (MK_COMB (@lem4383451) (@lem4383450 _105178 A f)). Qed.
Lemma lem4383453 {_105178 A : Type'} (f : A -> _105178) : (term31 _105178 A f) = True.
Proof. exact (eq_refl (term31 _105178 A f)). Qed.
Lemma lem4383454 {_105178 A : Type'} (f : A -> _105178) : ((term30 _105178 A f) = (term31 _105178 A f)) = ((term28 _105178 A f) = True).
Proof. exact (MK_COMB (@lem4383452 _105178 A f) (@lem4383453 _105178 A f)). Qed.
Lemma lem4383455 {_105178 A : Type'} (f : A -> _105178) : (term28 _105178 A f) = True.
Proof. exact (EQ_MP (@lem4383454 _105178 A f) (@lem4383437 _105178 A f)). Qed.
Lemma lem4383456 {_105178 A : Type'} (f : A -> _105178) : (@EXTENSIONAL A _105178 (@UNIV A) f) = True.
Proof. exact (TRANS (@lem4383433 _105178 A f) (@lem4383455 _105178 A f)). Qed.
Lemma lem4383457 {_105178 A : Type'} : (term41 _105178 A) = (term32 _105178 A).
Proof. exact (fun_ext (fun f : A -> _105178 => @lem4383456 _105178 A f)). Qed.
Lemma lem4383458 {_105178 A : Type'} : (@all (A -> _105178)) = (@all (A -> _105178)).
Proof. exact (eq_refl (@all (A -> _105178))). Qed.
Lemma lem4383459 {_105178 A : Type'} : (term42 _105178 A) = (term43 _105178 A).
Proof. exact (MK_COMB (@lem4383458 _105178 A) (@lem4383457 _105178 A)). Qed.
Lemma lem4383461 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4383462 {_105178 A : Type'} (t : Prop) : (term44 _105178 A t) = t.
Proof. exact (@lem4383461 (A -> _105178) t). Qed.
Lemma lem4383463 {_105178 A : Type'} : (term43 _105178 A) = True.
Proof. exact (@lem4383462 _105178 A True). Qed.
Lemma lem4383464 {_105178 A : Type'} : (term42 _105178 A) = True.
Proof. exact (TRANS (@lem4383459 _105178 A) (@lem4383463 _105178 A)). Qed.
Lemma lem4383465 {_105178 A : Type'} : True = (term42 _105178 A).
Proof. exact (SYM (@lem4383464 _105178 A)). Qed.
Lemma lem4383466 {_105178 A : Type'} : term42 _105178 A.
Proof. exact (EQ_MP (@lem4383465 _105178 A) (@lem0)). Qed.
