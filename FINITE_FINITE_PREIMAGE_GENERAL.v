Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_FINITE_PREIMAGE_GENERAL_term_abbrevs.
Require Import EXISTS_IN_IMAGE_spec.
Require Import EXTENSION_spec.
Require Import FINITE_FINITE_UNIONS_spec.
Require Import FINITE_IMAGE_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import IN_UNIONS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm18394_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem3616286 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) : term0 _88003 _88004 P f.
Proof. exact (@lem3388254 _88003 _88004 P f). Qed.
Lemma lem3616287 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) : (term0 _88003 _88004 P f) = (term1 _88003 _88004 P f).
Proof. exact (eq_refl (term0 _88003 _88004 P f)). Qed.
Lemma lem3616288 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) : term1 _88003 _88004 P f.
Proof. exact (EQ_MP (@lem3616287 _88003 _88004 P f) (@lem3616286 _88003 _88004 P f)). Qed.
Lemma lem3616289 {_88003 _88004 : Type'} (P : _88003 -> Prop) (f : _88004 -> _88003) (s : _88004 -> Prop) : term2 _88003 _88004 P f s.
Proof. exact (@lem3616288 _88003 _88004 P f s). Qed.
Lemma lem3616290 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term2 _88003 _88004 P f s) = ((term3 _88003 _88004 f s P) = (term4 _88003 _88004 s P f)).
Proof. exact (eq_refl (term2 _88003 _88004 P f s)). Qed.
Lemma lem3616292 {A : Type'} (s : type686 A) : term5 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem3616293 {A : Type'} (s : type686 A) : (term5 A s) = (term6 A s).
Proof. exact (eq_refl (term5 A s)). Qed.
Lemma lem3616294 {A : Type'} (s : type686 A) : term6 A s.
Proof. exact (EQ_MP (@lem3616293 A s) (@lem3616292 A s)). Qed.
Lemma lem3616295 {A : Type'} (s : type686 A) (x : A) : term7 A s x.
Proof. exact (@lem3616294 A s x). Qed.
Lemma lem3616296 {A : Type'} (s : type686 A) (x : A) : (term7 A s x) = ((term8 A x s) = (term9 A s x)).
Proof. exact (eq_refl (term7 A s x)). Qed.
Lemma lem3616322 {_83095 : Type'} : term10 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3616323 {_83095 : Type'} (p : _83095 -> Prop) : term11 _83095 p.
Proof. exact (@lem3616322 _83095 p). Qed.
Lemma lem3616324 {_83095 : Type'} (p : _83095 -> Prop) : (term11 _83095 p) = (term12 _83095 p).
Proof. exact (eq_refl (term11 _83095 p)). Qed.
Lemma lem3616325 {_83095 : Type'} (p : _83095 -> Prop) : term12 _83095 p.
Proof. exact (EQ_MP (@lem3616324 _83095 p) (@lem3616323 _83095 p)). Qed.
Lemma lem3616326 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term13 _83095 p x.
Proof. exact (@lem3616325 _83095 p x). Qed.
Lemma lem3616327 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term13 _83095 p x) = ((term14 _83095 x p) = (p x)).
Proof. exact (eq_refl (term13 _83095 p x)). Qed.
Lemma lem3616336 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3616337 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (eq_refl (term15 A s)). Qed.
Lemma lem3616338 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (EQ_MP (@lem3616337 A s) (@lem3616336 A s)). Qed.
Lemma lem3616339 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term17 A s t.
Proof. exact (@lem3616338 A s t). Qed.
Lemma lem3616340 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term17 A s t) = ((s = t) = (term18 A s t)).
Proof. exact (eq_refl (term17 A s t)). Qed.
Lemma lem3616342 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term19 A B t s f) : term19 A B t s f.
Proof. exact (h1). Qed.
Lemma lem3616343 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : term20 A B t s f.
Proof. exact (h1). Qed.
Lemma lem3616344 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem3616345 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : (term21 A B s f t) = (term22 A B s f t)) : (term21 A B s f t) = (term22 A B s f t).
Proof. exact (h1). Qed.
Lemma lem3616346 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (eq_refl (term23 A)). Qed.
Lemma lem3616347 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : (term21 A B s f t) = (term22 A B s f t)) : (term24 A B s f t) = (term25 A B s f t).
Proof. exact (MK_COMB (@lem3616346 A) (@lem3616345 A B s f t h1)). Qed.
Lemma lem3616348 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term25 A B s f t) = (term26 A B s f t).
Proof. exact (eq_refl (term25 A B s f t)). Qed.
Lemma lem3616349 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term27 A B s f t) = (term27 A B s f t).
Proof. exact (eq_refl (term27 A B s f t)). Qed.
Lemma lem3616350 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : ((term24 A B s f t) = (term25 A B s f t)) = ((term24 A B s f t) = (term26 A B s f t)).
Proof. exact (MK_COMB (@lem3616349 A B s f t) (@lem3616348 A B s f t)). Qed.
Lemma lem3616351 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term24 A B s f t) = (term28 A B s f t).
Proof. exact (eq_refl (term24 A B s f t)). Qed.
Lemma lem3616352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3616353 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term27 A B s f t) = (term29 A B s f t).
Proof. exact (MK_COMB (@lem3616352) (@lem3616351 A B s f t)). Qed.
Lemma lem3616354 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term26 A B s f t) = (term26 A B s f t).
Proof. exact (eq_refl (term26 A B s f t)). Qed.
Lemma lem3616355 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : ((term24 A B s f t) = (term26 A B s f t)) = ((term28 A B s f t) = (term26 A B s f t)).
Proof. exact (MK_COMB (@lem3616353 A B s f t) (@lem3616354 A B s f t)). Qed.
Lemma lem3616356 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : ((term24 A B s f t) = (term25 A B s f t)) = ((term28 A B s f t) = (term26 A B s f t)).
Proof. exact (TRANS (@lem3616350 A B s f t) (@lem3616355 A B s f t)). Qed.
Lemma lem3616357 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : (term21 A B s f t) = (term22 A B s f t)) : (term28 A B s f t) = (term26 A B s f t).
Proof. exact (EQ_MP (@lem3616356 A B s f t) (@lem3616347 A B s f t h1)). Qed.
Lemma lem3616358 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : (term21 A B s f t) = (term22 A B s f t)) : (term26 A B s f t) = (term28 A B s f t).
Proof. exact (SYM (@lem3616357 A B s f t h1)). Qed.
Lemma lem3616360 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem3616340 A s t) (@lem3616339 A s t)). Qed.
Lemma lem3616361 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (@lem3616360 A s t). Qed.
Lemma lem3616362 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : ((term21 A B s f t) = (term22 A B s f t)) = (term30 A B s f t).
Proof. exact (@lem3616361 A (term21 A B s f t) (term22 A B s f t)). Qed.
Lemma lem3616363 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term30 A B s f t) = ((term21 A B s f t) = (term22 A B s f t)).
Proof. exact (SYM (@lem3616362 A B s f t)). Qed.
Lemma lem3616371 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term14 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3616327 _83095 p x) (@lem3616326 _83095 p x)). Qed.
Lemma lem3616372 {A : Type'} (p : A -> Prop) (x : A) : (term14 A x p) = (p x).
Proof. exact (@lem3616371 A p x). Qed.
Lemma lem3616373 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term31 A B x s f t) = (term32 A B s f t x).
Proof. exact (@lem3616372 A (term33 A B s f t) x). Qed.
Lemma lem3616374 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term32 A B s f t x) = (term34 A B s f x t).
Proof. exact (eq_refl (term32 A B s f t x)). Qed.
Lemma lem3616375 {A : Type'} (GEN_PVAR_96 : A) : (@SETSPEC A GEN_PVAR_96) = (@SETSPEC A GEN_PVAR_96).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_96)). Qed.
Lemma lem3616376 {A B : Type'} (GEN_PVAR_96 : A) (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term35 A B GEN_PVAR_96 s f t x) = (term36 A B GEN_PVAR_96 s f x t).
Proof. exact (MK_COMB (@lem3616375 A GEN_PVAR_96) (@lem3616374 A B s f x t)). Qed.
Lemma lem3616377 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3616378 {A B : Type'} (GEN_PVAR_96 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term37 A B GEN_PVAR_96 s f t x) = (term38 A B GEN_PVAR_96 s f t x).
Proof. exact (MK_COMB (@lem3616376 A B GEN_PVAR_96 s f x t) (@lem3616377 A x)). Qed.
Lemma lem3616379 {A B : Type'} (GEN_PVAR_96 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term39 A B GEN_PVAR_96 s f t) = (term40 A B GEN_PVAR_96 s f t).
Proof. exact (fun_ext (fun x : A => @lem3616378 A B GEN_PVAR_96 s f t x)). Qed.
Lemma lem3616380 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3616381 {A B : Type'} (GEN_PVAR_96 : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term41 A B GEN_PVAR_96 s f t) = (term42 A B GEN_PVAR_96 s f t).
Proof. exact (MK_COMB (@lem3616380 A) (@lem3616379 A B GEN_PVAR_96 s f t)). Qed.
Lemma lem3616382 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term43 A B s f t) = (term44 A B s f t).
Proof. exact (fun_ext (fun GEN_PVAR_96 : A => @lem3616381 A B GEN_PVAR_96 s f t)). Qed.
Lemma lem3616383 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3616384 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term45 A B s f t) = (term21 A B s f t).
Proof. exact (MK_COMB (@lem3616383 A) (@lem3616382 A B s f t)). Qed.
Lemma lem3616385 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3616386 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term31 A B x s f t) = (term46 A B x s f t).
Proof. exact (MK_COMB (@lem3616385 A x) (@lem3616384 A B s f t)). Qed.
Lemma lem3616387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3616388 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term47 A B x s f t) = (term48 A B x s f t).
Proof. exact (MK_COMB (@lem3616387) (@lem3616386 A B x s f t)). Qed.
Lemma lem3616389 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term32 A B s f t x) = (term34 A B s f x t).
Proof. exact (eq_refl (term32 A B s f t x)). Qed.
Lemma lem3616390 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : ((term31 A B x s f t) = (term32 A B s f t x)) = ((term46 A B x s f t) = (term34 A B s f x t)).
Proof. exact (MK_COMB (@lem3616388 A B x s f t) (@lem3616389 A B s f x t)). Qed.
Lemma lem3616391 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term46 A B x s f t) = (term34 A B s f x t).
Proof. exact (EQ_MP (@lem3616390 A B s f x t) (@lem3616373 A B s f t x)). Qed.
Lemma lem3616394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3616395 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term48 A B x s f t) = (term49 A B s f x t).
Proof. exact (MK_COMB (@lem3616394) (@lem3616391 A B s f x t)). Qed.
Lemma lem3616397 {A : Type'} (s : type686 A) (x : A) : (term8 A x s) = (term9 A s x).
Proof. exact (EQ_MP (@lem3616296 A s x) (@lem3616295 A s x)). Qed.
Lemma lem3616398 {A : Type'} (s : type686 A) (x : A) : (term8 A x s) = (term9 A s x).
Proof. exact (@lem3616397 A s x). Qed.
Lemma lem3616399 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term50 A B x s f t) = (term51 A B s f t x).
Proof. exact (@lem3616398 A (term52 A B s f t) x). Qed.
Lemma lem3616414 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : ((term46 A B x s f t) = (term50 A B x s f t)) = ((term34 A B s f x t) = (term51 A B s f t x)).
Proof. exact (MK_COMB (@lem3616395 A B s f x t) (@lem3616399 A B s f t x)). Qed.
Lemma lem3616417 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term53 A B s f t) = (term54 A B s f t).
Proof. exact (fun_ext (fun x : A => @lem3616414 A B s f t x)). Qed.
Lemma lem3616418 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3616419 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term30 A B s f t) = (term55 A B s f t).
Proof. exact (MK_COMB (@lem3616418 A) (@lem3616417 A B s f t)). Qed.
Lemma lem3616424 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term55 A B s f t) = (term30 A B s f t).
Proof. exact (SYM (@lem3616419 A B s f t)). Qed.
Lemma lem3616434 {_88003 _88004 : Type'} (s : _88004 -> Prop) (P : _88003 -> Prop) (f : _88004 -> _88003) : (term3 _88003 _88004 f s P) = (term4 _88003 _88004 s P f).
Proof. exact (EQ_MP (@lem3616290 _88003 _88004 s P f) (@lem3616289 _88003 _88004 P f s)). Qed.
Lemma lem3616435 {A B : Type'} (s : B -> Prop) (P : type686 A) (f : type1470 A B) : (term56 A B f s P) = (term57 A B s P f).
Proof. exact (@lem3616434 (A -> Prop) B s P f). Qed.
Lemma lem3616436 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) : (term58 A B s f t x) = (term59 A B t x s f).
Proof. exact (@lem3616435 A B t (term60 A x) (term61 A B s f)). Qed.
Lemma lem3616437 {A : Type'} (x : A) (t : A -> Prop) : (term62 A x t) = (@IN A x t).
Proof. exact (eq_refl (term62 A x t)). Qed.
Lemma lem3616438 {A B : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> B) (t' : B -> Prop) : (term63 A B t s f t') = (term63 A B t s f t').
Proof. exact (eq_refl (term63 A B t s f t')). Qed.
Lemma lem3616439 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) (t' : A -> Prop) : (term64 A B s f t x t') = (term65 A B s f t x t').
Proof. exact (MK_COMB (@lem3616438 A B t' s f t) (@lem3616437 A x t')). Qed.
Lemma lem3616440 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term66 A B s f t x) = (term67 A B s f t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3616439 A B s f t x t')). Qed.
Lemma lem3616441 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3616442 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term58 A B s f t x) = (term51 A B s f t x).
Proof. exact (MK_COMB (@lem3616441 A) (@lem3616440 A B s f t x)). Qed.
Lemma lem3616443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3616444 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (x : A) : (term68 A B s f t x) = (term69 A B s f t x).
Proof. exact (MK_COMB (@lem3616443) (@lem3616442 A B s f t x)). Qed.
Lemma lem3616445 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : B) : (term70 A B x s f x') = (term71 A B x s f x').
Proof. exact (eq_refl (term70 A B x s f x')). Qed.
Lemma lem3616446 {B : Type'} (x : B) (t : B -> Prop) : (term72 B x t) = (term72 B x t).
Proof. exact (eq_refl (term72 B x t)). Qed.
Lemma lem3616447 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) (x' : B) : (term73 A B t x s f x') = (term74 A B t x s f x').
Proof. exact (MK_COMB (@lem3616446 B x' t) (@lem3616445 A B x s f x')). Qed.
Lemma lem3616448 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) : (term75 A B t x s f) = (term76 A B t x s f).
Proof. exact (fun_ext (fun x' : B => @lem3616447 A B t x s f x')). Qed.
Lemma lem3616449 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3616450 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) : (term59 A B t x s f) = (term77 A B t x s f).
Proof. exact (MK_COMB (@lem3616449 B) (@lem3616448 A B t x s f)). Qed.
Lemma lem3616451 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) : ((term58 A B s f t x) = (term59 A B t x s f)) = ((term51 A B s f t x) = (term77 A B t x s f)).
Proof. exact (MK_COMB (@lem3616444 A B s f t x) (@lem3616450 A B t x s f)). Qed.
Lemma lem3616452 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) : (term51 A B s f t x) = (term77 A B t x s f).
Proof. exact (EQ_MP (@lem3616451 A B t x s f) (@lem3616436 A B t x s f)). Qed.
Lemma lem3616460 {A B : Type'} (f : A -> B) (y : A) : (term78 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3616461 {A B : Type'} (f : type1470 A B) (y : B) : (term79 A B f y) = (f y).
Proof. exact (@lem3616460 B (A -> Prop) f y). Qed.
Lemma lem3616462 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term80 A B s f x) = (term81 A B s f x).
Proof. exact (@lem3616461 A B (term61 A B s f) x). Qed.
Lemma lem3616463 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : B) : (term81 A B s f a) = (term82 A B s f a).
Proof. exact (eq_refl (term81 A B s f a)). Qed.
Lemma lem3616464 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term83 A B s f) = (term61 A B s f).
Proof. exact (fun_ext (fun a : B => @lem3616463 A B s f a)). Qed.
Lemma lem3616465 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3616466 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term80 A B s f x) = (term81 A B s f x).
Proof. exact (MK_COMB (@lem3616464 A B s f) (@lem3616465 B x)). Qed.
Lemma lem3616467 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3616468 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term84 A B s f x) = (term85 A B s f x).
Proof. exact (MK_COMB (@lem3616467 A) (@lem3616466 A B s f x)). Qed.
Lemma lem3616469 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term81 A B s f x) = (term82 A B s f x).
Proof. exact (eq_refl (term81 A B s f x)). Qed.
Lemma lem3616470 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : ((term80 A B s f x) = (term81 A B s f x)) = ((term81 A B s f x) = (term82 A B s f x)).
Proof. exact (MK_COMB (@lem3616468 A B s f x) (@lem3616469 A B s f x)). Qed.
Lemma lem3616471 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term81 A B s f x) = (term82 A B s f x).
Proof. exact (EQ_MP (@lem3616470 A B s f x) (@lem3616462 A B s f x)). Qed.
Lemma lem3616480 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3616481 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : B) : (term71 A B x s f x') = (term86 A B x s f x').
Proof. exact (MK_COMB (@lem3616480 A x) (@lem3616471 A B s f x')). Qed.
Lemma lem3616482 {B : Type'} (x : B) (t : B -> Prop) : (term72 B x t) = (term72 B x t).
Proof. exact (eq_refl (term72 B x t)). Qed.
Lemma lem3616483 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) (x' : B) : (term74 A B t x s f x') = (term87 A B t x s f x').
Proof. exact (MK_COMB (@lem3616482 B x' t) (@lem3616481 A B x s f x')). Qed.
Lemma lem3616486 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) : (term76 A B t x s f) = (term88 A B t x s f).
Proof. exact (fun_ext (fun x' : B => @lem3616483 A B t x s f x')). Qed.
Lemma lem3616487 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3616488 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) : (term77 A B t x s f) = (term89 A B t x s f).
Proof. exact (MK_COMB (@lem3616487 B) (@lem3616486 A B t x s f)). Qed.
Lemma lem3616493 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) : (term51 A B s f t x) = (term89 A B t x s f).
Proof. exact (TRANS (@lem3616452 A B t x s f) (@lem3616488 A B t x s f)). Qed.
Lemma lem3616494 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (t : B -> Prop) : (term49 A B s f x t) = (term49 A B s f x t).
Proof. exact (eq_refl (term49 A B s f x t)). Qed.
Lemma lem3616495 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) : ((term34 A B s f x t) = (term51 A B s f t x)) = ((term34 A B s f x t) = (term89 A B t x s f)).
Proof. exact (MK_COMB (@lem3616494 A B s f x t) (@lem3616493 A B t x s f)). Qed.
Lemma lem3616498 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term54 A B s f t) = (term90 A B t s f).
Proof. exact (fun_ext (fun x : A => @lem3616495 A B t x s f)). Qed.
Lemma lem3616499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3616500 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term55 A B s f t) = (term91 A B t s f).
Proof. exact (MK_COMB (@lem3616499 A) (@lem3616498 A B t s f)). Qed.
Lemma lem3616505 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term91 A B t s f) = (term55 A B s f t).
Proof. exact (SYM (@lem3616500 A B t s f)). Qed.
Lemma lem3616543 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3616544 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3616543 A P x). Qed.
Lemma lem3616545 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3616544 A s x). Qed.
Lemma lem3616546 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3616547 {A : Type'} (s : A -> Prop) (x : A) : (term72 A x s) = (term92 A s x).
Proof. exact (MK_COMB (@lem3616546) (@lem3616545 A s x)). Qed.
Lemma lem3616549 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3616550 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3616549 B P x). Qed.
Lemma lem3616551 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term93 A B f x t) = (term94 A B t f x).
Proof. exact (@lem3616550 B t (f x)). Qed.
Lemma lem3616552 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term34 A B s f x t) = (term95 A B s t f x).
Proof. exact (MK_COMB (@lem3616547 A s x) (@lem3616551 A B t f x)). Qed.
Lemma lem3616555 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3616556 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term49 A B s f x t) = (term96 A B s t f x).
Proof. exact (MK_COMB (@lem3616555) (@lem3616552 A B s t f x)). Qed.
Lemma lem3616564 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3616565 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3616564 B P x). Qed.
Lemma lem3616566 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem3616565 B t x). Qed.
Lemma lem3616567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3616568 {B : Type'} (t : B -> Prop) (x : B) : (term72 B x t) = (term92 B t x).
Proof. exact (MK_COMB (@lem3616567) (@lem3616566 B t x)). Qed.
Lemma lem3616570 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term14 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3616571 {A : Type'} (p : A -> Prop) (x : A) : (term14 A x p) = (p x).
Proof. exact (@lem3616570 A p x). Qed.
Lemma lem3616572 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (x' : A) : (term97 A B x' s f x) = (term98 A B s f x x').
Proof. exact (@lem3616571 A (term99 A B s f x) x'). Qed.
Lemma lem3616573 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term98 A B s f x' x) = (term100 A B s f x x').
Proof. exact (eq_refl (term98 A B s f x' x)). Qed.
Lemma lem3616574 {A : Type'} (GEN_PVAR_97 : A) : (@SETSPEC A GEN_PVAR_97) = (@SETSPEC A GEN_PVAR_97).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_97)). Qed.
Lemma lem3616575 {A B : Type'} (GEN_PVAR_97 : A) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term101 A B GEN_PVAR_97 s f x' x) = (term102 A B GEN_PVAR_97 s f x x').
Proof. exact (MK_COMB (@lem3616574 A GEN_PVAR_97) (@lem3616573 A B s f x x')). Qed.
Lemma lem3616576 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3616577 {A B : Type'} (GEN_PVAR_97 : A) (s : A -> Prop) (f : A -> B) (x : B) (x' : A) : (term103 A B GEN_PVAR_97 s f x x') = (term104 A B GEN_PVAR_97 s f x x').
Proof. exact (MK_COMB (@lem3616575 A B GEN_PVAR_97 s f x' x) (@lem3616576 A x')). Qed.
Lemma lem3616578 {A B : Type'} (GEN_PVAR_97 : A) (s : A -> Prop) (f : A -> B) (x : B) : (term105 A B GEN_PVAR_97 s f x) = (term106 A B GEN_PVAR_97 s f x).
Proof. exact (fun_ext (fun x' : A => @lem3616577 A B GEN_PVAR_97 s f x x')). Qed.
Lemma lem3616579 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3616580 {A B : Type'} (GEN_PVAR_97 : A) (s : A -> Prop) (f : A -> B) (x : B) : (term107 A B GEN_PVAR_97 s f x) = (term108 A B GEN_PVAR_97 s f x).
Proof. exact (MK_COMB (@lem3616579 A) (@lem3616578 A B GEN_PVAR_97 s f x)). Qed.
Lemma lem3616581 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term109 A B s f x) = (term110 A B s f x).
Proof. exact (fun_ext (fun GEN_PVAR_97 : A => @lem3616580 A B GEN_PVAR_97 s f x)). Qed.
Lemma lem3616582 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3616583 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term111 A B s f x) = (term82 A B s f x).
Proof. exact (MK_COMB (@lem3616582 A) (@lem3616581 A B s f x)). Qed.
Lemma lem3616584 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3616585 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : B) : (term97 A B x s f x') = (term86 A B x s f x').
Proof. exact (MK_COMB (@lem3616584 A x) (@lem3616583 A B s f x')). Qed.
Lemma lem3616586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3616587 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (x' : B) : (term112 A B x s f x') = (term113 A B x s f x').
Proof. exact (MK_COMB (@lem3616586) (@lem3616585 A B x s f x')). Qed.
Lemma lem3616588 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term98 A B s f x' x) = (term100 A B s f x x').
Proof. exact (eq_refl (term98 A B s f x' x)). Qed.
Lemma lem3616589 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : ((term97 A B x s f x') = (term98 A B s f x' x)) = ((term86 A B x s f x') = (term100 A B s f x x')).
Proof. exact (MK_COMB (@lem3616587 A B x s f x') (@lem3616588 A B s f x x')). Qed.
Lemma lem3616590 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term86 A B x s f x') = (term100 A B s f x x').
Proof. exact (EQ_MP (@lem3616589 A B s f x x') (@lem3616572 A B s f x' x)). Qed.
Lemma lem3616594 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3616595 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3616594 A P x). Qed.
Lemma lem3616596 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3616595 A s x). Qed.
Lemma lem3616597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3616598 {A : Type'} (s : A -> Prop) (x : A) : (term72 A x s) = (term92 A s x).
Proof. exact (MK_COMB (@lem3616597) (@lem3616596 A s x)). Qed.
Lemma lem3616601 {A B : Type'} (f : A -> B) (x : A) (x' : B) : ((f x) = x') = ((f x) = x').
Proof. exact (eq_refl ((f x) = x')). Qed.
Lemma lem3616602 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term100 A B s f x x') = (term114 A B s f x x').
Proof. exact (MK_COMB (@lem3616598 A s x) (@lem3616601 A B f x x')). Qed.
Lemma lem3616605 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term86 A B x s f x') = (term114 A B s f x x').
Proof. exact (TRANS (@lem3616590 A B s f x x') (@lem3616602 A B s f x x')). Qed.
Lemma lem3616606 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term87 A B t x s f x') = (term115 A B t s f x x').
Proof. exact (MK_COMB (@lem3616568 B t x') (@lem3616605 A B s f x x')). Qed.
Lemma lem3616609 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term88 A B t x s f) = (term116 A B t s f x).
Proof. exact (fun_ext (fun x' : B => @lem3616606 A B t s f x x')). Qed.
Lemma lem3616610 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3616611 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term89 A B t x s f) = (term117 A B t s f x).
Proof. exact (MK_COMB (@lem3616610 B) (@lem3616609 A B t s f x)). Qed.
Lemma lem3616616 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term34 A B s f x t) = (term89 A B t x s f)) = ((term95 A B s t f x) = (term117 A B t s f x)).
Proof. exact (MK_COMB (@lem3616556 A B s t f x) (@lem3616611 A B t s f x)). Qed.
Lemma lem3616619 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term90 A B t s f) = (term118 A B t s f).
Proof. exact (fun_ext (fun x : A => @lem3616616 A B t s f x)). Qed.
Lemma lem3616620 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3616621 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term91 A B t s f) = (term119 A B t s f).
Proof. exact (MK_COMB (@lem3616620 A) (@lem3616619 A B t s f)). Qed.
Lemma lem3616626 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term119 A B t s f) = (term91 A B t s f).
Proof. exact (SYM (@lem3616621 A B t s f)). Qed.
Lemma lem3616628 (p : Prop) : p = (term120 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3616629 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term119 A B t s f) = (term121 A B t s f).
Proof. exact (@lem3616628 (term119 A B t s f)). Qed.
Lemma lem3616630 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term121 A B t s f) = (term119 A B t s f).
Proof. exact (SYM (@lem3616629 A B t s f)). Qed.
Lemma lem3616631 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term122 A B t s f) : term122 A B t s f.
Proof. exact (h1). Qed.
Lemma lem3616634 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term121 A B t s f) : term121 A B t s f.
Proof. exact (h1). Qed.
Lemma lem3616635 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term123 A B t s f.
Proof. exact (fun h0 : term121 A B t s f => @lem3616634 A B t s f h0). Qed.
Lemma lem3616636 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term123 A B t s f) : term123 A B t s f.
Proof. exact (h1). Qed.
Lemma lem3616637 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term121 A B t s f) : term121 A B t s f.
Proof. exact (h1). Qed.
Lemma lem3616638 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term121 A B t s f) (h2 : term123 A B t s f) : term121 A B t s f.
Proof. exact (@lem3616636 A B t s f h2 (@lem3616637 A B t s f h1)). Qed.
Lemma lem3616639 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term121 A B t s f) : term124 A B t s f.
Proof. exact (fun h0 : term123 A B t s f => @lem3616638 A B t s f h1 h0). Qed.
Lemma lem3616640 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term123 A B t s f) : term123 A B t s f.
Proof. exact (h1). Qed.
Lemma lem3616641 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term121 A B t s f) (h2 : term123 A B t s f) : term121 A B t s f.
Proof. exact (@lem3616639 A B t s f h1 (@lem3616640 A B t s f h2)). Qed.
Lemma lem3616642 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term123 A B t s f) : term123 A B t s f.
Proof. exact (fun h0 : term121 A B t s f => @lem3616641 A B t s f h0 h1). Qed.
Lemma lem3616643 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term125 A B t s f.
Proof. exact (fun h0 : term123 A B t s f => @lem3616642 A B t s f h0). Qed.
Lemma lem3616646 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term123 A B t s f.
Proof. exact (@lem3616643 A B t s f (@lem3616635 A B t s f)). Qed.
Lemma lem3616647 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term123 A B t s f.
Proof. exact (@lem3616646 A B t s f). Qed.
Lemma lem3616661 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3616662 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term121 A B t s f) = (term126 A B t s f).
Proof. exact (@lem3616661 (term122 A B t s f)). Qed.
Lemma lem3616664 (t : Prop) : (term127 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3616665 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term126 A B t s f) = (term119 A B t s f).
Proof. exact (@lem3616664 (term119 A B t s f)). Qed.
Lemma lem3616670 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term121 A B t s f) = (term119 A B t s f).
Proof. exact (TRANS (@lem3616662 A B t s f) (@lem3616665 A B t s f)). Qed.
Lemma lem3616705 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term128 A B s f) = (term129 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3616670 A B t s f)). Qed.
Lemma lem3616706 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3616707 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term130 A B s f) = (term131 A B s f).
Proof. exact (MK_COMB (@lem3616706 B) (@lem3616705 A B s f)). Qed.
Lemma lem3616712 {A B : Type'} (f : A -> B) : (term132 A B f) = (term133 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3616707 A B s f)). Qed.
Lemma lem3616713 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3616714 {A B : Type'} (f : A -> B) : (term134 A B f) = (term135 A B f).
Proof. exact (MK_COMB (@lem3616713 A) (@lem3616712 A B f)). Qed.
Lemma lem3616719 {A B : Type'} : (term136 A B) = (term137 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3616714 A B f)). Qed.
Lemma lem3616720 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3616729 {A B : Type'} : (term138 A B) = (term139 A B).
Proof. exact (MK_COMB (@lem3616720 A B) (@lem3616719 A B)). Qed.
Lemma lem3616738 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term115 A B t s f x x') = (term115 A B t s f x x').
Proof. exact (eq_refl (term115 A B t s f x x')). Qed.
Lemma lem3616739 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term116 A B t s f x) = (term116 A B t s f x).
Proof. exact (fun_ext (fun x' : B => @lem3616738 A B t s f x x')). Qed.
Lemma lem3616740 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3616741 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term117 A B t s f x) = (term117 A B t s f x).
Proof. exact (MK_COMB (@lem3616740 B) (@lem3616739 A B t s f x)). Qed.
Lemma lem3616748 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term96 A B s t f x) = (term96 A B s t f x).
Proof. exact (eq_refl (term96 A B s t f x)). Qed.
Lemma lem3616749 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term95 A B s t f x) = (term117 A B t s f x)) = ((term95 A B s t f x) = (term117 A B t s f x)).
Proof. exact (MK_COMB (@lem3616748 A B s t f x) (@lem3616741 A B t s f x)). Qed.
Lemma lem3616750 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term118 A B t s f) = (term118 A B t s f).
Proof. exact (fun_ext (fun x : A => @lem3616749 A B t s f x)). Qed.
Lemma lem3616751 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3616752 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term119 A B t s f) = (term119 A B t s f).
Proof. exact (MK_COMB (@lem3616751 A) (@lem3616750 A B t s f)). Qed.
Lemma lem3616753 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term129 A B s f) = (term129 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3616752 A B t s f)). Qed.
Lemma lem3616754 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3616755 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term131 A B s f) = (term131 A B s f).
Proof. exact (MK_COMB (@lem3616754 B) (@lem3616753 A B s f)). Qed.
Lemma lem3616756 {A B : Type'} (f : A -> B) : (term133 A B f) = (term133 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3616755 A B s f)). Qed.
Lemma lem3616757 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3616758 {A B : Type'} (f : A -> B) : (term135 A B f) = (term135 A B f).
Proof. exact (MK_COMB (@lem3616757 A) (@lem3616756 A B f)). Qed.
Lemma lem3616759 {A B : Type'} : (term137 A B) = (term137 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3616758 A B f)). Qed.
Lemma lem3616760 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3616761 {A B : Type'} : (term139 A B) = (term139 A B).
Proof. exact (MK_COMB (@lem3616760 A B) (@lem3616759 A B)). Qed.
Lemma lem3616800 {A B : Type'} : (term138 A B) = (term139 A B).
Proof. exact (TRANS (@lem3616729 A B) (@lem3616761 A B)). Qed.
Lemma lem3616801 {A B : Type'} : (term139 A B) = (term138 A B).
Proof. exact (SYM (@lem3616800 A B)). Qed.
Lemma lem3616803 (p : Prop) : p = (term120 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3616804 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term95 A B s t f x) = (term117 A B t s f x)) = (term140 A B t s f x).
Proof. exact (@lem3616803 ((term95 A B s t f x) = (term117 A B t s f x))). Qed.
Lemma lem3616805 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term140 A B t s f x) = ((term95 A B s t f x) = (term117 A B t s f x)).
Proof. exact (SYM (@lem3616804 A B t s f x)). Qed.
Lemma lem3616806 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term141 A B t s f x) : term141 A B t s f x.
Proof. exact (h1). Qed.
Lemma lem3616815 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term142 A B s t f x) = (term143 A B s t f x).
Proof. exact (@lem17045 (s x) (term94 A B t f x)). Qed.
Lemma lem3616829 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term144 A B s f x x') = (term145 A B s f x x').
Proof. exact (@lem17045 (s x) ((f x) = x')). Qed.
Lemma lem3616834 {B : Type'} (t : B -> Prop) (x : B) : (term146 B t x) = (term146 B t x).
Proof. exact (eq_refl (term146 B t x)). Qed.
Lemma lem3616835 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term147 A B t s f x x') = (term148 A B t s f x x').
Proof. exact (MK_COMB (@lem3616834 B t x') (@lem3616829 A B s f x x')). Qed.
Lemma lem3616836 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term149 A B t s f x x') = (term147 A B t s f x x').
Proof. exact (@lem17045 (t x') (term114 A B s f x x')). Qed.
Lemma lem3616837 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term149 A B t s f x x') = (term148 A B t s f x x').
Proof. exact (TRANS (@lem3616836 A B t s f x x') (@lem3616835 A B t s f x x')). Qed.
Lemma lem3616840 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term115 A B t s f x x') = (term115 A B t s f x x').
Proof. exact (eq_refl (term115 A B t s f x x')). Qed.
Lemma lem3616841 {B : Type'} (P : B -> Prop) : (term150 B P) = (term151 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem3616842 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term152 A B t s f x) = (term153 A B t s f x).
Proof. exact (@lem3616841 B (term116 A B t s f x)). Qed.
Lemma lem3616843 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term154 A B t s f x x') = (term115 A B t s f x x').
Proof. exact (eq_refl (term154 A B t s f x x')). Qed.
Lemma lem3616844 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3616845 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term155 A B t s f x x') = (term149 A B t s f x x').
Proof. exact (MK_COMB (@lem3616844) (@lem3616843 A B t s f x x')). Qed.
Lemma lem3616846 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term155 A B t s f x x') = (term148 A B t s f x x').
Proof. exact (TRANS (@lem3616845 A B t s f x x') (@lem3616837 A B t s f x x')). Qed.
Lemma lem3616847 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term156 A B t s f x) = (term157 A B t s f x).
Proof. exact (fun_ext (fun x' : B => @lem3616846 A B t s f x x')). Qed.
Lemma lem3616848 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3616849 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term153 A B t s f x) = (term158 A B t s f x).
Proof. exact (MK_COMB (@lem3616848 B) (@lem3616847 A B t s f x)). Qed.
Lemma lem3616850 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term152 A B t s f x) = (term158 A B t s f x).
Proof. exact (TRANS (@lem3616842 A B t s f x) (@lem3616849 A B t s f x)). Qed.
Lemma lem3616851 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term116 A B t s f x) = (term116 A B t s f x).
Proof. exact (fun_ext (fun x' : B => @lem3616840 A B t s f x x')). Qed.
Lemma lem3616852 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3616853 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term117 A B t s f x) = (term117 A B t s f x).
Proof. exact (MK_COMB (@lem3616852 B) (@lem3616851 A B t s f x)). Qed.
Lemma lem3616854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3616855 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term159 A B s t f x) = (term160 A B s t f x).
Proof. exact (MK_COMB (@lem3616854) (@lem3616815 A B s t f x)). Qed.
Lemma lem3616856 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term161 A B t s f x) = (term162 A B t s f x).
Proof. exact (MK_COMB (@lem3616855 A B s t f x) (@lem3616853 A B t s f x)). Qed.
Lemma lem3616858 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term163 A B s t f x) = (term163 A B s t f x).
Proof. exact (eq_refl (term163 A B s t f x)). Qed.
Lemma lem3616859 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term164 A B t s f x) = (term165 A B t s f x).
Proof. exact (MK_COMB (@lem3616858 A B s t f x) (@lem3616850 A B t s f x)). Qed.
Lemma lem3616860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3616861 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term166 A B t s f x) = (term167 A B t s f x).
Proof. exact (MK_COMB (@lem3616860) (@lem3616859 A B t s f x)). Qed.
Lemma lem3616862 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term168 A B t s f x) = (term169 A B t s f x).
Proof. exact (MK_COMB (@lem3616861 A B t s f x) (@lem3616856 A B t s f x)). Qed.
Lemma lem3616863 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term141 A B t s f x) = (term168 A B t s f x).
Proof. exact (@lem17646 (term95 A B s t f x) (term117 A B t s f x)). Qed.
Lemma lem3616864 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term141 A B t s f x) = (term169 A B t s f x).
Proof. exact (TRANS (@lem3616863 A B t s f x) (@lem3616862 A B t s f x)). Qed.
Lemma lem3616943 {A : Type'} (P : Prop) (Q : A -> Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3616944 {B : Type'} (P : Prop) (Q : B -> Prop) : (term170 B P Q) = (term171 B P Q).
Proof. exact (@lem3616943 B P Q). Qed.
Lemma lem3616945 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term172 A B t s f x) = (term173 A B t s f x).
Proof. exact (@lem3616944 B (term143 A B s t f x) (term116 A B t s f x)). Qed.
Lemma lem3616946 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term154 A B t s f x x') = (term115 A B t s f x x').
Proof. exact (eq_refl (term154 A B t s f x x')). Qed.
Lemma lem3616947 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term174 A B t s f x) = (term116 A B t s f x).
Proof. exact (fun_ext (fun x' : B => @lem3616946 A B t s f x x')). Qed.
Lemma lem3616948 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3616949 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term175 A B t s f x) = (term117 A B t s f x).
Proof. exact (MK_COMB (@lem3616948 B) (@lem3616947 A B t s f x)). Qed.
Lemma lem3616950 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term160 A B s t f x) = (term160 A B s t f x).
Proof. exact (eq_refl (term160 A B s t f x)). Qed.
Lemma lem3616951 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term172 A B t s f x) = (term162 A B t s f x).
Proof. exact (MK_COMB (@lem3616950 A B s t f x) (@lem3616949 A B t s f x)). Qed.
Lemma lem3616952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3616953 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term176 A B t s f x) = (term177 A B t s f x).
Proof. exact (MK_COMB (@lem3616952) (@lem3616951 A B t s f x)). Qed.
Lemma lem3616954 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term154 A B t s f x x') = (term115 A B t s f x x').
Proof. exact (eq_refl (term154 A B t s f x x')). Qed.
Lemma lem3616955 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term160 A B s t f x) = (term160 A B s t f x).
Proof. exact (eq_refl (term160 A B s t f x)). Qed.
Lemma lem3616956 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term178 A B t s f x x') = (term179 A B t s f x x').
Proof. exact (MK_COMB (@lem3616955 A B s t f x) (@lem3616954 A B t s f x x')). Qed.
Lemma lem3616957 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term180 A B t s f x) = (term181 A B t s f x).
Proof. exact (fun_ext (fun x' : B => @lem3616956 A B t s f x x')). Qed.
Lemma lem3616958 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3616959 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term173 A B t s f x) = (term182 A B t s f x).
Proof. exact (MK_COMB (@lem3616958 B) (@lem3616957 A B t s f x)). Qed.
Lemma lem3616960 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term172 A B t s f x) = (term173 A B t s f x)) = ((term162 A B t s f x) = (term182 A B t s f x)).
Proof. exact (MK_COMB (@lem3616953 A B t s f x) (@lem3616959 A B t s f x)). Qed.
Lemma lem3616961 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term162 A B t s f x) = (term182 A B t s f x).
Proof. exact (EQ_MP (@lem3616960 A B t s f x) (@lem3616945 A B t s f x)). Qed.
Lemma lem3616962 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term167 A B t s f x) = (term167 A B t s f x).
Proof. exact (eq_refl (term167 A B t s f x)). Qed.
Lemma lem3616963 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term169 A B t s f x) = (term183 A B t s f x).
Proof. exact (MK_COMB (@lem3616962 A B t s f x) (@lem3616961 A B t s f x)). Qed.
Lemma lem3616965 {A : Type'} (P : Prop) (Q : A -> Prop) : (term184 A P Q) = (term185 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3616966 {B : Type'} (P : Prop) (Q : B -> Prop) : (term184 B P Q) = (term185 B P Q).
Proof. exact (@lem3616965 B P Q). Qed.
Lemma lem3616967 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term186 A B t s f x) = (term187 A B t s f x).
Proof. exact (@lem3616966 B (term165 A B t s f x) (term181 A B t s f x)). Qed.
Lemma lem3616968 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term188 A B t s f x x') = (term179 A B t s f x x').
Proof. exact (eq_refl (term188 A B t s f x x')). Qed.
Lemma lem3616969 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term189 A B t s f x) = (term181 A B t s f x).
Proof. exact (fun_ext (fun x' : B => @lem3616968 A B t s f x x')). Qed.
Lemma lem3616970 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3616971 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term190 A B t s f x) = (term182 A B t s f x).
Proof. exact (MK_COMB (@lem3616970 B) (@lem3616969 A B t s f x)). Qed.
Lemma lem3616972 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term167 A B t s f x) = (term167 A B t s f x).
Proof. exact (eq_refl (term167 A B t s f x)). Qed.
Lemma lem3616973 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term186 A B t s f x) = (term183 A B t s f x).
Proof. exact (MK_COMB (@lem3616972 A B t s f x) (@lem3616971 A B t s f x)). Qed.
Lemma lem3616974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3616975 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term191 A B t s f x) = (term192 A B t s f x).
Proof. exact (MK_COMB (@lem3616974) (@lem3616973 A B t s f x)). Qed.
Lemma lem3616976 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term188 A B t s f x x') = (term179 A B t s f x x').
Proof. exact (eq_refl (term188 A B t s f x x')). Qed.
Lemma lem3616977 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term167 A B t s f x) = (term167 A B t s f x).
Proof. exact (eq_refl (term167 A B t s f x)). Qed.
Lemma lem3616978 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term193 A B t s f x x') = (term194 A B t s f x x').
Proof. exact (MK_COMB (@lem3616977 A B t s f x) (@lem3616976 A B t s f x x')). Qed.
Lemma lem3616979 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term195 A B t s f x) = (term196 A B t s f x).
Proof. exact (fun_ext (fun x' : B => @lem3616978 A B t s f x x')). Qed.
Lemma lem3616980 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3616981 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term187 A B t s f x) = (term197 A B t s f x).
Proof. exact (MK_COMB (@lem3616980 B) (@lem3616979 A B t s f x)). Qed.
Lemma lem3616982 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : ((term186 A B t s f x) = (term187 A B t s f x)) = ((term183 A B t s f x) = (term197 A B t s f x)).
Proof. exact (MK_COMB (@lem3616975 A B t s f x) (@lem3616981 A B t s f x)). Qed.
Lemma lem3616983 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term183 A B t s f x) = (term197 A B t s f x).
Proof. exact (EQ_MP (@lem3616982 A B t s f x) (@lem3616967 A B t s f x)). Qed.
Lemma lem3616985 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term169 A B t s f x) = (term197 A B t s f x).
Proof. exact (TRANS (@lem3616963 A B t s f x) (@lem3616983 A B t s f x)). Qed.
Lemma lem3616986 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term141 A B t s f x) = (term197 A B t s f x).
Proof. exact (TRANS (@lem3616864 A B t s f x) (@lem3616985 A B t s f x)). Qed.
Lemma lem3616987 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term141 A B t s f x) : term197 A B t s f x.
Proof. exact (EQ_MP (@lem3616986 A B t s f x) (@lem3616806 A B t s f x h1)). Qed.
Lemma lem3616988 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term194 A B t s f x x') : term194 A B t s f x x'.
Proof. exact (h1). Qed.
Lemma lem3617025 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term179 A B t s f x x') = (term179 A B t s f x x').
Proof. exact (eq_refl (term179 A B t s f x x')). Qed.
Lemma lem3617050 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term148 A B t s f x x') = (term148 A B t s f x x').
Proof. exact (eq_refl (term148 A B t s f x x')). Qed.
Lemma lem3617051 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term157 A B t s f x) = (term157 A B t s f x).
Proof. exact (fun_ext (fun x' : B => @lem3617050 A B t s f x x')). Qed.
Lemma lem3617052 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3617053 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term158 A B t s f x) = (term158 A B t s f x).
Proof. exact (MK_COMB (@lem3617052 B) (@lem3617051 A B t s f x)). Qed.
Lemma lem3617066 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (x : A) : (term163 A B s t f x) = (term163 A B s t f x).
Proof. exact (eq_refl (term163 A B s t f x)). Qed.
Lemma lem3617067 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term165 A B t s f x) = (term165 A B t s f x).
Proof. exact (MK_COMB (@lem3617066 A B s t f x) (@lem3617053 A B t s f x)). Qed.
Lemma lem3617068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3617069 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term167 A B t s f x) = (term167 A B t s f x).
Proof. exact (MK_COMB (@lem3617068) (@lem3617067 A B t s f x)). Qed.
Lemma lem3617070 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term194 A B t s f x x') = (term194 A B t s f x x').
Proof. exact (MK_COMB (@lem3617069 A B t s f x) (@lem3617025 A B t s f x x')). Qed.
Lemma lem3617071 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term194 A B t s f x x') : term194 A B t s f x x'.
Proof. exact (EQ_MP (@lem3617070 A B t s f x x') (@lem3616988 A B t s f x x' h1)). Qed.
Lemma lem3617072 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term165 A B t s f x.
Proof. exact (h1). Qed.
Lemma lem3617073 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : term179 A B t s f x x'.
Proof. exact (h1). Qed.
Lemma lem3617074 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term158 A B t s f x.
Proof. exact (proj2 (@lem3617072 A B t s f x h1)). Qed.
Lemma lem3617075 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term95 A B s t f x.
Proof. exact (proj1 (@lem3617072 A B t s f x h1)). Qed.
Lemma lem3617078 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : term115 A B t s f x x'.
Proof. exact (proj2 (@lem3617073 A B t s f x x' h1)). Qed.
Lemma lem3617079 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : term143 A B s t f x.
Proof. exact (proj1 (@lem3617073 A B t s f x x' h1)). Qed.
Lemma lem3617080 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : term114 A B s f x x'.
Proof. exact (proj2 (@lem3617078 A B t s f x x' h1)). Qed.
Lemma lem3617099 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) : (term148 A B t s f x x') = (term148 A B t s f x x').
Proof. exact (eq_refl (term148 A B t s f x x')). Qed.
Lemma lem3617100 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term157 A B t s f x) = (term157 A B t s f x).
Proof. exact (fun_ext (fun x' : B => @lem3617099 A B t s f x x')). Qed.
Lemma lem3617101 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3617103 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term158 A B t s f x) = (term158 A B t s f x).
Proof. exact (MK_COMB (@lem3617101 B) (@lem3617100 A B t s f x)). Qed.
Lemma lem3617104 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term158 A B t s f x.
Proof. exact (EQ_MP (@lem3617103 A B t s f x) (@lem3617074 A B t s f x h1)). Qed.
Lemma lem3617128 {A : Type'} (s : A -> Prop) (x : A) (h1 : term198 A s x) : term198 A s x.
Proof. exact (h1). Qed.
Lemma lem3617144 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) (h1 : term199 A B t f x) : term199 A B t f x.
Proof. exact (h1). Qed.
Lemma lem3617145 {A B : Type'} (_39288 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term200 A B t s f x _39288.
Proof. exact (@lem3617104 A B t s f x h1 _39288). Qed.
Lemma lem3617146 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (_39288 : B) : (term200 A B t s f x _39288) = (term148 A B t s f x _39288).
Proof. exact (eq_refl (term200 A B t s f x _39288)). Qed.
Lemma lem3617157 {A B : Type'} (_39288 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term148 A B t s f x _39288.
Proof. exact (EQ_MP (@lem3617146 A B t s f x _39288) (@lem3617145 A B _39288 t s f x h1)). Qed.
Lemma lem3617169 {A : Type'} (s : A -> Prop) (x : A) (h1 : term198 A s x) : term198 A s x.
Proof. exact (h1). Qed.
Lemma lem3617171 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : t x'.
Proof. exact (proj1 (@lem3617078 A B t s f x x' h1)). Qed.
Lemma lem3617175 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : (f x) = x'.
Proof. exact (proj2 (@lem3617080 A B t s f x x' h1)). Qed.
Lemma lem3617177 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) (h1 : term199 A B t f x) : term199 A B t f x.
Proof. exact (h1). Qed.
Lemma lem3617233 {A : Type'} (s : A -> Prop) (x : A) (h1 : term198 A s x) : term198 A s x.
Proof. exact (h1). Qed.
Lemma lem3617234 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : x' = (f x).
Proof. exact (SYM (@lem3617175 A B t s f x x' h1)). Qed.
Lemma lem3617249 {B : Type'} (t : B -> Prop) : (term201 B t) = (term201 B t).
Proof. exact (eq_refl (term201 B t)). Qed.
Lemma lem3617250 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : (term202 B t x') = (term203 A B t f x).
Proof. exact (MK_COMB (@lem3617249 B t) (@lem3617234 A B t s f x x' h1)). Qed.
Lemma lem3617251 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term203 A B t f x) = (term94 A B t f x).
Proof. exact (eq_refl (term203 A B t f x)). Qed.
Lemma lem3617252 {B : Type'} (t : B -> Prop) (x' : B) : (term204 B t x') = (term204 B t x').
Proof. exact (eq_refl (term204 B t x')). Qed.
Lemma lem3617253 {A B : Type'} (x' : B) (t : B -> Prop) (f : A -> B) (x : A) : ((term202 B t x') = (term203 A B t f x)) = ((term202 B t x') = (term94 A B t f x)).
Proof. exact (MK_COMB (@lem3617252 B t x') (@lem3617251 A B t f x)). Qed.
Lemma lem3617254 {B : Type'} (t : B -> Prop) (x' : B) : (term202 B t x') = (t x').
Proof. exact (eq_refl (term202 B t x')). Qed.
Lemma lem3617255 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3617256 {B : Type'} (t : B -> Prop) (x' : B) : (term204 B t x') = (term205 B t x').
Proof. exact (MK_COMB (@lem3617255) (@lem3617254 B t x')). Qed.
Lemma lem3617257 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term94 A B t f x) = (term94 A B t f x).
Proof. exact (eq_refl (term94 A B t f x)). Qed.
Lemma lem3617258 {A B : Type'} (x' : B) (t : B -> Prop) (f : A -> B) (x : A) : ((term202 B t x') = (term94 A B t f x)) = ((t x') = (term94 A B t f x)).
Proof. exact (MK_COMB (@lem3617256 B t x') (@lem3617257 A B t f x)). Qed.
Lemma lem3617259 {A B : Type'} (x' : B) (t : B -> Prop) (f : A -> B) (x : A) : ((term202 B t x') = (term203 A B t f x)) = ((t x') = (term94 A B t f x)).
Proof. exact (TRANS (@lem3617253 A B x' t f x) (@lem3617258 A B x' t f x)). Qed.
Lemma lem3617260 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : (t x') = (term94 A B t f x).
Proof. exact (EQ_MP (@lem3617259 A B x' t f x) (@lem3617250 A B t s f x x' h1)). Qed.
Lemma lem3617289 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) (h1 : term199 A B t f x) : term199 A B t f x.
Proof. exact (h1). Qed.
Lemma lem3617327 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term94 A B t f x.
Proof. exact (proj2 (@lem3617075 A B t s f x h1)). Qed.
Lemma lem3617328 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term206 A B t f x.
Proof. exact (fun h0 : term199 A B t f x => @lem3617327 A B t s f x h1). Qed.
Lemma lem3617330 (p : Prop) : (term207 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3617331 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term206 A B t f x) = (term94 A B t f x).
Proof. exact (@lem3617330 (term94 A B t f x)). Qed.
Lemma lem3617332 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term94 A B t f x.
Proof. exact (EQ_MP (@lem3617331 A B t f x) (@lem3617328 A B t s f x h1)). Qed.
Lemma lem3617334 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : s x.
Proof. exact (proj1 (@lem3617075 A B t s f x h1)). Qed.
Lemma lem3617335 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term208 A s x.
Proof. exact (fun h0 : term198 A s x => @lem3617334 A B t s f x h1). Qed.
Lemma lem3617337 (p : Prop) : (term207 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3617338 {A : Type'} (s : A -> Prop) (x : A) : (term208 A s x) = (s x).
Proof. exact (@lem3617337 (s x)). Qed.
Lemma lem3617339 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : s x.
Proof. exact (EQ_MP (@lem3617338 A s x) (@lem3617335 A B t s f x h1)). Qed.
Lemma lem3617341 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3617342 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3617341 B x). Qed.
Lemma lem3617343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem3617342 B (f x)). Qed.
Lemma lem3617344 {A B : Type'} (f : A -> B) (x : A) : term209 A B f x.
Proof. exact (fun h0 : term210 A B f x => @lem3617343 A B f x). Qed.
Lemma lem3617346 (p : Prop) : (term207 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3617347 {A B : Type'} (f : A -> B) (x : A) : (term209 A B f x) = ((f x) = (f x)).
Proof. exact (@lem3617346 ((f x) = (f x))). Qed.
Lemma lem3617348 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3617347 A B f x) (@lem3617344 A B f x)). Qed.
Lemma lem3617350 (a : Prop) (b : Prop) : (term211 a b) = (term212 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3617351 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (_39288 : B) : (term145 A B s f x _39288) = (term144 A B s f x _39288).
Proof. exact (@lem3617350 (s x) ((f x) = _39288)). Qed.
Lemma lem3617352 {B : Type'} (t : B -> Prop) (_39288 : B) : (term146 B t _39288) = (term146 B t _39288).
Proof. exact (eq_refl (term146 B t _39288)). Qed.
Lemma lem3617353 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (_39288 : B) : (term148 A B t s f x _39288) = (term147 A B t s f x _39288).
Proof. exact (MK_COMB (@lem3617352 B t _39288) (@lem3617351 A B s f x _39288)). Qed.
Lemma lem3617355 (a : Prop) (b : Prop) : (term211 a b) = (term212 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3617356 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (_39288 : B) : (term147 A B t s f x _39288) = (term149 A B t s f x _39288).
Proof. exact (@lem3617355 (t _39288) (term114 A B s f x _39288)). Qed.
Lemma lem3617357 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (_39288 : B) : (term148 A B t s f x _39288) = (term149 A B t s f x _39288).
Proof. exact (TRANS (@lem3617353 A B t s f x _39288) (@lem3617356 A B t s f x _39288)). Qed.
Lemma lem3617359 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3617360 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (_39288 : B) : (term149 A B t s f x _39288) = (term213 A B t s f x _39288).
Proof. exact (@lem3617359 (term115 A B t s f x _39288)). Qed.
Lemma lem3617361 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (_39288 : B) : (term148 A B t s f x _39288) = (term213 A B t s f x _39288).
Proof. exact (TRANS (@lem3617357 A B t s f x _39288) (@lem3617360 A B t s f x _39288)). Qed.
Lemma lem3617363 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term214 A B s f x.
Proof. exact (conj (@lem3617339 A B t s f x h1) (@lem3617348 A B f x)). Qed.
Lemma lem3617364 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term215 A B t s f x.
Proof. exact (conj (@lem3617332 A B t s f x h1) (@lem3617363 A B t s f x h1)). Qed.
Lemma lem3617366 {A B : Type'} (_39288 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term213 A B t s f x _39288.
Proof. exact (EQ_MP (@lem3617361 A B t s f x _39288) (@lem3617157 A B _39288 t s f x h1)). Qed.
Lemma lem3617367 {A B : Type'} (_39288 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term213 A B t s f x _39288.
Proof. exact (@lem3617366 A B _39288 t s f x h1). Qed.
Lemma lem3617368 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term216 A B t s f x.
Proof. exact (@lem3617367 A B (f x) t s f x h1). Qed.
Lemma lem3617371 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : False.
Proof. exact (@lem3617368 A B t s f x h1 (@lem3617364 A B t s f x h1)). Qed.
Lemma lem3617372 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : term217.
Proof. exact (fun h0 : ~ False => @lem3617371 A B t s f x h1). Qed.
Lemma lem3617374 (p : Prop) : (term207 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3617375 : term217 = False.
Proof. exact (@lem3617374 False). Qed.
Lemma lem3617376 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term165 A B t s f x) : False.
Proof. exact (EQ_MP (@lem3617375) (@lem3617372 A B t s f x h1)). Qed.
Lemma lem3617378 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : s x.
Proof. exact (proj1 (@lem3617080 A B t s f x x' h1)). Qed.
Lemma lem3617379 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : term208 A s x.
Proof. exact (fun h0 : term198 A s x => @lem3617378 A B t s f x x' h1). Qed.
Lemma lem3617381 (p : Prop) : (term207 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3617382 {A : Type'} (s : A -> Prop) (x : A) : (term208 A s x) = (s x).
Proof. exact (@lem3617381 (s x)). Qed.
Lemma lem3617383 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : s x.
Proof. exact (EQ_MP (@lem3617382 A s x) (@lem3617379 A B t s f x x' h1)). Qed.
Lemma lem3617386 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3617388 {A : Type'} (s : A -> Prop) (x : A) : (term198 A s x) = (term218 A s x).
Proof. exact (@lem3617386 (s x)). Qed.
Lemma lem3617391 {A : Type'} (s : A -> Prop) (x : A) (h1 : term198 A s x) : term218 A s x.
Proof. exact (EQ_MP (@lem3617388 A s x) (@lem3617233 A s x h1)). Qed.
Lemma lem3617394 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term198 A s x) (h2 : term179 A B t s f x x') : False.
Proof. exact (@lem3617391 A s x h1 (@lem3617383 A B t s f x x' h2)). Qed.
Lemma lem3617395 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term198 A s x) (h2 : term179 A B t s f x x') : term217.
Proof. exact (fun h0 : ~ False => @lem3617394 A B t s f x x' h1 h2). Qed.
Lemma lem3617397 (p : Prop) : (term207 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3617398 : term217 = False.
Proof. exact (@lem3617397 False). Qed.
Lemma lem3617399 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term198 A s x) (h2 : term179 A B t s f x x') : False.
Proof. exact (EQ_MP (@lem3617398) (@lem3617395 A B t s f x x' h1 h2)). Qed.
Lemma lem3617401 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : term94 A B t f x.
Proof. exact (EQ_MP (@lem3617260 A B t s f x x' h1) (@lem3617171 A B t s f x x' h1)). Qed.
Lemma lem3617402 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : term206 A B t f x.
Proof. exact (fun h0 : term199 A B t f x => @lem3617401 A B t s f x x' h1). Qed.
Lemma lem3617404 (p : Prop) : (term207 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3617405 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term206 A B t f x) = (term94 A B t f x).
Proof. exact (@lem3617404 (term94 A B t f x)). Qed.
Lemma lem3617406 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : term94 A B t f x.
Proof. exact (EQ_MP (@lem3617405 A B t f x) (@lem3617402 A B t s f x x' h1)). Qed.
Lemma lem3617409 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3617411 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) : (term199 A B t f x) = (term219 A B t f x).
Proof. exact (@lem3617409 (term94 A B t f x)). Qed.
Lemma lem3617414 {A B : Type'} (t : B -> Prop) (f : A -> B) (x : A) (h1 : term199 A B t f x) : term219 A B t f x.
Proof. exact (EQ_MP (@lem3617411 A B t f x) (@lem3617289 A B t f x h1)). Qed.
Lemma lem3617417 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term199 A B t f x) (h2 : term179 A B t s f x x') : False.
Proof. exact (@lem3617414 A B t f x h1 (@lem3617406 A B t s f x x' h2)). Qed.
Lemma lem3617418 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term199 A B t f x) (h2 : term179 A B t s f x x') : term217.
Proof. exact (fun h0 : ~ False => @lem3617417 A B t s f x x' h1 h2). Qed.
Lemma lem3617420 (p : Prop) : (term207 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3617421 : term217 = False.
Proof. exact (@lem3617420 False). Qed.
Lemma lem3617422 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term199 A B t f x) (h2 : term179 A B t s f x x') : False.
Proof. exact (EQ_MP (@lem3617421) (@lem3617418 A B t s f x x' h1 h2)). Qed.
Lemma lem3617423 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term199 A B t f x) (h2 : term179 A B t s f x x') : (term199 A B t f x) = False.
Proof. exact (prop_ext (fun h3 : term199 A B t f x => @lem3617422 A B t s f x x' h1 h2) (fun h3 : False => @lem3617289 A B t f x h1)). Qed.
Lemma lem3617425 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term199 A B t f x) (h2 : term179 A B t s f x x') : False.
Proof. exact (EQ_MP (@lem3617423 A B t s f x x' h1 h2) (@lem3617289 A B t f x h1)). Qed.
Lemma lem3617426 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term198 A s x) (h2 : term179 A B t s f x x') : (term198 A s x) = False.
Proof. exact (prop_ext (fun h3 : term198 A s x => @lem3617399 A B t s f x x' h1 h2) (fun h3 : False => @lem3617233 A s x h1)). Qed.
Lemma lem3617428 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term198 A s x) (h2 : term179 A B t s f x x') : False.
Proof. exact (EQ_MP (@lem3617426 A B t s f x x' h1 h2) (@lem3617233 A s x h1)). Qed.
Lemma lem3617429 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term199 A B t f x) (h2 : term179 A B t s f x x') : (term199 A B t f x) = False.
Proof. exact (prop_ext (fun h3 : term199 A B t f x => @lem3617425 A B t s f x x' h1 h2) (fun h3 : False => @lem3617177 A B t f x h1)). Qed.
Lemma lem3617430 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term199 A B t f x) (h2 : term179 A B t s f x x') : False.
Proof. exact (EQ_MP (@lem3617429 A B t s f x x' h1 h2) (@lem3617177 A B t f x h1)). Qed.
Lemma lem3617431 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term198 A s x) (h2 : term179 A B t s f x x') : (term198 A s x) = False.
Proof. exact (prop_ext (fun h3 : term198 A s x => @lem3617428 A B t s f x x' h1 h2) (fun h3 : False => @lem3617169 A s x h1)). Qed.
Lemma lem3617432 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term198 A s x) (h2 : term179 A B t s f x x') : False.
Proof. exact (EQ_MP (@lem3617431 A B t s f x x' h1 h2) (@lem3617169 A s x h1)). Qed.
Lemma lem3617433 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term199 A B t f x) (h2 : term179 A B t s f x x') : (term199 A B t f x) = False.
Proof. exact (prop_ext (fun h3 : term199 A B t f x => @lem3617430 A B t s f x x' h1 h2) (fun h3 : False => @lem3617144 A B t f x h1)). Qed.
Lemma lem3617434 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term199 A B t f x) (h2 : term179 A B t s f x x') : False.
Proof. exact (EQ_MP (@lem3617433 A B t s f x x' h1 h2) (@lem3617144 A B t f x h1)). Qed.
Lemma lem3617435 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term198 A s x) (h2 : term179 A B t s f x x') : (term198 A s x) = False.
Proof. exact (prop_ext (fun h3 : term198 A s x => @lem3617432 A B t s f x x' h1 h2) (fun h3 : False => @lem3617128 A s x h1)). Qed.
Lemma lem3617436 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term198 A s x) (h2 : term179 A B t s f x x') : False.
Proof. exact (EQ_MP (@lem3617435 A B t s f x x' h1 h2) (@lem3617128 A s x h1)). Qed.
Lemma lem3617437 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term199 A B t f x) (h2 : term179 A B t s f x x') : (term199 A B t f x) = False.
Proof. exact (prop_ext (fun h3 : term199 A B t f x => @lem3617434 A B t s f x x' h1 h2) (fun h3 : False => @lem3617144 A B t f x h1)). Qed.
Lemma lem3617438 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term199 A B t f x) (h2 : term179 A B t s f x x') : False.
Proof. exact (EQ_MP (@lem3617437 A B t s f x x' h1 h2) (@lem3617144 A B t f x h1)). Qed.
Lemma lem3617439 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term198 A s x) (h2 : term179 A B t s f x x') : (term198 A s x) = False.
Proof. exact (prop_ext (fun h3 : term198 A s x => @lem3617436 A B t s f x x' h1 h2) (fun h3 : False => @lem3617128 A s x h1)). Qed.
Lemma lem3617440 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term198 A s x) (h2 : term179 A B t s f x x') : False.
Proof. exact (EQ_MP (@lem3617439 A B t s f x x' h1 h2) (@lem3617128 A s x h1)). Qed.
Lemma lem3617441 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term179 A B t s f x x') : False.
Proof. exact (or_elim (@lem3617079 A B t s f x x' h1) (fun h0 : term198 A s x => @lem3617440 A B t s f x x' h0 h1) (fun h0 : term199 A B t f x => @lem3617438 A B t s f x x' h0 h1)). Qed.
Lemma lem3617442 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term194 A B t s f x x') : False.
Proof. exact (or_elim (@lem3617071 A B t s f x x' h1) (fun h0 : term165 A B t s f x => @lem3617376 A B t s f x h0) (fun h0 : term179 A B t s f x x' => @lem3617441 A B t s f x x' h0)). Qed.
Lemma lem3617443 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term194 A B t s f x x') : (term194 A B t s f x x') = False.
Proof. exact (prop_ext (fun h2 : term194 A B t s f x x' => @lem3617442 A B t s f x x' h1) (fun h2 : False => @lem3617071 A B t s f x x' h1)). Qed.
Lemma lem3617444 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (x' : B) (h1 : term194 A B t s f x x') : False.
Proof. exact (EQ_MP (@lem3617443 A B t s f x x' h1) (@lem3617071 A B t s f x x' h1)). Qed.
Lemma lem3617445 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term141 A B t s f x) : False.
Proof. exact (ex_elim (@lem3616987 A B t s f x h1) (fun x' : B => fun h0 : term196 A B t s f x x' => @lem3617444 A B t s f x x' h0)). Qed.
Lemma lem3617446 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term141 A B t s f x) : (term141 A B t s f x) = False.
Proof. exact (prop_ext (fun h2 : term141 A B t s f x => @lem3617445 A B t s f x h1) (fun h2 : False => @lem3616806 A B t s f x h1)). Qed.
Lemma lem3617447 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term141 A B t s f x) : False.
Proof. exact (EQ_MP (@lem3617446 A B t s f x h1) (@lem3616806 A B t s f x h1)). Qed.
Lemma lem3617448 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : term140 A B t s f x.
Proof. exact (fun h0 : term141 A B t s f x => @lem3617447 A B t s f x h0). Qed.
Lemma lem3617449 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : A) : (term95 A B s t f x) = (term117 A B t s f x).
Proof. exact (EQ_MP (@lem3616805 A B t s f x) (@lem3617448 A B t s f x)). Qed.
Lemma lem3617454 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term119 A B t s f.
Proof. exact (fun x : A => @lem3617449 A B t s f x). Qed.
Lemma lem3617459 {A B : Type'} (s : A -> Prop) (f : A -> B) : term131 A B s f.
Proof. exact (fun t : B -> Prop => @lem3617454 A B t s f). Qed.
Lemma lem3617464 {A B : Type'} (f : A -> B) : term135 A B f.
Proof. exact (fun s : A -> Prop => @lem3617459 A B s f). Qed.
Lemma lem3617469 {A B : Type'} : term139 A B.
Proof. exact (fun f : A -> B => @lem3617464 A B f). Qed.
Lemma lem3617470 {A B : Type'} : term138 A B.
Proof. exact (EQ_MP (@lem3616801 A B) (@lem3617469 A B)). Qed.
Lemma lem3617471 {A B : Type'} (f : A -> B) : term220 A B f.
Proof. exact (@lem3617470 A B f). Qed.
Lemma lem3617472 {A B : Type'} (f : A -> B) : (term220 A B f) = (term134 A B f).
Proof. exact (eq_refl (term220 A B f)). Qed.
Lemma lem3617473 {A B : Type'} (f : A -> B) : term134 A B f.
Proof. exact (EQ_MP (@lem3617472 A B f) (@lem3617471 A B f)). Qed.
Lemma lem3617474 {A B : Type'} (f : A -> B) (s : A -> Prop) : term221 A B f s.
Proof. exact (@lem3617473 A B f s). Qed.
Lemma lem3617475 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term221 A B f s) = (term130 A B s f).
Proof. exact (eq_refl (term221 A B f s)). Qed.
Lemma lem3617476 {A B : Type'} (s : A -> Prop) (f : A -> B) : term130 A B s f.
Proof. exact (EQ_MP (@lem3617475 A B s f) (@lem3617474 A B f s)). Qed.
Lemma lem3617477 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term222 A B s f t.
Proof. exact (@lem3617476 A B s f t). Qed.
Lemma lem3617478 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term222 A B s f t) = (term121 A B t s f).
Proof. exact (eq_refl (term222 A B s f t)). Qed.
Lemma lem3617479 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term121 A B t s f.
Proof. exact (EQ_MP (@lem3617478 A B t s f) (@lem3617477 A B s f t)). Qed.
Lemma lem3617481 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term121 A B t s f.
Proof. exact (@lem3616647 A B t s f (@lem3617479 A B t s f)). Qed.
Lemma lem3617482 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term122 A B t s f) : False.
Proof. exact (@lem3617481 A B t s f (@lem3616631 A B t s f h1)). Qed.
Lemma lem3617483 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term122 A B t s f) : (term122 A B t s f) = False.
Proof. exact (prop_ext (fun h2 : term122 A B t s f => @lem3617482 A B t s f h1) (fun h2 : False => @lem3616631 A B t s f h1)). Qed.
Lemma lem3617484 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term122 A B t s f) : False.
Proof. exact (EQ_MP (@lem3617483 A B t s f h1) (@lem3616631 A B t s f h1)). Qed.
Lemma lem3617485 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term121 A B t s f.
Proof. exact (fun h0 : term122 A B t s f => @lem3617484 A B t s f h0). Qed.
Lemma lem3617486 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term119 A B t s f.
Proof. exact (EQ_MP (@lem3616630 A B t s f) (@lem3617485 A B t s f)). Qed.
Lemma lem3617488 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term91 A B t s f.
Proof. exact (EQ_MP (@lem3616626 A B t s f) (@lem3617486 A B t s f)). Qed.
Lemma lem3617489 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term55 A B s f t.
Proof. exact (EQ_MP (@lem3616505 A B s f t) (@lem3617488 A B t s f)). Qed.
Lemma lem3617490 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term30 A B s f t.
Proof. exact (EQ_MP (@lem3616424 A B s f t) (@lem3617489 A B s f t)). Qed.
Lemma lem3617491 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : (term21 A B s f t) = (term22 A B s f t).
Proof. exact (EQ_MP (@lem3616363 A B s f t) (@lem3617490 A B s f t)). Qed.
Lemma lem3617492 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term223 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem3617493 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term223 _87967 _87968 P f) = (term224 _87967 _87968 P f).
Proof. exact (eq_refl (term223 _87967 _87968 P f)). Qed.
Lemma lem3617494 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term224 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem3617493 _87967 _87968 P f) (@lem3617492 _87967 _87968 P f)). Qed.
Lemma lem3617495 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term225 _87967 _87968 P f s.
Proof. exact (@lem3617494 _87967 _87968 P f s). Qed.
Lemma lem3617496 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term225 _87967 _87968 P f s) = ((term226 _87967 _87968 f s P) = (term227 _87967 _87968 s P f)).
Proof. exact (eq_refl (term225 _87967 _87968 P f s)). Qed.
Lemma lem3617498 {A B : Type'} (f : A -> B) : term228 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem3617499 {A B : Type'} (f : A -> B) : (term228 A B f) = (term229 A B f).
Proof. exact (eq_refl (term228 A B f)). Qed.
Lemma lem3617500 {A B : Type'} (f : A -> B) : term229 A B f.
Proof. exact (EQ_MP (@lem3617499 A B f) (@lem3617498 A B f)). Qed.
Lemma lem3617501 {A B : Type'} (f : A -> B) (s : A -> Prop) : term230 A B f s.
Proof. exact (@lem3617500 A B f s). Qed.
Lemma lem3617502 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term230 A B f s) = (term231 A B f s).
Proof. exact (eq_refl (term230 A B f s)). Qed.
Lemma lem3617503 {A B : Type'} (f : A -> B) (s : A -> Prop) : term231 A B f s.
Proof. exact (EQ_MP (@lem3617502 A B f s) (@lem3617501 A B f s)). Qed.
Lemma lem3617504 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3617505 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term232 A B f s.
Proof. exact (@lem3617503 A B f s (@lem3617504 A s h1)). Qed.
Lemma lem3617506 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term232 A B f s) = ((term232 A B f s) = True).
Proof. exact (@lem7 (term232 A B f s)). Qed.
Lemma lem3617507 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term232 A B f s) = True.
Proof. exact (EQ_MP (@lem3617506 A B f s) (@lem3617505 A B f s h1)). Qed.
Lemma lem3617513 {_92445 : Type'} (s : type686 _92445) : term233 _92445 s.
Proof. exact (@lem3612894 _92445 s). Qed.
Lemma lem3617514 {_92445 : Type'} (s : type686 _92445) : (term233 _92445 s) = (term234 _92445 s).
Proof. exact (eq_refl (term233 _92445 s)). Qed.
Lemma lem3617515 {_92445 : Type'} (s : type686 _92445) : term234 _92445 s.
Proof. exact (EQ_MP (@lem3617514 _92445 s) (@lem3617513 _92445 s)). Qed.
Lemma lem3617516 {_92445 : Type'} (s : type686 _92445) (h1 : @FINITE (_92445 -> Prop) s) : @FINITE (_92445 -> Prop) s.
Proof. exact (h1). Qed.
Lemma lem3617517 {_92445 : Type'} (s : type686 _92445) (h1 : @FINITE (_92445 -> Prop) s) : (term235 _92445 s) = (term236 _92445 s).
Proof. exact (@lem3617515 _92445 s (@lem3617516 _92445 s h1)). Qed.
Lemma lem3617523 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem3617525 {A B : Type'} (y : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : term237 A B t s f y.
Proof. exact (@lem3616343 A B t s f h1 y). Qed.
Lemma lem3617526 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term237 A B t s f y) = (term238 A B t s f y).
Proof. exact (eq_refl (term237 A B t s f y)). Qed.
Lemma lem3617527 {A B : Type'} (y : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : term238 A B t s f y.
Proof. exact (EQ_MP (@lem3617526 A B t s f y) (@lem3617525 A B y t s f h1)). Qed.
Lemma lem3617528 {B : Type'} (y : B) (t : B -> Prop) (h1 : @IN B y t) : @IN B y t.
Proof. exact (h1). Qed.
Lemma lem3617529 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @IN B y t) : term239 A B s f y.
Proof. exact (@lem3617527 A B y t s f h1 (@lem3617528 B y t h2)). Qed.
Lemma lem3617530 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term239 A B s f y) = ((term239 A B s f y) = True).
Proof. exact (@lem7 (term239 A B s f y)). Qed.
Lemma lem3617531 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @IN B y t) : (term239 A B s f y) = True.
Proof. exact (EQ_MP (@lem3617530 A B s f y) (@lem3617529 A B s f y t h1 h2)). Qed.
Lemma lem3617538 {_92445 : Type'} (s : type686 _92445) : term234 _92445 s.
Proof. exact (fun h0 : @FINITE (_92445 -> Prop) s => @lem3617517 _92445 s h0). Qed.
Lemma lem3617539 {A : Type'} (s : type686 A) : term234 A s.
Proof. exact (@lem3617538 A s). Qed.
Lemma lem3617540 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term240 A B s f t.
Proof. exact (@lem3617539 A (term52 A B s f t)). Qed.
Lemma lem3617542 {A B : Type'} (f : A -> B) (s : A -> Prop) : term241 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem3617507 A B f s h0). Qed.
Lemma lem3617543 {A B : Type'} (f : type1470 A B) (s : B -> Prop) : term242 A B f s.
Proof. exact (@lem3617542 B (A -> Prop) f s). Qed.
Lemma lem3617544 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term243 A B s f t.
Proof. exact (@lem3617543 A B (term61 A B s f) t). Qed.
Lemma lem3617546 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem3617523 B t) (@lem3616344 B t h1)). Qed.
Lemma lem3617547 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem3617546 B t h1)). Qed.
Lemma lem3617548 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem3617547 B t h1) (@lem0)). Qed.
Lemma lem3617549 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : @FINITE B t) : (term244 A B s f t) = True.
Proof. exact (@lem3617544 A B s f t (@lem3617548 B t h1)). Qed.
Lemma lem3617550 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : @FINITE B t) : True = (term244 A B s f t).
Proof. exact (SYM (@lem3617549 A B s f t h1)). Qed.
Lemma lem3617551 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : @FINITE B t) : term244 A B s f t.
Proof. exact (EQ_MP (@lem3617550 A B s f t h1) (@lem0)). Qed.
Lemma lem3617552 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : @FINITE B t) : (term26 A B s f t) = (term245 A B s f t).
Proof. exact (@lem3617540 A B s f t (@lem3617551 A B s f t h1)). Qed.
Lemma lem3617554 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term226 _87967 _87968 f s P) = (term227 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem3617496 _87967 _87968 s P f) (@lem3617495 _87967 _87968 P f s)). Qed.
Lemma lem3617555 {A B : Type'} (s : B -> Prop) (P : type686 A) (f : type1470 A B) : (term246 A B f s P) = (term247 A B s P f).
Proof. exact (@lem3617554 (A -> Prop) B s P f). Qed.
Lemma lem3617556 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term245 A B s f t) = (term248 A B t s f).
Proof. exact (@lem3617555 A B t (@FINITE A) (term61 A B s f)). Qed.
Lemma lem3617564 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term249 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3617565 (p : Prop) (q : Prop) (p' : Prop) : term250 p q p'.
Proof. exact (fun q' : Prop => @lem3617564 p q p' q'). Qed.
Lemma lem3617566 (p : Prop) (q : Prop) : term251 p q.
Proof. exact (fun p' : Prop => @lem3617565 p q p'). Qed.
Lemma lem3617567 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) : term252 A B t s f x.
Proof. exact (@lem3617566 (@IN B x t) (term253 A B s f x)). Qed.
Lemma lem3617568 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (p' : Prop) : term254 A B t s f x p'.
Proof. exact (@lem3617567 A B t s f x p'). Qed.
Lemma lem3617569 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (p' : Prop) : (term254 A B t s f x p') = (term255 A B t s f x p').
Proof. exact (eq_refl (term254 A B t s f x p')). Qed.
Lemma lem3617570 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (p' : Prop) : term255 A B t s f x p'.
Proof. exact (EQ_MP (@lem3617569 A B t s f x p') (@lem3617568 A B t s f x p')). Qed.
Lemma lem3617571 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (p' : Prop) (q' : Prop) : term256 A B t s f x p' q'.
Proof. exact (@lem3617570 A B t s f x p' q'). Qed.
Lemma lem3617572 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (p' : Prop) (q' : Prop) : (term256 A B t s f x p' q') = (term257 A B t s f x p' q').
Proof. exact (eq_refl (term256 A B t s f x p' q')). Qed.
Lemma lem3617573 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (x : B) (p' : Prop) (q' : Prop) : term257 A B t s f x p' q'.
Proof. exact (EQ_MP (@lem3617572 A B t s f x p' q') (@lem3617571 A B t s f x p' q')). Qed.
Lemma lem3617574 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (@IN B x t).
Proof. exact (eq_refl (@IN B x t)). Qed.
Lemma lem3617575 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (t : B -> Prop) (q' : Prop) : term258 A B s f x t q'.
Proof. exact (@lem3617573 A B t s f x (@IN B x t) q'). Qed.
Lemma lem3617576 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (t : B -> Prop) (q' : Prop) : term259 A B s f x t q'.
Proof. exact (@lem3617575 A B s f x t q' (@lem3617574 B x t)). Qed.
Lemma lem3617577 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : @IN B x t.
Proof. exact (h1). Qed.
Lemma lem3617578 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = ((@IN B x t) = True).
Proof. exact (@lem7 (@IN B x t)). Qed.
Lemma lem3617581 {A B : Type'} (f : A -> B) (y : A) : (term78 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3617582 {A B : Type'} (f : type1470 A B) (y : B) : (term79 A B f y) = (f y).
Proof. exact (@lem3617581 B (A -> Prop) f y). Qed.
Lemma lem3617583 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term80 A B s f x) = (term81 A B s f x).
Proof. exact (@lem3617582 A B (term61 A B s f) x). Qed.
Lemma lem3617584 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : B) : (term81 A B s f a) = (term82 A B s f a).
Proof. exact (eq_refl (term81 A B s f a)). Qed.
Lemma lem3617585 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term83 A B s f) = (term61 A B s f).
Proof. exact (fun_ext (fun a : B => @lem3617584 A B s f a)). Qed.
Lemma lem3617586 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3617587 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term80 A B s f x) = (term81 A B s f x).
Proof. exact (MK_COMB (@lem3617585 A B s f) (@lem3617586 B x)). Qed.
Lemma lem3617588 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3617589 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term84 A B s f x) = (term85 A B s f x).
Proof. exact (MK_COMB (@lem3617588 A) (@lem3617587 A B s f x)). Qed.
Lemma lem3617590 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term81 A B s f x) = (term82 A B s f x).
Proof. exact (eq_refl (term81 A B s f x)). Qed.
Lemma lem3617591 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : ((term80 A B s f x) = (term81 A B s f x)) = ((term81 A B s f x) = (term82 A B s f x)).
Proof. exact (MK_COMB (@lem3617589 A B s f x) (@lem3617590 A B s f x)). Qed.
Lemma lem3617592 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term81 A B s f x) = (term82 A B s f x).
Proof. exact (EQ_MP (@lem3617591 A B s f x) (@lem3617583 A B s f x)). Qed.
Lemma lem3617601 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem3617602 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term253 A B s f x) = (term239 A B s f x).
Proof. exact (MK_COMB (@lem3617601 A) (@lem3617592 A B s f x)). Qed.
Lemma lem3617604 {A B : Type'} (y : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : term260 A B t s f y.
Proof. exact (fun h0 : @IN B y t => @lem3617531 A B s f y t h1 h0). Qed.
Lemma lem3617605 {A B : Type'} (y : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : term260 A B t s f y.
Proof. exact (@lem3617604 A B y t s f h1). Qed.
Lemma lem3617606 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : term260 A B t s f x.
Proof. exact (@lem3617605 A B x t s f h1). Qed.
Lemma lem3617608 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : (@IN B x t) = True.
Proof. exact (EQ_MP (@lem3617578 B x t) (@lem3617577 B x t h1)). Qed.
Lemma lem3617609 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : True = (@IN B x t).
Proof. exact (SYM (@lem3617608 B x t h1)). Qed.
Lemma lem3617610 {B : Type'} (x : B) (t : B -> Prop) (h1 : @IN B x t) : @IN B x t.
Proof. exact (EQ_MP (@lem3617609 B x t h1) (@lem0)). Qed.
Lemma lem3617611 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @IN B x t) : (term239 A B s f x) = True.
Proof. exact (@lem3617606 A B x t s f h1 (@lem3617610 B x t h2)). Qed.
Lemma lem3617612 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @IN B x t) : (term253 A B s f x) = True.
Proof. exact (TRANS (@lem3617602 A B s f x) (@lem3617611 A B s f x t h1 h2)). Qed.
Lemma lem3617613 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : term261 A B t s f x.
Proof. exact (fun h0 : @IN B x t => @lem3617612 A B s f x t h1 h0). Qed.
Lemma lem3617614 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) (t : B -> Prop) : term262 A B s f x t.
Proof. exact (@lem3617576 A B s f x t True). Qed.
Lemma lem3617615 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : (term263 A B t s f x) = (term264 B x t).
Proof. exact (@lem3617614 A B s f x t (@lem3617613 A B x t s f h1)). Qed.
Lemma lem3617617 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3617618 {B : Type'} (x : B) (t : B -> Prop) : (term264 B x t) = True.
Proof. exact (@lem3617617 (@IN B x t)). Qed.
Lemma lem3617619 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : (term263 A B t s f x) = True.
Proof. exact (TRANS (@lem3617615 A B x t s f h1) (@lem3617618 B x t)). Qed.
Lemma lem3617620 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : (term265 A B t s f) = (term266 B).
Proof. exact (fun_ext (fun x : B => @lem3617619 A B x t s f h1)). Qed.
Lemma lem3617621 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3617622 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : (term248 A B t s f) = (term267 B).
Proof. exact (MK_COMB (@lem3617621 B) (@lem3617620 A B t s f h1)). Qed.
Lemma lem3617624 {A : Type'} (t : Prop) : (term268 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3617625 {B : Type'} (t : Prop) : (term268 B t) = t.
Proof. exact (@lem3617624 B t). Qed.
Lemma lem3617626 {B : Type'} : (term267 B) = True.
Proof. exact (@lem3617625 B True). Qed.
Lemma lem3617627 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : (term248 A B t s f) = True.
Proof. exact (TRANS (@lem3617622 A B t s f h1) (@lem3617626 B)). Qed.
Lemma lem3617628 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term20 A B t s f) : (term245 A B s f t) = True.
Proof. exact (TRANS (@lem3617556 A B t s f) (@lem3617627 A B t s f h1)). Qed.
Lemma lem3617629 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @FINITE B t) : (term26 A B s f t) = True.
Proof. exact (TRANS (@lem3617552 A B s f t h2) (@lem3617628 A B t s f h1)). Qed.
Lemma lem3617630 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @FINITE B t) : True = (term26 A B s f t).
Proof. exact (SYM (@lem3617629 A B s f t h1 h2)). Qed.
Lemma lem3617631 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @FINITE B t) : term26 A B s f t.
Proof. exact (EQ_MP (@lem3617630 A B s f t h1 h2) (@lem0)). Qed.
Lemma lem3617632 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @FINITE B t) (h3 : (term21 A B s f t) = (term22 A B s f t)) : term28 A B s f t.
Proof. exact (EQ_MP (@lem3616358 A B s f t h3) (@lem3617631 A B s f t h1 h2)). Qed.
Lemma lem3617633 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @FINITE B t) : ((term21 A B s f t) = (term22 A B s f t)) = (term28 A B s f t).
Proof. exact (prop_ext (fun h3 : (term21 A B s f t) = (term22 A B s f t) => @lem3617632 A B s f t h1 h2 h3) (fun h3 : term28 A B s f t => @lem3617491 A B s f t)). Qed.
Lemma lem3617634 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @FINITE B t) : term28 A B s f t.
Proof. exact (EQ_MP (@lem3617633 A B s f t h1 h2) (@lem3617491 A B s f t)). Qed.
Lemma lem3617635 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term19 A B t s f) : term20 A B t s f.
Proof. exact (proj2 (@lem3616342 A B t s f h1)). Qed.
Lemma lem3617636 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term19 A B t s f) : @FINITE B t.
Proof. exact (proj1 (@lem3616342 A B t s f h1)). Qed.
Lemma lem3617637 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @FINITE B t) : (term20 A B t s f) = (term28 A B s f t).
Proof. exact (prop_ext (fun h3 : term20 A B t s f => @lem3617634 A B s f t h1 h2) (fun h3 : term28 A B s f t => @lem3616343 A B t s f h1)). Qed.
Lemma lem3617638 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @FINITE B t) : term28 A B s f t.
Proof. exact (EQ_MP (@lem3617637 A B s f t h1 h2) (@lem3616343 A B t s f h1)). Qed.
Lemma lem3617639 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @FINITE B t) : (@FINITE B t) = (term28 A B s f t).
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem3617638 A B s f t h1 h2) (fun h3 : term28 A B s f t => @lem3616344 B t h2)). Qed.
Lemma lem3617640 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) (h1 : term20 A B t s f) (h2 : @FINITE B t) : term28 A B s f t.
Proof. exact (EQ_MP (@lem3617639 A B s f t h1 h2) (@lem3616344 B t h2)). Qed.
Lemma lem3617641 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : @FINITE B t) (h2 : term19 A B t s f) : (term20 A B t s f) = (term28 A B s f t).
Proof. exact (prop_ext (fun h3 : term20 A B t s f => @lem3617640 A B s f t h3 h1) (fun h3 : term28 A B s f t => @lem3617635 A B t s f h2)). Qed.
Lemma lem3617642 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : @FINITE B t) (h2 : term19 A B t s f) : term28 A B s f t.
Proof. exact (EQ_MP (@lem3617641 A B t s f h1 h2) (@lem3617635 A B t s f h2)). Qed.
Lemma lem3617643 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term19 A B t s f) : (@FINITE B t) = (term28 A B s f t).
Proof. exact (prop_ext (fun h2 : @FINITE B t => @lem3617642 A B t s f h2 h1) (fun h2 : term28 A B s f t => @lem3617636 A B t s f h1)). Qed.
Lemma lem3617644 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term19 A B t s f) : term28 A B s f t.
Proof. exact (EQ_MP (@lem3617643 A B t s f h1) (@lem3617636 A B t s f h1)). Qed.
Lemma lem3617645 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term269 A B s f t.
Proof. exact (fun h0 : term19 A B t s f => @lem3617644 A B t s f h0). Qed.
Lemma lem3617650 {A B : Type'} (s : A -> Prop) (f : A -> B) : term270 A B s f.
Proof. exact (fun t : B -> Prop => @lem3617645 A B s f t). Qed.
Lemma lem3617655 {A B : Type'} (f : A -> B) : term271 A B f.
Proof. exact (fun s : A -> Prop => @lem3617650 A B s f). Qed.
Lemma lem3617662 {A B : Type'} : term272 A B.
Proof. exact (fun f : A -> B => @lem3617655 A B f). Qed.
